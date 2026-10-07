//! Memory layout of the values `validate_fee_payer` reaches through its
//! pointer arguments, measured with the toolchain the validator was built with.
//!
//! Rust guarantees neither field order nor enum encodings, so none of this is
//! read off the source. Private fields (`AccountSharedData`, `Arc`, `Vec`) are
//! located by filling them with distinctive values and searching the raw bytes
//! of the value, padding included.
#![allow(deprecated)] // Rent::exemption_threshold and Rent::burn_percent

use {
    crate::{code::Code, hex::Hex},
    anyhow::{Result, bail, ensure},
    iced_x86::{Code as Opcode, OpKind},
    serde::Serialize,
    solana_account::{Account, AccountSharedData, ReadableAccount},
    solana_pubkey::Pubkey,
    solana_rent::Rent,
    solana_svm::{
        account_loader::validate_fee_payer, transaction_error_metrics::TransactionErrorMetrics,
    },
    solana_transaction_error::TransactionError,
    std::{
        collections::{BTreeMap, BTreeSet},
        mem::{MaybeUninit, align_of, offset_of, size_of},
        num::Saturating,
        sync::Arc,
    },
};

/// The signature the disassembly was read against. The second parameter is
/// `IndexOfAccount`.
type ValidateFeePayer = fn(
    &mut AccountSharedData,
    u16,
    &mut TransactionErrorMetrics,
    &Rent,
    u64,
    bool,
) -> Result<(), TransactionError>;
const _: ValidateFeePayer = validate_fee_payer;

#[derive(Serialize)]
pub struct Layout {
    pub account_shared_data: AccountLayout,
    pub rent: RentLayout,
    pub transaction_error_metrics: MetricsLayout,
    pub result: ResultLayout,
}

/// Byte offsets within `AccountSharedData`.
#[derive(Serialize)]
pub struct AccountLayout {
    pub size: Hex,
    pub align: Hex,
    pub lamports: Hex,
    pub owner: Hex,
    pub rent_epoch: Hex,
    /// The `Arc<Vec<u8>>`: a pointer to its heap block (`ArcInner`).
    pub data_arc: Hex,
    pub arc_inner: ArcInnerLayout,
}

/// Byte offsets from the start of the `ArcInner<Vec<u8>>` block.
#[derive(Serialize)]
pub struct ArcInnerLayout {
    pub data_ptr: Hex,
    pub data_len: Hex,
    pub data_capacity: Hex,
}

#[derive(Serialize)]
pub struct RentLayout {
    pub size: Hex,
    pub lamports_per_byte: Hex,
    pub exemption_threshold: Hex,
    pub burn_percent: Hex,
}

/// The counters are `Saturating<usize>`; only those `validate_fee_payer` bumps.
#[derive(Serialize)]
pub struct MetricsLayout {
    pub size: Hex,
    pub counter_size: Hex,
    pub account_not_found: Hex,
    pub insufficient_funds: Hex,
    pub invalid_account_for_fee: Hex,
}

/// `Result<(), TransactionError>`: a u32 tag at offset 0 selects the variant.
#[derive(Serialize)]
pub struct ResultLayout {
    pub size: Hex,
    pub tags: BTreeMap<&'static str, Hex>,
    /// `InsufficientFundsForRent { account_index: u8 }`.
    pub account_index: Hex,
}

pub fn measure() -> Result<Layout> {
    ensure!(
        cfg!(all(target_arch = "x86_64", target_os = "linux")),
        "layouts must be measured on x86_64-linux, the validator's target"
    );
    Ok(Layout {
        account_shared_data: account_shared_data()?,
        rent: RentLayout {
            size: size_of::<Rent>().into(),
            lamports_per_byte: offset_of!(Rent, lamports_per_byte).into(),
            exemption_threshold: offset_of!(Rent, exemption_threshold).into(),
            burn_percent: offset_of!(Rent, burn_percent).into(),
        },
        transaction_error_metrics: MetricsLayout {
            size: size_of::<TransactionErrorMetrics>().into(),
            counter_size: size_of::<Saturating<usize>>().into(),
            account_not_found: offset_of!(TransactionErrorMetrics, account_not_found).into(),
            insufficient_funds: offset_of!(TransactionErrorMetrics, insufficient_funds).into(),
            invalid_account_for_fee: offset_of!(TransactionErrorMetrics, invalid_account_for_fee)
                .into(),
        },
        result: result()?,
    })
}

fn account_shared_data() -> Result<AccountLayout> {
    const LAMPORTS: u64 = 0x1111_2222_3333_4444;
    const RENT_EPOCH: u64 = 0x5555_6666_7777_8888;
    const OWNER: [u8; 32] = [0xaa; 32];
    // Distinct, so len and capacity can be told apart.
    const LEN: u64 = 80;
    const CAPACITY: u64 = 200;

    let mut data = Vec::with_capacity(CAPACITY as usize);
    data.resize(LEN as usize, 0);
    let account = AccountSharedData::from(Account {
        lamports: LAMPORTS,
        data,
        owner: Pubkey::new_from_array(OWNER),
        executable: false,
        rent_epoch: RENT_EPOCH,
    });
    let account_bytes = raw_bytes(&account);

    // Arc::as_ptr points at the Vec inside the ArcInner, a few bytes past the
    // pointer the Arc stores.
    let arc = account.data_clone();
    let vec_addr = Arc::as_ptr(&arc) as u64;
    let data_arc = unique(
        words(account_bytes)
            .filter(|&(_, w)| vec_addr.wrapping_sub(w) < 64)
            .map(|(o, _)| o),
        "Arc pointer",
    )?;
    let arc_inner_addr = word_at(account_bytes, data_arc);
    let vec_in_arc_inner = (vec_addr - arc_inner_addr) as usize;
    let vec_bytes = raw_bytes(&*arc);
    let field_of_vec = |value, what| {
        Ok::<Hex, anyhow::Error>(
            (vec_in_arc_inner + unique(word_offsets(vec_bytes, value), what)?).into(),
        )
    };

    Ok(AccountLayout {
        size: size_of::<AccountSharedData>().into(),
        align: align_of::<AccountSharedData>().into(),
        lamports: unique(word_offsets(account_bytes, LAMPORTS), "lamports")?.into(),
        owner: unique(
            (0..=account_bytes.len() - OWNER.len())
                .filter(|&o| account_bytes[o..].starts_with(&OWNER)),
            "owner",
        )?
        .into(),
        rent_epoch: unique(word_offsets(account_bytes, RENT_EPOCH), "rent_epoch")?.into(),
        data_arc: data_arc.into(),
        arc_inner: ArcInnerLayout {
            data_ptr: field_of_vec(account.data().as_ptr() as u64, "Vec pointer")?,
            data_len: field_of_vec(LEN, "Vec length")?,
            data_capacity: field_of_vec(CAPACITY, "Vec capacity")?,
        },
    })
}

fn result() -> Result<ResultLayout> {
    type R = Result<(), TransactionError>;
    let rent_error =
        |account_index| Err(TransactionError::InsufficientFundsForRent { account_index });
    let variants: [(&str, R); 5] = [
        ("Ok", Ok(())),
        ("AccountNotFound", Err(TransactionError::AccountNotFound)),
        (
            "InsufficientFundsForFee",
            Err(TransactionError::InsufficientFundsForFee),
        ),
        (
            "InvalidAccountForFee",
            Err(TransactionError::InvalidAccountForFee),
        ),
        ("InsufficientFundsForRent", rent_error(0)),
    ];
    let tags: BTreeMap<_, _> = variants
        .into_iter()
        .map(|(name, value)| {
            (
                name,
                Hex::from(u32::from_le_bytes(encode(value)[..4].try_into().unwrap())),
            )
        })
        .collect();
    ensure!(
        tags.values().collect::<BTreeSet<_>>().len() == tags.len(),
        "tags not distinct"
    );

    let (a, b) = (encode(rent_error(0x01)), encode(rent_error(0x02)));
    let account_index = unique((0..a.len()).filter(|&o| a[o] != b[o]), "account_index")?;
    Ok(ResultLayout {
        size: size_of::<R>().into(),
        tags,
        account_index: account_index.into(),
    })
}

/// Every `mov dword ptr [mem], imm32` in the code writes a Result tag, and every
/// tag is written somewhere. Ties the measured encoding to the binary.
pub fn check_result_tags(layout: &Layout, code: &Code) -> Result<()> {
    let stored: BTreeSet<u32> = code
        .instructions()
        .filter(|i| i.code() == Opcode::Mov_rm32_imm32 && i.op0_kind() == OpKind::Memory)
        .map(|i| i.immediate32())
        .collect();
    let measured: BTreeSet<u32> = layout
        .result
        .tags
        .values()
        .map(|tag| tag.0 as u32)
        .collect();
    if stored != measured {
        bail!("code stores tags {stored:x?}, layout says {measured:x?}");
    }
    Ok(())
}

/// The bytes of a value written into zeroed memory, so bytes the value leaves
/// unwritten compare equal across values.
fn encode<T>(value: T) -> Vec<u8> {
    let mut slot = MaybeUninit::<T>::zeroed();
    slot.write(value);
    raw_bytes(unsafe { slot.assume_init_ref() }).to_vec()
}

fn raw_bytes<T>(value: &T) -> &[u8] {
    unsafe { std::slice::from_raw_parts(value as *const T as *const u8, size_of::<T>()) }
}

/// (offset, value) of every aligned u64 in `bytes`.
fn words(bytes: &[u8]) -> impl Iterator<Item = (usize, u64)> + '_ {
    (0..bytes.len() / 8).map(move |i| (i * 8, word_at(bytes, i * 8)))
}

fn word_offsets(bytes: &[u8], value: u64) -> impl Iterator<Item = usize> + '_ {
    words(bytes)
        .filter(move |&(_, w)| w == value)
        .map(|(offset, _)| offset)
}

fn word_at(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..][..8].try_into().unwrap())
}

fn unique(offsets: impl Iterator<Item = usize>, what: &str) -> Result<usize> {
    let offsets: Vec<usize> = offsets.collect();
    match offsets[..] {
        [offset] => Ok(offset),
        _ => bail!("{what}: found at {offsets:?}, expected exactly one offset"),
    }
}
