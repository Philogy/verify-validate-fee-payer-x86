import ValidateFeePayer.Proof.Facts
import ValidateFeePayer.Proof.Constants
import ValidateFeePayer.Proof.Outcome
import ValidateFeePayer.Proof.Entry

/-!
The entry state of `Pre` over plain variables: every value the code starts
from is a variable, tied to `c`, `s` and the spec's values by an equation.
The walk is proved over these variables. Run directly on the projections of
`s` it would leave `s.register r` inside the walked state, and the kernel
then checks `(State.mk … (s.register r) …).register r ≡ s.register r` by
unfolding both sides.
-/

namespace ValidateFeePayer.Proof

open X86

/-- What the walk knows at entry, about the variables standing for `c`, `s`
and the spec values. -/
structure Entry (c : Call) (account : Spec.Account) (metrics : Spec.ErrorMetrics) (rent : Spec.Rent)
    (relax : Bool) (s : State) (lb S acct arc dat res met rnt fee ra : UInt64)
    (r2 r3 r5 r12 r13 r14 r15 : UInt64) (o1 o2 : BitVec 128) (m : Memory) : Prop where
  loadBase : c.loadBase = lb
  accountPtr : c.account.account = acct
  arcInnerPtr : c.account.arcInner = arc
  dataPtr : c.account.data = dat
  resultPtr : c.result = res
  metricsPtr : c.errorMetrics = met
  rentPtr : c.rent = rnt
  feeArg : c.fee = fee
  returnAddress : c.returnAddress = ra
  memory : s.memory = m
  stackPointer : s.stackPointer = S + 96
  -- Only the low 16 bits of `rdx` are the `u16`.
  payerIndex : r2 &&& 0xffff = c.payerIndex.toUInt64
  base : s.register .base = r3
  framePointer : s.register .framePointer = r5
  r12 : s.register .r12 = r12
  r13 : s.register .r13 = r13
  r14 : s.register .r14 = r14
  r15 : s.register .r15 = r15
  notPanic : ra ≠ lb + 0x12be100
  codeExits : CodeExits lb c.exits
  code : CodeAt lb m
  data : DataAt lb m
  aligned : lb % 16 = 0
  stackFree : WritableAt m S 96
  resultWritable : WritableAt m res 12
  metricsWritable : WritableAt m met 192
  lamportsWritable : WritableAt m (acct + 8) 8
  readReturn : m.read .bytes8 (S + 96) = .ok ra
  readRelax : m.read .bytes1 (S + 104) = .ok (if relax then 1 else 0)
  readArc : m.read .bytes8 acct = .ok arc
  readLamports : m.read .bytes8 (acct + 8) = .ok account.lamports
  readOwnerLow : m.read128 (acct + 16) = .ok o1
  readOwnerHigh : m.read128 (acct + 32) = .ok o2
  owner : o2 ||| o1 = 0 ↔ account.owner = Spec.systemProgramId
  readData : m.read .bytes8 (arc + 24) = .ok dat
  readLength : m.read .bytes8 (arc + 32) = .ok account.data.length.toUInt64
  readVersions : account.data.length.toUInt64 = 80 →
    m.read .bytes4 dat = .ok (ofLittleEndian (account.data.take 4))
  readState : account.data.length.toUInt64 = 80 →
    m.read .bytes4 (dat + 4) = .ok (ofLittleEndian ((account.data.drop 4).take 4))
  readLamportsPerByte : m.read .bytes8 rnt = .ok rent.lamportsPerByte
  readThreshold : m.read .bytes8 (rnt + 8) = .ok rent.exemptionThreshold
  readAccountNotFound : m.read .bytes8 (met + 32) = .ok metrics.accountNotFound
  readInvalidAccountForFee : m.read .bytes8 (met + 88) = .ok metrics.invalidAccountForFee
  readInsufficientFunds : m.read .bytes8 (met + 80) = .ok metrics.insufficientFunds
  accountEncoded : account.Encodes m c.account
  metricsEncoded : metrics.Encodes m c.errorMetrics
  dataLength : account.data.length < 2 ^ 64
  stackBound : S.toNat + 112 ≤ 2 ^ 64
  resultBound : res.toNat + 12 ≤ 2 ^ 64
  accountBound : acct.toNat + 64 ≤ 2 ^ 64
  arcBound : arc.toNat + 40 ≤ 2 ^ 64
  dataBound : dat.toNat + account.data.length ≤ 2 ^ 64
  metricsBound : met.toNat + 192 ≤ 2 ^ 64
  rentBound : rnt.toNat + 24 ≤ 2 ^ 64
  result_account : Separate res 12 acct 64
  result_arcInner : Separate res 12 arc 40
  result_data : Separate res 12 dat account.data.length
  result_metrics : Separate res 12 met 192
  result_rent : Separate res 12 rnt 24
  result_stack : Separate res 12 S 112
  account_arcInner : Separate acct 64 arc 40
  account_data : Separate acct 64 dat account.data.length
  account_metrics : Separate acct 64 met 192
  account_rent : Separate acct 64 rnt 24
  account_stack : Separate acct 64 S 112
  arcInner_data : Separate arc 40 dat account.data.length
  arcInner_metrics : Separate arc 40 met 192
  arcInner_rent : Separate arc 40 rnt 24
  arcInner_stack : Separate arc 40 S 112
  data_metrics : Separate dat account.data.length met 192
  data_rent : Separate dat account.data.length rnt 24
  data_stack : Separate dat account.data.length S 112
  metrics_rent : Separate met 192 rnt 24
  metrics_stack : Separate met 192 S 112
  rent_stack : Separate rnt 24 S 112
  nonceData_stack : account.data.length.toUInt64 = 80 → Separate dat 80 S 112
  nonceDataBound : account.data.length.toUInt64 = 80 → dat.toNat + 80 ≤ 2 ^ 64

/-- The entry state as `vwalk` starts from it. -/
abbrev entryState (lb S acct res met rnt fee r0 r2 r3 r5 r10 r11 r12 r13 r14 r15 : UInt64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : BitVec 128) (fc : UInt32) (m : Memory) :
    State :=
  State.mk (lb + 0x27f3560)
    #v[r0, met, r2, r3, S + 96, r5, acct, res, rnt, fee, r10, r11, r12, r13, r14, r15]
    .undefined #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] fc m

/-- The owner's halves as the code loads them. -/
def ownerLow (x : Spec.Account) : BitVec 128 :=
  ofHalves (ofLittleEndian ((x.owner.toList.take 16).take 8)) (ofLittleEndian ((x.owner.toList.take 16).drop 8))

def ownerHigh (x : Spec.Account) : BitVec 128 :=
  ofHalves (ofLittleEndian ((x.owner.toList.drop 16).take 8)) (ofLittleEndian ((x.owner.toList.drop 16).drop 8))

theorem entry_of_pre {c : Call} {account : Spec.Account} {metrics : Spec.ErrorMetrics} {rent : Spec.Rent}
    {relax : Bool} {s : State} (pre : Pre c account metrics rent relax s)
    (notPanic : c.returnAddress ≠ panicAddress c.loadBase) :
    Entry c account metrics rent relax s c.loadBase (s.stackPointer - 96) c.account.account
      c.account.arcInner c.account.data c.result c.errorMetrics c.rent c.fee c.returnAddress
      (s.register .data) (s.register .base) (s.register .framePointer) (s.register .r12) (s.register .r13)
      (s.register .r14) (s.register .r15) (ownerLow account) (ownerHigh account) s.memory := by
  have sep := separation_of_pre pre
  obtain ⟨harc, hlam, ho1, ho2, hdat, hlen, hdata⟩ := Spec.Account.reads pre.accountEncoded
  obtain ⟨hlpb, hthr⟩ := pre.rentEncoded
  obtain ⟨hc1, hc2, hc3⟩ := pre.metricsEncoded
  have hsp : s.stackPointer - 96 + 96 = s.stackPointer := UInt64.sub_add_cancel _ _
  have hn : account.data.length < 2 ^ 64 := by
    have := sep.result_data; have := sep.data; have := sep.result; unfold Separate at *; omega
  have h80 : account.data.length.toUInt64 = 80 → account.data.length = 80 := by
    intro h; have := congrArg UInt64.toNat h
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat'] at this; simp at this; omega
  simp only [Memory.Holds, BoolEncodes, off_eq, Image.Layout.rent.lamports_per_byte,
    Image.Layout.rent.exemption_threshold, Image.Layout.transaction_error_metrics.account_not_found,
    Image.Layout.transaction_error_metrics.invalid_account_for_fee,
    Image.Layout.transaction_error_metrics.insufficient_funds, Nat.toUInt64_eq, UInt64.reduceOfNat,
    UInt64.add_zero] at hlpb hthr hc1 hc2 hc3
  refine
    { loadBase := rfl, accountPtr := rfl, arcInnerPtr := rfl, dataPtr := rfl, resultPtr := rfl,
      metricsPtr := rfl, rentPtr := rfl, feeArg := rfl, returnAddress := rfl, memory := rfl,
      stackPointer := hsp.symm, payerIndex := pre.payerIndexRegister, base := rfl, framePointer := rfl,
      r12 := rfl, r13 := rfl, r14 := rfl, r15 := rfl,
      notPanic := fun h => notPanic (by rw [h]; rfl),
      codeExits := codeExits_of_pre pre, code := codeAt_of_pre pre, data := dataAt_of_pre pre,
      aligned := pre.alignedBase, owner := ownerHalves_eq_zero account.owner,
      readArc := harc, readLamports := hlam, readOwnerLow := ho1, readOwnerHigh := ho2, readData := hdat,
      readLength := hlen,
      readVersions := fun h => (hdata (h80 h)).1, readState := fun h => (hdata (h80 h)).2,
      readLamportsPerByte := hlpb, readThreshold := hthr, readAccountNotFound := hc1,
      readInvalidAccountForFee := hc2, readInsufficientFunds := hc3,
      accountEncoded := pre.accountEncoded, metricsEncoded := pre.metricsEncoded, dataLength := hn,
      stackBound := sep.stack, resultBound := sep.result, accountBound := sep.account,
      arcBound := sep.arcInner, dataBound := sep.data, metricsBound := sep.metrics, rentBound := sep.rent,
      result_account := sep.result_account, result_arcInner := sep.result_arcInner,
      result_data := sep.result_data, result_metrics := sep.result_metrics, result_rent := sep.result_rent,
      result_stack := sep.result_stack, account_arcInner := sep.account_arcInner,
      account_data := sep.account_data, account_metrics := sep.account_metrics,
      account_rent := sep.account_rent, account_stack := sep.account_stack,
      arcInner_data := sep.arcInner_data, arcInner_metrics := sep.arcInner_metrics,
      arcInner_rent := sep.arcInner_rent, arcInner_stack := sep.arcInner_stack,
      data_metrics := sep.data_metrics, data_rent := sep.data_rent, data_stack := sep.data_stack,
      metrics_rent := sep.metrics_rent, metrics_stack := sep.metrics_stack, rent_stack := sep.rent_stack,
      nonceData_stack := fun h => by have := sep.data_stack; rwa [h80 h] at this,
      nonceDataBound := fun h => by have := sep.data; rwa [h80 h] at this,
      stackFree := ?_, resultWritable := ?_, metricsWritable := ?_, lamportsWritable := ?_,
      readReturn := ?_, readRelax := ?_ }
  · have := WritableAt.of_writable pre.stackFree
    simpa [stackUse] using this
  · simpa [Image.Layout.result.size] using WritableAt.of_writable pre.resultWritable
  · simpa [Image.Layout.transaction_error_metrics.size] using WritableAt.of_writable pre.metricsWritable
  · simpa [off_eq, Image.Layout.account_shared_data.lamports] using WritableAt.of_writable pre.lamportsWritable
  · rw [hsp]; exact pre.returnAddress
  · have := pre.relaxArgument
    simp only [BoolEncodes, Memory.Holds] at this
    rw [show s.stackPointer - 96 + 104 = s.stackPointer + 8 by
      rw [show (104 : UInt64) = 96 + 8 from rfl, ← UInt64.add_assoc, hsp]]
    simpa using this

end ValidateFeePayer.Proof
