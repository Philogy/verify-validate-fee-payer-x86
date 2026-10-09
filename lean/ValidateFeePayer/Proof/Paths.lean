import ValidateFeePayer.Proof.Facts
import ValidateFeePayer.Proof.Constants
import ValidateFeePayer.Proof.Outcome

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

end ValidateFeePayer.Proof
