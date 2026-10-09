import ValidateFeePayer.Proof.Paths

/-!
Closing a path of the walk: the machine has returned or reached the panic
entry, and the path conditions decide every branch of the spec. `vspec`
evaluates `Spec.validateFeePayer` under them; `vpost` proves `Post` from the
final state.
-/

namespace ValidateFeePayer.Proof

open X86 Lean Elab Tactic Meta

theorem saturating_eq (x : UInt64) :
    (if ¬x = 18446744073709551615 then x + 1 else 18446744073709551615) = Spec.saturatingIncrement x := by
  unfold Spec.saturatingIncrement; split <;> simp_all

theorem minimumBalance_simd0194 {rent : Spec.Rent} (h : rent.exemptionThreshold = Spec.simd0194ExemptionThreshold)
    (d : UInt64) : Spec.minimumBalance rent d =
      if d ≤ Spec.maxPermittedDataLength ∧ rent.lamportsPerByte ≤ Spec.simd0194MaxLamportsPerByte
      then .ok ((Spec.accountStorageOverhead + d) * rent.lamportsPerByte)
      else .error .maximumPermittedDataLengthExceeded := by
  simp only [Spec.minimumBalance, h, ↓reduceIte]
  by_cases h1 : d ≤ Spec.maxPermittedDataLength <;>
    by_cases h2 : rent.lamportsPerByte ≤ Spec.simd0194MaxLamportsPerByte <;>
    simp [h1, h2, guard, failure, bind, Except.bind, pure, Except.pure]

theorem minimumBalance_current {rent : Spec.Rent} (h : rent.exemptionThreshold = Spec.currentExemptionThreshold)
    (d : UInt64) : Spec.minimumBalance rent d =
      if d ≤ Spec.maxPermittedDataLength ∧ rent.lamportsPerByte ≤ Spec.currentMaxLamportsPerByte
      then .ok (2 * (Spec.accountStorageOverhead + d) * rent.lamportsPerByte)
      else .error .maximumPermittedDataLengthExceeded := by
  have : rent.exemptionThreshold ≠ Spec.simd0194ExemptionThreshold := by
    rw [h]; decide
  simp only [Spec.minimumBalance, h, ↓reduceIte, Spec.currentExemptionThreshold,
    Spec.simd0194ExemptionThreshold]
  by_cases h1 : d ≤ Spec.maxPermittedDataLength <;>
    by_cases h2 : rent.lamportsPerByte ≤ Spec.currentMaxLamportsPerByte <;>
    simp [h1, h2, guard, failure, bind, Except.bind, pure, Except.pure]

/-- `systemAccountKind` with its conditions as the code tests them: on the
length as a `u64`, and on the tags as numbers. -/
theorem systemAccountKind_eq (a : Spec.Account) (hn : a.data.length < 2 ^ 64) :
    Spec.systemAccountKind a =
      if a.owner = Spec.systemProgramId then
        if a.data.length.toUInt64 = 0 then some .system
        else if a.data.length.toUInt64 = 80 ∧
            (ofLittleEndian (a.data.take 4) = 0 ∨ ofLittleEndian (a.data.take 4) = 1) ∧
            ofLittleEndian ((a.data.drop 4).take 4) = 1 then some .nonce
        else none
      else none := by
  have h0 : a.data = [] ↔ a.data.length.toUInt64 = 0 := by
    rw [← List.length_eq_zero_iff, ← UInt64.toNat_inj]
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.toNat_zero]
    omega
  have h80 : a.data.length = Spec.nonceStateSize ↔ a.data.length.toUInt64 = 80 := by
    rw [← UInt64.toNat_inj]
    simp only [Spec.nonceStateSize, Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.toNat_ofNat]
    omega
  simp only [Spec.systemAccountKind, ← h0, ← h80]
  by_cases ho : a.owner = Spec.systemProgramId <;> by_cases hd : a.data = [] <;>
    by_cases hl : a.data.length = Spec.nonceStateSize <;>
    by_cases ht : (ofLittleEndian (a.data.take 4) = 0 ∨ ofLittleEndian (a.data.take 4) = 1) ∧
      ofLittleEndian ((a.data.drop 4).take 4) = 1 <;>
    simp only [ho, hd, hl, ht, guard, failure, bind, Option.bind, pure, ↓reduceIte,
      and_true, and_false] <;> simp_all

/-! ## Deciding the spec's branches -/

/-- The first `if` in `e` whose condition mentions no bound variable and is
not in `skip`; with `inState := false`, not inside a machine state. -/
partial def firstCondition? (skip : Array Expr) (inState : Bool) (e : Expr) : Option Expr :=
  let cond? := if e.isAppOfArity ``ite 5 then some e.appFn!.appFn!.appFn!.appArg! else none
  if let some c := cond?.filter fun c => !c.hasLooseBVars && !skip.contains c then some c
  else if !inState && e.isAppOf ``X86.State.mk then none
  else match e with
    | .app f a => firstCondition? skip inState f <|> firstCondition? skip inState a
    | .lam _ t b _ | .forallE _ t b _ => firstCondition? skip inState t <|> firstCondition? skip inState b
    | .letE _ t v b _ =>
      firstCondition? skip inState t <|> firstCondition? skip inState v <|> firstCondition? skip inState b
    | .mdata _ b => firstCondition? skip inState b
    | .proj _ _ b => firstCondition? skip inState b
    | _ => none

/-- Decide the `if`s of the goal that the path conditions decide, simplifying
with `lemmas` in between. The others in the machine state are values the code
computes, such as a saturating increment, and stay; the others in the spec are
branches whose outcome the path does not fix, such as the two fee checks the
code fuses into one, and are split on. -/
elab "vdecide" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let simpStep ← `(tactic| simp only [$ls,*, ↓reduceIte, ↓reduceDIte, throw, throwThe,
    MonadExceptOf.throw, Except.bind, bind, pure, Except.pure, liftM, monadLift, MonadLift.monadLift,
    Except.mapError, Except.map, and_true, true_and, and_false, false_and, or_true, true_or, or_false,
    false_or, not_true_eq_false, not_false_eq_true, Bool.false_eq_true, ite_true, ite_false])
  let _ ← tryTactic (evalTactic simpStep)
  let mut todo := (← getGoals).map ((·, (#[] : Array Expr)))
  let mut done := #[]
  for _ in [0:256] do
    let some ((g, skip), rest) := todo.head?.map (·, todo.tail) | setGoals done.toList; return
    todo := rest
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    let some c := firstCondition? skip true t | done := done.push g; continue
    setGoals [g]
    let decided ← g.withContext do
      if let some prf ← refute? c then
        takePath (mkNot c) prf; pure true
      else if let some prf ← refute? (mkNot c) then
        takePath c (← mkAppM ``Classical.byContradiction #[prf]); pure true
      else pure false
    -- A decided condition the path rewrote away is gone; one that stays sits
    -- in a value, like an undecided one.
    let skip := skip.push c
    if decided then
      let _ ← tryTactic (evalTactic simpStep)
      todo := (← getGoals).map ((·, skip)) ++ todo
    else if (firstCondition? (skip.pop) false t) == some c then
      let path := mkIdent `path
      evalTactic (← `(tactic| by_cases $path:ident : $(← Term.exprToSyntax c)))
      let gs ← getGoals
      let mut split := []
      for g' in gs do
        setGoals [g']
        evalTactic (← `(tactic| try simp only [$path:ident, ↓reduceIte, not_false_eq_true]))
        let _ ← tryTactic (evalTactic simpStep)
        split := split ++ (← getGoals).map ((·, skip))
      todo := split ++ todo
    else todo := (g, skip) :: todo
  throwError "vdecide: too many conditions"

/-- Rewrite hypothesis `h`, or the goal, with the path conditions, so facts
about the entry values match the state, which `vsplit` rewrote with them. -/
syntax "simp_paths" (" at " ident)? : tactic

elab_rules : tactic | `(tactic| simp_paths $[at $h]?) => withMainContext do
  let mut thms : SimpTheorems := {}
  for d in ← getLCtx do
    if d.userName == `path && !d.isImplementationDetail then
      thms ← thms.add (.fvar d.fvarId) #[] (mkFVar d.fvarId)
  let ctx ← Simp.mkContext (simpTheorems := #[thms])
  match h with
  | some h =>
    let (r, _) ← simpLocalDecl (← getMainGoal) (← getFVarId h) ctx
    replaceMainGoal (r.map (·.2) |>.toList)
  | none =>
    let (r, _) ← simpTarget (← getMainGoal) ctx
    replaceMainGoal r.toList

/-- `Account.Encodes` after a successful run: the lamports were stored, and
the other fields are read through the stores from the entry memory. -/
syntax "vaccount" term : tactic
macro_rules
  | `(tactic| vaccount $e) => `(tactic| (
    have henc := ($e).accountEncoded
    simp only [Spec.Account.Encodes, Abi.PtrAt, Memory.Holds, Memory.HoldsBytes, off_eq, ($e).accountPtr,
      ($e).arcInnerPtr, ($e).dataPtr, ($e).memory, Image.Layout.account_shared_data.data_arc,
      Image.Layout.account_shared_data.lamports, Image.Layout.account_shared_data.owner,
      Image.Layout.account_shared_data.arc_inner.data_ptr, Image.Layout.account_shared_data.arc_inner.data_len,
      Nat.toUInt64_eq, UInt64.reduceOfNat, UInt64.add_zero, Vector.length_toList] at henc ⊢
    simp_paths at henc
    try simp_paths
    obtain ⟨h1, -, h3, h4, h5, h6⟩ := henc
    simp (disch := walk_disch) only [vexec, h1, h3, h4, h5, h6, and_true, true_and]))

/-- `mov byte [rdi + 4], r9b` stores the low byte of the `u16` passed in `dx`. -/
theorem payerIndexByte {r2 : UInt64} {p : UInt16} (h : r2 &&& 0xffff = p.toUInt64) :
    r2 &&& 4294967295 &&& 255 = p.toUInt8.toUInt64 := by
  have e1 : r2 &&& 4294967295 &&& 255 = (r2 &&& 0xffff) &&& 255 := by bits64
  rw [e1, h]
  apply UInt64.toNat_inj.1
  simp only [UInt64.toNat_and, UInt16.toNat_toUInt64, UInt8.toNat_toUInt64, UInt16.toNat_toUInt8,
    UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  have := p.toNat_lt
  rw [show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem uint8_toUInt64_and_255 (x : UInt8) : x.toUInt64 &&& 255 = x.toUInt64 := by
  apply UInt64.toNat_inj.1
  simp only [UInt64.toNat_and, UInt8.toNat_toUInt64, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  have := x.toNat_lt
  rw [show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The final state wrote only what the call may write. -/
syntax "vframe" term : tactic
macro_rules
  | `(tactic| vframe $e) => `(tactic| (
    unfold Call.Frame
    intro access a ha
    rw [← ($e).memory]
    simp only [Call.Written, ($e).resultPtr, ($e).accountPtr, ($e).metricsPtr, ($e).rsp, off_eq,
      Image.Layout.result.size, Image.Layout.account_shared_data.lamports,
      Image.Layout.transaction_error_metrics.account_not_found,
      Image.Layout.transaction_error_metrics.invalid_account_for_fee,
      Image.Layout.transaction_error_metrics.insufficient_funds, stackUse, Nat.toUInt64_eq, UInt64.reduceOfNat,
      not_or, not_and, Nat.not_lt] at ha
    repeat rw [byte_wr_other (by
      intro j hj eq
      replace eq := congrArg UInt64.toNat eq
      simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.toNat_ofNat, OperandSize.byteCount,
        Nat.reducePow, Nat.reduceMod, UInt64.toNat_sub] at eq hj ha
      omega_conjunct ha)]))

/-- The final state of a returning path meets `Post`. -/
syntax "vpost" term : tactic
macro_rules
  | `(tactic| vpost $e) => `(tactic| (
    refine ⟨?r, ?a, ?m, ?rax, ?sp, ?cs, ?fc, ?frame⟩
    case r =>
      simp only [ResultEncodes, resultTag, Except.map, ($e).resultPtr, Memory.Holds, off_eq,
        Image.Layout.result.tags.AccountNotFound, Image.Layout.result.tags.InvalidAccountForFee,
        Image.Layout.result.tags.InsufficientFundsForFee, Image.Layout.result.tags.InsufficientFundsForRent,
        Image.Layout.result.tags.Ok, Image.Layout.result.account_index, Nat.toUInt64_eq, UInt64.reduceOfNat]
      simp (disch := walk_disch) only [vexec, and_true, true_and, payerIndexByte ($e).payerIndex,
        uint8_toUInt64_and_255]
    case a =>
      intro _ h
      first
        | (cases h; done)
        | (cases h; vaccount $e)
    case m =>
      simp only [Spec.ErrorMetrics.Encodes, Memory.Holds, off_eq, ($e).metricsPtr,
        Image.Layout.transaction_error_metrics.account_not_found,
        Image.Layout.transaction_error_metrics.invalid_account_for_fee,
        Image.Layout.transaction_error_metrics.insufficient_funds, Nat.toUInt64_eq, UInt64.reduceOfNat]
      simp (disch := walk_disch) only [vexec, ($e).readAccountNotFound, ($e).readInvalidAccountForFee,
        ($e).readInsufficientFunds, and_true, saturating_eq]
    case rax => simp only [vexec, ($e).resultPtr]
    case sp =>
      rw [($e).rsp]; simp only [State.rsp, vexec, UInt64.add_assoc, foldAdd]
    case cs =>
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, or_false, forall_eq, vexec,
        ($e).rbx, ($e).rbp, ($e).r12, ($e).r13, ($e).r14, ($e).r15, and_self]
    case fc => simp only [($e).mxcsr]
    case frame => vframe $e))

/-- Close a path: it returned or panicked, the path conditions decide the
spec, and the final state meets `Post`. `minimumBalance_eq` is the
`minimumBalance` equation of the path's exemption threshold. -/
syntax "vleaf" term "," term "," term : tactic
macro_rules
  | `(tactic| vleaf $e, $account, $minimumBalance_eq) => `(tactic| (
    first
      | (refine (Finishes.returned ?_ ?_).mono (by omega)
         · simp only [Call.exits, exits, ($e).returnAddress])
      | (refine (Finishes.panicked ?_ ?_ ?_).mono (by omega)
         · simp only [Call.exits, exits, ($e).returnAddress]; exact fun h => ($e).notPanic h.symm
         · simp only [Call.exits, exits, panicAddress, ImageOffset.at, Image.panicEntry, ($e).loadBase]; rfl)
    have path := ($e).dataLength
    have := ($e).result_data
    have := ($e).account_data
    have := ($e).arcInner_data
    have := ($e).data_metrics
    have := ($e).data_rent
    have := ($e).data_stack
    have := ($e).dataBound
    vdecide [Spec.Outcome, Spec.validateFeePayer, Spec.chargeFeePayer,
      systemAccountKind_eq $account ($e).dataLength, ← ($e).owner, $minimumBalance_eq:term, ($e).feeArg,
      Spec.maxPermittedDataLength, Spec.simd0194MaxLamportsPerByte, Spec.currentMaxLamportsPerByte,
      Spec.accountStorageOverhead, Spec.nonceStateSize, foldAdd, foldMul, UInt64.reduceOfNat, Nat.toUInt64_eq]
    all_goals first | vpost $e | vframe $e | trivial))

/-- Every path from the entry state of `e`: `hthr` fixes the exemption
threshold `threshold`, and `minimumBalance_eq` is its `minimumBalance`
equation. -/
syntax "vpaths" term "," term "," term "," term "," term : tactic
macro_rules
  | `(tactic| vpaths $e, $account, $hthr, $threshold, $minimumBalance_eq) => `(tactic| (
    have hx := ($e).codeExits
    have hc := ($e).code
    have hd := ($e).data
    have hw := ($e).stackFree
    have hwr := ($e).resultWritable
    have hwm1 := ($e).accountNotFoundWritable
    have hwm2 := ($e).insufficientFundsWritable
    have hwm3 := ($e).invalidAccountForFeeWritable
    have hwl := ($e).lamportsWritable
    have hSt := ($e).stackBound
    have hR := ($e).resultBound
    have hA := ($e).accountBound
    have hArc := ($e).arcBound
    have hM := ($e).metricsBound
    have hRnt := ($e).rentBound
    have s01 := ($e).result_account
    have s02 := ($e).result_arcInner
    have s04 := ($e).result_metrics
    have s05 := ($e).result_rent
    have s06 := ($e).result_stack
    have s12 := ($e).account_arcInner
    have s14 := ($e).account_metrics
    have s15 := ($e).account_rent
    have s16 := ($e).account_stack
    have s24 := ($e).arcInner_metrics
    have s25 := ($e).arcInner_rent
    have s26 := ($e).arcInner_stack
    have s45 := ($e).metrics_rent
    have s46 := ($e).metrics_stack
    have s56 := ($e).rent_stack
    have hs36 := ($e).nonceData_stack
    have hDat80 := ($e).nonceDataBound
    have hthrM := ($e).readThreshold
    rw [$hthr:term, $threshold:term] at hthrM
    simp only [entryState]
    vwalk [($e).readReturn, ($e).readRelax, ($e).readArc, ($e).readLamports, ($e).readOwnerLow,
      ($e).readOwnerHigh, ($e).readData, ($e).readLength, ($e).readVersions, ($e).readState,
      ($e).readLamportsPerByte, hthrM, ($e).readAccountNotFound, ($e).readInvalidAccountForFee,
      ($e).readInsufficientFunds]
    without_info all_goals vleaf $e, $account, $minimumBalance_eq))

end ValidateFeePayer.Proof
