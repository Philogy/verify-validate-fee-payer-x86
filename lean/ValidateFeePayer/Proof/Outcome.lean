import ValidateFeePayer.Contract

namespace ValidateFeePayer

open X86

/-- What a finished run must look like: it panics exactly when the spec
panics, having written only what `c` may write, and otherwise returns in a
state satisfying `Post`. -/
def Spec.Outcome (c : Call) (account : Spec.Account) (metrics : Spec.ErrorMetrics) (rent : Spec.Rent)
    (relax : Bool) (s : State) (o : X86.Outcome) : Prop :=
  match Spec.validateFeePayer account c.payerIndex rent c.fee relax metrics, o with
  | (.error (.panic _), _), .panicked s' => c.Frame s s'
  | (.error (.tx e), metrics'), .returned s' => Post c s metrics' (.error e) s'
  | (.ok account', metrics'), .returned s' => Post c s metrics' (.ok account') s'
  | _, _ => False

end ValidateFeePayer
