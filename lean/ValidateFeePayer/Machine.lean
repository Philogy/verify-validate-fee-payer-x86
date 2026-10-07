import ValidateFeePayer.Memory

/-!
Placeholder for the x86-64 semantics. Its shape is still open; these opaque
declarations only let other files name a state and a step until then.
-/

namespace ValidateFeePayer.Machine

opaque State : Type

/-- One instruction; a memory fault is its own outcome. -/
opaque step : State → Except Fault State

end ValidateFeePayer.Machine
