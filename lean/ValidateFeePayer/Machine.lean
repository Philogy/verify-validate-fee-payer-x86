/-!
Placeholder for the x86-64 semantics. Its shape is still open; these opaque
declarations only let other files name a state and a step until then.
-/

namespace ValidateFeePayer.Machine

opaque State : Type

/-- One instruction; `none` for a fault (e.g. reading an unmapped address). -/
opaque step : State → Option State

end ValidateFeePayer.Machine
