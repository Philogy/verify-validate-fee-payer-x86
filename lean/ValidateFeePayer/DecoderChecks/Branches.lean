import ValidateFeePayer.Code

namespace ValidateFeePayer
open X86

theorem branch_targets :
    listing.all (fun e => match e.instruction with
      | .jumpIf _ offset | .jump offset =>
        (instructionAt (e.address + e.length.toUInt64 + offset)).isSome
      | _ => true) := by
  set_option maxRecDepth 100000 in decide +kernel

end ValidateFeePayer
