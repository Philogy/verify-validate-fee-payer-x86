import ValidateFeePayer.Code

namespace ValidateFeePayer

theorem sweepImage_ok : sweepImage.toOption = some listing := by
  set_option maxRecDepth 100000 in decide +kernel

end ValidateFeePayer
