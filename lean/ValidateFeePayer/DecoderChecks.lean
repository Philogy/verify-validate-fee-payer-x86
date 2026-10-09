import ValidateFeePayer.DecoderChecks.Sweep
import ValidateFeePayer.DecoderChecks.Objdump
import ValidateFeePayer.DecoderChecks.Branches

-- Separate from `Checks.lean`: the proof does not use these, and each takes
-- the kernel ~10s, so they are separate modules that check in parallel.
