import X86.Memory
import ValidateFeePayer.Image

/-! The carved image as the loader maps it at `loadBase`. -/

namespace ValidateFeePayer

open X86

open Image in
def regions : List Region := functions ++ data

def imageEnd : Nat := regions.foldl (fun acc r => max acc r.endAddress) 0

/-- No carved address wraps around `2^64`. Nothing in the code depends on
the base being page-aligned, so that is not required. -/
def ValidLoadBase (loadBase : UInt64) : Prop := loadBase.toNat + imageEnd ≤ 2 ^ 64

instance : DecidablePred ValidLoadBase := fun _ => inferInstanceAs (Decidable (_ ≤ _))

-- The GOT slots are read-only, as after RELRO.
def Region.mapping (loadBase : UInt64) (r : Region) : Option Mapping :=
  r.contents.bytesAt loadBase |>.map fun bytes =>
    { base := loadBase + r.address, bytes,
      permissions := if r.contents.isCode then .readExecute else .readOnly }

def imageMappings (loadBase : UInt64) : List Mapping := regions.filterMap (·.mapping loadBase)

def entryAddress (loadBase : UInt64) : UInt64 := loadBase + Image.validate_fee_payer.address

def panicAddress (loadBase : UInt64) : UInt64 := loadBase + Image.panicEntry

end ValidateFeePayer
