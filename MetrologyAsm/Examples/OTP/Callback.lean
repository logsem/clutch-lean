import MetrologyAsm.Examples.OTP.Source
import MetrologyAsm.ABI.Interface
import Metrology.Micrometer.Examples.RandomBytes
import Metrology.Micrometer.AsmOrdinary
import Metrology.Iris.LocalBI

/-! # The real ProbLang sampler callback under the Sail FFI kernel -/

namespace MetrologyAsm.OTP

open Iris Iris.BI ProbLang ProbLang.Asm MicrometerWpGS GradedLifting

/-- The OTP program executes actual Sail and supplies the ordinary randombytes lambda. -/
noncomputable def otpEnv {rT : Type} : FfiEnv rT := ⟨rv, fun _ => RandomBytes.randombytesValue⟩

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B]
  [CanonicallyOrderedAdd B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerGS rT hlc GF] [BudgetGS B GF]
  [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind]
  {E : CoPset}

local bi IProp GF

/-- The actual callback fills its owned pad byte under the same kernel as the assembly call. -/
theorem otp_randombytes_wp (l : Loc) (v : Val rT) (Φ : Val rT → IProp GF) : iprop%
    appArrayFrag l v 1 ∗ (RandomBytes.byteArray l 1 -∗ Φ .unit) ⊢
      wpFor (primStepWith otpEnv) L E (pl% &RandomBytes.randombytes (#loc l, (#int 1, #()))) Φ :=
  (RandomBytes.wp_randombytes 1 l v Φ).trans (wp_ffi_of_wp otpEnv)

end MetrologyAsm.OTP
