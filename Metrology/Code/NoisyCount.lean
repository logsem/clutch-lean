module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Noisy count

The program `noisyCount`: apply a sampler value to the number of `true` entries of a database.
Its DP theorem, conditional on the sampler's spec, is in `Micrometer/Examples/NoisyCount`. -/

namespace ProbLang
namespace NoisyCount

/-- The number of `true` entries of the database `db`. -/
noncomputable def count {n : ℕ} (db : Fin n → Bool) : ℝ :=
  ∑ i, if db i then 1 else 0

/-- The program that applies the sampler value `lap` to the count of `db`. -/
noncomputable def noisyCount (lap : Val ℝ) {n : ℕ} (db : Fin n → Bool) : Exp ℝ :=
  pl% {Exp.ofVal lap} #(.real (count db))

end NoisyCount
end ProbLang
