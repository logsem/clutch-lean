module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Noisy count

Proved differentially private in `Micrometer/Examples/NoisyCount`. -/

namespace ProbLang
namespace NoisyCount

/-- The number of `true` entries of the database `db`. -/
noncomputable def count {n : ℕ} (db : Fin n → Bool) : ℝ :=
  ∑ i, if db i then 1 else 0

/-- Release the count of `db` perturbed by the sampler `lap`. -/
noncomputable def noisyCount (lap : Val ℝ) {n : ℕ} (db : Fin n → Bool) : Exp ℝ :=
  pl% {Exp.ofVal lap} #(.real (count db))

end NoisyCount
end ProbLang
