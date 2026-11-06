module

public import Konig.ConstructionSequence
public import Konig.CoefficientLimit
public import Konig.EnvelopeSeries
public import Konig.FinalAssembly

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Konig.Construction

theorem coefficientSequence_norm_le_one (c : ℝ) (r n : ℕ) :
    ‖coefficientSequence c r n‖ ≤ 1 :=
  phaseCoefficient_norm_le_one (by positivity) _ _ _

theorem envelopeSeries_limit {k : ℕ} (a s : Fin k → ℝ) :
    Tendsto (fun r => envelopeSeries (coefficientSequence phaseScale r) a s) atTop
      (𝓝 (∫ x, (∑ i, a i * Real.sin (s i * x)) ^ 2 ∂GaussianSineGram.gaussian)) :=
  tendsto_envelopeSeries (coefficientSequence phaseScale)
    (coefficientSequence_norm_le_one phaseScale)
    (coefficientSequence_tendsto phaseScale phaseScale_cube) a s

/-- Final assembly once the exact Gaussian integral formula for the explicit
candidates is established. No existence of extremizers is assumed here. -/
theorem constant_eq_one_of_candidate_formula
    (hformula : ∀ (k : ℕ) (a s : Fin k → ℝ),
      (∀ x, |sineEnvelope a s x| ≤ 1) → ∀ (r : ℕ),
      bilinear (candidateLeft a s r) (candidateRight a s r) =
        envelopeSeries (coefficientSequence phaseScale r) a s) :
    constant = 1 := by
  apply constant_eq_one_of_envelope_limits GaussianSineGram.gaussian
  intro k a s hb
  refine ⟨dimension, candidateLeft a s, candidateRight a s, ?_, ?_⟩
  · intro r
    obtain ⟨hf, hfb⟩ := candidateLeft_admissible a s hb r
    obtain ⟨hg, hgb⟩ := candidateRight_admissible a s hb r
    exact ⟨dimension_pos r, hf, hg, hfb, hgb⟩
  · simpa only [hformula k a s hb] using envelopeSeries_limit a s

end Konig.Construction
