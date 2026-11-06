module

public import Konig.PhaseSineSeries
public import Konig.ComplexKernel
public import Konig.ConstructionSequence
public import Konig.HadamardEnvelope

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace Konig.Construction

/-- Integrate the finite envelope sum and substitute the exact coefficient series. -/
theorem normalized_phase_envelope_eq_series {m k : ℕ} (hm : 0 < m)
    (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) (a s : Fin k → ℝ) :
    (((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ (2*m))⁻¹ *
      (∫ x, ∫ y, ∑ i, ∑ j,
        ((a i * a j * Real.exp (-(s i ^ 2 + s j ^ 2) / 4) : ℝ) : ℂ) *
        (vectorPlaneWaveKernel 0 0 x y *
          (Real.sin ((s i * s j / 2) * phaseCorrelation H ε x y) : ℂ))) =
      ∑ i, ∑ j, ((a i * a j * Real.exp (-(s i ^ 2 + s j ^ 2) / 4) : ℝ) : ℂ) *
        correctedSineSeries (fun n => phaseCoefficient H ε (2*n+1)) (s i * s j / 2) := by
  let E := EuclideanSpace ℝ (Fin m ⊕ Fin m)
  let c := fun i j => ((a i * a j * Real.exp (-(s i ^ 2 + s j ^ 2) / 4) : ℝ) : ℂ)
  let F := fun i j (x y : E) => c i j * (vectorPlaneWaveKernel 0 0 x y *
    (Real.sin ((s i * s j / 2) * phaseCorrelation H ε x y) : ℂ))
  have hF (i j : Fin k) : Integrable (Function.uncurry (F i j)) (volume.prod volume) := by
    have h := integrable_complexKernel_mul_real
      (fun p : E × E => Real.sin ((s i * s j / 2) * phaseCorrelation H ε p.1 p.2))
      (by
        apply Continuous.aemeasurable
        exact Real.continuous_sin.comp (continuous_const.mul (continuous_phaseCorrelation H ε)))
      1 (fun _ => Real.abs_sin_le_one _)
    exact h.const_mul (c i j)
  change _ * (∫ x, ∫ y, ∑ i, ∑ j, F i j x y) = _
  rw [integral_integral_finsetSum volume volume Finset.univ
    (fun i x y => ∑ j, F i j x y)
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hF i j))]
  simp_rw [integral_integral_finsetSum volume volume Finset.univ
    (fun j x y => F _ j x y) (fun j _ => hF _ j)]
  simp only [F, c, integral_const_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_left_comm, phase_sine_integral_eq_series hm]

/-- The Gaussian-envelope integrand in the block formula has the same scalar series. -/
theorem phase_envelope_eq_envelopeSeries {m k : ℕ} (hm : 0 < m)
    (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) (a s : Fin k → ℝ) :
    ((((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ (2*m))⁻¹ *
      (∫ x, ∫ y,
        (∑ i, ∑ j, ((a i * a j : ℝ) : ℂ) *
          Complex.exp (-((s i : ℂ)^2 + (s j : ℂ)^2) / 4) *
          Complex.sin (((s i * s j * phaseCorrelation H ε x y : ℝ) : ℂ) / 2)) *
          vectorPlaneWaveKernel 0 0 x y)).re =
      envelopeSeries (fun n => phaseCoefficient H ε (2*n+1)) a s := by
  have he (x y : EuclideanSpace ℝ (Fin m ⊕ Fin m)) :
      (∑ i, ∑ j, ((a i * a j : ℝ) : ℂ) *
        Complex.exp (-((s i : ℂ)^2 + (s j : ℂ)^2) / 4) *
        Complex.sin (((s i * s j * phaseCorrelation H ε x y : ℝ) : ℂ) / 2)) *
        vectorPlaneWaveKernel 0 0 x y =
      ∑ i, ∑ j, ((a i * a j * Real.exp (-(s i ^ 2 + s j ^ 2) / 4) : ℝ) : ℂ) *
        (vectorPlaneWaveKernel 0 0 x y *
          (Real.sin ((s i * s j / 2) * phaseCorrelation H ε x y) : ℂ)) := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    rw [show (s i : ℂ) * s j * (phaseCorrelation H ε x y : ℂ) / 2 =
        ((s i : ℂ) * s j / 2) * (phaseCorrelation H ε x y : ℂ) by ring]
    ring
  simp_rw [he]
  rw [normalized_phase_envelope_eq_series hm]
  rfl

/-- The exact formula for the fixed admissible candidate family. -/
theorem candidate_formula {k : ℕ} (a s : Fin k → ℝ)
    (hb : ∀ x, |sineEnvelope a s x| ≤ 1) (r : ℕ) :
    bilinear (candidateLeft a s r) (candidateRight a s r) =
      envelopeSeries (coefficientSequence phaseScale r) a s := by
  have hm : 0 < 2 ^ (3*r) := by positivity
  exact (hadamard_sineEnvelope_bilinear hm (sylvester (3*r))
    (phaseScale / (2 : ℝ)^r) a s hb).trans
    (phase_envelope_eq_envelopeSeries hm (sylvester (3*r)) (phaseScale / (2 : ℝ)^r) a s)

end Konig.Construction
