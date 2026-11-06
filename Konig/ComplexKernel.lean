module

public import Konig.EnvelopeReduction

@[expose] public section

open MeasureTheory

noncomputable section
namespace Konig

variable {ι : Type*} [Fintype ι]

/-- Arbitrary bounded measurable insertions preserve joint Gaussian integrability. -/
theorem integrable_complexKernel_mul
    (F : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℂ)
    (hF : AEMeasurable F (volume.prod volume)) (B : ℝ)
    (hB : ∀ p, ‖F p‖ ≤ B) :
    Integrable (fun p => vectorPlaneWaveKernel 0 0 p.1 p.2 * F p)
      (volume.prod volume) :=
  (vectorPlaneWaveKernel_integrable (0 : EuclideanSpace ℝ ι) 0).mul_bdd
    hF.aestronglyMeasurable (Filter.Eventually.of_forall hB)

theorem integrable_complexKernel_mul_real
    (F : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ)
    (hF : AEMeasurable F (volume.prod volume)) (B : ℝ)
    (hB : ∀ p, |F p| ≤ B) :
    Integrable (fun p => vectorPlaneWaveKernel 0 0 p.1 p.2 * (F p : ℂ))
      (volume.prod volume) := by
  apply integrable_complexKernel_mul _
    (Complex.continuous_ofReal.measurable.comp_aemeasurable hF) B
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using hB

end Konig
