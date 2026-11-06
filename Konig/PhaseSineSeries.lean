module

public import Konig.CoefficientIntegral
public import Konig.IntegralSeries
public import Konig.EnvelopeSeries

@[expose] public section

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace Konig.Construction

/-- The normalized phase integral of a sine is exactly its corrected sine series. -/
theorem phase_sine_integral_eq_series {m : ℕ} (hm : 0 < m)
    (H : Matrix (Fin m) (Fin m) ℝ) (ε q : ℝ) :
    (((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ (2*m))⁻¹ *
      (∫ x, ∫ y, vectorPlaneWaveKernel 0 0 x y *
        (Real.sin (q * phaseCorrelation H ε x y) : ℂ)) =
      correctedSineSeries (fun n => phaseCoefficient H ε (2*n+1)) q := by
  let E := EuclideanSpace ℝ (Fin m ⊕ Fin m)
  let K : E × E → ℂ := Function.uncurry (vectorPlaneWaveKernel 0 0)
  let Z : E × E → ℝ := Function.uncurry (phaseCorrelation H ε)
  have hK : Integrable K (volume.prod volume) := vectorPlaneWaveKernel_integrable 0 0
  have hZ : Continuous Z := continuous_phaseCorrelation H ε
  have hZb (p : E × E) : |Z p| ≤ 1 := phaseCorrelation_abs_le_one hm H ε p.1 p.2
  have hsin : Integrable (fun p : E × E => K p * (Real.sin (q * Z p) : ℂ))
      (volume.prod volume) := by
    apply hK.mul_bdd (c := 1)
    · exact (Complex.continuous_ofReal.comp (Real.continuous_sin.comp
        (continuous_const.mul hZ))).aestronglyMeasurable
    · filter_upwards [] with p
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_sin_le_one (q*Z p)
  have hp (k : ℕ) : Integrable (fun p : E × E => K p * (Z p : ℂ)^k)
      (volume.prod volume) := by
    apply hK.mul_bdd (c := 1)
    · exact ((Complex.continuous_ofReal.comp hZ).pow k).aestronglyMeasurable
    · filter_upwards [] with p
      simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs]
      exact pow_le_one₀ (abs_nonneg _) (hZb p)
  have hs := integral_mul_real_sin_series K hK Z hZ.aemeasurable hZb q
  rw [integral_integral hsin]
  change _ * (∫ p, K p * (Real.sin (q*Z p) : ℂ) ∂volume.prod volume) = _
  rw [hs, ← tsum_mul_left]
  unfold correctedSineSeries
  apply tsum_congr
  intro n
  dsimp only
  rw [phaseCoefficient_eq_integral, integral_integral (hp (2*n+1))]
  change _ * (_ * (∫ p, K p * (Z p : ℂ)^(2*n+1) ∂volume.prod volume)) =
    _ * (_ * (∫ p, K p * (Z p : ℂ)^(2*n+1) ∂volume.prod volume))
  ring

end Konig.Construction
