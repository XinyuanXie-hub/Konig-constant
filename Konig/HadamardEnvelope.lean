module

public import Konig.BlockEnvelope
public import Konig.SineEnvelope
public import Konig.ConstructionSequence
public import Konig.CoefficientIntegral

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace Konig.Construction

/-- Exact envelope reduction for the explicit Hadamard candidates, before expanding
in powers of the phase correlation. -/
theorem hadamard_sineEnvelope_bilinear {m k : ℕ} (hm : 0 < m)
    (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) (a s : Fin k → ℝ)
    (hb : ∀ t, |sineEnvelope a s t| ≤ 1) :
    bilinear (hadamardInputFin H ε (sineEnvelope a s))
      (hadamardInputFin H (-ε) (sineEnvelope a s)) =
      ((((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ (2*m))⁻¹ *
        ∫ u, ∫ v,
          (∑ i, ∑ j, ((a i*a j : ℝ) : ℂ) *
            Complex.exp (-((s i : ℂ)^2 + (s j : ℂ)^2)/4) *
            Complex.sin (((s i*s j*phaseCorrelation H ε u v : ℝ) : ℂ)/2)) *
              vectorPlaneWaveKernel 0 0 u v).re := by
  let E := EuclideanSpace ℝ (Fin m ⊕ Fin m)
  let F := hadamardInput H ε (sineEnvelope a s)
  let G := hadamardInput H (-ε) (sineEnvelope a s)
  let S := fun u v : E => ∑ i, ∑ j, ((a i*a j : ℝ) : ℂ) *
    Complex.exp (-((s i : ℂ)^2 + (s j : ℂ)^2)/4) *
    Complex.sin (((s i*s j*phaseCorrelation H ε u v : ℝ) : ℂ)/2)
  let C : ℂ := (Real.sqrt 2 * Real.pi : ℝ)
  let J := ∫ p : E × E, ∫ q : E × E, (F p : ℂ) * (G q : ℂ) *
    (vectorPlaneWaveKernel 0 0 p.1 q.1 * vectorPlaneWaveKernel 0 0 p.2 q.2)
  have hF : Continuous F := continuous_hadamardInput _ _ _ (continuous_sineEnvelope a s)
  have hG : Continuous G := continuous_hadamardInput _ _ _ (continuous_sineEnvelope a s)
  have hFb (p) : |F p| ≤ 1 := hb _
  have hGb (p) : |G p| ≤ 1 := hb _
  have hH := integrable_block_envelope F G hF hG hFb hGb
  have hR (u v : E) : (C ^ (2*m))⁻¹ *
      (∫ x : E, ∫ y : E, (F (x,u) : ℂ) * (G (y,v) : ℂ) *
        vectorPlaneWaveKernel 0 0 x y) = Complex.I * S u v := by
    simpa only [C, F, G, S, hadamardInput, sineEnvelope, hadamardPhase_neg,
      phaseCorrelation] using
      phase_sine_envelope_pairing hm a s (hadamardPhase H ε u) (hadamardPhase H ε v)
  have hnorm : (C ^ (4*m))⁻¹ * J =
      (C ^ (2*m))⁻¹ * ∫ u : E, ∫ v : E,
        (Complex.I * S u v) * vectorPlaneWaveKernel 0 0 u v := by
    have h := normalized_envelope_reduction (volume : Measure E) (volume : Measure E)
      (fun p => (F p : ℂ)) (fun p => (G p : ℂ))
      (vectorPlaneWaveKernel 0 0) (vectorPlaneWaveKernel 0 0) (fun u v => Complex.I * S u v)
      C (2*m) (by simpa only [Measure.volume_eq_prod] using hH) hR
    simpa only [show 2*m+2*m = 4*m by omega, ← Measure.volume_eq_prod] using h
  have him : ((C ^ (4*m))⁻¹ * J).im =
      (((Real.sqrt 2 * Real.pi)^ (4*m))⁻¹) * J.im := by
    simp only [C, ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hbil := bilinear_blocks_eq_im m F G hF hG hFb hGb
  change bilinear (fun x => F (WithLp.ofLp (blockCoordinates m x)))
    (fun x => G (WithLp.ofLp (blockCoordinates m x))) = _
  rw [hbil, ← him, hnorm]
  simp_rw [mul_assoc, integral_const_mul]
  rw [← mul_assoc, mul_comm ((C ^ (2*m))⁻¹) Complex.I, mul_assoc]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  simp only [C, S, mul_assoc]
  rfl

end Konig.Construction
