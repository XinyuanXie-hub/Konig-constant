module

public import Konig.EnvelopeReduction
public import Konig.Coordinates

@[expose] public section

open MeasureTheory
noncomputable section
namespace Konig

/-- Imaginary parts commute with jointly integrable iterated integrals. -/
theorem im_integral_integral {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (H : A → B → ℂ) (hH : Integrable (Function.uncurry H) (μ.prod ν)) :
    (∫ x, ∫ y, H x y ∂ν ∂μ).im = ∫ x, ∫ y, (H x y).im ∂ν ∂μ := by
  change RCLike.im (∫ x, ∫ y, H x y ∂ν ∂μ) = _
  rw [integral_integral hH]
  change RCLike.im (∫ p, Function.uncurry H p ∂μ.prod ν) = _
  rw [← integral_im hH]
  exact integral_prod _ hH.im

/-- The imaginary part of the two-block complex Gaussian is the original sine kernel. -/
theorem block_kernel_im {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b : ℝ) (x y : EuclideanSpace ℝ ι) (u v : EuclideanSpace ℝ κ) :
    ((a : ℂ) * (b : ℂ) * (vectorPlaneWaveKernel 0 0 x y *
      vectorPlaneWaveKernel 0 0 u v)).im =
      a * b * Real.exp (-((‖x‖ ^ 2 + ‖u‖ ^ 2 + (‖y‖ ^ 2 + ‖v‖ ^ 2)) / 2)) *
        Real.sin (inner ℝ x y + inner ℝ u v) := by
  simp only [vectorPlaneWaveKernel, inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero]
  rw [← Complex.exp_add]
  have hsum :
      -(((‖x‖ : ℝ) : ℂ)^2 + ((‖y‖ : ℝ) : ℂ)^2)/2 +
        Complex.I*(inner ℝ x y : ℝ) +
      (-(((‖u‖ : ℝ) : ℂ)^2 + ((‖v‖ : ℝ) : ℂ)^2)/2 +
        Complex.I*(inner ℝ u v : ℝ)) =
      ((-((‖x‖^2+‖u‖^2+(‖y‖^2+‖v‖^2))/2) : ℝ) : ℂ) +
        Complex.I*((inner ℝ x y + inner ℝ u v : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hsum]
  simp [Complex.mul_im, Complex.exp_im, mul_assoc, -Complex.ofReal_pow]

/-- Exact bridge from the challenge's real bilinear form to a complex block pairing. -/
theorem bilinear_blocks_eq_im (m : ℕ)
    (F G : EuclideanSpace ℝ (Fin m ⊕ Fin m) × EuclideanSpace ℝ (Fin m ⊕ Fin m) → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hFb : ∀ p, |F p| ≤ 1) (hGb : ∀ p, |G p| ≤ 1) :
    bilinear (fun x => F (WithLp.ofLp (blockCoordinates m x)))
      (fun x => G (WithLp.ofLp (blockCoordinates m x))) =
      ((Real.sqrt 2 * Real.pi) ^ (4*m))⁻¹ *
        (∫ p, ∫ q, (F p : ℂ) * (G q : ℂ) *
          (vectorPlaneWaveKernel 0 0 p.1 q.1 * vectorPlaneWaveKernel 0 0 p.2 q.2)).im := by
  have hH := integrable_block_envelope F G hF hG hFb hGb
  rw [bilinear_blockCoordinates]
  rw [im_integral_integral volume volume _ hH]
  simp only [block_kernel_im]

/-- The normalized two-block pairing reduces to the normalized phase pairing.
The hypothesis is the exact normalized inner Gaussian identity. -/
theorem normalized_envelope_reduction {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (F G : A × B → ℂ) (K : A → A → ℂ) (L : B → B → ℂ) (R : B → B → ℂ)
    (c : ℂ) (d : ℕ)
    (hH : Integrable (fun p : (A × B) × (A × B) =>
      F p.1 * G p.2 * (K p.1.1 p.2.1 * L p.1.2 p.2.2))
      ((μ.prod ν).prod (μ.prod ν)))
    (hR : ∀ u v, (c ^ d)⁻¹ *
      (∫ x, ∫ y, F (x,u) * G (y,v) * K x y ∂μ ∂μ) = R u v) :
    (c ^ (d+d))⁻¹ *
      (∫ p, ∫ q, F p * G q * (K p.1 q.1 * L p.2 q.2) ∂μ.prod ν ∂μ.prod ν) =
      (c ^ d)⁻¹ * ∫ u, ∫ v, R u v * L u v ∂ν ∂ν := by
  let P := fun u v => ∫ x, ∫ y, F (x,u) * G (y,v) * K x y ∂μ ∂μ
  rw [integral_envelope_kernel_reduction μ ν F G K L P hH (fun _ _ => rfl)]
  calc
    _ = (c ^ d)⁻¹ * ∫ u, ∫ v, ((c ^ d)⁻¹ * P u v) * L u v ∂ν ∂ν := by
      simp_rw [mul_assoc, integral_const_mul]
      rw [pow_add, mul_inv_rev]
      ring
    _ = _ := by simp_rw [show ∀ u v, (c ^ d)⁻¹ * P u v = R u v from hR]

end Konig
