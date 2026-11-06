module

public import Konig.EnvelopeReduction

@[expose] public section

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace Konig

theorem sine_product_exp (a b z : ℂ) :
    Complex.sin a * Complex.sin b * Complex.exp z =
      -(Complex.exp (z + Complex.I*a + Complex.I*b) -
        Complex.exp (z + Complex.I*a - Complex.I*b) -
        Complex.exp (z - Complex.I*a + Complex.I*b) +
        Complex.exp (z - Complex.I*a - Complex.I*b)) / 4 := by
  simp only [Complex.sin, sub_eq_add_neg, Complex.exp_add]
  simp only [mul_comm]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem vector_sine_kernel_expansion {ι : Type*} [Fintype ι]
    (u v x y : EuclideanSpace ℝ ι) :
    (Real.sin (inner ℝ u x) : ℂ) * (Real.sin (inner ℝ v y) : ℂ) *
        vectorPlaneWaveKernel 0 0 x y =
      -(vectorPlaneWaveKernel u v x y - vectorPlaneWaveKernel u (-v) x y -
        vectorPlaneWaveKernel (-u) v x y + vectorPlaneWaveKernel (-u) (-v) x y) / 4 := by
  simp only [vectorPlaneWaveKernel, inner_zero_left, Complex.ofReal_zero,
    mul_zero, add_zero, inner_neg_left, Complex.ofReal_neg, mul_neg,
    Complex.ofReal_sin]
  convert sine_product_exp (inner ℝ u x : ℝ) (inner ℝ v y : ℝ)
    (-(((‖x‖ : ℝ) : ℂ)^2 + ((‖y‖ : ℝ) : ℂ)^2)/2 +
      Complex.I*(inner ℝ x y : ℝ)) using 1

theorem integral_sub_sub_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h k : α → ℂ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hh : Integrable h μ) (hk : Integrable k μ) :
    (∫ x, f x - g x - h x + k x ∂μ) =
      (∫ x, f x ∂μ) - (∫ x, g x ∂μ) - (∫ x, h x ∂μ) + (∫ x, k x ∂μ) := by
  have h12 := integral_sub hf hg
  have h123 := integral_sub (hf.sub hg) hh
  have h1234 := integral_add ((hf.sub hg).sub hh) hk
  simp only [Pi.sub_apply] at h123 h1234
  rw [h1234, h123, h12]

set_option backward.isDefEq.respectTransparency false in
theorem vector_sine_integral_expansion {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℝ ι) :
    (∫ x, ∫ y, (Real.sin (inner ℝ u x) : ℂ) * (Real.sin (inner ℝ v y) : ℂ) *
      vectorPlaneWaveKernel 0 0 x y) =
      -((∫ x, ∫ y, vectorPlaneWaveKernel u v x y) -
        (∫ x, ∫ y, vectorPlaneWaveKernel u (-v) x y) -
        (∫ x, ∫ y, vectorPlaneWaveKernel (-u) v x y) +
        (∫ x, ∫ y, vectorPlaneWaveKernel (-u) (-v) x y)) / 4 := by
  rw [integral_integral (vector_sine_pair_integrable u v)]
  simp_rw [vector_sine_kernel_expansion]
  rw [integral_div, integral_neg]
  have h := integral_sub_sub_add (vectorPlaneWaveKernel_integrable u v)
    (vectorPlaneWaveKernel_integrable u (-v))
    (vectorPlaneWaveKernel_integrable (-u) v)
    (vectorPlaneWaveKernel_integrable (-u) (-v))
  simp only [Function.uncurry] at h
  rw [h]
  congr 2
  simp only [integral_integral (vectorPlaneWaveKernel_integrable _ _)]

/-- The bounded-sine replacement for the oscillatory sign half-space identity. -/
theorem vector_sine_integral {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℝ ι) :
    (((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ Fintype.card ι)⁻¹ *
      (∫ x, ∫ y, (Real.sin (inner ℝ u x) : ℂ) * (Real.sin (inner ℝ v y) : ℂ) *
        vectorPlaneWaveKernel 0 0 x y) =
      Complex.I * Complex.exp (-(((‖u‖ : ℝ) : ℂ)^2 + ((‖v‖ : ℝ) : ℂ)^2)/4) *
        Complex.sin ((inner ℝ u v : ℝ) / 2) := by
  rw [vector_sine_integral_expansion]
  let C : ℂ := (((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ Fintype.card ι)⁻¹
  have hd (a b c d : ℂ) : C * (-(a-b-c+d)/4) = -(C*a-C*b-C*c+C*d)/4 := by ring
  rw [hd]
  dsimp only [C]
  rw [vector_planeWave_integral_norm, vector_planeWave_integral_norm,
    vector_planeWave_integral_norm, vector_planeWave_integral_norm]
  simp only [norm_neg, inner_neg_left, inner_neg_right, neg_neg,
    Complex.ofReal_neg, mul_neg, neg_div, sub_neg_eq_add]
  rw [show Complex.I * (inner ℝ u v : ℝ) / 2 =
    (((inner ℝ u v : ℝ) : ℂ) / 2) * Complex.I by ring]
  simpa only [neg_div] using gaussian_sine_extraction
    ((((‖u‖ : ℝ) : ℂ)^2 + ((‖v‖ : ℝ) : ℂ)^2)/4)
    (((inner ℝ u v : ℝ) : ℂ)/2)

end Konig
