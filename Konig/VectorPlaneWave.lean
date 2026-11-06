module

public import Konig.Halfspace
public import Konig.ScalarPlaneWave

@[expose] public section

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace Konig

def vectorPlaneWaveKernel {ι : Type*} [Fintype ι]
    (u v x y : EuclideanSpace ℝ ι) : ℂ :=
  Complex.exp (-(((‖x‖ : ℝ) : ℂ) ^ 2 + ((‖y‖ : ℝ) : ℂ) ^ 2) / 2 +
    Complex.I * (inner ℝ x y : ℝ) + Complex.I * (inner ℝ u x : ℝ) +
    Complex.I * (inner ℝ v y : ℝ))

/-- The fully normalized Gaussian integral with two plane-wave insertions. -/
theorem vector_planeWave_integral {ι : Type*} [Fintype ι] (u v : EuclideanSpace ℝ (ι)) :
    (((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ Fintype.card ι)⁻¹ *
      (∫ x : EuclideanSpace ℝ (ι), ∫ y : EuclideanSpace ℝ (ι),
        Complex.exp (-(((‖x‖ : ℝ) : ℂ) ^ 2 + ((‖y‖ : ℝ) : ℂ) ^ 2) / 2 +
          Complex.I * (inner ℝ x y : ℝ) + Complex.I * (inner ℝ u x : ℝ) +
          Complex.I * (inner ℝ v y : ℝ))) =
      Complex.exp (∑ i, (-((u i : ℂ) ^ 2 + (v i : ℂ) ^ 2) / 4 -
        Complex.I * u i * v i / 2)) := by
  simp_rw [planeWave_exponent_eq_sum]
  rw [integral_euclidean_cexp_sum_pair (fun i (x y : ℝ) =>
    -((x : ℂ)^2 + (y : ℂ)^2) / 2 + Complex.I*x*y +
      Complex.I*u i*x + Complex.I*v i*y)]
  change _ * (∏ i, ∫ x : ℝ, ∫ y : ℝ, planeWaveKernel (u i) (v i) x y) = _
  simp_rw [planeWave_integral_standard]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← Complex.exp_sum, ← mul_assoc, inv_mul_cancel₀, one_mul]
  apply pow_ne_zero
  exact_mod_cast mul_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
    Real.pi_ne_zero

theorem planeWave_result_exponent {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℝ ι) :
    -(((‖u‖ : ℝ) : ℂ)^2 + ((‖v‖ : ℝ) : ℂ)^2) / 4 -
        Complex.I * (inner ℝ u v : ℝ) / 2 =
      ∑ i, (-((u i : ℂ)^2 + (v i : ℂ)^2) / 4 - Complex.I*u i*v i/2) := by
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib, Finset.sum_div,
    Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem vector_planeWave_integral_norm {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℝ ι) :
    (((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ Fintype.card ι)⁻¹ *
      (∫ x, ∫ y, vectorPlaneWaveKernel u v x y) =
    Complex.exp (-(((‖u‖ : ℝ) : ℂ)^2 + ((‖v‖ : ℝ) : ℂ)^2) / 4 -
      Complex.I * (inner ℝ u v : ℝ) / 2) := by
  rw [planeWave_result_exponent]
  exact vector_planeWave_integral u v

end Konig
