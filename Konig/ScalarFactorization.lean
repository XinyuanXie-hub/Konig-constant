module

public import Konig.ScalarGaussian
public import Konig.Halfspace

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace Konig

variable {ι : Type*} [Fintype ι]

theorem integral_euclidean_pair_prod_fintype (F : ι → ℝ → ℝ → ℂ) :
    (∫ x : EuclideanSpace ℝ ι, ∫ y : EuclideanSpace ℝ ι,
      ∏ i, F i (x i) (y i)) = ∏ i, ∫ u : ℝ, ∫ v : ℝ, F i u v := by
  have h (f : EuclideanSpace ℝ ι → ℂ) :
      (∫ x : EuclideanSpace ℝ ι, f x) =
        ∫ x : ι → ℝ, f (WithLp.toLp 2 x) := by
    symm
    exact (PiLp.volume_preserving_toLp ι).integral_comp
      (MeasurableEquiv.toLp 2 _).measurableEmbedding f
  rw [h]
  simp_rw [h]
  simp_rw [integral_fintype_prod_volume_eq_prod]
  exact integral_fintype_prod_volume_eq_prod (fun i u => ∫ v : ℝ, F i u v)

/-- Tensor product of the centered scalar phases, with the exact normalization. -/
theorem scalarPhase_prod (t : ι → ℝ) :
    (((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ Fintype.card ι)⁻¹ *
      (∫ x : EuclideanSpace ℝ ι, ∫ y : EuclideanSpace ℝ ι,
        Complex.exp (∑ i,
          (-((1 - Complex.I * t i) / 2) *
            ((x i : ℂ)^2 + (y i : ℂ)^2) +
            Complex.I * x i * y i - Complex.I * t i / 2))) =
      ∏ i, scalarPhase (t i) := by
  simp_rw [Complex.exp_sum]
  rw [integral_euclidean_pair_prod_fintype (fun i (u v : ℝ) =>
    Complex.exp (-((1 - Complex.I * t i) / 2) *
      ((u : ℂ)^2 + (v : ℂ)^2) + Complex.I * u * v - Complex.I * t i / 2))]
  simp only [scalarPhase, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    inv_pow]

/-- Converts the coordinate exponent to the invariant oscillatory Gaussian form. -/
theorem scalarPhase_sum_exponent (t : ι → ℝ) (x y : EuclideanSpace ℝ ι) :
    (∑ i, (-((1 - Complex.I * t i) / 2) *
        ((x i : ℂ)^2 + (y i : ℂ)^2) +
        Complex.I * x i * y i - Complex.I * t i / 2)) =
      -(((‖x‖ : ℝ) : ℂ)^2 + ((‖y‖ : ℝ) : ℂ)^2) / 2 +
      Complex.I * (inner ℝ x y : ℝ) +
      Complex.I / 2 * ∑ i, (t i : ℂ) * ((x i : ℂ)^2 + (y i : ℂ)^2 - 1) := by
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    Finset.sum_add_distrib, Finset.mul_sum]
  simp only [div_eq_mul_inv, neg_add_rev, neg_mul, add_mul, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum, mul_sub, sub_mul, Finset.sum_sub_distrib,
    mul_add, mul_one, one_mul]
  simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem scalarPhase_prod_invariant (t : ι → ℝ) :
    (((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ Fintype.card ι)⁻¹ *
      (∫ x : EuclideanSpace ℝ ι, ∫ y : EuclideanSpace ℝ ι,
        Complex.exp (-(((‖x‖ : ℝ) : ℂ)^2 + ((‖y‖ : ℝ) : ℂ)^2) / 2 +
          Complex.I * (inner ℝ x y : ℝ) +
          Complex.I / 2 * ∑ i, (t i : ℂ) * ((x i : ℂ)^2 + (y i : ℂ)^2 - 1))) =
      ∏ i, scalarPhase (t i) := by
  simp_rw [← scalarPhase_sum_exponent]
  exact scalarPhase_prod t

end Konig
