module

public import Konig.Definitions
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace Konig

noncomputable section

/-- The unnormalized rotating vector used by the half-space construction. -/
def phaseVector {m : ℕ} (θ : Fin m → ℝ) :
    EuclideanSpace ℝ (Fin m ⊕ Fin m) :=
  WithLp.toLp 2 (Sum.elim (fun i => Real.cos (θ i)) (fun i => Real.sin (θ i)))

theorem phaseVector_norm_sq {m : ℕ} (θ : Fin m → ℝ) :
    ‖phaseVector θ‖ ^ 2 = m := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [phaseVector, Fintype.sum_sum_type]
  rw [← Finset.sum_add_distrib]
  simp [Real.cos_sq_add_sin_sq]

theorem phaseVector_inner_neg {m : ℕ} (θ φ : Fin m → ℝ) :
    inner ℝ (phaseVector θ) (phaseVector (fun i => -φ i)) =
      ∑ i, Real.cos (θ i + φ i) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    phaseVector, Fintype.sum_sum_type, star_trivial,
    Real.cos_neg, Real.sin_neg]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Sum.elim_inl, Sum.elim_inr, Real.cos_add]
  ring

theorem phaseVector_norm {m : ℕ} (θ : Fin m → ℝ) :
    ‖phaseVector θ‖ = Real.sqrt m := by
  rw [← phaseVector_norm_sq θ, Real.sqrt_sq (norm_nonneg _)]

/-- The unit normal for a rotating half-space. -/
def phaseNormal {m : ℕ} (θ : Fin m → ℝ) :
    EuclideanSpace ℝ (Fin m ⊕ Fin m) :=
  (Real.sqrt m)⁻¹ • phaseVector θ

theorem continuous_phaseNormal {m : ℕ} :
    Continuous (fun θ : Fin m → ℝ => phaseNormal θ) := by
  have hc : Continuous (fun θ : Fin m → ℝ => phaseVector θ) := by
    unfold phaseVector
    apply (PiLp.continuous_toLp 2 (fun _ : Fin m ⊕ Fin m => ℝ)).comp
    apply continuous_pi
    intro i
    cases i with
    | inl i => exact Real.continuous_cos.comp (continuous_apply i)
    | inr i => exact Real.continuous_sin.comp (continuous_apply i)
  exact (continuous_const_smul ((Real.sqrt (m : ℝ))⁻¹)).comp hc

theorem phaseNormal_norm {m : ℕ} (hm : 0 < m) (θ : Fin m → ℝ) :
    ‖phaseNormal θ‖ = 1 := by
  have hs : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.2 hm))
  simp [phaseNormal, norm_smul, phaseVector_norm, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg (m : ℝ)), hs]

theorem phaseNormal_inner_neg {m : ℕ} (θ φ : Fin m → ℝ) :
    inner ℝ (phaseNormal θ) (phaseNormal (fun i => -φ i)) =
      (m : ℝ)⁻¹ * ∑ i, Real.cos (θ i + φ i) := by
  simp only [phaseNormal, real_inner_smul_left, real_inner_smul_right,
    phaseVector_inner_neg]
  rw [← mul_assoc, ← mul_inv, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg m)]

/-- Algebraic sine-sine extraction from the four Gaussian plane-wave pairings. -/
theorem gaussian_sine_extraction (A z : ℂ) :
    -(Complex.exp (-A - z * Complex.I) - Complex.exp (-A + z * Complex.I) -
        Complex.exp (-A + z * Complex.I) + Complex.exp (-A - z * Complex.I)) / 4 =
      Complex.I * Complex.exp (-A) * Complex.sin z := by
  rw [show -A - z * Complex.I = -A + (-z * Complex.I) by ring]
  simp only [Complex.exp_add, Complex.sin]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem integral_euclidean_pair_prod {ι : Type*} [Fintype ι] (F : ι → ℝ → ℝ → ℂ) :
    (∫ x : EuclideanSpace ℝ (ι), ∫ y : EuclideanSpace ℝ (ι),
      ∏ i, F i (x i) (y i)) = ∏ i, ∫ u : ℝ, ∫ v : ℝ, F i u v := by
  have h (f : EuclideanSpace ℝ (ι) → ℂ) :
      (∫ x : EuclideanSpace ℝ (ι), f x) =
        ∫ x : ι → ℝ, f (WithLp.toLp 2 x) := by
    symm
    exact (PiLp.volume_preserving_toLp (ι)).integral_comp
      (MeasurableEquiv.toLp 2 _).measurableEmbedding f
  rw [h]
  simp_rw [h]
  simp_rw [integral_fintype_prod_volume_eq_prod]
  exact integral_fintype_prod_volume_eq_prod (fun i u => ∫ v : ℝ, F i u v)

theorem integral_euclidean_cexp_sum_pair {ι : Type*} [Fintype ι] (F : ι → ℝ → ℝ → ℂ) :
    (∫ x : EuclideanSpace ℝ (ι), ∫ y : EuclideanSpace ℝ (ι),
      Complex.exp (∑ i, F i (x i) (y i))) =
        ∏ i, ∫ u : ℝ, ∫ v : ℝ, Complex.exp (F i u v) := by
  simp_rw [Complex.exp_sum]
  exact integral_euclidean_pair_prod (fun i u v => Complex.exp (F i u v))

theorem planeWave_exponent_eq_sum {ι : Type*} [Fintype ι]
    (u v x y : EuclideanSpace ℝ (ι)) :
    -(((‖x‖ : ℝ) : ℂ) ^ 2 + ((‖y‖ : ℝ) : ℂ) ^ 2) / 2 +
        Complex.I * (inner ℝ x y : ℝ) + Complex.I * (inner ℝ u x : ℝ) +
        Complex.I * (inner ℝ v y : ℝ) =
      ∑ i, (-((x i : ℂ) ^ 2 + (y i : ℂ) ^ 2) / 2 +
        Complex.I * x i * y i + Complex.I * u i * x i + Complex.I * v i * y i) := by
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib, Finset.sum_div]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end

end Konig
