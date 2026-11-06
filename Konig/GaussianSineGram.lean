module

public import Konig.SineApproximation
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable section

namespace Konig.GaussianSineGram

/-- The Gaussian probability measure with variance `1/2`, used by the Fourier normalization. -/
def gaussian : Measure ℝ := gaussianReal 0 (1 / 2)

instance : IsProbabilityMeasure gaussian := by unfold gaussian; infer_instance

instance : NullSingletonClass gaussian :=
  nullSingletonClass_gaussianReal (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)

theorem integrable_cos (s : ℝ) : Integrable (fun x : ℝ => Real.cos (s * x)) gaussian := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact ae_of_all _ fun x => by simpa using Real.abs_cos_le_one (s * x)

theorem integrable_sin_mul_sin (s t : ℝ) :
    Integrable (fun x : ℝ => Real.sin (s * x) * Real.sin (t * x)) gaussian := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem integral_cos (s : ℝ) :
    (∫ x, Real.cos (s * x) ∂gaussian) = Real.exp (-s ^ 2 / 4) := by
  have hi : Integrable (fun x : ℝ => Complex.exp ((s : ℂ) * x * Complex.I)) gaussian := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards [] with x
    simp [Complex.norm_exp]
  have h := congrArg Complex.re (charFun_gaussianReal (μ := 0) (v := 1 / 2) s)
  rw [charFun_apply_real] at h
  have hre : (∫ x, Complex.exp ((s : ℂ) * x * Complex.I) ∂gaussian).re =
      ∫ x, (Complex.exp ((s : ℂ) * x * Complex.I)).re ∂gaussian :=
    (integral_re hi).symm
  change (∫ x, Complex.exp ((s : ℂ) * x * Complex.I) ∂gaussian).re = _ at h
  rw [hre] at h
  simp [← Complex.ofReal_pow, Complex.exp_re, Complex.mul_re, Complex.mul_im] at h
  convert h using 1
  congr 1
  ring

theorem integral_sin_mul_sin (s t : ℝ) :
    (∫ x, Real.sin (s * x) * Real.sin (t * x) ∂gaussian) =
      Real.exp (-(s ^ 2 + t ^ 2) / 4) * Real.sinh (s * t / 2) := by
  have hid : (fun x : ℝ => Real.sin (s * x) * Real.sin (t * x)) =
      fun x => (Real.cos ((s - t) * x) - Real.cos ((s + t) * x)) / 2 := by
    funext x
    simp only [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  rw [hid, integral_div, integral_sub (integrable_cos _) (integrable_cos _),
    integral_cos, integral_cos, Real.sinh_eq]
  have h₁ : -(s - t) ^ 2 / 4 = -(s ^ 2 + t ^ 2) / 4 + s * t / 2 := by ring
  have h₂ : -(s + t) ^ 2 / 4 = -(s ^ 2 + t ^ 2) / 4 + -(s * t / 2) := by ring
  rw [h₁, h₂, Real.exp_add, Real.exp_add]
  ring

theorem integral_sine_sum_sq {ι : Type} [Fintype ι] (a s : ι → ℝ) :
    (∫ x, (∑ i, a i * Real.sin (s i * x)) ^ 2 ∂gaussian) =
      ∑ i, ∑ j, a i * a j *
        (Real.exp (-(s i ^ 2 + s j ^ 2) / 4) * Real.sinh (s i * s j / 2)) := by
  have hid (x : ℝ) : (∑ i, a i * Real.sin (s i * x)) ^ 2 =
      ∑ i, ∑ j, (a i * a j) * (Real.sin (s i * x) * Real.sin (s j * x)) := by
    simp only [pow_two, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hi (i j : ι) : Integrable (fun x =>
      (a i * a j) * (Real.sin (s i * x) * Real.sin (s j * x))) gaussian :=
    (integrable_sin_mul_sin (s i) (s j)).const_mul _
  simp_rw [hid]
  simp [integral_finsetSum, hi, integrable_finsetSum,
    integral_const_mul, integral_sin_mul_sin]

theorem exists_bounded_sine_gram {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (a s : Fin n → ℝ),
      (∀ x : ℝ, |∑ i, a i * Real.sin (s i * x)| ≤ 1) ∧
      1 - ε < ∑ i, ∑ j, a i * a j *
        (Real.exp (-(s i ^ 2 + s j ^ 2) / 4) * Real.sinh (s i * s j / 2)) := by
  obtain ⟨n, a, s, hb, hm⟩ :=
    SineApproximation.exists_bounded_sine_polynomial gaussian hε
  exact ⟨n, a, s, hb, by rwa [← integral_sine_sum_sq]⟩

end Konig.GaussianSineGram
