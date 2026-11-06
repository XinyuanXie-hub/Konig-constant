module

public import Konig.Definitions
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

open MeasureTheory

namespace Konig

theorem integrable_gaussian_mul (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-b * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := (b : ℂ)) hb 0 (0 : EuclideanSpace ℝ (Fin n))).re
  simpa [← Complex.ofReal_pow, Complex.exp_re] using h

theorem integrable_gaussian_weight (n : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-(‖x‖ ^ 2 / 2))) := by
  simpa only [neg_mul, div_eq_mul_inv, mul_comm] using
    integrable_gaussian_mul n (b := 2⁻¹) (by norm_num)

theorem gaussian_weight_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    Real.exp (-(‖x‖ ^ 2 / 2)) ^ 2 = Real.exp (-‖x‖ ^ 2) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

theorem integrable_weighted {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : AEMeasurable f volume) (hfb : ∀ x, |f x| ≤ 1) :
    Integrable (fun x => f x * Real.exp (-(‖x‖ ^ 2 / 2))) :=
  (integrable_gaussian_weight n).bdd_mul hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hfb)

theorem weighted_sq_le {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfb : ∀ x, |f x| ≤ 1) (x : EuclideanSpace ℝ (Fin n)) :
    (f x * Real.exp (-(‖x‖ ^ 2 / 2))) ^ 2 ≤ Real.exp (-‖x‖ ^ 2) := by
  rw [mul_pow, gaussian_weight_sq]
  exact (mul_le_mul_of_nonneg_right ((sq_le_one_iff_abs_le_one _).mpr (hfb x))
    (Real.exp_nonneg _)).trans_eq (one_mul _)

theorem integrable_weighted_sq {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : AEMeasurable f volume) (hfb : ∀ x, |f x| ≤ 1) :
    Integrable (fun x => (f x * Real.exp (-(‖x‖ ^ 2 / 2))) ^ 2) := by
  have hg : Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x‖ ^ 2)) := by
    simpa using integrable_gaussian_mul n (b := 1) (by norm_num)
  apply hg.mono'
  · exact ((hf.mul (by fun_prop)).pow_const 2).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f x * Real.exp (-(‖x‖ ^ 2 / 2))))]
    exact weighted_sq_le f hfb x

theorem memLp_weighted {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : AEMeasurable f volume) (hfb : ∀ x, |f x| ≤ 1) :
    MemLp (fun x => f x * Real.exp (-(‖x‖ ^ 2 / 2))) 2 :=
  (memLp_two_iff_integrable_sq (integrable_weighted f hf hfb).aestronglyMeasurable).mpr
    (integrable_weighted_sq f hf hfb)

theorem integral_weighted_sq_le {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : AEMeasurable f volume) (hfb : ∀ x, |f x| ≤ 1) :
    (∫ x, (f x * Real.exp (-(‖x‖ ^ 2 / 2))) ^ 2) ≤ Real.pi ^ ((n : ℝ) / 2) := by
  have hg : Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x‖ ^ 2)) := by
    simpa using integrable_gaussian_mul n (b := 1) (by norm_num)
  have he : (∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-‖x‖ ^ 2)) =
      Real.pi ^ ((n : ℝ) / 2) := by
    simpa using GaussianFourier.integral_rexp_neg_mul_sq_norm
      (V := EuclideanSpace ℝ (Fin n)) (b := 1) (by norm_num)
  rw [← he]
  exact integral_mono (integrable_weighted_sq f hf hfb) hg (weighted_sq_le f hfb)

theorem gaussian_weight_factor {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    Real.exp (-((‖x‖ ^ 2 + ‖y‖ ^ 2) / 2)) =
      Real.exp (-(‖x‖ ^ 2 / 2)) * Real.exp (-(‖y‖ ^ 2 / 2)) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem kernel_norm_le_gaussian {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ‖f x * g y * Real.exp (-((‖x‖ ^ 2 + ‖y‖ ^ 2) / 2)) *
        Real.sin (inner ℝ x y)‖ ≤
      Real.exp (-(‖x‖ ^ 2 / 2)) * Real.exp (-(‖y‖ ^ 2 / 2)) := by
  rw [← gaussian_weight_factor]
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (1 * 1) * Real.exp (-((‖x‖ ^ 2 + ‖y‖ ^ 2) / 2)) * 1 := by
      gcongr
      · exact hf x
      · exact hg y
      · exact Real.abs_sin_le_one _
    _ = _ := by ring

theorem integrable_kernel {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hfb : ∀ x, |f x| ≤ 1) (hgb : ∀ x, |g x| ≤ 1) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      f p.1 * g p.2 * Real.exp (-((‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) / 2)) *
        Real.sin (inner ℝ p.1 p.2)) (volume.prod volume) := by
  apply ((integrable_gaussian_weight n).mul_prod (integrable_gaussian_weight n)).mono'
  · apply AEMeasurable.aestronglyMeasurable
    exact ((hf.comp_fst.mul hg.comp_snd).mul
      (by fun_prop)).mul (by fun_prop)
  · exact Filter.Eventually.of_forall (fun p => kernel_norm_le_gaussian f g hfb hgb p.1 p.2)

end Konig
