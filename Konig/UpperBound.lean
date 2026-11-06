module

public import Konig.Definitions
public import Konig.Integrability
public import Konig.Normalization
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

open MeasureTheory FourierTransform
open scoped FourierTransform ContDiff SchwartzMap

noncomputable section
namespace Konig

/-- On `L¹ ∩ L²`, the integral Fourier transform agrees almost everywhere with
Mathlib's isometric `L²` Fourier transform. -/
theorem fourierIntegral_ae_eq_L2 {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (𝓕 f) =ᵐ[volume] (𝓕 hf2.toLp : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2 volume) := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf1).locallyIntegrable
  · exact (Lp.memLp (𝓕 hf2.toLp : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2 volume)).locallyIntegrable (by norm_num)
  intro g hg hgc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let s := hg₁.toSchwartzMap hg₂
  have hdual := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (μ := volume) (ν := volume) (L := innerₗ (EuclideanSpace ℝ (Fin n)))
    Real.continuous_fourierChar continuous_inner hf1 s.integrable
  have hdist := congrArg (fun d : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) => d s)
    (Lp.fourier_toTemperedDistribution_eq hf2.toLp)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hdist
  calc
    (∫ x, g x • 𝓕 f x) = ∫ x, s x * 𝓕 f x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp [s, Complex.real_smul]
    _ = ∫ x, (𝓕 s) x * f x := by
      simpa [Real.fourier_eq, SchwartzMap.fourier_coe, VectorFourier.fourierIntegral, mul_comm] using hdual
    _ = ∫ x, (𝓕 s) x * (hf2.toLp : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2 volume) x := by
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x, s x * (𝓕 hf2.toLp : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2 volume) x := by
      simpa only [smul_eq_mul] using hdist
    _ = ∫ x, g x • (𝓕 hf2.toLp : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2 volume) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp [s, Complex.real_smul]

/-- The square integral realizes the norm of the associated `L²` class. -/
theorem integral_norm_sq_eq_toLp_norm_sq {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : MemLp f 2) :
    (∫ x, ‖f x‖ ^ 2) = ‖hf.toLp f‖ ^ 2 := by
  calc
    (∫ x, ‖f x‖ ^ 2) = ∫ x, inner ℝ ((hf.toLp f) x) ((hf.toLp f) x) := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
    _ = ‖hf.toLp f‖ ^ 2 := by rw [← L2.inner_def, real_inner_self_eq_norm_sq]

/-- The classical Fourier integral of an `L¹ ∩ L²` function belongs to `L²`. -/
theorem memLp_fourier {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2) : MemLp (𝓕 f) 2 :=
  (memLp_congr_ae (fourierIntegral_ae_eq_L2 hf1 hf2)).mpr (Lp.memLp _)

/-- Integral Plancherel for arbitrary complex `L¹ ∩ L²` functions. -/
theorem integral_norm_sq_fourier {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (∫ x, ‖𝓕 f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  rw [integral_norm_sq_eq_toLp_norm_sq (memLp_fourier hf1 hf2),
    integral_norm_sq_eq_toLp_norm_sq hf2,
    MemLp.toLp_congr (memLp_fourier hf1 hf2) (Lp.memLp _)
      (fourierIntegral_ae_eq_L2 hf1 hf2), Lp.toLp_coeFn, Lp.norm_fourier_eq]

set_option maxHeartbeats 400000 in
/-- Cauchy–Schwarz and integral Plancherel, including the frequency scaling
needed for the unscaled sine kernel in the König form. -/
theorem norm_integral_fourier_mul_scaled_le {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2) (hg2 : MemLp g 2)
    {a : ℝ} (ha : a ≠ 0) :
    ‖∫ y, 𝓕 f (a • y) * g y‖ ≤
      Real.sqrt (|(a ^ n)⁻¹| * ∫ x, ‖f x‖ ^ 2) * Real.sqrt (∫ y, ‖g y‖ ^ 2) := by
  have hF := memLp_fourier hf1 hf2
  have hFc : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf1
  have hc : Continuous (fun y : EuclideanSpace ℝ (Fin n) => a • y) :=
    continuous_const_smul a
  have hFm : AEStronglyMeasurable (fun y => 𝓕 f (a • y)) volume :=
    (hFc.comp hc).aestronglyMeasurable
  have hFi : Integrable (fun y => ‖𝓕 f y‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hFs : MemLp (fun y => 𝓕 f (a • y)) 2 :=
    (memLp_two_iff_integrable_sq_norm hFm).mpr (hFi.comp_smul ha)
  have hs : (∫ y, ‖𝓕 f (a • y)‖ ^ 2) = |(a ^ n)⁻¹| * ∫ x, ‖f x‖ ^ 2 := by
    rw [Measure.integral_comp_smul volume (fun x => ‖𝓕 f x‖ ^ 2) a]
    simp [integral_norm_sq_fourier hf1 hf2, finrank_euclideanSpace]
  calc
    ‖∫ y, 𝓕 f (a • y) * g y‖ ≤ ∫ y, ‖𝓕 f (a • y) * g y‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ y, ‖𝓕 f (a • y)‖ * ‖g y‖ := by simp only [norm_mul]
    _ ≤ Real.sqrt (∫ y, ‖𝓕 f (a • y)‖ ^ 2) * Real.sqrt (∫ y, ‖g y‖ ^ 2) := by
      have hh : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
      simpa [Real.sqrt_eq_rpow] using
        integral_mul_norm_le_Lp_mul_Lq hh (by simpa using hFs) (by simpa using hg2)
    _ = _ := by rw [hs]

/-- The imaginary part of the integral Fourier transform at the frequency
`-y/(2π)` is the sine transform with unscaled inner-product phase. -/
theorem im_fourier_neg_inv_two_pi {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Integrable u)
    (y : EuclideanSpace ℝ (Fin n)) :
    (𝓕 (fun x => (u x : ℂ)) ((-(2 * Real.pi)⁻¹) • y)).im =
      ∫ x, u x * Real.sin (inner ℝ x y) := by
  rw [Real.fourier_eq]
  change RCLike.im (∫ v, Real.fourierChar (-inner ℝ v ((-(2 * Real.pi)⁻¹) • y)) • (u v : ℂ)) = _
  rw [← integral_im ((Real.fourierIntegral_convergent_iff _).mpr hu.ofReal)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Circle.smul_def, Real.fourierChar_apply, Complex.exp_im, mul_comm]
  left
  congr 1
  rw [inner_smul_right]
  field_simp

/-- The dimension-independent Fourier upper bound for the exact König form. -/
theorem abs_bilinear_le_one {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hfb : ∀ x, |f x| ≤ 1) (hgb : ∀ x, |g x| ≤ 1) :
    |bilinear f g| ≤ 1 := by
  let u := fun x => f x * Real.exp (-(‖x‖ ^ 2 / 2))
  let v := fun x => g x * Real.exp (-(‖x‖ ^ 2 / 2))
  let F := fun x => (u x : ℂ)
  let G := fun x => (v x : ℂ)
  let a := -(2 * Real.pi)⁻¹
  let I := ∫ y, 𝓕 F (a • y) * G y
  have hu : Integrable u := integrable_weighted f hf hfb
  have hv : Integrable v := integrable_weighted g hg hgb
  have hF1 : Integrable F := hu.ofReal
  have hG1 : Integrable G := hv.ofReal
  have hF2 : MemLp F 2 := (memLp_weighted f hf hfb).ofReal
  have hG2 : MemLp G 2 := (memLp_weighted g hg hgb).ofReal
  have hFc : Continuous (𝓕 F) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hF1
  have hJ : Integrable (fun y => 𝓕 F (a • y) * G y) := by
    apply hG1.bdd_mul ((hFc.comp (continuous_const_smul a)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun y => Real.norm_fourier_le_integral_norm F (a • y))
  have him : I.im = ∫ y, v y * ∫ x, u x * Real.sin (inner ℝ x y) := by
    change RCLike.im (∫ y, 𝓕 F (a • y) * G y) = _
    rw [← integral_im hJ]
    apply integral_congr_ae
    filter_upwards [] with y
    change (𝓕 F (a • y) * (v y : ℂ)).im = _
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
    change (𝓕 (fun x => (u x : ℂ)) (a • y)).im * v y = _
    rw [im_fourier_neg_inv_two_pi hu]
    ring
  have hb : bilinear f g = ((Real.sqrt 2 * Real.pi) ^ n)⁻¹ * I.im := by
    rw [bilinear, him, integral_integral_swap (integrable_kernel f g hf hg hfb hgb)]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [u, v]
    rw [gaussian_weight_factor]
    ring
  have ha : a ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hscale : |(a ^ n)⁻¹| = (2 * Real.pi) ^ n := by
    calc
      |(a ^ n)⁻¹| = |a⁻¹| ^ n := by rw [← inv_pow, abs_pow]
      _ = _ := by simp [a, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)]
  have hboundF : (∫ x, ‖F x‖ ^ 2) ≤ Real.pi ^ ((n : ℝ) / 2) := by
    simpa only [F, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      integral_weighted_sq_le f hf hfb
  have hboundG : (∫ x, ‖G x‖ ^ 2) ≤ Real.pi ^ ((n : ℝ) / 2) := by
    simpa only [G, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      integral_weighted_sq_le g hg hgb
  have hnorm : ‖I‖ ≤ Real.sqrt ((2 * Real.pi) ^ n * Real.pi ^ ((n : ℝ) / 2)) *
      Real.sqrt (Real.pi ^ ((n : ℝ) / 2)) := by
    have h := norm_integral_fourier_mul_scaled_le hF1 hF2 hG2 ha
    rw [hscale] at h
    apply h.trans
    gcongr
  rw [hb, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((Real.sqrt 2 * Real.pi) ^ n)⁻¹)]
  calc
    _ ≤ ((Real.sqrt 2 * Real.pi) ^ n)⁻¹ * ‖I‖ := by
      gcongr
      exact Complex.abs_im_le_norm I
    _ ≤ ((Real.sqrt 2 * Real.pi) ^ n)⁻¹ *
        (Real.sqrt ((2 * Real.pi) ^ n * Real.pi ^ ((n : ℝ) / 2)) *
          Real.sqrt (Real.pi ^ ((n : ℝ) / 2))) := by gcongr
    _ = 1 := gaussian_normalization n

end Konig
