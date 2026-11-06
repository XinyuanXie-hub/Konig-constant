module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

open MeasureTheory

noncomputable section

namespace Konig

private lemma re_add_inv_pos {a : ℂ} (ha : 0 < a.re) :
    0 < (a + 1 / (4 * a)).re := by
  rw [Complex.add_re, one_div, Complex.inv_re]
  have h : 0 < (4 * a).re := by simpa using (mul_pos (by norm_num : (0 : ℝ) < 4) ha)
  exact add_pos_of_pos_of_nonneg ha (div_nonneg h.le (Complex.normSq_nonneg _))

/-- Evaluates the two-variable oscillatory Gaussian by successive scalar integrals.
The two powers are principal complex square roots of numbers with positive real part. -/
theorem integral_cexp_pair {a : ℂ} (ha : 0 < a.re) (d : ℂ) :
    (∫ u : ℝ, ∫ v : ℝ,
      Complex.exp (-a * ((u : ℂ) ^ 2 + (v : ℂ) ^ 2) +
        Complex.I * u * v + d)) =
      ((Real.pi : ℂ) / a) ^ (1 / 2 : ℂ) *
      ((Real.pi : ℂ) / (a + 1 / (4 * a))) ^ (1 / 2 : ℂ) * Complex.exp d := by
  have han : (-a).re < 0 := by simpa using (neg_neg_of_pos ha)
  have ha0 : a ≠ 0 := by intro h; simpa [h] using ha
  have hinner (u : ℝ) :
      (∫ v : ℝ, Complex.exp (-a * ((u : ℂ) ^ 2 + (v : ℂ) ^ 2) +
        Complex.I * u * v + d)) =
      ((Real.pi : ℂ) / a) ^ (1 / 2 : ℂ) *
        Complex.exp (-(a + 1 / (4 * a)) * (u : ℂ) ^ 2 + d) := by
    calc
      _ = ∫ v : ℝ, Complex.exp ((-a) * (v : ℂ) ^ 2 +
          (Complex.I * u) * v + (-a * (u : ℂ) ^ 2 + d)) := by
        congr 1; ext v; congr 1; ring
      _ = _ := by
        rw [integral_cexp_quadratic han, neg_neg]
        congr 2
        field_simp
        simp [Complex.I_sq]
        ring
  simp_rw [hinner]
  rw [integral_const_mul]
  have hneg : (-(a + 1 / (4 * a))).re < 0 := by
    simpa using neg_neg_of_pos (re_add_inv_pos ha)
  have hout := integral_cexp_quadratic hneg (0 : ℂ) d
  simp only [zero_mul, add_zero, pow_two, zero_div, sub_zero, neg_neg] at hout
  simp only [pow_two]
  rw [hout, mul_assoc]

/-- The scalar phase integral in the Hadamard construction (source equation 3.1). -/
def scalarPhase (t : ℝ) : ℂ :=
  ((Real.sqrt 2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ u : ℝ, ∫ v : ℝ,
      Complex.exp (-((1 - Complex.I * t) / 2) *
        ((u : ℂ) ^ 2 + (v : ℂ) ^ 2) + Complex.I * u * v - Complex.I * t / 2)

/-- Exact branch-safe evaluation using two principal Gaussian square roots. -/
theorem scalarPhase_eq (t : ℝ) :
    scalarPhase t =
      ((Real.sqrt 2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ((Real.pi : ℂ) / ((1 - Complex.I * t) / 2)) ^ (1 / 2 : ℂ) *
      ((Real.pi : ℂ) / ((1 - Complex.I * t) / 2 +
        1 / (4 * ((1 - Complex.I * t) / 2)))) ^ (1 / 2 : ℂ) *
      Complex.exp (-Complex.I * t / 2) := by
  have ha : 0 < (((1 : ℂ) - Complex.I * t) / 2).re := by simp
  unfold scalarPhase
  have h := integral_cexp_pair ha (-Complex.I * t / 2)
  have he : ∀ u v : ℝ,
      -((1 - Complex.I * t) / 2) * ((u : ℂ)^2 + (v : ℂ)^2) +
        Complex.I * u * v - Complex.I * t / 2 =
      -((1 - Complex.I * t) / 2) * ((u : ℂ)^2 + (v : ℂ)^2) +
        Complex.I * u * v + (-Complex.I * t / 2) := by intros; ring
  simp_rw [he]
  rw [h]
  ring

/-- The scalar denominator has no real zeros. -/
theorem scalar_denominator_normSq (t : ℝ) :
    Complex.normSq (1 - Complex.I * t - (t : ℂ) ^ 2 / 2) = 1 + t ^ 4 / 4 := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
  ring

theorem scalar_denominator_ne_zero (t : ℝ) :
    1 - Complex.I * t - (t : ℂ) ^ 2 / 2 ≠ 0 := by
  intro h
  have hn := scalar_denominator_normSq t
  rw [h] at hn
  norm_num at hn
  nlinarith [sq_nonneg (t ^ 2)]

/-- Branch-free exact identity for the square of the source scalar phase. -/
theorem scalarPhase_sq (t : ℝ) :
    scalarPhase t ^ 2 = Complex.exp (-Complex.I * t) /
      (1 - Complex.I * t - (t : ℂ) ^ 2 / 2) := by
  have hs (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ (2 : ℕ) = z := by
    simpa using Complex.cpow_nat_inv_pow z (n := 2) (by decide)
  have ha : ((1 : ℂ) - Complex.I * t) / 2 ≠ 0 := by
    have hr : (((1 : ℂ) - Complex.I * t) / 2).re = 1 / 2 := by simp
    intro h; rw [h] at hr; norm_num at hr
  have hb : (1 - Complex.I * t) / 2 + 1 / (4 * ((1 - Complex.I * t) / 2)) ≠ 0 := by
    have hr := re_add_inv_pos (a := (1 - Complex.I * t) / 2) (by simp)
    intro h; rw [h] at hr; simpa using hr
  have h1 : (1 : ℂ) - Complex.I * t ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hr : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have he : Complex.exp (-Complex.I * t / 2) ^ (2 : ℕ) = Complex.exp (-Complex.I * t) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  rw [scalarPhase_eq]
  simp only [mul_pow, hs, he, Complex.ofReal_mul, inv_pow, hr]
  field_simp [ha, hb, hp, h1, scalar_denominator_ne_zero t]
  ring_nf
  simp [Complex.I_sq]
  field_simp
  rw [show (8 : ℂ) * (1 - Complex.I * t) + -((t : ℂ)^2 * 4) =
      4 * ((1 - Complex.I * t) * 2 - (t : ℂ)^2) by ring, ← div_div]
  norm_num

private lemma cpow_half_ofReal (r : ℝ) (hr : 0 ≤ r) :
    (r : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt r : ℂ) := by
  rw [Real.sqrt_eq_rpow]
  simpa using (Complex.ofReal_cpow hr (1 / 2)).symm

theorem gaussian_pair_prefactor :
    ((Real.pi : ℂ) / (1 / 2)) ^ (1 / 2 : ℂ) *
      (Real.pi : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt 2 * Real.pi : ℝ) : ℂ) := by
  rw [show (Real.pi : ℂ) / (1 / 2) = ((Real.pi * 2 : ℝ) : ℂ) by push_cast; ring]
  rw [cpow_half_ofReal _ (by positivity), cpow_half_ofReal _ Real.pi_pos.le]
  norm_cast
  rw [Real.sqrt_mul Real.pi_pos.le]
  calc
    _ = Real.sqrt 2 * (Real.sqrt Real.pi)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt Real.pi_pos.le]

theorem scalarPhase_zero : scalarPhase 0 = 1 := by
  rw [scalarPhase_eq]
  norm_num
  rw [mul_assoc, gaussian_pair_prefactor, Complex.ofReal_mul, ← mul_inv_rev, inv_mul_cancel₀]
  exact_mod_cast mul_ne_zero
    (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)) Real.pi_ne_zero

theorem continuousAt_scalarPhase_zero : ContinuousAt scalarPhase 0 := by
  change ContinuousAt (fun t : ℝ => scalarPhase t) 0
  simp_rw [scalarPhase_eq]
  have hA : ContinuousAt (fun t : ℝ => (Real.pi : ℂ) / ((1 - Complex.I * t) / 2)) 0 := by
    fun_prop (disch := norm_num)
  have hB : ContinuousAt (fun t : ℝ => (Real.pi : ℂ) /
      ((1 - Complex.I * t) / 2 + 1 / (4 * ((1 - Complex.I * t) / 2)))) 0 := by
    fun_prop (disch := norm_num)
  have hpA := hA.cpow (continuousAt_const (y := (1 / 2 : ℂ))) (by
    apply Or.inl
    norm_num [Complex.div_re]
    positivity)
  have hpB := hB.cpow (continuousAt_const (y := (1 / 2 : ℂ))) (by
    apply Or.inl
    norm_num [Complex.div_re]
    exact Real.pi_pos)
  exact ((continuousAt_const.mul hpA).mul hpB).mul (by fun_prop)

theorem scalarPhase_norm_le_one (t : ℝ) : ‖scalarPhase t‖ ≤ 1 := by
  have hd := scalar_denominator_normSq t
  rw [Complex.normSq_eq_norm_sq] at hd
  have hd1 : 1 ≤ ‖1 - Complex.I * t - (t : ℂ)^2 / 2‖ := by
    nlinarith [norm_nonneg (1 - Complex.I * t - (t : ℂ)^2 / 2), sq_nonneg (t^2)]
  have hn := congrArg norm (scalarPhase_sq t)
  rw [norm_pow, norm_div, Complex.norm_exp] at hn
  have he : (-Complex.I * (t : ℂ)).re = 0 := by simp
  rw [he, Real.exp_zero] at hn
  have hle : ‖scalarPhase t‖ ^ 2 ≤ 1 := by
    rw [hn]
    exact (div_le_one (lt_of_lt_of_le zero_lt_one hd1)).2 hd1
  nlinarith [norm_nonneg (scalarPhase t)]

end Konig
