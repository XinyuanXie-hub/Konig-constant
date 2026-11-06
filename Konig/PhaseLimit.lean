module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Konig.ScalarGaussian
public import Konig.HadamardFactorization
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace Konig
namespace PhaseLimit

/-- The first uncancelled term in the squared scalar phase is quartic. -/
theorem exp_cubic_residual :
    (fun z : ℂ => Complex.exp z - (1 + z + z ^ 2 / 2) * Complex.exp (z ^ 3 / 6))
      =O[𝓝 0] (fun z => z ^ 4) := by
  have h₁ : (fun z : ℂ => Complex.exp z - (1 + z + z ^ 2 / 2 + z ^ 3 / 6))
      =O[𝓝 0] (fun z => z ^ 4) := by
    simpa [Finset.sum_range_succ, Nat.factorial] using
      Complex.exp_sub_sum_range_isBigO_pow 4
  have h₂ : (fun z : ℂ => Complex.exp (z ^ 3 / 6) - 1 - z ^ 3 / 6)
      =O[𝓝 0] (fun z => z ^ 6) := by
    have h := (Complex.exp_sub_sum_range_isBigO_pow 2).comp_tendsto
      (show Tendsto (fun z : ℂ => z ^ 3 / 6) (𝓝 0) (𝓝 0) by
        simpa using (show ContinuousAt (fun z : ℂ => z ^ 3 / 6) 0 by fun_prop).tendsto)
    have he : (fun z : ℂ => (z ^ 3 / 6) ^ 2) = fun z => (1 / 36 : ℂ) * z ^ 6 := by
      funext z; ring
    simp only [Function.comp_def] at h
    rw [he] at h
    apply h.congr_left ?_ |>.trans (isBigO_const_mul_self _ _ _)
    intro z
    simp [Finset.sum_range_succ, Nat.factorial, sub_add_eq_sub_sub]
  have hd : (fun z : ℂ => 1 + z + z ^ 2 / 2) =O[𝓝 0] (fun _ => (1 : ℂ)) :=
    (show Tendsto (fun z : ℂ => 1 + z + z ^ 2 / 2) (𝓝 0) (𝓝 1) by
      simpa using (show ContinuousAt (fun z : ℂ => 1 + z + z ^ 2 / 2) 0 by fun_prop).tendsto).isBigO_one ℂ
  have h₂' : (fun z : ℂ => (1 + z + z ^ 2 / 2) *
      (Complex.exp (z ^ 3 / 6) - 1 - z ^ 3 / 6)) =O[𝓝 0] (fun z => z ^ 4) := by
    simpa only [one_mul] using hd.mul (h₂.trans (isLittleO_pow_pow (by decide : 4 < 6)).isBigO)
  have h₄ : (fun z : ℂ => z ^ 4 / 6) =O[𝓝 0] (fun z => z ^ 4) := by
    simpa [div_eq_mul_inv, mul_comm] using
      isBigO_const_mul_self (1 / 6 : ℂ) (fun z : ℂ => z ^ 4) (𝓝 0)
  have h₅ : (fun z : ℂ => z ^ 5 / 12) =O[𝓝 0] (fun z => z ^ 4) := by
    have h := (isLittleO_pow_pow (𝕜 := ℂ) (by decide : 4 < 5)).isBigO.const_mul_left (1 / 12 : ℂ)
    simpa [div_eq_mul_inv, mul_comm] using h
  convert ((h₁.sub h₂').sub h₄).sub h₅ using 1
  funext z
  ring

/-- A continuous choice of the square root near one inherits its squared error. -/
theorem root_error_isBigO {α : Type*} {l : Filter α} {f g h : α → ℂ}
    (hf : Tendsto f l (𝓝 1)) (hg : Tendsto g l (𝓝 1))
    (hsq : (fun x => f x ^ 2 - g x ^ 2) =O[l] h) :
    (fun x => f x - g x) =O[l] h := by
  have hsum : Tendsto (fun x => f x + g x) l (𝓝 (2 : ℂ)) := by
    convert hf.add hg using 1 <;> norm_num
  have hinv : (fun x => (f x + g x)⁻¹) =O[l] (fun _ => (1 : ℂ)) :=
    (hsum.inv₀ (by norm_num)).isBigO_one ℂ
  have heq : (fun x => (f x ^ 2 - g x ^ 2) * (f x + g x)⁻¹)
      =ᶠ[l] (fun x => f x - g x) := by
    filter_upwards [hsum.eventually_ne (by norm_num : (2 : ℂ) ≠ 0)] with x hx
    field_simp
    <;> ring
  simpa only [mul_one] using (hsq.mul hinv).congr' heq Filter.EventuallyEq.rfl

/-- Branch-free scalar cubic phase asymptotics. The hypotheses select the
continuous square root equal to one at zero, as supplied by the Gaussian integral. -/
theorem scalar_cubic_asymptotic {ψ : ℝ → ℂ}
    (hψ : ContinuousAt ψ 0) (hzero : ψ 0 = 1)
    (hsq : ∀ t : ℝ, ψ t ^ 2 = Complex.exp (-Complex.I * t) /
      (1 - Complex.I * t - (t : ℂ) ^ 2 / 2)) :
    (fun t : ℝ => ψ t - Complex.exp (Complex.I * (t : ℂ) ^ 3 / 12))
      =O[𝓝 0] (fun t => (t : ℂ) ^ 4) := by
  have hlin : Tendsto (fun t : ℝ => -Complex.I * t) (𝓝 0) (𝓝 0) := by
    simpa using (show ContinuousAt (fun t : ℝ => -Complex.I * t) 0 by fun_prop).tendsto
  have hr := exp_cubic_residual.comp_tendsto hlin
  have hcub (t : ℝ) : (-Complex.I * (t : ℂ)) ^ 3 / 6 =
      Complex.I * (t : ℂ) ^ 3 / 6 := by
    rw [mul_pow]
    have hi : (-Complex.I) ^ 3 = Complex.I := by
      ring_nf
      rw [Complex.I_pow_three]
      ring
    rw [hi]
  have hfour (t : ℝ) : (-Complex.I * (t : ℂ)) ^ 4 = (t : ℂ) ^ 4 := by
    rw [mul_pow]
    have hi : (-Complex.I) ^ 4 = 1 := by
      ring_nf
      exact Complex.I_pow_four
    rw [hi, one_mul]
  have hden (t : ℝ) : 1 + -Complex.I * (t : ℂ) + (-Complex.I * (t : ℂ)) ^ 2 / 2 =
      1 - Complex.I * t - (t : ℂ) ^ 2 / 2 := by
    simp [mul_pow, Complex.I_sq]
    ring
  simp only [Function.comp_def, hcub, hfour, hden] at hr
  have hd : ContinuousAt (fun t : ℝ => 1 - Complex.I * t - (t : ℂ) ^ 2 / 2) 0 := by
    fun_prop
  have hd0 : (1 : ℂ) - Complex.I * (0 : ℝ) - ((0 : ℝ) : ℂ) ^ 2 / 2 ≠ 0 := by simp
  have hi := (hd.inv₀ hd0).tendsto.isBigO_one ℂ
  have herr : (fun t : ℝ => ψ t ^ 2 -
      (Complex.exp (Complex.I * (t : ℂ) ^ 3 / 12)) ^ 2)
      =O[𝓝 0] (fun t => (t : ℂ) ^ 4) := by
    have heq : (fun t : ℝ =>
        (Complex.exp (-Complex.I * t) -
          (1 - Complex.I * t - (t : ℂ) ^ 2 / 2) *
            Complex.exp (Complex.I * (t : ℂ) ^ 3 / 6)) *
        (1 - Complex.I * t - (t : ℂ) ^ 2 / 2)⁻¹) =ᶠ[𝓝 0]
        (fun t => ψ t ^ 2 - (Complex.exp (Complex.I * (t : ℂ) ^ 3 / 12)) ^ 2) := by
      filter_upwards [hd.eventually_ne hd0] with t ht
      rw [hsq]
      have he : (Complex.exp (Complex.I * (t : ℂ) ^ 3 / 12)) ^ 2 =
          Complex.exp (Complex.I * (t : ℂ) ^ 3 / 6) := by
        rw [pow_two, ← Complex.exp_add]
        congr 1
        ring
      rw [he]
      generalize hdv : (1 - Complex.I * (t : ℂ) - (t : ℂ) ^ 2 / 2) = d at ht ⊢
      field_simp [ht]
      <;> ring
    simpa only [mul_one] using (hr.mul hi).congr' heq Filter.EventuallyEq.rfl
  apply root_error_isBigO (hzero ▸ hψ.tendsto) _ herr
  simpa using (show ContinuousAt
    (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ) ^ 3 / 12)) 0 by fun_prop).tendsto

theorem scalarPhase_cubic_asymptotic :
    (fun t : ℝ => scalarPhase t - Complex.exp (Complex.I * (t : ℂ) ^ 3 / 12))
      =O[𝓝 0] (fun t => (t : ℂ) ^ 4) :=
  scalar_cubic_asymptotic continuousAt_scalarPhase_zero scalarPhase_zero scalarPhase_sq

/-- Telescoping controls the error of a product of contractions. -/
theorem norm_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (a b : ι → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖(∏ i ∈ s, a i) - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    have has : ∀ j ∈ s, ‖a j‖ ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hbs : ∀ j ∈ s, ‖b j‖ ≤ 1 := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hpa : ‖∏ j ∈ s, a j‖ ≤ 1 :=
      (Finset.norm_prod_le s a).trans (Finset.prod_le_one₀ (fun j _ => norm_nonneg _) has)
    rw [Finset.prod_insert his, Finset.prod_insert his, Finset.sum_insert his]
    calc
      _ = ‖(a i - b i) * (∏ j ∈ s, a j) + b i *
          ((∏ j ∈ s, a j) - ∏ j ∈ s, b j)‖ := by congr 1; ring
      _ ≤ ‖(a i - b i) * (∏ j ∈ s, a j)‖ +
          ‖b i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j)‖ := norm_add_le _ _
      _ = ‖a i - b i‖ * ‖∏ j ∈ s, a j‖ +
          ‖b i‖ * ‖(∏ j ∈ s, a j) - ∏ j ∈ s, b j‖ := by simp only [norm_mul]
      _ ≤ ‖a i - b i‖ * 1 + 1 * (∑ j ∈ s, ‖a j - b j‖) := by
        gcongr
        · exact hb i (Finset.mem_insert_self _ _)
        · exact ih has hbs
      _ = _ := by ring

theorem geometric_cubic_scale (c : ℝ) (r : ℕ) :
    (8 : ℝ) ^ r * (c / 2 ^ r) ^ 3 = c ^ 3 := by
  have h : (2 : ℝ) ^ r ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_pow]
  have he : (8 : ℝ) ^ r = (2 ^ r) ^ 3 := by rw [← pow_mul, mul_comm r 3, pow_mul]; norm_num
  rw [he]
  field_simp

theorem geometric_quartic_scale (c : ℝ) (r : ℕ) :
    (8 : ℝ) ^ r * (c / 2 ^ r) ^ 4 = c ^ 4 * (1 / 2 : ℝ) ^ r := by
  have he : ((2 : ℝ) ^ r) ^ 4 = (16 : ℝ) ^ r := by
    rw [← pow_mul, mul_comm r 4, pow_mul]
    norm_num
  rw [div_pow, he]
  calc
    _ = c ^ 4 * ((8 : ℝ) ^ r / 16 ^ r) := by ring
    _ = _ := by rw [← div_pow]; norm_num

theorem geometric_quartic_tendsto_zero (c : ℝ) :
    Tendsto (fun r : ℕ => (8 : ℝ) ^ r * (c / 2 ^ r) ^ 4) atTop (𝓝 0) := by
  simp_rw [geometric_quartic_scale]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (c ^ 4)

theorem scalarPhase_product_norm_le_one {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    ‖∏ i, scalarPhase (t i)‖ ≤ 1 :=
  (Finset.norm_prod_le _ _).trans
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => scalarPhase_norm_le_one _))

theorem prod_exp_cubic {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    (∏ i, Complex.exp (Complex.I * (t i : ℂ) ^ 3 / 12)) =
      Complex.exp (Complex.I * (∑ i, (t i : ℂ) ^ 3) / 12) := by
  rw [← Complex.exp_sum]
  congr 1
  simp [Finset.mul_sum, Finset.sum_div]

/-- One pair of constants works uniformly in the number of factors and arguments. -/
theorem scalarPhase_product_error_uniform :
    ∃ C > 0, ∃ δ > 0, ∀ {ι : Type*} [Fintype ι] (t : ι → ℝ) (u : ℝ),
      (∀ i, |t i| ≤ u) → u < δ →
      ‖(∏ i, scalarPhase (t i)) -
        Complex.exp (Complex.I * (∑ i, (t i : ℂ) ^ 3) / 12)‖ ≤
          C * ((Fintype.card ι : ℝ) * u ^ 4) := by
  obtain ⟨C, hC, hlocal⟩ := isBigO_iff'.mp scalarPhase_cubic_asymptotic
  obtain ⟨δ, hδ, hlocal⟩ := Metric.eventually_nhds_iff.mp hlocal
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro ι inst t u htu huδ
  rw [← prod_exp_cubic]
  calc
    _ ≤ ∑ i, ‖scalarPhase (t i) - Complex.exp (Complex.I * (t i : ℂ) ^ 3 / 12)‖ :=
      norm_prod_sub_prod_le_sum Finset.univ _ _
        (fun i _ => scalarPhase_norm_le_one _)
        (fun i _ => by simp [Complex.norm_exp, ← Complex.ofReal_pow, Complex.mul_re])
    _ ≤ ∑ _i : ι, C * u ^ 4 := by
      apply Finset.sum_le_sum
      intro i hi
      have htδ : dist (t i) 0 < δ := by simpa [Real.dist_eq] using (htu i).trans_lt huδ
      have hpt := hlocal htδ
      simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs] at hpt
      exact hpt.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (htu i) _) hC.le)
    _ = _ := by simp; ring

/-- Uniformly small scalar arguments with a vanishing fourth-power budget give
the cubic phase product limit, even when the number of factors grows. -/
theorem scalarPhase_product_error_tendsto {ι : ℕ → Type*} [∀ r, Fintype (ι r)]
    (t : ∀ r, ι r → ℝ) (u : ℕ → ℝ)
    (htu : ∀ r i, |t r i| ≤ u r)
    (hu : Tendsto u atTop (𝓝 0))
    (hbudget : Tendsto (fun r => (Fintype.card (ι r) : ℝ) * u r ^ 4) atTop (𝓝 0)) :
    Tendsto (fun r => (∏ i, scalarPhase (t r i)) -
      ∏ i, Complex.exp (Complex.I * (t r i : ℂ) ^ 3 / 12)) atTop (𝓝 0) := by
  obtain ⟨C, _, δ, hδ, hbound⟩ := scalarPhase_product_error_uniform
  apply squeeze_zero_norm' (a := fun r => C * ((Fintype.card (ι r) : ℝ) * u r ^ 4))
  · filter_upwards [hu.eventually (gt_mem_nhds hδ)] with r hr
    rw [prod_exp_cubic]
    exact hbound (t r) (u r) (htu r) hr
  · simpa using hbudget.const_mul C

open Construction in
theorem phaseFrequency_cubic_sum {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (hH : H.IsHadamard) (ε : ℝ) (μ : Fin m → ℝ) :
    (∑ i, (phaseFrequency H ε μ i) ^ 3) =
      2 * (m : ℝ) * ε ^ 3 * ((∑ s, μ s) ^ 3 + 3 * (∑ s, μ s) * ∑ s, (μ s) ^ 2) := by
  simp only [phaseFrequency, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_pow]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add, ← Finset.sum_add_distrib,
    hadamard_cubic_sum H hH]
  simp only [Fintype.card_fin]
  ring

open Construction in
theorem phaseFrequency_abs_le {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (hH : H.IsHadamard) (ε : ℝ) (μ : Fin m → ℝ) (k : ℝ)
    (hμ : ∑ s, |μ s| ≤ k) (i : Fin m ⊕ Fin m) :
    |phaseFrequency H ε μ i| ≤ |ε| * (2 * k) := by
  cases i with
  | inl j =>
    simp only [phaseFrequency, Sum.elim_inl, abs_mul]
    exact mul_le_mul_of_nonneg_left
      ((hadamard_plus_frequency_abs H hH μ j).trans
        (mul_le_mul_of_nonneg_left hμ (by norm_num))) (abs_nonneg _)
  | inr j =>
    simp only [phaseFrequency, Sum.elim_inr, abs_mul]
    exact mul_le_mul_of_nonneg_left
      ((hadamard_minus_frequency_abs H hH μ j).trans
        (mul_le_mul_of_nonneg_left hμ (by norm_num))) (abs_nonneg _)

open Construction in
/-- The quantitative estimate needed before averaging channel assignments.
The constants are uniform in dimension, frequencies and Hadamard matrix. -/
theorem hadamard_phase_product_error_uniform :
    ∃ C > 0, ∃ δ > 0, ∀ (m : ℕ) (H : Matrix (Fin m) (Fin m) ℝ),
      H.IsHadamard → ∀ (ε : ℝ) (μ : Fin m → ℝ) (k : ℝ),
      (∑ s, |μ s|) ≤ k → |ε| * (2 * k) < δ →
      (m : ℝ) * ε ^ 3 = 3 * Real.pi →
      ‖(∏ i, scalarPhase (phaseFrequency H ε μ i)) -
        Complex.exp ((Real.pi : ℂ) * Complex.I / 2 *
          (((∑ s, μ s : ℝ) : ℂ) ^ 3 +
            3 * ((∑ s, μ s : ℝ) : ℂ) * ((∑ s, (μ s) ^ 2 : ℝ) : ℂ)))‖ ≤
        C * (m : ℝ) * ε ^ 4 * (2 * k) ^ 4 := by
  obtain ⟨C, hC, δ, hδ, h⟩ := scalarPhase_product_error_uniform
  refine ⟨2 * C, by positivity, δ, hδ, ?_⟩
  intro m H hH ε μ k hμ hsmall hscale
  have hb := h (phaseFrequency H ε μ) (|ε| * (2 * k))
    (phaseFrequency_abs_le H hH ε μ k hμ) hsmall
  have hscaleC : (m : ℂ) * (ε : ℂ) ^ 3 = 3 * (Real.pi : ℂ) := by
    exact_mod_cast hscale
  have he : Complex.I * (∑ i, (phaseFrequency H ε μ i : ℂ) ^ 3) / 12 =
      (Real.pi : ℂ) * Complex.I / 2 *
        (((∑ s, μ s : ℝ) : ℂ) ^ 3 +
          3 * ((∑ s, μ s : ℝ) : ℂ) * ((∑ s, (μ s) ^ 2 : ℝ) : ℂ)) := by
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_sum]
    rw [phaseFrequency_cubic_sum H hH]
    push_cast
    linear_combination (Complex.I / 6 *
      ((∑ s, (μ s : ℂ)) ^ 3 + 3 * (∑ s, (μ s : ℂ)) * ∑ s, (μ s : ℂ) ^ 2)) * hscaleC
  rw [he] at hb
  have habs : |ε| ^ 4 = ε ^ 4 := by rw [show 4 = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  convert hb using 1
  simp only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, mul_pow, habs]
  ring

end PhaseLimit
end Konig
