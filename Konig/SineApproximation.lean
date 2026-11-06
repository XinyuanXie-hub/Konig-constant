module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp

@[expose] public section

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Konig.SineApproximation

/-- An odd cubic that amplifies nonzero values in the unit interval. -/
def step (x : ℝ) : ℝ := (3 * x - x ^ 3) / 2

def amplify : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => step (amplify n x)

theorem step_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    step x ∈ Set.Icc (-1 : ℝ) 1 := by
  have h₁ := mul_nonneg (sq_nonneg (1 - x)) (show 0 ≤ x + 2 by linarith [hx.1])
  have h₂ := mul_nonneg (sq_nonneg (1 + x)) (show 0 ≤ 2 - x by linarith [hx.2])
  constructor <;> dsimp [step] <;> nlinarith

theorem le_step {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : x ≤ step x := by
  have h := mul_nonneg hx.1 (show 0 ≤ 1 - x ^ 2 by nlinarith [hx.1, hx.2])
  dsimp [step]
  nlinarith

theorem amplify_mem_Icc (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    amplify n x ∈ Set.Icc (-1 : ℝ) 1 := by
  induction n with
  | zero => exact hx
  | succ n ih => exact step_mem_Icc ih

theorem amplify_mem_Icc_pos (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    amplify n x ∈ Set.Icc (0 : ℝ) 1 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    exact ⟨ih.1.trans (le_step ih),
      (step_mem_Icc ⟨by linarith [ih.1], ih.2⟩).2⟩

theorem amplify_monotone {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Monotone (fun n => amplify n x) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_step (amplify_mem_Icc_pos n hx)

theorem amplify_neg (n : ℕ) (x : ℝ) : amplify n (-x) = -amplify n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [amplify, step, ih]; ring

theorem tendsto_amplify_one {x : ℝ} (hx : 0 < x) (hx₁ : x ≤ 1) :
    Tendsto (fun n => amplify n x) atTop (𝓝 1) := by
  have hmon := amplify_monotone ⟨hx.le, hx₁⟩
  have hb : BddAbove (Set.range (fun n => amplify n x)) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (amplify_mem_Icc_pos n ⟨hx.le, hx₁⟩).2⟩
  let l := ⨆ n, amplify n x
  have ht : Tendsto (fun n => amplify n x) atTop (𝓝 l) :=
    tendsto_atTop_ciSup hmon hb
  have hxl : x ≤ l := le_ciSup hb 0
  have hl₁ : l ≤ 1 := ciSup_le fun n => (amplify_mem_Icc_pos n ⟨hx.le, hx₁⟩).2
  have hs : Tendsto (fun n => amplify (n + 1) x) atTop (𝓝 l) :=
    (tendsto_add_atTop_iff_nat 1).2 ht
  have hs' : Tendsto (fun n => amplify (n + 1) x) atTop (𝓝 (step l)) := by
    exact ((tendsto_const_nhds.mul ht).sub (ht.pow 3)).div_const 2
  have he : l = step l := tendsto_nhds_unique hs hs'
  have he' : l = 1 := by
    have : 0 < l := hx.trans_le hxl
    dsimp [step] at he
    nlinarith [mul_pos this (show 0 < l + 1 by linarith)]
  simpa [he'] using ht

theorem tendsto_amplify_sq_one {x : ℝ} (hx : |x| ≤ 1) (hx₀ : x ≠ 0) :
    Tendsto (fun n => (amplify n x) ^ 2) atTop (𝓝 1) := by
  rcases lt_or_gt_of_ne hx₀ with hneg | hpos
  · have h := (tendsto_amplify_one (neg_pos.mpr hneg)
      (show -x ≤ 1 by linarith [(abs_le.mp hx).1])).pow 2
    simpa only [amplify_neg, neg_sq, one_pow] using h
  · simpa only [one_pow] using
      (tendsto_amplify_one hpos (abs_le.mp hx).2).pow 2

def sineApprox (n : ℕ) (x : ℝ) : ℝ := amplify n (Real.sin x)

theorem sineApprox_abs_le_one (n : ℕ) (x : ℝ) : |sineApprox n x| ≤ 1 := by
  exact abs_le.mpr (amplify_mem_Icc n (abs_le.mp (Real.abs_sin_le_one x)))

theorem continuous_amplify (n : ℕ) : Continuous (amplify n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih =>
    exact ((continuous_const.mul ih).sub (ih.pow 3)).div_const 2

theorem continuous_sineApprox (n : ℕ) : Continuous (sineApprox n) :=
  (continuous_amplify n).comp Real.continuous_sin

theorem sineApprox_neg (n : ℕ) (x : ℝ) : sineApprox n (-x) = -sineApprox n x := by
  simp only [sineApprox, Real.sin_neg, amplify_neg]

theorem ae_sin_ne_zero (μ : Measure ℝ) [NullSingletonClass μ] :
    ∀ᵐ x ∂μ, Real.sin x ≠ 0 := by
  have hc : Set.Countable {x : ℝ | Real.sin x = 0} := by
    apply (Set.countable_range (fun n : ℤ => (n : ℝ) * Real.pi)).mono
    intro x hx
    exact Real.sin_eq_zero_iff.mp hx
  apply ae_iff.mpr
  simpa using hc.measure_zero μ

/-- Bounded odd trigonometric polynomials whose squared norm tends to one
under every atomless probability measure, in particular a nondegenerate Gaussian. -/
theorem tendsto_integral_sineApprox_sq (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    Tendsto (fun n => ∫ x, (sineApprox n x) ^ 2 ∂μ) atTop (𝓝 1) := by
  have ht := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x => (sineApprox n x) ^ 2) (f := fun _ => (1 : ℝ))
    (fun _ => (1 : ℝ))
    (fun n => ((continuous_sineApprox n).pow 2).aestronglyMeasurable)
    (integrable_const 1) ?_ ?_
  · simpa using ht
  · intro n
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_one_iff_abs_le_one _).mpr (sineApprox_abs_le_one n x)
  · filter_upwards [ae_sin_ne_zero μ] with x hx
    exact tendsto_amplify_sq_one (Real.abs_sin_le_one x) hx

/-- A finite real linear combination of sine waves. -/
def HasSineExpansion (f : ℝ → ℝ) : Prop :=
  ∃ (n : ℕ) (a s : Fin n → ℝ), ∀ x, f x = ∑ i, a i * Real.sin (s i * x)

theorem hasSineExpansion_sin (s : ℝ) : HasSineExpansion (fun x => Real.sin (s * x)) := by
  refine ⟨1, fun _ => 1, fun _ => s, ?_⟩
  intro x
  simp

theorem HasSineExpansion.add {f g : ℝ → ℝ} (hf : HasSineExpansion f)
    (hg : HasSineExpansion g) : HasSineExpansion (fun x => f x + g x) := by
  obtain ⟨n, a, s, ha⟩ := hf
  obtain ⟨m, b, t, hb⟩ := hg
  refine ⟨n + m, Fin.addCases a b, Fin.addCases s t, ?_⟩
  intro x
  simp [Fin.sum_univ_add, ha, hb]

theorem HasSineExpansion.smul {f : ℝ → ℝ} (hf : HasSineExpansion f) (c : ℝ) :
    HasSineExpansion (fun x => c * f x) := by
  obtain ⟨n, a, s, ha⟩ := hf
  refine ⟨n, fun i => c * a i, s, ?_⟩
  intro x
  simp [ha, Finset.mul_sum, mul_assoc]

theorem hasSineExpansion_of_fintype {ι : Type} [Fintype ι] (a s : ι → ℝ) :
    HasSineExpansion (fun x => ∑ i, a i * Real.sin (s i * x)) := by
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, a ∘ e.symm, s ∘ e.symm, ?_⟩
  intro x
  exact (e.symm.sum_comp (fun i => a i * Real.sin (s i * x))).symm

theorem sin_mul_sin_mul_sin (a b c : ℝ) :
    Real.sin a * Real.sin b * Real.sin c =
      (Real.sin (a + b - c) + Real.sin (a - b + c) +
        Real.sin (-a + b + c) - Real.sin (a + b + c)) / 4 := by
  simp only [Real.sin_add, Real.sin_sub, Real.sin_neg, Real.cos_add,
    Real.cos_sub, Real.cos_neg]
  ring

theorem HasSineExpansion.triple {f g h : ℝ → ℝ}
    (hf : HasSineExpansion f) (hg : HasSineExpansion g) (hh : HasSineExpansion h) :
    HasSineExpansion (fun x => f x * g x * h x) := by
  obtain ⟨n, a, s, ha⟩ := hf
  obtain ⟨m, b, t, hb⟩ := hg
  obtain ⟨l, c, u, hc⟩ := hh
  let A : Fin n × Fin m × Fin l → ℝ := fun i => a i.1 * b i.2.1 * c i.2.2 / 4
  let r₁ : Fin n × Fin m × Fin l → ℝ := fun i => s i.1 + t i.2.1 - u i.2.2
  let r₂ : Fin n × Fin m × Fin l → ℝ := fun i => s i.1 - t i.2.1 + u i.2.2
  let r₃ : Fin n × Fin m × Fin l → ℝ := fun i => -s i.1 + t i.2.1 + u i.2.2
  let r₄ : Fin n × Fin m × Fin l → ℝ := fun i => s i.1 + t i.2.1 + u i.2.2
  have hp := (((hasSineExpansion_of_fintype A r₁).add
    (hasSineExpansion_of_fintype A r₂)).add
    (hasSineExpansion_of_fintype A r₃)).add
    ((hasSineExpansion_of_fintype A r₄).smul (-1))
  convert hp using 1
  funext x
  rw [mul_assoc, ha, hb, hc]
  simp only [Fintype.sum_mul_sum]
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  dsimp [A, r₁, r₂, r₃, r₄]
  have ht := sin_mul_sin_mul_sin (s i * x) (t j * x) (u k * x)
  simp only [add_mul, sub_mul, neg_mul] at *
  calc
    _ = (a i * b j * c k) *
        (Real.sin (s i * x) * Real.sin (t j * x) * Real.sin (u k * x)) := by ring
    _ = _ := by rw [ht]; ring

theorem hasSineExpansion_sineApprox (n : ℕ) : HasSineExpansion (sineApprox n) := by
  induction n with
  | zero =>
    change HasSineExpansion (fun x => Real.sin x)
    simpa using hasSineExpansion_sin 1
  | succ n ih =>
    have h := (ih.smul (3 / 2)).add ((ih.triple ih ih).smul (-1 / 2))
    convert h using 1
    funext x
    dsimp [sineApprox, amplify, step]
    ring

/-- The finite sine-polynomial envelope needed for the bounded-function
construction: uniformly bounded by one, with squared mass arbitrarily close to one. -/
theorem exists_bounded_sine_polynomial (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (a s : Fin n → ℝ),
      (∀ x : ℝ, |∑ i, a i * Real.sin (s i * x)| ≤ 1) ∧
      1 - ε < ∫ x, (∑ i, a i * Real.sin (s i * x)) ^ 2 ∂μ := by
  have he : ∀ᶠ n in atTop, 1 - ε < ∫ x, (sineApprox n x) ^ 2 ∂μ :=
    (tendsto_integral_sineApprox_sq μ).eventually
      (Ioi_mem_nhds (show 1 - ε < 1 by linarith))
  obtain ⟨k, hk⟩ := he.exists
  obtain ⟨n, a, s, hp⟩ := hasSineExpansion_sineApprox k
  refine ⟨n, a, s, ?_, ?_⟩
  · intro x
    rw [← hp]
    exact sineApprox_abs_le_one k x
  · simpa only [← hp] using hk

end Konig.SineApproximation
