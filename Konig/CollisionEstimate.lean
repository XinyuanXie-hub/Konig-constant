module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

open Filter
open scoped Topology

namespace Konig.Construction

/-- Exact number of collision-free channel assignments. -/
theorem card_injective_assignments (k m : ℕ) :
    Fintype.card {τ : Fin k → Fin m // Function.Injective τ} = m.descFactorial k := by
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq]
  simp

theorem tendsto_nat_sub_div (k : ℕ) :
    Tendsto (fun m : ℕ => ((m-k : ℕ) : ℝ) / (m : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))
  have heq : (fun m : ℕ => ((m-k : ℕ) : ℝ) / (m : ℝ)) =ᶠ[atTop]
      (fun m : ℕ => 1 - (k : ℝ) / (m : ℝ)) := by
    filter_upwards [eventually_ge_atTop k, eventually_ge_atTop 1] with m hmk hm
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    rw [Nat.cast_sub hmk, sub_div, div_self hm0]
  have h' : Tendsto (fun m : ℕ => 1 - (k : ℝ) / (m : ℝ)) atTop (𝓝 1) := by
    simpa using h
  exact h'.congr' heq.symm

/-- For each fixed word length, collisions have asymptotically zero proportion.
This qualitative statement avoids a birthday-bound rate. -/
theorem tendsto_descFactorial_div_pow (k : ℕ) :
    Tendsto (fun m : ℕ => (m.descFactorial k : ℝ) / (m : ℝ)^k)
      atTop (𝓝 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := (tendsto_nat_sub_div k).mul ih
    convert h using 1
    · ext m
      simp only [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · norm_num

theorem card_noninjective_assignments (k m : ℕ) :
    Fintype.card {τ : Fin k → Fin m // ¬ Function.Injective τ} =
      m^k - m.descFactorial k := by
  rw [Fintype.card_subtype_compl, card_injective_assignments]
  simp

/-- The exact bad proportion tends to zero; no quantitative collision estimate is needed. -/
theorem tendsto_collision_fraction (k : ℕ) :
    Tendsto (fun m : ℕ =>
      (Fintype.card {τ : Fin k → Fin m // ¬ Function.Injective τ} : ℝ) / (m : ℝ)^k)
      atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_descFactorial_div_pow k)
  have heq : (fun m : ℕ =>
      (Fintype.card {τ : Fin k → Fin m // ¬ Function.Injective τ} : ℝ) / (m : ℝ)^k)
      =ᶠ[atTop] (fun m : ℕ => 1 - (m.descFactorial k : ℝ)/(m : ℝ)^k) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    have hcard : m.descFactorial k ≤ m^k := by
      rw [← card_injective_assignments]
      simpa using Fintype.card_subtype_le (fun τ : Fin k → Fin m => Function.Injective τ)
    rw [card_noninjective_assignments, Nat.cast_sub hcard, Nat.cast_pow,
      sub_div, div_self (pow_ne_zero _ hm0)]
  have h' : Tendsto (fun m : ℕ => 1 - (m.descFactorial k : ℝ)/(m : ℝ)^k)
      atTop (𝓝 0) := by simpa using h
  exact h'.congr' heq.symm

/-- Uniform finite averages are controlled by a good-event error and bad-event proportion. -/
theorem norm_average_sub_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Prop) [DecidablePred P] (f : ι → ℂ) (c : ℂ) (δ C : ℝ)
    (hδ : 0 ≤ δ) (hgood : ∀ i, P i → ‖f i - c‖ ≤ δ)
    (hbound : ∀ i, ‖f i - c‖ ≤ C) :
    ‖(∑ i, f i) / (Fintype.card ι : ℂ) - c‖ ≤
      δ + C * ((Fintype.card {i // ¬ P i} : ℝ) / (Fintype.card ι : ℝ)) := by
  have hcR : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hcC : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Fintype.card_pos : Fintype.card ι ≠ 0)
  have havg : (∑ i, f i) / (Fintype.card ι : ℂ) - c =
      (∑ i, (f i - c)) / (Fintype.card ι : ℂ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [havg, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hcR).2
  calc
    _ ≤ ∑ i, ‖f i - c‖ := norm_sum_le _ _
    _ ≤ ∑ i, (δ + if P i then 0 else C) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : P i
      · simpa [hi] using hgood i hi
      · simpa [hi] using (hbound i).trans (le_add_of_nonneg_left hδ)
    _ = (Fintype.card ι : ℝ)*δ + (Fintype.card {i // ¬ P i} : ℝ)*C := by
      simp [Finset.sum_add_distrib, Finset.sum_ite, Fintype.card_subtype]
    _ = _ := by field_simp

end Konig.Construction
