module

public import Konig.Definitions

@[expose] public section

open MeasureTheory

namespace Konig

theorem bilinear_zero_left {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    bilinear (fun _ => 0) g = 0 := by
  simp [bilinear]

theorem bilinear_zero_right {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    bilinear f (fun _ => 0) = 0 := by
  simp [bilinear]

/-- An order-theoretic assembly lemma; the two analytic hypotheses still need proofs. -/
theorem constant_eq_one_of_bounds
    (upper : ∀ (n : ℕ), 0 < n →
      ∀ (f g : EuclideanSpace ℝ (Fin n) → ℝ),
        AEMeasurable f volume → AEMeasurable g volume →
        (∀ x, |f x| ≤ 1) → (∀ x, |g x| ≤ 1) → bilinear f g ≤ 1)
    (lower : ∀ b : ℝ, b < 1 → ∃ (n : ℕ), 0 < n ∧
      ∃ (f g : EuclideanSpace ℝ (Fin n) → ℝ),
        AEMeasurable f volume ∧ AEMeasurable g volume ∧
        (∀ x, |f x| ≤ 1) ∧ (∀ x, |g x| ≤ 1) ∧ b < bilinear f g) :
    constant = 1 := by
  unfold constant
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨0, 1, by decide, (fun _ => 0), (fun _ => 0),
      aemeasurable_const, aemeasurable_const, by simp, by simp,
      (bilinear_zero_left _).symm⟩
  · rintro b ⟨n, hn, f, g, hf, hg, hfb, hgb, rfl⟩
    exact upper n hn f g hf hg hfb hgb
  · intro b hb
    obtain ⟨n, hn, f, g, hf, hg, hfb, hgb, hlt⟩ := lower b hb
    exact ⟨bilinear f g, ⟨n, hn, f, g, hf, hg, hfb, hgb, rfl⟩, hlt⟩

end Konig
