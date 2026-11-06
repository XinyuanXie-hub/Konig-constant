module

public import Konig.Supremum
public import Konig.UpperBound
public import Konig.SineApproximation

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace Konig

theorem constant_le_one : constant ≤ 1 := by
  unfold constant
  apply csSup_le
  · exact ⟨0, 1, by decide, (fun _ => 0), (fun _ => 0),
      aemeasurable_const, aemeasurable_const, by simp, by simp,
      (bilinear_zero_left _).symm⟩
  · rintro b ⟨n, hn, f, g, hf, hg, hfb, hgb, rfl⟩
    exact (le_abs_self _).trans (abs_bilinear_le_one f g hf hg hfb hgb)

/-- Assembly from bounded sine-envelope constructions. The hypothesis is the
remaining analytic construction limit, not an additional assumption on the target. -/
theorem constant_eq_one_of_envelope_limits (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hconstruction : ∀ (k : ℕ) (a s : Fin k → ℝ),
      (∀ x : ℝ, |∑ i, a i * Real.sin (s i * x)| ≤ 1) →
      ∃ (N : ℕ → ℕ)
        (f g : (r : ℕ) → EuclideanSpace ℝ (Fin (N r)) → ℝ),
        (∀ r, 0 < N r ∧ AEMeasurable (f r) volume ∧ AEMeasurable (g r) volume ∧
          (∀ x, |f r x| ≤ 1) ∧ (∀ x, |g r x| ≤ 1)) ∧
        Tendsto (fun r => bilinear (f r) (g r)) atTop
          (𝓝 (∫ x, (∑ i, a i * Real.sin (s i * x)) ^ 2 ∂μ))) :
    constant = 1 := by
  apply constant_eq_one_of_bounds
  · intro n hn f g hf hg hfb hgb
    exact (le_abs_self _).trans (abs_bilinear_le_one f g hf hg hfb hgb)
  · intro b hb
    obtain ⟨k, a, s, hp, hgram⟩ :=
      SineApproximation.exists_bounded_sine_polynomial μ (sub_pos.mpr hb)
    have hbgram : b < ∫ x, (∑ i, a i * Real.sin (s i * x)) ^ 2 ∂μ := by
      linarith
    obtain ⟨N, f, g, hadm, hlim⟩ := hconstruction k a s hp
    obtain ⟨r, hr⟩ := (hlim.eventually (lt_mem_nhds hbgram)).exists
    obtain ⟨hN, hf, hg, hfb, hgb⟩ := hadm r
    exact ⟨N r, hN, f r, g r, hf, hg, hfb, hgb, hr⟩

end Konig
