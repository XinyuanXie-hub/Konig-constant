module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open MeasureTheory

noncomputable section

namespace Konig

/-- The normalized König bilinear form, integrated against Lebesgue volume. -/
def bilinear {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ((Real.sqrt 2 * Real.pi) ^ n)⁻¹ *
    ∫ x, ∫ y, f x * g y *
      Real.exp (-((‖x‖ ^ 2 + ‖y‖ ^ 2) / 2)) * Real.sin (inner ℝ x y)

/-- Supremum over positive dimensions and real Lebesgue-measurable functions
bounded in absolute value by one. -/
def constant : ℝ :=
  sSup {b : ℝ | ∃ (n : ℕ), 0 < n ∧
    ∃ (f g : EuclideanSpace ℝ (Fin n) → ℝ),
      AEMeasurable f volume ∧ AEMeasurable g volume ∧
      (∀ x, |f x| ≤ 1) ∧ (∀ x, |g x| ≤ 1) ∧ b = bilinear f g}

end Konig
