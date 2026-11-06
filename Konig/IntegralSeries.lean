module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

open MeasureTheory

namespace Konig

/-- Integrate the sine expansion against an integrable complex kernel.
The real amplitude is only required to be measurable and bounded by one. -/
theorem integral_mul_sin_series {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (K : α → ℂ) (hK : Integrable K μ) (Z : α → ℝ)
    (hZ : AEMeasurable Z μ) (hZb : ∀ x, |Z x| ≤ 1) (q : ℝ) :
    (∫ x, K x * Complex.sin ((q : ℂ) * (Z x : ℂ)) ∂μ) =
      ∑' n : ℕ, ((-1 : ℂ) ^ n * (q : ℂ) ^ (2*n+1) /
        (Nat.factorial (2*n+1) : ℂ)) * (∫ x, K x * (Z x : ℂ) ^ (2*n+1) ∂μ) := by
  let c : ℕ → ℂ := fun n => (-1 : ℂ) ^ n * (q : ℂ) ^ (2*n+1) /
    (Nat.factorial (2*n+1) : ℂ)
  let b : ℕ → ℝ := fun n => |q| ^ (2*n+1) / (Nat.factorial (2*n+1) : ℝ)
  have hc (n : ℕ) : ‖c n‖ = b n := by
    simp [c, b, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hb (n : ℕ) : 0 ≤ b n := by dsimp [b]; positivity
  have hZC : AEMeasurable (fun x => (Z x : ℂ)) μ :=
    Complex.continuous_ofReal.measurable.comp_aemeasurable hZ
  have hs : HasSum (fun n : ℕ => ∫ x, c n * (K x * (Z x : ℂ) ^ (2*n+1)) ∂μ)
      (∫ x, K x * Complex.sin ((q : ℂ) * (Z x : ℂ)) ∂μ) := by
    apply hasSum_integral_of_dominated_convergence
      (bound := fun n x => b n * ‖K x‖)
    · intro n
      exact (hK.aestronglyMeasurable.mul
        ((hZC.pow_const (2*n+1)).aestronglyMeasurable)).const_mul (c n)
    · intro n
      filter_upwards [] with x
      simp only [norm_mul, norm_pow, hc, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ b n * (‖K x‖ * 1) := by
          gcongr
          exact pow_le_one₀ (abs_nonneg _) (hZb x)
        _ = _ := by ring
    · filter_upwards [] with x
      exact (Real.hasSum_sinh |q|).summable.mul_right ‖K x‖
    · have he : (fun x => ∑' n : ℕ, b n * ‖K x‖) =
          fun x => Real.sinh |q| * ‖K x‖ := by
        funext x
        rw [tsum_mul_right, (Real.hasSum_sinh |q|).tsum_eq]
      rw [he]
      exact hK.norm.const_mul _
    · filter_upwards [] with x
      convert (Complex.hasSum_sin ((q : ℂ) * (Z x : ℂ))).mul_left (K x) using 1
      funext n
      dsimp [c]
      rw [mul_pow]
      ring
  rw [← hs.tsum_eq]
  apply tsum_congr
  intro n
  exact integral_const_mul _ _

theorem integral_mul_real_sin_series {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (K : α → ℂ) (hK : Integrable K μ) (Z : α → ℝ)
    (hZ : AEMeasurable Z μ) (hZb : ∀ x, |Z x| ≤ 1) (q : ℝ) :
    (∫ x, K x * (Real.sin (q * Z x) : ℂ) ∂μ) =
      ∑' n : ℕ, ((-1 : ℂ) ^ n * (q : ℂ) ^ (2*n+1) /
        (Nat.factorial (2*n+1) : ℂ)) * (∫ x, K x * (Z x : ℂ) ^ (2*n+1) ∂μ) := by
  simpa only [← Complex.ofReal_mul, Complex.ofReal_sin] using
    integral_mul_sin_series K hK Z hZ hZb q

end Konig
