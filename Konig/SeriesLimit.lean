module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

open Filter
open scoped Topology

namespace Konig

/-- Cubic phase correction converts the sine series into the hyperbolic sine series. -/
theorem tendsto_corrected_sine_series (T : ℕ → ℕ → ℂ)
    (hbound : ∀ r n, ‖T r n‖ ≤ 1)
    (hlim : ∀ n, Tendsto (fun r => T r n) atTop (𝓝 ((-1 : ℂ)^n))) (q : ℝ) :
    Tendsto (fun r => ∑' n : ℕ,
      ((-1 : ℂ)^n * (q : ℂ)^(2*n+1) / (Nat.factorial (2*n+1) : ℂ)) * T r n)
      atTop (𝓝 (Complex.sinh (q : ℂ))) := by
  have hs := (Real.hasSum_sinh |q|).summable
  have ht : Tendsto (fun r => ∑' n : ℕ,
      ((-1 : ℂ)^n * (q : ℂ)^(2*n+1) / (Nat.factorial (2*n+1) : ℂ)) * T r n)
      atTop (𝓝 (∑' n : ℕ, (q : ℂ)^(2*n+1) / (Nat.factorial (2*n+1) : ℂ))) := by
    apply tendsto_tsum_of_dominated_convergence hs
    · intro n
      have h := (tendsto_const_nhds (x :=
        ((-1 : ℂ)^n * (q : ℂ)^(2*n+1) / (Nat.factorial (2*n+1) : ℂ)))).mul (hlim n)
      convert h using 1
      congr 1
      have hp : ((-1 : ℂ)^n)^2 = 1 := by
        rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
        norm_num
      have he : ((-1 : ℂ)^n * (q : ℂ)^(2*n+1) / (Nat.factorial (2*n+1) : ℂ)) *
          (-1 : ℂ)^n = ((-1 : ℂ)^n)^2 *
            ((q : ℂ)^(2*n+1) / (Nat.factorial (2*n+1) : ℂ)) := by ring
      rw [he, hp, one_mul]
    · filter_upwards [] with r n
      rw [norm_mul]
      calc
        _ ≤ ‖(-1 : ℂ)^n * (q : ℂ)^(2*n+1) /
          (Nat.factorial (2*n+1) : ℂ)‖ * 1 := mul_le_mul_of_nonneg_left (hbound r n) (norm_nonneg _)
        _ = _ := by simp [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  simpa only [← Complex.sinh_eq_tsum] using ht

end Konig
