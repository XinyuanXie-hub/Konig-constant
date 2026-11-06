module

public import Konig.Definitions
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Konig

theorem gaussian_normalization (n : ℕ) :
    ((Real.sqrt 2 * Real.pi) ^ n)⁻¹ *
      (Real.sqrt ((2 * Real.pi)^n * Real.pi^((n : ℝ)/2)) *
        Real.sqrt (Real.pi^((n : ℝ)/2))) = 1 := by
  have hp := Real.pi_pos
  have hpow : Real.pi ^ ((n : ℝ) / 2) * Real.pi ^ ((n : ℝ) / 2) = Real.pi ^ n := by
    rw [← Real.rpow_add hp]
    simp
  have hprod : ((2 * Real.pi) ^ n * Real.pi ^ ((n : ℝ) / 2)) *
      Real.pi ^ ((n : ℝ) / 2) = ((Real.sqrt 2 * Real.pi) ^ n) ^ 2 := by
    rw [mul_assoc, hpow, ← mul_pow]
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    congr 1
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [← Real.sqrt_mul (by positivity), hprod, Real.sqrt_sq (by positivity)]
  exact inv_mul_cancel₀ (by positivity)

end Konig
