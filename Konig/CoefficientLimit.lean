module

public import Konig.PhaseLimit
public import Konig.PhaseCoefficient
public import Konig.CollisionEstimate
public import Konig.CoefficientEstimate

@[expose] public section

open Filter
open scoped Topology

namespace Konig.Construction

theorem sylvester_cubic_order (r : ℕ) : 2 ^ (3 * r) = 8 ^ r := by
  rw [pow_mul]
  norm_num

theorem sylvester_cubic_order_tendsto :
    Tendsto (fun r : ℕ => 2 ^ (3 * r)) atTop atTop := by
  simp_rw [sylvester_cubic_order]
  exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 8)

theorem coefficient_scale (c : ℝ) (hc : c ^ 3 = 3 * Real.pi) (r : ℕ) :
    ((2 ^ (3 * r) : ℕ) : ℝ) * (c / (2 : ℝ) ^ r) ^ 3 = 3 * Real.pi := by
  rw [sylvester_cubic_order, Nat.cast_pow, Nat.cast_ofNat,
    PhaseLimit.geometric_cubic_scale, hc]

theorem coefficient_argument_tendsto (c K : ℝ) :
    Tendsto (fun r : ℕ => |c / (2 : ℝ) ^ r| * K) atTop (𝓝 0) := by
  have he (r : ℕ) : |c / (2 : ℝ) ^ r| * K = (|c| * K) * (1 / 2 : ℝ) ^ r := by
    simp only [abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_pow, one_pow]
    ring
  simp_rw [he]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (|c| * K)

theorem coefficient_error_tendsto (c C K : ℝ) :
    Tendsto (fun r : ℕ => C * ((2 ^ (3 * r) : ℕ) : ℝ) *
      (c / (2 : ℝ) ^ r) ^ 4 * K ^ 4) atTop (𝓝 0) := by
  have he (r : ℕ) : C * ((2 ^ (3 * r) : ℕ) : ℝ) *
      (c / (2 : ℝ) ^ r) ^ 4 * K ^ 4 =
      (C * K ^ 4) * ((8 : ℝ) ^ r * (c / (2 : ℝ) ^ r) ^ 4) := by
    rw [sylvester_cubic_order, Nat.cast_pow, Nat.cast_ofNat]
    ring
  simp_rw [he]
  simpa using (PhaseLimit.geometric_quartic_tendsto_zero c).const_mul (C * K ^ 4)

theorem coefficient_collision_tendsto (k : ℕ) :
    Tendsto (fun r : ℕ =>
      (Fintype.card {τ : Fin k → Fin (2 ^ (3 * r)) // ¬ Function.Injective τ} : ℝ) /
        (((2 ^ (3 * r) : ℕ) : ℝ) ^ k)) atTop (𝓝 0) :=
  (tendsto_collision_fraction k).comp sylvester_cubic_order_tendsto

/-- Every fixed odd coefficient approaches its required alternating sign. -/
theorem coefficientSequence_tendsto (c : ℝ) (hc : c ^ 3 = 3 * Real.pi) (n : ℕ) :
    Tendsto (fun r : ℕ => coefficientSequence c r n) atTop (𝓝 ((-1 : ℂ) ^ n)) := by
  obtain ⟨C, hC, δ, hδ, herr⟩ := phaseCoefficient_error_uniform
  have hsmall : ∀ᶠ r in atTop,
      |c / (2 : ℝ) ^ r| * (2 * ((2*n+1 : ℕ) : ℝ)) < δ :=
    (coefficient_argument_tendsto c (2 * ((2*n+1 : ℕ) : ℝ))).eventually (gt_mem_nhds hδ)
  have he := (coefficient_error_tendsto c C (2 * ((2*n+1 : ℕ) : ℝ))).add
    ((coefficient_collision_tendsto (2*n+1)).const_mul 2)
  have hz : Tendsto (fun r : ℕ => coefficientSequence c r n - (-1 : ℂ)^n)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [hsmall] with r hr
      exact herr (2 ^ (3*r)) (pow_pos (by norm_num) _) (sylvester (3*r))
        (sylvester_isHadamard (3*r)) (c / (2 : ℝ)^r) n hr (coefficient_scale c hc r)
    · simpa using he
  exact (tendsto_sub_nhds_zero_iff).mp hz

end Konig.Construction
