module

public import Konig.HadamardFactorization

@[expose] public section

open scoped BigOperators
open MeasureTheory
noncomputable section
namespace Konig.Construction

def boolSign (b : Bool) : ℝ := realSign b

def signedFrequency {m k : ℕ} (τ : Fin k → Fin m) (σ : Fin k → Bool) : Fin m → ℝ :=
  frequency τ (fun a => boolSign (σ a))

/-- The exact Gaussian multiplier for a prescribed real channel-frequency vector. -/
def phaseMultiplier {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (μ : Fin m → ℝ) : ℂ :=
  ∏ i, scalarPhase (phaseFrequency H ε μ i)

/-- Uniform average over independent channel assignments and independent signs. -/
def phaseCoefficient {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) (k : ℕ) : ℂ :=
  (((m : ℂ)^k * (2 : ℂ)^k))⁻¹ *
    ∑ τ : Fin k → Fin m, ∑ σ : Fin k → Bool,
      phaseMultiplier H ε (signedFrequency τ σ)

/-- Cubically growing dimensions and inversely shrinking phases; take `c^3 = 3*pi`. -/
def coefficientSequence (c : ℝ) (r n : ℕ) : ℂ :=
  phaseCoefficient (sylvester (3*r)) (c / (2 : ℝ)^r) (2*n+1)

@[simp] theorem boolSign_abs (b : Bool) : |boolSign b| = 1 := by simp [boolSign]
@[simp] theorem boolSign_sq (b : Bool) : boolSign b ^ 2 = 1 := by simp [boolSign]

theorem phaseMultiplier_norm_le_one {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (ε : ℝ) (μ : Fin m → ℝ) : ‖phaseMultiplier H ε μ‖ ≤ 1 := by
  rw [phaseMultiplier, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => scalarPhase_norm_le_one _)

/-- Exact Hadamard phase integral factorization; no orthogonality is required here. -/
theorem phaseMultiplier_eq_integral {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (ε : ℝ) (μ : Fin m → ℝ) :
    phaseMultiplier H ε μ =
      (((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ (2*m))⁻¹ *
        (∫ x : EuclideanSpace ℝ (Fin m ⊕ Fin m),
         ∫ y : EuclideanSpace ℝ (Fin m ⊕ Fin m),
          Complex.exp (-(((‖x‖ : ℝ) : ℂ)^2 + ((‖y‖ : ℝ) : ℂ)^2) / 2 +
            Complex.I * (inner ℝ x y : ℝ) +
            Complex.I * ((∑ s, μ s * (hadamardPhase H ε x s + hadamardPhase H ε y s) : ℝ) : ℂ))) := by
  unfold phaseMultiplier
  rw [← scalarPhase_prod_invariant]
  congr 1
  · simp [Fintype.card_sum, Fintype.card_fin, two_mul]
  · apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with y
    congr 1
    rw [weighted_hadamardPhase_pair]
    push_cast
    ring

theorem phaseCoefficient_norm_le_one {m : ℕ} (hm : 0 < m)
    (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) (k : ℕ) :
    ‖phaseCoefficient H ε k‖ ≤ 1 := by
  have hs : ‖∑ τ : Fin k → Fin m, ∑ σ : Fin k → Bool,
      phaseMultiplier H ε (signedFrequency τ σ)‖ ≤ (m : ℝ)^k * 2^k := by
    calc
      _ ≤ ∑ τ : Fin k → Fin m, ‖∑ σ : Fin k → Bool,
          phaseMultiplier H ε (signedFrequency τ σ)‖ := norm_sum_le _ _
      _ ≤ ∑ τ : Fin k → Fin m, ∑ σ : Fin k → Bool,
          ‖phaseMultiplier H ε (signedFrequency τ σ)‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
      _ ≤ ∑ _τ : Fin k → Fin m, ∑ _σ : Fin k → Bool, (1 : ℝ) :=
        Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ => phaseMultiplier_norm_le_one _ _ _))
      _ = _ := by simp [Fintype.card_fun]
  have hp : 0 < (m : ℝ)^k * (2 : ℝ)^k := by positivity
  unfold phaseCoefficient
  rw [norm_mul, norm_inv, norm_mul, norm_pow, norm_pow]
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  simp only [Complex.norm_natCast]
  calc
    _ ≤ ((m : ℝ)^k * (2 : ℝ)^k)⁻¹ * ((m : ℝ)^k * (2 : ℝ)^k) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hp.le)
    _ = 1 := inv_mul_cancel₀ hp.ne'

end Konig.Construction
