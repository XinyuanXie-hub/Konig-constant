module

public import Konig.PhaseCoefficient
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Konig.Construction

theorem sum_frequency_mul {m k : ℕ} (τ : Fin k → Fin m) (σ : Fin k → ℝ)
    (η : Fin m → ℝ) :
    ∑ j, frequency τ σ j * η j = ∑ a, σ a * η (τ a) := by
  simp only [frequency, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

theorem cos_eq_bool_exp (x : ℝ) :
    (Real.cos x : ℂ) = (2 : ℂ)⁻¹ *
      ∑ b : Bool, Complex.exp (Complex.I * (boolSign b : ℂ) * (x : ℂ)) := by
  rw [Complex.ofReal_cos]
  simp [boolSign, realSign, intSign, Complex.cos,
    div_eq_mul_inv, mul_comm, mul_left_comm]

theorem prod_cos_eq_sign_exp {m k : ℕ} (τ : Fin k → Fin m) (η : Fin m → ℝ) :
    (∏ a, (Real.cos (η (τ a)) : ℂ)) = ((2 : ℂ) ^ k)⁻¹ *
      ∑ σ : Fin k → Bool,
        Complex.exp (Complex.I * (∑ a, (boolSign (σ a) : ℂ) * (η (τ a) : ℂ))) := by
  simp_rw [cos_eq_bool_exp]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [← Complex.exp_sum]
  congr 1
  simp only [Finset.mul_sum, mul_assoc]

/-- Exact finite cosine-power expansion, indexed by independent channel
assignments and signs. No positivity or nonzero-dimension hypothesis is needed. -/
theorem cosine_average_pow {m k : ℕ} (η : Fin m → ℝ) :
    ((m : ℂ)⁻¹ * ∑ j, (Real.cos (η j) : ℂ)) ^ k =
      ((m : ℂ) ^ k * (2 : ℂ) ^ k)⁻¹ *
        ∑ τ : Fin k → Fin m, ∑ σ : Fin k → Bool,
          Complex.exp (Complex.I *
            (∑ j, (signedFrequency τ σ j : ℂ) * (η j : ℂ))) := by
  rw [mul_pow, inv_pow, Fintype.sum_pow]
  simp_rw [prod_cos_eq_sign_exp]
  rw [← Finset.mul_sum]
  simp only [mul_inv_rev]
  rw [← mul_assoc]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro τ hτ
    apply Finset.sum_congr rfl
    intro σ hσ
    congr 2
    exact_mod_cast (sum_frequency_mul τ (fun a => boolSign (σ a)) η).symm

end Konig.Construction
