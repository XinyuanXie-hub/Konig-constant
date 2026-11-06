module

public import Konig.PhaseLimit
public import Konig.PhaseCoefficient
public import Konig.CollisionEstimate

@[expose] public section

noncomputable section
namespace Konig.Construction

theorem norm_average_sub_le_all {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℂ) (c : ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ i, ‖f i - c‖ ≤ δ) :
    ‖(∑ i, f i) / (Fintype.card ι : ℂ) - c‖ ≤ δ := by
  simpa using norm_average_sub_le (fun _ : ι => True) f c δ δ hδ (fun i _ => h i) h

theorem phaseCoefficient_eq_average {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (ε : ℝ) (k : ℕ) :
    phaseCoefficient H ε k =
      (∑ τ : Fin k → Fin m,
        (∑ σ : Fin k → Bool, phaseMultiplier H ε (signedFrequency τ σ)) /
          (Fintype.card (Fin k → Bool) : ℂ)) /
            (Fintype.card (Fin k → Fin m) : ℂ) := by
  simp only [phaseCoefficient, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, ← Finset.sum_mul, mul_inv_rev]
  ring

/-- Averaging the uniform phase error adds only the vanishing collision proportion. -/
theorem phaseCoefficient_error_uniform :
    ∃ C > 0, ∃ δ > 0, ∀ (m : ℕ), 0 < m →
      ∀ (H : Matrix (Fin m) (Fin m) ℝ), H.IsHadamard → ∀ (ε : ℝ) (n : ℕ),
      |ε| * (2 * ((2*n+1 : ℕ) : ℝ)) < δ →
      (m : ℝ) * ε^3 = 3 * Real.pi →
      ‖phaseCoefficient H ε (2*n+1) - (-1 : ℂ)^n‖ ≤
        C * (m : ℝ) * ε^4 * (2 * ((2*n+1 : ℕ) : ℝ))^4 +
          2 * ((Fintype.card {τ : Fin (2*n+1) → Fin m // ¬ Function.Injective τ} : ℝ) /
            (m : ℝ)^(2*n+1)) := by
  obtain ⟨C, hC, δ, hδ, herr⟩ := PhaseLimit.hadamard_phase_product_error_uniform
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro m hm H hH ε n hsmall hscale
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let k := 2*n+1
  let D := C * (m : ℝ) * ε^4 * (2 * (k : ℝ))^4
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let f := fun τ : Fin k → Fin m =>
    (∑ σ : Fin k → Bool, phaseMultiplier H ε (signedFrequency τ σ)) /
      (Fintype.card (Fin k → Bool) : ℂ)
  have hb (τ : Fin k → Fin m) (σ : Fin k → Bool) :
      ‖phaseMultiplier H ε (signedFrequency τ σ) - (-1 : ℂ)^n‖ ≤ 2 := by
    calc
      _ ≤ ‖phaseMultiplier H ε (signedFrequency τ σ)‖ + ‖(-1 : ℂ)^n‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (phaseMultiplier_norm_le_one H ε _) (by simp)
      _ = _ := by norm_num
  have hgood (τ : Fin k → Fin m) (hτ : Function.Injective τ) :
      ‖f τ - (-1 : ℂ)^n‖ ≤ D := by
    apply norm_average_sub_le_all _ _ D hD
    intro σ
    have h := herr m H hH ε (signedFrequency τ σ) k
      (sign_frequency_l1_le τ σ) hsmall hscale
    change ‖phaseMultiplier H ε (signedFrequency τ σ) - _‖ ≤ D at h
    rw [show Complex.exp ((Real.pi : ℂ) * Complex.I / 2 *
        (((∑ s, signedFrequency τ σ s : ℝ) : ℂ)^3 +
          3*((∑ s, signedFrequency τ σ s : ℝ) : ℂ)*
            ((∑ s, (signedFrequency τ σ s)^2 : ℝ) : ℂ))) = (-1 : ℂ)^n from
      collision_free_multiplier τ hτ σ] at h
    exact h
  have hbound (τ : Fin k → Fin m) : ‖f τ - (-1 : ℂ)^n‖ ≤ 2 :=
    norm_average_sub_le_all _ _ 2 (by norm_num) (hb τ)
  have h := norm_average_sub_le Function.Injective f ((-1 : ℂ)^n) D 2 hD hgood hbound
  rw [phaseCoefficient_eq_average]
  simpa only [f, D, k, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using h

end Konig.Construction
