module

public import Konig.HadamardCandidates
public import Konig.ScalarFactorization

@[expose] public section

open scoped BigOperators
open MeasureTheory
noncomputable section
namespace Konig.Construction

private theorem weighted_matrix_sum {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (μ B : Fin m → ℝ) :
    (∑ s, μ s * ∑ j, H s j * B j) = ∑ j, (∑ s, H s j * μ s) * B j := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The diagonal frequencies corresponding to a weighted sum of phase channels. -/
def phaseFrequency {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (μ : Fin m → ℝ) : Fin m ⊕ Fin m → ℝ :=
  Sum.elim (fun j => ε * ((∑ s, μ s) + ∑ s, H s j * μ s))
    (fun j => ε * ((∑ s, μ s) - ∑ s, H s j * μ s))

private theorem weighted_hadamardPhase {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (ε : ℝ) (μ : Fin m → ℝ) (u : EuclideanSpace ℝ (Fin m ⊕ Fin m)) :
    (∑ s, μ s * hadamardPhase H ε u s) =
      ε / 2 * ∑ j, (((∑ s, μ s) + ∑ s, H s j * μ s) * (u (.inl j))^2 +
        ((∑ s, μ s) - ∑ s, H s j * μ s) * (u (.inr j))^2 - ∑ s, μ s) := by
  let S := ∑ s, μ s
  let A := ∑ j, ((u (.inl j))^2 + (u (.inr j))^2)
  let B := fun j => (u (.inl j))^2 - (u (.inr j))^2
  calc
    _ = ε / 2 * (∑ s, μ s * ((A - m) + ∑ j, H s j * B j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      simp only [hadamardPhase, A, B]
      ring
    _ = ε / 2 * (S * (A - m) + ∑ j, (∑ s, H s j * μ s) * B j) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, weighted_matrix_sum]
      dsimp [S]
      ring
    _ = _ := by
      congr 1
      dsimp [S, A, B]
      simp only [mul_sub, mul_add, sub_mul, Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring_nf
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      ring

/-- The real exponent identity used to factor every weighted phase integral. -/
theorem weighted_hadamardPhase_pair {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (ε : ℝ) (μ : Fin m → ℝ) (x y : EuclideanSpace ℝ (Fin m ⊕ Fin m)) :
    (∑ s, μ s * (hadamardPhase H ε x s + hadamardPhase H ε y s)) =
      1 / 2 * ∑ i, phaseFrequency H ε μ i * ((x i)^2 + (y i)^2 - 1) := by
  simp only [mul_add, Finset.sum_add_distrib]
  rw [weighted_hadamardPhase, weighted_hadamardPhase]
  simp only [phaseFrequency, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  set S := ∑ s, μ s
  set b := fun j => ∑ s, H s j * μ s
  change ε / 2 * (∑ j, ((S + b j) * (x (.inl j))^2 + (S - b j) * (x (.inr j))^2 - S)) +
      ε / 2 * (∑ j, ((S + b j) * (y (.inl j))^2 + (S - b j) * (y (.inr j))^2 - S)) =
      1 / 2 * ((∑ j, ε * (S + b j) * ((x (.inl j))^2 + (y (.inl j))^2 - 1)) +
        ∑ j, ε * (S - b j) * ((x (.inr j))^2 + (y (.inr j))^2 - 1))
  simp only [Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Konig.Construction
