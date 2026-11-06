module

public import Konig.HadamardCandidates
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Konig.Construction

def phaseScale : ℝ := (3 * Real.pi) ^ ((3 : ℝ)⁻¹)

theorem phaseScale_pos : 0 < phaseScale :=
  Real.rpow_pos_of_pos (by positivity) _

theorem phaseScale_cube : phaseScale ^ 3 = 3 * Real.pi :=
  Real.rpow_inv_natCast_pow (by positivity) (by decide : (3 : ℕ) ≠ 0)

def sineEnvelope {k : ℕ} (a s : Fin k → ℝ) (x : ℝ) : ℝ :=
  ∑ i, a i * Real.sin (s i * x)

theorem continuous_sineEnvelope {k : ℕ} (a s : Fin k → ℝ) :
    Continuous (sineEnvelope a s) := by
  unfold sineEnvelope
  fun_prop

def dimension (r : ℕ) : ℕ := 4 * 2 ^ (3 * r)

theorem dimension_pos (r : ℕ) : 0 < dimension r := by
  unfold dimension
  positivity

def candidateLeft {k : ℕ} (a s : Fin k → ℝ) (r : ℕ) :
    EuclideanSpace ℝ (Fin (dimension r)) → ℝ :=
  hadamardInputFin (sylvester (3*r)) (phaseScale / (2 : ℝ)^r) (sineEnvelope a s)

def candidateRight {k : ℕ} (a s : Fin k → ℝ) (r : ℕ) :
    EuclideanSpace ℝ (Fin (dimension r)) → ℝ :=
  hadamardInputFin (sylvester (3*r)) (-(phaseScale / (2 : ℝ)^r)) (sineEnvelope a s)

theorem candidateLeft_admissible {k : ℕ} (a s : Fin k → ℝ)
    (hb : ∀ x, |sineEnvelope a s x| ≤ 1) (r : ℕ) :
    AEMeasurable (candidateLeft a s r) volume ∧ ∀ x, |candidateLeft a s r x| ≤ 1 :=
  hadamardInputFin_admissible _ _ _ (continuous_sineEnvelope a s) hb

theorem candidateRight_admissible {k : ℕ} (a s : Fin k → ℝ)
    (hb : ∀ x, |sineEnvelope a s x| ≤ 1) (r : ℕ) :
    AEMeasurable (candidateRight a s r) volume ∧ ∀ x, |candidateRight a s r x| ≤ 1 :=
  hadamardInputFin_admissible _ _ _ (continuous_sineEnvelope a s) hb

end Konig.Construction
