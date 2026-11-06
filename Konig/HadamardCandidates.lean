module

public import Konig.CyclicConstruction
public import Konig.Halfspace
public import Konig.Coordinates

@[expose] public section

namespace Konig.Construction

noncomputable section

/-- The diagonal quadratic phases in the Hadamard construction. -/
def hadamardPhase {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (u : EuclideanSpace ℝ (Fin m ⊕ Fin m)) (s : Fin m) : ℝ :=
  ε / 2 * ((∑ j, ((u (.inl j))^2 + (u (.inr j))^2)) +
    (∑ j, H s j * ((u (.inl j))^2 - (u (.inr j))^2)) - m)

theorem continuous_hadamardPhase {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) :
    Continuous (fun u : EuclideanSpace ℝ (Fin m ⊕ Fin m) => hadamardPhase H ε u) := by
  apply continuous_pi
  intro s
  unfold hadamardPhase
  fun_prop

/-- A rotating input for any continuous real envelope bounded by one. -/
def hadamardInput {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (h : ℝ → ℝ)
    (z : EuclideanSpace ℝ (Fin m ⊕ Fin m) × EuclideanSpace ℝ (Fin m ⊕ Fin m)) : ℝ :=
  h (inner ℝ (phaseNormal (hadamardPhase H ε z.2)) z.1)

theorem continuous_hadamardInput {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (h : ℝ → ℝ) (hh : Continuous h) : Continuous (hadamardInput H ε h) := by
  unfold hadamardInput
  exact hh.comp ((continuous_phaseNormal.comp
    ((continuous_hadamardPhase H ε).comp continuous_snd)).inner continuous_fst)

theorem measurable_hadamardInput {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (h : ℝ → ℝ) (hh : Continuous h) : Measurable (hadamardInput H ε h) :=
  (continuous_hadamardInput H ε h hh).measurable

theorem aemeasurable_hadamardInput {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (h : ℝ → ℝ) (hh : Continuous h) :
    AEMeasurable (hadamardInput H ε h) MeasureTheory.volume :=
  (measurable_hadamardInput H ε h hh).aemeasurable

theorem hadamardInput_abs_le_one {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (h : ℝ → ℝ) (hh : ∀ t, |h t| ≤ 1) (z) :
    |hadamardInput H ε h z| ≤ 1 := hh _

/-- The same candidate on the challenge's canonical coordinate space. -/
def hadamardInputFin {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (h : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin (4*m))) : ℝ :=
  hadamardInput H ε h (WithLp.ofLp (blockCoordinates m x))

theorem continuous_hadamardInputFin {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (h : ℝ → ℝ) (hh : Continuous h) : Continuous (hadamardInputFin H ε h) :=
  (continuous_hadamardInput H ε h hh).comp (continuous_blockCoordinates m)

theorem hadamardInputFin_admissible {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (h : ℝ → ℝ) (hc : Continuous h) (hb : ∀ t, |h t| ≤ 1) :
    AEMeasurable (hadamardInputFin H ε h) MeasureTheory.volume ∧
      ∀ x, |hadamardInputFin H ε h x| ≤ 1 :=
  ⟨(continuous_hadamardInputFin H ε h hc).measurable.aemeasurable, fun _x => hb _⟩

/-- The opposite phase gives the second input; no separate construction is needed. -/
theorem hadamardPhase_neg {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) (u) :
    hadamardPhase H (-ε) u = fun s => -hadamardPhase H ε u s := by
  funext s
  simp only [hadamardPhase]
  ring

theorem hadamardPhase_even {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) (u) :
    hadamardPhase H ε (-u) = hadamardPhase H ε u := by
  funext s
  simp [hadamardPhase]

theorem hadamardInput_odd {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (h : ℝ → ℝ) (hh : ∀ t, h (-t) = -h t) (z) :
    hadamardInput H ε h (-z) = -hadamardInput H ε h z := by
  simp [hadamardInput, hadamardPhase_even, hh]

end
end Konig.Construction
