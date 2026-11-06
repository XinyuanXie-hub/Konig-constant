module

public import Konig.Definitions
public import Mathlib.Tactic.Ring

@[expose] public section

open MeasureTheory

noncomputable section

namespace Konig

private theorem integral_integral_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {e : α → β}
    (he : MeasurePreserving e μ ν) (hemb : MeasurableEmbedding e)
    (F : β → β → ℝ) :
    (∫ x, ∫ y, F (e x) (e y) ∂μ ∂μ) = ∫ x, ∫ y, F x y ∂ν ∂ν := by
  simp_rw [he.integral_comp hemb]
  exact he.integral_comp hemb (fun x => ∫ y, F x y ∂ν)

/-- The integral formula is invariant under orthonormal changes of coordinates. -/
theorem integral_kernel_isometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ₗᵢ[ℝ] F) (f g : F → ℝ) :
    (∫ x : E, ∫ y : E, f (e x) * g (e y) *
      Real.exp (-((‖x‖ ^ 2 + ‖y‖ ^ 2) / 2)) * Real.sin (inner ℝ x y)) =
    ∫ x : F, ∫ y : F, f x * g y *
      Real.exp (-((‖x‖ ^ 2 + ‖y‖ ^ 2) / 2)) * Real.sin (inner ℝ x y) := by
  simpa only [e.norm_map, e.inner_map_map] using
    integral_integral_comp e.measurePreserving e.toHomeomorph.measurableEmbedding
      (fun x y => f x * g y * Real.exp (-((‖x‖ ^ 2 + ‖y‖ ^ 2) / 2)) *
        Real.sin (inner ℝ x y))

theorem bilinear_isometry {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) :
    bilinear (f ∘ e) (g ∘ e) = bilinear f g := by
  unfold bilinear
  congr 1
  exact integral_kernel_isometry e f g

/-- Canonical orthonormal coordinates for a pair of `2m`-dimensional blocks. -/
def blockCoordinates (m : ℕ) :
    EuclideanSpace ℝ (Fin (4 * m)) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin m ⊕ Fin m) ×
        EuclideanSpace ℝ (Fin m ⊕ Fin m)) := by
  let E := EuclideanSpace ℝ (Fin m ⊕ Fin m)
  let V := WithLp 2 (E × E)
  have hdim : Module.finrank ℝ V = 4 * m := by
    have h := (WithLp.linearEquiv 2 ℝ (E × E)).finrank_eq
    simpa [V, E, Module.finrank_prod, finrank_euclideanSpace, Nat.mul_add,
      show 4 * m = (m + m) + (m + m) by omega] using h
  exact ((stdOrthonormalBasis ℝ V).reindex (finCongr hdim)).repr.symm

/-- Removing the `WithLp` wrapper turns the norm and inner product into block sums. -/
theorem integral_kernel_blocks (m : ℕ)
    (f g : (EuclideanSpace ℝ (Fin m ⊕ Fin m) ×
      EuclideanSpace ℝ (Fin m ⊕ Fin m)) → ℝ) :
    (∫ x : WithLp 2 (EuclideanSpace ℝ (Fin m ⊕ Fin m) ×
        EuclideanSpace ℝ (Fin m ⊕ Fin m)), ∫ y,
      f (WithLp.ofLp x) * g (WithLp.ofLp y) *
        Real.exp (-((‖x‖ ^ 2 + ‖y‖ ^ 2) / 2)) * Real.sin (inner ℝ x y)) =
    ∫ x, ∫ y, f x * g y *
      Real.exp (-((‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 + (‖y.1‖ ^ 2 + ‖y.2‖ ^ 2)) / 2)) *
        Real.sin (inner ℝ x.1 y.1 + inner ℝ x.2 y.2) := by
  let E := EuclideanSpace ℝ (Fin m ⊕ Fin m)
  let e := (MeasurableEquiv.toLp 2 (E × E)).symm
  have he : MeasurePreserving e := WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E E
  simpa [e, E, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_inner_apply] using
    integral_integral_comp he e.measurableEmbedding
      (fun x y : E × E => f x * g y *
        Real.exp (-((‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 + (‖y.1‖ ^ 2 + ‖y.2‖ ^ 2)) / 2)) *
        Real.sin (inner ℝ x.1 y.1 + inner ℝ x.2 y.2))

theorem bilinear_blockCoordinates (m : ℕ)
    (f g : (EuclideanSpace ℝ (Fin m ⊕ Fin m) ×
      EuclideanSpace ℝ (Fin m ⊕ Fin m)) → ℝ) :
    bilinear (fun x => f (WithLp.ofLp (blockCoordinates m x)))
      (fun x => g (WithLp.ofLp (blockCoordinates m x))) =
    ((Real.sqrt 2 * Real.pi) ^ (4 * m))⁻¹ *
      ∫ x, ∫ y, f x * g y *
        Real.exp (-((‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 + (‖y.1‖ ^ 2 + ‖y.2‖ ^ 2)) / 2)) *
          Real.sin (inner ℝ x.1 y.1 + inner ℝ x.2 y.2) := by
  unfold bilinear
  congr 1
  exact (integral_kernel_isometry (blockCoordinates m)
    (fun z => f (WithLp.ofLp z)) (fun z => g (WithLp.ofLp z))).trans
      (integral_kernel_blocks m f g)

theorem continuous_blockCoordinates (m : ℕ) :
    Continuous (fun x => WithLp.ofLp (blockCoordinates m x)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ
    (EuclideanSpace ℝ (Fin m ⊕ Fin m))
    (EuclideanSpace ℝ (Fin m ⊕ Fin m))).continuous.comp (blockCoordinates m).continuous

end Konig
