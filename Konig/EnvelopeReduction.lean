module

public import Konig.Integrability
public import Konig.VectorPlaneWave
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators
noncomputable section
namespace Konig

/-- Regroup two input blocks so that the phase variables are integrated first. -/
def envelopeShuffle {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] :
    ((A × B) × (C × D)) ≃ᵐ ((B × D) × (A × C)) where
  toEquiv := {
    toFun := fun p => ((p.1.2, p.2.2), (p.1.1, p.2.1))
    invFun := fun p => ((p.2.1, p.1.1), (p.2.2, p.1.2))
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  measurable_toFun := by
    change Measurable (fun p : (A × B) × (C × D) => ((p.1.2, p.2.2), (p.1.1, p.2.1)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : (B × D) × (A × C) => ((p.2.1, p.1.1), (p.2.2, p.1.2)))
    fun_prop

theorem envelopeShuffle_measurePreserving {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) (σ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite σ] :
    MeasurePreserving (envelopeShuffle (A := A) (B := B) (C := C) (D := D))
      ((μ.prod ν).prod (ρ.prod σ)) ((ν.prod σ).prod (μ.prod ρ)) := by
  have h1 := (measurePreserving_swap (μ := μ) (ν := ν)).prod
    (measurePreserving_swap (μ := ρ) (ν := σ))
  have h2 := measurePreserving_prodAssoc ν μ (σ.prod ρ)
  have h3 := (MeasurePreserving.id ν).prod
    ((measurePreserving_prodAssoc μ σ ρ).symm MeasurableEquiv.prodAssoc)
  have h4 := (MeasurePreserving.id ν).prod
    ((measurePreserving_swap (μ := μ) (ν := σ)).prod (MeasurePreserving.id ρ))
  have h5 := (MeasurePreserving.id ν).prod (measurePreserving_prodAssoc σ μ ρ)
  have h6 := (measurePreserving_prodAssoc ν σ (μ.prod ρ)).symm MeasurableEquiv.prodAssoc
  exact h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1))))

/-- Fubini regrouping from `(X,u),(Y,v)` to `u,v,X,Y`. -/
theorem integral_envelope_shuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) (σ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite σ]
    (H : (A × B) → (C × D) → ℂ)
    (hH : Integrable (Function.uncurry H) ((μ.prod ν).prod (ρ.prod σ))) :
    (∫ p, ∫ q, H p q ∂ρ.prod σ ∂μ.prod ν) =
      ∫ u, ∫ v, ∫ x, ∫ y, H (x,u) (y,v) ∂ρ ∂μ ∂σ ∂ν := by
  let e := envelopeShuffle (A := A) (B := B) (C := C) (D := D)
  let K := fun p : (B × D) × (A × C) => H (p.2.1, p.1.1) (p.2.2, p.1.2)
  have he := envelopeShuffle_measurePreserving μ ν ρ σ
  have hK : Integrable K ((ν.prod σ).prod (μ.prod ρ)) :=
    (he.integrable_comp_emb e.measurableEmbedding).mp hH
  rw [integral_integral hH]
  calc
    (∫ p, Function.uncurry H p ∂(μ.prod ν).prod (ρ.prod σ)) =
        ∫ p, K p ∂(ν.prod σ).prod (μ.prod ρ) :=
      he.integral_comp e.measurableEmbedding K
    _ = ∫ uv, ∫ xy, K (uv,xy) ∂μ.prod ρ ∂ν.prod σ := integral_prod K hK
    _ = ∫ u, ∫ v, ∫ xy, K ((u,v),xy) ∂μ.prod ρ ∂σ ∂ν :=
      integral_prod _ hK.integral_prod_left
    _ = _ := by
      apply integral_congr_ae
      have hs := hK.prod_right_ae
      have hs := ae_ae_of_ae_prod hs
      filter_upwards [hs] with u hu
      apply integral_congr_ae
      filter_upwards [hu] with v hv
      exact integral_prod _ hv

/-- Expand a finite combination inside an iterated integral without assuming
pointwise integrability of every slice. Joint integrability is sufficient. -/
theorem integral_integral_finsetSum {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (s : Finset ι) (F : ι → A → B → ℂ)
    (hF : ∀ i ∈ s, Integrable (Function.uncurry (F i)) (μ.prod ν)) :
    (∫ x, ∫ y, ∑ i ∈ s, F i x y ∂ν ∂μ) =
      ∑ i ∈ s, ∫ x, ∫ y, F i x y ∂ν ∂μ := by
  have hsum : Integrable (fun p : A × B => ∑ i ∈ s, F i p.1 p.2) (μ.prod ν) :=
    integrable_finsetSum s hF
  rw [integral_integral hsum]
  change (∫ p, ∑ i ∈ s, Function.uncurry (F i) p ∂μ.prod ν) = _
  rw [integral_finsetSum s hF]
  apply Finset.sum_congr rfl
  intro i hi
  exact (integral_integral (hF i hi)).symm

/-- Finite bilinear expansion of an oscillatory kernel pairing. -/
theorem integral_integral_bilinear_finsetSum {A B ι κ : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [Fintype ι] [Fintype κ]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (a : ι → ℂ) (b : κ → ℂ) (F : ι → A → ℂ) (G : κ → B → ℂ)
    (K : A → B → ℂ)
    (hFG : ∀ i j, Integrable (fun p : A × B => F i p.1 * G j p.2 * K p.1 p.2)
      (μ.prod ν)) :
    (∫ x, ∫ y, (∑ i, a i * F i x) * (∑ j, b j * G j y) * K x y ∂ν ∂μ) =
      ∑ i, ∑ j, (a i * b j) * (∫ x, ∫ y, F i x * G j y * K x y ∂ν ∂μ) := by
  have hexpand (x : A) (y : B) :
      (∑ i, a i * F i x) * (∑ j, b j * G j y) * K x y =
      ∑ i, ∑ j, (a i * b j) * (F i x * G j y * K x y) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_left_comm, mul_comm]
  simp_rw [hexpand]
  have hij (i : ι) (j : κ) : Integrable
      (fun p : A × B => (a i * b j) * (F i p.1 * G j p.2 * K p.1 p.2)) (μ.prod ν) :=
    (hFG i j).const_mul _
  have hi (i : ι) : Integrable
      (fun p : A × B => ∑ j, (a i * b j) * (F i p.1 * G j p.2 * K p.1 p.2))
      (μ.prod ν) := integrable_finsetSum _ (fun j _ => hij i j)
  rw [integral_integral_finsetSum μ ν Finset.univ
    (fun i x y => ∑ j, (a i * b j) * (F i x * G j y * K x y)) (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_integral_finsetSum μ ν Finset.univ
    (fun j x y => (a i * b j) * (F i x * G j y * K x y)) (fun j _ => hij i j)]
  simp_rw [integral_const_mul]

/-- The plane-wave insertions do not change the Gaussian absolute value. -/
theorem vectorPlaneWaveKernel_norm {ι : Type*} [Fintype ι]
    (u v x y : EuclideanSpace ℝ ι) :
    ‖vectorPlaneWaveKernel u v x y‖ =
      Real.exp (-(‖x‖ ^ 2 / 2)) * Real.exp (-(‖y‖ ^ 2 / 2)) := by
  simp only [vectorPlaneWaveKernel, Complex.norm_exp]
  rw [← Real.exp_add]
  congr 1
  simp [← Complex.ofReal_pow]
  ring

/-- Joint absolute integrability of the oscillatory Gaussian. -/
theorem vectorPlaneWaveKernel_integrable {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℝ ι) :
    Integrable (Function.uncurry (vectorPlaneWaveKernel u v)) (volume.prod volume) := by
  have hG : Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (-(‖x‖ ^ 2 / 2))) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (b := (1 / 2 : ℂ)) (by norm_num) 0 (0 : EuclideanSpace ℝ ι)).re
    simpa [← Complex.ofReal_pow, Complex.exp_re, Complex.exp_ofReal_re,
      div_eq_mul_inv, mul_comm] using h
  apply (hG.mul_prod hG).mono'
  · apply Continuous.aestronglyMeasurable
    unfold Function.uncurry vectorPlaneWaveKernel
    fun_prop
  · exact Filter.Eventually.of_forall (fun p => (vectorPlaneWaveKernel_norm u v p.1 p.2).le)

/-- Joint integrability of the sine-sine insertion used in a finite envelope. -/
theorem vector_sine_pair_integrable {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℝ ι) :
    Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      (Real.sin (inner ℝ u p.1) : ℂ) * (Real.sin (inner ℝ v p.2) : ℂ) *
        vectorPlaneWaveKernel 0 0 p.1 p.2) (volume.prod volume) := by
  apply (vectorPlaneWaveKernel_integrable (0 : EuclideanSpace ℝ ι) 0).bdd_mul
    (show AEStronglyMeasurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      (Real.sin (inner ℝ u p.1) : ℂ) * (Real.sin (inner ℝ v p.2) : ℂ)) (volume.prod volume) from
      (by fun_prop : Continuous _).aestronglyMeasurable)
  filter_upwards [] with p
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ 1 * 1 := mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

/-- A finite sine envelope reduces exactly to its finitely many sine pairings. -/
theorem finite_sine_envelope_pairing {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a s : κ → ℝ) (u v : EuclideanSpace ℝ ι) :
    (∫ x, ∫ y,
      ((∑ i, a i * Real.sin (s i * inner ℝ u x) : ℝ) : ℂ) *
      ((∑ j, a j * Real.sin (s j * inner ℝ v y) : ℝ) : ℂ) *
      vectorPlaneWaveKernel 0 0 x y) =
      ∑ i, ∑ j, ((a i * a j : ℝ) : ℂ) *
        (∫ x, ∫ y, (Real.sin (inner ℝ (s i • u) x) : ℂ) *
          (Real.sin (inner ℝ (s j • v) y) : ℂ) * vectorPlaneWaveKernel 0 0 x y) := by
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, ← real_inner_smul_left]
  exact integral_integral_bilinear_finsetSum volume volume
    (fun i => (a i : ℂ)) (fun i => (a i : ℂ))
    (fun i x => (Real.sin (inner ℝ (s i • u) x) : ℂ))
    (fun i y => (Real.sin (inner ℝ (s i • v) y) : ℂ))
    (vectorPlaneWaveKernel 0 0) (fun i j => vector_sine_pair_integrable (s i • u) (s j • v))

/-- Abstract envelope reduction after regrouping the half-space and phase blocks.
The inner-pairing formula can be supplied by the finite sine-envelope identity. -/
theorem integral_envelope_kernel_reduction {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (F G : A × B → ℂ) (K : A → A → ℂ) (L : B → B → ℂ) (R : B → B → ℂ)
    (hH : Integrable (fun p : (A × B) × (A × B) =>
      F p.1 * G p.2 * (K p.1.1 p.2.1 * L p.1.2 p.2.2))
      ((μ.prod ν).prod (μ.prod ν)))
    (hR : ∀ u v, (∫ x, ∫ y, F (x,u) * G (y,v) * K x y ∂μ ∂μ) = R u v) :
    (∫ p, ∫ q, F p * G q * (K p.1 q.1 * L p.2 q.2) ∂μ.prod ν ∂μ.prod ν) =
      ∫ u, ∫ v, R u v * L u v ∂ν ∂ν := by
  rw [integral_envelope_shuffle μ ν μ ν
    (fun p q => F p * G q * (K p.1 q.1 * L p.2 q.2)) hH]
  apply integral_congr_ae
  filter_upwards [] with u
  apply integral_congr_ae
  filter_upwards [] with v
  simp_rw [← mul_assoc, integral_mul_const]
  rw [hR]

/-- Joint integrability for two bounded continuous envelopes over two Gaussian blocks. -/
theorem integrable_block_envelope {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hFb : ∀ p, |F p| ≤ 1) (hGb : ∀ p, |G p| ≤ 1) :
    Integrable (fun p : (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) ×
        (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) =>
      (F p.1 : ℂ) * (G p.2 : ℂ) * (vectorPlaneWaveKernel 0 0 p.1.1 p.2.1 *
        vectorPlaneWaveKernel 0 0 p.1.2 p.2.2)) (volume.prod volume) := by
  have he := envelopeShuffle_measurePreserving
    (volume : Measure (EuclideanSpace ℝ ι)) (volume : Measure (EuclideanSpace ℝ κ))
    (volume : Measure (EuclideanSpace ℝ ι)) (volume : Measure (EuclideanSpace ℝ κ))
  have hbase := (vectorPlaneWaveKernel_integrable (0 : EuclideanSpace ℝ κ) 0).mul_prod
    (vectorPlaneWaveKernel_integrable (0 : EuclideanSpace ℝ ι) 0)
  have hb := (he.integrable_comp_emb envelopeShuffle.measurableEmbedding).mpr hbase
  have hbase' : Integrable (fun p : (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) ×
        (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) =>
      vectorPlaneWaveKernel 0 0 p.1.1 p.2.1 * vectorPlaneWaveKernel 0 0 p.1.2 p.2.2)
      (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod, Function.comp_def, envelopeShuffle, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
      Function.uncurry_apply_pair, mul_comm] using hb
  apply hbase'.bdd_mul (c := 1)
    ((Complex.continuous_ofReal.comp (hF.comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp (hG.comp continuous_snd))).aestronglyMeasurable
  filter_upwards [] with p
  change ‖(F p.1 : ℂ) * (G p.2 : ℂ)‖ ≤ 1
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_one₀ (hFb p.1) (abs_nonneg _) (hGb p.2)

end Konig
