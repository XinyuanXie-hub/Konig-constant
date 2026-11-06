module

public import Konig.VectorSine
public import Konig.EnvelopeReduction

@[expose] public section

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace Konig

theorem unit_vector_sine_integral {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℝ ι) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (s t : ℝ) :
    (((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ Fintype.card ι)⁻¹ *
      (∫ x, ∫ y, (Real.sin (s * inner ℝ u x) : ℂ) *
        (Real.sin (t * inner ℝ v y) : ℂ) * vectorPlaneWaveKernel 0 0 x y) =
      Complex.I * Complex.exp (-((s : ℂ)^2 + (t : ℂ)^2)/4) *
        Complex.sin (((s*t*inner ℝ u v : ℝ) : ℂ)/2) := by
  have h := vector_sine_integral (s • u) (t • v)
  simpa [norm_smul, hu, hv, Real.norm_eq_abs, ← Complex.ofReal_pow,
    real_inner_smul_left, real_inner_smul_right, mul_assoc, mul_left_comm] using h

/-- Exact normalized pairing of finite sine envelopes on arbitrary unit normals. -/
theorem unit_sine_envelope_pairing {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a s : κ → ℝ) (u v : EuclideanSpace ℝ ι) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ Fintype.card ι)⁻¹ *
      (∫ x, ∫ y,
        ((∑ i, a i * Real.sin (s i * inner ℝ u x) : ℝ) : ℂ) *
        ((∑ j, a j * Real.sin (s j * inner ℝ v y) : ℝ) : ℂ) *
        vectorPlaneWaveKernel 0 0 x y) =
      Complex.I * ∑ i, ∑ j, ((a i*a j : ℝ) : ℂ) *
        Complex.exp (-((s i : ℂ)^2 + (s j : ℂ)^2)/4) *
        Complex.sin (((s i*s j*inner ℝ u v : ℝ) : ℂ)/2) := by
  rw [finite_sine_envelope_pairing]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_left_comm, ← real_inner_smul_left]
  have h := unit_vector_sine_integral u v hu hv (s i) (s j)
  simp only [← real_inner_smul_left] at h
  rw [h]
  ring

/-- Specialization to the rotating unit normals used in the Hadamard construction. -/
theorem phase_sine_envelope_pairing {m : ℕ} (hm : 0 < m)
    {κ : Type*} [Fintype κ] (a s : κ → ℝ) (θ φ : Fin m → ℝ) :
    (((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ (2*m))⁻¹ *
      (∫ x, ∫ y,
        ((∑ i, a i * Real.sin (s i * inner ℝ (phaseNormal θ) x) : ℝ) : ℂ) *
        ((∑ j, a j * Real.sin (s j * inner ℝ (phaseNormal (fun l => -φ l)) y) : ℝ) : ℂ) *
        vectorPlaneWaveKernel 0 0 x y) =
      Complex.I * ∑ i, ∑ j, ((a i*a j : ℝ) : ℂ) *
        Complex.exp (-((s i : ℂ)^2 + (s j : ℂ)^2)/4) *
        Complex.sin (((s i*s j*((m : ℝ)⁻¹ * ∑ l, Real.cos (θ l + φ l)) : ℝ) : ℂ)/2) := by
  simpa only [Fintype.card_sum, Fintype.card_fin, ← two_mul, phaseNormal_inner_neg] using
    unit_sine_envelope_pairing a s (phaseNormal θ) (phaseNormal (fun l => -φ l))
      (phaseNormal_norm hm θ) (phaseNormal_norm hm (fun l => -φ l))

end Konig
