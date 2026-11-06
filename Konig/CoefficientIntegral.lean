module

public import Konig.CosineExpansion
public import Konig.EnvelopeReduction

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace Konig.Construction

def phaseKernel {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) (μ : Fin m → ℝ)
    (x y : EuclideanSpace ℝ (Fin m ⊕ Fin m)) : ℂ :=
  Complex.exp (-(((‖x‖ : ℝ) : ℂ)^2 + ((‖y‖ : ℝ) : ℂ)^2) / 2 +
    Complex.I * (inner ℝ x y : ℝ) +
    Complex.I * ((∑ s, μ s * (hadamardPhase H ε x s + hadamardPhase H ε y s) : ℝ) : ℂ))

theorem phaseKernel_norm {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (μ : Fin m → ℝ) (x y : EuclideanSpace ℝ (Fin m ⊕ Fin m)) :
    ‖phaseKernel H ε μ x y‖ =
      Real.exp (-(‖x‖^2 / 2)) * Real.exp (-(‖y‖^2 / 2)) := by
  simp only [phaseKernel, Complex.norm_exp]
  rw [← Real.exp_add]
  congr 1
  simp [← Complex.ofReal_pow]
  ring

theorem phaseKernel_integrable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (μ : Fin m → ℝ) :
    Integrable (Function.uncurry (phaseKernel H ε μ)) (volume.prod volume) := by
  have hG : Integrable (fun x : EuclideanSpace ℝ (Fin m ⊕ Fin m) =>
      Real.exp (-(‖x‖^2 / 2))) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (b := (1 / 2 : ℂ)) (by norm_num) 0 (0 : EuclideanSpace ℝ (Fin m ⊕ Fin m))).re
    simpa [← Complex.ofReal_pow, Complex.exp_re, Complex.exp_ofReal_re,
      div_eq_mul_inv, mul_comm] using h
  apply (hG.mul_prod hG).mono'
  · apply Continuous.aestronglyMeasurable
    unfold Function.uncurry phaseKernel hadamardPhase
    fun_prop
  · exact Filter.Eventually.of_forall (fun p => (phaseKernel_norm H ε μ p.1 p.2).le)

theorem phaseMultiplier_eq_phaseKernel {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (ε : ℝ) (μ : Fin m → ℝ) :
    phaseMultiplier H ε μ =
      (((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ (2*m))⁻¹ *
      ∫ x, ∫ y, phaseKernel H ε μ x y := phaseMultiplier_eq_integral H ε μ

def phaseCorrelation {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (x y : EuclideanSpace ℝ (Fin m ⊕ Fin m)) : ℝ :=
  (m : ℝ)⁻¹ * ∑ j, Real.cos (hadamardPhase H ε x j + hadamardPhase H ε y j)

theorem phaseKernel_expansion {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (k : ℕ) (x y : EuclideanSpace ℝ (Fin m ⊕ Fin m)) :
    vectorPlaneWaveKernel 0 0 x y * (phaseCorrelation H ε x y : ℂ)^k =
      ((m : ℂ)^k * (2 : ℂ)^k)⁻¹ *
      ∑ τ : Fin k → Fin m, ∑ σ : Fin k → Bool,
        phaseKernel H ε (signedFrequency τ σ) x y := by
  have he (μ : Fin m → ℝ) : vectorPlaneWaveKernel 0 0 x y *
      Complex.exp (Complex.I * ∑ j, (μ j : ℂ) *
        ((hadamardPhase H ε x j + hadamardPhase H ε y j : ℝ) : ℂ)) =
      phaseKernel H ε μ x y := by
    unfold vectorPlaneWaveKernel phaseKernel
    rw [← Complex.exp_add]
    congr 1
    push_cast
    simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero]
  simp only [Finset.mul_sum] at he
  unfold phaseCorrelation
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_sum]
  rw [cosine_average_pow]
  rw [mul_left_comm]
  simp only [Finset.mul_sum, he]

theorem phaseCoefficient_eq_integral {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (ε : ℝ) (k : ℕ) :
    phaseCoefficient H ε k =
      (((Real.sqrt 2 * Real.pi : ℝ) : ℂ) ^ (2*m))⁻¹ *
      ∫ x, ∫ y, vectorPlaneWaveKernel 0 0 x y * (phaseCorrelation H ε x y : ℂ)^k := by
  simp_rw [phaseKernel_expansion, integral_const_mul]
  rw [integral_integral_finsetSum volume volume Finset.univ
    (fun τ x y => ∑ σ : Fin k → Bool, phaseKernel H ε (signedFrequency τ σ) x y)
    (fun τ _ => integrable_finsetSum Finset.univ (fun σ _ => phaseKernel_integrable H ε _))]
  simp_rw [integral_integral_finsetSum volume volume Finset.univ
    (fun σ x y => phaseKernel H ε (signedFrequency _ σ) x y)
    (fun σ _ => phaseKernel_integrable H ε _)]
  unfold phaseCoefficient
  simp_rw [phaseMultiplier_eq_phaseKernel]
  simp only [← Finset.mul_sum]
  ring

theorem continuous_phaseCorrelation {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) :
    Continuous (Function.uncurry (phaseCorrelation H ε)) := by
  unfold Function.uncurry phaseCorrelation hadamardPhase
  fun_prop

theorem phaseCorrelation_abs_le_one {m : ℕ} (hm : 0 < m)
    (H : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (x y : EuclideanSpace ℝ (Fin m ⊕ Fin m)) : |phaseCorrelation H ε x y| ≤ 1 := by
  have h := abs_real_inner_le_norm (phaseNormal (hadamardPhase H ε x))
    (phaseNormal (fun s => -hadamardPhase H ε y s))
  rw [phaseNormal_inner_neg, phaseNormal_norm hm, phaseNormal_norm hm, one_mul] at h
  exact h

end Konig.Construction
