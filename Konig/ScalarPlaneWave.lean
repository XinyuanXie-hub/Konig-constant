module

public import Konig.ScalarGaussian

@[expose] public section

open MeasureTheory
noncomputable section
namespace Konig

def planeWaveKernel (u v x y : ℝ) : ℂ :=
  Complex.exp (-((x : ℂ)^2 + (y : ℂ)^2) / 2 +
    Complex.I * x * y + Complex.I * u * x + Complex.I * v * y)

private theorem planeWave_exponent (u v x y : ℝ) :
    -((x : ℂ)^2 + (y : ℂ)^2) / 2 +
      Complex.I * x * y + Complex.I * u * x + Complex.I * v * y =
    (-1 / 2 : ℂ) * (y : ℂ)^2 + (Complex.I * (x + v)) * y +
      (-(x : ℂ)^2 / 2 + Complex.I * u * x) := by push_cast; ring

theorem planeWave_inner_integrable (u v x : ℝ) :
    Integrable (planeWaveKernel u v x) := by
  unfold planeWaveKernel
  simp_rw [planeWave_exponent]
  exact integrable_cexp_quadratic' (by norm_num : (-1 / 2 : ℂ).re < 0) _ _

theorem planeWave_inner (u v x : ℝ) :
    (∫ y : ℝ, planeWaveKernel u v x y) =
      ((Real.pi : ℂ) / (1 / 2)) ^ (1 / 2 : ℂ) *
      Complex.exp (-(x : ℂ)^2 + (Complex.I * u - v) * x - (v : ℂ)^2 / 2) := by
  unfold planeWaveKernel
  simp_rw [planeWave_exponent]
  rw [integral_cexp_quadratic (by norm_num : (-1 / 2 : ℂ).re < 0)]
  congr 1
  · congr 2; ring
  · congr 1
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring

theorem planeWave_outer_integrable (u v : ℝ) :
    Integrable (fun x : ℝ => ∫ y : ℝ, planeWaveKernel u v x y) := by
  simp_rw [planeWave_inner]
  have h := integrable_cexp_quadratic' (by norm_num : (-1 : ℂ).re < 0)
    (Complex.I * u - v) (-(v : ℂ)^2 / 2)
  convert h.const_mul (((Real.pi : ℂ) / (1 / 2)) ^ (1 / 2 : ℂ)) using 1 <;>
    congr 1 <;> ext x <;> congr 2 <;> ring

theorem planeWave_integral (u v : ℝ) :
    (∫ x : ℝ, ∫ y : ℝ, planeWaveKernel u v x y) =
      ((Real.pi : ℂ) / (1 / 2)) ^ (1 / 2 : ℂ) *
      (Real.pi : ℂ) ^ (1 / 2 : ℂ) *
      Complex.exp (-((u : ℂ)^2 + (v : ℂ)^2) / 4 - Complex.I * u * v / 2) := by
  simp_rw [planeWave_inner]
  rw [integral_const_mul]
  have he (x : ℝ) : -(x : ℂ)^2 + (Complex.I * u - v) * x - (v : ℂ)^2 / 2 =
      (-1 : ℂ) * (x : ℂ)^2 + (Complex.I * u - v) * x + (-(v : ℂ)^2 / 2) := by ring
  simp_rw [he]
  rw [integral_cexp_quadratic (by norm_num : (-1 : ℂ).re < 0)]
  have he2 : -(v : ℂ)^2 / 2 - (Complex.I * u - v)^2 / (4 * (-1)) =
      -((u : ℂ)^2 + (v : ℂ)^2) / 4 - Complex.I * u * v / 2 := by
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [he2]
  norm_num
  ring

theorem planeWave_integral_normalized (u v : ℝ) :
    ((Real.sqrt 2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ x : ℝ, ∫ y : ℝ, planeWaveKernel u v x y) =
      Complex.exp (-((u : ℂ)^2 + (v : ℂ)^2) / 4 - Complex.I * u * v / 2) := by
  rw [planeWave_integral, gaussian_pair_prefactor, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast mul_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)) Real.pi_ne_zero

theorem planeWave_integral_standard (u v : ℝ) :
    (∫ x : ℝ, ∫ y : ℝ, planeWaveKernel u v x y) =
      ((Real.sqrt 2 * Real.pi : ℝ) : ℂ) *
      Complex.exp (-((u : ℂ)^2 + (v : ℂ)^2) / 4 - Complex.I * u * v / 2) := by
  rw [planeWave_integral, gaussian_pair_prefactor]

end Konig
