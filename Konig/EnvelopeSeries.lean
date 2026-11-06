module

public import Konig.SeriesLimit
public import Konig.GaussianSineGram

@[expose] public section

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Konig

def correctedSineSeries (T : ℕ → ℂ) (q : ℝ) : ℂ :=
  ∑' n : ℕ, ((-1 : ℂ)^n * (q : ℂ)^(2*n+1) /
    (Nat.factorial (2*n+1) : ℂ)) * T n

def envelopeSeries {k : ℕ} (T : ℕ → ℂ) (a s : Fin k → ℝ) : ℝ :=
  (∑ i, ∑ j, ((a i * a j * Real.exp (-(s i ^ 2 + s j ^ 2) / 4) : ℝ) : ℂ) *
    correctedSineSeries T (s i * s j / 2)).re

theorem tendsto_envelopeSeries {k : ℕ} (T : ℕ → ℕ → ℂ)
    (hbound : ∀ r n, ‖T r n‖ ≤ 1)
    (hlim : ∀ n, Tendsto (fun r => T r n) atTop (𝓝 ((-1 : ℂ)^n)))
    (a s : Fin k → ℝ) :
    Tendsto (fun r => envelopeSeries (T r) a s) atTop
      (𝓝 (∫ x, (∑ i, a i * Real.sin (s i * x)) ^ 2 ∂GaussianSineGram.gaussian)) := by
  rw [GaussianSineGram.integral_sine_sum_sq]
  have ht := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ =>
      (tendsto_const_nhds (x := ((a i * a j * Real.exp (-(s i ^ 2 + s j ^ 2) / 4) : ℝ) : ℂ))).mul
        (tendsto_corrected_sine_series T hbound hlim (s i * s j / 2))))
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  simpa only [envelopeSeries, correctedSineSeries, Function.comp_def, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.sinh_ofReal_re, mul_assoc] using hr

end Konig
