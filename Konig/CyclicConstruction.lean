module

public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Basic.Real.Star
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace Konig.Construction

open scoped Kronecker

/-- The order-two real Hadamard matrix. -/
def hadamardTwo : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 1 ∧ j = 1 then -1 else 1

theorem hadamardTwo_isHadamard : hadamardTwo.IsHadamard := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [hadamardTwo, Unitary.mem_iff]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [hadamardTwo, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Matrix.one_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [hadamardTwo, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Matrix.one_apply]

/-- Index identification for one Sylvester doubling. -/
def doubleIndex (r : ℕ) : Fin 2 × Fin (2^r) ≃ Fin (2^(r+1)) :=
  finProdFinEquiv.trans (finCongr (by simp [Nat.pow_succ, Nat.mul_comm]))

/-- Explicit Sylvester matrices, without any existence assumption. -/
def sylvester : (r : ℕ) → Matrix (Fin (2^r)) (Fin (2^r)) ℝ
  | 0 => Matrix.of fun _ _ => 1
  | r+1 => (hadamardTwo ⊗ₖ sylvester r).reindex (doubleIndex r) (doubleIndex r)

theorem sylvester_isHadamard (r : ℕ) : (sylvester r).IsHadamard := by
  induction r with
  | zero =>
    change Matrix.IsHadamard (Matrix.of (fun _ _ : Fin 1 => (1 : ℝ)))
    constructor
    · intro i j
      norm_num [Matrix.of_apply, Unitary.mem_iff]
    · ext i j
      fin_cases i
      fin_cases j
      rw [Matrix.mul_apply]
      norm_num [Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    · ext i j
      fin_cases i
      fin_cases j
      rw [Matrix.mul_apply]
      norm_num [Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  | succ r ih =>
    exact (hadamardTwo_isHadamard.kronecker ih).reindex (doubleIndex r) (doubleIndex r)

/-- The cubic congruence used by both the Hadamard and cyclic constructions.
Here `S = 2*a+1` and the collision-free number of channels is `2*n+1`. -/
theorem cubic_parity (a n : ℤ) :
    4 ∣ (2 * a + 1) ^ 3 + 3 * (2 * a + 1) * (2 * n + 1) - 2 * n := by
  refine ⟨2*a^3 + 3*a^2 + 3*a + 3*a*n + n + 1, ?_⟩
  ring

/-- The collision-free cubic multiplier is precisely the alternating series sign. -/
theorem cubic_multiplier_parity (a : ℤ) (n : ℕ) :
    Complex.exp (((Real.pi : ℂ) * Complex.I / 2) *
      ((2 * (a : ℂ) + 1)^3 + 3*(2*(a : ℂ)+1)*(2*(n : ℂ)+1))) =
      (-1 : ℂ)^n := by
  let q : ℤ := 2*a^3 + 3*a^2 + 3*a + 3*a*(n : ℤ) + n + 1
  have hphase : ((Real.pi : ℂ) * Complex.I / 2) *
      ((2 * (a : ℂ) + 1)^3 + 3*(2*(a : ℂ)+1)*(2*(n : ℂ)+1)) =
      (n : ℂ) * ((Real.pi : ℂ) * Complex.I) +
        (q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    dsimp [q]
    push_cast
    ring
  rw [hphase, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    mul_one, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- Pairing the two diagonal phase frequencies cancels the odd powers of `b`. -/
theorem paired_cubes (S b : ℝ) :
    (S + b)^3 + (S - b)^3 = 2*S^3 + 6*S*b^2 := by
  ring

/-- The sum-of-squares identity furnished by row orthogonality. -/
theorem hadamard_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ι → ι → ℝ) (μ : ι → ℝ)
    (horth : ∀ s t, ∑ j, H s j * H t j =
      if s = t then (Fintype.card ι : ℝ) else 0) :
    ∑ j, (∑ s, H s j * μ s)^2 =
      (Fintype.card ι : ℝ) * ∑ s, (μ s)^2 := by
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl (fun s _ => Finset.sum_comm))
  simp_rw [show ∀ j s t, H s j * μ s * (H t j * μ t) =
    (H s j * H t j) * (μ s * μ t) by intros; ring]
  simp_rw [← Finset.sum_mul, horth]
  simp

/-- The energy identity applies directly to Mathlib's Hadamard predicate. -/
theorem hadamard_energy_of_isHadamard {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.IsHadamard) (μ : ι → ℝ) :
    ∑ j, (∑ s, H s j * μ s)^2 =
      (Fintype.card ι : ℝ) * ∑ s, (μ s)^2 := by
  apply hadamard_energy H μ
  intro s t
  have h := congrArg (fun M : Matrix ι ι ℝ => M s t) hH.mul_conjTranspose
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h

/-- The exact cubic identity which replaces the cyclic construction's trace calculation. -/
theorem hadamard_cubic_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.IsHadamard) (μ : ι → ℝ) (S : ℝ) :
    ∑ j, ((S + ∑ s, H s j * μ s)^3 + (S - ∑ s, H s j * μ s)^3) =
      2 * (Fintype.card ι : ℝ) * (S^3 + 3*S*(∑ s, (μ s)^2)) := by
  simp_rw [paired_cubes, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hadamard_energy_of_isHadamard H hH μ]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Real Hadamard entries have absolute value one. -/
theorem hadamard_entry_abs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.IsHadamard) (s j : ι) : |H s j| = 1 := by
  rcases Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem s j) with h | h <;>
    simp [h]

/-- A deterministic frequency bound suffices for qualitative convergence;
no fourth-moment estimate is required. -/
theorem hadamard_frequency_abs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.IsHadamard) (μ : ι → ℝ) (j : ι) :
    |∑ s, H s j * μ s| ≤ ∑ s, |μ s| := by
  calc
    _ ≤ ∑ s, |H s j * μ s| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp [abs_mul, hadamard_entry_abs H hH]

theorem hadamard_plus_frequency_abs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.IsHadamard) (μ : ι → ℝ) (j : ι) :
    |(∑ s, μ s) + ∑ s, H s j * μ s| ≤ 2 * ∑ s, |μ s| := by
  calc
    _ ≤ |∑ s, μ s| + |∑ s, H s j * μ s| := abs_add_le _ _
    _ ≤ (∑ s, |μ s|) + ∑ s, |μ s| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (hadamard_frequency_abs H hH μ j)
    _ = _ := (two_mul _).symm

theorem hadamard_minus_frequency_abs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.IsHadamard) (μ : ι → ℝ) (j : ι) :
    |(∑ s, μ s) - ∑ s, H s j * μ s| ≤ 2 * ∑ s, |μ s| := by
  calc
    _ ≤ |∑ s, μ s| + |∑ s, H s j * μ s| := abs_sub _ _
    _ ≤ (∑ s, |μ s|) + ∑ s, |μ s| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (hadamard_frequency_abs H hH μ j)
    _ = _ := (two_mul _).symm

/-- Deterministic fourth-power control; enough for each fixed series coefficient. -/
theorem hadamard_fourth_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.IsHadamard) (μ : ι → ℝ) :
    ∑ j, (|(∑ s, μ s) + ∑ s, H s j * μ s|^4 +
      |(∑ s, μ s) - ∑ s, H s j * μ s|^4) ≤
      2 * (Fintype.card ι : ℝ) * (2 * ∑ s, |μ s|)^4 := by
  calc
    _ ≤ ∑ _j : ι, ((2 * ∑ s, |μ s|)^4 + (2 * ∑ s, |μ s|)^4) := by
      apply Finset.sum_le_sum
      intro j _
      exact add_le_add
        (pow_le_pow_left₀ (abs_nonneg _) (hadamard_plus_frequency_abs H hH μ j) 4)
        (pow_le_pow_left₀ (abs_nonneg _) (hadamard_minus_frequency_abs H hH μ j) 4)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Frequencies obtained by assigning signed occurrences to channels. -/
def frequency {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    (τ : κ → ι) (σ : κ → ℝ) (s : ι) : ℝ :=
  ∑ a, if τ a = s then σ a else 0

theorem sum_frequency {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (τ : κ → ι) (σ : κ → ℝ) :
    ∑ s, frequency τ σ s = ∑ a, σ a := by
  simp only [frequency]
  rw [Finset.sum_comm]
  simp

theorem frequency_at_channel {κ ι : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (τ : κ → ι) (hτ : Function.Injective τ) (σ : κ → ℝ) (a : κ) :
    frequency τ σ (τ a) = σ a := by
  simp [frequency, hτ.eq_iff]

/-- Collision-free frequencies preserve the sum of squares. -/
theorem frequency_energy {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq κ] [DecidableEq ι]
    (τ : κ → ι) (hτ : Function.Injective τ) (σ : κ → ℝ) :
    ∑ s, (frequency τ σ s)^2 = ∑ a, (σ a)^2 := by
  calc
    _ = ∑ s, (frequency τ σ s) * ∑ a, if τ a = s then σ a else 0 := by
      simp only [frequency, pow_two]
    _ = ∑ a, ∑ s, (frequency τ σ s) * (if τ a = s then σ a else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by simp [mul_ite, frequency_at_channel τ hτ, pow_two]

theorem sum_abs_frequency_le {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq ι] (τ : κ → ι) (σ : κ → ℝ) :
    ∑ s, |frequency τ σ s| ≤ ∑ a, |σ a| := by
  calc
    _ ≤ ∑ s, ∑ a, |if τ a = s then σ a else 0| :=
      Finset.sum_le_sum (fun s _ => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [apply_ite abs, abs_zero]
      simp

/-- Integer and real signs for the finite coefficient expansion. -/
def intSign (b : Bool) : ℤ := if b then 1 else -1

def realSign (b : Bool) : ℝ := (intSign b : ℝ)

@[simp] theorem abs_realSign (b : Bool) : |realSign b| = 1 := by
  cases b <;> norm_num [realSign, intSign]

@[simp] theorem sq_realSign (b : Bool) : realSign b ^ 2 = 1 := by
  cases b <;> norm_num [realSign, intSign]

theorem odd_sign_sum (n : ℕ) (σ : Fin (2*n+1) → Bool) :
    ∃ a : ℤ, ∑ j, intSign (σ j) = 2*a+1 := by
  let b : Fin (2*n+1) → ℤ := fun j => if σ j then 0 else -1
  have hb (j) : intSign (σ j) = 2*b j+1 := by
    cases h : σ j <;> norm_num [intSign, b, h]
  refine ⟨(∑ j, b j) + n, ?_⟩
  simp_rw [hb]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp
  ring

theorem sign_frequency_l1_le {k m : ℕ} (τ : Fin k → Fin m) (σ : Fin k → Bool) :
    ∑ s, |frequency τ (fun a => realSign (σ a)) s| ≤ (k : ℝ) := by
  simpa using sum_abs_frequency_le τ (fun a => realSign (σ a))

theorem sign_frequency_energy {k m : ℕ} (τ : Fin k → Fin m)
    (hτ : Function.Injective τ) (σ : Fin k → Bool) :
    ∑ s, (frequency τ (fun a => realSign (σ a)) s)^2 = (k : ℝ) := by
  rw [frequency_energy τ hτ]
  simp

/-- The total frequency of an odd word is an odd integer, even if channels collide. -/
theorem odd_sign_frequency_sum {n m : ℕ} (τ : Fin (2*n+1) → Fin m)
    (σ : Fin (2*n+1) → Bool) :
    ∃ a : ℤ, ∑ s, frequency τ (fun a => realSign (σ a)) s = 2*(a : ℝ)+1 := by
  obtain ⟨a, ha⟩ := odd_sign_sum n σ
  refine ⟨a, ?_⟩
  rw [sum_frequency]
  simpa [realSign] using congrArg (fun z : ℤ => (z : ℝ)) ha

theorem collision_free_multiplier {n m : ℕ} (τ : Fin (2*n+1) → Fin m)
    (hτ : Function.Injective τ) (σ : Fin (2*n+1) → Bool) :
    let μ := frequency τ (fun a => realSign (σ a))
    Complex.exp (((Real.pi : ℂ) * Complex.I / 2) *
      (((∑ s, μ s : ℝ) : ℂ)^3 +
        3*((∑ s, μ s : ℝ) : ℂ)*((∑ s, (μ s)^2 : ℝ) : ℂ))) = (-1 : ℂ)^n := by
  dsimp only
  obtain ⟨a, ha⟩ := odd_sign_frequency_sum τ σ
  rw [ha, sign_frequency_energy τ hτ σ]
  push_cast
  exact cubic_multiplier_parity a n

end Konig.Construction
