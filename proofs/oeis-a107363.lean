import OMAStatements.S_oeis_a107363

-- Creighton Dement conjectured the Fibonacci and Pellian descriptions in OEIS A107363. The six residue classes satisfy the same second-order recurrence.

namespace OMA.A107363

open PowerSeries S_oeis_a107363

lemma num_expanded : num =
    (1 + X - X^2 + X^3 + X^4 + X^4 + X^6 - X^7 - X^8 - X^8 - X^8 - X^9 : ℤ⟦X⟧) := by
  unfold num
  ring

lemma a_coeff_equation (n : ℕ) : a n = coeff n num
    + 4 * (if 6 ≤ n then a (n - 6) else 0)
    + (if 12 ≤ n then a (n - 12) else 0) := by
  let f := num * invOfUnit den 1
  have hd : den = (1 - 4 * X^6 - X^12 : ℤ⟦X⟧) := by unfold den; ring
  have hc : constantCoeff den = (1 : ℤˣ) := by simp [den]
  have he : f - (f*X^6 + f*X^6 + f*X^6 + f*X^6) - f*X^12 = num := by
    calc
      _ = f * den := by rw [hd]; ring
      _ = num := by dsimp [f]; rw [mul_assoc, invOfUnit_mul den 1 hc, mul_one]
  have hh := congrArg (coeff n) he
  simp only [map_sub, map_add, coeff_mul_X_pow'] at hh
  change coeff n f = coeff n num
    + 4 * (if 6 ≤ n then coeff (n - 6) f else 0)
    + (if 12 ≤ n then coeff (n - 12) f else 0)
  linarith only [hh]

lemma a_recurrence (n : ℕ) : a (n + 12) = 4 * a (n + 6) + a n := by
  have h := a_coeff_equation (n + 12)
  simpa [num_expanded, map_add, map_sub, coeff_one, coeff_X, coeff_X_pow,
    show 6 ≤ n + 12 by omega, show n + 12 - 6 = n + 6 by omega] using h

@[simp] lemma a_zero : a 0 = 1 := by
  have h := a_coeff_equation 0
  norm_num [num_expanded, map_add, map_sub, coeff_X, coeff_X_pow, coeff_one] at h
  exact h

@[simp] lemma a_one : a 1 = 1 := by
  have h := a_coeff_equation 1
  norm_num [num_expanded, map_add, map_sub, coeff_X, coeff_X_pow, coeff_one] at h
  exact h

@[simp] lemma a_two : a 2 = -1 := by
  have h := a_coeff_equation 2
  norm_num [num_expanded, map_add, map_sub, coeff_X, coeff_X_pow, coeff_one] at h
  exact h

@[simp] lemma a_three : a 3 = 1 := by
  have h := a_coeff_equation 3
  norm_num [num_expanded, map_add, map_sub, coeff_X, coeff_X_pow, coeff_one] at h
  exact h

@[simp] lemma a_four : a 4 = 2 := by
  have h := a_coeff_equation 4
  norm_num [num_expanded, map_add, map_sub, coeff_X, coeff_X_pow, coeff_one] at h
  exact h

@[simp] lemma a_five : a 5 = 0 := by
  have h := a_coeff_equation 5
  norm_num [num_expanded, map_add, map_sub, coeff_X, coeff_X_pow, coeff_one] at h
  exact h

@[simp] lemma a_six : a 6 = 5 := by
  have h := a_coeff_equation 6
  norm_num [num_expanded, map_add, map_sub, coeff_X, coeff_X_pow, coeff_one] at h
  exact h

@[simp] lemma a_seven : a 7 = 3 := by
  have h := a_coeff_equation 7
  norm_num [num_expanded, map_add, map_sub, coeff_X, coeff_X_pow, coeff_one] at h
  exact h

@[simp] lemma a_eight : a 8 = -7 := by
  have h := a_coeff_equation 8
  norm_num [num_expanded, map_add, map_sub, coeff_X, coeff_X_pow, coeff_one] at h
  exact h

@[simp] lemma a_nine : a 9 = 3 := by
  have h := a_coeff_equation 9
  norm_num [num_expanded, map_add, map_sub, coeff_X, coeff_X_pow, coeff_one] at h
  exact h

@[simp] lemma a_ten : a 10 = 8 := by
  have h := a_coeff_equation 10
  norm_num [num_expanded, map_add, map_sub, coeff_X, coeff_X_pow, coeff_one] at h
  exact h

@[simp] lemma a_eleven : a 11 = 0 := by
  have h := a_coeff_equation 11
  norm_num [num_expanded, map_add, map_sub, coeff_X, coeff_X_pow, coeff_one] at h
  exact h

end OMA.A107363

namespace OMA.A107363

open S_oeis_a107363

def expected (k : ℕ) : ℕ → ℤ
  | 0 => Nat.fib (3 * k + 2)
  | 1 => Nat.fib (3 * k + 1)
  | 2 => -b k
  | 3 => Nat.fib (3 * k + 1)
  | 4 => Nat.fib (3 * k + 3)
  | _ => 0

lemma fib_six (n : ℕ) : Nat.fib (n + 6) = 4 * Nat.fib (n + 3) + Nat.fib n := by
  have h₀ := @Nat.fib_add_two n
  have h₁ := @Nat.fib_add_two (n + 1)
  have h₂ := @Nat.fib_add_two (n + 2)
  have h₃ := @Nat.fib_add_two (n + 3)
  have h₄ := @Nat.fib_add_two (n + 4)
  norm_num [Nat.add_assoc] at h₀ h₁ h₂ h₃ h₄
  omega

lemma expected_step (k r : ℕ) (hr : r < 6) :
    expected (k + 2) r = 4 * expected (k + 1) r + expected k r := by
  have hf (s : ℕ) : (Nat.fib (3 * (k + 2) + s) : ℤ) =
      4 * Nat.fib (3 * (k + 1) + s) + Nat.fib (3 * k + s) := by
    rw [show 3 * (k + 2) + s = (3 * k + s) + 6 by omega,
      show 3 * (k + 1) + s = (3 * k + s) + 3 by omega]
    exact_mod_cast fib_six (3 * k + s)
  interval_cases r <;> simp [expected, hf, b]
  ring

theorem columns (k r : ℕ) (hr : r < 6) : a (6 * k + r) = expected k r := by
  induction k using Nat.twoStepInduction with
  | zero => interval_cases r <;> norm_num [expected, Nat.fib, b]
  | one => interval_cases r <;> norm_num [expected, Nat.fib, b]
  | more k ih₀ ih₁ =>
    rw [show 6 * (k + 2) + r = (6 * k + r) + 12 by omega, a_recurrence,
      show 6 * k + r + 6 = 6 * (k + 1) + r by omega, ih₀, ih₁, expected_step k r hr]

end OMA.A107363

namespace OMA.A107363

open OMA.S_oeis_a107363

lemma pell_positive : ∀ k : ℕ, 0 < b k
  | 0 => by decide
  | 1 => by decide
  | k + 2 => by
    have h₀ := pell_positive k
    have h₁ := pell_positive (k + 1)
    rw [b]
    omega

theorem finish (h : ∀ k r : ℕ, r < 6 → a (6 * k + r) = expected k r) :
    Set.range (fun n : ℕ => (Nat.fib n : ℤ)) = {x : ℤ | ∃ n : ℕ, a n = x ∧ 0 ≤ x} ∧
    Set.range (fun n : ℕ => (Nat.fib n : ℤ)) = {x : ℤ | ∃ n : ℕ, n % 6 ≠ 2 ∧ a n = x} ∧
    ∀ n : ℕ, a (6 * n + 2) = - b n := by
  have value (i : ℕ) : a i = expected (i / 6) (i % 6) := by
    simpa only [Nat.div_add_mod] using h (i / 6) (i % 6) (by omega)
  have member (i : ℕ) (hi : i % 6 ≠ 2) : a i ∈ Set.range (fun n : ℕ => (Nat.fib n : ℤ)) := by
    rw [value]
    have hr : i % 6 < 6 := by omega
    generalize i % 6 = r at hi hr ⊢
    interval_cases r
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · contradiction
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨0, rfl⟩
  have regular (i : ℕ) : i % 6 ≠ 2 ↔ 0 ≤ a i := by
    constructor
    · intro hi
      obtain ⟨j, hj⟩ := member i hi
      rw [← hj]
      exact Int.natCast_nonneg _
    · intro ha he
      have hv := value i
      rw [he] at hv
      change a i = -b (i / 6) at hv
      have hp := pell_positive (i / 6)
      omega
  have realizes (j : ℕ) : ∃ i : ℕ, i % 6 ≠ 2 ∧ a i = (Nat.fib j : ℤ) := by
    cases j with
    | zero => exact ⟨5, by decide, h 0 5 (by decide)⟩
    | succ j =>
      have witness (r : ℕ) (hr : r < 6) (hnot : r ≠ 2)
          (hv : expected (j / 3) r = (Nat.fib (j + 1) : ℤ)) :
          ∃ i : ℕ, i % 6 ≠ 2 ∧ a i = (Nat.fib (j + 1) : ℤ) :=
        ⟨6 * (j / 3) + r, by omega, (h _ _ hr).trans hv⟩
      rcases (show j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 by omega) with ht | ht | ht
      · apply witness 1 (by decide) (by decide)
        exact congrArg (fun t : ℕ => (Nat.fib t : ℤ)) (by omega : 3 * (j / 3) + 1 = j + 1)
      · apply witness 0 (by decide) (by decide)
        exact congrArg (fun t : ℕ => (Nat.fib t : ℤ)) (by omega : 3 * (j / 3) + 2 = j + 1)
      · apply witness 4 (by decide) (by decide)
        exact congrArg (fun t : ℕ => (Nat.fib t : ℤ)) (by omega : 3 * (j / 3) + 3 = j + 1)
  have hrange : Set.range (fun n : ℕ => (Nat.fib n : ℤ)) =
      {x : ℤ | ∃ n : ℕ, n % 6 ≠ 2 ∧ a n = x} := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact realizes j
    · rintro ⟨i, hi, rfl⟩
      exact member i hi
  refine ⟨?_, hrange, fun n => h n 2 (by decide)⟩
  rw [hrange]
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, rfl, (regular i).mp hi⟩
  · rintro ⟨i, rfl, hi⟩
    exact ⟨i, (regular i).mpr hi, rfl⟩

end OMA.A107363

theorem OMA.solution : type_of% @OMA.S_oeis_a107363.main := OMA.A107363.finish OMA.A107363.columns
