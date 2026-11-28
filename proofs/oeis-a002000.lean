import OMAStatements.S_oeis_a002000
import Mathlib

/-!
# Proof for OEIS A002000: a(n+1) == a(n) (mod 3^(n+r+2)) for n >= r

Here `a(0) = 7` and `a(n+1) = a(n)*(a(n)^2 - 3)`. Put `d(n) = a(n)^2 - 4`.

1. `a(n+1) - a(n) = a(n) * d(n)`.
2. `d(n+1) = d(n) * (a(n)^2 - 1)^2`, because `x*(x-3)^2 - 4 = (x-4)*(x-1)^2` with `x = a(n)^2`.
3. `3^(2n+2)` divides `d(n)`: `d(0) = 45 = 9 * 5`, and if `3` divides `d(n)` then `3` divides
   `a(n)^2 - 1 = d(n) + 3`, so `9` divides `(a(n)^2 - 1)^2` and step 2 adds two powers of `3`.
4. For `r <= n` the exponent `n + r + 2` is at most `2n + 2`, so `3^(n+r+2)` divides
   `a(n) * d(n) = a(n+1) - a(n)`.

The proof uses only the recurrence; the Lucas number formula of the entry is not needed.
-/

namespace A002000Proof

open OMA.S_oeis_a002000

/-- The recurrence of the name line. -/
private lemma a_succ (n : ℕ) : a (n + 1) = a n * (a n ^ 2 - 3) := rfl

/-- Step 1: `a(n+1) - a(n) = a(n) * (a(n)^2 - 4)`. -/
private lemma diff_eq (n : ℕ) : a (n + 1) - a n = a n * (a n ^ 2 - 4) := by
  rw [a_succ]
  ring

/-- Step 2: `a(n+1)^2 - 4 = (a(n)^2 - 4) * (a(n)^2 - 1)^2`. -/
private lemma d_succ (n : ℕ) :
    a (n + 1) ^ 2 - 4 = (a n ^ 2 - 4) * (a n ^ 2 - 1) ^ 2 := by
  rw [a_succ]
  ring

/-- Step 3: `3^(2n+2)` divides `a(n)^2 - 4`. -/
private lemma three_pow_dvd (n : ℕ) : (3 : ℤ) ^ (2 * n + 2) ∣ a n ^ 2 - 4 := by
  induction n with
  | zero =>
    have h0 : a 0 = 7 := rfl
    refine ⟨5, ?_⟩
    rw [h0]
    norm_num
  | succ k ih =>
    have h1 : (3 : ℤ) ∣ a k ^ 2 - 4 :=
      (dvd_pow_self (3 : ℤ) (by omega)).trans ih
    have h3 : (3 : ℤ) ∣ a k ^ 2 - 1 := by
      have e : a k ^ 2 - 1 = (a k ^ 2 - 4) + 3 := by ring
      rw [e]
      exact dvd_add h1 (dvd_refl 3)
    have h9 : (3 : ℤ) ^ 2 ∣ (a k ^ 2 - 1) ^ 2 := pow_dvd_pow_of_dvd h3 2
    have e : (3 : ℤ) ^ (2 * (k + 1) + 2) = 3 ^ (2 * k + 2) * 3 ^ 2 := by ring
    rw [d_succ, e]
    exact mul_dvd_mul ih h9

/-- Step 4: the divisibility form of the conjecture. -/
private lemma key (n r : ℕ) (hr : r ≤ n) : (3 : ℤ) ^ (n + r + 2) ∣ a (n + 1) - a n := by
  have h1 : (3 : ℤ) ^ (n + r + 2) ∣ (3 : ℤ) ^ (2 * n + 2) := pow_dvd_pow 3 (by omega)
  rw [diff_eq]
  exact Dvd.dvd.mul_left (h1.trans (three_pow_dvd n)) (a n)

end A002000Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a002000.main := by
  intro n r hr
  exact (Int.modEq_iff_dvd.mpr (A002000Proof.key n r hr)).symm
