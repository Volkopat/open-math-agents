import Mathlib

/-!
# OEIS A377000: linear recurrences for the rows (Conjecture 2)

Source: https://oeis.org/A377000 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry, offset 2: Array read by ascending antidiagonals: T(n,k) = number of n-esthetic numbers
with k digits (n >= 2, k >= 1). Rows: T(6,k) = 5, 9, 16, 29, 52, 94, ...;
T(7,k) = 6, 11, 20, 37, 68, 126, ...; T(9,k) = 8, 15, 28, 53, 100, 190, ...
Formula section: Conjectures from Chai Wah Wu, Oct 21 2024: ... Conjecture 2: For each n, the
row T(n,k) satisfies a linear recurrence. For example:
T(6,k) = T(6,k-1) + 2*T(6,k-2) - T(6,k-3) for k > 3.
T(7,k) = 4*T(7,k-2) - 2*T(7,k-4) for k > 4.
T(8,k) = T(8,k-1) + 3*T(8,k-2) - 2*T(8,k-3) - T(8,k-4) for k > 4.
T(9,k) = 5*T(9,k-2) - 5*T(9,k-4) for k > 4.
T(10,k) = T(10,k-1) + 4*T(10,k-2) - 3*T(10,k-3) - 3*T(10,k-4) + T(10,k-5) for k > 5.
T(11,k) = 6*T(11,k-2) - 9*T(11,k-4) + 2*T(11,k-6) for k > 6.
T(12,k) = T(12,k-1) + 5*T(12,k-2) - 4*T(12,k-3) - 6*T(12,k-4) + 3*T(12,k-5) + T(12,k-6)
for k > 6.

Formalization notes:
* An n-esthetic number is a positive integer whose base n digits differ by exactly 1 between
  any two adjacent digits. A k-digit base n number is a digit string `x : Fin k → Fin n`,
  `x 0` being the leading digit, which must be nonzero; distinct strings give distinct numbers.
  So `T n k` counts the strings `x : Fin k → Fin n` with nonzero leading digit and adjacent
  digits differing by 1.
* This reading reproduces all 78 data terms of the entry (rows n = 2..12).
* Conjecture 2 is stated as: for each n >= 2 there are an order `d` and integer coefficients
  `c 0, ..., c (d - 1)` with `T(n, k + d) = Sum_(i < d) c i * T(n, k + i)` for all k >= 1,
  together with the seven listed recurrences, each for the listed range of k, in the integers.
* Conjectures 1 and 3 of the same comment are not part of this statement.
-/

namespace OMA.S_oeis_a377000

/-- A digit string `x : Fin k → Fin n` (leading digit `x 0`) is the base `n` representation of
an n-esthetic number: the leading digit is nonzero and adjacent digits differ by 1. -/
def IsEsthetic {n k : ℕ} (x : Fin k → Fin n) : Prop :=
  (∀ h : 0 < k, (x ⟨0, h⟩ : ℕ) ≠ 0) ∧
    ∀ (i : Fin k) (h : (i : ℕ) + 1 < k),
      (x i : ℕ) + 1 = x ⟨(i : ℕ) + 1, h⟩ ∨ (x ⟨(i : ℕ) + 1, h⟩ : ℕ) + 1 = x i

instance {n k : ℕ} (x : Fin k → Fin n) : Decidable (IsEsthetic x) := by
  unfold IsEsthetic; infer_instance

/-- A377000: `T n k` is the number of n-esthetic numbers with k digits. -/
def T (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin k → Fin n => IsEsthetic x).card

/-- Conjecture 2 of Chai Wah Wu for A377000: every row satisfies a linear recurrence, and the
seven listed recurrences hold for rows 6 to 12. -/
theorem main :
    (∀ n : ℕ, 2 ≤ n → ∃ d : ℕ, ∃ c : ℕ → ℤ, ∀ k : ℕ, 1 ≤ k →
      (T n (k + d) : ℤ) = ∑ i ∈ Finset.range d, c i * T n (k + i)) ∧
    (∀ k : ℕ, 3 < k → (T 6 k : ℤ) = T 6 (k - 1) + 2 * T 6 (k - 2) - T 6 (k - 3)) ∧
    (∀ k : ℕ, 4 < k → (T 7 k : ℤ) = 4 * T 7 (k - 2) - 2 * T 7 (k - 4)) ∧
    (∀ k : ℕ, 4 < k →
      (T 8 k : ℤ) = T 8 (k - 1) + 3 * T 8 (k - 2) - 2 * T 8 (k - 3) - T 8 (k - 4)) ∧
    (∀ k : ℕ, 4 < k → (T 9 k : ℤ) = 5 * T 9 (k - 2) - 5 * T 9 (k - 4)) ∧
    (∀ k : ℕ, 5 < k → (T 10 k : ℤ) = T 10 (k - 1) + 4 * T 10 (k - 2) - 3 * T 10 (k - 3) -
      3 * T 10 (k - 4) + T 10 (k - 5)) ∧
    (∀ k : ℕ, 6 < k → (T 11 k : ℤ) = 6 * T 11 (k - 2) - 9 * T 11 (k - 4) + 2 * T 11 (k - 6)) ∧
    (∀ k : ℕ, 6 < k → (T 12 k : ℤ) = T 12 (k - 1) + 5 * T 12 (k - 2) - 4 * T 12 (k - 3) -
      6 * T 12 (k - 4) + 3 * T 12 (k - 5) + T 12 (k - 6)) := by
  sorry

end OMA.S_oeis_a377000
