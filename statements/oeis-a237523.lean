import Mathlib

/-!
# A237523: a(n) = |{0 < k < n/2: phi(k*(n-k)) + 1 is a square}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A237523
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 7, and a(n) = 1 only for n = 8, 9, 13, 15, 20, 132.
(ii) If n > 5 is not among 10, 15, 20, 60, 105, then phi(k*(n-k)) is a square for some 0 < k < n/2.

Formalization notes:
* phi = `Nat.totient`, sigma = `ArithmeticFunction.sigma 1`, prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2). "x is a square" is `IsSquare x`.
* "k < n/2" is stated as 2k < n. "a(n) = 1 only for n in S" is stated as: a(n) = 1 iff n ∈ S.
* Controls (computed): a(1..30) = 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 4, 4, 1, 3, 3, 3,
  2, 4, 4, 4, 2, 4, 5, as in the entry; for n < 300, a(n) = 1 exactly at 8, 9, 13, 15, 20, 132, and
  both parts hold.
-/

namespace OMA.S_oeis_a237523


/-- A237523(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter fun k => 2 * k < n ∧ IsSquare (Nat.totient (k * (n - k)) + 1)).card

/-- The conjecture of the entry (all parts listed above). -/
theorem main :
    (∀ n : ℕ, 7 < n → 0 < a n) ∧
      (∀ n : ℕ, a n = 1 ↔ n = 8 ∨ n = 9 ∨ n = 13 ∨ n = 15 ∨ n = 20 ∨ n = 132) ∧
      ∀ n : ℕ, 5 < n → n ≠ 10 → n ≠ 15 → n ≠ 20 → n ≠ 60 → n ≠ 105 →
        ∃ k, 0 < k ∧ 2 * k < n ∧ IsSquare (Nat.totient (k * (n - k))) := by
  sorry

end OMA.S_oeis_a237523
