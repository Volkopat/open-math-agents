import Mathlib

/-!
# A290639: a(n) = largest number <= prime(n) such that 1 + a(1)*a(2)*...*a(n) is prime.

Source: https://oeis.org/A290639
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A290639 (Thomas Ordowski, Aug 08 2017): a(n) > 1 for every n.

Conventions:
* The sequence has offset 1 (data 2, 3, 5, 7, 11, 11, 16, 15, 21, 22, 30, 36, ...).
* The recursion is carried by `aux n = (a(n), a(1)*a(2)*...*a(n))` for n >= 1, with the
  dummy value `aux 0 = (0, 1)` (empty product 1; the first component at 0 is not used).
  Then a(n+1) is the largest natural number k <= prime(n+1) such that
  1 + a(1)*...*a(n)*k is prime.
* prime(n+1) is `Nat.nth Nat.Prime n` (0-indexed, `Nat.nth Nat.Prime 0 = 2`).
* The largest element is `sSup` of a bounded set of natural numbers. If no such k existed the
  term would be undefined in the entry; here `sSup` of the empty set is 0, so the statement
  a(n) > 1 also contains the existence of every term.
* The conjecture is stated for every n >= 1 (the offset).
-/

namespace OMA.S_oeis_a290639

/-- `aux n = (a(n), a(1)*...*a(n))` for n >= 1; `aux 0 = (0, 1)` is a dummy start. -/
noncomputable def aux : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | (n + 1) =>
    (sSup {k : ℕ | k ≤ Nat.nth Nat.Prime n ∧ (1 + (aux n).2 * k).Prime},
      (aux n).2 * sSup {k : ℕ | k ≤ Nat.nth Nat.Prime n ∧ (1 + (aux n).2 * k).Prime})

/-- A290639: a(n) = largest number <= prime(n) such that 1 + a(1)*...*a(n) is prime. -/
noncomputable def a (n : ℕ) : ℕ := (aux n).1

/-- The conjecture: a(n) > 1 for every n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → 1 < a n := by
  sorry

end OMA.S_oeis_a290639
