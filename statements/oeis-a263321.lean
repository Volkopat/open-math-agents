import Mathlib

/-!
# A263321: Least positive integer m such that the numbers phi(k)*pi(k^2) (k = 1..n) are pairwise incongruent modulo m.

Source: https://oeis.org/A263321
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) <= n^2 for all n > 0, and the only even term is a(7) = 16.

Formalization notes:
* phi = `Nat.totient`, pi = `Nat.primeCounting`. a(n) is the least m > 0 for which k ↦ phi(k) pi(k^2)
  mod m is injective on {1, ..., n} (such m exists, e.g. any m larger than all the values).
* Controls (computed): a(1..21) = 1, 3, 5, 7, 11, 13, 16, 19, 19, 19, 29, 29, 29, 37, 37, 59, 59, 59, 59,
  59, 59, as in the entry; for n < 60, a(n) ≤ n^2 and a(n) is even only at n = 7.
-/

namespace OMA.S_oeis_a263321

/-- A263321(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ Set.InjOn (fun k => Nat.totient k * Nat.primeCounting (k ^ 2) % m)
    (Finset.Icc 1 n : Set ℕ)}

/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 0 < n → a n ≤ n ^ 2 ∧ (Even (a n) ↔ n = 7) := by
  sorry

end OMA.S_oeis_a263321
