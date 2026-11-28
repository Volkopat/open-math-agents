import Mathlib

/-!
# A333820: a(n) is the number of pairs (q,r) such that q <= r and phi(q) + phi(r) = 2*n.

Source: https://oeis.org/A333820
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A333820: Paul Erdős and Leo Moser conjectured that,
for any even numbers 2*n, there exist integers q and r such that phi(q) + phi(r) = 2*n.
Therefore, they conjecture a(n) > 0 for all n.

Conventions:
* The sequence has offset 1 (data 3, 6, 12, 22, 31, 36, ...), so the conjecture is stated for
  all n >= 1.
* phi is the Euler totient `Nat.totient`. The pairs (q, r) are pairs of positive integers with
  q <= r (a(1) = 3 counts (1,1), (1,2), (2,2)); positivity of q is required explicitly because
  Mathlib sets `Nat.totient 0 = 0`.
* The set of such pairs is finite for every n (phi takes each value only finitely often), so
  `Set.ncard` is its number of elements, and a(n) > 0 says exactly that such a pair exists.
-/

namespace OMA.S_oeis_a333820

/-- A333820: number of pairs (q, r) of positive integers with q <= r and
phi(q) + phi(r) = 2n. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ | 0 < x.1 ∧ x.1 ≤ x.2 ∧ Nat.totient x.1 + Nat.totient x.2 = 2 * n}

/-- The Erdős-Moser conjecture as recorded in A333820: a(n) > 0 for all n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a333820
