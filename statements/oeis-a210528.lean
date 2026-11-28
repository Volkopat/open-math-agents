import Mathlib

/-!
# A210528: Number of ways to write 2n = p+q (p<=q) with p, q and p^6+q^6 all practical.

Source: https://oeis.org/A210528
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A210528 (Zhi-Wei Sun, Jan 27 2013): a(n)>0 for all n>0.

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 4, ...). `a n` is the number of
  pairs (p, q) with 2n = p + q, p <= q, and p, q and p^6 + q^6 all practical, exactly as in the
  OEIS name.
* A positive integer m is practical (A005153) if every natural number k <= sigma(m) is a sum of
  distinct divisors of m; this is the helper `Practical`, where sigma(m) is the sum over
  `Nat.divisors m` and a sum of distinct divisors is the sum over a subset of `Nat.divisors m`. 0
  is not practical.
* Only the first sentence of the conjecture is formalized; the `Moreover` sentence (about p^(3m) +
  q^(3m)) is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a210528

/-- m is a practical number (A005153): m > 0 and every k <= sigma(m) is a sum of distinct
divisors of m. -/
def Practical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k : ℕ, k ≤ ∑ d ∈ m.divisors, d → ∃ s : Finset ℕ, s ⊆ m.divisors ∧ ∑ d ∈ s, d = k

/-- The condition in the name of A210528 on a tuple, for a given n. -/
def P (n : ℕ) (p q : ℕ) : Prop :=
  p + q = 2 * n ∧ p ≤ q ∧ Practical p ∧ Practical q ∧ Practical (p ^ 6 + q ^ 6)

/-- A210528: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A210528. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a210528
