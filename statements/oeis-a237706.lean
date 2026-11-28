import Mathlib

/-!
# A237706: Number of primes p < n with pi(n-p) a square, where pi(.) is given by A000720.

Source: https://oeis.org/A237706
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A237706 (Zhi-Wei Sun, Feb 11 2014), part (i): a(n) > 0
for all n > 2, and a(n) = 1 only for n = 3, 5, 6, 7, 8, 16, 17, 22, 23, 148, 149.

Conventions:
* The sequence has offset 1 (data 0, 0, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, ...). `a n` is the number of
  primes p < n with pi(n-p) a square, exactly as in the OEIS name.
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x.
* `a square` is the Mathlib predicate `IsSquare` on natural numbers; 0 counts as a square (the
  data needs this: a(3) = 1 comes from p = 2, pi(1) = 0).
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a237706

/-- The condition in the name of A237706 on a tuple, for a given n. -/
def P (n : ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ p < n ∧ IsSquare (Nat.primeCounting (n - p))

/-- A237706: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A237706. -/
theorem main : ∀ n : ℕ, 0 < n → ((2 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({3, 5, 6, 7, 8, 16, 17, 22, 23, 148, 149} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a237706
