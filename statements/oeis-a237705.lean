import Mathlib

/-!
# A237705: Number of primes p < n with pi(n-p) prime, where pi(.) is given by A000720.

Source: https://oeis.org/A237705
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A237705 (Zhi-Wei Sun, Feb 11 2014), part (i): a(n) > 0
for all n > 4, and a(n) = 1 only for n = 5, 12, 26, 27, 32, 68.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 1, 2, 2, 3, 2, 2, 2, 1, ...). `a n` is the number of
  primes p < n with pi(n-p) prime, exactly as in the OEIS name.
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a237705

/-- The condition in the name of A237705 on a tuple, for a given n. -/
def P (n : ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ p < n ∧ (Nat.primeCounting (n - p)).Prime

/-- A237705: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A237705. -/
theorem main : ∀ n : ℕ, 0 < n → ((4 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({5, 12, 26, 27, 32, 68} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a237705
