import Mathlib

/-!
# A237815: Number of primes p < n such that the number of Sophie Germain primes among 1, ..., n-p is a Sophie Germain prime.

Source: https://oeis.org/A237815
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A237815 (Zhi-Wei Sun, Feb 13 2014), part (i): a(n) > 0
for all n > 4.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 1, 2, 2, 3, 3, 4, 4, 4, ...). `a n` is the number of
  primes p < n such that the number of Sophie Germain primes among 1, ..., n-p is a Sophie Germain
  prime, exactly as in the OEIS name.
* A Sophie Germain prime is a prime q such that 2*q + 1 is also prime. The helper `sg x` is the
  number of Sophie Germain primes among 1, ..., x (a finite set, counted with `Set.ncard`).
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a237815

/-- The number of Sophie Germain primes (primes q with 2*q + 1 prime) among 1, ..., x. -/
noncomputable def sg (x : ℕ) : ℕ := Set.ncard {q : ℕ | q ≤ x ∧ q.Prime ∧ (2 * q + 1).Prime}

/-- The condition in the name of A237815 on a tuple, for a given n. -/
def P (n : ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ p < n ∧ (sg (n - p)).Prime ∧ (2 * sg (n - p) + 1).Prime

/-- A237815: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A237815. -/
theorem main : ∀ n : ℕ, 4 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a237815
