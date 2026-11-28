import Mathlib

/-!
# A136032: Number of prime factors (with multiplicity) of Mersenne composites (A065341)

Source: https://oeis.org/A136032
Credit: @sobrien032

A065341 lists the Mersenne composites, the numbers `2^p - 1` with `p` prime that are not prime,
in increasing order (offset 1): 2047, 8388607, 536870911, ... A136032(n) is the number of prime
factors of A065341(n) counted with multiplicity, and A135975(n) is the number of distinct prime
factors of A065341(n) (both offset 1).

The entry's comment (Felix Fröhlich, Aug 24 2014): "If the conjecture that all Mersenne
composites are squarefree is true, then this sequence is identical to A135975."

`A065341 n` below is `Nat.nth` of the set of Mersenne composites at index `n - 1`. Whether that
set is infinite is not known; if it were finite, `Nat.nth` would give 0 beyond its last element,
and both counts of 0 are 0, so the statement is about the actual terms either way.
-/

namespace OMA.S_oeis_a136032

/-- `m` is a Mersenne composite: `m = 2^p - 1` for a prime `p`, and `m` is not prime. -/
def IsMersenneComposite (m : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ m = 2 ^ p - 1 ∧ ¬ m.Prime

/-- A065341(n): the `n`-th Mersenne composite, `n ≥ 1`. -/
noncomputable def A065341 (n : ℕ) : ℕ := Nat.nth IsMersenneComposite (n - 1)

/-- A136032(n): the number of prime factors of A065341(n), with multiplicity. -/
noncomputable def a (n : ℕ) : ℕ := ArithmeticFunction.cardFactors (A065341 n)

/-- A135975(n): the number of distinct prime factors of A065341(n). -/
noncomputable def A135975 (n : ℕ) : ℕ := ArithmeticFunction.cardDistinctFactors (A065341 n)

/-- If every Mersenne composite is squarefree, then A136032(n) = A135975(n) for all `n ≥ 1`. -/
theorem main : (∀ m : ℕ, IsMersenneComposite m → Squarefree m) →
    ∀ n : ℕ, 1 ≤ n → a n = A135975 n := by
  sorry

end OMA.S_oeis_a136032
