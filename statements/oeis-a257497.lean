import Mathlib

/-!
# A257497: Number of ordered ways to write n as the sum of a term of A257121 and a positive generalized pentagonal number.

Source: https://oeis.org/A257497
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A257497 (Zhi-Wei Sun, Apr 26 2015): a(n) > 0 for all n
> 0, and a(n) = 1 only for n = 1, 54, 84, 87, 109, 174, 252, 344, 1234, 1439, 2924.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 2, 3, 2, 3, 3, 3, 2, 2, 2, ...). `a n` is the number of
  pairs (m, z) with m a term of A257121, z a nonzero integer and n = m + z*(3z-1)/2, i.e. the
  number of ordered ways to write n as the sum of a term of A257121 and a positive generalized
  pentagonal number, as in the OEIS name.
* A257121 is the set of natural numbers m (0 included) such that 9*m + 3*r - 1 and 9*m + 3*r + 1
  are twin primes for some r = 0, 1, 2; this is the helper `T`. For r = 0 and m = 0 the truncated
  value 9*0 + 3*0 - 1 = 0 is not prime, in agreement with -1 not being prime.
* The positive generalized pentagonal numbers are z*(3z-1)/2 with z a nonzero integer (1, 2, 5, 7,
  12, ...); distinct z give distinct values, so counting (m, z) counts the ordered ways. The
  equation is stated in `ℤ` with m and n cast, and the integer division by 2 is exact.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a257497

/-- m is a term of A257121: 9m+3r-1 and 9m+3r+1 are twin primes for some r = 0, 1, 2. -/
def T (m : ℕ) : Prop :=
  ∃ r : ℕ, r ≤ 2 ∧ (9 * m + 3 * r - 1).Prime ∧ (9 * m + 3 * r + 1).Prime

/-- The condition in the name of A257497 on a tuple, for a given n. -/
def P (n : ℕ) (m : ℕ) (z : ℤ) : Prop :=
  T m ∧ z ≠ 0 ∧ (m : ℤ) + z * (3 * z - 1) / 2 = n

/-- A257497: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℤ | P n t.1 t.2}

/-- The conjecture recorded in A257497. -/
theorem main : ∀ n : ℕ, 0 < n → ((0 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({1, 54, 84, 87, 109, 174, 252, 344, 1234, 1439, 2924} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a257497
