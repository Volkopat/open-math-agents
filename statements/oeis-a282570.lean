import Mathlib

/-!
# A282570: Number of ways to write n as an ordered sum of two multiplicatively perfect numbers (A007422).

Source: https://oeis.org/A282570
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A282570 (Ilya Gutkovskiy, Feb 18 2017): a(n) > 0 for
all n > 51.

Conventions:
* The sequence has offset 0 (data 0, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 2, ...). `a n` is the number of
  ordered pairs (i, j) of multiplicatively perfect numbers (A007422) with n = i + j, exactly as in
  the OEIS name.
* A positive integer k is multiplicatively perfect (A007422: 1, 6, 8, 10, 14, 15, ...) when the
  product of its divisors equals k^2; this is the helper `MP`, with the product taken over
  `Nat.divisors k`. 1 is multiplicatively perfect, as in the OEIS example a(16) = 5 (which uses 15
  + 1 and 1 + 15).
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a282570

/-- k is multiplicatively perfect (A007422): k > 0 and the product of the divisors of k is k^2. -/
def MP (k : ℕ) : Prop := 0 < k ∧ ∏ d ∈ k.divisors, d = k ^ 2

/-- The condition in the name of A282570 on a tuple, for a given n. -/
def P (n : ℕ) (i j : ℕ) : Prop :=
  i + j = n ∧ MP i ∧ MP j

/-- A282570: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A282570. -/
theorem main : ∀ n : ℕ, 51 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a282570
