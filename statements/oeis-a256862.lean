import Mathlib

/-!
# A256862: a(1)=1, then a(n) = least number > a(n-1) such that 2*a(n-1)+a(n) is prime.

Source: https://oeis.org/A256862
Credit: @eltociear

Let `next x` be the least `y > x` such that `2x + y` is prime. A256862 is the orbit of `1` under
`next`: `1, 3, 5, 7, 9, 11, 15, ...` (so `a(n) = next^[n-1] 1`). The entry conjectures:

  any initial term a(1) eventually merges with this sequence,

that is, the sequence built by the same rule from any other start `s` eventually reaches a term
of A256862. `main` states this for every positive integer start `s ≥ 1`: some iterate of `next`
from `s` equals some term of A256862. After the first common value the two sequences agree,
since each term determines the next one.

`next x` is well defined because there are infinitely many primes, so some prime `p > 3x` exists
and `y = p - 2x` works.
-/

namespace OMA.S_oeis_a256862

/-- The least `y > x` with `2 * x + y` prime. -/
noncomputable def next (x : ℕ) : ℕ := sInf {y : ℕ | x < y ∧ (2 * x + y).Prime}

/-- The conjecture in OEIS A256862: from any start `s ≥ 1`, the sequence built by `next`
eventually meets A256862 (the orbit of `1`). -/
theorem main : ∀ s : ℕ, 1 ≤ s → ∃ i j : ℕ, next^[i] s = next^[j] 1 := by
  sorry

end OMA.S_oeis_a256862
-- ci: re-run check-proof
