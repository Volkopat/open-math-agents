import Mathlib

/-!
# A123365: Values of k such that A046530(k) = (k+2)/3, where A046530(k) is the number of distinct residues of cubes mod k.

Source: https://oeis.org/A123365
Credit: @divmxnd0x

Conjecture (stated in A123365): with the exception of the first term `a(1) = 1`, this is exactly
the sequence of primes of the form `6k + 1` (A002476).

Formalization notes:
* `cubes k` is the number of distinct values of `x^3` in `ZMod k` (A046530), for `k ≥ 1`;
  `A046530(k) = (k + 2)/3` is written `3 · A046530(k) = k + 2` (so that `(k + 2)/3` is an integer).
* The conjecture: the `k ≥ 1` with this property are exactly `1` and the primes `p ≡ 1 (mod 6)`.
-/

namespace OMA.S_oeis_a123365

/-- A046530(k): the number of distinct cubes in `ZMod k`, for `k ≥ 1`. -/
noncomputable def cubes (k : ℕ) : ℕ := Nat.card (Set.range fun x : ZMod k => x ^ 3)

/-- The terms of A123365 are exactly `1` and the primes `≡ 1 (mod 6)`. -/
theorem main : {k : ℕ | 1 ≤ k ∧ 3 * cubes k = k + 2} = {1} ∪ {p : ℕ | p.Prime ∧ p % 6 = 1} := by
  sorry

end OMA.S_oeis_a123365
