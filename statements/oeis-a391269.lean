import Mathlib

/-!
# A391269: a(n) is the number of iterations of x-> gpf(2*x+1) starting at n until the value 3 is reached; a(n)=-1 if 3 is not reached.

Source: https://oeis.org/A391269
Credit: @luciusacarr

Data: 1, 7, 0, 1, 6, 2, 7, 9, 3, 8, 5, 7, 1, 11, 9, 6, 8, 8, 2, ... (offset 1).

Conjecture (from the entry): a(n) is never equal to -1. `main` states it.

Reading of the source:
* `gpf(m)` is the greatest prime factor of `m`, here the largest element of `Nat.primeFactors m`
  (for `m = 2x + 1 ≥ 3` this set is nonempty; the value at `m = 1` is never used).
* a(n) is never -1 means every positive integer `n` reaches 3: some iterate `g^[k] n` (k ≥ 0) of
  `g(x) = gpf(2x + 1)` equals 3 (k = 0 for n = 3, matching a(3) = 0). The first 19 data values
  were recomputed from this map.
-/

namespace OMA.S_oeis_a391269

/-- The greatest prime factor of `m` (0 if `m` has none). -/
def gpf (m : ℕ) : ℕ := (Nat.primeFactors m).sup id

/-- The map `x ↦ gpf(2x + 1)`. -/
def g (x : ℕ) : ℕ := gpf (2 * x + 1)

theorem main :
    -- Every positive integer reaches 3 under iteration of g.
    ∀ n : ℕ, 0 < n → ∃ k : ℕ, g^[k] n = 3 := by
  sorry

end OMA.S_oeis_a391269
