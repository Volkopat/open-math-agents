import Mathlib

/-!
# A392329: a(n) is the number of iterations x->gpf(6*x+1) starting at n until the value 13 or 47 is reached; a(n) = -1 if neither of these two values is reached.

Source: https://oeis.org/A392329
Credit: @luciusacarr

Data: 8, 1, 18, 7, 6, 6, 7, 8, 8, 12, 7, 8, 0, 5, 1, 11, 4, 14, 17, ... (offset 1).

Conjecture (from the entry): a(n) is never equal to -1. `main` states it.

Reading of the source:
* `gpf(m)` is the greatest prime factor of `m`, here the largest element of `Nat.primeFactors m`
  (for `m = 6x + 1 ≥ 7` this set is nonempty; the value at `m = 1` is never used).
* a(n) is never -1 means every positive integer `n` reaches 13 or 47: some iterate `g^[k] n`
  (k ≥ 0) of `g(x) = gpf(6x + 1)` equals 13 or 47 (k = 0 for n = 13 and n = 47). The first 19
  data values were recomputed from this map.
-/

namespace OMA.S_oeis_a392329

/-- The greatest prime factor of `m` (0 if `m` has none). -/
def gpf (m : ℕ) : ℕ := (Nat.primeFactors m).sup id

/-- The map `x ↦ gpf(6x + 1)`. -/
def g (x : ℕ) : ℕ := gpf (6 * x + 1)

theorem main :
    -- Every positive integer reaches 13 or 47 under iteration of g.
    ∀ n : ℕ, 0 < n → ∃ k : ℕ, g^[k] n = 13 ∨ g^[k] n = 47 := by
  sorry

end OMA.S_oeis_a392329
