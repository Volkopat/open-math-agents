import Mathlib

/-!
# A339991: The number of steps that n requires to reach 1 under the map: m -> m/2 if m is even, m-> m^2 - 1 if m is an odd prime, otherwise m -> m - 1. a(n) = -1 if 1 is never reached.

Source: https://oeis.org/A339991
Credit: @luciusacarr

Data: 0, 1, 4, 2, 8, 5, 9, 3, 4, 9, 15, 6, 15, 10, 11, 4, 10, 5, 22, 10, ... (offset 1).

Conjecture (from the entry): a(n) is never equal to -1. `main` states it.

Reading of the source:
* The map is `f(m) = m/2` for even `m`, `m^2 - 1` for odd primes `m`, and `m - 1` otherwise
  (odd non-primes).
* a(n) is never -1 means every positive integer `n` reaches 1: some iterate `f^[k] n` (k ≥ 0)
  equals 1 (k = 0 for n = 1, matching a(1) = 0). The first 29 data values were recomputed from
  this map.
-/

namespace OMA.S_oeis_a339991

/-- The map of A339991. -/
def f (m : ℕ) : ℕ :=
  if Even m then m / 2 else if m.Prime then m ^ 2 - 1 else m - 1

theorem main :
    -- Every positive integer reaches 1 under iteration of f.
    ∀ n : ℕ, 0 < n → ∃ k : ℕ, f^[k] n = 1 := by
  sorry

end OMA.S_oeis_a339991
