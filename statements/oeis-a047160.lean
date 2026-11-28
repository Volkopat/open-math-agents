import Mathlib

/-!
# A047160: least `m ≥ 0` such that `n-m` and `n+m` are both prime, or `-1` if none exists.

Source: https://oeis.org/A047160
Credit: @cjchaffin

Conjecture (equivalent to Goldbach's conjecture, as recorded on the page): for all
`n ≥ 2` there are primes `p` and `q` equidistant from `n`, so `a(n)` is never `-1`.

Conventions: offset 2; `m` is a natural number (so `m ≤ n` is implicit in `n-m` being
prime). The conjecture is formalized as existence of some such `m`, not the least-`m`
part of the name.
-/

namespace OMA.S_oeis_a047160

theorem main : ∀ n : ℕ, 2 ≤ n →
    ∃ m : ℕ, m ≤ n ∧ (n - m).Prime ∧ (n + m).Prime := by
  sorry

end OMA.S_oeis_a047160
