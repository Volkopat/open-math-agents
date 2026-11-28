import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Bounds.Defs

/-!
# OEIS A342070

The conjecture says that 1323 is the last value of k for which the interval
[2k + 1, 3k] contains more primes than [k + 1, 2k].
Source: https://oeis.org/A342070
-/

namespace OMA.S_oeis_a342070

def primesIn (lower upper : ℕ) : ℕ :=
  ((Finset.Icc lower upper).filter Nat.Prime).card

theorem main :
    IsGreatest {k : ℕ | primesIn (k + 1) (2 * k) < primesIn (2 * k + 1) (3 * k)} 1323 := by
  sorry

end OMA.S_oeis_a342070
