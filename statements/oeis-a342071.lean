import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Bounds.Defs

/-!
# OEIS A342071

The conjecture says that 3977, the 194th term, is the final value of k for
which [3k + 1, 4k] contains more primes than [2k + 1, 3k].
Source: https://oeis.org/A342071
-/

namespace OMA.S_oeis_a342071

def primesIn (lower upper : ℕ) : ℕ :=
  ((Finset.Icc lower upper).filter Nat.Prime).card

theorem main :
    IsGreatest {k : ℕ | primesIn (2 * k + 1) (3 * k) < primesIn (3 * k + 1) (4 * k)} 3977 := by
  sorry

end OMA.S_oeis_a342071
