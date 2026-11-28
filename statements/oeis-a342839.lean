import Mathlib

/-!
# The last term of OEIS A342839

Source: https://oeis.org/A342839
Credit: @HBreitkreutz
-/

namespace OMA.S_oeis_a342839

/-- The positive integers `k` for which `(4k, 5k]` contains more primes than `(3k, 4k]`. -/
def terms : Set ℕ :=
  {k | 0 < k ∧ Nat.primeCounting (4 * k) - Nat.primeCounting (3 * k) <
    Nat.primeCounting (5 * k) - Nat.primeCounting (4 * k)}

/-- Jon E. Schoenfield conjectured that the 876th term, 11895, is the last. -/
theorem main : IsGreatest terms 11895 ∧ terms.ncard = 876 := by
  sorry

end OMA.S_oeis_a342839
