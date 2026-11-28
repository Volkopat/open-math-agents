import Mathlib

/-!
# A088054: Factorial primes: primes which are within 1 of a factorial number

Source: https://oeis.org/A088054
Credit: @sntntHb

Conjecture (in the comments of A088054): 3 is the intersection of A002981 and A002982.

Here A002981 lists the numbers `n` such that `n! + 1` is prime, and A002982 lists the numbers
`n` such that `n! - 1` is prime. The conjecture says that `n = 3` (with the twin primes
`5 = 3! - 1` and `7 = 3! + 1`) is the only `n` for which both `n! - 1` and `n! + 1` are prime.

Conventions:
* `n` ranges over the natural numbers; for `n ≤ 2` the number `n! - 1` is `0` or `1` (natural
  number subtraction), which is not prime, so no small case is lost or added.
-/

namespace OMA.S_oeis_a088054

/-- If `n! - 1` and `n! + 1` are both prime, then `n = 3`. -/
theorem main : ∀ n : ℕ, (n.factorial - 1).Prime → (n.factorial + 1).Prime → n = 3 := by
  sorry

end OMA.S_oeis_a088054
