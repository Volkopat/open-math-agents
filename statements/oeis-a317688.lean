import Mathlib

/-!
# A317688: Absolute primes that are not repunits: primes where the number resulting from any permutation of the digits is also prime, excluding repunit primes.

Source: https://oeis.org/A317688
Credit: @keiichisince1986-bot

A317688 is the sequence `a(n)` named in the title. The entry states:
Conjecture: The sequence is finite, with 991 being the last term.

Conventions:
- `IsAbsolutePrime n`: every permutation of the decimal digit list of `n` gives a prime (read with
  `Nat.ofDigits 10`). A number with a digit `0` is never an absolute prime under any reading of leading
  zeros, since the permutation that puts `0` in the units place gives a multiple of `10`.
- `IsRepunit n`: all decimal digits of `n` are `1`. The data includes the one-digit primes `2, 3, 5, 7`.
- The sequence is finite with last term `991` exactly when `991` is the greatest element of the set:
  `IsGreatest S 991`.
-/

namespace OMA.S_oeis_a317688

/-- Every permutation of the decimal digits of `n` gives a prime. -/
def IsAbsolutePrime (n : ℕ) : Prop :=
  ∀ l : List ℕ, l.Perm (Nat.digits 10 n) → (Nat.ofDigits 10 l).Prime

/-- All decimal digits of `n` are `1`. -/
def IsRepunit (n : ℕ) : Prop := ∀ d ∈ Nat.digits 10 n, d = 1

theorem main :
    IsGreatest {n : ℕ | IsAbsolutePrime n ∧ ¬ IsRepunit n} 991 := by
  sorry

end OMA.S_oeis_a317688
