import Mathlib

/-!
# A076449: Least number whose digits can be used to form exactly n different primes (not necessarily using all digits).

Source: https://oeis.org/A076449
Credit: @divmxnd0x

A039993(m) is the number of distinct primes that can be formed from the decimal digits of `m`:
each digit of `m` is used at most once, in any order, and not necessarily all of them are used.
A076449(n) is the least `m ≥ 1` with A039993(m) = n (offset 0, a(0) = 1).

Conjecture (Mike Keith, reported by N. J. A. Sloane, Jan 25 2008): a(n) always exists, i.e. for
every `n ≥ 0` there is some `m ≥ 1` whose digits form exactly `n` different primes.
Keith checked this for `n ≤ 66`.

Formalization notes:
* A prime `p` can be formed from the digits of `m` exactly when the multiset of decimal digits of
  `p` is contained in the multiset of decimal digits of `m`. A number written with leading zeros
  equals the number formed from the remaining digits, so allowing leading zeros does not change
  the set of formable primes.
* Every such `p` has at most as many digits as `m`, so `p < 10 ^ (number of digits of m)`; the
  count below is therefore over a finite range and equals A039993(m).
* With this definition the least `m ≥ 1` with `A039993 m = n` is
  1, 2, 25, 13, 37, 107, 127, 113, 167, 1027, 179, 137, 1036, 1127, 1013, 1137 for n = 0, ..., 15,
  matching the data of A076449.
-/

namespace OMA.S_oeis_a076449

/-- A039993(m): the number of distinct primes whose decimal digits form a sub-multiset of the
decimal digits of `m`. -/
def A039993 (m : ℕ) : ℕ :=
  ((Finset.range (10 ^ (Nat.digits 10 m).length)).filter fun p =>
    p.Prime ∧ (Nat.digits 10 p : Multiset ℕ) ≤ (Nat.digits 10 m : Multiset ℕ)).card

/-- Mike Keith's conjecture: A076449(n) exists for every `n`, i.e. every `n` is attained by
A039993 at some positive integer. -/
theorem main : ∀ n : ℕ, ∃ m : ℕ, 0 < m ∧ A039993 m = n := by
  sorry

end OMA.S_oeis_a076449
