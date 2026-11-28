import Mathlib

/-!
# A116086: Perfect powers n with no primes between n and the next larger perfect power, which is in A116455.

Source: https://oeis.org/A116086
Credit: @luciusacarr

The entry records one conjecture: the sequence is finite. (The source adds: no other terms below
10^12, later extended to 10^18 and 4.5*10^18.) Its terms are 8, 25, 32, 121, 2187, 3125, 32761,
79507, 97336, 503284356, with prime-free ranges (2^3, 3^2), (5^2, 3^3), (2^5, 6^2), ...

Reading of the source:
* A perfect power (A001597) is a number `a^k` with `a ≥ 1` and `k ≥ 2` (this includes `1`; `1` is
  not a term, since the primes 2 and 3 lie between 1 and the next perfect power 4).
* `n` is a term if it is a perfect power and there is no prime `p` with `n < p < m`, where `m` is
  the next larger perfect power: the least perfect power exceeding `n` (it exists, e.g.
  `(n + 1)^2`). This is stated as: there is a perfect power `m > n` with no perfect power strictly
  between `n` and `m` and no prime strictly between `n` and `m`.
-/

namespace OMA.S_oeis_a116086

/-- `n` is a perfect power: `n = a^k` for some `a ≥ 1` and `k ≥ 2`. -/
def IsPerfectPower (n : ℕ) : Prop := ∃ a k : ℕ, 1 ≤ a ∧ 2 ≤ k ∧ n = a ^ k

/-- `n` is a term of A116086: a perfect power with no prime between it and the next larger
perfect power `m`. -/
def IsTerm (n : ℕ) : Prop :=
  IsPerfectPower n ∧ ∃ m : ℕ, n < m ∧ IsPerfectPower m ∧
    (∀ j : ℕ, n < j → j < m → ¬ IsPerfectPower j) ∧
    (∀ p : ℕ, n < p → p < m → ¬ p.Prime)

theorem main : {n : ℕ | IsTerm n}.Finite := by
  sorry

end OMA.S_oeis_a116086
