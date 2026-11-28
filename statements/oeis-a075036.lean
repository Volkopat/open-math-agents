import Mathlib

/-!
# A075036: Smaller of two smallest consecutive numbers with 2n divisors.

Source: https://oeis.org/A075036
Credit: @avivorly

A075036 (offset 1): `a(n)` is the least `k` such that `k` and `k + 1` both have exactly `2n` divisors:
2, 14, 44, 104, 2511, 735, 29888, 2295, 6075, 5264, ...

Conjecture (Chai Wah Wu, Mar 12 2019): if a term `k` is even, the highest p-adic order of `k` (the maximum
may be attained by several p's) occurs at `p = 2` and the highest p-adic order of `k + 1` occurs at `p = 3`.
If a term `k` is odd, the highest p-adic order of `k` occurs at `p = 3` and the highest p-adic order of
`k + 1` occurs at `p = 2`.

The other conjecture recorded in the entry (if `p` is prime then `a(p) = A215199(p-1)`) is a separate
claim and is not part of this statement.

Conventions:
- `d m` is the number of divisors of `m` (`Nat.divisors`). `a n` is the least `k` with `d k = 2n` and
  `d (k + 1) = 2n` (`sInf`). If no such `k` existed, `a n` would be 0, for which every p-adic order of
  `0` and of `1` is 0 in Mathlib, so the statement would hold there trivially; it constrains only the terms
  that exist.
- The highest p-adic order of `m` occurs at `q` means: `padicValNat p m ≤ padicValNat q m` for every
  prime `p` (ties allowed, as the entry says).
-/

namespace OMA.S_oeis_a075036

/-- The number of divisors of `m`. -/
def d (m : ℕ) : ℕ := m.divisors.card

/-- A075036: the least `k` such that `k` and `k + 1` both have `2n` divisors. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | d k = 2 * n ∧ d (k + 1) = 2 * n}

/-- The highest p-adic order of `m` occurs at `q` (possibly together with other primes). -/
def TopAt (q m : ℕ) : Prop := ∀ p : ℕ, p.Prime → padicValNat p m ≤ padicValNat q m

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (Even (a n) → TopAt 2 (a n) ∧ TopAt 3 (a n + 1)) ∧
      (Odd (a n) → TopAt 3 (a n) ∧ TopAt 2 (a n + 1)) := by
  sorry

end OMA.S_oeis_a075036
