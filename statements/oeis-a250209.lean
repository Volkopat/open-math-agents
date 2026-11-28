import Mathlib

/-!
# A250209: a multiple of n whose index gives a prime value of a cyclotomic polynomial at 2

Source: https://oeis.org/A250209
Credit: @R-Dson

`a(n)` is the least `k` such that `k * n` is in A072226, or `0` if no such `k` exists.
Conjecture: `a(n) > 0` for all `n`.

Conventions.
- A072226 is the sequence of positive integers `m` such that the `m`-th cyclotomic polynomial
  evaluated at `2` is prime. Here `m ≥ 1` and the value `(Polynomial.cyclotomic m ℤ).eval 2`;
  that value is positive for `m ≥ 1`, so taking its absolute value changes nothing, and a prime
  is a prime natural number.
- `a(n)` is the infimum in `ℕ` of the set of positive such `k`, so it is `0` exactly when the set
  is empty.
- The offset of the entry is `1`.
- First terms of the entry: 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2 (so `a(1) = 2` because the first
  cyclotomic polynomial is `X - 1`, whose value at `2` is `1`, while the second is `X + 1`).
-/

namespace OMA.S_oeis_a250209

/-- A072226: `k ≥ 1` and the `k`-th cyclotomic polynomial evaluated at `2` is a prime number. -/
def InA072226 (k : ℕ) : Prop :=
  1 ≤ k ∧ (Int.natAbs ((Polynomial.cyclotomic k ℤ).eval 2)).Prime

/-- Least `k` such that `k * n` is in A072226, or `0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ InA072226 (k * n)}

theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a250209
