import Mathlib

/-!
# A153772: a(n) = (2^n + 2*(-1)^n - 6)/3.

Source: https://oeis.org/A153772
Credit: @avivorly

A153772 (offset 0): `a(n) = (2^n + 2*(-1)^n - 6)/3`: -1, -2, 0, 0, 4, 8, 20, 40, 84, 168, 340, ...

Conjecture (Markus Sigg, Sep 14 2020): For `n >= 6`, `a(n)` is the third largest natural number whose
Collatz orbit has length `n+2`.

Conventions:
- The Collatz map is `m ↦ m / 2` for even `m` and `m ↦ 3m + 1` for odd `m`. The Collatz orbit of `m` is
  `m, T(m), T(T(m)), ...` up to and including the first `1`, so its length is the number of its terms: the orbit
  of `m` has length `n + 2` exactly when the `(n + 1)`-st iterate of `m` is `1` and no earlier iterate is `1`
  (e.g. `20, 10, 5, 16, 8, 4, 2, 1` has length 8, so `20` is counted for `n = 6`; the numbers with orbit length 8
  are `128 > 21 > 20 > ...`).
- A natural number here means `m ≥ 1` (`0` is a fixed point of the map and never reaches `1`, so it is excluded anyway).
- `a(n)` is the third largest element of a set `S` of naturals means: `a(n)` is in `S` and exactly two elements
  of `S` are larger than it (if infinitely many were larger, the `ncard` would be `0`, not `2`).
- `a n` is computed in `ℤ`; the division by `3` is exact.
-/

namespace OMA.S_oeis_a153772

/-- A153772: `a(n) = (2^n + 2*(-1)^n - 6)/3`. -/
def a (n : ℕ) : ℤ := (2 ^ n + 2 * (-1) ^ n - 6) / 3

/-- The Collatz map: `m / 2` for even `m`, `3m + 1` for odd `m`. -/
def collatz (m : ℕ) : ℕ := if m % 2 = 0 then m / 2 else 3 * m + 1

/-- The Collatz orbit of `m` (its terms up to and including the first `1`) has length `L`:
the `(L - 1)`-st iterate is `1` and no earlier iterate is `1`. -/
def OrbitLength (m L : ℕ) : Prop :=
  collatz^[L - 1] m = 1 ∧ ∀ k < L - 1, collatz^[k] m ≠ 1

/-- The natural numbers whose Collatz orbit has length `L`. -/
def S (L : ℕ) : Set ℕ := {m : ℕ | 1 ≤ m ∧ OrbitLength m L}

theorem main :
    ∀ n : ℕ, 6 ≤ n → ∃ m : ℕ, (m : ℤ) = a n ∧ m ∈ S (n + 2) ∧
      {x : ℕ | x ∈ S (n + 2) ∧ m < x}.ncard = 2 := by
  sorry

end OMA.S_oeis_a153772
