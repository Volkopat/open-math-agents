import Mathlib

/-!
# A236241: a(n) = |{0 < k < n: m = phi(k) + phi(n-k)/8 is an integer with C(2*m, m) + prime(m) prime}|

Source: https://oeis.org/A236241
Credit: @gblacher2

The sequence: `a(n)` is the number of `k` with `0 < k < n` such that
`m = phi(k) + phi(n-k)/8` is an integer and `C(2*m, m) + prime(m)` is prime, where
`C(2*m, m) = (2*m)!/(m!)^2` and `phi` is Euler's totient function.

Conjecture (Zhi-Wei Sun, A236241): "a(n) > 0 for every n = 20, 21, ... ."

Conventions: `prime(m)` is the `m`-th prime with `prime(1) = 2` (OEIS convention), written
`Nat.nth Nat.Prime (m - 1)`. Since `phi(k)` is an integer, `m` is an integer exactly when
`8 ∣ phi(n-k)`, and then `m = phi(k) + phi(n-k) / 8` with natural-number division. For
`0 < k` we have `phi(k) ≥ 1`, so `m ≥ 1` and `prime(m)` is defined. `C(2*m, m)` is
`Nat.choose (2 * m) m`. With these conventions `a(n) = 0` for `n < 20` and the values for
`n = 20, …, 30` are `1, 1, 2, 2, 3, 4, 2, 3, 4, 5, 2`, as in the OEIS data.
-/

namespace OMA.S_oeis_a236241

/-- `prime m`: the `m`-th prime, 1-indexed, so `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)

/-- The condition on `k` for a given `n`: `m = phi(k) + phi(n-k)/8` is an integer
(that is, `8 ∣ phi(n-k)`) and `C(2*m, m) + prime(m)` is prime. -/
def Good (n k : ℕ) : Prop :=
  8 ∣ Nat.totient (n - k) ∧
    (Nat.choose (2 * (Nat.totient k + Nat.totient (n - k) / 8))
        (Nat.totient k + Nat.totient (n - k) / 8) +
      prime (Nat.totient k + Nat.totient (n - k) / 8)).Prime

open Classical in
/-- `a n = |{0 < k < n : Good n k}|`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter (fun k => Good n k)).card

/-- Conjecture: `a(n) > 0` for every `n ≥ 20`. -/
theorem main : ∀ n : ℕ, 20 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a236241
