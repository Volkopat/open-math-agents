import Mathlib

/-!
# A236256: a(n) = |{0 < k < n: m = phi(k) + phi(n-k)/4 is an integer with C(2*m, m) - prime(m) prime}|, where C(2*m, m) = (2*m)!/(m!)^2.

Source: https://oeis.org/A236256
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, comment in A236256): "a(n) > 0 for all n > 410." That is, for every
`n > 410` there is some `k` with `0 < k < n` such that `phi(n - k)` is divisible by 4 and, for
`m = phi(k) + phi(n - k)/4`, the number `C(2*m, m) - prime(m)` is prime.

Conventions:
* `phi` is Euler's totient function `Nat.totient`.
* "`m` is an integer" means `4 ∣ phi(n - k)`; then `m = phi(k) + phi(n - k) / 4` exactly.
* `prime(m)` is the `m`-th prime with `prime(1) = 2` (OEIS convention), written
  `Nat.nth Nat.Prime (m - 1)`; here `m ≥ phi(k) ≥ 1`.
* `C(2*m, m)` is `Nat.choose (2 * m) m`. Since `C(2*m, m) ≥ prime(m)` for every `m ≥ 1`, the
  natural-number subtraction `C(2*m, m) - prime(m)` is the true difference.

With these definitions the first terms are 0, 0, 0, 0, 0, 1, 1, 0, 1, 2, as in the OEIS data (for
example `a(12) = 1` from `phi(2) + phi(10)/4 = 2` and `C(4, 2) - prime(2) = 3`), and the first
2000 terms of the b-file are reproduced.
-/

namespace OMA.S_oeis_a236256

/-- `prime m`: the `m`-th prime, 1-indexed, so `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)

/-- The condition counted by A236256 for `0 < k < n`: `m = phi(k) + phi(n-k)/4` is an integer
and `C(2*m, m) - prime(m)` is prime. -/
def Good (n k : ℕ) : Prop :=
  4 ∣ Nat.totient (n - k) ∧
    (Nat.choose (2 * (Nat.totient k + Nat.totient (n - k) / 4))
        (Nat.totient k + Nat.totient (n - k) / 4) -
      prime (Nat.totient k + Nat.totient (n - k) / 4)).Prime

/-- A236256: `a n` is the number of `k` with `0 < k < n` satisfying `Good n k`. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioo 0 n).filter (fun k => Good n k)).card

/-- Sun's conjecture: `a(n) > 0` for all `n > 410`. -/
theorem main : ∀ n : ℕ, 410 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a236256
