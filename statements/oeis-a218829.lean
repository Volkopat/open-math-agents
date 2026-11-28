import Mathlib

/-!
# A218829: Number of ordered ways to write n = k + m with k > 0 and m > 0 such that prime(k) + 2 and prime(prime(m)) + 2 are both prime.

Source: https://oeis.org/A218829
Credit: @divmxnd0x

Conjecture (i) (Zhi-Wei Sun, stated in A218829): `a(n) > 0` for all `n > 2`, and `a(n) = 1` only
for `n = 3, 22, 25, 38, 101, 273`.

Formalization notes:
* `prime(k)` is the `k`-th prime (`prime 1 = 2`); `a n` counts the `k` with `0 < k < n` such that
  `prime(k) + 2` and `prime(prime(n - k)) + 2` are both prime (data `0, 0, 1, 2, 2, 3, 2, ...`).
-/

namespace OMA.S_oeis_a218829

/-- The `k`-th prime, `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- A218829(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter fun k => (prime k + 2).Prime ∧ (prime (prime (n - k)) + 2).Prime).card

/-- Sun's conjecture (i). -/
theorem main : (∀ n : ℕ, 2 < n → 0 < a n) ∧
    ∀ n : ℕ, 2 < n → (a n = 1 ↔ n ∈ ({3, 22, 25, 38, 101, 273} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a218829
