import Mathlib

/-!
# A065515: Number of prime powers ≤ n

Source: https://oeis.org/A065515
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of prime powers `≤ n`, counting `1 = p⁰` (offset `1`: `1, 2, 3, 4, 5, 5, …`).
Conjecture (Chayim Lowen, OEIS, 2015): `a(n) ≥ π(A069623(n)) + π(n) + 1`, where A069623(n) is the
number of perfect powers `≤ n` (counting `1`).

## Encoding

* Prime powers: `1` together with Mathlib's `IsPrimePow`. Perfect powers: `1` together with the
  numbers `m^k`, `m ≥ 2`, `k ≥ 2`.
* `π` is `Nat.primeCounting`. The statement is for all `n ≥ 1` (checked numerically for
  `n < 20000`).
-/

namespace OMA.S_oeis_a065515

/-- `a n`: number of prime powers (including `1`) in `[1, n]`. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun m => m = 1 ∨ IsPrimePow m).card

/-- `m` is a perfect power (including `1`). -/
def IsPerfectPower (m : ℕ) : Prop := m = 1 ∨ ∃ b k : ℕ, 2 ≤ b ∧ 2 ≤ k ∧ m = b ^ k

/-- A069623: number of perfect powers in `[1, n]`. -/
noncomputable def A069623 (n : ℕ) : ℕ :=
  Set.ncard {m : ℕ | 1 ≤ m ∧ m ≤ n ∧ IsPerfectPower m}

theorem main :
    ∀ n : ℕ, 1 ≤ n → Nat.primeCounting (A069623 n) + Nat.primeCounting n + 1 ≤ a n := by
  sorry

end OMA.S_oeis_a065515
