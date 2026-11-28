import Mathlib

/-!
# A conjecture involving `P_n = ∏_{k=1}^n p_k`

Source: https://mathoverflow.net/questions/360496 (Zhi-Wei Sun, CC BY-SA 4.0).

For each positive integer `n` let `P_n = ∏_{k=1}^n p_k`, where `p_k` is the `k`-th prime.
Conjecture: for any integer `n > 1` there are `k, m ∈ {1, …, n-1}` such that
`P_n ≡ P_k (mod n)` and `P_n ≡ -P_m (mod n)`. For example `P_32 ≡ P_23 (mod 32)` and
`P_32 ≡ -P_8 (mod 32)`. (Verified by the asker for `2 ≤ n ≤ 70000`; trivial for squarefree `n`.)

Formalization notes:
* `p_k` is the `k`-th prime with `p_1 = 2`, so `P n = ∏_{i < n} Nat.nth Nat.Prime i`.
* The congruences are taken in `ℤ` (because of the sign in `-P_m`).
* Checked numerically: holds for `2 ≤ n ≤ 3000`.
-/

namespace OMA.S_mo_360496

/-- `P_n`, the product of the first `n` primes. -/
noncomputable def P (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

/-- For every `n > 1` there are `k, m ∈ {1, …, n-1}` with `P_n ≡ P_k` and `P_n ≡ -P_m (mod n)`. -/
theorem main : ∀ n : ℕ, 1 < n → ∃ k ∈ Finset.Icc 1 (n - 1), ∃ m ∈ Finset.Icc 1 (n - 1),
    (P n : ℤ) ≡ P k [ZMOD n] ∧ (P n : ℤ) ≡ -(P m : ℤ) [ZMOD n] := by
  sorry

end OMA.S_mo_360496
