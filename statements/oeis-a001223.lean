import Mathlib

/-!
# A001223: Prime gaps

Source: https://oeis.org/A001223
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = prime(n+1) - prime(n)` (offset `1`: `a(1) = 1, a(2) = 2, a(3) = 2, …`).
Two conjectures from the OEIS entry:
1. for any positive numbers `x` and `y` there is an index `k` with `x / y = a(k) / a(k+1)`;
2. for any three positive numbers `x`, `y` and `j` there is an index `k` with
   `x / y = a(k) / a(k+j)`.

## Encoding

* `x`, `y`, `j` are positive integers (ratios of gaps are rational, and `j` is an index shift).
* `gap k = Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k` is `a(k + 1)`; the shift of the
  index by one does not affect an existential over `k`.
* `x / y = a(k) / a(k+j)` is written without division as `x · a(k+j) = y · a(k)`.
* `main` is the conjunction of the two conjectures (the first is the case `j = 1` of the
  second, kept separately for faithfulness).
-/

namespace OMA.S_oeis_a001223

/-- The `k`-th prime gap (0-indexed): `prime(k+2) - prime(k+1)` in 1-indexed notation. -/
noncomputable def gap (k : ℕ) : ℕ := Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k

theorem main :
    (∀ x y : ℕ, 0 < x → 0 < y → ∃ k : ℕ, x * gap (k + 1) = y * gap k) ∧
    (∀ x y j : ℕ, 0 < x → 0 < y → 0 < j → ∃ k : ℕ, x * gap (k + j) = y * gap k) := by
  sorry

end OMA.S_oeis_a001223
