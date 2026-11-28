import Mathlib

/-!
# Erdős Problem 374

Source: https://www.erdosproblems.com/374
Credit: @shc261392

For any `m ∈ ℕ`, let `F(m)` be the minimal `k ≥ 2` (if it exists) such that there are
`a₁ < ⋯ < a_k = m` with `a₁! ⋯ a_k!` a square. Let `D_k = {m : F(m) = k}`. What is the order of
growth of `|D_k ∩ {1, …, n}|` for `3 ≤ k ≤ 6`? For example, is it true that
`|D_6 ∩ {1, …, n}| ≫ n`?

This file states the explicit yes/no question: `|D_6 ∩ {1, …, n}| ≫ n`.

Reading used here:
* The `a_i` are positive integers (as in Erdős–Graham; allowing `0` would only append the factor
  `0! = 1`). `F m` is the least `k ≥ 2` admitting such `a`; if there is none, `sInf ∅ = 0`, so
  such `m` are in no `D_k` with `k ≥ 2`, matching "if it exists".
* `≫ n` means: there is `c > 0` with `c * n ≤ |D_6 ∩ {1, …, n}|` for all large `n`.
-/

namespace OMA.S_erdos_374

/-- `F m`: the least `k ≥ 2` such that some `0 < a₁ < ⋯ < a_k = m` have `a₁! ⋯ a_k!` a square. -/
noncomputable def F (m : ℕ) : ℕ :=
  sInf {k : ℕ | 2 ≤ k ∧ ∃ a : Fin k → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
    (∃ h : 0 < k, a ⟨k - 1, by omega⟩ = m) ∧ IsSquare (∏ i, (a i).factorial)}

theorem main :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      c * n ≤ (((Finset.Icc 1 n).filter (fun m => F m = 6)).card : ℝ) := by
  sorry

end OMA.S_erdos_374
