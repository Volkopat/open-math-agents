import Mathlib

/-!
# Erdős Problem 411

Source: https://www.erdosproblems.com/411

Let `g n = n + φ n` and let `g_k` be its `k`-th iterate. For which `n` and `r` is it true that
`g_{k+r} n = 2 g_k n` for all large `k`?

`main` states the conjectured answer recorded on the source page (Cambie): this happens
exactly when `r = 2` and `n = 2 ^ l * p` with `l ≥ 1` and `p ∈ {2, 3, 5, 7, 35, 47}`.

Conventions. `n ≥ 1` and `r ≥ 1`; `g_k` is `g^[k]` (so `g_0 = id`, which does not affect
"for all large `k`").

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_erdos_411

/-- `g n = n + φ n`. -/
def g (n : ℕ) : ℕ := n + Nat.totient n

theorem main :
    ∀ n r : ℕ, 1 ≤ n → 1 ≤ r →
      ((∀ᶠ k in Filter.atTop, g^[k + r] n = 2 * g^[k] n) ↔
        (r = 2 ∧ ∃ l p : ℕ, 1 ≤ l ∧ p ∈ ({2, 3, 5, 7, 35, 47} : Finset ℕ) ∧ n = 2 ^ l * p)) := by
  sorry

end OMA.S_erdos_411
