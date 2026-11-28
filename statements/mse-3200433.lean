import Mathlib

/-!
# Complete Classification of Nontrivial Identical Binomial Coefficients

Source: https://math.stackexchange.com/questions/3200433/new-results-on-identical-binomial-coefficient
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
Are there any nontrivial identical binomial coefficients `C(n, k) = C(m, l)`
with `2 ≤ k ≤ n / 2`, `2 ≤ l ≤ m / 2`, and `(n, k) ≠ (m, l)` other than the
sporadic equalities
- `C(16, 2) = C(10, 3) = 120`
- `C(21, 2) = C(10, 4) = 210`
- `C(56, 2) = C(22, 3) = 1540`
- `C(120, 2) = C(36, 3) = 7140`
- `C(153, 2) = C(19, 5) = 11628`
- `C(221, 2) = C(17, 8) = 24310`
- `C(78, 2) = C(15, 5) = C(14, 6) = 3003`
and the infinite Fibonacci family (for `i ≥ 1`)
`C(F_{2i+2} F_{2i+3}, F_{2i} F_{2i+3}) = C(F_{2i+2} F_{2i+3} - 1, F_{2i} F_{2i+3} + 1)`?

## Formalization Notes
We normalize the ordered pair by requiring `m < n` (since `n = m` and `2 ≤ k, l ≤ n/2`
with `C(n, k) = C(n, l)` forces `k = l`). We state the 1996 conjecture that every such
pair belongs to the 9 sporadic pairs (6 pairs + 3 pairs from the triple `3003`) or the
infinite Fibonacci family.
-/

namespace OMA.S_mse_3200433

def IsKnownPair (n k m l : ℕ) : Prop :=
  ((n, k, m, l) ∈ ({
    (16, 2, 10, 3),
    (21, 2, 10, 4),
    (56, 2, 22, 3),
    (120, 2, 36, 3),
    (153, 2, 19, 5),
    (221, 2, 17, 8),
    (78, 2, 15, 5),
    (78, 2, 14, 6),
    (15, 5, 14, 6)
  } : Set (ℕ × ℕ × ℕ × ℕ))) ∨
  ∃ i : ℕ, 1 ≤ i ∧
    n = Nat.fib (2 * i + 2) * Nat.fib (2 * i + 3) ∧
    k = Nat.fib (2 * i) * Nat.fib (2 * i + 3) ∧
    m = n - 1 ∧
    l = k + 1

theorem main :
    ∀ n k m l : ℕ,
      2 ≤ k → 2 * k ≤ n →
      2 ≤ l → 2 * l ≤ m →
      m < n →
      n.choose k = m.choose l →
      IsKnownPair n k m l := by
  sorry

end OMA.S_mse_3200433
