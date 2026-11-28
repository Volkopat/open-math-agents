import Mathlib

/-!
# Does $\sum_{i\le k}\mathrm{frac}(n\alpha_i)<1$ hold infinitely often?

Source: https://mathoverflow.net/questions/351446
Credit: @ivillar

Status: known result, the answer is yes. The comments on the question give the argument: by
simultaneous approximation (or Poincaré recurrence) there are arbitrarily large `m` for which
all `m α_i` are very close to integers, and then the fractional parts of `(m + 1) α_i` are
almost the `α_i` themselves.

For each $t \in \mathbf{R}$, let $\mathrm{frac}(t)$ be its fractional part.

Question. Fix reals $\alpha_1,\ldots,\alpha_k \in (0,1)$ such that $\sum_{i\le k}\alpha_i<1$.
Do there exist infinitely many positive integers $n$ such that
$$ \sum_{i\le k}\mathrm{frac}(n\alpha_i)<1\,? $$

Formalization notes:
* The reals are a family `α : Fin k → ℝ`, and `frac` is `Int.fract`.
* "Infinitely many positive integers `n`" is the statement that the set of such `n : ℕ` is
  infinite.
-/

namespace OMA.S_mo_351446

theorem main : ∀ (k : ℕ) (α : Fin k → ℝ), (∀ i, 0 < α i ∧ α i < 1) → ∑ i, α i < 1 →
    {n : ℕ | 0 < n ∧ ∑ i, Int.fract ((n : ℝ) * α i) < 1}.Infinite := by
  sorry

end OMA.S_mo_351446
