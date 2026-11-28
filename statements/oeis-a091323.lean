import Mathlib

/-!
# OEIS A091323: transversals in Latin squares of odd order (Ryser's conjecture)

Source: https://oeis.org/A091323
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the minimum number of transversals in a Latin square of order `2n + 1`. Ryser
conjectured that `a(n) ≥ 1` for all `n`: every Latin square of odd order has a transversal.

Conventions:
* A Latin square of order `m` is `L : Fin m → Fin m → Fin m` with every row and every column a
  bijection. A transversal is a permutation `σ` of the rows such that the cells `(i, σ i)` carry
  pairwise distinct symbols.
-/

namespace OMA.S_oeis_a091323

/-- `L` is a Latin square. -/
def IsLatin {m : ℕ} (L : Fin m → Fin m → Fin m) : Prop :=
  (∀ i, Function.Bijective (L i)) ∧ ∀ j, Function.Bijective fun i => L i j

/-- Every Latin square of odd order has a transversal. -/
theorem main : ∀ (n : ℕ) (L : Fin (2 * n + 1) → Fin (2 * n + 1) → Fin (2 * n + 1)), IsLatin L →
    ∃ σ : Equiv.Perm (Fin (2 * n + 1)), Function.Injective fun i => L i (σ i) := by
  sorry

end OMA.S_oeis_a091323
