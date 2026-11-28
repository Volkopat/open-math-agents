import Mathlib

/-!
# If `|G| = p³q²` then the Frattini subgroup is cyclic

Source: https://math.stackexchange.com/questions/1870482
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (asker): if `G` is a finite group of order `p³q²` for distinct primes `p, q`, then the
Frattini subgroup `Φ(G)` is cyclic.

Conventions:
* `Φ(G)` is Mathlib's `frattini G` (intersection of the maximal subgroups); cyclic is
  `IsCyclic` of the subgroup.
-/

namespace OMA.S_mse_1870482

/-- `Φ(G)` is cyclic when `|G| = p³q²`. -/
theorem main : ∀ (G : Type) [Group G] [Fintype G] (p q : ℕ), p.Prime → q.Prime → p ≠ q →
    Fintype.card G = p ^ 3 * q ^ 2 → IsCyclic (frattini G) := by
  sorry

end OMA.S_mse_1870482
