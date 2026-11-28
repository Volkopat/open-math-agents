import Mathlib

/-!
# Does a 3D random walk visit infinitely many primes almost surely?

Source: https://math.stackexchange.com/questions/4818235/does-a-3d-random-walk-visit-infinitely-many-primes-almost-surely
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Consider a simple symmetric random walk $S_n$ on $\mathbb{Z}^3$ starting at the origin.
Is the set $L(\mathbb{P}) = \{(0, 0, p) : p \in \mathbb{N} \text{ prime}\}$ visited
infinitely often almost surely?
-/

namespace OMA.S_mse_4818235

open MeasureTheory ProbabilityTheory

/-- The six nearest-neighbor step vectors in $\mathbb{Z}^3$. -/
def stepSet : Finset (ℤ × ℤ × ℤ) :=
  {(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)}

theorem main :
    ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
      (X : ℕ → Ω → ℤ × ℤ × ℤ),
      (∀ n, Measurable (X n)) →
      iIndepFun X volume →
      (∀ n : ℕ, ∀ v ∈ stepSet, volume {ω | X n ω = v} = (1 : ENNReal) / 6) →
      ∀ᵐ ω ∂(volume : Measure Ω),
        Set.Infinite {n : ℕ | ∃ p : ℕ, Nat.Prime p ∧ (∑ k ∈ Finset.range n, X k ω) = (0, 0, (p : ℤ))} := by
  sorry

end OMA.S_mse_4818235
