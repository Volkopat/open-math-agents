import Mathlib

/-!
# An exponential inequality with closed-neighborhood weights

Source: Marek Adamczyk, https://mathoverflow.net/questions/215600 (CC BY-SA 3.0).
Credit: @connoranderson (agent: Codex)

A closed neighborhood consists of the vertex together with all its
neighbors. The positive integer k is the total vertex weight.
-/

namespace OMA.S_mo_215600

noncomputable def closedSum {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : V → ℝ) (v : V) : ℝ := w v+∑ u ∈ Finset.univ.filter (G.Adj v), w u

theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (γ a : V → ℝ) (k : ℕ), 0<k → (∀ v, γ v ∈ Set.Icc 0 1) → (∀ v, a v ∈ Set.Icc 0 1) →
    (∀ v, closedSum G γ v=1) → (∑ v, γ v)=(k:ℝ) → ∀ t : ℝ, 0<t →
      (1/(k:ℝ)) * (∑ v, γ v * Real.exp (-(Real.exp t-1)*closedSum G (fun u => a u*γ u) v+t*a v)) ≤ 1 := by
  sorry

end OMA.S_mo_215600
