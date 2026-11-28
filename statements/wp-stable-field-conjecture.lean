import Mathlib

/-!
# Stable field conjecture

Source: https://en.wikipedia.org/wiki/Stable_theory
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture: every infinite field with a stable first-order theory is separably closed.

Conventions:
* First-order formulas are over Mathlib's language of rings `FirstOrder.Language.ring`, with the
  field `K` made a structure by `FirstOrder.Ring.compatibleRingOfRing` (the ring operations).
* `Th(K)` is stable iff no formula `φ(x̄; ȳ)` has the order property in a model of `Th(K)`. By
  compactness this is equivalent to: for every formula `φ(x̄; ȳ)` (`x̄` of length `n`, `ȳ` of
  length `m`) there is `N` such that there are no tuples `a₀, …, a_{N-1} ∈ Kⁿ`,
  `b₀, …, b_{N-1} ∈ Kᵐ` in `K` itself with `K ⊨ φ(aᵢ; bⱼ) ↔ i < j` for all `i, j < N`. This
  is the definition used below.
-/

namespace OMA.S_wp_stable_field_conjecture

open FirstOrder FirstOrder.Language

/-- `K` has a stable theory: no ring formula has the order property in `K` (uniformly
bounded ladders). -/
def IsStableField (K : Type) [Field K] : Prop :=
  letI := FirstOrder.Ring.compatibleRingOfRing K
  ∀ (n m : ℕ) (φ : Language.ring.Formula (Fin n ⊕ Fin m)), ∃ N : ℕ,
    ¬ ∃ (a : Fin N → Fin n → K) (b : Fin N → Fin m → K),
      ∀ i j : Fin N, (φ.Realize (Sum.elim (a i) (b j)) ↔ i < j)

/-- Every infinite stable field is separably closed. -/
theorem main : ∀ (K : Type) [Field K], Infinite K → IsStableField K → IsSepClosed K := by
  sorry

end OMA.S_wp_stable_field_conjecture
