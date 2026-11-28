import Mathlib

/-!
# End-devouring rays

Source: https://www.openproblemgarden.org/op/end_devouring_rays
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Problem (Georgakopoulos): let `G` be a graph, `ω` a countable end of `G`, and `K` an infinite
set of pairwise disjoint `ω`-rays. Then there is a set `K'` of pairwise disjoint `ω`-rays that
devours `ω` and whose set of starting vertices equals that of `K`.

Conventions (graphs arbitrary, possibly uncountable; Halin's ends).
* A ray is an injective sequence `r : ℕ → V` with `r n` adjacent to `r (n+1)`; its starting
  vertex is `r 0`. Rays are identified with sequences.
* Two rays are equivalent (lie in the same end) iff for every finite `S ⊆ V`, some tails of
  `r` and `s` avoid `S` and lie in one component of `G - S`. The end `ω` is given by a ray
  `r₀`, and the `ω`-rays are the rays equivalent to `r₀`.
* `K` devours `ω` iff every `ω`-ray meets (shares a vertex with) some ray of `K`; `ω` is
  countable iff some countable set of rays devours it.
-/

namespace OMA.S_opg_end_devouring_rays

open SimpleGraph

variable {V : Type} (G : SimpleGraph V)

/-- A ray of `G`. -/
def IsRay (r : ℕ → V) : Prop := Function.Injective r ∧ ∀ n, G.Adj (r n) (r (n + 1))

/-- Rays `r, s` belong to the same end. -/
def SameEnd (r s : ℕ → V) : Prop :=
  ∀ S : Finset V, ∃ (m n : ℕ) (hm : r m ∉ S) (hn : s n ∉ S),
    (∀ i, m ≤ i → r i ∉ S) ∧ (∀ j, n ≤ j → s j ∉ S) ∧
    (G.induce {v | v ∉ S}).Reachable ⟨r m, hm⟩ ⟨s n, hn⟩

/-- `r` is an `ω`-ray, where `ω` is the end of the ray `r₀`. -/
def IsEndRay (r₀ r : ℕ → V) : Prop := IsRay G r ∧ SameEnd G r₀ r

/-- A set of rays devours the end of `r₀`. -/
def Devours (r₀ : ℕ → V) (K : Set (ℕ → V)) : Prop :=
  ∀ r, IsEndRay G r₀ r → ∃ s ∈ K, ∃ m n, r m = s n

/-- Pairwise disjoint rays. -/
def PairwiseDisjointRays (K : Set (ℕ → V)) : Prop :=
  ∀ r ∈ K, ∀ s ∈ K, r ≠ s → ∀ m n, r m ≠ s n

/-- The problem's assertion. -/
theorem main :
    ∀ (V : Type) (G : SimpleGraph V) (r₀ : ℕ → V), IsRay G r₀ →
      (∃ C : Set (ℕ → V), C.Countable ∧ (∀ r ∈ C, IsRay G r) ∧ Devours G r₀ C) →
      ∀ K : Set (ℕ → V), K.Infinite → (∀ r ∈ K, IsEndRay G r₀ r) → PairwiseDisjointRays K →
        ∃ K' : Set (ℕ → V), (∀ r ∈ K', IsEndRay G r₀ r) ∧ PairwiseDisjointRays K' ∧
          Devours G r₀ K' ∧ (fun r => r 0) '' K' = (fun r => r 0) '' K := by
  sorry

end OMA.S_opg_end_devouring_rays
