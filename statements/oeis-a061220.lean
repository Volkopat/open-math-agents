import Mathlib

/-!
# A061220: Least entry in character table of the symmetric group S_n

Source: https://oeis.org/A061220
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: For n ≥ 2, the least entry in the character table of the symmetric group S_n
occurs in the column indexed by the transpositions, of cycle type (2, 1^(n-2)).

Conventions:
- Every finite-dimensional complex irreducible representation of S_n is realized on
  `Fin d → ℂ` for some `d ≥ 1`.
- Irreducibility is expressed by requiring `1 ≤ d` and that the only S_n-invariant
  `ℂ`-submodules of `Fin d → ℂ` are `⊥` and `⊤`.
- All character values of S_n are integers (in particular real), so we compare their
  real parts `(LinearMap.trace ℂ _ (ρ σ)).re`.
-/

namespace OMA.S_oeis_a061220

/-- A complex representation `ρ` of a group `G` on `Fin d → ℂ` is irreducible if `d ≥ 1`
and the only `G`-invariant subspaces are `⊥` and `⊤`. -/
def IsIrreducibleRep {G : Type} [Group G] {d : ℕ}
    (ρ : Representation ℂ G (Fin d → ℂ)) : Prop :=
  1 ≤ d ∧ ∀ W : Submodule ℂ (Fin d → ℂ),
    (∀ g : G, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤

/-- The real part of the character value of `ρ` at `g`. -/
noncomputable def charRe {G : Type} [Group G] {d : ℕ}
    (ρ : Representation ℂ G (Fin d → ℂ)) (g : G) : ℝ :=
  (LinearMap.trace ℂ (Fin d → ℂ) (ρ g)).re

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      ∃ (d₀ : ℕ) (ρ₀ : Representation ℂ (Equiv.Perm (Fin n)) (Fin d₀ → ℂ))
        (i j : Fin n),
        IsIrreducibleRep ρ₀ ∧ i ≠ j ∧
        ∀ (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Fin n)) (Fin d → ℂ))
          (σ : Equiv.Perm (Fin n)),
          IsIrreducibleRep ρ → charRe ρ₀ (Equiv.swap i j) ≤ charRe ρ σ := by
  sorry

end OMA.S_oeis_a061220
