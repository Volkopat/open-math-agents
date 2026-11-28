import Mathlib

/-!
# McKay conjecture

Source: https://en.wikipedia.org/wiki/McKay_conjecture
For a finite group `G` and a prime `p`, the number of irreducible complex characters of `G` of
degree not divisible by `p` equals the same number for the normaliser `N_G(P)` of a Sylow
`p`-subgroup `P`. (A proof by Cabanes and Späth was announced in 2024; the source list records
the problem.)

Conventions. Irreducible complex characters of a finite group `H` are the characters of simple
objects of Mathlib's category `FDRep ℂ H`; the degree is the dimension. Distinct irreducible
representations have distinct characters, so `p'Count H p` counts them up to isomorphism.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_wp_mckay_conjecture

open CategoryTheory

/-- The number of irreducible complex characters of `H` whose degree is prime to `p`. -/
noncomputable def p'Count (H : Type) [Group H] (p : ℕ) : ℕ :=
  Set.ncard {χ : H → ℂ | ∃ V : FDRep ℂ H, Simple V ∧ V.character = χ ∧
    ¬ p ∣ Module.finrank ℂ V}

theorem main :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      p'Count G p = p'Count (Subgroup.normalizer (P : Set G)) p := by
  sorry

end OMA.S_wp_mckay_conjecture
