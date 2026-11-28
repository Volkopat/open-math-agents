import Mathlib

/-!
# Periodic automorphism towers

Source: https://mathoverflow.net/questions/27861/periodic-automorphism-towers
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (the one asked on the page): does there exist a finite group `G` such that
`Aut(G) ≇ G` but `Aut⁽ⁿ⁾(G) ≅ G` for some `n ≥ 2`? `main` states the existence.

Encoding: `Aut⁽⁰⁾(G) = G`, `Aut⁽ⁿ⁺¹⁾(G) = Aut(Aut⁽ⁿ⁾(G))` with Mathlib's `MulAut`; the tower is
a sequence of groups packaged as `Σ H : Type, Group H`.
-/

namespace OMA.S_mo_27861

/-- The automorphism tower of `G`. -/
def tower (G : Type) [Group G] : ℕ → Σ H : Type, Group H
  | 0 => ⟨G, inferInstance⟩
  | (n + 1) =>
    letI := (tower G n).2
    ⟨MulAut (tower G n).1, inferInstance⟩

/-- Existence of a finite group with a nontrivially periodic automorphism tower. -/
theorem main :
    ∃ (G : Type) (_ : Group G) (_ : Finite G),
      IsEmpty (MulAut G ≃* G) ∧
      ∃ n : ℕ, 2 ≤ n ∧
        letI := (tower G n).2
        Nonempty ((tower G n).1 ≃* G) := by
  sorry

end OMA.S_mo_27861
