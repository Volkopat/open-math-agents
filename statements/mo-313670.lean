import Mathlib

/-!
# Zero divisors with support size 3 in complex group algebras

Source: https://mathoverflow.net/questions/313670
Conjecture (asker). There is `f : ℕ → ℕ` such that: if `β` is a nonzero element of the complex
group algebra `ℂ[G]` of a finite group `G` with `1 ∈ supp β`, and `(1 + x + y) β = 0` or
`(1 + x - y) β = 0` for some distinct nontrivial `x, y ∈ G`, then the exponent of `⟨x, y⟩`
is at most `f |supp β|`.

Conventions. `ℂ[G]` is `MonoidAlgebra ℂ G` (a finitely supported function `G →₀ ℂ`), with
`of ℂ G g` the basis element of `g`; `supp β` is `β.coeff.support`. The exponent of `⟨x, y⟩` is
`Monoid.exponent` of the subgroup `Subgroup.closure {x, y}`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_313670

open MonoidAlgebra

theorem main :
    ∃ f : ℕ → ℕ, ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G]
      (β : MonoidAlgebra ℂ G) (x y : G),
      β ≠ 0 → (1 : G) ∈ β.coeff.support → x ≠ y → x ≠ 1 → y ≠ 1 →
      ((1 + of ℂ G x + of ℂ G y) * β = 0 ∨ (1 + of ℂ G x - of ℂ G y) * β = 0) →
      Monoid.exponent (Subgroup.closure ({x, y} : Set G)) ≤ f β.coeff.support.card := by
  sorry

end OMA.S_mo_313670
