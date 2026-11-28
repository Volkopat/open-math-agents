import Mathlib

/-!
# Has every finite group a minimal presentation?

Source: https://math.stackexchange.com/questions/217774
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For a finite group `G` let `d(G)` be the minimal number of generators and `r(G)` the minimal number
of relators in a finite presentation of `G`. A minimal presentation has `d(G)` generators and
`r(G)` relators. Question: does every finite group have a minimal presentation? `main` states the
answer yes.

Conventions:
* A presentation with `g` generators and `r` relators is a family `rel : Fin r → FreeGroup (Fin g)`
  with `PresentedGroup (Set.range rel) ≃* G`. `d(G)` is the least number of generators of `G`
  (a generating map `Fin g → G`), and `r(G)` the least `r` over all finite presentations (any
  number of generators).
-/

namespace OMA.S_mse_217774

/-- `G` has a presentation with `g` generators and `r` relators. -/
def HasPres (G : Type) [Group G] (g r : ℕ) : Prop :=
  ∃ rel : Fin r → FreeGroup (Fin g), Nonempty (PresentedGroup (Set.range rel) ≃* G)

/-- Every finite group has a presentation with `d(G)` generators and `r(G)` relators. -/
theorem main : ∀ (G : Type) [Group G] [Finite G],
    HasPres G (sInf {g | ∃ x : Fin g → G, Subgroup.closure (Set.range x) = ⊤})
      (sInf {r | ∃ g, HasPres G g r}) := by
  sorry

end OMA.S_mse_217774
