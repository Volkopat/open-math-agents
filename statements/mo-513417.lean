import Mathlib

/-!
# Gardam's support-21 unit in `𝔽₂[P]` is support-minimal

Source: https://mathoverflow.net/questions/513417/is-gardams-support-21-unit-in-mathbbf-2p-promislow-group-support-minim
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Gardam disproved Kaplansky's unit conjecture with a nontrivial unit of support size 21 in
`𝔽₂[P]`, `P = ⟨a, b | b⁻¹a²b = a⁻², a⁻¹b²a = b⁻²⟩` the Promislow group, and remarked that it is
plausible that every nontrivial unit has support size at least 21. `main` states this.

Conventions:
* `P` is the presented group on generators `a = of 0`, `b = of 1` with relators
  `b⁻¹a²b a²` and `a⁻¹b²a b²`.
* The support of `x ∈ 𝔽₂[P]` is `x.coeff.support`. Over `𝔽₂` the trivial units `λ g` are exactly
  the units of support size 1, so "nontrivial unit" means a unit whose support size is not 1.
-/

namespace OMA.S_mo_513417

/-- The relators of the Promislow group. -/
def rels : Set (FreeGroup (Fin 2)) :=
  let a := FreeGroup.of (0 : Fin 2)
  let b := FreeGroup.of (1 : Fin 2)
  {b⁻¹ * a ^ 2 * b * a ^ 2, a⁻¹ * b ^ 2 * a * b ^ 2}

/-- The Promislow group `P`. -/
abbrev Promislow := PresentedGroup rels

theorem main :
    ∀ u : (MonoidAlgebra (ZMod 2) Promislow)ˣ,
      (u : MonoidAlgebra (ZMod 2) Promislow).coeff.support.card ≠ 1 →
        21 ≤ (u : MonoidAlgebra (ZMod 2) Promislow).coeff.support.card := by
  sorry

end OMA.S_mo_513417
