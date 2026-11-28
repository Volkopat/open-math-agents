import Mathlib

-- Is every group surjunctive? (Gottschalk 1973)
-- Source: https://en.wikipedia.org/wiki/Surjunctive_group
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
The source's definition (citing Ceccherini-Silberstein and Coornaert 2010, p. 57): a group `G` is
surjunctive if, for every finite set `S`, every continuous equivariant injective function
`f : S^G → S^G` is also surjective. Here `S^G` carries the prodiscrete topology (product of the
discrete topologies on `S`), and `G` acts on `S^G` by shifting: `(g • x) h = x (g⁻¹ * h)`.
The open question is whether every group is surjunctive; it is stated here in the affirmative.

Conventions:
* `S^G` is the function type `G → S` with Mathlib's product topology, `S` discrete.
* The shift is the left action `(g • x) h = x (g⁻¹ h)` used in the cited book; equivariance is
  `f (g • x) = g • f x` for all `g` and `x`.
* Groups and alphabets range over arbitrary universes.
-/

universe u v

namespace OMA.S_wp_is_every_group_surjunctive

/-- The left shift action of `G` on configurations `G → S`. -/
def shift {G : Type u} [Group G] {S : Type v} (g : G) (x : G → S) : G → S :=
  fun h => x (g⁻¹ * h)

/-- `G` is surjunctive: every injective cellular automaton over `G` with a finite alphabet,
i.e. every continuous shift-equivariant injective map `S^G → S^G`, is surjective. -/
def IsSurjunctive (G : Type u) [Group G] : Prop :=
  ∀ (S : Type v) [Finite S] [TopologicalSpace S] [DiscreteTopology S] (f : (G → S) → (G → S)),
    Continuous f → (∀ g x, f (shift g x) = shift g (f x)) → Function.Injective f →
      Function.Surjective f

/-- Gottschalk's question: every group is surjunctive. -/
theorem main : ∀ (G : Type u) [Group G], IsSurjunctive.{u, v} G := by
  sorry

end OMA.S_wp_is_every_group_surjunctive
