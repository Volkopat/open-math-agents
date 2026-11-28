import Mathlib

/-!
# Trees in groups of exponential growth

Source: https://mathoverflow.net/questions/60011/trees-in-groups-of-exponential-growth
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: let `G` be a finitely generated group of exponential growth. Is there a finite
generating set `S` such that the Cayley graph `Cay(G, S)` contains a binary tree? `main`
states the positive answer.

Conventions.
* Word balls: `B_S(n)` is the set of products of at most `n` elements of `S ∪ S⁻¹`.
* Exponential growth (independent of the finite generating set): for some finite generating
  set `S` there is `c > 1` with `|B_S(n)| ≥ cⁿ` for all `n`.
* Binary tree: the rooted infinite binary tree has vertices `List Bool`, a vertex `l` being
  joined to its children `b :: l`. `Cay(G, S)` contains it if there is an injective map
  `φ : List Bool → G` with `φ (b :: l) = φ l * s` for some `s ∈ S ∪ S⁻¹` (a subgraph, not
  necessarily induced).
-/

namespace OMA.S_mo_60011

/-- The word ball of radius `n`. -/
def ball {G : Type} [Group G] (S : Set G) (n : ℕ) : Set G :=
  {g | ∃ l : List G, l.length ≤ n ∧ (∀ x ∈ l, x ∈ S ∨ x⁻¹ ∈ S) ∧ l.prod = g}

/-- `G` has exponential growth. -/
def ExponentialGrowth (G : Type) [Group G] : Prop :=
  ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
    ∃ c : ℝ, 1 < c ∧ ∀ n : ℕ, c ^ n ≤ ((ball (S : Set G) n).ncard : ℝ)

/-- `Cay(G, S)` contains a binary tree. -/
def ContainsBinaryTree {G : Type} [Group G] (S : Set G) : Prop :=
  ∃ φ : List Bool → G, Function.Injective φ ∧
    ∀ (b : Bool) (l : List Bool), ∃ s, (s ∈ S ∨ s⁻¹ ∈ S) ∧ φ (b :: l) = φ l * s

/-- Positive answer. -/
theorem main :
    ∀ (G : Type) [Group G], Group.FG G → ExponentialGrowth G →
      ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ ContainsBinaryTree (S : Set G) := by
  sorry

end OMA.S_mo_60011
