import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Logic.Relation

namespace OMA.S_mo_370694

abbrev Vertex (height : ℕ) := Fin (2 ^ (height + 1) - 1)

/-- Vertices have heap labels starting at one, and each non-root
vertex is joined to the vertex with half its label, rounded down. -/
def binaryTree (height : ℕ) : SimpleGraph (Vertex height) :=
  SimpleGraph.fromRel fun v w => (v.val + 1) / 2 = w.val + 1

/-- A move sends the whole source pile to an occupied vertex
at distance equal to the size of the source pile. -/
def Move (height : ℕ) (before after : Vertex height → ℕ) : Prop :=
  ∃ src dst : Vertex height,
    src ≠ dst ∧ 0 < before src ∧ 0 < before dst ∧
      (binaryTree height).dist src dst = before src ∧
      after = fun v => if v = src then 0
        else if v = dst then before dst + before src else before v

/-- All frogs can end at the root of a complete binary tree
whenever its height is different from two. -/
theorem main :
    ∀ height : ℕ, height ≠ 2 →
      Relation.ReflTransGen (Move height) (fun _ => 1)
        (fun v => if v.val = 0 then 2 ^ (height + 1) - 1 else 0) := by
  sorry

end OMA.S_mo_370694
