import Mathlib.Data.List.FinRange

/-!
# Dynamic optimality conjecture for splay trees

Source: https://en.wikipedia.org/wiki/Optimal_binary_search_tree#Dynamic_optimality
Credit: @RiverMint78

We use Sleator and Tarjan's original search-and-rotation model (Section 7,
Conjecture 1, https://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf).
A successful search costs one plus the depth and a rotation costs one.
The bound includes the original linear initialization allowance. The splay
tree starts in any shape and the offline comparator may choose its initial
shape for the same set of keys.
-/

namespace OMA.S_wpc_dynamic_optimality

inductive Tree (α : Type) where
  | empty
  | node (left : Tree α) (key : α) (right : Tree α)
  deriving DecidableEq

def Tree.inorder : Tree α → List α
  | .empty => []
  | .node left key right => left.inorder ++ key :: right.inorder

/-- All keys occur exactly once and in search-tree order. -/
def IsBST (tree : Tree (Fin n)) : Prop :=
  tree.inorder = List.finRange n

/-- One ancestor on a search path, with its subtree off the path. -/
inductive Frame (α : Type) where
  | fromLeft (parent : α) (right : Tree α)
  | fromRight (left : Tree α) (parent : α)

structure SearchHit (α : Type) where
  left : Tree α
  key : α
  right : Tree α
  ancestors : List (Frame α)

/-- Standard BST search. The closest ancestor comes first in the returned path. -/
def search [Ord α] (target : α) : Tree α → List (Frame α) → Option (SearchHit α)
  | .empty, _ => none
  | .node left key right, ancestors =>
      match compare target key with
      | .lt => search target left (.fromLeft key right :: ancestors)
      | .eq => some ⟨left, key, right, ancestors⟩
      | .gt => search target right (.fromRight left key :: ancestors)

/-- Splay the located node using a final zig and the four two-rotation cases. -/
def splayUp (key : α) : Tree α → Tree α → List (Frame α) → Tree α
  | left, right, [] => .node left key right
  | left, right, [.fromLeft parent sibling] =>
      .node left key (.node right parent sibling)
  | left, right, [.fromRight sibling parent] =>
      .node (.node sibling parent left) key right
  | left, right, .fromLeft parent sibling :: .fromLeft grandparent uncle :: rest =>
      splayUp key left (.node right parent (.node sibling grandparent uncle)) rest
  | left, right, .fromRight sibling parent :: .fromRight uncle grandparent :: rest =>
      splayUp key (.node (.node uncle grandparent sibling) parent left) right rest
  | left, right, .fromLeft parent sibling :: .fromRight uncle grandparent :: rest =>
      splayUp key (.node uncle grandparent left) (.node right parent sibling) rest
  | left, right, .fromRight sibling parent :: .fromLeft grandparent uncle :: rest =>
      splayUp key (.node sibling parent left) (.node right grandparent uncle) rest

/-- Each splay access pays for the search and for one rotation per ancestor. -/
def splayCost [Ord α] : List α → Tree α → Option ℕ
  | [], _ => some 0
  | target :: requests, tree => do
      let hit ← search target tree []
      let next := splayUp hit.key hit.left hit.right hit.ancestors
      let remaining ← splayCost requests next
      return 1 + 2 * hit.ancestors.length + remaining

/-- One rotation at any edge of the current tree. -/
inductive Rotation : Tree α → Tree α → Prop where
  | right (a : Tree α) (x : α) (b : Tree α) (y : α) (c : Tree α) :
      Rotation (.node (.node a x b) y c) (.node a x (.node b y c))
  | left (a : Tree α) (x : α) (b : Tree α) (y : α) (c : Tree α) :
      Rotation (.node a x (.node b y c)) (.node (.node a x b) y c)
  | inLeft {a a' : Tree α} (key : α) (b : Tree α) :
      Rotation a a' → Rotation (.node a key b) (.node a' key b)
  | inRight (a : Tree α) (key : α) {b b' : Tree α} :
      Rotation b b' → Rotation (.node a key b) (.node a key b')

/-- Legal offline executions may select rotations with knowledge of all requests. -/
inductive OfflineRun [Ord α] : Tree α → List α → ℕ → Prop where
  | done (tree : Tree α) : OfflineRun tree [] 0
  | rotate {tree next : Tree α} {requests : List α} {cost : ℕ} :
      Rotation tree next → OfflineRun next requests cost → OfflineRun tree requests (1 + cost)
  | access {tree : Tree α} {target : α} {hit : SearchHit α}
      {requests : List α} {cost : ℕ} :
      search target tree [] = some hit → OfflineRun tree requests cost →
      OfflineRun tree (target :: requests) (1 + hit.ancestors.length + cost)

/-- Comparison with every legal offline execution includes the cheapest one. -/
theorem main :
    ∃ C D : ℕ, 0 < C ∧
      ∀ (n : ℕ) (initial : Tree (Fin n)) (requests : List (Fin n)),
        IsBST initial →
          ∃ cost : ℕ, splayCost requests initial = some cost ∧
            ∀ (offlineInitial : Tree (Fin n)) (offlineCost : ℕ),
              IsBST offlineInitial → OfflineRun offlineInitial requests offlineCost →
                cost ≤ C * offlineCost + D * n := by
  sorry

end OMA.S_wpc_dynamic_optimality
