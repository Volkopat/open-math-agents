import Mathlib
/-!
# Comparing number of spanning subgraphs

Source: https://mathoverflow.net/questions/15242
Credit: @LDJAI

Vertices are numbered by rows, with (x,y) at y*(n+1)+x. Each direction
has n*(n+1) edges. A spanning subgraph is specified by its deleted edges
of each direction, enumerated without repetition as increasing lists.
-/

namespace OMA.S_mo_15242

def size (n : Nat) := (n+1)*(n+1)

def origin (n : Nat) : Fin (size n) := ⟨0, by simp [size]⟩

/-- Horizontal edges are indexed row by row, n per row.
Vertical edge i joins i and i+(n+1). -/
def adjacent (n : Nat) (hdel vdel : List Nat) (a b : Nat) : Prop :=
  (∃ i < n*(n+1), i ∉ hdel ∧ a = (i/n)*(n+1)+i%n ∧ b = a+1) ∨
  (∃ i < n*(n+1), i ∉ hdel ∧ b = (i/n)*(n+1)+i%n ∧ a = b+1) ∨
  (a < n*(n+1) ∧ a ∉ vdel ∧ b = a+(n+1)) ∨
  (b < n*(n+1) ∧ b ∉ vdel ∧ a = b+(n+1))

def grid (n : Nat) (hdel vdel : List Nat) : SimpleGraph (Fin (size n)) where
  Adj a b := adjacent n hdel vdel a b
  symm := ⟨by
    intro a b h
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨by intro a h; rcases h with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> omega⟩

/-- The root and the specified row-major vertex belong to the same connected component. -/
def connectedTo (n : Nat) (hdel vdel : List Nat) (x y : Nat) : Prop :=
  ∃ t : Fin (size n), t.val = y*(n+1)+x ∧ (grid n hdel vdel).Reachable (origin n) t

noncomputable def count (n x y m p : Nat) : Nat := by
  classical
  let N := n*(n+1)
  let choices := fun k => (List.range N).sublistsLen k
  exact if m > N || p > N then 0 else
    ((choices (N-m)).map fun h =>
      ((choices (N-p)).filter fun v => decide (connectedTo n h v x y)).length).sum

theorem main : ∀ n x y m p : Nat, x ≤ n → y ≤ n → x < y → p < m →
    count n x y m p ≤ count n x y p m := by
  sorry

end OMA.S_mo_15242
