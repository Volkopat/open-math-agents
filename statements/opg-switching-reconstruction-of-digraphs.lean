import Mathlib

/-!
# Switching reconstruction of digraphs

Source: http://www.openproblemgarden.org/op/switching_reconstruction_of_digraphs
Credit: @shc261392

Question. Are there any switching-nonreconstructible digraphs on twelve or more vertices?

To switch a vertex of a digraph is to reverse all the arcs incident to it. The switching deck of
`D` is the collection of its switchings (one per vertex, up to isomorphism), and `D` is
switching-reconstructible if every digraph with the same deck is isomorphic to `D`.

Reading used here:
* Digraphs are oriented graphs (no loops, no pair of opposite arcs), the setting of Bondy and
  Mercier and of McKay and Schweitzer, given by an arc relation `r` on `Fin n`.
* Two digraphs have the same deck when some bijection `τ` of the vertices makes the switching of
  the first at `v` isomorphic to the switching of the second at `τ v`, for every `v`
  (equality of the multisets of isomorphism types).
* The question is stated in the affirmative: such a digraph exists on some `n ≥ 12` vertices.
-/

namespace OMA.S_opg_switching_reconstruction_of_digraphs

/-- `r` is an oriented graph: no arc has its reverse (in particular no loops). -/
def Oriented {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ∀ a b, r a b → ¬ r b a

/-- Switching `r` at `v`: reverse every arc with exactly one end equal to `v`. -/
def switch {n : ℕ} (r : Fin n → Fin n → Prop) (v : Fin n) (a b : Fin n) : Prop :=
  if (a = v ∧ b ≠ v) ∨ (a ≠ v ∧ b = v) then r b a else r a b

/-- Isomorphism of digraphs on `Fin n`. -/
def Iso {n : ℕ} (r s : Fin n → Fin n → Prop) : Prop :=
  ∃ σ : Fin n ≃ Fin n, ∀ a b, r a b ↔ s (σ a) (σ b)

/-- `r` and `s` have the same switching deck. -/
def SameDeck {n : ℕ} (r s : Fin n → Fin n → Prop) : Prop :=
  ∃ τ : Fin n ≃ Fin n, ∀ v, Iso (switch r v) (switch s (τ v))

/-- `r` is switching-reconstructible. -/
def Reconstructible {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ∀ s : Fin n → Fin n → Prop, Oriented s → SameDeck r s → Iso r s

theorem main :
    ∃ n : ℕ, 12 ≤ n ∧ ∃ r : Fin n → Fin n → Prop, Oriented r ∧ ¬ Reconstructible r := by
  sorry

end OMA.S_opg_switching_reconstruction_of_digraphs
