import OMAStatements.S_oeis_a144876
import Mathlib

/-!
# Area bounds for square dissections into distinct polyominoes

Relative to a threshold of t cells, each smaller free shape can lower the
required area only once. A square dissection meeting the resulting integer
bound has as many pieces as any family of the same total area.
-/

namespace OMA.R_oeis_a144876_R1

open Finset OMA.S_oeis_a144876

/-- A catalogue covering the small shapes bounds the total area deficit. -/
def H1 : Prop :=
  ∀ (t : ℕ) (catalogue pieces : Finset Shape), distinctPolyominoes pieces →
    (∀ a ∈ pieces, a.card < t → ∃ r ∈ catalogue, congruent a r) →
    t * pieces.card ≤ (∑ a ∈ pieces, a.card) + ∑ r ∈ catalogue, (t - r.card)

/-- Construct a square dissection tight at some area threshold. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → ∃ (t : ℕ) (catalogue tiles : Finset Shape),
    0 < t ∧ (∀ a : Shape, polyomino a → a.card < t → ∃ r ∈ catalogue, congruent a r) ∧
    distinctPolyominoes tiles ∧ dissects n tiles ∧
    n ^ 2 + (∑ r ∈ catalogue, (t - r.card)) < t * (tiles.card + 1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a144876.main := by
  intro count construct n positive
  obtain ⟨t,catalogue,tiles,_,covers,distinct,board,sharp⟩ := construct n positive
  refine ⟨tiles,distinct,board,?_⟩
  intro candidates separate total
  have bound := count t catalogue candidates separate
    (fun a ha small => covers a (separate.1 a ha) small)
  rw [total] at bound
  by_contra! more
  have cost : t * (tiles.card + 1) ≤ t * candidates.card :=
    Nat.mul_le_mul_left t (by omega)
  omega

end OMA.R_oeis_a144876_R1
