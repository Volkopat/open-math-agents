import Mathlib

/-!
# OEIS A144876: attaining the area bound for square dissections

Charlie Neder's conjecture of March 6, 2019, in https://oeis.org/A144876.
Ken Duisenberg's original puzzle identifies rotations and reflections:
https://ken.duisenberg.com/potw/archive/arch08/080912sol.html
Credit: @saientropy
-/

namespace OMA.S_oeis_a144876

abbrev Cell := ℤ × ℤ
abbrev Shape := Finset Cell

def adjacent (a b : Cell) : Prop :=
  (a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2)) ∨
  (a.2 = b.2 ∧ (a.1 + 1 = b.1 ∨ b.1 + 1 = a.1))

def polyomino (s : Shape) : Prop :=
  s.Nonempty ∧ ∀ p q : {c // c ∈ s},
    Relation.ReflTransGen (fun a b : {c // c ∈ s} => adjacent a.val b.val) p q

/-- Signed coordinate permutations are precisely the eight symmetries of a square. -/
def congruent (a b : Shape) : Prop :=
  ∃ (swap : Bool) (sx sy : ℤ) (offset : Cell),
    (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧
    b = a.image (fun c =>
      let d := if swap then (c.2, c.1) else c
      (offset.1 + sx * d.1, offset.2 + sy * d.2))

def distinctPolyominoes (pieces : Finset Shape) : Prop :=
  (∀ a ∈ pieces, polyomino a) ∧
  ∀ a ∈ pieces, ∀ b ∈ pieces, congruent a b → a = b

def square (n : ℕ) : Shape :=
  ((Finset.range n).product (Finset.range n)).image
    (fun c : ℕ × ℕ => ((c.1 : ℤ), (c.2 : ℤ)))

def dissects (n : ℕ) (pieces : Finset Shape) : Prop :=
  pieces.biUnion id = square n ∧
  ∀ a ∈ pieces, ∀ b ∈ pieces, a ≠ b → Disjoint a b

/-- For each positive side length, a dissection attains the largest cardinality
among all collections of distinct free shapes of exactly the board's area.
The abstract competitors have unrestricted placements. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ tiles : Finset Shape,
      distinctPolyominoes tiles ∧ dissects n tiles ∧
      ∀ candidates : Finset Shape, distinctPolyominoes candidates →
        (∑ a ∈ candidates, a.card) = n ^ 2 → candidates.card ≤ tiles.card := by
  sorry

end OMA.S_oeis_a144876
