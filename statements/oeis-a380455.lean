import Mathlib

/-!
# Prime factors of a polyomino

Gordon Hamilton's four proposed maxima in OEIS A380455. Each factor tiles
the whole board with congruent copies of itself. Translations, rotations,
and reflections are allowed, and the one-cell shape is the unit.

Sources: https://oeis.org/A380455 and https://oeis.org/A342430.
-/

namespace OMA.S_oeis_a380455

abbrev Cell := ℤ × ℤ
abbrev Shape := Finset Cell

def adjacent (u v : Cell) : Prop :=
  (u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2)) ∨
  (u.2 = v.2 ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1))

def polyomino (s : Shape) : Prop :=
  s.Nonempty ∧ ∀ p q : {c // c ∈ s},
    Relation.ReflTransGen (fun a b : {c // c ∈ s} => adjacent a.val b.val) p q

def congruent (a b : Shape) : Prop :=
  ∃ (swap : Bool) (sx sy : ℤ) (offset : Cell),
    (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧
    b = a.image (fun c =>
      let d := if swap then (c.2, c.1) else c
      (offset.1 + sx * d.1, offset.2 + sy * d.2))

def tiles (factor board : Shape) : Prop :=
  ∃ parts : Finset Shape,
    parts.Nonempty ∧ parts.biUnion id = board ∧
    (∀ p ∈ parts, congruent factor p) ∧
    (∀ p ∈ parts, ∀ q ∈ parts, p ≠ q → Disjoint p q)

/-- A prime shape has no monohedral tiling by a smaller nonunit shape. -/
def primeShape (s : Shape) : Prop :=
  polyomino s ∧ 1 < s.card ∧
    ∀ t : Shape, polyomino t → 1 < t.card → tiles t s → t.card = s.card

/-- A single board of area n admits k pairwise noncongruent prime factors.
Each factor has its own tiling of the board. -/
def realizes (n k : ℕ) : Prop :=
  ∃ (board : Shape) (factors : Finset Shape),
    polyomino board ∧ board.card = n ∧ factors.card = k ∧
    (∀ t ∈ factors, primeShape t ∧ tiles t board) ∧
    (∀ p ∈ factors, ∀ q ∈ factors, congruent p q → p = q)

def maximum (n k : ℕ) : Prop :=
  realizes n k ∧ ∀ j : ℕ, realizes n j → j ≤ k

theorem main : maximum 14 10 ∧ maximum 15 3 ∧ maximum 16 12 ∧ maximum 17 1 := by
  sorry

end OMA.S_oeis_a380455
