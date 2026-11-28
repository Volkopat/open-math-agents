import Mathlib

/-!
# Almost all free polyominoes are holey (OEIS A000105 / A000104)

Source: https://oeis.org/A000105
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture (John Mason, 2021): Almost all free polyominoes are holey; that is,
`A000104(n) / A000105(n) → 0` as `n → ∞`, where `A000105(n)` is the number of
free polyominoes with `n` cells and `A000104(n)` is the number of free hole-free
(simply connected) polyominoes with `n` cells.

Conventions:
- A polyomino of size `n` is a 4-connected finite subset of `ℤ × ℤ` of cardinality `n`.
- Two polyominoes are equivalent as free polyominoes if one is obtained from the
  other by a lattice isometry (translation plus reflection/rotation in `D_4`).
- A polyomino `S` is hole-free if its complement `(ℤ × ℤ) \ S` is 4-connected.
-/

namespace OMA.S_oeis_a000105

def gridAdj (p q : ℤ × ℤ) : Prop :=
  (p.1 = q.1 ∧ Int.natAbs (p.2 - q.2) = 1) ∨
  (p.2 = q.2 ∧ Int.natAbs (p.1 - q.1) = 1)

def IsPolyomino (n : ℕ) (S : Finset (ℤ × ℤ)) : Prop :=
  S.card = n ∧
  ∀ a ∈ S, ∀ b ∈ S,
    Relation.ReflTransGen (fun p q => p ∈ S ∧ q ∈ S ∧ gridAdj p q) a b

def IsHoleFree (S : Finset (ℤ × ℤ)) : Prop :=
  ∀ a : ℤ × ℤ, a ∉ S → ∀ b : ℤ × ℤ, b ∉ S →
    Relation.ReflTransGen (fun p q => p ∉ S ∧ q ∉ S ∧ gridAdj p q) a b

def GridSymEq (S T : Finset (ℤ × ℤ)) : Prop :=
  ∃ (dx dy sx sy : ℤ) (swap : Bool),
    (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧
    T = S.image (fun p =>
      if swap then (dx + sx * p.2, dy + sy * p.1)
      else (dx + sx * p.1, dy + sy * p.2))

noncomputable def freePolyominoCount (n : ℕ) : ℕ :=
  Nat.card (Quot (fun (S T : {S : Finset (ℤ × ℤ) // IsPolyomino n S}) => GridSymEq S.1 T.1))

noncomputable def holeFreePolyominoCount (n : ℕ) : ℕ :=
  Nat.card (Quot (fun (S T : {S : Finset (ℤ × ℤ) // IsPolyomino n S ∧ IsHoleFree S}) =>
    GridSymEq S.1 T.1))

theorem main :
    Filter.Tendsto
      (fun n : ℕ => (holeFreePolyominoCount n : ℝ) / (freePolyominoCount n : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

end OMA.S_oeis_a000105
