import Mathlib

/-!
# A001419: Almost all polyominoes have holes

Source: https://oeis.org/A001419
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A001419: Number of n-celled polyominoes with holes.

Statement:
Conjecture (OEIS entry): Almost all polyominoes are holey.
In other words, a(n)/A000105(n) tends to 1 for increasing n.

Conventions:
- A fixed `n`-celled polyomino is a 4-connected subset of `ℤ × ℤ` of cardinality `n`.
- A free polyomino is an equivalence class of fixed polyominoes under lattice congruences
  (translations, rotations, and reflections of `ℤ × ℤ`).
- A polyomino has a hole iff its complement in `ℤ × ℤ` is not 4-connected.
-/

namespace OMA.S_oeis_a001419

/-- Two lattice cells in `ℤ × ℤ` are 4-adjacent (share an edge). -/
def Adj4 (p q : ℤ × ℤ) : Prop :=
  (p.1 - q.1).natAbs + (p.2 - q.2).natAbs = 1

/-- A set of lattice cells is 4-connected. -/
def ConnectedIn (S : Set (ℤ × ℤ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S,
    Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ Adj4 u v) p q

/-- `P` is a fixed `n`-celled polyomino. -/
def IsFixedPolyomino (n : ℕ) (P : Finset (ℤ × ℤ)) : Prop :=
  P.card = n ∧ ConnectedIn (P : Set (ℤ × ℤ))

/-- `P` has a hole iff its complement in `ℤ × ℤ` is disconnected. -/
def HasHole (P : Finset (ℤ × ℤ)) : Prop :=
  ¬ ConnectedIn ((P : Set (ℤ × ℤ))ᶜ)

/-- Two finite subsets of `ℤ × ℤ` are congruent under lattice isometries (translations + D_4). -/
def Congruent (P Q : Finset (ℤ × ℤ)) : Prop :=
  ∃ (tx ty sx sy : ℤ) (swap : Bool),
    (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧
    Q = P.image (fun p =>
      if swap then (sx * p.2 + tx, sy * p.1 + ty) else (sx * p.1 + tx, sy * p.2 + ty))

/-- `A000105(n)`: number of free `n`-celled polyominoes. -/
noncomputable def numPolyominoes (n : ℕ) : ℕ :=
  Nat.card (Quot (fun (P Q : {P : Finset (ℤ × ℤ) // IsFixedPolyomino n P}) => Congruent P.1 Q.1))

/-- `A001419(n)`: number of free `n`-celled polyominoes with holes. -/
noncomputable def numHoleyPolyominoes (n : ℕ) : ℕ :=
  Nat.card (Quot (fun (P Q : {P : Finset (ℤ × ℤ) // IsFixedPolyomino n P ∧ HasHole P}) =>
    Congruent P.1 Q.1))

theorem main :
    Filter.Tendsto (fun n : ℕ => (numHoleyPolyominoes n : ℝ) / (numPolyominoes n : ℝ))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a001419
