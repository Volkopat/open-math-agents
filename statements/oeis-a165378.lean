import Mathlib

/-!
# OEIS A165378

Source: https://oeis.org/A165378 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Haruzame0

R. H. Hardin defines a(n) as the number of slanted n by 4 arrays with entries in
1..4, rows i = 1..n and columns j = i..i+3, such that each value is orthogonally
connected, the four corners are 1, 2, 3 and 4 in that order, and no cell has more
than two orthogonal neighbors of its own value.

Colin Barker conjectured that a(n) = 9*n^2 + 4*n - 2 for every n > 3, and gave the
ordinary generating function x^2 * (33 - 5*x - 25*x^2 + 18*x^3 - 3*x^4) / (1 - x)^3.
The theorem is the closed form. Neighbors are orthogonal adjacency.
Colors below are Fin 4 values 0, 1, 2, 3 in place of entries 1, 2, 3, 4.
-/

namespace OMA.S_oeis_a165378

/-- Cell `(row, offset)` of the slanted board. Absolute column is `row + offset`. -/
abbrev Cell (n : ℕ) := Fin n × Fin 4

def absCol {n : ℕ} (c : Cell n) : ℕ := c.1.val + c.2.val

/-- Orthogonal adjacency on the slanted board. -/
def neighbors {n : ℕ} (c d : Cell n) : Prop :=
  (c.1 = d.1 ∧ (c.2.val + 1 = d.2.val ∨ d.2.val + 1 = c.2.val)) ∨
    (c.1.val + 1 = d.1.val ∧ absCol c = absCol d) ∨
      (d.1.val + 1 = c.1.val ∧ absCol c = absCol d)

def sameAdj {n : ℕ} (f : Cell n → Fin 4) (c d : Cell n) : Prop :=
  neighbors c d ∧ f c = f d

/-- Cells of one color form a connected orthogonal graph. -/
def colorConnected {n : ℕ} (f : Cell n → Fin 4) (v : Fin 4) : Prop :=
  ∀ c d, f c = v → f d = v → Relation.ReflTransGen (sameAdj f) c d

noncomputable instance {n : ℕ} (c d : Cell n) : Decidable (neighbors c d) :=
  Classical.propDecidable (neighbors c d)

noncomputable instance {n : ℕ} (f : Cell n → Fin 4) (c d : Cell n) :
    Decidable (neighbors c d ∧ f d = f c) :=
  Classical.propDecidable (neighbors c d ∧ f d = f c)

noncomputable def neighborSame {n : ℕ} (f : Cell n → Fin 4) (c : Cell n) : ℕ :=
  ((Finset.univ : Finset (Cell n)).filter fun d => neighbors c d ∧ f d = f c).card

/-- Hardin's conditions: corner values, each color connected, degree at most 2. -/
def Valid (n : ℕ) (f : Cell n → Fin 4) : Prop :=
  ∃ hn : 0 < n,
    f ⟨⟨0, hn⟩, ⟨0, by decide⟩⟩ = 0 ∧
      f ⟨⟨0, hn⟩, ⟨3, by decide⟩⟩ = 1 ∧
        f ⟨⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩, ⟨0, by decide⟩⟩ = 2 ∧
          f ⟨⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩, ⟨3, by decide⟩⟩ = 3 ∧
            (∀ v : Fin 4, colorConnected f v) ∧
              ∀ c, neighborSame f c ≤ 2

theorem main : ∀ n : ℕ, 3 < n →
    Nat.card {f : Cell n → Fin 4 // Valid n f} = 9 * n ^ 2 + 4 * n - 2 := by
  sorry

end OMA.S_oeis_a165378
