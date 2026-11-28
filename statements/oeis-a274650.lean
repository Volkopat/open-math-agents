import Mathlib

open Finset

/-!
# A274650: every column and diagonal of the greedy triangle is a permutation

Source: https://oeis.org/A274650 (offset 0).
Credit: @bnb9001

The triangle is filled row by row, from left to right, starting at (0,0).
Each entry is the least nonnegative integer not already used in its row,
column, diagonal or antidiagonal. The conjecture of Omar E. Pol, proved
by N. J. A. Sloane, states that every column and every diagonal is a
permutation of the nonnegative integers.

Here triangle n k is the actual greedy entry at row n and column k,
for 0 <= k <= n. Its definition uses well-founded recursion over earlier
cells and the least excluded value. The four attack equations specify
rows, columns and the two diagonal directions on the right triangle.
Column c is parameterized by (c+t,c), and diagonal d by (d+t,t), t >= 0.

Reference proof: https://oeis.org/A274650/a274650.txt
-/

namespace OMA.S_oeis_a274650

def attacks (n k r c : ℕ) : Prop :=
  n = r ∨ k = c ∨ n + c = r + k ∨ n + k = r + c

instance (n k r c : ℕ) : Decidable (attacks n k r c) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

def previous (n k : ℕ) : Finset (ℕ × ℕ) :=
  ((range (n+1)).product (range (n+1))).filter fun p =>
    p.2 ≤ p.1 ∧ (p.1 < n ∨ p.1 = n ∧ p.2 < k) ∧ attacks n k p.1 p.2

def mex (s : Finset ℕ) : ℕ := Nat.find (show ∃ m, m ∉ s from
  ⟨s.sup id + 1, fun h => by have := Finset.le_sup (f := id) h; simp only [id_eq] at this; omega⟩)

def triangle (n k : ℕ) : ℕ :=
  mex ((previous n k).attach.image fun p => triangle p.val.1 p.val.2)
termination_by n * (n+1) + k
decreasing_by
  have h := (Finset.mem_filter.mp p.property).2
  rcases h.2.1 with hlt | ⟨heq, hlt⟩
  · have _hsq : p.val.1 * p.val.1 ≤ n * p.val.1 := Nat.mul_le_mul_right _ (by omega)
    have hsq' : n * p.val.1 < n * n := Nat.mul_lt_mul_of_pos_left hlt (by omega)
    nlinarith [h.1]
  · rw [heq]
    omega

theorem main :
    (∀ c, Function.Bijective (fun t => OMA.S_oeis_a274650.triangle (c+t) c)) ∧
    (∀ d, Function.Bijective (fun t => OMA.S_oeis_a274650.triangle (d+t) t)) := by sorry

end OMA.S_oeis_a274650

