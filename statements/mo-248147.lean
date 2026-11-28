import Mathlib

/-!
# Level sets and exact distribution of sums of inner-product scores on the Boolean cube

Source: https://mathoverflow.net/questions/248147 (Steve, CC BY-SA 3.0).
Credit: @connoranderson

A mask records the bits of the k vectors at one coordinate. All overlaps
are nonnegative integers. Work in the additive monoid algebra of k-by-k
overlap matrices: multiplication convolves counts and a monomial has one
matrix as its exponent. One row-mask contributes a product of k binomials.
The coefficient after mapping each matrix to its score counts its level
set, including collisions between different overlap matrices or scores.
The second formula gives the complete uniform law after division by
2^(2kd). No general-position or monotonicity assumption is needed.
-/

namespace OMA.S_mo_248147
open Finset
noncomputable section

abbrev Mask (k : ℕ) := Fin k → Bool
abbrev Overlaps (k : ℕ) := Fin k → Fin k → ℕ
abbrev Count (k : ℕ) := AddMonoidAlgebra ℕ (Overlaps k)

def atom {k : ℕ} (a b : Mask k) : Overlaps k :=
  fun i j => (a i && b j).toNat

def column {k : ℕ} (a : Mask k) (j : Fin k) : Overlaps k :=
  fun i l => if l=j then (a i).toNat else 0

def factor {k : ℕ} (a : Mask k) : Count k :=
  ∏ j, (1 + AddMonoidAlgebra.single (column a j) 1)

def overlaps {d k : ℕ} (a b : Fin d → Mask k) : Overlaps k :=
  ∑ t, atom (a t) (b t)

def score {k : ℕ} (f : ℕ → ℝ) (o : Overlaps k) : ℝ :=
  ∑ i, ∑ j, f (o i j)

def countAt {T : Type*} [Fintype T] (g : T → ℝ) (s : ℝ) : ℕ := by
  classical
  exact (univ.filter (fun t => g t = s)).card

def push {k : ℕ} (f : ℕ → ℝ) (c : Count k) (s : ℝ) : ℕ :=
  (AddMonoidAlgebra.mapDomain (score f) c).coeff s

theorem main : ∀ (d k : ℕ) (f : ℕ → ℝ) (s : ℝ),
    (∀ a : Fin d → Mask k,
      countAt (fun b => score f (overlaps a b)) s =
        push f (∏ t, factor (a t)) s) ∧
    countAt (fun z : Fin d → Mask k × Mask k =>
      score f (overlaps (fun t => (z t).1) (fun t => (z t).2))) s =
      push f ((∑ a : Mask k, factor a)^d) s := by
  sorry

end
end OMA.S_mo_248147
