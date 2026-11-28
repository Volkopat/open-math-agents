import Mathlib

/-!
# OEIS A329395 and palindromic compositions
Source: https://oeis.org/A329395
Credit: @etaubman

A329395 compares the lengths of the ordered Lyndon factorizations in the
ordinary and opposite binary alphabet orders. Complementing every bit
transports the opposite alphabet order to the ordinary order. A066099 gives
the composition from the successive distances between set bits, counted
from the low end, then read in reverse order.
-/

namespace OMA.S_oeis_a329395

/-- Strict lexicographic order on digit strings; a proper prefix is smaller. -/
def lexLess : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: w, b :: v => if a = b then lexLess w v else decide (a < b)

/-- Compare the nonempty word with each of its nontrivial cyclic rotations. -/
def isLyndon (w : List ℕ) : Bool :=
  !w.isEmpty && (List.range (w.length - 1)).all (fun j =>
    lexLess w (w.drop (j + 1) ++ w.take (j + 1)))

/-- A Chen–Fox–Lyndon factorization is a nonincreasing list of Lyndon words. -/
def factors (w : List ℕ) (fs : List (List ℕ)) : Bool :=
  (fs.flatten == w) && fs.all isLyndon &&
    (fs.zip fs.tail).all (fun p => !(lexLess p.1 p.2))

def trimmed (n : ℕ) : List ℕ := (Nat.digits 2 n).reverse.tail

def equalCounts (n : ℕ) : Prop :=
  ∃ f g : List (List ℕ), factors (trimmed n) f = true ∧
    factors ((trimmed n).map (fun d => 1 - d)) g = true ∧ f.length = g.length

/-- Distances between successive one bits, with the initial position zero. -/
def oneGaps : ℕ → List ℕ → List ℕ
  | _, [] => []
  | gap, bit :: bits =>
      if bit = 1 then (gap + 1) :: oneGaps 0 bits else oneGaps (gap + 1) bits

def composition (n : ℕ) : List ℕ := (oneGaps 0 (Nat.digits 2 n)).reverse

def conjecture : Prop :=
  ∀ n : ℕ, 0 < n → (equalCounts n ↔ composition n = (composition n).reverse)

theorem main : conjecture := by
  sorry

end OMA.S_oeis_a329395
