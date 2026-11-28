import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Chain
import Mathlib.Order.Lattice.Nat

/-!
# Longest paths of the fiveleaper on square boards

A fiveleaper jumps between two lattice squares at Euclidean distance five.
Path length counts moves. A307554 starts at board side one. The second
conjecture below is the generating function written coefficientwise after
multiplication by (1-x)^3.

Source: https://oeis.org/A307554
Credit: @wtho704
-/

namespace OMA.S_oeis_a307554

abbrev Square := ℤ × ℤ

def jump (p q : Square) : Prop :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = 25

instance (p q : Square) : Decidable (jump p q) :=
  inferInstanceAs (Decidable (_ = _))

def box (xmin xmax ymin ymax : ℤ) (p : Square) : Prop :=
  xmin ≤ p.1 ∧ p.1 < xmax ∧ ymin ≤ p.2 ∧ p.2 < ymax

instance (xmin xmax ymin ymax : ℤ) (p : Square) : Decidable (box xmin xmax ymin ymax p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def pathOn (area : Square → Prop) (l : List Square) : Prop :=
  l.Nodup ∧ l.IsChain jump ∧ ∀ p ∈ l, area p

noncomputable def a (n : ℕ) : ℕ :=
  sSup {k | ∃ l : List Square, pathOn (box 0 n 0 n) l ∧ l.length - 1 = k}

/-- The coefficient of x^j, extended by zero outside the sequence's range. -/
noncomputable def coeff (j : ℤ) : ℤ := if 0 < j then (a j.toNat : ℤ) else 0

/-- Coefficients of x^5 (2 + 13x - 4x^2 - 23x^3 + 13x^4 + x^5). -/
def numerator : ℕ → ℤ
  | 5 => 2
  | 6 => 13
  | 7 => -4
  | 8 => -23
  | 9 => 13
  | 10 => 1
  | _ => 0

theorem main :
    (∀ n : ℕ, 7 < n → a n = n ^ 2 - 1) ∧
    ∀ n : ℕ, coeff n - 3 * coeff (n - 1 : ℤ) + 3 * coeff (n - 2 : ℤ) -
      coeff (n - 3 : ℤ) = numerator n := by
  sorry

end OMA.S_oeis_a307554
