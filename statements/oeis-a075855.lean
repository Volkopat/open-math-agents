import Mathlib.Order.Bounds.Defs
import Mathlib.Data.Nat.Basic

/-!
# Longest diagonal path on the black squares of a chessboard

OEIS A075855 asks for the greatest number of black squares a simple path
can visit on an n-by-n chessboard. It gives the odd-order value and
conjectures the even-order value. Coordinates start at the black corner
(0,0). Both colors of even-order board give the same graph by reflection.

Source: https://oeis.org/A075855
Credit: @wtho704
-/

namespace OMA.S_oeis_a075855

abbrev Square := ℕ × ℕ

def Black (rows cols : ℕ) (p : Square) : Prop :=
  p.1 < rows ∧ p.2 < cols ∧ p.1 % 2 = p.2 % 2

def Step (a b : ℕ) : Prop := a + 1 = b ∨ b + 1 = a

def Adjacent (p q : Square) : Prop := Step p.1 q.1 ∧ Step p.2 q.2

/-- The first m entries give a path of m distinct black squares, with
successive entries diagonally adjacent. Entries beyond the path are unused. -/
def lengths (rows cols : ℕ) : Set ℕ :=
  {m | ∃ p : ℕ → Square,
    (∀ i < m, Black rows cols (p i)) ∧
    (∀ i < m, ∀ j < m, p i = p j → i = j) ∧
    ∀ i, i + 1 < m → Adjacent (p i) (p (i + 1))}

/-- Writing the side length as 2k+1 or 2k gives the two formulas of A075855. -/
theorem main :
    (∀ k : ℕ, IsGreatest (lengths (2 * k + 1) (2 * k + 1)) (2 * k ^ 2 + 1)) ∧
    (∀ k : ℕ, 0 < k → IsGreatest (lengths (2 * k) (2 * k)) (2 * k ^ 2 - k + 1)) := by
  sorry

end OMA.S_oeis_a075855
