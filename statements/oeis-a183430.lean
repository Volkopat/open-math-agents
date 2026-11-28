import Mathlib

/-!
# A183430, two-column arrays with a condition on row and column sums

Fix the left and right column sums A and B modulo four. In a row (x,y), the
exclusion x ≠ x+y+A means y ≠ -A. Its other exclusion y ≠ x+y+B means
x ≠ -B. Once A and B are fixed the columns can therefore be chosen
independently. The finite recursion counts words of actual residues with
the prescribed sum and one prohibited symbol.

The OEIS term is one third of the number of arrays. We state Colin Barker's
two formulas after multiplying by three, and clear the same factor in
the coefficient identity for the generating function. It starts at n=1.

Source: https://oeis.org/A183430
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a183430

open Finset

def column : ℕ → ZMod 4 → ZMod 4 → ℤ
  | 0, _, t => if t=0 then 1 else 0
  | n+1, f, t => ∑ x ∈ (univ.erase f), column n f (t-x)

def total (n : ℕ) : ℤ := ∑ a : ZMod 4, ∑ b : ZMod 4, column n (-b) a * column n (-a) b
def tripleTerm (n : ℕ) : ℤ := if n=0 then 0 else total n
def delayed (j n : ℕ) : ℤ := if j≤n then tripleTerm (n-j) else 0

theorem main :
    (∀ k : ℕ, 0<k → tripleTerm (2*k) = 9^(2*k)) ∧
    (∀ k : ℕ, tripleTerm (2*k+1) = 9^(2*k+1)+3) ∧
    (∀ n : ℕ, tripleTerm n-9*delayed 1 n-delayed 2 n+9*delayed 3 n =
      if n=1 then 12 else if n=2 then -27 else if n=3 then -9 else 0) := by
  sorry

end OMA.S_oeis_a183430
