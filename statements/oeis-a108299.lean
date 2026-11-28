import Mathlib

/-!
# Characteristic polynomial of Jeffery's tridiagonal matrix

OEIS A108299 indexes the coefficients from the leading term downwards. The
matrix has ones immediately above and below its main diagonal, with one more
one in its bottom right corner. The final equivalence gives all its real
characteristic roots. Index j runs from zero to n−1 here.

Source: L. Edson Jeffery, March 12, 2011, https://oeis.org/A108299
Credit: @connoranderson
-/

namespace OMA.S_oeis_a108299
open Matrix Polynomial

def jeffery (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if i.val+1=j.val ∨ j.val+1=i.val ∨ (i=j ∧ i.val+1=n) then 1 else 0

def rowEntry (n k : ℕ) : ℤ :=
  (Nat.choose (n-(k+1)/2) (k/2) : ℤ)*(-1)^((k+1)/2)

noncomputable def rootValue (n : ℕ) (j : Fin n) : ℝ :=
  2*Real.cos (((2:ℝ)*j.val+1)*Real.pi/(2*n+1))

theorem main : ∀ n : ℕ, 2 < n →
    (∀ k ≤ n, (jeffery n).charpoly.coeff (n-k) = rowEntry n k) ∧
    (∀ t : ℝ, (jeffery n).charpoly.IsRoot t ↔ ∃ j : Fin n, t=rootValue n j) := by
  sorry

end OMA.S_oeis_a108299
