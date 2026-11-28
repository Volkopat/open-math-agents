import Mathlib

/-!
# Barker's formulas for OEIS A280364

Source: https://oeis.org/A280364
Credit: @Heart-galaxy

We count the indicated matrices directly. The two pairs in the representation
of a matrix are its main diagonal `(a,d)` and its antidiagonal `(b,c)`.
Sela Fried proved the coefficient formulas in 2026, see
https://oeis.org/A280364/a280364_1.pdf, Theorem 1.
-/

namespace OMA.S_oeis_a280364

/-- Pairs of entries from `{0, …, n}`. -/
def entryPairs (n : ℕ) : Finset (ℕ × ℕ) := (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))

def pairProduct (p : ℕ × ℕ) : ℕ := p.1 * p.2

/-- Express the permanent and determinant equation over the integers. -/
def accept (n x y : ℕ) : Prop := (x : ℤ) + (y : ℤ) = ((x : ℤ) - (y : ℤ)) ^ n

instance (n x y : ℕ) : Decidable (accept n x y) :=
  inferInstanceAs (Decidable ((x : ℤ) + (y : ℤ) = ((x : ℤ) - (y : ℤ)) ^ n))

/-- The matrices whose permanent is their determinant to the power `n`. -/
def matrices (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((entryPairs n) ×ˢ (entryPairs n)).filter (fun p => accept n (pairProduct p.1) (pairProduct p.2))

/-- OEIS A280364 counts the matrices satisfying the equation. -/
def a (n : ℕ) : ℕ := (matrices n).card

/-- The ordinary generating function over the rationals. -/
def ogf : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))

/-- Barker's two coefficient formulas, recurrence, and ordinary generating function. -/
theorem main :
    (∀ n : ℕ, 0 < n → Even n → a n = 4 * n ^ 2 + 8 * n + 3) ∧
    (∀ n : ℕ, Odd n → a n = 4 * n ^ 2 + 6 * n + 2) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = (a (n - 1) : ℤ) + 2 * (a (n - 2) : ℤ) -
      2 * (a (n - 3) : ℤ) - (a (n - 4) : ℤ) + (a (n - 5) : ℤ)) ∧
    (let X : PowerSeries ℚ := PowerSeries.X;
      ogf = X * (12 + 23 * X - 3 * X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4) *
        (((1 - X) ^ 3 * (1 + X) ^ 2)⁻¹)) := by
  sorry

end OMA.S_oeis_a280364
