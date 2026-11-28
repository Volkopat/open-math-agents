import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod

/-!
# OEIS A200166

R. H. Hardin counts triples of integers in [−n,n] with nonzero total
and with every zeroth, first and second difference nonzero. Colin Barker
conjectured a generating function and two parity formulas on May 17, 2018.

The zeroth differences are the three entries. The first differences are
nonzero exactly when neighbors differ, and the second is nonzero exactly
when the sum of the two endpoints differs from twice the middle entry.
The generating function starts at index one. Multiplying both sides by
(1−x)^4(1+x) gives the coefficient identity below.

Source: https://oeis.org/A200166
Credit: @ali-hamdan-007
-/

namespace OMA.S_oeis_a200166

def alphabet (n : ℕ) : Finset ℤ := (Finset.Icc (-(n : ℤ)) n).erase 0

/-- Triples whose zeroth, first and second differences are all nonzero. -/
def baseSet (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (alphabet n ×ˢ alphabet n ×ˢ alphabet n).filter fun t =>
    t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1+t.2.2 ≠ 2*t.2.1

def zeroSet (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (baseSet n).filter fun t => t.1 + t.2.1 + t.2.2 = 0

def goodSet (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (baseSet n).filter fun t => t.1 + t.2.1 + t.2.2 ≠ 0

def a (n : ℕ) : ℕ := (goodSet n).card

/-- Coefficient of x^j in the series beginning with a(1) x. -/
def seriesCoeff (j : ℤ) : ℤ := if 0 < j then (a j.toNat : ℤ) else 0

def numeratorCoeff : ℕ → ℤ
  | 1 => 2
  | 2 => 28
  | 3 => 30
  | 4 => 36
  | _ => 0

theorem main :
    (∀ n : ℕ, seriesCoeff n - 3*seriesCoeff ((n : ℤ)-1)
      + 2*seriesCoeff ((n : ℤ)-2) + 2*seriesCoeff ((n : ℤ)-3)
      - 3*seriesCoeff ((n : ℤ)-4) + seriesCoeff ((n : ℤ)-5) = numeratorCoeff n) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℤ) = 11*(n : ℤ) - 13*n^2 + 8*n^3) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℤ) = -4 + 11*(n : ℤ) - 13*n^2 + 8*n^3) := by
  sorry

end OMA.S_oeis_a200166
