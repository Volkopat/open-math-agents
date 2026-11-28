import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card

/-!
# Distinct-part partitions with parts from A084215

R. J. Mathar conjectured that a(n+1) from A011558 counts partitions of n into
distinct parts from A084215. The latter sequence is 1, 2, 5, 10, 20, 40, ... .

Sources: https://oeis.org/A011558 and https://oeis.org/A084215
Credit: @wtho704
-/

namespace OMA.S_oeis_a011558

/-- A011558, the principal character modulo 5. Over the field of two
elements, multiplying the numerator and denominator of its defining series
by 1+x gives (x+x²+x³+x⁴)/(1+x⁵). -/
def a (n : ℕ) : ℕ := if n % 5 = 0 then 0 else 1

/-- A finite selection of distinct parts: choose 1 and 2 independently, and
choose the exponents j of the remaining parts 5 * 2^j. These three families
of parts are disjoint and the exponents determine distinct parts. -/
structure Selection where
  one : Bool
  two : Bool
  exponents : Finset ℕ

/-- Sum of the selected parts, with a parameter for the first large part. -/
def weight (b : ℕ) (p : Selection) : ℕ :=
  p.one.toNat + 2 * p.two.toNat + ∑ j ∈ p.exponents, b * 2 ^ j

/-- The empty selection gives the unique partition of zero. -/
theorem main : ∀ n : ℕ,
    a (n + 1) = ({p : Selection | weight 5 p = n} : Set Selection).ncard := by
  sorry

end OMA.S_oeis_a011558
