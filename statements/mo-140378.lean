import Mathlib

/-!
# A recurrence for the zero-charge coefficient of two partition products

Source: Nithilher, https://mathoverflow.net/questions/140378 (CC BY-SA 3.0).
Credit: @connoranderson.

The size variable is the power series variable and the charge variable is the
Laurent polynomial variable. The factor for part size d+1 and charge s sums
all possible multiplicities of that part. Factors above m do not affect the
size-m coefficient. At charge zero the recurrence uses only nonzero charges
at smaller sizes, so the other recurrence in the source can determine them.
-/

namespace OMA.S_mo_140378
open PowerSeries
noncomputable section
abbrev LP := LaurentPolynomial ℤ
abbrev PS := PowerSeries LP

def geom (d : ℕ) (s : ℤ) : PS :=
  expand (d+1) (by omega) (mk (fun k : ℕ => LaurentPolynomial.T (s*k)))

def partitionProduct (m : ℕ) : PS :=
  ∏ d ∈ Finset.range m, (geom d 1 * geom d (-1))

def count (m : ℕ) (z : ℤ) : ℤ := (coeff m (partitionProduct m)).coeff z

theorem main : count 0 0=1 ∧ ∀ (m : ℕ) (z : ℤ), 0 < m →
    (m:ℤ)*count m z =
      ∑ d ∈ Finset.range m, ∑ r ∈ Finset.range m,
        if d+1 ∣ r+1 then ((d+1:ℕ):ℤ) *
          (count (m-(r+1)) (z-((r+1)/(d+1):ℕ)) +
           count (m-(r+1)) (z+((r+1)/(d+1):ℕ))) else 0 := by
  sorry

end
end OMA.S_mo_140378
