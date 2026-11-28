import Mathlib

/-!
# Kurkov's in-place algorithm for the row polynomials of A253829

Source: Mikhail Kurkov, https://mathoverflow.net/questions/491017 (CC BY-SA 4.0).
Credit: @connoranderson.

The vector is indexed from zero. In outer pass i, position j is incremented by
x times the sum of the already updated entries at positions 0 through j-i.
The product in z is read coefficientwise, so its degree-j coefficient is its
value for every finite truncation retaining at least the factors 1 through j.
-/

namespace OMA.S_mo_491017
open PowerSeries
noncomputable section
abbrev R := Polynomial ℤ

/-- Process the first t positions during outer pass i. -/
def sweep (i : ℕ) (v : ℕ → R) : ℕ → ℕ → R
  | 0 => v
  | t+1 => let w := sweep i v t
           Function.update w t (w t + if i ≤ t then Polynomial.X *
              ∑ k ∈ Finset.range (t-i+1), w k else 0)

/-- The first d outer passes on a length-m vector. -/
def vector (m : ℕ) : ℕ → ℕ → R
  | 0 => fun j => if j=0 then 1 else 0
  | d+1 => sweep (d+1) (vector m d) m

/-- The i-th factor (1-z)/(1-z-x*z^i) as a power series in z. -/
def factor (i : ℕ) : R⟦X⟧ :=
  (1-X) * invOfUnit (1-X-C (Polynomial.X : R)*X^i) 1

theorem main : ∀ m j N : ℕ, j < m → j ≤ N →
    vector m (m-1) j = coeff j (∏ i ∈ Finset.range N, factor (i+1)) := by
  sorry

end
end OMA.S_mo_491017
