import Mathlib

/-!
# Two recurrences for the mean binomial transform of the Catalan numbers

A102318 is the mean of the ordinary and signed binomial transforms of the
Catalan numbers. Averaging the two powers of the sign retains exactly the
terms with n-k even. Both recurrences are conjectured by R. J. Mathar
(June 8, 2016). Their first meaningful indices are five and four.

Source: https://oeis.org/A102318
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a102318

def transform (t : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n+1), t^(n-k) * (n.choose k : ℚ) * (catalan k : ℚ)

def sequence (n : ℕ) : ℚ := (transform 1 n + transform (-1) n) / 2

def orderFive (a : ℕ → ℚ) (m : ℕ) : ℚ :=
  let n := (m : ℚ) + 5
  (-(n-1))*(n+1)*a (m+5) + 2*(5*n^2-9*n+1)*a (m+4)
    + 2*(-15*n^2+58*n-49)*a (m+3) + 2*(10*n^2-76*n+123)*a (m+2)
    + (31*n-55)*(n-3)*a (m+1) - 30*(n-3)*(n-4)*a m

def orderFour (a : ℕ → ℚ) (m : ℕ) : ℚ :=
  let n := (m : ℚ) + 4
  (3*n-10)*(n-1)*(n+1)*a (m+4) + 2*(-12*n^3+58*n^2-67*n+10)*a (m+3)
    + 2*(21*n^3-136*n^2+289*n-196)*a (m+2) + 2*(n-2)*(12*n^2-46*n+27)*a (m+1)
    - 15*(n-2)*(n-3)*(3*n-7)*a m

theorem main : ∀ m : ℕ, orderFive sequence m = 0 ∧ orderFour sequence m = 0 := by
  sorry

end OMA.S_oeis_a102318
