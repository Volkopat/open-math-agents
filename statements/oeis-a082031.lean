import Mathlib

/-!
# A082031: Mathar's recurrence for the e.g.f. exp(2x)/(1-x)^3

Source: https://oeis.org/A082031
Credit: @ivillar

A082031 (offset 0) is the expansion of the e.g.f. exp(2*x)/(1-x)^3;
data 1, 5, 28, 176, 1240, 9752, 85120, 819296, ... The entry gives the formula
a(n) = (1/2)*( Sum_{k = 0..n} (k+2)!*binomial(n,k)*2^(n-k) ) (Peter Bala, Sep 20 2013).

Conjecture (R. J. Mathar, Nov 24 2012; called a conjecture in Bala's comment):
a(n) + (-n-4)*a(n-1) + 2*(n-1)*a(n-2) = 0.

Formalization: a(n) is defined by Bala's formula, with (k+2)!/2 written as k! * C(k+2, 2), so
that every term is an integer. The recurrence is stated for every n ≥ 2, the range in which
a(n-2) is defined.
-/

namespace OMA.S_oeis_a082031

/-- a(n) = ∑_{k=0}^{n} C(n,k) k! C(k+2,2) 2^(n-k) = (1/2) ∑_k (k+2)! C(n,k) 2^(n-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (n.choose k : ℤ) * (k.factorial : ℤ) * ((k + 2).choose 2 : ℤ) * 2 ^ (n - k)

/-- Mathar's recurrence. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    a n + (-(n : ℤ) - 4) * a (n - 1) + 2 * ((n : ℤ) - 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a082031
