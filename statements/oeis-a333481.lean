import Mathlib

/-!
# A333481: a(n) = [x^n] S(x)^(2*n), where S(x) = (1 - x - sqrt(1 - 6*x + x^2))/(2*x) is the o.g.f. of the large Schröder numbers A006318.

Source: https://oeis.org/A333481
Credit: @azmiozgen

Conjecture (Peter Bala, from the entry): the stronger supercongruences
a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) hold for prime p >= 5 and positive integers n and k.

Formalization notes:
* S(x) = (1 - x - sqrt(1 - 6x + x^2))/(2x) is the o.g.f. of the large Schröder numbers A006318,
  r(k) = Sum_{j=0..k} C(k,j) C(k+j,j)/(j+1) (1, 2, 6, 22, 90, ...); S is defined by these
  coefficients over ℚ.
* "x == y (mod p^(3k))" is stated as: x - y = p^(3k) * z for an integer z.
* Controls (computed): a(0..9) = 1, 4, 48, 652, 9344, 138004, 2077968, 31712412, 488793088,
  7591462564, as in the entry; the congruence holds for p = 5, 7 and n = 1, 2 with k = 1.
-/

namespace OMA.S_oeis_a333481

open PowerSeries

/-- The large Schröder numbers A006318: `r(k) = ∑_{j=0}^{k} C(k,j) C(k+j,j) / (j+1)`. -/
noncomputable def S : PowerSeries ℚ :=
  mk fun k => ∑ j ∈ Finset.range (k + 1), ((k.choose j * (k + j).choose j : ℕ) : ℚ) / (j + 1)

/-- A333481(n) = [x^n] S(x)^(2n). -/
noncomputable def a (n : ℕ) : ℚ := coeff n (S ^ (2 * n))

/-- The conjecture of the entry. -/
theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n r : ℕ, 1 ≤ n → 1 ≤ r →
      ∃ z : ℤ, a (n * p ^ r) - a (n * p ^ (r - 1)) = (p : ℚ) ^ (3 * r) * z := by
  sorry

end OMA.S_oeis_a333481
