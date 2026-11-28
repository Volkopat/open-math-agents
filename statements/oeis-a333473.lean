import Mathlib

/-!
# A333473: a(n) = [x^n] ( S(x/(1 + x)) )^n, S the o.g.f. of the large Schroeder numbers

Source: https://oeis.org/A333473

Definition: `a(n) = [x^n] F(x)^n` with `F(x) = S(x/(1 + x))`, where
`S(x) = (1 - x - sqrt(1 - 6*x + x^2))/(2*x)` is the o.g.f. of the large Schroeder numbers A006318.
Offset 0; the data starts 1, 2, 12, 92, 752, 6352, 54768, ...
The entry also gives `F(x) = (1 - sqrt(1 - 4*x - 4*x^2))/(2*x) = 1 + 2*x + 4*x^2 + 12*x^3 + ...`
(A025227).

Conjectures of Peter Bala (Mar 23 2020), stated together here in the order of the entry:

1. `a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k))` for prime `p >= 5` and positive integers `n`, `k`;
2. more generally, for a positive integer `r` and an integer `s`, the sequence
   `a(r,s;n) := [x^(r*n)] F(x)^(s*n)` satisfies the same congruences.

The Gauss congruences (modulo `p^k`) quoted in the entry are known and are not part of the target;
the remarks on A103885 and A333090 concern other sequences and are not stated here.

Formalized:
* `F` is the integer power series with coefficients `fc`, defined by the recursion
  `fc 0 = 1`, `fc (n+1) = [n = 0] + sum_{i=0..n} fc i * fc (n - i)`, i.e. `F = 1 + x + x * F^2`.
  This is the unique power series with constant term 1 solving `x*F^2 - F + 1 + x = 0`, which is
  the quadratic satisfied by `(1 - sqrt(1 - 4*x - 4*x^2))/(2*x)`, the closed form of `S(x/(1+x))`
  given in the entry. The first 16 terms of `a` computed from it agree with the OEIS data.
* For negative `s`, `F^(s*n)` means `(F⁻¹)^(|s|*n)`, the inverse taken in `PowerSeries ℤ`
  (`F` has constant coefficient 1, so it is a unit).
* A congruence `x == y (mod N)` between integers is written as `N ∣ x - y`.
-/

namespace OMA.S_oeis_a333473

/-- Coefficients of `F(x) = S(x/(1+x))`, via `F = 1 + x + x * F^2`. -/
def fc : ℕ → ℤ
  | 0 => 1
  | n + 1 => (if n = 0 then 1 else 0) + ∑ i : Fin (n + 1), fc i * fc (n - i)
decreasing_by
  all_goals (have := i.2; omega)

/-- The power series `F(x) = S(x/(1+x)) = 1 + 2x + 4x^2 + 12x^3 + ...`. -/
def F : PowerSeries ℤ := PowerSeries.mk fc

/-- A333473: `a(n) = [x^n] F(x)^n`. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (F ^ n)

/-- `F(x)^m` for an integer exponent `m`, negative powers taken of the inverse of `F`. -/
noncomputable def Fpow (m : ℤ) : PowerSeries ℤ :=
  if 0 ≤ m then F ^ m.toNat else (Ring.inverse F) ^ (-m).toNat

/-- `a(r,s;n) = [x^(r*n)] F(x)^(s*n)`. -/
noncomputable def ars (r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  PowerSeries.coeff (r * n) (Fpow (s * n))

/-- The two conjectured congruences of the entry. -/
theorem main :
    (∀ p n k : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < k →
      ((p : ℤ) ^ (2 * k)) ∣ (a (n * p ^ k) - a (n * p ^ (k - 1)))) ∧
    (∀ (r : ℕ) (s : ℤ) (p n k : ℕ), 0 < r → p.Prime → 5 ≤ p → 0 < n → 0 < k →
      ((p : ℤ) ^ (2 * k)) ∣ (ars r s (n * p ^ k) - ars r s (n * p ^ (k - 1)))) := by
  sorry

end OMA.S_oeis_a333473
