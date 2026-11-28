import Mathlib

/-!
# A193663: Q-residue of A049310 (triangle of coefficients of Fibonacci polynomials), where Q is the triangle given by t(n,k)=k+1 for 0<=k<=n.  (See Comments.)

Source: https://oeis.org/A193663
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A193663 (R. J. Mathar, Feb 19 2015):
G.f.: x*(1-x+x^2) / ( 1-2*x-6*x^2+7*x^3+x^4 ).

Conventions:
* The sequence has offset 0 (data 0, 1, 1, 9, 17, 80, 198, 748, ...).
* The Q-residue is computed by the formulation given in the COMMENTS of A193649 (to which the
  entry refers for the definition) and used verbatim by the Mathematica program of the entry:
  write q(n,k) for the entries of Q, define r(0) = 1 and
  r(k) = Sum_{i=0..k-1} q(k-1,i)*r(k-1-i), and then a(n) = v(n) = Sum_{k=0..n} p(n,k)*r(n-k),
  where p(n,k) is the entry in row n and column k of the triangle P.
* Here q(n,k) = k+1 and, as in the Mathematica program, p(n,k) is the coefficient of x^k in the
  Fibonacci polynomial Fibonacci[n, x], i.e. F_0 = 0, F_1 = 1, F_n = x*F_(n-1) + F_(n-2)
  (`F n` below, in `ℤ[X]`). This choice reproduces the data.
* The ordinary generating function is the formal power series `∑_{n ≥ 0} a(n) x^n`, here
  `PowerSeries.mk a` in `PowerSeries ℤ`. "G.f. = N(x)/D(x)" is stated without division, as
  `G.f. * D(x) = N(x)` with D(x) = 1-2*x-6*x^2+7*x^3+x^4, which is the same assertion (D has
  constant term 1, so it is invertible as a power series).
-/

namespace OMA.S_oeis_a193663

open Polynomial

/-- The Fibonacci polynomials: F_0 = 0, F_1 = 1, F_n = x*F_(n-1) + F_(n-2). -/
noncomputable def F : ℕ → ℤ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => X * F (n + 1) + F n

/-- r(0) = 1 and r(k) = Sum_{i=0..k-1} q(k-1,i)*r(k-1-i) with q(n,i) = i+1. -/
def r : ℕ → ℤ
  | 0 => 1
  | k + 1 => ∑ i : Fin (k + 1), (((i : ℕ) : ℤ) + 1) * r (k - (i : ℕ))

/-- A193663 (offset 0): a(n) = Sum_{k=0..n} p(n,k)*r(n-k), p(n,k) = [x^k] F_n(x). -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (F n).coeff k * r (n - k)

/-- The generating function of A193663 is x*(1-x+x^2) / (1-2*x-6*x^2+7*x^3+x^4). -/
theorem main :
    PowerSeries.mk a
        * (1 - 2 * PowerSeries.X - 6 * PowerSeries.X ^ 2 + 7 * PowerSeries.X ^ 3
          + PowerSeries.X ^ 4)
      = (PowerSeries.X : PowerSeries ℤ) * (1 - PowerSeries.X + PowerSeries.X ^ 2) := by
  sorry

end OMA.S_oeis_a193663
