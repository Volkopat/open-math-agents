import Mathlib

/-!
# A193661: Q-residue of the triangle A193673, with t(i,j) = 1

Source: https://oeis.org/A193661
Credit: @jagong-cmu

Definition in the entry: Q-residue of the triangle A193673, where Q is the triangular array
(t(i,j)) given by t(i,j)=1. The Q-residue is defined in A193649: for a polynomial
p = p(0)*x^n + p(1)*x^(n-1) + ... + p(n) of positive degree and the polynomials
q(k,x) = t(k,0)*x^k + t(k,1)*x^(k-1) + ... + t(k,k), the Q-downstep of p is
D(p) = p(0)*q(n-1,x) + p(1)*q(n-2,x) + ... + p(n-1)*q(0,x) + p(n); if p is a constant, D(p) = p.
The result of n applications of D is a constant, the Q-residue of p. Row n of a triangle
(T(n,0), ..., T(n,n)) is the polynomial T(n,0)*x^n + T(n,1)*x^(n-1) + ... + T(n,n).

The entry gives (R. J. Mathar, Feb 19 2015):
Conjecture: G.f.: ( -1+8*x-13*x^2 ) / ( (x-1)*(3*x-1)*(7*x-1) ).

Conventions:
* Offset 0, as in the entry (data: 1, 3, 15, 93, 621, 4263, ...).
* A193673 (offset 0) is the triangle with rows 1; 2, 1; 5, 4, 1; 14, 15, 6, 1; ... Its name
  says "coefficient of x^(n-k) in (1/2)((x+3)^n+(x+1)^n)", but its data and its formula
  T(n,k) = binomial(n,k)*(1 + 3^(n-k))/2 give the coefficient of x^k. We follow the data:
  `T n k` is the coefficient of `X^k` in `(X+3)^n + (X+1)^n`, divided by 2 (the division in
  `ℤ` is exact). With the other reading the residues are 1, 3, 11, ..., not the data.
* Polynomials are in `ℤ[X]`. For `p` of degree `n = p.natDegree`, the entry `p(i)` (the
  coefficient of `x^(n-i)`) is `p.coeff (n - i)`. `q k = Σ_{j=0..k} X^(k-j)`.
* `residue p` applies `down` exactly `p.natDegree` times and takes the constant coefficient.
* The g.f. is stated in the equivalent form `A(x) * ((x-1)(3x-1)(7x-1)) = -1 + 8x - 13x^2`
  in `PowerSeries ℤ`.
-/

namespace OMA.S_oeis_a193661

open Polynomial

/-- `q(k,x) = x^k + x^(k-1) + ... + 1`, the row `k` of `Q` with `t(k,j) = 1`. -/
noncomputable def q (k : ℕ) : ℤ[X] := ∑ j ∈ Finset.range (k + 1), X ^ (k - j)

/-- The Q-downstep `D(p) = p(0)*q(n-1,x) + ... + p(n-1)*q(0,x) + p(n)`, and `D(p) = p` for a
constant `p`. -/
noncomputable def down (p : ℤ[X]) : ℤ[X] :=
  if p.natDegree = 0 then p
  else (∑ i ∈ Finset.range p.natDegree, C (p.coeff (p.natDegree - i)) * q (p.natDegree - 1 - i)) +
    C (p.coeff 0)

/-- The Q-residue: the constant left after `n` downsteps, `n` the degree of `p`. -/
noncomputable def residue (p : ℤ[X]) : ℤ := ((down^[p.natDegree]) p).coeff 0

/-- A193673: `T(n,k)`, half the coefficient of `x^k` in `(x+3)^n + (x+1)^n`. -/
noncomputable def T (n k : ℕ) : ℤ := (((X + 3 : ℤ[X]) ^ n + (X + 1) ^ n).coeff k) / 2

/-- Row `n` of A193673 as the polynomial `T(n,0)*x^n + ... + T(n,n)`. -/
noncomputable def P (n : ℕ) : ℤ[X] := ∑ k ∈ Finset.range (n + 1), C (T n k) * X ^ (n - k)

/-- A193661: the Q-residue of row `n` of A193673. -/
noncomputable def a (n : ℕ) : ℤ := residue (P n)

/-- The g.f. of `a` is `(-1+8x-13x^2)/((x-1)(3x-1)(7x-1))`. -/
theorem main :
    PowerSeries.mk a * ((PowerSeries.X - 1) * (3 * PowerSeries.X - 1) * (7 * PowerSeries.X - 1)) =
      -1 + 8 * PowerSeries.X - 13 * PowerSeries.X ^ 2 := by
  sorry

end OMA.S_oeis_a193661
