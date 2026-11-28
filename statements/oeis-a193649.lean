import Mathlib

/-!
# A193649: Q-residue of the (n+1)st Fibonacci polynomial, with t(i,j) = 1

Source: https://oeis.org/A193649
Credit: @xor2k
Sibling of OEIS A193661 (same conjecture wording); statement modelled on the accepted one for that entry.

Definition in the entry: Q-residue of the (n+1)st Fibonacci polynomial, where Q is the triangular
array (t(i,j)) given by t(i,j)=1. For a polynomial p = p(0)*x^n + p(1)*x^(n-1) + ... + p(n) of
positive degree and the polynomials q(k,x) = t(k,0)*x^k + t(k,1)*x^(k-1) + ... + t(k,k), the
Q-downstep of p is D(p) = p(0)*q(n-1,x) + p(1)*q(n-2,x) + ... + p(n-1)*q(0,x) + p(n); if p is a
constant, D(p) = p. The result of n applications of D is a constant, the Q-residue of p.

The entry gives (R. J. Mathar, Feb 19 2015):
Conjecture: G.f.: -(1+x)*(2*x-1) / ( (x-1)*(4*x^2+x-1) ).

Conventions:
* Offset 0, as in the entry (data: 1, 1, 3, 5, 15, 33, 91, 221, 583, ...).
* Fibonacci polynomials: `F 0 = 0`, `F 1 = 1`, `F (n+2) = X * F (n+1) + F n`, so that
  `F 5 = X^4 + 3*X^2 + 1`, the polynomial of the entry's worked example for a(4) = 15. They are
  not in Mathlib (which has the signed Vieta-Fibonacci polynomials `Chebyshev.S`).
* The entry displays the rows of coefficients 1; 1, 0; 1, 0, 1; 1, 0, 2, 0; 1, 0, 3, 0, 1 (the
  unsigned triangle A049310, whose `T(n,k)` is the coefficient of `x^k`). As in the accepted
  statement of A193661, row `n` is turned into `p = T(n,0)*x^n + T(n,1)*x^(n-1) + ... + T(n,n)`
  with `T(n,k)` the coefficient of `x^k` in `F (n+1)`, i.e. `p` is the reversal of `F (n+1)`.
  This is the reading that reproduces the data: with `p = F (n+1)` itself the residues are
  1, 1, 3, 6, 15, 35, ..., which differ from the data at n = 3 (the worked example n = 4 is a
  palindrome and does not distinguish the two readings).
* Polynomials are in `ℤ[X]`. For `p` of degree `n = p.natDegree`, the entry `p(i)` (the
  coefficient of `x^(n-i)`) is `p.coeff (n - i)`. `q k = Σ_{j=0..k} X^(k-j)`.
* `residue p` applies `down` exactly `p.natDegree` times and takes the constant coefficient.
* The g.f. is stated in the equivalent form `A(x) * ((x-1)(4x^2+x-1)) = -(1+x)(2x-1)` in
  `PowerSeries ℤ`.
-/

namespace OMA.S_oeis_a193649

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

/-- Fibonacci polynomials: `F 0 = 0`, `F 1 = 1`, `F (n+2) = X * F (n+1) + F n`. -/
noncomputable def F : ℕ → ℤ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => X * F (n + 1) + F n

/-- `T(n,k)`: the coefficient of `x^k` in the `(n+1)`st Fibonacci polynomial. -/
noncomputable def T (n k : ℕ) : ℤ := (F (n + 1)).coeff k

/-- Row `n` as the polynomial `T(n,0)*x^n + ... + T(n,n)`. -/
noncomputable def P (n : ℕ) : ℤ[X] := ∑ k ∈ Finset.range (n + 1), C (T n k) * X ^ (n - k)

/-- A193649: the Q-residue of row `n`. -/
noncomputable def a (n : ℕ) : ℤ := residue (P n)

/-- The g.f. of `a` is `-(1+x)(2x-1)/((x-1)(4x^2+x-1))`. -/
theorem main :
    PowerSeries.mk a * ((PowerSeries.X - 1) * (4 * PowerSeries.X ^ 2 + PowerSeries.X - 1)) =
      -((1 + PowerSeries.X) * (2 * PowerSeries.X - 1)) := by
  sorry

end OMA.S_oeis_a193649
