import Mathlib

/-!
# A193656: Q-residue of the triangle p(n,k) = 2^(n-k)*5^k, with t(i,j) = 1

Source: https://oeis.org/A193656
Credit: @jagong-cmu

Definition in the entry: Q-residue of the triangle p(n,k)=(2^(n - k))*5^k, 0<=k<=n, where Q
is the triangular array (t(i,j)) given by t(i,j)=1. The Q-residue is defined in A193649:
for a polynomial p = p(0)*x^n + p(1)*x^(n-1) + ... + p(n) of positive degree and the polynomials
q(k,x) = t(k,0)*x^k + t(k,1)*x^(k-1) + ... + t(k,k), the Q-downstep of p is
D(p) = p(0)*q(n-1,x) + p(1)*q(n-2,x) + ... + p(n-1)*q(0,x) + p(n); if p is a constant, D(p) = p.
The result of n applications of D is a constant, the Q-residue of p. Row n of the triangle is
the polynomial p(n,0)*x^n + p(n,1)*x^(n-1) + ... + p(n,n).

The entry gives (R. J. Mathar, Feb 19 2015):
Conjecture: a(n) = 3*5^n-2*4^n; G.f.: ( 1-2*x ) / ( (5*x-1)*(4*x-1) ).

Conventions:
* Offset 0, as in the entry (data: 1, 7, 43, 247, 1363, ...).
* Polynomials are in `ℤ[X]`. For `p` of degree `n = p.natDegree`, the entry `p(i)` (the
  coefficient of `x^(n-i)`) is `p.coeff (n - i)`.
* `q k = Σ_{j=0..k} X^(k-j)`, since every `t(k,j)` is `1`.
* `residue p` applies `down` exactly `p.natDegree` times and takes the constant coefficient.
  For row `n` the degree is `n`, because the leading coefficient `2^n` is not zero.
* Both parts are stated: the closed form for every `n >= 0`, and the g.f. in the equivalent
  form `A(x) * (5x-1)*(4x-1) = 1 - 2x` in `PowerSeries ℤ`.
-/

namespace OMA.S_oeis_a193656

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

/-- Row `n` of the triangle: `Σ_{k=0..n} 2^(n-k)*5^k * x^(n-k)`. -/
noncomputable def P (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (2 ^ (n - k) * 5 ^ k) * X ^ (n - k)

/-- A193656: the Q-residue of row `n`. -/
noncomputable def a (n : ℕ) : ℤ := residue (P n)

/-- `a(n) = 3*5^n - 2*4^n`, and the g.f. is `(1-2x)/((5x-1)(4x-1))`. -/
theorem main :
    (∀ n : ℕ, a n = 3 * 5 ^ n - 2 * 4 ^ n) ∧
      PowerSeries.mk a * ((5 * PowerSeries.X - 1) * (4 * PowerSeries.X - 1)) =
        1 - 2 * PowerSeries.X := by
  sorry

end OMA.S_oeis_a193656
