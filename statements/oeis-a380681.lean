import Mathlib

/-!
# The integral-series primality criterion of OEIS A380681

Source: https://oeis.org/A380681. The related entries A380682 through A380686
specialize the same conjecture at different primes. We use positive integer
parameters, for which the bilateral expression is a locally finite formal
power series. The parameter one is included. Zero and negative parameters
do not give this formal power-series sum.

Write Y for an indeterminate before substituting F(x). At an index n ≥ 0,
the monomial Y^j has coefficient (−1)^n binom(pn,j) and x-degree
n(pn+p−j). All such n start at ceil(j/p). At index −m, with m ≥ 1,
the summand is (−1)^m x^(pm(m−1))(1+x^mY)^(−pm). The Y^j
coefficient is (−1)^(m+j) binom(pm+j−1,j) at x-degree m(p(m−1)+j).
In both cases j and the excess index u are bounded by the x-degree.
-/
namespace OMA.S_oeis_a380681
open Finset

def firstIndex (p j : ℕ) : ℕ := j/p + if j%p=0 then 0 else 1

def term (p d j u : ℕ) : ℤ :=
  let n := u + firstIndex p j
  let m := u + 1
  (if n*(p*n+p-j)=d then (-1:ℤ)^n * (p*n).choose j else 0) +
  (if m*(p*u+j)=d then (-1:ℤ)^(m+j) * (p*m+j-1).choose j else 0)

def weight (p d j : ℕ) : ℤ := ∑ u ∈ range (d+1), term p d j u

noncomputable def layer (p d k : ℕ) (F : PowerSeries ℚ) : ℚ :=
  ∑ j ∈ range (d+1), (weight p d j : ℚ) * PowerSeries.coeff k (F^j)

/-- Coefficientwise form of p*x = S_p(x,F(x)), with F(0) = 1. -/
def satisfies (p : ℕ) (F : PowerSeries ℚ) : Prop :=
  PowerSeries.coeff 0 F=1 ∧ ∀ d : ℕ,
    (∑ t ∈ range (d+1), layer p t (d-t) F) = if d=1 then (p:ℚ) else 0

def integral (F : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n F=(z:ℚ)

theorem main : ∀ p : ℕ, 0<p → ∀ F : PowerSeries ℚ, satisfies p F →
    (integral F ↔ p.Prime) := by
  sorry

end OMA.S_oeis_a380681
