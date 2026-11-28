import Mathlib

/-!
Source: https://oeis.org/A081672
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A081/A081672.seq
Credit: @sntntHb

A081672: Expansion of exp(2x) - exp(0) + BesselI_0(2x).

Source text: Conjecture: na(n) +2(1-n)a(n-1) +4(1-n)a(n-2) +8(n-2)a(n-3)=0
(R. J. Mathar, Nov 12 2012). Robert Israel (Jun 03 2016): the e.g.f.
satisfies a third-order differential equation which implies the recurrence.

Expanding the e.g.f.: exp(2x) has coefficient 2^n, the constant exp(0)=1
removes 1 at n=0, and BesselI_0(2x) = Sum_k x^(2k)/(k!)^2 has e.g.f.
coefficient C(2k,k) at n=2k. Hence a(0)=1 and a(n) = 2^n + [n even] C(n,n/2)
for n>=1 (first terms 1, 2, 6, 8, 22, 32, 84, 128, as in the OEIS data).

Domain: the recurrence fails at n=3 (3*8 - 4*6 - 8*2 + 8*1 = -8, because of
the exceptional term a(0)); it is checked numerically for 4 <= n < 60, so it
is formalized for n>=4.
-/

namespace OMA.S_oeis_a081672

def a (n : ℕ) : ℤ :=
  if n = 0 then 1 else (2:ℤ)^n+(if n % 2 = 0 then (n.choose (n/2):ℤ) else 0)

theorem main :
    ∀ n : ℕ, 4 ≤ n →
      (n:ℤ)*a n+2*(1-(n:ℤ))*a (n-1)+4*(1-(n:ℤ))*a (n-2)+8*((n:ℤ)-2)*a (n-3)=0 := by
  sorry

end OMA.S_oeis_a081672
