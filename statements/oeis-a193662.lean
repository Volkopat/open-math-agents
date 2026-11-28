import Mathlib

/-!
# A193662: Q-residue of the Lucas triangle A114525, where Q is the triangle given by t(i,j)=1 for 0<=i<=j

Source: https://oeis.org/A193662
Credit: @ivillar

Clark Kimberling's sequence (offset 0, data 2, 1, 5, 7, 25, 51, 149, 351, ...). For the Q-residue see
A193649: with q(k,x) = x^k + x^(k-1) + ... + 1 (all t(i,j) = 1), the Q-downstep of
p = p(0)*x^n + ... + p(n) is D(p) = p(0)*q(n-1,x) + ... + p(n-1)*q(0,x) + p(n), and the Q-residue is
the constant obtained after n downsteps. As in the entry's program, the residue is linear in p and
the residue of x^k is r(k), where r(0) = 1 and r(k) = Sum_{i=0..k-1} t(k-1,i)*r(k-1-i) =
Sum_{i=0..k-1} r(k-1-i). Hence a(n) = Sum_{k=0..n} [x^k]L(n,x) * r(n-k), where L(n,x) is the n-th
Lucas polynomial (Mathematica's LucasL[n,x], the rows of A114525): L(0,x) = 2, L(1,x) = x,
L(n,x) = x*L(n-1,x) + L(n-2,x).

Conjecture (R. J. Mathar, Feb 19 2015): a(n) = 2*a(n-1) +3*a(n-2) -4*a(n-3) if n>3.
-/

namespace OMA.S_oeis_a193662

open Polynomial

/-- The Lucas polynomials L(n,x). -/
noncomputable def L : ℕ → ℤ[X]
  | 0 => 2
  | 1 => X
  | n + 2 => X * L (n + 1) + L n

/-- r(0) = 1, r(k) = Sum_{i=0..k-1} r(k-1-i): the Q-residue of x^k. -/
def r : ℕ → ℤ
  | 0 => 1
  | k + 1 => ∑ i : Fin (k + 1), r (k - i)

/-- a(n) = Sum_{k=0..n} [x^k]L(n,x) * r(n-k). -/
noncomputable def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (L n).coeff k * r (n - k)

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 3 < n → a n = 2 * a (n - 1) + 3 * a (n - 2) - 4 * a (n - 3) := by
  sorry

end OMA.S_oeis_a193662
