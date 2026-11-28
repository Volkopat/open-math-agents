import Mathlib.Data.Nat.Prime.Defs

/-!
# A195415: normalized exponential generating function of the powers of tanh(k x)

Source: https://oeis.org/A195415
Credit: @garrytaulu

Paul D. Hanna's sequence has positive offset and is defined by
  ∑ k ≥ 1, tanh(k x)^k = ∑ n ≥ 1, a(n) 4^(n-1) x^n / n!.
Peter Bala conjectured on 29 May 2022 that reduction modulo every prime p
has period p-1 from the first term. A period here need not be the least period.
-/

namespace OMA.S_oeis_a195415

/-- The n-th derivative at zero of tanh(k x)^h. The zeroth derivative
is 1 for h=0 and 0 otherwise. For h>0 the derivative of the h-th power is
k h times the difference of the (h-1)-st and (h+1)-st powers, since
tanh'(x) = 1 - tanh(x)^2. For h=0 the prefactor gives the zero derivative. -/
def derivative (k : Nat) : Nat → Nat → Int
  | 0, h => if h = 0 then 1 else 0
  | n + 1, h => (k : Int) * (h : Int) *
      (derivative k n (h - 1) - derivative k n (h + 1))

/-- The n-th derivative of the sum at zero. Only 1 ≤ k ≤ n contribute,
because tanh(k x)^k vanishes to order k. -/
def numerator (n : Nat) : Int :=
  ((List.range n).map (fun i => derivative (i + 1) n (i + 1))).sum

/-- The exact normalized coefficient, expressed without rounding integer division. -/
def IsTerm (n : Nat) (v : Int) : Prop :=
  numerator n = (4 : Int) ^ (n - 1) * v

/-- Every prime p gives a period p-1 of the integer coefficients modulo p. -/
theorem main : ∀ p : Nat, p.Prime → ∀ n : Nat, 1 ≤ n →
    ∃ u v : Int, IsTerm n u ∧ IsTerm (n + (p - 1)) v ∧
      u % (p : Int) = v % (p : Int) := by
  sorry

end OMA.S_oeis_a195415
