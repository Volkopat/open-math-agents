import Mathlib

/-!
# OEIS A195549: hypotenuses in the Pythagorean approximations to 1/2

For slope 1/2, Shiu's parameter r + √(1+r²) is the golden ratio. Its
continued fraction has all partial quotients 1. The positive-index numerator
and denominator pairs are generated from (1,0) by (u,v) ↦ (u+v,u).
Moses's construction in A195547 applies Euclid's triple formula to each
pair and reduces to a primitive triple. The first triple is (2,0,2)
before reduction and (1,0,1) after reduction.

The conjectures are Colin Barker's 2012 recurrence and rational generating
function, and Sébastien Labbé's 2022 reduced-denominator formula. Gary
Detlefs gave the Fibonacci-square formula in 2011; see also A131534.

Sources: https://oeis.org/A195549, https://oeis.org/A195547,
https://oeis.org/A195548, https://oeis.org/A131534.
Credit: @rleshner (agent: Codex, model: GPT-6)
-/

namespace OMA.S_oeis_a195549

def convergent : ℕ → ℕ × ℕ
  | 0 => (1,0)
  | n+1 => let (u,v) := convergent n; (u+v,u)

/-- Divide all three coordinates of (2uv,u²−v²,u²+v²) by their common gcd. -/
def hyp (u v : ℕ) : ℕ :=
  (u^2+v^2) / Nat.gcd (Nat.gcd (2*(u*v)) (u^2+v^2)) (u^2-v^2)

/-- The sequence starts with index 1; the generating series has constant term 0. -/
def a (n : ℕ) : ℕ := if n=0 then 0 else hyp (convergent n).1 (convergent n).2

def recurrence : Prop := ∀ n : ℕ, 1 ≤ n → a (n+6) + a n = 18*a (n+3)

open PowerSeries

def generatingFunction : Prop :=
  ((1-3*X+X^2)*(1+3*X+8*X^2+3*X^3+X^4) : PowerSeries ℤ) *
    PowerSeries.mk (fun n => (a n : ℤ)) = X*(1+5*X+13*X^2-X^3-X^4-X^5)

def reducedDenominator : Prop := ∀ n : ℕ, 1 ≤ n →
  a n = (mkRat ((Nat.fib (2*n+1) : ℤ)-2) (Nat.fib (2*n+1))).den

theorem main : recurrence ∧ generatingFunction ∧ reducedDenominator := by
  sorry

end OMA.S_oeis_a195549
