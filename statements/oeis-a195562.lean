import Mathlib

/-!
# OEIS A195562: denominators of Pythagorean approximations to 1/4

Shiu's construction, implemented by Peter J. C. Moses in A195562, takes the
successive simple continued-fraction convergents u/v of r + √(1+r²), here
r = 1/4. It reduces the slope (u²−v²)/(2uv) to lowest terms. The sequence,
indexed from 1, consists of the resulting denominators. In particular its
first term is the denominator of the reduced slope 0/2.

R. J. Mathar proposed the recurrence in 2011 and Colin Barker gave the
empirical generating function in 2015. For the series we extend by a(0)=0.

Sources: https://oeis.org/A195562 and https://oeis.org/A195500
Credit: @rleshner (agent: Codex, model: GPT-6)
-/

namespace OMA.S_oeis_a195562

/-- The numerator and denominator after the first n partial quotients.
The empty continued fraction is represented by (1,0). -/
noncomputable def conv (r : ℝ) : ℕ → ℕ × ℕ
  | 0 => (1,0)
  | n+1 =>
    let p := conv ((r-⌊r⌋₊)⁻¹) n
    (⌊r⌋₊*p.1+p.2,p.1)
termination_by n => n

noncomputable def pair (n : ℕ) := conv ((1+Real.sqrt 17)/4) n

def reduced (p : ℕ × ℕ) : ℕ :=
  (2*(p.1*p.2)) / Nat.gcd (2*(p.1*p.2)) (p.1^2-p.2^2)

noncomputable def a (n : ℕ) := if n=0 then 0 else reduced (pair n)

def recurrence : Prop := ∀ n : ℕ, 1 ≤ n →
  a (n+9)+a n = 65*a (n+6)+65*a (n+3)

open PowerSeries

def generatingFunction : Prop :=
  ((X^9-65*X^6-65*X^3+1) : PowerSeries ℤ)*PowerSeries.mk (fun n => (a n : ℤ)) =
    X*(X^6+24*X^5+40*X^4-2*X^3+40*X^2+24*X+1)

theorem main : recurrence ∧ generatingFunction := by
  sorry

end OMA.S_oeis_a195562
