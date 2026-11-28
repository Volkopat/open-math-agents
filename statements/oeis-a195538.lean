import Mathlib

/-! # A195538: Pythagorean approximations to sqrt(8)
Source: https://oeis.org/A195538
Source algorithm: https://oeis.org/A195538
Credit: @jaredwilder

Zero-based index n represents OEIS index n+1. The source takes the (n+1)-term
continued fraction of sqrt(8)+3, whose digits are [5;1,4,1,4,...].
The two successive convergents are updated with the standard continuant
recurrence. The reduced rational is (p²-q²)/(2*p*q); the sequence is its
denominator. The reference bisection sequences use the independently
published recurrence formulas on their OEIS entries:
A098602 (0,12,420; recurrence 35,-35,1), A076218 (1,5,145;
recurrence 35,-35,1, after its leading zero), A000129 (Pell),
and A046176 (1,35; recurrence 34,-1). Only the applicable references
are included below. The full stated conjecture includes all bisections.
-/
namespace OMA.S_oeis_a195538

def convPair : ℕ → (ℤ × ℤ) × (ℤ × ℤ)
  | 0 => ((5,1),(6,1))
  | n+1 =>
    let z := convPair n
    ((4*z.2.1+z.1.1,4*z.2.2+z.1.2),
     (5*z.2.1+z.1.1,5*z.2.2+z.1.2))

def sourceRatio (n : ℕ) : ℚ :=
  let z := if n%2=0 then (convPair (n/2)).1 else (convPair (n/2)).2
  ((z.1:ℚ)^2-(z.2:ℚ)^2)/(2*(z.1:ℚ)*(z.2:ℚ))

def r3 (x y z : ℚ) : ℕ → ℚ
  | 0 => x
  | 1 => y
  | 2 => z
  | n+3 => 35*r3 x y z (n+2)-35*r3 x y z (n+1)+r3 x y z n

def a (n : ℕ) : ℚ := ((sourceRatio n).den:ℚ)

theorem main :
  (∀ n : ℕ, a (n+6) = 35*a (n+4)-35*a (n+2)+a n) ∧
  (∀ n : ℕ, a (2*n) = r3 1 5 145 (n+1)) ∧
  (∀ n : ℕ, a (2*n+1) = r3 0 12 420 (n+1)) := by
  sorry
end OMA.S_oeis_a195538
