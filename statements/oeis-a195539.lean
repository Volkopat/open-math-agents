import Mathlib

/-! # A195539: Pythagorean approximations to sqrt(8)
Source: https://oeis.org/A195539
Source algorithm: https://oeis.org/A195538
Credit: @jaredwilder

Zero-based index n represents OEIS index n+1. The source takes the (n+1)-term
continued fraction of sqrt(8)+3, whose digits are [5;1,4,1,4,...].
The two successive convergents are updated with the standard continuant
recurrence. The reduced rational is (p²-q²)/(2*p*q); the sequence is its
numerator. The reference bisection sequences use the independently
published recurrence formulas on their OEIS entries:
A098602 (0,12,420; recurrence 35,-35,1), A076218 (1,5,145;
recurrence 35,-35,1, after its leading zero), A000129 (Pell),
and A046176 (1,35; recurrence 34,-1). Only the applicable references
are included below. The full stated conjecture includes all bisections.
-/
namespace OMA.S_oeis_a195539

def convPair : ℕ → (ℤ × ℤ) × (ℤ × ℤ)
  | 0 => ((5,1),(6,1))
  | n+1 =>
    let z := convPair n
    ((4*z.2.1+z.1.1,4*z.2.2+z.1.2),
     (5*z.2.1+z.1.1,5*z.2.2+z.1.2))

def sourceRatio (n : ℕ) : ℚ :=
  let z := if n%2=0 then (convPair (n/2)).1 else (convPair (n/2)).2
  ((z.1:ℚ)^2-(z.2:ℚ)^2)/(2*(z.1:ℚ)*(z.2:ℚ))

def r2 (x y : ℚ) : ℕ → ℚ
  | 0 => x
  | 1 => y
  | n+2 => 34*r2 x y (n+1)-r2 x y n

def pell : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | n+2 => 2*pell (n+1)+pell n

def a (n : ℕ) : ℚ := ((sourceRatio n).num:ℚ)

theorem main :
  (∀ n : ℕ, a (n+4) = 34*a (n+2)-a n) ∧
  (∀ n : ℕ, a (2*n) = pell (4*n+4)) ∧
  (∀ n : ℕ, a (2*n+1) = r2 1 35 (n+1)) := by
  sorry
end OMA.S_oeis_a195539
