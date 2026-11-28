import Mathlib

/-! # A174655: Partial sums of A049486
Source: https://oeis.org/A174655
Parent: https://oeis.org/A049486
The parent sequence is encoded using the published Mathematica LinearRecurrence
program of Harvey P. Dale (Aug 21 2013), with initial prefix 1,4 and tail
10,21,34,53 and signature (2,0,-2,1). This uses the independent published
parent recurrence, not the conjectured closed form or generating function of
the target. The offset is 1; index zero is a dummy value.
The conjecture is Barker's formula for every n > 1, with denominator cleared.
-/
namespace OMA.S_oeis_a174655
def tail : ℕ → ℤ
  | 0 => 10
  | 1 => 21
  | 2 => 34
  | 3 => 53
  | n+4 => 2*tail (n+3) - 2*tail (n+1) + tail n
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | n+3 => tail n
def a (n : ℕ) : ℤ := ∑ i ∈ Finset.range n, b (i+1)

open PowerSeries in
theorem main :
  (∀ n : ℕ, 1 < n →
    12*a n = 3*(-9+(-1 : ℤ)^n)+34*(n:ℤ)-12*(n:ℤ)^2+8*(n:ℤ)^3) ∧
  ((X-1)^4*(X+1) * mk a : ℤ⟦X⟧) = X*(X^5-X^4+3*X^3+2*X^2+2*X+1) := by
  sorry
end OMA.S_oeis_a174655
