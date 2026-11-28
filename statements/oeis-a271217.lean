import Mathlib

/-!
# A271217: Number of symmetric reduced rearrangement maps.

Source: https://oeis.org/A271217
Credit: @agchua

R. J. Mathar (Jan 04 2017), in the formula section of A271217:
  Conjecture: (-2*n+9)*a(n) -4*a(n-1) +(2*n-3)*(2*n-7)*a(n-2) -4*a(n-3)
  +2*(2*n-5)*(n-4)*a(n-4)=0.
The offset is 0 (data 1, 2, 2, 6, 22, 50, 274, 598, 4486, ...).

The definition used here is the recurrence of the formula section,
  a(2*k+1) = 2*a(2*k) + a(2*k-1); a(2*k) = (2*k-1)*a(2*k-1) + (2*k-2)*a(2*k-3),
with the initial values a(0) = 1, a(1) = 2, a(2) = 2; this is exactly how the entry's PARI
program (Andrew Howroyd, Oct 30 2025, who also added the terms from a(21) on) computes the
sequence, and it reproduces all listed terms. So for m >= 3:
a(m) = 2*a(m-1) + a(m-2) if m is odd, and a(m) = (m-1)*a(m-1) + (m-2)*a(m-3) if m is even.
The counting definition of the name (signed permutations with symmetry conditions) is not
restated here. Values are integers.
The recurrence uses a(n-4), so the conjecture is stated for n >= 4.
-/

namespace OMA.S_oeis_a271217

/-- A271217 by the recurrence of its formula section, with a(0) = 1, a(1) = a(2) = 2. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | n + 3 =>
      if (n + 3) % 2 = 1 then 2 * a (n + 2) + a (n + 1)
      else ((n : ℤ) + 2) * a (n + 2) + ((n : ℤ) + 1) * a n

/-- Mathar's conjecture, for n >= 4. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (-2 * (n : ℤ) + 9) * a n - 4 * a (n - 1) + (2 * (n : ℤ) - 3) * (2 * (n : ℤ) - 7) * a (n - 2)
      - 4 * a (n - 3) + 2 * (2 * (n : ℤ) - 5) * ((n : ℤ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a271217
