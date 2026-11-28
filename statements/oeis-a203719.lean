import Mathlib

/-!
# OEIS A203719

Source: https://oeis.org/A203719 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Haruzame0

Hasler's enumeration: scan n = 0, 1, 2, ... and emit floor(n^2 / 5) whenever that
value is a perfect square. These are the squares which, written in base 5, remain
squares after one digit is appended. The sequence keeps repeats, so the three ways
to append a digit to 0 and obtain a square give the three leading zeros.

Colin Barker conjectured that a(n) = 323*a(n-4) - 323*a(n-8) + a(n-12) for n > 13.
`term n` is that 1-based a(n).
-/

namespace OMA.S_oeis_a203719

def good (n : ℕ) : Prop := ∃ t : ℕ, t * t = n * n / 5

noncomputable def term (n : ℕ) : ℕ :=
  let m := Nat.nth good (n - 1)
  m * m / 5

theorem main : ∀ n : ℕ, 13 < n →
    (term n : ℤ) =
      323 * (term (n - 4) : ℤ) - 323 * (term (n - 8) : ℤ) + (term (n - 12) : ℤ) := by
  sorry

end OMA.S_oeis_a203719
