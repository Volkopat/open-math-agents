import Mathlib

/-!
# A107928: a(n) is the numerator of harmonic mean of a(n-1) and a(n-2).

Source: https://oeis.org/A107928
Credit: @jagong-cmu

Definition in the entry: a(1)=2; a(2)=3; n>=3: a(n) = numerator(2*a(n-1)*a(n-2)/(a(n-2)+a(n-1))).

The entry gives (Ralf Stephan, Dec 01 2010):
Conjecture: G.f.: x*(2+3*x+12*x^2+8*x^3+8*x^4)/[(1-2*x)*(1+2*x+4*x^2)].
a(3n) = (3/2)*8^n, a(3n+1) = 3*8^n, a(3n+2) = 2*8^n, for n>0.

Conventions:
* Offset 1, as in the entry (data: 2, 3, 12, 24, 16, 96, 192, 128, ...). The value `a 0 = 0`
  is a placeholder; the recursion never uses it.
* `a n` is an integer, the numerator (`Rat.num`) of the harmonic mean computed in `ℚ`.
* The three closed forms are stated for every `n > 0`, as in the entry. The first one is
  stated in `ℚ`, because of the factor `3/2`; the other two are stated in `ℤ`.
* The g.f. part is not stated, because it is false as printed. The denominator is
  `(1-2x)(1+2x+4x^2) = 1 - 8x^3`, so the g.f. gives a(5) = 8 + 8*a(2) = 32, but a(5) = 16
  (the numerator of 2*24*12/36 = 16). The g.f. disagrees with the closed forms and with the
  data at every a(3n+2) with n >= 1. The closed forms agree with the data.
-/

namespace OMA.S_oeis_a107928

/-- A107928: `a(1) = 2`, `a(2) = 3`, and for `n >= 3`, `a(n)` is the numerator of the
harmonic mean `2*a(n-1)*a(n-2)/(a(n-2)+a(n-1))`. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | (n + 3) => ((2 * a (n + 2) * a (n + 1) : ℚ) / ((a (n + 1) : ℚ) + a (n + 2))).num

/-- For `n > 0`: `a(3n) = (3/2)*8^n`, `a(3n+1) = 3*8^n` and `a(3n+2) = 2*8^n`. -/
theorem main :
    ∀ n : ℕ, 0 < n →
      (a (3 * n) : ℚ) = 3 / 2 * 8 ^ n ∧ a (3 * n + 1) = 3 * 8 ^ n ∧
        a (3 * n + 2) = 2 * 8 ^ n := by
  sorry

end OMA.S_oeis_a107928
