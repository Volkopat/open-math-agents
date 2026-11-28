import Mathlib

/-!
# A230299: Define a sequence b_s by b_s(1)=s, b_s(k+1)=b_s(k)+(sum of digits of b_s(k)); a(n) is the number of steps needed for b_n to reach a term in one of b_0, b_1, b_3 or b_9, or a(n) = -1 if b_n never joins one of these four sequences.

Source: https://oeis.org/A230299
Credit: @keiichisince1986-bot

A230299 is the sequence `a(n)` named in the title. The entry states:
We conjecture that a(n) is never -1.

Conventions:
- `digitAdd x = x + (sum of the decimal digits of x)`, so `b_s(k) = digitAdd^[k - 1] s`.
- `a(n) ≠ -1` means that some term of `b_n` equals some term of one of `b_0, b_1, b_3, b_9`:
  `digitAdd^[i] n = digitAdd^[j] s` for some `i, j` and some `s ∈ {0, 1, 3, 9}`. (`b_0` is constantly
  `0`, so it is joined only by `b_0` itself.)
-/

namespace OMA.S_oeis_a230299

/-- One step of the sequences `b_s`: add the sum of the decimal digits. -/
def digitAdd (x : ℕ) : ℕ := x + (Nat.digits 10 x).sum

theorem main :
    ∀ n : ℕ, ∃ s ∈ ({0, 1, 3, 9} : Finset ℕ), ∃ i j : ℕ, digitAdd^[i] n = digitAdd^[j] s := by
  sorry

end OMA.S_oeis_a230299
