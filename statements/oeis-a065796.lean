import Mathlib

/-!
# Infinitely many omitted signed values in OEIS A065796

Source: https://oeis.org/A065796
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A065/A065796.seq
Credit: @Heart-galaxy

A065796 is the signed alternating sum of decimal digits of n^2, with offset 1.
The least significant digit has positive sign, as in the source formula and
the example a(18)=4-2+3=5. Nat.digits returns digits in exactly that order.

Wilson conjectured on December 10, 2001 that infinitely many signed integer
values are omitted. Israel proved this in the OEIS entry on October 24, 2017:
a(n) is congruent to n^2 modulo 11, so every integer congruent to 2 modulo 11
(and several other residue classes) is omitted. We state the known conjecture
itself, retaining the positive index domain and signed integer codomain.
-/

namespace OMA.S_oeis_a065796

def alternatingSum : List ℕ → ℤ
  | [] => 0
  | d :: ds => (d : ℤ) - alternatingSum ds

def a (n : ℕ) : ℤ := alternatingSum (Nat.digits 10 (n ^ 2))


theorem main : Set.Infinite {z : ℤ | ∀ n : ℕ, 1 ≤ n → a n ≠ z} := by
  sorry

end OMA.S_oeis_a065796
