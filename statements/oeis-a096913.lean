import Mathlib

/-!
# A096913: Numbers k such that (largest digit of k)^(smallest digit of k) + k is a square.

Source: https://oeis.org/A096913
Credit: @darealpandaboi

Conjecture: 0 and 3844 are the only squares in this sequence.

Translation notes.
* The decimal digits of k are Nat.digits 10 k, except that 0 has the single digit 0
  (Nat.digits 10 0 is empty). For 0 this gives 0^0 + 0 = 1, a square, so 0 is a term (a(1) = 0).
* This reproduces the listed data (checked by computer). Among squares k = r^2 with r < 40000
  only 0 and 3844 = 62^2 are terms (8^3 + 3844 = 4356 = 66^2).
-/

namespace OMA.S_oeis_a096913

/-- The decimal digits of k, with 0 having the single digit 0. -/
def ds (k : ℕ) : List ℕ := if k = 0 then [0] else Nat.digits 10 k

/-- k is a term: (largest digit)^(smallest digit) + k is a perfect square. -/
def IsTerm (k : ℕ) : Prop :=
  IsSquare ((ds k).foldr max 0 ^ (ds k).foldr min 9 + k)

theorem main : {k : ℕ | IsSquare k ∧ IsTerm k} = {0, 3844} := by
  sorry

end OMA.S_oeis_a096913
