import Mathlib

/-!
# Fixed points of the octal Kaprekar map

Reorder the base-eight digits in descending and ascending order and subtract
the second number from the first. Leading zeros in the ascending word
contribute zero to its value. The integer zero has one octal digit.
The sequence, indexed from one, counts fixed points of each digit length.

The generating function is stated coefficientwise. Multiplying both
displayed polynomials by -1 gives a denominator with constant term 1.

Sources: https://oeis.org/A165105 and https://oeis.org/A165090
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a165105

def digits (m : ℕ) : List ℕ := if m = 0 then [0] else Nat.digits 8 m

def kaprekar (m : ℕ) : ℕ :=
  let sorted := (digits m).insertionSort (· ≤ ·)
  Nat.ofDigits 8 sorted - Nat.ofDigits 8 sorted.reverse

def a (n : ℕ) : ℤ :=
  Int.ofNat (((Finset.range (8^n)).filter
    (fun m => (digits m).length = n ∧ kaprekar m = m)).card)

def lag (n d : ℕ) : ℤ := if d < n then a (n-d) else 0

def numerator (n : ℕ) : ℤ :=
  ([0,1,1,1,0,-1,1,0,0,-1,0,0,0,0,0,1] : List ℤ).getD n 0

theorem main :
    (∀ n : ℕ, 15 < n → a n = -a (n-1) + a (n-3) + 2*a (n-4) +
      2*a (n-5) + a (n-6) - a (n-7) - 2*a (n-8) - 2*a (n-9) -
      a (n-10) + a (n-12) + a (n-13)) ∧
    (∀ n : ℕ, lag n 0 + lag n 1 - lag n 3 - 2*lag n 4 - 2*lag n 5 -
      lag n 6 + lag n 7 + 2*lag n 8 + 2*lag n 9 + lag n 10 -
      lag n 12 - lag n 13 = numerator n) := by
  sorry

end OMA.S_oeis_a165105
