import Mathlib

/-!
# A212797: Mathar's identities with A001109 and A144133

Source: https://oeis.org/A212797
Credit: @rgoldman73-dev

This states both identities conjectured by R. J. Mathar on April 16, 2018.
All three sequences are represented by established formulas in their source
entries, independently of these conjectured identities:

* A001108 has initial values 0,1 and b(n+2)=6b(n+1)-b(n)+2.
* A001109 has initial values 0,1 and c(n+2)=6c(n+1)-c(n).
* A144133 has initial values 1,12,106,828 and characteristic polynomial
  (x^2-6x+1)^2. Its source gives this recurrence (Munarini, March 7, 2018)
  and identifies it with the Gegenbauer values C_n^2(3).
* A212797(n)=2*n*A001108(n), the entry's nonconjectural formula attributed
  to Seiichi Manyama, January 13, 2021. It starts at n=1.

The first conjectured identity is stated for n>=1, so its least index n-1
exists. The second is stated for n>=3, so all three A144133 indices are
nonnegative. Integers preserve the subtractions exactly.

Sources for the defining recurrences: https://oeis.org/A001108,
https://oeis.org/A001109, https://oeis.org/A144133.
-/

namespace OMA.S_oeis_a212797

def squareTriIndex : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n+2 => 6*squareTriIndex (n+1) - squareTriIndex n + 2

def c : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n+2 => 6*c (n+1) - c n

def g : ℕ → ℤ
  | 0 => 1
  | 1 => 12
  | 2 => 106
  | 3 => 828
  | n+4 => 12*g (n+3) - 38*g (n+2) + 12*g (n+1) - g n

def a (n : ℕ) : ℤ := 2*(n : ℤ)*squareTriIndex n

theorem main :
    (∀ n : ℕ, 1 ≤ n →
      a n = 16*c (n+1) + 3*c n - 16*(g n - 6*g (n-1)) - (n : ℤ)) ∧
    (∀ n : ℕ, 3 ≤ n →
      a n = 3*g (n-1) - 2*g (n-2) + 3*g (n-3) - (n : ℤ)) := by
  sorry

end OMA.S_oeis_a212797
