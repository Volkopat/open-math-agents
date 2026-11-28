import Mathlib

/-!
# A247000: maximal number of palindromes in a circular binary word of length n

Source: https://oeis.org/A247000 (conjectures by Colin Barker, Nov 14 2015)

Entry (offset 1): Maximal number of palindromes in a circular binary word of length n.
The word is to be imagined as written around a circle; only palindromes of length m with
1 <= m <= n are counted (entry comment).
Formula section, Conjectures from Colin Barker, Nov 14 2015:
a(n) = a(n-1)+a(n-3)-a(n-4) for n>4.
G.f.: x*(x^13-x^12+x^11-x^10+x^9-x^8+x^7-x^6+x^3+2*x^2+x+1) / ((x-1)^2*(x^2+x+1)).

Formalization notes:
* A binary word of length n is encoded by a number `w < 2^n`: its letters are the bits
  `w.testBit 0, ..., w.testBit (n-1)`; this is a bijection with the 2^n binary words.
* The circular factor of length m starting at position i is the list of letters at positions
  `(i + k) mod n` for `k = 0..m-1`. The palindromes of the circular word are the distinct lists
  among the circular factors of lengths `1..n` (all starting positions `0..n-1`) that equal their
  reverse; a(n) is the maximum of their number over all words of length n. With this reading the
  definition reproduces the entry data 1, 2, 4, 6, 7, 9, 10, 12, 13, 15, 16, 18 for n = 1..12.
* The recurrence is stated with the range n > 4 given in the entry, in the integers.
* With offset 1 the generating function is `A(x) = Sum_(n >= 1) a(n) x^n`, the power series with
  coefficient 0 at `x^0`. Since `(x-1)^2*(x^2+x+1)` has constant term 1, the identity `A = N/D` is
  stated as `A * D = N` in the formal power series ring over the integers.
-/

namespace OMA.S_oeis_a247000

open PowerSeries

/-- The circular factor of length `m` starting at position `i` of the binary word of length `n`
whose letters are the bits of `w`. -/
def factor (n w i m : ℕ) : List Bool := (List.range m).map fun k => w.testBit ((i + k) % n)

/-- The distinct palindromic circular factors of lengths `1..n` of the word `w`. -/
def pals (n w : ℕ) : Finset (List Bool) :=
  ((Finset.range n ×ˢ Finset.Icc 1 n).image fun p => factor n w p.1 p.2).filter
    fun l => l = l.reverse

/-- A247000(n): the maximal number of palindromes over all binary words of length `n`. -/
def a (n : ℕ) : ℕ := (Finset.range (2 ^ n)).sup fun w => (pals n w).card

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 4 < n → (a n : ℤ) = a (n - 1) + a (n - 3) - a (n - 4)) ∧
    mk (fun n => if n = 0 then 0 else (a n : ℤ)) * ((X - 1) ^ 2 * (X ^ 2 + X + 1)) =
      (X * (X ^ 13 - X ^ 12 + X ^ 11 - X ^ 10 + X ^ 9 - X ^ 8 + X ^ 7 - X ^ 6 + X ^ 3 +
        2 * X ^ 2 + X + 1) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a247000
