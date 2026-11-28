import Mathlib

/-!
# OEIS A215230: circular square-free words of length seven
Source: https://oeis.org/A215230
Credit: @etaubman

R. H. Hardin introduced the sequence in 2012. Colin Barker proposed the
generating function and recurrence in 2018. Count a word by its pattern of
equal letters and the ordered list of its distinct actual letters. Number
the classes by first appearance when scanning from the left: having seen r
classes, the next position is any class 0,...,r-1 or the new class r. Thus each
word corresponds uniquely to one pattern and an injection from its classes
into the n+1 letters. The falling factorial counts these injections.
-/

namespace OMA.S_oeis_a215230

/-- All starts and all block lengths from 1 to 6 are tested cyclically. -/
def squarefree7 (w : List ℕ) : Bool :=
  (List.range 7).all fun i =>
    (List.range 6).all fun j =>
      (List.range (j+1)).any fun h =>
        w[(i+h)%7]? != w[(i+h+j+1)%7]?


/-- Count ordinary words over 0,...,n directly, in the positions 0,...,6. -/
noncomputable def count (n : ℕ) : ℤ :=
  (Nat.card {w : List ℕ // w.length = 7 ∧ (∀ c ∈ w, c < n+1) ∧ squarefree7 w = true} : ℤ)


open PowerSeries

theorem main :
    (∀ n : ℕ, count n = (n:ℤ)^7 - 7*(n:ℤ)^5 + 14*(n:ℤ)^3 - 8*(n:ℤ)) ∧
    (∀ n : ℕ, count (n+8) = 8*count (n+7) - 28*count (n+6) + 56*count (n+5) -
      70*count (n+4) + 56*count (n+3) - 28*count (n+2) + 8*count (n+1) - count n) ∧
    (1-X)^8 * mk count = (840*X^3*(1+4*X+X^2) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a215230
