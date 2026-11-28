import Mathlib

/-!
# A211924, almost-injective colorings of a lower triangle

With T=n(n+1)/2 cells, the required color T−2 forces at least T−1
distinct colors because colors are introduced in order. The only possibilities
are the unique all-distinct coloring and a coloring with a single repeated
pair. Each possible repeated pair fixes one actual coloring by first occurrence.
It is allowed exactly when its two cells are nonadjacent. Coordinates are
(row,column), increasing down and right. An antidiagonal step goes down-left.
For n=1 the requested color is −1, which cannot occur.

The generating function is stated after multiplying by its denominator.
Index zero has coefficient zero because the OEIS sequence starts at one.

Source: https://oeis.org/A211924
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a211924

abbrev Cell := ℕ × ℕ

def cells (n : ℕ) : Finset Cell :=
  (Finset.range n).biUnion fun r => (Finset.range (r+1)).image fun c => (r,c)

abbrev earlier (a b : Cell) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)
abbrev neighbor (a b : Cell) : Prop := (a.1 = b.1 ∧ b.2 = a.2+1) ∨
  (b.1 = a.1+1 ∧ (b.2 = a.2 ∨ a.2 = b.2+1))

def repeatedPairs (n : ℕ) : Finset (Cell × Cell) :=
  ((cells n).product (cells n)).filter fun ab => earlier ab.1 ab.2 ∧ ¬ neighbor ab.1 ab.2

def sequence (n : ℕ) : ℤ := if n < 2 then 0 else 1 + ((repeatedPairs n).card : ℤ)

def lag (d n : ℕ) : ℤ := if d ≤ n then sequence (n-d) else 0
def numerator (n : ℕ) : ℤ := if n = 2 then 2 else if n = 3 then -1 else if n = 4 then 6 else if n = 5 then -5 else if n = 6 then 1 else 0

theorem main :
    (∀ n : ℕ, lag 0 n - 5*lag 1 n + 10*lag 2 n - 10*lag 3 n + 5*lag 4 n - lag 5 n = numerator n) ∧
    (∀ k : ℕ, sequence (k+7) = 6*sequence (k+6) - 15*sequence (k+5) + 20*sequence (k+4) - 15*sequence (k+3) + 6*sequence (k+2) - sequence (k+1)) := by
  sorry

end OMA.S_oeis_a211924
