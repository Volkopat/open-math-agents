import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

/-!
# OEIS A222777

R. H. Hardin counts n by 2 arrays on 0,...,6 with unequal entries at Manhattan
distance two. Colours are named by their first appearance in row-major order.
Colin Barker proposed the closed form and generating function on August 16,
2018. https://oeis.org/A222777
-/
namespace OMA.S_oeis_a222777

/-- An already introduced, unblocked colour, or the single next new colour. -/
def choices (k : ℕ) (blocked : List ℕ) (f : ℕ → ℕ → ℤ) : ℤ :=
  (∑ c ∈ Finset.range k \ blocked.toFinset, f c k) +
    if k < 7 then f k (k+1) else 0

def remember (c : ℕ) (prev : List ℕ) := c :: prev.take 1

/-- Each cell has the previous two cells of its checkerboard parity as its
only possible forbidden predecessors. These lie diagonally one row back and
vertically two rows back. The left and right parities exchange roles at the
next row. Entries are chosen from left to right before advancing the row. -/
def rows : ℕ → ℕ → List ℕ → List ℕ → ℤ
  | 0, _, _, _ => 1
  | n+1, k, left, right =>
      choices k left (fun c j => choices j right (fun e l =>
        rows n l (remember e right) (remember c left)))

/-- Zero constant coefficient, since the source indexes nonempty strips. -/
def coeff : ℕ → ℤ
  | 0 => 0
  | n+1 => rows (n+1) 0 [] []

def shift (a : ℕ → ℤ) (j m : ℕ) := if j ≤ m then a (m-j) else 0

def numerator : ℕ → ℤ
  | 1 => 2 | 2 => -71 | 3 => 559 | 4 => -667 | 5 => -1779 | 6 => 660 | _ => 0

/-- The denominator expands to 1-39x+399x²-1261x³+900x⁴.
In the closed formula n=t+3; multiplying by four clears its denominators. -/
theorem main :
    (∀ m, coeff m - 39*shift coeff 1 m + 399*shift coeff 2 m
      - 1261*shift coeff 3 m + 900*shift coeff 4 m = numerator m) ∧
    (∀ t, 4*coeff (t+3) = 9 + 4*2^(2*t+3) + 20*3^(2*t+1) + 7*5^(2*t+1)) := by
  sorry
end OMA.S_oeis_a222777
