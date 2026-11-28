import Mathlib

/-!
# Unlabelled six-color grids with complementary pairs (OEIS A233123)

Orthogonal neighbors may have neither the same color nor colors adding to
five. The upper left cell is zero. In row-major order 1 must precede the
first 2, 3 or 4, and 2 must precede the first 3. Consequently the upper
right cell is 1: the neighbor rule excludes 0 and 5, and the first-use
rule excludes 2, 3 and 4. Later rows track whether 2 has appeared.

Colin Barker (March 2018) conjectured the generating function and the
closed form. At height n+1 his expression is equivalently
6 a(n+1) = 4ⁿ (3ⁿ⁺¹ + 3), including height one.
Source: https://oeis.org/A233123
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a233123
open PowerSeries

abbrev Color := Fin 6
abbrev Row := Color × Color
def colors : List Color := [0,1,2,3,4,5]
def rows : List Row := colors.flatMap fun l => colors.map fun r => (l,r)

def compatible (x y : Color) : Bool := x != y && x.val+y.val != 5
def usesTwo (r : Row) : Bool := r.1 == 2 || r.2 == 2

def legal (seen : Bool) (prev r : Row) : Bool :=
  compatible r.1 r.2 && compatible prev.1 r.1 && compatible prev.2 r.2 &&
    (seen || r.1 != 3) && (seen || r.1 == 2 || r.2 != 3)

def nextRows (seen : Bool) (r : Row) := rows.filter (legal seen r)

def count : ℕ → Row → Bool → ℕ
  | 0, _, _ => 1
  | k+1, r, seen =>
    ((nextRows seen r).map fun s => count k s (seen || usesTwo s)).sum

def a : ℕ → ℕ
  | 0 => 0
  | n+1 => count n (0,1) false

theorem main :
    (∀ n : ℕ, a (n+3)+48*a (n+1)=16*a (n+2)) ∧
    ((1-4*X)*(1-12*X)*(PowerSeries.mk (fun n => (a n : ℚ))) = X*(1-8*X)) ∧
    ∀ n : ℕ, 6*a (n+1) = 4^n*(3^(n+1)+3) := by
  sorry

end OMA.S_oeis_a233123
