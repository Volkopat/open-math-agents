import Mathlib

/-!
# A059158: A hierarchical sequence (S(W'3{2,2}cc) - see A059126).

Source: https://oeis.org/A059158
Credit: @rtflynn

In the formula section of A059158:
  a(n) = (24/7) * (8*16^n - 2^n) (conjectured). - Ralf Stephan, May 05 2004
  Conjectures from Colin Barker, Oct 07 2015: a(n) = 18*a(n-1) - 32*a(n-2) for n > 1.
  G.f.: 24 / ((2*x-1)*(16*x-1)).
This file states all three parts: the closed form (over ℚ), the recurrence for n ≥ 2 (offset 0),
and the g.f. as an identity of formal power series over ℚ,
(∑_{n ≥ 0} a(n) X^n) * (2X-1)(16X-1) = 24.

Definitions, from Jonas Wallgren's note "Remarks on Hierarchical Sequences" (linked from A059126):
* W1 = A001511 = 1,2,1,3,1,2,1,4,...; its k-th term (k ≥ 1) is 1 + the 2-adic valuation of k.
* W3{2,2} = A059128 = ((1,2,1),(3,4,3),(1,2,1)),((5,6,5),(7,8,7),(5,6,5)),((1,2,1),...),...:
  its k-th element (k ≥ 1) is ((b,b+1,b),(b+2,b+3,b+2),(b,b+1,b)), where b is the first number
  not used before, b = 4*(A001511(k) - 1) + 1.
* The W' sequences use consecutive powers of 2 instead of consecutive integers (W'1 = A006519),
  i.e. each integer i becomes 2^(i-1): W'3{2,2} = A059148 =
  ((1,2,1),(4,8,4),(1,2,1)),((16,32,16),(64,128,64),(16,32,16)),...
* Xc ("collapsed") replaces each innermost phrase by the sum of its elements; Xcc does it twice,
  so the k-th term of W'3{2,2}cc (A059157) is the sum of all numbers in the k-th element:
  24, 384, 24, 6144, ...
* S(x)[n] is the sum of the first 2^n - 1 terms of x (the length of a phrase). The entry has
  offset 0 with a(0) = 24, a(1) = 24+384+24 = 432, so a(n) here is the sum of the first
  2^(n+1) - 1 terms of W'3{2,2}cc. With these definitions a(0), ..., a(15) agree with the entry.
-/

namespace OMA.S_oeis_a059158

open PowerSeries

/-- A001511(k) for k ≥ 1: one more than the 2-adic valuation of k. -/
def ruler (k : ℕ) : ℕ := padicValNat 2 k + 1

/-- The k-th element (k ≥ 1) of W3{2,2} (A059128), with b = 4*(A001511(k) - 1) + 1. -/
def element (k : ℕ) : List (List ℕ) :=
  let b := 4 * (ruler k - 1) + 1
  [[b, b + 1, b], [b + 2, b + 3, b + 2], [b, b + 1, b]]

/-- The k-th element of W'3{2,2} (A059148): each integer i of W3{2,2} becomes 2^(i-1). -/
def element' (k : ℕ) : List (List ℕ) := (element k).map (List.map fun i => 2 ^ (i - 1))

/-- The k-th term (k ≥ 1) of W'3{2,2}cc (A059157): collapse twice (sum everything). -/
def collapsed2 (k : ℕ) : ℕ := ((element' k).map List.sum).sum

/-- A059158, offset 0: the sum of the first 2^(n+1) - 1 terms of W'3{2,2}cc. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 ^ (n + 1) - 1), collapsed2 (k + 1)

/-- Stephan's and Barker's conjectures: closed form, recurrence and g.f. -/
theorem main :
    (∀ n : ℕ, (a n : ℚ) = 24 / 7 * (8 * 16 ^ n - 2 ^ n)) ∧
    (∀ n : ℕ, 2 ≤ n → (a n : ℤ) = 18 * a (n - 1) - 32 * a (n - 2)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((2 * X - 1) * (16 * X - 1)) = 24 := by
  sorry

end OMA.S_oeis_a059158
