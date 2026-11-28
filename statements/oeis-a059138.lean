import Mathlib

/-!
# A059138: A hierarchical sequence (S(W3{2,2}cc) - see A059126)

Source: https://oeis.org/A059138
Credit: @ivillar

Status: open conjecture in the OEIS entry. The closed form, the recurrence and the g.f. are
all listed as Conjectures from Colin Barker (Oct 07 2015); all three are stated here.

Conjectures (Colin Barker, Oct 07 2015):
  a(n) = 18*(-5 + 3*2^(1+n) - 2*n) = 18*A050488(n+1).
  a(n) = 4*a(n-1) - 5*a(n-2) + 2*a(n-3) for n>2.
  G.f.: -18*(x+1) / ((x-1)^2*(2*x-1)).
Data (offset 0): 18, 90, 270, 666, 1494, 3186, 6606, 13482, 27270, ...

Definitions, from J. Wallgren's description of hierarchical sequences (linked from A059126),
read off the related entries A059128, A059136 and A059137:
* A001511(k) = 1 + (2-adic valuation of k), for k >= 1.
* W3{2,2} = A059128 = 1,2,1,3,4,3,1,2,1, 5,6,5,7,8,7,5,6,5, 1,2,1,3,4,3,1,2,1, 9,... is the
  concatenation, for k = 1, 2, 3, ..., of the height-3 elements
  ((b, b+1, b), (b+2, b+3, b+2), (b, b+1, b)) with b = 4*(A001511(k) - 1) + 1.
* Xc (collapsed) replaces each innermost phrase by the sum of its terms, so W3{2,2}c = A059136
  = 4,10,4,16,22,16,4,10,4,... and W3{2,2}cc = A059137 = 18,54,18,90,18,54,18,126,...
  replaces the k-th element by the sum of its nine entries.
* S(x)[n] is the sum of the first 2^n - 1 terms of x (the length of a phrase). With the entry's
  offset 0, a(0) = 18 and a(1) = 18 + 54 + 18 = 90, so a(n) here is the sum of the first
  2^(n+1) - 1 terms of W3{2,2}cc. With these definitions a(0), ..., a(15) agree with the data.

Formalization notes: the closed form and the recurrence (n >= 3, offset 0) are stated in ℤ; the
g.f. is stated over ℚ, cross-multiplied by the denominator (x-1)^2*(2x-1).
-/

namespace OMA.S_oeis_a059138

open PowerSeries

/-- A001511(k) for k ≥ 1: one more than the 2-adic valuation of k. -/
def ruler (k : ℕ) : ℕ := padicValNat 2 k + 1

/-- The k-th element (k ≥ 1) of W3{2,2} (A059128), as a list of its three innermost phrases. -/
def element (k : ℕ) : List (List ℕ) :=
  let b := 4 * (ruler k - 1) + 1
  [[b, b + 1, b], [b + 2, b + 3, b + 2], [b, b + 1, b]]

/-- The k-th term (k ≥ 1) of W3{2,2}cc (A059137): the sum of the entries of the k-th element. -/
def collapsed2 (k : ℕ) : ℕ := ((element k).map List.sum).sum

/-- A059138, offset 0: the sum of the first 2^(n+1) - 1 terms of W3{2,2}cc. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 ^ (n + 1) - 1), collapsed2 (k + 1)

/-- Colin Barker's conjectured closed form, recurrence and generating function for A059138. -/
theorem main :
    (∀ n : ℕ, (a n : ℤ) = 18 * (-5 + 3 * 2 ^ (1 + n) - 2 * n)) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (2 * X - 1)) = -18 * (X + 1) := by
  sorry

end OMA.S_oeis_a059138
