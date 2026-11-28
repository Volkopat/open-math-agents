import Mathlib

/-!
# A059145: A hierarchical sequence (S(W3{2,2}*cc) - see A059126)

Source: https://oeis.org/A059145
Credit: @ivillar

Status: open conjecture in the OEIS entry. The closed form, the recurrence and the g.f. are
all listed as Conjectures from Colin Barker (Oct 07 2015); all three are stated here.

Conjectures (Colin Barker, Oct 07 2015):
  a(n) = 3*(-11 + 2^(4+n) - 3*n).
  a(n) = 4*a(n-1) - 5*a(n-2) + 2*a(n-3) for n > 2.
  G.f.: 3*(2*x-5) / ((x-1)^2*(2*x-1)).
Data (offset 0): 15, 54, 141, 324, 699, 1458, 2985, 6048, 12183, ...

Definitions, from J. Wallgren's description of hierarchical sequences (linked from A059126),
read off the related entries A059131, A059143 and A059144:
* A001511(k) = 1 + (2-adic valuation of k), for k >= 1.
* W3{2,2}* = A059131 = 1,2,1,2,3,2,1,2,1, 2,3,2,3,4,3,2,3,2, 1,2,1,2,3,2,1,2,1, 3,4,3,... is the
  concatenation, for k = 1, 2, 3, ..., of the height-3 elements
  ((h, h+1, h), (h+1, h+2, h+1), (h, h+1, h)) with h = A001511(k).
* Xc (collapsed) replaces each innermost phrase by the sum of its terms, so W3{2,2}*c = A059143
  = 4,7,4,7,10,7,4,7,4,... and W3{2,2}*cc = A059144 = 15,24,15,33,15,24,15,42,... replaces the
  k-th element by the sum of its nine entries.
* S(x)[n] is the sum of the first 2^n - 1 terms of x (the length of a phrase). With the entry's
  offset 0, a(0) = 15 and a(1) = 15 + 24 + 15 = 54, so a(n) here is the sum of the first
  2^(n+1) - 1 terms of W3{2,2}*cc. With these definitions a(0), ..., a(12) agree with the data.

Formalization notes: the closed form and the recurrence (n >= 3, offset 0) are stated in ℤ; the
g.f. is stated over ℚ, cross-multiplied by the denominator (x-1)^2*(2x-1).
-/

namespace OMA.S_oeis_a059145

open PowerSeries

/-- A001511(k) for k ≥ 1: one more than the 2-adic valuation of k. -/
def ruler (k : ℕ) : ℕ := padicValNat 2 k + 1

/-- The k-th element (k ≥ 1) of W3{2,2}* (A059131), as a list of its three innermost phrases. -/
def element (k : ℕ) : List (List ℕ) :=
  [[ruler k, ruler k + 1, ruler k], [ruler k + 1, ruler k + 2, ruler k + 1],
    [ruler k, ruler k + 1, ruler k]]

/-- The k-th term (k ≥ 1) of W3{2,2}*cc (A059144): the sum of the entries of the k-th element. -/
def collapsed2 (k : ℕ) : ℕ := ((element k).map List.sum).sum

/-- A059145, offset 0: the sum of the first 2^(n+1) - 1 terms of W3{2,2}*cc. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 ^ (n + 1) - 1), collapsed2 (k + 1)

/-- Colin Barker's conjectured closed form, recurrence and generating function for A059145. -/
theorem main :
    (∀ n : ℕ, (a n : ℤ) = 3 * (-11 + 2 ^ (4 + n) - 3 * n)) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (2 * X - 1)) = 3 * (2 * X - 5) := by
  sorry

end OMA.S_oeis_a059145
