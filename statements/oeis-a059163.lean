import Mathlib

/-!
# A059163: A hierarchical sequence (W'3{2,2}*c - see A059126)

Source: https://oeis.org/A059163
Credit: @ivillar

Status: open conjecture in the OEIS entry (R. J. Mathar, Apr 04 2019):
  Conjecture: a(n) = 2^(1+A059129(n)).
Data (offset 0): 4, 8, 4, 8, 16, 8, 4, 8, 4, 16, 32, 16, 4, 8, 4, 8, 16, 8, 4, 8, 4, 32, 64, 32, ...

Definitions, from J. Wallgren's description of hierarchical sequences (linked from A059126),
read off the related entries A059129, A059131 and A059151:
* A001511(k) = 1 + (2-adic valuation of k), for k >= 1.
* W2{2}* = A059129 = 1,2,1,2,3,2,1,2,1,3,4,3,... (offset 0) is the concatenation, for
  k = 1, 2, 3, ..., of the phrases (h, h+1, h) with h = A001511(k). Its term at n is therefore
  entry n mod 3 of the phrase with k = floor(n/3) + 1.
* W3{2,2}* = A059131 is the concatenation, for k = 1, 2, 3, ..., of the height-3 elements
  ((h, h+1, h), (h+1, h+2, h+1), (h, h+1, h)) with h = A001511(k).
* W'3{2,2}* = A059151 = 1,2,1,2,4,2,1,2,1,2,4,2,4,8,4,... replaces each entry i of W3{2,2}* by
  2^(i-1).
* Xc (collapsed) replaces each innermost phrase by the sum of its terms, so W'3{2,2}*c lists,
  for k = 1, 2, 3, ..., the sums of the three innermost phrases of the k-th element of
  W'3{2,2}*. Its term at n (offset 0) is the sum of phrase n mod 3 of element floor(n/3) + 1,
  in agreement with the formula a(n) = A059151(3n) + A059151(3n+1) + A059151(3n+2) (Sean A.
  Irvine, Sep 13 2022). With these definitions the first 36 terms agree with the data.
-/

namespace OMA.S_oeis_a059163

/-- A001511(k) for k ≥ 1: one more than the 2-adic valuation of k. -/
def ruler (k : ℕ) : ℕ := padicValNat 2 k + 1

/-- The k-th phrase (k ≥ 1) of W2{2}* (A059129): (h, h+1, h) with h = A001511(k). -/
def phrase (k : ℕ) : List ℕ := [ruler k, ruler k + 1, ruler k]

/-- A059129 (W2{2}*), offset 0: entry n mod 3 of the phrase with index floor(n/3) + 1. -/
def A059129 (n : ℕ) : ℕ := (phrase (n / 3 + 1)).getD (n % 3) 0

/-- The k-th element (k ≥ 1) of W3{2,2}* (A059131), as a list of its three innermost phrases. -/
def element (k : ℕ) : List (List ℕ) :=
  [[ruler k, ruler k + 1, ruler k], [ruler k + 1, ruler k + 2, ruler k + 1],
    [ruler k, ruler k + 1, ruler k]]

/-- The k-th element of W'3{2,2}* (A059151): each entry i of W3{2,2}* replaced by 2^(i-1). -/
def element' (k : ℕ) : List (List ℕ) := (element k).map (List.map fun i => 2 ^ (i - 1))

/-- A059163 (W'3{2,2}*c), offset 0: the sum of the innermost phrase n mod 3 of the element of
W'3{2,2}* with index floor(n/3) + 1. -/
def a (n : ℕ) : ℕ := ((element' (n / 3 + 1)).map List.sum).getD (n % 3) 0

/-- R. J. Mathar's conjecture: a(n) = 2^(1 + A059129(n)). -/
theorem main : ∀ n : ℕ, a n = 2 ^ (1 + A059129 n) := by
  sorry

end OMA.S_oeis_a059163
