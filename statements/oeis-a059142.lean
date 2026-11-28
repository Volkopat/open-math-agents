import Mathlib

/-!
# A059142: A hierarchical sequence (S(W2{3}*) - see A059126).

Source: https://oeis.org/A059142
Credit: @rtflynn

Colin Barker (Oct 06 2015), in the formula section of A059142:
  Conjectures: a(n) = 4*a(n-1) - 5*a(n-2) + 2*a(n-3) for n > 2. a(n) = (-25 + 9*2^(2+n) - 7*n).
  G.f.: (4*x-11) / ((x-1)^2*(2*x-1)).
This file states all three parts: the recurrence for n ≥ 3 (offset 0), the closed form, and the
g.f. as an identity of formal power series over ℚ, (∑_{n ≥ 0} a(n) X^n) * (X-1)^2 (2X-1) = 4X - 11.

Definitions, from Jonas Wallgren's note "Remarks on Hierarchical Sequences" (linked from A059126):
* W1 = A001511 = 1,2,1,3,1,2,1,4,...; its k-th term (k ≥ 1) is 1 + the 2-adic valuation of k.
* W2{3}* = A059130 = (1,2,1,3,1,2,1),(2,3,2,4,2,3,2),(1,2,1,3,1,2,1),...: its k-th element
  (k ≥ 1) is the height-3 phrase (h, h+1, h, h+2, h, h+1, h) with h = A001511(k).
* S(x)[n] is the sum of the first 2^n - 1 elements of x (the length of a phrase). Wallgren uses
  S only on sequences that are not nested, so here each element (a phrase) contributes the sum of
  its terms (the collapsed sequence W2{3}*c = A059141 = 11,18,11,25,...). The entry has offset 0
  with a(0) = 11, a(1) = 11+18+11 = 40, so a(n) here is the sum of the first 2^(n+1) - 1
  elements of W2{3}*. With these definitions a(0), ..., a(15) agree with the entry.
-/

namespace OMA.S_oeis_a059142

open PowerSeries

/-- A001511(k) for k ≥ 1: one more than the 2-adic valuation of k. -/
def ruler (k : ℕ) : ℕ := padicValNat 2 k + 1

/-- The k-th element (k ≥ 1) of W2{3}* (A059130): the phrase (h, h+1, h, h+2, h, h+1, h) with
h = A001511(k). -/
def phrase (k : ℕ) : List ℕ :=
  [ruler k, ruler k + 1, ruler k, ruler k + 2, ruler k, ruler k + 1, ruler k]

/-- A059142, offset 0: the sum of the terms of the first 2^(n+1) - 1 elements of W2{3}*. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 ^ (n + 1) - 1), (phrase (k + 1)).sum

/-- Barker's conjectures: recurrence, closed form and g.f. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3)) ∧
    (∀ n : ℕ, (a n : ℤ) = -25 + 9 * 2 ^ (2 + n) - 7 * n) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (2 * X - 1)) = 4 * X - 11 := by
  sorry

end OMA.S_oeis_a059142
