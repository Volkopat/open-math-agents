import Mathlib

/-!
# A059140: A hierarchical sequence (S(W2{2}*c) - see A059126).

Source: https://oeis.org/A059140
Credit: @rtflynn

Colin Barker (Oct 07 2015), in the formula section of A059140:
  Conjectures: a(n) = 2*(-5 + 7*2^n) - 3*n. a(n) = 4*a(n-1) - 5*a(n-2) + 2*a(n-3) for n > 2.
  G.f.: (x-4) / ((x-1)^2*(2*x-1)).
This file states all three parts: the closed form, the recurrence for n ≥ 3 (offset 0), and the
g.f. as an identity of formal power series over ℚ, (∑_{n ≥ 0} a(n) X^n) * (X-1)^2 (2X-1) = X - 4.

Definitions, from Jonas Wallgren's note "Remarks on Hierarchical Sequences" (linked from A059126):
* W1 = A001511 = 1,2,1,3,1,2,1,4,...; its k-th term (k ≥ 1) is 1 + the 2-adic valuation of k.
* W2{2}* = A059129 = (1,2,1),(2,3,2),(1,2,1),(3,4,3),(1,2,1),(2,3,2),(1,2,1),...: its k-th
  element (k ≥ 1) is the height-2 phrase (h, h+1, h) with h = A001511(k).
* Xc ("collapsed") replaces each innermost phrase by the sum of its elements: W2{2}*c = A059139
  = 4,7,4,10,4,7,4,13,...
* S(x)[n] is the sum of the first 2^n - 1 terms of x (the length of a phrase). The entry has
  offset 0 with a(0) = 4, a(1) = 4+7+4 = 15, a(2) = 40, so a(n) here is the sum of the first
  2^(n+1) - 1 terms of W2{2}*c. With these definitions a(0), ..., a(15) agree with the entry.
-/

namespace OMA.S_oeis_a059140

open PowerSeries

/-- A001511(k) for k ≥ 1: one more than the 2-adic valuation of k. -/
def ruler (k : ℕ) : ℕ := padicValNat 2 k + 1

/-- The k-th element (k ≥ 1) of W2{2}* (A059129): the phrase (h, h+1, h) with h = A001511(k). -/
def phrase (k : ℕ) : List ℕ := [ruler k, ruler k + 1, ruler k]

/-- The k-th term (k ≥ 1) of W2{2}*c (A059139): the sum of the k-th phrase. -/
def collapsed (k : ℕ) : ℕ := (phrase k).sum

/-- A059140, offset 0: the sum of the first 2^(n+1) - 1 terms of W2{2}*c. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 ^ (n + 1) - 1), collapsed (k + 1)

/-- Barker's conjectures: closed form, recurrence and g.f. -/
theorem main :
    (∀ n : ℕ, (a n : ℤ) = 2 * (-5 + 7 * 2 ^ n) - 3 * n) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (2 * X - 1)) = X - 4 := by
  sorry

end OMA.S_oeis_a059140
