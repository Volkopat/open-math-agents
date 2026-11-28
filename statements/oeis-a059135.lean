import Mathlib

/-!
# A059135: A hierarchical sequence (S(W2{3}c) - see A059126).

Source: https://oeis.org/A059135
Credit: @rtflynn

Colin Barker (Oct 07 2015), in the formula section of A059135:
  Conjectures: a(n) = -53 + 2^(6+n) - 21*n. a(n) = 4*a(n-1) - 5*a(n-2) + 2*a(n-3) for n > 2.
  G.f.: -(10*x+11) / ((x-1)^2*(2*x-1)).
This file states all three parts: the closed form, the recurrence for n ≥ 3 (offset 0), and the
g.f. as an identity of formal power series over ℚ,
(∑_{n ≥ 0} a(n) X^n) * (X-1)^2 (2X-1) = -(10X + 11).

Definitions, from Jonas Wallgren's note "Remarks on Hierarchical Sequences" (linked from A059126):
* W1 = A001511 = 1,2,1,3,1,2,1,4,...; its k-th term (k ≥ 1) is 1 + the 2-adic valuation of k.
* W2{3} = A059127 = (1,2,1,3,1,2,1),(4,5,4,6,4,5,4),(1,2,1,3,1,2,1),(7,8,7,9,7,8,7),...: its
  k-th element (k ≥ 1) is the height-3 phrase (h, h+1, h, h+2, h, h+1, h), where h is the first
  number not used before, h = 3*(A001511(k) - 1) + 1.
* Xc ("collapsed") replaces each innermost phrase by the sum of its elements: W2{3}c =
  11,32,11,53,...
* S(x)[n] is the sum of the first 2^n - 1 terms of x (the length of a phrase). The entry has
  offset 0 with a(0) = 11, a(1) = 11+32+11 = 54, so a(n) here is the sum of the first
  2^(n+1) - 1 terms of W2{3}c (as in Sean A. Irvine's formula in the entry). With these
  definitions a(0), ..., a(15) agree with the entry.
-/

namespace OMA.S_oeis_a059135

open PowerSeries

/-- A001511(k) for k ≥ 1: one more than the 2-adic valuation of k. -/
def ruler (k : ℕ) : ℕ := padicValNat 2 k + 1

/-- The first term of the k-th element of W2{3}: 3*(A001511(k) - 1) + 1. -/
def base (k : ℕ) : ℕ := 3 * (ruler k - 1) + 1

/-- The k-th element (k ≥ 1) of W2{3} (A059127): the phrase (h, h+1, h, h+2, h, h+1, h). -/
def phrase (k : ℕ) : List ℕ :=
  [base k, base k + 1, base k, base k + 2, base k, base k + 1, base k]

/-- The k-th term (k ≥ 1) of W2{3}c: the sum of the k-th phrase. -/
def collapsed (k : ℕ) : ℕ := (phrase k).sum

/-- A059135, offset 0: the sum of the first 2^(n+1) - 1 terms of W2{3}c. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 ^ (n + 1) - 1), collapsed (k + 1)

/-- Barker's conjectures: closed form, recurrence and g.f. -/
theorem main :
    (∀ n : ℕ, (a n : ℤ) = -53 + 2 ^ (6 + n) - 21 * n) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (2 * X - 1)) = -(10 * X + 11) := by
  sorry

end OMA.S_oeis_a059135
