import Mathlib

/-!
# A059133: A hierarchical sequence (S(W2{2}c) - see A059126).

Source: https://oeis.org/A059133
Credit: @rickmanelius

Conjectures from Colin Barker, Oct 07 2015: a(n) = 4*(-4+5*2^n)-6*n. a(n) = 4*a(n-1)-5*a(n-2)+2*a(n-3)
for n>2. G.f.: -2*(x+2) / ((x-1)^2*(2*x-1)).

Formalization notes:
* The definitions follow the file Hierarchical sequences by Jonas Wallgren, linked from A059126 and
  A059133. The starting point W1 is the ruler sequence A001511: A001511(k), for k ≥ 1, is the
  2-adic valuation of 2k, written padicValNat 2 k + 1.
* W2{2} (A059126) is the sequence of height-2 phrases (1,2,1),(3,4,3),(1,2,1),(5,6,5),...: every
  2nd element is 1,2,1, every 4th element is 3,4,3, and so on, so its k-th element (k ≥ 1) is the
  phrase (2m-1, 2m, 2m-1) with m = A001511(k). This agrees with the formula
  a(3n+1) = 2*A001511(1+n) of A059126 and with its listed terms.
* W2{2}c (A059132) is the collapsed sequence: each phrase is replaced by the sum of its elements,
  giving 4, 10, 4, 16, 4, 10, 4, 22, ... as listed in A059132.
* S(x) is the sequence whose n-th term is the sum of the first 2^n - 1 elements of x. A059133
  has offset 0 and a(0) = 4 is the sum of the first phrase (1,2,1) (comment of Charlie Neder in
  the entry; Wallgren counts from 1), so a(n) is the sum of the first 2^(n+1) - 1 elements of
  W2{2}c. These definitions reproduce the listed terms 4, 18, 52, 126, 280, ... up to n = 24
  (checked by computer).
* The closed form and the recurrence are stated over the integers (the closed form has a negative
  term, the recurrence a subtraction). The recurrence is stated for every n > 2, as in the source.
* The g.f. is the formal power series A(x), the sum of a(n) x^n over n ≥ 0 (the offset). The
  conjectured A(x) = -2*(x+2) / ((x-1)^2*(2*x-1)) is stated as (x-1)^2*(2*x-1)*A(x) = -2*(x+2) in
  the integer power series ring; this is equivalent since (x-1)^2*(2*x-1) has constant
  coefficient -1, a unit.
-/

namespace OMA.S_oeis_a059133

/-- A001511(k) for k ≥ 1: the 2-adic valuation of 2k. -/
def A001511 (k : ℕ) : ℕ := padicValNat 2 k + 1

/-- The k-th element (k ≥ 1) of W2{2}: the height-2 phrase (2m-1, 2m, 2m-1), m = A001511(k). -/
def phrase (k : ℕ) : List ℕ := [2 * A001511 k - 1, 2 * A001511 k, 2 * A001511 k - 1]

/-- W2{2}c: the k-th term (k ≥ 1) is the sum of the elements of the k-th phrase. -/
def W2c (k : ℕ) : ℕ := (phrase k).sum

/-- S(x)(n): the sum of the first 2^n - 1 elements x(1), ..., x(2^n - 1) of x. -/
def S (x : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range (2 ^ n - 1), x (i + 1)

/-- A059133(n), offset 0: S(W2{2}c), with a(0) = 4 the sum of the first phrase. -/
def a (n : ℕ) : ℕ := S W2c (n + 1)

/-- The conjectures of Colin Barker: the closed form, the recurrence for n > 2, and the g.f. -/
theorem main :
    (∀ n : ℕ, (a n : ℤ) = 4 * (-4 + 5 * 2 ^ n) - 6 * n) ∧
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3)) ∧
    ((PowerSeries.X - 1) ^ 2 * (2 * PowerSeries.X - 1) * PowerSeries.mk (fun n => (a n : ℤ)) =
      -2 * (PowerSeries.X + 2)) := by
  sorry

end OMA.S_oeis_a059133
