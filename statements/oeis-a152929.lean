import Mathlib

/-!
# A152929: Weidmann's Fibonacci-Lucas formula

Source: https://oeis.org/A152929
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there. It follows
from the linear recurrence recorded in the entry, which is used as the definition here.

A152929 (offset 1): number of sets (in the Hausdorff metric geometry) at each location between two
sets defining a polygonal configuration consisting of two 4-gonal polygonal components chained with
string components of length l as l varies;
data 113, 176, 289, 465, 754, 1219, 1973, 3192, 5165, 8357, 13522, 21879, 35401, 57280, ...

Conjecture (Philipp Emanuel Weidmann): a(n) = (163*A000045(n)+63*A000032(n))/2,
where A000045 are the Fibonacci numbers and A000032 the Lucas numbers.

Formalization: the entry records the recurrence a(n) = a(n-1) + a(n-2) for n > 2 (Colin Barker,
Aug 05 2020; the entry is indexed as a linear recurrence with signature (1,1)) with a(1) = 113 and
a(2) = 176, and this recurrence is the definition of a(n) used here; the value a 0 = 0 lies outside
the offset and is not used. The Lucas numbers are defined by L(0) = 2, L(1) = 1,
L(n) = L(n-1) + L(n-2). The formula is stated without division, as 2*a(n) = 163*F(n) + 63*L(n),
for n ≥ 1; for example at n = 1: 2*113 = 163*1 + 63*1.
-/

namespace OMA.S_oeis_a152929

/-- a(1) = 113, a(2) = 176, a(n) = a(n-1) + a(n-2) for n > 2, as recorded in the entry. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 113
  | 2 => 176
  | (n + 3) => a (n + 2) + a (n + 1)

/-- The Lucas numbers A000032. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

/-- Weidmann's conjectured formula for A152929, cleared of the division by 2. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    2 * a n = 163 * (Nat.fib n : ℤ) + 63 * lucas n := by
  sorry

end OMA.S_oeis_a152929
