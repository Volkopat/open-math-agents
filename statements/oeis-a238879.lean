import Mathlib

/-!
# A238879: Row sums of the triangle of generalized ballot numbers A238762.

Source: https://oeis.org/A238879 (the triangle: https://oeis.org/A238762)
Credit: @agchua

Ralf Stephan (Mar 14 2014), in the formula section of A238879:
  a(2n) = A000108(n), a(2n+1) = A002054(n) (conjectured). - _Ralf Stephan_, Mar 14 2014
This file states the conjecture literally. A238879 has offset 0, A000108 (the Catalan numbers,
Mathlib's catalan) has offset 0, and A002054(m) = binomial(2m+1, m-1) has offset 1, so the second
part is stated for n >= 1. With these offsets the printed indices are one too low against the
entry's own data: a(2) = 2 while A000108(1) = 1, and a(3) = 5 while A002054(1) = 1. The shifted
form a(2n) = A000108(n+1), a(2n+1) = A002054(n+1) fits all 36 listed terms a(0), ..., a(35).

Definition of A238762, from its formula section (notation of Knuth, TAOCP 4a, 7.2.1.6):
  T(0, 0) = 1; T(p, q) = 0 if p < 0 or p > q; T(p, q) = T(p-2, q) + (q mod 2) T(p-1, q-1) + T(p, q-2).
Row q of the triangle is T(0, q), ..., T(q, q), and a(q) is its sum. Below p and q are natural
numbers: a term T(p-2, q) with p < 2 or T(p-1, q-1) with p = 0 has a negative first argument, and a
term T(p, q-2) with q < 2 has p > q-2, so these terms are 0 by the rule above and are written as 0.
-/

namespace OMA.S_oeis_a238879

/-- A238762: the generalized ballot numbers T(p, q), 0 ≤ p ≤ q (and 0 for p > q). -/
def T (p q : ℕ) : ℕ :=
  if p = 0 ∧ q = 0 then 1
  else if q < p then 0
  else (if _h : 2 ≤ p then T (p - 2) q else 0) +
    q % 2 * (if _h : 1 ≤ p then T (p - 1) (q - 1) else 0) +
    (if _h : 2 ≤ q then T p (q - 2) else 0)
termination_by p + q
decreasing_by all_goals omega

/-- A238879: the row sums of A238762. -/
def a (n : ℕ) : ℕ := ∑ p ∈ Finset.range (n + 1), T p n

/-- A002054: binomial(2m+1, m-1), offset 1. -/
def A002054 (m : ℕ) : ℕ := Nat.choose (2 * m + 1) (m - 1)

/-- The conjecture as printed: a(2n) = A000108(n) and a(2n+1) = A002054(n). -/
theorem main : (∀ n : ℕ, a (2 * n) = catalan n) ∧
    (∀ n : ℕ, 1 ≤ n → a (2 * n + 1) = A002054 n) := by
  sorry

end OMA.S_oeis_a238879
