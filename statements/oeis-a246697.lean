import Mathlib

/-!
# A246697: Row sums of the triangular array A246696.

Source: https://oeis.org/A246697
Credit: @JeremyDevs

Formalizes two conjectures recorded in the FORMULA section of OEIS A246697:
* Conjecture: a(n) = (2*n^3+6*n^2+9*n+4+n*(-1)^n)/4. (Luce ETIENNE, Oct 16 2016)
* Conjectured linear recurrence: a(n) = 2*a(n-1) + a(n-2) - 4*a(n-3) + a(n-4) + 2*a(n-5) - a(n-6),
  with a(0) = 1, a(1) = 5, a(2) = 16, a(3) = 34, a(4) = 67, a(5) = 111, a(6) = 178.

Conventions:
* A246696 is the triangle t(n,k), n >= 0, 0 <= k <= n, defined by its name:
  t(n,k) = t(n,k-2) + 2 if n > 1 and 2 <= k <= n; t(0,0) = 1, t(1,0) = 2, t(1,1) = 3;
  if n > 1 is odd, then t(n,0) = t(n-1,n-2) + 2 and t(n,1) = t(n-1,n-1) + 2;
  if n > 1 is even, then t(n,0) = t(n-1,n-1) + 2 and t(n,1) = t(n-1,n-2) + 2.
  Rows: 1; 2,3; 5,4,7; 6,9,8,11; 13,10,15,12,17; ...
  `row x0 x1` is the rule t(n,k) = t(n,k-2) + 2 started from the two values x0 = t(n,0) and
  x1 = t(n,1), and `t n` is row n of the triangle. For n >= 2 the rule t(n,k) = t(n,k-2) + 2 is
  applied for every k >= 2, and rows 0 and 1 are also given values for k > n; these values
  outside the triangle (k > n) are never used by the rules above nor by the row sums.
* The sequence has offset 0 and a(n) = Sum_{k=0..n} t(n,k); data 1, 5, 16, 34, 67, 111, 178, ...
* The closed form is stated multiplied out, as 4*a(n) = 2*n^3+6*n^2+9*n+4+n*(-1)^n in the
  integers, for every n >= 0 (so no division is involved).
* The source gives no range for the recurrence. It needs n >= 6 for the indices to be natural
  numbers, and it is asserted for every n >= 6; the listed initial terms a(0), ..., a(6) are
  consistent with it (for n = 6 it reads 178 = 222 + 67 - 136 + 16 + 10 - 1).
* The generating function (1 + 3*x + 5*x^2 + x^3 + 2*x^4)/((x - 1)^4*(x + 1)^2) and the
  exponential generating function conjectured in the same section are not stated separately:
  given the initial terms, the first is the same assertion as the recurrence, and the second is
  the exponential generating function of the closed form.
-/

namespace OMA.S_oeis_a246697

/-- A row of the triangle from its first two entries: the rule t(n,k) = t(n,k-2) + 2. -/
def row (x0 x1 : ℤ) : ℕ → ℤ
  | 0 => x0
  | 1 => x1
  | k + 2 => row x0 x1 k + 2

/-- A246696: t(0,0) = 1; t(1,0) = 2, t(1,1) = 3; for n > 1, t(n,k) = t(n,k-2) + 2 for k >= 2,
and t(n,0) = t(n-1,n-2) + 2, t(n,1) = t(n-1,n-1) + 2 if n is odd,
t(n,0) = t(n-1,n-1) + 2, t(n,1) = t(n-1,n-2) + 2 if n is even. -/
def t : ℕ → ℕ → ℤ
  | 0 => fun _ => 1
  | 1 => fun k => if k = 0 then 2 else 3
  | n + 2 =>
    row (if (n + 2) % 2 = 1 then t (n + 1) n + 2 else t (n + 1) (n + 1) + 2)
      (if (n + 2) % 2 = 1 then t (n + 1) (n + 1) + 2 else t (n + 1) n + 2)

/-- A246697 (offset 0): the row sums a(n) = Sum_{k=0..n} t(n,k). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), t n k

/-- The conjectured closed form 4*a(n) = 2n^3 + 6n^2 + 9n + 4 + n*(-1)^n for every n >= 0, and
the conjectured recurrence a(n) = 2a(n-1) + a(n-2) - 4a(n-3) + a(n-4) + 2a(n-5) - a(n-6) for
every n >= 6. -/
theorem main :
    (∀ n : ℕ, 4 * a n = 2 * (n : ℤ) ^ 3 + 6 * (n : ℤ) ^ 2 + 9 * (n : ℤ) + 4 + (n : ℤ) * (-1) ^ n)
    ∧ (∀ n : ℕ, 6 ≤ n →
      a n = 2 * a (n - 1) + a (n - 2) - 4 * a (n - 3) + a (n - 4) + 2 * a (n - 5)
        - a (n - 6)) := by
  sorry

end OMA.S_oeis_a246697
