import Mathlib

/-!
# OEIS A045740: Mathar's recurrence

Source: https://oeis.org/A045740 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Emeric Deutsch), offset 1: Number of components in all forests on nodes on a circle. Data: 1, 3, 12,
62, 370, 2397, 16345, 115376, 834786, 6152285, 45990120, 347673108, ... The formula section states:
Sum(k*binomial(n, k-1)*binomial(3*n-2*k-1, n-k)/(2*n-k), k=1..n), and: Conjecture D-finite with recurrence
-2*(n-1)*(2*n-1) *(7912210314*n^2 +24034951267*n -109031255382)*a(n) +2*(-15824420628*n^4 +759853283620*n^3
-1653756416501*n^2 -3170366114943*n +6074871939666) *a(n-1) +2*(1171007126472*n^4 -5580539787848*n^3
-21281457754861*n^2 +151349953543323*n -205322404158756) *a(n-2) +(530118091038*n^4 -3085109917817*n^3
-8408054715093*n^2 +76142928591932*n -101713943817720) *a(n-3) -15*(n-3)*(n-6) *(23736630942*n^2
+73277266499*n-235582184233)*a(n-4)=0. - R. J. Mathar, Jul 22 2022

Formalization notes:
* The entry describes the sequence by its name and by the formula a(n) = Sum(k*binomial(n,
  k-1)*binomial(3*n-2*k-1, n-k)/(2*n-k), k=1..n); Mathar's Maple program in the entry computes the terms from
  that formula, and the conjecture is about them. `a n` is that formula, as a rational number; for 1 ≤ k ≤ n
  the natural-number subtractions 3n - 2k - 1 and n - k do not truncate, and 2n - k ≥ n > 0.
* The formula reproduces the entry's data a(1..21). The reading of the name is checked as well: for n ≤ 8, a
  brute force over edge sets finds exactly C(n, k-1) C(3n-2k-1, n-k) / (2n-k) forests with k components among
  the forests drawn on n points of a circle with straight noncrossing edges, so the k-th term of the formula
  counts the components of those forests, and the totals 1, 3, 12, 62, 370, 2397, 16345, 115376 are the first
  eight terms.
* The site's excerpt of the conjecture stops after the a(n-3) term; the entry's formula section continues on
  the next line with -15*(n-3)*(n-6)*(23736630942*n^2+73277266499*n-235582184233)*a(n-4)=0, and main states
  the whole recurrence.
* The recurrence is stated in the rationals for every n ≥ 5, the first n for which a(n-4) is a term (offset
  1).
-/

namespace OMA.S_oeis_a045740

/-- A045740(n), by the entry's formula: Sum_{k=1..n} k C(n, k-1) C(3n-2k-1, n-k) / (2n-k). -/
def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n,
    (k : ℚ) * (n.choose (k - 1) : ℚ) * ((3 * n - 2 * k - 1).choose (n - k) : ℚ) / (2 * (n : ℚ) - k)

/-- Mathar's conjectured recurrence. -/
theorem main :
    ∀ n : ℕ, 5 ≤ n →
    -2 * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) *
        (7912210314 * (n : ℚ) ^ 2 + 24034951267 * (n : ℚ) - 109031255382) * a n +
      2 * (-15824420628 * (n : ℚ) ^ 4 + 759853283620 * (n : ℚ) ^ 3 - 1653756416501 * (n : ℚ) ^ 2 -
        3170366114943 * (n : ℚ) + 6074871939666) * a (n - 1) +
      2 * (1171007126472 * (n : ℚ) ^ 4 - 5580539787848 * (n : ℚ) ^ 3 - 21281457754861 * (n : ℚ) ^ 2 +
        151349953543323 * (n : ℚ) - 205322404158756) * a (n - 2) +
      (530118091038 * (n : ℚ) ^ 4 - 3085109917817 * (n : ℚ) ^ 3 - 8408054715093 * (n : ℚ) ^ 2 +
        76142928591932 * (n : ℚ) - 101713943817720) * a (n - 3) -
      15 * ((n : ℚ) - 3) * ((n : ℚ) - 6) *
        (23736630942 * (n : ℚ) ^ 2 + 73277266499 * (n : ℚ) - 235582184233) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a045740
