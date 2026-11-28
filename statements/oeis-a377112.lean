import Mathlib

/-!
# OEIS A377112: every prime divides infinitely many terms, with eventually periodic gaps

Source: https://oeis.org/A377112 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Oct 20 2024), offset 0: a(n) = coefficient of sqrt(6) in the expansion
of (2 + sqrt(2) + sqrt(3))^n. Data: 0, 0, 2, 12, 68, 360, 1878, ...
Comment: Conjecture: every prime divides a(n) for infinitely many n, and if K(p) = (k(1),
k(2),...) is the maximal subsequence of indices n such that p divides a(n), then the difference
sequence of K(p) is eventually periodic; indeed, K(p) is purely periodic for the first 7 primes,
with respective period lengths 6, 5, 18, 28, 16, 14, 35: p = 2: (1, 2, 2, 1, 3, 3), p = 3:
(1, 4, 3, 8, 8).

Formalization notes:
* (2 + sqrt 2 + sqrt 3)^n = c0 + c2 sqrt 2 + c3 sqrt 3 + c6 sqrt 6 with integers c0, c2, c3, c6,
  unique because 1, sqrt 2, sqrt 3, sqrt 6 are linearly independent over the rationals.
  `coeffs n` = (c0, c2, c3, c6) is computed by the multiplication rule: multiplying
  c0 + c2 sqrt 2 + c3 sqrt 3 + c6 sqrt 6 by 2 + sqrt 2 + sqrt 3 gives the vector `step`.
  The proof file proves the real identity (2 + sqrt 2 + sqrt 3)^n = c0 + c2 sqrt 2 + c3 sqrt 3 +
  c6 sqrt 6 for every n, and the data a(0..5) = 0, 0, 2, 12, 68, 360.
* K(p) is the increasing enumeration `Nat.nth` of {n : p divides a(n)} (indexed from 0 instead
  of 1, which does not change the difference sequence). The difference sequence is
  d(i) = K(i+1) - K(i), and eventually periodic means: there are N0 and Q > 0 with
  d(i + Q) = d(i) for all i >= N0.
* The clause after indeed is an illustration with data, not part of the conjecture, and is not
  formalized; its patterns are those of the odd primes 3 and 5 (2 divides every term).
-/

namespace OMA.S_oeis_a377112

/-- Multiplication by 2 + sqrt 2 + sqrt 3 on the coefficient vector (c0, c2, c3, c6) of
c0 + c2 sqrt 2 + c3 sqrt 3 + c6 sqrt 6. -/
def step (v : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (2 * v.1 + 2 * v.2.1 + 3 * v.2.2.1,
   v.1 + 2 * v.2.1 + 3 * v.2.2.2,
   v.1 + 2 * v.2.2.1 + 2 * v.2.2.2,
   v.2.1 + v.2.2.1 + 2 * v.2.2.2)

/-- The coefficient vector of (2 + sqrt 2 + sqrt 3)^n. -/
def coeffs : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (1, 0, 0, 0)
  | n + 1 => step (coeffs n)

/-- A377112(n): the coefficient of sqrt 6 in (2 + sqrt 2 + sqrt 3)^n. -/
def a (n : ℕ) : ℤ := (coeffs n).2.2.2

/-- Kimberling's conjecture: for every prime p, infinitely many n have p dividing a(n), and the
difference sequence of the increasing enumeration of those n is eventually periodic. -/
theorem main : ∀ p : ℕ, p.Prime →
    {n : ℕ | (p : ℤ) ∣ a n}.Infinite ∧
    ∃ N0 Q : ℕ, 0 < Q ∧ ∀ i, N0 ≤ i →
      Nat.nth (fun n => (p : ℤ) ∣ a n) (i + Q + 1) - Nat.nth (fun n => (p : ℤ) ∣ a n) (i + Q) =
      Nat.nth (fun n => (p : ℤ) ∣ a n) (i + 1) - Nat.nth (fun n => (p : ℤ) ∣ a n) i := by
  sorry

end OMA.S_oeis_a377112
