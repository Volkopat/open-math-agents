import Mathlib

/-!
# A188571: the coefficient of sqrt(2) in (1 + sqrt(2) + sqrt(3))^n

Source: https://oeis.org/A188571 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry, offset 0: a(n) = coefficient of sqrt(2) in the expansion of (1 + sqrt(2) + sqrt(3))^n.
Data 0, 1, 2, 14, 48, 224, 880, 3760, 15360, 64192, ...

Comment (Clark Kimberling, Oct 23 2024): Conjecture: every prime divides a(n) for infinitely
many n, and if K(p) = (k(1), k(2),...) is the maximal subsequence of indices n such that p
divides a(n), then the difference sequence of K(p) is eventually periodic.

Formula section: Conjectures from Colin Barker, Jan 08 2013:
a(n) = 4*a(n-1) + 4*a(n-2) - 16*a(n-3) + 8*a(n-4).
G.f.: -x*(2*x^2-2*x+1) / (8*x^4-16*x^3+4*x^2+4*x-1).

Formalization notes.
* Elements of Z[sqrt(2), sqrt(3)] are written in the basis (1, sqrt(2), sqrt(3), sqrt(6)) as
  tuples (c1, c2, c3, c6) of integers, as in `statements/oeis-a188572.lean`. `quadStep` is the
  multiplication by 1 + sqrt(2) + sqrt(3), and `a n` is the sqrt(2)-coordinate of the n-th power.
* `main` states the first claim of Kimberling's conjecture (every prime divides a(n) for
  infinitely many n) and Barker's recurrence, for n >= 4. The claim on the difference sequence
  of K(p) is not stated here. The generating function is the recurrence together with the
  terms a(0..3) = 0, 1, 2, 14.
-/

namespace OMA.S_oeis_a188571

/-- Multiplication by `1 + √2 + √3` in the basis `(1, √2, √3, √6)` of `ℤ[√2, √3]`. -/
def quadStep (v : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (v.1 + 2 * v.2.1 + 3 * v.2.2.1, v.1 + v.2.1 + 3 * v.2.2.2, v.1 + v.2.2.1 + 2 * v.2.2.2,
    v.2.1 + v.2.2.1 + v.2.2.2)

/-- Coordinates of `(1 + √2 + √3)^n` in the basis `(1, √2, √3, √6)`. -/
def quadPow : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (1, 0, 0, 0)
  | n + 1 => quadStep (quadPow n)

/-- A188571: the coefficient of `√2` in `(1 + √2 + √3)^n`. -/
def a (n : ℕ) : ℤ := (quadPow n).2.1

/-- Kimberling's conjecture (first claim) and Barker's recurrence. -/
theorem main :
    (∀ p : ℕ, Nat.Prime p → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (p : ℤ) ∣ a n) ∧
    ∀ n : ℕ, 4 ≤ n → a n = 4 * a (n - 1) + 4 * a (n - 2) - 16 * a (n - 3) + 8 * a (n - 4) := by
  sorry

end OMA.S_oeis_a188571
