import Mathlib

/-!
# OEIS A185020: Mathar's recurrence for Catalan(n)*A002605(n+1)

Source: https://oeis.org/A185020 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Paul D. Hanna, Dec 26 2012), offset 0: a(n) = A000108(n)*A002605(n+1), where A000108 are the
Catalan numbers. Comment (R. J. Mathar, Oct 08 2016): Conjecture: +n*(n+1)*a(n) -4*n*(2*n-1)*a(n-1)
-8*(2*n-1)*(2*n-3)*a(n-2)=0.
Entry A002605, offset 0: a(n) = 2*(a(n-1) + a(n-2)), a(0) = 0, a(1) = 1.

Formalization notes:
* A000108 is Mathlib's `catalan`; A002605 is `s` below.
* The recurrence has no stated range; it is taken for n >= 2, the indices for which a(n-2) is a
  term. The identity is stated in the integers.
* Controls: the definitions give a(0..5) = 1, 2, 12, 80, 616, 5040, as in the entry.
-/

namespace OMA.S_oeis_a185020

/-- A002605: `s(0) = 0, s(1) = 1, s(n+2) = 2 s(n+1) + 2 s(n)`. -/
def s : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * s (n + 1) + 2 * s n

/-- A185020(n) = Catalan(n) * A002605(n+1). -/
def a (n : ℕ) : ℤ := (catalan n : ℤ) * s (n + 1)

/-- Mathar's conjecture: n(n+1)a(n) - 4n(2n-1)a(n-1) - 8(2n-1)(2n-3)a(n-2) = 0 for n >= 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (n : ℤ) * (n + 1) * a n - 4 * n * (2 * n - 1) * a (n - 1)
      - 8 * (2 * n - 1) * (2 * n - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a185020
