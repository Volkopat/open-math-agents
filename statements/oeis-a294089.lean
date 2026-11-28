import Mathlib

/-!
# OEIS A294089: Sun's conjecture that s(n)*sqrt(5)/Pi^(2n) is rational and a(n) is never 0

Source: https://oeis.org/A294089 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Zhi-Wei Sun, Feb 09 2018), offset 1: a(n) = b(n) if b(n) :=
(Sum_{k>=1}(k/5)/k^(2n))*sqrt(5)^(floor((n+1)/2)*floor((n+11)/2)-1)/(24*zeta(2n)) is an integer,
and a(n) = 0 otherwise, where (k/5) is the Legendre symbol. Comment: Conjecture: For each n =
1,2,3,... the number (Sum_{k>=1}(k/5)/k^(2n))*sqrt(5)/Pi^(2n) is rational, where (k/5) is the
Legendre symbol. Moreover, a(n) is a nonzero integer for every positive integer n.

Formalization notes:
* (k/5) is the Legendre symbol modulo 5, taken as a real number, and s(n) is the sum of the series
  Sum_{k>=1} (k/5)/k^(2n) (`tsum`; the series converges absolutely for n >= 1).
* zeta is Mathlib's `riemannZeta`, a function on the complex numbers, so b(n) is computed in C;
  b(n) is an integer when it is the image of an integer.
* The exponent floor((n+1)/2)*floor((n+11)/2)-1 is computed in N with floor division; for n >= 1
  the product is at least 6, so subtracting 1 is exact.
* a(n) is an integer by definition, so a(n) is a nonzero integer exactly when a(n) /= 0, that is,
  when b(n) is a nonzero integer.
* `main` is the conjunction of both sentences of the conjecture.
* Controls: the definitions give a(1..5) = 1, 2, 1407, 1444, 4540261, as in the entry, and the
  values s(1), ..., s(5) quoted in the entry, for example s(1) = (4*Pi^2)/(25*sqrt(5)).
-/

namespace OMA.S_oeis_a294089

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The Legendre symbol `(k/5)`, as a real number. -/
def chi (k : ℕ) : ℝ := (legendreSym 5 (k : ℤ) : ℝ)

/-- `s(n) = Sum_{k>=1} (k/5)/k^(2n)`. -/
noncomputable def s (n : ℕ) : ℝ := ∑' k : ℕ, chi (k + 1) / ((k + 1 : ℕ) : ℝ) ^ (2 * n)

/-- The exponent `floor((n+1)/2)*floor((n+11)/2) - 1` (division of naturals is the floor). -/
def e (n : ℕ) : ℕ := (n + 1) / 2 * ((n + 11) / 2) - 1

/-- `b(n) = s(n) * sqrt(5)^e(n) / (24 * zeta(2n))`. -/
noncomputable def b (n : ℕ) : ℂ :=
  (s n : ℂ) * ((Real.sqrt 5 : ℝ) : ℂ) ^ e n / (24 * riemannZeta (2 * n))

open Classical in
/-- `a(n) = b(n)` if `b(n)` is an integer, and `a(n) = 0` otherwise. -/
noncomputable def a (n : ℕ) : ℤ := if h : ∃ m : ℤ, b n = m then h.choose else 0

/-- Sun's conjecture: s(n)*sqrt(5)/Pi^(2n) is rational for every n >= 1, and a(n) is a nonzero
integer for every n >= 1. -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ q : ℚ, s n * Real.sqrt 5 / Real.pi ^ (2 * n) = q) ∧
    (∀ n : ℕ, 0 < n → a n ≠ 0) := by
  sorry

end OMA.S_oeis_a294089
