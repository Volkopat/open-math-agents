import Mathlib

/-!
# OEIS A375948: a recurrence for the e.g.f. 1/(3 - 2*exp(x))^(3/2)

Source: https://oeis.org/A375948 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-sonnet-5-5), submitted by @Genbox.

Entry A375948, offset 0: Expansion of e.g.f. 1 / (3 - 2 * exp(x))^(3/2). Data: 1, 3, 18, 153,
1683, 22698, ... Conjecture (Mikhail Kurkov, Jun 14 2026): a(n) = b(n-1) + 2 * Sum_{j=0..n-1}
binomial(n, j) * a(j) for n > 0 where b(n) = b(n-1) + Sum_{j=0..n-1} binomial(n-1, j) * a(j+1)
for n > 0 with b(0) = 1.

Formalization notes:
* The sequence is characterised by its e.g.f. G(x) = Sum a(n) x^n / n!: G is the power series
  with constant term 1 (the positive branch of the square root) and G^2 * (3 - 2 exp(x))^3 = 1.
  This determines G uniquely, so a is the entry's sequence.
* b is the auxiliary sequence of the conjecture, given by b(0) = 1 and its recurrence for n > 0.
* Controls: the characterisation gives a(0) = 1, a(1) = 3, a(2) = 18, a(3) = 153; the conjecture
  holds at n = 1 (3 = 1 + 2) and n = 2 (18 = 4 + 14).
-/

namespace OMA.S_oeis_a375948

open PowerSeries

/-- `a` is the coefficient sequence of the e.g.f. `(3 - 2 * exp x)^(-3/2)`. -/
def IsA375948 (a : ℕ → ℚ) : Prop :=
  a 0 = 1 ∧
    (PowerSeries.mk fun n => a n / (n.factorial : ℚ)) ^ 2 * (3 - 2 * PowerSeries.exp ℚ) ^ 3 = 1

/-- Kurkov's conjecture. -/
theorem main : ∀ a b : ℕ → ℚ, IsA375948 a → b 0 = 1 →
    (∀ n : ℕ, 0 < n →
      b n = b (n - 1) + ∑ j ∈ Finset.range n, ((n - 1).choose j : ℚ) * a (j + 1)) →
    ∀ n : ℕ, 0 < n →
      a n = b (n - 1) + 2 * ∑ j ∈ Finset.range n, (n.choose j : ℚ) * a j := by
  sorry

end OMA.S_oeis_a375948
