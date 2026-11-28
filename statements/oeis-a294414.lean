import Mathlib

/-!
# A294414: the ratio a(n)/a(n-1) tends to the golden ratio

Source: https://oeis.org/A294414 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry (Clark Kimberling, 2017), offset 0:
Solution of the complementary equation a(n) = a(n-1) + a(n-2) + b(n-1) + b(n-2), where
a(0) = 1, a(1) = 3, b(0) = 2, b(1) = 4, and (a(n)) and (b(n)) are increasing complementary sequences.

Comment: Conjecture: a(n)/a(n-1) -> (1 + sqrt(5))/2, the golden ratio.

Formalization notes.
* Complementary sequences are two strictly increasing sequences a and b of positive integers
  such that each positive integer is a term of exactly one of them. The entry says that a and b
  are determined by the equation and the initial values. `main` is stated for every pair (a, b)
  with these properties, so it does not depend on a construction of the sequences.
* The equation is required for n >= 2, where the index subtractions are true ones.
* The limit of a(n)/a(n-1) is written as the limit of a(n+1)/a(n) as n tends to infinity.
-/

namespace OMA.S_oeis_a294414

/-- Kimberling's conjecture: a(n)/a(n-1) tends to the golden ratio (1 + sqrt(5))/2. -/
theorem main : ∀ a b : ℕ → ℕ, StrictMono a → StrictMono b →
    (∀ m : ℕ, 0 < m → (m ∈ Set.range a ↔ m ∉ Set.range b)) →
    a 0 = 1 → a 1 = 3 → b 0 = 2 → b 1 = 4 →
    (∀ n : ℕ, 2 ≤ n → a n = a (n - 1) + a (n - 2) + b (n - 1) + b (n - 2)) →
    Filter.Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ)) Filter.atTop
      (nhds ((1 + Real.sqrt 5) / 2)) := by
  sorry

end OMA.S_oeis_a294414
