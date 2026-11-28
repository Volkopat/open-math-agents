import Mathlib

/-!
# A294426: the ratio a(n)/a(n-1) tends to the golden ratio

Source: https://oeis.org/A294426 (OEIS Foundation, CC BY-SA 4.0).

Entry (Clark Kimberling, 2017), offset 0:
Solution of the complementary equation a(n) = a(n-1) + a(n-2) + 2*b(n-1) - b(n-2) - 2, where
a(0) = 1, a(1) = 3, b(0) = 2, b(1) = 4.

Comments: The complementary sequences a() and b() are uniquely determined by the titular equation
and initial values. Conjecture: a(n)/a(n-1) -> (1 + sqrt(5))/2, the golden ratio.

Formalization notes.
* Complementary sequences are two strictly increasing sequences a and b of positive integers
  such that each positive integer is a term of exactly one of them. The entry says that a and b
  are determined by the equation and the initial values. `main` is stated for every pair (a, b)
  with these properties, so it does not depend on a construction of the sequences. This follows
  the merged statement of the sister entry A294414.
* The equation is required for n >= 2, where the index subtractions are true ones. It is written
  in the integers, so the subtractions in it are true ones too.
* The limit of a(n)/a(n-1) is written as the limit of a(n+1)/a(n) as n tends to infinity.
-/

namespace OMA.S_oeis_a294426

/-- Kimberling's conjecture: a(n)/a(n-1) tends to the golden ratio (1 + sqrt(5))/2. -/
theorem main : ∀ a b : ℕ → ℕ, StrictMono a → StrictMono b →
    (∀ m : ℕ, 0 < m → (m ∈ Set.range a ↔ m ∉ Set.range b)) →
    a 0 = 1 → a 1 = 3 → b 0 = 2 → b 1 = 4 →
    (∀ n : ℕ, 2 ≤ n →
      (a n : ℤ) = a (n - 1) + a (n - 2) + 2 * b (n - 1) - b (n - 2) - 2) →
    Filter.Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ)) Filter.atTop
      (nhds ((1 + Real.sqrt 5) / 2)) := by
  sorry

end OMA.S_oeis_a294426
