import Mathlib

/-!
# Positive integers m with 2m² - 1 = x⁴ + y⁴, |x - y| > 1

Source: https://mathoverflow.net/questions/391894 (Zhi-Wei Sun, CC BY-SA 4.0).

The identity `2(n² + n + 1)² - 1 = n⁴ + (n + 1)⁴` gives solutions with `|x - y| = 1`.
Question 1 (the title): are there infinitely many positive integers `m` such that
`2m² - 1 = x⁴ + y⁴` for some `x, y ∈ ℕ = {0, 1, …}` with `|x - y| > 1`? The poser guesses yes
(53 such `m` below `10⁸`, OEIS A343913); `main` states the expected yes.
The equation is written `2m² = x⁴ + y⁴ + 1` and `|x - y| > 1` as `x + 1 < y ∨ y + 1 < x`,
avoiding natural-number subtraction.
-/

namespace OMA.S_mo_391894

theorem main : Set.Infinite {m : ℕ | 0 < m ∧
    ∃ x y : ℕ, 2 * m ^ 2 = x ^ 4 + y ^ 4 + 1 ∧ (x + 1 < y ∨ y + 1 < x)} := by
  sorry

end OMA.S_mo_391894
