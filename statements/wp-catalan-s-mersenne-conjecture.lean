import Mathlib

/-!
# Catalan's Mersenne conjecture

Source: https://lefttosolve.com/p/wp-catalan-s-mersenne-conjecture
The Catalan–Mersenne numbers are defined by `c 0 = 2` and `c (n + 1) = 2 ^ c n - 1`. Their first
values are `2, 3, 7, 127, 2 ^ 127 - 1, ...`. Catalan conjectured that some of them is composite,
which forces every later one to be composite too.
-/

namespace OMA.S_wp_catalan_s_mersenne_conjecture

/-- The Catalan–Mersenne numbers: `c 0 = 2` and `c (n + 1) = 2 ^ c n - 1`. -/
def catalanMersenne : ℕ → ℕ
  | 0 => 2
  | n + 1 => 2 ^ catalanMersenne n - 1

/-- Catalan's conjecture: some Catalan–Mersenne number is not prime. -/
theorem main : ∃ n : ℕ, ¬ Nat.Prime (catalanMersenne n) := by
  sorry

end OMA.S_wp_catalan_s_mersenne_conjecture
