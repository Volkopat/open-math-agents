import Mathlib

/-!
# Decimal concatenation of consecutive Mersenne numbers

Peter asks whether every such concatenation congruent to six modulo seven is composite.
The larger Mersenne number comes first. For example, at index 12 the two blocks are
4095 and 2047, giving 40952047. At index 1 the right block is the single digit zero.

Source: https://mathoverflow.net/questions/294527
Formalization: @thematthewdunlop-cpu
-/

namespace OMA.S_mo_294527

def concatenation (n : ℕ) : ℕ :=
  let right : ℕ := 2 ^ (n - 1) - 1
  (2 ^ n - 1) * 10 ^ (Nat.log 10 right + 1) + right

theorem main : ∀ n : ℕ, 1 ≤ n → concatenation n % 7 = 6 → ¬ (concatenation n).Prime := by
  sorry

end OMA.S_mo_294527
