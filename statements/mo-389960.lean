import Mathlib

/-!
# Natural numbers represented by four cubes

Zhi-Wei Sun conjectured that every natural number is the floor of the sum
of two half-weighted cubes and two sixth-weighted cubes, with the larger
base in each pair positive. Combining the fractions gives a single natural
number division by six, which takes the floor after the addition.

Source: https://mathoverflow.net/questions/389960
Lean statement by @jacklarmer.
-/

namespace OMA.S_mo_389960

theorem main :
    ∀ n : ℕ, ∃ a b c d : ℕ, max b 1 ≤ a ∧ max d 1 ≤ c ∧
      n = (3 * (a ^ 3 + b ^ 3) + (c ^ 3 + d ^ 3)) / 6 := by
  sorry

end OMA.S_mo_389960
