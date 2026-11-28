import Mathlib

/-!
# Are there primitive weird numbers divisible by the cube of an odd prime?

Source: https://mathoverflow.net/questions/506281
Credit: @datdzrgb
-/

namespace OMA.S_mo_506281

theorem main :
    ∃ p n : ℕ, p.Prime ∧ Odd p ∧ 0 < n ∧ p ^ 3 ∣ n ∧
      n.Weird ∧ ∀ d ∈ n.properDivisors, ¬ d.Weird := by
  sorry

end OMA.S_mo_506281
