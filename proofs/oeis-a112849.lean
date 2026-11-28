import OMAStatements.S_oeis_a112849
import Mathlib

open OMA.S_oeis_a112849

namespace P112849

theorem cf (j : ℕ) : ((2 * j + 3).choose (j + 2) : ℚ) =
    ((2 * j + 3).factorial : ℚ) / (((j + 2).factorial : ℚ) * ((j + 1).factorial : ℚ)) := by
  rw [Nat.cast_choose ℚ (by omega : j + 2 ≤ 2 * j + 3), show 2 * j + 3 - (j + 2) = j + 1 by omega]

theorem fsucc (m : ℕ) : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
  rw [Nat.factorial_succ]; push_cast; ring

theorem crec (j : ℕ) : ((2 * (j + 1) + 3).choose (j + 1 + 2) : ℚ) * ((j : ℚ) + 3) =
    2 * (2 * (j : ℚ) + 5) * ((2 * j + 3).choose (j + 2) : ℚ) := by
  rw [cf, cf, show 2 * (j + 1) + 3 = 2 * j + 3 + 1 + 1 by ring, show j + 1 + 2 = j + 2 + 1 by ring,
    show j + 1 + 1 = j + 2 by ring, fsucc, fsucc, fsucc (j + 2), show j + 2 = j + 1 + 1 by ring, fsucc (j + 1)]
  have f1 : ((j + 1).factorial : ℚ) ≠ 0 := by positivity
  have f2 : ((2 * j + 3).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem av (a : ℕ → ℚ) (hf : ∀ n : ℕ, 2 ≤ n → a n = 1 + (1 / 2) * ((2 * n - 1).choose (n - 1) : ℚ) +
      (1 / 2) * ((2 * n - 1).choose n : ℚ)) (j : ℕ) :
    a (j + 2) = 1 + ((2 * j + 3).choose (j + 2) : ℚ) := by
  rw [hf (j + 2) (by omega), show 2 * (j + 2) - 1 = 2 * j + 3 by omega, show j + 2 - 1 = j + 1 by omega,
    Nat.choose_symm_of_eq_add (show 2 * j + 3 = (j + 1) + (j + 2) by ring)]
  ring

end P112849

open P112849 in
theorem OMA.solution : type_of% @OMA.S_oeis_a112849.main := by
  intro a h1 hf n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 - 1 = (k + 1) + 2 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 = (k + 2) + 2 by omega, av a hf, av a hf, av a hf]
  have e1 := crec k
  have e2 := crec (k + 1)
  rw [show k + 1 + 1 = k + 2 by ring] at e2
  push_cast at e1 e2 ⊢
  linear_combination (3 * (k : ℚ) + 7) * e2 - (3 * (k : ℚ) + 10) * e1
