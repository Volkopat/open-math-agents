import OMAStatements.S_oeis_a192480

namespace CatalanLinearShift

open OMA.S_oeis_a192480

private theorem catalan_step (k : ℕ) :
    ((k : ℤ) + 2) * catalan (k + 1) = (4 * (k : ℤ) + 2) * catalan k := by
  have h := Nat.succ_mul_centralBinom_succ k
  rw [← succ_mul_catalan_eq_centralBinom (k + 1), ← succ_mul_catalan_eq_centralBinom k] at h
  have hm : (k + 1) * ((k + 2) * catalan (k + 1)) =
      (k + 1) * ((4 * k + 2) * catalan k) := by nlinarith only [h]
  exact_mod_cast Nat.eq_of_mul_eq_mul_left (by omega : 0 < k + 1) hm

private theorem recurrence (n : ℕ) (hn : 4 ≤ n) :
    (n : ℤ) * (3 * (n : ℤ) ^ 2 - 16 * (n : ℤ) + 19) * (a n : ℤ) +
      (-15 * (n : ℤ) ^ 3 + 95 * (n : ℤ) ^ 2 - 188 * (n : ℤ) + 120) * (a (n - 1) : ℤ) +
      2 * (2 * (n : ℤ) - 5) * (3 * (n : ℤ) ^ 2 - 10 * (n : ℤ) + 6) * (a (n - 2) : ℤ) = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have he : n = k + 4 := by omega
  rw [he]
  rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega]
  rw [show a (k + 4) = k + 4 + catalan (k + 3) from rfl,
    show a (k + 3) = k + 3 + catalan (k + 2) from rfl,
    show a (k + 2) = k + 2 + catalan (k + 1) from rfl]
  push_cast
  have h₁ := catalan_step (k + 1)
  have h₂ := catalan_step (k + 2)
  push_cast at h₁ h₂
  let x : ℤ := (k : ℤ) + 4
  linear_combination (3 * x ^ 2 - 16 * x + 19) * h₂ - (3 * x ^ 2 - 10 * x + 6) * h₁

end CatalanLinearShift

theorem OMA.solution : type_of% @OMA.S_oeis_a192480.main :=
  CatalanLinearShift.recurrence
