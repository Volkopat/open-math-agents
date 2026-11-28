import OMAStatements.S_oeis_a103777
open OMA.S_oeis_a103777
private theorem composite {j : ℕ} (hj : 3 ≤ j % 5) : ¬ (f j).Prime := fun hp => by
  have h := (Nat.mod_modEq j 5).symm
  have hz : f (j % 5) ≡ 0 [MOD 5] := by
    rcases (by omega : j % 5 = 3 ∨ j % 5 = 4) with hm | hm <;> rw [hm] <;> decide
  have := (Nat.prime_dvd_prime_iff_eq (by decide) hp).mp
    (Nat.dvd_of_mod_eq_zero (((((h.pow 2).mul_left 8).add (h.mul_left 4)).add_right 1).trans hz))
  unfold f at this
  nlinarith [hj.trans (Nat.mod_le j 5)]
theorem OMA.solution : type_of% @OMA.S_oeis_a103777.main := by
  intro n ⟨h₀, h₁, h₂, h₃⟩
  rcases (by omega : 3 ≤ n % 5 ∨ 3 ≤ (n + 1) % 5 ∨ 3 ≤ (n + 2) % 5 ∨ 3 ≤ (n + 3) % 5) with
    h | h | h | h <;> exact composite h ‹_›
