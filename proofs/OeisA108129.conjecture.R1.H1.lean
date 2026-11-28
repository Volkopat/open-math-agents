import OMAReductions.R_OeisA108129_conjecture_R1
-- Credit: @kofls (shorter proof)
set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_OeisA108129_conjecture_R1.H1 := by
  show OeisA108129.a 254602 = -1
  rw [OeisA108129.a, if_neg (by norm_num), dif_neg]
  rintro ⟨m, hm, hp⟩
  norm_num at hp
  obtain ⟨p, l, h3, hP, h⟩ := (by decide : ∀ r < 24, ∃ p < 242, 3 ≤ p ∧ p ∣ 5592405 ∧
    509203 * 2 ^ r % 5592405 % p = 1) _ (m.mod_lt (by norm_num : 24 > 0))
  have e : 509203 * 2 ^ m % 5592405 = 509203 * 2 ^ (m % 24) % 5592405 := by
    conv_lhs => rw [← Nat.mod_add_div m 24, pow_add, pow_mul, ← mul_assoc]
    exact ((Nat.ModEq.pow _ (by decide : 2 ^ 24 ≡ 1 [MOD 5592405])).mul_left _).trans (by simp [Nat.ModEq])
  rw [← e, Nat.mod_mod_of_dvd _ hP] at h
  have d := Nat.dvd_sub_mod (n := p) (509203 * 2 ^ m)
  rw [h] at d
  have t : 2 ≤ 2 ^ m := Nat.le_self_pow hm 2
  rcases hp.eq_one_or_self_of_dvd p d with h | h <;> omega
