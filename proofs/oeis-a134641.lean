import OMAStatements.S_oeis_a134641
import Mathlib

open OMA.S_oeis_a134641 in
theorem OMA.solution : type_of% @OMA.S_oeis_a134641.main := by
  intro p hp
  constructor
  · rintro ⟨b, hb, σ, hσ⟩
    have h1 : ∑ i : Fin b, ((σ i : Fin b) : ℕ) = ∑ i : Fin b, (i : ℕ) :=
      Equiv.sum_comp σ (fun i : Fin b => (i : ℕ))
    have h2 : ∑ i : Fin b, (i : ℕ) = ∑ i ∈ Finset.range b, i :=
      Fin.sum_univ_eq_sum_range (fun i => i) b
    have hS : (∑ i : Fin b, ((σ i : Fin b) : ℕ)) * 2 = b * (b - 1) := by
      rw [h1, h2]
      exact Finset.sum_range_id_mul_two b
    have hlow : (∑ i : Fin b, ((σ i : Fin b) : ℕ)) ≤ p := by
      rw [hσ]
      apply Finset.sum_le_sum
      intro i _
      have := Nat.one_le_pow (i : ℕ) b (by omega)
      nlinarith
    have hb1 : ((b : ℕ) : ZMod (b - 1)) = 1 := by
      have h0 : ((b - 1 : ℕ) : ZMod (b - 1)) = 0 := ZMod.natCast_self _
      have h3 : ((b : ℕ) : ZMod (b - 1)) = ((b - 1 : ℕ) : ZMod (b - 1)) + 1 := by
        rw [← Nat.cast_succ]
        congr 1
        omega
      rw [h3, h0, zero_add]
    have hmod : p % (b - 1) = (∑ i : Fin b, ((σ i : Fin b) : ℕ)) % (b - 1) := by
      rw [← ZMod.natCast_eq_natCast_iff', hσ]
      push_cast
      simp [hb1]
    generalize (∑ i : Fin b, ((σ i : Fin b) : ℕ)) = S at hS hlow hmod
    have key : b = 2 ∨ b = 3 := by
      obtain ⟨m, hm⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
      have hm1 : b - 1 = m := by omega
      rw [hm1] at hmod hS
      rw [hm] at hS
      rcases Nat.even_or_odd' m with ⟨c, hc | hc⟩
      · subst hc
        have hS' : S = 2 * c * c + c := by nlinarith
        rcases Nat.eq_zero_or_pos c with h0 | hcpos
        · subst h0
          exfalso
          have hS0 : S = 0 := by simpa using hS'
          have hpS : p = S := by simpa using hmod
          exact hp.ne_zero (hpS.trans hS0)
        · have hm2 : S % (2 * c) = c := by
            rw [hS', show 2 * c * c + c = c + c * (2 * c) by ring, Nat.add_mul_mod_self_right]
            exact Nat.mod_eq_of_lt (by omega)
          have hd : c ∣ p := by
            have hdm := Nat.div_add_mod p (2 * c)
            rw [hmod, hm2] at hdm
            exact ⟨2 * (p / (2 * c)) + 1, by first | linarith [hdm] | nlinarith [hdm]⟩
          rcases Nat.Prime.eq_one_or_self_of_dvd hp c hd with h3 | h3
          · right; omega
          · exfalso; nlinarith
      · subst hc
        have hS' : S = (c + 1) * (2 * c + 1) := by nlinarith
        have hm2 : S % (2 * c + 1) = 0 := by
          rw [hS']
          exact Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _)
        have hd : (2 * c + 1) ∣ p := Nat.dvd_of_mod_eq_zero (by rw [hmod, hm2])
        rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hd with h3 | h3
        · left; omega
        · exfalso
          have := hp.two_le
          nlinarith
    rcases key with rfl | rfl
    · have h0 := (σ 0).isLt
      have h1' := (σ 1).isLt
      have hne : (σ 0 : ℕ) ≠ σ 1 := fun h => (σ.injective.ne (by decide : (0 : Fin 2) ≠ 1)) (Fin.ext h)
      simp [Fin.sum_univ_two] at hσ
      have := hp.two_le
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · have h0 := (σ 0).isLt
      have h1' := (σ 1).isLt
      have h2' := (σ 2).isLt
      have hne1 : (σ 0 : ℕ) ≠ σ 1 := fun h => (σ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) (Fin.ext h)
      have hne2 : (σ 0 : ℕ) ≠ σ 2 := fun h => (σ.injective.ne (by decide : (0 : Fin 3) ≠ 2)) (Fin.ext h)
      have hne3 : (σ 1 : ℕ) ≠ σ 2 := fun h => (σ.injective.ne (by decide : (1 : Fin 3) ≠ 2)) (Fin.ext h)
      simp [Fin.sum_univ_three] at hσ
      have hcases : p = 21 ∨ p = 15 ∨ p = 19 ∨ p = 7 ∨ p = 11 ∨ p = 5 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | decide
        | (exfalso; norm_num at hp)
  · intro hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · exact ⟨2, by norm_num, 1, by first | rfl | decide | simp [Fin.sum_univ_two]⟩
    · exact ⟨3, by norm_num, Equiv.swap 0 2, by
        first | rfl | decide | simp [Fin.sum_univ_three, Equiv.swap_apply_def]⟩
    · exact ⟨3, by norm_num, Equiv.swap 0 1 * Equiv.swap 1 2, by
        first | rfl | decide | simp [Fin.sum_univ_three, Equiv.swap_apply_def, Equiv.Perm.mul_apply]⟩
    · exact ⟨3, by norm_num, Equiv.swap 0 2 * Equiv.swap 1 2, by
        first | rfl | decide | simp [Fin.sum_univ_three, Equiv.swap_apply_def, Equiv.Perm.mul_apply]⟩
    · exact ⟨3, by norm_num, Equiv.swap 0 1, by
        first | rfl | decide | simp [Fin.sum_univ_three, Equiv.swap_apply_def]⟩
