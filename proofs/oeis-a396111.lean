import OMAStatements.S_oeis_a396111
open OMA.S_oeis_a396111
theorem OMA.solution : type_of% @OMA.S_oeis_a396111.main := by
  have h (n : ℕ) : 16 * a n ≡ 1 [MOD 2 * n + 1] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have : ((2 * n + 1 : ℕ) : ZMod (2 * n + 1)) = 0 := ZMod.natCast_self _
    push_cast [a, ZMod.natCast_mod] at this ⊢
    linear_combination ((2 * n - 1) * (4 * n ^ 2 + 1)) * this
  refine ⟨fun k => ?_, fun k => (Set.finite_Iic (8 * k)).subset fun n (e : a n = k) => ?_⟩
  · rcases k.eq_zero_or_pos with rfl | hk
    · exact ⟨0, rfl⟩
    refine ⟨8 * k - 1, Nat.ModEq.eq_of_lt_of_lt ?_ (Nat.mod_lt _ (by omega)) (by omega)⟩
    have c : 16 * k ≡ 1 [MOD 2 * (8 * k - 1) + 1] := by
      rw [show 2 * (8 * k - 1) + 1 = 16 * k - 1 by omega]; exact Nat.modEq_sub (by omega)
    exact Nat.ModEq.cancel_left_of_coprime (Nat.coprime_of_mul_modEq_one k c).symm ((h _).trans c.symm)
  · have := (h n).symm
    rw [e] at this
    rcases k.eq_zero_or_pos with rfl | hk
    · have := Nat.le_of_dvd one_pos (Nat.modEq_zero_iff_dvd.1 this)
      simp only [Set.mem_Iic]; omega
    · have := Nat.le_of_dvd (by omega) ((Nat.modEq_iff_dvd' (by omega)).1 this)
      simp only [Set.mem_Iic]; omega
