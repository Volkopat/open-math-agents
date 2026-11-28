import OMAReductions.R_oeis_a144743_R1

namespace A144743ShortRange

private abbrev A : ℕ := 180680260792773944179

private def moduli : List ℕ := [113,191,269,431,607,30047,109819,122399,149119]

/-- Combine the two possible signs modulo each prime. -/
private def roots : List ℕ → List ℕ
  | [] => [0]
  | p :: ps => if h : p.Coprime ps.prod then
      (roots ps).flatMap fun r => [(Nat.chineseRemainder h 1 r).val,
        (Nat.chineseRemainder h (p-1) r).val]
    else []

private theorem complete (x : ℕ) (ps : List ℕ) (co : ps.Pairwise Nat.Coprime)
    (pos : ∀ p ∈ ps, p ≠ 0)
    (signs : ∀ p ∈ ps, x ≡ 1 [MOD p] ∨ x ≡ p-1 [MOD p]) : x % ps.prod ∈ roots ps := by
  induction ps with
  | nil => simp [roots, Nat.mod_one]
  | cons p ps ih =>
    have cop : p.Coprime ps.prod := Nat.coprime_list_prod_right_iff.mpr (List.pairwise_cons.mp co).1
    have hp := pos p List.mem_cons_self
    have hm : ps.prod ≠ 0 := by
      rw [ne_eq, List.prod_eq_zero_iff]
      exact fun h => pos 0 (List.mem_cons_of_mem _ h) rfl
    have tailMem := ih co.of_cons (fun q h => pos q (List.mem_cons_of_mem _ h))
      (fun q h => signs q (List.mem_cons_of_mem _ h))
    have eqcrt (b : ℕ) (hb : x ≡ b [MOD p]) :
        x % (p * ps.prod) = (Nat.chineseRemainder cop b (x % ps.prod)).val := by
      have e := Nat.chineseRemainder_modEq_unique cop hb (Nat.mod_modEq x ps.prod).symm
      exact Eq.trans e (Nat.mod_eq_of_lt (Nat.chineseRemainder_lt_mul cop _ _ hp hm))
    simp only [List.prod_cons, roots, dif_pos cop, List.mem_flatMap]
    refine ⟨x % ps.prod, tailMem, ?_⟩
    rcases signs p List.mem_cons_self with h | h
    · simp [eqcrt 1 h]
    · simp [eqcrt (p-1) h]

private theorem exclude (c x : ℕ) (hc : 2 ≤ c) (hbound : 2*c^2 ≤ A)
    (hs : x*x = (A*A-1)*(c*c-1)+1) : False := by
  have hc2 : 4 ≤ c*c := by nlinarith
  have hx2 : x*x = (A*A-1)*(c*c) - (A*A-1) + 1 := by
    rw [hs, Nat.mul_sub, Nat.mul_one]
  have hxl : A < x := by
    by_contra! h
    have hle := Nat.mul_self_le_mul_self h
    dsimp [A] at *
    omega
  have hxu : x < 2000000000000000000000000000000 := by
    by_contra! h
    have hle := Nat.mul_self_le_mul_self h
    rw [pow_two] at hbound
    dsimp [A] at *
    omega
  have factors : (x-1)*(x+1) = (A*A-1)*(c*c-1) := by
    have h := Nat.sub_add_cancel (show 1 ≤ x by omega)
    nlinarith only [h, hs, congrArg (fun z : ℕ => z*x) h]
  have data : ∀ p ∈ moduli, p.Prime ∧ p ∣ A*A-1 := by
    intro p hp
    simp [moduli] at hp
    rcases hp with h|h|h|h|h|h|h|h|h <;> subst p <;> constructor <;> norm_num [A]
  have signs (p : ℕ) (hp : p ∈ moduli) : x ≡ 1 [MOD p] ∨ x ≡ p-1 [MOD p] := by
    obtain ⟨prime, div⟩ := data p hp
    have d : p ∣ (x-1)*(x+1) := factors ▸ dvd_mul_of_dvd_left div _
    rcases prime.dvd_mul.mp d with d | d
    · exact Or.inl ((Nat.modEq_iff_dvd' (by omega : 1 ≤ x)).mpr d).symm
    · right
      apply Nat.ModEq.add_right_cancel' 1
      rw [Nat.sub_add_cancel prime.one_le]
      exact d.modEq_zero_nat.trans (dvd_refl p).zero_modEq_nat
  have member := complete x moduli (by decide) (fun p hp => (data p hp).1.ne_zero) signs
  rw [Nat.mod_eq_of_lt (hxu.trans (by decide : 2000000000000000000000000000000 < moduli.prod))] at member
  have cert : (roots moduli).all (fun r => decide (r ≤ A ∨ 2000000000000000000000000000000 ≤ r ∨
      (r*r-1) % (A*A-1) ≠ 0)) = true := by decide +kernel
  have rem : (x*x-1) % (A*A-1) = 0 := by simp [hs]
  have h := of_decide_eq_true (List.all_eq_true.mp cert x member)
  omega

end A144743ShortRange

theorem OMA.solution : OMA.R_oeis_a144743_R1.H1 := by
  intro c hc hb ⟨s, hs⟩
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ c)
  have ha : OMA.S_oeis_a144743.a 6 = (A144743ShortRange.A : ℤ) := by decide
  rw [ha] at hb hs
  apply A144743ShortRange.exclude m s.natAbs (by exact_mod_cast hc) (by exact_mod_cast hb)
  have hm : 1 ≤ m*m := by
    have : 2 ≤ m := by exact_mod_cast hc
    nlinarith
  have hA : 1 ≤ A144743ShortRange.A * A144743ShortRange.A := by decide
  apply Int.natCast_inj.mp
  rw [Nat.cast_mul, Int.natAbs_mul_self', Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub hA, Nat.cast_sub hm]
  push_cast
  norm_num [A144743ShortRange.A, pow_two] at hs ⊢ <;> exact hs
