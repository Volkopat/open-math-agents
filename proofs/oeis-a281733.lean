import OMAStatements.S_oeis_a281733

namespace BC281733

theorem desc_mod (p N M : ℕ) (hN : p = N + 1) (hM : N = M + 1) :
    ∀ k, k ≤ M → (((3 * N + 1).descFactorial k : ℕ) : ZMod p) =
      (-1) ^ k * (((k + 1).factorial : ℕ) : ZMod p) := by
  have e : ((3 * N + 1 : ℕ) : ZMod p) + 2 = 3 * (p : ZMod p) := by
    have h' : 3 * N + 1 + 2 = 3 * p := by omega
    have h'' := congrArg (fun x : ℕ => (x : ZMod p)) h'
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h''
    push_cast
    linear_combination h''
  rw [ZMod.natCast_self, mul_zero] at e
  have h3 : ((3 * N + 1 : ℕ) : ZMod p) = -2 := by linear_combination e
  intro k
  induction k with
  | zero =>
    intro _
    simp
  | succ k ih =>
    intro hk
    have hkM : k ≤ M := by omega
    have hk3 : k ≤ 3 * N + 1 := by omega
    rw [Nat.descFactorial_succ, Nat.cast_mul, ih hkM, Nat.cast_sub hk3, h3,
      Nat.factorial_succ (k + 1)]
    push_cast
    ring

end BC281733

theorem OMA.solution : type_of% @OMA.S_oeis_a281733.main := by
  intro p hp
  rcases hp.eq_two_or_odd' with rfl | hodd
  · first
    | decide
    | (norm_num [OMA.S_oeis_a281733.T, Int.ModEq])
  · haveI := Fact.mk hp
    have hp2 := hp.two_le
    obtain ⟨r, hr⟩ := id hodd
    obtain ⟨N, hN⟩ : ∃ N, p = N + 1 := ⟨p - 1, by omega⟩
    obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hMo : Odd M := ⟨r - 1, by omega⟩
    obtain ⟨C, hC⟩ : ∃ C, C = Nat.choose (3 * p - 2) (2 * p - 1) := ⟨_, rfl⟩
    have hC' : C = Nat.choose (3 * N + 1) N := by
      rw [hC, show 3 * p - 2 = (2 * p - 1) + N by omega, Nat.choose_symm_add,
        show 2 * p - 1 + N = 3 * N + 1 by omega]
    have hdesc : (3 * N + 1).descFactorial N = N.factorial * C := by
      rw [hC', Nat.descFactorial_eq_factorial_mul_choose]
    have hdesc2 : (3 * N + 1).descFactorial N = 2 * p * (3 * N + 1).descFactorial M := by
      rw [hM, Nat.descFactorial_succ]
      congr 1
      omega
    have hpC : p ∣ C := by
      have h1 : p ∣ N.factorial * C := by
        rw [← hdesc, hdesc2]
        exact Dvd.dvd.mul_right (dvd_mul_left p 2) _
      have h2 : ¬ p ∣ N.factorial := by
        rw [hp.dvd_factorial]
        omega
      exact (hp.dvd_mul.mp h1).resolve_left h2
    obtain ⟨X, hX⟩ := hpC
    have hXN : N.factorial * X = 2 * (3 * N + 1).descFactorial M := by
      have h := hdesc.symm.trans hdesc2
      rw [hX] at h
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      calc p * (N.factorial * X) = N.factorial * (p * X) := by ring
        _ = 2 * p * (3 * N + 1).descFactorial M := h
        _ = p * (2 * (3 * N + 1).descFactorial M) := by ring
    have hD := BC281733.desc_mod p N M hN hM M le_rfl
    have hfact : ((N.factorial : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p, hp.dvd_factorial]
      omega
    have hXmod : (X : ZMod p) = -2 := by
      have h := congrArg (fun x : ℕ => (x : ZMod p)) hXN
      simp only [Nat.cast_mul, Nat.cast_ofNat] at h
      rw [hD, show M + 1 = N by omega, hMo.neg_one_pow] at h
      apply mul_left_cancel₀ hfact
      linear_combination h
    have h16 : (16 : ZMod p) ^ N = 1 := by
      have hne : (16 : ZMod p) ≠ 0 := by
        intro h0
        have h0' : ((16 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
        rw [CharP.cast_eq_zero_iff (ZMod p) p] at h0'
        have h24 : p ∣ 2 ^ 4 := by norm_num; exact h0'
        have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h24
        have := Nat.le_of_dvd (by norm_num) h2
        omega
      have := ZMod.pow_card_sub_one_eq_one hne
      rwa [show p - 1 = N by omega] at this
    have hT : OMA.S_oeis_a281733.T p = 16 ^ N * X := by
      unfold OMA.S_oeis_a281733.T
      rw [show p - 1 = N by omega, ← hC, hX, show 16 ^ N * (p * X) = p * (16 ^ N * X) by ring]
      exact Nat.mul_div_cancel_left _ hp.pos
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [hT]
    push_cast
    rw [h16, hXmod]
    ring
