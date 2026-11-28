import OMAStatements.S_oeis_a337868

namespace OMA.S_oeis_a337868

open Finset



/-- Control: the first 26 terms of the entry. -/
theorem first_terms :
    (List.range 26).map (fun i => a (i + 1)) = [0, 2, 3, 3, 5, 6, 7, 6, 7, 10, 11, 9, 13, 14, 15,
      11, 17, 14, 19, 15, 21, 22, 23, 17, 21, 26] := by
  decide +kernel

/-- The units below n. -/
def U (n : ℕ) : Finset ℕ := (range n).filter (fun u => n.Coprime u)

theorem card_U (n : ℕ) : (U n).card = n.totient := by
  rw [Nat.totient]
  rfl

theorem mem_R {n y : ℕ} : y ∈ R n ↔ ∃ x < n, ∃ r, 2 ≤ r ∧ r ≤ n ∧ x ^ r % n = y := by
  simp only [R, mem_image, mem_product, mem_range, mem_Icc, Prod.exists]
  constructor
  · rintro ⟨x, r, ⟨hx, hr1, hr2⟩, h⟩
    exact ⟨x, hx, r, hr1, hr2, h⟩
  · rintro ⟨x, hx, r, hr1, hr2, h⟩
    exact ⟨x, r, ⟨hx, hr1, hr2⟩, h⟩

theorem totient_le {n : ℕ} (hn : 2 ≤ n) : n.totient + 1 ≤ n := by
  have := Nat.totient_lt n (by omega)
  omega

theorem U_sub {n : ℕ} (hn : 2 ≤ n) : U n ⊆ R n := by
  intro u hu
  simp only [U, mem_filter, mem_range] at hu
  rw [mem_R]
  refine ⟨u, hu.1, n.totient + 1, ?_, totient_le hn, ?_⟩
  · have := Nat.totient_pos.mpr (by omega : 0 < n)
    omega
  · have h := Nat.ModEq.pow_totient (Nat.Coprime.symm hu.2)
    have : u ^ (n.totient + 1) ≡ 1 * u [MOD n] := by
      rw [pow_succ]
      exact h.mul_right u
    rw [one_mul] at this
    rw [this, Nat.mod_eq_of_lt hu.1]

theorem zero_mem {n : ℕ} (hn : 2 ≤ n) : 0 ∈ R n := by
  rw [mem_R]
  exact ⟨0, by omega, 2, le_refl 2, hn, by simp⟩

theorem zero_not_U {n : ℕ} (hn : 2 ≤ n) : 0 ∉ U n := by
  simp only [U, mem_filter, mem_range, Nat.coprime_zero_right]
  omega

theorem ge_totient {n : ℕ} (hn : 2 ≤ n) : n.totient + 1 ≤ a n := by
  have hsub : insert 0 (U n) ⊆ R n := by
    intro y hy
    rw [mem_insert] at hy
    rcases hy with rfl | hy
    · exact zero_mem hn
    · exact U_sub hn hy
  have := card_le_card hsub
  rw [card_insert_of_notMem (zero_not_U hn), card_U] at this
  exact this

/-- For primes and squares of primes every residue x^r (r >= 2) is 0 or a unit. -/
theorem R_sub {n : ℕ} (h : ∃ p : ℕ, p.Prime ∧ (n = p ∨ n = p ^ 2)) : R n ⊆ insert 0 (U n) := by
  obtain ⟨p, hp, hn⟩ := h
  intro y hy
  rw [mem_R] at hy
  obtain ⟨x, hx, r, hr1, hr2, rfl⟩ := hy
  rw [mem_insert]
  by_cases hpx : p ∣ x
  · left
    rcases hn with rfl | rfl
    · exact Nat.mod_eq_zero_of_dvd (dvd_pow hpx (by omega))
    · exact Nat.mod_eq_zero_of_dvd ((pow_dvd_pow_of_dvd hpx 2).trans (pow_dvd_pow x hr1))
  · right
    simp only [U, mem_filter, mem_range]
    have hcop : Nat.Coprime p x := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpx
    have hn0 : 0 < n := by
      rcases hn with rfl | rfl
      · exact hp.pos
      · exact pow_pos hp.pos 2
    refine ⟨Nat.mod_lt _ hn0, ?_⟩
    have : Nat.Coprime n (x ^ r) := by
      rcases hn with rfl | rfl
      · exact (Nat.Coprime.pow_right r hcop)
      · exact Nat.Coprime.pow_left 2 (Nat.Coprime.pow_right r hcop)
    rw [Nat.Coprime, Nat.gcd_comm, ← Nat.gcd_rec]
    exact this

/-- Otherwise there is a residue that is neither 0 nor a unit. -/
theorem extra {n : ℕ} (hn : 2 ≤ n) (h : ¬ ∃ p : ℕ, p.Prime ∧ (n = p ∨ n = p ^ 2)) :
    ∃ y ∈ R n, y ≠ 0 ∧ y ∉ U n := by
  set p := n.minFac with hp
  have hpp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  by_cases hpow : ∃ k, n = p ^ k
  · obtain ⟨k, hk⟩ := hpow
    have hk3 : 3 ≤ k := by
      by_contra hk3
      push_neg at hk3
      interval_cases k
      · rw [pow_zero] at hk; omega
      · exact h ⟨p, hpp, Or.inl (by rw [hk, pow_one])⟩
      · exact h ⟨p, hpp, Or.inr hk⟩
    refine ⟨p ^ 2, ?_, ?_, ?_⟩
    · rw [mem_R]
      have hlt : p ^ 2 < n := by
        rw [hk]
        exact Nat.pow_lt_pow_right hpp.one_lt (by omega)
      refine ⟨p, lt_of_le_of_lt (by nlinarith [hpp.two_le]) hlt, 2, le_refl 2, hn, ?_⟩
      exact Nat.mod_eq_of_lt hlt
    · exact pow_ne_zero 2 hpp.ne_zero
    · simp only [U, mem_filter, mem_range, not_and]
      intro _ hcop
      have : p ∣ Nat.gcd n (p ^ 2) := Nat.dvd_gcd hpn (dvd_pow_self p (by norm_num))
      rw [hcop] at this
      exact hpp.one_lt.ne' (Nat.dvd_one.mp this)
  · -- two coprime factors a = p^v, b = n / p^v > 1
    set v := n.factorization p
    set A := p ^ v
    set B := n / A
    have hA : A ∣ n := Nat.ordProj_dvd n p
    have hcopAB : Nat.Coprime A B := Nat.coprime_ordCompl hpp (by omega) |>.pow_left v
    have hB1 : 1 < B := by
      by_contra hB
      push_neg at hB
      have hB0 : 0 < B := Nat.div_pos (Nat.le_of_dvd (by omega) hA) (pow_pos hpp.pos v)
      have : B = 1 := by omega
      apply hpow
      exact ⟨v, by rw [← Nat.div_mul_cancel hA]; simp [B, this] at *; omega⟩
    have hA1 : 1 < A := by
      have hv : 1 ≤ v := (hpp.dvd_iff_one_le_factorization (by omega)).mp hpn
      calc 1 < p := hpp.one_lt
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ A := Nat.pow_le_pow_right hpp.pos hv
    have hnAB : n = A * B := (Nat.mul_div_cancel' hA).symm
    -- the idempotent e = 0 mod A, 1 mod B
    set e := (Nat.chineseRemainder hcopAB 0 1 : ℕ) with he
    have he1 : e ≡ 0 [MOD A] := (Nat.chineseRemainder hcopAB 0 1).2.1
    have he2 : e ≡ 1 [MOD B] := (Nat.chineseRemainder hcopAB 0 1).2.2
    have helt : e < A * B := Nat.chineseRemainder_lt_mul hcopAB 0 1 (by omega) (by omega)
    refine ⟨e, ?_, ?_, ?_⟩
    · rw [mem_R]
      refine ⟨e, by rw [hnAB]; exact helt, 2, le_refl 2, hn, ?_⟩
      have hsq : e ^ 2 ≡ e [MOD A * B] := by
        rw [← Nat.modEq_and_modEq_iff_modEq_mul hcopAB]
        constructor
        · have := he1.pow 2
          rw [zero_pow (by norm_num)] at this
          exact this.trans he1.symm
        · have := he2.pow 2
          rw [one_pow] at this
          exact this.trans he2.symm
      rw [hnAB]
      unfold Nat.ModEq at hsq
      rw [hsq, Nat.mod_eq_of_lt helt]
    · intro h0
      rw [h0] at he2
      unfold Nat.ModEq at he2
      rw [Nat.zero_mod, Nat.mod_eq_of_lt hB1] at he2
      omega
    · simp only [U, mem_filter, mem_range, not_and]
      intro _ hcop
      have hAe : A ∣ e := (Nat.modEq_zero_iff_dvd).mp he1
      have : A ∣ Nat.gcd n e := Nat.dvd_gcd hA hAe
      rw [hcop] at this
      have := Nat.le_of_dvd one_pos this
      omega

/-- The conjecture: for n > 1, a(n) = phi(n) + 1 iff n is a prime or the square of a prime. -/
theorem conjecture (n : ℕ) (hn : 2 ≤ n) :
    a n = n.totient + 1 ↔ ∃ p : ℕ, p.Prime ∧ (n = p ∨ n = p ^ 2) := by
  constructor
  · intro heq
    by_contra h
    obtain ⟨y, hyR, hy0, hyU⟩ := extra hn h
    have hsub : insert y (insert 0 (U n)) ⊆ R n := by
      intro z hz
      rw [mem_insert, mem_insert] at hz
      rcases hz with rfl | rfl | hz
      · exact hyR
      · exact zero_mem hn
      · exact U_sub hn hz
    have hcard := card_le_card hsub
    have hy : y ∉ insert 0 (U n) := by
      rw [mem_insert]
      push_neg
      exact ⟨hy0, hyU⟩
    rw [card_insert_of_notMem hy, card_insert_of_notMem (zero_not_U hn), card_U] at hcard
    unfold a at heq
    omega
  · intro h
    apply le_antisymm
    · have := card_le_card (R_sub h)
      rw [card_insert_of_notMem (zero_not_U hn), card_U] at this
      exact this
    · exact ge_totient hn

end OMA.S_oeis_a337868

theorem OMA.solution : type_of% @OMA.S_oeis_a337868.main :=
  fun n hn => OMA.S_oeis_a337868.conjecture n hn
