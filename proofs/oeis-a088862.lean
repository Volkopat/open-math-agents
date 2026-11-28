import OMAStatements.S_oeis_a088862

open Finset OMA.S_oeis_a088862

theorem OMA.solution : type_of% @OMA.S_oeis_a088862.main := by
  classical
  intro n
  have hcube : ∀ k, 10 ≤ k → k ^ 3 ≤ 2 ^ k := fun k hk => by
    induction k, hk using Nat.le_induction with
    | base => decide
    | succ k hk ih =>
      rw [pow_succ 2 k]
      refine le_trans ?_ (Nat.mul_le_mul_right 2 ih)
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
      ring_nf; omega
  have hnat : ∀ k, 2 ^ k ≤ (2 ^ k).primeCounting * k + (k + 1) := fun k => by
    have h0 := Chebyshev.psi_ge (2 ^ k)
    have h1 := Chebyshev.psi_le_primeCounting_mul_log (2 ^ k)
    have h2 : (2 : ℝ) ^ k + 1 ≤ 2 ^ (k + 1) := by rw [pow_succ]; linarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k)]
    have h3 := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ k + 1) h2
    push_cast at h0 h1 h3
    rw [Real.log_pow] at h1 h3
    push_cast at h3
    have he : (2 : ℝ) ^ k ≤ ((2 ^ k).primeCounting : ℝ) * k + (k + 1) :=
      le_of_mul_le_mul_right (by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    exact_mod_cast he
  let J := (n + 1) ^ 2 + 16
  have hgr : (n + 1) * (J * n + 1) < (2 ^ J).primeCounting := by
    by_contra! h
    have := Nat.mul_le_mul_right J h
    have := hcube J (by omega)
    have := hnat J
    have hr : (n + 1) * (J * n + 1) * J + (J + 1) < J ^ 3 := by dsimp [J]; ring_nf; omega
    omega
  let rootAt (dt : ℕ × ℕ) : ℕ := sInf {s : ℕ | 2 ^ dt.2 ≤ s ^ dt.1}
  let codes := range (n + 1) ×ˢ range (J * n + 1)
  have hc : (codes.image rootAt).card < (2 ^ J).primesLE.card := by
    rw [Nat.primesLE_card_eq_primeCounting]
    exact (card_image_le.trans (le_of_eq (by simp [codes]))).trans_lt hgr
  obtain ⟨p, hp, hnot⟩ := exists_mem_notMem_of_card_lt_card hc
  obtain ⟨hbd, hpr⟩ := Nat.mem_primesLE.1 hp
  have hgap : ∀ d ≤ n, ∀ t, 2 ^ t ≤ p ^ d → ¬ (p - 1) ^ d < 2 ^ t := fun d hd t hi lo => by
    have hdt : t ≤ J * n := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1
      (hi.trans ((Nat.pow_le_pow_left hbd d).trans ((pow_mul 2 J d).symm.trans_le (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left J hd)))))
    have hreq : rootAt (d, t) = p := IsLeast.csInf_eq ⟨hi, fun q hq => by
      by_contra! h
      exact not_lt_of_ge hq ((Nat.pow_le_pow_left (by omega : q ≤ p - 1) d).trans_lt lo)⟩
    exact hnot (mem_image.2 ⟨(d, t), by simp [codes, hd, hdt], hreq⟩)
  have hex : ∃ m, eligible n m := ⟨p ^ n, pow_pos hpr.pos _, by simp [hpr.primeFactorsList_pow], by
    intro a ha ha' b hb hb' t hab
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hpr).1 ha
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hpr).1 hb
    have hij : i ≤ j := (Nat.pow_le_pow_iff_right hpr.one_lt).1 (hab ▸ Nat.div_le_self _ _)
    by_contra hne
    obtain ⟨d, hdj⟩ := Nat.exists_eq_add_of_le hij
    have hd : 0 < d := by by_contra! h; exact hne (congrArg (p ^ ·) (by omega))
    have hi' : 0 < i := by by_contra! h; simp [show i = 0 by omega] at ha'
    have hpos : 0 < 2 ^ t := by positivity
    have hlo := (Nat.le_div_iff_mul_le hpos).1 hab.ge
    have hup := (Nat.div_lt_iff_lt_mul hpos).1 (Nat.lt_succ_of_le hab.le)
    rw [hdj, pow_add] at hlo hup
    apply hgap d (by omega) t (Nat.le_of_mul_le_mul_left hlo (pow_pos hpr.pos i))
    by_contra! hge
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    have hpi : p ≤ p ^ i := by simpa using Nat.pow_le_pow_right hpr.pos (show 1 ≤ i by omega)
    have h0 : (p ^ i + 1) * (p - 1) ≤ p ^ i * p := by
      have hp' : p - 1 + 1 = p := Nat.sub_add_cancel hpr.pos
      nlinarith [congrArg (· * p ^ i) hp']
    have hgb : (p ^ i + 1) * (p - 1) ^ (e + 1) ≤ p ^ i * p ^ (e + 1) := by
      calc (p ^ i + 1) * (p - 1) ^ (e + 1) = (p ^ i + 1) * (p - 1) * (p - 1) ^ e := by ring
        _ ≤ p ^ i * p * p ^ e := Nat.mul_le_mul h0 (Nat.pow_le_pow_left (by omega) e)
        _ = _ := by rw [pow_succ]; ring
    exact not_lt_of_ge ((Nat.mul_le_mul_left (p ^ i + 1) hge).trans hgb) hup⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun _ hm => Nat.find_min' hex hm⟩
