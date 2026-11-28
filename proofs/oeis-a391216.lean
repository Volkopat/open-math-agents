import OMAStatements.S_oeis_a391216

namespace OMA.S_oeis_a391216




/-! ### A Lucas certificate for 31# + 1 -/

/-- b^e mod m by repeated squaring, with fuel f. -/
def pm : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, m => 1 % m
  | f + 1, b, e, m => if e = 0 then 1 % m else
      (if e % 2 = 1 then b % m else 1 % m) * pm f (b * b % m) (e / 2) m % m

lemma pm_spec : ∀ f b e m, e < 2 ^ f → pm f b e m = b ^ e % m := by
  intro f
  induction f with
  | zero =>
    intro b e m he
    have : e = 0 := by simpa using he
    subst this
    simp [pm]
  | succ f ih =>
    intro b e m he
    have he2 : e / 2 < 2 ^ f := by rw [pow_succ] at he; omega
    simp only [pm]
    rw [ih _ _ _ he2]
    split_ifs with h0 h1
    · subst h0
      simp
    · have h : b ^ e = b * (b * b) ^ (e / 2) := by
        conv_lhs => rw [show e = 2 * (e / 2) + 1 by omega]
        rw [pow_succ, pow_mul, sq]
        ring
      rw [h, Nat.mul_mod b ((b * b) ^ (e / 2)) m, Nat.pow_mod (b * b) (e / 2) m]
    · have h : b ^ e = (b * b) ^ (e / 2) := by
        conv_lhs => rw [show e = 2 * (e / 2) by omega]
        rw [pow_mul, sq]
      rw [h, Nat.pow_mod (b * b) (e / 2) m, ← Nat.mul_mod, one_mul]

/-- 31# + 1 is prime. -/
theorem prime_P1 : Nat.Prime 200560490131 := by
  have hcast : ∀ e : ℕ, pm 40 34 e 200560490131 = 1 → e < 2 ^ 40 →
      ((34 : ZMod 200560490131)) ^ e = 1 := by
    intro e h he
    rw [pm_spec 40 34 e _ he] at h
    have : ((34 ^ e : ℕ) : ZMod 200560490131) = ((1 : ℕ) : ZMod 200560490131) :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (by rw [h])
    simpa using this
  have hne : ∀ e : ℕ, pm 40 34 e 200560490131 ≠ 1 → e < 2 ^ 40 →
      ((34 : ZMod 200560490131)) ^ e ≠ 1 := by
    intro e h he hc
    apply h
    rw [pm_spec 40 34 e _ he]
    have : ((34 ^ e : ℕ) : ZMod 200560490131) = ((1 : ℕ) : ZMod 200560490131) := by
      simpa using hc
    have h2 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp this
    simpa using h2
  apply lucas_primality 200560490131 34
  · exact hcast _ (by decide +kernel) (by norm_num)
  · intro q hq hqd
    have hprod : (200560490131 - 1 : ℕ) =
        ∏ r ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ), r := by decide
    rw [hprod] at hqd
    obtain ⟨r, hr, hqr⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hqd
    have hrp : r.Prime := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hqr' : q = r := (Nat.prime_dvd_prime_iff_eq hq hrp).mp hqr
    subst hqr'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hne _ (by decide +kernel) (by norm_num)

/-! ### Products of distinct primes -/

lemma prod_ge (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ i ∈ Finset.range S.card, Nat.nth Nat.Prime i ≤ ∏ p ∈ S, p := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert M S hlt ih =>
    have hM : M ∉ S := fun h => lt_irrefl _ (hlt M h)
    rw [Finset.card_insert_of_notMem hM, Finset.prod_range_succ, Finset.prod_insert hM]
    have ih' := ih (fun p hp => hS p (Finset.mem_insert_of_mem hp))
    have hMp : M.Prime := hS M (Finset.mem_insert_self M S)
    have hcount : S.card ≤ Nat.count Nat.Prime M := by
      rw [Nat.count_eq_card_filter_range]
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hlt x hx, hS x (Finset.mem_insert_of_mem hx)⟩
    have hnth : Nat.nth Nat.Prime S.card ≤ M := by
      calc Nat.nth Nat.Prime S.card ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime M) :=
            Nat.nth_monotone Nat.infinite_setOfPred_prime hcount
        _ = M := Nat.nth_count hMp
    calc (∏ i ∈ Finset.range S.card, Nat.nth Nat.Prime i) * Nat.nth Nat.Prime S.card
        ≤ (∏ p ∈ S, p) * M := Nat.mul_le_mul ih' hnth
      _ = M * ∏ p ∈ S, p := mul_comm _ _

lemma nth_prime_eq {p k : ℕ} (hp : p.Prime) (hk : Nat.count Nat.Prime p = k) :
    Nat.nth Nat.Prime k = p := hk ▸ Nat.nth_count hp

lemma first_eleven : ∏ i ∈ Finset.range 11, Nat.nth Nat.Prime i = 200560490130 := by
  have h0 := nth_prime_eq (k := 0) (by norm_num : (2 : ℕ).Prime)
    (by simp only [Nat.count_succ, Nat.count_zero]; norm_num)
  have h1 := nth_prime_eq (k := 1) (by norm_num : (3 : ℕ).Prime)
    (by simp only [Nat.count_succ, Nat.count_zero]; norm_num)
  have h2 := nth_prime_eq (k := 2) (by norm_num : (5 : ℕ).Prime)
    (by simp only [Nat.count_succ, Nat.count_zero]; norm_num)
  have h3 := nth_prime_eq (k := 3) (by norm_num : (7 : ℕ).Prime)
    (by simp only [Nat.count_succ, Nat.count_zero]; norm_num)
  have h4 := nth_prime_eq (k := 4) (by norm_num : (11 : ℕ).Prime)
    (by simp only [Nat.count_succ, Nat.count_zero]; norm_num)
  have h5 := nth_prime_eq (k := 5) (by norm_num : (13 : ℕ).Prime)
    (by simp only [Nat.count_succ, Nat.count_zero]; norm_num)
  have h6 := nth_prime_eq (k := 6) (by norm_num : (17 : ℕ).Prime)
    (by simp only [Nat.count_succ, Nat.count_zero]; norm_num)
  have h7 := nth_prime_eq (k := 7) (by norm_num : (19 : ℕ).Prime)
    (by simp only [Nat.count_succ, Nat.count_zero]; norm_num)
  have h8 := nth_prime_eq (k := 8) (by norm_num : (23 : ℕ).Prime)
    (by simp only [Nat.count_succ, Nat.count_zero]; norm_num)
  have h9 := nth_prime_eq (k := 9) (by norm_num : (29 : ℕ).Prime)
    (by simp only [Nat.count_succ, Nat.count_zero]; norm_num)
  have h10 := nth_prime_eq (k := 10) (by norm_num : (31 : ℕ).Prime)
    (by simp only [Nat.count_succ, Nat.count_zero]; norm_num)
  norm_num [Finset.prod_range_succ, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-- A number with eleven distinct prime factors is at least 31#. -/
lemma ge_of_omega {m : ℕ} (h : omega m = 11) : 200560490130 ≤ m := by
  have hm : m ≠ 0 := by
    rintro rfl
    simp [omega] at h
  have h1 := prod_ge m.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  unfold omega at h
  rw [h, first_eleven] at h1
  exact h1.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m))

/-! ### The disproof -/

lemma omega_P : omega 200560490130 = 11 := by
  have e : (200560490130 : ℕ) =
      ∏ r ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ), r := by decide
  unfold omega
  rw [e, Nat.primeFactors_prod]
  · decide
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma omega_P1 : omega 200560490131 = 1 := by
  unfold omega
  rw [Nat.Prime.primeFactors prime_P1]
  rfl

lemma mem_P : (200560490130 : ℕ) ∈ {k | 1 ≤ k ∧ omega k * omega (k + 1) = 11} := by
  rw [Set.mem_setOf_eq]
  have e : (200560490130 + 1 : ℕ) = 200560490131 := by norm_num
  rw [e, omega_P, omega_P1]
  exact ⟨by norm_num, by norm_num⟩

lemma a_eleven_le : a 11 ≤ 200560490130 := Nat.sInf_le mem_P

lemma a_eleven_ne : a 11 ≠ b 11 := by
  intro hab
  have hne : {k | 1 ≤ k ∧ omega k * omega (k + 1) = 11}.Nonempty := ⟨200560490130, mem_P⟩
  have ha1 : 1 ≤ a 11 := (Nat.sInf_mem hne).1
  have hle : b 11 ≤ 200560490130 := hab ▸ a_eleven_le
  by_cases hb : {p | p.Prime ∧ Squarefree (p + 1) ∧ omega (p + 1) = 11}.Nonempty
  · have hmem : b 11 ∈ {p | p.Prime ∧ Squarefree (p + 1) ∧ omega (p + 1) = 11} :=
      Nat.sInf_mem hb
    obtain ⟨hq, -, hqo⟩ := hmem
    have hge := ge_of_omega hqo
    have hcases : b 11 = 200560490129 ∨ b 11 = 200560490130 := by omega
    rcases hcases with h | h
    · rw [h, show (200560490129 : ℕ) = 228737 * 876817 by norm_num] at hq
      exact Nat.not_prime_mul (by norm_num) (by norm_num) hq
    · rw [h] at hq
      have := hq.eq_one_or_self_of_dvd 2 (by norm_num)
      omega
  · have hb0 : b 11 = 0 := by
      unfold b
      rw [Set.not_nonempty_iff_eq_empty.mp hb, Nat.sInf_empty]
    omega

lemma omega_Pm1 : omega 200560490129 = 2 := by
  unfold omega
  rw [show (200560490129 : ℕ) = 228737 * 876817 by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  rfl

/-- The true value: a(11) = 31# = 200560490130 (the entry's data list 239378649509). -/
theorem a_eleven : a 11 = 200560490130 := by
  apply le_antisymm a_eleven_le
  obtain ⟨h1, h2⟩ : 1 ≤ a 11 ∧ omega (a 11) * omega (a 11 + 1) = 11 :=
    Nat.sInf_mem ⟨200560490130, mem_P⟩
  have h11 : omega (a 11) = 11 ∨ omega (a 11 + 1) = 11 := by
    have hd : omega (a 11) ∣ 11 := ⟨_, h2.symm⟩
    rcases (Nat.prime_eleven.eq_one_or_self_of_dvd _ hd) with h | h
    · right
      rw [h, one_mul] at h2
      exact h2
    · left
      exact h
  rcases h11 with h | h
  · exact ge_of_omega h
  · have hge := ge_of_omega h
    by_contra hlt
    have he : a 11 = 200560490129 := by omega
    rw [he, omega_Pm1, show (200560490129 + 1 : ℕ) = 200560490130 by norm_num, omega_P] at h2
    omega

/-- The conjecture "for p prime, a(p) = A098026(p)" is false. -/
theorem disproof : ¬ ∀ p : ℕ, p.Prime → a p = b p := by
  intro h
  exact a_eleven_ne (h 11 (by norm_num))

end OMA.S_oeis_a391216

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a391216.main) :=
  OMA.S_oeis_a391216.disproof
