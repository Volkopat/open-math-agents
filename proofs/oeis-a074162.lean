import OMAStatements.S_oeis_a074162

-- Problem: A074162: a(1) = 1; a(n) = smallest multiple of n (>n) using all nonprime digits (1,4,6,8,9 and 0) if n is a prime else using all prime digits and 1 if n is composite; or 0 if no such number exists.
-- Upstream: formal-conjectures statements/oeis-a074162.lean:0 (declaration OMA.S_oeis_a074162.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: n = 15625k is composite, so the digits must lie in {1, 2, 3, 5, 7}. A multiple m > n
-- of 15625 has at least 5 digits, and a sixth when m >= 100000. With c(i) = m mod 10^i and
-- e(i) = digit i of m, c(i+1) = c(i) + 10^i e(i) and 5^(i+1) divides c(i+1) (as 5^6 | m). Level by
-- level (L0 to L5): c(1) = 5, c(2) is 25 or 75, c(3) is 125 or 375, c(4) = 3125, c(5) = 53125
-- (not a multiple of 5^6, so m >= 100000), and no digit e(5) is possible.

set_option maxHeartbeats 4000000 in
open OMA.S_oeis_a074162 in
theorem OMA.solution : type_of% @OMA.S_oeis_a074162.main := by
  have step : ∀ x : ℕ, 1 ≤ x → (∀ d ∈ Nat.digits 10 x, d ∈ ({1, 2, 3, 5, 7} : Finset ℕ)) →
      (x % 10 = 1 ∨ x % 10 = 2 ∨ x % 10 = 3 ∨ x % 10 = 5 ∨ x % 10 = 7) ∧
      (∀ d ∈ Nat.digits 10 (x / 10), d ∈ ({1, 2, 3, 5, 7} : Finset ℕ)) := by
    intro x hx h
    rw [Nat.digits_def' (show 1 < 10 by norm_num) (show 0 < x by omega)] at h
    have h0 := h (x % 10) (List.mem_cons.mpr (Or.inl rfl))
    simp only [Finset.mem_insert, Finset.mem_singleton] at h0
    exact ⟨h0, fun d hd => h d (List.mem_cons.mpr (Or.inr hd))⟩
  have dig : ∀ i x : ℕ, 10 ^ i ≤ x → (∀ d ∈ Nat.digits 10 x, d ∈ ({1, 2, 3, 5, 7} : Finset ℕ)) →
      (x / 10 ^ i % 10 = 1 ∨ x / 10 ^ i % 10 = 2 ∨ x / 10 ^ i % 10 = 3 ∨
        x / 10 ^ i % 10 = 5 ∨ x / 10 ^ i % 10 = 7) := by
    intro i
    induction i with
    | zero =>
      intro x hx h
      rw [pow_zero] at hx
      rw [pow_zero, Nat.div_one]
      exact (step x hx h).1
    | succ i ih =>
      intro x hx h
      have hx1 : 1 ≤ x := le_trans (Nat.one_le_pow (i + 1) 10 (by norm_num)) hx
      have e : x / 10 ^ (i + 1) = x / 10 / 10 ^ i := by
        rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
      rw [e]
      refine ih (x / 10) ?_ (step x hx1 h).2
      rw [Nat.le_div_iff_mul_le (show 0 < 10 by norm_num), ← pow_succ]
      exact hx
  have Pg : ∀ x i : ℕ, 5 ^ 6 ∣ x → i ≤ 5 → 5 ^ (i + 1) ∣ x % 10 ^ (i + 1) := by
    intro x i hx hi
    rw [Nat.dvd_mod_iff (pow_dvd_pow_of_dvd (show (5 : ℕ) ∣ 10 by norm_num) (i + 1))]
    exact (pow_dvd_pow (5 : ℕ) (show i + 1 ≤ 6 by omega)).trans hx
  have L0 : ∀ b d c : ℕ, c = b + 10 ^ 0 * d → 5 ^ (0 + 1) ∣ c → b = 0 →
      (d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 5 ∨ d = 7) → c = 5 := by
    intro b d c hc hdv hb hd
    subst hb
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> omega
  have L1 : ∀ b d c : ℕ, c = b + 10 ^ 1 * d → 5 ^ (1 + 1) ∣ c → b = 5 →
      (d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 5 ∨ d = 7) → c = 25 ∨ c = 75 := by
    intro b d c hc hdv hb hd
    subst hb
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> omega
  have L2 : ∀ b d c : ℕ, c = b + 10 ^ 2 * d → 5 ^ (2 + 1) ∣ c → (b = 25 ∨ b = 75) →
      (d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 5 ∨ d = 7) → c = 125 ∨ c = 375 := by
    intro b d c hc hdv hb hd
    rcases hb with rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl | rfl <;> omega
  have L3 : ∀ b d c : ℕ, c = b + 10 ^ 3 * d → 5 ^ (3 + 1) ∣ c → (b = 125 ∨ b = 375) →
      (d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 5 ∨ d = 7) → c = 3125 := by
    intro b d c hc hdv hb hd
    rcases hb with rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl | rfl <;> omega
  have L4 : ∀ b d c : ℕ, c = b + 10 ^ 4 * d → 5 ^ (4 + 1) ∣ c → b = 3125 →
      (d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 5 ∨ d = 7) → c = 53125 := by
    intro b d c hc hdv hb hd
    subst hb
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> omega
  have L5 : ∀ b d c : ℕ, c = b + 10 ^ 5 * d → 5 ^ (5 + 1) ∣ c → b = 53125 →
      (d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 5 ∨ d = 7) → False := by
    intro b d c hc hdv hb hd
    subst hb
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> omega
  intro k hk
  rw [show (5 : ℕ) ^ 6 = 15625 by norm_num]
  have hnp : ¬ Nat.Prime (k * 15625) := by
    intro hp
    rcases hp.eq_one_or_self_of_dvd 5 ⟨k * 3125, by ring⟩ with h | h <;> omega
  have hD : D (k * 15625) = {1, 2, 3, 5, 7} := by
    unfold D
    rw [if_neg hnp]
  unfold a
  rw [if_neg (show ¬ (k * 15625 = 1) by omega)]
  apply Nat.sInf_eq_zero.mpr
  right
  apply Set.eq_empty_of_forall_notMem
  intro m hm
  have hm' : k * 15625 < m ∧ k * 15625 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d ∈ D (k * 15625) := hm
  rw [hD] at hm'
  obtain ⟨hlt, hdvd, hdig⟩ := hm'
  have d0 := dig 0 m (by omega) hdig
  have d1 := dig 1 m (by omega) hdig
  have d2 := dig 2 m (by omega) hdig
  have d3 := dig 3 m (by omega) hdig
  have d4 := dig 4 m (by omega) hdig
  have d5 : m < 10 ^ 5 ∨ (m / 10 ^ 5 % 10 = 1 ∨ m / 10 ^ 5 % 10 = 2 ∨ m / 10 ^ 5 % 10 = 3 ∨
      m / 10 ^ 5 % 10 = 5 ∨ m / 10 ^ 5 % 10 = 7) := by
    by_cases hm5 : m < 10 ^ 5
    · exact Or.inl hm5
    · exact Or.inr (dig 5 m (by omega) hdig)
  have h15 : 15625 ∣ m := Dvd.dvd.trans (⟨k, by ring⟩ : 15625 ∣ k * 15625) hdvd
  have h56 : 5 ^ 6 ∣ m := by
    rw [show (5 : ℕ) ^ 6 = 15625 by norm_num]
    exact h15
  have P : ∀ i : ℕ, i ≤ 5 → 5 ^ (i + 1) ∣ m % 10 ^ (i + 1) := fun i hi => Pg m i h56 hi
  have B : ∀ i : ℕ, m % 10 ^ (i + 1) = m % 10 ^ i + 10 ^ i * (m / 10 ^ i % 10) :=
    fun i => Nat.mod_pow_succ
  have c0 : m % 10 ^ 0 = 0 := by
    rw [pow_zero, Nat.mod_one]
  have c1 := L0 _ _ _ (B 0) (P 0 (by norm_num)) c0 d0
  have c2 := L1 _ _ _ (B 1) (P 1 (by norm_num)) c1 d1
  have c3 := L2 _ _ _ (B 2) (P 2 (by norm_num)) c2 d2
  have c4 := L3 _ _ _ (B 3) (P 3 (by norm_num)) c3 d3
  have c5 := L4 _ _ _ (B 4) (P 4 (by norm_num)) c4 d4
  rcases d5 with hm5 | hd5
  · have hmm : m % 10 ^ (4 + 1) = m := Nat.mod_eq_of_lt hm5
    have hm' : m = 53125 := hmm.symm.trans c5
    rw [hm'] at h56
    exact absurd h56 (by norm_num)
  · exact L5 _ _ _ (B 5) (P 5 (by norm_num)) c5 hd5
