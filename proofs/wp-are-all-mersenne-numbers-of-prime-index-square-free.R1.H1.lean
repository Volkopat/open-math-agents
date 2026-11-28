import OMAReductions.R_wp_are_all_mersenne_numbers_of_prime_index_square_free_R1
import Mathlib
-- Credit: @LordMike

def mersAllRange (f : ℕ → ℕ → Bool) (lo : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => f lo n && mersAllRange f lo n

theorem mersAllRange_spec (f : ℕ → ℕ → Bool) (lo n : ℕ) :
    mersAllRange f lo n = true ↔ ∀ x < n, f lo x = true := by
  induction n with
  | zero => simp [mersAllRange]
  | succ n ih =>
    simp only [mersAllRange, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rcases Nat.lt_succ_iff_lt_or_eq.1 hx with h | h
      · exact h2 x h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun x hx => h x (Nat.lt_succ_of_lt hx)⟩

def mersChk (lo x : ℕ) : Bool :=
  decide (lo + x < 2 ∨ 2 ^ (lo + x - 1) % (lo + x) ^ 2 ≠ 1 ∨ lo + x = 1093 ∨ lo + x = 3511)

theorem mers_block (lo n : ℕ) (h : mersAllRange mersChk lo n = true) :
    ∀ q, lo ≤ q → q < lo + n → q < 2 ∨ 2 ^ (q - 1) % q ^ 2 ≠ 1 ∨ q = 1093 ∨ q = 3511 := by
  intro q h1 h2
  have := (mersAllRange_spec mersChk lo n).1 h (q - lo) (by omega)
  simpa [mersChk, show lo + (q - lo) = q by omega] using this

theorem mers_b0 : mersAllRange mersChk 0 20000 = true := by decide +kernel
theorem mers_b1 : mersAllRange mersChk 20000 20000 = true := by decide +kernel
theorem mers_b2 : mersAllRange mersChk 40000 20000 = true := by decide +kernel
theorem mers_b3 : mersAllRange mersChk 60000 20000 = true := by decide +kernel
theorem mers_b4 : mersAllRange mersChk 80000 20001 = true := by decide +kernel

theorem mers_small : ∀ q, q < 100001 → q < 2 ∨ 2 ^ (q - 1) % q ^ 2 ≠ 1 ∨ q = 1093 ∨ q = 3511 := by
  intro q hq
  by_cases h0 : q < 20000
  · exact mers_block 0 20000 mers_b0 q (by omega) (by omega)
  by_cases h1 : q < 40000
  · exact mers_block 20000 20000 mers_b1 q (by omega) (by omega)
  by_cases h2 : q < 60000
  · exact mers_block 40000 20000 mers_b2 q (by omega) (by omega)
  by_cases h3 : q < 80000
  · exact mers_block 60000 20000 mers_b3 q (by omega) (by omega)
  · exact mers_block 80000 20001 mers_b4 q (by omega) (by omega)

def mersChk2 (M N a b c lo x : ℕ) : Bool :=
  decide (¬ (lo + x ∣ N) ∨ 2 ^ (lo + x) % M ≠ 1 ∨ lo + x = a ∨ lo + x = b ∨ lo + x = c)

theorem mers_1093 : ∀ p, p ∣ 1092 → 2 ^ p % 1093 = 1 → p = 364 ∨ p = 728 ∨ p = 1092 := by
  have h := (mersAllRange_spec (mersChk2 1093 1092 364 728 1092) 0 1093).1 (by decide +kernel)
  intro p hp h2
  have hp1 : p ≤ 1092 := Nat.le_of_dvd (by norm_num) hp
  have := h p (by omega)
  simp only [mersChk2, zero_add, decide_eq_true_eq] at this
  rcases this with h3 | h3 | h3 | h3 | h3
  · exact absurd hp h3
  · exact absurd h2 h3
  · exact Or.inl h3
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h3)

theorem mers_3511 : ∀ p, p ∣ 3510 → 2 ^ p % 3511 = 1 → p = 1755 ∨ p = 3510 := by
  have h := (mersAllRange_spec (mersChk2 3511 3510 1755 3510 3510) 0 3511).1 (by decide +kernel)
  intro p hp h2
  have hp1 : p ≤ 3510 := Nat.le_of_dvd (by norm_num) hp
  have := h p (by omega)
  simp only [mersChk2, zero_add, decide_eq_true_eq] at this
  rcases this with h3 | h3 | h3 | h3 | h3
  · exact absurd hp h3
  · exact absurd h2 h3
  · exact Or.inl h3
  · exact Or.inr h3
  · exact Or.inr h3

theorem mers_order (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : q ∣ 2 ^ p - 1) : p ∣ q - 1 := by
  have := Fact.mk hq
  have hq2 : q ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ p := dvd_pow_self 2 hp.ne_zero
    have h1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
    omega
  have h1 : (2 : ZMod q) ^ p = 1 := by
    have h1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
    have := (ZMod.natCast_eq_zero_iff (2 ^ p - 1) q).2 h
    push_cast [Nat.cast_sub h1] at this
    exact sub_eq_zero.1 this
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h0
    have := (ZMod.natCast_eq_zero_iff 2 q).1 (by exact_mod_cast h0)
    have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 this
    exact hq2 this
  have hord : orderOf (2 : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one h1
  have hne : orderOf (2 : ZMod q) ≠ 1 := by
    intro h3
    rw [orderOf_eq_one_iff] at h3
    have h4 : (1 : ZMod q) = 0 := by
      have : (2 : ZMod q) - 1 = 1 := by norm_num
      rw [h3] at this
      simpa using this.symm
    exact one_ne_zero h4
  have hop : orderOf (2 : ZMod q) = p := by
    rcases (Nat.dvd_prime hp).1 hord with h | h
    · exact absurd h hne
    · exact h
  rw [← hop]
  exact ZMod.orderOf_dvd_card_sub_one h2

theorem OMA.solution : OMA.R_wp_are_all_mersenne_numbers_of_prime_index_square_free_R1.H1 := by
  intro p q hp hq hd
  have hq2 : 2 ≤ q := hq.two_le
  have hp2 : 2 ≤ p := hp.two_le
  have hqd : q ∣ 2 ^ p - 1 := dvd_trans (dvd_pow_self q two_ne_zero) hd
  have h1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  obtain ⟨k, hk⟩ := mers_order p q hp hq hqd
  have hqq : 1 < q ^ 2 := by nlinarith
  have hmod : 2 ^ p % q ^ 2 = 1 := by
    have := (Nat.modEq_iff_dvd' h1).2 hd
    unfold Nat.ModEq at this
    rw [Nat.mod_eq_of_lt hqq] at this
    exact this.symm
  have hW : 2 ^ (q - 1) % q ^ 2 = 1 := by
    rw [hk, pow_mul, Nat.pow_mod, hmod, one_pow, Nat.mod_eq_of_lt hqq]
  refine ⟨hW, ?_, ?_⟩
  · have hq_odd : q ≠ 2 := by
      rintro rfl
      have : 2 ∣ 2 ^ p := dvd_pow_self 2 hp.ne_zero
      omega
    have hp_odd : p ≠ 2 := by
      rintro rfl
      have h4 : q ^ 2 ≤ 3 := Nat.le_of_dvd (by norm_num) (by simpa using hd)
      nlinarith
    have hqodd : q % 2 = 1 := hq.eq_one_or_self_of_dvd 2 |> fun _ => by
      rcases hq.eq_two_or_odd with h | h
      · exact absurd h hq_odd
      · exact h
    have hpodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp_odd
      · exact h
    have hkeven : 2 ∣ k := by
      have h2 : 2 ∣ p * k := by omega
      have hc : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp_odd)
      exact hc.dvd_of_dvd_mul_left h2
    obtain ⟨m, hm⟩ := hkeven
    have : q = 2 * p * m + 1 := by
      have : q - 1 = p * (2 * m) := by rw [hk, hm]
      have h5 : p * (2 * m) = 2 * p * m := by ring
      omega
    rw [this, Nat.mul_add_mod]
    have : 1 < 2 * p := by omega
    exact Nat.mod_eq_of_lt this
  · by_contra hlt
    push Not at hlt
    have hmod2 : 2 ^ p % q = 1 := by
      have := (Nat.modEq_iff_dvd' h1).2 hqd
      unfold Nat.ModEq at this
      rw [Nat.mod_eq_of_lt hq.one_lt] at this
      exact this.symm
    rcases mers_small q (by omega) with h | h | h | h
    · omega
    · exact h hW
    · subst h
      have hdv : p ∣ 1092 := by exact Dvd.intro k hk.symm
      rcases mers_1093 p hdv hmod2 with h | h | h <;> subst h <;> norm_num at hp
    · subst h
      have hdv : p ∣ 3510 := by exact Dvd.intro k hk.symm
      rcases mers_3511 p hdv hmod2 with h | h <;> subst h <;> norm_num at hp
