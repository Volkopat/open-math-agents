import OMAStatements.S_oeis_a281817
import Mathlib

namespace A281817P

open Finset

private def V (n k : ℕ) : ℤ :=
  ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (k.choose j : ℤ) * (j : ℤ) ^ n

private lemma pt (k j : ℕ) :
    (j : ℤ) * ((k + 1).choose j : ℤ) = ((k : ℤ) + 1) * (((k + 1).choose j : ℤ) - (k.choose j : ℤ)) := by
  cases j with
  | zero => simp
  | succ i =>
    have h1 : (k + 1) * k.choose i = (k + 1).choose (i + 1) * (i + 1) := Nat.add_one_mul_choose_eq k i
    have h2 : (k + 1).choose (i + 1) = k.choose i + k.choose (i + 1) := Nat.choose_succ_succ k i
    have e : (((k + 1).choose (i + 1) : ℕ) : ℤ) - (k.choose (i + 1) : ℤ) = (k.choose i : ℤ) := by
      rw [h2]; push_cast; ring
    rw [e]
    have h1' : ((k : ℤ) + 1) * (k.choose i : ℤ) = ((k + 1).choose (i + 1) : ℤ) * ((i : ℤ) + 1) := by
      exact_mod_cast h1
    push_cast
    linear_combination -h1'

private lemma V_eq (n k : ℕ) :
    V n k = (-1 : ℤ) ^ k * (k.factorial : ℤ) * (Nat.stirlingSecond n k : ℤ) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [V]
    | succ k =>
      have := Int.alternating_sum_range_choose (n := k + 1)
      simp only [V, pow_zero, mul_one, Nat.stirlingSecond_zero_succ]
      simpa using this
  | succ n ih =>
    cases k with
    | zero => simp [V]
    | succ k =>
      have hs : V (n + 1) (k + 1) = ((k : ℤ) + 1) * (V n (k + 1) - V n k) := by
        have hVk : V n k = ∑ j ∈ range (k + 1 + 1), (-1 : ℤ) ^ j * (k.choose j : ℤ) * (j : ℤ) ^ n := by
          rw [Finset.sum_range_succ, Nat.choose_succ_self]; simp [V]
        rw [hVk, V, V, ← sum_sub_distrib, mul_sum]
        apply sum_congr rfl
        intro j _
        rw [pow_succ]
        have := pt k j
        linear_combination ((-1 : ℤ) ^ j * (j : ℤ) ^ n) * this
      rw [hs, ih, ih, Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
      push_cast
      ring

private lemma Vz (p : ℕ) (n k : ℕ) :
    (-1 : ZMod p) ^ k * (k.factorial : ZMod p) * (Nat.stirlingSecond n k : ZMod p) =
      ∑ j ∈ range (k + 1), (-1 : ZMod p) ^ j * (k.choose j : ZMod p) * (j : ZMod p) ^ n := by
  have := congrArg (Int.cast : ℤ → ZMod p) (V_eq n k)
  push_cast [V] at this
  exact this.symm

private lemma G (p : ℕ) [hp : Fact p.Prime] (k b q : ℕ) (hb : 1 ≤ b) :
    (k.factorial : ZMod p) * (Nat.stirlingSecond (b + (p - 1) * q) k : ZMod p) =
      (k.factorial : ZMod p) * (Nat.stirlingSecond b k : ZMod p) := by
  have hj : ∀ x : ZMod p, x ^ (b + (p - 1) * q) = x ^ b := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [zero_pow (by omega), zero_pow (by omega)]
    · rw [pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, mul_one]
  have h1 := Vz p (b + (p - 1) * q) k
  have h2 := Vz p b k
  simp only [hj] at h1
  rw [← h2] at h1
  have hu : ((-1 : ZMod p) ^ k) * (-1 : ZMod p) ^ k = 1 := by rw [← mul_pow]; simp
  calc _ = ((-1 : ZMod p) ^ k * (-1 : ZMod p) ^ k) *
          ((k.factorial : ZMod p) * (Nat.stirlingSecond (b + (p - 1) * q) k : ZMod p)) := by
          rw [hu, one_mul]
    _ = (-1 : ZMod p) ^ k * ((-1 : ZMod p) ^ k * (k.factorial : ZMod p) *
          (Nat.stirlingSecond (b + (p - 1) * q) k : ZMod p)) := by ring
    _ = _ := by
      rw [h1]
      linear_combination ((k.factorial : ZMod p) * (Nat.stirlingSecond b k : ZMod p)) * hu

private lemma L (p : ℕ) [hp : Fact p.Prime] : ∀ r n : ℕ,
    (Nat.stirlingSecond (n + p) (p + r) : ZMod p) =
      (Nat.stirlingSecond (n + 1) (p + r) : ZMod p) + (Nat.stirlingSecond n r : ZMod p) := by
  have hp2 := hp.out.two_le
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  have hpz : ((p' : ZMod (p' + 1)) + 1) = 0 := by exact_mod_cast ZMod.natCast_self (p' + 1)
  have hstep : ∀ x, (Nat.stirlingSecond (x + 1) (p' + 1) : ZMod (p' + 1)) =
      Nat.stirlingSecond x p' := by
    intro x
    rw [Nat.stirlingSecond_succ_succ]
    push_cast
    rw [hpz, zero_mul, zero_add]
  have hfac : ((p'.factorial : ℕ) : ZMod (p' + 1)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (hp.out.dvd_factorial).not.mpr (by omega)
  intro r
  induction r with
  | zero =>
    intro n
    rw [add_zero, show n + (p' + 1) = (n + p') + 1 by ring, hstep, hstep]
    cases n with
    | zero =>
      simp [Nat.stirlingSecond_self, Nat.stirlingSecond_eq_zero_of_lt (show 0 < p' by omega)]
    | succ m =>
      have := G (p' + 1) p' (m + 1) 1 (by omega)
      simp only [Nat.add_sub_cancel, mul_one] at this
      have h := mul_left_cancel₀ hfac this
      rw [h]
      simp
  | succ r ih =>
    intro n
    have hk : p' + 1 + (r + 1) = p' + 1 + r + 1 := by ring
    induction n with
    | zero =>
      rw [Nat.stirlingSecond_eq_zero_of_lt (by omega), Nat.stirlingSecond_eq_zero_of_lt (by omega),
        Nat.stirlingSecond_eq_zero_of_lt (by omega)]
      simp
    | succ n ihn =>
      rw [hk] at ihn ⊢
      rw [show n + 1 + (p' + 1) = n + (p' + 1) + 1 by ring,
        Nat.stirlingSecond_succ_succ (n + (p' + 1)) (p' + 1 + r),
        Nat.stirlingSecond_succ_succ (n + 1) (p' + 1 + r),
        Nat.stirlingSecond_succ_succ n r]
      push_cast
      linear_combination ((p' : ZMod (p' + 1)) + 1 + r + 1) * ihn + ih n +
        (Nat.stirlingSecond n (r + 1) : ZMod (p' + 1)) * hpz

private lemma Kodd (p' : ℕ) [hp : Fact (p' + 1).Prime] (h2 : 2 ≤ p') (q : ℕ) :
    (Nat.stirlingSecond (2 + p' * q) (2 * p' + 1) : ZMod (p' + 1)) = 0 := by
  have hfac : ((p'.factorial : ℕ) : ZMod (p' + 1)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (hp.out.dvd_factorial).not.mpr (by omega)
  rw [show 2 * p' + 1 = p' + 1 + p' by ring]
  induction q with
  | zero => rw [Nat.stirlingSecond_eq_zero_of_lt (by omega)]; simp
  | succ q ih =>
    rw [show 2 + p' * (q + 1) = 1 + p' * q + (p' + 1) by ring, L (p' + 1) p' (1 + p' * q),
      show 1 + p' * q + 1 = 2 + p' * q by ring, ih]
    have hG := G (p' + 1) p' 1 q le_rfl
    simp only [Nat.add_sub_cancel] at hG
    rw [Nat.stirlingSecond_eq_zero_of_lt (show 1 < p' by omega), Nat.cast_zero, mul_zero] at hG
    rw [(mul_eq_zero.mp hG).resolve_left hfac]
    simp

private lemma s1 (n : ℕ) (hn : 1 ≤ n) : Nat.stirlingSecond n 1 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact Nat.stirlingSecond_one_right k

private lemma K2 (q : ℕ) : (Nat.stirlingSecond (2 + 2 * q) 3 : ZMod 2) = 0 := by
  have hL := L 2 1
  induction q with
  | zero => rw [Nat.stirlingSecond_eq_zero_of_lt (by norm_num)]; simp
  | succ q ih =>
    have h1 : (Nat.stirlingSecond (2 * q + 2 + 2) 3 : ZMod 2) =
        (Nat.stirlingSecond (2 * q + 2 + 1) 3 : ZMod 2) + (Nat.stirlingSecond (2 * q + 2) 1 : ZMod 2) :=
      hL (2 * q + 2)
    have h2 : (Nat.stirlingSecond (2 * q + 1 + 2) 3 : ZMod 2) =
        (Nat.stirlingSecond (2 * q + 1 + 1) 3 : ZMod 2) + (Nat.stirlingSecond (2 * q + 1) 1 : ZMod 2) :=
      hL (2 * q + 1)
    rw [show 2 + 2 * (q + 1) = 2 * q + 2 + 2 by ring, h1, show 2 * q + 2 + 1 = 2 * q + 1 + 2 by ring,
      h2, show 2 * q + 1 + 1 = 2 + 2 * q by ring, ih, s1 _ (by omega), s1 _ (by omega)]
    decide

private def c (k : ℕ) : ℕ := 2 * k.factorial / (k + 1)

private def A (m : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (m + 1)).filter Odd, c k * Nat.stirlingSecond m k

private lemma two_r_dvd (r : ℕ) (hr : 3 ≤ r) : 2 * r ∣ r.factorial := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [Nat.factorial_succ, mul_comm 2]
  exact Nat.mul_dvd_mul_left _ (Nat.dvd_factorial (by norm_num) (by omega))

private lemma D1 (k : ℕ) (hk : Odd k) : (k + 1) ∣ 2 * k.factorial := by
  obtain ⟨t, rfl⟩ := hk
  rcases (show t = 0 ∨ t = 1 ∨ 2 ≤ t by omega) with h | h | h
  · subst h; decide
  · subst h; decide
  · have : 2 * (t + 1) ∣ (2 * t + 1).factorial :=
      (two_r_dvd (t + 1) (by omega)).trans (Nat.factorial_dvd_factorial (by omega))
    rw [show 2 * t + 1 + 1 = 2 * (t + 1) by ring]
    exact this.trans (Nat.dvd_mul_left _ _)

private lemma D2 (p k : ℕ) (hp : p.Prime) (hk : Odd k) (hpk : p ≤ k) (hne : k ≠ 2 * p - 1) :
    p * (k + 1) ∣ 2 * k.factorial := by
  have hp2 := hp.two_le
  by_cases hd : p ∣ k + 1
  · by_cases h5 : k = 5
    · subst h5
      have hp5 : p ≤ 5 := hpk
      interval_cases p
      · decide
      · omega
      · norm_num at hp
      · omega
    obtain ⟨t, ht⟩ := hd
    have ht3 : 3 ≤ t := by
      rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ 3 ≤ t by omega) with h | h | h | h
      · subst h; omega
      · subst h; omega
      · subst h; omega
      · exact h
    have h2p : 2 * p ≤ k := by nlinarith
    obtain ⟨b, hb⟩ : ∃ b, k = 2 * p + b := ⟨k - 2 * p, by omega⟩
    have hA : (2 * p).factorial * b.factorial ∣ k.factorial := by
      rw [hb]; exact Nat.factorial_mul_factorial_dvd_factorial_add _ _
    have hB : p * (2 * p) ∣ (2 * p).factorial := by
      obtain ⟨u, hu⟩ : ∃ u, 2 * p = u + 1 := ⟨2 * p - 1, by omega⟩
      rw [hu, Nat.factorial_succ, mul_comm p]
      exact Nat.mul_dvd_mul_left _ (Nat.dvd_factorial hp.pos (by omega))
    have hC : t ∣ 4 * b.factorial := by
      by_cases htb : t ≤ b
      · exact (Nat.dvd_factorial (by omega) htb).mul_left 4
      · have hlt : b < t := by omega
        have hp23 : p = 2 ∨ p = 3 := by
          by_contra hc
          have h4 : 4 ≤ p := by omega
          nlinarith
        rcases hp23 with h | h
        · subst h
          have : t = 4 := by omega
          rw [this]; exact Nat.dvd_mul_right 4 _
        · subst h
          obtain ⟨j, hj⟩ := hk
          omega
    rw [ht]
    have h1 : (p * (2 * p)) * t ∣ (2 * p).factorial * (4 * b.factorial) := Nat.mul_dvd_mul hB hC
    have h2 : (2 * p).factorial * (4 * b.factorial) ∣ 2 * (2 * k.factorial) := by
      obtain ⟨w, hw⟩ := hA
      exact ⟨w, by rw [hw]; ring⟩
    have h3 : 2 * (p * (p * t)) ∣ 2 * (2 * k.factorial) := by
      have : p * (2 * p) * t = 2 * (p * (p * t)) := by ring
      rw [← this]; exact h1.trans h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  · have hc : Nat.Coprime p (k + 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hd
    exact hc.mul_dvd_of_dvd_of_dvd ((Nat.dvd_factorial hp.pos hpk).mul_left 2) (D1 k hk)

private lemma c_dvd (p b : ℕ) (hp : p.Prime) (hb : Odd b) (hpb : p ≤ b) (hne : b ≠ 2 * p - 1) :
    p ∣ c b := by
  have h1 := D2 p b hp hb hpb hne
  have h2 : c b * (b + 1) = 2 * b.factorial := Nat.div_mul_cancel (D1 b hb)
  rw [← h2] at h1
  exact Nat.dvd_of_mul_dvd_mul_right (by omega) h1

private lemma aA (m : ℕ) : OMA.S_oeis_a281817.a m = ((A m : ℕ) : ℚ) := by
  unfold OMA.S_oeis_a281817.a A
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hko : Odd k := (Finset.mem_filter.mp hk).2
  have hc : (c k : ℚ) * ((k : ℚ) + 1) = 2 * (k.factorial : ℚ) := by
    have := Nat.div_mul_cancel (D1 k hko)
    exact_mod_cast this
  have hpos : (k : ℚ) + 1 ≠ 0 := by positivity
  rw [show (c k : ℚ) = 2 * (k.factorial : ℚ) / ((k : ℚ) + 1) from by rw [eq_div_iff hpos]; exact hc]
  ring

private lemma core (p' q : ℕ) [hp : Fact (p' + 1).Prime] (hev : Even (2 + p' * q)) :
    ((A (2 + p' * q) : ℕ) : ZMod (p' + 1)) = 1 := by
  have hp2 : 1 ≤ p' := by have := hp.out.two_le; omega
  unfold A
  push_cast
  rw [Finset.sum_eq_single 1]
  · rw [s1 _ (by omega)]
    have : c 1 = 1 := by decide
    rw [this]; simp
  · intro b hb hb1
    rw [Finset.mem_filter, Finset.mem_range] at hb
    obtain ⟨hbm, hbo⟩ := hb
    have hb3 : 3 ≤ b := by obtain ⟨j, hj⟩ := hbo; omega
    rcases lt_or_ge b (p' + 1) with hlt | hge
    · have hG := G (p' + 1) b 2 q (by norm_num)
      simp only [Nat.add_sub_cancel] at hG
      rw [Nat.stirlingSecond_eq_zero_of_lt (show 2 < b by omega), Nat.cast_zero, mul_zero] at hG
      have hfac : ((b.factorial : ℕ) : ZMod (p' + 1)) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact (hp.out.dvd_factorial).not.mpr (by omega)
      rw [(mul_eq_zero.mp hG).resolve_left hfac]
      simp
    · by_cases hbe : b = 2 * (p' + 1) - 1
      · have hb' : b = 2 * p' + 1 := by omega
        rw [hb']
        rcases (show p' = 1 ∨ 2 ≤ p' by omega) with h1 | h2
        · subst h1
          obtain ⟨r, hr⟩ := hev
          have hK : ((Nat.stirlingSecond (2 + 1 * q) (2 * 1 + 1) : ℕ) : ZMod (1 + 1)) = 0 := by
            have := K2 (r - 1)
            rw [show 2 + 2 * (r - 1) = 2 + 1 * q by omega] at this
            exact this
          rw [hK, mul_zero]
        · rw [Kodd p' h2 q, mul_zero]
      · have := c_dvd (p' + 1) b hp.out hbo hge hbe
        rw [(ZMod.natCast_eq_zero_iff _ _).mpr this]
        simp
  · intro h
    exfalso
    apply h
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, odd_one⟩

private lemma claim1 : ∀ n : ℕ, 1 ≤ n → ∀ p : ℕ, p.Prime → (p - 1) ∣ (2 * n - 2) →
    ∃ m : ℤ, OMA.S_oeis_a281817.a (2 * n) - 1 = (p : ℚ) * m := by
  intro n hn p hp hd
  obtain ⟨q, hq⟩ := hd
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  haveI : Fact (p' + 1).Prime := ⟨hp⟩
  simp only [Nat.add_sub_cancel] at hq
  obtain ⟨t, ht⟩ : ∃ t, t = p' * q := ⟨_, rfl⟩
  rw [← ht] at hq
  have hm : 2 * n = 2 + p' * q := by rw [← ht]; omega
  have hev : Even (2 + p' * q) := ⟨n, by rw [← hm]; ring⟩
  have hc := core p' q hev
  rw [← hm] at hc
  have hdvd : (((p' + 1 : ℕ)) : ℤ) ∣ ((A (2 * n) : ℕ) : ℤ) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hc]
    ring
  obtain ⟨z, hz⟩ := hdvd
  refine ⟨z, ?_⟩
  rw [aA]
  have : (((A (2 * n) : ℕ) : ℤ) : ℚ) - 1 = (((p' + 1 : ℕ) : ℤ) : ℚ) * z := by exact_mod_cast hz
  push_cast at this ⊢
  linarith

end A281817P

theorem OMA.solution : type_of% @OMA.S_oeis_a281817.main := by
  refine ⟨A281817P.claim1, fun p hp => A281817P.claim1 p hp.one_lt.le p hp ⟨2, by omega⟩⟩
