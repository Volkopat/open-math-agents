import OMAStatements.S_oeis_a135051

-- Problem: A135051: Pyramid game person numbers that have integer solutions.
-- Upstream: formal-conjectures statements/oeis-a135051.lean:0 (declaration OMA.S_oeis_a135051.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: if k^2 = 4(8n - 7) then k = 2s is even and s^2 = 8n - 7; with n = 7 (mod 8),
-- s^2 = 49 (mod 64), which forces s = 7 or 25 (mod 32) (a check of the 64 residues). With
-- s = 32t + 7 one gets n = 128t^2 + 56t + 7, with s = 32t + 25 one gets n = 128t^2 + 200t + 79,
-- and conversely these n are terms. So the terms are f(2t) = 128t^2 + 56t + 7 and
-- f(2t+1) = 128t^2 + 200t + 79; f is strictly increasing with range the set of terms, hence
-- f = Nat.nth IsTerm (two strictly increasing maps on the naturals with the same range are equal).
-- Then a(n) = f(n-1), which is the closed form (split by the parity of n), and the g.f. follows
-- by comparing coefficients: (1-x)^3 (1+x)^2 = 1 - x - 2x^2 + 2x^3 + x^4 - x^5 annihilates
-- 32n^2 - 32n + 9 + (-1)^n (4n - 2).

namespace R02A135051

open OMA.S_oeis_a135051

theorem sq_mod (s : ℕ) (h : s ^ 2 % 64 = 49) : s % 32 = 7 ∨ s % 32 = 25 := by
  have h1 : s ^ 2 % 64 = (s % 64) ^ 2 % 64 := Nat.pow_mod s 2 64
  have h2 : s % 64 < 64 := Nat.mod_lt s (by norm_num)
  have h4 : s % 32 = s % 64 % 32 := by omega
  obtain ⟨r, hr⟩ : ∃ r, r = s % 64 := ⟨_, rfl⟩
  rw [← hr] at h1 h2 h4
  rw [h1, pow_two] at h
  rw [h4]
  interval_cases r <;> omega

theorem isTerm_iff (n : ℕ) : IsTerm n ↔
    ∃ t : ℕ, n = 128 * t ^ 2 + 56 * t + 7 ∨ n = 128 * t ^ 2 + 200 * t + 79 := by
  constructor
  · intro h
    unfold IsTerm at h
    obtain ⟨⟨k, hk⟩, hn⟩ := h
    obtain ⟨s, hs | hs⟩ := Nat.even_or_odd' k
    · subst hs
      have e1 : (2 * s) ^ 2 = 4 * s ^ 2 := by ring
      have hs2 : s ^ 2 = 8 * n - 7 := by omega
      have h64 : s ^ 2 % 64 = 49 := by omega
      rcases sq_mod s h64 with h7 | h25
      · obtain ⟨q, rfl⟩ : ∃ q, s = 32 * q + 7 := ⟨s / 32, by omega⟩
        have e2 : (32 * q + 7) ^ 2 = 1024 * q ^ 2 + 448 * q + 49 := by ring
        exact ⟨q, Or.inl (by omega)⟩
      · obtain ⟨q, rfl⟩ : ∃ q, s = 32 * q + 25 := ⟨s / 32, by omega⟩
        have e2 : (32 * q + 25) ^ 2 = 1024 * q ^ 2 + 1600 * q + 625 := by ring
        exact ⟨q, Or.inr (by omega)⟩
    · subst hs
      have e1 : (2 * s + 1) ^ 2 = 4 * (s ^ 2 + s) + 1 := by ring
      exfalso
      omega
  · intro h
    obtain ⟨t, rfl | rfl⟩ := h
    · unfold IsTerm
      have e : (64 * t + 14) ^ 2 = 4096 * t ^ 2 + 1792 * t + 196 := by ring
      exact ⟨⟨64 * t + 14, by omega⟩, by omega⟩
    · unfold IsTerm
      have e : (64 * t + 50) ^ 2 = 4096 * t ^ 2 + 6400 * t + 2500 := by ring
      exact ⟨⟨64 * t + 50, by omega⟩, by omega⟩

end R02A135051

open OMA.S_oeis_a135051 in
theorem OMA.solution : type_of% @OMA.S_oeis_a135051.main := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ j, f j = if j % 2 = 0 then 128 * (j / 2) ^ 2 + 56 * (j / 2) + 7
      else 128 * (j / 2) ^ 2 + 200 * (j / 2) + 79 := ⟨_, fun _ => rfl⟩
  have hf0 : ∀ t, f (2 * t) = 128 * t ^ 2 + 56 * t + 7 := by
    intro t
    rw [hf, if_pos (show 2 * t % 2 = 0 by omega), show 2 * t / 2 = t by omega]
  have hf1 : ∀ t, f (2 * t + 1) = 128 * t ^ 2 + 200 * t + 79 := by
    intro t
    rw [hf, if_neg (show ¬ ((2 * t + 1) % 2 = 0) by omega), show (2 * t + 1) / 2 = t by omega]
  have hmono : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro j
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [hf0 t, hf1 t]
      omega
    · rw [hf1 t, show 2 * t + 1 + 1 = 2 * (t + 1) by ring, hf0 (t + 1)]
      have e : (t + 1) ^ 2 = t ^ 2 + 2 * t + 1 := by ring
      omega
  have hrange : Set.range f = Set.ofPred IsTerm := by
    ext n
    constructor
    · intro h
      obtain ⟨j, rfl⟩ := Set.mem_range.mp h
      show IsTerm (f j)
      rw [R02A135051.isTerm_iff]
      obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
      · exact ⟨t, Or.inl (hf0 t)⟩
      · exact ⟨t, Or.inr (hf1 t)⟩
    · intro h
      have hP : IsTerm n := h
      rw [R02A135051.isTerm_iff] at hP
      obtain ⟨t, h1 | h1⟩ := hP
      · exact Set.mem_range.mpr ⟨2 * t, by rw [hf0 t, h1]⟩
      · exact Set.mem_range.mpr ⟨2 * t + 1, by rw [hf1 t, h1]⟩
  have hinf : (Set.ofPred IsTerm).Infinite := by
    rw [← hrange]
    exact Set.infinite_range_of_injective hmono.injective
  have hnth : Nat.nth IsTerm = f :=
    (StrictMono.range_inj (Nat.nth_strictMono hinf) hmono).mp
      (by rw [Nat.range_nth_of_infinite hinf, hrange])
  have ha : ∀ n : ℕ, 1 ≤ n → a n = f (n - 1) := by
    intro n hn
    rw [a, if_neg (show ¬ (n = 0) by omega), hnth]
  have hcz : ∀ n : ℕ, 1 ≤ n →
      (a n : ℤ) = 9 - 2 * (-1) ^ n + 4 * (-8 + (-1) ^ n) * n + 32 * n ^ 2 := by
    intro n hn
    rw [ha n hn]
    obtain ⟨t, rfl | rfl⟩ : ∃ t, n = 2 * t + 1 ∨ n = 2 * t + 2 := ⟨(n - 1) / 2, by omega⟩
    · have hodd : (-1 : ℤ) ^ (2 * t + 1) = -1 := by
        rw [pow_succ, pow_mul]
        norm_num
      rw [show 2 * t + 1 - 1 = 2 * t by omega, hf0 t, hodd]
      push_cast
      ring
    · have hev : (-1 : ℤ) ^ (2 * t + 2) = 1 := by
        rw [show 2 * t + 2 = 2 * (t + 1) by ring, pow_mul]
        norm_num
      rw [show 2 * t + 2 - 1 = 2 * t + 1 by omega, hf1 t, hev]
      push_cast
      ring
  have hcq : ∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = 9 - 2 * (-1) ^ n + 4 * (-8 + (-1) ^ n) * n + 32 * n ^ 2 := by
    intro n hn
    rw [ha n hn]
    obtain ⟨t, rfl | rfl⟩ : ∃ t, n = 2 * t + 1 ∨ n = 2 * t + 2 := ⟨(n - 1) / 2, by omega⟩
    · have hodd : (-1 : ℚ) ^ (2 * t + 1) = -1 := by
        rw [pow_succ, pow_mul]
        norm_num
      rw [show 2 * t + 1 - 1 = 2 * t by omega, hf0 t, hodd]
      push_cast
      ring
    · have hev : (-1 : ℚ) ^ (2 * t + 2) = 1 := by
        rw [show 2 * t + 2 = 2 * (t + 1) by ring, pow_mul]
        norm_num
      rw [show 2 * t + 2 - 1 = 2 * t + 1 by omega, hf1 t, hev]
      push_cast
      ring
  have a0 : a 0 = 0 := by
    rw [a, if_pos rfl]
  have a1 : a 1 = 7 := by
    have h := hcz 1 (by norm_num)
    norm_num at h
    exact_mod_cast h
  have a2 : a 2 = 79 := by
    have h := hcz 2 (by norm_num)
    norm_num at h
    exact_mod_cast h
  have a3 : a 3 = 191 := by
    have h := hcz 3 (by norm_num)
    norm_num at h
    exact_mod_cast h
  have a4 : a 4 = 407 := by
    have h := hcz 4 (by norm_num)
    norm_num at h
    exact_mod_cast h
  have a5 : a 5 = 631 := by
    have h := hcz 5 (by norm_num)
    norm_num at h
    exact_mod_cast h
  refine ⟨hcz, ?_⟩
  have e : PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2) =
      PowerSeries.mk (fun n => (a n : ℚ))
        - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
        + PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4
        - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 5 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    ring
  have e2 : (PowerSeries.X * (7 + 72 * PowerSeries.X + 98 * PowerSeries.X ^ 2 +
      72 * PowerSeries.X ^ 3 + 7 * PowerSeries.X ^ 4) : PowerSeries ℚ) =
      PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7
        + PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 72
        + PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 98
        + PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 72
        + PowerSeries.X ^ 5 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 72,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 98]
    ring
  rw [e, e2]
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge m 6 with hm | hm
  · interval_cases m <;> norm_num [a0, a1, a2, a3, a4, a5]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
    rw [if_pos (show 1 ≤ k + 6 by omega), if_pos (show 2 ≤ k + 6 by omega),
      if_pos (show 3 ≤ k + 6 by omega), if_pos (show 4 ≤ k + 6 by omega),
      if_pos (show 5 ≤ k + 6 by omega),
      if_neg (show ¬ (k + 6 = 1) by omega), if_neg (show ¬ (k + 6 = 2) by omega),
      if_neg (show ¬ (k + 6 = 3) by omega), if_neg (show ¬ (k + 6 = 4) by omega),
      if_neg (show ¬ (k + 6 = 5) by omega),
      show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega,
      show k + 6 - 5 = k + 1 by omega,
      hcq (k + 6) (by omega), hcq (k + 5) (by omega), hcq (k + 4) (by omega),
      hcq (k + 3) (by omega), hcq (k + 2) (by omega), hcq (k + 1) (by omega)]
    push_cast
    ring
