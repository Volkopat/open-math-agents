import OMAStatements.S_oeis_a210374

-- Problem: A210374: Number of 2 X 2 matrices with all terms in {0,1,...,n} and (sum of terms) = n+2.
-- Upstream: formal-conjectures statements/oeis-a210374.lean:0 (declaration OMA.S_oeis_a210374.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for fixed w, x, y there is one z exactly when 2 <= w + x + y <= n + 2, and for
-- s = w + x the number of y is h(n, s) = n - 1, n, n + 3 - s (truncated at 0) for s = 0, 1, >= 2.
-- For n = p + 1 the sum over x is then 2p + 1 + (p + 2 + ... + 3), (p + 1) + (p + 2) + ..., and
-- M(M + 1)/2 with M = p + 2 - w for w >= 2; summing over w with the formulas for the sums of
-- 1, w, w^2 gives a(n) = (n^3 + 12n^2 + 47n - 36)/6 for n >= 1. The recurrence is the vanishing
-- fourth difference of this cubic, and the generating function follows by comparing coefficients.

open OMA.S_oeis_a210374 in
theorem OMA.solution : type_of% @OMA.S_oeis_a210374.main := by
  obtain ⟨h, hh⟩ : ∃ h : ℕ → ℕ → ℕ, ∀ n s,
      h n s = if s = 0 then n - 1 else if s = 1 then n else n + 3 - s := ⟨_, fun _ _ => rfl⟩
  have hN : ∀ n s : ℕ, 2 ≤ s → h n s = n + 3 - s := by
    intro n s h2
    rw [hh, if_neg (show ¬ s = 0 by omega), if_neg (show ¬ s = 1 by omega)]
  have innerz : ∀ n w x y : ℕ, (∑ z ∈ Finset.Icc 0 n,
      (if w + x + y + z = n + 2 then 1 else 0 : ℕ)) =
      if 2 ≤ w + x + y ∧ w + x + y ≤ n + 2 then 1 else 0 := by
    intro n w x y
    by_cases hc : 2 ≤ w + x + y ∧ w + x + y ≤ n + 2
    · rw [if_pos hc, Finset.sum_eq_single (n + 2 - (w + x + y))]
      · rw [if_pos (show w + x + y + (n + 2 - (w + x + y)) = n + 2 by omega)]
      · intro z _ hz
        rw [if_neg (show ¬ (w + x + y + z = n + 2) by omega)]
      · intro hn
        exact (hn (Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)).elim
    · rw [if_neg hc]
      apply Finset.sum_eq_zero
      intro z hz
      rw [Finset.mem_Icc] at hz
      rw [if_neg (show ¬ (w + x + y + z = n + 2) by omega)]
  have hy : ∀ n s : ℕ, (∑ y ∈ Finset.Icc 0 n,
      (if 2 ≤ s + y ∧ s + y ≤ n + 2 then 1 else 0 : ℕ)) = h n s := by
    intro n s
    by_cases hbig : n + 2 < s
    · rw [Finset.sum_eq_zero, hN n s (by omega)]
      · omega
      · intro y _
        rw [if_neg (show ¬ (2 ≤ s + y ∧ s + y ≤ n + 2) by omega)]
    · rw [← Finset.card_filter]
      by_cases h0 : s = 0
      · have e : (Finset.Icc 0 n).filter (fun y => 2 ≤ s + y ∧ s + y ≤ n + 2) =
            Finset.Icc 2 n := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · intro hx
            omega
          · intro hx
            omega
        rw [e, Nat.card_Icc, hh, if_pos h0]
        omega
      · by_cases h1 : s = 1
        · have e : (Finset.Icc 0 n).filter (fun y => 2 ≤ s + y ∧ s + y ≤ n + 2) =
              Finset.Icc 1 n := by
            ext y
            simp only [Finset.mem_filter, Finset.mem_Icc]
            constructor
            · intro hx
              omega
            · intro hx
              omega
          rw [e, Nat.card_Icc, hh, if_neg h0, if_pos h1]
          omega
        · have e : (Finset.Icc 0 n).filter (fun y => 2 ≤ s + y ∧ s + y ≤ n + 2) =
              Finset.Icc 0 (n + 2 - s) := by
            ext y
            simp only [Finset.mem_filter, Finset.mem_Icc]
            constructor
            · intro hx
              omega
            · intro hx
              omega
          rw [e, Nat.card_Icc, hh, if_neg h0, if_neg h1]
          omega
  have perwx : ∀ n w x : ℕ, (∑ y ∈ Finset.Icc 0 n, ∑ z ∈ Finset.Icc 0 n,
      (if w + x + y + z = n + 2 then 1 else 0 : ℕ)) = h n (w + x) := by
    intro n w x
    rw [Finset.sum_congr rfl (fun y _ => innerz n w x y)]
    exact hy n (w + x)
  have hA0 : ∀ n : ℕ, a n = ∑ w ∈ Finset.Icc 0 n, ∑ x ∈ Finset.Icc 0 n, h n (w + x) := by
    intro n
    unfold a
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_product]
    exact perwx n w x
  have hI : ∀ n : ℕ, Finset.Icc 0 n = Finset.range (n + 1) := by
    intro n
    ext x
    simp only [Finset.mem_Icc, Finset.mem_range]
    constructor
    · intro hx
      omega
    · intro hx
      omega
  have hAq : ∀ n : ℕ, (a n : ℚ) =
      ∑ w ∈ Finset.range (n + 1), ∑ x ∈ Finset.range (n + 1), (h n (w + x) : ℚ) := by
    intro n
    rw [hA0 n, hI n]
    simp only [Nat.cast_sum]
  have quad : ∀ (A B C : ℚ) (N : ℕ), ∑ w ∈ Finset.range N, (A + B * (w : ℚ) + C * (w : ℚ) ^ 2) =
      (N : ℚ) * A + B * ((N : ℚ) * ((N : ℚ) - 1) / 2)
        + C * ((N : ℚ) * ((N : ℚ) - 1) * (2 * (N : ℚ) - 1) / 6) := by
    intro A B C N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have tri : ∀ M N : ℕ, M ≤ N →
      ∑ x ∈ Finset.range N, ((M - x : ℕ) : ℚ) = (M : ℚ) * ((M : ℚ) + 1) / 2 := by
    intro M N hMN
    obtain ⟨j, rfl⟩ : ∃ j, N = M + j := ⟨N - M, by omega⟩
    rw [Finset.sum_range_add]
    have z : ∑ x ∈ Finset.range j, ((M - (M + x) : ℕ) : ℚ) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [show M - (M + x) = 0 by omega, Nat.cast_zero]
    have t : ∀ x ∈ Finset.range M,
        ((M - x : ℕ) : ℚ) = (M : ℚ) + (-1) * (x : ℚ) + 0 * (x : ℚ) ^ 2 := by
      intro x hx
      have hx' := Finset.mem_range.mp hx
      rw [Nat.cast_sub hx'.le]
      ring
    rw [z, Finset.sum_congr rfl t, quad]
    ring
  have peel2 : ∀ (F : ℕ → ℚ) (p : ℕ), ∑ w ∈ Finset.range (p + 2), F w =
      F 0 + F 1 + ∑ w ∈ Finset.range p, F (w + 2) := by
    intro F p
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    show ∑ w ∈ Finset.range p, F (w + 2) + F 1 + F 0 =
      F 0 + F 1 + ∑ w ∈ Finset.range p, F (w + 2)
    ring
  have hq : ∀ n s : ℕ, 2 ≤ s → s ≤ n + 3 → (h n s : ℚ) = (n : ℚ) + 3 - (s : ℚ) := by
    intro n s h2 h3
    have e : h n s + s = n + 3 := by
      rw [hN n s h2]
      omega
    have e' : ((h n s + s : ℕ) : ℚ) = ((n + 3 : ℕ) : ℚ) := by rw [e]
    push_cast at e'
    linarith
  have hq0 : ∀ n s : ℕ, s = 0 → 1 ≤ n → (h n s : ℚ) = (n : ℚ) - 1 := by
    intro n s hs hn
    have e : h n s + 1 = n := by
      rw [hh, if_pos hs]
      omega
    have e' : ((h n s + 1 : ℕ) : ℚ) = (n : ℚ) := by rw [e]
    push_cast at e'
    linarith
  have hq1 : ∀ n s : ℕ, s = 1 → (h n s : ℚ) = (n : ℚ) := by
    intro n s hs
    have e : h n s = n := by
      rw [hh, if_neg (show ¬ s = 0 by omega), if_pos hs]
    rw [e]
  have F0v : ∀ p : ℕ, ∑ x ∈ Finset.range (p + 2), (h (p + 1) (0 + x) : ℚ) =
      2 * (p : ℚ) + 1 + ((p : ℚ) * ((p : ℚ) + 2) - (p : ℚ) * ((p : ℚ) - 1) / 2) := by
    intro p
    have t : ∀ x ∈ Finset.range p, (h (p + 1) (0 + (x + 2)) : ℚ) =
        ((p : ℚ) + 2) + (-1) * (x : ℚ) + 0 * (x : ℚ) ^ 2 := by
      intro x hx
      have hx' := Finset.mem_range.mp hx
      rw [hq (p + 1) (0 + (x + 2)) (by omega) (by omega)]
      push_cast
      ring
    rw [peel2, hq0 (p + 1) (0 + 0) rfl (by omega), hq1 (p + 1) (0 + 1) rfl,
      Finset.sum_congr rfl t, quad]
    push_cast
    ring
  have F1v : ∀ p : ℕ, ∑ x ∈ Finset.range (p + 2), (h (p + 1) (1 + x) : ℚ) =
      (p : ℚ) + 1 + ((p : ℚ) + 2) + ((p : ℚ) * ((p : ℚ) + 1) - (p : ℚ) * ((p : ℚ) - 1) / 2) := by
    intro p
    have t : ∀ x ∈ Finset.range p, (h (p + 1) (1 + (x + 2)) : ℚ) =
        ((p : ℚ) + 1) + (-1) * (x : ℚ) + 0 * (x : ℚ) ^ 2 := by
      intro x hx
      have hx' := Finset.mem_range.mp hx
      rw [hq (p + 1) (1 + (x + 2)) (by omega) (by omega)]
      push_cast
      ring
    rw [peel2, hq1 (p + 1) (1 + 0) rfl, hq (p + 1) (1 + 1) (by omega) (by omega),
      Finset.sum_congr rfl t, quad]
    push_cast
    ring
  have F2v : ∀ p : ℕ, ∀ w ∈ Finset.range p,
      ∑ x ∈ Finset.range (p + 2), (h (p + 1) (w + 2 + x) : ℚ) =
        ((p : ℚ) + 2) * ((p : ℚ) + 3) / 2 + (-(2 * (p : ℚ) + 5) / 2) * (w : ℚ)
          + (1 / 2) * (w : ℚ) ^ 2 := by
    intro p w hw
    have hw' := Finset.mem_range.mp hw
    have t : ∀ x ∈ Finset.range (p + 2),
        (h (p + 1) (w + 2 + x) : ℚ) = ((p + 2 - w - x : ℕ) : ℚ) := by
      intro x _
      rw [hN (p + 1) (w + 2 + x) (by omega),
        show p + 1 + 3 - (w + 2 + x) = p + 2 - w - x by omega]
    rw [Finset.sum_congr rfl t, tri (p + 2 - w) (p + 2) (by omega),
      Nat.cast_sub (show w ≤ p + 2 by omega)]
    push_cast
    ring
  have hC : ∀ n : ℕ, 0 < n →
      (a n : ℚ) = (-36 + 47 * (n : ℚ) + 12 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) / 6 := by
    intro n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    rw [hAq (p + 1)]
    show ∑ w ∈ Finset.range (p + 2), ∑ x ∈ Finset.range (p + 2), (h (p + 1) (w + x) : ℚ) = _
    rw [peel2, F0v p, F1v p, Finset.sum_congr rfl (F2v p), quad]
    push_cast
    ring
  have a0 : (a 0 : ℚ) = 0 := by
    rw [hAq 0]
    simp [hh]
  have a1 : (a 1 : ℚ) = 4 := by
    rw [hC 1 (by omega)]
    norm_num
  have a2 : (a 2 : ℚ) = 19 := by
    rw [hC 2 (by omega)]
    norm_num
  have a3 : (a 3 : ℚ) = 40 := by
    rw [hC 3 (by omega)]
    norm_num
  have a4 : (a 4 : ℚ) = 68 := by
    rw [hC 4 (by omega)]
    norm_num
  refine ⟨?_, hC, ?_⟩
  · have key : PowerSeries.mk (fun n => (a n : ℚ))
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
        + PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4 =
        PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4
        + PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3
        - PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 12
        + PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 := by
      ext m
      simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
        PowerSeries.coeff_mk, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow]
      rcases Nat.lt_or_ge m 5 with hm | hm
      · interval_cases m
        · norm_num [a0]
        · norm_num [a0, a1]
        · norm_num [a0, a1, a2]
        · norm_num [a0, a1, a2, a3]
        · norm_num [a0, a1, a2, a3, a4]
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
        rw [if_pos (show 1 ≤ k + 5 by omega), if_pos (show 2 ≤ k + 5 by omega),
          if_pos (show 3 ≤ k + 5 by omega), if_pos (show 4 ≤ k + 5 by omega),
          if_neg (show ¬ (k + 5 = 1) by omega), if_neg (show ¬ (k + 5 = 2) by omega),
          if_neg (show ¬ (k + 5 = 3) by omega), if_neg (show ¬ (k + 5 = 4) by omega),
          show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
          show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
          hC (k + 5) (by omega), hC (k + 4) (by omega), hC (k + 3) (by omega),
          hC (k + 2) (by omega), hC (k + 1) (by omega)]
        push_cast
        ring
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 12] at key
    linear_combination key
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
      show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega]
    have e : ((a (k + 5) : ℤ) : ℚ) = ((4 * (a (k + 4) : ℤ) - 6 * (a (k + 3) : ℤ)
        + 4 * (a (k + 2) : ℤ) - (a (k + 1) : ℤ) : ℤ) : ℚ) := by
      push_cast
      rw [hC (k + 5) (by omega), hC (k + 4) (by omega), hC (k + 3) (by omega),
        hC (k + 2) (by omega), hC (k + 1) (by omega)]
      push_cast
      ring
    exact Int.cast_injective e
