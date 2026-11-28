import OMAStatements.S_oeis_a068962

-- Problem: A068962: Number of successive terms of A028356 that add to n; or length of n-th term of A028355.
-- Upstream: formal-conjectures statements/oeis-a068962.lean:0 (declaration OMA.S_oeis_a068962.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: S is strictly increasing with S(m+6) = S(m) + 15. Every triangular number
-- T(n) = n(n+1)/2 is a value S(p(n)) (checked for n < 15, and T(n+15) = T(n) + 15(n+8) gives
-- S(p(n) + 6(n+8)) = T(n+15)), so p(n+15) = p(n) + 6(n+8) by injectivity. The set counted by
-- a(n) is the interval (p(n-1), p(n)], so a(n) = p(n) - p(n-1) and a(n+15) = a(n) + 6 for
-- n >= 1. The recurrence follows, and the g.f. by comparing coefficients with a(0..16).

open OMA.S_oeis_a068962 in
theorem OMA.solution : type_of% @OMA.S_oeis_a068962.main := by
  have hS1 : ∀ m, S (m + 1) = S m + c m := by
    intro m
    unfold S
    exact Finset.sum_range_succ c m
  have hc6 : ∀ i, c (i + 6) = c i := by
    intro i
    unfold c
    rw [Nat.add_mod_right]
  have hcmod : ∀ i, c i = c (i % 6) := by
    intro i
    unfold c
    rw [Nat.mod_mod]
  have hcpos : ∀ i, 1 ≤ c i := by
    intro i
    rw [hcmod i]
    obtain ⟨r, hr, hri⟩ : ∃ r, r < 6 ∧ i % 6 = r := ⟨i % 6, Nat.mod_lt i (by norm_num), rfl⟩
    rw [hri]
    interval_cases r <;> decide
  have hblock : ∀ m, c m + c (m + 1) + c (m + 2) + c (m + 3) + c (m + 4) + c (m + 5) = 15 := by
    intro m
    induction m with
    | zero => decide
    | succ k ih =>
      rw [show k + 1 + 1 = k + 2 by omega, show k + 1 + 2 = k + 3 by omega,
        show k + 1 + 3 = k + 4 by omega, show k + 1 + 4 = k + 5 by omega,
        show k + 1 + 5 = k + 6 by omega, hc6 k]
      omega
  have hS6 : ∀ m, S (m + 6) = S m + 15 := by
    intro m
    have e1 : S (m + 1) = S m + c m := hS1 m
    have e2 : S (m + 2) = S (m + 1) + c (m + 1) := by
      rw [show m + 2 = m + 1 + 1 by omega]
      exact hS1 (m + 1)
    have e3 : S (m + 3) = S (m + 2) + c (m + 2) := by
      rw [show m + 3 = m + 2 + 1 by omega]
      exact hS1 (m + 2)
    have e4 : S (m + 4) = S (m + 3) + c (m + 3) := by
      rw [show m + 4 = m + 3 + 1 by omega]
      exact hS1 (m + 3)
    have e5 : S (m + 5) = S (m + 4) + c (m + 4) := by
      rw [show m + 5 = m + 4 + 1 by omega]
      exact hS1 (m + 4)
    have e6 : S (m + 6) = S (m + 5) + c (m + 5) := by
      rw [show m + 6 = m + 5 + 1 by omega]
      exact hS1 (m + 5)
    have hb := hblock m
    omega
  have hS6j : ∀ j m, S (m + 6 * j) = S m + 15 * j := by
    intro j
    induction j with
    | zero =>
      intro m
      simp
    | succ k ih =>
      intro m
      rw [show m + 6 * (k + 1) = m + 6 * k + 6 by ring, hS6, ih]
      omega
  have hSmono : StrictMono S := by
    apply strictMono_nat_of_lt_succ
    intro m
    rw [hS1]
    have := hcpos m
    omega
  have hSge : ∀ m, m ≤ S m := by
    intro m
    induction m with
    | zero => omega
    | succ k ih =>
      rw [hS1]
      have := hcpos k
      omega
  have hT : ∀ n, (n + 15) * (n + 15 + 1) / 2 = n * (n + 1) / 2 + 15 * (n + 8) := by
    intro n
    have h : (n + 15) * (n + 15 + 1) = n * (n + 1) + 2 * (15 * (n + 8)) := by ring
    rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
  have hpos : ∀ n, ∃ m, S m = n * (n + 1) / 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.lt_or_ge n 15 with hn | hn
      · interval_cases n
        · exact ⟨0, by decide⟩
        · exact ⟨1, by decide⟩
        · exact ⟨2, by decide⟩
        · exact ⟨3, by decide⟩
        · exact ⟨4, by decide⟩
        · exact ⟨6, by decide⟩
        · exact ⟨9, by decide⟩
        · exact ⟨11, by decide⟩
        · exact ⟨15, by decide⟩
        · exact ⟨18, by decide⟩
        · exact ⟨22, by decide⟩
        · exact ⟨27, by decide⟩
        · exact ⟨32, by decide⟩
        · exact ⟨37, by decide⟩
        · exact ⟨42, by decide⟩
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 15 := ⟨n - 15, by omega⟩
        obtain ⟨m, hm⟩ := ih k (by omega)
        exact ⟨m + 6 * (k + 8), by rw [hS6j, hm, hT]⟩
  choose p hp using hpos
  have hpv : ∀ n w, S w = n * (n + 1) / 2 → p n = w :=
    fun n w h => hSmono.injective ((hp n).trans h.symm)
  have hpstep : ∀ n, p (n + 15) = p n + 6 * (n + 8) := by
    intro n
    apply hSmono.injective
    rw [hp, hS6j, hp, hT]
  have hpmono : ∀ n, p n ≤ p (n + 1) := by
    intro n
    rw [← hSmono.le_iff_le, hp, hp]
    have h : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
    omega
  have ha : ∀ n, 1 ≤ n → a n = p n - p (n - 1) := by
    intro n hn
    have e1 : (n - 1) * n / 2 = S (p (n - 1)) := by
      rw [hp (n - 1), show n - 1 + 1 = n by omega]
    have e2 : n * (n + 1) / 2 = S (p n) := (hp n).symm
    have h1 : p n ≤ S (p n) := hSge (p n)
    rw [← Nat.card_Ioc (p (n - 1)) (p n)]
    unfold a
    congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    rw [e1, e2, hSmono.lt_iff_lt, hSmono.le_iff_le]
    constructor
    · intro h
      exact h.2
    · intro h
      refine ⟨?_, h⟩
      have := h.2
      omega
  have hshift : ∀ n, 1 ≤ n → a (n + 15) = a n + 6 := by
    intro n hn
    have hm : p (n - 1) ≤ p n := by
      have h := hpmono (n - 1)
      rwa [show n - 1 + 1 = n by omega] at h
    rw [ha (n + 15) (by omega), ha n hn, show n + 15 - 1 = n - 1 + 15 by omega, hpstep, hpstep]
    omega
  have p0 : p 0 = 0 := hpv 0 0 (by decide)
  have p1 : p 1 = 1 := hpv 1 1 (by decide)
  have p2 : p 2 = 2 := hpv 2 2 (by decide)
  have p3 : p 3 = 3 := hpv 3 3 (by decide)
  have p4 : p 4 = 4 := hpv 4 4 (by decide)
  have p5 : p 5 = 6 := hpv 5 6 (by decide)
  have p6 : p 6 = 9 := hpv 6 9 (by decide)
  have p7 : p 7 = 11 := hpv 7 11 (by decide)
  have p8 : p 8 = 15 := hpv 8 15 (by decide)
  have p9 : p 9 = 18 := hpv 9 18 (by decide)
  have p10 : p 10 = 22 := hpv 10 22 (by decide)
  have p11 : p 11 = 27 := hpv 11 27 (by decide)
  have p12 : p 12 = 32 := hpv 12 32 (by decide)
  have p13 : p 13 = 37 := hpv 13 37 (by decide)
  have p14 : p 14 = 42 := hpv 14 42 (by decide)
  have p15 : p 15 = 48 := hpv 15 48 (by decide)
  have p16 : p 16 = 55 := hpv 16 55 (by decide)
  have a0 : a 0 = 0 := by decide
  have a1 : a 1 = 1 := by
    have h : a 1 = p 1 - p 0 := ha 1 (by norm_num)
    omega
  have a2 : a 2 = 1 := by
    have h : a 2 = p 2 - p 1 := ha 2 (by norm_num)
    omega
  have a3 : a 3 = 1 := by
    have h : a 3 = p 3 - p 2 := ha 3 (by norm_num)
    omega
  have a4 : a 4 = 1 := by
    have h : a 4 = p 4 - p 3 := ha 4 (by norm_num)
    omega
  have a5 : a 5 = 2 := by
    have h : a 5 = p 5 - p 4 := ha 5 (by norm_num)
    omega
  have a6 : a 6 = 3 := by
    have h : a 6 = p 6 - p 5 := ha 6 (by norm_num)
    omega
  have a7 : a 7 = 2 := by
    have h : a 7 = p 7 - p 6 := ha 7 (by norm_num)
    omega
  have a8 : a 8 = 4 := by
    have h : a 8 = p 8 - p 7 := ha 8 (by norm_num)
    omega
  have a9 : a 9 = 3 := by
    have h : a 9 = p 9 - p 8 := ha 9 (by norm_num)
    omega
  have a10 : a 10 = 4 := by
    have h : a 10 = p 10 - p 9 := ha 10 (by norm_num)
    omega
  have a11 : a 11 = 5 := by
    have h : a 11 = p 11 - p 10 := ha 11 (by norm_num)
    omega
  have a12 : a 12 = 5 := by
    have h : a 12 = p 12 - p 11 := ha 12 (by norm_num)
    omega
  have a13 : a 13 = 5 := by
    have h : a 13 = p 13 - p 12 := ha 13 (by norm_num)
    omega
  have a14 : a 14 = 5 := by
    have h : a 14 = p 14 - p 13 := ha 14 (by norm_num)
    omega
  have a15 : a 15 = 6 := by
    have h : a 15 = p 15 - p 14 := ha 15 (by norm_num)
    omega
  have a16 : a 16 = 7 := by
    have h : a 16 = p 16 - p 15 := ha 16 (by norm_num)
    omega
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 17 := ⟨n - 17, by omega⟩
    rw [show k + 17 - 1 = k + 1 + 15 by omega, show k + 17 - 15 = k + 2 by omega,
      show k + 17 - 16 = k + 1 by omega, show k + 17 = k + 2 + 15 by omega]
    have h1 := hshift (k + 1) (by omega)
    have h2 := hshift (k + 2) (by omega)
    omega
  · have e : PowerSeries.mk (fun n => (a n : ℚ)) *
        (PowerSeries.X ^ 16 - PowerSeries.X ^ 15 - PowerSeries.X + 1) =
        PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 16
          - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 15
          - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1
          + PowerSeries.mk (fun n => (a n : ℚ)) := by
      ring
    have e2 : (PowerSeries.X * (PowerSeries.X ^ 14 + PowerSeries.X ^ 10 + PowerSeries.X ^ 9 -
        PowerSeries.X ^ 8 + 2 * PowerSeries.X ^ 7 - PowerSeries.X ^ 6 + PowerSeries.X ^ 5 +
        PowerSeries.X ^ 4 + 1) : PowerSeries ℚ) =
        PowerSeries.X ^ 15 + PowerSeries.X ^ 11 + PowerSeries.X ^ 10 - PowerSeries.X ^ 9 +
          PowerSeries.X ^ 8 + PowerSeries.X ^ 8 - PowerSeries.X ^ 7 +
          PowerSeries.X ^ 6 + PowerSeries.X ^ 5 + PowerSeries.X ^ 1 := by
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 17 with hm | hm
    · interval_cases m <;>
        norm_num [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 17 := ⟨m - 17, by omega⟩
      rw [if_pos (show 16 ≤ k + 17 by omega), if_pos (show 15 ≤ k + 17 by omega),
        if_pos (show 1 ≤ k + 17 by omega),
        if_neg (show ¬ (k + 17 = 15) by omega), if_neg (show ¬ (k + 17 = 11) by omega),
        if_neg (show ¬ (k + 17 = 10) by omega), if_neg (show ¬ (k + 17 = 9) by omega),
        if_neg (show ¬ (k + 17 = 8) by omega), if_neg (show ¬ (k + 17 = 7) by omega),
        if_neg (show ¬ (k + 17 = 6) by omega), if_neg (show ¬ (k + 17 = 5) by omega),
        if_neg (show ¬ (k + 17 = 1) by omega),
        show k + 17 - 16 = k + 1 by omega, show k + 17 - 15 = k + 2 by omega,
        show k + 17 - 1 = k + 1 + 15 by omega, show k + 17 = k + 2 + 15 by omega,
        hshift (k + 1) (by omega), hshift (k + 2) (by omega)]
      push_cast
      ring
