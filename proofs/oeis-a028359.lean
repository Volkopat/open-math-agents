import OMAStatements.S_oeis_a028359

-- Problem: A028359: Two-bell analog of A028355.
-- Upstream: formal-conjectures statements/oeis-a028359.lean:0 (declaration OMA.S_oeis_a028359.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: S(j) = j + floor(j/2), so c(n) = floor((n(n+1)+1)/3) (n(n+1) is even and not
-- 1 mod 3), hence c(n+3) = c(n) + 2n + 4. So group n+3 has two digits more than group n and
-- starts at a position of the same parity: since the digits have period 2, it is group n
-- followed by two digits t(n) = 10 d(c(n+3)-2) + d(c(n+3)-1), i.e. a(n+3) = 100 a(n) + t(n),
-- and t(n+3) = t(n). This gives a(n+6) = 101 a(n+3) - 100 a(n); the g.f. follows by
-- comparing coefficients (the first seven by evaluation).

open OMA.S_oeis_a028359 in
theorem OMA.solution : type_of% @OMA.S_oeis_a028359.main := by
  have hS : ∀ j, S j = j + j / 2 := by
    intro j
    induction j with
    | zero => simp [S]
    | succ k ih =>
      have h : S (k + 1) = S k + d k := Finset.sum_range_succ d k
      rw [h, ih]
      unfold d
      split_ifs with hk
      · omega
      · omega
  have key : ∀ N j : ℕ, N % 2 = 0 → N % 3 ≠ 1 → (j + j / 2 = N / 2 ↔ j = (N + 1) / 3) := by
    intro N j h2 h3
    constructor
    · intro h
      omega
    · intro h
      omega
  have hc : ∀ n, c n = (n * (n + 1) + 1) / 3 := by
    intro n
    have h2 : n * (n + 1) % 2 = 0 := Nat.even_iff.mp (Nat.even_mul_succ_self n)
    have h3 : n * (n + 1) % 3 ≠ 1 := by
      rw [Nat.mul_mod, Nat.add_mod]
      have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h with h | h | h
      · rw [h]
        decide
      · rw [h]
        decide
      · rw [h]
        decide
    have hset : {j : ℕ | S j = n * (n + 1) / 2} = {(n * (n + 1) + 1) / 3} := by
      ext j
      show S j = n * (n + 1) / 2 ↔ j = (n * (n + 1) + 1) / 3
      rw [hS j]
      exact key (n * (n + 1)) j h2 h3
    rw [c, hset, csInf_singleton]
  have hc3 : ∀ n, c (n + 3) = c n + 2 * n + 4 := by
    intro n
    rw [hc (n + 3), hc n, show (n + 3) * (n + 3 + 1) = n * (n + 1) + 6 * n + 12 by ring]
    omega
  have hmono : ∀ q, c q ≤ c (q + 1) := by
    intro q
    rw [hc q, hc (q + 1), show (q + 1) * (q + 1 + 1) = q * (q + 1) + 2 * q + 2 by ring]
    omega
  have hd : ∀ x t, d (x + 2 * t) = d x := by
    intro x t
    unfold d
    rw [show (x + 2 * t) % 2 = x % 2 by omega]
  have hT : ∀ n, 1 ≤ n → a (n + 3) = 100 * a n + (10 * d (c (n + 3) - 2) + d (c (n + 3) - 1)) := by
    intro n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    have h1 : c (p + 1 + 3) = c (p + 1) + 2 * (p + 1) + 4 := hc3 (p + 1)
    have hlen : c (p + 1 + 3) - c (p + 1 + 3 - 1) = c (p + 1) - c (p + 1 - 1) + 1 + 1 := by
      rw [show p + 1 + 3 - 1 = p + 3 by omega, show p + 1 - 1 = p by omega, hc3 (p + 1), hc3 p]
      have := hmono p
      omega
    have hsum : ∑ i ∈ Finset.range (c (p + 1) - c (p + 1 - 1)),
          d (c (p + 1 + 3) - 1 - (i + 1 + 1)) * 10 ^ (i + 1 + 1) =
        100 * ∑ i ∈ Finset.range (c (p + 1) - c (p + 1 - 1)), d (c (p + 1) - 1 - i) * 10 ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [show c (p + 1 + 3) - 1 - (i + 1 + 1) = c (p + 1) - 1 - i + 2 * (p + 2) by omega, hd]
      ring
    unfold a
    rw [hlen, Finset.sum_range_succ', Finset.sum_range_succ', hsum,
      show c (p + 1 + 3) - 1 - (0 + 1) = c (p + 1 + 3) - 2 by omega, Nat.sub_zero]
    ring
  have hrecN : ∀ m, 1 ≤ m → a (m + 6) + 100 * a m = 101 * a (m + 3) := by
    intro m hm
    have e1 := hT (m + 3) (by omega)
    have e2 := hT m hm
    have hcc : c (m + 3 + 3) = c (m + 3) + 2 * (m + 3) + 4 := hc3 (m + 3)
    have hge : 2 ≤ c (m + 3) := by
      rw [hc3 m]
      omega
    have t1 : d (c (m + 3 + 3) - 2) = d (c (m + 3) - 2) := by
      rw [show c (m + 3 + 3) - 2 = c (m + 3) - 2 + 2 * (m + 5) by omega, hd]
    have t2 : d (c (m + 3 + 3) - 1) = d (c (m + 3) - 1) := by
      rw [show c (m + 3 + 3) - 1 = c (m + 3) - 1 + 2 * (m + 5) by omega, hd]
    rw [t1, t2] at e1
    rw [show m + 6 = m + 3 + 3 by omega, e1, e2]
    ring
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 3 = m + 3 by omega, show m + 6 - 6 = m by omega]
    have h := congrArg (fun x : ℕ => (x : ℤ)) (hrecN m (by omega))
    push_cast at h
    linarith
  · have a0 : a 0 = 0 := by norm_num [a, hc]
    have a1 : a 1 = 1 := by norm_num [a, hc, Finset.sum_range_succ, d]
    have a2 : a 2 = 2 := by norm_num [a, hc, Finset.sum_range_succ, d]
    have a3 : a 3 = 12 := by norm_num [a, hc, Finset.sum_range_succ, d]
    have a4 : a 4 = 121 := by norm_num [a, hc, Finset.sum_range_succ, d]
    have a5 : a 5 = 212 := by norm_num [a, hc, Finset.sum_range_succ, d]
    have a6 : a 6 = 1212 := by norm_num [a, hc, Finset.sum_range_succ, d]
    have hq : ∀ k : ℕ, (a (k + 7) : ℚ) = 101 * (a (k + 4) : ℚ) - 100 * (a (k + 1) : ℚ) := by
      intro k
      have h := congrArg (fun x : ℕ => (x : ℚ)) (hrecN (k + 1) (by omega))
      rw [show k + 1 + 6 = k + 7 by omega, show k + 1 + 3 = k + 4 by omega] at h
      push_cast at h
      linarith
    have e : PowerSeries.mk (fun n => (a n : ℚ)) *
        (100 * PowerSeries.X ^ 6 - 101 * PowerSeries.X ^ 3 + 1) =
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 100 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 6)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 101 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
          + PowerSeries.mk (fun n => (a n : ℚ)) := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 100,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 101]
      ring
    have e2 : (PowerSeries.X * (10 * PowerSeries.X ^ 4 + 20 * PowerSeries.X ^ 3 +
        12 * PowerSeries.X ^ 2 + 2 * PowerSeries.X + 1) : PowerSeries ℚ) =
        PowerSeries.X ^ 5 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10
          + PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 20
          + PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 12
          + PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
          + PowerSeries.X ^ 1 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 20,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 12,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
      ring
    rw [e, e2]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge n 7 with hn | hn
    · interval_cases n
      · norm_num [a0]
      · norm_num [a1]
      · norm_num [a2]
      · norm_num [a3, a0]
      · norm_num [a4, a1]
      · norm_num [a5, a2]
      · norm_num [a6, a3, a0]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
      rw [if_pos (show 6 ≤ k + 7 by omega), if_pos (show 3 ≤ k + 7 by omega),
        if_neg (show ¬ (k + 7 = 5) by omega), if_neg (show ¬ (k + 7 = 4) by omega),
        if_neg (show ¬ (k + 7 = 3) by omega), if_neg (show ¬ (k + 7 = 2) by omega),
        if_neg (show ¬ (k + 7 = 1) by omega),
        show k + 7 - 6 = k + 1 by omega, show k + 7 - 3 = k + 4 by omega, hq k]
      ring
