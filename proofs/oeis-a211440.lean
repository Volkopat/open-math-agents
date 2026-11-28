import OMAStatements.S_oeis_a211440

-- Problem: A211440: Number of ordered triples (w,x,y) with all terms in {-n,...,0,...,n} and 2w+3x+3y=0.
-- Upstream: formal-conjectures statements/oeis-a211440.lean:0 (declaration OMA.S_oeis_a211440.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: 2w + 3x + 3y = 0 forces w = 3k and y = -2k - x, and then the x with -n <= x <= n and
-- -n <= -2k - x <= n form an interval of 2n + 1 - 2|k| integers. Summing over w = 3k in [-n, n]
-- (pairing w with -w) gives a(n) = (2n + 1)(2q + 1) - 2q(q + 1) with q = floor(n/3). The
-- recurrence follows from this closed form by cases on n mod 3, and the generating function by
-- comparing coefficients (the recurrence for m >= 7, the values a(0..6) below).

open OMA.S_oeis_a211440 in
theorem OMA.solution : type_of% @OMA.S_oeis_a211440.main := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℤ → ℤ, ∀ n w, c n w = if w % 3 = 0 then
      (if 0 ≤ w then 2 * (n : ℤ) + 1 - 2 * (w / 3) else 2 * (n : ℤ) + 1 + 2 * (w / 3)) else 0 :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ → ℤ, ∀ n i, g n i = if ((i : ℤ) + 1) % 3 = 0 then
      2 * (2 * (n : ℤ) + 1) - 4 * (((i : ℤ) + 1) / 3) else 0 := ⟨_, fun _ _ => rfl⟩
  have inner : ∀ (n : ℕ) (w x : ℤ), (∑ y ∈ Finset.Icc (-(n : ℤ)) n,
      (if 2 * w + 3 * x + 3 * y = 0 then 1 else 0 : ℕ)) =
      if w % 3 = 0 ∧ -(n : ℤ) ≤ -(2 * (w / 3)) - x ∧ -(2 * (w / 3)) - x ≤ n then 1 else 0 := by
    intro n w x
    by_cases h : w % 3 = 0 ∧ -(n : ℤ) ≤ -(2 * (w / 3)) - x ∧ -(2 * (w / 3)) - x ≤ n
    · rw [if_pos h, Finset.sum_eq_single (-(2 * (w / 3)) - x)]
      · rw [if_pos (show 2 * w + 3 * x + 3 * (-(2 * (w / 3)) - x) = 0 by omega)]
      · intro y _ hy
        rw [if_neg (show ¬ (2 * w + 3 * x + 3 * y = 0) by omega)]
      · intro hn
        exact (hn (Finset.mem_Icc.mpr ⟨h.2.1, h.2.2⟩)).elim
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro y hy
      rw [Finset.mem_Icc] at hy
      rw [if_neg (show ¬ (2 * w + 3 * x + 3 * y = 0) by omega)]
  have pairs : ∀ (n : ℕ) (w : ℤ), -(n : ℤ) ≤ w → w ≤ n →
      ((∑ x ∈ Finset.Icc (-(n : ℤ)) n, (if w % 3 = 0 ∧ -(n : ℤ) ≤ -(2 * (w / 3)) - x ∧
        -(2 * (w / 3)) - x ≤ n then 1 else 0 : ℕ) : ℕ) : ℤ) = c n w := by
    intro n w hw1 hw2
    by_cases h3 : w % 3 = 0
    · rw [← Finset.card_filter]
      by_cases hs : 0 ≤ w
      · have e : (Finset.Icc (-(n : ℤ)) n).filter (fun x => w % 3 = 0 ∧
            -(n : ℤ) ≤ -(2 * (w / 3)) - x ∧ -(2 * (w / 3)) - x ≤ n) =
            Finset.Icc (-(n : ℤ)) (n - 2 * (w / 3)) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · intro hx
            omega
          · intro hx
            omega
        rw [e, Int.card_Icc, Int.toNat_of_nonneg, hc, if_pos h3, if_pos hs]
        · ring
        · omega
      · have e : (Finset.Icc (-(n : ℤ)) n).filter (fun x => w % 3 = 0 ∧
            -(n : ℤ) ≤ -(2 * (w / 3)) - x ∧ -(2 * (w / 3)) - x ≤ n) =
            Finset.Icc (-(n : ℤ) - 2 * (w / 3)) n := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · intro hx
            omega
          · intro hx
            omega
        rw [e, Int.card_Icc, Int.toNat_of_nonneg, hc, if_pos h3, if_neg hs]
        · ring
        · omega
    · have hz : ∀ x ∈ Finset.Icc (-(n : ℤ)) n, (if w % 3 = 0 ∧ -(n : ℤ) ≤ -(2 * (w / 3)) - x ∧
          -(2 * (w / 3)) - x ≤ n then 1 else 0 : ℕ) = 0 := by
        intro x _
        exact if_neg (by omega)
      rw [Finset.sum_eq_zero hz, hc, if_neg h3, Nat.cast_zero]
  have perw : ∀ (n : ℕ) (w : ℤ), -(n : ℤ) ≤ w → w ≤ n →
      ((∑ x ∈ Finset.Icc (-(n : ℤ)) n, ∑ y ∈ Finset.Icc (-(n : ℤ)) n,
        (if 2 * w + 3 * x + 3 * y = 0 then 1 else 0 : ℕ) : ℕ) : ℤ) = c n w := by
    intro n w hw1 hw2
    rw [Finset.sum_congr rfl (fun x _ => inner n w x)]
    exact pairs n w hw1 hw2
  have hA : ∀ n : ℕ, (a n : ℤ) = ∑ w ∈ Finset.Icc (-(n : ℤ)) n, c n w := by
    intro n
    unfold a
    rw [Finset.card_filter, Finset.sum_product, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    rw [Finset.sum_product]
    exact perw n w (Finset.mem_Icc.mp hw).1 (Finset.mem_Icc.mp hw).2
  have ssum : ∀ (f : ℤ → ℤ) (n : ℕ), ∑ w ∈ Finset.Icc (-(n : ℤ)) n, f w =
      f 0 + ∑ i ∈ Finset.range n, (f ((i : ℤ) + 1) + f (-((i : ℤ) + 1))) := by
    intro f n
    induction n with
    | zero => simp
    | succ k ih =>
      have e : Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) =
          insert ((k : ℤ) + 1) (insert (-((k : ℤ) + 1)) (Finset.Icc (-(k : ℤ)) k)) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        push_cast
        constructor
        · intro hx
          omega
        · intro hx
          omega
      have h1 : -((k : ℤ) + 1) ∉ Finset.Icc (-(k : ℤ)) k := by
        rw [Finset.mem_Icc]
        omega
      have h2 : (k : ℤ) + 1 ∉ insert (-((k : ℤ) + 1)) (Finset.Icc (-(k : ℤ)) k) := by
        rw [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [e, Finset.sum_insert h2, Finset.sum_insert h1, ih, Finset.sum_range_succ]
      ring
  have c0 : ∀ n : ℕ, c n 0 = 2 * (n : ℤ) + 1 := by
    intro n
    rw [hc]
    norm_num
  have cpair : ∀ (n i : ℕ), c n ((i : ℤ) + 1) + c n (-((i : ℤ) + 1)) = g n i := by
    intro n i
    rw [hc, hc, hg]
    by_cases h : ((i : ℤ) + 1) % 3 = 0
    · have h' : (-((i : ℤ) + 1)) % 3 = 0 := by omega
      have hd : (-((i : ℤ) + 1)) / 3 = -(((i : ℤ) + 1) / 3) := by omega
      rw [if_pos h, if_pos h, if_pos h', if_pos (show (0 : ℤ) ≤ (i : ℤ) + 1 by omega),
        if_neg (show ¬ ((0 : ℤ) ≤ -((i : ℤ) + 1)) by omega), hd]
      ring
    · have h' : ¬ ((-((i : ℤ) + 1)) % 3 = 0) := by omega
      rw [if_neg h, if_neg h, if_neg h', add_zero]
  have rsum : ∀ n N : ℕ, ∑ i ∈ Finset.range N, g n i =
      2 * (2 * (n : ℤ) + 1) * ((N / 3 : ℕ) : ℤ) - 2 * ((N / 3 : ℕ) : ℤ) * (((N / 3 : ℕ) : ℤ) + 1) := by
    intro n N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, hg]
      by_cases h : ((N : ℤ) + 1) % 3 = 0
      · have e1 : (N + 1) / 3 = N / 3 + 1 := by omega
        have e2 : ((N : ℤ) + 1) / 3 = ((N / 3 : ℕ) : ℤ) + 1 := by omega
        rw [if_pos h, e1, e2]
        push_cast
        ring
      · have e1 : (N + 1) / 3 = N / 3 := by omega
        rw [if_neg h, e1, add_zero]
  have hB : ∀ n : ℕ, (a n : ℤ) = (2 * (n : ℤ) + 1) * (2 * ((n / 3 : ℕ) : ℤ) + 1)
      - 2 * ((n / 3 : ℕ) : ℤ) * (((n / 3 : ℕ) : ℤ) + 1) := by
    intro n
    rw [hA n, ssum (c n) n, Finset.sum_congr rfl (fun i _ => cpair n i), rsum n n, c0 n]
    ring
  have hrc : ∀ n : ℕ, 6 < n →
      (a n : ℤ) = (a (n - 1) : ℤ) + 2 * (a (n - 3) : ℤ) - 2 * (a (n - 4) : ℤ)
        - (a (n - 6) : ℤ) + (a (n - 7) : ℤ) := by
    intro n hn
    obtain ⟨j, hj | hj | hj⟩ : ∃ j, n = 3 * j + 7 ∨ n = 3 * j + 8 ∨ n = 3 * j + 9 :=
      ⟨(n - 7) / 3, by omega⟩
    · subst hj
      rw [show 3 * j + 7 - 1 = 3 * j + 6 by omega, show 3 * j + 7 - 3 = 3 * j + 4 by omega,
        show 3 * j + 7 - 4 = 3 * j + 3 by omega, show 3 * j + 7 - 6 = 3 * j + 1 by omega,
        show 3 * j + 7 - 7 = 3 * j by omega, hB, hB, hB, hB, hB, hB,
        show (3 * j + 7) / 3 = j + 2 by omega, show (3 * j + 6) / 3 = j + 2 by omega,
        show (3 * j + 4) / 3 = j + 1 by omega, show (3 * j + 3) / 3 = j + 1 by omega,
        show (3 * j + 1) / 3 = j by omega, show 3 * j / 3 = j by omega]
      push_cast
      ring
    · subst hj
      rw [show 3 * j + 8 - 1 = 3 * j + 7 by omega, show 3 * j + 8 - 3 = 3 * j + 5 by omega,
        show 3 * j + 8 - 4 = 3 * j + 4 by omega, show 3 * j + 8 - 6 = 3 * j + 2 by omega,
        show 3 * j + 8 - 7 = 3 * j + 1 by omega, hB, hB, hB, hB, hB, hB,
        show (3 * j + 8) / 3 = j + 2 by omega, show (3 * j + 7) / 3 = j + 2 by omega,
        show (3 * j + 5) / 3 = j + 1 by omega, show (3 * j + 4) / 3 = j + 1 by omega,
        show (3 * j + 2) / 3 = j by omega, show (3 * j + 1) / 3 = j by omega]
      push_cast
      ring
    · subst hj
      rw [show 3 * j + 9 - 1 = 3 * j + 8 by omega, show 3 * j + 9 - 3 = 3 * j + 6 by omega,
        show 3 * j + 9 - 4 = 3 * j + 5 by omega, show 3 * j + 9 - 6 = 3 * j + 3 by omega,
        show 3 * j + 9 - 7 = 3 * j + 2 by omega, hB, hB, hB, hB, hB, hB,
        show (3 * j + 9) / 3 = j + 3 by omega, show (3 * j + 8) / 3 = j + 2 by omega,
        show (3 * j + 6) / 3 = j + 2 by omega, show (3 * j + 5) / 3 = j + 1 by omega,
        show (3 * j + 3) / 3 = j + 1 by omega, show (3 * j + 2) / 3 = j by omega]
      push_cast
      ring
  refine ⟨hrc, ?_⟩
  have a0 : (a 0 : ℚ) = 1 := by
    have h := hB 0
    norm_num at h
    exact_mod_cast h
  have a1 : (a 1 : ℚ) = 3 := by
    have h := hB 1
    norm_num at h
    exact_mod_cast h
  have a2 : (a 2 : ℚ) = 5 := by
    have h := hB 2
    norm_num at h
    exact_mod_cast h
  have a3 : (a 3 : ℚ) = 17 := by
    have h := hB 3
    norm_num at h
    exact_mod_cast h
  have a4 : (a 4 : ℚ) = 23 := by
    have h := hB 4
    norm_num at h
    exact_mod_cast h
  have a5 : (a 5 : ℚ) = 29 := by
    have h := hB 5
    norm_num at h
    exact_mod_cast h
  have a6 : (a 6 : ℚ) = 53 := by
    have h := hB 6
    norm_num at h
    exact_mod_cast h
  have hrecQ : ∀ k : ℕ, (a (k + 7) : ℚ) = (a (k + 6) : ℚ) + 2 * (a (k + 4) : ℚ)
      - 2 * (a (k + 3) : ℚ) - (a (k + 1) : ℚ) + (a k : ℚ) := by
    intro k
    have h := hrc (k + 7) (by omega)
    rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 3 = k + 4 by omega,
      show k + 7 - 4 = k + 3 by omega, show k + 7 - 6 = k + 1 by omega,
      show k + 7 - 7 = k by omega] at h
    have h2 := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at h2
    linarith
  have key : PowerSeries.mk (fun n => (a n : ℚ))
      - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1
      - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
        (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
      + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
        (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4)
      + PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 6
      - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 7 =
      PowerSeries.X ^ 0 + PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
      + PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
      + PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10
      + PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
      + PowerSeries.X ^ 5 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
      + PowerSeries.X ^ 6 := by
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 7 with hm | hm
    · interval_cases m
      · norm_num [a0]
      · norm_num [a0, a1]
      · norm_num [a1, a2]
      · norm_num [a0, a2, a3]
      · norm_num [a0, a1, a3, a4]
      · norm_num [a1, a2, a4, a5]
      · norm_num [a0, a2, a3, a5, a6]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 7 := ⟨m - 7, by omega⟩
      rw [if_pos (show 1 ≤ k + 7 by omega), if_pos (show 3 ≤ k + 7 by omega),
        if_pos (show 4 ≤ k + 7 by omega), if_pos (show 6 ≤ k + 7 by omega),
        if_pos (show 7 ≤ k + 7 by omega),
        if_neg (show ¬ (k + 7 = 0) by omega), if_neg (show ¬ (k + 7 = 1) by omega),
        if_neg (show ¬ (k + 7 = 2) by omega), if_neg (show ¬ (k + 7 = 3) by omega),
        if_neg (show ¬ (k + 7 = 4) by omega), if_neg (show ¬ (k + 7 = 5) by omega),
        if_neg (show ¬ (k + 7 = 6) by omega),
        show k + 7 - 1 = k + 6 by omega, show k + 7 - 3 = k + 4 by omega,
        show k + 7 - 4 = k + 3 by omega, show k + 7 - 6 = k + 1 by omega,
        show k + 7 - 7 = k by omega, hrecQ k]
      ring
  rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2,
    map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10] at key
  linear_combination key
