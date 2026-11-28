import OMAStatements.S_oeis_a126397

-- Problem: A126397: Number of base 10 n-digit numbers with adjacent digits differing by two or less.
-- Upstream: formal-conjectures statements/oeis-a126397.lean:0 (declaration OMA.S_oeis_a126397.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: n3W D n k is the set of digit strings s(0..n) with s(n) = k and adjacent digits
-- differing by at most D. Removing the last digit (Fin.init, inverse Fin.snoc) gives the
-- transfer-matrix recursion |n3W D (n+1) k| = sum of |n3W D n j| over the digits j with
-- |j - k| <= D (n3card), |n3W D 0 k| = 1 (n3base), and sorting the strings of length n+1 by their
-- last digit gives a(n+1) = sum over k of |n3W 2 n k| (n3A_succ). For D = 2 each of the ten counts
-- c(m, k) satisfies c(m+4) + 11 c(m+2) = 7 c(m+3) + c(m): true for m = 0 by computation, and the
-- left side minus the right side at m+1 is the sum of the same differences at m over the
-- neighbours j of k. Summing over k gives the recurrence; the g.f. follows by comparing
-- coefficients, with a(0..4) = 1, 10, 44, 200, 918.

/-- Digit strings s(0..n) with values in 0..9, last digit k, adjacent digits differing by at most
D. -/
def n3W (D n k : ℕ) : Finset (Fin (n + 1) → ℕ) :=
  (Fintype.piFinset fun _ : Fin (n + 1) => Finset.range 10).filter
    (fun s => s (Fin.last n) = k ∧
      ∀ i : Fin n, s i.succ ≤ s i.castSucc + D ∧ s i.castSucc ≤ s i.succ + D)

/-- All digit strings of length n with adjacent digits differing by at most D. -/
def n3A (D n : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range 10).filter
    (fun s => ∀ i j : Fin n, j.val = i.val + 1 → s j ≤ s i + D ∧ s i ≤ s j + D)

theorem n3mem (D n k : ℕ) (s : Fin (n + 1) → ℕ) :
    s ∈ n3W D n k ↔ (∀ i, s i < 10) ∧ s (Fin.last n) = k ∧
      ∀ i : Fin n, s i.succ ≤ s i.castSucc + D ∧ s i.castSucc ≤ s i.succ + D := by
  unfold n3W
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  simp only [Finset.mem_range]

theorem n3Amem (D n : ℕ) (s : Fin n → ℕ) :
    s ∈ n3A D n ↔ (∀ i, s i < 10) ∧
      ∀ i j : Fin n, j.val = i.val + 1 → s j ≤ s i + D ∧ s i ≤ s j + D := by
  unfold n3A
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  simp only [Finset.mem_range]

theorem n3step (D n k : ℕ) (hk : k < 10) :
    n3W D (n + 1) k = ((Finset.range 10).filter (fun j => k ≤ j + D ∧ j ≤ k + D)).biUnion
      (fun j => (n3W D n j).image (fun t => (Fin.snoc t k : Fin (n + 1 + 1) → ℕ))) := by
  ext s
  rw [Finset.mem_biUnion]
  constructor
  · intro hs
    obtain ⟨hr, hl, hst⟩ := (n3mem D (n + 1) k s).1 hs
    have e1 : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
    have hlast := hst (Fin.last n)
    rw [e1, hl] at hlast
    refine ⟨s (Fin.last n).castSucc, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hr _, hlast⟩
    · rw [Finset.mem_image]
      refine ⟨Fin.init s, ?_, ?_⟩
      · rw [n3mem]
        refine ⟨fun i => hr i.castSucc, rfl, fun i => ?_⟩
        show s i.succ.castSucc ≤ s i.castSucc.castSucc + D ∧
          s i.castSucc.castSucc ≤ s i.succ.castSucc + D
        have h := hst i.castSucc
        rw [Fin.succ_castSucc] at h
        exact h
      · show (Fin.snoc (Fin.init s) k : Fin (n + 1 + 1) → ℕ) = s
        rw [← hl]
        exact Fin.snoc_init_self s
  · rintro ⟨j, hj, hs⟩
    rw [Finset.mem_filter, Finset.mem_range] at hj
    rw [Finset.mem_image] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨hr, hl, hst⟩ := (n3mem D n j t).1 ht
    rw [n3mem]
    refine ⟨fun i => ?_, ?_, fun i => ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        exact hr i'
      · rw [Fin.snoc_last]
        exact hk
    · rw [Fin.snoc_last]
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hst i'
      · have e1 : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
        rw [e1, Fin.snoc_last, Fin.snoc_castSucc, hl]
        exact hj.2

/-- The transfer-matrix recursion. -/
theorem n3card (D n k : ℕ) (hk : k < 10) :
    (n3W D (n + 1) k).card =
      ∑ j ∈ (Finset.range 10).filter (fun j => k ≤ j + D ∧ j ≤ k + D), (n3W D n j).card := by
  rw [n3step D n k hk, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.card_image_of_injective
    intro t t' h
    have h' : Fin.init (Fin.snoc t k : Fin (n + 1 + 1) → ℕ) =
        Fin.init (Fin.snoc t' k : Fin (n + 1 + 1) → ℕ) := congrArg Fin.init h
    rw [Fin.init_snoc, Fin.init_snoc] at h'
    exact h'
  · intro j _ j' _ hjj'
    exact Finset.disjoint_left.2 (fun s hs hs' => by
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨t', ht', e⟩ := Finset.mem_image.1 hs'
      have h1 := ((n3mem D n j t).1 ht).2.1
      have h2 := ((n3mem D n j' t').1 ht').2.1
      have h3 := congrFun e (Fin.last n).castSucc
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at h3
      omega)

/-- Strings of length one. -/
theorem n3base (D k : ℕ) (hk : k < 10) : (n3W D 0 k).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨fun _ => k, ?_⟩
  ext s
  rw [n3mem, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h0, -⟩
    funext i
    have hi0 : i = Fin.last 0 := (Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero _).symm
    rw [hi0]
    exact h0
  · rintro rfl
    exact ⟨fun _ => hk, rfl, fun i => i.elim0⟩

/-- The empty string. -/
theorem n3A0 (D : ℕ) : (n3A D 0).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨fun i => i.elim0, ?_⟩
  ext s
  rw [n3Amem, Finset.mem_singleton]
  constructor
  · intro _
    funext i
    exact i.elim0
  · intro _
    exact ⟨fun i => i.elim0, fun i => i.elim0⟩

/-- Sorting the strings of length m+1 by their last digit. -/
theorem n3A_succ (D m : ℕ) :
    (n3A D (m + 1)).card = ∑ k ∈ Finset.range 10, (n3W D m k).card := by
  have H : Set.MapsTo (fun s : Fin (m + 1) → ℕ => s (Fin.last m))
      (n3A D (m + 1) : Set (Fin (m + 1) → ℕ)) (Finset.range 10 : Set ℕ) := by
    intro s hs
    rw [Finset.mem_coe, n3Amem] at hs
    rw [Finset.mem_coe, Finset.mem_range]
    exact hs.1 (Fin.last m)
  rw [Finset.card_eq_sum_card_fiberwise H]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  ext s
  rw [Finset.mem_filter, n3mem, n3Amem]
  constructor
  · rintro ⟨⟨hr, hadj⟩, hl⟩
    exact ⟨hr, hl, fun i => hadj i.castSucc i.succ (by simp)⟩
  · rintro ⟨hr, hl, hadj⟩
    refine ⟨⟨hr, fun i j hij => ?_⟩, hl⟩
    have hj := j.isLt
    have hi : i.val < m := by omega
    have e1 : (⟨i.val, hi⟩ : Fin m).castSucc = i := Fin.ext rfl
    have e2 : (⟨i.val, hi⟩ : Fin m).succ = j := Fin.ext (show i.val + 1 = j.val by omega)
    have h := hadj ⟨i.val, hi⟩
    rw [e1, e2] at h
    exact h

/-- The g.f. from the initial values and the recurrence (coefficient comparison). -/
theorem n3gf2 (f : ℕ → ℚ) (h0 : f 0 = 1) (h1 : f 1 = 10) (h2 : f 2 = 44) (h3 : f 3 = 200)
    (h4 : f 4 = 918) (hq : ∀ m, 5 ≤ m → f m = 7 * f (m - 1) - 11 * f (m - 2) + f (m - 4)) :
    PowerSeries.mk f * (1 - 7 * PowerSeries.X + 11 * PowerSeries.X ^ 2 - PowerSeries.X ^ 4) =
      1 + 3 * PowerSeries.X - 15 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 +
        PowerSeries.X ^ 4 := by
  have e : PowerSeries.mk f * (1 - 7 * PowerSeries.X + 11 * PowerSeries.X ^ 2 - PowerSeries.X ^ 4) =
      PowerSeries.mk f
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7 * (PowerSeries.mk f * PowerSeries.X ^ 1)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 11 * (PowerSeries.mk f * PowerSeries.X ^ 2)
        - PowerSeries.mk f * PowerSeries.X ^ 4 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 11]
    ring
  have e2 : (1 + 3 * PowerSeries.X - 15 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 +
      PowerSeries.X ^ 4 : PowerSeries ℚ) =
      PowerSeries.X ^ 0
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 * PowerSeries.X ^ 1
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 15 * PowerSeries.X ^ 2
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * PowerSeries.X ^ 3
        + PowerSeries.X ^ 4 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 15,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    ring
  rw [e, e2]
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m
    · norm_num [h0]
    · norm_num [h0, h1]
    · norm_num [h0, h1, h2]
    · norm_num [h1, h2, h3]
    · norm_num [h0, h2, h3, h4]
  · simp (disch := omega) only [if_pos, if_neg]
    linarith [hq m hm]

open OMA.S_oeis_a126397 in
theorem OMA.solution : type_of% @OMA.S_oeis_a126397.main := by
  have ha : ∀ n, a n = (n3A 2 n).card := fun n => rfl
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℤ, ∀ n k, c n k = ((n3W 2 n k).card : ℤ) :=
    ⟨_, fun _ _ => rfl⟩
  have hr : ∀ m k, k < 10 → c (m + 1) k =
      ∑ j ∈ Finset.range 10, if k ≤ j + 2 ∧ j ≤ k + 2 then c m j else 0 := by
    intro m k hk
    rw [hc, n3card 2 m k hk, Finset.sum_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Nat.cast_ite, Nat.cast_zero, hc]
  have row : ∀ m n, n = m + 1 →
      c n 0 = c m 0 + c m 1 + c m 2 ∧
      c n 1 = c m 0 + c m 1 + c m 2 + c m 3 ∧
      c n 2 = c m 0 + c m 1 + c m 2 + c m 3 + c m 4 ∧
      c n 3 = c m 1 + c m 2 + c m 3 + c m 4 + c m 5 ∧
      c n 4 = c m 2 + c m 3 + c m 4 + c m 5 + c m 6 ∧
      c n 5 = c m 3 + c m 4 + c m 5 + c m 6 + c m 7 ∧
      c n 6 = c m 4 + c m 5 + c m 6 + c m 7 + c m 8 ∧
      c n 7 = c m 5 + c m 6 + c m 7 + c m 8 + c m 9 ∧
      c n 8 = c m 6 + c m 7 + c m 8 + c m 9 ∧
      c n 9 = c m 7 + c m 8 + c m 9 := by
    intro m n hn
    subst hn
    have h0 := hr m 0 (by norm_num)
    have h1 := hr m 1 (by norm_num)
    have h2 := hr m 2 (by norm_num)
    have h3 := hr m 3 (by norm_num)
    have h4 := hr m 4 (by norm_num)
    have h5 := hr m 5 (by norm_num)
    have h6 := hr m 6 (by norm_num)
    have h7 := hr m 7 (by norm_num)
    have h8 := hr m 8 (by norm_num)
    have h9 := hr m 9 (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith⟩
  have b : ∀ k, k < 10 → c 0 k = 1 := fun k hk => by rw [hc, n3base 2 k hk, Nat.cast_one]
  have b0 := b 0 (by norm_num)
  have b1 := b 1 (by norm_num)
  have b2 := b 2 (by norm_num)
  have b3 := b 3 (by norm_num)
  have b4 := b 4 (by norm_num)
  have b5 := b 5 (by norm_num)
  have b6 := b 6 (by norm_num)
  have b7 := b 7 (by norm_num)
  have b8 := b 8 (by norm_num)
  have b9 := b 9 (by norm_num)
  have v1 : c 1 0 = 3 ∧ c 1 1 = 4 ∧ c 1 2 = 5 ∧ c 1 3 = 5 ∧ c 1 4 = 5 ∧ c 1 5 = 5 ∧
      c 1 6 = 5 ∧ c 1 7 = 5 ∧ c 1 8 = 4 ∧ c 1 9 = 3 := by
    obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9⟩ := row 0 1 rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have v2 : c 2 0 = 12 ∧ c 2 1 = 17 ∧ c 2 2 = 22 ∧ c 2 3 = 24 ∧ c 2 4 = 25 ∧ c 2 5 = 25 ∧
      c 2 6 = 24 ∧ c 2 7 = 22 ∧ c 2 8 = 17 ∧ c 2 9 = 12 := by
    obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9⟩ := row 1 2 rfl
    obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := v1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have v3 : c 3 0 = 51 ∧ c 3 1 = 75 ∧ c 3 2 = 100 ∧ c 3 3 = 113 ∧ c 3 4 = 120 ∧
      c 3 5 = 120 ∧ c 3 6 = 113 ∧ c 3 7 = 100 ∧ c 3 8 = 75 ∧ c 3 9 = 51 := by
    obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9⟩ := row 2 3 rfl
    obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := v2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have v4 : c 4 0 = 226 ∧ c 4 1 = 339 ∧ c 4 2 = 459 ∧ c 4 3 = 528 ∧ c 4 4 = 566 ∧
      c 4 5 = 566 ∧ c 4 6 = 528 ∧ c 4 7 = 459 ∧ c 4 8 = 339 ∧ c 4 9 = 226 := by
    obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9⟩ := row 3 4 rfl
    obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := v3
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have comp : ∀ m k, k < 10 → c (m + 4) k + 11 * c (m + 2) k = 7 * c (m + 3) k + c m k := by
    intro m
    induction m with
    | zero =>
      intro k hk
      show c 4 k + 11 * c 2 k = 7 * c 3 k + c 0 k
      obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9⟩ := v2
      obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9⟩ := v3
      obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := v4
      interval_cases k
      · linear_combination z0 + 11 * x0 - 7 * y0 - b0
      · linear_combination z1 + 11 * x1 - 7 * y1 - b1
      · linear_combination z2 + 11 * x2 - 7 * y2 - b2
      · linear_combination z3 + 11 * x3 - 7 * y3 - b3
      · linear_combination z4 + 11 * x4 - 7 * y4 - b4
      · linear_combination z5 + 11 * x5 - 7 * y5 - b5
      · linear_combination z6 + 11 * x6 - 7 * y6 - b6
      · linear_combination z7 + 11 * x7 - 7 * y7 - b7
      · linear_combination z8 + 11 * x8 - 7 * y8 - b8
      · linear_combination z9 + 11 * x9 - 7 * y9 - b9
    | succ m ih =>
      intro k hk
      show c (m + 5) k + 11 * c (m + 3) k = 7 * c (m + 4) k + c (m + 1) k
      obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := row m (m + 1) rfl
      obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := row (m + 2) (m + 3) rfl
      obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := row (m + 3) (m + 4) rfl
      obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := row (m + 4) (m + 5) rfl
      have i0 := ih 0 (by norm_num)
      have i1 := ih 1 (by norm_num)
      have i2 := ih 2 (by norm_num)
      have i3 := ih 3 (by norm_num)
      have i4 := ih 4 (by norm_num)
      have i5 := ih 5 (by norm_num)
      have i6 := ih 6 (by norm_num)
      have i7 := ih 7 (by norm_num)
      have i8 := ih 8 (by norm_num)
      have i9 := ih 9 (by norm_num)
      interval_cases k
      · linear_combination s0 + 11 * q0 - 7 * r0 - p0 + i0 + i1 + i2
      · linear_combination s1 + 11 * q1 - 7 * r1 - p1 + i0 + i1 + i2 + i3
      · linear_combination s2 + 11 * q2 - 7 * r2 - p2 + i0 + i1 + i2 + i3 + i4
      · linear_combination s3 + 11 * q3 - 7 * r3 - p3 + i1 + i2 + i3 + i4 + i5
      · linear_combination s4 + 11 * q4 - 7 * r4 - p4 + i2 + i3 + i4 + i5 + i6
      · linear_combination s5 + 11 * q5 - 7 * r5 - p5 + i3 + i4 + i5 + i6 + i7
      · linear_combination s6 + 11 * q6 - 7 * r6 - p6 + i4 + i5 + i6 + i7 + i8
      · linear_combination s7 + 11 * q7 - 7 * r7 - p7 + i5 + i6 + i7 + i8 + i9
      · linear_combination s8 + 11 * q8 - 7 * r8 - p8 + i6 + i7 + i8 + i9
      · linear_combination s9 + 11 * q9 - 7 * r9 - p9 + i7 + i8 + i9
  have hA : ∀ m n, n = m + 1 → (a n : ℤ) = c m 0 + c m 1 + c m 2 + c m 3 + c m 4 + c m 5 +
      c m 6 + c m 7 + c m 8 + c m 9 := by
    intro m n hn
    subst hn
    have hs : (a (m + 1) : ℤ) = ∑ k ∈ Finset.range 10, c m k := by
      rw [ha, n3A_succ, Nat.cast_sum]
      exact Finset.sum_congr rfl (fun k _ => (hc m k).symm)
    rw [hs]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  have hrec : ∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 11 * a (n - 2) + a (n - 4) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 4 = m + 1 by omega]
    have t5 := hA (m + 4) (m + 5) rfl
    have t4 := hA (m + 3) (m + 4) rfl
    have t3 := hA (m + 2) (m + 3) rfl
    have t1 := hA m (m + 1) rfl
    have k0 := comp m 0 (by norm_num)
    have k1 := comp m 1 (by norm_num)
    have k2 := comp m 2 (by norm_num)
    have k3 := comp m 3 (by norm_num)
    have k4 := comp m 4 (by norm_num)
    have k5 := comp m 5 (by norm_num)
    have k6 := comp m 6 (by norm_num)
    have k7 := comp m 7 (by norm_num)
    have k8 := comp m 8 (by norm_num)
    have k9 := comp m 9 (by norm_num)
    linear_combination t5 - 7 * t4 + 11 * t3 - t1 + k0 + k1 + k2 + k3 + k4 + k5 + k6 + k7 +
      k8 + k9
  have w0 : a 0 = 1 := (ha 0).trans (n3A0 2)
  have w1 : (a 1 : ℤ) = 10 := by
    have t := hA 0 1 rfl
    linear_combination t + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9
  have w2 : (a 2 : ℤ) = 44 := by
    have t := hA 1 2 rfl
    obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := v1
    linear_combination t + z0 + z1 + z2 + z3 + z4 + z5 + z6 + z7 + z8 + z9
  have w3 : (a 3 : ℤ) = 200 := by
    have t := hA 2 3 rfl
    obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := v2
    linear_combination t + z0 + z1 + z2 + z3 + z4 + z5 + z6 + z7 + z8 + z9
  have w4 : (a 4 : ℤ) = 918 := by
    have t := hA 3 4 rfl
    obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := v3
    linear_combination t + z0 + z1 + z2 + z3 + z4 + z5 + z6 + z7 + z8 + z9
  have q0 : (a 0 : ℚ) = 1 := by exact_mod_cast w0
  have q1 : (a 1 : ℚ) = 10 := by exact_mod_cast w1
  have q2 : (a 2 : ℚ) = 44 := by exact_mod_cast w2
  have q3 : (a 3 : ℚ) = 200 := by exact_mod_cast w3
  have q4 : (a 4 : ℚ) = 918 := by exact_mod_cast w4
  have hq : ∀ m, 5 ≤ m → (a m : ℚ) = 7 * (a (m - 1) : ℚ) - 11 * (a (m - 2) : ℚ) +
      (a (m - 4) : ℚ) := by
    intro m hm
    have h := hrec m (by omega)
    have h' := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at h'
    linarith
  exact ⟨hrec, n3gf2 (fun n => (a n : ℚ)) q0 q1 q2 q3 q4 hq⟩
