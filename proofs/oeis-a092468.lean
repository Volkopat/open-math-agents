import OMAStatements.S_oeis_a092468

/-! A weighted binomial estimate gives an exponential upper bound along multiples of three. A ratio limit above 39/8 would force faster growth on this same subsequence. -/

open Filter Topology
open OMA.S_oeis_a092468

private theorem weightedChoose (r s : ℕ) (x y : ℚ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ r * y ^ s * (r+s).choose r ≤ (x+y) ^ (r+s) := by
  rw [add_pow]
  have hr : r ∈ Finset.range (r+s+1) := Finset.mem_range.mpr (by omega)
  simpa using Finset.single_le_sum
    (f := fun v : ℕ => x^v * y^(r+s-v) * ((r+s).choose v : ℚ))
    (fun v _ => by positivity) hr

private theorem termBound (m i j k : ℕ) (h : i+j+k = 3*m) (hij : i ≤ j) (hjk : j ≤ k) :
    ((3*m + 2*k).factorial : ℚ) / (i.factorial * j.factorial * (3*k).factorial)
      ≤ (3125/27 : ℚ)^m := by
  have hN : 3*m + 2*k = (i+j) + 3*k := by omega
  have hchoose : ((i+j).choose i : ℚ) ≤ (2:ℚ)^(i+j) := by
    simpa [show (1:ℚ)+1=2 by norm_num] using weightedChoose i j 1 1 (by norm_num) (by norm_num)
  have hweight : (2:ℚ)^(i+j) * (3:ℚ)^(3*k) * ((i+j+3*k).choose (i+j) : ℚ)
      ≤ (5:ℚ)^(i+j+3*k) := by
    simpa [show (2:ℚ)+3=5 by norm_num] using weightedChoose (i+j) (3*k) 2 3 (by norm_num) (by norm_num)
  have hfac : ((3*m + 2*k).factorial : ℚ) / (i.factorial * j.factorial * (3*k).factorial) =
      ((i+j).choose i : ℚ) * ((i+j+3*k).choose (i+j) : ℚ) := by
    rw [hN, Nat.cast_add_choose, Nat.cast_add_choose]
    field_simp
  calc
    _ ≤ (5:ℚ)^(3*m + 2*k) / (3:ℚ)^(3*k) := by
      rw [hfac, hN, le_div_iff₀ (by positivity)]
      calc
        _ = ((i+j).choose i : ℚ) * (3:ℚ)^(3*k) * ((i+j+3*k).choose (i+j) : ℚ) := by ring
        _ ≤ _ := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hchoose
          (by positivity)) (by positivity)).trans hweight
    _ = (5:ℚ)^(3*m) * (25/27:ℚ)^k := by
      rw [pow_add, pow_mul 5 2, pow_mul 3 3, div_pow]
      norm_num
      ring
    _ ≤ (5:ℚ)^(3*m) * (25/27:ℚ)^m := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (show m ≤ k by omega)) (by positivity)
    _ = (3125/27 : ℚ)^m := by
      rw [pow_mul, ← mul_pow]
      norm_num

private theorem upper (m : ℕ) : (OMA.S_oeis_a092468.a (3*m) : ℝ) ≤
    (3*(m:ℝ)+1)^3 * (3125/27 : ℝ)^m := by
  suffices h : a (3*m) ≤ (3*(m:ℚ)+1)^3 * (3125/27 : ℚ)^m by
    have hr := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at hr
    exact hr
  unfold a
  apply le_trans (Finset.sum_le_card_nsmul _ _ ((3125/27:ℚ)^m) ?_)
  · rw [nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hc := Finset.card_filter_le
      (s := Finset.range (3*m+1) ×ˢ Finset.range (3*m+1) ×ˢ Finset.range (3*m+1))
      (p := fun t => t.1 + t.2.1 + t.2.2 = 3*m ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2)
    simp only [Finset.card_product, Finset.card_range] at hc
    exact_mod_cast hc.trans_eq (by ring : _ = (3*m+1)^3)
  · rintro ⟨i,j,k⟩ ht
    obtain ⟨h, hij, hjk⟩ := (Finset.mem_filter.mp ht).2
    exact termBound m i j k h hij hjk

private theorem apos (n : ℕ) : 0 < (a n : ℝ) := by
  exact_mod_cast (show 0 < a n by
    unfold a
    apply Finset.sum_pos'
    · intro t _
      positivity
    · refine ⟨(0, 0, n), ?_, ?_⟩
      · simp
      · positivity)

private theorem limit_gt : (39/8 : ℝ) < L := by
  let u : ℝ := (73 + 6 * Real.sqrt 87) ^ (1 / 3 : ℝ)
  have hbase : 0 ≤ 73 + 6 * Real.sqrt 87 := by positivity
  have hc : u ^ 3 = 73 + 6 * Real.sqrt 87 := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
    norm_num
  have hs : (9327/1000 : ℝ) < Real.sqrt 87 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 87 by norm_num), Real.sqrt_nonneg 87]
  have hu : (1263/250 : ℝ) < u := by
    by_contra! h
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ u) h 3
    norm_num at hp
    linarith
  change 39/8 < u/3 + 13/(3*u) + 7/3
  have up : 0 < 3*u := by linarith
  rw [show u/3 + 13/(3*u) + 7/3 = (u^2 + 13 + 7*u)/(3*u) by
    field_simp [ne_of_gt (show 0 < u by linarith)], lt_div_iff₀ up]
  nlinarith [sq_nonneg (u - 1263/250)]

private theorem ratio_growth_impossible (a : ℕ → ℚ) (L : ℝ)
    (upper : ∀ m : ℕ, (a (3*m) : ℝ) ≤ (3*(m:ℝ)+1)^3 * (3125/27 : ℝ)^m)
    (apos : ∀ n : ℕ, 0 < (a n : ℝ)) (limit_gt : (39/8 : ℝ) < L) :
    ¬ Tendsto (fun n : ℕ => (a (n+1) : ℝ) / a n) atTop (𝓝 L) := by
  intro h
  let r : ℝ := 39 / 8
  have hr : 0 < r := by norm_num [r]
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually (eventually_gt_nhds limit_gt))
  let c : ℝ := (a N : ℝ) / r^N
  have hc : 0 < c := div_pos (apos N) (pow_pos hr _)
  have lower (k : ℕ) : c * r^(N+k) ≤ (a (N+k) : ℝ) := by
    induction k with
    | zero => simp [c, ne_of_gt (pow_pos hr N)]
    | succ k ih =>
      have step := (lt_div_iff₀ (apos (N+k))).mp (hN (N+k) (by omega))
      rw [Nat.add_succ, pow_succ, ← mul_assoc]
      exact (mul_le_mul_of_nonneg_right ih hr.le).trans (by simpa [mul_comm, r] using step.le)
  let q : ℝ := (3125/27)/r^3
  have hq : 0 ≤ q := by norm_num [q,r]
  have hq' : q < 1 := by norm_num [q,r]
  have decay : Tendsto (fun m : ℕ => 64 * ((m:ℝ)^3 * q^m)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_mul_const_pow_of_lt_one 3 hq hq').const_mul 64
  obtain ⟨m, hm, hm', hsmall⟩ :=
    ((eventually_ge_atTop N).and ((eventually_ge_atTop 1).and (decay.eventually (Iio_mem_nhds hc)))).exists
  have low : c * r^(3*m) ≤ (a (3*m) : ℝ) := by
    simpa only [Nat.add_sub_of_le (show N ≤ 3*m by omega)] using lower (3*m-N)
  have cap := low.trans (upper m)
  have hpow : r^(3*m) = (r^3)^m := pow_mul _ _ _
  rw [hpow] at cap
  have bound : c ≤ (3*(m:ℝ)+1)^3 * q^m := by
    dsimp only [q]
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    exact cap
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm'
  have poly : (3*(m:ℝ)+1)^3 ≤ (4*(m:ℝ))^3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have comp := mul_le_mul_of_nonneg_right poly (pow_nonneg hq m)
  linarith only [bound, show (3*(m:ℝ)+1)^3 * q^m ≤ 64*((m:ℝ)^3*q^m) by calc
    _ ≤ (4*(m:ℝ))^3 * q^m := comp
    _ = _ := by ring, hsmall]

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a092468.main) := 
  ratio_growth_impossible a L upper apos limit_gt
