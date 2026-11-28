import OMAStatements.S_oeis_a129890

-- Problem: A129890: a(n) = (2*n+2)!! - (2*n+1)!!.
-- Upstream: formal-conjectures statements/oeis-a129890.lean:0 (declaration OMA.S_oeis_a129890.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with P_m(x) = Product_{j=0..m} (x + 2j) one has
-- 1/P_{m+1}(x) = (1/P_m(x) - 1/P_m(x+2))/(2m+2). With f(k) = 1/P_n(k) and
-- H(k) = (-1)^k (f(k+1) - f(k+2)) the k-th term of the series is (H(k) - H(k+1))/(2n+2), so the
-- partial sums telescope to (H(0) - H(K))/(2n+2). H(K) tends to 0 and the terms are bounded by
-- 1/(k+1)^(n+2), so the sum is H(0)/(2n+2) = (1/(2n+1)!! - 1/(2n+2)!!)/(2n+2), and
-- (2n+2)! = (2n+2)!! (2n+1)!! gives the claim.

namespace R08A129890

open OMA.S_oeis_a129890 Filter Topology

theorem prod_pos' (m : ℕ) (x : ℝ) (hx : 0 < x) :
    0 < ∏ j ∈ Finset.range (m + 1), (x + 2 * (j : ℝ)) := by
  apply Finset.prod_pos
  intro j _
  have : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
  linarith

theorem prod_ge (m : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    x ^ (m + 1) ≤ ∏ j ∈ Finset.range (m + 1), (x + 2 * (j : ℝ)) := by
  have h : ∏ _j ∈ Finset.range (m + 1), x ≤ ∏ j ∈ Finset.range (m + 1), (x + 2 * (j : ℝ)) :=
    Finset.prod_le_prod (fun _ _ => by linarith) (fun j _ => by
      have : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
      linarith)
  rwa [Finset.prod_const, Finset.card_range] at h

theorem key_id (m : ℕ) (x : ℝ) (hx : 0 < x) :
    1 / ∏ j ∈ Finset.range (m + 2), (x + 2 * (j : ℝ)) =
      (1 / ∏ j ∈ Finset.range (m + 1), (x + 2 * (j : ℝ)) -
        1 / ∏ j ∈ Finset.range (m + 1), ((x + 2) + 2 * (j : ℝ))) / (2 * m + 2) := by
  have hA := prod_pos' m x hx
  have hB := prod_pos' m (x + 2) (by linarith)
  have hQ1 : ∏ j ∈ Finset.range (m + 2), (x + 2 * (j : ℝ)) =
      (∏ j ∈ Finset.range (m + 1), (x + 2 * (j : ℝ))) * (x + 2 * ((m + 1 : ℕ) : ℝ)) :=
    Finset.prod_range_succ _ _
  have hQ2 : ∏ j ∈ Finset.range (m + 2), (x + 2 * (j : ℝ)) =
      (∏ j ∈ Finset.range (m + 1), ((x + 2) + 2 * (j : ℝ))) * x := by
    rw [Finset.prod_range_succ']
    have e : ∀ j : ℕ, x + 2 * ((j + 1 : ℕ) : ℝ) = (x + 2) + 2 * (j : ℝ) := by
      intro j
      push_cast
      ring
    simp only [e, Nat.cast_zero, mul_zero, add_zero]
  have hm1 : (0 : ℝ) ≤ 2 * ((m + 1 : ℕ) : ℝ) := by positivity
  have hQ : 0 < ∏ j ∈ Finset.range (m + 2), (x + 2 * (j : ℝ)) := by
    rw [hQ1]
    exact mul_pos hA (by linarith)
  have hc : (0 : ℝ) < 2 * (m : ℝ) + 2 := by positivity
  have e1 : 1 / ∏ j ∈ Finset.range (m + 1), (x + 2 * (j : ℝ)) =
      (x + 2 * ((m + 1 : ℕ) : ℝ)) / ∏ j ∈ Finset.range (m + 2), (x + 2 * (j : ℝ)) := by
    rw [div_eq_div_iff hA.ne' hQ.ne', hQ1]
    ring
  have e2 : 1 / ∏ j ∈ Finset.range (m + 1), ((x + 2) + 2 * (j : ℝ)) =
      x / ∏ j ∈ Finset.range (m + 2), (x + 2 * (j : ℝ)) := by
    rw [div_eq_div_iff hB.ne' hQ.ne', hQ2]
    ring
  rw [e1, e2, div_sub_div_same, div_div, div_eq_div_iff hQ.ne' (mul_pos hQ hc).ne']
  push_cast
  ring

theorem f_bound (n m : ℕ) (hm : 1 ≤ m) :
    0 < 1 / ∏ j ∈ Finset.range (n + 1), ((m : ℝ) + 2 * (j : ℝ)) ∧
      1 / ∏ j ∈ Finset.range (n + 1), ((m : ℝ) + 2 * (j : ℝ)) ≤ 1 / (m : ℝ) := by
  have hx1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hP := prod_ge n (m : ℝ) hx1
  have hpow : (m : ℝ) ≤ (m : ℝ) ^ (n + 1) := le_self_pow₀ hx1 (by omega)
  have hPpos := prod_pos' n (m : ℝ) hm0
  exact ⟨one_div_pos.mpr hPpos, one_div_le_one_div_of_le hm0 (le_trans hpow hP)⟩

theorem odd_prod (n : ℕ) :
    ∏ j ∈ Finset.range (n + 1), ((1 : ℝ) + 2 * (j : ℝ)) = ((2 * n + 1).doubleFactorial : ℝ) := by
  induction n with
  | zero => simp [Nat.doubleFactorial]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring,
      Nat.doubleFactorial_add_two (2 * n + 1)]
    push_cast
    ring

theorem even_prod (n : ℕ) :
    ∏ j ∈ Finset.range (n + 1), ((2 : ℝ) + 2 * (j : ℝ)) = ((2 * n + 2).doubleFactorial : ℝ) := by
  induction n with
  | zero => simp [Nat.doubleFactorial]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, show 2 * (n + 1) + 2 = 2 * n + 2 + 2 by ring,
      Nat.doubleFactorial_add_two (2 * n + 2)]
    push_cast
    ring

end R08A129890

open OMA.S_oeis_a129890 R08A129890 Filter Topology in
theorem OMA.solution : type_of% @OMA.S_oeis_a129890.main := by
  intro n
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, ∀ k, f k = 1 / ∏ j ∈ Finset.range (n + 1), ((k : ℝ) + 2 * (j : ℝ)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℕ → ℝ, ∀ k, H k = (-1 : ℝ) ^ (k + 2) * (f (k + 1) - f (k + 2)) :=
    ⟨_, fun _ => rfl⟩
  have hterm : ∀ k : ℕ, (-1 : ℝ) ^ ((k + 1) + 1) /
      ∏ j ∈ Finset.range (n + 2), (((k + 1 : ℕ) : ℝ) + 2 * j) = (H k - H (k + 1)) / (2 * n + 2) := by
    intro k
    have hx : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have h := key_id n (((k + 1 : ℕ) : ℝ)) hx
    have e3 : ((k + 1 : ℕ) : ℝ) + 2 = ((k + 3 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [e3, ← hf (k + 1), ← hf (k + 3)] at h
    rw [div_eq_mul_one_div, h, hH k, hH (k + 1), show k + 1 + 1 = k + 2 from rfl,
      show k + 1 + 2 = k + 3 from rfl]
    ring
  have hpartial : ∀ K : ℕ, ∑ k ∈ Finset.range K, (-1 : ℝ) ^ ((k + 1) + 1) /
      ∏ j ∈ Finset.range (n + 2), (((k + 1 : ℕ) : ℝ) + 2 * j) = (H 0 - H K) / (2 * n + 2) := by
    intro K
    rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_div, Finset.sum_range_sub']
  have hbound : ∀ k : ℕ, ‖(-1 : ℝ) ^ ((k + 1) + 1) /
      ∏ j ∈ Finset.range (n + 2), (((k + 1 : ℕ) : ℝ) + 2 * j)‖ ≤
        1 / ((k + 1 : ℕ) : ℝ) ^ (n + 2) := by
    intro k
    have hx1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ k + 1 := by omega
      exact_mod_cast this
    have hP : ((k + 1 : ℕ) : ℝ) ^ (n + 2) ≤
        ∏ j ∈ Finset.range (n + 2), (((k + 1 : ℕ) : ℝ) + 2 * (j : ℝ)) :=
      prod_ge (n + 1) (((k + 1 : ℕ) : ℝ)) hx1
    have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) ^ (n + 2) := by positivity
    have hPpos := lt_of_lt_of_le hpos hP
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_eq_abs, abs_of_pos hPpos]
    exact one_div_le_one_div_of_le hpos hP
  have hsum0 : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ (n + 2)) :=
    (summable_nat_add_iff (f := fun m : ℕ => 1 / (m : ℝ) ^ (n + 2)) 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by omega))
  have hs : Summable (fun k : ℕ => (-1 : ℝ) ^ ((k + 1) + 1) /
      ∏ j ∈ Finset.range (n + 2), (((k + 1 : ℕ) : ℝ) + 2 * j)) :=
    Summable.of_norm_bounded hsum0 hbound
  have hHt : Tendsto H atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun K : ℕ => 2 * (1 / ((K : ℝ) + 1)))
    · intro K
      have b1 := f_bound n (K + 1) (by omega)
      have b2 := f_bound n (K + 2) (by omega)
      rw [← hf (K + 1), Nat.cast_add_one] at b1
      rw [← hf (K + 2)] at b2
      have hK2 : (1 : ℝ) / ((K + 2 : ℕ) : ℝ) ≤ 1 / ((K : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by rw [Nat.cast_add, Nat.cast_ofNat]; linarith)
      rw [hH K, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
        abs_le]
      constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, hK2]
    · have h2 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
      rw [mul_zero] at h2
      exact h2
  have hlim : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, (-1 : ℝ) ^ ((k + 1) + 1) /
      ∏ j ∈ Finset.range (n + 2), (((k + 1 : ℕ) : ℝ) + 2 * j)) atTop
        (𝓝 ((H 0 - 0) / (2 * n + 2))) := by
    have h1 := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => H 0) atTop (𝓝 (H 0))).sub hHt).div_const
      (2 * (n : ℝ) + 2)
    exact Tendsto.congr (fun K => (hpartial K).symm) h1
  have htsum : ∑' k : ℕ, (-1 : ℝ) ^ ((k + 1) + 1) /
      ∏ j ∈ Finset.range (n + 2), (((k + 1 : ℕ) : ℝ) + 2 * j) = (H 0 - 0) / (2 * n + 2) :=
    tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hlim
  have hH0 : H 0 = 1 / ((2 * n + 1).doubleFactorial : ℝ) - 1 / ((2 * n + 2).doubleFactorial : ℝ) := by
    rw [hH 0, show (0 : ℕ) + 1 = 1 from rfl, show (0 : ℕ) + 2 = 2 from rfl, hf 1, hf 2,
      Nat.cast_one, Nat.cast_ofNat, odd_prod n, even_prod n]
    norm_num
  have hfac0 := Nat.factorial_eq_mul_doubleFactorial (2 * n + 1)
  rw [show 2 * n + 1 + 1 = 2 * n + 2 from rfl] at hfac0
  have hfac : ((2 * n + 2).factorial : ℝ) =
      ((2 * n + 2).doubleFactorial : ℝ) * ((2 * n + 1).doubleFactorial : ℝ) := by
    exact_mod_cast hfac0
  have hO : ((2 * n + 1).doubleFactorial : ℝ) ≠ 0 := by positivity
  have hE : ((2 * n + 2).doubleFactorial : ℝ) ≠ 0 := by positivity
  have hden : ((2 * n + 1).doubleFactorial : ℝ) * ((2 * n + 2).doubleFactorial : ℝ) *
      (2 * (n : ℝ) + 2) ≠ 0 := by positivity
  rw [htsum, hH0, sub_zero, hfac, a]
  push_cast
  rw [div_sub_div 1 1 hO hE, div_div, mul_div_assoc', eq_div_iff hden]
  ring
