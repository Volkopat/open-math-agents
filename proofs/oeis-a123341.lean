import OMAStatements.S_oeis_a123341

-- Credit: @rpinho
-- Franklin T. Adams-Watters's sequence and its prime/composite recurrence
-- are recorded in OEIS A123341. The omitted geometric weights are summable
-- by Chebyshev's lower bound, preserving a positive limit.

open Filter Finset
open scoped Topology

namespace OMA.S_oeis_a123341

private lemma prime_count_pos {n : ℕ} (hn : 2 ≤ n) : 0 < n.primeCounting := by
  exact Nat.pos_of_ne_zero fun h => by have := Nat.primeCounting_eq_zero_iff.mp h; omega

private lemma prime_count_lt {n : ℕ} (hn : 0 < n) : n.primeCounting < n := by
  have h : n.primeCounting ≤ n - 1 :=
    (Nat.count_le_iff_le_nth (p := Nat.Prime) Nat.infinite_setOfPred_prime).2 (by
      have := Nat.add_two_le_nth_prime (n - 1)
      omega)
  omega

private lemma recur {n : ℕ} (hn : 1 < n) :
    a n = ∑ i ∈ range n.primeCounting, a (n - (i + 1)) := by
  rw [a, dif_neg (by omega)]

private lemma a_pos {n : ℕ} (hn : 0 < n) : 0 < a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n = 1
    · subst n
      simp [a]
    · rw [recur (by omega)]
      have hz : 0 ∈ range n.primeCounting :=
        mem_range.mpr (prime_count_pos (n := n) (by omega))
      exact lt_of_lt_of_le (ih (n - (0 + 1)) (by omega) (by omega))
        (single_le_sum (f := fun i => a (n - (i + 1))) (fun _ _ => Nat.zero_le _) hz)

private lemma a_step_le (n : ℕ) (hn : 0 < n) : a (n + 1) ≤ 2 * a n := by
  by_cases h : n = 1
  · subst n
    have ha1 : a 1 = 1 := by simp [a]
    have hp2 : (2 : ℕ).primeCounting = 1 := by
      change Nat.primeCounting' 3 = 1
      simpa only [Nat.nth_prime_one_eq_three] using Nat.primeCounting'_nth_eq 1
    norm_num [recur (n := 2) (by decide), hp2, ha1]
  · have hp : (n + 1).primeCounting ≤ n.primeCounting + 1 := by
      unfold Nat.primeCounting Nat.primeCounting'
      rw [Nat.count_succ]
      split <;> omega
    rw [recur (show 1 < n + 1 by omega)]
    calc
      _ ≤ ∑ i ∈ range (n.primeCounting + 1), a (n + 1 - (i + 1)) :=
        sum_le_sum_of_subset (range_subset_range.mpr hp)
      _ = 2 * a n := by
        rw [sum_range_succ']
        simp only [show n + 1 - (0 + 1) = n by omega,
          show ∀ i, n + 1 - (i + 1 + 1) = n - (i + 1) by intro i; omega]
        rw [← recur (show 1 < n by omega)]
        omega

private noncomputable def b (n : ℕ) : ℝ := (a n : ℝ) / 2 ^ n

private lemma b_antitone : AntitoneOn b (Set.Ici 1) := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  have h : (a (n + 1) : ℝ) ≤ 2 * a n := by exact_mod_cast a_step_le n (by omega)
  unfold b
  rw [pow_succ]
  calc
    _ ≤ (2 * a n : ℝ) / (2 ^ n * 2) := div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by ring

private lemma geometric_weight (p : ℕ) :
    (∑ i ∈ range p, (1 : ℝ) / 2 ^ (i + 1)) = 1 - 1 / 2 ^ p := by
  induction p with
  | zero => norm_num
  | succ p ih =>
    rw [sum_range_succ, ih, pow_succ]
    field_simp
    ring

private lemma b_step_ge {n : ℕ} (hn : 0 < n) :
    b n * (1 - (1 : ℝ) / 2 ^ (n + 1).primeCounting) ≤ b (n + 1) := by
  let p := (n + 1).primeCounting
  have hrec : b (n + 1) = ∑ i ∈ range p, b (n + 1 - (i + 1)) * (1 / 2 ^ (i + 1)) := by
    conv_lhs => rw [b, recur (show 1 < n + 1 by omega), Nat.cast_sum, sum_div]
    apply sum_congr rfl
    intro i hi
    have hi' : i + 1 ≤ n + 1 :=
      (Nat.succ_le_of_lt (mem_range.mp hi)).trans (prime_count_lt (by omega)).le
    rw [b, div_mul_div_comm, mul_one, ← pow_add, Nat.sub_add_cancel hi']
  rw [hrec, ← geometric_weight, mul_sum]
  apply sum_le_sum
  intro i hi
  have hp : p < n + 1 := prime_count_lt (by omega)
  have hi' := mem_range.mp hi
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact b_antitone (by change 1 ≤ n + 1 - (i + 1); omega)
    (by change 1 ≤ n; omega) (by omega)

private lemma weights_summable : Summable (fun n : ℕ => (1 : ℝ) / 2 ^ n.primeCounting) := by
  apply (Real.summable_one_div_nat_pow.mpr (show 1 < 2 by decide)).of_norm_bounded_eventually_nat
  let c := Real.log 2
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hlogSq := (isLittleO_log_rpow_rpow_atTop (s := 1) 2 zero_lt_one).bound
    (show 0 < c ^ 2 / 8 by positivity)
  have hlog := Real.isLittleO_log_id_atTop.bound (show 0 < c / 4 by positivity)
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hcast' : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    convert hcast.comp (tendsto_add_atTop_nat 1) using 1
    ext n
    simp
  filter_upwards [hcast.eventually hlogSq, hcast'.eventually hlog, eventually_ge_atTop 2]
    with n hs hl hn
  have hn' : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hn'
  have hsq : Real.log (n : ℝ) ^ (2 : ℕ) ≤ c ^ 2 / 8 * n := by
    simpa only [Real.rpow_two, Real.rpow_one, Real.norm_of_nonneg
      (sq_nonneg (Real.log (n : ℝ))), Real.norm_of_nonneg (Nat.cast_nonneg n)] using hs
  have hnext : Real.log ((n : ℝ) + 1) ≤ c * n / 2 := by
    have hpos : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
    simp only [id_eq, Real.norm_of_nonneg hpos,
      Real.norm_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity)] at hl
    nlinarith
  have hpi := (div_le_iff₀ hlogn).1 (Chebyshev.pi_ge n)
  change (n : ℝ) * c - Real.log ((n : ℝ) + 1) ≤ (n.primeCounting : ℝ) * Real.log n at hpi
  have hp : 2 * Real.log (n : ℝ) ≤ (n.primeCounting : ℝ) * c := by
    apply (mul_le_mul_iff_of_pos_right hlogn).mp
    have hm := mul_le_mul_of_nonneg_right (show (n : ℝ) * c / 2 ≤
        (n.primeCounting : ℝ) * Real.log n by linarith) hc.le
    nlinarith
  have hb : (n : ℝ) ^ (2 : ℕ) ≤ (2 : ℝ) ^ n.primeCounting :=
    (Real.log_le_log_iff (by positivity) (by positivity)).1 (by
      simpa only [Real.log_pow, Nat.cast_ofNat] using hp)
  rw [Real.norm_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le (by positivity) hb

end OMA.S_oeis_a123341

open OMA.S_oeis_a123341 in
theorem OMA.solution : type_of% @OMA.S_oeis_a123341.main := by
  let err : ℕ → ℝ := fun n => 1 / 2 ^ n.primeCounting
  have hs : Summable err := weights_summable
  have htail : Tendsto (fun N : ℕ => ∑' i, err (i + N)) atTop (𝓝 0) :=
    tendsto_sum_nat_add err
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htail.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2))
  let start := N + 1
  let loss (k : ℕ) := ∑ i ∈ range k, err (i + (start + 1))
  have hstart : 0 < start := by dsimp [start]; omega
  have hb : 0 < b start := by unfold b; exact div_pos (by exact_mod_cast a_pos hstart) (by positivity)
  have hsum : ∀ k, loss k ≤ 1 / 2 := by
    intro k
    have hs' : Summable (fun i => err (i + (start + 1))) := (summable_nat_add_iff _).2 hs
    exact (hs'.sum_le_tsum (range k) (fun i _ => by dsimp [err]; positivity)).trans
      (hN (start + 1) (by dsimp [start]; omega)).le
  have hr : ∀ k, b start * (1 - loss k) ≤ b (k + start) := by
    intro k
    induction k with
    | zero => simp [loss]
    | succ k ih =>
      have h₀ : 0 ≤ loss k := sum_nonneg (fun i _ => by dsimp [err]; positivity)
      have h₁ : 0 ≤ err (k + (start + 1)) := by dsimp [err]; positivity
      have h₂ : err (k + (start + 1)) ≤ 1 := by
        dsimp [err]
        exact (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
      have hstep := b_step_ge (n := k + start) (by omega)
      have hstep' := (mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr h₂)).trans
        (show b (k + start) * (1 - err (k + (start + 1))) ≤ b (k + 1 + start) by
          simpa only [err, Nat.add_assoc, Nat.add_comm start 1] using hstep)
      have hloss : loss (k + 1) = loss k + err (k + (start + 1)) := sum_range_succ _ _
      rw [hloss]
      calc
        _ ≤ (b start * (1 - loss k)) * (1 - err (k + (start + 1))) := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ hb.le
          nlinarith
        _ ≤ _ := by simpa only [mul_assoc] using hstep'
  have hlower : ∀ k, b start / 2 ≤ b (k + start) := by
    intro k
    apply le_trans _ (hr k)
    simpa only [mul_one_div, mul_one] using
      mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ 1 - loss k by linarith [hsum k]) hb.le
  have ha : Antitone (fun k => b (k + start)) := by
    intro i j hij
    exact b_antitone (by change 1 ≤ i + start; omega)
      (by change 1 ≤ j + start; omega) (by omega)
  have hbd : BddBelow (Set.range (fun k => b (k + start))) :=
    ⟨b start / 2, by rintro _ ⟨k, rfl⟩; exact hlower k⟩
  have hlim := tendsto_atTop_ciInf ha hbd
  refine ⟨⨅ k, b (k + start), ?_, (tendsto_add_atTop_iff_nat start).1 hlim⟩
  exact lt_of_lt_of_le (by positivity) (le_ciInf hlower)
