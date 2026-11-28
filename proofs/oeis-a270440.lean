import OMAStatements.S_oeis_a270440

-- Problem: A270440: Least k such that binomial(k, 2) >= binomial(2*n, n).
-- Upstream: formal-conjectures statements/oeis-a270440.lean:0 (declaration OMA.S_oeis_a270440.main)
-- Credit: @a5teri5k (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Asymptotics Topology

namespace OMA.A270440

noncomputable def B (n : ℕ) : ℝ := ((2 * n).choose n : ℝ)

lemma key {C : ℕ} (hC : 1 ≤ C) (k : ℕ) :
    C ≤ k.choose 2 ↔ (Real.sqrt (8 * (C : ℝ) + 1) + 1) / 2 ≤ k := by
  rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by norm_num)]
  have hid : k * (k - 1) + k = k * k := by
    cases k with
    | zero => simp
    | succ m => simp only [Nat.add_sub_cancel]; ring
  have hs0 : 0 ≤ Real.sqrt (8 * (C : ℝ) + 1) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (8 * (C : ℝ) + 1) ^ 2 = 8 * C + 1 := Real.sq_sqrt (by positivity)
  have hC' : (1 : ℝ) ≤ C := by exact_mod_cast hC
  constructor
  · intro h
    have h' : 2 * C + k ≤ k * k := by
      generalize k * (k - 1) = P at h hid
      generalize k * k = Q at hid
      omega
    have hr : (2 * C + k : ℝ) ≤ k * k := by exact_mod_cast h'
    have hk : (1 : ℝ) ≤ k := by nlinarith
    have : Real.sqrt (8 * (C : ℝ) + 1) ≤ 2 * k - 1 := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    linarith
  · intro h
    have h2 : Real.sqrt (8 * (C : ℝ) + 1) ≤ 2 * k - 1 := by linarith
    have h3 : (8 * (C : ℝ) + 1) ≤ (2 * k - 1) ^ 2 := by
      rw [← hs2]; exact pow_le_pow_left₀ hs0 h2 2
    have hr : (2 * C + k : ℝ) ≤ k * k := by nlinarith
    have h' : 2 * C + k ≤ k * k := by exact_mod_cast hr
    generalize k * (k - 1) = P at hid ⊢
    generalize k * k = Q at hid h'
    omega

lemma part1 (n : ℕ) :
    OMA.S_oeis_a270440.a n = ⌈(Real.sqrt (8 * ((2 * n).choose n : ℝ) + 1) + 1) / 2⌉₊ := by
  have hC : 1 ≤ (2 * n).choose n := Nat.choose_pos (by omega)
  have hS : ∀ k, k ∈ {k : ℕ | (2 * n).choose n ≤ k.choose 2} ↔
      (Real.sqrt (8 * ((2 * n).choose n : ℝ) + 1) + 1) / 2 ≤ k := fun k => key hC k
  unfold OMA.S_oeis_a270440.a
  apply le_antisymm
  · exact Nat.sInf_le ((hS _).2 (Nat.le_ceil _))
  · have hne : ({k : ℕ | (2 * n).choose n ≤ k.choose 2}).Nonempty :=
      ⟨_, (hS _).2 (Nat.le_ceil _)⟩
    exact Nat.ceil_le.2 ((hS _).1 (Nat.sInf_mem hne))

lemma ratio_eq {n : ℕ} (hn : n ≠ 0) :
    B n * Real.sqrt (Real.pi * n) / 4 ^ n =
      Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2 * Real.sqrt Real.pi := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold B Stirling.stirlingSeq
  rw [Nat.cast_choose ℝ (by omega : n ≤ 2 * n), show 2 * n - n = n by omega]
  have htp : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnr
  have e1 : Real.sqrt (2 * ((2 * n : ℕ) : ℝ)) = 2 * Real.sqrt n := by
    rw [show (2 * ((2 * n : ℕ) : ℝ)) = 2 ^ 2 * n by push_cast; ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have e2 : Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt n := Real.sqrt_mul (by norm_num) _
  have e3 : Real.sqrt (Real.pi * n) = Real.sqrt Real.pi * Real.sqrt n :=
    Real.sqrt_mul Real.pi_pos.le _
  have e4 : (((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n) =
      (2 ^ n) ^ 2 * (((n : ℝ) / Real.exp 1) ^ n) ^ 2 := by
    rw [show (((2 * n : ℕ) : ℝ) / Real.exp 1) = 2 * ((n : ℝ) / Real.exp 1) by push_cast; ring,
      mul_pow, ← pow_mul, ← pow_mul, mul_comm n 2]
  have e5 : (4 : ℝ) ^ n = (2 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [e1, e2, e3, e4, e5]
  have hq : 0 < ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have hf : 0 < ((2 * n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hf' : 0 < ((n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  generalize ((n : ℝ) / Real.exp 1) ^ n = Q at hq ⊢
  generalize ((2 * n).factorial : ℝ) = A at hf ⊢
  generalize ((n).factorial : ℝ) = F at hf' ⊢
  generalize Real.sqrt (n : ℝ) = t at htp ⊢
  rw [div_pow, mul_pow, mul_pow, h2]
  field_simp

lemma ratio_tendsto :
    Tendsto (fun n : ℕ => B n * Real.sqrt (Real.pi * n) / 4 ^ n) atTop (𝓝 1) := by
  have h1 := Stirling.tendsto_stirlingSeq_sqrt_pi
  have h2 : Tendsto (fun n : ℕ => Stirling.stirlingSeq (2 * n)) atTop (𝓝 (Real.sqrt Real.pi)) :=
    h1.comp (tendsto_atTop_mono (fun n => show n ≤ 2 * n by omega) tendsto_id)
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have h3 := (h2.div (h1.pow 2) (pow_ne_zero 2 hpi)).mul_const (Real.sqrt Real.pi)
  have h4 : Real.sqrt Real.pi / Real.sqrt Real.pi ^ 2 * Real.sqrt Real.pi = 1 := by
    field_simp
  rw [h4] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (ratio_eq hn).symm

lemma g_eq {n : ℕ} :
    (2 : ℝ) ^ ((n : ℝ) + 1 / 2) / (Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4) =
      Real.sqrt (2 * 4 ^ n / Real.sqrt (Real.pi * n)) := by
  have hpn : 0 ≤ Real.pi * (n : ℝ) := by positivity
  have hq : (Real.pi * n) ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt (Real.pi * n)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hpn]; norm_num
  have h2 : (2 : ℝ) ^ ((n : ℝ) + 1 / 2) = 2 ^ n * Real.sqrt 2 := by
    rw [Real.rpow_add two_pos, Real.rpow_natCast, Real.sqrt_eq_rpow]
  have h4 : Real.sqrt (2 * 4 ^ n) = Real.sqrt 2 * 2 ^ n := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) ^ n = (2 ^ n) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num, Real.sqrt_sq (by positivity)]
  rw [hq, h2, Real.sqrt_div' _ (Real.sqrt_nonneg _), h4, mul_comm]

lemma part2 : (fun n : ℕ => (OMA.S_oeis_a270440.a n : ℝ)) ~[atTop]
      (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) + 1 / 2) / (Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4)) := by
  have hB1 : ∀ n, (1 : ℝ) ≤ B n := fun n => by
    unfold B; exact_mod_cast Nat.choose_pos (by omega)
  have hS : (fun n : ℕ => (OMA.S_oeis_a270440.a n : ℝ)) ~[atTop]
      (fun n => Real.sqrt (2 * B n)) := by
    unfold IsEquivalent
    have hbig : (fun n : ℕ => (OMA.S_oeis_a270440.a n : ℝ) - Real.sqrt (2 * B n)) =O[atTop]
        (fun _ => (1 : ℝ)) := by
      refine IsBigO.of_bound 2 (Eventually.of_forall fun n => ?_)
      rw [part1 n, show ((2 * n).choose n : ℝ) = B n from rfl]
      have hC := hB1 n
      generalize B n = C at hC ⊢
      have hx := Nat.le_ceil ((Real.sqrt (8 * C + 1) + 1) / 2)
      have hx2 := Nat.ceil_lt_add_one
        (show 0 ≤ (Real.sqrt (8 * C + 1) + 1) / 2 by positivity)
      have hs : 0 ≤ Real.sqrt (2 * C) := Real.sqrt_nonneg _
      have hs2 : Real.sqrt (2 * C) ^ 2 = 2 * C := Real.sq_sqrt (by linarith)
      have l1 : 2 * Real.sqrt (2 * C) ≤ Real.sqrt (8 * C + 1) := by
        rw [Real.le_sqrt (by linarith) (by linarith)]; nlinarith
      have l2 : Real.sqrt (8 * C + 1) ≤ 2 * Real.sqrt (2 * C) + 1 := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      rw [Real.norm_eq_abs, norm_one, mul_one, abs_le]
      constructor <;> linarith
    have hlit : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n => Real.sqrt (2 * B n)) := by
      rw [isLittleO_one_left_iff]
      have ht : Tendsto (fun n : ℕ => Real.sqrt (2 * B n)) atTop atTop := by
        refine Real.tendsto_sqrt_atTop.comp ?_
        refine tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
        have h := Nat.choose_le_centralBinom 1 n
        rw [Nat.choose_one_right, Nat.centralBinom_eq_two_mul_choose] at h
        have h' : (n : ℝ) ≤ ((2 * n).choose n : ℝ) := by exact_mod_cast (by omega : n ≤ _)
        have h0 : (0 : ℝ) ≤ ((2 * n).choose n : ℝ) := by positivity
        show (n : ℝ) ≤ 2 * B n
        unfold B
        linarith
      refine ht.congr' ?_
      filter_upwards with n
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hbig.trans_isLittleO hlit
  have hT : (fun n : ℕ => Real.sqrt (2 * B n)) ~[atTop]
      (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) + 1 / 2) / (Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4)) := by
    apply isEquivalent_of_tendsto_one
    have h := ratio_tendsto.sqrt
    rw [Real.sqrt_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hsp : 0 < Real.sqrt (Real.pi * n) := Real.sqrt_pos.2 (by positivity)
    simp only [Pi.div_apply]
    rw [g_eq, ← Real.sqrt_div' _ (by positivity)]
    congr 1
    field_simp
  exact hS.trans hT

end OMA.A270440

theorem OMA.solution : type_of% @OMA.S_oeis_a270440.main :=
  ⟨OMA.A270440.part1, OMA.A270440.part2⟩
