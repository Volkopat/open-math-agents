import OMAStatements.S_oeis_a002193

open OMA.S_oeis_a002193

private noncomputable def qVal : ℝ := Real.exp (-Real.pi)

private noncomputable def gPlus (p : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))

private noncomputable def gMinus (p : ℤ × ℤ) : ℝ :=
  (-1 : ℝ) ^ (p.1 + p.2).natAbs * gPlus p

private noncomputable def thetaA : ℝ :=
  ∑' n : ℤ, Real.exp (-2 * Real.pi * (n : ℝ) ^ 2)

private noncomputable def thetaB : ℝ :=
  ∑' n : ℤ, Real.exp (-2 * Real.pi * ((n : ℝ) + 1 / 2) ^ 2)

private noncomputable def thetaC : ℝ :=
  ∑' m : ℤ, Real.exp (-Real.pi * (1 / 2) * (m : ℝ) ^ 2)

private lemma mem_reps_iff (k : ℕ) (m : ℤ × ℤ) :
    m ∈ reps k ↔ m.1 ^ 2 + m.2 ^ 2 = (k : ℤ) := by
  have hsq : ∀ z : ℤ, z ≤ z ^ 2 ∧ -z ≤ z ^ 2 := by
    intro z
    rcases lt_trichotomy z 0 with hz | rfl | hz
    · constructor <;> nlinarith
    · norm_num
    · constructor <;> nlinarith
  simp only [reps, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun ⟨_, heq⟩ => heq
  · intro heq
    have hx := hsq m.1
    have hy := hsq m.2
    have h1 : m.1 ^ 2 ≤ (k : ℤ) := by nlinarith [sq_nonneg m.2]
    have h2 : m.2 ^ 2 ≤ (k : ℤ) := by nlinarith [sq_nonneg m.1]
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, heq⟩

private lemma reps_zero : reps 0 = {(0, 0)} := by
  ext ⟨x, y⟩
  rw [mem_reps_iff, Finset.mem_singleton, Prod.mk.injEq]
  norm_num
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  · rintro ⟨rfl, rfl⟩
    norm_num

private lemma r3_zero : r₃ 0 = 1 := by
  rw [r₃, reps_zero]
  rfl

private lemma r4_zero : r₄ 0 = 1 := by
  rw [r₄, reps_zero]
  simp

private lemma bList_length (k : ℕ) : (bList k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [bList, ih]

private lemma bList_getD (j k : ℕ) (hjk : j ≤ k) : (bList k).getD j 0 = b j := by
  induction k generalizing j with
  | zero =>
    have hj : j = 0 := by omega
    subst hj
    rfl
  | succ k ih =>
    rcases eq_or_lt_of_le hjk with rfl | hlt
    · rfl
    · have hlen : j < (bList k).length := by rw [bList_length]; exact hlt
      simp only [bList, List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
      rw [← List.getD_eq_getElem?_getD]
      exact ih j (by omega)

private lemma b_zero : b 0 = 1 := by
  rw [b, bList, List.getD_eq_getElem?_getD]
  simp [r3_zero]

private lemma b_succ (k : ℕ) :
    b (k + 1) = r₃ (k + 1) - ∑ i ∈ Finset.range (k + 1), b i * r₄ (k + 1 - i) := by
  have hlen : (bList k).length = k + 1 := bList_length k
  have hb : b (k + 1) = (bList (k + 1)).getD (k + 1) 0 := rfl
  rw [hb, bList, List.getD_eq_getElem?_getD, List.getElem?_append_right hlen.le, hlen, Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.getD_some]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [bList_getD i k hi']

private lemma b_recurrence (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), b i * r₄ (k - i) = r₃ k := by
  cases k with
  | zero =>
    simp [b_zero, r4_zero, r3_zero]
  | succ k =>
    rw [Finset.sum_range_succ, Nat.sub_self, r4_zero, mul_one, b_succ k]
    ring

private lemma sq_two_mul_add_one_le (j : ℕ) (hj : 1 ≤ j) : (2 * j + 1) ^ 2 ≤ 9 ^ j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases eq_or_lt_of_le hj with h1 | hgt
    · have hj0 : j = 0 := by omega
      subst hj0
      norm_num
    · have hj1 : 1 ≤ j := by omega
      have ih' := ih hj1
      have hstep : 2 * (j + 1) + 1 ≤ 3 * (2 * j + 1) := by omega
      calc
        (2 * (j + 1) + 1) ^ 2 ≤ (3 * (2 * j + 1)) ^ 2 := Nat.pow_le_pow_left hstep 2
        _ = 9 * (2 * j + 1) ^ 2 := by ring
        _ ≤ 9 * 9 ^ j := Nat.mul_le_mul_left 9 ih'
        _ = 9 ^ (j + 1) := by rw [pow_succ']

private lemma r3_natAbs_le (k : ℕ) : (r₃ k).natAbs ≤ 9 ^ k := by
  cases k with
  | zero =>
    rw [r3_zero]
    norm_num
  | succ k =>
    rw [r₃, Int.natAbs_natCast]
    have hsub : reps (k + 1) ⊆ Finset.Icc (-((k + 1 : ℕ) : ℤ)) (k + 1 : ℕ) ×ˢ
        Finset.Icc (-((k + 1 : ℕ) : ℤ)) (k + 1 : ℕ) :=
      Finset.filter_subset _ _
    have hcard : (Finset.Icc (-((k + 1 : ℕ) : ℤ)) (k + 1 : ℕ) ×ˢ
        Finset.Icc (-((k + 1 : ℕ) : ℤ)) (k + 1 : ℕ)).card = (2 * (k + 1) + 1) ^ 2 := by
      rw [Finset.card_product, Int.card_Icc]
      have hlen : (((k + 1 : ℕ) : ℤ) + 1 - -((k + 1 : ℕ) : ℤ)).toNat = 2 * (k + 1) + 1 := by omega
      rw [hlen, sq]
    exact (Finset.card_le_card hsub).trans (hcard ▸ sq_two_mul_add_one_le (k + 1) (by omega))

private lemma r4_natAbs_le_r3 (k : ℕ) : (r₄ k).natAbs ≤ (r₃ k).natAbs := by
  have habs : |(r₄ k : ℤ)| ≤ r₃ k := by
    rw [r₄, r₃]
    calc
      |∑ m ∈ reps k, (-1 : ℤ) ^ (m.1 + m.2).natAbs|
          ≤ ∑ m ∈ reps k, |(-1 : ℤ) ^ (m.1 + m.2).natAbs| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ _m ∈ reps k, (1 : ℤ) := by
          refine Finset.sum_congr rfl fun m _ => abs_neg_one_pow _
      _ = ((reps k).card : ℤ) := by simp
  zify
  rw [abs_of_nonneg (show (0 : ℤ) ≤ r₃ k by rw [r₃]; exact Nat.cast_nonneg _)]
  exact habs

private lemma r4_natAbs_le (k : ℕ) : (r₄ k).natAbs ≤ 9 ^ k :=
  (r4_natAbs_le_r3 k).trans (r3_natAbs_le k)

private lemma geom_sum_two_mul_pow (k : ℕ) :
    9 ^ k + ∑ i ∈ Finset.range k, 18 ^ i * 9 ^ (k - i) = 18 ^ k := by
  have hgeom : ∀ m : ℕ, 1 + ∑ i ∈ Finset.range m, 2 ^ i = 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      omega
  have hterm : ∑ i ∈ Finset.range k, 18 ^ i * 9 ^ (k - i) =
      (∑ i ∈ Finset.range k, 2 ^ i) * 9 ^ k := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := (Finset.mem_range.mp hi).le
    have h18 : 18 ^ i = 2 ^ i * 9 ^ i := by
      rw [show (18 : ℕ) = 2 * 9 by norm_num, mul_pow]
    rw [h18, mul_assoc, ← pow_add, Nat.add_sub_of_le hik]
  rw [hterm]
  calc
    9 ^ k + (∑ i ∈ Finset.range k, 2 ^ i) * 9 ^ k
        = (1 + ∑ i ∈ Finset.range k, 2 ^ i) * 9 ^ k := by ring
    _ = 2 ^ k * 9 ^ k := by rw [hgeom k]
    _ = 18 ^ k := by rw [← mul_pow]; norm_num

private lemma abs_int_le_of_natAbs {z : ℤ} {n : ℕ} (h : z.natAbs ≤ n) : |z| ≤ (n : ℤ) := by
  rcases le_total z 0 with hz | hz
  · rw [abs_of_nonpos hz]; omega
  · rw [abs_of_nonneg hz]; omega

private lemma b_natAbs_le (k : ℕ) : (b k).natAbs ≤ 18 ^ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      rw [b_zero]
      norm_num
    | succ k =>
      have habs : |(b (k + 1) : ℤ)| ≤
          |(r₃ (k + 1) : ℤ)| + ∑ i ∈ Finset.range (k + 1), |(b i : ℤ)| * |(r₄ (k + 1 - i) : ℤ)| := by
        rw [b_succ k]
        refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
        calc
          |∑ i ∈ Finset.range (k + 1), b i * r₄ (k + 1 - i)|
              ≤ ∑ i ∈ Finset.range (k + 1), |b i * r₄ (k + 1 - i)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i ∈ Finset.range (k + 1), |b i| * |r₄ (k + 1 - i)| := by
            refine Finset.sum_congr rfl fun i _ => abs_mul _ _
      have hr3 : |(r₃ (k + 1) : ℤ)| ≤ ((9 ^ (k + 1) : ℕ) : ℤ) :=
        abs_int_le_of_natAbs (r3_natAbs_le (k + 1))
      have hsum : ∑ i ∈ Finset.range (k + 1), |(b i : ℤ)| * |(r₄ (k + 1 - i) : ℤ)| ≤
          ∑ i ∈ Finset.range (k + 1), ((18 ^ i : ℕ) : ℤ) * ((9 ^ (k + 1 - i) : ℕ) : ℤ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik : i < k + 1 := Finset.mem_range.mp hi
        refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
        · exact abs_int_le_of_natAbs (ih i hik)
        · exact abs_int_le_of_natAbs (r4_natAbs_le (k + 1 - i))
      have hZ : |(b (k + 1) : ℤ)| ≤ ((18 ^ (k + 1) : ℕ) : ℤ) := by
        calc
          |(b (k + 1) : ℤ)|
              ≤ ((9 ^ (k + 1) : ℕ) : ℤ) +
                ∑ i ∈ Finset.range (k + 1), ((18 ^ i : ℕ) : ℤ) * ((9 ^ (k + 1 - i) : ℕ) : ℤ) :=
            habs.trans (add_le_add hr3 hsum)
          _ = (((9 ^ (k + 1) + ∑ i ∈ Finset.range (k + 1), 18 ^ i * 9 ^ (k + 1 - i) : ℕ)) : ℤ) := by
            push_cast
            rfl
          _ = ((18 ^ (k + 1) : ℕ) : ℤ) := by
            rw [geom_sum_two_mul_pow (k + 1)]
      rcases le_total (b (k + 1)) 0 with hz | hz
      · rw [abs_of_nonpos hz] at hZ; omega
      · rw [abs_of_nonneg hz] at hZ; omega

private lemma qVal_pos : 0 < qVal := Real.exp_pos _

private lemma eighteen_mul_qVal_lt_one : 18 * qVal < 1 := by
  have hexp1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpow : (18 : ℝ) < Real.exp 3 := by
    calc
      (18 : ℝ) < (2.7 : ℝ) ^ 3 := by norm_num
      _ < (Real.exp 1) ^ 3 := by gcongr
      _ = Real.exp ((3 : ℕ) : ℝ) := Real.exp_one_pow 3
      _ = Real.exp 3 := by norm_num
  have hexp_pi : (18 : ℝ) < Real.exp Real.pi :=
    hpow.trans (Real.exp_lt_exp.mpr Real.pi_gt_three)
  have hpos : 0 < Real.exp Real.pi := Real.exp_pos Real.pi
  calc
    18 * qVal = 18 * (Real.exp Real.pi)⁻¹ := by rw [qVal, Real.exp_neg]
    _ < Real.exp Real.pi * (Real.exp Real.pi)⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hpos.ne'

private lemma summable_norm_b : Summable fun k : ℕ => ‖(b k : ℝ) * qVal ^ k‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (summable_geometric_of_lt_one (by positivity [qVal_pos]) eighteen_mul_qVal_lt_one)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg qVal_pos.le k), mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg qVal_pos.le k)
  have hb : |(b k : ℝ)| ≤ ((18 ^ k : ℕ) : ℝ) := by
    rw [← Int.cast_abs]
    exact_mod_cast abs_int_le_of_natAbs (b_natAbs_le k)
  simpa using hb

private lemma summable_norm_r4 : Summable fun k : ℕ => ‖(r₄ k : ℝ) * qVal ^ k‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (summable_geometric_of_lt_one (by positivity [qVal_pos]) eighteen_mul_qVal_lt_one)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg qVal_pos.le k), mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg qVal_pos.le k)
  have hr : (r₄ k).natAbs ≤ 18 ^ k := (r4_natAbs_le k).trans (Nat.pow_le_pow_left (by norm_num) k)
  have hr' : |(r₄ k : ℝ)| ≤ ((18 ^ k : ℕ) : ℝ) := by
    rw [← Int.cast_abs]
    exact_mod_cast abs_int_le_of_natAbs hr
  simpa using hr'

private lemma cauchy_b_mul_r4 :
    (∑' k : ℕ, (b k : ℝ) * qVal ^ k) * (∑' k : ℕ, (r₄ k : ℝ) * qVal ^ k) =
      ∑' k : ℕ, (r₃ k : ℝ) * qVal ^ k := by
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm summable_norm_b summable_norm_r4]
  refine tsum_congr fun k => ?_
  calc
    ∑ i ∈ Finset.range (k + 1), (b i : ℝ) * qVal ^ i * ((r₄ (k - i) : ℝ) * qVal ^ (k - i))
        = ∑ i ∈ Finset.range (k + 1), ((b i * r₄ (k - i) : ℤ) : ℝ) * qVal ^ k := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          push_cast
          calc
            (b i : ℝ) * qVal ^ i * ((r₄ (k - i) : ℝ) * qVal ^ (k - i))
                = (b i : ℝ) * (r₄ (k - i) : ℝ) * (qVal ^ i * qVal ^ (k - i)) := by ring
            _ = (b i : ℝ) * (r₄ (k - i) : ℝ) * qVal ^ k := by
                rw [← pow_add, Nat.add_sub_of_le hik]
    _ = ((∑ i ∈ Finset.range (k + 1), b i * r₄ (k - i) : ℤ) : ℝ) * qVal ^ k := by
          rw [← Finset.sum_mul]
          push_cast
          rfl
    _ = (r₃ k : ℝ) * qVal ^ k := by
          rw [b_recurrence k]

private lemma summable_exp_neg_mul_int_sq {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2) := by
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hnat : Summable fun m : ℕ => Real.exp (-c * (m : ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun m => ?_)
      (summable_geometric_of_lt_one hr0 hr1)
    have hm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      cases m with
      | zero => norm_num
      | succ m =>
        have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by norm_cast; omega
        nlinarith
    calc
      Real.exp (-c * (m : ℝ) ^ 2) ≤ Real.exp (-c * (m : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp ((m : ℕ) * (-c)) := by congr 1; ring
      _ = (Real.exp (-c)) ^ m := Real.exp_nat_mul (-c) m
  have hneg : Summable fun m : ℕ => Real.exp (-c * ((-m : ℤ) : ℝ) ^ 2) := by
    simpa only [Int.cast_neg, Int.cast_natCast, neg_sq] using hnat
  exact summable_int_iff_summable_nat_and_neg.mpr ⟨by simpa using hnat, hneg⟩

private lemma summable_prod_exp {a : ℤ → ℝ} {b : ℤ → ℝ}
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ y, 0 ≤ b y)
    (ha : Summable a) (hb : Summable b) :
    Summable fun p : ℤ × ℤ => a p.1 * b p.2 := by
  refine (summable_prod_of_nonneg fun p => mul_nonneg (ha0 p.1) (hb0 p.2)).mpr ?_
  refine ⟨fun x => hb.mul_left (a x), ?_⟩
  simp only [tsum_mul_left]
  exact ha.mul_right (∑' y, b y)

private lemma summable_gPlus : Summable gPlus := by
  have h := summable_exp_neg_mul_int_sq Real.pi_pos
  have hp := summable_prod_exp (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le) h h
  refine hp.congr fun p => ?_
  simp only [gPlus, ← Real.exp_add]
  congr 1
  ring

private lemma summable_gMinus : Summable gMinus := by
  refine (summable_gPlus.norm.congr fun p => ?_).of_norm
  simp only [gMinus, Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul]

private def repsSigmaEquiv : (Σ k : ℕ, ↥(reps k)) ≃ ℤ × ℤ where
  toFun p := p.2.1
  invFun m := ⟨(m.1 ^ 2 + m.2 ^ 2).natAbs, ⟨m, (mem_reps_iff _ m).mpr
    (Int.natAbs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))).symm⟩⟩
  left_inv := by
    rintro ⟨k, ⟨m, hm⟩⟩
    have hk : (m.1 ^ 2 + m.2 ^ 2).natAbs = k := by
      have hm' := (mem_reps_iff k m).mp hm
      zify
      rw [← hm']
      exact abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
    cases hk
    rfl
  right_inv _ := rfl

private lemma tsum_r3_eq_gPlus :
    (∑' k : ℕ, (r₃ k : ℝ) * qVal ^ k) = ∑' p : ℤ × ℤ, gPlus p := by
  rw [← repsSigmaEquiv.tsum_eq gPlus]
  have hs : Summable fun p : Σ k : ℕ, ↥(reps k) => gPlus (repsSigmaEquiv p) :=
    (repsSigmaEquiv.summable_iff).mpr summable_gPlus
  rw [hs.tsum_sigma]
  refine tsum_congr fun k => ?_
  change (r₃ k : ℝ) * qVal ^ k = ∑' m : ↥(reps k), gPlus m.1
  rw [Finset.tsum_subtype (reps k) gPlus]
  have hterm : ∑ m ∈ reps k, gPlus m = ∑ _m ∈ reps k, qVal ^ k := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := (mem_reps_iff k m).mp hm
    have hmr : (m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2 = (k : ℝ) := by exact_mod_cast hm'
    simp only [gPlus, hmr, qVal, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hterm, Finset.sum_const, nsmul_eq_mul, r₃, Int.cast_natCast]

private lemma tsum_r4_eq_gMinus :
    (∑' k : ℕ, (r₄ k : ℝ) * qVal ^ k) = ∑' p : ℤ × ℤ, gMinus p := by
  rw [← repsSigmaEquiv.tsum_eq gMinus]
  have hs : Summable fun p : Σ k : ℕ, ↥(reps k) => gMinus (repsSigmaEquiv p) :=
    (repsSigmaEquiv.summable_iff).mpr summable_gMinus
  rw [hs.tsum_sigma]
  refine tsum_congr fun k => ?_
  change (r₄ k : ℝ) * qVal ^ k = ∑' m : ↥(reps k), gMinus m.1
  rw [Finset.tsum_subtype (reps k) gMinus]
  have hterm : ∑ m ∈ reps k, gMinus m = ∑ m ∈ reps k, (-1 : ℝ) ^ (m.1 + m.2).natAbs * qVal ^ k := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := (mem_reps_iff k m).mp hm
    have hmr : (m.1 : ℝ) ^ 2 + (m.2 : ℝ) ^ 2 = (k : ℝ) := by exact_mod_cast hm'
    simp only [gMinus, gPlus, hmr, qVal, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [hterm, ← Finset.sum_mul, r₄]
  push_cast
  rfl

private def evenOddIntEquiv : ℤ ⊕ ℤ ≃ ℤ where
  toFun := Sum.elim (fun n => 2 * n) (fun n => 2 * n + 1)
  invFun m := if m % 2 = 0 then Sum.inl (m / 2) else Sum.inr ((m - 1) / 2)
  left_inv x := by
    rcases x with n | n
    · dsimp only [Sum.elim_inl]
      split_ifs
      · congr 1; omega
      · omega
    · dsimp only [Sum.elim_inr]
      split_ifs
      · omega
      · congr 1; omega
  right_inv m := by
    dsimp only
    split_ifs <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> omega

private lemma summable_thetaC : Summable fun m : ℤ => Real.exp (-Real.pi * (1 / 2) * (m : ℝ) ^ 2) := by
  have h := summable_exp_neg_mul_int_sq (mul_pos Real.pi_pos (by norm_num : (0 : ℝ) < 1 / 2))
  refine h.congr fun m => ?_
  congr 1
  ring

private lemma summable_thetaA : Summable fun n : ℤ => Real.exp (-2 * Real.pi * (n : ℝ) ^ 2) := by
  have hsum := (evenOddIntEquiv.summable_iff).mpr summable_thetaC
  refine (hsum.comp_injective Sum.inl_injective).congr fun n => ?_
  simp only [Function.comp_apply, evenOddIntEquiv, Equiv.coe_fn_mk, Sum.elim_inl, Int.cast_mul,
    Int.cast_ofNat]
  congr 1
  ring

private lemma summable_thetaB :
    Summable fun n : ℤ => Real.exp (-2 * Real.pi * ((n : ℝ) + 1 / 2) ^ 2) := by
  have hsum := (evenOddIntEquiv.summable_iff).mpr summable_thetaC
  refine (hsum.comp_injective Sum.inr_injective).congr fun n => ?_
  simp only [Function.comp_apply, evenOddIntEquiv, Equiv.coe_fn_mk, Sum.elim_inr, Int.cast_add,
    Int.cast_mul, Int.cast_ofNat, Int.cast_one]
  congr 1
  ring

private lemma thetaC_eq_add : thetaC = thetaA + thetaB := by
  have hsum := (evenOddIntEquiv.summable_iff (f := fun m : ℤ =>
    Real.exp (-Real.pi * (1 / 2) * (m : ℝ) ^ 2))).mpr summable_thetaC
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  rw [thetaC, ← evenOddIntEquiv.tsum_eq (fun m : ℤ => Real.exp (-Real.pi * (1 / 2) * (m : ℝ) ^ 2))]
  change (∑' x : ℤ ⊕ ℤ,
    ((fun m : ℤ => Real.exp (-Real.pi * (1 / 2) * (m : ℝ) ^ 2)) ∘ evenOddIntEquiv) x) =
    thetaA + thetaB
  rw [h1.tsum_sum h2, thetaA, thetaB]
  congr 1
  · refine tsum_congr fun n => ?_
    simp only [Function.comp_apply, evenOddIntEquiv, Equiv.coe_fn_mk, Sum.elim_inl, Int.cast_mul,
      Int.cast_ofNat]
    congr 1
    ring
  · refine tsum_congr fun n => ?_
    simp only [Function.comp_apply, evenOddIntEquiv, Equiv.coe_fn_mk, Sum.elim_inr, Int.cast_add,
      Int.cast_mul, Int.cast_ofNat, Int.cast_one]
    congr 1
    ring

private lemma thetaB_eq : thetaB = (√2 - 1) * thetaA := by
  have hpois := Real.tsum_exp_neg_mul_int_sq (by norm_num : (0 : ℝ) < 2)
  have hL : (∑' n : ℤ, Real.exp (-Real.pi * 2 * (n : ℝ) ^ 2)) = thetaA := by
    rw [thetaA]
    refine tsum_congr fun n => ?_
    congr 1
    ring
  have hR : (∑' n : ℤ, Real.exp (-Real.pi / 2 * (n : ℝ) ^ 2)) = thetaC := by
    rw [thetaC]
    refine tsum_congr fun n => ?_
    congr 1
    ring
  rw [hL, hR, ← Real.sqrt_eq_rpow 2, thetaC_eq_add] at hpois
  have hsq : √2 ≠ 0 := by positivity
  have hmul : √2 * thetaA = thetaA + thetaB := by
    calc
      √2 * thetaA = √2 * (1 / √2 * (thetaA + thetaB)) := by rw [← hpois]
      _ = thetaA + thetaB := by field_simp [hsq]
  linarith

private lemma thetaA_pos : 0 < thetaA := by
  have hge : Real.exp (-2 * Real.pi * ((0 : ℤ) : ℝ) ^ 2) ≤ thetaA :=
    summable_thetaA.le_tsum 0 fun j _ => (Real.exp_pos _).le
  simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Real.exp_zero] at hge
  linarith

private lemma thetaA_sq :
    thetaA ^ 2 = ∑' p : ℤ × ℤ, Real.exp (-2 * Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  have hp := summable_prod_exp (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
    summable_thetaA summable_thetaA
  have hsq : thetaA ^ 2 = ∑' p : ℤ × ℤ,
      Real.exp (-2 * Real.pi * (p.1 : ℝ) ^ 2) * Real.exp (-2 * Real.pi * (p.2 : ℝ) ^ 2) := by
    rw [sq, thetaA, hp.tsum_prod]
    simp only [tsum_mul_left, tsum_mul_right]
  rw [hsq]
  refine tsum_congr fun p => ?_
  rw [← Real.exp_add]
  congr 1
  ring

private lemma thetaB_sq :
    thetaB ^ 2 = ∑' p : ℤ × ℤ,
      Real.exp (-2 * Real.pi * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2)) := by
  have hp := summable_prod_exp (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
    summable_thetaB summable_thetaB
  have hsq : thetaB ^ 2 = ∑' p : ℤ × ℤ,
      Real.exp (-2 * Real.pi * ((p.1 : ℝ) + 1 / 2) ^ 2) *
      Real.exp (-2 * Real.pi * ((p.2 : ℝ) + 1 / 2) ^ 2) := by
    rw [sq, thetaB, hp.tsum_prod]
    simp only [tsum_mul_left, tsum_mul_right]
  rw [hsq]
  refine tsum_congr fun p => ?_
  rw [← Real.exp_add]
  congr 1
  ring

private def parityPairEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun := Sum.elim (fun p => (p.1 + p.2, p.1 - p.2)) (fun p => (p.1 + p.2 + 1, p.1 - p.2))
  invFun q := if (q.1 + q.2) % 2 = 0 then Sum.inl ((q.1 + q.2) / 2, (q.1 - q.2) / 2)
    else Sum.inr ((q.1 + q.2 - 1) / 2, (q.1 - q.2 - 1) / 2)
  left_inv x := by
    rcases x with ⟨u, v⟩ | ⟨u, v⟩
    · dsimp only [Sum.elim_inl]
      split_ifs
      · congr 1; ext <;> omega
      · omega
    · dsimp only [Sum.elim_inr]
      split_ifs
      · omega
      · congr 1; ext <;> omega
  right_inv q := by
    dsimp only
    split_ifs <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> ext <;> omega

private lemma gPlus_inl (p : ℤ × ℤ) :
    gPlus (parityPairEquiv (Sum.inl p)) =
      Real.exp (-2 * Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  simp only [parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inl, gPlus, Int.cast_add, Int.cast_sub]
  congr 1
  ring

private lemma gPlus_inr (p : ℤ × ℤ) :
    gPlus (parityPairEquiv (Sum.inr p)) =
      Real.exp (-2 * Real.pi * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2)) := by
  simp only [parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inr, gPlus, Int.cast_add, Int.cast_sub,
    Int.cast_one]
  congr 1
  ring

private lemma gMinus_inl (p : ℤ × ℤ) :
    gMinus (parityPairEquiv (Sum.inl p)) =
      Real.exp (-2 * Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  have hev : Even ((p.1 + p.2 + (p.1 - p.2)).natAbs) :=
    Int.natAbs_even.mpr ⟨p.1, by ring⟩
  change (-1 : ℝ) ^ (p.1 + p.2 + (p.1 - p.2)).natAbs * gPlus (parityPairEquiv (Sum.inl p)) = _
  rw [hev.neg_one_pow, one_mul, gPlus_inl]

private lemma gMinus_inr (p : ℤ × ℤ) :
    gMinus (parityPairEquiv (Sum.inr p)) =
      -Real.exp (-2 * Real.pi * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2)) := by
  have hodd : Odd ((p.1 + p.2 + 1 + (p.1 - p.2)).natAbs) :=
    Int.natAbs_odd.mpr ⟨p.1, by ring⟩
  change (-1 : ℝ) ^ (p.1 + p.2 + 1 + (p.1 - p.2)).natAbs * gPlus (parityPairEquiv (Sum.inr p)) = _
  rw [hodd.neg_one_pow, gPlus_inr]
  ring

private lemma tsum_gPlus_eq : (∑' p : ℤ × ℤ, gPlus p) = thetaA ^ 2 + thetaB ^ 2 := by
  have hsum := (parityPairEquiv.summable_iff (f := gPlus)).mpr summable_gPlus
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  rw [← parityPairEquiv.tsum_eq gPlus]
  change (∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ), (gPlus ∘ parityPairEquiv) x) = thetaA ^ 2 + thetaB ^ 2
  rw [h1.tsum_sum h2, thetaA_sq, thetaB_sq]
  congr 1
  · exact tsum_congr gPlus_inl
  · exact tsum_congr gPlus_inr

private lemma tsum_gMinus_eq : (∑' p : ℤ × ℤ, gMinus p) = thetaA ^ 2 - thetaB ^ 2 := by
  have hsum := (parityPairEquiv.summable_iff (f := gMinus)).mpr summable_gMinus
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  rw [← parityPairEquiv.tsum_eq gMinus]
  change (∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ), (gMinus ∘ parityPairEquiv) x) = thetaA ^ 2 - thetaB ^ 2
  rw [h1.tsum_sum h2, thetaA_sq, thetaB_sq, sub_eq_add_neg, ← tsum_neg]
  congr 1
  · exact tsum_congr gMinus_inl
  · exact tsum_congr gMinus_inr

theorem OMA.solution : type_of% @OMA.S_oeis_a002193.main := by
  have hsq2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hmain : (∑' k : ℕ, (b k : ℝ) * qVal ^ k) * (thetaA ^ 2 - thetaB ^ 2) =
      √2 * (thetaA ^ 2 - thetaB ^ 2) := by
    calc
      (∑' k : ℕ, (b k : ℝ) * qVal ^ k) * (thetaA ^ 2 - thetaB ^ 2)
          = (∑' k : ℕ, (b k : ℝ) * qVal ^ k) * (∑' k : ℕ, (r₄ k : ℝ) * qVal ^ k) := by
            rw [tsum_r4_eq_gMinus, tsum_gMinus_eq]
      _ = ∑' k : ℕ, (r₃ k : ℝ) * qVal ^ k := cauchy_b_mul_r4
      _ = thetaA ^ 2 + thetaB ^ 2 := by rw [tsum_r3_eq_gPlus, tsum_gPlus_eq]
      _ = thetaA ^ 2 + ((√2 - 1) * thetaA) ^ 2 := by rw [thetaB_eq]
      _ = (4 - 2 * √2) * thetaA ^ 2 := by
          calc
            thetaA ^ 2 + ((√2 - 1) * thetaA) ^ 2
                = (2 + √2 ^ 2 - 2 * √2) * thetaA ^ 2 := by ring
            _ = (4 - 2 * √2) * thetaA ^ 2 := by rw [hsq2]; ring
      _ = √2 * (thetaA ^ 2 - ((√2 - 1) * thetaA) ^ 2) := by
          have hsub : thetaA ^ 2 - ((√2 - 1) * thetaA) ^ 2 = (2 * √2 - 2) * thetaA ^ 2 := by
            calc
              thetaA ^ 2 - ((√2 - 1) * thetaA) ^ 2 = (2 * √2 - √2 ^ 2) * thetaA ^ 2 := by ring
              _ = (2 * √2 - 2) * thetaA ^ 2 := by rw [hsq2]
          rw [hsub]
          calc
            (4 - 2 * √2) * thetaA ^ 2 = (2 * 2 - 2 * √2) * thetaA ^ 2 := by ring
            _ = (2 * √2 ^ 2 - 2 * √2) * thetaA ^ 2 := by rw [hsq2]
            _ = √2 * (2 * √2 - 2) * thetaA ^ 2 := by ring
            _ = √2 * ((2 * √2 - 2) * thetaA ^ 2) := by ring
      _ = √2 * (thetaA ^ 2 - thetaB ^ 2) := by rw [thetaB_eq]
  have hden_pos : 0 < thetaA ^ 2 - thetaB ^ 2 := by
    rw [thetaB_eq]
    have hsqrt_gt_one : (1 : ℝ) < √2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hA_sq_pos : 0 < thetaA ^ 2 := sq_pos_of_pos thetaA_pos
    have hfac : thetaA ^ 2 - ((√2 - 1) * thetaA) ^ 2 = (2 * (√2 - 1)) * thetaA ^ 2 := by
      calc
        thetaA ^ 2 - ((√2 - 1) * thetaA) ^ 2 = (2 * √2 - √2 ^ 2) * thetaA ^ 2 := by ring
        _ = (2 * √2 - 2) * thetaA ^ 2 := by rw [hsq2]
        _ = (2 * (√2 - 1)) * thetaA ^ 2 := by ring
    rw [hfac]
    exact mul_pos (by linarith) hA_sq_pos
  have hsum_q : (∑' k : ℕ, (b k : ℝ) * qVal ^ k) = √2 :=
    mul_right_cancel₀ hden_pos.ne' hmain
  rw [← hsum_q]
  refine tsum_congr fun k => ?_
  rw [qVal, Real.exp_neg, inv_pow, div_eq_mul_inv, Real.exp_nat_mul]
