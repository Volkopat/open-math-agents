import OMAStatements.S_oeis_a014549

-- Original Lean proof: @treybeathard-jpg.

open OMA.S_oeis_a014549 Filter Topology Real

private noncomputable def q0 : ℝ := Real.exp (-Real.pi)

private noncomputable def theta3 (q : ℝ) : ℝ :=
  ∑' m : ℤ, q ^ (m.natAbs ^ 2)

private noncomputable def theta4 (q : ℝ) : ℝ :=
  ∑' m : ℤ, (-1 : ℝ) ^ m.natAbs * q ^ (m.natAbs ^ 2)

private noncomputable def thetaA : ℝ :=
  ∑' n : ℤ, Real.exp (-2 * Real.pi * (n : ℝ) ^ 2)

private noncomputable def thetaB : ℝ :=
  ∑' n : ℤ, Real.exp (-2 * Real.pi * ((n : ℝ) + 1 / 2) ^ 2)

private noncomputable def thetaC : ℝ :=
  ∑' m : ℤ, Real.exp (-Real.pi * (1 / 2) * (m : ℝ) ^ 2)

private noncomputable def reps (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(k : ℤ)) k ×ˢ Finset.Icc (-(k : ℤ)) k).filter
    fun m => m.1 ^ 2 + m.2 ^ 2 = (k : ℤ)

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

private lemma summable_theta3 {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun m : ℤ => q ^ (m.natAbs ^ 2) := by
  have hnat : Summable fun m : ℕ => q ^ (m ^ 2) := by
    refine Summable.of_nonneg_of_le (fun _ => pow_nonneg hq0 _) (fun m => ?_)
      (summable_geometric_of_lt_one hq0 hq1)
    exact pow_le_pow_of_le_one hq0 hq1.le (by nlinarith)
  have hneg : Summable fun m : ℕ => q ^ ((-m : ℤ).natAbs ^ 2) := by
    simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hnat
  exact summable_int_iff_summable_nat_and_neg.mpr
    ⟨by simpa only [Int.natAbs_natCast] using hnat, hneg⟩

private lemma summable_norm_theta3 {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun m : ℤ => ‖q ^ (m.natAbs ^ 2)‖ :=
  (summable_theta3 hq0 hq1).norm

private lemma summable_norm_theta4 {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun m : ℤ => ‖(-1 : ℝ) ^ m.natAbs * q ^ (m.natAbs ^ 2)‖ := by
  refine (summable_theta3 hq0 hq1).norm.congr fun m => ?_
  simp only [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul]

private lemma summable_theta4 {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun m : ℤ => (-1 : ℝ) ^ m.natAbs * q ^ (m.natAbs ^ 2) :=
  (summable_norm_theta4 hq0 hq1).of_norm

private lemma summable_succ_sq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n : ℕ => q ^ ((n + 1) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun _ => pow_nonneg hq0 _) (fun n => ?_)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left q)
  calc
    q ^ ((n + 1) ^ 2) ≤ q ^ (n + 1) := pow_le_pow_of_le_one hq0 hq1.le (by nlinarith)
    _ = q * q ^ n := pow_succ' q n

private lemma tsum_succ_sq_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n : ℕ, q ^ ((n + 1) ^ 2)) ≤ q / (1 - q) := by
  have hgeom : Summable fun n : ℕ => q * q ^ n :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left q
  have hle : ∀ n : ℕ, q ^ ((n + 1) ^ 2) ≤ q * q ^ n := fun n => by
    calc
      q ^ ((n + 1) ^ 2) ≤ q ^ (n + 1) := pow_le_pow_of_le_one hq0 hq1.le (by nlinarith)
      _ = q * q ^ n := pow_succ' q n
  calc
    (∑' n : ℕ, q ^ ((n + 1) ^ 2)) ≤ ∑' n : ℕ, q * q ^ n :=
      (summable_succ_sq hq0 hq1).tsum_le_tsum hle hgeom
    _ = q * ∑' n : ℕ, q ^ n := tsum_mul_left
    _ = q * (1 - q)⁻¹ := by rw [tsum_geometric_of_lt_one hq0 hq1]
    _ = q / (1 - q) := (div_eq_mul_inv q (1 - q)).symm

private lemma theta3_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    1 ≤ theta3 q ∧ theta3 q ≤ 1 + 2 * (q / (1 - q)) := by
  have heven : Function.Even (fun m : ℤ => q ^ (m.natAbs ^ 2)) :=
    fun m => by simp only [Int.natAbs_neg]
  have hsplit := tsum_int_eq_zero_add_two_mul_tsum_pnat heven (summable_theta3 hq0 hq1)
  have h0 : q ^ ((0 : ℤ).natAbs ^ 2) = 1 := by simp
  have hpnat : (∑' n : ℕ+, q ^ ((↑(n : ℕ) : ℤ).natAbs ^ 2)) = ∑' n : ℕ, q ^ ((n + 1) ^ 2) := by
    have hcongr : (∑' n : ℕ+, q ^ ((↑(n : ℕ) : ℤ).natAbs ^ 2)) = ∑' n : ℕ+, q ^ ((n : ℕ) ^ 2) :=
      tsum_congr fun n => by simp only [Int.natAbs_natCast]
    rw [hcongr, tsum_pnat_eq_tsum_succ (f := fun n : ℕ => q ^ (n ^ 2))]
  have htheta : theta3 q = 1 + 2 * ∑' n : ℕ, q ^ ((n + 1) ^ 2) := by
    rw [theta3, hsplit, h0, hpnat, nsmul_eq_mul]
    norm_num
  rw [htheta]
  have hnonneg : 0 ≤ ∑' n : ℕ, q ^ ((n + 1) ^ 2) := tsum_nonneg fun _ => pow_nonneg hq0 _
  have hle := tsum_succ_sq_le hq0 hq1
  constructor <;> linarith

private lemma theta3_pos {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 < theta3 q := by
  linarith [(theta3_bounds hq0 hq1).1]

private lemma theta4_pos {q : ℝ} (hq0 : 0 ≤ q) (hq3 : q < 1 / 3) : 0 < theta4 q := by
  have hq1 : q < 1 := by linarith
  have heven : Function.Even (fun m : ℤ => (-1 : ℝ) ^ m.natAbs * q ^ (m.natAbs ^ 2)) :=
    fun m => by simp only [Int.natAbs_neg]
  have hsplit := tsum_int_eq_zero_add_two_mul_tsum_pnat heven (summable_theta4 hq0 hq1)
  have h0 : (-1 : ℝ) ^ (0 : ℤ).natAbs * q ^ ((0 : ℤ).natAbs ^ 2) = 1 := by simp
  have hpnat : (∑' n : ℕ+, (-1 : ℝ) ^ (↑(n : ℕ) : ℤ).natAbs * q ^ ((↑(n : ℕ) : ℤ).natAbs ^ 2)) =
      ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2) := by
    have hcongr : (∑' n : ℕ+, (-1 : ℝ) ^ (↑(n : ℕ) : ℤ).natAbs * q ^ ((↑(n : ℕ) : ℤ).natAbs ^ 2)) =
        ∑' n : ℕ+, (-1 : ℝ) ^ (n : ℕ) * q ^ ((n : ℕ) ^ 2) :=
      tsum_congr fun n => by simp only [Int.natAbs_natCast]
    rw [hcongr, tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (-1 : ℝ) ^ n * q ^ (n ^ 2))]
  have htheta : theta4 q = 1 + 2 * ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2) := by
    rw [theta4, hsplit, h0, hpnat, nsmul_eq_mul]
    norm_num
  have hsum_alt : Summable fun n : ℕ => (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2) := by
    refine ((summable_succ_sq hq0 hq1).norm.congr fun n => ?_).of_norm
    simp only [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul]
  have hge_term : ∀ n : ℕ, -(q ^ ((n + 1) ^ 2)) ≤ (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2) := by
    intro n
    have hsign : (-1 : ℝ) ≤ (-1 : ℝ) ^ (n + 1) := by
      rcases Nat.even_or_odd (n + 1) with h | h
      · rw [h.neg_one_pow]; norm_num
      · rw [h.neg_one_pow]
    have hnn : 0 ≤ q ^ ((n + 1) ^ 2) := pow_nonneg hq0 _
    nlinarith
  have htail : -(q / (1 - q)) ≤ ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2) := by
    calc
      -(q / (1 - q)) ≤ -(∑' n : ℕ, q ^ ((n + 1) ^ 2)) := neg_le_neg (tsum_succ_sq_le hq0 hq1)
      _ = ∑' n : ℕ, -(q ^ ((n + 1) ^ 2)) := tsum_neg.symm
      _ ≤ ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2) :=
          (summable_succ_sq hq0 hq1).neg.tsum_le_tsum hge_term hsum_alt
  have hfrac : 2 * (q / (1 - q)) < 1 := by
    rw [← mul_div_assoc, div_lt_one (by linarith)]
    linarith
  linarith

private lemma neg_one_pow_add_natAbs (x y : ℤ) :
    (-1 : ℝ) ^ x.natAbs * (-1 : ℝ) ^ y.natAbs = (-1 : ℝ) ^ (x + y).natAbs := by
  have h (z : ℤ) : (-1 : ℝ) ^ z = (-1 : ℝ) ^ z.natAbs := by
    simp only [neg_one_zpow_eq_ite, neg_one_pow_eq_ite, Int.natAbs_even]
  simp only [← h, zpow_add₀ (neg_ne_zero.mpr (one_ne_zero : (1 : ℝ) ≠ 0))]

private lemma natAbs_sq_add_sub (u v : ℤ) :
    (u + v).natAbs ^ 2 + (u - v).natAbs ^ 2 = 2 * (u.natAbs ^ 2 + v.natAbs ^ 2) := by
  zify
  simp only [sq_abs]
  ring

private lemma summable_prod_of_nonneg_mul {a b : ℤ → ℝ}
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ y, 0 ≤ b y)
    (ha : Summable a) (hb : Summable b) :
    Summable fun p : ℤ × ℤ => a p.1 * b p.2 := by
  refine (summable_prod_of_nonneg fun p => mul_nonneg (ha0 p.1) (hb0 p.2)).mpr ?_
  refine ⟨fun x => hb.mul_left (a x), ?_⟩
  simp only [tsum_mul_left]
  exact ha.mul_right (∑' y, b y)

private lemma summable_q_pair {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun p : ℤ × ℤ => q ^ (p.1.natAbs ^ 2 + p.2.natAbs ^ 2) := by
  have hp := summable_prod_of_nonneg_mul (fun _ => pow_nonneg hq0 _) (fun _ => pow_nonneg hq0 _)
    (summable_theta3 hq0 hq1) (summable_theta3 hq0 hq1)
  refine hp.congr fun p => ?_
  rw [pow_add]

private lemma summable_q_pair_signed {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun p : ℤ × ℤ => (-1 : ℝ) ^ (p.1 + p.2).natAbs * q ^ (p.1.natAbs ^ 2 + p.2.natAbs ^ 2) := by
  refine ((summable_q_pair hq0 hq1).norm.congr fun p => ?_).of_norm
  simp only [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul]

private lemma summable_q_pair_half {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun p : ℤ × ℤ => (-1 : ℝ) ^ p.2.natAbs * q ^ (p.1.natAbs ^ 2 + p.2.natAbs ^ 2) := by
  refine ((summable_q_pair hq0 hq1).norm.congr fun p => ?_).of_norm
  simp only [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul]

private lemma theta3_sq_eq_prod {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (theta3 q) ^ 2 = ∑' p : ℤ × ℤ, q ^ (p.1.natAbs ^ 2 + p.2.natAbs ^ 2) := by
  rw [sq, theta3, tsum_mul_tsum_of_summable_norm (summable_norm_theta3 hq0 hq1)
    (summable_norm_theta3 hq0 hq1)]
  refine tsum_congr fun p => ?_
  rw [← pow_add]

private lemma theta4_sq_eq_prod {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (theta4 q) ^ 2 = ∑' p : ℤ × ℤ,
      (-1 : ℝ) ^ (p.1 + p.2).natAbs * q ^ (p.1.natAbs ^ 2 + p.2.natAbs ^ 2) := by
  rw [sq, theta4, tsum_mul_tsum_of_summable_norm (summable_norm_theta4 hq0 hq1)
    (summable_norm_theta4 hq0 hq1)]
  refine tsum_congr fun p => ?_
  calc
    (-1 : ℝ) ^ p.1.natAbs * q ^ (p.1.natAbs ^ 2) * ((-1 : ℝ) ^ p.2.natAbs * q ^ (p.2.natAbs ^ 2))
        = ((-1 : ℝ) ^ p.1.natAbs * (-1 : ℝ) ^ p.2.natAbs) *
          (q ^ (p.1.natAbs ^ 2) * q ^ (p.2.natAbs ^ 2)) := by ring
    _ = (-1 : ℝ) ^ (p.1 + p.2).natAbs * q ^ (p.1.natAbs ^ 2 + p.2.natAbs ^ 2) := by
          rw [neg_one_pow_add_natAbs, ← pow_add]

private lemma theta3_mul_theta4_eq_prod {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    theta3 q * theta4 q = ∑' p : ℤ × ℤ,
      (-1 : ℝ) ^ p.2.natAbs * q ^ (p.1.natAbs ^ 2 + p.2.natAbs ^ 2) := by
  rw [theta3, theta4, tsum_mul_tsum_of_summable_norm (summable_norm_theta3 hq0 hq1)
    (summable_norm_theta4 hq0 hq1)]
  refine tsum_congr fun p => ?_
  calc
    q ^ (p.1.natAbs ^ 2) * ((-1 : ℝ) ^ p.2.natAbs * q ^ (p.2.natAbs ^ 2))
        = (-1 : ℝ) ^ p.2.natAbs * (q ^ (p.1.natAbs ^ 2) * q ^ (p.2.natAbs ^ 2)) := by ring
    _ = (-1 : ℝ) ^ p.2.natAbs * q ^ (p.1.natAbs ^ 2 + p.2.natAbs ^ 2) := by rw [← pow_add]

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

private def swapOddEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1, -p.2 - 1)
  invFun p := (p.1, -p.2 - 1)
  left_inv p := by
    ext
    · rfl
    · dsimp only; omega
  right_inv p := by
    ext
    · rfl
    · dsimp only; omega

private lemma agm_step_arith {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ((theta3 q) ^ 2 + (theta4 q) ^ 2) / 2 = (theta3 (q ^ 2)) ^ 2 := by
  have hq2_0 : 0 ≤ q ^ 2 := sq_nonneg q
  have hq2_1 : q ^ 2 < 1 := by nlinarith
  let F : ℤ × ℤ → ℝ := fun p => q ^ (p.1.natAbs ^ 2 + p.2.natAbs ^ 2)
  let G : ℤ × ℤ → ℝ := fun p => (-1 : ℝ) ^ (p.1 + p.2).natAbs * F p
  have hFsum := (parityPairEquiv.summable_iff (f := F)).mpr (summable_q_pair hq0 hq1)
  have hF1 := hFsum.comp_injective Sum.inl_injective
  have hF2 := hFsum.comp_injective Sum.inr_injective
  have hGsum := (parityPairEquiv.summable_iff (f := G)).mpr (summable_q_pair_signed hq0 hq1)
  have hG1 := hGsum.comp_injective Sum.inl_injective
  have hG2 := hGsum.comp_injective Sum.inr_injective
  have h3split : (theta3 q) ^ 2 =
      (theta3 (q ^ 2)) ^ 2 + ∑' p : ℤ × ℤ, F (parityPairEquiv (Sum.inr p)) := by
    rw [theta3_sq_eq_prod hq0 hq1]
    change (∑' p : ℤ × ℤ, F p) = _
    rw [← parityPairEquiv.tsum_eq F]
    change (∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ), (F ∘ parityPairEquiv) x) = _
    rw [hF1.tsum_sum hF2, theta3_sq_eq_prod hq2_0 hq2_1]
    congr 1
    refine tsum_congr fun p => ?_
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inl, F,
      natAbs_sq_add_sub, pow_mul]
  have h4split : (theta4 q) ^ 2 =
      (theta3 (q ^ 2)) ^ 2 - ∑' p : ℤ × ℤ, F (parityPairEquiv (Sum.inr p)) := by
    rw [theta4_sq_eq_prod hq0 hq1]
    change (∑' p : ℤ × ℤ, G p) = _
    rw [← parityPairEquiv.tsum_eq G]
    change (∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ), (G ∘ parityPairEquiv) x) = _
    rw [hG1.tsum_sum hG2, theta3_sq_eq_prod hq2_0 hq2_1, sub_eq_add_neg, ← tsum_neg]
    congr 1
    · refine tsum_congr fun p => ?_
      have hev : Even ((p.1 + p.2 + (p.1 - p.2)).natAbs) := Int.natAbs_even.mpr ⟨p.1, by ring⟩
      simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inl, G, F]
      rw [hev.neg_one_pow, one_mul, natAbs_sq_add_sub, pow_mul]
    · refine tsum_congr fun p => ?_
      have hodd : Odd ((p.1 + p.2 + 1 + (p.1 - p.2)).natAbs) := Int.natAbs_odd.mpr ⟨p.1, by ring⟩
      simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inr, G, F]
      rw [hodd.neg_one_pow]
      ring
  linarith

private lemma agm_step_geom {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    theta3 q * theta4 q = (theta4 (q ^ 2)) ^ 2 := by
  have hq2_0 : 0 ≤ q ^ 2 := sq_nonneg q
  have hq2_1 : q ^ 2 < 1 := by nlinarith
  let H : ℤ × ℤ → ℝ := fun p =>
    (-1 : ℝ) ^ p.2.natAbs * q ^ (p.1.natAbs ^ 2 + p.2.natAbs ^ 2)
  have hHsum := (parityPairEquiv.summable_iff (f := H)).mpr (summable_q_pair_half hq0 hq1)
  have hH1 := hHsum.comp_injective Sum.inl_injective
  have hH2 := hHsum.comp_injective Sum.inr_injective
  have hsplit : theta3 q * theta4 q =
      (theta4 (q ^ 2)) ^ 2 + ∑' p : ℤ × ℤ, H (parityPairEquiv (Sum.inr p)) := by
    rw [theta3_mul_theta4_eq_prod hq0 hq1]
    change (∑' p : ℤ × ℤ, H p) = _
    rw [← parityPairEquiv.tsum_eq H]
    change (∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ), (H ∘ parityPairEquiv) x) = _
    rw [hH1.tsum_sum hH2, theta4_sq_eq_prod hq2_0 hq2_1]
    congr 1
    refine tsum_congr fun p => ?_
    have hsign : (-1 : ℝ) ^ (p.1 - p.2).natAbs = (-1 : ℝ) ^ (p.1 + p.2).natAbs := by
      have h1 : p.1 - p.2 = p.1 + (-p.2) := by ring
      rw [h1, ← neg_one_pow_add_natAbs, Int.natAbs_neg, neg_one_pow_add_natAbs]
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inl, H]
    rw [hsign, natAbs_sq_add_sub, pow_mul]
  have hodd_zero : (∑' p : ℤ × ℤ, H (parityPairEquiv (Sum.inr p))) = 0 := by
    let T : ℝ := ∑' p : ℤ × ℤ, H (parityPairEquiv (Sum.inr p))
    have hneg : T = -T := by
      calc
        T = ∑' p : ℤ × ℤ, H (parityPairEquiv (Sum.inr (swapOddEquiv p))) :=
            (swapOddEquiv.tsum_eq (fun p => H (parityPairEquiv (Sum.inr p)))).symm
        _ = ∑' p : ℤ × ℤ, -(H (parityPairEquiv (Sum.inr p))) := by
            refine tsum_congr fun p => ?_
            have h1 : p.1 + (-p.2 - 1) + 1 = p.1 - p.2 := by ring
            have h2 : p.1 - (-p.2 - 1) = p.1 + p.2 + 1 := by ring
            have hpar : (-1 : ℝ) ^ (p.1 + p.2 + 1).natAbs = -((-1 : ℝ) ^ (p.1 - p.2).natAbs) := by
              have heq : p.1 + p.2 + 1 = (p.1 - p.2) + (2 * p.2 + 1) := by ring
              have hodd : Odd ((2 * p.2 + 1).natAbs) := Int.natAbs_odd.mpr ⟨p.2, rfl⟩
              rw [heq, ← neg_one_pow_add_natAbs, hodd.neg_one_pow]
              ring
            simp only [parityPairEquiv, swapOddEquiv, Equiv.coe_fn_mk, Sum.elim_inr, H]
            rw [h1, h2, hpar, add_comm ((p.1 - p.2).natAbs ^ 2)]
            ring
        _ = -T := tsum_neg
    linarith
  linarith

private lemma q0_pos : 0 < q0 := Real.exp_pos _

private lemma q0_lt_third : q0 < 1 / 3 := by
  have hexp3 : (3 : ℝ) < Real.exp Real.pi := by
    calc
      (3 : ℝ) < (2 : ℝ) ^ 3 := by norm_num
      _ < (Real.exp 1) ^ 3 := by gcongr; exact Real.exp_one_gt_two
      _ = Real.exp ((3 : ℕ) : ℝ) := Real.exp_one_pow 3
      _ = Real.exp 3 := by norm_num
      _ < Real.exp Real.pi := Real.exp_lt_exp.mpr Real.pi_gt_three
  have hpos : 0 < Real.exp Real.pi := Real.exp_pos _
  rw [q0, Real.exp_neg, one_div]
  exact inv_strictAnti₀ (by norm_num) hexp3

private lemma q0_lt_one : q0 < 1 := by linarith [q0_lt_third]

private lemma exp_pow_natAbs_sq (c : ℝ) (m : ℤ) :
    Real.exp c ^ (m.natAbs ^ 2) = Real.exp (c * (m : ℝ) ^ 2) := by
  rw [← Real.exp_nat_mul]
  have h : ((m.natAbs ^ 2 : ℕ) : ℤ) = m ^ 2 := by
    rw [Nat.cast_pow, Int.natAbs_sq]
  rw [← Int.cast_natCast, h, Int.cast_pow, mul_comm]

private lemma q0_pow_natAbs_sq (m : ℤ) :
    q0 ^ (m.natAbs ^ 2) = Real.exp (-Real.pi * (m : ℝ) ^ 2) :=
  exp_pow_natAbs_sq _ m

private lemma summable_exp_neg_mul_int_sq {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2) :=
  (summable_theta3 (Real.exp_pos (-c)).le
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc))).congr (exp_pow_natAbs_sq (-c))

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
  let f (m : ℤ) := Real.exp (-Real.pi * (1 / 2) * (m : ℝ) ^ 2)
  let e := evenOddIntEquiv
  have hs : Summable (f ∘ e) := (e.summable_iff (f := f)).2 summable_thetaC
  have heven : (∑' n : ℤ, f (e (Sum.inl n))) = thetaA := by
    unfold thetaA
    refine tsum_congr fun n => congrArg Real.exp ?_
    change -Real.pi * (1 / 2) * ((2 * n : ℤ) : ℝ) ^ 2 = -2 * Real.pi * (n : ℝ) ^ 2
    push_cast
    ring
  have hodd : (∑' n : ℤ, f (e (Sum.inr n))) = thetaB := by
    unfold thetaB
    refine tsum_congr fun n => congrArg Real.exp ?_
    change -Real.pi * (1 / 2) * ((2 * n + 1 : ℤ) : ℝ) ^ 2 =
      -2 * Real.pi * ((n : ℝ) + 1 / 2) ^ 2
    push_cast
    ring
  change (∑' m : ℤ, f m) = thetaA + thetaB
  calc
    _ = ∑' t : ℤ ⊕ ℤ, (f ∘ e) t := (e.tsum_eq f).symm
    _ = (∑' n : ℤ, f (e (Sum.inl n))) + ∑' n : ℤ, f (e (Sum.inr n)) :=
      (hs.comp_injective Sum.inl_injective).tsum_sum (hs.comp_injective Sum.inr_injective)
    _ = _ := congrArg₂ (· + ·) heven hodd

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

private lemma thetaA_sq :
    thetaA ^ 2 = ∑' p : ℤ × ℤ, Real.exp (-2 * Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  have hp := summable_prod_of_nonneg_mul (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le) summable_thetaA summable_thetaA
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
  have hp := summable_prod_of_nonneg_mul (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le) summable_thetaB summable_thetaB
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

private lemma theta3_q0_sq_eq_AB : (theta3 q0) ^ 2 = thetaA ^ 2 + thetaB ^ 2 := by
  let F : ℤ × ℤ → ℝ := fun p => q0 ^ (p.1.natAbs ^ 2 + p.2.natAbs ^ 2)
  have hsum := (parityPairEquiv.summable_iff (f := F)).mpr (summable_q_pair q0_pos.le q0_lt_one)
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  rw [theta3_sq_eq_prod q0_pos.le q0_lt_one]
  change (∑' p : ℤ × ℤ, F p) = _
  rw [← parityPairEquiv.tsum_eq F]
  change (∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ), (F ∘ parityPairEquiv) x) = _
  rw [h1.tsum_sum h2, thetaA_sq, thetaB_sq]
  congr 1
  · refine tsum_congr fun p => ?_
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inl, F,
      pow_add, q0_pow_natAbs_sq, ← Real.exp_add, Int.cast_add, Int.cast_sub]
    congr 1
    ring
  · refine tsum_congr fun p => ?_
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inr, F,
      pow_add, q0_pow_natAbs_sq, ← Real.exp_add, Int.cast_add, Int.cast_sub, Int.cast_one]
    congr 1
    ring

private lemma theta4_q0_sq_eq_AB : (theta4 q0) ^ 2 = thetaA ^ 2 - thetaB ^ 2 := by
  let G : ℤ × ℤ → ℝ := fun p =>
    (-1 : ℝ) ^ (p.1 + p.2).natAbs * q0 ^ (p.1.natAbs ^ 2 + p.2.natAbs ^ 2)
  have hsum := (parityPairEquiv.summable_iff (f := G)).mpr
    (summable_q_pair_signed q0_pos.le q0_lt_one)
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  rw [theta4_sq_eq_prod q0_pos.le q0_lt_one]
  change (∑' p : ℤ × ℤ, G p) = _
  rw [← parityPairEquiv.tsum_eq G]
  change (∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ), (G ∘ parityPairEquiv) x) = _
  rw [h1.tsum_sum h2, thetaA_sq, thetaB_sq, sub_eq_add_neg, ← tsum_neg]
  congr 1
  · refine tsum_congr fun p => ?_
    have hev : Even ((p.1 + p.2 + (p.1 - p.2)).natAbs) := Int.natAbs_even.mpr ⟨p.1, by ring⟩
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inl, G]
    rw [hev.neg_one_pow, one_mul, pow_add, q0_pow_natAbs_sq, q0_pow_natAbs_sq, ← Real.exp_add]
    congr 1
    push_cast
    ring
  · refine tsum_congr fun p => ?_
    have hodd : Odd ((p.1 + p.2 + 1 + (p.1 - p.2)).natAbs) := Int.natAbs_odd.mpr ⟨p.1, by ring⟩
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inr, G]
    rw [hodd.neg_one_pow, pow_add, q0_pow_natAbs_sq, q0_pow_natAbs_sq, ← Real.exp_add]
    have hexp : -Real.pi * ((p.1 + p.2 + 1 : ℤ) : ℝ) ^ 2 + -Real.pi * ((p.1 - p.2 : ℤ) : ℝ) ^ 2 =
        -2 * Real.pi * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2) := by
      push_cast
      ring
    rw [hexp]
    ring

private lemma theta3_q0_sq_eq_sqrt2 : (theta3 q0) ^ 2 = √2 * (theta4 q0) ^ 2 := by
  have h : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [theta3_q0_sq_eq_AB, theta4_q0_sq_eq_AB, thetaB_eq]
  linear_combination ((√2 - 1) * thetaA ^ 2) * h

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

private lemma tsum_A104794_eq_theta4_sq :
    (∑' k : ℕ, (A104794 k : ℝ) / Real.exp (k * Real.pi)) = (theta4 q0) ^ 2 := by
  let G : ℤ × ℤ → ℝ := fun p =>
    (-1 : ℝ) ^ (p.1 + p.2).natAbs * q0 ^ (p.1.natAbs ^ 2 + p.2.natAbs ^ 2)
  have hs : Summable fun p : Σ k : ℕ, ↥(reps k) => G (repsSigmaEquiv p) :=
    (repsSigmaEquiv.summable_iff (f := G)).mpr (summable_q_pair_signed q0_pos.le q0_lt_one)
  rw [theta4_sq_eq_prod q0_pos.le q0_lt_one]
  change _ = ∑' p : ℤ × ℤ, G p
  rw [← repsSigmaEquiv.tsum_eq G, hs.tsum_sigma]
  refine tsum_congr fun k => ?_
  change (A104794 k : ℝ) / Real.exp (k * Real.pi) = ∑' m : ↥(reps k), G m.1
  rw [Finset.tsum_subtype (reps k) G]
  have hterm : ∑ m ∈ reps k, G m = ∑ m ∈ reps k, (-1 : ℝ) ^ (m.1 + m.2).natAbs * q0 ^ k := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := (mem_reps_iff k m).mp hm
    have hnat : m.1.natAbs ^ 2 + m.2.natAbs ^ 2 = k := by
      zify
      simp only [sq_abs]
      exact hm'
    simp only [G, hnat]
  have hdiv : (A104794 k : ℝ) / Real.exp (k * Real.pi) = (A104794 k : ℝ) * q0 ^ k := by
    rw [q0, Real.exp_neg, inv_pow, div_eq_mul_inv, Real.exp_nat_mul]
  rw [hterm, ← Finset.sum_mul, hdiv]
  have hA : (A104794 k : ℝ) = ∑ m ∈ reps k, (-1 : ℝ) ^ (m.1 + m.2).natAbs := by
    change ((∑ m ∈ reps k, (-1 : ℤ) ^ (m.1 + m.2).natAbs : ℤ) : ℝ) = _
    push_cast
    rfl
  rw [hA]

private lemma q0_pow_two_pow_lt_third (n : ℕ) : q0 ^ (2 ^ n) < 1 / 3 := by
  have hge : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hle : q0 ^ (2 ^ n) ≤ q0 ^ 1 := pow_le_pow_of_le_one q0_pos.le q0_lt_one.le hge
  rw [pow_one] at hle
  exact hle.trans_lt q0_lt_third

private lemma agmSeq_succ (k : ℕ) :
    agmSeq (k + 1) =
      ((theta3 (q0 ^ (2 ^ (k + 1)))) ^ 2 / (theta4 q0) ^ 2,
       (theta4 (q0 ^ (2 ^ (k + 1)))) ^ 2 / (theta4 q0) ^ 2) := by
  have h4pos : 0 < theta4 q0 := theta4_pos q0_pos.le q0_lt_third
  have h4sq_pos : 0 < (theta4 q0) ^ 2 := sq_pos_of_pos h4pos
  have h4sq_ne : (theta4 q0) ^ 2 ≠ 0 := h4sq_pos.ne'
  induction k with
  | zero =>
    have hq2 : q0 ^ (2 ^ 1) = q0 ^ 2 := by norm_num
    rw [agmSeq, agmSeq, hq2]
    have h1 : (1 : ℝ) = (theta4 q0) ^ 2 / (theta4 q0) ^ 2 := (div_self h4sq_ne).symm
    have h2 : √2 = (theta3 q0) ^ 2 / (theta4 q0) ^ 2 := by
      rw [theta3_q0_sq_eq_sqrt2, mul_div_cancel_right₀ _ h4sq_ne]
    ext
    · dsimp only
      rw [h1, h2]
      calc
        ((theta4 q0) ^ 2 / (theta4 q0) ^ 2 + (theta3 q0) ^ 2 / (theta4 q0) ^ 2) / 2
            = (((theta3 q0) ^ 2 + (theta4 q0) ^ 2) / 2) / (theta4 q0) ^ 2 := by ring
        _ = (theta3 (q0 ^ 2)) ^ 2 / (theta4 q0) ^ 2 := by
            rw [agm_step_arith q0_pos.le q0_lt_one]
    · dsimp only
      rw [h1, h2]
      have hmul : (theta4 q0) ^ 2 / (theta4 q0) ^ 2 * ((theta3 q0) ^ 2 / (theta4 q0) ^ 2) =
          (theta3 q0 * theta4 q0 / (theta4 q0) ^ 2) ^ 2 := by ring
      have hnn : 0 ≤ theta3 q0 * theta4 q0 / (theta4 q0) ^ 2 :=
        div_nonneg (mul_nonneg (theta3_pos q0_pos.le q0_lt_one).le h4pos.le) h4sq_pos.le
      rw [hmul, Real.sqrt_sq hnn, agm_step_geom q0_pos.le q0_lt_one]
  | succ k ih =>
    let r : ℝ := q0 ^ (2 ^ (k + 1))
    have hr0 : 0 ≤ r := pow_nonneg q0_pos.le _
    have hr3 : r < 1 / 3 := q0_pow_two_pow_lt_third (k + 1)
    have hr1 : r < 1 := by linarith
    have hr_sq : r ^ 2 = q0 ^ (2 ^ (k + 2)) := by
      dsimp only [r]
      rw [← pow_mul]
      rfl
    rw [agmSeq, ih]
    ext
    · dsimp only
      rw [← hr_sq]
      calc
        ((theta3 r) ^ 2 / (theta4 q0) ^ 2 + (theta4 r) ^ 2 / (theta4 q0) ^ 2) / 2
            = (((theta3 r) ^ 2 + (theta4 r) ^ 2) / 2) / (theta4 q0) ^ 2 := by ring
        _ = (theta3 (r ^ 2)) ^ 2 / (theta4 q0) ^ 2 := by rw [agm_step_arith hr0 hr1]
    · dsimp only
      rw [← hr_sq]
      have hmul : (theta3 r) ^ 2 / (theta4 q0) ^ 2 * ((theta4 r) ^ 2 / (theta4 q0) ^ 2) =
          (theta3 r * theta4 r / (theta4 q0) ^ 2) ^ 2 := by ring
      have hnn : 0 ≤ theta3 r * theta4 r / (theta4 q0) ^ 2 :=
        div_nonneg (mul_nonneg (theta3_pos hr0 hr1).le (theta4_pos hr0 hr3).le) h4sq_pos.le
      rw [hmul, Real.sqrt_sq hnn, agm_step_geom hr0 hr1]

theorem OMA.solution : type_of% @OMA.S_oeis_a014549.main := by
  rw [tsum_A104794_eq_theta4_sq, ← Filter.tendsto_add_atTop_iff_nat 1]
  have hfun : (fun k : ℕ => (agmSeq (k + 1)).1) =
      fun k : ℕ => (theta3 (q0 ^ (2 ^ (k + 1)))) ^ 2 / (theta4 q0) ^ 2 := by
    ext k
    rw [agmSeq_succ k]
  rw [hfun]
  have hq_tendsto : Tendsto (fun k : ℕ => q0 ^ (2 ^ (k + 1))) atTop (𝓝 0) := by
    have hpow : Tendsto (fun k : ℕ => q0 ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one q0_pos.le q0_lt_one
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow
      (fun k => pow_nonneg q0_pos.le _) (fun k => ?_)
    have hle : k ≤ 2 ^ (k + 1) := by
      have hk : k < 2 ^ k := Nat.lt_two_pow_self
      have h2 : 2 ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact pow_le_pow_of_le_one q0_pos.le q0_lt_one.le hle
  have hupper : Tendsto (fun k : ℕ => 1 + 2 * (q0 ^ (2 ^ (k + 1)) / (1 - q0 ^ (2 ^ (k + 1)))))
      atTop (𝓝 1) := by
    have hden : Tendsto (fun k : ℕ => 1 - q0 ^ (2 ^ (k + 1))) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hq_tendsto
    have hdiv : Tendsto (fun k : ℕ => q0 ^ (2 ^ (k + 1)) / (1 - q0 ^ (2 ^ (k + 1))))
        atTop (𝓝 (0 / (1 - 0))) := hq_tendsto.div hden (by norm_num)
    have hmul : Tendsto (fun k : ℕ => 1 + 2 * (q0 ^ (2 ^ (k + 1)) / (1 - q0 ^ (2 ^ (k + 1)))))
        atTop (𝓝 (1 + 2 * (0 / (1 - 0)))) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul hdiv)
    simpa only [sub_zero, zero_div, mul_zero, add_zero] using hmul
  have htheta3_tendsto : Tendsto (fun k : ℕ => theta3 (q0 ^ (2 ^ (k + 1)))) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper ?_ ?_
    · intro k
      have hr0 : 0 ≤ q0 ^ (2 ^ (k + 1)) := pow_nonneg q0_pos.le _
      have hr1 : q0 ^ (2 ^ (k + 1)) < 1 := by linarith [q0_pow_two_pow_lt_third (k + 1)]
      exact (theta3_bounds hr0 hr1).1
    · intro k
      have hr0 : 0 ≤ q0 ^ (2 ^ (k + 1)) := pow_nonneg q0_pos.le _
      have hr1 : q0 ^ (2 ^ (k + 1)) < 1 := by linarith [q0_pow_two_pow_lt_third (k + 1)]
      exact (theta3_bounds hr0 hr1).2
  have hlim := (htheta3_tendsto.pow 2).div_const ((theta4 q0) ^ 2)
  simpa only [one_pow] using hlim
