import OMAReductions.R_Green40_green_40_variants_arbitrary_subsets_R1

/-! Proof of the one-step density bound for binary covering codes. -/

namespace Green40Repair

theorem hammingDist_sum {I J A : Type*} [Fintype I] [Fintype J] [DecidableEq A]
    (x y : (I → A) × (J → A)) :
    hammingDist (Sum.elim x.1 x.2) (Sum.elim y.1 y.2) =
      hammingDist x.1 y.1 + hammingDist x.2 y.2 := by
  have support :
      (Finset.univ.filter fun i : I ⊕ J => Sum.elim x.1 x.2 i ≠ Sum.elim y.1 y.2 i) =
        (Finset.univ.filter fun i => x.1 i ≠ y.1 i).disjSum
          (Finset.univ.filter fun j => x.2 j ≠ y.2 j) := by
    ext i
    cases i <;> simp
  simp only [hammingDist, support, Finset.card_disjSum]

theorem hammingDist_relabel {I J A : Type*} [Fintype I] [Fintype J] [DecidableEq A]
    (e : I ≃ J) (x y : J → A) :
    hammingDist (fun i => x (e i)) (fun i => y (e i)) = hammingDist x y := by
  unfold hammingDist
  rw [← Finset.card_map e.toEmbedding]
  rw [Finset.map_filter, Finset.map_univ_equiv]
  simp only [Function.comp_apply, Equiv.apply_symm_apply]

def appendBlocks {n m : ℕ} {A : Type*} :
    ((Fin n → A) × (Fin m → A)) ≃ (Fin (n + m) → A) :=
  (Equiv.sumArrowEquivProdArrow (Fin n) (Fin m) A).symm.trans
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl A))

theorem hammingDist_appendBlocks {n m : ℕ} {A : Type*} [DecidableEq A]
    (x y : (Fin n → A) × (Fin m → A)) :
    hammingDist (appendBlocks x) (appendBlocks y) =
      hammingDist x.1 y.1 + hammingDist x.2 y.2 := by
  have relabeled := hammingDist_relabel finSumFinEquiv (appendBlocks x) (appendBlocks y)
  have eval (p : (Fin n → A) × (Fin m → A)) :
      (fun i => appendBlocks p (finSumFinEquiv i)) = Sum.elim p.1 p.2 := by
    funext i
    obtain ⟨left, right⟩ := p
    cases i <;> simp [appendBlocks]
  rw [eval x, eval y, hammingDist_sum] at relabeled
  exact relabeled.symm


open scoped Pointwise
open scoped ENNReal

theorem covering_iff (n r : ℕ) (centers : Finset (𝔽₂ n)) :
    Green40.IsCoveringFinset n r centers ↔
      ∀ x, ∃ c ∈ centers, hammingDist x c ≤ r := by
  unfold Green40.IsCoveringFinset
  constructor
  · intro covers x
    have member : x ∈ centers + Green40.hammingBallFinset n r := by
      rw [covers]
      exact Finset.mem_univ _
    obtain ⟨c, hc, offset, hoffset, rfl⟩ := Finset.mem_add.mp member
    have hball := (Finset.mem_filter.mp hoffset).2
    refine ⟨c, hc, ?_⟩
    rw [hammingDist_comm, hammingDist_eq_hammingNorm]
    simpa [← add_assoc] using hball
  · intro covers
    ext x
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨c, hc, hdist⟩ := covers x
    refine Finset.mem_add.mpr ⟨c, hc, -c + x, ?_, by simp [← add_assoc]⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rwa [hammingDist_comm, hammingDist_eq_hammingNorm] at hdist

theorem exists_cover_product (n m r s : ℕ)
    (first : Finset (𝔽₂ n)) (second : Finset (𝔽₂ m))
    (hfirst : Green40.IsCoveringFinset n r first)
    (hsecond : Green40.IsCoveringFinset m s second) :
    ∃ cover : Finset (𝔽₂ (n + m)), Green40.IsCoveringFinset (n + m) (r + s) cover ∧
      cover.card = first.card * second.card := by
  classical
  refine ⟨(first ×ˢ second).map appendBlocks.toEmbedding, ?_, by
    simp only [Finset.card_map, Finset.card_product]⟩
  rw [covering_iff]
  intro x
  let split := (appendBlocks (n := n) (m := m)).symm x
  obtain ⟨a, ha, closeA⟩ := (covering_iff n r first).mp hfirst split.1
  obtain ⟨b, hb, closeB⟩ := (covering_iff m s second).mp hsecond split.2
  refine ⟨appendBlocks (a, b), Finset.mem_map.mpr ⟨(a, b), Finset.mk_mem_product ha hb, rfl⟩, ?_⟩
  calc
    hammingDist x (appendBlocks (a, b)) =
        hammingDist (appendBlocks split) (appendBlocks (a, b)) := by simp [split]
    _ ≤ r + s := by
      rw [hammingDist_appendBlocks]
      exact Nat.add_le_add closeA closeB



open scoped BigOperators Pointwise

theorem binary_cube_card (n : ℕ) : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by
  simp [ZMod.card]

theorem single_weight_one (n : ℕ) (j : Fin n) :
    hammingNorm (Pi.single j 1 : Fin n → ZMod 2) = 1 := by
  have support :
      (Finset.univ.filter fun i : Fin n => (Pi.single j 1 : Fin n → ZMod 2) i ≠ 0) = {j} := by
    ext i
    by_cases hi : i = j <;> simp [Pi.single_apply, hi]
  simp [hammingNorm, support]

def syndromeMap {n k : ℕ} (label : Fin n → (Fin k → ZMod 2)) :
    (Fin n → ZMod 2) →+ (Fin k → ZMod 2) where
  toFun x := ∑ i, x i • label i
  map_zero' := by simp
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]

theorem syndromeMap_single {n k : ℕ} (label : Fin n → (Fin k → ZMod 2)) (j : Fin n) :
    syndromeMap label (Pi.single j (1 : ZMod 2)) = label j := by
  change (∑ i, (Pi.single j 1 : Fin n → ZMod 2) i • label i) = _
  simp [Pi.single_apply]

theorem exists_radius_one_code (n k : ℕ) (hsize : 2 ^ k ≤ n + 1) :
    ∃ code : Finset (Fin n → ZMod 2), Green40.IsCoveringFinset n 1 code ∧
      code.card * 2 ^ k = 2 ^ n := by
  classical
  have hlabels : Fintype.card {v : Fin k → ZMod 2 // v ≠ 0} ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_subtype_compl, binary_cube_card, Fintype.card_fin]
    simpa using Nat.sub_le_of_le_add hsize
  obtain ⟨position⟩ := Function.Embedding.nonempty_of_card_le hlabels
  let label (i : Fin n) : Fin k → ZMod 2 :=
    if h : ∃ v, position v = i then (Classical.choose h).1 else 0
  have hlabel (v : {v : Fin k → ZMod 2 // v ≠ 0}) : label (position v) = v.1 := by
    have hexists : ∃ w, position w = position v := ⟨v, rfl⟩
    unfold label
    rw [dif_pos hexists]
    exact congrArg Subtype.val (position.injective (Classical.choose_spec hexists))
  let syndrome := syndromeMap label
  let representative (v : Fin k → ZMod 2) : Fin n → ZMod 2 :=
    if hv : v = 0 then 0 else Pi.single (position ⟨v, hv⟩) 1
  have hrepresentative (v : Fin k → ZMod 2) : syndrome (representative v) = v := by
    by_cases hv : v = 0
    · simp [representative, hv]
    · rw [show representative v = Pi.single (position ⟨v, hv⟩) 1 by simp [representative, hv]]
      exact (syndromeMap_single label _).trans (hlabel ⟨v, hv⟩)
  have hweight (v : Fin k → ZMod 2) : hammingNorm (representative v) ≤ 1 := by
    by_cases hv : v = 0
    · simp [representative, hv]
    · simp [representative, hv, single_weight_one]
  let code : Finset (Fin n → ZMod 2) := Finset.univ.filter fun x => syndrome x = 0
  refine ⟨code, ?_, ?_⟩
  · unfold Green40.IsCoveringFinset
    ext x
    simp only [Finset.mem_univ, iff_true]
    refine Finset.mem_add.mpr ⟨x - representative (syndrome x), ?_,
      representative (syndrome x), ?_, sub_add_cancel _ _⟩
    · simp [code, map_sub, hrepresentative]
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hweight _⟩
  · let e : (Fin n → ZMod 2) ≃ (code × (Fin k → ZMod 2)) :=
      { toFun := fun x => (⟨x - representative (syndrome x), by
          simp [code, map_sub, hrepresentative]⟩, syndrome x)
        invFun := fun p => p.1.1 + representative p.2
        left_inv := fun _ => sub_add_cancel _ _
        right_inv := by
          rintro ⟨c, v⟩
          have hc : syndrome c.1 = 0 := (Finset.mem_filter.mp c.2).2
          have hv : syndrome (c.1 + representative v) = v := by simp [hc, hrepresentative]
          apply Prod.ext
          · apply Subtype.ext
            change c.1 + representative v - representative (syndrome (c.1 + representative v)) = c.1
            rw [hv, add_sub_cancel_right]
          · exact hv }
    have hc := Fintype.card_congr e.symm
    simpa [Fintype.card_prod, binary_cube_card] using hc

theorem exists_radius_one_code_two_density (n : ℕ) :
    ∃ code : Finset (Fin n → ZMod 2), Green40.IsCoveringFinset n 1 code ∧
      code.card * (n + 1) ≤ 2 * 2 ^ n := by
  let k := Nat.log 2 (n + 1)
  obtain ⟨code, cover, hcard⟩ :=
    exists_radius_one_code n k (Nat.pow_log_le_self 2 (Nat.succ_ne_zero n))
  refine ⟨code, cover, ?_⟩
  have hnext : n + 1 < 2 ^ (k + 1) := Nat.lt_pow_of_log_lt (by decide) (Nat.lt_succ_self _)
  calc
    code.card * (n + 1) ≤ code.card * 2 ^ (k + 1) := Nat.mul_le_mul_left _ hnext.le
    _ = 2 * 2 ^ n := by rw [pow_succ, ← mul_assoc, hcard, mul_comm]



open scoped BigOperators Pointwise ENNReal
open Filter Topology

def binarySupportEquiv (n : ℕ) : (Fin n → ZMod 2) ≃ Finset (Fin n) where
  toFun x := Finset.univ.filter fun i => x i ≠ 0
  invFun s i := if i ∈ s then 1 else 0
  left_inv x := by
    have zeroOrOne : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    funext i
    rcases zeroOrOne (x i) with h | h <;> simp [h]
  right_inv s := by
    ext i
    by_cases h : i ∈ s <;> simp [h]

theorem binarySupport_card (n : ℕ) (x : Fin n → ZMod 2) :
    (binarySupportEquiv n x).card = hammingNorm x := rfl

theorem hammingShell_card (n k : ℕ) :
    (Finset.univ.filter fun x : Fin n → ZMod 2 => hammingNorm x = k).card = n.choose k := by
  let e := binarySupportEquiv n
  let shell := Finset.univ.filter fun x : Fin n → ZMod 2 => hammingNorm x = k
  have hmapped : shell.map e.toEmbedding =
      (Finset.univ : Finset (Fin n)).powersetCard k := by
    ext s
    rw [Finset.mem_map_equiv, Finset.mem_powersetCard]
    simp only [shell, Finset.mem_filter, Finset.mem_univ, true_and, Finset.subset_univ]
    rw [← binarySupport_card, show binarySupportEquiv n = e from rfl, Equiv.apply_symm_apply]
  change shell.card = _
  rw [← Finset.card_map e.toEmbedding, hmapped, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]

theorem hammingBallFinset_card (n r : ℕ) :
    (Green40.hammingBallFinset n r).card = ∑ k ∈ Finset.range (r + 1), n.choose k := by
  let ball := Green40.hammingBallFinset n r
  have hmaps (x : Fin n → ZMod 2) (hx : x ∈ ball) :
      hammingNorm x ∈ Finset.range (r + 1) := by
    have hx' : hammingNorm x ≤ r := (Finset.mem_filter.mp hx).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hx')
  have hfiber (k : ℕ) (hk : k ∈ Finset.range (r + 1)) :
      (ball.filter fun x => hammingNorm x = k) =
        Finset.univ.filter fun x : Fin n → ZMod 2 => hammingNorm x = k := by
    have hkr := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    ext x
    simp only [ball, Green40.hammingBallFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hx => hx.2, fun h => ⟨by simpa only [h] using hkr, h⟩⟩
  change ball.card = _
  calc
    ball.card = ∑ _ ∈ ball, (1 : ℕ) := by simp
    _ = ∑ k ∈ Finset.range (r + 1), ∑ x ∈ ball with hammingNorm x = k, (1 : ℕ) := by
      exact (Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1 : ℕ))).symm
    _ = ∑ k ∈ Finset.range (r + 1), n.choose k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hfiber k hk, hammingShell_card] <;> rfl

theorem hammingBall_card (n r : ℕ) :
    Nat.card (Green40.hammingBall n r) = ∑ k ∈ Finset.range (r + 1), n.choose k := by
  have hset : (↑(Green40.hammingBallFinset n r) : Set (Fin n → ZMod 2)) =
      Green40.hammingBall n r := by
    ext x
    simp [Green40.hammingBallFinset, Green40.hammingBall]
  rw [← hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, hammingBallFinset_card]

theorem tendsto_choose_normalized (k : ℕ) :
    Tendsto (fun n : ℕ => (n.choose k : ℝ) / (n : ℝ) ^ k)
      atTop (𝓝 ((k.factorial : ℝ)⁻¹)) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) * (n : ℝ)⁻¹) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    simp [hn0]
  simpa [div_eq_mul_inv, inv_pow] using ProbabilityTheory.tendsto_choose_mul_pow_atTop k h

theorem tendsto_hammingBall_normalized (r : ℕ) :
    Tendsto (fun n : ℕ => (Nat.card (Green40.hammingBall n r) : ℝ) / (n : ℝ) ^ r)
      atTop (𝓝 ((r.factorial : ℝ)⁻¹)) := by
  have term (k : ℕ) (hk : k ∈ Finset.range (r + 1)) :
      Tendsto (fun n : ℕ => (n.choose k : ℝ) / (n : ℝ) ^ r)
        atTop (𝓝 (if k = r then (r.factorial : ℝ)⁻¹ else 0)) := by
    have hkr := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    by_cases heq : k = r
    · subst k
      simpa using tendsto_choose_normalized r
    · have hpos : r - k ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt (lt_of_le_of_ne hkr heq))
      have hInv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      have hpow : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) ^ (r - k)) atTop (𝓝 0) := by
        simpa only [zero_pow hpos] using hInv.pow (r - k)
      simp only [if_neg heq]
      have h := (tendsto_choose_normalized k).mul hpow
      simp only [mul_zero] at h
      convert h using 1
      ext n
      simp only [div_eq_mul_inv, ← inv_pow, mul_assoc, ← pow_add,
        Nat.add_sub_of_le hkr]
  have h := tendsto_finsetSum (Finset.range (r + 1)) term
  simpa only [hammingBall_card, Nat.cast_sum, Finset.sum_div, Finset.sum_ite_eq',
    Finset.mem_range, Nat.lt_succ_self, if_pos] using h



theorem successor_factor_lt_three (r : ℕ) (hr : 0 < r) :
    (1 + 1 / (r : ℝ)) ^ r < 3 := by
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hbase : 1 + 1 / (r : ℝ) ≤ Real.exp (1 / (r : ℝ)) := by
    simpa [add_comm] using Real.add_one_le_exp (1 / (r : ℝ))
  have hpow : (1 + 1 / (r : ℝ)) ^ r ≤ (Real.exp (1 / (r : ℝ))) ^ r :=
    pow_le_pow_left₀ (by positivity) hbase r
  have hexp : (Real.exp (1 / (r : ℝ))) ^ r = Real.exp 1 := by
    rw [← Real.exp_nat_mul, mul_one_div_cancel (ne_of_gt hr')]
  rw [hexp] at hpow
  exact hpow.trans_lt Real.exp_one_lt_three



open Filter Topology
open scoped ENNReal

theorem tendsto_quotient_div (r : ℕ) (hr : 0 < r) :
    Tendsto (fun n : ℕ => ((n / r : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 (1 / (r : ℝ))) := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_mod_div_atTop_nhds_zero_nat hr)
  have h' := h.div_const (r : ℝ)
  simp only [sub_zero] at h'
  apply h'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hdivision : ((n % r : ℕ) : ℝ) + (r : ℝ) * ((n / r : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.mod_add_div n r
  field_simp
  linarith

theorem eventually_ball_successor_le (r : ℕ) (hr : 0 < r) :
    ∀ᶠ n in atTop, Nat.card (Green40.hammingBall (n + n / r) (r + 1)) ≤
      3 * Nat.card (Green40.hammingBall n r) * (n / r + 1) := by
  let m (n : ℕ) := n / r
  let N (n : ℕ) := n + m n
  let v (n k : ℕ) : ℝ := Nat.card (Green40.hammingBall n k)
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hfact : 0 < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have hN : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n (m n)) tendsto_id
  have hm : Tendsto (fun n : ℕ => (m n : ℝ) / (n : ℝ)) atTop (𝓝 (1 / (r : ℝ))) :=
    tendsto_quotient_div r hr
  have hm' : Tendsto (fun n : ℕ => ((m n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 (1 / (r : ℝ))) := by
    simpa only [add_div, add_zero] using hm.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hNratio : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (𝓝 (1 + 1 / (r : ℝ))) := by
    apply (hm.const_add 1).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp [N, Nat.cast_add, add_div, hn0]
  have hL : Tendsto (fun n : ℕ => v (N n) (r + 1) / (n : ℝ) ^ (r + 1))
      atTop (𝓝 ((((r + 1).factorial : ℝ)⁻¹) * (1 + 1 / (r : ℝ)) ^ (r + 1))) := by
    apply (((tendsto_hammingBall_normalized (r + 1)).comp hN).mul
      (hNratio.pow (r + 1))).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hN0 : (N n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (Nat.lt_of_succ_le hn) (Nat.le_add_right _ _)))
    change v (N n) (r + 1) / (N n : ℝ) ^ (r + 1) * ((N n : ℝ) / (n : ℝ)) ^ (r + 1) =
      v (N n) (r + 1) / (n : ℝ) ^ (r + 1)
    rw [div_pow]
    field_simp
  have hR : Tendsto (fun n : ℕ => 3 * ((v n r / (n : ℝ) ^ r) *
      (((m n : ℝ) + 1) / (n : ℝ)))) atTop
      (𝓝 (3 * ((r.factorial : ℝ)⁻¹ * (1 / (r : ℝ))))) :=
    ((tendsto_hammingBall_normalized r).mul hm').const_mul 3
  have hLim :
      ((r + 1).factorial : ℝ)⁻¹ * (1 + 1 / (r : ℝ)) ^ (r + 1) <
        3 * ((r.factorial : ℝ)⁻¹ * (1 / (r : ℝ))) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have heq :
        (((r : ℝ) + 1) * (r.factorial : ℝ))⁻¹ *
            ((1 + 1 / (r : ℝ)) ^ r * (1 + 1 / (r : ℝ))) =
          (1 + 1 / (r : ℝ)) ^ r * ((r.factorial : ℝ)⁻¹ * (1 / (r : ℝ))) := by
      field_simp
    rw [heq]
    exact mul_lt_mul_of_pos_right (successor_factor_lt_three r hr) (by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hL.eventually_lt hR hLim] with n hn h
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hRewrite :
      3 * (v n r / (n : ℝ) ^ r * (((m n : ℝ) + 1) / (n : ℝ))) =
        (3 * v n r * ((m n : ℝ) + 1)) / (n : ℝ) ^ (r + 1) := by
    rw [pow_succ]
    ring
  rw [hRewrite] at h
  have hlt := (div_lt_div_iff_of_pos_right (pow_pos hn' _)).mp h
  dsimp only [v, N, m] at hlt
  exact_mod_cast hlt.le

theorem minDensity_successor_of_cover (n m r : ℕ) (centers : Finset (Fin n → ZMod 2))
    (covers : Green40.IsCoveringFinset n r centers)
    (hvol : Nat.card (Green40.hammingBall (n + m) (r + 1)) ≤
      3 * Nat.card (Green40.hammingBall n r) * (m + 1)) :
    Green40.minDensityFinset (n + m) (r + 1) ≤
      6 * ((centers.card : ℝ≥0∞) * Nat.card (Green40.hammingBall n r) / 2 ^ n) := by
  obtain ⟨auxiliary, hauxiliary, hauxCard⟩ := exists_radius_one_code_two_density m
  obtain ⟨cover, hcover, hcard⟩ := exists_cover_product n m r 1 centers auxiliary covers hauxiliary
  have hNat : cover.card * Nat.card (Green40.hammingBall (n + m) (r + 1)) ≤
      (6 * (centers.card * Nat.card (Green40.hammingBall n r))) * 2 ^ m := by
    rw [hcard]
    calc
      _ ≤ (centers.card * auxiliary.card) *
          (3 * Nat.card (Green40.hammingBall n r) * (m + 1)) :=
        Nat.mul_le_mul_left _ hvol
      _ = (3 * (centers.card * Nat.card (Green40.hammingBall n r))) *
            (auxiliary.card * (m + 1)) := by ring
      _ ≤ (3 * (centers.card * Nat.card (Green40.hammingBall n r))) * (2 * 2 ^ m) :=
        Nat.mul_le_mul_left _ hauxCard
      _ = _ := by ring
  have hENN : (cover.card : ℝ≥0∞) * Nat.card (Green40.hammingBall (n + m) (r + 1)) ≤
      (6 * ((centers.card : ℝ≥0∞) * Nat.card (Green40.hammingBall n r))) * 2 ^ m := by
    exact_mod_cast hNat
  calc
    Green40.minDensityFinset (n + m) (r + 1) ≤
        (cover.card : ℝ≥0∞) * Nat.card (Green40.hammingBall (n + m) (r + 1)) /
          2 ^ (n + m) := iInf₂_le cover hcover
    _ ≤ ((6 * ((centers.card : ℝ≥0∞) * Nat.card (Green40.hammingBall n r))) * 2 ^ m) /
        2 ^ (n + m) := by gcongr
    _ = 6 * ((centers.card : ℝ≥0∞) * Nat.card (Green40.hammingBall n r) / 2 ^ n) := by
      rw [pow_add, ENNReal.mul_div_mul_right _ _ (by simp) (by simp), mul_div_assoc]

theorem successor_density_le (r : ℕ) (hr : 0 < r) :
    Green40.f_tilde (r + 1) ≤ 6 * Green40.f_tilde r := by
  by_contra! bad
  obtain ⟨threshold, hlower, hupper⟩ := exists_between bad
  let budget : ℝ≥0∞ := threshold / 6
  have hbudget : (6 : ℝ≥0∞) * budget = threshold := by
    dsimp [budget]
    rw [mul_comm, ENNReal.div_mul_cancel (by simp) (by simp)]
  have hlt : Green40.f_tilde r < budget :=
    (ENNReal.mul_lt_mul_iff_right (a := (6 : ℝ≥0∞)) (by simp) (by simp)).mp
      (by simpa only [hbudget] using hlower)
  have hnear : ∃ᶠ n in atTop, Green40.minDensityFinset n r < budget :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
  have hnext : ∃ᶠ n in atTop, Green40.minDensityFinset (n + n / r) (r + 1) ≤ threshold := by
    refine (hnear.and_eventually (eventually_ball_successor_le r hr)).mono ?_
    intro n hn
    obtain ⟨low, hvol⟩ := hn
    simp only [Green40.minDensityFinset, iInf_lt_iff, exists_prop] at low
    obtain ⟨centers, covers, hcenters⟩ := low
    refine (minDensity_successor_of_cover n (n / r) r centers covers hvol).trans ?_
    rw [← hbudget]
    exact (ENNReal.mul_le_mul_iff_right (a := (6 : ℝ≥0∞)) (by simp) (by simp)).mpr hcenters.le
  apply not_le_of_gt hupper
  unfold Green40.f_tilde
  apply liminf_le_of_frequently_le'
  rw [frequently_atTop]
  intro bound
  obtain ⟨n, hn, good⟩ := frequently_atTop.mp hnext bound
  exact ⟨n + n / r, hn.trans (Nat.le_add_right n _), good⟩


end Green40Repair

theorem OMA.solution : OMA.R_Green40_green_40_variants_arbitrary_subsets_R1.H2 := by
  exact Green40Repair.successor_density_le
