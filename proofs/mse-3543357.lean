import OMAStatements.S_mse_3543357

open MeasureTheory
open scoped ENNReal

namespace MSE3543357Proof

def branch (n : ℕ) : ℕ := 2 ^ (n + 1)

abbrev Path : Type := (n : ℕ) → Fin (branch n)

abbrev Prefix (n : ℕ) : Type := (i : Fin n) → Fin (branch i.val)

def X : Type := Path ⊕ (Σ n : ℕ, Prefix n)

def takePrefix (x : Path) (n : ℕ) : Prefix n := fun i => x i.val

def baseIn (x : Path) : X := Sum.inl x

def atomIn (n : ℕ) (x : Path) : X := Sum.inr ⟨n, takePrefix x n⟩

def signature (x : X) (i : ℕ) : Option (Fin (branch i)) :=
  match (x : Path ⊕ (Σ n : ℕ, Prefix n)) with
  | .inl y => some (y i)
  | .inr ⟨n, p⟩ => if h : i < n then some (p ⟨i, h⟩) else none

def cyl (x : Path) (n : ℕ) : Set Path := {y | ∀ i < n, y i = x i}

def subtree (x : Path) (n : ℕ) : Set X := {y | ∀ i < n, signature y i = some (x i)}

noncomputable def scale (n : ℕ) : ℝ := (1 / 4 : ℝ) ^ n

noncomputable def coordinateMeasure (n : ℕ) : Measure (Fin (branch n)) :=
  (branch n : ℝ≥0∞)⁻¹ • Measure.count

noncomputable def base : Measure Path := Measure.infinitePi coordinateMeasure

noncomputable def weight (n : ℕ) : ℝ≥0∞ := 3 * (1 / 4 : ℝ≥0∞) ^ (n + 1)

noncomputable def μ [MeasurableSpace X] : Measure X :=
  (1 / 2 : ℝ≥0∞) • (base.map baseIn + Measure.sum (fun n => weight n • base.map (atomIn n)))

end MSE3543357Proof

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace MSE3543357Proof

private def starDist {α : Type} [DecidableEq α] (a b : Option α) : ℝ :=
  if a = b then 0 else if a.isSome && b.isSome then 2 else 1

private theorem starDist_nonneg {α : Type} [DecidableEq α] (a b : Option α) :
    0 ≤ starDist a b := by
  unfold starDist
  split_ifs <;> norm_num

private theorem starDist_le_two {α : Type} [DecidableEq α] (a b : Option α) :
    starDist a b ≤ 2 := by
  unfold starDist
  split_ifs <;> norm_num

private theorem starDist_ge_one {α : Type} [DecidableEq α] {a b : Option α}
    (h : a ≠ b) : 1 ≤ starDist a b := by
  unfold starDist
  rw [if_neg h]
  split_ifs <;> norm_num

private theorem starDist_comm {α : Type} [DecidableEq α] (a b : Option α) :
    starDist a b = starDist b a := by
  by_cases h : a = b
  · subst b
    rfl
  · simp only [starDist, if_neg h, if_neg (Ne.symm h)]
    rw [Bool.and_comm a.isSome b.isSome]

private theorem starDist_triangle {α : Type} [DecidableEq α] (a b c : Option α) :
    starDist a c ≤ starDist a b + starDist b c := by
  by_cases hab : a = b
  · subst b
    simp [starDist]
  by_cases hbc : b = c
  · subst c
    simp [starDist]
  linarith [starDist_le_two a c, starDist_ge_one hab, starDist_ge_one hbc]

theorem scale_pos (n : ℕ) : 0 < scale n := by
  unfold scale
  positivity

theorem scale_succ (n : ℕ) : scale (n + 1) = scale n / 4 := by
  simp [scale, pow_succ, div_eq_mul_inv]

theorem scale_antitone : Antitone scale := by
  intro n m h
  induction m with
  | zero =>
    have hn : n = 0 := Nat.eq_zero_of_le_zero h
    subst n
    rfl
  | succ m ih =>
    by_cases hm : n ≤ m
    · rw [scale_succ]
      exact (show scale m / 4 ≤ scale m by linarith [scale_pos m]).trans (ih hm)
    · have hn : n = m + 1 := by omega
      rw [hn]

theorem scale_vanishes : Tendsto scale atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (1 / 4 : ℝ) ^ n) atTop (𝓝 0)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1 / 4 by norm_num) (by norm_num)

private noncomputable def rawCoordinate (x y : X) (n : ℕ) : ℝ :=
  scale n * starDist (signature x n) (signature y n)

private theorem rawCoordinate_le (x y : X) (n : ℕ) :
    rawCoordinate x y n ≤ 2 * scale n := by
  rw [mul_comm 2]
  exact mul_le_mul_of_nonneg_left (starDist_le_two _ _) (scale_pos _).le

private theorem rawCoordinate_bounded (x y : X) :
    BddAbove (range (rawCoordinate x y)) := by
  refine ⟨2, ?_⟩
  rintro _ ⟨i, rfl⟩
  have h := scale_antitone (Nat.zero_le i)
  have h0 : scale 0 = 1 := by norm_num [scale]
  rw [h0] at h
  exact (rawCoordinate_le _ _ _).trans (by linarith)

private theorem rawCoordinate_below_iSup (x y : X) (i : ℕ) :
    rawCoordinate x y i ≤ iSup (rawCoordinate x y) :=
  le_ciSup (rawCoordinate_bounded x y) i

private theorem rawCoordinate_ge_scale {x y : X} {i : ℕ}
    (h : signature x i ≠ signature y i) : scale i ≤ rawCoordinate x y i := by
  unfold rawCoordinate
  simpa using mul_le_mul_of_nonneg_left (starDist_ge_one h) (scale_pos i).le

private theorem eq_atom_of_signatures (n : ℕ) (p : Prefix n) (y : X)
    (h : ∀ i ≤ n, signature y i = signature (Sum.inr ⟨n, p⟩ : X) i) :
    y = (Sum.inr ⟨n, p⟩ : X) := by
  cases y with
  | inl u =>
    simpa [signature] using h n (Nat.le_refl n)
  | inr v =>
    rcases v with ⟨m, q⟩
    by_cases hmn : m < n
    · have hf : False := by simpa [signature, hmn] using h m hmn.le
      exact hf.elim
    by_cases hnm : n < m
    · have hf : False := by simpa [signature, hnm] using h n (Nat.le_refl n)
      exact hf.elim
    have heq : m = n := by omega
    subst m
    have hpq : q = p := by
      funext i
      simpa [signature, i.isLt] using h i.val i.isLt.le
    subst q
    rfl

private theorem signature_injective : Function.Injective (fun x : X => signature x) := by
  intro x y h
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      have huv : u = v := by
        funext i
        simpa [signature] using congrFun h i
      subst v
      rfl
    | inr v =>
      rcases v with ⟨m, q⟩
      exact eq_atom_of_signatures m q (Sum.inl u) (fun i _ => congrFun h i)
  | inr u =>
    rcases u with ⟨m, q⟩
    exact (eq_atom_of_signatures m q y (fun i _ => (congrFun h i).symm)).symm

noncomputable instance : MetricSpace X where
  dist x y := iSup (rawCoordinate x y)
  dist_self x := by
    have h : rawCoordinate x x = fun _ => 0 := by
      funext i
      simp [rawCoordinate, starDist]
    rw [h, ciSup_const]
  dist_comm x y := by
    congr 1
    funext i
    exact congrArg (scale i * ·) (starDist_comm _ _)
  dist_triangle x y z := by
    apply ciSup_le
    intro i
    calc
      rawCoordinate x z i ≤ rawCoordinate x y i + rawCoordinate y z i := by
        unfold rawCoordinate
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (starDist_triangle _ _ _) (scale_pos i).le
      _ ≤ iSup (rawCoordinate x y) + iSup (rawCoordinate y z) :=
        add_le_add (rawCoordinate_below_iSup _ _ _) (rawCoordinate_below_iSup _ _ _)
  eq_of_dist_eq_zero := by
    intro x y h
    apply signature_injective
    funext i
    by_contra hi
    have ht := (rawCoordinate_ge_scale hi).trans (rawCoordinate_below_iSup x y i)
    change iSup (rawCoordinate x y) = 0 at h
    exact (not_le_of_gt (scale_pos i)) (h ▸ ht)

private theorem coordinate_le_dist (x y : X) (i : ℕ) :
    rawCoordinate x y i ≤ dist x y := rawCoordinate_below_iSup x y i

private theorem dist_le_of_coordinates {x y : X} {r : ℝ}
    (h : ∀ i, rawCoordinate x y i ≤ r) : dist x y ≤ r := ciSup_le h

theorem signature_eq_of_dist_lt {x y : X} {i : ℕ} (h : dist x y < scale i) :
    signature x i = signature y i := by
  by_contra hi
  exact (not_lt_of_ge ((rawCoordinate_ge_scale hi).trans (coordinate_le_dist x y i))) h

theorem dist_le_of_agree {x y : X} {n : ℕ}
    (h : ∀ i < n, signature x i = signature y i) : dist x y ≤ 2 * scale n := by
  apply dist_le_of_coordinates
  intro i
  by_cases hi : i < n
  · simp [rawCoordinate, starDist, h i hi, (scale_pos n).le]
  · exact (rawCoordinate_le x y i).trans (by
      have hs := scale_antitone (Nat.le_of_not_gt hi)
      linarith)

theorem dist_baseIn_atomIn (x : Path) (n : ℕ) :
    dist (baseIn x) (atomIn n x) = scale n := by
  apply le_antisymm
  · apply dist_le_of_coordinates
    intro i
    by_cases hi : i < n
    · simpa [rawCoordinate, baseIn, atomIn, signature, starDist, takePrefix, hi] using
        (scale_pos n).le
    · simpa [rawCoordinate, baseIn, atomIn, signature, starDist, takePrefix, hi] using
        scale_antitone (Nat.le_of_not_gt hi)
  · have h := coordinate_le_dist (baseIn x) (atomIn n x) n
    simpa [rawCoordinate, baseIn, atomIn, signature, starDist] using h

theorem closedBall_baseIn (x : Path) (n : ℕ) {r : ℝ}
    (hlo : 2 * scale (n + 1) ≤ r) (hhi : r < 2 * scale n) :
    Metric.closedBall (baseIn x) r =
      subtree x (n + 1) ∪ (if scale n ≤ r then {atomIn n x} else ∅) := by
  ext y
  rw [Metric.mem_closedBall, dist_comm, Set.mem_union]
  constructor
  · intro hy
    have hprefix : ∀ i < n, signature y i = some (x i) := by
      intro i hi
      by_contra h
      have hd := (rawCoordinate_ge_scale (x := baseIn x) (y := y)
        (show signature (baseIn x) i ≠ signature y i from Ne.symm h)).trans
        (coordinate_le_dist (baseIn x) y i)
      have hs := scale_antitone (Nat.succ_le_of_lt hi)
      rw [scale_succ] at hs
      linarith [scale_pos i]
    cases hn : signature y n with
    | none =>
      have hay : y = atomIn n x := by
        apply eq_atom_of_signatures n (takePrefix x n) y
        intro i hi
        rcases hi.eq_or_lt with h | hi
        · subst i
          have hsig : signature (atomIn n x) n = none := by
            simp [atomIn, signature]
          exact hn.trans hsig.symm
        · have hsig : signature (atomIn n x) i = some (x i) := by
            simp [atomIn, signature, takePrefix, hi]
          exact (hprefix i hi).trans hsig.symm
      subst y
      rw [dist_baseIn_atomIn] at hy
      exact Or.inr (by simp [hy])
    | some a =>
      have hax : a = x n := by
        by_contra hne
        have hd := coordinate_le_dist (baseIn x) y n
        have hd' : 2 * scale n ≤ dist (baseIn x) y := by
          change scale n * starDist (some (x n)) (signature y n) ≤ dist (baseIn x) y at hd
          rw [hn] at hd
          simpa [starDist, Ne.symm hne, mul_comm] using hd
        linarith
      apply Or.inl
      intro i hi
      rcases (Nat.le_of_lt_succ hi).eq_or_lt with rfl | hi
      · simpa only [hax] using hn
      · exact hprefix i hi
  · rintro (hsub | hatom)
    · apply le_trans (dist_le_of_agree (n := n + 1) fun i hi => ?_) hlo
      exact (hsub i hi).symm
    · by_cases hs : scale n ≤ r
      · have hy : y = atomIn n x := by simpa [hs] using hatom
        simpa [hy, dist_baseIn_atomIn] using hs
      · simp [hs] at hatom

private def pointAtom (a : Σ n : ℕ, Prefix n) : X := Sum.inr a

private theorem ball_pointAtom (n : ℕ) (p : Prefix n) :
    Metric.ball (pointAtom ⟨n, p⟩) (scale n) = {pointAtom ⟨n, p⟩} := by
  ext y
  rw [Metric.mem_ball, Set.mem_singleton_iff]
  constructor
  · intro hy
    apply eq_atom_of_signatures n p y
    intro i hi
    exact signature_eq_of_dist_lt (hy.trans_le (scale_antitone hi))
  · rintro rfl
    rw [dist_self]
    exact scale_pos n

theorem ball_atomIn (n : ℕ) (x : Path) :
    Metric.ball (atomIn n x) (scale n) = {atomIn n x} :=
  ball_pointAtom n (takePrefix x n)

theorem isOpen_singleton_atomIn (n : ℕ) (x : Path) : IsOpen ({atomIn n x} : Set X) := by
  rw [← ball_atomIn n x]
  exact Metric.isOpen_ball

theorem isClosed_subtree (x : Path) (n : ℕ) : IsClosed (subtree x n) := by
  cases n with
  | zero =>
    have he : subtree x 0 = univ := by ext y; simp [subtree]
    rw [he]
    exact isClosed_univ
  | succ n =>
    have hr : 2 * scale (n + 1) < scale n := by
      rw [scale_succ]
      linarith [scale_pos n]
    have hball := closedBall_baseIn x n le_rfl (show 2 * scale (n + 1) < 2 * scale n by
      linarith [scale_pos n])
    rw [if_neg (not_le_of_gt hr), Set.union_empty] at hball
    rw [← hball]
    exact Metric.isClosed_closedBall

private theorem exists_small_scale {ε : ℝ} (hε : 0 < ε) :
    ∃ n, 2 * scale n < ε := by
  have hh : 0 < ε / 2 := by positivity
  obtain ⟨n, hn⟩ := (scale_vanishes.eventually (gt_mem_nhds hh)).exists
  change scale n < ε / 2 at hn
  exact ⟨n, by linarith⟩

instance : SeparableSpace X := by
  refine .of_denseRange pointAtom ?_
  intro z
  apply Metric.mem_closure_iff.2
  intro ε hε
  cases z with
  | inl x =>
    obtain ⟨n, hn⟩ := exists_small_scale hε
    refine ⟨pointAtom ⟨n, takePrefix x n⟩, ⟨⟨n, takePrefix x n⟩, rfl⟩, ?_⟩
    apply lt_of_le_of_lt (dist_le_of_agree (n := n) fun i hi => ?_) hn
    simp [pointAtom, signature, takePrefix, hi]
  | inr a =>
    refine ⟨pointAtom a, ⟨a, rfl⟩, ?_⟩
    change dist (pointAtom a) (pointAtom a) < ε
    rwa [dist_self]

private theorem isOpen_cyl (x : Path) (n : ℕ) : IsOpen (cyl x n) := by
  change IsOpen ((Set.Iio n).pi fun i => {x i})
  exact isOpen_set_pi (Set.finite_Iio n) fun i _ => isOpen_discrete _

theorem continuous_baseIn : Continuous baseIn := by
  refine Metric.continuous_iff'.2 fun x ε hε => ?_
  obtain ⟨n, hn⟩ := exists_small_scale hε
  have hx : x ∈ cyl x n := fun _ _ => rfl
  refine Filter.mem_of_superset ((isOpen_cyl x n).mem_nhds hx) fun y hy => ?_
  exact (dist_le_of_agree (x := baseIn y) (y := baseIn x) (n := n)
    fun i hi => congrArg some (hy i hi)).trans_lt hn

theorem continuous_atomIn (n : ℕ) : Continuous (atomIn n) := by
  refine Metric.continuous_iff'.2 fun x ε hε => ?_
  have hx : x ∈ cyl x n := fun _ _ => rfl
  refine Filter.mem_of_superset ((isOpen_cyl x n).mem_nhds hx) fun y hy => ?_
  have hxy : takePrefix y n = takePrefix x n := funext fun i => hy i.val i.isLt
  have hEq : atomIn n y = atomIn n x :=
    congrArg (fun p : Prefix n => (Sum.inr ⟨n, p⟩ : X)) hxy
  change dist (atomIn n y) (atomIn n x) < ε
  rwa [hEq, dist_self]

noncomputable instance : MeasurableSpace X := borel X

instance : BorelSpace X := ⟨rfl⟩

theorem measurable_baseIn : Measurable baseIn := continuous_baseIn.measurable

theorem measurable_atomIn (n : ℕ) : Measurable (atomIn n) := (continuous_atomIn n).measurable

theorem measurableEmbedding_baseIn : MeasurableEmbedding baseIn :=
  (continuous_baseIn.isClosedEmbedding fun _ _ h => Sum.inl.inj h).measurableEmbedding

instance : CompleteSpace X := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  choose N hN using fun i : ℕ => (Metric.cauchySeq_iff.mp hu) (scale i) (scale_pos i)
  let s (i : ℕ) := signature (u (N i)) i
  have hs (i m : ℕ) (hm : N i ≤ m) : signature (u m) i = s i :=
    signature_eq_of_dist_lt (hN i m hm (N i) le_rfl)
  have hstable (k m : ℕ) (hm : N k ≤ m) (i : ℕ) (hi : i ≤ k) :
      signature (u m) i = s i := by
    let j := max m (N i)
    have hjm : m ≤ j := le_max_left _ _
    have hji : N i ≤ j := le_max_right _ _
    have hd := (hN k m hm j (hm.trans hjm)).trans_le (scale_antitone hi)
    exact (signature_eq_of_dist_lt hd).trans (hs i j hji)
  by_cases hnone : ∃ k, s k = none
  · obtain ⟨k, hk⟩ := hnone
    have hk' : signature (u (N k)) k = none := hk
    use u (N k)
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [eventually_ge_atTop (N k)] with m hm
    cases ha : u (N k) with
    | inl x =>
      simp [ha, signature] at hk'
    | inr a =>
      rcases a with ⟨j, p⟩
      have hj : j ≤ k := by
        by_contra h
        have hkj := Nat.lt_of_not_ge h
        simp [ha, signature, hkj] at hk'
      have he : u m = (Sum.inr ⟨j, p⟩ : X) := by
        apply eq_atom_of_signatures j p
        intro i hi
        have hsig := (hstable k m hm i (hi.trans hj)).trans
          (hstable k (N k) le_rfl i (hi.trans hj)).symm
        exact hsig.trans (congrArg (signature · i) ha)
      change dist (u m) (pointAtom ⟨j, p⟩) < ε
      change u m = pointAtom ⟨j, p⟩ at he
      rw [he, dist_self]
      exact hε
  · have hsome (i : ℕ) : (s i).isSome := by
      cases h : s i with
      | none => exact (hnone ⟨i, h⟩).elim
      | some a => rfl
    let x : Path := fun i => (s i).get (hsome i)
    have hx (i : ℕ) : signature (baseIn x) i = s i := by
      change some ((s i).get (hsome i)) = s i
      exact Option.some_get _
    use baseIn x
    apply Metric.tendsto_nhds.2
    intro ε hε
    obtain ⟨k, hk⟩ := exists_small_scale hε
    filter_upwards [eventually_ge_atTop (N k)] with m hm
    exact (dist_le_of_agree (n := k) fun i hi =>
      (hstable k m hm i hi.le).trans (hx i).symm).trans_lt hk

end MSE3543357Proof

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators

namespace MSE3543357Proof

theorem measure_branch_pos (n : ℕ) : 0 < branch n := by
  unfold branch
  positivity

theorem measure_branch_ne_zero (n : ℕ) : (branch n : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast (measure_branch_pos n).ne'

instance measure_coordinate_probability (n : ℕ) : IsProbabilityMeasure (coordinateMeasure n) := by
  constructor
  rw [coordinateMeasure, Measure.smul_apply, smul_eq_mul, Measure.count_univ]
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin, ENat.toENNReal_coe]
  exact ENNReal.inv_mul_cancel (measure_branch_ne_zero n) (by simp)

instance measure_base_probability : IsProbabilityMeasure base := by
  unfold base
  infer_instance

theorem cyl_eq_pi (x : Path) (n : ℕ) :
    cyl x n = (↑(Finset.range n) : Set ℕ).pi (fun i => ({x i} : Set (Fin (branch i)))) := by
  ext y
  simp [cyl, Set.mem_pi]

theorem measurable_cyl (x : Path) (n : ℕ) : MeasurableSet (cyl x n) := by
  rw [cyl_eq_pi]
  exact MeasurableSet.pi (Finset.countable_toSet _) (fun i _ => measurableSet_singleton (x i))

theorem base_cyl_eq_prod (x : Path) (n : ℕ) :
    base (cyl x n) = ∏ i ∈ Finset.range n, (branch i : ℝ≥0∞)⁻¹ := by
  rw [base, cyl_eq_pi, Measure.infinitePi_pi coordinateMeasure]
  · simp only [coordinateMeasure, Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one]
  · exact fun i _ => measurableSet_singleton (x i)

theorem base_cyl_pos (x : Path) (n : ℕ) : 0 < base (cyl x n) := by
  rw [base_cyl_eq_prod]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    exact ENNReal.mul_pos ih.ne' (ENNReal.inv_pos.mpr (by simp)).ne'

theorem base_cyl_succ (x : Path) (n : ℕ) :
    base (cyl x (n + 1)) = base (cyl x n) / (branch n : ℝ≥0∞) := by
  simp only [base_cyl_eq_prod, Finset.prod_range_succ, div_eq_mul_inv]

theorem base_cyl_mul (x : Path) (n : ℕ) :
    base (cyl x (n + 1)) * (branch n : ℝ≥0∞) = base (cyl x n) := by
  rw [base_cyl_succ, div_eq_mul_inv]
  exact ENNReal.inv_mul_cancel_right (measure_branch_ne_zero n) (by simp)

theorem measure_weight_pos (n : ℕ) : 0 < weight n := by
  rw [weight, one_div]
  exact ENNReal.mul_pos (by simp) (pow_ne_zero _ (ENNReal.inv_pos.mpr (by simp)).ne')

theorem measure_weight_ne_top (n : ℕ) : weight n ≠ ⊤ := by
  unfold weight
  finiteness

theorem measure_weight_tsum : ∑' n : ℕ, weight n = 1 := by
  calc
    (∑' n : ℕ, weight n) = (3 * (1 / 4) : ℝ≥0∞) * ∑' n : ℕ, (1 / 4 : ℝ≥0∞) ^ n := by
      simp only [weight, pow_succ', ← mul_assoc, ENNReal.tsum_mul_left]
    _ = 1 := by
      rw [ENNReal.tsum_geometric]
      have hdiv : (↑(1 / 4 : ℝ≥0) : ℝ≥0∞) = 1 / 4 := by
        rw [ENNReal.coe_div (by norm_num), ENNReal.coe_one, ENNReal.coe_ofNat]
      have hlt : (1 / 4 : ℝ≥0) < 1 := by norm_num
      have hinv : (↑((1 - 1 / 4 : ℝ≥0)⁻¹) : ℝ≥0∞) = (1 - 1 / 4)⁻¹ := by
        rw [ENNReal.coe_inv (ne_of_gt (tsub_pos_of_lt hlt)), ENNReal.coe_sub, ENNReal.coe_one, hdiv]
      have hcalc : (3 : ℝ≥0) * (1 / 4) * ((1 - 1 / 4)⁻¹) = 1 := by
        apply NNReal.coe_injective
        norm_num [NNReal.coe_sub hlt.le]
      simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat, hdiv, hinv, ENNReal.coe_one] using
        congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hcalc

theorem measure_weight_tail (n : ℕ) :
    (∑' m : ℕ, if n ≤ m then weight m else 0) = (1 / 4 : ℝ≥0∞) ^ n := by
  let e : ℕ ≃ Set.Ici n :=
    { toFun := fun k => ⟨k + n, Nat.le_add_left n k⟩
      invFun := fun k => k.val - n
      left_inv := fun k => by simp
      right_inv := fun k => Subtype.ext (Nat.sub_add_cancel k.property) }
  calc
    (∑' m : ℕ, if n ≤ m then weight m else 0) = ∑' m : Set.Ici n, weight m := by
      simpa [Set.indicator, Set.mem_Ici] using (tsum_subtype (s := Set.Ici n) (f := weight)).symm
    _ = ∑' m : ℕ, weight (m + n) := (e.tsum_eq fun m => weight m.val).symm
    _ = ∑' m : ℕ, (1 / 4 : ℝ≥0∞) ^ n * weight m := by
      refine tsum_congr fun m => ?_
      rw [weight, weight, show m + n + 1 = (m + 1) + n by omega, pow_add]
      exact (mul_assoc (3 : ℝ≥0∞) _ _).symm.trans (mul_comm _ _)
    _ = _ := by rw [ENNReal.tsum_mul_left, measure_weight_tsum, mul_one]

theorem base_preimage_subtree (x : Path) (n : ℕ) : baseIn ⁻¹' subtree x n = cyl x n := by
  ext y
  simp [baseIn, subtree, signature, cyl]

theorem atom_preimage_subtree (x : Path) (n m : ℕ) :
    atomIn m ⁻¹' subtree x n = if n ≤ m then cyl x n else ∅ := by
  classical
  ext y
  by_cases h : n ≤ m
  · simp only [h, ite_true, mem_preimage, subtree, cyl, mem_ofPred_eq]
    constructor
    · intro hy i hi
      have hm : i < m := hi.trans_le h
      simpa [atomIn, signature, hm, takePrefix] using hy i hi
    · intro hy i hi
      have hm : i < m := hi.trans_le h
      simpa [atomIn, signature, hm, takePrefix] using hy i hi
  · simp only [h, ite_false, mem_empty_iff_false, iff_false, mem_preimage,
      subtree, mem_ofPred_eq]
    intro hy
    have hy' := hy m (lt_of_not_ge h)
    simp [atomIn, signature] at hy'

theorem base_preimage_parent (x : Path) (n : ℕ) :
    baseIn ⁻¹' ({atomIn n x} : Set X) = ∅ := by
  ext y
  change (baseIn y = atomIn n x) ↔ False
  simp [baseIn, atomIn]

theorem atom_preimage_parent_same (x : Path) (n : ℕ) :
    atomIn n ⁻¹' ({atomIn n x} : Set X) = cyl x n := by
  ext y
  change ((Sum.inr ⟨n, takePrefix y n⟩ : Path ⊕ (Σ k, Prefix k)) =
    Sum.inr ⟨n, takePrefix x n⟩) ↔ ∀ i < n, y i = x i
  simp only [Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and]
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.val i.isLt

theorem atom_preimage_parent_ne (x : Path) {m n : ℕ} (h : m ≠ n) :
    atomIn m ⁻¹' ({atomIn n x} : Set X) = ∅ := by
  ext y
  change ((Sum.inr ⟨m, takePrefix y m⟩ : Path ⊕ (Σ k, Prefix k)) =
    Sum.inr ⟨n, takePrefix x n⟩) ↔ False
  simp [h]

noncomputable def spikeHeight (n : ℕ) : ℝ≥0∞ := (weight n * (branch n : ℝ≥0∞))⁻¹

noncomputable def spike (z : X) : ℝ :=
  match (z : Path ⊕ (Σ n : ℕ, Prefix n)) with
  | .inl _ => 0
  | .inr a => (spikeHeight a.1).toReal

theorem spike_base (x : Path) : spike (baseIn x) = 0 := rfl

theorem spike_atom (x : Path) (n : ℕ) : spike (atomIn n x) = (spikeHeight n).toReal := rfl

theorem spike_nonneg (z : X) : 0 ≤ spike z := by
  rcases (z : Path ⊕ (Σ n : ℕ, Prefix n)) with x | a
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

theorem spikeHeight_ne_top (n : ℕ) : spikeHeight n ≠ ⊤ :=
  ENNReal.inv_ne_top.mpr (mul_ne_zero (measure_weight_pos n).ne' (measure_branch_ne_zero n))

theorem spikeHeight_mul (n : ℕ) : weight n * spikeHeight n = (branch n : ℝ≥0∞)⁻¹ := by
  rw [spikeHeight, ENNReal.mul_inv (Or.inl (measure_weight_pos n).ne')
    (Or.inl (measure_weight_ne_top n)), ← mul_assoc,
    ENNReal.mul_inv_cancel (measure_weight_pos n).ne' (measure_weight_ne_top n), one_mul]

theorem inv_branch_tsum : ∑' n : ℕ, (branch n : ℝ≥0∞)⁻¹ = 1 := by
  simp_rw [branch, Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow,
    ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

section WithMeasure

variable [MeasurableSpace X]

theorem measurable_spike [MeasurableSingletonClass X] : Measurable spike := by
  have hzero : Measurable (fun _ : X => (0 : ℝ)) := measurable_const
  refine hzero.measurable_of_countable_ne ?_
  refine (Set.countable_range (fun p : (Σ n, Prefix n) => (Sum.inr p : X))).mono ?_
  intro z hz
  rcases (z : Path ⊕ (Σ n : ℕ, Prefix n)) with x | a
  · exact False.elim (hz rfl)
  · exact ⟨a, rfl⟩

theorem mixture_apply (hbase : Measurable baseIn) (hatom : ∀ n, Measurable (atomIn n))
    {s : Set X} (hs : MeasurableSet s) :
    μ s = (1 / 2 : ℝ≥0∞) *
      (base (baseIn ⁻¹' s) + ∑' n : ℕ, weight n * base (atomIn n ⁻¹' s)) := by
  rw [μ, Measure.smul_apply, smul_eq_mul, Measure.add_apply, Measure.map_apply hbase hs,
    Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hatom _) hs]

theorem mixture_probability (hbase : Measurable baseIn) (hatom : ∀ n, Measurable (atomIn n)) :
    IsProbabilityMeasure μ := by
  constructor
  rw [mixture_apply hbase hatom MeasurableSet.univ]
  simp [measure_weight_tsum]
  norm_num
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

theorem mixture_subtree (hbase : Measurable baseIn) (hatom : ∀ n, Measurable (atomIn n))
    (x : Path) (n : ℕ) (hs : MeasurableSet (subtree x n)) :
    μ (subtree x n) = (1 / 2 : ℝ≥0∞) *
      (base (cyl x n) + ∑' m : ℕ, if n ≤ m then weight m * base (cyl x n) else 0) := by
  classical
  have ht : (∑' m : ℕ, weight m * base (atomIn m ⁻¹' subtree x n)) =
      ∑' m : ℕ, if n ≤ m then weight m * base (cyl x n) else 0 := by
    refine tsum_congr fun m => ?_
    rw [atom_preimage_subtree]
    split <;> simp
  rw [mixture_apply hbase hatom hs, base_preimage_subtree, ht]

theorem mixture_parent (hbase : Measurable baseIn) (hatom : ∀ n, Measurable (atomIn n))
    (x : Path) (n : ℕ) (hs : MeasurableSet ({atomIn n x} : Set X)) :
    μ ({atomIn n x} : Set X) = (1 / 2 : ℝ≥0∞) * (weight n * base (cyl x n)) := by
  rw [mixture_apply hbase hatom hs, base_preimage_parent, measure_empty, zero_add]
  rw [tsum_eq_single n]
  · rw [atom_preimage_parent_same]
  · intro m hm
    simp [atom_preimage_parent_ne x hm]

theorem mixture_base_image (hbase : Measurable baseIn) (hatom : ∀ n, Measurable (atomIn n))
    (s : Set Path) (hs : MeasurableSet (baseIn '' s)) :
    μ (baseIn '' s) = (1 / 2 : ℝ≥0∞) * base s := by
  rw [mixture_apply hbase hatom hs]
  have hinj : Function.Injective baseIn := Sum.inl_injective
  have hd (n : ℕ) : atomIn n ⁻¹' (baseIn '' s) = ∅ := by
    ext y
    change (∃ a ∈ s, baseIn a = atomIn n y) ↔ False
    simp [atomIn, baseIn]
  simp [hinj.preimage_image, hd]

theorem spike_integrable (hbase : Measurable baseIn) (hatom : ∀ n, Measurable (atomIn n))
    (hf : Measurable spike) : Integrable spike μ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  change (∫⁻ z, ‖spike z‖ₑ ∂μ) < ∞
  have hNorm : Measurable (fun z => ‖spike z‖ₑ) := measurable_enorm.comp hf
  have hleft : (∫⁻ z, ‖spike z‖ₑ ∂(base.map baseIn)) = 0 := by
    rw [lintegral_map hNorm hbase]
    simp [spike_base]
  have hright (n : ℕ) : (∫⁻ z, ‖spike z‖ₑ ∂(base.map (atomIn n))) = spikeHeight n := by
    rw [lintegral_map hNorm (hatom n)]
    simp [spike_atom, Real.enorm_toReal (spikeHeight_ne_top n)]
  rw [μ, lintegral_smul_measure, lintegral_add_measure, lintegral_sum_measure, hleft, zero_add]
  simp_rw [lintegral_smul_measure, smul_eq_mul, hright, spikeHeight_mul, inv_branch_tsum, mul_one]
  finiteness

theorem spike_parent_integral [MeasurableSingletonClass X] (hbase : Measurable baseIn)
    (hatom : ∀ n, Measurable (atomIn n)) (x : Path) (n : ℕ) :
    (∫ z in {atomIn n x}, spike z ∂μ) = (1 / 2 : ℝ) * (base (cyl x (n + 1))).toReal := by
  rw [integral_singleton, measureReal_def, mixture_parent hbase hatom x n
    (measurableSet_singleton _), smul_eq_mul, spike_atom, ← ENNReal.toReal_mul]
  have hparent : ((1 / 2 : ℝ≥0∞) * (weight n * base (cyl x n))) * spikeHeight n =
      (1 / 2) * (base (cyl x n) * (branch n : ℝ≥0∞)⁻¹) := by
    calc
      _ = (1 / 2) * (base (cyl x n) * (weight n * spikeHeight n)) := by ac_rfl
      _ = _ := by rw [spikeHeight_mul]
  rw [hparent, ← div_eq_mul_inv, ← base_cyl_succ, ENNReal.toReal_mul, ENNReal.toReal_div]
  norm_num

theorem spike_set_integral_lower [MeasurableSingletonClass X] (hbase : Measurable baseIn)
    (hatom : ∀ n, Measurable (atomIn n)) (hI : Integrable spike μ) (x : Path) (n : ℕ)
    {s : Set X} (hs : atomIn n x ∈ s) :
    (1 / 2 : ℝ) * (base (cyl x (n + 1))).toReal ≤ ∫ z in s, spike z ∂μ := by
  rw [← spike_parent_integral hbase hatom x n]
  exact setIntegral_mono_set hI.integrableOn (Filter.Eventually.of_forall spike_nonneg)
    (Filter.Eventually.of_forall (singleton_subset_iff.mpr hs))

end WithMeasure

end MSE3543357Proof

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace MSE3543357Proof

theorem mixture_subtree_real (x : Path) (n : ℕ) :
    (μ (subtree x n)).toReal = (base (cyl x n)).toReal / 2 * (1 + scale n) := by
  classical
  have ht : (∑' m : ℕ, if n ≤ m then weight m * base (cyl x n) else 0) =
      (1 / 4 : ℝ≥0∞) ^ n * base (cyl x n) := by
    calc
      _ = ∑' m : ℕ, (if n ≤ m then weight m else 0) * base (cyl x n) := by
        refine tsum_congr fun m => ?_
        split <;> simp_all
      _ = _ := by rw [ENNReal.tsum_mul_right, measure_weight_tail]
  have hb : base (cyl x n) ≠ ⊤ := measure_ne_top _ _
  have hw : (1 / 4 : ℝ≥0∞) ^ n ≠ ⊤ := by finiteness
  rw [mixture_subtree measurable_baseIn measurable_atomIn x n (isClosed_subtree x n).measurableSet, ht]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
    ENNReal.toReal_add hb (ENNReal.mul_ne_top hw hb), ENNReal.toReal_pow, scale]
  ring

theorem mixture_parent_real (x : Path) (n : ℕ) :
    (μ {atomIn n x}).toReal = (base (cyl x (n + 1))).toReal / 2 *
      (3 * (1 / 2 : ℝ) ^ (n + 1)) := by
  have hw : (weight n * (branch n : ℝ≥0∞)).toReal = 3 * (1 / 2 : ℝ) ^ (n + 1) := by
    simp only [weight, branch, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
      ENNReal.toReal_one, ENNReal.toReal_ofNat, Nat.cast_pow, Nat.cast_ofNat, mul_assoc, ← mul_pow]
    norm_num
  rw [mixture_parent measurable_baseIn measurable_atomIn x n (measurableSet_singleton _), ← base_cyl_mul x n,
    show weight n * (base (cyl x (n + 1)) * (branch n : ℝ≥0∞)) =
      (weight n * (branch n : ℝ≥0∞)) * base (cyl x (n + 1)) by ac_rfl,
    ENNReal.toReal_mul, ENNReal.toReal_mul, hw, ENNReal.toReal_div]
  norm_num
  ring

end MSE3543357Proof

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace MSE3543357Proof

theorem find_window {r : ℝ} (hr : 0 < r) (hsmall : r < 2 * scale 0) :
    ∃ n : ℕ, 2 * scale (n + 1) ≤ r ∧ r < 2 * scale n := by
  have h2 : Tendsto (fun n : ℕ => 2 * scale n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul scale_vanishes
  have hchoose : ∃ n : ℕ, 2 * scale (n + 1) ≤ r := by
    obtain ⟨n, hn⟩ := eventually_atTop.1 ((tendsto_order.1 h2).2 r hr)
    exact ⟨n, (hn (n + 1) (Nat.le_succ n)).le⟩
  refine ⟨Nat.find hchoose, Nat.find_spec hchoose, ?_⟩
  cases hn : Nat.find hchoose with
  | zero => exact hsmall
  | succ n =>
    by_contra! hfail
    exact Nat.find_min hchoose (by rw [hn]; exact Nat.lt_succ_self n) hfail

theorem squeezeByScale (D : ℝ → ℝ) (F : ℕ → ℝ)
    (hF : Tendsto F atTop (𝓝 1)) (hupper : ∀ r, D r ≤ 1)
    (hlower : ∀ r n, 2 * scale (n + 1) ≤ r → r < 2 * scale n → F n ≤ D r) :
    Tendsto D (𝓝[Set.Ioi 0] 0) (𝓝 1) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hF).1 a ha)
    have hnear : ∀ᶠ r : ℝ in 𝓝[Set.Ioi 0] 0, r < 2 * scale N :=
      (eventually_lt_nhds (show (0 : ℝ) < 2 * scale N by linarith [scale_pos N])).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hnear] with r hr hrN
    have hr0 : r < 2 * scale 0 :=
      hrN.trans_le (mul_le_mul_of_nonneg_left (scale_antitone (Nat.zero_le N)) (by norm_num))
    obtain ⟨n, hleft, hright⟩ := find_window hr hr0
    have hNn : N ≤ n := by
      by_contra! hnN
      have hh := mul_le_mul_of_nonneg_left (scale_antitone (Nat.succ_le_of_lt hnN))
        (show (0 : ℝ) ≤ 2 by norm_num)
      linarith
    exact (hN n hNn).trans_le (hlower r n hleft hright)
  · intro a ha
    exact Filter.Eventually.of_forall fun r => (hupper r).trans_lt ha

theorem ratio_lower {p q e numerator den : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (he : 0 ≤ e)
    (hnumerator : q / 2 ≤ numerator) (hden : den ≤ p / 2 * (1 + e)) (hpos : 0 < den) :
    q / p / (1 + e) ≤ numerator / den := by
  have he' : 0 < 1 + e := by linarith
  calc
    q / p / (1 + e) = (q / 2) / (p / 2 * (1 + e)) := by field_simp
    _ ≤ (q / 2) / den := div_le_div_of_nonneg_left (by positivity) hpos hden
    _ ≤ numerator / den := div_le_div_of_nonneg_right hnumerator hpos.le

noncomputable def excess (n : ℕ) : ℝ := scale (n + 1) + 3 * (1 / 2 : ℝ) ^ (n + 1)

theorem excess_nonneg (n : ℕ) : 0 ≤ excess n := by
  unfold excess scale
  positivity

theorem excess_converges : Tendsto excess atTop (𝓝 0) := by
  have h₁ := scale_vanishes.comp (tendsto_add_atTop_nat 1)
  have h₂ : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h₃ := (tendsto_const_nhds (x := (3 : ℝ))).mul (h₂.comp (tendsto_add_atTop_nat 1))
  have h := h₁.add h₃
  simp only [mul_zero, add_zero] at h
  change Tendsto (fun n => scale (n + 1) + 3 * (1 / 2 : ℝ) ^ (n + 1))
    atTop (𝓝 0)
  convert h using 1
  rfl

theorem ratioConverges {F : ℕ → ℝ} (hF : Tendsto F atTop (𝓝 1)) :
    Tendsto (fun n => F (n + 1) / (1 + excess n)) atTop (𝓝 1) := by
  have hnum : Tendsto (fun n : ℕ => F (n + 1)) atTop (𝓝 1) :=
    hF.comp (tendsto_add_atTop_nat 1)
  have hden : Tendsto (fun n : ℕ => 1 + excess n) atTop (𝓝 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).add excess_converges
  have heq :
      (fun n : ℕ => F (n + 1) / (1 + excess n)) =
        (fun n : ℕ => F (n + 1)) / (fun n : ℕ => 1 + excess n) := by
    funext n
    rfl
  rw [heq]
  simpa only [div_one] using hnum.div hden one_ne_zero

end MSE3543357Proof

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace MSE3543357Proof

theorem scale_mem_window (n : ℕ) : 2 * scale (n + 1) ≤ scale n ∧ scale n < 2 * scale n := by
  have h := scale_pos n
  rw [scale_succ]
  constructor <;> linarith

theorem base_preimage_window {x : Path} {r : ℝ} {n : ℕ}
    (h : Metric.closedBall (baseIn x) r = subtree x (n + 1) ∪
      (if scale n ≤ r then {atomIn n x} else ∅)) :
    baseIn ⁻¹' Metric.closedBall (baseIn x) r = cyl x (n + 1) := by
  rw [h]
  ext y
  have hnot : baseIn y ∉ (if scale n ≤ r then {atomIn n x} else ∅ : Set X) := by
    split_ifs
    · intro hy
      have he : baseIn y = atomIn n x := Set.mem_singleton_iff.mp hy
      change (Sum.inl y : Path ⊕ (Σ j : ℕ, Prefix j)) = Sum.inr ⟨n, takePrefix x n⟩ at he
      cases he
    · exact Set.notMem_empty (baseIn y)
  rw [Set.mem_preimage, Set.mem_union, or_iff_left hnot]
  change (∀ i < n + 1, some (y i) = some (x i)) ↔ ∀ i < n + 1, y i = x i
  simp only [Option.some.injEq]

theorem ball_mass_window (ν : Measure X) [IsFiniteMeasure ν]
    {x : Path} {n : ℕ} {r p : ℝ} (hp : 0 < p)
    (hball : Metric.closedBall (baseIn x) r = subtree x (n + 1) ∪
      (if scale n ≤ r then {atomIn n x} else ∅))
    (hsub : (ν (subtree x (n + 1))).toReal = p / 2 * (1 + scale (n + 1)))
    (hatom : (ν {atomIn n x}).toReal = p / 2 * (3 * (1 / 2 : ℝ) ^ (n + 1))) :
    p / 2 ≤ (ν (Metric.closedBall (baseIn x) r)).toReal ∧
      (ν (Metric.closedBall (baseIn x) r)).toReal ≤ p / 2 * (1 + excess n) := by
  constructor
  · calc
      p / 2 ≤ (ν (subtree x (n + 1))).toReal := by
        rw [hsub]
        nlinarith [mul_nonneg hp.le (scale_pos (n + 1)).le]
      _ ≤ (ν (Metric.closedBall (baseIn x) r)).toReal := by
        apply ENNReal.toReal_mono (measure_ne_top ν _)
        rw [hball]
        exact measure_mono subset_union_left
  · have hle : Metric.closedBall (baseIn x) r ⊆ subtree x (n + 1) ∪ {atomIn n x} := by
      rw [hball]
      by_cases h : scale n ≤ r <;> simp [h]
    have hbound := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨measure_ne_top ν _, measure_ne_top ν _⟩)
      ((measure_mono hle).trans (measure_union_le (μ := ν) _ _))
    rw [ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _), hsub, hatom] at hbound
    unfold excess
    convert hbound using 1
    ring

theorem path_density_of_bounds (ν : Measure X) [IsFiniteMeasure ν] {A : Set X} {x : Path}
    (P Q : ℕ → ℝ) (hP : ∀ n, 0 < P n) (hQ : ∀ n, 0 ≤ Q n)
    (hbase : Tendsto (fun n => Q n / P n) atTop (𝓝 1))
    (hwindow : ∀ n r, 2 * scale (n + 1) ≤ r → r < 2 * scale n →
      P (n + 1) / 2 ≤ (ν (Metric.closedBall (baseIn x) r)).toReal ∧
      (ν (Metric.closedBall (baseIn x) r)).toReal ≤ P (n + 1) / 2 * (1 + excess n) ∧
      Q (n + 1) / 2 ≤ (ν (A ∩ Metric.closedBall (baseIn x) r)).toReal) :
    Tendsto (fun r : ℝ => (ν (A ∩ Metric.closedBall (baseIn x) r)).toReal /
      (ν (Metric.closedBall (baseIn x) r)).toReal) (𝓝[Set.Ioi 0] 0) (𝓝 1) := by
  apply squeezeByScale _ _ (ratioConverges hbase)
  · intro r
    apply div_le_one_of_le₀ _ ENNReal.toReal_nonneg
    exact ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono inter_subset_right)
  · intro r n hl hr
    obtain ⟨hden₁, hden₂, hnum⟩ := hwindow n r hl hr
    exact ratio_lower (hP (n + 1)) (hQ (n + 1)) (excess_nonneg n)
      hnum hden₂ ((by linarith [hP (n + 1)] : 0 < P (n + 1) / 2).trans_le hden₁)

theorem support_base_of_window (ν : Measure X) (x : Path)
    (hwindow : ∀ n r, 2 * scale (n + 1) ≤ r → r < 2 * scale n →
      0 < ν (Metric.closedBall (baseIn x) r)) :
    ∀ r : ℝ, 0 < r → 0 < ν (Metric.closedBall (baseIn x) r) := by
  intro r hr
  let t := min r (scale 0)
  have ht : 0 < t := lt_min hr (scale_pos 0)
  have ht' : t < 2 * scale 0 := (min_le_right _ _).trans_lt (scale_mem_window 0).2
  obtain ⟨n, hl, hu⟩ := find_window ht ht'
  exact (hwindow n t hl hu).trans_le (measure_mono (Metric.closedBall_subset_closedBall (min_le_left _ _)))

end MSE3543357Proof

open Filter Set MeasureTheory Metric
open scoped Topology

namespace MSE3543357Proof

section CylinderDensity

variable {E : ℕ → Type*} [∀ i, TopologicalSpace (E i)] [∀ i, DiscreteTopology (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]

noncomputable local instance : MetricSpace (∀ i, E i) := PiNat.metricSpace

omit [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  [∀ i, SecondCountableTopology (E i)] in
private theorem cylinderAsClosedBall (x : ∀ i, E i) (n : ℕ) :
    PiNat.cylinder x n = closedBall x ((1 / 2 : ℝ) ^ n) :=
  Set.ext fun _ => PiNat.mem_cylinder_iff_dist_le

omit [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)] in
private theorem cylinderDisjointCover (μ : Measure (∀ i, E i))
    (s : Set (∀ i, E i)) (f : (∀ i, E i) → Set (Set (∀ i, E i)))
    (hf : ∀ x ∈ s, f x ⊆ Set.range (PiNat.cylinder x))
    (hsmall : ∀ x ∈ s, ∀ ε > (0 : ℝ), ∃ b ∈ f x, b ⊆ closedBall x ε) :
    ∃ t : Set ((∀ i, E i) × Set (∀ i, E i)),
      (∀ p ∈ t, p.1 ∈ s) ∧ t.PairwiseDisjoint (fun p => p.2) ∧
      (∀ p ∈ t, p.2 ∈ f p.1) ∧ μ (s \ ⋃ p ∈ t, p.2) = 0 := by
  classical
  let candidates : Set (Set (∀ i, E i)) := {b | ∃ y ∈ s, b ∈ f y}
  have existsDepth (x : s) : ∃ n, PiNat.cylinder x.1 n ∈ candidates := by
    obtain ⟨b, hb, -⟩ := hsmall x.1 x.2 1 zero_lt_one
    obtain ⟨n, rfl⟩ := hf x.1 x.2 hb
    exact ⟨n, x.1, x.2, hb⟩
  let depth (x : s) := Nat.find (existsDepth x)
  let cover (x : s) := PiNat.cylinder x.1 (depth x)
  have cover_mem (x : s) : cover x ∈ candidates := Nat.find_spec (existsDepth x)
  have witness (b : Set.range cover) : ∃ y ∈ s, b.1 ∈ f y := by
    obtain ⟨x, hx⟩ := b.2
    rw [← hx]
    exact cover_mem x
  let p (b : Set.range cover) : (∀ i, E i) × Set (∀ i, E i) :=
    ((witness b).choose, b.1)
  have p_spec (b : Set.range cover) : (p b).1 ∈ s ∧ (p b).2 ∈ f (p b).1 :=
    (witness b).choose_spec
  have depth_le {x z : s} {y : ∀ i, E i} (hx : y ∈ cover x) (hz : y ∈ cover z) :
      depth x ≤ depth z := by
    by_contra! h
    have hxy := PiNat.mem_cylinder_iff_eq.mp (PiNat.cylinder_anti x.1 h.le hx)
    have hzy := PiNat.mem_cylinder_iff_eq.mp hz
    have heq : PiNat.cylinder x.1 (depth z) = cover z := hxy.symm.trans hzy
    exact Nat.find_min (existsDepth x) h (heq.symm ▸ cover_mem z)
  refine ⟨Set.range p, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨b, rfl⟩
    exact (p_spec b).1
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne
    change Disjoint (p a).2 (p b).2
    rw [Set.disjoint_left]
    intro y hy hz
    apply hne
    apply congrArg p
    apply Subtype.ext
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨z, hz'⟩ := b.2
    change y ∈ a.1 at hy
    change y ∈ b.1 at hz
    rw [← hx] at hy ⊢
    rw [← hz'] at hz ⊢
    have hdepth := le_antisymm (depth_le hy hz) (depth_le hz hy)
    change PiNat.cylinder x.1 (depth x) = PiNat.cylinder z.1 (depth z)
    change y ∈ PiNat.cylinder z.1 (depth z) at hz
    rw [← hdepth] at hz ⊢
    exact (PiNat.mem_cylinder_iff_eq.mp hy).symm.trans
      (PiNat.mem_cylinder_iff_eq.mp hz)
  · rintro _ ⟨b, rfl⟩
    exact (p_spec b).2
  · suffices h : s ⊆ ⋃ b ∈ Set.range p, b.2 by
      rw [Set.sdiff_eq_empty.mpr h, measure_empty]
    intro x hx
    let a : Set.range cover := ⟨cover ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    exact Set.mem_iUnion₂.mpr ⟨p a, ⟨a, rfl⟩, PiNat.self_mem_cylinder _ _⟩

private def cylinderVitali (μ : Measure (∀ i, E i)) : VitaliFamily μ where
  setsAt x := Set.range (PiNat.cylinder x)
  measurableSet := by
    rintro x _ ⟨n, rfl⟩
    exact (PiNat.isOpen_cylinder E x n).measurableSet
  nonempty_interior := by
    rintro x _ ⟨n, rfl⟩
    rw [(PiNat.isOpen_cylinder E x n).interior_eq]
    exact ⟨x, PiNat.self_mem_cylinder x n⟩
  nontrivial := by
    intro x ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨_, ⟨n, rfl⟩, cylinderAsClosedBall x n ▸ closedBall_subset_closedBall hn.le⟩
  covering := cylinderDisjointCover μ

theorem cylinderDensity (μ : Measure (∀ i, E i)) [IsFiniteMeasure μ] (A : Set (∀ i, E i)) :
    ∀ᵐ x ∂μ.restrict A,
      Tendsto (fun n : ℕ => (μ (A ∩ PiNat.cylinder x n)).toReal /
        (μ (PiNat.cylinder x n)).toReal) atTop (𝓝 1) := by
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hshrinking (x : ∀ i, E i) :
      Tendsto (PiNat.cylinder x) atTop ((cylinderVitali μ).filterAt x) := by
    refine ((cylinderVitali μ).tendsto_filterAt_iff).2 ⟨.of_forall (fun n => ⟨n, rfl⟩), ?_⟩
    intro ε hε
    filter_upwards [(tendsto_order.1 hpow).2 ε hε] with n hn
    rw [cylinderAsClosedBall]
    exact closedBall_subset_closedBall hn.le
  filter_upwards [(cylinderVitali μ).ae_tendsto_measure_inter_div A] with x hx
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_one] using
    (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp (hx.comp (hshrinking x))

end CylinderDensity

/-- Finite measures differentiate their measurable sets along initial-coordinate cylinders. -/
theorem baseCylinderDensity (ν : Measure Path) [IsFiniteMeasure ν] {A : Set Path}
    (hA : MeasurableSet A) :
    ∀ᵐ x ∂ν, x ∈ A →
      Tendsto (fun n : ℕ => (ν (A ∩ cyl x n)).toReal / (ν (cyl x n)).toReal) atTop (𝓝 1) :=
  (ae_restrict_iff' hA).1 (cylinderDensity ν A)

end MSE3543357Proof

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology

namespace MSE3543357Proof

/-- An isolated point of positive mass has density one in every set that contains it. -/
theorem densityAtIsolatedPoint {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν] {A : Set Y} {x : Y} (hxA : x ∈ A)
    (hpos : ∀ r > (0 : ℝ), 0 < ν (closedBall x r))
    (hisolated : ∃ δ > (0 : ℝ), ∀ r, 0 < r → r < δ → closedBall x r = {x}) :
    Tendsto (fun r : ℝ => (ν (A ∩ closedBall x r)).toReal / (ν (closedBall x r)).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  obtain ⟨δ, hδ, hball⟩ := hisolated
  refine (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1)).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have hsingle : closedBall x r = {x} := hball r hr.1 hr.2
  have hmass : (ν ({x} : Set Y)).toReal ≠ 0 := by
    rw [← hsingle]
    exact (ENNReal.toReal_pos (hpos r hr.1).ne' (measure_ne_top _ _)).ne'
  have hA' : A ∩ ({x} : Set Y) = {x} :=
    Set.inter_eq_right.2 (Set.singleton_subset_iff.2 hxA)
  rw [hsingle, hA', div_self hmass]

/-- An almost-everywhere assertion for the base and a pointwise assertion for the atoms
give an almost-everywhere assertion for the mixture. -/
theorem ae_baseAndAtoms [MeasurableSpace X] [MeasurableSpace.CountablySeparated X]
    [MeasurableSingletonClass X]
    (hBase : Measurable baseIn) (hAtoms : ∀ n, Measurable (atomIn n)) {p : X → Prop}
    (hpBase : ∀ᵐ x ∂base, p (baseIn x)) (hpAtoms : ∀ n x, p (atomIn n x)) :
    ∀ᵐ y ∂μ, p y := by
  have hEmbed : MeasurableEmbedding baseIn :=
    hBase.measurableEmbedding (fun _ _ h => Sum.inl.inj h)
  have hMappedBase : ∀ᵐ y ∂base.map baseIn, p y := hEmbed.ae_map_iff.2 hpBase
  have hMappedAtom (n : ℕ) : ∀ᵐ y ∂base.map (atomIn n), p y := by
    have hfinite : (Set.range (atomIn n)).Finite := by
      let place : Prefix n → X := fun a => Sum.inr ⟨n, a⟩
      refine (Set.finite_range place).subset ?_
      rintro _ ⟨x, rfl⟩
      exact ⟨takePrefix x n, rfl⟩
    have hRange : ∀ᵐ y ∂base.map (atomIn n), y ∈ Set.range (atomIn n) := by
      rw [ae_iff]
      change (base.map (atomIn n)) ((Set.range (atomIn n))ᶜ) = 0
      rw [Measure.map_apply (hAtoms n) hfinite.measurableSet.compl,
        Set.preimage_compl, Set.preimage_range, Set.compl_univ, measure_empty]
    filter_upwards [hRange] with y hy
    obtain ⟨x, rfl⟩ := hy
    exact hpAtoms n x
  have hSum : ∀ᵐ y ∂Measure.sum (fun n => weight n • base.map (atomIn n)), p y :=
    Measure.ae_sum_iff.2 (fun n => Measure.ae_smul_measure (hMappedAtom n) (weight n))
  exact Measure.ae_smul_measure (ae_add_measure_iff.2 ⟨hMappedBase, hSum⟩) (1 / 2 : ℝ≥0∞)

theorem densityFromBase [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsFiniteMeasure μ]
    (hBase : Measurable baseIn) (hAtoms : ∀ n, Measurable (atomIn n))
    (hIso : ∀ n x, ∃ δ > (0 : ℝ), ∀ r, 0 < r → r < δ →
      closedBall (atomIn n x) r = {atomIn n x})
    {A S : Set X} (hSupport : ∀ z ∈ S, ∀ r > (0 : ℝ), 0 < μ (closedBall z r))
    (hBaseDensity : ∀ᵐ x ∂base, baseIn x ∈ A ∩ S →
      Tendsto (fun r : ℝ => (μ (A ∩ closedBall (baseIn x) r)).toReal /
        (μ (closedBall (baseIn x) r)).toReal) (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    ∀ᵐ z ∂μ, z ∈ A ∩ S →
      Tendsto (fun r : ℝ => (μ (A ∩ closedBall z r)).toReal /
        (μ (closedBall z r)).toReal) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
  ae_baseAndAtoms hBase hAtoms hBaseDensity (fun n x hx =>
    densityAtIsolatedPoint μ hx.1 (hSupport _ hx.2) (hIso n x))

end MSE3543357Proof

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology

namespace MSE3543357Proof

theorem scaleTendstoRight : Tendsto scale atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · change 0 < (1 / 4 : ℝ) ^ n
    positivity

theorem notDifferentiatesOnSupport [MetricSpace X] [MeasurableSpace X]
    [MeasurableSpace.CountablySeparated X] [IsProbabilityMeasure base]
    (hBase : Measurable baseIn) {S : Set X} {f : X → ℝ} {c : ℝ} (hc : 0 < c)
    (hSupport : ∀ x, baseIn x ∈ S) (hZero : ∀ x, f (baseIn x) = 0)
    (hLower : ∀ x n, c ≤
      ((μ (closedBall (baseIn x) (scale n))).toReal)⁻¹ *
        ∫ y in closedBall (baseIn x) (scale n), f y ∂μ) :
    ¬ (∀ᵐ z ∂μ, z ∈ S → Tendsto
      (fun r : ℝ => ((μ (closedBall z r)).toReal)⁻¹ * ∫ y in closedBall z r, f y ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (f z))) := by
  intro h
  have hEmbed : MeasurableEmbedding baseIn :=
    hBase.measurableEmbedding (fun _ _ hEq => Sum.inl.inj hEq)
  have hComponents := (Measure.ae_ennreal_smul_measure_iff
    (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)).1 h
  have hp := hEmbed.ae_map_iff.1 (ae_add_measure_iff.1 hComponents).1
  obtain ⟨x, hx⟩ := hp.exists
  have hxLimit := (hx (hSupport x)).comp scaleTendstoRight
  have hle : c ≤ f (baseIn x) := ge_of_tendsto hxLimit
    (Filter.Eventually.of_forall (hLower x))
  rw [hZero x] at hle
  exact hc.not_ge hle

end MSE3543357Proof

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace MSE3543357Proof

instance mixtureProbability : IsProbabilityMeasure μ :=
  mixture_probability measurable_baseIn measurable_atomIn

theorem cylinder_real_pos (x : Path) (n : ℕ) : 0 < (base (cyl x n)).toReal :=
  ENNReal.toReal_pos (base_cyl_pos x n).ne' (measure_ne_top base _)

theorem mixture_lower_toReal {A : Set X} (hA : MeasurableSet A) :
    (base (baseIn ⁻¹' A)).toReal / 2 ≤ (μ A).toReal := by
  have h : (1 / 2 : ℝ≥0∞) * base (baseIn ⁻¹' A) ≤ μ A := by
    rw [mixture_apply measurable_baseIn measurable_atomIn hA]
    gcongr
    exact le_self_add
  have hh := ENNReal.toReal_mono (measure_ne_top μ A) h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_div, div_eq_mul_inv, mul_comm] using hh

theorem mixture_ball_real (x : Path) (n : ℕ) {r : ℝ}
    (hl : 2 * scale (n + 1) ≤ r) (hr : r < 2 * scale n) :
    (base (cyl x (n + 1))).toReal / 2 ≤ (μ (Metric.closedBall (baseIn x) r)).toReal ∧
    (μ (Metric.closedBall (baseIn x) r)).toReal ≤
      (base (cyl x (n + 1))).toReal / 2 * (1 + excess n) := by
  apply ball_mass_window μ (cylinder_real_pos x (n + 1)) (closedBall_baseIn x n hl hr)
  · exact mixture_subtree_real x (n + 1)
  · exact mixture_parent_real x n

def supported : Set X := {x | ∀ r : ℝ, 0 < r → 0 < μ (Metric.closedBall x r)}

theorem base_supported (x : Path) : baseIn x ∈ supported := by
  apply support_base_of_window μ x
  intro n r hl hr
  have h := (show 0 < (base (cyl x (n + 1))).toReal / 2 by
    linarith [cylinder_real_pos x (n + 1)]).trans_le (mixture_ball_real x n hl hr).1
  by_contra! hn
  have hz : μ (Metric.closedBall (baseIn x) r) = 0 := le_antisymm hn zero_le
  simp [hz] at h

theorem atom_isolated (n : ℕ) (x : Path) : ∃ δ > (0 : ℝ), ∀ r, 0 < r → r < δ →
    Metric.closedBall (atomIn n x) r = {atomIn n x} := by
  refine ⟨scale n, scale_pos n, fun r hr hlt => Subset.antisymm ?_ ?_⟩
  · rw [← ball_atomIn n x]
    exact Metric.closedBall_subset_ball hlt
  · exact singleton_subset_iff.2 (Metric.mem_closedBall_self hr.le)

theorem mixture_density (A : Set X) (hA : MeasurableSet A) :
    ∀ᵐ z ∂μ, z ∈ A ∩ supported → Tendsto
      (fun r : ℝ => (μ (A ∩ Metric.closedBall z r)).toReal /
        (μ (Metric.closedBall z r)).toReal) (𝓝[Set.Ioi 0] 0) (𝓝 1) := by
  apply densityFromBase measurable_baseIn measurable_atomIn atom_isolated
    (S := supported) (fun _ hx => hx)
  have hDensity := baseCylinderDensity base (hA.preimage measurable_baseIn)
  filter_upwards [hDensity] with x hx hmem
  apply path_density_of_bounds μ (fun n => (base (cyl x n)).toReal)
    (fun n => (base (baseIn ⁻¹' A ∩ cyl x n)).toReal) (cylinder_real_pos x)
    (fun _ => ENNReal.toReal_nonneg) (hx hmem.1)
  intro n r hl hr
  have h := mixture_ball_real x n hl hr
  refine ⟨h.1, h.2, ?_⟩
  have hBall : MeasurableSet (Metric.closedBall (baseIn x) r) :=
    Metric.isClosed_closedBall.measurableSet
  have hu := mixture_lower_toReal (hA.inter hBall)
  rw [preimage_inter, base_preimage_window (closedBall_baseIn x n hl hr)] at hu
  exact hu

theorem mixture_spike_integrable : Integrable spike μ :=
  spike_integrable measurable_baseIn measurable_atomIn measurable_spike

theorem excess_le_four (n : ℕ) : excess n ≤ 4 := by
  have h₁ : scale (n + 1) ≤ 1 := by
    simpa [scale] using scale_antitone (Nat.zero_le (n + 1))
  have h₂ : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 := by
    simpa using pow_right_anti₀ (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (show (1 / 2 : ℝ) ≤ 1 by norm_num) (Nat.zero_le (n + 1))
  dsimp [excess]
  linarith

theorem spike_average_lower (x : Path) (n : ℕ) : (1 / 6 : ℝ) ≤
    ((μ (Metric.closedBall (baseIn x) (scale n))).toReal)⁻¹ *
      ∫ z in Metric.closedBall (baseIn x) (scale n), spike z ∂μ := by
  have hw := scale_mem_window n
  have hd := mixture_ball_real x n hw.1 hw.2
  have hm : atomIn n x ∈ Metric.closedBall (baseIn x) (scale n) := by
    rw [closedBall_baseIn x n hw.1 hw.2]
    simp
  have hN := spike_set_integral_lower measurable_baseIn measurable_atomIn
    mixture_spike_integrable x n hm
  have hNum : (base (cyl x (n + 1))).toReal / 2 ≤
      ∫ z in Metric.closedBall (baseIn x) (scale n), spike z ∂μ := by
    simpa [div_eq_mul_inv, mul_comm] using hN
  have hp := cylinder_real_pos x (n + 1)
  have hdpos := (show 0 < (base (cyl x (n + 1))).toReal / 2 by linarith).trans_le hd.1
  have hh := ratio_lower hp hp.le (excess_nonneg n) hNum hd.2 hdpos
  have hk : (1 / 6 : ℝ) ≤ 1 / (1 + excess n) := by
    apply (le_div_iff₀ (show 0 < 1 + excess n by linarith [excess_nonneg n])).2
    linarith [excess_le_four n]
  rw [div_self hp.ne'] at hh
  simpa [div_eq_mul_inv, mul_comm] using hk.trans hh

end MSE3543357Proof

open MSE3543357Proof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_3543357.main) := by
  intro h
  have hdiff := h X μ mixture_density spike mixture_spike_integrable
  exact notDifferentiatesOnSupport measurable_baseIn (by norm_num : (0 : ℝ) < 1 / 6)
    base_supported spike_base spike_average_lower hdiff
