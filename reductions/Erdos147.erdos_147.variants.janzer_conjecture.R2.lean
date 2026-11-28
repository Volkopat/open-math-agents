import FormalConjectures.ErdosProblems.«147»

-- Reduction Erdos147.erdos_147.variants.janzer_conjecture.R2 of Erdős Problem 147 — janzer conjecture
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Proved here: every even r, and every odd r with ε > 2/(r(r+1)) (cycle blow-ups and their
-- matching-deleted subgraphs). Left open: H1 the cubic case r = 3, H2 odd r ≥ 5 with small ε.

open Filter Asymptotics SimpleGraph Finset
open scoped Classical

namespace OMA.R_Erdos147_erdos_147_variants_janzer_conjecture_R2

theorem pathWeight_spec : ∃ pw : ∀ {V : Type}, Matrix V V ℝ → (n : ℕ) → V → (Fin n → V) → V → ℝ,
    (∀ (V : Type) (M : Matrix V V ℝ) (a : V) (x : Fin 0 → V) (b : V), pw M 0 a x b = M a b) ∧
    (∀ (V : Type) (M : Matrix V V ℝ) (n : ℕ) (a : V) (x : Fin (n + 1) → V) (b : V),
      pw M (n + 1) a x b = M a (x 0) * pw M n (x 0) (Fin.tail x) b) :=
  ⟨fun {V} M n => Nat.rec (motive := fun n => V → (Fin n → V) → V → ℝ) (fun a _ b => M a b)
    (fun n ih a x b => M a (x 0) * ih (x 0) (Fin.tail x) b) n,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

theorem pw_zero {V : Type} (M : Matrix V V ℝ) (a : V) (x : Fin 0 → V) (b : V) :
    (Classical.choose pathWeight_spec) M 0 a x b = M a b :=
  (Classical.choose_spec pathWeight_spec).1 V M a x b

theorem pw_succ {V : Type} (M : Matrix V V ℝ) (n : ℕ) (a : V) (x : Fin (n + 1) → V) (b : V) :
    (Classical.choose pathWeight_spec) M (n + 1) a x b =
      M a (x 0) * (Classical.choose pathWeight_spec) M n (x 0) (Fin.tail x) b :=
  (Classical.choose_spec pathWeight_spec).2 V M n a x b

theorem closedWeight_spec : ∃ cw : ∀ {V : Type}, Matrix V V ℝ → ∀ {n : ℕ}, (Fin (n + 1) → V) → ℝ,
    ∀ (V : Type) (M : Matrix V V ℝ) (n : ℕ) (x : Fin (n + 1) → V),
      cw M x = (Classical.choose pathWeight_spec) M n (x 0) (Fin.tail x) (x 0) :=
  ⟨fun M _ x => (Classical.choose pathWeight_spec) M _ (x 0) (Fin.tail x) (x 0),
    fun _ _ _ _ => rfl⟩

theorem cw_eq {V : Type} (M : Matrix V V ℝ) {n : ℕ} (x : Fin (n + 1) → V) :
    (Classical.choose closedWeight_spec) M x =
      (Classical.choose pathWeight_spec) M n (x 0) (Fin.tail x) (x 0) :=
  Classical.choose_spec closedWeight_spec V M n x

theorem extremal_of_degree_threshold {W : Type} (H : SimpleGraph W) {a C : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C)
    (force : ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
      (∀ v, C * (Fintype.card V : ℝ) ^ a < (G.degree v : ℝ)) → H ⊑ G) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (a + 1) := by
  classical
  rw [isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have bound : ∀ (m : ℕ) (V : Type) [Fintype V], Fintype.card V = m → m ≤ n →
      ∀ (G : SimpleGraph V), H.Free G →
        (G.edgeFinset.card : ℝ) ≤ (m : ℝ) * (C * (n : ℝ) ^ a) := by
    intro m
    induction m with
    | zero =>
      intro V _ hV _ G _
      have : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
      have : G = ⊥ := Subsingleton.elim _ _
      simp [this]
    | succ m ih =>
      intro V _ hV hmn G hfree
      have : Nonempty V := Fintype.card_pos_iff.mp (hV.symm ▸ m.succ_pos)
      obtain ⟨v, hv⟩ : ∃ v, (G.degree v : ℝ) ≤ C * (n : ℝ) ^ a := by
        by_contra! hf
        apply hfree (force V G ?_)
        intro v
        have hc : (Fintype.card V : ℝ) ≤ n := by exact_mod_cast (hV.trans_le hmn)
        exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hc ha) hC).trans_lt (hf v)
      let T : Set V := {v}ᶜ
      have hT : Fintype.card T = m := by
        change Fintype.card (({v} : Set V)ᶜ : Set V) = m
        rw [Fintype.card_compl_set, hV, @Fintype.card_unique ({v} : Set V), Nat.add_sub_cancel]
      have hfreeT : H.Free (G.induce T) := fun hc => hfree (hc.trans ⟨Copy.induce G T⟩)
      have hrest := ih T hT (by omega) (G.induce T) hfreeT
      have hsplit : (G.induce T).edgeFinset.card + G.degree v = G.edgeFinset.card := by
        simp only [T, card_edgeFinset_induce_compl_singleton, card_edgeFinset_deleteIncidenceSet]
        exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)
      have hsplitR : ((G.induce T).edgeFinset.card : ℝ) + G.degree v = G.edgeFinset.card := by
        exact_mod_cast hsplit
      rw [← hsplitR, Nat.cast_succ, add_mul, one_mul]
      exact add_le_add hrest hv
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.rpow_nonneg hnR.le _)]
  have hrewrite : C * (n : ℝ) ^ (a + 1) = (n : ℝ) * (C * (n : ℝ) ^ a) := by
    rw [Real.rpow_add hnR, Real.rpow_one]
    ring
  rw [hrewrite, ← Fintype.card_fin n]
  apply (extremalNumber_le_iff_of_nonneg (V := Fin n) H (by positivity)).2
  intro G _ hfree
  have h := bound n (Fin n) (Fintype.card_fin n) le_rfl G hfree
  rw [Fintype.card_fin]
  convert! h


theorem mem_packedTuples {E : Type} [Fintype E] {s : Finset E}
    {conflict : E → E → Prop} {t : ℕ} {x : Fin t → E} :
    x ∈ ((Fintype.piFinset (fun _ : Fin t => s)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p)) ↔ (∀ i, x i ∈ s) ∧
       (∀ i j, i < j → ¬ conflict (x i) (x j)) := by
  classical
  simp []

theorem sigma_subtype_ext {A B : Type} {P : A → B → Prop}
    {x y : Σ a : A, {b : B // P a b}} (h : x.1 = y.1) (h' : x.2.val = y.2.val) :
    x = y := by
  rcases x with ⟨x, ⟨a, ha⟩⟩
  rcases y with ⟨y, ⟨b, hb⟩⟩
  change x = y at h
  change a = b at h'
  subst y
  subst b
  rfl

theorem card_packedTuples_succ {E : Type} [Fintype E] (s : Finset E)
    (conflict : E → E → Prop) (t : ℕ) :
    (((Fintype.piFinset (fun _ : Fin (t + 1) => s)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p))).card =
      ∑ x ∈ ((Fintype.piFinset (fun _ : Fin t => s)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p)), ((s.filter fun a_c => ∀ i_c, ¬ conflict a_c (x i_c))).card := by
  classical
  let long := ↥(((Fintype.piFinset (fun _ : Fin (t + 1) => s)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p)))
  let short := ↥(((Fintype.piFinset (fun _ : Fin t => s)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p)))
  let e : long ≃ Σ x : short, ↥((s.filter fun a_c => ∀ i_c, ¬ conflict a_c (x.val i_c))) := by
    refine {
      toFun := fun x => ⟨⟨Fin.tail x.val, ?_⟩, ⟨x.val 0, ?_⟩⟩
      invFun := fun y => ⟨Fin.cons y.2.val y.1.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
    · have h := mem_packedTuples.mp x.prop
      exact mem_packedTuples.mpr
        ⟨fun i => h.1 i.succ, fun i j hij => h.2 i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)⟩
    · have h := mem_packedTuples.mp x.prop
      apply mem_filter.mpr
      exact ⟨h.1 0, fun i => h.2 0 i.succ (Fin.succ_pos i)⟩
    · have hx := mem_packedTuples.mp y.1.prop
      have hy := mem_filter.mp y.2.prop
      apply mem_packedTuples.mpr
      constructor
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hy.1
        · simpa using hx.1 j
      · intro i j hij
        revert hij
        refine Fin.cases (fun j hj => ?_) (fun i j hj => ?_) i j
        · revert hj
          refine Fin.cases ?_ (fun j hj => ?_) j
          · simp
          · simpa using hy.2 j
        · revert hj
          refine Fin.cases ?_ (fun j hj => ?_) j
          · simp
          · simpa using hx.2 i j (Fin.succ_lt_succ_iff.mp hj)
    · intro x
      apply Subtype.ext
      simp
    · rintro ⟨x, a⟩
      apply sigma_subtype_ext
      · apply Subtype.ext
        simp
      · simp
  have hc := Fintype.card_congr e
  rw [Fintype.card_coe, Fintype.card_sigma] at hc
  calc
    _ = ∑ x : short, ((s.filter fun a_c => ∀ i_c, ¬ conflict a_c (x.val i_c))).card := by
      simpa only [Fintype.card_coe] using hc
    _ = _ := by
      convert Finset.sum_coe_sort (((Fintype.piFinset (fun _ : Fin t => s)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p)))
        (fun (x : Fin t → E) => ((s.filter fun a_c => ∀ i_c, ¬ conflict a_c (x i_c))).card) using 0


theorem card_packedTuples_lower {E : Type} [Fintype E] (s : Finset E)
    (conflict : E → E → Prop) (B t : ℕ)
    (hB : ∀ b ∈ s, (s.filter fun a => conflict a b).card ≤ B) :
    (s.card - t * B) ^ t ≤ (((Fintype.piFinset (fun _ : Fin t => s)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p))).card := by
  classical
  induction t with
  | zero =>
    simp []
  | succ t ih =>
    let lower := s.card - (t + 1) * B
    have hshift : lower ≤ s.card - t * B := by
      dsimp [lower]
      exact Nat.sub_le_sub_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
    have hheads (x : Fin t → E) (hx : x ∈ ((Fintype.piFinset (fun _ : Fin t => s)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p))) :
        lower ≤ ((s.filter fun a_c => ∀ i_c, ¬ conflict a_c (x i_c))).card := by
      have hxs := (mem_packedTuples.mp hx).1
      let bad := (univ : Finset (Fin t)).biUnion (fun i => s.filter fun a => conflict a (x i))
      have hbad : bad.card ≤ t * B := by
        apply card_biUnion_le.trans
        calc
          _ ≤ ∑ _i : Fin t, B := sum_le_sum fun i _ => hB _ (hxs i)
          _ = _ := by simp
      have hbadId : bad = s.filter (fun a => ¬ ∀ i, ¬ conflict a (x i)) := by
        ext a
        simp [bad, mem_biUnion, mem_filter, exists_and_left]
      have hsplit : ((s.filter fun a_c => ∀ i_c, ¬ conflict a_c (x i_c))).card + bad.card = s.card := by
        rw [hbadId, card_filter_add_card_filter_not]
      dsimp [lower]
      omega
    rw [card_packedTuples_succ, pow_succ]
    calc
      lower ^ t * lower ≤ (((Fintype.piFinset (fun _ : Fin t => s)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p))).card * lower :=
        Nat.mul_le_mul_right _ ((Nat.pow_le_pow_left hshift t).trans ih)
      _ = ∑ _x ∈ ((Fintype.piFinset (fun _ : Fin t => s)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p)), lower := by simp
      _ ≤ _ := sum_le_sum hheads


theorem sum_card_packed_neighborhoods {E : Type} [Fintype E]
    (s : Finset E) (R conflict : E → E → Prop) (t : ℕ) :
    (∑ e ∈ s, (((Fintype.piFinset (fun _ : Fin t => (s.filter fun f => R f e))).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p))).card) =
      ∑ x ∈ ((Fintype.piFinset (fun _ : Fin t => s)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p)), (s.filter fun e => ∀ i, R (x i) e).card := by
  classical
  let P := ((Fintype.piFinset (fun _ : Fin t => s)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p))
  have hfilter (e : E) : ((Fintype.piFinset (fun _ : Fin t => (s.filter fun f => R f e))).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p)) =
      P.filter fun x => ∀ i, R (x i) e := by
    ext x
    simp only [P, mem_packedTuples, Fintype.mem_piFinset, mem_filter]
    constructor
    · rintro ⟨hm, hc⟩
      exact ⟨⟨fun i => (hm i).1, hc⟩, fun i => (hm i).2⟩
    · rintro ⟨⟨hm, hc⟩, hr⟩
      exact ⟨fun i => ⟨hm i, hr i⟩, hc⟩
  calc
    _ = ∑ e ∈ s, ∑ x ∈ P, if ∀ i, R (x i) e then 1 else 0 := by
      apply sum_congr rfl
      intro e _
      rw [hfilter, card_filter]
    _ = ∑ x ∈ P, ∑ e ∈ s, if ∀ i, R (x i) e then 1 else 0 := sum_comm
    _ = _ := by simp only [card_filter, P]

theorem power_mean_le {I : Type} (T : Finset I) (hT : T.Nonempty)
    (f : I → ℝ) (hf : ∀ i ∈ T, 0 ≤ f i) (t : ℕ) :
    (T.card : ℝ) * ((∑ i ∈ T, f i) / T.card) ^ t ≤ ∑ i ∈ T, f i ^ t := by
  let k : ℝ := T.card
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast hT.card_pos
  let w : I → ℝ := fun _ => k⁻¹
  have hw : ∑ i ∈ T, w i = 1 := by
    simp only [w, sum_const, nsmul_eq_mul]
    change k * k⁻¹ = 1
    exact mul_inv_cancel₀ hk.ne'
  have h := (convexOn_pow (𝕜 := ℝ) t).map_sum_le (t := T)
    (w := w) (p := f) (fun _ _ => inv_nonneg.mpr hk.le) hw hf
  simp only [w, smul_eq_mul, ← mul_sum] at h
  rw [← div_eq_inv_mul, ← div_eq_inv_mul] at h
  simpa only [mul_comm _ k] using (le_div_iff₀ hk).mp h


theorem sum_card_packed_lower {I E : Type} [Fintype E] (T : Finset I) (hT : T.Nonempty)
    (s : I → Finset E) (conflict : E → E → Prop) (B t : ℕ) (d : ℝ)
    (hd : (t : ℝ) * B ≤ d)
    (hmean : (T.card : ℝ) * d ≤ ∑ i ∈ T, ((s i).card : ℝ))
    (hB : ∀ i ∈ T, ∀ b ∈ s i, ((s i).filter fun a => conflict a b).card ≤ B) :
    (T.card : ℝ) * (d - (t : ℝ) * B) ^ t ≤
      ∑ i ∈ T, ((((Fintype.piFinset (fun _ : Fin t => (s i))).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p))).card : ℝ) := by
  let f : I → ℝ := fun i => ↑((s i).card - t * B)
  have hTpos : 0 < (T.card : ℝ) := by exact_mod_cast hT.card_pos
  have hf (i : I) : (s i).card - (t : ℝ) * B ≤ f i := by
    dsimp [f]
    rw [← Nat.cast_mul]
    by_cases h : t * B ≤ (s i).card
    · rw [Nat.cast_sub h]
    · rw [Nat.sub_eq_zero_of_le (le_of_not_ge h), Nat.cast_zero]
      exact sub_nonpos.mpr (by exact_mod_cast le_of_not_ge h)
  have hsum := sum_le_sum (fun i hi => hf i : ∀ i ∈ T, _)
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul] at hsum
  have hmean' : d - (t : ℝ) * B ≤ (∑ i ∈ T, f i) / T.card := by
    apply (le_div_iff₀ hTpos).2
    linarith only [hsum, hmean]
  calc
    _ ≤ (T.card : ℝ) * ((∑ i ∈ T, f i) / T.card) ^ t :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sub_nonneg.mpr hd) hmean' t) hTpos.le
    _ ≤ ∑ i ∈ T, f i ^ t := power_mean_le T hT f (fun _ _ => by positivity) t
    _ ≤ _ := by
      apply sum_le_sum
      intro i hi
      dsimp [f]
      exact_mod_cast card_packedTuples_lower (s i) conflict B t (hB i hi)


theorem card_packedTuples_filter_hit_le {E : Type} [Fintype E] (s : Finset E)
    (conflict : E → E → Prop) (t : ℕ) (P : E → Prop) :
    ((((Fintype.piFinset (fun _ : Fin t => s)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p))).filter fun x => ∃ i, P (x i)).card ≤
      t * (s.filter P).card * s.card ^ (t - 1) := by
  classical
  let U (i : Fin t) := Fintype.piFinset (Function.update (fun _ : Fin t => s) i (s.filter P))
  have hsub : (((Fintype.piFinset (fun _ : Fin t => s)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p))).filter (fun x => ∃ i, P (x i)) ⊆ univ.biUnion U := by
    intro x hx
    obtain ⟨hx, i, hi⟩ := mem_filter.mp hx
    have hxs := (mem_packedTuples.mp hx).1
    refine mem_biUnion.mpr ⟨i, mem_univ i, Fintype.mem_piFinset.mpr fun j => ?_⟩
    obtain rfl | hji := eq_or_ne j i
    · simp [hxs, hi]
    · simp [Function.update_of_ne hji, hxs]
  have hcard (i : Fin t) : (U i).card = (s.filter P).card * s.card ^ (t - 1) := by
    dsimp [U]
    rw [Fintype.card_piFinset]
    calc
      _ = ∏ j : Fin t, Function.update (fun _ : Fin t => s.card) i (s.filter P).card j := by
        apply Fintype.prod_congr
        intro j
        obtain rfl | hji := eq_or_ne j i <;> simp [*]
      _ = _ := by
        rw [prod_update_of_mem (mem_univ i)]
        simp only [sdiff_singleton_eq_erase, prod_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  calc
    _ ≤ (univ.biUnion U).card := card_le_card hsub
    _ ≤ ∑ i : Fin t, (U i).card := card_biUnion_le
    _ = _ := by simp [hcard, mul_assoc]


theorem exists_degree_core {E : Type} (S : Finset E) (R : E → E → Prop) (w : E → ℝ)
    (hsym : ∀ ⦃x y⦄, R x y → R y x) (hirr : ∀ x, ¬ R x x)
    (hdense : 2 * ∑ x ∈ S, w x < ∑ x ∈ S, ((S.filter (R x)).card : ℝ)) :
    ∃ T ⊆ S, T.Nonempty ∧ ∀ x ∈ T, w x ≤ ((T.filter (R x)).card : ℝ) := by
  classical
  let d (T : Finset E) (x : E) : ℝ := ∑ y ∈ T, if R x y then 1 else 0
  have hd (T : Finset E) (x : E) : d T x = (T.filter (R x)).card := by
    simp only [d, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  let score (T : Finset E) := (∑ x ∈ T, d T x) - 2 * ∑ x ∈ T, w x
  obtain ⟨T, hTS, hmax⟩ := exists_max_image S.powerset score
    ⟨∅, mem_powerset.mpr (empty_subset _)⟩
  have hsub := mem_powerset.mp hTS
  have hpos : 0 < score T := by
    apply lt_of_lt_of_le _ (hmax S (mem_powerset.mpr le_rfl))
    dsimp [score]
    simp_rw [hd]
    linarith only [hdense]
  have hne : T.Nonempty := by
    by_contra! h
    simp [score, h] at hpos
  refine ⟨T, hsub, hne, ?_⟩
  intro x hx
  let U := T.erase x
  have hUS : U ∈ S.powerset := mem_powerset.mpr ((erase_subset x T).trans hsub)
  have hw : ∑ y ∈ U, w y = (∑ y ∈ T, w y) - w x := by
    exact eq_sub_of_add_eq (sum_erase_add _ _ hx)
  have hds (y : E) : d T y = d U y + (if R y x then 1 else 0) := by
    exact (sum_erase_add _ _ hx).symm
  have hflip : (∑ y ∈ U, if R y x then (1 : ℝ) else 0) = d T x := by
    calc
      _ = d U x := by
        apply sum_congr rfl
        intro y _
        have hiff : R y x ↔ R x y := ⟨fun h => hsym h, fun h => hsym h⟩
        rw [hiff]
      _ = d T x := by simpa [hirr x] using (hds x).symm
  have hdsum : (∑ y ∈ U, d T y) = (∑ y ∈ U, d U y) + d T x := by
    rw [← hflip, ← sum_add_distrib]
    exact sum_congr rfl (fun y _ => hds y)
  have hsum : ∑ y ∈ T, d T y = (∑ y ∈ U, d U y) + 2 * d T x := by
    calc
      _ = (∑ y ∈ U, d T y) + d T x := (sum_erase_add _ _ hx).symm
      _ = _ := by rw [hdsum]; ring
  have hless := hmax U hUS
  change (∑ y ∈ U, d U y) - 2 * ∑ y ∈ U, w y ≤
    (∑ y ∈ T, d T y) - 2 * ∑ y ∈ T, w y at hless
  rw [hw, hsum] at hless
  rw [← hd]
  linarith only [hless]


theorem packed_size_le {E : Type} [Fintype E] (s : Finset E)
    (conflict : E → E → Prop) (t : ℕ) :
    (((Fintype.piFinset (fun _ : Fin t => s)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ conflict (x_p i_p) (x_p j_p))).card ≤ s.card ^ t := by
  classical
  refine (card_filter_le _ _).trans ?_
  rw [Fintype.card_piFinset_const]


theorem exists_sparse_tuple_core {E : Type} [Fintype E]
    (C : E → E → Prop) (t L θ : ℕ) (ht : 0 < t) (hθ : 0 < θ) (hθL : 4 * t * L ≤ θ)
    (Q : (Fin t → E) → (Fin t → E) → Prop) (common : (Fin t → E) → Finset E)
    (hsym : ∀ ⦃x y⦄, Q x y → Q y x) (hirr : ∀ x, ¬ Q x x)
    (hneighbor : ∀ x, (((Fintype.piFinset (fun _ : Fin t => univ)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ C (x_p i_p) (x_p j_p))).filter (Q x) = ((Fintype.piFinset (fun _ : Fin t => (common x))).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ C (x_p i_p) (x_p j_p)))
    (hcap : ∀ x ∈ ((Fintype.piFinset (fun _ : Fin t => univ)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ C (x_p i_p) (x_p j_p)), ∀ f, ((common x).filter fun e => C e f).card ≤ 2 * L)
    (hsum : let P := ((Fintype.piFinset (fun _ : Fin t => (univ : Finset E))).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ C (x_p i_p) (x_p j_p))
      4 * (P.card : ℝ) * ((θ : ℝ) ^ t + 1) <
        ∑ x ∈ P, ((((Fintype.piFinset (fun _ : Fin t => (common x))).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ C (x_p i_p) (x_p j_p))).card : ℝ)) :
    ∃ U : Finset (Fin t → E), U ⊆ ((Fintype.piFinset (fun _ : Fin t => univ)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ C (x_p i_p) (x_p j_p)) ∧ U.Nonempty ∧
      ∀ x ∈ U, 0 < (U.filter (Q x)).card ∧
        ∀ f : Fin t → E, θ * (U.filter fun y => Q x y ∧ (∃ i_o j_o, C (y j_o) (f i_o))).card ≤
          (8 * 2 ^ t * t ^ 2 * L) * (U.filter (Q x)).card := by
  classical
  let P := ((Fintype.piFinset (fun _ : Fin t => (univ : Finset (E)))).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ C (x_p i_p) (x_p j_p))
  let D (x : Fin t → E) := (P.filter (Q x)).card
  have hD (x : Fin t → E) : D x =
      (((Fintype.piFinset (fun _ : Fin t => (common x))).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ C (x_p i_p) (x_p j_p))).card :=
    congrArg Finset.card (hneighbor x)
  let M (x : Fin t → E) := (common x).card
  let w (x : Fin t → E) : ℝ :=
    if θ ≤ M x then (D x : ℝ) / 4 else (D x : ℝ) + 1
  have hw (x : Fin t → E) :
      w x ≤ (D x : ℝ) / 4 + ((θ : ℝ) ^ t + 1) := by
    unfold w
    split_ifs with hx
    · exact le_add_of_nonneg_right (by positivity)
    · have hD' : (D x : ℝ) ≤ (θ : ℝ) ^ t := by
        have h := (hD x).le.trans (packed_size_le (common x) C t)
        exact_mod_cast h.trans (Nat.pow_le_pow_left (le_of_lt (lt_of_not_ge hx)) _)
      have hnonneg : 0 ≤ (D x : ℝ) / 4 := by positivity
      linarith only [hD', hnonneg]
  have hsum' : 4 * (P.card : ℝ) * ((θ : ℝ) ^ t + 1) < ∑ x ∈ P, (D x : ℝ) := by
    simpa only [hD] using hsum
  have hds : 2 * ∑ x ∈ P, w x < ∑ x ∈ P, (D x : ℝ) := by
    have h := sum_le_sum (fun x (_ : x ∈ P) => hw x)
    rw [sum_add_distrib, ← sum_div, sum_const, nsmul_eq_mul] at h
    linarith only [hsum', h]
  obtain ⟨U, hUP, hUne, hU⟩ := exists_degree_core P Q w hsym hirr hds
  refine ⟨U, hUP, hUne, fun x hx => ?_⟩
  let deg := (U.filter (Q x)).card
  have hless : deg ≤ D x := card_le_card (filter_subset_filter _ hUP)
  have hlarge : θ ≤ M x := by
    by_contra! hn
    have h := hU x hx
    change w x ≤ (deg : ℝ) at h
    rw [show w x = (D x : ℝ) + 1 by simp only [w, if_neg (not_le.mpr hn)]] at h
    have h' : (deg : ℝ) ≤ D x := by exact_mod_cast hless
    linarith only [h, h']
  have hquarter : D x ≤ 4 * deg := by
    have h := hU x hx
    change w x ≤ (deg : ℝ) at h
    simp only [w, if_pos hlarge] at h
    exact_mod_cast (show (D x : ℝ) ≤ 4 * deg by linarith only [h])
  let S := common x
  have hBc (f : E) : (S.filter fun e => C e f).card ≤ 2 * L :=
    hcap x (hUP hx) f
  have hfull : (M x - t * (2 * L)) ^ t ≤ D x := by
    rw [hD]
    exact card_packedTuples_lower S C (2 * L) t (fun b _ => hBc b)
  have hshift : M x ≤ 2 * (M x - t * (2 * L)) := by
    have hm : 2 * (t * (2 * L)) ≤ M x := by
      calc
        _ = 4 * t * L := by ring
        _ ≤ _ := hθL.trans hlarge
    omega
  have hpower : (M x) ^ t ≤ 2 ^ t * D x := by
    calc
      _ ≤ (2 * (M x - t * (2 * L))) ^ t := Nat.pow_le_pow_left hshift _
      _ = _ := mul_pow _ _ _
      _ ≤ _ := Nat.mul_le_mul_left _ hfull
  have hpos : 0 < deg := by
    have hm : 0 < (M x) ^ t := Nat.pow_pos (hθ.trans_le hlarge)
    by_contra! hz
    have : D x = 0 := by omega
    simp [this] at hpower
    omega
  refine ⟨hpos, fun f => ?_⟩
  let hits (i : Fin t) := (((Fintype.piFinset (fun _ : Fin t => S)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ C (x_p i_p) (x_p j_p))).filter fun y => ∃ j, C (y j) (f i)
  have hsub : (U.filter fun y => Q x y ∧ (∃ i_o j_o, C (y j_o) (f i_o))) ⊆ univ.biUnion hits := by
    intro y hy
    obtain ⟨hyU, hyQ, i, j, hc⟩ := mem_filter.mp hy
    refine mem_biUnion.mpr ⟨i, mem_univ i, mem_filter.mpr ⟨?_, ⟨j, hc⟩⟩⟩
    have h : y ∈ P.filter (Q x) := mem_filter.mpr ⟨hUP hyU, hyQ⟩
    rw [hneighbor x] at h
    exact h
  have hhits (i : Fin t) : (hits i).card ≤ t * (2 * L) * (M x) ^ (t - 1) := by
    exact (card_packedTuples_filter_hit_le S C t _).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hBc (f i))))
  have total : (U.filter fun y => Q x y ∧ (∃ i_o j_o, C (y j_o) (f i_o))).card ≤
      t * (t * (2 * L) * (M x) ^ (t - 1)) := by
    calc
      _ ≤ (univ.biUnion hits).card := card_le_card hsub
      _ ≤ ∑ i : Fin t, (hits i).card := card_biUnion_le
      _ ≤ _ := by simpa using sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin t))) => hhits i)
  calc
    _ ≤ M x * (t * (t * (2 * L) * (M x) ^ (t - 1))) :=
      Nat.mul_le_mul hlarge total
    _ = (2 * t ^ 2 * L) * (M x) ^ t := by
      have hmPow : (M x) ^ t = (M x) ^ (t - 1) * M x :=
        (congrArg (fun k : ℕ => (M x) ^ k) (show t = (t - 1) + 1 by omega)).trans
          (pow_succ _ _)
      rw [hmPow]
      ring
    _ ≤ (2 * t ^ 2 * L) * (2 ^ t * (4 * deg)) :=
      Nat.mul_le_mul_left _ (hpower.trans (Nat.mul_le_mul_left _ hquarter))
    _ = _ := by ring


theorem sum_packing_degrees_of_average {E : Type} [Fintype E]
    (P : Finset (Fin t → E)) (hPpos : P.Nonempty)
    (S : (Fin t → E) → Finset E) (C : E → E → Prop) (L θ : ℕ)
    (ht : 0 < t) (hθ : 0 < θ) (hθL : 4 * t * L ≤ θ)
    (hS : (P.card : ℝ) * (10 * θ) ≤ ∑ x ∈ P, ((S x).card : ℝ))
    (hcap : ∀ x ∈ P, ∀ b, ((S x).filter fun a => C a b).card ≤ 2 * L) :
    4 * (P.card : ℝ) * ((θ : ℝ) ^ t + 1) <
      ∑ x ∈ P, ((((Fintype.piFinset (fun _ : Fin t => (S x))).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ C (x_p i_p) (x_p j_p))).card : ℝ) := by
  have hθR : (1 : ℝ) ≤ θ := by exact_mod_cast (show 1 ≤ θ from hθ)
  have hcodegR : (t : ℝ) * (2 * L : ℕ) ≤ θ := by
    exact_mod_cast (show t * (2 * L) ≤ θ from
      (show t * (2 * L) ≤ 4 * t * L from calc
        _ ≤ 2 * (t * (2 * L)) := by omega
        _ = _ := by ring).trans hθL)
  have hd' : (t : ℝ) * (2 * L : ℕ) ≤ 10 * θ := by linarith
  have hord := sum_card_packed_lower P hPpos S C (2 * L) t (10 * θ) hd' hS
    (fun x hx b _ => hcap x hx b)
  have hsharp : 4 * ((θ : ℝ) ^ t + 1) < (10 * (θ : ℝ) - (t : ℝ) * (2 * L : ℕ)) ^ t := by
    have hbase : 9 * (θ : ℝ) ≤ 10 * (θ : ℝ) - (t : ℝ) * (2 * L : ℕ) := by linarith
    have h₉ : (9 : ℝ) ≤ (9 : ℝ) ^ t := le_self_pow₀ (by norm_num) (by omega)
    have hθt : 1 ≤ (θ : ℝ) ^ t := one_le_pow₀ hθR
    calc
      _ < 9 * (θ : ℝ) ^ t := by linarith
      _ ≤ (9 * (θ : ℝ)) ^ t := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right h₉ (by positivity)
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hbase _
  have hp : 0 < (P.card : ℝ) := by exact_mod_cast hPpos.card_pos
  change 4 * (P.card : ℝ) * ((θ : ℝ) ^ t + 1) <
    ∑ x ∈ P, ((((Fintype.piFinset (fun _ : Fin t => (S x))).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ C (x_p i_p) (x_p j_p))).card : ℝ)
  rw [mul_comm (4 : ℝ), mul_assoc]
  exact (mul_lt_mul_of_pos_left hsharp hp).trans_le hord


theorem degree_independentBlowup {V : Type} [Fintype V] (G : SimpleGraph V)
    (t : ℕ) (v : V × Fin t) :
    ((SimpleGraph.comap (Prod.fst : _ × Fin t → _) G)).degree v = G.degree v.1 * t := by
  classical
  have h :
      ((SimpleGraph.comap (Prod.fst : _ × Fin t → _) G)).neighborFinset v = G.neighborFinset v.1 ×ˢ (univ : Finset (Fin t)) := by
    ext w
    rw [mem_neighborFinset, mem_product, mem_neighborFinset]
    simp []
  rw [← card_neighborFinset_eq_degree, h, card_product, card_univ, Fintype.card_fin, card_neighborFinset_eq_degree]


theorem exists_cycle_of_sparse_tuple_core {E : Type} [Fintype E]
    (C : E → E → Prop) (t l b c : ℕ)
    (Q : (Fin t → E) → (Fin t → E) → Prop)
    (hC : ∀ ⦃u v⦄, C u v → C v u)
    (hQ : ∀ ⦃x y⦄, Q x y → Q y x) (hQirr : ∀ x, ¬ Q x x)
    (findCycle : (∀ (W : Type) [Fintype W], Fintype.card W ≤ (Fintype.card E ^ t) →
    ∀ (G : SimpleGraph W) (conflict : W → W → Prop),
      (∀ ⦃x y⦄, conflict x y → conflict y x) → G.edgeFinset.Nonempty →
      (∀ u v, b * ((G.neighborFinset v).filter (conflict u)).card ≤ c * G.degree v) →
      ∃ f : cycleGraph l →g G, ∀ i j, i ≠ j → ¬ conflict (f i) (f j)))
    (U : Finset (Fin t → E)) (hU : U ⊆ ((Fintype.piFinset (fun _ : Fin t => univ)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ C (x_p i_p) (x_p j_p)))
    (hUne : U.Nonempty)
    (hd : ∀ x ∈ U, 0 < (U.filter (Q x)).card)
    (hover : ∀ x ∈ U, ∀ f : Fin t → E,
      b * (U.filter fun y => Q x y ∧ (∃ i_o j_o, C (y j_o) (f i_o))).card ≤ c * (U.filter (Q x)).card) :
    ∃ x : Fin l → Fin t → E,
      (∀ i, x i ∈ ((Fintype.piFinset (fun _ : Fin t => univ)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ C (x_p i_p) (x_p j_p))) ∧
      (∀ i j, (cycleGraph l).Adj i j → Q (x i) (x j)) ∧
      ∀ i j, i ≠ j → ¬ (∃ i_o j_o, C ((x j) j_o) ((x i) i_o)) := by
  classical
  let W := ↥U
  let G : SimpleGraph W :=
    { Adj := fun x y => Q x.val y.val
      symm.symm := fun _ _ h => hQ h
      loopless.irrefl := fun x h => hQirr x.val h }
  let conflict (x y : W) := (∃ i_o j_o, C (y.val j_o) (x.val i_o))
  have hc ⦃x y : W⦄ (h : conflict x y) : conflict y x := by
    obtain ⟨i, j, h⟩ := h
    exact ⟨j, i, hC h⟩
  have hcard : Fintype.card W ≤ Fintype.card (E) ^ t := by
    rw [show Fintype.card W = U.card from Fintype.card_coe U]
    exact (card_le_card hU).trans (by
      simpa only [card_univ] using packed_size_le (univ : Finset (E)) C t)
  have hfiber (v : W) (P : (Fin t → E) → Prop) :
      (((G.neighborFinset v).filter fun u => P u.val).map (Function.Embedding.subtype _)) =
        U.filter (fun u => Q v.val u ∧ P u) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      have hy' := mem_filter.mp hy
      exact mem_filter.mpr ⟨y.property, (mem_neighborFinset _ _ _).mp hy'.1, hy'.2⟩
    · intro hx
      obtain ⟨hu, ha, hp⟩ := mem_filter.mp hx
      let y : W := ⟨x, hu⟩
      exact mem_map.mpr ⟨y, mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr ha, hp⟩, rfl⟩
  have hdeg (v : W) : G.degree v = (U.filter (Q v.val)).card := by
    have h := congrArg Finset.card (hfiber v (fun _ => True))
    simpa [card_map, card_neighborFinset_eq_degree] using h
  have he : G.edgeFinset.Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    let v : W := ⟨x, hx⟩
    have hp := hd x hx
    have hp' : 0 < (G.neighborFinset v).card := by
      rw [card_neighborFinset_eq_degree, hdeg]
      exact hp
    obtain ⟨y, hy⟩ := card_pos.mp hp'
    exact ⟨s(v, y), by simpa using (mem_neighborFinset _ _ _).mp hy⟩
  have hlocal (u v : W) :
      b * ((G.neighborFinset v).filter (conflict u)).card ≤ c * G.degree v := by
    have h := congrArg Finset.card (hfiber v (fun y_q => (∃ i_o j_o, C (y_q j_o) (u.val i_o))))
    have h' : ((G.neighborFinset v).filter (conflict u)).card =
        (U.filter fun y => Q v.val y ∧ (∃ i_o j_o, C (y j_o) (u.val i_o))).card := by
      rw [card_map] at h
      convert h using 2
      all_goals (ext; simp [conflict])
    rw [h', hdeg]
    exact hover v.val v.property u.val
  obtain ⟨f, hdisj⟩ := findCycle W hcard G conflict hc he (fun u v => by convert hlocal u v)
  exact ⟨fun i => (f i).val, fun i => hU (f i).property,
    fun _ _ hij => f.map_adj hij, hdisj⟩


theorem pathWeight_cons {V : Type} (M : Matrix V V ℝ) {n : ℕ} (a w b : V)
    (x : Fin n → V) :
    (Classical.choose pathWeight_spec) M (n + 1) a (Fin.cons w x) b = M a w * (Classical.choose pathWeight_spec) M n w x b := by
  simp [pw_zero, pw_succ]

theorem pathWeight_nonneg {V : Type} (M : Matrix V V ℝ) (hM : ∀ a b, 0 ≤ M a b) :
    ∀ n a x b, 0 ≤ (Classical.choose pathWeight_spec) M n a x b := by
  intro n
  induction n with
  | zero => exact fun a x b => by rw [pw_zero]; exact hM a b
  | succ n ih =>
    intro a x b
    rw [pw_succ]
    exact mul_nonneg (hM a (x 0)) (ih (x 0) (Fin.tail x) b)

theorem sum_pathWeight_eq_pow {V : Type} [Fintype V] (M : Matrix V V ℝ) :
    ∀ n a b, (∑ x : Fin n → V, (Classical.choose pathWeight_spec) M n a x b) = (M ^ (n + 1)) a b := by
  classical
  intro n
  induction n with
  | zero =>
    intro a b
    simp [pw_zero, pw_succ]
  | succ n ih =>
    intro a b
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => V)
    calc
      _ = ∑ z : V × (Fin n → V), (Classical.choose pathWeight_spec) M (n + 1) a (e z) b :=
        (Fintype.sum_equiv e (fun z => (Classical.choose pathWeight_spec) M (n + 1) a (e z) b)
          (fun x => (Classical.choose pathWeight_spec) M (n + 1) a x b) (fun _ => rfl)).symm
      _ = ∑ w : V, M a w * (M ^ (n + 1)) w b := by
        rw [Fintype.sum_prod_type]
        apply sum_congr rfl
        intro w _
        change (∑ x : Fin n → V, (Classical.choose pathWeight_spec) M (n + 1) a (Fin.cons w x) b) = _
        simp only [pathWeight_cons, ← mul_sum, ih]
      _ = _ := by
        rw [show M ^ (n + 1 + 1) = M * M ^ (n + 1) from pow_succ' _ _, Matrix.mul_apply]

theorem pathWeight_cast {V : Type} (M : Matrix V V ℝ) {n m : ℕ}
    (h : n = m) (x : Fin m → V) (a b : V) :
    (Classical.choose pathWeight_spec) M n a (x ∘ Fin.cast h) b = (Classical.choose pathWeight_spec) M m a x b := by
  subst m
  rfl

theorem pathWeight_append_cons {V : Type} (M : Matrix V V ℝ) {m n : ℕ}
    (a c b : V) (x : Fin m → V) (y : Fin n → V) :
    (Classical.choose pathWeight_spec) M (m + (n + 1)) a (Fin.append x (Fin.cons c y)) b =
      (Classical.choose pathWeight_spec) M m a x c * (Classical.choose pathWeight_spec) M n c y b := by
  induction m generalizing a with
  | zero =>
    have hx : Fin.append x (Fin.cons c y) =
        Fin.cons c y ∘ Fin.cast (Nat.zero_add (n + 1)) := by
      exact Fin.append_left_nil _ _ rfl
    rw [hx, pathWeight_cast, pathWeight_cons, pw_zero]
  | succ m ih =>
    let z := x 0
    let u := Fin.tail x
    have hx : x = Fin.cons z u := (Fin.cons_self_tail x).symm
    rw [hx, Fin.append_cons]
    have he : m + 1 + (n + 1) = (m + (n + 1)) + 1 := Nat.add_right_comm m 1 (n + 1)
    rw [pathWeight_cast M he, pathWeight_cons, pathWeight_cons, ih]
    ring


theorem pathWeight_eq_prod {V : Type} (M : Matrix V V ℝ) :
    ∀ n (a : V) (x : Fin n → V) (b : V),
      let y : Fin (n + 2) → V := Fin.cons a (Fin.snoc x b)
      (Classical.choose pathWeight_spec) M n a x b =
        ∏ i : Fin (n + 1), M (y i.castSucc) (y i.succ) := by
  intro n
  induction n with
  | zero =>
    intro a x b
    simp [pw_zero, pw_succ, Fin.snoc]
  | succ n ih =>
    intro a x b y
    rw [Fin.prod_univ_succ]
    have h0 : y ((0 : Fin (n + 2)).castSucc) = a := by simp [y]
    have h1 : y ((0 : Fin (n + 2)).succ) = x 0 := by
      simp only [y, Fin.cons_succ]
      exact Fin.snoc_castSucc (α := fun _ => V) b x (0 : Fin (n + 1))
    have hy : Fin.tail y = Fin.cons (x 0) (Fin.snoc (Fin.tail x) b) := by
      simp only [y, Fin.tail_cons]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Fin.snoc_castSucc (α := fun _ => V) b x (0 : Fin (n + 1))
      · simp only [Fin.cons_succ]
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simp
        · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
          rfl
    rw [h0, h1]
    rw [show (Classical.choose pathWeight_spec) M (n + 1) a x b = M a (x 0) *
      (Classical.choose pathWeight_spec) M n (x 0) (Fin.tail x) b from pw_succ M n a x b, ih]
    congr 1
    apply Fintype.prod_congr
    intro i
    simp only [← hy, Fin.tail, Fin.succ_castSucc]


theorem pow_detailedBalance {V : Type} [Fintype V] (M : Matrix V V ℝ)
    (w : V → ℝ) (h : ∀ a b, w a * M a b = w b * M b a) :
    ∀ n a b, w a * (M ^ n) a b = w b * (M ^ n) b a := by
  classical
  intro n
  induction n with
  | zero =>
    intro a b
    by_cases hab : a = b
    · subst b
      rfl
    · simp [hab, Ne.symm hab]
  | succ n ih =>
    intro a b
    calc
      _ = ∑ x : V, (w a * M a x) * (M ^ n) x b := by
        rw [pow_succ', Matrix.mul_apply, mul_sum]
        exact sum_congr rfl (fun x _ => by ring)
      _ = ∑ x : V, (w b * (M ^ n) b x) * M x a := by
        apply sum_congr rfl
        intro x _
        rw [h a x, mul_assoc, mul_comm (M x a), ← mul_assoc, ih x b]
      _ = _ := by
        rw [pow_succ, Matrix.mul_apply, mul_sum]
        exact sum_congr rfl (fun x _ => by ring)


theorem pow_rows_eq_one {V : Type} [Fintype V] (M : Matrix V V ℝ)
    (h : ∀ a, ∑ b : V, M a b = 1) :
    ∀ n a, ∑ b : V, (M ^ n) a b = 1 := by
  classical
  intro n
  induction n with
  | zero => intro a; simp [Matrix.one_apply]
  | succ n ih =>
    intro a
    simp_rw [pow_succ', Matrix.mul_apply]
    rw [sum_comm]
    simp_rw [← mul_sum, ih, mul_one]
    exact h a

theorem trace_pow_split {V : Type} [Fintype V] (M : Matrix V V ℝ) (a b : ℕ) :
    Matrix.trace (M ^ (a + b)) = ∑ x : V × V, (M ^ a) x.1 x.2 * (M ^ b) x.2 x.1 := by
  rw [pow_add, Matrix.trace, Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Matrix.mul_apply]


theorem one_le_even_trace {V : Type} [Fintype V] [Nonempty V]
    (M : Matrix V V ℝ) (w : V → ℝ) (hw : ∀ v, 0 < w v)
    (hbal : ∀ a b, w a * M a b = w b * M b a)
    (hrow : ∀ a, ∑ b : V, M a b = 1) (n : ℕ) :
    1 ≤ Matrix.trace (M ^ (n + n)) := by
  classical
  let W := ∑ v : V, w v
  have hW : 0 < W := sum_pos (fun v _ => hw v) univ_nonempty
  have rowBound (a : V) :
      w a / W ≤ ∑ b : V, (M ^ n) a b * (M ^ n) b a := by
    have hc := sq_sum_div_le_sum_sq_div univ (fun b => (M ^ n) a b)
      (g := w) (fun b _ => hw b)
    rw [pow_rows_eq_one M hrow n a, one_pow] at hc
    calc
      _ = w a * (1 / W) := by ring
      _ ≤ w a * ∑ b : V, ((M ^ n) a b) ^ 2 / w b :=
        mul_le_mul_of_nonneg_left hc (hw a).le
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro b _
        have hb := pow_detailedBalance M w hbal n a b
        have hb' : (M ^ n) b a = w a * (M ^ n) a b / w b :=
          (eq_div_iff (hw b).ne').2 (by rw [mul_comm, hb])
        rw [hb']
        ring
  have h := sum_le_sum (fun a (_ : a ∈ (univ : Finset V)) => rowBound a)
  rw [← sum_div, div_self hW.ne', ← Fintype.sum_prod_type'] at h
  simpa only [trace_pow_split] using h


theorem even_trace_logConvex {V : Type} [Fintype V]
    (M : Matrix V V ℝ) (w : V → ℝ) (hw : ∀ v, 0 < w v)
    (hbal : ∀ a b, w a * M a b = w b * M b a) (j : ℕ) :
    (Matrix.trace (M ^ ((j + 1) + (j + 1)))) ^ 2 ≤
      Matrix.trace (M ^ (j + j)) * Matrix.trace (M ^ ((j + 2) + (j + 2))) := by
  classical
  let f (k : ℕ) (p : V × V) := Real.sqrt (w p.1 / w p.2) * (M ^ k) p.1 p.2
  have hprod (a b : ℕ) :
      (∑ p : V × V, f a p * f b p) = Matrix.trace (M ^ (a + b)) := by
    rw [trace_pow_split]
    apply sum_congr rfl
    intro p _
    have hroot : Real.sqrt (w p.1 / w p.2) ^ 2 = w p.1 / w p.2 :=
      Real.sq_sqrt (by positivity [hw p.1, hw p.2])
    have hbal' := pow_detailedBalance M w hbal b p.1 p.2
    calc
      _ = Real.sqrt (w p.1 / w p.2) ^ 2 * ((M ^ a) p.1 p.2 * (M ^ b) p.1 p.2) := by
        dsimp [f]
        ring
      _ = _ := by
        rw [hroot]
        have hb' : (M ^ b) p.2 p.1 = w p.1 * (M ^ b) p.1 p.2 / w p.2 :=
          (eq_div_iff (hw p.2).ne').2 (by rw [mul_comm, hbal'])
        rw [hb']
        ring
  have h := sum_mul_sq_le_sq_mul_sq univ (f j) (f (j + 2))
  simp only [sq, hprod] at h ⊢
  simpa only [show j + (j + 2) = (j + 1) + (j + 1) by omega] using h


theorem logConvex_nat_interpolation (T : ℕ → ℝ) (hp : ∀ n, 0 < T n)
    (hcv : ∀ n, (T (n + 1)) ^ 2 ≤ T n * T (n + 2)) {n : ℕ} (hn : 0 < n) :
    (T (n - 1)) ^ n ≤ T 0 * (T n) ^ (n - 1) := by
  let r (k : ℕ) := T (k + 1) / T k
  have hstep (k : ℕ) : r k ≤ r (k + 1) := by
    dsimp [r]
    rw [div_le_div_iff₀ (hp k) (hp (k + 1))]
    simpa only [sq, mul_comm] using hcv k
  have hr : Monotone r := monotone_nat_of_le_succ hstep
  have hprod (m : ℕ) : T 0 * ∏ k ∈ range m, r k = T m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [prod_range_succ, ← mul_assoc, ih]
      exact mul_div_cancel₀ _ (hp _).ne'
  have hbound : (∏ k ∈ range (n - 1), r k) ≤ (r (n - 1)) ^ (n - 1) := by
    calc
      _ ≤ ∏ _k ∈ range (n - 1), r (n - 1) :=
        prod_le_prod (fun k _ => div_nonneg (hp _).le (hp _).le)
          (fun k hk => hr (by have := mem_range.mp hk; omega))
      _ = _ := by simp
  have ht := mul_le_mul_of_nonneg_left hbound (hp 0).le
  rw [hprod] at ht
  have hrn : r (n - 1) = T n / T (n - 1) := by
    dsimp [r]
    rw [Nat.sub_add_cancel (show 1 ≤ n from hn)]
  rw [hrn, div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos (hp _) _)] at ht
  calc
    _ = T (n - 1) * T (n - 1) ^ (n - 1) := by
      exact (congrArg (fun k : ℕ => (T (n - 1)) ^ k)
        (Nat.sub_add_cancel (show 1 ≤ n from hn)).symm).trans (pow_succ' _ _)
    _ ≤ _ := ht


theorem badPrefixWeight_nonneg {V : Type} [Fintype V] (M : Matrix V V ℝ)
    (hM : ∀ u v, 0 ≤ M u v) (conflict : V → V → Prop) (n : ℕ) (a b c : V) :
    0 ≤ (∑ x_b : Fin (n + 1) → _, if ∃ i_b : Fin (n + 2), conflict a (Fin.cons (α := fun _ => _) b x_b i_b) then (Classical.choose pathWeight_spec) M (n + 1) b x_b c else 0) := by
  exact sum_nonneg fun x _ => by split <;> first | exact pathWeight_nonneg M hM _ _ _ _ | (rw [cw_eq]; exact pathWeight_nonneg M hM _ _ _ _) | rfl

theorem badPrefixWeight_le_pow {V : Type} [Fintype V] (M : Matrix V V ℝ)
    (hM : ∀ u v, 0 ≤ M u v) (conflict : V → V → Prop) (n : ℕ) (a b c : V) :
    (∑ x_b : Fin (n + 1) → _, if ∃ i_b : Fin (n + 2), conflict a (Fin.cons (α := fun _ => _) b x_b i_b) then (Classical.choose pathWeight_spec) M (n + 1) b x_b c else 0) ≤ (M ^ (n + 2)) b c := by
  classical
  rw [← sum_pathWeight_eq_pow M (n + 1)]
  exact sum_le_sum fun x _ => by split <;> first | exact le_rfl | exact pathWeight_nonneg M hM _ _ _ _

theorem sum_mass_ratio_square {I : Type} [Fintype I] (T X Y : I → ℝ)
    (hT : ∀ i, 0 ≤ T i) (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i)
    (hs : ∀ i, T i ≠ 0 → X i ≠ 0 ∧ Y i ≠ 0) :
    (∑ i, T i) ^ 2 ≤ (∑ i, T i * (X i / Y i)) * (∑ i, T i * (Y i / X i)) := by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => mul_nonneg (hT i) (div_nonneg (hX i) (hY i)))
    (fun i _ => mul_nonneg (hT i) (div_nonneg (hY i) (hX i)))
  intro i _
  by_cases h : T i = 0
  · simp [h]
  · obtain ⟨hx, hy⟩ := hs i h
    exact le_of_eq (by field_simp)

theorem sum_badPrefixWeight_row {V : Type} [Fintype V] (M : Matrix V V ℝ)
    (hM : ∀ u v, 0 ≤ M u v) (conflict : V → V → Prop)
    (α : ℝ) (hloc : ∀ u v, ∑ a : V, (if conflict a u then M v a else 0) ≤ α)
    (n : ℕ) (b c : V) :
    (∑ a : V, M b a * (∑ x_b : Fin (n + 1) → _, if ∃ i_b : Fin (n + 2), conflict a (Fin.cons (α := fun _ => _) b x_b i_b) then (Classical.choose pathWeight_spec) M (n + 1) b x_b c else 0)) ≤
      ((n + 2 : ℕ) : ℝ) * α * (M ^ (n + 2)) b c := by
  classical
  let k : ℝ := (n + 2 : ℕ)
  let w (x : Fin (n + 1) → V) := (Classical.choose pathWeight_spec) M (n + 1) b x c
  let bad (x : Fin (n + 1) → V) (a : V) := ∃ i : Fin (n + 2), conflict a (Fin.cons (α := fun _ => V) b x i)
  have hweight (x : Fin (n + 1) → V) :
      (∑ a : V, if bad x a then M b a else 0) ≤ k * α := by
    calc
      _ ≤ ∑ a : V, ∑ i : Fin (n + 2), if conflict a (Fin.cons (α := fun _ => V) b x i) then M b a else 0 := by
        apply sum_le_sum
        intro a _
        by_cases hb : bad x a
        · obtain ⟨i, hi⟩ := hb
          simpa only [if_pos (show bad x a from ⟨i, hi⟩), if_pos hi] using
            (Finset.single_le_sum
              (f := fun j : Fin (n + 2) => if conflict a (Fin.cons (α := fun _ => V) b x j) then M b a else 0)
              (fun j _ => by split <;> first | exact hM b a | rfl) (mem_univ i))
        · simpa only [if_neg hb] using sum_nonneg (fun i (_ : i ∈ (univ : Finset (Fin (n + 2)))) =>
            by split <;> first | exact hM b a | rfl)
      _ = ∑ i : Fin (n + 2), ∑ a : V, if conflict a (Fin.cons (α := fun _ => V) b x i) then M b a else 0 := sum_comm
      _ ≤ ∑ _i : Fin (n + 2), α := sum_le_sum fun i _ => hloc (Fin.cons (α := fun _ => V) b x i) b
      _ = _ := by simp [k]
  calc
    _ = ∑ a : V, ∑ x : Fin (n + 1) → V, (if bad x a then M b a else 0) * w x := by
      apply sum_congr rfl
      intro a _
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      by_cases hx : bad x a <;> simp [bad, w] at hx ⊢
    _ = ∑ x : Fin (n + 1) → V, (∑ a : V, if bad x a then M b a else 0) * w x := by
      rw [sum_comm]
      simp only [sum_mul]
    _ ≤ ∑ x : Fin (n + 1) → V, (k * α) * w x := by
      exact sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hweight x) (pathWeight_nonneg M hM _ _ _ _)
    _ = _ := by rw [← mul_sum]; congr 1; exact sum_pathWeight_eq_pow M (n + 1) b c


theorem badHalfWalk_mass_square {V : Type} [Fintype V] (M : Matrix V V ℝ)
    (w : V → ℝ) (hw : ∀ v, 0 < w v)
    (hM : ∀ u v, 0 ≤ M u v) (hrow : ∀ a, ∑ b : V, M a b = 1)
    (hbal : ∀ a b, w a * M a b = w b * M b a)
    (conflict : V → V → Prop) (α : ℝ) (_hα : 0 ≤ α)
    (hloc : ∀ u v, ∑ a : V, (if conflict a u then M v a else 0) ≤ α)
    (n : ℕ) :
    (∑ a : V, ∑ b : V, ∑ c : V,
      M a b * (∑ x_b : Fin (n + 1) → _, if ∃ i_b : Fin (n + 2), conflict a (Fin.cons (α := fun _ => _) b x_b i_b) then (Classical.choose pathWeight_spec) M (n + 1) b x_b c else 0) * (M ^ (n + 1)) c a) ^ 2 ≤
      ((n + 2 : ℕ) : ℝ) * α * Matrix.trace (M ^ ((n + 1) + (n + 1))) *
        Matrix.trace (M ^ ((n + 2) + (n + 2))) := by
  classical
  let U := fun a_q b_q c_q => (∑ x_b : Fin (n + 1) → _, if ∃ i_b : Fin (n + 2), conflict a_q (Fin.cons (α := fun _ => _) b_q x_b i_b) then (Classical.choose pathWeight_spec) M (n + 1) b_q x_b c_q else 0)
  let A₂ (a c : V) := (M ^ (n + 1)) a c
  let B₂ (a c : V) := (M ^ (n + 2)) a c
  let T (p : V × V × V) := M p.1 p.2.1 * U p.1 p.2.1 p.2.2 * A₂ p.2.2 p.1
  let X (p : V × V × V) := A₂ p.1 p.2.2
  let Y (p : V × V × V) := B₂ p.2.1 p.2.2
  have hA (a c : V) : 0 ≤ A₂ a c := Matrix.pow_apply_nonneg hM _ a c
  have hB (a c : V) : 0 ≤ B₂ a c := Matrix.pow_apply_nonneg hM _ a c
  have hU (a b c : V) : 0 ≤ U a b c := badPrefixWeight_nonneg M hM conflict n a b c
  have hUB (a b c : V) : U a b c ≤ B₂ b c := badPrefixWeight_le_pow M hM conflict n a b c
  have hT (p : V × V × V) : 0 ≤ T p := mul_nonneg (mul_nonneg (hM _ _) (hU _ _ _)) (hA _ _)
  have hs (p : V × V × V) (hp : T p ≠ 0) : X p ≠ 0 ∧ Y p ≠ 0 := by
    obtain ⟨a, b, c⟩ := p
    change M a b * U a b c * A₂ c a ≠ 0 at hp
    refine ⟨?_, (lt_of_lt_of_le (lt_of_le_of_ne (hU a b c) ?_) (hUB a b c)).ne'⟩
    · change A₂ a c ≠ 0
      intro hx
      have hb := pow_detailedBalance M w hbal (n + 1) a c
      change w a * A₂ a c = w c * A₂ c a at hb
      rw [hx, mul_zero] at hb
      have hc : A₂ c a = 0 := (mul_eq_zero.mp hb.symm).resolve_left (hw c).ne'
      simp [hc] at hp
    · exact Ne.symm (fun h => hp (by simp [h]))
  have hratio₁ (a b c : V) : T (a, b, c) * (X (a, b, c) / Y (a, b, c)) ≤
      M a b * (A₂ a c * A₂ c a) := by
    have hu : U a b c * (A₂ a c / B₂ b c) ≤ A₂ a c := by
      by_cases h : B₂ b c = 0
      · simpa [h] using hA a c
      · calc
          _ ≤ B₂ b c * (A₂ a c / B₂ b c) :=
            mul_le_mul_of_nonneg_right (hUB a b c) (div_nonneg (hA a c) (hB b c))
          _ = _ := by field_simp
    dsimp [T, X, Y]
    calc
      _ = M a b * (U a b c * (A₂ a c / B₂ b c)) * A₂ c a := by ring
      _ ≤ M a b * A₂ a c * A₂ c a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (hM a b)) (hA c a)
      _ = _ := by ring
  have hratio₂ (a b c : V) : T (a, b, c) * (Y (a, b, c) / X (a, b, c)) ≤
      B₂ c b * (M b a * U a b c) := by
    by_cases hx : A₂ a c = 0
    · simpa [T, X, Y, hx] using mul_nonneg (hB c b) (mul_nonneg (hM b a) (hU a b c))
    have ha := pow_detailedBalance M w hbal (n + 1) a c
    have hb := pow_detailedBalance M w hbal (n + 2) b c
    change w a * A₂ a c = w c * A₂ c a at ha
    change w b * B₂ b c = w c * B₂ c b at hb
    have hret : A₂ c a / A₂ a c = w a / w c := by
      apply (div_eq_div_iff hx (hw c).ne').2
      linarith only [ha]
    have hret' : w b * B₂ b c / w c = B₂ c b := (div_eq_iff (hw c).ne').2 (by simpa only [mul_comm (w c)] using hb)
    apply le_of_eq
    dsimp [T, X, Y]
    calc
      _ = U a b c * (M a b * ((A₂ c a / A₂ a c) * B₂ b c)) := by ring
      _ = U a b c * ((w a * M a b) * B₂ b c / w c) := by rw [hret]; ring
      _ = U a b c * (M b a * (w b * B₂ b c / w c)) := by rw [hbal]; ring
      _ = _ := by rw [hret']; ring
  have h₁ : (∑ p : V × V × V, T p * (X p / Y p)) ≤ Matrix.trace (M ^ ((n + 1) + (n + 1))) := by
    calc
      _ ≤ ∑ a : V, ∑ b : V, ∑ c : V, M a b * (A₂ a c * A₂ c a) := by
        simp only [Fintype.sum_prod_type]
        exact sum_le_sum fun a _ => sum_le_sum fun b _ => sum_le_sum fun c _ => hratio₁ a b c
      _ = ∑ a : V, ∑ c : V, A₂ a c * A₂ c a := by
        apply sum_congr rfl
        intro a _
        rw [sum_comm]
        simp only [← sum_mul, hrow, one_mul]
      _ = _ := by rw [trace_pow_split, Fintype.sum_prod_type]
  have h₂ : (∑ p : V × V × V, T p * (Y p / X p)) ≤
      ((n + 2 : ℕ) : ℝ) * α * Matrix.trace (M ^ ((n + 2) + (n + 2))) := by
    calc
      _ ≤ ∑ a : V, ∑ b : V, ∑ c : V, B₂ c b * (M b a * U a b c) := by
        simp only [Fintype.sum_prod_type]
        exact sum_le_sum fun a _ => sum_le_sum fun b _ => sum_le_sum fun c _ => hratio₂ a b c
      _ = ∑ b : V, ∑ c : V, B₂ c b * ∑ a : V, M b a * U a b c := by
        rw [sum_comm]
        apply sum_congr rfl
        intro b _
        rw [sum_comm]
        simp only [← mul_sum]
      _ ≤ ∑ b : V, ∑ c : V, B₂ c b * (((n + 2 : ℕ) : ℝ) * α * B₂ b c) := by
        exact sum_le_sum fun b _ => sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (sum_badPrefixWeight_row M hM conflict α hloc n b c) (hB c b)
      _ = _ := by
        rw [trace_pow_split, Fintype.sum_prod_type]
        have h (b c : V) : B₂ c b * (((n + 2 : ℕ) : ℝ) * α * B₂ b c) =
            ((n + 2 : ℕ) : ℝ) * α * (B₂ b c * B₂ c b) := by ring
        simp only [h, ← mul_sum, B₂]
  have hT₂ : 0 ≤ ∑ p : V × V × V, T p * (Y p / X p) :=
    sum_nonneg fun p _ => mul_nonneg (hT p) (div_nonneg (hB _ _) (hA _ _))
  have htr₁ : 0 ≤ Matrix.trace (M ^ ((n + 1) + (n + 1))) := by
    rw [trace_pow_split]
    exact sum_nonneg fun p _ => mul_nonneg (hA _ _) (hA _ _)
  calc
    _ = (∑ p : V × V × V, T p) ^ 2 := by simp only [Fintype.sum_prod_type, T, U, A₂]
    _ ≤ (∑ p : V × V × V, T p * (X p / Y p)) * ∑ p : V × V × V, T p * (Y p / X p) :=
      sum_mass_ratio_square T X Y hT (fun _ => hA _ _) (fun _ => hB _ _) hs
    _ ≤ Matrix.trace (M ^ ((n + 1) + (n + 1))) *
        (((n + 2 : ℕ) : ℝ) * α * Matrix.trace (M ^ ((n + 2) + (n + 2)))) :=
      mul_le_mul h₁ h₂ hT₂ htr₁
    _ = _ := by ring

theorem closedWeight_eq_prod {V : Type} (M : Matrix V V ℝ) {n : ℕ}
    (x : Fin (n + 2) → V) :
    (Classical.choose closedWeight_spec) M x = ∏ i : Fin (n + 2), M (x i) (x (i + 1)) := by
  rw [cw_eq]
  rw [pathWeight_eq_prod]
  have hy : (Fin.cons (α := fun _ => V) (x 0) (Fin.snoc (Fin.tail x) (x 0))) =
      Fin.snoc x (x 0) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [← Fin.succ_last, Fin.cons_succ, Fin.snoc_last, Fin.succ_last, Fin.snoc_last]
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · rw [Fin.castSucc_succ, Fin.cons_succ, Fin.snoc_castSucc, ← Fin.castSucc_succ, Fin.snoc_castSucc]
        rfl
  simp only [hy]
  apply Fintype.prod_congr
  intro i
  rw [Fin.snoc_castSucc]
  congr 1
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.succ_last, Fin.snoc_last]
    congr 1
    apply Fin.ext
    have h1 : ((1 : Fin (n + 2)) : ℕ) = 1 := by simp
    rw [Fin.val_add, Fin.val_last, h1, Fin.val_zero, Nat.mod_self]
  · rw [Fin.succ_castSucc, Fin.snoc_castSucc]
    congr 1
    apply Fin.ext
    have h1 : ((1 : Fin (n + 2)) : ℕ) = 1 := by simp
    rw [Fin.val_add, Fin.val_castSucc, h1, Fin.val_succ]
    exact (Nat.mod_eq_of_lt (show j.val + 1 < n + 2 from j.succ.isLt)).symm

theorem packClosedCycle_zero {V : Type} (n : ℕ) (a b : V) (x : Fin (n + 1) → V)
    (c : V) (y : Fin n → V) : (Fin.cons a (Fin.cons b (Fin.append x (Fin.cons c y))) : Fin (((n + 1) + (n + 1)) + 2) → _) 0 = a :=
  Fin.cons_zero _ _

theorem packClosedCycle_prefix {V : Type} (n : ℕ) (a b : V) (x : Fin (n + 1) → V)
    (c : V) (y : Fin n → V) (i : Fin (n + 2)) :
    (Fin.cons a (Fin.cons b (Fin.append x (Fin.cons c y))) : Fin (((n + 1) + (n + 1)) + 2) → _) ((⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (((n + 1) + (n + 1)) + 2))) = Fin.cons (α := fun _ => V) b x i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change Fin.cons (α := fun _ => V) a
        (Fin.cons b (Fin.append x (Fin.cons c y))) (Fin.succ 0) = _
    simp
  · change Fin.cons (α := fun _ => V) a
        (Fin.cons b (Fin.append x (Fin.cons c y))) ((Fin.castAdd (n + 1) j).succ.succ) = _
    simp only [Fin.cons_succ, Fin.append_left]

theorem closedWeight_pack {V : Type} (M : Matrix V V ℝ) (n : ℕ) (a b : V)
    (x : Fin (n + 1) → V) (c : V) (y : Fin n → V) :
    (Classical.choose closedWeight_spec) M ((Fin.cons a (Fin.cons b (Fin.append x (Fin.cons c y))) : Fin (((n + 1) + (n + 1)) + 2) → _)) =
      M a b * (Classical.choose pathWeight_spec) M (n + 1) b x c * (Classical.choose pathWeight_spec) M n c y a := by
  simp only [cw_eq, Fin.cons_zero, Fin.tail_cons, pathWeight_cons, pathWeight_append_cons, mul_assoc]

theorem sum_over_packClosedCycle {V : Type} [Fintype V] (n : ℕ)
    (F : (Fin (((n + 1) + (n + 1)) + 2) → V) → ℝ) :
    (∑ z, F z) = ∑ a, ∑ b, ∑ x, ∑ c, ∑ y, F ((Fin.cons a (Fin.cons b (Fin.append x (Fin.cons c y))) : Fin (((n + 1) + (n + 1)) + 2) → _)) := by
  let e₀ : V × (Fin n → V) ≃ (Fin (n + 1) → V) := Fin.consEquiv (fun _ : Fin (n + 1) => V)
  let e₁ : (Fin (n + 1) → V) × V × (Fin n → V) ≃
      (Fin ((n + 1) + (n + 1)) → V) :=
    (Equiv.prodCongr (Equiv.refl _) e₀).trans (Fin.appendEquiv _ _)
  let e₂ : V × (Fin (n + 1) → V) × V × (Fin n → V) ≃
      (Fin (((n + 1) + (n + 1)) + 1) → V) :=
    (Equiv.prodCongr (Equiv.refl _) e₁).trans (Fin.consEquiv (fun _ : Fin (((n + 1) + (n + 1)) + 1) => V))
  let e : V × V × (Fin (n + 1) → V) × V × (Fin n → V) ≃
      (Fin (((n + 1) + (n + 1)) + 2) → V) :=
    (Equiv.prodCongr (Equiv.refl _) e₂).trans (Fin.consEquiv (fun _ : Fin (((n + 1) + (n + 1)) + 2) => V))
  have h := (Fintype.sum_equiv e (fun p => F ((Fin.cons p.1 (Fin.cons p.2.1 (Fin.append p.2.2.1 (Fin.cons p.2.2.2.1 p.2.2.2.2))) : Fin (((n + 1) + (n + 1)) + 2) → _))) F (fun _ => rfl)).symm
  simpa only [Fintype.sum_prod_type] using h


theorem sum_closedWeight_prefix {V : Type} [Fintype V] (M : Matrix V V ℝ) (n : ℕ)
    (P : V → (Fin (n + 2) → V) → Prop) :
    (∑ z : Fin (((n + 1) + (n + 1)) + 2) → V,
      if P (z 0) (fun i => z ((⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (((n + 1) + (n + 1)) + 2)))) then (Classical.choose closedWeight_spec) M z else 0) =
    ∑ a : V, ∑ b : V, ∑ c : V, M a b *
      (∑ x : Fin (n + 1) → V, if P a (Fin.cons (α := fun _ => V) b x)
        then (Classical.choose pathWeight_spec) M (n + 1) b x c else 0) * (M ^ (n + 1)) c a := by
  classical
  rw [sum_over_packClosedCycle]
  simp only [packClosedCycle_zero, packClosedCycle_prefix, closedWeight_pack]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  rw [mul_sum, sum_mul]
  apply sum_congr rfl
  intro x _
  by_cases hx : P a (Fin.cons (α := fun _ => V) b x)
  · simp only [hx, if_true, ← mul_sum, sum_pathWeight_eq_pow]
  · simp [hx]

theorem sum_closedWeight_eq_trace {V : Type} [Fintype V] (M : Matrix V V ℝ) (n : ℕ) :
    (∑ z : Fin (((n + 1) + (n + 1)) + 2) → V, (Classical.choose closedWeight_spec) M z) =
      Matrix.trace (M ^ ((n + 2) + (n + 2))) := by
  have h := sum_closedWeight_prefix M n (fun _ _ => True)
  simp only [if_true, sum_pathWeight_eq_pow] at h
  rw [h, show (n + 2) + (n + 2) = (n + 3) + (n + 1) by omega, trace_pow_split, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  calc
    _ = (∑ b : V, M a b * (M ^ (n + 2)) b c) * (M ^ (n + 1)) c a := by rw [sum_mul]
    _ = (M ^ (n + 3)) a c * (M ^ (n + 1)) c a := by
      rw [show M ^ (n + 3) = M * M ^ (n + 2) from pow_succ' _ _, Matrix.mul_apply]

theorem closedWeight_translate {V : Type} (M : Matrix V V ℝ) {n : ℕ}
    (j : Fin (n + 2)) (x : Fin (n + 2) → V) :
    (Classical.choose closedWeight_spec) M (({ toFun := fun x_w i_w => x_w (i_w + j), invFun := fun x_w i_w => x_w (i_w - j), left_inv := fun x_w => funext fun _ => by simp, right_inv := fun x_w => funext fun _ => by simp } : (Fin _ → _) ≃ (Fin _ → _)) x) = (Classical.choose closedWeight_spec) M x := by
  rw [closedWeight_eq_prod, closedWeight_eq_prod]
  let e : Fin (n + 2) ≃ Fin (n + 2) :=
    ⟨fun i => i + j, fun i => i - j, fun _ => by simp, fun _ => by simp⟩
  apply Fintype.prod_equiv e
  intro i
  change M (x (i + j)) (x ((i + 1) + j)) = M (x (i + j)) (x ((i + j) + 1))
  rw [add_right_comm]

theorem conflict_detected_by_translation {V : Type} (conflict : V → V → Prop)
    (hsym : ∀ ⦃u v⦄, conflict u v → conflict v u)
    (n : ℕ) (z : Fin (((n + 1) + (n + 1)) + 2) → V)
    (hb : ∃ i j, i ≠ j ∧ conflict (z i) (z j)) :
    ∃ j : Fin (((n + 1) + (n + 1)) + 2), ∃ i : Fin (n + 2),
      conflict ((({ toFun := fun x_w i_w => x_w (i_w + j), invFun := fun x_w i_w => x_w (i_w - j), left_inv := fun x_w => funext fun _ => by simp, right_inv := fun x_w => funext fun _ => by simp } : (Fin _ → _) ≃ (Fin _ → _)) z) 0) ((({ toFun := fun x_w i_w => x_w (i_w + j), invFun := fun x_w i_w => x_w (i_w - j), left_inv := fun x_w => funext fun _ => by simp, right_inv := fun x_w => funext fun _ => by simp } : (Fin _ → _) ≃ (Fin _ → _)) z) ((⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (((n + 1) + (n + 1)) + 2)))) := by
  let L := ((n + 1) + (n + 1)) + 2
  have detect (i j : Fin L) (hij : i < j) (h : conflict (z i) (z j)) :
      ∃ j' : Fin L, ∃ p : Fin (n + 2),
        conflict ((({ toFun := fun x_w i_w => x_w (i_w + j'), invFun := fun x_w i_w => x_w (i_w - j'), left_inv := fun x_w => funext fun _ => by simp, right_inv := fun x_w => funext fun _ => by simp } : (Fin _ → _) ≃ (Fin _ → _)) z) 0) ((({ toFun := fun x_w i_w => x_w (i_w + j'), invFun := fun x_w i_w => x_w (i_w - j'), left_inv := fun x_w => funext fun _ => by simp, right_inv := fun x_w => funext fun _ => by simp } : (Fin _ → _) ≃ (Fin _ → _)) z) ((⟨p.val + 1, by have := p.isLt; omega⟩ : Fin (((n + 1) + (n + 1)) + 2)))) := by
    have hlt : i.val < j.val := hij
    by_cases hp : j.val - i.val ≤ n + 2
    · let p : Fin (n + 2) := ⟨j.val - i.val - 1, by omega⟩
      have he : (⟨p.val + 1, by have := p.isLt; omega⟩ : Fin (((n + 1) + (n + 1)) + 2)) + i = j := by
        apply Fin.ext
        rw [Fin.val_add]
        have hw : ((⟨p.val + 1, by have := p.isLt; omega⟩ : Fin (((n + 1) + (n + 1)) + 2))).val + i.val = j.val := by
          change j.val - i.val - 1 + 1 + i.val = j.val
          omega
        rw [hw, Nat.mod_eq_of_lt j.isLt]
      refine ⟨i, p, ?_⟩
      change conflict (z (0 + i)) (z ((⟨p.val + 1, by have := p.isLt; omega⟩ : Fin (((n + 1) + (n + 1)) + 2)) + i))
      simpa only [zero_add, he] using h
    · have hgap : 0 < L - (j.val - i.val) := by
        have hj := j.isLt
        omega
      let p : Fin (n + 2) := ⟨L - (j.val - i.val) - 1, by dsimp [L] at *; omega⟩
      have he : (⟨p.val + 1, by have := p.isLt; omega⟩ : Fin (((n + 1) + (n + 1)) + 2)) + j = i := by
        apply Fin.ext
        rw [Fin.val_add]
        have hw : ((⟨p.val + 1, by have := p.isLt; omega⟩ : Fin (((n + 1) + (n + 1)) + 2))).val + j.val = L + i.val := by
          change L - (j.val - i.val) - 1 + 1 + j.val = L + i.val
          have hj := j.isLt
          omega
        change (((⟨p.val + 1, by have := p.isLt; omega⟩ : Fin (((n + 1) + (n + 1)) + 2))).val + j.val) % L = i.val
        rw [hw, Nat.add_mod_left, Nat.mod_eq_of_lt i.isLt]
      refine ⟨j, p, ?_⟩
      change conflict (z (0 + j)) (z ((⟨p.val + 1, by have := p.isLt; omega⟩ : Fin (((n + 1) + (n + 1)) + 2)) + j))
      simpa only [zero_add, he] using hsym h
  obtain ⟨i, j, hij, h⟩ := hb
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact detect i j hij h
  · exact detect j i hij (hsym h)

theorem sum_badClosed_le_prefix {V : Type} [Fintype V] (M : Matrix V V ℝ)
    (hM : ∀ a b, 0 ≤ M a b) (conflict : V → V → Prop)
    (hsym : ∀ ⦃u v⦄, conflict u v → conflict v u) (n : ℕ) :
    let L := ((n + 1) + (n + 1)) + 2
    (∑ z : Fin L → V,
      if ∃ i j, i ≠ j ∧ conflict (z i) (z j) then (Classical.choose closedWeight_spec) M z else 0) ≤
    (L : ℝ) * ∑ a : V, ∑ b : V, ∑ c : V,
      M a b * (∑ x_b : Fin (n + 1) → _, if ∃ i_b : Fin (n + 2), conflict a (Fin.cons (α := fun _ => _) b x_b i_b) then (Classical.choose pathWeight_spec) M (n + 1) b x_b c else 0) * (M ^ (n + 1)) c a := by
  classical
  intro L
  let front : (Fin L → V) → Prop :=
    fun z => ∃ i : Fin (n + 2), conflict (z 0) (z ((⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (((n + 1) + (n + 1)) + 2))))
  let w : (Fin L → V) → ℝ := fun z_q => (Classical.choose closedWeight_spec) M z_q
  have hw (z : Fin L → V) : 0 ≤ w z := by simp only [w]; rw [cw_eq]; exact pathWeight_nonneg M hM _ _ _ _
  have hfront :
      (∑ z : Fin L → V, if front z then w z else 0) =
        ∑ a : V, ∑ b : V, ∑ c : V,
          M a b * (∑ x_b : Fin (n + 1) → _, if ∃ i_b : Fin (n + 2), conflict a (Fin.cons (α := fun _ => _) b x_b i_b) then (Classical.choose pathWeight_spec) M (n + 1) b x_b c else 0) * (M ^ (n + 1)) c a := by
    convert! sum_closedWeight_prefix M n (fun a x => ∃ i, conflict a (x i))
  calc
    _ ≤ ∑ z : Fin L → V, ∑ j : Fin L, if front (({ toFun := fun x_w i_w => x_w (i_w + j), invFun := fun x_w i_w => x_w (i_w - j), left_inv := fun x_w => funext fun _ => by simp, right_inv := fun x_w => funext fun _ => by simp } : (Fin _ → _) ≃ (Fin _ → _)) z) then w z else 0 := by
      apply sum_le_sum
      intro z _
      by_cases hb : ∃ i j, i ≠ j ∧ conflict (z i) (z j)
      · obtain ⟨j, hj⟩ := conflict_detected_by_translation conflict hsym n z hb
        have h : front (({ toFun := fun x_w i_w => x_w (i_w + j), invFun := fun x_w i_w => x_w (i_w - j), left_inv := fun x_w => funext fun _ => by simp, right_inv := fun x_w => funext fun _ => by simp } : (Fin _ → _) ≃ (Fin _ → _)) z) := hj
        simp only [if_pos hb]
        exact (le_of_eq (if_pos h).symm).trans
          (single_le_sum (f := fun j : Fin L => if front (({ toFun := fun x_w i_w => x_w (i_w + j), invFun := fun x_w i_w => x_w (i_w - j), left_inv := fun x_w => funext fun _ => by simp, right_inv := fun x_w => funext fun _ => by simp } : (Fin _ → _) ≃ (Fin _ → _)) z) then w z else 0)
            (fun k _ => by split <;> first | exact hw z | rfl) (mem_univ j))
      · simp only [if_neg hb]
        exact sum_nonneg fun j _ => by split <;> first | exact hw z | rfl
    _ = ∑ j : Fin L, ∑ z : Fin L → V, if front (({ toFun := fun x_w i_w => x_w (i_w + j), invFun := fun x_w i_w => x_w (i_w - j), left_inv := fun x_w => funext fun _ => by simp, right_inv := fun x_w => funext fun _ => by simp } : (Fin _ → _) ≃ (Fin _ → _)) z) then w z else 0 := sum_comm
    _ = ∑ _j : Fin L, ∑ z : Fin L → V, if front z then w z else 0 := by
      apply sum_congr rfl
      intro j _
      apply Fintype.sum_equiv (({ toFun := fun x_w i_w => x_w (i_w + j), invFun := fun x_w i_w => x_w (i_w - j), left_inv := fun x_w => funext fun _ => by simp, right_inv := fun x_w => funext fun _ => by simp } : (Fin _ → _) ≃ (Fin _ → _)))
      intro z
      rw [show w (({ toFun := fun x_w i_w => x_w (i_w + j), invFun := fun x_w i_w => x_w (i_w - j), left_inv := fun x_w => funext fun _ => by simp, right_inv := fun x_w => funext fun _ => by simp } : (Fin _ → _) ≃ (Fin _ → _)) z) = w z from closedWeight_translate M j z]
    _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hfront]


theorem exists_conflict_free_kernel_cycle {V : Type} [Fintype V] [Nonempty V]
    (M : Matrix V V ℝ) (w : V → ℝ) (hw : ∀ a, 0 < w a)
    (hM : ∀ u v, 0 ≤ M u v) (hrow : ∀ a, ∑ b : V, M a b = 1)
    (hbal : ∀ a b, w a * M a b = w b * M b a)
    (conflict : V → V → Prop) (hsym : ∀ ⦃u v⦄, conflict u v → conflict v u)
    (α : ℝ) (hα : 0 ≤ α)
    (hloc : ∀ u v, ∑ a : V, (if conflict a u then M v a else 0) ≤ α)
    (n : ℕ)
    (hsmall : (Fintype.card V : ℝ) * (4 * ((n + 2 : ℕ) : ℝ) ^ 3 * α) ^ (n + 2) < 1) :
    let L := ((n + 1) + (n + 1)) + 2
    ∃ x : Fin L → V, (∀ i, 0 < M (x i) (x (i + 1))) ∧
      ∀ i j, i ≠ j → ¬ conflict (x i) (x j) := by
  classical
  intro L
  let k := n + 2
  let T (j : ℕ) := Matrix.trace (M ^ (j + j))
  let K : ℝ := k
  let β := 4 * K ^ 3 * α
  let bad (x : Fin L → V) : Prop := ∃ i j, i ≠ j ∧ conflict (x i) (x j)
  let S := ∑ x : Fin L → V, if bad x then (Classical.choose closedWeight_spec) M x else 0
  let U := ∑ a : V, ∑ b : V, ∑ c : V,
    M a b * (∑ x_b : Fin (n + 1) → _, if ∃ i_b : Fin (n + 2), conflict a (Fin.cons (α := fun _ => _) b x_b i_b) then (Classical.choose pathWeight_spec) M (n + 1) b x_b c else 0) * (M ^ (n + 1)) c a
  have ht (j : ℕ) : 1 ≤ T j := one_le_even_trace M w hw hbal hrow j
  have htpos (j : ℕ) : 0 < T j := zero_lt_one.trans_le (ht j)
  have hcv (j : ℕ) : (T (j + 1)) ^ 2 ≤ T j * T (j + 2) := even_trace_logConvex M w hw hbal j
  have hk : 0 < k := by dsimp [k]; omega
  have hprev : k - 1 = n + 1 := rfl
  have hinterp := logConvex_nat_interpolation T htpos hcv hk
  have hzero : T 0 = (Fintype.card V : ℝ) := by simp [T, Matrix.trace_one]
  rw [hzero] at hinterp
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hβlt : β * T (k - 1) < T k := by
    have hp : (β * T (k - 1)) ^ k < (T k) ^ k := by
      calc
        _ = β ^ k * (T (k - 1)) ^ k := mul_pow _ _ _
        _ ≤ β ^ k * ((Fintype.card V : ℝ) * (T k) ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left hinterp (by positivity)
        _ = (Fintype.card V : ℝ) * β ^ k * (T k) ^ (k - 1) := by ring
        _ < 1 * (T k) ^ (k - 1) :=
          mul_lt_mul_of_pos_right hsmall (pow_pos (htpos k) _)
        _ ≤ _ := by
          rw [one_mul]
          exact pow_le_pow_right₀ (ht k) (Nat.sub_le _ _)
    by_contra! h
    exact (not_le_of_gt hp) (pow_le_pow_left₀ (htpos k).le h k)
  have hS : S ≤ (L : ℝ) * U := sum_badClosed_le_prefix M hM conflict hsym n
  have hS0 : 0 ≤ S := by
    apply sum_nonneg
    intro x _
    split <;> first | exact pathWeight_nonneg M hM _ _ _ _ | (rw [cw_eq]; exact pathWeight_nonneg M hM _ _ _ _) | rfl
  have hU : U ^ 2 ≤ K * α * T (k - 1) * T k := by
    rw [hprev]
    exact badHalfWalk_mass_square M w hw hM hrow hbal conflict α hα hloc n
  have hL : (L : ℝ) = 2 * K := by
    change (L : ℝ) = 2 * (k : ℝ)
    exact_mod_cast (show L = 2 * k by dsimp [L, k]; omega)
  have hSq : S ^ 2 < (T k) ^ 2 := by
    calc
      _ ≤ ((L : ℝ) * U) ^ 2 := pow_le_pow_left₀ hS0 hS 2
      _ = (L : ℝ) ^ 2 * U ^ 2 := mul_pow _ _ _
      _ ≤ (L : ℝ) ^ 2 * (K * α * T (k - 1) * T k) :=
        mul_le_mul_of_nonneg_left hU (sq_nonneg _)
      _ = (β * T (k - 1)) * T k := by rw [hL]; dsimp [β]; ring
      _ < _ := by simpa only [pow_two] using mul_lt_mul_of_pos_right hβlt (htpos k)
  have hbad : S < T k := by
    by_contra! h
    exact (not_le_of_gt hSq) (pow_le_pow_left₀ (htpos k).le h 2)
  have hsum : ∑ x : Fin L → V, (Classical.choose closedWeight_spec) M x = T k := sum_closedWeight_eq_trace M n
  obtain ⟨x, hx, hxb⟩ : ∃ x : Fin L → V, (Classical.choose closedWeight_spec) M x ≠ 0 ∧ ¬ bad x := by
    by_contra! h
    apply (not_le_of_gt hbad)
    rw [← hsum]
    apply sum_le_sum
    intro x _
    by_cases hb : bad x
    · exact le_of_eq (if_pos hb).symm
    · have hx : (Classical.choose closedWeight_spec) M x = 0 := by
        by_contra hn
        exact hb (h x hn)
      simp [hx]
  refine ⟨x, fun i => ?_, fun i j hij hc => hxb ⟨i, j, hij, hc⟩⟩
  by_contra! hi
  have hz : M (x i) (x (i + 1)) = 0 := le_antisymm hi (hM _ _)
  apply hx
  rw [closedWeight_eq_prod]
  exact Finset.prod_eq_zero (mem_univ i) hz


theorem conflict_free_cycle_of_ratio {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hdegree : ∀ v, 0 < G.degree v)
    (conflict : V → V → Prop) (hsym : ∀ ⦃u v⦄, conflict u v → conflict v u)
    (α : ℝ) (hα : 0 ≤ α)
    (hloc : ∀ u v, (((G.neighborFinset v).filter (conflict u)).card : ℝ) ≤ α * G.degree v)
    (n : ℕ)
    (hsmall : (Fintype.card V : ℝ) * (4 * ((n + 2 : ℕ) : ℝ) ^ 3 * α) ^ (n + 2) < 1) :
    let L := ((n + 1) + (n + 1)) + 2
    ∃ f : cycleGraph L →g G, ∀ i j, i ≠ j → ¬ conflict (f i) (f j) := by
  classical
  intro L
  let w (v : V) : ℝ := G.degree v
  let M : Matrix V V ℝ := fun u v => if G.Adj u v then (w u)⁻¹ else 0
  have hw (v : V) : 0 < w v := by
    dsimp [w]
    exact_mod_cast hdegree v
  have hM (u v : V) : 0 ≤ M u v := by
    change 0 ≤ if G.Adj u v then (w u)⁻¹ else 0
    split <;> positivity
  have hrow (u : V) : ∑ v : V, M u v = 1 := by
    calc
      _ = ∑ _v ∈ G.neighborFinset u, (w u)⁻¹ := by
        have hf : G.neighborFinset u = univ.filter (G.Adj u) := by
          ext v
          simp [mem_neighborFinset]
        rw [hf, sum_filter]
      _ = _ := by
        rw [sum_const, nsmul_eq_mul, card_neighborFinset_eq_degree]
        exact mul_inv_cancel₀ (hw u).ne'
  have hbal (u v : V) : w u * M u v = w v * M v u := by
    by_cases h : G.Adj u v
    · simp only [M, if_pos h, if_pos h.symm, mul_inv_cancel₀ (hw u).ne', mul_inv_cancel₀ (hw v).ne']
    · have h' : ¬ G.Adj v u := fun hv => h hv.symm
      simp [M, h, h']
  have hlocM (u v : V) : ∑ a : V, (if conflict a u then M v a else 0) ≤ α := by
    let S := (G.neighborFinset v).filter (conflict u)
    have hS : S = univ.filter (fun a => G.Adj v a ∧ conflict u a) := by
      ext a
      simp [S, mem_neighborFinset]
    have hnum : (S.card : ℝ) ≤ α * w v := hloc u v
    calc
      _ = ∑ _a ∈ S, (w v)⁻¹ := by
        rw [hS, sum_filter]
        apply sum_congr rfl
        intro a _
        by_cases hv : G.Adj v a <;> by_cases hu : conflict u a
        · simp [M, hv, hu, hsym hu]
        · have h' : ¬ conflict a u := fun hc => hu (hsym hc)
          simp [M, hv, hu, h']
        · simp [M, hv]
        · simp [M, hv]
      _ ≤ α := by
        rw [sum_const, nsmul_eq_mul, ← div_eq_mul_inv]
        exact (div_le_iff₀ (hw v)).2 hnum
  obtain ⟨x, hpos, hdisj⟩ := exists_conflict_free_kernel_cycle M w hw hM hrow hbal
    conflict hsym α hα hlocM n hsmall
  have hpath (i : Fin L) : G.Adj (x i) (x (i + 1)) := by
    by_contra hi
    simpa only [M, if_neg hi, lt_self_iff_false] using hpos i
  refine ⟨⟨x, fun {i j} hij => ?_⟩, hdisj⟩
  rcases cycleGraph_adj.mp hij with h | h
  · have he : i = j + 1 := sub_eq_iff_eq_add'.mp h
    rw [he]
    exact (hpath j).symm
  · have he : j = i + 1 := sub_eq_iff_eq_add'.mp h
    rw [he]
    exact hpath i


theorem sparseConflictCycles_of_ratio (N b c n : ℕ) (hb : 0 < b)
    (hsmall : (N : ℝ) * (4 * ((n + 2 : ℕ) : ℝ) ^ 3 * (c : ℝ) / b) ^ (n + 2) < 1) :
    (∀ (W : Type) [Fintype W], Fintype.card W ≤ N →
    ∀ (G : SimpleGraph W) (conflict : W → W → Prop),
      (∀ ⦃x y⦄, conflict x y → conflict y x) → G.edgeFinset.Nonempty →
      (∀ u v, b * ((G.neighborFinset v).filter (conflict u)).card ≤ c * G.degree v) →
      ∃ f : cycleGraph (((n + 1) + (n + 1)) + 2) →g G, ∀ i j, i ≠ j → ¬ conflict (f i) (f j)) := by
  classical
  intro V _ hcard G conflict hsym he hloc
  let S := G.support
  let B := G.induce S
  let conflictS (u v : S) := conflict u.val v.val
  have hne : Nonempty S := by
    obtain ⟨e, he⟩ := he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have h : G.Adj a b := by simpa using he
      exact ⟨⟨a, h.mem_support_left⟩⟩
  have hfilter (v : S) (P : V → Prop) :
      (((B.neighborFinset v).filter fun u => P u.val).map (Function.Embedding.subtype _)) =
        (G.neighborFinset v.val).filter P := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      obtain ⟨hd, hp⟩ := mem_filter.mp hy
      have hBy : B.Adj v y := (mem_neighborFinset B v y).mp hd
      exact mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr hBy, hp⟩
    · intro hx
      obtain ⟨hd, hp⟩ := mem_filter.mp hx
      have ha : G.Adj v.val x := (mem_neighborFinset _ _ _).mp hd
      let y : S := ⟨x, ha.mem_support_right⟩
      exact mem_map.mpr ⟨y, mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr ha, hp⟩, rfl⟩
  have hdeg (v : S) : B.degree v = G.degree v.val := by
    have h := congrArg Finset.card (hfilter v (fun _ => True))
    simpa [card_map, card_neighborFinset_eq_degree] using h
  have hdegree (v : S) : 0 < B.degree v := by
    rw [hdeg]
    exact (G.degree_pos_iff_mem_support v.val).mpr v.property
  have hlocS (u v : S) :
      (((B.neighborFinset v).filter (conflictS u)).card : ℝ) ≤ ((c : ℝ) / b) * B.degree v := by
    have h := congrArg Finset.card (hfilter v (conflict u.val))
    have h' : ((B.neighborFinset v).filter (conflictS u)).card =
        ((G.neighborFinset v.val).filter (conflict u.val)).card := by
      simpa only [card_map, conflictS] using h
    rw [h', hdeg, div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast hb)]
    have hh : (b : ℝ) * ((G.neighborFinset v.val).filter (conflict u.val)).card ≤
        (c : ℝ) * G.degree v.val := by
      exact_mod_cast hloc u.val v.val
    simpa only [mul_comm (b : ℝ)] using hh
  have hS : (Fintype.card S : ℝ) ≤ N := by
    exact_mod_cast (Fintype.card_le_of_injective (fun u : S => (u : V)) Subtype.val_injective).trans hcard
  have hsmall' : (Fintype.card S : ℝ) * (4 * ((n + 2 : ℕ) : ℝ) ^ 3 *
      ((c : ℝ) / b)) ^ (n + 2) < 1 := by
    rw [← mul_div_assoc]
    exact (mul_le_mul_of_nonneg_right hS (by positivity)).trans_lt hsmall
  obtain ⟨f, hf⟩ := conflict_free_cycle_of_ratio B hdegree conflictS
    (fun {u v} h => hsym h) ((c : ℝ) / b) (by positivity) hlocS n hsmall'
  exact ⟨(Copy.induce G S).toHom.comp f, hf⟩

theorem card_filter_eq_le_one {V : Type} (s : Finset V) (b : V) :
    (s.filter (· = b)).card ≤ 1 := by
  classical
  have hs : s.filter (· = b) ⊆ {b} := by
    intro x hx
    exact mem_singleton.mpr (mem_filter.mp hx).2
  simpa using card_le_card hs

theorem injective_of_packed_eq {V : Type} [Fintype V] {t : ℕ} {x : Fin t → V}
    (hx : x ∈ ((Fintype.piFinset (fun _ : Fin t => univ)).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ Eq (x_p i_p) (x_p j_p))) : Function.Injective x := by
  intro i j he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (mem_packedTuples.mp hx).2 i j h he
  · exact (mem_packedTuples.mp hx).2 j i h he.symm


theorem contains_even_cycle_blowup {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (t l θ : ℕ) (ht : 0 < t) (hθ : 0 < θ) (hθt : 4 * t ≤ θ) (d : ℝ)
    (hd : (t : ℝ) ≤ d) (hdeg : ∀ v, d ≤ (G.degree v : ℝ))
    (hpow : 10 * (θ : ℝ) * (Fintype.card V : ℝ) ^ (t - 1) ≤ (d - t) ^ t)
    (findCycle : (∀ (W : Type) [Fintype W], Fintype.card W ≤ (Fintype.card V ^ t) →
    ∀ (G : SimpleGraph W) (conflict : W → W → Prop),
      (∀ ⦃x y⦄, conflict x y → conflict y x) → G.edgeFinset.Nonempty →
      (∀ u v, θ * ((G.neighborFinset v).filter (conflict u)).card ≤ (8 * 2 ^ t * t ^ 2 * 1) * G.degree v) →
      ∃ f : cycleGraph l →g G, ∀ i j, i ≠ j → ¬ conflict (f i) (f j))) :
    (SimpleGraph.comap (Prod.fst : _ × Fin t → _) (cycleGraph l)) ⊑ G := by
  classical
  let P := ((Fintype.piFinset (fun _ : Fin t => (univ : Finset V))).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ Eq (x_p i_p) (x_p j_p))
  let Q (x y : Fin t → V) := ∀ i j, G.Adj (x i) (y j)
  let common (x : Fin t → V) := (univ : Finset V).filter fun v => ∀ i, G.Adj (x i) v
  let m : ℝ := Fintype.card V
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast Fintype.card_pos (α := V)
  let nh (v : V) := (univ : Finset V).filter fun f => G.Adj f v
  have hnh (v : V) : nh v = G.neighborFinset v := by
    ext f
    simp [nh, mem_neighborFinset, adj_comm]
  have hsum := sum_card_packed_lower univ univ_nonempty nh Eq 1 t d (by simpa using hd)
    (by
      calc
        _ = ∑ _v : V, d := by simp [sum_const, nsmul_eq_mul]
        _ ≤ _ := sum_le_sum (fun v _ => by
          simpa only [hnh, card_neighborFinset_eq_degree] using hdeg v))
    (fun v _ b _ => card_filter_eq_le_one (nh v) b)
  have hcount : (∑ v : V, ((((Fintype.piFinset (fun _ : Fin t => (nh v))).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ Eq (x_p i_p) (x_p j_p))).card : ℝ)) =
      ∑ x ∈ P, ((common x).card : ℝ) := by
    exact_mod_cast sum_card_packed_neighborhoods (univ : Finset V) G.Adj Eq t
  have havg : m * (d - t) ^ t ≤ ∑ x ∈ P, ((common x).card : ℝ) := by
    simpa only [card_univ, Nat.cast_one, mul_one, hcount] using hsum
  have hPne : P.Nonempty := by
    by_contra! h
    rw [h, sum_empty] at havg
    have hp := (show 0 < 10 * (θ : ℝ) * m ^ (t - 1) by positivity).trans_le hpow
    exact (not_lt_of_ge havg) (mul_pos hm hp)
  have hP : (P.card : ℝ) ≤ m ^ t := by
    have h := packed_size_le (univ : Finset V) Eq t
    rw [card_univ] at h
    dsimp [m]
    exact_mod_cast h
  have hmPow : m ^ t = m ^ (t - 1) * m :=
    (congrArg (fun k : ℕ => m ^ k) (show t = (t - 1) + 1 by omega)).trans (pow_succ _ _)
  have hmean : (P.card : ℝ) * (10 * θ) ≤ ∑ x ∈ P, ((common x).card : ℝ) := by
    calc
      _ ≤ m ^ t * (10 * θ) := mul_le_mul_of_nonneg_right hP (by positivity)
      _ = m * (10 * θ * m ^ (t - 1)) := by rw [hmPow]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hpow hm.le).trans havg
  have hcap (x : Fin t → V) (_ : x ∈ P) (b : V) :
      ((common x).filter fun a => a = b).card ≤ 2 * 1 :=
    (card_filter_eq_le_one (common x) b).trans (by norm_num)
  have hs := sum_packing_degrees_of_average P hPne common Eq 1 θ ht hθ
    (by simpa using hθt) hmean hcap
  have hneigh (x : Fin t → V) : P.filter (Q x) = ((Fintype.piFinset (fun _ : Fin t => (common x))).filter fun x_p => ∀ i_p j_p, i_p < j_p → ¬ Eq (x_p i_p) (x_p j_p)) := by
    ext y
    simp only [P, Q, common, mem_filter, mem_packedTuples, Fintype.mem_piFinset, mem_univ, true_and]
    tauto
  have hsym ⦃x y⦄ (h : Q x y) : Q y x := fun i j => (h j i).symm
  have hirr : ∀ x, ¬ Q x x := by
    intro x h
    exact G.irrefl (h ⟨0, ht⟩ ⟨0, ht⟩)
  obtain ⟨U, hu, hne, hU⟩ := exists_sparse_tuple_core Eq t 1 θ ht hθ
    (by simpa using hθt) Q common hsym hirr (fun x => by convert! hneigh x) hcap hs
  obtain ⟨x, hx, hstep, hdisj⟩ := exists_cycle_of_sparse_tuple_core Eq t l θ _
    Q (fun {_ _} h => h.symm) hsym hirr findCycle U hu hne
    (fun z hz => (hU z hz).1) (fun z hz => (hU z hz).2)
  refine ⟨⟨⟨fun p => x p.1 p.2, ?_⟩, ?_⟩⟩
  · rintro ⟨i, a⟩ ⟨j, b⟩ hij
    exact hstep i j hij a b
  · rintro ⟨i, a⟩ ⟨j, b⟩ he
    have he' : x i a = x j b := he
    have hij : i = j := by
      by_contra hne
      exact hdisj i j hne ⟨a, b, he'.symm⟩
    subst j
    exact Prod.ext rfl (injective_of_packed_eq (hx i) he')

theorem eventually_even_scales (t : ℕ) (ht : 0 < t) (ε : ℝ) (hε : 0 < ε) :
    let a := 1 - 1 / (t : ℝ) + ε
    let c : ℕ := 8 * 2 ^ t * t ^ 2 * 1
    ∃ k : ℕ, ∀ᶠ m : ℕ in atTop, ∃ θ : ℕ,
      0 < θ ∧ 4 * t ≤ θ ∧ (t : ℝ) ≤ 20 * t * (m : ℝ) ^ a ∧
      10 * (θ : ℝ) * (m : ℝ) ^ (t - 1) ≤ (20 * (t : ℝ) * (m : ℝ) ^ a - t) ^ t ∧
      ((m ^ t : ℕ) : ℝ) * (4 * ((k + 2 : ℕ) : ℝ) ^ 3 * (c : ℝ) / θ) ^ (k + 2) < 1 := by
  intro a c
  let δ := (t : ℝ) * ε / 2
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t from ht)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have ha : 0 ≤ a := by
    have hh := (div_le_one htR).2 ht1
    dsimp [a]
    linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((t : ℝ) / δ)
  let j := k + 2
  let K : ℝ := j
  let η := δ * K - t
  have hη : 0 < η := by
    have hh := (div_lt_iff₀ hδ).mp hk
    dsimp [η, K, j]
    rw [Nat.cast_add]
    nlinarith only [hh, hδ]
  let B := 8 * K ^ 3 * (c : ℝ)
  have hlimδ : Tendsto (fun m : ℕ => (m : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hlimη : Tendsto (fun m : ℕ => (m : ℝ) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  refine ⟨k, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlimδ.eventually_ge_atTop (8 * (t : ℝ) + 2), hlimη.eventually_gt_atTop (B ^ j)] with m hm hδm hηm
  let θ := ⌊(m : ℝ) ^ δ⌋₊
  let mR : ℝ := m
  have hmR : 1 ≤ mR := by dsimp [mR]; exact_mod_cast hm
  have hmpos : 0 < mR := zero_lt_one.trans_le hmR
  have hθupper : (θ : ℝ) ≤ mR ^ δ := Nat.floor_le (by positivity)
  have hθlower : mR ^ δ / 2 ≤ θ := by
    have hf := Nat.lt_floor_add_one (mR ^ δ)
    change mR ^ δ < (θ : ℝ) + 1 at hf
    change 8 * (t : ℝ) + 2 ≤ mR ^ δ at hδm
    linarith
  have hθt : 4 * t ≤ θ := by
    have h : 4 * (t : ℝ) ≤ θ := by
      change 8 * (t : ℝ) + 2 ≤ mR ^ δ at hδm
      linarith only [hδm, hθlower]
    exact_mod_cast h
  have hθ : 0 < θ := by omega
  have hθR : (0 : ℝ) < θ := by exact_mod_cast hθ
  let d := 20 * (t : ℝ) * mR ^ a
  have hd : 2 * (t : ℝ) ≤ d := by
    have h := mul_le_mul_of_nonneg_left (Real.one_le_rpow hmR ha) (by positivity : 0 ≤ 20 * (t : ℝ))
    dsimp [d]
    linarith only [h, htR]
  have hpower : 10 * (θ : ℝ) * mR ^ (t - 1) ≤ (d - t) ^ t := by
    have hconst : (10 : ℝ) ≤ (10 * (t : ℝ)) ^ t :=
      (show (10 : ℝ) ≤ 10 * (t : ℝ) by linarith only [ht1]).trans
        (le_self_pow₀ (by linarith only [ht1]) (by omega))
    have hθeps : (θ : ℝ) ≤ mR ^ ((t : ℝ) * ε) :=
      hθupper.trans (Real.rpow_le_rpow_of_exponent_le hmR (by dsimp [δ]; nlinarith only [mul_pos htR hε]))
    have hpow : (mR ^ a) ^ t = mR ^ (a * (t : ℝ)) := by
      rw [Real.rpow_mul hmpos.le, Real.rpow_natCast]
    have hexp : a * (t : ℝ) = ((t - 1 : ℕ) : ℝ) + (t : ℝ) * ε := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      dsimp [a]
      field_simp [htR.ne']
    calc
      _ ≤ (10 * (t : ℝ)) ^ t * mR ^ ((t : ℝ) * ε) * mR ^ (t - 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hconst hθeps hθR.le (by positivity)) (by positivity)
      _ = (d / 2) ^ t := by
        have hd' : d / 2 = (10 * (t : ℝ)) * mR ^ a := by dsimp [d]; ring
        rw [hd', mul_pow (10 * (t : ℝ)) (mR ^ a), hpow, hexp, Real.rpow_add hmpos, Real.rpow_natCast]
        ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith only [hd]) _
  refine ⟨θ, hθ, hθt, by exact le_trans (by linarith only [htR]) hd, hpower, ?_⟩
  have hratio : 4 * K ^ 3 * (c : ℝ) / θ ≤ B / mR ^ δ := by
    have hdv : (1 : ℝ) / θ ≤ 2 / mR ^ δ := by
      rw [div_le_div_iff₀ hθR (Real.rpow_pos_of_pos hmpos _)]
      linarith only [hθlower]
    calc
      _ = (4 * K ^ 3 * (c : ℝ)) * (1 / θ) := by ring
      _ ≤ (4 * K ^ 3 * (c : ℝ)) * (2 / mR ^ δ) :=
        mul_le_mul_of_nonneg_left hdv (by positivity)
      _ = _ := by dsimp [B]; ring
  have hmδ : (mR ^ δ) ^ j = mR ^ (δ * K) := by
    rw [show K = (j : ℝ) from rfl, Real.rpow_mul hmpos.le, Real.rpow_natCast]
  have hfinal : mR ^ t * (B / mR ^ δ) ^ j < 1 := by
    have he : mR ^ t / (mR ^ δ) ^ j = (mR ^ η)⁻¹ := by
      rw [hmδ, ← Real.rpow_natCast, ← Real.rpow_sub hmpos, ← Real.rpow_neg hmpos.le]
      congr 1
      dsimp [η]
      ring
    calc
      _ = B ^ j * (mR ^ t / (mR ^ δ) ^ j) := by rw [div_pow]; ring
      _ = B ^ j / mR ^ η := by rw [he, div_eq_mul_inv]
      _ < _ := (div_lt_one (Real.rpow_pos_of_pos hmpos _)).2 hηm
  rw [Nat.cast_pow]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio j) (by positivity)).trans_lt hfinal


theorem even_cycle_blowup_bound (t : ℕ) (ht : 0 < t) (ε : ℝ) (hε : 0 < ε) :
    ∃ l : ℕ, 4 ≤ l ∧ Even l ∧
      (fun m : ℕ => (extremalNumber m ((SimpleGraph.comap (Prod.fst : _ × Fin t → _) (cycleGraph l))) : ℝ)) =O[atTop]
        fun m : ℕ => (m : ℝ) ^ (2 - 1 / (t : ℝ) + ε) := by
  classical
  let a := 1 - 1 / (t : ℝ) + ε
  let c : ℕ := 8 * 2 ^ t * t ^ 2 * 1
  obtain ⟨k, he⟩ := eventually_even_scales t ht ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  let l := ((k + 1) + (k + 1)) + 2
  refine ⟨l, by dsimp [l]; omega, ⟨k + 2, by dsimp [l]; omega⟩, ?_⟩
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t from ht)
  have ha : 0 ≤ a := by
    have hh := (div_le_one (by positivity : 0 < (t : ℝ))).2 ht1
    dsimp [a]
    linarith
  let C : ℝ := N + 20 * t
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb := extremal_of_degree_threshold ((SimpleGraph.comap (Prod.fst : _ × Fin t → _) (cycleGraph l))) ha hC (by
    intro V _ _ G hd
    let m := Fintype.card V
    have hm : 1 ≤ m := Fintype.card_pos (α := V)
    have hmR : 1 ≤ (m : ℝ) := by exact_mod_cast hm
    by_cases hmN : N ≤ m
    · obtain ⟨θ, hθ, hθt, hdeg, hp, hsmall⟩ := hN m hmN
      have hdeg' (v : V) : 20 * (t : ℝ) * (m : ℝ) ^ a ≤ (G.degree v : ℝ) := by
        apply le_of_lt
        exact (mul_le_mul_of_nonneg_right (by dsimp [C]; exact le_add_of_nonneg_left (by positivity) : 20 * (t : ℝ) ≤ C)
          (by positivity)).trans_lt (hd v)
      exact contains_even_cycle_blowup G t l θ ht hθ hθt _ hdeg hdeg' hp
        (sparseConflictCycles_of_ratio (m ^ t) θ c k hθ hsmall)
    · obtain ⟨v⟩ := (inferInstance : Nonempty V)
      have hc : (N : ℝ) ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (by positivity)
      have hpow : 1 ≤ (m : ℝ) ^ a := Real.one_le_rpow hmR ha
      have hn : (m : ℝ) ≤ N := by exact_mod_cast (show m ≤ N by omega)
      have hv : (G.degree v : ℝ) < m := by exact_mod_cast G.degree_lt_card_verts v
      have hcontra : (m : ℝ) ≤ C * (m : ℝ) ^ a :=
        (hn.trans hc).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hC)
      exact (not_lt_of_ge hcontra) ((hd v).trans hv) |>.elim)
  have hExp : a + 1 = 2 - 1 / (t : ℝ) + ε := by dsimp [a]; ring
  simpa only [hExp] using hb

theorem regular_witness_on_fin {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (r : ℕ) (hr : G.IsRegularOfDegree r) (f : ℕ → ℝ)
    (hG : (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] f) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsRegularOfDegree r ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] f := by
  classical
  let q := Fintype.card V
  let e : V ≃ Fin q := Fintype.equivFin V
  let H := G.map e
  let iso : G ≃g H := Iso.map e G
  refine ⟨q, H, Fintype.card_pos, ?_, ?_⟩
  · intro v
    obtain ⟨u, hu⟩ : ∃ u, iso u = v := iso.toEquiv.surjective v
    rw [← hu]
    have he : H.degree (iso u) = G.degree u := by
      rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
      convert! (Fintype.card_congr (iso.mapNeighborSet u)).symm
    convert! he.trans (hr u)
  simpa only [extremalNumber_congr rfl iso.symm] using hG

theorem cycle_degree_const {l : ℕ} (hl : 3 ≤ l) (v : Fin l) :
    (cycleGraph l).degree v = 2 := by
  have hlen : l = (l - 3) + 3 := (Nat.sub_add_cancel hl).symm
  generalize l - 3 = k at hlen
  subst l
  convert! cycleGraph_degree_three_le (v := v)


theorem degree_deletePairedEdges {V : Type} [Fintype V] (G : SimpleGraph V) (f : V → V)
    (hf : Function.Involutive f) (hadj : ∀ u, G.Adj u (f u)) (v : V) :
    (({ Adj := fun u_d v_d => G.Adj u_d v_d ∧ v_d ≠ f u_d, symm := ⟨fun u_d v_d (h_d : G.Adj u_d v_d ∧ v_d ≠ f u_d) => (⟨h_d.1.symm, fun he_d => h_d.2 (by rw [he_d, hf v_d])⟩ : G.Adj v_d u_d ∧ u_d ≠ f v_d)⟩, loopless := ⟨fun x_d (h_d : G.Adj x_d x_d ∧ x_d ≠ f x_d) => G.irrefl h_d.1⟩ } : SimpleGraph _)).degree v = G.degree v - 1 := by
  classical
  have hn : (({ Adj := fun u_d v_d => G.Adj u_d v_d ∧ v_d ≠ f u_d, symm := ⟨fun u_d v_d (h_d : G.Adj u_d v_d ∧ v_d ≠ f u_d) => (⟨h_d.1.symm, fun he_d => h_d.2 (by rw [he_d, hf v_d])⟩ : G.Adj v_d u_d ∧ u_d ≠ f v_d)⟩, loopless := ⟨fun x_d (h_d : G.Adj x_d x_d ∧ x_d ≠ f x_d) => G.irrefl h_d.1⟩ } : SimpleGraph _)).neighborFinset v = (G.neighborFinset v).erase (f v) := by
    ext u
    rw [mem_neighborFinset, mem_erase, mem_neighborFinset]
    exact and_comm
  rw [← card_neighborFinset_eq_degree, hn, card_erase_of_mem ((mem_neighborFinset _ _ _).mpr (hadj v)), card_neighborFinset_eq_degree]

theorem pairedCyclePos_exists (k : ℕ) : ∃ p : Fin (2 * k) → Fin (2 * k),
    Function.Involutive p ∧ ∀ i, (cycleGraph (2 * k)).Adj i (p i) := by
  let p : Fin (2 * k) → Fin (2 * k) := fun i =>
    ⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1, by
      have hi := i.isLt
      split_ifs <;> omega⟩
  refine ⟨p, ?_, ?_⟩
  · intro i
    apply Fin.ext
    simp only [p]
    split_ifs <;> omega
  · intro i
    rw [cycleGraph_adj']
    by_cases hi : i.val % 2 = 0
    · right
      have hle : i ≤ p i := by
        change i.val ≤ (if i.val % 2 = 0 then i.val + 1 else i.val - 1)
        simp [hi]
      rw [Fin.coe_sub_iff_le.mpr hle]
      simp [p, hi]
    · left
      have hle : p i ≤ i := by
        change (if i.val % 2 = 0 then i.val + 1 else i.val - 1) ≤ i.val
        simp [hi]
      rw [Fin.coe_sub_iff_le.mpr hle]
      simp only [p, if_neg hi]
      omega

theorem adjacent_degrees_bound (t : ℕ) (ht : 0 < t) (ε : ℝ) (hε : 0 < ε) :
    ∀ r, (r = 2 * t ∨ r = 2 * t - 1) →
      ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsRegularOfDegree r ∧
        (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
          fun n : ℕ => (n : ℝ) ^ (2 - 1 / (t : ℝ) + ε) := by
  classical
  obtain ⟨l, hl, he, hbound⟩ := even_cycle_blowup_bound t ht ε hε
  obtain ⟨k, hk⟩ := he
  have hlen : l = 2 * k := by omega
  clear hk
  subst l
  obtain ⟨G, hGdef⟩ : ∃ G : SimpleGraph (Fin (2 * k) × Fin t), G = SimpleGraph.comap (Prod.fst : Fin (2 * k) × Fin t → Fin (2 * k)) (cycleGraph (2 * k)) := ⟨_, rfl⟩
  rw [← hGdef] at hbound
  have hin : Nonempty (Fin (2 * k) × Fin t) :=
    ⟨(⟨0, by omega⟩, ⟨0, ht⟩)⟩
  have hreg : G.IsRegularOfDegree (2 * t) := by
    intro v
    subst hGdef
    calc
      _ = (cycleGraph (2 * k)).degree v.1 * t := by
        convert degree_independentBlowup (cycleGraph (2 * k)) t v using 2
        all_goals (try (congr 1; exact Subsingleton.elim _ _))
      _ = _ := by rw [cycle_degree_const (by omega)]
  intro r hr
  rcases hr with rfl | rfl
  · exact regular_witness_on_fin G _ hreg _ hbound
  obtain ⟨pp, hppi, hppa⟩ := pairedCyclePos_exists k
  let f (v : Fin (2 * k) × Fin t) := (pp v.1, v.2)
  have hf : Function.Involutive f := by
    intro v
    exact Prod.ext (hppi v.1) rfl
  have hpair (v : Fin (2 * k) × Fin t) : G.Adj v (f v) := by subst hGdef; exact hppa v.1
  obtain ⟨G', hG'⟩ : ∃ G' : SimpleGraph (Fin (2 * k) × Fin t), ∀ u v, G'.Adj u v ↔ G.Adj u v ∧ v ≠ f u :=
    ⟨({ Adj := fun u_d v_d => G.Adj u_d v_d ∧ v_d ≠ f u_d, symm := ⟨fun u_d v_d (h_d : G.Adj u_d v_d ∧ v_d ≠ f u_d) => (⟨h_d.1.symm, fun he_d => h_d.2 (by rw [he_d, hf v_d])⟩ : G.Adj v_d u_d ∧ u_d ≠ f v_d)⟩, loopless := ⟨fun x_d (h_d : G.Adj x_d x_d ∧ x_d ≠ f x_d) => G.irrefl h_d.1⟩ } : SimpleGraph (Fin (2 * k) × Fin t)), fun _ _ => Iff.rfl⟩
  have hreg' : G'.IsRegularOfDegree (2 * t - 1) := by
    intro v
    have hn : G'.neighborFinset v = (G.neighborFinset v).erase (f v) := by
      ext u
      rw [mem_neighborFinset, mem_erase, mem_neighborFinset, hG']
      exact and_comm
    rw [← card_neighborFinset_eq_degree, hn,
      card_erase_of_mem ((mem_neighborFinset _ _ _).mpr (hpair v)), card_neighborFinset_eq_degree, hreg v]
  have hle : G' ≤ G := fun u v h => ((hG' u v).mp h).1
  have hO : (fun n : ℕ => (extremalNumber n G' : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (2 - 1 / (t : ℝ) + ε) := by
    apply IsBigO.trans _ hbound
    refine isBigO_of_le _ fun n => ?_
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact_mod_cast (IsContained.of_le hle).extremalNumber_le (n := n)
  exact regular_witness_on_fin G' _ hreg' _ hO


theorem even_degree_case (r : ℕ) (hr : 3 ≤ r) (he : Even r) (ε : ℝ) (hε : 0 < ε) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsRegularOfDegree r ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (2 - 2 / (r : ℝ) + ε) := by
  obtain ⟨t, ht⟩ := he
  have heq : r = 2 * t := by omega
  have htpos : 0 < t := by omega
  obtain ⟨q, H, hq, hreg, hO⟩ := adjacent_degrees_bound t htpos ε hε r (Or.inl heq)
  have htR : (0 : ℝ) < t := by exact_mod_cast htpos
  have hdiv : 2 / (r : ℝ) = 1 / (t : ℝ) := by
    rw [heq, Nat.cast_mul, Nat.cast_two]
    field_simp
  exact ⟨q, H, hq, hreg, by simpa only [hdiv] using hO⟩


theorem odd_degree_with_error (r : ℕ) (hr : 3 ≤ r) (ho : Odd r) (ε : ℝ)
    (hε : 2 / ((r : ℝ) * ((r : ℝ) + 1)) < ε) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsRegularOfDegree r ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (2 - 2 / (r : ℝ) + ε) := by
  obtain ⟨t₀, ht₀⟩ := ho
  let t := t₀ + 1
  have ht : 0 < t := Nat.succ_pos _
  have heq : r + 1 = 2 * t := by dsimp [t]; omega
  have hr' : r = 2 * t - 1 := by omega
  let η := ε - 2 / ((r : ℝ) * ((r : ℝ) + 1))
  have hη : 0 < η := sub_pos.mpr hε
  obtain ⟨q, H, hq, hreg, hO⟩ := adjacent_degrees_bound t ht η hη r (Or.inr hr')
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have heR : (r : ℝ) + 1 = 2 * (t : ℝ) := by exact_mod_cast heq
  have hdiv : 1 / (t : ℝ) = 2 / ((r : ℝ) + 1) := by
    rw [heR]
    field_simp
  have hgap : 2 / (r : ℝ) - 2 / ((r : ℝ) + 1) = 2 / ((r : ℝ) * ((r : ℝ) + 1)) := by
    have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hrR.ne', hr1]
    ring
  have hexp : 2 - 1 / (t : ℝ) + η = 2 - 2 / (r : ℝ) + ε := by
    rw [hdiv]
    dsimp [η]
    linarith only [hgap]
  exact ⟨q, H, hq, hreg, by simpa only [hexp] using hO⟩

def H1 : Prop := ∀ ε : ℝ, 0 < ε →
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsRegularOfDegree 3 ∧
      (fun n : ℕ => (SimpleGraph.extremalNumber n H : ℝ)) =O[Filter.atTop]
        fun n : ℕ => (n : ℝ) ^ (2 - 2 / (3 : ℝ) + ε)

def H2 : Prop := ∀ t : ℕ, 2 ≤ t → ∀ ε : ℝ, 0 < ε →
    ε ≤ 2 / (((2 * t + 1 : ℕ) : ℝ) * (((2 * t + 1 : ℕ) : ℝ) + 1)) →
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsRegularOfDegree (2 * t + 1) ∧
      (fun n : ℕ => (SimpleGraph.extremalNumber n H : ℝ)) =O[Filter.atTop]
        fun n : ℕ => (n : ℝ) ^ (2 - 2 / ((2 * t + 1 : ℕ) : ℝ) + ε)

theorem main : H1 → H2 → type_of% @Erdos147.erdos_147.variants.janzer_conjecture := by
  intro h1 h2 r hr ε hε
  by_cases he : Even r
  · exact even_degree_case r hr he ε hε
  have ho : Odd r := Nat.not_even_iff_odd.mp he
  by_cases hlarge : 2 / ((r : ℝ) * ((r : ℝ) + 1)) < ε
  · exact odd_degree_with_error r hr ho ε hlarge
  obtain ⟨t, rfl⟩ := ho
  rcases Nat.lt_or_ge t 2 with ht | ht
  · have h3 : t = 1 := by omega
    subst h3
    have h := h1 ε hε
    norm_num at h ⊢
    exact h
  · exact h2 t ht ε hε (le_of_not_gt hlarge)

end OMA.R_Erdos147_erdos_147_variants_janzer_conjecture_R2
