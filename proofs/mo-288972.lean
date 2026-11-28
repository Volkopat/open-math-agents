import OMAStatements.S_mo_288972

namespace OMA.S_mo_288972
open Matrix Module Finset
open scoped Classical
private lemma chart_exists {n : ℕ} (V : Space n) : Nonempty (Chart V) := by
  classical
  let v (i : Fin n) : Module.Dual ℝ V := (LinearMap.proj i).comp V.subtype
  obtain ⟨κ,idx,hi,hspan,hli⟩ := exists_linearIndependent' ℝ v
  let : Fintype κ := Fintype.ofInjective idx hi
  let R : V →ₗ[ℝ] (κ→ℝ) := LinearMap.pi (v ∘ idx)
  have hR : Function.Injective R := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    let Z := LinearMap.ker (Module.Dual.eval ℝ V x)
    have hz : Submodule.span ℝ (Set.range (v ∘ idx)) ≤ Z := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact congrFun hx i
    rw [hspan] at hz
    apply Subtype.ext
    funext i
    exact hz (Submodule.subset_span (Set.mem_range_self (f := v) i))
  have hc : Fintype.card κ = finrank ℝ V := by
    apply le_antisymm
    · simpa only [Subspace.dual_finrank_eq] using hli.fintype_card_le_finrank
    · simpa using LinearMap.finrank_le_finrank_of_injective hR
  let c : Fin (finrank ℝ V) ≃ κ := Fintype.equivOfCardEq (by simp [hc])
  let e := LinearEquiv.ofBijective R ⟨hR,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hc])).mp hR⟩
  let S : (Fin (finrank ℝ V) → ℝ) ≃ₗ[ℝ] V :=
    (LinearEquiv.funCongrLeft ℝ ℝ c.symm).trans e.symm
  refine ⟨⟨⟨idx ∘ c,hi.comp c.injective⟩, S, ?_⟩⟩
  intro x j
  change R (e.symm _) (c j) = x j
  calc
    _ = ((LinearEquiv.funCongrLeft ℝ ℝ c.symm) x) (c j) := congrFun (e.apply_symm_apply _) _
    _ = _ := by change x (c.symm (c j))=x j;simp
private lemma chart_inj {n : ℕ} {V : Space n} (T : Chart V) {x y : V}
    (h : ∀ j, x.val (T.index j)=y.val (T.index j)) : x=y := by
  obtain ⟨u,rfl⟩ := T.solve.surjective x
  obtain ⟨v,rfl⟩ := T.solve.surjective y
  exact congrArg T.solve (funext (fun j => by simpa only [T.reads] using h j))

private lemma candidate_bound {n : ℕ} {V : Space n} (T : Chart V) (a : Row n) :
    (candidates T a).card ≤ 2^(finrank ℝ V-1) := by
  classical
  unfold candidates
  split_ifs with h
  · apply (card_filter_le ..).trans
    apply card_image_le.trans
    simp [Fintype.card_subtype_compl]
  · simp

private lemma candidate_valid {n : ℕ} {V : Space n} {T : Chart V} {a v : Row n}
    (hv : v ∈ candidates T a) : v ∈ V ∧ unitRow a v := by
  classical
  unfold candidates at hv
  split_ifs at hv
  · obtain ⟨hv,hu⟩ := mem_filter.mp hv
    obtain ⟨b,_,rfl⟩ := mem_image.mp hv
    exact ⟨Subtype.prop _,hu⟩
  · simp at hv

private lemma unitRow_neg {n : ℕ} {a v : Row n} (h : unitRow a v) : unitRow a (-v) := by
  exact ⟨by simpa using h.1,fun i => by simpa using h.2 i⟩

private lemma candidate_complete {n : ℕ} {V : Space n} (T : Chart V) {a v : Row n}
    (hv : v ∈ V) (hu : unitRow a v) : v ∈ candidates T a ∨ -v ∈ candidates T a := by
  classical
  have hnon : ∃ j, 0 < a (T.index j) := by
    by_contra! h
    have he : (⟨v,hv⟩ : V) = 0 := chart_inj T fun j => by
      change v (T.index j) = 0
      nlinarith [hu.2 (T.index j),h j,sq_nonneg (v (T.index j))]
    have hv0 : v=0 := congrArg Subtype.val he
    simpa [hv0] using hu.1
  let j := hnon.choose
  have H {w : Row n} (hw : w∈V) (hw' : unitRow a w) (hp : 0≤w (T.index j)) :
      w ∈ candidates T a := by
    let b (i : {i : Fin (finrank ℝ V) // i ≠ j}) : Bool := decide (0 ≤ w (T.index i))
    have he : decode T a j b = (⟨w,hw⟩ : V) := by
      apply chart_inj T
      intro i
      rw [decode,T.reads]
      by_cases hij : i=j
      · subst i;simp [← hw'.2 _,Real.sqrt_sq hp]
      · simp only [dif_neg hij,b,decide_eq_true_eq,← hw'.2 _,Real.sqrt_sq_eq_abs]
        by_cases hp' : 0 ≤ w (T.index i)
        · simp [hp',abs_of_nonneg hp']
        · simp [hp',abs_of_neg (lt_of_not_ge hp')]
    unfold candidates
    rw [dif_pos hnon]
    exact mem_filter.mpr ⟨mem_image.mpr ⟨b,mem_univ _,congrArg Subtype.val he⟩,hw'⟩
  by_cases hp : 0≤v (T.index j)
  · exact Or.inl (H hv hu hp)
  · exact Or.inr (H (V.neg_mem hv) (unitRow_neg hu) (by simpa using (le_of_not_ge hp)))

private lemma cut_dim {n : ℕ} {V : Space n} {a v : Row n} (hv : v∈V) (hu : unitRow a v) :
    finrank ℝ (nextSpace V v) < finrank ℝ V := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne inf_le_left
  intro h
  have : v ∈ nextSpace V v := by rw [show nextSpace V v=V from h];exact hv
  have hz : v ⬝ᵥ v=0 := this.2
  linarith [hu.1]

private lemma cut_neg {n : ℕ} (V : Space n) (v : Row n) : nextSpace V (-v)=nextSpace V v := by
  ext w
  change (_ ∧ (-v) ⬝ᵥ w = 0) ↔ (_ ∧ v ⬝ᵥ w = 0)
  simp

private def fits {n m : ℕ} (V : Space n) (A O : Fin m → Row n) : Prop :=
  (∀ i, O i∈V ∧ ∀ k, O i k^2=A i k) ∧ ∀ i j, O i ⬝ᵥ O j = if i=j then 1 else 0

private lemma fits_cons {n m : ℕ} {V : Space n} {A : Fin (m+1) → Row n}
    {v : Row n} {O : Fin m → Row n} :
    fits V A (Fin.cons v O) ↔
      v∈V ∧ unitRow (A 0) v ∧ fits (nextSpace V v) (fun i => A i.succ) O := by
  classical
  constructor
  · rintro ⟨hm,ho⟩
    refine ⟨(hm 0).1,⟨by simpa using ho 0 0,(hm 0).2⟩,?_,?_⟩
    · intro i
      refine ⟨⟨(hm i.succ).1,?_⟩,(hm i.succ).2⟩
      change v ⬝ᵥ O i=0
      simpa [Ne.symm (Fin.succ_ne_zero i)] using ho 0 i.succ
    · intro i j;simpa using ho i.succ j.succ
  · rintro ⟨hv,hu,hm,ho⟩
    constructor
    · exact Fin.cases ⟨hv,hu.2⟩ fun i => ⟨(hm i).1.1,(hm i).2⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hu.1
      · have h : v ⬝ᵥ O _=0 := (hm j).1.2;simpa [Ne.symm (Fin.succ_ne_zero j)] using h
      · have h : v ⬝ᵥ O _=0 := (hm i).1.2;simpa [dotProduct_comm (O i) v] using h
      · simpa using ho i j
private lemma search_sound {n : ℕ} (T : ∀ V : Space n, Chart V) :
    ∀ (m) (V : Space n) (A : Fin m → Row n) (O : Fin m → Row n), O ∈ search T m V A → fits V A O := by
  classical
  intro m
  induction m with
  | zero =>
    intro V A O _
    exact ⟨fun i => i.elim0,fun i => i.elim0⟩
  | succ m ih =>
    intro V A O h
    obtain ⟨q,hq,hO⟩ := mem_biUnion.mp h
    obtain ⟨P,hP,rfl⟩ := mem_image.mp hO
    exact fits_cons.mpr ⟨(candidate_valid hq).1,(candidate_valid hq).2,ih _ _ _ hP⟩

private lemma search_complete {n : ℕ} (T : ∀ V : Space n, Chart V) :
    ∀ (m) (V : Space n) (A O : Fin m → Row n), fits V A O → (search T m V A).Nonempty := by
  classical
  intro m
  induction m with
  | zero => intro V A O _; simp [search]
  | succ m ih =>
    intro V A O h
    let v := O 0
    let P (i : Fin m) := O i.succ
    have he : Fin.cons v P=O := funext (Fin.cases rfl (fun _ => rfl))
    obtain ⟨hv,hu,hs⟩ := fits_cons.mp (he ▸ h : fits V A (Fin.cons v P))
    have H (w : Row n) (hw : w∈candidates (T V) (A 0)) (heq : nextSpace V w=nextSpace V v) :
        (search T (m+1) V A).Nonempty := by
      obtain ⟨Q,hQ⟩ := ih (nextSpace V v) _ P hs
      refine ⟨Fin.cons w Q, mem_biUnion.mpr ⟨w,hw,mem_image.mpr ⟨Q,?_,rfl⟩⟩⟩
      rwa [heq]
    exact (candidate_complete (T V) hv hu).elim (fun hv => H v hv rfl)
      (fun hw => H (-v) hw (cut_neg V v))

private lemma search_bound {n : ℕ} (T : ∀ V : Space n, Chart V) :
    ∀ (m) (V : Space n) (A : Fin m → Row n), (search T m V A).card ≤ 2^((finrank ℝ V).choose 2) := by
  classical
  intro m
  induction m with
  | zero => intro V A; simp only [search,card_singleton];exact Nat.one_le_pow _ _ (by decide)
  | succ m ih =>
    intro V A
    let d := finrank ℝ V
    let B := candidates (T V) (A 0)
    have hi (v : Row n) (hv : v∈B) :
        (search T m (nextSpace V v) (fun i => A i.succ)).card ≤ 2^((d-1).choose 2) := by
      obtain ⟨h1,h2⟩ := candidate_valid hv
      have h := cut_dim h1 h2
      apply (ih _ _).trans
      exact Nat.pow_le_pow_right (by decide) (Nat.choose_le_choose 2 (by dsimp [d];omega))
    have hcomb (r : ℕ) : r-1+(r-1).choose 2=r.choose 2 := by
      cases r <;> simp [Nat.choose_succ_succ]
    let branch (v : Row n) : Finset (Fin (m+1) → Row n) :=
      (search T m (nextSpace V v) (fun i => A i.succ)).image (Fin.cons v)
    have htree : search T (m+1) V A = B.biUnion branch := rfl
    rw [htree]
    calc
      (B.biUnion branch).card ≤ ∑ v ∈ B, (branch v).card :=
        Finset.card_biUnion_le (s := B) (t := branch)
      _ ≤ ∑ _v ∈ B, 2^((d-1).choose 2) := by
        apply sum_le_sum
        intro v hv
        dsimp only [branch]
        exact card_image_le.trans (hi v hv)
      _ = B.card * 2^((d-1).choose 2) := by simp
      _ ≤ 2^(d-1)*2^((d-1).choose 2) := Nat.mul_le_mul_right _ (candidate_bound (T V) (A 0))
      _ = _ := by rw [←pow_add,hcomb]

private lemma leaves_bound {n : ℕ} (T : ∀ V : Space n, Chart V) :
    ∀ (m) (V : Space n) (A : Fin m → Row n), leaves T m V A ≤ 2^((finrank ℝ V).choose 2) := by
  classical
  intro m
  induction m with
  | zero => intro V A;exact Nat.one_le_pow _ _ (by decide)
  | succ m ih =>
    intro V A
    let d := finrank ℝ V
    let B := candidates (T V) (A 0)
    let K := 2^((d-1).choose 2)
    let slots : ℕ := if ∃ j, 0<A 0 ((T V).index j) then 2^(d-1) else 1
    have hslots : slots ≤ 2^(d-1) := by dsimp [slots];split_ifs <;> simp [Nat.one_le_pow]
    have hb : B.card ≤ slots := by
      dsimp [slots]
      split_ifs with h
      · exact candidate_bound _ _
      · simp [B,candidates,h]
    have hk : 1 ≤ K := Nat.one_le_pow _ _ (by decide)
    have hs : (∑ v ∈ B, leaves T m (nextSpace V v) (fun i => A i.succ)) ≤ B.card*K := by
      rw [← Nat.nsmul_eq_mul,← Finset.sum_const]
      apply sum_le_sum
      intro v hv
      obtain ⟨h1,h2⟩ := candidate_valid hv
      have hd := cut_dim h1 h2
      exact (ih _ _).trans (Nat.pow_le_pow_right (by decide) (Nat.choose_le_choose 2 (by dsimp [d];omega)))
    have hcomb (r : ℕ) : r-1+(r-1).choose 2=r.choose 2 := by
      cases r <;> simp [Nat.choose_succ_succ]
    change slots - B.card + _ ≤ _
    calc
      _ ≤ (slots-B.card)*K + B.card*K :=
        Nat.add_le_add (Nat.le_mul_of_pos_right _ hk) hs
      _ = slots*K := by rw [←Nat.add_mul,Nat.sub_add_cancel hb]
      _ ≤ 2^(d-1)*K := Nat.mul_le_mul_right _ hslots
      _ = _ := by dsimp only [K];rw [← pow_add,hcomb]

private lemma fits_top {n : ℕ} {A O : Matrix (Fin n) (Fin n) ℝ} :
    fits ⊤ A O ↔ Witness A O := by
  classical
  constructor
  · rintro ⟨hs,ho⟩
    refine ⟨?_,fun i => (hs i).2⟩
    ext i j
    simpa [Matrix.mul_apply,Matrix.one_apply,dotProduct] using ho i j
  · rintro ⟨ho,hs⟩
    refine ⟨fun i => ⟨Submodule.mem_top,hs i⟩,?_⟩
    intro i j
    simpa [Matrix.mul_apply,Matrix.one_apply,dotProduct] using congrFun (congrFun ho i) j

private lemma orient_columns {n : ℕ} {A O : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (h : Witness A O) : ∃ W, fits ⊤ A W ∧ W 0 = fun j => Real.sqrt (A 0 j) := by
  classical
  let d (j : Fin (n+1)) : ℝ := if 0≤O 0 j then 1 else -1
  let W (i j : Fin (n+1)) := O i j * d j
  have hd (j : Fin (n+1)) : d j^2=1 := by unfold d;split_ifs <;> norm_num
  have hc (i j k : Fin (n+1)) : W i k * W j k = O i k * O j k := by
    dsimp [W]
    linear_combination (O i k*O j k)*hd k
  refine ⟨W,⟨fun i => ⟨Submodule.mem_top, fun j => by simp [W,mul_pow,hd,h.2]⟩,?_⟩,?_⟩
  · intro i j
    simpa only [dotProduct,hc] using (fits_top.mpr h).2 i j
  · funext j
    rw [←h.2,Real.sqrt_sq_eq_abs]
    unfold W d
    split_ifs with hp
    · simp [abs_of_nonneg hp]
    · simp [abs_of_neg (lt_of_not_ge hp)]

end OMA.S_mo_288972

open OMA.S_mo_288972 in
theorem OMA.solution : type_of% @OMA.S_mo_288972.main := by
  classical
  intro n
  let T (V : OMA.S_mo_288972.Space (n+1)) := (OMA.S_mo_288972.chart_exists V).some
  refine ⟨T,fun V a => OMA.S_mo_288972.candidate_bound (T V) a, OMA.S_mo_288972.leaves_bound T,?_⟩
  intro A
  let v : Row (n+1) := fun j => Real.sqrt (A 0 j)
  have hr : reconstruct T A =
      if unitRow (A 0) v then (search T n (nextSpace ⊤ v) (fun i => A i.succ)).image (Fin.cons v)
      else ∅ := rfl
  have hs : ∀ O ∈ reconstruct T A, Witness A O := by
    intro O hO
    rw [hr] at hO
    split_ifs at hO with hu
    · obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hO
      exact fits_top.mp (fits_cons.mpr ⟨Submodule.mem_top,hu,search_sound T _ _ _ _ hQ⟩)
    · simp at hO
  have hdim (hu : unitRow (A 0) v) : Module.finrank ℝ (nextSpace ⊤ v) ≤ n := by
    have hd := cut_dim (V := ⊤) (v := v) Submodule.mem_top hu
    have him : Module.finrank ℝ (⊤ : Space (n+1)) = n+1 := by simp
    omega
  refine ⟨?_,?_,hs,⟨fun ⟨O,hO⟩ => ⟨O,hs O hO⟩,?_⟩⟩
  · change (if unitRow (A 0) v then leaves T n (nextSpace ⊤ v) (fun i => A i.succ) else 1) ≤ _
    split_ifs with hu
    · exact (leaves_bound T n _ _).trans (Nat.pow_le_pow_right (by decide) (Nat.choose_le_choose 2 (hdim hu)))
    · exact Nat.one_le_pow _ _ (by decide)
  · rw [hr]
    split_ifs with hu
    · apply Finset.card_image_le.trans
      apply (OMA.S_mo_288972.search_bound T n _ _).trans
      exact Nat.pow_le_pow_right (by decide) (Nat.choose_le_choose 2 (hdim hu))
    · simp
  · rintro ⟨O,hO⟩
    obtain ⟨W,hW,hW0⟩ := OMA.S_mo_288972.orient_columns hO
    let Q (i : Fin n) := W i.succ
    have he : Fin.cons v Q=W := funext (Fin.cases hW0.symm (fun _ => rfl))
    rw [← he] at hW
    obtain ⟨_,hu,hQ⟩ := OMA.S_mo_288972.fits_cons.mp hW
    rw [hr,if_pos hu]
    exact (OMA.S_mo_288972.search_complete T n _ _ Q hQ).image _
