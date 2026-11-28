import OMAStatements.S_mo_279516

/-!
# Proof of MathOverflow 279516: Generic rank of a weighted projected matrix

For any `Q : Matrix (Fin n) (Fin n) ℝ` and `C : Matrix (Fin n) (Fin k) ℝ`, column `j` of
`transformed Q C Y = (Q * Y).hadamard C` lies in `columnSpace Q C j`, which immediately yields
the upper bound `(transformed Q C Y).rank ≤ bound Q C J` for every `Y` and `J : Finset (Fin k)`.

For the matching lower bound `r := sInf (Set.range (bound Q C))`, we show by induction on `r`
(using finite-union avoidance over `ℝ` and passing to the quotient by a single chosen vector)
that there exist vectors `v j ∈ columnSpace Q C j` spanning a subspace of dimension at least `r`,
hence a witness matrix `Y₀` with `r ≤ (transformed Q C Y₀).rank`. Extracting an `r × r`
submatrix with nonzero determinant gives a nonzero multivariate polynomial in the entries of `Y`,
whose zero set has Lebesgue measure zero (proved by Tonelli induction on the coordinates), and
therefore `μ`-measure zero for any `μ ≪ volume`.
-/

namespace OMA.Mo279516Proof

open MeasureTheory Matrix Finset Set
open scoped Classical

/-- Over `ℝ`, a subspace `V` cannot be covered by finitely many submodules none of which contains `V`. -/
private lemma exists_mem_not_mem_finset_submodules {E : Type*} [AddCommGroup E] [Module ℝ E]
    (V : Submodule ℝ E) (S : Finset (Submodule ℝ E)) (hS : ∀ W ∈ S, ¬ V ≤ W) :
    ∃ v ∈ V, ∀ W ∈ S, v ∉ W := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, V.zero_mem, by simp⟩
  | @insert W S hWS ih =>
    obtain ⟨u, huV, huS⟩ := ih (fun U hU => hS U (mem_insert_of_mem hU))
    by_cases huW : u ∉ W
    · exact ⟨u, huV, fun U hU => by
        rcases mem_insert.mp hU with rfl | hU'
        · exact huW
        · exact huS U hU'⟩
    · push_neg at huW
      have hVW : ¬ V ≤ W := hS W (mem_insert_self W S)
      obtain ⟨w, hwV, hwW⟩ : ∃ w ∈ V, w ∉ W := by
        by_contra h
        push_neg at h
        exact hVW h
      -- For each U ∈ S, at most one t : ℝ satisfies u + t • w ∈ U
      have huniq : ∀ U ∈ S, ∀ t₁ t₂ : ℝ, u + t₁ • w ∈ U → u + t₂ • w ∈ U → t₁ = t₂ := by
        intro U hU t₁ t₂ h1 h2
        by_contra hne
        have hdiff : (t₁ - t₂) • w ∈ U := by
          have : (t₁ - t₂) • w = (u + t₁ • w) - (u + t₂ • w) := by rw [sub_smul]; abel
          rw [this]
          exact U.sub_mem h1 h2
        have hwU : w ∈ U := by
          have : w = (t₁ - t₂)⁻¹ • ((t₁ - t₂) • w) := by
            rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
          rw [this]
          exact U.smul_mem _ hdiff
        have huU : u ∈ U := by
          have : u = (u + t₁ • w) - t₁ • w := by abel
          rw [this]
          exact U.sub_mem h1 (U.smul_mem _ hwU)
        exact huS U hU huU
      let bad : Finset ℝ := insert 0 (S.image fun U =>
        if h : ∃ t : ℝ, u + t • w ∈ U then Classical.choose h else 0)
      obtain ⟨t, _, ht⟩ := Set.Infinite.exists_notMem_finset (Set.infinite_univ (α := ℝ)) bad
      have ht0 : t ≠ 0 := fun h0 => ht (by simp [bad, h0])
      refine ⟨u + t • w, V.add_mem huV (V.smul_mem t hwV), fun U hU => ?_⟩
      rcases mem_insert.mp hU with rfl | hU'
      · intro hmem
        have htw : t • w ∈ U := by
          have : t • w = (u + t • w) - u := by abel
          rw [this]
          exact U.sub_mem hmem huW
        have : w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
        exact hwW (this ▸ U.smul_mem _ htw)
      · intro hmem
        have hex : ∃ s : ℝ, u + s • w ∈ U := ⟨t, hmem⟩
        have heq : t = Classical.choose hex := huniq U hU' t _ hmem (Classical.choose_spec hex)
        apply ht
        refine mem_insert_of_mem (mem_image.mpr ⟨U, hU', ?_⟩)
        simp [hex, heq]

/-- Rado-type selection theorem for a finite family of subspaces over `ℝ`:
if `r ≤ k - |J| + dim (J.sup V)` for all `J`, then there exist `v j ∈ V j` spanning at least `r` dimensions. -/
private lemma exists_vectors_finrank_ge {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] :
    ∀ (r k : ℕ) (V : Fin k → Submodule ℝ E),
      (∀ J : Finset (Fin k), r ≤ k - J.card + Module.finrank ℝ ↥(J.sup V)) →
      ∃ v : Fin k → E, (∀ j, v j ∈ V j) ∧ r ≤ Module.finrank ℝ ↥(Submodule.span ℝ (Set.range v)) := by
  intro r
  induction r generalizing E with
  | zero =>
    intro k V _
    exact ⟨fun _ => 0, fun j => (V j).zero_mem, Nat.zero_le _⟩
  | succ r ih =>
    intro k V hr
    have hk_pos : 0 < k := by
      have h0 := hr ∅
      rw [Finset.sup_empty, finrank_bot] at h0
      simp at h0
      omega
    have huniv_ne : Finset.univ.sup V ≠ ⊥ := by
      intro hbot
      have hu := hr Finset.univ
      rw [hbot, finrank_bot] at hu
      simp at hu
    obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin k, V j₀ ≠ ⊥ := by
      by_contra h
      push_neg at h
      apply huniv_ne
      rw [eq_bot_iff]
      exact Finset.sup_le fun j _ => by rw [h j]
    -- Tight subsets J not containing j₀
    let tight : Finset (Finset (Fin k)) :=
      Finset.univ.filter fun J => j₀ ∉ J ∧ k - J.card + Module.finrank ℝ ↥(J.sup V) = r + 1
    let badMods : Finset (Submodule ℝ E) := insert ⊥ (tight.image fun J => J.sup V)
    have hnotle : ∀ W ∈ badMods, ¬ V j₀ ≤ W := by
      intro W hW
      rcases mem_insert.mp hW with rfl | hW'
      · exact fun hle => hj₀ (le_bot_iff.mp hle)
      · obtain ⟨J, hJ, rfl⟩ := mem_image.mp hW'
        obtain ⟨_, hj₀J, htight⟩ := mem_filter.mp hJ
        intro hle
        have hsup : (insert j₀ J).sup V = J.sup V := by
          rw [Finset.sup_insert, sup_eq_right.mpr hle]
        have hcard : (insert j₀ J).card = J.card + 1 := Finset.card_insert_of_notMem hj₀J
        have hle_k : J.card + 1 ≤ k := by
          rw [← hcard]
          exact le_trans (Finset.card_le_univ _) (by simp)
        have hins := hr (insert j₀ J)
        rw [hsup, hcard] at hins
        omega
    obtain ⟨v₀, hv₀V, hv₀bad⟩ := exists_mem_not_mem_finset_submodules (V j₀) badMods hnotle
    have hv₀_ne : v₀ ≠ 0 := fun h0 => hv₀bad ⊥ (mem_insert_self _ _) (by simp [h0])
    have hv₀_tight : ∀ J : Finset (Fin k), j₀ ∉ J →
        k - J.card + Module.finrank ℝ ↥(J.sup V) = r + 1 → v₀ ∉ J.sup V := by
      intro J hj₀J ht
      exact hv₀bad (J.sup V) (mem_insert_of_mem (mem_image.mpr ⟨J, mem_filter.mpr ⟨mem_univ _, hj₀J, ht⟩, rfl⟩))
    let L : Submodule ℝ E := Submodule.span ℝ {v₀}
    have hL_dim : Module.finrank ℝ ↥L = 1 := finrank_span_singleton hv₀_ne
    let π : E →ₗ[ℝ] E ⧸ L := L.mkQ
    let e : Fin (k - 1) ≃ {j : Fin k // j ≠ j₀} :=
      Fintype.equivFinOfCardEq (by
        rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]) |>.symm
    let V' : Fin (k - 1) → Submodule ℝ (E ⧸ L) := fun i => (V (e i).val).map π
    have hr' : ∀ J' : Finset (Fin (k - 1)),
        r ≤ (k - 1) - J'.card + Module.finrank ℝ ↥(J'.sup V') := by
      intro J'
      let J : Finset (Fin k) := J'.image fun i => (e i).val
      have hinj : Function.Injective (fun i : Fin (k - 1) => (e i).val) :=
        Subtype.val_injective.comp e.injective
      have hJcard : J.card = J'.card := Finset.card_image_of_injective J' hinj
      have hj₀J : j₀ ∉ J := by
        intro hmem
        obtain ⟨i, _, hi⟩ := mem_image.mp hmem
        exact (e i).property hi
      have hJ_le_k : J.card + 1 ≤ k := by
        have : (insert j₀ J).card ≤ k := by
          simpa using Finset.card_le_univ (insert j₀ J)
        rwa [Finset.card_insert_of_notMem hj₀J] at this
      have hsup_eq : J'.sup V' = (J.sup V).map π := by
        have haux : ∀ s : Finset (Fin (k - 1)),
            s.sup V' = ((s.image fun i => (e i).val).sup V).map π := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp
          | insert a s ha ih =>
            rw [Finset.image_insert, Finset.sup_insert, Finset.sup_insert, Submodule.map_sup, ih]
        exact haux J'
      rw [hsup_eq]
      -- Rank-nullity for π restricted to J.sup V
      have hdim_rn : Module.finrank ℝ ↥((J.sup V).map π) + Module.finrank ℝ ↥((J.sup V) ⊓ L) =
          Module.finrank ℝ ↥(J.sup V) := by
        have hker : LinearMap.ker (π.domRestrict (J.sup V)) =
            ((J.sup V) ⊓ L).comap (J.sup V).subtype := by
          ext ⟨x, hx⟩
          simp [π, hx]
        have hrange : LinearMap.range (π.domRestrict (J.sup V)) = (J.sup V).map π := by
          ext y
          simp [Submodule.mem_map]
        have hrn := LinearMap.finrank_range_add_finrank_ker (π.domRestrict (J.sup V))
        rw [hrange, hker] at hrn
        have hcomap : Module.finrank ℝ ↥(((J.sup V) ⊓ L).comap (J.sup V).subtype) =
            Module.finrank ℝ ↥((J.sup V) ⊓ L) := by
          refine LinearEquiv.finrank_eq ?_
          exact Submodule.equivMapOfInjective (J.sup V).subtype Subtype.val_injective _ |>.trans
            (LinearEquiv.ofEq _ _ (by
              ext x
              simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype,
                Submodule.mem_inf, Subtype.exists, exists_and_right, exists_eq_right]
              tauto))
        rwa [hcomap] at hrn
      have hJbound := hr J
      by_cases hvJ : v₀ ∈ J.sup V
      · have hnot_tight : k - J.card + Module.finrank ℝ ↥(J.sup V) ≠ r + 1 :=
          fun ht => hv₀_tight J hj₀J ht hvJ
        have hinf_le : Module.finrank ℝ ↥((J.sup V) ⊓ L) ≤ 1 := by
          rw [← hL_dim]
          exact Submodule.finrank_mono inf_le_right
        omega
      · have hinf_bot : (J.sup V) ⊓ L = ⊥ := by
          rw [eq_bot_iff]
          intro x ⟨hxJ, hxL⟩
          dsimp only [L] at hxL
          rw [SetLike.mem_coe, Submodule.mem_span_singleton] at hxL
          rw [SetLike.mem_coe] at hxJ
          obtain ⟨c, rfl⟩ := hxL
          by_cases hc : c = 0
          · simp [hc]
          · exfalso
            apply hvJ
            have : v₀ = c⁻¹ • (c • v₀) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
            rw [this]
            exact (J.sup V).smul_mem _ hxJ
        rw [hinf_bot, finrank_bot, add_zero] at hdim_rn
        omega
    obtain ⟨w', hw'V, hw'dim⟩ := ih (k - 1) V' hr'
    have hlift : ∀ i : Fin (k - 1), ∃ u ∈ V (e i).val, π u = w' i := fun i =>
      Submodule.mem_map.mp (hw'V i)
    let v : Fin k → E := fun j =>
      if h : j = j₀ then v₀ else Classical.choose (hlift (e.symm ⟨j, h⟩))
    refine ⟨v, fun j => ?_, ?_⟩
    · dsimp only [v]
      split_ifs with h
      · subst h; exact hv₀V
      · have := (Classical.choose_spec (hlift (e.symm ⟨j, h⟩))).1
        simpa using this
    · let S := Submodule.span ℝ (Set.range v)
      have hv₀S : v₀ ∈ S := Submodule.subset_span ⟨j₀, by simp [v]⟩
      have hLS : L ≤ S := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv₀S)
      have hmap_ge : Submodule.span ℝ (Set.range w') ≤ S.map π := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine ⟨v (e i).val, Submodule.subset_span ⟨(e i).val, rfl⟩, ?_⟩
        dsimp only [v]
        rw [dif_neg (e i).property]
        have hspec := (Classical.choose_spec (hlift (e.symm ⟨(e i).val, (e i).property⟩))).2
        simpa using hspec
      have hdim_rn : Module.finrank ℝ ↥(S.map π) + Module.finrank ℝ ↥L = Module.finrank ℝ ↥S := by
        have hker : LinearMap.ker (π.domRestrict S) = L.comap S.subtype := by
          ext ⟨x, hx⟩
          simp [π]
        have hrange : LinearMap.range (π.domRestrict S) = S.map π := by
          ext y
          simp [Submodule.mem_map]
        have hrn := LinearMap.finrank_range_add_finrank_ker (π.domRestrict S)
        rw [hrange, hker] at hrn
        have hcomap : Module.finrank ℝ ↥(L.comap S.subtype) = Module.finrank ℝ ↥L := by
          refine LinearEquiv.finrank_eq ?_
          exact Submodule.equivMapOfInjective S.subtype Subtype.val_injective _ |>.trans
            (LinearEquiv.ofEq _ _ (by
              ext x
              simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype,
                Subtype.exists, exists_and_right, exists_eq_right]
              exact ⟨fun ⟨_, hxL⟩ => hxL, fun hxL => ⟨hLS hxL, hxL⟩⟩))
        rwa [hcomap] at hrn
      have h1 : r ≤ Module.finrank ℝ ↥(S.map π) := hw'dim.trans (Submodule.finrank_mono hmap_ge)
      change r + 1 ≤ Module.finrank ℝ ↥S
      omega

/-- Any matrix over `ℝ` of rank at least `r` has an `r × r` submatrix with nonzero determinant. -/
private lemma exists_submatrix_det_ne_zero {n k r : ℕ} (M : Matrix (Fin n) (Fin k) ℝ)
    (hr : r ≤ M.rank) :
    ∃ (row : Fin r → Fin n) (col : Fin r → Fin k), (M.submatrix row col).det ≠ 0 := by
  have hcol_span : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range M.col)) = M.rank := by
    rw [Matrix.rank, Matrix.range_mulVecLin]
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent ℝ (Set.range M.col)
  haveI : Fintype s := ((Set.finite_range M.col).subset hs_sub).fintype
  have hs_card : Fintype.card s = M.rank := by
    have h1 : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range (Subtype.val : s → Fin n → ℝ))) =
        Fintype.card s := finrank_span_eq_card hs_li
    rw [Subtype.range_coe] at h1
    rw [← h1, hs_span, hcol_span]
  have hr_le_s : r ≤ Fintype.card s := hr.trans_eq hs_card.symm
  let es := Fintype.equivFin s
  let col : Fin r → Fin k := fun j =>
    Classical.choose (hs_sub (es.symm ⟨j.val, lt_of_lt_of_le j.isLt hr_le_s⟩).property)
  have hcol_eq : ∀ j : Fin r, M.col (col j) = (es.symm ⟨j.val, lt_of_lt_of_le j.isLt hr_le_s⟩).val :=
    fun j => Classical.choose_spec (hs_sub (es.symm ⟨j.val, lt_of_lt_of_le j.isLt hr_le_s⟩).property)
  have hcol_li : LinearIndependent ℝ (fun j : Fin r => M.col (col j)) := by
    have hinj : Function.Injective (fun j : Fin r => es.symm ⟨j.val, lt_of_lt_of_le j.isLt hr_le_s⟩) := by
      intro a b hab
      have := es.symm.injective hab
      exact Fin.ext (by simpa using congrArg Fin.val this)
    have heq : (fun j : Fin r => M.col (col j)) =
        (Subtype.val ∘ fun j : Fin r => es.symm ⟨j.val, lt_of_lt_of_le j.isLt hr_le_s⟩) :=
      funext hcol_eq
    rw [heq]
    exact hs_li.comp _ hinj
  -- Now M1 = M.submatrix id col has rank r, so M1ᵀ has rank r
  let M1 : Matrix (Fin n) (Fin r) ℝ := M.submatrix id col
  have hM1_rank : M1.rank = r := by
    have h1 : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range M1.col)) = M1.rank := by
      rw [Matrix.rank, Matrix.range_mulVecLin]
    rw [← h1]
    have hM1col : M1.col = fun j => M.col (col j) := rfl
    rw [hM1col, finrank_span_eq_card hcol_li, Fintype.card_fin]
  have hM1T_rank : M1ᵀ.rank = r := by rw [Matrix.rank_transpose, hM1_rank]
  have hrow_span : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range M1ᵀ.col)) = r := by
    rw [← Matrix.range_mulVecLin]
    exact hM1T_rank
  obtain ⟨t, ht_sub, ht_span, ht_li⟩ := exists_linearIndependent ℝ (Set.range M1ᵀ.col)
  haveI : Fintype t := ((Set.finite_range M1ᵀ.col).subset ht_sub).fintype
  have ht_card : Fintype.card t = r := by
    have h1 : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range (Subtype.val : t → Fin r → ℝ))) =
        Fintype.card t := finrank_span_eq_card ht_li
    rw [Subtype.range_coe] at h1
    rw [← h1, ht_span, hrow_span]
  let et := Fintype.equivFinOfCardEq ht_card
  let row : Fin r → Fin n := fun i => Classical.choose (ht_sub (et.symm i).property)
  have hrow_eq : ∀ i : Fin r, M1ᵀ.col (row i) = (et.symm i).val :=
    fun i => Classical.choose_spec (ht_sub (et.symm i).property)
  have hrow_li : LinearIndependent ℝ (fun i : Fin r => (M.submatrix row col) i) := by
    have heq : (fun i : Fin r => (M.submatrix row col) i) = (Subtype.val ∘ et.symm) := by
      ext i j
      have := congrFun (hrow_eq i) j
      simpa [M1, Matrix.col, Matrix.submatrix] using this
    rw [heq]
    exact ht_li.comp et.symm et.symm.injective
  refine ⟨row, col, ?_⟩
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrow_li)).ne_zero

/-- The zero set of a nonzero multivariate polynomial on `Fin m → ℝ` has Lebesgue measure zero. -/
private lemma volume_mvPolynomial_zero_eq_zero :
    ∀ {m : ℕ} (p : MvPolynomial (Fin m) ℝ), p ≠ 0 →
      volume {x : Fin m → ℝ | MvPolynomial.eval x p = 0} = 0 := by
  intro m
  induction m with
  | zero =>
    intro p hp
    have heq : p = MvPolynomial.C (p.coeff 0) :=
      ((MvPolynomial.isEmptyRingEquiv ℝ (Fin 0)).symm_apply_apply p).symm
    have hc : MvPolynomial.eval (Fin.elim0 : Fin 0 → ℝ) p ≠ 0 := by
      intro h0
      rw [heq, MvPolynomial.eval_C] at h0
      exact hp (by rw [heq, h0, map_zero])
    have hempty : {x : Fin 0 → ℝ | MvPolynomial.eval x p = 0} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      have hx : x = Fin.elim0 := Subsingleton.elim _ _
      rwa [hx]
    rw [hempty, measure_empty]
  | succ m ih =>
    intro p hp
    let q : Polynomial (MvPolynomial (Fin m) ℝ) := MvPolynomial.finSuccEquiv ℝ m p
    have hq_ne : q ≠ 0 := fun h0 => hp ((MvPolynomial.finSuccEquiv ℝ m).injective (by simpa [q] using h0))
    obtain ⟨d, hd⟩ : ∃ d : ℕ, q.coeff d ≠ 0 := by
      by_contra h
      push_neg at h
      exact hq_ne (Polynomial.ext fun d => by simp [h d])
    let S : Set (Fin (m + 1) → ℝ) := {x | MvPolynomial.eval x p = 0}
    have hS_meas : MeasurableSet S :=
      (isClosed_eq (MvPolynomial.continuous_eval p) continuous_const).measurableSet
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have hmp : MeasurePreserving e.symm (volume.prod volume) volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
    have hvol : volume S = (volume.prod volume) (e.symm ⁻¹' S) := by
      rw [← hmp.map_eq, Measure.map_apply e.symm.measurable hS_meas]
    rw [hvol, Measure.prod_apply_symm (e.symm.measurable hS_meas)]
    have hae : ∀ᵐ y : Fin m → ℝ ∂volume,
        volume ((fun a => (a, y)) ⁻¹' (e.symm ⁻¹' S)) = 0 := by
      have hbad : volume {y : Fin m → ℝ | MvPolynomial.eval y (q.coeff d) = 0} = 0 := ih _ hd
      filter_upwards [compl_mem_ae_iff.mpr hbad] with y hy
      simp only [mem_compl_iff, mem_setOf_eq] at hy
      let qy : Polynomial ℝ := q.map (MvPolynomial.eval y)
      have hqy_ne : qy ≠ 0 := by
        intro h0
        have := congrArg (fun r => r.coeff d) h0
        simp [qy] at this
        exact hy this
      have hslice : (fun a => (a, y)) ⁻¹' (e.symm ⁻¹' S) = {a : ℝ | qy.IsRoot a} := by
        ext a
        have he_eq : e.symm (a, y) = Fin.cons a y := by
          ext i
          simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
        simp only [Set.mem_preimage, S, Set.mem_setOf_eq, Polynomial.IsRoot, he_eq]
        rw [MvPolynomial.eval_eq_eval_mv_eval']
      rw [hslice]
      exact (Polynomial.finite_setOf_isRoot hqy_ne).measure_zero volume
    rw [lintegral_congr_ae hae, lintegral_zero]

/-- The zero set of a nonzero polynomial in matrix entries has Lebesgue measure zero on `Fin n → Fin k → ℝ`. -/
private lemma volume_matrix_poly_zero_eq_zero {n k : ℕ}
    (p : MvPolynomial (Fin n × Fin k) ℝ) (hp : p ≠ 0) :
    volume {Y : Fin n → Fin k → ℝ | MvPolynomial.eval (Function.uncurry Y) p = 0} = 0 := by
  have hmp : ∀ {m : ℕ} (q : MvPolynomial (Fin m × Fin k) ℝ), q ≠ 0 →
      volume {Y : Fin m → Fin k → ℝ | MvPolynomial.eval (Function.uncurry Y) q = 0} = 0 := by
    intro m
    induction m with
    | zero =>
      intro q hq
      have heq : q = MvPolynomial.C (q.coeff 0) :=
        ((MvPolynomial.isEmptyRingEquiv ℝ (Fin 0 × Fin k)).symm_apply_apply q).symm
      have h0 : MvPolynomial.eval (Function.uncurry (Fin.elim0 : Fin 0 → Fin k → ℝ)) q ≠ 0 := by
        intro hval
        rw [heq, MvPolynomial.eval_C] at hval
        exact hq (by rw [heq, hval, map_zero])
      have hempty : {Y : Fin 0 → Fin k → ℝ | MvPolynomial.eval (Function.uncurry Y) q = 0} = ∅ := by
        ext Y
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
        have : Y = Fin.elim0 := Subsingleton.elim _ _
        rwa [this]
      rw [hempty, measure_empty]
    | succ m ih =>
      intro q hq
      let eSplit : Fin (m + 1) × Fin k ≃ Fin k ⊕ (Fin m × Fin k) :=
        { toFun := fun ⟨i, j⟩ => Fin.cases (Sum.inl j) (fun i' => Sum.inr (i', j)) i
          invFun := Sum.elim (fun j => (0, j)) (fun ⟨i', j⟩ => (i'.succ, j))
          left_inv := fun ⟨i, j⟩ => by
            cases i using Fin.cases <;> simp
          right_inv := fun x => by
            cases x with
            | inl j => simp
            | inr ij => simp }
      let q1 : MvPolynomial (Fin k) (MvPolynomial (Fin m × Fin k) ℝ) :=
        (MvPolynomial.sumAlgEquiv ℝ (Fin k) (Fin m × Fin k)) (MvPolynomial.rename eSplit q)
      have hq1_ne : q1 ≠ 0 := by
        intro h0
        apply hq
        have hren : MvPolynomial.rename eSplit q = 0 :=
          (MvPolynomial.sumAlgEquiv ℝ (Fin k) (Fin m × Fin k)).injective (by simpa [q1] using h0)
        exact MvPolynomial.rename_injective eSplit eSplit.injective (by simpa using hren)
      obtain ⟨d, hd⟩ : ∃ d : Fin k →₀ ℕ, MvPolynomial.coeff d q1 ≠ 0 := by
        by_contra h
        push_neg at h
        exact hq1_ne (MvPolynomial.ext _ _ fun d => by simp [h d])
      let S : Set (Fin (m + 1) → Fin k → ℝ) := {Y | MvPolynomial.eval (Function.uncurry Y) q = 0}
      have hcont : Continuous (fun Y : Fin (m + 1) → Fin k → ℝ =>
          MvPolynomial.eval (Function.uncurry Y) q) := by
        have hunc : Continuous (fun Y : Fin (m + 1) → Fin k → ℝ => Function.uncurry Y) :=
          continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
        exact (MvPolynomial.continuous_eval q).comp hunc
      have hS_meas : MeasurableSet S := (isClosed_eq hcont continuous_const).measurableSet
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Fin k → ℝ) 0
      have hmp_e : MeasurePreserving e.symm (volume.prod volume) volume :=
        (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => Fin k → ℝ) 0).symm
      have hvol : volume S = (volume.prod volume) (e.symm ⁻¹' S) := by
        rw [← hmp_e.map_eq, Measure.map_apply e.symm.measurable hS_meas]
      rw [hvol, Measure.prod_apply_symm (e.symm.measurable hS_meas)]
      have hae : ∀ᵐ rest : Fin m → Fin k → ℝ ∂volume,
          volume ((fun row0 => (row0, rest)) ⁻¹' (e.symm ⁻¹' S)) = 0 := by
        have hbad := ih (MvPolynomial.coeff d q1) hd
        filter_upwards [compl_mem_ae_iff.mpr hbad] with rest hrest
        simp only [mem_compl_iff, mem_setOf_eq] at hrest
        let qrest : MvPolynomial (Fin k) ℝ := MvPolynomial.map (MvPolynomial.eval (Function.uncurry rest)) q1
        have hqrest_ne : qrest ≠ 0 := by
          intro h0
          have := congrArg (MvPolynomial.coeff d) h0
          rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this
          exact hrest this
        have hslice : (fun row0 => (row0, rest)) ⁻¹' (e.symm ⁻¹' S) =
            {row0 : Fin k → ℝ | MvPolynomial.eval row0 qrest = 0} := by
          ext row0
          have he_eq : e.symm (row0, rest) = Fin.cons row0 rest := by
            ext i j
            simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
          simp only [Set.mem_preimage, S, Set.mem_setOf_eq, he_eq]
          suffices hev : MvPolynomial.eval (Function.uncurry (Fin.cons row0 rest)) q =
              MvPolynomial.eval row0 qrest by rw [hev]
          have h1 : MvPolynomial.eval row0 qrest =
              MvPolynomial.eval₂ (MvPolynomial.eval (Function.uncurry rest)) row0 q1 := by
            simp [qrest, MvPolynomial.eval_map]
          rw [h1]
          have h2 : ∀ r : MvPolynomial (Fin (m + 1) × Fin k) ℝ,
              MvPolynomial.eval₂ (MvPolynomial.eval (Function.uncurry rest)) row0
                ((MvPolynomial.sumAlgEquiv ℝ (Fin k) (Fin m × Fin k)) (MvPolynomial.rename eSplit r)) =
              MvPolynomial.eval (Sum.elim row0 (Function.uncurry rest)) (MvPolynomial.rename eSplit r) := by
            intro r
            induction r using MvPolynomial.induction_on with
            | C a => simp
            | add f g hf hg => simp [map_add, hf, hg]
            | mul_X f p hf =>
              simp only [map_mul, MvPolynomial.eval₂_mul, MvPolynomial.rename_X, hf]
              congr 1
              cases hsp : eSplit p with
              | inl j => simp
              | inr ij => simp
          rw [h2 q, MvPolynomial.eval_rename]
          congr 2
          funext ⟨i, j⟩
          cases i using Fin.cases with
          | zero => simp [eSplit, Function.uncurry]
          | succ i => simp [eSplit, Function.uncurry]
        rw [hslice]
        exact volume_mvPolynomial_zero_eq_zero qrest hqrest_ne
      rw [lintegral_congr_ae hae, lintegral_zero]
  exact hmp p hp

/-- Column `j` of `transformed Q C Y` equals `(diagonal (C · j) * Q).mulVec (Y.col j)`. -/
private lemma transformed_col {n k : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (C Y : Matrix (Fin n) (Fin k) ℝ) (j : Fin k) :
    (OMA.S_mo_279516.transformed Q C Y).col j =
      (Matrix.diagonal (fun i => C i j) * Q).mulVec (Y.col j) := by
  ext i
  simp [OMA.S_mo_279516.transformed, Matrix.hadamard, Matrix.mul_apply, Matrix.mulVec,
    Matrix.diagonal, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

private lemma rank_eq_finrank_span_col {n k : ℕ} (M : Matrix (Fin n) (Fin k) ℝ) :
    M.rank = Module.finrank ℝ ↥(Submodule.span ℝ (Set.range M.col)) := by
  have hrange : LinearMap.range M.mulVecLin = Submodule.span ℝ (Set.range M.col) := by
    ext v
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨x, rfl⟩
      have hsum : M.mulVec x = ∑ j : Fin k, x j • M.col j := by
        ext i
        simp [Matrix.mulVec, dotProduct, Matrix.col, Finset.sum_apply, mul_comm]
      rw [hsum]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · intro hv
      rw [Submodule.mem_span_range_iff_exists_fun] at hv
      obtain ⟨x, hx⟩ := hv
      refine ⟨x, ?_⟩
      rw [← hx]
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.col, Finset.sum_apply, mul_comm]
  rw [Matrix.rank, hrange]

/-- Upper bound: for every `Y` and `J`, `(transformed Q C Y).rank ≤ bound Q C J`. -/
private lemma rank_le_bound {n k : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (C Y : Matrix (Fin n) (Fin k) ℝ) (J : Finset (Fin k)) :
    (OMA.S_mo_279516.transformed Q C Y).rank ≤ OMA.S_mo_279516.bound Q C J := by
  let M := OMA.S_mo_279516.transformed Q C Y
  rw [rank_eq_finrank_span_col M]
  let A : Submodule ℝ (Fin n → ℝ) := J.sup (OMA.S_mo_279516.columnSpace Q C)
  let B : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ ((Jᶜ.image M.col : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
  have hsub : Submodule.span ℝ (Set.range M.col) ≤ A ⊔ B := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hj : j ∈ J
    · apply Submodule.mem_sup_left
      have hmem : M.col j ∈ OMA.S_mo_279516.columnSpace Q C j := by
        rw [OMA.S_mo_279516.columnSpace, LinearMap.mem_range]
        exact ⟨Y.col j, (transformed_col Q C Y j).symm⟩
      exact Finset.le_sup (f := OMA.S_mo_279516.columnSpace Q C) hj hmem
    · apply Submodule.mem_sup_right
      exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, by simp [hj], rfl⟩))
  have hB_le : Module.finrank ℝ ↥B ≤ k - J.card := by
    have h1 : Module.finrank ℝ ↥B ≤ (Jᶜ.image M.col).card := by
      simpa [B] using finrank_span_le_card ((Jᶜ.image M.col : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
    have h2 : (Jᶜ.image M.col).card ≤ (Jᶜ : Finset (Fin k)).card := Finset.card_image_le
    have h3 : (Jᶜ : Finset (Fin k)).card = k - J.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hsup_eq := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hmono := Submodule.finrank_mono hsub
  have hA_eq : Module.finrank ℝ ↥A = Module.finrank ℝ ↥(J.sup (OMA.S_mo_279516.columnSpace Q C)) := rfl
  unfold OMA.S_mo_279516.bound
  omega

/-- The determinant of an `r × r` submatrix of `transformed Q C Y` is a polynomial in the entries of `Y`. -/
private lemma exists_poly_submatrix_det {n k r : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin k) ℝ) (row : Fin r → Fin n) (col : Fin r → Fin k) :
    ∃ P : MvPolynomial (Fin n × Fin k) ℝ,
      ∀ Y : Matrix (Fin n) (Fin k) ℝ,
        MvPolynomial.eval (Function.uncurry Y) P =
          ((OMA.S_mo_279516.transformed Q C Y).submatrix row col).det := by
  let entryPoly (a b : Fin r) : MvPolynomial (Fin n × Fin k) ℝ :=
    MvPolynomial.C (C (row a) (col b)) *
      ∑ l : Fin n, MvPolynomial.C (Q (row a) l) * MvPolynomial.X (l, col b)
  let MPoly : Matrix (Fin r) (Fin r) (MvPolynomial (Fin n × Fin k) ℝ) :=
    Matrix.of entryPoly
  refine ⟨MPoly.det, fun Y => ?_⟩
  rw [RingHom.map_det (MvPolynomial.eval (Function.uncurry Y)) MPoly]
  congr 1
  ext a b
  simp [MPoly, entryPoly, OMA.S_mo_279516.transformed, Matrix.hadamard, Matrix.mul_apply,
    map_sum, map_mul, Function.uncurry, mul_comm]

end OMA.Mo279516Proof

open MeasureTheory OMA.S_mo_279516 OMA.Mo279516Proof in
theorem OMA.solution : type_of% @OMA.S_mo_279516.main := by
  intro n k Q C _ _ μ hμ
  let r : ℕ := sInf (Set.range (bound Q C))
  have hne : (Set.range (bound Q C)).Nonempty := ⟨bound Q C ∅, ∅, rfl⟩
  have hr_mem : r ∈ Set.range (bound Q C) := Nat.sInf_mem hne
  have hr_le : ∀ J : Finset (Fin k), r ≤ bound Q C J := fun J => Nat.sInf_le ⟨J, rfl⟩
  obtain ⟨v, hv_mem, hv_dim⟩ := exists_vectors_finrank_ge r k (columnSpace Q C) hr_le
  have hy_ex : ∀ j : Fin k, ∃ y : Fin n → ℝ, (Matrix.diagonal (fun i => C i j) * Q).mulVec y = v j :=
    fun j => LinearMap.mem_range.mp (hv_mem j)
  let Y₀ : Matrix (Fin n) (Fin k) ℝ := Matrix.of fun i j => Classical.choose (hy_ex j) i
  have hY₀_col : (transformed Q C Y₀).col = v := by
    ext j i
    have h1 := congrFun (transformed_col Q C Y₀ j) i
    have h2 := congrFun (Classical.choose_spec (hy_ex j)) i
    simpa [Y₀, Matrix.col] using h1.trans h2
  have hY₀_rank : r ≤ (transformed Q C Y₀).rank := by
    rw [rank_eq_finrank_span_col, hY₀_col]
    exact hv_dim
  obtain ⟨row, col, hdet₀⟩ := exists_submatrix_det_ne_zero (transformed Q C Y₀) hY₀_rank
  obtain ⟨P, hP⟩ := exists_poly_submatrix_det Q C row col
  have hP_ne : P ≠ 0 := by
    intro h0
    have := hP Y₀
    rw [h0, map_zero] at this
    exact hdet₀ this.symm
  have hvol0 : volume {Y : Matrix (Fin n) (Fin k) ℝ |
      MvPolynomial.eval (Function.uncurry Y) P = 0} = 0 :=
    volume_matrix_poly_zero_eq_zero P hP_ne
  have hμ0 : μ {Y : Matrix (Fin n) (Fin k) ℝ |
      MvPolynomial.eval (Function.uncurry Y) P = 0} = 0 := hμ hvol0
  filter_upwards [compl_mem_ae_iff.mpr hμ0] with Y hY
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hY
  have hdetY : ((transformed Q C Y).submatrix row col).det ≠ 0 := by
    rwa [← hP Y]
  have hrank_ge : r ≤ (transformed Q C Y).rank := by
    have hsub_rank : ((transformed Q C Y).submatrix row col).rank = r := by
      rw [Matrix.rank, LinearMap.finrank_range_of_inj
        (Matrix.mulVec_injective_of_det_ne_zero hdetY), Module.finrank_fin_fun]
    exact hsub_rank ▸ Matrix.rank_submatrix_le (transformed Q C Y) row col
  have hrank_le : (transformed Q C Y).rank ≤ r := by
    obtain ⟨J₀, hJ₀⟩ := hr_mem
    exact hJ₀ ▸ rank_le_bound Q C Y J₀
  have hrank_eq : (transformed Q C Y).rank = r := le_antisymm hrank_le hrank_ge
  rw [hrank_eq]
  exact ⟨hr_mem, fun _ ⟨J, hJ⟩ => hJ ▸ hr_le J⟩
