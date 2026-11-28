import OMAStatements.S_arxiv_2206_06881

namespace Arxiv220606881

open Finset OMA.S_arxiv_2206_06881

-- ============================================================================
-- Section 1: Fano Matrix R over ZMod 2, Vector Matroid M, and Circuit Vectors q
-- ============================================================================

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

private lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl
  · exact absurd rfl hx
  · rfl

private lemma zmod2_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  revert a b
  decide

private lemma vec_add_eq_zero_iff (u v : Fin 3 → ZMod 2) : u + v = 0 ↔ u = v := by
  constructor
  · intro h
    ext i
    have hi : u i + v i = 0 := congrFun h i
    exact (zmod2_add_eq_zero_iff (u i) (v i)).mp hi
  · rintro rfl
    ext i
    exact (zmod2_add_eq_zero_iff (u i) (u i)).mpr rfl

private def R : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 1, 1, 0, 1;
     0, 1, 0, 1, 1, 1, 0;
     0, 0, 1, 0, 1, 1, 1]

private def col (e : Fin 7) : Fin 3 → ZMod 2 := fun i => R i e

private lemma col_injective : Function.Injective col := by
  decide

private lemma col_ne_zero (e : Fin 7) : col e ≠ 0 := by
  revert e
  decide

private lemma set_range_coe_col (I : Set (Fin 7)) :
    Set.range (fun x : I => col x.1) = col '' I := by
  ext v
  simp

private lemma finrank_span_col_eq_card {I : Set (Fin 7)} [Fintype I]
    (hI : LinearIndepOn (ZMod 2) col I) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (col '' I)) = I.toFinset.card := by
  have h1 := finrank_span_eq_card hI
  rw [set_range_coe_col, ← Set.toFinset_card] at h1
  exact h1

private noncomputable def M_indep : IndepMatroid (Fin 7) :=
  IndepMatroid.ofBddAugment
    (E := Set.univ)
    (Indep := fun I => LinearIndepOn (ZMod 2) col I)
    (indep_empty := linearIndepOn_empty (ZMod 2) col)
    (indep_subset := fun _ _ hJ hIJ => hJ.mono hIJ)
    (indep_aug := by
      classical
      intro I J hI hJ hlt
      by_contra hnone
      push Not at hnone
      have hspan : Submodule.span (ZMod 2) (col '' J) ≤ Submodule.span (ZMod 2) (col '' I) := by
        rw [Submodule.span_le]
        rintro _ ⟨e, heJ, rfl⟩
        by_cases heI : e ∈ I
        · exact Submodule.subset_span ⟨e, heI, rfl⟩
        · have hnot : ¬ LinearIndepOn (ZMod 2) col (insert e I) := hnone e heJ heI
          by_contra hnotmem
          exact hnot ((linearIndepOn_insert heI).mpr ⟨hI, hnotmem⟩)
      have hle : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (col '' J)) ≤
          Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (col '' I)) :=
        Submodule.finrank_mono hspan
      rw [finrank_span_col_eq_card hJ, finrank_span_col_eq_card hI] at hle
      rw [Set.encard_eq_coe_toFinset_card I, Set.encard_eq_coe_toFinset_card J] at hlt
      have hlt_nat : I.toFinset.card < J.toFinset.card := Nat.cast_lt.mp hlt
      omega)
    (indep_bdd := ⟨7, fun I _ => by
      classical
      rw [Set.encard_eq_coe_toFinset_card I]
      exact_mod_cast (Finset.card_le_univ I.toFinset).trans_eq (Fintype.card_fin 7)⟩)
    (subset_ground := fun _ _ => Set.subset_univ _)

private noncomputable def M : Matroid (Fin 7) := M_indep.matroid

private lemma hRep : IsRepresentation M R :=
  ⟨rfl, fun _ => Iff.rfl⟩

private lemma M_indep_iff (I : Set (Fin 7)) : M.Indep I ↔ LinearIndepOn (ZMod 2) col I :=
  Iff.rfl

private def q (C : Circuits M) (e : Fin 7) : ZMod 2 :=
  if e ∈ C.1 then 1 else 0

private lemma hCV (C : Circuits M) : IsCircuitVector R C.1 (q C) := by
  classical
  constructor
  · have hnot : ¬ LinearIndepOn (ZMod 2) col (C.1 : Set (Fin 7)) := C.2.not_indep
    rw [LinearIndepOn, Fintype.linearIndependent_iff] at hnot
    push Not at hnot
    obtain ⟨g, hgsum, x₁, hx₁⟩ := hnot
    have hg_one : ∀ x : (C.1 : Set (Fin 7)), g x = 1 := by
      intro x₀
      apply zmod2_eq_one_of_ne_zero
      intro hgx0
      have hx0C : x₀.1 ∈ C.1 := x₀.2
      have hind : LinearIndepOn (ZMod 2) col ((C.1 : Set (Fin 7)) \ {x₀.1}) :=
        C.2.sdiff_singleton_indep x₀.2
      rw [LinearIndepOn, Fintype.linearIndependent_iff] at hind
      let g' : ((C.1 : Set (Fin 7)) \ {x₀.1} : Set (Fin 7)) → ZMod 2 :=
        fun y => g ⟨y.1, y.2.1⟩
      have hsum' : ∑ y : ((C.1 : Set (Fin 7)) \ {x₀.1} : Set (Fin 7)), g' y • col y.1 = 0 := by
        have hsum_fin : ∑ e ∈ C.1, (if h : e ∈ C.1 then g ⟨e, h⟩ else 0) • col e = 0 := by
          rw [← hgsum]
          symm
          refine Finset.sum_nbij (fun x : (C.1 : Set (Fin 7)) => x.1) ?_ ?_ ?_ ?_
          · intro x _; exact x.2
          · intro a _ b _ h; exact Subtype.ext h
          · intro e he; exact ⟨⟨e, he⟩, mem_univ _, rfl⟩
          · intro x _; simp
        have hsum_er : ∑ e ∈ C.1.erase x₀.1, (if h : e ∈ C.1 then g ⟨e, h⟩ else 0) • col e = 0 := by
          have h1 := Finset.add_sum_erase C.1
            (fun e => (if h : e ∈ C.1 then g ⟨e, h⟩ else 0) • col e) hx0C
          simp only [hx0C, ↓reduceDIte, hgx0, zero_smul, zero_add] at h1
          exact h1.trans hsum_fin
        rw [← hsum_er]
        refine Finset.sum_nbij (fun y : ((C.1 : Set (Fin 7)) \ {x₀.1} : Set (Fin 7)) => y.1) ?_ ?_ ?_ ?_
        · intro y _
          exact mem_erase.mpr ⟨y.2.2, y.2.1⟩
        · intro a _ b _ h; exact Subtype.ext h
        · intro e he
          rw [Finset.mem_coe, mem_erase] at he
          exact ⟨⟨e, he.2, he.1⟩, mem_univ _, rfl⟩
        · intro y _
          have hyC : y.1 ∈ C.1 := y.2.1
          simp [g', hyC]
      have hx1_ne : x₁.1 ≠ x₀.1 := by
        intro heq
        have : x₁ = x₀ := Subtype.ext heq
        rw [this] at hx₁
        exact hx₁ hgx0
      have hx1_zero := hind g' hsum' ⟨x₁.1, x₁.2, hx1_ne⟩
      exact hx₁ hx1_zero
    have hsum_col : ∑ e ∈ C.1, col e = 0 := by
      rw [← hgsum]
      symm
      refine Finset.sum_nbij (fun x : (C.1 : Set (Fin 7)) => x.1) ?_ ?_ ?_ ?_
      · intro x _; exact x.2
      · intro a _ b _ h; exact Subtype.ext h
      · intro e he; exact ⟨⟨e, he⟩, mem_univ _, rfl⟩
      · intro x _
        have h1 := hg_one x
        simp [h1]
    ext i
    simp only [Matrix.mulVec, dotProduct, q, Pi.zero_apply]
    have hmul : (∑ e : Fin 7, R i e * if e ∈ C.1 then (1 : ZMod 2) else 0) =
        ∑ e ∈ C.1, col e i := by
      have h1 : (∑ e : Fin 7, R i e * if e ∈ C.1 then (1 : ZMod 2) else 0) =
          ∑ e : Fin 7, if e ∈ C.1 then col e i else 0 := by
        refine Finset.sum_congr rfl fun e _ => ?_
        by_cases he : e ∈ C.1 <;> simp [he, col]
      rw [h1, ← Finset.sum_filter]
      have hflt : (Finset.univ.filter fun e : Fin 7 => e ∈ C.1) = C.1 := by
        ext e; simp
      rw [hflt]
    rw [hmul]
    have hev := congrFun hsum_col i
    simpa [Finset.sum_apply] using hev
  · intro e
    by_cases he : e ∈ C.1 <;> simp [q, he]

-- ============================================================================
-- Section 2: Rank, Nullity, and F_2 Kernel Cardinality Bounds for F_7
-- ============================================================================

private lemma card_fintype_eq_two_pow_finrank (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] : Fintype.card V = 2 ^ Module.finrank (ZMod 2) V := by
  have h1 := Fintype.card_congr (Module.finBasis (ZMod 2) V).equivFun.toEquiv
  simpa [Fintype.card_pi, ZMod.card] using h1

private lemma rank_le_card (S : Finset (Fin 7)) : rank M S ≤ S.card := by
  classical
  unfold rank
  apply Finset.sup_le
  intro T hT
  exact Finset.card_le_card (mem_powerset.mp (mem_filter.mp hT).1)

private lemma rank_eq_finrank_span (S : Finset (Fin 7)) :
    rank M S = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (col '' (S : Set (Fin 7)))) := by
  classical
  apply le_antisymm
  · unfold rank
    apply Finset.sup_le
    intro T hT
    have hTS : T ⊆ S := mem_powerset.mp (mem_filter.mp hT).1
    have hTind : LinearIndepOn (ZMod 2) col (T : Set (Fin 7)) := (mem_filter.mp hT).2
    have hcard : T.card = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (col '' (T : Set (Fin 7)))) := by
      rw [finrank_span_col_eq_card hTind]
      simp
    rw [hcard]
    exact Submodule.finrank_mono (Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr hTS)))
  · set Fset := S.powerset.filter (fun T : Finset (Fin 7) => M.Indep (T : Set (Fin 7)))
    have hne : Fset.Nonempty := ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset S), by
      simp [M_indep_iff, linearIndepOn_empty]⟩⟩
    obtain ⟨T, hTF, hTsup⟩ := Finset.exists_mem_eq_sup Fset hne Finset.card
    have hTS : T ⊆ S := mem_powerset.mp (mem_filter.mp hTF).1
    have hTind : LinearIndepOn (ZMod 2) col (T : Set (Fin 7)) := (mem_filter.mp hTF).2
    have hspan_le : Submodule.span (ZMod 2) (col '' (S : Set (Fin 7))) ≤
        Submodule.span (ZMod 2) (col '' (T : Set (Fin 7))) := by
      rw [Submodule.span_le]
      rintro _ ⟨e, heS, rfl⟩
      by_cases heT : e ∈ T
      · exact Submodule.subset_span ⟨e, heT, rfl⟩
      · by_contra hnotmem
        have hins_ind : LinearIndepOn (ZMod 2) col ((insert e T : Finset (Fin 7)) : Set (Fin 7)) := by
          rw [Finset.coe_insert]
          exact (linearIndepOn_insert (by simpa using heT)).mpr ⟨hTind, hnotmem⟩
        have hins_mem : insert e T ∈ Fset :=
          mem_filter.mpr ⟨mem_powerset.mpr (insert_subset heS hTS), hins_ind⟩
        have hle := Finset.le_sup (f := Finset.card) hins_mem
        rw [Finset.card_insert_of_notMem heT, ← hTsup] at hle
        omega
    have hle := Submodule.finrank_mono hspan_le
    rw [finrank_span_col_eq_card hTind] at hle
    simp at hle
    have hrank_eq : rank M S = T.card := by
      unfold rank
      convert hTsup
    omega

private lemma rank_le_three (S : Finset (Fin 7)) : rank M S ≤ 3 := by
  rw [rank_eq_finrank_span]
  calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (col '' (S : Set (Fin 7))))
      ≤ Module.finrank (ZMod 2) (Fin 3 → ZMod 2) := Submodule.finrank_le _
    _ = 3 := by simp

private lemma rank_eq_three_of_four_le_card {S : Finset (Fin 7)} (hS : 4 ≤ S.card) :
    rank M S = 3 := by
  classical
  set V := Submodule.span (ZMod 2) (col '' (S : Set (Fin 7)))
  have hcardV : Fintype.card V = 2 ^ rank M S := by
    rw [rank_eq_finrank_span, card_fintype_eq_two_pow_finrank]
  let f : Option S → V
    | none => 0
    | some e => ⟨col e.1, Submodule.subset_span ⟨e.1, e.2, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some e =>
        have : (0 : Fin 3 → ZMod 2) = col e.1 := congrArg Subtype.val hab
        exact absurd this.symm (col_ne_zero e.1)
    | some e₁ =>
      cases b with
      | none =>
        have : col e₁.1 = (0 : Fin 3 → ZMod 2) := congrArg Subtype.val hab
        exact absurd this (col_ne_zero e₁.1)
      | some e₂ =>
        have : col e₁.1 = col e₂.1 := congrArg Subtype.val hab
        exact congrArg some (Subtype.ext (col_injective this))
  have hle : S.card + 1 ≤ 2 ^ rank M S := by
    have h1 := Fintype.card_le_of_injective f hf_inj
    simpa [Fintype.card_option, Fintype.card_coe, hcardV] using h1
  have hr3 : rank M S ≤ 3 := rank_le_three S
  by_contra hne
  have hr2 : rank M S ≤ 2 := by omega
  have hpow : 2 ^ rank M S ≤ 4 := by
    calc 2 ^ rank M S ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hr2
      _ = 4 := by norm_num
  omega

private lemma card_circuits_le_two_pow_nullity {A : Finset (Circuits M)} {S : Finset (Fin 7)}
    (hAS : support A ⊆ S) : A.card + 1 ≤ 2 ^ nullity M S := by
  classical
  let L : (S → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    Fintype.linearCombination (ZMod 2) (fun e : S => col e.1)
  have hrange : LinearMap.range L = Submodule.span (ZMod 2) (col '' (S : Set (Fin 7))) := by
    rw [Fintype.range_linearCombination]
    congr 1
    ext v
    simp
  have hrk : Module.finrank (ZMod 2) (LinearMap.ker L) = nullity M S := by
    have hrn := LinearMap.finrank_range_add_finrank_ker L
    rw [hrange, ← rank_eq_finrank_span, Module.finrank_pi, Fintype.card_coe] at hrn
    have hle := rank_le_card S
    unfold nullity
    omega
  have hcardK : Fintype.card (LinearMap.ker L) = 2 ^ nullity M S := by
    rw [← hrk, card_fintype_eq_two_pow_finrank]
  have hmemK : ∀ C : A, (fun e : S => q C.1 e.1) ∈ LinearMap.ker L := by
    intro C
    rw [LinearMap.mem_ker]
    have hCS : C.1.1 ⊆ S := Subset.trans (Finset.subset_biUnion_of_mem (fun D : Circuits M => D.1) C.2) hAS
    have hmv : R.mulVec (q C.1) = 0 := (hCV C.1).1
    ext i
    have hi := congrFun hmv i
    simp only [L, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hi
    rw [← hi]
    have hsum1 : (∑ e : S, q C.1 e.1 * col e.1 i) = ∑ e ∈ S, R i e * q C.1 e := by
      rw [← Finset.sum_coe_sort S (fun e => R i e * q C.1 e)]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp [col, mul_comm]
    rw [hsum1]
    refine Finset.sum_subset (subset_univ S) fun e _ heS => ?_
    have heC : e ∉ C.1.1 := fun h => heS (hCS h)
    simp [q, heC]
  let φ : Option A → LinearMap.ker L
    | none => 0
    | some C => ⟨fun e : S => q C.1 e.1, hmemK C⟩
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some C =>
        have hCS : C.1.1 ⊆ S :=
          Subset.trans (Finset.subset_biUnion_of_mem (fun D : Circuits M => D.1) C.2) hAS
        obtain ⟨e, heC⟩ := C.1.2.nonempty
        have heC' : e ∈ C.1.1 := heC
        have h0 : (0 : ZMod 2) = q C.1 e := congrFun (congrArg Subtype.val hab) ⟨e, hCS heC'⟩
        simp [q, heC'] at h0
    | some C₁ =>
      cases b with
      | none =>
        have hCS : C₁.1.1 ⊆ S :=
          Subset.trans (Finset.subset_biUnion_of_mem (fun D : Circuits M => D.1) C₁.2) hAS
        obtain ⟨e, heC⟩ := C₁.1.2.nonempty
        have heC' : e ∈ C₁.1.1 := heC
        have h0 : q C₁.1 e = (0 : ZMod 2) := congrFun (congrArg Subtype.val hab) ⟨e, hCS heC'⟩
        simp [q, heC'] at h0
      | some C₂ =>
        have hCS₁ : C₁.1.1 ⊆ S :=
          Subset.trans (Finset.subset_biUnion_of_mem (fun D : Circuits M => D.1) C₁.2) hAS
        have hCS₂ : C₂.1.1 ⊆ S :=
          Subset.trans (Finset.subset_biUnion_of_mem (fun D : Circuits M => D.1) C₂.2) hAS
        have heq_sub : C₁.1.1 = C₂.1.1 := by
          ext e
          by_cases heS : e ∈ S
          · have hv : q C₁.1 e = q C₂.1 e := congrFun (congrArg Subtype.val hab) ⟨e, heS⟩
            by_cases h1 : e ∈ C₁.1.1 <;> by_cases h2 : e ∈ C₂.1.1 <;> simp [q, h1, h2] at hv ⊢
          · exact ⟨fun h => absurd (hCS₁ h) heS, fun h => absurd (hCS₂ h) heS⟩
        exact congrArg some (Subtype.ext (Subtype.ext heq_sub))
  have hle := Fintype.card_le_of_injective φ hφ_inj
  rw [Fintype.card_option, Fintype.card_coe, hcardK] at hle
  exact hle

private lemma indep_of_card_le_two {T : Finset (Fin 7)} (hT : T.card ≤ 2) :
    M.Indep (T : Set (Fin 7)) := by
  rw [M_indep_iff, LinearIndepOn, Fintype.linearIndependent_iff]
  intro g hsum x
  have hcard : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by omega
  rcases hcard with h0 | h1 | h2
  · rw [Finset.card_eq_zero] at h0
    have := x.2
    simp [h0] at this
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    have hxa : x = ⟨a, mem_singleton_self a⟩ := Subtype.ext (mem_singleton.mp x.2)
    have hsum1 : g ⟨a, mem_singleton_self a⟩ • col a = 0 := by
      have : ∑ y : (({a} : Finset (Fin 7)) : Set (Fin 7)), g y • col y.1 =
          g ⟨a, mem_singleton_self a⟩ • col a := by
        rw [Finset.sum_eq_single ⟨a, mem_singleton_self a⟩]
        · intro y _ hy
          exfalso; exact hy (Subtype.ext (mem_singleton.mp y.2))
        · intro h; exact absurd (mem_univ _) h
      exact this.symm.trans hsum
    rw [hxa]
    rcases zmod2_eq_zero_or_one (g ⟨a, mem_singleton_self a⟩) with h | h
    · exact h
    · rw [h, one_smul] at hsum1
      exact absurd hsum1 (col_ne_zero a)
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
    let xa : (({a, b} : Finset (Fin 7)) : Set (Fin 7)) := ⟨a, by simp⟩
    let xb : (({a, b} : Finset (Fin 7)) : Set (Fin 7)) := ⟨b, by simp⟩
    have hxab : xa ≠ xb := fun h => hab (congrArg Subtype.val h)
    have huniv : (Finset.univ : Finset (({a, b} : Finset (Fin 7)) : Set (Fin 7))) = {xa, xb} := by
      ext y
      simp only [mem_univ, mem_insert, mem_singleton, true_iff]
      have hy : y.1 = a ∨ y.1 = b := by simpa using y.2
      rcases hy with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h
    have hsum2 : g xa • col a + g xb • col b = 0 := by
      rw [← hsum]
      change g xa • col a + g xb • col b = ∑ y ∈ Finset.univ, g y • col y.1
      rw [huniv, Finset.sum_pair hxab]
    have hga : g xa = 0 ∧ g xb = 0 := by
      rcases zmod2_eq_zero_or_one (g xa) with ha0 | ha1 <;>
        rcases zmod2_eq_zero_or_one (g xb) with hb0 | hb1
      · exact ⟨ha0, hb0⟩
      · rw [ha0, hb1, zero_smul, one_smul, zero_add] at hsum2
        exact absurd hsum2 (col_ne_zero b)
      · rw [ha1, hb0, one_smul, zero_smul, add_zero] at hsum2
        exact absurd hsum2 (col_ne_zero a)
      · rw [ha1, hb1, one_smul, one_smul] at hsum2
        exact absurd (col_injective ((vec_add_eq_zero_iff _ _).mp hsum2)) hab
    have hx : x = xa ∨ x = xb := by
      have : x.1 = a ∨ x.1 = b := by simpa using x.2
      rcases this with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h
    rcases hx with rfl | rfl
    · exact hga.1
    · exact hga.2

private lemma circuit_card_ge_three (C : Circuits M) : 3 ≤ C.1.card := by
  by_contra hlt
  exact C.2.not_indep (indep_of_card_le_two (by omega))

private lemma circuit_nullity_eq_one (C : Circuits M) : nullity M C.1 = 1 := by
  classical
  have h3 := circuit_card_ge_three C
  have hle : rank M C.1 ≤ C.1.card - 1 := by
    unfold rank
    apply Finset.sup_le
    intro T hT
    have hTS : T ⊆ C.1 := mem_powerset.mp (mem_filter.mp hT).1
    have hTind : M.Indep (T : Set (Fin 7)) := (mem_filter.mp hT).2
    have hne : T ≠ C.1 := fun h => C.2.not_indep (h ▸ hTind)
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hne⟩)
    omega
  obtain ⟨e, heC⟩ := C.2.nonempty
  have heC' : e ∈ C.1 := heC
  have her_ind : M.Indep ((C.1.erase e : Finset (Fin 7)) : Set (Fin 7)) := by
    rw [Finset.coe_erase]
    exact C.2.sdiff_singleton_indep heC
  have hge : C.1.card - 1 ≤ rank M C.1 := by
    have hmem : C.1.erase e ∈ C.1.powerset.filter (fun T : Finset (Fin 7) => M.Indep (T : Set (Fin 7))) :=
      mem_filter.mpr ⟨mem_powerset.mpr (erase_subset e C.1), her_ind⟩
    have h1 := Finset.le_sup (f := Finset.card) hmem
    rw [Finset.card_erase_of_mem heC'] at h1
    exact h1
  unfold nullity
  omega

private lemma union_card_ge_five {C₁ C₂ : Circuits M} (hne : C₁ ≠ C₂) :
    5 ≤ (C₁.1 ∪ C₂.1).card := by
  have hnot_sub : ¬ C₁.1 ⊆ C₂.1 := fun hsub =>
    hne (Subtype.ext (Finset.coe_injective (C₁.2.eq_of_subset_isCircuit C₂.2 (Finset.coe_subset.mpr hsub))))
  have hnot_sub' : ¬ C₂.1 ⊆ C₁.1 := fun hsub =>
    hne.symm (Subtype.ext (Finset.coe_injective (C₂.2.eq_of_subset_isCircuit C₁.2 (Finset.coe_subset.mpr hsub))))
  have hlt : C₁.1 ⊂ C₁.1 ∪ C₂.1 := Finset.ssubset_iff_subset_ne.mpr
    ⟨subset_union_left, fun heq => hnot_sub' (heq ▸ subset_union_right)⟩
  have h4 : 4 ≤ (C₁.1 ∪ C₂.1).card := by
    have := circuit_card_ge_three C₁
    have := Finset.card_lt_card hlt
    omega
  by_contra hlt5
  have heq4 : (C₁.1 ∪ C₂.1).card = 4 := by omega
  have hr3 : rank M (C₁.1 ∪ C₂.1) = 3 := rank_eq_three_of_four_le_card h4
  have hnul1 : nullity M (C₁.1 ∪ C₂.1) = 1 := by unfold nullity; omega
  let A : Finset (Circuits M) := {C₁, C₂}
  have hsupp : support A ⊆ C₁.1 ∪ C₂.1 := by
    simp [A, support]
  have hbound := card_circuits_le_two_pow_nullity hsupp
  rw [Finset.card_pair hne, hnul1] at hbound
  omega

private lemma initial_card_ge_three {A : Finset (Circuits M)} (hA : A ∈ initial M) :
    3 ≤ A.card := by
  have hlt : nullity M (support A) < A.card := hA
  by_contra hle2
  have hcases : A.card = 0 ∨ A.card = 1 ∨ A.card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · omega
  · obtain ⟨C, rfl⟩ := Finset.card_eq_one.mp h1
    have hsupp : support {C} = C.1 := by simp [support]
    rw [hsupp, circuit_nullity_eq_one] at hlt
    simp at hlt
  · obtain ⟨C₁, C₂, hne, rfl⟩ := Finset.card_eq_two.mp h2
    have hsupp : support {C₁, C₂} = C₁.1 ∪ C₂.1 := by simp [support]
    have h5 := union_card_ge_five hne
    have hr3 := rank_le_three (C₁.1 ∪ C₂.1)
    rw [hsupp, Finset.card_pair hne] at hlt
    unfold nullity at hlt
    omega

private lemma initial_card_three_eq_of_inter_ge_two {A₁ A₂ : Finset (Circuits M)}
    (h₁ : A₁ ∈ initial M) (h₂ : A₂ ∈ initial M)
    (hc₁ : A₁.card = 3) (hc₂ : A₂.card = 3) (hint : 2 ≤ (A₁ ∩ A₂).card) :
    A₁ = A₂ := by
  obtain ⟨Ca, hCa, Cb, hCb, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (A₁ ∩ A₂).card)
  let S₀ : Finset (Fin 7) := Ca.1 ∪ Cb.1
  have hS₀5 : 5 ≤ S₀.card := union_card_ge_five hne
  have hsub1 : S₀ ⊆ support A₁ := by
    refine union_subset ?_ ?_
    · exact Finset.subset_biUnion_of_mem (fun D : Circuits M => D.1) (mem_inter.mp hCa).1
    · exact Finset.subset_biUnion_of_mem (fun D : Circuits M => D.1) (mem_inter.mp hCb).1
  have hsub2 : S₀ ⊆ support A₂ := by
    refine union_subset ?_ ?_
    · exact Finset.subset_biUnion_of_mem (fun D : Circuits M => D.1) (mem_inter.mp hCa).2
    · exact Finset.subset_biUnion_of_mem (fun D : Circuits M => D.1) (mem_inter.mp hCb).2
  have hcard1 : (support A₁).card ≤ 5 := by
    have hlt : nullity M (support A₁) < 3 := hc₁ ▸ h₁
    have hr3 := rank_le_three (support A₁)
    have hrc := rank_le_card (support A₁)
    unfold nullity at hlt
    omega
  have hcard2 : (support A₂).card ≤ 5 := by
    have hlt : nullity M (support A₂) < 3 := hc₂ ▸ h₂
    have hr3 := rank_le_three (support A₂)
    have hrc := rank_le_card (support A₂)
    unfold nullity at hlt
    omega
  have heq1 : S₀ = support A₁ := Finset.eq_of_subset_of_card_le hsub1 (by omega)
  have heq2 : S₀ = support A₂ := Finset.eq_of_subset_of_card_le hsub2 (by omega)
  have hS₀card : S₀.card = 5 := by
    have := Finset.card_le_card hsub1
    omega
  have hnul2 : nullity M S₀ = 2 := by
    have hr3 := rank_eq_three_of_four_le_card (by omega : 4 ≤ S₀.card)
    unfold nullity
    omega
  have hsuppU : support (A₁ ∪ A₂) ⊆ S₀ := by
    rw [support, Finset.union_biUnion]
    exact union_subset heq1.symm.subset heq2.symm.subset
  have hbound := card_circuits_le_two_pow_nullity hsuppU
  rw [hnul2] at hbound
  have hUle : (A₁ ∪ A₂).card ≤ 3 := by omega
  have h1eq : A₁ = A₁ ∪ A₂ := Finset.eq_of_subset_of_card_le subset_union_left (by omega)
  have h2eq : A₂ = A₁ ∪ A₂ := Finset.eq_of_subset_of_card_le subset_union_right (by omega)
  exact h1eq.trans h2eq.symm

-- ============================================================================
-- Section 3: Stage Invariant and Stage Monotonicity
-- ============================================================================

private lemma stage_mono (i : ℕ) : stage M i ⊆ stage M (i + 1) := by
  intro A hA
  exact ⟨A, Or.inl hA, Subset.rfl⟩

private lemma stage_invariant :
    ∀ k : ℕ, ∀ A : Finset (Circuits M), A ∈ stage M k → 4 ≤ A.card ∨ A ∈ initial M := by
  intro k
  induction k with
  | zero =>
    intro A hA
    exact Or.inr hA
  | succ k ih =>
    intro A hA
    rcases hA with ⟨W, hW_eps, hWA⟩
    have hW_inv : 4 ≤ W.card ∨ W ∈ initial M := by
      rcases hW_eps with hWk | ⟨A₁, hA₁, A₂, hA₂, hinter_not, C, hC, rfl⟩
      · exact ih W hWk
      · have hne : A₁ ≠ A₂ := by
          rintro rfl
          rw [inter_self] at hinter_not
          exact hinter_not hA₁
        have hnot12 : ¬ A₁ ⊆ A₂ := fun hsub =>
          hinter_not (by rwa [Finset.inter_eq_left.mpr hsub])
        have hnot21 : ¬ A₂ ⊆ A₁ := fun hsub =>
          hinter_not (by rwa [Finset.inter_eq_right.mpr hsub])
        have hlt1 : A₁.card < (A₁ ∪ A₂).card := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left, fun h => hnot21 (h ▸ subset_union_right)⟩)
        have hlt2 : A₂.card < (A₁ ∪ A₂).card := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_right, fun h => hnot12 (h ▸ subset_union_left)⟩)
        have hC_mem : C ∈ A₁ ∪ A₂ := mem_union_left A₂ (mem_inter.mp hC).1
        have hcard_er : ((A₁ ∪ A₂).erase C).card = (A₁ ∪ A₂).card - 1 :=
          Finset.card_erase_of_mem hC_mem
        left
        by_cases hbig : 4 ≤ A₁.card ∨ 4 ≤ A₂.card
        · rcases hbig with h1 | h2 <;> omega
        · push Not at hbig
          have hA₁_init : A₁ ∈ initial M := (ih A₁ hA₁).resolve_left (by omega)
          have hA₂_init : A₂ ∈ initial M := (ih A₂ hA₂).resolve_left (by omega)
          have hc₁ : A₁.card = 3 := by have := initial_card_ge_three hA₁_init; omega
          have hc₂ : A₂.card = 3 := by have := initial_card_ge_three hA₂_init; omega
          have hint_le : (A₁ ∩ A₂).card ≤ 1 := by
            by_contra hgt
            exact hne (initial_card_three_eq_of_inter_ge_two hA₁_init hA₂_init hc₁ hc₂ (by omega))
          have hinc := Finset.card_union_add_card_inter A₁ A₂
          omega
    rcases hW_inv with hW4 | hWinit
    · left
      exact le_trans hW4 (Finset.card_le_card hWA)
    · by_cases heq : W = A
      · right; exact heq ▸ hWinit
      · left
        have h3 := initial_card_ge_three hWinit
        have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hWA, heq⟩)
        omega

private lemma not_mem_stage_of_card_le_three {k : ℕ} {A : Finset (Circuits M)}
    (hc : A.card ≤ 3) (hnot : A ∉ initial M) : A ∉ stage M k := by
  intro hmem
  rcases stage_invariant k A hmem with h4 | hinit
  · omega
  · exact hnot hinit

-- ============================================================================
-- Section 4: Seven Explicit Circuits, Stage-3 Derivation, and Linear Independence
-- ============================================================================

private lemma not_indep_of_sum_zero {S : Finset (Fin 7)} (hne : S.Nonempty)
    (hsum : ∑ e ∈ S, col e = 0) : ¬ M.Indep (S : Set (Fin 7)) := by
  rw [M_indep_iff, LinearIndepOn, Fintype.linearIndependent_iff]
  intro hind
  obtain ⟨e₀, he₀⟩ := hne
  have hsum' : ∑ x : (S : Set (Fin 7)), (1 : ZMod 2) • col x.1 = 0 := by
    rw [← hsum]
    refine Finset.sum_nbij (fun x : (S : Set (Fin 7)) => x.1) ?_ ?_ ?_ ?_
    · intro x _; exact x.2
    · intro a _ b _ h; exact Subtype.ext h
    · intro e he; exact ⟨⟨e, he⟩, mem_univ _, rfl⟩
    · intro x _; simp
  have h10 := hind (fun _ => (1 : ZMod 2)) hsum' ⟨e₀, he₀⟩
  exact absurd h10 (by decide)

private lemma isCircuit_of_card_three {a b c : Fin 7}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsum : col a + col b + col c = 0) :
    M.IsCircuit (({a, b, c} : Finset (Fin 7)) : Set (Fin 7)) := by
  classical
  rw [Matroid.isCircuit_iff_forall_ssubset]
  have hSsum : ∑ e ∈ ({a, b, c} : Finset (Fin 7)), col e = 0 := by
    rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, ← add_assoc]
    exact hsum
  refine ⟨⟨not_indep_of_sum_zero ⟨a, by simp⟩ hSsum, Set.subset_univ _⟩, ?_⟩
  intro I hI
  have hss : I.toFinset ⊂ ({a, b, c} : Finset (Fin 7)) := by
    rw [← Finset.coe_ssubset, Set.coe_toFinset]
    exact hI
  have hcard : I.toFinset.card ≤ 2 := by
    have hlt := Finset.card_lt_card hss
    have h3 : ({a, b, c} : Finset (Fin 7)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
    omega
  have hind := indep_of_card_le_two hcard
  rwa [Set.coe_toFinset] at hind

private lemma isCircuit_of_card_four {a b c d : Fin 7}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hsum : col a + col b + col c + col d = 0) :
    M.IsCircuit (({a, b, c, d} : Finset (Fin 7)) : Set (Fin 7)) := by
  classical
  let S : Finset (Fin 7) := {a, b, c, d}
  have hSsum : ∑ e ∈ S, col e = 0 := by
    simp only [S]
    rw [Finset.sum_insert (by simp [hab, hac, had]),
        Finset.sum_insert (by simp [hbc, hbd]),
        Finset.sum_pair hcd]
    rw [← add_assoc, ← add_assoc]
    exact hsum
  have hScard : S.card = 4 := by
    simp only [S]
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
        Finset.card_insert_of_notMem (by simp [hbc, hbd]),
        Finset.card_pair hcd]
  rw [Matroid.isCircuit_iff_forall_ssubset]
  refine ⟨⟨not_indep_of_sum_zero ⟨a, by simp⟩ hSsum, Set.subset_univ _⟩, ?_⟩
  intro I hI
  have hss : I.toFinset ⊂ S := by
    rw [← Finset.coe_ssubset, Set.coe_toFinset]
    exact hI
  have hcard_le : I.toFinset.card ≤ 3 := by
    have := Finset.card_lt_card hss
    omega
  by_cases h2 : I.toFinset.card ≤ 2
  · have hind := indep_of_card_le_two h2
    rwa [Set.coe_toFinset] at hind
  · have hT3 : I.toFinset.card = 3 := by omega
    rw [← Set.coe_toFinset I, M_indep_iff, LinearIndepOn, Fintype.linearIndependent_iff]
    intro g hgsum x
    let U : Finset (Fin 7) := I.toFinset.filter fun e => ∃ h : e ∈ I.toFinset, g ⟨e, h⟩ ≠ 0
    have hUS : U ⊆ I.toFinset := Finset.filter_subset _ _
    have hUsum : ∑ e ∈ U, col e = 0 := by
      have h1 : ∑ e ∈ I.toFinset, (if h : e ∈ I.toFinset then g ⟨e, h⟩ else 0) • col e = 0 := by
        rw [← hgsum]
        symm
        refine Finset.sum_nbij (fun y : (I.toFinset : Set (Fin 7)) => y.1) ?_ ?_ ?_ ?_
        · intro y _; exact y.2
        · intro u _ v _ h; exact Subtype.ext h
        · intro e he; exact ⟨⟨e, he⟩, mem_univ _, rfl⟩
        · intro y _; simp
      rw [← h1]
      symm
      rw [← Finset.sum_subset hUS]
      · refine Finset.sum_congr rfl fun e heU => ?_
        obtain ⟨heI, hgnz⟩ := (mem_filter.mp heU).2
        have hge1 : g ⟨e, heI⟩ = 1 := zmod2_eq_one_of_ne_zero hgnz
        simp [heI, hge1]
      · intro e heI heU
        have hgz : g ⟨e, heI⟩ = 0 := by
          by_contra hnz
          exact heU (mem_filter.mpr ⟨heI, heI, hnz⟩)
        simp [heI, hgz]
    have hUempty : U = ∅ := by
      by_contra hne
      have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      by_cases hU2 : U.card ≤ 2
      · exact not_indep_of_sum_zero hUne hUsum (indep_of_card_le_two hU2)
      · have hU3 : U.card = 3 := by
          have := Finset.card_le_card hUS
          omega
        have hUI : U = I.toFinset := Finset.eq_of_subset_of_card_le hUS (by omega)
        have hdiff_ne : (S \ I.toFinset).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.sdiff_eq_empty_iff_subset]
          exact fun h => hss.ne (Finset.Subset.antisymm hss.subset h)
        obtain ⟨e₀, he₀⟩ := hdiff_ne
        have he₀S : e₀ ∈ S := (mem_sdiff.mp he₀).1
        have he₀I : e₀ ∉ I.toFinset := (mem_sdiff.mp he₀).2
        have hIeq : I.toFinset = S.erase e₀ := by
          refine Finset.eq_of_subset_of_card_le ?_ ?_
          · intro e heI
            exact mem_erase.mpr ⟨fun h => he₀I (h ▸ heI), hss.subset heI⟩
          · rw [Finset.card_erase_of_mem he₀S, hScard, hT3]
        have hadd := Finset.add_sum_erase S col he₀S
        rw [← hIeq, ← hUI, hUsum, add_zero, hSsum] at hadd
        exact col_ne_zero e₀ hadd
    by_contra hnz
    have hxU : x.1 ∈ U := mem_filter.mpr ⟨x.2, x.2, hnz⟩
    rw [hUempty] at hxU
    exact Finset.notMem_empty _ hxU

private noncomputable def C₀ : Circuits M :=
  ⟨{0, 1, 3}, isCircuit_of_card_three (by decide) (by decide) (by decide) (by decide)⟩

private noncomputable def C₁ : Circuits M :=
  ⟨{0, 1, 2, 4}, isCircuit_of_card_four (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

private noncomputable def C₄ : Circuits M :=
  ⟨{0, 2, 3, 5}, isCircuit_of_card_four (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

private noncomputable def C₆ : Circuits M :=
  ⟨{1, 3, 4, 5}, isCircuit_of_card_four (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

private noncomputable def C₇ : Circuits M :=
  ⟨{0, 2, 6}, isCircuit_of_card_three (by decide) (by decide) (by decide) (by decide)⟩

private noncomputable def C₉ : Circuits M :=
  ⟨{1, 4, 6}, isCircuit_of_card_three (by decide) (by decide) (by decide) (by decide)⟩

private noncomputable def C₁₂ : Circuits M :=
  ⟨{3, 5, 6}, isCircuit_of_card_three (by decide) (by decide) (by decide) (by decide)⟩

private lemma circuit_ne {a b : Circuits M} (h : a.1 ≠ b.1) : a ≠ b :=
  fun heq => h (congrArg Subtype.val heq)

private noncomputable def B₁ : Finset (Circuits M) := {C₄, C₇, C₁₂}
private noncomputable def B₂ : Finset (Circuits M) := {C₆, C₉, C₁₂}
private noncomputable def B₃ : Finset (Circuits M) := {C₁, C₇, C₉}
private noncomputable def B₄ : Finset (Circuits M) := {C₀, C₁, C₄, C₆}
private noncomputable def D₁ : Finset (Circuits M) := {C₄, C₆, C₇, C₉}
private noncomputable def D₂ : Finset (Circuits M) := {C₁, C₄, C₆, C₇}
private noncomputable def I_set : Finset (Circuits M) := {C₁, C₄, C₆}
private noncomputable def W : Finset (Circuits M) := {C₀, C₄, C₆, C₇}

private lemma hB₁_stage0 : B₁ ∈ stage M 0 := by
  have hcard : B₁.card = 3 := by
    simp only [B₁]
    rw [Finset.card_insert_of_notMem (by simp [circuit_ne (a := C₄) (b := C₇) (by decide),
          circuit_ne (a := C₄) (b := C₁₂) (by decide)]),
        Finset.card_pair (circuit_ne (a := C₇) (b := C₁₂) (by decide))]
  have hsupp : (support B₁).card = 5 := by
    have : support B₁ = ({0, 2, 3, 5} ∪ {0, 2, 6} ∪ {3, 5, 6} : Finset (Fin 7)) := by
      simp [B₁, support, C₄, C₇, C₁₂]
    rw [this]; decide
  have hr := rank_eq_three_of_four_le_card (by omega : 4 ≤ (support B₁).card)
  change nullity M (support B₁) < B₁.card
  unfold nullity
  omega

private lemma hB₂_stage0 : B₂ ∈ stage M 0 := by
  have hcard : B₂.card = 3 := by
    simp only [B₂]
    rw [Finset.card_insert_of_notMem (by simp [circuit_ne (a := C₆) (b := C₉) (by decide),
          circuit_ne (a := C₆) (b := C₁₂) (by decide)]),
        Finset.card_pair (circuit_ne (a := C₉) (b := C₁₂) (by decide))]
  have hsupp : (support B₂).card = 5 := by
    have : support B₂ = ({1, 3, 4, 5} ∪ {1, 4, 6} ∪ {3, 5, 6} : Finset (Fin 7)) := by
      simp [B₂, support, C₆, C₉, C₁₂]
    rw [this]; decide
  have hr := rank_eq_three_of_four_le_card (by omega : 4 ≤ (support B₂).card)
  change nullity M (support B₂) < B₂.card
  unfold nullity
  omega

private lemma hB₃_stage0 : B₃ ∈ stage M 0 := by
  have hcard : B₃.card = 3 := by
    simp only [B₃]
    rw [Finset.card_insert_of_notMem (by simp [circuit_ne (a := C₁) (b := C₇) (by decide),
          circuit_ne (a := C₁) (b := C₉) (by decide)]),
        Finset.card_pair (circuit_ne (a := C₇) (b := C₉) (by decide))]
  have hsupp : (support B₃).card = 5 := by
    have : support B₃ = ({0, 1, 2, 4} ∪ {0, 2, 6} ∪ {1, 4, 6} : Finset (Fin 7)) := by
      simp [B₃, support, C₁, C₇, C₉]
    rw [this]; decide
  have hr := rank_eq_three_of_four_le_card (by omega : 4 ≤ (support B₃).card)
  change nullity M (support B₃) < B₃.card
  unfold nullity
  omega

private lemma hB₄_stage0 : B₄ ∈ stage M 0 := by
  have hcard : B₄.card = 4 := by
    simp only [B₄]
    rw [Finset.card_insert_of_notMem (by simp [circuit_ne (a := C₀) (b := C₁) (by decide),
          circuit_ne (a := C₀) (b := C₄) (by decide), circuit_ne (a := C₀) (b := C₆) (by decide)]),
        Finset.card_insert_of_notMem (by simp [circuit_ne (a := C₁) (b := C₄) (by decide),
          circuit_ne (a := C₁) (b := C₆) (by decide)]),
        Finset.card_pair (circuit_ne (a := C₄) (b := C₆) (by decide))]
  have hsupp : (support B₄).card = 6 := by
    have : support B₄ = ({0, 1, 3} ∪ {0, 1, 2, 4} ∪ {0, 2, 3, 5} ∪ {1, 3, 4, 5} : Finset (Fin 7)) := by
      simp [B₄, support, C₀, C₁, C₄, C₆]; decide
    rw [this]; decide
  have hr := rank_eq_three_of_four_le_card (by omega : 4 ≤ (support B₄).card)
  change nullity M (support B₄) < B₄.card
  unfold nullity
  omega

private lemma hD₁_stage1 : D₁ ∈ stage M 1 := by
  have hinter : B₁ ∩ B₂ = {C₁₂} := by
    ext x
    simp only [B₁, B₂, mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩
      · rcases h2 with h | h | h
        · exact absurd h (circuit_ne (by decide))
        · exact absurd h (circuit_ne (by decide))
        · exact absurd h (circuit_ne (by decide))
      · rcases h2 with h | h | h
        · exact absurd h (circuit_ne (by decide))
        · exact absurd h (circuit_ne (by decide))
        · exact absurd h (circuit_ne (by decide))
      · rfl
    · rintro rfl; simp
  have hnot : B₁ ∩ B₂ ∉ stage M 0 := by
    rw [hinter]
    intro hmem
    have := initial_card_ge_three hmem
    simp at this
  have her : (B₁ ∪ B₂).erase C₁₂ = D₁ := by
    ext x
    simp only [B₁, B₂, D₁, mem_erase, mem_union, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hne, (rfl | rfl | rfl) | (rfl | rfl | rfl)⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact absurd rfl hne
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact absurd rfl hne
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨circuit_ne (by decide), Or.inl (Or.inl rfl)⟩
      · exact ⟨circuit_ne (by decide), Or.inr (Or.inl rfl)⟩
      · exact ⟨circuit_ne (by decide), Or.inl (Or.inr (Or.inl rfl))⟩
      · exact ⟨circuit_ne (by decide), Or.inr (Or.inr (Or.inl rfl))⟩
  refine ⟨D₁, Or.inr ⟨B₁, hB₁_stage0, B₂, hB₂_stage0, hnot, C₁₂, ?_, her.symm⟩, Subset.rfl⟩
  rw [hinter]
  exact mem_singleton_self C₁₂

private lemma hD₂_stage2 : D₂ ∈ stage M 2 := by
  have hinter : B₃ ∩ D₁ = {C₇, C₉} := by
    ext x
    simp only [B₃, D₁, mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, h2⟩
      · rcases h2 with h | h | h | h
        · exact absurd h (circuit_ne (by decide))
        · exact absurd h (circuit_ne (by decide))
        · exact absurd h (circuit_ne (by decide))
        · exact absurd h (circuit_ne (by decide))
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl) <;> simp
  have hnot_init : B₃ ∩ D₁ ∉ initial M := by
    rw [hinter]
    intro hmem
    have h3 := initial_card_ge_three hmem
    have h2 : ({C₇, C₉} : Finset (Circuits M)).card = 2 :=
      Finset.card_pair (circuit_ne (by decide))
    omega
  have hnot : B₃ ∩ D₁ ∉ stage M 1 := by
    apply not_mem_stage_of_card_le_three _ hnot_init
    rw [hinter, Finset.card_pair (circuit_ne (by decide))]
    omega
  have her : (B₃ ∪ D₁).erase C₉ = D₂ := by
    ext x
    simp only [B₃, D₁, D₂, mem_erase, mem_union, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hne, (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact absurd rfl hne
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact absurd rfl hne
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨circuit_ne (by decide), Or.inl (Or.inl rfl)⟩
      · exact ⟨circuit_ne (by decide), Or.inr (Or.inl rfl)⟩
      · exact ⟨circuit_ne (by decide), Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨circuit_ne (by decide), Or.inl (Or.inr (Or.inl rfl))⟩
  refine ⟨D₂, Or.inr ⟨B₃, stage_mono 0 hB₃_stage0, D₁, hD₁_stage1, hnot, C₉, ?_, her.symm⟩, Subset.rfl⟩
  rw [hinter]
  simp

private lemma hW_stage3 : W ∈ stage M 3 := by
  have hinter : B₄ ∩ D₂ = I_set := by
    ext x
    simp only [B₄, D₂, I_set, mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h2⟩
      · rcases h2 with h | h | h | h
        · exact absurd h (circuit_ne (by decide))
        · exact absurd h (circuit_ne (by decide))
        · exact absurd h (circuit_ne (by decide))
        · exact absurd h (circuit_ne (by decide))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl) <;> simp
  have hIcard : I_set.card = 3 := by
    simp only [I_set]
    rw [Finset.card_insert_of_notMem (by simp [circuit_ne (a := C₁) (b := C₄) (by decide),
          circuit_ne (a := C₁) (b := C₆) (by decide)]),
        Finset.card_pair (circuit_ne (a := C₄) (b := C₆) (by decide))]
  have hInot_init : I_set ∉ initial M := by
    have hsupp : (support I_set).card = 6 := by
      have : support I_set = ({0, 1, 2, 4} ∪ {0, 2, 3, 5} ∪ {1, 3, 4, 5} : Finset (Fin 7)) := by
        simp [I_set, support, C₁, C₄, C₆]
      rw [this]; decide
    have hr := rank_eq_three_of_four_le_card (by omega : 4 ≤ (support I_set).card)
    intro hmem
    have hlt : nullity M (support I_set) < I_set.card := hmem
    unfold nullity at hlt
    omega
  have hnot : B₄ ∩ D₂ ∉ stage M 2 := by
    rw [hinter]
    exact not_mem_stage_of_card_le_three (by omega) hInot_init
  have her : (B₄ ∪ D₂).erase C₁ = W := by
    ext x
    simp only [B₄, D₂, W, mem_erase, mem_union, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hne, (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)⟩
      · exact Or.inl rfl
      · exact absurd rfl hne
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact absurd rfl hne
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨circuit_ne (by decide), Or.inl (Or.inl rfl)⟩
      · exact ⟨circuit_ne (by decide), Or.inl (Or.inr (Or.inr (Or.inl rfl)))⟩
      · exact ⟨circuit_ne (by decide), Or.inl (Or.inr (Or.inr (Or.inr rfl)))⟩
      · exact ⟨circuit_ne (by decide), Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
  refine ⟨W, Or.inr ⟨B₄, stage_mono 1 (stage_mono 0 hB₄_stage0), D₂, hD₂_stage2, hnot, C₁, ?_, her.symm⟩, Subset.rfl⟩
  rw [hinter]
  simp [I_set]

private lemma hW_not_ow : ¬ OWDependent q W := by
  classical
  unfold OWDependent
  rw [not_not, Fintype.linearIndependent_iff]
  intro g hgsum x
  let ext_g : Circuits M → ZMod 2 := fun C => if h : C ∈ W then g ⟨C, h⟩ else 0
  have hsumW : ∑ C ∈ W, ext_g C • q C = 0 := by
    rw [← hgsum]
    symm
    refine Finset.sum_nbij (fun y : W => y.1) ?_ ?_ ?_ ?_
    · intro y _; exact y.2
    · intro a _ b _ h; exact Subtype.ext h
    · intro C hC; exact ⟨⟨C, hC⟩, mem_univ _, rfl⟩
    · intro y _; simp [ext_g, y.2]
  have hsum4 : ext_g C₀ • q C₀ + ext_g C₄ • q C₄ + ext_g C₆ • q C₆ + ext_g C₇ • q C₇ = 0 := by
    have h1 := hsumW
    simp only [W] at h1
    rw [Finset.sum_insert (by simp [circuit_ne (a := C₀) (b := C₄) (by decide),
          circuit_ne (a := C₀) (b := C₆) (by decide), circuit_ne (a := C₀) (b := C₇) (by decide)]),
        Finset.sum_insert (by simp [circuit_ne (a := C₄) (b := C₆) (by decide),
          circuit_ne (a := C₄) (b := C₇) (by decide)]),
        Finset.sum_pair (circuit_ne (a := C₆) (b := C₇) (by decide))] at h1
    rw [← add_assoc, ← add_assoc] at h1
    exact h1
  have hq0 : q C₀ 6 = 0 ∧ q C₀ 4 = 0 ∧ q C₀ 2 = 0 ∧ q C₀ 0 = 1 := by simp [q, C₀]
  have hq4 : q C₄ 6 = 0 ∧ q C₄ 4 = 0 ∧ q C₄ 2 = 1 ∧ q C₄ 0 = 1 := by simp [q, C₄]
  have hq6 : q C₆ 6 = 0 ∧ q C₆ 4 = 1 ∧ q C₆ 2 = 0 ∧ q C₆ 0 = 0 := by simp [q, C₆]
  have hq7 : q C₇ 6 = 1 ∧ q C₇ 4 = 0 ∧ q C₇ 2 = 1 ∧ q C₇ 0 = 1 := by simp [q, C₇]
  have h7 : ext_g C₇ = 0 := by
    have hev := congrFun hsum4 (6 : Fin 7)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      hq0.1, hq4.1, hq6.1, hq7.1, mul_zero, mul_one, zero_add] at hev
    exact hev
  have h6 : ext_g C₆ = 0 := by
    have hev := congrFun hsum4 (4 : Fin 7)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      hq0.2.1, hq4.2.1, hq6.2.1, hq7.2.1, mul_zero, mul_one, zero_add, add_zero] at hev
    exact hev
  have h4 : ext_g C₄ = 0 := by
    have hev := congrFun hsum4 (2 : Fin 7)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      hq0.2.2.1, hq4.2.2.1, hq6.2.2.1, hq7.2.2.1, h7, mul_zero, mul_one, zero_add, add_zero] at hev
    exact hev
  have h0 : ext_g C₀ = 0 := by
    have hev := congrFun hsum4 (0 : Fin 7)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      hq0.2.2.2, hq4.2.2.2, hq6.2.2.2, hq7.2.2.2, h7, h4, mul_zero, mul_one, add_zero] at hev
    exact hev
  have hx_eq : g x = ext_g x.1 := by simp [ext_g, x.2]
  rw [hx_eq]
  have hxmem : x.1 = C₀ ∨ x.1 = C₄ ∨ x.1 = C₆ ∨ x.1 = C₇ := by
    simpa [W] using x.2
  rcases hxmem with h | h | h | h
  · rw [h]; exact h0
  · rw [h]; exact h4
  · rw [h]; exact h6
  · rw [h]; exact h7

theorem main_disproof :
    ¬ (∀ (F : Type) [Field F] (E : Type) [Fintype E] [DecidableEq E] (M : Matroid E) (m : ℕ)
        (R : Matrix (Fin m) E F), IsRepresentation M R →
        ∀ q : Circuits M → E → F, (∀ C : Circuits M, IsCircuitVector R C.1 (q C)) →
          WeakGE (DerivedDependent M) (OWDependent q)) := by
  intro hmain
  have hweak := hmain (ZMod 2) (Fin 7) M 3 R hRep q hCV
  exact hW_not_ow (hweak W ⟨3, hW_stage3⟩)

end Arxiv220606881

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2206_06881.main) :=
  Arxiv220606881.main_disproof
