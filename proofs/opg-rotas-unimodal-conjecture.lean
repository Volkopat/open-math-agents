import OMAStatements.S_opg_rotas_unimodal_conjecture
import Mathlib

namespace RotaDisproof

open Set Submodule Module
open OMA.S_opg_rotas_unimodal_conjecture

noncomputable section
section Linear

variable {K V E : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite E]
variable (v : E → V)

omit [FiniteDimensional K V] in
private theorem dim_indep {I : Set E} (hI : LinearIndepOn K v I) :
    finrank K (span K (v '' I)) = I.ncard := by
  let := Fintype.ofFinite I
  rw [Set.image_eq_range, finrank_span_eq_card hI, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq]

private noncomputable def linearMatroid : Matroid E :=
  (IndepMatroid.ofFinite (E := univ) (Set.toFinite _) (LinearIndepOn K v)
    (by exact linearIndependent_empty_type)
    (fun {_ _} h hsub => h.mono hsub)
    (by
      intro I J hI hJ hcard
      by_contra! h
      have hle : span K (v '' J) ≤ span K (v '' I) := by
        apply span_le.mpr
        rintro _ ⟨e, he, rfl⟩
        by_contra hn
        exact h e he (fun hi => hn (subset_span ⟨e, hi, rfl⟩)) (hI.insert hn)
      have hh := Submodule.finrank_mono hle
      rw [dim_indep v hI, dim_indep v hJ] at hh
      omega)
    (fun {_} _ => subset_univ _)).matroid

private theorem basis_span {I X : Set E} (h : (linearMatroid (K := K) v).IsBasis I X) :
    span K (v '' I) = span K (v '' X) := by
  have hb := (Matroid.isBasis_iff (M := linearMatroid (K := K) v) (subset_univ X)).mp h
  refine le_antisymm (span_mono (image_mono hb.2.1)) (span_le.mpr ?_)
  rintro _ ⟨e, he, rfl⟩
  by_contra hn
  have hi : LinearIndepOn K v I := hb.1
  have hh := hb.2.2 (insert e I) (hi.insert hn) (subset_insert e I)
    (insert_subset he hb.2.1)
  exact hn (subset_span ⟨e, hh.symm ▸ mem_insert e I, rfl⟩)

private theorem linear_rank (X : Set E) :
    (linearMatroid (K := K) v).eRk X = ↑(finrank K (span K (v '' X))) := by
  obtain ⟨I, hI⟩ := (linearMatroid (K := K) v).exists_isBasis X (subset_univ _)
  rw [← basis_span v hI, dim_indep v (show LinearIndepOn K v I from hI.indep),
    hI.eRk_eq_encard, (Set.toFinite I).cast_ncard_eq]

private theorem linear_closure (X : Set E) :
    (linearMatroid (K := K) v).closure X = v ⁻¹' (span K (v '' X) : Set V) := by
  obtain ⟨I, hI⟩ := (linearMatroid (K := K) v).exists_isBasis X (subset_univ _)
  rw [← hI.closure_eq_closure, ← basis_span v hI]
  ext e
  rw [hI.indep.mem_closure_iff]
  change ((linearMatroid (K := K) v).Dep (insert e I) ∨ e ∈ I) ↔
    v e ∈ span K (v '' I)
  have hi : LinearIndepOn K v I := hI.indep
  rw [hi.mem_span_iff]
  by_cases he : e ∈ I
  · simp [he]
  · change ((linearMatroid (K := K) v).Dep (insert e I) ∨ e ∈ I) ↔ _
    rw [Matroid.dep_iff]
    change ((¬ LinearIndepOn K v (insert e I) ∧ insert e I ⊆ univ) ∨ e ∈ I) ↔ _
    simp [he]

private theorem linear_flat (X : Set E) :
    (linearMatroid (K := K) v).IsFlat X ↔
      ∀ e, v e ∈ span K (v '' X) → e ∈ X := by
  rw [Matroid.isFlat_iff_closure_eq, linear_closure]
  exact ⟨fun h e he => h ▸ he, fun h => Subset.antisymm h
    (fun e he => subset_span ⟨e, he, rfl⟩)⟩

private def FlatSpace (i : ℕ) :=
  {U : Submodule K V // span K (v '' (v ⁻¹' (U : Set V))) = U ∧ finrank K U = i}

private noncomputable def flatSpaceEquiv (i : ℕ) :
    {X : Set E // (linearMatroid (K := K) v).IsFlat X ∧
      (linearMatroid (K := K) v).eRk X = (i : ℕ∞)} ≃ FlatSpace (K := K) v i where
  toFun X := ⟨span K (v '' X.1), by
    have hx := Matroid.isFlat_iff_closure_eq.mp X.2.1
    rw [linear_closure] at hx
    exact ⟨by rw [hx], ENat.natCast_inj.mp ((linear_rank v X.1).symm.trans X.2.2)⟩⟩
  invFun U := ⟨v ⁻¹' (U.1 : Set V), by
    rw [linear_flat, linear_rank, U.2.1, U.2.2]
    exact ⟨fun _ h => h, rfl⟩⟩
  left_inv X := Subtype.ext (by
    exact (linear_closure v X.1).symm.trans X.2.1.closure)
  right_inv U := Subtype.ext U.2.1

private theorem whitney_space (i : ℕ) :
    whitneySecond (linearMatroid (K := K) v) i = Nat.card (FlatSpace (K := K) v i) := by
  rw [whitneySecond, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (flatSpaceEquiv v i)

end Linear
section Lift

variable {K V E : Type} [Field K] [AddCommGroup V] [Module K V]
variable (v : E → V)

private def lifted : Unit ⊕ (K × E) → K × V
  | .inl _ => (1, 0)
  | .inr (a, e) => (a, v e)

private abbrev sndL : K × V →ₗ[K] V := LinearMap.snd K K V
private abbrev apex : K × V := (1, 0)

private theorem map_lift_span (S : Submodule K (K × V)) :
    (span K (lifted v '' (lifted v ⁻¹' (S : Set (K × V))))).map sndL =
      span K (v '' (v ⁻¹' (S.map sndL : Set V))) := by
  rw [Submodule.map_span, Set.image_image]
  apply le_antisymm <;> apply span_le.mpr
  · rintro _ ⟨e, he, rfl⟩
    cases e with
    | inl a => exact zero_mem _
    | inr q => exact subset_span ⟨q.2, ⟨(q.1, v q.2), he, rfl⟩, rfl⟩
  · rintro _ ⟨e, ⟨⟨a, y⟩, ha, hy⟩, rfl⟩
    change y = v e at hy
    subst y
    exact subset_span ⟨.inr (a, e), ha, rfl⟩

private theorem snd_injOn (S : Submodule K (K × V)) (h : apex ∉ S) :
    Set.InjOn sndL (S : Set (K × V)) := by
  rintro ⟨a, x⟩ ha ⟨b, y⟩ hb (rfl : x = y)
  by_cases hab : a = b
  · subst b
    rfl
  exfalso
  apply h
  have hh : (a - b, (0 : V)) ∈ S := by
    simpa using S.sub_mem ha hb
  convert S.smul_mem (a - b)⁻¹ hh using 1
  simp [smul_eq_mul, sub_ne_zero.mpr hab]

private theorem vertical_eq {S : Submodule K (K × V)} (h : apex ∈ S) :
    S = (S.map sndL).comap sndL := by
  rw [Submodule.comap_map_eq]
  symm
  rw [sup_eq_left]
  rintro ⟨a, x⟩ hx
  change x = 0 at hx
  subst x
  simpa [smul_eq_mul] using S.smul_mem a h

private def verticalMap (U : Submodule K V) : K × U →ₗ[K] K × V :=
  (LinearMap.fst K K U).prod (U.subtype.comp (LinearMap.snd K K U))

private def vertical (U : Submodule K V) : Submodule K (K × V) :=
  (verticalMap U).range

private theorem vertical_comap (U : Submodule K V) :
    vertical U = U.comap sndL := by
  ext ⟨a, x⟩
  constructor
  · rintro ⟨⟨b, y⟩, h⟩
    change x ∈ U
    have he : (y : V) = x := congrArg Prod.snd h
    exact he ▸ y.2
  · intro h
    exact ⟨(a, ⟨x, h⟩), rfl⟩

private theorem vertical_proj (U : Submodule K V) : (vertical U).map sndL = U := by
  rw [vertical_comap, map_comap_eq_of_surjective]
  exact fun x => ⟨(0, x), rfl⟩

private theorem vertical_dim [FiniteDimensional K V] (U : Submodule K V) :
    finrank K (vertical U) = finrank K U + 1 := by
  rw [vertical, LinearMap.finrank_range_of_inj, Module.finrank_prod, Module.finrank_self,
    add_comm]
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  exact Prod.ext (show a = b from congrArg Prod.fst h)
    (Subtype.ext (show (x : V) = (y : V) from congrArg Prod.snd h))

private def graph (U : Submodule K V) (f : U →ₗ[K] K) : Submodule K (K × V) :=
  (f.prod U.subtype).range

private theorem graph_proj (U : Submodule K V) (f : U →ₗ[K] K) :
    (graph U f).map sndL = U := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact y.2
  · intro hx
    exact ⟨(f ⟨x, hx⟩, x), ⟨⟨x, hx⟩, rfl⟩, rfl⟩

private theorem graph_dim (U : Submodule K V) (f : U →ₗ[K] K) :
    finrank K (graph U f) = finrank K U := by
  rw [graph, LinearMap.finrank_range_of_inj]
  exact fun _ _ h => Subtype.ext (congrArg Prod.snd h)

private theorem graph_no_apex (U : Submodule K V) (f : U →ₗ[K] K) :
    apex ∉ graph U f := by
  rintro ⟨y, hy⟩
  have hz : y = 0 := Subtype.ext (congrArg Prod.snd hy)
  have hh : f y = 1 := congrArg Prod.fst hy
  simp [hz] at hh

private theorem is_graph (S : Submodule K (K × V)) (h : apex ∉ S) :
    ∃ f : (S.map sndL : Submodule K V) →ₗ[K] K, graph (S.map sndL) f = S := by
  let L : S →ₗ[K] (S.map sndL : Submodule K V) :=
    ((sndL).domRestrict S).codRestrict _ (fun x => ⟨x, x.2, rfl⟩)
  let e : S ≃ₗ[K] (S.map sndL : Submodule K V) :=
    LinearEquiv.ofBijective L ⟨fun x y hxy =>
      Subtype.ext (snd_injOn S h x.2 y.2 (congrArg Subtype.val hxy)),
      fun ⟨x, y, hy, hxy⟩ => ⟨⟨y, hy⟩, Subtype.ext hxy⟩⟩
  let f : (S.map sndL : Submodule K V) →ₗ[K] K :=
    ((LinearMap.fst K K V).domRestrict S).comp e.symm.toLinearMap
  have he (x : S.map sndL) : (e.symm x : K × V).2 = (x : V) :=
    congrArg Subtype.val (e.apply_symm_apply x)
  have hf (x : S.map sndL) : (f x, (x : V)) = (e.symm x : K × V) :=
    Prod.ext rfl (he x).symm
  refine ⟨f, ?_⟩
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    change (f x, (x : V)) ∈ S
    rw [hf]
    exact (e.symm x).2
  · intro hz
    refine ⟨e ⟨z, hz⟩, ?_⟩
    change (f (e ⟨z, hz⟩), (e ⟨z, hz⟩ : V)) = z
    rw [hf, e.symm_apply_apply]

private theorem graph_inj {U : Submodule K V} {f g : U →ₗ[K] K}
    (h : graph U f = graph U g) : f = g := by
  ext x
  have hx : (f x, (x : V)) ∈ graph U g := h ▸ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hx
  have he : y = x := Subtype.ext (congrArg Prod.snd hy)
  exact (show g y = f x from congrArg Prod.fst hy).symm.trans (congrArg g he)

private theorem vertical_gen {U : Submodule K V}
    (hU : span K (v '' (v ⁻¹' (U : Set V))) = U) :
    span K (lifted v '' (lifted v ⁻¹' (vertical U : Set (K × V)))) = vertical U := by
  let T := span K (lifted v '' (lifted v ⁻¹' (vertical U : Set (K × V))))
  have ht : apex ∈ T := subset_span ⟨.inl (), by
    change apex ∈ vertical U
    rw [vertical_comap]
    exact U.zero_mem, rfl⟩
  change T = vertical U
  rw [vertical_eq ht, vertical_comap]
  congr 1
  dsimp only [T]
  rw [map_lift_span, vertical_proj, hU]

private theorem graph_gen {U : Submodule K V}
    (hU : span K (v '' (v ⁻¹' (U : Set V))) = U) (f : U →ₗ[K] K) :
    span K (lifted v '' (lifted v ⁻¹' (graph U f : Set (K × V)))) = graph U f := by
  let S := graph U f
  let T := span K (lifted v '' (lifted v ⁻¹' (S : Set (K × V))))
  have hts : T ≤ S := span_le.mpr (image_preimage_subset _ _)
  have ht : T.map sndL = U := by
    dsimp only [T, S]
    rw [map_lift_span, graph_proj, hU]
  apply le_antisymm hts
  intro z hz
  have hz' : sndL z ∈ T.map sndL := by
    rw [ht, ← graph_proj U f]
    exact ⟨z, hz, rfl⟩
  obtain ⟨y, hy, hyz⟩ := hz'
  exact snd_injOn S (graph_no_apex U f) (hts hy) hz hyz ▸ hy
variable [FiniteDimensional K V] [Finite E] [Fintype K]

private def liftEquiv (i : ℕ) :
    (FlatSpace (K := K) v i ⊕
      (Σ U : FlatSpace (K := K) v (i + 1), U.1 →ₗ[K] K)) ≃
      FlatSpace (K := K) (lifted (K := K) v) (i + 1) := by
  let f : (FlatSpace (K := K) v i ⊕
      (Σ U : FlatSpace (K := K) v (i + 1), U.1 →ₗ[K] K)) →
      FlatSpace (K := K) (lifted (K := K) v) (i + 1)
    | .inl U => ⟨vertical U.1, vertical_gen v U.2.1, by rw [vertical_dim, U.2.2]⟩
    | .inr ⟨U, g⟩ => ⟨graph U.1 g, graph_gen v U.2.1 g, by rw [graph_dim, U.2.2]⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    have hs := congrArg Subtype.val h
    have hp := congrArg (fun S : Submodule K (K × V) => S.map sndL) hs
    cases x with
    | inl U =>
      cases y with
      | inl W =>
        change (vertical U.1).map sndL = (vertical W.1).map sndL at hp
        rw [vertical_proj, vertical_proj] at hp
        exact congrArg Sum.inl (Subtype.ext hp)
      | inr y =>
        change vertical U.1 = graph y.1.1 y.2 at hs
        have ha : apex ∈ vertical U.1 := by
          rw [vertical_comap]
          exact U.1.zero_mem
        exact (graph_no_apex y.1.1 y.2 (hs ▸ ha)).elim
    | inr x =>
      obtain ⟨U, g⟩ := x
      cases y with
      | inl W =>
        change graph U.1 g = vertical W.1 at hs
        have ha : apex ∈ vertical W.1 := by
          rw [vertical_comap]
          exact W.1.zero_mem
        exact (graph_no_apex U.1 g (hs.symm ▸ ha)).elim
      | inr y =>
        obtain ⟨W, hW⟩ := y
        change (graph U.1 g).map sndL = (graph W.1 hW).map sndL at hp
        rw [graph_proj, graph_proj] at hp
        have he : U = W := Subtype.ext hp
        subst W
        change graph U.1 g = graph U.1 hW at hs
        rw [graph_inj hs]
  · intro S
    have hg : span K (v '' (v ⁻¹' (S.1.map sndL : Set V))) = S.1.map sndL := by
      rw [← map_lift_span, S.2.1]
    by_cases h : apex ∈ S.1
    · have hs : vertical (S.1.map sndL) = S.1 :=
        (vertical_comap _).trans (vertical_eq h).symm
      have hr := vertical_dim (S.1.map sndL)
      rw [hs, S.2.2] at hr
      exact ⟨.inl ⟨S.1.map sndL, hg, by omega⟩, Subtype.ext hs⟩
    · obtain ⟨g, hs⟩ := is_graph S.1 h
      have hr := graph_dim (S.1.map sndL) g
      rw [hs, S.2.2] at hr
      exact ⟨.inr ⟨⟨S.1.map sndL, hg, hr.symm⟩, g⟩, Subtype.ext hs⟩

private theorem lift_count (i : ℕ) :
    whitneySecond (linearMatroid (K := K) (lifted (K := K) v)) (i + 1) =
      Fintype.card K ^ (i + 1) * whitneySecond (linearMatroid (K := K) v) (i + 1) +
        whitneySecond (linearMatroid (K := K) v) i := by
  classical
  let (j : ℕ) : Finite (FlatSpace (K := K) v j) :=
    Finite.of_equiv _ (flatSpaceEquiv v j)
  let := Fintype.ofFinite (FlatSpace (K := K) v (i + 1))
  let (U : FlatSpace (K := K) v (i + 1)) : Finite (U.1 →ₗ[K] K) :=
    Module.finite_of_finite K
  rw [whitney_space, whitney_space, whitney_space,
    ← Nat.card_congr (liftEquiv v i), Nat.card_sum, Nat.card_sigma, add_comm]
  congr 1
  have hc (U : FlatSpace (K := K) v (i + 1)) :
      Nat.card (U.1 →ₗ[K] K) = Fintype.card K ^ (i + 1) := by
    let b := Module.finBasis K U.1
    rw [← Nat.card_congr (b.constr K (M' := K)).toEquiv, Nat.card_fun, Nat.card_eq_fintype_card,
      Nat.card_fin, U.2.2]
  simp_rw [hc]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card, mul_comm]
  rfl

end Lift
section Quotient

variable {K E A V W : Type} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [FiniteDimensional K V]

private theorem dim_map_add (f : V →ₗ[K] W) (T : Submodule K V) :
    finrank K (T.map f) + finrank K (T ⊓ f.ker : Submodule K V) = finrank K T := by
  have h := (f.domRestrict T).finrank_range_add_finrank_ker
  have hr : (f.domRestrict T).range = T.map f := by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hk : (f.domRestrict T).ker.map T.subtype = T ⊓ f.ker := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hT, hf⟩
      exact ⟨⟨x, hT⟩, hf, rfl⟩
  rw [hr, (equivSubtypeMap T (f.domRestrict T).ker).finrank_eq, hk] at h
  exact h

variable [Fintype E] [DecidableEq E]
variable [AddCommGroup A] [Module K A]

private def restrict (S : Set E) : (E → K) →ₗ[K] (S → K) :=
  LinearMap.funLeft K K Subtype.val

omit [Fintype E] [DecidableEq E] in
private theorem restrict_surj (S : Set E) : Function.Surjective (restrict (K := K) S) := by
  classical
  intro f
  exact ⟨fun x => if h : x ∈ S then f ⟨x, h⟩ else 0, funext fun x => by
    simp [restrict, x.2]⟩

omit [Fintype E] in
private def unitVec (e : E) : E → K := Pi.single e 1

omit [Fintype E] in
@[simp] private theorem unitVec_apply (e x : E) :
    unitVec (K := K) e x = if x = e then 1 else 0 := by
  simp [unitVec, Pi.single_apply]

private theorem span_single_compl (S : Set E) :
    span K ((fun e : E => unitVec (K := K) e) '' Sᶜ) = (restrict (K := K) S).ker := by
  classical
  apply le_antisymm
  · refine span_le.mpr ?_
    rintro _ ⟨e, he, rfl⟩
    change (fun x : S => unitVec (K := K) e x.1) = 0
    funext x
    have hne : e ≠ x.1 := fun h => he (h.symm ▸ x.2)
    simp [hne.symm]
  · intro f hf
    have hzero (e : E) (he : e ∈ S) : f e = 0 := congrFun hf ⟨e, he⟩
    have hsum : (∑ e : E, f e • unitVec (K := K) e) = f := by
      ext x
      simp [Finset.sum_apply]
    rw [← hsum]
    apply Submodule.sum_mem
    intro e _
    by_cases h : e ∈ S
    · simp [hzero e h]
    · exact smul_mem _ _ (subset_span ⟨e, h, rfl⟩)

variable (row : A →ₗ[K] (E → K))

private def quotientVec (e : E) : (E → K) ⧸ row.range :=
  row.range.mkQ (unitVec e)

private theorem quotient_span (S : Set E) :
    span K (quotientVec row '' Sᶜ) = ((restrict (K := K) S).ker).map row.range.mkQ := by
  rw [← span_single_compl, Submodule.map_span, Set.image_image]
  rfl

private theorem quotient_mem (S : Set E) (e : E) :
    quotientVec row e ∈ span K (quotientVec row '' Sᶜ) ↔
      ∃ a : A, ∀ x : S, row a x.1 = unitVec (K := K) e x.1 := by
  rw [quotient_span]
  constructor
  · rintro ⟨f, hf, h⟩
    have hm : unitVec (K := K) e - f ∈ row.range :=
      (Submodule.Quotient.eq _).mp h.symm
    obtain ⟨a, ha⟩ := hm
    refine ⟨a, fun x => ?_⟩
    have hz : f x.1 = 0 := congrFun hf x
    rw [ha]
    change unitVec (K := K) e x.1 - f x.1 = _
    rw [hz, sub_zero]
  · rintro ⟨a, ha⟩
    refine ⟨unitVec (K := K) e - row a, ?_, ?_⟩
    · change (fun x : S => unitVec (K := K) e x.1 - row a x.1) = 0
      ext x
      exact sub_eq_zero.mpr (ha x).symm
    · apply (Submodule.Quotient.eq _).mpr
      simp

private theorem quotient_dim (S : Set E) :
    finrank K (span K (quotientVec row '' Sᶜ)) + S.ncard =
      finrank K ((E → K) ⧸ row.range) +
        finrank K ((restrict (K := K) S).comp row).range := by
  have h1 := dim_map_add row.range.mkQ (restrict (K := K) S).ker
  rw [Submodule.ker_mkQ, ← quotient_span] at h1
  have h2 := dim_map_add (restrict (K := K) S) row.range
  rw [← LinearMap.range_comp, inf_comm] at h2
  have h3 := (restrict (K := K) S).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (restrict_surj S), finrank_top] at h3
  let := Fintype.ofFinite S
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h3
  have h4 := row.range.finrank_quotient_add_finrank
  omega

end Quotient
section Theta

private abbrev Ground := Unit ⊕ (Fin 3 × Fin 300)
private abbrev Blocks := Fin 3 → Finset (Fin 300)

variable (K : Type) [Field K]

private def rowMap : (Fin 3 → K) →ₗ[K] Ground → K :=
  LinearMap.pi fun
    | .inl _ => ∑ i : Fin 3, LinearMap.proj i
    | .inr (i, _) => LinearMap.proj i

@[simp] private theorem row_inl (a : Fin 3 → K) (u : Unit) :
    rowMap K a (.inl u) = ∑ i, a i := by
  simp [rowMap, LinearMap.sum_apply]

@[simp] private theorem row_inr (a : Fin 3 → K) (i : Fin 3) (j : Fin 300) :
    rowMap K a (.inr (i, j)) = a i := rfl

private abbrev baseVec := quotientVec (rowMap K)

private def missing (b : Bool) (A : Blocks) : Set Ground
  | .inl _ => b = true
  | .inr (i, j) => j ∈ A i

@[simp] private theorem missing_inl (b : Bool) (A : Blocks) (u : Unit) :
    Sum.inl u ∈ missing b A ↔ b = true := Iff.rfl

@[simp] private theorem missing_inr (b : Bool) (A : Blocks) (i : Fin 3) (j : Fin 300) :
    Sum.inr (i, j) ∈ missing b A ↔ j ∈ A i := Iff.rfl

private def missingEquiv : Bool × Blocks ≃ Set Ground := by
  classical
  refine Equiv.ofBijective (fun q => missing q.1 q.2) ⟨?_, ?_⟩
  · rintro ⟨b, A⟩ ⟨c, B⟩ h
    change missing b A = missing c B at h
    congr 1
    · have hu : b = true ↔ c = true := by
        simpa only [missing_inl] using Set.ext_iff.mp h (.inl ())
      cases b <;> cases c <;> simp_all
    · funext i
      ext j
      simpa only [missing_inr] using Set.ext_iff.mp h (.inr (i, j))
  · intro S
    refine ⟨(decide (Sum.inl () ∈ S), fun i => Finset.univ.filter (fun j => .inr (i,j) ∈ S)), ?_⟩
    ext e
    cases e with
    | inl u => cases u; simp
    | inr q => obtain ⟨i, j⟩ := q; simp

private def allowed (b : Bool) (A : Blocks) : Prop :=
  if b then ∀ i, (A i).Nonempty else ∀ i, (A i).card ≠ 1

private theorem base_flat (b : Bool) (A : Blocks) :
    (linearMatroid (K := K) (baseVec K)).IsFlat (missing b A)ᶜ ↔ allowed b A := by
  classical
  rw [linear_flat]
  simp only [quotient_mem, Set.mem_compl_iff]
  cases b with
  | false =>
    change (∀ e, (∃ a : Fin 3 → K, ∀ x : missing false A,
      rowMap K a x.1 = unitVec e x.1) → e ∉ missing false A) ↔
        ∀ i, (A i).card ≠ 1
    constructor
    · intro h i hi
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hi
      apply h (.inr (i,j)) _ (by simp [hj])
      refine ⟨unitVec i, fun ⟨x, hx⟩ => ?_⟩
      cases x with
      | inl u => simp at hx
      | inr q =>
        obtain ⟨l, k⟩ := q
        by_cases hl : l = i
        · subst l
          have hk : k = j := by simpa [hj] using hx
          subst k
          simp
        · simp [hl]
    · intro h e ⟨a, ha⟩ he
      cases e with
      | inl u => simp at he
      | inr q =>
        obtain ⟨i, j⟩ := q
        have hj : j ∈ A i := he
        have hh : A i ≠ {j} := fun hEq => h i (by simp [hEq])
        obtain ⟨k, hk, hkj⟩ : ∃ k ∈ A i, k ≠ j := by
          by_contra! hn
          exact hh (Finset.Subset.antisymm
            (fun x hx => Finset.mem_singleton.mpr (hn x hx)) (Finset.singleton_subset_iff.mpr hj))
        have h1 := ha ⟨.inr (i, j), hj⟩
        have h0 := ha ⟨.inr (i, k), hk⟩
        simp [hkj] at h1 h0
        exact zero_ne_one (h0.symm.trans h1)
  | true =>
    change (∀ e, (∃ a : Fin 3 → K, ∀ x : missing true A,
      rowMap K a x.1 = unitVec e x.1) → e ∉ missing true A) ↔
        ∀ i, (A i).Nonempty
    constructor
    · intro h i
      by_contra hi
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hi
      apply h (.inl ()) _ (by simp)
      refine ⟨unitVec i, fun ⟨x, hx⟩ => ?_⟩
      cases x with
      | inl u => cases u; simp
      | inr q =>
        obtain ⟨l, j⟩ := q
        have hli : l ≠ i := by rintro rfl; simp [hempty] at hx
        simp [hli]
    · intro h e ⟨a, ha⟩ he
      have hs := ha ⟨.inl (), by simp⟩
      cases e with
      | inl u =>
        cases u
        have hz : a = 0 := by
          funext i
          obtain ⟨j, hj⟩ := h i
          simpa using ha ⟨.inr (i,j), hj⟩
        simp [hz] at hs
      | inr q =>
        obtain ⟨i,j⟩ := q
        have hz : a = unitVec i := by
          funext l
          by_cases hl : l = i
          · subst l
            simpa using ha ⟨.inr (i,j), he⟩
          · obtain ⟨k, hk⟩ := h l
            simpa [hl] using ha ⟨.inr (l,k), hk⟩
        have hs1 : ∑ l : Fin 3, unitVec (K := K) i l = 1 := by simp
        simp only [row_inl, unitVec_apply, Sum.inl_ne_inr, if_false] at hs
        rw [hz, hs1] at hs
        exact one_ne_zero hs
private abbrev Active (A : Blocks) := {i : Fin 3 // (A i).Nonempty}

private theorem row_injective : Function.Injective (rowMap K) := by
  intro a b h
  funext i
  exact congrFun h (.inr (i, 0))

private theorem base_dim :
    finrank K ((Ground → K) ⧸ (rowMap K).range) = 898 := by
  rw [Submodule.finrank_quotient, LinearMap.finrank_range_of_inj (row_injective K),
    Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
  simp [Ground]

private theorem row_restrict_dim (b : Bool) (A : Blocks) (h : allowed b A) :
    finrank K ((restrict (K := K) (missing b A)).comp (rowMap K)).range =
      Fintype.card (Active A) := by
  classical
  cases b with
  | false =>
    let g : missing false A → Active A
      | ⟨.inl u, hu⟩ => False.elim (by simp at hu)
      | ⟨.inr (i, j), hj⟩ => ⟨i, j, hj⟩
    have hg : Function.Surjective g := by
      rintro ⟨i, j, hj⟩
      exact ⟨⟨.inr (i, j), hj⟩, rfl⟩
    let P : (Fin 3 → K) →ₗ[K] (Active A → K) := LinearMap.funLeft K K Subtype.val
    let Q : (Active A → K) →ₗ[K] (missing false A → K) := LinearMap.funLeft K K g
    have hp : Function.Surjective P := restrict_surj (fun i => (A i).Nonempty)
    have hq : Function.Injective Q := fun a c hac => funext fun x => by
      obtain ⟨y, rfl⟩ := hg x
      exact congrFun hac y
    have he : (restrict (K := K) (missing false A)).comp (rowMap K) = Q.comp P := by
      ext a ⟨e, he⟩
      cases e with
      | inl u => simp at he
      | inr q => obtain ⟨i, j⟩ := q; rfl
    rw [he, LinearMap.range_comp, LinearMap.range_eq_top.mpr hp, Submodule.map_top,
      LinearMap.finrank_range_of_inj hq, Module.finrank_fintype_fun_eq_card]
  | true =>
    have ha : ∀ i, (A i).Nonempty := h
    have hi : Function.Injective ((restrict (K := K) (missing true A)).comp (rowMap K)) := by
      intro a c hac
      funext i
      obtain ⟨j, hj⟩ := ha i
      exact congrFun hac ⟨.inr (i,j), hj⟩
    rw [LinearMap.finrank_range_of_inj hi, Module.finrank_fintype_fun_eq_card]
    apply Fintype.card_congr
    exact Equiv.ofBijective (fun i => ⟨i, ha i⟩)
      ⟨fun _ _ e => congrArg Subtype.val e, fun i => ⟨i.1, rfl⟩⟩

private def missingCardEquiv (b : Bool) (A : Blocks) :
    missing b A ≃ ({_u : Unit // b = true} ⊕ (Σ i : Fin 3, ↥(A i))) where
  toFun
    | ⟨.inl u, hu⟩ => .inl ⟨u, hu⟩
    | ⟨.inr (i, j), hj⟩ => .inr ⟨i, ⟨j, hj⟩⟩
  invFun
    | .inl ⟨u, hu⟩ => ⟨.inl u, hu⟩
    | .inr ⟨i, j⟩ => ⟨.inr (i, j.1), j.2⟩
  left_inv := by rintro ⟨u | ⟨i, j⟩, _⟩ <;> rfl
  right_inv := by rintro (⟨u, hu⟩ | ⟨i, j⟩) <;> rfl

private theorem missing_card (b : Bool) (A : Blocks) :
    (missing b A).ncard = b.toNat + ∑ i, (A i).card := by
  rw [← Nat.card_coe_set_eq, Nat.card_congr (missingCardEquiv b A), Nat.card_sum,
    Nat.card_sigma]
  have hu : Nat.card {_u : Unit // b = true} = b.toNat := by
    classical
    cases b <;> simp [Nat.card_eq_fintype_card]
  rw [hu]
  simp [Nat.card_eq_fintype_card]

private def nullity (b : Bool) (a : Fin 3 → ℕ) : ℕ :=
  b.toNat + ∑ i, (a i - 1)

private theorem active_add_nullity (b : Bool) (A : Blocks) :
    (missing b A).ncard = nullity b (fun i => (A i).card) + Fintype.card (Active A) := by
  classical
  have hc : Fintype.card (Active A) = ∑ i : Fin 3, if (A i).Nonempty then 1 else 0 := by
    rw [Fintype.card_subtype, Finset.sum_boole]
    rfl
  rw [missing_card, nullity, hc, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (A i).Nonempty
  · have := Finset.card_pos.mpr h
    simp only [h, if_true]
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

private theorem base_flat_rank (b : Bool) (A : Blocks) (h : allowed b A) :
    finrank K (span K (baseVec K '' (missing b A)ᶜ)) +
      nullity b (fun i => (A i).card) = 898 := by
  have hr := quotient_dim (rowMap K) (missing b A)
  rw [base_dim K, row_restrict_dim K b A h, active_add_nullity] at hr
  exact Nat.add_right_cancel (by simpa only [add_assoc] using hr)
private def allowedSizes (b : Bool) (a : Fin 3 → ℕ) : Prop :=
  ∀ i, if b then 0 < a i else a i ≠ 1

private theorem allowed_card (b : Bool) (A : Blocks) :
    allowed b A ↔ allowedSizes b (fun i => (A i).card) := by
  cases b <;> simp [allowed, allowedSizes, Finset.card_pos]

private abbrev DataAt (d : ℕ) :=
  {q : Bool × Blocks // allowedSizes q.1 (fun i => (q.2 i).card) ∧
    nullity q.1 (fun i => (q.2 i).card) = d}

private theorem base_count_data (d : ℕ) (hd : d ≤ 898) :
    whitneySecond (linearMatroid (K := K) (baseVec K)) (898 - d) =
      Nat.card (DataAt d) := by
  rw [whitneySecond, ← Nat.card_coe_set_eq]
  symm
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (missingEquiv.trans ⟨Set.compl, Set.compl, compl_compl, compl_compl⟩)
  rintro ⟨b, A⟩
  change (allowedSizes b (fun i => (A i).card) ∧ nullity b (fun i => (A i).card) = d) ↔
    (linearMatroid (K := K) (baseVec K)).IsFlat (missing b A)ᶜ ∧
    (linearMatroid (K := K) (baseVec K)).eRk (missing b A)ᶜ = ((898 - d : ℕ) : ℕ∞)
  rw [base_flat, linear_rank, ENat.natCast_inj, ← allowed_card]
  apply and_congr_right
  intro h
  have hr := base_flat_rank K b A h
  omega

private abbrev Sizes := Bool × (Fin 3 → Fin 6)

private def good (d : ℕ) (q : Sizes) : Prop :=
  allowedSizes q.1 (fun i => (q.2 i).val) ∧ nullity q.1 (fun i => (q.2 i).val) = d

private instance (d : ℕ) (q : Sizes) : Decidable (good d q) := by
  unfold good allowedSizes
  cases q.1 <;> dsimp only [Bool.false_eq_true, if_false, if_true] <;> infer_instance

private abbrev Pattern (d : ℕ) := {q : Sizes // good d q}

private def sizes {d : ℕ} (hd : d ≤ 4) (q : DataAt d) : Pattern d :=
  ⟨(q.1.1, fun i => ⟨(q.1.2 i).card, by
    have hs : (q.1.2 i).card - 1 ≤ ∑ j : Fin 3, ((q.1.2 j).card - 1) :=
      Finset.single_le_sum (fun j _ => Nat.zero_le ((q.1.2 j).card - 1))
        (Finset.mem_univ i)
    have h := q.2.2
    dsimp only [nullity] at h
    omega⟩), q.2⟩

private abbrev Choices {d : ℕ} (a : Pattern d) :=
  ∀ i : Fin 3, {s : Finset (Fin 300) // s.card = (a.1.2 i).val}

private def fiberChoices {d : ℕ} (hd : d ≤ 4) (a : Pattern d) :
    {q : DataAt d // sizes hd q = a} ≃ Choices a where
  toFun q i := ⟨q.1.1.2 i, congrArg (fun x : Pattern d => (x.1.2 i).val) q.2⟩
  invFun F := ⟨⟨(a.1.1, fun i => (F i).1), by
    have he : (fun i => (F i).1.card) = fun i => (a.1.2 i).val :=
      funext (fun i => (F i).2)
    change allowedSizes a.1.1 (fun i => (F i).1.card) ∧
      nullity a.1.1 (fun i => (F i).1.card) = d
    rw [he]
    exact a.2⟩, by
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · rfl
    · funext i
      exact Fin.ext (F i).2⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg (fun x : Pattern d => x.1.1) q.2).symm rfl
  right_inv F := funext (fun _ => Subtype.ext rfl)

private def W (d : ℕ) : ℕ :=
  ∑ a : Pattern d, ∏ i : Fin 3, Nat.fast_choose 300 (a.1.2 i).val

private theorem base_count (d : ℕ) (hd : d ≤ 4) :
    whitneySecond (linearMatroid (K := K) (baseVec K)) (898 - d) = W d := by
  rw [base_count_data K d (by omega),
    ← Nat.card_congr (Equiv.sigmaFiberEquiv (sizes hd)),
    Nat.card_congr (Equiv.sigmaCongrRight (fiberChoices hd)), Nat.card_sigma]
  unfold W
  apply Finset.sum_congr rfl
  intro a _
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  simp only [Fintype.card_finset_len, Fintype.card_fin,
    Nat.choose_eq_descFactorial_div_factorial, Nat.fast_choose]

end Theta
set_option maxRecDepth 4096 in
private theorem values :
    W 1 = 27134550 ∧ W 2 = 18157432800 ∧
      W 3 = 94429891158525 ∧ W 4 = 27572410695360180 := by
  decide +kernel
private abbrev Scalar := ZMod 1009

private instance : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

private def witness : Matroid (Unit ⊕ (Scalar × Ground)) :=
  linearMatroid (K := Scalar) (lifted (K := Scalar) (baseVec Scalar))

private def power (i : ℕ) : ℕ := 1009 ^ i

private theorem power_succ (i : ℕ) : power (i + 1) = power i * 1009 :=
  pow_succ 1009 i

private theorem power_lower (i : ℕ) (h : 2 ≤ i) : 1018081 ≤ power i :=
  Nat.pow_le_pow_right (n := 1009) (by decide) h

private theorem witness_count (i : ℕ) (hi : 894 ≤ i) (hj : i ≤ 896) :
    whitneySecond witness (i + 1) =
      power (i + 1) * W (897 - i) + W (898 - i) := by
  have h1 := base_count Scalar (897 - i) (by omega)
  have h2 := base_count Scalar (898 - i) (by omega)
  rw [show 898 - (897 - i) = i + 1 by omega] at h1
  rw [show 898 - (898 - i) = i by omega] at h2
  simpa only [witness, power, ZMod.card, h1, h2] using lift_count (K := Scalar) (baseVec Scalar) i

theorem witness_bad : ¬ IsUnimodal (whitneySecond witness) witness.eRank.toNat := by
  obtain ⟨h1, h2, h3, h4⟩ := values
  have c895 := witness_count 894 (by decide) (by decide)
  have c896 := witness_count 895 (by decide) (by decide)
  have c897 := witness_count 896 (by decide) (by decide)
  simp only [show 894 + 1 = 895 by decide, show 897 - 894 = 3 by decide,
    show 898 - 894 = 4 by decide] at c895
  simp only [show 895 + 1 = 896 by decide, show 897 - 895 = 2 by decide,
    show 898 - 895 = 3 by decide] at c896
  simp only [show 896 + 1 = 897 by decide, show 897 - 896 = 1 by decide,
    show 898 - 896 = 2 by decide] at c897
  rw [h3, h4] at c895
  rw [h2, h3] at c896
  rw [h1, h2] at c897
  have hl : whitneySecond witness 896 < whitneySecond witness 895 := by
    rw [c896, c895, show power 896 = power 895 * 1009 from power_succ 895]
    have h (x : ℕ) :
        x * 1009 * 18157432800 + 94429891158525 <
          x * 94429891158525 + 27572410695360180 := by omega
    exact h _
  have hr : whitneySecond witness 896 < whitneySecond witness 897 := by
    rw [c896, c897, show power 897 = power 896 * 1009 from power_succ 896]
    have h (x : ℕ) (hx : 1018081 ≤ x) :
        x * 18157432800 + 94429891158525 < x * 1009 * 27134550 + 18157432800 := by omega
    exact h _ (power_lower 896 (by decide))
  have hp : 0 < whitneySecond witness 897 := by
    rw [c897]
    exact (by omega : ∀ x : ℕ, 0 < x + 18157432800) _
  have htop : witness.eRank ≠ ⊤ :=
    (Matroid.eRank_ne_top_iff _).mpr inferInstance
  have hb : 897 ≤ witness.eRank.toNat := by
    rw [whitneySecond] at hp
    obtain ⟨X, _, hX⟩ := (Set.ncard_pos (Set.toFinite _)).mp hp
    have hx := witness.eRk_le_eRank X
    rw [hX] at hx
    simpa only [ENat.toNat_natCast] using ENat.toNat_le_toNat hx htop
  rintro ⟨k, _, hinc, hdec⟩
  by_cases hk : 896 ≤ k
  · exact (not_le_of_gt hl) (hinc 895 896 (by decide) hk)
  · exact (not_le_of_gt hr) (hdec 896 897 (by omega) (by decide) hb)

end
end RotaDisproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_rotas_unimodal_conjecture.main) := by
  intro h
  exact RotaDisproof.witness_bad (h _ RotaDisproof.witness)
