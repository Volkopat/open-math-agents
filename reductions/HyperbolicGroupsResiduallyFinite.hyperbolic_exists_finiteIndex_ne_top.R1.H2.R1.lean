import OMAReductions.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R1
import Mathlib

/-! Kapovich–Wise, Theorem 3.3: normal generation in the swapped double. -/
namespace OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R1_H2_R1
open scoped Monoid.Coprod

open Equiv Equiv.Perm

theorem alternating_embedding (F : Type) [Group F] [Fintype F] :
    ∃ (K : Type) (_ : Group K) (_ : Finite K) (_ : IsSimpleGroup K),
      ∃ f : F →* K, Function.Injective f := by
  classical
  let P := F ⊕ F
  let X := P ⊕ Fin 5
  let act := MulAction.toPermHom F F
  let dup := (sumCongrHom F F).comp (act.prod act)
  let perm := (sumCongrHom P (Fin 5)).comp (dup.prod (1 : F →* Equiv.Perm (Fin 5)))
  have even (x : F) : perm x∈alternatingGroup X := by
    rw [mem_alternatingGroup]
    change sign ((Equiv.Perm.sumCongr ((act x).sumCongr (act x)) (1 : Perm (Fin 5))))=1
    rw [sign_sumCongr,sign_sumCongr,map_one,mul_one,Int.units_mul_self]
  let emb := perm.codRestrict (alternatingGroup X) even
  have inj : Function.Injective emb := by
    intro a b eq
    have e : perm a=perm b := congrArg Subtype.val eq
    have e' := sumCongrHom_injective e
    have d : dup a=dup b := congrArg Prod.fst e'
    have d' := sumCongrHom_injective d
    exact MulAction.toPerm_injective (congrArg Prod.fst d')
  have five : 5≤Nat.card X := by simp [X,P]
  exact ⟨alternatingGroup X, inferInstance, inferInstance,alternatingGroup.isSimpleGroup five,emb,inj⟩

theorem finite_detected {A F : Type} [Group A] [Group F] [Finite F] (u : A →* F) (a : A)
    (detected : u a≠1) :
    ∃ (K : Type) (_ : Group K) (_ : Group.IsHyperbolic K) (_ : Nontrivial K),
      Subgroup.normalClosure {x : K | ∃ f : A →* K, f a=x}=⊤ := by
  classical
  let _ := Fintype.ofFinite F
  obtain ⟨K,_,_,_,emb,inj⟩ := alternating_embedding F
  let f := emb.comp u
  have ne : f a≠1 := by
    intro e
    exact detected (inj (e.trans (map_one emb).symm))
  let H := Subgroup.normalClosure {x : K | ∃ g : A →* K, g a=x}
  have mem : f a∈H := Subgroup.subset_normalClosure ⟨f,rfl⟩
  have nontriv : H≠⊥ := by
    intro eq; rw [eq] at mem; exact ne mem
  exact ⟨K,inferInstance,inferInstance,inferInstance,
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal H inferInstance).resolve_left nontriv⟩


/-- The free subgroup preparation in Kapovich–Wise, Theorem 3.3 and Lemma 3.1.
Its first basis half consists of conjugates of generators of the vertex group.
Its second half is killed whenever every image of the specified element is killed. -/
def H1 : Prop := ∀ (A : Type) [Group A] [Group.IsHyperbolic A] (a : A), a≠1 →
  (∀ (F : Type) [Group F] [Finite F] (f : A →* F), f a=1) →
  ∃ (C : Type) (_ : Group C) (_ : Group.IsHyperbolic C) (_ : Nontrivial C)
    (n : ℕ) (P : Group.Generators C (Fin n)) (h : FreeGroup (Fin n ⊕ Fin n) →* C),
    Function.Injective h ∧
    (∀ g x : C, g∉h.range → x∈h.range → g*x*g⁻¹∈h.range → x=1) ∧
    (∃ B : ℕ, ∀ v, v.toWord.length ≤ B*(P.wordLength (h v)+1)) ∧
    (∀ i, IsConj (h (FreeGroup.of (Sum.inl i))) (P.val i)) ∧
    ∀ i, h (FreeGroup.of (Sum.inr i)) ∈
      Subgroup.normalClosure {y : C | ∃ f : A →* C, f a=y}

/-- The combination theorem for a double along a malnormal undistorted free subgroup.
The gluing interchanges the two halves of its given free basis. -/
def H2 : Prop := ∀ (C : Type) [Group C] [Group.IsHyperbolic C] [Nontrivial C]
    (n : ℕ) (P : Group.Generators C (Fin n)) (h : FreeGroup (Fin n ⊕ Fin n) →* C),
    Function.Injective h →
    (∀ g x : C, g∉h.range → x∈h.range → g*x*g⁻¹∈h.range → x=1) →
    (∃ B : ℕ, ∀ v, v.toWord.length ≤ B*(P.wordLength (h v)+1)) →
    let φ : Bool → FreeGroup (Fin n ⊕ Fin n) →* C :=
      fun side => if side then h.comp (FreeGroup.map Sum.swap) else h
    Group.IsHyperbolic (Monoid.PushoutI (G := fun _ : Bool => C) φ)

theorem main : H1 → H2 → OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R1.H2 := by
  classical
  intro prep combine A _ _ a ha
  by_cases seen : ∃ (F : Type) (_ : Group F) (_ : Finite F) (f : A →* F), f a ≠ 1
  · obtain ⟨F,_,_,f,hf⟩ := seen
    exact finite_detected f a hf
  obtain ⟨C,_,_,_,n,P,h,inj,mal,qi,gens,words⟩ := prep A a ha (by
    intro F _ _ f; by_contra hn; exact seen ⟨F,inferInstance,inferInstance,f,hn⟩)
  let b (i : Fin n ⊕ Fin n) := h (FreeGroup.of i)
  let φ : Bool → FreeGroup (Fin n ⊕ Fin n) →* C :=
    fun side => if side then h.comp (FreeGroup.map Sum.swap) else h
  let K := Monoid.PushoutI (G := fun _ : Bool => C) φ
  have hyp : Group.IsHyperbolic K := combine C n P h inj mal qi
  let side (i : Bool) : C →* K := Monoid.PushoutI.of (φ := φ) i
  let l := side false
  let r := side true
  have swap_inj : Function.Injective (FreeGroup.map (@Sum.swap (Fin n) (Fin n))) := by
    apply Function.LeftInverse.injective (g := FreeGroup.map Sum.swap)
    intro v
    rw [FreeGroup.map.comp]
    simpa [Function.comp_def] using FreeGroup.map.id v
  have side_inj (i : Bool) : Function.Injective (φ i) := by
    cases i
    · exact inj
    · exact inj.comp swap_inj
  have nt : Nontrivial K := (Monoid.PushoutI.of_injective (G := fun _ : Bool => C) side_inj false).nontrivial
  have glue (i : Fin n ⊕ Fin n) : l (b i)=r (b i.swap) := by
    have e := (Monoid.PushoutI.of_apply_eq_base (G := fun _ : Bool => C) φ false (FreeGroup.of i)).trans
      (Monoid.PushoutI.of_apply_eq_base (G := fun _ : Bool => C) φ true (FreeGroup.of i)).symm
    exact e
  let H := Subgroup.normalClosure {x : K | ∃ f : A →* K, f a=x}
  have kill (f : C →* K) (i : Fin n) : f (b (Sum.inr i))∈H := by
    have le : Subgroup.normalClosure {y : C | ∃ g : A →* C, g a=y} ≤ H.comap f := by
      apply Subgroup.normalClosure_le_normal
      rintro y ⟨g,rfl⟩
      exact Subgroup.subset_normalClosure ⟨f.comp g,rfl⟩
    exact le (words i)
  have factor (f : C →* K) (triv : ∀ i, f (b (Sum.inl i))∈H) : f.range ≤ H := by
    have incl : Subgroup.closure (Set.range P.val) ≤ H.comap f := by
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨i,rfl⟩
      obtain ⟨c,e⟩ := isConj_iff.mp (gens i)
      change f (P.val i)∈H
      rw [←e,map_mul,map_mul,map_inv]
      exact (inferInstance : H.Normal).conj_mem _ (triv i) _
    rw [P.closure_eq_top] at incl
    rintro _ ⟨x,rfl⟩
    exact incl (Subgroup.mem_top x)
  have hl := factor l (fun i => glue (Sum.inl i) ▸ kill r i)
  have hr := factor r (fun i => (glue (Sum.inr i)).symm ▸ kill l i)
  have covered (i : Bool) (x : C) : side i x ∈ H := by
    cases i
    · exact hl ⟨x,rfl⟩
    · exact hr ⟨x,rfl⟩
  refine ⟨K,inferInstance,hyp,nt,top_unique ?_⟩
  intro x _
  exact Monoid.PushoutI.induction_on x covered (fun v => by
    rw [←Monoid.PushoutI.of_apply_eq_base φ false v]
    exact covered false _) (fun _ _ => H.mul_mem)

end OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R1_H2_R1
