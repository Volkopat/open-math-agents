import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1

-- Credit: @mattdorman
/-! # The two-dimensional normal-space level for complex tensor rank

Write r=(a−1)(b−1)−1. A pinned bilinear normal on (a−1) × a becomes a
separated family of normal lines on a × a after extending the first axis.
The disjoint-column construction then makes (2a−1) marked normal planes
independent on the exceptional rectangle b=3a−2.

For an odd total a+b with too few ordinary batch slots, start from an
ordinary marking on (a−1) × b. Two batches share one marked sample.
Their old relation space has dimension at most two. Two transverse poles
separate the exclusive contributions as the first factor increases to
dimension a. The resulting weighted normal equations have trivial kernel.

Together with the cyclic square, one-column and signed-chord markings,
the rectangular tail and the finite three-slice tangent, these arguments
prove the entire two-normal child of the registered last-slice statement.

Friedland, Conjecture 5.1, https://arxiv.org/abs/0805.3777 .
The statement comes from project PR 12200. The marked batch constructions
occur in PRs 17105 and 22377. All arguments below use the registered
parent as their sole project import.
-/

namespace CriticalLastSlice.TwoPlanes

/-- A basis of the common kernel of two independent forms detects precisely
their linear span inside the dual. -/
theorem common_kernel_basis {a : ℕ} (L M : (Fin a → ℂ) →ₗ[ℂ] ℂ)
    (ind : LinearIndependent ℂ ![L,M]) :
    ∃ B : Fin (a-2) → Fin a → ℂ,
      (∀ i, L (B i) = 0 ∧ M (B i) = 0) ∧
      Submodule.span ℂ (Set.range B) = L.ker ⊓ M.ker ∧
      (∀ H : (Fin a → ℂ) →ₗ[ℂ] ℂ, (∀ i, H (B i) = 0) ↔ ∃ u v : ℂ, H = u • L + v • M) := by
  classical
  let W := Submodule.span ℂ (Set.range ![L,M])
  have dimW : Module.finrank ℂ W = 2 := by simpa [W] using finrank_span_eq_card ind
  have dimK : Module.finrank ℂ W.dualCoannihilator = a-2 := by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq W
    rw [dimW, Module.finrank_fin_fun] at h
    omega
  let b := Module.finBasisOfFinrankEq ℂ W.dualCoannihilator dimK
  let B (i : Fin (a-2)) : Fin a → ℂ := b i
  have eqK : W.dualCoannihilator = L.ker ⊓ M.ker := by
    ext x
    change x ∈ ((Submodule.span ℂ (Set.range ![L,M])).dualCoannihilator : Set (Fin a → ℂ)) ↔ _
    rw [Submodule.coe_dualCoannihilator_span]
    simp [LinearMap.mem_ker,and_comm]
  have inside (i : Fin (a-2)) : B i ∈ W.dualCoannihilator := (b i).property
  have span : Submodule.span ℂ (Set.range B) = W.dualCoannihilator :=
    (Submodule.span_range_subtype_eq_top_iff W.dualCoannihilator inside).mp b.span_eq
  refine ⟨B,?_,span.trans eqK,?_⟩
  · intro i
    change B i ∈ L.ker ⊓ M.ker
    rw [←eqK]
    exact inside i
  intro H
  have annihilator : (∀ i, H (B i) = 0) ↔ H ∈ W.dualCoannihilator.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro h x hx
      have eq : H.comp W.dualCoannihilator.subtype = 0 := b.ext fun i => h i
      exact DFunLike.congr_fun eq ⟨x,hx⟩
    · exact fun h i => h (B i) (inside i)
  rw [annihilator, Subspace.dualCoannihilator_dualAnnihilator_eq]
  change H ∈ Submodule.span ℂ (Set.range ![L,M]) ↔ _
  rw [Matrix.range_cons_cons_empty,Submodule.mem_span_pair]
  exact exists_congr fun u => exists_congr fun v => eq_comm

/-- Prescribe the first value and kill the other two independent forms. -/
theorem dual_separate_three {a : ℕ} (L₀ L₁ Lⱼ : (Fin a → ℂ) →ₗ[ℂ] ℂ)
    (ind : LinearIndependent ℂ ![L₀,L₁,Lⱼ]) :
    ∃ x : Fin a → ℂ, L₀ x = 1 ∧ L₁ x = 0 ∧ Lⱼ x = 0 := by
  have h : LinearIndependent ℂ ![L₁,Lⱼ] ∧
      L₀ ∉ Submodule.span ℂ (Set.range ![L₁,Lⱼ]) := linearIndependent_finCons.mp ind
  obtain ⟨B,zero,_,detect⟩ := common_kernel_basis L₁ Lⱼ h.1
  obtain ⟨i,hi⟩ : ∃ i, L₀ (B i) ≠ 0 := by
    by_contra! hall
    obtain ⟨u,v,eq⟩ := (detect L₀).mp hall
    exact h.2 (by rw [Matrix.range_cons_cons_empty,Submodule.mem_span_pair]; exact ⟨u,v,eq.symm⟩)
  refine ⟨(L₀ (B i))⁻¹ • B i,?_,?_,?_⟩
  · simp [hi]
  · simp [(zero i).1]
  · simp [(zero i).2]

end CriticalLastSlice.TwoPlanes

namespace TwoNormalAvoiding

open Module

private lemma avoid_inside {E I : Type*} [AddCommGroup E] [Module ℂ E] [Finite I]
    (H : Submodule ℂ E) (bad : I → Submodule ℂ E) (proper : ∀ i, ¬H≤bad i) :
    ∃ f ∈ H, ∀ i, f ∉ bad i := by
  classical
  let cut (i : I) := (bad i).comap H.subtype
  have h (i : I) : cut i ≠ ⊤ := by
    intro eq
    apply proper i
    intro v hv
    have mem : (⟨v,hv⟩ : H) ∈ cut i := by rw [eq]; trivial
    exact mem
  obtain ⟨f,hf⟩ := Submodule.exists_forall_notMem_of_forall_ne_top cut h
  exact ⟨f,f.property,fun i => hf i⟩

private lemma span_bound {I E : Type*} [AddCommGroup E] [Module ℂ E] (v : I → E) (T : Finset I) :
    finrank ℂ (Submodule.span ℂ (v '' (T : Set I))) ≤ T.card := by
  classical
  have range_eq : Set.range (fun j : T => v j.val) = v '' (T : Set I) := by
    ext x
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨j.val,j.property,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      exact ⟨⟨j,hj⟩,rfl⟩
  have bound := finrank_range_le_card (R:=ℂ) (fun j : T => v j.val)
  rw [←range_eq]
  exact bound.trans_eq (Fintype.card_coe T)

private lemma annihilates_line {a : ℕ} (x : Fin a → ℂ) (f : Dual ℂ (Fin a → ℂ)) :
    f ∈ (Submodule.span ℂ {x}).dualAnnihilator ↔ f x=0 := by
  constructor
  · exact fun h => (Submodule.mem_dualAnnihilator f).mp h x (Submodule.subset_span (Set.mem_singleton x))
  · intro h
    have inc : Submodule.span ℂ {x}≤f.ker := by
      apply Submodule.span_le.mpr
      rintro w hw
      rw [Set.mem_singleton_iff.mp hw]
      exact h
    exact (Submodule.mem_dualAnnihilator f).mpr (fun _ hw => inc hw)

private lemma next_form {a m n : ℕ} (ha : 3≤a) (x : Fin m → Fin a → ℂ)
    (nz : ∀ t, x t≠0)
    (distinct : ∀ s t : Fin m, s≠t → x s ∉ Submodule.span ℂ {x t})
    (S : Finset (Fin n)) (i : Fin n) (fresh : i ∉ S) (L : Fin n → Dual ℂ (Fin a → ℂ))
    (incidence : ∀ j∈S, ∀ t : Fin m, L j (x t)=0 ↔ j.val=t.val) :
    ∃ f : Dual ℂ (Fin a → ℂ), (∀ t : Fin m, f (x t)=0 ↔ i.val=t.val) ∧
      ∀ T : Finset (Fin n), T⊆S → T.card≤2 → f ∉ Submodule.span ℂ (L '' (T : Set (Fin n))) := by
  classical
  let E := Dual ℂ (Fin a → ℂ)
  let off := {t : Fin m // i.val≠t.val}
  let small := {T : Finset (Fin n) // T⊆S ∧ T.card≤2}
  let ev (t : Fin m) : E →ₗ[ℂ] ℂ := Dual.eval ℂ _ (x t)
  let P (T : Finset (Fin n)) := Submodule.span ℂ (L '' (T : Set (Fin n)))
  let bad : off ⊕ small → Submodule ℂ E :=
    Sum.elim (fun t : off => (ev t.val).ker) (fun T : small => P T.val)
  have assemble (H : Submodule ℂ E) (hH : ∀ f∈H, ∀ t : Fin m, i.val=t.val → f (x t)=0)
      (proper1 : ∀ t : off, ¬ H≤(ev t.val).ker) (proper2 : ∀ T : small, ¬ H≤P T.val) :
      ∃ f : E, (∀ t : Fin m, f (x t)=0 ↔ i.val=t.val) ∧
        ∀ T : Finset (Fin n), T⊆S → T.card≤2 → f ∉ P T := by
    have proper (z : off ⊕ small) : ¬H≤bad z := by
      cases z with
      | inl t => exact proper1 t
      | inr T => exact proper2 T
    obtain ⟨f,inside,avoids⟩ := avoid_inside H bad proper
    refine ⟨f,fun t => ⟨?_,hH f inside t⟩,fun T hT card => avoids (.inr ⟨T,hT,card⟩)⟩
    intro zero
    by_contra ne
    exact avoids (.inl ⟨t,ne⟩) zero
  by_cases marked : i.val < m
  · let t : Fin m := ⟨i.val,marked⟩
    let W := Submodule.span ℂ {x t}
    let H := W.dualAnnihilator
    have hdim : 2≤finrank ℂ H := by
      have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
      change finrank ℂ (Submodule.span ℂ {x t})+finrank ℂ H=finrank ℂ (Fin a → ℂ) at h
      rw [finrank_span_singleton (nz t),Module.finrank_fin_fun] at h
      omega
    apply assemble H
    · intro f hf s eq
      have same : t=s := Fin.ext eq
      exact same ▸ (annihilates_line (x t) f).mp hf
    · intro s le
      have ne : s.val≠t := fun eq => s.property (congrArg Fin.val eq).symm
      obtain ⟨f,nonzero,hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
        (distinct s.val t ne) inferInstance
      have ht : f (x t)=0 := by
        have mem : f (x t) ∈ W.map f := ⟨x t,Submodule.subset_span (Set.mem_singleton _),rfl⟩
        change W.map f=⊥ at hmap
        rw [hmap] at mem
        exact (Submodule.mem_bot ℂ).mp mem
      exact nonzero (le ((annihilates_line (x t) f).mpr ht))
    · intro T le
      have bound := span_bound L T.val
      change finrank ℂ (P T.val)≤T.val.card at bound
      have eq : H=P T.val := Submodule.eq_of_le_of_finrank_le le (by have := T.property.2; omega)
      rcases T.val.eq_empty_or_nonempty with empty|⟨j,hj⟩
      · have upper : finrank ℂ H ≤ 0 := by
          rw [eq]
          exact bound.trans (by rw [empty]; exact le_rfl)
        omega
      · have mem : L j ∈ P T.val := Submodule.subset_span ⟨j,hj,rfl⟩
        have inside : L j ∈ H := by rwa [eq]
        have hz := (annihilates_line (x t) (L j)).mp inside
        have value := (incidence j (T.property.1 hj) t).mp hz
        have same : j=i := Fin.ext value
        exact fresh (same ▸ T.property.1 hj)
  · apply assemble ⊤
    · intro f _ t eq
      omega
    · intro t le
      obtain ⟨j,hj⟩ : ∃ j, x t.val j≠0 := by by_contra! no; exact nz t.val (funext no)
      exact hj (le (show LinearMap.proj (R:=ℂ) j ∈ (⊤ : Submodule ℂ E) from Submodule.mem_top) :
        LinearMap.proj (R:=ℂ) j (x t.val)=0)
    · intro T le
      have bound := span_bound L T.val
      change finrank ℂ (P T.val)≤T.val.card at bound
      rw [top_unique le] at bound
      rw [finrank_top,Subspace.dual_finrank_eq,Module.finrank_fin_fun] at bound
      have := T.property.2
      omega

/-- Choose hyperplanes with precisely the designated incidences and with
every subfamily of at most three defining forms linearly independent. -/
theorem choose_forms {a m d : ℕ} (ha : 3≤a) (_hm : m≤d+1) (x : Fin m → Fin a → ℂ)
    (nonzero : ∀ t, x t≠0)
    (distinct : ∀ s t : Fin m, s≠t → x s ∉ Submodule.span ℂ {x t}) :
    ∃ L : Fin (d+1) → Dual ℂ (Fin a → ℂ),
      (∀ i t, L i (x t)=0 ↔ i.val=t.val) ∧
      ∀ S : Finset (Fin (d+1)), S.card≤3 → LinearIndependent ℂ (fun i : S => L i.val) := by
  classical
  let I := Fin (d+1)
  let E := Dual ℂ (Fin a → ℂ)
  have select (P : Finset I) :
      ∃ L : I → E, (∀ i∈P, ∀ t : Fin m, L i (x t)=0 ↔ i.val=t.val) ∧
        ∀ S : Finset I, S⊆P → S.card≤3 → LinearIndepOn ℂ L (S : Set I) := by
    induction P using Finset.induction_on with
    | empty =>
      refine ⟨0,by simp,?_⟩
      intro S h _
      have eq : S=∅ := Finset.subset_empty.mp h
      simp [eq]
    | @insert i P new ih =>
      obtain ⟨L,old,ind⟩ := ih
      obtain ⟨f,matching,out⟩ := next_form ha x nonzero distinct P i new L old
      let M := Function.update L i f
      have same {j : I} (hj : j∈P) : L j=M j := by
        have ne : j≠i := fun h => new (h ▸ hj)
        exact (Function.update_of_ne ne f L).symm
      refine ⟨M,?_,?_⟩
      · intro j hj t
        rcases Finset.mem_insert.mp hj with rfl|h
        · simpa [M] using matching t
        · rw [←same h]
          exact old j h t
      · intro S subset card
        by_cases added : i ∈ S
        · let T := S.erase i
          have sub : T⊆P := by
            intro j hj
            obtain ⟨ne,h⟩ := Finset.mem_erase.mp hj
            exact (Finset.mem_insert.mp (subset h)).resolve_left ne
          have size : T.card≤2 := by dsimp [T]; rw [Finset.card_erase_of_mem added]; omega
          have equal : Set.EqOn L M (T : Set I) := fun _ h => same (sub h)
          have hT := (ind T sub (by omega)).congr equal
          have beyond : M i ∉ Submodule.span ℂ (M '' (T : Set I)) := by
            rw [←equal.image_eq,show M i=f from Function.update_self i f L]
            exact out T sub size
          have rest : i ∉ (T : Set I) := Finset.notMem_erase i S
          have glued := (linearIndepOn_insert (f:=M) rest).mpr ⟨hT,beyond⟩
          have full : insert i (T : Set I) = (S : Set I) := by
            change insert i ((S.erase i : Finset I) : Set I) = _
            rw [←Finset.coe_insert,Finset.insert_erase added]
          rwa [full] at glued
        · have sub : S⊆P := by
            intro j hj
            rcases Finset.mem_insert.mp (subset hj) with eq|old
            · exact False.elim (added (eq ▸ hj))
            · exact old
          exact (ind S sub card).congr (fun _ h => same (sub h))
  obtain ⟨L,hL,hI⟩ := select Finset.univ
  exact ⟨L,fun i => hL i (Finset.mem_univ _),fun S h => hI S (Finset.subset_univ _) h⟩

/-- In particular, any injectively indexed pair or triple of these
chosen forms is linearly independent in its specified order. -/
theorem independent_of_injective_tuple {I J E : Type*} [Fintype I] [Fintype J]
    [AddCommGroup E] [Module ℂ E] (L : I → E)
    (good : ∀ S : Finset I, S.card≤3 → LinearIndependent ℂ (fun i : S => L i.val))
    (e : J ↪ I) (card : Fintype.card J≤3) : LinearIndependent ℂ (fun j => L (e j)) := by
  classical
  let T := Finset.univ.map e
  have hit (j : J) : e j ∈ T := Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩
  let f (j : J) : T := ⟨e j,hit j⟩
  have inj : Function.Injective f := fun _ _ eq => e.injective (congrArg Subtype.val eq)
  exact (good T (by simpa [T] using card)).comp f inj

end TwoNormalAvoiding

namespace LastSliceTwo

/-- Both types of marked points have one-dimensional normal spaces for this explicit
choice of factors. The scalar in the last column determines every entry. -/
lemma explicit_factor_formulas (A B : ℕ) :
    let lam : Fin 2 ⊕ Fin A → ℂ := Sum.elim (fun v => if v=0 then 1 else 0) (fun _ => 2)
    let x (p : Fin B × (Fin 2 ⊕ Fin A)) : (Fin 3 ⊕ Fin A) → ℂ :=
      match p.2 with
      | .inl v => Sum.elim (if v=0 then ![1,(p.1.val:ℂ),(p.1.val:ℂ)^2] else ![0,1,2*(p.1.val:ℂ)]) 0
      | .inr l => Sum.elim ![0,0,-(p.1.val:ℂ)^(l.val+3)] (fun u => if u=l then 1 else 0)
    let y (p : Fin B × (Fin 2 ⊕ Fin A)) : Option (Fin B) → ℂ := fun
      | none => lam p.2
      | some j => if j=p.1 then 1 else 0
    ∀ (i : Fin B) (v : Fin 2) (H : (Fin 3 ⊕ Fin A) × Option (Fin B) → ℂ),
      (∀ t, ∑ ij, (x t ij.1*y t ij.2)*H ij=0) →
      (∀ u, ∑ k, y (i,.inl v) k*H (u,k)=0) →
      (∀ k, ∑ u, x (i,.inl v) u*H (u,k)=0) →
      let s := H (.inl 2,none)
      (∀ u : Fin 3 ⊕ Fin A, H (u,none) = s * u.elim ![(i.val:ℂ)^2,-2*(i.val:ℂ),1]
        (fun l => (i.val:ℂ)^(l.val+3))) ∧
      (∀ j, H (.inl 2,some j) = if v=0 then (if i=j then -s else s) else 0) ∧ (s=0 → H=0) := by
  intro lam x y
  have second_action (p : Fin B × (Fin 2 ⊕ Fin A)) (w : Option (Fin B) → ℂ) :
      (∑ k, y p k*w k) = lam p.2*w none + w (some p.1) := by
    rw [Fintype.sum_option]
    simp [y,ite_mul,Finset.sum_ite_eq']
  have product_action (p : Fin B × (Fin 2 ⊕ Fin A)) (H : (Fin 3 ⊕ Fin A) × Option (Fin B) → ℂ) :
      (∑ ij, (x p ij.1*y p ij.2)*H ij) = ∑ u, x p u*(lam p.2*H (u,none)+H (u,some p.1)) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u _
    rw [← second_action p (fun k => H (u,k)),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have first_action (j : Fin B) (w : (Fin 3 ⊕ Fin A) → ℂ) : (∑ u, x (j,.inl 0) u*w u) =
      w (.inl 0)+(j.val:ℂ)*w (.inl 1)+(j.val:ℂ)^2*w (.inl 2) := by
    simp [Fintype.sum_sum_type,Fin.sum_univ_three,x,Matrix.cons_val_two]
  have slope_action (j : Fin B) (w : (Fin 3 ⊕ Fin A) → ℂ) : (∑ u, x (j,.inl 1) u*w u) =
      w (.inl 1)+2*(j.val:ℂ)*w (.inl 2) := by
    simp [Fintype.sum_sum_type,Fin.sum_univ_three,x,Matrix.cons_val_two]
  have extra_action (j : Fin B) (l : Fin A) (w : (Fin 3 ⊕ Fin A) → ℂ) : (∑ u, x (j,.inr l) u*w u) =
      w (.inr l)-(j.val:ℂ)^(l.val+3)*w (.inl 2) := by
    simp [Fintype.sum_sum_type,Fin.sum_univ_three,x,Matrix.cons_val_two,ite_mul,Finset.sum_ite_eq']
    ring
  intro i v H prod row col s
  let I : ℂ := i.val
  have selected (u : Fin 3 ⊕ Fin A) : (if v=0 then (1:ℂ) else 0)*H (u,none)+H (u,some i)=0 :=
    (second_action (i,.inl v) (fun k => H (u,k))).symm.trans (row u)
  have Xarm (hv : v=0) (k : Option (Fin B)) : H (.inl 0,k)+I*H (.inl 1,k)+I^2*H (.inl 2,k)=0 := by
    subst v
    exact (first_action i (fun u => H (u,k))).symm.trans (col k)
  have Darm (hv : v≠0) (k : Option (Fin B)) : H (.inl 1,k)+2*I*H (.inl 2,k)=0 := by
    have hv' : v=1 := by fin_cases v <;> simp_all
    subst v
    exact (slope_action i (fun u => H (u,k))).symm.trans (col k)
  have anchor (j : Fin B) : (H (.inl 0,none)+H (.inl 0,some j)) +
      (j.val:ℂ)*(H (.inl 1,none)+H (.inl 1,some j)) +
      (j.val:ℂ)^2*(H (.inl 2,none)+H (.inl 2,some j))=0 := by
    apply (first_action j (fun u => H (u,none)+H (u,some j))).symm.trans
    simpa only [lam,Sum.elim_inl,if_true,one_mul] using (product_action (j,.inl 0) H).symm.trans (prod (j,.inl 0))
  have slope (j : Fin B) : H (.inl 1,some j)+2*(j.val:ℂ)*H (.inl 2,some j)=0 := by
    apply (slope_action j (fun u => H (u,some j))).symm.trans
    simpa [lam] using (product_action (j,.inl 1) H).symm.trans (prod (j,.inl 1))
  have extra (j : Fin B) (l : Fin A) : (2*H (.inr l,none)+H (.inr l,some j)) -
      (j.val:ℂ)^(l.val+3)*(2*H (.inl 2,none)+H (.inl 2,some j))=0 := by
    apply (extra_action j l (fun u => 2*H (u,none)+H (u,some j))).symm.trans
    simpa only [lam,Sum.elim_inr] using (product_action (j,.inr l) H).symm.trans (prod (j,.inr l))
  have lastSlope : H (.inl 1,none)+2*I*s=0 := by
    by_cases hv : v=0
    · have u := selected (.inl 1)
      have w := selected (.inl 2)
      simp only [if_pos hv,one_mul] at u w
      dsimp only [I,s]
      linear_combination u + 2*(i.val:ℂ)*w - slope i
    · exact Darm hv none
  have lastPoint : H (.inl 0,none)+I*H (.inl 1,none)+I^2*s=0 := by
    by_cases hv : v=0
    · exact Xarm hv none
    · have zero (u : Fin 3 ⊕ Fin A) : H (u,some i)=0 := by simpa only [if_neg hv,zero_mul,zero_add] using selected u
      simpa only [zero,add_zero] using anchor i
  have last₁ : H (.inl 1,none) = -2*I*s := by linear_combination lastSlope
  have last₀ : H (.inl 0,none) = I^2*s := by linear_combination lastPoint - I*lastSlope
  have lastExtra (l : Fin A) : H (.inr l,none) = I^(l.val+3)*s := by
    have a := selected (.inr l)
    have b := selected (.inl 2)
    dsimp only [I,s]
    by_cases hv : v=0
    · simp only [if_pos hv,one_mul] at a b
      linear_combination extra i l - a + (i.val:ℂ)^(l.val+3)*b
    · simp only [if_neg hv,zero_mul,zero_add] at a b
      linear_combination (extra i l - a + (i.val:ℂ)^(l.val+3)*b)/2
  have atLast (u : Fin 3 ⊕ Fin A) : H (u,none) = s*u.elim ![(i.val:ℂ)^2,-2*(i.val:ℂ),1]
      (fun l => (i.val:ℂ)^(l.val+3)) := by
    rcases u with k|l
    · fin_cases k
      · change H (.inl (0:Fin 3),none)=s*I^2
        rw [last₀,mul_comm]
      · change H (.inl (1:Fin 3),none)=s*(-2*I)
        rw [last₁,mul_comm]
      · change s=s*1
        rw [mul_one]
    · change H (.inr l,none)=s*I^(l.val+3)
      rw [lastExtra,mul_comm]
  have old₁ (j : Fin B) : H (.inl 1,some j) = -2*(j.val:ℂ)*H (.inl 2,some j) := by
    linear_combination slope j
  have old₀ (j : Fin B) : H (.inl 0,some j) = (j.val:ℂ)^2*H (.inl 2,some j) -
      (H (.inl 0,none)+(j.val:ℂ)*H (.inl 1,none)+(j.val:ℂ)^2*s) := by
    dsimp only [s]
    linear_combination anchor j - (j.val:ℂ)*slope j
  have signs (j : Fin B) : H (.inl 2,some j) = if v=0 then (if i=j then -s else s) else 0 := by
    have diff (h : i≠j) : (j.val:ℂ) ≠ I := by
      intro eq
      apply h
      apply Fin.ext
      dsimp only [I] at eq
      exact_mod_cast eq.symm
    by_cases hv : v=0
    · rw [if_pos hv]
      by_cases h : i=j
      · subst j
        rw [if_pos rfl]
        have u := selected (.inl 2)
        simp only [if_pos hv,one_mul] at u
        dsimp only [s]
        linear_combination u
      · rw [if_neg h]
        have fact : ((j.val:ℂ)-I)^2*(s-H (.inl 2,some j))=0 := by
          have hy := Xarm hv (some j)
          rw [old₀,old₁,last₀,last₁] at hy
          linear_combination -hy
        exact (sub_eq_zero.mp ((mul_eq_zero.mp fact).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr (diff h))))).symm
    · rw [if_neg hv]
      by_cases h : i=j
      · subst j
        simpa only [if_neg hv,zero_mul,zero_add] using selected (.inl 2)
      · have fact : (2*(I-(j.val:ℂ)))*H (.inl 2,some j)=0 := by
          linear_combination Darm hv (some j) - slope j
        exact (mul_eq_zero.mp fact).resolve_left (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm (diff h))))
  refine ⟨atLast,signs,?_⟩
  intro hs
  have lastZ (u : Fin 3 ⊕ Fin A) : H (u,none)=0 := by simpa only [hs,zero_mul] using atLast u
  have oldZ (j : Fin B) (u : Fin 3 ⊕ Fin A) : H (u,some j)=0 := by
    have z₂ : H (.inl 2,some j)=0 := by simpa only [hs,neg_zero,ite_self] using signs j
    rcases u with k|l
    · fin_cases k
      · change H (.inl (0 : Fin 3),some j)=0
        simpa only [z₂,lastZ,hs,mul_zero,add_zero,sub_zero] using old₀ j
      · change H (.inl (1 : Fin 3),some j)=0
        simpa only [z₂,mul_zero] using old₁ j
      · exact z₂
    · simpa only [lastZ,z₂,mul_zero,zero_add,add_zero,sub_zero] using extra j l
  funext ⟨u,k⟩
  cases k with
  | none => exact lastZ u
  | some j => exact oldZ j u

/-- Choose all the first marked points and the first `min (A+3) B` second points.
The normals form a direct sum, and the marked factor vectors on each side represent
distinct projective points. -/
lemma exists_large_batch_separated (A B : ℕ) (hB : 3 ≤ B) :
    ∃ label : (Fin B ⊕ Fin (min (A+3) B)) ↪ (Fin B × (Fin 2 ⊕ Fin A)),
    ∃ x : (Fin B × (Fin 2 ⊕ Fin A)) → (Fin 3 ⊕ Fin A) → ℂ,
    ∃ y : (Fin B × (Fin 2 ⊕ Fin A)) → Option (Fin B) → ℂ,
    (∀ H : (Fin B ⊕ Fin (min (A+3) B)) → (Fin 3 ⊕ Fin A) × Option (Fin B) → ℂ,
      (∀ t s, (∑ ij, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (label t) j*H t (i,j))=0) →
      (∀ t j, (∑ i, x (label t) i*H t (i,j))=0) → (∑ t,H t)=0 → H=0) ∧
    (∀ t, x (label t) ≠ 0) ∧ (∀ t, y (label t) ≠ 0) ∧
    (∀ i j, i ≠ j → ∀ c : ℂ, x (label i) ≠ c • x (label j)) ∧
    (∀ i j, i ≠ j → ∀ c : ℂ, y (label i) ≠ c • y (label j)) := by
  classical
  let k := min (A+3) B
  let inc (t : Fin k) := t.castLE (Nat.min_le_right (A+3) B)
  let label : (Fin B ⊕ Fin k) ↪ (Fin B × (Fin 2 ⊕ Fin A)) := {
    toFun := Sum.elim (fun i => (i,.inl 0)) (fun t => (inc t,.inl 1))
    inj' := by
      rintro (i|i) (j|j) he
      · exact congrArg Sum.inl (congrArg Prod.fst he)
      · have ht : (0 : Fin 2)=1 := Sum.inl.inj (congrArg Prod.snd he)
        exact (zero_ne_one ht).elim
      · have ht : (1 : Fin 2)=0 := Sum.inl.inj (congrArg Prod.snd he)
        exact (one_ne_zero ht).elim
      · have hv : inc i=inc j := congrArg Prod.fst he
        exact congrArg Sum.inr (Fin.ext (congrArg (fun v : Fin B => v.val) hv)) }
  let lam : Fin 2 ⊕ Fin A → ℂ := Sum.elim (fun v => if v=0 then 1 else 0) (fun _ => 2)
  let x (p : Fin B × (Fin 2 ⊕ Fin A)) : (Fin 3 ⊕ Fin A) → ℂ :=
    match p.2 with
    | .inl v => Sum.elim (if v=0 then ![1,(p.1.val:ℂ),(p.1.val:ℂ)^2] else ![0,1,2*(p.1.val:ℂ)]) 0
    | .inr l => Sum.elim ![0,0,-(p.1.val:ℂ)^(l.val+3)] (fun u => if u=l then 1 else 0)
  let y (p : Fin B × (Fin 2 ⊕ Fin A)) : Option (Fin B) → ℂ := fun
    | none => lam p.2
    | some j => if j=p.1 then 1 else 0
  have formula := explicit_factor_formulas A B
  refine ⟨label,x,y,?_,?_,?_,?_,?_⟩
  · intro H outer rows cols total
    let s (i : Fin B) := H (.inl i) (.inl 2,none)
    let q (i : Fin k) := H (.inr i) (.inl 2,none)
    let v (i : Fin B) (u : Fin 3 ⊕ Fin A) := u.elim ![(i.val : ℂ)^2,-2*(i.val : ℂ),1] (fun l => (i.val : ℂ)^(l.val+3))
    have first (i : Fin B) := formula i 0 (H (.inl i)) (outer (.inl i)) (rows (.inl i)) (cols (.inl i))
    have extra (i : Fin k) := formula (inc i) 1 (H (.inr i)) (outer (.inr i)) (rows (.inr i)) (cols (.inr i))
    have f₁ (i : Fin B) (u : Fin 3 ⊕ Fin A) : H (.inl i) (u,none) = s i*v i u := (first i).1 u
    have f₂ (i j : Fin B) : H (.inl i) (.inl 2,some j) = if i=j then -s i else s i := (first i).2.1 j
    have e₁ (i : Fin k) (u : Fin 3 ⊕ Fin A) : H (.inr i) (u,none) = q i * v (inc i) u := (extra i).1 u
    have e₂ (i : Fin k) (j : Fin B) : H (.inr i) (.inl 2,some j) = 0 := (extra i).2.1 j
    have signed (j : Fin B) : (∑ i, if i=j then -s i else s i)=0 := by
      have he := congrFun total (.inl 2,some j)
      simpa only [Fintype.sum_sum_type,Pi.add_apply,Finset.sum_apply,f₂,e₂,Finset.sum_const_zero,add_zero,Pi.zero_apply] using he
    have last (u : Fin 3 ⊕ Fin A) : (∑ i, s i*v i u) + (∑ j, q j*v (inc j) u)=0 := by
      have he := congrFun total (u,none)
      simpa only [Fintype.sum_sum_type,Pi.add_apply,Finset.sum_apply,f₁,e₁,Pi.zero_apply] using he
    obtain ⟨hs,hq⟩ := tagged_coefficients (A:=A) (by omega : B≠2) s q signed last
    funext t
    cases t with
    | inl i => exact (first i).2.2 (congrFun hs i)
    | inr i => exact (extra i).2.2 (congrFun hq i)

  · rintro (i|i) he
    · exact one_ne_zero (congrFun he (.inl (0 : Fin 3)))
    · exact one_ne_zero (congrFun he (.inl (1 : Fin 3)))
  · rintro (i|i) he
    · have h := congrFun he (some i)
      change (if i=i then (1 : ℂ) else 0) = 0 at h
      simp at h
    · have h := congrFun he (some (inc i))
      change (if inc i=inc i then (1 : ℂ) else 0) = 0 at h
      simp at h
  · rintro (i|i) (j|j) hne c he
    · have h₀ := congrFun he (.inl (0 : Fin 3))
      have h₁ := congrFun he (.inl (1 : Fin 3))
      change (1 : ℂ) = c*1 at h₀
      change (i.val : ℂ) = c*(j.val : ℂ) at h₁
      rw [mul_one] at h₀
      rw [← h₀,one_mul] at h₁
      exact hne (congrArg Sum.inl (Fin.ext (by exact_mod_cast h₁)))
    · have h := congrFun he (.inl (0 : Fin 3))
      change (1 : ℂ) = c*0 at h
      exact one_ne_zero (h.trans (mul_zero c))
    · have h₀ := congrFun he (.inl (0 : Fin 3))
      have h₁ := congrFun he (.inl (1 : Fin 3))
      change (0 : ℂ) = c*1 at h₀
      change (1 : ℂ) = c*(j.val : ℂ) at h₁
      rw [mul_one] at h₀
      rw [← h₀,zero_mul] at h₁
      exact one_ne_zero h₁
    · have h₁ := congrFun he (.inl (1 : Fin 3))
      have h₂ := congrFun he (.inl (2 : Fin 3))
      change (1 : ℂ) = c*1 at h₁
      change 2*(i.val : ℂ) = c*(2*(j.val : ℂ)) at h₂
      rw [mul_one] at h₁
      rw [← h₁,one_mul] at h₂
      have h : (i.val : ℂ) = (j.val : ℂ) := by linear_combination h₂/2
      exact hne (congrArg Sum.inr (Fin.ext (by exact_mod_cast h)))
  · let col : Fin B ⊕ Fin k → Fin B := Sum.elim id inc
    have old (t : Fin B ⊕ Fin k) (j : Fin B) :
        y (label t) (some j) = if j=col t then 1 else 0 := by cases t <;> rfl
    intro t s hne c he
    have eq := congrFun he (some (col t))
    change y (label t) (some (col t)) = c * y (label s) (some (col t)) at eq
    rw [old,old,if_pos rfl] at eq
    by_cases hc : col t = col s
    · rw [if_pos hc,mul_one] at eq
      have last := congrFun he none
      rcases t with i|i <;> rcases s with j|j
      · exact hne (congrArg Sum.inl hc)
      · change (1 : ℂ) = c*0 at last
        exact one_ne_zero (last.trans (mul_zero c))
      · change (0 : ℂ) = c*1 at last
        rw [← eq,mul_one] at last
        exact zero_ne_one last
      · exact hne (congrArg Sum.inr (Fin.ext (congrArg (fun u : Fin B => u.val) hc)))
    · rw [if_neg hc,mul_zero] at eq
      exact one_ne_zero eq

end LastSliceTwo

namespace LastSliceTwo

/-- Restrict a direct family along an embedding by extending the smaller
tuple by zero on the complement. -/
private lemma restrict_fixed_rows {A B P Q T : Type*} [Fintype A] [Fintype B] [Fintype Q] [Fintype T]
    (x : P → A → ℂ) (y : P → B → ℂ) (e : Q ↪ P) (f : T ↪ Q)
    (direct : ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0) : ∀ H : T → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e (f t)) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e (f t)) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0 := by
  classical
  let C := (Set.range f)ᶜ
  let q : T ⊕ C ≃ Q := (Equiv.sumCongr f.toEquivRange (Equiv.refl C)).trans (Equiv.Set.sumCompl _)
  have ql (t : T) : q (.inl t)=f t := rfl
  intro H outer row col total
  let F (s : Q) : A × B → ℂ := (q.symm s).elim H (fun _ => 0)
  have fl (t : T) : F (q (.inl t))=H t := by simp only [F,Equiv.symm_apply_apply,Sum.elim_inl]
  have fr (t : C) : F (q (.inr t))=0 := by simp only [F,Equiv.symm_apply_apply,Sum.elim_inr]
  have outer' (t : Q) (s : P) : ∑ ij : A×B, (x s ij.1*y s ij.2)*F t ij=0 := by
    obtain ⟨t|t,rfl⟩ := q.surjective t
    · rw [fl]
      exact outer t s
    · simp [fr]
  have row' (t : Q) (i : A) : (∑ j, y (e t) j*F t (i,j))=0 := by
    obtain ⟨t|t,rfl⟩ := q.surjective t
    · rw [fl,ql]
      exact row t i
    · simp [fr]
  have col' (t : Q) (j : B) : (∑ i, x (e t) i*F t (i,j))=0 := by
    obtain ⟨t|t,rfl⟩ := q.surjective t
    · rw [fl,ql]
      exact col t j
    · simp [fr]
  have all_sum : ∑ t,F t=0 := by
    rw [←q.sum_comp F,Fintype.sum_sum_type]
    simpa only [fl,fr,Finset.sum_const_zero,add_zero] using total
  have zero := direct F outer' row' col' all_sum
  funext t ij
  exact congrFun ((fl t).symm.trans (congrFun zero (q (.inl t)))) ij

/-- Transport a marked collection of independent normal spaces through
bijections on the total points and both matrix axes. -/
private lemma move_fixed_rows {A B P Q A' B' P' : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B'] [Fintype Q]
    (ea : A ≃ A') (eb : B ≃ B') (ep : P ≃ P') (first : Q ↪ P)
    (x : P → A → ℂ) (y : P → B → ℂ) (ind : ∀ H : Q → A × B → ℂ,
      (∀ t s, ∑ ij : A × B, (x s ij.1*y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, y (first t) j*H t (i,j)=0) →
      (∀ t j, ∑ i, x (first t) i*H t (i,j)=0) → (∑ t, H t)=0 → H=0) :
    let X (s : P') (i : A') := x (ep.symm s) (ea.symm i)
    let Y (s : P') (j : B') := y (ep.symm s) (eb.symm j)
    ∀ H : Q → A' × B' → ℂ,
      (∀ t s, ∑ ij : A' × B', (X s ij.1*Y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, Y (ep (first t)) j*H t (i,j)=0) →
      (∀ t j, ∑ i, X (ep (first t)) i*H t (i,j)=0) → (∑ t, H t)=0 → H=0 := by
  classical
  intro X Y H outer row col total
  let pull (t : Q) (ij : A × B) := H t (ea ij.1,eb ij.2)
  have out (t : Q) (s : P) : ∑ ij : A × B, (x s ij.1*y s ij.2)*pull t ij=0 := by
    have h := outer t (ep s)
    rw [← (ea.prodCongr eb).sum_comp] at h
    simpa only [pull,X,Y,Equiv.prodCongr_apply,Prod.map,Equiv.symm_apply_apply] using h
  have rows (t : Q) (i : A) : ∑ j, y (first t) j*pull t (i,j)=0 := by
    have h := row t (ea i)
    rw [← eb.sum_comp] at h
    simpa only [pull,Y,Equiv.symm_apply_apply] using h
  have cols (t : Q) (j : B) : ∑ i, x (first t) i*pull t (i,j)=0 := by
    have h := col t (eb j)
    rw [← ea.sum_comp] at h
    simpa only [pull,X,Equiv.symm_apply_apply] using h
  have trace : ∑ t, pull t=0 := by
    funext ij
    simpa only [Finset.sum_apply,pull,Pi.zero_apply] using congrFun total (ea ij.1,eb ij.2)
  have zero := ind pull out rows cols trace
  funext t ij
  simpa only [pull,Equiv.apply_symm_apply,Prod.mk.eta,Pi.zero_apply] using
    congrFun (congrFun zero t) (ea.symm ij.1,eb.symm ij.2)

/-- Interchanging the two matrix axes preserves directness of the marked normals. -/
private lemma transpose_fixed_rows {A B P Q : Type*} [Fintype A] [Fintype B] [Fintype Q]
    (x : P → A → ℂ) (y : P → B → ℂ) (e : Q ↪ P)
    (direct : ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0) : ∀ H : Q → B×A → ℂ,
      (∀ t s, (∑ ij : B×A, (y s ij.1*x s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, x (e t) j*H t (i,j))=0) → (∀ t j, (∑ i, y (e t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0 := by
  intro H outer row col total
  let F (t : Q) (ij : A×B) := H t ij.swap
  have prod (t : Q) (s : P) : (∑ ij : A×B, (x s ij.1*y s ij.2)*F t ij)=0 := by
    have eq := outer t s
    rw [← (Equiv.prodComm A B).sum_comp] at eq
    simpa only [F,Equiv.prodComm_apply,Prod.fst_swap,Prod.snd_swap,mul_comm] using eq
  have sum : (∑ t,F t)=0 := by
    funext ij
    simpa only [F,Finset.sum_apply,Pi.zero_apply] using congrFun total ij.swap
  have zero := direct F prod (fun t i => col t i) (fun t j => row t j) sum
  funext t ij
  exact congrFun (congrFun zero t) ij.swap

/-- With the second side designated for the groups, any subset up to the
Vandermonde capacity keeps its independent normals and separated factors. -/
private lemma finite_rows_in_order {a b m : ℕ} (ha : 3≤a) (hb : 4≤b)
    (hm : m ≤ b-1+min a (b-1)) :
    ∃ first : Fin m ↪ Fin ((a-1)*(b-1)),
    ∃ x : Fin ((a-1)*(b-1)) → Fin a → ℂ, ∃ y : Fin ((a-1)*(b-1)) → Fin b → ℂ,
    (∀ H : Fin m → Fin a × Fin b → ℂ,
      (∀ t s, (∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (first t) j*H t (i,j))=0) →
      (∀ t j, (∑ i, x (first t) i*H t (i,j))=0) → (∑ t,H t)=0 → H=0) ∧
    (∀ t, x (first t) ≠ 0) ∧ (∀ t, y (first t) ≠ 0) ∧
    (∀ i j, i ≠ j → ∀ c : ℂ, x (first i) ≠ c • x (first j)) ∧
    (∀ i j, i ≠ j → ∀ c : ℂ, y (first i) ≠ c • y (first j)) := by
  classical
  obtain ⟨A,rfl⟩ : ∃ A, a=A+3 := ⟨a-3,by omega⟩
  obtain ⟨B,rfl⟩ : ∃ B, b=B+1 := ⟨b-1,by omega⟩
  let P := Fin B × (Fin 2 ⊕ Fin A)
  let Q := Fin B ⊕ Fin (min (A+3) B)
  let w := (A+2)*B
  have size : Fintype.card P=w := by simp [P,w,Fintype.card_prod,Nat.mul_comm,Nat.add_comm]
  let ep : P ≃ Fin w := (Fintype.equivFin P).trans (finCongr size)
  let ea : (Fin 3 ⊕ Fin A) ≃ Fin (A+3) := finSumFinEquiv.trans (finCongr (Nat.add_comm 3 A))
  let eb : Option (Fin B) ≃ Fin (B+1) := (finSuccEquiv B).symm
  obtain ⟨mark,x,y,direct,nx,ny,dx,dy⟩ := exists_large_batch_separated A B (by omega)
  obtain ⟨clip⟩ : Nonempty (Fin m ↪ Q) :=
    Function.Embedding.nonempty_of_card_le (by simpa [Q] using hm)
  let e : Fin m ↪ P := clip.trans mark
  let first : Fin m ↪ Fin w := e.trans ep.toEmbedding
  let X (s : Fin w) (i : Fin (A+3)) := x (ep.symm s) (ea.symm i)
  let Y (s : Fin w) (j : Fin (B+1)) := y (ep.symm s) (eb.symm j)
  have atX (t : Fin m) (i : Fin 3 ⊕ Fin A) : X (first t) (ea i) = x (mark (clip t)) i := by
    change x (ep.symm (ep (mark (clip t)))) (ea.symm (ea i)) = _
    simp
  have atY (t : Fin m) (j : Option (Fin B)) : Y (first t) (eb j) = y (mark (clip t)) j := by
    change y (ep.symm (ep (mark (clip t)))) (eb.symm (eb j)) = _
    simp
  have restricted := restrict_fixed_rows x y mark clip direct
  refine ⟨first,X,Y,move_fixed_rows ea eb ep e x y restricted,?_,?_,?_,?_⟩
  · intro t he
    apply nx (clip t)
    funext i
    simpa only [atX,Pi.zero_apply] using congrFun he (ea i)
  · intro t he
    apply ny (clip t)
    funext j
    simpa only [atY,Pi.zero_apply] using congrFun he (eb j)
  · intro i j hne c he
    apply dx (clip i) (clip j) (fun h => hne (clip.injective h)) c
    funext u
    simpa only [Pi.smul_apply,atX] using congrFun he (ea u)
  · intro i j hne c he
    apply dy (clip i) (clip j) (fun h => hne (clip.injective h)) c
    funext u
    simpa only [Pi.smul_apply,atY] using congrFun he (eb u)

/-- A rectangle in either orientation admits any number of marked labels up to
the capacity of the longer side. The marked row directions are nonzero and
pairwise projectively distinct for the same factors with independent normals. -/
lemma exists_finite_batch_separated {a b m : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : 4 ≤ max a b)
    (hm : m ≤ max a b - 1 + min (min a b) (max a b - 1)) :
    ∃ first : Fin m ↪ Fin ((a-1)*(b-1)),
    ∃ x : Fin ((a-1)*(b-1)) → Fin a → ℂ, ∃ y : Fin ((a-1)*(b-1)) → Fin b → ℂ,
    (∀ H : Fin m → Fin a × Fin b → ℂ,
      (∀ t s, (∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (first t) j*H t (i,j))=0) →
      (∀ t j, (∑ i, x (first t) i*H t (i,j))=0) → (∑ t,H t)=0 → H=0) ∧
    (∀ t, x (first t) ≠ 0) ∧
    (∀ i j, i ≠ j → ∀ c : ℂ, x (first i) ≠ c • x (first j)) := by
  by_cases h : a≤b
  · rw [max_eq_right h] at hab
    rw [max_eq_right h,min_eq_left h] at hm
    obtain ⟨first,x,y,direct,nx,_,dx,_⟩ := finite_rows_in_order ha hab hm
    exact ⟨first,x,y,direct,nx,dx⟩
  · have h' : b≤a := by omega
    rw [max_eq_left h'] at hab
    rw [max_eq_left h',min_eq_right h'] at hm
    obtain ⟨first,x,y,direct,_,ny,_,dy⟩ := finite_rows_in_order hb hab hm
    rw [Nat.mul_comm (a-1) (b-1)]
    exact ⟨first,y,x,transpose_fixed_rows x y first direct,ny,dy⟩

end LastSliceTwo

namespace CriticalLastSlice.TwoPlanes.Cross

private lemma columnForm_point {a d : ℕ} (H : Fin a × Fin d → ℂ) (i : Fin a) (j : Fin d) :
    ((dotProductBilin ℂ ℂ).flip (fun r : Fin a => H (r,j))) (Pi.single i 1)=H (i,j) := by
  classical
  change (∑ k,(Pi.single i (1:ℂ) : Fin a→ℂ) k*H (k,j))=_
  simp [Pi.single_apply,ite_mul]

private lemma columnForm_sum {a d m : ℕ} (H : Fin m → Fin a × Fin d → ℂ)
    (zero : ∑ t,H t=0) (j : Fin d) : ∑ t,((dotProductBilin ℂ ℂ).flip (fun r : Fin a => H t (r,j)))=0 := by
  apply LinearMap.ext
  intro x
  have at_point (i : Fin a) : ∑ t,H t (i,j)=0 := by
    simpa only [Finset.sum_apply,Pi.zero_apply] using congrFun zero (i,j)
  change (∑ t,((dotProductBilin ℂ ℂ).flip (fun r : Fin a => H t (r,j)))) x=0
  rw [LinearMap.sum_apply]
  change (∑ t, ∑ i, x i*H t (i,j))=0
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,at_point,mul_zero,Finset.sum_const_zero]

private lemma pair_coeff {V : Type*} [AddCommGroup V] [Module ℂ V] (L M : V)
    (lin : LinearIndependent ℂ ![L,M]) (c d : ℂ) (h : c • L+d • M=0) : c=0 ∧ d=0 := by
  have rel : ∑ i : Fin 2, (![c,d] : Fin 2→ℂ) i • (![L,M] : Fin 2→V) i=0 := by
    simpa [Fin.sum_univ_two] using h
  have good := Fintype.linearIndependent_iff.mp lin (![c,d] : Fin 2→ℂ) rel
  exact ⟨good 0,good 1⟩

/-- A family of column matrices represented by one common central coefficient
and one coefficient per column has independent marked kernels if each marked
row vanishes on exactly its own node form. -/
theorem tagged_columns {a d m : ℕ} (L : Fin (d+2)→Module.Dual ℂ (Fin a→ℂ))
    (rows : Fin m→Fin a→ℂ) (label : Fin m↪Fin (d+2))
    (zeros : ∀ i t,L i (rows t)=0 ↔ i=label t)
    (pair : ∀ j : Fin (d+1),LinearIndependent ℂ ![L 0,L j.succ])
    (H : Fin m→Fin a × Fin (d+1)→ℂ) (coeff : Fin m→Fin (d+2)→ℂ)
    (form : ∀ t j, ((dotProductBilin ℂ ℂ).flip (fun r : Fin a => H t (r,j)))=coeff t 0 • L 0 + coeff t j.succ • L j.succ)
    (mark : ∀ t j, ∑ i,rows t i*H t (i,j)=0) (total : ∑ t,H t=0) : H=0 := by
  classical
  have eq (t : Fin m) (j : Fin (d+1)) :
      coeff t 0*L 0 (rows t)+coeff t j.succ*L j.succ (rows t)=0 := by
    have h := congrArg (fun f : Module.Dual ℂ (Fin a→ℂ) => f (rows t)) (form t j).symm
    exact h.trans (mark t j)
  have centered (t : Fin m) : coeff t 0*L 0 (rows t)=0 := by
    by_cases hz : label t=0
    · rw [(zeros 0 t).mpr hz.symm,mul_zero]
    · obtain ⟨j,he⟩ := Fin.exists_succ_eq_of_ne_zero hz
      simpa only [(zeros j.succ t).mpr he,mul_zero,add_zero] using eq t j
  have support (t : Fin m) (s : Fin (d+2)) (ne : s≠label t) : coeff t s=0 := by
    have prod : coeff t s*L s (rows t)=0 := by
      cases s using Fin.cases with
      | zero => exact centered t
      | succ j => simpa only [centered t,zero_add] using eq t j
    exact (mul_eq_zero.mp prod).resolve_right (fun hs => ne ((zeros s t).mp hs))
  have sums (j : Fin (d+1)) : (∑ t,coeff t 0)=0 ∧ (∑ t,coeff t j.succ)=0 := by
    apply pair_coeff (L 0) (L j.succ) (pair j)
    have h := columnForm_sum H total j
    simp_rw [form] at h
    simpa only [Finset.sum_add_distrib,← Finset.sum_smul] using h
  have sumzero (s : Fin (d+2)) : (∑ t,coeff t s)=0 := by
    cases s using Fin.cases with
    | zero => exact (sums 0).1
    | succ j => exact (sums j).2
  have each (t : Fin m) (s : Fin (d+2)) : coeff t s=0 := by
    by_cases h : s=label t
    · subst s
      have h' := sumzero (label t)
      rw [Finset.sum_eq_single t] at h'
      · exact h'
      · intro v _ hv
        exact support v _ (fun eq' => hv (label.injective eq'.symm))
      · simp
    · exact support t s h
  funext t ij
  obtain ⟨i,j⟩ := ij
  have h : ((dotProductBilin ℂ ℂ).flip (fun r : Fin a => H t (r,j)))=0 := by rw [form,each,each,zero_smul,zero_smul,add_zero]
  rw [← columnForm_point (H t) i j,h]
  rfl

end CriticalLastSlice.TwoPlanes.Cross

namespace CriticalLastSlice.TwoPlanes.Cross

private lemma point_eval {a d : ℕ} (v : Fin a→ℂ) (H : Fin a × Fin d→ℂ) (j : Fin d) :
    (∑ ij : Fin a × Fin d, (v ij.1*(Pi.single j 1 : Fin d→ℂ) ij.2)*H ij)=((dotProductBilin ℂ ℂ).flip (fun r : Fin a => H (r,j))) v := by
  classical
  rw [Fintype.sum_prod_type]
  change (∑ i,∑ k,(v i*(Pi.single j (1:ℂ) : Fin d→ℂ) k)*H (i,k))=∑ i,v i*H (i,j)
  simp [Pi.single_apply,mul_ite,ite_mul]

private lemma difference_eval {a d : ℕ} (v : Fin a→ℂ) (H : Fin a × Fin d→ℂ) (i j : Fin d) :
    (∑ ij : Fin a × Fin d, (v ij.1*(Pi.single i 1-Pi.single j 1 : Fin d→ℂ) ij.2)*H ij) =
      ((dotProductBilin ℂ ℂ).flip (fun r : Fin a => H (r,i))) v - ((dotProductBilin ℂ ℂ).flip (fun r : Fin a => H (r,j))) v := by
  simp only [Pi.sub_apply,mul_sub,sub_mul,Finset.sum_sub_distrib,point_eval]

/-- The cross block is realized with (a−2) samples in each column and one
link sample for every column after the first. The link samples force all
coefficients of the central form to coincide. -/
theorem from_scalar_tests {a d m : ℕ} (ha : 3≤a)
    (L : Fin (d+2)→Module.Dual ℂ (Fin a→ℂ))
    (rows : Fin m→Fin a→ℂ) (label : Fin m↪Fin (d+2))
    (zeros : ∀ i t,L i (rows t)=0 ↔ i=label t)
    (pair : ∀ j : Fin (d+1),LinearIndependent ℂ ![L 0,L j.succ])
    (columns : ∀ j : Fin (d+1), ∃ b : Fin (a-2)→Fin a→ℂ,
      ∀ f : Module.Dual ℂ (Fin a→ℂ), (∀ k,f (b k)=0) → ∃ u v : ℂ, f=u • L 0+v • L j.succ)
    (links : ∀ j : Fin d, ∃ x : Fin a→ℂ, L 0 x=1 ∧ L ((0:Fin (d+1)).succ) x=0 ∧
      L j.succ.succ x=0) :
    ∃ X : Fin ((a-1)*(d+1)-1)→Fin a→ℂ, ∃ Y : Fin ((a-1)*(d+1)-1)→Fin (d+1)→ℂ,
      ∀ H : Fin m→Fin a × Fin (d+1)→ℂ,
        (∀ t s, ∑ ij : Fin a × Fin (d+1), (X s ij.1*Y s ij.2)*H t ij=0) →
        (∀ t j, ∑ i,rows t i*H t (i,j)=0) → (∑ t,H t)=0 → H=0 := by
  classical
  let S := (Fin (d+1) × Fin (a-2)) ⊕ Fin d
  have calcN : (d+1)*(a-2)+d+1=(a-1)*(d+1) := by
    rw [show a-1=(a-2)+1 by omega]
    ring
  let e : S ≃ Fin ((a-1)*(d+1)-1) := Fintype.equivOfCardEq (by
    simp only [S,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega)
  choose b hb using columns
  choose w hw using links
  let x : S→Fin a→ℂ := Sum.elim (fun jk => b jk.1 jk.2) w
  let y : S→Fin (d+1)→ℂ := Sum.elim (fun jk => Pi.single jk.1 1)
    (fun k => Pi.single k.succ 1-Pi.single 0 1)
  refine ⟨fun s => x (e.symm s),fun s => y (e.symm s),?_⟩
  intro H prod mark total
  have vanish (t : Fin m) (s : S) : ∑ ij : Fin a × Fin (d+1), (x s ij.1*y s ij.2)*H t ij=0 := by
    simpa only [Equiv.symm_apply_apply] using prod t (e s)
  have allk (t : Fin m) (j : Fin (d+1)) (k : Fin (a-2)) : ((dotProductBilin ℂ ℂ).flip (fun r : Fin a => H t (r,j))) (b j k)=0 :=
    (point_eval (b j k) (H t) j).symm.trans (vanish t (.inl (j,k)))
  choose u v represent using fun t j => hb j (((dotProductBilin ℂ ℂ).flip (fun r : Fin a => H t (r,j)))) (allk t j)
  have same (t : Fin m) (j : Fin (d+1)) : u t j=u t 0 := by
    cases j using Fin.cases with
    | zero => rfl
    | succ k =>
      have a0 := (difference_eval (w k) (H t) k.succ 0).symm.trans (vanish t (.inr k))
      rw [represent,represent] at a0
      obtain ⟨h0,h1,h2⟩ := hw k
      simpa only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,h0,h1,h2,mul_one,mul_zero,add_zero,sub_eq_zero]
        using a0
  let coeff (t : Fin m) : Fin (d+2)→ℂ := Fin.cases (u t 0) (v t)
  apply tagged_columns L rows label zeros pair H coeff _ mark total
  intro t j
  change ((dotProductBilin ℂ ℂ).flip (fun r : Fin a => H t (r,j)))=u t 0 • L 0 + v t j • L j.succ
  rw [← same t j]
  exact represent t j

end CriticalLastSlice.TwoPlanes.Cross

namespace CriticalLastSlice.TwoPlanes.Cross

/-- For d+1 additional columns choose (a−1)(d+1)−1 product samples.
Each marked row has one remaining cross normal, and all those lines are independent. -/
theorem exists_cross {a d m : ℕ} (ha : 3≤a) (hm : m≤d+2)
    (rows : Fin m→Fin a→ℂ) (nonzero : ∀ t,rows t≠0)
    (distinct : ∀ s t : Fin m,s≠t → rows s ∉ Submodule.span ℂ {rows t}) :
    ∃ X : Fin ((a-1)*(d+1)-1)→Fin a→ℂ, ∃ Y : Fin ((a-1)*(d+1)-1)→Fin (d+1)→ℂ,
      ∀ H : Fin m→Fin a × Fin (d+1)→ℂ,
        (∀ t s, ∑ ij : Fin a × Fin (d+1), (X s ij.1*Y s ij.2)*H t ij=0) →
        (∀ t j, ∑ i,rows t i*H t (i,j)=0) → (∑ t,H t)=0 → H=0 := by
  classical
  obtain ⟨L,inc,gen⟩ := TwoNormalAvoiding.choose_forms (d:=d+1) ha hm rows nonzero distinct
  let label : Fin m ↪ Fin (d+2) := Fin.castLEEmb hm
  have zero (i : Fin (d+2)) (t : Fin m) : L i (rows t)=0 ↔ i=label t := by
    rw [inc]
    exact ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  have pair (j : Fin (d+1)) : LinearIndependent ℂ ![L 0,L j.succ] := by
    let e : Fin 2 ↪ Fin (d+2) := {
      toFun := ![0,j.succ]
      inj' := by
        intro u v h
        fin_cases u <;> fin_cases v
        · rfl
        · have bad : (0:ℕ) = j.val+1 := congrArg Fin.val h
          omega
        · have bad : j.val+1 = (0:ℕ) := congrArg Fin.val h
          omega
        · rfl }
    have result := TwoNormalAvoiding.independent_of_injective_tuple L gen e (by simp)
    have eq : (fun i => L (e i))=![L 0,L j.succ] := by funext i; fin_cases i <;> rfl
    exact eq ▸ result
  apply from_scalar_tests ha L rows label zero pair
  · intro j
    obtain ⟨B,_,_,all⟩ := CriticalLastSlice.TwoPlanes.common_kernel_basis (L 0) (L j.succ) (pair j)
    exact ⟨B,fun f => (all f).mp⟩
  · intro j
    let e : Fin 3 ↪ Fin (d+2) := {
      toFun := ![0,(0:Fin (d+1)).succ,j.succ.succ]
      inj' := by
        intro u v h
        fin_cases u <;> fin_cases v
        · rfl
        · have bad : (0:ℕ) = (1:ℕ) := congrArg Fin.val h
          omega
        · have bad : (0:ℕ) = j.val+2 := congrArg Fin.val h
          omega
        · have bad : (1:ℕ) = (0:ℕ) := congrArg Fin.val h
          omega
        · rfl
        · have bad : (1:ℕ) = j.val+2 := congrArg Fin.val h
          omega
        · have bad : j.val+2 = (0:ℕ) := congrArg Fin.val h
          omega
        · have bad : j.val+2 = (1:ℕ) := congrArg Fin.val h
          omega
        · rfl }
    have result := TwoNormalAvoiding.independent_of_injective_tuple L gen e (by simp)
    have eq : (fun i => L (e i))=![L 0,L ((0:Fin (d+1)).succ),L j.succ.succ] := by
      funext i; fin_cases i <;> rfl
    exact CriticalLastSlice.TwoPlanes.dual_separate_three _ _ _ (eq ▸ result)

/-- The same cross construction indexed by the actual additional width. -/
theorem exists_cross_width {a width m : ℕ} (ha : 3≤a) (positive : 0<width) (hm : m≤width+1)
    (rows : Fin m→Fin a→ℂ) (nonzero : ∀ t,rows t≠0)
    (distinct : ∀ s t : Fin m,s≠t → rows s ∉ Submodule.span ℂ {rows t}) :
    ∃ X : Fin ((a-1)*width-1)→Fin a→ℂ, ∃ Y : Fin ((a-1)*width-1)→Fin width→ℂ,
      ∀ H : Fin m→Fin a × Fin width→ℂ,
        (∀ t s, ∑ ij : Fin a × Fin width, (X s ij.1*Y s ij.2)*H t ij=0) →
        (∀ t j, ∑ i,rows t i*H t (i,j)=0) → (∑ t,H t)=0 → H=0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  exact exists_cross ha hm rows nonzero distinct

end CriticalLastSlice.TwoPlanes.Cross

namespace CriticalLastSlice.TwoPlanes.Cross

/-- Join the original batch in the first column block to the independent
cross normal lines in a disjoint column block. All marks lie in the first block. -/
theorem split_marked {a b w m : ℕ} (ha : 3≤a) (hb : 0<b) (hw : 0<w) (hm : m≤w+1)
    (first : Fin m↪Fin ((a-1)*(b-1)))
    (x : Fin ((a-1)*(b-1))→Fin a→ℂ) (y : Fin ((a-1)*(b-1))→Fin b→ℂ)
    (old : ∀ H : Fin m→Fin a × Fin b→ℂ,
      (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j,y (first t) j*H t (i,j)=0) →
      (∀ t j, ∑ i,x (first t) i*H t (i,j)=0) → (∑ t,H t)=0 → H=0)
    (nz : ∀ t,x (first t)≠0)
    (sep : ∀ s t : Fin m,s≠t → x (first s) ∉ Submodule.span ℂ {x (first t)}) :
    ∃ label : Fin m↪Fin ((a-1)*(b+w-1)-1),
    ∃ X : Fin ((a-1)*(b+w-1)-1)→Fin a→ℂ, ∃ Y : Fin ((a-1)*(b+w-1)-1)→Fin (b+w)→ℂ,
      ∀ H : Fin m→Fin a × Fin (b+w)→ℂ,
        (∀ t s, ∑ ij : Fin a × Fin (b+w), (X s ij.1*Y s ij.2)*H t ij=0) →
        (∀ t i, ∑ j,Y (label t) j*H t (i,j)=0) →
        (∀ t j, ∑ i,X (label t) i*H t (i,j)=0) → (∑ t,H t)=0 → H=0 := by
  classical
  let r := (a-1)*(b-1)
  let c := (a-1)*w-1
  let n := (a-1)*(b+w-1)-1
  have pos : 1≤(a-1)*w := Nat.mul_pos (by omega) hw
  have dim : r+c=n := by
    have id : (a-1)*(b+w-1)=(a-1)*(b-1)+(a-1)*w := by
      rw [show b+w-1=(b-1)+w by omega,Nat.mul_add]
    dsimp [r,c,n]
    omega
  let S := Fin r ⊕ Fin c
  let J := Fin b ⊕ Fin w
  let e : J ≃ Fin (b+w) := finSumFinEquiv
  let f : S ≃ Fin n := finSumFinEquiv.trans (finCongr dim)
  let label : Fin m ↪ Fin n := {
    toFun := fun t => f (.inl (first t))
    inj' := fun _ _ he => first.injective (Sum.inl.inj (f.injective he)) }
  have first_back (t : Fin m) : f.symm (label t)=Sum.inl (first t) := f.symm_apply_apply _
  obtain ⟨xc,yc,cross⟩ := exists_cross_width ha hw hm (fun t => x (first t)) nz sep
  let XX : S → Fin a → ℂ := Sum.elim x xc
  let YY : S → J → ℂ := Sum.elim (fun s => Sum.elim (y s) (fun _ => 0))
                                     (fun s => Sum.elim (fun _ => 0) (yc s))
  refine ⟨label,fun s => XX (f.symm s),fun s j => YY (f.symm s) (e.symm j),?_⟩
  intro H prod rows cols sum
  let left (t : Fin m) (ij : Fin a × Fin b) := H t (ij.1,e (.inl ij.2))
  let right (t : Fin m) (ij : Fin a × Fin w) := H t (ij.1,e (.inr ij.2))
  have both (t : Fin m) (s : S) :
      ∑ i,∑ j : J,(XX s i*YY s j)*H t (i,e j)=0 := by
    have h := prod t (f s)
    rw [Fintype.sum_prod_type] at h
    simp only [Equiv.symm_apply_apply] at h
    calc
      _ = ∑ i,∑ j : Fin (b+w),(XX s i*YY s (e.symm j))*H t (i,j) := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [Equiv.symm_apply_apply] using e.sum_comp (fun j => (XX s i*YY s (e.symm j))*H t (i,j))
      _ = 0 := h
  have left_prod (t : Fin m) (s : Fin r) :
      ∑ ij : Fin a × Fin b,(x s ij.1*y s ij.2)*left t ij=0 := by
    simpa only [left,J,Fintype.sum_prod_type,Fintype.sum_sum_type,XX,YY,Sum.elim_inl,Sum.elim_inr,
      mul_zero,zero_mul,Finset.sum_const_zero,add_zero] using both t (.inl s)
  have right_prod (t : Fin m) (s : Fin c) :
      ∑ ij : Fin a × Fin w,(xc s ij.1*yc s ij.2)*right t ij=0 := by
    simpa only [right,J,Fintype.sum_prod_type,Fintype.sum_sum_type,XX,YY,Sum.elim_inl,Sum.elim_inr,
      mul_zero,zero_mul,Finset.sum_const_zero,zero_add] using both t (.inr s)
  have row (t : Fin m) (i : Fin a) : ∑ j, y (first t) j*left t (i,j)=0 := by
    have h := rows t i
    rw [← e.sum_comp] at h
    simpa only [left,J,first_back,Equiv.symm_apply_apply,Fintype.sum_sum_type,
      YY,Sum.elim_inl,Sum.elim_inr,zero_mul,Finset.sum_const_zero,add_zero] using h
  have lcol (t : Fin m) (j : Fin b) : ∑ i, x (first t) i*left t (i,j)=0 := by
    simpa only [left,XX,first_back,Equiv.symm_apply_apply,Sum.elim_inl]
      using cols t (e (.inl j))
  have rcol (t : Fin m) (j : Fin w) : ∑ i, x (first t) i*right t (i,j)=0 := by
    simpa only [right,XX,first_back,Equiv.symm_apply_apply,Sum.elim_inl]
      using cols t (e (.inr j))
  have left_sum : ∑ t,left t=0 := by
    funext ij
    simpa only [Finset.sum_apply,left,Pi.zero_apply] using congrFun sum (ij.1,e (.inl ij.2))
  have right_sum : ∑ t,right t=0 := by
    funext ij
    simpa only [Finset.sum_apply,right,Pi.zero_apply] using congrFun sum (ij.1,e (.inr ij.2))
  have lz := old left left_prod row lcol left_sum
  have rz := cross right right_prod rcol right_sum
  funext t ij
  obtain ⟨i,j⟩ := ij
  obtain ⟨u|v,rfl⟩ := e.surjective j
  · exact congrFun (congrFun lz t) (i,u)
  · exact congrFun (congrFun rz t) (i,v)

end CriticalLastSlice.TwoPlanes.Cross

namespace CriticalLastSlice.TwoPlanes.Cross

/-- Choose the core and added widths to balance the two independent normal
lines. At b=3a−2 the required core is square and its known marking is one smaller. -/
theorem rectangular_widths {a b : ℕ} (ha : 3≤a) (gap : a+3≤b)
    (size : 4≤a ∨ 8≤b) (exception : b+2≠3*a) :
    let m := (a+b)/2
    ∃ u w : ℕ, u+w=b ∧ 3≤u ∧ 4≤ max a u ∧ 0<w ∧
      m≤ max a u-1+min (min a u) (max a u-1) ∧ m≤w+1 := by
  intro m
  let u := b+1-m
  let w := m-1
  have hm : m=(a+b)/2 := rfl
  have hu : u=b+1-m := rfl
  have hw : w=m-1 := rfl
  refine ⟨u,w,by omega,by omega,?_,by omega,?_,by omega⟩
  · rcases size with h|h
    · exact h.trans (le_max_left _ _)
    · by_cases h' : 4≤a
      · exact h'.trans (le_max_left _ _)
      · exact (show 4≤u by omega).trans (le_max_right _ _)
  · rcases lt_trichotomy a u with lt | eq | gt
    · rw [max_eq_right lt.le,min_eq_left lt.le,min_eq_left (by omega : a≤u-1)]
      omega
    · rw [← eq,max_self,min_self,min_eq_right (Nat.sub_le a 1)]
      omega
    · rw [max_eq_left gt.le,min_eq_right gt.le,min_eq_left (by omega : u≤a-1)]
      omega

end CriticalLastSlice.TwoPlanes.Cross

namespace CriticalLastSlice.TwoPlanes.Cross

/-- A separated one-dimensional marking in the core and the tagged cross
construction give independent two-dimensional normals throughout these formats. -/
theorem rectangular_batch {a b₁ w m : ℕ} (ha : 3≤a) (hb : 3≤b₁) (big : 4≤ max a b₁)
    (hw : 0<w) (core : m≤ max a b₁-1+min (min a b₁) (max a b₁-1)) (tail : m≤w+1) :
    ∃ label : Fin m↪Fin ((a-1)*(b₁+w-1)-1),
    ∃ X : Fin ((a-1)*(b₁+w-1)-1)→Fin a→ℂ, ∃ Y : Fin ((a-1)*(b₁+w-1)-1)→Fin (b₁+w)→ℂ,
      ∀ H : Fin m→Fin a × Fin (b₁+w)→ℂ,
        (∀ t s, ∑ ij : Fin a × Fin (b₁+w), (X s ij.1*Y s ij.2)*H t ij=0) →
        (∀ t i, ∑ j,Y (label t) j*H t (i,j)=0) →
        (∀ t j, ∑ i,X (label t) i*H t (i,j)=0) → (∑ t,H t)=0 → H=0 := by
  obtain ⟨first,x,y,old,nz,separate⟩ := LastSliceTwo.exists_finite_batch_separated ha hb big core
  apply split_marked ha (by omega) hw tail first x y old nz
  intro s t ne membership
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp membership
  exact separate s t ne c hc.symm

/-- For long rectangles satisfying the displayed numerical conditions,
the batch attains the dimension bound floor((a+b)/2). -/
theorem half_batch {a b : ℕ} (ha : 3≤a) (gap : a+3≤b) (size : 4≤a ∨ 8≤b)
    (exception : b+2≠3*a) :
    let m := (a+b)/2
    ∃ label : Fin m↪Fin ((a-1)*(b-1)-1),
    ∃ X : Fin ((a-1)*(b-1)-1)→Fin a→ℂ, ∃ Y : Fin ((a-1)*(b-1)-1)→Fin b→ℂ,
      ∀ H : Fin m→Fin a × Fin b→ℂ,
        (∀ t s, ∑ ij : Fin a × Fin b, (X s ij.1*Y s ij.2)*H t ij=0) →
        (∀ t i, ∑ j,Y (label t) j*H t (i,j)=0) →
        (∀ t j, ∑ i,X (label t) i*H t (i,j)=0) → (∑ t,H t)=0 → H=0 := by
  obtain ⟨u,w,dim,hu,big,hw,core,tail⟩ := rectangular_widths ha gap size exception
  subst b
  exact rectangular_batch ha hu big hw core tail

end CriticalLastSlice.TwoPlanes.Cross

namespace CriticalLastSlice.TwoPlanes

/-- At this level the common ambient normal space has dimension a+b.
The expected tangent count provides at least as many scalar relation
equations as the two unknown coordinates at each sampled point. -/
theorem relation_budget (a b c r : ℕ) (ha : 3 ≤ a) (hb : a ≤ b)
    (level : r+1=(a-1)*(b-1)) (count : r=a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)) :
    a*b=r+(a+b) ∧ c+1≤r ∧ 2*r ≤ (r-(c+1))*(a+b) := by
  have ab : a*b=r+(a+b) := by
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b≠0)
    simp only [Nat.succ_sub_one] at level
    nlinarith only [level]
  let n := c+1
  let D := a+b+n-2
  have pos : 0<D := by dsimp [D,n]; omega
  have hden : D+2=a+b+n := by dsimp [D,n]; omega
  have cap : a*b*n ≤ D*r := by
    apply (ceilDiv_le_iff_le_mul pos).mp
    exact count.ge
  have budget : n*(a+b)+2*r ≤ r*(a+b) := by
    have hn := congrArg (fun q : ℕ => q*n) ab
    have hr := congrArg (fun q : ℕ => q*r) hden
    nlinarith only [cap,hn,hr]
  have enough : n≤r := Nat.le_of_mul_le_mul_right (show n*(a+b)≤r*(a+b) by omega) (by omega)
  refine ⟨ab,enough,?_⟩
  have h := congrArg (fun q : ℕ => q*(a+b)) (Nat.sub_add_cancel enough)
  change 2*r ≤ (r-n)*(a+b)
  nlinarith only [h,budget]

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes.Cross

/-- When all labels fit in ordinary disjoint batches, the optimal marking
generates a complete tangent-space witness in the original rectangular format. -/
theorem tangent {a b n r : ℕ} (ha : 3≤a) (gap : a+3≤b) (size : 4≤a ∨ 8≤b)
    (exception : b+2≠3*a) (level : r+1=(a-1)*(b-1)) (enough : n≤r)
    (fit : r≤(r-n)*((a+b)/2)) :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k=∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  classical
  have batch := half_batch ha gap size exception
  dsimp only at batch
  have hr : (a-1)*(b-1)-1=r := by omega
  rw [hr] at batch
  obtain ⟨first,x,y,one⟩ := batch
  obtain ⟨label,onto,bound⟩ := LastSliceBatch.balanced_partition (Nat.sub_le r n) fit
  have cap (g : Fin (r-n)) : Fintype.card {t : Fin r // label t=g} ≤ Fintype.card (Fin ((a+b)/2)) := by
    simpa only [Fintype.card_fin] using bound g
  obtain ⟨X,Y,direct⟩ := LastSliceBatch.common_small_fibers first label cap ⟨x,y,one⟩
  have h := LastSliceBatch.spans_of_ragged_independence label onto X Y direct
  rw [Fintype.card_fin r,Fintype.card_fin (r-n),show r-(r-n)=n by omega] at h
  exact h

/-- In the two-dimensional normal level the ordinary batch condition is
automatic when a+b is even. -/
theorem tangent_of_even {a b c r : ℕ} (ha : 3≤a) (gap : a+3≤b) (size : 4≤a ∨ 8≤b)
    (exception : b+2≠3*a) (even : Even (a+b)) (level : r+1=(a-1)*(b-1))
    (count : r=a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)) :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin (c+1) → ℂ,
      ∀ T : Fin a → Fin b → Fin (c+1) → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin (c+1) → ℂ, ∀ i j k,
          T i j k=∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  obtain ⟨_,enough,total⟩ := CriticalLastSlice.TwoPlanes.relation_budget a b c r ha (by omega) level count
  apply tangent ha gap size exception level enough
  obtain ⟨m,he⟩ := even
  have twice : (r-(c+1))*(a+b)=2*((r-(c+1))*m) := by rw [he]; ring
  rw [twice] at total
  rw [show (a+b)/2=m by omega]
  omega

end CriticalLastSlice.TwoPlanes.Cross

namespace CriticalLastSlice.TwoPlanes.Cross

/-- Past this explicit bound on the second side, the parameter count forces
at least 2(a−1) relations. Every sample then fits in the independent batches. -/
theorem ordinary_of_long {a b n r : ℕ} (ha : 3≤a) (long : a*(2*a-1)<b)
    (level : r+1=(a-1)*(b-1)) (ab : a*b=r+(a+b))
    (budget : 2*r≤(r-n)*(a+b)) : r≤(r-n)*((a+b)/2) := by
  have high : 2*(a-1)≤r-n := by
    by_contra! h
    have bound : r-n≤2*a-3 := by omega
    have small := budget.trans (Nat.mul_le_mul_right (a+b) bound)
    have e₁ := congrArg (fun k : ℕ => k*(a+b)) (show 2*a-3+3=2*a by omega)
    have e₂ := congrArg (fun k : ℕ => a*k) (show 2*a-1+1=2*a by omega)
    nlinarith only [small,ab,long,e₁,e₂]
  have hr : r≤(a-1)*b := (Nat.le_succ r).trans (level.le.trans (Nat.mul_le_mul_left _ (Nat.sub_le b 1)))
  calc
    _ ≤ (a-1)*b := hr
    _ ≤ (a-1)*(2*((a+b)/2)) := Nat.mul_le_mul_left _ (by omega)
    _ = (2*(a-1))*((a+b)/2) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ high

private lemma long_conditions {a b : ℕ} (ha : 3≤a) (h : a*(2*a-1)<b) :
    a+3≤b ∧ (4≤a ∨ 8≤b) ∧ b+2≠3*a := by
  have triple : 3*a < b := calc
    3*a = a*3 := Nat.mul_comm _ _
    _ ≤ a*(2*a-1) := Nat.mul_le_mul_left _ (by omega)
    _ < b := h
  omega

theorem tangent_of_long {a b c r : ℕ} (ha : 3≤a) (long : a*(2*a-1)<b)
    (level : r+1=(a-1)*(b-1)) (count : r=a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)) :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin (c+1) → ℂ,
      ∀ T : Fin a → Fin b → Fin (c+1) → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin (c+1) → ℂ, ∀ i j k,
          T i j k=∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  obtain ⟨gap,size,ex⟩ := long_conditions ha long
  obtain ⟨ab,enough,budget⟩ := CriticalLastSlice.TwoPlanes.relation_budget a b c r ha (by omega) level count
  exact tangent ha gap size ex level enough (ordinary_of_long ha long level ab budget)

end CriticalLastSlice.TwoPlanes.Cross

namespace CriticalLastSlice.TwoPlanes

open MvPolynomial Arxiv.«0805.3777»

/-- A complex spanning tangent witness exists exactly when the normal tuples
at the independent rational-function coordinates are detected by the third-factor relations. -/
theorem witness_iff_normals {a b n r : ℕ} (enough : n ≤ r) :
    (∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) ↔
    let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin n))
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let q (s : V) := algebraMap R K (X s)
    let x (t : Fin r) (i : Fin a) := q (t,.inl i)
    let y (t : Fin r) (j : Fin b) := q (t,.inr (.inl j))
    let z (t : Fin r) (k : Fin n) := q (t,.inr (.inr k))
    ∀ F : Fin r → Fin a × Fin b → K,
      (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*F t ij=0) →
      (∀ t i, ∑ j, y t j*F t (i,j)=0) → (∀ t j, ∑ i, x t i*F t (i,j)=0) →
      (∀ v : Fin r → K, (∀ k, ∑ t, v t*z t k=0) → ∑ t, v t • F t=0) → F=0 := by
  let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin n))
  let R := MvPolynomial V ℂ
  let K := FractionRing R
  let q (s : V) := algebraMap R K (X s)
  let x (t : Fin r) (i : Fin a) := q (t,.inl i)
  let y (t : Fin r) (j : Fin b) := q (t,.inr (.inl j))
  let z (t : Fin r) (k : Fin n) := q (t,.inr (.inr k))
  let P : Matrix ((Fin a × Fin b) × Fin n) V R := fun row col =>
    col.2.elim (fun i => if i=row.1.1 then X (col.1,.inr (.inl row.1.2))*X (col.1,.inr (.inr row.2)) else 0)
      (Sum.elim (fun j => if j=row.1.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inr row.2)) else 0)
        (fun k => if k=row.2 then X (col.1,.inl row.1.1)*X (col.1,.inr (.inl row.1.2)) else 0))
  have specialized := CriticalJacobian.restricted_tangent_iff (a:=a) (b:=b) (c:=n) (r:=r) id P
    (fun _ _ _ _ _ => rfl)
  apply specialized.trans ((CriticalTensor.Unrestricted.generic_surjective_iff P).symm.trans ?_)
  apply LastSliceRelation.tangent_iff_normal_relations x y z (CriticalLastSlice.third_span a b n r enough)
  intro i j k t v
  change algebraMap R K (P ((i,j),k) (t,v)) = _
  rcases v with i' | j' | k'
  · by_cases hi : i'=i <;> simp [P,x,y,z,q,hi]
  · by_cases hj : j'=j <;> simp [P,x,y,z,q,hj]
  · by_cases hk : k'=k <;> simp [P,x,y,z,q,hk]

/-- A spanning witness at the parameter-count ceiling gives the original
complex generic-rank conclusion in balanced dimensions. -/
theorem generic_rank_of_witness {a b n r : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) (hbn : b ≤ n)
    (count : r = a*b*n ⌈/⌉ (a+b+n-2))
    (witness : ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    IsGenericRank [a,b,n] r := by
  subst r
  exact OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1.generic_of_bounded a b n ha hab hbn
    (CriticalReduction.bounded_of_witness witness)

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes.Cross

open Arxiv.«0805.3777» MvPolynomial

theorem generic_rank {a b n r : ℕ} (ha : 3≤a) (gap : a+3≤b) (size : 4≤a ∨ 8≤b)
    (exception : b+2≠3*a) (hbn : b≤n) (level : r+1=(a-1)*(b-1)) (enough : n≤r)
    (fit : r≤(r-n)*((a+b)/2)) (count : r=a*b*n ⌈/⌉ (a+b+n-2)) :
    IsGenericRank [a,b,n] r :=
  CriticalLastSlice.TwoPlanes.generic_rank_of_witness ha (by omega) hbn count
    (tangent ha gap size exception level enough fit)

theorem generic_rank_of_even {a b c r : ℕ} (ha : 3≤a) (gap : a+3≤b) (size : 4≤a ∨ 8≤b)
    (exception : b+2≠3*a) (even : Even (a+b)) (hbc : b≤c+1) (level : r+1=(a-1)*(b-1))
    (count : r=a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)) : IsGenericRank [a,b,c+1] r :=
  CriticalLastSlice.TwoPlanes.generic_rank_of_witness ha (by omega) hbc count
    (tangent_of_even ha gap size exception even level count)

/-- The literal generic weighted normal equations of the registered H1 step. -/
theorem registered_normals {a b n r : ℕ} (ha : 3≤a) (gap : a+3≤b) (size : 4≤a ∨ 8≤b)
    (exception : b+2≠3*a) (level : r+1=(a-1)*(b-1)) (enough : n≤r)
    (fit : r≤(r-n)*((a+b)/2)) :
    let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin n))
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let q (s : V) := algebraMap R K (X s)
    let x (t : Fin r) (i : Fin a) := q (t,.inl i)
    let y (t : Fin r) (j : Fin b) := q (t,.inr (.inl j))
    let z (t : Fin r) (k : Fin n) := q (t,.inr (.inr k))
    ∀ F : Fin r → Fin a × Fin b → K,
      (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*F t ij=0) →
      (∀ t i, ∑ j, y t j*F t (i,j)=0) → (∀ t j, ∑ i, x t i*F t (i,j)=0) →
      (∀ v : Fin r → K, (∀ k, ∑ t, v t*z t k=0) → ∑ t, v t • F t=0) → F=0 :=
  (CriticalLastSlice.TwoPlanes.witness_iff_normals enough).mp
    (tangent ha gap size exception level enough fit)

end CriticalLastSlice.TwoPlanes.Cross

namespace CriticalLastSlice.TwoPlanes.Cross

/-- The full rank level one below (a−1)(b−1) is attained at every eligible
third dimension when b exceeds a(2a−1). -/
theorem generic_rank_of_long {a b c r : ℕ} (ha : 3≤a) (long : a*(2*a-1)<b)
    (hbc : b≤c+1) (level : r+1=(a-1)*(b-1)) (count : r=a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)) :
    Arxiv.«0805.3777».IsGenericRank [a,b,c+1] r := by
  have gap := (long_conditions ha long).1
  exact CriticalLastSlice.TwoPlanes.generic_rank_of_witness ha (by omega) hbc count
    (tangent_of_long ha long level count)

end CriticalLastSlice.TwoPlanes.Cross

namespace CriticalLastSlice.TwoPlanes.Cross

/-- The endpoint b=a(2a−1) has even a+b. Thus the full normal level is
covered from that second dimension onward, inclusively. -/
theorem tangent_tail {a b c r : ℕ} (ha : 3≤a) (long : a*(2*a-1)≤b)
    (level : r+1=(a-1)*(b-1)) (count : r=a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)) :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin (c+1) → ℂ,
      ∀ T : Fin a → Fin b → Fin (c+1) → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin (c+1) → ℂ, ∀ i j k,
          T i j k=∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  rcases lt_or_eq_of_le long with gt | eq
  · exact tangent_of_long ha gt level count
  · have big : a*4≤b := eq ▸ Nat.mul_le_mul_left a (show 4≤2*a-1 by omega)
    have even : Even (a+b) := by
      refine ⟨a*a,?_⟩
      have h := congrArg (fun k : ℕ => a*k) (show 2*a-1+1=2*a by omega)
      change a+b=a*a+a*a
      nlinarith only [eq,h]
    exact tangent_of_even ha (by omega) (Or.inr (by omega)) (by omega) even level count

theorem generic_rank_tail {a b c r : ℕ} (ha : 3≤a) (long : a*(2*a-1)≤b)
    (hbc : b≤c+1) (level : r+1=(a-1)*(b-1)) (count : r=a*b*(c+1) ⌈/⌉ (a+b+(c+1)-2)) :
    Arxiv.«0805.3777».IsGenericRank [a,b,c+1] r := by
  have big := (Nat.mul_le_mul_left a (show 3≤2*a-1 by omega)).trans long
  exact CriticalLastSlice.TwoPlanes.generic_rank_of_witness ha (by omega) hbc count
    (tangent_tail ha long level count)

end CriticalLastSlice.TwoPlanes.Cross

namespace CriticalLastSlice.TwoPlanes.Cross

open MvPolynomial

/-- The literal registered H1 conclusion on the complete long rectangular tail. -/
theorem registered_normals_tail {a b n r : ℕ} (ha : 3≤a) (long : a*(2*a-1)≤b) (hn : 0<n)
    (level : r+1=(a-1)*(b-1)) (count : r=a*b*n ⌈/⌉ (a+b+n-2)) :
    let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin n))
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let q (s : V) := algebraMap R K (X s)
    let x (t : Fin r) (i : Fin a) := q (t,.inl i)
    let y (t : Fin r) (j : Fin b) := q (t,.inr (.inl j))
    let z (t : Fin r) (k : Fin n) := q (t,.inr (.inr k))
    ∀ F : Fin r → Fin a × Fin b → K,
      (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*F t ij=0) →
      (∀ t i, ∑ j, y t j*F t (i,j)=0) → (∀ t j, ∑ i, x t i*F t (i,j)=0) →
      (∀ v : Fin r → K, (∀ k, ∑ t, v t*z t k=0) → ∑ t, v t • F t=0) → F=0 := by
  obtain ⟨c,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have big := (Nat.mul_le_mul_left a (show 3≤2*a-1 by omega)).trans long
  obtain ⟨_,enough,_⟩ := CriticalLastSlice.TwoPlanes.relation_budget a b c r ha (by omega) level count
  exact (CriticalLastSlice.TwoPlanes.witness_iff_normals enough).mp (tangent_tail ha long level count)

end CriticalLastSlice.TwoPlanes.Cross

namespace ThreePlaneTail

/-- At the two-normal level n+d=2b, the upper and strict lower
ceiling inequalities are linear in the offset for fixed b. -/
theorem count_iff_offset {b n d : ℕ} (hb : 3 ≤ b) (hd : n+d=2*b) :
    3*b*n ⌈/⌉ (b+n+1) = 2*b-3 ↔
      7*(b+3) ≤ d*(b+3)+18 ∧ d*(b+4)+36 < 10*(b+4) := by
  have hpos : 0 < b+n+1 := by omega
  have ha : 2*b-3+3=2*b := by omega
  have hp : 2*b-4+4=2*b := by omega
  have h₁ := congrArg (fun x : ℕ => x*(b+n+1)) ha
  have h₂ := congrArg (fun x : ℕ => x*(b+n+1)) hp
  have h₃ := congrArg (fun x : ℕ => x*(b+3)) hd
  have h₄ := congrArg (fun x : ℕ => x*(b+4)) hd
  have upper : (3*b*n ⌈/⌉ (b+n+1) ≤ 2*b-3) ↔ 7*(b+3) ≤ d*(b+3)+18 := by
    rw [ceilDiv_le_iff_le_mul hpos]
    constructor <;> intro h <;> nlinarith only [h,h₁,h₃]
  have lower : (3*b*n ⌈/⌉ (b+n+1) ≤ 2*b-4) ↔ 10*(b+4) ≤ d*(b+4)+36 := by
    rw [ceilDiv_le_iff_le_mul hpos]
    constructor <;> intro h <;> nlinarith only [h,h₂,h₄]
  omega

/-- Precisely the third dimensions in the strict rectangular two-normal stratum
for first dimension three. In particular there are no such formats below b=8. -/
theorem third_sizes {b n : ℕ} (hb : 3 ≤ b) :
    (b+2 ≤ n ∧ n < 2*(b-1) ∧ 3*b*n ⌈/⌉ (b+n+1)=2*b-3) ↔
    (8 ≤ b ∧ b ≤ 15 ∧ n+6=2*b) ∨ (9 ≤ b ∧ n+7=2*b) ∨
      (15 ≤ b ∧ n+8=2*b) ∨ (33 ≤ b ∧ n+9=2*b) := by
  constructor
  · rintro ⟨hn,hstrict,hcount⟩
    let d := 2*b-n
    have hd : n+d=2*b := by dsimp [d]; omega
    obtain ⟨up,low⟩ := (count_iff_offset hb hd).mp hcount
    have eight : 8 ≤ b := by
      by_contra! sm
      interval_cases b <;> omega
    have dlo : 6 ≤ d := by
      by_contra! ht
      have hh := Nat.mul_le_mul_right (b+3) (show d ≤ 5 by omega)
      omega
    have dhi : d ≤ 9 := by
      by_contra! ht
      have hh := Nat.mul_le_mul_right (b+4) (show 10 ≤ d by omega)
      omega
    interval_cases d <;> omega
  · rintro (⟨lo,hi,hd⟩ | ⟨lo,hd⟩ | ⟨lo,hd⟩ | ⟨lo,hd⟩)
    all_goals
      refine ⟨by omega,by omega,(count_iff_offset hb hd).mpr ?_⟩
      constructor <;> omega

end ThreePlaneTail

namespace ThreePlaneTail

/-- Splitting the b axis at its midpoint fits the marked core and the column block
at the full integer capacity floor((b+3)/2), including the endpoint b=8. -/
theorem midpoint_parameters (b : ℕ) (hb : 8 ≤ b) :
    let d := b/2
    let w := b-d
    let m := (b+3)/2
    4 ≤ d ∧ 0 < w ∧ d+w=b ∧ m ≤ (max 3 d-1)+min (min 3 d) (max 3 d-1) ∧
      m ≤ w+1 ∧ (3-1)*(d+w-1)-1=2*b-3 := by
  intro d w m
  have hd : 4 ≤ d := by dsimp [d]; omega
  simp only [max_eq_right (by omega : 3 ≤ d),min_eq_left (by omega : 3 ≤ d),
    min_eq_left (by omega : 3 ≤ d-1)]
  dsimp [d,w,m]
  omega

/-- The only strict rectangular three-slice format whose normal equations
lack room in disjoint batches is (3,14,22), with 25 marked points and three relations. -/
theorem ordinary_capacity_iff {b n : ℕ} (hb : 3 ≤ b) (hn : b+2 ≤ n)
    (region : n < 2*(b-1)) (level : 3*b*n ⌈/⌉ (b+n+1) = 2*b-3) :
    (2*b-3 ≤ (2*b-3-n)*((b+3)/2)) ↔ (b ≠ 14 ∨ n ≠ 22) := by
  rcases (third_sizes hb).mp ⟨hn,region,level⟩ with ⟨lo,hi,off⟩ | band
  · interval_cases b <;> omega
  · have small : n ≤ 2*b-7 := by rcases band with h|h|h <;> omega
    have slots : 4 ≤ 2*b-3-n := by omega
    have four : 2*b-3 ≤ 4*((b+3)/2) := by omega
    have hit := four.trans (Nat.mul_le_mul_right ((b+3)/2) slots)
    exact ⟨fun _ => by omega,fun _ => hit⟩

theorem missing_at_fourteen :
    3*14*22 ⌈/⌉ (3+14+22-2)=25 ∧ 2*25 ≤ (25-22)*(3+14) ∧
      (25-22)*((3+14)/2)<25 := by decide

end ThreePlaneTail

namespace ThreePlaneTail

/-- Any disjoint-batch specialization at full integer capacity yields
a spanning tangent at every admissible level instance except the single leftover. -/
theorem spans_except_fourteen
    {b n : ℕ} (hb : 3 ≤ b) (hn : b+2 ≤ n) (region : n < 2*(b-1))
    (level : 3*b*n ⌈/⌉ (b+n+1)=2*b-3) (remaining : b ≠ 14 ∨ n ≠ 22) :
    let r := 2*b-3
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin 3 → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  classical
  intro r
  have bands := (third_sizes hb).mp ⟨hn,region,level⟩
  have eight : 8 ≤ b := by rcases bands with h|h|h|h <;> omega
  let d := b/2
  let w := b-d
  let m := (b+3)/2
  obtain ⟨hd,hw,side,core,wing,points⟩ := midpoint_parameters b eight
  have one := CriticalLastSlice.TwoPlanes.Cross.rectangular_batch
    (a:=3) (b₁:=d) (w:=w) (m:=m) (by decide) (by omega) (hd.trans (le_max_right 3 d)) hw core wing
  change (3-1)*(d+w-1)-1=r at points
  rw [points, show d+w=b from side] at one
  obtain ⟨first,X,Y,ind⟩ := one
  have cap : r ≤ (r-n)*m := (ordinary_capacity_iff hb hn region level).mpr remaining
  have enough : n ≤ r := by dsimp only [r]; omega
  obtain ⟨label,onto,bound⟩ := LastSliceBatch.balanced_partition (Nat.sub_le r n) cap
  have fit (g : Fin (r-n)) :
      Fintype.card {t : Fin r // label t=g} ≤ Fintype.card (Fin m) := by
    simpa only [Fintype.card_fin] using bound g
  obtain ⟨x,y,direct⟩ := LastSliceBatch.common_small_fibers first label fit ⟨X,Y,ind⟩
  have hit := LastSliceBatch.spans_of_ragged_independence label onto x y direct
  rw [Fintype.card_fin r,Fintype.card_fin (r-n),show r-(r-n)=n by omega] at hit
  exact hit

end ThreePlaneTail

namespace ThreePlaneTail

open Arxiv.«0805.3777» MvPolynomial

/-- One numerical rectangle suffices for every registered three-slice format. -/
theorem witnesses_of_fourteen
    (fourteen : ∃ x : Fin 25 → Fin 3 → ℂ, ∃ y : Fin 25 → Fin 14 → ℂ, ∃ z : Fin 25 → Fin 22 → ℂ,
      ∀ T : Fin 3 → Fin 14 → Fin 22 → ℂ, ∃ u : Fin 25 → Fin 3 → ℂ,
      ∃ v : Fin 25 → Fin 14 → ℂ, ∃ w : Fin 25 → Fin 22 → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)))
    {b n : ℕ} (hb : 3 ≤ b) (hn : b+2 ≤ n) (region : n < 2*(b-1))
    (level : 3*b*n ⌈/⌉ (b+n+1) = 2*b-3) :
    let r := 2*b-3
    ∃ x : Fin r → Fin 3 → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin 3 → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin 3 → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  by_cases h : b=14 ∧ n=22
  · obtain ⟨rfl,rfl⟩ := h
    exact fourteen
  · exact spans_except_fourteen hb hn region level (by omega)

/-- The full three-slice normal condition at this level is equivalent to one
finite tangent witness, with no unverified arithmetic or rank premise. -/
theorem registered_three_iff_fourteen :
    (∀ b c : ℕ, 3 ≤ b → b < c → c+1 < 2*(b-1) →
      let n := c+1
      let r := 3*b*n ⌈/⌉ (3+b+n-2)
      r+1=2*(b-1) →
      let V := Fin r × (Fin 3 ⊕ (Fin b ⊕ Fin n))
      let R := MvPolynomial V ℂ
      let K := FractionRing R
      let q (s : V) := algebraMap R K (X s)
      let x (t : Fin r) (i : Fin 3) := q (t,.inl i)
      let y (t : Fin r) (j : Fin b) := q (t,.inr (.inl j))
      let z (t : Fin r) (k : Fin n) := q (t,.inr (.inr k))
      ∀ F : Fin r → Fin 3 × Fin b → K,
        (∀ t s, ∑ ij, (x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j, y t j*F t (i,j)=0) → (∀ t j, ∑ i, x t i*F t (i,j)=0) →
        (∀ v : Fin r → K, (∀ k, ∑ t, v t*z t k=0) → ∑ t,v t • F t=0) → F=0) ↔
    ∃ x : Fin 25 → Fin 3 → ℂ, ∃ y : Fin 25 → Fin 14 → ℂ, ∃ z : Fin 25 → Fin 22 → ℂ,
      ∀ T : Fin 3 → Fin 14 → Fin 22 → ℂ, ∃ u : Fin 25 → Fin 3 → ℂ,
      ∃ v : Fin 25 → Fin 14 → ℂ, ∃ w : Fin 25 → Fin 22 → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  constructor
  · intro normal
    exact (CriticalLastSlice.TwoPlanes.witness_iff_normals (a:=3) (b:=14) (n:=22) (r:=25)
      (by decide)).mpr (normal 14 21 (by decide) (by decide) (by decide) (by decide))
  · intro fourteen b c hb hc region n r level
    have count : r=2*b-3 := by omega
    have formula : 3*b*n ⌈/⌉ (b+n+1)=2*b-3 := by
      simpa only [r,show 3+b+n-2=b+n+1 by omega] using count
    have wit := witnesses_of_fourteen fourteen hb (n:=n) (by dsimp [n]; omega) region formula
    apply (CriticalLastSlice.TwoPlanes.witness_iff_normals (a:=3) (b:=b) (n:=n) (r:=r)
      (by dsimp [n]; omega)).mp
    rwa [count]

theorem generic_rank_except_fourteen {b n : ℕ} (hb : 3 ≤ b) (hn : b+2 ≤ n)
    (region : n < 2*(b-1)) (level : 3*b*n ⌈/⌉ (b+n+1)=2*b-3) (off : b ≠ 14 ∨ n ≠ 22) :
    IsGenericRank [3,b,n] (2*b-3) := by
  apply CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) hb (by omega) _
    (spans_except_fourteen hb hn region level off)
  simpa only [show 3+b+n-2=b+n+1 by omega] using level.symm

end ThreePlaneTail

namespace CriticalLastSlice.CyclicFlow

/-- On each orbit of a finite group translation, a harmonic function to a
characteristic-zero field is constant. -/
theorem harmonic_shift {G K : Type*} [AddGroup G] [Finite G] [Field K] [CharZero K]
    (h : G) (f : G → K) (harmonic : ∀ i, f (i+h)+f (i-h)=2*f i) (i : G) :
    f (i+h) = f i := by
  let u (m : ℕ) := f (i+m • h)
  have recurrence (m : ℕ) : u (m+2)+u m=2*u (m+1) := by
    have next : i+(m+1) • h+h=i+(m+2) • h := by rw [succ_nsmul h (m+1),add_assoc]
    have prev : i+(m+1) • h-h=i+m • h := by rw [succ_nsmul,← add_assoc,add_sub_cancel_right]
    have eq := harmonic (i+(m+1) • h)
    rwa [next,prev] at eq
  have affine (m : ℕ) : u m = u 0 + (m:K)*(u 1-u 0) := by
    induction m using Nat.twoStepInduction with
    | zero => simp
    | one => simp
    | more m hm hs =>
      have eq := recurrence m
      rw [hm,hs] at eq
      push_cast at eq ⊢
      linear_combination eq
  have period : u (addOrderOf h) = u 0 := by simp [u]
  have slope := affine (addOrderOf h)
  rw [period] at slope
  have zero : (addOrderOf h : K)*(u 1-u 0)=0 := by linear_combination -slope
  have positive : (addOrderOf h : K) ≠ 0 := Nat.cast_ne_zero.mpr (addOrderOf_pos h).ne'
  have same := sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left positive)
  simpa [u] using same

/-- One translation by 1 generates all residue indices. -/
theorem constant_of_shift_one {k : ℕ} [NeZero k] {S : Type*} (f : ZMod k → S)
    (step : ∀ i, f (i+1)=f i) (i : ZMod k) : f i=f 0 := by
  have all (m : ℕ) : f (m : ZMod k)=f 0 := by
    induction m with
    | zero => simp
    | succ m prev => rw [Nat.cast_succ,step,prev]
  simpa only [ZMod.natCast_zmod_val] using all i.val

/-- Twice the inverse of two is one, including for composite odd moduli. -/
theorem inverse_two_add_self {k : ℕ} (odd : Odd k) : (2 : ZMod k)⁻¹+(2 : ZMod k)⁻¹=1 := by
  rw [← two_mul]
  exact ZMod.coe_mul_inv_eq_one 2 (Nat.coprime_two_left.mpr odd)

/-- A half-step generates the cyclic index group. -/
theorem half_generates {k : ℕ} [NeZero k] (h : ZMod k) (half : h+h=1) (i : ZMod k) :
    ∃ m : ℕ, m • h=i := by
  refine ⟨2*i.val,?_⟩
  rw [mul_nsmul,two_nsmul,half]
  simp

theorem constant_of_half_shift {k : ℕ} [NeZero k] {S : Type*} (h : ZMod k) (half : h+h=1)
    (f : ZMod k → S) (step : ∀ i, f (i+h)=f i) (i : ZMod k) : f i=f 0 := by
  apply constant_of_shift_one f _ i
  intro j
  calc
    f (j+1) = f ((j+h)+h) := by rw [add_assoc,half]
    _ = f (j+h) := step _
    _ = f j := step _

end CriticalLastSlice.CyclicFlow

namespace CriticalLastSlice.CyclicFlow

/-- Subtract the right-vertex equation from the next color equation and
the left-vertex equation from the current color equation. -/
theorem middle_harmonic {k : ℕ} {K : Type*} [CommRing K] (h : ZMod k) (half : h+h=1)
    (A B C : ZMod k → K) (left : ∀ i, A i+B i+C i=0)
    (right : ∀ i, A i+B (i-1)+C (i-2)=0) (color : ∀ i, A i+B (i-h)+C (i-1)=0)
    (j : ZMod k) : B (j+h)+B (j-h)=2*B j := by
  have prev : j+1-2=j-1 := by ring
  have mid : j+1-h=j+h := by rw [← half]; abel
  have nextRight := right (j+1)
  have nextColor := color (j+1)
  rw [add_sub_cancel_right,prev] at nextRight
  rw [add_sub_cancel_right,mid] at nextColor
  linear_combination nextColor - nextRight + color j - left j

/-- The three cyclic edge classes carry constant weights; their three
constants sum to zero. -/
theorem weights_constant {k : ℕ} [NeZero k] {K : Type*} [Field K] [CharZero K]
    (h : ZMod k) (half : h+h=1) (A B C : ZMod k → K)
    (left : ∀ i, A i+B i+C i=0) (right : ∀ i, A i+B (i-1)+C (i-2)=0)
    (color : ∀ i, A i+B (i-h)+C (i-1)=0) :
    (∀ i, A i=A 0 ∧ B i=B 0 ∧ C i=C 0) ∧ A 0+B 0+C 0=0 := by
  have harmonic := middle_harmonic h half A B C left right color
  have bconst := constant_of_half_shift h half B (harmonic_shift h B harmonic)
  have cstep (j : ZMod k) : C (j+1)=C j := by
    have e₁ := left (j+1)
    have e₂ := color (j+1)
    rw [bconst (j+1)] at e₁
    rw [bconst (j+1-h),add_sub_cancel_right] at e₂
    linear_combination e₁ - e₂
  have cconst := constant_of_shift_one C cstep
  refine ⟨fun i => ⟨?_,bconst i,cconst i⟩,left 0⟩
  have e := left i
  rw [bconst i,cconst i] at e
  linear_combination e - left 0

theorem profiles_iff_constants {k : ℕ} [NeZero k] {K : Type*} [Field K] [CharZero K]
    (h : ZMod k) (half : h+h=1) (A B C : ZMod k → K) :
    ((∀ i, A i+B i+C i=0) ∧ (∀ i, A i+B (i-1)+C (i-2)=0) ∧
      (∀ i, A i+B (i-h)+C (i-1)=0)) ↔
    (∀ i, A i=A 0 ∧ B i=B 0 ∧ C i=C 0) ∧ A 0+B 0+C 0=0 := by
  constructor
  · rintro ⟨left,right,color⟩
    exact weights_constant h half A B C left right color
  · rintro ⟨constant,zero⟩
    have all (i j l : ZMod k) : A i+B j+C l=0 := by
      rw [(constant i).1,(constant j).2.1,(constant l).2.2]
      exact zero
    exact ⟨fun i => all i i i, fun i => all i (i-1) (i-2), fun i => all i (i-h) (i-1)⟩

/-- The usual odd-modulus form with the half-step written as `2⁻¹`. -/
theorem weights_constant_odd {k : ℕ} {K : Type*} [Field K] [CharZero K] (odd : Odd k)
    (A B C : ZMod k → K) (left : ∀ i, A i+B i+C i=0)
    (right : ∀ i, A i+B (i-1)+C (i-2)=0)
    (color : ∀ i, A i+B (i-(2 : ZMod k)⁻¹)+C (i-1)=0) :
    (∀ i, A i=A 0 ∧ B i=B 0 ∧ C i=C 0) ∧ A 0+B 0+C 0=0 := by
  let _ : NeZero k := ⟨by rintro rfl; exact Nat.not_odd_zero odd⟩
  exact weights_constant _ (inverse_two_add_self odd) A B C left right color

end CriticalLastSlice.CyclicFlow

namespace CriticalLastSlice.CyclicFlow

/-- In offset class `d`, the edge starting at `i` has color `j+j`
precisely when `i=j-h*d`. -/
theorem color_eq_iff {k : ℕ} (h : ZMod k) (half : h+h=1) (i d j : ZMod k) :
    i+(i+d)=j+j ↔ i=j-h*d := by
  have inv : 2*h=1 := (two_mul h).trans half
  constructor
  · intro he
    linear_combination h*he + (j-i)*inv
  · rintro rfl
    linear_combination -d*inv

/-- Sum the three offset classes on a prescribed right vertex. -/
theorem right_vertex_sum {k : ℕ} [NeZero k] {S : Type*} [AddCommMonoid S]
    (A B C : ZMod k → S) (j : ZMod k) :
    (∑ i : ZMod k, ((if i=j then A i else 0) + (if i+1=j then B i else 0) +
      (if i+2=j then C i else 0))) = A j+B (j-1)+C (j-2) := by
  have one (i : ZMod k) : i+1=j ↔ i=j-1 := eq_sub_iff_add_eq.symm
  have two (i : ZMod k) : i+2=j ↔ i=j-2 := eq_sub_iff_add_eq.symm
  simp [one,two,Finset.sum_add_distrib]

/-- The three edges of color `j+j` start at `j`, `j-h` and `j-1`. -/
theorem color_sum {k : ℕ} [NeZero k] {S : Type*} [AddCommMonoid S]
    (h : ZMod k) (half : h+h=1) (A B C : ZMod k → S) (j : ZMod k) :
    (∑ i : ZMod k, ((if i+i=j+j then A i else 0) + (if i+(i+1)=j+j then B i else 0) +
      (if i+(i+2)=j+j then C i else 0))) = A j+B (j-h)+C (j-1) := by
  have zero (i : ZMod k) : i+i=j+j ↔ i=j := by simpa using color_eq_iff h half i 0 j
  have one (i : ZMod k) : i+(i+1)=j+j ↔ i=j-h := by simpa using color_eq_iff h half i 1 j
  have two (i : ZMod k) : i+(i+2)=j+j ↔ i=j-1 := by simpa only [mul_two,half] using color_eq_iff h half i 2 j
  simp only [zero,one,two,Finset.sum_add_distrib]
  simp

theorem color_sum_at {k : ℕ} [NeZero k] {S : Type*} [AddCommMonoid S]
    (h : ZMod k) (half : h+h=1) (A B C : ZMod k → S) (s : ZMod k) :
    (∑ i : ZMod k, ((if i+i=s then A i else 0) + (if i+(i+1)=s then B i else 0) +
      (if i+(i+2)=s then C i else 0))) = A (h*s)+B (h*s-h)+C (h*s-1) := by
  have double : h*s+h*s=s := by rw [← add_mul,half,one_mul]
  simpa only [double] using color_sum h half A B C (h*s)

/-- Zero left, right and color sums characterize the two-dimensional space
of constant offset-class weights whose constants sum to zero. -/
theorem fiber_sums_iff_constants {k : ℕ} [NeZero k] {K : Type*} [Field K] [CharZero K]
    (h : ZMod k) (half : h+h=1) (A B C : ZMod k → K) :
    ((∀ i, A i+B i+C i=0) ∧
      (∀ j, (∑ i : ZMod k, ((if i=j then A i else 0) + (if i+1=j then B i else 0) +
        (if i+2=j then C i else 0)))=0) ∧
      (∀ s, (∑ i : ZMod k, ((if i+i=s then A i else 0) + (if i+(i+1)=s then B i else 0) +
        (if i+(i+2)=s then C i else 0)))=0)) ↔
    (∀ i, A i=A 0 ∧ B i=B 0 ∧ C i=C 0) ∧ A 0+B 0+C 0=0 := by
  constructor
  · rintro ⟨left,right,color⟩
    exact weights_constant h half A B C left
      (fun j => (right_vertex_sum A B C j).symm.trans (right j))
      (fun j => (color_sum h half A B C j).symm.trans (color (j+j)))
  · intro constants
    obtain ⟨left,right,color⟩ := (profiles_iff_constants h half A B C).mpr constants
    exact ⟨left,fun j => (right_vertex_sum A B C j).trans (right j),
      fun s => (color_sum_at h half A B C s).trans (color (h*s))⟩

end CriticalLastSlice.CyclicFlow

namespace CriticalLastSlice.TwoPlanes

/-- The standard cyclic product character factors along the two vertex labels. -/
theorem character_add {k : ℕ} [NeZero k] (t s u : ZMod k) :
    ZMod.stdAddChar (t*(s+u)) = ZMod.stdAddChar (t*s)*ZMod.stdAddChar (t*u) := by
  rw [mul_add, AddChar.map_add_eq_mul]

theorem character_ne_zero {k : ℕ} [NeZero k] (t s : ZMod k) : ZMod.stdAddChar (t*s) ≠ 0 :=
  (AddChar.val_isUnit _ _).ne_zero

theorem character_inv {k : ℕ} [NeZero k] (t s : ZMod k) :
    (ZMod.stdAddChar (t*s))⁻¹ = ZMod.stdAddChar (t*(-s)) := by
  rw [mul_neg, AddChar.map_neg_eq_inv]

/-- Vanishing of all cyclic Fourier coefficients forces the vector to vanish. -/
theorem character_separates {k : ℕ} [NeZero k] (v : ZMod k → ℂ)
    (h : ∀ s, ∑ t, ZMod.stdAddChar (t*s)*v t = 0) : v = 0 := by
  apply ZMod.dft.injective
  rw [map_zero]
  funext s
  rw [ZMod.dft_apply]
  simpa only [mul_neg,smul_eq_mul,Pi.zero_apply] using h (-s)

theorem character_inv_separates {k : ℕ} [NeZero k] (v : ZMod k → ℂ)
    (h : ∀ s, ∑ t, (ZMod.stdAddChar (t*s))⁻¹*v t = 0) : v = 0 := by
  apply character_separates v
  intro s
  simpa only [character_inv,neg_neg] using h (-s)

/-- Testing every tagged product is equivalent to zero sums on each color class. -/
theorem character_color_sums_iff {k : ℕ} [NeZero k] {E : Type*} [Fintype E]
    (c : E → ZMod k) (w : E → ℂ) :
    (∀ t : ZMod k, ∑ e, ZMod.stdAddChar (t*c e)*w e = 0) ↔
      ∀ s : ZMod k, (∑ e, if c e = s then w e else 0) = 0 := by
  classical
  let v (s : ZMod k) := ∑ e, if c e = s then w e else 0
  have grouped (t : ZMod k) : (∑ s, ZMod.stdAddChar (s*t)*v s) =
      ∑ e, ZMod.stdAddChar (t*c e)*w e := by
    simp only [v,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp [mul_ite,mul_comm (c e) t]
  constructor
  · intro h
    have zero := character_separates v (fun t => (grouped t).trans (h t))
    exact fun s => congrFun zero s
  · intro h t
    rw [← grouped]
    exact Finset.sum_eq_zero fun s _ => by rw [show v s = 0 from h s,mul_zero]

/-- Each color's samples determine the common normal space. A relation between
inverse-character translates first vanishes on that fiber, then on every edge.
Fourier inversion at any edge separates its coefficients by tag. -/
theorem character_planes_direct {k : ℕ} [NeZero k] {E : Type*} (color : E → ZMod k)
    (S : Submodule ℂ (E → ℂ))
    (fiber : ∀ (s : ZMod k) (f : E → ℂ), f ∈ S → (∀ e, color e = s → f e = 0) → f = 0)
    (F : ZMod k → E → ℂ) (member : ∀ t, F t ∈ S)
    (hsum : ∀ e, ∑ t, (ZMod.stdAddChar (t*color e))⁻¹*F t e = 0) : F = 0 := by
  classical
  let G (s : ZMod k) : E → ℂ := ∑ t, (ZMod.stdAddChar (t*s))⁻¹ • F t
  have hmem (s : ZMod k) : G s ∈ S := S.sum_mem fun t _ => S.smul_mem _ (member t)
  have evalG (s : ZMod k) (e : E) : G s e = ∑ t, (ZMod.stdAddChar (t*s))⁻¹*F t e := by
    simp [G,Finset.sum_apply]
  have zero (s : ZMod k) : G s = 0 := by
    apply fiber s _ (hmem s)
    intro e h
    rw [evalG,← h]
    exact hsum e
  funext t e
  have he := character_inv_separates (fun u => F u e) (fun s => (evalG s e).symm.trans (congrFun (zero s) e))
  exact congrFun he t

/-- The normal in the original sampled coordinates is recovered by division
by the tagged edge character, which never vanishes. -/
theorem character_tagged_normals_zero {k : ℕ} [NeZero k] {E : Type*} (color : E → ZMod k)
    (S : Submodule ℂ (E → ℂ))
    (fiber : ∀ (s : ZMod k) (f : E → ℂ), f ∈ S → (∀ e, color e = s → f e = 0) → f = 0)
    (F : ZMod k → E → ℂ) (member : ∀ t, (fun e => ZMod.stdAddChar (t*color e)*F t e) ∈ S)
    (hsum : ∀ e, ∑ t, F t e = 0) : F = 0 := by
  let G (t : ZMod k) (e : E) := ZMod.stdAddChar (t*color e)*F t e
  have relation (e : E) : ∑ t, (ZMod.stdAddChar (t*color e))⁻¹*G t e = 0 := by
    simpa only [G,← mul_assoc,inv_mul_cancel₀ (character_ne_zero _ _),one_mul] using hsum e
  have hG := character_planes_direct color S fiber G member relation
  funext t e
  have z : ZMod.stdAddChar (t*color e)*F t e = 0 := congrFun (congrFun hG t) e
  exact (mul_eq_zero.mp z).resolve_left (character_ne_zero _ _)

/-- A color seeing every displacement detects functions constant on each displacement. -/
theorem character_fiber_detects {k : ℕ} {E D : Type*} (color : E → ZMod k) (disp : E → D)
    (s : ZMod k) (hit : ∀ i, ∃ e : E, color e = s ∧ disp e = i)
    (f : E → ℂ) (constant : ∀ e j, disp e = disp j → f e = f j)
    (zero : ∀ e, color e = s → f e = 0) : f = 0 := by
  funext e
  obtain ⟨j,hc,hd⟩ := hit (disp e)
  exact (constant e j hd.symm).trans (zero j hc)

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- Twisting one marked normal by its edge character removes the row and
column weights. The remaining product samples impose all color balances. -/
theorem character_twisted_balances {k : ℕ} [NeZero k] {E I J : Type*}
    [Fintype E] [DecidableEq I] [DecidableEq J] (left : E → I) (right : E → J)
    (a : I → ZMod k) (b : J → ZMod k) (tag : ZMod k) (F : E → ℂ)
    (rows : ∀ i : I, (∑ e, if left e = i then ZMod.stdAddChar (tag*b (right e))*F e else 0) = 0)
    (cols : ∀ j : J, (∑ e, if right e = j then ZMod.stdAddChar (tag*a (left e))*F e else 0) = 0)
    (marks : ∀ t : ZMod k, ∑ e, (ZMod.stdAddChar (t*a (left e))*
      ZMod.stdAddChar (t*b (right e)))*F e = 0) :
    let c := fun e => a (left e)+b (right e)
    let G := fun e => ZMod.stdAddChar (tag*c e)*F e
    (∀ i, (∑ e, if left e = i then G e else 0) = 0) ∧
    (∀ j, (∑ e, if right e = j then G e else 0) = 0) ∧
    (∀ s, (∑ e, if c e = s then G e else 0) = 0) := by
  dsimp only
  let c (e : E) := a (left e)+b (right e)
  have colors := (character_color_sums_iff c F).mp (fun t => by simpa only [c,character_add] using marks t)
  refine ⟨?_,?_,?_⟩
  · intro i
    have h := congrArg (fun z : ℂ => ZMod.stdAddChar (tag*a i)*z) (rows i)
    simp only [Finset.mul_sum,mul_zero] at h
    refine Eq.trans ?_ h
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : left e = i <;> simp [he,character_add,mul_assoc]
  · intro j
    have h := congrArg (fun z : ℂ => ZMod.stdAddChar (tag*b j)*z) (cols j)
    simp only [Finset.mul_sum,mul_zero] at h
    refine Eq.trans ?_ h
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : right e = j <;> simp [he,character_add,mul_assoc,mul_left_comm]
  · intro s
    have h := congrArg (fun z : ℂ => ZMod.stdAddChar (tag*s)*z) (colors s)
    simp only [Finset.mul_sum,mul_zero] at h
    change (∑ e, if c e = s then ZMod.stdAddChar (tag*c e)*F e else 0) = 0
    refine Eq.trans ?_ h
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : c e = s <;> simp [he]

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- Sample all nonedges by their coordinate products and sample the graph by
the k cyclic products. If the row, column and color balances are detected
on each color fiber, the k marked normal spaces sum directly. -/
theorem bipartite_character_batch {k : ℕ} [NeZero k] {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (edge : A × B → Prop) (a : A → ZMod k) (b : B → ZMod k)
    (fiber : ∀ (s : ZMod k) (w : A × B → ℂ), (∀ ij, ¬edge ij → w ij = 0) →
      (∀ i, ∑ j, w (i,j) = 0) → (∀ j, ∑ i, w (i,j) = 0) →
      (∀ c : ZMod k, (∑ ij : A × B, if a ij.1+b ij.2 = c then w ij else 0) = 0) →
      (∀ ij, a ij.1+b ij.2 = s → w ij = 0) → w = 0) :
    let X : ({ij : A × B // ¬edge ij} ⊕ ZMod k) → A → ℂ :=
      Sum.elim (fun p i => if i=p.val.1 then 1 else 0) (fun t i => ZMod.stdAddChar (t*a i))
    let Y : ({ij : A × B // ¬edge ij} ⊕ ZMod k) → B → ℂ :=
      Sum.elim (fun p j => if j=p.val.2 then 1 else 0) (fun t j => ZMod.stdAddChar (t*b j))
    ∀ F : ZMod k → A × B → ℂ, (∀ t s, ∑ ij : A × B, (X s ij.1*Y s ij.2)*F t ij = 0) →
      (∀ t i, ∑ j, Y (.inr t) j*F t (i,j) = 0) → (∀ t j, ∑ i, X (.inr t) i*F t (i,j) = 0) →
      (∀ ij, ∑ t, F t ij = 0) → F = 0 := by
  classical
  intro X Y F products rows cols relation
  let color (p : A × B) := a p.1+b p.2
  let support (s : ZMod k) := (Finset.univ : Finset (A × B)).filter (fun e => color e=s)
  let S : Submodule ℂ (A × B → ℂ) := {
    carrier := {w | (∀ ij, ¬edge ij → w ij = 0) ∧
      (∀ i, ∑ j, w (i,j) = 0) ∧ (∀ j, ∑ i, w (i,j) = 0) ∧
      (∀ s, ∑ ij ∈ support s, w ij = 0)}
    zero_mem' := by simp
    add_mem' := by
      intro f g hf hg
      exact ⟨fun e he => by simp only [Pi.add_apply,hf.1 e he,hg.1 e he,add_zero],
        fun i => by simp only [Pi.add_apply,Finset.sum_add_distrib,hf.2.1 i,hg.2.1 i,add_zero],
        fun j => by simp only [Pi.add_apply,Finset.sum_add_distrib,hf.2.2.1 j,hg.2.2.1 j,add_zero],
        fun s => by simp only [Pi.add_apply,Finset.sum_add_distrib,hf.2.2.2 s,hg.2.2.2 s,add_zero]⟩
    smul_mem' := by
      intro t f hf
      exact ⟨fun e he => by simp only [Pi.smul_apply,smul_eq_mul,hf.1 e he,mul_zero],
        fun i => by simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,hf.2.1 i,mul_zero],
        fun j => by simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,hf.2.2.1 j,mul_zero],
        fun s => by simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,hf.2.2.2 s,mul_zero]⟩ }
  have zeros (t : ZMod k) (e : A × B) (he : ¬edge e) : F t e = 0 := by
    obtain ⟨i,j⟩ := e
    have h := products t (Sum.inl ⟨(i,j),he⟩)
    simpa [X,Y,Fintype.sum_prod_type,ite_mul,mul_ite,Finset.sum_ite_irrel] using h
  apply character_tagged_normals_zero color S _ F _ relation
  · intro s w hw seen
    exact fiber s w hw.1 hw.2.1 hw.2.2.1 (fun c => by
      simpa only [support,Finset.sum_filter,color] using hw.2.2.2 c) seen
  · intro t
    have weightedRow (i : A) : (∑ e : A × B, if e.1 = i then ZMod.stdAddChar (t*b e.2)*F t e else 0) = 0 := by
      simpa [Fintype.sum_prod_type,Finset.sum_ite_irrel,Y] using rows t i
    have weightedCol (j : B) : (∑ e : A × B, if e.2 = j then ZMod.stdAddChar (t*a e.1)*F t e else 0) = 0 := by
      simpa [Fintype.sum_prod_type,X] using cols t j
    have bal := character_twisted_balances Prod.fst Prod.snd a b t (F t) weightedRow weightedCol
      (fun v => products t (.inr v))
    refine ⟨fun e h => by simp only [zeros t e h,mul_zero],?_,?_,?_⟩
    · intro i
      simpa [Fintype.sum_prod_type,Finset.sum_ite_irrel,color] using bal.1 i
    · intro j
      simpa [Fintype.sum_prod_type,color] using bal.2.1 j
    · intro s
      simpa only [support,Finset.sum_filter,color] using bal.2.2 s

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- A nonedge in the three-diagonal cyclic graph is a row and a difference
outside the three-element set {0,1,2}. -/
theorem square_nonedge_card (k : ℕ) [NeZero k] (hk : 3 ≤ k) :
    Fintype.card {ij : ZMod k × ZMod k // ¬ (ij.2=ij.1 ∨ ij.2=ij.1+1 ∨ ij.2=ij.1+2)} =
      k*(k-3) := by
  classical
  let ban : Finset (ZMod k) := {0,1,2}
  have distinct (u v : ℕ) (hu : u<k) (hv : v<k) (hne : u ≠ v) :
      (u : ZMod k) ≠ (v : ZMod k) := by
    intro h
    exact hne ((ZMod.val_natCast_of_lt hu).symm.trans ((congrArg ZMod.val h).trans (ZMod.val_natCast_of_lt hv)))
  have h01 : (0 : ZMod k) ≠ 1 := by simpa only [Nat.cast_zero,Nat.cast_one] using distinct 0 1 (by omega) (by omega) (by decide)
  have h02 : (0 : ZMod k) ≠ 2 := by simpa only [Nat.cast_zero,Nat.cast_ofNat] using distinct 0 2 (by omega) (by omega) (by decide)
  have h12 : (1 : ZMod k) ≠ 2 := by simpa only [Nat.cast_one,Nat.cast_ofNat] using distinct 1 2 (by omega) (by omega) (by decide)
  have size : ban.card = 3 := by simp [ban,h01,h02,h12]
  let rem := {j : ZMod k // j ∈ banᶜ}
  have convert (i j : ZMod k) :
      (j-i ∈ banᶜ) ↔ ¬(j=i ∨ j=i+1 ∨ j=i+2) := by
    have shift (c : ZMod k) : j-i=c ↔ j=i+c := by rw [sub_eq_iff_eq_add,add_comm c i]
    simp only [ban,Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton,shift,add_zero]
  let e : {ij : ZMod k × ZMod k // ¬(ij.2=ij.1 ∨ ij.2=ij.1+1 ∨ ij.2=ij.1+2)} ≃ ZMod k × rem :=
    { toFun := fun p => ⟨p.val.1,⟨p.val.2-p.val.1,(convert _ _).mpr p.property⟩⟩
      invFun := fun z => ⟨(z.1,z.1+z.2.val),(convert _ _).mp (by simp)⟩
      left_inv := by
        rintro ⟨⟨i,j⟩,h⟩
        apply Subtype.ext
        exact Prod.ext rfl (by dsimp; abel)
      right_inv := by
        rintro ⟨i,j⟩
        exact Prod.ext rfl (Subtype.ext (by dsimp; abel)) }
  have rest : Fintype.card rem=k-3 := by
    change Fintype.card (↥(banᶜ) : Type) = _
    rw [Fintype.card_coe,Finset.card_compl,size,ZMod.card]
  rw [Fintype.card_congr e,Fintype.card_prod,ZMod.card,rest]

theorem square_point_card (k : ℕ) [NeZero k] (hk : 3 ≤ k) :
    Fintype.card ({ij : ZMod k × ZMod k // ¬(ij.2=ij.1 ∨ ij.2=ij.1+1 ∨ ij.2=ij.1+2)} ⊕ ZMod k) =
      k*k-2*k := by
  rw [Fintype.card_sum,square_nonedge_card k hk,ZMod.card]
  have eq := congrArg (fun t => k*t) (Nat.sub_add_cancel hk)
  rw [Nat.mul_add] at eq
  omega

theorem square_marked_card (k : ℕ) [NeZero k] :
    let P := {ij : ZMod k × ZMod k // ¬(ij.2=ij.1 ∨ ij.2=ij.1+1 ∨ ij.2=ij.1+2)} ⊕ ZMod k
    let first : ZMod k ↪ P := Function.Embedding.inr
    (Finset.univ.map first).card = k := by
  intro P first
  rw [Finset.card_map,Finset.card_univ,ZMod.card]

/-- On the penultimate critical level the cubic count has precisely the
number of points in the three-diagonal graph. -/
theorem square_card_of_level {k r : ℕ} (hk : 3 ≤ k) (level : r+1=(k-1)*(k-1)) :
    r=k*k-2*k := by
  have h : k-1+1=k := Nat.sub_add_cancel (by omega)
  have z : k*k = (k-1)*(k-1)+2*(k-1)+1 := by
    conv_lhs => rw [← h]
    ring
  omega

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- Transport a marked collection of independent normal spaces through
bijections on the total points and both matrix axes. -/
private lemma move_mark {A B P Q A' B' P' : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B'] [Fintype Q]
    (ea : A ≃ A') (eb : B ≃ B') (ep : P ≃ P') (first : Q ↪ P)
    (one : ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ H : Q → A × B → ℂ,
      (∀ t s, ∑ ij : A × B, (x s ij.1*y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, y (first t) j*H t (i,j)=0) →
      (∀ t j, ∑ i, x (first t) i*H t (i,j)=0) → (∑ t, H t)=0 → H=0) :
    ∃ X : P' → A' → ℂ, ∃ Y : P' → B' → ℂ, ∀ H : Q → A' × B' → ℂ,
      (∀ t s, ∑ ij : A' × B', (X s ij.1*Y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, Y (ep (first t)) j*H t (i,j)=0) →
      (∀ t j, ∑ i, X (ep (first t)) i*H t (i,j)=0) → (∑ t, H t)=0 → H=0 := by
  classical
  obtain ⟨x,y,ind⟩ := one
  let X (s : P') (i : A') := x (ep.symm s) (ea.symm i)
  let Y (s : P') (j : B') := y (ep.symm s) (eb.symm j)
  refine ⟨X,Y,?_⟩
  intro H outer row col total
  let pull (t : Q) (ij : A × B) := H t (ea ij.1,eb ij.2)
  have out (t : Q) (s : P) : ∑ ij : A × B, (x s ij.1*y s ij.2)*pull t ij=0 := by
    have h := outer t (ep s)
    rw [← (ea.prodCongr eb).sum_comp] at h
    simpa only [pull,X,Y,Equiv.prodCongr_apply,Prod.map,Equiv.symm_apply_apply] using h
  have rows (t : Q) (i : A) : ∑ j, y (first t) j*pull t (i,j)=0 := by
    have h := row t (ea i)
    rw [← eb.sum_comp] at h
    simpa only [pull,Y,Equiv.symm_apply_apply] using h
  have cols (t : Q) (j : B) : ∑ i, x (first t) i*pull t (i,j)=0 := by
    have h := col t (eb j)
    rw [← ea.sum_comp] at h
    simpa only [pull,X,Equiv.symm_apply_apply] using h
  have trace : ∑ t, pull t=0 := by
    funext ij
    simpa only [Finset.sum_apply,pull,Pi.zero_apply] using congrFun total (ea ij.1,eb ij.2)
  have zero := ind pull out rows cols trace
  funext t ij
  simpa only [pull,Equiv.apply_symm_apply,Prod.mk.eta,Pi.zero_apply] using
    congrFun (congrFun zero t) (ea.symm ij.1,eb.symm ij.2)

end CriticalLastSlice.TwoPlanes


namespace CriticalLastSlice.TwoPlanes

/-- A marked independent family of size m permits w points to span whenever
the w−c batches can be chosen with at most m points apiece. -/
private lemma from_capacity {a b w c m : ℕ} {Q : Type*} [Fintype Q]
    (hq : Fintype.card Q=m) (first : Q ↪ Fin w) (hc : c≤w) (fit : w≤(w-c)*m)
    (one : ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∀ H : Q → Fin a × Fin b → ℂ,
      (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, y (first t) j*H t (i,j)=0) →
      (∀ t j, ∑ i, x (first t) i*H t (i,j)=0) → (∑ t,H t)=0 → H=0) :
    ∃ x : Fin w → Fin a → ℂ, ∃ y : Fin w → Fin b → ℂ, ∃ z : Fin w → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin w → Fin a → ℂ,
        ∃ v : Fin w → Fin b → ℂ, ∃ v' : Fin w → Fin c → ℂ, ∀ i j k,
          T i j k=∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*v' t k)) := by
  classical
  obtain ⟨label,onto,bound⟩ := LastSliceBatch.balanced_partition (Nat.sub_le w c) fit
  have cap (g : Fin (w-c)) : Fintype.card {t : Fin w // label t=g} ≤ Fintype.card Q := hq ▸ bound g
  obtain ⟨x,y,direct⟩ := LastSliceBatch.common_small_fibers first label cap one
  have result := LastSliceBatch.spans_of_ragged_independence label onto x y direct
  rw [Fintype.card_fin w,Fintype.card_fin (w-c),show w-(w-c)=c by omega] at result
  exact result

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

open MvPolynomial Arxiv.«0805.3777»

/-- A marked independent family on arbitrary finite axis and point labels
gives a spanning complex witness as soon as its batch capacity covers all points. -/
theorem spans_from_independent_batch {A B P Q : Type*} [Fintype A] [Fintype B] [Fintype P] [Fintype Q]
    {a b n r : ℕ} (first : Q ↪ P) (ca : Fintype.card A=a) (cb : Fintype.card B=b)
    (cp : Fintype.card P=r) (enough : n≤r) (fit : r ≤ (r-n)*Fintype.card Q)
    (one : ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ H : Q → A × B → ℂ,
      (∀ t s, ∑ ij : A × B, (x s ij.1*y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, y (first t) j*H t (i,j)=0) →
      (∀ t j, ∑ i, x (first t) i*H t (i,j)=0) → (∑ t,H t)=0 → H=0) :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
    ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ,
      ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j l,
        T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*w t l)) := by
  classical
  let ea := (Fintype.equivFin A).trans (finCongr ca)
  let eb := (Fintype.equivFin B).trans (finCongr cb)
  let ep := (Fintype.equivFin P).trans (finCongr cp)
  exact from_capacity rfl (first.trans ep.toEmbedding) enough fit (move_mark ea eb ep first one)

/-- The k marked cyclic points supply batches of size k in the square format. -/
theorem square_spans_of_batch {k n r : ℕ} [NeZero k] (hk : 3 ≤ k)
    (level : r+1=(k-1)*(k-1)) (enough : n≤r) (budget : 2*r≤(r-n)*(2*k)) :
    let P := {ij : ZMod k × ZMod k // ¬(ij.2=ij.1 ∨ ij.2=ij.1+1 ∨ ij.2=ij.1+2)} ⊕ ZMod k
    (∃ x : P → ZMod k → ℂ, ∃ y : P → ZMod k → ℂ, ∀ H : ZMod k → ZMod k × ZMod k → ℂ,
      (∀ t s, ∑ ij : ZMod k × ZMod k, (x s ij.1*y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, y (.inr t) j*H t (i,j)=0) →
      (∀ t j, ∑ i, x (.inr t) i*H t (i,j)=0) → (∑ t,H t)=0 → H=0) →
    ∃ x : Fin r → Fin k → ℂ, ∃ y : Fin r → Fin k → ℂ, ∃ z : Fin r → Fin n → ℂ,
    ∀ T : Fin k → Fin k → Fin n → ℂ, ∃ u : Fin r → Fin k → ℂ,
      ∃ v : Fin r → Fin k → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j l,
        T i j l = ∑ t, (u t i*(y t j*z t l) + x t i*(v t j*z t l) + x t i*(y t j*w t l)) := by
  intro P one
  let first : ZMod k ↪ P := Function.Embedding.inr
  have size : Fintype.card P = r := (square_point_card k hk).trans (square_card_of_level hk level).symm
  have fit : r ≤ (r-n)*Fintype.card (ZMod k) := by
    rw [ZMod.card]
    have eq : (r-n)*(2*k)=2*((r-n)*k) := by ring
    rw [eq] at budget
    omega
  exact spans_from_independent_batch first (ZMod.card k) (ZMod.card k) size enough fit one

/-- The cyclic marked-family assumption gives the catalogue generic rank
at every square format on this level. -/
theorem square_generic_rank_of_batch {k c r : ℕ} [NeZero k]
    (hk : 3 ≤ k) (hkc : k < c) (level : r+1=(k-1)*(k-1))
    (count : r=k*k*(c+1) ⌈/⌉ (k+k+(c+1)-2)) :
    let P := {ij : ZMod k × ZMod k // ¬(ij.2=ij.1 ∨ ij.2=ij.1+1 ∨ ij.2=ij.1+2)} ⊕ ZMod k
    (∃ x : P → ZMod k → ℂ, ∃ y : P → ZMod k → ℂ, ∀ H : ZMod k → ZMod k × ZMod k → ℂ,
      (∀ t s, ∑ ij : ZMod k × ZMod k, (x s ij.1*y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, y (.inr t) j*H t (i,j)=0) →
      (∀ t j, ∑ i, x (.inr t) i*H t (i,j)=0) → (∑ t,H t)=0 → H=0) →
    IsGenericRank [k,k,c+1] r := by
  intro P one
  obtain ⟨_,enough,budget⟩ := relation_budget k k c r hk le_rfl level count
  exact generic_rank_of_witness hk le_rfl (by omega) count
    (square_spans_of_batch hk level enough (by simpa only [two_mul] using budget) one)

/-- This is the complete rational-function annihilator from the registered H1,
restricted to equal first and second dimensions. -/
theorem square_normals_of_batch {k c r : ℕ} [NeZero k]
    (hk : 3 ≤ k) (level : r+1=(k-1)*(k-1)) (count : r=k*k*(c+1) ⌈/⌉ (k+k+(c+1)-2)) :
    let P := {ij : ZMod k × ZMod k // ¬(ij.2=ij.1 ∨ ij.2=ij.1+1 ∨ ij.2=ij.1+2)} ⊕ ZMod k
    (∃ x : P → ZMod k → ℂ, ∃ y : P → ZMod k → ℂ, ∀ H : ZMod k → ZMod k × ZMod k → ℂ,
      (∀ t s, ∑ ij : ZMod k × ZMod k, (x s ij.1*y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, y (.inr t) j*H t (i,j)=0) →
      (∀ t j, ∑ i, x (.inr t) i*H t (i,j)=0) → (∑ t,H t)=0 → H=0) →
    let V := Fin r × (Fin k ⊕ (Fin k ⊕ Fin (c+1)))
    let R := MvPolynomial V ℂ
    let K := FractionRing R
    let q (s : V) := algebraMap R K (X s)
    let x (t : Fin r) (i : Fin k) := q (t,.inl i)
    let y (t : Fin r) (j : Fin k) := q (t,.inr (.inl j))
    let z (t : Fin r) (j : Fin (c+1)) := q (t,.inr (.inr j))
    ∀ F : Fin r → Fin k × Fin k → K,
      (∀ t s, ∑ ij : Fin k × Fin k, (x s ij.1*y s ij.2)*F t ij=0) →
      (∀ t i, ∑ j, y t j*F t (i,j)=0) → (∀ t j, ∑ i, x t i*F t (i,j)=0) →
      (∀ v : Fin r → K, (∀ j, ∑ t, v t*z t j=0) → ∑ t, v t • F t=0) → F=0 := by
  intro P one
  obtain ⟨_,enough,budget⟩ := relation_budget k k c r hk le_rfl level count
  exact (witness_iff_normals enough).mp
    (square_spans_of_batch hk level enough (by simpa only [two_mul] using budget) one)

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- Collect the explicit coordinate products and character products into
the full marked-family hypothesis, including its vector-valued sum. -/
theorem batch_of_character_fibers {k : ℕ} [NeZero k] {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (edge : A × B → Prop) (a : A → ZMod k) (b : B → ZMod k)
    (fiber : ∀ (s : ZMod k) (w : A × B → ℂ), (∀ ij, ¬edge ij → w ij = 0) →
      (∀ i, ∑ j, w (i,j)=0) → (∀ j, ∑ i, w (i,j)=0) →
      (∀ c : ZMod k, (∑ ij : A × B, if a ij.1+b ij.2=c then w ij else 0)=0) →
      (∀ ij, a ij.1+b ij.2=s → w ij=0) → w=0) :
    let P := {ij : A × B // ¬edge ij} ⊕ ZMod k
    ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ H : ZMod k → A × B → ℂ,
      (∀ t s, ∑ ij : A × B, (x s ij.1*y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, y (.inr t) j*H t (i,j)=0) →
      (∀ t j, ∑ i, x (.inr t) i*H t (i,j)=0) → (∑ t,H t)=0 → H=0 := by
  intro P
  let X : P → A → ℂ :=
    Sum.elim (fun p i => if i=p.val.1 then 1 else 0) (fun t i => ZMod.stdAddChar (t*a i))
  let Y : P → B → ℂ :=
    Sum.elim (fun p j => if j=p.val.2 then 1 else 0) (fun t j => ZMod.stdAddChar (t*b j))
  refine ⟨X,Y,?_⟩
  intro H products rows cols total
  exact bipartite_character_batch edge a b fiber H products rows cols
    (fun ij => by simpa only [Finset.sum_apply,Pi.zero_apply] using congrFun total ij)

/-- Arbitrarily labeled row and column vertices can use the same character
construction as soon as the point count and batch capacity fit. -/
theorem spans_of_character_fibers {k d e n r : ℕ} [NeZero k] {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (edge : A × B → Prop) [DecidablePred edge]
    (a : A → ZMod k) (b : B → ZMod k)
    (ca : Fintype.card A=d) (cb : Fintype.card B=e)
    (cp : Fintype.card ({ij : A × B // ¬edge ij} ⊕ ZMod k)=r)
    (enough : n≤r) (cap : r≤(r-n)*k)
    (fiber : ∀ (s : ZMod k) (w : A × B → ℂ), (∀ ij, ¬edge ij → w ij = 0) →
      (∀ i, ∑ j, w (i,j)=0) → (∀ j, ∑ i, w (i,j)=0) →
      (∀ c : ZMod k, (∑ ij : A × B, if a ij.1+b ij.2=c then w ij else 0)=0) →
      (∀ ij, a ij.1+b ij.2=s → w ij=0) → w=0) :
    ∃ x : Fin r → Fin d → ℂ, ∃ y : Fin r → Fin e → ℂ, ∃ z : Fin r → Fin n → ℂ,
    ∀ T : Fin d → Fin e → Fin n → ℂ, ∃ u : Fin r → Fin d → ℂ, ∃ v : Fin r → Fin e → ℂ,
      ∃ w : Fin r → Fin n → ℂ, ∀ i j l,
        T i j l=∑ t, (u t i*(y t j*z t l)+x t i*(v t j*z t l)+x t i*(y t j*w t l)) := by
  let first : ZMod k ↪ ({ij : A × B // ¬edge ij} ⊕ ZMod k) := Function.Embedding.inr
  exact spans_from_independent_batch first ca cb cp enough (by simpa only [ZMod.card] using cap)
    (batch_of_character_fibers edge a b fiber)

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- A sum supported at three different indices is the sum of its three values. -/
private theorem three_values {I : Type*} [Fintype I] [DecidableEq I] (f : I → ℂ)
    (a b c : I) (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (off : ∀ i, i≠a → i≠b → i≠c → f i=0) :
    ∑ i, f i = f a+f b+f c := by
  have unpack (i : I) : f i =
      (if i=a then f a else 0)+(if i=b then f b else 0)+(if i=c then f c else 0) := by
    by_cases ia : i=a
    · subst i
      simp [ab,ac]
    by_cases ib : i=b
    · subst i
      simp [ia,bc]
    by_cases ic : i=c
    · subst i
      simp [ia,ib]
    · simp [ia,ib,ic,off i ia ib ic]
  calc
    _ = ∑ i, ((if i=a then f a else 0)+(if i=b then f b else 0)+(if i=c then f c else 0)) :=
      Finset.sum_congr rfl fun i _ => unpack i
    _ = _ := by simp [Finset.sum_add_distrib]

/-- In the odd cyclic square, the three diagonals of displacements 0, 1 and 2
form a graph whose balanced flows are detected by every single color. -/
theorem square_color_detects {k : ℕ} [NeZero k] (hk : 3 ≤ k) (odd : Odd k)
    (s : ZMod k) (w : ZMod k × ZMod k → ℂ)
    (off : ∀ ij, ¬(ij.2=ij.1 ∨ ij.2=ij.1+1 ∨ ij.2=ij.1+2) → w ij=0)
    (left : ∀ i, ∑ j,w (i,j)=0) (right : ∀ j, ∑ i,w (i,j)=0)
    (color : ∀ z : ZMod k, (∑ ij : ZMod k × ZMod k, if ij.1+ij.2=z then w ij else 0)=0)
    (van : ∀ ij, ij.1+ij.2=s → w ij=0) : w=0 := by
  classical
  let h : ZMod k := (2 : ZMod k)⁻¹
  have half : h+h=1 := CyclicFlow.inverse_two_add_self odd
  let A (i : ZMod k) := w (i,i)
  let B (i : ZMod k) := w (i,i+1)
  let C (i : ZMod k) := w (i,i+2)
  have small (d : ℕ) (pos : 0<d) (lt : d<k) : (d : ZMod k)≠0 := by
    intro zero
    exact (Nat.not_le_of_lt lt) (Nat.le_of_dvd pos ((ZMod.natCast_eq_zero_iff d k).mp zero))
  have nz1 : (1 : ZMod k)≠0 := by simpa using small 1 (by decide) (by omega)
  have nz2 : (2 : ZMod k)≠0 := by simpa using small 2 (by decide) (by omega)
  have e01 (i : ZMod k) : i≠i+1 := by intro eq; apply nz1; linear_combination -eq
  have e02 (i : ZMod k) : i≠i+2 := by intro eq; apply nz2; linear_combination -eq
  have e12 (i : ZMod k) : i+1≠i+2 := by intro eq; apply nz1; linear_combination -eq
  have split (i j : ZMod k) : w (i,j) =
      (if i=j then A i else 0)+(if i+1=j then B i else 0)+(if i+2=j then C i else 0) := by
    by_cases v : i=j
    · subst j
      simp [A,(e01 i).symm,(e02 i).symm]
    by_cases u : i+1=j
    · subst j
      rw [if_neg (e01 i),if_pos rfl,if_neg (e12 i).symm,zero_add,add_zero]
    by_cases q : i+2=j
    · subst j
      simp [C,e02,e12]
    · simp [v,u,q,off (i,j) (by simp [Ne.symm v,Ne.symm u,Ne.symm q])]
  have left' (i : ZMod k) : A i+B i+C i=0 := by
    have eq := three_values (fun j => w (i,j)) i (i+1) (i+2) (e01 i) (e02 i) (e12 i)
      (fun j h0 h1 h2 => off (i,j) (by simp [h0,h1,h2]))
    exact eq.symm.trans (left i)
  have right' (j : ZMod k) : (∑ i : ZMod k, ((if i=j then A i else 0)+
      (if i+1=j then B i else 0)+(if i+2=j then C i else 0)))=0 := by
    exact (Finset.sum_congr rfl fun i _ => (split i j).symm).trans (right j)
  have color' (z : ZMod k) : (∑ i : ZMod k, ((if i+i=z then A i else 0)+
      (if i+(i+1)=z then B i else 0)+(if i+(i+2)=z then C i else 0)))=0 := by
    have each (i : ZMod k) : (∑ j : ZMod k, if i+j=z then w (i,j) else 0) =
        (if i+i=z then A i else 0)+(if i+(i+1)=z then B i else 0)+(if i+(i+2)=z then C i else 0) := by
      apply three_values (fun j => if i+j=z then w (i,j) else 0)
        i (i+1) (i+2) (e01 i) (e02 i) (e12 i)
      intro j h0 h1 h2
      simp [off (i,j) (by simp [h0,h1,h2])]
    have hz := color z
    rw [Fintype.sum_prod_type] at hz
    simpa only [each] using hz
  have constants := (CyclicFlow.fiber_sums_iff_constants h half A B C).mp ⟨left',right',color'⟩
  have reach (d : ZMod k) : ∃ i : ZMod k, i+(i+d)=s := by
    refine ⟨h*(s-d),?_⟩
    linear_combination (s-d)*half
  obtain ⟨i,hi⟩ := reach 0
  obtain ⟨j,hj⟩ := reach 1
  obtain ⟨l,hl⟩ := reach 2
  have a0 : A 0=0 := (constants.1 i).1.symm.trans (van (i,i) (by simpa using hi))
  have b0 : B 0=0 := (constants.1 j).2.1.symm.trans (van (j,j+1) hj)
  have c0 : C 0=0 := (constants.1 l).2.2.symm.trans (van (l,l+2) hl)
  funext ij
  rw [split ij.1 ij.2,(constants.1 ij.1).1,(constants.1 ij.1).2.1,(constants.1 ij.1).2.2,a0,b0,c0]
  simp

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

open Arxiv.«0805.3777»

/-- Fourier markings on the three-diagonal graph give an independent
two-plane normal at each of the k distinguished points. -/
theorem odd_square_batch (k : ℕ) [NeZero k] (hk : 3 ≤ k) (odd : Odd k) :
    let P := {ij : ZMod k × ZMod k // ¬(ij.2=ij.1 ∨ ij.2=ij.1+1 ∨ ij.2=ij.1+2)} ⊕ ZMod k
    ∃ x : P → ZMod k → ℂ, ∃ y : P → ZMod k → ℂ, ∀ H : ZMod k → ZMod k × ZMod k → ℂ,
      (∀ t s, ∑ ij : ZMod k × ZMod k, (x s ij.1*y s ij.2)*H t ij=0) →
      (∀ t i, ∑ j, y (.inr t) j*H t (i,j)=0) →
      (∀ t j, ∑ i, x (.inr t) i*H t (i,j)=0) → (∑ t,H t)=0 → H=0 :=
  batch_of_character_fibers (fun ij : ZMod k × ZMod k => ij.2=ij.1 ∨ ij.2=ij.1+1 ∨ ij.2=ij.1+2)
    id id (square_color_detects hk odd)

theorem square_spans_of_odd {k n r : ℕ} (hk : 3 ≤ k) (odd : Odd k)
    (level : r+1=(k-1)*(k-1)) (enough : n≤r) (budget : 2*r≤(r-n)*(2*k)) :
    ∃ x : Fin r → Fin k → ℂ, ∃ y : Fin r → Fin k → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin k → Fin k → Fin n → ℂ, ∃ u : Fin r → Fin k → ℂ,
        ∃ v : Fin r → Fin k → ℂ, ∃ w : Fin r → Fin n → ℂ, ∀ i j l,
          T i j l = ∑ t, (u t i*(y t j*z t l)+x t i*(v t j*z t l)+x t i*(y t j*w t l)) := by
  let _ : NeZero k := ⟨by omega⟩
  exact square_spans_of_batch hk level enough budget (odd_square_batch k hk odd)

/-- On the whole third dimension-count level the ordinary complex generic
rank of every square format of odd side is the predicted value. -/
theorem square_odd_generic_level {k c r : ℕ} (hk : 3 ≤ k) (odd : Odd k) (hkc : k<c)
    (level : r+1=(k-1)*(k-1)) (count : r=k*k*(c+1) ⌈/⌉ (k+k+(c+1)-2)) :
    IsGenericRank [k,k,c+1] r := by
  let _ : NeZero k := ⟨by omega⟩
  exact square_generic_rank_of_batch hk hkc level count (odd_square_batch k hk odd)

/-- In particular, the perfect format k×k×((k−1)(k−2)) has exact
generic rank k(k−2) for every odd k at least five. -/
theorem square_odd_perfect (k : ℕ) (hk : 5 ≤ k) (odd : Odd k) :
    IsGenericRank [k,k,(k-1)*(k-2)] (k*(k-2)) := by
  obtain ⟨m,rfl⟩ : ∃ m : ℕ, k=m+5 := ⟨k-5,by omega⟩
  let n := (m+4)*(m+3)
  let r := (m+5)*(m+3)
  have lev : r+1=(m+4)*(m+4) := by dsimp [r]; ring
  have eqden : (m+5)+(m+5)+n-2 = (m+5)*(m+4) := by
    dsimp [n]
    have : (m+5)+(m+5)+(m+4)*(m+3)=(m+5)*(m+4)+2 := by ring
    omega
  have product : (m+5)*(m+5)*n=((m+5)*(m+4))*r := by dsimp [n,r]; ring
  have denom : 0<(m+5)*(m+4) := by positivity
  have count : r=(m+5)*(m+5)*n ⌈/⌉ ((m+5)+(m+5)+n-2) := by
    rw [eqden,product]
    apply le_antisymm
    · have h : (m+5)*(m+4)*r ≤ (m+5)*(m+4) * (((m+5)*(m+4)*r) ⌈/⌉ ((m+5)*(m+4))) :=
        (ceilDiv_le_iff_le_mul denom).mp le_rfl
      exact Nat.le_of_mul_le_mul_left h denom
    · exact (ceilDiv_le_iff_le_mul denom).mpr le_rfl
  have bounded : n≤r := by dsimp [n,r]; nlinarith
  have gap : r-n=m+3 := by
    have : r=n+(m+3) := by dsimp [n,r]; ring
    omega
  have budget : 2*r≤(r-n)*(2*(m+5)) := by rw [gap]; dsimp [r]; nlinarith
  change IsGenericRank [m+5,m+5,n] r
  apply generic_rank_of_witness (by omega) le_rfl (by dsimp [n]; nlinarith) count
  exact square_spans_of_odd (by omega) odd lev bounded budget

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- Two relation rows with a shared unknown have exactly one possible
additional kernel, namely the part of the shared plane in both old images. -/
theorem shared_pair_iff {K E U V : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (A : U →ₗ[K] E) (B : V →ₗ[K] E) (P : Submodule K E) :
    Function.Injective (fun t : U × V × P =>
      (A t.1 + (t.2.2 : E), B t.2.1 + (t.2.2 : E))) ↔
      Function.Injective A ∧ Function.Injective B ∧ P ⊓ (A.range ⊓ B.range) = ⊥ := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro x y eq
      have hh : (x,(0:V),(0:P))=(y,0,0) := h (by simp [eq])
      exact congrArg Prod.fst hh
    · intro x y eq
      have hh : ((0:U),x,(0:P))=(0,y,0) := h (by simp [eq])
      exact congrArg (fun t : U × V × P => t.2.1) hh
    · apply bot_unique
      intro z hz
      obtain ⟨u,hu⟩ := hz.2.1
      obtain ⟨v,hv⟩ := hz.2.2
      let p : P := ⟨z,hz.1⟩
      have hh : (u,v,(0:P))=(0,0,p) := h (by simp [hu,hv,p])
      exact (congrArg (fun t : U × V × P => (t.2.2 : E)) hh).symm
  · rintro ⟨hA,hB,hP⟩ ⟨x,y,p⟩ ⟨x',y',p'⟩ he
    obtain ⟨ha,hb⟩ := Prod.mk.inj he
    have eqA : A (x'-x) = (p:E)-p' := by
      rw [map_sub]
      calc
        _ = (A x'+(p':E))-(A x+(p':E)) := by abel
        _ = (p:E)-p' := by rw [← ha]; abel
    have eqB : B (y'-y) = (p:E)-p' := by
      rw [map_sub]
      calc
        _ = (B y'+(p':E))-(B y+(p':E)) := by abel
        _ = (p:E)-p' := by rw [← hb]; abel
    have hm : (p:E)-p' ∈ P ⊓ (A.range ⊓ B.range) :=
      ⟨P.sub_mem p.property p'.property, ⟨x'-x,eqA⟩, ⟨y'-y,eqB⟩⟩
    rw [hP, Submodule.mem_bot] at hm
    have hp : p=p' := Subtype.ext (sub_eq_zero.mp hm)
    subst p'
    exact Prod.ext (hA (add_right_cancel ha)) (Prod.ext (hB (add_right_cancel hb)) rfl)

/-- For hyperplanes with defining functionals f and g, the residual
criterion is exactly joint injectivity of their restrictions to the shared plane. -/
theorem hyperplane_cuts_iff {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : Submodule K E) (f g : E →ₗ[K] K) :
    P ⊓ (f.ker ⊓ g.ker) = ⊥ ↔ Function.Injective (fun p : P => (f p.val,g p.val)) := by
  constructor
  · intro he p q h
    obtain ⟨hf,hg⟩ := Prod.mk.inj h
    have hmem : (p:E)-q ∈ P ⊓ (f.ker ⊓ g.ker) := by
      refine ⟨P.sub_mem p.property q.property,?_,?_⟩
      · exact LinearMap.mem_ker.mpr (by rw [map_sub,hf,sub_self])
      · exact LinearMap.mem_ker.mpr (by rw [map_sub,hg,sub_self])
    rw [he,Submodule.mem_bot] at hmem
    exact Subtype.ext (sub_eq_zero.mp hmem)
  · intro h
    apply bot_unique
    intro z hz
    have h0 : (⟨z,hz.1⟩:P) = 0 := h (by
      change (f z,g z) = (f 0,g 0)
      simp [LinearMap.mem_ker.mp hz.2.1,LinearMap.mem_ker.mp hz.2.2])
    exact congrArg Subtype.val h0

/-- A two-by-two determinant verifies independence of the two residual
directions in coordinates on the shared plane. -/
theorem separating_cuts {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : Submodule K E) (e : Module.Basis (Fin 2) K P) (f g : E →ₗ[K] K)
    (det : f (e 0).val*g (e 1).val - f (e 1).val*g (e 0).val ≠ 0) :
    P ⊓ (f.ker ⊓ g.ker) = ⊥ := by
  apply bot_unique
  intro z hz
  let p : P := ⟨z,hz.1⟩
  let u := e.repr p 0
  let v := e.repr p 1
  have rep : u • (e 0).val + v • (e 1).val = z := by
    simpa only [Fin.sum_univ_two,Submodule.coe_add,Submodule.coe_smul_of_tower] using
      congrArg Subtype.val (e.sum_repr p)
  have hf := congrArg f rep
  have hg := congrArg g rep
  simp only [map_add, map_smul, smul_eq_mul, LinearMap.mem_ker.mp hz.2.1] at hf
  simp only [map_add, map_smul, smul_eq_mul, LinearMap.mem_ker.mp hz.2.2] at hg
  have hu : (f (e 0).val*g (e 1).val - f (e 1).val*g (e 0).val)*u=0 := by
    linear_combination (g (e 1).val)*hf - (f (e 1).val)*hg
  have hv : (f (e 0).val*g (e 1).val - f (e 1).val*g (e 0).val)*v=0 := by
    linear_combination (f (e 0).val)*hg - (g (e 0).val)*hf
  change z=0
  simpa only [(mul_eq_zero.mp hu).resolve_left det,(mul_eq_zero.mp hv).resolve_left det,
    zero_smul, add_zero] using rep.symm

/-- For a genuine two-plane the residual determinant test is also necessary. -/
theorem cut_determinant_iff {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : Submodule K E) (e : Module.Basis (Fin 2) K P) (f g : E →ₗ[K] K) :
    P ⊓ (f.ker ⊓ g.ker) = ⊥ ↔
      f (e 0).val*g (e 1).val - f (e 1).val*g (e 0).val ≠ 0 := by
  classical
  refine ⟨?_, separating_cuts P e f g⟩
  intro h
  let M : Matrix (Fin 2) (Fin 2) K := !![f (e 0).val, f (e 1).val; g (e 0).val, g (e 1).val]
  have coordinates (u : Fin 2 → K) :
      (f (e.equivFun.symm u).val, g (e.equivFun.symm u).val) =
      (M.mulVec u 0, M.mulVec u 1) := by
    simp [M, Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct,
      smul_eq_mul, mul_comm]
  have hm : Function.Injective M.mulVec := by
    intro u v hv
    have eq := congrArg (fun z : Fin 2 → K => (z 0,z 1)) hv
    exact e.equivFun.symm.injective (((hyperplane_cuts_iff P f g).mp h)
      ((coordinates u).trans (eq.trans (coordinates v).symm)))
  have hd := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hm))
  simpa [M, Matrix.det_fin_two] using hd

/-- Annihilating all the ordinary summands suffices. Thus the same
two-by-two minor checks the intersection hypothesis of the coupled schedule. -/
theorem batch_cuts_of_det {K E H : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : Submodule K E) (e : Module.Basis (Fin 2) K P) (U V : H → Submodule K E)
    (f g : E →ₗ[K] K) (left : ∀ i, U i ≤ f.ker) (right : ∀ i, V i ≤ g.ker)
    (det : f (e 0).val*g (e 1).val - f (e 1).val*g (e 0).val ≠ 0) :
    P ⊓ ((⨆ i, U i) ⊓ (⨆ i, V i)) = ⊥ := by
  apply bot_unique
  intro z hz
  have hm : z ∈ P ⊓ (f.ker ⊓ g.ker) := ⟨hz.1,(iSup_le left) hz.2.1,(iSup_le right) hz.2.2⟩
  rwa [separating_cuts P e f g det] at hm

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- The whole-plane packing fails only at odd D. In that case precisely
e surplus planes consume two unused single-coordinate slots each. -/
theorem capacity_cases {r s D : ℕ} (budget : 2*r ≤ s*D) :
    r ≤ s*(D/2) ∨ ∃ e f : ℕ, 0<e ∧ D=2*(D/2)+1 ∧
      s=2*e+f ∧ r=s*(D/2)+e := by
  by_cases h : r ≤ s*(D/2)
  · exact Or.inl h
  · right
    have hd : D=2*(D/2)+1 := by
      by_contra hn
      have hd : D=2*(D/2) := by omega
      have hm := congrArg (s*·) hd
      nlinarith only [hm,budget,show s*(D/2)<r by omega]
    have cap : 2*r≤2*(s*(D/2))+s := by
      have hm := congrArg (s*·) hd
      nlinarith only [hm,budget]
    exact ⟨r-s*(D/2),s-2*(r-s*(D/2)),by omega,hd,by omega,by omega⟩

/-- Disjoint whole-plane batches use ordinary indicator rows. -/
theorem disjoint_rows {K E P G : Type*} [Field K] [AddCommGroup E] [Module K E]
    [Fintype P] [DecidableEq G] (label : P → G) (N : P → Submodule K E)
    (indep : ∀ (g : G) (v : {p : P // label p=g} → E),
      (∀ i, v i ∈ N i.val) → ∑ i, v i = 0 → v=0)
    (F : P → E) (membership : ∀ p, F p∈N p)
    (relations : ∀ g, (∑ p, (if label p=g then (1:K) else 0) • F p)=0) :
    F=0 := by
  classical
  have fiber (g : G) : ∑ p : {p : P // label p=g}, F p.val=0 := by
    have he := (Equiv.sumCompl (fun p : P => label p=g)).sum_comp
      (fun p => (if label p=g then (1:K) else 0) • F p)
    rw [Fintype.sum_sum_type, relations g] at he
    have yes (p : {p : P // label p=g}) : label p.val=g := p.property
    have no (p : {p : P // label p≠g}) : label p.val≠g := p.property
    simpa [yes,no] using he
  funext p
  exact congrFun (indep (label p) (fun q => F q.val) (fun q => membership q.val)
    (fiber (label p))) ⟨p,rfl⟩

/-- Pair rows indexed by the first two copies of J. Every ordinary plane
belongs to one row; the additional plane at j belongs to the corresponding
row in each copy. Their two residual hyperplanes must cut it transversely. -/
theorem coupled_rows {K E J O H : Type*} [Field K] [AddCommGroup E] [Module K E]
    [Fintype J] [Fintype O] [Fintype H] [DecidableEq J] [DecidableEq O]
    (N : (J ⊕ J ⊕ O) → H → Submodule K E) (P : J → Submodule K E)
    (indep : ∀ (g : J ⊕ J ⊕ O) (u : H → E), (∀ i, u i∈N g i) → ∑ i, u i=0 → u=0)
    (cuts : ∀ j, P j ⊓ ((⨆ i, N (.inl j) i) ⊓ (⨆ i, N (.inr (.inl j)) i))=⊥) :
    let G := J ⊕ J ⊕ O
    let weight (g : G) : (G × H) ⊕ J → K :=
      Sum.elim (fun t => if t.1=g then 1 else 0) (fun j =>
        g.elim (fun l => if j=l then 1 else 0)
          (Sum.elim (fun l => if j=l then 1 else 0) (fun _ => 0)))
    ∀ F : (G × H) ⊕ J → E,
      (∀ g i, F (.inl (g,i)) ∈ N g i) → (∀ j, F (.inr j) ∈ P j) →
      (∀ g, (∑ t, weight g t • F t)=0) → F=0 := by
  classical
  intro G weight F base shared rows
  have row (g : G) : (∑ i, F (.inl (g,i))) +
      g.elim (fun j => F (.inr j)) (Sum.elim (fun j => F (.inr j)) (fun _ => 0)) = 0 := by
    have base_sum : (∑ t : G × H, (if t.1=g then (1:K) else 0) • F (.inl t)) =
        ∑ i, F (.inl (g,i)) := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single g]
      · simp
      · intro g' _ hne; simp [hne]
      · simp
    have h := rows g
    rw [Fintype.sum_sum_type] at h
    simp only [weight, Sum.elim_inl, Sum.elim_inr] at h
    rw [base_sum] at h
    rcases g with l | l | o <;> simpa [ite_smul] using h
  have in_span (g : G) : (∑ i, F (.inl (g,i))) ∈ ⨆ i, N g i :=
    Submodule.sum_mem _ fun i _ => (le_iSup (N g) i) (base g i)
  have zero (j : J) : F (.inr j)=0 := by
    have h₁ : F (.inr j) = -∑ i, F (.inl (.inl j,i)) :=
      eq_neg_of_add_eq_zero_right (row (.inl j))
    have h₂ : F (.inr j) = -∑ i, F (.inl (.inr (.inl j),i)) :=
      eq_neg_of_add_eq_zero_right (row (.inr (.inl j)))
    have hm : F (.inr j) ∈ P j ⊓ ((⨆ i, N (.inl j) i) ⊓ (⨆ i, N (.inr (.inl j)) i)) :=
      ⟨shared j, h₁ ▸ Submodule.neg_mem _ (in_span (.inl j)),
        h₂ ▸ Submodule.neg_mem _ (in_span (.inr (.inl j)))⟩
    rwa [cuts j,Submodule.mem_bot] at hm
  have local_zero (g : G) : (fun i => F (.inl (g,i)))=0 := by
    apply indep g _ (base g)
    obtain l | l | o := g <;> simpa [zero] using row _
  funext p
  rcases p with ⟨g,i⟩ | j
  · exact congrFun (local_zero g) i
  · exact zero j

/-- The shared schedule has two rows per paired block, one row per leftover
block, and exactly one additional point per row pair. -/
theorem coupled_card (e f h : ℕ) :
    Fintype.card (Fin e ⊕ Fin e ⊕ Fin f) = 2*e+f ∧
      Fintype.card (((Fin e ⊕ Fin e ⊕ Fin f) × Fin h) ⊕ Fin e) = (2*e+f)*h+e := by
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  constructor <;> ring

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- Choose a basis for the kernel of a full-row-rank relation matrix.
Its coordinate rows span the desired third factor. Every prescribed row
of the relation matrix annihilates these third-factor vectors. -/
theorem realize_relations {K P G : Type*} [Field K] [Fintype P] [Fintype G]
    (A : Matrix G P K) (onto : Function.Surjective A.mulVec) :
    ∃ z : P → Fin (Fintype.card P - Fintype.card G) → K,
      Submodule.span K (Set.range z)=⊤ ∧ ∀ g k, ∑ p, A g p*z p k=0 := by
  classical
  let N := A.mulVecLin.ker
  have hdim : Module.finrank K N = Fintype.card P - Fintype.card G := by
    have h := A.mulVecLin.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr onto, finrank_top] at h
    simp only [Module.finrank_fintype_fun_eq_card] at h
    change _ + Module.finrank K N = _ at h
    omega
  let b := Module.finBasisOfFinrankEq K N hdim
  let z : Matrix P (Fin (Fintype.card P-Fintype.card G)) K := fun p i => (b i).val p
  have indep : LinearIndependent K z.transpose.row := b.linearIndependent.map' N.subtype N.ker_subtype
  have hZ : Submodule.span K (Set.range z.row)=⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← z.rank_eq_finrank_span_row, ← z.rank_transpose, indep.rank_matrix,
      Module.finrank_fintype_fun_eq_card]
  refine ⟨z,hZ,fun g k => ?_⟩
  exact congrFun (LinearMap.mem_ker.mp (b k).property) g

/-- An identity set of pivot columns gives a right inverse for the relation map. -/
theorem surjective_of_pivots {K P G : Type*} [Field K] [Fintype P] [Fintype G] [DecidableEq G]
    (A : Matrix G P K) (pivot : G → P)
    (h : ∀ g j, A g (pivot j) = if g=j then 1 else 0) : Function.Surjective A.mulVec := by
  classical
  let B : Matrix P G K := fun t j => if t=pivot j then 1 else 0
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  refine ⟨B,?_⟩
  ext g j
  rw [Matrix.one_apply]
  change (∑ t : P, A g t * (if t=pivot j then 1 else 0)) = if g=j then 1 else 0
  simp [mul_ite, h]

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- Injectivity of weighted normal equations supplies an actual spanning tensor
configuration with card(P)-card(G) slices. The third factors are constructed
from the kernel of the prescribed relation matrix. -/
theorem spans_of_weighted_normals {K P G : Type*} [Field K] [Fintype P] [Fintype G]
    {a b : ℕ} (x : P → Fin a → K) (y : P → Fin b → K)
    (A : Matrix G P K) (onto : Function.Surjective A.mulVec)
    (indep : ∀ F : P → Fin a × Fin b → K,
      (∀ p s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*F p ij=0) →
      (∀ p i, ∑ j, y p j*F p (i,j)=0) → (∀ p j, ∑ i, x p i*F p (i,j)=0) →
      (∀ g, ∑ t, A g t • F t = 0) → F=0) :
    let r := Fintype.card P
    let c := r-Fintype.card G
    ∃ X : Fin r → Fin a → K, ∃ Y : Fin r → Fin b → K, ∃ Z : Fin r → Fin c → K,
      ∀ T : Fin a → Fin b → Fin c → K, ∃ u : Fin r → Fin a → K,
        ∃ v : Fin r → Fin b → K, ∃ w : Fin r → Fin c → K, ∀ i j k,
          T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  classical
  intro r c
  obtain ⟨z,hz,relations⟩ := realize_relations A onto
  let e : P ≃ Fin r := Fintype.equivFin P
  let X (i : Fin r) := x (e.symm i)
  let Y (i : Fin r) := y (e.symm i)
  let Z (i : Fin r) := z (e.symm i)
  have spanZ : Submodule.span K (Set.range Z)=⊤ := by
    have he : Set.range Z = Set.range z := by
      apply Set.Subset.antisymm
      · rintro _ ⟨t,rfl⟩; exact Set.mem_range_self _
      · rintro _ ⟨p,rfl⟩; exact ⟨e p,by simp [Z]⟩
    rwa [he]
  let V := Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))
  let M : Matrix ((Fin a × Fin b) × Fin c) V K := fun row col =>
    col.2.elim (fun i => if i=row.1.1 then Y col.1 row.1.2*Z col.1 row.2 else 0)
      (Sum.elim (fun j => if j=row.1.2 then X col.1 row.1.1*Z col.1 row.2 else 0)
        (fun k => if k=row.2 then X col.1 row.1.1*Y col.1 row.1.2 else 0))
  have full : Function.Surjective M.mulVec := by
    apply (LastSliceRelation.tangent_iff_normal_relations X Y Z spanZ M (fun _ _ _ _ _ => rfl)).mpr
    intro F outer row col rel
    have trace (g : G) : ∑ q, A g q • F (e q)=0 := by
      let v (t : Fin r) := A g (e.symm t)
      have hv (k : Fin c) : ∑ t, v t*Z t k=0 :=
        (e.symm.sum_comp (fun p => A g p*z p k)).trans (relations g k)
      have near := rel v hv
      have ecomp := e.sum_comp (fun t => v t • F t)
      simpa only [v,Equiv.symm_apply_apply,near] using ecomp.trans near
    have zero := indep (fun q => F (e q))
      (fun p s => by simpa only [X,Y,Equiv.symm_apply_apply] using outer (e p) (e s))
      (fun p i => by simpa only [Y,Equiv.symm_apply_apply] using row (e p) i)
      (fun p j => by simpa only [X,Equiv.symm_apply_apply] using col (e p) j) trace
    funext i
    simpa only [Equiv.apply_symm_apply,Pi.zero_apply] using congrFun zero (e.symm i)
  refine ⟨X,Y,Z,?_⟩
  intro T
  obtain ⟨u,hu⟩ := full (fun row => T row.1.1 row.1.2 row.2)
  refine ⟨fun t i => u (t,.inl i),fun t j => u (t,.inr (.inl j)),fun t k => u (t,.inr (.inr k)),?_⟩
  intro i j k
  refine (congrFun hu ((i,j),k)).symm.trans ?_
  change (∑ q : V, M ((i,j),k) q*u q) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [M,ite_mul,Finset.sum_ite_eq']
  ring

/-- An exact normal-batch type exists at every point count in the scalar
budget. For the overflowing odd case there is an exclusive pivot available
in each of the s rows. -/
theorem capacity_partition {D r s : ℕ} (hs : s≤r) (budget : 2*r ≤ s*D) :
    (∃ label : Fin r → Fin s, Function.Surjective label ∧
      ∀ g, Fintype.card {p : Fin r // label p=g} ≤ D/2) ∨
    ∃ e f : ℕ, 0<e ∧ 0<D/2 ∧ D=2*(D/2)+1 ∧
      Nonempty (Fin s ≃ (Fin e ⊕ Fin e ⊕ Fin f)) ∧
      Nonempty (Fin r ≃ (((Fin e ⊕ Fin e ⊕ Fin f) × Fin (D/2)) ⊕ Fin e)) := by
  rcases capacity_cases budget with h | ⟨e,f,he,odd,hrows,hpoints⟩
  · exact Or.inl (LastSliceBatch.balanced_partition hs h)
  · have hh : 0<D/2 := by
      by_contra! hn
      rw [show D/2=0 by omega, Nat.mul_zero, Nat.zero_add] at hpoints
      omega
    obtain ⟨crow,cpoint⟩ := coupled_card e f (D/2)
    refine Or.inr ⟨e,f,he,hh,odd,⟨Fintype.equivOfCardEq ?_⟩,⟨Fintype.equivOfCardEq ?_⟩⟩
    · simpa only [Fintype.card_fin, crow] using hrows
    · simpa only [Fintype.card_fin, cpoint, ← hrows] using hpoints

/-- In the nonoverflow case, direct ordinary batches suffice for a full
tangent witness. Each row of the relation matrix is its fiber indicator. -/
theorem spans_of_disjoint_planes {K P G : Type*} [Field K] [Fintype P] [Fintype G] [DecidableEq G]
    {a b : ℕ} (label : P → G) (covers : Function.Surjective label)
    (x : P → Fin a → K) (y : P → Fin b → K) (N : P → Submodule K (Fin a × Fin b → K))
    (normals : ∀ (t : P) (z : Fin a × Fin b → K),
      (∀ p, ∑ ij : Fin a × Fin b, (x p ij.1*y p ij.2)*z ij=0) →
      (∀ i, ∑ j, y t j*z (i,j)=0) → (∀ j, ∑ i, x t i*z (i,j)=0) → z∈N t)
    (indep : ∀ (g : G) (u : {p : P // label p=g} → Fin a × Fin b → K),
      (∀ t, u t ∈ N t.val) → ∑ t, u t=0 → u=0) :
    let r := Fintype.card P
    let c := r-Fintype.card G
    ∃ X : Fin r → Fin a → K, ∃ Y : Fin r → Fin b → K, ∃ Z : Fin r → Fin c → K,
      ∀ T : Fin a → Fin b → Fin c → K, ∃ u : Fin r → Fin a → K,
        ∃ v : Fin r → Fin b → K, ∃ w : Fin r → Fin c → K, ∀ i j k,
          T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  classical
  let A : Matrix G P K := fun g t => if label t=g then 1 else 0
  choose pivot right using covers
  have surj : Function.Surjective A.mulVec := by
    apply surjective_of_pivots A pivot
    intro g j
    simp only [A,right]
    by_cases h : g=j
    · subst j; simp
    · simp [h,Ne.symm h]
  apply spans_of_weighted_normals x y A surj
  intro F outer row col rel
  exact disjoint_rows label N indep F (fun p => normals p (F p) (outer p) (row p) (col p)) rel

/-- Transverse sharing of one normal plane per paired relation, together with
directness inside each ordinary batch, gives an actual tangent witness. -/
theorem spans_of_coupled_planes {K J O H : Type*} [Field K]
    [Fintype J] [Fintype O] [Fintype H] [Nonempty H] [DecidableEq J] [DecidableEq O]
    {a b : ℕ} :
    let G := J ⊕ J ⊕ O
    let P := (G × H) ⊕ J
    ∀ (x : P → Fin a → K) (y : P → Fin b → K)
      (N : G → H → Submodule K (Fin a × Fin b → K)) (Q : J → Submodule K (Fin a × Fin b → K)),
      (∀ (t : P) (z : Fin a × Fin b → K),
        (∀ p, ∑ ij : Fin a × Fin b, (x p ij.1*y p ij.2)*z ij=0) →
        (∀ i, ∑ j, y t j*z (i,j)=0) → (∀ j, ∑ i, x t i*z (i,j)=0) →
        z ∈ t.elim (fun p => N p.1 p.2) Q) →
      (∀ (g : G) (u : H → Fin a × Fin b → K), (∀ i, u i∈N g i) → ∑ i, u i=0 → u=0) →
      (∀ j, Q j ⊓ ((⨆ i, N (.inl j) i) ⊓ (⨆ i, N (.inr (.inl j)) i))=⊥) →
      let r := Fintype.card P
      let c := r-Fintype.card G
      ∃ X : Fin r → Fin a → K, ∃ Y : Fin r → Fin b → K, ∃ Z : Fin r → Fin c → K,
        ∀ T : Fin a → Fin b → Fin c → K, ∃ u : Fin r → Fin a → K,
          ∃ v : Fin r → Fin b → K, ∃ w : Fin r → Fin c → K, ∀ i j k,
            T i j k = ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  classical
  intro G P x y N Q normals within cuts
  let A : Matrix G P K := fun g => Sum.elim (fun t => if t.1=g then 1 else 0) (fun j =>
    g.elim (fun l => if j=l then 1 else 0) (Sum.elim (fun l => if j=l then 1 else 0) (fun _ => 0)))
  let pivot (g : G) : P := .inl (g,Classical.choice ‹Nonempty H›)
  have surj : Function.Surjective A.mulVec := by
    apply surjective_of_pivots A pivot
    intro g j
    change (if j=g then (1:K) else 0) = if g=j then 1 else 0
    by_cases h : g=j
    · subst j; simp
    · simp [h,Ne.symm h]
  apply spans_of_weighted_normals x y A surj
  intro F outer row col hrelations
  have mem (t : P) := normals t (F t) (outer t) (row t) (col t)
  exact coupled_rows N Q within cuts F (fun g i => mem (.inl (g,i)))
    (fun j => mem (.inr j)) hrelations

end CriticalLastSlice.TwoPlanes
namespace CriticalLastSlice.TwoPlanes

/-- The matrix of the marked normal equations, including any number of
weighted row sums, is injective exactly when they have joint trivial kernel. -/
theorem weighted_stack_iff {K A B S G W : Type*} [Field K] [Fintype A] [Fintype B] [Fintype G]
    [DecidableEq A] [DecidableEq B] [DecidableEq G]
    (label : G → S) (weights : Matrix W G K) (x : S → A → K) (y : S → B → K)
    (M : Matrix ((G × (S ⊕ (A ⊕ B))) ⊕ (W × (A × B))) (G × (A × B)) K)
    (entry : ∀ row col, M row col = row.elim
      (fun ge => if col.1=ge.1 then ge.2.elim
        (fun s => x s col.2.1*y s col.2.2)
        (Sum.elim (fun i => if col.2.1=i then y (label ge.1) col.2.2 else 0)
          (fun j => if col.2.2=j then x (label ge.1) col.2.1 else 0)) else 0)
      (fun wij => if col.2=wij.2 then weights wij.1 col.1 else 0)) :
    Function.Injective M.mulVec ↔
      ∀ H : G → A × B → K, (∀ g s, ∑ ij : A × B, (x s ij.1*y s ij.2)*H g ij=0) →
        (∀ g i, ∑ j, y (label g) j*H g (i,j)=0) →
        (∀ g j, ∑ i, x (label g) i*H g (i,j)=0) → (∀ w, ∑ g, weights w g • H g=0) → H=0 := by
  classical
  have outer (H : G → A × B → K) (g : G) (s : S) :
      M.mulVec (Function.uncurry H) (.inl (g,.inl s)) = ∑ ij, (x s ij.1*y s ij.2)*H g ij := by
    change (∑ z : G × (A × B), M (.inl (g,.inl s)) z*H z.1 z.2) = _
    rw [Fintype.sum_prod_type]
    simp [entry,ite_mul,Finset.sum_ite_eq']
  have row₁ (H : G → A × B → K) (g : G) (i : A) :
      M.mulVec (Function.uncurry H) (.inl (g,.inr (.inl i))) = ∑ j, y (label g) j*H g (i,j) := by
    change (∑ z : G × (A × B), M (.inl (g,.inr (.inl i))) z*H z.1 z.2) = _
    simp [Fintype.sum_prod_type,entry,ite_mul,Finset.sum_ite_eq']
  have col₁ (H : G → A × B → K) (g : G) (j : B) :
      M.mulVec (Function.uncurry H) (.inl (g,.inr (.inr j))) = ∑ i, x (label g) i*H g (i,j) := by
    change (∑ z : G × (A × B), M (.inl (g,.inr (.inr j))) z*H z.1 z.2) = _
    simp [Fintype.sum_prod_type,entry,ite_mul,Finset.sum_ite_eq']
  have total (H : G → A × B → K) (w : W) (ij : A × B) :
      M.mulVec (Function.uncurry H) (.inr (w,ij)) = (∑ g, weights w g • H g) ij := by
    change (∑ z : G × (A × B), M (.inr (w,ij)) z*H z.1 z.2) = _
    rw [Fintype.sum_prod_type]
    simp [entry,ite_mul,Finset.sum_apply,Finset.sum_ite_eq',Pi.smul_apply,smul_eq_mul]
  constructor
  · intro inject H hp hx hy hz
    have ker : M.mulVec (Function.uncurry H)=0 := by
      funext z
      rcases z with ⟨g,s|i|j⟩|⟨w,ij⟩
      · exact (outer H g s).trans (hp g s)
      · exact (row₁ H g i).trans (hx g i)
      · exact (col₁ H g j).trans (hy g j)
      · exact (total H w ij).trans (congrFun (hz w) ij)
    have he := inject (ker.trans (Matrix.mulVec_zero M).symm)
    exact funext fun g => funext fun ij => congrFun he (g,ij)
  · intro hs
    change Function.Injective M.mulVecLin
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro f hf
    let H : G → A × B → K := Function.curry f
    have eq : M.mulVec (Function.uncurry H) = 0 := hf
    have van := hs H (fun g s => (outer H g s).symm.trans (congrFun eq _))
      (fun g i => (row₁ H g i).symm.trans (congrFun eq _))
      (fun g j => (col₁ H g j).symm.trans (congrFun eq _))
      (fun w => funext fun ij => (total H w ij).symm.trans (congrFun eq _))
    exact funext fun z => congrFun (congrFun van z.1) z.2

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

open MvPolynomial

/-- One configuration on which the prescribed weighted normal equations
are injective yields a single configuration that works for every ordered marking. -/
theorem common_weighted_markings {A B P Q W : Type*} [Fintype W] [Fintype A] [Fintype B] [Fintype P] [Fintype Q]
    (weights : Matrix W Q ℂ) (first : Q ↪ P) (one : ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (first t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (first t) i*H t (i,j))=0) →
      (∀ w, ∑ t, weights w t • H t=0) → H=0) :
    ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ e : Q ↪ P, ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e t) i*H t (i,j))=0) →
      (∀ w, ∑ t, weights w t • H t=0) → H=0 := by
  classical
  let V := P × (A ⊕ B)
  let Row := (Q × (P ⊕ (A ⊕ B))) ⊕ (W × (A × B))
  let Col := Q × (A × B)
  let M (e : Q ↪ P) : Matrix Row Col (MvPolynomial V ℂ) := fun row col => row.elim
    (fun te => if col.1=te.1 then te.2.elim
      (fun s => X (s,.inl col.2.1)*X (s,.inr col.2.2))
      (Sum.elim (fun i => if col.2.1=i then X (e te.1,.inr col.2.2) else 0)
        (fun j => if col.2.2=j then X (e te.1,.inl col.2.1) else 0)) else 0)
    (fun w => if col.2=w.2 then C (weights w.1 col.1) else 0)
  let D (x : P → A → ℂ) (y : P → B → ℂ) (e : Q ↪ P) : Prop := ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e t) i*H t (i,j))=0) →
      (∀ w, ∑ t, weights w t • H t=0) → H=0
  have action (e : Q ↪ P) (p : V → ℂ) : Function.Injective ((M e).map (eval p)).mulVec ↔
      D (fun s i => p (s,.inl i)) (fun s j => p (s,.inr j)) e := by
    apply weighted_stack_iff e weights (fun s i => p (s,.inl i)) (fun s j => p (s,.inr j))
    intro row col
    change eval p (M e row col) = _
    rcases row with ⟨t,s|i|j⟩|⟨w,ij⟩ <;> rcases col with ⟨l,u,v⟩
    · by_cases ht : l=t <;> simp [M,ht]
    · by_cases ht : l=t <;> by_cases hi : u=i <;> simp [M,ht,hi]
    · by_cases ht : l=t <;> by_cases hj : v=j <;> simp [M,ht,hj]
    · by_cases he : (u,v)=ij <;> simp [M,he]
  obtain ⟨x₀,y₀,h₀⟩ := one
  have each (e : Q ↪ P) : ∃ p : V → ℂ, Function.Injective ((M e).map (eval p)).mulVec := by
    obtain ⟨σ,hσ⟩ := LastSliceBatch.permutation_of_markings e first
    let p (z : V) := z.2.elim (x₀ (σ z.1)) (y₀ (σ z.1))
    refine ⟨p,(action e p).mpr ?_⟩
    intro H outer row col
    apply h₀ H
    · intro t s
      obtain ⟨s,rfl⟩ := σ.surjective s
      exact outer t s
    · simpa only [p,Sum.elim_inr,hσ] using row
    · simpa only [p,Sum.elim_inl,hσ] using col
  obtain ⟨p,hp⟩ := LastSliceBatch.common_injective (U:=fun _ : Q ↪ P => Row) (W:=fun _ => Col) M each
  exact ⟨fun s i => p (s,.inl i),fun s j => p (s,.inr j),fun e => (action e p).mp (hp e)⟩

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

set_option maxHeartbeats 800000 in

/-- A single ordered pair of h-point batches, sharing one additional normal,
suffices for every paired and unpaired row of the odd schedule. Across
different pairs the complex factors can be chosen simultaneously. -/
theorem spans_of_single_paired_marking {J O H : Type*} [Fintype J] [Fintype O]
    [Fintype H] [Nonempty J] [Nonempty H] {a b : ℕ} :
    let G := J ⊕ J ⊕ O
    let P := (G × H) ⊕ J
    let Q := H ⊕ H ⊕ Unit
    (∃ first : Q ↪ P, ∃ x : P → Fin a → ℂ, ∃ y : P → Fin b → ℂ, ∀ F : Q → Fin a × Fin b → ℂ,
      (∀ t s, ∑ ij : Fin a × Fin b,(x s ij.1*y s ij.2)*F t ij=0) →
      (∀ t i, ∑ j,y (first t) j*F t (i,j)=0) → (∀ t j, ∑ i,x (first t) i*F t (i,j)=0) →
      (∑ i : H, F (.inl i))+F (.inr (.inr ()))=0 →
      (∑ i : H, F (.inr (.inl i)))+F (.inr (.inr ()))=0 → F=0) →
    let r := Fintype.card P
    let c := r-Fintype.card G
    ∃ X : Fin r → Fin a → ℂ, ∃ Y : Fin r → Fin b → ℂ, ∃ Z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin b → ℂ, ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k=∑ t,(u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  classical
  intro G P Q
  let mark (g₁ g₂ : G) (ne : g₁ ≠ g₂) (j : J) : Q ↪ P :=
    { toFun := Sum.elim (fun i => .inl (g₁,i)) (Sum.elim (fun i => .inl (g₂,i)) (fun _ => .inr j))
      inj' := by
        rintro (i|i|⟨⟩) (k|k|⟨⟩) eq <;> simp_all
        · exact congrArg Sum.inl (congrArg Prod.snd (Sum.inl.inj eq))
        · exact ne (congrArg Prod.fst (Sum.inl.inj eq))
        · exact ne (congrArg Prod.fst (Sum.inl.inj eq)).symm
        · exact congrArg (fun i : H => (Sum.inr (Sum.inl i) : Q)) (congrArg Prod.snd (Sum.inl.inj eq)) }
  rintro ⟨first,x₀,y₀,one⟩
  let weights : Matrix Bool Q ℂ := fun w => Sum.elim (fun _ => if w then 0 else 1)
    (Sum.elim (fun _ => if w then 1 else 0) (fun _ => 1))
  have total (F : Q → Fin a × Fin b → ℂ) (w : Bool) :
      ∑ t, weights w t • F t = (if w then ∑ i : H, F (.inr (.inl i)) else ∑ i : H, F (.inl i)) +
        F (.inr (.inr ())) := by
    cases w <;> simp [weights,Q,Fintype.sum_sum_type]
  obtain ⟨x,y,allMarks⟩ := common_weighted_markings weights first
    ⟨x₀,y₀,fun F ht hr hc hsum => one F ht hr hc
      (by simpa only [total,Bool.false_eq_true,if_false] using hsum false)
      (by simpa only [total,if_true] using hsum true)⟩
  let A : Matrix G P ℂ := fun g => Sum.elim (fun q => if q.1=g then 1 else 0) (fun j =>
    g.elim (fun l => if j=l then 1 else 0) (Sum.elim (fun l => if j=l then 1 else 0) (fun _ => 0)))
  let pivot (g : G) : P := .inl (g,Classical.choice ‹Nonempty H›)
  have onto : Function.Surjective A.mulVec := by
    apply surjective_of_pivots A pivot
    intro g j
    change (if j=g then (1:ℂ) else 0) = if g=j then 1 else 0
    by_cases h : g=j
    · subst j; simp
    · simp [h,Ne.symm h]
  apply spans_of_weighted_normals x y A onto
  intro F outer rows cols rel
  have row (g : G) : (∑ i, F (.inl (g,i))) +
      g.elim (fun j => F (.inr j)) (Sum.elim (fun j => F (.inr j)) (fun _ => 0))=0 := by
    have base : (∑ t : G × H, (if t.1=g then (1:ℂ) else 0) • F (.inl t)) =
        ∑ i, F (.inl (g,i)) := by
      rw [Fintype.sum_prod_type,Finset.sum_eq_single g]
      · simp
      · intro g' _ hne; simp [hne]
      · simp
    have h := rel g
    rw [Fintype.sum_sum_type] at h
    simp only [A,Sum.elim_inl,Sum.elim_inr] at h
    rw [base] at h
    rcases g with l|l|o <;> simpa [ite_smul] using h
  have vanish (g₁ g₂ : G) (ne : g₁≠g₂) (j : J)
      (h₁ : (∑ i, F (.inl (g₁,i)))+F (.inr j)=0)
      (h₂ : (∑ i, F (.inl (g₂,i)))+F (.inr j)=0) :
      ∀ t, F (mark g₁ g₂ ne j t)=0 := by
    let e := mark g₁ g₂ ne j
    have test := allMarks e (fun t => F (e t)) (fun t => outer (e t))
      (fun t => rows (e t)) (fun t => cols (e t)) (fun w => (total _ w).trans (by
        cases w
        · exact h₁
        · exact h₂))
    exact fun t => congrFun test t
  have full (j : J) := vanish (.inl j) (.inr (.inl j)) (by simp) j (row _) (row _)
  funext p
  rcases p with ⟨j|j|o,i⟩|j
  · exact full j (.inl i)
  · exact full j (.inr (.inl i))
  · let j : J := Classical.choice ‹Nonempty J›
    have shared : F (.inr j)=0 := full j (.inr (.inr ()))
    have unpaired : (∑ i, F (.inl (.inr (.inr o),i)))+F (.inr j)=0 := by
      simpa only [shared,Sum.elim_inr] using row (.inr (.inr o))
    exact vanish (.inr (.inr o)) (.inl j) (by simp) j unpaired (row _) (.inl i)
  · exact full j (.inr (.inr ()))

end CriticalLastSlice.TwoPlanes


namespace CriticalLastSlice.TwoPlanes

/-- Finite-index form of the odd construction, expressed using the original
r sampled points and n third coordinates. -/
theorem spans_of_paired_marking {a b r n h e f : ℕ} (hn : n≤r) (hh : 0<h) (he : 0<e)
    (rows : r-n=2*e+f) (points : r=(r-n)*h+e)
    (one : ∃ mark : (Fin h ⊕ Fin h ⊕ Unit) ↪ Fin r,
      ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
      ∀ F : (Fin h ⊕ Fin h ⊕ Unit) → Fin a × Fin b → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin b,(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) → (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) →
        (∑ i : Fin h,F (.inl i))+F (.inr (.inr ()))=0 →
        (∑ i : Fin h,F (.inr (.inl i)))+F (.inr (.inr ()))=0 → F=0) :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
        ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k=∑ t,(u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  classical
  let : Nonempty (Fin h) := ⟨⟨0,hh⟩⟩
  let : Nonempty (Fin e) := ⟨⟨0,he⟩⟩
  let G := Fin e ⊕ Fin e ⊕ Fin f
  let P := (G × Fin h) ⊕ Fin e
  have crow : Fintype.card G=r-n := (coupled_card e f h).1.trans rows.symm
  have cpoint : Fintype.card P=r := (coupled_card e f h).2.trans (by rw [← rows,← points])
  let index : P ≃ Fin r := (Fintype.equivFin P).trans (finCongr cpoint)
  obtain ⟨first,x,y,good⟩ := one
  have hit := spans_of_single_paired_marking (J:=Fin e) (O:=Fin f) (H:=Fin h) (a:=a) (b:=b)
    ⟨first.trans index.symm.toEmbedding,fun p => x (index p),fun p => y (index p),by
      intro F outer row col
      apply good F
      · intro t s
        obtain ⟨p,rfl⟩ := index.surjective s
        exact outer t p
      · simpa only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.apply_symm_apply] using row
      · simpa only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.apply_symm_apply] using col⟩
  change ∃ x : Fin (Fintype.card P) → Fin a → ℂ, ∃ y : Fin (Fintype.card P) → Fin b → ℂ,
    ∃ z : Fin (Fintype.card P) → Fin (Fintype.card P-Fintype.card G) → ℂ, _ at hit
  rw [cpoint,crow,show r-(r-n)=n by omega] at hit
  exact hit

/-- The scalar dimension bound reduces every format to one local configuration.
One ordinary marking with enough capacity suffices in the disjoint case.
The odd overflow case uses two floor((a+b)/2) batches and one shared point. -/
theorem spans_of_capacity_markings {a b r n : ℕ} (hn : n≤r) (budget : 2*r≤(r-n)*(a+b)) :
    let h := (a+b)/2
    (r≤(r-n)*h → ∃ m : ℕ, r≤(r-n)*m ∧ ∃ mark : Fin m ↪ Fin r,
      ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∀ F : Fin m → Fin a × Fin b → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin b,(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) → (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) →
        (∑ t,F t)=0 → F=0) →
    ((r-n)*h<r → ∃ mark : (Fin h ⊕ Fin h ⊕ Unit) ↪ Fin r,
      ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
      ∀ F : (Fin h ⊕ Fin h ⊕ Unit) → Fin a × Fin b → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin b,(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) → (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) →
        (∑ i : Fin h,F (.inl i))+F (.inr (.inr ()))=0 →
        (∑ i : Fin h,F (.inr (.inl i)))+F (.inr (.inr ()))=0 → F=0) →
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
        ∃ w : Fin r → Fin n → ℂ, ∀ i j k,
          T i j k=∑ t,(u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  classical
  intro h ordinary coupled
  by_cases fit : r≤(r-n)*h
  · obtain ⟨m,room,first,x,y,good⟩ := ordinary fit
    obtain ⟨label,onto,bound⟩ := LastSliceBatch.balanced_partition (Nat.sub_le r n) room
    have size (g : Fin (r-n)) :
        Fintype.card {t : Fin r // label t=g} ≤ Fintype.card (Fin m) := by
      simpa only [Fintype.card_fin] using bound g
    obtain ⟨X,Y,direct⟩ := LastSliceBatch.common_small_fibers first label size ⟨x,y,good⟩
    have hit := LastSliceBatch.spans_of_ragged_independence label onto X Y direct
    rw [Fintype.card_fin r,Fintype.card_fin (r-n),show r-(r-n)=n by omega] at hit
    exact hit
  · rcases capacity_cases budget with hfit|⟨e,f,he,_,rows,points⟩
    · exact (fit hfit).elim
    · change r=(r-n)*h+e at points
      have hh : 0<h := by
        by_contra! hz
        rw [show h=0 by omega,Nat.mul_zero,Nat.zero_add] at points
        omega
      exact spans_of_paired_marking hn hh he rows points (coupled (by omega))

end CriticalLastSlice.TwoPlanes

namespace CriticalHigher.Blocks

open MvPolynomial

/-- A full-row-rank specialization gives a nonzero determinant polynomial.
Taking the product gives one specialization for a finite family of matrices. -/
theorem common_surjective {G V : Type*} [Fintype G] {I J : G → Type*}
    [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (M : ∀ g, Matrix (I g) (J g) (MvPolynomial V ℂ))
    (each : ∀ g, ∃ v : V → ℂ, Function.Surjective ((M g).map (eval v)).mulVec) :
    ∃ p : V → ℂ, ∀ g, Function.Surjective ((M g).map (eval p)).mulVec := by
  classical
  choose v good using each
  choose B inverse using fun g => Matrix.mulVec_surjective_iff_exists_right_inverse.mp (good g)
  let P (g : G) := (B g).map (C : ℂ →+* MvPolynomial V ℂ)
  let Q (g : G) := (M g*P g).det
  have spec (g : G) (u : V → ℂ) :
      eval u (Q g) = ((M g).map (eval u)*B g).det := by
    have constant : (P g).map (eval u)=B g := by ext; simp [P,Matrix.map_apply]
    change eval u (M g*P g).det = _
    rw [RingHom.map_det,RingHom.mapMatrix_apply,Matrix.map_mul,constant]
  have nz (g : G) : Q g≠0 := by
    intro zero
    have atPoint := spec g (v g)
    rw [zero,map_zero,inverse g,Matrix.det_one] at atPoint
    exact zero_ne_one atPoint
  have allnz : (∏ g,Q g)≠0 := Finset.prod_ne_zero_iff.mpr fun g _ => nz g
  obtain ⟨p,hp⟩ : ∃ p : V → ℂ, eval p (∏ g,Q g)≠0 := by
    by_contra! vanish
    exact allnz (MvPolynomial.funext fun q => by rw [vanish q,map_zero])
  have eachnz : (∏ g,eval p (Q g))≠0 := by simpa only [map_prod] using hp
  refine ⟨p,fun g => ?_⟩
  have hdet := Finset.prod_ne_zero_iff.mp eachnz g (Finset.mem_univ g)
  rw [spec] at hdet
  have onto := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  intro t
  obtain ⟨s,hs⟩ := onto t
  exact ⟨(B g).mulVec s,(Matrix.mulVec_mulVec _ _ _).trans hs⟩

end CriticalHigher.Blocks

namespace CriticalHigher.Blocks

/-- Reindex a full tangent plus an external-product supplement onto any
finite point set, allowing the first two variations only on its marked set. -/
private theorem restricted_tangent_of_split {A B C P M N : Type*}
    [Fintype P] [Fintype M] [Fintype N] (active : P → Prop) [DecidablePred active]
    (e : (M ⊕ N) ≃ P) (marked : ∀ t : M, active (e (.inl t)))
    (one : ∃ x : M → A → ℂ, ∃ y : M → B → ℂ, ∃ z : M → C → ℂ,
      ∃ x' : N → A → ℂ, ∃ y' : N → B → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : M → A → ℂ, ∃ v : M → B → ℂ, ∃ w : M → C → ℂ,
      ∃ w' : N → C → ℂ, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k)) :
    ∃ X : P → A → ℂ, ∃ Y : P → B → ℂ, ∃ Z : P → C → ℂ,
      ∀ T : A → B → C → ℂ, ∃ u : P → A → ℂ, ∃ v : P → B → ℂ, ∃ w : P → C → ℂ, ∀ i j k,
      T i j k = ∑ t, ((if active t then u t i*(Y t j*Z t k)+X t i*(v t j*Z t k) else 0) +
        X t i*(Y t j*w t k)) := by
  obtain ⟨x,y,z,x',y',hit⟩ := one
  let X (p : P) := (e.symm p).elim x x'
  let Y (p : P) := (e.symm p).elim y y'
  let Z (p : P) := (e.symm p).elim z 0
  refine ⟨X,Y,Z,?_⟩
  intro T
  obtain ⟨u,v,w,w',cover⟩ := hit T
  refine ⟨fun p => (e.symm p).elim u 0,fun p => (e.symm p).elim v 0,fun p => (e.symm p).elim w w',?_⟩
  intro i j k
  rw [cover i j k,← e.sum_comp,Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    simp only [X,Y,Z,Equiv.symm_apply_apply,Sum.elim_inl,if_pos (marked t)]
  · apply Finset.sum_congr rfl
    intro t _
    simp [X,Y,Z]

end CriticalHigher.Blocks

namespace CriticalHigher.Blocks

open MvPolynomial

/-- The open full-rank conditions for independent coordinate blocks
remain compatible when their dimensions differ. An unassigned point
contributes only its freely chosen last-factor variation. -/
theorem different_common_tangents {A B P G : Type*} {C : G → Type*}
    [Fintype A] [Fintype B] [Fintype P] [Fintype G] [∀ g,Fintype (C g)] [DecidableEq G]
    (label : P → Option G) :
    let D (g : G) (x : P→A→ℂ) (y : P→B→ℂ) (z : P→C g→ℂ) :=
      ∀ T : A→B→C g→ℂ, ∃ u : P→A→ℂ, ∃ v : P→B→ℂ, ∃ w : P→C g→ℂ, ∀ i j k,
        T i j k=∑ t, ((if label t=some g then u t i*(y t j*z t k)+x t i*(v t j*z t k) else 0)
          +x t i*(y t j*w t k))
    (∀ g,∃ x y z,D g x y z) → ∃ x y, ∃ z : ∀ g,P→C g→ℂ, ∀ g,D g x y (z g) := by
  classical
  intro D each
  let V := (P×A) ⊕ (P×B) ⊕ ((g : G) × (P×C g))
  let J (g : G) := P × (A ⊕ B ⊕ C g)
  let M (g : G) : Matrix ((A×B)×C g) (J g) (MvPolynomial V ℂ) := fun row col => col.2.elim
    (fun i => if label col.1=some g ∧ i=row.1.1 then
      X (.inr (.inl (col.1,row.1.2)))*X (.inr (.inr ⟨g,col.1,row.2⟩)) else 0)
    (Sum.elim (fun j => if label col.1=some g ∧ j=row.1.2 then
      X (.inl (col.1,row.1.1))*X (.inr (.inr ⟨g,col.1,row.2⟩)) else 0)
      (fun k => if k=row.2 then X (.inl (col.1,row.1.1))*X (.inr (.inl (col.1,row.1.2))) else 0))
  let x (p : V → ℂ) (t : P) (i : A) := p (.inl (t,i))
  let y (p : V → ℂ) (t : P) (j : B) := p (.inr (.inl (t,j)))
  let z (p : V → ℂ) (g : G) (t : P) (k : C g) := p (.inr (.inr ⟨g,t,k⟩))
  have action (g : G) (p : V→ℂ) (q : J g→ℂ) (i : A) (j : B) (k : C g) :
      ((M g).map (eval p)).mulVec q ((i,j),k)=∑ t,
        ((if label t=some g then q (t,.inl i)*(y p t j*z p g t k)+
           x p t i*(q (t,.inr (.inl j))*z p g t k) else 0)+
           x p t i*(y p t j*q (t,.inr (.inr k)))) := by
    change (∑ s : J g, eval p (M g ((i,j),k) s)*q s)=_
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    by_cases hit : label t=some g <;> simp [M,hit,x,y,z,apply_ite,ite_mul,Finset.sum_ite_eq'] <;> ring
  have full (g : G) : ∃ p : V→ℂ, Function.Surjective ((M g).map (eval p)).mulVec := by
    obtain ⟨X₀,Y₀,Z₀,good⟩ := each g
    let Zs : ∀ g,P→C g→ℂ := Function.update (fun _ _ _ => 0) g Z₀
    let p : V→ℂ := Sum.elim (fun t => X₀ t.1 t.2)
      (Sum.elim (fun t => Y₀ t.1 t.2) (fun t => Zs t.1 t.2.1 t.2.2))
    have back (t : P) (k : C g) : z p g t k=Z₀ t k := by simp [z,p,Zs]
    refine ⟨p,?_⟩
    intro T
    obtain ⟨u,v,w,repr⟩ := good fun i j k => T ((i,j),k)
    let q : J g→ℂ := fun s => s.2.elim (u s.1) (Sum.elim (v s.1) (w s.1))
    refine ⟨q,?_⟩
    funext ⟨⟨i,j⟩,k⟩
    rw [action]
    simpa only [back,q,x,y,p,Sum.elim_inl,Sum.elim_inr] using (repr i j k).symm
  obtain ⟨p,onto⟩ := common_surjective M full
  refine ⟨x p,y p,z p,?_⟩
  intro g T
  obtain ⟨q,hq⟩ := onto g fun row => T row.1.1 row.1.2 row.2
  exact ⟨fun t i => q (t,.inl i),fun t j => q (t,.inr (.inl j)),fun t k => q (t,.inr (.inr k)),
    fun i j k => (congrFun hq ((i,j),k)).symm.trans (action g p q i j k)⟩

/-- Spanning in each coordinate block gives a spanning tangent in the full
tensor. Both the block widths and the numbers of assigned points may vary. -/
theorem spans_of_different_blocks {A B P G : Type*} {C : G→Type*} [Fintype A] [Fintype B]
    [Fintype P] [Fintype G] [∀ g,Fintype (C g)] [DecidableEq G] (label : P→Option G)
    (one : ∀ g, ∃ x : P→A→ℂ, ∃ y : P→B→ℂ, ∃ z : P→C g→ℂ,
      ∀ T : A→B→C g→ℂ, ∃ u : P→A→ℂ, ∃ v : P→B→ℂ, ∃ w : P→C g→ℂ, ∀ i j k,
        T i j k=∑ t,((if label t=some g then u t i*(y t j*z t k)+x t i*(v t j*z t k) else 0)+
          x t i*(y t j*w t k))) :
    ∃ x : P→A→ℂ, ∃ y : P→B→ℂ, ∃ Z : P→((g : G) × C g)→ℂ,
      ∀ T : A→B→((g : G) × C g)→ℂ, ∃ u : P→A→ℂ, ∃ v : P→B→ℂ,
        ∃ w : P→((g : G) × C g)→ℂ, ∀ i j k,
          T i j k=∑ t,(u t i*(y t j*Z t k)+x t i*(v t j*Z t k)+x t i*(y t j*w t k)) := by
  classical
  obtain ⟨x,y,z,good⟩ := different_common_tangents label one
  let Z (t : P) (p : (g : G) × C g) := if label t=some p.1 then z p.1 t p.2 else 0
  refine ⟨x,y,Z,?_⟩
  intro T
  choose U V W repr using fun g => good g fun i j k => T i j ⟨g,k⟩
  refine ⟨fun t => (label t).elim 0 (fun g => U g t),fun t => (label t).elim 0 (fun g => V g t),
    fun t k => W k.1 t k.2,?_⟩
  rintro i j ⟨g,k⟩
  apply (repr g i j k).trans
  apply Finset.sum_congr rfl
  intro t _
  by_cases hit : label t=some g <;> simp [Z,hit]

end CriticalHigher.Blocks

namespace CriticalHigher.Blocks

/-- Enumerate the complement of any fixed embedded family of m marks.
Under the equivalence each initial mark keeps its specified image. -/
private theorem block_complement_fin {P : Type*} [Fintype P] (m r : ℕ)
    (points : Fintype.card P=r) (f : Fin m → P) (inj : Function.Injective f) :
    ∃ e : (Fin m ⊕ Fin (r-m)) ≃ P, ∀ j, e (.inl j)=f j := by
  classical
  let first := Equiv.ofInjective f inj
  have count : Fintype.card {p : P // p∈Set.range f}=m := by
    rw [← Fintype.card_congr first,Fintype.card_fin]
  let last : {p : P // p∉Set.range f} ≃ Fin (r-m) := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype_compl,count,points])
  exact ⟨(Equiv.sumCongr first last.symm).trans (Equiv.sumCompl (fun p => p ∈ Set.range f)),fun _ => rfl⟩

/-- Dissimilar blocks can be assembled using independent local tests, each
with its prescribed full marks and all remaining points as external products. -/
theorem different_block_tangent (a b g r : ℕ) (width mark : Fin g → ℕ)
    (slots : (∑ q, mark q) ≤ r)
    (each : ∀ q : Fin g,
      ∃ x : Fin (mark q) → Fin a → ℂ, ∃ y : Fin (mark q) → Fin b → ℂ, ∃ z : Fin (mark q) → Fin (width q) → ℂ,
      ∃ x' : Fin (r-mark q) → Fin a → ℂ, ∃ y' : Fin (r-mark q) → Fin b → ℂ,
      ∀ T : Fin a → Fin b → Fin (width q) → ℂ, ∃ u : Fin (mark q) → Fin a → ℂ, ∃ v : Fin (mark q) → Fin b → ℂ,
      ∃ w : Fin (mark q) → Fin (width q) → ℂ, ∃ w' : Fin (r-mark q) → Fin (width q) → ℂ, ∀ i j k,
        T i j k=(∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k)) :
    ∃ X : Fin r → Fin a → ℂ, ∃ Y : Fin r → Fin b → ℂ, ∃ Z : Fin r → Fin (∑ q, width q) → ℂ,
      ∀ T : Fin a → Fin b → Fin (∑ q, width q) → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
      ∃ w : Fin r → Fin (∑ q, width q) → ℂ, ∀ i j k,
        T i j k=∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  classical
  let P := (Σ q : Fin g, Fin (mark q)) ⊕ Fin (r-∑ q,mark q)
  let label : P → Option (Fin g) := Sum.elim (fun p => some p.1) (fun _ => none)
  have size : Fintype.card P=r := by
    simp only [P,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin]
    omega
  have localPoint (q : Fin g) :
      ∃ X : P → Fin a → ℂ, ∃ Y : P → Fin b → ℂ, ∃ Z : P → Fin (width q) → ℂ,
      ∀ T : Fin a → Fin b → Fin (width q) → ℂ, ∃ u : P → Fin a → ℂ, ∃ v : P → Fin b → ℂ,
      ∃ w : P → Fin (width q) → ℂ, ∀ i j k,
        T i j k=∑ t, ((if label t=some q then u t i*(Y t j*Z t k)+X t i*(v t j*Z t k) else 0) +
          X t i*(Y t j*w t k)) := by
    let f : Fin (mark q) → P := fun j => .inl ⟨q,j⟩
    have inject : Function.Injective f := by
      intro u v eq
      have pair : (⟨q,u⟩ : Σ i : Fin g, Fin (mark i)) = ⟨q,v⟩ := Sum.inl.inj eq
      exact eq_of_heq (Sigma.mk.inj_iff.mp pair).2
    obtain ⟨e,marked⟩ := block_complement_fin (mark q) r size f inject
    apply restricted_tangent_of_split (fun s => label s=some q) e _ (each q)
    intro j
    rw [marked]
    rfl
  obtain ⟨x,y,z,hit⟩ := spans_of_different_blocks (C:=fun q => Fin (width q)) label localPoint
  let points : P ≃ Fin r := Fintype.equivFinOfCardEq size
  let coords : (Σ q : Fin g, Fin (width q)) ≃ Fin (∑ q,width q) :=
    Fintype.equivFinOfCardEq (by simp)
  refine ⟨fun t => x (points.symm t),fun t => y (points.symm t),
    fun t k => z (points.symm t) (coords.symm k),?_⟩
  intro T
  obtain ⟨u,v,w,cover⟩ := hit fun i j k => T i j (coords k)
  refine ⟨fun t => u (points.symm t),fun t => v (points.symm t),
    fun t k => w (points.symm t) (coords.symm k),?_⟩
  intro i j k
  have eq := cover i j (coords.symm k)
  simp only [Equiv.apply_symm_apply] at eq
  rw [eq,←points.sum_comp]
  simp only [Equiv.symm_apply_apply]

end CriticalHigher.Blocks

namespace HigherPencil

/-- A tensor annihilating the three tangent variations at each marked point
and the third variation at each exterior point detects surjectivity of their sum. -/
theorem augmented_span_of_annihilator {𝕜 I J K P Q : Type*} [Field 𝕜]
    [Fintype I] [Fintype J] [Fintype K] [Fintype P] [Fintype Q]
    (x : P → I → 𝕜) (y : P → J → 𝕜) (z : P → K → 𝕜) (x' : Q → I → 𝕜) (y' : Q → J → 𝕜)
    (detect : ∀ H : I → J → K → 𝕜,
      (∀ t i, ∑ j, ∑ k, (y t j*z t k)*H i j k=0) →
      (∀ t j, ∑ i, ∑ k, (x t i*z t k)*H i j k=0) →
      (∀ t k, ∑ i, ∑ j, (x t i*y t j)*H i j k=0) →
      (∀ t k, ∑ i, ∑ j, (x' t i*y' t j)*H i j k=0) → H=0) :
    ∀ T : I → J → K → 𝕜,
      ∃ u : P → I → 𝕜, ∃ v : P → J → 𝕜, ∃ w : P → K → 𝕜, ∃ w' : Q → K → 𝕜, ∀ i j k,
        T i j k = (∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) +
          ∑ t, x' t i*(y' t j*w' t k) := by
  classical
  let C := (P × I) ⊕ ((P × J) ⊕ ((P × K) ⊕ (Q × K)))
  let M : Matrix (I × J × K) C 𝕜
    | (i,j,k),.inl (t,h) => if h=i then y t j*z t k else 0
    | (i,j,k),.inr (.inl (t,h)) => if h=j then x t i*z t k else 0
    | (i,j,k),.inr (.inr (.inl (t,h))) => if h=k then x t i*y t j else 0
    | (i,j,k),.inr (.inr (.inr (t,h))) => if h=k then x' t i*y' t j else 0
  have no_rel (v : I × J × K → 𝕜) (hv : M.transpose.mulVec v=0) : v=0 := by
    let H (i : I) (j : J) (k : K) := v (i,j,k)
    have read (c : C) : (∑ q : I × J × K, M q c * v q)=0 := congrFun hv c
    have zero := detect H
      (fun t i => by simpa [H,M,Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel] using read (.inl (t,i)))
      (fun t j => by simpa [H,M,Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel] using read (.inr (.inl (t,j))))
      (fun t k => by simpa [H,M,Fintype.sum_prod_type,ite_mul] using read (.inr (.inr (.inl (t,k)))))
      (fun t k => by simpa [H,M,Fintype.sum_prod_type,ite_mul] using read (.inr (.inr (.inr (t,k)))))
    funext ⟨i,j,k⟩
    exact congrFun (congrFun (congrFun zero i) j) k
  have ker : LinearMap.ker M.transpose.mulVecLin=⊥ := by
    apply bot_unique
    intro u hu
    exact (Submodule.mem_bot 𝕜).mpr (no_rel u hu)
  have size := LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp ker)
  change M.transpose.rank=Module.finrank 𝕜 (I × J × K → 𝕜) at size
  rw [Matrix.rank_transpose] at size
  have onto : Function.Surjective M.mulVec := LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq size)
  intro T
  obtain ⟨p,hp⟩ := onto (fun q => T q.1 q.2.1 q.2.2)
  refine ⟨fun t i => p (.inl (t,i)),fun t j => p (.inr (.inl (t,j))),
    fun t k => p (.inr (.inr (.inl (t,k)))),fun t k => p (.inr (.inr (.inr (t,k)))),?_⟩
  intro i j k
  refine (congrFun hp (i,j,k)).symm.trans ?_
  change (∑ q : (P × I) ⊕ ((P × J) ⊕ ((P × K) ⊕ (Q × K))), M (i,j,k) q*p q)=_
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,M,ite_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,if_true,Finset.sum_add_distrib]
  simp only [mul_assoc,mul_comm,add_assoc]

end HigherPencil

namespace CriticalThreeQuotient

/-- Enumerate exactly the samples outside the chosen marks. -/
private lemma exterior_embedding {A M : Type*} [Fintype A] [Fintype M] (e : M ↪ A) :
    ∃ f : Fin (Fintype.card A-Fintype.card M) ↪ A, Set.range f = (Set.range e)ᶜ := by
  classical
  let C := {s : A // s ∉ Set.range e}
  let g : C ≃ Fin (Fintype.card A-Fintype.card M) := Fintype.equivFinOfCardEq (by
    change Fintype.card {s : A // s ∉ Set.range e} = _
    rw [Fintype.card_subtype_compl,← Fintype.card_congr e.toEquivRange])
  let f := g.symm.toEmbedding.trans (Function.Embedding.subtype (fun s : A => s ∉ Set.range e))
  refine ⟨f, Set.ext fun s => ⟨?_,?_⟩⟩
  · rintro ⟨p,rfl⟩
    exact (g.symm p).property
  · intro hs
    refine ⟨g ⟨s,hs⟩,?_⟩
    change (g.symm (g ⟨s,hs⟩)).val = s
    rw [Equiv.symm_apply_apply]

/-- Contract the physical normal against the marked third factors. All
samples impose product equations, while only marks impose the two arm
equations. Every relation of the third factors couples the contracted forms. -/
lemma augmented_of_contracted {K I J A M N G : Type*} [Field K]
    [Fintype I] [Fintype J] [Fintype A] [Fintype M] [Fintype N]
    (e : M ↪ A) (x : A → I → K) (y : A → J → K) (Z : Matrix M N K)
    (Q : Matrix G M K) (qZ : Q*Z=0)
    (detect : ∀ (H : I → J → N → K) (F : M → I×J → K),
      (∀ t i j, F t (i,j) = ∑ k, Z t k*H i j k) →
      (∀ t s, (∑ ij, (x s ij.1*y s ij.2)*F t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*F t (i,j))=0) →
      (∀ t j, (∑ i, x (e t) i*F t (i,j))=0) →
      (∀ q, (∑ t, Q q t • F t)=0) → H=0) :
    ∃ f : Fin (Fintype.card A-Fintype.card M) ↪ A, Set.range f = (Set.range e)ᶜ ∧
      ∀ T : I → J → N → K,
      ∃ u : M → I → K, ∃ v : M → J → K, ∃ w : M → N → K,
      ∃ w' : Fin (Fintype.card A-Fintype.card M) → N → K, ∀ i j k,
        T i j k = (∑ t, (u t i*(y (e t) j*Z t k)+x (e t) i*(v t j*Z t k)+x (e t) i*(y (e t) j*w t k))) +
          ∑ t, x (f t) i*(y (f t) j*w' t k) := by
  classical
  obtain ⟨f,hf⟩ := exterior_embedding e
  refine ⟨f,hf,HigherPencil.augmented_span_of_annihilator (fun t => x (e t)) (fun t => y (e t))
    Z (fun p => x (f p)) (fun p => y (f p)) ?_⟩
  intro H xarm yarm marked exterior
  let F (t : M) (ij : I×J) := ∑ k, Z t k*H ij.1 ij.2 k
  have allprod (s : A) (k : N) : (∑ ij : I×J, (x s ij.1*y s ij.2)*H ij.1 ij.2 k)=0 := by
    rw [Fintype.sum_prod_type]
    by_cases hs : s ∈ Set.range e
    · obtain ⟨t,rfl⟩ := hs
      exact marked t k
    · have hm : s ∈ Set.range f := by rw [hf]; exact hs
      obtain ⟨p,rfl⟩ := hm
      exact exterior p k
  refine detect H F (fun _ _ _ => rfl) ?_ ?_ ?_ ?_
  · intro t s
    calc
      _ = ∑ k, Z t k*(∑ ij : I×J, (x s ij.1*y s ij.2)*H ij.1 ij.2 k) := by
        simp only [F,Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro ij _
        ring
      _ = 0 := by simp [allprod]
  · intro t i
    simpa only [F,Finset.mul_sum,mul_assoc] using xarm t i
  · intro t j
    simpa only [F,Finset.mul_sum,mul_assoc] using yarm t j
  · intro q
    funext ij
    have zero (k : N) : (∑ t, Q q t*Z t k)=0 := congrFun (congrFun qZ q) k
    change (∑ t, Q q t • F t) ij = 0
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    calc
      _ = ∑ k, (∑ t, Q q t*Z t k)*H ij.1 ij.2 k := by
        simp only [F,Finset.mul_sum,Finset.sum_mul,mul_assoc]
        rw [Finset.sum_comm]
      _ = 0 := by simp [zero]

/-- Select independent columns in the kernel with arbitrary finite row and column
labels. The selected columns have an explicit matrix left inverse. -/
lemma kernel_frame_finite {K M N G : Type*} [Field K] [Fintype M] [Fintype N] [Fintype G]
    [DecidableEq N] (Q : Matrix G M K)
    (room : Fintype.card N ≤ Fintype.card M-Fintype.card G) :
    ∃ Z : Matrix M N K, ∃ L : Matrix N M K, Q*Z=0 ∧ L*Z=1 := by
  classical
  let F := Q.mulVecLin
  have dims : Module.finrank K F.range+Module.finrank K F.ker=Fintype.card M := by
    simpa only [Module.finrank_fintype_fun_eq_card] using F.finrank_range_add_finrank_ker
  have height : Module.finrank K F.range ≤ Fintype.card G := by
    simpa only [Module.finrank_fintype_fun_eq_card] using F.range.finrank_le
  have fit : Module.finrank K (N → K) ≤ Module.finrank K F.ker := by
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  obtain ⟨g,hg⟩ := finrank_le_iff_exists_linearMap.mp fit
  let f := F.ker.subtype.comp g
  have injective : Function.Injective f := Subtype.val_injective.comp hg
  obtain ⟨L,hL⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr injective)
  refine ⟨LinearMap.toMatrix' f,LinearMap.toMatrix' L,?_,?_⟩
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',map_zero]
    change F.comp f = 0
    apply LinearMap.ext
    intro v
    exact (g v).property
  · rw [← LinearMap.toMatrix'_comp,hL,LinearMap.toMatrix'_id]

/-- Each off-diagonal entry of the three sampled matrices is governed by one
scalar. Marking only some samples leaves the row and column index types distinct. -/
private lemma rectangular_sample_zero {K A M U V : Type*} [Field K] [Fintype A] [Fintype M]
    (e : M ↪ A) (l d : A → K) (distinct : Function.Injective l)
    (P : Matrix U A K) (Q : Matrix V M K)
    (exactPair : ∀ E : A → M → K,
      (∀ u t, (∑ s, P u s*((l s-l (e t))*E s t))=0) →
      (∀ u t, (∑ s, P u s*((d s-d (e t))*E s t))=0) →
      (∀ v s, (∑ t, ((l s-l (e t))*E s t)*Q v t)=0) →
      (∀ v s, (∑ t, ((d s-d (e t))*E s t)*Q v t)=0) →
      ∀ s t, s≠e t → E s t=0)
    (X B C : Matrix A M K)
    (diag : ∀ t, X (e t) t=0 ∧ B (e t) t=0 ∧ C (e t) t=0)
    (row : ∀ s t, X s t+l s*B s t+d s*C s t=0)
    (col : ∀ s t, X s t+l (e t)*B s t+d (e t)*C s t=0)
    (leftB : P*B=0) (leftC : P*C=0) (rightB : B*Q.transpose=0) (rightC : C*Q.transpose=0) :
    ∀ s t, X s t=0 ∧ B s t=0 ∧ C s t=0 := by
  let E (s : A) (t : M) := C s t/(l s-l (e t))
  have entries (s : A) (t : M) :
      C s t=(l s-l (e t))*E s t ∧ (d s-d (e t))*E s t= -B s t := by
    by_cases eq : s=e t
    · subst s
      simp [diag t]
    · have gap : l s-l (e t)≠0 := sub_ne_zero.mpr (distinct.ne eq)
      have hC : C s t=(l s-l (e t))*E s t := by dsimp only [E]; field_simp
      refine ⟨hC,?_⟩
      apply mul_left_cancel₀ gap
      linear_combination (row s t)-(col s t)-(d s-d (e t))*hC
  have left (N : Matrix A M K) (h : P*N=0) (u : U) (t : M) : (∑ s, P u s*N s t)=0 :=
    congrFun (congrFun h u) t
  have right (N : Matrix A M K) (h : N*Q.transpose=0) (v : V) (s : A) : (∑ t, N s t*Q v t)=0 :=
    congrFun (congrFun h s) v
  have eC (s : A) (t : M) := (entries s t).1
  have eB (s : A) (t : M) := (entries s t).2
  have zero := exactPair E
    (fun u t => by simpa only [← eC] using left C leftC u t)
    (fun u t => by simp only [eB,mul_neg,Finset.sum_neg_distrib,left B leftB,neg_zero])
    (fun v s => by simpa only [← eC] using right C rightC v s)
    (fun v s => by simp only [eB,neg_mul,Finset.sum_neg_distrib,right B rightB,neg_zero])
  intro s t
  by_cases eq : s=e t
  · subst s
    exact diag t
  · have zz := entries s t
    rw [zero s t eq,mul_zero,mul_zero] at zz
    have bzero : B s t=0 := by linear_combination zz.2
    exact ⟨by simpa only [bzero,zz.1,mul_zero,add_zero] using row s t,bzero,zz.1⟩

/-- Rectangular commutator certificates suffice for augmented three-slice
tangents. The full sample set and the set of marks have independent index types. -/
lemma rectangular_tangent_of_samples {K A M B N U V : Type*} [Field K]
    [Fintype A] [Fintype M] [Fintype B] [Fintype N]
    (e : M ↪ A) (l d : A → K) (distinct : Function.Injective l)
    (Y : Matrix A B K) (Z : Matrix M N K) (P : Matrix U A K) (Q : Matrix V M K)
    (pY : P*Y=0) (qZ : Q*Z=0) (embed : Function.Injective (fun H : Matrix B N K => Y*H*Z.transpose))
    (exactPair : ∀ E : A → M → K,
      (∀ u t, (∑ s, P u s*((l s-l (e t))*E s t))=0) →
      (∀ u t, (∑ s, P u s*((d s-d (e t))*E s t))=0) →
      (∀ v s, (∑ t, ((l s-l (e t))*E s t)*Q v t)=0) →
      (∀ v s, (∑ t, ((d s-d (e t))*E s t)*Q v t)=0) →
      ∀ s t, s≠e t → E s t=0) :
    let x (s : A) : Fin 3 → K := ![1,l s,d s]
    ∃ f : Fin (Fintype.card A-Fintype.card M) ↪ A, Set.range f = (Set.range e)ᶜ ∧
      ∀ T : Fin 3 → B → N → K,
      ∃ u : M → Fin 3 → K, ∃ v : M → B → K, ∃ w : M → N → K,
      ∃ w' : Fin (Fintype.card A-Fintype.card M) → N → K, ∀ i j k,
        T i j k = (∑ t, (u t i*(Y (e t) j*Z t k)+x (e t) i*(v t j*Z t k)+x (e t) i*(Y (e t) j*w t k))) +
          ∑ t, x (f t) i*(Y (f t) j*w' t k) := by
  classical
  intro x
  apply augmented_of_contracted e x Y Z Q qZ
  intro H F value outer row col coupled
  let D (i : Fin 3) : Matrix B N K := H i
  let R (i : Fin 3) : Matrix B M K := fun j t => F t (i,j)
  let S (i : Fin 3) := Y*R i
  have repr (i : Fin 3) : R i=D i*Z.transpose := by
    ext j t
    change F t (i,j) = ∑ k, H i j k * Z t k
    simpa only [mul_comm] using value t i j
  have entry (i : Fin 3) (s : A) (t : M) : S i s t=∑ j, Y s j*F t (i,j) := rfl
  have sample (s : A) (t : M) : (∑ i, x s i*S i s t)=0 := by
    have h := outer t s
    rw [Fintype.sum_prod_type] at h
    simpa only [entry,Finset.mul_sum,mul_assoc] using h
  have mark (s : A) (t : M) : (∑ i, x (e t) i*S i s t)=0 := by
    simp only [entry,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    calc
      _ = Y s j*(∑ i, x (e t) i*F t (i,j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [col,mul_zero]
  have left (i : Fin 3) : P*S i=0 := by simp [S,← Matrix.mul_assoc,pY]
  have right (i : Fin 3) : S i*Q.transpose=0 := by
    have h : R i*Q.transpose=0 := by
      ext j q
      change (∑ t, F t (i,j)*Q q t)=0
      simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,mul_comm] using
        congrFun (coupled q) (i,j)
    simp only [S,Matrix.mul_assoc,h,Matrix.mul_zero]
  have vanish := rectangular_sample_zero e l d distinct P Q exactPair (S 0) (S 1) (S 2)
    (fun t => ⟨row t 0,row t 1,row t 2⟩)
    (fun s t => by simpa [x,Fin.sum_univ_succ,add_assoc] using sample s t)
    (fun s t => by simpa [x,Fin.sum_univ_succ,add_assoc] using mark s t)
    (left 1) (left 2) (right 1) (right 2)
  have allZero (i : Fin 3) : D i=0 := by
    have z : S i=0 := by
      ext s t
      fin_cases i
      · exact (vanish s t).1
      · exact (vanish s t).2.1
      · exact (vanish s t).2.2
    apply embed
    change Y*D i*Z.transpose=Y*0*Z.transpose
    simpa only [Matrix.mul_zero,Matrix.zero_mul,S,repr,Matrix.mul_assoc] using z
  funext i j k
  exact congrFun (congrFun (allZero i) j) k

/-- Choose both rectangular frames from the two relation matrices. The
bounds are on the number of relation rows, with no independence assumption. -/
lemma rectangular_tangent_of_kernel_samples {K A M B N U V : Type*} [Field K]
    [Fintype A] [Fintype M] [Fintype B] [Fintype N] [Fintype U] [Fintype V]
    (hb : Fintype.card B ≤ Fintype.card A-Fintype.card U)
    (hn : Fintype.card N ≤ Fintype.card M-Fintype.card V)
    (e : M ↪ A) (l d : A → K) (distinct : Function.Injective l) (P : Matrix U A K) (Q : Matrix V M K)
    (exactPair : ∀ E : A → M → K,
      (∀ u t, (∑ s, P u s*((l s-l (e t))*E s t))=0) →
      (∀ u t, (∑ s, P u s*((d s-d (e t))*E s t))=0) →
      (∀ v s, (∑ t, ((l s-l (e t))*E s t)*Q v t)=0) →
      (∀ v s, (∑ t, ((d s-d (e t))*E s t)*Q v t)=0) →
      ∀ s t, s≠e t → E s t=0) :
    let x (s : A) : Fin 3 → K := ![1,l s,d s]
    ∃ Y : Matrix A B K, ∃ Z : Matrix M N K, ∃ f : Fin (Fintype.card A-Fintype.card M) ↪ A, ∀ T : Fin 3 → B → N → K,
      ∃ u : M → Fin 3 → K, ∃ v : M → B → K, ∃ w : M → N → K,
      ∃ w' : Fin (Fintype.card A-Fintype.card M) → N → K, ∀ i j k,
        T i j k = (∑ t, (u t i*(Y (e t) j*Z t k)+x (e t) i*(v t j*Z t k)+x (e t) i*(Y (e t) j*w t k))) +
          ∑ t, x (f t) i*(Y (f t) j*w' t k) := by
  classical
  intro x
  obtain ⟨Y,L,pY,left⟩ := kernel_frame_finite P hb
  obtain ⟨Z,R,qZ,right⟩ := kernel_frame_finite Q hn
  have recover (H : Matrix B N K) : L*(Y*H*Z.transpose)*R.transpose=H := by
    calc
      _ = (L*Y)*H*(R*Z).transpose := by simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _ = H := by rw [left,right,Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one]
  have embed : Function.Injective (fun H : Matrix B N K => Y*H*Z.transpose) :=
    fun H J h => (recover H).symm.trans ((congrArg (fun C => L*C*R.transpose) h).trans (recover J))
  obtain ⟨f,_,span⟩ := rectangular_tangent_of_samples e l d distinct Y Z P Q pY qZ embed exactPair
  exact ⟨Y,Z,f,span⟩

end CriticalThreeQuotient

namespace CriticalThreeBatch

/-- Removing one sample and one pole keeps the same quadratic row with
the updated coefficient `a+x+v`. The removed entry of the new vector is zero. -/
private theorem shift_private_vector {K I : Type*} [Field K] [Fintype I]
    (t f : I → K) (a x v : K) (regular : ∀ i, t i+v≠0)
    (mass : (∑ i, f i)=0) (hub : (∑ i, (t i^2+a*t i)*f i)=0)
    (atPole : (∑ i, f i/(t i+v))=0) :
    let d (i : I) := (t i-x)/(t i+v)*f i
    (∑ i, d i)=0 ∧ (∑ i, (t i^2+(a+x+v)*t i)*d i)=0 ∧
      ∀ y : K, y≠v → (∀ i, t i+y≠0) → (∑ i, f i/(t i+y))=0 → (∑ i, d i/(t i+y))=0 := by
  intro d
  have scale (i : I) : (t i+v)*d i=(t i-x)*f i := by
    dsimp only [d]
    field_simp [regular i]
  have first : (∑ i, d i)=0 := by
    calc
      _ = ∑ i, (f i-(x+v)*(f i/(t i+v))) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [d]
        field_simp [regular i]
        ring
      _ = 0 := by rw [Finset.sum_sub_distrib,← Finset.mul_sum,mass,atPole,mul_zero,sub_zero]
  refine ⟨first,?_,?_⟩
  · calc
      _ = ∑ i, ((t i^2+a*t i)*f i-x*(a+x)*f i-v*(a+x)*d i) := by
        apply Finset.sum_congr rfl
        intro i _
        linear_combination (t i+a+x)*scale i
      _ = 0 := by
        rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,hub,mass,first]
        ring
  · intro y different off hit
    have eq : (y-v)*(∑ i, d i/(t i+y))=0 := by
      calc
        _ = ∑ i, ((y+x)*(f i/(t i+y))-(v+x)*(f i/(t i+v))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [d]
          field_simp [regular i,off i]
          ring
        _ = 0 := by rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,hit,atPole,mul_zero,mul_zero,sub_zero]
    exact (mul_eq_zero.mp eq).resolve_left (sub_ne_zero.mpr different)

private theorem private_no_poles {K : Type*} [Field K] {n : ℕ} (t : Fin n → K) (a : K)
    (inj : Function.Injective t) (size : n≤2) (edge : n=2 → a+(∑ i,t i)≠0)
    (f : Fin n → K) (mass : (∑ i, f i)=0) (hub : (∑ i, (t i^2+a*t i)*f i)=0) : f=0 := by
  interval_cases n
  · exact Subsingleton.elim _ _
  · funext i
    fin_cases i
    change f 0=0
    simpa only [Fin.sum_univ_one] using mass
  · rw [Fin.sum_univ_two] at hub mass
    have sumne : a+t 0+t 1≠0 := by simpa only [Fin.sum_univ_two,add_assoc] using edge rfl
    have difference : (t 0-t 1)*(a+t 0+t 1)*f 0=0 := by
      linear_combination hub-(t 1^2+a*t 1)*mass
    have x : f 0=0 := (mul_eq_zero.mp difference).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr (inj.ne (by decide))) sumne)
    have y : f 1=0 := by simpa only [x,zero_add] using mass
    funext i
    fin_cases i
    · exact x
    · exact y

private theorem private_spark_fin {K : Type*} [Field K] (g : ℕ) :
    ∀ (n : ℕ) (t : Fin n → K) (w : Fin g → K) (a : K), Function.Injective t → Function.Injective w →
      (∀ i j, t i+w j≠0) → n≤g+2 → (n=g+2 → a+(∑ i,t i)+(∑ j,w j)≠0) → ∀ f : Fin n → K,
      (∑ i,f i)=0 → (∑ i,(t i^2+a*t i)*f i)=0 → (∀ j,(∑ i,f i/(t i+w j))=0) → f=0 := by
  classical
  induction g with
  | zero =>
    intro n t w a ti _ _ size edge f mass hub _
    exact private_no_poles t a ti size (fun h => by simpa using edge h) f mass hub
  | succ g ih =>
    intro n t w a ti wi regular size edge f mass hub poles
    cases n with
    | zero => exact Subsingleton.elim _ _
    | succ n =>
      let x := t (Fin.last n)
      let v := w (Fin.last g)
      let d (i : Fin (n+1)) := (t i-x)/(t i+v)*f i
      have bottom : d (Fin.last n)=0 := by simp [d,x]
      obtain ⟨zm,zh,zp⟩ := shift_private_vector t f a x v (fun i => regular i (Fin.last g)) mass hub (poles (Fin.last g))
      have trim (F : Fin (n+1) → K) (last : F (Fin.last n)=0) (sum : (∑ i,F i)=0) :
          (∑ i : Fin n,F i.castSucc)=0 := by
        rw [Fin.sum_univ_castSucc,last,add_zero] at sum
        exact sum
      have dt : Function.Injective (fun i : Fin n => t i.castSucc) := fun _ _ h =>
        Fin.ext (congrArg (fun u : Fin (n+1) => u.val) (ti h))
      have dw : Function.Injective (fun j : Fin g => w j.castSucc) := fun _ _ h =>
        Fin.ext (congrArg (fun u : Fin (g+1) => u.val) (wi h))
      have newEdge (eq : n=g+2) : a+x+v+(∑ i : Fin n,t i.castSucc)+(∑ j : Fin g,w j.castSucc)≠0 := by
        have e := edge (by omega)
        rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc] at e
        dsimp only [x,v]
        convert e using 1
        ring
      have killed := ih n (fun i => t i.castSucc) (fun j => w j.castSucc) (a+x+v) dt dw
        (fun i j => regular i.castSucc j.castSucc) (by omega) newEdge (fun i => d i.castSucc)
        (trim d bottom zm)
        (trim (fun i => (t i^2+(a+x+v)*t i)*d i) (by rw [bottom,mul_zero]) zh)
        (fun j => trim (fun i => d i/(t i+w j.castSucc)) (by rw [bottom,zero_div])
          (zp (w j.castSucc) (fun eq => Fin.castSucc_ne_last j (wi eq))
            (fun i => regular i j.castSucc) (poles j.castSucc)))
      have head (i : Fin n) : f i.castSucc=0 := by
        have ne : t i.castSucc≠x := fun eq => Fin.castSucc_ne_last i (ti eq)
        have eq : (t i.castSucc-x)/(t i.castSucc+v)*f i.castSucc=0 := congrFun killed i
        exact (mul_eq_zero.mp eq).resolve_left (div_ne_zero (sub_ne_zero.mpr ne) (regular i.castSucc (Fin.last g)))
      have last : f (Fin.last n)=0 := by
        rw [Fin.sum_univ_castSucc] at mass
        simpa only [head,Finset.sum_const_zero,zero_add] using mass
      funext i
      exact Fin.lastCases last head i

/-- The constant row, the quadratic hub row and the reciprocal pole rows
detect every coefficient vector through two samples beyond the pole count.
Only at that last size is the indicated scalar condition needed. -/
theorem private_full_spark {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    (t : I → K) (w : J → K) (a : K) (tinj : Function.Injective t) (winj : Function.Injective w)
    (regular : ∀ i j, t i+w j≠0) (size : Fintype.card I≤Fintype.card J+2)
    (edge : Fintype.card I=Fintype.card J+2 → a+(∑ i,t i)+(∑ j,w j)≠0) (f : I → K)
    (mass : (∑ i,f i)=0) (hub : (∑ i,(t i^2+a*t i)*f i)=0)
    (poles : ∀ j,(∑ i,f i/(t i+w j))=0) : f=0 := by
  classical
  let E := (Fintype.equivFin I).symm
  let D := (Fintype.equivFin J).symm
  have result := private_spark_fin (Fintype.card J) (Fintype.card I) (fun i => t (E i)) (fun j => w (D j)) a
    (tinj.comp E.injective) (winj.comp D.injective) (fun i j => regular (E i) (D j)) size
    (fun h => by rw [E.sum_comp,D.sum_comp]; exact edge h) (fun i => f (E i))
    ((E.sum_comp f).trans mass) ((E.sum_comp (fun i => (t i^2+a*t i)*f i)).trans hub)
    (fun j => (E.sum_comp (fun i => f i/(t i+w (D j)))).trans (poles (D j)))
  funext i
  change f i=0
  simpa only [Equiv.apply_symm_apply,Pi.zero_apply] using congrFun result (E.symm i)

/-- Positive real nodes, positive poles and a positive hub parameter
automatically satisfy both nonvanishing conditions over the complex field. -/
theorem private_full_spark_positive {I J : Type*} [Fintype I] [Fintype J]
    (t : I → ℝ) (w : J → ℝ) (a : ℝ) (tinj : Function.Injective t) (winj : Function.Injective w)
    (posT : ∀ i,0<t i) (posW : ∀ j,0<w j) (posA : 0<a)
    (size : Fintype.card I≤Fintype.card J+2) (f : I → ℂ) (mass : (∑ i,f i)=0)
    (hub : (∑ i,((t i : ℂ)^2+(a : ℂ)*(t i : ℂ))*f i)=0)
    (poles : ∀ j,(∑ i,f i/((t i : ℂ)+(w j : ℂ)))=0) : f=0 := by
  apply private_full_spark (fun i => (t i : ℂ)) (fun j => (w j : ℂ)) (a : ℂ)
    (Complex.ofReal_injective.comp tinj) (Complex.ofReal_injective.comp winj) _ size _ f mass hub poles
  · intro i j
    exact_mod_cast (ne_of_gt (add_pos (posT i) (posW j)))
  · intro _
    have h : 0<a+(∑ i,t i)+(∑ j,w j) := add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg posA (Finset.sum_nonneg fun i _ => (posT i).le))
      (Finset.sum_nonneg fun j _ => (posW j).le)
    exact_mod_cast (ne_of_gt h)

/-- For one hub, distribute its outside marks among u color classes. Each
class has capacity ≤k and its own weighted test recovers its coefficients. -/
theorem one_right_coloring {I M S : Type*} [Fintype M] [DecidableEq I]
    (label : M → I) (i : I) (u k : ℕ) (features : S → M → ℂ)
    (room : Fintype.card {m : M // label m≠i} ≤ u*k)
    (spark : ∀ T : Finset M,(∀ m∈T,label m≠i) → T.card≤k →
      ∀ f : T → ℂ,(∀ z,∑ m : T, features z m.val*f m=0) → f=0) :
    ∃ Q : Matrix (Fin u) M ℂ, ∀ f : M→ℂ,(∀ m,label m=i → f m=0) →
      (∀ q z,∑ m,Q q m*(features z m*f m)=0) → f=0 := by
  classical
  let O := {m : M // label m≠i}
  obtain ⟨slot⟩ : Nonempty (O ↪ Fin u × Fin k) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_prod,Fintype.card_fin] using room)
  let color (m : M) : Option (Fin u) := if h : label m≠i then some (slot ⟨m,h⟩).1 else none
  let cluster (q : Fin u) := Finset.univ.filter (fun m : M => color m=some q)
  let Q : Matrix (Fin u) M ℂ := fun q m => if color m=some q then 1 else 0
  have outside (q : Fin u) (m : M) (hm : m∈cluster q) : label m≠i := by
    have h := (Finset.mem_filter.mp hm).2
    intro eq
    simp only [color,dif_neg (not_not.mpr eq),reduceCtorEq] at h
  have size (q : Fin u) : (cluster q).card≤k := by
    let idx (m : cluster q) : O := ⟨m.val,outside q m.val m.property⟩
    have lab (m : cluster q) : (slot (idx m)).1=q := by
      have hm := (Finset.mem_filter.mp m.property).2
      exact Option.some.inj (by simpa only [color,dif_pos (outside q m.val m.property)] using hm)
    have inj : Function.Injective (fun m : cluster q => (slot (idx m)).2) := by
      intro x y eq
      have both := slot.injective (Prod.ext ((lab x).trans (lab y).symm) eq)
      exact Subtype.ext (congrArg (fun v : O => v.val) both)
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective _ inj
  have restrict (q : Fin u) (v : M → ℂ) :
      (∑ m : cluster q,v m.val) = ∑ m : M,Q q m*v m := by
    calc
      _ = ∑ m ∈ cluster q,v m := Finset.sum_coe_sort _ _
      _ = _ := by simp [cluster,Q,Finset.sum_filter,ite_mul]
  refine ⟨Q,?_⟩
  intro f own test
  funext m
  by_cases h : label m=i
  · exact own m h
  · let q := (slot ⟨m,h⟩).1
    have mem : m∈cluster q := by simp [cluster,color,h,q]
    have zero := spark (cluster q) (outside q) (size q) (fun n => f n.val)
      (fun z => (restrict q (fun n => features z n*f n)).trans (test q z))
    exact congrFun zero ⟨m,mem⟩

end CriticalThreeBatch

namespace CriticalThreeBatch

open MvPolynomial

private theorem colors_reindex_injective {A B A' B' : Type*} [Fintype B] [Fintype B']
    (M : Matrix A B ℂ) (e : A'≃A) (f : B'≃B) :
    Function.Injective (M.submatrix e f).mulVec ↔ Function.Injective M.mulVec := by
  constructor
  · intro inj x y h
    have eq : (M.submatrix e f).mulVec (x ∘ f)=(M.submatrix e f).mulVec (y ∘ f) := by
      rw [Matrix.submatrix_mulVec_equiv,Matrix.submatrix_mulVec_equiv]
      simpa only [Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id] using congrArg (· ∘ e) h
    funext b
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using congrFun (inj eq) (f.symm b)
  · intro inj x y h
    rw [Matrix.submatrix_mulVec_equiv,Matrix.submatrix_mulVec_equiv] at h
    have eq : M.mulVec (x ∘ f.symm)=M.mulVec (y ∘ f.symm) := by
      funext a
      simpa only [Function.comp_apply,Equiv.apply_symm_apply] using congrFun h (e.symm a)
    funext b
    simpa only [Function.comp_apply,Equiv.symm_apply_apply] using congrFun (inj eq) (f b)

/-- Simultaneous injectivity with one additional square test. Reindexing by
Fin lets the square and rectangular systems have unrelated index types. -/
private theorem common_colors_with_square {I R C V : Type*} [Fintype I] [Fintype R] [Fintype C]
    {u : ℕ} (H : I → Matrix R C (MvPolynomial V ℂ)) (T : Matrix (Fin u) (Fin u) (MvPolynomial V ℂ))
    (one : ∀ i,∃ p : V→ℂ,Function.Injective ((H i).map (eval p)).mulVec)
    (square : ∃ p : V→ℂ,Function.Injective (T.map (eval p)).mulVec) :
    ∃ p : V→ℂ,Function.Injective (T.map (eval p)).mulVec ∧
      ∀ i,Function.Injective ((H i).map (eval p)).mulVec := by
  classical
  let rows : Option I → ℕ := Option.elim' u (fun _ => Fintype.card R)
  let cols : Option I → ℕ := Option.elim' u (fun _ => Fintype.card C)
  let er := (Fintype.equivFin R).symm
  let ec := (Fintype.equivFin C).symm
  let test : (i : Option I) → Matrix (Fin (rows i)) (Fin (cols i)) (MvPolynomial V ℂ)
    | none => T
    | some i => (H i).submatrix er ec
  have each : ∀ i : Option I, ∃ p : V→ℂ,Function.Injective ((test i).map (eval p)).mulVec := by
    intro i
    cases i with
    | none => exact square
    | some i =>
      obtain ⟨p,hp⟩ := one i
      exact ⟨p,(colors_reindex_injective ((H i).map (eval p)) er ec).mpr hp⟩
  obtain ⟨p,hp⟩ := LastSliceBatch.common_injective test each
  exact ⟨p,hp none,fun i => (colors_reindex_injective ((H i).map (eval p)) er ec).mp (hp (some i))⟩

private theorem right_system_iff {I M S : Type*} [Fintype M] [DecidableEq M] [DecidableEq I]
    {u : ℕ} (label : M→I) (i : I) (feature : S→M→ℂ) (Q : Matrix (Fin u) M ℂ)
    (H : Matrix (M ⊕ (Fin u × S)) M ℂ)
    (entries : ∀ row m,H row m=row.elim
      (fun c => if m=c ∧ label c=i then 1 else 0)
      (fun e => Q e.1 m * feature e.2 m)) :
    Function.Injective H.mulVec ↔
      ∀ f : M→ℂ,(∀ m,label m=i → f m=0) →
        (∀ q z,∑ m,Q q m*(feature z m*f m)=0) → f=0 := by
  classical
  have own (f : M→ℂ) (m : M) : H.mulVec f (.inl m)=if label m=i then f m else 0 := by
    change (∑ x : M,H (.inl m) x*f x)=_
    by_cases same : label m=i <;> simp [entries,same,ite_mul,Finset.sum_ite_eq']
  have rest (f : M→ℂ) (q : Fin u) (z : S) :
      H.mulVec f (.inr (q,z))=∑ m,Q q m*(feature z m*f m) := by
    change (∑ x : M,H (.inr (q,z)) x*f x)=_
    simp only [entries,Sum.elim_inr,mul_assoc]
  constructor
  · intro inj f atzero test
    have ker : H.mulVec f=0 := by
      funext row
      rcases row with m | ⟨q,z⟩
      · by_cases eq : label m=i <;> simp [own,eq,atzero]
      · exact (rest f q z).trans (test q z)
    exact inj (ker.trans (Matrix.mulVec_zero _).symm)
  · intro direct
    change Function.Injective H.mulVecLin
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro f zero
    apply direct f
    · intro m eq
      have h := congrFun zero (.inl m)
      change H.mulVec f (.inl m)=0 at h
      rwa [own,if_pos eq] at h
    · intro q z
      exact (rest f q z).symm.trans (congrFun zero (.inr (q,z)))

/-- If every small outside subset is detected by its local scalar functions,
one right matrix of full row rank supplies all required hub equations.
The per-hub colorings may use different partitions. -/
theorem common_colored_functionals {I M S : Type*} [Fintype I] [Fintype M] [Fintype S] [DecidableEq I]
    (u : ℕ) (label : M→I) (capacity : I→ℕ) (feature : I→S→M→ℂ)
    (rankRoom : u≤Fintype.card M)
    (room : ∀ i,Fintype.card {m : M // label m≠i}≤u*capacity i)
    (spark : ∀ i,∀ T : Finset M,(∀ m∈T,label m≠i) → T.card≤capacity i →
      ∀ f : T→ℂ,(∀ z,∑ m : T,feature i z m.val*f m=0) → f=0) :
    ∃ Q : Matrix (Fin u) M ℂ,Function.Surjective Q.mulVec ∧
      ∀ i,∀ f : M→ℂ,(∀ m,label m=i → f m=0) →
        (∀ q z,∑ m,Q q m*(feature i z m*f m)=0) → f=0 := by
  classical
  let V := Fin u × M
  let R := M ⊕ (Fin u × S)
  let H (i : I) : Matrix R M (MvPolynomial V ℂ) := fun row m => row.elim
    (fun c => if m=c ∧ label c=i then 1 else 0)
    (fun e => X (e.1,m)*C (feature i e.2 m))
  have action (i : I) (p : V→ℂ) :
      Function.Injective ((H i).map (eval p)).mulVec ↔
      ∀ f : M→ℂ,(∀ m,label m=i → f m=0) →
        (∀ q z,∑ m,p (q,m)*(feature i z m*f m)=0) → f=0 := by
    apply right_system_iff label i (feature i) (fun q m => p (q,m))
    intro row m
    change eval p (H i row m)=_
    rcases row with c|⟨q,z⟩
    · by_cases h : m=c ∧ label c=i <;> simp [H,h]
    · simp [H]
  have possible (i : I) : ∃ p : V→ℂ,Function.Injective ((H i).map (eval p)).mulVec := by
    obtain ⟨Q,hQ⟩ := one_right_coloring label i u (capacity i) (feature i) (room i) (spark i)
    exact ⟨fun v => Q v.1 v.2,(action i _).mpr hQ⟩
  obtain ⟨pivot⟩ : Nonempty (Fin u ↪ M) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using rankRoom)
  let minor : Matrix (Fin u) (Fin u) (MvPolynomial V ℂ) := fun q j => X (q,pivot j)
  have rankTest : ∃ p : V→ℂ,Function.Injective (minor.map (eval p)).mulVec := by
    let seed (v : V) : ℂ := if v.2=pivot v.1 then 1 else 0
    have ident : minor.map (eval seed)=1 := by
      apply Matrix.ext
      intro i j
      rw [Matrix.one_apply]
      change eval seed (X (i,pivot j))=_
      rw [eval_X]
      change (if pivot j=pivot i then (1:ℂ) else 0)=_
      rw [pivot.injective.eq_iff]
      by_cases e : i=j
      · subst j; simp
      · simp [e,Ne.symm e]
    refine ⟨seed,?_⟩
    rw [ident]
    intro x y eq
    simpa only [Matrix.one_mulVec] using eq
  obtain ⟨p,ind,localTests⟩ := common_colors_with_square H minor possible rankTest
  let Q : Matrix (Fin u) M ℂ := fun q m => p (q,m)
  have evalMinor : minor.map (eval p)=Q.submatrix id pivot := by
    apply Matrix.ext
    intro i j
    change eval p (X (i,pivot j))=p (i,pivot j)
    rw [eval_X]
  rw [evalMinor] at ind
  have surj : Function.Surjective (Q.submatrix id pivot).mulVecLin :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp ind)
  have top := LinearMap.range_eq_top.mpr surj
  rw [Matrix.range_mulVecLin] at top
  have full : Function.Surjective Q.mulVecLin := by
    apply LinearMap.range_eq_top.mp
    rw [Matrix.range_mulVecLin]
    apply top_unique
    rw [← top]
    apply Submodule.span_mono
    rintro _ ⟨i,rfl⟩
    exact ⟨pivot i,rfl⟩
  exact ⟨Q,full,fun i => (action i p).mp (localTests i)⟩

end CriticalThreeBatch

namespace CriticalThreeBatch

/-- One right relation matrix detects the mass, quadratic hub and private
pole equations at every hub. The number of outside marks may be as large
as the number of right relations times the local interpolation dimension. -/
theorem common_right_colors {I J M : Type*} [Fintype I] [Fintype J] [Fintype M] [DecidableEq I]
    (u : ℕ) (owner : J→I) (label : M→I) (t : M→ℂ) (a : I→ℂ) (w : J→ℂ)
    (rankRoom : u≤Fintype.card M)
    (room : ∀ i,Fintype.card {m : M // label m≠i} ≤ u*(Fintype.card {j : J // owner j=i}+2))
    (spark : ∀ i,∀ B : Finset M,(∀ m∈B,label m≠i) →
      B.card≤Fintype.card {j : J // owner j=i}+2 →
      ∀ f : B→ℂ,(∑ m,f m)=0 → (∑ m,(t m.val^2+a i*t m.val)*f m)=0 →
        (∀ j,owner j=i → (∑ m,f m/(t m.val+w j))=0) → f=0) :
    ∃ Q : Matrix (Fin u) M ℂ,Function.Surjective Q.mulVec ∧
      ∀ i,∀ f : M→ℂ,(∀ m,label m=i → f m=0) →
        (∀ q,∑ m,Q q m*f m=0) →
        (∀ q,∑ m,(Q q m*f m)*(t m^2+a i*t m)=0) →
        (∀ j,owner j=i → ∀ q,∑ m,(Q q m*f m)/(t m+w j)=0) → f=0 := by
  classical
  let S := Unit ⊕ Unit ⊕ J
  let feature (i : I) (s : S) (m : M) : ℂ := s.elim (fun _ => 1)
    (Sum.elim (fun _ => t m^2+a i*t m) (fun j => if owner j=i then (t m+w j)⁻¹ else 0))
  let cap (i : I) := Fintype.card {j : J // owner j=i}+2
  obtain ⟨Q,onto,good⟩ := common_colored_functionals u label cap feature rankRoom room (by
    intro i B outside size f test
    apply spark i B outside size f
    · simpa only [feature,Sum.elim_inl,one_mul] using test (.inl ())
    · exact test (.inr (.inl ()))
    · intro j hj
      simpa only [feature,Sum.elim_inr,if_pos hj,div_eq_mul_inv,mul_comm (t _+_)⁻¹] using test (.inr (.inr j)))
  refine ⟨Q,onto,?_⟩
  intro i f own mass hub poles
  apply good i f own
  intro q s
  rcases s with ⟨⟩|⟨⟩|j
  · simpa only [feature,Sum.elim_inl,one_mul] using mass q
  · simpa [feature,mul_assoc,mul_comm,mul_left_comm] using hub q
  · by_cases eq : owner j=i
    · simpa [feature,eq,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using poles j eq q
    · simp [feature,eq]

/-- Positive real nodes and distinct private poles give the required local
tests over ℂ, so the common right matrix requires only the count assumptions. -/
theorem common_right_colors_positive {I J M : Type*} [Fintype I] [Fintype J] [Fintype M] [DecidableEq I]
    (u : ℕ) (owner : J→I) (label : M→I) (t : M→ℝ) (a : I→ℝ) (w : J→ℝ)
    (tinj : Function.Injective t)
    (winj : ∀ i,Function.Injective (fun j : {j : J // owner j=i} => w j.val))
    (posT : ∀ m,0<t m) (posA : ∀ i,0<a i) (posW : ∀ j,0<w j)
    (rankRoom : u≤Fintype.card M)
    (room : ∀ i,Fintype.card {m : M // label m≠i} ≤ u*(Fintype.card {j : J // owner j=i}+2)) :
    ∃ Q : Matrix (Fin u) M ℂ,Function.Surjective Q.mulVec ∧
      ∀ i,∀ f : M→ℂ,(∀ m,label m=i → f m=0) →
        (∀ q,∑ m,Q q m*f m=0) →
        (∀ q,∑ m,(Q q m*f m)*((t m:ℂ)^2+(a i:ℂ)*(t m:ℂ))=0) →
        (∀ j,owner j=i → ∀ q,∑ m,(Q q m*f m)/((t m:ℂ)+(w j:ℂ))=0) → f=0 := by
  apply common_right_colors u owner label (fun m => (t m:ℂ)) (fun i => (a i:ℂ)) (fun j => (w j:ℂ)) rankRoom room
  intro i B _ size f mass hub poles
  exact private_full_spark_positive (fun m : B => t m.val) (fun j : {j : J // owner j=i} => w j.val) (a i)
    (tinj.comp Subtype.val_injective) (winj i) (fun m => posT m.val) (fun j => posW j.val) (posA i)
    (by simpa only [Fintype.card_coe] using size) f mass hub (fun j => poles j.val j.property)

end CriticalThreeBatch

namespace CriticalThreeCubic

/-- With first factors (1,t,t³), the two commutators differ entrywise by
a quadratic divided difference. Eliminating one row from a pair leaves
only one pole, at −u−v. -/
theorem cubic_pair {I K : Type*} [Fintype I] [Field K]
    (a p b : I → K) (u v t x y : K) (pole : t+u+v≠0)
    (linear : x+y+∑ i,p i*b i=0)
    (cubic : (u^2+u*t+t^2)*x+(v^2+v*t+t^2)*y+
      ∑ i,p i*(a i^2+a i*t+t^2)*b i=0) :
    let R := (∑ i,p i*(a i-u)*(a i-v)*b i)/(t+u+v)
    (u-v)*x=-(∑ i,p i*(a i-v)*b i)-R ∧
    (u-v)*((u^2+u*t+t^2)*x)=-(∑ i,p i*(a i-v)*((a i^2+a i*t+t^2)*b i))+
      (∑ i,p i*(a i-u)*(a i-v)*(a i+(u+v))*b i)+(u*v-(u+v)^2)*R := by
  intro R
  have elim : (u-v)*(t+u+v)*x=-(∑ i,p i*(a i-v)*(t+a i+v)*b i) := by
    have sub : (∑ i,p i*(a i-v)*(t+a i+v)*b i)=
        (∑ i,p i*(a i^2+a i*t+t^2)*b i)-(v^2+v*t+t^2)*(∑ i,p i*b i) := by
      rw [Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [sub]
    linear_combination cubic - (v^2+v*t+t^2)*linear
  have split : (∑ i,p i*(a i-v)*(t+a i+v)*b i)=
      (t+u+v)*(∑ i,p i*(a i-v)*b i)+(∑ i,p i*(a i-u)*(a i-v)*b i) := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have clear : R*(t+u+v)=(∑ i,p i*(a i-u)*(a i-v)*b i) := div_mul_cancel₀ _ pole
  have first : (u-v)*x=-(∑ i,p i*(a i-v)*b i)-R := by
    apply mul_right_cancel₀ pole
    rw [split] at elim
    linear_combination elim + clear
  refine ⟨first,?_⟩
  have changeRows : (u^2+u*t+t^2)*(∑ i,p i*(a i-v)*b i)-
      (∑ i,p i*(a i-v)*((a i^2+a i*t+t^2)*b i)) =
      -((t-v)*(∑ i,p i*(a i-u)*(a i-v)*b i)+
        (∑ i,p i*(a i-u)*(a i-v)*(a i+(u+v))*b i)) := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linear_combination (u^2+u*t+t^2)*first - changeRows - (t-v)*clear

end CriticalThreeCubic

namespace CriticalThreeBatch

/-- In a component with several right relations, each pair belongs to
one hub. Its two physical diagonals force that hub coordinate to vanish
at either member of the pair. All remaining tests are scalar. -/
theorem rectangular_private_kernel {K I J A M V : Type*} [Field K] [Fintype A] [Fintype M]
    (node : A→K) (distinct : Function.Injective node) (mark : M↪A)
    (hub : I→A) (left right : J→A) (owner : J→I) (attach : A→I)
    (covers : ∀ s,(∃ i,hub i=s) ∨ (∃ j,left j=s) ∨ ∃ j,right j=s)
    (hubGroup : ∀ i,attach (hub i)=i) (leftGroup : ∀ j,attach (left j)=owner j)
    (rightGroup : ∀ j,attach (right j)=owner j)
    (awayU : ∀ j,hub (owner j)≠left j) (awayV : ∀ j,hub (owner j)≠right j)
    (pairwise : ∀ j,left j≠right j)
    (regular : ∀ j s,node s+node (left j)+node (right j)≠0)
    (Q : Matrix V M K) :
    let a (i : I) := node (hub i)
    let u (j : J) := node (left j)
    let v (j : J) := node (right j)
    let t (k : M) := node (mark k)
    (∀ i : I, ∀ f : M→K, (∀ k, attach (mark k)=i → f k=0) →
      (∀ q,(∑ k,f k*Q q k)=0) → (∀ q,(∑ k,(((t k)^2+a i*t k)*f k)*Q q k)=0) →
      (∀ j, owner j=i → ∀ q,(∑ k,(f k/(t k+u j+v j))*Q q k)=0) → f=0) →
    ∃ P : Matrix J A K, ∀ E : A→M→K,
      (∀ j k,(∑ s,P j s*((node s-t k)*E s k))=0) →
      (∀ j k,(∑ s,P j s*(((node s)^3-(t k)^3)*E s k))=0) →
      (∀ q s,(∑ k,((node s-t k)*E s k)*Q q k)=0) →
      (∀ q s,(∑ k,(((node s)^3-(t k)^3)*E s k)*Q q k)=0) →
      ∀ s k,s≠mark k → E s k=0 := by
  classical
  intro a u v t scalar
  let P : Matrix J A K := fun j s =>
    (if s=left j then 1 else 0)+(if s=right j then 1 else 0)+(if s=hub (owner j) then 1 else 0)
  have row (j : J) (f : A→K) :
      (∑ s,P j s*f s)=f (left j)+f (right j)+f (hub (owner j)) := by
    simp [P,add_mul,Finset.sum_add_distrib,ite_mul]
  refine ⟨P,?_⟩
  intro E leftB leftC rightB rightC
  let B (s : A) (k : M) := (node s-t k)*E s k
  let C (s : A) (k : M) := ((node s)^2+node s*t k+(t k)^2)*B s k
  let S (i : I) := B (hub i)
  have cube (s : A) (k : M) : C s k=((node s)^3-(t k)^3)*E s k := by dsimp [C,B]; ring
  have diag (k : M) : B (mark k) k=0 := by simp [B,t]
  have lin (j : J) (k : M) : B (left j) k+B (right j) k+S (owner j) k=0 :=
    (row j (fun s => B s k)).symm.trans (leftB j k)
  have cub (j : J) (k : M) :
      ((u j)^2+u j*t k+(t k)^2)*B (left j) k+
      ((v j)^2+v j*t k+(t k)^2)*B (right j) k+
      ((a (owner j))^2+a (owner j)*t k+(t k)^2)*S (owner j) k=0 := by
    have z : (∑ s,P j s*C s k)=0 := by simp only [cube,leftC]
    exact (row j (fun s => C s k)).symm.trans z
  have aU (j : J) : a (owner j)-u j≠0 := sub_ne_zero.mpr (distinct.ne (awayU j))
  have aV (j : J) : a (owner j)-v j≠0 := sub_ne_zero.mpr (distinct.ne (awayV j))
  have aSum (j : J) : a (owner j)+u j+v j≠0 := regular j (hub (owner j))
  let G (j : J) := (a (owner j)-u j)*(a (owner j)-v j)
  have pair (j : J) (k : M) :
      (u j-v j)*B (left j) k+(a (owner j)-v j)*S (owner j) k+
      G j*(S (owner j) k/(t k+u j+v j))=0 := by
    have e := (CriticalThreeCubic.cubic_pair (I:=Unit) (fun _ => a (owner j)) (fun _ => 1)
      (fun _ => S (owner j) k) (u j) (v j) (t k) (B (left j) k) (B (right j) k)
      (regular j (mark k)) (by simpa using lin j k) (by simpa using cub j k)).1
    simp only [Fintype.sum_unique,one_mul] at e
    dsimp only [G]
    linear_combination e
  have own (k : M) : S (attach (mark k)) k=0 := by
    rcases covers (mark k) with ⟨i,atI⟩ | ⟨j,atU⟩ | ⟨j,atV⟩
    · rw [← atI,hubGroup]
      exact (congrArg (fun s => B s k) atI).trans (diag k)
    · rw [← atU,leftGroup]
      have z : B (left j) k=0 := atU ▸ diag k
      have lk := lin j k
      have ck := cub j k
      rw [z,zero_add] at lk
      rw [z,mul_zero,zero_add] at ck
      have val : t k=u j := congrArg node atU.symm
      rw [val] at ck
      apply (mul_eq_zero.mp (show ((a (owner j)-v j)*(a (owner j)+u j+v j))*S (owner j) k=0 by
        linear_combination ck-((v j)^2+v j*u j+(u j)^2)*lk)).resolve_left
      exact mul_ne_zero (aV j) (aSum j)
    · rw [← atV,rightGroup]
      have z : B (right j) k=0 := atV ▸ diag k
      have lk := lin j k
      have ck := cub j k
      rw [z,add_zero] at lk
      rw [z,mul_zero,add_zero] at ck
      have val : t k=v j := congrArg node atV.symm
      rw [val] at ck
      apply (mul_eq_zero.mp (show ((a (owner j)-u j)*(a (owner j)+u j+v j))*S (owner j) k=0 by
        linear_combination ck-((u j)^2+u j*v j+(v j)^2)*lk)).resolve_left
      exact mul_ne_zero (aU j) (aSum j)
  let L (q : V) : (M→K) →ₗ[K] K := ∑ k,(Q q k) • (LinearMap.proj k : (M→K) →ₗ[K] K)
  have readL (q : V) (f : M→K) : L q f=∑ k,f k*Q q k := by
    simp [L,LinearMap.sum_apply,mul_comm]
  have hB (q : V) (s : A) : L q (B s)=0 := (readL q _).trans (rightB q s)
  have hC (q : V) (s : A) : L q (C s)=0 := by rw [readL]; simp only [cube,rightC]
  have hubZero (i : I) : S i=0 := by
    apply scalar i _ (fun k eq => eq ▸ own k)
    · exact fun q => (readL q _).symm.trans (hB q (hub i))
    · intro q
      have split : (fun k => ((t k)^2+a i*t k)*S i k)=C (hub i)-(a i)^2 • S i := by
        funext k
        change _=(((a i)^2+a i*t k+(t k)^2)*S i k)-(a i)^2*S i k
        ring
      rw [← readL,split,map_sub,map_smul,hC,hB q (hub i)]
      simp
    · intro j eq q
      subst i
      let f (k : M) := S (owner j) k/(t k+u j+v j)
      have e : (u j-v j) • B (left j)+(a (owner j)-v j) • S (owner j)+G j • f=0 := by
        funext k
        exact pair j k
      have he := congrArg (L q) e
      simp only [map_add,map_smul,map_zero,smul_eq_mul,hB,
        show L q (S (owner j))=0 from hB q _,mul_zero,zero_add] at he
      exact (readL q _).symm.trans ((mul_eq_zero.mp he).resolve_left (mul_ne_zero (aU j) (aV j)))
  intro s k ne
  have all (j : J) : B (left j) k=0 ∧ B (right j) k=0 := by
    have hs : S (owner j) k=0 := congrFun (hubZero _) k
    have e := pair j k
    rw [hs,zero_div,mul_zero,mul_zero,add_zero,add_zero] at e
    have e₁ := (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr (distinct.ne (pairwise j)))
    exact ⟨e₁,by simpa only [hs,e₁,zero_add,add_zero] using lin j k⟩
  have zero : B s k=0 := by
    rcases covers s with ⟨i,rfl⟩ | ⟨j,rfl⟩ | ⟨j,rfl⟩
    · exact congrFun (hubZero i) k
    · exact (all j).1
    · exact (all j).2
  exact (mul_eq_zero.mp zero).resolve_left (sub_ne_zero.mpr (distinct.ne ne))

private theorem sigma_fiber_card {I T : Type*} [Fintype I] [Fintype T] [DecidableEq I]
    (slots : I→ℕ) (idx : T ≃ Σ i,Fin (slots i)) (i : I) :
    Fintype.card {z : T // (idx z).1=i}=slots i := by
  classical
  let a : {z : T // (idx z).1=i} ≃ {z : Σ j,Fin (slots j) // z.1=i} :=
    idx.subtypeEquiv fun _ => Iff.rfl
  let b : {z : Σ j,Fin (slots j) // z.1=i} ≃ Fin (slots i) :=
    { toFun := fun z => finCongr (congrArg slots z.property) z.val.2
      invFun := fun x => ⟨⟨i,x⟩,rfl⟩
      left_inv := by rintro ⟨⟨j,x⟩,rfl⟩;rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_fin] using Fintype.card_congr (a.trans b)

/-- Private pairs and component marks with arbitrary prescribed quotas.
Each hub owns itself and both samples of every assigned pair. -/
theorem private_marks {h p m : ℕ} (g e : Fin h→ℕ)
    (pairs : ∑ i,g i=p) (marks : ∑ i,e i=m) (room : ∀ i,e i≤2*g i+1) :
    ∃ owner : Fin p→Fin h, ∃ mark : Fin m ↪ (Fin h ⊕ (Fin p ⊕ Fin p)),
      let attach : Fin h ⊕ (Fin p ⊕ Fin p) → Fin h := Sum.elim id (Sum.elim owner owner)
      (∀ i,Fintype.card {j : Fin p // owner j=i}=g i) ∧
      (∀ i,Fintype.card {k : Fin m // attach (mark k)≠i}=m-e i) := by
  classical
  let pg : (Σ i : Fin h,Fin (g i)) ≃ Fin p := Fintype.equivOfCardEq (by simpa using pairs)
  let me : Fin m ≃ (Σ i : Fin h,Fin (e i)) := Fintype.equivOfCardEq (by simpa using marks.symm)
  let owner (j : Fin p) := (pg.symm j).1
  let Pos (i : Fin h) := Unit ⊕ (Fin (g i) ⊕ Fin (g i))
  let attach : Fin h ⊕ (Fin p ⊕ Fin p) → Fin h := Sum.elim id (Sum.elim owner owner)
  let localSlot (i : Fin h) : Fin (e i) ↪ Pos i := Classical.choice (Function.Embedding.nonempty_of_card_le (by
    simp only [Pos,Fintype.card_sum,Fintype.card_unit,Fintype.card_fin]
    have := room i
    omega))
  let represent (z : Σ i : Fin h,Pos i) : Fin h ⊕ (Fin p ⊕ Fin p) :=
    z.2.elim (fun _ => .inl z.1) (Sum.elim
      (fun j => .inr (.inl (pg ⟨z.1,j⟩))) (fun j => .inr (.inr (pg ⟨z.1,j⟩))))
  have allocated (i : Fin h) (s : Pos i) : attach (represent ⟨i,s⟩)=i := by
    rcases s with _ | j | j <;> simp [represent,attach,owner]
  have atOne (i : Fin h) : Function.Injective (fun s : Pos i => represent ⟨i,s⟩) := by
    rintro (⟨⟩|a|a) (⟨⟩|b|b) eq <;> simp [represent] at eq <;> subst_vars <;> rfl
  have inj : Function.Injective represent := by
    rintro ⟨i,z⟩ ⟨j,w⟩ eq
    have same := congrArg attach eq
    rw [allocated,allocated] at same
    subst j
    exact congrArg (Sigma.mk i) (atOne i eq)
  let lift := Function.Embedding.sigmaMap (Function.Embedding.refl (Fin h)) localSlot
  let mark := (me.toEmbedding.trans lift).trans (show (Σ i,Pos i) ↪ _ from ⟨represent,inj⟩)
  have group (k : Fin m) : attach (mark k)=(me k).1 := allocated _ _
  refine ⟨owner,mark,sigma_fiber_card g pg.symm,?_⟩
  intro i
  change Fintype.card {k : Fin m // ¬attach (mark k)=i}=_
  rw [Fintype.card_subtype_compl,Fintype.card_fin]
  simp only [group,sigma_fiber_card e me]

/-- Natural sample parameters give distinct positive first coordinates
and distinct positive denominators on all the private pairs. -/
theorem private_nodes (h p : ℕ) :
    ∃ node : Fin h ⊕ (Fin p ⊕ Fin p) → ℕ, Function.Injective node ∧ (∀ s,0<node s) ∧
      Function.Injective (fun j : Fin p => node (.inr (.inl j))+node (.inr (.inr j))) := by
  let node : Fin h ⊕ (Fin p ⊕ Fin p)→ℕ := Sum.elim (fun i => i.val+1)
    (Sum.elim (fun j => h+j.val+1) (fun j => h+p+j.val+1))
  refine ⟨node,?_,?_,?_⟩
  · rintro (i|j|j) (i'|j'|j') eq <;> dsimp [node] at eq
    all_goals first | exact congrArg Sum.inl (Fin.ext (by omega))
                    | exact congrArg (fun x => Sum.inr (Sum.inl x)) (Fin.ext (by omega))
                    | exact congrArg (fun x => Sum.inr (Sum.inr x)) (Fin.ext (by omega))
                    | omega
  · rintro (i|j|j) <;> dsimp [node] <;> omega
  · intro j k eq
    dsimp [node] at eq
    exact Fin.ext (by omega)

/-- Local CP tangent for a component with u independent right relations.
The numbers eᵢ count marks on the 2gᵢ+1 physical labels belonging to hub
i. Every label outside that hub is detected by its private scalar functions. -/
theorem local_cubic_component {h p m u : ℕ} (hu : u≤ m) (g e : Fin h→ℕ)
    (pairs : (∑ i,g i)=p) (marks : (∑ i,e i)=m)
    (room : ∀ i,e i≤2*g i+1) (fit : ∀ i,m-e i≤u*(g i+2)) :
    let r := 2*p+h
    let b := p+h
    let n := m-u
    ∃ x : Fin m→Fin 3→ℂ, ∃ y : Fin m→Fin b→ℂ, ∃ z : Fin m→Fin n→ℂ,
    ∃ x' : Fin (r-m)→Fin 3→ℂ, ∃ y' : Fin (r-m)→Fin b→ℂ,
    ∀ T : Fin 3→Fin b→Fin n→ℂ, ∃ U : Fin m→Fin 3→ℂ,
      ∃ V : Fin m→Fin b→ℂ, ∃ W : Fin m→Fin n→ℂ, ∃ W' : Fin (r-m)→Fin n→ℂ,
      ∀ i j k,T i j k=(∑ s,(U s i*(y s j*z s k)+x s i*(V s j*z s k)+x s i*(y s j*W s k)))+
        ∑ s,x' s i*(y' s j*W' s k) := by
  classical
  intro r b n
  obtain ⟨owner,mark,fiber,outside⟩ := private_marks g e pairs marks room
  let A := Fin h ⊕ (Fin p ⊕ Fin p)
  let H (i : Fin h) : A := .inl i
  let L (j : Fin p) : A := .inr (.inl j)
  let R (j : Fin p) : A := .inr (.inr j)
  let attach : A→Fin h := Sum.elim id (Sum.elim owner owner)
  let label (k : Fin m) := attach (mark k)
  obtain ⟨natNode,distinct,positive,poleDistinct⟩ := private_nodes h p
  let re (s : A) : ℝ := natNode s
  let node (s : A) : ℂ := re s
  let pole (j : Fin p) : ℝ := re (L j)+re (R j)
  have injReal : Function.Injective re := by
    intro s t eq
    apply distinct
    dsimp only [re] at eq
    exact_mod_cast eq
  have injC : Function.Injective node := Complex.ofReal_injective.comp injReal
  have posReal (s : A) : 0<re s := by dsimp only [re]; exact_mod_cast positive s
  have injPole : Function.Injective pole := by
    intro a b eq
    apply poleDistinct
    dsimp only [pole,re,L,R] at eq
    exact_mod_cast eq
  have reg (j : Fin p) (s : A) : node s+node (L j)+node (R j)≠0 := by
    dsimp only [node]
    exact_mod_cast (ne_of_gt (add_pos (add_pos (posReal s) (posReal (L j))) (posReal (R j))))
  obtain ⟨Q,_,detect⟩ := common_right_colors_positive u owner label (fun k => re (mark k))
    (fun i => re (H i)) pole (injReal.comp mark.injective)
    (fun _ => injPole.comp Subtype.val_injective)
    (fun k => posReal (mark k)) (fun i => posReal (H i)) (fun j => add_pos (posReal _) (posReal _))
    (by simpa only [Fintype.card_fin] using hu)
    (fun i => by
      change Fintype.card {k : Fin m // attach (mark k)≠i}≤_
      rw [outside i,fiber i];exact fit i)
  have cover (s : A) : (∃ i,H i=s) ∨ (∃ j,L j=s) ∨ ∃ j,R j=s := by
    rcases s with i | j | j
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr (Or.inl ⟨j,rfl⟩)
    · exact Or.inr (Or.inr ⟨j,rfl⟩)
  obtain ⟨P,kernel⟩ := rectangular_private_kernel node injC mark H L R owner attach cover
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => by simp [H,L])
    (fun _ => by simp [H,R]) (fun _ eq => nomatch Sum.inr.inj eq) reg Q (by
      intro i f own mass quad poles
      apply detect i f own
      · intro q
        simpa only [mul_comm] using mass q
      · intro q
        simpa only [node,mul_assoc,mul_left_comm,mul_comm] using quad q
      · intro j assigned q
        simpa only [node,pole,Complex.ofReal_add,add_assoc,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
          using poles j assigned q)
  have countA : Fintype.card A=r := by
    simp only [A,Fintype.card_sum,Fintype.card_fin,r]
    omega
  have hb : Fintype.card (Fin b) ≤ Fintype.card A-Fintype.card (Fin p) := by
    simp only [countA,Fintype.card_fin,b,r]
    omega
  have hn : Fintype.card (Fin n) ≤ Fintype.card (Fin m)-Fintype.card (Fin u) := by
    simp only [Fintype.card_fin,n,le_refl]
  have tangent := CriticalThreeQuotient.rectangular_tangent_of_kernel_samples
    hb hn mark node (fun s => (node s)^3) injC P Q kernel
  dsimp only at tangent
  rw [countA,Fintype.card_fin] at tangent
  obtain ⟨Y,Z,other,span⟩ := tangent
  exact ⟨fun s => ![1,node (mark s),(node (mark s))^3],fun s => Y (mark s),Z,
    fun s => ![1,node (other s),(node (other s))^3],fun s => Y (other s),span⟩

end CriticalThreeBatch

namespace CriticalThreeComponents

open Arxiv.«0805.3777»

/-- Each group of relations may use its own arrangement of paired physical
labels. The number of third coordinates for a group is its mark count
minus its relation count. After the common specialization those coordinates
exhaust the entire third factor. -/
theorem tangent_of_components {h b n r C : ℕ} (hb : h≤b) (hn : n≤r) (level : r+h=2*b)
    (rel marks : Fin C→ℕ) (rows : (∑ c,rel c)=r-n) (points : (∑ c,marks c)=r)
    (localCount : ∀ c,rel c ≤ marks c)
    (geometry : ∀ c,∃ g e : Fin h→ℕ, (∑ i,g i)=b-h ∧ (∑ i,e i)=marks c ∧
      ∀ i,e i ≤ 2*g i+1 ∧ marks c-e i ≤ rel c*(g i+2)) :
    ∃ X : Fin r→Fin 3→ℂ, ∃ Y : Fin r→Fin b→ℂ, ∃ Z : Fin r→Fin n→ℂ,
    ∀ T : Fin 3→Fin b→Fin n→ℂ, ∃ U : Fin r→Fin 3→ℂ, ∃ V : Fin r→Fin b→ℂ,
      ∃ W : Fin r→Fin n→ℂ, ∀ i j k,
        T i j k=∑ t,(U t i*(Y t j*Z t k)+X t i*(V t j*Z t k)+X t i*(Y t j*W t k)) := by
  let width (c : Fin C) := marks c-rel c
  have dimensions : (∑ c,width c)=n := by
    have total : (∑ c,width c)+(∑ c,rel c)=∑ c,marks c := by
      rw [←Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun c _ => Nat.sub_add_cancel (localCount c))
    rw [rows,points] at total
    omega
  rw [←dimensions]
  apply CriticalHigher.Blocks.different_block_tangent 3 b C r width marks points.le
  intro c
  obtain ⟨g,e,gSize,eSize,assign⟩ := geometry c
  have hit := CriticalThreeBatch.local_cubic_component (p:=b-h) (localCount c) g e
    gSize eSize (fun i => (assign i).1) (fun i => (assign i).2)
  dsimp only at hit
  rwa [Nat.sub_add_cancel hb,show 2*(b-h)+h=r by omega] at hit

end CriticalThreeComponents

namespace CriticalSquareFlows

/-- A figure-eight of two parallel-edge circuits detects the four-edge base. -/
theorem four : (∃ a b : ℕ, a+b+1=4 ∧ ∃ left : Fin 4→Fin a, ∃ right : Fin 4→Fin b,
    ∀ f : Fin 4→ℂ,
    (∀ i, (∑ j,if left j=i then f j else 0)=0) →
    (∀ i, (∑ j,if right j=i then f j else 0)=0) →
    ∀ i j : Fin 4, (j.val=i.val+1 ∨ (i.val+1=4 ∧ j.val=0)) →
        f i=0 → f j=0 → f=0) := by
  let r : Fin 4 → Fin 2 := ![0,1,0,1]
  refine ⟨1,2,by decide,fun _ => 0,r,?_⟩
  intro f _ sums i j adj fi fj
  have even := sums 0
  have odd := sums 1
  norm_num [r,Fin.sum_univ_succ] at even odd
  change f 0+f 2=0 at even
  change f 1+f 3=0 at odd
  have f2 : f 2= -f 0 := by linear_combination even
  have f3 : f 3= -f 1 := by linear_combination odd
  suffices f 0=0 ∧ f 1=0 by
    funext t
    fin_cases t <;> simp_all
  fin_cases i <;> fin_cases j <;> norm_num at adj <;> simp_all

/-- Three length-two paths detect the six-edge base. The values on the
first half add to zero and the second half is their termwise negative. -/
theorem six : (∃ a b : ℕ, a+b+1=6 ∧ ∃ left : Fin 6→Fin a, ∃ right : Fin 6→Fin b,
    ∀ f : Fin 6→ℂ,
    (∀ i, (∑ j,if left j=i then f j else 0)=0) →
    (∀ i, (∑ j,if right j=i then f j else 0)=0) →
    ∀ i j : Fin 6, (j.val=i.val+1 ∨ (i.val+1=6 ∧ j.val=0)) →
        f i=0 → f j=0 → f=0) := by
  let p : Fin 6→Fin 2 := ![0,0,0,1,1,1]
  let q : Fin 6→Fin 3 := ![0,1,2,0,1,2]
  refine ⟨2,3,by decide,p,q,?_⟩
  intro f sums₁ sums₂ i j adj fi fj
  have head := sums₁ 0
  have p₀ := sums₂ 0
  have p₁ := sums₂ 1
  have p₂ := sums₂ 2
  norm_num [p,q,Fin.sum_univ_succ] at head p₀ p₁ p₂
  simp only [show (0:Fin 3)≠2 by decide,show (1:Fin 3)≠2 by decide,
    show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,if_false,add_zero,zero_add] at p₀ p₁ p₂
  change f 0+(f 1+f 2)=0 at head
  change f 0+f 3=0 at p₀
  change f 1+f 4=0 at p₁
  change f 2+f 5=0 at p₂
  have third : f 2= -(f 0)-f 1 := by linear_combination head
  have n₀ : f 3= -f 0 := by linear_combination p₀
  have n₁ : f 4= -f 1 := by linear_combination p₁
  have n₂ : f 5= -f 2 := by linear_combination p₂
  suffices f 0=0 ∧ f 1=0 by
    funext t
    fin_cases t <;> simp_all
  fin_cases i <;> fin_cases j <;> norm_num at adj <;> simp_all

/-- The two initial graphs and subdivisions produce every even size. -/
theorem all_even_of_step (step : ∀ n,2≤n→(∃ a b : ℕ, a+b+1=n ∧ ∃ left : Fin n→Fin a, ∃ right : Fin n→Fin b,
    ∀ f : Fin n→ℂ,
    (∀ i, (∑ j,if left j=i then f j else 0)=0) →
    (∀ i, (∑ j,if right j=i then f j else 0)=0) →
    ∀ i j : Fin n, (j.val=i.val+1 ∨ (i.val+1=n ∧ j.val=0)) →
        f i=0 → f j=0 → f=0)→(∃ a b : ℕ, a+b+1=(n+4) ∧ ∃ left : Fin (n+4)→Fin a, ∃ right : Fin (n+4)→Fin b,
    ∀ f : Fin (n+4)→ℂ,
    (∀ i, (∑ j,if left j=i then f j else 0)=0) →
    (∀ i, (∑ j,if right j=i then f j else 0)=0) →
    ∀ i j : Fin (n+4), (j.val=i.val+1 ∨ (i.val+1=(n+4) ∧ j.val=0)) →
        f i=0 → f j=0 → f=0))
    (n : ℕ) (large : 4≤n) (even : Even n) : (∃ a b : ℕ, a+b+1=n ∧ ∃ left : Fin n→Fin a, ∃ right : Fin n→Fin b,
    ∀ f : Fin n→ℂ,
    (∀ i, (∑ j,if left j=i then f j else 0)=0) →
    (∀ i, (∑ j,if right j=i then f j else 0)=0) →
    ∀ i j : Fin n, (j.val=i.val+1 ∨ (i.val+1=n ∧ j.val=0)) →
        f i=0 → f j=0 → f=0) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n<8
    · obtain rfl | rfl : n=4 ∨ n=6 := by obtain ⟨k,hk⟩ := even; omega
      · exact four
      · exact six
    obtain ⟨j,rfl⟩ : ∃ j,n=j+4 := ⟨n-4,by omega⟩
    have par : Even j := by
      obtain ⟨k,hk⟩ := even
      exact ⟨k-2,by omega⟩
    exact step j (by omega) (ih j (by omega) (by omega) par)

end CriticalSquareFlows

namespace CriticalSquareFlows

/-- A fiber sum on a reindexed edge set splits into the two parts, with
the vertex relabeling removed. -/
private theorem split_vertex_sum {S T E V W : Type*} [Fintype S] [Fintype T] [Fintype E]
    [DecidableEq V] [DecidableEq W] (edges : S ⊕ T ≃ E) (vertices : V ≃ W)
    (p : S→V) (q : T→V) (F : E→ℂ)
    (vsum : ∀ w : W,(∑ j : E,if vertices ((edges.symm j).elim p q)=w then F j else 0)=0)
    (v : V) :
    (∑ s : S,if p s=v then F (edges (.inl s)) else 0) +
      (∑ z : T,if q z=v then F (edges (.inr z)) else 0)=0 := by
  have h := vsum (vertices v)
  rw [← edges.sum_comp (fun j : E => if vertices ((edges.symm j).elim p q)=vertices v then F j else 0)] at h
  simp only [Fintype.sum_sum_type,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr] at h
  have test (z : V) (x : ℂ) :
      (if z=v then x else 0)=(if vertices z=vertices v then x else 0) := by
    by_cases hz : z=v
    · subst z; simp
    · simp [hz,vertices.injective.ne hz]
  calc
    _ = (∑ s : S,if vertices (p s)=vertices v then F (edges (.inl s)) else 0) +
      (∑ z : T,if vertices (q z)=vertices v then F (edges (.inr z)) else 0) := by
        exact congrArg₂ (·+·) (Finset.sum_congr rfl (fun s _ => test (p s) _))
          (Finset.sum_congr rfl (fun z _ => test (q z) _))
    _ = 0 := h

private theorem sum_six (f : Fin 6→ℂ) :
    (∑ i,f i)=f 0+(f 1+(f 2+(f 3+(f 4+f 5)))) := by
  simp [Fin.sum_univ_succ]

/-- Replace each of the first two edges by a path of length three. The old
coordinates are the last two path pieces followed by the unchanged edges;
the four new coordinates alternate between the original values and their
negatives. -/
theorem subdivide {n : ℕ} (two : 2≤n) : (∃ a b : ℕ, a+b+1=n ∧ ∃ left : Fin n→Fin a, ∃ right : Fin n→Fin b,
    ∀ f : Fin n→ℂ,
    (∀ i, (∑ j,if left j=i then f j else 0)=0) →
    (∀ i, (∑ j,if right j=i then f j else 0)=0) →
    ∀ i j : Fin n, (j.val=i.val+1 ∨ (i.val+1=n ∧ j.val=0)) →
        f i=0 → f j=0 → f=0) → (∃ a b : ℕ, a+b+1=(n+4) ∧ ∃ left : Fin (n+4)→Fin a, ∃ right : Fin (n+4)→Fin b,
    ∀ f : Fin (n+4)→ℂ,
    (∀ i, (∑ j,if left j=i then f j else 0)=0) →
    (∀ i, (∑ j,if right j=i then f j else 0)=0) →
    ∀ i j : Fin (n+4), (j.val=i.val+1 ∨ (i.val+1=(n+4) ∧ j.val=0)) →
        f i=0 → f j=0 → f=0) := by
  classical
  rintro ⟨a,b,size,left,right,detect⟩
  let k := n-2
  let old : Fin 2 ⊕ Fin k ≃ Fin n := finSumFinEquiv.trans (finCongr (by dsimp [k];omega))
  let added : Fin 6 ⊕ Fin k ≃ Fin (n+4) := finSumFinEquiv.trans (finCongr (by dsimp [k];omega))
  let i₀ := old (.inl 0)
  let i₁ := old (.inl 1)
  let oldtail (z : Fin k) := old (.inr z)
  let lhead : Fin 6 → Fin a ⊕ Fin 2 :=
    ![.inl (left i₀),.inl (left i₁),.inr 0,.inr 1,.inr 0,.inr 1]
  let rhead : Fin 6 → Fin b ⊕ Fin 2 :=
    ![.inr 0,.inr 1,.inr 0,.inr 1,.inl (right i₀),.inl (right i₁)]
  let ltail (z : Fin k) : Fin a ⊕ Fin 2 := .inl (left (oldtail z))
  let rtail (z : Fin k) : Fin b ⊕ Fin 2 := .inl (right (oldtail z))
  let left' (e : Fin (n+4)) := finSumFinEquiv ((added.symm e).elim lhead ltail)
  let right' (e : Fin (n+4)) := finSumFinEquiv ((added.symm e).elim rhead rtail)
  refine ⟨a+2,b+2,by omega,left',right',?_⟩
  intro F leftZero rightZero
  let x (j : Fin 6) := F (added (.inl j))
  let y (j : Fin k) := F (added (.inr j))
  have leftSum (v : Fin a ⊕ Fin 2) :
      (∑ j : Fin 6,if lhead j=v then x j else 0)+(∑ j : Fin k,if ltail j=v then y j else 0)=0 :=
    split_vertex_sum added finSumFinEquiv lhead ltail F leftZero v
  have rightSum (v : Fin b ⊕ Fin 2) :
      (∑ j : Fin 6,if rhead j=v then x j else 0)+(∑ j : Fin k,if rtail j=v then y j else 0)=0 :=
    split_vertex_sum added finSumFinEquiv rhead rtail F rightZero v
  have rr₀ : x 0+x 2=0 := by simpa [sum_six,rhead,rtail] using rightSum (.inr 0)
  have rr₁ : x 1+x 3=0 := by simpa [sum_six,rhead,rtail] using rightSum (.inr 1)
  have ll₀ : x 2+x 4=0 := by simpa [sum_six,lhead,ltail] using leftSum (.inr 0)
  have ll₁ : x 3+x 5=0 := by simpa [sum_six,lhead,ltail] using leftSum (.inr 1)
  have tie₀ : x 0=x 4 := by linear_combination rr₀-ll₀
  have tie₁ : x 1=x 5 := by linear_combination rr₁-ll₁
  let shift (j : Fin n) : Fin (n+4) := ⟨4+j.val,by have := j.isLt; omega⟩
  let f (j : Fin n) := F (shift j)
  have first₀ : f i₀=x 4 := congrArg F (Fin.ext rfl)
  have first₁ : f i₁=x 5 := congrArg F (Fin.ext rfl)
  have tail (z : Fin k) : f (oldtail z)=y z := congrArg F (Fin.ext (by change 4+(2+z.val)=6+z.val; omega))
  have originalL (v : Fin a) : (∑ j,if left j=v then f j else 0)=0 := by
    rw [← old.sum_comp (fun j : Fin n => if left j=v then f j else 0),Fintype.sum_sum_type,Fin.sum_univ_two]
    change (if left i₀=v then f i₀ else 0)+(if left i₁=v then f i₁ else 0) +
      (∑ z : Fin k, if left (oldtail z)=v then f (oldtail z) else 0)=0
    simpa [sum_six,lhead,ltail,tie₀,tie₁,first₀,first₁,tail] using leftSum (.inl v)
  have originalR (v : Fin b) : (∑ j,if right j=v then f j else 0)=0 := by
    rw [← old.sum_comp (fun j : Fin n => if right j=v then f j else 0),Fintype.sum_sum_type,Fin.sum_univ_two]
    change (if right i₀=v then f i₀ else 0)+(if right i₁=v then f i₁ else 0) +
      (∑ z : Fin k, if right (oldtail z)=v then f (oldtail z) else 0)=0
    simpa [sum_six,rhead,rtail,first₀,first₁,tail] using rightSum (.inl v)
  let project (j : Fin (n+4)) : Fin n :=
    ⟨if j.val<4 then j.val%2 else j.val-4,by split <;> have := j.isLt <;> omega⟩
  have early (s : Fin 4) :
      F (added (.inl ⟨s.val,by have := s.isLt; omega⟩))=0 ↔
        f (old (.inl ⟨s.val%2,Nat.mod_lt _ (by decide)⟩))=0 := by
    fin_cases s
    · change x 0=0 ↔ f i₀=0
      rw [first₀,tie₀]
    · change x 1=0 ↔ f i₁=0
      rw [first₁,tie₁]
    · change x 2=0 ↔ f i₀=0
      rw [first₀,eq_neg_of_add_eq_zero_left ll₀,neg_eq_zero]
    · change x 3=0 ↔ f i₁=0
      rw [first₁,eq_neg_of_add_eq_zero_left ll₁,neg_eq_zero]
  have zeroes (j : Fin (n+4)) : F j=0 ↔ f (project j)=0 := by
    by_cases sm : j.val<4
    · let s : Fin 4 := ⟨j.val,sm⟩
      have aeq : added (.inl (⟨s.val,by have := s.isLt; omega⟩ : Fin 6))=j := Fin.ext rfl
      have peq : old (.inl (⟨s.val%2,Nat.mod_lt _ (by decide)⟩ : Fin 2))=project j := by
        apply Fin.ext
        change j.val%2=(if j.val<4 then j.val%2 else j.val-4)
        rw [if_pos sm]
      simpa only [aeq,peq] using early s
    · have eq : shift (project j)=j := by
        apply Fin.ext
        change 4+(if j.val<4 then j.val%2 else j.val-4)=j.val
        rw [if_neg sm]
        omega
      change F j=0 ↔ F (shift (project j))=0
      rw [eq]
  intro i j adj zi zj
  have adjacent :
      ((project j).val=(project i).val+1 ∨ ((project i).val+1=n ∧ (project j).val=0)) ∨
      ((project i).val=(project j).val+1 ∨ ((project j).val+1=n ∧ (project i).val=0)) := by
    dsimp only [project]
    split_ifs <;> omega
  have orig : f=0 := by
    rcases adjacent with hn|hn
    · exact detect f originalL originalR _ _ hn ((zeroes i).mp zi) ((zeroes j).mp zj)
    · exact detect f originalL originalR _ _ hn ((zeroes j).mp zj) ((zeroes i).mp zi)
  funext e
  exact (zeroes e).mpr (congrFun orig (project e))

end CriticalSquareFlows

namespace CriticalSquareFlows

/-- Convert cyclic adjacency in the finite list to addition by one modulo its length. -/
private lemma cyclic_detector {k a b : ℕ} [NeZero k] (hk : 4 ≤ k)
    (left : Fin k → Fin a) (right : Fin k → Fin b) (d : (∀ f : Fin k→ℂ,
    (∀ i, (∑ j,if left j=i then f j else 0)=0) →
    (∀ i, (∑ j,if right j=i then f j else 0)=0) →
    ∀ i j : Fin k, (j.val=i.val+1 ∨ (i.val+1=k ∧ j.val=0)) →
        f i=0 → f j=0 → f=0)) :
    ∃ L : ZMod k → Fin a, ∃ R : ZMod k → Fin b, ∀ f : ZMod k → ℂ,
      (∀ i, (∑ j, if L j=i then f j else 0)=0) →
      (∀ i, (∑ j, if R j=i then f j else 0)=0) →
      ∀ j, f j=0 → f (j+1)=0 → f=0 := by
  classical
  let z : Fin k ≃ ZMod k := {
    toFun := fun j => (j.val : ZMod k)
    invFun := fun j => ⟨j.val,j.val_lt⟩
    left_inv := by intro j; apply Fin.ext; simp [ZMod.val_natCast,Nat.mod_eq_of_lt j.isLt]
    right_inv := fun j => ZMod.natCast_zmod_val j }
  refine ⟨fun j => left (z.symm j),fun j => right (z.symm j),?_⟩
  intro f lzero rzero j h₀ h₁
  let F (i : Fin k) := f (z i)
  have balance {n : ℕ} (m : Fin k → Fin n)
      (zero : ∀ i, (∑ j, if m (z.symm j)=i then f j else 0)=0) (i : Fin n) :
      (∑ s : Fin k, if m s=i then F s else 0)=0 := by
    have h := zero i
    rw [←z.sum_comp] at h
    simpa only [F,Equiv.symm_apply_apply] using h
  have adj : (z.symm (j+1)).val=(z.symm j).val+1 ∨ ((z.symm j).val+1=k ∧ (z.symm (j+1)).val=0) := by
    change (j+1).val=j.val+1 ∨ (j.val+1=k ∧ (j+1).val=0)
    rw [ZMod.val_add,ZMod.val_one'' (by omega : k≠1)]
    by_cases lt : j.val+1<k
    · exact Or.inl (Nat.mod_eq_of_lt lt)
    · have eq : j.val+1=k := by have := j.val_lt; omega
      exact Or.inr ⟨eq,by rw [eq,Nat.mod_self]⟩
  have all := d F (balance left lzero) (balance right rzero) (z.symm j) (z.symm (j+1)) adj
    (by simpa only [F,Equiv.apply_symm_apply] using h₀) (by simpa only [F,Equiv.apply_symm_apply] using h₁)
  funext v
  simpa only [F,Equiv.apply_symm_apply,Pi.zero_apply] using congrFun all (z.symm v)

/-- The column and color balances differ by one cyclic shift. Their
difference makes the sum of the middle weight and two adjacent bottom
weights constant. The row balances make that constant zero. -/
private lemma profile_vanish {k a b : ℕ} [NeZero k]
    (L : ZMod k → Fin a) (R : ZMod k → Fin b)
    (detect : ∀ f : ZMod k → ℂ, (∀ i, (∑ j, if L j=i then f j else 0)=0) →
      (∀ i, (∑ j, if R j=i then f j else 0)=0) → ∀ j, f j=0 → f (j+1)=0 → f=0)
    (A B C : ZMod k → ℂ) (col : ∀ j, A j+B j+C j=0)
    (color : ∀ j, A j+B (j-1)+C (j-2)=0)
    (left : ∀ i, (∑ j, if L (j-1)=i then A j else 0)=0) (middle : (∑ j,B j)=0)
    (right : ∀ i, (∑ j, if R j=i then C j else 0)=0)
    (s : ZMod k) (atA : A s=0) (atC : C (s-2)=0) : A=0 ∧ B=0 ∧ C=0 := by
  classical
  have bottom : (∑ j,C j)=0 := by
    have all : (∑ i : Fin b, ∑ j, if R j=i then C j else 0)=0 := by simp only [right,Finset.sum_const_zero]
    rw [Finset.sum_comm] at all
    simpa using all
  let D (j : ZMod k) := B j+C j+C (j-1)
  have step (j : ZMod k) : D (j+1)=D j := by
    have one := col (j+1)
    have two := color (j+1)
    rw [add_sub_cancel_right,show j+1-2=j-1 by ring] at two
    dsimp only [D]
    rw [add_sub_cancel_right]
    linear_combination one-two
  have constant (j : ZMod k) : D j=D 0 := by
    have fromNat (n : ℕ) : D (n : ZMod k)=D 0 := by
      induction n with
      | zero => simp
      | succ n ih => rw [Nat.cast_succ,step,ih]
    simpa only [ZMod.natCast_zmod_val] using fromNat j.val
  have shifted : (∑ j : ZMod k, C (j-1))=∑ j,C j := by
    exact Equiv.sum_comp (Equiv.subRight (1 : ZMod k)) C
  have sumD : (∑ j,D j)=0 := by
    simp only [D,Finset.sum_add_distrib,shifted,middle,bottom,add_zero]
  have van : D 0=0 := by
    have prod : (k:ℂ)*D 0=0 := by
      simpa only [constant,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul] using sumD
    exact (mul_eq_zero.mp prod).resolve_left (Nat.cast_ne_zero.mpr (NeZero.ne k))
  have equal (j : ZMod k) : A j=C (j-1) := by
    have z := (constant j).trans van
    dsimp only [D] at z
    linear_combination col j-z
  have Lzero (i : Fin a) : (∑ j, if L j=i then C j else 0)=0 := by
    have h := left i
    rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod k))] at h
    change (∑ j : ZMod k, if L (j+1-1)=i then A (j+1) else 0)=0 at h
    simpa only [equal,add_sub_cancel_right] using h
  have last := detect C Lzero right (s-2) atC (by
    rw [show s-2+1=s-1 by ring,←equal,atA])
  have first : A=0 := by funext j; rw [equal,last]; rfl
  refine ⟨first,?_,last⟩
  funext j
  have h := col j
  simpa only [first,last,Pi.zero_apply,zero_add,add_zero] using h

end CriticalSquareFlows

namespace CriticalSquareFlows

/-- The three physical edges in each column come from three disjoint kinds
of row. Their row labels are 0, 1, and 2, and the column label is the column itself. -/
lemma physical_graph {k : ℕ} [NeZero k] (hk : 4 ≤ k) (flow : (∃ a b : ℕ, a+b+1=k ∧ ∃ left : Fin k→Fin a, ∃ right : Fin k→Fin b,
    ∀ f : Fin k→ℂ,
    (∀ i, (∑ j,if left j=i then f j else 0)=0) →
    (∀ i, (∑ j,if right j=i then f j else 0)=0) →
    ∀ i j : Fin k, (j.val=i.val+1 ∨ (i.val+1=k ∧ j.val=0)) →
        f i=0 → f j=0 → f=0)) :
    ∃ a b : ℕ, a+b+1=k ∧
    ∃ edge : ((Fin a ⊕ (Unit ⊕ Fin b)) × ZMod k) → Bool,
    ∃ label : (Fin a ⊕ (Unit ⊕ Fin b)) → ZMod k,
      Fintype.card {ij // edge ij=true}=3*k ∧
      ∀ (s : ZMod k) (w : (Fin a ⊕ (Unit ⊕ Fin b)) × ZMod k → ℂ),
        (∀ ij, ¬edge ij=true → w ij=0) →
        (∀ i, (∑ j, w (i,j))=0) → (∀ j, (∑ i, w (i,j))=0) →
        (∀ c : ZMod k, (∑ ij, if label ij.1+ij.2=c then w ij else 0)=0) →
        (∀ ij, label ij.1+ij.2=s → w ij=0) → w=0 := by
  classical
  obtain ⟨a,b,vertices,left,right,d⟩ := flow
  obtain ⟨L,R,detect⟩ := cyclic_detector hk left right d
  let I := Fin a ⊕ (Unit ⊕ Fin b)
  let lo (j : ZMod k) : I := .inl (L (j-1))
  let mid : I := .inr (.inl ())
  let hi (j : ZMod k) : I := .inr (.inr (R j))
  let edge (ij : I × ZMod k) := decide (ij.1=lo ij.2 ∨ ij.1=mid ∨ ij.1=hi ij.2)
  let label : I → ZMod k := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))
  refine ⟨a,b,vertices,edge,label,?_,?_⟩
  · let row (t : Fin 3) (j : ZMod k) := ![lo j,mid,hi j] t
    let kind : I → Fin 3 := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))
    have tag (t : Fin 3) (j : ZMod k) : kind (row t j)=t := by fin_cases t <;> rfl
    let put (u : Fin 3 × ZMod k) : {ij // edge ij=true} :=
      ⟨(row u.1 u.2,u.2),by rcases u with ⟨t,j⟩; fin_cases t <;> simp [edge,row,Matrix.cons_val_two]⟩
    have recover (u : Fin 3 × ZMod k) : (kind (put u).val.1,(put u).val.2)=u := by
      obtain ⟨t,j⟩ := u
      change (kind (row t j),j)=(t,j)
      rw [tag]
    have inj : Function.Injective put := fun u v eq =>
      (recover u).symm.trans ((congrArg (fun (z : {ij // edge ij=true}) => (kind z.val.1,z.val.2)) eq).trans (recover v))
    have onto : Function.Surjective put := by
      rintro ⟨⟨i,j⟩,he⟩
      have alt : i=lo j ∨ i=mid ∨ i=hi j := of_decide_eq_true he
      rcases alt with rfl|rfl|rfl
      · exact ⟨(0,j),rfl⟩
      · exact ⟨(1,j),rfl⟩
      · exact ⟨(2,j),rfl⟩
    rw [← Fintype.card_congr (Equiv.ofBijective put ⟨inj,onto⟩),Fintype.card_prod,Fintype.card_fin,ZMod.card]
  · intro s w off rows cols colors black
    let A (j : ZMod k) := w (lo j,j)
    let B (j : ZMod k) := w (mid,j)
    let C (j : ZMod k) := w (hi j,j)
    have lo_mid (j : ZMod k) : lo j≠mid := Sum.inl_ne_inr
    have lo_hi (j : ZMod k) : lo j≠hi j := Sum.inl_ne_inr
    have mid_hi (j : ZMod k) : mid≠hi j := fun z => Sum.inl_ne_inr (Sum.inr.inj z)
    have expand (i : I) (j : ZMod k) : w (i,j)=(if i=lo j then A j else 0)+
        (if i=mid then B j else 0)+(if i=hi j then C j else 0) := by
      by_cases a₀ : i=lo j
      · subst i; rw [if_pos rfl,if_neg (lo_mid j),if_neg (lo_hi j),add_zero,add_zero]
      by_cases b₀ : i=mid
      · subst i; rw [if_neg a₀,if_pos rfl,if_neg (mid_hi j),zero_add,add_zero]
      by_cases c₀ : i=hi j
      · subst i; rw [if_neg a₀,if_neg b₀,if_pos rfl,zero_add,zero_add]
      have outside : ¬edge (i,j)=true := by simp [edge,a₀,b₀,c₀]
      rw [off _ outside,if_neg a₀,if_neg b₀,if_neg c₀,add_zero,add_zero]
    have moment (j : ZMod k) (f : I → ℂ) :
        (∑ i : I, f i*w (i,j))=f (lo j)*A j+f mid*B j+f (hi j)*C j := by
      simp only [expand,mul_add,mul_ite,mul_zero,Finset.sum_add_distrib]
      rw [Fintype.sum_ite_eq' (lo j) (fun i => f i*A j),Fintype.sum_ite_eq' mid (fun i => f i*B j),
        Fintype.sum_ite_eq' (hi j) (fun i => f i*C j)]
    have col (j : ZMod k) : A j+B j+C j=0 := by
      have h := moment j (fun _ => 1)
      simp only [one_mul] at h
      exact h.symm.trans (cols j)
    have sel (c j : ZMod k) : (∑ i, if label i+j=c then w (i,j) else 0) =
        (if (0 : ZMod k)+j=c then A j else 0)+(if 1+j=c then B j else 0)+(if 2+j=c then C j else 0) := by
      let gate (t : ZMod k) : ℂ := if t+j=c then 1 else 0
      have action (t : ZMod k) (v : ℂ) : gate t*v=(if t+j=c then v else 0) := by
        by_cases h : t+j=c <;> simp [gate,h]
      calc
        _ = ∑ i, gate (label i)*w (i,j) := Finset.sum_congr rfl fun i _ => (action (label i) _).symm
        _ = _ := by
          rw [moment j (fun i => gate (label i))]
          change gate 0*A j+gate 1*B j+gate 2*C j=_
          rw [action,action,action]
    have select (a c : ZMod k) (f : ZMod k → ℂ) :
        (∑ j, if a+j=c then f j else 0)=f (c-a) := by
      have iff (j : ZMod k) : a+j=c ↔ j=c-a := by rw [eq_sub_iff_add_eq,add_comm j a]
      simp [iff]
    have color (c : ZMod k) : A c+B (c-1)+C (c-2)=0 := by
      have h := colors c
      rw [Fintype.sum_prod_type,Finset.sum_comm] at h
      have bycol : (∑ j, ∑ i : I, if label i+j=c then w (i,j) else 0) =
          ∑ j, ((if (0:ZMod k)+j=c then A j else 0)+(if 1+j=c then B j else 0)+(if 2+j=c then C j else 0)) :=
        Finset.sum_congr rfl fun j _ => sel c j
      have z := bycol.symm.trans h
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib,select,select,select,sub_zero] at z
      exact z
    have lzero (v : Fin a) : (∑ j, if L (j-1)=v then A j else 0)=0 := by
      have atL (j : ZMod k) : w ((.inl v : I),j)=(if L (j-1)=v then A j else 0) := by
        have eq : (.inl v : I)=lo j ↔ L (j-1)=v :=
          ⟨fun z => (Sum.inl.inj z).symm,fun z => congrArg Sum.inl z.symm⟩
        have ne₁ : (.inl v : I)≠mid := Sum.inl_ne_inr
        have ne₂ : (.inl v : I)≠hi j := Sum.inl_ne_inr
        rw [expand,if_neg ne₁,if_neg ne₂,add_zero,add_zero]
        by_cases h : L (j-1)=v
        · rw [if_pos (eq.mpr h),if_pos h]
        · rw [if_neg (fun z => h (eq.mp z)),if_neg h]
      exact (Finset.sum_congr rfl (fun j _ => atL j)).symm.trans (rows (.inl v))
    have mzero : (∑ j,B j)=0 := rows mid
    have rzero (v : Fin b) : (∑ j, if R j=v then C j else 0)=0 := by
      have atR (j : ZMod k) : w ((.inr (.inr v) : I),j)=(if R j=v then C j else 0) := by
        have eq : (.inr (.inr v) : I)=hi j ↔ R j=v :=
          ⟨fun z => (Sum.inr.inj (Sum.inr.inj z)).symm,fun z => congrArg Sum.inr (congrArg Sum.inr z.symm)⟩
        have ne₀ : (.inr (.inr v) : I)≠lo j := Sum.inr_ne_inl
        have ne₁ : (.inr (.inr v) : I)≠mid := fun z => Sum.inr_ne_inl (Sum.inr.inj z)
        rw [expand,if_neg ne₀,if_neg ne₁,zero_add,zero_add]
        by_cases h : R j=v
        · rw [if_pos (eq.mpr h),if_pos h]
        · rw [if_neg (fun z => h (eq.mp z)),if_neg h]
      exact (Finset.sum_congr rfl (fun j _ => atR j)).symm.trans (rows (.inr (.inr v)))
    have atA : A s=0 := black (lo s,s) (by change 0+s=s; rw [zero_add])
    have atC : C (s-2)=0 := black (hi (s-2),s-2) (by change 2+(s-2)=s; ring)
    obtain ⟨Az,Bz,Cz⟩ := profile_vanish L R detect A B C col color lzero mzero rzero s atA atC
    funext ⟨i,j⟩
    rw [expand,Az,Bz,Cz]
    simp

end CriticalSquareFlows

namespace CriticalSquareFlows

/-- Transport both matrix axes, all samples and the marked labels through
bijections, preserving every normal equation and their vector-valued sum. -/
private lemma transport_marked {A B P Q A' B' P' Q' : Type*}
    [Fintype A] [Fintype B] [Fintype Q] [Fintype A'] [Fintype B'] [Fintype Q']
    (ea : A ≃ A') (eb : B ≃ B') (ep : P ≃ P') (em : Q' ≃ Q) (first : Q ↪ P)
    (one : ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ H : Q → A × B → ℂ,
      (∀ t s, (∑ ij : A × B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (first t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (first t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0) :
    ∃ label : Q' ↪ P', ∃ X : P' → A' → ℂ, ∃ Y : P' → B' → ℂ, ∀ H : Q' → A' × B' → ℂ,
      (∀ t s, (∑ ij : A' × B', (X s ij.1*Y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, Y (label t) j*H t (i,j))=0) → (∀ t j, (∑ i, X (label t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0 := by
  obtain ⟨x,y,direct⟩ := one
  let label := (em.toEmbedding.trans first).trans ep.toEmbedding
  let X (s : P') (i : A') := x (ep.symm s) (ea.symm i)
  let Y (s : P') (j : B') := y (ep.symm s) (eb.symm j)
  have tag (t : Q') : label t=ep (first (em t)) := rfl
  refine ⟨label,X,Y,?_⟩
  intro H outer row col total
  let pull (t : Q) (ij : A × B) := H (em.symm t) (ea ij.1,eb ij.2)
  have out (t : Q) (s : P) : (∑ ij : A×B, (x s ij.1*y s ij.2)*pull t ij)=0 := by
    have h := outer (em.symm t) (ep s)
    rw [← (ea.prodCongr eb).sum_comp] at h
    simpa only [pull,X,Y,Equiv.prodCongr_apply,Prod.map,Equiv.symm_apply_apply] using h
  have rows (t : Q) (i : A) : (∑ j, y (first t) j*pull t (i,j))=0 := by
    have h := row (em.symm t) (ea i)
    rw [← eb.sum_comp] at h
    simpa only [tag,Y,pull,Equiv.symm_apply_apply,Equiv.apply_symm_apply] using h
  have cols (t : Q) (j : B) : (∑ i, x (first t) i*pull t (i,j))=0 := by
    have h := col (em.symm t) (eb j)
    rw [← ea.sum_comp] at h
    simpa only [tag,X,pull,Equiv.symm_apply_apply,Equiv.apply_symm_apply] using h
  have trace : (∑ t,pull t)=0 := by
    funext ij
    have h := congrFun total (ea ij.1,eb ij.2)
    rw [Finset.sum_apply,← em.symm.sum_comp] at h
    simpa only [pull,Finset.sum_apply,Pi.zero_apply] using h
  have zero := direct pull out rows cols trace
  funext t ij
  simpa only [pull,Equiv.apply_symm_apply,Equiv.symm_apply_apply,Prod.mk.eta,Pi.zero_apply] using
    congrFun (congrFun zero (em t)) (ea.symm ij.1,eb.symm ij.2)

/-- A detecting auxiliary graph gives k independent marked normal spaces
on the two-dimensional normal level, in the original finite tensor axes. -/
lemma square_marked_batch {k r : ℕ} (hk : 4 ≤ k) (level : r+1=(k-1)*(k-1)) (flow : (∃ a b : ℕ, a+b+1=k ∧ ∃ left : Fin k→Fin a, ∃ right : Fin k→Fin b,
    ∀ f : Fin k→ℂ,
    (∀ i, (∑ j,if left j=i then f j else 0)=0) →
    (∀ i, (∑ j,if right j=i then f j else 0)=0) →
    ∀ i j : Fin k, (j.val=i.val+1 ∨ (i.val+1=k ∧ j.val=0)) →
        f i=0 → f j=0 → f=0)) :
    ∃ first : Fin k ↪ Fin r, ∃ x : Fin r → Fin k → ℂ, ∃ y : Fin r → Fin k → ℂ,
    ∀ H : Fin k → Fin k × Fin k → ℂ,
      (∀ t s, (∑ ij : Fin k × Fin k, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (first t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (first t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0 := by
  classical
  let _ : NeZero k := ⟨by omega⟩
  obtain ⟨a,b,vertices,edge,label,edges,fiber⟩ := physical_graph hk flow
  let I := Fin a ⊕ (Unit ⊕ Fin b)
  let P := {ij : I × ZMod k // ¬edge ij=true} ⊕ ZMod k
  have ca : Fintype.card I=k := by simp [I]; omega
  have cp : Fintype.card P=r := by
    have dim : k*k=(k-1)*(k-1)+(k-1)+(k-1)+1 := by
      calc
        _ = (k-1+1)*(k-1+1) := by rw [show k-1+1=k by omega]
        _ = _ := by ring
    have room : 3*k ≤ k*k := Nat.mul_le_mul_right k (by omega)
    simp only [P,Fintype.card_sum,Fintype.card_subtype_compl,Fintype.card_prod,ca,ZMod.card]
    change k*k - Fintype.card {ij : I × ZMod k // edge ij=true} + k = r
    rw [show Fintype.card {ij : I × ZMod k // edge ij=true}=3*k from edges]
    omega
  let ea : I ≃ Fin k := Fintype.equivFinOfCardEq ca
  let eb : ZMod k ≃ Fin k := Fintype.equivFinOfCardEq (ZMod.card k)
  let ep : P ≃ Fin r := Fintype.equivFinOfCardEq cp
  let first : ZMod k ↪ P := Function.Embedding.inr
  exact transport_marked ea eb ep eb.symm first
    (CriticalLastSlice.TwoPlanes.batch_of_character_fibers (fun ij => edge ij=true) label id fiber)

end CriticalSquareFlows

namespace CriticalSquareFlows

/-- One common list of a−1 vectors, together with each chosen nonzero
vector separately, detects all linear functionals on the first factor. -/
theorem common_last_column_tests {a m : ℕ} (ha : 0<a) (v : Fin m → Fin a → ℂ)
    (nonzero : ∀ t, v t≠0) :
    ∃ W : Fin (a-1) → Fin a → ℂ, ∀ (t : Fin m) (g : Fin a → ℂ),
      (∀ j, ∑ i, W j i*g i=0) → (∑ i, v t i*g i)=0 → g=0 := by
  classical
  let _ : NeZero a := ⟨ha.ne'⟩
  let pts : Option (Fin m) → Fin a → ℂ := fun t => t.elim 1 v
  have all (t : Option (Fin m)) : pts t≠0 := by
    cases t with | none => exact one_ne_zero | some s => exact nonzero s
  obtain ⟨h,regular⟩ := Module.exists_dual_forall_apply_ne_zero (K:=ℂ) pts all
  have hn : h≠0 := fun hz => regular .none (by rw [hz,LinearMap.zero_apply])
  have transverse (t : Fin m) : h (v t) ≠ 0 := regular (.some t)
  have dim : Module.finrank ℂ h.ker=a-1 := by
    have eq := Module.Dual.finrank_ker_add_one_of_ne_zero hn
    rw [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at eq
    omega
  let B := (Module.finBasis ℂ h.ker).reindex (finCongr dim)
  refine ⟨fun j => (B j : Fin a → ℂ),?_⟩
  intro t g basis old
  let L : (Fin a → ℂ) →ₗ[ℂ] ℂ := {
    toFun := fun q => ∑ i,q i*g i
    map_add' := by intro u v; simp [add_mul,Finset.sum_add_distrib]
    map_smul' := by intro c v; simp [mul_assoc,Finset.mul_sum] }
  have on_hyperplane : L.comp h.ker.subtype=0 :=
    B.ext fun j => basis j
  have atPoint : L (v t)=0 := old
  have kill (p : Fin a → ℂ) : L p=0 := by
    let c := h p / h (v t)
    let q := p-c • v t
    have hq : q∈h.ker := by
      change h (p-c • v t)=0
      rw [map_sub,map_smul,smul_eq_mul,show c*h (v t)=h p from div_mul_cancel₀ _ (transverse t),sub_self]
    have zero : L q=0 := LinearMap.congr_fun on_hyperplane ⟨q,hq⟩
    simpa only [q,map_sub,map_smul,atPoint,smul_zero,sub_zero] using zero
  funext i
  have eq := kill (Pi.single i 1)
  change (∑ j, (Pi.single i 1 : Fin a → ℂ) j*g j)=0 at eq
  simpa [Pi.single_apply,ite_mul] using eq

/-- An independent batch remains independent after adding one column and
a−1 samples. A zero sampled first vector can first be replaced by a
nonzero one: its previous constraints were zero, so only additional
constraints are imposed. -/
theorem add_one_column {a b r m : ℕ} (ha : 0<a)
    (one : ∃ mark : Fin m ↪ Fin r, ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
      ∀ F : Fin m → Fin a × Fin b → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin b,(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) → (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) →
        (∑ t,F t)=0 → F=0) :
    ∃ mark : Fin m ↪ Fin (r+(a-1)), ∃ x : Fin (r+(a-1)) → Fin a → ℂ,
      ∃ y : Fin (r+(a-1)) → Fin (b+1) → ℂ, ∀ F : Fin m → Fin a × Fin (b+1) → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin (b+1),(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) → (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) →
        (∑ t,F t)=0 → F=0 := by
  classical
  let _ : NeZero a := ⟨ha.ne'⟩
  obtain ⟨first,x₀,y,direct⟩ := one
  let x (s : Fin r) : Fin a → ℂ := if x₀ s=0 then 1 else x₀ s
  have xn (s : Fin r) : x s≠0 := by
    by_cases hz : x₀ s=0 <;> simp [x,hz]
  obtain ⟨W,test⟩ := common_last_column_tests ha (fun t => x (first t)) (fun t => xn (first t))
  let M := first.trans (Fin.castAddEmb (a-1))
  let X : Fin (r+(a-1)) → Fin a → ℂ := Fin.append x W
  let Y : Fin (r+(a-1)) → Fin (b+1) → ℂ :=
    Fin.append (fun s => Fin.snoc (y s) 0) (fun _ => Fin.snoc (0 : Fin b → ℂ) 1)
  have mark_val (t : Fin m) : M t=Fin.castAdd (a-1) (first t) := rfl
  refine ⟨M,X,Y,?_⟩
  intro F products rows cols total
  let old (t : Fin m) (ij : Fin a × Fin b) := F t (ij.1,ij.2.castSucc)
  have oldsum : ∑ t,old t=0 := by
    funext ij
    simpa only [old,Finset.sum_apply,Pi.zero_apply] using congrFun total (ij.1,ij.2.castSucc)
  have oldzero : old=0 := by
    apply direct old _ _ _ oldsum
    · intro t s
      by_cases zero : x₀ s=0
      · simp [zero]
      · have eq := products t (Fin.castAdd (a-1) s)
        simpa only [X,Y,Fin.append_left,Fintype.sum_prod_type,Fin.sum_univ_castSucc,Fin.snoc_castSucc,
          Fin.snoc_last,mul_zero,zero_mul,add_zero,old,x,if_neg zero] using eq
    · intro t i
      simpa only [Y,mark_val,Fin.append_left,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,
        zero_mul,add_zero,old] using rows t i
    · intro t j
      by_cases zero : x₀ (first t)=0
      · simp [zero]
      · simpa only [X,mark_val,Fin.append_left,x,if_neg zero,old] using cols t j.castSucc
  have last (t : Fin m) : (fun i => F t (i,Fin.last b))=0 := by
    apply test t
    · intro j
      have eq := products t (Fin.natAdd r j)
      simpa only [X,Y,Fin.append_right,Fintype.sum_prod_type,Fin.sum_univ_castSucc,Fin.snoc_castSucc,
        Fin.snoc_last,Pi.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero,zero_add,mul_one] using eq
    · simpa only [X,mark_val,Fin.append_left] using cols t (Fin.last b)
  funext t ij
  obtain ⟨i,j⟩ := ij
  exact Fin.lastCases (motive:=fun j => F t (i,j)=0) (congrFun (last t) i)
    (fun k => congrFun (congrFun oldzero t) (i,k)) j

/-- At the penultimate critical point count the one-column extension uses
exactly the new prescribed count and keeps the full ordinary batch size. -/
theorem near_square_of_square (k : ℕ) (hk : 2 ≤ k)
    (one : let r := (k-1)*(k-1)-1
      ∃ mark : Fin k ↪ Fin r, ∃ x : Fin r → Fin k → ℂ, ∃ y : Fin r → Fin k → ℂ,
      ∀ F : Fin k → Fin k × Fin k → ℂ,
        (∀ t s, ∑ ij : Fin k × Fin k,(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) → (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) →
        (∑ t,F t)=0 → F=0) :
    let b := k+1
    let r := (k-1)*(b-1)-1
    let h := (k+b)/2
    ∃ mark : Fin h ↪ Fin r, ∃ x : Fin r → Fin k → ℂ, ∃ y : Fin r → Fin b → ℂ,
      ∀ F : Fin h → Fin k × Fin b → ℂ,
        (∀ t s, ∑ ij : Fin k × Fin b,(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) → (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) →
        (∑ t,F t)=0 → F=0 := by
  dsimp only
  have sides : (k+(k+1))/2=k := by omega
  have diff : ((k-1)*(k-1)-1)+(k-1)=(k-1)*((k+1)-1)-1 := by
    have pos : 0<(k-1)*(k-1) := Nat.mul_pos (by omega) (by omega)
    have sum := congrArg (fun j : ℕ => (k-1)*j) (Nat.sub_add_cancel (show 1≤k by omega))
    rw [Nat.mul_add,Nat.mul_one] at sum
    rw [Nat.add_sub_cancel]
    omega
  rw [sides,←diff]
  exact add_one_column (by omega : 0<k) one

end CriticalSquareFlows

namespace CriticalSquareFlows

open CriticalLastSlice.TwoPlanes

/-- The original odd cyclic square construction, with both coordinates,
all samples, and the marked subset reindexed by their finite cardinalities. -/
theorem odd_square_marking (k : ℕ) (hk : 3≤k) (odd : Odd k) :
    let r := (k-1)*(k-1)-1
    ∃ mark : Fin k ↪ Fin r, ∃ x : Fin r → Fin k → ℂ, ∃ y : Fin r → Fin k → ℂ,
    ∀ F : Fin k → Fin k × Fin k → ℂ,
      (∀ t s, ∑ ij : Fin k × Fin k,(x s ij.1*y s ij.2)*F t ij=0) →
      (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) → (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) →
      (∑ t,F t)=0 → F=0 := by
  classical
  intro r
  let _ : NeZero k := ⟨by omega⟩
  let P := {ij : ZMod k × ZMod k // ¬(ij.2=ij.1 ∨ ij.2=ij.1+1 ∨ ij.2=ij.1+2)} ⊕ ZMod k
  have lev : r+1=(k-1)*(k-1) := by
    have pos := Nat.mul_pos (show 0<k-1 by omega) (show 0<k-1 by omega)
    dsimp [r]
    omega
  have size : Fintype.card P=r := (square_point_card k hk).trans (square_card_of_level hk lev).symm
  let ea : ZMod k ≃ Fin k := Fintype.equivFinOfCardEq (ZMod.card k)
  let ep : P ≃ Fin r := Fintype.equivFinOfCardEq size
  exact transport_marked ea ea ep ea.symm Function.Embedding.inr (odd_square_batch k hk odd)

/-- For odd k, the ordinary near-square marking is unconditional. -/
theorem odd_near_square (k : ℕ) (hk : 3≤k) (odd : Odd k) :
    let b := k+1
    let r := (k-1)*(b-1)-1
    let h := (k+b)/2
    ∃ mark : Fin h ↪ Fin r, ∃ x : Fin r → Fin k → ℂ, ∃ y : Fin r → Fin b → ℂ,
    ∀ F : Fin h → Fin k × Fin b → ℂ,
      (∀ t s, ∑ ij : Fin k × Fin b,(x s ij.1*y s ij.2)*F t ij=0) →
      (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) → (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) →
      (∑ t,F t)=0 → F=0 :=
  near_square_of_square k (by omega) (odd_square_marking k hk odd)

end CriticalSquareFlows

namespace CriticalSquareFlows

open CriticalLastSlice.TwoPlanes Arxiv.«0805.3777»

/-- At consecutive sides the dimension count always leaves enough batches
of size k. Write k=d+2. At most d batches would violate 2r≤(2k+1)s. -/
theorem consecutive_budget {k r s : ℕ} (hk : 2≤k) (level : r+1=(k-1)*k)
    (budget : 2*r ≤ s*(k+(k+1))) : r ≤ s*k := by
  obtain ⟨d,rfl⟩ : ∃ d : ℕ,k=d+2 := ⟨k-2,by omega⟩
  rw [show d+2-1=d+1 by omega] at level
  have lower : d+1 ≤ s := by
    by_contra! small
    have upper := Nat.mul_le_mul_right ((d+2)+(d+2+1)) (show s≤d by omega)
    nlinarith
  have fit := Nat.mul_le_mul_right (d+2) lower
  omega

/-- The consecutive-side dimension count caps the third side at k(k−2). -/
theorem consecutive_cutoff {k r n : ℕ} (hk : 2≤k) (level : r+1=(k-1)*k) (enough : n≤r)
    (budget : 2*r ≤ (r-n)*(k+(k+1))) : n ≤ k*(k-2) := by
  have fit := consecutive_budget hk level budget
  obtain ⟨d,rfl⟩ : ∃ d : ℕ,k=d+2 := ⟨k-2,by omega⟩
  rw [show d+2-1=d+1 by omega] at level
  have lower : d+1 ≤ r-n := by
    by_contra! small
    have upper := Nat.mul_le_mul_right (d+2) (show r-n≤d by omega)
    nlinarith
  have total := Nat.sub_add_cancel enough
  rw [Nat.add_sub_cancel]
  nlinarith

/-- No shared point is required in the consecutive-side two-plane family. -/
theorem consecutive_no_overflow (k : ℕ) (hk : 2≤k) :
    let b := k+1
    let r := (k-1)*(b-1)-1
    r ≤ (2*r ⌈/⌉ (k+b))*((k+b)/2) := by
  intro b r
  rw [show (k+b)/2=k by dsimp [b]; omega]
  apply consecutive_budget hk
  · dsimp [r,b]
    have pos := Nat.mul_pos (show 0<k-1 by omega) (show 0<k by omega)
    omega
  · rw [Nat.mul_comm (2*r ⌈/⌉ (k+b))]
    exact (ceilDiv_le_iff_le_mul (by dsimp [b]; omega : 0<k+b)).mp le_rfl

/-- A square marked witness gives the actual generic rank at the entire
two-plane consecutive-side count level. -/
theorem consecutive_generic_rank_of_square {k n r : ℕ} (hk : 3≤k) (sorted : k+1≤n)
    (level : r+1=(k-1)*k) (count : r=k*(k+1)*n ⌈/⌉ (k+(k+1)+n-2))
    (one : let n := (k-1)*(k-1)-1
      ∃ mark : Fin k ↪ Fin n, ∃ x : Fin n → Fin k → ℂ, ∃ y : Fin n → Fin k → ℂ,
      ∀ F : Fin k → Fin k × Fin k → ℂ,
        (∀ t s, ∑ ij : Fin k × Fin k,(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) → (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) →
        (∑ t,F t)=0 → F=0) :
    IsGenericRank [k,k+1,n] r := by
  obtain ⟨c,rfl⟩ : ∃ c : ℕ,n=c+1 := ⟨n-1,by omega⟩
  obtain ⟨_,enough,budget⟩ := relation_budget k (k+1) c r hk (by omega) (by simpa only [Nat.add_sub_cancel] using level) count
  have fit := consecutive_budget (by omega : 2≤k) level budget
  have marking := near_square_of_square k (by omega) one
  dsimp only at marking
  rw [show (k+(k+1))/2=k by omega,show (k-1)*((k+1)-1)-1=r by rw [Nat.add_sub_cancel]; omega] at marking
  obtain ⟨mark,x,y,direct⟩ := marking
  apply generic_rank_of_witness hk (by omega) sorted count
  apply spans_from_independent_batch mark (Fintype.card_fin k) (Fintype.card_fin (k+1))
    (Fintype.card_fin r) enough (by simpa only [Fintype.card_fin] using fit)
  exact ⟨x,y,direct⟩

end CriticalSquareFlows

namespace CriticalSquareFlows

open Arxiv.«0805.3777»

/-- The largest third side allowed by the two-plane dimension count is
k(k−2). Here the total parameter count exceeds the dimension by k+1. -/
theorem consecutive_top_count (k : ℕ) (hk : 4≤k) :
    let n := k*(k-2)
    let r := (k-1)*k-1
    k+1≤n ∧ r+1=(k-1)*k ∧ r=k*(k+1)*n ⌈/⌉ (k+(k+1)+n-2) := by
  obtain ⟨d,rfl⟩ : ∃ d : ℕ,k=d+4 := ⟨k-4,by omega⟩
  intro n r
  let D := (d+4)+((d+4)+1)+n-2
  have first : d+4-1=d+3 := by omega
  have rvalue : r=d*d+7*d+11 := by
    change (d+3)*(d+4)-1 = _
    rw [show (d+3)*(d+4)=(d*d+7*d+11)+1 by ring,Nat.add_sub_cancel]
  have nvalue : n=d*d+6*d+8 := by
    change (d+4)*(d+2) = _
    ring
  have dvalue : D=d*d+8*d+15 := by dsimp [D]; omega
  have pos : 0<D := by omega
  have offset : D*r=(d+4)*((d+4)+1)*n+(d+5) := by rw [dvalue,rvalue,nvalue]; ring
  have decomp : D*(r-1)+D=D*r := by
    rw [← Nat.mul_add_one,show r-1+1=r by omega]
  have below : D*(r-1)<(d+4)*((d+4)+1)*n := by omega
  have upper : (d+4)*((d+4)+1)*n ⌈/⌉ D ≤ r := (ceilDiv_le_iff_le_mul pos).mpr (by omega)
  have lower : r ≤ (d+4)*((d+4)+1)*n ⌈/⌉ D := by
    by_contra! small
    have eq := (ceilDiv_le_iff_le_mul pos).mp
      (show (d+4)*((d+4)+1)*n ⌈/⌉ D ≤ r-1 by omega)
    omega
  refine ⟨by omega,?_,lower.antisymm upper⟩
  rw [first,rvalue]
  ring

/-- Every square marking gives the actual generic rank at the largest
third side of the corresponding consecutive format. -/
theorem consecutive_top_of_square (k : ℕ) (hk : 4≤k)
    (one : let n := (k-1)*(k-1)-1
      ∃ mark : Fin k ↪ Fin n, ∃ x : Fin n → Fin k → ℂ, ∃ y : Fin n → Fin k → ℂ,
      ∀ F : Fin k → Fin k × Fin k → ℂ,
        (∀ t s, ∑ ij : Fin k × Fin k,(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) → (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) →
        (∑ t,F t)=0 → F=0) :
    IsGenericRank [k,k+1,k*(k-2)] ((k-1)*k-1) := by
  obtain ⟨sorted,level,count⟩ := consecutive_top_count k hk
  exact consecutive_generic_rank_of_square (by omega) sorted level count one

/-- For each odd k≥5, the complex generic rank of k×(k+1)×k(k−2)
is k(k−1)−1. The smallest instance is 5×6×15 of rank 19. -/
theorem odd_consecutive_top (k : ℕ) (hk : 4≤k) (odd : Odd k) :
    IsGenericRank [k,k+1,k*(k-2)] ((k-1)*k-1) :=
  consecutive_top_of_square k hk (odd_square_marking k (by omega) odd)

theorem five_six_fifteen : IsGenericRank [5,6,15] 19 :=
  odd_consecutive_top 5 (by decide) (by decide)

end CriticalSquareFlows

namespace CriticalSquareFlows

open Arxiv.«0805.3777»

/-- The cyclic odd construction and the subdivided even graph together
supply a full square marking for every side of size at least four. -/
theorem all_square_marking {k r : ℕ} (hk : 4≤k) (level : r+1=(k-1)*(k-1)) :
    ∃ first : Fin k ↪ Fin r, ∃ x : Fin r→Fin k→ℂ, ∃ y : Fin r→Fin k→ℂ,
  ∀ H : Fin k→Fin k × Fin k→ℂ,
    (∀ t s, (∑ ij : Fin k × Fin k,(x s ij.1*y s ij.2)*H t ij)=0) →
    (∀ t i,(∑ j,y (first t) j*H t (i,j))=0) →
    (∀ t j,(∑ i,x (first t) i*H t (i,j))=0) → (∑ t,H t)=0 → H=0 := by
  rcases Nat.even_or_odd k with even | odd
  · exact square_marked_batch hk level
      (all_even_of_step (fun _ two flow => subdivide two flow) k hk even)
  have eq : r=(k-1)*(k-1)-1 := by omega
  rw [eq]
  exact odd_square_marking k (by omega) odd

private theorem square_level_value {k r : ℕ} (large : 4≤k) (level : r+1=(k-1)*(k-1)) :
    r=k*(k-2) ∧ r+2*k=k*k := by
  obtain ⟨t,rfl⟩ : ∃ t, k=t+4 := ⟨k-4,by omega⟩
  simp only [show t+4-1=t+3 by omega,show t+4-2=t+2 by omega] at level ⊢
  constructor <;> nlinarith only [level]

/-- The complete r=(k−1)²−1 level for square first and second factors. -/
theorem square_rank_level {k n r : ℕ} (hk : 4≤k) (ordered : k≤n)
    (level : r+1=(k-1)*(k-1)) (count : r=k*k*n ⌈/⌉ (k+k+n-2)) :
    IsGenericRank [k,k,n] r := by
  have positive : 0<k+k+n-2 := by omega
  have mass := (ceilDiv_le_iff_le_mul positive).mp count.ge
  have sr := (square_level_value hk level).2
  have weight := congrArg (fun t : ℕ => t*n) sr
  have den := congrArg (fun t : ℕ => t*r) (Nat.sub_add_cancel (by omega : 2≤k+k+n))
  have bound : k*n+r≤k*r := by nlinarith only [mass,weight,den]
  have nr := Nat.le_of_mul_le_mul_left (show k*n≤k*r by omega) (by omega : 0<k)
  have eq := congrArg (fun t : ℕ => t*k) (Nat.sub_add_cancel nr)
  have fit : r≤(r-n)*k := by nlinarith only [bound,eq]
  obtain ⟨mark,x,y,direct⟩ := all_square_marking hk level
  apply CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by omega) le_rfl ordered count
  exact CriticalLastSlice.TwoPlanes.spans_from_independent_batch (A:=Fin k) (B:=Fin k)
    mark (Fintype.card_fin _) (Fintype.card_fin _) (Fintype.card_fin _) nr
    (by simpa only [Fintype.card_fin] using fit) ⟨x,y,direct⟩

/-- At the largest member of the level the secant parameter count is exact. -/
theorem square_rank_endpoint (k : ℕ) (hk : 4≤k) :
    IsGenericRank [k,k,(k-1)*(k-2)] (k*(k-2)) := by
  obtain ⟨t,rfl⟩ : ∃ t,k=t+4 := ⟨k-4,by omega⟩
  simp only [show t+4-1=t+3 by omega,show t+4-2=t+2 by omega]
  have level : (t+4)*(t+2)+1=(t+4-1)*(t+4-1) := by
    rw [show t+4-1=t+3 by omega]; ring
  have budget : t+4+(t+4)+(t+3)*(t+2)-2=(t+4)*(t+3) := by
    have e : t+4+(t+4)+(t+3)*(t+2)=(t+4)*(t+3)+2 := by ring
    omega
  apply square_rank_level (by omega) (by nlinarith only [Nat.zero_le (t*t)]) level
  rw [budget]
  have eq : (t+4)*(t+4)*((t+3)*(t+2))=((t+4)*(t+3))*((t+4)*(t+2)) := by ring
  rw [eq]
  have pos : 0<(t+4)*(t+3) := by positivity
  apply le_antisymm
  · exact Nat.le_of_mul_le_mul_left ((ceilDiv_le_iff_le_mul pos).mp le_rfl) pos
  · exact (ceilDiv_le_iff_le_mul pos).mpr le_rfl

theorem consecutive_rank_level {k n r : ℕ} (hk : 4≤k) (sorted : k+1≤n)
    (level : r+1=(k-1)*k) (count : r=k*(k+1)*n ⌈/⌉ (k+(k+1)+n-2)) :
    IsGenericRank [k,k+1,n] r := by
  have positive : 0<(k-1)*(k-1) := Nat.mul_pos (by omega) (by omega)
  exact consecutive_generic_rank_of_square (by omega) sorted level count
    (all_square_marking hk (by omega))

theorem consecutive_rank_endpoint (k : ℕ) (hk : 4≤k) :
    IsGenericRank [k,k+1,k*(k-2)] ((k-1)*k-1) := by
  have positive : 0<(k-1)*(k-1) := Nat.mul_pos (by omega) (by omega)
  exact consecutive_top_of_square k hk (all_square_marking hk (by omega))

theorem even_square_example : IsGenericRank [100,100,9702] 9800 := square_rank_endpoint 100 (by decide)

theorem even_consecutive_example : IsGenericRank [100,101,9800] 9899 :=
  consecutive_rank_endpoint 100 (by decide)

end CriticalSquareFlows

namespace CriticalSquareFlows

private lemma zero_theta (v : Fin 3 → ℂ) (total : v 0+v 1+v 2=0) (a b : Fin 3)
    (distinct : a≠b) (first : v a=0) (second : v b=0) : v=0 := by
  have choices (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by fin_cases i <;> decide
  rcases choices a with rfl | rfl | rfl <;> rcases choices b with rfl | rfl | rfl <;> first
    | exact False.elim (distinct rfl)
    | funext t; change v t=0; rcases choices t with rfl | rfl | rfl <;> first | exact first | exact second | linear_combination total-first-second

/-- On the three paths, each edge has the same zero condition as its path
weight. Two adjacent edges on different paths determine the entire flow. -/
private lemma theta_detect {n : ℕ} (path : Fin n → Fin 3) (v : Fin 3 → ℂ) (f : Fin n → ℂ)
    (total : v 0+v 1+v 2=0) (values : ∀ i, f i=0 ↔ v (path i)=0)
    (different : ∀ i j : Fin n, (j.val=i.val+1 ∨ (i.val+1=n ∧ j.val=0)) → path i≠path j) :
    ∀ i j : Fin n, (j.val=i.val+1 ∨ (i.val+1=n ∧ j.val=0)) → f i=0 → f j=0 → f=0 := by
  intro i j adjacent hi hj
  have vanishes := zero_theta v total (path i) (path j) (different i j adjacent) ((values i).mp hi) ((values j).mp hj)
  funext e
  exact (values e).mpr (congrFun vanishes (path e))

/-- Two parallel ordinary edges and one path through the signed chord. -/
theorem chord_four : (∃ a b : ℕ, a+b+1=4 ∧ ∃ source sink : Fin a, ∃ _ : Fin b,
    ∃ left : Fin 4→Fin a, ∃ right : Fin 4→Fin b,
    ∀ f : Fin 4→ℂ,
    (∀ i,(∑ j,if j.val=0 then (if source=i then f j else 0)-(if sink=i then f j else 0)
        else if left j=i then f j else 0)=0) →
    (∀ i,(∑ j,if j.val≠0 ∧ right j=i then f j else 0)=0) →
    ∀ i j : Fin 4,(j.val=i.val+1 ∨ (i.val+1=4 ∧ j.val=0)) →
       f i=0 → f j=0 → f=0) := by
  let l : Fin 4 → Fin 2 := ![0,0,1,0]
  let r : Fin 4 → Fin 1 := fun _ => 0
  refine ⟨2,1,by decide,0,1,0,l,r,?_⟩
  intro f left _
  have flow := left 0
  have through := left 1
  norm_num [l,Fin.sum_univ_succ] at flow through
  change f 0+(f 1+f 3)=0 at flow
  change -f 0+f 2=0 at through
  have c₂ : f 2=f 0 := by linear_combination through
  let path : Fin 4 → Fin 3 := ![0,1,0,2]
  let v : Fin 3 → ℂ := ![f 0,f 1,f 3]
  apply theta_detect path v f _ _ (by decide)
  · change f 0+f 1+f 3=0
    linear_combination flow
  · intro i
    fin_cases i
    · rfl
    · rfl
    · change f 2=0 ↔ f 0=0
      rw [c₂]
    · rfl

/-- The left terminals are joined by the chord and by two ordinary
length-two paths. -/
theorem chord_five : (∃ a b : ℕ, a+b+1=5 ∧ ∃ source sink : Fin a, ∃ _ : Fin b,
    ∃ left : Fin 5→Fin a, ∃ right : Fin 5→Fin b,
    ∀ f : Fin 5→ℂ,
    (∀ i,(∑ j,if j.val=0 then (if source=i then f j else 0)-(if sink=i then f j else 0)
        else if left j=i then f j else 0)=0) →
    (∀ i,(∑ j,if j.val≠0 ∧ right j=i then f j else 0)=0) →
    ∀ i j : Fin 5,(j.val=i.val+1 ∨ (i.val+1=5 ∧ j.val=0)) →
       f i=0 → f j=0 → f=0) := by
  let l : Fin 5 → Fin 2 := ![0,0,0,1,1]
  let r : Fin 5 → Fin 2 := ![0,0,1,0,1]
  refine ⟨2,2,by decide,0,1,0,l,r,?_⟩
  intro f left right
  have flow := left 0
  have arm₀ := right 0
  have arm₁ := right 1
  norm_num [l,Fin.sum_univ_succ] at flow
  norm_num [r,Fin.sum_univ_succ] at arm₀ arm₁
  change f 0+(f 1+f 2)=0 at flow
  change f 1+f 3=0 at arm₀
  change f 2+f 4=0 at arm₁
  have a₃ : f 3= -f 1 := by linear_combination arm₀
  have b₄ : f 4= -f 2 := by linear_combination arm₁
  let path : Fin 5 → Fin 3 := ![0,1,2,1,2]
  let v : Fin 3 → ℂ := ![f 0,f 1,f 2]
  apply theta_detect path v f _ _ (by decide)
  · change f 0+f 1+f 2=0
    linear_combination flow
  · intro i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · change f 3=0 ↔ f 1=0
      rw [a₃,neg_eq_zero]
    · change f 4=0 ↔ f 2=0
      rw [b₄,neg_eq_zero]

/-- The left and right terminals have paths of lengths three, one and
two; the two-edge path starts with the chord. -/
theorem chord_six : (∃ a b : ℕ, a+b+1=6 ∧ ∃ source sink : Fin a, ∃ _ : Fin b,
    ∃ left : Fin 6→Fin a, ∃ right : Fin 6→Fin b,
    ∀ f : Fin 6→ℂ,
    (∀ i,(∑ j,if j.val=0 then (if source=i then f j else 0)-(if sink=i then f j else 0)
        else if left j=i then f j else 0)=0) →
    (∀ i,(∑ j,if j.val≠0 ∧ right j=i then f j else 0)=0) →
    ∀ i j : Fin 6,(j.val=i.val+1 ∨ (i.val+1=6 ∧ j.val=0)) →
       f i=0 → f j=0 → f=0) := by
  let l : Fin 6 → Fin 3 := ![0,0,1,2,0,2]
  let r : Fin 6 → Fin 2 := ![0,1,0,1,0,0]
  refine ⟨3,2,by decide,0,1,0,l,r,?_⟩
  intro f left right
  have flow := left 0
  have through := left 1
  have last := left 2
  have middle := right 1
  norm_num [l,Fin.sum_univ_succ,show (0:Fin 3)≠2 by decide,show (1:Fin 3)≠2 by decide,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide] at flow through last
  norm_num [r,Fin.sum_univ_succ] at middle
  change f 0+(f 1+f 4)=0 at flow
  change -f 0+f 2=0 at through
  change f 3+f 5=0 at last
  change f 1+f 3=0 at middle
  have c₂ : f 2=f 0 := by linear_combination through
  have a₃ : f 3= -f 1 := by linear_combination middle
  have a₅ : f 5=f 1 := by linear_combination last-middle
  let path : Fin 6 → Fin 3 := ![0,1,0,1,2,1]
  let v : Fin 3 → ℂ := ![f 0,f 1,f 4]
  apply theta_detect path v f _ _ (by decide)
  · change f 0+f 1+f 4=0
    linear_combination flow
  · intro i
    fin_cases i
    · rfl
    · rfl
    · change f 2=0 ↔ f 0=0
      rw [c₂]
    · change f 3=0 ↔ f 1=0
      rw [a₃,neg_eq_zero]
    · rfl
    · change f 5=0 ↔ f 1=0
      rw [a₅]

/-- Two ordinary paths of length two and a three-edge chord path end at
the same pair of left terminals. -/
theorem chord_seven : (∃ a b : ℕ, a+b+1=7 ∧ ∃ source sink : Fin a, ∃ _ : Fin b,
    ∃ left : Fin 7→Fin a, ∃ right : Fin 7→Fin b,
    ∀ f : Fin 7→ℂ,
    (∀ i,(∑ j,if j.val=0 then (if source=i then f j else 0)-(if sink=i then f j else 0)
        else if left j=i then f j else 0)=0) →
    (∀ i,(∑ j,if j.val≠0 ∧ right j=i then f j else 0)=0) →
    ∀ i j : Fin 7,(j.val=i.val+1 ∨ (i.val+1=7 ∧ j.val=0)) →
       f i=0 → f j=0 → f=0) := by
  let l : Fin 7 → Fin 3 := ![0,0,2,0,1,1,1]
  let r : Fin 7 → Fin 3 := ![0,0,2,1,2,0,1]
  refine ⟨3,3,by decide,0,2,0,l,r,?_⟩
  intro f left right
  have flow := left 0
  have through := left 2
  have cEnd := right 2
  have aEnd := right 0
  have bEnd := right 1
  norm_num [l,Fin.sum_univ_succ,show (0:Fin 3)≠2 by decide,show (1:Fin 3)≠2 by decide,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide] at flow through
  norm_num [r,Fin.sum_univ_succ,show (0:Fin 3)≠2 by decide,show (1:Fin 3)≠2 by decide,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide] at cEnd aEnd bEnd
  change f 0+(f 1+f 3)=0 at flow
  change -f 0+f 2=0 at through
  change f 2+f 4=0 at cEnd
  change f 1+f 5=0 at aEnd
  change f 3+f 6=0 at bEnd
  have c₂ : f 2=f 0 := by linear_combination through
  have c₄ : f 4= -f 0 := by linear_combination cEnd-through
  have a₅ : f 5= -f 1 := by linear_combination aEnd
  have b₆ : f 6= -f 3 := by linear_combination bEnd
  let path : Fin 7 → Fin 3 := ![0,1,0,2,0,1,2]
  let v : Fin 3 → ℂ := ![f 0,f 1,f 3]
  apply theta_detect path v f _ _ (by decide)
  · change f 0+f 1+f 3=0
    linear_combination flow
  · intro i
    fin_cases i
    · rfl
    · rfl
    · change f 2=0 ↔ f 0=0
      rw [c₂]
    · rfl
    · change f 4=0 ↔ f 0=0
      rw [c₄,neg_eq_zero]
    · change f 5=0 ↔ f 1=0
      rw [a₅,neg_eq_zero]
    · change f 6=0 ↔ f 3=0
      rw [b₆,neg_eq_zero]

end CriticalSquareFlows

namespace CriticalSquareFlows

private theorem chord_sum_seven (f : Fin 7→ℂ) :
    (∑ i,f i)=f 0+(f 1+(f 2+(f 3+(f 4+(f 5+f 6))))) := by
  simp [Fin.sum_univ_succ]

private theorem same_ite {V W : Type*} [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (x y : V) (z : ℂ) :
    (if e x=e y then z else 0)=(if x=y then z else 0) := by
  by_cases h : x=y
  · subst y; simp
  · simp [h,e.injective.ne h]

/-- Keep the signed chord at index zero, and insert two vertices on each
of the first two ordinary edges. Either orientation of a projected
adjacent zero pair detects the original flow. -/
theorem chord_subdivide {n : ℕ} (hn : 3≤n) : (∃ a b : ℕ, a+b+1=n ∧ ∃ source sink : Fin a, ∃ _ : Fin b,
    ∃ left : Fin n→Fin a, ∃ right : Fin n→Fin b,
    ∀ f : Fin n→ℂ,
    (∀ i,(∑ j,if j.val=0 then (if source=i then f j else 0)-(if sink=i then f j else 0)
        else if left j=i then f j else 0)=0) →
    (∀ i,(∑ j,if j.val≠0 ∧ right j=i then f j else 0)=0) →
    ∀ i j : Fin n,(j.val=i.val+1 ∨ (i.val+1=n ∧ j.val=0)) →
       f i=0 → f j=0 → f=0) → (∃ a b : ℕ, a+b+1=(n+4) ∧ ∃ source sink : Fin a, ∃ _ : Fin b,
    ∃ left : Fin (n+4)→Fin a, ∃ right : Fin (n+4)→Fin b,
    ∀ f : Fin (n+4)→ℂ,
    (∀ i,(∑ j,if j.val=0 then (if source=i then f j else 0)-(if sink=i then f j else 0)
        else if left j=i then f j else 0)=0) →
    (∀ i,(∑ j,if j.val≠0 ∧ right j=i then f j else 0)=0) →
    ∀ i j : Fin (n+4),(j.val=i.val+1 ∨ (i.val+1=(n+4) ∧ j.val=0)) →
       f i=0 → f j=0 → f=0) := by
  classical
  rintro ⟨a,b,size,source,sink,wit,left,right,detect⟩
  let k := n-3
  let old : Fin 3 ⊕ Fin k ≃ Fin n := finSumFinEquiv.trans (finCongr (by dsimp [k];omega))
  let added : Fin 7 ⊕ Fin k ≃ Fin (n+4) := finSumFinEquiv.trans (finCongr (by dsimp [k];omega))
  let va : (Fin a ⊕ Fin 2) ≃ Fin (a+2) := finSumFinEquiv
  let vb : (Fin b ⊕ Fin 2) ≃ Fin (b+2) := finSumFinEquiv
  let i₀ := old (.inl 0)
  let i₁ := old (.inl 1)
  let i₂ := old (.inl 2)
  let oldtail (z : Fin k) := old (.inr z)
  let lhead : Fin 7 → Fin a ⊕ Fin 2 :=
    ![.inl (left i₀),.inl (left i₁),.inl (left i₂),.inr 0,.inr 1,.inr 0,.inr 1]
  let rhead : Fin 7 → Fin b ⊕ Fin 2 :=
    ![.inl (right i₀),.inr 0,.inr 1,.inr 0,.inr 1,.inl (right i₁),.inl (right i₂)]
  let ltail (z : Fin k) : Fin a ⊕ Fin 2 := .inl (left (oldtail z))
  let rtail (z : Fin k) : Fin b ⊕ Fin 2 := .inl (right (oldtail z))
  let left' (e : Fin (n+4)) := va ((added.symm e).elim lhead ltail)
  let right' (e : Fin (n+4)) := vb ((added.symm e).elim rhead rtail)
  refine ⟨a+2,b+2,by omega,va (.inl source),va (.inl sink),vb (.inl wit),left',right',?_⟩
  intro F leftZero rightZero
  let x (j : Fin 7) := F (added (.inl j))
  let y (j : Fin k) := F (added (.inr j))
  have total (φ : Fin (n+4)→ℂ) : (∑ j,φ j)=
      (∑ i : Fin 7,φ (added (.inl i)))+∑ z : Fin k,φ (added (.inr z)) := by
    rw [← added.sum_comp φ,Fintype.sum_sum_type]
  have atPrefix (i : Fin 7) : (added (.inl i)).val=i.val := rfl
  have away (z : Fin k) : (added (.inr z)).val≠0 := by change 7+z.val≠0; omega
  have leftSum (v : Fin a ⊕ Fin 2) :
      (∑ j : Fin 7,if j.val=0 then
          (if (.inl source : Fin a ⊕ Fin 2)=v then x j else 0)-(if (.inl sink : Fin a ⊕ Fin 2)=v then x j else 0)
        else if lhead j=v then x j else 0)+
      (∑ j : Fin k,if ltail j=v then y j else 0)=0 := by
    have h := leftZero (va v)
    rw [total] at h
    simpa only [left',Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,atPrefix,if_neg (away _),
      same_ite va,x,y] using h
  have rightSum (v : Fin b ⊕ Fin 2) :
      (∑ j : Fin 7,if j.val≠0 then (if rhead j=v then x j else 0) else 0)+
      (∑ j : Fin k,if rtail j=v then y j else 0)=0 := by
    have h := rightZero (vb v)
    rw [total] at h
    simpa only [right',Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,atPrefix,ite_and,
      if_pos (away _),same_ite vb,x,y] using h
  have rr₀ : x 1+x 3=0 := by simpa [chord_sum_seven,rhead,rtail] using rightSum (.inr 0)
  have rr₁ : x 2+x 4=0 := by simpa [chord_sum_seven,rhead,rtail] using rightSum (.inr 1)
  have ll₀ : x 3+x 5=0 := by simpa [chord_sum_seven,lhead,ltail] using leftSum (.inr 0)
  have ll₁ : x 4+x 6=0 := by simpa [chord_sum_seven,lhead,ltail] using leftSum (.inr 1)
  have tie₀ : x 1=x 5 := by linear_combination rr₀-ll₀
  have tie₁ : x 2=x 6 := by linear_combination rr₁-ll₁
  let shift (j : Fin n) : Fin (n+4) := ⟨if j.val=0 then 0 else 4+j.val,by split <;> have := j.isLt <;> omega⟩
  let f (j : Fin n) := F (shift j)
  have first₀ : f i₀=x 0 := congrArg F (Fin.ext rfl)
  have first₁ : f i₁=x 5 := congrArg F (Fin.ext rfl)
  have first₂ : f i₂=x 6 := congrArg F (Fin.ext rfl)
  have tail (z : Fin k) : f (oldtail z)=y z := congrArg F (Fin.ext (by
    change (if 3+z.val=0 then 0 else 4+(3+z.val))=7+z.val
    split <;> omega))
  have oldPrefix (j : Fin 3) : (old (.inl j)).val=j.val := rfl
  have oldAway (z : Fin k) : (old (.inr z)).val≠0 := by change 3+z.val≠0; omega
  have oldLeft (v : Fin a) : (∑ j : Fin n,if j.val=0 then (if source=v then f j else 0)-
        (if sink=v then f j else 0) else if left j=v then f j else 0)=0 := by
    rw [← old.sum_comp (fun j : Fin n => if j.val=0 then (if source=v then f j else 0)-
        (if sink=v then f j else 0) else if left j=v then f j else 0),Fintype.sum_sum_type,Fin.sum_univ_three]
    have h := leftSum (.inl v)
    simp [chord_sum_seven,lhead,ltail,tie₀,tie₁] at h
    simp only [oldPrefix,if_neg (oldAway _)]
    change
      ((if source=v then f i₀ else 0)-(if sink=v then f i₀ else 0)+(if left i₁=v then f i₁ else 0)+
       (if left i₂=v then f i₂ else 0))+(∑ z : Fin k,if left (oldtail z)=v then f (oldtail z) else 0)=0
    simpa only [first₀,first₁,first₂,tail,add_assoc] using h
  have oldRight (v : Fin b) : (∑ j : Fin n,if j.val≠0 ∧ right j=v then f j else 0)=0 := by
    rw [← old.sum_comp (fun j : Fin n => if j.val≠0 ∧ right j=v then f j else 0),Fintype.sum_sum_type,
      Fin.sum_univ_three]
    have h := rightSum (.inl v)
    simp [chord_sum_seven,rhead,rtail] at h
    simp only [oldPrefix,ite_and,if_pos (oldAway _)]
    change (0+(if right i₁=v then f i₁ else 0)+(if right i₂=v then f i₂ else 0))+
      (∑ z : Fin k,if right (oldtail z)=v then f (oldtail z) else 0)=0
    simpa only [first₁,first₂,tail,zero_add] using h
  let project (e : Fin (n+4)) : Fin n :=
    ⟨if e.val=0 then 0 else if e.val<5 then (e.val-1)%2+1 else e.val-4,by
      split_ifs <;> have := e.isLt <;> omega⟩
  have early (s : Fin 5) :
      F (added (.inl ⟨s.val,by have := s.isLt; omega⟩))=0 ↔
      f (project (added (.inl ⟨s.val,by have := s.isLt; omega⟩)))=0 := by
    fin_cases s
    · change x 0=0 ↔ f i₀=0
      rw [first₀]
    · change x 1=0 ↔ f i₁=0
      rw [first₁,tie₀]
    · change x 2=0 ↔ f i₂=0
      rw [first₂,tie₁]
    · have eq : project (added (.inl (3 : Fin 7)))=i₁ := by
        apply Fin.ext
        change (if (3:ℕ)=0 then 0 else if 3<5 then (3-1)%2+1 else 3-4)=1
        decide
      change x 3=0 ↔ f (project (added (.inl (3:Fin 7))))=0
      rw [eq,first₁,eq_neg_of_add_eq_zero_left ll₀,neg_eq_zero]
    · have eq : project (added (.inl (4 : Fin 7)))=i₂ := by
        apply Fin.ext
        change (if (4:ℕ)=0 then 0 else if 4<5 then (4-1)%2+1 else 4-4)=2
        decide
      change x 4=0 ↔ f (project (added (.inl (4:Fin 7))))=0
      rw [eq,first₂,eq_neg_of_add_eq_zero_left ll₁,neg_eq_zero]
  have zeroes (i : Fin (n+4)) : F i=0 ↔ f (project i)=0 := by
    by_cases sm : i.val<5
    · let s : Fin 5 := ⟨i.val,sm⟩
      have eq : added (.inl (⟨s.val,by have := s.isLt;omega⟩ : Fin 7))=i := Fin.ext rfl
      simpa only [eq] using early s
    · have eq : shift (project i)=i := by
        apply Fin.ext
        change (if (if i.val=0 then 0 else if i.val<5 then (i.val-1)%2+1 else i.val-4)=0
          then 0 else 4+(if i.val=0 then 0 else if i.val<5 then (i.val-1)%2+1 else i.val-4))=i.val
        split_ifs <;> omega
      change F i=0 ↔ F (shift (project i))=0
      rw [eq]
  intro i j adj zi zj
  have edge :
      ((project j).val=(project i).val+1 ∨ ((project i).val+1=n ∧ (project j).val=0)) ∨
      ((project i).val=(project j).val+1 ∨ ((project j).val+1=n ∧ (project i).val=0)) := by
    dsimp only [project]
    split_ifs <;> omega
  have orig : f=0 := by
    rcases edge with h|h
    · exact detect f oldLeft oldRight _ _ h ((zeroes i).mp zi) ((zeroes j).mp zj)
    · exact detect f oldLeft oldRight _ _ h ((zeroes j).mp zj) ((zeroes i).mp zi)
  funext e
  exact (zeroes e).mpr (congrFun orig (project e))

end CriticalSquareFlows

namespace CriticalSquareFlows

/-- Signed-chord markings exist at every size at least four. -/
theorem all_chords (n : ℕ) (hn : 4≤n) : (∃ a b : ℕ, a+b+1=n ∧ ∃ source sink : Fin a, ∃ _ : Fin b,
    ∃ left : Fin n→Fin a, ∃ right : Fin n→Fin b,
    ∀ f : Fin n→ℂ,
    (∀ i,(∑ j,if j.val=0 then (if source=i then f j else 0)-(if sink=i then f j else 0)
        else if left j=i then f j else 0)=0) →
    (∀ i,(∑ j,if j.val≠0 ∧ right j=i then f j else 0)=0) →
    ∀ i j : Fin n,(j.val=i.val+1 ∨ (i.val+1=n ∧ j.val=0)) →
       f i=0 → f j=0 → f=0) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n<8
    · obtain rfl | rfl | rfl | rfl : n=4 ∨ n=5 ∨ n=6 ∨ n=7 := by omega
      · exact chord_four
      · exact chord_five
      · exact chord_six
      · exact chord_seven
    · obtain ⟨j,rfl⟩ : ∃ j,n=j+4 := ⟨n-4,by omega⟩
      exact chord_subdivide (by omega : 3≤j) (ih j (by omega) (by omega))

end CriticalSquareFlows

namespace CriticalSquareFlows

private theorem split_chord_value {n : ℕ} (origin : Fin n) (atZero : origin.val=0)
    (u v : Fin n→ℂ) :
    (∑ j,if j.val=0 then u j else v j)=u origin+(∑ j,if j.val≠0 then v j else 0) := by
  classical
  have split (j : Fin n) : (if j.val=0 then u j else v j)=
      (if j=origin then u origin else 0)+(if j.val≠0 then v j else 0) := by
    by_cases h : j=origin
    · subst j; simp [atZero]
    · have nz : j.val≠0 := fun e => h (Fin.ext (e.trans atZero.symm))
      simp [h,nz]
  simp only [split,Finset.sum_add_distrib]
  simp

private theorem labeled_chord_values {n : ℕ} (origin : Fin n) (atZero : origin.val=0)
    {V : Type*} [DecidableEq V] (special v : V) (side : Fin n→V) (f : Fin n→ℂ) :
    (∑ j,if (if j.val=0 then special else side j)=v then f j else 0)=
      (if special=v then f origin else 0)+(∑ j,if j.val≠0 ∧ side j=v then f j else 0) := by
  classical
  calc
    _ = ∑ j,if j.val=0 then (if special=v then f j else 0) else (if side j=v then f j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j.val=0 <;> simp [h]
    _ = _ := by
      rw [split_chord_value origin atZero]
      simp only [ite_and]

/-- Turn a signed auxiliary chord into left and right labels for the cyclic
profiles. The three special right terms cancel at the designated vertex.
Two neighboring ordinary coordinates, or the last and first at the seam,
then detect the entire profile. -/
theorem chord_profile_detector {k : ℕ} [NeZero k] (hk : 5≤k) (hc : (∃ a b : ℕ, a+b+1=(k-1) ∧ ∃ source sink : Fin a, ∃ _ : Fin b,
    ∃ left : Fin (k-1)→Fin a, ∃ right : Fin (k-1)→Fin b,
    ∀ f : Fin (k-1)→ℂ,
    (∀ i,(∑ j,if j.val=0 then (if source=i then f j else 0)-(if sink=i then f j else 0)
        else if left j=i then f j else 0)=0) →
    (∀ i,(∑ j,if j.val≠0 ∧ right j=i then f j else 0)=0) →
    ∀ i j : Fin (k-1),(j.val=i.val+1 ∨ (i.val+1=(k-1) ∧ j.val=0)) →
       f i=0 → f j=0 → f=0)) :
    ∃ a b : ℕ,a+b+1=k-1 ∧ ∃ center : Fin b,∃ L : ZMod k→Fin a,∃ R : ZMod k→Fin b,
      ∀ A C : ZMod k→ℂ,∀ D : ℂ,
        (∀ j,j≠1 → A j=C (j-1)) → A 1= -C 1 → C 0= -C (-1) → D= -C 1+C (-1) →
        (∀ i,(∑ j,if L j=i then A j else 0)=0) →
        (∀ i,(∑ j,if R j=i then C j else 0)+(if center=i then D else 0)=0) →
        ∀ s : ZMod k,A s=0 → C (s-2)=0 → C=0 := by
  classical
  let n := k-1
  let zero : Fin n := ⟨0,by dsimp [n]; omega⟩
  let last : Fin n := ⟨n-1,by dsimp [n]; omega⟩
  obtain ⟨a,b,size,source,sink,center,left,right,detect⟩ := hc
  let toZ : Fin k ≃ ZMod k :=
    { toFun := fun j => (j.val:ZMod k)
      invFun := fun j => ⟨j.val,j.val_lt⟩
      left_inv := fun j => Fin.ext (ZMod.val_natCast_of_lt j.isLt)
      right_inv := ZMod.natCast_zmod_val }
  let E : Fin 1 ⊕ Fin n ≃ ZMod k :=
    (finSumFinEquiv.trans (finCongr (by dsimp [n]; omega))).trans toZ
  let E' := E.trans (Equiv.addRight (1:ZMod k))
  let node (e : Fin n) := ((1+e.val:ℕ):ZMod k)
  have initial (s : Fin 1) : E (.inl s)=0 := by
    change (s.val:ZMod k)=0
    rw [show s.val=0 by have := s.isLt; omega,Nat.cast_zero]
  have atEdge (s : Fin n) : E (.inr s)=node s := rfl
  have moved (s : Fin 1 ⊕ Fin n) : E' s=E s+1 := rfl
  have origin : node zero=1 := by change ((1+0:ℕ):ZMod k)=1; simp
  have final : node last=(-1:ZMod k) := by
    have lim : (1+last.val)+1=k := by dsimp [last,n]; omega
    have z : node last+1=0 := by rw [show node last+1=(((1+last.val)+1:ℕ):ZMod k) by simp [node],lim,ZMod.natCast_self]
    exact eq_neg_of_add_eq_zero_left z
  let ltag : Fin 1 ⊕ Fin n → Fin a :=
    Sum.elim (fun _ => sink) (fun j => if j.val=0 then source else left j)
  let rtag : Fin 1 ⊕ Fin n → Fin b :=
    Sum.elim (fun _ => center) (fun j => if j.val=0 then center else right j)
  let L (j : ZMod k) := ltag (E'.symm j)
  let R (j : ZMod k) := rtag (E.symm j)
  refine ⟨a,b,size,center,L,R,?_⟩
  intro A C D ordinary sinkValue zeroValue correction leftRows rightRows
  let f (j : Fin n) := C (node j)
  have fzero : f zero=C 1 := by simp only [f,origin]
  have flast : f last=C (-1) := by simp only [f,final]
  have edgeVal (j : Fin n) : A (node j+1)=f j := by
    have nz : node j≠0 := by
      intro eq
      have bound : 1+j.val<k := by have := j.isLt; dsimp [n] at this; omega
      have vals := congrArg ZMod.val eq
      change (((1+j.val:ℕ):ZMod k)).val=(0:ZMod k).val at vals
      rw [ZMod.val_natCast_of_lt bound,ZMod.val_zero] at vals
      omega
    have ne : node j+1≠(1:ZMod k) := fun h => nz (by linear_combination h)
    simpa only [add_sub_cancel_right] using ordinary (node j+1) ne
  have oldLeft (v : Fin a) : (∑ j : Fin n,if j.val=0 then (if source=v then f j else 0)-
      (if sink=v then f j else 0) else if left j=v then f j else 0)=0 := by
    have row := leftRows v
    rw [← E'.sum_comp (fun j => if L j=v then A j else 0),Fintype.sum_sum_type] at row
    simp only [L,Equiv.symm_apply_apply,ltag,Sum.elim_inl,Sum.elim_inr] at row
    simp only [moved,initial,atEdge,zero_add,edgeVal,Finset.sum_const,Finset.card_univ,Fintype.card_fin,one_nsmul] at row
    rw [labeled_chord_values zero rfl source v left f,sinkValue,← fzero] at row
    rw [split_chord_value zero rfl]
    simp only [ite_and] at row
    by_cases sv : source=v <;> by_cases tv : sink=v <;> simp [sv,tv] at row ⊢ <;> linear_combination row
  have oldRight (v : Fin b) : (∑ j : Fin n,if j.val≠0 ∧ right j=v then f j else 0)=0 := by
    have row := rightRows v
    rw [← E.sum_comp (fun j => if R j=v then C j else 0),Fintype.sum_sum_type] at row
    simp only [R,Equiv.symm_apply_apply,rtag,Sum.elim_inl,Sum.elim_inr] at row
    simp only [initial,atEdge,Finset.sum_const,Finset.card_univ,Fintype.card_fin,one_nsmul] at row
    change (if center=v then C 0 else 0)+
      (∑ j : Fin n,if (if j.val=0 then center else right j)=v then f j else 0)+
      (if center=v then D else 0)=0 at row
    rw [labeled_chord_values zero rfl center v right f] at row
    by_cases cv : center=v
    · simp only [if_pos cv,fzero,zeroValue,correction] at row
      linear_combination row
    · simpa only [if_neg cv,zero_add,add_zero] using row
  intro s hA hC
  have lastFirst (atEnd : f last=0) (atStart : f zero=0) : f=0 :=
    detect f oldLeft oldRight last zero (.inr ⟨by dsimp [last,n]; omega,rfl⟩) atEnd atStart
  have killed : f=0 := by
    obtain ⟨u|e,rfl⟩ := E'.surjective s
    · rw [moved,initial,zero_add] at hA hC
      rw [sinkValue,neg_eq_zero] at hA
      exact lastFirst (by simpa only [flast,show (1:ZMod k)-2= -1 by ring] using hC)
        (fzero.trans hA)
    · rw [moved,atEdge] at hA hC
      rw [edgeVal] at hA
      by_cases iszero : e.val=0
      · have ez : e=zero := Fin.ext iszero
        subst e
        rw [origin,show (1:ZMod k)+1-2=0 by ring,zeroValue,neg_eq_zero] at hC
        exact lastFirst (flast.trans hC) hA
      · let prev : Fin n := ⟨e.val-1,by have := e.isLt; omega⟩
        have inc : e.val=prev.val+1 := by dsimp [prev]; omega
        have eq : node e+1-2=node prev := by
          change ((1+e.val:ℕ):ZMod k)+1-2=((1+prev.val:ℕ):ZMod k)
          rw [inc,Nat.cast_add,Nat.cast_add,Nat.cast_add,Nat.cast_one]
          ring
        rw [eq] at hC
        exact detect f oldLeft oldRight prev e (Or.inl inc) hC hA
  funext j
  obtain ⟨u|e,rfl⟩ := E.surjective j
  · rw [initial,zeroValue,← flast,congrFun killed last,Pi.zero_apply,neg_zero]
    rfl
  · exact congrFun killed e

end CriticalSquareFlows

namespace CriticalSquareFlows

/-- Moving the middle edge at index one into the duplicated column zero
changes precisely two column balances. Correcting the ordinary cyclic
first integral at zero then makes it identically zero. -/
theorem chord_balances {k : ℕ} [NeZero k] (hk : 5≤k)
    (A B C : ZMod k→ℂ)
    (first : A 0+C 0=0) (second : A 1+C 1=0) (duplicate : B 0+B 1=0)
    (ordinary : ∀ j,j≠0 → j≠1 → A j+B j+C j=0)
    (color : ∀ j,A j+B (j-1)+C (j-2)=0)
    (middle : (∑ j,B j)=B 1) (bottom : (∑ j,C j)+B 1=0) :
    (∀ j,j≠1 → A j=C (j-1)) ∧ A 1= -C 1 ∧ C 0= -C (-1) ∧ B 1= -C 1+C (-1) := by
  classical
  have : Fact (1<k) := ⟨by omega⟩
  let D := B 1
  let E (j : ZMod k) := if j=1 then D else 0
  let Z (j : ZMod k) := if j=0 then D else 0
  have cols (j : ZMod k) : A j+B j+C j=E j-Z j := by
    by_cases zero : j=0
    · subst j
      simp only [E,Z,D,zero_ne_one,if_false,if_true,zero_sub]
      linear_combination first+duplicate
    by_cases one : j=1
    · subst j
      simp only [E,Z,D,one_ne_zero,if_false,if_true,sub_zero]
      linear_combination second
    simpa only [E,Z,zero,one,if_false,sub_zero] using ordinary j zero one
  let K (j : ZMod k) := B j+C j+C (j-1)+Z j
  have step (j : ZMod k) : K (j+1)=K j := by
    have c := cols (j+1)
    have w := color (j+1)
    rw [add_sub_cancel_right,show j+1-2=j-1 by ring] at w
    have shift : E (j+1)=Z j := by
      change (if j+1=1 then D else 0)=(if j=0 then D else 0)
      simp
    rw [shift] at c
    dsimp only [K]
    rw [add_sub_cancel_right]
    linear_combination c-w
  have fixed (j : ZMod k) : K j=K 0 := by
    have nat (v : ℕ) : K (v:ZMod k)=K 0 := by
      induction v with
      | zero => simp
      | succ v ih => rw [Nat.cast_succ,step,ih]
    simpa only [ZMod.natCast_zmod_val] using nat j.val
  have sc : (∑ j : ZMod k,C (j-1))=∑ j,C j := (Equiv.subRight (1:ZMod k)).sum_comp C
  have sz : (∑ j,Z j)=D := by simp [Z]
  have sumK : (∑ j,K j)=0 := by
    simp only [K,Finset.sum_add_distrib,sc,sz,middle,D]
    linear_combination 2*bottom
  have kk : K 0=0 := by
    have z : (k:ℂ)*K 0=0 := by
      simpa only [fixed,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul] using sumK
    exact (mul_eq_zero.mp z).resolve_left (Nat.cast_ne_zero.mpr (NeZero.ne k))
  have allA (j : ZMod k) : A j=C (j-1)+E j := by
    have z := (fixed j).trans kk
    dsimp only [K] at z
    linear_combination cols j-z
  have regular (j : ZMod k) (one : j≠1) : A j=C (j-1) := by simpa only [E,if_neg one,add_zero] using allA j
  have left : A 1= -C 1 := eq_neg_of_add_eq_zero_left second
  have initial : C 0= -C (-1) := by
    have z := regular 0 zero_ne_one
    rw [zero_sub] at z
    linear_combination first-z
  refine ⟨regular,left,initial,?_⟩
  have z := allA 1
  simp only [sub_self,E,if_true,D] at z
  linear_combination left-initial-z

end CriticalSquareFlows

namespace CriticalSquareFlows

private theorem sum_of_supported {E A : Type*} [Fintype E] [Fintype A] [DecidableEq A]
    (put : E↪A) (f : A→ℂ) (outside : ∀ x,x∉Finset.univ.map put → f x=0) :
    (∑ x,f x)=∑ z,f (put z) := by
  calc
    _=∑ x ∈ Finset.univ.map put,f x := (Finset.sum_subset (Finset.subset_univ _)
      (fun x _ => outside x)).symm
    _=_ := Finset.sum_map ..

/-- Duplicate column zero and move the middle edge from column one to
the duplicate. Its new row has label two, preserving its old color. -/
theorem chord_graph_of_profile {k a b : ℕ} [NeZero k] (hk : 5≤k)
    (center : Fin b) (L : ZMod k→Fin a) (R : ZMod k→Fin b)
    (detect : ∀ A C : ZMod k→ℂ,∀ D : ℂ,
      (∀ j,j≠1 → A j=C (j-1)) → A 1= -C 1 → C 0= -C (-1) → D= -C 1+C (-1) →
      (∀ i,(∑ j,if L j=i then A j else 0)=0) →
      (∀ i,(∑ j,if R j=i then C j else 0)+(if center=i then D else 0)=0) →
      ∀ s : ZMod k,A s=0 → C (s-2)=0 → C=0) :
    let I := Fin a ⊕ (Unit ⊕ Fin b)
    let J := ZMod k ⊕ Unit
    ∃ edge : I×J→Bool, ∃ l : I→ZMod k, ∃ r : J→ZMod k,
    Fintype.card {ij // edge ij=true}=3*k ∧
    ∀ s : ZMod k,∀ w : I×J→ℂ, (∀ ij,¬edge ij=true → w ij=0) →
      (∀ i,(∑ j,w (i,j))=0) → (∀ j,(∑ i,w (i,j))=0) →
      (∀ c : ZMod k,(∑ ij,if l ij.1+r ij.2=c then w ij else 0)=0) →
      (∀ ij,l ij.1+r ij.2=s → w ij=0) → w=0 := by
  classical
  dsimp only
  have : Fact (1<k) := ⟨by omega⟩
  let low (j : ZMod k) : (Fin a ⊕ (Unit ⊕ Fin b)) := .inl (L j)
  let mid : (Fin a ⊕ (Unit ⊕ Fin b)) := .inr (.inl ())
  let high (j : ZMod k) : (Fin a ⊕ (Unit ⊕ Fin b)) := .inr (.inr (R j))
  let hub : (Fin a ⊕ (Unit ⊕ Fin b)) := .inr (.inr center)
  let dup : (ZMod k ⊕ Unit) := .inr ()
  let base (j : ZMod k) : (ZMod k ⊕ Unit) := .inl j
  let eA (j : ZMod k) : (Fin a ⊕ (Unit ⊕ Fin b))×(ZMod k ⊕ Unit) := (low j,base j)
  let eB (j : ZMod k) : (Fin a ⊕ (Unit ⊕ Fin b))×(ZMod k ⊕ Unit) := ((if j=1 then hub else mid),(if j=0 ∨ j=1 then dup else base j))
  let eC (j : ZMod k) : (Fin a ⊕ (Unit ⊕ Fin b))×(ZMod k ⊕ Unit) := (high j,base j)
  let put (p : Fin 3 × ZMod k) : (Fin a ⊕ (Unit ⊕ Fin b))×(ZMod k ⊕ Unit) := ![eA p.2,eB p.2,eC p.2] p.1
  let kind : (Fin a ⊕ (Unit ⊕ Fin b))→Fin 3 := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))
  let get (ij : (Fin a ⊕ (Unit ⊕ Fin b))×(ZMod k ⊕ Unit)) : Fin 3 × ZMod k :=
    ij.2.elim (fun j => (kind ij.1,j)) (fun _ => (1,if kind ij.1=1 then 0 else 1))
  have recover (p : Fin 3 × ZMod k) : get (put p)=p := by
    obtain ⟨u,j⟩ := p
    fin_cases u
    · rfl
    · by_cases one : j=1
      · subst j
        simp [put,eB,get,kind,dup,hub]
      · by_cases zero : j=0
        · subst j
          simp [put,eB,get,kind,dup,mid,zero_ne_one]
        · simp [put,eB,get,kind,base,mid,zero,one]
    · rfl
  let emb : (Fin 3 × ZMod k) ↪ (Fin a ⊕ (Unit ⊕ Fin b))×(ZMod k ⊕ Unit) := ⟨put,fun _ _ h => (recover _).symm.trans ((congrArg get h).trans (recover _))⟩
  let active := Finset.univ.map emb
  let edge (p : (Fin a ⊕ (Unit ⊕ Fin b))×(ZMod k ⊕ Unit)) := decide (p∈active)
  let l : (Fin a ⊕ (Unit ⊕ Fin b))→ZMod k := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))
  let r : (ZMod k ⊕ Unit)→ZMod k := Sum.elim id (fun _ => 0)
  refine ⟨edge,l,r,?_,?_⟩
  · have conv : {p // edge p=true} ≃ (↥active : Type) :=
      Equiv.subtypeEquivRight (fun _ => decide_eq_true_iff)
    rw [Fintype.card_congr conv,Fintype.card_coe,Finset.card_map,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,ZMod.card]
  · intro s w off rows cols colors black
    let A (j : ZMod k) := w (eA j)
    let B (j : ZMod k) := w (eB j)
    let C (j : ZMod k) := w (eC j)
    have test {U : Type} [DecidableEq U] (f : (Fin a ⊕ (Unit ⊕ Fin b))×(ZMod k ⊕ Unit)→U) (z : U) :
        (∑ ij,if f ij=z then w ij else 0)=
        (∑ j,if f (eA j)=z then A j else 0)+(∑ j,if f (eB j)=z then B j else 0)+
          (∑ j,if f (eC j)=z then C j else 0) := by
      let gated (ij : (Fin a ⊕ (Unit ⊕ Fin b))×(ZMod k ⊕ Unit)) : ℂ := if f ij=z then w ij else 0
      have h := sum_of_supported emb gated (fun ij hx => by
        have wz : w ij=0 := off ij (by simpa only [edge,decide_eq_true_eq] using hx)
        simp [gated,wz])
      change (∑ p,gated p)=∑ u : Fin 3 × ZMod k,gated (put u) at h
      conv_rhs at h => rw [Fintype.sum_prod_type]
      change (∑ p,gated p)=_
      rw [h]
      simp [gated,put,A,B,C,Fin.sum_univ_succ,add_assoc]
      rfl'
    have lr (i : (Fin a ⊕ (Unit ⊕ Fin b))) :
        (∑ j,if (eA j).1=i then A j else 0)+(∑ j,if (eB j).1=i then B j else 0)+
          (∑ j,if (eC j).1=i then C j else 0)=0 := by
      apply (test Prod.fst i).symm.trans
      rw [Fintype.sum_prod_type,Finset.sum_comm]
      simpa using rows i
    have cl (j : (ZMod k ⊕ Unit)) :
        (∑ q,if (eA q).2=j then A q else 0)+(∑ q,if (eB q).2=j then B q else 0)+
          (∑ q,if (eC q).2=j then C q else 0)=0 := by
      apply (test Prod.snd j).symm.trans
      rw [Fintype.sum_prod_type]
      simpa using cols j
    have baseB (j q : ZMod k) :
        (if (eB q).2=base j then B q else 0) =
        (if q=j then (if j=0 ∨ j=1 then 0 else B j) else 0) := by
      by_cases eq : q=j
      · subst q
        by_cases cut : j=0 ∨ j=1 <;> simp [eB,base,dup,cut]
      · by_cases cut : q=0 ∨ q=1 <;> simp [eB,base,dup,cut,eq]
    have columns (j : ZMod k) : A j+(if j=0 ∨ j=1 then 0 else B j)+C j=0 := by
      have h := cl (base j)
      simp only [baseB] at h
      simpa [eA,eC,base] using h
    have first : A 0+C 0=0 := by simpa using columns 0
    have second : A 1+C 1=0 := by simpa using columns 1
    have plain (j : ZMod k) (z : j≠0) (o : j≠1) : A j+B j+C j=0 := by simpa [z,o] using columns j
    have dupB (j : ZMod k) : (if (eB j).2=dup then B j else 0)=
        (if j=0 then B 0 else 0)+(if j=1 then B 1 else 0) := by
      by_cases zero : j=0
      · subst j
        simp [eB,dup,zero_ne_one]
      by_cases one : j=1
      · subst j
        simp [eB,dup,one_ne_zero]
      · simp [eB,dup,base,zero,one]
    have dupEq : B 0+B 1=0 := by
      have h := cl dup
      simp only [dupB,Finset.sum_add_distrib] at h
      simpa [eA,eC,base,dup] using h
    have leftZero (i : Fin a) : (∑ j,if L j=i then A j else 0)=0 := by
      have other (j : ZMod k) : (eB j).1≠(.inl i : (Fin a ⊕ (Unit ⊕ Fin b))) := by
        change (if j=1 then hub else mid)≠_
        split <;> exact Sum.inr_ne_inl
      have h := lr (Sum.inl i)
      simpa [eA,eC,low,high,other] using h
    have central (j : ZMod k) : (if (eB j).1=mid then B j else 0)=B j-(if j=1 then B 1 else 0) := by
      by_cases one : j=1
      · subst j
        simp [eB,hub,mid]
      · simp [eB,one]
    have midSum : (∑ j,B j)=B 1 := by
      have h := lr mid
      simp only [central,Finset.sum_sub_distrib] at h
      simpa [eA,eC,low,high,mid,sub_eq_zero] using h
    have midRight (j : ZMod k) (i : Fin b) :
        (if (eB j).1=(.inr (.inr i) : (Fin a ⊕ (Unit ⊕ Fin b))) then B j else 0)=
        (if j=1 then (if center=i then B 1 else 0) else 0) := by
      by_cases one : j=1
      · subst j
        by_cases own : center=i <;> simp [eB,hub,own]
      · simp [eB,mid,one]
    have rightZero (i : Fin b) : (∑ j,if R j=i then C j else 0)+(if center=i then B 1 else 0)=0 := by
      have h := lr (Sum.inr (Sum.inr i))
      simp only [midRight] at h
      simpa [eA,eC,low,high,add_comm] using h
    have bottom : (∑ j,C j)+B 1=0 := by
      have h : (∑ i : Fin b,((∑ j,if R j=i then C j else 0)+(if center=i then B 1 else 0)))=0 := by
        simp only [rightZero,Finset.sum_const_zero]
      rw [Finset.sum_add_distrib,Finset.sum_comm] at h
      simpa using h
    have aColor (j : ZMod k) : l (eA j).1+r (eA j).2=j := by change 0+j=j;rw [zero_add]
    have cColor (j : ZMod k) : l (eC j).1+r (eC j).2=2+j := rfl
    have bColor (j : ZMod k) : l (eB j).1+r (eB j).2=1+j := by
      by_cases one : j=1
      · subst j
        change l (if (1:ZMod k)=1 then hub else mid)+r (if (1:ZMod k)=0 ∨ 1=1 then dup else base 1)=1+1
        simp [l,r,hub,dup]
        ring
      · by_cases zero : j=0
        · subst j
          simp [eB,l,r,mid,dup,zero_ne_one]
        · simp [eB,l,r,mid,base,zero,one]
    have select (d c : ZMod k) (F : ZMod k→ℂ) : (∑ j,if d+j=c then F j else 0)=F (c-d) := by
      have iff (j : ZMod k) : d+j=c ↔ j=c-d := by rw [eq_sub_iff_add_eq,add_comm j d]
      simp [iff]
    have moment (c : ZMod k) : A c+B (c-1)+C (c-2)=0 := by
      have eq := (test (fun ij => l ij.1+r ij.2) c).symm.trans (colors c)
      simpa only [aColor,bColor,cColor,select,Finset.sum_ite_eq',Finset.mem_univ,if_true] using eq
    have atA : A s=0 := black (eA s) (aColor s)
    have atC : C (s-2)=0 := black (eC (s-2)) (by rw [cColor];ring)
    obtain ⟨equal,one,zero,diff⟩ := chord_balances hk A B C first second dupEq plain moment midSum bottom
    have cZero := detect A C (B 1) equal one zero diff leftZero rightZero s atA atC
    have aZero (j : ZMod k) : A j=0 := by
      by_cases same : j=1
      · simp only [same,one,cZero,Pi.zero_apply,neg_zero]
      · simp only [equal j same,cZero,Pi.zero_apply]
    have bZero (j : ZMod k) : B j=0 := by
      have d0 : B 1=0 := by simpa only [cZero,Pi.zero_apply,neg_zero,zero_add] using diff
      by_cases o : j=1
      · simpa only [o] using d0
      by_cases z : j=0
      · simpa only [z,d0,add_zero] using dupEq
      · simpa only [aZero,cZero,Pi.zero_apply,zero_add,add_zero] using plain j z o
    funext ij
    by_cases inRange : ij∈active
    · obtain ⟨⟨q,j⟩,_,rfl⟩ := Finset.mem_map.mp inRange
      fin_cases q
      · exact aZero j
      · exact bZero j
      · exact congrFun cZero j
    · exact off ij (by simpa only [edge,decide_eq_true_eq] using inRange)

end CriticalSquareFlows

namespace CriticalSquareFlows

/-- A detecting chord on k−1 slots yields a three-color-level physical
graph with k−1 row vertices, k+1 column vertices and exactly 3k edges. -/
theorem rectangular_chord_graph {k : ℕ} [NeZero k] (hk : 5≤k) (flow : (∃ a b : ℕ, a+b+1=(k-1) ∧ ∃ source sink : Fin a, ∃ _ : Fin b,
    ∃ left : Fin (k-1)→Fin a, ∃ right : Fin (k-1)→Fin b,
    ∀ f : Fin (k-1)→ℂ,
    (∀ i,(∑ j,if j.val=0 then (if source=i then f j else 0)-(if sink=i then f j else 0)
        else if left j=i then f j else 0)=0) →
    (∀ i,(∑ j,if j.val≠0 ∧ right j=i then f j else 0)=0) →
    ∀ i j : Fin (k-1),(j.val=i.val+1 ∨ (i.val+1=(k-1) ∧ j.val=0)) →
       f i=0 → f j=0 → f=0)) :
    ∃ a b : ℕ, a+b+1=k-1 ∧
      ∃ edge : ((Fin a ⊕ (Unit ⊕ Fin b)) × (ZMod k ⊕ Unit))→Bool,
      ∃ l : (Fin a ⊕ (Unit ⊕ Fin b))→ZMod k, ∃ r : (ZMod k ⊕ Unit)→ZMod k,
      Fintype.card {ij // edge ij=true}=3*k ∧
      ∀ s : ZMod k,∀ w : (Fin a ⊕ (Unit ⊕ Fin b)) × (ZMod k ⊕ Unit)→ℂ,
        (∀ ij,¬edge ij=true → w ij=0) → (∀ i,(∑ j,w (i,j))=0) → (∀ j,(∑ i,w (i,j))=0) →
        (∀ c : ZMod k,(∑ ij,if l ij.1+r ij.2=c then w ij else 0)=0) →
        (∀ ij,l ij.1+r ij.2=s → w ij=0) → w=0 := by
  obtain ⟨a,b,count,center,L,R,detect⟩ := chord_profile_detector hk flow
  exact ⟨a,b,count,chord_graph_of_profile hk center L R detect⟩

/-- For middle dimension b=a+2, k=(a+b)/2 selected rank-one
samples have independent normal spaces at the second normal level. -/
theorem chord_marked_batch {k r : ℕ} (hk : 5≤k) (level : r+1=(k-2)*k) (flow : (∃ a b : ℕ, a+b+1=(k-1) ∧ ∃ source sink : Fin a, ∃ _ : Fin b,
    ∃ left : Fin (k-1)→Fin a, ∃ right : Fin (k-1)→Fin b,
    ∀ f : Fin (k-1)→ℂ,
    (∀ i,(∑ j,if j.val=0 then (if source=i then f j else 0)-(if sink=i then f j else 0)
        else if left j=i then f j else 0)=0) →
    (∀ i,(∑ j,if j.val≠0 ∧ right j=i then f j else 0)=0) →
    ∀ i j : Fin (k-1),(j.val=i.val+1 ∨ (i.val+1=(k-1) ∧ j.val=0)) →
       f i=0 → f j=0 → f=0)) :
    ∃ first : Fin k ↪ Fin r, ∃ x : Fin r→Fin (k-1)→ℂ, ∃ y : Fin r→Fin (k+1)→ℂ,
    ∀ F : Fin k→Fin (k-1) × Fin (k+1)→ℂ,
      (∀ t s, (∑ ij,(x s ij.1*y s ij.2)*F t ij)=0) →
      (∀ t i, (∑ j,y (first t) j*F t (i,j))=0) →
      (∀ t j, (∑ i,x (first t) i*F t (i,j))=0) →
      (∑ t,F t)=0 → F=0 := by
  classical
  have : NeZero k := ⟨by omega⟩
  obtain ⟨a,b,vertices,edge,l,q,edges,fiber⟩ := rectangular_chord_graph hk flow
  let I := Fin a ⊕ (Unit ⊕ Fin b)
  let J := ZMod k ⊕ Unit
  let P := {ij : I×J // ¬edge ij=true} ⊕ ZMod k
  have ca : Fintype.card I=k-1 := by simp [I];omega
  have cb : Fintype.card J=k+1 := by simp [J,ZMod.card]
  have dim : (k-1)*(k+1)=r+2*k := by
    have e1 := congrArg (fun n : ℕ => n*k) (Nat.sub_add_cancel (by omega : 2≤k))
    have e2 := congrArg (fun n : ℕ => n*(k+1)) (Nat.sub_add_cancel (by omega : 1≤k))
    nlinarith only [e1,e2,level]
  have room := Nat.mul_le_mul_right k (show 3≤k-2 by omega)
  have edges' : Fintype.card {ij : I×J // edge ij=true}=3*k := edges
  have cp : Fintype.card P=r := by
    simp only [P,Fintype.card_sum,Fintype.card_subtype_compl,Fintype.card_prod,ca,cb,ZMod.card,edges',dim]
    omega
  let ea : I ≃ Fin (k-1) := Fintype.equivFinOfCardEq ca
  let eb : J ≃ Fin (k+1) := Fintype.equivFinOfCardEq cb
  let ep : P ≃ Fin r := Fintype.equivFinOfCardEq cp
  let first : ZMod k ↪ P := Function.Embedding.inr
  exact transport_marked ea eb ep (ZMod.finEquiv k).toEquiv first
    (CriticalLastSlice.TwoPlanes.batch_of_character_fibers (fun ij => edge ij=true) l q fiber)

/-- The complete finite chord family supplies the rectangular marked
normal-space witness uniformly in k. -/
theorem all_chord_marked_batches {k r : ℕ} (hk : 5≤k) (level : r+1=(k-2)*k) :
    ∃ first : Fin k ↪ Fin r, ∃ x : Fin r→Fin (k-1)→ℂ, ∃ y : Fin r→Fin (k+1)→ℂ,
    ∀ F : Fin k→Fin (k-1) × Fin (k+1)→ℂ,
      (∀ t s, (∑ ij,(x s ij.1*y s ij.2)*F t ij)=0) →
      (∀ t i, (∑ j,y (first t) j*F t (i,j))=0) →
      (∀ t j, (∑ i,x (first t) i*F t (i,j))=0) →
      (∑ t,F t)=0 → F=0 :=
  chord_marked_batch hk level (all_chords (k-1) (by omega))

end CriticalSquareFlows

namespace CriticalExtreme

private lemma line0 (H : Fin 4 × Fin 4 → ℂ)
    (p0 : H (0,0)=0)
    (p1 : H (1,1)=0)
    (p2 : H (2,2)=0)
    (p3 : H (1,0) + H (1,2) + H (2,0) + H (2,2) + H (3,0) + H (3,2)=0)
    (p4 : H (1,1) + H (1,2) + H (3,1) + H (3,2)=0)
    (p5 : H (0,2) + H (0,3) + H (2,2) + H (2,3)=0)
    (p6 : H (0,0) + H (0,1) + H (0,2) + H (0,3) + H (1,0) + H (1,1) + H (1,2) + H (1,3)=0)
    (p7 : H (3,3)=0)
    (p8 : H (0,0) + H (0,2) + H (0,3) + H (3,0) + H (3,2) + H (3,3)=0)
    (l1 : H (1,0)=0)
    (l2 : H (2,0)=0)
    (l3 : H (3,0)=0)
    (c1 : H (0,1)=0)
    (c2 : H (0,2)=0)
    (c3 : H (0,3)=0) :
    ∀ i j : Fin 4, H (i,j)=(![![0,0,0,0],![0,0,0,0],![0,1,0,0],![0,0,0,0]] i j : ℂ)*H (2,1) := by
  intro i j
  fin_cases i <;> fin_cases j
  · change H (0,0)=(0 : ℂ)*H (2,1)
    linear_combination p0
  · change H (0,1)=(0 : ℂ)*H (2,1)
    linear_combination c1
  · change H (0,2)=(0 : ℂ)*H (2,1)
    linear_combination c2
  · change H (0,3)=(0 : ℂ)*H (2,1)
    linear_combination c3
  · change H (1,0)=(0 : ℂ)*H (2,1)
    linear_combination l1
  · change H (1,1)=(0 : ℂ)*H (2,1)
    linear_combination p1
  · change H (1,2)=(0 : ℂ)*H (2,1)
    linear_combination p0 - p2 + p3 + p7 - p8 - l1 - l2 + c2 + c3
  · change H (1,3)=(0 : ℂ)*H (2,1)
    linear_combination -2*p0 - p1 + p2 - p3 + p6 - p7 + p8 + l2 - c1 - 2*c2 - 2*c3
  · change H (2,0)=(0 : ℂ)*H (2,1)
    linear_combination l2
  · change H (2,1)=(1 : ℂ)*H (2,1)
    ring
  · change H (2,2)=(0 : ℂ)*H (2,1)
    linear_combination p2
  · change H (2,3)=(0 : ℂ)*H (2,1)
    linear_combination -p2 + p5 - c2 - c3
  · change H (3,0)=(0 : ℂ)*H (2,1)
    linear_combination l3
  · change H (3,1)=(0 : ℂ)*H (2,1)
    linear_combination -p1 + p2 - p3 + p4 + l1 + l2 + l3
  · change H (3,2)=(0 : ℂ)*H (2,1)
    linear_combination -p0 - p7 + p8 - l3 - c2 - c3
  · change H (3,3)=(0 : ℂ)*H (2,1)
    linear_combination p7

private lemma line1 (H : Fin 4 × Fin 4 → ℂ)
    (p0 : H (0,0)=0)
    (p1 : H (1,1)=0)
    (p2 : H (2,2)=0)
    (p3 : H (1,0) + H (1,2) + H (2,0) + H (2,2) + H (3,0) + H (3,2)=0)
    (p4 : H (1,1) + H (1,2) + H (3,1) + H (3,2)=0)
    (p5 : H (0,2) + H (0,3) + H (2,2) + H (2,3)=0)
    (p6 : H (0,0) + H (0,1) + H (0,2) + H (0,3) + H (1,0) + H (1,1) + H (1,2) + H (1,3)=0)
    (p7 : H (3,3)=0)
    (p8 : H (0,0) + H (0,2) + H (0,3) + H (3,0) + H (3,2) + H (3,3)=0)
    (l0 : H (0,1)=0)
    (l2 : H (2,1)=0)
    (l3 : H (3,1)=0)
    (c0 : H (1,0)=0)
    (c2 : H (1,2)=0)
    (c3 : H (1,3)=0) :
    ∀ i j : Fin 4, H (i,j)=(![![0,0,-1,1],![0,0,0,0],![0,0,0,0],![0,0,0,0]] i j : ℂ)*H (0,3) := by
  intro i j
  fin_cases i <;> fin_cases j
  · change H (0,0)=(0 : ℂ)*H (0,3)
    linear_combination p0
  · change H (0,1)=(0 : ℂ)*H (0,3)
    linear_combination l0
  · change H (0,2)=(-1 : ℂ)*H (0,3)
    linear_combination -p0 - p1 + p6 - l0 - c0 - c2 - c3
  · change H (0,3)=(1 : ℂ)*H (0,3)
    ring
  · change H (1,0)=(0 : ℂ)*H (0,3)
    linear_combination c0
  · change H (1,1)=(0 : ℂ)*H (0,3)
    linear_combination p1
  · change H (1,2)=(0 : ℂ)*H (0,3)
    linear_combination c2
  · change H (1,3)=(0 : ℂ)*H (0,3)
    linear_combination c3
  · change H (2,0)=(0 : ℂ)*H (0,3)
    linear_combination -p1 - p2 + p3 + p6 + p7 - p8 - l0 - 2*c0 - 2*c2 - c3
  · change H (2,1)=(0 : ℂ)*H (0,3)
    linear_combination l2
  · change H (2,2)=(0 : ℂ)*H (0,3)
    linear_combination p2
  · change H (2,3)=(0 : ℂ)*H (0,3)
    linear_combination p0 + p1 - p2 + p5 - p6 + l0 + c0 + c2 + c3
  · change H (3,0)=(0 : ℂ)*H (0,3)
    linear_combination 2*p1 - p4 - p6 - p7 + p8 + l0 + l3 + c0 + 2*c2 + c3
  · change H (3,1)=(0 : ℂ)*H (0,3)
    linear_combination l3
  · change H (3,2)=(0 : ℂ)*H (0,3)
    linear_combination -p1 + p4 - l3 - c2
  · change H (3,3)=(0 : ℂ)*H (0,3)
    linear_combination p7

private lemma line2 (H : Fin 4 × Fin 4 → ℂ)
    (p0 : H (0,0)=0)
    (p1 : H (1,1)=0)
    (p2 : H (2,2)=0)
    (p3 : H (1,0) + H (1,2) + H (2,0) + H (2,2) + H (3,0) + H (3,2)=0)
    (p4 : H (1,1) + H (1,2) + H (3,1) + H (3,2)=0)
    (p5 : H (0,2) + H (0,3) + H (2,2) + H (2,3)=0)
    (p6 : H (0,0) + H (0,1) + H (0,2) + H (0,3) + H (1,0) + H (1,1) + H (1,2) + H (1,3)=0)
    (p7 : H (3,3)=0)
    (p8 : H (0,0) + H (0,2) + H (0,3) + H (3,0) + H (3,2) + H (3,3)=0)
    (l0 : H (0,2)=0)
    (l1 : H (1,2)=0)
    (l3 : H (3,2)=0)
    (c0 : H (2,0)=0)
    (c1 : H (2,1)=0)
    (c3 : H (2,3)=0) :
    ∀ i j : Fin 4, H (i,j)=(![![0,-1,0,0],![0,0,0,1],![0,0,0,0],![0,0,0,0]] i j : ℂ)*H (1,3) := by
  intro i j
  fin_cases i <;> fin_cases j
  · change H (0,0)=(0 : ℂ)*H (1,3)
    linear_combination p0
  · change H (0,1)=(-1 : ℂ)*H (1,3)
    linear_combination -2*p0 - p1 + 3*p2 - p3 - 2*p5 + p6 - p7 + p8 + c0 + 2*c3
  · change H (0,2)=(0 : ℂ)*H (1,3)
    linear_combination l0
  · change H (0,3)=(0 : ℂ)*H (1,3)
    linear_combination -p2 + p5 - l0 - c3
  · change H (1,0)=(0 : ℂ)*H (1,3)
    linear_combination p0 - 2*p2 + p3 + p5 + p7 - p8 - l1 - c0 - c3
  · change H (1,1)=(0 : ℂ)*H (1,3)
    linear_combination p1
  · change H (1,2)=(0 : ℂ)*H (1,3)
    linear_combination l1
  · change H (1,3)=(1 : ℂ)*H (1,3)
    ring
  · change H (2,0)=(0 : ℂ)*H (1,3)
    linear_combination c0
  · change H (2,1)=(0 : ℂ)*H (1,3)
    linear_combination c1
  · change H (2,2)=(0 : ℂ)*H (1,3)
    linear_combination p2
  · change H (2,3)=(0 : ℂ)*H (1,3)
    linear_combination c3
  · change H (3,0)=(0 : ℂ)*H (1,3)
    linear_combination -p0 + p2 - p5 - p7 + p8 - l3 + c3
  · change H (3,1)=(0 : ℂ)*H (1,3)
    linear_combination -p1 + p4 - l1 - l3
  · change H (3,2)=(0 : ℂ)*H (1,3)
    linear_combination l3
  · change H (3,3)=(0 : ℂ)*H (1,3)
    linear_combination p7

private lemma line3 (H : Fin 4 × Fin 4 → ℂ)
    (p0 : H (0,0)=0)
    (p1 : H (1,1)=0)
    (p2 : H (2,2)=0)
    (p3 : H (1,0) + H (1,2) + H (2,0) + H (2,2) + H (3,0) + H (3,2)=0)
    (p4 : H (1,1) + H (1,2) + H (3,1) + H (3,2)=0)
    (p5 : H (0,2) + H (0,3) + H (2,2) + H (2,3)=0)
    (p6 : H (0,0) + H (0,1) + H (0,2) + H (0,3) + H (1,0) + H (1,1) + H (1,2) + H (1,3)=0)
    (p7 : H (3,3)=0)
    (p8 : H (0,0) + H (0,2) + H (0,3) + H (3,0) + H (3,2) + H (3,3)=0)
    (l0 : H (0,0) + H (0,2)=0)
    (l1 : H (1,0) + H (1,2)=0)
    (l3 : H (3,0) + H (3,2)=0)
    (c0 : H (1,0) + H (2,0) + H (3,0)=0)
    (c1 : H (1,1) + H (2,1) + H (3,1)=0)
    (c3 : H (1,3) + H (2,3) + H (3,3)=0) :
    ∀ i j : Fin 4, H (i,j)=(![![0,0,0,0],![1,0,-1,0],![0,0,0,0],![-1,0,1,0]] i j : ℂ)*H (3,2) := by
  intro i j
  fin_cases i <;> fin_cases j
  · change H (0,0)=(0 : ℂ)*H (3,2)
    linear_combination p0
  · change H (0,1)=(0 : ℂ)*H (3,2)
    linear_combination p0 - p1 - p2 + p5 + p6 + 3*p7 - 2*p8 - l1 + 2*l3 - c3
  · change H (0,2)=(0 : ℂ)*H (3,2)
    linear_combination -p0 + l0
  · change H (0,3)=(0 : ℂ)*H (3,2)
    linear_combination -p7 + p8 - l0 - l3
  · change H (1,0)=(1 : ℂ)*H (3,2)
    linear_combination p2 - p3 + l1 + c0
  · change H (1,1)=(0 : ℂ)*H (3,2)
    linear_combination p1
  · change H (1,2)=(-1 : ℂ)*H (3,2)
    linear_combination -p2 + p3 - c0
  · change H (1,3)=(0 : ℂ)*H (3,2)
    linear_combination -p0 + p2 - p5 - 2*p7 + p8 - l3 + c3
  · change H (2,0)=(0 : ℂ)*H (3,2)
    linear_combination -p2 + p3 - l1 - l3
  · change H (2,1)=(0 : ℂ)*H (3,2)
    linear_combination -p2 + p3 - p4 - c0 + c1
  · change H (2,2)=(0 : ℂ)*H (3,2)
    linear_combination p2
  · change H (2,3)=(0 : ℂ)*H (3,2)
    linear_combination p0 - p2 + p5 + p7 - p8 + l3
  · change H (3,0)=(-1 : ℂ)*H (3,2)
    linear_combination l3
  · change H (3,1)=(0 : ℂ)*H (3,2)
    linear_combination -p1 + p2 - p3 + p4 + c0
  · change H (3,2)=(1 : ℂ)*H (3,2)
    ring
  · change H (3,3)=(0 : ℂ)*H (3,2)
    linear_combination p7

private lemma line4 (H : Fin 4 × Fin 4 → ℂ)
    (p0 : H (0,0)=0)
    (p1 : H (1,1)=0)
    (p2 : H (2,2)=0)
    (p3 : H (1,0) + H (1,2) + H (2,0) + H (2,2) + H (3,0) + H (3,2)=0)
    (p4 : H (1,1) + H (1,2) + H (3,1) + H (3,2)=0)
    (p5 : H (0,2) + H (0,3) + H (2,2) + H (2,3)=0)
    (p6 : H (0,0) + H (0,1) + H (0,2) + H (0,3) + H (1,0) + H (1,1) + H (1,2) + H (1,3)=0)
    (p7 : H (3,3)=0)
    (p8 : H (0,0) + H (0,2) + H (0,3) + H (3,0) + H (3,2) + H (3,3)=0)
    (l0 : H (0,1) + H (0,2)=0)
    (l2 : H (2,1) + H (2,2)=0)
    (l3 : H (3,1) + H (3,2)=0)
    (c0 : H (1,0) + H (3,0)=0)
    (c1 : H (1,1) + H (3,1)=0)
    (c3 : H (1,3) + H (3,3)=0) :
    ∀ i j : Fin 4, H (i,j)=(![![0,2,-2,1],![-1,0,0,0],![0,0,0,1],![1,0,0,0]] i j : ℂ)*H (3,0) := by
  intro i j
  fin_cases i <;> fin_cases j
  · change H (0,0)=(0 : ℂ)*H (3,0)
    linear_combination p0
  · change H (0,1)=(2 : ℂ)*H (3,0)
    linear_combination p1 - p4 + p6 + 2*p7 - p8 + 2*l3 - c0 - c1 - c3
  · change H (0,2)=(-2 : ℂ)*H (3,0)
    linear_combination -p1 + p4 - p6 - 2*p7 + p8 + l0 - 2*l3 + c0 + c1 + c3
  · change H (0,3)=(1 : ℂ)*H (3,0)
    linear_combination -p0 - p4 + p6 + p7 - l0 + l3 - c0 - c3
  · change H (1,0)=(-1 : ℂ)*H (3,0)
    linear_combination c0
  · change H (1,1)=(0 : ℂ)*H (3,0)
    linear_combination p1
  · change H (1,2)=(0 : ℂ)*H (3,0)
    linear_combination -p1 + p4 - l3
  · change H (1,3)=(0 : ℂ)*H (3,0)
    linear_combination -p7 + c3
  · change H (2,0)=(0 : ℂ)*H (3,0)
    linear_combination -p2 + p3 - p4 - c0 + c1
  · change H (2,1)=(0 : ℂ)*H (3,0)
    linear_combination -p2 + l2
  · change H (2,2)=(0 : ℂ)*H (3,0)
    linear_combination p2
  · change H (2,3)=(1 : ℂ)*H (3,0)
    linear_combination p0 + p1 - p2 + p5 + p7 - p8 + l3 - c1
  · change H (3,0)=(1 : ℂ)*H (3,0)
    ring
  · change H (3,1)=(0 : ℂ)*H (3,0)
    linear_combination -p1 + c1
  · change H (3,2)=(0 : ℂ)*H (3,0)
    linear_combination p1 + l3 - c1
  · change H (3,3)=(0 : ℂ)*H (3,0)
    linear_combination p7

private lemma line5 (H : Fin 4 × Fin 4 → ℂ)
    (p0 : H (0,0)=0)
    (p1 : H (1,1)=0)
    (p2 : H (2,2)=0)
    (p3 : H (1,0) + H (1,2) + H (2,0) + H (2,2) + H (3,0) + H (3,2)=0)
    (p4 : H (1,1) + H (1,2) + H (3,1) + H (3,2)=0)
    (p5 : H (0,2) + H (0,3) + H (2,2) + H (2,3)=0)
    (p6 : H (0,0) + H (0,1) + H (0,2) + H (0,3) + H (1,0) + H (1,1) + H (1,2) + H (1,3)=0)
    (p7 : H (3,3)=0)
    (p8 : H (0,0) + H (0,2) + H (0,3) + H (3,0) + H (3,2) + H (3,3)=0)
    (l1 : H (1,2) + H (1,3)=0)
    (l2 : H (2,2) + H (2,3)=0)
    (l3 : H (3,2) + H (3,3)=0)
    (c0 : H (0,0) + H (2,0)=0)
    (c1 : H (0,1) + H (2,1)=0)
    (c2 : H (0,2) + H (2,2)=0) :
    ∀ i j : Fin 4, H (i,j)=(![![0,-1,0,0],![1,0,-1,1],![0,1,0,0],![0,1,0,0]] i j : ℂ)*H (3,1) := by
  intro i j
  fin_cases i <;> fin_cases j
  · change H (0,0)=(0 : ℂ)*H (3,1)
    linear_combination p0
  · change H (0,1)=(-1 : ℂ)*H (3,1)
    linear_combination -3*p0 - 2*p1 + p2 - p3 + p4 - 2*p5 + p6 + p8 - l1 + 2*l2 - l3 + c0
  · change H (0,2)=(0 : ℂ)*H (3,1)
    linear_combination -p2 + c2
  · change H (0,3)=(0 : ℂ)*H (3,1)
    linear_combination p2 + p5 - l2 - c2
  · change H (1,0)=(1 : ℂ)*H (3,1)
    linear_combination 2*p0 + p1 - p2 + p3 - p4 + p5 - p8 - l2 + l3 - c0
  · change H (1,1)=(0 : ℂ)*H (3,1)
    linear_combination p1
  · change H (1,2)=(-1 : ℂ)*H (3,1)
    linear_combination -p1 + p4 + p7 - l3
  · change H (1,3)=(1 : ℂ)*H (3,1)
    linear_combination p1 - p4 - p7 + l1 + l3
  · change H (2,0)=(0 : ℂ)*H (3,1)
    linear_combination -p0 + c0
  · change H (2,1)=(1 : ℂ)*H (3,1)
    linear_combination 3*p0 + 2*p1 - p2 + p3 - p4 + 2*p5 - p6 - p8 + l1 - 2*l2 + l3 - c0 + c1
  · change H (2,2)=(0 : ℂ)*H (3,1)
    linear_combination p2
  · change H (2,3)=(0 : ℂ)*H (3,1)
    linear_combination -p2 + l2
  · change H (3,0)=(0 : ℂ)*H (3,1)
    linear_combination -p0 - p5 + p8 + l2 - l3
  · change H (3,1)=(1 : ℂ)*H (3,1)
    ring
  · change H (3,2)=(0 : ℂ)*H (3,1)
    linear_combination -p7 + l3
  · change H (3,3)=(0 : ℂ)*H (3,1)
    linear_combination p7

private lemma line6 (H : Fin 4 × Fin 4 → ℂ)
    (p0 : H (0,0)=0)
    (p1 : H (1,1)=0)
    (p2 : H (2,2)=0)
    (p3 : H (1,0) + H (1,2) + H (2,0) + H (2,2) + H (3,0) + H (3,2)=0)
    (p4 : H (1,1) + H (1,2) + H (3,1) + H (3,2)=0)
    (p5 : H (0,2) + H (0,3) + H (2,2) + H (2,3)=0)
    (p6 : H (0,0) + H (0,1) + H (0,2) + H (0,3) + H (1,0) + H (1,1) + H (1,2) + H (1,3)=0)
    (p7 : H (3,3)=0)
    (p8 : H (0,0) + H (0,2) + H (0,3) + H (3,0) + H (3,2) + H (3,3)=0)
    (l0 : H (0,0) + H (0,1) + H (0,2) + H (0,3)=0)
    (l2 : H (2,0) + H (2,1) + H (2,2) + H (2,3)=0)
    (l3 : H (3,0) + H (3,1) + H (3,2) + H (3,3)=0)
    (c0 : H (0,0) + H (1,0)=0)
    (c1 : H (0,1) + H (1,1)=0)
    (c2 : H (0,2) + H (1,2)=0) :
    ∀ i j : Fin 4, H (i,j)=(![![0,0,1,-1],![0,0,-1,1],![1,-1,0,0],![-1,0,1,0]] i j : ℂ)*H (3,2) := by
  intro i j
  fin_cases i <;> fin_cases j
  · change H (0,0)=(0 : ℂ)*H (3,2)
    linear_combination p0
  · change H (0,1)=(0 : ℂ)*H (3,2)
    linear_combination -p1 + c1
  · change H (0,2)=(1 : ℂ)*H (3,2)
    linear_combination 2*p1 - p4 - p8 + l0 + l3 - c1 + c2
  · change H (0,3)=(-1 : ℂ)*H (3,2)
    linear_combination -p0 - p1 + p4 + p8 - l3 - c2
  · change H (1,0)=(0 : ℂ)*H (3,2)
    linear_combination -p0 + c0
  · change H (1,1)=(0 : ℂ)*H (3,2)
    linear_combination p1
  · change H (1,2)=(-1 : ℂ)*H (3,2)
    linear_combination -2*p1 + p4 + p8 - l0 - l3 + c1
  · change H (1,3)=(1 : ℂ)*H (3,2)
    linear_combination p0 + p1 - p4 + p6 - p8 + l3 - c0 - c1
  · change H (2,0)=(1 : ℂ)*H (3,2)
    linear_combination p0 + 3*p1 - p2 + p3 - p4 + p7 - 2*p8 + 2*l0 + l3 - c0 - 2*c1
  · change H (2,1)=(-1 : ℂ)*H (3,2)
    linear_combination -2*p0 - 2*p1 + p2 - p3 + p4 - p5 - p7 + 2*p8 - l0 + l2 - l3 + c0 + c1
  · change H (2,2)=(0 : ℂ)*H (3,2)
    linear_combination p2
  · change H (2,3)=(0 : ℂ)*H (3,2)
    linear_combination p0 - p1 - p2 + p5 - l0 + c1
  · change H (3,0)=(-1 : ℂ)*H (3,2)
    linear_combination -p1 - p7 + p8 - l0 + c1
  · change H (3,1)=(0 : ℂ)*H (3,2)
    linear_combination p1 - p8 + l0 + l3 - c1
  · change H (3,2)=(1 : ℂ)*H (3,2)
    ring
  · change H (3,3)=(0 : ℂ)*H (3,2)
    linear_combination p7

/-- Seven projectively distinct marks on a four-by-four core have independent
normal lines at nine integer sample pairs. -/
lemma four_square_marked :
    ∃ first : Fin 7 ↪ Fin 9, ∃ x : Fin 9 → Fin 4 → ℂ, ∃ y : Fin 9 → Fin 4 → ℂ,
    (∀ H : Fin 7 → Fin 4 × Fin 4 → ℂ,
      (∀ t s, (∑ ij : Fin 4 × Fin 4, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (first t) j*H t (i,j))=0) →
      (∀ t j, (∑ i, x (first t) i*H t (i,j))=0) → (∑ t,H t)=0 → H=0) ∧
    (∀ t, x (first t)≠0) ∧ (∀ i j, i≠j → ∀ c : ℂ, x (first i)≠c • x (first j)) := by
  let first : Fin 7 ↪ Fin 9 := Fin.castLEEmb (by decide)
  let X : Fin 9 → Fin 4 → ℕ := ![![1,0,0,0],![0,1,0,0],![0,0,1,0],![0,1,1,1],![0,1,0,1],![1,0,1,0],![1,1,0,0],![0,0,0,1],![1,0,0,1]]
  let Y : Fin 9 → Fin 4 → ℕ := ![![1,0,0,0],![0,1,0,0],![0,0,1,0],![1,0,1,0],![0,1,1,0],![0,0,1,1],![1,1,1,1],![0,0,0,1],![1,0,1,1]]
  let x (t : Fin 9) (i : Fin 4) := (X t i : ℂ)
  let y (t : Fin 9) (j : Fin 4) := (Y t j : ℂ)
  refine ⟨first,x,y,?_,?_,?_⟩
  · intro H outer row col total
    have p0 (t : Fin 7) : H t (0,0)=0 := by
      simpa [x,y,X,Y,Fintype.sum_prod_type,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using outer t 0
    have p1 (t : Fin 7) : H t (1,1)=0 := by
      simpa [x,y,X,Y,Fintype.sum_prod_type,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using outer t 1
    have p2 (t : Fin 7) : H t (2,2)=0 := by
      simpa [x,y,X,Y,Fintype.sum_prod_type,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using outer t 2
    have p3 (t : Fin 7) : H t (1,0) + H t (1,2) + H t (2,0) + H t (2,2) + H t (3,0) + H t (3,2)=0 := by
      simpa [x,y,X,Y,Fintype.sum_prod_type,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using outer t 3
    have p4 (t : Fin 7) : H t (1,1) + H t (1,2) + H t (3,1) + H t (3,2)=0 := by
      simpa [x,y,X,Y,Fintype.sum_prod_type,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using outer t 4
    have p5 (t : Fin 7) : H t (0,2) + H t (0,3) + H t (2,2) + H t (2,3)=0 := by
      simpa [x,y,X,Y,Fintype.sum_prod_type,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using outer t 5
    have p6 (t : Fin 7) : H t (0,0) + H t (0,1) + H t (0,2) + H t (0,3) + H t (1,0) + H t (1,1) + H t (1,2) + H t (1,3)=0 := by
      simpa [x,y,X,Y,Fintype.sum_prod_type,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using outer t 6
    have p7 (t : Fin 7) : H t (3,3)=0 := by
      simpa [x,y,X,Y,Fintype.sum_prod_type,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using outer t 7
    have p8 (t : Fin 7) : H t (0,0) + H t (0,2) + H t (0,3) + H t (3,0) + H t (3,2) + H t (3,3)=0 := by
      simpa [x,y,X,Y,Fintype.sum_prod_type,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using outer t 8
    have l1_0 : H 0 (1,0)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 0 1
    have l2_0 : H 0 (2,0)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 0 2
    have l3_0 : H 0 (3,0)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 0 3
    have c1_0 : H 0 (0,1)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 0 1
    have c2_0 : H 0 (0,2)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 0 2
    have c3_0 : H 0 (0,3)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 0 3
    have h0 := line0 (H 0) (p0 0) (p1 0) (p2 0) (p3 0) (p4 0) (p5 0) (p6 0) (p7 0) (p8 0) l1_0 l2_0 l3_0 c1_0 c2_0 c3_0
    have l0_1 : H 1 (0,1)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 1 0
    have l2_1 : H 1 (2,1)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 1 2
    have l3_1 : H 1 (3,1)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 1 3
    have c0_1 : H 1 (1,0)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 1 0
    have c2_1 : H 1 (1,2)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 1 2
    have c3_1 : H 1 (1,3)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 1 3
    have h1 := line1 (H 1) (p0 1) (p1 1) (p2 1) (p3 1) (p4 1) (p5 1) (p6 1) (p7 1) (p8 1) l0_1 l2_1 l3_1 c0_1 c2_1 c3_1
    have l0_2 : H 2 (0,2)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 2 0
    have l1_2 : H 2 (1,2)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 2 1
    have l3_2 : H 2 (3,2)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 2 3
    have c0_2 : H 2 (2,0)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 2 0
    have c1_2 : H 2 (2,1)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 2 1
    have c3_2 : H 2 (2,3)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 2 3
    have h2 := line2 (H 2) (p0 2) (p1 2) (p2 2) (p3 2) (p4 2) (p5 2) (p6 2) (p7 2) (p8 2) l0_2 l1_2 l3_2 c0_2 c1_2 c3_2
    have l0_3 : H 3 (0,0) + H 3 (0,2)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 3 0
    have l1_3 : H 3 (1,0) + H 3 (1,2)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 3 1
    have l3_3 : H 3 (3,0) + H 3 (3,2)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 3 3
    have c0_3 : H 3 (1,0) + H 3 (2,0) + H 3 (3,0)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 3 0
    have c1_3 : H 3 (1,1) + H 3 (2,1) + H 3 (3,1)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 3 1
    have c3_3 : H 3 (1,3) + H 3 (2,3) + H 3 (3,3)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 3 3
    have h3 := line3 (H 3) (p0 3) (p1 3) (p2 3) (p3 3) (p4 3) (p5 3) (p6 3) (p7 3) (p8 3) l0_3 l1_3 l3_3 c0_3 c1_3 c3_3
    have l0_4 : H 4 (0,1) + H 4 (0,2)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 4 0
    have l2_4 : H 4 (2,1) + H 4 (2,2)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 4 2
    have l3_4 : H 4 (3,1) + H 4 (3,2)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 4 3
    have c0_4 : H 4 (1,0) + H 4 (3,0)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 4 0
    have c1_4 : H 4 (1,1) + H 4 (3,1)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 4 1
    have c3_4 : H 4 (1,3) + H 4 (3,3)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 4 3
    have h4 := line4 (H 4) (p0 4) (p1 4) (p2 4) (p3 4) (p4 4) (p5 4) (p6 4) (p7 4) (p8 4) l0_4 l2_4 l3_4 c0_4 c1_4 c3_4
    have l1_5 : H 5 (1,2) + H 5 (1,3)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 5 1
    have l2_5 : H 5 (2,2) + H 5 (2,3)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 5 2
    have l3_5 : H 5 (3,2) + H 5 (3,3)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 5 3
    have c0_5 : H 5 (0,0) + H 5 (2,0)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 5 0
    have c1_5 : H 5 (0,1) + H 5 (2,1)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 5 1
    have c2_5 : H 5 (0,2) + H 5 (2,2)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 5 2
    have h5 := line5 (H 5) (p0 5) (p1 5) (p2 5) (p3 5) (p4 5) (p5 5) (p6 5) (p7 5) (p8 5) l1_5 l2_5 l3_5 c0_5 c1_5 c2_5
    have l0_6 : H 6 (0,0) + H 6 (0,1) + H 6 (0,2) + H 6 (0,3)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 6 0
    have l2_6 : H 6 (2,0) + H 6 (2,1) + H 6 (2,2) + H 6 (2,3)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 6 2
    have l3_6 : H 6 (3,0) + H 6 (3,1) + H 6 (3,2) + H 6 (3,3)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using row 6 3
    have c0_6 : H 6 (0,0) + H 6 (1,0)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 6 0
    have c1_6 : H 6 (0,1) + H 6 (1,1)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 6 1
    have c2_6 : H 6 (0,2) + H 6 (1,2)=0 := by
      simpa [x,y,X,Y,first,Fin.castLEEmb,Fin.sum_univ_four,Matrix.cons_val_three,add_assoc] using col 6 2
    have h6 := line6 (H 6) (p0 6) (p1 6) (p2 6) (p3 6) (p4 6) (p5 6) (p6 6) (p7 6) (p8 6) l0_6 l2_6 l3_6 c0_6 c1_6 c2_6
    let N : Fin 7 → Fin 4 → Fin 4 → ℂ := ![![![0,0,0,0],![0,0,0,0],![0,1,0,0],![0,0,0,0]],![![0,0,-1,1],![0,0,0,0],![0,0,0,0],![0,0,0,0]],![![0,-1,0,0],![0,0,0,1],![0,0,0,0],![0,0,0,0]],![![0,0,0,0],![1,0,-1,0],![0,0,0,0],![-1,0,1,0]],![![0,2,-2,1],![-1,0,0,0],![0,0,0,1],![1,0,0,0]],![![0,-1,0,0],![1,0,-1,1],![0,1,0,0],![0,1,0,0]],![![0,0,1,-1],![0,0,-1,1],![1,-1,0,0],![-1,0,1,0]]]
    let p : Fin 7 → Fin 4 × Fin 4 := ![(2,1),(0,3),(1,3),(3,2),(3,0),(3,1),(3,2)]
    let scalar (t : Fin 7) := H t (p t)
    have lineValue (t : Fin 7) (i j : Fin 4) : H t (i,j)=N t i j*scalar t := by
      fin_cases t
      · exact h0 i j
      · exact h1 i j
      · exact h2 i j
      · exact h3 i j
      · exact h4 i j
      · exact h5 i j
      · exact h6 i j
    have z1 : -scalar 2 + 2*scalar 4 - scalar 5=0 := by
      have hz := congrFun total (0,1)
      simp only [Finset.sum_apply,Pi.zero_apply,lineValue] at hz
      simpa [N,Fin.sum_univ_succ,Matrix.cons_val_three,sub_eq_add_neg,add_assoc] using hz
    have z2 : -scalar 1 - 2*scalar 4 + scalar 6=0 := by
      have hz := congrFun total (0,2)
      simp only [Finset.sum_apply,Pi.zero_apply,lineValue] at hz
      simpa [N,Fin.sum_univ_succ,Matrix.cons_val_three,sub_eq_add_neg,add_assoc] using hz
    have z3 : scalar 1 + scalar 4 - scalar 6=0 := by
      have hz := congrFun total (0,3)
      simp only [Finset.sum_apply,Pi.zero_apply,lineValue] at hz
      simpa [N,Fin.sum_univ_succ,Matrix.cons_val_three,sub_eq_add_neg,add_assoc] using hz
    have z4 : scalar 3 - scalar 4 + scalar 5=0 := by
      have hz := congrFun total (1,0)
      simp only [Finset.sum_apply,Pi.zero_apply,lineValue] at hz
      simpa [N,Fin.sum_univ_succ,Matrix.cons_val_three,sub_eq_add_neg,add_assoc] using hz
    have z6 : -scalar 3 - scalar 5 - scalar 6=0 := by
      have hz := congrFun total (1,2)
      simp only [Finset.sum_apply,Pi.zero_apply,lineValue] at hz
      simpa [N,Fin.sum_univ_succ,Matrix.cons_val_three,sub_eq_add_neg,add_assoc] using hz
    have z9 : scalar 0 + scalar 5 - scalar 6=0 := by
      have hz := congrFun total (2,1)
      simp only [Finset.sum_apply,Pi.zero_apply,lineValue] at hz
      simpa [N,Fin.sum_univ_succ,Matrix.cons_val_three,sub_eq_add_neg,add_assoc] using hz
    have z12 : -scalar 3 + scalar 4 - scalar 6=0 := by
      have hz := congrFun total (3,0)
      simp only [Finset.sum_apply,Pi.zero_apply,lineValue] at hz
      simpa [N,Fin.sum_univ_succ,Matrix.cons_val_three,sub_eq_add_neg,add_assoc] using hz
    have zero (t : Fin 7) : scalar t=0 := by
      fin_cases t
      · change scalar 0=0
        linear_combination -z4 + z9 - z12
      · change scalar 1=0
        linear_combination 2*z2 + 3*z3 - z4 - z6
      · change scalar 2=0
        linear_combination -z1 - 3*z2 - 3*z3 + z6 - z12
      · change scalar 3=0
        linear_combination -2*z2 - 2*z3 + z4 + z6 - z12
      · change scalar 4=0
        linear_combination -z2 - z3
      · change scalar 5=0
        linear_combination z2 + z3 - z6 + z12
      · change scalar 6=0
        linear_combination z2 + z3 - z4 - z6
    funext t ⟨i,j⟩
    change H t (i,j)=0
    rw [lineValue,zero,mul_zero]
  · have exists_one : ∀ t : Fin 7, ∃ i, X (first t) i=1 := by decide +kernel
    intro t hz
    obtain ⟨i,hi⟩ := exists_one t
    have z := congrFun hz i
    change (X (first t) i : ℂ)=0 at z
    rw [hi,Nat.cast_one] at z
    exact one_ne_zero z
  · have exists_one : ∀ t : Fin 7, ∃ i, X (first t) i=1 := by decide +kernel
    have binary : ∀ t : Fin 7, ∀ i, X (first t) i=0 ∨ X (first t) i=1 := by decide +kernel
    have separated : ∀ t u : Fin 7, t≠u → ∃ i, X (first t) i≠X (first u) i := by decide +kernel
    intro t u htu c eq
    obtain ⟨i,hi⟩ := exists_one t
    have en := congrFun eq i
    change (X (first t) i : ℂ)=c*(X (first u) i : ℂ) at en
    rw [hi,Nat.cast_one] at en
    obtain h|h := binary u i
    · rw [h,Nat.cast_zero,mul_zero] at en
      exact one_ne_zero en
    · rw [h,Nat.cast_one,mul_one] at en
      obtain ⟨j,hj⟩ := separated t u htu
      apply hj
      have z := congrFun eq j
      change (X (first t) j : ℂ)=c*(X (first u) j : ℂ) at z
      rw [← en,one_mul] at z
      exact_mod_cast z

end CriticalExtreme

namespace ThreePlaneTail

/-- The 25 points split into two coordinate blocks, with respectively one
and two relations. The block mark counts are 8 and 17. -/
theorem fourteen :
    ∃ x : Fin 25 → Fin 3 → ℂ, ∃ y : Fin 25 → Fin 14 → ℂ, ∃ z : Fin 25 → Fin 22 → ℂ,
    ∀ T : Fin 3 → Fin 14 → Fin 22 → ℂ, ∃ u : Fin 25 → Fin 3 → ℂ,
      ∃ v : Fin 25 → Fin 14 → ℂ, ∃ w : Fin 25 → Fin 22 → ℂ, ∀ i j k,
        T i j k = ∑ t,(u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  let rel : Fin 2 → ℕ := ![1,2]
  let marks : Fin 2 → ℕ := ![8,17]
  let g : Fin 3 → ℕ := ![4,4,3]
  apply CriticalThreeComponents.tangent_of_components (h:=3) (by decide) (by decide) (by decide)
    rel marks (by decide) (by decide) (by decide)
  intro c
  fin_cases c
  · exact ⟨g,![3,2,3],by decide,by decide,by decide⟩
  · exact ⟨g,![5,5,7],by decide,by decide,by decide⟩

end ThreePlaneTail

namespace CriticalSquareFlows

/-- Seven independent normal planes for the exceptional longer pair with
first side four. The first block has seven independent marked normal lines,
and the complementary block supplies a second line at each mark. -/
theorem four_by_ten :
    ∃ first : Fin 7 ↪ Fin 26, ∃ x : Fin 26 → Fin 4 → ℂ, ∃ y : Fin 26 → Fin 10 → ℂ,
    ∀ F : Fin 7 → Fin 4 × Fin 10 → ℂ,
      (∀ t s, ∑ ij : Fin 4 × Fin 10, (x s ij.1*y s ij.2)*F t ij=0) →
      (∀ t i, ∑ j,y (first t) j*F t (i,j)=0) →
      (∀ t j, ∑ i,x (first t) i*F t (i,j)=0) → (∑ t,F t)=0 → F=0 := by
  obtain ⟨first,x,y,independent,nz,separated⟩ := CriticalExtreme.four_square_marked
  apply CriticalLastSlice.TwoPlanes.Cross.split_marked (a:=4) (b:=4) (w:=6) (m:=7)
    (by decide) (by decide) (by decide) (by decide) first x y independent nz
  intro s t distinct member
  obtain ⟨c,eq⟩ := Submodule.mem_span_singleton.mp member
  exact separated s t distinct c eq.symm

/-- All three gaps up through two admit a full independent marked batch
at the two-normal level, simultaneously for all side lengths. -/
theorem near_markings {a b : ℕ} (ha : 4≤a) (order : a≤b) (close : b≤a+2) :
    let r := (a-1)*(b-1)-1
    let h := (a+b)/2
    ∃ mark : Fin h ↪ Fin r, ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
      ∀ F : Fin h → Fin a × Fin b → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin b,(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) →
        (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) → (∑ t,F t)=0 → F=0 := by
  let M (p q r m : ℕ) : Prop :=
    ∃ mark : Fin m ↪ Fin r, ∃ x : Fin r → Fin p → ℂ, ∃ y : Fin r → Fin q → ℂ,
      ∀ F : Fin m → Fin p × Fin q → ℂ,
        (∀ t s, ∑ ij : Fin p × Fin q,(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) →
        (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) → (∑ t,F t)=0 → F=0
  change M a b ((a-1)*(b-1)-1) ((a+b)/2)
  have pos : 0<(a-1)*(a-1) := Nat.mul_pos (by omega) (by omega)
  have sq := all_square_marking (r:=(a-1)*(a-1)-1) ha (by omega)
  rcases (show b=a ∨ b=a+1 ∨ b=a+2 by omega) with eq|eq|eq
  · subst b
    rw [show (a+a)/2=a by omega]
    exact sq
  · subst b
    exact near_square_of_square a (by omega) sq
  · subst b
    rw [show (a+(a+2))/2=a+1 by omega,show a+2-1=a+1 by omega]
    have positive := Nat.mul_pos (show 0<a-1 by omega) (show 0<a+1 by omega)
    have span : M (a+1-1) (a+2) ((a-1)*(a+1)-1) (a+1) :=
      all_chord_marked_batches (k:=a+1) (by omega) (by
        rw [show a+1-2=a-1 by omega]; omega)
    rwa [show a+1-1=a by omega] at span


/-- At every ordinary pair of first sides outside b=3a−2 with a≥5, the
full floor((a+b)/2) marks exist independently of the third dimension. -/
theorem ordinary_markings {a b : ℕ} (ha : 4≤a) (hab : a≤b)
    (exception : b+2=3*a → a=4) :
    let r := (a-1)*(b-1)-1
    let h := (a+b)/2
    ∃ mark : Fin h ↪ Fin r, ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
      ∀ F : Fin h → Fin a × Fin b → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin b,(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) →
        (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) → (∑ t,F t)=0 → F=0 := by
  by_cases near : b≤a+2
  · exact near_markings ha hab near
  by_cases ratio : b+2=3*a
  · obtain rfl : a=4 := exception ratio
    obtain rfl : b=10 := by omega
    exact four_by_ten
  exact CriticalLastSlice.TwoPlanes.Cross.half_batch (by omega) (by omega) (Or.inl ha) ratio

end CriticalSquareFlows

namespace CriticalTwoNormalReduction

open CriticalLastSlice.TwoPlanes

/-- The ordinary exception at aspect ratio b=3a−2 after the seven-plane
construction for (4,10). This asks for 2a−1 independent normal planes. -/
def H1 : Prop :=
  ∀ a : ℕ, 5≤a →
    let b := 3*a-2
    let r := (a-1)*(b-1)-1
    let h := (a+b)/2
    ∃ mark : Fin h ↪ Fin r, ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
      ∀ F : Fin h → Fin a × Fin b → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin b,(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) →
        (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) → (∑ t,F t)=0 → F=0

/-- In odd ambient dimension, two batches can share one marked point.
The obstruction is needed only below the rectangular tail, at gaps of
at least three, when the minimum number of relations gives too few ordinary batch slots. -/
def H2 : Prop :=
  ∀ a b : ℕ, 4≤a → a+3≤b → b<a*(2*a-1) → Odd (a+b) →
    let r := (a-1)*(b-1)-1
    let h := (a+b)/2
    (2*r ⌈/⌉ (a+b))*h<r →
    ∃ mark : (Fin h ⊕ Fin h ⊕ Unit) ↪ Fin r,
      ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
      ∀ F : (Fin h ⊕ Fin h ⊕ Unit) → Fin a × Fin b → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin b,(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) →
        (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) →
        (∑ i : Fin h,F (.inl i))+F (.inr (.inr ()))=0 →
        (∑ i : Fin h,F (.inr (.inl i)))+F (.inr (.inr ()))=0 → F=0

/-- Use the finite three-slice specimen, independent ordinary batches
and the remaining odd paired batches in the registered normal-space criterion. -/
theorem main : H1 → H2 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H1 := by
  intro exceptional paired a b c ha hab hbc region w r level
  change r+1=(a-1)*(b-1) at level
  by_cases three : a=3
  · subst a
    exact ThreePlaneTail.registered_three_iff_fourteen.mpr ThreePlaneTail.fourteen b c hab hbc region level
  have four : 4≤a := by omega
  obtain ⟨_,enough,budget⟩ := relation_budget a b c r ha hab level rfl
  apply (witness_iff_normals (a:=a) (b:=b) enough).mp
  by_cases long : a*(2*a-1)≤b
  · exact Cross.tangent_tail ha long level rfl
  have dim : r=(a-1)*(b-1)-1 := by omega
  apply spans_of_capacity_markings enough budget
  · intro fit
    refine ⟨(a+b)/2,fit,?_⟩
    rw [dim]
    by_cases missing : b+2=3*a ∧ 5≤a
    · have side : b=3*a-2 := by omega
      subst b
      exact exceptional a missing.2
    · exact CriticalSquareFlows.ordinary_markings four hab (fun ratio => by omega)
  · intro overflow
    have odd : Odd (a+b) := by
      rcases capacity_cases budget with fit|⟨_,_,_,parity,_,_⟩
      · exact (not_lt_of_ge fit overflow).elim
      · exact ⟨(a+b)/2,parity⟩
    have minRows : (2*r ⌈/⌉ (a+b)) ≤ r-(c+1) := by
      apply (ceilDiv_le_iff_le_mul (by omega : 0<a+b)).mpr
      exact budget.trans_eq (Nat.mul_comm _ _)
    have deficit := lt_of_le_of_lt (Nat.mul_le_mul_right ((a+b)/2) minRows) overflow
    have gap : a+3≤b := by
      by_contra! near
      have consecutive : b=a+1 := by obtain ⟨j,hj⟩ := odd; omega
      subst b
      have fit := CriticalSquareFlows.consecutive_no_overflow a (by omega)
      dsimp only at fit
      rw [← dim] at fit
      omega
    have specimen := paired a b four gap (by omega) odd
    dsimp only at specimen
    rw [← dim] at specimen
    exact specimen deficit

end CriticalTwoNormalReduction

namespace CriticalExtreme

open MvPolynomial

/-- A left inverse at one point gives a polynomial sufficient for injectivity at other points. -/
private lemma rank_polynomial {I J V : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J (MvPolynomial V ℂ)) (p : V → ℂ) (hi : Function.Injective (M.map (eval p)).mulVec) :
    ∃ Q : MvPolynomial V ℂ, Q≠0 ∧ ∀ u : V → ℂ, eval u Q≠0 → Function.Injective (M.map (eval u)).mulVec := by
  classical
  let A := M.map (eval p)
  obtain ⟨L,hL⟩ := A.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  let B := LinearMap.toMatrix' L
  have left : B*A=1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul,Matrix.toLin'_one]
    change (Matrix.toLin' (LinearMap.toMatrix' L)).comp A.mulVecLin=LinearMap.id
    rw [Matrix.toLin'_toMatrix']
    exact hL
  let P := B.map (MvPolynomial.C : ℂ →+* MvPolynomial V ℂ)
  have spec (u : V → ℂ) : eval u (P*M).det = (B*M.map (eval u)).det := by
    have hP : P.map (eval u)=B := by ext; simp [P,Matrix.map_apply]
    rw [RingHom.map_det,RingHom.mapMatrix_apply,Matrix.map_mul,hP]
  have one : eval p (P*M).det=1 := (spec p).trans ((congrArg Matrix.det left).trans Matrix.det_one)
  refine ⟨(P*M).det,fun h => zero_ne_one (by simpa only [h,map_zero] using one),?_⟩
  intro u hu
  have nz : (B*M.map (eval u)).det≠0 := (spec u) ▸ hu
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr nz))
  intro x y he
  apply hinj
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,he]

/-- Independence of the old normal spaces holds off a polynomial
hypersurface in the shared factor coordinates. -/
private lemma old_polynomial {A B P Q : Type*} [Fintype A] [Fintype B] [Fintype P] [Fintype Q]
    (e : Q ↪ P) (one : ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0) :
    ∃ C : MvPolynomial (P × (A ⊕ B)) ℂ, C≠0 ∧ ∀ p, eval p C≠0 →
      ∀ H : Q → A×B → ℂ,
        (∀ t s, (∑ ij, (p (s,.inl ij.1)*p (s,.inr ij.2))*H t ij)=0) →
        (∀ t i, (∑ j, p (e t,.inr j)*H t (i,j))=0) →
        (∀ t j, (∑ i, p (e t,.inl i)*H t (i,j))=0) → (∑ t,H t)=0 → H=0 := by
  classical
  let V := P × (A ⊕ B)
  let Row := (Q × (P ⊕ (A ⊕ B))) ⊕ (A × B)
  let Col := Q × (A × B)
  let M : Matrix Row Col (MvPolynomial V ℂ) := fun row col => row.elim
    (fun te => if col.1=te.1 then te.2.elim
      (fun s => X (s,.inl col.2.1)*X (s,.inr col.2.2))
      (Sum.elim (fun i => if col.2.1=i then X (e te.1,.inr col.2.2) else 0)
        (fun j => if col.2.2=j then X (e te.1,.inl col.2.1) else 0)) else 0)
    (fun ij => if col.2=ij then 1 else 0)
  let D (x : P → A → ℂ) (y : P → B → ℂ) : Prop := ∀ H : Q → A×B → ℂ,
      (∀ t s, (∑ ij : A×B, (x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i, (∑ j, y (e t) j*H t (i,j))=0) → (∀ t j, (∑ i, x (e t) i*H t (i,j))=0) →
      (∑ t,H t)=0 → H=0
  have action (p : V → ℂ) : Function.Injective (M.map (eval p)).mulVec ↔
      D (fun s i => p (s,.inl i)) (fun s j => p (s,.inr j)) := by
    apply LastSliceBatch.stack_injective_iff e (fun s i => p (s,.inl i)) (fun s j => p (s,.inr j))
    intro row col
    change eval p (M row col) = _
    rcases row with ⟨t,s|i|j⟩|ij <;> rcases col with ⟨l,u,v⟩
    · by_cases ht : l=t <;> simp [M,ht]
    · by_cases ht : l=t <;> by_cases hi : u=i <;> simp [M,ht,hi]
    · by_cases ht : l=t <;> by_cases hj : v=j <;> simp [M,ht,hj]
    · by_cases he : (u,v)=ij <;> simp [M,he]
  obtain ⟨x,y,h⟩ := one
  let w (p : V) := p.2.elim (x p.1) (y p.1)
  obtain ⟨C,nz,works⟩ := rank_polynomial M w ((action w).mpr h)
  exact ⟨C,nz,fun p hp => (action p).mp (works p hp)⟩

/-- The single marked normal becomes zero after pinning one entry exactly
when the sampled products, marked arms and pinned entry separate forms. -/
private lemma pin_polynomial {A B P : Type*} [Fintype A] [Fintype B] [Fintype P]
    (s₀ : P) (pin : A×B) (one : ∃ x : P → A → ℂ, ∃ y : P → B → ℂ, ∀ H : A×B → ℂ,
      (∀ s, (∑ ij, (x s ij.1*y s ij.2)*H ij)=0) →
      (∀ i, (∑ j, y s₀ j*H (i,j))=0) → (∀ j, (∑ i, x s₀ i*H (i,j))=0) → H pin=0 → H=0) :
    ∃ C : MvPolynomial (P × (A ⊕ B)) ℂ, C≠0 ∧ ∀ p, eval p C≠0 →
      ∀ H : A×B → ℂ, (∀ s, (∑ ij, (p (s,.inl ij.1)*p (s,.inr ij.2))*H ij)=0) →
        (∀ i, (∑ j, p (s₀,.inr j)*H (i,j))=0) →
        (∀ j, (∑ i, p (s₀,.inl i)*H (i,j))=0) → H pin=0 → H=0 := by
  classical
  let V := P × (A ⊕ B)
  let Row := P ⊕ (A ⊕ (B ⊕ Unit))
  let M : Matrix Row (A×B) (MvPolynomial V ℂ) := fun r ij => r.elim
    (fun s => X (s,.inl ij.1)*X (s,.inr ij.2))
    (Sum.elim (fun i => if ij.1=i then X (s₀,.inr ij.2) else 0)
      (Sum.elim (fun j => if ij.2=j then X (s₀,.inl ij.1) else 0)
        (fun _ => if ij=pin then 1 else 0)))
  let null (p : V → ℂ) := ∀ H : A×B → ℂ, (∀ s, (∑ ij, (p (s,.inl ij.1)*p (s,.inr ij.2))*H ij)=0) →
    (∀ i, (∑ j, p (s₀,.inr j)*H (i,j))=0) → (∀ j, (∑ i, p (s₀,.inl i)*H (i,j))=0) → H pin=0 → H=0
  have action (p : V → ℂ) : Function.Injective (M.map (eval p)).mulVec ↔ null p := by
    let N := M.map (eval p)
    have outer (s : P) (H : A×B → ℂ) :
        N.mulVec H (.inl s)=(∑ ij, (p (s,.inl ij.1)*p (s,.inr ij.2))*H ij) := by
      apply Finset.sum_congr rfl
      intro ij _
      change (eval p (M (.inl s) ij))*H ij=_
      rw [show M (.inl s) ij=X (s,.inl ij.1)*X (s,.inr ij.2) from rfl,map_mul,eval_X,eval_X]
    have row (i : A) (H : A×B → ℂ) : N.mulVec H (.inr (.inl i))=(∑ j, p (s₀,.inr j)*H (i,j)) := by
      change (∑ ij : A×B, eval p (if ij.1=i then X (s₀,.inr ij.2) else 0)*H ij)=_
      rw [Fintype.sum_prod_type]
      simp [apply_ite,ite_mul,Finset.sum_ite_irrel]
    have col (j : B) (H : A×B → ℂ) : N.mulVec H (.inr (.inr (.inl j)))=(∑ i, p (s₀,.inl i)*H (i,j)) := by
      change (∑ ij : A×B, eval p (if ij.2=j then X (s₀,.inl ij.1) else 0)*H ij)=_
      rw [Fintype.sum_prod_type]
      simp [apply_ite,ite_mul]
    have entry (H : A×B → ℂ) : N.mulVec H (.inr (.inr (.inr ())))=H pin := by
      change (∑ ij, eval p (if ij=pin then 1 else 0)*H ij)=_
      simp [apply_ite,ite_mul]
    change Function.Injective N.mulVecLin ↔ _
    rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
    constructor
    · intro drop H pr le ri val
      apply drop H
      funext r
      rcases r with s|i|j|⟨⟩
      · exact (outer s H).trans (pr s)
      · exact (row i H).trans (le i)
      · exact (col j H).trans (ri j)
      · exact (entry H).trans val
    · intro cert H vanish
      exact cert H (fun s => (outer s H).symm.trans (congrFun vanish _))
        (fun i => (row i H).symm.trans (congrFun vanish _))
        (fun j => (col j H).symm.trans (congrFun vanish _)) ((entry H).symm.trans (congrFun vanish _))
  obtain ⟨x,y,h⟩ := one
  let w (p : V) := p.2.elim (x p.1) (y p.1)
  obtain ⟨C,nz,works⟩ := rank_polynomial M w ((action w).mpr h)
  exact ⟨C,nz,fun p hp => (action p).mp (works p hp)⟩

end CriticalExtreme

namespace CriticalExtreme

open MvPolynomial

/-- Put the distinguished product at the last row and column and place the
other products in every old coordinate except one. A normal left after both
marked arms is completely determined by that missing coordinate. -/
private lemma one_coordinate_free (d e : ℕ) (s₀ : Fin (d*e)) :
    ∃ pin : Fin (d+1) × Fin (e+1),
    ∃ x : Fin (d*e) → Fin (d+1) → ℂ, ∃ y : Fin (d*e) → Fin (e+1) → ℂ,
      ∀ H : Fin (d+1) × Fin (e+1) → ℂ, (∀ s, (∑ ij, (x s ij.1*y s ij.2)*H ij)=0) →
        (∀ i, (∑ j, y s₀ j*H (i,j))=0) → (∀ j, (∑ i, x s₀ i*H (i,j))=0) →
        H pin=0 → H=0 := by
  classical
  let pos : Fin (d*e) ≃ Fin d × Fin e := finProdFinEquiv.symm
  let a (s : Fin (d*e)) := if s=s₀ then Fin.last d else (pos s).1.castSucc
  let b (s : Fin (d*e)) := if s=s₀ then Fin.last e else (pos s).2.castSucc
  let x (s : Fin (d*e)) : Fin (d+1) → ℂ := Pi.single (a s) 1
  let y (s : Fin (d*e)) : Fin (e+1) → ℂ := Pi.single (b s) 1
  refine ⟨((pos s₀).1.castSucc,(pos s₀).2.castSucc),x,y,?_⟩
  intro H products rows cols pinned
  have val (s : Fin (d*e)) : H (a s,b s)=0 := by
    simpa [x,y,Fintype.sum_prod_type,Pi.single_apply,ite_mul,mul_ite,Finset.sum_ite_irrel] using products s
  have lastRow (j : Fin (e+1)) : H (Fin.last d,j)=0 := by
    simpa [x,a,Pi.single_apply,ite_mul] using cols j
  have lastCol (i : Fin (d+1)) : H (i,Fin.last e)=0 := by
    simpa [y,b,Pi.single_apply,ite_mul] using rows i
  have old (i : Fin d) (j : Fin e) : H (i.castSucc,j.castSucc)=0 := by
    let s := pos.symm (i,j)
    have loc : pos s=(i,j) := pos.apply_symm_apply _
    by_cases h : s=s₀
    · rwa [← h,loc] at pinned
    · simpa only [a,b,if_neg h,loc] using val s
  funext ⟨i,j⟩
  exact Fin.lastCases (lastRow j) (fun i => Fin.lastCases (lastCol i.castSucc) (old i) j) i

/-- A nonzero coordinate in every vector and nonzero two-coordinate minors
keep all the corresponding projective directions distinct. -/
private lemma projective_polynomial {P I V : Type*} [Fintype P] (coord : P → I → V)
    (i₀ i₁ : I) (p₀ : V → ℂ) (one : ∀ t, p₀ (coord t i₀)=1)
    (different : Function.Injective (fun t => p₀ (coord t i₁))) :
    ∃ C : MvPolynomial V ℂ, C≠0 ∧ ∀ p : V → ℂ, eval p C≠0 →
      (∀ t, (fun i => p (coord t i))≠0) ∧
      ∀ t s, t≠s → ∀ c : ℂ, (fun i => p (coord t i))≠c • (fun i => p (coord s i)) := by
  classical
  let U := {ts : P×P // ts.1≠ts.2}
  let delta (z : U) : MvPolynomial V ℂ :=
    X (coord z.val.1 i₀)*X (coord z.val.2 i₁)-X (coord z.val.1 i₁)*X (coord z.val.2 i₀)
  let C : MvPolynomial V ℂ := (∏ t : P, X (coord t i₀))*(∏ z : U, delta z)
  have goodDelta (z : U) : eval p₀ (delta z) ≠ 0 := by
    simp only [delta,map_sub,map_mul,eval_X,one,one_mul,mul_one]
    exact sub_ne_zero.mpr (different.ne (Ne.symm z.property))
  have nonzero : eval p₀ C≠0 := by
    simp only [C,map_mul,map_prod,eval_X,one,Finset.prod_const_one,one_mul]
    exact Finset.prod_ne_zero_iff.mpr fun z _ => goodDelta z
  refine ⟨C,fun h => nonzero (by rw [h,map_zero]),?_⟩
  intro p hp
  simp only [C,map_mul,map_prod,eval_X] at hp
  obtain ⟨lead,pairs⟩ := mul_ne_zero_iff.mp hp
  refine ⟨fun t ht => Finset.prod_ne_zero_iff.mp lead t (Finset.mem_univ _) (congrFun ht i₀),?_⟩
  intro t s hts c eq
  apply Finset.prod_ne_zero_iff.mp pairs (⟨(t,s),hts⟩ : U) (Finset.mem_univ _)
  have h₀ : p (coord t i₀)=c*p (coord s i₀) := congrFun eq i₀
  have h₁ : p (coord t i₁)=c*p (coord s i₁) := congrFun eq i₁
  simp only [delta,map_sub,map_mul,eval_X,h₀,h₁]
  ring

end CriticalExtreme

namespace CriticalExtreme

open MvPolynomial

/-- A direct family may be extended by one marked point at the cost of
pinning a single coefficient of its normal. All marked vectors can be
chosen projectively distinct on both axes. -/
private lemma prepare_one_more {d e m : ℕ} (hd : 0<d) (he : 0<e) (room : m<d*e)
    (old : ∃ mark : Fin m ↪ Fin (d*e), ∃ x : Fin (d*e) → Fin (d+1) → ℂ,
      ∃ y : Fin (d*e) → Fin (e+1) → ℂ, ∀ H : Fin m → Fin (d+1) × Fin (e+1) → ℂ,
        (∀ t s, (∑ ij, (x s ij.1*y s ij.2)*H t ij)=0) →
        (∀ t i, (∑ j, y (mark t) j*H t (i,j))=0) →
        (∀ t j, (∑ i, x (mark t) i*H t (i,j))=0) → (∑ t,H t)=0 → H=0) :
    ∃ first : Fin (m+1) ↪ Fin (d*e), ∃ x : Fin (d*e) → Fin (d+1) → ℂ,
    ∃ y : Fin (d*e) → Fin (e+1) → ℂ, ∃ t₀ : Fin (m+1), ∃ ij₀ : Fin (d+1) × Fin (e+1),
      (∀ t, x (first t)≠0) ∧ (∀ t s, t≠s → ∀ c : ℂ, x (first t)≠c • x (first s)) ∧
      (∀ t, y (first t)≠0) ∧ (∀ t s, t≠s → ∀ c : ℂ, y (first t)≠c • y (first s)) ∧
      ∀ H : Fin (m+1) → Fin (d+1) × Fin (e+1) → ℂ,
        (∀ t s, (∑ ij, (x s ij.1*y s ij.2)*H t ij)=0) →
        (∀ t i, (∑ j, y (first t) j*H t (i,j))=0) →
        (∀ t j, (∑ i, x (first t) i*H t (i,j))=0) →
        (∑ t,H t)=0 → H t₀ ij₀=0 → H=0 := by
  classical
  obtain ⟨mark,initial⟩ := old
  obtain ⟨s₀,unused⟩ : ∃ s : Fin (d*e), s ∉ Set.range mark := by
    by_contra! all
    have onto : Function.Surjective mark := all
    have bad := Fintype.card_le_of_surjective mark onto
    simp only [Fintype.card_fin] at bad
    omega
  let first : Fin (m+1) ↪ Fin (d*e) := Fin.Embedding.cons mark unused
  have newLabel : first 0=s₀ := rfl
  have oldLabel (i : Fin m) : first i.succ=mark i := rfl
  obtain ⟨P,Pnz,oldGood⟩ := old_polynomial mark initial
  obtain ⟨ij₀,extra⟩ := one_coordinate_free d e s₀
  obtain ⟨Q,Qnz,pinGood⟩ := pin_polynomial s₀ ij₀ extra
  let V := Fin (d*e) × (Fin (d+1) ⊕ Fin (e+1))
  let xi (s : Fin (d*e)) (i : Fin (d+1)) : V := (s,.inl i)
  let yi (s : Fin (d*e)) (j : Fin (e+1)) : V := (s,.inr j)
  let i₁ : Fin (d+1) := ⟨1,by omega⟩
  let j₁ : Fin (e+1) := ⟨1,by omega⟩
  let test (q : V) : ℂ := q.2.elim (fun i => if i.val=0 then 1 else (q.1.val : ℂ))
    (fun j => if j.val=0 then 1 else (q.1.val : ℂ))
  have inj : Function.Injective (fun (s : Fin (d*e)) => (s.val : ℂ)) :=
    fun _ _ h => Fin.ext (Nat.cast_injective h)
  obtain ⟨S,Snz,xGood⟩ := projective_polynomial xi 0 i₁ test (fun _ => by simp [test,xi]) (by
    simpa [test,xi,i₁] using inj)
  obtain ⟨T,Tnz,yGood⟩ := projective_polynomial yi 0 j₁ test (fun _ => by simp [test,yi]) (by
    simpa [test,yi,j₁] using inj)
  obtain ⟨p,hp⟩ : ∃ p : V → ℂ, eval p (P*Q*S*T)≠0 := by
    by_contra! vanish
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero Pnz Qnz) Snz) Tnz)
      (MvPolynomial.funext fun p => by rw [vanish p,map_zero])
  simp only [map_mul,mul_ne_zero_iff] at hp
  obtain ⟨⟨⟨pP,pQ⟩,pS⟩,pT⟩ := hp
  obtain ⟨xn,xd⟩ := xGood p pS
  obtain ⟨yn,yd⟩ := yGood p pT
  let x (s : Fin (d*e)) (i : Fin (d+1)) := p (xi s i)
  let y (s : Fin (d*e)) (j : Fin (e+1)) := p (yi s j)
  refine ⟨first,x,y,0,ij₀,fun t => xn (first t),
    fun t s h => xd (first t) (first s) (fun z => h (first.injective z)),
    fun t => yn (first t),fun t s h => yd (first t) (first s) (fun z => h (first.injective z)),?_⟩
  intro H products rows cols total pinned
  have zero₀ := pinGood p pQ (H 0) (products 0)
    (fun i => by simpa only [newLabel,y,yi] using rows 0 i)
    (fun j => by simpa only [newLabel,x,xi] using cols 0 j) pinned
  have sumOld : (∑ t : Fin m, H t.succ)=0 := by
    rwa [Fin.sum_univ_succ,zero₀,zero_add] at total
  have zeroOld := oldGood p pP (fun t : Fin m => H t.succ) (fun t => products t.succ)
    (fun t i => by simpa only [oldLabel,y,yi] using rows t.succ i)
    (fun t j => by simpa only [oldLabel,x,xi] using cols t.succ j) sumOld
  funext t
  change H t=0
  exact Fin.cases zero₀ (fun j => congrFun zeroOld j) t

/-- On the short rectangular core, the ordinary relation space for all
`2a-1` selected points is detected by one prescribed scalar entry. -/
lemma pinned_core (a : ℕ) (ha : 5 ≤ a) :
    let p := (a-2)*(a-1)
    let m := 2*a-1
    ∃ first : Fin m ↪ Fin p, ∃ x : Fin p → Fin (a-1) → ℂ, ∃ y : Fin p → Fin a → ℂ,
    ∃ t₀ : Fin m, ∃ ij₀ : Fin (a-1) × Fin a,
      (∀ t, x (first t)≠0) ∧ (∀ t s, t≠s → ∀ c : ℂ, x (first t)≠c • x (first s)) ∧
      (∀ t, y (first t)≠0) ∧ (∀ t s, t≠s → ∀ c : ℂ, y (first t)≠c • y (first s)) ∧
      ∀ H : Fin m → Fin (a-1) × Fin a → ℂ,
        (∀ t s, (∑ ij, (x s ij.1*y s ij.2)*H t ij)=0) →
        (∀ t i, (∑ j, y (first t) j*H t (i,j))=0) →
        (∀ t j, (∑ i, x (first t) i*H t (i,j))=0) →
        (∑ t,H t)=0 → H t₀ ij₀=0 → H=0 := by
  obtain ⟨k,rfl⟩ : ∃ k, a=k+5 := ⟨a-5,by omega⟩
  dsimp only
  rw [show 2*(k+5)-1=2*(k+4)+1 by omega]
  apply prepare_one_more (d:=k+3) (e:=k+4) (m:=2*(k+4)) (by omega) (by omega)
    (by nlinarith only [Nat.zero_le k,Nat.zero_le (k*k)])
  obtain ⟨mark,x,y,direct,_,_⟩ := LastSliceTwo.exists_finite_batch_separated
    (a:=k+4) (b:=k+5) (m:=2*(k+4)) (by omega) (by omega) (by omega) (by omega)
  exact ⟨mark,x,y,direct⟩

end CriticalExtreme

namespace CriticalLastSlice.TwoPlanes

/-- Restriction to a basis of a hyperplane, together with one transverse
value, determines a linear form on the enlarged row. -/
theorem tilted_row_iff {K V J : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h ell g : V →ₗ[K] K) (B : Module.Basis J K h.ker) (y : V) (hy : h y ≠ 0) (c : K) :
    (g y = 0 ∧ ∀ j, g (B j : V) = -c*ell (B j : V)) ↔
      g = (-c) • ell + (c*ell y / h y) • h := by
  constructor
  · rintro ⟨gy,gb⟩
    let L : h.ker →ₗ[K] K := (g + c • ell).comp h.ker.subtype
    have hz : L = 0 := B.ext fun j => by
      change g (B j : V) + c*ell (B j : V) = 0
      rw [gb]
      ring
    ext p
    let q := p - (h p / h y) • y
    have hq : q ∈ h.ker := by
      change h (p - (h p/h y) • y) = 0
      rw [map_sub,map_smul,smul_eq_mul,div_mul_cancel₀ _ hy,sub_self]
    have eq : g q + c*ell q = 0 := LinearMap.congr_fun hz ⟨q,hq⟩
    simp only [q,map_sub,map_smul,smul_eq_mul,gy,mul_zero,sub_zero,div_eq_mul_inv] at eq
    change g p = -c*ell p + (c*ell y / h y)*h p
    rw [div_eq_mul_inv]
    linear_combination eq
  · rintro rfl
    constructor
    · change -c*ell y + (c*ell y / h y)*h y = 0
      rw [div_mul_cancel₀ _ hy]
      ring
    · intro j
      have hb := (B j).property
      change h (B j : V) = 0 at hb
      change -c*ell (B j : V) + (c*ell y / h y)*h (B j : V) = _
      rw [hb,mul_zero,add_zero]

/-- Every bilinear form on the extended first factor has this unique
decomposition into its old rows and its last row. -/
theorem tilted_form_decompose {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] (H : (U × K) →ₗ[K] (V →ₗ[K] K)) (x : U) (a : K) :
    H (x,a) = H (x,0) + a • H (0,1) := by
  have split : (x,a) = (x,0) + a • ((0,1) : U × K) := by ext <;> simp
  rw [split,map_add,map_smul]

/-- Conversely all pairs of old rows and a last row admit a linear lift. -/
theorem tilted_form_exists {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] (F : U →ₗ[K] (V →ₗ[K] K)) (g : V →ₗ[K] K) :
    ∃ H : (U × K) →ₗ[K] (V →ₗ[K] K), ∀ p, H p = F p.1 + p.2 • g := by
  refine ⟨F.comp (LinearMap.fst K U K) + (LinearMap.snd K U K).smulRight g,?_⟩
  intro p
  rfl

/-- After extending the first factor by one coordinate, sample a basis of
the right hyperplane against the new row. Tilt just its distinguished
basis product by u. At each old marked point the normal has a unique
possible last row, recovered by a divided evaluation. -/
theorem tilted_normal_iff {K U V I J : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [DecidableEq J]
    (x : I → U) (y : I → V) (t : I) (h ell : V →ₗ[K] K) (B : Module.Basis J K h.ker)
    (j₀ : J) (dual : ∀ j, ell (B j : V) = if j=j₀ then 1 else 0)
    (hy : h (y t) ≠ 0) (u : U) (F : U →ₗ[K] (V →ₗ[K] K)) (g : V →ₗ[K] K) :
    let X : I ⊕ J → U × K := Sum.elim (fun i => (x i,0)) (fun j => ((if j=j₀ then u else 0),1))
    let Y : I ⊕ J → V := Sum.elim y (fun j => (B j : V))
    let b := fun (p : U × K) (v : V) => F p.1 v + p.2*g v
    ((∀ i, b (X i) (Y i) = 0) ∧ (∀ p, b p (y t) = 0) ∧ (∀ v, b (x t,0) v = 0)) ↔
      (∀ i, F (x i) (y i) = 0) ∧ (∀ p, F p (y t) = 0) ∧ (∀ v, F (x t) v = 0) ∧
      g = (-(F u (B j₀ : V))) • ell + (F u (B j₀ : V)*ell (y t)/h (y t)) • h := by
  intro X Y b
  let c := F u (B j₀ : V)
  have split (j : J) :
      b (X (.inr j)) (Y (.inr j))=0 ↔ g (B j : V) = -c*ell (B j : V) := by
    by_cases atZero : j=j₀
    · subst j
      simp [X,Y,b,dual,c]
      constructor <;> intro eq <;> linear_combination eq
    · simp [X,Y,b,atZero,dual]
  constructor
  · rintro ⟨points,atY,atX⟩
    refine ⟨fun i => by simpa [X,Y,b] using points (.inl i),
      fun p => by simpa [b] using atY (p,0), fun v => by simpa [b] using atX v,?_⟩
    apply (tilted_row_iff h ell g B (y t) hy c).mp
    exact ⟨by simpa [b] using atY (0,1),fun j => (split j).mp (points (.inr j))⟩
  · rintro ⟨points,atY,atX,row⟩
    obtain ⟨gy,gb⟩ := (tilted_row_iff h ell g B (y t) hy c).mpr row
    refine ⟨?_,?_,?_⟩
    · rintro (i|j)
      · simpa only [X,Y,b,Sum.elim_inl,zero_mul,add_zero] using points i
      · exact (split j).mpr (gb j)
    · intro p
      simp [b,atY,gy]
    · intro v
      simp [b,atX]

/-- On an old relation, the entire sum of new rows is a scalar multiple
of h. Its coefficient is the divided evaluation of the tilted sample. -/
theorem tilted_bottom_sum {K U V T : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [Fintype T] (h ell : V →ₗ[K] K) (u : U) (z : V)
    (y : T → V) (F : T → U →ₗ[K] (V →ₗ[K] K)) (g : T → V →ₗ[K] K) (w : T → K)
    (row : ∀ t, g t = (-(F t u z)) • ell + (F t u z*ell (y t)/h (y t)) • h)
    (old : ∑ t, w t • F t = 0) :
    (∑ t, w t • g t) = (∑ t, w t * (F t u z*ell (y t)/h (y t))) • h := by
  have cancel : ∑ t, w t * F t u z = 0 := by
    have he := LinearMap.congr_fun (LinearMap.congr_fun old u) z
    simpa only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,LinearMap.zero_apply] using he
  calc
    _ = ∑ t, ((-(w t*F t u z)) • ell + (w t*(F t u z*ell (y t)/h (y t))) • h) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [row t,smul_add,smul_smul,smul_smul,mul_neg]
    _ = _ := by
      rw [Finset.sum_add_distrib,← Finset.sum_smul,← Finset.sum_smul,Finset.sum_neg_distrib,cancel,
        neg_zero,zero_smul,zero_add]

/-- Restoring the last row imposes precisely one extra scalar equation on
a weighted relation between the marked old normals. -/
theorem tilted_relations_iff {K U V T : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [Fintype T] (h ell : V →ₗ[K] K) (hh : h ≠ 0)
    (u : U) (z : V) (y : T → V) (F : T → U →ₗ[K] (V →ₗ[K] K)) (g : T → V →ₗ[K] K) (w : T → K)
    (row : ∀ t, g t = (-(F t u z)) • ell + (F t u z*ell (y t)/h (y t)) • h) :
    ((∑ t, w t • F t) = 0 ∧ (∑ t, w t • g t) = 0) ↔
      ((∑ t, w t • F t) = 0 ∧ ∑ t, w t * (F t u z*ell (y t)/h (y t)) = 0) := by
  constructor
  · rintro ⟨old,bot⟩
    rw [tilted_bottom_sum h ell u z y F g w row old] at bot
    exact ⟨old,(smul_eq_zero.mp bot).resolve_right hh⟩
  · rintro ⟨old,value⟩
    exact ⟨old,(tilted_bottom_sum h ell u z y F g w row old).trans (by rw [value,zero_smul])⟩

theorem tilted_unweighted_iff {K U V T : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [Fintype T] (h ell : V →ₗ[K] K) (hh : h ≠ 0)
    (u : U) (z : V) (y : T → V) (F : T → U →ₗ[K] (V →ₗ[K] K)) (g : T → V →ₗ[K] K)
    (row : ∀ t, g t = (-(F t u z)) • ell + (F t u z*ell (y t)/h (y t)) • h) :
    ((∑ t, F t) = 0 ∧ (∑ t, g t) = 0) ↔
      ((∑ t, F t) = 0 ∧ ∑ t, F t u z*ell (y t)/h (y t) = 0) := by
  simpa only [one_smul,one_mul] using tilted_relations_iff h ell hh u z y F g (fun _ => 1) row

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- A prescribed z in the hyperplane and a linear form taking value one
there extend to a basis of the hyperplane with exactly the required
Kronecker evaluations. The number of new samples is dim(V) minus one. -/
theorem tilted_adapted_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h ell : V →ₗ[K] K) (hh : h ≠ 0)
    (z : V) (hz : h z = 0) (unit : ell z = 1) :
    ∃ (B : Module.Basis (Fin (Module.finrank K V - 1)) K h.ker) (j₀ : Fin (Module.finrank K V - 1)),
      (B j₀ : V) = z ∧ (∀ j, ell (B j : V) = if j=j₀ then 1 else 0) := by
  classical
  let z₀ : h.ker := ⟨z,hz⟩
  let l := ell.comp h.ker.subtype
  have lz : l z₀=1 := unit
  have nonzero : l≠0 := by
    intro eq
    rw [eq,LinearMap.zero_apply] at lz
    exact zero_ne_one lz
  let lift : K × l.ker →ₗ[K] h.ker := (LinearMap.fst K K l.ker).smulRight z₀ +
      l.ker.subtype.comp (LinearMap.snd K K l.ker)
  have act (p : K × l.ker) : lift p = p.1 • z₀ + (p.2 : h.ker) := rfl
  have left (p : K × l.ker) : l (lift p) = p.1 := by
    rw [act,map_add,map_smul,smul_eq_mul,lz,mul_one,LinearMap.mem_ker.mp p.2.property,add_zero]
  have inj : Function.Injective lift := by
    intro p q eq
    have h1 := (left p).symm.trans ((congrArg l eq).trans (left q))
    refine Prod.ext h1 (Subtype.ext ?_)
    rw [act,act,h1] at eq
    exact add_left_cancel eq
  have sur : Function.Surjective lift := by
    intro w
    have hk : w - l w • z₀ ∈ l.ker := by
      rw [LinearMap.mem_ker,map_sub,map_smul,smul_eq_mul,lz,mul_one,sub_self]
    exact ⟨(l w, ⟨_,hk⟩),(act _).trans (by simp)⟩
  let E := LinearEquiv.ofBijective lift ⟨inj,sur⟩
  let bp := Module.Basis.singleton Unit K
  let bq := Module.finBasis K l.ker
  let b₀ := (bp.prod bq).map E
  let j₁ : Unit ⊕ Fin (Module.finrank K l.ker) := .inl ()
  have zval : b₀ j₁ = z₀ := by
    rw [show b₀ j₁ = lift ((bp.prod bq) (.inl ())) from rfl,act]
    simp [bp]
  have dval (j : Unit ⊕ Fin (Module.finrank K l.ker)) :
      l (b₀ j) = if j=j₁ then 1 else 0 := by
    change l (lift ((bp.prod bq) j)) = _
    rw [left]
    rcases j with a|b <;> simp [bp,j₁]
  have dim1 := Module.Dual.finrank_ker_add_one_of_ne_zero nonzero
  have dim2 := Module.Dual.finrank_ker_add_one_of_ne_zero hh
  let ids : (Unit ⊕ Fin (Module.finrank K l.ker)) ≃ Fin (Module.finrank K V - 1) :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unit]; omega)
  refine ⟨b₀.reindex ids,ids j₁,?_ ,?_⟩
  · rw [Module.Basis.reindex_apply,Equiv.symm_apply_apply,zval]
  · intro j
    obtain ⟨i,rfl⟩ := ids.surjective j
    rw [Module.Basis.reindex_apply,Equiv.symm_apply_apply]
    change l (b₀ i) = _
    simpa only [Equiv.apply_eq_iff_eq] using dval i

/-- A nonzero restriction of a scalar test cuts the relation space by
exactly one dimension. -/
theorem tilted_cut_dimension {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (R : Submodule K W) [FiniteDimensional K R] (f : W →ₗ[K] K)
    (nonzero : ∃ w ∈ R, f w ≠ 0) :
    Module.finrank K (R ⊓ f.ker : Submodule K W) + 1 = Module.finrank K R := by
  let g := f.comp R.subtype
  have hg : g≠0 := by
    rintro eq
    obtain ⟨w,hw,hn⟩ := nonzero
    exact hn (LinearMap.congr_fun eq ⟨w,hw⟩)
  let incl : g.ker →ₗ[K] (R ⊓ f.ker : Submodule K W) :=
    (R.subtype.comp g.ker.subtype).codRestrict _ (fun x => ⟨x.val.property,x.property⟩)
  have inj : Function.Injective incl := by
    intro x y eq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : (R ⊓ f.ker : Submodule K W) => (q : W)) eq
  have sur : Function.Surjective incl := fun w => ⟨⟨⟨w.val,w.property.1⟩,w.property.2⟩,Subtype.ext rfl⟩
  have dims := (LinearEquiv.ofBijective incl ⟨inj,sur⟩).finrank_eq
  rw [← dims]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero hg

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- A surviving relation is exactly in the kernel of the divided-evaluation
functional on the original relation space. One nonzero witness therefore
certifies a drop of exactly one dimension. -/
theorem tilted_relation_rank_step {K U V T D : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup D] [Module K D] [FiniteDimensional K D]
    [Fintype T] (h ell : V →ₗ[K] K) (hh : h≠0) (u : U) (z : V) (y : T → V)
    (F : D →ₗ[K] (T → U →ₗ[K] (V →ₗ[K] K))) (old : ∀ v, ∑ t, F v t=0)
    (witness : ∃ v, ∑ t, F v t u z*ell (y t)/h (y t) ≠ 0) :
    let row (v : D) (t : T) :=
      (-(F v t u z)) • ell + (F v t u z*ell (y t)/h (y t)) • h
    ∃ R : Submodule K D, (∀ v, v∈R ↔ ∑ t, row v t=0) ∧
      Module.finrank K R + 1 = Module.finrank K D := by
  intro row
  let L : D →ₗ[K] K := {
    toFun := fun v => ∑ t, F v t u z*ell (y t)/h (y t)
    map_add' := by
      intro v w
      simp only [map_add,Pi.add_apply,LinearMap.add_apply,add_mul,add_div,Finset.sum_add_distrib]
    map_smul' := by
      intro c v
      simp only [map_smul,Pi.smul_apply,LinearMap.smul_apply,smul_eq_mul,RingHom.id_apply,
        ← Finset.mul_sum,div_eq_mul_inv,mul_assoc] }
  have hL : L≠0 := by
    intro zero
    obtain ⟨v,hv⟩ := witness
    exact hv (LinearMap.congr_fun zero v)
  refine ⟨L.ker,?_,Module.Dual.finrank_ker_add_one_of_ne_zero hL⟩
  intro v
  have eq := tilted_unweighted_iff h ell hh u z y (F v) (row v) (fun _ => rfl)
  constructor
  · intro hv
    exact (eq.mpr ⟨old v,LinearMap.mem_ker.mp hv⟩).2
  · intro hv
    exact LinearMap.mem_ker.mpr (eq.mp ⟨old v,hv⟩).2

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- Vanishing on both summands is equivalent to vanishing of a weighted
sum of the enlarged bilinear forms themselves. -/
theorem tilted_sum_forms {K U V T : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [Fintype T]
    (H : T → (U × K) →ₗ[K] (V →ₗ[K] K)) (F : T → U →ₗ[K] (V →ₗ[K] K))
    (g : T → V →ₗ[K] K) (w : T → K) (split : ∀ t p, H t p = F t p.1 + p.2 • g t) :
    (∑ t, w t • H t) = 0 ↔ (∑ t, w t • F t) = 0 ∧ (∑ t, w t • g t) = 0 := by
  have parts (p : U × K) : (∑ t, w t • H t) p = (∑ t, w t • F t) p.1 + p.2 • ∑ t, w t • g t := by
    simp only [LinearMap.sum_apply,LinearMap.smul_apply,split,smul_add,Finset.sum_add_distrib,
      Finset.smul_sum,smul_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [mul_comm]
  constructor
  · intro zero
    refine ⟨LinearMap.ext fun u => ?_,?_⟩
    · simpa only [zero,LinearMap.zero_apply,zero_smul,add_zero] using (parts (u,0)).symm
    · simpa only [zero,LinearMap.zero_apply,map_zero,one_smul,zero_add] using (parts (0,1)).symm
  · rintro ⟨old,last⟩
    exact LinearMap.ext fun p => by simp [parts,old,last]

/-- A linear relation among the enlarged normals is exactly an old
relation satisfying the one divided-evaluation equation. -/
theorem tilted_lifted_relation_iff {K U V T : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [Fintype T] (h ell : V →ₗ[K] K) (hh : h≠0)
    (u : U) (z : V) (y : T → V) (F : T → U →ₗ[K] (V →ₗ[K] K)) (g : T → V →ₗ[K] K)
    (H : T → (U × K) →ₗ[K] (V →ₗ[K] K)) (w : T → K)
    (split : ∀ t p, H t p=F t p.1 + p.2 • g t)
    (row : ∀ t, g t = (-(F t u z)) • ell + (F t u z*ell (y t)/h (y t)) • h) :
    (∑ t, w t • H t) = 0 ↔ (∑ t, w t • F t)=0 ∧
      ∑ t, w t*(F t u z*ell (y t)/h (y t))=0 :=
  (tilted_sum_forms H F g w split).trans (tilted_relations_iff h ell hh u z y F g w row)

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.Poles

open Polynomial

/-- A pole appearing in exactly one term prevents a reciprocal combination
from vanishing at every common regular evaluation point. -/
theorem reciprocal_polynomials {K I : Type*} [Field K] [Infinite K] [Fintype I]
    (d : I → K[X]) (v : I → K) (p : I) (t₀ : K) (vp : v p ≠ 0)
    (regular : ∀ i, d i ≠ 0) (pole : (d p).eval t₀=0)
    (other : ∀ i, i ≠ p → (d i).eval t₀ ≠ 0) :
    ∃ t : K, (∀ i, (d i).eval t ≠ 0) ∧ (∑ i, v i/(d i).eval t) ≠ 0 := by
  classical
  let N : K[X] := ∑ i, C (v i) * ∏ j ∈ Finset.univ.erase i, d j
  have evalN (t : K) : N.eval t = ∑ i, v i * ∏ j ∈ Finset.univ.erase i, (d j).eval t := by
    simp only [N,eval_finsetSum,eval_mul,eval_C,eval_prod]
  have atPole : N.eval t₀ = v p * ∏ j ∈ Finset.univ.erase p, (d j).eval t₀ := by
    rw [evalN, Finset.sum_eq_single p]
    · intro i _ hi
      have mem : p ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hi,Finset.mem_univ p⟩
      rw [Finset.prod_eq_zero mem pole,mul_zero]
    · simp
  have survives : N.eval t₀ ≠ 0 := by
    rw [atPole]
    exact mul_ne_zero vp (Finset.prod_ne_zero_iff.mpr fun j hj => other j (Finset.ne_of_mem_erase hj))
  have num : N ≠ 0 := fun zero => survives (by rw [zero,eval_zero])
  have joint : N*(∏ i,d i) ≠ 0 := mul_ne_zero num (Finset.prod_ne_zero_iff.mpr fun i _ => regular i)
  obtain ⟨t,ht⟩ : ∃ t : K, (N*(∏ i,d i)).eval t ≠ 0 := by
    by_contra! vanishes
    exact joint (Polynomial.funext fun u => by rw [vanishes u,eval_zero])
  rw [eval_mul,eval_prod] at ht
  have nz (i : I) : (d i).eval t ≠ 0 := Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp ht).2 i (Finset.mem_univ i)
  refine ⟨t,nz,?_⟩
  have clear : N.eval t = (∑ i, v i/(d i).eval t) * (∏ j, (d j).eval t) := by
    rw [evalN,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    let E := ∏ j ∈ Finset.univ.erase i, (d j).eval t
    have product : E*(d i).eval t = ∏ j, (d j).eval t :=
      Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i)
    rw [← product]
    change v i*E = v i/(d i).eval t*(E*(d i).eval t)
    calc
      _ = (v i/(d i).eval t*(d i).eval t)*E := by rw [div_mul_cancel₀ _ (nz i)]
      _ = _ := by ring
  intro zero
  exact (mul_ne_zero_iff.mp ht).1 (by rw [clear,zero,zero_mul])

/-- Along `a+t*b`, only the slope of the marked denominator must be nonzero. -/
theorem reciprocal_on_line {K I : Type*} [Field K] [Infinite K] [Fintype I]
    (a b v : I → K) (p : I) (vp : v p ≠ 0) (pole : a p=0)
    (other : ∀ i, i≠p → a i≠0) (slope : b p≠0) :
    ∃ t : K, (∀ i, a i+t*b i≠0) ∧ (∑ i, v i/(a i+t*b i))≠0 := by
  let d (i : I) : K[X] := C (a i)+X*C (b i)
  have ev (i : I) (t : K) : (d i).eval t = a i+t*b i := by
    simp only [d,eval_add,eval_mul,eval_X,eval_C]
  have regular (i : I) : d i ≠ 0 := by
    intro zero
    by_cases eq : i=p
    · subst i
      apply slope
      have atOne := ev p 1
      simpa only [zero,eval_zero,pole,one_mul,zero_add] using atOne.symm
    · apply other i eq
      have atZero := ev i 0
      simpa only [zero,eval_zero,zero_mul,add_zero] using atZero.symm
  obtain ⟨t,ht,nonzero⟩ := reciprocal_polynomials d v p 0 vp regular
    (by simpa only [ev,zero_mul,add_zero] using pole)
    (fun i hi => by simpa only [ev,zero_mul,add_zero] using other i hi)
  exact ⟨t,fun i => by simpa only [ev] using ht i, by simpa only [ev] using nonzero⟩

end CriticalLastSlice.Poles

namespace CriticalLastSlice.Poles

open Module

private lemma quotient_form {K E J : Type*} [Field K] [Infinite K] [AddCommGroup E]
    [Module K E] [Finite J] (W : Submodule K E) (y : J → E) (off : ∀ j, y j ∉ W) :
    ∃ f : Dual K E, W ≤ f.ker ∧ ∀ j, f (y j) ≠ 0 := by
  have nz (j : J) : W.mkQ (y j) ≠ 0 := fun h => off j ((Submodule.Quotient.mk_eq_zero W).mp h)
  obtain ⟨g,hg⟩ := Module.exists_dual_forall_apply_ne_zero (K:=K) (fun j => W.mkQ (y j)) nz
  refine ⟨g.comp W.mkQ,?_,hg⟩
  intro w hw
  change g (W.mkQ w)=0
  rw [show W.mkQ w=0 from (Submodule.Quotient.mk_eq_zero W).mpr hw,map_zero]

/-- In the annihilator of `W`, the reciprocal sum has a nonzero value
if the marked line at `p` is distinct from all the others in the quotient. -/
theorem reciprocal_on_annihilator {K E I : Type*} [Field K] [Infinite K] [AddCommGroup E]
    [Module K E] [Fintype I] (W : Submodule K E) (y : I → E) (v : I → K) (p : I)
    (vp : v p ≠ 0) (off : ∀ i, y i ∉ W)
    (apart : ∀ i, i≠p → y i ∉ W ⊔ Submodule.span K {y p}) :
    ∃ f : Dual K E, W ≤ f.ker ∧ (∀ i, f (y i) ≠ 0) ∧ (∑ i, v i/f (y i)) ≠ 0 := by
  classical
  let U := W ⊔ Submodule.span K {y p}
  obtain ⟨f₀,ker₀,off₀⟩ := quotient_form U (fun i : {i : I // i≠p} => y i.val)
    (fun i => apart i.val i.property)
  obtain ⟨f₁,ker₁,off₁⟩ := quotient_form W y off
  have pole : f₀ (y p)=0 := ker₀ ((show Submodule.span K {y p} ≤ U from le_sup_right)
    (Submodule.subset_span (Set.mem_singleton _)))
  obtain ⟨t,regular,nonzero⟩ := reciprocal_on_line (fun i => f₀ (y i)) (fun i => f₁ (y i)) v p vp
    pole (fun i hi => off₀ ⟨i,hi⟩) (off₁ p)
  refine ⟨f₀+t • f₁,?_,regular,nonzero⟩
  intro w hw
  change f₀ w+t*f₁ w=0
  rw [show f₀ w=0 from ker₀ ((show W ≤ U from le_sup_left) hw),show f₁ w=0 from ker₁ hw,mul_zero,add_zero]

/-- A reciprocal witness annihilating the given vector `z`. -/
theorem reciprocal_at_z {K E I : Type*} [Field K] [Infinite K] [AddCommGroup E]
    [Module K E] [Fintype I] (z : E) (y : I → E) (v : I → K) (p : I) (vp : v p ≠ 0)
    (off : ∀ i, y i ∉ Submodule.span K {z})
    (apart : ∀ i, i≠p → y i ∉ Submodule.span K {z,y p}) :
    ∃ f : Dual K E, f z=0 ∧ (∀ i, f (y i) ≠ 0) ∧ (∑ i, v i/f (y i)) ≠ 0 := by
  have sep (i : I) (hi : i≠p) : y i ∉ Submodule.span K {z} ⊔ Submodule.span K {y p} := by
    rw [← Submodule.span_insert]
    exact apart i hi
  obtain ⟨f,hf,regular,nonzero⟩ := reciprocal_on_annihilator (Submodule.span K {z}) y v p vp off sep
  exact ⟨f,hf (Submodule.subset_span (Set.mem_singleton _)),regular,nonzero⟩

end CriticalLastSlice.Poles

namespace CriticalLastSlice.Poles

open Module

/-- In dimension at least three, a single vector avoids an additional
proper subspace and every plane spanned by two marked vectors. -/
theorem exists_outside_pairs {K E I : Type*} [Field K] [Infinite K] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] [Finite I] (dim : 3 ≤ finrank K E)
    (y : I → E) (bad : Submodule K E) (proper : bad≠⊤) :
    ∃ z : E, z ∉ bad ∧ ∀ i j, z ∉ Submodule.span K {y i,y j} := by
  classical
  let avoid : Unit ⊕ (I × I) → Submodule K E := Sum.elim (fun _ => bad)
    (fun t => Submodule.span K {y t.1,y t.2})
  have small (t : Unit ⊕ (I × I)) : avoid t ≠ ⊤ := by
    rcases t with u | ⟨i,j⟩
    · exact proper
    · apply (span_lt_top_of_card_lt_finrank (s:={y i,y j}) ?_).ne
      have two : ({y i,y j} : Set E).toFinset.card ≤ 2 := by
        rw [Set.toFinset_insert,Set.toFinset_singleton]
        exact Finset.card_le_two
      omega
  obtain ⟨z,away⟩ := Submodule.exists_forall_notMem_of_forall_ne_top avoid small
  exact ⟨z,away (.inl ()),fun i j => away (.inr (i,j))⟩

/-- Avoiding the spans of pairs preserves all the distinct nonzero marked
lines after projection modulo the prescribed vector `z`. -/
theorem projected_lines {K E I : Type*} [Field K] [AddCommGroup E] [Module K E]
    (z : E) (y : I → E) (nonzero : ∀ i, y i ≠ 0)
    (distinct : ∀ i j, i≠j → y i ∉ Submodule.span K {y j})
    (planes : ∀ i j, z ∉ Submodule.span K {y i,y j}) :
    (∀ i, y i ∉ Submodule.span K {z}) ∧ (∀ i p, i≠p → y i ∉ Submodule.span K {z,y p}) := by
  have off (i : I) : y i ∉ Submodule.span K {z} := by
    intro mem
    obtain ⟨a,eq⟩ := Submodule.mem_span_singleton.mp mem
    by_cases zero : a=0
    · exact nonzero i (by simpa only [zero,zero_smul] using eq.symm)
    · apply planes i i
      apply (Submodule.smul_mem_iff _ zero).mp
      rw [eq]
      exact Submodule.subset_span (Set.mem_insert _ _)
  have apart (i p : I) (hi : i≠p) : y i ∉ Submodule.span K {z,y p} := by
    intro mem
    obtain ⟨a,b,eq⟩ := Submodule.mem_span_pair.mp mem
    by_cases zero : a=0
    · apply distinct i p hi
      exact Submodule.mem_span_singleton.mpr ⟨b,by simpa only [zero,zero_smul,zero_add] using eq⟩
    · let W := Submodule.span K {y i,y p}
      have first : y i ∈ W := Submodule.subset_span (Set.mem_insert _ _)
      have last : y p ∈ W := Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have az : a • z = y i-b • y p := eq_sub_of_add_eq eq
      have inside : a • z ∈ W := az ▸ W.sub_mem first (W.smul_mem b last)
      exact planes i p ((W.smul_mem_iff zero).mp inside)
  exact ⟨off,apart⟩

/-- Every nonzero array can be detected with a functional annihilating a
previously chosen `z` outside the pair spans. -/
theorem reciprocal_of_avoids_pairs {K E I : Type*} [Field K] [Infinite K] [AddCommGroup E]
    [Module K E] [Fintype I] (z : E) (y : I → E) (nonzero : ∀ i, y i ≠ 0)
    (distinct : ∀ i j, i≠j → y i ∉ Submodule.span K {y j})
    (planes : ∀ i j, z ∉ Submodule.span K {y i,y j}) (v : I → K) (hv : v≠0) :
    ∃ f : Dual K E, f z=0 ∧ (∀ i, f (y i) ≠ 0) ∧ (∑ i, v i/f (y i)) ≠ 0 := by
  obtain ⟨off,apart⟩ := projected_lines z y nonzero distinct planes
  obtain ⟨p,vp⟩ : ∃ p, v p ≠ 0 := by
    by_contra! all
    exact hv (funext all)
  exact reciprocal_at_z z y v p vp off (fun i hi => apart i p hi)

/-- The same `z` works for every nonzero coefficient array. The annihilating
functional may depend on that array. -/
theorem exists_z_reciprocal {K E I : Type*} [Field K] [Infinite K] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] [Fintype I] (dim : 3 ≤ finrank K E)
    (y : I → E) (nonzero : ∀ i, y i ≠ 0)
    (distinct : ∀ i j, i≠j → y i ∉ Submodule.span K {y j}) (bad : Submodule K E) (proper : bad≠⊤) :
    ∃ z : E, z ∉ bad ∧ (∀ i j, z ∉ Submodule.span K {y i,y j}) ∧
      ∀ v : I → K, v≠0 → ∃ f : Dual K E, f z=0 ∧ (∀ i, f (y i) ≠ 0) ∧ (∑ i, v i/f (y i)) ≠ 0 := by
  obtain ⟨z,safe,planes⟩ := exists_outside_pairs dim y bad proper
  exact ⟨z,safe,planes,reciprocal_of_avoids_pairs z y nonzero distinct planes⟩

end CriticalLastSlice.Poles

namespace CriticalLastSlice.TwoPlanes

/-- A nonzero tuple of bilinear forms is detected by a one-row tilt that
is transverse to every old marked right line. -/
theorem exists_tilt_detecting {K U V T : Type*} [Field K] [Infinite K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype T]
    (dim : 3 ≤ Module.finrank K V) (y : T → V) (nz : ∀ t, y t≠0)
    (apart : ∀ t s, t≠s → y t ∉ Submodule.span K {y s})
    (F : T → U →ₗ[K] (V →ₗ[K] K)) (nonzero : F≠0) :
    ∃ (u : U) (z : V) (h ell : V →ₗ[K] K), h≠0 ∧ h z=0 ∧ ell z=1 ∧
      (∀ t, h (y t)≠0) ∧ (∑ t, F t u z * ell (y t)/h (y t))≠0 := by
  classical
  obtain ⟨p,hp⟩ : ∃ p, F p ≠ 0 := by
    by_contra! none
    exact nonzero (funext none)
  obtain ⟨u,hu⟩ : ∃ u, F p u ≠ 0 := by
    by_contra! none
    exact hp (LinearMap.ext fun u => none u)
  have proper : (F p u).ker≠⊤ := fun eq => hu (LinearMap.ker_eq_top.mp eq)
  obtain ⟨z,hz,planes⟩ := CriticalLastSlice.Poles.exists_outside_pairs dim y (F p u).ker proper
  have value : F p u z≠0 := fun eq => hz (LinearMap.mem_ker.mpr eq)
  have zne : z≠0 := fun eq => value (by rw [eq,map_zero])
  let two : Fin 2 → V := ![z,y p]
  have exclude (i : Fin 2) : two i ≠ 0 := by
    fin_cases i
    · exact zne
    · exact nz p
  obtain ⟨w,hw⟩ := Module.exists_dual_forall_apply_ne_zero (K:=K) two exclude
  have wz : w z≠0 := hw 0
  have wp : w (y p)≠0 := hw 1
  let ell := (w z)⁻¹ • w
  have unit : ell z=1 := inv_mul_cancel₀ wz
  have ellp : ell (y p)≠0 := mul_ne_zero (inv_ne_zero wz) wp
  let coeff (t : T) := F t u z * ell (y t)
  have not_all : coeff≠0 := fun eq => mul_ne_zero value ellp (congrFun eq p)
  obtain ⟨h,ker,transverse,detected⟩ :=
    CriticalLastSlice.Poles.reciprocal_of_avoids_pairs z y nz apart planes coeff not_all
  have hn : h≠0 := fun eq => transverse p (by rw [eq,LinearMap.zero_apply])
  exact ⟨u,z,h,ell,hn,ker,unit,transverse,detected⟩

/-- Select the tilt, construct its dim(V)−1 new right basis vectors, and
identify the surviving parameters of the old relation space. -/
theorem exists_tilt_decreasing {K U V T D : Type*} [Field K] [Infinite K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup D] [Module K D] [FiniteDimensional K D] [Fintype T]
    (dim : 3 ≤ Module.finrank K V) (y : T → V) (nz : ∀ t, y t≠0)
    (apart : ∀ t s, t≠s → y t ∉ Submodule.span K {y s})
    (F : D →ₗ[K] (T → U →ₗ[K] (V →ₗ[K] K))) (old : ∀ v, ∑ t, F v t=0)
    (active : ∃ v, F v≠0) :
    ∃ (u : U) (z : V) (h ell : V →ₗ[K] K), h≠0 ∧ h z=0 ∧ ell z=1 ∧
      (∀ t, h (y t)≠0) ∧
      (∃ (B : Module.Basis (Fin (Module.finrank K V - 1)) K h.ker)
         (j₀ : Fin (Module.finrank K V - 1)),
         (B j₀ : V)=z ∧ ∀ j, ell (B j : V)=if j=j₀ then 1 else 0) ∧
      ∃ R : Submodule K D, (∀ v, v ∈ R ↔
        (∑ t, ((-(F v t u z)) • ell + (F v t u z*ell (y t)/h (y t)) • h))=0) ∧
        Module.finrank K R + 1 = Module.finrank K D := by
  obtain ⟨v,hv⟩ := active
  obtain ⟨u,z,h,ell,hh,hz,unit,transverse,witness⟩ := exists_tilt_detecting dim y nz apart (F v) hv
  obtain ⟨B,j₀,first,other⟩ := tilted_adapted_basis h ell hh z hz unit
  obtain ⟨R,survives,count⟩ := tilted_relation_rank_step h ell hh u z y F old ⟨v,witness⟩
  exact ⟨u,z,h,ell,hh,hz,unit,transverse,⟨B,j₀,first,other⟩,R,survives,count⟩

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- Varying the old normal tuple linearly varies its canonical tilted
extension. Restriction to the old coordinates recovers the original map. -/
theorem tilted_linear_lift {K U V T D : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup D] [Module K D]
    (F : D →ₗ[K] (T → U →ₗ[K] (V →ₗ[K] K))) (inj : Function.Injective F)
    (h ell : V →ₗ[K] K) (u : U) (z : V) (y : T → V) :
    let row (d : D) (t : T) := (-(F d t u z)) • ell + (F d t u z*ell (y t)/h (y t)) • h
    ∃ H : D →ₗ[K] (T → (U × K) →ₗ[K] (V →ₗ[K] K)), Function.Injective H ∧
      ∀ d t p, H d t p = F d t p.1 + p.2 • row d t := by
  intro row
  choose L act using fun (d : D) (t : T) => tilted_form_exists (F d t) (row d t)
  let H : D →ₗ[K] (T → (U × K) →ₗ[K] (V →ₗ[K] K)) := {
    toFun := L
    map_add' := by
      intro a b
      funext t
      apply LinearMap.ext
      intro p
      apply LinearMap.ext
      intro v
      change L (a+b) t p v = L a t p v + L b t p v
      rw [act,act,act]
      simp only [row,map_add,Pi.add_apply,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
        div_eq_mul_inv]
      ring
    map_smul' := by
      intro c a
      funext t
      apply LinearMap.ext
      intro p
      apply LinearMap.ext
      intro v
      change L (c • a) t p v = c * L a t p v
      rw [act,act]
      simp only [row,map_smul,Pi.smul_apply,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
        div_eq_mul_inv]
      ring }
  refine ⟨H,?_,act⟩
  intro a b eq
  apply inj
  funext t
  apply LinearMap.ext
  intro x
  have result := congrArg (fun W : T → (U × K) →ₗ[K] (V →ₗ[K] K) => W t (x,0)) eq
  change L a t (x,0) = L b t (x,0) at result
  simpa only [act,zero_smul,add_zero] using result

/-- A convenient version of the normal test for the genuine enlarged
bilinear form rather than its two coordinate evaluations. -/
theorem tilted_actual_normal_iff {K U V I J : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [DecidableEq J]
    (x : I → U) (y : I → V) (t : I) (h ell : V →ₗ[K] K) (B : Module.Basis J K h.ker)
    (j₀ : J) (dual : ∀ j, ell (B j : V) = if j=j₀ then 1 else 0)
    (hy : h (y t) ≠ 0) (u : U) (F : U →ₗ[K] (V →ₗ[K] K)) (g : V →ₗ[K] K)
    (L : (U × K) →ₗ[K] (V →ₗ[K] K)) (split : ∀ p, L p=F p.1+p.2 • g) :
    let X : I ⊕ J → U × K := Sum.elim (fun i => (x i,0)) (fun j => ((if j=j₀ then u else 0),1))
    let Y : I ⊕ J → V := Sum.elim y (fun j => (B j : V))
    ((∀ i, L (X i) (Y i) = 0) ∧ (∀ p, L p (y t) = 0) ∧ (∀ v, L (x t,0) v = 0)) ↔
      (∀ i, F (x i) (y i) = 0) ∧ (∀ p, F p (y t) = 0) ∧ (∀ v, F (x t) v = 0) ∧
      g = (-(F u (B j₀ : V))) • ell + (F u (B j₀ : V)*ell (y t)/h (y t)) • h := by
  simpa only [split,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] using
    tilted_normal_iff x y t h ell B j₀ dual hy u F g

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- The row lift with the exact new sample set. The range of the
returned injective map is precisely the new space of relations. -/
theorem tilted_iterable_step {K U V I T D : Type*} [Field K] [Infinite K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup D] [Module K D] [FiniteDimensional K D] [Fintype T]
    (dim : 3 ≤ Module.finrank K V) (x : I → U) (y : I → V) (mark : T → I)
    (nz : ∀ t, y (mark t)≠0) (apart : ∀ t s, t≠s → y (mark t) ∉ Submodule.span K {y (mark s)})
    (F : D →ₗ[K] (T → U →ₗ[K] (V →ₗ[K] K))) (inj : Function.Injective F)
    (complete : ∀ f : T → U →ₗ[K] (V →ₗ[K] K),
      ((∀ t i, f t (x i) (y i)=0) ∧ (∀ t p, f t p (y (mark t))=0) ∧
       (∀ t v, f t (x (mark t)) v=0) ∧ (∑ t, f t)=0) ↔ ∃ d, F d=f)
    (active : ∃ d, F d≠0) :
    ∃ (X : I ⊕ Fin (Module.finrank K V-1) → U × K) (Y : I ⊕ Fin (Module.finrank K V-1) → V)
      (R : Submodule K D) (H : R →ₗ[K] (T → (U × K) →ₗ[K] (V →ₗ[K] K))),
      (∀ i, X (.inl i)=(x i,0)) ∧ (∀ i, Y (.inl i)=y i) ∧
      Module.finrank K R + 1 = Module.finrank K D ∧ Function.Injective H ∧
      ∀ G : T → (U × K) →ₗ[K] (V →ₗ[K] K),
        ((∀ t i, G t (X i) (Y i)=0) ∧ (∀ t p, G t p (Y (.inl (mark t)))=0) ∧
         (∀ t v, G t (X (.inl (mark t))) v=0) ∧ (∑ t, G t)=0) ↔ ∃ d, H d=G := by
  classical
  have old d := (complete (F d)).mpr ⟨d,rfl⟩
  obtain ⟨u,z,h,ell,_,_,_,hy,⟨B,j₀,hz,dual⟩,R,survives,count⟩ :=
    exists_tilt_decreasing dim (fun t => y (mark t)) nz apart F (fun d => (old d).2.2.2) active
  let X : I ⊕ Fin (Module.finrank K V-1) → U × K :=
    Sum.elim (fun i => (x i,0)) (fun j => ((if j=j₀ then u else 0),1))
  let Y : I ⊕ Fin (Module.finrank K V-1) → V := Sum.elim y (fun j => (B j : V))
  let row (d : D) (t : T) := (-(F d t u z)) • ell + (F d t u z*ell (y (mark t))/h (y (mark t))) • h
  obtain ⟨H,hH,lift⟩ := tilted_linear_lift F inj h ell u z (fun t => y (mark t))
  have lift' (d : D) (t : T) (p : U × K) : H d t p = F d t p.1 + p.2 • row d t := lift d t p
  have norms (t : T) (f : U →ₗ[K] (V →ₗ[K] K)) (g : V →ₗ[K] K)
      (G : (U × K) →ₗ[K] (V →ₗ[K] K)) (sp : ∀ p, G p=f p.1+p.2 • g) :
      ((∀ i, G (X i) (Y i)=0) ∧ (∀ p, G p (y (mark t))=0) ∧ (∀ v, G (x (mark t),0) v=0)) ↔
        (∀ i, f (x i) (y i)=0) ∧ (∀ p, f p (y (mark t))=0) ∧ (∀ v, f (x (mark t)) v=0) ∧
        g=(-(f u z)) • ell + (f u z*ell (y (mark t))/h (y (mark t))) • h := by
    simpa only [X,Y,hz] using tilted_actual_normal_iff x y (mark t) h ell B j₀ dual (hy t) u f g G sp
  refine ⟨X,Y,R,H.comp R.subtype,fun _ => rfl,fun _ => rfl,count,hH.comp Subtype.val_injective,?_⟩
  intro G
  constructor
  · rintro ⟨points,left,right,total⟩
    let f (t : T) := (G t).comp (LinearMap.inl K U K)
    let g (t : T) := G t (0,1)
    have sp (t : T) (p : U × K) : G t p = f t p.1+p.2 • g t :=
      tilted_form_decompose (G t) p.1 p.2
    have facts (t : T) := (norms t (f t) (g t) (G t) (sp t)).mp ⟨points t,left t,right t⟩
    have splitSum : (∑ t, f t)=0 ∧ (∑ t, g t)=0 := by
      simpa only [one_smul] using (tilted_sum_forms G f g (fun _ => 1) sp).mp (by simpa only [one_smul] using total)
    obtain ⟨d,hd⟩ := (complete f).mp
      ⟨fun t => (facts t).1,fun t => (facts t).2.1,fun t => (facts t).2.2.1,splitSum.1⟩
    have hg (t : T) : g t=row d t := by
      dsimp only [row]
      rw [hd]
      exact (facts t).2.2.2
    have hr : d ∈ R := (survives d).mpr (by simpa only [← show (fun t => row d t) = g from funext (fun t => (hg t).symm)] using splitSum.2)
    refine ⟨⟨d,hr⟩,?_⟩
    funext t
    apply LinearMap.ext
    intro p
    change H d t p=G t p
    rw [lift',sp,hd,hg]
  · rintro ⟨d,rfl⟩
    have good := old d.val
    have fs (t : T) := (norms t (F d.val t) (row d.val t) (H d.val t) (lift' d.val t)).mpr
      ⟨good.1 t,good.2.1 t,good.2.2.1 t,rfl⟩
    refine ⟨fun t => (fs t).1,fun t => (fs t).2.1,fun t => (fs t).2.2,?_⟩
    change (∑ t, H d.val t)=0
    have both : (∑ t, F d.val t)=0 ∧ (∑ t, row d.val t)=0 := ⟨good.2.2.2,(survives d.val).mp d.property⟩
    simpa only [one_smul] using (tilted_sum_forms (H d.val) (F d.val) (row d.val) (fun _ => 1) (lift' d.val)).mpr
      (by simpa only [one_smul] using both)

end CriticalLastSlice.TwoPlanes

namespace CriticalLastSlice.TwoPlanes

/-- A direct collection of marked normals stays direct after adjoining one
un-tilted row and a basis of a hyperplane transverse to every marked right
vector. This allows padding after the relation dimension reaches zero. -/
theorem tilted_padding_zero {K U V I T : Type*} [Field K] [Infinite K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype T]
    (dim : 3 ≤ Module.finrank K V) (x : I → U) (y : I → V) (mark : T → I) (nz : ∀ t, y (mark t)≠0)
    (direct : ∀ f : T → U →ₗ[K] (V →ₗ[K] K),
      (∀ t i, f t (x i) (y i)=0) → (∀ t p, f t p (y (mark t))=0) →
      (∀ t v, f t (x (mark t)) v=0) → (∑ t, f t)=0 → f=0) :
    ∃ (X : I ⊕ Fin (Module.finrank K V-1) → U × K) (Y : I ⊕ Fin (Module.finrank K V-1) → V),
      (∀ i, X (.inl i)=(x i,0)) ∧ (∀ i, Y (.inl i)=y i) ∧
      ∀ G : T → (U × K) →ₗ[K] (V →ₗ[K] K),
        (∀ t i, G t (X i) (Y i)=0) → (∀ t p, G t p (Y (.inl (mark t)))=0) →
        (∀ t v, G t (X (.inl (mark t))) v=0) → (∑ t, G t)=0 → G=0 := by
  classical
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos (R:=K) (by omega)
  obtain ⟨p,hp⟩ := exists_ne (0 : V)
  let pts : Option T → V := fun j => j.elim p (fun t => y (mark t))
  have unique (j : Option T) : pts j ≠ 0 := by cases j with | none => exact hp | some t => exact nz t
  obtain ⟨h,all⟩ := Module.exists_dual_forall_apply_ne_zero (K:=K) pts unique
  have hh : h ≠ 0 := fun zero => all .none (by rw [zero,LinearMap.zero_apply])
  have regular (t : T) : h (y (mark t))≠0 := all (.some t)
  have rank := Module.Dual.finrank_ker_add_one_of_ne_zero hh
  let B := (Module.finBasis K h.ker).reindex (finCongr (show Module.finrank K h.ker = Module.finrank K V-1 by omega))
  let X : I ⊕ Fin (Module.finrank K V-1) → U × K := Sum.elim (fun i => (x i,0)) (fun _ => (0,1))
  let Y : I ⊕ Fin (Module.finrank K V-1) → V := Sum.elim y (fun j => (B j : V))
  refine ⟨X,Y,fun _ => rfl,fun _ => rfl,?_⟩
  intro G products left right total
  let f (t : T) := (G t).comp (LinearMap.inl K U K)
  let g (t : T) := G t (0,1)
  have sp (t : T) (p : U × K) : G t p = f t p.1 + p.2 • g t := tilted_form_decompose (G t) p.1 p.2
  have both : (∑ t, f t)=0 ∧ (∑ t, g t)=0 := by
    simpa only [one_smul] using (tilted_sum_forms G f g (fun _ => 1) sp).mp (by simpa only [one_smul] using total)
  have hf := direct f (fun t i => products t (.inl i)) (fun t p => left t (p,0))
    (fun t v => right t v) both.1
  have hg (t : T) : g t=0 := by
    have eq := (tilted_row_iff h h (g t) B (y (mark t)) (regular t) 0).mp
      ⟨left t (0,1),fun j => by simpa only [neg_zero,zero_mul,g,X,Y,Sum.elim_inr] using products t (.inr j)⟩
    simpa only [neg_zero,zero_smul,zero_mul,zero_div,add_zero] using eq
  funext t
  apply LinearMap.ext
  intro p
  rw [sp,hg,hf]
  simp

/-- A row may always be added. At positive relation dimension it removes
one dimension; at zero it preserves directness. -/
theorem tilted_iterable_step_any {K U V I T D : Type*} [Field K] [Infinite K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup D] [Module K D] [FiniteDimensional K D] [Fintype T]
    (dim : 3 ≤ Module.finrank K V) (x : I → U) (y : I → V) (mark : T → I)
    (nz : ∀ t, y (mark t)≠0) (apart : ∀ t s, t≠s → y (mark t) ∉ Submodule.span K {y (mark s)})
    (F : D →ₗ[K] (T → U →ₗ[K] (V →ₗ[K] K))) (inj : Function.Injective F)
    (complete : ∀ f : T → U →ₗ[K] (V →ₗ[K] K),
      ((∀ t i, f t (x i) (y i)=0) ∧ (∀ t p, f t p (y (mark t))=0) ∧
       (∀ t v, f t (x (mark t)) v=0) ∧ (∑ t, f t)=0) ↔ ∃ d, F d=f) :
    ∃ (X : I ⊕ Fin (Module.finrank K V-1) → U × K) (Y : I ⊕ Fin (Module.finrank K V-1) → V)
      (R : Submodule K D) (H : R →ₗ[K] (T → (U × K) →ₗ[K] (V →ₗ[K] K))),
      (∀ i, X (.inl i)=(x i,0)) ∧ (∀ i, Y (.inl i)=y i) ∧
      Module.finrank K R = Module.finrank K D - 1 ∧ Function.Injective H ∧
      ∀ G : T → (U × K) →ₗ[K] (V →ₗ[K] K),
        ((∀ t i, G t (X i) (Y i)=0) ∧ (∀ t p, G t p (Y (.inl (mark t)))=0) ∧
         (∀ t v, G t (X (.inl (mark t))) v=0) ∧ (∑ t, G t)=0) ↔ ∃ d, H d=G := by
  classical
  by_cases active : ∃ d, F d≠0
  · obtain ⟨X,Y,R,H,hx,hy,rank,inj',complete'⟩ := tilted_iterable_step dim x y mark nz apart F inj complete active
    exact ⟨X,Y,R,H,hx,hy,by omega,inj',complete'⟩
  push Not at active
  have : Subsingleton D := ⟨fun i j => inj ((active i).trans (active j).symm)⟩
  have oldzero (f : T → U →ₗ[K] (V →ₗ[K] K)) (points : ∀ t i, f t (x i) (y i)=0)
      (left : ∀ t p, f t p (y (mark t))=0) (right : ∀ t v, f t (x (mark t)) v=0)
      (sum : (∑ t, f t)=0) : f=0 := by
    obtain ⟨d,hd⟩ := (complete f).mp ⟨points,left,right,sum⟩
    exact hd.symm.trans (active d)
  obtain ⟨X,Y,hx,hy,none⟩ := tilted_padding_zero dim x y mark nz oldzero
  refine ⟨X,Y,⊥,0,hx,hy,?_,fun a b _ => Subsingleton.elim a b,?_⟩
  · simp only [Module.finrank_zero_of_subsingleton,Nat.zero_sub]
  · intro G
    constructor
    · rintro ⟨pts,lr,rr,ss⟩
      exact ⟨0,(none G pts lr rr ss).symm⟩
    · rintro ⟨d,rfl⟩
      simp

end CriticalLastSlice.TwoPlanes

namespace CriticalExtreme

/-- The coordinate array of a bilinear form and the form evaluate identically
on arbitrary vectors in the two finite coordinate spaces. -/
theorem coordinate_form {A B : Type*} [Fintype A] [Fintype B] :
    ∃ E : (A×B→ℂ) ≃ₗ[ℂ] ((A→ℂ) →ₗ[ℂ] ((B→ℂ) →ₗ[ℂ] ℂ)),
      ∀ H x y,E H x y=∑ ij,(x ij.1*y ij.2)*H ij := by
  classical
  let curry : (A×B→ℂ) ≃ₗ[ℂ] Matrix A B ℂ :=
    { toFun := fun H => Matrix.of fun i j => H (i,j)
      invFun := fun M p => M p.1 p.2
      left_inv := fun H => funext (fun ⟨_,_⟩ => rfl)
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let E := curry.trans (Matrix.toLinearMap₂' ℂ (S₁:=ℂ) (S₂:=ℂ))
  refine ⟨E,?_⟩
  intro H x y
  change Matrix.toLinearMap₂' ℂ (curry H) x y=_
  rw [Matrix.toLinearMap₂'_apply,Fintype.sum_prod_type]
  simp only [smul_eq_mul,mul_assoc]
  rfl

/-- The raw sample, left, right and total constraints are exactly the
four bilinear-form relations used in the iterable tilt. -/
theorem coordinate_relations {A B T I : Type*} [Fintype A] [Fintype B] [Fintype T]
    (E : (A×B→ℂ) ≃ₗ[ℂ] ((A→ℂ) →ₗ[ℂ] ((B→ℂ) →ₗ[ℂ] ℂ)))
    (eval : ∀ H x y,E H x y=∑ ij,(x ij.1*y ij.2)*H ij)
    (x : I→A→ℂ) (y : I→B→ℂ) (first : T→I) (H : T→A×B→ℂ) :
    ((∀ t s,(∑ ij,(x s ij.1*y s ij.2)*H t ij)=0) ∧
     (∀ t i,(∑ j,y (first t) j*H t (i,j))=0) ∧
     (∀ t j,(∑ i,x (first t) i*H t (i,j))=0) ∧ (∑ t,H t)=0) ↔
    ((∀ t s,E (H t) (x s) (y s)=0) ∧
     (∀ t p,E (H t) p (y (first t))=0) ∧
     (∀ t v,E (H t) (x (first t)) v=0) ∧ (∑ t,E (H t))=0) := by
  classical
  have rowEval (t : T) (p : A→ℂ) :
      E (H t) p (y (first t))=∑ i,p i*(∑ j,y (first t) j*H t (i,j)) := by
    rw [eval,Fintype.sum_prod_type]
    simp only [Finset.mul_sum,mul_assoc]
  have colEval (t : T) (v : B→ℂ) :
      E (H t) (x (first t)) v=∑ j,v j*(∑ i,x (first t) i*H t (i,j)) := by
    rw [eval,Fintype.sum_prod_type,Finset.sum_comm]
    simp only [Finset.mul_sum,mul_assoc,mul_left_comm]
  constructor
  · rintro ⟨prod,row,col,tot⟩
    exact ⟨fun t s => (eval _ _ _).trans (prod t s),
      (fun t p => by rw [rowEval];simp [row]),(fun t v => by rw [colEval];simp [col]),
      (by rw [← map_sum,tot,map_zero])⟩
  · rintro ⟨prod,row,col,tot⟩
    refine ⟨fun t s => (eval _ _ _).symm.trans (prod t s),?_,?_,?_⟩
    · intro t i
      have z := row t (Pi.single i 1)
      rw [rowEval] at z
      simpa [Pi.single_apply,ite_mul] using z
    · intro t j
      have z := col t (Pi.single j 1)
      rw [colEval] at z
      simpa [Pi.single_apply,ite_mul] using z
    · apply E.injective
      simpa only [map_sum,map_zero] using tot

end CriticalExtreme

namespace CriticalExtreme

/-- A space of old relations of dimension at most one has an independent
tilted marking after the dimension drop. -/
private theorem tilt_small_space {U V I T D : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup D] [Module ℂ D]
    [FiniteDimensional ℂ D] [Fintype T] (dim : 3≤Module.finrank ℂ V)
    (x : I→U) (y : I→V) (first : T→I) (nz : ∀ t,y (first t)≠0)
    (apart : ∀ t s,t≠s → y (first t)∉Submodule.span ℂ {y (first s)})
    (F : D →ₗ[ℂ] (T → U →ₗ[ℂ] (V →ₗ[ℂ] ℂ))) (inj : Function.Injective F)
    (rank : Module.finrank ℂ D≤1)
    (complete : ∀ f : T → U →ₗ[ℂ] (V →ₗ[ℂ] ℂ),
      ((∀ t i,f t (x i) (y i)=0) ∧ (∀ t p,f t p (y (first t))=0) ∧
       (∀ t v,f t (x (first t)) v=0) ∧ (∑ t,f t)=0) ↔ ∃ d,F d=f) :
    ∃ X : I ⊕ Fin (Module.finrank ℂ V-1) → U × ℂ,
    ∃ Y : I ⊕ Fin (Module.finrank ℂ V-1) → V,
      (∀ i,X (.inl i)=(x i,0)) ∧ (∀ i,Y (.inl i)=y i) ∧
      ∀ G : T → (U × ℂ) →ₗ[ℂ] (V →ₗ[ℂ] ℂ),
        (∀ t i,G t (X i) (Y i)=0) → (∀ t p,G t p (Y (.inl (first t)))=0) →
        (∀ t v,G t (X (.inl (first t))) v=0) → (∑ t,G t)=0 → G=0 := by
  obtain ⟨X,Y,R,H,hx,hy,count,_,exactR⟩ := CriticalLastSlice.TwoPlanes.tilted_iterable_step_any
    dim x y first nz apart F inj complete
  have r0 : Module.finrank ℂ R=0 := by omega
  have trivialR : Subsingleton R := (Module.finrank_zero_iff (R:=ℂ) (M:=↥R)).mp r0
  refine ⟨X,Y,hx,hy,?_⟩
  intro G p l r s
  obtain ⟨d,e⟩ := (exactR G).mp ⟨p,l,r,s⟩
  rw [← e,show d=0 from @Subsingleton.elim R trivialR d 0,map_zero]

/-- A scalar observation that detects all old relations bounds their
dimension by one. The iterable tilt therefore gives directness after one
row increase, including when the old family was already direct. -/
theorem tilt_of_pinned_relation {U V I T : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ U] [FiniteDimensional ℂ V] [Fintype T]
    (dim : 3 ≤ Module.finrank ℂ V) (x : I→U) (y : I→V) (first : T→I)
    (nz : ∀ t,y (first t)≠0)
    (apart : ∀ t s,t≠s → y (first t)∉Submodule.span ℂ {y (first s)})
    (pin : (T → U →ₗ[ℂ] (V →ₗ[ℂ] ℂ)) →ₗ[ℂ] ℂ)
    (detect : ∀ F : T → U →ₗ[ℂ] (V →ₗ[ℂ] ℂ),
      (∀ t i,F t (x i) (y i)=0) → (∀ t p,F t p (y (first t))=0) →
      (∀ t v,F t (x (first t)) v=0) → (∑ t,F t)=0 → pin F=0 → F=0) :
    ∃ X : I ⊕ Fin (Module.finrank ℂ V-1) → U × ℂ,
    ∃ Y : I ⊕ Fin (Module.finrank ℂ V-1) → V,
      (∀ i,X (.inl i)=(x i,0)) ∧ (∀ i,Y (.inl i)=y i) ∧
      ∀ G : T → (U × ℂ) →ₗ[ℂ] (V →ₗ[ℂ] ℂ),
        (∀ t i,G t (X i) (Y i)=0) → (∀ t p,G t p (Y (.inl (first t)))=0) →
        (∀ t v,G t (X (.inl (first t))) v=0) → (∑ t,G t)=0 → G=0 := by
  classical
  let D : Submodule ℂ (T → U →ₗ[ℂ] (V →ₗ[ℂ] ℂ)) :=
    { carrier := {F | (∀ t i,F t (x i) (y i)=0) ∧ (∀ t p,F t p (y (first t))=0) ∧
          (∀ t v,F t (x (first t)) v=0) ∧ (∑ t,F t)=0}
      zero_mem' := by simp
      add_mem' := by
        rintro f g ⟨fp,fl,fr,fs⟩ ⟨gp,gl,gr,gs⟩
        exact ⟨(fun t i => by change f t (x i) (y i)+g t (x i) (y i)=0; rw [fp,gp,add_zero]),
          (fun t p => by change f t p (y (first t))+g t p (y (first t))=0;rw [fl,gl,add_zero]),
          (fun t v => by change f t (x (first t)) v+g t (x (first t)) v=0;rw [fr,gr,add_zero]),
          (by change (∑ t,(f t+g t))=0; rw [Finset.sum_add_distrib,fs,gs,add_zero])⟩
      smul_mem' := by
        rintro c f ⟨fp,fl,fr,fs⟩
        exact ⟨(fun t i => by change c*(f t (x i) (y i))=0;rw [fp,mul_zero]),
          (fun t p => by change c*(f t p (y (first t)))=0;rw [fl,mul_zero]),
          (fun t v => by change c*(f t (x (first t)) v)=0;rw [fr,mul_zero]),
          (by change (∑ t,c • f t)=0; rw [← Finset.smul_sum,fs,smul_zero])⟩ }
  have inj : Function.Injective (pin.comp D.subtype) := by
    intro f g eq
    change pin f.val=pin g.val at eq
    have z : pin (f-g).val=0 := by change pin (f.val-g.val)=0;rw [map_sub,eq,sub_self]
    obtain ⟨p,l,r,s⟩ := (f-g).property
    have dz : f-g=0 := Subtype.ext (detect (f-g).val p l r s z)
    exact sub_eq_zero.mp dz
  have small : Module.finrank ℂ D ≤ 1 := by
    simpa only [Module.finrank_self] using LinearMap.finrank_le_finrank_of_injective inj
  have complete (f : T → U →ₗ[ℂ] (V →ₗ[ℂ] ℂ)) : ((∀ t i,f t (x i) (y i)=0) ∧ (∀ t p,f t p (y (first t))=0) ∧
      (∀ t v,f t (x (first t)) v=0) ∧ (∑ t,f t)=0) ↔ ∃ d : D,D.subtype d=f :=
    ⟨fun hf => ⟨⟨f,hf⟩,rfl⟩,fun ⟨d,e⟩ => e ▸ d.property⟩
  have into : Function.Injective D.subtype := fun _ _ e => Subtype.ext e
  exact tilt_small_space (D:=↥D) dim x y first nz apart D.subtype into small complete

end CriticalExtreme

namespace CriticalExtreme

/-- A scalar pin on the old (a−1)-by-a coordinates gives a square batch
of 2a−1 marks on (a−1)² samples. The marked first factors stay separated. -/
theorem square_of_pinned (a : ℕ) (ha : 5≤a) :
    let p := (a-2)*(a-1)
    let m := 2*a-1
    ∀ first : Fin m ↪ Fin p, ∀ x : Fin p→Fin (a-1)→ℂ, ∀ y : Fin p→Fin a→ℂ,
    ∀ t₀ : Fin m, ∀ ij₀ : Fin (a-1) × Fin a,
      (∀ t,x (first t)≠0) → (∀ t s,t≠s → ∀ c : ℂ,x (first t)≠c • x (first s)) →
      (∀ t,y (first t)≠0) → (∀ t s,t≠s → ∀ c : ℂ,y (first t)≠c • y (first s)) →
      (∀ H : Fin m→Fin (a-1) × Fin a→ℂ,
        (∀ t s,(∑ ij,(x s ij.1*y s ij.2)*H t ij)=0) →
        (∀ t i,(∑ j,y (first t) j*H t (i,j))=0) →
        (∀ t j,(∑ i,x (first t) i*H t (i,j))=0) → (∑ t,H t)=0 → H t₀ ij₀=0 → H=0) →
      ∃ newMark : Fin m ↪ Fin ((a-1)*(a-1)), ∃ X : Fin ((a-1)*(a-1))→Fin a→ℂ,
      ∃ Y : Fin ((a-1)*(a-1))→Fin a→ℂ,
        (∀ H : Fin m→Fin a × Fin a→ℂ,
          (∀ t s,(∑ ij,(X s ij.1*Y s ij.2)*H t ij)=0) →
          (∀ t i,(∑ j,Y (newMark t) j*H t (i,j))=0) →
          (∀ t j,(∑ i,X (newMark t) i*H t (i,j))=0) → (∑ t,H t)=0 → H=0) ∧
        (∀ t,X (newMark t)≠0) ∧ (∀ t s,t≠s → ∀ c : ℂ,X (newMark t)≠c • X (newMark s)) := by
  classical
  intro p m first x y t₀ ij₀ xnz xsep ynz ysep pinned
  let U := Fin (a-1)→ℂ
  let V := Fin a→ℂ
  obtain ⟨E,ev⟩ := coordinate_form (A:=Fin (a-1)) (B:=Fin a)
  let pin : (Fin m → U →ₗ[ℂ] (V →ₗ[ℂ] ℂ)) →ₗ[ℂ] ℂ :=
    (LinearMap.proj ij₀).comp (E.symm.toLinearMap.comp (LinearMap.proj t₀))
  have detects (f : Fin m → U →ₗ[ℂ] (V →ₗ[ℂ] ℂ)) (pts : ∀ t i,f t (x i) (y i)=0)
      (lr : ∀ t p,f t p (y (first t))=0) (rr : ∀ t v,f t (x (first t)) v=0)
      (total : (∑ t,f t)=0) (zero : pin f=0) : f=0 := by
    let H (t : Fin m) := E.symm (f t)
    obtain ⟨outer,row,col,sum⟩ := (coordinate_relations E ev x y first H).mpr (by
      simpa only [H,E.apply_symm_apply] using And.intro pts (And.intro lr (And.intro rr total)))
    have all := pinned H outer row col sum zero
    funext t
    change f t=0
    have hv := congrFun all t
    change E.symm (f t)=0 at hv
    exact E.symm.injective (hv.trans (map_zero _).symm)
  have rankV : Module.finrank ℂ V=a := by simp only [V,Module.finrank_fintype_fun_eq_card,Fintype.card_fin]
  have apart (t s : Fin m) (ne : t≠s) : y (first t)∉Submodule.span ℂ {y (first s)} := by
    intro member
    obtain ⟨c,e⟩ := Submodule.mem_span_singleton.mp member
    exact ysep t s ne c e.symm
  obtain ⟨X,Y,hx,_,direct⟩ := tilt_of_pinned_relation
    (by rw [rankV];omega) x y first ynz apart pin detects
  let S := Fin p ⊕ Fin (Module.finrank ℂ V-1)
  have size : p+(Module.finrank ℂ V-1)=(a-1)*(a-1) := by
    rw [rankV]
    dsimp only [p]
    have id := congrArg (fun t : ℕ => t*(a-1)) (show a-2+1=a-1 by omega)
    nlinarith only [id]
  let ep : S ≃ Fin ((a-1)*(a-1)) := finSumFinEquiv.trans (finCongr size)
  have dim : Module.finrank ℂ (U × ℂ)=a := by
    simp only [U,Module.finrank_prod,Module.finrank_fintype_fun_eq_card,Fintype.card_fin,Module.finrank_self]
    omega
  let coord := ((Module.finBasis ℂ (U × ℂ)).reindex (finCongr dim)).equivFun
  let tag : Fin m ↪ Fin ((a-1)*(a-1)) := (first.trans Function.Embedding.inl).trans ep.toEmbedding
  let XX (s : Fin ((a-1)*(a-1))) := coord (X (ep.symm s))
  let YY (s : Fin ((a-1)*(a-1))) := Y (ep.symm s)
  have back (t : Fin m) : ep.symm (tag t)=Sum.inl (first t) := ep.symm_apply_apply _
  refine ⟨tag,XX,YY,?_,?_,?_⟩
  · intro H outer row col sum
    obtain ⟨N,evN⟩ := coordinate_form (A:=Fin a) (B:=Fin a)
    let f (t : Fin m) := N (H t)
    obtain ⟨fpt,fl,fr,ft⟩ := (coordinate_relations N evN XX YY tag H).mp ⟨outer,row,col,sum⟩
    let G (t : Fin m) := (f t).comp coord.toLinearMap
    have zero : G=0 := direct G (by
      intro t i
      simpa only [G,f,XX,YY,LinearMap.comp_apply,LinearEquiv.coe_coe,ep.symm_apply_apply] using fpt t (ep i))
      (by
        intro t q
        simpa only [G,f,YY,LinearMap.comp_apply,LinearEquiv.coe_coe,back] using fl t (coord q))
      (by
        intro t v
        simpa only [G,f,XX,LinearMap.comp_apply,LinearEquiv.coe_coe,back] using fr t v)
      (by
        apply LinearMap.ext
        intro q
        have z := congrArg (fun L : (Fin a→ℂ) →ₗ[ℂ] ((Fin a→ℂ) →ₗ[ℂ] ℂ) => L (coord q)) ft
        simpa only [G,f,LinearMap.sum_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearMap.zero_apply] using z)
    funext t
    change H t=0
    apply N.injective
    rw [map_zero]
    apply LinearMap.ext
    intro p
    have v := congrArg (fun fs : Fin m → (U × ℂ) →ₗ[ℂ] ((Fin a→ℂ) →ₗ[ℂ] ℂ) =>
      fs t (coord.symm p)) zero
    simpa only [G,f,LinearMap.comp_apply,LinearEquiv.coe_coe,coord.apply_symm_apply,
      Pi.zero_apply,LinearMap.zero_apply] using v
  · intro t h
    have pre : X (.inl (first t))=0 := coord.injective ((by simpa only [XX,back] using h : coord (X (.inl (first t)))=0).trans (map_zero _).symm)
    have hfst := congrArg Prod.fst pre
    exact xnz t (by simpa only [hx,Prod.fst_zero] using hfst)
  · intro t s ne c eq
    have pre : coord (X (.inl (first t)))=coord (c • X (.inl (first s))) := by
      simpa only [XX,back,map_smul] using eq
    have hpre := coord.injective pre
    rw [hx,hx] at hpre
    exact xsep t s ne c (congrArg Prod.fst hpre)

end CriticalExtreme

namespace CriticalExtreme

/-- Square batches of size 2a−1 with pairwise distinct marked row lines.
At a=4 use the explicit square witness; larger squares use a pinned tilt. -/
theorem separated_square (a : ℕ) (ha : 4≤a) :
    let m := 2*a-1
    let r := (a-1)*(a-1)
    ∃ first : Fin m ↪ Fin r, ∃ x : Fin r→Fin a→ℂ, ∃ y : Fin r→Fin a→ℂ,
      (∀ H : Fin m→Fin a × Fin a→ℂ,
        (∀ t s,(∑ ij,(x s ij.1*y s ij.2)*H t ij)=0) →
        (∀ t i,(∑ j,y (first t) j*H t (i,j))=0) →
        (∀ t j,(∑ i,x (first t) i*H t (i,j))=0) → (∑ t,H t)=0 → H=0) ∧
      (∀ t,x (first t)≠0) ∧ (∀ t s,t≠s → ∀ c : ℂ,x (first t)≠c • x (first s)) := by
  by_cases four : a=4
  · subst a
    exact four_square_marked
  have large : 5≤a := by omega
  obtain ⟨first,x,y,t₀,ij₀,xnz,xsep,ynz,ysep,pinned⟩ := pinned_core a large
  exact square_of_pinned a large first x y t₀ ij₀ xnz xsep ynz ysep pinned

/-- The extreme rectangle b=3a−2 attains the optimal batch size
(a+b)/2=2a−1 throughout the second normal level. -/
theorem extreme_marked_batch (a : ℕ) (ha : 4≤a) :
    let b := 3*a-2
    let m := 2*a-1
    let r := (a-1)*(b-1)-1
    ∃ first : Fin m ↪ Fin r, ∃ x : Fin r→Fin a→ℂ, ∃ y : Fin r→Fin b→ℂ,
    ∀ H : Fin m→Fin a × Fin b→ℂ,
      (∀ t s,(∑ ij,(x s ij.1*y s ij.2)*H t ij)=0) →
      (∀ t i,(∑ j,y (first t) j*H t (i,j))=0) →
      (∀ t j,(∑ i,x (first t) i*H t (i,j))=0) → (∑ t,H t)=0 → H=0 := by
  obtain ⟨mark,x,y,old,nz,apart⟩ := separated_square a ha
  have noSpan (i j : Fin (2*a-1)) (ne : i≠j) : x (mark i)∉Submodule.span ℂ {x (mark j)} := by
    intro h
    obtain ⟨c,e⟩ := Submodule.mem_span_singleton.mp h
    exact apart i j ne c e.symm
  have done := CriticalLastSlice.TwoPlanes.Cross.split_marked (a:=a) (b:=a) (w:=2*a-2) (m:=2*a-1)
    (by omega) (by omega) (by omega) (by omega) mark x y old nz noSpan
  rwa [show a+(2*a-2)=3*a-2 by omega] at done

end CriticalExtreme

namespace CriticalDoubleTilt

/-- The sampled-product and two marked contraction equations for a normal matrix. -/
def Normal {a b r : ℕ} (x : Fin r → Fin a → ℂ) (y : Fin r → Fin b → ℂ)
    (s : Fin r) (H : Fin a × Fin b → ℂ) : Prop :=
  (∀ t, ∑ ij : Fin a × Fin b,(x t ij.1*y t ij.2)*H ij=0) ∧
    (∀ i, ∑ j,y s j*H (i,j)=0) ∧ (∀ j, ∑ i,x s i*H (i,j)=0)

/-- The normal matrices at the specified ordered marking sum directly. -/
def Direct {a b r k : ℕ} (x : Fin r → Fin a → ℂ) (y : Fin r → Fin b → ℂ)
    (e : Fin k → Fin r) : Prop :=
  ∀ F : Fin k → Fin a × Fin b → ℂ, (∀ i, Normal x y (e i) (F i)) → (∑ i,F i)=0 → F=0

/-- The shared normal is determined by its two prescribed coordinate entries. -/
def Detect {a b r : ℕ} (x : Fin r → Fin a → ℂ) (y : Fin r → Fin b → ℂ)
    (s : Fin r) (uv : Fin 2 → Fin a × Fin b) : Prop :=
  ∀ H, Normal x y s H → (∀ i,H (uv i)=0) → H=0

/-- For paired relations a vanishing shared normal kills both direct batches.
This bounds the entire relation space by two and makes each exclusive
batch separately determine the relation. -/
theorem paired_relation_bounds {a b r k : ℕ} {D : Type*} [AddCommGroup D] [Module ℂ D]
    (x : Fin r → Fin a → ℂ) (y : Fin r → Fin b → ℂ)
    (mark : Fin k ⊕ (Fin k ⊕ Unit) → Fin r) (uv : Fin 2 → Fin a × Fin b)
    (da : Direct x y (fun i => mark (.inl i))) (db : Direct x y (fun i => mark (.inr (.inl i))))
    (shared : Detect x y (mark (.inr (.inr ()))) uv)
    (F : D →ₗ[ℂ] ((Fin k ⊕ (Fin k ⊕ Unit)) → Fin a × Fin b → ℂ)) (inj : Function.Injective F)
    (normal : ∀ d t, Normal x y (mark t) (F d t))
    (left : ∀ d,(∑ i : Fin k,F d (.inl i))+F d (.inr (.inr ()))=0)
    (right : ∀ d,(∑ i : Fin k,F d (.inr (.inl i)))+F d (.inr (.inr ()))=0) :
    Module.finrank ℂ D≤2 ∧ (∀ d,(∀ i : Fin k,F d (.inl i)=0) → d=0) ∧
      (∀ d,(∀ i : Fin k,F d (.inr (.inl i))=0) → d=0) := by
  classical
  have vanish (d : D) (zero : F d (.inr (.inr ()))=0) : d=0 := by
    have l := da (fun i => F d (.inl i)) (fun i => normal _ _) (by simpa only [zero,add_zero] using left d)
    have r := db (fun i => F d (.inr (.inl i))) (fun i => normal _ _) (by simpa only [zero,add_zero] using right d)
    apply inj
    rw [map_zero]
    funext t
    rcases t with i|i|u
    · exact congrFun l i
    · exact congrFun r i
    · cases u
      exact zero
  let readout : D →ₗ[ℂ] (Fin 2 → ℂ) :=
    LinearMap.pi fun i =>
      (LinearMap.proj (uv i)).comp ((LinearMap.proj (.inr (.inr ()))).comp F)
  have hi : Function.Injective readout := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro d eq
    exact vanish d (shared _ (normal _ _) (fun i => congrFun eq i))
  refine ⟨by simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using
    LinearMap.finrank_le_finrank_of_injective hi,?_,?_⟩
  · intro d l
    exact vanish d (by simpa only [l,Finset.sum_const_zero,zero_add] using left d)
  · intro d r
    exact vanish d (by simpa only [r,Finset.sum_const_zero,zero_add] using right d)

end CriticalDoubleTilt

namespace CriticalDoubleTilt

/-- At one selected point, two fixed coordinate readings complete the
normal equations. Mark the top-left coordinate product and sample every
remaining interior cell except the two readout cells. -/
theorem grid_shared_specimen {a b r : ℕ} (s : Fin r) (level : r+1=a*b) :
    ∃ uv : Fin 2 → Fin (a+1) × Fin (b+1),
    ∃ x : Fin r → Fin (a+1) → ℂ, ∃ y : Fin r → Fin (b+1) → ℂ, Detect x y s uv := by
  classical
  let P := {t : Fin r // t≠s}
  have cP : Fintype.card P=r-1 := by
    change Fintype.card {t : Fin r // ¬ t=s}=r-1
    rw [Fintype.card_subtype_compl]
    simp
  have c : Fintype.card (P ⊕ Fin 2)=Fintype.card (Fin a × Fin b) := by
    rw [Fintype.card_sum,Fintype.card_prod,cP,Fintype.card_fin,Fintype.card_fin,Fintype.card_fin]
    have := s.isLt
    omega
  let E : (P ⊕ Fin 2) ≃ (Fin a × Fin b) := Fintype.equivOfCardEq c
  let cell (u : P ⊕ Fin 2) := ((E u).1.succ,(E u).2.succ)
  let ij (t : Fin r) : Fin (a+1) × Fin (b+1) := if h : t=s then (0,0) else cell (.inl ⟨t,h⟩)
  let x (t : Fin r) : Fin (a+1) → ℂ := Pi.single (ij t).1 1
  let y (t : Fin r) : Fin (b+1) → ℂ := Pi.single (ij t).2 1
  refine ⟨fun q => cell (.inr q),x,y,?_⟩
  intro H normal missing
  have sampled (t : Fin r) : H (ij t)=0 := by
    simpa [x,y,Fintype.sum_prod_type,Pi.single_apply,ite_mul,mul_ite] using normal.1 t
  have top (j : Fin (b+1)) : H (0,j)=0 := by
    simpa [x,ij,Pi.single_apply,ite_mul] using normal.2.2 j
  have side (i : Fin (a+1)) : H (i,0)=0 := by
    simpa [y,ij,Pi.single_apply,ite_mul] using normal.2.1 i
  funext z
  obtain ⟨i,j⟩ := z
  change H (i,j)=0
  refine Fin.cases (top j) (fun i => ?_) i
  refine Fin.cases (side i.succ) (fun j => ?_) j
  obtain ⟨u,hu⟩ := E.surjective (i,j)
  cases u with
  | inl t =>
    have ht : ij t.val=cell (.inl t) := dif_neg t.property
    simpa only [ht,cell,hu] using sampled t.val
  | inr q => simpa only [cell,hu] using missing q

end CriticalDoubleTilt

namespace CriticalDoubleTilt

open MvPolynomial

private abbrev Vars (a b r : ℕ) := Fin r × (Fin a ⊕ Fin b)
private abbrev XY {a b r : ℕ} (p : Vars a b r → ℂ) (s : Fin r) (i : Fin a) : ℂ := p (s,.inl i)
private abbrev YY {a b r : ℕ} (p : Vars a b r → ℂ) (s : Fin r) (j : Fin b) : ℂ := p (s,.inr j)
private abbrev DR (a b r k : ℕ) := (Fin k × (Fin r ⊕ (Fin a ⊕ Fin b))) ⊕ (Fin a × Fin b)
private abbrev DC (a b k : ℕ) := Fin k × (Fin a × Fin b)
private abbrev SR (a b r : ℕ) := Fin r ⊕ (Fin a ⊕ (Fin b ⊕ Fin 2))

private noncomputable def dm {a b r k : ℕ} (e : Fin k ↪ Fin r) :
    Matrix (DR a b r k) (DC a b k) (MvPolynomial (Vars a b r) ℂ) := fun row col => row.elim
    (fun te => if col.1=te.1 then te.2.elim
      (fun s => X (s,.inl col.2.1)*X (s,.inr col.2.2))
      (Sum.elim (fun i => if col.2.1=i then X (e te.1,.inr col.2.2) else 0)
        (fun j => if col.2.2=j then X (e te.1,.inl col.2.1) else 0)) else 0)
    (fun ij => if col.2=ij then 1 else 0)

private theorem dm_action {a b r k : ℕ} (e : Fin k ↪ Fin r) (p : Vars a b r → ℂ) :
    Function.Injective (((dm e).map (eval p)).mulVec) ↔ Direct (XY p) (YY p) e := by
  classical
  have h := LastSliceBatch.stack_injective_iff e (XY p) (YY p) ((dm e).map (eval p)) (by
    intro row col
    change eval p (dm e row col) = _
    rcases row with ⟨t,s|i|j⟩|ij <;> rcases col with ⟨l,u,v⟩
    · by_cases ht : l=t <;> simp [dm,ht]
    · by_cases ht : l=t <;> by_cases hi : u=i <;> simp [dm,ht,hi]
    · by_cases ht : l=t <;> by_cases hj : v=j <;> simp [dm,ht,hj]
    · by_cases he : (u,v)=ij <;> simp [dm,he])
  rw [h]
  constructor
  · intro good F normals
    exact good F (fun t => (normals t).1) (fun t => (normals t).2.1) (fun t => (normals t).2.2)
  · intro good F pr rows cols
    exact good F fun t => ⟨pr t,rows t,cols t⟩

private noncomputable def sm {a b r : ℕ} (s : Fin r) (uv : Fin 2 → Fin a × Fin b) :
    Matrix (SR a b r) (Fin a × Fin b) (MvPolynomial (Vars a b r) ℂ) := fun row ij =>
    row.elim (fun t => X (t,.inl ij.1)*X (t,.inr ij.2))
      (Sum.elim (fun i => if ij.1=i then X (s,.inr ij.2) else 0)
        (Sum.elim (fun j => if ij.2=j then X (s,.inl ij.1) else 0)
          (fun c => if ij=uv c then 1 else 0)))

private theorem sm_action {a b r : ℕ} (s : Fin r) (uv : Fin 2 → Fin a × Fin b) (p : Vars a b r → ℂ) :
    Function.Injective (((sm s uv).map (eval p)).mulVec) ↔ Detect (XY p) (YY p) s uv := by
  classical
  let M := (sm s uv).map (eval p)
  have pr (H : Fin a × Fin b → ℂ) (t : Fin r) :
      M.mulVec H (.inl t)=∑ ij : Fin a × Fin b,(XY p t ij.1*YY p t ij.2)*H ij := by
    simp [M,sm,Matrix.mulVec,dotProduct,Matrix.map_apply]
  have rows (H : Fin a × Fin b → ℂ) (i : Fin a) :
      M.mulVec H (.inr (.inl i))=∑ j,YY p s j*H (i,j) := by
    simp [M,sm,Matrix.mulVec,dotProduct,Matrix.map_apply,Fintype.sum_prod_type,apply_ite,ite_mul,
      Finset.sum_ite_eq']
  have cols (H : Fin a × Fin b → ℂ) (j : Fin b) :
      M.mulVec H (.inr (.inr (.inl j)))=∑ i,XY p s i*H (i,j) := by
    simp [M,sm,Matrix.mulVec,dotProduct,Matrix.map_apply,Fintype.sum_prod_type,apply_ite,ite_mul,
      Finset.sum_ite_eq']
  have pin (H : Fin a × Fin b → ℂ) (c : Fin 2) :
      M.mulVec H (.inr (.inr (.inr c)))=H (uv c) := by
    simp [M,sm,Matrix.mulVec,dotProduct,Matrix.map_apply,apply_ite,ite_mul,Finset.sum_ite_eq']
  change Function.Injective M.mulVecLin ↔ _
  rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
  constructor
  · intro detect H normal readout
    apply detect
    funext row
    rcases row with t|i|j|c
    · exact (pr H t).trans (normal.1 t)
    · exact (rows H i).trans (normal.2.1 i)
    · exact (cols H j).trans (normal.2.2 j)
    · exact (pin H c).trans (readout c)
  · intro detect H eq
    exact detect H ⟨fun t => (pr H t).symm.trans (congrFun eq _),
      fun i => (rows H i).symm.trans (congrFun eq _),
      fun j => (cols H j).symm.trans (congrFun eq _)⟩ (fun c => (pin H c).symm.trans (congrFun eq _))

private noncomputable def tm {a b r : ℕ} (e : Fin 3 ↪ Fin r) :
    Matrix (Fin b) (Fin 3) (MvPolynomial (Vars a b r) ℂ) := fun j i => X (e i,.inr j)

private theorem tm_action {a b r : ℕ} (e : Fin 3 ↪ Fin r) (p : Vars a b r → ℂ) :
    Function.Injective (((tm e).map (eval p)).mulVec) ↔ LinearIndependent ℂ (fun i => YY p (e i)) := by
  classical
  let M := (tm e).map (eval p)
  have action (u : Fin 3 → ℂ) : M.mulVec u=∑ i,u i • YY p (e i) := by
    funext j
    simp [M,tm,Matrix.map_apply,Matrix.mulVec,dotProduct,Finset.sum_apply,mul_comm]
  change Function.Injective M.mulVecLin ↔ _
  rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot',Fintype.linearIndependent_iff]
  constructor
  · intro ker u h i
    exact congrFun (ker u ((action u).trans h)) i
  · intro independent u zero
    exact funext fun i => independent u ((action u).symm.trans zero) i

private theorem tm_realized {a b r : ℕ} (hb : 3≤b) (e : Fin 3 ↪ Fin r) :
    ∃ p : Vars a b r → ℂ, Function.Injective (((tm e).map (eval p)).mulVec) := by
  classical
  let axis : Fin 3 ↪ Fin b := Fin.castLEEmb hb
  let w (s : Fin r) (j : Fin b) : ℂ := if ∃ i, e i=s ∧ axis i=j then 1 else 0
  let p (z : Vars a b r) : ℂ := z.2.elim (fun _ => 0) (w z.1)
  have atMark (j i : Fin 3) : YY p (e i) (axis j)=if i=j then 1 else 0 := by
    change w (e i) (axis j) = _
    simp [w]
  refine ⟨p,(tm_action e p).mpr ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro u zero j
  have eq := congrFun zero (axis j)
  simpa [Finset.sum_apply,atMark,mul_ite,Finset.sum_ite_eq'] using eq

end CriticalDoubleTilt

namespace CriticalDoubleTilt

open MvPolynomial

/-- A single complex specialization enforces all ordered direct batches,
the two coordinates detecting the shared normal, and independence of
every ordered triple of second-factor vectors. -/
theorem common_at_coordinates {a b r k : ℕ} (hb : 3≤b) (s : Fin r) (uv : Fin 2 → Fin a × Fin b)
    (first : Fin k ↪ Fin r) (one : ∃ x y, Direct (a:=a) (b:=b) x y first)
    (pin : ∃ x y, Detect x y s uv) :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
      (∀ e : Fin k ↪ Fin r,Direct x y e) ∧ Detect x y s uv ∧
      (∀ e : Fin 3 ↪ Fin r, LinearIndependent ℂ (fun i => y (e i))) := by
  classical
  let G := (Fin k ↪ Fin r) ⊕ (Unit ⊕ (Fin 3 ↪ Fin r))
  let U : G → Type := Sum.elim (fun _ => DR a b r k) (Sum.elim (fun _ => SR a b r) (fun _ => Fin b))
  let W : G → Type := Sum.elim (fun _ => DC a b k) (Sum.elim (fun _ => Fin a × Fin b) (fun _ => Fin 3))
  let _ (g : G) : Fintype (U g) := by rcases g with e|u|e <;> dsimp only [U,Sum.elim_inl,Sum.elim_inr] <;> infer_instance
  let _ (g : G) : Fintype (W g) := by rcases g with e|u|e <;> dsimp only [W,Sum.elim_inl,Sum.elim_inr] <;> infer_instance
  let M (g : G) : Matrix (U g) (W g) (MvPolynomial (Vars a b r) ℂ) := by
    rcases g with e|u|e
    · exact dm e
    · exact sm s uv
    · exact tm e
  have all (g : G) : ∃ p : Vars a b r → ℂ, Function.Injective (((M g).map (eval p)).mulVec) := by
    rcases g with e|u|e
    · obtain ⟨x₀,y₀,direct⟩ := one
      obtain ⟨σ,hσ⟩ := LastSliceBatch.permutation_of_markings e first
      let p (z : Vars a b r) : ℂ := z.2.elim (x₀ (σ z.1)) (y₀ (σ z.1))
      refine ⟨p,(dm_action e p).mpr ?_⟩
      intro F normals
      apply direct F
      intro i
      refine ⟨fun t => ?_,?_,?_⟩
      · obtain ⟨v,rfl⟩ := σ.surjective t
        exact (normals i).1 v
      · simpa only [YY,p,Sum.elim_inr,hσ] using (normals i).2.1
      · simpa only [XY,p,Sum.elim_inl,hσ] using (normals i).2.2
    · obtain ⟨x,y,detect⟩ := pin
      let p (z : Vars a b r) : ℂ := z.2.elim (x z.1) (y z.1)
      exact ⟨p,(sm_action s uv p).mpr detect⟩
    · exact tm_realized hb e
  obtain ⟨p,allgood⟩ := LastSliceBatch.common_injective (U:=U) (W:=W) M all
  exact ⟨XY p,YY p,fun e => (dm_action e p).mp (allgood (.inl e)),
    (sm_action s uv p).mp (allgood (.inr (.inl ()))),
    fun e => (tm_action e p).mp (allgood (.inr (.inr e)))⟩

/-- On the two-normal level every single ordinary specimen gives common
old sampling data for the paired row construction, at any shared point. -/
theorem common_preparation {a b r k : ℕ} (ha : 0<a) (hb : 3≤b) (level : r+1=(a-1)*(b-1))
    (s : Fin r) (first : Fin k ↪ Fin r) (one : ∃ x y, Direct (a:=a) (b:=b) x y first) :
    ∃ uv : Fin 2 → Fin a × Fin b, ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
      (∀ e : Fin k ↪ Fin r, Direct x y e) ∧ Detect x y s uv ∧
      (∀ e : Fin 3 ↪ Fin r, LinearIndependent ℂ (fun i => y (e i))) := by
  obtain ⟨u,rfl⟩ : ∃ u : ℕ,a=u+1 := ⟨a-1,by omega⟩
  obtain ⟨v,rfl⟩ : ∃ v : ℕ,b=v+1 := ⟨b-1,by omega⟩
  obtain ⟨uv,x,y,detect⟩ := grid_shared_specimen s (by simpa only [Nat.add_sub_cancel] using level)
  exact ⟨uv,common_at_coordinates hb s uv first one ⟨x,y,detect⟩⟩

end CriticalDoubleTilt

namespace CriticalDoubleTilt

private theorem normal_zero {a b r : ℕ} (x : Fin r → Fin a → ℂ) (y : Fin r → Fin b → ℂ) (s : Fin r) :
    Normal x y s 0 := by simp [Normal]

private theorem normal_add {a b r : ℕ} {x : Fin r → Fin a → ℂ} {y : Fin r → Fin b → ℂ} {s : Fin r}
    {F G : Fin a × Fin b → ℂ} (f : Normal x y s F) (g : Normal x y s G) : Normal x y s (F+G) := by
  refine ⟨fun t => ?_,fun i => ?_,fun j => ?_⟩
  · simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib,f.1,g.1,zero_add]
  · simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib,f.2.1,g.2.1,zero_add]
  · simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib,f.2.2,g.2.2,zero_add]

private theorem normal_smul {a b r : ℕ} {x : Fin r → Fin a → ℂ} {y : Fin r → Fin b → ℂ} {s : Fin r}
    {F : Fin a × Fin b → ℂ} (z : ℂ) (f : Normal x y s F) : Normal x y s (z • F) := by
  refine ⟨fun t => ?_,fun i => ?_,fun j => ?_⟩
  · simp only [Pi.smul_apply,smul_eq_mul,mul_left_comm _ z,← Finset.mul_sum,f.1,mul_zero]
  · simp only [Pi.smul_apply,smul_eq_mul,mul_left_comm _ z,← Finset.mul_sum,f.2.1,mul_zero]
  · simp only [Pi.smul_apply,smul_eq_mul,mul_left_comm _ z,← Finset.mul_sum,f.2.2,mul_zero]

/-- The old paired relations as an actual finite-dimensional linear subspace.
A member assigns one normal matrix to each marked point. Both exclusive
batch sums equal the negative of its assigned shared matrix. -/
def pairedSpace {a b r k : ℕ} (x : Fin r → Fin a → ℂ) (y : Fin r → Fin b → ℂ)
    (m : Fin k ⊕ (Fin k ⊕ Unit) → Fin r) :
    Submodule ℂ ((Fin k ⊕ (Fin k ⊕ Unit)) → Fin a × Fin b → ℂ) where
  carrier := {F | (∀ t, Normal x y (m t) (F t)) ∧
    (∑ i : Fin k,F (.inl i))+F (.inr (.inr ()))=0 ∧
    (∑ i : Fin k,F (.inr (.inl i)))+F (.inr (.inr ()))=0}
  zero_mem' := ⟨fun t => normal_zero x y (m t),by simp,by simp⟩
  add_mem' := by
    intro F G f g
    refine ⟨fun t => normal_add (f.1 t) (g.1 t),?_,?_⟩
    · simp only [Pi.add_apply,Finset.sum_add_distrib]
      rw [add_add_add_comm,f.2.1,g.2.1,zero_add]
    · simp only [Pi.add_apply,Finset.sum_add_distrib]
      rw [add_add_add_comm,f.2.2,g.2.2,zero_add]
  smul_mem' := by
    intro z F f
    refine ⟨fun t => normal_smul z (f.1 t),?_,?_⟩
    · simp only [Pi.smul_apply,← Finset.smul_sum,← smul_add,f.2.1,smul_zero]
    · simp only [Pi.smul_apply,← Finset.smul_sum,← smul_add,f.2.2,smul_zero]

/-- The simultaneously prepared old data, with disjoint exclusive mark sets,
one additional shared mark, and an explicit relation submodule of rank ≤2. -/
theorem exists_prepared_marking {a b r k : ℕ} (ha : 0<a) (hb : 3≤b) (level : r+1=(a-1)*(b-1))
    (room : 2*k+1≤r)
    (one : ∃ mark : Fin k ↪ Fin r, ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
      ∀ F : Fin k → Fin a × Fin b → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin b,(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) → (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) →
        (∑ t,F t)=0 → F=0) :
    ∃ m : (Fin k ⊕ (Fin k ⊕ Unit)) ↪ Fin r, ∃ uv : Fin 2 → Fin a × Fin b,
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
      (∀ e : Fin k ↪ Fin r, Direct x y e) ∧ Detect x y (m (.inr (.inr ()))) uv ∧
      (∀ e : Fin 3 ↪ Fin r, LinearIndependent ℂ (fun i => y (e i))) ∧
      Module.finrank ℂ (pairedSpace x y m)≤2 ∧
      (∀ d : pairedSpace x y m, (∀ i : Fin k,d.val (.inl i)=0) → d=0) ∧
      (∀ d : pairedSpace x y m, (∀ i : Fin k,d.val (.inr (.inl i))=0) → d=0) := by
  classical
  obtain ⟨first,x₀,y₀,specimen⟩ := one
  have direct : Direct x₀ y₀ first := fun H normals =>
    specimen H (fun t => (normals t).1) (fun t => (normals t).2.1) (fun t => (normals t).2.2)
  have size : Fintype.card (Fin k ⊕ (Fin k ⊕ Unit)) ≤ Fintype.card (Fin r) := by simp; omega
  obtain ⟨m⟩ := Function.Embedding.nonempty_of_card_le size
  obtain ⟨uv,x,y,all,shared,triples⟩ := common_preparation ha hb level (m (.inr (.inr ()))) first ⟨x₀,y₀,direct⟩
  let eA : Fin k ↪ Fin r := Function.Embedding.inl.trans m
  let eB : Fin k ↪ Fin r := (Function.Embedding.inl.trans Function.Embedding.inr).trans m
  exact ⟨m,uv,x,y,all,shared,triples,paired_relation_bounds x y m uv (all eA) (all eB) shared
    (pairedSpace x y m).subtype (Submodule.subtype_injective _) (fun d => d.property.1)
    (fun d => d.property.2.1) (fun d => d.property.2.2)⟩

/-- Full triple independence also gives independence of all marked singletons
and pairs under the same specialization. -/
theorem smaller_independent {I : Type*} [Fintype I] {b r : ℕ} (hr : 3≤r)
    (y : Fin r → Fin b → ℂ) (h : ∀ e : Fin 3 ↪ Fin r, LinearIndependent ℂ (fun i => y (e i)))
    (q : I ↪ Fin r) (card : Fintype.card I ≤ 3) : LinearIndependent ℂ (fun i => y (q i)) := by
  classical
  obtain ⟨sub⟩ := Function.Embedding.nonempty_of_card_le (show Fintype.card I ≤ Fintype.card (Fin 3) by simpa using card)
  let e : Fin 3 ↪ Fin r := Fin.castLEEmb hr
  obtain ⟨σ,agree⟩ := LastSliceBatch.permutation_of_markings (sub.trans e) q
  have all := (h (e.trans σ.toEmbedding)).comp sub sub.injective
  have eq : (fun i => y ((e.trans σ.toEmbedding) (sub i)))=(fun i => y (q i)) :=
    funext fun i => congrArg y (agree i)
  exact eq ▸ all

end CriticalDoubleTilt

namespace CriticalDoubleTilt

/-- Adapt a basis of `ker h` to two prescribed dual coordinates. Only
the two distinguished basis vectors survive their respective evaluations. -/
theorem adapted_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (h A B : V →ₗ[K] K) (hh : h≠0) (zA zB : V) (hzA : h zA=0) (hzB : h zB=0)
    (aa : A zA=1) (ab : A zB=0) (ba : B zA=0) (bb : B zB=1) :
    ∃ β : Module.Basis (Fin (Module.finrank K V-1)) K h.ker,
    ∃ jA jB : Fin (Module.finrank K V-1), jA≠jB ∧ (β jA : V)=zA ∧ (β jB : V)=zB ∧
      (∀ j,A (β j : V)=if j=jA then 1 else 0) ∧ (∀ j,B (β j : V)=if j=jB then 1 else 0) := by
  classical
  let za : h.ker := ⟨zA,hzA⟩
  let zb : h.ker := ⟨zB,hzB⟩
  let l := A.comp h.ker.subtype
  let b := B.comp h.ker.subtype
  have la : l za=1 := aa
  have bz : b za=0 := ba
  have ln : l≠0 := fun e => zero_ne_one (by simpa only [e,LinearMap.zero_apply] using la)
  obtain ⟨γ,j₀,jpoint,jdual⟩ := CriticalLastSlice.TwoPlanes.tilted_adapted_basis l b ln zb ab bb
  let lift : K × l.ker →ₗ[K] h.ker := (LinearMap.fst K K l.ker).smulRight za +
    l.ker.subtype.comp (LinearMap.snd K K l.ker)
  have act (p : K × l.ker) : lift p=p.1 • za+(p.2 : h.ker) := rfl
  have first (p : K × l.ker) : l (lift p)=p.1 := by
    rw [act,map_add,map_smul,smul_eq_mul,la,mul_one,LinearMap.mem_ker.mp p.2.property,add_zero]
  have second (p : K × l.ker) : b (lift p)=b (p.2 : h.ker) := by
    rw [act,map_add,map_smul,smul_eq_mul,bz,mul_zero,zero_add]
  have inject : Function.Injective lift := by
    intro p q eq
    have e := (first p).symm.trans ((congrArg l eq).trans (first q))
    refine Prod.ext e (Subtype.ext ?_)
    rw [act,act,e] at eq
    exact add_left_cancel eq
  have onto : Function.Surjective lift := by
    intro v
    have rem : v-l v • za∈l.ker := by rw [LinearMap.mem_ker,map_sub,map_smul,smul_eq_mul,la,mul_one,sub_self]
    exact ⟨(l v,⟨_,rem⟩),(act _).trans (by simp)⟩
  let E := LinearEquiv.ofBijective lift ⟨inject,onto⟩
  let line := Module.Basis.singleton Unit K
  let base := (line.prod γ).map E
  let iA : Unit ⊕ Fin (Module.finrank K h.ker-1) := .inl ()
  let iB : Unit ⊕ Fin (Module.finrank K h.ker-1) := .inr j₀
  have atA : base iA=za := by
    rw [show base iA=lift ((line.prod γ) (.inl ())) from rfl,act]
    simp [line]
  have atB : base iB=zb := by
    rw [show base iB=lift ((line.prod γ) (.inr j₀)) from rfl,act]
    simpa only [Module.Basis.prod_apply_inr_fst,Module.Basis.prod_apply_inr_snd,zero_smul,zero_add] using jpoint
  have eA (j : Unit ⊕ Fin (Module.finrank K h.ker-1)) : l (base j)=if j=iA then 1 else 0 := by
    change l (lift ((line.prod γ) j))=_
    rw [first]
    rcases j with a | t <;> simp [line,iA]
  have eB (j : Unit ⊕ Fin (Module.finrank K h.ker-1)) : b (base j)=if j=iB then 1 else 0 := by
    change b (lift ((line.prod γ) j))=_
    rw [second]
    rcases j with a | t
    · simp [iB]
    · simpa [iB] using jdual t
  have dh := Module.Dual.finrank_ker_add_one_of_ne_zero hh
  have dl := Module.Dual.finrank_ker_add_one_of_ne_zero ln
  let ids : (Unit ⊕ Fin (Module.finrank K h.ker-1)) ≃ Fin (Module.finrank K V-1) :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_sum,Fintype.card_unit,Fintype.card_fin]; omega)
  refine ⟨base.reindex ids,ids iA,ids iB,ids.injective.ne (by simp [iA,iB]),?_,?_,?_,?_⟩
  · rw [Module.Basis.reindex_apply,Equiv.symm_apply_apply,atA]
  · rw [Module.Basis.reindex_apply,Equiv.symm_apply_apply,atB]
  · intro j
    obtain ⟨i,rfl⟩ := ids.surjective j
    rw [Module.Basis.reindex_apply,Equiv.symm_apply_apply]
    change l (base i)=_
    simpa only [Equiv.apply_eq_iff_eq] using eA i
  · intro j
    obtain ⟨i,rfl⟩ := ids.surjective j
    rw [Module.Basis.reindex_apply,Equiv.symm_apply_apply]
    change b (base i)=_
    simpa only [Equiv.apply_eq_iff_eq] using eB i

end CriticalDoubleTilt

namespace CriticalDoubleTilt

open CriticalLastSlice.TwoPlanes

private theorem row_iff {K V J : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h lA lB g : V →ₗ[K] K) (β : Module.Basis J K h.ker) (y : V) (hy : h y≠0) (a b : K) :
    (g y=0 ∧ ∀ j,g (β j : V)= -(a*lA (β j : V)+b*lB (β j : V))) ↔
    g=(-a) • lA+(-b) • lB+((a*lA y+b*lB y)/h y) • h := by
  let e := a • lA+b • lB
  have neg : (-1 : K) • e=(-a) • lA+(-b) • lB := by
    ext v
    change -1*(a*lA v+b*lB v)= -a*lA v+ -b*lB v
    ring
  have ev (v : V) : e v=a*lA v+b*lB v := rfl
  simpa only [neg,ev,one_mul,neg_one_mul] using tilted_row_iff h e g β y hy 1

/-- The two marked additions prescribe the restriction of the last row
to `ker h`; normality at the old tag then fixes that row uniquely. -/
theorem normal_iff {K U V I J : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [DecidableEq J]
    (x : I → U) (y : I → V) (t : I) (h lA lB : V →ₗ[K] K)
    (β : Module.Basis J K h.ker) (jA jB : J) (ne : jA≠jB)
    (dualA : ∀ j,lA (β j : V)=if j=jA then 1 else 0) (dualB : ∀ j,lB (β j : V)=if j=jB then 1 else 0)
    (hy : h (y t)≠0) (uA uB : U) (F : U →ₗ[K] (V →ₗ[K] K)) (g : V →ₗ[K] K)
    (H : (U × K) →ₗ[K] (V →ₗ[K] K)) (split : ∀ p,H p=F p.1+p.2 • g) :
    let X : I ⊕ J → U × K := Sum.elim (fun i => (x i,0))
      (fun j => ((if j=jA then uA else if j=jB then uB else 0),1))
    let Y : I ⊕ J → V := Sum.elim y (fun j => (β j : V))
    let a := F uA (β jA : V)
    let b := F uB (β jB : V)
    ((∀ i,H (X i) (Y i)=0) ∧ (∀ p,H p (y t)=0) ∧ ∀ v,H (x t,0) v=0) ↔
      (∀ i,F (x i) (y i)=0) ∧ (∀ p,F p (y t)=0) ∧ (∀ v,F (x t) v=0) ∧
        g=(-a) • lA+(-b) • lB+((a*lA (y t)+b*lB (y t))/h (y t)) • h := by
  intro X Y a b
  have evaluated (j : J) : H (X (.inr j)) (Y (.inr j)) =
      (a*lA (β j : V)+b*lB (β j : V))+g (β j : V) := by
    by_cases ha : j=jA
    · subst j
      simp [X,Y,split,dualA,dualB,ne,a]
    · by_cases hb : j=jB
      · subst j
        simp [X,Y,split,dualA,dualB,ha,b]
      · simp [X,Y,split,dualA,dualB,ha,hb]
  have points (j : J) : H (X (.inr j)) (Y (.inr j))=0 ↔
      g (β j : V)= -(a*lA (β j : V)+b*lB (β j : V)) := by
    rw [evaluated]
    constructor <;> intro eq <;> linear_combination eq
  constructor
  · rintro ⟨all,left,right⟩
    refine ⟨fun i => by simpa [X,Y,split] using all (.inl i),
      fun p => by simpa [split] using left (p,0), fun v => by simpa [split] using right v,?_⟩
    apply (row_iff h lA lB g β (y t) hy a b).mp
    exact ⟨by simpa [split] using left (0,1),fun j => (points j).mp (all (.inr j))⟩
  · rintro ⟨old,left,right,row⟩
    obtain ⟨atY,atB⟩ := (row_iff h lA lB g β (y t) hy a b).mpr row
    refine ⟨?_,?_,?_⟩
    · rintro (i|j)
      · simpa [X,Y,split] using old i
      · exact (points j).mpr (atB j)
    · intro p
      simp [split,left,atY]
    · intro v
      simp [split,right]

/-- Every old marked normal extends to exactly one normal on the enlarged
sample set. The old bilinear form is recovered on the zero last coordinate. -/
theorem unique_extension {K U V I J : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [DecidableEq J]
    (x : I → U) (y : I → V) (t : I) (h lA lB : V →ₗ[K] K)
    (β : Module.Basis J K h.ker) (jA jB : J) (ne : jA≠jB)
    (dualA : ∀ j,lA (β j : V)=if j=jA then 1 else 0) (dualB : ∀ j,lB (β j : V)=if j=jB then 1 else 0)
    (hy : h (y t)≠0) (uA uB : U) (F : U →ₗ[K] (V →ₗ[K] K))
    (old : ∀ i,F (x i) (y i)=0) (left : ∀ p,F p (y t)=0) (right : ∀ v,F (x t) v=0) :
    let X : I ⊕ J → U × K := Sum.elim (fun i => (x i,0))
      (fun j => ((if j=jA then uA else if j=jB then uB else 0),1))
    let Y : I ⊕ J → V := Sum.elim y (fun j => (β j : V))
    ∃! H : (U × K) →ₗ[K] (V →ₗ[K] K), (∀ p : U,H (p,0)=F p) ∧ (∀ i,H (X i) (Y i)=0) ∧
      (∀ p,H p (y t)=0) ∧ ∀ v,H (x t,0) v=0 := by
  intro X Y
  let a := F uA (β jA : V)
  let b := F uB (β jB : V)
  let row := (-a) • lA+(-b) • lB+((a*lA (y t)+b*lB (y t))/h (y t)) • h
  obtain ⟨H,split⟩ := tilted_form_exists F row
  have normal := (normal_iff x y t h lA lB β jA jB ne dualA dualB hy uA uB F row H split).mpr
    ⟨old,left,right,rfl⟩
  refine ⟨H,⟨fun p => by rw [split]; simp,normal⟩,?_⟩
  intro H' data
  let g := H' (0,1)
  have split' (p : U × K) : H' p=F p.1+p.2 • g :=
    (tilted_form_decompose H' p.1 p.2).trans (by rw [data.1])
  have same : g=row := ((normal_iff x y t h lA lB β jA jB ne dualA dualB hy uA uB F g H' split').mp data.2).2.2.2
  apply LinearMap.ext
  intro p
  rw [split',split,same]

end CriticalDoubleTilt

namespace CriticalDoubleTilt

open CriticalLastSlice.TwoPlanes

/-- On each old linear relation, the only contribution from the last row
is its divided-evaluation scalar times `h`. -/
theorem weighted_row_sum {K U V T : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [Fintype T]
    (h lA lB : V →ₗ[K] K) (uA uB : U) (zA zB : V) (y : T → V)
    (F : T → U →ₗ[K] (V →ₗ[K] K)) (g : T → V →ₗ[K] K) (w : T → K)
    (rows : ∀ t,g t= (-(F t uA zA)) • lA+(-(F t uB zB)) • lB+
      ((F t uA zA*lA (y t)+F t uB zB*lB (y t))/h (y t)) • h)
    (old : (∑ t,w t • F t)=0) :
    (∑ t,w t • g t) = (∑ t,w t*((F t uA zA*lA (y t)+F t uB zB*lB (y t))/h (y t))) • h := by
  have cancels (u : U) (z : V) : (∑ t,w t*F t u z)=0 := by
    have eq := LinearMap.congr_fun (LinearMap.congr_fun old u) z
    simpa only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,LinearMap.zero_apply] using eq
  calc
    _ = ∑ t, ((-(w t*F t uA zA)) • lA+(-(w t*F t uB zB)) • lB+
          (w t*((F t uA zA*lA (y t)+F t uB zB*lB (y t))/h (y t))) • h) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [rows t,smul_add,smul_add,smul_smul,smul_smul,smul_smul,mul_neg,mul_neg]
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.sum_smul,Finset.sum_neg_distrib,cancels,neg_zero,zero_smul,zero_add]

/-- A relation on the enlarged forms is equivalent to the old relation
and one scalar cut with the same weights. -/
theorem relation_iff {K U V T : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [Fintype T]
    (h lA lB : V →ₗ[K] K) (hh : h≠0) (uA uB : U) (zA zB : V) (y : T → V)
    (F : T → U →ₗ[K] (V →ₗ[K] K)) (g : T → V →ₗ[K] K) (w : T → K)
    (H : T → (U × K) →ₗ[K] (V →ₗ[K] K)) (split : ∀ t p,H t p=F t p.1+p.2 • g t)
    (rows : ∀ t,g t= (-(F t uA zA)) • lA+(-(F t uB zB)) • lB+
      ((F t uA zA*lA (y t)+F t uB zB*lB (y t))/h (y t)) • h) :
    (∑ t,w t • H t)=0 ↔ (∑ t,w t • F t)=0 ∧
      (∑ t,w t*((F t uA zA*lA (y t)+F t uB zB*lB (y t))/h (y t)))=0 := by
  apply (tilted_sum_forms H F g w split).trans
  constructor
  · rintro ⟨old,last⟩
    rw [weighted_row_sum h lA lB uA uB zA zB y F g w rows old] at last
    exact ⟨old,(smul_eq_zero.mp last).resolve_right hh⟩
  · rintro ⟨old,cut⟩
    exact ⟨old,(weighted_row_sum h lA lB uA uB zA zB y F g w rows old).trans (by rw [cut,zero_smul])⟩

end CriticalDoubleTilt

namespace CriticalDoubleTilt

open CriticalLastSlice.TwoPlanes

/-- Add exactly `dim V−1` samples. The old labels and both weighted
relations are preserved, and the two prescribed scalar cuts detect the
entire enlarged compatible normal family. -/
theorem paired_lift {K U V I T : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype T]
    (x : I → U) (y : I → V) (mark : T → I) (w : Fin 2 → T → K)
    (h lA lB : V →ₗ[K] K) (hh : h≠0) (hy : ∀ t,h (y (mark t))≠0)
    (uA uB : U) (zA zB : V) (hzA : h zA=0) (hzB : h zB=0)
    (aa : lA zA=1) (ab : lA zB=0) (ba : lB zA=0) (bb : lB zB=1)
    (detect : ∀ F : T → U →ₗ[K] (V →ₗ[K] K), (∀ t i,F t (x i) (y i)=0) →
      (∀ t p,F t p (y (mark t))=0) → (∀ t v,F t (x (mark t)) v=0) →
      (∀ c,(∑ t,w c t • F t)=0) → (∀ c,(∑ t,w c t*((F t uA zA*lA (y (mark t))+
        F t uB zB*lB (y (mark t)))/h (y (mark t))))=0) → F=0) :
    ∃ X : I ⊕ Fin (Module.finrank K V-1) → U × K, ∃ Y : I ⊕ Fin (Module.finrank K V-1) → V,
      (∀ i,X (.inl i)=(x i,0)) ∧ (∀ i,Y (.inl i)=y i) ∧
      ∀ H : T → (U × K) →ₗ[K] (V →ₗ[K] K), (∀ t i,H t (X i) (Y i)=0) →
        (∀ t p,H t p (Y (.inl (mark t)))=0) → (∀ t v,H t (X (.inl (mark t))) v=0) →
        (∀ c,(∑ t,w c t • H t)=0) → H=0 := by
  classical
  obtain ⟨β,jA,jB,ne,atA,atB,dualA,dualB⟩ := adapted_basis h lA lB hh zA zB hzA hzB aa ab ba bb
  let J := Fin (Module.finrank K V-1)
  let X : I ⊕ J → U × K := Sum.elim (fun i => (x i,0))
    (fun j => ((if j=jA then uA else if j=jB then uB else 0),1))
  let Y : I ⊕ J → V := Sum.elim y (fun j => (β j : V))
  refine ⟨X,Y,fun i => rfl,fun i => rfl,?_⟩
  intro H samples left right relations
  let F (t : T) := (H t).comp (LinearMap.inl K U K)
  let g (t : T) := H t (0,1)
  have split (t : T) (p : U × K) : H t p=F t p.1+p.2 • g t := tilted_form_decompose (H t) p.1 p.2
  have facts (t : T) : (∀ i,F t (x i) (y i)=0) ∧ (∀ p,F t p (y (mark t))=0) ∧
      (∀ v,F t (x (mark t)) v=0) ∧ g t= (-(F t uA zA)) • lA+(-(F t uB zB)) • lB+
        ((F t uA zA*lA (y (mark t))+F t uB zB*lB (y (mark t)))/h (y (mark t))) • h := by
    have normal := (normal_iff x y (mark t) h lA lB β jA jB ne dualA dualB (hy t) uA uB
      (F t) (g t) (H t) (split t)).mp ⟨samples t,left t,right t⟩
    simpa only [atA,atB] using normal
  have conditions (c : Fin 2) := (relation_iff h lA lB hh uA uB zA zB (fun t => y (mark t)) F g (w c) H
    split (fun t => (facts t).2.2.2)).mp (relations c)
  have old := detect F (fun t => (facts t).1) (fun t => (facts t).2.1) (fun t => (facts t).2.2.1)
    (fun c => (conditions c).1) (fun c => (conditions c).2)
  have bottom (t : T) : g t=0 := by
    rw [(facts t).2.2.2,old]
    simp
  funext t
  apply LinearMap.ext
  intro p
  rw [split,old,bottom]
  simp

/-- A parametrization of the old compatible relations is sufficient. The
two scalar cuts need only detect its parameters. -/
theorem paired_lift_of_family {K U V I T D : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype T] [AddCommGroup D] [Module K D]
    (x : I → U) (y : I → V) (mark : T → I) (w : Fin 2 → T → K)
    (F : D →ₗ[K] (T → U →ₗ[K] (V →ₗ[K] K)))
    (complete : ∀ G : T → U →ₗ[K] (V →ₗ[K] K), (∀ t i,G t (x i) (y i)=0) →
      (∀ t p,G t p (y (mark t))=0) → (∀ t v,G t (x (mark t)) v=0) →
      (∀ c,(∑ t,w c t • G t)=0) → ∃ d,F d=G)
    (h lA lB : V →ₗ[K] K) (hh : h≠0) (hy : ∀ t,h (y (mark t))≠0)
    (uA uB : U) (zA zB : V) (hzA : h zA=0) (hzB : h zB=0)
    (aa : lA zA=1) (ab : lA zB=0) (ba : lB zA=0) (bb : lB zB=1)
    (detect : ∀ d : D, (∀ c,(∑ t,w c t*((F d t uA zA*lA (y (mark t))+
      F d t uB zB*lB (y (mark t)))/h (y (mark t))))=0) → d=0) :
    ∃ X : I ⊕ Fin (Module.finrank K V-1) → U × K, ∃ Y : I ⊕ Fin (Module.finrank K V-1) → V,
      (∀ i,X (.inl i)=(x i,0)) ∧ (∀ i,Y (.inl i)=y i) ∧
      ∀ H : T → (U × K) →ₗ[K] (V →ₗ[K] K), (∀ t i,H t (X i) (Y i)=0) →
        (∀ t p,H t p (Y (.inl (mark t)))=0) → (∀ t v,H t (X (.inl (mark t))) v=0) →
        (∀ c,(∑ t,w c t • H t)=0) → H=0 := by
  apply paired_lift x y mark w h lA lB hh hy uA uB zA zB hzA hzB aa ab ba bb
  intro G samples left right relations cuts
  obtain ⟨d,rfl⟩ := complete G samples left right relations
  rw [detect d cuts,map_zero]

end CriticalDoubleTilt

namespace CriticalDoubleTilt

private theorem onto_of_dual_hit {D : Type*} [AddCommGroup D] [Module ℂ D]
    (f : D →ₗ[ℂ] ℂ) {x : D} (hx : f x≠0) : Function.Surjective f := by
  intro y
  refine ⟨(y/f x) • x,?_⟩
  rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hx]

/-- Two separately detecting families on a space of dimension at most two
have a jointly detecting pair with one member from each family. -/
theorem choose_two_functionals {D A B : Type*} [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D]
    [Nonempty A] [Nonempty B] (dimension : Module.finrank ℂ D≤2)
    (left : A → D →ₗ[ℂ] ℂ) (right : B → D →ₗ[ℂ] ℂ)
    (hl : ∀ d : D,(∀ a,left a d=0) → d=0) (hr : ∀ d : D,(∀ b,right b d=0) → d=0) :
    ∃ a b,∀ d : D,left a d=0 → right b d=0 → d=0 := by
  classical
  by_cases trivial : ∀ d : D,d=0
  · exact ⟨Classical.choice ‹Nonempty A›,Classical.choice ‹Nonempty B›,fun d _ _ => trivial d⟩
  push Not at trivial
  obtain ⟨v,hv⟩ := trivial
  obtain ⟨a,ha⟩ : ∃ a,left a v≠0 := by by_contra! bad; exact hv (hl _ bad)
  let N := (left a).ker
  have dimN : Module.finrank ℂ N≤1 := by
    have e := (left a).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (onto_of_dual_hit _ ha),finrank_top,Module.finrank_self] at e
    change Module.finrank ℂ (left a).ker≤1
    omega
  by_cases all : ∀ x : N,x=0
  · refine ⟨a,Classical.choice ‹Nonempty B›,?_⟩
    intro d ed _
    exact congrArg Subtype.val (all ⟨d,ed⟩)
  push Not at all
  obtain ⟨w,hw⟩ := all
  have nonzero : (w:D)≠0 := fun eq => hw (Subtype.ext eq)
  obtain ⟨b,hb⟩ : ∃ b,right b (w:D)≠0 := by by_contra! bad; exact nonzero (hr _ bad)
  let g := (right b).domRestrict N
  have inj : Function.Injective g := by
    have hit : g w≠0 := hb
    have e := g.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (onto_of_dual_hit g hit),finrank_top,Module.finrank_self] at e
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp (by omega))
  refine ⟨a,b,?_⟩
  intro d da db
  have eq : (⟨d,da⟩:N)=0 := inj (by rw [map_zero]; exact db)
  exact congrArg Subtype.val eq

/-- Move one test vector off finitely many proper subspaces while preserving
separation together with a fixed scalar functional. -/
theorem avoid_preserving_pair {D V I : Type*} [AddCommGroup D] [Module ℂ D]
    [AddCommGroup V] [Module ℂ V] [Finite I] (avoid : I→Submodule ℂ V)
    (proper : ∀ i,avoid i≠⊤) (E : V →ₗ[ℂ] (D →ₗ[ℂ] ℂ)) (l : D →ₗ[ℂ] ℂ) (x₀ : V)
    (separates : ∀ d,E x₀ d=0 → l d=0 → d=0) :
    ∃ x : V,(∀ i,x∉avoid i) ∧ ∀ d,E x d=0 → l d=0 → d=0 := by
  classical
  by_cases alone : ∀ d,l d=0 → d=0
  · obtain ⟨x,hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top avoid proper
    exact ⟨x,hx,fun d _ h => alone d h⟩
  push Not at alone
  obtain ⟨v,lv,hv⟩ := alone
  let m := E.flip v
  have nz : m x₀≠0 := fun eq => hv (separates v eq lv)
  have pk : m.ker≠⊤ := by
    intro h
    have mem : x₀∈m.ker := h ▸ Submodule.mem_top
    exact nz (LinearMap.mem_ker.mp mem)
  let family : Option I → Submodule ℂ V := Option.elim' m.ker avoid
  have pf (i : Option I) : family i≠⊤ := by cases i with
    | none => exact pk
    | some i => exact proper i
  obtain ⟨x,hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top family pf
  have good : E x v≠0 := hx none
  refine ⟨x,fun i => hx (some i),?_⟩
  intro d ed ld
  let z := (E x₀ v) • d - (E x₀ d) • v
  have e₀ : E x₀ z=0 := by simp only [z,map_sub,map_smul,smul_eq_mul]; ring
  have l₀ : l z=0 := by simp [z,ld,lv]
  have relation := congrArg (E x) (separates z e₀ l₀)
  have van : E x₀ d*E x v=0 := by
    simpa only [z,map_sub,map_smul,smul_eq_mul,ed,mul_zero,zero_sub,map_zero,neg_eq_zero] using relation
  exact separates d ((mul_eq_zero.mp van).resolve_right good) ld

end CriticalDoubleTilt

namespace CriticalDoubleTilt

/-- The two scalar tests may be made jointly separating while enlarging
each of the finitely many independent triples to an independent five-tuple. -/
theorem choose_transverse_vectors {D V I : Type*} [AddCommGroup D] [Module ℂ D]
    [AddCommGroup V] [Module ℂ V] [Finite I] (dimension : 5≤Module.finrank ℂ V)
    (triples : I → Fin 3 → V) (ind : ∀ i,LinearIndependent ℂ (triples i))
    (E F : V →ₗ[ℂ] (D →ₗ[ℂ] ℂ)) (u₀ v₀ : V)
    (separates : ∀ d,E u₀ d=0 → F v₀ d=0 → d=0) :
    ∃ u v : V,(∀ d,E u d=0 → F v d=0 → d=0) ∧
      ∀ i,LinearIndependent ℂ (Fin.cons v (Fin.cons u (triples i))) := by
  classical
  let P (i : I) := Submodule.span ℂ (Set.range (triples i))
  have proper (i : I) : P i≠⊤ := by
    intro eq
    have h := finrank_le_of_span_eq_top eq
    change Module.finrank ℂ V≤Fintype.card (Fin 3) at h
    simp only [Fintype.card_fin] at h
    omega
  obtain ⟨u,avoid,first⟩ := avoid_preserving_pair P proper E (F v₀) u₀ separates
  let Q (i : I) := Submodule.span ℂ (Set.range (Fin.cons u (triples i)))
  have ok (i : I) : Q i≠⊤ := by
    intro eq
    have h := finrank_le_of_span_eq_top eq
    change Module.finrank ℂ V≤Fintype.card (Fin 4) at h
    simp only [Fintype.card_fin] at h
    omega
  obtain ⟨v,skip,second⟩ := avoid_preserving_pair Q ok F (E u) v₀ (fun d b a => first d a b)
  exact ⟨u,v,fun d a b => second d b a,fun i => ((ind i).finCons (avoid i)).finCons (skip i)⟩

/-- Interpolate any scalar values on an independent finite family by a
linear functional on the entire ambient space. -/
theorem dual_interpolates {V I : Type*} [AddCommGroup V] [Module ℂ V]
    (v : I→V) (ind : LinearIndependent ℂ v) (value : I→ℂ) :
    ∃ phi : V →ₗ[ℂ] ℂ,∀ i,phi (v i)=value i := by
  classical
  let W := Submodule.span ℂ (Set.range v)
  let basis := Module.Basis.span ind
  let psi := basis.constr ℂ value
  obtain ⟨phi,extend⟩ := psi.exists_extend
  refine ⟨phi,?_⟩
  intro i
  have point : ((basis i:W):V)=v i := congrArg Subtype.val (Module.Basis.span_apply ind i)
  calc
    _ = (phi.comp W.subtype) (basis i) := by rw [LinearMap.comp_apply]; exact congrArg phi point.symm
    _ = psi (basis i) := congrArg (fun f : W →ₗ[ℂ] ℂ => f (basis i)) extend
    _ = _ := basis.constr_basis ℂ value i

end CriticalDoubleTilt

namespace CriticalDoubleTilt

/-- Prescribed values on the four selected vectors, with a simultaneous
nonzero value on every other mark for the first deformation covector. -/
theorem conditioning_forms {V I : Type*} [AddCommGroup V] [Module ℂ V] [Finite I]
    (p q zA zB : V) (other : I→V) (first : I)
    (ind : ∀ i,LinearIndependent ℂ (Fin.cons zB (Fin.cons zA ![p,q,other i]))) :
    ∃ h₀ h₁ ellA ellB : V →ₗ[ℂ] ℂ,
      (h₀ zA=0 ∧ h₀ zB=0 ∧ h₀ p=0 ∧ h₀ q=0 ∧ ∀ i,h₀ (other i)≠0) ∧
      (h₁ zA=0 ∧ h₁ zB=0 ∧ h₁ p=1 ∧ h₁ q=1) ∧
      (ellA zA=1 ∧ ellA zB=0 ∧ ellA p=1 ∧ ellA q=0) ∧
      (ellB zA=0 ∧ ellB zB=1 ∧ ellB p=0 ∧ ellB q=1) := by
  classical
  let dual := Module.Dual.eval ℂ V
  let Z := ((dual zA).ker ⊓ (dual zB).ker) ⊓ ((dual p).ker ⊓ (dual q).ker)
  have avoid (i : I) : ∃ f∈Z,dual (other i) f≠0 := by
    obtain ⟨f,vals⟩ := dual_interpolates _ (ind i) (![0,0,0,0,1] : Fin 5→ℂ)
    refine ⟨f,⟨⟨vals 1,vals 0⟩,⟨vals 2,vals 3⟩⟩,?_⟩
    change f (other i)≠0
    rw [show f (other i)=1 from vals 4]
    exact one_ne_zero
  obtain ⟨h₀,van,nonzero⟩ := Module.Dual.exists_forall_mem_ne_zero_of_forall_exists Z
    (fun i => dual (other i)) avoid
  obtain ⟨h₁,hval⟩ := dual_interpolates _ (ind first) (![0,0,1,1,0] : Fin 5→ℂ)
  obtain ⟨ellA,aval⟩ := dual_interpolates _ (ind first) (![0,1,1,0,0] : Fin 5→ℂ)
  obtain ⟨ellB,bval⟩ := dual_interpolates _ (ind first) (![1,0,0,1,0] : Fin 5→ℂ)
  exact ⟨h₀,h₁,ellA,ellB,⟨van.1.1,van.1.2,van.2.1,van.2.2,nonzero⟩,
    ⟨hval 1,hval 0,hval 2,hval 3⟩,⟨aval 1,aval 0,aval 2,aval 3⟩,
    ⟨bval 1,bval 0,bval 2,bval 3⟩⟩

end CriticalDoubleTilt

namespace CriticalDoubleTilt

open Filter Topology

/-- The two simple poles control the leading linear map. If their combined
residue is injective, some common nonzero complex displacement preserves
injectivity while avoiding every denominator. -/
theorem exists_two_pole_injective {T D : Type*} [Fintype T] [AddCommGroup D] [Module ℂ D]
    [FiniteDimensional ℂ D] (β : Fin 2 → T → ℂ) (N : T → D →ₗ[ℂ] ℂ)
    (p q : T) (pq : p ≠ q) (a b : T → ℂ)
    (ap : a p = 0) (aq : a q = 0) (bp : b p = 1) (bq : b q = 1)
    (away : ∀ t, t≠p → t≠q → a t≠0)
    (indep : Function.Injective (fun w : D => fun i : Fin 2 =>
      β i p*N p w + β i q*N q w)) :
    ∃ ε : ℂ, ε≠0 ∧ (∀ t, a t+ε*b t≠0) ∧
      ∀ w : D, (∀ i : Fin 2, (∑ t, β i t*(N t w/(a t+ε*b t)))=0) → w=0 := by
  classical
  let E := Fin (Module.finrank ℂ D) → ℂ
  let e : D ≃ₗ[ℂ] E := (Module.finBasis ℂ D).equivFun
  let L (t : T) : E →L[ℂ] (Fin 2 → ℂ) := LinearMap.toContinuousLinearMap
    (LinearMap.pi (fun i : Fin 2 => β i t • ((N t).comp e.symm.toLinearMap)))
  let c (t : T) (z : ℂ) : ℂ := if t=p ∨ t=q then 1 else z/(a t+z*b t)
  let G (z : ℂ) : E →L[ℂ] (Fin 2 → ℂ) := ∑ t, c t z • L t
  have read (z : ℂ) (u : E) (i : Fin 2) :
      G z u i = ∑ t, c t z * (β i t * N t (e.symm u)) := by
    simp only [G,sum_apply,Finset.sum_apply,smul_apply,
      Pi.smul_apply,smul_eq_mul]
    rfl
  have at_zero (t : T) : c t 0 = (if t=p then 1 else 0)+(if t=q then 1 else 0) := by
    by_cases h : t=p
    · subst t
      simp [c,pq]
    · by_cases h' : t=q
      · subst t
        simp [c,pq.symm]
      · simp [c,h,h']
  have read_zero (u : E) (i : Fin 2) :
      G 0 u i = β i p*N p (e.symm u) + β i q*N q (e.symm u) := by
    rw [read]
    simp_rw [at_zero,add_mul,ite_mul,zero_mul,one_mul,Finset.sum_add_distrib]
    simp
  have inject_zero : Function.Injective (G 0) := by
    intro x y eq
    apply e.symm.injective
    apply indep
    funext i
    exact (read_zero x i).symm.trans ((congrFun eq i).trans (read_zero y i))
  have continuous_weight (t : T) : ContinuousAt (c t) 0 := by
    by_cases h : t=p ∨ t=q
    · simpa only [c,if_pos h] using (continuousAt_const : ContinuousAt (fun _ : ℂ => (1:ℂ)) 0)
    · have h₀ := away t (fun x => h (.inl x)) (fun x => h (.inr x))
      simp only [c,if_neg h]
      apply ContinuousAt.div continuousAt_id
      · fun_prop
      · simpa using h₀
  have cont : ContinuousAt G 0 := by
    have partial_sum (U : Finset T) : ContinuousAt (fun z => ∑ t ∈ U, c t z • L t) 0 := by
      induction U using Finset.induction_on with
      | empty => simpa only [Finset.sum_empty] using
          (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : E →L[ℂ] (Fin 2 → ℂ))) 0)
      | insert t U ht ih =>
        simp only [Finset.sum_insert ht]
        exact ((continuous_weight t).smul continuousAt_const).add ih
    exact partial_sum Finset.univ
  have opened : ∀ᶠ z : ℂ in 𝓝 0, Function.Injective (G z) :=
    cont.tendsto.eventually (ContinuousLinearMap.isOpen_injective.eventually_mem inject_zero)
  have near_ne : ∀ᶠ z : ℂ in 𝓝[≠] 0, z ≠ 0 := self_mem_nhdsWithin
  have near_den (t : T) : ∀ᶠ z : ℂ in 𝓝[≠] 0, a t+z*b t ≠ 0 := by
    by_cases pin : t=p
    · subst t
      simpa only [ap,bp,mul_one,zero_add] using near_ne
    by_cases qin : t=q
    · subst t
      simpa only [aq,bq,mul_one,zero_add] using near_ne
    have hc : ContinuousAt (fun z : ℂ => a t+z*b t) 0 := by fun_prop
    exact (hc.eventually_ne (by simpa using away t pin qin)).filter_mono nhdsWithin_le_nhds
  have all_den : ∀ᶠ z : ℂ in 𝓝[≠] 0, ∀ t, a t+z*b t ≠ 0 := eventually_all.mpr near_den
  obtain ⟨ε,nonzero,den,good⟩ :=
    (near_ne.and (all_den.and (opened.filter_mono nhdsWithin_le_nhds))).exists
  refine ⟨ε,nonzero,den,?_⟩
  have ratio (t : T) : c t ε = ε/(a t+ε*b t) := by
    by_cases pin : t=p
    · subst t
      simp [c,ap,bp,nonzero]
    by_cases qin : t=q
    · subst t
      simp [c,aq,bq,nonzero]
    simp [c,pin,qin]
  intro w zero
  have kill : G ε (e w)=0 := by
    funext i
    rw [read]
    simp only [e.symm_apply_apply,ratio]
    calc
      _ = ε * ∑ t, β i t*(N t w/(a t+ε*b t)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
      _ = 0 := by rw [zero,mul_zero]
  apply e.injective
  rw [map_zero]
  apply good
  simpa only [map_zero] using kill

end CriticalDoubleTilt

namespace CriticalDoubleTilt

/-- A residue matrix normalized to the two coordinate tests is injective
exactly when the two original pole forms have no common nonzero vector. -/
theorem exists_normalized_two_poles {T D : Type*} [Fintype T] [AddCommGroup D] [Module ℂ D]
    [FiniteDimensional ℂ D] (β : Fin 2 → T → ℂ) (N : T → D →ₗ[ℂ] ℂ)
    (p q : T) (pq : p ≠ q) (a b : T → ℂ)
    (ap : a p = 0) (aq : a q = 0) (bp : b p = 1) (bq : b q = 1)
    (away : ∀ t, t≠p → t≠q → a t≠0)
    (pp : β 0 p=1) (pq₀ : β 0 q=0) (qp : β 1 p=0) (qq : β 1 q=1)
    (separate : ∀ w : D, N p w=0 → N q w=0 → w=0) :
    ∃ ε : ℂ, ε≠0 ∧ (∀ t, a t+ε*b t≠0) ∧
      ∀ w : D, (∀ i : Fin 2, (∑ t, β i t*(N t w/(a t+ε*b t)))=0) → w=0 := by
  apply exists_two_pole_injective β N p q pq a b ap aq bp bq away
  intro x y equal
  apply sub_eq_zero.mp
  apply separate
  · have atP := congrFun equal 0
    simp only [pp,pq₀,one_mul,zero_mul,add_zero] at atP
    rw [map_sub,atP,sub_self]
  · have atQ := congrFun equal 1
    simp only [qp,qq,zero_mul,one_mul,zero_add] at atQ
    rw [map_sub,atQ,sub_self]

end CriticalDoubleTilt

namespace CriticalDoubleTilt

/-- For two individually detecting exclusive batches, two tilted scalar
rows still detect their joint defect. Their additional shared-row weights
are unrestricted. The two tilt vectors lie in the common kernel of h. -/
theorem two_pole_cut_weighted {D U V : Type*} [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (hk : 0<k) (hd : Module.finrank ℂ D≤2) (hv : 5≤Module.finrank ℂ V) :
    let T := Fin k ⊕ (Fin k ⊕ Unit)
    ∀ (y : T→V) (F : D →ₗ[ℂ] (T → U →ₗ[ℂ] (V →ₗ[ℂ] ℂ))) (β : Fin 2→T→ℂ),
      (∀ e : Fin 3 ↪ T,LinearIndependent ℂ (fun i => y (e i))) →
      (∀ d : D,(∀ i : Fin k,F d (.inl i)=0) → d=0) →
      (∀ d : D,(∀ i : Fin k,F d (.inr (.inl i))=0) → d=0) →
      (∀ i : Fin k,β 0 (.inl i)=1 ∧ β 1 (.inl i)=0) →
      (∀ i : Fin k,β 0 (.inr (.inl i))=0 ∧ β 1 (.inr (.inl i))=1) →
      ∃ uA uB : U,∃ zA zB : V,∃ h ellA ellB : V →ₗ[ℂ] ℂ,
        h zA=0 ∧ h zB=0 ∧ (∀ t,h (y t)≠0) ∧
        ellA zA=1 ∧ ellA zB=0 ∧ ellB zA=0 ∧ ellB zB=1 ∧
        ∀ d : D,(∀ i : Fin 2,(∑ t,β i t*((F d t uA zA*ellA (y t)+F d t uB zB*ellB (y t))/h (y t)))=0) → d=0 := by
  classical
  intro T y F β triples left right wl wr
  let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  let probe (t : T) (x : U) : V →ₗ[ℂ] (D →ₗ[ℂ] ℂ) := (((LinearMap.proj t).comp F).flip x).flip
  let A (x : Fin k × U × V) := probe (.inl x.1) x.2.1 x.2.2
  let B (x : Fin k × U × V) := probe (.inr (.inl x.1)) x.2.1 x.2.2
  have sa (d : D) (zero : ∀ x,A x d=0) : d=0 := by
    apply left d
    intro i
    exact LinearMap.ext (fun u => LinearMap.ext (fun v => zero (i,u,v)))
  have sb (d : D) (zero : ∀ x,B x d=0) : d=0 := by
    apply right d
    intro i
    exact LinearMap.ext (fun u => LinearMap.ext (fun v => zero (i,u,v)))
  obtain ⟨xa,xb,measured⟩ := choose_two_functionals hd A B sa sb
  let p : T := .inl xa.1
  let q : T := .inr (.inl xb.1)
  have pq : p≠q := by simp [p,q]
  let R := {s : T // s≠p ∧ s≠q}
  let other : R := ⟨.inr (.inr ()),by
    let tag : T→ℕ := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))
    constructor
    · intro e; have invalid : (2:ℕ)=0 := congrArg tag e; omega
    · intro e; have invalid : (2:ℕ)=1 := congrArg tag e; omega⟩
  let tr (s : R) : Fin 3→V := ![y p,y q,y s.val]
  have independent (s : R) : LinearIndependent ℂ (tr s) := by
    let tag : Fin 3→T := ![p,q,s.val]
    have inj : Function.Injective tag := by
      intro i j eq
      fin_cases i <;> fin_cases j <;> simp [tag] at eq ⊢
      all_goals first | exact pq eq | exact pq eq.symm | exact s.property.1 eq |
        exact s.property.1 eq.symm | exact s.property.2 eq | exact s.property.2 eq.symm
    have lin := triples ⟨tag,inj⟩
    have agree : (fun i => y (tag i))=tr s := by funext i; fin_cases i <;> rfl
    exact agree ▸ lin
  obtain ⟨zA,zB,tests,flags⟩ := choose_transverse_vectors hv tr independent
    (probe p xa.2.1) (probe q xb.2.1) xa.2.2 xb.2.2 measured
  obtain ⟨h₀,h₁,ellA,ellB,⟨hA₀,hB₀,hp₀,hq₀,away⟩,⟨hA₁,hB₁,hp₁,hq₁⟩,
    ⟨azA,azB,ap,aq⟩,⟨bzA,bzB,bp,bq⟩⟩ :=
    conditioning_forms (y p) (y q) zA zB (fun s : R => y s.val) other flags
  let N (t : T) : D →ₗ[ℂ] ℂ := ellA (y t) • probe t xa.2.1 zA + ellB (y t) • probe t xb.2.1 zB
  have normP (d : D) : N p d=probe p xa.2.1 zA d := by simp [N,ap,bp]
  have normQ (d : D) : N q d=probe q xb.2.1 zB d := by simp [N,aq,bq]
  obtain ⟨ε,_,denom,cut⟩ := exists_normalized_two_poles β N p q pq
    (fun s => h₀ (y s)) (fun s => h₁ (y s)) hp₀ hq₀ hp₁ hq₁
    (fun t a b => away ⟨t,a,b⟩) (wl xa.1).1 (wr xb.1).1 (wl xa.1).2 (wr xb.1).2
    (fun d x z => tests d ((normP d).symm.trans x) ((normQ d).symm.trans z))
  let h := h₀+ε • h₁
  refine ⟨xa.2.1,xb.2.1,zA,zB,h,ellA,ellB,?_,?_,denom,azA,azB,bzA,bzB,?_⟩
  · simp [h,hA₀,hA₁]
  · simp [h,hB₀,hB₁]
  · intro d zero
    apply cut d
    intro i
    convert zero i using 1
    apply Finset.sum_congr rfl
    intro t _
    change β i t*((ellA (y t)*F d t xa.2.1 zA+ellB (y t)*F d t xb.2.1 zB)/h (y t))=_
    ring

/-- The ordinary paired sector has one row on each exclusive batch and
unit weight on the shared point in both rows. -/
theorem two_pole_cut {D U V : Type*} [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (hk : 0<k) (hd : Module.finrank ℂ D≤2) (hv : 5≤Module.finrank ℂ V) :
    let T := Fin k ⊕ (Fin k ⊕ Unit)
    ∀ (y : T→V) (F : D →ₗ[ℂ] (T → U →ₗ[ℂ] (V →ₗ[ℂ] ℂ))),
      (∀ e : Fin 3 ↪ T,LinearIndependent ℂ (fun i => y (e i))) →
      (∀ d : D,(∀ i : Fin k,F d (.inl i)=0) → d=0) →
      (∀ d : D,(∀ i : Fin k,F d (.inr (.inl i))=0) → d=0) →
      let β (i : Fin 2) (s : T) : ℂ := s.elim (fun _ => if i=0 then 1 else 0)
        (Sum.elim (fun _ => if i=1 then 1 else 0) (fun _ => 1))
      ∃ uA uB : U,∃ zA zB : V,∃ h ellA ellB : V →ₗ[ℂ] ℂ,
        h zA=0 ∧ h zB=0 ∧ (∀ t,h (y t)≠0) ∧
        ellA zA=1 ∧ ellA zB=0 ∧ ellB zA=0 ∧ ellB zB=1 ∧
        ∀ d : D,(∀ i : Fin 2,(∑ t,β i t*((F d t uA zA*ellA (y t)+F d t uB zB*ellB (y t))/h (y t)))=0) → d=0 := by
  intro T y F triples left right β
  apply two_pole_cut_weighted k hk hd hv y F β triples left right
  · intro i
    simp [β]
  · intro i
    simp [β]

end CriticalDoubleTilt

namespace CriticalDoubleTilt

/-- The canonical finite-coordinate matrix-to-bilinear equivalence, with
the unconjugated pairing used in the registered normal equations. -/
theorem bilinear_coordinates (a b : ℕ) :
    ∃ E : (Fin a × Fin b → ℂ) ≃ₗ[ℂ] ((Fin a → ℂ) →ₗ[ℂ] ((Fin b → ℂ) →ₗ[ℂ] ℂ)),
      ∀ M u v, E M u v=∑ ij : Fin a × Fin b, (u ij.1*v ij.2)*M ij := by
  let E : (Fin a × Fin b → ℂ) ≃ₗ[ℂ] ((Fin a → ℂ) →ₗ[ℂ] ((Fin b → ℂ) →ₗ[ℂ] ℂ)) :=
    (LinearEquiv.curry ℂ ℂ (Fin a) (Fin b)).trans (Matrix.toLinearMap₂' ℂ)
  refine ⟨E,?_⟩
  intro M u v
  change Matrix.toLinearMap₂' ℂ (Matrix.of (fun i j => M (i,j))) u v=_
  rw [Matrix.toLinearMap₂'_apply,Fintype.sum_prod_type]
  simp only [Matrix.of_apply,smul_eq_mul,mul_assoc]

theorem normal_iff_bilinear {a b r : ℕ} (x : Fin r → Fin a → ℂ) (y : Fin r → Fin b → ℂ) (s : Fin r)
    (E : (Fin a × Fin b → ℂ) ≃ₗ[ℂ] ((Fin a → ℂ) →ₗ[ℂ] ((Fin b → ℂ) →ₗ[ℂ] ℂ)))
    (action : ∀ M u v,E M u v=∑ ij : Fin a × Fin b, (u ij.1*v ij.2)*M ij) (M : Fin a × Fin b → ℂ) :
    Normal x y s M ↔ (∀ t,E M (x t) (y t)=0) ∧ (∀ u,E M u (y s)=0) ∧ ∀ v,E M (x s) v=0 := by
  have first (u : Fin a → ℂ) (v : Fin b → ℂ) : E M u v=∑ i,u i*(∑ j,v j*M (i,j)) := by
    rw [action,Fintype.sum_prod_type]
    simp only [Finset.mul_sum,mul_assoc]
  have second (u : Fin a → ℂ) (v : Fin b → ℂ) : E M u v=∑ j,v j*(∑ i,u i*M (i,j)) := by
    rw [first]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
  constructor
  · rintro ⟨outer,left,right⟩
    refine ⟨fun t => (action M _ _).trans (outer t),?_,?_⟩
    · intro u
      simp only [first,left,mul_zero,Finset.sum_const_zero]
    · intro v
      simp only [second,right,mul_zero,Finset.sum_const_zero]
  · rintro ⟨outer,left,right⟩
    refine ⟨fun t => (action M _ _).symm.trans (outer t),?_,?_⟩
    · intro i
      have eq := left (Pi.single i 1)
      rw [first] at eq
      simpa [Pi.single_apply,ite_mul] using eq
    · intro j
      have eq := right (Pi.single j 1)
      rw [second] at eq
      simpa [Pi.single_apply,ite_mul] using eq

/-- The two weight rows are the two exclusive sums, each together with
the distinguished shared mark. -/
theorem paired_sum_iff {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (k : ℕ) (G : (Fin k ⊕ (Fin k ⊕ Unit)) → E) :
    let w (c : Fin 2) (t : Fin k ⊕ (Fin k ⊕ Unit)) : K := t.elim (fun _ => if c=0 then 1 else 0)
      (Sum.elim (fun _ => if c=1 then 1 else 0) (fun _ => 1))
    (∀ c,(∑ t,w c t • G t)=0) ↔
      (∑ i : Fin k,G (.inl i))+G (.inr (.inr ()))=0 ∧ (∑ i : Fin k,G (.inr (.inl i)))+G (.inr (.inr ()))=0 := by
  intro w
  have left : (∑ t,w 0 t • G t)=(∑ i : Fin k,G (.inl i))+G (.inr (.inr ())) := by simp [w,Fintype.sum_sum_type]
  have right : (∑ t,w 1 t • G t)=(∑ i : Fin k,G (.inr (.inl i)))+G (.inr (.inr ())) := by simp [w,Fintype.sum_sum_type]
  constructor
  · intro all
    exact ⟨left.symm.trans (all 0),right.symm.trans (all 1)⟩
  · rintro ⟨a,b⟩ c
    fin_cases c
    · exact left.trans a
    · exact right.trans b

/-- The concrete paired subspace is precisely the space of the curried
old compatible tuples. Zero at any tag is preserved in both directions. -/
theorem prepared_bilinear_family {a b r k : ℕ} (x : Fin r → Fin a → ℂ) (y : Fin r → Fin b → ℂ)
    (mark : Fin k ⊕ (Fin k ⊕ Unit) → Fin r) :
    let T := Fin k ⊕ (Fin k ⊕ Unit)
    let D := pairedSpace x y mark
    let w (c : Fin 2) (t : T) : ℂ := t.elim (fun _ => if c=0 then 1 else 0)
      (Sum.elim (fun _ => if c=1 then 1 else 0) (fun _ => 1))
    ∃ F : D →ₗ[ℂ] (T → (Fin a → ℂ) →ₗ[ℂ] ((Fin b → ℂ) →ₗ[ℂ] ℂ)), Function.Injective F ∧
      (∀ (d : D) t,F d t=0 ↔ d.val t=0) ∧
      ∀ G : T → (Fin a → ℂ) →ₗ[ℂ] ((Fin b → ℂ) →ₗ[ℂ] ℂ), (∃ d,F d=G) ↔
        (∀ t i,G t (x i) (y i)=0) ∧ (∀ t u,G t u (y (mark t))=0) ∧ (∀ t v,G t (x (mark t)) v=0) ∧
        (∀ c,(∑ t,w c t • G t)=0) := by
  intro T D w
  obtain ⟨E,action⟩ := bilinear_coordinates a b
  let all := LinearEquiv.piCongrRight (fun _ : T => E)
  let F := all.toLinearMap.comp D.subtype
  have value (d : D) (t : T) : F d t=E (d.val t) := rfl
  have compatible (M : T → Fin a × Fin b → ℂ) : M∈D ↔
      (∀ t i,E (M t) (x i) (y i)=0) ∧ (∀ t u,E (M t) u (y (mark t))=0) ∧
      (∀ t v,E (M t) (x (mark t)) v=0) ∧ (∀ c,(∑ t,w c t • E (M t))=0) := by
    constructor
    · intro member
      have normals (t : T) := (normal_iff_bilinear x y (mark t) E action (M t)).mp (member.1 t)
      have raw := (paired_sum_iff (K:=ℂ) k M).mpr ⟨member.2.1,member.2.2⟩
      refine ⟨fun t => (normals t).1,fun t => (normals t).2.1,fun t => (normals t).2.2,?_⟩
      intro c
      have eq := congrArg E (raw c)
      simpa only [map_sum,map_smul,map_zero] using eq
    · rintro ⟨sample,left,right,relation⟩
      have weights (c : Fin 2) : (∑ t,w c t • M t)=0 := by
        apply E.injective
        simpa only [map_sum,map_smul,map_zero] using relation c
      have both := (paired_sum_iff (K:=ℂ) k M).mp weights
      exact ⟨fun t => (normal_iff_bilinear x y (mark t) E action (M t)).mpr ⟨sample t,left t,right t⟩,both⟩
  refine ⟨F,all.injective.comp (Submodule.subtype_injective _),?_,?_⟩
  · intro d t
    rw [value]
    exact ⟨fun eq => E.injective (eq.trans E.map_zero.symm),fun eq => by rw [eq,map_zero]⟩
  · intro G
    constructor
    · rintro ⟨d,rfl⟩
      exact (compatible d.val).mp d.property
    · intro conditions
      let M (t : T) := E.symm (G t)
      have read (t : T) : E (M t)=G t := E.apply_symm_apply _
      have belongs : M∈D := (compatible M).mpr (by simpa only [read] using conditions)
      exact ⟨⟨M,belongs⟩,funext read⟩

end CriticalDoubleTilt

namespace CriticalDoubleTilt

/-- A direct old `k`-mark specimen yields two direct relations sharing one
point after increasing the first dimension by one. Exactly `b-1` unmarked
samples are added. -/
theorem fin_paired_lift {a b r k : ℕ} (ha : 0<a) (hb : 5≤b) (hk : 0<k)
    (level : r+1=(a-1)*(b-1)) (room : 2*k+1≤r)
    (one : ∃ mark : Fin k ↪ Fin r, ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
      ∀ F : Fin k → Fin a × Fin b → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin b,(x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j,y (mark t) j*F t (i,j)=0) → (∀ t j, ∑ i,x (mark t) i*F t (i,j)=0) →
        (∑ t,F t)=0 → F=0) :
    ∃ mark : (Fin k ⊕ (Fin k ⊕ Unit)) ↪ Fin (r+(b-1)),
    ∃ x : Fin (r+(b-1)) → Fin (a+1) → ℂ, ∃ y : Fin (r+(b-1)) → Fin b → ℂ,
      ∀ M : (Fin k ⊕ (Fin k ⊕ Unit)) → Fin (a+1) × Fin b → ℂ, (∀ t,Normal x y (mark t) (M t)) →
        (∑ i : Fin k,M (.inl i))+M (.inr (.inr ()))=0 →
        (∑ i : Fin k,M (.inr (.inl i)))+M (.inr (.inr ()))=0 → M=0 := by
  classical
  let T := Fin k ⊕ (Fin k ⊕ Unit)
  let U := Fin a → ℂ
  let V := Fin b → ℂ
  obtain ⟨m,_,x,y,_,_,triples,dimension,oldA,oldB⟩ :=
    exists_prepared_marking ha (by omega : 3≤b) level room one
  let D := pairedSpace x y m
  let β (i : Fin 2) (s : T) : ℂ := s.elim (fun _ => if i=0 then 1 else 0)
    (Sum.elim (fun _ => if i=1 then 1 else 0) (fun _ => 1))
  obtain ⟨F,_,tag,complete⟩ := prepared_bilinear_family x y m
  have tested (e : Fin 3 ↪ T) : LinearIndependent ℂ (fun i => y (m (e i))) := triples (e.trans m)
  have testA (d : D) (h : ∀ i : Fin k,F d (.inl i)=0) : d=0 :=
    oldA d (fun i => (tag d (.inl i)).mp (h i))
  have testB (d : D) (h : ∀ i : Fin k,F d (.inr (.inl i))=0) : d=0 :=
    oldB d (fun i => (tag d (.inr (.inl i))).mp (h i))
  have rankV : Module.finrank ℂ V=b := by simp only [V,Module.finrank_fintype_fun_eq_card,Fintype.card_fin]
  obtain ⟨uA,uB,zA,zB,h,lA,lB,hzA,hzB,hy,aa,ab,ba,bb,detect⟩ :=
    two_pole_cut (D:=D) (U:=U) (V:=V) k hk dimension (by rw [rankV]; exact hb)
      (fun t : T => y (m t)) F tested testA testB
  have hh : h≠0 := fun eq => hy (.inr (.inr ())) (by rw [eq]; rfl)
  obtain ⟨X,Y,_,_,kills⟩ := paired_lift_of_family x y (fun t : T => m t) β F
    (fun G sample left right weights => (complete G).mpr ⟨sample,left,right,weights⟩)
    h lA lB hh hy uA uB zA zB hzA hzB aa ab ba bb detect
  let S := Fin r ⊕ Fin (Module.finrank ℂ V-1)
  let ids : S ≃ Fin (r+(b-1)) := finSumFinEquiv.trans (finCongr (by rw [rankV]))
  have rankU : Module.finrank ℂ (U × ℂ)=a+1 := by
    simp only [U,Module.finrank_prod,Module.finrank_fintype_fun_eq_card,Fintype.card_fin,Module.finrank_self]
  let coord := ((Module.finBasis ℂ (U × ℂ)).reindex (finCongr rankU)).equivFun
  let mark : T ↪ Fin (r+(b-1)) := (m.trans Function.Embedding.inl).trans ids.toEmbedding
  let xx (i : Fin (r+(b-1))) := coord (X (ids.symm i))
  let yy (i : Fin (r+(b-1))) := Y (ids.symm i)
  have back (t : T) : ids.symm (mark t)=Sum.inl (m t) := ids.symm_apply_apply _
  refine ⟨mark,xx,yy,?_⟩
  intro M normal left right
  obtain ⟨E,action⟩ := bilinear_coordinates (a+1) b
  let G (t : T) := (E (M t)).comp coord.toLinearMap
  have all (t : T) := (normal_iff_bilinear xx yy (mark t) E action (M t)).mp (normal t)
  have point (t : T) (i : S) : G t (X i) (Y i)=0 := by
    simpa only [G,xx,yy,LinearMap.comp_apply,LinearEquiv.coe_coe,ids.symm_apply_apply] using (all t).1 (ids i)
  have atY (t : T) (u : U × ℂ) : G t u (Y (.inl (m t)))=0 := by
    simpa only [G,yy,LinearMap.comp_apply,LinearEquiv.coe_coe,back] using (all t).2.1 (coord u)
  have atX (t : T) (v : V) : G t (X (.inl (m t))) v=0 := by
    simpa only [G,xx,LinearMap.comp_apply,LinearEquiv.coe_coe,back] using (all t).2.2 v
  have weights := (paired_sum_iff (K:=ℂ) k M).mpr ⟨left,right⟩
  have lifted (c : Fin 2) : (∑ t,β c t • G t)=0 := by
    have raw := congrArg E (weights c)
    have forms : (∑ t : T,β c t • E (M t))=0 := by simpa only [map_sum,map_smul,map_zero] using raw
    apply LinearMap.ext
    intro p
    have eq := LinearMap.congr_fun forms (coord p)
    simpa only [G,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearMap.zero_apply] using eq
  have zero := kills G point atY atX lifted
  funext t
  change M t=0
  apply E.injective
  rw [map_zero]
  apply LinearMap.ext
  intro p
  have eq := congrArg (fun B : T → (U × ℂ) →ₗ[ℂ] (V →ₗ[ℂ] ℂ) => B t (coord.symm p)) zero
  simpa only [G,LinearMap.comp_apply,LinearEquiv.coe_coe,coord.apply_symm_apply,Pi.zero_apply,
    LinearMap.zero_apply] using eq

end CriticalDoubleTilt

namespace CriticalDoubleTiltCompletion

abbrev Ordinary (a b r k : ℕ) : Prop :=
  ∃ mark : Fin k ↪ Fin r, ∃ x : Fin r→Fin a→ℂ, ∃ y : Fin r→Fin b→ℂ,
  ∀ F : Fin k→Fin a × Fin b→ℂ,
    (∀ t s, (∑ ij : Fin a × Fin b,(x s ij.1*y s ij.2)*F t ij)=0) →
    (∀ t i,(∑ j,y (mark t) j*F t (i,j))=0) →
    (∀ t j,(∑ i,x (mark t) i*F t (i,j))=0) → (∑ t,F t)=0 → F=0

/-- There are enough old samples to select two disjoint batches and a
shared point, even at the smallest relevant dimensions. -/
theorem old_counts {a b : ℕ} (four : 4≤a) (wide : a+3≤b) (odd : Odd (a+b)) :
    let k := (a+b)/2
    let r₀ := (a-2)*(b-1)-1
    0<k ∧ 2*k+1≤r₀ ∧ r₀+1=(a-1-1)*(b-1) ∧ (a-1+b)/2=k ∧
      r₀+(b-1)=(a-1)*(b-1)-1 := by
  intro k r₀
  obtain ⟨i,ai⟩ : ∃ i,a=i+4 := ⟨a-4,by omega⟩
  obtain ⟨j,bj⟩ : ∃ j,b=i+7+j := ⟨b-(i+7),by omega⟩
  obtain ⟨l,eq⟩ := odd
  have parity : 2*k+1=a+b := by dsimp only [k]; omega
  have p : (a-2)*(b-1)=i^2+i*j+8*i+2*j+12 := by
    rw [ai,bj,show i+4-2=i+2 by omega,show i+7+j-1=i+6+j by omega]
    ring
  have big : (a-1)*(b-1)=(a-2)*(b-1)+(b-1) := by
    rw [show a-1=(a-2)+1 by omega,Nat.add_mul,Nat.one_mul]
  dsimp only [r₀]
  refine ⟨by omega,?_,?_,?_,?_⟩
  · rw [p,parity]
    omega
  · rw [show a-1-1=a-2 by omega,p]
    omega
  · dsimp only [k]
    omega
  · rw [big,p]
    omega

/-- At the potentially overflowing odd levels, the old right dimension
is large enough for two independent choices of poles. -/
theorem right_large {a b : ℕ} (four : 4≤a) (wide : a+3≤b)
    (deficit : (2*((a-1)*(b-1)-1) ⌈/⌉ (a+b))*((a+b)/2)<(a-1)*(b-1)-1) :
    8≤b := by
  by_contra! small
  obtain ⟨rfl,rfl⟩ : a=4 ∧ b=7 := by omega
  exact (by decide : ¬(2*((4-1)*(7-1)-1) ⌈/⌉ (4+7))*((4+7)/2)<(4-1)*(7-1)-1) deficit

/-- Only the already isolated extreme ordinary marking can occur as an
exception when applying the existing large-rectangle construction to
the old core. -/
theorem old_marking {a b : ℕ} (four : 4≤a) (wide : a+3≤b) (odd : Odd (a+b))
    (deficit : (2*((a-1)*(b-1)-1) ⌈/⌉ (a+b))*((a+b)/2)<(a-1)*(b-1)-1)
    (exceptional : ∀ u : ℕ, 4≤u → Ordinary u (3*u-2) ((u-1)*(3*u-2-1)-1) ((u+(3*u-2))/2)) :
    Ordinary (a-1) b ((a-2)*(b-1)-1) ((a+b)/2) := by
  have large := right_large four wide deficit
  have marks := (old_counts four wide odd).2.2.2.1
  rw [←marks,show a-2=a-1-1 by omega]
  by_cases hit : b+2=3*(a-1)
  · have da : 4≤a-1 := by omega
    have dim : 3*(a-1)-2=b := by omega
    simpa only [dim] using exceptional (a-1) da
  exact CriticalLastSlice.TwoPlanes.Cross.half_batch (by omega) (by omega) (Or.inr large) hit

end CriticalDoubleTiltCompletion

namespace CriticalDoubleTiltCompletion

/-- Both normal directions are independent on the previously exceptional
rectangle. The core supplies a separated family and the appended columns
supply the transverse directions. -/
theorem ordinary_extreme (a : ℕ) (ha : 4≤a) :
    Ordinary a (3*a-2) ((a-1)*(3*a-2-1)-1) ((a+(3*a-2))/2) := by
  rw [show (a+(3*a-2))/2=2*a-1 by omega]
  exact CriticalExtreme.extreme_marked_batch a ha

/-- The two exclusive sums and their shared normal are separated by the
two poles after extending the first axis of an ordinary core. -/
theorem complete_paired :
    CriticalTwoNormalReduction.H2 := by
  intro a b ha gap _ odd r k deficit
  let r₀ := (a-2)*(b-1)-1
  have dims := old_counts ha gap odd
  change 0<k ∧ 2*k+1≤r₀ ∧ r₀+1=(a-1-1)*(b-1) ∧ (a-1+b)/2=k ∧ r₀+(b-1)=r at dims
  have right := right_large ha gap deficit
  have old := old_marking ha gap odd deficit ordinary_extreme
  have lifted := CriticalDoubleTilt.fin_paired_lift (a:=a-1) (b:=b) (r:=r₀) (k:=k)
    (by omega) (by omega) dims.1 dims.2.2.1 dims.2.1 old
  rw [Nat.sub_add_cancel (by omega : 1≤a),dims.2.2.2.2] at lifted
  obtain ⟨mark,x,y,detect⟩ := lifted
  refine ⟨mark,x,y,?_⟩
  intro F outer rows cols first second
  exact detect F (fun t => ⟨outer t,rows t,cols t⟩) first second

end CriticalDoubleTiltCompletion

/-- The defining rank-normal relation of the registered parent vanishes
throughout its entire two-dimensional level. -/
theorem OMA.solution :
    OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H1 :=
  CriticalTwoNormalReduction.main
    (fun a ha => CriticalDoubleTiltCompletion.ordinary_extreme a (by omega))
    CriticalDoubleTiltCompletion.complete_paired
