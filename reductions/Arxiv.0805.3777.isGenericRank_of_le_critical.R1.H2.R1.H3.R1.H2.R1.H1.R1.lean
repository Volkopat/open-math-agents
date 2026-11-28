import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1

/-! # Marked bilinear normals for complex tensor rank

At r=(a−1)(b−1)−1, the dimension count gives 2r≤(r−n)(a+b).
We construct ordinary markings by splitting the column coordinates into
two blocks. This settles all admissible third dimensions for b≥a(2a−1).
For odd square first factors, three cyclic diagonals and Fourier inversion
give the full marking. In particular, k × k × (k−1)(k−2) has generic rank
k(k−2) for every odd k≥5.

For the other pairs of sides, a single ordinary or paired marking can be
specialized simultaneously to all needed batches. The three-slice case
reduces to one finite tangent witness at 3 × 14 × 22. The two other hypotheses
concern only the first two dimensions. Their equations are over the complex
numbers and mention neither a third vector nor the rational-function field.

The rank prediction is Friedland's Conjecture 5.1 (https://arxiv.org/abs/0805.3777).
The tensor model is from the Formal Conjectures Authors. The parameter-count
and tangent bounds come from https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3300.
The conic marking and ragged-batch lemmas come from the parent construction,
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12200.
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

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H1_R1

open CriticalLastSlice.TwoPlanes

/-- The only three-slice format on this level which exceeds the ordinary
batch capacity is 3 × 14 × 22. -/
def H1 : Prop :=
  ∃ x : Fin 25 → Fin 3 → ℂ, ∃ y : Fin 25 → Fin 14 → ℂ, ∃ z : Fin 25 → Fin 22 → ℂ,
    ∀ T : Fin 3 → Fin 14 → Fin 22 → ℂ, ∃ u : Fin 25 → Fin 3 → ℂ,
      ∃ v : Fin 25 → Fin 14 → ℂ, ∃ w : Fin 25 → Fin 22 → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))

/-- In the remaining ordinary formats, find a single independent family of
marked normal planes. The number of samples and marks uses only a and b. -/
def H2 : Prop :=
  ∀ a b : ℕ, 4≤a → a≤b →
    ((b=a ∧ ¬Odd a) ∨ b=a+1 ∨ b=a+2 ∨ b+2=3*a) →
    let r := (a-1)*(b-1)-1
    let h := (a+b)/2
    ∃ mark : Fin h ↪ Fin r, ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
      ∀ F : Fin h → Fin a × Fin b → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j, y (mark t) j*F t (i,j)=0) →
        (∀ t j, ∑ i, x (mark t) i*F t (i,j)=0) → (∑ t,F t)=0 → F=0

/-- In odd ambient dimension, two batches can share one marked point.
Only pairs where the minimum relation count overflows the ordinary batches
and the rectangular tail has not started need such a specimen. -/
def H3 : Prop :=
  ∀ a b : ℕ, 4≤a → a≤b → b<a*(2*a-1) → Odd (a+b) →
    let r := (a-1)*(b-1)-1
    let h := (a+b)/2
    (2*r ⌈/⌉ (a+b))*h<r →
    ∃ mark : (Fin h ⊕ Fin h ⊕ Unit) ↪ Fin r,
      ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ,
      ∀ F : (Fin h ⊕ Fin h ⊕ Unit) → Fin a × Fin b → ℂ,
        (∀ t s, ∑ ij : Fin a × Fin b, (x s ij.1*y s ij.2)*F t ij=0) →
        (∀ t i, ∑ j, y (mark t) j*F t (i,j)=0) →
        (∀ t j, ∑ i, x (mark t) i*F t (i,j)=0) →
        (∑ i : Fin h,F (.inl i))+F (.inr (.inr ()))=0 →
        (∑ i : Fin h,F (.inr (.inl i)))+F (.inr (.inr ()))=0 → F=0

/-- Independent ordinary markings propagate by genericity to every small
batch simultaneously. In odd dimension, pairs of batches share their surplus
point. Realizing all these relations as a kernel supplies the third factor. -/
theorem main : H1 → H2 → H3 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1.H1 := by
  intro finiteMark ordinary paired a b c ha hab hbc region w r level
  change r+1=(a-1)*(b-1) at level
  by_cases three : a=3
  · subst a
    exact ThreePlaneTail.registered_three_iff_fourteen.mpr finiteMark b c hab hbc region level
  have four : 4≤a := by omega
  obtain ⟨_,enough,budget⟩ := relation_budget a b c r ha hab level rfl
  apply (witness_iff_normals (a:=a) (b:=b) enough).mp
  by_cases long : a*(2*a-1)≤b
  · exact Cross.tangent_tail ha long level rfl
  by_cases square : b=a ∧ Odd a
  · obtain ⟨rfl,odd⟩ := square
    exact square_spans_of_odd ha odd level enough (by simpa only [two_mul] using budget)
  have dim : r=(a-1)*(b-1)-1 := by omega
  apply spans_of_capacity_markings enough budget
  · intro fit
    refine ⟨(a+b)/2,fit,?_⟩
    rw [dim]
    by_cases split : a+3≤b ∧ b+2≠3*a
    · exact Cross.half_batch ha split.1 (Or.inl four) split.2
    · apply ordinary a b four hab
      by_cases equal : b=a
      · exact Or.inl ⟨equal,fun odd => square ⟨equal,odd⟩⟩
      · exact Or.inr (by omega)
  · intro overflow
    have odd : Odd (a+b) := by
      rcases capacity_cases budget with fit|⟨_,_,_,parity,_,_⟩
      · exact (not_lt_of_ge fit overflow).elim
      · exact ⟨(a+b)/2,parity⟩
    have minRows : (2*r ⌈/⌉ (a+b)) ≤ r-(c+1) := by
      apply (ceilDiv_le_iff_le_mul (by omega : 0<a+b)).mpr
      exact budget.trans_eq (Nat.mul_comm _ _)
    have deficit := lt_of_le_of_lt (Nat.mul_le_mul_right ((a+b)/2) minRows) overflow
    have specimen := paired a b four hab (by omega) odd
    dsimp only at specimen
    rw [← dim] at specimen
    exact specimen deficit

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H1_R1
