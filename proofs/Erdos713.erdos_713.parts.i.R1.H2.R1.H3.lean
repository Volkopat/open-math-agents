import OMAReductions.R_Erdos713_erdos_713_parts_i_R1_H2_R1

-- Credit: @zarnab222-dev

/-!
# Sustained linear lower bounds for extremal numbers

Fix a forbidden graph F on q vertices without isolated vertices and a host X
avoiding F. Starting at a boundary B, enlarge B to Z by retaining witnesses
for every way part of F can attach to B. A maximal packing of small
realizations either supplies q+1 disjoint candidates or yields a bounded
hitting set. Hence parts realized outside Z can be realized again while
avoiding any q prescribed vertices.

Keep B and repeat copies of the body outside Z. A putative forbidden copy
uses at most q vertices in total, so its bodies can be placed disjointly back
in X. Of K successive layers Z minus B, one has total degree at most twice
the edge count of X divided by K. All edges inside Z contribute only a
constant depending on q and K. Thus, for a large enough host exceeding slope
b, the repeatable body contributes more than a edges per vertex for any
positive a below b. Repetition and padding attain every sufficiently large
order. This argument proves the mixed-forest step without needing a bound
on the lengths of paths in the host.
-/
/-! Repeating a graph piece with a fixed boundary preserves exclusion once
there are as many interchangeable copies as vertices in the pattern. -/
open Finset SimpleGraph
open scoped Classical
namespace E713Repeat

def fan {A W : Type*} (H : SimpleGraph A) (P : SimpleGraph W) (attach : A → W → Prop) (I : Type*) :
    SimpleGraph (A ⊕ (I × W)) where
  Adj x y := match x,y with
    | .inl a,.inl b => H.Adj a b
    | .inl a,.inr (_,v) | .inr (_,v),.inl a => attach a v
    | .inr (i,u),.inr (j,v) => i=j ∧ P.Adj u v
  symm := ⟨by rintro (a|⟨i,u⟩) (b|⟨j,v⟩) hab
              · exact hab.symm
              · exact hab
              · exact hab
              · exact ⟨hab.1.symm,hab.2.symm⟩⟩
  loopless := ⟨by rintro (a|⟨i,u⟩)
                  · exact H.loopless.irrefl a
                  · exact fun h => h.2.ne rfl⟩

noncomputable def mass {A W : Type*} [Fintype A] [Fintype W] (P : SimpleGraph W)
    (attach : A → W → Prop) : ℕ :=
  (∑ a : A, (univ.filter (attach a)).card) +
  ∑ w : W, ((univ.filter fun a => attach a w).card + P.degree w)

theorem count {A W I : Type*} [Fintype A] [Fintype W] [Fintype I]
    (H : SimpleGraph A) (P : SimpleGraph W) (attach : A → W → Prop) :
    2*(fan H P attach I).edgeFinset.card = 2*H.edgeFinset.card + Fintype.card I * mass P attach := by
  classical
  let X := fan H P attach I
  let L (a : A) := univ.filter (attach a)
  let R (w : W) := univ.filter fun a => attach a w
  have left (a : A) : X.neighborFinset (.inl a) = (H.neighborFinset a).disjSum (univ ×ˢ L a) := by
    ext v
    rw [X.mem_neighborFinset]
    cases v with
    | inl b => simp [SimpleGraph.mem_neighborFinset,X,fan]
    | inr x => obtain ⟨i,w⟩ := x; simp [X,fan,L]
  have right (i : I) (w : W) : X.neighborFinset (.inr (i,w)) =
      (R w).disjSum (({i}:Finset I) ×ˢ P.neighborFinset w) := by
    ext v
    rw [X.mem_neighborFinset]
    cases v with
    | inl a => simp [X,fan,R]
    | inr x => obtain ⟨j,z⟩ := x; simp [SimpleGraph.mem_neighborFinset,X,fan,eq_comm,and_comm]
  have dl (a : A) : X.degree (.inl a) = H.degree a + Fintype.card I*(L a).card := by
    rw [← X.card_neighborFinset_eq_degree,left,card_disjSum,card_product,card_univ,H.card_neighborFinset_eq_degree]
  have dr (i : I) (w : W) : X.degree (.inr (i,w)) = (R w).card + P.degree w := by
    rw [← X.card_neighborFinset_eq_degree,right,card_disjSum,card_product]
    simp
  change 2*X.edgeFinset.card = _
  rw [← X.sum_degrees_eq_twice_card_edges,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [dl,dr,sum_add_distrib,← mul_sum,sum_const,card_univ,smul_eq_mul,
    H.sum_degrees_eq_twice_card_edges]
  unfold mass
  simp only [sum_add_distrib]
  change _ = 2*H.edgeFinset.card + Fintype.card I*((∑ a, (L a).card) + ((∑ w,(R w).card)+∑ w,P.degree w))
  ring

end E713Repeat

/-! Bounded families of representatives for anchored embeddings. -/
open Finset SimpleGraph
open scoped Classical
namespace E713Mixed

/-- For a family of small sets, a bounded set of vertices either meets every
member, or there are enough disjoint members to avoid any prescribed blocker. -/
theorem capture {W : Type*} [Fintype W] (P : Finset (Finset W)) (q r : ℕ)
    (size : ∀ t ∈ P, t.card ≤ r) :
    ∃ Z : Finset W, Z.card ≤ q*r ∧
      ((∀ t ∈ P, ¬ Disjoint t Z) ∨
       ∀ D : Finset W, D.card < q → ∃ t ∈ P, Disjoint t D) := by
  classical
  by_cases empty : ∅ ∈ P
  · exact ⟨∅,by simp,Or.inr (fun D _ => ⟨∅,empty,by simp⟩)⟩
  let good : Finset (Finset (Finset W)) := P.powerset.filter fun (S : Finset (Finset W)) => (S : Set (Finset W)).PairwiseDisjoint id
  have seed : ∅ ∈ good := by simp [good]
  obtain ⟨S,hs,maxi⟩ := exists_max_image good Finset.card ⟨_,seed⟩
  obtain ⟨sub,pair⟩ := mem_filter.mp hs
  have sub' := mem_powerset.mp sub
  by_cases small : S.card < q
  · refine ⟨S.biUnion id,?_,Or.inl ?_⟩
    · calc (S.biUnion id).card ≤ ∑ t ∈ S, t.card := card_biUnion_le
           _ ≤ ∑ _ ∈ S, r := sum_le_sum fun t ht => size t (sub' ht)
           _ ≤ q*r := by simpa [smul_eq_mul] using Nat.mul_le_mul_right r small.le
    · intro t ht dis
      by_cases h : t ∈ S
      · have inside : t ⊆ S.biUnion id := fun x hx => mem_biUnion.mpr ⟨t,h,hx⟩
        by_cases e : t.Nonempty
        · obtain ⟨x,hx⟩ := e
          exact Finset.disjoint_left.mp dis hx (inside hx)
        · exact empty ((by simpa only [nonempty_iff_ne_empty,not_not] using e : t = ∅) ▸ ht)
      have covered (w : Finset W) (hw : w ∈ S) : w ⊆ S.biUnion id :=
        fun x hx => mem_biUnion.mpr ⟨w,hw,hx⟩
      have added : insert t S ∈ good := by
        apply mem_filter.mpr
        refine ⟨mem_powerset.mpr (insert_subset ht sub'),?_⟩
        intro u hu v hv ne
        change u ∈ insert t S at hu
        change v ∈ insert t S at hv
        rcases mem_insert.mp hu with rfl | hu0
        · rcases mem_insert.mp hv with rfl | hv0
          · exact (ne rfl).elim
          · exact dis.mono_right (covered v hv0)
        · rcases mem_insert.mp hv with rfl | hv0
          · exact (dis.mono_right (covered u hu0)).symm
          · exact pair hu0 hv0 ne
      have bound := maxi _ added
      rw [card_insert_of_notMem h] at bound
      omega
  · refine ⟨∅,by simp,Or.inr ?_⟩
    intro D d
    by_contra! bad
    have hit (t : S) : ∃ x : D, x.val ∈ t.val := by
      have nd := bad t.val (sub' t.property)
      rw [Finset.not_disjoint_iff] at nd
      obtain ⟨x,ht,hx⟩ := nd
      exact ⟨⟨x,hx⟩,ht⟩
    choose f hf using hit
    have inject : Function.Injective f := by
      intro u v eq
      by_contra ne
      have sep := pair u.property v.property (fun h => ne (Subtype.ext h))
      exact Finset.disjoint_left.mp sep (hf u) (eq.symm ▸ hf v)
    have cap := Fintype.card_le_of_injective f inject
    simp only [Fintype.card_coe] at cap
    omega
/-- A realization preserves edges inside S and all required incidences to the
individually specified boundary vertices. The image lives outside the boundary. -/
def Realizes {V W : Type*} (F : SimpleGraph V) (X : SimpleGraph W) (B : Finset W)
    (S : Finset V) (labels : V → Option B) (T : Finset W) : Prop :=
  Disjoint T B ∧ ∃ e : S ≃ T,
    (∀ x y : S, F.Adj x.val y.val → X.Adj (e x).val (e y).val) ∧
    ∀ x : S, ∀ v b, labels v=some b → F.Adj x.val v → X.Adj (e x).val b.val

theorem stage {V W : Type*} [Fintype V] [Fintype W] (F : SimpleGraph V) (X : SimpleGraph W)
    (B : Finset W) :
    ∃ Z : Finset W, B ⊆ Z ∧ Z.card ≤ B.card +
       (2^Fintype.card V * (B.card+1)^Fintype.card V) * ((Fintype.card V+1)*Fintype.card V) ∧
      ∀ (S : Finset V) (labels : V → Option B) (T : Finset W), Realizes F X B S labels T →
        Disjoint T Z → ∀ (D : Finset W), D.card ≤ Fintype.card V →
          ∃ T' : Finset W, Realizes F X B S labels T' ∧ Disjoint T' D := by
  classical
  let q := Fintype.card V
  let A := Finset V × (V → Option B)
  let family (a : A) := univ.filter (Realizes F X B a.1 a.2)
  have bound (a : A) (t) (h : t ∈ family a) : t.card ≤ q := by
    obtain ⟨_,e,_⟩ := (mem_filter.mp h).2
    have sz := Fintype.card_congr e
    simp only [Fintype.card_coe] at sz
    exact sz ▸ card_le_univ a.1
  choose C size dich using (fun a : A => capture (family a) (q+1) q (bound a))
  let Z := B ∪ univ.biUnion C
  refine ⟨Z,subset_union_left,?_,?_⟩
  · have ntypes : Fintype.card A = 2^q*(B.card+1)^q := by simp [A,q,Fintype.card_finset]
    have union := card_biUnion_le (s:=(univ : Finset A)) (t:=C)
    have total := sum_le_sum (s:=(univ : Finset A)) (fun a _ => size a)
    rw [sum_const,card_univ,smul_eq_mul,ntypes] at total
    exact (card_union_le ..).trans (Nat.add_le_add_left (union.trans total) _)
  · intro S labels T model untouched D cap
    let a : A := (S,labels)
    have h : T ∈ family a := mem_filter.mpr ⟨mem_univ _,model⟩
    rcases dich a with stop | supply
    · exact (stop T h (untouched.mono_right (fun x hx => mem_union_right B (mem_biUnion.mpr ⟨a,mem_univ _,hx⟩)))).elim
    · obtain ⟨T',ht,hd⟩ := supply D (by change D.card < Fintype.card V+1; omega)
      exact ⟨T',(mem_filter.mp ht).2,hd⟩

theorem choose_disjoint {I W : Type*} [Fintype I] [Fintype W] (A : I → Type*)
    [∀ i, Fintype (A i)] (valid : ∀ i, (A i ↪ W) → Prop) (q : ℕ)
    (space : ∑ i, Fintype.card (A i) ≤ q)
    (supply : ∀ i (D : Finset W), D.card ≤ q →
      ∃ f : A i ↪ W, valid i f ∧ Disjoint (univ.map f) D) :
    ∃ f : ∀ i, A i ↪ W, (∀ i, valid i (f i)) ∧
      ∀ i j, i ≠ j → Disjoint (univ.map (f i)) (univ.map (f j)) := by
  classical
  choose seed hseed using (fun i => supply i ∅ (by simp))
  have go (P : Finset I) : ∃ f : ∀ i, A i ↪ W, (∀ i ∈ P, valid i (f i)) ∧
      ∀ i ∈ P, ∀ j ∈ P, i ≠ j → Disjoint (univ.map (f i)) (univ.map (f j)) := by
    induction P using Finset.induction_on with
    | empty => exact ⟨seed,by simp,by simp⟩
    | @insert i P ni ih =>
      obtain ⟨f,ok,sep⟩ := ih
      let D := P.biUnion fun j => univ.map (f j)
      have size : D.card ≤ q := by
        calc D.card ≤ ∑ j ∈ P, (univ.map (f j)).card := card_biUnion_le
             _ = ∑ j ∈ P, Fintype.card (A j) := by simp
             _ ≤ ∑ j, Fintype.card (A j) := sum_le_sum_of_subset (subset_univ _)
             _ ≤ q := space
      obtain ⟨g,good,away⟩ := supply i D size
      let h := Function.update f i g
      have eq : h i = g := Function.update_self ..
      have same {j} (hj : j ∈ P) : h j = f j := Function.update_of_ne (show j ≠ i from fun e => ni (e ▸ hj)) ..
      have far (j) (hj : j ∈ P) : Disjoint (univ.map g) (univ.map (f j)) :=
        away.mono_right (fun _ hx => mem_biUnion.mpr ⟨j,hj,hx⟩)
      refine ⟨h,?_,?_⟩
      · intro j hj
        rcases mem_insert.mp hj with rfl | hp
        · simpa only [eq] using good
        · rw [same hp]; exact ok _ hp
      · intro j hj k hk ne
        rcases mem_insert.mp hj with rfl | hp
        · rcases mem_insert.mp hk with rfl | hq
          · exact (ne rfl).elim
          · rw [eq,same hq]; exact far _ hq
        · rcases mem_insert.mp hk with rfl | hq
          · rw [same hp,eq]; exact (far _ hp).symm
          · rw [same hp,same hq]; exact sep _ hp _ hq ne
  obtain ⟨f,ok,sep⟩ := go univ
  exact ⟨f,fun i => ok _ (mem_univ i),fun i j => sep i (mem_univ _) j (mem_univ _)⟩

theorem fan_free {V W I : Type*} [Fintype V] [Fintype W] [Fintype I]
    (F : SimpleGraph V) (X : SimpleGraph W) (free : F.Free X) (B Z U : Finset W)
    (inc : B ⊆ Z) (outside : Disjoint U Z)
    (supply : ∀ (S : Finset V) (labels : V → Option B) (T : Finset W), Realizes F X B S labels T →
      Disjoint T Z → ∀ D : Finset W, D.card ≤ Fintype.card V →
        ∃ T' : Finset W, Realizes F X B S labels T' ∧ Disjoint T' D) :
    F.Free (E713Repeat.fan (⊥ : SimpleGraph B) (X.induce (U : Set W))
      (fun b u => X.Adj b.val u.val) I) := by
  classical
  rintro ⟨e⟩
  let labels (v : V) : Option B := match e v with
    | .inl b => some b
    | .inr _ => none
  let S (i : I) : Finset V := univ.filter fun v => ∃ w : U, e v = Sum.inr (i,w)
  have hit (v : V) (i : I) (w : U) (h : e v = Sum.inr (i,w)) : v ∈ S i :=
    mem_filter.mpr ⟨mem_univ _,w,h⟩
  have body (i : I) (v : S i) : ∃ w : U, e v.val = Sum.inr (i,w) := (mem_filter.mp v.property).2
  choose orig orig_eq using body
  have left {v : V} {b : B} (h : labels v = some b) : e v = Sum.inl b := by
    unfold labels at h
    split at h
    next c hc => exact hc.trans (congrArg Sum.inl (Option.some.inj h))
    next p hp => contradiction
  have cross (i : I) (u : S i) (v : V) (b : B) (lab : labels v = some b) (adj : F.Adj u.val v) :
      X.Adj (orig i u).val b.val := by
    have edge := e.toHom.map_rel' adj
    change (E713Repeat.fan _ _ _ I).Adj (e u.val) (e v) at edge
    rw [orig_eq,left lab] at edge
    exact (show X.Adj b.val (orig i u).val from edge).symm
  have inner (i : I) (u v : S i) (adj : F.Adj u.val v.val) : X.Adj (orig i u).val (orig i v).val := by
    have edge := e.toHom.map_rel' adj
    change (E713Repeat.fan _ _ _ I).Adj (e u.val) (e v.val) at edge
    rw [orig_eq,orig_eq] at edge
    exact edge.2
  let valid (i : I) (g : S i ↪ W) : Prop := (∀ x, g x ∉ B) ∧
    (∀ x y : S i, F.Adj x.val y.val → X.Adj (g x) (g y)) ∧
    ∀ x : S i, ∀ v b, labels v=some b → F.Adj x.val v → X.Adj (g x) b.val
  have fresh (i : I) (D : Finset W) (cap : D.card ≤ Fintype.card V) :
      ∃ g : S i ↪ W, valid i g ∧ Disjoint (univ.map g) D := by
    let f : S i ↪ W := ⟨fun x => (orig i x).val,by
      intro x y eq
      apply Subtype.ext
      apply e.injective
      change e x.val = e y.val
      rw [orig_eq,orig_eq]
      exact congrArg (fun w : U => Sum.inr (i,w)) (Subtype.ext eq)⟩
    let T := univ.map f
    have inside : T ⊆ U := by
      intro w hw
      obtain ⟨x,_,rfl⟩ := mem_map.mp hw
      exact (orig i x).property
    let eqv : S i ≃ T := Equiv.ofBijective (fun x => (⟨f x,mem_map.mpr ⟨x,mem_univ _,rfl⟩⟩ : T))
      ⟨fun _ _ h => f.injective (congrArg (fun z : T => z.val) h), by
       intro w
       obtain ⟨x,_,hx⟩ := mem_map.mp w.property
       exact ⟨x,Subtype.ext hx⟩⟩
    have model : Realizes F X B (S i) labels T :=
      ⟨outside.mono inside inc,eqv,inner i,cross i⟩
    obtain ⟨T',⟨apart,g,internal,external⟩,away⟩ := supply _ _ _ model (outside.mono_left inside) D cap
    let f' : S i ↪ W := g.toEmbedding.trans (Function.Embedding.subtype _)
    refine ⟨f',⟨fun x hx => Finset.disjoint_left.mp apart (g x).property hx,internal,external⟩,?_⟩
    apply away.mono_left
    intro w hw
    obtain ⟨x,_,rfl⟩ := mem_map.mp hw
    exact (g x).property
  have indexeq {i j : I} (x : S i) (y : S j) (h : x.val = y.val) : i=j := by
    have z := (orig_eq i x).symm.trans ((congrArg e h).trans (orig_eq j y))
    exact (Prod.mk.inj (Sum.inr.inj z)).1
  have space : ∑ i, Fintype.card (S i) ≤ Fintype.card V := by
    rw [← Fintype.card_sigma]
    apply Fintype.card_le_of_injective (fun p : (i : I) × S i => p.2.val)
    rintro ⟨i,x⟩ ⟨j,y⟩ eq
    obtain rfl := indexeq x y eq
    exact congrArg (Sigma.mk i) (Subtype.ext eq)
  obtain ⟨g,good,sep⟩ := choose_disjoint (fun i => ↥(S i)) valid _ space fresh
  let f (v : V) : W := match h : e v with
    | .inl b => b.val
    | .inr (i,w) => g i ⟨v,hit v i w h⟩
  have fl (v : V) (b : B) (h : e v = Sum.inl b) : f v=b.val := by
    unfold f
    split
    next c hc => exact congrArg Subtype.val (Sum.inl.inj (hc.symm.trans h))
    next j z hz => exact (Sum.inr_ne_inl (hz.symm.trans h)).elim
  have fr (v : V) (i : I) (w : U) (h : e v = Sum.inr (i,w)) : f v=g i ⟨v,hit v i w h⟩ := by
    unfold f
    split
    next c hc => exact (Sum.inl_ne_inr (hc.symm.trans h)).elim
    next j z hz =>
      have ij := (Prod.mk.inj (Sum.inr.inj (hz.symm.trans h))).1
      subst j
      rfl
  have lbl (v : V) (b : B) (h : e v = Sum.inl b) : labels v=some b := by simp [labels,h]
  apply free
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · intro u v adj
    have edge := e.toHom.map_rel' adj
    change (E713Repeat.fan _ _ _ I).Adj (e u) (e v) at edge
    cases hu : e u with
    | inl b =>
      cases hv : e v with
      | inl c => rw [hu,hv] at edge; exact edge.elim
      | inr p =>
        obtain ⟨i,w⟩ := p
        rw [fl _ _ hu,fr _ _ _ hv]
        exact ((good i).2.2 _ _ _ (lbl _ _ hu) adj.symm).symm
    | inr p =>
      obtain ⟨i,w⟩ := p
      cases hv : e v with
      | inl b =>
        rw [fr _ _ _ hu,fl _ _ hv]
        exact (good i).2.2 _ _ _ (lbl _ _ hv) adj
      | inr p =>
        obtain ⟨j,z⟩ := p
        rw [hu,hv] at edge
        obtain rfl : i=j := edge.1
        rw [fr _ _ _ hu,fr _ _ _ hv]
        exact (good i).2.1 _ _ adj
  · intro u v eq
    change f u=f v at eq
    cases hu : e u with
    | inl b =>
      cases hv : e v with
      | inl c =>
        rw [fl _ _ hu,fl _ _ hv] at eq
        exact e.injective (hu.trans ((congrArg Sum.inl (Subtype.ext eq)).trans hv.symm))
      | inr p =>
        obtain ⟨i,w⟩ := p
        rw [fl _ _ hu,fr _ _ _ hv] at eq
        exact ((good i).1 _ (eq ▸ b.property)).elim
    | inr p =>
      obtain ⟨i,w⟩ := p
      cases hv : e v with
      | inl b =>
        rw [fr _ _ _ hu,fl _ _ hv] at eq
        exact ((good i).1 _ (eq.symm ▸ b.property)).elim
      | inr p =>
        obtain ⟨j,z⟩ := p
        rw [fr _ _ _ hu,fr _ _ _ hv] at eq
        by_cases ij : i=j
        · subst j
          exact congrArg Subtype.val ((g i).injective eq)
        · have first : g i ⟨u,hit u i w hu⟩ ∈ univ.map (g i) := mem_map.mpr ⟨(⟨u,hit u i w hu⟩ : S i),mem_univ _,rfl⟩
          have second : g j ⟨v,hit v j z hv⟩ ∈ univ.map (g j) := mem_map.mpr ⟨(⟨v,hit v j z hv⟩ : S j),mem_univ _,rfl⟩
          exact (Finset.disjoint_left.mp (sep i j ij) first (eq.symm ▸ second)).elim

end E713Mixed
namespace E713Layers

def step (q b : ℕ) := b+(2^q*(b+1)^q)*((q+1)*q)

def limit (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => step q (limit q k)

theorem mono (q : ℕ) : Monotone (limit q) := by
  apply monotone_nat_of_le_succ
  intro k
  change limit q k ≤ limit q k+_
  omega

def FreeFan {V W : Type*} (F : SimpleGraph V) (X : SimpleGraph W) (B U : Finset W) : Prop :=
  ∀ l : ℕ, F.Free (E713Repeat.fan (⊥ : SimpleGraph B) (X.induce (U : Set W))
    (fun b u => X.Adj b.val u.val) (Fin l))

theorem light {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W] (F : SimpleGraph V)
    (X : SimpleGraph W) (free : F.Free X) (K : ℕ) (hK : 0<K) :
    ∃ B Z : Finset W, B ⊆ Z ∧ Z.card ≤ limit (Fintype.card V) K ∧ FreeFan F X B Zᶜ ∧
      K*(∑ v ∈ Z\B, X.degree v) ≤ 2*X.edgeFinset.card := by
  classical
  let q := Fintype.card V
  let E := 2*X.edgeFinset.card
  by_contra! fail
  have grow (k : ℕ) (hk : k ≤ K) : ∃ B : Finset W, B.card ≤ limit q k ∧
      k*(E+1) ≤ K*(∑ v ∈ B, X.degree v) := by
    induction k with
    | zero => exact ⟨∅,by simp [limit],by simp⟩
    | succ k ih =>
      obtain ⟨B,bsize,st⟩ := ih (by omega)
      obtain ⟨Z,inc,sz,supply⟩ := E713Mixed.stage F X B
      have size : Z.card ≤ limit q (k+1) := by
        refine sz.trans ?_
        change B.card + (2^q*(B.card+1)^q)*_ ≤ limit q k + (2^q*(limit q k+1)^q)*_
        gcongr
      have copies : FreeFan F X B Zᶜ := fun l => E713Mixed.fan_free F X free B Z Zᶜ inc
        (Finset.disjoint_left.mpr fun v hv hz => mem_compl.mp hv hz) supply
      have large := fail B Z inc (size.trans (mono q hk)) copies
      have s := Finset.sum_sdiff inc (f:=fun v => X.degree v)
      refine ⟨Z,size,?_⟩
      calc (k+1)*(E+1) = k*(E+1)+(E+1) := by ring
           _ ≤ K*(∑ v ∈ B, X.degree v) + K*(∑ v ∈ Z\B, X.degree v) := Nat.add_le_add st large
           _ = _ := by rw [← Nat.mul_add,Nat.add_comm,s]
  obtain ⟨B,_,sum⟩ := grow K le_rfl
  have cap := sum_le_sum_of_subset (f:=fun v => X.degree v) (subset_univ B)
  rw [X.sum_degrees_eq_twice_card_edges] at cap
  have h := sum.trans (Nat.mul_le_mul_left K cap)
  change K*(E+1) ≤ K*E at h
  rw [Nat.mul_add,Nat.mul_one] at h
  omega

end E713Layers

namespace E713Peel

theorem filter_card {V : Type*} (S : Finset V) (p : V → Prop) :
    (univ.filter (fun x : S => p x.val)).card = (S.filter p).card := by
  classical
  change (S.attach.filter _).card = _
  rw [Finset.filter_attach p S,card_map,card_attach]

theorem sum_on {V : Type*} (S : Finset V) (f : V → ℕ) : (∑ v : S, f v.val) = ∑ v ∈ S, f v :=
  Finset.sum_attach S f

theorem peel {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (B U : Finset V)
    (dis : Disjoint B U) (out : ∀ u ∈ U, ∀ v ∉ U, G.Adj u v → v ∈ B) :
    2*G.edgeFinset.card = 2*(G.induce (↑(Uᶜ) : Set V)).edgeFinset.card +
      E713Repeat.mass (G.induce (U : Set V)) (fun (b : B) (u : U) => G.Adj b.val u.val) := by
  classical
  let deg (T : Finset V) (v : V) := (T.filter (G.Adj v)).card
  have subdeg (T : Finset V) (x : T) : (G.induce (T : Set V)).degree x = deg T x.val := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have eq : (G.induce (T : Set V)).neighborFinset x = univ.filter (fun y : T => G.Adj x.val y.val) := by
      ext y
      simp [SimpleGraph.mem_neighborFinset]
    exact eq ▸ filter_card T (G.Adj x.val)
  have split (v : V) : G.degree v = deg U v + deg Uᶜ v := by
    have eq : U.filter (G.Adj v) ∪ Uᶜ.filter (G.Adj v) = G.neighborFinset v := by
      ext w
      simp [SimpleGraph.mem_neighborFinset]
      tauto
    have ds : Disjoint (U.filter (G.Adj v)) (Uᶜ.filter (G.Adj v)) :=
      Finset.disjoint_left.mpr fun w hw ht => (mem_compl.mp (mem_filter.mp ht).1) (mem_filter.mp hw).1
    rw [← G.card_neighborFinset_eq_degree,← eq,card_union_of_disjoint ds]
  have inc : B ⊆ Uᶜ := fun _ hv => mem_compl.mpr fun hu => Finset.disjoint_left.mp dis hv hu
  have internal (u) (hu : u ∈ U) : deg Uᶜ u = deg B u := by
    apply congrArg Finset.card
    ext v
    simp only [mem_filter,mem_compl]
    exact ⟨fun h => ⟨out u hu v h.1 h.2,h.2⟩,fun h => ⟨mem_compl.mp (inc h.1),h.2⟩⟩
  have cross : (∑ v ∈ B, deg U v) = ∑ v ∈ Uᶜ, deg U v := by
    apply sum_subset inc
    intro v hv nb
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact nb (out u (mem_filter.mp hu).1 v (mem_compl.mp hv) (mem_filter.mp hu).2.symm)
  have once (T : Finset V) : 2*(G.induce (T : Set V)).edgeFinset.card = ∑ v ∈ T, deg T v := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
    simp_rw [subdeg]
    exact sum_on _ _
  have left (b : B) : (univ.filter (fun u : U => G.Adj b.val u.val)).card = deg U b.val := filter_card _ _
  have right (u : U) : (univ.filter (fun b : B => G.Adj b.val u.val)).card = deg B u.val := by
    calc _ = (univ.filter (fun b : B => G.Adj u.val b.val)).card := by
           congr 1
           ext b
           simp [SimpleGraph.adj_comm]
         _ = _ := filter_card _ _
  rw [once,← G.sum_degrees_eq_twice_card_edges,← U.sum_add_sum_compl]
  simp_rw [split]
  have massEq : E713Repeat.mass (G.induce (U : Set V)) (fun (b : B) (u : U) => G.Adj b.val u.val) =
      (∑ b ∈ B, deg U b) + ((∑ u ∈ U, deg B u) + ∑ u ∈ U, deg U u) := by
    unfold E713Repeat.mass
    rw [sum_add_distrib]
    apply congrArg₂ Nat.add
    · exact (sum_congr rfl (fun b _ => left b)).trans (sum_on B (deg U))
    · apply congrArg₂ Nat.add
      · exact (sum_congr rfl (fun u _ => right u)).trans (sum_on U (deg B))
      · exact (sum_congr rfl (fun u _ => subdeg U u)).trans (sum_on U (deg U))
  rw [massEq]
  simp only [sum_add_distrib]
  have mid : (∑ x ∈ U, deg Uᶜ x) = ∑ x ∈ U, deg B x := sum_congr rfl internal
  rw [mid,← cross]
  ring

end E713Peel
namespace E713MixedCount
open E713Peel

noncomputable def into {W : Type*} (X : SimpleGraph W) (U : Finset W) (v : W) := (U.filter (X.Adj v)).card

theorem swap {W : Type*} (X : SimpleGraph W) (B U : Finset W) :
    (∑ b ∈ B, into X U b) = ∑ u ∈ U, into X B u := by
  classical
  simp only [into,Finset.card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro b hb
  rw [X.adj_comm b u]

theorem mass_eq {W : Type*} (X : SimpleGraph W) (B U : Finset W) :
    E713Repeat.mass (X.induce (U : Set W)) (fun (b : B) (u : U) => X.Adj b.val u.val) =
      2*(∑ b ∈ B, into X U b)+2*(X.induce (U : Set W)).edgeFinset.card := by
  classical
  have L (b : B) : (univ.filter (fun u : U => X.Adj b.val u.val)).card = into X U b.val :=
    filter_card _ _
  have R (u : U) : (univ.filter (fun b : B => X.Adj b.val u.val)).card = into X B u.val := by
    calc _ = (univ.filter (fun b : B => X.Adj u.val b.val)).card := by
           congr 1
           ext b
           simp [SimpleGraph.adj_comm]
         _ = _ := filter_card _ _
  unfold E713Repeat.mass
  rw [sum_add_distrib]
  have l := (sum_congr (s₁:=univ) rfl (fun b _ => L b)).trans (sum_on B (into X U))
  have r := (sum_congr (s₁:=univ) rfl (fun u _ => R u)).trans (sum_on U (into X B))
  calc _ = (∑ b ∈ B, into X U b) + ((∑ u ∈ U, into X B u) + 2*(X.induce (U : Set W)).edgeFinset.card) := by
           apply congrArg₂ Nat.add l
           exact congrArg₂ Nat.add r (X.induce (U : Set W)).sum_degrees_eq_twice_card_edges
       _ = _ := by rw [← swap X B U]; ring

theorem loss {W : Type*} [Fintype W] [DecidableEq W] (X : SimpleGraph W) (B Z : Finset W)
    (inc : B ⊆ Z) :
    2*X.edgeFinset.card ≤ E713Repeat.mass (X.induce (↑(Zᶜ) : Set W))
      (fun (b : B) (u : ↥(Zᶜ)) => X.Adj b.val u.val) +
      2*Z.card^2 + 2*∑ v ∈ Z\B, X.degree v := by
  classical
  let U := Zᶜ
  have strip := peel X Z U (Finset.disjoint_left.mpr fun v hv hw => mem_compl.mp hw hv) (by simp [U]; grind)
  have compl : Uᶜ=Z := by simp [U]
  rw [compl,mass_eq] at strip
  rw [mass_eq]
  have combined := Finset.sum_sdiff inc (f:=into X U)
  have mt (v : W) : into X U v ≤ X.degree v := by
    rw [← X.card_neighborFinset_eq_degree]
    apply card_le_card
    intro w hw
    exact (X.mem_neighborFinset _ _).mpr (mem_filter.mp hw).2
  have cut := sum_le_sum (s:=Z\B) (fun v _ => mt v)
  have cl := card_edgeFinset_le_card_choose_two (G:=X.induce (Z : Set W))
  have cardZ : Fintype.card (↑(Z : Set W)) = Z.card := Fintype.card_coe Z
  rw [cardZ] at cl
  have sq : Z.card.choose 2 ≤ Z.card^2 := by
    rw [Nat.choose_two_right]; have := Nat.div_le_self (Z.card*(Z.card-1)) 2
    exact this.trans (by simpa only [pow_two] using Nat.mul_le_mul_left Z.card (Nat.sub_le Z.card 1))
  change 2*X.edgeFinset.card ≤ 2*(∑ b ∈ B, into X U b)+2*(X.induce (U : Set W)).edgeFinset.card +
    2*Z.card^2 + 2*∑ v ∈ Z\B, X.degree v
  omega
end E713MixedCount
namespace E713Amplify
theorem padding {V W : Type*} [Fintype W] (G : SimpleGraph V) (active : ∀ v, ¬G.IsIsolated v)
    (X : SimpleGraph W) (free : G.Free X) (m : ℕ) (fit : Fintype.card W ≤ m) :
    X.edgeFinset.card ≤ extremalNumber m G := by
  classical
  let k := m-Fintype.card W
  let Z := X ⊕g (⊥ : SimpleGraph (Fin k))
  have hf : G.Free Z := by
    rintro ⟨e⟩
    have original (v : V) : ∃ w : W, e v = Sum.inl w := by
      cases h : e v with
      | inl w => exact ⟨w,rfl⟩
      | inr i =>
        obtain ⟨u,adj⟩ := exists_adj_iff_not_isIsolated.mpr (active v)
        have a := e.toHom.map_rel' adj
        change Z.Adj (e v) (e u) at a
        rw [h] at a
        cases hu : e u with
        | inl t => rw [hu] at a; exact (not_adj_sum_inl_inr t i a.symm).elim
        | inr j => rw [hu] at a; exact (sum_adj_inr.mp a).elim
    choose f he using original
    apply free
    refine ⟨⟨⟨f,?_⟩,?_⟩⟩
    · intro a b adj
      have h := e.toHom.map_rel' adj
      change Z.Adj (e a) (e b) at h
      rw [he a,he b] at h
      exact sum_adj_inl.mp h
    · intro a b eq
      exact e.injective ((he a).trans ((congrArg Sum.inl eq).trans (he b).symm))
  have sumedges : Z.edgeFinset.card=X.edgeFinset.card := by
    simp only [Z,edgeFinset_card]
    have eq := Fintype.card_congr (edgeSetSumEquiv (G:=X) (H:=(⊥ : SimpleGraph (Fin k))))
    simpa using eq
  have hh := card_edgeFinset_le_extremalNumber hf
  have sz : Fintype.card (W ⊕ Fin k)=m := by simp [k,fit]
  simpa only [sumedges,sz] using hh


theorem eventual (h s e : ℕ) (hs : 0 < s) (a : ℚ) (ha : 0 < a)
    (gap : 2*a*s < e) (f : ℕ → ℕ) (lower : ∀ m ≥ h, ((m-h)/s)*e ≤ 2*f m) :
    ∃ M, ∀ m ≥ M, a*m ≤ (f m : ℚ) := by
  obtain ⟨k,hk⟩ := exists_nat_gt ((2*a*(h+s))/(e-2*a*s))
  have pos : 0 < (e:ℚ)-2*a*s := sub_pos.mpr gap
  have pay := (div_lt_iff₀ pos).mp hk
  refine ⟨h+s*k,?_⟩
  intro m hm
  let l := (m-h)/s
  have fit : h ≤ m := by omega
  have kl : k ≤ l := (Nat.le_div_iff_mul_le hs).mpr (by rw [Nat.mul_comm]; omega)
  have tail := Nat.mod_lt (m-h) hs
  have div := Nat.mod_add_div (m-h) s
  have endpt : m ≤ h+l*s+s := by dsimp [l]; rw [Nat.mul_comm ((m-h)/s)]; omega
  have endQ : (m:ℚ) ≤ h+(l:ℚ)*s+s := by exact_mod_cast endpt
  have low : (l:ℚ)*e ≤ 2*(f m:ℚ) := by exact_mod_cast lower m fit
  have ge : (k:ℚ) ≤ l := by exact_mod_cast kl
  nlinarith [mul_le_mul_of_nonneg_left endQ ha.le, mul_le_mul_of_nonneg_right ge pos.le]

theorem amplify {V W : Type*} [Fintype V] [Fintype W] (F : SimpleGraph V)
    (active : ∀ v, ¬F.IsIsolated v) (X : SimpleGraph W) (B U : Finset W)
    (hu : U.Nonempty) (copies : E713Layers.FreeFan F X B U)
    (a : ℚ) (ha : 0 < a) (gain : 2*a*U.card <
      (E713Repeat.mass (X.induce (U : Set W)) (fun (b : B) (u : U) => X.Adj b.val u.val) : ℚ)) :
    ∃ M, ∀ m ≥ M, a*m ≤ (extremalNumber m F : ℚ) := by
  classical
  let e := E713Repeat.mass (X.induce (U : Set W)) (fun (b : B) (u : U) => X.Adj b.val u.val)
  apply eventual B.card U.card e (card_pos.mpr hu) a ha gain
  intro m hm
  let l := (m-B.card)/U.card
  let Y := E713Repeat.fan (⊥ : SimpleGraph B) (X.induce (U : Set W)) (fun b u => X.Adj b.val u.val) (Fin l)
  have fr : F.Free Y := copies l
  have fit : Fintype.card (B ⊕ (Fin l × U)) ≤ m := by
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe]
    have h := Nat.div_mul_le_self (m-B.card) U.card
    dsimp [l]
    omega
  have upper := padding F active Y fr m fit
  have eq : 2*Y.edgeFinset.card = 2*(⊥ : SimpleGraph B).edgeFinset.card + l*e := by
    calc _ = 2*(⊥ : SimpleGraph B).edgeFinset.card + Fintype.card (Fin l)*e := by
           convert! E713Repeat.count (I:=Fin l) (⊥ : SimpleGraph B) (X.induce (U : Set W))
             (fun (b : B) (u : U) => X.Adj b.val u.val) using 1 <;> congr! 3
           ext z
           simp only [SimpleGraph.mem_edgeFinset]
         _ = _ := by rw [Fintype.card_fin]
  change l*e ≤ _
  omega

end E713Amplify
namespace E713Mixed

/-- If the density of extremal hosts exceeds b arbitrarily late, then every
lower rational slope a is eventually attained. -/
theorem sustained {V : Type*} [Fintype V] (F : SimpleGraph V) (nbot : F ≠ ⊥)
    (active : ∀ v, ¬ F.IsIsolated v) (a b : ℚ) (ab : a < b)
    (high : ∀ N, ∃ n ≥ N, b*n < (extremalNumber n F : ℚ)) :
    ∃ M, ∀ m ≥ M, a*m ≤ (extremalNumber m F : ℚ) := by
  classical
  by_cases nonpos : a ≤ 0
  · exact ⟨0,fun m _ => (mul_nonpos_of_nonpos_of_nonneg nonpos (Nat.cast_nonneg _)).trans (Nat.cast_nonneg _)⟩
  have pos : 0<a := lt_of_not_ge nonpos
  obtain ⟨k,hk⟩ := exists_nat_gt (2*b/(b-a))
  let K := k+3
  have Kpos : (2:ℚ)<K := by dsimp [K]; push_cast; linarith [Nat.cast_nonneg k (α:=ℚ)]
  have enough : 0 < (K:ℚ)*(b-a)-2*b := by
    have val := (div_lt_iff₀ (sub_pos.mpr ab)).mp hk
    dsimp [K]; push_cast; nlinarith
  let L := E713Layers.limit (Fintype.card V) K
  obtain ⟨N,hN⟩ := exists_nat_gt ((K:ℚ)*L^2/((K:ℚ)*(b-a)-2*b))
  obtain ⟨n,hn,above⟩ := high (max N (L+1))
  have witness : ∃ X : SimpleGraph (Fin n), F.Free X ∧ X.edgeFinset.card = extremalNumber n F := by
    obtain ⟨X,_,ext⟩ := exists_isExtremal_free (V:=Fin n) nbot
    obtain ⟨fr,extreme⟩ := isExtremal_free_iff.mp ext
    refine ⟨X,fr,?_⟩
    convert! extreme using 1
    · congr! 2
    · rw [Fintype.card_fin]
  obtain ⟨X,free,eEq⟩ := witness
  have overX : b*n < (X.edgeFinset.card : ℚ) := by rw [eEq]; exact above
  obtain ⟨B,Z,inc,sz,repeatable,light⟩ := E713Layers.light F X free K (by dsimp [K]; omega)
  let U := Zᶜ
  have zsmall : Z.card<n := by change Z.card ≤ L at sz; omega
  have usize : U.card = n-Z.card := by simp [U,card_compl]
  have hu : U.Nonempty := card_pos.mp (by omega)
  let mass := E713Repeat.mass (X.induce (U : Set (Fin n))) (fun (b : B) (u : U) => X.Adj b.val u.val)
  apply E713Amplify.amplify F active X B U hu repeatable a pos
  change 2*a*U.card < (mass:ℚ)
  by_contra! cheap
  let loss := ∑ v ∈ Z\B, X.degree v
  have capNat : 2*X.edgeFinset.card ≤ mass+2*Z.card^2+2*loss := by
    exact E713MixedCount.loss X B Z inc
  have cap : 2*(X.edgeFinset.card : ℚ) ≤ mass+2*(Z.card:ℚ)^2+2*loss := by exact_mod_cast capNat
  have few : (K:ℚ)*loss ≤ 2*(X.edgeFinset.card:ℚ) := by exact_mod_cast light
  have us : (U.card : ℚ) ≤ n := by exact_mod_cast (show U.card ≤ n by omega)
  have zs : (Z.card : ℚ)^2 ≤ (L:ℚ)^2 := by gcongr
  have pay : (K:ℚ)*L^2 < n*((K:ℚ)*(b-a)-2*b) :=
    (div_lt_iff₀ enough).mp (hN.trans_le (by exact_mod_cast (le_max_left N (L+1)).trans hn))
  have bound : (X.edgeFinset.card : ℚ) ≤ a*n+(L:ℚ)^2+loss := by
    nlinarith only [cap,cheap,zs,mul_le_mul_of_nonneg_left us pos.le]
  have scaled := mul_le_mul_of_nonneg_left bound (show (0:ℚ)≤K by positivity)
  have opp := mul_lt_mul_of_pos_left overX (sub_pos.mpr Kpos)
  nlinarith only [scaled,opp,few,pay]

end E713Mixed
theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_i_R1_H2_R1.H3 := by
  classical
  intro q F _ _ _ active _ vertex _ _ a b ab high
  apply E713Mixed.sustained F _ active a b ab high
  rintro rfl
  obtain ⟨v,h⟩ := vertex
  simp at h
