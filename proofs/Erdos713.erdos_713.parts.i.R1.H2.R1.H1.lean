import OMAReductions.R_Erdos713_erdos_713_parts_i_R1_H2_R1

/-!
# Proof of `Erdos713.erdos_713.parts.i.R1.H2.R1.H1`

Proves sustained linear lower density transfer for disconnected linear-forest forbidden graphs
via bounded-boundary witness retention and fan-graph amplification.
-/

open Finset SimpleGraph
open scoped Classical

namespace E713LinearForestSustained

def fanGraph {A W : Type*} (P : SimpleGraph W) (attach : A → W → Prop) (I : Type*) :
    SimpleGraph (A ⊕ (I × W)) where
  Adj x y := match x, y with
    | .inl _, .inl _ => False
    | .inl a, .inr (_, v) | .inr (_, v), .inl a => attach a v
    | .inr (i, u), .inr (j, v) => i = j ∧ P.Adj u v
  symm := ⟨by
    rintro (a | ⟨i, u⟩) (b | ⟨j, v⟩) hab
    · exact hab
    · exact hab
    · exact hab
    · exact ⟨hab.1.symm, hab.2.symm⟩⟩
  loopless := ⟨by
    rintro (a | ⟨i, u⟩)
    · exact id
    · exact fun h => h.2.ne rfl⟩

noncomputable def fanMass {A W : Type*} [Fintype A] [Fintype W]
    (P : SimpleGraph W) (attach : A → W → Prop) : ℕ :=
  (∑ a : A, (univ.filter (attach a)).card) +
    ∑ w : W, ((univ.filter fun a => attach a w).card + P.degree w)

lemma fanGraph_two_edges {A W I : Type*} [Fintype A] [Fintype W] [Fintype I]
    (P : SimpleGraph W) (attach : A → W → Prop) :
    2 * (fanGraph P attach I).edgeFinset.card = Fintype.card I * fanMass P attach := by
  classical
  let X := fanGraph P attach I
  let L (a : A) := univ.filter (attach a)
  let R (w : W) := univ.filter fun a => attach a w
  have hL (a : A) : X.neighborFinset (.inl a) = (∅ : Finset A).disjSum (univ ×ˢ L a) := by
    ext v; rw [X.mem_neighborFinset]
    cases v with
    | inl b => simp [X, fanGraph]
    | inr p => obtain ⟨i, w⟩ := p; simp [X, fanGraph, L]
  have hR (i : I) (w : W) : X.neighborFinset (.inr (i, w)) =
      (R w).disjSum (({i} : Finset I) ×ˢ P.neighborFinset w) := by
    ext v; rw [X.mem_neighborFinset]
    cases v with
    | inl a => simp [X, fanGraph, R]
    | inr p => obtain ⟨j, z⟩ := p; simp [X, fanGraph, SimpleGraph.mem_neighborFinset, eq_comm, and_comm]
  have dL (a : A) : X.degree (.inl a) = Fintype.card I * (L a).card := by
    rw [← X.card_neighborFinset_eq_degree, hL, card_disjSum, card_empty, zero_add, card_product, card_univ]
  have dR (i : I) (w : W) : X.degree (.inr (i, w)) = (R w).card + P.degree w := by
    rw [← X.card_neighborFinset_eq_degree, hR, card_disjSum, card_product]; simp
  change 2 * X.edgeFinset.card = _
  rw [← X.sum_degrees_eq_twice_card_edges, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [dL, dR, sum_add_distrib, ← mul_sum, sum_const, card_univ, smul_eq_mul]
  unfold fanMass
  simp only [sum_add_distrib]
  change _ = Fintype.card I * ((∑ a, (L a).card) + ((∑ w, (R w).card) + ∑ w, P.degree w))
  ring

lemma capture_hitting_or_disjoint {W : Type*} [Fintype W] (P : Finset (Finset W)) (q r : ℕ)
    (hsize : ∀ t ∈ P, t.card ≤ r) :
    ∃ C : Finset W, C.card ≤ q * r ∧
      ((∀ t ∈ P, ¬ Disjoint t C) ∨ ∀ D : Finset W, D.card < q → ∃ t ∈ P, Disjoint t D) := by
  classical
  by_cases hemp : ∅ ∈ P
  · exact ⟨∅, by simp, Or.inr fun _ _ => ⟨∅, hemp, by simp⟩⟩
  let good := P.powerset.filter fun S : Finset (Finset W) => (S : Set (Finset W)).PairwiseDisjoint id
  obtain ⟨S, hS, hmax⟩ := exists_max_image good Finset.card ⟨∅, by simp [good]⟩
  obtain ⟨hSpow, hpair⟩ := mem_filter.mp hS
  have hsub := mem_powerset.mp hSpow
  by_cases hlt : S.card < q
  · refine ⟨S.biUnion id, ?_, Or.inl fun t ht hdis => ?_⟩
    · calc (S.biUnion id).card ≤ ∑ t ∈ S, t.card := card_biUnion_le
        _ ≤ ∑ _ ∈ S, r := sum_le_sum fun t ht => hsize t (hsub ht)
        _ ≤ q * r := by simpa [smul_eq_mul] using Nat.mul_le_mul_right r hlt.le
    · by_cases htS : t ∈ S
      · rcases t.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
        · exact hemp ht
        · exact Finset.disjoint_left.mp hdis hx (mem_biUnion.mpr ⟨t, htS, hx⟩)
      · have hins : insert t S ∈ good := by
          refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset ht hsub), fun u hu v hv hne => ?_⟩
          rcases mem_insert.mp hu with rfl | huS <;> rcases mem_insert.mp hv with rfl | hvS
          · exact (hne rfl).elim
          · exact hdis.mono_right fun x hx => mem_biUnion.mpr ⟨v, hvS, hx⟩
          · exact (hdis.mono_right fun x hx => mem_biUnion.mpr ⟨u, huS, hx⟩).symm
          · exact hpair huS hvS hne
        have := hmax _ hins
        rw [card_insert_of_notMem htS] at this; omega
  · refine ⟨∅, by simp, Or.inr fun D hD => ?_⟩
    by_contra! hbad
    have hhit (t : S) : ∃ x : D, x.val ∈ t.val := by
      obtain ⟨x, hxt, hxD⟩ := Finset.not_disjoint_iff.mp (hbad t.val (hsub t.property))
      exact ⟨⟨x, hxD⟩, hxt⟩
    choose f hf using hhit
    have hinj : Function.Injective f := fun u v heq => by
      by_contra hne
      exact Finset.disjoint_left.mp
        (hpair u.property v.property fun h => hne (Subtype.ext h)) (hf u) (heq.symm ▸ hf v)
    have := Fintype.card_le_of_injective f hinj
    simp only [Fintype.card_coe] at this; omega

def Realizes {V W : Type*} (F : SimpleGraph V) (X : SimpleGraph W) (B : Finset W)
    (S : Finset V) (labels : V → Option B) (T : Finset W) : Prop :=
  Disjoint T B ∧ ∃ e : S ≃ T,
    (∀ x y : S, F.Adj x.val y.val → X.Adj (e x).val (e y).val) ∧
    ∀ x : S, ∀ v b, labels v = some b → F.Adj x.val v → X.Adj (e x).val b.val

lemma stage_enlarge {V W : Type*} [Fintype V] [Fintype W] (F : SimpleGraph V) (X : SimpleGraph W)
    (B : Finset W) :
    ∃ Z : Finset W, B ⊆ Z ∧
      Z.card ≤ B.card + (2 ^ Fintype.card V * (B.card + 1) ^ Fintype.card V) *
        ((Fintype.card V + 1) * Fintype.card V) ∧
      ∀ (S : Finset V) (labels : V → Option B) (T : Finset W),
        Realizes F X B S labels T → Disjoint T Z → ∀ D : Finset W, D.card ≤ Fintype.card V →
          ∃ T' : Finset W, Realizes F X B S labels T' ∧ Disjoint T' D := by
  classical
  let q := Fintype.card V
  let A := Finset V × (V → Option B)
  let fam (a : A) := univ.filter (Realizes F X B a.1 a.2)
  have hbd (a : A) (t : Finset W) (ht : t ∈ fam a) : t.card ≤ q := by
    obtain ⟨_, e, _⟩ := (mem_filter.mp ht).2
    have hsz := Fintype.card_congr e
    simp only [Fintype.card_coe] at hsz
    exact hsz ▸ card_le_univ a.1
  choose C hCsz hdich using fun a : A => capture_hitting_or_disjoint (fam a) (q + 1) q (hbd a)
  refine ⟨B ∪ univ.biUnion C, subset_union_left, ?_, fun S labels T hmod hunt D hD => ?_⟩
  · have hA : Fintype.card A = 2 ^ q * (B.card + 1) ^ q := by simp [A, q, Fintype.card_finset]
    have htot := sum_le_sum (s := (univ : Finset A)) fun a _ => hCsz a
    rw [sum_const, card_univ, smul_eq_mul, hA] at htot
    exact (card_union_le ..).trans (Nat.add_le_add_left (card_biUnion_le.trans htot) _)
  · let a : A := (S, labels)
    have hT : T ∈ fam a := mem_filter.mpr ⟨mem_univ _, hmod⟩
    rcases hdich a with hhit | hsup
    · exact (hhit T hT (hunt.mono_right fun x hx =>
        mem_union_right B (mem_biUnion.mpr ⟨a, mem_univ _, hx⟩))).elim
    · obtain ⟨T', hT', hd⟩ := hsup D (by change D.card < Fintype.card V + 1; omega)
      exact ⟨T', (mem_filter.mp hT').2, hd⟩

lemma choose_disjoint_embeddings {I W : Type*} [Fintype I] [Fintype W] (A : I → Type*)
    [∀ i, Fintype (A i)] (valid : ∀ i, (A i ↪ W) → Prop) (q : ℕ)
    (hspace : ∑ i, Fintype.card (A i) ≤ q)
    (hsup : ∀ i (D : Finset W), D.card ≤ q →
      ∃ f : A i ↪ W, valid i f ∧ Disjoint (univ.map f) D) :
    ∃ f : ∀ i, A i ↪ W, (∀ i, valid i (f i)) ∧
      ∀ i j, i ≠ j → Disjoint (univ.map (f i)) (univ.map (f j)) := by
  classical
  choose seed _ using fun i => hsup i ∅ (by simp)
  have hgo (P : Finset I) : ∃ f : ∀ i, A i ↪ W, (∀ i ∈ P, valid i (f i)) ∧
      ∀ i ∈ P, ∀ j ∈ P, i ≠ j → Disjoint (univ.map (f i)) (univ.map (f j)) := by
    induction P using Finset.induction_on with
    | empty => exact ⟨seed, by simp, by simp⟩
    | @insert i P hi ih =>
      obtain ⟨f, hok, hsep⟩ := ih
      let D := P.biUnion fun j => univ.map (f j)
      have hD : D.card ≤ q := calc
        D.card ≤ ∑ j ∈ P, (univ.map (f j)).card := card_biUnion_le
        _ = ∑ j ∈ P, Fintype.card (A j) := by simp
        _ ≤ ∑ j, Fintype.card (A j) := sum_le_sum_of_subset (subset_univ _)
        _ ≤ q := hspace
      obtain ⟨g, hgood, haway⟩ := hsup i D hD
      let h := Function.update f i g
      have heq : h i = g := Function.update_self ..
      have hsame {j} (hj : j ∈ P) : h j = f j :=
        Function.update_of_ne (show j ≠ i from fun e => hi (e ▸ hj)) ..
      have hfar (j) (hj : j ∈ P) : Disjoint (univ.map g) (univ.map (f j)) :=
        haway.mono_right fun _ hx => mem_biUnion.mpr ⟨j, hj, hx⟩
      refine ⟨h, fun j hj => ?_, fun j hj k hk hne => ?_⟩
      · rcases mem_insert.mp hj with rfl | hjP
        · simpa [heq] using hgood
        · rw [hsame hjP]; exact hok j hjP
      · rcases mem_insert.mp hj with rfl | hjP <;> rcases mem_insert.mp hk with rfl | hkP
        · exact (hne rfl).elim
        · rw [heq, hsame hkP]; exact hfar k hkP
        · rw [hsame hjP, heq]; exact (hfar j hjP).symm
        · rw [hsame hjP, hsame hkP]; exact hsep j hjP k hkP hne
  obtain ⟨f, hok, hsep⟩ := hgo univ
  exact ⟨f, fun i => hok i (mem_univ i), fun i j => hsep i (mem_univ i) j (mem_univ j)⟩

lemma fan_free {V W I : Type*} [Fintype V] [Fintype W] [Fintype I]
    (F : SimpleGraph V) (X : SimpleGraph W) (hfree : F.Free X) (B Z U : Finset W)
    (hinc : B ⊆ Z) (hout : Disjoint U Z)
    (hsup : ∀ (S : Finset V) (labels : V → Option B) (T : Finset W),
      Realizes F X B S labels T → Disjoint T Z → ∀ D : Finset W, D.card ≤ Fintype.card V →
        ∃ T' : Finset W, Realizes F X B S labels T' ∧ Disjoint T' D) :
    F.Free (fanGraph (X.induce (U : Set W)) (fun (b : B) (u : U) => X.Adj b.val u.val) I) := by
  classical
  rintro ⟨e⟩
  let labels (v : V) : Option B := match e v with | .inl b => some b | .inr _ => none
  let S (i : I) : Finset V := univ.filter fun v => ∃ w : U, e v = Sum.inr (i, w)
  have hhit (v : V) (i : I) (w : U) (h : e v = Sum.inr (i, w)) : v ∈ S i :=
    mem_filter.mpr ⟨mem_univ _, w, h⟩
  choose orig horig using fun (i : I) (v : S i) => (mem_filter.mp v.property).2
  have hleft {v : V} {b : B} (h : labels v = some b) : e v = Sum.inl b := by
    unfold labels at h; split at h
    next c hc => exact hc.trans (congrArg Sum.inl (Option.some.inj h))
    next _ => contradiction
  have hcross (i : I) (u : S i) (v : V) (b : B) (hlab : labels v = some b) (hadj : F.Adj u.val v) :
      X.Adj (orig i u).val b.val := by
    have hedge := e.toHom.map_rel' hadj
    change (fanGraph _ _ I).Adj (e u.val) (e v) at hedge
    rw [horig, hleft hlab] at hedge
    exact (show X.Adj b.val (orig i u).val from hedge).symm
  have hinner (i : I) (u v : S i) (hadj : F.Adj u.val v.val) :
      X.Adj (orig i u).val (orig i v).val := by
    have hedge := e.toHom.map_rel' hadj
    change (fanGraph _ _ I).Adj (e u.val) (e v.val) at hedge
    rw [horig, horig] at hedge; exact hedge.2
  let valid (i : I) (g : S i ↪ W) : Prop :=
    (∀ x, g x ∉ B) ∧ (∀ x y : S i, F.Adj x.val y.val → X.Adj (g x) (g y)) ∧
      ∀ x : S i, ∀ v b, labels v = some b → F.Adj x.val v → X.Adj (g x) b.val
  have hfresh (i : I) (D : Finset W) (hD : D.card ≤ Fintype.card V) :
      ∃ g : S i ↪ W, valid i g ∧ Disjoint (univ.map g) D := by
    let f0 : S i ↪ W := ⟨fun x => (orig i x).val, fun x y heq => Subtype.ext <| e.injective <| by
      change e x.val = e y.val; rw [horig, horig]
      exact congrArg (fun w : U => Sum.inr (i, w)) (Subtype.ext heq)⟩
    let T := univ.map f0
    have hinU : T ⊆ U := fun w hw => by obtain ⟨x, _, rfl⟩ := mem_map.mp hw; exact (orig i x).property
    let eqv : S i ≃ T := Equiv.ofBijective
      (fun x => (⟨f0 x, mem_map.mpr ⟨x, mem_univ _, rfl⟩⟩ : T))
      ⟨fun _ _ h => f0.injective (congrArg (fun z : T => z.val) h), fun w => by
        obtain ⟨x, _, hx⟩ := mem_map.mp w.property; exact ⟨x, Subtype.ext hx⟩⟩
    obtain ⟨T', ⟨hapart, g, hint, hext⟩, haway⟩ :=
      hsup _ _ _ ⟨hout.mono hinU hinc, eqv, hinner i, hcross i⟩ (hout.mono_left hinU) D hD
    refine ⟨g.toEmbedding.trans (Function.Embedding.subtype _),
      ⟨fun x hx => Finset.disjoint_left.mp hapart (g x).property hx, hint, hext⟩,
      haway.mono_left fun w hw => ?_⟩
    obtain ⟨x, _, rfl⟩ := mem_map.mp hw; exact (g x).property
  have hspace : ∑ i, Fintype.card (S i) ≤ Fintype.card V := by
    rw [← Fintype.card_sigma]
    refine Fintype.card_le_of_injective (fun p : (i : I) × S i => p.2.val) ?_
    rintro ⟨i, x⟩ ⟨j, y⟩ heq
    have hz := (horig i x).symm.trans ((congrArg e heq).trans (horig j y))
    obtain rfl : i = j := (Prod.mk.inj (Sum.inr.inj hz)).1
    exact congrArg (Sigma.mk i) (Subtype.ext heq)
  obtain ⟨g, hgood, hsep⟩ := choose_disjoint_embeddings (fun i => ↥(S i)) valid _ hspace hfresh
  let f (v : V) : W := match h : e v with
    | .inl b => b.val
    | .inr (i, w) => g i ⟨v, hhit v i w h⟩
  have hfl (v : V) (b : B) (h : e v = Sum.inl b) : f v = b.val := by
    unfold f; split
    next c hc => exact congrArg Subtype.val (Sum.inl.inj (hc.symm.trans h))
    next _ _ hz => exact (Sum.inr_ne_inl (hz.symm.trans h)).elim
  have hfr (v : V) (i : I) (w : U) (h : e v = Sum.inr (i, w)) : f v = g i ⟨v, hhit v i w h⟩ := by
    unfold f; split
    next _ hc => exact (Sum.inl_ne_inr (hc.symm.trans h)).elim
    next j _ hz => obtain rfl : j = i := (Prod.mk.inj (Sum.inr.inj (hz.symm.trans h))).1; rfl
  apply hfree
  refine ⟨⟨⟨f, fun {u v} hadj => ?_⟩, fun u v heq => ?_⟩⟩
  · have hedge := e.toHom.map_rel' hadj
    change (fanGraph _ _ I).Adj (e u) (e v) at hedge
    cases hu : e u with
    | inl b =>
      cases hv : e v with
      | inl c => rw [hu, hv] at hedge; exact hedge.elim
      | inr p =>
        obtain ⟨i, w⟩ := p; rw [hfl u b hu, hfr v i w hv]
        exact ((hgood i).2.2 _ u b (by simp [labels, hu]) hadj.symm).symm
    | inr p =>
      obtain ⟨i, w⟩ := p
      cases hv : e v with
      | inl b =>
        rw [hfr u i w hu, hfl v b hv]
        exact (hgood i).2.2 _ v b (by simp [labels, hv]) hadj
      | inr p2 =>
        obtain ⟨j, z⟩ := p2; rw [hu, hv] at hedge; obtain rfl := hedge.1
        rw [hfr u i w hu, hfr v i z hv]; exact (hgood i).2.1 _ _ hadj
  · change f u = f v at heq
    cases hu : e u with
    | inl b =>
      cases hv : e v with
      | inl c =>
        rw [hfl u b hu, hfl v c hv] at heq
        exact e.injective (hu.trans ((congrArg Sum.inl (Subtype.ext heq)).trans hv.symm))
      | inr p =>
        obtain ⟨i, w⟩ := p; rw [hfl u b hu, hfr v i w hv] at heq
        exact ((hgood i).1 _ (heq ▸ b.property)).elim
    | inr p =>
      obtain ⟨i, w⟩ := p
      cases hv : e v with
      | inl b =>
        rw [hfr u i w hu, hfl v b hv] at heq
        exact ((hgood i).1 _ (heq.symm ▸ b.property)).elim
      | inr p2 =>
        obtain ⟨j, z⟩ := p2; rw [hfr u i w hu, hfr v j z hv] at heq
        by_cases hij : i = j
        · subst hij; exact congrArg Subtype.val ((g i).injective heq)
        · exact (Finset.disjoint_left.mp (hsep i j hij)
            (mem_map.mpr ⟨_, mem_univ _, rfl⟩) (heq.symm ▸ mem_map.mpr ⟨_, mem_univ _, rfl⟩)).elim

def stepBound (q b : ℕ) : ℕ := b + (2 ^ q * (b + 1) ^ q) * ((q + 1) * q)

def layerLimit (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => stepBound q (layerLimit q k)

lemma layerLimit_mono (q : ℕ) : Monotone (layerLimit q) :=
  monotone_nat_of_le_succ fun _ => Nat.le_add_right _ _

def FreeFan {V W : Type*} (F : SimpleGraph V) (X : SimpleGraph W) (B U : Finset W) : Prop :=
  ∀ l : ℕ, F.Free (fanGraph (X.induce (U : Set W)) (fun (b : B) (u : U) => X.Adj b.val u.val) (Fin l))

lemma exists_light_layer {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W] (F : SimpleGraph V)
    (X : SimpleGraph W) (hfree : F.Free X) (K : ℕ) (hK : 0 < K) :
    ∃ B Z : Finset W, B ⊆ Z ∧ Z.card ≤ layerLimit (Fintype.card V) K ∧ FreeFan F X B Zᶜ ∧
      K * (∑ v ∈ Z \ B, X.degree v) ≤ 2 * X.edgeFinset.card := by
  classical
  let q := Fintype.card V
  let E := 2 * X.edgeFinset.card
  by_contra! hfail
  have hgrow (k : ℕ) (hk : k ≤ K) : ∃ B : Finset W, B.card ≤ layerLimit q k ∧
      k * (E + 1) ≤ K * (∑ v ∈ B, X.degree v) := by
    induction k with
    | zero => exact ⟨∅, by simp [layerLimit], by simp⟩
    | succ k ih =>
      obtain ⟨B, hBsz, hst⟩ := ih (by omega)
      obtain ⟨Z, hinc, hZsz, hsup⟩ := stage_enlarge F X B
      have hsz : Z.card ≤ layerLimit q (k + 1) := hZsz.trans (by
        change B.card + (2 ^ q * (B.card + 1) ^ q) * _ ≤
          layerLimit q k + (2 ^ q * (layerLimit q k + 1) ^ q) * _
        gcongr)
      have hff : FreeFan F X B Zᶜ := fun l => fan_free F X hfree B Z Zᶜ hinc
        (Finset.disjoint_left.mpr fun _ hv hz => mem_compl.mp hv hz) hsup
      have hlarge := hfail B Z hinc (hsz.trans (layerLimit_mono q hk)) hff
      refine ⟨Z, hsz, ?_⟩
      calc (k + 1) * (E + 1) = k * (E + 1) + (E + 1) := by ring
        _ ≤ K * (∑ v ∈ B, X.degree v) + K * (∑ v ∈ Z \ B, X.degree v) := Nat.add_le_add hst hlarge
        _ = K * (∑ v ∈ Z, X.degree v) := by
          rw [← Nat.mul_add, Nat.add_comm, Finset.sum_sdiff hinc]
  obtain ⟨B, _, hsum⟩ := hgrow K le_rfl
  have hcap := sum_le_sum_of_subset (f := fun v => X.degree v) (subset_univ B)
  rw [X.sum_degrees_eq_twice_card_edges] at hcap
  have := hsum.trans (Nat.mul_le_mul_left K hcap)
  change K * (E + 1) ≤ K * E at this
  nlinarith

lemma subtype_filter_card {W : Type*} (S : Finset W) (p : W → Prop) :
    (univ.filter fun x : S => p x.val).card = (S.filter p).card := by
  classical
  change (S.attach.filter _).card = _
  rw [Finset.filter_attach p S, card_map, card_attach]

lemma edge_loss_bound {W : Type*} [Fintype W] [DecidableEq W] (X : SimpleGraph W) (B Z : Finset W) (hinc : B ⊆ Z) :
    2 * X.edgeFinset.card ≤ fanMass (X.induce (↑(Zᶜ) : Set W))
      (fun (b : B) (u : ↥(Zᶜ)) => X.Adj b.val u.val) +
      Z.card ^ 2 + 2 * ∑ v ∈ Z \ B, X.degree v := by
  classical
  let U := Zᶜ
  let d (S : Finset W) (v : W) := (S.filter (X.Adj v)).card
  have hd_le_deg (S : Finset W) (v : W) : d S v ≤ X.degree v := by
    rw [← X.card_neighborFinset_eq_degree]
    exact card_le_card fun w hw => (X.mem_neighborFinset _ _).mpr (mem_filter.mp hw).2
  have hd_le_card (S : Finset W) (v : W) : d S v ≤ S.card := card_filter_le _ _
  have hdeg_split (v : W) : X.degree v = d Z v + d U v := by
    rw [← X.card_neighborFinset_eq_degree]
    have heq : Z.filter (X.Adj v) ∪ U.filter (X.Adj v) = X.neighborFinset v := by
      ext w; simp [U, SimpleGraph.mem_neighborFinset]; tauto
    have hdis : Disjoint (Z.filter (X.Adj v)) (U.filter (X.Adj v)) :=
      Finset.disjoint_left.mpr fun _ h1 h2 => (mem_compl.mp (mem_filter.mp h2).1) (mem_filter.mp h1).1
    dsimp only [d]; rw [← heq, card_union_of_disjoint hdis]
  have hdZ_split (u : W) : d Z u = d B u + d (Z \ B) u := by
    have heq : B.filter (X.Adj u) ∪ (Z \ B).filter (X.Adj u) = Z.filter (X.Adj u) := by
      ext w; simp only [mem_union, mem_filter, mem_sdiff]
      exact ⟨fun h => h.elim (fun h1 => ⟨hinc h1.1, h1.2⟩) (fun h2 => ⟨h2.1.1, h2.2⟩),
        fun ⟨hwZ, hwu⟩ => if hwB : w ∈ B then Or.inl ⟨hwB, hwu⟩ else Or.inr ⟨⟨hwZ, hwB⟩, hwu⟩⟩
    have hdis : Disjoint (B.filter (X.Adj u)) ((Z \ B).filter (X.Adj u)) :=
      Finset.disjoint_left.mpr fun _ h1 h2 => (mem_sdiff.mp (mem_filter.mp h2).1).2 (mem_filter.mp h1).1
    dsimp only [d]; rw [← heq, card_union_of_disjoint hdis]
  have hswap (S T : Finset W) : (∑ x ∈ S, d T x) = ∑ y ∈ T, d S y := by
    simp only [d, card_filter]; rw [sum_comm]
    exact sum_congr rfl fun y _ => sum_congr rfl fun x _ => by rw [X.adj_comm x y]
  have hsubdeg (u : ↥(U : Set W)) : (X.induce (U : Set W)).degree u = d U u.val := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : (X.induce (U : Set W)).neighborFinset u =
        univ.filter fun y : ↥(U : Set W) => X.Adj u.val y.val := by
      ext y; simp [SimpleGraph.mem_neighborFinset]
    rw [this]; exact subtype_filter_card U (X.Adj u.val)
  have hmass : fanMass (X.induce (U : Set W)) (fun (b : B) (u : U) => X.Adj b.val u.val) =
      (∑ b ∈ B, d U b) + ∑ u ∈ U, (d B u + d U u) := by
    unfold fanMass
    congr 1
    · exact (sum_congr rfl fun b _ => subtype_filter_card U (X.Adj b.val)).trans (Finset.sum_attach B (d U))
    · refine (sum_congr rfl fun u _ => ?_).trans (Finset.sum_attach U fun w => d B w + d U w)
      have hR : (univ.filter fun b : B => X.Adj b.val u.val).card = d B u.val := by
        calc _ = (univ.filter fun b : B => X.Adj u.val b.val).card := by
              congr 1; ext b; simp [SimpleGraph.adj_comm]
          _ = _ := subtype_filter_card B (X.Adj u.val)
      rw [hR]
      exact congrArg (d B u.val + ·) (hsubdeg u)
  have htot : 2 * X.edgeFinset.card = (∑ v ∈ Z, X.degree v) + ∑ u ∈ U, X.degree u := by
    rw [← X.sum_degrees_eq_twice_card_edges, ← Z.sum_add_sum_compl]
  have hZ_sum : (∑ v ∈ Z, X.degree v) ≤ Z.card ^ 2 + (∑ b ∈ B, d U b) + ∑ v ∈ Z \ B, X.degree v := by
    rw [← Finset.sum_sdiff hinc]
    have hB : (∑ b ∈ B, X.degree b) ≤ Z.card ^ 2 + ∑ b ∈ B, d U b := by
      calc ∑ b ∈ B, X.degree b = ∑ b ∈ B, (d Z b + d U b) := sum_congr rfl fun b _ => hdeg_split b
        _ = (∑ b ∈ B, d Z b) + ∑ b ∈ B, d U b := sum_add_distrib
        _ ≤ (∑ _ ∈ B, Z.card) + ∑ b ∈ B, d U b :=
          Nat.add_le_add_right (sum_le_sum fun b _ => hd_le_card Z b) _
        _ = B.card * Z.card + ∑ b ∈ B, d U b := by simp [smul_eq_mul]
        _ ≤ Z.card ^ 2 + ∑ b ∈ B, d U b := by
          rw [pow_two]; exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (card_le_card hinc)) _
    omega
  have hU_sum : (∑ u ∈ U, X.degree u) ≤ (∑ u ∈ U, (d B u + d U u)) + ∑ v ∈ Z \ B, X.degree v := by
    calc ∑ u ∈ U, X.degree u = ∑ u ∈ U, (d Z u + d U u) := sum_congr rfl fun u _ => hdeg_split u
      _ = ∑ u ∈ U, ((d B u + d U u) + d (Z \ B) u) :=
        sum_congr rfl fun u _ => by rw [hdZ_split u]; ring
      _ = (∑ u ∈ U, (d B u + d U u)) + ∑ u ∈ U, d (Z \ B) u := sum_add_distrib
      _ = (∑ u ∈ U, (d B u + d U u)) + ∑ v ∈ Z \ B, d U v := by rw [hswap U (Z \ B)]
      _ ≤ (∑ u ∈ U, (d B u + d U u)) + ∑ v ∈ Z \ B, X.degree v :=
        Nat.add_le_add_left (sum_le_sum fun v _ => hd_le_deg U v) _
  rw [htot, hmass]; omega

lemma pad_isolated {V W : Type*} [Fintype W] (G : SimpleGraph V) (hact : ∀ v, ¬ G.IsIsolated v)
    (X : SimpleGraph W) (hfree : G.Free X) (m : ℕ) (hfit : Fintype.card W ≤ m) :
    X.edgeFinset.card ≤ extremalNumber m G := by
  classical
  let k := m - Fintype.card W
  let Z := X ⊕g (⊥ : SimpleGraph (Fin k))
  have hZfree : G.Free Z := by
    rintro ⟨e⟩
    have horig (v : V) : ∃ w : W, e v = Sum.inl w := by
      cases hv : e v with
      | inl w => exact ⟨w, rfl⟩
      | inr i =>
        obtain ⟨u, hadj⟩ := exists_adj_iff_not_isIsolated.mpr (hact v)
        have ha : Z.Adj (e v) (e u) := e.toHom.map_rel' hadj
        rw [hv] at ha
        cases hu : e u <;> rw [hu] at ha
        · exact (not_adj_sum_inl_inr _ i ha.symm).elim
        · exact (sum_adj_inr.mp ha).elim
    choose f hf using horig
    refine hfree ⟨⟨⟨f, fun {a b} hadj => ?_⟩, fun a b heq => ?_⟩⟩
    · have ha : Z.Adj (e a) (e b) := e.toHom.map_rel' hadj
      rw [hf a, hf b] at ha; exact sum_adj_inl.mp ha
    · exact e.injective ((hf a).trans ((congrArg Sum.inl heq).trans (hf b).symm))
  have hedges : Z.edgeFinset.card = X.edgeFinset.card := by
    simp only [Z, edgeFinset_card]
    simpa using Fintype.card_congr (edgeSetSumEquiv (G := X) (H := (⊥ : SimpleGraph (Fin k))))
  have hle := card_edgeFinset_le_extremalNumber hZfree
  have hsz : Fintype.card (W ⊕ Fin k) = m := by simp [k, hfit]
  simpa only [hedges, hsz] using hle

theorem sustained_slope {V : Type*} [Fintype V] (F : SimpleGraph V) (hnbot : F ≠ ⊥)
    (hact : ∀ v, ¬ F.IsIsolated v) (a b : ℚ) (hab : a < b)
    (hhigh : ∀ N, ∃ n ≥ N, b * n < (extremalNumber n F : ℚ)) :
    ∃ M, ∀ m ≥ M, a * m ≤ (extremalNumber m F : ℚ) := by
  classical
  by_cases hle0 : a ≤ 0
  · exact ⟨0, fun m _ => (mul_nonpos_of_nonpos_of_nonneg hle0 (Nat.cast_nonneg _)).trans (Nat.cast_nonneg _)⟩
  have ha : 0 < a := lt_of_not_ge hle0
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * b / (b - a))
  let K := k + 3
  have hKpos : (2 : ℚ) < K := by dsimp [K]; push_cast; linarith [Nat.cast_nonneg k (α := ℚ)]
  have henough : 0 < (K : ℚ) * (b - a) - 2 * b := by
    have := (div_lt_iff₀ (sub_pos.mpr hab)).mp hk
    dsimp [K]; push_cast; nlinarith
  let L := layerLimit (Fintype.card V) K
  obtain ⟨N, hN⟩ := exists_nat_gt ((K : ℚ) * L ^ 2 / ((K : ℚ) * (b - a) - 2 * b))
  obtain ⟨n, hn, habove⟩ := hhigh (max N (L + 1))
  have hwit : ∃ X : SimpleGraph (Fin n), F.Free X ∧ X.edgeFinset.card = extremalNumber n F := by
    obtain ⟨X, _, hext⟩ := exists_isExtremal_free (V := Fin n) hnbot
    obtain ⟨hfree, heqE⟩ := isExtremal_free_iff.mp hext
    refine ⟨X, hfree, ?_⟩
    convert! heqE using 1
    · congr! 2
    · rw [Fintype.card_fin]
  obtain ⟨X, hfree, heEq⟩ := hwit
  have hoverX : b * n < (X.edgeFinset.card : ℚ) := by rwa [heEq]
  obtain ⟨B, Z, hinc, hZsz, hrep, hlight⟩ := exists_light_layer F X hfree K (by dsimp [K]; omega)
  let U := Zᶜ
  have hZlt : Z.card < n := by change Z.card ≤ L at hZsz; omega
  have hUcard : U.card = n - Z.card := by simp [U, card_compl]
  have hUpos : 0 < U.card := by omega
  let e := fanMass (X.induce (U : Set (Fin n))) (fun (b : B) (u : U) => X.Adj b.val u.val)
  have hgain : 2 * a * U.card < (e : ℚ) := by
    by_contra! hcheap
    let loss := ∑ v ∈ Z \ B, X.degree v
    have hcapNat : 2 * X.edgeFinset.card ≤ e + Z.card ^ 2 + 2 * loss :=
      by dsimp only [e, U, loss]; exact edge_loss_bound X B Z hinc
    have hcap : 2 * (X.edgeFinset.card : ℚ) ≤ e + (Z.card : ℚ) ^ 2 + 2 * loss := by
      exact_mod_cast hcapNat
    have hfew : (K : ℚ) * loss ≤ 2 * (X.edgeFinset.card : ℚ) := by dsimp only [loss]; exact_mod_cast hlight
    have hUs : (U.card : ℚ) ≤ n := by exact_mod_cast (show U.card ≤ n by omega)
    have hZs : (Z.card : ℚ) ^ 2 ≤ (L : ℚ) ^ 2 := by gcongr
    have hpay : (K : ℚ) * L ^ 2 < n * ((K : ℚ) * (b - a) - 2 * b) :=
      (div_lt_iff₀ henough).mp (hN.trans_le (by exact_mod_cast (le_max_left N (L + 1)).trans hn))
    have hbd : (X.edgeFinset.card : ℚ) ≤ a * n + (L : ℚ) ^ 2 + loss := by
      nlinarith [hcap, hcheap, hZs, mul_le_mul_of_nonneg_left hUs ha.le]
    have hscaled := mul_le_mul_of_nonneg_left hbd (show (0 : ℚ) ≤ K by positivity)
    have hopp := mul_lt_mul_of_pos_left hoverX (sub_pos.mpr hKpos)
    nlinarith [hscaled, hopp, hfew, hpay]
  obtain ⟨k0, hk0⟩ := exists_nat_gt ((2 * a * (B.card + U.card)) / (e - 2 * a * U.card))
  have hgap : 0 < (e : ℚ) - 2 * a * U.card := sub_pos.mpr hgain
  have hpay0 := (div_lt_iff₀ hgap).mp hk0
  refine ⟨B.card + U.card * k0, fun m hm => ?_⟩
  let l := (m - B.card) / U.card
  have hfitB : B.card ≤ m := by omega
  have hkl : k0 ≤ l := (Nat.le_div_iff_mul_le hUpos).mpr (by rw [Nat.mul_comm]; omega)
  let Y := fanGraph (X.induce (U : Set (Fin n))) (fun (b : B) (u : U) => X.Adj b.val u.val) (Fin l)
  have hfitY : Fintype.card (B ⊕ (Fin l × U)) ≤ m := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
    have := Nat.div_mul_le_self (m - B.card) U.card
    dsimp [l]; omega
  have hup := pad_isolated F hact Y (by dsimp only [Y, U]; exact hrep l) m hfitY
  have hYedges : 2 * Y.edgeFinset.card = l * e := by
    calc 2 * Y.edgeFinset.card = Fintype.card (Fin l) * e := by
          convert! fanGraph_two_edges (I := Fin l) (X.induce (U : Set (Fin n)))
            (fun (b : B) (u : U) => X.Adj b.val u.val) using 1
      _ = l * e := by rw [Fintype.card_fin]
  have hlow : (l : ℚ) * e ≤ 2 * (extremalNumber m F : ℚ) := by
    have : l * e ≤ 2 * extremalNumber m F := by omega
    exact_mod_cast this
  have hend : m ≤ B.card + l * U.card + U.card := by
    have := Nat.mod_lt (m - B.card) hUpos
    have := Nat.mod_add_div (m - B.card) U.card
    dsimp [l]; rw [Nat.mul_comm ((m - B.card) / U.card)]; omega
  have hendQ : (m : ℚ) ≤ B.card + (l : ℚ) * U.card + U.card := by exact_mod_cast hend
  have hgeQ : (k0 : ℚ) ≤ l := by exact_mod_cast hkl
  nlinarith [mul_le_mul_of_nonneg_left hendQ ha.le, mul_le_mul_of_nonneg_right hgeQ hgap.le]

end E713LinearForestSustained

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_i_R1_H2_R1.H1 := by
  intro q G _ _ _ hact _ ⟨v, hv⟩ _ a b hab hhigh
  refine E713LinearForestSustained.sustained_slope G ?_ hact a b hab hhigh
  rintro rfl; simp at hv