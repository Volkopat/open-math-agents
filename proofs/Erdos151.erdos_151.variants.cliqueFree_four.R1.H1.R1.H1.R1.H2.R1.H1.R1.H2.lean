import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H2_R1_H1_R1

/-!
# The degree-five case on 23 vertices

The nonneighbors of any degree-five vertex induce a seventeen-vertex
Ramsey (3,6) graph. Its catalogue forces at least 40 edges. Combining this
bound with the handshaking lemma shows that every degree-five vertex has
more than half of the degree-five vertices among its neighbors. Two
adjacent degree-five vertices have disjoint neighborhoods, a contradiction.

The Ramsey graph rows are from Brendan McKay's
[Ramsey graph data](https://users.cecs.anu.edu.au/~bdm/data/ramsey.html),
licensed [CC BY 4.0](https://users.cecs.anu.edu.au/~bdm/data/).
The catalogue verification applies the vertex gluing method of Goedgebeur
and Radziszowski, [New Computational Upper Bounds for Ramsey Numbers R(3,k)](https://arxiv.org/abs/1210.5826),
Section 3. Daniel Prakah-Asante's [verified 22-vertex edge bound](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12460)
also establishes the smaller twelve- and thirteen-vertex catalogues. The
reconstruction and certificates here were developed independently.
-/

/-
# Reconstruction from a vertex and its two neighborhoods

In a triangle-free graph the neighbors of a root have no internal edges.
Retain the induced graph on the nonneighbors and the attachment sets from
each neighbor to that induced graph.
-/

namespace OMA.RamseyCatalogue

open SimpleGraph Finset

abbrev Vertex (d n : ℕ) := Option (Fin d ⊕ Fin n)

def near {d n : ℕ} : Fin d ↪ Vertex d n :=
  ⟨fun i => some (Sum.inl i), by simp [Function.Injective]⟩

def far {d n : ℕ} : Fin n ↪ Vertex d n :=
  ⟨fun j => some (Sum.inr j), by simp [Function.Injective]⟩

@[simp] theorem near_apply {d n : ℕ} (i : Fin d) :
    near (n := n) i = (some (Sum.inl i) : Vertex d n) := rfl

@[simp] theorem far_apply {d n : ℕ} (j : Fin n) :
    far (d := d) j = (some (Sum.inr j) : Vertex d n) := rfl

def glued {d n : ℕ} (H : SimpleGraph (Fin n)) (B : Fin d → Finset (Fin n)) :
    SimpleGraph (Vertex d n) where
  Adj
    | none, some (Sum.inl _) => True
    | some (Sum.inl _), none => True
    | some (Sum.inl i), some (Sum.inr j) => j ∈ B i
    | some (Sum.inr j), some (Sum.inl i) => j ∈ B i
    | some (Sum.inr i), some (Sum.inr j) => H.Adj i j
    | _, _ => False
  symm := ⟨by
    intro x y h
    rcases x with _ | (i | i) <;> rcases y with _ | (j | j) <;> try exact h
    exact H.adj_symm h⟩
  loopless := ⟨by
    intro x
    rcases x with _ | (i | i)
    · exact not_false
    · exact not_false
    · exact H.irrefl⟩

instance gluedAdjDecidable {d n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (B : Fin d → Finset (Fin n)) : DecidableRel (glued H B).Adj
  | none, none => inferInstanceAs (Decidable False)
  | none, some (Sum.inl _) => inferInstanceAs (Decidable True)
  | none, some (Sum.inr _) => inferInstanceAs (Decidable False)
  | some (Sum.inl _), none => inferInstanceAs (Decidable True)
  | some (Sum.inl _), some (Sum.inl _) => inferInstanceAs (Decidable False)
  | some (Sum.inl i), some (Sum.inr j) => inferInstanceAs (Decidable (j ∈ B i))
  | some (Sum.inr _), none => inferInstanceAs (Decidable False)
  | some (Sum.inr j), some (Sum.inl i) => inferInstanceAs (Decidable (j ∈ B i))
  | some (Sum.inr i), some (Sum.inr j) => inferInstanceAs (Decidable (H.Adj i j))

private theorem near_ne_far {d n : ℕ} (i : Fin d) (j : Fin n) :
    (near (n := n) i : Vertex d n) ≠ far j := by
  intro h
  simp only [near_apply, far_apply, Option.some.injEq, Sum.inl_ne_inr] at h

theorem degree_near {d n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (B : Fin d → Finset (Fin n)) (i : Fin d) :
    (glued H B).degree (near i) = 1 + (B i).card := by
  have eq : (glued H B).neighborFinset (near i) = insert none ((B i).map far) := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    rcases x with _ | (j | j)
    · simp [glued, Finset.mem_map]
    · simp [glued, Finset.mem_map]
    · simp [glued, Finset.mem_map]
  rw [← card_neighborFinset_eq_degree, eq, Finset.card_insert_of_notMem, Finset.card_map]
  · omega
  · simp [Finset.mem_map]

theorem degree_far {d n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (B : Fin d → Finset (Fin n)) (j : Fin n) :
    (glued H B).degree (far j) =
      H.degree j + (Finset.univ.filter fun i => j ∈ B i).card := by
  let touching := Finset.univ.filter (fun i => j ∈ B i)
  have eq : (glued H B).neighborFinset (far j) =
      (H.neighborFinset j).map far ∪ touching.map near := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    rcases x with _ | (i | i)
    · simp [glued, touching, Finset.mem_map]
    · simp [glued, touching, Finset.mem_map]
    · simp [glued, touching, Finset.mem_map]
  have hDisj : Disjoint ((H.neighborFinset j).map (far (d := d))) (touching.map near) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨u, _, hu⟩ := Finset.mem_map.mp hy
    exact near_ne_far u i hu
  rw [← card_neighborFinset_eq_degree, eq, Finset.card_union_of_disjoint hDisj,
    Finset.card_map, Finset.card_map, card_neighborFinset_eq_degree]

theorem attachment_independent {d n : ℕ} (H : SimpleGraph (Fin n))
    (B : Fin d → Finset (Fin n)) (h : (glued H B).CliqueFree 3) (i : Fin d) :
    Hᶜ.IsClique (B i : Set (Fin n)) := by
  intro j hj k hk hne
  refine ⟨hne, ?_⟩
  intro ha
  apply (glued H B).isIndepSet_neighborSet_of_triangleFree h (near i)
    (show (glued H B).Adj (near i) (far j) from hj)
    (show (glued H B).Adj (near i) (far k) from hk)
    (fun he => hne (far.injective he))
  exact ha

theorem attachment_avoiding_size {d n s : ℕ} (H : SimpleGraph (Fin n))
    (B : Fin d → Finset (Fin n)) (h : (glued H B)ᶜ.CliqueFree s)
    (T : Finset (Fin n)) (hT : Hᶜ.IsClique (T : Set (Fin n))) (I : Finset (Fin d))
    (hAvoid : ∀ i ∈ I, Disjoint (B i) T) : I.card + T.card < s := by
  let S := I.map (near (n := n)) ∪ T.map (far (d := d))
  have hIQ : (glued H B)ᶜ.IsClique (S : Set (Vertex d n)) := by
    intro a ha b hb hne
    change a ∈ S at ha
    change b ∈ S at hb
    refine ⟨hne, ?_⟩
    rcases Finset.mem_union.mp ha with ha | ha <;> rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hb
      exact not_false
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
      exact fun hAdj => Finset.disjoint_left.mp (hAvoid i hi) hAdj hj
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hb
      exact fun hAdj => Finset.disjoint_left.mp (hAvoid i hi) hAdj hj
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
      exact (hT hi hj (fun he => hne (congrArg far he))).2
  have hDisj : Disjoint (I.map (near (n := n))) (T.map (far (d := d))) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hz'
    exact near_ne_far i j hj.symm
  have hCard : S.card = I.card + T.card := by
    simp only [S, Finset.card_union_of_disjoint hDisj, Finset.card_map]
  by_contra! hLarge
  obtain ⟨U, hUS, hU⟩ := Finset.exists_subset_card_eq (hCard ▸ hLarge : s ≤ S.card)
  exact h U ⟨hIQ.subset hUS, hU⟩

end OMA.RamseyCatalogue

namespace OMA.RamseyCatalogue

open SimpleGraph Finset

private def partitionMap {V : Type*} {d n : ℕ}
    (w : V) (a : Fin d → V) (b : Fin n → V) : Vertex d n → V
  | none => w
  | some (Sum.inl i) => a i
  | some (Sum.inr j) => b j

private theorem partitionMap_injective {V : Type*} {d n : ℕ}
    (G : SimpleGraph V) (w : V) (a : Fin d ↪ V) (b : Fin n ↪ V)
    (ha : ∀ i, G.Adj w (a i)) (hb : ∀ j, Gᶜ.Adj w (b j)) :
    Function.Injective (partitionMap w a b) := by
  rintro (_ | (i | i)) (_ | (j | j)) h <;> simp only [partitionMap] at h
  · rfl
  · exact (G.irrefl (h.symm ▸ ha j)).elim
  · exact ((hb j).1 h).elim
  · exact (G.irrefl (h ▸ ha i)).elim
  · exact congrArg (fun x => some (Sum.inl x)) (a.injective h)
  · exact ((hb j).2 (h ▸ ha i)).elim
  · exact ((hb i).1 h.symm).elim
  · exact ((hb i).2 (h.symm ▸ ha j)).elim
  · exact congrArg (fun x => some (Sum.inr x)) (b.injective h)

private noncomputable def iso_of_partition {V : Type*} {d n : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) (a : Fin d ↪ V) (b : Fin n ↪ V)
    (ha : ∀ i, G.Adj w (a i)) (hb : ∀ j, Gᶜ.Adj w (b j))
    (hCover : Function.Surjective (partitionMap w a b)) (htri : G.CliqueFree 3) :
    glued (G.comap b) (fun i => univ.filter (G.Adj (a i) ∘ b)) ≃g G := by
  let e : Vertex d n ≃ V := Equiv.ofBijective _
    ⟨partitionMap_injective G w a b ha hb, hCover⟩
  refine ⟨e, ?_⟩
  rintro (_ | (i | i)) (_ | (j | j))
  · change G.Adj w w ↔ False
    simp
  · change G.Adj w (a j) ↔ True
    exact iff_true_intro (ha j)
  · change G.Adj w (b j) ↔ False
    exact iff_false_intro (hb j).2
  · change G.Adj (a i) w ↔ True
    exact iff_true_intro (G.adj_symm (ha i))
  · change G.Adj (a i) (a j) ↔ False
    apply iff_false_intro
    by_cases hij : i = j
    · subst j
      exact G.irrefl
    · exact G.isIndepSet_neighborSet_of_triangleFree htri w (ha i) (ha j)
        (fun he => hij (a.injective he))
  · change G.Adj (a i) (b j) ↔ j ∈ univ.filter (G.Adj (a i) ∘ b)
    simp
  · change G.Adj (b i) w ↔ False
    exact iff_false_intro fun h => (hb i).2 h.symm
  · change G.Adj (b i) (a j) ↔ i ∈ univ.filter (G.Adj (a j) ∘ b)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    exact G.adj_comm _ _
  · rfl

theorem exists_gluing_root {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : V) {d n s : ℕ} (hw : G.degree w = d)
    (hn : Gᶜ.degree w = n) (htri : G.CliqueFree 3) (hind : Gᶜ.CliqueFree (s + 1)) :
    ∃ (H : SimpleGraph (Fin n)) (B : Fin d → Finset (Fin n)),
      H.CliqueFree 3 ∧ Hᶜ.CliqueFree s ∧ ∃ e : glued H B ≃g G, e none = w := by
  let A := G.neighborFinset w
  let C := Gᶜ.neighborFinset w
  let a₀ : Fin d ≃ A := Fintype.equivOfCardEq (by simpa only [A, Fintype.card_fin, Fintype.card_coe, card_neighborFinset_eq_degree] using hw.symm)
  let b₀ : Fin n ≃ C := Fintype.equivOfCardEq (by simpa only [C, Fintype.card_fin, Fintype.card_coe, card_neighborFinset_eq_degree] using hn.symm)
  let a : Fin d ↪ V := a₀.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  let b : Fin n ↪ V := b₀.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  have ha (i) : G.Adj w (a i) := (G.mem_neighborFinset w _).mp (a₀ i).2
  have hb (j) : Gᶜ.Adj w (b j) := (Gᶜ.mem_neighborFinset w _).mp (b₀ j).2
  have hCover : Function.Surjective (partitionMap w a b) := by
    intro x
    by_cases hwx : x = w
    · exact ⟨none, hwx.symm⟩
    by_cases hx : G.Adj w x
    · let v : A := ⟨x, (G.mem_neighborFinset w x).mpr hx⟩
      exact ⟨some (Sum.inl (a₀.symm v)), congrArg Subtype.val (a₀.apply_symm_apply v)⟩
    · let v : C := ⟨x, (Gᶜ.mem_neighborFinset w x).mpr ⟨fun h => hwx h.symm, hx⟩⟩
      exact ⟨some (Sum.inr (b₀.symm v)), congrArg Subtype.val (b₀.apply_symm_apply v)⟩
  let H := G.comap b
  let iso := iso_of_partition G w a b ha hb hCover htri
  let e : H ↪g G := SimpleGraph.Embedding.comap b G
  have hHT : H.CliqueFree 3 := htri.comap e.isContained
  have hHI : Hᶜ.CliqueFree s := by
    intro T hT
    let f := SimpleGraph.Embedding.complEquiv e
    have hMap : Gᶜ.IsNClique s (T.map b) := by
      refine ⟨?_, by rw [Finset.card_map, hT.card_eq]⟩
      intro x hx y hy hxy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
      exact f.map_adj_iff.mpr (hT.isClique hi hj (fun he => hxy (congrArg b he)))
    apply hind _ (hMap.insert (a := w) ?_)
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
    exact hb j
  exact ⟨H, _, hHT, hHI, iso, rfl⟩

theorem exists_gluing {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : V) {d n s : ℕ} (hw : G.degree w = d)
    (hn : Gᶜ.degree w = n) (hT : G.CliqueFree 3) (hind : Gᶜ.CliqueFree (s + 1)) :
    ∃ (H : SimpleGraph (Fin n)) (B : Fin d → Finset (Fin n)),
      H.CliqueFree 3 ∧ Hᶜ.CliqueFree s ∧ Nonempty (glued H B ≃g G) := by
  obtain ⟨H, B, hHT, hHI, iso, _⟩ := exists_gluing_root G w hw hn hT hind
  exact ⟨H, B, hHT, hHI, ⟨iso⟩⟩

end OMA.RamseyCatalogue

/-
Degree bounds derived from the anti-neighborhood of a vertex, including the
small orders needed to classify the seventeen-vertex Ramsey graphs.
-/

namespace OMA.RamseyCatalogue

open SimpleGraph Finset
open scoped BigOperators

theorem degree_lt_independent {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : ℕ}
    (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree s) (v : V) : G.degree v < s := by
  by_contra! h
  rw [← card_neighborFinset_eq_degree] at h
  obtain ⟨S, hSV, hCard⟩ := Finset.exists_subset_card_eq h
  apply hI S
  refine ⟨?_, hCard⟩
  intro a ha b hb hab
  exact ⟨hab, G.isIndepSet_neighborSet_of_triangleFree hT v
    ((G.mem_neighborFinset v a).mp (hSV ha)) ((G.mem_neighborFinset v b).mp (hSV hb)) hab⟩

def antiGraph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    SimpleGraph (Gᶜ.neighborFinset v) :=
  G.comap Subtype.val

instance antiAdjDecidable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : DecidableRel (antiGraph G v).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj a.val b.val))

theorem anti_triangleFree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (hT : G.CliqueFree 3) : (antiGraph G v).CliqueFree 3 :=
  hT.comap (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G).isContained

theorem anti_independentFree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) {s : ℕ} (hI : Gᶜ.CliqueFree (s + 1)) :
    (antiGraph G v)ᶜ.CliqueFree s := by
  intro T hT
  let e : (antiGraph G v) ↪g G :=
    SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G
  let eC := SimpleGraph.Embedding.complEquiv e
  let b := eC.toEmbedding
  have hMap : Gᶜ.IsNClique s (T.map b) := by
    refine ⟨?_, by rw [Finset.card_map, hT.card_eq]⟩
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    exact eC.map_adj_iff.mpr (hT.isClique hi hj (fun he => hxy (congrArg b he)))
  apply hI _ (hMap.insert (a := v) ?_)
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
  exact (Gᶜ.mem_neighborFinset v j.val).mp j.2

theorem card_le_five {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 3) : Fintype.card V ≤ 5 := by
  by_contra! h
  have hv : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v := Classical.choice hv
  have hl := degree_lt_independent G hT hI v
  have hr := degree_lt_independent Gᶜ hI (by simpa using hT) v
  rw [SimpleGraph.degree_compl] at hr
  omega

theorem anti_card_le_five {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 4) (v : V) : Gᶜ.degree v ≤ 5 := by
  simpa only [Fintype.card_coe, card_neighborFinset_eq_degree] using
    card_le_five (antiGraph G v) (anti_triangleFree G v hT) (anti_independentFree G v hI)

theorem card_le_eight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 4) : Fintype.card V ≤ 8 := by
  by_contra! h
  have hv : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hall (v : V) : G.degree v = 3 ∧ Fintype.card V = 9 := by
    have hl := degree_lt_independent G hT hI v
    have hr := anti_card_le_five G hT hI v
    rw [SimpleGraph.degree_compl] at hr
    omega
  have hn := (hall (Classical.choice hv)).2
  have he := G.sum_degrees_eq_twice_card_edges
  simp only [(hall _).1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn] at he
  omega

theorem anti_card_le_eight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 5) (v : V) : Gᶜ.degree v ≤ 8 := by
  simpa only [Fintype.card_coe, card_neighborFinset_eq_degree] using
    card_le_eight (antiGraph G v) (anti_triangleFree G v hT) (anti_independentFree G v hI)

theorem card_le_thirteen {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 5) : Fintype.card V ≤ 13 := by
  by_contra! h
  have hv : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v := Classical.choice hv
  have hl := degree_lt_independent G hT hI v
  have hr := anti_card_le_eight G hT hI v
  rw [SimpleGraph.degree_compl] at hr
  omega

theorem anti_card_le_thirteen {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 6) (v : V) : Gᶜ.degree v ≤ 13 := by
  simpa only [Fintype.card_coe, card_neighborFinset_eq_degree] using
    card_le_thirteen (antiGraph G v) (anti_triangleFree G v hT) (anti_independentFree G v hI)

end OMA.RamseyCatalogue

namespace OMA.RamseyCatalogue

open SimpleGraph Finset

def relabel_near {d n : ℕ} (H : SimpleGraph (Fin n)) (B : Fin d → Finset (Fin n))
    (e : Equiv.Perm (Fin d)) : glued H (B ∘ e) ≃g glued H B where
  toEquiv := Equiv.optionCongr (Equiv.sumCongr e (Equiv.refl _))
  map_rel_iff' := by
    rintro (_ | (i | i)) (_ | (j | j)) <;> rfl

def relabel_far {d n : ℕ} {H K : SimpleGraph (Fin n)} (e : H ≃g K)
    (B : Fin d → Finset (Fin n)) :
    glued H B ≃g glued K (fun i => (B i).map e.toEquiv.toEmbedding) where
  toEquiv := Equiv.optionCongr (Equiv.sumCongr (Equiv.refl _) e.toEquiv)
  map_rel_iff' := by
    rintro (_ | (i | i)) (_ | (j | j)) <;> try rfl
    · change e j ∈ (B i).map e.toEquiv.toEmbedding ↔ j ∈ B i
      rw [Finset.mem_map_equiv]
      change e.toEquiv.symm (e.toEquiv j) ∈ B i ↔ j ∈ B i
      rw [e.toEquiv.symm_apply_apply]
    · change e i ∈ (B j).map e.toEquiv.toEmbedding ↔ i ∈ B j
      rw [Finset.mem_map_equiv]
      change e.toEquiv.symm (e.toEquiv i) ∈ B j ↔ i ∈ B j
      rw [e.toEquiv.symm_apply_apply]
    · exact e.map_rel_iff'

def vertexNumbering (d n : ℕ) : Vertex d n ≃ Fin (d + n + 1) :=
  (Equiv.optionCongr finSumFinEquiv).trans (finSuccEquiv _).symm

def numbered {d n : ℕ} (H : SimpleGraph (Fin n)) (B : Fin d → Finset (Fin n)) :
    SimpleGraph (Fin (d + n + 1)) :=
  (glued H B).comap (vertexNumbering d n).symm

instance numberedAdjDecidable {d n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (B : Fin d → Finset (Fin n)) : DecidableRel (numbered H B).Adj :=
  fun a b => inferInstanceAs
    (Decidable ((glued H B).Adj ((vertexNumbering d n).symm a) ((vertexNumbering d n).symm b)))

def number_glued {d n : ℕ} (H : SimpleGraph (Fin n)) (B : Fin d → Finset (Fin n)) :
    numbered H B ≃g glued H B :=
  SimpleGraph.Iso.comap (vertexNumbering d n).symm (glued H B)

end OMA.RamseyCatalogue

namespace OMA.RamseyCatalogue

open SimpleGraph Finset

def graphFromRows {n : ℕ} (rowMask : Fin n → ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (rowMask (min i j)).testBit (max i j).val = true
  symm := ⟨fun {i j} h => ⟨h.1.symm, by simpa only [min_comm, max_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance graphFromRowsAdj {n : ℕ} (rowMask : Fin n → ℕ) :
    DecidableRel (graphFromRows rowMask).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

def encodeVertices {n : ℕ} : List (Fin n) → ℕ
  | [] => 0
  | i :: is => 2 ^ i.val ||| encodeVertices is

theorem encodeVertices_testBit {n : ℕ} (l : List (Fin n)) (j : ℕ) :
    (encodeVertices l).testBit j = true ↔ ∃ i ∈ l, i.val = j := by
  induction l with
  | nil => simp [encodeVertices]
  | cons i is ih =>
      rw [encodeVertices, Nat.testBit_lor, Bool.or_eq_true, ih]
      simp [Nat.testBit_two_pow, List.mem_cons, or_and_right, exists_or]

def encodeFinset {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  encodeVertices ((List.finRange n).filter (fun i => decide (i ∈ S)))

theorem encodeFinset_testBit {n : ℕ} (S : Finset (Fin n)) (j : ℕ) :
    (encodeFinset S).testBit j = true ↔ ∃ i ∈ S, i.val = j := by
  simp [encodeFinset, encodeVertices_testBit]

theorem encodeFinset_testBit_fin {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    (encodeFinset S).testBit i.val = true ↔ i ∈ S := by
  simp [encodeFinset_testBit, Fin.ext_iff.symm]

theorem encodeVertices_toFinset {n : ℕ} (l : List (Fin n)) :
    encodeFinset l.toFinset = encodeVertices l := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  simp [encodeFinset_testBit, encodeVertices_testBit]

def decodeFinset {n : ℕ} (x : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x.testBit i.val = true)

theorem decodeFinset_encode {n : ℕ} (S : Finset (Fin n)) : decodeFinset (encodeFinset S) = S := by
  ext i
  simp [decodeFinset, encodeFinset_testBit_fin]

theorem encode_disjoint {n : ℕ} {S T : Finset (Fin n)} (h : Disjoint S T) :
    encodeFinset S &&& encodeFinset T = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, Nat.zero_testBit]
  apply Bool.eq_false_iff.mpr
  intro he
  rw [Bool.and_eq_true] at he
  obtain ⟨hS, hT⟩ := he
  obtain ⟨a, ha, haVal⟩ := (encodeFinset_testBit S i).mp hS
  obtain ⟨b, hb, hbVal⟩ := (encodeFinset_testBit T i).mp hT
  have hEq : a = b := Fin.ext (haVal.trans hbVal.symm)
  exact Finset.disjoint_left.mp h ha (hEq.symm ▸ hb)

theorem encode_nonDisjoint_union {n : ℕ} {S T U : Finset (Fin n)}
    (h : ¬ Disjoint S (T ∪ U)) : ((encodeFinset T ||| encodeFinset U) &&& encodeFinset S) ≠ 0 := by
  obtain ⟨i, hi, hTU⟩ := Finset.not_disjoint_iff.mp h
  have hHit : ((encodeFinset T ||| encodeFinset U) &&& encodeFinset S).testBit i.val = true := by
    rw [Nat.testBit_land, Nat.testBit_lor]
    simp only [Bool.and_eq_true, Bool.or_eq_true, encodeFinset_testBit_fin]
    exact ⟨Finset.mem_union.mp hTU, hi⟩
  intro hZero
  rw [hZero, Nat.zero_testBit] at hHit
  contradiction

private def extendable {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (i j : Fin n) :
    Bool := decide (i < j) && !(decide (H.Adj i j))

private theorem extendable_iff {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (i j : Fin n) :
    extendable H i j = true ↔ i < j ∧ Hᶜ.Adj i j := by
  by_cases hij : i < j
  · simp [extendable, hij, ne_of_lt hij]
  · simp [extendable, hij]

private def findIndependent {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    ℕ → List (Fin n) → List (List (Fin n))
  | 0, _ => [[]]
  | k + 1, xs => xs.flatMap fun i =>
      (findIndependent H k (xs.filter (extendable H i))).map fun l => i :: l

private theorem findIndependent_complete {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (k : ℕ) (xs : List (Fin n)) (S : Finset (Fin n)) (hCard : S.card = k)
    (hS : Hᶜ.IsClique (S : Set (Fin n))) (hAll : ∀ i ∈ S, i ∈ xs) :
    ∃ l ∈ findIndependent H k xs, l.toFinset = S := by
  induction k generalizing xs S with
  | zero =>
      have hz := Finset.card_eq_zero.mp hCard
      subst S
      exact ⟨[], by simp [findIndependent], by simp⟩
  | succ k ih =>
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      let i := S.min' hne
      have hi : i ∈ S := S.min'_mem hne
      obtain ⟨l, hl, hL⟩ := ih (xs.filter (extendable H i)) (S.erase i)
        (by rw [Finset.card_erase_of_mem hi, hCard]; omega) (hS.subset (Finset.erase_subset i S)) (by
          intro j hj
          obtain ⟨hji, hjS⟩ := Finset.mem_erase.mp hj
          exact List.mem_filter.mpr ⟨hAll _ hjS, (extendable_iff H i j).mpr
            ⟨lt_of_le_of_ne (S.min'_le j hjS) hji.symm, hS hi hjS hji.symm⟩⟩)
      refine ⟨i :: l, ?_, ?_⟩
      · exact List.mem_flatMap.mpr ⟨i, hAll _ hi, List.mem_map.mpr ⟨l, hl, rfl⟩⟩
      · rw [List.toFinset_cons, hL, Finset.insert_erase hi]

private theorem findIndependent_sound {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (k : ℕ) (xs : List (Fin n)) (l : List (Fin n)) (h : l ∈ findIndependent H k xs) :
    Hᶜ.IsNClique k l.toFinset ∧ ∀ i ∈ l, i ∈ xs := by
  induction k generalizing xs l with
  | zero => simp [findIndependent] at h; subst l; simp
  | succ k ih =>
      change l ∈ xs.flatMap (fun i =>
        (findIndependent H k (xs.filter (extendable H i))).map fun l => i :: l) at h
      obtain ⟨i, hi, hm⟩ := List.mem_flatMap.mp h
      obtain ⟨l', hTail, rfl⟩ := List.mem_map.mp hm
      obtain ⟨hClique, hVertices⟩ := ih _ l' hTail
      rw [List.toFinset_cons]
      constructor
      · apply hClique.insert
        intro j hj
        exact ((extendable_iff H i j).mp (List.mem_filter.mp (hVertices j (by simpa using hj))).2).2
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hi
        · exact (List.mem_filter.mp (hVertices j hj)).1

def independentMasks {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (k : ℕ) :
    List ℕ :=
  (findIndependent H k (List.finRange n).reverse).map encodeVertices

theorem independentMasks_complete {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (S : Finset (Fin n)) (hS : Hᶜ.IsClique (S : Set (Fin n))) :
    encodeFinset S ∈ independentMasks H S.card := by
  obtain ⟨l, hl, hL⟩ := findIndependent_complete H S.card (List.finRange n).reverse S rfl hS (by simp)
  have hm : encodeVertices l ∈ independentMasks H S.card := List.mem_map_of_mem hl
  rwa [← encodeVertices_toFinset, hL] at hm

theorem independentMasks_sound {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (k m : ℕ) (hm : m ∈ independentMasks H k) :
    ∃ S, Hᶜ.IsNClique k S ∧ encodeFinset S = m := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
  exact ⟨l.toFinset, (findIndependent_sound H k _ l hl).1, encodeVertices_toFinset l⟩

end OMA.RamseyCatalogue

namespace OMA.RamseyCatalogue

open SimpleGraph Finset

theorem encode_inter {n : ℕ} (S T : Finset (Fin n)) :
    encodeFinset (S ∩ T) = encodeFinset S &&& encodeFinset T := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [Nat.testBit_land, Bool.and_eq_true, encodeFinset_testBit, encodeFinset_testBit,
    encodeFinset_testBit]
  constructor
  · rintro ⟨a, ha, he⟩
    exact ⟨⟨a, (Finset.mem_inter.mp ha).1, he⟩, ⟨a, (Finset.mem_inter.mp ha).2, he⟩⟩
  · rintro ⟨⟨a, ha, hA⟩, ⟨b, hb, hB⟩⟩
    have he : a = b := Fin.ext (hA.trans hB.symm)
    exact ⟨a, Finset.mem_inter.mpr ⟨ha, he.symm ▸ hb⟩, hA⟩

theorem encode_union {n : ℕ} (S T : Finset (Fin n)) :
    encodeFinset (S ∪ T) = encodeFinset S ||| encodeFinset T := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [Nat.testBit_lor, Bool.or_eq_true, encodeFinset_testBit, encodeFinset_testBit,
    encodeFinset_testBit]
  simp only [Finset.mem_union, or_and_right, exists_or]

theorem encode_finset_empty {n : ℕ} : encodeFinset (∅ : Finset (Fin n)) = 0 := by
  simp [encodeFinset, encodeVertices]

theorem encode_disjoint_iff {n : ℕ} (S T : Finset (Fin n)) :
    encodeFinset S &&& encodeFinset T = 0 ↔ Disjoint S T := by
  refine ⟨?_, encode_disjoint⟩
  intro h
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hBit : (encodeFinset S &&& encodeFinset T).testBit i.val = true := by
    rw [Nat.testBit_land, Bool.and_eq_true, encodeFinset_testBit_fin, encodeFinset_testBit_fin]
    exact ⟨hi, hj⟩
  rw [h, Nat.zero_testBit] at hBit
  contradiction

def avoidanceMask (witnesses : List ℕ) (row : ℕ) : ℕ :=
  witnesses.foldr (fun q rest => Nat.bit (decide (row &&& q = 0)) rest) 0

theorem avoidanceMask_testBit (witnesses : List ℕ) (row i : ℕ) :
    (avoidanceMask witnesses row).testBit i = true ↔
      ∃ h : i < witnesses.length, row &&& witnesses[i] = 0 := by
  induction witnesses generalizing i with
  | nil => simp [avoidanceMask]
  | cons q qs ih =>
      cases i with
      | zero => simp [avoidanceMask]
      | succ i =>
          simp only [avoidanceMask, List.foldr_cons, Nat.testBit_bit_succ, List.length_cons,
            Nat.succ_lt_succ_iff, List.getElem_cons_succ] at *
          exact ih i

private theorem foldr_land_bit (rows : List ℕ) (initial i : ℕ) :
    ((rows.foldr Nat.land initial).testBit i = true) ↔
      initial.testBit i = true ∧ ∀ x ∈ rows, x.testBit i = true := by
  induction rows with
  | nil => simp
  | cons x rows ih =>
      change ((x &&& rows.foldr Nat.land initial).testBit i = true) ↔ _
      rw [Nat.testBit_land, Bool.and_eq_true, ih]
      simp only [List.mem_cons]
      constructor
      · rintro ⟨hx, hi, hr⟩
        refine ⟨hi, ?_⟩
        intro y hy
        rcases hy with rfl | hy
        · exact hx
        · exact hr y hy
      · rintro ⟨hi, h⟩
        exact ⟨h x (Or.inl rfl), hi, fun y hy => h y (Or.inr hy)⟩

theorem avoidance_meet_zero (witnesses : List ℕ) (rows : List ℕ) (last : ℕ)
    (h : ∀ s ∈ witnesses, (∀ row ∈ last :: rows, row &&& s = 0) → False) :
    (rows.map (avoidanceMask witnesses)).foldr Nat.land (avoidanceMask witnesses last) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit]
  apply Bool.eq_false_iff.mpr
  intro he
  obtain ⟨hl, hRows⟩ := (foldr_land_bit _ _ _).mp he
  obtain ⟨hi, hLast⟩ := (avoidanceMask_testBit _ _ _).mp hl
  apply h _ (List.getElem_mem hi)
  intro row hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hLast
  · obtain ⟨_, hr⟩ := (avoidanceMask_testBit _ _ _).mp
      (hRows _ (List.mem_map_of_mem hr))
    exact hr

theorem glued_avoidance_meet_zero {d n s q : ℕ} (H : SimpleGraph (Fin n))
    (B : Fin d → Finset (Fin n)) (hI : (glued H B)ᶜ.CliqueFree s)
    (witnesses : List ℕ) (hWitnesses : ∀ x ∈ witnesses, ∃ T : Finset (Fin n),
      Hᶜ.IsNClique q T ∧ encodeFinset T = x)
    (rows : List (Fin d)) (last : Fin d) (hDistinct : (last :: rows).Nodup)
    (hSize : s ≤ q + (last :: rows).length) :
    (rows.map (fun i => avoidanceMask witnesses (encodeFinset (B i)))).foldr Nat.land
      (avoidanceMask witnesses (encodeFinset (B last))) = 0 := by
  have hm := avoidance_meet_zero witnesses (rows.map (fun i => encodeFinset (B i)))
    (encodeFinset (B last)) (by
      intro x hx ha
      obtain ⟨T, hT, rfl⟩ := hWitnesses x hx
      have hSizeLess := attachment_avoiding_size H B hI T hT.isClique (last :: rows).toFinset (by
        intro i hi
        apply (encode_disjoint_iff (B i) T).mp
        have hiL := List.mem_toFinset.mp hi
        rcases List.mem_cons.mp hiL with rfl | hiL
        · exact ha _ (by simp)
        · exact ha _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hiL)))
      rw [List.toFinset_card_of_nodup hDistinct, hT.card_eq] at hSizeLess
      omega)
  rw [List.map_map] at hm
  exact hm

end OMA.RamseyCatalogue

namespace OMA.RamseyCatalogue

open SimpleGraph

def checkGraphRelabel {n : ℕ} (G K : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    [DecidableRel K.Adj] (e : Fin n → Fin n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    decide (e i = e j ↔ i = j) && decide (K.Adj (e i) (e j) ↔ G.Adj i j)

theorem graph_iso_of_check {n : ℕ} (G K : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    [DecidableRel K.Adj] (e : Fin n → Fin n) (h : checkGraphRelabel G K e = true) :
    Nonempty (G ≃g K) := by
  have hPair (i j : Fin n) :
      (e i = e j ↔ i = j) ∧ (K.Adj (e i) (e j) ↔ G.Adj i j) := by
    have hi := List.all_eq_true.mp h i (by simp)
    have hj := List.all_eq_true.mp hi j (by simp)
    rw [Bool.and_eq_true] at hj
    exact ⟨of_decide_eq_true hj.1, of_decide_eq_true hj.2⟩
  have hInjective : Function.Injective e := fun _ _ he => (hPair _ _).1.mp he
  let eqv : Fin n ≃ Fin n := Equiv.ofBijective e
    ⟨hInjective, Finite.surjective_of_injective hInjective⟩
  exact ⟨⟨eqv, fun {i j} => (hPair i j).2⟩⟩

end OMA.RamseyCatalogue

/-
# No three-attachment extension of the thirteen-vertex base

The base adjacency row masks were decoded from Brendan McKay's Ramsey graph
catalogue, https://users.cecs.anu.edu.au/~bdm/data/r35_13.g6, CC BY 4.0.
The selected independent-four witnesses and the finite compatibility test
are checked by Lean's kernel.
-/

namespace OMA.RamseyCatalogue

open SimpleGraph Finset

def base13Rows : Fin 13 → ℕ := ![0x1e, 0x621, 0x1481, 0x1901, 0xa41, 0x8c2, 0x1130, 0x324, 0x4c8, 0x1092, 0x906, 0x438, 0x24c]

def base13 : SimpleGraph (Fin 13) := graphFromRows base13Rows

instance base13AdjDecidable : DecidableRel base13.Adj := graphFromRowsAdj _

private def attachmentChunks : List (List ℕ) :=
  [
    [0x1800, 0x1400, 0xa00, 0x600, 0x1100, 0x900, 0x300, 0x1080, 0x880, 0x480, 0x840, 0x440],
    [0x240, 0xc0, 0x1020, 0x420, 0x220, 0x120, 0x1010, 0x410, 0x110, 0x90, 0x30, 0x408],
    [0x208, 0x88, 0x48, 0x28, 0x18, 0x804, 0x204, 0x104, 0x44, 0x24, 0x14, 0xc],
    [0x1002, 0x802, 0x102, 0x82, 0x42, 0x12, 0xa, 0x6, 0x1001, 0x801, 0x401, 0x201],
    [0x101, 0x81, 0x41, 0x21, 0x1900, 0xb00, 0x1880, 0x1480, 0xa40, 0x640, 0x8c0, 0x4c0],
    [0x1420, 0x620, 0x1120, 0x320, 0x1410, 0x1110, 0x1090, 0x490, 0x1030, 0x430, 0x130, 0x608],
    [0x488, 0x448, 0x248, 0xc8, 0x428, 0x228, 0x418, 0x98, 0x38, 0xa04, 0x904, 0x304],
    [0x844, 0x244, 0x224, 0x124, 0x114, 0x34, 0x20c, 0x4c, 0x2c, 0x1c, 0x1802, 0x1102],
    [0x902, 0x1082, 0x882, 0x842, 0xc2, 0x1012, 0x112, 0x92, 0x8a, 0x4a, 0x1a, 0x806],
    [0x106, 0x46, 0x16, 0xe, 0x1801, 0x1401, 0xa01, 0x601, 0x1101, 0x901, 0x301, 0x1081],
    [0x881, 0x481, 0x841, 0x441, 0x241, 0xc1, 0x1021, 0x421, 0x221, 0x121, 0x1490, 0x1430],
    [0x1130, 0x648, 0x4c8, 0x628, 0x498, 0x438, 0xb04, 0xa44, 0x324, 0x134, 0x24c, 0x22c],
    [0x3c, 0x1902, 0x1882, 0x8c2, 0x1112, 0x1092, 0xca, 0x9a, 0x906, 0x846, 0x116, 0x4e],
    [0x1e, 0x1901, 0xb01, 0x1881, 0x1481, 0xa41, 0x641, 0x8c1, 0x4c1, 0x1421, 0x621, 0x1121],
    [0x321]
  ]

private def witnesses : List ℕ :=
  [0x1490, 0x1130, 0x648, 0x4c8, 0x628, 0x498, 0x438, 0xb04, 0x324, 0x24c, 0x22c, 0x3c, 0x8c2, 0x1092, 0x906, 0x1e]

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem attachmentChunks_correct :
    attachmentChunks.flatten = independentMasks base13 2 ++ independentMasks base13 3 ++
      independentMasks base13 4 := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem base13_witnesses_correct :
    witnesses.all (fun x => decide (x ∈ independentMasks base13 4)) = true := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem independentMasks_base13_five : independentMasks base13 5 = [] := by
  decide +kernel

private theorem base_degree_four (x : Fin 13) : base13.degree x = 4 := by
  fin_cases x <;> decide +kernel

private def compatible (a b : ℕ) : Bool :=
  ((a &&& b) == 0) && witnesses.all (fun s => ((a ||| b) &&& s) != 0)

private def canExtend (a : ℕ) : Bool :=
  let good := attachmentChunks.flatten.filter (compatible a)
  good.any (fun b => good.any (compatible b))

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem clause_0 : attachmentChunks[0].any canExtend = false := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem clause_1 : attachmentChunks[1].any canExtend = false := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem clause_2 : attachmentChunks[2].any canExtend = false := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem clause_3 : attachmentChunks[3].any canExtend = false := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem clause_4 : attachmentChunks[4].any canExtend = false := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem clause_5 : attachmentChunks[5].any canExtend = false := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem clause_6 : attachmentChunks[6].any canExtend = false := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem clause_7 : attachmentChunks[7].any canExtend = false := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem clause_8 : attachmentChunks[8].any canExtend = false := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem clause_9 : attachmentChunks[9].any canExtend = false := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem clause_10 : attachmentChunks[10].any canExtend = false := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem clause_11 : attachmentChunks[11].any canExtend = false := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem clause_12 : attachmentChunks[12].any canExtend = false := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem clause_13 : attachmentChunks[13].any canExtend = false := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 50000000 in
private theorem clause_14 : attachmentChunks[14].any canExtend = false := by
  decide +kernel

private theorem no_triangle_scan : attachmentChunks.flatten.any canExtend = false := by
  apply List.any_eq_false.mpr
  intro x hx
  obtain ⟨ls, hMem, hL⟩ := List.mem_flatten.mp hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hMem
  have h : ∀ j : Fin attachmentChunks.length, attachmentChunks[j.val].any canExtend = false := by
    intro j
    fin_cases j
    · exact clause_0
    · exact clause_1
    · exact clause_2
    · exact clause_3
    · exact clause_4
    · exact clause_5
    · exact clause_6
    · exact clause_7
    · exact clause_8
    · exact clause_9
    · exact clause_10
    · exact clause_11
    · exact clause_12
    · exact clause_13
    · exact clause_14
  exact List.any_eq_false.mp (h ⟨i, hi⟩) x hL

theorem glued_base13_impossible (B : Fin 3 → Finset (Fin 13))
    (hT : (glued base13 B).CliqueFree 3) (hI : (glued base13 B)ᶜ.CliqueFree 6)
    (hMin : ∀ i, 3 ≤ (glued base13 B).degree (near i))
    (hMax : ∀ j, (glued base13 B).degree (far j) ≤ 5) : False := by
  have hInd i := attachment_independent base13 B hT i
  have hCard i : 2 ≤ (B i).card ∧ (B i).card ≤ 4 := by
    constructor
    · have h := hMin i
      rw [degree_near] at h
      omega
    · by_contra! hw
      obtain ⟨T, hTB, hCard⟩ := Finset.exists_subset_card_eq (show 5 ≤ (B i).card by omega)
      have hT := independentMasks_complete base13 T ((hInd i).subset hTB)
      rw [hCard, independentMasks_base13_five] at hT
      exact List.not_mem_nil hT
  have hMem i : encodeFinset (B i) ∈ attachmentChunks.flatten := by
    have h := independentMasks_complete base13 _ (hInd i)
    have hlo := (hCard i).1
    have hhi := (hCard i).2
    generalize he : (B i).card = k at *
    rw [attachmentChunks_correct]
    interval_cases k <;> simp only [List.mem_append] <;> tauto
  have hCompat (i j : Fin 3) (hij : i ≠ j) :
      compatible (encodeFinset (B i)) (encodeFinset (B j)) = true := by
    have hd : Disjoint (B i) (B j) := by
      apply Finset.disjoint_left.mpr
      intro x hi hj
      have hSubs : ({i, j} : Finset (Fin 3)) ⊆ univ.filter (fun t => x ∈ B t) := by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · simp [hi]
        · have he := Finset.mem_singleton.mp ht
          subst t
          simp [hj]
      have h := Finset.card_le_card hSubs
      rw [Finset.card_pair hij] at h
      have hUpper := hMax x
      rw [degree_far, base_degree_four] at hUpper
      omega
    unfold compatible
    rw [encode_disjoint hd]
    simp only [beq_self_eq_true, Bool.true_and]
    apply List.all_eq_true.mpr
    intro s hs
    have hw := of_decide_eq_true (List.all_eq_true.mp base13_witnesses_correct s hs)
    obtain ⟨T, hT, rfl⟩ := independentMasks_sound base13 4 s hw
    have hHit : ¬ Disjoint T (B i ∪ B j) := by
      intro hD
      have hSmall := attachment_avoiding_size base13 B hI T hT.isClique {i, j} (by
        intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact (hD.mono_right Finset.subset_union_left).symm
        · obtain rfl := Finset.mem_singleton.mp hr
          exact (hD.mono_right Finset.subset_union_right).symm)
      rw [Finset.card_pair hij, hT.card_eq] at hSmall
      omega
    simpa using encode_nonDisjoint_union hHit
  have hExists : attachmentChunks.flatten.any canExtend = true := by
    exact List.any_eq_true.mpr ⟨_, hMem 0, List.any_eq_true.mpr
      ⟨_, List.mem_filter.mpr ⟨hMem 1, hCompat 0 1 (by decide)⟩, List.any_eq_true.mpr
        ⟨_, List.mem_filter.mpr ⟨hMem 2, hCompat 0 2 (by decide)⟩, hCompat 1 2 (by decide)⟩⟩⟩
  rw [no_triangle_scan] at hExists
  contradiction

end OMA.RamseyCatalogue

namespace OMA.RamseyCatalogue

open SimpleGraph Finset

structure ProfileRow where
  vertices : ℕ
  avoidTwo : ℕ
  avoidThree : ℕ
  avoidFour : ℕ
  deriving DecidableEq

def profileRow (w2 w3 w4 : List ℕ) (k : ℕ) : ProfileRow :=
  ⟨k, avoidanceMask w2 k, avoidanceMask w3 k, avoidanceMask w4 k⟩

def compatiblePair (tight : ℕ) (a b : ProfileRow) : Bool :=
  decide (a.vertices ≤ b.vertices) &&
    ((a.avoidFour &&& b.avoidFour) == 0) &&
    ((a.vertices &&& b.vertices &&& tight) == 0)

def compatibleTriple (a b c : ProfileRow) : Bool :=
  ((a.avoidThree &&& b.avoidThree &&& c.avoidThree) == 0) &&
    ((a.vertices &&& b.vertices &&& c.vertices) == 0)

def coversLow (needed : ℕ) (a b c u : ProfileRow) : Bool :=
  (((a.vertices ||| b.vertices ||| c.vertices ||| u.vertices) &&& needed) == needed) &&
    ((a.avoidTwo &&& b.avoidTwo &&& c.avoidTwo &&& u.avoidTwo) == 0)

abbrev FourMasks := ℕ × ℕ × ℕ × ℕ

def feasibleFrom (options : List ProfileRow) (tight needed : ℕ) (a : ProfileRow) :
    List FourMasks :=
  let Bs := options.filter (compatiblePair tight a)
  Bs.flatMap fun b =>
    let Cs := Bs.filter (compatiblePair tight b)
    (Cs.filter (compatibleTriple a b)).flatMap fun c =>
      let Ds := Cs.filter (compatiblePair tight c)
      (Ds.filter (fun u => compatibleTriple a b u &&
        compatibleTriple a c u && compatibleTriple b c u && coversLow needed a b c u)).map
          fun u => (a.vertices, b.vertices, c.vertices, u.vertices)

theorem mem_feasibleFrom (options : List ProfileRow) (tight needed : ℕ) (a b c u : ProfileRow)
    (hb : b ∈ options) (hc : c ∈ options) (hu : u ∈ options)
    (hab : compatiblePair tight a b = true) (hac : compatiblePair tight a c = true)
    (hau : compatiblePair tight a u = true) (hbc : compatiblePair tight b c = true)
    (hbu : compatiblePair tight b u = true) (hcu : compatiblePair tight c u = true)
    (habc : compatibleTriple a b c = true) (habu : compatibleTriple a b u = true)
    (hacu : compatibleTriple a c u = true) (hbcu : compatibleTriple b c u = true)
    (hAll : coversLow needed a b c u = true) :
    (a.vertices, b.vertices, c.vertices, u.vertices) ∈ feasibleFrom options tight needed a := by
  apply List.mem_flatMap.mpr
  refine ⟨b, List.mem_filter.mpr ⟨hb, hab⟩, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨c, List.mem_filter.mpr ⟨List.mem_filter.mpr
    ⟨List.mem_filter.mpr ⟨hc, hac⟩, hbc⟩, habc⟩, ?_⟩
  apply List.mem_map.mpr
  refine ⟨u, List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_filter.mpr
    ⟨List.mem_filter.mpr ⟨hu, hau⟩, hbu⟩, hcu⟩, ?_⟩, rfl⟩
  simp only [habu, hacu, hbcu, hAll, Bool.and_self]

theorem encode_subset_meet {n : ℕ} (S T : Finset (Fin n)) (h : S ⊆ T) :
    encodeFinset T &&& encodeFinset S = encodeFinset S := by
  rw [← encode_inter, Finset.inter_eq_right.mpr h]

theorem profilePair_of_glued {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (B : Fin 4 → Finset (Fin n)) (hi : (glued H B)ᶜ.CliqueFree 6)
    (hMax : ∀ v, (glued H B).degree (far v) ≤ 5)
    (w2 w3 w4 : List ℕ) (hW : ∀ x ∈ w4, ∃ T : Finset (Fin n),
      Hᶜ.IsNClique 4 T ∧ encodeFinset T = x)
    (i j : Fin 4) (hij : i ≠ j) (hord : encodeFinset (B i) ≤ encodeFinset (B j)) :
    compatiblePair (encodeFinset (univ.filter fun v => H.degree v = 4))
      (profileRow w2 w3 w4 (encodeFinset (B i)))
      (profileRow w2 w3 w4 (encodeFinset (B j))) = true := by
  have hAvoid := glued_avoidance_meet_zero H B hi w4 hW [i] j
    (by simp [Ne.symm hij]) (by change 6 ≤ 6; exact le_rfl)
  change (avoidanceMask w4 (encodeFinset (B i)) &&& avoidanceMask w4 (encodeFinset (B j))) = 0 at hAvoid
  have hE : B i ∩ B j ∩ (univ.filter fun v => H.degree v = 4) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hB, hD⟩ := Finset.mem_inter.mp hv
    have hdeg := (Finset.mem_filter.mp hD).2
    obtain ⟨hvI, hvJ⟩ := Finset.mem_inter.mp hB
    have hInside : ({i, j} : Finset (Fin 4)) ⊆ univ.filter (fun t => v ∈ B t) := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · simp [hvI]
      · obtain rfl := Finset.mem_singleton.mp ht
        simp [hvJ]
    have h := Finset.card_le_card hInside
    rw [Finset.card_pair hij] at h
    have hCap := hMax v
    rw [degree_far, hdeg] at hCap
    omega
  have hq := congrArg encodeFinset hE
  rw [encode_inter, encode_inter, encode_finset_empty] at hq
  simp [compatiblePair, profileRow, hord, hAvoid, hq]

theorem profileTriple_of_glued {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (B : Fin 4 → Finset (Fin n)) (hi : (glued H B)ᶜ.CliqueFree 6)
    (hMax : ∀ v, (glued H B).degree (far v) ≤ 5) (hMinH : ∀ v, 3 ≤ H.degree v)
    (w2 w3 w4 : List ℕ) (hW : ∀ x ∈ w3, ∃ T : Finset (Fin n),
      Hᶜ.IsNClique 3 T ∧ encodeFinset T = x)
    (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    compatibleTriple
      (profileRow w2 w3 w4 (encodeFinset (B i)))
      (profileRow w2 w3 w4 (encodeFinset (B j)))
      (profileRow w2 w3 w4 (encodeFinset (B l))) = true := by
  have hAvoid := glued_avoidance_meet_zero H B hi w3 hW [i, j] l
    (by simp [hij, hil.symm, hjl.symm]) (by change 6 ≤ 6; exact le_rfl)
  change (avoidanceMask w3 (encodeFinset (B i)) &&&
      (avoidanceMask w3 (encodeFinset (B j)) &&& avoidanceMask w3 (encodeFinset (B l)))) = 0 at hAvoid
  have hE : B i ∩ B j ∩ B l = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hB, hvL⟩ := Finset.mem_inter.mp hv
    obtain ⟨hvI, hvJ⟩ := Finset.mem_inter.mp hB
    have hInside : ({i, j, l} : Finset (Fin 4)) ⊆ univ.filter (fun t => v ∈ B t) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · simp [hvI]
      · simp [hvJ]
      · simp [hvL]
    have hCard : ({i, j, l} : Finset (Fin 4)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hij, hil]), Finset.card_pair hjl]
    have h := Finset.card_le_card hInside
    rw [hCard] at h
    have hCap := hMax v
    rw [degree_far] at hCap
    have := hMinH v
    omega
  have hq := congrArg encodeFinset hE
  rw [encode_inter, encode_inter, encode_finset_empty] at hq
  simp [compatibleTriple, profileRow, Nat.land_assoc, hAvoid, hq]

theorem profileCover_of_glued {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (B : Fin 4 → Finset (Fin n)) (hi : (glued H B)ᶜ.CliqueFree 6)
    (hMin : ∀ v, 4 ≤ (glued H B).degree (far v))
    (w2 w3 w4 : List ℕ) (hW : ∀ x ∈ w2, ∃ T : Finset (Fin n),
      Hᶜ.IsNClique 2 T ∧ encodeFinset T = x) :
    coversLow (encodeFinset (univ.filter fun v => H.degree v = 3))
      (profileRow w2 w3 w4 (encodeFinset (B 0)))
      (profileRow w2 w3 w4 (encodeFinset (B 1)))
      (profileRow w2 w3 w4 (encodeFinset (B 2)))
      (profileRow w2 w3 w4 (encodeFinset (B 3))) = true := by
  have hAvoid := glued_avoidance_meet_zero H B hi w2 hW [0, 1, 2] 3 (by decide) (by decide)
  change (avoidanceMask w2 (encodeFinset (B 0)) &&&
      (avoidanceMask w2 (encodeFinset (B 1)) &&&
      (avoidanceMask w2 (encodeFinset (B 2)) &&& avoidanceMask w2 (encodeFinset (B 3))))) = 0 at hAvoid
  have hSubs : univ.filter (fun v => H.degree v = 3) ⊆ B 0 ∪ B 1 ∪ B 2 ∪ B 3 := by
    intro v hv
    obtain ⟨_, hdegree⟩ := Finset.mem_filter.mp hv
    have h := hMin v
    rw [degree_far, hdegree] at h
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (univ.filter (fun i => v ∈ B i)).card by omega)
    have him := (Finset.mem_filter.mp hi).2
    simp only [Finset.mem_union]
    fin_cases i
    · exact Or.inl (Or.inl (Or.inl him))
    · exact Or.inl (Or.inl (Or.inr him))
    · exact Or.inl (Or.inr him)
    · exact Or.inr him
  have hCover := encode_subset_meet _ _ hSubs
  simp only [encode_union] at hCover
  simp [coversLow, profileRow, Nat.land_assoc, hCover, hAvoid]

end OMA.RamseyCatalogue

/-
The base and target rows come from Brendan McKay's Ramsey graph catalogue
(https://users.cecs.anu.edu.au/~bdm/data/, CC BY 4.0). The independently
generated candidate rows and relabelings are checked by the kernel.
-/

namespace OMA.RamseyCatalogue

open SimpleGraph Finset

def base12Rows : Fin 12 → Fin 12 → ℕ := ![
    ![0x540, 0xa80, 0xb20, 0x710, 0x868, 0x494, 0x291, 0x162, 0x8d, 0x4e, 0x829, 0x416],
    ![0xc40, 0x380, 0x550, 0xa60, 0xa84, 0x588, 0x8d, 0x72, 0x826, 0x41a, 0x225, 0x119],
    ![0x310, 0xa40, 0xc80, 0x520, 0x461, 0x898, 0x192, 0x264, 0x849, 0x483, 0x21c, 0x126],
    ![0xa20, 0x640, 0x888, 0x504, 0xd80, 0x4c1, 0x922, 0x234, 0x258, 0x183, 0x3a, 0x55],
    ![0x114, 0x228, 0x881, 0x442, 0x241, 0x182, 0x898, 0x464, 0xc21, 0xc12, 0x388, 0x344],
    ![0x442, 0x901, 0xa08, 0x484, 0xe80, 0xd40, 0x2a1, 0x158, 0x2a2, 0x154, 0x39, 0x36],
    ![0x812, 0x421, 0x148, 0x284, 0x241, 0x182, 0x494, 0x868, 0xa24, 0x518, 0xa42, 0x581],
    ![0x32, 0xc1, 0xc08, 0x304, 0xe01, 0x981, 0xb02, 0x622, 0x468, 0xd8, 0x194, 0x74],
    ![0x32, 0xc1, 0x908, 0x604, 0x581, 0xa41, 0x522, 0xa12, 0x254, 0x1a8, 0x858, 0x4a4],
    ![0x106, 0x841, 0x481, 0x190, 0x828, 0x250, 0x422, 0x20c, 0x609, 0x9a0, 0x944, 0x612],
    ![0x1e, 0xc81, 0xb01, 0x2c1, 0x521, 0xa90, 0xd08, 0x12a, 0xd4, 0x42c, 0x252, 0x66],
    ![0x1e, 0xc81, 0xa41, 0xb01, 0x521, 0x8d0, 0x524, 0x322, 0xd8, 0x48c, 0x252, 0x2e]
  ]

def base12 (k : Fin 12) : SimpleGraph (Fin 12) := graphFromRows (base12Rows k)
instance base12Adj (k : Fin 12) : DecidableRel (base12 k).Adj := graphFromRowsAdj _

def target17Rows : Fin 7 → Fin 17 → ℕ := ![
    ![0x1c200, 0x12880, 0x9500, 0x1a140, 0x150a0, 0x2e10, 0x5c08, 0x8612, 0x4a0c, 0x11a1, 0x100e4, 0x8162, 0x2254, 0x502a, 0x2151, 0x88d, 0x41b],
    ![0x18600, 0x15080, 0xa900, 0x12890, 0xd108, 0x16240, 0x9c20, 0x830a, 0x10494, 0x18a1, 0x6141, 0x424c, 0x2252, 0x142c, 0xc32, 0xd5, 0x12b],
    ![0x10310, 0x8490, 0x14808, 0xb004, 0x63, 0xaa10, 0x15410, 0x17002, 0xe801, 0x5421, 0x2a42, 0x1524, 0xac8, 0x5a8, 0x3c4, 0x1012a, 0x80c5],
    ![0x780, 0x14804, 0xb002, 0x1c220, 0x1a140, 0x2d08, 0x5610, 0x7801, 0x5031, 0x2849, 0x18061, 0x82a2, 0x101c4, 0x2b4, 0x1ca, 0xc1c, 0x141a],
    ![0x1e000, 0x2224, 0x11102, 0x8890, 0x4448, 0x4582, 0x2390, 0x11068, 0x8864, 0x18842, 0x13030, 0x6308, 0xc484, 0xc43, 0x1831, 0x1309, 0x685],
    ![0x1e, 0x6061, 0x15801, 0x18601, 0xa181, 0x10a82, 0x11502, 0x5430, 0x4a50, 0x3128, 0x28c8, 0x8524, 0x82c4, 0x10612, 0x8186, 0x5818, 0x206c],
    ![0x1e, 0x6061, 0x14c01, 0x18281, 0xb101, 0x11902, 0x11602, 0x3c08, 0x4630, 0x2948, 0x81c4, 0x82a4, 0x40f0, 0x10292, 0x9106, 0x4c18, 0x206c]
  ]

def target17 (k : Fin 7) : SimpleGraph (Fin 17) := graphFromRows (target17Rows k)
instance target17Adj (k : Fin 7) : DecidableRel (target17 k).Adj := graphFromRowsAdj _

private def degreeThreeMask : Fin 12 → ℕ :=
  ![0x3, 0x3, 0xf, 0xf, 0x3f, 0xf, 0x3f, 0xf, 0xf, 0xff, 0x0, 0x0]

private def degreeFourMask : Fin 12 → ℕ :=
  ![0xffc, 0xffc, 0xff0, 0xff0, 0xfc0, 0xff0, 0xfc0, 0xff0, 0xff0, 0xf00, 0xfff, 0xfff]

private def witnessMasks (k : Fin 12) (q : ℕ) : List ℕ :=
  match k.val, q with
  | 0, 2 => [0xa00, 0x600, 0x900, 0x500, 0x300, 0x880, 0x480, 0x280, 0x840, 0x440, 0x140, 0x820,
      0x220, 0x120, 0x60, 0x410, 0x210, 0x110, 0x90, 0x808, 0x88, 0x48, 0x28, 0x404,
      0x84, 0x44, 0x14, 0xc, 0x402, 0x102, 0x42, 0x22, 0x12, 0xa, 0x6, 0x801,
      0x201, 0x81, 0x21, 0x11, 0x9, 0x5, 0x3]
  | 0, 3 => [0xb00, 0x700, 0xa80, 0x680, 0x940, 0x540, 0xa20, 0x920, 0x320, 0x860, 0x160, 0x610,
      0x510, 0x310, 0x490, 0x290, 0x888, 0x848, 0x828, 0x68, 0x484, 0x444, 0x414, 0x94,
      0x8c, 0x4c, 0x502, 0x442, 0x142, 0x122, 0x62, 0x412, 0x112, 0x4a, 0x2a, 0x406,
      0x46, 0x16, 0xe, 0xa01, 0x881, 0x281, 0x821, 0x221, 0x211, 0x91, 0x809, 0x89,
      0x29, 0x85, 0x15, 0xd, 0x23, 0x13, 0xb, 0x7]
  | 0, 4 => [0xb20, 0x960, 0x710, 0x690, 0x868, 0x494, 0x542, 0x162, 0x512, 0x6a, 0x446, 0x416,
      0x4e, 0xa81, 0xa21, 0x291, 0x889, 0x829, 0x95, 0x8d, 0x2b, 0x17, 0xf]
  | 1, 2 => [0xc00, 0xa00, 0x500, 0x300, 0x880, 0x480, 0x280, 0x180, 0x840, 0x440, 0x240, 0x140,
      0x820, 0x220, 0x60, 0x410, 0x110, 0x50, 0x30, 0x408, 0x108, 0x88, 0x18, 0x804,
      0x204, 0x84, 0x24, 0xc, 0x802, 0x402, 0x42, 0x22, 0x12, 0xa, 0x6, 0x201,
      0x101, 0x81, 0x21, 0x11, 0x9, 0x5, 0x3]
  | 1, 3 => [0xc80, 0xa80, 0x580, 0x380, 0xc40, 0xa40, 0x540, 0x340, 0xa20, 0x860, 0x260, 0x510,
      0x450, 0x150, 0x70, 0x508, 0x488, 0x188, 0x418, 0x118, 0xa04, 0x884, 0x284, 0x824,
      0x224, 0x8c, 0xc02, 0x842, 0x442, 0x822, 0x62, 0x412, 0x52, 0x32, 0x40a, 0x1a,
      0x806, 0x26, 0xe, 0x301, 0x281, 0x181, 0x221, 0x111, 0x31, 0x109, 0x89, 0x19,
      0x205, 0x85, 0x25, 0xd, 0x23, 0x13, 0xb, 0x7]
  | 1, 4 => [0xa60, 0x550, 0x588, 0x518, 0xa84, 0xa24, 0xc42, 0x862, 0x452, 0x72, 0x41a, 0x826,
      0x381, 0x189, 0x119, 0x285, 0x225, 0x8d, 0x33, 0x1b, 0x27, 0xf]
  | 2, 2 => [0xc00, 0xa00, 0x500, 0x300, 0x880, 0x480, 0x180, 0x840, 0x440, 0x240, 0x420, 0x220,
      0x120, 0x60, 0x810, 0x210, 0x110, 0x90, 0x808, 0x208, 0x88, 0x48, 0x18, 0x204,
      0x104, 0x44, 0x24, 0x14, 0xc, 0x402, 0x102, 0x82, 0x22, 0x12, 0xa, 0x6,
      0x801, 0x401, 0x81, 0x41, 0x21, 0x9, 0x5, 0x3]
  | 2, 3 => [0xc80, 0x580, 0xc40, 0xa40, 0x520, 0x320, 0x460, 0x260, 0xa10, 0x310, 0x890, 0x190,
      0xa08, 0x888, 0x848, 0x248, 0x818, 0x218, 0x98, 0x304, 0x244, 0x224, 0x124, 0x64,
      0x214, 0x114, 0x20c, 0x4c, 0x1c, 0x502, 0x482, 0x182, 0x422, 0x122, 0x112, 0x92,
      0x8a, 0x1a, 0x106, 0x26, 0x16, 0xe, 0xc01, 0x881, 0x481, 0x841, 0x441, 0x421,
      0x61, 0x809, 0x89, 0x49, 0x45, 0x25, 0xd, 0x403, 0x83, 0x23, 0xb, 0x7]
  | 2, 4 => [0xa48, 0xa18, 0x898, 0x324, 0x264, 0x314, 0x24c, 0x21c, 0x582, 0x522, 0x192, 0x9a,
      0x126, 0x116, 0x1e, 0xc81, 0xc41, 0x461, 0x889, 0x849, 0x65, 0x4d, 0x483, 0x423,
      0x8b, 0x27, 0xf]
  | 3, 2 => [0xc00, 0xa00, 0x600, 0x900, 0x500, 0x880, 0x480, 0x180, 0x440, 0x240, 0xc0, 0x820,
      0x220, 0x120, 0x210, 0x50, 0x30, 0x808, 0x208, 0x88, 0x48, 0x28, 0x18, 0x404,
      0x204, 0x104, 0x44, 0x24, 0x14, 0x802, 0x102, 0x82, 0x22, 0x12, 0xa, 0x6,
      0x401, 0x101, 0x81, 0x41, 0x11, 0x9, 0x5, 0x3]
  | 3, 3 => [0xe00, 0xd00, 0xc80, 0x980, 0x580, 0x640, 0x4c0, 0xa20, 0x920, 0x250, 0x230, 0xa08,
      0x888, 0x248, 0xc8, 0x828, 0x228, 0x218, 0x58, 0x38, 0x604, 0x504, 0x444, 0x244,
      0x224, 0x124, 0x214, 0x54, 0x34, 0x902, 0x882, 0x182, 0x822, 0x122, 0x32, 0x80a,
      0x8a, 0x2a, 0x1a, 0x106, 0x26, 0x16, 0x501, 0x481, 0x181, 0x441, 0xc1, 0x51,
      0x89, 0x49, 0x19, 0x405, 0x105, 0x45, 0x15, 0x103, 0x83, 0x13, 0xb, 0x7]
  | 3, 4 => [0xd80, 0xa28, 0x258, 0x238, 0x644, 0x254, 0x234, 0x982, 0x922, 0x88a, 0x82a, 0x3a,
      0x126, 0x36, 0x581, 0x4c1, 0xc9, 0x59, 0x505, 0x445, 0x55, 0x183, 0x8b, 0x1b,
      0x107, 0x17]
  | 4, 2 => [0xc00, 0x300, 0x880, 0x280, 0x180, 0x440, 0x240, 0x140, 0x820, 0x420, 0x220, 0x60,
      0x810, 0x410, 0x110, 0x90, 0x30, 0x808, 0x208, 0x108, 0x88, 0x28, 0x18, 0x404,
      0x204, 0x104, 0x44, 0x24, 0x14, 0xc, 0x802, 0x402, 0x102, 0x82, 0x42, 0x12,
      0x6, 0x801, 0x401, 0x201, 0x81, 0x41, 0x21, 0x9, 0x3]
  | 4, 3 => [0x380, 0x340, 0xc20, 0x460, 0x260, 0xc10, 0x890, 0x190, 0x830, 0x430, 0x308, 0x888,
      0x288, 0x188, 0x828, 0x228, 0x818, 0x118, 0x98, 0x38, 0x304, 0x444, 0x244, 0x144,
      0x424, 0x224, 0x64, 0x414, 0x114, 0x34, 0x20c, 0x10c, 0x2c, 0x1c, 0xc02, 0x882,
      0x182, 0x442, 0x142, 0x812, 0x412, 0x112, 0x92, 0x406, 0x106, 0x46, 0x16, 0xc01,
      0x881, 0x281, 0x441, 0x241, 0x821, 0x421, 0x221, 0x61, 0x809, 0x209, 0x89, 0x29,
      0x803, 0x403, 0x83, 0x43]
  | 4, 4 => [0xc30, 0x388, 0x898, 0x198, 0x838, 0x344, 0x464, 0x264, 0x434, 0x30c, 0x22c, 0x11c,
      0x3c, 0xc12, 0x892, 0x192, 0x446, 0x146, 0x416, 0x116, 0xc21, 0x461, 0x261, 0x889,
      0x289, 0x829, 0x229, 0xc03, 0x883, 0x443]
  | 5, 2 => [0xc00, 0xa00, 0x600, 0x900, 0x500, 0x880, 0x480, 0x280, 0x840, 0x440, 0x140, 0x220,
      0xa0, 0x110, 0x50, 0x30, 0x808, 0x208, 0x108, 0x48, 0x28, 0x18, 0x404, 0x104,
      0x84, 0x44, 0x24, 0x14, 0x402, 0x202, 0x82, 0x42, 0x22, 0x12, 0xa, 0x6,
      0x801, 0x201, 0x101, 0x81, 0x21, 0x11, 0x9, 0x5]
  | 5, 3 => [0xe00, 0xd00, 0xc80, 0xa80, 0x680, 0xc40, 0x940, 0x540, 0x2a0, 0x150, 0xa08, 0x908,
      0x848, 0x148, 0x228, 0x118, 0x58, 0x38, 0x504, 0x484, 0x444, 0x144, 0xa4, 0x114,
      0x54, 0x34, 0x602, 0x482, 0x282, 0x442, 0x222, 0xa2, 0x52, 0x32, 0x20a, 0x4a,
      0x2a, 0x1a, 0x406, 0x86, 0x46, 0x26, 0x16, 0xa01, 0x901, 0x881, 0x281, 0x221,
      0xa1, 0x111, 0x31, 0x809, 0x209, 0x109, 0x29, 0x19, 0x105, 0x85, 0x25, 0x15]
  | 5, 4 => [0xe80, 0xd40, 0x948, 0x158, 0x544, 0x154, 0x682, 0x2a2, 0x22a, 0x5a, 0x3a, 0x486,
      0x446, 0xa6, 0x56, 0x36, 0xa81, 0x2a1, 0xa09, 0x909, 0x229, 0x119, 0x39, 0xa5,
      0x115, 0x35]
  | 6, 2 => [0xa00, 0x500, 0x480, 0x280, 0x180, 0x840, 0x240, 0x140, 0x820, 0x420, 0x220, 0x60,
      0x810, 0x410, 0x110, 0x90, 0x30, 0x808, 0x408, 0x108, 0x48, 0x28, 0x18, 0x804,
      0x404, 0x204, 0x84, 0x24, 0x14, 0x802, 0x202, 0x102, 0x82, 0x42, 0x12, 0xa,
      0x6, 0x401, 0x201, 0x101, 0x81, 0x41, 0x21, 0x9, 0x5]
  | 6, 3 => [0x580, 0xa40, 0xa20, 0x860, 0x260, 0x510, 0x490, 0x190, 0x830, 0x430, 0x508, 0x848,
      0x148, 0x828, 0x428, 0x68, 0x818, 0x418, 0x118, 0x38, 0xa04, 0x484, 0x284, 0x824,
      0x424, 0x224, 0x814, 0x414, 0x94, 0x34, 0xa02, 0x282, 0x182, 0x842, 0x242, 0x142,
      0x812, 0x112, 0x92, 0x80a, 0x10a, 0x4a, 0x1a, 0x806, 0x206, 0x86, 0x16, 0x501,
      0x481, 0x281, 0x181, 0x241, 0x141, 0x421, 0x221, 0x61, 0x409, 0x109, 0x49, 0x29,
      0x405, 0x205, 0x85, 0x25]
  | 6, 4 => [0xa60, 0x590, 0x868, 0x518, 0x838, 0x438, 0xa24, 0x494, 0x834, 0x434, 0xa42, 0x192,
      0x84a, 0x14a, 0x81a, 0x11a, 0xa06, 0x286, 0x816, 0x96, 0x581, 0x261, 0x509, 0x149,
      0x429, 0x69, 0x485, 0x285, 0x425, 0x225]
  | 7, 2 => [0xc00, 0xa00, 0x600, 0x900, 0x300, 0x880, 0x180, 0x440, 0xc0, 0x420, 0x220, 0x60,
      0x110, 0x90, 0x50, 0x30, 0x808, 0x408, 0x88, 0x48, 0x28, 0x18, 0x204, 0x104,
      0x84, 0x44, 0x24, 0x14, 0x802, 0x402, 0x202, 0x102, 0x22, 0x12, 0xa, 0x6,
      0x801, 0x401, 0x201, 0x101, 0x81, 0x41, 0x9, 0x5]
  | 7, 3 => [0xe00, 0xb00, 0x980, 0x620, 0x460, 0x190, 0xd0, 0x70, 0xc08, 0x888, 0x448, 0xc8,
      0x428, 0x68, 0x98, 0x58, 0x38, 0x304, 0x184, 0xc4, 0x224, 0x64, 0x114, 0x94,
      0x54, 0x34, 0xc02, 0xa02, 0x602, 0x902, 0x302, 0x422, 0x222, 0x112, 0x32, 0x80a,
      0x40a, 0x2a, 0x1a, 0x206, 0x106, 0x26, 0x16, 0xc01, 0xa01, 0x601, 0x901, 0x301,
      0x881, 0x181, 0x441, 0xc1, 0x809, 0x409, 0x89, 0x49, 0x205, 0x105, 0x85, 0x45]
  | 7, 4 => [0x468, 0xd8, 0x78, 0x194, 0xd4, 0x74, 0xe02, 0xb02, 0x622, 0xc0a, 0x42a, 0x3a,
      0x306, 0x226, 0x116, 0x36, 0xe01, 0xb01, 0x981, 0xc09, 0x889, 0x449, 0xc9, 0x305,
      0x185, 0xc5]
  | 8, 2 => [0xa00, 0x600, 0x900, 0x500, 0x480, 0x180, 0x840, 0x240, 0xc0, 0x420, 0x120, 0xa0,
      0x810, 0x210, 0x50, 0x30, 0x808, 0x108, 0x88, 0x48, 0x28, 0x18, 0x404, 0x204,
      0x84, 0x44, 0x24, 0x14, 0x802, 0x402, 0x202, 0x102, 0x22, 0x12, 0xa, 0x6,
      0x801, 0x401, 0x201, 0x101, 0x81, 0x41, 0x9, 0x5]
  | 8, 3 => [0x580, 0xa40, 0x520, 0x4a0, 0x1a0, 0xa10, 0x850, 0x250, 0x908, 0x188, 0x848, 0xc8,
      0x128, 0xa8, 0x818, 0x58, 0x38, 0x604, 0x484, 0x244, 0xc4, 0x424, 0xa4, 0x214,
      0x54, 0x34, 0xa02, 0x602, 0x902, 0x502, 0x422, 0x122, 0x812, 0x212, 0x32, 0x80a,
      0x10a, 0x2a, 0x1a, 0x406, 0x206, 0x26, 0x16, 0xa01, 0x601, 0x901, 0x501, 0x481,
      0x181, 0x841, 0x241, 0xc1, 0x809, 0x109, 0x89, 0x49, 0x405, 0x205, 0x85, 0x45]
  | 8, 4 => [0x5a0, 0xa50, 0x1a8, 0x858, 0x4a4, 0x254, 0x522, 0xa12, 0x90a, 0x12a, 0x81a, 0x3a,
      0x606, 0x426, 0x216, 0x36, 0x581, 0xa41, 0x909, 0x189, 0x849, 0xc9, 0x605, 0x485,
      0x245, 0xc5]
  | 9, 2 => [0x600, 0x900, 0x880, 0x480, 0x180, 0x840, 0x240, 0x140, 0xc0, 0x820, 0x420, 0x120,
      0xa0, 0x410, 0x210, 0x110, 0x90, 0x50, 0x808, 0x408, 0x208, 0x48, 0x28, 0x804,
      0x204, 0x104, 0x44, 0x24, 0x14, 0xc, 0x402, 0x202, 0x102, 0x82, 0x22, 0x12,
      0xa, 0x6, 0x801, 0x401, 0x201, 0x81, 0x41, 0x21, 0x11, 0x9]
  | 9, 3 => [0x980, 0x940, 0x8c0, 0x1c0, 0x920, 0x8a0, 0x4a0, 0x1a0, 0x610, 0x490, 0x190, 0x250,
      0x150, 0xd0, 0x608, 0x848, 0x248, 0x828, 0x428, 0x904, 0x844, 0x244, 0x144, 0x824,
      0x124, 0x214, 0x114, 0x54, 0x80c, 0x20c, 0x4c, 0x2c, 0x602, 0x482, 0x182, 0x422,
      0x122, 0xa2, 0x412, 0x212, 0x112, 0x92, 0x40a, 0x20a, 0x2a, 0x206, 0x106, 0x26,
      0x16, 0xe, 0x601, 0x881, 0x481, 0x841, 0x241, 0xc1, 0x821, 0x421, 0xa1, 0x411,
      0x211, 0x91, 0x51, 0x809, 0x409, 0x209, 0x49, 0x29]
  | 9, 4 => [0x9c0, 0x9a0, 0x1d0, 0x944, 0x924, 0x254, 0x154, 0x84c, 0x24c, 0x82c, 0x4a2, 0x1a2,
      0x612, 0x492, 0x192, 0x60a, 0x42a, 0x126, 0x216, 0x116, 0x20e, 0x2e, 0x8c1, 0x8a1,
      0x4a1, 0x611, 0x491, 0x251, 0xd1, 0x609, 0x849, 0x249, 0x829, 0x429]
  | 10, 2 => [0xc00, 0xa00, 0x900, 0x500, 0x300, 0x880, 0x480, 0x280, 0x240, 0xc0, 0x420, 0x120,
      0x60, 0x810, 0x210, 0x90, 0x50, 0x808, 0x408, 0x108, 0x28, 0x18, 0x404, 0x84,
      0x44, 0x24, 0x14, 0xc, 0x202, 0x102, 0x42, 0x22, 0x12, 0xa, 0x6, 0x801,
      0x401, 0x201, 0x101, 0x81, 0x41, 0x21]
  | 10, 3 => [0xd00, 0xb00, 0xc80, 0xa80, 0x2c0, 0x520, 0xa10, 0x890, 0x290, 0x250, 0xd0, 0xc08,
      0x908, 0x508, 0x428, 0x128, 0x818, 0x484, 0xc4, 0x424, 0x64, 0x94, 0x54, 0x40c,
      0x2c, 0x1c, 0x302, 0x242, 0x122, 0x62, 0x212, 0x52, 0x10a, 0x2a, 0x1a, 0x46,
      0x26, 0x16, 0xe, 0xc01, 0xa01, 0x901, 0x501, 0x301, 0x881, 0x481, 0x281, 0x241,
      0xc1, 0x421, 0x121, 0x61]
  | 10, 4 => [0xa90, 0x2d0, 0xd08, 0x528, 0xd4, 0x42c, 0x252, 0x12a, 0x66, 0x56, 0x2e, 0x1e,
      0xd01, 0xb01, 0xc81, 0xa81, 0x2c1, 0x521]
  | 11, 2 => [0xc00, 0xa00, 0x900, 0x500, 0x300, 0x880, 0x480, 0x840, 0x240, 0xc0, 0x420, 0x220,
      0x120, 0x810, 0x210, 0x90, 0x50, 0x408, 0x88, 0x48, 0x28, 0x18, 0x404, 0x104,
      0x84, 0x24, 0x14, 0xc, 0x202, 0x102, 0x42, 0x22, 0x12, 0xa, 0x6, 0x801,
      0x401, 0x201, 0x101, 0x81, 0x41, 0x21]
  | 11, 3 => [0xd00, 0xb00, 0xc80, 0xa40, 0x8c0, 0x520, 0x320, 0xa10, 0x890, 0x850, 0x250, 0xd0,
      0x488, 0xc8, 0x428, 0x98, 0x58, 0x504, 0x484, 0x424, 0x124, 0x94, 0x40c, 0x8c,
      0x2c, 0x1c, 0x302, 0x242, 0x222, 0x122, 0x212, 0x52, 0x4a, 0x2a, 0x1a, 0x106,
      0x26, 0x16, 0xe, 0xc01, 0xa01, 0x901, 0x501, 0x301, 0x881, 0x481, 0x841, 0x241,
      0xc1, 0x421, 0x221, 0x121]
  | 11, 4 => [0xa50, 0x8d0, 0xd8, 0x524, 0x48c, 0x42c, 0x9c, 0x322, 0x252, 0x5a, 0x126, 0x2e,
      0x1e, 0xd01, 0xb01, 0xc81, 0xa41, 0x8c1, 0x521, 0x321]
  | _, _ => []

private def candidateChunks (k : Fin 12) : List (List ProfileRow) :=
  match k.val with
  | 0 => [
      [⟨0xb00, 0x7e7dff4c240, 0xffa07ecbf84000, 0x7c1e20⟩, ⟨0x700, 0x7efcf7c4920, 0xffe576438f0200, 0x7f1210⟩,
       ⟨0xa80, 0x7c7fee2e608, 0xfd007ffe681420, 0x701fc0⟩, ⟨0x680, 0x7cfee6a6d04, 0xfd4477720e0690, 0x721292⟩,
       ⟨0x940, 0x7f79dd590c2, 0xffba6c81d0c808, 0x7c8828⟩, ⟨0x540, 0x7ff8d5d18a1, 0xffffe401858044, 0x7fe000⟩,
       ⟨0xa20, 0x7a77fb68648, 0xeea07b9ff05020, 0x6c1d60⟩, ⟨0x920, 0x7b75fb582c2, 0xeeb27a8bf0c808, 0x6c9c28⟩,
       ⟨0x320, 0x7af5fbc8360, 0xeee17a8bf34000, 0x6d1c20⟩, ⟨0x860, 0x7b73d9780da, 0xeeb26985d0f80a, 0x6c892c⟩],
      [⟨0x160, 0x7bf1d9d80e3, 0xeef3e881d1c80c, 0x6da828⟩, ⟨0x610, 0x76eeb786d24, 0xdbc556730f0690, 0x5b1292⟩,
       ⟨0x510, 0x77ecb7859a1, 0xdbcfd6430f0244, 0x5b7210⟩, ⟨0x310, 0x76edbf84b60, 0xdbc55e4b3f0200, 0x5b1610⟩,
       ⟨0x490, 0x75eea687d15, 0xd94cd6720e07d1, 0x525293⟩, ⟨0x290, 0x74efae86f0c, 0xd9445e7e2e06b0, 0x5216d2⟩,
       ⟨0x888, 0x6d5f683f61a, 0xb41839fc603d22, 0x200dc4⟩, ⟨0x848, 0x6f5b587b0da, 0xb63a29a4d0f90a, 0x24892c⟩,
       ⟨0x828, 0x6b5778786da, 0xa632399cf0f82a, 0x248d6c⟩, ⟨0x68, 0x6bd358780ff, 0xa633a984d0f80f, 0x24a92c⟩],
      [⟨0x484, 0x5dbe06b7d15, 0x715c87700e27d1, 0x124293⟩, ⟨0x444, 0x5fba05f38b5, 0x71ff852005a1c5, 0x13e001⟩,
       ⟨0x414, 0x57ae0787db5, 0x51cf86700f07d5, 0x136293⟩, ⟨0x94, 0x55af0687f1f, 0x514c867c0e07f3, 0x1242d3⟩,
       ⟨0x8c, 0x4d9f003ff1f, 0x301c81fc003ff3, 0x41c7⟩, ⟨0x4c, 0x4f9b007b8ff, 0x303f81a400f9cf, 0xe10d⟩,
       ⟨0x502, 0x3f80f7d59a1, 0xfff80038f8244, 0xfe010⟩, ⟨0x442, 0x3f80d5f38b5, 0xfff800185a1c5, 0xfe001⟩,
       ⟨0x142, 0x3f80ddd98e3, 0xfff8001d5c84c, 0xfe028⟩, ⟨0x122, 0x3b80fbd83e3, 0xef38003f3c80c, 0xda028⟩],
      [⟨0x62, 0x3b80d9f80ff, 0xef38001d1f80f, 0xda02c⟩, ⟨0x412, 0x3780b787db5, 0xbcf80030f07d5, 0xb6013⟩,
       ⟨0x112, 0x3780bf85be3, 0xbcf80033f024c, 0xb6010⟩, ⟨0x4a, 0x2f80587b8ff, 0x63f8000d0f9cf, 0x4e02d⟩,
       ⟨0x2a, 0x2b8078787ff, 0x6338000f0f83f, 0x4a02c⟩, ⟨0x406, 0x1f8007f7db5, 0x1ff80000fa7d5, 0x3e013⟩,
       ⟨0x46, 0x1f8005fb8ff, 0x1ff800005f9cf, 0x3e00d⟩, ⟨0x16, 0x17800787fff, 0x1cf80000f07ff, 0x36013⟩,
       ⟨0xe, 0xf80007ffff, 0x3f800000ffff, 0xe00f⟩, ⟨0xa01, 0x7fff6e648, 0x7ffff85420, 0x1fe0⟩],
      [⟨0x881, 0x7fee3f61a, 0x7ffe683d22, 0x1fc4⟩, ⟨0x281, 0x7feeaef0c, 0x7ffe6e16b0, 0x1fd2⟩,
       ⟨0x821, 0x77fb786da, 0x7b9ff0f82a, 0x1d6c⟩, ⟨0x221, 0x77fbe876c, 0x7b9ff35030, 0x1d60⟩,
       ⟨0x211, 0x6fbf86f6c, 0x5e7f3f06b0, 0x16d2⟩, ⟨0x91, 0x6fae87f1f, 0x5e7e2e07f3, 0x16d3⟩,
       ⟨0x809, 0x5f787f6da, 0x39fcf0fd2a, 0xdec⟩, ⟨0x89, 0x5f683ff1f, 0x39fc603ff3, 0xdc7⟩,
       ⟨0x29, 0x5778787ff, 0x399cf0f83f, 0xd6c⟩, ⟨0x85, 0x3f06bff1f, 0x7fc0e3ff3, 0x3d7⟩],
      [⟨0x15, 0x2f0787fff, 0x67c0f07ff, 0x2d3⟩, ⟨0xd, 0x1f007ffff, 0x1fc00ffff, 0x1cf⟩,
       ⟨0x23, 0xfbf87ff, 0x3f3f83f, 0x2c⟩, ⟨0x13, 0xbf87fff, 0x33f07ff, 0x13⟩,
       ⟨0xb, 0x787ffff, 0xf0ffff, 0x2f⟩, ⟨0x7, 0x7fffff, 0xfffff, 0x1f⟩,
       ⟨0xb20, 0x7a75fb48240, 0xeea07a8bf04000, 0x6c1c20⟩, ⟨0x960, 0x7b71d9580c2, 0xeeb26881d0c808, 0x6c8828⟩,
       ⟨0x710, 0x76ecb784920, 0xdbc556430f0200, 0x5b1210⟩, ⟨0x690, 0x74eea686d04, 0xd94456720e0690, 0x521292⟩],
      [⟨0x868, 0x6b5358780da, 0xa6322984d0f80a, 0x24892c⟩, ⟨0x494, 0x55ae0687d15, 0x514c86700e07d1, 0x124293⟩,
       ⟨0x542, 0x3f80d5d18a1, 0xfff8001858044, 0xfe000⟩, ⟨0x162, 0x3b80d9d80e3, 0xef38001d1c80c, 0xda028⟩,
       ⟨0x512, 0x3780b7859a1, 0xbcf80030f0244, 0xb6010⟩, ⟨0x6a, 0x2b8058780ff, 0x6338000d0f80f, 0x4a02c⟩,
       ⟨0x446, 0x1f8005f38b5, 0x1ff800005a1c5, 0x3e001⟩, ⟨0x416, 0x17800787db5, 0x1cf80000f07d5, 0x36013⟩,
       ⟨0x4e, 0xf80007b8ff, 0x3f800000f9cf, 0xe00d⟩, ⟨0xa81, 0x7fee2e608, 0x7ffe681420, 0x1fc0⟩],
      [⟨0xa21, 0x77fb68648, 0x7b9ff05020, 0x1d60⟩, ⟨0x291, 0x6fae86f0c, 0x5e7e2e06b0, 0x16d2⟩,
       ⟨0x889, 0x5f683f61a, 0x39fc603d22, 0xdc4⟩, ⟨0x829, 0x5778786da, 0x399cf0f82a, 0xd6c⟩,
       ⟨0x95, 0x2f0687f1f, 0x67c0e07f3, 0x2d3⟩, ⟨0x8d, 0x1f003ff1f, 0x1fc003ff3, 0x1c7⟩,
       ⟨0x2b, 0x78787ff, 0xf0f83f, 0x2c⟩, ⟨0x17, 0x787fff, 0xf07ff, 0x13⟩,
       ⟨0xf, 0x7ffff, 0xffff, 0xf⟩]
    ]
  | 1 => [
      [⟨0xc80, 0x7dfcd576c08, 0xfdbceb41086480, 0x3d4200⟩, ⟨0xa80, 0x7d7ec5fca04, 0xfcb86fd00cf840, 0x3c470a⟩,
       ⟨0x580, 0x7cfddc67502, 0xfd947b69904720, 0x3d0aa1⟩, ⟨0x380, 0x7c7fcced301, 0xfc907ffc845210, 0x3c0fc0⟩,
       ⟨0xc40, 0x7ff8f7520c8, 0xffffea034a0008, 0x3ff000⟩, ⟨0xa40, 0x7f7ae7d80a4, 0xfefa6e820f8804, 0x3e640c⟩,
       ⟨0x540, 0x7ef9fe43052, 0xffd57a23f00102, 0x3f8830⟩, ⟨0x340, 0x7e7beec9031, 0xfed07ea6a50001, 0x3e0c00⟩,
       ⟨0xa20, 0x7b76a7b8aa4, 0xeaea4d920fb844, 0x2a650e⟩, ⟨0x860, 0x7bf2b7980ec, 0xebebcc824f880c, 0x2af40c⟩],
      [⟨0x260, 0x7b73af980b5, 0xeaea5c862f8805, 0x2a640c⟩, ⟨0x510, 0x76edfa07552, 0xdf45706bf00722, 0x3388b1⟩,
       ⟨0x450, 0x77e9fb030da, 0xdf67f023f2010a, 0x33b830⟩, ⟨0x150, 0x76ebfa83073, 0xdf457427f10103, 0x338830⟩,
       ⟨0x70, 0x73e3bb800ff, 0xcb63d40673800f, 0x22b014⟩, ⟨0x508, 0x6edd7867552, 0xb7153369f04722, 0x158ab1⟩,
       ⟨0x488, 0x6ddd5877d0a, 0xb51cb3699067a0, 0x150aa1⟩, ⟨0x188, 0x6cdf586f703, 0xb51433fd905730, 0x150be1⟩,
       ⟨0x418, 0x67cd7807dda, 0x9707b069f007aa, 0x1198b1⟩, ⟨0x118, 0x66cf7807773, 0x9705307df00733, 0x1188f1⟩],
      [⟨0xa04, 0x5f3e07fcaa4, 0x70fa0fd00ff844, 0xc670e⟩, ⟨0x884, 0x5dbe05fee0c, 0x70bc8fd00cfcc0, 0xc470a⟩,
       ⟨0x284, 0x5d3f05fdb05, 0x70b80ffc0cfa50, 0xc47ca⟩, ⟨0x824, 0x5bb607b8eec, 0x60eb8d900fb8cc, 0x8750e⟩,
       ⟨0x224, 0x5b3707b8bb5, 0x60ea0d9c0fb855, 0x8654e⟩, ⟨0x8c, 0x4d9f007ff0f, 0x301c83fc007ff0, 0x403c3⟩,
       ⟨0xc02, 0x3f80f776cc8, 0xfff80034a6488, 0x3f000⟩, ⟨0x842, 0x3f80f7da0ec, 0xfff80034f880c, 0x3f00c⟩,
       ⟨0x442, 0x3f80ff530da, 0xfff8003fa010a, 0x3f030⟩, ⟨0x822, 0x3b80b7b8eec, 0xbeb80024fb8cc, 0x2f00e⟩],
      [⟨0x62, 0x3b80bf980ff, 0xbeb80027f880f, 0x2f01c⟩, ⟨0x412, 0x3780fb07dda, 0xf678003f207aa, 0x3b031⟩,
       ⟨0x52, 0x3780fb830ff, 0xf678003f3810f, 0x3b034⟩, ⟨0x32, 0x3380bb80fff, 0xb6380027380ff, 0x2b014⟩,
       ⟨0x40a, 0x2f807877dda, 0x71f8001f067aa, 0x19031⟩, ⟨0x1a, 0x27807807fff, 0x7078001f007ff, 0x19031⟩,
       ⟨0x806, 0x1f8007feeec, 0xff80000ffccc, 0x700e⟩, ⟨0x26, 0x1b8007b8fff, 0xeb80000fb8ff, 0x700e⟩,
       ⟨0xe, 0xf80007ffff, 0x1f8000007fff, 0x1003⟩, ⟨0x301, 0x7feeed331, 0x7ffea55211, 0xfc0⟩],
      [⟨0x281, 0x7fcdfdb05, 0x7ffc8cfa50, 0xfca⟩, ⟨0x181, 0x7fdcef703, 0x7ffd945730, 0xfe1⟩,
       ⟨0x221, 0x77afb8bb5, 0x5d9e2fb855, 0x54e⟩, ⟨0x111, 0x6ffa87773, 0x747ff10733, 0x8f1⟩,
       ⟨0x31, 0x67bb80fff, 0x541e7380ff, 0x54⟩, ⟨0x109, 0x5f786f773, 0x33fdf05733, 0xbf1⟩,
       ⟨0x89, 0x5f587ff0f, 0x33fd907ff0, 0xbe3⟩, ⟨0x19, 0x4f7807fff, 0x307df007ff, 0x8f1⟩,
       ⟨0x205, 0x3f07fdbb5, 0xffc0ffa55, 0x7ce⟩, ⟨0x85, 0x3f05fff0f, 0xffc0cfff0, 0x7cb⟩],
      [⟨0x25, 0x3707b8fff, 0xd9c0fb8ff, 0x54e⟩, ⟨0xd, 0x1f007ffff, 0x3fc007fff, 0x3c3⟩,
       ⟨0x23, 0xbfb8fff, 0x27fb8ff, 0x1e⟩, ⟨0x13, 0xfb87fff, 0x3f387ff, 0x35⟩,
       ⟨0xb, 0x787ffff, 0x1f07fff, 0x33⟩, ⟨0x7, 0x7fffff, 0xfffff, 0xf⟩,
       ⟨0xa60, 0x7b72a7980a4, 0xeaea4c820f8804, 0x2a640c⟩, ⟨0x550, 0x76e9fa03052, 0xdf457023f00102, 0x338830⟩,
       ⟨0x588, 0x6cdd5867502, 0xb5143369904720, 0x150aa1⟩, ⟨0x518, 0x66cd7807552, 0x97053069f00722, 0x1188b1⟩],
      [⟨0xa84, 0x5d3e05fca04, 0x70b80fd00cf840, 0xc470a⟩, ⟨0xa24, 0x5b3607b8aa4, 0x60ea0d900fb844, 0x8650e⟩,
       ⟨0xc42, 0x3f80f7520c8, 0xfff80034a0008, 0x3f000⟩, ⟨0x862, 0x3b80b7980ec, 0xbeb80024f880c, 0x2f00c⟩,
       ⟨0x452, 0x3780fb030da, 0xf678003f2010a, 0x3b030⟩, ⟨0x72, 0x3380bb800ff, 0xb63800273800f, 0x2b014⟩,
       ⟨0x41a, 0x27807807dda, 0x7078001f007aa, 0x19031⟩, ⟨0x826, 0x1b8007b8eec, 0xeb80000fb8cc, 0x700e⟩,
       ⟨0x381, 0x7fcced301, 0x7ffc845210, 0xfc0⟩, ⟨0x189, 0x5f586f703, 0x33fd905730, 0xbe1⟩],
      [⟨0x119, 0x4f7807773, 0x307df00733, 0x8f1⟩, ⟨0x285, 0x3f05fdb05, 0xffc0cfa50, 0x7ca⟩,
       ⟨0x225, 0x3707b8bb5, 0xd9c0fb855, 0x54e⟩, ⟨0x8d, 0x1f007ff0f, 0x3fc007ff0, 0x3c3⟩,
       ⟨0x33, 0xbb80fff, 0x27380ff, 0x14⟩, ⟨0x1b, 0x7807fff, 0x1f007ff, 0x31⟩,
       ⟨0x27, 0x7b8fff, 0xfb8ff, 0xe⟩, ⟨0xf, 0x7ffff, 0x7fff, 0x3⟩]
    ]
  | 2 => [
      [⟨0xc80, 0xf8f5fe9ba08, 0xe7903e61ffa82a0, 0x63070f8⟩, ⟨0x580, 0xf9f1eecea82, 0xe7b23a01db3d188, 0x63840d3⟩,
       ⟨0xc40, 0xf4fdddb9848, 0xf6403fe976e0a20, 0x7007ca8⟩, ⟨0xa40, 0xf6ffd531464, 0xfe493fff2440812, 0x7c07f00⟩,
       ⟨0x520, 0xede9afec292, 0xd5e2b381d17f508, 0x52c48c7⟩, ⟨0x320, 0xefeba7641b1, 0xdde7f3858056405, 0x56dc804⟩,
       ⟨0x460, 0xe5ed9dfc05a, 0xd460b7c970f3f00, 0x5046ca6⟩, ⟨0x260, 0xe7ef9574075, 0xdc61f7cf2052c03, 0x544ed04⟩,
       ⟨0xa10, 0xfedf7303564, 0xffdd2d3e8c00052, 0x7f21300⟩, ⟨0x310, 0xffdb63425b1, 0xffffe9148806045, 0x7ff8000⟩],
      [⟨0x890, 0xfad77a83f0c, 0xef9c2c32cf880f0, 0x6b21258⟩, ⟨0x190, 0xfbd36ac2f83, 0xefbe6810cb0d0cc, 0x6bb0051⟩,
       ⟨0xa08, 0xdebef033564, 0xbb1d1cfe2c00852, 0x2d23700⟩, ⟨0x888, 0xdab6f81bf0c, 0xab1c1c723f802f0, 0x2923238⟩,
       ⟨0x848, 0xd6bed839c6c, 0xba091cfe3680a32, 0x2c03728⟩, ⟨0x248, 0xd7bed035475, 0xba09dcfe2400c13, 0x2c0b700⟩,
       ⟨0x818, 0xde9e7803f6c, 0xbb1d0c3e0f800f2, 0x2d21318⟩, ⟨0x218, 0xdf9e70035f5, 0xbb1fcc3e0c00057, 0x2d39300⟩,
       ⟨0x98, 0xdb967803f8f, 0xab1e4c320f800fc, 0x2931218⟩, ⟨0x304, 0xbf7a07665b1, 0x78ffc3940056445, 0x1cf8804⟩],
      [⟨0x244, 0xb77e0575475, 0x7869c3fe0052c13, 0x1c48f04⟩, ⟨0x224, 0xaf6e07741f5, 0x58e7c3ce0056c07, 0x14d8d04⟩,
       ⟨0x124, 0xaf6a07ec3b3, 0x58e7c384007f50d, 0x14d8807⟩, ⟨0x64, 0xa76e05fc07f, 0x5861c3ce0073f03, 0x1448d06⟩,
       ⟨0x214, 0xbf5e03435f5, 0x78ffc13e0006057, 0x1cf8300⟩, ⟨0x114, 0xbf5a03c2fb3, 0x78ffc114000f0cd, 0x1cf8001⟩,
       ⟨0x20c, 0x9f3e00375f5, 0x381fc0fe0000c57, 0xc38700⟩, ⟨0x4c, 0x973e003dc7f, 0x3809c0fe0000f33, 0xc08700⟩,
       ⟨0x1c, 0x9f1e0003fff, 0x381fc03e00000ff, 0xc38300⟩, ⟨0x502, 0x7d01efeea92, 0x7f28001db7f588, 0x3c00d7⟩],
      [⟨0x482, 0x7901fedfa8a, 0x7b20001ffbd3a8, 0x3800fb⟩, ⟨0x182, 0x7b01eecef83, 0x7be4001db3d1cc, 0x3b00d3⟩,
       ⟨0x422, 0x6d01bffc2da, 0x5e28001f1fff08, 0x2c00e7⟩, ⟨0x122, 0x6f01afec3b3, 0x5e7c001d17f50d, 0x2d80c7⟩,
       ⟨0x112, 0x7f016bc2fb3, 0x7ffc000cb0f0cd, 0x3f8051⟩, ⟨0x92, 0x7b017ac3f8f, 0x7be4000cf8d0fc, 0x3b0059⟩,
       ⟨0x8a, 0x5b00f81ff8f, 0x31e40003f803fc, 0x130038⟩, ⟨0x1a, 0x5f007803fff, 0x31fc0000f800ff, 0x138018⟩,
       ⟨0x106, 0x3f0007eefb3, 0xffc000007f5cd, 0xf8007⟩, ⟨0x26, 0x2f0007fc3ff, 0xe7c000007ff0f, 0xd8007⟩],
      [⟨0x16, 0x3f0003c3fff, 0xffc000000f0ff, 0xf8001⟩, ⟨0xe, 0x1f00003ffff, 0x1fc0000000fff, 0x38000⟩,
       ⟨0xc01, 0xfdffbba48, 0x3fe9ffe8aa0, 0x7cf8⟩, ⟨0x881, 0xf7fe9bf0c, 0x3e73ffa82f0, 0x72f8⟩,
       ⟨0x481, 0xf5fedfa8a, 0x3e61ffbd3a8, 0x70fb⟩, ⟨0x841, 0xffddb9c6c, 0x3fff76e0a32, 0x7fa8⟩,
       ⟨0x441, 0xfdddfd85a, 0x3fe976f3f20, 0x7cae⟩, ⟨0x421, 0xedbffc2da, 0x37c9f1fff08, 0x6ce7⟩,
       ⟨0x61, 0xef9dfc07f, 0x37cf70f3f03, 0x6da6⟩, ⟨0x809, 0xbef83bf6c, 0x1cfe3f80af2, 0x3738⟩],
      [⟨0x89, 0xb6f81ff8f, 0x1c723f803fc, 0x3238⟩, ⟨0x49, 0xbed83dc7f, 0x1cfe3680f33, 0x3728⟩,
       ⟨0x45, 0x7e05fdc7f, 0x3fe0073f33, 0xf06⟩, ⟨0x25, 0x6e07fc3ff, 0x3ce007ff0f, 0xd07⟩,
       ⟨0xd, 0x3e003ffff, 0xfe0000fff, 0x700⟩, ⟨0x403, 0x1ffffada, 0x1fffffa8, 0xff⟩,
       ⟨0x83, 0x1fedff8f, 0x1ffbd3fc, 0xfb⟩, ⟨0x23, 0x1bffc3ff, 0x1f1fff0f, 0xe7⟩,
       ⟨0xb, 0xf83ffff, 0x3f80fff, 0x38⟩, ⟨0x7, 0x7fffff, 0x7ffff, 0x7⟩],
      [⟨0xa48, 0xd6bed031464, 0xba091cfe2400812, 0x2c03700⟩, ⟨0xa18, 0xde9e7003564, 0xbb1d0c3e0c00052, 0x2d21300⟩,
       ⟨0x898, 0xda967803f0c, 0xab1c0c320f800f0, 0x2921218⟩, ⟨0x324, 0xaf6a07641b1, 0x58e7c3840056405, 0x14d8804⟩,
       ⟨0x264, 0xa76e0574075, 0x5861c3ce0052c03, 0x1448d04⟩, ⟨0x314, 0xbf5a03425b1, 0x78ffc1140006045, 0x1cf8000⟩,
       ⟨0x24c, 0x973e0035475, 0x3809c0fe0000c13, 0xc08700⟩, ⟨0x21c, 0x9f1e00035f5, 0x381fc03e0000057, 0xc38300⟩,
       ⟨0x582, 0x7901eecea82, 0x7b20001db3d188, 0x3800d3⟩, ⟨0x522, 0x6d01afec292, 0x5e28001d17f508, 0x2c00c7⟩],
      [⟨0x192, 0x7b016ac2f83, 0x7be4000cb0d0cc, 0x3b0051⟩, ⟨0x9a, 0x5b007803f8f, 0x31e40000f800fc, 0x130018⟩,
       ⟨0x126, 0x2f0007ec3b3, 0xe7c000007f50d, 0xd8007⟩, ⟨0x116, 0x3f0003c2fb3, 0xffc000000f0cd, 0xf8001⟩,
       ⟨0x1e, 0x1f000003fff, 0x1fc00000000ff, 0x38000⟩, ⟨0xc81, 0xf5fe9ba08, 0x3e61ffa82a0, 0x70f8⟩,
       ⟨0xc41, 0xfdddb9848, 0x3fe976e0a20, 0x7ca8⟩, ⟨0x461, 0xed9dfc05a, 0x37c970f3f00, 0x6ca6⟩,
       ⟨0x889, 0xb6f81bf0c, 0x1c723f802f0, 0x3238⟩, ⟨0x849, 0xbed839c6c, 0x1cfe3680a32, 0x3728⟩],
      [⟨0x65, 0x6e05fc07f, 0x3ce0073f03, 0xd06⟩, ⟨0x4d, 0x3e003dc7f, 0xfe0000f33, 0x700⟩,
       ⟨0x483, 0x1fedfa8a, 0x1ffbd3a8, 0xfb⟩, ⟨0x423, 0x1bffc2da, 0x1f1fff08, 0xe7⟩,
       ⟨0x8b, 0xf81ff8f, 0x3f803fc, 0x38⟩, ⟨0x27, 0x7fc3ff, 0x7ff0f, 0x7⟩,
       ⟨0xf, 0x3ffff, 0xfff, 0x0⟩]
    ]
  | 3 => [
      [⟨0xe00, 0xfefde79a480, 0xff7d3f69a0c4000, 0x3f33800⟩, ⟨0xd00, 0xfcf9d7dd600, 0xf67c3741d8f6600, 0x2d3286c⟩,
       ⟨0xc80, 0xfaf5f75f200, 0xef683e61f8f2600, 0x392386c⟩, ⟨0x980, 0xf9f1df5d304, 0xe6ea3641ddf2620, 0x29a287c⟩,
       ⟨0x580, 0xf8f3d77da02, 0xe66836d1d8fae80, 0x2922c6e⟩, ⟨0x640, 0xf6ffa6b28a8, 0xfd513fff2089108, 0x3e03f80⟩,
       ⟨0x4c0, 0xf2f7b67780a, 0xed403ef370b8d80, 0x3803d4a⟩, ⟨0xa20, 0xffed6d885d0, 0xffffed088644050, 0x3ffc000⟩,
       ⟨0x920, 0xfde95dcc744, 0xf6fea500cd66260, 0x2db8034⟩, ⟨0x250, 0xe7deaaa28f9, 0xd991dbbe220911e, 0x1645781⟩],
      [⟨0x230, 0xefce69a05f9, 0xdbb7c98e060505e, 0x16dc281⟩, ⟨0xa08, 0xdfbde81a5d0, 0xbf8ff869a600050, 0x33cf000⟩,
       ⟨0x888, 0xdbb5f81f314, 0xaf8a7861ff00620, 0x31c3070⟩, ⟨0x248, 0xd7bfa8128f9, 0xbd81f87f220011e, 0x3247181⟩,
       ⟨0xc8, 0xd3b7b81781f, 0xad8078737300583, 0x3043140⟩, ⟨0x828, 0xdfad780c7d4, 0xbf8fe808cf00270, 0x33cc030⟩,
       ⟨0x228, 0xdfaf68085f9, 0xbf8fe80e860005e, 0x33cc081⟩, ⟨0x218, 0xcf9ee802df9, 0x9b87d83e260015e, 0x12cd181⟩,
       ⟨0x58, 0xc79eb8038ff, 0x9981d83e330019f, 0x1245181⟩, ⟨0x38, 0xcf8e78007ff, 0x9b87c80e0f0007f, 0x12cc091⟩],
      [⟨0x604, 0xbe7e07baca8, 0x787d07fe00cd108, 0xe30f80⟩, ⟨0x504, 0xbc7a07fde22, 0x707c07d400ffe80, 0xc30e0e⟩,
       ⟨0x444, 0xb67e06f78aa, 0x785107fe00b9d88, 0xe00f8a⟩, ⟨0x244, 0xb77e06b28f9, 0x7851c7fe008911e, 0xe04f81⟩,
       ⟨0x224, 0xbf6e05a85f9, 0x787fc58e004505e, 0xe3c281⟩, ⟨0x124, 0xbd6a05ec767, 0x707e85840067a65, 0xc38204⟩,
       ⟨0x214, 0xaf5e03a2df9, 0x5837c3be000d15e, 0x61c781⟩, ⟨0x54, 0xa75e02e38ff, 0x5811c3be001999f, 0x604783⟩,
       ⟨0x34, 0xaf4e01e07ff, 0x5837c18e000787f, 0x61c281⟩, ⟨0x902, 0x7d01dfdd744, 0x6fe8001ddf6660, 0x1b807c⟩],
      [⟨0x882, 0x7b01ff5f314, 0x7ea4001fff2620, 0x1e007c⟩, ⟨0x182, 0x7901df7db07, 0x6ea0001ddfaea1, 0x1a007e⟩,
       ⟨0x822, 0x7f017dcc7d4, 0x7ffc000cf66270, 0x1fc034⟩, ⟨0x122, 0x7d015dec767, 0x6fe8000cd67a65, 0x1b8034⟩,
       ⟨0x32, 0x6f0079e07ff, 0x3b7c0000f0787f, 0xdc011⟩, ⟨0x80a, 0x5f01f81f7d4, 0x78fc001ff00670, 0x1cc070⟩,
       ⟨0x8a, 0x5b01f81fb1f, 0x78a4001ff007a3, 0x1c0070⟩, ⟨0x2a, 0x5f01780c7ff, 0x78fc000cf0027f, 0x1cc031⟩,
       ⟨0x1a, 0x4f00f803fff, 0x387c0003f001ff, 0xcc011⟩, ⟨0x106, 0x3d0007fdf67, 0x7e800000ffee5, 0x3800e⟩],
      [⟨0x26, 0x3f0005ec7ff, 0x7fc0000067a7f, 0x3c005⟩, ⟨0x16, 0x2f0003e3fff, 0x37c000001f9ff, 0x1c003⟩,
       ⟨0x501, 0xfbd7fde22, 0x37d5d8ffe80, 0x2e6e⟩, ⟨0x481, 0xf7f77fa0a, 0x3ef3f8faf80, 0x3d6e⟩,
       ⟨0x181, 0xf3df7db07, 0x36d1ddfaea1, 0x2c7e⟩, ⟨0x441, 0xffb6f78aa, 0x3fff70b9d88, 0x3fca⟩,
       ⟨0xc1, 0xf7be7781f, 0x3ef373b8d83, 0x3d4a⟩, ⟨0x51, 0xdebae38ff, 0x1bbe331999f, 0x1783⟩,
       ⟨0x89, 0xb7f81fb1f, 0x3873ff007a3, 0x3170⟩, ⟨0x49, 0xbfb8178ff, 0x387f730059f, 0x31c1⟩],
      [⟨0x19, 0x9ef803fff, 0x183e3f001ff, 0x1191⟩, ⟨0x405, 0x7e07ffeaa, 0x7fe00fff88, 0xf8e⟩,
       ⟨0x105, 0x7a07fdf67, 0x7d400ffee5, 0xe0e⟩, ⟨0x45, 0x7e06f78ff, 0x7fe00b9d9f, 0xf8b⟩,
       ⟨0x15, 0x5e03e3fff, 0x3be001f9ff, 0x783⟩, ⟨0x103, 0x1dffdf67, 0x1ddffee5, 0x7e⟩,
       ⟨0x83, 0x1ff7fb1f, 0x1fffafa3, 0x7e⟩, ⟨0x13, 0xfbe3fff, 0x3f1f9ff, 0x13⟩,
       ⟨0xb, 0x1f81ffff, 0x1ff007ff, 0x71⟩, ⟨0x7, 0x7fffff, 0xfffff, 0xf⟩],
      [⟨0xd80, 0xf8f1d75d200, 0xe6683641d8f2600, 0x292286c⟩, ⟨0xa28, 0xdfad68085d0, 0xbf8fe8088600050, 0x33cc000⟩,
       ⟨0x258, 0xc79ea8028f9, 0x9981d83e220011e, 0x1245181⟩, ⟨0x238, 0xcf8e68005f9, 0x9b87c80e060005e, 0x12cc081⟩,
       ⟨0x644, 0xb67e06b28a8, 0x785107fe0089108, 0xe00f80⟩, ⟨0x254, 0xa75e02a28f9, 0x5811c3be000911e, 0x604781⟩,
       ⟨0x234, 0xaf4e01a05f9, 0x5837c18e000505e, 0x61c281⟩, ⟨0x982, 0x7901df5d304, 0x6ea0001ddf2620, 0x1a007c⟩,
       ⟨0x922, 0x7d015dcc744, 0x6fe8000cd66260, 0x1b8034⟩, ⟨0x88a, 0x5b01f81f314, 0x78a4001ff00620, 0x1c0070⟩],
      [⟨0x82a, 0x5f01780c7d4, 0x78fc000cf00270, 0x1cc030⟩, ⟨0x3a, 0x4f0078007ff, 0x387c0000f0007f, 0xcc011⟩,
       ⟨0x126, 0x3d0005ec767, 0x7e80000067a65, 0x38004⟩, ⟨0x36, 0x2f0001e07ff, 0x37c000000787f, 0x1c001⟩,
       ⟨0x581, 0xf3d77da02, 0x36d1d8fae80, 0x2c6e⟩, ⟨0x4c1, 0xf7b67780a, 0x3ef370b8d80, 0x3d4a⟩,
       ⟨0xc9, 0xb7b81781f, 0x38737300583, 0x3140⟩, ⟨0x59, 0x9eb8038ff, 0x183e330019f, 0x1181⟩,
       ⟨0x505, 0x7a07fde22, 0x7d400ffe80, 0xe0e⟩, ⟨0x445, 0x7e06f78aa, 0x7fe00b9d88, 0xf8a⟩],
      [⟨0x55, 0x5e02e38ff, 0x3be001999f, 0x783⟩, ⟨0x183, 0x1df7db07, 0x1ddfaea1, 0x7e⟩,
       ⟨0x8b, 0x1f81fb1f, 0x1ff007a3, 0x70⟩, ⟨0x1b, 0xf803fff, 0x3f001ff, 0x11⟩,
       ⟨0x107, 0x7fdf67, 0xffee5, 0xe⟩, ⟨0x17, 0x3e3fff, 0x1f9ff, 0x3⟩]
    ]
  | 4 => [
      [⟨0x380, 0x1e7cfce33b21, 0xb9b4e9a72d29432c, 0x2a353151⟩, ⟨0x340, 0x1d7af8f3b305, 0x7d31cd8f290d4b64, 0x1a947115⟩,
       ⟨0xc20, 0x1b9f375cc0da, 0xc60a7652d0d63483, 0x10a8a2a⟩, ⟨0x460, 0x19bb735ed01e, 0x5703569ad0173cc1, 0x1188ca0e⟩,
       ⟨0x260, 0x197bf2daf015, 0x7501df9e980728e0, 0x188ce80c⟩, ⟨0xc10, 0x1f972f3c0cda, 0xceca3051c6d0b413, 0x54206a2⟩,
       ⟨0x890, 0x1ed5afac0ee2, 0xaaec3861c7f0841a, 0x246306e0⟩, ⟨0x190, 0x1ef4eda60f61, 0xbbfca8254760c01c, 0x2e7104c0⟩,
       ⟨0x830, 0x1bd7a79c00fa, 0xe60e3870c0f03403, 0x21030222⟩, ⟨0x430, 0x1bb7671e00de, 0xd70b3058c0d03c03, 0x11820222⟩],
      [⟨0x308, 0x177edc81bb25, 0xf0b5edac2d20036c, 0x38356141⟩, ⟨0x888, 0x16dd9f816ee2, 0xa0ec7b603ff0021a, 0x206f01e0⟩,
       ⟨0x288, 0x167dde817ba1, 0xb0b4fbe43da0032c, 0x283f2141⟩, ⟨0x188, 0x16fcdd813f61, 0xb0fce9a42f60033c, 0x287521c1⟩,
       ⟨0x828, 0x13df9780e0fa, 0xe00e7f7018f00083, 0x200f8020⟩, ⟨0x228, 0x137fd680f0b5, 0xf005fffc18a000e0, 0x380fe000⟩,
       ⟨0x818, 0x17d78f800efa, 0xe0ee387007f0001b, 0x206300e0⟩, ⟨0x118, 0x17f6cd800f6d, 0xf0ffa82c0760001c, 0x387100c0⟩,
       ⟨0x98, 0x16f5cf800fe3, 0xb0fcb86407f0001e, 0x287300e0⟩, ⟨0x38, 0x13f7c78000ff, 0xf00fb87c00f00003, 0x38030020⟩],
      [⟨0x304, 0x1f6ec073bb25, 0xfdb585ac000d4b6c, 0x3ab06015⟩, ⟨0x444, 0x1dab407fd51e, 0x5f530698000ffdc1, 0x1780c01e⟩,
       ⟨0x244, 0x1d6bc07bf315, 0x7d31879c000f6be4, 0x1a90e01d⟩, ⟨0x144, 0x1deac077b70d, 0x7f73858c000ddb64, 0x1f906015⟩,
       ⟨0x424, 0x1baf405ed0de, 0xd70b06d800073cc3, 0x1180c00e⟩, ⟨0x224, 0x1b6fc05af0b5, 0xf50587fc000728e0, 0x3880e00c⟩,
       ⟨0x64, 0x19ebc05ef01f, 0x7703879c00073ce1, 0x1980e00e⟩, ⟨0x414, 0x1fa7403e0dde, 0xdfdb00580000fc13, 0x17c00002⟩,
       ⟨0x114, 0x1fe6c0360f6d, 0xffff802c0000d81c, 0x3ff00000⟩, ⟨0x34, 0x1be7c01e00ff, 0xf70f807c00003c03, 0x39800002⟩],
      [⟨0x20c, 0x176fc001fbb5, 0xf0b587fc000003ec, 0x3830e001⟩, ⟨0x10c, 0x17eec001bf6d, 0xf0ff85ac0000037c, 0x38706001⟩,
       ⟨0x2c, 0x13efc000f0ff, 0xf00f87fc000000e3, 0x3800e000⟩, ⟨0x1c, 0x17e7c0000fff, 0xf0ff807c0000001f, 0x38700000⟩,
       ⟨0xc02, 0xf803f7dccda, 0xeca0003f6deb493, 0x5401eaa⟩, ⟨0x882, 0xec03fed6ee2, 0xaec0003fffa861a, 0x4601fe0⟩,
       ⟨0x182, 0xee03de73f61, 0xbfc80036f69c33c, 0x67015d1⟩, ⟨0x442, 0xda03b7fd51e, 0xf530003f21ffdc1, 0x7801e1e⟩,
       ⟨0x142, 0xde039f7b70d, 0xf7380036b0ddb64, 0x7901515⟩, ⟨0x812, 0xfc02fbc0efa, 0xeee0001c7f0b41b, 0x56006e2⟩],
      [⟨0x412, 0xfa02f3e0dde, 0xfdb0001c6d0fc13, 0x7c006a2⟩, ⟨0x112, 0xfe02db60f6d, 0xfff80014760d81c, 0x7f004c0⟩,
       ⟨0x92, 0xee02fae0fe3, 0xbfc8001c7f0c41e, 0x67006e0⟩, ⟨0x406, 0xfa0007fddde, 0xfdb0000000ffdd3, 0x7c0001e⟩,
       ⟨0x106, 0xfe00077bf6d, 0xfff8000000ddb7c, 0x7f00015⟩, ⟨0x46, 0xde0007ff71f, 0xf738000000fffe5, 0x790001f⟩,
       ⟨0x16, 0xfe0003e0fff, 0xfff80000000fc1f, 0x7f00002⟩, ⟨0xc01, 0x1f3f7dccda, 0x7653f6deb493, 0xa9eaa⟩,
       ⟨0x881, 0x1dbfed6ee2, 0x7b63fffa861a, 0xf1fe0⟩, ⟨0x281, 0x1dfeeb7ba1, 0x7be7bdab432c, 0xf3951⟩],
      [⟨0x441, 0x1b7b7fd51e, 0x569bf21ffdc1, 0x8de1e⟩, ⟨0x241, 0x1bfafbf315, 0x5f9fb90f6be4, 0xcf91d⟩,
       ⟨0x821, 0x1fb7dce0fa, 0x7f72d8f63483, 0xf8a2a⟩, ⟨0x421, 0x1f775ed0de, 0x76dad0d73cc3, 0xaca2e⟩,
       ⟨0x221, 0x1ff6daf0b5, 0x7ffe98a728e0, 0xfe80c⟩, ⟨0x61, 0x1bf3def01f, 0x5f9ed8173ce1, 0xcea0e⟩,
       ⟨0x809, 0x1f9f81eefa, 0x7f703ff0029b, 0xf81e0⟩, ⟨0x209, 0x1fde81fbb5, 0x7ffc3da003ec, 0xfe141⟩,
       ⟨0x89, 0x1ddf817fe3, 0x7be43ff0033e, 0xf21e1⟩, ⟨0x29, 0x1fd780f0ff, 0x7ffc18f000e3, 0xfe020⟩],
      [⟨0x803, 0x3ffdeefa, 0x3fffeb69b, 0x1fea⟩, ⟨0x403, 0x3f7fddde, 0x3f6dffdd3, 0x1ebe⟩,
       ⟨0x83, 0x3fef7fe3, 0x3fffbc73e, 0x1ff1⟩, ⟨0x43, 0x3bfff71f, 0x3fb1fffe5, 0x1f1f⟩,
       ⟨0xc30, 0x1b97271c00da, 0xc60a3050c0d03403, 0x1020222⟩, ⟨0x388, 0x167cdc813b21, 0xb0b4e9a42d20032c, 0x28352141⟩,
       ⟨0x898, 0x16d58f800ee2, 0xa0ec386007f0001a, 0x206300e0⟩, ⟨0x198, 0x16f4cd800f61, 0xb0fca8240760001c, 0x287100c0⟩,
       ⟨0x838, 0x13d7878000fa, 0xe00e387000f00003, 0x20030020⟩, ⟨0x344, 0x1d6ac073b305, 0x7d31858c000d4b64, 0x1a906015⟩],
      [⟨0x464, 0x19ab405ed01e, 0x5703069800073cc1, 0x1180c00e⟩, ⟨0x264, 0x196bc05af015, 0x7501879c000728e0, 0x1880e00c⟩,
       ⟨0x434, 0x1ba7401e00de, 0xd70b005800003c03, 0x11800002⟩, ⟨0x30c, 0x176ec001bb25, 0xf0b585ac0000036c, 0x38306001⟩,
       ⟨0x22c, 0x136fc000f0b5, 0xf00587fc000000e0, 0x3800e000⟩, ⟨0x11c, 0x17e6c0000f6d, 0xf0ff802c0000001c, 0x38700000⟩,
       ⟨0x3c, 0x13e7c00000ff, 0xf00f807c00000003, 0x38000000⟩, ⟨0xc12, 0xf802f3c0cda, 0xeca0001c6d0b413, 0x54006a2⟩,
       ⟨0x892, 0xec02fac0ee2, 0xaec0001c7f0841a, 0x46006e0⟩, ⟨0x192, 0xee02da60f61, 0xbfc80014760c01c, 0x67004c0⟩],
      [⟨0x446, 0xda0007fd51e, 0xf530000000ffdc1, 0x780001e⟩, ⟨0x146, 0xde00077b70d, 0xf738000000ddb64, 0x7900015⟩,
       ⟨0x416, 0xfa0003e0dde, 0xfdb00000000fc13, 0x7c00002⟩, ⟨0x116, 0xfe000360f6d, 0xfff80000000d81c, 0x7f00000⟩,
       ⟨0xc21, 0x1f375cc0da, 0x7652d0d63483, 0xa8a2a⟩, ⟨0x461, 0x1b735ed01e, 0x569ad0173cc1, 0x8ca0e⟩,
       ⟨0x261, 0x1bf2daf015, 0x5f9e980728e0, 0xce80c⟩, ⟨0x889, 0x1d9f816ee2, 0x7b603ff0021a, 0xf01e0⟩,
       ⟨0x289, 0x1dde817ba1, 0x7be43da0032c, 0xf2141⟩, ⟨0x829, 0x1f9780e0fa, 0x7f7018f00083, 0xf8020⟩],
      [⟨0x229, 0x1fd680f0b5, 0x7ffc18a000e0, 0xfe000⟩, ⟨0xc03, 0x3f7dccda, 0x3f6deb493, 0x1eaa⟩,
       ⟨0x883, 0x3fed6ee2, 0x3fffa861a, 0x1fe0⟩, ⟨0x443, 0x3b7fd51e, 0x3f21ffdc1, 0x1e1e⟩]
    ]
  | 5 => [
      [⟨0xe00, 0xfcfcfbcf400, 0xfe707bb83e3a200, 0x3e0e628⟩, ⟨0xd00, 0xfafef3ad880, 0xed5c7bfd3434100, 0x2d2e780⟩,
       ⟨0xc80, 0xf6faebeec00, 0xdf6873f43a3e200, 0x370c728⟩, ⟨0xa80, 0xf4f9efce610, 0xde6077b23b7a280, 0x360d638⟩,
       ⟨0x680, 0xf5f8ebde508, 0xdee173b03a3ba40, 0x368c62c⟩, ⟨0xc40, 0xfef6db6b880, 0xff7c6b6d2c2c100, 0x3f2a580⟩,
       ⟨0x940, 0xfaf7d7298c4, 0xed5c6f6de4a4110, 0x2d2adc0⟩, ⟨0x540, 0xfbf6d3398a2, 0xeddeeb6d2424508, 0x2d7a580⟩,
       ⟨0x2a0, 0xe5e9aed6719, 0x9aa156921b5bae2, 0x128523e⟩, ⟨0x150, 0xdbd755318e7, 0x659ead4dc48451d, 0x9729c1⟩],
      [⟨0xa08, 0xbcbdfc0f650, 0xf0707c3abfc0280, 0x380f830⟩, ⟨0x908, 0xbabff40dac4, 0xe05c7c3ff580110, 0x282f8c0⟩,
       ⟨0x848, 0xbeb7dc0b8d4, 0xf07c6c2decc0110, 0x382a8c0⟩, ⟨0x148, 0xbbb7d4098e7, 0xe05eec2de48011d, 0x283a8c1⟩,
       ⟨0x228, 0xadadbc06779, 0xb0235c129bc02e6, 0x1005832⟩, ⟨0x118, 0x9b9f7401be7, 0x601ebc0fc58013d, 0x8338c1⟩,
       ⟨0x58, 0x9f975c018ff, 0x701fac0dc4c011f, 0x8328c1⟩, ⟨0x38, 0x8f8f3c007ff, 0x30079c03c3c00ff, 0x11853⟩,
       ⟨0x504, 0x7b7e03bd9a2, 0xdde83fd0035508, 0x570780⟩, ⟨0x484, 0x777a03fed0a, 0xfe983f4003fe40, 0x7c070c⟩],
      [⟨0x444, 0x7f76037b8aa, 0xfff836d002cd08, 0x7f0580⟩, ⟨0x144, 0x7b7703398e7, 0xdde836dc02451d, 0x5705c1⟩,
       ⟨0xa4, 0x676b02f671f, 0xba182d2401bee3, 0x2c020e⟩, ⟨0x114, 0x5b5f01b1be7, 0x59e81cfc00553d, 0x1701c1⟩,
       ⟨0x54, 0x5f5701718ff, 0x79f814dc004d1f, 0x1f01c1⟩, ⟨0x34, 0x4f4f00f07ff, 0x38780c3c003cff, 0xd0047⟩,
       ⟨0x602, 0xfd00fbdf528, 0xfef300003e3ba40, 0x3e8002c⟩, ⟨0x482, 0xf700ebfed0a, 0xdfe980003a3fe40, 0x37c002c⟩,
       ⟨0x282, 0xf500efde719, 0xdee100003b7bae2, 0x368003e⟩, ⟨0x442, 0xff00db7b8aa, 0xffff80002c2cd08, 0x3ff0000⟩],
      [⟨0x222, 0xed00bed6779, 0xbaa300001bdbae6, 0x128003e⟩, ⟨0xa2, 0xe700aef671f, 0x9ba180001b5bee3, 0x12c003e⟩,
       ⟨0x52, 0xdf005d718ff, 0x779f800004c4d1f, 0x9f0001⟩, ⟨0x32, 0xcf003cf07ff, 0x3387800003c3cff, 0xd0017⟩,
       ⟨0x20a, 0xbd00fc0f779, 0xf07300003fc02e6, 0x3800032⟩, ⟨0x4a, 0xbf00dc0b8ff, 0xf07f80002cc011f, 0x3830001⟩,
       ⟨0x2a, 0xaf00bc067ff, 0xb02780001bc02ff, 0x1010033⟩, ⟨0x1a, 0x9f007c01fff, 0x701f800007c01ff, 0x830013⟩,
       ⟨0x406, 0x7f0003ffdaa, 0xfff8000003ff48, 0x7f000c⟩, ⟨0x86, 0x770003fef1f, 0xfe98000003fee3, 0x7c000e⟩],
      [⟨0x46, 0x7f00037b8ff, 0xfff8000002cd1f, 0x7f0001⟩, ⟨0x26, 0x6f0002f67ff, 0xba78000001beff, 0x2d000f⟩,
       ⟨0x16, 0x5f0001f1fff, 0x79f80000007dff, 0x1f0007⟩, ⟨0xa01, 0xfdffcf650, 0x7fbabffa280, 0xfe38⟩,
       ⟨0x901, 0xfff7adac4, 0x7ffff5b4110, 0xffc0⟩, ⟨0x881, 0xfbefeee14, 0x77f67b7e280, 0xd738⟩,
       ⟨0x281, 0xf9efde719, 0x77b23b7bae2, 0xd63e⟩, ⟨0x221, 0xedbed6779, 0x5e929bdbae6, 0x5a3e⟩,
       ⟨0xa1, 0xebaef671f, 0x56d25b5bee3, 0x523e⟩, ⟨0x111, 0xdf75b1be7, 0x3dcfc58553d, 0x39c1⟩],
      [⟨0x31, 0xcf3cf07ff, 0x1cc3c3c3cff, 0x1857⟩, ⟨0x809, 0xbffc0fed4, 0x7c3fffc0390, 0xf8f0⟩,
       ⟨0x209, 0xbdfc0f779, 0x7c3abfc02e6, 0xf832⟩, ⟨0x109, 0xbff40dbe7, 0x7c3ff58013d, 0xf8c1⟩,
       ⟨0x29, 0xafbc067ff, 0x5c13dbc02ff, 0x5873⟩, ⟨0x19, 0x9f7c01fff, 0x3c0fc7c01ff, 0x38d3⟩,
       ⟨0x105, 0x7f03bdbe7, 0x3ffc03553d, 0x7c1⟩, ⟨0x85, 0x7b03fef1f, 0x3f6403fee3, 0x70e⟩,
       ⟨0x25, 0x6f02f67ff, 0x2d3c01beff, 0x24f⟩, ⟨0x15, 0x5f01f1fff, 0x1cfc007dff, 0x1c7⟩],
      [⟨0xe80, 0xf4f8ebce400, 0xde6073b03a3a200, 0x360c628⟩, ⟨0xd40, 0xfaf6d329880, 0xed5c6b6d2424100, 0x2d2a580⟩,
       ⟨0x948, 0xbab7d4098c4, 0xe05c6c2de480110, 0x282a8c0⟩, ⟨0x158, 0x9b9754018e7, 0x601eac0dc48011d, 0x8328c1⟩,
       ⟨0x544, 0x7b7603398a2, 0xdde836d0024508, 0x570580⟩, ⟨0x154, 0x5b5701318e7, 0x59e814dc00451d, 0x1701c1⟩,
       ⟨0x682, 0xf500ebde508, 0xdee100003a3ba40, 0x368002c⟩, ⟨0x2a2, 0xe500aed6719, 0x9aa100001b5bae2, 0x128003e⟩,
       ⟨0x22a, 0xad00bc06779, 0xb02300001bc02e6, 0x1000032⟩, ⟨0x5a, 0x9f005c018ff, 0x701f800004c011f, 0x830001⟩],
      [⟨0x3a, 0x8f003c007ff, 0x3007800003c00ff, 0x10013⟩, ⟨0x486, 0x770003fed0a, 0xfe98000003fe40, 0x7c000c⟩,
       ⟨0x446, 0x7f00037b8aa, 0xfff8000002cd08, 0x7f0000⟩, ⟨0xa6, 0x670002f671f, 0xba18000001bee3, 0x2c000e⟩,
       ⟨0x56, 0x5f0001718ff, 0x79f80000004d1f, 0x1f0001⟩, ⟨0x36, 0x4f0000f07ff, 0x38780000003cff, 0xd0007⟩,
       ⟨0xa81, 0xf9efce610, 0x77b23b7a280, 0xd638⟩, ⟨0x2a1, 0xe9aed6719, 0x56921b5bae2, 0x523e⟩,
       ⟨0xa09, 0xbdfc0f650, 0x7c3abfc0280, 0xf830⟩, ⟨0x909, 0xbff40dac4, 0x7c3ff580110, 0xf8c0⟩],
      [⟨0x229, 0xadbc06779, 0x5c129bc02e6, 0x5832⟩, ⟨0x119, 0x9f7401be7, 0x3c0fc58013d, 0x38c1⟩,
       ⟨0x39, 0x8f3c007ff, 0x1c03c3c00ff, 0x1853⟩, ⟨0xa5, 0x6b02f671f, 0x2d2401bee3, 0x20e⟩,
       ⟨0x115, 0x5f01b1be7, 0x1cfc00553d, 0x1c1⟩, ⟨0x35, 0x4f00f07ff, 0xc3c003cff, 0x47⟩]
    ]
  | 6 => [
      [⟨0x580, 0x1e5e7af31d61, 0xacc85e966699a91e, 0x22255555⟩, ⟨0xa40, 0x1dbd9d6de216, 0xdb25e561392e46e1, 0x15588aaa⟩,
       ⟨0xa20, 0x1bbf955ce096, 0x5715e769182614e1, 0x4d8a88a⟩, ⟨0x860, 0x19fdd74ce01e, 0x7307f561986604e1, 0xc5a888a⟩,
       ⟨0x260, 0x19bdb5cef016, 0x5305edf11c2704e1, 0x45cc88a⟩, ⟨0x510, 0x1f5b6eb20d69, 0xecca3a86c2d0a81e, 0x2a231445⟩,
       ⟨0x490, 0x1edaeaba0de1, 0xaed81b8e4290b81e, 0x22a13445⟩, ⟨0x190, 0x1e7a6bb60f61, 0xbde81a864390e81e, 0x33211445⟩,
       ⟨0x830, 0x1bfbc71c00de, 0x771fb30d80601401, 0xcd22000⟩, ⟨0x430, 0x1bdbe69a00f9, 0x661e3b8fc0501802, 0x8833400⟩],
      [⟨0x508, 0x17577e819d69, 0xe0ca7856f6d0011e, 0x282f0541⟩, ⟨0x848, 0x15f5df01e61e, 0xf067f061bb6002e1, 0x3c1a0a82⟩,
       ⟨0x148, 0x15757f81b70d, 0xf0637850fff00344, 0x3c0f03c0⟩, ⟨0x828, 0x13f7d700e0de, 0x701ff06d986000e1, 0xc1a0882⟩,
       ⟨0x428, 0x13d7f680d0f9, 0x601e787fd4500082, 0x80f0c00⟩, ⟨0x68, 0x11f5f780f01f, 0x7007f871dc7000e1, 0xc1f0882⟩,
       ⟨0x818, 0x17f3cf000ede, 0xf0ffb00d83600011, 0x3c320000⟩, ⟨0x418, 0x17d3ee800df9, 0xe0de380fc2d0001e, 0x28230441⟩,
       ⟨0x118, 0x17736f800f6d, 0xf0eb3806c3f0001e, 0x3c230441⟩, ⟨0x38, 0x13f3e78000ff, 0x701fb80fc0700003, 0xc130400⟩],
      [⟨0xa04, 0xfaf807dea96, 0xfb58769000ed6e1, 0x3d0a82a⟩, ⟨0x484, 0xecee07b5de1, 0xed807be400db91e, 0x2a0f415⟩,
       ⟨0x284, 0xeaea07f7ba2, 0xfb087ba000fff28, 0x3c0f03c⟩, ⟨0x824, 0xbefc05ce0de, 0x71f876d800614e1, 0xd0a80a⟩,
       ⟨0x424, 0xbcfe05ad0f9, 0x61e07ffc0051882, 0x80fc00⟩, ⟨0x224, 0xbafa05ef0b6, 0x71587fb00071ce1, 0xd0f80a⟩,
       ⟨0x814, 0xfebc03c0ede, 0xfff830d8000d411, 0x3f02000⟩, ⟨0x414, 0xfcbe03a0df9, 0xede038fc000b81e, 0x2a03405⟩,
       ⟨0x94, 0xeeae03e0fe3, 0xff8838e4000fc1e, 0x3e03405⟩, ⟨0x34, 0xbebe01e00ff, 0x71f838fc0001c03, 0xd03400⟩],
      [⟨0xa02, 0x1fa01d7dea96, 0xdfb58000392ed6e1, 0x17d002aa⟩, ⟨0x282, 0x1ea019ff7ba2, 0x9fb080002d8fff28, 0x13c0033c⟩,
       ⟨0x182, 0x1e601bf73f61, 0xbde800002f9beb1e, 0x33200375⟩, ⟨0x842, 0x1de01f6de61e, 0xfb6780003b6e46e1, 0x3d5002aa⟩,
       ⟨0x242, 0x1da01deff316, 0xdb2580003daf67e1, 0x155003ba⟩, ⟨0x142, 0x1d601fe7b70d, 0xf96300003ffb6344, 0x3d0003f0⟩,
       ⟨0x812, 0x1fe00f3c0ede, 0xffff80000360d411, 0x3ff00000⟩, ⟨0x112, 0x1f600fb60f6d, 0xfdeb000003f0e81e, 0x3f200045⟩,
       ⟨0x92, 0x1ee00bbe0fe3, 0xbff880000390fc1e, 0x33e00045⟩, ⟨0x80a, 0x17e01f01eede, 0xf0ff80003b6002f1, 0x3c300282⟩],
      [⟨0x10a, 0x17601f81bf6d, 0xf0eb00003ff0035e, 0x3c2003c1⟩, ⟨0x4a, 0x15e01f81f71f, 0xf06780003ff003e5, 0x3c1003c2⟩,
       ⟨0x1a, 0x17e00f800fff, 0xf0ff800003f0001f, 0x3c300041⟩, ⟨0x806, 0xfe0007deede, 0xfff8000000ed6f1, 0x3f0002a⟩,
       ⟨0x206, 0xfa0007ffbb6, 0xfb58000000fffe9, 0x3d0003e⟩, ⟨0x86, 0xee0007f7fe3, 0xff88000000fff3e, 0x3e0003d⟩,
       ⟨0x16, 0xfe0003e0fff, 0xfff80000000fc1f, 0x3f00005⟩, ⟨0x501, 0x1f7ef39d69, 0x7ed6f6d9a91e, 0xf5555⟩,
       ⟨0x481, 0x1efafb5de1, 0x5fbe669db91e, 0x5f555⟩, ⟨0x281, 0x1eb9ff7ba2, 0x4fba2d8fff28, 0x4f33c⟩],
      [⟨0x181, 0x1e7bf73f61, 0x5e966f9beb1e, 0x55775⟩, ⟨0x241, 0x1dbdeff316, 0x6df13daf67e1, 0xccbba⟩,
       ⟨0x141, 0x1d7fe7b70d, 0x7cd0fffb6344, 0xf43f0⟩, ⟨0x421, 0x1ff6dad0f9, 0x7fffd4551882, 0xffc00⟩,
       ⟨0x221, 0x1fb5def0b6, 0x6ffb1c271ce1, 0xcf88a⟩, ⟨0x61, 0x1df7cef01f, 0x7df1dc7704e1, 0xfc88a⟩,
       ⟨0x409, 0x17fe81ddf9, 0x787ff6d0019e, 0xf0d41⟩, ⟨0x109, 0x177f81bf6d, 0x7856fff0035e, 0xf07c1⟩,
       ⟨0x49, 0x15ff81f71f, 0x7871fff003e5, 0xf0bc2⟩, ⟨0x29, 0x17f780f0ff, 0x787fdc7000e3, 0xf0c82⟩],
      [⟨0x405, 0xfe07bddf9, 0x7ffc00db99e, 0xfc15⟩, ⟨0x205, 0xfa07ffbb6, 0x7fb000fffe9, 0xf83e⟩,
       ⟨0x85, 0xee07f7fe3, 0x7be400fff3e, 0xf43d⟩, ⟨0x25, 0xfe05ef0ff, 0x7ffc0071ce3, 0xfc0a⟩,
       ⟨0xa60, 0x19bd954ce016, 0x5305e561182604e1, 0x458888a⟩, ⟨0x590, 0x1e5a6ab20d61, 0xacc81a864290a81e, 0x22211445⟩,
       ⟨0x868, 0x11f5d700e01e, 0x7007f061986000e1, 0xc1a0882⟩, ⟨0x518, 0x17536e800d69, 0xe0ca3806c2d0001e, 0x28230441⟩,
       ⟨0x838, 0x13f3c70000de, 0x701fb00d80600001, 0xc120000⟩, ⟨0x438, 0x13d3e68000f9, 0x601e380fc0500002, 0x8030400⟩],
      [⟨0xa24, 0xbaf805ce096, 0x7158769000614e1, 0xd0a80a⟩, ⟨0x494, 0xecae03a0de1, 0xed8038e4000b81e, 0x2a03405⟩,
       ⟨0x834, 0xbebc01c00de, 0x71f830d80001401, 0xd02000⟩, ⟨0x434, 0xbcbe01a00f9, 0x61e038fc0001802, 0x803400⟩,
       ⟨0xa42, 0x1da01d6de216, 0xdb258000392e46e1, 0x155002aa⟩, ⟨0x192, 0x1e600bb60f61, 0xbde800000390e81e, 0x33200045⟩,
       ⟨0x84a, 0x15e01f01e61e, 0xf06780003b6002e1, 0x3c100282⟩, ⟨0x14a, 0x15601f81b70d, 0xf06300003ff00344, 0x3c0003c0⟩,
       ⟨0x81a, 0x17e00f000ede, 0xf0ff800003600011, 0x3c300000⟩, ⟨0x11a, 0x17600f800f6d, 0xf0eb000003f0001e, 0x3c200041⟩],
      [⟨0xa06, 0xfa0007dea96, 0xfb58000000ed6e1, 0x3d0002a⟩, ⟨0x286, 0xea0007f7ba2, 0xfb08000000fff28, 0x3c0003c⟩,
       ⟨0x816, 0xfe0003c0ede, 0xfff80000000d411, 0x3f00000⟩, ⟨0x96, 0xee0003e0fe3, 0xff880000000fc1e, 0x3e00005⟩,
       ⟨0x581, 0x1e7af31d61, 0x5e966699a91e, 0x55555⟩, ⟨0x261, 0x1db5cef016, 0x6df11c2704e1, 0xcc88a⟩,
       ⟨0x509, 0x177e819d69, 0x7856f6d0011e, 0xf0541⟩, ⟨0x149, 0x157f81b70d, 0x7850fff00344, 0xf03c0⟩,
       ⟨0x429, 0x17f680d0f9, 0x787fd4500082, 0xf0c00⟩, ⟨0x69, 0x15f780f01f, 0x7871dc7000e1, 0xf0882⟩],
      [⟨0x485, 0xee07b5de1, 0x7be400db91e, 0xf415⟩, ⟨0x285, 0xea07f7ba2, 0x7ba000fff28, 0xf03c⟩,
       ⟨0x425, 0xfe05ad0f9, 0x7ffc0051882, 0xfc00⟩, ⟨0x225, 0xfa05ef0b6, 0x7fb00071ce1, 0xf80a⟩]
    ]
  | 7 => [
      [⟨0xe00, 0xf8f8fbcf940, 0xeca076603ede8e0, 0x340c83e⟩, ⟨0xb00, 0xf2f2f3eeb80, 0xcec067483a9fcd0, 0x2608c37⟩,
       ⟨0x980, 0xe6f6e7ace84, 0x9a426f59331b498, 0x20ad25⟩, ⟨0x620, 0xf9e9bad7168, 0xedb454a21ccca64, 0x354401a⟩,
       ⟨0x460, 0xdded9e5307a, 0x753d5ca68c64226, 0x1965088⟩, ⟨0x190, 0xe7d765b0e87, 0x9b43ab99c303519, 0x292741⟩,
       ⟨0xd0, 0xcfdf4d3061f, 0x330fbb9fc12110b, 0x8b37c0⟩, ⟨0x70, 0xdfcf1c7007f, 0x773f9987c060307, 0x19f12c0⟩,
       ⟨0xc08, 0xbcbcfc0fd50, 0xf0a878743fe00e0, 0x380f038⟩, ⟨0x888, 0xaebeec0de94, 0xb04a787d3720098, 0x80f120⟩],
      [⟨0x448, 0x9dbddc0b47a, 0x703d7876ad60026, 0x186f088⟩, ⟨0xc8, 0x8fbfcc0961f, 0x300ff87fe52000b, 0x83f1c0⟩,
       ⟨0x428, 0xbdadbc0717a, 0xf0bd58269ce0066, 0x3865098⟩, ⟨0x68, 0x9faf9c0307f, 0x703fd827cc60027, 0x18750c8⟩,
       ⟨0x98, 0xaf9f6c00e9f, 0xb04fb81fc32001b, 0x8331c0⟩, ⟨0x58, 0x9f9f5c0067f, 0x703fb81fc16000f, 0x18731c0⟩,
       ⟨0x38, 0xbf8f3c001ff, 0xf0ff9807c0e0007, 0x38710c0⟩, ⟨0x304, 0x737303feba1, 0xfd087c8401ffd0, 0x780e07⟩,
       ⟨0x184, 0x677703bce87, 0xb4387d9c01b599, 0x290f45⟩, ⟨0xc4, 0x4f7f033961f, 0x30f87ffc01110b, 0xb0fc0⟩],
      [⟨0x224, 0x7b6b02f71e9, 0xff485a2400cf64, 0x7c0202⟩, ⟨0x64, 0x5f6f027307f, 0x73f85a7c004327, 0x1f02c0⟩,
       ⟨0x114, 0x775701f0fa7, 0xfd38399c003f19, 0x790741⟩, ⟨0x94, 0x6f5f01b0e9f, 0xb4f839fc00351b, 0x2b07c1⟩,
       ⟨0x54, 0x5f5f017067f, 0x73f839fc00130f, 0x1f07c0⟩, ⟨0x34, 0x7f4f00f01ff, 0xfff8187c000f07, 0x7f02c0⟩,
       ⟨0xc02, 0xfc00ffcfd50, 0xfca800003ffe8e0, 0x3c0003e⟩, ⟨0xa02, 0xfa00fbefbc0, 0xeee000003edfcf0, 0x360003f⟩,
       ⟨0x602, 0xf900fbdf968, 0xedb400003edeae4, 0x354003e⟩, ⟨0x902, 0xf600f7eef84, 0xdec200003b9fcd8, 0x2600037⟩],
      [⟨0x302, 0xf300f3feba1, 0xcfd080003a9ffd0, 0x2780037⟩, ⟨0x422, 0xfd00bed717a, 0xfdbd00001ceca66, 0x3d6001a⟩,
       ⟨0x222, 0xfb00baf71e9, 0xeff480001cccf64, 0x37c001a⟩, ⟨0x112, 0xf70075f0fa7, 0xdfd380000383f19, 0x2790001⟩,
       ⟨0x32, 0xff003cf01ff, 0xffff800000e0f07, 0x3ff0000⟩, ⟨0x80a, 0xbe00fc0ffd4, 0xf0ea00003fe00f8, 0x3800038⟩,
       ⟨0x40a, 0xbd00fc0fd7a, 0xf0bd00003fe00e6, 0x3860038⟩, ⟨0x2a, 0xbf00bc071ff, 0xf0ff80001ce0067, 0x3870018⟩,
       ⟨0x1a, 0xbf007c00fff, 0xf0ff800003e001f, 0x3870000⟩, ⟨0x206, 0x7b0003ffbe9, 0xff48000001fff4, 0x7c0007⟩],
      [⟨0x106, 0x770003fefa7, 0xfd38000001ffd9, 0x790007⟩, ⟨0x26, 0x7f0002f71ff, 0xfff8000000cf67, 0x7f0002⟩,
       ⟨0x16, 0x7f0001f0fff, 0xfff80000003f1f, 0x7f0001⟩, ⟨0xc01, 0xfcffcfd50, 0x7e743ffe8e0, 0xf83e⟩,
       ⟨0xa01, 0xfafbefbc0, 0x77683edfcf0, 0xcc3f⟩, ⟨0x601, 0xf9fbdf968, 0x76e23edeae4, 0xc83e⟩,
       ⟨0x901, 0xf6f7eef84, 0x6f593b9fcd8, 0xad37⟩, ⟨0x301, 0xf3f3feba1, 0x67c87a9ffd0, 0x8e37⟩,
       ⟨0x881, 0xfeefade94, 0x7f7d373b498, 0xfd25⟩, ⟨0x181, 0xf7e7bce87, 0x6fd9f31b599, 0xaf65⟩],
      [⟨0x441, 0xfddf5b47a, 0x7ef6ad74226, 0xf888⟩, ⟨0xc1, 0xffcf3961f, 0x7fffe53110b, 0xffc0⟩,
       ⟨0x809, 0xbefc0ffd4, 0x787d3fe00f8, 0xf138⟩, ⟨0x409, 0xbdfc0fd7a, 0x7876bfe00e6, 0xf0b8⟩,
       ⟨0x89, 0xbfec0de9f, 0x787ff72009b, 0xf1e0⟩, ⟨0x49, 0xbfdc0b67f, 0x787fed6002f, 0xf1c8⟩,
       ⟨0x205, 0x7b03ffbe9, 0x7ea401fff4, 0xe07⟩, ⟨0x105, 0x7703fefa7, 0x7d9c01ffd9, 0xf47⟩,
       ⟨0x85, 0x7f03bde9f, 0x7ffc01b59b, 0xfc5⟩, ⟨0x45, 0x7f037b67f, 0x7ffc01532f, 0xfc0⟩],
      [⟨0x468, 0x9dad9c0307a, 0x703d58268c60026, 0x1865088⟩, ⟨0xd8, 0x8f9f4c0061f, 0x300fb81fc12000b, 0x8331c0⟩,
       ⟨0x78, 0x9f8f1c0007f, 0x703f9807c060007, 0x18710c0⟩, ⟨0x194, 0x675701b0e87, 0xb438399c003519, 0x290741⟩,
       ⟨0xd4, 0x4f5f013061f, 0x30f839fc00110b, 0xb07c0⟩, ⟨0x74, 0x5f4f007007f, 0x73f8187c000307, 0x1f02c0⟩,
       ⟨0xe02, 0xf800fbcf940, 0xeca000003ede8e0, 0x340003e⟩, ⟨0xb02, 0xf200f3eeb80, 0xcec000003a9fcd0, 0x2600037⟩,
       ⟨0x622, 0xf900bad7168, 0xedb400001ccca64, 0x354001a⟩, ⟨0xc0a, 0xbc00fc0fd50, 0xf0a800003fe00e0, 0x3800038⟩],
      [⟨0x42a, 0xbd00bc0717a, 0xf0bd00001ce0066, 0x3860018⟩, ⟨0x3a, 0xbf003c001ff, 0xf0ff800000e0007, 0x3870000⟩,
       ⟨0x306, 0x730003feba1, 0xfd08000001ffd0, 0x780007⟩, ⟨0x226, 0x7b0002f71e9, 0xff48000000cf64, 0x7c0002⟩,
       ⟨0x116, 0x770001f0fa7, 0xfd380000003f19, 0x790001⟩, ⟨0x36, 0x7f0000f01ff, 0xfff80000000f07, 0x7f0000⟩,
       ⟨0xe01, 0xf8fbcf940, 0x76603ede8e0, 0xc83e⟩, ⟨0xb01, 0xf2f3eeb80, 0x67483a9fcd0, 0x8c37⟩,
       ⟨0x981, 0xf6e7ace84, 0x6f59331b498, 0xad25⟩, ⟨0xc09, 0xbcfc0fd50, 0x78743fe00e0, 0xf038⟩],
      [⟨0x889, 0xbeec0de94, 0x787d3720098, 0xf120⟩, ⟨0x449, 0xbddc0b47a, 0x7876ad60026, 0xf088⟩,
       ⟨0xc9, 0xbfcc0961f, 0x787fe52000b, 0xf1c0⟩, ⟨0x305, 0x7303feba1, 0x7c8401ffd0, 0xe07⟩,
       ⟨0x185, 0x7703bce87, 0x7d9c01b599, 0xf45⟩, ⟨0xc5, 0x7f033961f, 0x7ffc01110b, 0xfc0⟩]
    ]
  | 8 => [
      [⟨0x580, 0xe5f5eb9f0c1, 0xa960f6f0789c4e2, 0x112ccaa⟩, ⟨0xa40, 0xdafad768e38, 0x561c6f4e265321d, 0x89aa55⟩,
       ⟨0x520, 0xf5e5bad71c1, 0xede0d4b0598cce2, 0x33244aa⟩, ⟨0x4a0, 0xededaab70c5, 0xab62d5b1588c5e2, 0x11645aa⟩,
       ⟨0x1a0, 0xe7e7ae970c3, 0xb961dcb0d8ac4e2, 0x15254aa⟩, ⟨0xa10, 0xfada75e0f38, 0xde9c2b0e0743a1d, 0x2a92255⟩,
       ⟨0x850, 0xdede5d60e3a, 0x761d3b0e866321d, 0xc93255⟩, ⟨0x250, 0xdbdb5570e3c, 0x571e2b8f064331d, 0x8d2355⟩,
       ⟨0x908, 0xb6b6fc0eb92, 0xf0c97864bfe0088, 0x3c0f030⟩, ⟨0x188, 0xa7b7ec0f2c3, 0xb061f874faa00e2, 0x142f0a2⟩],
      [⟨0x848, 0x9ebedc0ae3a, 0x701d786eae6001d, 0xc1f051⟩, ⟨0xc8, 0x8fbfcc0b60f, 0x3007f87fea20024, 0x40f0c0⟩,
       ⟨0x128, 0xb7a7bc071d3, 0xf0e9d830d9e00e2, 0x3c250a2⟩, ⟨0xa8, 0xafafac070cf, 0xb067d833d8a00e2, 0x14250a2⟩,
       ⟨0x818, 0xbe9e7c00fba, 0xf0dd380e87e001d, 0x3c13051⟩, ⟨0x58, 0x9f9f5c00e3f, 0x701fb80fc66001d, 0xc13051⟩,
       ⟨0x38, 0xbf8f3c001ff, 0xf0ff9803c1e0003, 0x3c31000⟩, ⟨0x604, 0x797903fdd64, 0xfb207d9001ff50, 0x3c0f0c⟩,
       ⟨0x484, 0x6d7d03bf4c5, 0xb6287f9401d5e2, 0x160f8a⟩, ⟨0x244, 0x5b7b0379e3c, 0x71e07df001731d, 0xd0f45⟩],
      [⟨0xc4, 0x4f7f033b60f, 0x30787ffc015124, 0x40fc0⟩, ⟨0x424, 0x7d6d02f71e5, 0xff285b1400cfe2, 0x3e058a⟩,
       ⟨0xa4, 0x6f6f02b70cf, 0xb6785b3c00c5e2, 0x16058a⟩, ⟨0x214, 0x7b5b01f0f7c, 0xfbe038f0003f1d, 0x3d0345⟩,
       ⟨0x54, 0x5f5f0170e3f, 0x71f838fc00331d, 0xd0345⟩, ⟨0x34, 0x7f4f00f01ff, 0xfff8183c000f03, 0x3f0100⟩,
       ⟨0xa02, 0xfa00f7ecf38, 0xde9c0000375ba1d, 0x2a90015⟩, ⟨0x602, 0xf900f3fdd64, 0xcfb20000351ff50, 0x23c000c⟩,
       ⟨0x902, 0xf600ffceb92, 0xfcc900003ffa888, 0x3e00030⟩, ⟨0x502, 0xf500fbdf9c1, 0xede080003d9ece2, 0x332002a⟩],
      [⟨0x422, 0xfd00baf71e5, 0xeff28000198cfe2, 0x33e002a⟩, ⟨0x122, 0xf700bed71d3, 0xfde9800019ecce2, 0x3f2002a⟩,
       ⟨0x812, 0xfe007de0fba, 0xfedd000007e3a1d, 0x3e90015⟩, ⟨0x212, 0xfb0075f0f7c, 0xdfbe00000743f1d, 0x2bd0015⟩,
       ⟨0x32, 0xff003cf01ff, 0xffff800001e0f03, 0x3ff0000⟩, ⟨0x80a, 0xbe00fc0efba, 0xf0dd00003fe009d, 0x3c10031⟩,
       ⟨0x10a, 0xb700fc0fbd3, 0xf0e980003fe00ea, 0x3c20032⟩, ⟨0x2a, 0xbf00bc071ff, 0xf0ff800019e00e3, 0x3c30022⟩,
       ⟨0x1a, 0xbf007c00fff, 0xf0ff800007e001f, 0x3c30011⟩, ⟨0x406, 0x7d0003ffde5, 0xff28000001fff2, 0x3e000e⟩],
      [⟨0x206, 0x7b0003fdf7c, 0xfbe0000001ff5d, 0x3d000d⟩, ⟨0x26, 0x7f0002f71ff, 0xfff8000000cfe3, 0x3f000a⟩,
       ⟨0x16, 0x7f0001f0fff, 0xfff80000003f1f, 0x3f0005⟩, ⟨0xa01, 0xfaf7ecf38, 0x6f4e375ba1d, 0xaa55⟩,
       ⟨0x601, 0xf9f3fdd64, 0x67d9351ff50, 0x8f0c⟩, ⟨0x901, 0xf6ffceb92, 0x7e64bffa888, 0xf830⟩,
       ⟨0x501, 0xf5fbdf9c1, 0x76f07d9ece2, 0xccaa⟩, ⟨0x481, 0xfdebbf4c5, 0x77f9789d5e2, 0xcfaa⟩,
       ⟨0x181, 0xf7ef9f2c3, 0x7ef4fabc4e2, 0xfcaa⟩, ⟨0x841, 0xfedf6ae3a, 0x7f6eae7321d, 0xfa55⟩],
      [⟨0x241, 0xfbd779e3c, 0x6fdf265731d, 0xaf55⟩, ⟨0xc1, 0xffcf3b60f, 0x7fffea35124, 0xffc0⟩,
       ⟨0x809, 0xbefc0efba, 0x786ebfe009d, 0xf071⟩, ⟨0x109, 0xb7fc0fbd3, 0x7874ffe00ea, 0xf0b2⟩,
       ⟨0x89, 0xbfec0f6cf, 0x787ffaa00e6, 0xf0e2⟩, ⟨0x49, 0xbfdc0be3f, 0x787fee6003d, 0xf0d1⟩,
       ⟨0x405, 0x7d03ffde5, 0x7f9401fff2, 0xf8e⟩, ⟨0x205, 0x7b03fdf7c, 0x7df001ff5d, 0xf4d⟩,
       ⟨0x85, 0x7f03bf6cf, 0x7ffc01d5e6, 0xfca⟩, ⟨0x45, 0x7f037be3f, 0x7ffc01733d, 0xfc5⟩],
      [⟨0x5a0, 0xe5e5aa970c1, 0xa960d4b0588c4e2, 0x11244aa⟩, ⟨0xa50, 0xdada5560e38, 0x561c2b0e064321d, 0x892255⟩,
       ⟨0x1a8, 0xa7a7ac070c3, 0xb061d830d8a00e2, 0x14250a2⟩, ⟨0x858, 0x9e9e5c00e3a, 0x701d380e866001d, 0xc13051⟩,
       ⟨0x4a4, 0x6d6d02b70c5, 0xb6285b1400c5e2, 0x16058a⟩, ⟨0x254, 0x5b5b0170e3c, 0x71e038f000331d, 0xd0345⟩,
       ⟨0x522, 0xf500bad71c1, 0xede08000198cce2, 0x332002a⟩, ⟨0xa12, 0xfa0075e0f38, 0xde9c00000743a1d, 0x2a90015⟩,
       ⟨0x90a, 0xb600fc0eb92, 0xf0c900003fe0088, 0x3c00030⟩, ⟨0x12a, 0xb700bc071d3, 0xf0e9800019e00e2, 0x3c20022⟩],
      [⟨0x81a, 0xbe007c00fba, 0xf0dd000007e001d, 0x3c10011⟩, ⟨0x3a, 0xbf003c001ff, 0xf0ff800001e0003, 0x3c30000⟩,
       ⟨0x606, 0x790003fdd64, 0xfb20000001ff50, 0x3c000c⟩, ⟨0x426, 0x7d0002f71e5, 0xff28000000cfe2, 0x3e000a⟩,
       ⟨0x216, 0x7b0001f0f7c, 0xfbe00000003f1d, 0x3d0005⟩, ⟨0x36, 0x7f0000f01ff, 0xfff80000000f03, 0x3f0000⟩,
       ⟨0x581, 0xf5eb9f0c1, 0x76f0789c4e2, 0xccaa⟩, ⟨0xa41, 0xfad768e38, 0x6f4e265321d, 0xaa55⟩,
       ⟨0x909, 0xb6fc0eb92, 0x7864bfe0088, 0xf030⟩, ⟨0x189, 0xb7ec0f2c3, 0x7874faa00e2, 0xf0a2⟩],
      [⟨0x849, 0xbedc0ae3a, 0x786eae6001d, 0xf051⟩, ⟨0xc9, 0xbfcc0b60f, 0x787fea20024, 0xf0c0⟩,
       ⟨0x605, 0x7903fdd64, 0x7d9001ff50, 0xf0c⟩, ⟨0x485, 0x7d03bf4c5, 0x7f9401d5e2, 0xf8a⟩,
       ⟨0x245, 0x7b0379e3c, 0x7df001731d, 0xf45⟩, ⟨0xc5, 0x7f033b60f, 0x7ffc015124, 0xfc0⟩]
    ]
  | 9 => [
      [⟨0x980, 0x3dbcfd7a6441, 0xf5a47bcc9ea254900, 0x2aa359120⟩, ⟨0x940, 0x3bbef9597409, 0xb3e17beeba2044340, 0x22735b400⟩,
       ⟨0x8c0, 0x39bdfb58ec01, 0xb1a07fdd9a7044100, 0x2223f9000⟩, ⟨0x1c0, 0x39fcf9dc6601, 0xb9b07bcc9b2864100, 0x322359200⟩,
       ⟨0x920, 0x37baf53b6149, 0x778d72ec36a216b00, 0xbe14b120⟩, ⟨0x8a0, 0x35b9f73ae0c1, 0x758476dc16e615900, 0xaa1c9160⟩,
       ⟨0x4a0, 0x3579b7b6c0e2, 0x6d06369807e799802, 0xc81c01e8⟩, ⟨0x1a0, 0x35f8f5be6061, 0x7d8672cc17a31c900, 0xea1491a0⟩,
       ⟨0x610, 0x2e772ee41bb6, 0xc85aad034d1da80bf, 0x140e20a9b⟩, ⟨0x490, 0x2d75aff40ae2, 0xe8162f810f1fb8012, 0x1c0320398⟩],
      [⟨0x190, 0x2df4edfc0661, 0xf8366bc09f0b7c000, 0x3e0318380⟩, ⟨0x250, 0x2af76acc1e1e, 0x9871ad43e918e00f1, 0x301a30e12⟩,
       ⟨0x150, 0x2bf6e9dc160d, 0xb871ebc2bb0864060, 0x321b18600⟩, ⟨0xd0, 0x29f5ebdc0e03, 0xb8306fc19b18e4010, 0x320338210⟩,
       ⟨0x608, 0x1e6f1e839bb6, 0x65a9c3340dd834bf, 0x10ca485f⟩, ⟨0x848, 0x1bafdb01fc19, 0x3e15e3ff070007c0, 0x70e7c00⟩,
       ⟨0x248, 0x1aef5a81be1e, 0x2f19c37e058806f1, 0x58a6c12⟩, ⟨0x828, 0x17abd703e1d9, 0x78d563c70e603f08, 0x1e0c7064⟩,
       ⟨0x428, 0x176b9783c1f6, 0x70e963840e783c0f, 0x184c406d⟩, ⟨0x904, 0x3f9ec07b7549, 0xf7ed41eeb00056b40, 0x2bf01b400⟩],
      [⟨0x844, 0x3b9fc059fc19, 0xb3e141fff000447c0, 0x22701fc00⟩, ⟨0x244, 0x3adf404dbe1e, 0x9af18177e000606f1, 0x305816c02⟩,
       ⟨0x144, 0x3bdec05d760d, 0xbbf1c1eeb00064360, 0x32781b400⟩, ⟨0x824, 0x379bc03be1d9, 0x778d40fc700017f08, 0xbe00f004⟩,
       ⟨0x124, 0x37dac03f616d, 0x7f8fc0ec30001eb04, 0xfe40b000⟩, ⟨0x214, 0x2ed7406c1fbe, 0xd87b8143e000680ff, 0x341c10c03⟩,
       ⟨0x114, 0x2fd6c07c176d, 0xf87fc1c2b0007c064, 0x3e1c18400⟩, ⟨0x54, 0x2bd7c05c1e1f, 0xb871c1c3f000640f1, 0x321818c02⟩,
       ⟨0x80c, 0x1f8fc003fdd9, 0x7ed403ff00003fc8, 0x1f007c04⟩, ⟨0x20c, 0x1ecf4003bfbe, 0x6fb8037e000036ff, 0x15c06c07⟩],
      [⟨0x4c, 0x1bcfc001fe1f, 0x3f1c03ff000007f1, 0x7807c02⟩, ⟨0x2c, 0x17cbc003e1ff, 0x78fc03c700003f0f, 0x1e407005⟩,
       ⟨0x602, 0x3e403ee79bb6, 0xce5a80000dddab4bf, 0x150c002df⟩, ⟨0x482, 0x3d403ff6cae2, 0xed1600000fffb9812, 0x1c80003f8⟩,
       ⟨0x182, 0x3dc03dfe6661, 0xfdb640000fab7c900, 0x3ea0003a0⟩, ⟨0x422, 0x374037b7c1f6, 0x6f0e800007e79bc0f, 0xd84001ed⟩,
       ⟨0x122, 0x37c035bf616d, 0x7f8fc00007a31eb04, 0xfe4001a0⟩, ⟨0xa2, 0x35c037bee0e3, 0x7d86400007e79d902, 0xea0001e8⟩,
       ⟨0x412, 0x2f402ff41bf6, 0xe85e80000f1fb80bf, 0x1c0c0039b⟩, ⟨0x212, 0x2ec02eec1fbe, 0xd87b80000d1de80ff, 0x341c0029b⟩],
      [⟨0x112, 0x2fc02dfc176d, 0xf87fc0000f0b7c064, 0x3e1c00380⟩, ⟨0x92, 0x2dc02ffc0ee3, 0xf83640000f1ffc012, 0x3e0000398⟩,
       ⟨0x40a, 0x1f401f83dbf6, 0x75e800000ff83cbf, 0x18c0007f⟩, ⟨0x20a, 0x1ec01e83bfbe, 0x6fb800000dd836ff, 0x15c0005f⟩,
       ⟨0x2a, 0x17c01783e1ff, 0x78fc00000e783f0f, 0x1e40006d⟩, ⟨0x206, 0x3ec0006fbfbe, 0xdefb800000006b6ff, 0x355c00007⟩,
       ⟨0x106, 0x3fc0007f776d, 0xffffc00000007eb64, 0x3ffc00000⟩, ⟨0x26, 0x37c0003fe1ff, 0x7f8fc00000001ff0f, 0xfe400005⟩,
       ⟨0x16, 0x2fc0007c1fff, 0xf87fc00000007c0ff, 0x3e1c00003⟩, ⟨0xe, 0x1fc00003ffff, 0x7ffc000000003fff, 0x1fc00007⟩],
      [⟨0x601, 0x3f3ee79bb6, 0x3d334dddab4bf, 0x2a4adf⟩, ⟨0x881, 0x3dff7aecc1, 0x3fdd9ef655900, 0x3f9160⟩,
       ⟨0x481, 0x3dbff6cae2, 0x3f990fffb9812, 0x3e03f8⟩, ⟨0x841, 0x3ffb59fc19, 0x3ffffa70447c0, 0x3ffc00⟩,
       ⟨0x241, 0x3f7acdbe1e, 0x3d77e958e06f1, 0x2b6e12⟩, ⟨0xc1, 0x3dfbdcee03, 0x3fdd9b78e4110, 0x3f9210⟩,
       ⟨0x821, 0x3bf73be1d9, 0x36fc76e617f08, 0x1cf164⟩, ⟨0x421, 0x3bb7b7c1f6, 0x36b847e79bc0f, 0x1c41ed⟩,
       ⟨0xa1, 0x39f7bee0e3, 0x36dc17e79d902, 0x1c91e8⟩, ⟨0x411, 0x37aff41bf6, 0x2f834f1fb80bf, 0x320b9b⟩],
      [⟨0x211, 0x376eec1fbe, 0x2d43ed1de80ff, 0x230e9b⟩, ⟨0x91, 0x35effc0ee3, 0x2fc19f1ffc012, 0x338398⟩,
       ⟨0x51, 0x37ebdc1e1f, 0x2fc3fb18e40f1, 0x338e12⟩, ⟨0x809, 0x2fdf03fdd9, 0x1e3ff0f603fc8, 0xe7c64⟩,
       ⟨0x409, 0x2f9f83dbf6, 0x1e3b40ff83cbf, 0xe487f⟩, ⟨0x209, 0x2f5e83bfbe, 0x1c37e0dd836ff, 0xa6c5f⟩,
       ⟨0x49, 0x2fdb81fe1f, 0x1e3ff078807f1, 0xe7c12⟩, ⟨0x29, 0x2bd783e1ff, 0x163c70e783f0f, 0xc706d⟩,
       ⟨0x9c0, 0x39bcf9586401, 0xb1a07bcc9a2044100, 0x222359000⟩, ⟨0x9a0, 0x35b8f53a6041, 0x758472cc16a214900, 0xaa149120⟩],
      [⟨0x1d0, 0x29f4e9dc0601, 0xb8306bc09b0864000, 0x320318200⟩, ⟨0x944, 0x3b9ec0597409, 0xb3e141eeb00044340, 0x22701b400⟩,
       ⟨0x924, 0x379ac03b6149, 0x778d40ec300016b00, 0xbe00b000⟩, ⟨0x254, 0x2ad7404c1e1e, 0x98718143e000600f1, 0x301810c02⟩,
       ⟨0x154, 0x2bd6c05c160d, 0xb871c1c2b00064060, 0x321818400⟩, ⟨0x84c, 0x1b8fc001fc19, 0x3e1403ff000007c0, 0x7007c00⟩,
       ⟨0x24c, 0x1acf4001be1e, 0x2f18037e000006f1, 0x5806c02⟩, ⟨0x82c, 0x178bc003e1d9, 0x78d403c700003f08, 0x1e007004⟩,
       ⟨0x4a2, 0x354037b6c0e2, 0x6d06000007e799802, 0xc80001e8⟩, ⟨0x1a2, 0x35c035be6061, 0x7d86400007a31c900, 0xea0001a0⟩],
      [⟨0x612, 0x2e402ee41bb6, 0xc85a80000d1da80bf, 0x140c0029b⟩, ⟨0x492, 0x2d402ff40ae2, 0xe81600000f1fb8012, 0x1c0000398⟩,
       ⟨0x192, 0x2dc02dfc0661, 0xf83640000f0b7c000, 0x3e0000380⟩, ⟨0x60a, 0x1e401e839bb6, 0x65a800000dd834bf, 0x10c0005f⟩,
       ⟨0x42a, 0x17401783c1f6, 0x70e800000e783c0f, 0x1840006d⟩, ⟨0x126, 0x37c0003f616d, 0x7f8fc00000001eb04, 0xfe400000⟩,
       ⟨0x216, 0x2ec0006c1fbe, 0xd87b80000000680ff, 0x341c00003⟩, ⟨0x116, 0x2fc0007c176d, 0xf87fc00000007c064, 0x3e1c00000⟩,
       ⟨0x20e, 0x1ec00003bfbe, 0x6fb80000000036ff, 0x15c00007⟩, ⟨0x2e, 0x17c00003e1ff, 0x78fc000000003f0f, 0x1e400005⟩],
      [⟨0x8c1, 0x3dfb58ec01, 0x3fdd9a7044100, 0x3f9000⟩, ⟨0x8a1, 0x39f73ae0c1, 0x36dc16e615900, 0x1c9160⟩,
       ⟨0x4a1, 0x39b7b6c0e2, 0x369807e799802, 0x1c01e8⟩, ⟨0x611, 0x372ee41bb6, 0x2d034d1da80bf, 0x220a9b⟩,
       ⟨0x491, 0x35aff40ae2, 0x2f810f1fb8012, 0x320398⟩, ⟨0x251, 0x376acc1e1e, 0x2d43e918e00f1, 0x230e12⟩,
       ⟨0xd1, 0x35ebdc0e03, 0x2fc19b18e4010, 0x338210⟩, ⟨0x609, 0x2f1e839bb6, 0x1c3340dd834bf, 0xa485f⟩,
       ⟨0x849, 0x2fdb01fc19, 0x1e3ff070007c0, 0xe7c00⟩, ⟨0x249, 0x2f5a81be1e, 0x1c37e058806f1, 0xa6c12⟩],
      [⟨0x829, 0x2bd703e1d9, 0x163c70e603f08, 0xc7064⟩, ⟨0x429, 0x2b9783c1f6, 0x163840e783c0f, 0xc406d⟩]
    ]
  | 10 => [
      [⟨0xd00, 0x3a7dfb1d380, 0x9c07eeb740710, 0x10f52⟩, ⟨0xb00, 0x397cff59640, 0xb207ea3fe4400, 0xf30⟩,
       ⟨0xc80, 0x367ff395910, 0xc887fff508200, 0xfc0⟩, ⟨0xa80, 0x357ef7d1c08, 0xe047fb3d8e020, 0x20fa8⟩,
       ⟨0x2c0, 0x25fae7e2c0d, 0x606f71389f821, 0x21cac⟩, ⟨0x520, 0x1af5da3e3a2, 0x1d16cca6507d8, 0x18a53⟩,
       ⟨0xa10, 0x3d6ebdc1e48, 0xf245b319ee020, 0x205a8⟩, ⟨0x890, 0x376fb5c1d18, 0xe8c5b3d98e020, 0x205a8⟩,
       ⟨0x290, 0x35eeb5e1c0d, 0xe06db3198f821, 0x215ac⟩, ⟨0x250, 0x2deaade0c6d, 0x636d3118af825, 0x254ac⟩],
      [⟨0xd0, 0x27eba5e0c1f, 0x60fd31588f823, 0x234ac⟩, ⟨0xc08, 0x3e5f781db90, 0xdc838fc740710, 0x10352⟩,
       ⟨0x908, 0x3b5d7c1d7c0, 0xbe038e87e0710, 0x10352⟩, ⟨0x508, 0x3add781f3a2, 0x9d138e87407d8, 0x18353⟩,
       ⟨0x428, 0x1ed7581e3b6, 0x1db28cc6407da, 0x1a253⟩, ⟨0x128, 0x1bd55c1e3e3, 0x1f1a8c86607dc, 0x1c253⟩,
       ⟨0x818, 0x3f4f3c01fd8, 0xfec183c1e0030, 0x30100⟩, ⟨0x484, 0x36bf03b7916, 0xc8b07fc019242, 0x20c0⟩,
       ⟨0xc4, 0x27bb03e6c1f, 0x60f875401f863, 0x2308c⟩, ⟨0x424, 0x1eb702be3b6, 0x1db05cc0117da, 0x1a043⟩],
      [⟨0x64, 0xfb302ee0ff, 0x7f85440139cf, 0xf005⟩, ⟨0x94, 0x37af01e1d1f, 0xe8f833c00f823, 0x2308c⟩,
       ⟨0x54, 0x2fab01e0cff, 0x67f831400f82f, 0x2f08c⟩, ⟨0x40c, 0x3e9f001fbb6, 0xddb00fc0007da, 0x1a043⟩,
       ⟨0x2c, 0x1f97001e3ff, 0x1ff80cc0007df, 0x1f043⟩, ⟨0x1c, 0x3f8f0001fff, 0xfff803c00003f, 0x3f000⟩,
       ⟨0x302, 0x3980ff7b661, 0xb308003ff4c84, 0x4030⟩, ⟨0x242, 0x2d80efeac6d, 0x6368003abf8a5, 0x2502c⟩,
       ⟨0x122, 0x1b80de7e3e3, 0x1f18002e70fdc, 0x1c013⟩, ⟨0x62, 0xf80ceee0ff, 0x7f8002a339cf, 0xf005⟩],
      [⟨0x212, 0x3d80bde1e6d, 0xf3680019ef825, 0x2502c⟩, ⟨0x52, 0x2f80ade0cff, 0x67f80018af82f, 0x2f02c⟩,
       ⟨0x10a, 0x3b807c1f7e3, 0xbf180007e07dc, 0x1c013⟩, ⟨0x2a, 0x1f805c1e3ff, 0x1ff80006607df, 0x1f013⟩,
       ⟨0x1a, 0x3f803c01fff, 0xfff80001e003f, 0x3f000⟩, ⟨0x46, 0x2f8003eecff, 0x67f800001f9ef, 0x2f00d⟩,
       ⟨0x26, 0x1f8002fe3ff, 0x1ff8000013fdf, 0x1f007⟩, ⟨0x16, 0x3f8001e1fff, 0xfff800000f83f, 0x3f00c⟩,
       ⟨0xe, 0x3f80001ffff, 0xfff80000007ff, 0x3f003⟩, ⟨0xc01, 0x7ffb9db90, 0x7fff748710, 0xfd2⟩],
      [⟨0xa01, 0x7effd9e48, 0x7fb3fee420, 0xfb8⟩, ⟨0x901, 0x7dff5d7c0, 0x7eebfe4710, 0xf72⟩,
       ⟨0x501, 0x7dfb3f3a2, 0x7eeb7507d8, 0xf53⟩, ⟨0x301, 0x7cff7b661, 0x7ea3ff4c84, 0xf30⟩,
       ⟨0x881, 0x7ff7d5d18, 0x7fffd8e220, 0xfe8⟩, ⟨0x481, 0x7ff3b7916, 0x7fff519242, 0xfc0⟩,
       ⟨0x281, 0x7ef7f3c0d, 0x7fb3d9f821, 0xfac⟩, ⟨0x241, 0x7aefeac6d, 0x7713abf8a5, 0xcac⟩,
       ⟨0xc1, 0x7be7e6c1f, 0x775789f863, 0xcac⟩, ⟨0x421, 0x77dabe3b6, 0x6dce6517da, 0xa53⟩],
      [⟨0x121, 0x75de7e3e3, 0x6ccae70fdc, 0xa53⟩, ⟨0x61, 0x73ceee0ff, 0x6546a339cf, 0x805⟩,
       ⟨0xa90, 0x356eb5c1c08, 0xe045b3198e020, 0x205a8⟩, ⟨0x2d0, 0x25eaa5e0c0d, 0x606d31188f821, 0x214ac⟩,
       ⟨0xd08, 0x3a5d781d380, 0x9c038e8740710, 0x10352⟩, ⟨0x528, 0x1ad5581e3a2, 0x1d128c86407d8, 0x18253⟩,
       ⟨0xd4, 0x27ab01e0c1f, 0x60f831400f823, 0x2308c⟩, ⟨0x42c, 0x1e97001e3b6, 0x1db00cc0007da, 0x1a043⟩,
       ⟨0x252, 0x2d80ade0c6d, 0x63680018af825, 0x2502c⟩, ⟨0x12a, 0x1b805c1e3e3, 0x1f180006607dc, 0x1c013⟩],
      [⟨0x66, 0xf8002ee0ff, 0x7f80000139cf, 0xf005⟩, ⟨0x56, 0x2f8001e0cff, 0x67f800000f82f, 0x2f00c⟩,
       ⟨0x2e, 0x1f80001e3ff, 0x1ff80000007df, 0x1f003⟩, ⟨0x1e, 0x3f800001fff, 0xfff800000003f, 0x3f000⟩,
       ⟨0xd01, 0x7dfb1d380, 0x7eeb740710, 0xf52⟩, ⟨0xb01, 0x7cff59640, 0x7ea3fe4400, 0xf30⟩,
       ⟨0xc81, 0x7ff395910, 0x7fff508200, 0xfc0⟩, ⟨0xa81, 0x7ef7d1c08, 0x7fb3d8e020, 0xfa8⟩,
       ⟨0x2c1, 0x7ae7e2c0d, 0x771389f821, 0xcac⟩, ⟨0x521, 0x75da3e3a2, 0x6cca6507d8, 0xa53⟩]
    ]
  | 11 => [
      [⟨0xd00, 0x3a7df3dcb00, 0x58077dba1ac00, 0x1b44⟩, ⟨0xb00, 0x397cf7f8640, 0x3207783edf800, 0x1a74⟩,
       ⟨0xc80, 0x367feb95910, 0xc887fff110440, 0x81f80⟩, ⟨0xa40, 0x2d7aff69448, 0xa247e23fed020, 0x41c78⟩,
       ⟨0x8c0, 0x277bef25c18, 0xe0c7e775a4060, 0xc1ca8⟩, ⟨0x520, 0x1af5d2de3a2, 0x1d165caa1af98, 0x31347⟩,
       ⟨0x320, 0x19f4d6fa2e1, 0x170e582e5bb14, 0x29256⟩, ⟨0xa10, 0x3d6ebde1648, 0xb245b21de7020, 0x40c38⟩,
       ⟨0x890, 0x376fada1d18, 0xe8c5b3d5a4060, 0xc0ca8⟩, ⟨0x850, 0x2f6bbd61c58, 0xe2c5a35de5060, 0xc0cb8⟩],
      [⟨0x250, 0x2deabd6146d, 0xa36da21de5025, 0x4ac38⟩, ⟨0xd0, 0x27ebad21c1f, 0xe0fda355a4063, 0xc6ca8⟩,
       ⟨0x488, 0x36df6817996, 0xccb38fc1006ca, 0x94581⟩, ⟨0xc8, 0x27db6c07c1f, 0xe0fb8741a00e3, 0xc6488⟩,
       ⟨0x428, 0x1ed7581e3b6, 0x1db28cc200f9a, 0x34103⟩, ⟨0x98, 0x37cf2c01d9f, 0xecf983c1a006b, 0xd6488⟩,
       ⟨0x58, 0x2fcb3c01c7f, 0xe3f98341e0067, 0xce488⟩, ⟨0x504, 0x3abd03deba2, 0x5d107d801af98, 0x30307⟩,
       ⟨0x484, 0x36bf0397996, 0xccb07fc0106ca, 0x94381⟩, ⟨0x424, 0x1eb702de3b6, 0x1db05cc01af9a, 0x34307⟩],
      [⟨0x124, 0x1bb502fe3e3, 0x1f185c801bf9c, 0x38307⟩, ⟨0x94, 0x37af01a1d9f, 0xecf833c00406b, 0xd6080⟩,
       ⟨0x40c, 0x3e9f001fbb6, 0xddb00fc000fda, 0xb4183⟩, ⟨0x8c, 0x379f0017d9f, 0xecf80fc0006eb, 0xd6181⟩,
       ⟨0x2c, 0x1f97001e3ff, 0x1ff80cc000f9f, 0x3e103⟩, ⟨0x1c, 0x3f8f0001fff, 0xfff803c00007f, 0xfe080⟩,
       ⟨0x302, 0x3980f7fa6e1, 0x3708003edfb14, 0x28076⟩, ⟨0x242, 0x2d80ff6b46d, 0xa368003fed125, 0x4a078⟩,
       ⟨0x222, 0x1d80defa2ed, 0x1768002e7bb15, 0x2a056⟩, ⟨0x122, 0x1b80d6fe3e3, 0x1f18002e5bf9c, 0x38057⟩],
      [⟨0x212, 0x3d80bde16ed, 0xb768001de7035, 0x6a038⟩, ⟨0x52, 0x2f80bd61c7f, 0xe3f8001de5067, 0xce038⟩,
       ⟨0x4a, 0x2f807c0fc7f, 0xe3f80003e01e7, 0xce008⟩, ⟨0x2a, 0x1f805c1e3ff, 0x1ff8000260f9f, 0x3e003⟩,
       ⟨0x1a, 0x3f803c01fff, 0xfff80001e007f, 0xfe008⟩, ⟨0x106, 0x3b8003fefe3, 0x7f1800001ff9c, 0x38007⟩,
       ⟨0x26, 0x1f8002fe3ff, 0x1ff800001bf9f, 0x3e007⟩, ⟨0x16, 0x3f8001e1fff, 0xfff800000707f, 0xfe000⟩,
       ⟨0xe, 0x3f80001ffff, 0xfff8000000fff, 0xfe003⟩, ⟨0xc01, 0x7ffbddb10, 0x7fffb1ac40, 0x1fc4⟩],
      [⟨0xa01, 0x7efff9648, 0x7fa3fff820, 0x1e7c⟩, ⟨0x901, 0x7df7fcf40, 0x77dbedfc00, 0x1b74⟩,
       ⟨0x501, 0x7df3deba2, 0x77dba1af98, 0x1b47⟩, ⟨0x301, 0x7cf7fa6e1, 0x7783edfb14, 0x1a76⟩,
       ⟨0x881, 0x7fefb5d18, 0x7fff5b4460, 0x1fa8⟩, ⟨0x481, 0x7feb97996, 0x7fff1106ca, 0x1f81⟩,
       ⟨0x841, 0x7bff6dc58, 0x7e77fed060, 0x1cf8⟩, ⟨0x241, 0x7aff6b46d, 0x7e23fed125, 0x1c78⟩,
       ⟨0xc1, 0x7bef27c1f, 0x7e775a40e3, 0x1ca8⟩, ⟨0x421, 0x77dade3b6, 0x6dcea1af9a, 0x1347⟩],
      [⟨0x221, 0x76defa2ed, 0x6d82e7bb15, 0x1256⟩, ⟨0x121, 0x75d6fe3e3, 0x65cae5bf9c, 0x1357⟩,
       ⟨0xa50, 0x2d6abd61448, 0xa245a21de5020, 0x40c38⟩, ⟨0x8d0, 0x276bad21c18, 0xe0c5a355a4060, 0xc0ca8⟩,
       ⟨0xd8, 0x27cb2c01c1f, 0xe0f98341a0063, 0xc6488⟩, ⟨0x524, 0x1ab502de3a2, 0x1d105c801af98, 0x30307⟩,
       ⟨0x48c, 0x369f0017996, 0xccb00fc0006ca, 0x94181⟩, ⟨0x42c, 0x1e97001e3b6, 0x1db00cc000f9a, 0x34103⟩,
       ⟨0x9c, 0x378f0001d9f, 0xecf803c00006b, 0xd6080⟩, ⟨0x322, 0x1980d6fa2e1, 0x1708002e5bb14, 0x28056⟩],
      [⟨0x252, 0x2d80bd6146d, 0xa368001de5025, 0x4a038⟩, ⟨0x5a, 0x2f803c01c7f, 0xe3f80001e0067, 0xce008⟩,
       ⟨0x126, 0x1b8002fe3e3, 0x1f1800001bf9c, 0x38007⟩, ⟨0x2e, 0x1f80001e3ff, 0x1ff8000000f9f, 0x3e003⟩,
       ⟨0x1e, 0x3f800001fff, 0xfff800000007f, 0xfe000⟩, ⟨0xd01, 0x7df3dcb00, 0x77dba1ac00, 0x1b44⟩,
       ⟨0xb01, 0x7cf7f8640, 0x7783edf800, 0x1a74⟩, ⟨0xc81, 0x7feb95910, 0x7fff110440, 0x1f80⟩,
       ⟨0xa41, 0x7aff69448, 0x7e23fed020, 0x1c78⟩, ⟨0x8c1, 0x7bef25c18, 0x7e775a4060, 0x1ca8⟩],
      [⟨0x521, 0x75d2de3a2, 0x65caa1af98, 0x1347⟩, ⟨0x321, 0x74d6fa2e1, 0x6582e5bb14, 0x1256⟩]
    ]
  | _ => []

private def candidates (k : Fin 12) : List ProfileRow := (candidateChunks k).flatten

private structure LabeledExtension where
  masks : FourMasks
  graphIndex : Fin 7
  relabel : Fin 17 → Fin 17

private def labeledExtensions (k : Fin 12) : List LabeledExtension :=
  match k.val with
  | 4 => [
      ⟨(0x1c, 0x229, 0x446, 0x883), 2, ![0, 4, 16, 9, 8, 15, 14, 5, 6, 1, 2, 10, 11, 3, 7, 12, 13]⟩,
      ⟨(0x2c, 0x116, 0x443, 0x889), 2, ![0, 4, 16, 8, 9, 14, 15, 6, 5, 2, 1, 11, 10, 7, 3, 13, 12]⟩,
      ⟨(0x3c, 0x46, 0x229, 0x883), 4, ![2, 16, 1, 12, 8, 15, 5, 9, 10, 0, 7, 13, 6, 3, 14, 4, 11]⟩,
      ⟨(0x3c, 0x89, 0x116, 0x443), 4, ![2, 16, 1, 12, 8, 5, 15, 10, 9, 7, 0, 6, 13, 14, 3, 11, 4]⟩,
      ⟨(0x3c, 0x106, 0x229, 0xc03), 2, ![2, 16, 3, 14, 11, 8, 12, 15, 6, 0, 7, 4, 1, 13, 9, 10, 5]⟩,
      ⟨(0x3c, 0x116, 0x209, 0xc03), 2, ![2, 16, 14, 3, 11, 12, 8, 6, 15, 7, 0, 1, 4, 9, 13, 5, 10]⟩,
      ⟨(0x3c, 0x116, 0x229, 0xc03), 3, ![0, 7, 8, 9, 10, 6, 5, 12, 11, 14, 13, 1, 2, 4, 3, 15, 16]⟩,
      ⟨(0x3c, 0x116, 0x289, 0x403), 4, ![1, 13, 9, 5, 2, 8, 16, 11, 10, 6, 0, 4, 14, 15, 7, 12, 3]⟩,
      ⟨(0x3c, 0x116, 0x289, 0x443), 1, ![1, 16, 7, 14, 12, 4, 9, 8, 5, 3, 0, 13, 10, 15, 11, 6, 2]⟩,
      ⟨(0x3c, 0x116, 0x289, 0xc03), 0, ![2, 15, 8, 10, 12, 6, 9, 3, 7, 11, 0, 1, 16, 14, 5, 4, 13]⟩,
      ⟨(0x3c, 0x116, 0x443, 0x889), 0, ![1, 16, 7, 11, 13, 5, 15, 4, 3, 10, 0, 6, 14, 9, 2, 8, 12]⟩,
      ⟨(0x3c, 0x146, 0x229, 0x803), 4, ![1, 13, 5, 9, 2, 16, 8, 10, 11, 0, 6, 14, 4, 7, 15, 3, 12]⟩,
      ⟨(0x3c, 0x146, 0x229, 0x883), 1, ![1, 16, 14, 7, 12, 9, 4, 5, 8, 0, 3, 10, 13, 11, 15, 2, 6]⟩,
      ⟨(0x3c, 0x146, 0x229, 0xc03), 0, ![2, 15, 10, 8, 12, 9, 6, 7, 3, 0, 11, 16, 1, 5, 14, 13, 4]⟩,
      ⟨(0x3c, 0x229, 0x446, 0x883), 0, ![1, 16, 7, 13, 11, 15, 5, 3, 4, 0, 10, 14, 6, 2, 9, 12, 8]⟩,
      ⟨(0x116, 0x22c, 0x443, 0x889), 0, ![0, 15, 16, 9, 14, 8, 7, 3, 4, 2, 1, 12, 13, 11, 10, 5, 6]⟩,
      ⟨(0x11c, 0x229, 0x446, 0x883), 0, ![0, 16, 15, 14, 9, 7, 8, 4, 3, 1, 2, 13, 12, 10, 11, 6, 5]⟩
    ]
  | 6 => [
      ⟨(0x149, 0x286, 0x425, 0x81a), 1, ![0, 9, 10, 15, 16, 7, 8, 6, 5, 1, 2, 12, 13, 11, 14, 4, 3]⟩,
      ⟨(0x14a, 0x285, 0x429, 0x816), 1, ![0, 9, 10, 16, 15, 8, 7, 6, 5, 2, 1, 11, 14, 12, 13, 3, 4]⟩
    ]
  | 7 => [
      ⟨(0x1a, 0x45, 0x306, 0xc09), 2, ![4, 0, 1, 6, 5, 15, 16, 10, 9, 8, 3, 7, 2, 12, 14, 11, 13]⟩,
      ⟨(0x1a, 0xc5, 0x306, 0xc09), 3, ![1, 2, 14, 16, 11, 7, 12, 3, 15, 13, 0, 6, 8, 10, 4, 5, 9]⟩,
      ⟨(0x36, 0xc9, 0x205, 0x80a), 2, ![4, 5, 6, 1, 0, 10, 9, 15, 16, 13, 11, 14, 12, 2, 7, 3, 8]⟩,
      ⟨(0x36, 0xc9, 0x205, 0xc0a), 3, ![1, 16, 11, 2, 14, 15, 3, 12, 7, 4, 10, 9, 5, 0, 13, 8, 6]⟩,
      ⟨(0x36, 0xc9, 0x305, 0x80a), 3, ![1, 11, 16, 14, 2, 3, 15, 7, 12, 9, 5, 4, 10, 8, 6, 0, 13]⟩,
      ⟨(0x36, 0xc9, 0x305, 0xc0a), 6, ![0, 1, 3, 2, 4, 16, 13, 14, 15, 5, 6, 7, 9, 10, 11, 8, 12]⟩,
      ⟨(0x3a, 0x45, 0x306, 0xc09), 3, ![1, 14, 2, 11, 16, 12, 7, 15, 3, 6, 8, 13, 0, 5, 9, 10, 4]⟩,
      ⟨(0x3a, 0xc5, 0x306, 0xc09), 6, ![0, 2, 4, 1, 3, 15, 14, 13, 16, 11, 10, 12, 8, 6, 5, 9, 7]⟩
    ]
  | 8 => [
      ⟨(0x36, 0xc9, 0x605, 0x90a), 5, ![0, 1, 3, 2, 4, 16, 13, 14, 15, 5, 6, 10, 9, 7, 12, 11, 8]⟩,
      ⟨(0x3a, 0xc5, 0x606, 0x909), 5, ![0, 1, 3, 4, 2, 16, 13, 15, 14, 5, 6, 10, 9, 11, 8, 7, 12]⟩
    ]
  | 9 => [
      ⟨(0x116, 0x251, 0x4a1, 0x82c), 4, ![0, 13, 16, 15, 14, 9, 1, 11, 4, 10, 12, 2, 3, 6, 7, 8, 5]⟩,
      ⟨(0x126, 0x254, 0x491, 0x829), 4, ![0, 14, 15, 16, 13, 10, 4, 12, 1, 9, 11, 3, 2, 5, 8, 7, 6]⟩,
      ⟨(0x192, 0x24c, 0x42a, 0x8c1), 4, ![0, 13, 15, 16, 14, 4, 10, 3, 9, 1, 2, 12, 11, 6, 8, 7, 5]⟩,
      ⟨(0x1d0, 0x20e, 0x4a2, 0x849), 4, ![0, 14, 16, 15, 13, 1, 9, 2, 10, 4, 3, 11, 12, 5, 7, 8, 6]⟩
    ]
  | _ => []

def profileAttachments {n : ℕ} (v : FourMasks) : Fin 4 → Finset (Fin n) :=
  ![decodeFinset v.1, decodeFinset v.2.1, decodeFinset v.2.2.1, decodeFinset v.2.2.2]

private theorem profileAttachments_encode {n : ℕ} (B : Fin 4 → Finset (Fin n)) :
    profileAttachments (encodeFinset (B 0), encodeFinset (B 1),
      encodeFinset (B 2), encodeFinset (B 3)) = B := by
  funext i
  fin_cases i <;> simp [profileAttachments, decodeFinset_encode]

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem witnesses_correct (k : Fin 12) (q : ℕ) (hL : 2 ≤ q) (hU : q ≤ 4) :
    witnessMasks k q = independentMasks (base12 k) q := by
  interval_cases q <;> fin_cases k <;> decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem candidates_correct (k : Fin 12) :
    candidates k = ((witnessMasks k 3) ++ (witnessMasks k 4)).map
      (profileRow (witnessMasks k 2) (witnessMasks k 3) (witnessMasks k 4)) := by
  fin_cases k <;> decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem degree_masks_correct (k : Fin 12) :
    degreeThreeMask k = encodeFinset (univ.filter fun v => (base12 k).degree v = 3) ∧
    degreeFourMask k = encodeFinset (univ.filter fun v => (base12 k).degree v = 4) := by
  fin_cases k <;> decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem base_degree_lower (k x : Fin 12) : 3 ≤ (base12 k).degree x := by
  fin_cases k <;> fin_cases x <;> decide +kernel

private def scanChunk (k : Fin 12) (i : Fin (candidateChunks k).length) : Bool :=
  ((candidateChunks k)[i.val]).all (fun a =>
    (feasibleFrom (candidates k) (degreeFourMask k) (degreeThreeMask k) a).all
      (fun v => decide (v ∈ (labeledExtensions k).map LabeledExtension.masks)))

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem scan_case_0 : ∀ i, scanChunk 0 i = true := by
  intro i
  change Fin 8 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem scan_case_1 : ∀ i, scanChunk 1 i = true := by
  intro i
  change Fin 8 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem scan_case_2 : ∀ i, scanChunk 2 i = true := by
  intro i
  change Fin 9 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem scan_case_3 : ∀ i, scanChunk 3 i = true := by
  intro i
  change Fin 9 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem scan_case_4 : ∀ i, scanChunk 4 i = true := by
  intro i
  change Fin 10 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem scan_case_5 : ∀ i, scanChunk 5 i = true := by
  intro i
  change Fin 9 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem scan_case_6 : ∀ i, scanChunk 6 i = true := by
  intro i
  change Fin 10 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem scan_case_7 : ∀ i, scanChunk 7 i = true := by
  intro i
  change Fin 9 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem scan_case_8 : ∀ i, scanChunk 8 i = true := by
  intro i
  change Fin 9 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem scan_case_9 : ∀ i, scanChunk 9 i = true := by
  intro i
  change Fin 11 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem scan_case_10 : ∀ i, scanChunk 10 i = true := by
  intro i
  change Fin 7 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem scan_case_11 : ∀ i, scanChunk 11 i = true := by
  intro i
  change Fin 8 at i
  fin_cases i <;> decide +kernel

private theorem scan_verified (k : Fin 12) (i : Fin (candidateChunks k).length) :
    scanChunk k i = true := by
  fin_cases k
  · exact scan_case_0 i
  · exact scan_case_1 i
  · exact scan_case_2 i
  · exact scan_case_3 i
  · exact scan_case_4 i
  · exact scan_case_5 i
  · exact scan_case_6 i
  · exact scan_case_7 i
  · exact scan_case_8 i
  · exact scan_case_9 i
  · exact scan_case_10 i
  · exact scan_case_11 i

private def checkLabel (k : Fin 12) (entry : LabeledExtension) : Bool :=
  checkGraphRelabel (numbered (base12 k) (profileAttachments entry.masks))
    (target17 entry.graphIndex) entry.relabel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 100000000 in
private theorem labels_checked (k : Fin 12) :
    (labeledExtensions k).all (checkLabel k) = true := by
  fin_cases k <;> decide +kernel

private theorem feasible_gives_iso {k : Fin 12} {a : ProfileRow} (ha : a ∈ candidates k)
    {v : FourMasks} (hv : v ∈ feasibleFrom (candidates k) (degreeFourMask k) (degreeThreeMask k) a) :
    ∃ j : Fin 7, Nonempty (numbered (base12 k) (profileAttachments v) ≃g target17 j) := by
  obtain ⟨ls, hls, hA⟩ := List.mem_flatten.mp ha
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hls
  have hh := List.all_eq_true.mp (scan_verified k ⟨i, hi⟩) a hA
  obtain ⟨entry, hE, rfl⟩ := List.mem_map.mp (of_decide_eq_true (List.all_eq_true.mp hh v hv))
  have hc := List.all_eq_true.mp (labels_checked k) entry hE
  exact ⟨entry.graphIndex, graph_iso_of_check _ _ entry.relabel hc⟩

private theorem witnesses_sound (k : Fin 12) {q : ℕ} (hL : 2 ≤ q) (hU : q ≤ 4) :
    ∀ x ∈ witnessMasks k q, ∃ T : Finset (Fin 12),
      (base12 k)ᶜ.IsNClique q T ∧ encodeFinset T = x := by
  intro x hx
  rw [witnesses_correct k q hL hU] at hx
  exact independentMasks_sound (base12 k) q x hx

private theorem glued_base12_sorted (k : Fin 12) (B : Fin 4 → Finset (Fin 12))
    (hT : (glued (base12 k) B).CliqueFree 3) (hI : (glued (base12 k) B)ᶜ.CliqueFree 6)
    (hMin : ∀ v, 4 ≤ (glued (base12 k) B).degree v)
    (hMax : ∀ v, (glued (base12 k) B).degree v ≤ 5)
    (hOrd : Monotone (fun i => encodeFinset (B i))) :
    ∃ j : Fin 7, Nonempty (glued (base12 k) B ≃g target17 j) := by
  let w2 := witnessMasks k 2
  let w3 := witnessMasks k 3
  let w4 := witnessMasks k 4
  let R i := profileRow w2 w3 w4 (encodeFinset (B i))
  have hMem (i : Fin 4) : R i ∈ candidates k := by
    have hCard1 := hMin (near i)
    have hCard2 := hMax (near i)
    rw [degree_near] at hCard1 hCard2
    rw [candidates_correct]
    apply List.mem_map_of_mem
    have q := independentMasks_complete (base12 k) _ (attachment_independent (base12 k) B hT i)
    rw [witnesses_correct k 3 (by decide) (by decide), witnesses_correct k 4 (by decide) (by decide)]
    have hc : (B i).card = 3 ∨ (B i).card = 4 := by omega
    rcases hc with hc | hc
    · exact List.mem_append_left _ (hc ▸ q)
    · exact List.mem_append_right _ (hc ▸ q)
  have hP (i j : Fin 4) (h : i < j) : compatiblePair (degreeFourMask k) (R i) (R j) = true := by
    rw [(degree_masks_correct k).2]
    exact profilePair_of_glued (base12 k) B hI (fun v => hMax (far v)) w2 w3 w4
      (witnesses_sound k (by decide) (by decide)) i j (ne_of_lt h) (hOrd h.le)
  have hTr (i j l : Fin 4) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
      compatibleTriple (R i) (R j) (R l) = true :=
    profileTriple_of_glued (base12 k) B hI (fun v => hMax (far v)) (base_degree_lower k) w2 w3 w4
      (witnesses_sound k (by decide) (by decide)) i j l hij hil hjl
  have hCov : coversLow (degreeThreeMask k) (R 0) (R 1) (R 2) (R 3) = true := by
    rw [(degree_masks_correct k).1]
    exact profileCover_of_glued (base12 k) B hI (fun v => hMin (far v)) w2 w3 w4
      (witnesses_sound k (by decide) (by decide))
  have hAll := mem_feasibleFrom (candidates k) (degreeFourMask k) (degreeThreeMask k)
    (R 0) (R 1) (R 2) (R 3) (hMem 1) (hMem 2) (hMem 3)
    (hP 0 1 (by decide)) (hP 0 2 (by decide)) (hP 0 3 (by decide))
    (hP 1 2 (by decide)) (hP 1 3 (by decide)) (hP 2 3 (by decide))
    (hTr 0 1 2 (by decide) (by decide) (by decide)) (hTr 0 1 3 (by decide) (by decide) (by decide))
    (hTr 0 2 3 (by decide) (by decide) (by decide)) (hTr 1 2 3 (by decide) (by decide) (by decide)) hCov
  obtain ⟨j, ⟨e⟩⟩ := feasible_gives_iso (hMem 0) hAll
  change numbered (base12 k) (profileAttachments
    (encodeFinset (B 0), encodeFinset (B 1), encodeFinset (B 2), encodeFinset (B 3))) ≃g target17 j at e
  rw [profileAttachments_encode] at e
  exact ⟨j, ⟨(number_glued (base12 k) B).symm.trans e⟩⟩

theorem glued_base12_catalogued (k : Fin 12) (B : Fin 4 → Finset (Fin 12))
    (hT : (glued (base12 k) B).CliqueFree 3) (hI : (glued (base12 k) B)ᶜ.CliqueFree 6)
    (hMin : ∀ v, 4 ≤ (glued (base12 k) B).degree v)
    (hMax : ∀ v, (glued (base12 k) B).degree v ≤ 5) :
    ∃ j : Fin 7, Nonempty (glued (base12 k) B ≃g target17 j) := by
  let e := Tuple.sort (fun i => encodeFinset (B i))
  let B' := B ∘ e
  let g := relabel_near (base12 k) B e
  have hT' : (glued (base12 k) B').CliqueFree 3 := hT.comap g.toEmbedding.isContained
  have hI' : (glued (base12 k) B')ᶜ.CliqueFree 6 :=
    hI.comap (SimpleGraph.Embedding.complEquiv g.toEmbedding).isContained
  have hM' (v : Vertex 4 12) : 4 ≤ (glued (base12 k) B').degree v := by
    rw [← g.degree_eq]
    exact hMin _
  have hX' (v : Vertex 4 12) : (glued (base12 k) B').degree v ≤ 5 := by
    rw [← g.degree_eq]
    exact hMax _
  obtain ⟨j, ⟨h⟩⟩ := glued_base12_sorted k B' hT' hI' hM' hX' (Tuple.monotone_sort (fun i : Fin 4 => encodeFinset (B i)))
  exact ⟨j, ⟨g.symm.trans h⟩⟩

end OMA.RamseyCatalogue

namespace OMA.RamseyCatalogue

open SimpleGraph Finset
open scoped BigOperators

/-- The classification of the seventeen-vertex Ramsey graphs follows from
the thirteen- and twelve-vertex catalogues and the finite gluing certificates. -/
theorem complete17_of_smaller
    (h13 : ∀ G : SimpleGraph (Fin 13), G.CliqueFree 3 → Gᶜ.CliqueFree 5 →
      Nonempty (G ≃g base13))
    (h12 : ∀ G : SimpleGraph (Fin 12), G.CliqueFree 3 → Gᶜ.CliqueFree 5 →
      ∃ k : Fin 12, Nonempty (G ≃g base12 k))
    (G : SimpleGraph (Fin 17)) (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 6) :
    ∃ k : Fin 7, Nonempty (G ≃g target17 k) := by
  classical
  have hLo (v : Fin 17) : 3 ≤ G.degree v := by
    have h := anti_card_le_thirteen G hT hI v
    rw [G.degree_compl, Fintype.card_fin] at h
    omega
  have hHi (v : Fin 17) : G.degree v ≤ 5 := by
    have h := degree_lt_independent G hT hI v
    omega
  have hLo4 (v : Fin 17) : 4 ≤ G.degree v := by
    by_contra! hv
    have hv3 : G.degree v = 3 := by have := hLo v; omega
    have ha : Gᶜ.degree v = 13 := by
      rw [G.degree_compl, Fintype.card_fin, hv3]
    obtain ⟨H, B, hHT, hHI, ⟨e⟩⟩ := exists_gluing G v (s := 5) hv3 ha hT hI
    obtain ⟨f⟩ := h13 H hHT hHI
    let B' := fun i => (B i).map f.toEquiv.toEmbedding
    let g : glued base13 B' ≃g G := (relabel_far f B).symm.trans e
    have hGT : (glued base13 B').CliqueFree 3 := hT.comap g.toEmbedding.isContained
    have hGI : (glued base13 B')ᶜ.CliqueFree 6 :=
      hI.comap (SimpleGraph.Embedding.complEquiv g.toEmbedding).isContained
    exact glued_base13_impossible B' hGT hGI
      (fun i => by rw [← g.degree_eq]; exact hLo _)
      (fun j => by rw [← g.degree_eq]; exact hHi _)
  have hSome4 : ∃ v : Fin 17, G.degree v = 4 := by
    by_contra! hImpossible
    have hAll (v : Fin 17) : G.degree v = 5 := by
      have hL := hLo4 v
      have hU := hHi v
      have hNe := hImpossible v
      omega
    have hsum := G.sum_degrees_eq_twice_card_edges
    simp only [hAll, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    omega
  obtain ⟨v, hv⟩ := hSome4
  have ha : Gᶜ.degree v = 12 := by
    rw [G.degree_compl, Fintype.card_fin, hv]
  obtain ⟨H, B, hHT, hHI, ⟨e⟩⟩ := exists_gluing G v (s := 5) hv ha hT hI
  obtain ⟨k, ⟨f⟩⟩ := h12 H hHT hHI
  let B' := fun i => (B i).map f.toEquiv.toEmbedding
  let g : glued (base12 k) B' ≃g G := (relabel_far f B).symm.trans e
  have hGT : (glued (base12 k) B').CliqueFree 3 := hT.comap g.toEmbedding.isContained
  have hGI : (glued (base12 k) B')ᶜ.CliqueFree 6 :=
    hI.comap (SimpleGraph.Embedding.complEquiv g.toEmbedding).isContained
  obtain ⟨j, ⟨h⟩⟩ := glued_base12_catalogued k B' hGT hGI
    (fun i => by rw [← g.degree_eq]; exact hLo4 _)
    (fun i => by rw [← g.degree_eq]; exact hHi _)
  exact ⟨j, ⟨g.symm.trans h⟩⟩

end OMA.RamseyCatalogue

/-
A finite labeled graph is determined by one bit for each strict upper-triangle
position. The triangular offsets make the code representation easy to enumerate.
-/

namespace OMA.RamseyCatalogue

open SimpleGraph Finset

def edgeIndex {n : ℕ} (i j : Fin n) : ℕ :=
  (max i.val j.val).choose 2 + min i.val j.val

theorem edgeIndex_comm {n : ℕ} (i j : Fin n) : edgeIndex i j = edgeIndex j i := by
  simp only [edgeIndex, max_comm, min_comm]

private theorem offset_lt {i j n : ℕ} (hij : i < j) (hjn : j < n) :
    j.choose 2 + i < n.choose 2 := by
  have h : j.choose 2 + i < (j + 1).choose 2 := by
    rw [Nat.choose_succ_succ' j 1, Nat.choose_one_right]
    change j.choose 2 + i < j + j.choose 2
    omega
  exact h.trans_le (Nat.choose_le_choose _ (by omega))

theorem edgeIndex_lt {n : ℕ} {i j : Fin n} (h : i ≠ j) : edgeIndex i j < n.choose 2 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [edgeIndex, max_eq_right (show i.val ≤ j.val from hlt.le), min_eq_left (show i.val ≤ j.val from hlt.le)]
    exact offset_lt hlt j.isLt
  · rw [edgeIndex_comm, edgeIndex, max_eq_right (show j.val ≤ i.val from hgt.le), min_eq_left (show j.val ≤ i.val from hgt.le)]
    exact offset_lt hgt i.isLt

theorem edgeIndex_inj {n : ℕ} {i j u v : Fin n} (h : i < j) (h' : u < v)
    (he : edgeIndex i j = edgeIndex u v) : i = u ∧ j = v := by
  rw [edgeIndex, edgeIndex, max_eq_right (show i.val ≤ j.val from h.le), min_eq_left (show i.val ≤ j.val from h.le),
    max_eq_right (show u.val ≤ v.val from h'.le), min_eq_left (show u.val ≤ v.val from h'.le)] at he
  have hjv : j = v := by
    by_contra! hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have q := offset_lt h hlt
      omega
    · have q := offset_lt h' hgt
      omega
  subst v
  exact ⟨Fin.ext (Nat.add_left_cancel he), rfl⟩

def graphFromCode (n : ℕ) (bits : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ bits.testBit (edgeIndex i j) = true
  symm := ⟨fun {i j} h => ⟨h.1.symm, by rw [edgeIndex_comm j i]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance graphFromCodeAdj (n bits : ℕ) : DecidableRel (graphFromCode n bits).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem exists_code {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ bits < 2 ^ (n.choose 2), graphFromCode n bits = G := by
  classical
  let S : Finset (Fin (n.choose 2)) :=
    Finset.univ.filter fun q => ∃ i j, i < j ∧ edgeIndex i j = q.val ∧ G.Adj i j
  let bits := encodeFinset S
  refine ⟨bits, ?_, ?_⟩
  · apply Nat.lt_pow_two_of_testBit
    intro i hi
    apply Bool.eq_false_iff.mpr
    intro he
    obtain ⟨j, _, hj⟩ := (encodeFinset_testBit S i).mp he
    omega
  · ext i j
    have hLower (a b : Fin n) (hab : a < b) :
        (graphFromCode n bits).Adj a b ↔ G.Adj a b := by
      let index : Fin (n.choose 2) := ⟨edgeIndex a b, edgeIndex_lt (ne_of_lt hab)⟩
      change a ≠ b ∧ (encodeFinset S).testBit index.val = true ↔ G.Adj a b
      rw [encodeFinset_testBit_fin]
      constructor
      · intro hm
        obtain ⟨u, v, hlt, hEq, hu⟩ := (Finset.mem_filter.mp hm.2).2
        obtain ⟨e₁, e₂⟩ := edgeIndex_inj hlt hab hEq
        simpa only [e₁, e₂] using hu
      · intro ha
        exact ⟨ne_of_lt hab, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, ⟨a, b, hab, rfl, ha⟩⟩⟩
    rcases lt_trichotomy i j with hin | hin | hin
    · exact hLower _ _ hin
    · subst j
      simp
    · rw [(graphFromCode n bits).adj_comm i j, G.adj_comm i j]
      exact hLower _ _ hin

end OMA.RamseyCatalogue

/-
The (3,3) catalogues at orders four and five come from an exhaustive triangular
bit enumeration. The labeled witnesses are the matching, path, and cycle
at order four and the five-cycle at order five.
-/

namespace OMA.RamseyCatalogue

open SimpleGraph Finset

def fourReference : Fin 3 → ℕ := ![33, 37, 45]
def baseFour (j : Fin 3) : SimpleGraph (Fin 4) := graphFromCode 4 (fourReference j)
def baseFive : SimpleGraph (Fin 5) := graphFromCode 5 613

instance baseFourAdj (j : Fin 3) : DecidableRel (baseFour j).Adj := graphFromCodeAdj _ _
instance baseFiveAdj : DecidableRel baseFive.Adj := graphFromCodeAdj _ _

private theorem forbiddenTriangle {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hT : G.CliqueFree 3) {i j k : V} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hIJ : G.Adj i j) (hIK : G.Adj i k) (hJK : G.Adj j k) : False := by
  apply hT ({i, j, k} : Finset V)
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
      | exact (hab rfl).elim
      | exact hIJ
      | exact hIK
      | exact hJK
      | exact hIJ.symm
      | exact hIK.symm
      | exact hJK.symm
  · rw [Finset.card_insert_of_notMem (by simp [hij, hik]), Finset.card_pair hjk]

private def checkTriplet {n : ℕ} (bits : ℕ) : List (Fin n) → Bool
  | [i, j, k] => !((bits.testBit (edgeIndex i j) == bits.testBit (edgeIndex i k)) &&
      (bits.testBit (edgeIndex i k) == bits.testBit (edgeIndex j k)))
  | _ => true

private theorem triplet_correct {n bits : ℕ}
    (hT : (graphFromCode n bits).CliqueFree 3) (hI : (graphFromCode n bits)ᶜ.CliqueFree 3)
    (vs : List (Fin n)) (hd : vs.Nodup) : checkTriplet bits vs = true := by
  rcases vs with _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨l, ls⟩⟩⟩⟩
  all_goals try rfl
  simp at hd
  obtain ⟨⟨hij, hik⟩, hjk⟩ := hd
  cases hIJ : bits.testBit (edgeIndex i j) <;>
    cases hIK : bits.testBit (edgeIndex i k) <;>
    cases hJK : bits.testBit (edgeIndex j k)
  all_goals simp [checkTriplet, hIJ, hIK, hJK]
  · exact forbiddenTriangle _ hI hij hik hjk
      ⟨hij, fun ha => Bool.noConfusion (hIJ.symm.trans ha.2)⟩
      ⟨hik, fun ha => Bool.noConfusion (hIK.symm.trans ha.2)⟩
      ⟨hjk, fun ha => Bool.noConfusion (hJK.symm.trans ha.2)⟩
  · exact forbiddenTriangle _ hT hij hik hjk ⟨hij, hIJ⟩ ⟨hik, hIK⟩ ⟨hjk, hJK⟩

private def checkSmall (n bits : ℕ) : Bool :=
  ((List.finRange n).sublistsLen 3).all (checkTriplet bits)

private theorem checkSmall_complete {n bits : ℕ}
    (hT : (graphFromCode n bits).CliqueFree 3) (hI : (graphFromCode n bits)ᶜ.CliqueFree 3) :
    checkSmall n bits = true := by
  apply List.all_eq_true.mpr
  intro vs hv
  exact triplet_correct hT hI vs ((List.nodup_finRange n).sublist (List.mem_sublistsLen.mp hv).1)

private structure SmallLabel (n g : ℕ) where
  code : ℕ
  index : Fin g
  reindex : Fin n → Fin n

private def fourLabels : List (SmallLabel 4 3) :=
  [⟨12, 0, ![0, 2, 3, 1]⟩,
   ⟨13, 1, ![1, 2, 3, 0]⟩,
   ⟨14, 1, ![1, 3, 2, 0]⟩,
   ⟨18, 0, ![0, 2, 1, 3]⟩,
   ⟨19, 1, ![1, 2, 0, 3]⟩,
   ⟨22, 1, ![0, 2, 1, 3]⟩,
   ⟨26, 1, ![1, 3, 0, 2]⟩,
   ⟨28, 1, ![0, 2, 3, 1]⟩,
   ⟨30, 2, ![0, 2, 1, 3]⟩,
   ⟨33, 0, ![0, 1, 2, 3]⟩,
   ⟨35, 1, ![1, 0, 2, 3]⟩,
   ⟨37, 1, ![0, 1, 2, 3]⟩,
   ⟨41, 1, ![1, 0, 3, 2]⟩,
   ⟨44, 1, ![0, 3, 2, 1]⟩,
   ⟨45, 2, ![0, 1, 2, 3]⟩,
   ⟨49, 1, ![0, 1, 3, 2]⟩,
   ⟨50, 1, ![0, 3, 1, 2]⟩,
   ⟨51, 2, ![0, 1, 3, 2]⟩]

private def fiveLabels : List (SmallLabel 5 1) :=
  [⟨236, 0, ![0, 2, 3, 4, 1]⟩,
   ⟨242, 0, ![0, 2, 4, 3, 1]⟩,
   ⟨348, 0, ![0, 2, 3, 1, 4]⟩,
   ⟨369, 0, ![0, 1, 3, 2, 4]⟩,
   ⟨410, 0, ![0, 2, 4, 1, 3]⟩,
   ⟨425, 0, ![0, 1, 3, 4, 2]⟩,
   ⟨598, 0, ![0, 2, 1, 3, 4]⟩,
   ⟨613, 0, ![0, 1, 2, 3, 4]⟩,
   ⟨654, 0, ![0, 2, 1, 4, 3]⟩,
   ⟨675, 0, ![0, 1, 4, 3, 2]⟩,
   ⟨781, 0, ![0, 1, 2, 4, 3]⟩,
   ⟨787, 0, ![0, 1, 4, 2, 3]⟩]

private def checkSmallLabel {n g : ℕ} (ref : Fin g → ℕ) (v : SmallLabel n g) : Bool :=
  checkGraphRelabel (graphFromCode n v.code) (graphFromCode n (ref v.index)) v.reindex

private theorem extract_small_iso {n g : ℕ} {ref : Fin g → ℕ} {labels : List (SmallLabel n g)}
    (h : labels.all (checkSmallLabel ref) = true) {b : ℕ} (hb : b ∈ labels.map SmallLabel.code) :
    ∃ j, Nonempty (graphFromCode n b ≃g graphFromCode n (ref j)) := by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
  exact ⟨v.index, graph_iso_of_check _ _ v.reindex (List.all_eq_true.mp h v hv)⟩

private def scanBlock {n g : ℕ} (labels : List (SmallLabel n g)) (j : ℕ) : Bool :=
  (List.range' (64*j) 64).all
    (fun b => !checkSmall n b || decide (b ∈ labels.map SmallLabel.code))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem four_scan : scanBlock fourLabels 0 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_0 : scanBlock fiveLabels 0 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_1 : scanBlock fiveLabels 1 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_2 : scanBlock fiveLabels 2 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_3 : scanBlock fiveLabels 3 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_4 : scanBlock fiveLabels 4 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_5 : scanBlock fiveLabels 5 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_6 : scanBlock fiveLabels 6 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_7 : scanBlock fiveLabels 7 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_8 : scanBlock fiveLabels 8 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_9 : scanBlock fiveLabels 9 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_10 : scanBlock fiveLabels 10 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_11 : scanBlock fiveLabels 11 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_12 : scanBlock fiveLabels 12 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_13 : scanBlock fiveLabels 13 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_14 : scanBlock fiveLabels 14 = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 15000000 in
private theorem five_scan_15 : scanBlock fiveLabels 15 = true := by
  decide +kernel

private theorem five_scan (i : Fin 16) : scanBlock fiveLabels i.val = true := by
  fin_cases i
  · exact five_scan_0
  · exact five_scan_1
  · exact five_scan_2
  · exact five_scan_3
  · exact five_scan_4
  · exact five_scan_5
  · exact five_scan_6
  · exact five_scan_7
  · exact five_scan_8
  · exact five_scan_9
  · exact five_scan_10
  · exact five_scan_11
  · exact five_scan_12
  · exact five_scan_13
  · exact five_scan_14
  · exact five_scan_15


private theorem four_iso_labels : fourLabels.all (checkSmallLabel fourReference) = true := by
  decide +kernel

private theorem five_iso_labels : fiveLabels.all (checkSmallLabel fun _ => 613) = true := by
  decide +kernel

theorem completeFour (G : SimpleGraph (Fin 4)) (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 3) :
    ∃ j : Fin 3, Nonempty (G ≃g baseFour j) := by
  obtain ⟨b, hb, rfl⟩ := exists_code G
  have hrange : b ∈ List.range' (64*0) 64 :=
    List.mem_range'_1.mpr ⟨by omega, by exact hb⟩
  have result := List.all_eq_true.mp four_scan b hrange
  have he := checkSmall_complete hT hI
  simp only [he, Bool.not_true, Bool.false_or] at result
  exact extract_small_iso four_iso_labels (of_decide_eq_true result)

theorem completeFive (G : SimpleGraph (Fin 5)) (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 3) :
    Nonempty (G ≃g baseFive) := by
  obtain ⟨b, hb, rfl⟩ := exists_code G
  have hb' : b < 1024 := hb
  let j : Fin 16 := ⟨b / 64, by omega⟩
  have hrange : b ∈ List.range' (64 * j.val) 64 :=
    List.mem_range'_1.mpr ⟨by change 64 * (b / 64) ≤ b; omega,
      by change b < 64 * (b / 64) + 64; omega⟩
  have result := List.all_eq_true.mp (five_scan j) b hrange
  have he := checkSmall_complete hT hI
  simp only [he, Bool.not_true, Bool.false_or] at result
  obtain ⟨_, h⟩ := extract_small_iso five_iso_labels (of_decide_eq_true result)
  exact h

end OMA.RamseyCatalogue

namespace OMA.RamseyCatalogue

open SimpleGraph Finset

structure ProfileCap where
  mask : ℕ
  onHit : Bool
  bound : ℕ
  deriving DecidableEq

structure ProfileDemand where
  mask : ℕ
  bound : ℕ
  deriving DecidableEq

def hitCount (rows : List ℕ) (m : ℕ) : ℕ :=
  rows.countP fun a => (a &&& m) != 0

def respectsCaps (caps : List ProfileCap) (rows : List ℕ) : Bool :=
  caps.all fun cap => decide (rows.countP (fun a => ((a &&& cap.mask) != 0) == cap.onHit)
    ≤ cap.bound)

def meetsDemands (demands : List ProfileDemand) (rows : List ℕ) : Bool :=
  demands.all fun demand => decide (demand.bound ≤ hitCount rows demand.mask)

def enumerateTails (opts : List ℕ) (caps : List ProfileCap) :
    ℕ → ℕ → List ℕ → List (List ℕ)
  | 0, _, _ => [[]]
  | m + 1, last, previous =>
      (opts.filter fun a => decide (last ≤ a) && respectsCaps caps (a :: previous)).flatMap
        fun a => (enumerateTails opts caps m a (a :: previous)).map (a :: ·)

private theorem respectsCaps_mono (caps : List ProfileCap) {small large : List ℕ}
    (hSub : List.Sublist small large) (h : respectsCaps caps large = true) : respectsCaps caps small = true := by
  apply List.all_eq_true.mpr
  intro cap hc
  have hBound := of_decide_eq_true (List.all_eq_true.mp h cap hc)
  apply decide_eq_true
  simp only [List.countP_eq_length_filter] at hBound ⊢
  exact (hSub.filter _).length_le.trans hBound

theorem mem_enumerateTails (opts : List ℕ) (caps : List ProfileCap)
    (last : ℕ) (previous xs : List ℕ) (hLast : ∀ a ∈ xs, last ≤ a)
    (hSorted : xs.Pairwise (· ≤ ·)) (hOptions : ∀ a ∈ xs, a ∈ opts)
    (hCaps : respectsCaps caps (xs ++ previous) = true) :
    xs ∈ enumerateTails opts caps xs.length last previous := by
  induction xs generalizing last previous with
  | nil => simp [enumerateTails]
  | cons a xs ih =>
      have hp : List.Sublist (a :: previous) ((a :: xs) ++ previous) :=
        (List.sublist_append_right xs previous).cons_cons a
      have ha := respectsCaps_mono caps hp hCaps
      apply List.mem_flatMap.mpr
      refine ⟨a, List.mem_filter.mpr ⟨hOptions a (by simp), ?_⟩, ?_⟩
      · simp only [ha, Bool.and_true]
        exact decide_eq_true (hLast _ (by simp))
      · apply List.mem_map.mpr
        have hc : respectsCaps caps (xs ++ a :: previous) = true := by
          apply List.all_eq_true.mpr
          intro c hc
          have hOld := List.all_eq_true.mp hCaps c hc
          simpa [List.countP_append, List.countP_cons, Nat.add_left_comm, Nat.add_comm,
            Nat.add_assoc] using hOld
        exact ⟨xs, ih a (a :: previous) (List.pairwise_cons.mp hSorted).1
          (List.pairwise_cons.mp hSorted).2 (fun x hx => hOptions x (List.mem_cons_of_mem _ hx)) hc, rfl⟩

def enumerateFrom (opts : List ℕ) (caps : List ProfileCap) (demands : List ProfileDemand)
    (tailSize first : ℕ) : List (List ℕ) :=
  if respectsCaps caps [first] then
    ((enumerateTails opts caps tailSize first [first]).map (first :: ·)).filter
      (meetsDemands demands)
  else []

theorem mem_enumerateFrom (opts : List ℕ) (caps : List ProfileCap) (demands : List ProfileDemand)
    (first : ℕ) (xs : List ℕ) (hSorted : (first :: xs).Pairwise (· ≤ ·))
    (hOpt : ∀ a ∈ xs, a ∈ opts) (hCaps : respectsCaps caps (first :: xs) = true)
    (hDemands : meetsDemands demands (first :: xs) = true) :
    first :: xs ∈ enumerateFrom opts caps demands xs.length first := by
  have h1 := respectsCaps_mono caps
    (List.sublist_append_left [first] xs) hCaps
  unfold enumerateFrom
  rw [if_pos h1]
  refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨xs, ?_, rfl⟩, hDemands⟩
  apply mem_enumerateTails opts caps first [first] xs
    (List.pairwise_cons.mp hSorted).1 (List.pairwise_cons.mp hSorted).2 hOpt
  apply List.all_eq_true.mpr
  intro c hc
  have hOld := List.all_eq_true.mp hCaps c hc
  simpa [List.countP_append, List.countP_cons, Nat.add_comm] using hOld

def attachmentRows {d n : ℕ} (B : Fin d → Finset (Fin n)) : List ℕ :=
  (List.finRange d).map fun i => encodeFinset (B i)

def attachmentsFromRows (d n : ℕ) (rows : List ℕ) : Fin d → Finset (Fin n) :=
  fun i => decodeFinset (rows[i.val]?.getD 0)

theorem attachmentsFromRows_correct {d n : ℕ} (B : Fin d → Finset (Fin n)) :
    attachmentsFromRows d n (attachmentRows B) = B := by
  funext i
  simp [attachmentsFromRows, attachmentRows, decodeFinset_encode]

theorem attachmentRows_sorted {d n : ℕ} (B : Fin d → Finset (Fin n))
    (h : Monotone (fun i => encodeFinset (B i))) : (attachmentRows B).Pairwise (· ≤ ·) := by
  rw [attachmentRows, List.pairwise_map]
  exact (List.pairwise_le_finRange d).imp (fun hij => h hij)

theorem attachmentRows_countP {d n : ℕ} (B : Fin d → Finset (Fin n)) (p : ℕ → Bool) :
    (attachmentRows B).countP p =
      (Finset.univ.filter fun i => p (encodeFinset (B i)) = true).card := by
  rw [attachmentRows, List.countP_map, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange d).filter _)]
  congr 1
  ext i
  simp

private theorem hit_singleton {n : ℕ} (B : Finset (Fin n)) (i : Fin n) :
    (encodeFinset B &&& 2 ^ i.val) ≠ 0 ↔ i ∈ B := by
  have he : encodeFinset ({i} : Finset (Fin n)) = 2 ^ i.val := by
    apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.mpr
    rw [encodeFinset_testBit, Nat.testBit_two_pow]
    simp [eq_comm]
  change ¬(encodeFinset B &&& 2 ^ i.val = 0) ↔ i ∈ B
  rw [← he, encode_disjoint_iff]
  simp

def encodeDegreeCaps {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (upper : ℕ) :
    List ProfileCap :=
  (List.finRange n).map fun v => ⟨2 ^ v.val, true, upper - H.degree v⟩

def encodeDegreeDemands {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (lower : ℕ) :
    List ProfileDemand :=
  (List.finRange n).map fun v => ⟨2 ^ v.val, lower - H.degree v⟩

def encodeAlphaCaps {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (sizes : List ℕ) (s : ℕ) : List ProfileCap :=
  sizes.flatMap fun q => (independentMasks H q).map fun m => ⟨m, false, s - 1 - q⟩

theorem glued_respects_caps {d n s : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (B : Fin d → Finset (Fin n)) (hI : (glued H B)ᶜ.CliqueFree s) (upper : ℕ)
    (hMax : ∀ v, (glued H B).degree (far v) ≤ upper)
    (sizes : List ℕ) :
    respectsCaps (encodeDegreeCaps H upper ++ encodeAlphaCaps H sizes s)
      (attachmentRows B) = true := by
  apply List.all_eq_true.mpr
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hu
    apply decide_eq_true
    have h := hMax v
    rw [degree_far] at h
    rw [attachmentRows_countP]
    convert (show (univ.filter (fun i => v ∈ B i)).card ≤ upper - H.degree v by omega) using 1
    congr 1
    ext i
    simp [hit_singleton]
  · obtain ⟨q, _, hm⟩ := List.mem_flatMap.mp hu
    obtain ⟨m, hM, rfl⟩ := List.mem_map.mp hm
    obtain ⟨T, hT, rfl⟩ := independentMasks_sound H q m hM
    let I := univ.filter (fun i => Disjoint (B i) T)
    have hc := attachment_avoiding_size H B hI T hT.isClique I
      (fun i hi => (Finset.mem_filter.mp hi).2)
    rw [hT.card_eq] at hc
    apply decide_eq_true
    rw [attachmentRows_countP]
    convert (show I.card ≤ s - 1 - q by omega) using 1
    congr 1
    ext i
    simp [I, encode_disjoint_iff]

theorem glued_meets_demands {d n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (B : Fin d → Finset (Fin n)) (lower : ℕ)
    (hMin : ∀ v, lower ≤ (glued H B).degree (far v)) :
    meetsDemands (encodeDegreeDemands H lower) (attachmentRows B) = true := by
  apply List.all_eq_true.mpr
  intro u hu
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hu
  apply decide_eq_true
  have h := hMin v
  rw [degree_far] at h
  unfold hitCount
  rw [attachmentRows_countP]
  convert (show lower - H.degree v ≤ (univ.filter (fun i => v ∈ B i)).card by omega) using 1
  congr 1
  ext i
  simp [hit_singleton]

end OMA.RamseyCatalogue

namespace OMA.RamseyCatalogue

open SimpleGraph Finset

structure AttachmentRelabeling (n d g : ℕ) where
  profile : List ℕ
  index : Fin g
  reindex : Fin (d + n + 1) → Fin (d + n + 1)

def testAttachmentRelabeling {n d g : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (K : Fin g → SimpleGraph (Fin (d + n + 1))) (decK : ∀ k, DecidableRel (K k).Adj)
    (label : AttachmentRelabeling n d g) : Bool :=
  letI := decK label.index
  checkGraphRelabel (numbered H (attachmentsFromRows d n label.profile))
    (K label.index) label.reindex

def attachmentOptions {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lower upper : ℕ) : List ℕ :=
  (List.range' (lower - 1) (upper - lower + 1)).flatMap (independentMasks H)

theorem glued_iso_from_profile_search {n d g : ℕ} (dpos : 0 < d)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (K : Fin g → SimpleGraph (Fin (d + n + 1))) (decK : ∀ k, DecidableRel (K k).Adj)
    (lower upper s : ℕ) (hLU : lower ≤ upper) (hL : 1 ≤ lower)
    (sizes : List ℕ) (opts : List ℕ) (caps : List ProfileCap) (demands : List ProfileDemand)
    (labels : List (AttachmentRelabeling n d g))
    (hOpts : opts = attachmentOptions H lower upper)
    (hCaps : caps = encodeDegreeCaps H upper ++ encodeAlphaCaps H sizes s)
    (hDemands : demands = encodeDegreeDemands H lower)
    (hSearch : ∀ first ∈ opts, (enumerateFrom opts caps demands (d - 1) first).all
      (fun p => decide (p ∈ labels.map AttachmentRelabeling.profile)) = true)
    (hLabels : labels.all (testAttachmentRelabeling H K decK) = true)
    (B : Fin d → Finset (Fin n))
    (hT : (glued H B).CliqueFree 3) (hI : (glued H B)ᶜ.CliqueFree s)
    (hMin : ∀ v, lower ≤ (glued H B).degree v) (hMax : ∀ v, (glued H B).degree v ≤ upper) :
    ∃ k, Nonempty (glued H B ≃g K k) := by
  let e := Tuple.sort (fun i => encodeFinset (B i))
  let B' := B ∘ e
  let f := relabel_near H B e
  have hT' : (glued H B').CliqueFree 3 := hT.comap f.toEmbedding.isContained
  have hI' : (glued H B')ᶜ.CliqueFree s :=
    hI.comap (SimpleGraph.Embedding.complEquiv f.toEmbedding).isContained
  have hM' (v : Vertex d n) : lower ≤ (glued H B').degree v := by
    rw [← f.degree_eq]
    exact hMin _
  have hX' (v : Vertex d n) : (glued H B').degree v ≤ upper := by
    rw [← f.degree_eq]
    exact hMax _
  have hInd i := attachment_independent H B' hT' i
  have hMemRow (a : ℕ) (ha : a ∈ attachmentRows B') : a ∈ opts := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    have hNearL := hM' (near i)
    have hNearU := hX' (near i)
    rw [degree_near] at hNearL hNearU
    rw [hOpts, attachmentOptions]
    apply List.mem_flatMap.mpr
    exact ⟨(B' i).card, List.mem_range'_1.mpr ⟨by omega, by omega⟩,
      independentMasks_complete H _ (hInd i)⟩
  have hLen : (attachmentRows B').length = d := by simp [attachmentRows]
  have hC : respectsCaps caps (attachmentRows B') = true := by
    rw [hCaps]
    exact glued_respects_caps H B' hI' upper (fun v => hX' (far v)) sizes
  have hD : meetsDemands demands (attachmentRows B') = true := by
    rw [hDemands]
    exact glued_meets_demands H B' lower (fun v => hM' (far v))
  have hSort : (attachmentRows B').Pairwise (· ≤ ·) :=
    attachmentRows_sorted B' (Tuple.monotone_sort (fun i : Fin d => encodeFinset (B i)))
  obtain ⟨a, xs, hr⟩ : ∃ a xs, attachmentRows B' = a :: xs := by
    cases h : attachmentRows B' with
    | nil =>
        rw [h] at hLen
        simp at hLen
        omega
    | cons a xs => exact ⟨a, xs, rfl⟩
  rw [hr] at hLen hC hD hSort
  have hLen' : xs.length = d - 1 := by simp only [List.length_cons] at hLen; omega
  have hEnum := mem_enumerateFrom opts caps demands a xs hSort
    (fun b hb => hMemRow b (by rw [hr]; exact List.mem_cons_of_mem _ hb)) hC hD
  rw [hLen'] at hEnum
  have hGood := List.all_eq_true.mp (hSearch a (hMemRow a (by rw [hr]; simp))) _ hEnum
  obtain ⟨label, hl, hcode⟩ := List.mem_map.mp (of_decide_eq_true hGood)
  have hCheck := List.all_eq_true.mp hLabels label hl
  let _ := decK label.index
  obtain ⟨iso⟩ := graph_iso_of_check
    (numbered H (attachmentsFromRows d n label.profile)) (K label.index) label.reindex hCheck
  have hCode : label.profile = attachmentRows B' := hcode.trans hr.symm
  rw [hCode, attachmentsFromRows_correct] at iso
  exact ⟨label.index, ⟨f.symm.trans ((number_glued H B').symm.trans iso)⟩⟩

end OMA.RamseyCatalogue

/-
A gluing enumeration of the smaller catalogues that feed the seventeen-vertex
classification. The reference graph rows came from Brendan McKay's Ramsey
graphs page (https://users.cecs.anu.edu.au/~bdm/data/), CC BY 4.0. All
precomputed masks, surviving profiles, and permutations are checked in Lean.
-/

namespace OMA.RamseyCatalogue

open SimpleGraph Finset

def singletonFive (_ : Fin 1) : SimpleGraph (Fin 5) := baseFive
instance singletonFiveAdj (i : Fin 1) : DecidableRel (singletonFive i).Adj := baseFiveAdj

def singletonThirteen (_ : Fin 1) : SimpleGraph (Fin 13) := base13
instance singletonThirteenAdj (i : Fin 1) : DecidableRel (singletonThirteen i).Adj := base13AdjDecidable

private structure ClassificationTrial (n d g : ℕ) where
  offerChunks : List (List ℕ)
  caps : List ProfileCap
  demands : List ProfileDemand
  labels : List (AttachmentRelabeling n d g)

private def ClassificationTrial.scan {n d g : ℕ} (T : ClassificationTrial n d g)
    (i : Fin T.offerChunks.length) : Bool :=
  (T.offerChunks[i.val]).all fun first =>
    (enumerateFrom T.offerChunks.flatten T.caps T.demands (d-1) first).all
      (fun p => decide (p ∈ T.labels.map AttachmentRelabeling.profile))

private theorem ClassificationTrial.checked {n d g : ℕ} (T : ClassificationTrial n d g)
    (dpos : 0 < d) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (K : Fin g → SimpleGraph (Fin (d + n + 1))) (decK : ∀ k, DecidableRel (K k).Adj)
    (lower upper s : ℕ) (hLU : lower ≤ upper) (hL : 1 ≤ lower)
    (sizes : List ℕ)
    (hOpts : T.offerChunks.flatten = attachmentOptions H lower upper)
    (hCaps : T.caps = encodeDegreeCaps H upper ++ encodeAlphaCaps H sizes s)
    (hDemands : T.demands = encodeDegreeDemands H lower)
    (hScanned : ∀ i, T.scan i = true)
    (hLabels : T.labels.all (testAttachmentRelabeling H K decK) = true)
    {B : Fin d → Finset (Fin n)} (hT : (glued H B).CliqueFree 3)
    (hI : (glued H B)ᶜ.CliqueFree s) (hMin : ∀ v, lower ≤ (glued H B).degree v)
    (hMax : ∀ v, (glued H B).degree v ≤ upper) :
    ∃ k, Nonempty (glued H B ≃g K k) := by
  refine glued_iso_from_profile_search dpos H K decK lower upper s hLU hL sizes
    T.offerChunks.flatten T.caps T.demands T.labels hOpts hCaps hDemands ?_ hLabels B hT hI hMin hMax
  intro first hF
  obtain ⟨xs, hs, hF⟩ := List.mem_flatten.mp hF
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
  exact List.all_eq_true.mp (hScanned ⟨i, hi⟩) first hF

def baseSevenRows : Fin 9 → Fin 7 → ℕ := ![
    ![0x28, 0x50, 0x60, 0x51, 0x2a, 0x15, 0xe],
    ![0x10, 0x24, 0x42, 0x60, 0x61, 0x1a, 0x1c],
    ![0x18, 0x24, 0x42, 0x61, 0x61, 0x1a, 0x1c],
    ![0x2, 0x41, 0x50, 0x60, 0x24, 0x18, 0xe],
    ![0x22, 0x41, 0x48, 0x24, 0x60, 0x19, 0x16],
    ![0x2, 0x1, 0x18, 0x24, 0x44, 0x48, 0x30],
    ![0x6, 0x21, 0x41, 0x30, 0x48, 0xa, 0x14],
    ![0x6, 0x21, 0x41, 0x30, 0x48, 0x4a, 0x34],
    ![0x6, 0x19, 0x61, 0x62, 0x62, 0x1c, 0x1c]
  ]

def baseSeven (idx : Fin 9) : SimpleGraph (Fin 7) :=
  graphFromRows (baseSevenRows idx)

instance baseSevenAdj (idx : Fin 9) : DecidableRel (baseSeven idx).Adj :=
  graphFromRowsAdj _

def baseEightRows : Fin 3 → Fin 8 → ℕ := ![
    ![0x90, 0x60, 0x58, 0xa4, 0x25, 0x1a, 0x86, 0x49],
    ![0x12, 0x81, 0x28, 0x44, 0x61, 0x94, 0x98, 0x62],
    ![0xe, 0x51, 0xa1, 0xc1, 0xa2, 0x54, 0x2a, 0x1c]
  ]

def baseEight (idx : Fin 3) : SimpleGraph (Fin 8) :=
  graphFromRows (baseEightRows idx)

instance baseEightAdj (idx : Fin 3) : DecidableRel (baseEight idx).Adj :=
  graphFromRowsAdj _

private def trial7At1 (k : Fin 1) : ClassificationTrial 5 1 9 :=
  match k.val with
  | 0 => ⟨[
      [0x0, 0x10, 0x8, 0x4, 0x2],
      [0x1, 0x14, 0x12, 0xa, 0x9],
      [0x5]
    ], [⟨0x1, true, 1⟩, ⟨0x2, true, 1⟩, ⟨0x4, true, 1⟩, ⟨0x8, true, 1⟩,
      ⟨0x10, true, 1⟩],
    [⟨0x1, 0⟩, ⟨0x2, 0⟩, ⟨0x4, 0⟩, ⟨0x8, 0⟩, ⟨0x10, 0⟩],
    [⟨[0x0], 5, ![0, 1, 2, 3, 5, 6, 4]⟩,
      ⟨[0x1], 3, ![0, 1, 6, 2, 4, 5, 3]⟩,
      ⟨[0x2], 3, ![0, 1, 2, 6, 3, 5, 4]⟩,
      ⟨[0x4], 3, ![0, 1, 4, 2, 6, 3, 5]⟩,
      ⟨[0x5], 1, ![0, 4, 5, 3, 6, 2, 1]⟩,
      ⟨[0x8], 3, ![0, 1, 4, 5, 3, 6, 2]⟩,
      ⟨[0x9], 1, ![0, 4, 5, 1, 2, 6, 3]⟩,
      ⟨[0xa], 1, ![0, 4, 1, 5, 3, 6, 2]⟩,
      ⟨[0x10], 3, ![0, 1, 2, 4, 5, 3, 6]⟩,
      ⟨[0x12], 1, ![0, 4, 3, 5, 1, 2, 6]⟩,
      ⟨[0x14], 1, ![0, 4, 1, 2, 6, 3, 5]⟩]⟩
  | _ => ⟨[], [], [], []⟩

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned7At1_0 (i : Fin (trial7At1 0).offerChunks.length) :
    (trial7At1 0).scan i = true := by
  change Fin 3 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
theorem classifyGlue7At1 (k : Fin 1) (B : Fin 1 → Finset (Fin 5))
    (ht : (glued (singletonFive k) B).CliqueFree 3) (hi : (glued (singletonFive k) B)ᶜ.CliqueFree 4)
    (hm : ∀ v, 1 ≤ (glued (singletonFive k) B).degree v)
    (hx : ∀ v, (glued (singletonFive k) B).degree v ≤ 3) :
    ∃ j : Fin 9, Nonempty (glued (singletonFive k) B ≃g baseSeven j) := by
  apply ClassificationTrial.checked (trial7At1 k) (by decide) (singletonFive k)
    baseSeven baseSevenAdj 1 3 4 (by decide) (by decide) [3]
  · fin_cases k
    decide +kernel
  · fin_cases k
    decide +kernel
  · fin_cases k
    decide +kernel
  · intro i
    fin_cases k
    · exact scanned7At1_0 i
  · fin_cases k
    decide +kernel
  · exact ht
  · exact hi
  · exact hm
  · exact hx

private def trial7At2 (k : Fin 3) : ClassificationTrial 4 2 9 :=
  match k.val with
  | 0 => ⟨[
      [0x8, 0x4, 0x2, 0x1, 0xa],
      [0x6, 0x9, 0x5]
    ], [⟨0x1, true, 2⟩, ⟨0x2, true, 2⟩, ⟨0x4, true, 2⟩, ⟨0x8, true, 2⟩,
      ⟨0xa, false, 1⟩, ⟨0x6, false, 1⟩, ⟨0x9, false, 1⟩, ⟨0x5, false, 1⟩],
    [⟨0x1, 1⟩, ⟨0x2, 1⟩, ⟨0x4, 1⟩, ⟨0x8, 1⟩],
    [⟨[0x5, 0xa], 4, ![4, 5, 6, 0, 1, 3, 2]⟩,
      ⟨[0x6, 0x9], 4, ![4, 5, 6, 1, 0, 3, 2]⟩]⟩
  | 1 => ⟨[
      [0x8, 0x4, 0x2, 0x1, 0xa],
      [0x9, 0x5]
    ], [⟨0x1, true, 2⟩, ⟨0x2, true, 1⟩, ⟨0x4, true, 1⟩, ⟨0x8, true, 2⟩,
      ⟨0xa, false, 1⟩, ⟨0x9, false, 1⟩, ⟨0x5, false, 1⟩],
    [⟨0x1, 1⟩, ⟨0x2, 0⟩, ⟨0x4, 0⟩, ⟨0x8, 1⟩],
    [⟨[0x1, 0x8], 6, ![0, 1, 2, 5, 3, 4, 6]⟩,
      ⟨[0x1, 0x9], 7, ![3, 4, 5, 6, 2, 0, 1]⟩,
      ⟨[0x1, 0xa], 7, ![1, 0, 5, 2, 6, 4, 3]⟩,
      ⟨[0x2, 0x9], 4, ![0, 1, 5, 4, 6, 2, 3]⟩,
      ⟨[0x4, 0x9], 4, ![0, 1, 5, 3, 2, 6, 4]⟩,
      ⟨[0x5, 0x8], 7, ![1, 5, 0, 3, 4, 6, 2]⟩,
      ⟨[0x5, 0x9], 0, ![0, 3, 5, 4, 1, 6, 2]⟩,
      ⟨[0x5, 0xa], 0, ![2, 5, 6, 0, 3, 4, 1]⟩,
      ⟨[0x8, 0x9], 7, ![3, 4, 5, 1, 0, 2, 6]⟩,
      ⟨[0x9, 0x9], 2, ![0, 3, 4, 5, 1, 2, 6]⟩,
      ⟨[0x9, 0xa], 0, ![0, 5, 3, 2, 6, 1, 4]⟩]⟩
  | 2 => ⟨[
      [0x8, 0x4, 0x2, 0x1, 0xa],
      [0x5]
    ], [⟨0x1, true, 1⟩, ⟨0x2, true, 1⟩, ⟨0x4, true, 1⟩, ⟨0x8, true, 1⟩,
      ⟨0xa, false, 1⟩, ⟨0x5, false, 1⟩],
    [⟨0x1, 0⟩, ⟨0x2, 0⟩, ⟨0x4, 0⟩, ⟨0x8, 0⟩],
    [⟨[0x1, 0x2], 7, ![0, 1, 2, 5, 6, 4, 3]⟩,
      ⟨[0x1, 0x8], 7, ![0, 1, 2, 5, 3, 4, 6]⟩,
      ⟨[0x1, 0xa], 2, ![1, 2, 5, 6, 3, 0, 4]⟩,
      ⟨[0x2, 0x4], 7, ![0, 1, 2, 3, 5, 6, 4]⟩,
      ⟨[0x2, 0x5], 2, ![1, 2, 5, 3, 6, 4, 0]⟩,
      ⟨[0x4, 0x8], 7, ![0, 1, 2, 4, 3, 5, 6]⟩,
      ⟨[0x4, 0xa], 2, ![1, 2, 5, 0, 3, 6, 4]⟩,
      ⟨[0x5, 0x8], 2, ![1, 5, 2, 3, 0, 4, 6]⟩,
      ⟨[0x5, 0xa], 8, ![0, 1, 2, 3, 5, 4, 6]⟩]⟩
  | _ => ⟨[], [], [], []⟩

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned7At2_0 (i : Fin (trial7At2 0).offerChunks.length) :
    (trial7At2 0).scan i = true := by
  change Fin 2 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned7At2_1 (i : Fin (trial7At2 1).offerChunks.length) :
    (trial7At2 1).scan i = true := by
  change Fin 2 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned7At2_2 (i : Fin (trial7At2 2).offerChunks.length) :
    (trial7At2 2).scan i = true := by
  change Fin 2 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
theorem classifyGlue7At2 (k : Fin 3) (B : Fin 2 → Finset (Fin 4))
    (ht : (glued (baseFour k) B).CliqueFree 3) (hi : (glued (baseFour k) B)ᶜ.CliqueFree 4)
    (hm : ∀ v, 2 ≤ (glued (baseFour k) B).degree v)
    (hx : ∀ v, (glued (baseFour k) B).degree v ≤ 3) :
    ∃ j : Fin 9, Nonempty (glued (baseFour k) B ≃g baseSeven j) := by
  apply ClassificationTrial.checked (trial7At2 k) (by decide) (baseFour k)
    baseSeven baseSevenAdj 2 3 4 (by decide) (by decide) [2, 3]
  · fin_cases k <;> decide +kernel
  · fin_cases k <;> decide +kernel
  · fin_cases k <;> decide +kernel
  · intro i
    fin_cases k
    · exact scanned7At2_0 i
    · exact scanned7At2_1 i
    · exact scanned7At2_2 i
  · fin_cases k <;> decide +kernel
  · exact ht
  · exact hi
  · exact hm
  · exact hx

private def trial8At2 (k : Fin 1) : ClassificationTrial 5 2 3 :=
  match k.val with
  | 0 => ⟨[
      [0x10, 0x8, 0x4, 0x2, 0x1],
      [0x14, 0x12, 0xa, 0x9, 0x5]
    ], [⟨0x1, true, 1⟩, ⟨0x2, true, 1⟩, ⟨0x4, true, 1⟩, ⟨0x8, true, 1⟩,
      ⟨0x10, true, 1⟩, ⟨0x14, false, 1⟩, ⟨0x12, false, 1⟩, ⟨0xa, false, 1⟩,
      ⟨0x9, false, 1⟩, ⟨0x5, false, 1⟩],
    [⟨0x1, 0⟩, ⟨0x2, 0⟩, ⟨0x4, 0⟩, ⟨0x8, 0⟩, ⟨0x10, 0⟩],
    [⟨[0x1, 0x12], 1, ![0, 1, 4, 7, 5, 2, 3, 6]⟩,
      ⟨[0x2, 0x5], 1, ![0, 1, 4, 6, 7, 5, 2, 3]⟩,
      ⟨[0x4, 0xa], 1, ![0, 1, 4, 2, 5, 7, 6, 3]⟩,
      ⟨[0x5, 0xa], 0, ![0, 7, 4, 6, 2, 3, 5, 1]⟩,
      ⟨[0x5, 0x12], 0, ![0, 4, 7, 2, 3, 5, 1, 6]⟩,
      ⟨[0x8, 0x14], 1, ![0, 1, 4, 2, 3, 6, 7, 5]⟩,
      ⟨[0x9, 0x10], 1, ![0, 4, 1, 5, 2, 3, 6, 7]⟩,
      ⟨[0x9, 0x12], 0, ![0, 4, 7, 2, 6, 1, 5, 3]⟩,
      ⟨[0x9, 0x14], 0, ![0, 4, 7, 5, 1, 6, 2, 3]⟩,
      ⟨[0xa, 0x14], 0, ![0, 7, 4, 1, 6, 2, 3, 5]⟩]⟩
  | _ => ⟨[], [], [], []⟩

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned8At2_0 (i : Fin (trial8At2 0).offerChunks.length) :
    (trial8At2 0).scan i = true := by
  change Fin 2 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
theorem classifyGlue8At2 (k : Fin 1) (B : Fin 2 → Finset (Fin 5))
    (ht : (glued (singletonFive k) B).CliqueFree 3) (hi : (glued (singletonFive k) B)ᶜ.CliqueFree 4)
    (hm : ∀ v, 2 ≤ (glued (singletonFive k) B).degree v)
    (hx : ∀ v, (glued (singletonFive k) B).degree v ≤ 3) :
    ∃ j : Fin 3, Nonempty (glued (singletonFive k) B ≃g baseEight j) := by
  apply ClassificationTrial.checked (trial8At2 k) (by decide) (singletonFive k)
    baseEight baseEightAdj 2 3 4 (by decide) (by decide) [2, 3]
  · fin_cases k
    decide +kernel
  · fin_cases k
    decide +kernel
  · fin_cases k
    decide +kernel
  · intro i
    fin_cases k
    · exact scanned8At2_0 i
  · fin_cases k
    decide +kernel
  · exact ht
  · exact hi
  · exact hm
  · exact hx

private def trial8At3 (k : Fin 3) : ClassificationTrial 4 3 3 :=
  match k.val with
  | 0 => ⟨[
      [0xa, 0x6, 0x9, 0x5]
    ], [⟨0x1, true, 2⟩, ⟨0x2, true, 2⟩, ⟨0x4, true, 2⟩, ⟨0x8, true, 2⟩,
      ⟨0x8, false, 2⟩, ⟨0x4, false, 2⟩, ⟨0x2, false, 2⟩, ⟨0x1, false, 2⟩,
      ⟨0xa, false, 1⟩, ⟨0x6, false, 1⟩, ⟨0x9, false, 1⟩, ⟨0x5, false, 1⟩],
    [⟨0x1, 2⟩, ⟨0x2, 2⟩, ⟨0x4, 2⟩, ⟨0x8, 2⟩],
    []⟩
  | 1 => ⟨[
      [0xa, 0x9, 0x5]
    ], [⟨0x1, true, 2⟩, ⟨0x2, true, 1⟩, ⟨0x4, true, 1⟩, ⟨0x8, true, 2⟩,
      ⟨0x8, false, 2⟩, ⟨0x4, false, 2⟩, ⟨0x2, false, 2⟩, ⟨0x1, false, 2⟩,
      ⟨0xa, false, 1⟩, ⟨0x9, false, 1⟩, ⟨0x5, false, 1⟩],
    [⟨0x1, 2⟩, ⟨0x2, 1⟩, ⟨0x4, 1⟩, ⟨0x8, 2⟩],
    [⟨[0x5, 0x9, 0xa], 2, ![0, 1, 3, 2, 6, 5, 4, 7]⟩]⟩
  | 2 => ⟨[
      [0xa, 0x5]
    ], [⟨0x1, true, 1⟩, ⟨0x2, true, 1⟩, ⟨0x4, true, 1⟩, ⟨0x8, true, 1⟩,
      ⟨0x8, false, 2⟩, ⟨0x4, false, 2⟩, ⟨0x2, false, 2⟩, ⟨0x1, false, 2⟩,
      ⟨0xa, false, 1⟩, ⟨0x5, false, 1⟩],
    [⟨0x1, 1⟩, ⟨0x2, 1⟩, ⟨0x4, 1⟩, ⟨0x8, 1⟩],
    []⟩
  | _ => ⟨[], [], [], []⟩

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned8At3_0 (i : Fin (trial8At3 0).offerChunks.length) :
    (trial8At3 0).scan i = true := by
  change Fin 1 at i
  fin_cases i
  decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned8At3_1 (i : Fin (trial8At3 1).offerChunks.length) :
    (trial8At3 1).scan i = true := by
  change Fin 1 at i
  fin_cases i
  decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned8At3_2 (i : Fin (trial8At3 2).offerChunks.length) :
    (trial8At3 2).scan i = true := by
  change Fin 1 at i
  fin_cases i
  decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
theorem classifyGlue8At3 (k : Fin 3) (B : Fin 3 → Finset (Fin 4))
    (ht : (glued (baseFour k) B).CliqueFree 3) (hi : (glued (baseFour k) B)ᶜ.CliqueFree 4)
    (hm : ∀ v, 3 ≤ (glued (baseFour k) B).degree v)
    (hx : ∀ v, (glued (baseFour k) B).degree v ≤ 3) :
    ∃ j : Fin 3, Nonempty (glued (baseFour k) B ≃g baseEight j) := by
  apply ClassificationTrial.checked (trial8At3 k) (by decide) (baseFour k)
    baseEight baseEightAdj 3 3 4 (by decide) (by decide) [1, 2, 3]
  · fin_cases k <;> decide +kernel
  · fin_cases k <;> decide +kernel
  · fin_cases k <;> decide +kernel
  · intro i
    fin_cases k
    · exact scanned8At3_0 i
    · exact scanned8At3_1 i
    · exact scanned8At3_2 i
  · fin_cases k <;> decide +kernel
  · exact ht
  · exact hi
  · exact hm
  · exact hx

private def trial12At3 (k : Fin 3) : ClassificationTrial 8 3 12 :=
  match k.val with
  | 0 => ⟨[
      [0xa0, 0x60, 0x90, 0x50, 0x48],
      [0x18, 0x84, 0x24, 0x82, 0x12],
      [0xa, 0x6, 0x41, 0x21, 0x9],
      [0x5, 0x3, 0x58, 0xa4, 0x92],
      [0x1a, 0x86, 0x61, 0x49, 0x25],
      [0xb, 0x7]
    ], [⟨0x1, true, 2⟩, ⟨0x2, true, 2⟩, ⟨0x4, true, 1⟩, ⟨0x8, true, 1⟩,
      ⟨0x10, true, 1⟩, ⟨0x20, true, 1⟩, ⟨0x40, true, 1⟩, ⟨0x80, true, 1⟩,
      ⟨0xa0, false, 2⟩, ⟨0x60, false, 2⟩, ⟨0x90, false, 2⟩, ⟨0x50, false, 2⟩,
      ⟨0x48, false, 2⟩, ⟨0x18, false, 2⟩, ⟨0x84, false, 2⟩, ⟨0x24, false, 2⟩,
      ⟨0x82, false, 2⟩, ⟨0x12, false, 2⟩, ⟨0xa, false, 2⟩, ⟨0x6, false, 2⟩,
      ⟨0x41, false, 2⟩, ⟨0x21, false, 2⟩, ⟨0x9, false, 2⟩, ⟨0x5, false, 2⟩,
      ⟨0x3, false, 2⟩, ⟨0x58, false, 1⟩, ⟨0xa4, false, 1⟩, ⟨0x92, false, 1⟩,
      ⟨0x1a, false, 1⟩, ⟨0x86, false, 1⟩, ⟨0x61, false, 1⟩, ⟨0x49, false, 1⟩,
      ⟨0x25, false, 1⟩, ⟨0xb, false, 1⟩, ⟨0x7, false, 1⟩],
    [⟨0x1, 1⟩, ⟨0x2, 1⟩, ⟨0x4, 0⟩, ⟨0x8, 0⟩, ⟨0x10, 0⟩, ⟨0x20, 0⟩, ⟨0x40, 0⟩, ⟨0x80, 0⟩],
    [⟨[0x3, 0x60, 0x92], 6, ![0, 1, 4, 11, 5, 10, 2, 3, 8, 9, 6, 7]⟩,
      ⟨[0x3, 0x61, 0x90], 6, ![0, 1, 11, 4, 10, 5, 2, 3, 6, 7, 8, 9]⟩,
      ⟨[0x3, 0x61, 0x92], 8, ![0, 1, 4, 5, 7, 6, 2, 3, 11, 10, 8, 9]⟩,
      ⟨[0x7, 0x12, 0x60], 4, ![0, 8, 2, 4, 5, 11, 10, 3, 7, 6, 9, 1]⟩,
      ⟨[0x7, 0x12, 0x61], 7, ![0, 5, 1, 4, 11, 7, 8, 3, 6, 9, 10, 2]⟩,
      ⟨[0x7, 0x1a, 0x60], 5, ![3, 10, 7, 2, 0, 4, 5, 8, 6, 9, 11, 1]⟩,
      ⟨[0x7, 0x1a, 0x61], 0, ![0, 8, 10, 6, 7, 3, 2, 11, 5, 4, 9, 1]⟩,
      ⟨[0x7, 0x41, 0x90], 4, ![0, 8, 2, 4, 11, 5, 10, 3, 9, 1, 7, 6]⟩,
      ⟨[0x7, 0x41, 0x92], 7, ![0, 5, 1, 4, 7, 11, 8, 3, 10, 2, 6, 9]⟩,
      ⟨[0x7, 0x49, 0x90], 5, ![3, 10, 7, 2, 4, 0, 5, 8, 11, 1, 6, 9]⟩,
      ⟨[0x7, 0x49, 0x92], 0, ![0, 8, 10, 6, 3, 7, 2, 11, 9, 1, 5, 4]⟩,
      ⟨[0x7, 0x60, 0x92], 3, ![2, 11, 3, 7, 0, 4, 6, 1, 5, 10, 8, 9]⟩,
      ⟨[0x7, 0x61, 0x90], 3, ![2, 11, 7, 3, 4, 0, 6, 1, 8, 9, 5, 10]⟩,
      ⟨[0x7, 0x61, 0x92], 1, ![0, 6, 10, 11, 2, 3, 7, 1, 4, 9, 5, 8]⟩,
      ⟨[0xb, 0x21, 0x90], 4, ![0, 8, 2, 4, 11, 5, 3, 10, 6, 7, 1, 9]⟩,
      ⟨[0xb, 0x21, 0x92], 7, ![0, 5, 1, 4, 7, 11, 3, 8, 9, 6, 2, 10]⟩,
      ⟨[0xb, 0x25, 0x90], 5, ![3, 10, 7, 2, 4, 0, 8, 5, 9, 6, 1, 11]⟩,
      ⟨[0xb, 0x25, 0x92], 0, ![0, 8, 10, 6, 3, 7, 11, 2, 4, 5, 1, 9]⟩,
      ⟨[0xb, 0x60, 0x82], 4, ![0, 8, 4, 2, 5, 11, 3, 10, 1, 9, 6, 7]⟩,
      ⟨[0xb, 0x60, 0x86], 5, ![3, 10, 2, 7, 0, 4, 8, 5, 1, 11, 9, 6]⟩,
      ⟨[0xb, 0x60, 0x92], 3, ![2, 11, 3, 7, 0, 4, 1, 6, 9, 8, 10, 5]⟩,
      ⟨[0xb, 0x61, 0x82], 7, ![0, 5, 4, 1, 11, 7, 3, 8, 2, 10, 9, 6]⟩,
      ⟨[0xb, 0x61, 0x86], 0, ![0, 8, 6, 10, 7, 3, 11, 2, 1, 9, 4, 5]⟩,
      ⟨[0xb, 0x61, 0x90], 3, ![2, 11, 7, 3, 4, 0, 1, 6, 10, 5, 9, 8]⟩,
      ⟨[0xb, 0x61, 0x92], 1, ![0, 6, 10, 11, 2, 3, 1, 7, 8, 5, 9, 4]⟩]⟩
  | 1 => ⟨[
      [0x60, 0x90, 0x88, 0x28, 0x18],
      [0x84, 0x44, 0x14, 0x42, 0x22],
      [0x12, 0xa, 0x6, 0x81, 0x41],
      [0x21, 0x9, 0x5, 0x98, 0x94],
      [0x62, 0x2a, 0x1a, 0x46, 0x16],
      [0x61, 0x89, 0x29, 0x85, 0x45]
    ], [⟨0x1, true, 2⟩, ⟨0x2, true, 2⟩, ⟨0x4, true, 2⟩, ⟨0x8, true, 2⟩,
      ⟨0x10, true, 1⟩, ⟨0x20, true, 1⟩, ⟨0x40, true, 1⟩, ⟨0x80, true, 1⟩,
      ⟨0x60, false, 2⟩, ⟨0x90, false, 2⟩, ⟨0x88, false, 2⟩, ⟨0x28, false, 2⟩,
      ⟨0x18, false, 2⟩, ⟨0x84, false, 2⟩, ⟨0x44, false, 2⟩, ⟨0x14, false, 2⟩,
      ⟨0x42, false, 2⟩, ⟨0x22, false, 2⟩, ⟨0x12, false, 2⟩, ⟨0xa, false, 2⟩,
      ⟨0x6, false, 2⟩, ⟨0x81, false, 2⟩, ⟨0x41, false, 2⟩, ⟨0x21, false, 2⟩,
      ⟨0x9, false, 2⟩, ⟨0x5, false, 2⟩, ⟨0x98, false, 1⟩, ⟨0x94, false, 1⟩,
      ⟨0x62, false, 1⟩, ⟨0x2a, false, 1⟩, ⟨0x1a, false, 1⟩, ⟨0x46, false, 1⟩,
      ⟨0x16, false, 1⟩, ⟨0x61, false, 1⟩, ⟨0x89, false, 1⟩, ⟨0x29, false, 1⟩,
      ⟨0x85, false, 1⟩, ⟨0x45, false, 1⟩],
    [⟨0x1, 1⟩, ⟨0x2, 1⟩, ⟨0x4, 1⟩, ⟨0x8, 1⟩, ⟨0x10, 0⟩, ⟨0x20, 0⟩, ⟨0x40, 0⟩, ⟨0x80, 0⟩],
    [⟨[0x5, 0x12, 0x29], 9, ![3, 7, 4, 8, 9, 5, 2, 0, 11, 10, 1, 6]⟩,
      ⟨[0x5, 0x16, 0x28], 9, ![3, 7, 8, 4, 2, 0, 9, 5, 10, 11, 6, 1]⟩,
      ⟨[0x5, 0x16, 0x29], 6, ![2, 3, 6, 8, 9, 4, 7, 5, 10, 11, 1, 0]⟩,
      ⟨[0x5, 0x16, 0x2a], 4, ![2, 0, 11, 7, 4, 6, 8, 5, 9, 10, 1, 3]⟩,
      ⟨[0x5, 0x1a, 0x29], 4, ![2, 0, 7, 11, 8, 5, 4, 6, 10, 9, 3, 1]⟩,
      ⟨[0x6, 0x28, 0x85], 9, ![3, 7, 4, 8, 0, 2, 9, 5, 1, 11, 6, 10]⟩,
      ⟨[0x6, 0x29, 0x85], 4, ![2, 0, 7, 11, 6, 4, 8, 5, 3, 10, 1, 9]⟩,
      ⟨[0x6, 0x2a, 0x81], 9, ![3, 7, 8, 4, 5, 9, 2, 0, 6, 10, 1, 11]⟩,
      ⟨[0x6, 0x2a, 0x85], 6, ![2, 3, 8, 6, 4, 9, 7, 5, 0, 11, 1, 10]⟩,
      ⟨[0x6, 0x2a, 0x89], 4, ![2, 0, 11, 7, 5, 8, 4, 6, 1, 9, 3, 10]⟩,
      ⟨[0x9, 0x12, 0x45], 9, ![3, 7, 4, 8, 9, 5, 0, 2, 11, 1, 10, 6]⟩,
      ⟨[0x9, 0x16, 0x45], 4, ![2, 0, 7, 11, 8, 5, 6, 4, 10, 3, 9, 1]⟩,
      ⟨[0x9, 0x1a, 0x44], 9, ![3, 7, 8, 4, 2, 0, 5, 9, 10, 6, 11, 1]⟩,
      ⟨[0x9, 0x1a, 0x45], 6, ![2, 3, 6, 8, 9, 4, 5, 7, 10, 1, 11, 0]⟩,
      ⟨[0x9, 0x1a, 0x46], 4, ![2, 0, 11, 7, 4, 6, 5, 8, 9, 1, 10, 3]⟩,
      ⟨[0xa, 0x44, 0x89], 9, ![3, 7, 4, 8, 0, 2, 5, 9, 1, 6, 11, 10]⟩,
      ⟨[0xa, 0x45, 0x89], 4, ![2, 0, 7, 11, 6, 4, 5, 8, 3, 1, 10, 9]⟩,
      ⟨[0xa, 0x46, 0x81], 9, ![3, 7, 8, 4, 5, 9, 0, 2, 6, 1, 10, 11]⟩,
      ⟨[0xa, 0x46, 0x85], 4, ![2, 0, 11, 7, 5, 8, 6, 4, 1, 3, 9, 10]⟩,
      ⟨[0xa, 0x46, 0x89], 6, ![2, 3, 8, 6, 4, 9, 5, 7, 0, 1, 11, 10]⟩,
      ⟨[0x12, 0x29, 0x45], 6, ![4, 0, 9, 6, 10, 1, 2, 3, 11, 8, 7, 5]⟩,
      ⟨[0x12, 0x29, 0x85], 4, ![4, 0, 9, 6, 11, 2, 3, 1, 8, 10, 5, 7]⟩,
      ⟨[0x12, 0x45, 0x89], 4, ![4, 0, 9, 6, 11, 2, 1, 3, 8, 5, 10, 7]⟩,
      ⟨[0x16, 0x28, 0x45], 4, ![4, 9, 0, 6, 3, 1, 11, 2, 10, 8, 7, 5]⟩,
      ⟨[0x16, 0x28, 0x85], 6, ![4, 9, 0, 6, 2, 3, 10, 1, 8, 11, 5, 7]⟩,
      ⟨[0x16, 0x29, 0x45], 3, ![0, 11, 9, 5, 7, 2, 6, 1, 4, 8, 10, 3]⟩,
      ⟨[0x16, 0x29, 0x85], 3, ![0, 9, 11, 5, 6, 1, 7, 2, 8, 4, 3, 10]⟩,
      ⟨[0x16, 0x2a, 0x45], 2, ![0, 4, 9, 8, 3, 10, 6, 1, 5, 7, 11, 2]⟩,
      ⟨[0x16, 0x2a, 0x81], 4, ![4, 6, 9, 0, 2, 11, 3, 1, 7, 10, 5, 8]⟩,
      ⟨[0x16, 0x2a, 0x85], 3, ![0, 5, 11, 9, 1, 6, 7, 2, 10, 4, 3, 8]⟩,
      ⟨[0x16, 0x2a, 0x89], 2, ![0, 8, 4, 9, 1, 6, 3, 10, 11, 5, 2, 7]⟩,
      ⟨[0x16, 0x45, 0x89], 2, ![0, 9, 4, 8, 6, 1, 10, 3, 7, 2, 5, 11]⟩,
      ⟨[0x1a, 0x29, 0x44], 4, ![4, 9, 6, 0, 3, 1, 2, 11, 10, 7, 8, 5]⟩,
      ⟨[0x1a, 0x29, 0x45], 3, ![0, 11, 5, 9, 7, 2, 1, 6, 4, 10, 8, 3]⟩,
      ⟨[0x1a, 0x29, 0x46], 2, ![0, 4, 8, 9, 3, 10, 1, 6, 5, 11, 7, 2]⟩,
      ⟨[0x1a, 0x29, 0x85], 2, ![0, 9, 4, 8, 6, 1, 3, 10, 7, 5, 2, 11]⟩,
      ⟨[0x1a, 0x44, 0x89], 6, ![4, 9, 0, 6, 2, 3, 1, 10, 8, 5, 11, 7]⟩,
      ⟨[0x1a, 0x45, 0x89], 3, ![0, 9, 11, 5, 6, 1, 2, 7, 8, 3, 4, 10]⟩,
      ⟨[0x1a, 0x46, 0x81], 4, ![4, 6, 9, 0, 2, 11, 1, 3, 7, 5, 10, 8]⟩,
      ⟨[0x1a, 0x46, 0x85], 2, ![0, 8, 4, 9, 1, 6, 10, 3, 11, 2, 5, 7]⟩,
      ⟨[0x1a, 0x46, 0x89], 3, ![0, 5, 11, 9, 1, 6, 2, 7, 10, 3, 4, 8]⟩,
      ⟨[0x28, 0x46, 0x85], 4, ![4, 0, 6, 9, 1, 3, 11, 2, 5, 8, 7, 10]⟩,
      ⟨[0x29, 0x46, 0x85], 2, ![0, 9, 8, 4, 10, 3, 6, 1, 2, 7, 11, 5]⟩,
      ⟨[0x2a, 0x44, 0x89], 4, ![4, 6, 0, 9, 1, 3, 2, 11, 5, 7, 8, 10]⟩,
      ⟨[0x2a, 0x45, 0x89], 2, ![0, 8, 9, 4, 10, 3, 1, 6, 2, 11, 7, 5]⟩,
      ⟨[0x2a, 0x46, 0x81], 6, ![4, 9, 6, 0, 1, 10, 2, 3, 5, 8, 7, 11]⟩,
      ⟨[0x2a, 0x46, 0x85], 3, ![0, 9, 5, 11, 2, 7, 6, 1, 3, 8, 10, 4]⟩,
      ⟨[0x2a, 0x46, 0x89], 3, ![0, 5, 9, 11, 2, 7, 1, 6, 3, 10, 8, 4]⟩]⟩
  | 2 => ⟨[
      [0xc0, 0xa0, 0x50, 0x28, 0x18],
      [0x44, 0x14, 0xc, 0x82, 0x22],
      [0xa, 0x6, 0x81, 0x41, 0x21],
      [0x11, 0x54, 0x1c, 0xa2, 0x2a],
      [0xe, 0xc1, 0xa1, 0x51]
    ], [⟨0x1, true, 1⟩, ⟨0x2, true, 1⟩, ⟨0x4, true, 1⟩, ⟨0x8, true, 1⟩,
      ⟨0x10, true, 1⟩, ⟨0x20, true, 1⟩, ⟨0x40, true, 1⟩, ⟨0x80, true, 1⟩,
      ⟨0xc0, false, 2⟩, ⟨0xa0, false, 2⟩, ⟨0x50, false, 2⟩, ⟨0x28, false, 2⟩,
      ⟨0x18, false, 2⟩, ⟨0x44, false, 2⟩, ⟨0x14, false, 2⟩, ⟨0xc, false, 2⟩,
      ⟨0x82, false, 2⟩, ⟨0x22, false, 2⟩, ⟨0xa, false, 2⟩, ⟨0x6, false, 2⟩,
      ⟨0x81, false, 2⟩, ⟨0x41, false, 2⟩, ⟨0x21, false, 2⟩, ⟨0x11, false, 2⟩,
      ⟨0x54, false, 1⟩, ⟨0x1c, false, 1⟩, ⟨0xa2, false, 1⟩, ⟨0x2a, false, 1⟩,
      ⟨0xe, false, 1⟩, ⟨0xc1, false, 1⟩, ⟨0xa1, false, 1⟩, ⟨0x51, false, 1⟩],
    [⟨0x1, 0⟩, ⟨0x2, 0⟩, ⟨0x4, 0⟩, ⟨0x8, 0⟩, ⟨0x10, 0⟩, ⟨0x20, 0⟩, ⟨0x40, 0⟩, ⟨0x80, 0⟩],
    []⟩
  | _ => ⟨[], [], [], []⟩

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned12At3_0 (i : Fin (trial12At3 0).offerChunks.length) :
    (trial12At3 0).scan i = true := by
  change Fin 6 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned12At3_1 (i : Fin (trial12At3 1).offerChunks.length) :
    (trial12At3 1).scan i = true := by
  change Fin 6 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned12At3_2 (i : Fin (trial12At3 2).offerChunks.length) :
    (trial12At3 2).scan i = true := by
  change Fin 5 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
theorem classifyGlue12At3 (k : Fin 3) (B : Fin 3 → Finset (Fin 8))
    (ht : (glued (baseEight k) B).CliqueFree 3) (hi : (glued (baseEight k) B)ᶜ.CliqueFree 5)
    (hm : ∀ v, 3 ≤ (glued (baseEight k) B).degree v)
    (hx : ∀ v, (glued (baseEight k) B).degree v ≤ 4) :
    ∃ j : Fin 12, Nonempty (glued (baseEight k) B ≃g base12 j) := by
  apply ClassificationTrial.checked (trial12At3 k) (by decide) (baseEight k)
    base12 base12Adj 3 4 5 (by decide) (by decide) [2, 3, 4]
  · fin_cases k <;> decide +kernel
  · fin_cases k <;> decide +kernel
  · fin_cases k <;> decide +kernel
  · intro i
    fin_cases k
    · exact scanned12At3_0 i
    · exact scanned12At3_1 i
    · exact scanned12At3_2 i
  · fin_cases k <;> decide +kernel
  · exact ht
  · exact hi
  · exact hm
  · exact hx

private def trial12At4 (k : Fin 9) : ClassificationTrial 7 4 12 :=
  match k.val with
  | 0 => ⟨[
      [0x2a, 0xe, 0x51, 0x15, 0x7]
    ], [⟨0x1, true, 2⟩, ⟨0x2, true, 2⟩, ⟨0x4, true, 2⟩, ⟨0x8, true, 1⟩,
      ⟨0x10, true, 1⟩, ⟨0x20, true, 1⟩, ⟨0x40, true, 1⟩, ⟨0x40, false, 3⟩,
      ⟨0x20, false, 3⟩, ⟨0x10, false, 3⟩, ⟨0x8, false, 3⟩, ⟨0x4, false, 3⟩,
      ⟨0x2, false, 3⟩, ⟨0x1, false, 3⟩, ⟨0x60, false, 2⟩, ⟨0x50, false, 2⟩,
      ⟨0x28, false, 2⟩, ⟨0x14, false, 2⟩, ⟨0xc, false, 2⟩, ⟨0x22, false, 2⟩,
      ⟨0xa, false, 2⟩, ⟨0x6, false, 2⟩, ⟨0x41, false, 2⟩, ⟨0x11, false, 2⟩,
      ⟨0x5, false, 2⟩, ⟨0x3, false, 2⟩, ⟨0x2a, false, 1⟩, ⟨0xe, false, 1⟩,
      ⟨0x51, false, 1⟩, ⟨0x15, false, 1⟩, ⟨0x7, false, 1⟩],
    [⟨0x1, 2⟩, ⟨0x2, 2⟩, ⟨0x4, 2⟩, ⟨0x8, 1⟩, ⟨0x10, 1⟩, ⟨0x20, 1⟩, ⟨0x40, 1⟩],
    []⟩
  | 1 => ⟨[
      [0x1c, 0x1a, 0x61, 0x25, 0xd],
      [0x43, 0xb]
    ], [⟨0x1, true, 3⟩, ⟨0x2, true, 2⟩, ⟨0x4, true, 2⟩, ⟨0x8, true, 2⟩,
      ⟨0x10, true, 1⟩, ⟨0x20, true, 1⟩, ⟨0x40, true, 1⟩, ⟨0x40, false, 3⟩,
      ⟨0x20, false, 3⟩, ⟨0x10, false, 3⟩, ⟨0x8, false, 3⟩, ⟨0x4, false, 3⟩,
      ⟨0x2, false, 3⟩, ⟨0x1, false, 3⟩, ⟨0x60, false, 2⟩, ⟨0x18, false, 2⟩,
      ⟨0x24, false, 2⟩, ⟨0x14, false, 2⟩, ⟨0xc, false, 2⟩, ⟨0x42, false, 2⟩,
      ⟨0x12, false, 2⟩, ⟨0xa, false, 2⟩, ⟨0x41, false, 2⟩, ⟨0x21, false, 2⟩,
      ⟨0x9, false, 2⟩, ⟨0x5, false, 2⟩, ⟨0x3, false, 2⟩, ⟨0x1c, false, 1⟩,
      ⟨0x1a, false, 1⟩, ⟨0x61, false, 1⟩, ⟨0x25, false, 1⟩, ⟨0xd, false, 1⟩,
      ⟨0x43, false, 1⟩, ⟨0xb, false, 1⟩],
    [⟨0x1, 3⟩, ⟨0x2, 2⟩, ⟨0x4, 2⟩, ⟨0x8, 2⟩, ⟨0x10, 1⟩, ⟨0x20, 1⟩, ⟨0x40, 1⟩],
    [⟨[0xb, 0x1c, 0x25, 0x43], 11, ![0, 3, 4, 1, 2, 11, 9, 10, 8, 5, 7, 6]⟩,
      ⟨[0xd, 0x1a, 0x25, 0x43], 11, ![0, 3, 4, 2, 1, 11, 10, 9, 8, 5, 6, 7]⟩]⟩
  | 2 => ⟨[
      [0x1c, 0x1a, 0x61, 0x25, 0x43]
    ], [⟨0x1, true, 2⟩, ⟨0x2, true, 2⟩, ⟨0x4, true, 2⟩, ⟨0x8, true, 1⟩,
      ⟨0x10, true, 1⟩, ⟨0x20, true, 1⟩, ⟨0x40, true, 1⟩, ⟨0x40, false, 3⟩,
      ⟨0x20, false, 3⟩, ⟨0x10, false, 3⟩, ⟨0x8, false, 3⟩, ⟨0x4, false, 3⟩,
      ⟨0x2, false, 3⟩, ⟨0x1, false, 3⟩, ⟨0x60, false, 2⟩, ⟨0x18, false, 2⟩,
      ⟨0x24, false, 2⟩, ⟨0x14, false, 2⟩, ⟨0xc, false, 2⟩, ⟨0x42, false, 2⟩,
      ⟨0x12, false, 2⟩, ⟨0xa, false, 2⟩, ⟨0x41, false, 2⟩, ⟨0x21, false, 2⟩,
      ⟨0x5, false, 2⟩, ⟨0x3, false, 2⟩, ⟨0x1c, false, 1⟩, ⟨0x1a, false, 1⟩,
      ⟨0x61, false, 1⟩, ⟨0x25, false, 1⟩, ⟨0x43, false, 1⟩],
    [⟨0x1, 2⟩, ⟨0x2, 2⟩, ⟨0x4, 2⟩, ⟨0x8, 1⟩, ⟨0x10, 1⟩, ⟨0x20, 1⟩, ⟨0x40, 1⟩],
    []⟩
  | 3 => ⟨[
      [0x1a, 0x26, 0xe, 0x61, 0x51],
      [0x19, 0x25, 0xd]
    ], [⟨0x1, true, 3⟩, ⟨0x2, true, 2⟩, ⟨0x4, true, 2⟩, ⟨0x8, true, 2⟩,
      ⟨0x10, true, 2⟩, ⟨0x20, true, 2⟩, ⟨0x40, true, 1⟩, ⟨0x40, false, 3⟩,
      ⟨0x20, false, 3⟩, ⟨0x10, false, 3⟩, ⟨0x8, false, 3⟩, ⟨0x4, false, 3⟩,
      ⟨0x2, false, 3⟩, ⟨0x1, false, 3⟩, ⟨0x60, false, 2⟩, ⟨0x50, false, 2⟩,
      ⟨0x18, false, 2⟩, ⟨0x24, false, 2⟩, ⟨0xc, false, 2⟩, ⟨0x22, false, 2⟩,
      ⟨0x12, false, 2⟩, ⟨0xa, false, 2⟩, ⟨0x6, false, 2⟩, ⟨0x41, false, 2⟩,
      ⟨0x21, false, 2⟩, ⟨0x11, false, 2⟩, ⟨0x9, false, 2⟩, ⟨0x5, false, 2⟩,
      ⟨0x1a, false, 1⟩, ⟨0x26, false, 1⟩, ⟨0xe, false, 1⟩, ⟨0x61, false, 1⟩,
      ⟨0x51, false, 1⟩, ⟨0x19, false, 1⟩, ⟨0x25, false, 1⟩, ⟨0xd, false, 1⟩],
    [⟨0x1, 3⟩, ⟨0x2, 2⟩, ⟨0x4, 2⟩, ⟨0x8, 2⟩, ⟨0x10, 2⟩, ⟨0x20, 2⟩, ⟨0x40, 1⟩],
    []⟩
  | 4 => ⟨[
      [0x1a, 0x26, 0x16, 0x49, 0x19],
      [0x15]
    ], [⟨0x1, true, 2⟩, ⟨0x2, true, 2⟩, ⟨0x4, true, 2⟩, ⟨0x8, true, 2⟩,
      ⟨0x10, true, 2⟩, ⟨0x20, true, 1⟩, ⟨0x40, true, 1⟩, ⟨0x40, false, 3⟩,
      ⟨0x20, false, 3⟩, ⟨0x10, false, 3⟩, ⟨0x8, false, 3⟩, ⟨0x4, false, 3⟩,
      ⟨0x2, false, 3⟩, ⟨0x1, false, 3⟩, ⟨0x60, false, 2⟩, ⟨0x48, false, 2⟩,
      ⟨0x18, false, 2⟩, ⟨0x24, false, 2⟩, ⟨0x14, false, 2⟩, ⟨0x22, false, 2⟩,
      ⟨0x12, false, 2⟩, ⟨0xa, false, 2⟩, ⟨0x6, false, 2⟩, ⟨0x41, false, 2⟩,
      ⟨0x11, false, 2⟩, ⟨0x9, false, 2⟩, ⟨0x5, false, 2⟩, ⟨0x1a, false, 1⟩,
      ⟨0x26, false, 1⟩, ⟨0x16, false, 1⟩, ⟨0x49, false, 1⟩, ⟨0x19, false, 1⟩,
      ⟨0x15, false, 1⟩],
    [⟨0x1, 2⟩, ⟨0x2, 2⟩, ⟨0x4, 2⟩, ⟨0x8, 2⟩, ⟨0x10, 2⟩, ⟨0x20, 1⟩, ⟨0x40, 1⟩],
    [⟨[0x15, 0x1a, 0x26, 0x49], 10, ![0, 1, 2, 3, 4, 10, 9, 7, 8, 11, 6, 5]⟩]⟩
  | 5 => ⟨[
      [0x32, 0x4a, 0x1a, 0x46, 0x26],
      [0x31, 0x49, 0x19, 0x45, 0x25]
    ], [⟨0x1, true, 3⟩, ⟨0x2, true, 3⟩, ⟨0x4, true, 2⟩, ⟨0x8, true, 2⟩,
      ⟨0x10, true, 2⟩, ⟨0x20, true, 2⟩, ⟨0x40, true, 2⟩, ⟨0x40, false, 3⟩,
      ⟨0x20, false, 3⟩, ⟨0x10, false, 3⟩, ⟨0x8, false, 3⟩, ⟨0x4, false, 3⟩,
      ⟨0x2, false, 3⟩, ⟨0x1, false, 3⟩, ⟨0x30, false, 2⟩, ⟨0x48, false, 2⟩,
      ⟨0x18, false, 2⟩, ⟨0x44, false, 2⟩, ⟨0x24, false, 2⟩, ⟨0x42, false, 2⟩,
      ⟨0x22, false, 2⟩, ⟨0x12, false, 2⟩, ⟨0xa, false, 2⟩, ⟨0x6, false, 2⟩,
      ⟨0x41, false, 2⟩, ⟨0x21, false, 2⟩, ⟨0x11, false, 2⟩, ⟨0x9, false, 2⟩,
      ⟨0x5, false, 2⟩, ⟨0x32, false, 1⟩, ⟨0x4a, false, 1⟩, ⟨0x1a, false, 1⟩,
      ⟨0x46, false, 1⟩, ⟨0x26, false, 1⟩, ⟨0x31, false, 1⟩, ⟨0x49, false, 1⟩,
      ⟨0x19, false, 1⟩, ⟨0x45, false, 1⟩, ⟨0x25, false, 1⟩],
    [⟨0x1, 3⟩, ⟨0x2, 3⟩, ⟨0x4, 2⟩, ⟨0x8, 2⟩, ⟨0x10, 2⟩, ⟨0x20, 2⟩, ⟨0x40, 2⟩],
    []⟩
  | 6 => ⟨[
      [0x34, 0x4a, 0x16, 0xe, 0x61],
      [0x31, 0x49]
    ], [⟨0x1, true, 2⟩, ⟨0x2, true, 2⟩, ⟨0x4, true, 2⟩, ⟨0x8, true, 2⟩,
      ⟨0x10, true, 2⟩, ⟨0x20, true, 2⟩, ⟨0x40, true, 2⟩, ⟨0x40, false, 3⟩,
      ⟨0x20, false, 3⟩, ⟨0x10, false, 3⟩, ⟨0x8, false, 3⟩, ⟨0x4, false, 3⟩,
      ⟨0x2, false, 3⟩, ⟨0x1, false, 3⟩, ⟨0x60, false, 2⟩, ⟨0x30, false, 2⟩,
      ⟨0x48, false, 2⟩, ⟨0x24, false, 2⟩, ⟨0x14, false, 2⟩, ⟨0xc, false, 2⟩,
      ⟨0x42, false, 2⟩, ⟨0x12, false, 2⟩, ⟨0xa, false, 2⟩, ⟨0x6, false, 2⟩,
      ⟨0x41, false, 2⟩, ⟨0x21, false, 2⟩, ⟨0x11, false, 2⟩, ⟨0x9, false, 2⟩,
      ⟨0x34, false, 1⟩, ⟨0x4a, false, 1⟩, ⟨0x16, false, 1⟩, ⟨0xe, false, 1⟩,
      ⟨0x61, false, 1⟩, ⟨0x31, false, 1⟩, ⟨0x49, false, 1⟩],
    [⟨0x1, 2⟩, ⟨0x2, 2⟩, ⟨0x4, 2⟩, ⟨0x8, 2⟩, ⟨0x10, 2⟩, ⟨0x20, 2⟩, ⟨0x40, 2⟩],
    []⟩
  | 7 => ⟨[
      [0x34, 0x4a, 0x16, 0xe, 0x31],
      [0x49]
    ], [⟨0x1, true, 2⟩, ⟨0x2, true, 2⟩, ⟨0x4, true, 2⟩, ⟨0x8, true, 2⟩,
      ⟨0x10, true, 2⟩, ⟨0x20, true, 1⟩, ⟨0x40, true, 1⟩, ⟨0x40, false, 3⟩,
      ⟨0x20, false, 3⟩, ⟨0x10, false, 3⟩, ⟨0x8, false, 3⟩, ⟨0x4, false, 3⟩,
      ⟨0x2, false, 3⟩, ⟨0x1, false, 3⟩, ⟨0x30, false, 2⟩, ⟨0x48, false, 2⟩,
      ⟨0x24, false, 2⟩, ⟨0x14, false, 2⟩, ⟨0xc, false, 2⟩, ⟨0x42, false, 2⟩,
      ⟨0x12, false, 2⟩, ⟨0xa, false, 2⟩, ⟨0x6, false, 2⟩, ⟨0x41, false, 2⟩,
      ⟨0x21, false, 2⟩, ⟨0x11, false, 2⟩, ⟨0x9, false, 2⟩, ⟨0x34, false, 1⟩,
      ⟨0x4a, false, 1⟩, ⟨0x16, false, 1⟩, ⟨0xe, false, 1⟩, ⟨0x31, false, 1⟩,
      ⟨0x49, false, 1⟩],
    [⟨0x1, 2⟩, ⟨0x2, 2⟩, ⟨0x4, 2⟩, ⟨0x8, 2⟩, ⟨0x10, 2⟩, ⟨0x20, 1⟩, ⟨0x40, 1⟩],
    [⟨[0xe, 0x16, 0x31, 0x49], 11, ![1, 0, 11, 7, 10, 9, 3, 2, 4, 5, 8, 6]⟩]⟩
  | 8 => ⟨[
      [0x1c, 0x62, 0x61, 0x19]
    ], [⟨0x1, true, 2⟩, ⟨0x2, true, 1⟩, ⟨0x4, true, 1⟩, ⟨0x8, true, 1⟩,
      ⟨0x10, true, 1⟩, ⟨0x20, true, 1⟩, ⟨0x40, true, 1⟩, ⟨0x40, false, 3⟩,
      ⟨0x20, false, 3⟩, ⟨0x10, false, 3⟩, ⟨0x8, false, 3⟩, ⟨0x4, false, 3⟩,
      ⟨0x2, false, 3⟩, ⟨0x1, false, 3⟩, ⟨0x60, false, 2⟩, ⟨0x18, false, 2⟩,
      ⟨0x14, false, 2⟩, ⟨0xc, false, 2⟩, ⟨0x42, false, 2⟩, ⟨0x22, false, 2⟩,
      ⟨0x6, false, 2⟩, ⟨0x41, false, 2⟩, ⟨0x21, false, 2⟩, ⟨0x11, false, 2⟩,
      ⟨0x9, false, 2⟩, ⟨0x1c, false, 1⟩, ⟨0x62, false, 1⟩, ⟨0x61, false, 1⟩,
      ⟨0x19, false, 1⟩],
    [⟨0x1, 2⟩, ⟨0x2, 1⟩, ⟨0x4, 1⟩, ⟨0x8, 1⟩, ⟨0x10, 1⟩, ⟨0x20, 1⟩, ⟨0x40, 1⟩],
    []⟩
  | _ => ⟨[], [], [], []⟩

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned12At4_0 (i : Fin (trial12At4 0).offerChunks.length) :
    (trial12At4 0).scan i = true := by
  change Fin 1 at i
  fin_cases i
  decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned12At4_1 (i : Fin (trial12At4 1).offerChunks.length) :
    (trial12At4 1).scan i = true := by
  change Fin 2 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned12At4_2 (i : Fin (trial12At4 2).offerChunks.length) :
    (trial12At4 2).scan i = true := by
  change Fin 1 at i
  fin_cases i
  decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned12At4_3 (i : Fin (trial12At4 3).offerChunks.length) :
    (trial12At4 3).scan i = true := by
  change Fin 2 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned12At4_4 (i : Fin (trial12At4 4).offerChunks.length) :
    (trial12At4 4).scan i = true := by
  change Fin 2 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned12At4_5 (i : Fin (trial12At4 5).offerChunks.length) :
    (trial12At4 5).scan i = true := by
  change Fin 2 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned12At4_6 (i : Fin (trial12At4 6).offerChunks.length) :
    (trial12At4 6).scan i = true := by
  change Fin 2 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned12At4_7 (i : Fin (trial12At4 7).offerChunks.length) :
    (trial12At4 7).scan i = true := by
  change Fin 2 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned12At4_8 (i : Fin (trial12At4 8).offerChunks.length) :
    (trial12At4 8).scan i = true := by
  change Fin 1 at i
  fin_cases i
  decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
theorem classifyGlue12At4 (k : Fin 9) (B : Fin 4 → Finset (Fin 7))
    (ht : (glued (baseSeven k) B).CliqueFree 3) (hi : (glued (baseSeven k) B)ᶜ.CliqueFree 5)
    (hm : ∀ v, 4 ≤ (glued (baseSeven k) B).degree v)
    (hx : ∀ v, (glued (baseSeven k) B).degree v ≤ 4) :
    ∃ j : Fin 12, Nonempty (glued (baseSeven k) B ≃g base12 j) := by
  apply ClassificationTrial.checked (trial12At4 k) (by decide) (baseSeven k)
    base12 base12Adj 4 4 5 (by decide) (by decide) [1, 2, 3, 4]
  · fin_cases k <;> decide +kernel
  · fin_cases k <;> decide +kernel
  · fin_cases k <;> decide +kernel
  · intro i
    fin_cases k
    · exact scanned12At4_0 i
    · exact scanned12At4_1 i
    · exact scanned12At4_2 i
    · exact scanned12At4_3 i
    · exact scanned12At4_4 i
    · exact scanned12At4_5 i
    · exact scanned12At4_6 i
    · exact scanned12At4_7 i
    · exact scanned12At4_8 i
  · fin_cases k <;> decide +kernel
  · exact ht
  · exact hi
  · exact hm
  · exact hx

private def trial13At4 (k : Fin 3) : ClassificationTrial 8 4 1 :=
  match k.val with
  | 0 => ⟨[
      [0x58, 0xa4, 0x92, 0x1a, 0x86],
      [0x61, 0x49, 0x25, 0xb, 0x7]
    ], [⟨0x1, true, 2⟩, ⟨0x2, true, 2⟩, ⟨0x4, true, 1⟩, ⟨0x8, true, 1⟩,
      ⟨0x10, true, 1⟩, ⟨0x20, true, 1⟩, ⟨0x40, true, 1⟩, ⟨0x80, true, 1⟩,
      ⟨0x80, false, 3⟩, ⟨0x40, false, 3⟩, ⟨0x20, false, 3⟩, ⟨0x10, false, 3⟩,
      ⟨0x8, false, 3⟩, ⟨0x4, false, 3⟩, ⟨0x2, false, 3⟩, ⟨0x1, false, 3⟩,
      ⟨0xa0, false, 2⟩, ⟨0x60, false, 2⟩, ⟨0x90, false, 2⟩, ⟨0x50, false, 2⟩,
      ⟨0x48, false, 2⟩, ⟨0x18, false, 2⟩, ⟨0x84, false, 2⟩, ⟨0x24, false, 2⟩,
      ⟨0x82, false, 2⟩, ⟨0x12, false, 2⟩, ⟨0xa, false, 2⟩, ⟨0x6, false, 2⟩,
      ⟨0x41, false, 2⟩, ⟨0x21, false, 2⟩, ⟨0x9, false, 2⟩, ⟨0x5, false, 2⟩,
      ⟨0x3, false, 2⟩, ⟨0x58, false, 1⟩, ⟨0xa4, false, 1⟩, ⟨0x92, false, 1⟩,
      ⟨0x1a, false, 1⟩, ⟨0x86, false, 1⟩, ⟨0x61, false, 1⟩, ⟨0x49, false, 1⟩,
      ⟨0x25, false, 1⟩, ⟨0xb, false, 1⟩, ⟨0x7, false, 1⟩],
    [⟨0x1, 2⟩, ⟨0x2, 2⟩, ⟨0x4, 1⟩, ⟨0x8, 1⟩, ⟨0x10, 1⟩, ⟨0x20, 1⟩, ⟨0x40, 1⟩, ⟨0x80, 1⟩],
    []⟩
  | 1 => ⟨[
      [0x98, 0x94, 0x62, 0x2a, 0x1a],
      [0x46, 0x16, 0x61, 0x89, 0x29],
      [0x85, 0x45]
    ], [⟨0x1, true, 2⟩, ⟨0x2, true, 2⟩, ⟨0x4, true, 2⟩, ⟨0x8, true, 2⟩,
      ⟨0x10, true, 1⟩, ⟨0x20, true, 1⟩, ⟨0x40, true, 1⟩, ⟨0x80, true, 1⟩,
      ⟨0x80, false, 3⟩, ⟨0x40, false, 3⟩, ⟨0x20, false, 3⟩, ⟨0x10, false, 3⟩,
      ⟨0x8, false, 3⟩, ⟨0x4, false, 3⟩, ⟨0x2, false, 3⟩, ⟨0x1, false, 3⟩,
      ⟨0x60, false, 2⟩, ⟨0x90, false, 2⟩, ⟨0x88, false, 2⟩, ⟨0x28, false, 2⟩,
      ⟨0x18, false, 2⟩, ⟨0x84, false, 2⟩, ⟨0x44, false, 2⟩, ⟨0x14, false, 2⟩,
      ⟨0x42, false, 2⟩, ⟨0x22, false, 2⟩, ⟨0x12, false, 2⟩, ⟨0xa, false, 2⟩,
      ⟨0x6, false, 2⟩, ⟨0x81, false, 2⟩, ⟨0x41, false, 2⟩, ⟨0x21, false, 2⟩,
      ⟨0x9, false, 2⟩, ⟨0x5, false, 2⟩, ⟨0x98, false, 1⟩, ⟨0x94, false, 1⟩,
      ⟨0x62, false, 1⟩, ⟨0x2a, false, 1⟩, ⟨0x1a, false, 1⟩, ⟨0x46, false, 1⟩,
      ⟨0x16, false, 1⟩, ⟨0x61, false, 1⟩, ⟨0x89, false, 1⟩, ⟨0x29, false, 1⟩,
      ⟨0x85, false, 1⟩, ⟨0x45, false, 1⟩],
    [⟨0x1, 2⟩, ⟨0x2, 2⟩, ⟨0x4, 2⟩, ⟨0x8, 2⟩, ⟨0x10, 1⟩, ⟨0x20, 1⟩, ⟨0x40, 1⟩, ⟨0x80, 1⟩],
    [⟨[0x16, 0x2a, 0x45, 0x89], 0, ![0, 1, 2, 4, 3, 11, 10, 9, 12, 5, 7, 6, 8]⟩,
      ⟨[0x1a, 0x29, 0x46, 0x85], 0, ![0, 1, 4, 2, 3, 11, 10, 12, 9, 5, 6, 7, 8]⟩]⟩
  | 2 => ⟨[
      [0x54, 0x1c, 0xa2, 0x2a, 0xe],
      [0xc1, 0xa1, 0x51]
    ], [⟨0x1, true, 1⟩, ⟨0x2, true, 1⟩, ⟨0x4, true, 1⟩, ⟨0x8, true, 1⟩,
      ⟨0x10, true, 1⟩, ⟨0x20, true, 1⟩, ⟨0x40, true, 1⟩, ⟨0x80, true, 1⟩,
      ⟨0x80, false, 3⟩, ⟨0x40, false, 3⟩, ⟨0x20, false, 3⟩, ⟨0x10, false, 3⟩,
      ⟨0x8, false, 3⟩, ⟨0x4, false, 3⟩, ⟨0x2, false, 3⟩, ⟨0x1, false, 3⟩,
      ⟨0xc0, false, 2⟩, ⟨0xa0, false, 2⟩, ⟨0x50, false, 2⟩, ⟨0x28, false, 2⟩,
      ⟨0x18, false, 2⟩, ⟨0x44, false, 2⟩, ⟨0x14, false, 2⟩, ⟨0xc, false, 2⟩,
      ⟨0x82, false, 2⟩, ⟨0x22, false, 2⟩, ⟨0xa, false, 2⟩, ⟨0x6, false, 2⟩,
      ⟨0x81, false, 2⟩, ⟨0x41, false, 2⟩, ⟨0x21, false, 2⟩, ⟨0x11, false, 2⟩,
      ⟨0x54, false, 1⟩, ⟨0x1c, false, 1⟩, ⟨0xa2, false, 1⟩, ⟨0x2a, false, 1⟩,
      ⟨0xe, false, 1⟩, ⟨0xc1, false, 1⟩, ⟨0xa1, false, 1⟩, ⟨0x51, false, 1⟩],
    [⟨0x1, 1⟩, ⟨0x2, 1⟩, ⟨0x4, 1⟩, ⟨0x8, 1⟩, ⟨0x10, 1⟩, ⟨0x20, 1⟩, ⟨0x40, 1⟩, ⟨0x80, 1⟩],
    []⟩
  | _ => ⟨[], [], [], []⟩

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned13At4_0 (i : Fin (trial13At4 0).offerChunks.length) :
    (trial13At4 0).scan i = true := by
  change Fin 2 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned13At4_1 (i : Fin (trial13At4 1).offerChunks.length) :
    (trial13At4 1).scan i = true := by
  change Fin 3 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
private theorem scanned13At4_2 (i : Fin (trial13At4 2).offerChunks.length) :
    (trial13At4 2).scan i = true := by
  change Fin 2 at i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 22000 in
set_option maxHeartbeats 80000000 in
theorem classifyGlue13At4 (k : Fin 3) (B : Fin 4 → Finset (Fin 8))
    (ht : (glued (baseEight k) B).CliqueFree 3) (hi : (glued (baseEight k) B)ᶜ.CliqueFree 5)
    (hm : ∀ v, 4 ≤ (glued (baseEight k) B).degree v)
    (hx : ∀ v, (glued (baseEight k) B).degree v ≤ 4) :
    ∃ j : Fin 1, Nonempty (glued (baseEight k) B ≃g singletonThirteen j) := by
  apply ClassificationTrial.checked (trial13At4 k) (by decide) (baseEight k)
    singletonThirteen singletonThirteenAdj 4 4 5 (by decide) (by decide) [1, 2, 3, 4]
  · fin_cases k <;> decide +kernel
  · fin_cases k <;> decide +kernel
  · fin_cases k <;> decide +kernel
  · intro i
    fin_cases k
    · exact scanned13At4_0 i
    · exact scanned13At4_1 i
    · exact scanned13At4_2 i
  · fin_cases k <;> decide +kernel
  · exact ht
  · exact hi
  · exact hm
  · exact hx

end OMA.RamseyCatalogue

namespace OMA.RamseyCatalogue

open SimpleGraph Finset
open scoped BigOperators

private theorem classify_from_root {N d n s g t : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (w : Fin N)
    (hw : G.degree w = d) (hn : Gᶜ.degree w = n)
    (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree (s + 1))
    (lower upper : ℕ) (hMin : ∀ v, lower ≤ G.degree v) (hMax : ∀ v, G.degree v ≤ upper)
    (source : Fin g → SimpleGraph (Fin n)) (decS : ∀ k, DecidableRel (source k).Adj)
    (target : Fin t → SimpleGraph (Fin N))
    (classifySource : ∀ H : SimpleGraph (Fin n), H.CliqueFree 3 → Hᶜ.CliqueFree s →
      ∃ k, Nonempty (H ≃g source k))
    (cert : ∀ (k : Fin g) (B : Fin d → Finset (Fin n)),
      letI := decS k
      (glued (source k) B).CliqueFree 3 → (glued (source k) B)ᶜ.CliqueFree (s + 1) →
      (∀ v, lower ≤ (glued (source k) B).degree v) →
      (∀ v, (glued (source k) B).degree v ≤ upper) →
      ∃ j, Nonempty (glued (source k) B ≃g target j)) :
    ∃ j, Nonempty (G ≃g target j) := by
  obtain ⟨H, B, hHT, hHI, ⟨e⟩⟩ := exists_gluing G w hw hn hT hI
  obtain ⟨k, ⟨f⟩⟩ := classifySource H hHT hHI
  let B' := fun i => (B i).map f.toEquiv.toEmbedding
  let iso : glued (source k) B' ≃g G := (relabel_far f B).symm.trans e
  let _ := decS k
  have hT' : (glued (source k) B').CliqueFree 3 := hT.comap iso.toEmbedding.isContained
  have hI' : (glued (source k) B')ᶜ.CliqueFree (s + 1) :=
    hI.comap (SimpleGraph.Embedding.complEquiv iso.toEmbedding).isContained
  have hL (v : Vertex d n) : lower ≤ (glued (source k) B').degree v := by
    rw [← iso.degree_eq]
    exact hMin _
  have hU (v : Vertex d n) : (glued (source k) B').degree v ≤ upper := by
    rw [← iso.degree_eq]
    exact hMax _
  obtain ⟨j, ⟨q⟩⟩ := cert k B' hT' hI' hL hU
  exact ⟨j, ⟨iso.symm.trans q⟩⟩

private theorem classifyFiveSingleton (G : SimpleGraph (Fin 5))
    (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 3) :
    ∃ k : Fin 1, Nonempty (G ≃g singletonFive k) :=
  ⟨0, completeFive G hT hI⟩

theorem completeSeven (G : SimpleGraph (Fin 7)) (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 4) :
    ∃ j : Fin 9, Nonempty (G ≃g baseSeven j) := by
  classical
  have hLo (v : Fin 7) : 1 ≤ G.degree v := by
    have h := anti_card_le_five G hT hI v
    rw [G.degree_compl, Fintype.card_fin] at h
    omega
  have hHi (v : Fin 7) : G.degree v ≤ 3 := by
    have h := degree_lt_independent G hT hI v
    omega
  by_cases hOne : ∃ w, G.degree w = 1
  · obtain ⟨w, hw⟩ := hOne
    have hAnti : Gᶜ.degree w = 5 := by rw [G.degree_compl, Fintype.card_fin, hw]
    exact classify_from_root G w (s := 3) hw hAnti hT hI 1 3 hLo hHi singletonFive
      singletonFiveAdj baseSeven classifyFiveSingleton classifyGlue7At1
  have hLo2 (v : Fin 7) : 2 ≤ G.degree v := by
    have hl := hLo v
    have hn : G.degree v ≠ 1 := fun he => hOne ⟨v, he⟩
    omega
  have hTwo : ∃ w, G.degree w = 2 := by
    by_contra! hh
    have hAll (v : Fin 7) : G.degree v = 3 := by
      have hl := hLo2 v
      have hu := hHi v
      have hn := hh v
      omega
    have hsum := G.sum_degrees_eq_twice_card_edges
    simp only [hAll, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    omega
  obtain ⟨w, hw⟩ := hTwo
  have hAnti : Gᶜ.degree w = 4 := by rw [G.degree_compl, Fintype.card_fin, hw]
  exact classify_from_root G w (s := 3) hw hAnti hT hI 2 3 hLo2 hHi baseFour
    baseFourAdj baseSeven completeFour classifyGlue7At2

theorem completeEight (G : SimpleGraph (Fin 8)) (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 4) :
    ∃ j : Fin 3, Nonempty (G ≃g baseEight j) := by
  classical
  have hLo (v : Fin 8) : 2 ≤ G.degree v := by
    have h := anti_card_le_five G hT hI v
    rw [G.degree_compl, Fintype.card_fin] at h
    omega
  have hHi (v : Fin 8) : G.degree v ≤ 3 := by
    have h := degree_lt_independent G hT hI v
    omega
  by_cases hTwo : ∃ w, G.degree w = 2
  · obtain ⟨w, hw⟩ := hTwo
    have hAnti : Gᶜ.degree w = 5 := by rw [G.degree_compl, Fintype.card_fin, hw]
    exact classify_from_root G w (s := 3) hw hAnti hT hI 2 3 hLo hHi singletonFive
      singletonFiveAdj baseEight classifyFiveSingleton classifyGlue8At2
  have hAll (v : Fin 8) : G.degree v = 3 := by
    have hl := hLo v
    have hu := hHi v
    have hn : G.degree v ≠ 2 := fun he => hTwo ⟨v, he⟩
    omega
  have hw := hAll 0
  have hAnti : Gᶜ.degree (0 : Fin 8) = 4 := by rw [G.degree_compl, Fintype.card_fin, hw]
  exact classify_from_root G 0 (s := 3) hw hAnti hT hI 3 3
    (fun v => (hAll v).ge) hHi baseFour baseFourAdj baseEight completeFour classifyGlue8At3

theorem completeTwelve (G : SimpleGraph (Fin 12)) (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 5) :
    ∃ j : Fin 12, Nonempty (G ≃g base12 j) := by
  classical
  have hLo (v : Fin 12) : 3 ≤ G.degree v := by
    have h := anti_card_le_eight G hT hI v
    rw [G.degree_compl, Fintype.card_fin] at h
    omega
  have hHi (v : Fin 12) : G.degree v ≤ 4 := by
    have h := degree_lt_independent G hT hI v
    omega
  by_cases hThree : ∃ w, G.degree w = 3
  · obtain ⟨w, hw⟩ := hThree
    have hAnti : Gᶜ.degree w = 8 := by rw [G.degree_compl, Fintype.card_fin, hw]
    exact classify_from_root G w (s := 4) hw hAnti hT hI 3 4 hLo hHi baseEight
      baseEightAdj base12 completeEight classifyGlue12At3
  have hAll (v : Fin 12) : G.degree v = 4 := by
    have hl := hLo v
    have hu := hHi v
    have hn : G.degree v ≠ 3 := fun he => hThree ⟨v, he⟩
    omega
  have hw := hAll 0
  have hAnti : Gᶜ.degree (0 : Fin 12) = 7 := by rw [G.degree_compl, Fintype.card_fin, hw]
  exact classify_from_root G 0 (s := 4) hw hAnti hT hI 4 4
    (fun v => (hAll v).ge) hHi baseSeven baseSevenAdj base12 completeSeven classifyGlue12At4

theorem completeThirteen (G : SimpleGraph (Fin 13)) (hT : G.CliqueFree 3)
    (hI : Gᶜ.CliqueFree 5) : Nonempty (G ≃g base13) := by
  classical
  have hLo (v : Fin 13) : 4 ≤ G.degree v := by
    have h := anti_card_le_eight G hT hI v
    rw [G.degree_compl, Fintype.card_fin] at h
    omega
  have hHi (v : Fin 13) : G.degree v ≤ 4 := by
    have h := degree_lt_independent G hT hI v
    omega
  have hw : G.degree (0 : Fin 13) = 4 := le_antisymm (hHi 0) (hLo 0)
  have hAnti : Gᶜ.degree (0 : Fin 13) = 8 := by rw [G.degree_compl, Fintype.card_fin, hw]
  obtain ⟨_, h⟩ := classify_from_root G 0 (s := 4) hw hAnti hT hI 4 4
    hLo hHi baseEight baseEightAdj singletonThirteen completeEight classifyGlue13At4
  exact h

end OMA.RamseyCatalogue

namespace OMA.Erdos151Ramsey37

open SimpleGraph Finset
open scoped BigOperators Classical
open OMA.RamseyCatalogue

theorem neighbor_root {d n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (B : Fin d → Finset (Fin n)) :
    (glued H B).neighborFinset none = (univ : Finset (Fin d)).map (near (n := n)) := by
  ext w
  rw [SimpleGraph.mem_neighborFinset]
  rcases w with _ | (i | j) <;> simp [glued, Finset.mem_map]

theorem attached_edge_count {d n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (B : Fin d → Finset (Fin n)) :
    (glued H B).edgeFinset.card = H.edgeFinset.card + d + ∑ i, (B i).card := by
  have hRoot : (glued H B).degree none = d := by
    rw [← card_neighborFinset_eq_degree, neighbor_root, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]
  have hNear (i : Fin d) : (glued H B).degree (some (Sum.inl i)) = 1 + (B i).card :=
    degree_near H B i
  have hFar (j : Fin n) : (glued H B).degree (some (Sum.inr j)) =
      H.degree j + (univ.filter (fun i => j ∈ B i)).card := degree_far H B j
  have hTouch : (∑ j : Fin n, (univ.filter (fun i => j ∈ B i)).card) = ∑ i, (B i).card := by
    calc
      _ = ∑ j : Fin n, ∑ i : Fin d, (if j ∈ B i then 1 else 0 : ℕ) :=
        Finset.sum_congr rfl (fun j _ => (Finset.sum_boole (R := ℕ) (fun i => j ∈ B i) _).symm)
      _ = ∑ i : Fin d, ∑ j : Fin n, (if j ∈ B i then 1 else 0 : ℕ) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have h : (univ.filter (fun j => j ∈ B i)) = B i := by
          ext j
          simp
        rw [Finset.sum_boole, h, Nat.cast_id]
  have hSum := (glued H B).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_option, Fintype.sum_sum_type, hRoot] at hSum
  simp only [hNear, hFar, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one, hTouch, H.sum_degrees_eq_twice_card_edges] at hSum
  omega

private theorem catalogue_edge_lower (k : Fin 7) : 40 ≤ (target17 k).edgeFinset.card := by
  fin_cases k <;> decide +kernel

private theorem lower_seventeen (H : SimpleGraph (Fin 17)) [DecidableRel H.Adj]
    (hT : H.CliqueFree 3) (hI : Hᶜ.CliqueFree 6) : 40 ≤ H.edgeFinset.card := by
  obtain ⟨k, ⟨e⟩⟩ := complete17_of_smaller completeThirteen completeTwelve H hT hI
  exact e.card_edgeFinset_eq ▸ catalogue_edge_lower k

private theorem local_edge_lower (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj]
    (hT : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 7) (v : Fin 23) (h5 : G.degree v = 5) :
    40 + (∑ w ∈ G.neighborFinset v, G.degree w) ≤ G.edgeFinset.card := by
  classical
  have hAnti : Gᶜ.degree v = 17 := by
    rw [G.degree_compl, Fintype.card_fin, h5]
  obtain ⟨H, B, hHT, hHI, e, he⟩ := exists_gluing_root G v (s := 6) h5 hAnti hT hI
  have hH := lower_seventeen H hHT hHI
  have hEdge := e.card_edgeFinset_eq
  rw [attached_edge_count] at hEdge
  have hMap : G.neighborFinset v =
      (univ : Finset (Fin 5)).map ((near (n := 17)).trans e.toEquiv.toEmbedding) := by
    ext w
    obtain ⟨w', rfl⟩ := e.toEquiv.surjective w
    rw [G.mem_neighborFinset, ← he]
    have hAdj : G.Adj (e none) (e.toEquiv w') ↔ (glued H B).Adj none w' := e.map_adj_iff
    rw [hAdj, ← SimpleGraph.mem_neighborFinset, neighbor_root]
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.trans_apply,
      Equiv.toEmbedding_apply]
    refine ⟨fun ⟨i, hi⟩ => ⟨i, ?_⟩, fun ⟨i, hi⟩ => ⟨i, ?_⟩⟩
    · exact congrArg e hi
    · exact e.injective hi
  have hSum : (∑ w ∈ G.neighborFinset v, G.degree w) = 5 + ∑ i, (B i).card := by
    rw [hMap, Finset.sum_map]
    calc
      _ = ∑ i : Fin 5, (1 + (B i).card) := by
        apply Finset.sum_congr rfl
        intro i _
        change G.degree (e (near i)) = 1 + (B i).card
        exact (e.degree_eq (near i)).trans (degree_near H B i)
      _ = _ := by simp [Finset.sum_add_distrib]
  omega

theorem degree_five_has_independent_seven (G : SimpleGraph (Fin 23)) (hT : G.CliqueFree 3)
    (hDegree : ∀ v : Fin 23, 5 ≤ (univ.filter (G.Adj v)).card ∧
      (univ.filter (G.Adj v)).card ≤ 6)
    (hFive : ∃ v : Fin 23, (univ.filter (G.Adj v)).card = 5) :
    ∃ s, G.IsNIndepSet 7 s := by
  classical
  by_contra hNone
  have hI : Gᶜ.CliqueFree 7 := fun s hs => hNone ⟨s, by simpa using hs⟩
  have hFilter (v : Fin 23) : G.degree v = (univ.filter (G.Adj v)).card := by
    rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  let L : Finset (Fin 23) := univ.filter (fun v => G.degree v = 5)
  have inL (v : Fin 23) : v ∈ L ↔ G.degree v = 5 := by simp [L]
  have hSum (S : Finset (Fin 23)) : (∑ v ∈ S, G.degree v) + (S ∩ L).card = 6 * S.card := by
    have hPoint (v : Fin 23) : G.degree v + (if v ∈ L then 1 else 0 : ℕ) = 6 := by
      have hBounds := hDegree v
      rw [← hFilter] at hBounds
      by_cases h : v ∈ L
      · simp [h, (inL v).mp h]
      · have hne := mt (inL v).mpr h
        rw [if_neg h]
        omega
    calc
      _ = ∑ v ∈ S, (G.degree v + (if v ∈ L then 1 else 0 : ℕ)) := by
        have h : S.filter (fun v => v ∈ L) = S ∩ L := by
          ext v
          simp
        rw [Finset.sum_add_distrib, Finset.sum_boole, h, Nat.cast_id]
      _ = 6 * S.card := by simp [hPoint, smul_eq_mul, Nat.mul_comm]
  have hGlobal := hSum (univ : Finset (Fin 23))
  rw [G.sum_degrees_eq_twice_card_edges, Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at hGlobal
  have hMany {v : Fin 23} (hv : v ∈ L) : L.card + 2 ≤ 2 * ((G.neighborFinset v) ∩ L).card := by
    have hv5 := (inL v).mp hv
    have hLocal := local_edge_lower G hT hI v hv5
    have hN := hSum (G.neighborFinset v)
    rw [G.card_neighborFinset_eq_degree, hv5] at hN
    omega
  obtain ⟨v, hv⟩ := hFive
  have hvL := (inL v).mpr ((hFilter v).trans hv)
  have hNbr := hMany hvL
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset v ∩ L).card by omega)
  have huN := (Finset.mem_inter.mp hu).1
  have huL := (Finset.mem_inter.mp hu).2
  have hvu := (G.mem_neighborFinset v u).mp huN
  have hDisj : Disjoint (G.neighborFinset v ∩ L) (G.neighborFinset u ∩ L) := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    have hvw := (G.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).1
    have huw := (G.mem_neighborFinset u w).mp (Finset.mem_inter.mp hw').1
    exact G.isIndepSet_neighborSet_of_triangleFree hT v hvu hvw huw.ne huw
  have hSub : (G.neighborFinset v ∩ L) ∪ (G.neighborFinset u ∩ L) ⊆ L :=
    Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
  have hCard := Finset.card_le_card hSub
  rw [Finset.card_union_of_disjoint hDisj] at hCard
  have hOther := hMany huL
  omega

end OMA.Erdos151Ramsey37

theorem OMA.solution : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H2_R1_H1_R1.H2 :=
  OMA.Erdos151Ramsey37.degree_five_has_independent_seven
