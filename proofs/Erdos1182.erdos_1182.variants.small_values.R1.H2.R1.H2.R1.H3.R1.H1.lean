import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1_H3_R1

-- Credit: @Ehdunhackme

-- allocation normalization and exact arithmetic classifier
noncomputable section
namespace Problem14.H3
open SimpleGraph Finset

variable {I V W : Type*} [Fintype I] [DecidableEq I]
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Cardinalities of the color fibers; their sum is the original vertex count. -/
def fiberSize (color : V → I) (i : I) : ℕ := Fintype.card {v // color v = i}

/-- Normalize each fiber independently, keeping its color as the sigma index. -/
def fiberEquiv (color : V → I) : V ≃ Σ i : I, Fin (fiberSize color i) :=
  (Equiv.sigmaFiberEquiv color).symm.trans
    (Equiv.sigmaCongrRight fun i => Fintype.equivFin {v // color v = i})

@[simp] theorem fiberEquiv_color (color : V → I) (v : V) :
    (fiberEquiv color v).1 = color v := rfl

lemma sum_fiberSize (color : V → I) : ∑ i, fiberSize color i = Fintype.card V := by
  have hc := Fintype.card_congr (fiberEquiv color)
  simpa only [Fintype.card_sigma, Fintype.card_fin] using hc.symm

lemma fiberSize_le (color : W → I) (f : V ↪ W) (i : I) :
    fiberSize (color ∘ f) i ≤ fiberSize color i := by
  let g : {v : V // color (f v) = i} → {w : W // color w = i} :=
    fun v => ⟨f v.val, v.property⟩
  apply Fintype.card_le_of_injective g
  intro v w h
  exact Subtype.ext (f.injective (congrArg Subtype.val h))

@[simp] lemma fiberSize_sigma (a : I → ℕ) (i : I) :
    fiberSize (fun v : Σ j : I, Fin (a j) => v.1) i = a i := by
  unfold fiberSize
  simpa only [Fintype.card_fin] using Fintype.card_congr (Equiv.sigmaSubtype (β := fun j => Fin (a j)) i)

/-- The complement of a blow-up of the color graph, on canonical fiber labels. -/
def canonical (L : SimpleGraph I) (a : I → ℕ) : SimpleGraph (Σ i : I, Fin (a i)) :=
  (L.comap (fun v => v.1))ᶜ

instance (L : SimpleGraph I) [DecidableRel L.Adj] (a : I → ℕ) :
    DecidableRel (canonical L a).Adj := by
  unfold canonical
  infer_instance

/-- Every placement in a colored host is isomorphic to its fiber-count graph. -/
def placementIso (L : SimpleGraph I) (color : W → I) (f : V ↪ W) :
    ((L.comap color)ᶜ.comap f) ≃g canonical L (fiberSize (color ∘ f)) where
  toEquiv := fiberEquiv (color ∘ f)
  map_rel_iff' := by
    intro v w
    simp only [canonical, compl_adj, comap_adj, fiberEquiv_color,
      (fiberEquiv (color ∘ f)).injective.ne_iff, f.injective.ne_iff, Function.comp_apply]

/-- A graph embedded in the host complement becomes a subgraph of the canonical allocation. -/
lemma normalized_subgraph (L : SimpleGraph I) (color : W → I) (f : V ↪ W)
    (G : SimpleGraph V) (hG : G ≤ (L.comap color)ᶜ.comap f) :
    G.map (fiberEquiv (color ∘ f)).toEmbedding ≤ canonical L (fiberSize (color ∘ f)) := by
  rw [map_le_iff_le_comap]
  intro v w h
  exact (placementIso L color f).map_rel_iff.mpr (hG h)

lemma normalized_edge_bound (L : SimpleGraph I) [DecidableRel L.Adj]
    (color : W → I) (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G ≤ (L.comap color)ᶜ.comap f) :
    G.edgeFinset.card ≤ (canonical L (fiberSize (color ∘ f))).edgeFinset.card := by
  classical
  have h := card_le_card (edgeFinset_mono (normalized_subgraph L color f G hG))
  rwa [card_edgeFinset_map] at h

/-- Allocation classifiers are supplied as ordinary proved hypotheses, so finite lists and
    dihedral reductions can be inserted without enumerating vertex images. -/
theorem normalize_with_classifier (L : SimpleGraph I) [DecidableRel L.Adj]
    (color : W → I) (capacity : I → ℕ)
    (hcapacity : ∀ i, fiberSize color i ≤ capacity i)
    (q : ℕ) (Allowed : (I → ℕ) → Prop)
    (classify : ∀ a : I → ℕ, (∑ i, a i) = Fintype.card V →
      (∀ i, a i ≤ capacity i) → q ≤ (canonical L a).edgeFinset.card → Allowed a)
    (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G ≤ (L.comap color)ᶜ.comap f) (hcard : q ≤ G.edgeFinset.card) :
    ∃ a : I → ℕ, Allowed a ∧ ∃ H : SimpleGraph (Σ i : I, Fin (a i)),
      H ≤ canonical L a ∧ Nonempty (G ≃g H) := by
  let a := fiberSize (color ∘ f)
  have ha : Allowed a := classify a (sum_fiberSize _) (fun i =>
    (fiberSize_le color f i).trans (hcapacity i))
    (hcard.trans (normalized_edge_bound L color f G hG))
  refine ⟨a, ha, G.map (fiberEquiv (color ∘ f)).toEmbedding,
    normalized_subgraph L color f G hG, ?_⟩
  exact ⟨SimpleGraph.Iso.map (fiberEquiv (color ∘ f)) G⟩


/-- Permuting colors along an automorphism of the base graph relabels allocations. -/
def allocationEquiv (a b : I → ℕ) (e : I ≃ I) (h : ∀ i, a i = b (e i)) :
    (Σ i : I, Fin (a i)) ≃ Σ i : I, Fin (b i) :=
  Equiv.sigmaCongr e (fun i => finCongr (h i))

@[simp] lemma allocationEquiv_color (a b : I → ℕ) (e : I ≃ I)
    (h : ∀ i, a i = b (e i)) (v : Σ i : I, Fin (a i)) :
    (allocationEquiv a b e h v).1 = e v.1 := rfl

def allocationIso (L : SimpleGraph I) (a b : I → ℕ) (e : L ≃g L)
    (h : ∀ i, a i = b (e i)) : canonical L a ≃g canonical L b where
  toEquiv := allocationEquiv a b e.toEquiv h
  map_rel_iff' := by
    intro v w
    simp only [canonical, compl_adj, comap_adj, allocationEquiv_color,
      (allocationEquiv a b e.toEquiv h).injective.ne_iff, RelIso.coe_fn_toEquiv, e.map_rel_iff]


/-- Native certificates use contiguous blocks, the explicit ordering of finSigmaFinEquiv. -/
def flatCanonical (L : SimpleGraph (Fin 5)) (a : Fin 5 → ℕ) :
    SimpleGraph (Fin (∑ i, a i)) :=
  (L.comap (fun v => ((finSigmaFinEquiv (n := a)).symm v).1))ᶜ

instance (L : SimpleGraph (Fin 5)) [DecidableRel L.Adj] (a : Fin 5 → ℕ) :
    DecidableRel (flatCanonical L a).Adj := by
  unfold flatCanonical
  infer_instance

def flattenIso (L : SimpleGraph (Fin 5)) (a : Fin 5 → ℕ) :
    canonical L a ≃g flatCanonical L a where
  toEquiv := finSigmaFinEquiv
  map_rel_iff' := by
    intro v w
    simp only [canonical, flatCanonical, compl_adj, comap_adj,
      Equiv.symm_apply_apply, (finSigmaFinEquiv (n := a)).injective.ne_iff]

end Problem14.H3


namespace Problem14.H3
open SimpleGraph Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Degree in a blow-up is the sum of the sizes of neighboring color fibers. -/
lemma blowup_degree (L : SimpleGraph I) [DecidableRel L.Adj] (a : I → ℕ)
    (v : Σ i : I, Fin (a i)) :
    (L.comap (fun w : Σ i : I, Fin (a i) => w.1)).degree v =
      ∑ j, if L.Adj v.1 j then a j else 0 := by
  let B := L.comap (fun w : Σ i : I, Fin (a i) => w.1)
  have e : B.neighborSet v ≃ Σ j : {j // L.Adj v.1 j}, Fin (a j.val) :=
    Equiv.subtypeSigmaEquiv (fun j => Fin (a j)) (L.Adj v.1)
  rw [← B.card_neighborSet_eq_degree v, Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← Finset.sum_subtype (univ.filter (L.Adj v.1)) (by simp) a, Finset.sum_filter]

lemma blowup_degree_sum (L : SimpleGraph I) [DecidableRel L.Adj] (a : I → ℕ) :
    (∑ v : Σ i : I, Fin (a i),
      (L.comap (fun w : Σ i : I, Fin (a i) => w.1)).degree v) =
    ∑ i, a i * ∑ j, if L.Adj i j then a j else 0 := by
  simp only [blowup_degree, Fintype.sum_sigma]
  change (∑ i, ∑ _ : Fin (a i), ∑ j, if L.Adj i j then a j else 0) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]

/-- Five cyclic colors; blow-ups have independent parts and complete consecutive pairs. -/
def cycle5 : SimpleGraph (Fin 5) where
  Adj i j := j = i + 1 ∨ i = j + 1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel cycle5.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

lemma cycle5_arithmetic (a : Fin 5 → ℕ) :
    (∑ i, a i * ∑ j, if cycle5.Adj i j then a j else 0) =
      2 * ∑ i, a i * a (i + 1) := by
  simp [Fin.sum_univ_succ, cycle5]
  ring

lemma cycle5_blowup_edges (a : Fin 5 → ℕ) :
    (cycle5.comap (fun w : Σ i : Fin 5, Fin (a i) => w.1)).edgeFinset.card =
      ∑ i, a i * a (i + 1) := by
  have hh := (cycle5.comap (fun w : Σ i : Fin 5, Fin (a i) => w.1)).sum_degrees_eq_twice_card_edges
  rw [blowup_degree_sum, cycle5_arithmetic] at hh
  omega

lemma complement_edge_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 - G.edgeFinset.card := by
  have he : Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset \ G.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ i j =>
      simp only [mem_edgeFinset, mem_edgeSet, compl_adj, mem_sdiff, top_adj]
  rw [he, card_sdiff_of_subset (edgeFinset_mono le_top),
    card_edgeFinset_top_eq_card_choose_two]

lemma cycle5_canonical_edges (a : Fin 5 → ℕ) :
    (canonical cycle5 a).edgeFinset.card =
      (∑ i, a i).choose 2 - ∑ i, a i * a (i + 1) := by
  change ((cycle5.comap (fun w : Σ i : Fin 5, Fin (a i) => w.1))ᶜ).edgeFinset.card = _
  rw [complement_edge_count, cycle5_blowup_edges]
  simp only [Fintype.card_sigma, Fintype.card_fin]

/-- The sole numerical screening required after normalizing any vertex placement. -/
theorem allocation_constraints {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (color : W → Fin 5) (capacity : Fin 5 → ℕ)
    (hcapacity : ∀ i, fiberSize color i ≤ capacity i)
    (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G ≤ (cycle5.comap color)ᶜ.comap f) (q : ℕ) (hcard : q ≤ G.edgeFinset.card) :
    let a := fiberSize (color ∘ f)
    (∑ i, a i) = Fintype.card V ∧ (∀ i, a i ≤ capacity i) ∧
      q ≤ (Fintype.card V).choose 2 - ∑ i, a i * a (i + 1) := by
  dsimp only
  refine ⟨sum_fiberSize _, (fun i => (fiberSize_le color f i).trans (hcapacity i)), ?_⟩
  have h := hcard.trans (normalized_edge_bound cycle5 color f G hG)
  rwa [cycle5_canonical_edges, sum_fiberSize] at h

end Problem14.H3


namespace Problem14.H3
open SimpleGraph Finset

def d5Map (t : Fin 10) (i : Fin 5) : Fin 5 :=
  let r : Fin 5 := ⟨t.val % 5, Nat.mod_lt _ (by decide)⟩
  if t.val < 5 then r + i else r - i

def d5Inv (t : Fin 10) (i : Fin 5) : Fin 5 :=
  let r : Fin 5 := ⟨t.val % 5, Nat.mod_lt _ (by decide)⟩
  if t.val < 5 then i - r else r - i

lemma d5_inverse_left : ∀ t : Fin 10, ∀ i : Fin 5, d5Inv t (d5Map t i) = i := by
  decide +kernel
lemma d5_inverse_right : ∀ t : Fin 10, ∀ i : Fin 5, d5Map t (d5Inv t i) = i := by
  decide +kernel

def d5Equiv (t : Fin 10) : Fin 5 ≃ Fin 5 where
  toFun := d5Map t
  invFun := d5Inv t
  left_inv := d5_inverse_left t
  right_inv := d5_inverse_right t

lemma d5_adjacency : ∀ t : Fin 10, ∀ i j : Fin 5,
    cycle5.Adj (d5Map t i) (d5Map t j) ↔ cycle5.Adj i j := by
  decide +kernel

def d5Iso (t : Fin 10) : cycle5 ≃g cycle5 where
  toEquiv := d5Equiv t
  map_rel_iff' := by
    intro i j
    exact d5_adjacency t i j

def reindexAllocation (a : Fin 5 → Fin 6) (t : Fin 10) : Fin 5 → Fin 6 :=
  fun i => a ((d5Equiv t).symm i)

/-- A finite arithmetic certificate over only 6^5 count vectors. -/
def AllocationCheck (n q : ℕ) (capacity : Fin 5 → ℕ)
    (allowed : Finset (Fin 5 → Fin 6)) : Prop :=
  ∀ a : Fin 5 → Fin 6, (∑ i, (a i).val) = n →
    (∀ i, (a i).val ≤ capacity i) →
    q ≤ n.choose 2 - ∑ i, (a i).val * (a (i+1)).val →
    ∃ t : Fin 10, reindexAllocation a t ∈ allowed

instance (n q : ℕ) (capacity : Fin 5 → ℕ) (allowed : Finset (Fin 5 → Fin 6)) :
    Decidable (AllocationCheck n q capacity allowed) := by
  unfold AllocationCheck
  infer_instance

lemma allocationCheck_sound (n q : ℕ) (capacity : Fin 5 → ℕ)
    (allowed : Finset (Fin 5 → Fin 6))
    (hcap : ∀ i, capacity i ≤ 5) (hc : AllocationCheck n q capacity allowed)
    (a : Fin 5 → ℕ) (hsum : (∑ i, a i) = n)
    (hsize : ∀ i, a i ≤ capacity i)
    (hedge : q ≤ (canonical cycle5 a).edgeFinset.card) :
    ∃ b ∈ allowed, Nonempty (canonical cycle5 a ≃g canonical cycle5 (fun i => (b i).val)) := by
  let af : Fin 5 → Fin 6 := fun i => ⟨a i, Nat.lt_succ_of_le ((hsize i).trans (hcap i))⟩
  have he : q ≤ n.choose 2 - ∑ i, a i * a (i+1) := by
    rwa [cycle5_canonical_edges, hsum] at hedge
  obtain ⟨t, ht⟩ := hc af hsum hsize he
  refine ⟨reindexAllocation af t, ht, ⟨allocationIso cycle5 a _ (d5Iso t) ?_⟩⟩
  intro i
  change a i = (af ((d5Equiv t).symm (d5Equiv t i))).val
  rw [Equiv.symm_apply_apply]


/-- Final transport into a native block-labeled allocation representative. -/
theorem normalize_to_allowed_flat {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (n q : ℕ) (hV : Fintype.card V = n)
    (color : W → Fin 5) (capacity : Fin 5 → ℕ)
    (allowed : Finset (Fin 5 → Fin 6))
    (hcapacity : ∀ i, fiberSize color i ≤ capacity i)
    (hcap : ∀ i, capacity i ≤ 5) (hc : AllocationCheck n q capacity allowed)
    (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G ≤ (cycle5.comap color)ᶜ.comap f) (hcard : q ≤ G.edgeFinset.card) :
    ∃ b ∈ allowed, ∃ e : V ≃ Fin (∑ i, (b i).val),
      G.map e.toEmbedding ≤ flatCanonical cycle5 (fun i => (b i).val) := by
  let a := fiberSize (color ∘ f)
  obtain ⟨b, hb, ⟨ab⟩⟩ := allocationCheck_sound n q capacity allowed hcap hc a
    ((sum_fiberSize _).trans hV)
    (fun i => (fiberSize_le color f i).trans (hcapacity i))
    (hcard.trans (normalized_edge_bound cycle5 color f G hG))
  let iso := ((placementIso cycle5 color f).trans ab).trans
    (flattenIso cycle5 (fun i => (b i).val))
  refine ⟨b, hb, iso.toEquiv, ?_⟩
  rw [map_le_iff_le_comap]
  intro v w h
  exact iso.map_rel_iff.mpr (hG h)

end Problem14.H3

namespace Problem14.H3
def capacities : Fin 3 → Fin 5 → ℕ := ![![4,4,4,4,3],![5,4,4,4,4],![5,5,5,4,4]]

def balancedColor {h : ℕ} (v : Fin h) : Fin 5 := ⟨v.val % 5, Nat.mod_lt _ (by decide)⟩

def balancedHost (h : ℕ) : SimpleGraph (Fin h) := cycle5.comap balancedColor

instance (h : ℕ) : DecidableRel (balancedHost h).Adj := fun _ _ =>
  inferInstanceAs (Decidable (cycle5.Adj _ _))

lemma balancedHost_triangleFree (h : ℕ) : (balancedHost h).CliqueFree 3 := by
  have ht : ∀ i j k : Fin 5, cycle5.Adj i j → cycle5.Adj i k → ¬ cycle5.Adj j k := by
    decide +kernel
  intro S hS
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := SimpleGraph.is3Clique_iff.mp hS
  exact ht _ _ _ hxy hxz hyz

lemma balanced_capacity : ∀ t : Fin 3, ∀ i : Fin 5,
    fiberSize (@balancedColor (2 * (t.val+10)-1)) i = capacities t i := by
  decide +kernel

def allocationLists : Fin 3 → Finset (Fin 5 → Fin 6) := ![{![0,2,4,0,4],![0,3,3,0,4],![0,4,1,1,4]},{![0,1,4,1,5],![0,2,4,0,5],![0,2,5,0,4],![0,3,2,1,5],![0,3,3,0,5],![0,3,4,0,4],![0,4,1,1,5]},{![0,1,5,1,5],![0,2,5,0,5],![0,3,4,0,5],![0,3,5,0,4],![0,4,0,4,4],![0,4,1,2,5],![0,4,2,1,5],![0,5,1,1,5]}]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allocationCheck10 : AllocationCheck 10 34 (capacities 0) (allocationLists 0) := by
  decide +kernel

end Problem14.H3

-- generic vertex-permutation and deletion coverage
/-! Generic coverage and transport for deletion-set orbit certificates.

The acting monoid is kept separate from the edge type: it can be the group
of color-preserving vertex permutations, with `act` its induced action on
unordered edges. Thus a certificate never needs arbitrary edge permutations.
No concrete finite enumeration is asserted in this file.
-/
namespace DeletionOrbit

variable {Edge : Type*} [DecidableEq Edge]
variable {G : Type*} [Monoid G]

def move (act : G →* Equiv.Perm Edge) (g : G) (s : Finset Edge) : Finset Edge :=
  s.map (act g).toEmbedding

omit [DecidableEq Edge] in
@[simp] theorem move_one (act : G →* Equiv.Perm Edge) (s : Finset Edge) :
    move act 1 s = s := by
  simp only [move, map_one]
  exact Finset.map_refl

omit [DecidableEq Edge] in
theorem move_mul (act : G →* Equiv.Perm Edge) (g h : G) (s : Finset Edge) :
    move act (g * h) s = move act g (move act h s) := by
  simp only [move, map_mul, Finset.map_map]
  rfl

@[simp] theorem move_insert (act : G →* Equiv.Perm Edge) (g : G)
    (e : Edge) (s : Finset Edge) :
    move act g (insert e s) = insert (act g e) (move act g s) := by
  simp [move]

omit [DecidableEq Edge] in
theorem move_subset (act : G →* Equiv.Perm Edge) (g : G)
    {s t : Finset Edge} (h : s ⊆ t) : move act g s ⊆ move act g t :=
  Finset.map_subset_map.mpr h

theorem move_sdiff (act : G →* Equiv.Perm Edge) (g : G) (s t : Finset Edge) :
    move act g (s \ t) = move act g s \ move act g t :=
  Finset.map_sdiff s t

/-- It is enough to check one new edge from each orbit of the stabilizer of
the current deletion set. For twin pruning, the first witness can be a
composition of swaps of twins and need not be stored in the certificate. -/
theorem extension_via_stabilizer (act : G →* Equiv.Perm Edge)
    (E r choices : Finset Edge) (Next : Finset Edge → Prop)
    (choose : ∀ e, e ∈ E → e ∉ r →
      ∃ e' ∈ choices, ∃ g, move act g r = r ∧ act g e = e')
    (checked : ∀ e' ∈ choices, ∃ h, Next (move act h (insert e' r))) :
    ∀ e, e ∈ E → e ∉ r → ∃ g, Next (move act g (insert e r)) := by
  intro e he hn
  obtain ⟨e', hc, g, hfix, heq⟩ := choose e he hn
  obtain ⟨h, hh⟩ := checked e' hc
  refine ⟨h * g, ?_⟩
  rw [move_mul, move_insert, hfix, heq]
  exact hh

/-- A certified extension step for every representative covers every deletion
set up to `K` edges. `Rep k s` can mean membership in an explicit finite layer.
The extension certificate only has to provide an admissible symmetry and
membership of its image in the next representative layer. -/
theorem coverage_up_to (act : G →* Equiv.Perm Edge) (E : Finset Edge)
    (Rep : ℕ → Finset Edge → Prop) (K : ℕ)
    (preserves : ∀ g, move act g E = E)
    (base : Rep 0 ∅)
    (step : ∀ k, k < K → ∀ r, Rep k r → r ⊆ E →
      ∀ e, e ∈ E → e ∉ r → ∃ g, Rep (k + 1) (move act g (insert e r))) :
    ∀ d : Finset Edge, d ⊆ E → d.card ≤ K →
      ∃ g, Rep d.card (move act g d) := by
  intro d
  induction d using Finset.induction_on with
  | empty =>
      intro _ _
      exact ⟨1, by simpa using base⟩
  | @insert e s he ih =>
      intro hd hcard
      have hs : s ⊆ E := fun x hx => hd (Finset.mem_insert_of_mem hx)
      have heE : e ∈ E := hd (Finset.mem_insert_self e s)
      have hk : s.card < K := Nat.lt_of_succ_le (by
        simpa only [Finset.card_insert_of_notMem he] using hcard)
      obtain ⟨g, hg⟩ := ih hs (Nat.le_of_lt hk)
      have hr : move act g s ⊆ E := by
        simpa only [preserves g] using move_subset act g hs
      have hge : act g e ∈ E := by
        have hm : act g e ∈ move act g E := by simpa [move] using heE
        simpa only [preserves g] using hm
      have hgn : act g e ∉ move act g s := by simpa [move] using he
      obtain ⟨h, hh⟩ := step s.card hk (move act g s) hg hr (act g e) hge hgn
      refine ⟨h * g, ?_⟩
      simpa only [Finset.card_insert_of_notMem he, move_mul, move_insert,
        map_mul, Equiv.Perm.mul_apply] using hh

/-- If a property of the remaining graph transports back along the admissible
symmetries, checking the representatives proves it for every deletion set of
the requested cardinality. The base edge set is preserved explicitly. -/
theorem property_of_representatives (act : G →* Equiv.Perm Edge)
    (E : Finset Edge) (Rep : ℕ → Finset Edge → Prop) (K k : ℕ)
    (preserves : ∀ g, move act g E = E)
    (base : Rep 0 ∅)
    (step : ∀ j, j < K → ∀ r, Rep j r → r ⊆ E →
      ∀ e, e ∈ E → e ∉ r → ∃ g, Rep (j + 1) (move act g (insert e r)))
    (P : Finset Edge → Prop)
    (transport : ∀ g s, P (move act g s) → P s)
    (checked : ∀ r, Rep k r → P (E \ r))
    (hk : k ≤ K) :
    ∀ d : Finset Edge, d ⊆ E → d.card = k → P (E \ d) := by
  intro d hd hcard
  obtain ⟨g, hg⟩ := coverage_up_to act E Rep K preserves base step d hd
    (by simpa only [hcard] using hk)
  apply transport g (E \ d)
  rw [move_sdiff, preserves]
  apply checked
  simpa only [hcard] using hg


end DeletionOrbit


/-! A bare-list certificate interface for edge-deletion orbit coverage.
The decoder, target lookup and witness selector are deliberately arbitrary:
only their checked outputs matter. No concrete enumeration is asserted. -/
namespace ListEncodedOrbit

variable {Edge : Type*} [DecidableEq Edge]

/-- Interpret a short list of edge indices. Repetitions are harmless. -/
def represented (edge : Nat → Edge) (xs : List Nat) : Finset Edge :=
  (xs.map edge).toFinset

@[simp] theorem mem_represented (edge : Nat → Edge) (xs : List Nat) (e : Edge) :
    e ∈ represented edge xs ↔ ∃ i ∈ xs, edge i = e := by
  simp [represented]

@[simp] theorem represented_nil (edge : Nat → Edge) : represented edge [] = ∅ := by
  simp [represented]

@[simp] theorem represented_cons (edge : Nat → Edge) (i : Nat) (xs : List Nat) :
    represented edge (i :: xs) = insert (edge i) (represented edge xs) := by
  simp [represented]

/-- Equality of small sets without sorting or a proof-bearing finite set. -/
def sameSet (xs ys : List Nat) : Bool :=
  xs.all (fun x => ys.contains x) && ys.all (fun y => xs.contains y)

theorem sameSet_sound {xs ys : List Nat} (h : sameSet xs ys = true) :
    ∀ i, i ∈ xs ↔ i ∈ ys := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true] at h
  intro i
  constructor
  · intro hi
    simpa using h.1 i hi
  · intro hi
    simpa using h.2 i hi

theorem represented_eq_of_sameSet (edge : Nat → Edge) {xs ys : List Nat}
    (h : sameSet xs ys = true) : represented edge xs = represented edge ys := by
  ext e
  simp only [mem_represented]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨i, (sameSet_sound h i).mp hi, he⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨i, (sameSet_sound h i).mpr hi, he⟩

def valid (m : Nat) (xs : List Nat) : Bool := xs.all (fun i => decide (i < m))

theorem valid_iff (m : Nat) (xs : List Nat) :
    valid m xs = true ↔ ∀ i ∈ xs, i < m := by
  simp [valid, List.all_eq_true]

theorem represented_map (edge : Nat → Edge) (p : Equiv.Perm Edge)
    (a : Nat → Nat) (xs : List Nat)
    (h : ∀ i ∈ xs, edge (a i) = p (edge i)) :
    represented edge (xs.map a) = (represented edge xs).map p.toEmbedding := by
  ext e
  simp only [mem_represented, List.mem_map, Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨j, ⟨i, hi, rfl⟩, he⟩
    exact ⟨edge i, ⟨i, hi, rfl⟩, (h i hi).symm.trans he⟩
  · rintro ⟨x, ⟨i, hi, rfl⟩, he⟩
    exact ⟨a i, ⟨i, hi, rfl⟩, (h i hi).trans he⟩

/-- Generators act in list order: the head acts first. -/
def runWord (actions : Nat → Nat → Nat) : List Nat → List Nat → List Nat
  | [], xs => xs
  | g :: gs, xs => runWord actions gs (xs.map (actions g))

variable {G : Type*} [Monoid G]

def wordValue (generators : Nat → G) : List Nat → G
  | [] => 1
  | g :: gs => wordValue generators gs * generators g

/-- The semantic part is separate from the numerical checker. -/
theorem runWord_sound (act : G →* Equiv.Perm Edge) (edge : Nat → Edge)
    (generators : Nat → G) (actions : Nat → Nat → Nat) (m c : Nat)
    (action_sound : ∀ g, g < c → ∀ i, i < m →
      edge (actions g i) = act (generators g) (edge i))
    (action_closed : ∀ g, g < c → ∀ i, i < m → actions g i < m)
    (word xs : List Nat) (hw : valid c word = true) (hx : valid m xs = true) :
    represented edge (runWord actions word xs) =
      (represented edge xs).map (act (wordValue generators word)).toEmbedding := by
  induction word generalizing xs with
  | nil =>
      simp only [runWord, wordValue, map_one]
      exact Finset.map_refl.symm
  | cons g gs ih =>
    have hg : g < c := (valid_iff c (g :: gs)).mp hw g (by simp)
    have hgs : valid c gs = true := (valid_iff c gs).mpr (by
      intro i hi
      exact (valid_iff c (g :: gs)).mp hw i (by simp [hi]))
    have hnext : valid m (xs.map (actions g)) = true := (valid_iff _ _).mpr (by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      exact action_closed g hg i ((valid_iff _ _).mp hx i hi))
    rw [runWord, ih _ hgs hnext]
    rw [represented_map edge (act (generators g)) (actions g) xs (by
      intro i hi
      exact action_sound g hg i ((valid_iff _ _).mp hx i hi))]
    simp only [wordValue, map_mul, Finset.map_map]
    rfl

/-- Each lookup returns a generator word and an index of the next layer. -/
def checkParent (m c : Nat) (actions : Nat → Nat → Nat)
    (parent : List Nat) (nextCount : Nat) (next : Nat → List Nat)
    (witness : Nat → List Nat × Nat) : Bool :=
  valid m parent && (List.range m).all (fun i =>
    parent.contains i ||
      let w := witness i
      valid c w.1 && decide (w.2 < nextCount) &&
        sameSet (runWord actions w.1 (i :: parent)) (next w.2))

theorem checkParent_sound (act : G →* Equiv.Perm Edge) (edge : Nat → Edge)
    (generators : Nat → G) (actions : Nat → Nat → Nat) (m c : Nat)
    (action_sound : ∀ g, g < c → ∀ i, i < m →
      edge (actions g i) = act (generators g) (edge i))
    (action_closed : ∀ g, g < c → ∀ i, i < m → actions g i < m)
    (parent : List Nat) (nextCount : Nat) (next : Nat → List Nat)
    (witness : Nat → List Nat × Nat)
    (hc : checkParent m c actions parent nextCount next witness = true) :
    ∀ i, i < m → edge i ∉ represented edge parent →
      ∃ g j, j < nextCount ∧
        represented edge (next j) =
          (insert (edge i) (represented edge parent)).map (act g).toEmbedding := by
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true] at hc
  intro i hi hn
  have hni : i ∉ parent := by
    intro h
    exact hn (mem_represented edge parent (edge i) |>.mpr ⟨i, h, rfl⟩)
  have step := hc.2 i (List.mem_range.mpr hi)
  simp [hni, Bool.and_eq_true] at step
  refine ⟨wordValue generators (witness i).1, (witness i).2, step.1.2, ?_⟩
  rw [← represented_cons]
  rw [← runWord_sound act edge generators actions m c action_sound action_closed
    (witness i).1 (i :: parent) step.1.1 ((valid_iff _ _).mpr (by
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact (valid_iff _ _).mp hc.1 j hj))]
  exact (represented_eq_of_sameSet edge step.2).symm

end ListEncodedOrbit



namespace ListEncodedOrbit
variable {Edge : Type*} [DecidableEq Edge] {G : Type*} [Monoid G]

/-- A layer is accessed lazily so packed blocks need not be expanded globally. -/
def checkLayer (m c : Nat) (actions : Nat → Nat → Nat)
    (count : Nat → Nat) (layer : Nat → Nat → List Nat)
    (witness : Nat → Nat → Nat → List Nat × Nat) (k : Nat) : Bool :=
  (List.range (count k)).all fun r =>
    checkParent m c actions (layer k r) (count (k+1)) (layer (k+1)) (witness k r)

def checkCoverage (m c K : Nat) (actions : Nat → Nat → Nat)
    (count : Nat → Nat) (layer : Nat → Nat → List Nat)
    (witness : Nat → Nat → Nat → List Nat × Nat) : Bool :=
  decide (0 < count 0) && sameSet (layer 0 0) [] &&
    (List.range K).all (checkLayer m c actions count layer witness)

/-- Packed target lookup is trusted only after the resulting list is checked.
No statement about sorting, ranking or unranking is assumed here. -/
theorem checked_coverage (act : G →* Equiv.Perm Edge) (edge : Nat → Edge)
    (generators : Nat → G) (actions : Nat → Nat → Nat) (m c K : Nat)
    (action_sound : ∀ g, g < c → ∀ i, i < m →
      edge (actions g i) = act (generators g) (edge i))
    (action_closed : ∀ g, g < c → ∀ i, i < m → actions g i < m)
    (preserves : ∀ g, DeletionOrbit.move act g (represented edge (List.range m)) =
      represented edge (List.range m))
    (count : Nat → Nat) (layer : Nat → Nat → List Nat)
    (witness : Nat → Nat → Nat → List Nat × Nat)
    (hc : checkCoverage m c K actions count layer witness = true) :
    ∀ d : Finset Edge, d ⊆ represented edge (List.range m) → d.card ≤ K →
      ∃ g j, j < count d.card ∧
        represented edge (layer d.card j) = DeletionOrbit.move act g d := by
  simp only [checkCoverage, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hc
  let Rep : Nat → Finset Edge → Prop :=
    fun k s => ∃ j, j < count k ∧ represented edge (layer k j) = s
  have hb : Rep 0 ∅ := ⟨0, hc.1.1,
    (represented_eq_of_sameSet edge hc.1.2).trans (represented_nil edge)⟩
  have hs : ∀ k, k < K → ∀ r, Rep k r →
      r ⊆ represented edge (List.range m) →
      ∀ e, e ∈ represented edge (List.range m) → e ∉ r →
      ∃ g, Rep (k+1) (DeletionOrbit.move act g (insert e r)) := by
    intro k hk r hr _ e he hn
    obtain ⟨j, hj, rfl⟩ := hr
    obtain ⟨i, hi, rfl⟩ := (mem_represented edge (List.range m) e).mp he
    have hL := hc.2 k (List.mem_range.mpr hk)
    have hP := List.all_eq_true.mp hL j (List.mem_range.mpr hj)
    obtain ⟨g, t, ht, hm⟩ := checkParent_sound act edge generators actions m c
      action_sound action_closed (layer k j) (count (k+1)) (layer (k+1))
      (witness k j) hP i (List.mem_range.mp hi) hn
    exact ⟨g, t, ht, hm⟩
  intro d hd hk
  exact DeletionOrbit.coverage_up_to act (represented edge (List.range m)) Rep K
    preserves hb hs d hd hk

end ListEncodedOrbit





namespace NumericPermutations

def check (n : Nat) (values : Nat → Nat) : Bool :=
  (List.range n).all fun i => decide (values i < n) &&
    (List.range i).all (fun j => values i != values j)

theorem checked_bound {n : Nat} {values : Nat → Nat} (hc : check n values = true)
    {i : Nat} (hi : i < n) : values i < n := by
  have h := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

def asFin {n : Nat} (hn : 0 < n) (values : Nat → Nat) (i : Fin n) : Fin n :=
  ⟨values i.val % n, Nat.mod_lt _ hn⟩

theorem checked_val {n : Nat} (hn : 0 < n) (values : Nat → Nat)
    (hc : check n values = true) (i : Fin n) :
    (asFin hn values i).val = values i.val :=
  Nat.mod_eq_of_lt (checked_bound hc i.isLt)

theorem checked_injective {n : Nat} (hn : 0 < n) (values : Nat → Nat)
    (hc : check n values = true) : Function.Injective (asFin hn values) := by
  intro i j heq
  have hv : values i.val = values j.val := by
    simpa only [checked_val hn values hc] using congrArg Fin.val heq
  have ne : ∀ a b : Nat, a < n → b < a → values a ≠ values b := by
    intro a b ha hb
    have h := List.all_eq_true.mp hc a (List.mem_range.mpr ha)
    have hh := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 b (List.mem_range.mpr hb)
    simpa using hh
  rcases lt_trichotomy i.val j.val with hlt | he | hgt
  · exact False.elim (ne j.val i.val j.isLt hlt hv.symm)
  · exact Fin.ext he
  · exact False.elim (ne i.val j.val i.isLt hgt hv)

noncomputable def toPerm {n : Nat} (hn : 0 < n) (values : Nat → Nat)
    (hc : check n values = true) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (asFin hn values) (checked_injective hn values hc).bijective_of_finite

theorem toPerm_val {n : Nat} (hn : 0 < n) (values : Nat → Nat)
    (hc : check n values = true) (i : Fin n) :
    (toPerm hn values hc i).val = values i.val := checked_val hn values hc i

/-- Vertex permutations induce actual permutations of unordered edges. -/
def sym2Perm {V : Type*} (p : Equiv.Perm V) : Equiv.Perm (Sym2 V) where
  toFun := Sym2.map p
  invFun := Sym2.map p.symm
  left_inv := by
    intro x
    rw [Sym2.map_map]
    simp only [Function.comp_def, Equiv.symm_apply_apply]
    exact congrFun Sym2.map_id' x
  right_inv := by
    intro x
    rw [Sym2.map_map]
    simp only [Function.comp_def, Equiv.apply_symm_apply]
    exact congrFun Sym2.map_id' x

def sym2Action (V : Type*) : Equiv.Perm V →* Equiv.Perm (Sym2 V) where
  toFun := sym2Perm
  map_one' := by
    apply Equiv.ext
    intro x
    exact congrFun Sym2.map_id' x
  map_mul' p q := by
    apply Equiv.ext
    intro x
    exact (Sym2.map_map (g := p) (f := q) x).symm

def normPair (a b : Nat) : Nat × Nat := (min a b, max a b)

theorem normPair_sym2 (a b : Nat) :
    s((normPair a b).1, (normPair a b).2) = (s(a,b) : Sym2 Nat) := by
  rcases le_total a b with h | h
  · simp [normPair, min_eq_left h, max_eq_right h]
  · simpa [normPair, min_eq_right h, max_eq_left h] using (Sym2.eq_swap (a := b) (b := a))

theorem normPair_sound {a b c d : Nat} (h : normPair a b = normPair c d) :
    (s(a,b) : Sym2 Nat) = s(c,d) := by
  rw [← normPair_sym2 a b, h, normPair_sym2 c d]

end NumericPermutations

namespace DeletionOrbit
variable {Edge : Type*} [DecidableEq Edge] {G : Type*} [Monoid G]

/-- Restrict to symmetries of the fixed allowed edge set. Only a monoid is
needed; inverses and color-specific automorphism theory are unnecessary. -/
def preserving (act : G →* Equiv.Perm Edge) (E : Finset Edge) : Submonoid G where
  carrier := {g | move act g E = E}
  one_mem' := move_one act E
  mul_mem' := by
    intro a b ha hb
    change move act (a*b) E = E
    rw [move_mul, hb, ha]

def preservingAction (act : G →* Equiv.Perm Edge) (E : Finset Edge) :
    preserving act E →* Equiv.Perm Edge := act.comp (preserving act E).subtype

theorem preservingAction_preserves (act : G →* Equiv.Perm Edge) (E : Finset Edge)
    (g : preserving act E) : move (preservingAction act E) g E = E := g.property

end DeletionOrbit

namespace NumericPermutations

def rawFin {n : Nat} (hn : 0 < n) (i : Nat) : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩

def rawEdge {n : Nat} (hn : 0 < n) (pairs : Nat → Nat × Nat) (i : Nat) : Sym2 (Fin n) :=
  s(rawFin hn (pairs i).1, rawFin hn (pairs i).2)

def checkEdgeBounds (n m : Nat) (pairs : Nat → Nat × Nat) : Bool :=
  (List.range m).all fun i => decide ((pairs i).1 < n) && decide ((pairs i).2 < n)

def checkAction (m : Nat) (pairs : Nat → Nat × Nat)
    (values action : Nat → Nat) : Bool :=
  (List.range m).all fun i => decide (action i < m) &&
    (normPair (values (pairs i).1) (values (pairs i).2) ==
      normPair (pairs (action i)).1 (pairs (action i)).2)

def checkGenerators (n m c : Nat) (pairs : Nat → Nat × Nat)
    (values : Nat → Nat → Nat) (actions : Nat → Nat → Nat) : Bool :=
  checkEdgeBounds n m pairs && (List.range c).all fun g =>
    check n (values g) && checkAction m pairs (values g) (actions g)

theorem toPerm_rawFin {n : Nat} (hn : 0 < n) (values : Nat → Nat)
    (hc : check n values = true) {i : Nat} (hi : i < n) :
    toPerm hn values hc (rawFin hn i) = rawFin hn (values i) := by
  apply Fin.ext
  rw [toPerm_val]
  change values (i % n) = values i % n
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (checked_bound hc hi)]

theorem checked_action {n m : Nat} (hn : 0 < n) (pairs : Nat → Nat × Nat)
    (values action : Nat → Nat) (hp : check n values = true)
    (hb : checkEdgeBounds n m pairs = true)
    (ha : checkAction m pairs values action = true) :
    ∀ i, i < m → action i < m ∧
      rawEdge hn pairs (action i) = sym2Perm (toPerm hn values hp) (rawEdge hn pairs i) := by
  intro i hi
  have bound := List.all_eq_true.mp hb i (List.mem_range.mpr hi)
  have h := List.all_eq_true.mp ha i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at bound h
  refine ⟨h.1, ?_⟩
  have eq := congrArg (Sym2.map (rawFin hn)) (normPair_sound h.2).symm
  change s(rawFin hn (pairs (action i)).1, rawFin hn (pairs (action i)).2) =
    s(toPerm hn values hp (rawFin hn (pairs i).1),
      toPerm hn values hp (rawFin hn (pairs i).2))
  rw [toPerm_rawFin hn values hp bound.1, toPerm_rawFin hn values hp bound.2]
  exact eq

end NumericPermutations

namespace ListEncodedOrbit
variable {Edge : Type*} [DecidableEq Edge]

theorem preserves_of_index_action (edge : Nat → Edge) (p : Equiv.Perm Edge)
    (m : Nat) (action : Nat → Nat)
    (closed : ∀ i, i < m → action i < m)
    (sound : ∀ i, i < m → edge (action i) = p (edge i)) :
    (represented edge (List.range m)).map p.toEmbedding = represented edge (List.range m) := by
  apply Finset.map_eq_of_subset
  intro e he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp he
  obtain ⟨i, hi, rfl⟩ := (mem_represented edge (List.range m) x).mp hx
  apply (mem_represented edge (List.range m) (p (edge i))).mpr
  exact ⟨action i, List.mem_range.mpr (closed i (List.mem_range.mp hi)),
    sound i (List.mem_range.mp hi)⟩
end ListEncodedOrbit

namespace NumericPermutations

/-- Soundness of the complete raw-index orbit checker for a genuine vertex
permutation action. The only trusted inputs are proved Boolean equalities. -/
theorem checked_vertex_orbit_coverage
    (n m c K : Nat) (hn : 0 < n) (pairs : Nat → Nat × Nat)
    (values actions : Nat → Nat → Nat)
    (count : Nat → Nat) (layer : Nat → Nat → List Nat)
    (witness : Nat → Nat → Nat → List Nat × Nat)
    (hg : checkGenerators n m c pairs values actions = true)
    (hc : ListEncodedOrbit.checkCoverage m c K actions count layer witness = true) :
    ∀ d : Finset (Sym2 (Fin n)),
      d ⊆ ListEncodedOrbit.represented (rawEdge hn pairs) (List.range m) →
      d.card ≤ K →
      ∃ (p : Equiv.Perm (Fin n)) (j : Nat),
        (ListEncodedOrbit.represented (rawEdge hn pairs) (List.range m)).map
          (sym2Perm p).toEmbedding =
            ListEncodedOrbit.represented (rawEdge hn pairs) (List.range m) ∧
        j < count d.card ∧
        ListEncodedOrbit.represented (rawEdge hn pairs) (layer d.card j) =
          d.map (sym2Perm p).toEmbedding := by
  classical
  let edge := rawEdge hn pairs
  let E := ListEncodedOrbit.represented edge (List.range m)
  let A := sym2Action (Fin n)
  let T := DeletionOrbit.preserving A E
  let act := DeletionOrbit.preservingAction A E
  have bounds : checkEdgeBounds n m pairs = true := (Bool.and_eq_true_iff.mp hg).1
  have specs : ∀ g, g < c → ∃ p : Equiv.Perm (Fin n),
      ∀ i, i < m → actions g i < m ∧
        edge (actions g i) = sym2Perm p (edge i) := by
    intro g hgc
    have hg' := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hg).2 g (List.mem_range.mpr hgc)
    exact ⟨toPerm hn (values g) (Bool.and_eq_true_iff.mp hg').1,
      checked_action hn pairs (values g) (actions g) (Bool.and_eq_true_iff.mp hg').1
        bounds (Bool.and_eq_true_iff.mp hg').2⟩
  have existsGenerators : ∀ g, ∃ p : T, ∀ i, g < c → i < m →
      actions g i < m ∧ edge (actions g i) = act p (edge i) := by
    intro g
    by_cases hgc : g < c
    · obtain ⟨p, hp⟩ := specs g hgc
      have hpres : DeletionOrbit.move A p E = E :=
        ListEncodedOrbit.preserves_of_index_action edge (sym2Perm p) m (actions g)
          (fun i hi => (hp i hi).1) (fun i hi => (hp i hi).2)
      exact ⟨⟨p, hpres⟩, fun i _ hi => hp i hi⟩
    · exact ⟨1, fun _ h _ => False.elim (hgc h)⟩
  let generators : Nat → T := fun g => Classical.choose (existsGenerators g)
  have hgenerators : ∀ g i, g < c → i < m →
      actions g i < m ∧ edge (actions g i) = act (generators g) (edge i) :=
    fun g => Classical.choose_spec (existsGenerators g)
  intro d hd hk
  obtain ⟨g, j, hj, he⟩ := ListEncodedOrbit.checked_coverage act edge generators actions
    m c K (fun g hg i hi => (hgenerators g i hg hi).2)
    (fun g hg i hi => (hgenerators g i hg hi).1)
    (DeletionOrbit.preservingAction_preserves A E) count layer witness hc d hd hk
  exact ⟨g.val, j, g.property, hj, he⟩

end NumericPermutations

namespace DeletionRows

/-- A union of vertex bits; repeated indices have no effect. -/
def bitSet : List Nat → Nat
  | [] => 0
  | i :: xs => (2^i) ||| bitSet xs

theorem testBit_bitSet (xs : List Nat) (v : Nat) :
    (bitSet xs).testBit v = true ↔ v ∈ xs := by
  induction xs with
  | nil => simp [bitSet]
  | cons i xs ih =>
      rw [bitSet, Nat.testBit_or, Nat.testBit_two_pow]
      rw [Bool.or_eq_true_iff, decide_eq_true_eq, ih, List.mem_cons]
      exact or_congr eq_comm Iff.rfl

/-- Neighbors generated by an unordered raw edge list. -/
def neighborList (pairs : Nat → Nat × Nat) (indices : List Nat) (v : Nat) : List Nat :=
  indices.flatMap fun i =>
    (if (pairs i).1 = v then [(pairs i).2] else []) ++
    (if (pairs i).2 = v then [(pairs i).1] else [])

def row (pairs : Nat → Nat × Nat) (indices : List Nat) (v : Nat) : Nat :=
  bitSet (neighborList pairs indices v)

theorem row_iff (pairs : Nat → Nat × Nat) (indices : List Nat) (u v : Nat) :
    (row pairs indices u).testBit v = true ↔
      ∃ i ∈ indices, ((pairs i).1 = u ∧ (pairs i).2 = v) ∨
        ((pairs i).1 = v ∧ (pairs i).2 = u) := by
  simp only [row, testBit_bitSet, neighborList, List.mem_flatMap, List.mem_append]
  constructor
  · rintro ⟨i, hi, h⟩
    refine ⟨i, hi, ?_⟩
    rcases h with h | h
    · by_cases hu : (pairs i).1 = u
      · exact Or.inl ⟨hu, by simpa [hu, eq_comm] using h⟩
      · simp [hu] at h
    · by_cases hu : (pairs i).2 = u
      · exact Or.inr ⟨by simpa [hu, eq_comm] using h, hu⟩
      · simp [hu] at h
  · rintro ⟨i, hi, h⟩
    refine ⟨i, hi, ?_⟩
    rcases h with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · exact Or.inl (by simp [hu,hv])
    · exact Or.inr (by simp [hu,hv])

/-- Cutting an arbitrary deletion row out of the base row is duplicate-safe. -/
def remaining (n : Nat) (base deleted : Nat → Nat) (u : Nat) : Nat :=
  base u &&& ((2^n-1) ^^^ deleted u)

theorem remaining_iff (n : Nat) (base deleted : Nat → Nat) (u v : Nat) (hv : v < n) :
    (remaining n base deleted u).testBit v = true ↔
      (base u).testBit v = true ∧ (deleted u).testBit v = false := by
  simp [remaining, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, hv]

end DeletionRows


namespace NumericPermutations

theorem rawFin_eq {n : Nat} (hn : 0 < n) {i : Nat} (hi : i < n) (v : Fin n) :
    rawFin hn i = v ↔ i = v.val := by
  rw [Fin.ext_iff]
  simp only [rawFin, Nat.mod_eq_of_lt hi]

theorem rawEdge_membership_row {n : Nat} (hn : 0 < n)
    (pairs : Nat → Nat × Nat) (indices : List Nat)
    (bound : ∀ i ∈ indices, (pairs i).1 < n ∧ (pairs i).2 < n)
    (u v : Fin n) :
    s(u,v) ∈ ListEncodedOrbit.represented (rawEdge hn pairs) indices ↔
      (DeletionRows.row pairs indices u.val).testBit v.val = true := by
  rw [ListEncodedOrbit.mem_represented, DeletionRows.row_iff]
  constructor
  · rintro ⟨i, hi, he⟩
    refine ⟨i, hi, ?_⟩
    simpa only [rawEdge, Sym2.eq_iff, rawFin_eq hn (bound i hi).1,
      rawFin_eq hn (bound i hi).2] using he
  · rintro ⟨i, hi, he⟩
    refine ⟨i, hi, ?_⟩
    simpa only [rawEdge, Sym2.eq_iff, rawFin_eq hn (bound i hi).1,
      rawFin_eq hn (bound i hi).2] using he

/-- Exact row interpretation of a base graph with the decoded deletion set
removed. Distinctness of every base edge supplies looplessness. -/
theorem deleted_graph_row {n : Nat} (hn : 0 < n)
    (pairs : Nat → Nat × Nat) (base deleted : List Nat)
    (base_bound : ∀ i ∈ base, (pairs i).1 < n ∧ (pairs i).2 < n)
    (deleted_bound : ∀ i ∈ deleted, (pairs i).1 < n ∧ (pairs i).2 < n)
    (no_loop : ∀ i ∈ base, (pairs i).1 ≠ (pairs i).2)
    (u v : Fin n) :
    (SimpleGraph.fromEdgeSet
      ((ListEncodedOrbit.represented (rawEdge hn pairs) base \
        ListEncodedOrbit.represented (rawEdge hn pairs) deleted : Finset (Sym2 (Fin n))) :
          Set (Sym2 (Fin n)))).Adj u v ↔
      (DeletionRows.remaining n (DeletionRows.row pairs base)
        (DeletionRows.row pairs deleted) u.val).testBit v.val = true := by
  rw [SimpleGraph.fromEdgeSet_adj, DeletionRows.remaining_iff _ _ _ _ _ v.isLt]
  simp only [Finset.mem_coe, Finset.mem_sdiff]
  rw [rawEdge_membership_row hn pairs base base_bound,
    rawEdge_membership_row hn pairs deleted deleted_bound]
  have hne : (DeletionRows.row pairs base u.val).testBit v.val = true → u ≠ v := by
    intro h he
    obtain ⟨i, hi, hpair⟩ := (DeletionRows.row_iff pairs base u.val v.val).mp h
    have hv : u.val = v.val := congrArg Fin.val he
    rcases hpair with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact no_loop i hi (ha.trans (hv.trans hb.symm))
    · exact no_loop i hi (ha.trans (hv.symm.trans hb.symm))
  cases hb : (DeletionRows.row pairs base u.val).testBit v.val <;>
    cases hd : (DeletionRows.row pairs deleted u.val).testBit v.val <;> simp_all

end NumericPermutations

/-! Evaluation helpers adapted from agent12's domain materializer. These are
identities; they merely force Nat values before invoking a continuation. -/
namespace CheckedBlocks

/-- Numerically check one fixed-size block, ignoring indices past the end. -/
def block (f : Nat → Bool) (total width b : Nat) : Bool :=
  (List.range width).all fun j =>
    let i := b*width+j
    if i < total then f i else true

/-- Separately checked blocks combine without rerunning their computations. -/
theorem all_of_blocks (f : Nat → Bool) (total width blocks : Nat)
    (hw : 0 < width) (cover : total ≤ blocks*width)
    (hc : ∀ b, b < blocks → block f total width b = true) :
    (List.range total).all f = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hi' := List.mem_range.mp hi
  have hb : i / width < blocks :=
    (Nat.div_lt_iff_lt_mul hw).mpr (lt_of_lt_of_le hi' cover)
  have hj : i % width < width := Nat.mod_lt i hw
  have h := List.all_eq_true.mp (hc (i/width) hb) (i%width) (List.mem_range.mpr hj)
  have he : i/width*width+i%width = i := Nat.div_add_mod' i width
  simpa only [he, if_pos hi'] using h

end CheckedBlocks



namespace NumericPermutations

theorem checked_edge_bounds {n m : Nat} {pairs : Nat → Nat × Nat}
    (hc : checkEdgeBounds n m pairs = true) {i : Nat} (hi : i < m) :
    (pairs i).1 < n ∧ (pairs i).2 < n := by
  have h := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using h


end NumericPermutations

namespace NumericPermutations

def checkNoLoops (m : Nat) (pairs : Nat → Nat × Nat) : Bool :=
  (List.range m).all fun i => (pairs i).1 != (pairs i).2

theorem checked_no_loops {m : Nat} {pairs : Nat → Nat × Nat}
    (hc : checkNoLoops m pairs = true) {i : Nat} (hi : i < m) :
    (pairs i).1 ≠ (pairs i).2 := by
  have h := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
  simpa using h

end NumericPermutations


namespace NumericPermutations

variable {V W : Type*} [DecidableEq V]

def remainingGraph (E D : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet ((E \ D : Finset (Sym2 V)) : Set (Sym2 V))

theorem remainingGraph_adj_perm (p : Equiv.Perm V) (E D R : Finset (Sym2 V))
    (hE : E.map (sym2Perm p).toEmbedding = E)
    (hD : D.map (sym2Perm p).toEmbedding = R) (u v : V) :
    (remainingGraph E R).Adj (p u) (p v) ↔ (remainingGraph E D).Adj u v := by
  have he : s(p u,p v) ∈ E.map (sym2Perm p).toEmbedding ↔ s(u,v) ∈ E := by
    change sym2Perm p s(u,v) ∈ E.map (sym2Perm p).toEmbedding ↔ _
    simp
  have hd : s(p u,p v) ∈ D.map (sym2Perm p).toEmbedding ↔ s(u,v) ∈ D := by
    change sym2Perm p s(u,v) ∈ D.map (sym2Perm p).toEmbedding ↔ _
    simp
  rw [hE] at he
  rw [hD] at hd
  have hn : p u ≠ p v ↔ u ≠ v :=
    ⟨fun h huv => h (congrArg p huv), fun h huv => h (p.injective huv)⟩
  simp only [remainingGraph, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
    Finset.mem_sdiff, he, hd, hn]

/-- A rejecting host for a deletion representative also rejects every
isomorphic deletion graph, using the actual vertex permutation from coverage. -/
theorem no_embedding_of_permuted (p : Equiv.Perm V) (E D R : Finset (Sym2 V))
    (H : SimpleGraph W)
    (hE : E.map (sym2Perm p).toEmbedding = E)
    (hD : D.map (sym2Perm p).toEmbedding = R)
    (reject : ¬ ∃ f : V → W, Function.Injective f ∧
      ∀ u v, (remainingGraph E R).Adj u v → H.Adj (f u) (f v)) :
    ¬ ∃ f : V → W, Function.Injective f ∧
      ∀ u v, (remainingGraph E D).Adj u v → H.Adj (f u) (f v) := by
  rintro ⟨f, hf, hedges⟩
  apply reject
  refine ⟨f ∘ p.symm, hf.comp p.symm.injective, ?_⟩
  intro u v hadj
  apply hedges
  apply (remainingGraph_adj_perm p E D R hE hD (p.symm u) (p.symm v)).mp
  simpa only [Equiv.apply_symm_apply] using hadj

end NumericPermutations

-- three concrete orbit certificates
namespace Order10Orbit.A02404
open ListEncodedOrbit
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgeCount : Nat := 37
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def depth : Nat := 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def generatorCount : Nat := 56
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgePairs : Array (Nat × Nat) := #[(0,1),(0,6),(0,7),(0,8),(0,9),(1,6),(1,7),(1,8),(1,9),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(4,5),(4,6),(4,7),(4,8),(4,9),(5,6),(5,7),(5,8),(5,9),(6,7),(6,8),(6,9),(7,8),(7,9),(8,9)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pairs (i : Nat) : Nat × Nat := edgePairs[i]!
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def vertexWords : Array Nat := #[453242008080,509361795600,521944707600,581587710480,646515536400,650290406160,650290409985,650793726480,654568530960,654568596240,654568600065,654568600080,654818038800,654819275280,654820131600,654820189200,654820196880,654820254480,654820258305,654820258320,654820258320,654820258305,654820258305,654820258320,654820258320,654820254480,654820127760,654817113360,654820254480,654820258320,654820196880,654818169360,654820127760,654820196880,654820258320,654819275280,654817113360,654818169360,654819275280,654820258320,654820258320,654568600080,646263878160,448712159760,654568600080,654820258320,650793726480,517918175760,646263878160,650793726480,654820258320,590395748880,448712159760,517918175760,590395748880,654820258320]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgeIndices : Array Nat := #[72910924139614245,0x207185965965940,0x3ce34c2ca265965,0x5544d2450949965,0x6996175a540a965,0x79d71b95644b965,0x8607e56d748c141,0x8e295f7184cd182,0x9258a075950e1c3,0x9648e179a54f204]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def values (g v : Nat) : Nat := (vertexWords[g]!).shiftRight (4*v) % 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgeActionWords : Array Nat := #[0x218247e389b79d71769961649551345030f38d2ca245207181103080,0x1f8e18a091c6de7585da6564d255445034c3ce2ca2461481c20440c0,0x238a47e181c79d6d86995d64d551245034f38c2ca246207142103040,0x2281f92385d71b79961769651349545038d30f2ca247185203081100,0x219208df89e6dd71a5d96165525134503cc38d2ca248147184043080,0x2385f92281e71b75a6176563cd30e2ca5534944502481851c40810c0,0x2385f92281e71b75a6176565534944503cd30e2ca2440810c81851c0,0x2392285f81e71d6da6195d65535124503cd38c2ca248187144083040,0x248608e27de75b7155124d13ce30d2c96995d85902881c51840c1080,0x248608e27de75b71a6576163ce30d2ca5544934502481c51840c1080,0x248608e27de75b71a6576165544934503ce30d2ca2440c10881c5180,0x248608e27de75b71a6576165544934503ce30d2ca2481c51840c1080,0x248e28607d551348f38d30979d71b44b69961740a5881c61440c2040,0x248e28607da6585de75c6d65544d24113ce34c28b2481c61440c2040,0x248e28607de75c6cf38d30b69961758a5544d24494081c61440c2040,0x248e28607de75c6d55134913ce34c2c96996175902881c61440c2040,0x248e28607de75c6d55134916996175903ce34c2c92881c61440c2040,0x248e28607de75c6da6585d63ce34c2ca5544d24502481c61440c2040,0x248e28607de75c6da6585d65544d24503ce34c2ca2440c20481c6140,0x248e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x248e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x248e28607de75c6da6585d65544d24503ce34c2ca2440c20481c6140,0x248e28607de75c6da6585d65544d24503ce34c2ca2440c20481c6140,0x248e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x248e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x248e28607de75c6da6585d63ce34c2ca5544d24502481c61440c2040,0x248e28607de75c6cf38d30b5544d244969961758a4081c61440c2040,0x248e28607cf38d31a6585ca5544d225079d71b2d64481c61440c2040,0x248e28607de75c6da6585d63ce34c2ca5544d24502481c61440c2040,0x248e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x248e28607de75c6d55134916996175903ce34c2c92881c61440c2040,0x248e28607d551349a6585d079d71b4563ce34c24a2c81c61440c2040,0x248e28607de75c6cf38d30b5544d244969961758a4081c61440c2040,0x248e28607de75c6d55134916996175903ce34c2c92881c61440c2040,0x248e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x248e28607da6585de75c6d65544d24113ce34c28b2481c61440c2040,0x248e28607cf38d31a6585ca5544d225079d71b2d64481c61440c2040,0x248e28607d551349a6585d079d71b4563ce34c24a2c81c61440c2040,0x248e28607da6585de75c6d65544d24113ce34c28b2481c61440c2040,0x248e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x248e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x248608e27de75b71a6576165544934503ce30d2ca2481c51840c1080,0x218df92089e6dc75a5d86565524d44503cc34e2ca2481461c40420c0,0x207e28648db75c7976586964944d545030e34f2ca2451c62010c2100,0x248608e27de75b71a6576165544934503ce30d2ca2481c51840c1080,0x248e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x2392285f81e71d6da6195d65535124503cd38c2ca248187144083040,0x228e47e085c75e6d865a5d64d455245034e3cc2ca2461c81420c4040,0x218df92089e6dc75a5d86565524d44503cc34e2ca2481461c40420c0,0x2392285f81e71d6da6195d65535124503cd38c2ca248187144083040,0x248e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x248a38217dd79c6d96985d65154d245038f34c2ca247206143102040,0x207e28648db75c7976586964944d545030e34f2ca2451c62010c2100,0x228e47e085c75e6d865a5d64d455245034e3cc2ca2461c81420c4040,0x248a38217dd79c6d96985d65154d245038f34c2ca247206143102040,0x248e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def actions (g i : Nat) : Nat := (edgeActionWords[g]!).shiftRight (6*i) % 64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def layerData : Array (Array (List Nat)) := #[#[[]],#[[0],[1],[9],[12],[31]],#[[1,0],[2,1],[5,1],[6,1],[9,0],[9,1],[10,9],[12,0],[12,1],[12,9],[13,1],[13,12],[18,12],[19,12],[22,9],[23,9],[31,0],[31,1],[31,9],[31,12],[32,31],[34,1],[34,12],[36,31]],#[[2,1,0],[3,2,1],[5,1,0],[5,2,1],[6,1,0],[7,2,1],[9,1,0],[9,2,1],[9,5,1],[9,6,1],[10,9,0],[10,9,1],[11,10,9],[12,1,0],[12,2,1],[12,5,1],[12,6,1],[12,9,0],[12,9,1],[12,10,9],[13,1,0],[13,5,1],[13,9,1],[13,12,0],[13,12,1],[13,12,9],[14,2,1],[14,6,1],[14,13,1],[14,13,12],[16,10,9],[16,13,12],[17,10,9],[18,10,9],[18,12,0],[18,12,1],[18,12,9],[18,13,12],[19,12,0],[19,12,1],[19,12,9],[19,13,1],[20,13,1],[20,13,12],[22,9,0],[22,9,1],[22,12,9],[22,18,12],[22,19,12],[23,9,0],[23,9,1],[23,12,9],[23,18,12],[24,9,1],[24,12,9],[24,18,12],[25,19,12],[27,10,9],[31,1,0],[31,2,1],[31,5,1],[31,6,1],[31,9,0],[31,9,1],[31,10,9],[31,12,0],[31,12,1],[31,12,9],[31,13,1],[31,13,12],[31,18,12],[31,19,12],[31,22,9],[31,23,9],[32,2,1],[32,6,1],[32,13,1],[32,13,12],[32,19,12],[32,31,0],[32,31,1],[32,31,4],[32,31,9],[32,31,12],[32,31,15],[33,32,31],[34,1,0],[34,5,1],[34,9,1],[34,12,0],[34,12,1],[34,12,9],[34,13,1],[34,18,12],[34,23,9],[34,31,1],[34,31,12],[34,32,31],[35,32,31],[36,2,1],[36,6,1],[36,13,1],[36,13,12],[36,19,12],[36,31,0],[36,31,1],[36,31,9],[36,31,12]]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def count (k : Nat) : Nat := (layerData[k]!).size
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def layer (k j : Nat) : List Nat := (layerData[k]!)[j]!
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def routeData : Array (Array Nat) := #[#[0x113d7089eb644f1b227ad113c6889db434f491a7848d3b2469d1234f481a7840d3b2069d1024e581a7a38d3c1c69d8e34e871272b89385c69e8c34f061a7630d3a1849cac24e16126eb053d1629e0b14ec58a742c53d1429e0a14ec50a7428135d4],#[0x413d70827ad904f1b209eb4413c688276d074f490e9e121d3b243a744874f480e9e101d3b203a744044e580e9e8e1d3c1c3a763874e87089cae11385c3a7a3074f060e9d8c1d3a182272b044e16089bac013d1602782c04ec5809d0b013d1402782804ec5009d0a000000,0x553db1aa7b5b54f2b629eb4453c688a76d0a4f59149e32293b64427448a4f58149e30293b6042744054e58149eae293c5c5276b884e870a9cae15385c527ab0a4f16149dac213a182a72b054e160a9bac0d3d571a78ae34ed5c49d0b853d540a78a814ed50000000135d4,0x493d70927ad924f1b249eb4493c689276d0f4f499e9e133d3b267a744cf4f489e9e113d3b227a7444e4e78929e8e253c1c4a763894e870c9cce19389c4a7a3094f06129d8c253a1832733064e26000000153d162a782c54ec58a9d0b153d142a782854ec50a9d0a1135d4,0x593db1b27b5b64f2b669eb44d3c689a76d0d4f595a9e32b53b6562744ad4f585a9e30b53b61627442f3e685a9eaeb53c5d6a76bac4e875e7ccebcf89d5a7ab0b4f16169dac0000004a72b094e16129bac28bd565178aca2ed5909d0b28bd545178a8a2ed5109d0a1d35d4,0x5d3df2a27b5944f2b289ed4513ca8000001613692c26524d3b249a7449613682c26504d3b209a744124e582c26ce584c9c9a763934e87249cae49385cb09b3161326269d8c4d3a189272b124e16249bac544d96a8992d14ec5a29d0b544d94a8992914ec5229d0a4135d4],#[0x1593db1ac9ed6d64f2b5d27ad0e93c68749db4144f590a278c8513b641a9d12144f580a278c0513b601a9d10064e580a27ab8513c5c289dae0d4e8703272b819385c289eac144f160a276b0353a180c9cac064e160326eb0113d57089e2b844ed5c12742e013d54009e2a004ed50000000000000,0x18d3df2949ed64a4f2b2527b51293ca8769db41a4f690d27948393b241c9d121a4f680d27940393b201c9d10074e580d27b38693c9c1c9d8e0e4e8703a72b81d385c349ecc1a4f260727630393a180e9cac074e1603a6eb0153d970a9e4b834ec5c1a742e053d94029e4a00000000000000135d4,0x15d3db1ae9ed6d74f2b5e27ad0f13c68789db4154f590aa78c8553b641e9d12154f580aa78c0553b601e9d10084e580aa7ab8553c5c2a9dae0f4e8704272b821385c2a9eac154f160aa76b03d3a18109cac084e160426eb00d3d56069e2b034ed580000000d3d54069e2a034ed500000000935d4,0x1913df29656d6cb2b2b65a7b512d3ca87a9db41b4f690da794840ab64209d121b4f680da794040ab60209d10094e580da7b386d3c9c2055ae104e8704a72b825385c369ecc1b4f2608156b0413a18129cac094e1604a6eb0146d970a364b80000001a542e144d940a264a032ed500000001135d4,0xf93d707c9eb63e4f1b1f27ad0f93c687c9db4314f4998a784cc53b26629d13314f4898a7844c53b22629d112c4e7888a7a38453c1c229d8e114e87052733829389c229e8c114f0608a7630453a18149ccc0a4e260000000193d160c9e0b064ec5832742c193d140c9e0a064ec50327428000000,0x1613db1b09ed6d84f2b5fa7ad0fd3c687e9db4354f599aa78ccd53b66649d13354f589aa78c4d53b62649d112d4e788b27ab8593c5c2c9dae124e8705a73382d389c2c9eac164f160b276b0493a18169ccc0b4e260000000253d57129e2b894ed5c42742e1d3d540e9e2a074ed500000001935d4,0x1013d70809eb6404f1b2027ad1013c68809db4394f49dca784ee53b27729d13a14f4850a7842853b21429d10a04e7850a7a3a853c1d429d8ea14e8750273ba79389d269e8c134f0609a76304d3a18189cec00000000000002d3d16169e0b0b4ec585a742c2d3d14169e0a0b4ec505a74282935d4,0x1653db1b29ed6d94f2b60a7ad1053c68829db4264f5953278ca993b65449d12a64f5853278c2993b61449d10b13e685327aba993c5d4c9daea24e87589f33ac4f89d2e9eac174f160ba76b0000000229cac114e1608a6eb050bd56285e2b142ed586a742c50bd54285e2a142ed506a7428000000,0x1693db1b49ed6da4f2b6127ad1093c68849db4274f5953a78ca9d3b65469d12a74f5853a78c29d3b61469d10b23e6853a7aba9d3c5d4e9daea34e87591f33ac8f89d309eac184f160c276b0000000249cac124e160926eb0413d57209e2b904ed5c7a742e393d541c9e2a0e4ed500000003535d4,0x16d3db1b69ed6db4f2b61a7ad10d3c68869db4364f599b278ccd93b66669d13364f589b278c4d93b62669d112e4e789427abaa13c5d509daea44e8750a333a85189d329eac194f160ca76b0000000269ccc134e26000000058bd562c5e2b162ed5892742c58bd542c5e2a162ed509274284535d4,0x1953df2b89ed6dc4f2b6627b51313ca8889db42a4f69552794aa53b654e8d12aa4f685527942a53b614e8d10b53e685527b3aa93c9d529daea746875a9f33ad4f89d389ecc1c4f260000000613a182c9cac164e160b26eb06c7d97363e4b902ad5caa742e684d9434264a0e2ed500000005135d4,0x1993df29a9ed64d4f2b26a7b51353ca88a9db42b4f6955a794a953b254a9d12ab4f6855a7942953b214a9d109f4e6855a7b3aad3c9d4a9d8ea54e874fa733a7d389d3a9ecc1d4f260000000000000329cac194e160ca6eb0704d9638264b184ec58c2742c704d9438264a184ec50c274285d35d4,0x1753db1ba9ed6dd4f2b6327ad1193c688c9db4374f599ba78ccdd3b66689d13374f589ba78c4dd3b62689d112f4e7892a7ab8953c5c4a9dae00000019a1338cd089c4a9eac254f1612a76b00000006684cc3342261226eb0a4bd56525e2b292ed591a742ca4bd54525e2a292ed511a74288935d4,0x19d3df29c4ed6ce272b6727b51393ca88e9db4384f699c2794cdc8b666e8513384f689c27944dc8b626e8511304e78958bb3aac5c9d0000002546875b1133ad8889d563ecc2b1f2612976b00000006c84cc3642261426eb0a84d9654264b2726d593a742ca84d9454264a2726d513a74289935d4,0x1213d70909eb6484f1b2427ad1213c68909db42e3349971984cb8cb265c65132e33489719844b8cb225c65110000001727a38b93c1c5c9d8e2e4e87102133881089c5c9e8c2e4f061727630b93a184084cc2042260000000b53d165a9e0b2d4ec596a742cb53d145a9e0a2d4ec516a7428b135d4,0x1793db1bc9ed6de4f2b64a7ad1253c68929db4303359d8198cec0cb675e65139f3b588f9d8c47ceb620000002e32789b17ab8d8bc5c6c5dae334e871c9b3b885089c6c5eac362f161b176b0cd3a18726cec2142260000000d4bd566a5e2b352ed5992742cd4bd546a5e2a352ed51927428c535d4,0x1a13df29e9ed64f4f2b27a7b513d3ca80000005913692c89949053b24829d125913682c89941053b20829d103e4e582c89b39644c9c829d8e414e871f272b8f9385cb226cc59132620a7631053a187c9cac3e4e161f26eb1584d96ac264b3a4ec59d2742d584d94ac264a3a4ec51d27428000000,0x1a53df2be9ed6df4f2b6827b51413ca80000004c1f69260f949113b64849d124c1f68260f941113b60849d103f4e58260fb39307c9c889dae424e871fa72b8fd385c983ecc4c1f2622276b1093a187e9cac3f4e161fa6eb12c7d97963e4bbd4ed5de2742f287d94943e4a3b4ed50000000e935d4,0x1a93df2a49ed6524f2b2927b51493ca80000005e1369af0994d253b26929d135e1368af09945253b22929d11484e78ad89b396c4c9c869d8e434e87202733901389cb626cc5b132621a76310d3a18809ccc404e260000001604d96b0264b3f4ec59fa742d604d94b0264a3f4ec51fa7428f935d4,0x1ad3df2c09ed6e04f2b69a7b514d3ca80000004e1f69670f94b1d3b658c9d12ce1f68670f9431d3b618c9d10c93e68670fb3b387c9d8e9daec64e87649f33b24f89d9a3ecc4d1f2622a76b0000000869cac434e1621a6eb1704d96b8264b442ed5a12742d704d94b8264a442ed521274290535d4,0x1893df1c49ef6e14f2b6aa7bd0000000000000544f7930178c980bb64a69d12544f7830178c180bb60a69d10524e582a27bb980bc5cc05dae534e8729272b949385ca89eec602f1630176b14d3a18a49cac524e162926eb1453dd6be5e2b5f2ed5a82742d453dd4be5e2a5f2ed528274293d35d4,0x1443df1a21ef68000003485bd17d3c68be9db4650b792e278c9713b64b49d12650b782e278c1713b60b49d10584e583285bb9713c5cb89dae5a4e872c272b961385cca16ec5c4f162e276b1693a18b09cac584e162c26eb1902dd796562bcb2ad5eba742f8c2dd4945e2a4a2ed500000015935d4,0x1503df1a81ef68000003585bd1813c68c09db4670b7967138cb389b65ba9d12e70b7867138c3389b61ba9d10de3e687385bbb389c5d9c4daedd4e876f1f33b78f89dcc16ec4d2f1626976b0000000b69cac5b4e162da6eb1940dd6985e2b4c2ed5ad2742d940dd4985e2a4c2ed52d274296535d4,0xc43ed6621f2b310fb51887ca80000006b07693583949ad3b24d69d126b07683583941ad3b20d69d106a4e583583b39ac1c9cd69d8e6b4e8735272b9a9385cd60ecc6b072635a7631ad3a18d49cac6a4e163526eb1a41d96d20e4b694ec5b4a742da41d94d20e4a694ec534a7429a135d4]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def routeWidths : Array Nat := #[21,23,25]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def witness (k r e : Nat) : List Nat × Nat :=
  let word := ((routeData[k]!)[r]!).shiftRight (routeWidths[k]!*e) % (2^(routeWidths[k]!))
  ([word % 64, word.shiftRight 6 % 64,
    word.shiftRight 12 % 64], word.shiftRight 18)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def parentChecker (k r : Nat) : Bool :=
  checkParent edgeCount generatorCount actions (layer k r) (count (k+1))
    (layer (k+1)) (witness k r)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def generatorChecker (g : Nat) : Bool :=
  NumericPermutations.check 10 (values g) &&
    NumericPermutations.checkAction edgeCount pairs (values g) (actions g)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def baseEdges : Finset (Sym2 (Fin 10)) := represented (NumericPermutations.rawEdge (by decide) pairs) (List.range edgeCount)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def representative (k j : Nat) : Finset (Sym2 (Fin 10)) := represented (NumericPermutations.rawEdge (by decide) pairs) (layer k j)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def graph (k j : Nat) : SimpleGraph (Fin 10) := NumericPermutations.remainingGraph baseEdges (representative k j)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def baseRows : Array Nat := #[962,961,1016,1012,1004,988,959,895,767,511]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sourceRows (k j u : Nat) : Nat := DeletionRows.remaining 10 (fun v => baseRows[v]!) (DeletionRows.row pairs (layer k j)) u



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock0 : CheckedBlocks.block (generatorChecker) 56 8 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock1 : CheckedBlocks.block (generatorChecker) 56 8 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock2 : CheckedBlocks.block (generatorChecker) 56 8 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock3 : CheckedBlocks.block (generatorChecker) 56 8 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock4 : CheckedBlocks.block (generatorChecker) 56 8 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock5 : CheckedBlocks.block (generatorChecker) 56 8 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock6 : CheckedBlocks.block (generatorChecker) 56 8 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGenerators : (List.range 56).all (generatorChecker) = true := by
  apply CheckedBlocks.all_of_blocks (generatorChecker) 56 8 7 (by decide) (by decide)
  intro b hb
  interval_cases b
  · exact allGeneratorsBlock0
  · exact allGeneratorsBlock1
  · exact allGeneratorsBlock2
  · exact allGeneratorsBlock3
  · exact allGeneratorsBlock4
  · exact allGeneratorsBlock5
  · exact allGeneratorsBlock6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedEdges : NumericPermutations.checkEdgeBounds 10 edgeCount pairs = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedGenerators : NumericPermutations.checkGenerators 10 edgeCount generatorCount pairs values actions = true :=
  Bool.and_eq_true_iff.mpr ⟨checkedEdges, allGenerators⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer0Block0 : CheckedBlocks.block (parentChecker 0) 1 4 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer0 : (List.range 1).all (parentChecker 0) = true := by
  apply CheckedBlocks.all_of_blocks (parentChecker 0) 1 4 1 (by decide) (by decide)
  intro b hb
  interval_cases b
  · exact checkedLayer0Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer1Block0 : CheckedBlocks.block (parentChecker 1) 5 4 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer1Block1 : CheckedBlocks.block (parentChecker 1) 5 4 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer1 : (List.range 5).all (parentChecker 1) = true := by
  apply CheckedBlocks.all_of_blocks (parentChecker 1) 5 4 2 (by decide) (by decide)
  intro b hb
  interval_cases b
  · exact checkedLayer1Block0
  · exact checkedLayer1Block1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block0 : CheckedBlocks.block (parentChecker 2) 24 1 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block1 : CheckedBlocks.block (parentChecker 2) 24 1 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block2 : CheckedBlocks.block (parentChecker 2) 24 1 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block3 : CheckedBlocks.block (parentChecker 2) 24 1 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block4 : CheckedBlocks.block (parentChecker 2) 24 1 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block5 : CheckedBlocks.block (parentChecker 2) 24 1 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block6 : CheckedBlocks.block (parentChecker 2) 24 1 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block7 : CheckedBlocks.block (parentChecker 2) 24 1 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block8 : CheckedBlocks.block (parentChecker 2) 24 1 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block9 : CheckedBlocks.block (parentChecker 2) 24 1 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block10 : CheckedBlocks.block (parentChecker 2) 24 1 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block11 : CheckedBlocks.block (parentChecker 2) 24 1 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block12 : CheckedBlocks.block (parentChecker 2) 24 1 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block13 : CheckedBlocks.block (parentChecker 2) 24 1 13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block14 : CheckedBlocks.block (parentChecker 2) 24 1 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block15 : CheckedBlocks.block (parentChecker 2) 24 1 15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block16 : CheckedBlocks.block (parentChecker 2) 24 1 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block17 : CheckedBlocks.block (parentChecker 2) 24 1 17 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block18 : CheckedBlocks.block (parentChecker 2) 24 1 18 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block19 : CheckedBlocks.block (parentChecker 2) 24 1 19 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block20 : CheckedBlocks.block (parentChecker 2) 24 1 20 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block21 : CheckedBlocks.block (parentChecker 2) 24 1 21 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block22 : CheckedBlocks.block (parentChecker 2) 24 1 22 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2Block23 : CheckedBlocks.block (parentChecker 2) 24 1 23 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer2 : (List.range 24).all (parentChecker 2) = true := by
  apply CheckedBlocks.all_of_blocks (parentChecker 2) 24 1 24 (by decide) (by decide)
  intro b hb
  interval_cases b
  · exact checkedLayer2Block0
  · exact checkedLayer2Block1
  · exact checkedLayer2Block2
  · exact checkedLayer2Block3
  · exact checkedLayer2Block4
  · exact checkedLayer2Block5
  · exact checkedLayer2Block6
  · exact checkedLayer2Block7
  · exact checkedLayer2Block8
  · exact checkedLayer2Block9
  · exact checkedLayer2Block10
  · exact checkedLayer2Block11
  · exact checkedLayer2Block12
  · exact checkedLayer2Block13
  · exact checkedLayer2Block14
  · exact checkedLayer2Block15
  · exact checkedLayer2Block16
  · exact checkedLayer2Block17
  · exact checkedLayer2Block18
  · exact checkedLayer2Block19
  · exact checkedLayer2Block20
  · exact checkedLayer2Block21
  · exact checkedLayer2Block22
  · exact checkedLayer2Block23
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closedCoverage : checkCoverage edgeCount generatorCount depth actions count layer witness = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by decide +kernel, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk := List.mem_range.mp hk
  change k < 3 at hk
  interval_cases k
  · exact checkedLayer0
  · exact checkedLayer1
  · exact checkedLayer2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem packedCoverage (d : Finset (Sym2 (Fin 10)))
    (hd : d ⊆ baseEdges) (hk : d.card ≤ depth) :
    ∃ (p : Equiv.Perm (Fin 10)) (j : Nat),
      baseEdges.map (NumericPermutations.sym2Perm p).toEmbedding = baseEdges ∧
      j < count d.card ∧ representative d.card j = d.map (NumericPermutations.sym2Perm p).toEmbedding :=
  NumericPermutations.checked_vertex_orbit_coverage 10 edgeCount generatorCount depth
    (by decide) pairs values actions count layer witness checkedGenerators closedCoverage d hd hk
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validLayersChecked : (List.range (depth+1)).all (fun k =>
    (List.range (count k)).all (fun j => valid edgeCount (layer k j))) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem layer_index_bound (k j : Nat) (hk : k ≤ depth) (hj : j < count k) :
    ∀ i ∈ layer k j, i < edgeCount := by
  have h := List.all_eq_true.mp validLayersChecked k (List.mem_range.mpr (by omega))
  exact (valid_iff _ _).mp (List.all_eq_true.mp h j (List.mem_range.mpr hj))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedNoLoops : NumericPermutations.checkNoLoops edgeCount pairs = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedBaseRows : (List.range 10).all (fun u => baseRows[u]! == DeletionRows.row pairs (List.range edgeCount) u) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem baseRow_value (u : Nat) (hu : u < 10) :
    baseRows[u]! = DeletionRows.row pairs (List.range edgeCount) u := by
  simpa using List.all_eq_true.mp checkedBaseRows u (List.mem_range.mpr hu)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem graph_adj_iff (k j : Nat) (hk : k ≤ depth) (hj : j < count k) (u v : Fin 10) :
    (graph k j).Adj u v ↔ (sourceRows k j u.val).testBit v.val = true := by
  have h := NumericPermutations.deleted_graph_row (by decide : 0 < 10) pairs
    (List.range edgeCount) (layer k j)
    (fun i hi => NumericPermutations.checked_edge_bounds checkedEdges (List.mem_range.mp hi))
    (fun i hi => NumericPermutations.checked_edge_bounds checkedEdges (layer_index_bound k j hk hj i hi))
    (fun i hi => NumericPermutations.checked_no_loops checkedNoLoops (List.mem_range.mp hi)) u v
  change (graph k j).Adj u v ↔
    (DeletionRows.remaining 10 (DeletionRows.row pairs (List.range edgeCount))
      (DeletionRows.row pairs (layer k j)) u.val).testBit v.val = true at h
  simpa only [sourceRows, DeletionRows.remaining, baseRow_value u.val u.isLt] using h
end Order10Orbit.A02404


namespace Order10Orbit.A03304
open ListEncodedOrbit
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgeCount : Nat := 36
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def depth : Nat := 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def generatorCount : Nat := 39
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgePairs : Array (Nat × Nat) := #[(0,1),(0,2),(0,6),(0,7),(0,8),(0,9),(1,2),(1,6),(1,7),(1,8),(1,9),(2,6),(2,7),(2,8),(2,9),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(4,5),(4,6),(4,7),(4,8),(4,9),(5,6),(5,7),(5,8),(5,9),(6,7),(6,8),(6,9),(7,8),(7,9),(8,9)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pairs (i : Nat) : Nat × Nat := edgePairs[i]!
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def vertexWords : Array Nat := #[646515536400,654568600080,654819152400,654820258050,654820258320,654820258320,654820258305,654820257810,654820258305,654820258320,654820258080,654820257810,654820258080,654820258320,654820258320,654820196880,654818169360,654820196880,654820258320,654819275280,654818169360,654819275280,654820258320,654820258320,654568600080,646263878160,448712159760,654568600080,654820258320,650793726480,517918175760,646263878160,650793726480,654820258320,590395748880,448712159760,517918175760,590395748880,654820258320]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgeIndices : Array Nat := #[91211263300866084,0x289207924906900,0x38d30b924924181,0x51349140f924924,0x6585d65643e4924,0x75c6da915424924,0x81f7a469644b1c2,0x8a191e6d748c203,0x8e485f7184cd244,0x9238a075950e285]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def values (g v : Nat) : Nat := (vertexWords[g]!).shiftRight (4*v) % 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def actions (g i : Nat) : Nat :=
  let p := pairs i
  (edgeIndices[values g p.1]!).shiftRight (6*values g p.2) % 64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def layerData : Array (Array (List Nat)) := #[#[[]],#[[0],[2],[15],[17],[30]],#[[1,0],[2,0],[3,2],[7,2],[8,2],[11,0],[15,0],[15,2],[16,15],[17,0],[17,2],[17,15],[18,2],[18,17],[22,17],[23,17],[26,15],[30,0],[30,2],[30,15],[30,17],[31,30],[33,2],[33,17],[35,30]]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def count (k : Nat) : Nat := (layerData[k]!).size
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def layer (k j : Nat) : List Nat := (layerData[k]!)[j]!
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def routeData : Array (Array Nat) := #[#[0x8248fc1246e09037049178240bc11c5d891a8c47d46236a311751891a2c47d162368b1174508aa2c48ce623e7311b3988b9c8454e4224711232c88f96446cb222e591232088f90446c8222e4010c208918a447c5223629117140860a04245],#[0x88923f11246e2240dc4491788902f111c5d2246a2447d4488da891175122468a447d1488da2911744c22a8a448ce488f9c911b39222e718454e30891c512334a23e69446cd288b9a112320223e40446c8088b90010d20224628447c5088d8a111714021a2800000,0xb092c1612572c242e48491790902f211c5d8248a304814608e28a1175182488b04811608e22a11744e22a8b0490e60901cc11c39422e71c454e38891c4124308240610470c188b9841242482404904709188b9250cd2442482884805108e0a00000022182844245,0x98923f31246e6240dcc491798902f311c5e0246b4047d6808dad01175962468ac47d1588da2b11745022c8ac48ce588f9cb11b39622e720458e00000071232ce23e59c46cb388b96712320e23e41c46c8388b90610c20e24629c47c5388d8a711714c2182984245,0xb892c1712572e242e504917a0902f411c5de248abc4815788e2ae11755e24893c4812788e24e1174a012c934490e68901cd11c38000002c454e58891cc0642d80c05b0170b508b96c0642180c04301708508b90910c2180c82b01805602e0aa1171522182a44245,0xc0934351256ea242dd44957a890ae000002e04aa5c0854a08da9411752e04a8dc0851a08da3411746622a8dc094eb8109d411b3a822e74c454e98891d60252ec0425c846cb908b97602522c04244846c8908b91110c22c04a2d80845908d8b21171622182c44245]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def routeWidths : Array Nat := #[21,23]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def witness (k r e : Nat) : List Nat × Nat :=
  let word := ((routeData[k]!)[r]!).shiftRight (routeWidths[k]!*e) % (2^(routeWidths[k]!))
  ([word % 64, word.shiftRight 6 % 64,
    word.shiftRight 12 % 64], word.shiftRight 18)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def parentChecker (k r : Nat) : Bool :=
  checkParent edgeCount generatorCount actions (layer k r) (count (k+1))
    (layer (k+1)) (witness k r)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def generatorChecker (g : Nat) : Bool :=
  NumericPermutations.check 10 (values g) &&
    NumericPermutations.checkAction edgeCount pairs (values g) (actions g)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def baseEdges : Finset (Sym2 (Fin 10)) := represented (NumericPermutations.rawEdge (by decide) pairs) (List.range edgeCount)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def representative (k j : Nat) : Finset (Sym2 (Fin 10)) := represented (NumericPermutations.rawEdge (by decide) pairs) (layer k j)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def graph (k j : Nat) : SimpleGraph (Fin 10) := NumericPermutations.remainingGraph baseEdges (representative k j)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def baseRows : Array Nat := #[966,965,963,1008,1000,984,959,895,767,511]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sourceRows (k j u : Nat) : Nat := DeletionRows.remaining 10 (fun v => baseRows[v]!) (DeletionRows.row pairs (layer k j)) u



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock0 : CheckedBlocks.block (generatorChecker) 39 8 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock1 : CheckedBlocks.block (generatorChecker) 39 8 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock2 : CheckedBlocks.block (generatorChecker) 39 8 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock3 : CheckedBlocks.block (generatorChecker) 39 8 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock4 : CheckedBlocks.block (generatorChecker) 39 8 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGenerators : (List.range 39).all (generatorChecker) = true := by
  apply CheckedBlocks.all_of_blocks (generatorChecker) 39 8 5 (by decide) (by decide)
  intro b hb
  interval_cases b
  · exact allGeneratorsBlock0
  · exact allGeneratorsBlock1
  · exact allGeneratorsBlock2
  · exact allGeneratorsBlock3
  · exact allGeneratorsBlock4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedEdges : NumericPermutations.checkEdgeBounds 10 edgeCount pairs = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedGenerators : NumericPermutations.checkGenerators 10 edgeCount generatorCount pairs values actions = true :=
  Bool.and_eq_true_iff.mpr ⟨checkedEdges, allGenerators⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer0Block0 : CheckedBlocks.block (parentChecker 0) 1 4 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer0 : (List.range 1).all (parentChecker 0) = true := by
  apply CheckedBlocks.all_of_blocks (parentChecker 0) 1 4 1 (by decide) (by decide)
  intro b hb
  interval_cases b
  · exact checkedLayer0Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer1Block0 : CheckedBlocks.block (parentChecker 1) 5 4 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer1Block1 : CheckedBlocks.block (parentChecker 1) 5 4 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer1 : (List.range 5).all (parentChecker 1) = true := by
  apply CheckedBlocks.all_of_blocks (parentChecker 1) 5 4 2 (by decide) (by decide)
  intro b hb
  interval_cases b
  · exact checkedLayer1Block0
  · exact checkedLayer1Block1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closedCoverage : checkCoverage edgeCount generatorCount depth actions count layer witness = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by decide +kernel, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk := List.mem_range.mp hk
  change k < 2 at hk
  interval_cases k
  · exact checkedLayer0
  · exact checkedLayer1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem packedCoverage (d : Finset (Sym2 (Fin 10)))
    (hd : d ⊆ baseEdges) (hk : d.card ≤ depth) :
    ∃ (p : Equiv.Perm (Fin 10)) (j : Nat),
      baseEdges.map (NumericPermutations.sym2Perm p).toEmbedding = baseEdges ∧
      j < count d.card ∧ representative d.card j = d.map (NumericPermutations.sym2Perm p).toEmbedding :=
  NumericPermutations.checked_vertex_orbit_coverage 10 edgeCount generatorCount depth
    (by decide) pairs values actions count layer witness checkedGenerators closedCoverage d hd hk
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validLayersChecked : (List.range (depth+1)).all (fun k =>
    (List.range (count k)).all (fun j => valid edgeCount (layer k j))) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem layer_index_bound (k j : Nat) (hk : k ≤ depth) (hj : j < count k) :
    ∀ i ∈ layer k j, i < edgeCount := by
  have h := List.all_eq_true.mp validLayersChecked k (List.mem_range.mpr (by omega))
  exact (valid_iff _ _).mp (List.all_eq_true.mp h j (List.mem_range.mpr hj))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedNoLoops : NumericPermutations.checkNoLoops edgeCount pairs = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedBaseRows : (List.range 10).all (fun u => baseRows[u]! == DeletionRows.row pairs (List.range edgeCount) u) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem baseRow_value (u : Nat) (hu : u < 10) :
    baseRows[u]! = DeletionRows.row pairs (List.range edgeCount) u := by
  simpa using List.all_eq_true.mp checkedBaseRows u (List.mem_range.mpr hu)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem graph_adj_iff (k j : Nat) (hk : k ≤ depth) (hj : j < count k) (u v : Fin 10) :
    (graph k j).Adj u v ↔ (sourceRows k j u.val).testBit v.val = true := by
  have h := NumericPermutations.deleted_graph_row (by decide : 0 < 10) pairs
    (List.range edgeCount) (layer k j)
    (fun i hi => NumericPermutations.checked_edge_bounds checkedEdges (List.mem_range.mp hi))
    (fun i hi => NumericPermutations.checked_edge_bounds checkedEdges (layer_index_bound k j hk hj i hi))
    (fun i hi => NumericPermutations.checked_no_loops checkedNoLoops (List.mem_range.mp hi)) u v
  change (graph k j).Adj u v ↔
    (DeletionRows.remaining 10 (DeletionRows.row pairs (List.range edgeCount))
      (DeletionRows.row pairs (layer k j)) u.val).testBit v.val = true at h
  simpa only [sourceRows, DeletionRows.remaining, baseRow_value u.val u.isLt] using h
end Order10Orbit.A03304


namespace Order10Orbit.A04114
open ListEncodedOrbit
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgeCount : Nat := 36
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def depth : Nat := 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def generatorCount : Nat := 39
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgePairs : Array (Nat × Nat) := #[(0,1),(0,2),(0,3),(0,5),(0,6),(0,7),(0,8),(0,9),(1,2),(1,3),(1,5),(1,6),(1,7),(1,8),(1,9),(2,3),(2,5),(2,6),(2,7),(2,8),(2,9),(3,5),(3,6),(3,7),(3,8),(3,9),(4,6),(4,7),(4,8),(4,9),(6,7),(6,8),(6,9),(7,8),(7,9),(8,9)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pairs (i : Nat) : Nat × Nat := edgePairs[i]!
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def vertexWords : Array Nat := #[646515536400,654568600080,654820258050,654820258305,654820258320,654820258320,654820258305,654820257810,654820246035,654820258305,654820258320,654820258080,654820250160,654820257810,654820258080,654820258320,654820254480,654820246035,654820250160,654820254480,654820258320,654820258320,654820258320,654820258320,654568600080,646263878160,448712159760,654568600080,654820258320,650793726480,517918175760,646263878160,650793726480,654820258320,590395748880,448712159760,517918175760,590395748880,654820258320]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgeIndices : Array Nat := #[0x1c61440e4081024,0x38d30b2a4248900,0x5134914243e4201,0x6585d656490f242,0x75c6da924924924,0x924924924550283,0x81f7a491a5912c4,0x8a191e91b5d2305,0x8e485f91c613346,0x9238a091d654387]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def values (g v : Nat) : Nat := (vertexWords[g]!).shiftRight (4*v) % 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgeActionWords : Array Nat := #[0x8237e27a175a71b6566175544534903ce2cd30a2481c41850c2040,0x8e07e285e75c69b6585975544d14903ce34b30a2481c61050c2040,0x8e28607de75c6da6585d654e34c2ca24718510308051349140f201,0x8e28607de75c6da6585d65544d24503c718510308138d30b289200,0x8e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x8e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x8e28607de75c6da6585d65544d24503c718510308138d30b289200,0x8e28607de75c6da6585d654718510308e34c2ca24051349140f048,0x8e28607de75c6da1c61440d44d245004e34c2ca0086585d65423c9,0x8e28607de75c6da6585d65544d24503c718510308138d30b289200,0x8e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x8e28607de75c6da6585d654e34c2ca2544d24503c81c61440c2001,0x8e28607de75c6da38d30b2944d245021961759524f1c61440c0042,0x8e28607de75c6da6585d654718510308e34c2ca24051349140f048,0x8e28607de75c6da6585d654e34c2ca2544d24503c81c61440c2001,0x8e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x8e28607de75c6da5134914196175953ce34c2ca2091c61440c1080,0x8e28607de75c6da1c61440d44d245004e34c2ca0086585d65423c9,0x8e28607de75c6da38d30b2944d245021961759524f1c61440c0042,0x8e28607de75c6da5134914196175953ce34c2ca2091c61440c1080,0x8e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x8e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x8e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x8e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x8e07e285e75c69b6585975544d14903ce34b30a2481c61050c2040,0x8227a37e175a6dc6565d85544524d03ce2cc34a2481c41460c2040,0x7de8608e269c6dd5985d95514d25103cb34c38a2481061470c2040,0x8e07e285e75c69b6585975544d14903ce34b30a2481c61050c2040,0x8e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x8a386079f75b71a6576165544934503ce30d2ca2481c51840c2040,0x8628de7e06dc75a5d86565524d44503cc34e2ca2481461c40c2040,0x8227a37e175a6dc6565d85544524d03ce2cc34a2481c41460c2040,0x8a386079f75b71a6576165544934503ce30d2ca2481c51840c2040,0x8e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x8e189f81e71d6da6195d65535124503cd38c2ca2481871440c2040,0x7de8608e269c6dd5985d95514d25103cb34c38a2481061470c2040,0x8628de7e06dc75a5d86565524d44503cc34e2ca2481461c40c2040,0x8e189f81e71d6da6195d65535124503cd38c2ca2481871440c2040,0x8e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def actions (g i : Nat) : Nat := (edgeActionWords[g]!).shiftRight (6*i) % 64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def layerData : Array (Array (List Nat)) := #[#[[]],#[[0],[3],[4],[26],[30]],#[[1,0],[3,0],[4,0],[4,3],[5,4],[10,3],[11,3],[11,4],[12,4],[15,0],[16,0],[17,0],[26,0],[26,3],[26,4],[27,4],[27,26],[30,0],[30,3],[30,4],[30,26],[31,30],[33,4],[33,26],[35,30]]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def count (k : Nat) : Nat := (layerData[k]!).size
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def layer (k j : Nat) : List Nat := (layerData[k]!)[j]!
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def routeData : Array (Array Nat) := #[#[0x8248fc1246e09037049178240bc11c5d891aac47d56236ab11755091a2847d142368a1174488b22848cd423e6a11b3508b9a4458d02246a1232508f92846c9422e4911624089120438942462a11f1508d8a845c5222c28112140870a04285],#[0x88923f11246e2240dc4491788902f111c5d8246ab047d5608daac1175562469ac47d3588da6b1174d422c9ac48cf588f9eb11b3d622e7a8458f488a1e212324423e48846c9108b92111624022648043c910918a211f14423628845c5088b0a011314021e2800000,0x90923f21246e4240dc8491790902f211c5da246ab447d5688daad11754c24691847d2308da4611748a22c91848ce308f9c611b38c22e714458e50499c612328c23e51846ca308b94511629412652823ca18918a311f14623628c45c5000000111214221c2844285,0xb092c1612572c242e4c491798902f311c5de248abc4815788e2ae1175502489204812408e24711748c1ac920490e40901c811c38e22e718358e58499c8124290240520470a388b9460d629612652c23ca20920a41201482382800000188b0a211214421c2884285,0xb892c1712572e242e504917a0902f411c5e0248ac04815808e2a000001e0c88bc1811782e22e11745a22c8bc190d78301af05c35c22e6b4458d60891af06425e0c04bc1709708b92d1162582244b0438978320af06015e0b82b845c5688b0ac11215821c2b04285,0xc0934351256ea242dd44957a890ae000002e04aadc0855a08dab411756c04a8d80851988da3311746422c8d8094db0109b311b36622e6c8458d88891b602526c0424cc46c9988b9321162622244c44389b0128b60211662362cc45c5908b0b111216221c2c44285]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def routeWidths : Array Nat := #[21,23]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def witness (k r e : Nat) : List Nat × Nat :=
  let word := ((routeData[k]!)[r]!).shiftRight (routeWidths[k]!*e) % (2^(routeWidths[k]!))
  ([word % 64, word.shiftRight 6 % 64,
    word.shiftRight 12 % 64], word.shiftRight 18)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def parentChecker (k r : Nat) : Bool :=
  checkParent edgeCount generatorCount actions (layer k r) (count (k+1))
    (layer (k+1)) (witness k r)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def generatorChecker (g : Nat) : Bool :=
  NumericPermutations.check 10 (values g) &&
    NumericPermutations.checkAction edgeCount pairs (values g) (actions g)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def baseEdges : Finset (Sym2 (Fin 10)) := represented (NumericPermutations.rawEdge (by decide) pairs) (List.range edgeCount)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def representative (k j : Nat) : Finset (Sym2 (Fin 10)) := represented (NumericPermutations.rawEdge (by decide) pairs) (layer k j)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def graph (k j : Nat) : SimpleGraph (Fin 10) := NumericPermutations.remainingGraph baseEdges (representative k j)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def baseRows : Array Nat := #[1006,1005,1003,999,960,15,927,863,735,479]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sourceRows (k j u : Nat) : Nat := DeletionRows.remaining 10 (fun v => baseRows[v]!) (DeletionRows.row pairs (layer k j)) u



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock0 : CheckedBlocks.block (generatorChecker) 39 8 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock1 : CheckedBlocks.block (generatorChecker) 39 8 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock2 : CheckedBlocks.block (generatorChecker) 39 8 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock3 : CheckedBlocks.block (generatorChecker) 39 8 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGeneratorsBlock4 : CheckedBlocks.block (generatorChecker) 39 8 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allGenerators : (List.range 39).all (generatorChecker) = true := by
  apply CheckedBlocks.all_of_blocks (generatorChecker) 39 8 5 (by decide) (by decide)
  intro b hb
  interval_cases b
  · exact allGeneratorsBlock0
  · exact allGeneratorsBlock1
  · exact allGeneratorsBlock2
  · exact allGeneratorsBlock3
  · exact allGeneratorsBlock4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedEdges : NumericPermutations.checkEdgeBounds 10 edgeCount pairs = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedGenerators : NumericPermutations.checkGenerators 10 edgeCount generatorCount pairs values actions = true :=
  Bool.and_eq_true_iff.mpr ⟨checkedEdges, allGenerators⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer0Block0 : CheckedBlocks.block (parentChecker 0) 1 4 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer0 : (List.range 1).all (parentChecker 0) = true := by
  apply CheckedBlocks.all_of_blocks (parentChecker 0) 1 4 1 (by decide) (by decide)
  intro b hb
  interval_cases b
  · exact checkedLayer0Block0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer1Block0 : CheckedBlocks.block (parentChecker 1) 5 4 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer1Block1 : CheckedBlocks.block (parentChecker 1) 5 4 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedLayer1 : (List.range 5).all (parentChecker 1) = true := by
  apply CheckedBlocks.all_of_blocks (parentChecker 1) 5 4 2 (by decide) (by decide)
  intro b hb
  interval_cases b
  · exact checkedLayer1Block0
  · exact checkedLayer1Block1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closedCoverage : checkCoverage edgeCount generatorCount depth actions count layer witness = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by decide +kernel, ?_⟩
  apply List.all_eq_true.mpr
  intro k hk
  have hk := List.mem_range.mp hk
  change k < 2 at hk
  interval_cases k
  · exact checkedLayer0
  · exact checkedLayer1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem packedCoverage (d : Finset (Sym2 (Fin 10)))
    (hd : d ⊆ baseEdges) (hk : d.card ≤ depth) :
    ∃ (p : Equiv.Perm (Fin 10)) (j : Nat),
      baseEdges.map (NumericPermutations.sym2Perm p).toEmbedding = baseEdges ∧
      j < count d.card ∧ representative d.card j = d.map (NumericPermutations.sym2Perm p).toEmbedding :=
  NumericPermutations.checked_vertex_orbit_coverage 10 edgeCount generatorCount depth
    (by decide) pairs values actions count layer witness checkedGenerators closedCoverage d hd hk
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validLayersChecked : (List.range (depth+1)).all (fun k =>
    (List.range (count k)).all (fun j => valid edgeCount (layer k j))) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem layer_index_bound (k j : Nat) (hk : k ≤ depth) (hj : j < count k) :
    ∀ i ∈ layer k j, i < edgeCount := by
  have h := List.all_eq_true.mp validLayersChecked k (List.mem_range.mpr (by omega))
  exact (valid_iff _ _).mp (List.all_eq_true.mp h j (List.mem_range.mpr hj))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedNoLoops : NumericPermutations.checkNoLoops edgeCount pairs = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedBaseRows : (List.range 10).all (fun u => baseRows[u]! == DeletionRows.row pairs (List.range edgeCount) u) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem baseRow_value (u : Nat) (hu : u < 10) :
    baseRows[u]! = DeletionRows.row pairs (List.range edgeCount) u := by
  simpa using List.all_eq_true.mp checkedBaseRows u (List.mem_range.mpr hu)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem graph_adj_iff (k j : Nat) (hk : k ≤ depth) (hj : j < count k) (u v : Fin 10) :
    (graph k j).Adj u v ↔ (sourceRows k j u.val).testBit v.val = true := by
  have h := NumericPermutations.deleted_graph_row (by decide : 0 < 10) pairs
    (List.range edgeCount) (layer k j)
    (fun i hi => NumericPermutations.checked_edge_bounds checkedEdges (List.mem_range.mp hi))
    (fun i hi => NumericPermutations.checked_edge_bounds checkedEdges (layer_index_bound k j hk hj i hi))
    (fun i hi => NumericPermutations.checked_no_loops checkedNoLoops (List.mem_range.mp hi)) u v
  change (graph k j).Adj u v ↔
    (DeletionRows.remaining 10 (DeletionRows.row pairs (List.range edgeCount))
      (DeletionRows.row pairs (layer k j)) u.val).testBit v.val = true at h
  simpa only [sourceRows, DeletionRows.remaining, baseRow_value u.val u.isLt] using h
end Order10Orbit.A04114

-- two additional hosts and common-neighbor bounds
namespace BoolCliqueCover
variable {V : Type*} [LinearOrder V]

/-- All clique branches must end in an accepted vertex list. The evaluator
uses only lists and Booleans; no finite-set union or proof data is built. -/
def check (adj : V → V → Bool) (accept : List V → Bool) :
    ℕ → List V → List V → Bool
  | 0, _, picked => accept picked
  | k + 1, candidates, picked =>
      candidates.all fun v =>
        check adj accept k
          (candidates.filter fun w => decide (v < w) && adj v w) (v :: picked)

/-- The Boolean adjacency may overapproximate the graph: only preservation
of actual edges is needed for the covering conclusion. -/
theorem complete (G : SimpleGraph V) (adj : V → V → Bool)
    (edges : ∀ v w, G.Adj v w → adj v w = true)
    (accept : List V → Bool) (k : ℕ) (candidates picked : List V)
    (s : Finset V) (checked : check adj accept k candidates picked = true)
    (sub : s ⊆ candidates.toFinset) (clique : G.IsNClique k s) :
    ∃ out : List V, accept out = true ∧ out.toFinset = s ∪ picked.toFinset := by
  induction k generalizing candidates picked s with
  | zero =>
      have hs : s = ∅ := Finset.card_eq_zero.mp clique.card_eq
      subst s
      exact ⟨picked, checked, by simp⟩
  | succ k ih =>
      have hn : s.Nonempty := Finset.card_pos.mp (by
        rw [clique.card_eq]
        exact Nat.succ_pos k)
      let v := s.min' hn
      have hv : v ∈ s := Finset.min'_mem s hn
      have hvc : v ∈ candidates := List.mem_toFinset.mp (sub hv)
      have hc := (List.all_eq_true.mp checked) v hvc
      have hsub : s.erase v ⊆
          (candidates.filter fun w => decide (v < w) && adj v w).toFinset := by
        intro w hw
        have hws : w ∈ s := Finset.mem_of_mem_erase hw
        have hvw : v < w := Finset.min'_lt_of_mem_erase_min' s hn hw
        simp only [List.mem_toFinset, List.mem_filter, Bool.and_eq_true,
          decide_eq_true_eq]
        exact ⟨List.mem_toFinset.mp (sub hws), hvw,
          edges v w (clique.isClique hv hws (ne_of_lt hvw))⟩
      have hclique : G.IsNClique k (s.erase v) := by
        simpa using clique.erase_of_mem hv
      obtain ⟨out, ha, hout⟩ := ih _ (v :: picked) (s.erase v) hc hsub hclique
      refine ⟨out, ha, ?_⟩
      rw [hout]
      ext w
      by_cases hw : w = v <;> simp [hw, hv]

end BoolCliqueCover


namespace CrossObstruction
open Finset SimpleGraph

def crossCount {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s t : Finset V) : Nat :=
  ((s ×ˢ t).filter fun p => G.Adj p.1 p.2).card

def prodEmbedding {V W : Type*} (f : V ↪ W) : V × V ↪ W × W where
  toFun p := (f p.1, f p.2)
  inj' := by
    intro a b h
    exact Prod.ext (f.injective (congrArg Prod.fst h))
      (f.injective (congrArg Prod.snd h))

theorem crossCount_map_le {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : V ↪ W) (hom : ∀ u v, G.Adj u v → H.Adj (f u) (f v))
    (s t : Finset V) : crossCount G s t ≤ crossCount H (s.map f) (t.map f) := by
  have sub : (((s ×ˢ t).filter fun p => G.Adj p.1 p.2).map (prodEmbedding f)) ⊆
      (((s.map f) ×ˢ (t.map f)).filter fun p => H.Adj p.1 p.2) := by
    intro p hp
    obtain ⟨⟨u,v⟩,huv,rfl⟩ := mem_map.mp hp
    obtain ⟨huv,hadj⟩ := mem_filter.mp huv
    obtain ⟨hu,hv⟩ := mem_product.mp huv
    exact mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_map.mpr ⟨u,hu,rfl⟩,mem_map.mpr ⟨v,hv,rfl⟩⟩,hom u v hadj⟩
  simpa only [card_map, crossCount] using card_le_card sub

theorem clique_pair_cross_bound {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : V ↪ W) (hom : ∀ u v, G.Adj u v → H.Adj (f u) (f v))
    (k overlap bound : Nat)
    (host_bound : ∀ a b : Finset W, H.IsNClique k a → H.IsNClique k b →
      (a ∩ b).card = overlap → crossCount H (a \ b) (b \ a) ≤ bound)
    {s t : Finset V} (hs : G.IsNClique k s) (ht : G.IsNClique k t)
    (hi : (s ∩ t).card = overlap) : crossCount G (s \ t) (t \ s) ≤ bound := by
  have hmap : G.map f ≤ H := by
    rw [map_le_iff_le_comap]
    exact hom
  have hb := host_bound (s.map f) (t.map f)
    (IsNClique.mono hmap hs.map) (IsNClique.mono hmap ht.map)
    (by simpa only [← map_inter, card_map] using hi)
  have hc := crossCount_map_le G H f hom (s \ t) (t \ s)
  rw [← Finset.map_sdiff, ← Finset.map_sdiff] at hb
  exact hc.trans hb

theorem no_embedding_clique_pair {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (k overlap bound : Nat)
    (host_bound : ∀ a b : Finset W, H.IsNClique k a → H.IsNClique k b →
      (a ∩ b).card = overlap → crossCount H (a \ b) (b \ a) ≤ bound)
    {s t : Finset V} (hs : G.IsNClique k s) (ht : G.IsNClique k t)
    (hi : (s ∩ t).card = overlap) (large : bound < crossCount G (s \ t) (t \ s)) :
    ¬ ∃ f : V ↪ W, ∀ u v, G.Adj u v → H.Adj (f u) (f v) := by
  rintro ⟨f,hf⟩
  exact (Nat.not_lt_of_ge (clique_pair_cross_bound G H f hf k overlap bound
    host_bound hs ht hi)) large

def maskList (n mask : Nat) : List Nat := (List.range n).filter mask.testBit

def maskSet (n mask : Nat) : Finset Nat := (maskList n mask).toFinset

def listMask : List Nat → Nat
  | [] => 0
  | v::rest => 2^v ||| listMask rest

theorem listMask_bit (xs : List Nat) (v : Nat) :
    (listMask xs).testBit v = true ↔ v ∈ xs := by
  induction xs with
  | nil => simp [listMask]
  | cons x xs ih =>
    rw [listMask, Nat.testBit_or, Nat.testBit_two_pow]
    rw [Bool.or_eq_true_iff, decide_eq_true_eq, ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

theorem mem_maskSet (n mask v : Nat) :
    v ∈ maskSet n mask ↔ v < n ∧ mask.testBit v = true := by
  simp [maskSet, maskList]

theorem maskSet_and (n a b : Nat) : maskSet n (a &&& b) = maskSet n a ∩ maskSet n b := by
  ext v
  simp [mem_maskSet, Nat.testBit_and, and_assoc]
  exact fun hv _ _ => hv

def minusMask (n a b : Nat) : Nat := a &&& ((2^n-1) ^^^ b)

theorem maskSet_minus (n a b : Nat) :
    maskSet n (minusMask n a b) = maskSet n a \ maskSet n b := by
  ext v
  by_cases hv : v < n
  · simp [mem_maskSet, minusMask, Nat.testBit_and, Nat.testBit_xor, hv]
  · simp [mem_maskSet, hv]

theorem maskList_nodup (n mask : Nat) : (maskList n mask).Nodup :=
  (List.nodup_range (n := n)).filter _

theorem maskList_length (n mask : Nat) : (maskList n mask).length = (maskSet n mask).card :=
  (List.toFinset_card_of_nodup (maskList_nodup n mask)).symm

def rawCross (rows : Nat → Nat) (n a b : Nat) : Nat :=
  (((maskList n a) ×ˢ (maskList n b)).filter fun p => (rows p.1).testBit p.2).length

theorem rawCross_eq (G : SimpleGraph Nat) [DecidableRel G.Adj]
    (rows : Nat → Nat) (n a b : Nat)
    (edges : ∀ u v, u < n → v < n → (G.Adj u v ↔ (rows u).testBit v = true)) :
    rawCross rows n a b = crossCount G (maskSet n a) (maskSet n b) := by
  have heq : (((maskList n a) ×ˢ (maskList n b)).filter
      fun p => (rows p.1).testBit p.2).toFinset =
      (((maskSet n a) ×ˢ (maskSet n b)).filter fun p => G.Adj p.1 p.2) := by
    ext p
    rcases p with ⟨u,v⟩
    simp only [List.mem_toFinset, List.mem_filter, List.mem_product, mem_filter, mem_product,
      maskSet]
    constructor
    · rintro ⟨⟨hu,hv⟩,he⟩
      exact ⟨⟨hu,hv⟩,(edges u v ((List.mem_filter.mp hu).1 |> List.mem_range.mp)
        ((List.mem_filter.mp hv).1 |> List.mem_range.mp)).mpr he⟩
    · rintro ⟨⟨hu,hv⟩,he⟩
      exact ⟨⟨hu,hv⟩,(edges u v ((List.mem_filter.mp hu).1 |> List.mem_range.mp)
        ((List.mem_filter.mp hv).1 |> List.mem_range.mp)).mp he⟩
  have hn := ((maskList_nodup n a).product (maskList_nodup n b)).filter
    (fun p => (rows p.1).testBit p.2)
  have hc := List.toFinset_card_of_nodup hn
  rw [heq] at hc
  exact hc.symm

end CrossObstruction


namespace CommonObstruction
open Finset SimpleGraph

def commonSet {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (domain s : Finset V) : Finset V :=
  domain.filter fun v => ∀ u ∈ s, G.Adj u v

theorem commonSet_map_le {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : V ↪ W) (hom : ∀ u v, G.Adj u v → H.Adj (f u) (f v))
    (domain : Finset V) (targetDomain : Finset W) (s : Finset V)
    (domain_sub : ∀ v ∈ domain, f v ∈ targetDomain) :
    (commonSet G domain s).card ≤ (commonSet H targetDomain (s.map f)).card := by
  have sub : (commonSet G domain s).map f ⊆ commonSet H targetDomain (s.map f) := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hw
    obtain ⟨hvd,hvadj⟩ := mem_filter.mp hv
    apply mem_filter.mpr
    refine ⟨domain_sub v hvd, ?_⟩
    intro x hx
    obtain ⟨u,hu,rfl⟩ := mem_map.mp hx
    exact hom u v (hvadj u hu)
  simpa only [card_map] using card_le_card sub

theorem no_embedding_common {V W : Type*} [DecidableEq V] [DecidableEq W]
    [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (k bound : Nat)
    (host_bound : ∀ s : Finset W, H.IsNClique k s → (commonSet H univ s).card ≤ bound)
    {s : Finset V} (hs : G.IsNClique k s) (large : bound < (commonSet G univ s).card) :
    ¬ ∃ f : V ↪ W, ∀ u v, G.Adj u v → H.Adj (f u) (f v) := by
  rintro ⟨f,hom⟩
  have hmap : G.map f ≤ H := by
    rw [map_le_iff_le_comap]
    exact hom
  have hb := host_bound (s.map f) (IsNClique.mono hmap hs.map)
  have hc := commonSet_map_le G H f hom univ univ s (by simp)
  exact (Nat.not_lt_of_ge (hc.trans hb)) large

def commonMask (n : Nat) (rows : Nat → Nat) : List Nat → Nat
  | [] => 2^n-1
  | v::rest => rows v &&& commonMask n rows rest

theorem commonMask_bit (n : Nat) (rows : Nat → Nat) (xs : List Nat) (v : Nat) :
    (commonMask n rows xs).testBit v = true ↔
      v < n ∧ ∀ u ∈ xs, (rows u).testBit v = true := by
  induction xs with
  | nil => simp [commonMask]
  | cons u xs ih =>
    simp [commonMask, Nat.testBit_and, ih, and_assoc, and_left_comm, and_comm]

end CommonObstruction

namespace Order10Common
open CrossObstruction CommonObstruction Finset SimpleGraph
def rows : List Nat := [493502, 505981, 64443, 292727, 159471, 89567, 490554, 249653, 382637, 451997, 476153, 258294, 387438, 449118, 16380, 473991, 433635, 372435, 243531]
def row (i : Nat) : Nat := rows.getD i 0
def target : SimpleGraph (Fin 19) where
  Adj i j := (row i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel target.Adj := fun i j =>
  inferInstanceAs (Decidable ((row i.val).testBit j.val = true))
abbrev natTarget : SimpleGraph Nat := target.map Fin.valEmbedding
def rawAdj (u v : Nat) : Bool := (row u).testBit v

theorem nat_edges (u v : Nat) (h : natTarget.Adj u v) : rawAdj u v = true := by
  obtain ⟨a,b,hab,rfl,rfl⟩ := (map_adj Fin.valEmbedding target u v).mp h
  exact hab

theorem nat_edges_iff (u v : Nat) (hu : u < 19) (hv : v < 19) :
    natTarget.Adj u v ↔ (row u).testBit v = true := by
  constructor
  · exact nat_edges u v
  · intro h
    exact (map_adj Fin.valEmbedding target u v).mpr
      ⟨⟨u,hu⟩,⟨v,hv⟩,h,rfl,rfl⟩

theorem mask_common_eq (xs : List Nat) (hb : ∀ u ∈ xs, u < 19) :
    maskSet 19 (commonMask 19 row xs) = commonSet natTarget (range 19) xs.toFinset := by
  classical
  ext v
  rw [mem_maskSet, commonMask_bit, commonSet, mem_filter, mem_range]
  constructor
  · rintro ⟨hv,_,hall⟩
    refine ⟨hv,?_⟩
    intro u hu
    have hul : u ∈ xs := List.mem_toFinset.mp hu
    exact (nat_edges_iff u v (hb u hul) hv).mpr (hall u hul)
  · rintro ⟨hv,hall⟩
    refine ⟨hv,hv,?_⟩
    intro u hu
    exact (nat_edges_iff u v (hb u hu) hv).mp (hall u (List.mem_toFinset.mpr hu))

def accept (bound : Nat) (picked : List Nat) : Bool :=
  decide ((maskList 19 (commonMask 19 row picked)).length ≤ bound)

theorem common_bound_of_checked (k bound : Nat)
    (checked : BoolCliqueCover.check rawAdj (accept bound) k (List.range 19) [] = true)
    (s : Finset (Fin 19)) (hs : target.IsNClique k s) :
    (commonSet target univ s).card ≤ bound := by
  classical
  have sub : s.map Fin.valEmbedding ⊆ (List.range 19).toFinset := by
    intro v hv
    obtain ⟨a,_,rfl⟩ := mem_map.mp hv
    simpa using a.isLt
  obtain ⟨out,ha,he⟩ := BoolCliqueCover.complete natTarget rawAdj nat_edges (accept bound) k
    (List.range 19) [] (s.map Fin.valEmbedding) checked sub hs.map
  have he' : out.toFinset = s.map Fin.valEmbedding := by simpa using he
  have hb : ∀ v ∈ out, v < 19 := by
    intro v hv
    have hm : v ∈ s.map Fin.valEmbedding := he' ▸ List.mem_toFinset.mpr hv
    obtain ⟨u,_,rfl⟩ := mem_map.mp hm
    exact u.isLt
  have hbound : (maskList 19 (commonMask 19 row out)).length ≤ bound := of_decide_eq_true ha
  rw [maskList_length,mask_common_eq out hb,he'] at hbound
  have hmap : ∀ u v, target.Adj u v → natTarget.Adj
      (Fin.valEmbedding u) (Fin.valEmbedding v) := by
    intro u v huv
    exact (map_adj Fin.valEmbedding target _ _).mpr ⟨u,v,huv,rfl,rfl⟩
  have hc := commonSet_map_le target natTarget Fin.valEmbedding hmap univ (range 19) s
    (by intro v _; exact mem_range.mpr v.isLt)
  exact hc.trans hbound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked4 : BoolCliqueCover.check rawAdj (accept 3) 4 (List.range 19) [] = true := by
  decide +kernel

theorem bound4 (s : Finset (Fin 19)) (hs : target.IsNClique 4 s) :
    (commonSet target univ s).card ≤ 3 := common_bound_of_checked 4 3 checked4 s hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked5 : BoolCliqueCover.check rawAdj (accept 1) 5 (List.range 19) [] = true := by
  decide +kernel

theorem bound5 (s : Finset (Fin 19)) (hs : target.IsNClique 5 s) :
    (commonSet target univ s).card ≤ 1 := common_bound_of_checked 5 1 checked5 s hs

def originalRows : List Nat := [30784, 18304, 459840, 231552, 364800, 434688, 33669, 274506, 141394, 71778, 47110, 263945, 132753, 66977, 491523, 17528, 25116, 20780, 18612]
def rawHostAdj (v w : Nat) : Bool := (originalRows.getD v 0).testBit w

def host : SimpleGraph (Fin 19) := targetᶜ
instance : DecidableRel host.Adj := fun i j =>
  inferInstanceAs (Decidable ((targetᶜ).Adj i j))

set_option maxRecDepth 100000 in
theorem checked_triangles :
    BoolCliqueCover.check rawHostAdj (fun _ => false) 3 (List.range 19) [] = true := by
  decide +kernel

theorem edge_check : ∀ i j : Fin 19, host.Adj i j → rawHostAdj i.val j.val = true := by
  decide +kernel

theorem host_edges (v w : Nat) (h : (host.map Fin.valEmbedding).Adj v w) :
    rawHostAdj v w = true := by
  obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj Fin.valEmbedding host v w).mp h
  exact edge_check a b hab

theorem host_triangle_free : host.CliqueFree 3 := by
  intro s hs
  have sub : s.map Fin.valEmbedding ⊆ (List.range 19).toFinset := by
    intro v hv
    obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hv
    simp only [List.mem_toFinset, List.mem_range]
    exact a.isLt
  obtain ⟨out,ha,_⟩ := BoolCliqueCover.complete (host.map Fin.valEmbedding)
    rawHostAdj host_edges (fun _ => false) 3 (List.range 19) []
    (s.map Fin.valEmbedding) checked_triangles sub hs.map
  cases ha

def rowsOther : List Nat := [62206, 62205, 462075, 462071, 210543, 315039, 210719, 315183, 523968, 61939, 461308, 509356, 254803, 250707, 310179, 293795, 408924, 343388, 249260]
def originalRowsOther : List Nat := [462080, 462080, 62208, 62208, 313728, 209216, 313504, 208976, 63, 461836, 61955, 12883, 265388, 265388, 197724, 197724, 49827, 49827, 12883]
def rowOther (v : Nat) : Nat := rowsOther.getD v 0

def targetOther : SimpleGraph (Fin 19) where
  Adj i j := (rowOther i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel targetOther.Adj := fun i j =>
  inferInstanceAs (Decidable ((rowOther i.val).testBit j.val = true))
def hostOther : SimpleGraph (Fin 19) := targetOtherᶜ
instance : DecidableRel hostOther.Adj := fun i j =>
  inferInstanceAs (Decidable ((targetOtherᶜ).Adj i j))

def rawOtherAdj (v w : Nat) : Bool := (originalRowsOther.getD v 0).testBit w
set_option maxRecDepth 100000 in
theorem checked_other_triangles :
    BoolCliqueCover.check rawOtherAdj (fun _ => false) 3 (List.range 19) [] = true := by
  decide +kernel

theorem other_edge_check : ∀ i j : Fin 19, hostOther.Adj i j → rawOtherAdj i.val j.val = true := by
  decide +kernel

theorem other_host_edges (v w : Nat) (h : (hostOther.map Fin.valEmbedding).Adj v w) :
    rawOtherAdj v w = true := by
  obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj Fin.valEmbedding hostOther v w).mp h
  exact other_edge_check a b hab

theorem other_triangle_free : hostOther.CliqueFree 3 := by
  intro s hs
  have sub : s.map Fin.valEmbedding ⊆ (List.range 19).toFinset := by
    intro v hv
    obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hv
    simp only [List.mem_toFinset, List.mem_range]
    exact a.isLt
  obtain ⟨out,ha,_⟩ := BoolCliqueCover.complete (hostOther.map Fin.valEmbedding)
    rawOtherAdj other_host_edges (fun _ => false) 3 (List.range 19) []
    (s.map Fin.valEmbedding) checked_other_triangles sub hs.map
  cases ha

def encoded (mask : Nat) : SimpleGraph (Fin 19) where
  Adj i j := i ≠ j ∧ mask.testBit ((min i j).val*19+(max i j).val) = true
  symm := ⟨fun i j h => ⟨h.1.symm, by simpa only [min_comm j i, max_comm j i] using h.2⟩⟩
  loopless := ⟨by intro i; simp⟩
instance (mask : Nat) : DecidableRel (encoded mask).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ mask.testBit ((min i j).val*19+(max i j).val) = true))
def mask0 : Nat := 58280081588215833825809426976908018284710095956426369088135680073876544451713796438080

theorem encoded0_eq : host = encoded mask0 := by
  have h : ∀ i j : Fin 19, host.Adj i j ↔ (encoded mask0).Adj i j := by decide +kernel
  ext i j
  exact h i j
def mask1 : Nat := 12222239170092908889127253311949034132647618607214953492547000784645901871293095398160665856

theorem encoded1_eq : hostOther = encoded mask1 := by
  have h : ∀ i j : Fin 19, hostOther.Adj i j ↔ (encoded mask1).Adj i j := by decide +kernel
  ext i j
  exact h i j
theorem encoded0_triangle_free : (encoded mask0).CliqueFree 3 := by
  rw [← encoded0_eq]
  exact host_triangle_free

theorem encoded1_triangle_free : (encoded mask1).CliqueFree 3 := by
  rw [← encoded1_eq]
  exact other_triangle_free

def targets (i : Fin 2) : SimpleGraph (Fin 19) := if i.val = 0 then target else targetOther

def masks (i : Fin 2) : Nat := if i.val = 0 then mask0 else mask1

end Order10Common

-- generic embedding search soundness
namespace EmbeddingDFS
open Finset SimpleGraph

def search {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    ℕ → List V → (V → Finset W) → Bool
  | 0, _, _ => true
  | _+1, [], _ => true
  | fuel+1, v::rest, domains =>
    decide (∃ w ∈ domains v, search G H fuel rest
      (fun u => (domains u).filter fun x => x ≠ w ∧ (G.Adj v u → H.Adj w x)) = true)

theorem search_complete {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : V ↪ W) (hadj : ∀ u v, G.Adj u v → H.Adj (f u) (f v))
    (fuel : ℕ) (todo : List V) (domains : V → Finset W)
    (hn : todo.Nodup) (hd : ∀ v ∈ todo, f v ∈ domains v) :
    search G H fuel todo domains = true := by
  induction fuel generalizing todo domains with
  | zero => rfl
  | succ fuel ih =>
    cases todo with
    | nil => rfl
    | cons v rest =>
      simp only [search, decide_eq_true_eq]
      refine ⟨f v, hd v (by simp), ?_⟩
      apply ih rest _ (List.nodup_cons.mp hn).2
      intro u hu
      apply mem_filter.mpr
      refine ⟨hd u (List.mem_cons_of_mem _ hu), ?_, hadj v u⟩
      apply f.injective.ne
      intro huv
      subst u
      exact (List.nodup_cons.mp hn).1 hu

theorem search_false_no_embedding {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (fuel : ℕ) (todo : List V) (domains : V → Finset W)
    (hn : todo.Nodup) (hfalse : search G H fuel todo domains = false) :
    ¬ ∃ f : V ↪ W, (∀ u v, G.Adj u v → H.Adj (f u) (f v)) ∧
      (∀ v ∈ todo, f v ∈ domains v) := by
  rintro ⟨f,ha,hd⟩
  have htrue := search_complete G H f ha fuel todo domains hn hd
  rw [hfalse] at htrue
  contradiction

def available (m w : ℕ) : ℕ := (2^m-1) ^^^ 2^w

theorem available_testBit (m w x : ℕ) (hx : x < m) (hne : x ≠ w) :
    (available m w).testBit x = true := by
  simp [available, Nat.testBit_xor, Nat.testBit_two_pow, hx, Ne.symm hne]

def propagate (source target : ℕ → ℕ) (m v w : ℕ)
    (todo : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  todo.map fun (u,dom) =>
    (u, (if (source v).testBit u then dom &&& target w else dom) &&& available m w)

def unionMask : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (_,dom)::rest => dom ||| unionMask rest

theorem unionMask_bit_of_mem (todo : List (ℕ × ℕ)) (v dom x : ℕ)
    (hmem : (v,dom) ∈ todo) (hbit : dom.testBit x = true) :
    (unionMask todo).testBit x = true := by
  induction todo with
  | nil => simp at hmem
  | cons pair rest ih =>
    rcases pair with ⟨u,d⟩
    rcases List.mem_cons.mp hmem with h | h
    · cases h
      simp [unionMask, Nat.testBit_or, hbit]
    · simp [unionMask, Nat.testBit_or, ih h]

def withNat {α : Sort*} (n : Nat) (k : Nat → α) : α :=
  match n with
  | 0 => k 0
  | d+1 => k (d+1)

theorem withNat_eq {α : Sort*} (n : Nat) (k : Nat → α) : withNat n k = k n := by
  cases n <;> rfl

def withDomains {α : Sort*} : List (Nat × Nat) → (List (Nat × Nat) → α) → α
  | [], k => k []
  | (v,d)::rest, k => withNat d (fun d => withDomains rest (fun rest => k ((v,d)::rest)))

theorem withDomains_eq {α : Sort*} (todo : List (Nat × Nat))
    (k : List (Nat × Nat) → α) : withDomains todo k = k todo := by
  induction todo generalizing k with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨v,d⟩
    simp only [withDomains, withNat_eq, ih]

def capacity (m : ℕ) (todo : List (ℕ × ℕ)) : ℕ :=
  withNat (unionMask todo) (fun mask => ((List.range m).filter mask.testBit).length)

def feasible (m : ℕ) (todo : List (ℕ × ℕ)) : Bool :=
  (todo.all fun p => decide (p.2 ≠ 0)) && decide (todo.length ≤ capacity m todo)

theorem feasible_of_embedding (m : ℕ) (valid : ℕ → Prop) (f : ℕ → ℕ)
    (hinj : ∀ u, valid u → ∀ v, valid v → u ≠ v → f u ≠ f v)
    (todo : List (ℕ × ℕ)) (hn : (todo.map Prod.fst).Nodup)
    (hv : ∀ v dom, (v,dom) ∈ todo → valid v)
    (hd : ∀ v dom, (v,dom) ∈ todo → f v < m ∧ dom.testBit (f v) = true) :
    feasible m todo = true := by
  have hvalid : ∀ v ∈ todo.map Prod.fst, valid v := by
    intro v hmem
    obtain ⟨⟨u,dom⟩,hu,heq⟩ := List.mem_map.mp hmem
    cases heq
    exact hv u dom hu
  have himage : ((todo.map Prod.fst).map f).Nodup := by
    apply List.Nodup.map_on _ hn
    intro u hu v hv' heq
    by_contra hne
    exact hinj u (hvalid u hu) v (hvalid v hv') hne heq
  have hsub : ((todo.map Prod.fst).map f) ⊆
      (List.range m).filter (unionMask todo).testBit := by
    intro x hx
    obtain ⟨v,hvkey,rfl⟩ := List.mem_map.mp hx
    obtain ⟨⟨u,dom⟩,hu,heq⟩ := List.mem_map.mp hvkey
    cases heq
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (hd u dom hu).1,
      unionMask_bit_of_mem todo u dom (f u) hu (hd u dom hu).2⟩
  unfold feasible
  apply Bool.and_eq_true_iff.mpr
  constructor
  · simp only [List.all_eq_true, decide_eq_true_eq]
    rintro ⟨v,dom⟩ hmem hz
    have hbit := (hd v dom hmem).2
    change dom = 0 at hz
    rw [hz] at hbit
    simpa only [Nat.zero_testBit, Bool.false_eq_true] using hbit
  · apply decide_eq_true_eq.mpr
    simpa only [List.length_map, capacity, withNat_eq] using himage.length_le_of_subset hsub

def bitSearch (source target : ℕ → ℕ) (m : ℕ) :
    ℕ → List (ℕ × ℕ) → Bool
  | 0, _ => true
  | _+1, [] => true
  | fuel+1, (v,dom)::rest =>
    if feasible m ((v,dom)::rest) then
      (List.range m).any fun w => dom.testBit w &&
        withDomains (propagate source target m v w rest) (fun child =>
          feasible m (child.filter fun pair => (source v).testBit pair.1) &&
          bitSearch source target m fuel child)
    else false

@[simp] theorem propagate_keys (source target : ℕ → ℕ) (m v w : ℕ)
    (todo : List (ℕ × ℕ)) :
    (propagate source target m v w todo).map Prod.fst = todo.map Prod.fst := by
  simp [propagate, List.map_map]

theorem bitSearch_complete (source target : ℕ → ℕ) (m : ℕ)
    (valid : ℕ → Prop) (f : ℕ → ℕ)
    (hinj : ∀ u, valid u → ∀ v, valid v → u ≠ v → f u ≠ f v)
    (hadj : ∀ u, valid u → ∀ v, valid v →
      (source u).testBit v = true → (target (f u)).testBit (f v) = true)
    (fuel : ℕ) (todo : List (ℕ × ℕ))
    (hn : (todo.map Prod.fst).Nodup)
    (hv : ∀ v dom, (v,dom) ∈ todo → valid v)
    (hd : ∀ v dom, (v,dom) ∈ todo → f v < m ∧ dom.testBit (f v) = true) :
    bitSearch source target m fuel todo = true := by
  induction fuel generalizing todo with
  | zero => rfl
  | succ fuel ih =>
    cases todo with
    | nil => rfl
    | cons pair rest =>
      rcases pair with ⟨v,dom⟩
      have hhead : (v,dom) ∈ (v,dom)::rest := by simp
      have hdom := hd v dom hhead
      have hfeasible := feasible_of_embedding m valid f hinj ((v,dom)::rest) hn hv hd
      let child := propagate source target m v (f v) rest
      have hnc : (child.map Prod.fst).Nodup := by
        simpa [child] using hn.tail
      have hvc : ∀ u d, (u,d) ∈ child → valid u := by
        intro u d hu
        obtain ⟨⟨x,dx⟩,hx,hpair⟩ := List.mem_map.mp hu
        cases hpair
        exact hv u dx (by simp [hx])
      have hdc : ∀ u d, (u,d) ∈ child → f u < m ∧ d.testBit (f u) = true := by
        intro u d hu
        obtain ⟨⟨x,dx⟩,hx,hpair⟩ := List.mem_map.mp hu
        cases hpair
        have hxall : (u,dx) ∈ (v,dom)::rest := by simp [hx]
        have hdx := hd u dx hxall
        have hxne : u ≠ v := by
          intro h
          subst u
          have hmem : v ∈ rest.map Prod.fst := List.mem_map.mpr ⟨(v,dx),hx,rfl⟩
          exact (List.nodup_cons.mp hn).1 hmem
        have hfn := hinj u (hv u dx hxall) v (hv v dom hhead) hxne
        refine ⟨hdx.1, ?_⟩
        rw [Nat.testBit_and, available_testBit m (f v) (f u) hdx.1 hfn]
        simp only [Bool.and_true]
        split
        · rename_i hsource
          rw [Nat.testBit_and, hdx.2, hadj v (hv v dom hhead) u (hv u dx hxall) hsource]
          rfl
        · exact hdx.2
      have hneighbor : feasible m (child.filter fun pair => (source v).testBit pair.1) = true := by
        apply feasible_of_embedding m valid f hinj
        · exact hnc.sublist (List.filter_sublist.map Prod.fst)
        · intro u d hmem
          exact hvc u d (List.mem_of_mem_filter hmem)
        · intro u d hmem
          exact hdc u d (List.mem_of_mem_filter hmem)
      rw [bitSearch, if_pos hfeasible, List.any_eq_true]
      refine ⟨f v, List.mem_range.mpr hdom.1, Bool.and_eq_true_iff.mpr ⟨hdom.2, ?_⟩⟩
      rw [withDomains_eq]
      exact Bool.and_eq_true_iff.mpr ⟨hneighbor, ih child hnc hvc hdc⟩

def extendMap {n m : ℕ} (f : Fin n ↪ Fin m) (v : ℕ) : ℕ :=
  if h : v < n then (f ⟨v,h⟩).val else 0

theorem bitSearch_false_no_embedding {n m : ℕ}
    (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (source target : ℕ → ℕ)
    (hg : ∀ u v : Fin n, G.Adj u v ↔ (source u.val).testBit v.val = true)
    (hh : ∀ u v : Fin m, H.Adj u v ↔ (target u.val).testBit v.val = true)
    (vertices : List ℕ) (hn : vertices.Nodup) (hv : ∀ v ∈ vertices, v < n)
    (fuel : ℕ)
    (hfalse : bitSearch source target m fuel
      (vertices.map fun v => (v,2^m-1)) = false) :
    ¬ ∃ f : Fin n ↪ Fin m, ∀ u v, G.Adj u v → H.Adj (f u) (f v) := by
  rintro ⟨f,ha⟩
  have hi : ∀ u, u < n → ∀ v, v < n → u ≠ v → extendMap f u ≠ extendMap f v := by
    intro u hu v hv hne heq
    simp only [extendMap, dif_pos hu, dif_pos hv] at heq
    exact hne (congrArg Fin.val (f.injective (Fin.ext heq)))
  have hadj : ∀ u, u < n → ∀ v, v < n →
      (source u).testBit v = true → (target (extendMap f u)).testBit (extendMap f v) = true := by
    intro u hu v hv hbit
    simp only [extendMap, dif_pos hu, dif_pos hv]
    exact (hh _ _).mp (ha _ _ ((hg ⟨u,hu⟩ ⟨v,hv⟩).mpr hbit))
  have htrue := bitSearch_complete source target m (fun v => v < n) (extendMap f)
    hi hadj fuel (vertices.map fun v => (v,2^m-1))
    (by simpa [List.map_map, Function.comp_def] using hn)
    (by intro v dom hmem; obtain ⟨x,hx,h⟩ := List.mem_map.mp hmem; cases h; exact hv v hx)
    (by
      intro v dom hmem
      obtain ⟨x,hx,h⟩ := List.mem_map.mp hmem
      cases h
      have hb : extendMap f v < m := by simpa [extendMap, hv v hx] using (f ⟨v,hv v hx⟩).isLt
      exact ⟨hb, by simp [Nat.testBit_two_pow_sub_one, hb]⟩)
  rw [hfalse] at htrue
  contradiction

end EmbeddingDFS

namespace EmbeddingDFS

def branch (source target : Nat → Nat) (m fuel v dom : Nat)
    (rest : List (Nat × Nat)) (w : Nat) : Bool :=
  dom.testBit w && withDomains (propagate source target m v w rest) (fun child =>
    feasible m (child.filter fun pair => (source v).testBit pair.1) &&
    bitSearch source target m fuel child)

theorem branch_false_of_child (source target : Nat → Nat) (m fuel v dom : Nat)
    (rest : List (Nat × Nat)) (w : Nat)
    (h : bitSearch source target m fuel (propagate source target m v w rest) = false) :
    branch source target m fuel v dom rest w = false := by
  simp only [branch, withDomains_eq, h, Bool.and_false]

theorem bitSearch_false_of_branches (source target : Nat → Nat) (m fuel v dom : Nat)
    (rest : List (Nat × Nat))
    (h : ∀ w ∈ List.range m, branch source target m fuel v dom rest w = false) :
    bitSearch source target m (fuel+1) ((v,dom)::rest) = false := by
  change (if feasible m ((v,dom)::rest) then
    (List.range m).any (branch source target m fuel v dom rest) else false) = false
  split
  · exact List.any_eq_false.mpr (fun w hw => by simp only [h w hw, Bool.false_eq_true, not_false_eq_true])
  · rfl

end EmbeddingDFS

-- closed residual embedding search 56
namespace Order10Search56
open EmbeddingDFS
def sourceRows : List Nat := [962, 961, 952, 884, 748, 988, 955, 887, 751, 511]
def targetRows : List Nat := [62206, 62205, 462075, 462071, 210543, 315039, 210719, 315183, 523968, 61939, 461308, 509356, 254803, 250707, 310179, 293795, 408924, 343388, 249260]
def source (v : Nat) : Nat := sourceRows.getD v 0
def target (v : Nat) : Nat := targetRows.getD v 0
def st0 : List (Nat × Nat) := [(7,248), (3,248), (5,248), (2,248), (0,62200), (1,62200), (6,248)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok0 : bitSearch source target 19 7 st0 = false := by
  decide +kernel
def st1 : List (Nat × Nat) := [(7,244), (3,244), (5,244), (2,244), (0,62196), (1,62196), (6,244)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok1 : bitSearch source target 19 7 st1 = false := by
  decide +kernel
def st2 : List (Nat × Nat) := [(7,12908), (3,12908), (5,12908), (2,12908), (0,62188), (1,62188), (6,12908)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok2 : bitSearch source target 19 7 st2 = false := by
  decide +kernel
def st3 : List (Nat × Nat) := [(7,49820), (3,49820), (5,49820), (2,49820), (0,62172), (1,62172), (6,49820)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3 : bitSearch source target 19 7 st3 = false := by
  decide +kernel
def st4 : List (Nat × Nat) := [(7,12828), (3,12828), (5,12828), (2,12828), (0,62140), (1,62140), (6,12828)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4 : bitSearch source target 19 7 st4 = false := by
  decide +kernel
def st5 : List (Nat × Nat) := [(7,49708), (3,49708), (5,49708), (2,49708), (0,62076), (1,62076), (6,49708)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5 : bitSearch source target 19 7 st5 = false := by
  decide +kernel
def st6 : List (Nat × Nat) := [(7,61680), (3,61680), (5,61680), (2,61680), (0,61692), (1,61692), (6,61680)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6 : bitSearch source target 19 7 st6 = false := by
  decide +kernel
def st7 : List (Nat × Nat) := [(7,57936), (3,57936), (5,57936), (2,57936), (0,58108), (1,58108), (6,57936)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7 : bitSearch source target 19 7 st7 = false := by
  decide +kernel
def st8 : List (Nat × Nat) := [(7,53840), (3,53840), (5,53840), (2,53840), (0,54012), (1,54012), (6,53840)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8 : bitSearch source target 19 7 st8 = false := by
  decide +kernel
def st9 : List (Nat × Nat) := [(7,45728), (3,45728), (5,45728), (2,45728), (0,45820), (1,45820), (6,45728)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok9 : bitSearch source target 19 7 st9 = false := by
  decide +kernel
def st10 : List (Nat × Nat) := [(7,29344), (3,29344), (5,29344), (2,29344), (0,29436), (1,29436), (6,29344)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok10 : bitSearch source target 19 7 st10 = false := by
  decide +kernel
def st11 : List (Nat × Nat) := [(4,62204), (7,62204), (3,62204), (5,62204), (2,62204), (0,62204), (1,62204), (6,62204)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok11 : bitSearch source target 19 8 st11 = false := by
  refine bitSearch_false_of_branches source target 19 7 4 62204 [(7,62204), (3,62204), (5,62204), (2,62204), (0,62204), (1,62204), (6,62204)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 4 2 [(7,62204), (3,62204), (5,62204), (2,62204), (0,62204), (1,62204), (6,62204)] = st0 := by decide +kernel
    rw [h]
    exact ok0
  · apply branch_false_of_child
    have h : propagate source target 19 4 3 [(7,62204), (3,62204), (5,62204), (2,62204), (0,62204), (1,62204), (6,62204)] = st1 := by decide +kernel
    rw [h]
    exact ok1
  · apply branch_false_of_child
    have h : propagate source target 19 4 4 [(7,62204), (3,62204), (5,62204), (2,62204), (0,62204), (1,62204), (6,62204)] = st2 := by decide +kernel
    rw [h]
    exact ok2
  · apply branch_false_of_child
    have h : propagate source target 19 4 5 [(7,62204), (3,62204), (5,62204), (2,62204), (0,62204), (1,62204), (6,62204)] = st3 := by decide +kernel
    rw [h]
    exact ok3
  · apply branch_false_of_child
    have h : propagate source target 19 4 6 [(7,62204), (3,62204), (5,62204), (2,62204), (0,62204), (1,62204), (6,62204)] = st4 := by decide +kernel
    rw [h]
    exact ok4
  · apply branch_false_of_child
    have h : propagate source target 19 4 7 [(7,62204), (3,62204), (5,62204), (2,62204), (0,62204), (1,62204), (6,62204)] = st5 := by decide +kernel
    rw [h]
    exact ok5
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 4 9 [(7,62204), (3,62204), (5,62204), (2,62204), (0,62204), (1,62204), (6,62204)] = st6 := by decide +kernel
    rw [h]
    exact ok6
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 4 12 [(7,62204), (3,62204), (5,62204), (2,62204), (0,62204), (1,62204), (6,62204)] = st7 := by decide +kernel
    rw [h]
    exact ok7
  · apply branch_false_of_child
    have h : propagate source target 19 4 13 [(7,62204), (3,62204), (5,62204), (2,62204), (0,62204), (1,62204), (6,62204)] = st8 := by decide +kernel
    rw [h]
    exact ok8
  · apply branch_false_of_child
    have h : propagate source target 19 4 14 [(7,62204), (3,62204), (5,62204), (2,62204), (0,62204), (1,62204), (6,62204)] = st9 := by decide +kernel
    rw [h]
    exact ok9
  · apply branch_false_of_child
    have h : propagate source target 19 4 15 [(7,62204), (3,62204), (5,62204), (2,62204), (0,62204), (1,62204), (6,62204)] = st10 := by decide +kernel
    rw [h]
    exact ok10
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st12 : List (Nat × Nat) := [(4,62190), (7,12910), (3,12910), (5,12910), (2,12910), (0,12910), (1,12910), (6,12910)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok12 : bitSearch source target 19 8 st12 = false := by
  decide +kernel
def st13 : List (Nat × Nat) := [(4,62174), (7,49822), (3,49822), (5,49822), (2,49822), (0,49822), (1,49822), (6,49822)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok13 : bitSearch source target 19 8 st13 = false := by
  decide +kernel
def st14 : List (Nat × Nat) := [(4,62142), (7,12830), (3,12830), (5,12830), (2,12830), (0,12830), (1,12830), (6,12830)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok14 : bitSearch source target 19 8 st14 = false := by
  decide +kernel
def st15 : List (Nat × Nat) := [(4,62078), (7,49710), (3,49710), (5,49710), (2,49710), (0,49710), (1,49710), (6,49710)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok15 : bitSearch source target 19 8 st15 = false := by
  decide +kernel
def st16 : List (Nat × Nat) := [(4,61694), (7,61682), (3,61682), (5,61682), (2,61682), (0,61682), (1,61682), (6,61682)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok16 : bitSearch source target 19 8 st16 = false := by
  decide +kernel
def st17 : List (Nat × Nat) := [(4,58110), (7,57938), (3,57938), (5,57938), (2,57938), (0,57938), (1,57938), (6,57938)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok17 : bitSearch source target 19 8 st17 = false := by
  decide +kernel
def st18 : List (Nat × Nat) := [(4,54014), (7,53842), (3,53842), (5,53842), (2,53842), (0,53842), (1,53842), (6,53842)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok18 : bitSearch source target 19 8 st18 = false := by
  decide +kernel
def st19 : List (Nat × Nat) := [(4,45822), (7,45730), (3,45730), (5,45730), (2,45730), (0,45730), (1,45730), (6,45730)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok19 : bitSearch source target 19 8 st19 = false := by
  decide +kernel
def st20 : List (Nat × Nat) := [(4,29438), (7,29346), (3,29346), (5,29346), (2,29346), (0,29346), (1,29346), (6,29346)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok20 : bitSearch source target 19 8 st20 = false := by
  decide +kernel
def st21 : List (Nat × Nat) := [(8,62206), (4,62206), (7,62206), (3,62206), (5,62206), (2,62206), (0,62206), (1,62206), (6,62206)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok21 : bitSearch source target 19 9 st21 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 62206 [(4,62206), (7,62206), (3,62206), (5,62206), (2,62206), (0,62206), (1,62206), (6,62206)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 1 [(4,62206), (7,62206), (3,62206), (5,62206), (2,62206), (0,62206), (1,62206), (6,62206)] = st11 := by decide +kernel
    rw [h]
    exact ok11
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 4 [(4,62206), (7,62206), (3,62206), (5,62206), (2,62206), (0,62206), (1,62206), (6,62206)] = st12 := by decide +kernel
    rw [h]
    exact ok12
  · apply branch_false_of_child
    have h : propagate source target 19 8 5 [(4,62206), (7,62206), (3,62206), (5,62206), (2,62206), (0,62206), (1,62206), (6,62206)] = st13 := by decide +kernel
    rw [h]
    exact ok13
  · apply branch_false_of_child
    have h : propagate source target 19 8 6 [(4,62206), (7,62206), (3,62206), (5,62206), (2,62206), (0,62206), (1,62206), (6,62206)] = st14 := by decide +kernel
    rw [h]
    exact ok14
  · apply branch_false_of_child
    have h : propagate source target 19 8 7 [(4,62206), (7,62206), (3,62206), (5,62206), (2,62206), (0,62206), (1,62206), (6,62206)] = st15 := by decide +kernel
    rw [h]
    exact ok15
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 9 [(4,62206), (7,62206), (3,62206), (5,62206), (2,62206), (0,62206), (1,62206), (6,62206)] = st16 := by decide +kernel
    rw [h]
    exact ok16
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 12 [(4,62206), (7,62206), (3,62206), (5,62206), (2,62206), (0,62206), (1,62206), (6,62206)] = st17 := by decide +kernel
    rw [h]
    exact ok17
  · apply branch_false_of_child
    have h : propagate source target 19 8 13 [(4,62206), (7,62206), (3,62206), (5,62206), (2,62206), (0,62206), (1,62206), (6,62206)] = st18 := by decide +kernel
    rw [h]
    exact ok18
  · apply branch_false_of_child
    have h : propagate source target 19 8 14 [(4,62206), (7,62206), (3,62206), (5,62206), (2,62206), (0,62206), (1,62206), (6,62206)] = st19 := by decide +kernel
    rw [h]
    exact ok19
  · apply branch_false_of_child
    have h : propagate source target 19 8 15 [(4,62206), (7,62206), (3,62206), (5,62206), (2,62206), (0,62206), (1,62206), (6,62206)] = st20 := by decide +kernel
    rw [h]
    exact ok20
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st22 : List (Nat × Nat) := [(4,62189), (7,12909), (3,12909), (5,12909), (2,12909), (0,12909), (1,12909), (6,12909)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok22 : bitSearch source target 19 8 st22 = false := by
  decide +kernel
def st23 : List (Nat × Nat) := [(4,62173), (7,49821), (3,49821), (5,49821), (2,49821), (0,49821), (1,49821), (6,49821)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok23 : bitSearch source target 19 8 st23 = false := by
  decide +kernel
def st24 : List (Nat × Nat) := [(4,62141), (7,12829), (3,12829), (5,12829), (2,12829), (0,12829), (1,12829), (6,12829)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok24 : bitSearch source target 19 8 st24 = false := by
  decide +kernel
def st25 : List (Nat × Nat) := [(4,62077), (7,49709), (3,49709), (5,49709), (2,49709), (0,49709), (1,49709), (6,49709)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok25 : bitSearch source target 19 8 st25 = false := by
  decide +kernel
def st26 : List (Nat × Nat) := [(4,61693), (7,61681), (3,61681), (5,61681), (2,61681), (0,61681), (1,61681), (6,61681)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok26 : bitSearch source target 19 8 st26 = false := by
  decide +kernel
def st27 : List (Nat × Nat) := [(4,58109), (7,57937), (3,57937), (5,57937), (2,57937), (0,57937), (1,57937), (6,57937)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok27 : bitSearch source target 19 8 st27 = false := by
  decide +kernel
def st28 : List (Nat × Nat) := [(4,54013), (7,53841), (3,53841), (5,53841), (2,53841), (0,53841), (1,53841), (6,53841)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok28 : bitSearch source target 19 8 st28 = false := by
  decide +kernel
def st29 : List (Nat × Nat) := [(4,45821), (7,45729), (3,45729), (5,45729), (2,45729), (0,45729), (1,45729), (6,45729)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok29 : bitSearch source target 19 8 st29 = false := by
  decide +kernel
def st30 : List (Nat × Nat) := [(4,29437), (7,29345), (3,29345), (5,29345), (2,29345), (0,29345), (1,29345), (6,29345)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok30 : bitSearch source target 19 8 st30 = false := by
  decide +kernel
def st31 : List (Nat × Nat) := [(8,62205), (4,62205), (7,62205), (3,62205), (5,62205), (2,62205), (0,62205), (1,62205), (6,62205)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok31 : bitSearch source target 19 9 st31 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 62205 [(4,62205), (7,62205), (3,62205), (5,62205), (2,62205), (0,62205), (1,62205), (6,62205)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 8 0 [(4,62205), (7,62205), (3,62205), (5,62205), (2,62205), (0,62205), (1,62205), (6,62205)] = st11 := by decide +kernel
    rw [h]
    exact ok11
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 4 [(4,62205), (7,62205), (3,62205), (5,62205), (2,62205), (0,62205), (1,62205), (6,62205)] = st22 := by decide +kernel
    rw [h]
    exact ok22
  · apply branch_false_of_child
    have h : propagate source target 19 8 5 [(4,62205), (7,62205), (3,62205), (5,62205), (2,62205), (0,62205), (1,62205), (6,62205)] = st23 := by decide +kernel
    rw [h]
    exact ok23
  · apply branch_false_of_child
    have h : propagate source target 19 8 6 [(4,62205), (7,62205), (3,62205), (5,62205), (2,62205), (0,62205), (1,62205), (6,62205)] = st24 := by decide +kernel
    rw [h]
    exact ok24
  · apply branch_false_of_child
    have h : propagate source target 19 8 7 [(4,62205), (7,62205), (3,62205), (5,62205), (2,62205), (0,62205), (1,62205), (6,62205)] = st25 := by decide +kernel
    rw [h]
    exact ok25
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 9 [(4,62205), (7,62205), (3,62205), (5,62205), (2,62205), (0,62205), (1,62205), (6,62205)] = st26 := by decide +kernel
    rw [h]
    exact ok26
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 12 [(4,62205), (7,62205), (3,62205), (5,62205), (2,62205), (0,62205), (1,62205), (6,62205)] = st27 := by decide +kernel
    rw [h]
    exact ok27
  · apply branch_false_of_child
    have h : propagate source target 19 8 13 [(4,62205), (7,62205), (3,62205), (5,62205), (2,62205), (0,62205), (1,62205), (6,62205)] = st28 := by decide +kernel
    rw [h]
    exact ok28
  · apply branch_false_of_child
    have h : propagate source target 19 8 14 [(4,62205), (7,62205), (3,62205), (5,62205), (2,62205), (0,62205), (1,62205), (6,62205)] = st29 := by decide +kernel
    rw [h]
    exact ok29
  · apply branch_false_of_child
    have h : propagate source target 19 8 15 [(4,62205), (7,62205), (3,62205), (5,62205), (2,62205), (0,62205), (1,62205), (6,62205)] = st30 := by decide +kernel
    rw [h]
    exact ok30
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st32 : List (Nat × Nat) := [(7,242), (3,242), (5,242), (2,242), (0,462066), (1,462066), (6,242)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok32 : bitSearch source target 19 7 st32 = false := by
  decide +kernel
def st33 : List (Nat × Nat) := [(7,241), (3,241), (5,241), (2,241), (0,462065), (1,462065), (6,241)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok33 : bitSearch source target 19 7 st33 = false := by
  decide +kernel
def st34 : List (Nat × Nat) := [(7,197731), (3,197731), (5,197731), (2,197731), (0,462051), (1,462051), (6,197731)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok34 : bitSearch source target 19 7 st34 = false := by
  decide +kernel
def st35 : List (Nat × Nat) := [(7,265363), (3,265363), (5,265363), (2,265363), (0,462035), (1,462035), (6,265363)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok35 : bitSearch source target 19 7 st35 = false := by
  decide +kernel
def st36 : List (Nat × Nat) := [(7,197651), (3,197651), (5,197651), (2,197651), (0,462003), (1,462003), (6,197651)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok36 : bitSearch source target 19 7 st36 = false := by
  decide +kernel
def st37 : List (Nat × Nat) := [(7,265251), (3,265251), (5,265251), (2,265251), (0,461939), (1,461939), (6,265251)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok37 : bitSearch source target 19 7 st37 = false := by
  decide +kernel
def st38 : List (Nat × Nat) := [(7,461040), (3,461040), (5,461040), (2,461040), (0,461043), (1,461043), (6,461040)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok38 : bitSearch source target 19 7 st38 = false := by
  decide +kernel
def st39 : List (Nat × Nat) := [(7,459936), (3,459936), (5,459936), (2,459936), (0,460019), (1,460019), (6,459936)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok39 : bitSearch source target 19 7 st39 = false := by
  decide +kernel
def st40 : List (Nat × Nat) := [(7,396368), (3,396368), (5,396368), (2,396368), (0,396531), (1,396531), (6,396368)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok40 : bitSearch source target 19 7 st40 = false := by
  decide +kernel
def st41 : List (Nat × Nat) := [(7,330832), (3,330832), (5,330832), (2,330832), (0,330995), (1,330995), (6,330832)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok41 : bitSearch source target 19 7 st41 = false := by
  decide +kernel
def st42 : List (Nat × Nat) := [(7,199840), (3,199840), (5,199840), (2,199840), (0,199923), (1,199923), (6,199840)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok42 : bitSearch source target 19 7 st42 = false := by
  decide +kernel
def st43 : List (Nat × Nat) := [(4,462067), (7,462067), (3,462067), (5,462067), (2,462067), (0,462067), (1,462067), (6,462067)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok43 : bitSearch source target 19 8 st43 = false := by
  refine bitSearch_false_of_branches source target 19 7 4 462067 [(7,462067), (3,462067), (5,462067), (2,462067), (0,462067), (1,462067), (6,462067)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 4 0 [(7,462067), (3,462067), (5,462067), (2,462067), (0,462067), (1,462067), (6,462067)] = st32 := by decide +kernel
    rw [h]
    exact ok32
  · apply branch_false_of_child
    have h : propagate source target 19 4 1 [(7,462067), (3,462067), (5,462067), (2,462067), (0,462067), (1,462067), (6,462067)] = st33 := by decide +kernel
    rw [h]
    exact ok33
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 4 4 [(7,462067), (3,462067), (5,462067), (2,462067), (0,462067), (1,462067), (6,462067)] = st34 := by decide +kernel
    rw [h]
    exact ok34
  · apply branch_false_of_child
    have h : propagate source target 19 4 5 [(7,462067), (3,462067), (5,462067), (2,462067), (0,462067), (1,462067), (6,462067)] = st35 := by decide +kernel
    rw [h]
    exact ok35
  · apply branch_false_of_child
    have h : propagate source target 19 4 6 [(7,462067), (3,462067), (5,462067), (2,462067), (0,462067), (1,462067), (6,462067)] = st36 := by decide +kernel
    rw [h]
    exact ok36
  · apply branch_false_of_child
    have h : propagate source target 19 4 7 [(7,462067), (3,462067), (5,462067), (2,462067), (0,462067), (1,462067), (6,462067)] = st37 := by decide +kernel
    rw [h]
    exact ok37
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 4 10 [(7,462067), (3,462067), (5,462067), (2,462067), (0,462067), (1,462067), (6,462067)] = st38 := by decide +kernel
    rw [h]
    exact ok38
  · apply branch_false_of_child
    have h : propagate source target 19 4 11 [(7,462067), (3,462067), (5,462067), (2,462067), (0,462067), (1,462067), (6,462067)] = st39 := by decide +kernel
    rw [h]
    exact ok39
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 4 16 [(7,462067), (3,462067), (5,462067), (2,462067), (0,462067), (1,462067), (6,462067)] = st40 := by decide +kernel
    rw [h]
    exact ok40
  · apply branch_false_of_child
    have h : propagate source target 19 4 17 [(7,462067), (3,462067), (5,462067), (2,462067), (0,462067), (1,462067), (6,462067)] = st41 := by decide +kernel
    rw [h]
    exact ok41
  · apply branch_false_of_child
    have h : propagate source target 19 4 18 [(7,462067), (3,462067), (5,462067), (2,462067), (0,462067), (1,462067), (6,462067)] = st42 := by decide +kernel
    rw [h]
    exact ok42
def st44 : List (Nat × Nat) := [(4,462059), (7,197739), (3,197739), (5,197739), (2,197739), (0,197739), (1,197739), (6,197739)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok44 : bitSearch source target 19 8 st44 = false := by
  decide +kernel
def st45 : List (Nat × Nat) := [(4,462043), (7,265371), (3,265371), (5,265371), (2,265371), (0,265371), (1,265371), (6,265371)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok45 : bitSearch source target 19 8 st45 = false := by
  decide +kernel
def st46 : List (Nat × Nat) := [(4,462011), (7,197659), (3,197659), (5,197659), (2,197659), (0,197659), (1,197659), (6,197659)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok46 : bitSearch source target 19 8 st46 = false := by
  decide +kernel
def st47 : List (Nat × Nat) := [(4,461947), (7,265259), (3,265259), (5,265259), (2,265259), (0,265259), (1,265259), (6,265259)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok47 : bitSearch source target 19 8 st47 = false := by
  decide +kernel
def st48 : List (Nat × Nat) := [(4,461051), (7,461048), (3,461048), (5,461048), (2,461048), (0,461048), (1,461048), (6,461048)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok48 : bitSearch source target 19 8 st48 = false := by
  decide +kernel
def st49 : List (Nat × Nat) := [(4,460027), (7,459944), (3,459944), (5,459944), (2,459944), (0,459944), (1,459944), (6,459944)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok49 : bitSearch source target 19 8 st49 = false := by
  decide +kernel
def st50 : List (Nat × Nat) := [(4,396539), (7,396376), (3,396376), (5,396376), (2,396376), (0,396376), (1,396376), (6,396376)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok50 : bitSearch source target 19 8 st50 = false := by
  decide +kernel
def st51 : List (Nat × Nat) := [(4,331003), (7,330840), (3,330840), (5,330840), (2,330840), (0,330840), (1,330840), (6,330840)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok51 : bitSearch source target 19 8 st51 = false := by
  decide +kernel
def st52 : List (Nat × Nat) := [(4,199931), (7,199848), (3,199848), (5,199848), (2,199848), (0,199848), (1,199848), (6,199848)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok52 : bitSearch source target 19 8 st52 = false := by
  decide +kernel
def st53 : List (Nat × Nat) := [(8,462075), (4,462075), (7,462075), (3,462075), (5,462075), (2,462075), (0,462075), (1,462075), (6,462075)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok53 : bitSearch source target 19 9 st53 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 462075 [(4,462075), (7,462075), (3,462075), (5,462075), (2,462075), (0,462075), (1,462075), (6,462075)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 3 [(4,462075), (7,462075), (3,462075), (5,462075), (2,462075), (0,462075), (1,462075), (6,462075)] = st43 := by decide +kernel
    rw [h]
    exact ok43
  · apply branch_false_of_child
    have h : propagate source target 19 8 4 [(4,462075), (7,462075), (3,462075), (5,462075), (2,462075), (0,462075), (1,462075), (6,462075)] = st44 := by decide +kernel
    rw [h]
    exact ok44
  · apply branch_false_of_child
    have h : propagate source target 19 8 5 [(4,462075), (7,462075), (3,462075), (5,462075), (2,462075), (0,462075), (1,462075), (6,462075)] = st45 := by decide +kernel
    rw [h]
    exact ok45
  · apply branch_false_of_child
    have h : propagate source target 19 8 6 [(4,462075), (7,462075), (3,462075), (5,462075), (2,462075), (0,462075), (1,462075), (6,462075)] = st46 := by decide +kernel
    rw [h]
    exact ok46
  · apply branch_false_of_child
    have h : propagate source target 19 8 7 [(4,462075), (7,462075), (3,462075), (5,462075), (2,462075), (0,462075), (1,462075), (6,462075)] = st47 := by decide +kernel
    rw [h]
    exact ok47
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 10 [(4,462075), (7,462075), (3,462075), (5,462075), (2,462075), (0,462075), (1,462075), (6,462075)] = st48 := by decide +kernel
    rw [h]
    exact ok48
  · apply branch_false_of_child
    have h : propagate source target 19 8 11 [(4,462075), (7,462075), (3,462075), (5,462075), (2,462075), (0,462075), (1,462075), (6,462075)] = st49 := by decide +kernel
    rw [h]
    exact ok49
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 16 [(4,462075), (7,462075), (3,462075), (5,462075), (2,462075), (0,462075), (1,462075), (6,462075)] = st50 := by decide +kernel
    rw [h]
    exact ok50
  · apply branch_false_of_child
    have h : propagate source target 19 8 17 [(4,462075), (7,462075), (3,462075), (5,462075), (2,462075), (0,462075), (1,462075), (6,462075)] = st51 := by decide +kernel
    rw [h]
    exact ok51
  · apply branch_false_of_child
    have h : propagate source target 19 8 18 [(4,462075), (7,462075), (3,462075), (5,462075), (2,462075), (0,462075), (1,462075), (6,462075)] = st52 := by decide +kernel
    rw [h]
    exact ok52
def st54 : List (Nat × Nat) := [(4,462055), (7,197735), (3,197735), (5,197735), (2,197735), (0,197735), (1,197735), (6,197735)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok54 : bitSearch source target 19 8 st54 = false := by
  decide +kernel
def st55 : List (Nat × Nat) := [(4,462039), (7,265367), (3,265367), (5,265367), (2,265367), (0,265367), (1,265367), (6,265367)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok55 : bitSearch source target 19 8 st55 = false := by
  decide +kernel
def st56 : List (Nat × Nat) := [(4,462007), (7,197655), (3,197655), (5,197655), (2,197655), (0,197655), (1,197655), (6,197655)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok56 : bitSearch source target 19 8 st56 = false := by
  decide +kernel
def st57 : List (Nat × Nat) := [(4,461943), (7,265255), (3,265255), (5,265255), (2,265255), (0,265255), (1,265255), (6,265255)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok57 : bitSearch source target 19 8 st57 = false := by
  decide +kernel
def st58 : List (Nat × Nat) := [(4,461047), (7,461044), (3,461044), (5,461044), (2,461044), (0,461044), (1,461044), (6,461044)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok58 : bitSearch source target 19 8 st58 = false := by
  decide +kernel
def st59 : List (Nat × Nat) := [(4,460023), (7,459940), (3,459940), (5,459940), (2,459940), (0,459940), (1,459940), (6,459940)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok59 : bitSearch source target 19 8 st59 = false := by
  decide +kernel
def st60 : List (Nat × Nat) := [(4,396535), (7,396372), (3,396372), (5,396372), (2,396372), (0,396372), (1,396372), (6,396372)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok60 : bitSearch source target 19 8 st60 = false := by
  decide +kernel
def st61 : List (Nat × Nat) := [(4,330999), (7,330836), (3,330836), (5,330836), (2,330836), (0,330836), (1,330836), (6,330836)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok61 : bitSearch source target 19 8 st61 = false := by
  decide +kernel
def st62 : List (Nat × Nat) := [(4,199927), (7,199844), (3,199844), (5,199844), (2,199844), (0,199844), (1,199844), (6,199844)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok62 : bitSearch source target 19 8 st62 = false := by
  decide +kernel
def st63 : List (Nat × Nat) := [(8,462071), (4,462071), (7,462071), (3,462071), (5,462071), (2,462071), (0,462071), (1,462071), (6,462071)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok63 : bitSearch source target 19 9 st63 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 462071 [(4,462071), (7,462071), (3,462071), (5,462071), (2,462071), (0,462071), (1,462071), (6,462071)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 2 [(4,462071), (7,462071), (3,462071), (5,462071), (2,462071), (0,462071), (1,462071), (6,462071)] = st43 := by decide +kernel
    rw [h]
    exact ok43
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 4 [(4,462071), (7,462071), (3,462071), (5,462071), (2,462071), (0,462071), (1,462071), (6,462071)] = st54 := by decide +kernel
    rw [h]
    exact ok54
  · apply branch_false_of_child
    have h : propagate source target 19 8 5 [(4,462071), (7,462071), (3,462071), (5,462071), (2,462071), (0,462071), (1,462071), (6,462071)] = st55 := by decide +kernel
    rw [h]
    exact ok55
  · apply branch_false_of_child
    have h : propagate source target 19 8 6 [(4,462071), (7,462071), (3,462071), (5,462071), (2,462071), (0,462071), (1,462071), (6,462071)] = st56 := by decide +kernel
    rw [h]
    exact ok56
  · apply branch_false_of_child
    have h : propagate source target 19 8 7 [(4,462071), (7,462071), (3,462071), (5,462071), (2,462071), (0,462071), (1,462071), (6,462071)] = st57 := by decide +kernel
    rw [h]
    exact ok57
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 10 [(4,462071), (7,462071), (3,462071), (5,462071), (2,462071), (0,462071), (1,462071), (6,462071)] = st58 := by decide +kernel
    rw [h]
    exact ok58
  · apply branch_false_of_child
    have h : propagate source target 19 8 11 [(4,462071), (7,462071), (3,462071), (5,462071), (2,462071), (0,462071), (1,462071), (6,462071)] = st59 := by decide +kernel
    rw [h]
    exact ok59
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 16 [(4,462071), (7,462071), (3,462071), (5,462071), (2,462071), (0,462071), (1,462071), (6,462071)] = st60 := by decide +kernel
    rw [h]
    exact ok60
  · apply branch_false_of_child
    have h : propagate source target 19 8 17 [(4,462071), (7,462071), (3,462071), (5,462071), (2,462071), (0,462071), (1,462071), (6,462071)] = st61 := by decide +kernel
    rw [h]
    exact ok61
  · apply branch_false_of_child
    have h : propagate source target 19 8 18 [(4,462071), (7,462071), (3,462071), (5,462071), (2,462071), (0,462071), (1,462071), (6,462071)] = st62 := by decide +kernel
    rw [h]
    exact ok62
def st64 : List (Nat × Nat) := [(4,210542), (7,12910), (3,12910), (5,12910), (2,12910), (0,12910), (1,12910), (6,12910)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok64 : bitSearch source target 19 8 st64 = false := by
  decide +kernel
def st65 : List (Nat × Nat) := [(4,210541), (7,12909), (3,12909), (5,12909), (2,12909), (0,12909), (1,12909), (6,12909)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok65 : bitSearch source target 19 8 st65 = false := by
  decide +kernel
def st66 : List (Nat × Nat) := [(4,210539), (7,197739), (3,197739), (5,197739), (2,197739), (0,197739), (1,197739), (6,197739)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok66 : bitSearch source target 19 8 st66 = false := by
  decide +kernel
def st67 : List (Nat × Nat) := [(4,210535), (7,197735), (3,197735), (5,197735), (2,197735), (0,197735), (1,197735), (6,197735)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok67 : bitSearch source target 19 8 st67 = false := by
  decide +kernel
def st68 : List (Nat × Nat) := [(4,210479), (7,210447), (3,210447), (5,210447), (2,210447), (0,210447), (1,210447), (6,210447)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok68 : bitSearch source target 19 8 st68 = false := by
  decide +kernel
def st69 : List (Nat × Nat) := [(4,206447), (7,205379), (3,205379), (5,205379), (2,205379), (0,205379), (1,205379), (6,205379)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok69 : bitSearch source target 19 8 st69 = false := by
  decide +kernel
def st70 : List (Nat × Nat) := [(4,202351), (7,201283), (3,201283), (5,201283), (2,201283), (0,201283), (1,201283), (6,201283)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok70 : bitSearch source target 19 8 st70 = false := by
  decide +kernel
def st71 : List (Nat × Nat) := [(4,145007), (7,144460), (3,144460), (5,144460), (2,144460), (0,144460), (1,144460), (6,144460)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok71 : bitSearch source target 19 8 st71 = false := by
  decide +kernel
def st72 : List (Nat × Nat) := [(4,79471), (7,78924), (3,78924), (5,78924), (2,78924), (0,78924), (1,78924), (6,78924)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok72 : bitSearch source target 19 8 st72 = false := by
  decide +kernel
def st73 : List (Nat × Nat) := [(8,210543), (4,210543), (7,210543), (3,210543), (5,210543), (2,210543), (0,210543), (1,210543), (6,210543)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok73 : bitSearch source target 19 9 st73 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 210543 [(4,210543), (7,210543), (3,210543), (5,210543), (2,210543), (0,210543), (1,210543), (6,210543)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 8 0 [(4,210543), (7,210543), (3,210543), (5,210543), (2,210543), (0,210543), (1,210543), (6,210543)] = st64 := by decide +kernel
    rw [h]
    exact ok64
  · apply branch_false_of_child
    have h : propagate source target 19 8 1 [(4,210543), (7,210543), (3,210543), (5,210543), (2,210543), (0,210543), (1,210543), (6,210543)] = st65 := by decide +kernel
    rw [h]
    exact ok65
  · apply branch_false_of_child
    have h : propagate source target 19 8 2 [(4,210543), (7,210543), (3,210543), (5,210543), (2,210543), (0,210543), (1,210543), (6,210543)] = st66 := by decide +kernel
    rw [h]
    exact ok66
  · apply branch_false_of_child
    have h : propagate source target 19 8 3 [(4,210543), (7,210543), (3,210543), (5,210543), (2,210543), (0,210543), (1,210543), (6,210543)] = st67 := by decide +kernel
    rw [h]
    exact ok67
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 6 [(4,210543), (7,210543), (3,210543), (5,210543), (2,210543), (0,210543), (1,210543), (6,210543)] = st68 := by decide +kernel
    rw [h]
    exact ok68
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 12 [(4,210543), (7,210543), (3,210543), (5,210543), (2,210543), (0,210543), (1,210543), (6,210543)] = st69 := by decide +kernel
    rw [h]
    exact ok69
  · apply branch_false_of_child
    have h : propagate source target 19 8 13 [(4,210543), (7,210543), (3,210543), (5,210543), (2,210543), (0,210543), (1,210543), (6,210543)] = st70 := by decide +kernel
    rw [h]
    exact ok70
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 16 [(4,210543), (7,210543), (3,210543), (5,210543), (2,210543), (0,210543), (1,210543), (6,210543)] = st71 := by decide +kernel
    rw [h]
    exact ok71
  · apply branch_false_of_child
    have h : propagate source target 19 8 17 [(4,210543), (7,210543), (3,210543), (5,210543), (2,210543), (0,210543), (1,210543), (6,210543)] = st72 := by decide +kernel
    rw [h]
    exact ok72
  · decide +kernel
def st74 : List (Nat × Nat) := [(4,315038), (7,49822), (3,49822), (5,49822), (2,49822), (0,49822), (1,49822), (6,49822)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok74 : bitSearch source target 19 8 st74 = false := by
  decide +kernel
def st75 : List (Nat × Nat) := [(4,315037), (7,49821), (3,49821), (5,49821), (2,49821), (0,49821), (1,49821), (6,49821)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok75 : bitSearch source target 19 8 st75 = false := by
  decide +kernel
def st76 : List (Nat × Nat) := [(4,315035), (7,265371), (3,265371), (5,265371), (2,265371), (0,265371), (1,265371), (6,265371)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok76 : bitSearch source target 19 8 st76 = false := by
  decide +kernel
def st77 : List (Nat × Nat) := [(4,315031), (7,265367), (3,265367), (5,265367), (2,265367), (0,265367), (1,265367), (6,265367)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok77 : bitSearch source target 19 8 st77 = false := by
  decide +kernel
def st78 : List (Nat × Nat) := [(4,314911), (7,314895), (3,314895), (5,314895), (2,314895), (0,314895), (1,314895), (6,314895)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok78 : bitSearch source target 19 8 st78 = false := by
  decide +kernel
def st79 : List (Nat × Nat) := [(4,312991), (7,312460), (3,312460), (5,312460), (2,312460), (0,312460), (1,312460), (6,312460)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok79 : bitSearch source target 19 8 st79 = false := by
  decide +kernel
def st80 : List (Nat × Nat) := [(4,298655), (7,297603), (3,297603), (5,297603), (2,297603), (0,297603), (1,297603), (6,297603)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok80 : bitSearch source target 19 8 st80 = false := by
  decide +kernel
def st81 : List (Nat × Nat) := [(4,282271), (7,281219), (3,281219), (5,281219), (2,281219), (0,281219), (1,281219), (6,281219)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok81 : bitSearch source target 19 8 st81 = false := by
  decide +kernel
def st82 : List (Nat × Nat) := [(4,52895), (7,52364), (3,52364), (5,52364), (2,52364), (0,52364), (1,52364), (6,52364)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok82 : bitSearch source target 19 8 st82 = false := by
  decide +kernel
def st83 : List (Nat × Nat) := [(8,315039), (4,315039), (7,315039), (3,315039), (5,315039), (2,315039), (0,315039), (1,315039), (6,315039)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok83 : bitSearch source target 19 9 st83 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 315039 [(4,315039), (7,315039), (3,315039), (5,315039), (2,315039), (0,315039), (1,315039), (6,315039)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 8 0 [(4,315039), (7,315039), (3,315039), (5,315039), (2,315039), (0,315039), (1,315039), (6,315039)] = st74 := by decide +kernel
    rw [h]
    exact ok74
  · apply branch_false_of_child
    have h : propagate source target 19 8 1 [(4,315039), (7,315039), (3,315039), (5,315039), (2,315039), (0,315039), (1,315039), (6,315039)] = st75 := by decide +kernel
    rw [h]
    exact ok75
  · apply branch_false_of_child
    have h : propagate source target 19 8 2 [(4,315039), (7,315039), (3,315039), (5,315039), (2,315039), (0,315039), (1,315039), (6,315039)] = st76 := by decide +kernel
    rw [h]
    exact ok76
  · apply branch_false_of_child
    have h : propagate source target 19 8 3 [(4,315039), (7,315039), (3,315039), (5,315039), (2,315039), (0,315039), (1,315039), (6,315039)] = st77 := by decide +kernel
    rw [h]
    exact ok77
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 7 [(4,315039), (7,315039), (3,315039), (5,315039), (2,315039), (0,315039), (1,315039), (6,315039)] = st78 := by decide +kernel
    rw [h]
    exact ok78
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 11 [(4,315039), (7,315039), (3,315039), (5,315039), (2,315039), (0,315039), (1,315039), (6,315039)] = st79 := by decide +kernel
    rw [h]
    exact ok79
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 14 [(4,315039), (7,315039), (3,315039), (5,315039), (2,315039), (0,315039), (1,315039), (6,315039)] = st80 := by decide +kernel
    rw [h]
    exact ok80
  · apply branch_false_of_child
    have h : propagate source target 19 8 15 [(4,315039), (7,315039), (3,315039), (5,315039), (2,315039), (0,315039), (1,315039), (6,315039)] = st81 := by decide +kernel
    rw [h]
    exact ok81
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 18 [(4,315039), (7,315039), (3,315039), (5,315039), (2,315039), (0,315039), (1,315039), (6,315039)] = st82 := by decide +kernel
    rw [h]
    exact ok82
def st84 : List (Nat × Nat) := [(4,210718), (7,12830), (3,12830), (5,12830), (2,12830), (0,12830), (1,12830), (6,12830)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok84 : bitSearch source target 19 8 st84 = false := by
  decide +kernel
def st85 : List (Nat × Nat) := [(4,210717), (7,12829), (3,12829), (5,12829), (2,12829), (0,12829), (1,12829), (6,12829)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok85 : bitSearch source target 19 8 st85 = false := by
  decide +kernel
def st86 : List (Nat × Nat) := [(4,210715), (7,197659), (3,197659), (5,197659), (2,197659), (0,197659), (1,197659), (6,197659)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok86 : bitSearch source target 19 8 st86 = false := by
  decide +kernel
def st87 : List (Nat × Nat) := [(4,210711), (7,197655), (3,197655), (5,197655), (2,197655), (0,197655), (1,197655), (6,197655)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok87 : bitSearch source target 19 8 st87 = false := by
  decide +kernel
def st88 : List (Nat × Nat) := [(4,210703), (7,210447), (3,210447), (5,210447), (2,210447), (0,210447), (1,210447), (6,210447)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok88 : bitSearch source target 19 8 st88 = false := by
  decide +kernel
def st89 : List (Nat × Nat) := [(4,206623), (7,205587), (3,205587), (5,205587), (2,205587), (0,205587), (1,205587), (6,205587)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok89 : bitSearch source target 19 8 st89 = false := by
  decide +kernel
def st90 : List (Nat × Nat) := [(4,202527), (7,201491), (3,201491), (5,201491), (2,201491), (0,201491), (1,201491), (6,201491)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok90 : bitSearch source target 19 8 st90 = false := by
  decide +kernel
def st91 : List (Nat × Nat) := [(4,145183), (7,144668), (3,144668), (5,144668), (2,144668), (0,144668), (1,144668), (6,144668)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok91 : bitSearch source target 19 8 st91 = false := by
  decide +kernel
def st92 : List (Nat × Nat) := [(4,79647), (7,79132), (3,79132), (5,79132), (2,79132), (0,79132), (1,79132), (6,79132)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok92 : bitSearch source target 19 8 st92 = false := by
  decide +kernel
def st93 : List (Nat × Nat) := [(8,210719), (4,210719), (7,210719), (3,210719), (5,210719), (2,210719), (0,210719), (1,210719), (6,210719)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok93 : bitSearch source target 19 9 st93 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 210719 [(4,210719), (7,210719), (3,210719), (5,210719), (2,210719), (0,210719), (1,210719), (6,210719)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 8 0 [(4,210719), (7,210719), (3,210719), (5,210719), (2,210719), (0,210719), (1,210719), (6,210719)] = st84 := by decide +kernel
    rw [h]
    exact ok84
  · apply branch_false_of_child
    have h : propagate source target 19 8 1 [(4,210719), (7,210719), (3,210719), (5,210719), (2,210719), (0,210719), (1,210719), (6,210719)] = st85 := by decide +kernel
    rw [h]
    exact ok85
  · apply branch_false_of_child
    have h : propagate source target 19 8 2 [(4,210719), (7,210719), (3,210719), (5,210719), (2,210719), (0,210719), (1,210719), (6,210719)] = st86 := by decide +kernel
    rw [h]
    exact ok86
  · apply branch_false_of_child
    have h : propagate source target 19 8 3 [(4,210719), (7,210719), (3,210719), (5,210719), (2,210719), (0,210719), (1,210719), (6,210719)] = st87 := by decide +kernel
    rw [h]
    exact ok87
  · apply branch_false_of_child
    have h : propagate source target 19 8 4 [(4,210719), (7,210719), (3,210719), (5,210719), (2,210719), (0,210719), (1,210719), (6,210719)] = st88 := by decide +kernel
    rw [h]
    exact ok88
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 12 [(4,210719), (7,210719), (3,210719), (5,210719), (2,210719), (0,210719), (1,210719), (6,210719)] = st89 := by decide +kernel
    rw [h]
    exact ok89
  · apply branch_false_of_child
    have h : propagate source target 19 8 13 [(4,210719), (7,210719), (3,210719), (5,210719), (2,210719), (0,210719), (1,210719), (6,210719)] = st90 := by decide +kernel
    rw [h]
    exact ok90
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 16 [(4,210719), (7,210719), (3,210719), (5,210719), (2,210719), (0,210719), (1,210719), (6,210719)] = st91 := by decide +kernel
    rw [h]
    exact ok91
  · apply branch_false_of_child
    have h : propagate source target 19 8 17 [(4,210719), (7,210719), (3,210719), (5,210719), (2,210719), (0,210719), (1,210719), (6,210719)] = st92 := by decide +kernel
    rw [h]
    exact ok92
  · decide +kernel
def st94 : List (Nat × Nat) := [(4,315182), (7,49710), (3,49710), (5,49710), (2,49710), (0,49710), (1,49710), (6,49710)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok94 : bitSearch source target 19 8 st94 = false := by
  decide +kernel
def st95 : List (Nat × Nat) := [(4,315181), (7,49709), (3,49709), (5,49709), (2,49709), (0,49709), (1,49709), (6,49709)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok95 : bitSearch source target 19 8 st95 = false := by
  decide +kernel
def st96 : List (Nat × Nat) := [(4,315179), (7,265259), (3,265259), (5,265259), (2,265259), (0,265259), (1,265259), (6,265259)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok96 : bitSearch source target 19 8 st96 = false := by
  decide +kernel
def st97 : List (Nat × Nat) := [(4,315175), (7,265255), (3,265255), (5,265255), (2,265255), (0,265255), (1,265255), (6,265255)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok97 : bitSearch source target 19 8 st97 = false := by
  decide +kernel
def st98 : List (Nat × Nat) := [(4,315151), (7,314895), (3,314895), (5,314895), (2,314895), (0,314895), (1,314895), (6,314895)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok98 : bitSearch source target 19 8 st98 = false := by
  decide +kernel
def st99 : List (Nat × Nat) := [(4,313135), (7,312620), (3,312620), (5,312620), (2,312620), (0,312620), (1,312620), (6,312620)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok99 : bitSearch source target 19 8 st99 = false := by
  decide +kernel
def st100 : List (Nat × Nat) := [(4,298799), (7,297763), (3,297763), (5,297763), (2,297763), (0,297763), (1,297763), (6,297763)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok100 : bitSearch source target 19 8 st100 = false := by
  decide +kernel
def st101 : List (Nat × Nat) := [(4,282415), (7,281379), (3,281379), (5,281379), (2,281379), (0,281379), (1,281379), (6,281379)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok101 : bitSearch source target 19 8 st101 = false := by
  decide +kernel
def st102 : List (Nat × Nat) := [(4,53039), (7,52524), (3,52524), (5,52524), (2,52524), (0,52524), (1,52524), (6,52524)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok102 : bitSearch source target 19 8 st102 = false := by
  decide +kernel
def st103 : List (Nat × Nat) := [(8,315183), (4,315183), (7,315183), (3,315183), (5,315183), (2,315183), (0,315183), (1,315183), (6,315183)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok103 : bitSearch source target 19 9 st103 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 315183 [(4,315183), (7,315183), (3,315183), (5,315183), (2,315183), (0,315183), (1,315183), (6,315183)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 8 0 [(4,315183), (7,315183), (3,315183), (5,315183), (2,315183), (0,315183), (1,315183), (6,315183)] = st94 := by decide +kernel
    rw [h]
    exact ok94
  · apply branch_false_of_child
    have h : propagate source target 19 8 1 [(4,315183), (7,315183), (3,315183), (5,315183), (2,315183), (0,315183), (1,315183), (6,315183)] = st95 := by decide +kernel
    rw [h]
    exact ok95
  · apply branch_false_of_child
    have h : propagate source target 19 8 2 [(4,315183), (7,315183), (3,315183), (5,315183), (2,315183), (0,315183), (1,315183), (6,315183)] = st96 := by decide +kernel
    rw [h]
    exact ok96
  · apply branch_false_of_child
    have h : propagate source target 19 8 3 [(4,315183), (7,315183), (3,315183), (5,315183), (2,315183), (0,315183), (1,315183), (6,315183)] = st97 := by decide +kernel
    rw [h]
    exact ok97
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 5 [(4,315183), (7,315183), (3,315183), (5,315183), (2,315183), (0,315183), (1,315183), (6,315183)] = st98 := by decide +kernel
    rw [h]
    exact ok98
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 11 [(4,315183), (7,315183), (3,315183), (5,315183), (2,315183), (0,315183), (1,315183), (6,315183)] = st99 := by decide +kernel
    rw [h]
    exact ok99
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 14 [(4,315183), (7,315183), (3,315183), (5,315183), (2,315183), (0,315183), (1,315183), (6,315183)] = st100 := by decide +kernel
    rw [h]
    exact ok100
  · apply branch_false_of_child
    have h : propagate source target 19 8 15 [(4,315183), (7,315183), (3,315183), (5,315183), (2,315183), (0,315183), (1,315183), (6,315183)] = st101 := by decide +kernel
    rw [h]
    exact ok101
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 18 [(4,315183), (7,315183), (3,315183), (5,315183), (2,315183), (0,315183), (1,315183), (6,315183)] = st102 := by decide +kernel
    rw [h]
    exact ok102
def st104 : List (Nat × Nat) := [(8,523968), (4,523968), (7,523968), (3,523968), (5,523968), (2,523968), (0,523968), (1,523968), (6,523968)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok104 : bitSearch source target 19 9 st104 = false := by
  decide +kernel
def st105 : List (Nat × Nat) := [(4,61938), (7,61682), (3,61682), (5,61682), (2,61682), (0,61682), (1,61682), (6,61682)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok105 : bitSearch source target 19 8 st105 = false := by
  decide +kernel
def st106 : List (Nat × Nat) := [(4,61937), (7,61681), (3,61681), (5,61681), (2,61681), (0,61681), (1,61681), (6,61681)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok106 : bitSearch source target 19 8 st106 = false := by
  decide +kernel
def st107 : List (Nat × Nat) := [(4,57843), (7,57683), (3,57683), (5,57683), (2,57683), (0,57683), (1,57683), (6,57683)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok107 : bitSearch source target 19 8 st107 = false := by
  decide +kernel
def st108 : List (Nat × Nat) := [(4,53747), (7,53587), (3,53587), (5,53587), (2,53587), (0,53587), (1,53587), (6,53587)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok108 : bitSearch source target 19 8 st108 = false := by
  decide +kernel
def st109 : List (Nat × Nat) := [(4,45555), (7,45475), (3,45475), (5,45475), (2,45475), (0,45475), (1,45475), (6,45475)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok109 : bitSearch source target 19 8 st109 = false := by
  decide +kernel
def st110 : List (Nat × Nat) := [(4,29171), (7,29091), (3,29091), (5,29091), (2,29091), (0,29091), (1,29091), (6,29091)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok110 : bitSearch source target 19 8 st110 = false := by
  decide +kernel
def st111 : List (Nat × Nat) := [(8,61939), (4,61939), (7,61939), (3,61939), (5,61939), (2,61939), (0,61939), (1,61939), (6,61939)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok111 : bitSearch source target 19 9 st111 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 61939 [(4,61939), (7,61939), (3,61939), (5,61939), (2,61939), (0,61939), (1,61939), (6,61939)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 8 0 [(4,61939), (7,61939), (3,61939), (5,61939), (2,61939), (0,61939), (1,61939), (6,61939)] = st105 := by decide +kernel
    rw [h]
    exact ok105
  · apply branch_false_of_child
    have h : propagate source target 19 8 1 [(4,61939), (7,61939), (3,61939), (5,61939), (2,61939), (0,61939), (1,61939), (6,61939)] = st106 := by decide +kernel
    rw [h]
    exact ok106
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 12 [(4,61939), (7,61939), (3,61939), (5,61939), (2,61939), (0,61939), (1,61939), (6,61939)] = st107 := by decide +kernel
    rw [h]
    exact ok107
  · apply branch_false_of_child
    have h : propagate source target 19 8 13 [(4,61939), (7,61939), (3,61939), (5,61939), (2,61939), (0,61939), (1,61939), (6,61939)] = st108 := by decide +kernel
    rw [h]
    exact ok108
  · apply branch_false_of_child
    have h : propagate source target 19 8 14 [(4,61939), (7,61939), (3,61939), (5,61939), (2,61939), (0,61939), (1,61939), (6,61939)] = st109 := by decide +kernel
    rw [h]
    exact ok109
  · apply branch_false_of_child
    have h : propagate source target 19 8 15 [(4,61939), (7,61939), (3,61939), (5,61939), (2,61939), (0,61939), (1,61939), (6,61939)] = st110 := by decide +kernel
    rw [h]
    exact ok110
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st112 : List (Nat × Nat) := [(4,461304), (7,461048), (3,461048), (5,461048), (2,461048), (0,461048), (1,461048), (6,461048)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok112 : bitSearch source target 19 8 st112 = false := by
  decide +kernel
def st113 : List (Nat × Nat) := [(4,461300), (7,461044), (3,461044), (5,461044), (2,461044), (0,461044), (1,461044), (6,461044)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok113 : bitSearch source target 19 8 st113 = false := by
  decide +kernel
def st114 : List (Nat × Nat) := [(4,459260), (7,459180), (3,459180), (5,459180), (2,459180), (0,459180), (1,459180), (6,459180)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok114 : bitSearch source target 19 8 st114 = false := by
  decide +kernel
def st115 : List (Nat × Nat) := [(4,395772), (7,395612), (3,395612), (5,395612), (2,395612), (0,395612), (1,395612), (6,395612)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok115 : bitSearch source target 19 8 st115 = false := by
  decide +kernel
def st116 : List (Nat × Nat) := [(4,330236), (7,330076), (3,330076), (5,330076), (2,330076), (0,330076), (1,330076), (6,330076)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok116 : bitSearch source target 19 8 st116 = false := by
  decide +kernel
def st117 : List (Nat × Nat) := [(4,199164), (7,199084), (3,199084), (5,199084), (2,199084), (0,199084), (1,199084), (6,199084)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok117 : bitSearch source target 19 8 st117 = false := by
  decide +kernel
def st118 : List (Nat × Nat) := [(8,461308), (4,461308), (7,461308), (3,461308), (5,461308), (2,461308), (0,461308), (1,461308), (6,461308)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok118 : bitSearch source target 19 9 st118 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 461308 [(4,461308), (7,461308), (3,461308), (5,461308), (2,461308), (0,461308), (1,461308), (6,461308)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 2 [(4,461308), (7,461308), (3,461308), (5,461308), (2,461308), (0,461308), (1,461308), (6,461308)] = st112 := by decide +kernel
    rw [h]
    exact ok112
  · apply branch_false_of_child
    have h : propagate source target 19 8 3 [(4,461308), (7,461308), (3,461308), (5,461308), (2,461308), (0,461308), (1,461308), (6,461308)] = st113 := by decide +kernel
    rw [h]
    exact ok113
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 11 [(4,461308), (7,461308), (3,461308), (5,461308), (2,461308), (0,461308), (1,461308), (6,461308)] = st114 := by decide +kernel
    rw [h]
    exact ok114
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 16 [(4,461308), (7,461308), (3,461308), (5,461308), (2,461308), (0,461308), (1,461308), (6,461308)] = st115 := by decide +kernel
    rw [h]
    exact ok115
  · apply branch_false_of_child
    have h : propagate source target 19 8 17 [(4,461308), (7,461308), (3,461308), (5,461308), (2,461308), (0,461308), (1,461308), (6,461308)] = st116 := by decide +kernel
    rw [h]
    exact ok116
  · apply branch_false_of_child
    have h : propagate source target 19 8 18 [(4,461308), (7,461308), (3,461308), (5,461308), (2,461308), (0,461308), (1,461308), (6,461308)] = st117 := by decide +kernel
    rw [h]
    exact ok117
def st119 : List (Nat × Nat) := [(4,509352), (7,459944), (3,459944), (5,459944), (2,459944), (0,459944), (1,459944), (6,459944)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok119 : bitSearch source target 19 8 st119 = false := by
  decide +kernel
def st120 : List (Nat × Nat) := [(4,509348), (7,459940), (3,459940), (5,459940), (2,459940), (0,459940), (1,459940), (6,459940)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok120 : bitSearch source target 19 8 st120 = false := by
  decide +kernel
def st121 : List (Nat × Nat) := [(4,509324), (7,312460), (3,312460), (5,312460), (2,312460), (0,312460), (1,312460), (6,312460)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok121 : bitSearch source target 19 8 st121 = false := by
  decide +kernel
def st122 : List (Nat × Nat) := [(4,509228), (7,312620), (3,312620), (5,312620), (2,312620), (0,312620), (1,312620), (6,312620)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok122 : bitSearch source target 19 8 st122 = false := by
  decide +kernel
def st123 : List (Nat × Nat) := [(4,509100), (7,509056), (3,509056), (5,509056), (2,509056), (0,509056), (1,509056), (6,509056)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok123 : bitSearch source target 19 8 st123 = false := by
  decide +kernel
def st124 : List (Nat × Nat) := [(4,508332), (7,459180), (3,459180), (5,459180), (2,459180), (0,459180), (1,459180), (6,459180)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok124 : bitSearch source target 19 8 st124 = false := by
  decide +kernel
def st125 : List (Nat × Nat) := [(4,247212), (7,247212), (3,247212), (5,247212), (2,247212), (0,247212), (1,247212), (6,247212)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok125 : bitSearch source target 19 8 st125 = false := by
  decide +kernel
def st126 : List (Nat × Nat) := [(8,509356), (4,509356), (7,509356), (3,509356), (5,509356), (2,509356), (0,509356), (1,509356), (6,509356)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok126 : bitSearch source target 19 9 st126 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 509356 [(4,509356), (7,509356), (3,509356), (5,509356), (2,509356), (0,509356), (1,509356), (6,509356)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 2 [(4,509356), (7,509356), (3,509356), (5,509356), (2,509356), (0,509356), (1,509356), (6,509356)] = st119 := by decide +kernel
    rw [h]
    exact ok119
  · apply branch_false_of_child
    have h : propagate source target 19 8 3 [(4,509356), (7,509356), (3,509356), (5,509356), (2,509356), (0,509356), (1,509356), (6,509356)] = st120 := by decide +kernel
    rw [h]
    exact ok120
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 5 [(4,509356), (7,509356), (3,509356), (5,509356), (2,509356), (0,509356), (1,509356), (6,509356)] = st121 := by decide +kernel
    rw [h]
    exact ok121
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 7 [(4,509356), (7,509356), (3,509356), (5,509356), (2,509356), (0,509356), (1,509356), (6,509356)] = st122 := by decide +kernel
    rw [h]
    exact ok122
  · apply branch_false_of_child
    have h : propagate source target 19 8 8 [(4,509356), (7,509356), (3,509356), (5,509356), (2,509356), (0,509356), (1,509356), (6,509356)] = st123 := by decide +kernel
    rw [h]
    exact ok123
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 10 [(4,509356), (7,509356), (3,509356), (5,509356), (2,509356), (0,509356), (1,509356), (6,509356)] = st124 := by decide +kernel
    rw [h]
    exact ok124
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 18 [(4,509356), (7,509356), (3,509356), (5,509356), (2,509356), (0,509356), (1,509356), (6,509356)] = st125 := by decide +kernel
    rw [h]
    exact ok125
def st127 : List (Nat × Nat) := [(4,254802), (7,57938), (3,57938), (5,57938), (2,57938), (0,57938), (1,57938), (6,57938)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok127 : bitSearch source target 19 8 st127 = false := by
  decide +kernel
def st128 : List (Nat × Nat) := [(4,254801), (7,57937), (3,57937), (5,57937), (2,57937), (0,57937), (1,57937), (6,57937)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok128 : bitSearch source target 19 8 st128 = false := by
  decide +kernel
def st129 : List (Nat × Nat) := [(4,254787), (7,205379), (3,205379), (5,205379), (2,205379), (0,205379), (1,205379), (6,205379)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok129 : bitSearch source target 19 8 st129 = false := by
  decide +kernel
def st130 : List (Nat × Nat) := [(4,254739), (7,205587), (3,205587), (5,205587), (2,205587), (0,205587), (1,205587), (6,205587)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok130 : bitSearch source target 19 8 st130 = false := by
  decide +kernel
def st131 : List (Nat × Nat) := [(4,254547), (7,254528), (3,254528), (5,254528), (2,254528), (0,254528), (1,254528), (6,254528)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok131 : bitSearch source target 19 8 st131 = false := by
  decide +kernel
def st132 : List (Nat × Nat) := [(4,254291), (7,57683), (3,57683), (5,57683), (2,57683), (0,57683), (1,57683), (6,57683)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok132 : bitSearch source target 19 8 st132 = false := by
  decide +kernel
def st133 : List (Nat × Nat) := [(4,246611), (7,246611), (3,246611), (5,246611), (2,246611), (0,246611), (1,246611), (6,246611)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok133 : bitSearch source target 19 8 st133 = false := by
  decide +kernel
def st134 : List (Nat × Nat) := [(8,254803), (4,254803), (7,254803), (3,254803), (5,254803), (2,254803), (0,254803), (1,254803), (6,254803)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok134 : bitSearch source target 19 9 st134 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 254803 [(4,254803), (7,254803), (3,254803), (5,254803), (2,254803), (0,254803), (1,254803), (6,254803)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 8 0 [(4,254803), (7,254803), (3,254803), (5,254803), (2,254803), (0,254803), (1,254803), (6,254803)] = st127 := by decide +kernel
    rw [h]
    exact ok127
  · apply branch_false_of_child
    have h : propagate source target 19 8 1 [(4,254803), (7,254803), (3,254803), (5,254803), (2,254803), (0,254803), (1,254803), (6,254803)] = st128 := by decide +kernel
    rw [h]
    exact ok128
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 4 [(4,254803), (7,254803), (3,254803), (5,254803), (2,254803), (0,254803), (1,254803), (6,254803)] = st129 := by decide +kernel
    rw [h]
    exact ok129
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 6 [(4,254803), (7,254803), (3,254803), (5,254803), (2,254803), (0,254803), (1,254803), (6,254803)] = st130 := by decide +kernel
    rw [h]
    exact ok130
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 8 [(4,254803), (7,254803), (3,254803), (5,254803), (2,254803), (0,254803), (1,254803), (6,254803)] = st131 := by decide +kernel
    rw [h]
    exact ok131
  · apply branch_false_of_child
    have h : propagate source target 19 8 9 [(4,254803), (7,254803), (3,254803), (5,254803), (2,254803), (0,254803), (1,254803), (6,254803)] = st132 := by decide +kernel
    rw [h]
    exact ok132
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 13 [(4,254803), (7,254803), (3,254803), (5,254803), (2,254803), (0,254803), (1,254803), (6,254803)] = st133 := by decide +kernel
    rw [h]
    exact ok133
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st135 : List (Nat × Nat) := [(4,250706), (7,53842), (3,53842), (5,53842), (2,53842), (0,53842), (1,53842), (6,53842)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok135 : bitSearch source target 19 8 st135 = false := by
  decide +kernel
def st136 : List (Nat × Nat) := [(4,250705), (7,53841), (3,53841), (5,53841), (2,53841), (0,53841), (1,53841), (6,53841)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok136 : bitSearch source target 19 8 st136 = false := by
  decide +kernel
def st137 : List (Nat × Nat) := [(4,250691), (7,201283), (3,201283), (5,201283), (2,201283), (0,201283), (1,201283), (6,201283)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok137 : bitSearch source target 19 8 st137 = false := by
  decide +kernel
def st138 : List (Nat × Nat) := [(4,250643), (7,201491), (3,201491), (5,201491), (2,201491), (0,201491), (1,201491), (6,201491)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok138 : bitSearch source target 19 8 st138 = false := by
  decide +kernel
def st139 : List (Nat × Nat) := [(4,250451), (7,250432), (3,250432), (5,250432), (2,250432), (0,250432), (1,250432), (6,250432)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok139 : bitSearch source target 19 8 st139 = false := by
  decide +kernel
def st140 : List (Nat × Nat) := [(4,250195), (7,53587), (3,53587), (5,53587), (2,53587), (0,53587), (1,53587), (6,53587)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok140 : bitSearch source target 19 8 st140 = false := by
  decide +kernel
def st141 : List (Nat × Nat) := [(8,250707), (4,250707), (7,250707), (3,250707), (5,250707), (2,250707), (0,250707), (1,250707), (6,250707)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok141 : bitSearch source target 19 9 st141 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 250707 [(4,250707), (7,250707), (3,250707), (5,250707), (2,250707), (0,250707), (1,250707), (6,250707)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 8 0 [(4,250707), (7,250707), (3,250707), (5,250707), (2,250707), (0,250707), (1,250707), (6,250707)] = st135 := by decide +kernel
    rw [h]
    exact ok135
  · apply branch_false_of_child
    have h : propagate source target 19 8 1 [(4,250707), (7,250707), (3,250707), (5,250707), (2,250707), (0,250707), (1,250707), (6,250707)] = st136 := by decide +kernel
    rw [h]
    exact ok136
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 4 [(4,250707), (7,250707), (3,250707), (5,250707), (2,250707), (0,250707), (1,250707), (6,250707)] = st137 := by decide +kernel
    rw [h]
    exact ok137
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 6 [(4,250707), (7,250707), (3,250707), (5,250707), (2,250707), (0,250707), (1,250707), (6,250707)] = st138 := by decide +kernel
    rw [h]
    exact ok138
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 8 [(4,250707), (7,250707), (3,250707), (5,250707), (2,250707), (0,250707), (1,250707), (6,250707)] = st139 := by decide +kernel
    rw [h]
    exact ok139
  · apply branch_false_of_child
    have h : propagate source target 19 8 9 [(4,250707), (7,250707), (3,250707), (5,250707), (2,250707), (0,250707), (1,250707), (6,250707)] = st140 := by decide +kernel
    rw [h]
    exact ok140
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 12 [(4,250707), (7,250707), (3,250707), (5,250707), (2,250707), (0,250707), (1,250707), (6,250707)] = st133 := by decide +kernel
    rw [h]
    exact ok133
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st142 : List (Nat × Nat) := [(4,310178), (7,45730), (3,45730), (5,45730), (2,45730), (0,45730), (1,45730), (6,45730)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok142 : bitSearch source target 19 8 st142 = false := by
  decide +kernel
def st143 : List (Nat × Nat) := [(4,310177), (7,45729), (3,45729), (5,45729), (2,45729), (0,45729), (1,45729), (6,45729)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok143 : bitSearch source target 19 8 st143 = false := by
  decide +kernel
def st144 : List (Nat × Nat) := [(4,310147), (7,297603), (3,297603), (5,297603), (2,297603), (0,297603), (1,297603), (6,297603)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok144 : bitSearch source target 19 8 st144 = false := by
  decide +kernel
def st145 : List (Nat × Nat) := [(4,310051), (7,297763), (3,297763), (5,297763), (2,297763), (0,297763), (1,297763), (6,297763)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok145 : bitSearch source target 19 8 st145 = false := by
  decide +kernel
def st146 : List (Nat × Nat) := [(4,309923), (7,309888), (3,309888), (5,309888), (2,309888), (0,309888), (1,309888), (6,309888)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok146 : bitSearch source target 19 8 st146 = false := by
  decide +kernel
def st147 : List (Nat × Nat) := [(4,309667), (7,45475), (3,45475), (5,45475), (2,45475), (0,45475), (1,45475), (6,45475)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok147 : bitSearch source target 19 8 st147 = false := by
  decide +kernel
def st148 : List (Nat × Nat) := [(4,277411), (7,277411), (3,277411), (5,277411), (2,277411), (0,277411), (1,277411), (6,277411)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok148 : bitSearch source target 19 8 st148 = false := by
  decide +kernel
def st149 : List (Nat × Nat) := [(8,310179), (4,310179), (7,310179), (3,310179), (5,310179), (2,310179), (0,310179), (1,310179), (6,310179)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok149 : bitSearch source target 19 9 st149 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 310179 [(4,310179), (7,310179), (3,310179), (5,310179), (2,310179), (0,310179), (1,310179), (6,310179)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 8 0 [(4,310179), (7,310179), (3,310179), (5,310179), (2,310179), (0,310179), (1,310179), (6,310179)] = st142 := by decide +kernel
    rw [h]
    exact ok142
  · apply branch_false_of_child
    have h : propagate source target 19 8 1 [(4,310179), (7,310179), (3,310179), (5,310179), (2,310179), (0,310179), (1,310179), (6,310179)] = st143 := by decide +kernel
    rw [h]
    exact ok143
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 5 [(4,310179), (7,310179), (3,310179), (5,310179), (2,310179), (0,310179), (1,310179), (6,310179)] = st144 := by decide +kernel
    rw [h]
    exact ok144
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 7 [(4,310179), (7,310179), (3,310179), (5,310179), (2,310179), (0,310179), (1,310179), (6,310179)] = st145 := by decide +kernel
    rw [h]
    exact ok145
  · apply branch_false_of_child
    have h : propagate source target 19 8 8 [(4,310179), (7,310179), (3,310179), (5,310179), (2,310179), (0,310179), (1,310179), (6,310179)] = st146 := by decide +kernel
    rw [h]
    exact ok146
  · apply branch_false_of_child
    have h : propagate source target 19 8 9 [(4,310179), (7,310179), (3,310179), (5,310179), (2,310179), (0,310179), (1,310179), (6,310179)] = st147 := by decide +kernel
    rw [h]
    exact ok147
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 15 [(4,310179), (7,310179), (3,310179), (5,310179), (2,310179), (0,310179), (1,310179), (6,310179)] = st148 := by decide +kernel
    rw [h]
    exact ok148
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st150 : List (Nat × Nat) := [(4,293794), (7,29346), (3,29346), (5,29346), (2,29346), (0,29346), (1,29346), (6,29346)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok150 : bitSearch source target 19 8 st150 = false := by
  decide +kernel
def st151 : List (Nat × Nat) := [(4,293793), (7,29345), (3,29345), (5,29345), (2,29345), (0,29345), (1,29345), (6,29345)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok151 : bitSearch source target 19 8 st151 = false := by
  decide +kernel
def st152 : List (Nat × Nat) := [(4,293763), (7,281219), (3,281219), (5,281219), (2,281219), (0,281219), (1,281219), (6,281219)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok152 : bitSearch source target 19 8 st152 = false := by
  decide +kernel
def st153 : List (Nat × Nat) := [(4,293667), (7,281379), (3,281379), (5,281379), (2,281379), (0,281379), (1,281379), (6,281379)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok153 : bitSearch source target 19 8 st153 = false := by
  decide +kernel
def st154 : List (Nat × Nat) := [(4,293539), (7,293504), (3,293504), (5,293504), (2,293504), (0,293504), (1,293504), (6,293504)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok154 : bitSearch source target 19 8 st154 = false := by
  decide +kernel
def st155 : List (Nat × Nat) := [(4,293283), (7,29091), (3,29091), (5,29091), (2,29091), (0,29091), (1,29091), (6,29091)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok155 : bitSearch source target 19 8 st155 = false := by
  decide +kernel
def st156 : List (Nat × Nat) := [(8,293795), (4,293795), (7,293795), (3,293795), (5,293795), (2,293795), (0,293795), (1,293795), (6,293795)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok156 : bitSearch source target 19 9 st156 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 293795 [(4,293795), (7,293795), (3,293795), (5,293795), (2,293795), (0,293795), (1,293795), (6,293795)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 8 0 [(4,293795), (7,293795), (3,293795), (5,293795), (2,293795), (0,293795), (1,293795), (6,293795)] = st150 := by decide +kernel
    rw [h]
    exact ok150
  · apply branch_false_of_child
    have h : propagate source target 19 8 1 [(4,293795), (7,293795), (3,293795), (5,293795), (2,293795), (0,293795), (1,293795), (6,293795)] = st151 := by decide +kernel
    rw [h]
    exact ok151
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 5 [(4,293795), (7,293795), (3,293795), (5,293795), (2,293795), (0,293795), (1,293795), (6,293795)] = st152 := by decide +kernel
    rw [h]
    exact ok152
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 7 [(4,293795), (7,293795), (3,293795), (5,293795), (2,293795), (0,293795), (1,293795), (6,293795)] = st153 := by decide +kernel
    rw [h]
    exact ok153
  · apply branch_false_of_child
    have h : propagate source target 19 8 8 [(4,293795), (7,293795), (3,293795), (5,293795), (2,293795), (0,293795), (1,293795), (6,293795)] = st154 := by decide +kernel
    rw [h]
    exact ok154
  · apply branch_false_of_child
    have h : propagate source target 19 8 9 [(4,293795), (7,293795), (3,293795), (5,293795), (2,293795), (0,293795), (1,293795), (6,293795)] = st155 := by decide +kernel
    rw [h]
    exact ok155
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 14 [(4,293795), (7,293795), (3,293795), (5,293795), (2,293795), (0,293795), (1,293795), (6,293795)] = st148 := by decide +kernel
    rw [h]
    exact ok148
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st157 : List (Nat × Nat) := [(4,408920), (7,396376), (3,396376), (5,396376), (2,396376), (0,396376), (1,396376), (6,396376)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok157 : bitSearch source target 19 8 st157 = false := by
  decide +kernel
def st158 : List (Nat × Nat) := [(4,408916), (7,396372), (3,396372), (5,396372), (2,396372), (0,396372), (1,396372), (6,396372)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok158 : bitSearch source target 19 8 st158 = false := by
  decide +kernel
def st159 : List (Nat × Nat) := [(4,408908), (7,144460), (3,144460), (5,144460), (2,144460), (0,144460), (1,144460), (6,144460)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok159 : bitSearch source target 19 8 st159 = false := by
  decide +kernel
def st160 : List (Nat × Nat) := [(4,408860), (7,144668), (3,144668), (5,144668), (2,144668), (0,144668), (1,144668), (6,144668)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok160 : bitSearch source target 19 8 st160 = false := by
  decide +kernel
def st161 : List (Nat × Nat) := [(4,408668), (7,408640), (3,408640), (5,408640), (2,408640), (0,408640), (1,408640), (6,408640)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok161 : bitSearch source target 19 8 st161 = false := by
  decide +kernel
def st162 : List (Nat × Nat) := [(4,407900), (7,395612), (3,395612), (5,395612), (2,395612), (0,395612), (1,395612), (6,395612)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok162 : bitSearch source target 19 8 st162 = false := by
  decide +kernel
def st163 : List (Nat × Nat) := [(4,277852), (7,277852), (3,277852), (5,277852), (2,277852), (0,277852), (1,277852), (6,277852)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok163 : bitSearch source target 19 8 st163 = false := by
  decide +kernel
def st164 : List (Nat × Nat) := [(8,408924), (4,408924), (7,408924), (3,408924), (5,408924), (2,408924), (0,408924), (1,408924), (6,408924)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok164 : bitSearch source target 19 9 st164 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 408924 [(4,408924), (7,408924), (3,408924), (5,408924), (2,408924), (0,408924), (1,408924), (6,408924)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 2 [(4,408924), (7,408924), (3,408924), (5,408924), (2,408924), (0,408924), (1,408924), (6,408924)] = st157 := by decide +kernel
    rw [h]
    exact ok157
  · apply branch_false_of_child
    have h : propagate source target 19 8 3 [(4,408924), (7,408924), (3,408924), (5,408924), (2,408924), (0,408924), (1,408924), (6,408924)] = st158 := by decide +kernel
    rw [h]
    exact ok158
  · apply branch_false_of_child
    have h : propagate source target 19 8 4 [(4,408924), (7,408924), (3,408924), (5,408924), (2,408924), (0,408924), (1,408924), (6,408924)] = st159 := by decide +kernel
    rw [h]
    exact ok159
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 6 [(4,408924), (7,408924), (3,408924), (5,408924), (2,408924), (0,408924), (1,408924), (6,408924)] = st160 := by decide +kernel
    rw [h]
    exact ok160
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 8 [(4,408924), (7,408924), (3,408924), (5,408924), (2,408924), (0,408924), (1,408924), (6,408924)] = st161 := by decide +kernel
    rw [h]
    exact ok161
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 10 [(4,408924), (7,408924), (3,408924), (5,408924), (2,408924), (0,408924), (1,408924), (6,408924)] = st162 := by decide +kernel
    rw [h]
    exact ok162
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 17 [(4,408924), (7,408924), (3,408924), (5,408924), (2,408924), (0,408924), (1,408924), (6,408924)] = st163 := by decide +kernel
    rw [h]
    exact ok163
  · decide +kernel
def st165 : List (Nat × Nat) := [(4,343384), (7,330840), (3,330840), (5,330840), (2,330840), (0,330840), (1,330840), (6,330840)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok165 : bitSearch source target 19 8 st165 = false := by
  decide +kernel
def st166 : List (Nat × Nat) := [(4,343380), (7,330836), (3,330836), (5,330836), (2,330836), (0,330836), (1,330836), (6,330836)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok166 : bitSearch source target 19 8 st166 = false := by
  decide +kernel
def st167 : List (Nat × Nat) := [(4,343372), (7,78924), (3,78924), (5,78924), (2,78924), (0,78924), (1,78924), (6,78924)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok167 : bitSearch source target 19 8 st167 = false := by
  decide +kernel
def st168 : List (Nat × Nat) := [(4,343324), (7,79132), (3,79132), (5,79132), (2,79132), (0,79132), (1,79132), (6,79132)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok168 : bitSearch source target 19 8 st168 = false := by
  decide +kernel
def st169 : List (Nat × Nat) := [(4,343132), (7,343104), (3,343104), (5,343104), (2,343104), (0,343104), (1,343104), (6,343104)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok169 : bitSearch source target 19 8 st169 = false := by
  decide +kernel
def st170 : List (Nat × Nat) := [(4,342364), (7,330076), (3,330076), (5,330076), (2,330076), (0,330076), (1,330076), (6,330076)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok170 : bitSearch source target 19 8 st170 = false := by
  decide +kernel
def st171 : List (Nat × Nat) := [(8,343388), (4,343388), (7,343388), (3,343388), (5,343388), (2,343388), (0,343388), (1,343388), (6,343388)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok171 : bitSearch source target 19 9 st171 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 343388 [(4,343388), (7,343388), (3,343388), (5,343388), (2,343388), (0,343388), (1,343388), (6,343388)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 2 [(4,343388), (7,343388), (3,343388), (5,343388), (2,343388), (0,343388), (1,343388), (6,343388)] = st165 := by decide +kernel
    rw [h]
    exact ok165
  · apply branch_false_of_child
    have h : propagate source target 19 8 3 [(4,343388), (7,343388), (3,343388), (5,343388), (2,343388), (0,343388), (1,343388), (6,343388)] = st166 := by decide +kernel
    rw [h]
    exact ok166
  · apply branch_false_of_child
    have h : propagate source target 19 8 4 [(4,343388), (7,343388), (3,343388), (5,343388), (2,343388), (0,343388), (1,343388), (6,343388)] = st167 := by decide +kernel
    rw [h]
    exact ok167
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 6 [(4,343388), (7,343388), (3,343388), (5,343388), (2,343388), (0,343388), (1,343388), (6,343388)] = st168 := by decide +kernel
    rw [h]
    exact ok168
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 8 [(4,343388), (7,343388), (3,343388), (5,343388), (2,343388), (0,343388), (1,343388), (6,343388)] = st169 := by decide +kernel
    rw [h]
    exact ok169
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 10 [(4,343388), (7,343388), (3,343388), (5,343388), (2,343388), (0,343388), (1,343388), (6,343388)] = st170 := by decide +kernel
    rw [h]
    exact ok170
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 16 [(4,343388), (7,343388), (3,343388), (5,343388), (2,343388), (0,343388), (1,343388), (6,343388)] = st163 := by decide +kernel
    rw [h]
    exact ok163
  · decide +kernel
  · decide +kernel
def st172 : List (Nat × Nat) := [(4,249256), (7,199848), (3,199848), (5,199848), (2,199848), (0,199848), (1,199848), (6,199848)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok172 : bitSearch source target 19 8 st172 = false := by
  decide +kernel
def st173 : List (Nat × Nat) := [(4,249252), (7,199844), (3,199844), (5,199844), (2,199844), (0,199844), (1,199844), (6,199844)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok173 : bitSearch source target 19 8 st173 = false := by
  decide +kernel
def st174 : List (Nat × Nat) := [(4,249228), (7,52364), (3,52364), (5,52364), (2,52364), (0,52364), (1,52364), (6,52364)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok174 : bitSearch source target 19 8 st174 = false := by
  decide +kernel
def st175 : List (Nat × Nat) := [(4,249132), (7,52524), (3,52524), (5,52524), (2,52524), (0,52524), (1,52524), (6,52524)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok175 : bitSearch source target 19 8 st175 = false := by
  decide +kernel
def st176 : List (Nat × Nat) := [(4,249004), (7,248960), (3,248960), (5,248960), (2,248960), (0,248960), (1,248960), (6,248960)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok176 : bitSearch source target 19 8 st176 = false := by
  decide +kernel
def st177 : List (Nat × Nat) := [(4,248236), (7,199084), (3,199084), (5,199084), (2,199084), (0,199084), (1,199084), (6,199084)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok177 : bitSearch source target 19 8 st177 = false := by
  decide +kernel
def st178 : List (Nat × Nat) := [(8,249260), (4,249260), (7,249260), (3,249260), (5,249260), (2,249260), (0,249260), (1,249260), (6,249260)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok178 : bitSearch source target 19 9 st178 = false := by
  refine bitSearch_false_of_branches source target 19 8 8 249260 [(4,249260), (7,249260), (3,249260), (5,249260), (2,249260), (0,249260), (1,249260), (6,249260)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 2 [(4,249260), (7,249260), (3,249260), (5,249260), (2,249260), (0,249260), (1,249260), (6,249260)] = st172 := by decide +kernel
    rw [h]
    exact ok172
  · apply branch_false_of_child
    have h : propagate source target 19 8 3 [(4,249260), (7,249260), (3,249260), (5,249260), (2,249260), (0,249260), (1,249260), (6,249260)] = st173 := by decide +kernel
    rw [h]
    exact ok173
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 5 [(4,249260), (7,249260), (3,249260), (5,249260), (2,249260), (0,249260), (1,249260), (6,249260)] = st174 := by decide +kernel
    rw [h]
    exact ok174
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 7 [(4,249260), (7,249260), (3,249260), (5,249260), (2,249260), (0,249260), (1,249260), (6,249260)] = st175 := by decide +kernel
    rw [h]
    exact ok175
  · apply branch_false_of_child
    have h : propagate source target 19 8 8 [(4,249260), (7,249260), (3,249260), (5,249260), (2,249260), (0,249260), (1,249260), (6,249260)] = st176 := by decide +kernel
    rw [h]
    exact ok176
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 8 10 [(4,249260), (7,249260), (3,249260), (5,249260), (2,249260), (0,249260), (1,249260), (6,249260)] = st177 := by decide +kernel
    rw [h]
    exact ok177
  · apply branch_false_of_child
    have h : propagate source target 19 8 11 [(4,249260), (7,249260), (3,249260), (5,249260), (2,249260), (0,249260), (1,249260), (6,249260)] = st125 := by decide +kernel
    rw [h]
    exact ok125
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st179 : List (Nat × Nat) := [(9,524287), (8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok179 : bitSearch source target 19 10 st179 = false := by
  refine bitSearch_false_of_branches source target 19 9 9 524287 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 9 0 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st21 := by decide +kernel
    rw [h]
    exact ok21
  · apply branch_false_of_child
    have h : propagate source target 19 9 1 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st31 := by decide +kernel
    rw [h]
    exact ok31
  · apply branch_false_of_child
    have h : propagate source target 19 9 2 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st53 := by decide +kernel
    rw [h]
    exact ok53
  · apply branch_false_of_child
    have h : propagate source target 19 9 3 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st63 := by decide +kernel
    rw [h]
    exact ok63
  · apply branch_false_of_child
    have h : propagate source target 19 9 4 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st73 := by decide +kernel
    rw [h]
    exact ok73
  · apply branch_false_of_child
    have h : propagate source target 19 9 5 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st83 := by decide +kernel
    rw [h]
    exact ok83
  · apply branch_false_of_child
    have h : propagate source target 19 9 6 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st93 := by decide +kernel
    rw [h]
    exact ok93
  · apply branch_false_of_child
    have h : propagate source target 19 9 7 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st103 := by decide +kernel
    rw [h]
    exact ok103
  · apply branch_false_of_child
    have h : propagate source target 19 9 8 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st104 := by decide +kernel
    rw [h]
    exact ok104
  · apply branch_false_of_child
    have h : propagate source target 19 9 9 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st111 := by decide +kernel
    rw [h]
    exact ok111
  · apply branch_false_of_child
    have h : propagate source target 19 9 10 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st118 := by decide +kernel
    rw [h]
    exact ok118
  · apply branch_false_of_child
    have h : propagate source target 19 9 11 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st126 := by decide +kernel
    rw [h]
    exact ok126
  · apply branch_false_of_child
    have h : propagate source target 19 9 12 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st134 := by decide +kernel
    rw [h]
    exact ok134
  · apply branch_false_of_child
    have h : propagate source target 19 9 13 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st141 := by decide +kernel
    rw [h]
    exact ok141
  · apply branch_false_of_child
    have h : propagate source target 19 9 14 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st149 := by decide +kernel
    rw [h]
    exact ok149
  · apply branch_false_of_child
    have h : propagate source target 19 9 15 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st156 := by decide +kernel
    rw [h]
    exact ok156
  · apply branch_false_of_child
    have h : propagate source target 19 9 16 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st164 := by decide +kernel
    rw [h]
    exact ok164
  · apply branch_false_of_child
    have h : propagate source target 19 9 17 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st171 := by decide +kernel
    rw [h]
    exact ok171
  · apply branch_false_of_child
    have h : propagate source target 19 9 18 [(8,524287), (4,524287), (7,524287), (3,524287), (5,524287), (2,524287), (0,524287), (1,524287), (6,524287)] = st178 := by decide +kernel
    rw [h]
    exact ok178
def sourceGraph : SimpleGraph (Fin 10) where
  Adj i j := (source i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
def targetGraph : SimpleGraph (Fin 19) where
  Adj i j := (target i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
def vertices : List Nat := [9, 8, 4, 7, 3, 5, 2, 0, 1, 6]
theorem no_embedding : ¬ ∃ f : Fin 10 ↪ Fin 19,
    ∀ u v, sourceGraph.Adj u v → targetGraph.Adj (f u) (f v) := by
  refine bitSearch_false_no_embedding sourceGraph targetGraph source target
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) vertices
    (by decide +kernel) (by decide +kernel) 10 ?_
  have h : (vertices.map fun v => (v,2^19-1)) = st179 := by decide +kernel
  rw [h]
  exact ok179
end Order10Search56

-- closed residual embedding search 72
namespace Order10Search72
open EmbeddingDFS
def sourceRows : List Nat := [962, 961, 1008, 1008, 972, 972, 831, 831, 767, 511]
def targetRows : List Nat := [493502, 505981, 64443, 292727, 159471, 89567, 490554, 249653, 382637, 451997, 476153, 258294, 387438, 449118, 16380, 473991, 433635, 372435, 243531]
def source (v : Nat) : Nat := sourceRows.getD v 0
def target (v : Nat) : Nat := targetRows.getD v 0
def st0 : List (Nat × Nat) := [(7,524286), (8,493502), (1,493502), (0,493502), (9,493502), (5,493502), (2,493502), (4,493502), (3,493502)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok0 : bitSearch source target 19 9 st0 = false := by
  decide +kernel
def st1 : List (Nat × Nat) := [(7,524285), (8,505981), (1,505981), (0,505981), (9,505981), (5,505981), (2,505981), (4,505981), (3,505981)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok1 : bitSearch source target 19 9 st1 = false := by
  decide +kernel
def st2 : List (Nat × Nat) := [(7,524283), (8,64443), (1,64443), (0,64443), (9,64443), (5,64443), (2,64443), (4,64443), (3,64443)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok2 : bitSearch source target 19 9 st2 = false := by
  decide +kernel
def st3 : List (Nat × Nat) := [(7,524279), (8,292727), (1,292727), (0,292727), (9,292727), (5,292727), (2,292727), (4,292727), (3,292727)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3 : bitSearch source target 19 9 st3 = false := by
  decide +kernel
def st4 : List (Nat × Nat) := [(7,524271), (8,159471), (1,159471), (0,159471), (9,159471), (5,159471), (2,159471), (4,159471), (3,159471)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4 : bitSearch source target 19 9 st4 = false := by
  decide +kernel
def st5 : List (Nat × Nat) := [(7,524255), (8,89567), (1,89567), (0,89567), (9,89567), (5,89567), (2,89567), (4,89567), (3,89567)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5 : bitSearch source target 19 9 st5 = false := by
  decide +kernel
def st6 : List (Nat × Nat) := [(7,524223), (8,490554), (1,490554), (0,490554), (9,490554), (5,490554), (2,490554), (4,490554), (3,490554)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6 : bitSearch source target 19 9 st6 = false := by
  decide +kernel
def st7 : List (Nat × Nat) := [(7,524159), (8,249653), (1,249653), (0,249653), (9,249653), (5,249653), (2,249653), (4,249653), (3,249653)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7 : bitSearch source target 19 9 st7 = false := by
  decide +kernel
def st8 : List (Nat × Nat) := [(7,524031), (8,382637), (1,382637), (0,382637), (9,382637), (5,382637), (2,382637), (4,382637), (3,382637)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8 : bitSearch source target 19 9 st8 = false := by
  decide +kernel
def st9 : List (Nat × Nat) := [(7,523775), (8,451997), (1,451997), (0,451997), (9,451997), (5,451997), (2,451997), (4,451997), (3,451997)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok9 : bitSearch source target 19 9 st9 = false := by
  decide +kernel
def st10 : List (Nat × Nat) := [(7,523263), (8,476153), (1,476153), (0,476153), (9,476153), (5,476153), (2,476153), (4,476153), (3,476153)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok10 : bitSearch source target 19 9 st10 = false := by
  decide +kernel
def st11 : List (Nat × Nat) := [(7,522239), (8,258294), (1,258294), (0,258294), (9,258294), (5,258294), (2,258294), (4,258294), (3,258294)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok11 : bitSearch source target 19 9 st11 = false := by
  decide +kernel
def st12 : List (Nat × Nat) := [(7,520191), (8,387438), (1,387438), (0,387438), (9,387438), (5,387438), (2,387438), (4,387438), (3,387438)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok12 : bitSearch source target 19 9 st12 = false := by
  decide +kernel
def st13 : List (Nat × Nat) := [(7,516095), (8,449118), (1,449118), (0,449118), (9,449118), (5,449118), (2,449118), (4,449118), (3,449118)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok13 : bitSearch source target 19 9 st13 = false := by
  decide +kernel
def st14 : List (Nat × Nat) := [(7,507903), (8,16380), (1,16380), (0,16380), (9,16380), (5,16380), (2,16380), (4,16380), (3,16380)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok14 : bitSearch source target 19 9 st14 = false := by
  decide +kernel
def st15 : List (Nat × Nat) := [(7,491519), (8,473991), (1,473991), (0,473991), (9,473991), (5,473991), (2,473991), (4,473991), (3,473991)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok15 : bitSearch source target 19 9 st15 = false := by
  decide +kernel
def st16 : List (Nat × Nat) := [(7,458751), (8,433635), (1,433635), (0,433635), (9,433635), (5,433635), (2,433635), (4,433635), (3,433635)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok16 : bitSearch source target 19 9 st16 = false := by
  decide +kernel
def st17 : List (Nat × Nat) := [(7,393215), (8,372435), (1,372435), (0,372435), (9,372435), (5,372435), (2,372435), (4,372435), (3,372435)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok17 : bitSearch source target 19 9 st17 = false := by
  decide +kernel
def st18 : List (Nat × Nat) := [(7,262143), (8,243531), (1,243531), (0,243531), (9,243531), (5,243531), (2,243531), (4,243531), (3,243531)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok18 : bitSearch source target 19 9 st18 = false := by
  decide +kernel
def st19 : List (Nat × Nat) := [(6,524287), (7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok19 : bitSearch source target 19 10 st19 = false := by
  refine bitSearch_false_of_branches source target 19 9 6 524287 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 6 0 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st0 := by decide +kernel
    rw [h]
    exact ok0
  · apply branch_false_of_child
    have h : propagate source target 19 6 1 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st1 := by decide +kernel
    rw [h]
    exact ok1
  · apply branch_false_of_child
    have h : propagate source target 19 6 2 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st2 := by decide +kernel
    rw [h]
    exact ok2
  · apply branch_false_of_child
    have h : propagate source target 19 6 3 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st3 := by decide +kernel
    rw [h]
    exact ok3
  · apply branch_false_of_child
    have h : propagate source target 19 6 4 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st4 := by decide +kernel
    rw [h]
    exact ok4
  · apply branch_false_of_child
    have h : propagate source target 19 6 5 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st5 := by decide +kernel
    rw [h]
    exact ok5
  · apply branch_false_of_child
    have h : propagate source target 19 6 6 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st6 := by decide +kernel
    rw [h]
    exact ok6
  · apply branch_false_of_child
    have h : propagate source target 19 6 7 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st7 := by decide +kernel
    rw [h]
    exact ok7
  · apply branch_false_of_child
    have h : propagate source target 19 6 8 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st8 := by decide +kernel
    rw [h]
    exact ok8
  · apply branch_false_of_child
    have h : propagate source target 19 6 9 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st9 := by decide +kernel
    rw [h]
    exact ok9
  · apply branch_false_of_child
    have h : propagate source target 19 6 10 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st10 := by decide +kernel
    rw [h]
    exact ok10
  · apply branch_false_of_child
    have h : propagate source target 19 6 11 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st11 := by decide +kernel
    rw [h]
    exact ok11
  · apply branch_false_of_child
    have h : propagate source target 19 6 12 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st12 := by decide +kernel
    rw [h]
    exact ok12
  · apply branch_false_of_child
    have h : propagate source target 19 6 13 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st13 := by decide +kernel
    rw [h]
    exact ok13
  · apply branch_false_of_child
    have h : propagate source target 19 6 14 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st14 := by decide +kernel
    rw [h]
    exact ok14
  · apply branch_false_of_child
    have h : propagate source target 19 6 15 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st15 := by decide +kernel
    rw [h]
    exact ok15
  · apply branch_false_of_child
    have h : propagate source target 19 6 16 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st16 := by decide +kernel
    rw [h]
    exact ok16
  · apply branch_false_of_child
    have h : propagate source target 19 6 17 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st17 := by decide +kernel
    rw [h]
    exact ok17
  · apply branch_false_of_child
    have h : propagate source target 19 6 18 [(7,524287), (8,524287), (1,524287), (0,524287), (9,524287), (5,524287), (2,524287), (4,524287), (3,524287)] = st18 := by decide +kernel
    rw [h]
    exact ok18
def sourceGraph : SimpleGraph (Fin 10) where
  Adj i j := (source i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
def targetGraph : SimpleGraph (Fin 19) where
  Adj i j := (target i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
def vertices : List Nat := [6, 7, 8, 1, 0, 9, 5, 2, 4, 3]
theorem no_embedding : ¬ ∃ f : Fin 10 ↪ Fin 19,
    ∀ u v, sourceGraph.Adj u v → targetGraph.Adj (f u) (f v) := by
  refine bitSearch_false_no_embedding sourceGraph targetGraph source target
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) vertices
    (by decide +kernel) (by decide +kernel) 10 ?_
  have h : (vertices.map fun v => (v,2^19-1)) = st19 := by decide +kernel
  rw [h]
  exact ok19
end Order10Search72

-- closed residual embedding search 94
namespace Order10Search94
open EmbeddingDFS
def sourceRows : List Nat := [962, 961, 1008, 1008, 940, 988, 943, 639, 639, 511]
def targetRows : List Nat := [493502, 505981, 64443, 292727, 159471, 89567, 490554, 249653, 382637, 451997, 476153, 258294, 387438, 449118, 16380, 473991, 433635, 372435, 243531]
def source (v : Nat) : Nat := sourceRows.getD v 0
def target (v : Nat) : Nat := targetRows.getD v 0
def st0 : List (Nat × Nat) := [(8,524286), (9,493502), (6,493502), (0,493502), (5,493502), (4,493502), (1,493502), (3,493502), (2,493502)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok0 : bitSearch source target 19 9 st0 = false := by
  decide +kernel
def st1 : List (Nat × Nat) := [(8,524285), (9,505981), (6,505981), (0,505981), (5,505981), (4,505981), (1,505981), (3,505981), (2,505981)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok1 : bitSearch source target 19 9 st1 = false := by
  decide +kernel
def st2 : List (Nat × Nat) := [(8,524283), (9,64443), (6,64443), (0,64443), (5,64443), (4,64443), (1,64443), (3,64443), (2,64443)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok2 : bitSearch source target 19 9 st2 = false := by
  decide +kernel
def st3 : List (Nat × Nat) := [(8,524279), (9,292727), (6,292727), (0,292727), (5,292727), (4,292727), (1,292727), (3,292727), (2,292727)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3 : bitSearch source target 19 9 st3 = false := by
  decide +kernel
def st4 : List (Nat × Nat) := [(8,524271), (9,159471), (6,159471), (0,159471), (5,159471), (4,159471), (1,159471), (3,159471), (2,159471)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4 : bitSearch source target 19 9 st4 = false := by
  decide +kernel
def st5 : List (Nat × Nat) := [(8,524255), (9,89567), (6,89567), (0,89567), (5,89567), (4,89567), (1,89567), (3,89567), (2,89567)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5 : bitSearch source target 19 9 st5 = false := by
  decide +kernel
def st6 : List (Nat × Nat) := [(8,524223), (9,490554), (6,490554), (0,490554), (5,490554), (4,490554), (1,490554), (3,490554), (2,490554)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6 : bitSearch source target 19 9 st6 = false := by
  decide +kernel
def st7 : List (Nat × Nat) := [(8,524159), (9,249653), (6,249653), (0,249653), (5,249653), (4,249653), (1,249653), (3,249653), (2,249653)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7 : bitSearch source target 19 9 st7 = false := by
  decide +kernel
def st8 : List (Nat × Nat) := [(8,524031), (9,382637), (6,382637), (0,382637), (5,382637), (4,382637), (1,382637), (3,382637), (2,382637)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8 : bitSearch source target 19 9 st8 = false := by
  decide +kernel
def st9 : List (Nat × Nat) := [(8,523775), (9,451997), (6,451997), (0,451997), (5,451997), (4,451997), (1,451997), (3,451997), (2,451997)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok9 : bitSearch source target 19 9 st9 = false := by
  decide +kernel
def st10 : List (Nat × Nat) := [(8,523263), (9,476153), (6,476153), (0,476153), (5,476153), (4,476153), (1,476153), (3,476153), (2,476153)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok10 : bitSearch source target 19 9 st10 = false := by
  decide +kernel
def st11 : List (Nat × Nat) := [(8,522239), (9,258294), (6,258294), (0,258294), (5,258294), (4,258294), (1,258294), (3,258294), (2,258294)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok11 : bitSearch source target 19 9 st11 = false := by
  decide +kernel
def st12 : List (Nat × Nat) := [(8,520191), (9,387438), (6,387438), (0,387438), (5,387438), (4,387438), (1,387438), (3,387438), (2,387438)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok12 : bitSearch source target 19 9 st12 = false := by
  decide +kernel
def st13 : List (Nat × Nat) := [(8,516095), (9,449118), (6,449118), (0,449118), (5,449118), (4,449118), (1,449118), (3,449118), (2,449118)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok13 : bitSearch source target 19 9 st13 = false := by
  decide +kernel
def st14 : List (Nat × Nat) := [(8,507903), (9,16380), (6,16380), (0,16380), (5,16380), (4,16380), (1,16380), (3,16380), (2,16380)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok14 : bitSearch source target 19 9 st14 = false := by
  decide +kernel
def st15 : List (Nat × Nat) := [(8,491519), (9,473991), (6,473991), (0,473991), (5,473991), (4,473991), (1,473991), (3,473991), (2,473991)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok15 : bitSearch source target 19 9 st15 = false := by
  decide +kernel
def st16 : List (Nat × Nat) := [(8,458751), (9,433635), (6,433635), (0,433635), (5,433635), (4,433635), (1,433635), (3,433635), (2,433635)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok16 : bitSearch source target 19 9 st16 = false := by
  decide +kernel
def st17 : List (Nat × Nat) := [(8,393215), (9,372435), (6,372435), (0,372435), (5,372435), (4,372435), (1,372435), (3,372435), (2,372435)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok17 : bitSearch source target 19 9 st17 = false := by
  decide +kernel
def st18 : List (Nat × Nat) := [(8,262143), (9,243531), (6,243531), (0,243531), (5,243531), (4,243531), (1,243531), (3,243531), (2,243531)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok18 : bitSearch source target 19 9 st18 = false := by
  decide +kernel
def st19 : List (Nat × Nat) := [(7,524287), (8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok19 : bitSearch source target 19 10 st19 = false := by
  refine bitSearch_false_of_branches source target 19 9 7 524287 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 7 0 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st0 := by decide +kernel
    rw [h]
    exact ok0
  · apply branch_false_of_child
    have h : propagate source target 19 7 1 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st1 := by decide +kernel
    rw [h]
    exact ok1
  · apply branch_false_of_child
    have h : propagate source target 19 7 2 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st2 := by decide +kernel
    rw [h]
    exact ok2
  · apply branch_false_of_child
    have h : propagate source target 19 7 3 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st3 := by decide +kernel
    rw [h]
    exact ok3
  · apply branch_false_of_child
    have h : propagate source target 19 7 4 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st4 := by decide +kernel
    rw [h]
    exact ok4
  · apply branch_false_of_child
    have h : propagate source target 19 7 5 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st5 := by decide +kernel
    rw [h]
    exact ok5
  · apply branch_false_of_child
    have h : propagate source target 19 7 6 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st6 := by decide +kernel
    rw [h]
    exact ok6
  · apply branch_false_of_child
    have h : propagate source target 19 7 7 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st7 := by decide +kernel
    rw [h]
    exact ok7
  · apply branch_false_of_child
    have h : propagate source target 19 7 8 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st8 := by decide +kernel
    rw [h]
    exact ok8
  · apply branch_false_of_child
    have h : propagate source target 19 7 9 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st9 := by decide +kernel
    rw [h]
    exact ok9
  · apply branch_false_of_child
    have h : propagate source target 19 7 10 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st10 := by decide +kernel
    rw [h]
    exact ok10
  · apply branch_false_of_child
    have h : propagate source target 19 7 11 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st11 := by decide +kernel
    rw [h]
    exact ok11
  · apply branch_false_of_child
    have h : propagate source target 19 7 12 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st12 := by decide +kernel
    rw [h]
    exact ok12
  · apply branch_false_of_child
    have h : propagate source target 19 7 13 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st13 := by decide +kernel
    rw [h]
    exact ok13
  · apply branch_false_of_child
    have h : propagate source target 19 7 14 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st14 := by decide +kernel
    rw [h]
    exact ok14
  · apply branch_false_of_child
    have h : propagate source target 19 7 15 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st15 := by decide +kernel
    rw [h]
    exact ok15
  · apply branch_false_of_child
    have h : propagate source target 19 7 16 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st16 := by decide +kernel
    rw [h]
    exact ok16
  · apply branch_false_of_child
    have h : propagate source target 19 7 17 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st17 := by decide +kernel
    rw [h]
    exact ok17
  · apply branch_false_of_child
    have h : propagate source target 19 7 18 [(8,524287), (9,524287), (6,524287), (0,524287), (5,524287), (4,524287), (1,524287), (3,524287), (2,524287)] = st18 := by decide +kernel
    rw [h]
    exact ok18
def sourceGraph : SimpleGraph (Fin 10) where
  Adj i j := (source i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
def targetGraph : SimpleGraph (Fin 19) where
  Adj i j := (target i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
def vertices : List Nat := [7, 8, 9, 6, 0, 5, 4, 1, 3, 2]
theorem no_embedding : ¬ ∃ f : Fin 10 ↪ Fin 19,
    ∀ u v, sourceGraph.Adj u v → targetGraph.Adj (f u) (f v) := by
  refine bitSearch_false_no_embedding sourceGraph targetGraph source target
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) vertices
    (by decide +kernel) (by decide +kernel) 10 ?_
  have h : (vertices.map fun v => (v,2^19-1)) = st19 := by decide +kernel
  rw [h]
  exact ok19
end Order10Search94

-- closed residual embedding search 103
namespace Order10Search103
open EmbeddingDFS
def sourceRows : List Nat := [962, 961, 952, 884, 1004, 988, 955, 887, 255, 255]
def targetRows : List Nat := [62206, 62205, 462075, 462071, 210543, 315039, 210719, 315183, 523968, 61939, 461308, 509356, 254803, 250707, 310179, 293795, 408924, 343388, 249260]
def source (v : Nat) : Nat := sourceRows.getD v 0
def target (v : Nat) : Nat := targetRows.getD v 0
def st0 : List (Nat × Nat) := [(6,62204), (2,62204), (5,62204), (4,62204), (3,62204), (0,62204), (1,62204), (7,62204)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok0 : bitSearch source target 19 8 st0 = false := by
  decide +kernel
def st1 : List (Nat × Nat) := [(6,12910), (2,12910), (5,12910), (4,12910), (3,12910), (0,12910), (1,12910), (7,12910)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok1 : bitSearch source target 19 8 st1 = false := by
  decide +kernel
def st2 : List (Nat × Nat) := [(6,49822), (2,49822), (5,49822), (4,49822), (3,49822), (0,49822), (1,49822), (7,49822)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok2 : bitSearch source target 19 8 st2 = false := by
  decide +kernel
def st3 : List (Nat × Nat) := [(6,61682), (2,61682), (5,61682), (4,61682), (3,61682), (0,61682), (1,61682), (7,61682)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3 : bitSearch source target 19 8 st3 = false := by
  decide +kernel
def st4 : List (Nat × Nat) := [(9,524286), (6,62206), (2,62206), (5,62206), (4,62206), (3,62206), (0,62206), (1,62206), (7,62206)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4 : bitSearch source target 19 9 st4 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 524286 [(6,62206), (2,62206), (5,62206), (4,62206), (3,62206), (0,62206), (1,62206), (7,62206)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 1 [(6,62206), (2,62206), (5,62206), (4,62206), (3,62206), (0,62206), (1,62206), (7,62206)] = st0 := by decide +kernel
    rw [h]
    exact ok0
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 4 [(6,62206), (2,62206), (5,62206), (4,62206), (3,62206), (0,62206), (1,62206), (7,62206)] = st1 := by decide +kernel
    rw [h]
    exact ok1
  · apply branch_false_of_child
    have h : propagate source target 19 9 5 [(6,62206), (2,62206), (5,62206), (4,62206), (3,62206), (0,62206), (1,62206), (7,62206)] = st2 := by decide +kernel
    rw [h]
    exact ok2
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 9 [(6,62206), (2,62206), (5,62206), (4,62206), (3,62206), (0,62206), (1,62206), (7,62206)] = st3 := by decide +kernel
    rw [h]
    exact ok3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st5 : List (Nat × Nat) := [(6,12909), (2,12909), (5,12909), (4,12909), (3,12909), (0,12909), (1,12909), (7,12909)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5 : bitSearch source target 19 8 st5 = false := by
  decide +kernel
def st6 : List (Nat × Nat) := [(6,49821), (2,49821), (5,49821), (4,49821), (3,49821), (0,49821), (1,49821), (7,49821)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6 : bitSearch source target 19 8 st6 = false := by
  decide +kernel
def st7 : List (Nat × Nat) := [(6,61681), (2,61681), (5,61681), (4,61681), (3,61681), (0,61681), (1,61681), (7,61681)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7 : bitSearch source target 19 8 st7 = false := by
  decide +kernel
def st8 : List (Nat × Nat) := [(9,524285), (6,62205), (2,62205), (5,62205), (4,62205), (3,62205), (0,62205), (1,62205), (7,62205)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8 : bitSearch source target 19 9 st8 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 524285 [(6,62205), (2,62205), (5,62205), (4,62205), (3,62205), (0,62205), (1,62205), (7,62205)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 9 0 [(6,62205), (2,62205), (5,62205), (4,62205), (3,62205), (0,62205), (1,62205), (7,62205)] = st0 := by decide +kernel
    rw [h]
    exact ok0
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 4 [(6,62205), (2,62205), (5,62205), (4,62205), (3,62205), (0,62205), (1,62205), (7,62205)] = st5 := by decide +kernel
    rw [h]
    exact ok5
  · apply branch_false_of_child
    have h : propagate source target 19 9 5 [(6,62205), (2,62205), (5,62205), (4,62205), (3,62205), (0,62205), (1,62205), (7,62205)] = st6 := by decide +kernel
    rw [h]
    exact ok6
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 9 [(6,62205), (2,62205), (5,62205), (4,62205), (3,62205), (0,62205), (1,62205), (7,62205)] = st7 := by decide +kernel
    rw [h]
    exact ok7
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st9 : List (Nat × Nat) := [(6,462067), (2,462067), (5,462067), (4,462067), (3,462067), (0,462067), (1,462067), (7,462067)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok9 : bitSearch source target 19 8 st9 = false := by
  decide +kernel
def st10 : List (Nat × Nat) := [(6,197739), (2,197739), (5,197739), (4,197739), (3,197739), (0,197739), (1,197739), (7,197739)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok10 : bitSearch source target 19 8 st10 = false := by
  decide +kernel
def st11 : List (Nat × Nat) := [(6,265371), (2,265371), (5,265371), (4,265371), (3,265371), (0,265371), (1,265371), (7,265371)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok11 : bitSearch source target 19 8 st11 = false := by
  decide +kernel
def st12 : List (Nat × Nat) := [(6,461048), (2,461048), (5,461048), (4,461048), (3,461048), (0,461048), (1,461048), (7,461048)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok12 : bitSearch source target 19 8 st12 = false := by
  decide +kernel
def st13 : List (Nat × Nat) := [(9,524283), (6,462075), (2,462075), (5,462075), (4,462075), (3,462075), (0,462075), (1,462075), (7,462075)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok13 : bitSearch source target 19 9 st13 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 524283 [(6,462075), (2,462075), (5,462075), (4,462075), (3,462075), (0,462075), (1,462075), (7,462075)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 3 [(6,462075), (2,462075), (5,462075), (4,462075), (3,462075), (0,462075), (1,462075), (7,462075)] = st9 := by decide +kernel
    rw [h]
    exact ok9
  · apply branch_false_of_child
    have h : propagate source target 19 9 4 [(6,462075), (2,462075), (5,462075), (4,462075), (3,462075), (0,462075), (1,462075), (7,462075)] = st10 := by decide +kernel
    rw [h]
    exact ok10
  · apply branch_false_of_child
    have h : propagate source target 19 9 5 [(6,462075), (2,462075), (5,462075), (4,462075), (3,462075), (0,462075), (1,462075), (7,462075)] = st11 := by decide +kernel
    rw [h]
    exact ok11
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 10 [(6,462075), (2,462075), (5,462075), (4,462075), (3,462075), (0,462075), (1,462075), (7,462075)] = st12 := by decide +kernel
    rw [h]
    exact ok12
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st14 : List (Nat × Nat) := [(6,197735), (2,197735), (5,197735), (4,197735), (3,197735), (0,197735), (1,197735), (7,197735)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok14 : bitSearch source target 19 8 st14 = false := by
  decide +kernel
def st15 : List (Nat × Nat) := [(6,265367), (2,265367), (5,265367), (4,265367), (3,265367), (0,265367), (1,265367), (7,265367)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok15 : bitSearch source target 19 8 st15 = false := by
  decide +kernel
def st16 : List (Nat × Nat) := [(6,461044), (2,461044), (5,461044), (4,461044), (3,461044), (0,461044), (1,461044), (7,461044)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok16 : bitSearch source target 19 8 st16 = false := by
  decide +kernel
def st17 : List (Nat × Nat) := [(9,524279), (6,462071), (2,462071), (5,462071), (4,462071), (3,462071), (0,462071), (1,462071), (7,462071)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok17 : bitSearch source target 19 9 st17 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 524279 [(6,462071), (2,462071), (5,462071), (4,462071), (3,462071), (0,462071), (1,462071), (7,462071)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 2 [(6,462071), (2,462071), (5,462071), (4,462071), (3,462071), (0,462071), (1,462071), (7,462071)] = st9 := by decide +kernel
    rw [h]
    exact ok9
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 4 [(6,462071), (2,462071), (5,462071), (4,462071), (3,462071), (0,462071), (1,462071), (7,462071)] = st14 := by decide +kernel
    rw [h]
    exact ok14
  · apply branch_false_of_child
    have h : propagate source target 19 9 5 [(6,462071), (2,462071), (5,462071), (4,462071), (3,462071), (0,462071), (1,462071), (7,462071)] = st15 := by decide +kernel
    rw [h]
    exact ok15
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 10 [(6,462071), (2,462071), (5,462071), (4,462071), (3,462071), (0,462071), (1,462071), (7,462071)] = st16 := by decide +kernel
    rw [h]
    exact ok16
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st18 : List (Nat × Nat) := [(6,210447), (2,210447), (5,210447), (4,210447), (3,210447), (0,210447), (1,210447), (7,210447)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok18 : bitSearch source target 19 8 st18 = false := by
  decide +kernel
def st19 : List (Nat × Nat) := [(9,524271), (6,210543), (2,210543), (5,210543), (4,210543), (3,210543), (0,210543), (1,210543), (7,210543)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok19 : bitSearch source target 19 9 st19 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 524271 [(6,210543), (2,210543), (5,210543), (4,210543), (3,210543), (0,210543), (1,210543), (7,210543)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 9 0 [(6,210543), (2,210543), (5,210543), (4,210543), (3,210543), (0,210543), (1,210543), (7,210543)] = st1 := by decide +kernel
    rw [h]
    exact ok1
  · apply branch_false_of_child
    have h : propagate source target 19 9 1 [(6,210543), (2,210543), (5,210543), (4,210543), (3,210543), (0,210543), (1,210543), (7,210543)] = st5 := by decide +kernel
    rw [h]
    exact ok5
  · apply branch_false_of_child
    have h : propagate source target 19 9 2 [(6,210543), (2,210543), (5,210543), (4,210543), (3,210543), (0,210543), (1,210543), (7,210543)] = st10 := by decide +kernel
    rw [h]
    exact ok10
  · apply branch_false_of_child
    have h : propagate source target 19 9 3 [(6,210543), (2,210543), (5,210543), (4,210543), (3,210543), (0,210543), (1,210543), (7,210543)] = st14 := by decide +kernel
    rw [h]
    exact ok14
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 6 [(6,210543), (2,210543), (5,210543), (4,210543), (3,210543), (0,210543), (1,210543), (7,210543)] = st18 := by decide +kernel
    rw [h]
    exact ok18
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st20 : List (Nat × Nat) := [(6,314895), (2,314895), (5,314895), (4,314895), (3,314895), (0,314895), (1,314895), (7,314895)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok20 : bitSearch source target 19 8 st20 = false := by
  decide +kernel
def st21 : List (Nat × Nat) := [(9,524255), (6,315039), (2,315039), (5,315039), (4,315039), (3,315039), (0,315039), (1,315039), (7,315039)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok21 : bitSearch source target 19 9 st21 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 524255 [(6,315039), (2,315039), (5,315039), (4,315039), (3,315039), (0,315039), (1,315039), (7,315039)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 9 0 [(6,315039), (2,315039), (5,315039), (4,315039), (3,315039), (0,315039), (1,315039), (7,315039)] = st2 := by decide +kernel
    rw [h]
    exact ok2
  · apply branch_false_of_child
    have h : propagate source target 19 9 1 [(6,315039), (2,315039), (5,315039), (4,315039), (3,315039), (0,315039), (1,315039), (7,315039)] = st6 := by decide +kernel
    rw [h]
    exact ok6
  · apply branch_false_of_child
    have h : propagate source target 19 9 2 [(6,315039), (2,315039), (5,315039), (4,315039), (3,315039), (0,315039), (1,315039), (7,315039)] = st11 := by decide +kernel
    rw [h]
    exact ok11
  · apply branch_false_of_child
    have h : propagate source target 19 9 3 [(6,315039), (2,315039), (5,315039), (4,315039), (3,315039), (0,315039), (1,315039), (7,315039)] = st15 := by decide +kernel
    rw [h]
    exact ok15
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 7 [(6,315039), (2,315039), (5,315039), (4,315039), (3,315039), (0,315039), (1,315039), (7,315039)] = st20 := by decide +kernel
    rw [h]
    exact ok20
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st22 : List (Nat × Nat) := [(6,205587), (2,205587), (5,205587), (4,205587), (3,205587), (0,205587), (1,205587), (7,205587)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok22 : bitSearch source target 19 8 st22 = false := by
  decide +kernel
def st23 : List (Nat × Nat) := [(6,201491), (2,201491), (5,201491), (4,201491), (3,201491), (0,201491), (1,201491), (7,201491)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok23 : bitSearch source target 19 8 st23 = false := by
  decide +kernel
def st24 : List (Nat × Nat) := [(6,144668), (2,144668), (5,144668), (4,144668), (3,144668), (0,144668), (1,144668), (7,144668)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok24 : bitSearch source target 19 8 st24 = false := by
  decide +kernel
def st25 : List (Nat × Nat) := [(6,79132), (2,79132), (5,79132), (4,79132), (3,79132), (0,79132), (1,79132), (7,79132)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok25 : bitSearch source target 19 8 st25 = false := by
  decide +kernel
def st26 : List (Nat × Nat) := [(9,524223), (6,210719), (2,210719), (5,210719), (4,210719), (3,210719), (0,210719), (1,210719), (7,210719)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok26 : bitSearch source target 19 9 st26 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 524223 [(6,210719), (2,210719), (5,210719), (4,210719), (3,210719), (0,210719), (1,210719), (7,210719)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 4 [(6,210719), (2,210719), (5,210719), (4,210719), (3,210719), (0,210719), (1,210719), (7,210719)] = st18 := by decide +kernel
    rw [h]
    exact ok18
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 12 [(6,210719), (2,210719), (5,210719), (4,210719), (3,210719), (0,210719), (1,210719), (7,210719)] = st22 := by decide +kernel
    rw [h]
    exact ok22
  · apply branch_false_of_child
    have h : propagate source target 19 9 13 [(6,210719), (2,210719), (5,210719), (4,210719), (3,210719), (0,210719), (1,210719), (7,210719)] = st23 := by decide +kernel
    rw [h]
    exact ok23
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 16 [(6,210719), (2,210719), (5,210719), (4,210719), (3,210719), (0,210719), (1,210719), (7,210719)] = st24 := by decide +kernel
    rw [h]
    exact ok24
  · apply branch_false_of_child
    have h : propagate source target 19 9 17 [(6,210719), (2,210719), (5,210719), (4,210719), (3,210719), (0,210719), (1,210719), (7,210719)] = st25 := by decide +kernel
    rw [h]
    exact ok25
  · decide +kernel
def st27 : List (Nat × Nat) := [(6,312620), (2,312620), (5,312620), (4,312620), (3,312620), (0,312620), (1,312620), (7,312620)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok27 : bitSearch source target 19 8 st27 = false := by
  decide +kernel
def st28 : List (Nat × Nat) := [(6,297763), (2,297763), (5,297763), (4,297763), (3,297763), (0,297763), (1,297763), (7,297763)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok28 : bitSearch source target 19 8 st28 = false := by
  decide +kernel
def st29 : List (Nat × Nat) := [(6,281379), (2,281379), (5,281379), (4,281379), (3,281379), (0,281379), (1,281379), (7,281379)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok29 : bitSearch source target 19 8 st29 = false := by
  decide +kernel
def st30 : List (Nat × Nat) := [(6,52524), (2,52524), (5,52524), (4,52524), (3,52524), (0,52524), (1,52524), (7,52524)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok30 : bitSearch source target 19 8 st30 = false := by
  decide +kernel
def st31 : List (Nat × Nat) := [(9,524159), (6,315183), (2,315183), (5,315183), (4,315183), (3,315183), (0,315183), (1,315183), (7,315183)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok31 : bitSearch source target 19 9 st31 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 524159 [(6,315183), (2,315183), (5,315183), (4,315183), (3,315183), (0,315183), (1,315183), (7,315183)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 5 [(6,315183), (2,315183), (5,315183), (4,315183), (3,315183), (0,315183), (1,315183), (7,315183)] = st20 := by decide +kernel
    rw [h]
    exact ok20
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 11 [(6,315183), (2,315183), (5,315183), (4,315183), (3,315183), (0,315183), (1,315183), (7,315183)] = st27 := by decide +kernel
    rw [h]
    exact ok27
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 14 [(6,315183), (2,315183), (5,315183), (4,315183), (3,315183), (0,315183), (1,315183), (7,315183)] = st28 := by decide +kernel
    rw [h]
    exact ok28
  · apply branch_false_of_child
    have h : propagate source target 19 9 15 [(6,315183), (2,315183), (5,315183), (4,315183), (3,315183), (0,315183), (1,315183), (7,315183)] = st29 := by decide +kernel
    rw [h]
    exact ok29
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 18 [(6,315183), (2,315183), (5,315183), (4,315183), (3,315183), (0,315183), (1,315183), (7,315183)] = st30 := by decide +kernel
    rw [h]
    exact ok30
def st32 : List (Nat × Nat) := [(9,524031), (6,523968), (2,523968), (5,523968), (4,523968), (3,523968), (0,523968), (1,523968), (7,523968)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok32 : bitSearch source target 19 9 st32 = false := by
  decide +kernel
def st33 : List (Nat × Nat) := [(6,57683), (2,57683), (5,57683), (4,57683), (3,57683), (0,57683), (1,57683), (7,57683)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok33 : bitSearch source target 19 8 st33 = false := by
  decide +kernel
def st34 : List (Nat × Nat) := [(6,53587), (2,53587), (5,53587), (4,53587), (3,53587), (0,53587), (1,53587), (7,53587)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok34 : bitSearch source target 19 8 st34 = false := by
  decide +kernel
def st35 : List (Nat × Nat) := [(6,45475), (2,45475), (5,45475), (4,45475), (3,45475), (0,45475), (1,45475), (7,45475)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok35 : bitSearch source target 19 8 st35 = false := by
  decide +kernel
def st36 : List (Nat × Nat) := [(6,29091), (2,29091), (5,29091), (4,29091), (3,29091), (0,29091), (1,29091), (7,29091)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok36 : bitSearch source target 19 8 st36 = false := by
  decide +kernel
def st37 : List (Nat × Nat) := [(9,523775), (6,61939), (2,61939), (5,61939), (4,61939), (3,61939), (0,61939), (1,61939), (7,61939)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok37 : bitSearch source target 19 9 st37 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 523775 [(6,61939), (2,61939), (5,61939), (4,61939), (3,61939), (0,61939), (1,61939), (7,61939)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 9 0 [(6,61939), (2,61939), (5,61939), (4,61939), (3,61939), (0,61939), (1,61939), (7,61939)] = st3 := by decide +kernel
    rw [h]
    exact ok3
  · apply branch_false_of_child
    have h : propagate source target 19 9 1 [(6,61939), (2,61939), (5,61939), (4,61939), (3,61939), (0,61939), (1,61939), (7,61939)] = st7 := by decide +kernel
    rw [h]
    exact ok7
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 12 [(6,61939), (2,61939), (5,61939), (4,61939), (3,61939), (0,61939), (1,61939), (7,61939)] = st33 := by decide +kernel
    rw [h]
    exact ok33
  · apply branch_false_of_child
    have h : propagate source target 19 9 13 [(6,61939), (2,61939), (5,61939), (4,61939), (3,61939), (0,61939), (1,61939), (7,61939)] = st34 := by decide +kernel
    rw [h]
    exact ok34
  · apply branch_false_of_child
    have h : propagate source target 19 9 14 [(6,61939), (2,61939), (5,61939), (4,61939), (3,61939), (0,61939), (1,61939), (7,61939)] = st35 := by decide +kernel
    rw [h]
    exact ok35
  · apply branch_false_of_child
    have h : propagate source target 19 9 15 [(6,61939), (2,61939), (5,61939), (4,61939), (3,61939), (0,61939), (1,61939), (7,61939)] = st36 := by decide +kernel
    rw [h]
    exact ok36
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st38 : List (Nat × Nat) := [(6,459180), (2,459180), (5,459180), (4,459180), (3,459180), (0,459180), (1,459180), (7,459180)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok38 : bitSearch source target 19 8 st38 = false := by
  decide +kernel
def st39 : List (Nat × Nat) := [(6,395612), (2,395612), (5,395612), (4,395612), (3,395612), (0,395612), (1,395612), (7,395612)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok39 : bitSearch source target 19 8 st39 = false := by
  decide +kernel
def st40 : List (Nat × Nat) := [(6,330076), (2,330076), (5,330076), (4,330076), (3,330076), (0,330076), (1,330076), (7,330076)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok40 : bitSearch source target 19 8 st40 = false := by
  decide +kernel
def st41 : List (Nat × Nat) := [(6,199084), (2,199084), (5,199084), (4,199084), (3,199084), (0,199084), (1,199084), (7,199084)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok41 : bitSearch source target 19 8 st41 = false := by
  decide +kernel
def st42 : List (Nat × Nat) := [(9,523263), (6,461308), (2,461308), (5,461308), (4,461308), (3,461308), (0,461308), (1,461308), (7,461308)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok42 : bitSearch source target 19 9 st42 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 523263 [(6,461308), (2,461308), (5,461308), (4,461308), (3,461308), (0,461308), (1,461308), (7,461308)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 2 [(6,461308), (2,461308), (5,461308), (4,461308), (3,461308), (0,461308), (1,461308), (7,461308)] = st12 := by decide +kernel
    rw [h]
    exact ok12
  · apply branch_false_of_child
    have h : propagate source target 19 9 3 [(6,461308), (2,461308), (5,461308), (4,461308), (3,461308), (0,461308), (1,461308), (7,461308)] = st16 := by decide +kernel
    rw [h]
    exact ok16
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 11 [(6,461308), (2,461308), (5,461308), (4,461308), (3,461308), (0,461308), (1,461308), (7,461308)] = st38 := by decide +kernel
    rw [h]
    exact ok38
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 16 [(6,461308), (2,461308), (5,461308), (4,461308), (3,461308), (0,461308), (1,461308), (7,461308)] = st39 := by decide +kernel
    rw [h]
    exact ok39
  · apply branch_false_of_child
    have h : propagate source target 19 9 17 [(6,461308), (2,461308), (5,461308), (4,461308), (3,461308), (0,461308), (1,461308), (7,461308)] = st40 := by decide +kernel
    rw [h]
    exact ok40
  · apply branch_false_of_child
    have h : propagate source target 19 9 18 [(6,461308), (2,461308), (5,461308), (4,461308), (3,461308), (0,461308), (1,461308), (7,461308)] = st41 := by decide +kernel
    rw [h]
    exact ok41
def st43 : List (Nat × Nat) := [(6,247212), (2,247212), (5,247212), (4,247212), (3,247212), (0,247212), (1,247212), (7,247212)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok43 : bitSearch source target 19 8 st43 = false := by
  decide +kernel
def st44 : List (Nat × Nat) := [(9,522239), (6,509356), (2,509356), (5,509356), (4,509356), (3,509356), (0,509356), (1,509356), (7,509356)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok44 : bitSearch source target 19 9 st44 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 522239 [(6,509356), (2,509356), (5,509356), (4,509356), (3,509356), (0,509356), (1,509356), (7,509356)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 7 [(6,509356), (2,509356), (5,509356), (4,509356), (3,509356), (0,509356), (1,509356), (7,509356)] = st27 := by decide +kernel
    rw [h]
    exact ok27
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 10 [(6,509356), (2,509356), (5,509356), (4,509356), (3,509356), (0,509356), (1,509356), (7,509356)] = st38 := by decide +kernel
    rw [h]
    exact ok38
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 18 [(6,509356), (2,509356), (5,509356), (4,509356), (3,509356), (0,509356), (1,509356), (7,509356)] = st43 := by decide +kernel
    rw [h]
    exact ok43
def st45 : List (Nat × Nat) := [(6,246611), (2,246611), (5,246611), (4,246611), (3,246611), (0,246611), (1,246611), (7,246611)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok45 : bitSearch source target 19 8 st45 = false := by
  decide +kernel
def st46 : List (Nat × Nat) := [(9,520191), (6,254803), (2,254803), (5,254803), (4,254803), (3,254803), (0,254803), (1,254803), (7,254803)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok46 : bitSearch source target 19 9 st46 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 520191 [(6,254803), (2,254803), (5,254803), (4,254803), (3,254803), (0,254803), (1,254803), (7,254803)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 6 [(6,254803), (2,254803), (5,254803), (4,254803), (3,254803), (0,254803), (1,254803), (7,254803)] = st22 := by decide +kernel
    rw [h]
    exact ok22
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 9 [(6,254803), (2,254803), (5,254803), (4,254803), (3,254803), (0,254803), (1,254803), (7,254803)] = st33 := by decide +kernel
    rw [h]
    exact ok33
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 13 [(6,254803), (2,254803), (5,254803), (4,254803), (3,254803), (0,254803), (1,254803), (7,254803)] = st45 := by decide +kernel
    rw [h]
    exact ok45
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st47 : List (Nat × Nat) := [(9,516095), (6,250707), (2,250707), (5,250707), (4,250707), (3,250707), (0,250707), (1,250707), (7,250707)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok47 : bitSearch source target 19 9 st47 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 516095 [(6,250707), (2,250707), (5,250707), (4,250707), (3,250707), (0,250707), (1,250707), (7,250707)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 6 [(6,250707), (2,250707), (5,250707), (4,250707), (3,250707), (0,250707), (1,250707), (7,250707)] = st23 := by decide +kernel
    rw [h]
    exact ok23
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 9 [(6,250707), (2,250707), (5,250707), (4,250707), (3,250707), (0,250707), (1,250707), (7,250707)] = st34 := by decide +kernel
    rw [h]
    exact ok34
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 12 [(6,250707), (2,250707), (5,250707), (4,250707), (3,250707), (0,250707), (1,250707), (7,250707)] = st45 := by decide +kernel
    rw [h]
    exact ok45
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st48 : List (Nat × Nat) := [(6,277411), (2,277411), (5,277411), (4,277411), (3,277411), (0,277411), (1,277411), (7,277411)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok48 : bitSearch source target 19 8 st48 = false := by
  decide +kernel
def st49 : List (Nat × Nat) := [(9,507903), (6,310179), (2,310179), (5,310179), (4,310179), (3,310179), (0,310179), (1,310179), (7,310179)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok49 : bitSearch source target 19 9 st49 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 507903 [(6,310179), (2,310179), (5,310179), (4,310179), (3,310179), (0,310179), (1,310179), (7,310179)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 7 [(6,310179), (2,310179), (5,310179), (4,310179), (3,310179), (0,310179), (1,310179), (7,310179)] = st28 := by decide +kernel
    rw [h]
    exact ok28
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 9 [(6,310179), (2,310179), (5,310179), (4,310179), (3,310179), (0,310179), (1,310179), (7,310179)] = st35 := by decide +kernel
    rw [h]
    exact ok35
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 15 [(6,310179), (2,310179), (5,310179), (4,310179), (3,310179), (0,310179), (1,310179), (7,310179)] = st48 := by decide +kernel
    rw [h]
    exact ok48
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st50 : List (Nat × Nat) := [(9,491519), (6,293795), (2,293795), (5,293795), (4,293795), (3,293795), (0,293795), (1,293795), (7,293795)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok50 : bitSearch source target 19 9 st50 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 491519 [(6,293795), (2,293795), (5,293795), (4,293795), (3,293795), (0,293795), (1,293795), (7,293795)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 7 [(6,293795), (2,293795), (5,293795), (4,293795), (3,293795), (0,293795), (1,293795), (7,293795)] = st29 := by decide +kernel
    rw [h]
    exact ok29
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 9 [(6,293795), (2,293795), (5,293795), (4,293795), (3,293795), (0,293795), (1,293795), (7,293795)] = st36 := by decide +kernel
    rw [h]
    exact ok36
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 14 [(6,293795), (2,293795), (5,293795), (4,293795), (3,293795), (0,293795), (1,293795), (7,293795)] = st48 := by decide +kernel
    rw [h]
    exact ok48
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st51 : List (Nat × Nat) := [(6,277852), (2,277852), (5,277852), (4,277852), (3,277852), (0,277852), (1,277852), (7,277852)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok51 : bitSearch source target 19 8 st51 = false := by
  decide +kernel
def st52 : List (Nat × Nat) := [(9,458751), (6,408924), (2,408924), (5,408924), (4,408924), (3,408924), (0,408924), (1,408924), (7,408924)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok52 : bitSearch source target 19 9 st52 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 458751 [(6,408924), (2,408924), (5,408924), (4,408924), (3,408924), (0,408924), (1,408924), (7,408924)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 6 [(6,408924), (2,408924), (5,408924), (4,408924), (3,408924), (0,408924), (1,408924), (7,408924)] = st24 := by decide +kernel
    rw [h]
    exact ok24
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 10 [(6,408924), (2,408924), (5,408924), (4,408924), (3,408924), (0,408924), (1,408924), (7,408924)] = st39 := by decide +kernel
    rw [h]
    exact ok39
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 17 [(6,408924), (2,408924), (5,408924), (4,408924), (3,408924), (0,408924), (1,408924), (7,408924)] = st51 := by decide +kernel
    rw [h]
    exact ok51
  · decide +kernel
def st53 : List (Nat × Nat) := [(9,393215), (6,343388), (2,343388), (5,343388), (4,343388), (3,343388), (0,343388), (1,343388), (7,343388)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok53 : bitSearch source target 19 9 st53 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 393215 [(6,343388), (2,343388), (5,343388), (4,343388), (3,343388), (0,343388), (1,343388), (7,343388)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 6 [(6,343388), (2,343388), (5,343388), (4,343388), (3,343388), (0,343388), (1,343388), (7,343388)] = st25 := by decide +kernel
    rw [h]
    exact ok25
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 10 [(6,343388), (2,343388), (5,343388), (4,343388), (3,343388), (0,343388), (1,343388), (7,343388)] = st40 := by decide +kernel
    rw [h]
    exact ok40
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 16 [(6,343388), (2,343388), (5,343388), (4,343388), (3,343388), (0,343388), (1,343388), (7,343388)] = st51 := by decide +kernel
    rw [h]
    exact ok51
  · decide +kernel
  · decide +kernel
def st54 : List (Nat × Nat) := [(9,262143), (6,249260), (2,249260), (5,249260), (4,249260), (3,249260), (0,249260), (1,249260), (7,249260)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok54 : bitSearch source target 19 9 st54 = false := by
  refine bitSearch_false_of_branches source target 19 8 9 262143 [(6,249260), (2,249260), (5,249260), (4,249260), (3,249260), (0,249260), (1,249260), (7,249260)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 7 [(6,249260), (2,249260), (5,249260), (4,249260), (3,249260), (0,249260), (1,249260), (7,249260)] = st30 := by decide +kernel
    rw [h]
    exact ok30
  · decide +kernel
  · decide +kernel
  · apply branch_false_of_child
    have h : propagate source target 19 9 10 [(6,249260), (2,249260), (5,249260), (4,249260), (3,249260), (0,249260), (1,249260), (7,249260)] = st41 := by decide +kernel
    rw [h]
    exact ok41
  · apply branch_false_of_child
    have h : propagate source target 19 9 11 [(6,249260), (2,249260), (5,249260), (4,249260), (3,249260), (0,249260), (1,249260), (7,249260)] = st43 := by decide +kernel
    rw [h]
    exact ok43
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
def st55 : List (Nat × Nat) := [(8,524287), (9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok55 : bitSearch source target 19 10 st55 = false := by
  refine bitSearch_false_of_branches source target 19 9 8 524287 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 8 0 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st4 := by decide +kernel
    rw [h]
    exact ok4
  · apply branch_false_of_child
    have h : propagate source target 19 8 1 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st8 := by decide +kernel
    rw [h]
    exact ok8
  · apply branch_false_of_child
    have h : propagate source target 19 8 2 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st13 := by decide +kernel
    rw [h]
    exact ok13
  · apply branch_false_of_child
    have h : propagate source target 19 8 3 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st17 := by decide +kernel
    rw [h]
    exact ok17
  · apply branch_false_of_child
    have h : propagate source target 19 8 4 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st19 := by decide +kernel
    rw [h]
    exact ok19
  · apply branch_false_of_child
    have h : propagate source target 19 8 5 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st21 := by decide +kernel
    rw [h]
    exact ok21
  · apply branch_false_of_child
    have h : propagate source target 19 8 6 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st26 := by decide +kernel
    rw [h]
    exact ok26
  · apply branch_false_of_child
    have h : propagate source target 19 8 7 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st31 := by decide +kernel
    rw [h]
    exact ok31
  · apply branch_false_of_child
    have h : propagate source target 19 8 8 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st32 := by decide +kernel
    rw [h]
    exact ok32
  · apply branch_false_of_child
    have h : propagate source target 19 8 9 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st37 := by decide +kernel
    rw [h]
    exact ok37
  · apply branch_false_of_child
    have h : propagate source target 19 8 10 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st42 := by decide +kernel
    rw [h]
    exact ok42
  · apply branch_false_of_child
    have h : propagate source target 19 8 11 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st44 := by decide +kernel
    rw [h]
    exact ok44
  · apply branch_false_of_child
    have h : propagate source target 19 8 12 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st46 := by decide +kernel
    rw [h]
    exact ok46
  · apply branch_false_of_child
    have h : propagate source target 19 8 13 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st47 := by decide +kernel
    rw [h]
    exact ok47
  · apply branch_false_of_child
    have h : propagate source target 19 8 14 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st49 := by decide +kernel
    rw [h]
    exact ok49
  · apply branch_false_of_child
    have h : propagate source target 19 8 15 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st50 := by decide +kernel
    rw [h]
    exact ok50
  · apply branch_false_of_child
    have h : propagate source target 19 8 16 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st52 := by decide +kernel
    rw [h]
    exact ok52
  · apply branch_false_of_child
    have h : propagate source target 19 8 17 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st53 := by decide +kernel
    rw [h]
    exact ok53
  · apply branch_false_of_child
    have h : propagate source target 19 8 18 [(9,524287), (6,524287), (2,524287), (5,524287), (4,524287), (3,524287), (0,524287), (1,524287), (7,524287)] = st54 := by decide +kernel
    rw [h]
    exact ok54
def sourceGraph : SimpleGraph (Fin 10) where
  Adj i j := (source i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
def targetGraph : SimpleGraph (Fin 19) where
  Adj i j := (target i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
def vertices : List Nat := [8, 9, 6, 2, 5, 4, 3, 0, 1, 7]
theorem no_embedding : ¬ ∃ f : Fin 10 ↪ Fin 19,
    ∀ u v, sourceGraph.Adj u v → targetGraph.Adj (f u) (f v) := by
  refine bitSearch_false_no_embedding sourceGraph targetGraph source target
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) vertices
    (by decide +kernel) (by decide +kernel) 10 ?_
  have h : (vertices.map fun v => (v,2^19-1)) = st55 := by decide +kernel
  rw [h]
  exact ok55
end Order10Search103

-- closed residual embedding search 106
namespace Order10Search106
open EmbeddingDFS
def sourceRows : List Nat := [962, 961, 1008, 1008, 1004, 988, 831, 831, 255, 255]
def targetRows : List Nat := [62206, 62205, 462075, 462071, 210543, 315039, 210719, 315183, 523968, 61939, 461308, 509356, 254803, 250707, 310179, 293795, 408924, 343388, 249260]
def source (v : Nat) : Nat := sourceRows.getD v 0
def target (v : Nat) : Nat := targetRows.getD v 0
def st0 : List (Nat × Nat) := [(7,524286), (8,62206), (9,62206), (4,62206), (5,62206), (2,62206), (3,62206), (0,62206), (1,62206)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok0 : bitSearch source target 19 9 st0 = false := by
  decide +kernel
def st1 : List (Nat × Nat) := [(7,524285), (8,62205), (9,62205), (4,62205), (5,62205), (2,62205), (3,62205), (0,62205), (1,62205)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok1 : bitSearch source target 19 9 st1 = false := by
  decide +kernel
def st2 : List (Nat × Nat) := [(7,524283), (8,462075), (9,462075), (4,462075), (5,462075), (2,462075), (3,462075), (0,462075), (1,462075)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok2 : bitSearch source target 19 9 st2 = false := by
  decide +kernel
def st3 : List (Nat × Nat) := [(7,524279), (8,462071), (9,462071), (4,462071), (5,462071), (2,462071), (3,462071), (0,462071), (1,462071)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3 : bitSearch source target 19 9 st3 = false := by
  decide +kernel
def st4 : List (Nat × Nat) := [(7,524271), (8,210543), (9,210543), (4,210543), (5,210543), (2,210543), (3,210543), (0,210543), (1,210543)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4 : bitSearch source target 19 9 st4 = false := by
  decide +kernel
def st5 : List (Nat × Nat) := [(7,524255), (8,315039), (9,315039), (4,315039), (5,315039), (2,315039), (3,315039), (0,315039), (1,315039)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5 : bitSearch source target 19 9 st5 = false := by
  decide +kernel
def st6 : List (Nat × Nat) := [(7,524223), (8,210719), (9,210719), (4,210719), (5,210719), (2,210719), (3,210719), (0,210719), (1,210719)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6 : bitSearch source target 19 9 st6 = false := by
  decide +kernel
def st7 : List (Nat × Nat) := [(7,524159), (8,315183), (9,315183), (4,315183), (5,315183), (2,315183), (3,315183), (0,315183), (1,315183)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7 : bitSearch source target 19 9 st7 = false := by
  decide +kernel
def st8 : List (Nat × Nat) := [(7,524031), (8,523968), (9,523968), (4,523968), (5,523968), (2,523968), (3,523968), (0,523968), (1,523968)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8 : bitSearch source target 19 9 st8 = false := by
  decide +kernel
def st9 : List (Nat × Nat) := [(7,523775), (8,61939), (9,61939), (4,61939), (5,61939), (2,61939), (3,61939), (0,61939), (1,61939)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok9 : bitSearch source target 19 9 st9 = false := by
  decide +kernel
def st10 : List (Nat × Nat) := [(7,523263), (8,461308), (9,461308), (4,461308), (5,461308), (2,461308), (3,461308), (0,461308), (1,461308)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok10 : bitSearch source target 19 9 st10 = false := by
  decide +kernel
def st11 : List (Nat × Nat) := [(7,522239), (8,509356), (9,509356), (4,509356), (5,509356), (2,509356), (3,509356), (0,509356), (1,509356)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok11 : bitSearch source target 19 9 st11 = false := by
  decide +kernel
def st12 : List (Nat × Nat) := [(7,520191), (8,254803), (9,254803), (4,254803), (5,254803), (2,254803), (3,254803), (0,254803), (1,254803)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok12 : bitSearch source target 19 9 st12 = false := by
  decide +kernel
def st13 : List (Nat × Nat) := [(7,516095), (8,250707), (9,250707), (4,250707), (5,250707), (2,250707), (3,250707), (0,250707), (1,250707)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok13 : bitSearch source target 19 9 st13 = false := by
  decide +kernel
def st14 : List (Nat × Nat) := [(7,507903), (8,310179), (9,310179), (4,310179), (5,310179), (2,310179), (3,310179), (0,310179), (1,310179)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok14 : bitSearch source target 19 9 st14 = false := by
  decide +kernel
def st15 : List (Nat × Nat) := [(7,491519), (8,293795), (9,293795), (4,293795), (5,293795), (2,293795), (3,293795), (0,293795), (1,293795)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok15 : bitSearch source target 19 9 st15 = false := by
  decide +kernel
def st16 : List (Nat × Nat) := [(7,458751), (8,408924), (9,408924), (4,408924), (5,408924), (2,408924), (3,408924), (0,408924), (1,408924)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok16 : bitSearch source target 19 9 st16 = false := by
  decide +kernel
def st17 : List (Nat × Nat) := [(7,393215), (8,343388), (9,343388), (4,343388), (5,343388), (2,343388), (3,343388), (0,343388), (1,343388)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok17 : bitSearch source target 19 9 st17 = false := by
  decide +kernel
def st18 : List (Nat × Nat) := [(7,262143), (8,249260), (9,249260), (4,249260), (5,249260), (2,249260), (3,249260), (0,249260), (1,249260)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok18 : bitSearch source target 19 9 st18 = false := by
  decide +kernel
def st19 : List (Nat × Nat) := [(6,524287), (7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok19 : bitSearch source target 19 10 st19 = false := by
  refine bitSearch_false_of_branches source target 19 9 6 524287 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 6 0 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st0 := by decide +kernel
    rw [h]
    exact ok0
  · apply branch_false_of_child
    have h : propagate source target 19 6 1 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st1 := by decide +kernel
    rw [h]
    exact ok1
  · apply branch_false_of_child
    have h : propagate source target 19 6 2 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st2 := by decide +kernel
    rw [h]
    exact ok2
  · apply branch_false_of_child
    have h : propagate source target 19 6 3 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st3 := by decide +kernel
    rw [h]
    exact ok3
  · apply branch_false_of_child
    have h : propagate source target 19 6 4 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st4 := by decide +kernel
    rw [h]
    exact ok4
  · apply branch_false_of_child
    have h : propagate source target 19 6 5 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st5 := by decide +kernel
    rw [h]
    exact ok5
  · apply branch_false_of_child
    have h : propagate source target 19 6 6 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st6 := by decide +kernel
    rw [h]
    exact ok6
  · apply branch_false_of_child
    have h : propagate source target 19 6 7 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st7 := by decide +kernel
    rw [h]
    exact ok7
  · apply branch_false_of_child
    have h : propagate source target 19 6 8 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st8 := by decide +kernel
    rw [h]
    exact ok8
  · apply branch_false_of_child
    have h : propagate source target 19 6 9 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st9 := by decide +kernel
    rw [h]
    exact ok9
  · apply branch_false_of_child
    have h : propagate source target 19 6 10 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st10 := by decide +kernel
    rw [h]
    exact ok10
  · apply branch_false_of_child
    have h : propagate source target 19 6 11 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st11 := by decide +kernel
    rw [h]
    exact ok11
  · apply branch_false_of_child
    have h : propagate source target 19 6 12 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st12 := by decide +kernel
    rw [h]
    exact ok12
  · apply branch_false_of_child
    have h : propagate source target 19 6 13 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st13 := by decide +kernel
    rw [h]
    exact ok13
  · apply branch_false_of_child
    have h : propagate source target 19 6 14 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st14 := by decide +kernel
    rw [h]
    exact ok14
  · apply branch_false_of_child
    have h : propagate source target 19 6 15 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st15 := by decide +kernel
    rw [h]
    exact ok15
  · apply branch_false_of_child
    have h : propagate source target 19 6 16 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st16 := by decide +kernel
    rw [h]
    exact ok16
  · apply branch_false_of_child
    have h : propagate source target 19 6 17 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st17 := by decide +kernel
    rw [h]
    exact ok17
  · apply branch_false_of_child
    have h : propagate source target 19 6 18 [(7,524287), (8,524287), (9,524287), (4,524287), (5,524287), (2,524287), (3,524287), (0,524287), (1,524287)] = st18 := by decide +kernel
    rw [h]
    exact ok18
def sourceGraph : SimpleGraph (Fin 10) where
  Adj i j := (source i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
def targetGraph : SimpleGraph (Fin 19) where
  Adj i j := (target i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
def vertices : List Nat := [6, 7, 8, 9, 4, 5, 2, 3, 0, 1]
theorem no_embedding : ¬ ∃ f : Fin 10 ↪ Fin 19,
    ∀ u v, sourceGraph.Adj u v → targetGraph.Adj (f u) (f v) := by
  refine bitSearch_false_no_embedding sourceGraph targetGraph source target
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) vertices
    (by decide +kernel) (by decide +kernel) 10 ?_
  have h : (vertices.map fun v => (v,2^19-1)) = st19 := by decide +kernel
  rw [h]
  exact ok19
end Order10Search106

-- closed residual embedding search 129
namespace Order10Search129
open EmbeddingDFS
def sourceRows : List Nat := [966, 965, 963, 1008, 1000, 984, 575, 831, 703, 511]
def targetRows : List Nat := [493502, 505981, 64443, 292727, 159471, 89567, 490554, 249653, 382637, 451997, 476153, 258294, 387438, 449118, 16380, 473991, 433635, 372435, 243531]
def source (v : Nat) : Nat := sourceRows.getD v 0
def target (v : Nat) : Nat := targetRows.getD v 0
def st0 : List (Nat × Nat) := [(8,493502), (6,524286), (3,493502), (2,493502), (0,493502), (9,493502), (5,493502), (1,493502), (4,493502)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok0 : bitSearch source target 19 9 st0 = false := by
  decide +kernel
def st1 : List (Nat × Nat) := [(8,505981), (6,524285), (3,505981), (2,505981), (0,505981), (9,505981), (5,505981), (1,505981), (4,505981)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok1 : bitSearch source target 19 9 st1 = false := by
  decide +kernel
def st2 : List (Nat × Nat) := [(8,64443), (6,524283), (3,64443), (2,64443), (0,64443), (9,64443), (5,64443), (1,64443), (4,64443)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok2 : bitSearch source target 19 9 st2 = false := by
  decide +kernel
def st3 : List (Nat × Nat) := [(8,292727), (6,524279), (3,292727), (2,292727), (0,292727), (9,292727), (5,292727), (1,292727), (4,292727)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3 : bitSearch source target 19 9 st3 = false := by
  decide +kernel
def st4 : List (Nat × Nat) := [(8,159471), (6,524271), (3,159471), (2,159471), (0,159471), (9,159471), (5,159471), (1,159471), (4,159471)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4 : bitSearch source target 19 9 st4 = false := by
  decide +kernel
def st5 : List (Nat × Nat) := [(8,89567), (6,524255), (3,89567), (2,89567), (0,89567), (9,89567), (5,89567), (1,89567), (4,89567)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5 : bitSearch source target 19 9 st5 = false := by
  decide +kernel
def st6 : List (Nat × Nat) := [(8,490554), (6,524223), (3,490554), (2,490554), (0,490554), (9,490554), (5,490554), (1,490554), (4,490554)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6 : bitSearch source target 19 9 st6 = false := by
  decide +kernel
def st7 : List (Nat × Nat) := [(8,249653), (6,524159), (3,249653), (2,249653), (0,249653), (9,249653), (5,249653), (1,249653), (4,249653)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7 : bitSearch source target 19 9 st7 = false := by
  decide +kernel
def st8 : List (Nat × Nat) := [(8,382637), (6,524031), (3,382637), (2,382637), (0,382637), (9,382637), (5,382637), (1,382637), (4,382637)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8 : bitSearch source target 19 9 st8 = false := by
  decide +kernel
def st9 : List (Nat × Nat) := [(8,451997), (6,523775), (3,451997), (2,451997), (0,451997), (9,451997), (5,451997), (1,451997), (4,451997)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok9 : bitSearch source target 19 9 st9 = false := by
  decide +kernel
def st10 : List (Nat × Nat) := [(8,476153), (6,523263), (3,476153), (2,476153), (0,476153), (9,476153), (5,476153), (1,476153), (4,476153)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok10 : bitSearch source target 19 9 st10 = false := by
  decide +kernel
def st11 : List (Nat × Nat) := [(8,258294), (6,522239), (3,258294), (2,258294), (0,258294), (9,258294), (5,258294), (1,258294), (4,258294)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok11 : bitSearch source target 19 9 st11 = false := by
  decide +kernel
def st12 : List (Nat × Nat) := [(8,387438), (6,520191), (3,387438), (2,387438), (0,387438), (9,387438), (5,387438), (1,387438), (4,387438)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok12 : bitSearch source target 19 9 st12 = false := by
  decide +kernel
def st13 : List (Nat × Nat) := [(8,449118), (6,516095), (3,449118), (2,449118), (0,449118), (9,449118), (5,449118), (1,449118), (4,449118)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok13 : bitSearch source target 19 9 st13 = false := by
  decide +kernel
def st14 : List (Nat × Nat) := [(8,16380), (6,507903), (3,16380), (2,16380), (0,16380), (9,16380), (5,16380), (1,16380), (4,16380)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok14 : bitSearch source target 19 9 st14 = false := by
  decide +kernel
def st15 : List (Nat × Nat) := [(8,473991), (6,491519), (3,473991), (2,473991), (0,473991), (9,473991), (5,473991), (1,473991), (4,473991)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok15 : bitSearch source target 19 9 st15 = false := by
  decide +kernel
def st16 : List (Nat × Nat) := [(8,433635), (6,458751), (3,433635), (2,433635), (0,433635), (9,433635), (5,433635), (1,433635), (4,433635)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok16 : bitSearch source target 19 9 st16 = false := by
  decide +kernel
def st17 : List (Nat × Nat) := [(8,372435), (6,393215), (3,372435), (2,372435), (0,372435), (9,372435), (5,372435), (1,372435), (4,372435)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok17 : bitSearch source target 19 9 st17 = false := by
  decide +kernel
def st18 : List (Nat × Nat) := [(8,243531), (6,262143), (3,243531), (2,243531), (0,243531), (9,243531), (5,243531), (1,243531), (4,243531)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok18 : bitSearch source target 19 9 st18 = false := by
  decide +kernel
def st19 : List (Nat × Nat) := [(7,524287), (8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok19 : bitSearch source target 19 10 st19 = false := by
  refine bitSearch_false_of_branches source target 19 9 7 524287 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 7 0 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st0 := by decide +kernel
    rw [h]
    exact ok0
  · apply branch_false_of_child
    have h : propagate source target 19 7 1 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st1 := by decide +kernel
    rw [h]
    exact ok1
  · apply branch_false_of_child
    have h : propagate source target 19 7 2 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st2 := by decide +kernel
    rw [h]
    exact ok2
  · apply branch_false_of_child
    have h : propagate source target 19 7 3 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st3 := by decide +kernel
    rw [h]
    exact ok3
  · apply branch_false_of_child
    have h : propagate source target 19 7 4 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st4 := by decide +kernel
    rw [h]
    exact ok4
  · apply branch_false_of_child
    have h : propagate source target 19 7 5 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st5 := by decide +kernel
    rw [h]
    exact ok5
  · apply branch_false_of_child
    have h : propagate source target 19 7 6 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st6 := by decide +kernel
    rw [h]
    exact ok6
  · apply branch_false_of_child
    have h : propagate source target 19 7 7 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st7 := by decide +kernel
    rw [h]
    exact ok7
  · apply branch_false_of_child
    have h : propagate source target 19 7 8 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st8 := by decide +kernel
    rw [h]
    exact ok8
  · apply branch_false_of_child
    have h : propagate source target 19 7 9 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st9 := by decide +kernel
    rw [h]
    exact ok9
  · apply branch_false_of_child
    have h : propagate source target 19 7 10 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st10 := by decide +kernel
    rw [h]
    exact ok10
  · apply branch_false_of_child
    have h : propagate source target 19 7 11 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st11 := by decide +kernel
    rw [h]
    exact ok11
  · apply branch_false_of_child
    have h : propagate source target 19 7 12 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st12 := by decide +kernel
    rw [h]
    exact ok12
  · apply branch_false_of_child
    have h : propagate source target 19 7 13 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st13 := by decide +kernel
    rw [h]
    exact ok13
  · apply branch_false_of_child
    have h : propagate source target 19 7 14 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st14 := by decide +kernel
    rw [h]
    exact ok14
  · apply branch_false_of_child
    have h : propagate source target 19 7 15 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st15 := by decide +kernel
    rw [h]
    exact ok15
  · apply branch_false_of_child
    have h : propagate source target 19 7 16 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st16 := by decide +kernel
    rw [h]
    exact ok16
  · apply branch_false_of_child
    have h : propagate source target 19 7 17 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st17 := by decide +kernel
    rw [h]
    exact ok17
  · apply branch_false_of_child
    have h : propagate source target 19 7 18 [(8,524287), (6,524287), (3,524287), (2,524287), (0,524287), (9,524287), (5,524287), (1,524287), (4,524287)] = st18 := by decide +kernel
    rw [h]
    exact ok18
def sourceGraph : SimpleGraph (Fin 10) where
  Adj i j := (source i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
def targetGraph : SimpleGraph (Fin 19) where
  Adj i j := (target i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
def vertices : List Nat := [7, 8, 6, 3, 2, 0, 9, 5, 1, 4]
theorem no_embedding : ¬ ∃ f : Fin 10 ↪ Fin 19,
    ∀ u v, sourceGraph.Adj u v → targetGraph.Adj (f u) (f v) := by
  refine bitSearch_false_no_embedding sourceGraph targetGraph source target
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) vertices
    (by decide +kernel) (by decide +kernel) 10 ?_
  have h : (vertices.map fun v => (v,2^19-1)) = st19 := by decide +kernel
  rw [h]
  exact ok19
end Order10Search129

-- closed residual embedding search 132
namespace Order10Search132
open EmbeddingDFS
def sourceRows : List Nat := [966, 965, 963, 1008, 1000, 984, 831, 831, 255, 255]
def targetRows : List Nat := [62206, 62205, 462075, 462071, 210543, 315039, 210719, 315183, 523968, 61939, 461308, 509356, 254803, 250707, 310179, 293795, 408924, 343388, 249260]
def source (v : Nat) : Nat := sourceRows.getD v 0
def target (v : Nat) : Nat := targetRows.getD v 0
def st0 : List (Nat × Nat) := [(7,524286), (8,62206), (9,62206), (0,62206), (1,62206), (2,62206), (3,62206), (4,62206), (5,62206)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok0 : bitSearch source target 19 9 st0 = false := by
  decide +kernel
def st1 : List (Nat × Nat) := [(7,524285), (8,62205), (9,62205), (0,62205), (1,62205), (2,62205), (3,62205), (4,62205), (5,62205)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok1 : bitSearch source target 19 9 st1 = false := by
  decide +kernel
def st2 : List (Nat × Nat) := [(7,524283), (8,462075), (9,462075), (0,462075), (1,462075), (2,462075), (3,462075), (4,462075), (5,462075)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok2 : bitSearch source target 19 9 st2 = false := by
  decide +kernel
def st3 : List (Nat × Nat) := [(7,524279), (8,462071), (9,462071), (0,462071), (1,462071), (2,462071), (3,462071), (4,462071), (5,462071)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3 : bitSearch source target 19 9 st3 = false := by
  decide +kernel
def st4 : List (Nat × Nat) := [(7,524271), (8,210543), (9,210543), (0,210543), (1,210543), (2,210543), (3,210543), (4,210543), (5,210543)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4 : bitSearch source target 19 9 st4 = false := by
  decide +kernel
def st5 : List (Nat × Nat) := [(7,524255), (8,315039), (9,315039), (0,315039), (1,315039), (2,315039), (3,315039), (4,315039), (5,315039)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5 : bitSearch source target 19 9 st5 = false := by
  decide +kernel
def st6 : List (Nat × Nat) := [(7,524223), (8,210719), (9,210719), (0,210719), (1,210719), (2,210719), (3,210719), (4,210719), (5,210719)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6 : bitSearch source target 19 9 st6 = false := by
  decide +kernel
def st7 : List (Nat × Nat) := [(7,524159), (8,315183), (9,315183), (0,315183), (1,315183), (2,315183), (3,315183), (4,315183), (5,315183)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7 : bitSearch source target 19 9 st7 = false := by
  decide +kernel
def st8 : List (Nat × Nat) := [(7,524031), (8,523968), (9,523968), (0,523968), (1,523968), (2,523968), (3,523968), (4,523968), (5,523968)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8 : bitSearch source target 19 9 st8 = false := by
  decide +kernel
def st9 : List (Nat × Nat) := [(7,523775), (8,61939), (9,61939), (0,61939), (1,61939), (2,61939), (3,61939), (4,61939), (5,61939)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok9 : bitSearch source target 19 9 st9 = false := by
  decide +kernel
def st10 : List (Nat × Nat) := [(7,523263), (8,461308), (9,461308), (0,461308), (1,461308), (2,461308), (3,461308), (4,461308), (5,461308)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok10 : bitSearch source target 19 9 st10 = false := by
  decide +kernel
def st11 : List (Nat × Nat) := [(7,522239), (8,509356), (9,509356), (0,509356), (1,509356), (2,509356), (3,509356), (4,509356), (5,509356)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok11 : bitSearch source target 19 9 st11 = false := by
  decide +kernel
def st12 : List (Nat × Nat) := [(7,520191), (8,254803), (9,254803), (0,254803), (1,254803), (2,254803), (3,254803), (4,254803), (5,254803)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok12 : bitSearch source target 19 9 st12 = false := by
  decide +kernel
def st13 : List (Nat × Nat) := [(7,516095), (8,250707), (9,250707), (0,250707), (1,250707), (2,250707), (3,250707), (4,250707), (5,250707)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok13 : bitSearch source target 19 9 st13 = false := by
  decide +kernel
def st14 : List (Nat × Nat) := [(7,507903), (8,310179), (9,310179), (0,310179), (1,310179), (2,310179), (3,310179), (4,310179), (5,310179)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok14 : bitSearch source target 19 9 st14 = false := by
  decide +kernel
def st15 : List (Nat × Nat) := [(7,491519), (8,293795), (9,293795), (0,293795), (1,293795), (2,293795), (3,293795), (4,293795), (5,293795)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok15 : bitSearch source target 19 9 st15 = false := by
  decide +kernel
def st16 : List (Nat × Nat) := [(7,458751), (8,408924), (9,408924), (0,408924), (1,408924), (2,408924), (3,408924), (4,408924), (5,408924)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok16 : bitSearch source target 19 9 st16 = false := by
  decide +kernel
def st17 : List (Nat × Nat) := [(7,393215), (8,343388), (9,343388), (0,343388), (1,343388), (2,343388), (3,343388), (4,343388), (5,343388)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok17 : bitSearch source target 19 9 st17 = false := by
  decide +kernel
def st18 : List (Nat × Nat) := [(7,262143), (8,249260), (9,249260), (0,249260), (1,249260), (2,249260), (3,249260), (4,249260), (5,249260)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok18 : bitSearch source target 19 9 st18 = false := by
  decide +kernel
def st19 : List (Nat × Nat) := [(6,524287), (7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok19 : bitSearch source target 19 10 st19 = false := by
  refine bitSearch_false_of_branches source target 19 9 6 524287 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] ?_
  intro w hw
  change w ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply branch_false_of_child
    have h : propagate source target 19 6 0 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st0 := by decide +kernel
    rw [h]
    exact ok0
  · apply branch_false_of_child
    have h : propagate source target 19 6 1 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st1 := by decide +kernel
    rw [h]
    exact ok1
  · apply branch_false_of_child
    have h : propagate source target 19 6 2 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st2 := by decide +kernel
    rw [h]
    exact ok2
  · apply branch_false_of_child
    have h : propagate source target 19 6 3 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st3 := by decide +kernel
    rw [h]
    exact ok3
  · apply branch_false_of_child
    have h : propagate source target 19 6 4 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st4 := by decide +kernel
    rw [h]
    exact ok4
  · apply branch_false_of_child
    have h : propagate source target 19 6 5 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st5 := by decide +kernel
    rw [h]
    exact ok5
  · apply branch_false_of_child
    have h : propagate source target 19 6 6 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st6 := by decide +kernel
    rw [h]
    exact ok6
  · apply branch_false_of_child
    have h : propagate source target 19 6 7 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st7 := by decide +kernel
    rw [h]
    exact ok7
  · apply branch_false_of_child
    have h : propagate source target 19 6 8 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st8 := by decide +kernel
    rw [h]
    exact ok8
  · apply branch_false_of_child
    have h : propagate source target 19 6 9 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st9 := by decide +kernel
    rw [h]
    exact ok9
  · apply branch_false_of_child
    have h : propagate source target 19 6 10 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st10 := by decide +kernel
    rw [h]
    exact ok10
  · apply branch_false_of_child
    have h : propagate source target 19 6 11 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st11 := by decide +kernel
    rw [h]
    exact ok11
  · apply branch_false_of_child
    have h : propagate source target 19 6 12 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st12 := by decide +kernel
    rw [h]
    exact ok12
  · apply branch_false_of_child
    have h : propagate source target 19 6 13 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st13 := by decide +kernel
    rw [h]
    exact ok13
  · apply branch_false_of_child
    have h : propagate source target 19 6 14 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st14 := by decide +kernel
    rw [h]
    exact ok14
  · apply branch_false_of_child
    have h : propagate source target 19 6 15 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st15 := by decide +kernel
    rw [h]
    exact ok15
  · apply branch_false_of_child
    have h : propagate source target 19 6 16 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st16 := by decide +kernel
    rw [h]
    exact ok16
  · apply branch_false_of_child
    have h : propagate source target 19 6 17 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st17 := by decide +kernel
    rw [h]
    exact ok17
  · apply branch_false_of_child
    have h : propagate source target 19 6 18 [(7,524287), (8,524287), (9,524287), (0,524287), (1,524287), (2,524287), (3,524287), (4,524287), (5,524287)] = st18 := by decide +kernel
    rw [h]
    exact ok18
def sourceGraph : SimpleGraph (Fin 10) where
  Adj i j := (source i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
def targetGraph : SimpleGraph (Fin 19) where
  Adj i j := (target i.val).testBit j.val = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
def vertices : List Nat := [6, 7, 8, 9, 0, 1, 2, 3, 4, 5]
theorem no_embedding : ¬ ∃ f : Fin 10 ↪ Fin 19,
    ∀ u v, sourceGraph.Adj u v → targetGraph.Adj (f u) (f v) := by
  refine bitSearch_false_no_embedding sourceGraph targetGraph source target
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) vertices
    (by decide +kernel) (by decide +kernel) 10 ?_
  have h : (vertices.map fun v => (v,2^19-1)) = st19 := by decide +kernel
  rw [h]
  exact ok19
end Order10Search132

-- 193 clique/common-neighbor obstructions
namespace Order10Leaves
open Finset SimpleGraph CommonObstruction

def rowGraph (rows : List Nat) : SimpleGraph (Fin 10) where
  Adj i j := i ≠ j ∧ ((rows.getD i.val 0).testBit j.val = true ∨
    (rows.getD j.val 0).testBit i.val = true)
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨by intro i; simp⟩
instance (rows : List Nat) : DecidableRel (rowGraph rows).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ ((rows.getD i.val 0).testBit j.val = true ∨
    (rows.getD j.val 0).testBit i.val = true)))

theorem rowGraph_eq (G : SimpleGraph (Fin 10)) (rows : List Nat)
    (hrow : ∀ i j, G.Adj i j ↔ (rows.getD i.val 0).testBit j.val = true) :
    rowGraph rows = G := by
  ext i j
  constructor
  · rintro ⟨_,h|h⟩
    · exact (hrow i j).mpr h
    · exact G.symm.symm j i ((hrow j i).mpr h)
  · intro h
    exact ⟨G.ne_of_adj h, Or.inl ((hrow i j).mp h)⟩

def NoEmbed (G : SimpleGraph (Fin 10)) (H : SimpleGraph (Fin 19)) : Prop :=
  ¬ ∃ f : Fin 10 ↪ Fin 19, ∀ u v, G.Adj u v → H.Adj (f u) (f v)

theorem noEmbed_as_bad (G : SimpleGraph (Fin 10)) (i : Fin 2)
    (h : NoEmbed G (Order10Common.targets i)) :
    ∃ i : Fin 2, ¬ ∃ f : Fin 10 → Fin 19, Function.Injective f ∧
      ∀ u v, G.Adj u v → (Order10Common.targets i).Adj (f u) (f v) := by
  refine ⟨i,?_⟩
  rintro ⟨f,hf,ha⟩
  exact h ⟨⟨f,hf⟩,ha⟩


theorem bad_of_rows (G : SimpleGraph (Fin 10)) (source : Nat → Nat)
    (hrow : ∀ u v : Fin 10, G.Adj u v ↔ (source u.val).testBit v.val = true)
    (rows : List Nat) (he : ∀ u : Fin 10, rows.getD u.val 0 = source u.val)
    (h : NoEmbed (rowGraph rows) Order10Common.target) :
    ∃ i : Fin 2, ¬ ∃ f : Fin 10 → Fin 19, Function.Injective f ∧
      ∀ u v, G.Adj u v → (Order10Common.targets i).Adj (f u) (f v) := by
  have hg : rowGraph rows = G := by
    apply rowGraph_eq
    intro u v
    rw [hrow u v, he u]
  apply noEmbed_as_bad G 0
  change NoEmbed G Order10Common.target
  rw [← hg]
  exact h

def rows_A02404_0_0 : List Nat := [962, 961, 1016, 1012, 1004, 988, 959, 895, 767, 511]
theorem reject_A02404_0_0 : NoEmbed (rowGraph rows_A02404_0_0) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_0_0) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_1_0 : List Nat := [960, 960, 1016, 1012, 1004, 988, 959, 895, 767, 511]
theorem reject_A02404_1_0 : NoEmbed (rowGraph rows_A02404_1_0) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_1_0) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_1_1 : List Nat := [898, 961, 1016, 1012, 1004, 988, 958, 895, 767, 511]
theorem reject_A02404_1_1 : NoEmbed (rowGraph rows_A02404_1_1) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_1_1) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_1_2 : List Nat := [962, 961, 1008, 1008, 1004, 988, 959, 895, 767, 511]
theorem reject_A02404_1_2 : NoEmbed (rowGraph rows_A02404_1_2) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_1_2) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_1_3 : List Nat := [962, 961, 952, 1012, 1004, 988, 955, 895, 767, 511]
theorem reject_A02404_1_3 : NoEmbed (rowGraph rows_A02404_1_3) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_1_3) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_1_4 : List Nat := [962, 961, 1016, 1012, 1004, 988, 831, 831, 767, 511]
theorem reject_A02404_1_4 : NoEmbed (rowGraph rows_A02404_1_4) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_1_4) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_0 : List Nat := [896, 960, 1016, 1012, 1004, 988, 958, 895, 767, 511]
theorem reject_A02404_2_0 : NoEmbed (rowGraph rows_A02404_2_0) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_0) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_1 : List Nat := [770, 961, 1016, 1012, 1004, 988, 958, 894, 767, 511]
theorem reject_A02404_2_1 : NoEmbed (rowGraph rows_A02404_2_1) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_1) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_2 : List Nat := [898, 897, 1016, 1012, 1004, 988, 956, 895, 767, 511]
theorem reject_A02404_2_2 : NoEmbed (rowGraph rows_A02404_2_2) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_2) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_3 : List Nat := [898, 833, 1016, 1012, 1004, 988, 958, 893, 767, 511]
theorem reject_A02404_2_3 : NoEmbed (rowGraph rows_A02404_2_3) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_3) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_4 : List Nat := [960, 960, 1008, 1008, 1004, 988, 959, 895, 767, 511]
theorem reject_A02404_2_4 : NoEmbed (rowGraph rows_A02404_2_4) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_4) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_5 : List Nat := [898, 961, 1008, 1008, 1004, 988, 958, 895, 767, 511]
theorem reject_A02404_2_5 : NoEmbed (rowGraph rows_A02404_2_5) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_5) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_6 : List Nat := [962, 961, 992, 1008, 1000, 988, 959, 895, 767, 511]
theorem reject_A02404_2_6 : NoEmbed (rowGraph rows_A02404_2_6) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_6) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_7 : List Nat := [960, 960, 952, 1012, 1004, 988, 955, 895, 767, 511]
theorem reject_A02404_2_7 : NoEmbed (rowGraph rows_A02404_2_7) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_7) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_8 : List Nat := [898, 961, 952, 1012, 1004, 988, 954, 895, 767, 511]
theorem reject_A02404_2_8 : NoEmbed (rowGraph rows_A02404_2_8) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_8) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_9 : List Nat := [962, 961, 944, 1008, 1004, 988, 955, 895, 767, 511]
theorem reject_A02404_2_9 : NoEmbed (rowGraph rows_A02404_2_9) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_9) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_10 : List Nat := [898, 961, 888, 1012, 1004, 988, 958, 891, 767, 511]
theorem reject_A02404_2_10 : NoEmbed (rowGraph rows_A02404_2_10) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_10) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_11 : List Nat := [962, 961, 824, 1012, 1004, 988, 955, 891, 767, 511]
theorem reject_A02404_2_11 : NoEmbed (rowGraph rows_A02404_2_11) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_11) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_12 : List Nat := [962, 961, 952, 948, 1004, 988, 947, 895, 767, 511]
theorem reject_A02404_2_12 : NoEmbed (rowGraph rows_A02404_2_12) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_12) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_13 : List Nat := [962, 961, 952, 884, 1004, 988, 955, 887, 767, 511]
theorem reject_A02404_2_13 : NoEmbed (rowGraph rows_A02404_2_13) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_13) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_14 : List Nat := [962, 961, 1008, 1008, 972, 972, 959, 895, 767, 511]
theorem reject_A02404_2_14 : NoEmbed (rowGraph rows_A02404_2_14) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_14) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,6,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_15 : List Nat := [962, 961, 1008, 1008, 940, 988, 943, 895, 767, 511]
theorem reject_A02404_2_15 : NoEmbed (rowGraph rows_A02404_2_15) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_15) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,5,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_16 : List Nat := [960, 960, 1016, 1012, 1004, 988, 831, 831, 767, 511]
theorem reject_A02404_2_16 : NoEmbed (rowGraph rows_A02404_2_16) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_16) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_17 : List Nat := [898, 961, 1016, 1012, 1004, 988, 830, 831, 767, 511]
theorem reject_A02404_2_17 : NoEmbed (rowGraph rows_A02404_2_17) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_17) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_18 : List Nat := [962, 961, 1008, 1008, 1004, 988, 831, 831, 767, 511]
theorem reject_A02404_2_18 : NoEmbed (rowGraph rows_A02404_2_18) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_18) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_19 : List Nat := [962, 961, 952, 1012, 1004, 988, 827, 831, 767, 511]
theorem reject_A02404_2_19 : NoEmbed (rowGraph rows_A02404_2_19) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_19) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_20 : List Nat := [962, 961, 1016, 1012, 1004, 988, 575, 831, 703, 511]
theorem reject_A02404_2_20 : NoEmbed (rowGraph rows_A02404_2_20) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_20) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_21 : List Nat := [898, 961, 1016, 1012, 1004, 988, 958, 639, 639, 511]
theorem reject_A02404_2_21 : NoEmbed (rowGraph rows_A02404_2_21) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_21) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_22 : List Nat := [962, 961, 952, 1012, 1004, 988, 955, 639, 639, 511]
theorem reject_A02404_2_22 : NoEmbed (rowGraph rows_A02404_2_22) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_22) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_2_23 : List Nat := [962, 961, 1016, 1012, 1004, 988, 831, 831, 255, 255]
theorem reject_A02404_2_23 : NoEmbed (rowGraph rows_A02404_2_23) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_2_23) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_0 : List Nat := [768, 960, 1016, 1012, 1004, 988, 958, 894, 767, 511]
theorem reject_A02404_3_0 : NoEmbed (rowGraph rows_A02404_3_0) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_0) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_1 : List Nat := [514, 961, 1016, 1012, 1004, 988, 958, 894, 766, 511]
theorem reject_A02404_3_1 : NoEmbed (rowGraph rows_A02404_3_1) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_1) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_2 : List Nat := [896, 896, 1016, 1012, 1004, 988, 956, 895, 767, 511]
theorem reject_A02404_3_2 : NoEmbed (rowGraph rows_A02404_3_2) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_2) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_3 : List Nat := [770, 897, 1016, 1012, 1004, 988, 956, 894, 767, 511]
theorem reject_A02404_3_3 : NoEmbed (rowGraph rows_A02404_3_3) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_3) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_4 : List Nat := [896, 832, 1016, 1012, 1004, 988, 958, 893, 767, 511]
theorem reject_A02404_3_4 : NoEmbed (rowGraph rows_A02404_3_4) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_4) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_5 : List Nat := [770, 705, 1016, 1012, 1004, 988, 958, 894, 765, 511]
theorem reject_A02404_3_5 : NoEmbed (rowGraph rows_A02404_3_5) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_5) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_6 : List Nat := [896, 960, 1008, 1008, 1004, 988, 958, 895, 767, 511]
theorem reject_A02404_3_6 : NoEmbed (rowGraph rows_A02404_3_6) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_6) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_7 : List Nat := [770, 961, 1008, 1008, 1004, 988, 958, 894, 767, 511]
theorem reject_A02404_3_7 : NoEmbed (rowGraph rows_A02404_3_7) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_7) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_8 : List Nat := [898, 897, 1008, 1008, 1004, 988, 956, 895, 767, 511]
theorem reject_A02404_3_8 : NoEmbed (rowGraph rows_A02404_3_8) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_8) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_9 : List Nat := [898, 833, 1008, 1008, 1004, 988, 958, 893, 767, 511]
theorem reject_A02404_3_9 : NoEmbed (rowGraph rows_A02404_3_9) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_9) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_10 : List Nat := [960, 960, 992, 1008, 1000, 988, 959, 895, 767, 511]
theorem reject_A02404_3_10 : NoEmbed (rowGraph rows_A02404_3_10) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_10) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_11 : List Nat := [898, 961, 992, 1008, 1000, 988, 958, 895, 767, 511]
theorem reject_A02404_3_11 : NoEmbed (rowGraph rows_A02404_3_11) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_11) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_12 : List Nat := [962, 961, 960, 1008, 1000, 984, 959, 895, 767, 511]
theorem reject_A02404_3_12 : NoEmbed (rowGraph rows_A02404_3_12) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_12) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_13 : List Nat := [896, 960, 952, 1012, 1004, 988, 954, 895, 767, 511]
theorem reject_A02404_3_13 : NoEmbed (rowGraph rows_A02404_3_13) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_13) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_14 : List Nat := [770, 961, 952, 1012, 1004, 988, 954, 894, 767, 511]
theorem reject_A02404_3_14 : NoEmbed (rowGraph rows_A02404_3_14) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_14) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_15 : List Nat := [898, 897, 952, 1012, 1004, 988, 952, 895, 767, 511]
theorem reject_A02404_3_15 : NoEmbed (rowGraph rows_A02404_3_15) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_15) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_16 : List Nat := [898, 833, 952, 1012, 1004, 988, 954, 893, 767, 511]
theorem reject_A02404_3_16 : NoEmbed (rowGraph rows_A02404_3_16) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_16) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_17 : List Nat := [960, 960, 944, 1008, 1004, 988, 955, 895, 767, 511]
theorem reject_A02404_3_17 : NoEmbed (rowGraph rows_A02404_3_17) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_17) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_18 : List Nat := [898, 961, 944, 1008, 1004, 988, 954, 895, 767, 511]
theorem reject_A02404_3_18 : NoEmbed (rowGraph rows_A02404_3_18) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_18) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_19 : List Nat := [962, 961, 928, 1008, 1000, 988, 955, 895, 767, 511]
theorem reject_A02404_3_19 : NoEmbed (rowGraph rows_A02404_3_19) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_19) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_20 : List Nat := [896, 960, 888, 1012, 1004, 988, 958, 891, 767, 511]
theorem reject_A02404_3_20 : NoEmbed (rowGraph rows_A02404_3_20) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_20) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_21 : List Nat := [898, 897, 888, 1012, 1004, 988, 956, 891, 767, 511]
theorem reject_A02404_3_21 : NoEmbed (rowGraph rows_A02404_3_21) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_21) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_22 : List Nat := [898, 961, 880, 1008, 1004, 988, 958, 891, 767, 511]
theorem reject_A02404_3_22 : NoEmbed (rowGraph rows_A02404_3_22) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_22) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_23 : List Nat := [960, 960, 824, 1012, 1004, 988, 955, 891, 767, 511]
theorem reject_A02404_3_23 : NoEmbed (rowGraph rows_A02404_3_23) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_23) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_24 : List Nat := [898, 961, 824, 1012, 1004, 988, 954, 891, 767, 511]
theorem reject_A02404_3_24 : NoEmbed (rowGraph rows_A02404_3_24) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_24) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_25 : List Nat := [962, 961, 816, 1008, 1004, 988, 955, 891, 767, 511]
theorem reject_A02404_3_25 : NoEmbed (rowGraph rows_A02404_3_25) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_25) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_26 : List Nat := [770, 961, 760, 1012, 1004, 988, 958, 894, 763, 511]
theorem reject_A02404_3_26 : NoEmbed (rowGraph rows_A02404_3_26) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_26) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_27 : List Nat := [898, 833, 760, 1012, 1004, 988, 958, 893, 763, 511]
theorem reject_A02404_3_27 : NoEmbed (rowGraph rows_A02404_3_27) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_27) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_28 : List Nat := [898, 961, 632, 1012, 1004, 988, 958, 891, 763, 511]
theorem reject_A02404_3_28 : NoEmbed (rowGraph rows_A02404_3_28) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_28) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_29 : List Nat := [962, 961, 568, 1012, 1004, 988, 955, 891, 763, 511]
theorem reject_A02404_3_29 : NoEmbed (rowGraph rows_A02404_3_29) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_29) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_30 : List Nat := [962, 961, 992, 992, 992, 988, 959, 895, 767, 511]
theorem reject_A02404_3_30 : NoEmbed (rowGraph rows_A02404_3_30) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_30) Order10Common.target 5 1
    Order10Common.bound5 (s := {5,6,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_31 : List Nat := [962, 961, 824, 996, 996, 988, 955, 891, 767, 511]
theorem reject_A02404_3_31 : NoEmbed (rowGraph rows_A02404_3_31) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_31) Order10Common.target 5 1
    Order10Common.bound5 (s := {5,6,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_32 : List Nat := [962, 961, 992, 976, 1000, 980, 959, 895, 767, 511]
theorem reject_A02404_3_32 : NoEmbed (rowGraph rows_A02404_3_32) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_32) Order10Common.target 5 1
    Order10Common.bound5 (s := {4,6,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_33 : List Nat := [962, 961, 992, 944, 1000, 988, 951, 895, 767, 511]
theorem reject_A02404_3_33 : NoEmbed (rowGraph rows_A02404_3_33) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_33) Order10Common.target 5 1
    Order10Common.bound5 (s := {4,5,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_34 : List Nat := [960, 960, 952, 948, 1004, 988, 947, 895, 767, 511]
theorem reject_A02404_3_34 : NoEmbed (rowGraph rows_A02404_3_34) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_34) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_35 : List Nat := [898, 961, 952, 948, 1004, 988, 946, 895, 767, 511]
theorem reject_A02404_3_35 : NoEmbed (rowGraph rows_A02404_3_35) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_35) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_36 : List Nat := [962, 961, 944, 944, 1004, 988, 947, 895, 767, 511]
theorem reject_A02404_3_36 : NoEmbed (rowGraph rows_A02404_3_36) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_36) Order10Common.target 5 1
    Order10Common.bound5 (s := {4,5,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_37 : List Nat := [962, 961, 824, 948, 1004, 988, 947, 891, 767, 511]
theorem reject_A02404_3_37 : NoEmbed (rowGraph rows_A02404_3_37) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_37) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_38 : List Nat := [960, 960, 952, 884, 1004, 988, 955, 887, 767, 511]
theorem reject_A02404_3_38 : NoEmbed (rowGraph rows_A02404_3_38) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_38) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_39 : List Nat := [898, 961, 952, 884, 1004, 988, 954, 887, 767, 511]
theorem reject_A02404_3_39 : NoEmbed (rowGraph rows_A02404_3_39) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_39) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_40 : List Nat := [962, 961, 944, 880, 1004, 988, 955, 887, 767, 511]
theorem reject_A02404_3_40 : NoEmbed (rowGraph rows_A02404_3_40) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_40) Order10Common.target 5 1
    Order10Common.bound5 (s := {4,5,6,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_41 : List Nat := [898, 961, 888, 884, 1004, 988, 958, 883, 767, 511]
theorem reject_A02404_3_41 : NoEmbed (rowGraph rows_A02404_3_41) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_41) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_42 : List Nat := [898, 961, 888, 756, 1004, 988, 958, 891, 759, 511]
theorem reject_A02404_3_42 : NoEmbed (rowGraph rows_A02404_3_42) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_42) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,6,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_43 : List Nat := [962, 961, 824, 756, 1004, 988, 955, 891, 759, 511]
theorem reject_A02404_3_43 : NoEmbed (rowGraph rows_A02404_3_43) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_43) Order10Common.target 5 1
    Order10Common.bound5 (s := {4,5,6,7,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_44 : List Nat := [960, 960, 1008, 1008, 972, 972, 959, 895, 767, 511]
theorem reject_A02404_3_44 : NoEmbed (rowGraph rows_A02404_3_44) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_44) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,6,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_45 : List Nat := [898, 961, 1008, 1008, 972, 972, 958, 895, 767, 511]
theorem reject_A02404_3_45 : NoEmbed (rowGraph rows_A02404_3_45) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_45) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,6,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_46 : List Nat := [962, 961, 944, 1008, 972, 972, 955, 895, 767, 511]
theorem reject_A02404_3_46 : NoEmbed (rowGraph rows_A02404_3_46) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_46) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,6,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_47 : List Nat := [962, 961, 952, 948, 972, 972, 947, 895, 767, 511]
theorem reject_A02404_3_47 : NoEmbed (rowGraph rows_A02404_3_47) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_47) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_48 : List Nat := [962, 961, 952, 884, 972, 972, 955, 887, 767, 511]
theorem reject_A02404_3_48 : NoEmbed (rowGraph rows_A02404_3_48) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_48) Order10Common.target 4 3
    Order10Common.bound4 (s := {6,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_49 : List Nat := [960, 960, 1008, 1008, 940, 988, 943, 895, 767, 511]
theorem reject_A02404_3_49 : NoEmbed (rowGraph rows_A02404_3_49) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_49) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,5,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_50 : List Nat := [898, 961, 1008, 1008, 940, 988, 942, 895, 767, 511]
theorem reject_A02404_3_50 : NoEmbed (rowGraph rows_A02404_3_50) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_50) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,5,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_51 : List Nat := [962, 961, 944, 1008, 940, 988, 939, 895, 767, 511]
theorem reject_A02404_3_51 : NoEmbed (rowGraph rows_A02404_3_51) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_51) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,5,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_52 : List Nat := [962, 961, 952, 948, 940, 988, 931, 895, 767, 511]
theorem reject_A02404_3_52 : NoEmbed (rowGraph rows_A02404_3_52) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_52) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_53 : List Nat := [898, 961, 1008, 1008, 876, 988, 958, 879, 767, 511]
theorem reject_A02404_3_53 : NoEmbed (rowGraph rows_A02404_3_53) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_53) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,5,6,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_54 : List Nat := [962, 961, 944, 1008, 876, 988, 955, 879, 767, 511]
theorem reject_A02404_3_54 : NoEmbed (rowGraph rows_A02404_3_54) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_54) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,5,6,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_55 : List Nat := [962, 961, 952, 948, 876, 988, 947, 879, 767, 511]
theorem reject_A02404_3_55 : NoEmbed (rowGraph rows_A02404_3_55) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_55) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,5,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_57 : List Nat := [962, 961, 992, 1008, 1000, 924, 927, 895, 767, 511]
theorem reject_A02404_3_57 : NoEmbed (rowGraph rows_A02404_3_57) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_57) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_58 : List Nat := [896, 960, 1016, 1012, 1004, 988, 830, 831, 767, 511]
theorem reject_A02404_3_58 : NoEmbed (rowGraph rows_A02404_3_58) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_58) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_59 : List Nat := [770, 961, 1016, 1012, 1004, 988, 830, 830, 767, 511]
theorem reject_A02404_3_59 : NoEmbed (rowGraph rows_A02404_3_59) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_59) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_60 : List Nat := [898, 897, 1016, 1012, 1004, 988, 828, 831, 767, 511]
theorem reject_A02404_3_60 : NoEmbed (rowGraph rows_A02404_3_60) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_60) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_61 : List Nat := [898, 833, 1016, 1012, 1004, 988, 830, 829, 767, 511]
theorem reject_A02404_3_61 : NoEmbed (rowGraph rows_A02404_3_61) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_61) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_62 : List Nat := [960, 960, 1008, 1008, 1004, 988, 831, 831, 767, 511]
theorem reject_A02404_3_62 : NoEmbed (rowGraph rows_A02404_3_62) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_62) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_63 : List Nat := [898, 961, 1008, 1008, 1004, 988, 830, 831, 767, 511]
theorem reject_A02404_3_63 : NoEmbed (rowGraph rows_A02404_3_63) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_63) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_64 : List Nat := [962, 961, 992, 1008, 1000, 988, 831, 831, 767, 511]
theorem reject_A02404_3_64 : NoEmbed (rowGraph rows_A02404_3_64) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_64) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_65 : List Nat := [960, 960, 952, 1012, 1004, 988, 827, 831, 767, 511]
theorem reject_A02404_3_65 : NoEmbed (rowGraph rows_A02404_3_65) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_65) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_66 : List Nat := [898, 961, 952, 1012, 1004, 988, 826, 831, 767, 511]
theorem reject_A02404_3_66 : NoEmbed (rowGraph rows_A02404_3_66) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_66) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_67 : List Nat := [962, 961, 944, 1008, 1004, 988, 827, 831, 767, 511]
theorem reject_A02404_3_67 : NoEmbed (rowGraph rows_A02404_3_67) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_67) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_68 : List Nat := [898, 961, 888, 1012, 1004, 988, 830, 827, 767, 511]
theorem reject_A02404_3_68 : NoEmbed (rowGraph rows_A02404_3_68) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_68) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_69 : List Nat := [962, 961, 824, 1012, 1004, 988, 827, 827, 767, 511]
theorem reject_A02404_3_69 : NoEmbed (rowGraph rows_A02404_3_69) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_69) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_70 : List Nat := [962, 961, 952, 948, 1004, 988, 819, 831, 767, 511]
theorem reject_A02404_3_70 : NoEmbed (rowGraph rows_A02404_3_70) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_70) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_71 : List Nat := [962, 961, 952, 884, 1004, 988, 827, 823, 767, 511]
theorem reject_A02404_3_71 : NoEmbed (rowGraph rows_A02404_3_71) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_71) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_73 : List Nat := [962, 961, 1008, 1008, 940, 988, 815, 831, 767, 511]
theorem reject_A02404_3_73 : NoEmbed (rowGraph rows_A02404_3_73) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_73) Order10Common.target 5 1
    Order10Common.bound5 (s := {4,5,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_74 : List Nat := [770, 961, 1016, 1012, 1004, 988, 702, 894, 703, 511]
theorem reject_A02404_3_74 : NoEmbed (rowGraph rows_A02404_3_74) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_74) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_75 : List Nat := [898, 833, 1016, 1012, 1004, 988, 702, 893, 703, 511]
theorem reject_A02404_3_75 : NoEmbed (rowGraph rows_A02404_3_75) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_75) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_76 : List Nat := [898, 961, 888, 1012, 1004, 988, 702, 891, 703, 511]
theorem reject_A02404_3_76 : NoEmbed (rowGraph rows_A02404_3_76) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_76) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_77 : List Nat := [962, 961, 824, 1012, 1004, 988, 699, 891, 703, 511]
theorem reject_A02404_3_77 : NoEmbed (rowGraph rows_A02404_3_77) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_77) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,7,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_78 : List Nat := [962, 961, 952, 884, 1004, 988, 699, 887, 703, 511]
theorem reject_A02404_3_78 : NoEmbed (rowGraph rows_A02404_3_78) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_78) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_79 : List Nat := [960, 960, 1016, 1012, 1004, 988, 575, 831, 703, 511]
theorem reject_A02404_3_79 : NoEmbed (rowGraph rows_A02404_3_79) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_79) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_80 : List Nat := [898, 961, 1016, 1012, 1004, 988, 574, 831, 703, 511]
theorem reject_A02404_3_80 : NoEmbed (rowGraph rows_A02404_3_80) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_80) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_81 : List Nat := [450, 961, 1016, 1012, 1004, 988, 575, 831, 703, 510]
theorem reject_A02404_3_81 : NoEmbed (rowGraph rows_A02404_3_81) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_81) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_82 : List Nat := [962, 961, 1008, 1008, 1004, 988, 575, 831, 703, 511]
theorem reject_A02404_3_82 : NoEmbed (rowGraph rows_A02404_3_82) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_82) Order10Common.target 5 1
    Order10Common.bound5 (s := {4,5,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_83 : List Nat := [962, 961, 952, 1012, 1004, 988, 571, 831, 703, 511]
theorem reject_A02404_3_83 : NoEmbed (rowGraph rows_A02404_3_83) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_83) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_84 : List Nat := [962, 961, 504, 1012, 1004, 988, 575, 831, 703, 507]
theorem reject_A02404_3_84 : NoEmbed (rowGraph rows_A02404_3_84) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_84) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,7,8}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_85 : List Nat := [962, 961, 1016, 1012, 1004, 988, 63, 831, 703, 447]
theorem reject_A02404_3_85 : NoEmbed (rowGraph rows_A02404_3_85) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_85) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_86 : List Nat := [896, 960, 1016, 1012, 1004, 988, 958, 639, 639, 511]
theorem reject_A02404_3_86 : NoEmbed (rowGraph rows_A02404_3_86) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_86) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_87 : List Nat := [898, 897, 1016, 1012, 1004, 988, 956, 639, 639, 511]
theorem reject_A02404_3_87 : NoEmbed (rowGraph rows_A02404_3_87) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_87) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_88 : List Nat := [898, 961, 1008, 1008, 1004, 988, 958, 639, 639, 511]
theorem reject_A02404_3_88 : NoEmbed (rowGraph rows_A02404_3_88) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_88) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,4,5,6,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_89 : List Nat := [960, 960, 952, 1012, 1004, 988, 955, 639, 639, 511]
theorem reject_A02404_3_89 : NoEmbed (rowGraph rows_A02404_3_89) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_89) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_90 : List Nat := [898, 961, 952, 1012, 1004, 988, 954, 639, 639, 511]
theorem reject_A02404_3_90 : NoEmbed (rowGraph rows_A02404_3_90) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_90) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_91 : List Nat := [962, 961, 944, 1008, 1004, 988, 955, 639, 639, 511]
theorem reject_A02404_3_91 : NoEmbed (rowGraph rows_A02404_3_91) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_91) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_92 : List Nat := [898, 961, 888, 1012, 1004, 988, 958, 635, 639, 511]
theorem reject_A02404_3_92 : NoEmbed (rowGraph rows_A02404_3_92) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_92) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_93 : List Nat := [962, 961, 952, 948, 1004, 988, 947, 639, 639, 511]
theorem reject_A02404_3_93 : NoEmbed (rowGraph rows_A02404_3_93) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_93) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_95 : List Nat := [898, 961, 1016, 1012, 1004, 988, 830, 575, 639, 511]
theorem reject_A02404_3_95 : NoEmbed (rowGraph rows_A02404_3_95) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_95) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_96 : List Nat := [962, 961, 952, 1012, 1004, 988, 827, 575, 639, 511]
theorem reject_A02404_3_96 : NoEmbed (rowGraph rows_A02404_3_96) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_96) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_97 : List Nat := [962, 961, 1016, 1012, 1004, 988, 575, 575, 575, 511]
theorem reject_A02404_3_97 : NoEmbed (rowGraph rows_A02404_3_97) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_97) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,9}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_98 : List Nat := [962, 961, 1016, 1012, 1004, 988, 575, 319, 703, 383]
theorem reject_A02404_3_98 : NoEmbed (rowGraph rows_A02404_3_98) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_98) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,8}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_99 : List Nat := [770, 961, 1016, 1012, 1004, 988, 958, 894, 255, 255]
theorem reject_A02404_3_99 : NoEmbed (rowGraph rows_A02404_3_99) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_99) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_100 : List Nat := [898, 833, 1016, 1012, 1004, 988, 958, 893, 255, 255]
theorem reject_A02404_3_100 : NoEmbed (rowGraph rows_A02404_3_100) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_100) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_101 : List Nat := [898, 961, 888, 1012, 1004, 988, 958, 891, 255, 255]
theorem reject_A02404_3_101 : NoEmbed (rowGraph rows_A02404_3_101) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_101) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_102 : List Nat := [962, 961, 824, 1012, 1004, 988, 955, 891, 255, 255]
theorem reject_A02404_3_102 : NoEmbed (rowGraph rows_A02404_3_102) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_102) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_104 : List Nat := [960, 960, 1016, 1012, 1004, 988, 831, 831, 255, 255]
theorem reject_A02404_3_104 : NoEmbed (rowGraph rows_A02404_3_104) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_104) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_105 : List Nat := [898, 961, 1016, 1012, 1004, 988, 830, 831, 255, 255]
theorem reject_A02404_3_105 : NoEmbed (rowGraph rows_A02404_3_105) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_105) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,6}) (by decide +kernel) (by decide +kernel)
def rows_A02404_3_107 : List Nat := [962, 961, 952, 1012, 1004, 988, 827, 831, 255, 255]
theorem reject_A02404_3_107 : NoEmbed (rowGraph rows_A02404_3_107) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A02404_3_107) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,3,4,5,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_0_0 : List Nat := [966, 965, 963, 1008, 1000, 984, 959, 895, 767, 511]
theorem reject_A03304_0_0 : NoEmbed (rowGraph rows_A03304_0_0) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_0_0) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_1_0 : List Nat := [964, 964, 963, 1008, 1000, 984, 959, 895, 767, 511]
theorem reject_A03304_1_0 : NoEmbed (rowGraph rows_A03304_1_0) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_1_0) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,6,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A03304_1_1 : List Nat := [902, 965, 963, 1008, 1000, 984, 958, 895, 767, 511]
theorem reject_A03304_1_1 : NoEmbed (rowGraph rows_A03304_1_1) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_1_1) Order10Common.target 5 1
    Order10Common.bound5 (s := {1,2,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A03304_1_2 : List Nat := [966, 965, 963, 992, 992, 984, 959, 895, 767, 511]
theorem reject_A03304_1_2 : NoEmbed (rowGraph rows_A03304_1_2) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_1_2) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_1_3 : List Nat := [966, 965, 963, 944, 1000, 984, 951, 895, 767, 511]
theorem reject_A03304_1_3 : NoEmbed (rowGraph rows_A03304_1_3) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_1_3) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_1_4 : List Nat := [966, 965, 963, 1008, 1000, 984, 831, 831, 767, 511]
theorem reject_A03304_1_4 : NoEmbed (rowGraph rows_A03304_1_4) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_1_4) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_0 : List Nat := [960, 964, 962, 1008, 1000, 984, 959, 895, 767, 511]
theorem reject_A03304_2_0 : NoEmbed (rowGraph rows_A03304_2_0) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_0) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_1 : List Nat := [900, 964, 963, 1008, 1000, 984, 958, 895, 767, 511]
theorem reject_A03304_2_1 : NoEmbed (rowGraph rows_A03304_2_1) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_1) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_2 : List Nat := [774, 965, 963, 1008, 1000, 984, 958, 894, 767, 511]
theorem reject_A03304_2_2 : NoEmbed (rowGraph rows_A03304_2_2) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_2) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_3 : List Nat := [902, 901, 963, 1008, 1000, 984, 956, 895, 767, 511]
theorem reject_A03304_2_3 : NoEmbed (rowGraph rows_A03304_2_3) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_3) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_4 : List Nat := [902, 837, 963, 1008, 1000, 984, 958, 893, 767, 511]
theorem reject_A03304_2_4 : NoEmbed (rowGraph rows_A03304_2_4) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_4) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_5 : List Nat := [964, 964, 899, 1008, 1000, 984, 955, 895, 767, 511]
theorem reject_A03304_2_5 : NoEmbed (rowGraph rows_A03304_2_5) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_5) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_6 : List Nat := [964, 964, 963, 992, 992, 984, 959, 895, 767, 511]
theorem reject_A03304_2_6 : NoEmbed (rowGraph rows_A03304_2_6) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_6) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,6,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_7 : List Nat := [902, 965, 963, 992, 992, 984, 958, 895, 767, 511]
theorem reject_A03304_2_7 : NoEmbed (rowGraph rows_A03304_2_7) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_7) Order10Common.target 5 1
    Order10Common.bound5 (s := {1,2,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_8 : List Nat := [966, 965, 963, 960, 992, 976, 959, 895, 767, 511]
theorem reject_A03304_2_8 : NoEmbed (rowGraph rows_A03304_2_8) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_8) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_9 : List Nat := [964, 964, 963, 944, 1000, 984, 951, 895, 767, 511]
theorem reject_A03304_2_9 : NoEmbed (rowGraph rows_A03304_2_9) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_9) Order10Common.target 5 1
    Order10Common.bound5 (s := {2,6,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_10 : List Nat := [902, 965, 963, 944, 1000, 984, 950, 895, 767, 511]
theorem reject_A03304_2_10 : NoEmbed (rowGraph rows_A03304_2_10) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_10) Order10Common.target 5 1
    Order10Common.bound5 (s := {1,2,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_11 : List Nat := [966, 965, 963, 928, 992, 984, 951, 895, 767, 511]
theorem reject_A03304_2_11 : NoEmbed (rowGraph rows_A03304_2_11) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_11) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_12 : List Nat := [902, 965, 963, 880, 1000, 984, 958, 887, 767, 511]
theorem reject_A03304_2_12 : NoEmbed (rowGraph rows_A03304_2_12) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_12) Order10Common.target 5 1
    Order10Common.bound5 (s := {1,2,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_13 : List Nat := [966, 965, 963, 816, 1000, 984, 951, 887, 767, 511]
theorem reject_A03304_2_13 : NoEmbed (rowGraph rows_A03304_2_13) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_13) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_14 : List Nat := [966, 965, 963, 944, 936, 984, 935, 895, 767, 511]
theorem reject_A03304_2_14 : NoEmbed (rowGraph rows_A03304_2_14) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_14) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_15 : List Nat := [966, 965, 963, 944, 872, 984, 951, 879, 767, 511]
theorem reject_A03304_2_15 : NoEmbed (rowGraph rows_A03304_2_15) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_15) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_16 : List Nat := [966, 965, 963, 992, 992, 920, 927, 895, 767, 511]
theorem reject_A03304_2_16 : NoEmbed (rowGraph rows_A03304_2_16) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_16) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_17 : List Nat := [964, 964, 963, 1008, 1000, 984, 831, 831, 767, 511]
theorem reject_A03304_2_17 : NoEmbed (rowGraph rows_A03304_2_17) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_17) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_18 : List Nat := [902, 965, 963, 1008, 1000, 984, 830, 831, 767, 511]
theorem reject_A03304_2_18 : NoEmbed (rowGraph rows_A03304_2_18) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_18) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_19 : List Nat := [966, 965, 963, 992, 992, 984, 831, 831, 767, 511]
theorem reject_A03304_2_19 : NoEmbed (rowGraph rows_A03304_2_19) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_19) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_20 : List Nat := [966, 965, 963, 944, 1000, 984, 823, 831, 767, 511]
theorem reject_A03304_2_20 : NoEmbed (rowGraph rows_A03304_2_20) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_20) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_22 : List Nat := [902, 965, 963, 1008, 1000, 984, 958, 639, 639, 511]
theorem reject_A03304_2_22 : NoEmbed (rowGraph rows_A03304_2_22) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_22) Order10Common.target 5 1
    Order10Common.bound5 (s := {3,4,5,6,9}) (by decide +kernel) (by decide +kernel)
def rows_A03304_2_23 : List Nat := [966, 965, 963, 944, 1000, 984, 951, 639, 639, 511]
theorem reject_A03304_2_23 : NoEmbed (rowGraph rows_A03304_2_23) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A03304_2_23) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,6,9}) (by decide +kernel) (by decide +kernel)
def rows_A04114_0_0 : List Nat := [1006, 1005, 1003, 999, 960, 15, 927, 863, 735, 479]
theorem reject_A04114_0_0 : NoEmbed (rowGraph rows_A04114_0_0) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_0_0) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,6}) (by decide +kernel) (by decide +kernel)
def rows_A04114_1_0 : List Nat := [1004, 1004, 1003, 999, 960, 15, 927, 863, 735, 479]
theorem reject_A04114_1_0 : NoEmbed (rowGraph rows_A04114_1_0) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_1_0) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,2,3,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A04114_1_1 : List Nat := [974, 1005, 1003, 999, 960, 14, 927, 863, 735, 479]
theorem reject_A04114_1_1 : NoEmbed (rowGraph rows_A04114_1_1) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_1_1) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,6}) (by decide +kernel) (by decide +kernel)
def rows_A04114_1_2 : List Nat := [942, 1005, 1003, 999, 960, 15, 926, 863, 735, 479]
theorem reject_A04114_1_2 : NoEmbed (rowGraph rows_A04114_1_2) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_1_2) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,7}) (by decide +kernel) (by decide +kernel)
def rows_A04114_1_3 : List Nat := [1006, 1005, 1003, 999, 896, 15, 911, 863, 735, 479]
theorem reject_A04114_1_3 : NoEmbed (rowGraph rows_A04114_1_3) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_1_3) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,6}) (by decide +kernel) (by decide +kernel)
def rows_A04114_1_4 : List Nat := [1006, 1005, 1003, 999, 960, 15, 799, 799, 735, 479]
theorem reject_A04114_1_4 : NoEmbed (rowGraph rows_A04114_1_4) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_1_4) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,6}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_0 : List Nat := [1000, 1004, 1002, 999, 960, 15, 927, 863, 735, 479]
theorem reject_A04114_2_0 : NoEmbed (rowGraph rows_A04114_2_0) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_0) Order10Common.target 5 1
    Order10Common.bound5 (s := {1,2,3,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_1 : List Nat := [972, 1004, 1003, 999, 960, 14, 927, 863, 735, 479]
theorem reject_A04114_2_1 : NoEmbed (rowGraph rows_A04114_2_1) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_1) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,2,3,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_2 : List Nat := [940, 1004, 1003, 999, 960, 15, 926, 863, 735, 479]
theorem reject_A04114_2_2 : NoEmbed (rowGraph rows_A04114_2_2) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_2) Order10Common.target 5 1
    Order10Common.bound5 (s := {1,2,3,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_3 : List Nat := [910, 1005, 1003, 999, 960, 14, 926, 863, 735, 479]
theorem reject_A04114_2_3 : NoEmbed (rowGraph rows_A04114_2_3) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_3) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,7}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_4 : List Nat := [814, 1005, 1003, 999, 960, 15, 926, 862, 735, 479]
theorem reject_A04114_2_4 : NoEmbed (rowGraph rows_A04114_2_4) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_4) Order10Common.target 5 1
    Order10Common.bound5 (s := {1,2,3,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_5 : List Nat := [974, 973, 1003, 999, 960, 12, 927, 863, 735, 479]
theorem reject_A04114_2_5 : NoEmbed (rowGraph rows_A04114_2_5) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_5) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,6}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_6 : List Nat := [974, 941, 1003, 999, 960, 14, 925, 863, 735, 479]
theorem reject_A04114_2_6 : NoEmbed (rowGraph rows_A04114_2_6) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_6) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,7}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_7 : List Nat := [942, 941, 1003, 999, 960, 15, 924, 863, 735, 479]
theorem reject_A04114_2_7 : NoEmbed (rowGraph rows_A04114_2_7) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_7) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,7}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_8 : List Nat := [942, 877, 1003, 999, 960, 15, 926, 861, 735, 479]
theorem reject_A04114_2_8 : NoEmbed (rowGraph rows_A04114_2_8) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_8) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,2,3,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_9 : List Nat := [1004, 1004, 995, 995, 960, 15, 927, 863, 735, 479]
theorem reject_A04114_2_9 : NoEmbed (rowGraph rows_A04114_2_9) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_9) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,6,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_10 : List Nat := [1004, 1004, 971, 999, 960, 11, 927, 863, 735, 479]
theorem reject_A04114_2_10 : NoEmbed (rowGraph rows_A04114_2_10) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_10) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,2,3,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_11 : List Nat := [1004, 1004, 939, 999, 960, 15, 923, 863, 735, 479]
theorem reject_A04114_2_11 : NoEmbed (rowGraph rows_A04114_2_11) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_11) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,3,7,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_12 : List Nat := [1004, 1004, 1003, 999, 896, 15, 911, 863, 735, 479]
theorem reject_A04114_2_12 : NoEmbed (rowGraph rows_A04114_2_12) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_12) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,2,3,6,7}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_13 : List Nat := [974, 1005, 1003, 999, 896, 14, 911, 863, 735, 479]
theorem reject_A04114_2_13 : NoEmbed (rowGraph rows_A04114_2_13) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_13) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,6}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_14 : List Nat := [942, 1005, 1003, 999, 896, 15, 910, 863, 735, 479]
theorem reject_A04114_2_14 : NoEmbed (rowGraph rows_A04114_2_14) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_14) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,7}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_15 : List Nat := [942, 1005, 1003, 999, 832, 15, 926, 847, 735, 479]
theorem reject_A04114_2_15 : NoEmbed (rowGraph rows_A04114_2_15) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_15) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,7}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_16 : List Nat := [1006, 1005, 1003, 999, 768, 15, 911, 847, 735, 479]
theorem reject_A04114_2_16 : NoEmbed (rowGraph rows_A04114_2_16) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_16) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,6}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_17 : List Nat := [1004, 1004, 1003, 999, 960, 15, 799, 799, 735, 479]
theorem reject_A04114_2_17 : NoEmbed (rowGraph rows_A04114_2_17) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_17) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,2,3,8,9}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_18 : List Nat := [974, 1005, 1003, 999, 960, 14, 799, 799, 735, 479]
theorem reject_A04114_2_18 : NoEmbed (rowGraph rows_A04114_2_18) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_18) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,6}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_19 : List Nat := [942, 1005, 1003, 999, 960, 15, 798, 799, 735, 479]
theorem reject_A04114_2_19 : NoEmbed (rowGraph rows_A04114_2_19) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_19) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,7}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_20 : List Nat := [1006, 1005, 1003, 999, 896, 15, 783, 799, 735, 479]
theorem reject_A04114_2_20 : NoEmbed (rowGraph rows_A04114_2_20) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_20) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,6}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_21 : List Nat := [1006, 1005, 1003, 999, 960, 15, 543, 799, 671, 479]
theorem reject_A04114_2_21 : NoEmbed (rowGraph rows_A04114_2_21) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_21) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,7}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_22 : List Nat := [942, 1005, 1003, 999, 960, 15, 926, 607, 607, 479]
theorem reject_A04114_2_22 : NoEmbed (rowGraph rows_A04114_2_22) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_22) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,9}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_23 : List Nat := [1006, 1005, 1003, 999, 896, 15, 911, 607, 607, 479]
theorem reject_A04114_2_23 : NoEmbed (rowGraph rows_A04114_2_23) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_23) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,6}) (by decide +kernel) (by decide +kernel)
def rows_A04114_2_24 : List Nat := [1006, 1005, 1003, 999, 960, 15, 799, 799, 223, 223]
theorem reject_A04114_2_24 : NoEmbed (rowGraph rows_A04114_2_24) Order10Common.target := by
  exact no_embedding_common (rowGraph rows_A04114_2_24) Order10Common.target 5 1
    Order10Common.bound5 (s := {0,1,2,3,6}) (by decide +kernel) (by decide +kernel)
end Order10Leaves

-- all200 representative adapters
namespace Order10Leaves
def bad_A02404_0_0 := bad_of_rows (Order10Orbit.A02404.graph 0 0) (Order10Orbit.A02404.sourceRows 0 0)
  (Order10Orbit.A02404.graph_adj_iff 0 0 (by decide +kernel) (by decide +kernel))
  rows_A02404_0_0 (by decide +kernel) reject_A02404_0_0
def bad_A02404_1_0 := bad_of_rows (Order10Orbit.A02404.graph 1 0) (Order10Orbit.A02404.sourceRows 1 0)
  (Order10Orbit.A02404.graph_adj_iff 1 0 (by decide +kernel) (by decide +kernel))
  rows_A02404_1_0 (by decide +kernel) reject_A02404_1_0
def bad_A02404_1_1 := bad_of_rows (Order10Orbit.A02404.graph 1 1) (Order10Orbit.A02404.sourceRows 1 1)
  (Order10Orbit.A02404.graph_adj_iff 1 1 (by decide +kernel) (by decide +kernel))
  rows_A02404_1_1 (by decide +kernel) reject_A02404_1_1
def bad_A02404_1_2 := bad_of_rows (Order10Orbit.A02404.graph 1 2) (Order10Orbit.A02404.sourceRows 1 2)
  (Order10Orbit.A02404.graph_adj_iff 1 2 (by decide +kernel) (by decide +kernel))
  rows_A02404_1_2 (by decide +kernel) reject_A02404_1_2
def bad_A02404_1_3 := bad_of_rows (Order10Orbit.A02404.graph 1 3) (Order10Orbit.A02404.sourceRows 1 3)
  (Order10Orbit.A02404.graph_adj_iff 1 3 (by decide +kernel) (by decide +kernel))
  rows_A02404_1_3 (by decide +kernel) reject_A02404_1_3
def bad_A02404_1_4 := bad_of_rows (Order10Orbit.A02404.graph 1 4) (Order10Orbit.A02404.sourceRows 1 4)
  (Order10Orbit.A02404.graph_adj_iff 1 4 (by decide +kernel) (by decide +kernel))
  rows_A02404_1_4 (by decide +kernel) reject_A02404_1_4
def bad_A02404_2_0 := bad_of_rows (Order10Orbit.A02404.graph 2 0) (Order10Orbit.A02404.sourceRows 2 0)
  (Order10Orbit.A02404.graph_adj_iff 2 0 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_0 (by decide +kernel) reject_A02404_2_0
def bad_A02404_2_1 := bad_of_rows (Order10Orbit.A02404.graph 2 1) (Order10Orbit.A02404.sourceRows 2 1)
  (Order10Orbit.A02404.graph_adj_iff 2 1 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_1 (by decide +kernel) reject_A02404_2_1
def bad_A02404_2_2 := bad_of_rows (Order10Orbit.A02404.graph 2 2) (Order10Orbit.A02404.sourceRows 2 2)
  (Order10Orbit.A02404.graph_adj_iff 2 2 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_2 (by decide +kernel) reject_A02404_2_2
def bad_A02404_2_3 := bad_of_rows (Order10Orbit.A02404.graph 2 3) (Order10Orbit.A02404.sourceRows 2 3)
  (Order10Orbit.A02404.graph_adj_iff 2 3 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_3 (by decide +kernel) reject_A02404_2_3
def bad_A02404_2_4 := bad_of_rows (Order10Orbit.A02404.graph 2 4) (Order10Orbit.A02404.sourceRows 2 4)
  (Order10Orbit.A02404.graph_adj_iff 2 4 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_4 (by decide +kernel) reject_A02404_2_4
def bad_A02404_2_5 := bad_of_rows (Order10Orbit.A02404.graph 2 5) (Order10Orbit.A02404.sourceRows 2 5)
  (Order10Orbit.A02404.graph_adj_iff 2 5 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_5 (by decide +kernel) reject_A02404_2_5
def bad_A02404_2_6 := bad_of_rows (Order10Orbit.A02404.graph 2 6) (Order10Orbit.A02404.sourceRows 2 6)
  (Order10Orbit.A02404.graph_adj_iff 2 6 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_6 (by decide +kernel) reject_A02404_2_6
def bad_A02404_2_7 := bad_of_rows (Order10Orbit.A02404.graph 2 7) (Order10Orbit.A02404.sourceRows 2 7)
  (Order10Orbit.A02404.graph_adj_iff 2 7 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_7 (by decide +kernel) reject_A02404_2_7
def bad_A02404_2_8 := bad_of_rows (Order10Orbit.A02404.graph 2 8) (Order10Orbit.A02404.sourceRows 2 8)
  (Order10Orbit.A02404.graph_adj_iff 2 8 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_8 (by decide +kernel) reject_A02404_2_8
def bad_A02404_2_9 := bad_of_rows (Order10Orbit.A02404.graph 2 9) (Order10Orbit.A02404.sourceRows 2 9)
  (Order10Orbit.A02404.graph_adj_iff 2 9 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_9 (by decide +kernel) reject_A02404_2_9
def bad_A02404_2_10 := bad_of_rows (Order10Orbit.A02404.graph 2 10) (Order10Orbit.A02404.sourceRows 2 10)
  (Order10Orbit.A02404.graph_adj_iff 2 10 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_10 (by decide +kernel) reject_A02404_2_10
def bad_A02404_2_11 := bad_of_rows (Order10Orbit.A02404.graph 2 11) (Order10Orbit.A02404.sourceRows 2 11)
  (Order10Orbit.A02404.graph_adj_iff 2 11 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_11 (by decide +kernel) reject_A02404_2_11
def bad_A02404_2_12 := bad_of_rows (Order10Orbit.A02404.graph 2 12) (Order10Orbit.A02404.sourceRows 2 12)
  (Order10Orbit.A02404.graph_adj_iff 2 12 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_12 (by decide +kernel) reject_A02404_2_12
def bad_A02404_2_13 := bad_of_rows (Order10Orbit.A02404.graph 2 13) (Order10Orbit.A02404.sourceRows 2 13)
  (Order10Orbit.A02404.graph_adj_iff 2 13 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_13 (by decide +kernel) reject_A02404_2_13
def bad_A02404_2_14 := bad_of_rows (Order10Orbit.A02404.graph 2 14) (Order10Orbit.A02404.sourceRows 2 14)
  (Order10Orbit.A02404.graph_adj_iff 2 14 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_14 (by decide +kernel) reject_A02404_2_14
def bad_A02404_2_15 := bad_of_rows (Order10Orbit.A02404.graph 2 15) (Order10Orbit.A02404.sourceRows 2 15)
  (Order10Orbit.A02404.graph_adj_iff 2 15 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_15 (by decide +kernel) reject_A02404_2_15
def bad_A02404_2_16 := bad_of_rows (Order10Orbit.A02404.graph 2 16) (Order10Orbit.A02404.sourceRows 2 16)
  (Order10Orbit.A02404.graph_adj_iff 2 16 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_16 (by decide +kernel) reject_A02404_2_16
def bad_A02404_2_17 := bad_of_rows (Order10Orbit.A02404.graph 2 17) (Order10Orbit.A02404.sourceRows 2 17)
  (Order10Orbit.A02404.graph_adj_iff 2 17 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_17 (by decide +kernel) reject_A02404_2_17
def bad_A02404_2_18 := bad_of_rows (Order10Orbit.A02404.graph 2 18) (Order10Orbit.A02404.sourceRows 2 18)
  (Order10Orbit.A02404.graph_adj_iff 2 18 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_18 (by decide +kernel) reject_A02404_2_18
def bad_A02404_2_19 := bad_of_rows (Order10Orbit.A02404.graph 2 19) (Order10Orbit.A02404.sourceRows 2 19)
  (Order10Orbit.A02404.graph_adj_iff 2 19 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_19 (by decide +kernel) reject_A02404_2_19
def bad_A02404_2_20 := bad_of_rows (Order10Orbit.A02404.graph 2 20) (Order10Orbit.A02404.sourceRows 2 20)
  (Order10Orbit.A02404.graph_adj_iff 2 20 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_20 (by decide +kernel) reject_A02404_2_20
def bad_A02404_2_21 := bad_of_rows (Order10Orbit.A02404.graph 2 21) (Order10Orbit.A02404.sourceRows 2 21)
  (Order10Orbit.A02404.graph_adj_iff 2 21 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_21 (by decide +kernel) reject_A02404_2_21
def bad_A02404_2_22 := bad_of_rows (Order10Orbit.A02404.graph 2 22) (Order10Orbit.A02404.sourceRows 2 22)
  (Order10Orbit.A02404.graph_adj_iff 2 22 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_22 (by decide +kernel) reject_A02404_2_22
def bad_A02404_2_23 := bad_of_rows (Order10Orbit.A02404.graph 2 23) (Order10Orbit.A02404.sourceRows 2 23)
  (Order10Orbit.A02404.graph_adj_iff 2 23 (by decide +kernel) (by decide +kernel))
  rows_A02404_2_23 (by decide +kernel) reject_A02404_2_23
def bad_A02404_3_0 := bad_of_rows (Order10Orbit.A02404.graph 3 0) (Order10Orbit.A02404.sourceRows 3 0)
  (Order10Orbit.A02404.graph_adj_iff 3 0 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_0 (by decide +kernel) reject_A02404_3_0
def bad_A02404_3_1 := bad_of_rows (Order10Orbit.A02404.graph 3 1) (Order10Orbit.A02404.sourceRows 3 1)
  (Order10Orbit.A02404.graph_adj_iff 3 1 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_1 (by decide +kernel) reject_A02404_3_1
def bad_A02404_3_2 := bad_of_rows (Order10Orbit.A02404.graph 3 2) (Order10Orbit.A02404.sourceRows 3 2)
  (Order10Orbit.A02404.graph_adj_iff 3 2 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_2 (by decide +kernel) reject_A02404_3_2
def bad_A02404_3_3 := bad_of_rows (Order10Orbit.A02404.graph 3 3) (Order10Orbit.A02404.sourceRows 3 3)
  (Order10Orbit.A02404.graph_adj_iff 3 3 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_3 (by decide +kernel) reject_A02404_3_3
def bad_A02404_3_4 := bad_of_rows (Order10Orbit.A02404.graph 3 4) (Order10Orbit.A02404.sourceRows 3 4)
  (Order10Orbit.A02404.graph_adj_iff 3 4 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_4 (by decide +kernel) reject_A02404_3_4
def bad_A02404_3_5 := bad_of_rows (Order10Orbit.A02404.graph 3 5) (Order10Orbit.A02404.sourceRows 3 5)
  (Order10Orbit.A02404.graph_adj_iff 3 5 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_5 (by decide +kernel) reject_A02404_3_5
def bad_A02404_3_6 := bad_of_rows (Order10Orbit.A02404.graph 3 6) (Order10Orbit.A02404.sourceRows 3 6)
  (Order10Orbit.A02404.graph_adj_iff 3 6 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_6 (by decide +kernel) reject_A02404_3_6
def bad_A02404_3_7 := bad_of_rows (Order10Orbit.A02404.graph 3 7) (Order10Orbit.A02404.sourceRows 3 7)
  (Order10Orbit.A02404.graph_adj_iff 3 7 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_7 (by decide +kernel) reject_A02404_3_7
def bad_A02404_3_8 := bad_of_rows (Order10Orbit.A02404.graph 3 8) (Order10Orbit.A02404.sourceRows 3 8)
  (Order10Orbit.A02404.graph_adj_iff 3 8 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_8 (by decide +kernel) reject_A02404_3_8
def bad_A02404_3_9 := bad_of_rows (Order10Orbit.A02404.graph 3 9) (Order10Orbit.A02404.sourceRows 3 9)
  (Order10Orbit.A02404.graph_adj_iff 3 9 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_9 (by decide +kernel) reject_A02404_3_9
def bad_A02404_3_10 := bad_of_rows (Order10Orbit.A02404.graph 3 10) (Order10Orbit.A02404.sourceRows 3 10)
  (Order10Orbit.A02404.graph_adj_iff 3 10 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_10 (by decide +kernel) reject_A02404_3_10
def bad_A02404_3_11 := bad_of_rows (Order10Orbit.A02404.graph 3 11) (Order10Orbit.A02404.sourceRows 3 11)
  (Order10Orbit.A02404.graph_adj_iff 3 11 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_11 (by decide +kernel) reject_A02404_3_11
def bad_A02404_3_12 := bad_of_rows (Order10Orbit.A02404.graph 3 12) (Order10Orbit.A02404.sourceRows 3 12)
  (Order10Orbit.A02404.graph_adj_iff 3 12 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_12 (by decide +kernel) reject_A02404_3_12
def bad_A02404_3_13 := bad_of_rows (Order10Orbit.A02404.graph 3 13) (Order10Orbit.A02404.sourceRows 3 13)
  (Order10Orbit.A02404.graph_adj_iff 3 13 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_13 (by decide +kernel) reject_A02404_3_13
def bad_A02404_3_14 := bad_of_rows (Order10Orbit.A02404.graph 3 14) (Order10Orbit.A02404.sourceRows 3 14)
  (Order10Orbit.A02404.graph_adj_iff 3 14 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_14 (by decide +kernel) reject_A02404_3_14
def bad_A02404_3_15 := bad_of_rows (Order10Orbit.A02404.graph 3 15) (Order10Orbit.A02404.sourceRows 3 15)
  (Order10Orbit.A02404.graph_adj_iff 3 15 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_15 (by decide +kernel) reject_A02404_3_15
def bad_A02404_3_16 := bad_of_rows (Order10Orbit.A02404.graph 3 16) (Order10Orbit.A02404.sourceRows 3 16)
  (Order10Orbit.A02404.graph_adj_iff 3 16 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_16 (by decide +kernel) reject_A02404_3_16
def bad_A02404_3_17 := bad_of_rows (Order10Orbit.A02404.graph 3 17) (Order10Orbit.A02404.sourceRows 3 17)
  (Order10Orbit.A02404.graph_adj_iff 3 17 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_17 (by decide +kernel) reject_A02404_3_17
def bad_A02404_3_18 := bad_of_rows (Order10Orbit.A02404.graph 3 18) (Order10Orbit.A02404.sourceRows 3 18)
  (Order10Orbit.A02404.graph_adj_iff 3 18 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_18 (by decide +kernel) reject_A02404_3_18
def bad_A02404_3_19 := bad_of_rows (Order10Orbit.A02404.graph 3 19) (Order10Orbit.A02404.sourceRows 3 19)
  (Order10Orbit.A02404.graph_adj_iff 3 19 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_19 (by decide +kernel) reject_A02404_3_19
def bad_A02404_3_20 := bad_of_rows (Order10Orbit.A02404.graph 3 20) (Order10Orbit.A02404.sourceRows 3 20)
  (Order10Orbit.A02404.graph_adj_iff 3 20 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_20 (by decide +kernel) reject_A02404_3_20
def bad_A02404_3_21 := bad_of_rows (Order10Orbit.A02404.graph 3 21) (Order10Orbit.A02404.sourceRows 3 21)
  (Order10Orbit.A02404.graph_adj_iff 3 21 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_21 (by decide +kernel) reject_A02404_3_21
def bad_A02404_3_22 := bad_of_rows (Order10Orbit.A02404.graph 3 22) (Order10Orbit.A02404.sourceRows 3 22)
  (Order10Orbit.A02404.graph_adj_iff 3 22 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_22 (by decide +kernel) reject_A02404_3_22
def bad_A02404_3_23 := bad_of_rows (Order10Orbit.A02404.graph 3 23) (Order10Orbit.A02404.sourceRows 3 23)
  (Order10Orbit.A02404.graph_adj_iff 3 23 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_23 (by decide +kernel) reject_A02404_3_23
def bad_A02404_3_24 := bad_of_rows (Order10Orbit.A02404.graph 3 24) (Order10Orbit.A02404.sourceRows 3 24)
  (Order10Orbit.A02404.graph_adj_iff 3 24 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_24 (by decide +kernel) reject_A02404_3_24
def bad_A02404_3_25 := bad_of_rows (Order10Orbit.A02404.graph 3 25) (Order10Orbit.A02404.sourceRows 3 25)
  (Order10Orbit.A02404.graph_adj_iff 3 25 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_25 (by decide +kernel) reject_A02404_3_25
def bad_A02404_3_26 := bad_of_rows (Order10Orbit.A02404.graph 3 26) (Order10Orbit.A02404.sourceRows 3 26)
  (Order10Orbit.A02404.graph_adj_iff 3 26 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_26 (by decide +kernel) reject_A02404_3_26
def bad_A02404_3_27 := bad_of_rows (Order10Orbit.A02404.graph 3 27) (Order10Orbit.A02404.sourceRows 3 27)
  (Order10Orbit.A02404.graph_adj_iff 3 27 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_27 (by decide +kernel) reject_A02404_3_27
def bad_A02404_3_28 := bad_of_rows (Order10Orbit.A02404.graph 3 28) (Order10Orbit.A02404.sourceRows 3 28)
  (Order10Orbit.A02404.graph_adj_iff 3 28 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_28 (by decide +kernel) reject_A02404_3_28
def bad_A02404_3_29 := bad_of_rows (Order10Orbit.A02404.graph 3 29) (Order10Orbit.A02404.sourceRows 3 29)
  (Order10Orbit.A02404.graph_adj_iff 3 29 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_29 (by decide +kernel) reject_A02404_3_29
def bad_A02404_3_30 := bad_of_rows (Order10Orbit.A02404.graph 3 30) (Order10Orbit.A02404.sourceRows 3 30)
  (Order10Orbit.A02404.graph_adj_iff 3 30 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_30 (by decide +kernel) reject_A02404_3_30
def bad_A02404_3_31 := bad_of_rows (Order10Orbit.A02404.graph 3 31) (Order10Orbit.A02404.sourceRows 3 31)
  (Order10Orbit.A02404.graph_adj_iff 3 31 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_31 (by decide +kernel) reject_A02404_3_31
def bad_A02404_3_32 := bad_of_rows (Order10Orbit.A02404.graph 3 32) (Order10Orbit.A02404.sourceRows 3 32)
  (Order10Orbit.A02404.graph_adj_iff 3 32 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_32 (by decide +kernel) reject_A02404_3_32
def bad_A02404_3_33 := bad_of_rows (Order10Orbit.A02404.graph 3 33) (Order10Orbit.A02404.sourceRows 3 33)
  (Order10Orbit.A02404.graph_adj_iff 3 33 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_33 (by decide +kernel) reject_A02404_3_33
def bad_A02404_3_34 := bad_of_rows (Order10Orbit.A02404.graph 3 34) (Order10Orbit.A02404.sourceRows 3 34)
  (Order10Orbit.A02404.graph_adj_iff 3 34 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_34 (by decide +kernel) reject_A02404_3_34
def bad_A02404_3_35 := bad_of_rows (Order10Orbit.A02404.graph 3 35) (Order10Orbit.A02404.sourceRows 3 35)
  (Order10Orbit.A02404.graph_adj_iff 3 35 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_35 (by decide +kernel) reject_A02404_3_35
def bad_A02404_3_36 := bad_of_rows (Order10Orbit.A02404.graph 3 36) (Order10Orbit.A02404.sourceRows 3 36)
  (Order10Orbit.A02404.graph_adj_iff 3 36 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_36 (by decide +kernel) reject_A02404_3_36
def bad_A02404_3_37 := bad_of_rows (Order10Orbit.A02404.graph 3 37) (Order10Orbit.A02404.sourceRows 3 37)
  (Order10Orbit.A02404.graph_adj_iff 3 37 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_37 (by decide +kernel) reject_A02404_3_37
def bad_A02404_3_38 := bad_of_rows (Order10Orbit.A02404.graph 3 38) (Order10Orbit.A02404.sourceRows 3 38)
  (Order10Orbit.A02404.graph_adj_iff 3 38 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_38 (by decide +kernel) reject_A02404_3_38
def bad_A02404_3_39 := bad_of_rows (Order10Orbit.A02404.graph 3 39) (Order10Orbit.A02404.sourceRows 3 39)
  (Order10Orbit.A02404.graph_adj_iff 3 39 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_39 (by decide +kernel) reject_A02404_3_39
def bad_A02404_3_40 := bad_of_rows (Order10Orbit.A02404.graph 3 40) (Order10Orbit.A02404.sourceRows 3 40)
  (Order10Orbit.A02404.graph_adj_iff 3 40 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_40 (by decide +kernel) reject_A02404_3_40
def bad_A02404_3_41 := bad_of_rows (Order10Orbit.A02404.graph 3 41) (Order10Orbit.A02404.sourceRows 3 41)
  (Order10Orbit.A02404.graph_adj_iff 3 41 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_41 (by decide +kernel) reject_A02404_3_41
def bad_A02404_3_42 := bad_of_rows (Order10Orbit.A02404.graph 3 42) (Order10Orbit.A02404.sourceRows 3 42)
  (Order10Orbit.A02404.graph_adj_iff 3 42 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_42 (by decide +kernel) reject_A02404_3_42
def bad_A02404_3_43 := bad_of_rows (Order10Orbit.A02404.graph 3 43) (Order10Orbit.A02404.sourceRows 3 43)
  (Order10Orbit.A02404.graph_adj_iff 3 43 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_43 (by decide +kernel) reject_A02404_3_43
def bad_A02404_3_44 := bad_of_rows (Order10Orbit.A02404.graph 3 44) (Order10Orbit.A02404.sourceRows 3 44)
  (Order10Orbit.A02404.graph_adj_iff 3 44 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_44 (by decide +kernel) reject_A02404_3_44
def bad_A02404_3_45 := bad_of_rows (Order10Orbit.A02404.graph 3 45) (Order10Orbit.A02404.sourceRows 3 45)
  (Order10Orbit.A02404.graph_adj_iff 3 45 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_45 (by decide +kernel) reject_A02404_3_45
def bad_A02404_3_46 := bad_of_rows (Order10Orbit.A02404.graph 3 46) (Order10Orbit.A02404.sourceRows 3 46)
  (Order10Orbit.A02404.graph_adj_iff 3 46 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_46 (by decide +kernel) reject_A02404_3_46
def bad_A02404_3_47 := bad_of_rows (Order10Orbit.A02404.graph 3 47) (Order10Orbit.A02404.sourceRows 3 47)
  (Order10Orbit.A02404.graph_adj_iff 3 47 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_47 (by decide +kernel) reject_A02404_3_47
def bad_A02404_3_48 := bad_of_rows (Order10Orbit.A02404.graph 3 48) (Order10Orbit.A02404.sourceRows 3 48)
  (Order10Orbit.A02404.graph_adj_iff 3 48 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_48 (by decide +kernel) reject_A02404_3_48
def bad_A02404_3_49 := bad_of_rows (Order10Orbit.A02404.graph 3 49) (Order10Orbit.A02404.sourceRows 3 49)
  (Order10Orbit.A02404.graph_adj_iff 3 49 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_49 (by decide +kernel) reject_A02404_3_49
def bad_A02404_3_50 := bad_of_rows (Order10Orbit.A02404.graph 3 50) (Order10Orbit.A02404.sourceRows 3 50)
  (Order10Orbit.A02404.graph_adj_iff 3 50 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_50 (by decide +kernel) reject_A02404_3_50
def bad_A02404_3_51 := bad_of_rows (Order10Orbit.A02404.graph 3 51) (Order10Orbit.A02404.sourceRows 3 51)
  (Order10Orbit.A02404.graph_adj_iff 3 51 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_51 (by decide +kernel) reject_A02404_3_51
def bad_A02404_3_52 := bad_of_rows (Order10Orbit.A02404.graph 3 52) (Order10Orbit.A02404.sourceRows 3 52)
  (Order10Orbit.A02404.graph_adj_iff 3 52 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_52 (by decide +kernel) reject_A02404_3_52
def bad_A02404_3_53 := bad_of_rows (Order10Orbit.A02404.graph 3 53) (Order10Orbit.A02404.sourceRows 3 53)
  (Order10Orbit.A02404.graph_adj_iff 3 53 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_53 (by decide +kernel) reject_A02404_3_53
def bad_A02404_3_54 := bad_of_rows (Order10Orbit.A02404.graph 3 54) (Order10Orbit.A02404.sourceRows 3 54)
  (Order10Orbit.A02404.graph_adj_iff 3 54 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_54 (by decide +kernel) reject_A02404_3_54
def bad_A02404_3_55 := bad_of_rows (Order10Orbit.A02404.graph 3 55) (Order10Orbit.A02404.sourceRows 3 55)
  (Order10Orbit.A02404.graph_adj_iff 3 55 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_55 (by decide +kernel) reject_A02404_3_55
theorem bad_A02404_3_56 (h : NoEmbed Order10Search56.sourceGraph Order10Search56.targetGraph) : ∃ i : Fin 2, ¬ ∃ f : Fin 10 → Fin 19, Function.Injective f ∧
      ∀ u v, (Order10Orbit.A02404.graph 3 56).Adj u v → (Order10Common.targets i).Adj (f u) (f v) := by
  have hr : ∀ u : Fin 10, Order10Search56.source u.val = Order10Orbit.A02404.sourceRows 3 56 u.val := by decide +kernel
  have hg : Order10Search56.sourceGraph = Order10Orbit.A02404.graph 3 56 := by
    ext u v
    rw [Order10Orbit.A02404.graph_adj_iff 3 56 (by decide +kernel) (by decide +kernel) u v]
    change (Order10Search56.source u.val).testBit v.val = true ↔ (Order10Orbit.A02404.sourceRows 3 56 u.val).testBit v.val = true
    rw [hr u]
  have ht : Order10Common.targetOther = Order10Search56.targetGraph := by ext u v; rfl
  apply noEmbed_as_bad (Order10Orbit.A02404.graph 3 56) 1
  change NoEmbed (Order10Orbit.A02404.graph 3 56) Order10Common.targetOther
  rw [← hg, ht]
  exact h
def bad_A02404_3_57 := bad_of_rows (Order10Orbit.A02404.graph 3 57) (Order10Orbit.A02404.sourceRows 3 57)
  (Order10Orbit.A02404.graph_adj_iff 3 57 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_57 (by decide +kernel) reject_A02404_3_57
def bad_A02404_3_58 := bad_of_rows (Order10Orbit.A02404.graph 3 58) (Order10Orbit.A02404.sourceRows 3 58)
  (Order10Orbit.A02404.graph_adj_iff 3 58 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_58 (by decide +kernel) reject_A02404_3_58
def bad_A02404_3_59 := bad_of_rows (Order10Orbit.A02404.graph 3 59) (Order10Orbit.A02404.sourceRows 3 59)
  (Order10Orbit.A02404.graph_adj_iff 3 59 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_59 (by decide +kernel) reject_A02404_3_59
def bad_A02404_3_60 := bad_of_rows (Order10Orbit.A02404.graph 3 60) (Order10Orbit.A02404.sourceRows 3 60)
  (Order10Orbit.A02404.graph_adj_iff 3 60 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_60 (by decide +kernel) reject_A02404_3_60
def bad_A02404_3_61 := bad_of_rows (Order10Orbit.A02404.graph 3 61) (Order10Orbit.A02404.sourceRows 3 61)
  (Order10Orbit.A02404.graph_adj_iff 3 61 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_61 (by decide +kernel) reject_A02404_3_61
def bad_A02404_3_62 := bad_of_rows (Order10Orbit.A02404.graph 3 62) (Order10Orbit.A02404.sourceRows 3 62)
  (Order10Orbit.A02404.graph_adj_iff 3 62 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_62 (by decide +kernel) reject_A02404_3_62
def bad_A02404_3_63 := bad_of_rows (Order10Orbit.A02404.graph 3 63) (Order10Orbit.A02404.sourceRows 3 63)
  (Order10Orbit.A02404.graph_adj_iff 3 63 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_63 (by decide +kernel) reject_A02404_3_63
def bad_A02404_3_64 := bad_of_rows (Order10Orbit.A02404.graph 3 64) (Order10Orbit.A02404.sourceRows 3 64)
  (Order10Orbit.A02404.graph_adj_iff 3 64 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_64 (by decide +kernel) reject_A02404_3_64
def bad_A02404_3_65 := bad_of_rows (Order10Orbit.A02404.graph 3 65) (Order10Orbit.A02404.sourceRows 3 65)
  (Order10Orbit.A02404.graph_adj_iff 3 65 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_65 (by decide +kernel) reject_A02404_3_65
def bad_A02404_3_66 := bad_of_rows (Order10Orbit.A02404.graph 3 66) (Order10Orbit.A02404.sourceRows 3 66)
  (Order10Orbit.A02404.graph_adj_iff 3 66 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_66 (by decide +kernel) reject_A02404_3_66
def bad_A02404_3_67 := bad_of_rows (Order10Orbit.A02404.graph 3 67) (Order10Orbit.A02404.sourceRows 3 67)
  (Order10Orbit.A02404.graph_adj_iff 3 67 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_67 (by decide +kernel) reject_A02404_3_67
def bad_A02404_3_68 := bad_of_rows (Order10Orbit.A02404.graph 3 68) (Order10Orbit.A02404.sourceRows 3 68)
  (Order10Orbit.A02404.graph_adj_iff 3 68 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_68 (by decide +kernel) reject_A02404_3_68
def bad_A02404_3_69 := bad_of_rows (Order10Orbit.A02404.graph 3 69) (Order10Orbit.A02404.sourceRows 3 69)
  (Order10Orbit.A02404.graph_adj_iff 3 69 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_69 (by decide +kernel) reject_A02404_3_69
def bad_A02404_3_70 := bad_of_rows (Order10Orbit.A02404.graph 3 70) (Order10Orbit.A02404.sourceRows 3 70)
  (Order10Orbit.A02404.graph_adj_iff 3 70 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_70 (by decide +kernel) reject_A02404_3_70
def bad_A02404_3_71 := bad_of_rows (Order10Orbit.A02404.graph 3 71) (Order10Orbit.A02404.sourceRows 3 71)
  (Order10Orbit.A02404.graph_adj_iff 3 71 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_71 (by decide +kernel) reject_A02404_3_71
theorem bad_A02404_3_72 (h : NoEmbed Order10Search72.sourceGraph Order10Search72.targetGraph) : ∃ i : Fin 2, ¬ ∃ f : Fin 10 → Fin 19, Function.Injective f ∧
      ∀ u v, (Order10Orbit.A02404.graph 3 72).Adj u v → (Order10Common.targets i).Adj (f u) (f v) := by
  have hr : ∀ u : Fin 10, Order10Search72.source u.val = Order10Orbit.A02404.sourceRows 3 72 u.val := by decide +kernel
  have hg : Order10Search72.sourceGraph = Order10Orbit.A02404.graph 3 72 := by
    ext u v
    rw [Order10Orbit.A02404.graph_adj_iff 3 72 (by decide +kernel) (by decide +kernel) u v]
    change (Order10Search72.source u.val).testBit v.val = true ↔ (Order10Orbit.A02404.sourceRows 3 72 u.val).testBit v.val = true
    rw [hr u]
  have ht : Order10Common.target = Order10Search72.targetGraph := by ext u v; rfl
  apply noEmbed_as_bad (Order10Orbit.A02404.graph 3 72) 0
  change NoEmbed (Order10Orbit.A02404.graph 3 72) Order10Common.target
  rw [← hg, ht]
  exact h
def bad_A02404_3_73 := bad_of_rows (Order10Orbit.A02404.graph 3 73) (Order10Orbit.A02404.sourceRows 3 73)
  (Order10Orbit.A02404.graph_adj_iff 3 73 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_73 (by decide +kernel) reject_A02404_3_73
def bad_A02404_3_74 := bad_of_rows (Order10Orbit.A02404.graph 3 74) (Order10Orbit.A02404.sourceRows 3 74)
  (Order10Orbit.A02404.graph_adj_iff 3 74 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_74 (by decide +kernel) reject_A02404_3_74
def bad_A02404_3_75 := bad_of_rows (Order10Orbit.A02404.graph 3 75) (Order10Orbit.A02404.sourceRows 3 75)
  (Order10Orbit.A02404.graph_adj_iff 3 75 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_75 (by decide +kernel) reject_A02404_3_75
def bad_A02404_3_76 := bad_of_rows (Order10Orbit.A02404.graph 3 76) (Order10Orbit.A02404.sourceRows 3 76)
  (Order10Orbit.A02404.graph_adj_iff 3 76 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_76 (by decide +kernel) reject_A02404_3_76
def bad_A02404_3_77 := bad_of_rows (Order10Orbit.A02404.graph 3 77) (Order10Orbit.A02404.sourceRows 3 77)
  (Order10Orbit.A02404.graph_adj_iff 3 77 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_77 (by decide +kernel) reject_A02404_3_77
def bad_A02404_3_78 := bad_of_rows (Order10Orbit.A02404.graph 3 78) (Order10Orbit.A02404.sourceRows 3 78)
  (Order10Orbit.A02404.graph_adj_iff 3 78 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_78 (by decide +kernel) reject_A02404_3_78
def bad_A02404_3_79 := bad_of_rows (Order10Orbit.A02404.graph 3 79) (Order10Orbit.A02404.sourceRows 3 79)
  (Order10Orbit.A02404.graph_adj_iff 3 79 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_79 (by decide +kernel) reject_A02404_3_79
def bad_A02404_3_80 := bad_of_rows (Order10Orbit.A02404.graph 3 80) (Order10Orbit.A02404.sourceRows 3 80)
  (Order10Orbit.A02404.graph_adj_iff 3 80 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_80 (by decide +kernel) reject_A02404_3_80
def bad_A02404_3_81 := bad_of_rows (Order10Orbit.A02404.graph 3 81) (Order10Orbit.A02404.sourceRows 3 81)
  (Order10Orbit.A02404.graph_adj_iff 3 81 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_81 (by decide +kernel) reject_A02404_3_81
def bad_A02404_3_82 := bad_of_rows (Order10Orbit.A02404.graph 3 82) (Order10Orbit.A02404.sourceRows 3 82)
  (Order10Orbit.A02404.graph_adj_iff 3 82 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_82 (by decide +kernel) reject_A02404_3_82
def bad_A02404_3_83 := bad_of_rows (Order10Orbit.A02404.graph 3 83) (Order10Orbit.A02404.sourceRows 3 83)
  (Order10Orbit.A02404.graph_adj_iff 3 83 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_83 (by decide +kernel) reject_A02404_3_83
def bad_A02404_3_84 := bad_of_rows (Order10Orbit.A02404.graph 3 84) (Order10Orbit.A02404.sourceRows 3 84)
  (Order10Orbit.A02404.graph_adj_iff 3 84 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_84 (by decide +kernel) reject_A02404_3_84
def bad_A02404_3_85 := bad_of_rows (Order10Orbit.A02404.graph 3 85) (Order10Orbit.A02404.sourceRows 3 85)
  (Order10Orbit.A02404.graph_adj_iff 3 85 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_85 (by decide +kernel) reject_A02404_3_85
def bad_A02404_3_86 := bad_of_rows (Order10Orbit.A02404.graph 3 86) (Order10Orbit.A02404.sourceRows 3 86)
  (Order10Orbit.A02404.graph_adj_iff 3 86 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_86 (by decide +kernel) reject_A02404_3_86
def bad_A02404_3_87 := bad_of_rows (Order10Orbit.A02404.graph 3 87) (Order10Orbit.A02404.sourceRows 3 87)
  (Order10Orbit.A02404.graph_adj_iff 3 87 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_87 (by decide +kernel) reject_A02404_3_87
def bad_A02404_3_88 := bad_of_rows (Order10Orbit.A02404.graph 3 88) (Order10Orbit.A02404.sourceRows 3 88)
  (Order10Orbit.A02404.graph_adj_iff 3 88 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_88 (by decide +kernel) reject_A02404_3_88
def bad_A02404_3_89 := bad_of_rows (Order10Orbit.A02404.graph 3 89) (Order10Orbit.A02404.sourceRows 3 89)
  (Order10Orbit.A02404.graph_adj_iff 3 89 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_89 (by decide +kernel) reject_A02404_3_89
def bad_A02404_3_90 := bad_of_rows (Order10Orbit.A02404.graph 3 90) (Order10Orbit.A02404.sourceRows 3 90)
  (Order10Orbit.A02404.graph_adj_iff 3 90 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_90 (by decide +kernel) reject_A02404_3_90
def bad_A02404_3_91 := bad_of_rows (Order10Orbit.A02404.graph 3 91) (Order10Orbit.A02404.sourceRows 3 91)
  (Order10Orbit.A02404.graph_adj_iff 3 91 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_91 (by decide +kernel) reject_A02404_3_91
def bad_A02404_3_92 := bad_of_rows (Order10Orbit.A02404.graph 3 92) (Order10Orbit.A02404.sourceRows 3 92)
  (Order10Orbit.A02404.graph_adj_iff 3 92 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_92 (by decide +kernel) reject_A02404_3_92
def bad_A02404_3_93 := bad_of_rows (Order10Orbit.A02404.graph 3 93) (Order10Orbit.A02404.sourceRows 3 93)
  (Order10Orbit.A02404.graph_adj_iff 3 93 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_93 (by decide +kernel) reject_A02404_3_93
theorem bad_A02404_3_94 (h : NoEmbed Order10Search94.sourceGraph Order10Search94.targetGraph) : ∃ i : Fin 2, ¬ ∃ f : Fin 10 → Fin 19, Function.Injective f ∧
      ∀ u v, (Order10Orbit.A02404.graph 3 94).Adj u v → (Order10Common.targets i).Adj (f u) (f v) := by
  have hr : ∀ u : Fin 10, Order10Search94.source u.val = Order10Orbit.A02404.sourceRows 3 94 u.val := by decide +kernel
  have hg : Order10Search94.sourceGraph = Order10Orbit.A02404.graph 3 94 := by
    ext u v
    rw [Order10Orbit.A02404.graph_adj_iff 3 94 (by decide +kernel) (by decide +kernel) u v]
    change (Order10Search94.source u.val).testBit v.val = true ↔ (Order10Orbit.A02404.sourceRows 3 94 u.val).testBit v.val = true
    rw [hr u]
  have ht : Order10Common.target = Order10Search94.targetGraph := by ext u v; rfl
  apply noEmbed_as_bad (Order10Orbit.A02404.graph 3 94) 0
  change NoEmbed (Order10Orbit.A02404.graph 3 94) Order10Common.target
  rw [← hg, ht]
  exact h
def bad_A02404_3_95 := bad_of_rows (Order10Orbit.A02404.graph 3 95) (Order10Orbit.A02404.sourceRows 3 95)
  (Order10Orbit.A02404.graph_adj_iff 3 95 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_95 (by decide +kernel) reject_A02404_3_95
def bad_A02404_3_96 := bad_of_rows (Order10Orbit.A02404.graph 3 96) (Order10Orbit.A02404.sourceRows 3 96)
  (Order10Orbit.A02404.graph_adj_iff 3 96 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_96 (by decide +kernel) reject_A02404_3_96
def bad_A02404_3_97 := bad_of_rows (Order10Orbit.A02404.graph 3 97) (Order10Orbit.A02404.sourceRows 3 97)
  (Order10Orbit.A02404.graph_adj_iff 3 97 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_97 (by decide +kernel) reject_A02404_3_97
def bad_A02404_3_98 := bad_of_rows (Order10Orbit.A02404.graph 3 98) (Order10Orbit.A02404.sourceRows 3 98)
  (Order10Orbit.A02404.graph_adj_iff 3 98 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_98 (by decide +kernel) reject_A02404_3_98
def bad_A02404_3_99 := bad_of_rows (Order10Orbit.A02404.graph 3 99) (Order10Orbit.A02404.sourceRows 3 99)
  (Order10Orbit.A02404.graph_adj_iff 3 99 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_99 (by decide +kernel) reject_A02404_3_99
def bad_A02404_3_100 := bad_of_rows (Order10Orbit.A02404.graph 3 100) (Order10Orbit.A02404.sourceRows 3 100)
  (Order10Orbit.A02404.graph_adj_iff 3 100 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_100 (by decide +kernel) reject_A02404_3_100
def bad_A02404_3_101 := bad_of_rows (Order10Orbit.A02404.graph 3 101) (Order10Orbit.A02404.sourceRows 3 101)
  (Order10Orbit.A02404.graph_adj_iff 3 101 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_101 (by decide +kernel) reject_A02404_3_101
def bad_A02404_3_102 := bad_of_rows (Order10Orbit.A02404.graph 3 102) (Order10Orbit.A02404.sourceRows 3 102)
  (Order10Orbit.A02404.graph_adj_iff 3 102 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_102 (by decide +kernel) reject_A02404_3_102
theorem bad_A02404_3_103 (h : NoEmbed Order10Search103.sourceGraph Order10Search103.targetGraph) : ∃ i : Fin 2, ¬ ∃ f : Fin 10 → Fin 19, Function.Injective f ∧
      ∀ u v, (Order10Orbit.A02404.graph 3 103).Adj u v → (Order10Common.targets i).Adj (f u) (f v) := by
  have hr : ∀ u : Fin 10, Order10Search103.source u.val = Order10Orbit.A02404.sourceRows 3 103 u.val := by decide +kernel
  have hg : Order10Search103.sourceGraph = Order10Orbit.A02404.graph 3 103 := by
    ext u v
    rw [Order10Orbit.A02404.graph_adj_iff 3 103 (by decide +kernel) (by decide +kernel) u v]
    change (Order10Search103.source u.val).testBit v.val = true ↔ (Order10Orbit.A02404.sourceRows 3 103 u.val).testBit v.val = true
    rw [hr u]
  have ht : Order10Common.targetOther = Order10Search103.targetGraph := by ext u v; rfl
  apply noEmbed_as_bad (Order10Orbit.A02404.graph 3 103) 1
  change NoEmbed (Order10Orbit.A02404.graph 3 103) Order10Common.targetOther
  rw [← hg, ht]
  exact h
def bad_A02404_3_104 := bad_of_rows (Order10Orbit.A02404.graph 3 104) (Order10Orbit.A02404.sourceRows 3 104)
  (Order10Orbit.A02404.graph_adj_iff 3 104 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_104 (by decide +kernel) reject_A02404_3_104
def bad_A02404_3_105 := bad_of_rows (Order10Orbit.A02404.graph 3 105) (Order10Orbit.A02404.sourceRows 3 105)
  (Order10Orbit.A02404.graph_adj_iff 3 105 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_105 (by decide +kernel) reject_A02404_3_105
theorem bad_A02404_3_106 (h : NoEmbed Order10Search106.sourceGraph Order10Search106.targetGraph) : ∃ i : Fin 2, ¬ ∃ f : Fin 10 → Fin 19, Function.Injective f ∧
      ∀ u v, (Order10Orbit.A02404.graph 3 106).Adj u v → (Order10Common.targets i).Adj (f u) (f v) := by
  have hr : ∀ u : Fin 10, Order10Search106.source u.val = Order10Orbit.A02404.sourceRows 3 106 u.val := by decide +kernel
  have hg : Order10Search106.sourceGraph = Order10Orbit.A02404.graph 3 106 := by
    ext u v
    rw [Order10Orbit.A02404.graph_adj_iff 3 106 (by decide +kernel) (by decide +kernel) u v]
    change (Order10Search106.source u.val).testBit v.val = true ↔ (Order10Orbit.A02404.sourceRows 3 106 u.val).testBit v.val = true
    rw [hr u]
  have ht : Order10Common.targetOther = Order10Search106.targetGraph := by ext u v; rfl
  apply noEmbed_as_bad (Order10Orbit.A02404.graph 3 106) 1
  change NoEmbed (Order10Orbit.A02404.graph 3 106) Order10Common.targetOther
  rw [← hg, ht]
  exact h
def bad_A02404_3_107 := bad_of_rows (Order10Orbit.A02404.graph 3 107) (Order10Orbit.A02404.sourceRows 3 107)
  (Order10Orbit.A02404.graph_adj_iff 3 107 (by decide +kernel) (by decide +kernel))
  rows_A02404_3_107 (by decide +kernel) reject_A02404_3_107
def bad_A03304_0_0 := bad_of_rows (Order10Orbit.A03304.graph 0 0) (Order10Orbit.A03304.sourceRows 0 0)
  (Order10Orbit.A03304.graph_adj_iff 0 0 (by decide +kernel) (by decide +kernel))
  rows_A03304_0_0 (by decide +kernel) reject_A03304_0_0
def bad_A03304_1_0 := bad_of_rows (Order10Orbit.A03304.graph 1 0) (Order10Orbit.A03304.sourceRows 1 0)
  (Order10Orbit.A03304.graph_adj_iff 1 0 (by decide +kernel) (by decide +kernel))
  rows_A03304_1_0 (by decide +kernel) reject_A03304_1_0
def bad_A03304_1_1 := bad_of_rows (Order10Orbit.A03304.graph 1 1) (Order10Orbit.A03304.sourceRows 1 1)
  (Order10Orbit.A03304.graph_adj_iff 1 1 (by decide +kernel) (by decide +kernel))
  rows_A03304_1_1 (by decide +kernel) reject_A03304_1_1
def bad_A03304_1_2 := bad_of_rows (Order10Orbit.A03304.graph 1 2) (Order10Orbit.A03304.sourceRows 1 2)
  (Order10Orbit.A03304.graph_adj_iff 1 2 (by decide +kernel) (by decide +kernel))
  rows_A03304_1_2 (by decide +kernel) reject_A03304_1_2
def bad_A03304_1_3 := bad_of_rows (Order10Orbit.A03304.graph 1 3) (Order10Orbit.A03304.sourceRows 1 3)
  (Order10Orbit.A03304.graph_adj_iff 1 3 (by decide +kernel) (by decide +kernel))
  rows_A03304_1_3 (by decide +kernel) reject_A03304_1_3
def bad_A03304_1_4 := bad_of_rows (Order10Orbit.A03304.graph 1 4) (Order10Orbit.A03304.sourceRows 1 4)
  (Order10Orbit.A03304.graph_adj_iff 1 4 (by decide +kernel) (by decide +kernel))
  rows_A03304_1_4 (by decide +kernel) reject_A03304_1_4
def bad_A03304_2_0 := bad_of_rows (Order10Orbit.A03304.graph 2 0) (Order10Orbit.A03304.sourceRows 2 0)
  (Order10Orbit.A03304.graph_adj_iff 2 0 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_0 (by decide +kernel) reject_A03304_2_0
def bad_A03304_2_1 := bad_of_rows (Order10Orbit.A03304.graph 2 1) (Order10Orbit.A03304.sourceRows 2 1)
  (Order10Orbit.A03304.graph_adj_iff 2 1 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_1 (by decide +kernel) reject_A03304_2_1
def bad_A03304_2_2 := bad_of_rows (Order10Orbit.A03304.graph 2 2) (Order10Orbit.A03304.sourceRows 2 2)
  (Order10Orbit.A03304.graph_adj_iff 2 2 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_2 (by decide +kernel) reject_A03304_2_2
def bad_A03304_2_3 := bad_of_rows (Order10Orbit.A03304.graph 2 3) (Order10Orbit.A03304.sourceRows 2 3)
  (Order10Orbit.A03304.graph_adj_iff 2 3 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_3 (by decide +kernel) reject_A03304_2_3
def bad_A03304_2_4 := bad_of_rows (Order10Orbit.A03304.graph 2 4) (Order10Orbit.A03304.sourceRows 2 4)
  (Order10Orbit.A03304.graph_adj_iff 2 4 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_4 (by decide +kernel) reject_A03304_2_4
def bad_A03304_2_5 := bad_of_rows (Order10Orbit.A03304.graph 2 5) (Order10Orbit.A03304.sourceRows 2 5)
  (Order10Orbit.A03304.graph_adj_iff 2 5 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_5 (by decide +kernel) reject_A03304_2_5
def bad_A03304_2_6 := bad_of_rows (Order10Orbit.A03304.graph 2 6) (Order10Orbit.A03304.sourceRows 2 6)
  (Order10Orbit.A03304.graph_adj_iff 2 6 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_6 (by decide +kernel) reject_A03304_2_6
def bad_A03304_2_7 := bad_of_rows (Order10Orbit.A03304.graph 2 7) (Order10Orbit.A03304.sourceRows 2 7)
  (Order10Orbit.A03304.graph_adj_iff 2 7 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_7 (by decide +kernel) reject_A03304_2_7
def bad_A03304_2_8 := bad_of_rows (Order10Orbit.A03304.graph 2 8) (Order10Orbit.A03304.sourceRows 2 8)
  (Order10Orbit.A03304.graph_adj_iff 2 8 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_8 (by decide +kernel) reject_A03304_2_8
def bad_A03304_2_9 := bad_of_rows (Order10Orbit.A03304.graph 2 9) (Order10Orbit.A03304.sourceRows 2 9)
  (Order10Orbit.A03304.graph_adj_iff 2 9 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_9 (by decide +kernel) reject_A03304_2_9
def bad_A03304_2_10 := bad_of_rows (Order10Orbit.A03304.graph 2 10) (Order10Orbit.A03304.sourceRows 2 10)
  (Order10Orbit.A03304.graph_adj_iff 2 10 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_10 (by decide +kernel) reject_A03304_2_10
def bad_A03304_2_11 := bad_of_rows (Order10Orbit.A03304.graph 2 11) (Order10Orbit.A03304.sourceRows 2 11)
  (Order10Orbit.A03304.graph_adj_iff 2 11 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_11 (by decide +kernel) reject_A03304_2_11
def bad_A03304_2_12 := bad_of_rows (Order10Orbit.A03304.graph 2 12) (Order10Orbit.A03304.sourceRows 2 12)
  (Order10Orbit.A03304.graph_adj_iff 2 12 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_12 (by decide +kernel) reject_A03304_2_12
def bad_A03304_2_13 := bad_of_rows (Order10Orbit.A03304.graph 2 13) (Order10Orbit.A03304.sourceRows 2 13)
  (Order10Orbit.A03304.graph_adj_iff 2 13 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_13 (by decide +kernel) reject_A03304_2_13
def bad_A03304_2_14 := bad_of_rows (Order10Orbit.A03304.graph 2 14) (Order10Orbit.A03304.sourceRows 2 14)
  (Order10Orbit.A03304.graph_adj_iff 2 14 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_14 (by decide +kernel) reject_A03304_2_14
def bad_A03304_2_15 := bad_of_rows (Order10Orbit.A03304.graph 2 15) (Order10Orbit.A03304.sourceRows 2 15)
  (Order10Orbit.A03304.graph_adj_iff 2 15 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_15 (by decide +kernel) reject_A03304_2_15
def bad_A03304_2_16 := bad_of_rows (Order10Orbit.A03304.graph 2 16) (Order10Orbit.A03304.sourceRows 2 16)
  (Order10Orbit.A03304.graph_adj_iff 2 16 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_16 (by decide +kernel) reject_A03304_2_16
def bad_A03304_2_17 := bad_of_rows (Order10Orbit.A03304.graph 2 17) (Order10Orbit.A03304.sourceRows 2 17)
  (Order10Orbit.A03304.graph_adj_iff 2 17 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_17 (by decide +kernel) reject_A03304_2_17
def bad_A03304_2_18 := bad_of_rows (Order10Orbit.A03304.graph 2 18) (Order10Orbit.A03304.sourceRows 2 18)
  (Order10Orbit.A03304.graph_adj_iff 2 18 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_18 (by decide +kernel) reject_A03304_2_18
def bad_A03304_2_19 := bad_of_rows (Order10Orbit.A03304.graph 2 19) (Order10Orbit.A03304.sourceRows 2 19)
  (Order10Orbit.A03304.graph_adj_iff 2 19 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_19 (by decide +kernel) reject_A03304_2_19
def bad_A03304_2_20 := bad_of_rows (Order10Orbit.A03304.graph 2 20) (Order10Orbit.A03304.sourceRows 2 20)
  (Order10Orbit.A03304.graph_adj_iff 2 20 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_20 (by decide +kernel) reject_A03304_2_20
theorem bad_A03304_2_21 (h : NoEmbed Order10Search129.sourceGraph Order10Search129.targetGraph) : ∃ i : Fin 2, ¬ ∃ f : Fin 10 → Fin 19, Function.Injective f ∧
      ∀ u v, (Order10Orbit.A03304.graph 2 21).Adj u v → (Order10Common.targets i).Adj (f u) (f v) := by
  have hr : ∀ u : Fin 10, Order10Search129.source u.val = Order10Orbit.A03304.sourceRows 2 21 u.val := by decide +kernel
  have hg : Order10Search129.sourceGraph = Order10Orbit.A03304.graph 2 21 := by
    ext u v
    rw [Order10Orbit.A03304.graph_adj_iff 2 21 (by decide +kernel) (by decide +kernel) u v]
    change (Order10Search129.source u.val).testBit v.val = true ↔ (Order10Orbit.A03304.sourceRows 2 21 u.val).testBit v.val = true
    rw [hr u]
  have ht : Order10Common.target = Order10Search129.targetGraph := by ext u v; rfl
  apply noEmbed_as_bad (Order10Orbit.A03304.graph 2 21) 0
  change NoEmbed (Order10Orbit.A03304.graph 2 21) Order10Common.target
  rw [← hg, ht]
  exact h
def bad_A03304_2_22 := bad_of_rows (Order10Orbit.A03304.graph 2 22) (Order10Orbit.A03304.sourceRows 2 22)
  (Order10Orbit.A03304.graph_adj_iff 2 22 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_22 (by decide +kernel) reject_A03304_2_22
def bad_A03304_2_23 := bad_of_rows (Order10Orbit.A03304.graph 2 23) (Order10Orbit.A03304.sourceRows 2 23)
  (Order10Orbit.A03304.graph_adj_iff 2 23 (by decide +kernel) (by decide +kernel))
  rows_A03304_2_23 (by decide +kernel) reject_A03304_2_23
theorem bad_A03304_2_24 (h : NoEmbed Order10Search132.sourceGraph Order10Search132.targetGraph) : ∃ i : Fin 2, ¬ ∃ f : Fin 10 → Fin 19, Function.Injective f ∧
      ∀ u v, (Order10Orbit.A03304.graph 2 24).Adj u v → (Order10Common.targets i).Adj (f u) (f v) := by
  have hr : ∀ u : Fin 10, Order10Search132.source u.val = Order10Orbit.A03304.sourceRows 2 24 u.val := by decide +kernel
  have hg : Order10Search132.sourceGraph = Order10Orbit.A03304.graph 2 24 := by
    ext u v
    rw [Order10Orbit.A03304.graph_adj_iff 2 24 (by decide +kernel) (by decide +kernel) u v]
    change (Order10Search132.source u.val).testBit v.val = true ↔ (Order10Orbit.A03304.sourceRows 2 24 u.val).testBit v.val = true
    rw [hr u]
  have ht : Order10Common.targetOther = Order10Search132.targetGraph := by ext u v; rfl
  apply noEmbed_as_bad (Order10Orbit.A03304.graph 2 24) 1
  change NoEmbed (Order10Orbit.A03304.graph 2 24) Order10Common.targetOther
  rw [← hg, ht]
  exact h
def bad_A04114_0_0 := bad_of_rows (Order10Orbit.A04114.graph 0 0) (Order10Orbit.A04114.sourceRows 0 0)
  (Order10Orbit.A04114.graph_adj_iff 0 0 (by decide +kernel) (by decide +kernel))
  rows_A04114_0_0 (by decide +kernel) reject_A04114_0_0
def bad_A04114_1_0 := bad_of_rows (Order10Orbit.A04114.graph 1 0) (Order10Orbit.A04114.sourceRows 1 0)
  (Order10Orbit.A04114.graph_adj_iff 1 0 (by decide +kernel) (by decide +kernel))
  rows_A04114_1_0 (by decide +kernel) reject_A04114_1_0
def bad_A04114_1_1 := bad_of_rows (Order10Orbit.A04114.graph 1 1) (Order10Orbit.A04114.sourceRows 1 1)
  (Order10Orbit.A04114.graph_adj_iff 1 1 (by decide +kernel) (by decide +kernel))
  rows_A04114_1_1 (by decide +kernel) reject_A04114_1_1
def bad_A04114_1_2 := bad_of_rows (Order10Orbit.A04114.graph 1 2) (Order10Orbit.A04114.sourceRows 1 2)
  (Order10Orbit.A04114.graph_adj_iff 1 2 (by decide +kernel) (by decide +kernel))
  rows_A04114_1_2 (by decide +kernel) reject_A04114_1_2
def bad_A04114_1_3 := bad_of_rows (Order10Orbit.A04114.graph 1 3) (Order10Orbit.A04114.sourceRows 1 3)
  (Order10Orbit.A04114.graph_adj_iff 1 3 (by decide +kernel) (by decide +kernel))
  rows_A04114_1_3 (by decide +kernel) reject_A04114_1_3
def bad_A04114_1_4 := bad_of_rows (Order10Orbit.A04114.graph 1 4) (Order10Orbit.A04114.sourceRows 1 4)
  (Order10Orbit.A04114.graph_adj_iff 1 4 (by decide +kernel) (by decide +kernel))
  rows_A04114_1_4 (by decide +kernel) reject_A04114_1_4
def bad_A04114_2_0 := bad_of_rows (Order10Orbit.A04114.graph 2 0) (Order10Orbit.A04114.sourceRows 2 0)
  (Order10Orbit.A04114.graph_adj_iff 2 0 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_0 (by decide +kernel) reject_A04114_2_0
def bad_A04114_2_1 := bad_of_rows (Order10Orbit.A04114.graph 2 1) (Order10Orbit.A04114.sourceRows 2 1)
  (Order10Orbit.A04114.graph_adj_iff 2 1 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_1 (by decide +kernel) reject_A04114_2_1
def bad_A04114_2_2 := bad_of_rows (Order10Orbit.A04114.graph 2 2) (Order10Orbit.A04114.sourceRows 2 2)
  (Order10Orbit.A04114.graph_adj_iff 2 2 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_2 (by decide +kernel) reject_A04114_2_2
def bad_A04114_2_3 := bad_of_rows (Order10Orbit.A04114.graph 2 3) (Order10Orbit.A04114.sourceRows 2 3)
  (Order10Orbit.A04114.graph_adj_iff 2 3 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_3 (by decide +kernel) reject_A04114_2_3
def bad_A04114_2_4 := bad_of_rows (Order10Orbit.A04114.graph 2 4) (Order10Orbit.A04114.sourceRows 2 4)
  (Order10Orbit.A04114.graph_adj_iff 2 4 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_4 (by decide +kernel) reject_A04114_2_4
def bad_A04114_2_5 := bad_of_rows (Order10Orbit.A04114.graph 2 5) (Order10Orbit.A04114.sourceRows 2 5)
  (Order10Orbit.A04114.graph_adj_iff 2 5 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_5 (by decide +kernel) reject_A04114_2_5
def bad_A04114_2_6 := bad_of_rows (Order10Orbit.A04114.graph 2 6) (Order10Orbit.A04114.sourceRows 2 6)
  (Order10Orbit.A04114.graph_adj_iff 2 6 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_6 (by decide +kernel) reject_A04114_2_6
def bad_A04114_2_7 := bad_of_rows (Order10Orbit.A04114.graph 2 7) (Order10Orbit.A04114.sourceRows 2 7)
  (Order10Orbit.A04114.graph_adj_iff 2 7 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_7 (by decide +kernel) reject_A04114_2_7
def bad_A04114_2_8 := bad_of_rows (Order10Orbit.A04114.graph 2 8) (Order10Orbit.A04114.sourceRows 2 8)
  (Order10Orbit.A04114.graph_adj_iff 2 8 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_8 (by decide +kernel) reject_A04114_2_8
def bad_A04114_2_9 := bad_of_rows (Order10Orbit.A04114.graph 2 9) (Order10Orbit.A04114.sourceRows 2 9)
  (Order10Orbit.A04114.graph_adj_iff 2 9 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_9 (by decide +kernel) reject_A04114_2_9
def bad_A04114_2_10 := bad_of_rows (Order10Orbit.A04114.graph 2 10) (Order10Orbit.A04114.sourceRows 2 10)
  (Order10Orbit.A04114.graph_adj_iff 2 10 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_10 (by decide +kernel) reject_A04114_2_10
def bad_A04114_2_11 := bad_of_rows (Order10Orbit.A04114.graph 2 11) (Order10Orbit.A04114.sourceRows 2 11)
  (Order10Orbit.A04114.graph_adj_iff 2 11 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_11 (by decide +kernel) reject_A04114_2_11
def bad_A04114_2_12 := bad_of_rows (Order10Orbit.A04114.graph 2 12) (Order10Orbit.A04114.sourceRows 2 12)
  (Order10Orbit.A04114.graph_adj_iff 2 12 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_12 (by decide +kernel) reject_A04114_2_12
def bad_A04114_2_13 := bad_of_rows (Order10Orbit.A04114.graph 2 13) (Order10Orbit.A04114.sourceRows 2 13)
  (Order10Orbit.A04114.graph_adj_iff 2 13 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_13 (by decide +kernel) reject_A04114_2_13
def bad_A04114_2_14 := bad_of_rows (Order10Orbit.A04114.graph 2 14) (Order10Orbit.A04114.sourceRows 2 14)
  (Order10Orbit.A04114.graph_adj_iff 2 14 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_14 (by decide +kernel) reject_A04114_2_14
def bad_A04114_2_15 := bad_of_rows (Order10Orbit.A04114.graph 2 15) (Order10Orbit.A04114.sourceRows 2 15)
  (Order10Orbit.A04114.graph_adj_iff 2 15 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_15 (by decide +kernel) reject_A04114_2_15
def bad_A04114_2_16 := bad_of_rows (Order10Orbit.A04114.graph 2 16) (Order10Orbit.A04114.sourceRows 2 16)
  (Order10Orbit.A04114.graph_adj_iff 2 16 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_16 (by decide +kernel) reject_A04114_2_16
def bad_A04114_2_17 := bad_of_rows (Order10Orbit.A04114.graph 2 17) (Order10Orbit.A04114.sourceRows 2 17)
  (Order10Orbit.A04114.graph_adj_iff 2 17 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_17 (by decide +kernel) reject_A04114_2_17
def bad_A04114_2_18 := bad_of_rows (Order10Orbit.A04114.graph 2 18) (Order10Orbit.A04114.sourceRows 2 18)
  (Order10Orbit.A04114.graph_adj_iff 2 18 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_18 (by decide +kernel) reject_A04114_2_18
def bad_A04114_2_19 := bad_of_rows (Order10Orbit.A04114.graph 2 19) (Order10Orbit.A04114.sourceRows 2 19)
  (Order10Orbit.A04114.graph_adj_iff 2 19 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_19 (by decide +kernel) reject_A04114_2_19
def bad_A04114_2_20 := bad_of_rows (Order10Orbit.A04114.graph 2 20) (Order10Orbit.A04114.sourceRows 2 20)
  (Order10Orbit.A04114.graph_adj_iff 2 20 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_20 (by decide +kernel) reject_A04114_2_20
def bad_A04114_2_21 := bad_of_rows (Order10Orbit.A04114.graph 2 21) (Order10Orbit.A04114.sourceRows 2 21)
  (Order10Orbit.A04114.graph_adj_iff 2 21 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_21 (by decide +kernel) reject_A04114_2_21
def bad_A04114_2_22 := bad_of_rows (Order10Orbit.A04114.graph 2 22) (Order10Orbit.A04114.sourceRows 2 22)
  (Order10Orbit.A04114.graph_adj_iff 2 22 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_22 (by decide +kernel) reject_A04114_2_22
def bad_A04114_2_23 := bad_of_rows (Order10Orbit.A04114.graph 2 23) (Order10Orbit.A04114.sourceRows 2 23)
  (Order10Orbit.A04114.graph_adj_iff 2 23 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_23 (by decide +kernel) reject_A04114_2_23
def bad_A04114_2_24 := bad_of_rows (Order10Orbit.A04114.graph 2 24) (Order10Orbit.A04114.sourceRows 2 24)
  (Order10Orbit.A04114.graph_adj_iff 2 24 (by decide +kernel) (by decide +kernel))
  rows_A04114_2_24 (by decide +kernel) reject_A04114_2_24
theorem all_A02404 (h56 : NoEmbed Order10Search56.sourceGraph Order10Search56.targetGraph) (h72 : NoEmbed Order10Search72.sourceGraph Order10Search72.targetGraph) (h94 : NoEmbed Order10Search94.sourceGraph Order10Search94.targetGraph) (h103 : NoEmbed Order10Search103.sourceGraph Order10Search103.targetGraph) (h106 : NoEmbed Order10Search106.sourceGraph Order10Search106.targetGraph) :
    ∀ k, k ≤ Order10Orbit.A02404.depth → ∀ j, j < Order10Orbit.A02404.count k →
    ∃ i : Fin 2, ¬ ∃ f : Fin 10 → Fin 19, Function.Injective f ∧
      ∀ u v, (Order10Orbit.A02404.graph k j).Adj u v → (Order10Common.targets i).Adj (f u) (f v) := by
  intro k hk j hj
  have hk' : k ∈ List.range 4 := List.mem_range.mpr (Nat.lt_succ_of_le hk)
  change k ∈ [0,1,2,3] at hk'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
  rcases hk' with rfl | rfl | rfl | rfl
  · have hj' : j ∈ List.range 1 := List.mem_range.mpr hj
    change j ∈ [0] at hj'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl
    exact bad_A02404_0_0
  · have hj' : j ∈ List.range 5 := List.mem_range.mpr hj
    change j ∈ [0,1,2,3,4] at hj'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl | rfl | rfl | rfl | rfl
    · exact bad_A02404_1_0
    · exact bad_A02404_1_1
    · exact bad_A02404_1_2
    · exact bad_A02404_1_3
    · exact bad_A02404_1_4
  · have hj' : j ∈ List.range 24 := List.mem_range.mpr hj
    change j ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] at hj'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bad_A02404_2_0
    · exact bad_A02404_2_1
    · exact bad_A02404_2_2
    · exact bad_A02404_2_3
    · exact bad_A02404_2_4
    · exact bad_A02404_2_5
    · exact bad_A02404_2_6
    · exact bad_A02404_2_7
    · exact bad_A02404_2_8
    · exact bad_A02404_2_9
    · exact bad_A02404_2_10
    · exact bad_A02404_2_11
    · exact bad_A02404_2_12
    · exact bad_A02404_2_13
    · exact bad_A02404_2_14
    · exact bad_A02404_2_15
    · exact bad_A02404_2_16
    · exact bad_A02404_2_17
    · exact bad_A02404_2_18
    · exact bad_A02404_2_19
    · exact bad_A02404_2_20
    · exact bad_A02404_2_21
    · exact bad_A02404_2_22
    · exact bad_A02404_2_23
  · have hj' : j ∈ List.range 108 := List.mem_range.mpr hj
    change j ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107] at hj'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bad_A02404_3_0
    · exact bad_A02404_3_1
    · exact bad_A02404_3_2
    · exact bad_A02404_3_3
    · exact bad_A02404_3_4
    · exact bad_A02404_3_5
    · exact bad_A02404_3_6
    · exact bad_A02404_3_7
    · exact bad_A02404_3_8
    · exact bad_A02404_3_9
    · exact bad_A02404_3_10
    · exact bad_A02404_3_11
    · exact bad_A02404_3_12
    · exact bad_A02404_3_13
    · exact bad_A02404_3_14
    · exact bad_A02404_3_15
    · exact bad_A02404_3_16
    · exact bad_A02404_3_17
    · exact bad_A02404_3_18
    · exact bad_A02404_3_19
    · exact bad_A02404_3_20
    · exact bad_A02404_3_21
    · exact bad_A02404_3_22
    · exact bad_A02404_3_23
    · exact bad_A02404_3_24
    · exact bad_A02404_3_25
    · exact bad_A02404_3_26
    · exact bad_A02404_3_27
    · exact bad_A02404_3_28
    · exact bad_A02404_3_29
    · exact bad_A02404_3_30
    · exact bad_A02404_3_31
    · exact bad_A02404_3_32
    · exact bad_A02404_3_33
    · exact bad_A02404_3_34
    · exact bad_A02404_3_35
    · exact bad_A02404_3_36
    · exact bad_A02404_3_37
    · exact bad_A02404_3_38
    · exact bad_A02404_3_39
    · exact bad_A02404_3_40
    · exact bad_A02404_3_41
    · exact bad_A02404_3_42
    · exact bad_A02404_3_43
    · exact bad_A02404_3_44
    · exact bad_A02404_3_45
    · exact bad_A02404_3_46
    · exact bad_A02404_3_47
    · exact bad_A02404_3_48
    · exact bad_A02404_3_49
    · exact bad_A02404_3_50
    · exact bad_A02404_3_51
    · exact bad_A02404_3_52
    · exact bad_A02404_3_53
    · exact bad_A02404_3_54
    · exact bad_A02404_3_55
    · exact bad_A02404_3_56 h56
    · exact bad_A02404_3_57
    · exact bad_A02404_3_58
    · exact bad_A02404_3_59
    · exact bad_A02404_3_60
    · exact bad_A02404_3_61
    · exact bad_A02404_3_62
    · exact bad_A02404_3_63
    · exact bad_A02404_3_64
    · exact bad_A02404_3_65
    · exact bad_A02404_3_66
    · exact bad_A02404_3_67
    · exact bad_A02404_3_68
    · exact bad_A02404_3_69
    · exact bad_A02404_3_70
    · exact bad_A02404_3_71
    · exact bad_A02404_3_72 h72
    · exact bad_A02404_3_73
    · exact bad_A02404_3_74
    · exact bad_A02404_3_75
    · exact bad_A02404_3_76
    · exact bad_A02404_3_77
    · exact bad_A02404_3_78
    · exact bad_A02404_3_79
    · exact bad_A02404_3_80
    · exact bad_A02404_3_81
    · exact bad_A02404_3_82
    · exact bad_A02404_3_83
    · exact bad_A02404_3_84
    · exact bad_A02404_3_85
    · exact bad_A02404_3_86
    · exact bad_A02404_3_87
    · exact bad_A02404_3_88
    · exact bad_A02404_3_89
    · exact bad_A02404_3_90
    · exact bad_A02404_3_91
    · exact bad_A02404_3_92
    · exact bad_A02404_3_93
    · exact bad_A02404_3_94 h94
    · exact bad_A02404_3_95
    · exact bad_A02404_3_96
    · exact bad_A02404_3_97
    · exact bad_A02404_3_98
    · exact bad_A02404_3_99
    · exact bad_A02404_3_100
    · exact bad_A02404_3_101
    · exact bad_A02404_3_102
    · exact bad_A02404_3_103 h103
    · exact bad_A02404_3_104
    · exact bad_A02404_3_105
    · exact bad_A02404_3_106 h106
    · exact bad_A02404_3_107
theorem all_A03304 (h129 : NoEmbed Order10Search129.sourceGraph Order10Search129.targetGraph) (h132 : NoEmbed Order10Search132.sourceGraph Order10Search132.targetGraph) :
    ∀ k, k ≤ Order10Orbit.A03304.depth → ∀ j, j < Order10Orbit.A03304.count k →
    ∃ i : Fin 2, ¬ ∃ f : Fin 10 → Fin 19, Function.Injective f ∧
      ∀ u v, (Order10Orbit.A03304.graph k j).Adj u v → (Order10Common.targets i).Adj (f u) (f v) := by
  intro k hk j hj
  have hk' : k ∈ List.range 3 := List.mem_range.mpr (Nat.lt_succ_of_le hk)
  change k ∈ [0,1,2] at hk'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
  rcases hk' with rfl | rfl | rfl
  · have hj' : j ∈ List.range 1 := List.mem_range.mpr hj
    change j ∈ [0] at hj'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl
    exact bad_A03304_0_0
  · have hj' : j ∈ List.range 5 := List.mem_range.mpr hj
    change j ∈ [0,1,2,3,4] at hj'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl | rfl | rfl | rfl | rfl
    · exact bad_A03304_1_0
    · exact bad_A03304_1_1
    · exact bad_A03304_1_2
    · exact bad_A03304_1_3
    · exact bad_A03304_1_4
  · have hj' : j ∈ List.range 25 := List.mem_range.mpr hj
    change j ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24] at hj'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bad_A03304_2_0
    · exact bad_A03304_2_1
    · exact bad_A03304_2_2
    · exact bad_A03304_2_3
    · exact bad_A03304_2_4
    · exact bad_A03304_2_5
    · exact bad_A03304_2_6
    · exact bad_A03304_2_7
    · exact bad_A03304_2_8
    · exact bad_A03304_2_9
    · exact bad_A03304_2_10
    · exact bad_A03304_2_11
    · exact bad_A03304_2_12
    · exact bad_A03304_2_13
    · exact bad_A03304_2_14
    · exact bad_A03304_2_15
    · exact bad_A03304_2_16
    · exact bad_A03304_2_17
    · exact bad_A03304_2_18
    · exact bad_A03304_2_19
    · exact bad_A03304_2_20
    · exact bad_A03304_2_21 h129
    · exact bad_A03304_2_22
    · exact bad_A03304_2_23
    · exact bad_A03304_2_24 h132
theorem all_A04114 :
    ∀ k, k ≤ Order10Orbit.A04114.depth → ∀ j, j < Order10Orbit.A04114.count k →
    ∃ i : Fin 2, ¬ ∃ f : Fin 10 → Fin 19, Function.Injective f ∧
      ∀ u v, (Order10Orbit.A04114.graph k j).Adj u v → (Order10Common.targets i).Adj (f u) (f v) := by
  intro k hk j hj
  have hk' : k ∈ List.range 3 := List.mem_range.mpr (Nat.lt_succ_of_le hk)
  change k ∈ [0,1,2] at hk'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
  rcases hk' with rfl | rfl | rfl
  · have hj' : j ∈ List.range 1 := List.mem_range.mpr hj
    change j ∈ [0] at hj'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl
    exact bad_A04114_0_0
  · have hj' : j ∈ List.range 5 := List.mem_range.mpr hj
    change j ∈ [0,1,2,3,4] at hj'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl | rfl | rfl | rfl | rfl
    · exact bad_A04114_1_0
    · exact bad_A04114_1_1
    · exact bad_A04114_1_2
    · exact bad_A04114_1_3
    · exact bad_A04114_1_4
  · have hj' : j ∈ List.range 25 := List.mem_range.mpr hj
    change j ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24] at hj'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bad_A04114_2_0
    · exact bad_A04114_2_1
    · exact bad_A04114_2_2
    · exact bad_A04114_2_3
    · exact bad_A04114_2_4
    · exact bad_A04114_2_5
    · exact bad_A04114_2_6
    · exact bad_A04114_2_7
    · exact bad_A04114_2_8
    · exact bad_A04114_2_9
    · exact bad_A04114_2_10
    · exact bad_A04114_2_11
    · exact bad_A04114_2_12
    · exact bad_A04114_2_13
    · exact bad_A04114_2_14
    · exact bad_A04114_2_15
    · exact bad_A04114_2_16
    · exact bad_A04114_2_17
    · exact bad_A04114_2_18
    · exact bad_A04114_2_19
    · exact bad_A04114_2_20
    · exact bad_A04114_2_21
    · exact bad_A04114_2_22
    · exact bad_A04114_2_23
    · exact bad_A04114_2_24
end Order10Leaves

-- normalization and common-intersection assembly
namespace Problem14.H3
open SimpleGraph Finset

/-- An injective edge-preserving placement; induced nonedges are unrestricted. -/
def Places {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V ↪ W, G ≤ H.comap f

lemma edge_ncard {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeSet.ncard = G.edgeFinset.card := by
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset]

/-- Every sufficiently dense subgraph is excluded by at least one additional host. -/
def DenseRejected {V W : Type*} (B : SimpleGraph V) (T : Fin 2 → SimpleGraph W)
    (q : ℕ) : Prop :=
  ∀ F : SimpleGraph V, F ≤ B → q ≤ F.edgeSet.ncard → ∃ i, ¬ Places F (T i)

/-- Deletion-orbit coverage plus the representative obstructions supplies the
    whole allocation certificate.  The hypotheses are exactly the two finite
    proof outputs; there is no assumption about untested graphs. -/
theorem denseRejected_of_orbits {V W : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) [DecidableRel B.Adj] (T : Fin 2 → SimpleGraph W)
    (q K : ℕ) (E : Finset (Sym2 V)) (hE : E = B.edgeFinset)
    (hK : E.card - q ≤ K) (count : ℕ → ℕ)
    (rep : ℕ → ℕ → Finset (Sym2 V))
    (coverage : ∀ d : Finset (Sym2 V), d ⊆ E → d.card ≤ K →
      ∃ (p : Equiv.Perm V) (j : ℕ),
        E.map (NumericPermutations.sym2Perm p).toEmbedding = E ∧
        j < count d.card ∧
        rep d.card j = d.map (NumericPermutations.sym2Perm p).toEmbedding)
    (leaves : ∀ k, k ≤ K → ∀ j, j < count k → ∃ i : Fin 2,
      ¬ ∃ f : V → W, Function.Injective f ∧
        ∀ u v, (NumericPermutations.remainingGraph E (rep k j)).Adj u v →
          (T i).Adj (f u) (f v)) : DenseRejected B T q := by
  classical
  intro F hFB hq
  let d := E \ F.edgeFinset
  have hFE : F.edgeFinset ⊆ E := by
    rw [hE]
    exact edgeFinset_mono hFB
  have hd : d ⊆ E := Finset.sdiff_subset
  have hq' : q ≤ F.edgeFinset.card := (edge_ncard F) ▸ hq
  have hdK : d.card ≤ K := by
    dsimp [d]
    rw [Finset.card_sdiff_of_subset hFE]
    exact (Nat.sub_le_sub_left hq' E.card).trans hK
  obtain ⟨p, j, hp, hj, hr⟩ := coverage d hd hdK
  obtain ⟨i, hi⟩ := leaves d.card hdK j hj
  refine ⟨i, ?_⟩
  rintro ⟨f, hf⟩
  have hrestore : NumericPermutations.remainingGraph E d = F := by
    unfold NumericPermutations.remainingGraph
    have hs : E \ d = F.edgeFinset := Finset.sdiff_sdiff_eq_self hFE
    rw [hs, F.coe_edgeFinset, fromEdgeSet_edgeSet]
  apply NumericPermutations.no_embedding_of_permuted p E d (rep d.card j) (T i)
    hp hr.symm hi
  refine ⟨f, f.injective, ?_⟩
  intro u v huv
  exact hf (hrestore ▸ huv)

/-- Relabeling a graph preserves every injective placement into a host. -/
theorem places_map_equiv {V U W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) (e : V ≃ U) (h : Places G H) :
    Places (G.map e.toEmbedding) H := by
  obtain ⟨f, hf⟩ := h
  refine ⟨e.symm.toEmbedding.trans f, ?_⟩
  intro u v huv
  apply hf
  apply (SimpleGraph.map_adj_apply (f := e.toEmbedding)).mp
  simpa only [Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using huv

lemma edge_ncard_map_equiv {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : V ≃ U) : (G.map e.toEmbedding).edgeSet.ncard = G.edgeSet.ncard := by
  classical
  rw [edge_ncard, edge_ncard]
  exact card_edgeFinset_map e.toEmbedding G

/-- All embeddings into the first host reduce to the three checked allocations.
    This bound is stronger than the requested connected-graph version. -/
theorem order10_bound (T : Fin 2 → SimpleGraph (Fin 19))
    (certificates : ∀ b ∈ allocationLists 0,
      DenseRejected (flatCanonical cycle5 (fun i => (b i).val)) T 34)
    (G : SimpleGraph (Fin 10)) (f0 : Fin 10 ↪ Fin 19)
    (h0 : G ≤ (balancedHost 19)ᶜ.comap f0)
    (hT : ∀ i, Places G (T i)) : G.edgeSet.ncard ≤ 33 := by
  classical
  by_contra hbad
  have hlarge : 34 ≤ G.edgeFinset.card := by
    rw [edge_ncard G] at hbad
    exact Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hbad)
  have hcapacity : ∀ i, fiberSize (@balancedColor 19) i ≤ capacities 0 i := by
    intro i
    exact le_of_eq (balanced_capacity 0 i)
  have hcap : ∀ i, capacities 0 i ≤ 5 := by decide +kernel
  obtain ⟨b, hb, e, he⟩ := normalize_to_allowed_flat 10 34 (by simp)
    (@balancedColor 19) (capacities 0) (allocationLists 0) hcapacity hcap
    allocationCheck10 f0 G h0 hlarge
  have hecard : 34 ≤ (G.map e.toEmbedding).edgeSet.ncard := by
    rw [edge_ncard_map_equiv, edge_ncard]
    exact hlarge
  obtain ⟨i, hi⟩ := certificates b hb (G.map e.toEmbedding) he hecard
  exact hi (places_map_equiv G (T i) e (hT i))

/-- The three named allocation certificates match the finite classifier list. -/
theorem order10_certificates (T : Fin 2 → SimpleGraph (Fin 19))
    (h02404 : DenseRejected (flatCanonical cycle5 ![0,2,4,0,4]) T 34)
    (h03304 : DenseRejected (flatCanonical cycle5 ![0,3,3,0,4]) T 34)
    (h04114 : DenseRejected (flatCanonical cycle5 ![0,4,1,1,4]) T 34) :
    ∀ b ∈ allocationLists 0,
      DenseRejected (flatCanonical cycle5 (fun i => (b i).val)) T 34 := by
  intro b hb
  change b ∈ {![0,2,4,0,4], ![0,3,3,0,4], ![0,4,1,1,4]} at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl
  · have hv : (fun i : Fin 5 => ((![0,2,4,0,4] : Fin 5 → Fin 6) i).val) =
        (![0,2,4,0,4] : Fin 5 → ℕ) := by decide +kernel
    rw [hv]
    exact h02404
  · have hv : (fun i : Fin 5 => ((![0,3,3,0,4] : Fin 5 → Fin 6) i).val) =
        (![0,3,3,0,4] : Fin 5 → ℕ) := by decide +kernel
    rw [hv]
    exact h03304
  · have hv : (fun i : Fin 5 => ((![0,4,1,1,4] : Fin 5 → Fin 6) i).val) =
        (![0,4,1,1,4] : Fin 5 → ℕ) := by decide +kernel
    rw [hv]
    exact h04114

/-- The site's mask convention, copied literally from the target. -/
def siteHost (mask : ℕ) : SimpleGraph (Fin 19) :=
  { Adj := fun i j => i ≠ j ∧ mask.testBit ((min i j).val*19+(max i j).val) = true
    symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
    loopless := ⟨by simp⟩ }

/-- Final three-host wrapper, ready for the actual masks and certified leaves. -/
theorem order10_mask_family (masks : Fin 3 → ℕ)
    (hbalanced : siteHost (masks 0) = balancedHost 19)
    (htriangle : ∀ a, (siteHost (masks a)).CliqueFree 3)
    (certificates : ∀ b ∈ allocationLists 0,
      DenseRejected (flatCanonical cycle5 (fun i => (b i).val))
        (fun i : Fin 2 => (siteHost (masks i.succ))ᶜ) 34) :
    (∀ a, (siteHost (masks a)).CliqueFree 3) ∧
    ∀ f : Fin 3 → Fin 10 ↪ Fin 19,
      let D := ⨅ a, (siteHost (masks a))ᶜ.comap (f a)
      D.Connected → D.edgeSet.ncard ≤ 33 := by
  refine ⟨htriangle, ?_⟩
  intro f D _
  apply order10_bound (fun i : Fin 2 => (siteHost (masks i.succ))ᶜ)
    certificates D (f 0)
  · rw [← hbalanced]
    exact iInf_le _ 0
  · intro i
    exact ⟨f i.succ, iInf_le _ i.succ⟩

end Problem14.H3

-- literal edge-table normalization
namespace Problem14.H3
open SimpleGraph

def A02404_base : SimpleGraph (Fin 10) := flatCanonical cycle5 ![0,2,4,0,4]

instance : DecidableRel A02404_base.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ ¬ cycle5.Adj
    ((finSigmaFinEquiv (n := ![0,2,4,0,4])).symm i).1
    ((finSigmaFinEquiv (n := ![0,2,4,0,4])).symm j).1))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A02404_baseEdges : Order10Orbit.A02404.baseEdges = A02404_base.edgeFinset := by
  have h : ∀ i j : Fin 10, s(i,j) ∈ Order10Orbit.A02404.baseEdges ↔
      A02404_base.Adj i j := by decide +kernel
  apply Finset.ext
  intro e
  refine Sym2.ind ?_ e
  intro i j
  exact (h i j).trans (SimpleGraph.mem_edgeFinset.trans (SimpleGraph.mem_edgeSet A02404_base)).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A02404_depth : Order10Orbit.A02404.baseEdges.card - 34 ≤ Order10Orbit.A02404.depth := by
  decide +kernel

def A03304_base : SimpleGraph (Fin 10) := flatCanonical cycle5 ![0,3,3,0,4]

instance : DecidableRel A03304_base.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ ¬ cycle5.Adj
    ((finSigmaFinEquiv (n := ![0,3,3,0,4])).symm i).1
    ((finSigmaFinEquiv (n := ![0,3,3,0,4])).symm j).1))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A03304_baseEdges : Order10Orbit.A03304.baseEdges = A03304_base.edgeFinset := by
  have h : ∀ i j : Fin 10, s(i,j) ∈ Order10Orbit.A03304.baseEdges ↔
      A03304_base.Adj i j := by decide +kernel
  apply Finset.ext
  intro e
  refine Sym2.ind ?_ e
  intro i j
  exact (h i j).trans (SimpleGraph.mem_edgeFinset.trans (SimpleGraph.mem_edgeSet A03304_base)).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A03304_depth : Order10Orbit.A03304.baseEdges.card - 34 ≤ Order10Orbit.A03304.depth := by
  decide +kernel

def A04114_base : SimpleGraph (Fin 10) := flatCanonical cycle5 ![0,4,1,1,4]

instance : DecidableRel A04114_base.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ ¬ cycle5.Adj
    ((finSigmaFinEquiv (n := ![0,4,1,1,4])).symm i).1
    ((finSigmaFinEquiv (n := ![0,4,1,1,4])).symm j).1))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A04114_baseEdges : Order10Orbit.A04114.baseEdges = A04114_base.edgeFinset := by
  have h : ∀ i j : Fin 10, s(i,j) ∈ Order10Orbit.A04114.baseEdges ↔
      A04114_base.Adj i j := by decide +kernel
  apply Finset.ext
  intro e
  refine Sym2.ind ?_ e
  intro i j
  exact (h i j).trans (SimpleGraph.mem_edgeFinset.trans (SimpleGraph.mem_edgeSet A04114_base)).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A04114_depth : Order10Orbit.A04114.baseEdges.card - 34 ≤ Order10Orbit.A04114.depth := by
  decide +kernel

end Problem14.H3

-- three orbit certificate adapters
namespace Problem14.H3
open SimpleGraph

/-- The checked orbit and leaf tables for allocation 02404. -/
theorem A02404_certificate (T : Fin 2 → SimpleGraph (Fin 19))
    (leaves : ∀ k, k ≤ Order10Orbit.A02404.depth →
      ∀ j, j < Order10Orbit.A02404.count k → ∃ i : Fin 2,
      ¬ ∃ f : Fin 10 → Fin 19, Function.Injective f ∧
        ∀ u v, (Order10Orbit.A02404.graph k j).Adj u v →
          (T i).Adj (f u) (f v)) :
    DenseRejected A02404_base T 34 :=
  denseRejected_of_orbits A02404_base T 34
    Order10Orbit.A02404.depth Order10Orbit.A02404.baseEdges
    A02404_baseEdges A02404_depth Order10Orbit.A02404.count
    Order10Orbit.A02404.representative Order10Orbit.A02404.packedCoverage leaves

/-- The checked orbit and leaf tables for allocation 03304. -/
theorem A03304_certificate (T : Fin 2 → SimpleGraph (Fin 19))
    (leaves : ∀ k, k ≤ Order10Orbit.A03304.depth →
      ∀ j, j < Order10Orbit.A03304.count k → ∃ i : Fin 2,
      ¬ ∃ f : Fin 10 → Fin 19, Function.Injective f ∧
        ∀ u v, (Order10Orbit.A03304.graph k j).Adj u v →
          (T i).Adj (f u) (f v)) :
    DenseRejected A03304_base T 34 :=
  denseRejected_of_orbits A03304_base T 34
    Order10Orbit.A03304.depth Order10Orbit.A03304.baseEdges
    A03304_baseEdges A03304_depth Order10Orbit.A03304.count
    Order10Orbit.A03304.representative Order10Orbit.A03304.packedCoverage leaves

/-- The checked orbit and leaf tables for allocation 04114. -/
theorem A04114_certificate (T : Fin 2 → SimpleGraph (Fin 19))
    (leaves : ∀ k, k ≤ Order10Orbit.A04114.depth →
      ∀ j, j < Order10Orbit.A04114.count k → ∃ i : Fin 2,
      ¬ ∃ f : Fin 10 → Fin 19, Function.Injective f ∧
        ∀ u v, (Order10Orbit.A04114.graph k j).Adj u v →
          (T i).Adj (f u) (f v)) :
    DenseRejected A04114_base T 34 :=
  denseRejected_of_orbits A04114_base T 34
    Order10Orbit.A04114.depth Order10Orbit.A04114.baseEdges
    A04114_baseEdges A04114_depth Order10Orbit.A04114.count
    Order10Orbit.A04114.representative Order10Orbit.A04114.packedCoverage leaves

end Problem14.H3

-- exact target wrapper
namespace Problem14.H3
/-- Exact published-order component, with only the literal host and leaf
    certificates still supplied by their independently checked modules. -/
theorem order10_exact_wrapper (masks : Fin 3 → ℕ)
    (hbalanced : siteHost (masks 0) = balancedHost 19)
    (htriangle : ∀ a, (siteHost (masks a)).CliqueFree 3)
    (certificates : ∀ b ∈ allocationLists 0,
      DenseRejected (flatCanonical cycle5 (fun i => (b i).val))
        (fun i : Fin 2 => (siteHost (masks i.succ))ᶜ) 34) :
    OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1_H3_R1.H1 := by
  refine ⟨3, masks, ?_⟩
  exact order10_mask_family masks hbalanced htriangle certificates
end Problem14.H3

-- literal three-host masks
namespace Problem14.H3
open SimpleGraph

instance (mask : ℕ) : DecidableRel (siteHost mask).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ mask.testBit ((min i j).val*19+(max i j).val) = true))

def balancedMask : ℕ := 4479493756333754369855791731682543007820621221470261340915593863855122242263076652253667222493308471890

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem balancedMask_eq : siteHost balancedMask = balancedHost 19 := by
  have h : ∀ i j : Fin 19, (siteHost balancedMask).Adj i j ↔
      (balancedHost 19).Adj i j := by decide +kernel
  ext i j
  exact h i j

def order10Masks : Fin 3 → ℕ :=
  ![balancedMask, Order10Common.mask0, Order10Common.mask1]

theorem order10Masks_triangleFree :
    ∀ i, (siteHost (order10Masks i)).CliqueFree 3 := by
  intro i
  fin_cases i
  · change (siteHost balancedMask).CliqueFree 3
    rw [balancedMask_eq]
    exact balancedHost_triangleFree 19
  · exact Order10Common.encoded0_triangle_free
  · exact Order10Common.encoded1_triangle_free

theorem order10Masks_targets :
    (fun i : Fin 2 => (siteHost (order10Masks i.succ))ᶜ) = Order10Common.targets := by
  funext i
  fin_cases i
  · change (Order10Common.encoded Order10Common.mask0)ᶜ = Order10Common.target
    rw [← Order10Common.encoded0_eq]
    exact compl_compl _
  · change (Order10Common.encoded Order10Common.mask1)ᶜ = Order10Common.targetOther
    rw [← Order10Common.encoded1_eq]
    exact compl_compl _

/-- Closing this theorem requires precisely the three finite orbit/leaf certificates. -/
theorem order10_from_three_certificates
    (h02404 : DenseRejected (flatCanonical cycle5 ![0,2,4,0,4]) Order10Common.targets 34)
    (h03304 : DenseRejected (flatCanonical cycle5 ![0,3,3,0,4]) Order10Common.targets 34)
    (h04114 : DenseRejected (flatCanonical cycle5 ![0,4,1,1,4]) Order10Common.targets 34) :
    OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1_H3_R1.H1 := by
  apply order10_exact_wrapper order10Masks balancedMask_eq order10Masks_triangleFree
  rw [order10Masks_targets]
  exact order10_certificates _ h02404 h03304 h04114

end Problem14.H3

theorem OMA.solution : OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1_H3_R1.H1 := by
  apply Problem14.H3.order10_from_three_certificates
  · exact Problem14.H3.A02404_certificate _
      (Order10Leaves.all_A02404 Order10Search56.no_embedding Order10Search72.no_embedding
        Order10Search94.no_embedding Order10Search103.no_embedding Order10Search106.no_embedding)
  · exact Problem14.H3.A03304_certificate _
      (Order10Leaves.all_A03304 Order10Search129.no_embedding Order10Search132.no_embedding)
  · exact Problem14.H3.A04114_certificate _ Order10Leaves.all_A04114
