import OMAReductions.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1

import Mathlib

/-! Formalization of the total coloring bounds of A. V. Kostochka, Discrete Mathematics 162 (1996), 199–214. -/


section -- MultiCore

/- Loopless finite multigraphs, as used in Sections 4–6 of Kostochka (1996).
An unordered pair of vertices receives a set of colors of the prescribed size,
so parallel edges have distinct colors. -/
namespace MultFive
open Finset SimpleGraph

structure Multi (V : Type*) where
  count : V → V → ℕ
  symm : ∀ x y, count x y = count y x
  loopless : ∀ x, count x x = 0

namespace Multi
variable {V : Type*} (m : Multi V)

def degree [Fintype V] (v : V) : ℕ := ∑ w, m.count v w

def support : SimpleGraph V where
  Adj v w := 0 < m.count v w
  symm := ⟨fun v w h => by rwa [← m.symm v w]⟩
  loopless := ⟨fun x => by simp [m.loopless]⟩

instance : DecidableRel m.support.Adj := fun x y => inferInstanceAs (Decidable (0 < m.count x y))

def induce (s : Set V) : Multi s where
  count x y := m.count x.val y.val
  symm x y := m.symm x.val y.val
  loopless x := m.loopless x.val

/-- Add an edge even when the given endpoints are already adjacent. -/
def addEdge [DecidableEq V] (a b : V) (ne : a ≠ b) : Multi V where
  count x y := m.count x y + if (x = a ∧ y = b) ∨ (x = b ∧ y = a) then 1 else 0
  symm x y := by rw [m.symm x y]; congr 2; grind
  loopless x := by simp only [m.loopless, zero_add]; split <;> grind

/-- A proper total coloring with seven colors. Each neighbor receives its own
set of edge colors and the size of that set is the number of parallel edges. -/
structure Valid (vc : V → Fin 7) (ec : V → V → Finset (Fin 7)) : Prop where
  symmetric : ∀ x y, ec x y = ec y x
  size : ∀ x y, (ec x y).card = m.count x y
  vertices : ∀ x y, 0 < m.count x y → vc x ≠ vc y
  avoids : ∀ x y, vc x ∉ ec x y
  disjoint : ∀ x y z, y ≠ z → Disjoint (ec x y) (ec x z)

def Colorable : Prop := ∃ vc ec, m.Valid vc ec

theorem Valid.induce {vc ec} (h : m.Valid vc ec) (s : Set V) :
    (m.induce s).Valid (fun x => vc x.val) (fun x y => ec x.val y.val) where
  symmetric x y := h.symmetric x.val y.val
  size x y := h.size x.val y.val
  vertices x y := h.vertices x.val y.val
  avoids x y := h.avoids x.val y.val
  disjoint x y z ne := h.disjoint x.val y.val z.val (fun eq => ne (Subtype.ext eq))

theorem Colorable.induce (h : m.Colorable) (s : Set V) : (m.induce s).Colorable := by
  obtain ⟨vc,ec,h⟩ := h
  exact ⟨_,_, h.induce m s⟩

end Multi

/-- The one-copy multiplicities of a simple graph. -/
def ofSimple {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] : Multi V where
  count x y := if G.Adj x y then 1 else 0
  symm x y := by simp only [G.adj_comm x y]
  loopless x := by simp

theorem degree_ofSimple {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (ofSimple G).degree v = G.degree v := by
  classical
  simp only [Multi.degree, ofSimple, Finset.sum_boole, ← G.neighborFinset_eq_filter, card_neighborFinset_eq_degree]
  rfl

end MultFive

end


section -- MultiHubGlue

/- Kostochka's Lemma 6, in the presence of parallel edges. A permutation of
each wing's palette aligns the hub colors and places all incident colors in
pairwise distinct slots at the hub. -/
namespace MultFive.Multi
open Finset

private theorem alignColors {J P : Type*} [Finite J] (a b : J → P)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    ∃ p : Equiv.Perm P, ∀ j, p (a j) = b j := by
  classical
  let _ := Fintype.ofFinite J
  suffices h : ∀ s : Finset J, ∃ p : Equiv.Perm P, ∀ j ∈ s, p (a j) = b j by
    obtain ⟨p,hp⟩ := h univ
    exact ⟨p,fun i => hp i (mem_univ _)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨Equiv.refl _,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨p,hp⟩ := ih
    refine ⟨p.trans (Equiv.swap (p (a i)) (b i)),?_⟩
    intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · exact Equiv.swap_apply_left _ _
    · have ne : j ≠ i := fun eq => hi (eq ▸ hj)
      rw [Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne (p.injective.ne (ha.ne ne))
        ((hp j hj).trans_ne (hb.ne ne)),hp j hj]

private def mark (s : Bool → Finset (Fin 7)) :
    (b : Bool) → s b → (s false ⊕ s true)
  | false => Sum.inl
  | true => Sum.inr

/-- Align the hub colors and separate the two sets of incident colors. -/
private theorem hubPalette (c : Bool → Fin 7) (s : Bool → Finset (Fin 7))
    (fresh : ∀ b, c b ∉ s b) (space : (s false).card + (s true).card ≤ 6) :
    ∃ p : Bool → Equiv.Perm (Fin 7), p false (c false) = p true (c true) ∧
      ∀ i ∈ s false, ∀ j ∈ s true, p false i ≠ p true j := by
  classical
  let target : Option (s false ⊕ s true) ↪ Fin 7 :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simp; omega))
  let old (b : Bool) : Option (s b) → Fin 7 := Option.elim' (c b) Subtype.val
  have inj (b : Bool) : Function.Injective (old b) := by
    rintro (_ | i) (_ | j) eq
    · rfl
    · change c b = j.val at eq
      exact (fresh b (eq ▸ j.property)).elim
    · change i.val = c b at eq
      exact (fresh b (eq ▸ i.property)).elim
    · exact congrArg some (Subtype.ext eq)
  have mi (b) : Function.Injective (mark s b) := by cases b; exact Sum.inl_injective; exact Sum.inr_injective
  have goal (b) := alignColors (old b) (target ∘ Option.map (mark s b)) (inj b)
    (target.injective.comp (Option.map_injective (mi b)))
  choose p hp using goal
  refine ⟨p,(hp false none).trans (hp true none).symm,?_⟩
  intro i hi j hj eq
  have a := hp false (some ⟨i,hi⟩)
  have b := hp true (some ⟨j,hj⟩)
  have bad := target.injective (a.symm.trans (eq.trans b))
  simp [mark] at bad

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem wingCount {A : Type*} [DecidableEq A] (x y h : A) (p : A → Bool) (n : ℕ)
    (ne : x ≠ y) (split : x ≠ h → y ≠ h → p x = p y) :
    (if (x = h ∨ p x = false) ∧ (y = h ∨ p y = false) then n else 0) +
    (if (x = h ∨ p x = true) ∧ (y = h ∨ p y = true) then n else 0) = n := by
  by_cases hx : x = h
  · subst x
    cases p y <;> simp [ne.symm]
  by_cases hy : y = h
  · subst y
    cases p x <;> simp [ne]
  have eq := split hx hy
  cases px : p x <;> simp [hx,hy,←eq,px]

/-- Glue two induced subgraphs whose only possible shared vertex is the hub. -/
theorem glueInducedHub (m : Multi V) (hub : V) (part : V → Bool)
    (split : ∀ x y, 0 < m.count x y → x ≠ hub → y ≠ hub → part x = part y)
    (deg : m.degree hub ≤ 6)
    (wings : ∀ b, (m.induce {v | v = hub ∨ part v = b}).Colorable) : m.Colorable := by
  classical
  let side (b : Bool) (v : V) := v = hub ∨ part v = b
  have here (b) : side b hub := Or.inl rfl
  choose vertex edge good using wings
  let vcol (b : Bool) (x : V) := if h : side b x then vertex b ⟨x,h⟩ else vertex b ⟨hub,here b⟩
  let ecol (b : Bool) (x y : V) := if h : side b x ∧ side b y then edge b ⟨x,h.1⟩ ⟨y,h.2⟩ else ∅
  have size (b x y) : (ecol b x y).card = if side b x ∧ side b y then m.count x y else 0 := by
    by_cases h : side b x ∧ side b y
    · simpa [ecol,h,induce] using (good b).size ⟨x,h.1⟩ ⟨y,h.2⟩
    · simp [ecol,h]
  have sym (b x y) : ecol b x y = ecol b y x := by
    by_cases h : side b x ∧ side b y
    · simpa [ecol,h,h.symm] using (good b).symmetric ⟨x,h.1⟩ ⟨y,h.2⟩
    · have hn := not_congr and_comm |>.mp h
      simp [ecol,h,hn]
  have touch {b x y k} (hit : k ∈ ecol b x y) : side b x ∧ side b y := by
    by_contra hn; simp [ecol,hn] at hit
  have apart (b x y z) (ne : y ≠ z) : Disjoint (ecol b x y) (ecol b x z) := by
    apply disjoint_left.mpr
    intro k hy hz
    have hxy := touch hy
    have hxz := touch hz
    exact disjoint_left.mp ((good b).disjoint ⟨x,hxy.1⟩ ⟨y,hxy.2⟩ ⟨z,hxz.2⟩
      (fun eq => ne (congrArg Subtype.val eq)))
      (by simpa only [ecol,dif_pos hxy] using hy) (by simpa only [ecol,dif_pos hxz] using hz)
  have avoid (b x y) : vcol b x ∉ ecol b x y := by
    intro hit
    obtain ⟨hx,hy⟩ := touch hit
    exact (good b).avoids ⟨x,hx⟩ ⟨y,hy⟩ (by simpa [vcol,ecol,hx,hy] using hit)
  have counts (x y) : (ecol false x y).card + (ecol true x y).card = m.count x y := by
    rw [size,size]
    by_cases pos : 0 < m.count x y
    · have xy : x ≠ y := fun eq => by subst y; simp [m.loopless] at pos
      exact wingCount x y hub part _ xy (split x y pos)
    · have hz : m.count x y = 0 := by omega
      simp [hz]
  let used (b : Bool) := univ.biUnion (ecol b hub)
  have fresh (b : Bool) : vcol b hub ∉ used b := by simpa [used] using avoid b hub
  have space : (used false).card + (used true).card ≤ 6 := by
    have l := card_biUnion_le (s := (univ : Finset V)) (t := ecol false hub)
    have r := card_biUnion_le (s := (univ : Finset V)) (t := ecol true hub)
    have t : ∑ x, (ecol false hub x).card + ∑ x, (ecol true hub x).card = m.degree hub := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun x _ => counts hub x
    dsimp [used]; omega
  obtain ⟨p,center,gap⟩ := hubPalette (fun b => vcol b hub) used fresh space
  let vc (x : V) := p (part x) (vcol (part x) x)
  have agree (b x) (h : side b x) : vc x = p b (vcol b x) := by
    rcases h with h | he
    · subst x
      cases hh : part hub <;> cases b <;> simp [vc,hh,center]
    · simp [vc,he]
  let set (b x y) := (ecol b x y).map (p b).toEmbedding
  have clash {b d x y z k} (hb : k ∈ set b x y) (hd : k ∈ set d x z) (bd : b ≠ d) : False := by
    obtain ⟨i,hi,ei⟩ := mem_map.mp hb
    obtain ⟨j,hj,ej⟩ := mem_map.mp hd
    have hx : x = hub := by
      obtain h | h := (touch hi).1
      · exact h
      · obtain h' | h' := (touch hj).1
        · exact h'
        · exact (bd (h.symm.trans h')).elim
    subst x
    have hu : i ∈ used b := mem_biUnion.mpr ⟨y,mem_univ _,hi⟩
    have hv : j ∈ used d := mem_biUnion.mpr ⟨z,mem_univ _,hj⟩
    cases b <;> cases d
    · contradiction
    · exact gap i hu j hv (ei.trans ej.symm)
    · exact gap j hv i hu (ej.trans ei.symm)
    · contradiction
  let ec x y := set false x y ∪ set true x y
  refine ⟨vc,ec,?_⟩
  constructor
  · intro x y; simp only [ec,set,sym _ x y]
  · intro x y
    have dj : Disjoint (set false x y) (set true x y) :=
      disjoint_left.mpr fun _ hl hr => clash hl hr (by decide)
    simpa [ec,card_union_of_disjoint dj,set] using counts x y
  · intro x y pos
    have e : ∃ b, side b x ∧ side b y := by
      by_cases hx : x = hub
      · exact ⟨part y,Or.inl hx,Or.inr rfl⟩
      by_cases hy : y = hub
      · exact ⟨part x,Or.inr rfl,Or.inl hy⟩
      exact ⟨part y,Or.inr (split _ _ pos hx hy),Or.inr rfl⟩
    obtain ⟨b,hx,hy⟩ := e
    rw [agree b x hx,agree b y hy]
    exact (p b).injective.ne (by simpa [vcol,hx,hy] using (good b).vertices ⟨x,hx⟩ ⟨y,hy⟩ pos)
  · intro x y hit
    have bad (b) (h : vc x ∈ set b x y) : False := by
      obtain ⟨i,hi,eq⟩ := mem_map.mp h
      have he := agree b x (touch hi).1
      exact avoid b x y ((p b).injective (eq.trans he) ▸ hi)
    exact (mem_union.mp hit).elim (bad false) (bad true)
  · intro x y z ne
    apply disjoint_left.mpr
    intro k hy hz
    have diff (b) (a : k ∈ set b x y) (c : k ∈ set b x z) : False :=
      disjoint_left.mp (show Disjoint (set b x y) (set b x z) by simpa [set] using apart b x y z ne) a c
    rcases mem_union.mp hy with l | r <;> rcases mem_union.mp hz with l' | r'
    · exact diff false l l'
    · exact clash l r' (by decide)
    · exact clash r l' (by decide)
    · exact diff true r r'

end MultFive.Multi

end


section -- CutGlueTutte

/-
The odd-cut count in the final argument of A. V. Kostochka, Discrete
Mathematics 162 (1996), Theorem 3. Cut sizes count edges from their unique
endpoint on the chosen side.
-/

namespace TotalColorFive

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Number of edges from `s` to its complement. -/
def cutSize (s : Finset V) : ℕ := ∑ v ∈ s, ((G.neighborFinset v) \ s).card

/-- Handshaking on the induced graph counts internal edges twice. -/
theorem degreeSumOn (s : Finset V) :
    ∑ v ∈ s, G.degree v = 2 * (G.induce (s : Set V)).edgeFinset.card + cutSize G s := by
  classical
  let H := G.induce (s : Set V)
  have atV (v : (s : Set V)) : (H.neighborFinset v).card = ((G.neighborFinset v) ∩ s).card := by
    have h : (H.neighborFinset v).map (.subtype (· ∈ (s : Set V))) = G.neighborFinset v ∩ s := by
      ext x
      simp [H]
    rw [← h, Finset.card_map]
  have inner : (∑ v ∈ s, ((G.neighborFinset v) ∩ s).card) = 2 * H.edgeFinset.card := by
    rw [← H.sum_degrees_eq_twice_card_edges]
    rw [← Finset.sum_attach s]
    exact Finset.sum_congr rfl fun v _ => (atV v).symm
  rw [← inner, cutSize, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  change (G.neighborFinset v).card = _
  rw [Nat.add_comm, Finset.card_sdiff_add_card_inter]

/-- An odd vertex set in a 5-regular graph has an odd edge boundary. -/
theorem odd_cutSize (regular : ∀ v, G.degree v = 5) {s : Finset V} (h : Odd s.card) :
    Odd (cutSize G s) := by
  have hs := degreeSumOn G s
  simp only [regular, Finset.sum_const, smul_eq_mul] at hs
  obtain ⟨k, hk⟩ := h
  rw [Nat.odd_iff]
  omega

/-- Three of the odd components must have fewer than five outgoing edges. -/
theorem threeSmallOddCounts {ι : Type*} (s : Finset ι) (out : ι → ℕ) (n : ℕ)
    (more : n + 2 ≤ s.card) (odd : ∀ i ∈ s, Odd (out i))
    (room : ∑ i ∈ s, out i ≤ 5 * n) : 3 ≤ (s.filter fun i => out i ≤ 3).card := by
  classical
  have one (i) (hi : i ∈ s) : 5 ≤ out i + (if out i ≤ 3 then 4 else 0) := by
    obtain ⟨k, hk⟩ := odd i hi
    split <;> omega
  have h := Finset.sum_le_sum one
  simp only [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_ite] at h
  omega

private theorem countInto (u : Finset V) :
    (∑ v : V, ((G.neighborFinset v) ∩ u).card) = ∑ w ∈ u, G.degree w := by
  classical
  have row (v) : ((G.neighborFinset v) ∩ u).card = ∑ w ∈ u, if G.Adj w v then 1 else 0 := by
    rw [Finset.sum_boole]
    congr 1
    ext w
    simp [and_comm, G.adj_comm]
  simp_rw [row]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.sum_boole]
  change _ = (G.neighborFinset w).card
  rw [G.neighborFinset_eq_filter]
  simp

/-- The pieces of a vertex-deletion graph have pairwise disjoint carriers.
Their only external neighbours belong to the deleted set. -/
private theorem countSeparatedCuts {ι : Type*} (u : Finset V) (s : Finset ι)
    (pieces : ι → Finset V) (disj : (s : Set ι).PairwiseDisjoint pieces)
    (extNbr : ∀ i ∈ s, ∀ v ∈ pieces i, (G.neighborFinset v) \ pieces i ⊆ u) :
    (∑ i ∈ s, cutSize G (pieces i)) ≤ ∑ v ∈ u, G.degree v := by
  classical
  rw [← countInto]
  calc
    _ ≤ ∑ i ∈ s, ∑ v ∈ pieces i, ((G.neighborFinset v) ∩ u).card := by
      exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun v hv =>
        Finset.card_le_card (fun w hw => Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hw).1, extNbr i hi v hv hw⟩)
    _ = ∑ v ∈ s.biUnion pieces, ((G.neighborFinset v) ∩ u).card := (Finset.sum_biUnion disj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- A finite 5-regular simple graph without a perfect matching has a separator
with at least three pairwise disjoint odd pieces, each sending either one or
three edges to the separator. Every neighbor outside a piece belongs to that
same separator. This is the Tutte count in Kostochka's Theorem 3. -/
theorem threeSmallOddCuts (regular : ∀ v, G.degree v = 5)
    (unmatched : ¬ ∃ M : G.Subgraph, M.IsPerfectMatching) :
    ∃ (u : Finset V) (pieces : Finset (Finset V)), 3 ≤ pieces.card ∧
      (pieces : Set (Finset V)).PairwiseDisjoint id ∧
      ∀ c ∈ pieces, Odd c.card ∧ Disjoint c u ∧ (cutSize G c = 1 ∨ cutSize G c = 3) ∧
        ∀ v ∈ c, (G.neighborFinset v) \ c ⊆ u := by
  classical
  obtain ⟨U, hu⟩ : ∃ U, G.IsTutteViolator U := by
    by_contra! h
    exact unmatched (G.tutte.mpr h)
  let D := (⊤ : G.Subgraph).deleteVerts U
  let H := D.coe
  let : Fintype D.verts := Fintype.ofFinite _
  let : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let u := U.toFinset
  let cs := H.oddComponents.toFinset
  let verts (c : H.ConnectedComponent) : Finset V := c.supp.toFinset.map (Function.Embedding.subtype _)
  have hcard (c) : (verts c).card = c.supp.ncard := by simp only [verts, Finset.card_map, ← Set.ncard_eq_toFinset_card']
  have nons (v : V) (hv : v ∉ U) : v ∈ D.verts := ⟨Set.mem_univ _, hv⟩
  have hmem (c : H.ConnectedComponent) (v : V) : v ∈ verts c ↔ ∃ hv : v ∈ D.verts, H.connectedComponentMk ⟨v,hv⟩ = c := by
    change v ∈ c.supp.toFinset.map (Function.Embedding.subtype _) ↔ _
    rw [Finset.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h : w ∈ c.supp := Set.mem_toFinset.mp hw
      exact ⟨w.2, h⟩
    · rintro ⟨h, hh⟩
      have hm : (⟨v,h⟩ : D.verts) ∈ c.supp := hh
      exact ⟨⟨v,h⟩, Set.mem_toFinset.mpr hm, rfl⟩
  have pinj : Function.Injective verts := by
    intro a b hab
    obtain ⟨v,hv⟩ := a.nonempty_supp
    have ha : v.val ∈ verts a := (hmem _ _).mpr ⟨v.property, hv⟩
    obtain ⟨_, hb⟩ := (hmem _ _).mp (hab ▸ ha)
    exact (show H.connectedComponentMk v = a from hv).symm.trans hb
  have dverts {c d : H.ConnectedComponent} (hne : c ≠ d) : Disjoint (verts c) (verts d) := by
    apply Finset.disjoint_left.mpr
    intro v hc hd
    obtain ⟨_, hv⟩ := (hmem _ _).mp hc
    obtain ⟨_, hw⟩ := (hmem _ _).mp hd
    exact hne (hv.symm.trans hw)
  have extNbr (c : H.ConnectedComponent) (v : V) (hv : v ∈ verts c) :
      G.neighborFinset v \ verts c ⊆ u := by
    intro w hw
    obtain ⟨hvw, hnc⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨hs, hcomp⟩ := (hmem _ _).mp hv
    by_contra hn
    have hd := nons w (by simpa [u] using hn)
    have ha : H.Adj ⟨v,hs⟩ ⟨w,hd⟩ := by
      exact Subgraph.deleteVerts_adj.mpr ⟨Set.mem_univ _, hs.2, Set.mem_univ _, hd.2, (G.mem_neighborFinset _ _).mp hvw⟩
    exact hnc ((hmem _ _).mpr ⟨hd, (ConnectedComponent.connectedComponentMk_eq_of_adj ha).symm.trans hcomp⟩)
  have hodd (c : H.ConnectedComponent) (h : c ∈ cs) : Odd (verts c).card := by
    rw [hcard]
    exact (Set.mem_toFinset.mp h : c ∈ H.oddComponents)
  have count := countSeparatedCuts G u cs verts (fun _ _ _ _ h => dverts h) (fun c _ => extNbr c)
  simp only [regular, Finset.sum_const, smul_eq_mul] at count
  have ht : u.card < cs.card := by
    simpa only [u, cs, H, D, IsTutteViolator, ← Set.ncard_eq_toFinset_card'] using hu
  have evenOrder : Even (Fintype.card V) := by
    have hs := G.sum_degrees_eq_twice_card_edges
    simp only [regular, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
    rw [Nat.even_iff]
    omega
  have hdiff : Nat.card D.verts + u.card = Fintype.card V := by
    have he : D.verts = Uᶜ := by ext v; simp [D]
    rw [he, Nat.card_coe_set_eq]
    simpa only [u, ← Set.ncard_eq_toFinset_card', Nat.card_eq_fintype_card] using U.ncard_compl_add_ncard
  have parity : Odd cs.card ↔ Odd (Nat.card D.verts) := by simpa only [cs, ← Set.ncard_eq_toFinset_card'] using H.odd_ncard_oddComponents
  have more : u.card + 2 ≤ cs.card := by
    rw [Nat.odd_iff, Nat.odd_iff] at parity
    rw [Nat.even_iff] at evenOrder
    omega
  let small := cs.filter fun c => cutSize G (verts c) ≤ 3
  have smallcard : 3 ≤ small.card := threeSmallOddCounts cs _ u.card more
    (fun c hc => odd_cutSize G regular (hodd c hc)) (by simpa [Nat.mul_comm] using count)
  refine ⟨u, small.image verts, ?_, ?_, ?_⟩
  · rwa [Finset.card_image_of_injective _ pinj]
  · intro a ha b hb hab
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
    exact dverts fun h => hab (congrArg verts h)
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨ha, hsize⟩ := Finset.mem_filter.mp ha
    have odd := hodd a ha
    refine ⟨odd, ?_, ?_, extNbr a⟩
    · apply Finset.disjoint_left.mpr
      intro v hv hin
      obtain ⟨hd,_⟩ := (hmem _ _).mp hv
      exact hd.2 (Set.mem_toFinset.mp hin)
    · obtain ⟨k,hk⟩ := odd_cutSize G regular odd
      omega

end TotalColorFive

end


section -- MultiTutte

/- Tutte's separator and small odd cuts, counting every parallel edge with its multiplicity. -/
namespace MultFive.Multi
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (m : Multi V)

def cutSize (s : Finset V) : ℕ := ∑ x ∈ s, ∑ y ∈ sᶜ, m.count x y

omit [Fintype V] in
private theorem even_internal (s : Finset V) : Even (∑ x ∈ s, ∑ y ∈ s, m.count x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s na ih =>
    obtain ⟨k,hk⟩ := ih
    simp only [sum_insert na, m.loopless, zero_add, sum_add_distrib]
    rw [hk]
    refine ⟨(∑ x ∈ s, m.count a x) + k, ?_⟩
    have h : ∑ x ∈ s, m.count x a = ∑ x ∈ s, m.count a x := by
      exact sum_congr rfl fun x _ => m.symm x a
    rw [h]; omega

private theorem degreeSum (s : Finset V) : (∑ x ∈ s, m.degree x) =
    (∑ x ∈ s, ∑ y ∈ s, m.count x y) + m.cutSize s := by
  rw [cutSize, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => (sum_add_sum_compl s (m.count x)).symm

theorem odd_regular_cut (reg : ∀ v, m.degree v = 5) {s : Finset V} (h : Odd s.card) :
    Odd (m.cutSize s) := by
  have a := degreeSum m s
  obtain ⟨k,hk⟩ := even_internal m s
  obtain ⟨l,hl⟩ := h
  simp only [reg, sum_const, smul_eq_mul] at a
  rw [Nat.odd_iff]; omega

private theorem countSeparated {ι : Type*} (u : Finset V) (s : Finset ι)
    (pieces : ι → Finset V) (disj : (s : Set ι).PairwiseDisjoint pieces)
    (external : ∀ i ∈ s, ∀ v ∈ pieces i, (m.support.neighborFinset v) \ pieces i ⊆ u) :
    (∑ i ∈ s, m.cutSize (pieces i)) ≤ ∑ w ∈ u, m.degree w := by
  classical
  calc
    (∑ i ∈ s, m.cutSize (pieces i)) ≤ ∑ i ∈ s, ∑ v ∈ pieces i, ∑ w ∈ u, m.count v w := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro v hv
      apply le_trans (b := ∑ w ∈ (pieces i)ᶜ ∩ u, m.count v w)
      · apply le_of_eq
        apply (Finset.sum_subset Finset.inter_subset_left _).symm
        intro w hw hn
        by_contra nonzero
        have adj : m.support.Adj v w := Nat.pos_of_ne_zero nonzero
        exact hn (mem_inter.mpr ⟨hw, external i hi v hv (mem_sdiff.mpr
          ⟨(m.support.mem_neighborFinset _ _).mpr adj, mem_compl.mp hw⟩)⟩)
      · exact sum_le_sum_of_subset inter_subset_right
    _ = ∑ v ∈ s.biUnion pieces, ∑ w ∈ u, m.count v w := (sum_biUnion disj).symm
    _ ≤ ∑ v : V, ∑ w ∈ u, m.count v w := sum_le_sum_of_subset (subset_univ _)
    _ = _ := by
      rw [sum_comm]
      exact sum_congr rfl fun w _ => sum_congr rfl fun v _ => m.symm v w

/-- A finite 5-regular loopless multigraph without a perfect matching has a separator
with at least three pairwise disjoint odd pieces, each sending either one or
three edges to the separator. Every neighbor outside a piece belongs to that
same separator. This is the Tutte count in Kostochka's Theorem 3. -/
theorem threeSmallOddCuts (regular : ∀ v, m.degree v = 5)
    (unmatched : ¬ ∃ M : m.support.Subgraph, M.IsPerfectMatching) :
    ∃ (u : Finset V) (pieces : Finset (Finset V)), 3 ≤ pieces.card ∧
      (pieces : Set (Finset V)).PairwiseDisjoint id ∧
      ∀ c ∈ pieces, Odd c.card ∧ Disjoint c u ∧ (m.cutSize c = 1 ∨ m.cutSize c = 3) ∧
        ∀ v ∈ c, (m.support.neighborFinset v) \ c ⊆ u := by
  classical
  obtain ⟨U, hu⟩ : ∃ U, m.support.IsTutteViolator U := by
    by_contra! h
    exact unmatched (m.support.tutte.mpr h)
  let D := (⊤ : m.support.Subgraph).deleteVerts U
  let H := D.coe
  let : Fintype D.verts := Fintype.ofFinite _
  let : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let u := U.toFinset
  let cs := H.oddComponents.toFinset
  let verts (c : H.ConnectedComponent) : Finset V := c.supp.toFinset.map (Function.Embedding.subtype _)
  have hcard (c) : (verts c).card = c.supp.ncard := by simp only [verts, Finset.card_map, ← Set.ncard_eq_toFinset_card']
  have nons (v : V) (hv : v ∉ U) : v ∈ D.verts := ⟨Set.mem_univ _, hv⟩
  have hmem (c : H.ConnectedComponent) (v : V) : v ∈ verts c ↔ ∃ hv : v ∈ D.verts, H.connectedComponentMk ⟨v,hv⟩ = c := by
    change v ∈ c.supp.toFinset.map (Function.Embedding.subtype _) ↔ _
    rw [Finset.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h : w ∈ c.supp := Set.mem_toFinset.mp hw
      exact ⟨w.2, h⟩
    · rintro ⟨h, hh⟩
      have hm : (⟨v,h⟩ : D.verts) ∈ c.supp := hh
      exact ⟨⟨v,h⟩, Set.mem_toFinset.mpr hm, rfl⟩
  have pinj : Function.Injective verts := by
    intro a b hab
    obtain ⟨v,hv⟩ := a.nonempty_supp
    have ha : v.val ∈ verts a := (hmem _ _).mpr ⟨v.property, hv⟩
    obtain ⟨_, hb⟩ := (hmem _ _).mp (hab ▸ ha)
    exact (show H.connectedComponentMk v = a from hv).symm.trans hb
  have dverts {c d : H.ConnectedComponent} (hne : c ≠ d) : Disjoint (verts c) (verts d) := by
    apply Finset.disjoint_left.mpr
    intro v hc hd
    obtain ⟨_, hv⟩ := (hmem _ _).mp hc
    obtain ⟨_, hw⟩ := (hmem _ _).mp hd
    exact hne (hv.symm.trans hw)
  have extNbr (c : H.ConnectedComponent) (v : V) (hv : v ∈ verts c) :
      m.support.neighborFinset v \ verts c ⊆ u := by
    intro w hw
    obtain ⟨hvw, hnc⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨hs, hcomp⟩ := (hmem _ _).mp hv
    by_contra hn
    have hd := nons w (by simpa [u] using hn)
    have ha : H.Adj ⟨v,hs⟩ ⟨w,hd⟩ := by
      exact Subgraph.deleteVerts_adj.mpr ⟨Set.mem_univ _, hs.2, Set.mem_univ _, hd.2, (m.support.mem_neighborFinset _ _).mp hvw⟩
    exact hnc ((hmem _ _).mpr ⟨hd, (ConnectedComponent.connectedComponentMk_eq_of_adj ha).symm.trans hcomp⟩)
  have hodd (c : H.ConnectedComponent) (h : c ∈ cs) : Odd (verts c).card := by
    rw [hcard]
    exact (Set.mem_toFinset.mp h : c ∈ H.oddComponents)
  have count := countSeparated m u cs verts (fun _ _ _ _ h => dverts h) (fun c _ => extNbr c)
  simp only [regular, Finset.sum_const, smul_eq_mul] at count
  have ht : u.card < cs.card := by
    simpa only [u, cs, H, D, IsTutteViolator, ← Set.ncard_eq_toFinset_card'] using hu
  have evenOrder : Even (Fintype.card V) := by
    have e := even_internal m (univ : Finset V)
    change Even (∑ v : V, m.degree v) at e
    simp only [regular, Finset.sum_const, Finset.card_univ, smul_eq_mul] at e
    rw [Nat.even_iff] at e ⊢
    omega
  have hdiff : Nat.card D.verts + u.card = Fintype.card V := by
    have he : D.verts = Uᶜ := by ext v; simp [D]
    rw [he, Nat.card_coe_set_eq]
    simpa only [u, ← Set.ncard_eq_toFinset_card', Nat.card_eq_fintype_card] using U.ncard_compl_add_ncard
  have parity : Odd cs.card ↔ Odd (Nat.card D.verts) := by simpa only [cs, ← Set.ncard_eq_toFinset_card'] using H.odd_ncard_oddComponents
  have more : u.card + 2 ≤ cs.card := by
    rw [Nat.odd_iff, Nat.odd_iff] at parity
    rw [Nat.even_iff] at evenOrder
    omega
  let small := cs.filter fun c => m.cutSize (verts c) ≤ 3
  have smallcard : 3 ≤ small.card := TotalColorFive.threeSmallOddCounts cs _ u.card more
    (fun c hc => odd_regular_cut m regular (hodd c hc)) (by simpa [Nat.mul_comm] using count)
  refine ⟨u, small.image verts, ?_, ?_, ?_⟩
  · rwa [Finset.card_image_of_injective _ pinj]
  · intro a ha b hb hab
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
    exact dverts fun h => hab (congrArg verts h)
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨ha, hsize⟩ := Finset.mem_filter.mp ha
    have odd := hodd a ha
    refine ⟨odd, ?_, ?_, extNbr a⟩
    · apply Finset.disjoint_left.mpr
      intro v hv hin
      obtain ⟨hd,_⟩ := (hmem _ _).mp hv
      exact hd.2 (Set.mem_toFinset.mp hin)
    · obtain ⟨k,hk⟩ := odd_regular_cut m regular odd
      omega


end MultFive.Multi

end


section -- CutGlue

/-
The three-edge cut recoloring argument of A. V. Kostochka, Discrete Mathematics
162 (1996), Lemma 7. A permutation of the palette on one side of the cut fixes
all three edge colors and removes the remaining vertex conflicts.
-/

namespace TotalColorFive

/-- A single switch on the right side fixes the conflict at `j` and keeps every
previously separated pair distinct. -/
private theorem repairCutPair (left right edge : Fin 3 → Fin 7) (j : Fin 3)
    (conflict : left j = right j) (fresh : ∀ k, left j ≠ edge k) :
    ∃ p : Equiv.Perm (Fin 7), (∀ k, p (edge k) = edge k) ∧
      left j ≠ p (right j) ∧ ∀ i, left i ≠ right i → left i ≠ p (right i) := by
  classical
  let a := left j
  let avoid (i : Fin 3) := if left i = a then right i else left i
  let forbidden := Finset.univ.image edge ∪ Finset.univ.image avoid
  have hcard : forbidden.card ≤ 3 + 3 := by
    refine (Finset.card_union_le _ _).trans ?_
    exact Nat.add_le_add ((Finset.card_image_le).trans (by decide : (Finset.univ : Finset (Fin 3)).card ≤ 3))
      ((Finset.card_image_le).trans (by decide : (Finset.univ : Finset (Fin 3)).card ≤ 3))
  obtain ⟨b, hb⟩ : ∃ b : Fin 7, b ∉ forbidden := by
    by_contra! hall
    have h := Finset.card_le_card (show (Finset.univ : Finset (Fin 7)) ⊆ forbidden from fun x _ => hall x)
    simp at h
    omega
  have bEdge (k) : b ≠ edge k := by
    intro h
    exact hb (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, h.symm⟩))
  have bAvoid (i) : b ≠ avoid i := by
    intro h
    exact hb (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩))
  have ba : b ≠ a := by simpa [avoid, a, ← conflict] using bAvoid j
  refine ⟨Equiv.swap a b, fun k => Equiv.swap_apply_of_ne_of_ne (fresh k).symm (bEdge k).symm, ?_, ?_⟩
  · simpa [← conflict, ← show left j = a from rfl] using ba.symm
  · intro i hi
    by_cases hr : right i = a
    · have hl : left i ≠ a := hr ▸ hi
      have h : left i ≠ b := by simpa [avoid, hl] using (bAvoid i).symm
      simpa [hr] using h
    · by_cases hs : right i = b
      · have hl : left i ≠ a := by
          intro h
          have := bAvoid i
          simp [avoid, h, hs] at this
        simpa [hs] using hl
      · simpa [Equiv.swap_apply_of_ne_of_ne hr hs] using hi

/-- The color permutation in Lemma 7. Repeated endpoints and repeated cut-edge
colors are permitted. -/
theorem cutPalettePermutation (left right edge : Fin 3 → Fin 7)
    (fresh : ∀ i, left i = right i → ∀ k, left i ≠ edge k) :
    ∃ p : Equiv.Perm (Fin 7), (∀ k, p (edge k) = edge k) ∧ ∀ i, left i ≠ p (right i) := by
  classical
  suffices H : ∀ s : Finset (Fin 3), ∃ p : Equiv.Perm (Fin 7),
      (∀ k, p (edge k) = edge k) ∧ (∀ i ∈ s, left i ≠ p (right i)) ∧
      ∀ i, left i ≠ right i → left i ≠ p (right i) by
    obtain ⟨p, hp, hs, _⟩ := H Finset.univ
    exact ⟨p, hp, fun i => hs i (Finset.mem_univ _)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨Equiv.refl _, fun _ => rfl, by simp, fun _ h => h⟩
  | insert j s hj ih =>
    obtain ⟨p, hp, hs, hi⟩ := ih
    by_cases h : left j = p (right j)
    · have h' : left j = right j := by by_contra hn; exact hi j hn h
      obtain ⟨q, hq, fixj, keep⟩ := repairCutPair left (fun i => p (right i)) edge j h (fresh j h')
      refine ⟨p.trans q, fun k => by simp [hp, hq], ?_, fun i h0 => keep i (hi i h0)⟩
      intro i him
      rcases Finset.mem_insert.mp him with rfl | hmem
      · exact fixj
      · exact keep i (hs i hmem)
    · refine ⟨p, hp, ?_, hi⟩
      intro i him
      rcases Finset.mem_insert.mp him with rfl | hmem
      · exact h
      · exact hs i hmem

/-- Kostochka's Lemma 7 for a cut of a simple graph. The initial coloring
already separates incident vertex–edge pairs and adjacent edges. Every
monochromatic adjacent pair crosses the cut and its common color is absent
from all cut edges. -/
theorem glueThreeEdgeCut {V : Type*} (G : SimpleGraph V) (side : Set V)
    (left right : Fin 3 → V) (boundary : Fin 3 → G.edgeSet)
    (vertex : V → Fin 7) (edge : G.edgeSet → Fin 7)
    (cover : ∀ (e : G.edgeSet) (u v : V), u ∈ (e : Sym2 V) → v ∈ (e : Sym2 V) →
      u ∉ side → v ∈ side → ∃ i, left i = u ∧ right i = v ∧ boundary i = e)
    (vertices : ∀ u v, G.Adj u v → (u ∈ side ↔ v ∈ side) → vertex u ≠ vertex v)
    (edges : ∀ e f : G.edgeSet, e ≠ f →
      (∃ v : V, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)) → edge e ≠ edge f)
    (incidence : ∀ v (e : G.edgeSet), v ∈ (e : Sym2 V) → vertex v ≠ edge e)
    (fresh : ∀ i, vertex (left i) = vertex (right i) → ∀ k, vertex (left i) ≠ edge (boundary k)) :
    G.TotalColorable 7 := by
  classical
  obtain ⟨p, hp, sep⟩ := cutPalettePermutation (vertex ∘ left) (vertex ∘ right) (edge ∘ boundary) fresh
  let vc (v : V) := if v ∈ side then p (vertex v) else vertex v
  let ec (e : G.edgeSet) := if ∀ w ∈ (e : Sym2 V), w ∈ side then p (edge e) else edge e
  have atVertex (e : G.edgeSet) (v : V) (hv : v ∈ (e : Sym2 V)) :
      ec e = if v ∈ side then p (edge e) else edge e := by
    by_cases hi : ∀ w ∈ (e : Sym2 V), w ∈ side
    · unfold ec
      rw [if_pos hi, if_pos (hi v hv)]
    · simp only [ec, if_neg hi]
      by_cases hs : v ∈ side
      · rw [if_pos hs]
        push Not at hi
        obtain ⟨u, hu, hout⟩ := hi
        obtain ⟨i, _, _, he⟩ := cover e u v hu hv hout hs
        exact he ▸ (hp i).symm
      · rw [if_neg hs]
  have cross (u v : V) (h : G.Adj u v) (hu : u ∉ side) (hv : v ∈ side) : vc u ≠ vc v := by
    let e : G.edgeSet := ⟨s(u, v), h⟩
    obtain ⟨i, h₁, h₂, _⟩ := cover e u v (Sym2.mem_mk_left _ _) (Sym2.mem_mk_right _ _) hu hv
    simpa [vc, hu, hv, Function.comp_def, h₁, h₂] using sep i
  refine ⟨Sum.elim vc ec, ?_, ?_, ?_⟩
  · intro u v huv
    change vc u ≠ vc v
    by_cases hu : u ∈ side <;> by_cases hv : v ∈ side
    · simpa [vc, hu, hv] using vertices u v huv (by simp [hu, hv])
    · exact (cross v u huv.symm hv hu).symm
    · exact cross u v huv hu hv
    · simpa [vc, hu, hv] using vertices u v huv (by simp [hu, hv])
  · intro e f nef hw
    obtain ⟨v, he, hf⟩ := hw
    change ec e ≠ ec f
    rw [atVertex e v he, atVertex f v hf]
    by_cases hv : v ∈ side <;> simpa [hv] using edges e f nef ⟨v, he, hf⟩
  · intro v e he
    change vc v ≠ ec e
    rw [atVertex e v he]
    by_cases hv : v ∈ side <;> simpa [vc, hv] using incidence v e he

end TotalColorFive

end


section -- CutGluePalette

/-
The finite palette problem at the two ends of a three-edge cut, from Lemma 8
of A. V. Kostochka, Discrete Mathematics 162 (1996). Index zero denotes the
first crossing edge. Indices one and two have distinct endpoints on each side.
-/

namespace TotalColorFive

/-- Information supplied by a total coloring of one auxiliary side. `repeated`
says that endpoint zero coincides with endpoint one or two. Its available list
then has at least three colors, since it has at least two missing incident edges. -/
structure CutSide where
  vertex : Fin 3 → Fin 7
  avail : Fin 3 → Finset (Fin 7)
  shared : Fin 7
  repeated : Prop
  one_ne_two : vertex 1 ≠ vertex 2
  shared_one : shared ∈ avail 1
  shared_two : shared ∈ avail 2
  vertex_blocked : ∀ i, vertex i ∉ avail i
  room : ∀ i, 2 ≤ (avail i).card
  repeat_room : repeated → 3 ≤ (avail 0).card
  repeat_color : repeated → vertex 0 = vertex 1 ∨ vertex 0 = vertex 2

/-- A local choice of colors for the three cut edges. We ask for the color of
edge zero to differ from both other colors whenever endpoint zero repeats. -/
def CutSide.Allows (s : CutSide) (e : Fin 3 → Fin 7) : Prop :=
  (∀ i, e i ∈ s.avail i) ∧ (s.repeated → e 0 ≠ e 1 ∧ e 0 ≠ e 2)

/-- Matching equality patterns allow the right-hand edge colors to be renamed
to the left-hand ones. The last condition removes unavoidable collisions on
edge colors. Lemma 7 will remove all remaining vertex conflicts. -/
structure CutPlan (s t : CutSide) (l r : Fin 3 → Fin 7) : Prop where
  left_ok : s.Allows l
  right_ok : t.Allows r
  pattern : ∀ i j, l i = l j ↔ r i = r j
  blocked : ∀ i j, s.vertex i ≠ l j ∨ t.vertex i ≠ r j

private theorem alignPalette (l r : Fin 3 → Fin 7) (pat : ∀ i j, l i = l j ↔ r i = r j) :
    ∃ p : Equiv.Perm (Fin 7), ∀ i, p (r i) = l i := by
  classical
  suffices h : ∀ a : Finset (Fin 3), ∃ p : Equiv.Perm (Fin 7), ∀ i ∈ a, p (r i) = l i by
    obtain ⟨p, hp⟩ := h Finset.univ
    exact ⟨p, fun i => hp i (Finset.mem_univ _)⟩
  intro a
  induction a using Finset.induction_on with
  | empty => exact ⟨Equiv.refl _, by simp⟩
  | insert j a _ ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.trans (Equiv.swap (p (r j)) (l j)), ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | h
    · exact Equiv.swap_apply_left _ _
    · by_cases he : r i = r j
      · rw [he, (pat i j).mpr he]
        exact Equiv.swap_apply_left _ _
      · have hr := p.injective.ne he
        have hl : p (r i) ≠ l j := by rw [hp i h]; exact fun eq => he ((pat i j).mp eq)
        exact (Equiv.swap_apply_of_ne_of_ne hr hl).trans (hp i h)

/-- Once a boundary plan is available, a single renumbering simultaneously
matches all three edge colors and separates each pair of opposite vertices. -/
theorem CutPlan.renumber {s t : CutSide} {l r : Fin 3 → Fin 7} (h : CutPlan s t l r) :
    ∃ p : Equiv.Perm (Fin 7), (∀ i, p (r i) = l i) ∧ ∀ i, s.vertex i ≠ p (t.vertex i) := by
  obtain ⟨p, hp⟩ := alignPalette l r h.pattern
  have safe (i) (hit : s.vertex i = p (t.vertex i)) (k) : s.vertex i ≠ l k := by
    intro eq
    rcases h.blocked i k with hl | hr
    · exact hl eq
    · exact hr (p.injective (hit.symm.trans (eq.trans (hp k).symm)))
  obtain ⟨q, hq, hs⟩ := cutPalettePermutation s.vertex (p ∘ t.vertex) l safe
  exact ⟨p.trans q, fun i => by simp [hp, hq], hs⟩

private abbrev Plans (s t : CutSide) := ∃ l r, CutPlan s t l r

private theorem plans_symm {s t : CutSide} (h : Plans s t) : Plans t s := by
  obtain ⟨l,r,h⟩ := h
  exact ⟨r,l,h.right_ok,h.left_ok,fun i j => (h.pattern i j).symm,fun i j => (h.blocked i j).symm⟩

private def Compatible (s t : CutSide) (a b : Fin 7) : Prop :=
  (s.vertex 1 ≠ a ∨ t.vertex 1 ≠ b) ∧ (s.vertex 2 ≠ a ∨ t.vertex 2 ≠ b)

private def Picks (s t : CutSide) (a b : Fin 7) : Prop :=
  ∃ x ∈ s.avail 0, x ≠ a ∧ ∃ y ∈ t.avail 0, y ≠ b ∧ Compatible s t x y

private theorem picks_flip {s t : CutSide} {a b : Fin 7} (h : Picks s t a b) : Picks t s b a := by
  obtain ⟨x,hx,hxa,y,hy,hyb,h₁,h₂⟩ := h
  exact ⟨y,hy,hyb,x,hx,hxa,h₁.symm,h₂.symm⟩

private theorem CutSide.other (s : CutSide) (i : Fin 3) (a : Fin 7) : ∃ x ∈ s.avail i, x ≠ a := by
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (s.room i)
  by_cases h : x = a
  · exact ⟨y,hy,h ▸ hxy.symm⟩
  · exact ⟨x,hx,h⟩

/-- Failure to choose compatible colors after excluding one color on either
side forces exactly two choices on the first side, including the excluded one.
Fix a choice on the second side. It can equal at most one of its two distinct
vertex colors, so every choice left on the first side is forced to one color. -/
private theorem forcedList {s t : CutSide} {a b : Fin 7} (h : ¬ Picks s t a b) :
    a ∈ s.avail 0 ∧ (s.avail 0).card ≤ 2 := by
  classical
  obtain ⟨y,hy,hyb⟩ := t.other 0 b
  obtain ⟨x,hx,hxa⟩ := s.other 0 a
  have forced (z) (hz : z ∈ s.avail 0) (hza : z ≠ a) :
      (s.vertex 1 = z ∧ t.vertex 1 = y) ∨ (s.vertex 2 = z ∧ t.vertex 2 = y) := by
    by_contra hn
    apply h
    refine ⟨z,hz,hza,y,hy,hyb,?_⟩
    unfold Compatible
    grind
  have same (z) (hz : z ∈ s.avail 0) (hza : z ≠ a) : z = x := by
    have := forced z hz hza
    have := forced x hx hxa
    have := t.one_ne_two
    grind
  have subset : s.avail 0 ⊆ {a,x} := by
    intro z hz
    by_cases hza : z = a
    · simp [hza]
    · simp [same z hz hza]
  refine ⟨?_, (Finset.card_le_card subset).trans (Finset.card_le_two)⟩
  by_contra ha
  have sub : s.avail 0 ⊆ {x} := fun z hz => Finset.mem_singleton.mpr (same z hz (by rintro rfl; exact ha hz))
  have hle := Finset.card_le_card sub
  have hge := s.room 0
  simp only [Finset.card_singleton] at hle
  omega

private theorem CutSide.block {s : CutSide} {i : Fin 3} {a : Fin 7} (ha : a ∈ s.avail i) : s.vertex i ≠ a :=
  fun h => s.vertex_blocked i (h ▸ ha)

private theorem doubleAllowed (s : CutSide) {a : Fin 7} (ha : a ∈ s.avail 0) (hd : a ≠ s.shared) :
    s.Allows ![a,s.shared,s.shared] := by
  constructor
  · intro i
    fin_cases i
    · exact ha
    · exact s.shared_one
    · exact s.shared_two
  · exact fun _ => ⟨hd,hd⟩

private theorem planTwo {s t : CutSide} (start : s.vertex 0 ≠ s.shared ∨ t.vertex 0 ≠ t.shared)
    (h : Picks s t s.shared t.shared) : Plans s t := by
  obtain ⟨a,ha,hsa,b,hb,htb,h₁,h₂⟩ := h
  refine ⟨![a,s.shared,s.shared],![b,t.shared,t.shared],doubleAllowed s ha hsa,doubleAllowed t hb htb,?_,?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [hsa,htb,hsa.symm,htb.symm]
  · intro i j
    have a₀ := CutSide.block ha
    have a₁ := CutSide.block s.shared_one
    have a₂ := CutSide.block s.shared_two
    fin_cases i <;> fin_cases j <;> first | exact Or.inl a₀ | exact Or.inl a₁ | exact Or.inl a₂ | exact start | exact h₁ | exact h₂

private theorem planOne {s t : CutSide} (h : ¬ Picks s t s.shared t.shared) : Plans s t := by
  have ⟨ha,sa⟩ := forcedList h
  have ⟨hb,sb⟩ := forcedList (fun p => h (picks_flip p))
  have ok (u : CutSide) (h0 : u.shared ∈ u.avail 0) (sz : (u.avail 0).card ≤ 2) :
      u.Allows (fun _ => u.shared) := by
    constructor
    · intro i
      fin_cases i
      · exact h0
      · exact u.shared_one
      · exact u.shared_two
    · intro repeated
      have := u.repeat_room repeated
      omega
  refine ⟨_,_,ok s ha sa,ok t hb sb,fun _ _ => iff_of_true rfl rfl,?_⟩
  intro i j
  exact Or.inl (CutSide.block ((ok s ha sa).1 i))

private theorem plansOfFirst {s t : CutSide} (start : s.vertex 0 ≠ s.shared ∨ t.vertex 0 ≠ t.shared) : Plans s t := by
  by_cases h : Picks s t s.shared t.shared
  · exact planTwo start h
  · exact planOne h

private theorem notRepeated {s : CutSide} (h : s.vertex 0 = s.shared) : ¬ s.repeated := by
  intro hr
  rcases s.repeat_color hr with h₁ | h₂
  · exact CutSide.block s.shared_one (h₁.symm.trans h)
  · exact CutSide.block s.shared_two (h₂.symm.trans h)

/-- The two sides use three distinct colors each. The shared spare is used
on edge two on the left and edge one on the right, so the first vertices have
different colors after alignment. -/
private theorem planThree {s t : CutSide} (h₀ : s.vertex 0 = s.shared) (h₀' : t.vertex 0 = t.shared)
    {d e : Fin 7} (hd : d ∈ s.avail 1) (hds : d ≠ s.shared)
    (he : e ∈ t.avail 2) (het : e ≠ t.shared) (h : Picks s t d e) : Plans s t := by
  obtain ⟨a,ha,had,b,hb,hbe,h₁,h₂⟩ := h
  have has : a ≠ s.shared := h₀ ▸ (CutSide.block ha).symm
  have hbt : b ≠ t.shared := h₀' ▸ (CutSide.block hb).symm
  let l := ![a,d,s.shared]
  let r := ![b,t.shared,e]
  have hl : s.Allows l := by
    refine ⟨?_,fun hr => (notRepeated h₀ hr).elim⟩
    intro i
    fin_cases i
    · exact ha
    · exact hd
    · exact s.shared_two
  have hr : t.Allows r := by
    refine ⟨?_,fun hr => (notRepeated h₀' hr).elim⟩
    intro i
    fin_cases i
    · exact hb
    · exact t.shared_one
    · exact he
  refine ⟨l,r,hl,hr,?_,?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [l,r,had,hbe,has,hbt,hds,het,had.symm,hbe.symm,has.symm,hbt.symm,hds.symm,het.symm]
  · intro i j
    have h0a := CutSide.block ha
    have h0d : s.vertex 0 ≠ d := h₀.trans_ne hds.symm
    have h0e : t.vertex 0 ≠ e := h₀'.trans_ne het.symm
    have h1d := CutSide.block hd
    have h1s := CutSide.block s.shared_one
    have h2t := CutSide.block t.shared_two
    have h2e := CutSide.block he
    fin_cases i <;> fin_cases j <;> first | exact Or.inl h0a | exact Or.inl h0d | exact Or.inr h0e | exact Or.inl h1d | exact Or.inl h1s | exact Or.inr h2t | exact Or.inr h2e | exact h₁ | exact h₂

/-- The boundary-palette conclusion of Kostochka, Lemma 8. -/
theorem boundaryPalette (s t : CutSide) :
    ∃ (l r : Fin 3 → Fin 7) (p : Equiv.Perm (Fin 7)),
      s.Allows l ∧ t.Allows r ∧ (∀ i, p (r i) = l i) ∧ ∀ i, s.vertex i ≠ p (t.vertex i) := by
  classical
  suffices existsPlan : Plans s t by
    obtain ⟨l,r,h⟩ := existsPlan
    obtain ⟨p,align,vertices⟩ := h.renumber
    exact ⟨l,r,p,h.left_ok,h.right_ok,align,vertices⟩
  by_cases hs : s.vertex 0 = s.shared
  · by_cases ht : t.vertex 0 = t.shared
    · obtain ⟨d,hd,hds⟩ := s.other 1 s.shared
      obtain ⟨e,he,hes⟩ := s.other 2 s.shared
      obtain ⟨f,hf,hft⟩ := t.other 1 t.shared
      obtain ⟨g,hg,hgt⟩ := t.other 2 t.shared
      by_cases hde : d = e
      · let s' : CutSide := {s with shared := d, shared_one := hd, shared_two := hde ▸ he}
        obtain ⟨l,r,h⟩ := plansOfFirst (s := s') (t := t) (Or.inl (hs.trans_ne hds.symm))
        exact ⟨l,r,h.left_ok,h.right_ok,h.pattern,h.blocked⟩
      by_cases hfg : f = g
      · let t' : CutSide := {t with shared := f, shared_one := hf, shared_two := hfg ▸ hg}
        obtain ⟨l,r,h⟩ := plansOfFirst (s := s) (t := t') (Or.inr (ht.trans_ne hft.symm))
        exact ⟨l,r,h.left_ok,h.right_ok,h.pattern,h.blocked⟩
      by_cases pick : Picks s t d g
      · exact planThree hs ht hd hds hg hgt pick
      by_cases reverse : Picks t s f e
      · exact plans_symm (planThree ht hs hf hft he hes reverse)
      have hsa := (forcedList (fun p => reverse (picks_flip p))).1
      have hta := (forcedList reverse).1
      exact planThree hs ht hd hds hg hgt
        ⟨e,hsa,Ne.symm hde,f,hta,hfg,Or.inr (CutSide.block hf),Or.inl (CutSide.block he)⟩
    · exact plansOfFirst (Or.inr ht)
  · exact plansOfFirst (Or.inl hs)

end TotalColorFive

end


section -- MultiCutGlue

/- The three-edge-cut reduction for loopless multigraphs in Kostochka's
Lemma 8. Bundles of parallel edges are represented by finite color sets. -/
namespace MultFive.Multi

open Finset TotalColorFive

variable {V : Type*} [DecidableEq V] {m : Multi V}

private def atPair (a b x y : V) : Prop := (x = a ∧ y = b) ∨ (x = b ∧ y = a)
private instance (a b x y : V) : Decidable (atPair a b x y) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

/-- Remove one copy of an auxiliary edge. Its color becomes free at both ends,
including when other copies of that edge were already present. -/
private theorem removeExtra (a b : V) (ab : a ≠ b) (given : (m.addEdge a b ab).Colorable) :
    ∃ vc ec, ∃ c : Fin 7, m.Valid vc ec ∧ vc a ≠ vc b ∧
      vc a ≠ c ∧ vc b ≠ c ∧ (∀ x, c ∉ ec a x) ∧ (∀ x, c ∉ ec b x) := by
  classical
  obtain ⟨vc,old,h⟩ := given
  have countAB : (old a b).card = m.count a b + 1 := by simpa [addEdge] using h.size a b
  obtain ⟨c,hc⟩ := card_pos.mp (show 0 < (old a b).card by omega)
  have hc' : c ∈ old b a := by rwa [h.symmetric b a]
  let ec x y := if atPair a b x y then (old x y).erase c else old x y
  have small (x y : V) : ec x y ⊆ old x y := by dsimp [ec]; split; exact erase_subset _ _; exact Subset.rfl
  have picked {x y} (hab : atPair a b x y) : c ∈ old x y := by
    rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
  have valid : m.Valid vc ec := {
    symmetric := by
      intro x y
      have eq : atPair a b x y ↔ atPair a b y x := by unfold atPair; grind
      simp [ec,eq,h.symmetric x y]
    size := by
      intro x y
      have sz := h.size x y
      change (old x y).card = m.count x y + if atPair a b x y then 1 else 0 at sz
      by_cases hp : atPair a b x y
      · simp only [ec,if_pos hp,card_erase_of_mem (picked hp)]
        simp only [if_pos hp] at sz
        omega
      · simpa [ec,hp] using sz
    vertices := by
      intro x y pos
      apply h.vertices
      change 0 < m.count x y + _
      omega
    avoids := fun x y hit => h.avoids x y (small x y hit)
    disjoint := fun x y z ne => (h.disjoint x y z ne).mono (small x y) (small x z) }
  refine ⟨vc,ec,c,valid,h.vertices a b (by simp [addEdge]),fun eq => h.avoids a b (eq ▸ hc),
    fun eq => h.avoids b a (eq ▸ hc'),?_,?_⟩
  · intro x hx; by_cases eq : x = b
    · subst x; simp [ec,atPair] at hx
    · exact Finset.disjoint_left.mp (h.disjoint a b x (Ne.symm eq)) hc (small a x hx)
  · intro x hx; by_cases eq : x = a
    · subst x; simp [ec,atPair] at hx
    · exact Finset.disjoint_left.mp (h.disjoint b a x (Ne.symm eq)) hc' (small b x hx)

variable [Fintype V]

private def free (vc : V → Fin 7) (ec : V → V → Finset (Fin 7)) (x : V) : Finset (Fin 7) :=
  (insert (vc x) (univ.biUnion (ec x)))ᶜ

omit [DecidableEq V] in
private theorem roomAt {vc ec} (h : m.Valid vc ec) (v : V) :
    6 ≤ (free vc ec v).card + m.degree v := by
  have hi := card_insert_le (vc v) (univ.biUnion (ec v))
  have hj := card_biUnion_le (s := (univ : Finset V)) (t := ec v)
  simp only [h.size] at hj
  simp only [free,card_compl,Fintype.card_fin]
  unfold degree
  omega

/-- A properly colored wing, with the boundary palette read off after removing
the auxiliary edge between terminals 1 and 2. -/
private structure Prepared (m : Multi V) (ep : Fin 3 → V) where
  vc : V → Fin 7
  ec : V → V → Finset (Fin 7)
  valid : m.Valid vc ec
  side : CutSide
  vertex : ∀ i, side.vertex i = vc (ep i)
  avail : ∀ i, side.avail i = free vc ec (ep i)
  repeated : side.repeated ↔ ep 0 = ep 1 ∨ ep 0 = ep 2

private theorem prepare (ep : Fin 3 → V) (ne : ep 1 ≠ ep 2)
    (deg : ∀ i, m.degree (ep i) ≤ 4)
    (repeatDegree : ep 0 = ep 1 ∨ ep 0 = ep 2 → m.degree (ep 0) ≤ 3)
    (color : (m.addEdge (ep 1) (ep 2) ne).Colorable) : Nonempty (Prepared m ep) := by
  classical
  obtain ⟨vc,ec,c,h,vne,v1,v2,f1,f2⟩ := removeExtra _ _ ne color
  refine ⟨⟨vc,ec,h, {
    vertex := vc ∘ ep
    avail := fun i => free vc ec (ep i)
    shared := c
    repeated := ep 0 = ep 1 ∨ ep 0 = ep 2
    one_ne_two := vne
    shared_one := by simp [free,Ne.symm v1,f1]
    shared_two := by simp [free,Ne.symm v2,f2]
    vertex_blocked := by simp [free]
    room := fun i => by have := roomAt h (ep i); have := deg i; omega
    repeat_room := fun rep => by have := roomAt h (ep 0); have := repeatDegree rep; omega
    repeat_color := fun rep => rep.imp (congrArg vc) (congrArg vc)
    },fun _ => rfl, fun _ => rfl, Iff.rfl⟩⟩


private theorem rename {W : Type*} {g : Multi W} {vc ec} (h : g.Valid vc ec) (p : Equiv.Perm (Fin 7)) :
    g.Valid (p ∘ vc) (fun x y => (ec x y).map p.toEmbedding) where
  symmetric x y := congrArg _ (h.symmetric x y)
  size x y := by simp [h.size]
  vertices x y pos := p.injective.ne (h.vertices _ _ pos)
  avoids x y := by simpa using h.avoids x y
  disjoint x y z ne := by simpa using h.disjoint x y z ne

private theorem separateColors {W : Type*} (ep : Fin 3 → W) (distinct : ep 1 ≠ ep 2)
    {s : CutSide} (rep : s.repeated ↔ ep 0 = ep 1 ∨ ep 0 = ep 2)
    {c : Fin 3 → Fin 7} (ok : s.Allows c) (i j : Fin 3) (ne : i ≠ j) (hit : ep i = ep j) :
    c i ≠ c j := by
  have c01 (h : ep 0 = ep 1) := (ok.2 (rep.mpr (Or.inl h))).1
  have c02 (h : ep 0 = ep 2) := (ok.2 (rep.mpr (Or.inr h))).2
  fin_cases i <;> fin_cases j <;> grind

private theorem free_ne {W : Type*} [Fintype W] {vc : W → Fin 7} {ec} {v} {k}
    (hk : k ∈ free vc ec v) : vc v ≠ k ∧ ∀ w, k ∉ ec v w := by
  simpa [free,ne_comm] using hk

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def cutIndices (left : Fin 3 → L) (right : Fin 3 → R) (x : L) (y : R) : Finset (Fin 3) :=
  univ.filter (fun i => left i = x ∧ right i = y)

/-- Rename the two interior colorings and fill the bundles of cut edges. -/
private theorem assemble (m : Multi (L ⊕ R)) {ml : Multi L} {mr : Multi R}
    (left : Fin 3 → L) (right : Fin 3 → R) (nl : left 1 ≠ left 2) (nr : right 1 ≠ right 2)
    (pl : Prepared ml left) (pr : Prepared mr right)
    (insideL : ∀ x y, m.count (.inl x) (.inl y) = ml.count x y)
    (insideR : ∀ x y, m.count (.inr x) (.inr y) = mr.count x y)
    (crossCount : ∀ x y, m.count (.inl x) (.inr y) = (cutIndices left right x y).card) :
    m.Colorable := by
  classical
  obtain ⟨l,r,p,hl,hr,align,sep⟩ := boundaryPalette pl.side pr.side
  have rightColor := rename pr.valid p
  let cross x y := (cutIndices left right x y).image l
  have mem (x y k) : k ∈ cross x y ↔ ∃ i, left i = x ∧ right i = y ∧ l i = k := by
    simp [cross,cutIndices,and_assoc]
  have freeL i := free_ne ((pl.avail i) ▸ hl.1 i)
  have freeR i := free_ne ((pr.avail i) ▸ hr.1 i)
  have matchL {i j} (ne : i ≠ j) (hit : left i = left j) : l i ≠ l j :=
    separateColors _ nl pl.repeated hl _ _ ne hit
  have matchR {i j} (ne : i ≠ j) (hit : right i = right j) : l i ≠ l j := by
    rw [← align,← align]
    exact p.injective.ne (separateColors _ nr pr.repeated hr _ _ ne hit)
  have crossSize (x y) : (cross x y).card = m.count (.inl x) (.inr y) := by
    rw [crossCount]
    apply card_image_of_injOn
    intro i hi j hj eq
    by_contra ne
    have hi' := (mem_filter.mp hi).2.1
    have hj' := (mem_filter.mp hj).2.1
    exact matchL ne (hi'.trans hj'.symm) eq
  have vertices (x y) (pos : 0 < m.count (.inl x) (.inr y)) : pl.vc x ≠ p (pr.vc y) := by
    rw [crossCount] at pos
    obtain ⟨i,hi⟩ := card_pos.mp pos
    obtain ⟨rfl,rfl⟩ := (mem_filter.mp hi).2
    simpa [pl.vertex,pr.vertex] using sep i
  have avoidL x y : pl.vc x ∉ cross x y := by
    intro h; obtain ⟨i,rfl,rfl,eq⟩ := (mem _ _ _).mp h
    exact (freeL i).1 eq.symm
  have avoidR x y : p (pr.vc y) ∉ cross x y := by
    intro h; obtain ⟨i,rfl,rfl,eq⟩ := (mem _ _ _).mp h
    exact (freeR i).1 (p.injective (eq.symm.trans (align i).symm))
  have mixedL (x z : L) (y : R) : Disjoint (pl.ec x z) (cross x y) := by
    apply disjoint_left.mpr
    intro k hk hit
    obtain ⟨i,rfl,rfl,rfl⟩ := (mem _ _ _).mp hit
    exact (freeL i).2 _ hk
  have mixedR (y z : R) (x : L) : Disjoint ((pr.ec y z).map p.toEmbedding) (cross x y) := by
    apply disjoint_left.mpr
    intro k hk hit
    obtain ⟨i,rfl,rfl,rfl⟩ := (mem _ _ _).mp hit
    rw [←align] at hk
    exact (freeR i).2 _ (by simpa using hk)
  have crossL (x : L) (y z : R) (ne : y ≠ z) : Disjoint (cross x y) (cross x z) := by
    apply disjoint_left.mpr
    intro k hk hit
    obtain ⟨i,hi,hiy,rfl⟩ := (mem _ _ _).mp hk
    obtain ⟨j,hj,hjz,eq⟩ := (mem _ _ _).mp hit
    exact matchL (i := i) (j := j) (fun ij => ne (hiy.symm.trans ((congrArg right ij).trans hjz))) (hi.trans hj.symm) eq.symm
  have crossR (y : R) (x z : L) (ne : x ≠ z) : Disjoint (cross x y) (cross z y) := by
    apply disjoint_left.mpr
    intro k hk hit
    obtain ⟨i,hix,hi,rfl⟩ := (mem _ _ _).mp hk
    obtain ⟨j,hjz,hj,eq⟩ := (mem _ _ _).mp hit
    exact matchR (i := i) (j := j) (fun ij => ne (hix.symm.trans ((congrArg left ij).trans hjz))) (hi.trans hj.symm) eq.symm
  let vc := Sum.elim pl.vc (p ∘ pr.vc)
  let ec : L ⊕ R → L ⊕ R → Finset (Fin 7)
    | .inl x, .inl y => pl.ec x y
    | .inr x, .inr y => (pr.ec x y).map p.toEmbedding
    | .inl x, .inr y | .inr y, .inl x => cross x y
  refine ⟨vc,ec,?_⟩
  constructor
  · rintro (x | x) (y | y)
    · exact pl.valid.symmetric _ _
    · rfl
    · rfl
    · exact rightColor.symmetric _ _
  · rintro (x | x) (y | y)
    · exact (pl.valid.size _ _).trans (insideL _ _).symm
    · exact crossSize _ _
    · exact (crossSize _ _).trans (m.symm _ _)
    · exact (rightColor.size _ _).trans (insideR _ _).symm
  · rintro (x | x) (y | y) pos
    · exact pl.valid.vertices _ _ (insideL _ _ ▸ pos)
    · exact vertices x y pos
    · exact (vertices y x (m.symm _ _ ▸ pos)).symm
    · exact rightColor.vertices _ _ (insideR _ _ ▸ pos)
  · rintro (x | x) (y | y)
    · exact pl.valid.avoids _ _
    · exact avoidL x y
    · exact avoidR y x
    · exact rightColor.avoids _ _
  · rintro (x | x) (y | y) (z | z) ne
    · exact pl.valid.disjoint _ _ _ (fun eq => ne (congrArg Sum.inl eq))
    · exact mixedL _ _ _
    · exact (mixedL _ _ _).symm
    · exact crossL _ _ _ (fun eq => ne (congrArg Sum.inr eq))
    · exact crossR _ _ _ (fun eq => ne (congrArg Sum.inl eq))
    · exact (mixedR _ _ _).symm
    · exact mixedR _ _ _
    · exact rightColor.disjoint _ _ _ (fun eq => ne (congrArg Sum.inr eq))


omit [Fintype L] in
private theorem sumIndices (left : Fin 3 → L) (right : Fin 3 → R) (x : L) :
    ∑ y, (cutIndices left right x y).card = (univ.filter (fun i => left i = x)).card := by
  classical
  calc
    _ = ∑ y : R, ∑ i : Fin 3, if left i = x ∧ right i = y then (1 : ℕ) else 0 := by simp [cutIndices]
    _ = ∑ i : Fin 3, ∑ y : R, if left i = x ∧ right i = y then (1 : ℕ) else 0 := sum_comm
    _ = ∑ i : Fin 3, if left i = x then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro i _
      by_cases h : left i = x <;> simp [h]
    _ = _ := by simp

omit [Fintype R] in
private theorem sumIndices' (left : Fin 3 → L) (right : Fin 3 → R) (y : R) :
    ∑ x, (cutIndices left right x y).card = (univ.filter (fun i => right i = y)).card := by
  have swap (x : L) : cutIndices left right x y = cutIndices right left y x := by simp [cutIndices,and_comm]
  simp only [swap,sumIndices]

private theorem prepareOfBound {W : Type*} [Fintype W] [DecidableEq W]
    (g : Multi W) (ep : Fin 3 → W) (ne : ep 1 ≠ ep 2)
    (bound : ∀ v, g.degree v + (univ.filter (fun i => ep i = v)).card ≤ 5)
    (color : (g.addEdge (ep 1) (ep 2) ne).Colorable) : Nonempty (Prepared g ep) := by
  classical
  apply prepare ep ne _ _ color
  · intro i
    have hp : 0 < (univ.filter (fun j => ep j = ep i)).card := card_pos.mpr ⟨i,by simp⟩
    have := bound (ep i)
    omega
  · intro rep
    have hp : 1 < (univ.filter (fun j => ep j = ep 0)).card := by
      rcases rep with h | h
      · exact one_lt_card.mpr ⟨0,by simp,1,by simp [h],by decide⟩
      · exact one_lt_card.mpr ⟨0,by simp,2,by simp [h],by decide⟩
    have := bound (ep 0)
    omega

private def parts (part : V → Bool) :
    {v // part v = false} ⊕ {v // part v = true} ≃ V where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun v := if hv : part v = false then .inl ⟨v,hv⟩ else .inr ⟨v,by simpa using hv⟩
  left_inv := by rintro (⟨v,hv⟩ | ⟨v,hv⟩) <;> simp [hv]
  right_inv := by intro v; by_cases h : part v = false <;> simp [h]

private def along {A B : Type*} (m : Multi A) (f : B ≃ A) : Multi B where
  count x y := m.count (f x) (f y)
  symm x y := m.symm (f x) (f y)
  loopless x := m.loopless (f x)

private theorem pushColor {A B : Type*} (m : Multi A) (f : B ≃ A) (h : (along m f).Colorable) :
    m.Colorable := by
  obtain ⟨vc,ec,valid⟩ := h
  refine ⟨vc ∘ f.symm,fun x y => ec (f.symm x) (f.symm y),?_⟩
  constructor
  · exact fun _ _ => valid.symmetric _ _
  · intro x y
    simpa [along] using valid.size (f.symm x) (f.symm y)
  · intro x y pos
    exact valid.vertices _ _ (by simpa [along] using pos)
  · exact fun _ _ => valid.avoids _ _
  · exact fun _ _ _ ne => valid.disjoint _ _ _ (f.symm.injective.ne ne)

private theorem wingBudget (m : Multi V) (part : V → Bool)
    (ep : ∀ b : Bool, Fin 3 → {v // part v = b})
    (crossCount : ∀ (x : {v // part v = false}) (y : {v // part v = true}),
        m.count x.val y.val = (cutIndices (ep false) (ep true) x y).card)
    (degreeBound : ∀ v, m.degree v ≤ 5)
    (b : Bool) (v : {v // part v = b}) :
    (m.induce {v | part v = b}).degree v +
      (univ.filter (fun i => ep b i = v)).card ≤ 5 := by
  classical
  let ml := m.induce {v | part v = false}
  let mr := m.induce {v | part v = true}
  let q := parts part
  let whole := along m q
  have split (v) : (whole.degree v) =
      ∑ x : {v // part v = false}, m.count (q v) x.val +
      ∑ y : {v // part v = true}, m.count (q v) y.val := by
    simp [whole,degree,along,Fintype.sum_sum_type,q,parts]
  have bound (v) : whole.degree v ≤ 5 := by
    have eq : whole.degree v = m.degree (q v) := q.sum_comp (fun w => m.count (q v) w)
    rw [eq]
    exact degreeBound _
  have lbound (x : {v // part v = false}) :
      ml.degree x + (univ.filter (fun i => ep false i = x)).card ≤ 5 := by
    have h := bound (.inl x)
    rw [split] at h
    change ml.degree x + ∑ y : {v // part v = true}, m.count x.val y.val ≤ 5 at h
    simpa only [crossCount,sumIndices] using h
  have rbound (y : {v // part v = true}) :
      mr.degree y + (univ.filter (fun i => ep true i = y)).card ≤ 5 := by
    have h := bound (.inr y)
    rw [split] at h
    change (∑ x : {v // part v = false}, m.count y.val x.val) + mr.degree y ≤ 5 at h
    rw [Nat.add_comm] at h
    simpa only [m.symm y.val,crossCount,sumIndices'] using h
  cases b
  · exact lbound v
  · exact rbound v

private theorem degreeExtra {W : Type*} [Fintype W] [DecidableEq W]
    (g : Multi W) (a b : W) (ne : a ≠ b) (x : W) :
    (g.addEdge a b ne).degree x = g.degree x + if x = a ∨ x = b then 1 else 0 := by
  unfold degree addEdge
  simp only [sum_add_distrib]
  congr 1
  by_cases ha : x = a
  · subst x; simp [ne]
  by_cases hb : x = b
  · subst x; simp [ne.symm]
  simp [ha,hb]

/-- The auxiliary multigraphs to which the induction hypothesis is applied
still have maximum degree at most five. -/
theorem threeCutWingDegree (m : Multi V) (part : V → Bool)
    (ep : ∀ b : Bool, Fin 3 → {v // part v = b})
    (distinct : ∀ b, ep b 1 ≠ ep b 2)
    (crossCount : ∀ (x : {v // part v = false}) (y : {v // part v = true}),
        m.count x.val y.val = (cutIndices (ep false) (ep true) x y).card)
    (degreeBound : ∀ v, m.degree v ≤ 5)
    (b : Bool) (v : {v // part v = b}) :
    ((m.induce {v | part v = b}).addEdge (ep b 1) (ep b 2) (distinct b)).degree v ≤ 5 := by
  have h := wingBudget m part ep crossCount degreeBound b v
  rw [degreeExtra]
  by_cases hit : v = ep b 1 ∨ v = ep b 2
  · have hp : 0 < (univ.filter (fun i => ep b i = v)).card :=
      card_pos.mpr (hit.elim (fun h => ⟨1,by simp [h]⟩) (fun h => ⟨2,by simp [h]⟩))
    simp only [if_pos hit]
    omega
  · simp only [if_neg hit]
    omega

/-- Kostochka's Lemma 8. Color each induced side after adding an edge between
its two distinct terminals. The resulting total coloring extends across all
three cut edges, including possible parallel edges. -/
theorem glueThreeCut (m : Multi V) (part : V → Bool)
    (ep : ∀ b : Bool, Fin 3 → {v // part v = b})
    (distinct : ∀ b, ep b 1 ≠ ep b 2)
    (crossCount : ∀ (x : {v // part v = false}) (y : {v // part v = true}),
        m.count x.val y.val = (cutIndices (ep false) (ep true) x y).card)
    (degreeBound : ∀ v, m.degree v ≤ 5)
    (wings : ∀ b, ((m.induce {v | part v = b}).addEdge (ep b 1) (ep b 2) (distinct b)).Colorable) :
    m.Colorable := by
  classical
  let ml := m.induce {v | part v = false}
  let mr := m.induce {v | part v = true}
  let q := parts part
  let whole := along m q
  have lbound := wingBudget m part ep crossCount degreeBound false
  have rbound := wingBudget m part ep crossCount degreeBound true
  obtain ⟨pl⟩ := prepareOfBound ml _ (distinct false) lbound (wings false)
  obtain ⟨pr⟩ := prepareOfBound mr _ (distinct true) rbound (wings true)
  exact pushColor m q (assemble whole _ _ (distinct false) (distinct true) pl pr
      (fun _ _ => rfl) (fun _ _ => rfl) crossCount)

end MultFive.Multi

end


section -- CutGlueAssemble

/- Assembly of the independent colorings at a three-edge cut in Lemma 8 of
A. V. Kostochka, Discrete Mathematics 162 (1996). -/

namespace TotalColorFive

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Three indexed edges of a cut. False denotes the left side, true the right
side. Endpoints 1 and 2 are distinct on each side. -/
structure ThreeEdgeCut (G : SimpleGraph V) where
  side : V → Bool
  left : Fin 3 → V
  right : Fin 3 → V
  edge : Fin 3 → G.edgeSet
  unique : Function.Injective edge
  edge_ends : ∀ i, (edge i : Sym2 V) = s(left i, right i)
  side_left : ∀ i, side (left i) = false
  side_right : ∀ i, side (right i) = true
  left_distinct : left 1 ≠ left 2
  right_distinct : right 1 ≠ right 2
  cover : ∀ (e : G.edgeSet) (u v : V), u ∈ (e : Sym2 V) → v ∈ (e : Sym2 V) →
    side u = false → side v = true → ∃ i, edge i = e

variable (C : ThreeEdgeCut G)

/-- True on every edge outside the cut. -/
def ThreeEdgeCut.Interior (C : ThreeEdgeCut G) (e : G.edgeSet) : Prop := ∀ i, C.edge i ≠ e

/-- The endpoint of an indexed edge on the specified side. -/
def ThreeEdgeCut.endpoint (C : ThreeEdgeCut G) (b : Bool) (i : Fin 3) : V :=
  if b then C.right i else C.left i

private theorem ThreeEdgeCut.identifyEndpoint (i : Fin 3) (v : V) (hv : v ∈ (C.edge i : Sym2 V)) :
    C.endpoint (C.side v) i = v := by
  rw [C.edge_ends i] at hv
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · simp [ThreeEdgeCut.endpoint,C.side_left]
  · simp [ThreeEdgeCut.endpoint,C.side_right]

private noncomputable def ThreeEdgeCut.edgeColor (C : ThreeEdgeCut G) (orig : G.edgeSet → Fin 7)
    (newColor : Fin 3 → Fin 7) (e : G.edgeSet) : Fin 7 := by
  classical
  exact if h : ∃ i, C.edge i = e then newColor h.choose else orig e

private theorem ThreeEdgeCut.colorOn (orig : G.edgeSet → Fin 7) (newColor : Fin 3 → Fin 7) (i : Fin 3) :
    C.edgeColor orig newColor (C.edge i) = newColor i := by
  classical
  let h : ∃ j, C.edge j = C.edge i := ⟨i,rfl⟩
  simp only [ThreeEdgeCut.edgeColor, dif_pos h, C.unique h.choose_spec]

private theorem ThreeEdgeCut.colorOff (orig : G.edgeSet → Fin 7) (newColor : Fin 3 → Fin 7)
    (e : G.edgeSet) (h : C.Interior e) : C.edgeColor orig newColor e = orig e := by
  classical
  exact dif_neg (not_exists.mpr h)

private theorem clashFree {s : CutSide} {col : Fin 3 → Fin 7} (hc : s.Allows col)
    (ep : Fin 3 → V) (distinct : ep 1 ≠ ep 2)
    (repeatOf : ep 0 = ep 1 ∨ ep 0 = ep 2 → s.repeated) (i j : Fin 3) (hne : i ≠ j)
    (hit : ep i = ep j) : col i ≠ col j := by
  have c01 (h : ep 0 = ep 1) : col 0 ≠ col 1 := (hc.2 (repeatOf (Or.inl h))).1
  have c02 (h : ep 0 = ep 2) : col 0 ≠ col 2 := (hc.2 (repeatOf (Or.inr h))).2
  fin_cases i <;> fin_cases j <;> grind

/-- Glue two interior colorings prepared by cutting the graph. Interior colors
on opposite sides may use independent labels. At each boundary vertex its list
of available colors omits its own color and the colors of its incident internal
edges. The availability conditions in `CutSide` suffice to color all three
missing edges and renumber the right side consistently. -/
theorem gluePreparedSides (C : ThreeEdgeCut G) (s : Bool → CutSide)
    (vc : V → Fin 7) (ec : G.edgeSet → Fin 7)
    (vEnds : ∀ b i, vc (C.endpoint b i) = (s b).vertex i)
    (repeatOf : ∀ b, C.endpoint b 0 = C.endpoint b 1 ∨ C.endpoint b 0 = C.endpoint b 2 → (s b).repeated)
    (vertices : ∀ v w, G.Adj v w → C.side v = C.side w → vc v ≠ vc w)
    (edges : ∀ (e f : G.edgeSet), C.Interior e → C.Interior f → e ≠ f →
      (∃ v : V, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)) → ec e ≠ ec f)
    (incident : ∀ v (e : G.edgeSet), C.Interior e → v ∈ (e : Sym2 V) → vc v ≠ ec e)
    (available : ∀ b i (e : G.edgeSet), C.Interior e → C.endpoint b i ∈ (e : Sym2 V) → ec e ∉ (s b).avail i) :
    G.TotalColorable 7 := by
  classical
  obtain ⟨l,r,p,hl,hr,align,separate⟩ := boundaryPalette (s false) (s true)
  let colors (b : Bool) : Fin 3 → Fin 7 := if b then r else l
  let rename (b : Bool) : Equiv.Perm (Fin 7) := if b then p else Equiv.refl _
  have ok (b : Bool) : (s b).Allows (colors b) := by cases b <;> assumption
  let atEnd (e : G.edgeSet) (b : Bool) := rename b (C.edgeColor ec (colors b) e)
  have crossSame (e : G.edgeSet) (i : Fin 3) (hi : C.edge i = e) : atEnd e false = atEnd e true := by
    subst e
    simpa [atEnd,rename,colors,C.colorOn] using (align i).symm
  have edgeConsistent (e : G.edgeSet) (v w : V) (hv : v ∈ (e : Sym2 V)) (hw : w ∈ (e : Sym2 V)) :
      atEnd e (C.side v) = atEnd e (C.side w) := by
    cases hv' : C.side v <;> cases hw' : C.side w
    · rfl
    · obtain ⟨i,hi⟩ := C.cover e v w hv hw hv' hw'; exact crossSame e i hi
    · obtain ⟨i,hi⟩ := C.cover e w v hw hv hw' hv'; exact (crossSame e i hi).symm
    · rfl
  let edgeOut (e : G.edgeSet) := atEnd e (C.side e.val.out.1)
  have actual (e : G.edgeSet) (v : V) (hv : v ∈ (e : Sym2 V)) : edgeOut e = atEnd e (C.side v) :=
    edgeConsistent e _ v (Sym2.out_fst_mem _) hv
  have vbnd (u v : V) (h : G.Adj u v) (hu : C.side u = false) (hv : C.side v = true) : vc u ≠ p (vc v) := by
    let e : G.edgeSet := ⟨s(u,v),h⟩
    have eu : u ∈ (e : Sym2 V) := Sym2.mem_mk_left _ _
    have ev : v ∈ (e : Sym2 V) := Sym2.mem_mk_right _ _
    obtain ⟨i,hi⟩ := C.cover e u v eu ev hu hv
    have hx := C.identifyEndpoint i u (hi ▸ eu)
    have hy := C.identifyEndpoint i v (hi ▸ ev)
    rw [hu] at hx; rw [hv] at hy
    rw [← hx,← hy,vEnds,vEnds]
    exact separate i
  have onEdge (e : G.edgeSet) (h : ¬ C.Interior e) : ∃ i, C.edge i = e := by
    simpa [ThreeEdgeCut.Interior] using h
  have mixed (e : G.edgeSet) (i : Fin 3) (v : V) (he : C.Interior e)
      (hv : v ∈ (e : Sym2 V)) (hi : v ∈ (C.edge i : Sym2 V)) :
      ec e ≠ colors (C.side v) i := by
    intro eq
    have endeq := C.identifyEndpoint i v hi
    have hm : C.endpoint (C.side v) i ∈ (e : Sym2 V) := by rwa [endeq]
    have hbad := available (C.side v) i e he hm
    exact hbad (eq ▸ (ok _).1 i)
  refine ⟨Sum.elim (fun v => rename (C.side v) (vc v)) edgeOut, ?_, ?_, ?_⟩
  · intro u v huv
    change rename (C.side u) (vc u) ≠ rename (C.side v) (vc v)
    by_cases h : C.side u = C.side v
    · rw [h]; exact (rename _).injective.ne (vertices _ _ huv h)
    · cases hu : C.side u <;> cases hv : C.side v
      · exact (h (hu.trans hv.symm)).elim
      · exact vbnd u v huv hu hv
      · exact (vbnd v u huv.symm hv hu).symm
      · exact (h (hu.trans hv.symm)).elim
  · intro e f nef meet
    obtain ⟨v,he,hf⟩ := meet
    change edgeOut e ≠ edgeOut f
    rw [actual e v he,actual f v hf]
    apply (rename _).injective.ne
    by_cases ei : C.Interior e <;> by_cases fi : C.Interior f
    · rw [C.colorOff _ _ e ei,C.colorOff _ _ f fi]
      exact edges e f ei fi nef ⟨v,he,hf⟩
    · obtain ⟨i,rfl⟩ := onEdge f fi
      rw [C.colorOff _ _ e ei,C.colorOn]
      exact mixed e i v ei he hf
    · obtain ⟨i,rfl⟩ := onEdge e ei
      rw [C.colorOn,C.colorOff _ _ f fi]
      exact (mixed f i v fi hf he).symm
    · obtain ⟨i,rfl⟩ := onEdge e ei
      obtain ⟨j,rfl⟩ := onEdge f fi
      rw [C.colorOn,C.colorOn]
      refine clashFree (ok _) (C.endpoint (C.side v)) ?_ (repeatOf _) i j (fun eq => nef (congrArg _ eq))
        ((C.identifyEndpoint i v he).trans (C.identifyEndpoint j v hf).symm)
      cases C.side v
      · exact C.left_distinct
      · exact C.right_distinct
  · intro v e he
    change rename (C.side v) (vc v) ≠ edgeOut e
    rw [actual e v he]
    apply (rename _).injective.ne
    by_cases hi : C.Interior e
    · rw [C.colorOff _ _ _ hi]
      exact incident v e hi he
    · obtain ⟨i,rfl⟩ := onEdge e hi
      rw [C.colorOn]
      have hh := vEnds (C.side v) i
      rw [C.identifyEndpoint i v he] at hh
      intro same
      exact (s _).vertex_blocked i (hh ▸ same ▸ (ok _).1 i)

end TotalColorFive

end


section -- CutGlueLayout

/- Orient cut edges from the chosen finite side to its complement. A cut of
size one lies at an articulation. For three edges either one vertex contains
them all, or two can be indexed with distinct endpoints on both sides, as in
A. V. Kostochka, Lemma 8. -/

namespace TotalColorFive

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- False inside the cut and true outside, matching `ThreeEdgeCut.side`. -/
def cutSide (s : Finset V) (v : V) : Bool := decide (v ∉ s)

/-- Directed crossing pairs with the inside endpoint first. -/
def cutPairs (s : Finset V) : Finset (V × V) := (s ×ˢ sᶜ).filter (fun e => G.Adj e.1 e.2)

private theorem memCutPair (s : Finset V) (v w : V) :
    (v,w) ∈ cutPairs G s ↔ v ∈ s ∧ w ∉ s ∧ G.Adj v w := by simp [cutPairs, and_assoc]

theorem cardCutPairs (s : Finset V) : (cutPairs G s).card = cutSize G s := by
  classical
  unfold cutPairs cutSize
  have hs : ((s ×ˢ sᶜ).filter (fun v : V × V => G.Adj v.1 v.2)).card =
      ∑ v ∈ s ×ˢ sᶜ, if G.Adj v.1 v.2 then 1 else 0 := by simp
  rw [hs, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [Finset.sum_boole, Nat.cast_id]
  apply congrArg Finset.card
  ext w
  simp [and_comm]

private theorem cutSize_compl (s : Finset V) : cutSize G sᶜ = cutSize G s := by
  rw [← cardCutPairs, ← cardCutPairs]
  apply Finset.card_bij' (fun a _ => a.swap) (fun a _ => a.swap)
  all_goals (rintro ⟨a,b⟩ h; simp_all [cutPairs,G.adj_comm])

/-- Both sides have two or more vertices if a positive cut in a 5-regular
graph has fewer than five edges. -/
theorem nontrivialSmallCut (regular : ∀ v, G.degree v = 5) (s : Finset V)
    (pos : 0 < cutSize G s) (small : cutSize G s < 5) : 2 ≤ s.card ∧ 2 ≤ sᶜ.card := by
  classical
  have side (t : Finset V) (hpos : 0 < cutSize G t) (hsmall : cutSize G t < 5) : 2 ≤ t.card := by
    by_contra! hn
    rcases Nat.eq_zero_or_pos t.card with hz | hp
    · have := Finset.card_eq_zero.mp hz
      simp [this,cutSize] at hpos
    · have eq : t.card = 1 := by omega
      obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp eq
      have hcut : cutSize G {v} = G.degree v := by
        have hleave : G.neighborFinset v \ {v} = G.neighborFinset v := by
          ext w
          by_cases h : w = v <;> simp [h]
        simp [cutSize,hleave]
      rw [hcut,regular] at hsmall
      omega
  exact ⟨side s pos small, side sᶜ (by rwa [cutSize_compl]) (by rwa [cutSize_compl])⟩

/-- Joining the hub to either wing still leaves a proper induced subgraph,
so induction on the number of vertices applies to each wing. -/
theorem hubWingSmall (s : Finset V) (sizeL : 2 ≤ s.card) (sizeR : 2 ≤ sᶜ.card)
    (hub : V) (b : Bool) :
    Fintype.card {v : V // v = hub ∨ cutSide s v = b} < Fintype.card V := by
  classical
  have other (t : Finset V) (sz : 2 ≤ t.card) : ∃ w ∈ t, w ≠ hub := by
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp sz
    by_cases eq : x = hub
    · exact ⟨y,hy,fun hyh => hxy (eq.trans hyh.symm)⟩
    · exact ⟨x,hx,eq⟩
  cases b with
  | false =>
    obtain ⟨w,hw,ne⟩ := other _ sizeR
    exact Fintype.card_subtype_lt (x := w) (by simpa [cutSide,ne] using Finset.mem_compl.mp hw)
  | true =>
    obtain ⟨w,hw,ne⟩ := other _ sizeL
    exact Fintype.card_subtype_lt (x := w) (by simpa [cutSide,ne] using hw)

/-- Edges away from `hub` never cross this vertex partition. This is exactly
the separation hypothesis of `glueInducedAtVertex`. -/
def SplitsAtHub (s : Finset V) (hub : V) : Prop :=
  ∀ ⦃v w⦄, G.Adj v w → v ≠ hub → w ≠ hub → cutSide s v = cutSide s w

omit [Fintype V] [DecidableRel G.Adj] in
private theorem hubOfTouch (s : Finset V) (hub : V)
    (touch : ∀ a b, a ∈ s → b ∉ s → G.Adj a b → a = hub ∨ b = hub) : SplitsAtHub G s hub := by
  intro v w adj hv hw
  by_cases hvs : v ∈ s <;> by_cases hws : w ∈ s
  · simp [cutSide,hvs,hws]
  · exact ((touch _ _ hvs hws adj).elim hv hw).elim
  · exact ((touch _ _ hws hvs adj.symm).elim hw hv).elim
  · simp [cutSide,hvs,hws]

omit [Fintype V] in
theorem matchingPair {I : Type*} (L R : I → V)
    (wideL : ∃ i j, L i ≠ L j) (wideR : ∃ i j, R i ≠ R j) :
    ∃ i j, L i ≠ L j ∧ R i ≠ R j := by
  obtain ⟨i,j,hL⟩ := wideL
  by_cases hR : R i = R j
  · obtain ⟨u,v,h⟩ := wideR
    obtain ⟨k,hk⟩ : ∃ k, R k ≠ R i := by by_contra! hn; exact h ((hn u).trans (hn v).symm)
    by_cases eq : L k = L i
    · exact ⟨k,j,eq.trans_ne hL,fun he => hk (he.trans hR.symm)⟩
    · exact ⟨k,i,eq,hk⟩
  · exact ⟨i,j,hL,hR⟩

theorem reindex (i j : Fin 3) (hij : i ≠ j) :
    ∃ p : Equiv.Perm (Fin 3), p 1 = i ∧ p 2 = j := by
  let f := Equiv.swap (1 : Fin 3) i
  have hf : f 1 = i := Equiv.swap_apply_left _ _
  have ne : i ≠ f 2 := by rw [← hf]; exact f.injective.ne (by decide)
  refine ⟨f.trans (Equiv.swap (f 2) j), ?_, Equiv.swap_apply_left _ _⟩
  change Equiv.swap (f 2) j (f 1) = i
  rw [hf,Equiv.swap_apply_of_ne_of_ne ne hij]

/-- A cut with a single edge always yields an articulation partition, and a
three-edge cut either has the same form or admits the indexing required by
`gluePreparedSides`. In the latter case its vertex partition is `cutSide s`. -/
theorem smallCutLayout (s : Finset V) (hsize : cutSize G s = 1 ∨ cutSize G s = 3) :
    (∃ hub, SplitsAtHub G s hub) ∨ ∃ C : ThreeEdgeCut G, C.side = cutSide s := by
  classical
  by_cases hub : ∃ hub, SplitsAtHub G s hub
  · exact Or.inl hub
  right
  let P := cutPairs G s
  have ps : P.card = cutSize G s := cardCutPairs G s
  have good (x : P) := (memCutPair G s x.val.1 x.val.2).mp x.property
  have hL : ∃ i j : P, i.val.1 ≠ j.val.1 := by
    by_contra! hn
    have hp : 0 < P.card := by omega
    obtain ⟨z,hz⟩ := Finset.card_pos.mp hp
    apply hub
    refine ⟨z.1,hubOfTouch G s _ (fun a b ha hb adj => Or.inl ?_)⟩
    exact hn ⟨(a,b),(memCutPair G s a b).mpr ⟨ha,hb,adj⟩⟩ ⟨z,hz⟩
  have hR : ∃ i j : P, i.val.2 ≠ j.val.2 := by
    by_contra! hn
    have hp : 0 < P.card := by omega
    obtain ⟨z,hz⟩ := Finset.card_pos.mp hp
    apply hub
    refine ⟨z.2,hubOfTouch G s _ (fun a b ha hb adj => Or.inr ?_)⟩
    exact hn ⟨(a,b),(memCutPair G s a b).mpr ⟨ha,hb,adj⟩⟩ ⟨z,hz⟩
  obtain ⟨i,j,hl,hr⟩ := matchingPair (fun x : P => x.val.1) (fun x => x.val.2) hL hR
  have card3 : P.card = 3 := by
    have hgt := Finset.one_lt_card.mpr ⟨i.val,i.property,j.val,j.property,fun h => hl (congrArg Prod.fst h)⟩
    omega
  let e := (Fintype.equivFinOfCardEq (show Fintype.card P = 3 by simpa only [Fintype.card_coe] using card3)).symm
  obtain ⟨p,hp1,hp2⟩ := reindex (e.symm i) (e.symm j) (e.symm.injective.ne (fun h => hl (congrArg (fun a : P => a.val.1) h)))
  let ord := p.trans e
  have o1 : ord 1 = i := by simp [ord,hp1]
  have o2 : ord 2 = j := by simp [ord,hp2]
  let L (k) := (ord k).val.1
  let R (k) := (ord k).val.2
  let bnd (k) : G.edgeSet := ⟨s(L k, R k),(good (ord k)).2.2⟩
  refine ⟨{
    side := cutSide s
    left := L
    right := R
    edge := bnd
    unique := ?_
    edge_ends := fun _ => rfl
    side_left := ?_
    side_right := ?_
    left_distinct := ?_
    right_distinct := ?_
    cover := ?_ },rfl⟩
  · intro a b h
    have he := congrArg Subtype.val h
    change s(L a,R a) = s(L b,R b) at he
    rcases Sym2.eq_iff.mp he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact ord.injective (Subtype.ext (Prod.ext h₁ h₂))
    · have ha : L a ∈ s := (good (ord a)).1
      have hb : R b ∉ s := (good (ord b)).2.1
      exact (hb (h₁ ▸ ha)).elim
  · intro k; simp [cutSide,L,(good (ord k)).1]
  · intro k; simp [cutSide,R,(good (ord k)).2.1]
  · simpa only [L,o1,o2] using hl
  · simpa only [R,o1,o2] using hr
  · intro edge a b ha hb sa sb
    have hain : a ∈ s := by simpa [cutSide] using sa
    have hbout : b ∉ s := by simpa [cutSide] using sb
    obtain ⟨w,hw⟩ := Sym2.mem_iff_exists.mp ha
    have hbw : b = w := (Sym2.mem_iff.mp (hw ▸ hb)).resolve_left (fun eq => hbout (eq ▸ hain))
    have he : edge.val = s(a,b) := by rwa [hbw]
    have adj : G.Adj a b := G.mem_edgeSet.mp (he ▸ edge.property)
    let v : P := ⟨(a,b),(memCutPair G s _ _).mpr ⟨hain,hbout,adj⟩⟩
    obtain ⟨k,hk⟩ := ord.surjective v
    refine ⟨k,Subtype.ext ?_⟩
    simpa [bnd,L,R,hk,v] using he.symm

end TotalColorFive

end


section -- MultiSmallCut

/- Indexing the three crossing edges with multiplicity, or locating the
single vertex that separates the two wings. -/
namespace MultFive.Multi
open Finset TotalColorFive

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

private abbrev W (s : Finset V) (b : Bool) := {v // cutSide s v = b}
private abbrev Copies (m : Multi V) (s : Finset V) :=
  (x : W s false) × (y : W s true) × Fin (m.count x.val y.val)

private theorem cardCopies (m : Multi V) (s : Finset V) :
    Fintype.card (Copies m s) = m.cutSize s := by
  classical
  let l : W s false ≃ s := Equiv.subtypeEquivRight (fun v => by simp [cutSide])
  let r : W s true ≃ ↥(sᶜ : Finset V) := Equiv.subtypeEquivRight (fun v => by simp [cutSide])
  simp only [Copies,Fintype.card_sigma,Fintype.card_fin]
  calc
    _ = ∑ x : W s false, ∑ y : ↥(sᶜ : Finset V), m.count x.val y.val := by
      apply sum_congr rfl
      intro x _
      exact r.sum_comp (fun y => m.count x.val y.val)
    _ = ∑ x : s, ∑ y : ↥(sᶜ : Finset V), m.count x.val y.val :=
      l.sum_comp (fun x => ∑ y : ↥(sᶜ : Finset V), m.count x.val y.val)
    _ = _ := by
      change (∑ x ∈ s.attach, ∑ y ∈ sᶜ.attach, m.count x.val y.val) = _
      simp_rw [sum_attach sᶜ (m.count _)]
      exact sum_attach s (fun x => ∑ y ∈ sᶜ, m.count x y)

private def Splits (m : Multi V) (s : Finset V) (hub : V) : Prop :=
  ∀ x y, 0 < m.count x y → x ≠ hub → y ≠ hub → cutSide s x = cutSide s y

omit [Fintype V] in
private theorem hubOfTouch (m : Multi V) (s : Finset V) (hub : V)
    (touch : ∀ z : Copies m s, z.1.val = hub ∨ z.2.1.val = hub) : Splits m s hub := by
  intro x y pos xh yh
  by_contra diff
  cases hx : cutSide s x <;> cases hy : cutSide s y
  · exact diff (hx.trans hy.symm)
  · exact (touch ⟨⟨x,hx⟩,⟨y,hy⟩,⟨0,pos⟩⟩).elim xh yh
  · exact (touch ⟨⟨y,hy⟩,⟨x,hx⟩,⟨0,m.symm x y ▸ pos⟩⟩).elim yh xh
  · exact diff (hx.trans hy.symm)

private theorem countOrdering (m : Multi V) (s : Finset V) (e : Fin 3 ≃ Copies m s)
    (x : W s false) (y : W s true) :
    m.count x.val y.val =
    (cutIndices (fun i => (e i).1) (fun i => (e i).2.1) x y).card := by
  classical
  let f (v : Copies m s) : ℕ := if v.1 = x ∧ v.2.1 = y then 1 else 0
  have h : (∑ z : Copies m s, f z) = m.count x.val y.val := by
    calc
      _ = ∑ a : W s false, ∑ b : W s true, ∑ _k : Fin (m.count a.val b.val),
            if a = x ∧ b = y then (1 : ℕ) else 0 := by
        rw [Fintype.sum_sigma]
        apply sum_congr rfl
        intro a _
        rw [Fintype.sum_sigma]
      _ = _ := by simp [sum_ite_irrel,ite_and]
  rw [←h,←e.sum_comp f]
  simp [cutIndices,f]

/-- A one-edge cut, or a three-edge cut with a common terminal, separates at
a hub. Otherwise the three crossing edge copies have the indexing of Lemma 8. -/
private theorem layout (m : Multi V) (s : Finset V) (size : m.cutSize s = 1 ∨ m.cutSize s = 3) :
    (∃ hub, Splits m s hub) ∨
    ∃ ep : ∀ b, Fin 3 → W s b, (∀ b, ep b 1 ≠ ep b 2) ∧
      ∀ x y, m.count x.val y.val = (cutIndices (ep false) (ep true) x y).card := by
  classical
  by_cases hub : ∃ hub, Splits m s hub
  · exact Or.inl hub
  right
  have sz := cardCopies m s
  have nonempty : Nonempty (Copies m s) := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨base⟩ := nonempty
  let L (z : Copies m s) := z.1.val
  let R (z : Copies m s) := z.2.1.val
  have hl : ∃ i j, L i ≠ L j := by
    by_contra! hn
    exact hub ⟨L base,hubOfTouch m s _ (fun z => Or.inl (hn z base))⟩
  have hr : ∃ i j, R i ≠ R j := by
    by_contra! hn
    exact hub ⟨R base,hubOfTouch m s _ (fun z => Or.inr (hn z base))⟩
  obtain ⟨u,v,hu,hv⟩ := matchingPair L R hl hr
  have uv : u ≠ v := fun eq => hu (congrArg L eq)
  have gt := Fintype.one_lt_card_iff.mpr ⟨u,v,uv⟩
  let e := (Fintype.equivFinOfCardEq (show Fintype.card (Copies m s) = 3 by omega)).symm
  obtain ⟨p,h1,h2⟩ := reindex (e.symm u) (e.symm v) (e.symm.injective.ne uv)
  let ord := p.trans e
  have o1 : ord 1 = u := by simp [ord,h1]
  have o2 : ord 2 = v := by simp [ord,h2]
  let ep : (b : Bool) → Fin 3 → W s b
    | false,i => (ord i).1
    | true,i => (ord i).2.1
  refine ⟨ep,?_,countOrdering m s ord⟩
  intro b hi
  cases b
  · change (ord 1).1 = (ord 2).1 at hi
    rw [o1,o2] at hi
    exact hu (congrArg Subtype.val hi)
  · change (ord 1).2.1 = (ord 2).2.1 at hi
    rw [o1,o2] at hi
    exact hv (congrArg Subtype.val hi)


omit [DecidableEq V] in
theorem induce_degree_le (m : Multi V) (s : Set V) [Fintype s] (x : s) :
    (m.induce s).degree x ≤ m.degree x.val := by
  classical
  let e := Function.Embedding.subtype (· ∈ s)
  calc
    _ = ∑ y ∈ univ.map e, m.count x.val y := by simp [degree,induce,e]
    _ ≤ _ := sum_le_sum_of_subset (subset_univ _)

/-- The induction hypothesis on the order of a loopless multigraph. -/
def SmallerColorable (n : ℕ) : Prop :=
  ∀ {X : Type u} [Fintype X] [DecidableEq X] (g : Multi X),
    Fintype.card X < n → (∀ v, g.degree v ≤ 5) → g.Colorable

private theorem ofHub (m : Multi V) (part : V → Bool) (h : V)
    (split : ∀ x y, 0 < m.count x y → x ≠ h → y ≠ h → part x = part y)
    (small : ∀ b, Fintype.card {v // v = h ∨ part v = b} < Fintype.card V)
    (bound : ∀ v, m.degree v ≤ 5) (ih : SmallerColorable.{u} (Fintype.card V)) : m.Colorable := by
  apply glueInducedHub m h part split (by have := bound h; omega)
  intro b
  exact ih (m.induce _) (small b) (fun v => (induce_degree_le m _ v).trans (bound _))

/-- Color a graph whose cut has one or three edges and at least two vertices
on each side, using only smaller graphs of maximum degree at most five. -/
theorem colorable_of_small_cut (m : Multi V) (s : Finset V)
    (size : m.cutSize s = 1 ∨ m.cutSize s = 3)
    (leftSize : 2 ≤ s.card) (rightSize : 2 ≤ sᶜ.card)
    (bound : ∀ v, m.degree v ≤ 5) (ih : SmallerColorable.{u} (Fintype.card V)) : m.Colorable := by
  classical
  obtain ⟨hub,hs⟩ | ⟨ep,dis,cross⟩ := layout m s size
  · exact ofHub m _ hub hs (hubWingSmall s leftSize rightSize hub) bound ih
  apply glueThreeCut m (cutSide s) ep dis cross bound
  intro b
  apply ih _ _ (threeCutWingDegree m _ ep dis cross bound b)
  cases b
  · obtain ⟨z,hz⟩ := card_pos.mp (show 0 < sᶜ.card by omega)
    exact Fintype.card_subtype_lt (x := z) (by simp [cutSide,mem_compl.mp hz])
  · obtain ⟨z,hz⟩ := card_pos.mp (show 0 < s.card by omega)
    exact Fintype.card_subtype_lt (x := z) (by simp [cutSide,hz])


private theorem splitWingOrders (s : Finset V) (h : V)
    (left : ∃ v ∈ s, v ≠ h) (right : ∃ v ∉ s, v ≠ h) :
    ∀ b, Fintype.card {v // v = h ∨ cutSide s v = b} < Fintype.card V := by
  intro b
  cases b
  · obtain ⟨v,hv,ne⟩ := right
    exact Fintype.card_subtype_lt (x := v) (by simp [ne,cutSide,hv])
  · obtain ⟨v,hv,ne⟩ := left
    exact Fintype.card_subtype_lt (x := v) (by simp [ne,cutSide,hv])

omit [Fintype V] in
private theorem otherIn (s : Finset V) (h : V) (sz : 2 ≤ s.card) : ∃ v ∈ s, v ≠ h := by
  obtain ⟨x,hx,y,hy,xy⟩ := one_lt_card.mp sz
  by_cases eq : x = h
  · exact ⟨y,hy,fun e => xy (eq.trans e.symm)⟩
  · exact ⟨x,hx,eq⟩

/-- A one-edge cut also gives a strict reduction when one side consists of a
single vertex, provided that the graph has at least three vertices. -/
theorem colorable_of_one_cut (m : Multi V) (s : Finset V) (size : m.cutSize s = 1)
    (order : 3 ≤ Fintype.card V) (bound : ∀ v, m.degree v ≤ 5)
    (ih : SmallerColorable.{u} (Fintype.card V)) : m.Colorable := by
  classical
  have one : Fintype.card (Copies m s) = 1 := (cardCopies m s).trans size
  obtain ⟨z,unique⟩ := Fintype.card_eq_one_iff.mp one
  have zl : z.1.val ∈ s := by simpa [cutSide] using z.1.property
  have zr : z.2.1.val ∉ s := by simpa [cutSide] using z.2.1.property
  have ne : z.1.val ≠ z.2.1.val := fun h => zr (h ▸ zl)
  by_cases l : 2 ≤ s.card
  · apply ofHub m (cutSide s) z.1.val _ _ bound ih
    · exact hubOfTouch m s _ (fun w => Or.inl (congrArg (fun i : Copies m s => i.1.val) (unique w)))
    · exact splitWingOrders s _ (otherIn _ _ l) ⟨_,zr,ne.symm⟩
  · have r : 2 ≤ sᶜ.card := by have := card_add_card_compl s; omega
    obtain ⟨w,hw,wn⟩ := otherIn sᶜ z.2.1.val r
    apply ofHub m (cutSide s) z.2.1.val _ _ bound ih
    · exact hubOfTouch m s _ (fun w => Or.inr (congrArg (fun i : Copies m s => i.2.1.val) (unique w)))
    · exact splitWingOrders s _ ⟨_,zl,ne⟩ ⟨_,mem_compl.mp hw,wn⟩


private theorem cutComplement (m : Multi V) (s : Finset V) : m.cutSize sᶜ = m.cutSize s := by
  simp only [cutSize,compl_compl]
  rw [sum_comm]
  exact sum_congr rfl (fun x _ => sum_congr rfl (fun y _ => m.symm _ _))

private theorem cutSingleton (m : Multi V) (x : V) : m.cutSize {x} = m.degree x := by
  have h := sum_add_sum_compl ({x} : Finset V) (m.count x)
  simpa [cutSize,degree,m.loopless] using h

/-- Neither side of a positive cut of size below five can be a singleton in
a five-regular loopless multigraph. -/
theorem regular_small_cut_orders (m : Multi V) (reg : ∀ x, m.degree x = 5) (s : Finset V)
    (pos : 0 < m.cutSize s) (small : m.cutSize s < 5) : 2 ≤ s.card ∧ 2 ≤ sᶜ.card := by
  have side (t : Finset V) (hp : 0 < m.cutSize t) (hs : m.cutSize t < 5) : 2 ≤ t.card := by
    by_contra! wrong
    rcases Nat.eq_zero_or_pos t.card with hz | hn
    · rw [card_eq_zero.mp hz] at hp
      simp [cutSize] at hp
    · obtain ⟨x,rfl⟩ := card_eq_one.mp (show t.card = 1 by omega)
      rw [cutSingleton,reg] at hs
      omega
  exact ⟨side s pos small,side sᶜ (by rwa [cutComplement]) (by rwa [cutComplement])⟩

/-- The unmatched five-regular case of Theorem 3 in Kostochka's induction. -/
theorem colorable_of_regular_unmatched (m : Multi V) (reg : ∀ x, m.degree x = 5)
    (unmatched : ¬ ∃ M : m.support.Subgraph, M.IsPerfectMatching)
    (ih : SmallerColorable.{u} (Fintype.card V)) : m.Colorable := by
  obtain ⟨_,cuts,hcard,_,props⟩ := threeSmallOddCuts m reg unmatched
  obtain ⟨s,hs⟩ := card_pos.mp (show 0 < cuts.card by omega)
  have size := (props s hs).2.2.1
  obtain ⟨hl,hr⟩ := regular_small_cut_orders m reg s (by omega) (by omega)
  exact colorable_of_small_cut m s size hl hr (fun v => (reg v).le) ih

end MultFive.Multi

end


section -- MultiMinimal

/-
# Minimal-Counterexample, Doubling, and Cut-Arrangement Reduction (Kostochka 1996, Theorem 3)

This file formalizes the structural and recursive minimal-counterexample argument of
Section 6, Theorem 3 of A. V. Kostochka, "The total chromatic number of any multigraph
with maximum degree five is at most seven", *Discrete Mathematics* 162 (1996), 199–214
(pp. 212–213), over the public multigraph interface `MultFive.Multi` in `MultiCore.lean`,
aligned with the compiled `MultiTutte` (`Multi.cutSize`, `Multi.threeSmallOddCuts`) and
`MultiSmallCut` (`Multi.SmallerColorable`, `Multi.colorable_of_small_cut`) modules.

Input black boxes (supplied as explicit role hypotheses, and discharged from `MultiSmallCut`
and `MultiTutte` in `colorable_of_regular_matching` so only `(A)` remains):
* `(A)` `RegularMatchingColorable`: every 5-regular multigraph whose support has a perfect
  matching is 7-total-colorable (Theorem 2).
* `(B1)` `CutOneColorable` and `(B3)` `CutThreeHubColorable`: a 1-edge cut or a 3-edge cut
  all incident to a single hub vertex, with both sides of order ≥ 2, yields colorability
  under the smaller-order induction hypothesis (Lemma 6).
* `(C)` `CutThreeColorable` (or `(C-nonhub)` `CutThreeNonHubColorable`): a 3-edge cut with
  both sides of order ≥ 2 yields colorability under the smaller-order induction hypothesis
  (Lemma 8, subsuming `(B3)`).
* `(D)` `TutteOddPieces` (or strengthened `TutteThreePieces`, not even requiring oddness):
  a 5-regular multigraph lacking a perfect matching admits a separator `U` and three
  pairwise disjoint nonempty pieces disjoint from `U`, each with cut count in `{1, 3}` and
  all exterior neighbors in `U`.

Key edge-case verifications included directly:
* Edge-deletion monotonicity (`Colorable.of_le`, `Colorable.of_addEdge`) and equivalence
  transport (`comap`).
* Disconnected gluing (`colorable_of_cutCount_eq_zero`), ensuring a minimal counterexample
  has no proper 0-edge cut.
* Direct greedy extension from `G - s` whenever `m.degree s ≤ 2` (`colorable_of_degree_le_two`),
  eliminating `m.degree s ∈ {0, 1, 2}` unconditionally (in particular eliminating `m.degree s = 1`,
  where a `2 + 1 = 3` cut split across layers could otherwise occur in the doubled graph).
* Exact cut-count decomposition in `m.double s` (`cutCount_double`), general proof that at
  most one Tutte piece separates the two copies of `s` (`at_most_one_separates_copies`), and
  complete singleton/complement classification leaving no room for the third piece
  (`not_hasTutteThreePieces_double`).
-/

namespace MultFive

open Finset SimpleGraph

namespace Multi

/- ## Cut count, submultigraph monotonicity, and vertex-equivalence transport -/

/-- Transparent alias for the shared cut count `Multi.cutSize` from `MultiTutte`:
sum of edge multiplicities crossing from `s` to `sᶜ` (ordered pairs `x ∈ s, y ∈ sᶜ`). -/
abbrev cutCount {V : Type*} [Fintype V] [DecidableEq V] (m : Multi V) (s : Finset V) : ℕ :=
  m.cutSize s

/-- Pointwise submultigraph relation (`m₁` is obtained from `m₂` by deleting edges). -/
def Le {V : Type*} (m₁ m₂ : Multi V) : Prop :=
  ∀ x y, m₁.count x y ≤ m₂.count x y

/-- Pull back a multigraph along an equivalence of vertex types. -/
def comap {V W : Type*} (m : Multi W) (e : V ≃ W) : Multi V where
  count x y := m.count (e x) (e y)
  symm x y := m.symm (e x) (e y)
  loopless x := m.loopless (e x)

/-- The support simple graph of `m` admits a perfect matching. -/
abbrev HasPerfectMatching {V : Type*} (m : Multi V) : Prop :=
  ∃ M : m.support.Subgraph, M.IsPerfectMatching

/-- All edges crossing `[s, sᶜ]` are incident to a single vertex (a hub) on one side. -/
def HasCutHub {V : Type*} [Fintype V] [DecidableEq V] (m : Multi V) (s : Finset V) : Prop :=
  (∃ h ∈ s, ∀ x ∈ s, ∀ y ∈ sᶜ, 0 < m.count x y → x = h) ∨
  (∃ h ∈ sᶜ, ∀ x ∈ s, ∀ y ∈ sᶜ, 0 < m.count x y → y = h)

section BasicCut

variable {V : Type*} [Fintype V] [DecidableEq V] (m : Multi V)

lemma cutCount_compl (s : Finset V) : m.cutCount sᶜ = m.cutCount s := by
  unfold cutCount cutSize
  rw [compl_compl, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  exact m.symm y x

@[simp]
lemma cutCount_empty : m.cutCount ∅ = 0 := by
  simp [cutCount, cutSize]

@[simp]
lemma cutCount_univ : m.cutCount Finset.univ = 0 := by
  simp [cutCount, cutSize]

lemma cutCount_singleton (v : V) : m.cutCount {v} = m.degree v := by
  unfold cutCount cutSize degree
  rw [Finset.sum_singleton]
  have hsplit :
      (∑ w : V, m.count v w) =
        (∑ w ∈ ({v} : Finset V), m.count v w) + (∑ w ∈ ({v} : Finset V)ᶜ, m.count v w) := by
    rw [Finset.sum_add_sum_compl]
  rw [hsplit, Finset.sum_singleton, m.loopless v, zero_add]

lemma cutCount_compl_singleton (v : V) : m.cutCount ({v}ᶜ : Finset V) = m.degree v := by
  rw [cutCount_compl, cutCount_singleton]

lemma cutCount_eq_zero_iff (s : Finset V) :
    m.cutCount s = 0 ↔ ∀ x ∈ s, ∀ y ∈ sᶜ, m.count x y = 0 := by
  simp [cutCount, cutSize, Finset.sum_eq_zero_iff]

lemma hasCutHub_compl (s : Finset V) : m.HasCutHub sᶜ ↔ m.HasCutHub s := by
  unfold HasCutHub
  rw [compl_compl]
  constructor
  · rintro (⟨h, hh, hprop⟩ | ⟨h, hh, hprop⟩)
    · refine Or.inr ⟨h, hh, fun x hx y hy hpos => ?_⟩
      exact hprop y hy x hx (by rwa [m.symm y x])
    · refine Or.inl ⟨h, hh, fun x hx y hy hpos => ?_⟩
      exact hprop y hy x hx (by rwa [m.symm y x])
  · rintro (⟨h, hh, hprop⟩ | ⟨h, hh, hprop⟩)
    · refine Or.inr ⟨h, hh, fun x hx y hy hpos => ?_⟩
      exact hprop y hy x hx (by rwa [m.symm y x])
    · refine Or.inl ⟨h, hh, fun x hx y hy hpos => ?_⟩
      exact hprop y hy x hx (by rwa [m.symm y x])

end BasicCut

lemma degree_induce_le {V : Type*} [Fintype V] (m : Multi V) (s : Set V) [Fintype s] (x : s) :
    (m.induce s).degree x ≤ m.degree x.val := by
  classical
  unfold degree induce
  have h1 :
      (∑ w : s, m.count x.val w.val) =
        ∑ w ∈ Finset.univ.filter (fun v : V => v ∈ s), m.count x.val w := by
    refine Finset.sum_nbij' (fun w : s => w.val) (fun w : V => if hw : w ∈ s then ⟨w, hw⟩ else x)
      ?_ ?_ ?_ ?_ ?_
    · intro w _
      simp [w.property]
    · intro w _
      simp
    · intro w _
      simp
    · intro w hw
      have hws : w ∈ s := (Finset.mem_filter.mp hw).2
      simp [hws]
    · intro w _
      rfl
  rw [h1]
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)

section Monotonicity

/-- Canonical subset of `S : Finset (Fin 7)` of cardinality `k` (when `k ≤ S.card`). -/
private def takeColors (S : Finset (Fin 7)) (k : ℕ) : Finset (Fin 7) :=
  ((S.sort (· ≤ ·)).take k).toFinset

private lemma takeColors_subset (S : Finset (Fin 7)) (k : ℕ) : takeColors S k ⊆ S := by
  intro c hc
  unfold takeColors at hc
  rw [List.mem_toFinset] at hc
  have hmem : c ∈ S.sort (· ≤ ·) := List.mem_of_mem_take hc
  exact (Finset.mem_sort (· ≤ ·)).mp hmem

private lemma takeColors_card (S : Finset (Fin 7)) (k : ℕ) (hk : k ≤ S.card) :
    (takeColors S k).card = k := by
  unfold takeColors
  have hnodup : ((S.sort (· ≤ ·)).take k).Nodup := (S.sort_nodup (· ≤ ·)).take
  rw [List.toFinset_card_of_nodup hnodup, List.length_take, S.length_sort]
  exact Nat.min_eq_left hk

lemma Valid.of_le {V : Type*} {m₁ m₂ : Multi V} {vc ec}
    (hle : m₁.Le m₂) (h : m₂.Valid vc ec) :
    m₁.Valid vc (fun x y => takeColors (ec x y) (m₁.count x y)) where
  symmetric x y := by
    rw [h.symmetric x y, m₁.symm x y]
  size x y := by
    refine takeColors_card (ec x y) (m₁.count x y) ?_
    rw [h.size x y]
    exact hle x y
  vertices x y hpos := by
    exact h.vertices x y (lt_of_lt_of_le hpos (hle x y))
  avoids x y hmem := by
    exact h.avoids x y (takeColors_subset _ _ hmem)
  disjoint x y z hyz := by
    exact (h.disjoint x y z hyz).mono (takeColors_subset _ _) (takeColors_subset _ _)

lemma Colorable.of_le {V : Type*} {m₁ m₂ : Multi V}
    (hle : m₁.Le m₂) (h : m₂.Colorable) : m₁.Colorable := by
  obtain ⟨vc, ec, hv⟩ := h
  exact ⟨vc, _, hv.of_le hle⟩

lemma le_addEdge {V : Type*} [DecidableEq V] (m : Multi V) (a b : V) (hne : a ≠ b) :
    m.Le (m.addEdge a b hne) := by
  intro x y
  simp [addEdge]

lemma Colorable.of_addEdge {V : Type*} [DecidableEq V] {m : Multi V} {a b : V} {hne : a ≠ b}
    (h : (m.addEdge a b hne).Colorable) : m.Colorable :=
  h.of_le (m.le_addEdge a b hne)

lemma degree_addEdge_left {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (a b : V) (hne : a ≠ b) :
    (m.addEdge a b hne).degree a = m.degree a + 1 := by
  unfold degree addEdge
  rw [Finset.sum_add_distrib]
  have h1 : (∑ w : V, if (a = a ∧ w = b) ∨ (a = b ∧ w = a) then 1 else 0) = 1 := by
    have heq :
        (fun w : V => if (a = a ∧ w = b) ∨ (a = b ∧ w = a) then (1 : ℕ) else 0) =
          fun w : V => if w = b then 1 else 0 := by
      funext w
      by_cases hwb : w = b <;> simp [hwb, hne]
    rw [heq]
    simp
  rw [h1]

lemma degree_addEdge_right {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (a b : V) (hne : a ≠ b) :
    (m.addEdge a b hne).degree b = m.degree b + 1 := by
  unfold degree addEdge
  rw [Finset.sum_add_distrib]
  have h1 : (∑ w : V, if (b = a ∧ w = b) ∨ (b = b ∧ w = a) then 1 else 0) = 1 := by
    have heq :
        (fun w : V => if (b = a ∧ w = b) ∨ (b = b ∧ w = a) then (1 : ℕ) else 0) =
          fun w : V => if w = a then 1 else 0 := by
      funext w
      by_cases hwa : w = a <;> simp [hwa, hne.symm]
    rw [heq]
    simp
  rw [h1]

lemma degree_addEdge_of_ne {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (a b v : V) (hne : a ≠ b) (hva : v ≠ a) (hvb : v ≠ b) :
    (m.addEdge a b hne).degree v = m.degree v := by
  unfold degree addEdge
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [hva, hvb]

lemma sum_degree_addEdge {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (a b : V) (hne : a ≠ b) :
    (∑ v : V, (m.addEdge a b hne).degree v) = (∑ v : V, m.degree v) + 2 := by
  have hfun :
      (fun v : V => (m.addEdge a b hne).degree v) =
        fun v : V => m.degree v + (if v = a then 1 else 0) + (if v = b then 1 else 0) := by
    funext v
    by_cases hva : v = a
    · subst hva
      simp [degree_addEdge_left, hne]
    · by_cases hvb : v = b
      · subst hvb
        simp [degree_addEdge_right, hne.symm]
      · simp [degree_addEdge_of_ne m a b v hne hva hvb, hva, hvb]
  rw [hfun, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp [add_assoc]

end Monotonicity

section Comap

lemma degree_comap {V W : Type*} [Fintype V] [Fintype W]
    (m : Multi W) (e : V ≃ W) (v : V) :
    (m.comap e).degree v = m.degree (e v) := by
  unfold degree comap
  exact Equiv.sum_comp e (fun w => m.count (e v) w)

lemma Valid.comap {V W : Type*} {m : Multi W} {vc ec}
    (h : m.Valid vc ec) (e : V ≃ W) :
    (m.comap e).Valid (fun x => vc (e x)) (fun x y => ec (e x) (e y)) where
  symmetric x y := h.symmetric (e x) (e y)
  size x y := h.size (e x) (e y)
  vertices x y hpos := h.vertices (e x) (e y) hpos
  avoids x y := h.avoids (e x) (e y)
  disjoint x y z hyz := h.disjoint (e x) (e y) (e z) (fun heq => hyz (e.injective heq))

lemma colorable_comap_iff {V W : Type*} (m : Multi W) (e : V ≃ W) :
    (m.comap e).Colorable ↔ m.Colorable := by
  constructor
  · rintro ⟨vc, ec, hv⟩
    refine ⟨fun x => vc (e.symm x), fun x y => ec (e.symm x) (e.symm y), ?_, ?_, ?_, ?_, ?_⟩
    · intro x y; exact hv.symmetric (e.symm x) (e.symm y)
    · intro x y; simpa [comap] using hv.size (e.symm x) (e.symm y)
    · intro x y hpos; exact hv.vertices (e.symm x) (e.symm y) (by simpa [comap] using hpos)
    · intro x y; exact hv.avoids (e.symm x) (e.symm y)
    · intro x y z hyz
      exact hv.disjoint (e.symm x) (e.symm y) (e.symm z) (fun heq => hyz (e.symm.injective heq))
  · rintro ⟨vc, ec, hv⟩
    exact ⟨_, _, hv.comap e⟩

end Comap

/- ## Disconnected gluing and greedy extension for vertices of degree ≤ 2 -/

/-- If a cut `[s, sᶜ]` has zero crossing edges and both induced subgraphs are colorable,
then the whole multigraph is colorable. -/
theorem colorable_of_cutCount_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (s : Finset V) (hcut : m.cutCount s = 0)
    (hs1 : (m.induce (s : Set V)).Colorable)
    (hs2 : (m.induce ((sᶜ : Finset V) : Set V)).Colorable) : m.Colorable := by
  have hzero : ∀ x ∈ s, ∀ y ∈ sᶜ, m.count x y = 0 := (m.cutCount_eq_zero_iff s).mp hcut
  obtain ⟨vc₁, ec₁, h₁⟩ := hs1
  obtain ⟨vc₂, ec₂, h₂⟩ := hs2
  refine ⟨fun x => if hx : x ∈ s then vc₁ ⟨x, hx⟩ else vc₂ ⟨x, Finset.mem_compl.mpr hx⟩,
    fun x y =>
      if hx : x ∈ s then
        if hy : y ∈ s then ec₁ ⟨x, hx⟩ ⟨y, hy⟩ else ∅
      else
        if hy : y ∈ s then ∅ else ec₂ ⟨x, Finset.mem_compl.mpr hx⟩ ⟨y, Finset.mem_compl.mpr hy⟩,
    ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s <;> simp [hx, hy, h₁.symmetric, h₂.symmetric]
  · intro x y
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
    · simp [hx, hy, h₁.size, induce]
    · simp only [hx, hy, ↓reduceDIte, Finset.card_empty]
      exact (hzero x hx y (Finset.mem_compl.mpr hy)).symm
    · simp only [hx, hy, ↓reduceDIte, Finset.card_empty]
      rw [m.symm x y]
      exact (hzero y hy x (Finset.mem_compl.mpr hx)).symm
    · simp [hx, hy, h₂.size, induce]
  · intro x y hpos
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
    · simp only [hx, hy, ↓reduceDIte]
      exact h₁.vertices ⟨x, hx⟩ ⟨y, hy⟩ hpos
    · exfalso
      have := hzero x hx y (Finset.mem_compl.mpr hy)
      omega
    · exfalso
      rw [m.symm x y] at hpos
      have := hzero y hy x (Finset.mem_compl.mpr hx)
      omega
    · simp only [hx, hy, ↓reduceDIte]
      exact h₂.vertices ⟨x, Finset.mem_compl.mpr hx⟩ ⟨y, Finset.mem_compl.mpr hy⟩ hpos
  · intro x y
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s <;> simp [hx, hy, h₁.avoids, h₂.avoids]
  · intro x y z hyz
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s <;> by_cases hz : z ∈ s <;>
      simp only [hx, hy, hz, ↓reduceDIte, Finset.disjoint_empty_left, Finset.disjoint_empty_right]
    · exact h₁.disjoint ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ (fun heq => hyz (congrArg Subtype.val heq))
    · exact h₂.disjoint ⟨x, Finset.mem_compl.mpr hx⟩ ⟨y, Finset.mem_compl.mpr hy⟩
        ⟨z, Finset.mem_compl.mpr hz⟩ (fun heq => hyz (congrArg Subtype.val heq))

private lemma extend_deg_zero {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (s : V)
    {vc' : (({s}ᶜ : Finset V) : Set V) → Fin 7}
    {ec' : (({s}ᶜ : Finset V) : Set V) → (({s}ᶜ : Finset V) : Set V) → Finset (Fin 7)}
    (hv' : (m.induce (({s}ᶜ : Finset V) : Set V)).Valid vc' ec')
    (hzero : ∀ w, m.count s w = 0) : m.Colorable := by
  have hmemS : ∀ {w : V}, w ≠ s → w ∈ (({s}ᶜ : Finset V) : Set V) := fun hw => by simp [hw]
  refine ⟨fun x => if hx : x = s then 0 else vc' ⟨x, hmemS hx⟩,
    fun x y => if hx : x = s then ∅ else if hy : y = s then ∅ else ec' ⟨x, hmemS hx⟩ ⟨y, hmemS hy⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    by_cases hx : x = s <;> by_cases hy : y = s <;> simp [hx, hy, hv'.symmetric]
  · intro x y
    by_cases hx : x = s <;> by_cases hy : y = s
    · simp [hx, hy, m.loopless]
    · simp [hx, hzero]
    · simp [hx, hy, m.symm x s, hzero]
    · simp [hx, hy, hv'.size, induce]
  · intro x y hpos
    by_cases hx : x = s
    · subst x; simp [hzero] at hpos
    · by_cases hy : y = s
      · subst y; rw [m.symm x s] at hpos; simp [hzero] at hpos
      · simp only [hx, hy, ↓reduceDIte]
        exact hv'.vertices ⟨x, hmemS hx⟩ ⟨y, hmemS hy⟩ hpos
  · intro x y
    by_cases hx : x = s <;> by_cases hy : y = s <;> simp [hx, hy, hv'.avoids]
  · intro x y z hyz
    by_cases hx : x = s <;> by_cases hy : y = s <;> by_cases hz : z = s <;>
      simp [hx, hy, hz]
    exact hv'.disjoint ⟨x, hmemS hx⟩ ⟨y, hmemS hy⟩ ⟨z, hmemS hz⟩
      (fun heq => hyz (congrArg Subtype.val heq))

private lemma extend_deg_one_neighbor {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (s w : V) (hw : w ≠ s)
    {vc' : (({s}ᶜ : Finset V) : Set V) → Fin 7}
    {ec' : (({s}ᶜ : Finset V) : Set V) → (({s}ᶜ : Finset V) : Set V) → Finset (Fin 7)}
    (hv' : (m.induce (({s}ᶜ : Finset V) : Set V)).Valid vc' ec')
    (hother : ∀ u, u ≠ w → m.count s u = 0)
    (E : Finset (Fin 7)) (hE_card : E.card = m.count s w)
    (hE_vc : vc' ⟨w, by simp [hw]⟩ ∉ E)
    (hE_ec : ∀ u : (({s}ᶜ : Finset V) : Set V), Disjoint E (ec' ⟨w, by simp [hw]⟩ u))
    (cs : Fin 7) (hcs_vc : cs ≠ vc' ⟨w, by simp [hw]⟩) (hcs_E : cs ∉ E) :
    m.Colorable := by
  have hmemS : ∀ {u : V}, u ≠ s → u ∈ (({s}ᶜ : Finset V) : Set V) := fun hu => by simp [hu]
  let vc : V → Fin 7 := fun x => if hx : x = s then cs else vc' ⟨x, hmemS hx⟩
  let ec : V → V → Finset (Fin 7) := fun x y =>
    if (x = s ∧ y = w) ∨ (x = w ∧ y = s) then E
    else if hx : x = s then ∅
    else if hy : y = s then ∅
    else ec' ⟨x, hmemS hx⟩ ⟨y, hmemS hy⟩
  refine ⟨vc, ec, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    dsimp only [ec]
    by_cases h1 : (x = s ∧ y = w) ∨ (x = w ∧ y = s)
    · have h2 : (y = s ∧ x = w) ∨ (y = w ∧ x = s) := by tauto
      simp [h1, h2]
    · have h2 : ¬ ((y = s ∧ x = w) ∨ (y = w ∧ x = s)) := by tauto
      simp only [h1, h2, ↓reduceIte]
      by_cases hx : x = s <;> by_cases hy : y = s <;> simp [hx, hy, hv'.symmetric]
  · intro x y
    dsimp only [ec]
    by_cases h1 : (x = s ∧ y = w) ∨ (x = w ∧ y = s)
    · simp only [h1, ↓reduceIte]
      rcases h1 with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rw [hx, hy]; exact hE_card
      · rw [hx, hy, m.symm w s]; exact hE_card
    · simp only [h1, ↓reduceIte]
      by_cases hx : x = s
      · subst x
        have hyw : y ≠ w := fun hyw => h1 (Or.inl ⟨rfl, hyw⟩)
        simp [hother y hyw]
      · by_cases hy : y = s
        · subst y
          have hxw : x ≠ w := fun hxw => h1 (Or.inr ⟨hxw, rfl⟩)
          simp [hx, m.symm x s, hother x hxw]
        · simp [hx, hy, hv'.size, induce]
  · intro x y hpos
    dsimp only [vc]
    by_cases hx : x = s
    · subst x
      have hyw : y = w := by
        by_contra hyw
        have := hother y hyw
        omega
      subst y
      simp [hw, hcs_vc]
    · by_cases hy : y = s
      · subst y
        have hxw : x = w := by
          by_contra hxw
          rw [m.symm x s] at hpos
          have := hother x hxw
          omega
        subst x
        simp [hw, hcs_vc.symm]
      · simp only [hx, hy, ↓reduceDIte]
        exact hv'.vertices ⟨x, hmemS hx⟩ ⟨y, hmemS hy⟩ hpos
  · intro x y
    dsimp only [vc, ec]
    by_cases h1 : (x = s ∧ y = w) ∨ (x = w ∧ y = s)
    · simp only [h1, ↓reduceIte]
      rcases h1 with ⟨hx, _⟩ | ⟨hx, _⟩
      · rw [hx]; simp [hcs_E]
      · rw [hx]; simp [hw, hE_vc]
    · simp only [h1, ↓reduceIte]
      by_cases hx : x = s <;> by_cases hy : y = s <;> simp [hx, hy, hv'.avoids]
  · intro x y z hyz
    dsimp only [ec]
    by_cases hx : x = s
    · subst x
      by_cases hyw : y = w
      · subst y
        have hzw : z ≠ w := hyz.symm
        simp [hw.symm, hzw]
      · by_cases hzw : z = w
        · subst z
          simp [hw.symm, hyw]
        · simp [hw.symm, hyw, hzw]
    · by_cases hxw : x = w
      · subst x
        by_cases hys : y = s
        · subst y
          have hzs : z ≠ s := hyz.symm
          have h1 : (w = s ∧ s = w) ∨ (w = w ∧ s = s) := Or.inr ⟨rfl, rfl⟩
          have h2 : ¬ ((w = s ∧ z = w) ∨ (w = w ∧ z = s)) := by
            rintro (⟨h, _⟩ | ⟨_, h⟩); exact hw h; exact hzs h
          rw [if_pos h1, if_neg h2, dif_neg hw, dif_neg hzs]
          exact hE_ec ⟨z, hmemS hzs⟩
        · by_cases hzs : z = s
          · subst z
            have h1 : ¬ ((w = s ∧ y = w) ∨ (w = w ∧ y = s)) := by
              rintro (⟨h, _⟩ | ⟨_, h⟩); exact hw h; exact hys h
            have h2 : (w = s ∧ s = w) ∨ (w = w ∧ s = s) := Or.inr ⟨rfl, rfl⟩
            rw [if_neg h1, dif_neg hw, dif_neg hys, if_pos h2]
            exact (hE_ec ⟨y, hmemS hys⟩).symm
          · have h1 : ¬ ((w = s ∧ y = w) ∨ (w = w ∧ y = s)) := by
              rintro (⟨h, _⟩ | ⟨_, h⟩); exact hw h; exact hys h
            have h2 : ¬ ((w = s ∧ z = w) ∨ (w = w ∧ z = s)) := by
              rintro (⟨h, _⟩ | ⟨_, h⟩); exact hw h; exact hzs h
            rw [if_neg h1, dif_neg hw, dif_neg hys, if_neg h2, dif_neg hw, dif_neg hzs]
            exact hv'.disjoint ⟨w, hmemS hw⟩ ⟨y, hmemS hys⟩ ⟨z, hmemS hzs⟩
              (fun heq => hyz (congrArg Subtype.val heq))
      · by_cases hys : y = s <;> by_cases hzs : z = s <;> simp [hx, hxw, hys, hzs]
        exact hv'.disjoint ⟨x, hmemS hx⟩ ⟨y, hmemS hys⟩ ⟨z, hmemS hzs⟩
          (fun heq => hyz (congrArg Subtype.val heq))

private lemma extend_deg_two_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (s w₁ w₂ : V) (hw12 : w₁ ≠ w₂) (hw₁ : w₁ ≠ s) (hw₂ : w₂ ≠ s)
    {vc' : (({s}ᶜ : Finset V) : Set V) → Fin 7}
    {ec' : (({s}ᶜ : Finset V) : Set V) → (({s}ᶜ : Finset V) : Set V) → Finset (Fin 7)}
    (hv' : (m.induce (({s}ᶜ : Finset V) : Set V)).Valid vc' ec')
    (hcnt₁ : m.count s w₁ = 1) (hcnt₂ : m.count s w₂ = 1)
    (hother : ∀ u, u ≠ w₁ → u ≠ w₂ → m.count s u = 0)
    (c₁ c₂ cs : Fin 7) (hc₂_ne_c₁ : c₂ ≠ c₁)
    (hc₁_vc : c₁ ≠ vc' ⟨w₁, by simp [hw₁]⟩)
    (hc₁_ec : ∀ u : (({s}ᶜ : Finset V) : Set V), c₁ ∉ ec' ⟨w₁, by simp [hw₁]⟩ u)
    (hc₂_vc : c₂ ≠ vc' ⟨w₂, by simp [hw₂]⟩)
    (hc₂_ec : ∀ u : (({s}ᶜ : Finset V) : Set V), c₂ ∉ ec' ⟨w₂, by simp [hw₂]⟩ u)
    (hcs_ne1 : cs ≠ vc' ⟨w₁, by simp [hw₁]⟩) (hcs_ne2 : cs ≠ vc' ⟨w₂, by simp [hw₂]⟩)
    (hcs_nec1 : cs ≠ c₁) (hcs_nec2 : cs ≠ c₂) :
    m.Colorable := by
  have hmemS : ∀ {u : V}, u ≠ s → u ∈ (({s}ᶜ : Finset V) : Set V) := fun hu => by simp [hu]
  let vc : V → Fin 7 := fun x => if hx : x = s then cs else vc' ⟨x, hmemS hx⟩
  let ec : V → V → Finset (Fin 7) := fun x y =>
    if (x = s ∧ y = w₁) ∨ (x = w₁ ∧ y = s) then {c₁}
    else if (x = s ∧ y = w₂) ∨ (x = w₂ ∧ y = s) then {c₂}
    else if hx : x = s then ∅
    else if hy : y = s then ∅
    else ec' ⟨x, hmemS hx⟩ ⟨y, hmemS hy⟩
  refine ⟨vc, ec, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    dsimp only [ec]
    by_cases h1 : (x = s ∧ y = w₁) ∨ (x = w₁ ∧ y = s)
    · have h1' : (y = s ∧ x = w₁) ∨ (y = w₁ ∧ x = s) := by tauto
      rw [if_pos h1, if_pos h1']
    · have h1' : ¬ ((y = s ∧ x = w₁) ∨ (y = w₁ ∧ x = s)) := by tauto
      rw [if_neg h1, if_neg h1']
      by_cases h2 : (x = s ∧ y = w₂) ∨ (x = w₂ ∧ y = s)
      · have h2' : (y = s ∧ x = w₂) ∨ (y = w₂ ∧ x = s) := by tauto
        rw [if_pos h2, if_pos h2']
      · have h2' : ¬ ((y = s ∧ x = w₂) ∨ (y = w₂ ∧ x = s)) := by tauto
        rw [if_neg h2, if_neg h2']
        by_cases hx : x = s <;> by_cases hy : y = s <;> simp [hx, hy, hv'.symmetric]
  · intro x y
    dsimp only [ec]
    by_cases h1 : (x = s ∧ y = w₁) ∨ (x = w₁ ∧ y = s)
    · rw [if_pos h1, Finset.card_singleton]
      rcases h1 with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rw [hx, hy]; exact hcnt₁.symm
      · rw [hx, hy, m.symm w₁ s]; exact hcnt₁.symm
    · rw [if_neg h1]
      by_cases h2 : (x = s ∧ y = w₂) ∨ (x = w₂ ∧ y = s)
      · rw [if_pos h2, Finset.card_singleton]
        rcases h2 with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · rw [hx, hy]; exact hcnt₂.symm
        · rw [hx, hy, m.symm w₂ s]; exact hcnt₂.symm
      · rw [if_neg h2]
        by_cases hx : x = s
        · subst x
          have hy1 : y ≠ w₁ := fun h => h1 (Or.inl ⟨rfl, h⟩)
          have hy2 : y ≠ w₂ := fun h => h2 (Or.inl ⟨rfl, h⟩)
          simp [hother y hy1 hy2]
        · by_cases hy : y = s
          · subst y
            have hx1 : x ≠ w₁ := fun h => h1 (Or.inr ⟨h, rfl⟩)
            have hx2 : x ≠ w₂ := fun h => h2 (Or.inr ⟨h, rfl⟩)
            simp [hx, m.symm x s, hother x hx1 hx2]
          · simp [hx, hy, hv'.size, induce]
  · intro x y hpos
    dsimp only [vc]
    by_cases hx : x = s
    · subst x
      have hy12 : y = w₁ ∨ y = w₂ := by
        by_contra hnot
        simp only [not_or] at hnot
        have := hother y hnot.1 hnot.2
        omega
      rcases hy12 with hy | hy
      · subst y; simp [hw₁, hcs_ne1]
      · subst y; simp [hw₂, hcs_ne2]
    · by_cases hy : y = s
      · subst y
        have hx12 : x = w₁ ∨ x = w₂ := by
          by_contra hnot
          simp only [not_or] at hnot
          rw [m.symm x s] at hpos
          have := hother x hnot.1 hnot.2
          omega
        rcases hx12 with hx' | hx'
        · subst x; simp [hw₁, hcs_ne1.symm]
        · subst x; simp [hw₂, hcs_ne2.symm]
      · simp only [hx, hy, ↓reduceDIte]
        exact hv'.vertices ⟨x, hmemS hx⟩ ⟨y, hmemS hy⟩ hpos
  · intro x y
    dsimp only [vc, ec]
    by_cases h1 : (x = s ∧ y = w₁) ∨ (x = w₁ ∧ y = s)
    · rw [if_pos h1]
      rcases h1 with ⟨hx, _⟩ | ⟨hx, _⟩
      · rw [hx]; simp [hcs_nec1]
      · rw [hx, dif_neg hw₁, Finset.mem_singleton]
        exact hc₁_vc.symm
    · rw [if_neg h1]
      by_cases h2 : (x = s ∧ y = w₂) ∨ (x = w₂ ∧ y = s)
      · rw [if_pos h2]
        rcases h2 with ⟨hx, _⟩ | ⟨hx, _⟩
        · rw [hx]; simp [hcs_nec2]
        · rw [hx, dif_neg hw₂, Finset.mem_singleton]
          exact hc₂_vc.symm
      · rw [if_neg h2]
        by_cases hx : x = s <;> by_cases hy : y = s <;> simp [hx, hy, hv'.avoids]
  · intro x y z hyz
    dsimp only [ec]
    by_cases hx : x = s
    · subst x
      by_cases hy1 : y = w₁
      · subst y
        have hz1 : z ≠ w₁ := hyz.symm
        by_cases hz2 : z = w₂
        · subst z
          simp [hw₁.symm, hw₂.symm, hw12.symm, hc₂_ne_c₁.symm]
        · simp [hw₁.symm, hw₂.symm, hz1, hz2]
      · by_cases hy2 : y = w₂
        · subst y
          have hz2 : z ≠ w₂ := hyz.symm
          by_cases hz1 : z = w₁
          · subst z
            simp [hw₁.symm, hw₂.symm, hw12.symm, hc₂_ne_c₁]
          · simp [hw₁.symm, hw₂.symm, hz1, hz2]
        · simp [hw₁.symm, hw₂.symm, hy1, hy2]
    · by_cases hx1 : x = w₁
      · subst x
        have h1s : (w₁ = s ∧ s = w₁) ∨ (w₁ = w₁ ∧ s = s) := Or.inr ⟨rfl, rfl⟩
        by_cases hys : y = s
        · subst y
          have hzs : z ≠ s := hyz.symm
          have h1z : ¬ ((w₁ = s ∧ z = w₁) ∨ (w₁ = w₁ ∧ z = s)) := by
            rintro (⟨h, _⟩ | ⟨_, h⟩); exact hw₁ h; exact hzs h
          have h2z : ¬ ((w₁ = s ∧ z = w₂) ∨ (w₁ = w₂ ∧ z = s)) := by
            rintro (⟨h, _⟩ | ⟨h, _⟩); exact hw₁ h; exact hw12 h
          rw [if_pos h1s, if_neg h1z, if_neg h2z, dif_neg hw₁, dif_neg hzs,
            Finset.disjoint_singleton_left]
          exact hc₁_ec ⟨z, hmemS hzs⟩
        · by_cases hzs : z = s
          · subst z
            have h1y : ¬ ((w₁ = s ∧ y = w₁) ∨ (w₁ = w₁ ∧ y = s)) := by
              rintro (⟨h, _⟩ | ⟨_, h⟩); exact hw₁ h; exact hys h
            have h2y : ¬ ((w₁ = s ∧ y = w₂) ∨ (w₁ = w₂ ∧ y = s)) := by
              rintro (⟨h, _⟩ | ⟨h, _⟩); exact hw₁ h; exact hw12 h
            rw [if_neg h1y, if_neg h2y, dif_neg hw₁, dif_neg hys, if_pos h1s,
              Finset.disjoint_singleton_right]
            exact hc₁_ec ⟨y, hmemS hys⟩
          · have h1y : ¬ ((w₁ = s ∧ y = w₁) ∨ (w₁ = w₁ ∧ y = s)) := by
              rintro (⟨h, _⟩ | ⟨_, h⟩); exact hw₁ h; exact hys h
            have h2y : ¬ ((w₁ = s ∧ y = w₂) ∨ (w₁ = w₂ ∧ y = s)) := by
              rintro (⟨h, _⟩ | ⟨h, _⟩); exact hw₁ h; exact hw12 h
            have h1z : ¬ ((w₁ = s ∧ z = w₁) ∨ (w₁ = w₁ ∧ z = s)) := by
              rintro (⟨h, _⟩ | ⟨_, h⟩); exact hw₁ h; exact hzs h
            have h2z : ¬ ((w₁ = s ∧ z = w₂) ∨ (w₁ = w₂ ∧ z = s)) := by
              rintro (⟨h, _⟩ | ⟨h, _⟩); exact hw₁ h; exact hw12 h
            rw [if_neg h1y, if_neg h2y, dif_neg hw₁, dif_neg hys,
              if_neg h1z, if_neg h2z, dif_neg hw₁, dif_neg hzs]
            exact hv'.disjoint ⟨w₁, hmemS hw₁⟩ ⟨y, hmemS hys⟩ ⟨z, hmemS hzs⟩
              (fun heq => hyz (congrArg Subtype.val heq))
      · by_cases hx2 : x = w₂
        · subst x
          have h1s : ¬ ((w₂ = s ∧ s = w₁) ∨ (w₂ = w₁ ∧ s = s)) := by
            rintro (⟨h, _⟩ | ⟨h, _⟩); exact hw₂ h; exact hw12.symm h
          have h2s : (w₂ = s ∧ s = w₂) ∨ (w₂ = w₂ ∧ s = s) := Or.inr ⟨rfl, rfl⟩
          by_cases hys : y = s
          · subst y
            have hzs : z ≠ s := hyz.symm
            have h1z : ¬ ((w₂ = s ∧ z = w₁) ∨ (w₂ = w₁ ∧ z = s)) := by
              rintro (⟨h, _⟩ | ⟨h, _⟩); exact hw₂ h; exact hw12.symm h
            have h2z : ¬ ((w₂ = s ∧ z = w₂) ∨ (w₂ = w₂ ∧ z = s)) := by
              rintro (⟨h, _⟩ | ⟨_, h⟩); exact hw₂ h; exact hzs h
            rw [if_neg h1s, if_pos h2s, if_neg h1z, if_neg h2z, dif_neg hw₂, dif_neg hzs,
              Finset.disjoint_singleton_left]
            exact hc₂_ec ⟨z, hmemS hzs⟩
          · by_cases hzs : z = s
            · subst z
              have h1y : ¬ ((w₂ = s ∧ y = w₁) ∨ (w₂ = w₁ ∧ y = s)) := by
                rintro (⟨h, _⟩ | ⟨h, _⟩); exact hw₂ h; exact hw12.symm h
              have h2y : ¬ ((w₂ = s ∧ y = w₂) ∨ (w₂ = w₂ ∧ y = s)) := by
                rintro (⟨h, _⟩ | ⟨_, h⟩); exact hw₂ h; exact hys h
              rw [if_neg h1y, if_neg h2y, dif_neg hw₂, dif_neg hys, if_neg h1s, if_pos h2s,
                Finset.disjoint_singleton_right]
              exact hc₂_ec ⟨y, hmemS hys⟩
            · have h1y : ¬ ((w₂ = s ∧ y = w₁) ∨ (w₂ = w₁ ∧ y = s)) := by
                rintro (⟨h, _⟩ | ⟨h, _⟩); exact hw₂ h; exact hw12.symm h
              have h2y : ¬ ((w₂ = s ∧ y = w₂) ∨ (w₂ = w₂ ∧ y = s)) := by
                rintro (⟨h, _⟩ | ⟨_, h⟩); exact hw₂ h; exact hys h
              have h1z : ¬ ((w₂ = s ∧ z = w₁) ∨ (w₂ = w₁ ∧ z = s)) := by
                rintro (⟨h, _⟩ | ⟨h, _⟩); exact hw₂ h; exact hw12.symm h
              have h2z : ¬ ((w₂ = s ∧ z = w₂) ∨ (w₂ = w₂ ∧ z = s)) := by
                rintro (⟨h, _⟩ | ⟨_, h⟩); exact hw₂ h; exact hzs h
              rw [if_neg h1y, if_neg h2y, dif_neg hw₂, dif_neg hys,
                if_neg h1z, if_neg h2z, dif_neg hw₂, dif_neg hzs]
              exact hv'.disjoint ⟨w₂, hmemS hw₂⟩ ⟨y, hmemS hys⟩ ⟨z, hmemS hzs⟩
                (fun heq => hyz (congrArg Subtype.val heq))
        · by_cases hys : y = s <;> by_cases hzs : z = s <;> simp [hx, hx1, hx2, hys, hzs]
          exact hv'.disjoint ⟨x, hmemS hx⟩ ⟨y, hmemS hys⟩ ⟨z, hmemS hzs⟩
            (fun heq => hyz (congrArg Subtype.val heq))

/-- Any vertex `s` of degree at most 2 in a multigraph of maximum degree at most 5 can be
greedily added to any 7-total-coloring of `m - s`.
This eliminates `m.degree s ∈ {0, 1, 2}` unconditionally (including `m.degree s = 1`, where
a `2 + 1 = 3` layer split would otherwise be possible in `m.double s`). -/
theorem colorable_of_degree_le_two {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (hdeg : ∀ v, m.degree v ≤ 5) (s : V) (hs : m.degree s ≤ 2)
    (hsub : (m.induce (({s}ᶜ : Finset V) : Set V)).Colorable) : m.Colorable := by
  obtain ⟨vc', ec', hv'⟩ := hsub
  let S : Finset V := ({s} : Finset V)ᶜ
  have hmemS : ∀ {w : V}, w ≠ s → w ∈ (S : Set V) := fun hw => by simp [S, hw]
  -- Colors used at `w ≠ s` in `m.induce S` (vertex color and all incident edge colors)
  let used (w : V) (hw : w ≠ s) : Finset (Fin 7) :=
    insert (vc' ⟨w, hmemS hw⟩) (Finset.univ.biUnion fun u : (S : Set V) => ec' ⟨w, hmemS hw⟩ u)
  let free (w : V) (hw : w ≠ s) : Finset (Fin 7) := Finset.univ \ used w hw
  have hused_card : ∀ (w : V) (hw : w ≠ s), (used w hw).card + m.count s w ≤ 6 := by
    intro w hw
    have h1 : (used w hw).card ≤
        1 + (Finset.univ.biUnion fun u : (S : Set V) => ec' ⟨w, hmemS hw⟩ u).card := by
      simpa [used, add_comm] using Finset.card_insert_le (vc' ⟨w, hmemS hw⟩)
        (Finset.univ.biUnion fun u : (S : Set V) => ec' ⟨w, hmemS hw⟩ u)
    have h2 : (Finset.univ.biUnion fun u : (S : Set V) => ec' ⟨w, hmemS hw⟩ u).card ≤
        ∑ u : (S : Set V), (ec' ⟨w, hmemS hw⟩ u).card := Finset.card_biUnion_le
    have h3 : (∑ u : (S : Set V), (ec' ⟨w, hmemS hw⟩ u).card) = ∑ u ∈ S, m.count w u := by
      calc
        (∑ u : (S : Set V), (ec' ⟨w, hmemS hw⟩ u).card)
            = ∑ u : (S : Set V), m.count w u.val := by
              refine Finset.sum_congr rfl fun u _ => ?_
              exact hv'.size ⟨w, hmemS hw⟩ u
        _ = ∑ u ∈ S, m.count w u := by
              refine Finset.sum_nbij' (fun u => u.val)
                (fun u => if hu : u ∈ S then ⟨u, hu⟩ else ⟨w, hmemS hw⟩) ?_ ?_ ?_ ?_ ?_
              · intro u _; exact u.property
              · intro u _; simp
              · intro u _; simp
              · intro u hu; simp [hu]
              · intro u _; rfl
    have h4 : m.count w s + ∑ u ∈ S, m.count w u = m.degree w := by
      unfold degree
      have hsp := Finset.sum_add_sum_compl ({s} : Finset V) (fun u => m.count w u)
      simpa [S] using hsp
    have h5 : m.degree w ≤ 5 := hdeg w
    rw [m.symm s w]
    omega
  have hfree_card : ∀ (w : V) (hw : w ≠ s), 1 + m.count s w ≤ (free w hw).card := by
    intro w hw
    have hu := hused_card w hw
    have hc : (free w hw).card = 7 - (used w hw).card := by
      dsimp only [free]
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  have hvc_not_free : ∀ (w : V) (hw : w ≠ s) {c : Fin 7}, c ∈ free w hw → c ≠ vc' ⟨w, hmemS hw⟩ := by
    intro w hw c hc heq
    have hnu : c ∉ used w hw := (Finset.mem_sdiff.mp hc).2
    apply hnu
    simp [used, heq]
  have hec_not_free : ∀ (w : V) (hw : w ≠ s) (u : (S : Set V)) {c : Fin 7},
      c ∈ free w hw → c ∉ ec' ⟨w, hmemS hw⟩ u := by
    intro w hw u c hc hmem
    have hnu : c ∉ used w hw := (Finset.mem_sdiff.mp hc).2
    apply hnu
    simp only [used, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inr ⟨u, hmem⟩
  -- Neighbor set of `s`
  let N : Finset V := Finset.univ.filter fun w => 0 < m.count s w
  have hN_ne_s : ∀ w ∈ N, w ≠ s := by
    intro w hw heq
    subst heq
    have : 0 < m.count w w := (Finset.mem_filter.mp hw).2
    simp [m.loopless] at this
  have hsum_N : (∑ w ∈ N, m.count s w) = m.degree s := by
    unfold degree
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : 0 < m.count s w
    · simp [h]
    · have h0 : m.count s w = 0 := Nat.eq_zero_of_not_pos h
      simp [h0]
  have hN_card_le : N.card ≤ 2 := by
    have hle : N.card ≤ ∑ w ∈ N, m.count s w := by
      calc
        N.card = ∑ _w ∈ N, 1 := by simp
        _ ≤ ∑ w ∈ N, m.count s w := by
          refine Finset.sum_le_sum fun w hw => ?_
          exact (Finset.mem_filter.mp hw).2
    omega
  have hcases : N.card = 0 ∨ N.card = 1 ∨ N.card = 2 := by omega
  rcases hcases with hN0 | hN1 | hN2
  · have hzero : ∀ w, m.count s w = 0 := by
      intro w
      by_contra hne
      have hpos : 0 < m.count s w := Nat.pos_of_ne_zero hne
      have hw : w ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩
      have hposN : 0 < N.card := Finset.card_pos.mpr ⟨w, hw⟩
      omega
    exact extend_deg_zero m s hv' hzero
  · obtain ⟨w, hNw⟩ := Finset.card_eq_one.mp hN1
    have hwN : w ∈ N := by simp [hNw]
    have hw : w ≠ s := hN_ne_s w hwN
    have hother : ∀ u, u ≠ w → m.count s u = 0 := by
      intro u hu
      by_contra hne
      have : u ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hne⟩
      rw [hNw, Finset.mem_singleton] at this
      exact hu this
    have hcnt_le : m.count s w ≤ 2 := by
      have : m.count s w = m.degree s := by rw [← hsum_N, hNw, Finset.sum_singleton]
      omega
    obtain ⟨E, hE_sub, hE_card⟩ :=
      Finset.exists_subset_card_eq (by have := hfree_card w hw; omega : m.count s w ≤ (free w hw).card)
    have hforb_card : (insert (vc' ⟨w, hmemS hw⟩) E).card < (Finset.univ : Finset (Fin 7)).card := by
      have h1 : (insert (vc' ⟨w, hmemS hw⟩) E).card ≤ E.card + 1 := Finset.card_insert_le _ _
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨cs, _, hcs_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hforb_card
    refine extend_deg_one_neighbor m s w hw hv' hother E hE_card ?_ ?_ cs
      (fun h => hcs_not (Finset.mem_insert.mpr (Or.inl h)))
      (fun h => hcs_not (Finset.mem_insert.mpr (Or.inr h)))
    · intro hmem; exact hvc_not_free w hw (hE_sub hmem) rfl
    · intro u; rw [Finset.disjoint_left]; intro c hcE; exact hec_not_free w hw u (hE_sub hcE)
  · obtain ⟨w₁, w₂, hw12, hNw⟩ := Finset.card_eq_two.mp hN2
    have hw₁N : w₁ ∈ N := by simp [hNw]
    have hw₂N : w₂ ∈ N := by simp [hNw]
    have hw₁ : w₁ ≠ s := hN_ne_s w₁ hw₁N
    have hw₂ : w₂ ≠ s := hN_ne_s w₂ hw₂N
    have hpos₁ : 0 < m.count s w₁ := (Finset.mem_filter.mp hw₁N).2
    have hpos₂ : 0 < m.count s w₂ := (Finset.mem_filter.mp hw₂N).2
    have hsum12 : m.count s w₁ + m.count s w₂ = m.degree s := by
      rw [← hsum_N, hNw, Finset.sum_pair hw12]
    have hcnt₁ : m.count s w₁ = 1 := by omega
    have hcnt₂ : m.count s w₂ = 1 := by omega
    have hother : ∀ u, u ≠ w₁ → u ≠ w₂ → m.count s u = 0 := by
      intro u hu1 hu2
      by_contra hne
      have : u ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hne⟩
      rw [hNw, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact hu1 rfl
      · exact hu2 rfl
    have hfree₁_pos : 0 < (free w₁ hw₁).card := by have := hfree_card w₁ hw₁; omega
    obtain ⟨c₁, hc₁⟩ := Finset.card_pos.mp hfree₁_pos
    have hfree₂_ge : 2 ≤ (free w₂ hw₂).card := by have := hfree_card w₂ hw₂; omega
    have herase_pos : 0 < ((free w₂ hw₂).erase c₁).card := by
      have := Finset.pred_card_le_card_erase (s := free w₂ hw₂) (a := c₁)
      omega
    obtain ⟨c₂, hc₂_er⟩ := Finset.card_pos.mp herase_pos
    have hc₂_ne_c₁ : c₂ ≠ c₁ := (Finset.mem_erase.mp hc₂_er).1
    have hc₂ : c₂ ∈ free w₂ hw₂ := (Finset.mem_erase.mp hc₂_er).2
    let forb : Finset (Fin 7) := {vc' ⟨w₁, hmemS hw₁⟩, vc' ⟨w₂, hmemS hw₂⟩, c₁, c₂}
    have hforb_card : forb.card < (Finset.univ : Finset (Fin 7)).card := by
      have h1 : forb.card ≤ 4 := by
        dsimp only [forb]
        calc
          ({vc' ⟨w₁, hmemS hw₁⟩, vc' ⟨w₂, hmemS hw₂⟩, c₁, c₂} : Finset (Fin 7)).card
              ≤ ({vc' ⟨w₂, hmemS hw₂⟩, c₁, c₂} : Finset (Fin 7)).card + 1 := Finset.card_insert_le _ _
          _ ≤ (({c₁, c₂} : Finset (Fin 7)).card + 1) + 1 := by
              have := Finset.card_insert_le (vc' ⟨w₂, hmemS hw₂⟩) ({c₁, c₂} : Finset (Fin 7))
              omega
          _ ≤ ((({c₂} : Finset (Fin 7)).card + 1) + 1) + 1 := by
              have := Finset.card_insert_le c₁ ({c₂} : Finset (Fin 7))
              omega
          _ = 4 := by simp
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨cs, _, hcs_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hforb_card
    exact extend_deg_two_neighbors m s w₁ w₂ hw12 hw₁ hw₂ hv' hcnt₁ hcnt₂ hother c₁ c₂ cs
      hc₂_ne_c₁ (hvc_not_free w₁ hw₁ hc₁) (fun u => hec_not_free w₁ hw₁ u hc₁)
      (hvc_not_free w₂ hw₂ hc₂) (fun u => hec_not_free w₂ hw₂ u hc₂)
      (fun h => hcs_not (by simp [forb, h])) (fun h => hcs_not (by simp [forb, h]))
      (fun h => hcs_not (by simp [forb, h])) (fun h => hcs_not (by simp [forb, h]))

/- ## Edge-maximality reduction to at most one deficient vertex -/

/-- Nested deficit induction: to prove every bounded-degree multigraph on `V` is colorable,
it suffices to prove colorability for those having at most one vertex of degree `< 5`. -/
theorem colorable_of_at_most_one_deficient {V : Type*} [Fintype V] [DecidableEq V]
    (hstep : ∀ m : Multi V, (∀ v, m.degree v ≤ 5) →
      (∀ a b, m.degree a < 5 → m.degree b < 5 → a = b) → m.Colorable) :
    ∀ m : Multi V, (∀ v, m.degree v ≤ 5) → m.Colorable := by
  intro m hdeg
  -- Induct on the total degree deficit `5 * |V| - ∑ v, m.degree v`.
  suffices hmain : ∀ d : ℕ, ∀ m : Multi V, (∀ v, m.degree v ≤ 5) →
      5 * Fintype.card V - (∑ v : V, m.degree v) = d → m.Colorable by
    exact hmain _ m hdeg rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro m hdeg hd
    by_cases htwo : ∃ a b : V, a ≠ b ∧ m.degree a < 5 ∧ m.degree b < 5
    · obtain ⟨a, b, hab, ha, hb⟩ := htwo
      let m' := m.addEdge a b hab
      have hdeg' : ∀ v, m'.degree v ≤ 5 := by
        intro v
        by_cases hva : v = a
        · subst hva; rw [degree_addEdge_left]; omega
        · by_cases hvb : v = b
          · subst hvb; rw [degree_addEdge_right]; omega
          · rw [degree_addEdge_of_ne m a b v hab hva hvb]; exact hdeg v
      have hsum_le : (∑ v : V, m'.degree v) ≤ 5 * Fintype.card V := by
        calc
          (∑ v : V, m'.degree v) ≤ ∑ _v : V, 5 := Finset.sum_le_sum fun v _ => hdeg' v
          _ = 5 * Fintype.card V := by simp [mul_comm]
      have hsum_eq : (∑ v : V, m'.degree v) = (∑ v : V, m.degree v) + 2 :=
        sum_degree_addEdge m a b hab
      have hlt : 5 * Fintype.card V - (∑ v : V, m'.degree v) < d := by omega
      have hcol' : m'.Colorable := ih _ hlt m' hdeg' rfl
      exact hcol'.of_addEdge
    · refine hstep m hdeg ?_
      intro a b ha hb
      by_contra hab
      exact htwo ⟨a, b, hab, ha, hb⟩

/- ## Boolean-layer doubling and cut decomposition -/

/-- Double `m` into two Boolean layers (`false`, `true`), connecting `(false, s)` and `(true, s)`
by `5 - m.degree s` parallel edges. -/
def double {V : Type*} [Fintype V] [DecidableEq V] (m : Multi V) (s : V) : Multi (Bool × V) where
  count p q :=
    if p.1 = q.1 then m.count p.2 q.2
    else if p.2 = s ∧ q.2 = s then 5 - m.degree s else 0
  symm p q := by
    by_cases h : p.1 = q.1
    · rw [if_pos h, if_pos h.symm, m.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
      simp [and_comm]
  loopless p := by simp [m.loopless]

/-- Layer `b` slice of a vertex subset `C` of `Bool × V`. -/
def layerSlice {V : Type*} [Fintype V] [DecidableEq V] (C : Finset (Bool × V)) (b : Bool) :
    Finset V :=
  Finset.univ.filter fun x => (b, x) ∈ C

/-- Whether `C ⊆ Bool × V` separates the two copies `(false, s)` and `(true, s)`. -/
def SeparatesCopies {V : Type*} (C : Finset (Bool × V)) (s : V) : Prop :=
  ((false, s) ∈ C ∧ (true, s) ∉ C) ∨ ((true, s) ∈ C ∧ (false, s) ∉ C)

instance instDecidableSeparatesCopies {V : Type*} [DecidableEq V] (C : Finset (Bool × V)) (s : V) :
    Decidable (SeparatesCopies C s) := by
  unfold SeparatesCopies
  infer_instance

lemma mem_layerSlice {V : Type*} [Fintype V] [DecidableEq V]
    (C : Finset (Bool × V)) (b : Bool) (x : V) :
    x ∈ layerSlice C b ↔ (b, x) ∈ C := by
  simp [layerSlice]

lemma not_separatesCopies_iff {V : Type*} (C : Finset (Bool × V)) (s : V) :
    ¬ SeparatesCopies C s ↔ ((false, s) ∈ C ↔ (true, s) ∈ C) := by
  unfold SeparatesCopies
  tauto

lemma degree_double {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (s : V) (hdeg_s : m.degree s ≤ 5) (hdeg_other : ∀ v, v ≠ s → m.degree v = 5)
    (p : Bool × V) : (m.double s).degree p = 5 := by
  rcases p with ⟨b, v⟩
  unfold degree
  rw [Fintype.sum_prod_type]
  cases b
  · rw [Fintype.sum_bool]
    have hff : (∑ x : V, (m.double s).count (false, v) (false, x)) = m.degree v := by
      simp [double, degree]
    have hft : (∑ x : V, (m.double s).count (false, v) (true, x)) =
        if v = s then 5 - m.degree s else 0 := by
      by_cases hvs : v = s
      · subst hvs
        simp [double]
      · simp [double, hvs]
    rw [hff, hft]
    by_cases hvs : v = s
    · subst hvs; simp; omega
    · simp [hvs, hdeg_other v hvs]
  · rw [Fintype.sum_bool]
    have htt : (∑ x : V, (m.double s).count (true, v) (true, x)) = m.degree v := by
      simp [double, degree]
    have htf : (∑ x : V, (m.double s).count (true, v) (false, x)) =
        if v = s then 5 - m.degree s else 0 := by
      by_cases hvs : v = s
      · subst hvs
        simp [double]
      · simp [double, hvs]
    rw [htt, htf]
    by_cases hvs : v = s
    · subst hvs; simp; omega
    · simp [hvs, hdeg_other v hvs]

lemma colorable_of_double {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (s : V) (h : (m.double s).Colorable) : m.Colorable := by
  obtain ⟨vc, ec, hv⟩ := h
  refine ⟨fun x => vc (false, x), fun x y => ec (false, x) (false, y), ?_, ?_, ?_, ?_, ?_⟩
  · intro x y; exact hv.symmetric (false, x) (false, y)
  · intro x y; simpa [double] using hv.size (false, x) (false, y)
  · intro x y hpos; exact hv.vertices (false, x) (false, y) (by simpa [double] using hpos)
  · intro x y; exact hv.avoids (false, x) (false, y)
  · intro x y z hyz
    exact hv.disjoint (false, x) (false, y) (false, z) (fun heq => hyz (congrArg Prod.snd heq))

/-- Exact cut-count formula in `m.double s` for any subset `C : Finset (Bool × V)`. -/
lemma cutCount_double {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (s : V) (C : Finset (Bool × V)) :
    (m.double s).cutCount C =
      m.cutCount (layerSlice C false) + m.cutCount (layerSlice C true) +
      (if SeparatesCopies C s then 5 - m.degree s else 0) := by
  classical
  have hsum_cut :
      (m.double s).cutCount C =
        ∑ p : Bool × V, ∑ q : Bool × V,
          if p ∈ C ∧ q ∈ Cᶜ then (m.double s).count p q else 0 := by
    unfold cutCount cutSize
    have hfilt : Finset.univ.filter (fun p => p ∈ C) = C := by ext p; simp
    calc
      (∑ p ∈ C, ∑ q ∈ Cᶜ, (m.double s).count p q)
          = ∑ p ∈ C, ∑ q : Bool × V, if q ∈ Cᶜ then (m.double s).count p q else 0 := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [← Finset.sum_filter]
            congr 1; ext q; simp
      _ = ∑ p : Bool × V, if p ∈ C then
            (∑ q : Bool × V, if q ∈ Cᶜ then (m.double s).count p q else 0) else 0 := by
            rw [← Finset.sum_filter, hfilt]
      _ = ∑ p : Bool × V, ∑ q : Bool × V,
            if p ∈ C ∧ q ∈ Cᶜ then (m.double s).count p q else 0 := by
            refine Finset.sum_congr rfl fun p _ => ?_
            by_cases hp : p ∈ C <;> simp [hp]
  have hlayer : ∀ b : Bool,
      (∑ x : V, ∑ y : V, if (b, x) ∈ C ∧ (b, y) ∈ Cᶜ then m.count x y else 0) =
        m.cutCount (layerSlice C b) := by
    intro b
    unfold cutCount cutSize
    calc
      (∑ x : V, ∑ y : V, if (b, x) ∈ C ∧ (b, y) ∈ Cᶜ then m.count x y else 0)
          = ∑ x : V, if x ∈ layerSlice C b then
              (∑ y : V, if y ∈ (layerSlice C b)ᶜ then m.count x y else 0) else 0 := by
            refine Finset.sum_congr rfl fun x _ => ?_
            by_cases hx : (b, x) ∈ C
            · simp only [mem_layerSlice, hx, true_and, ↓reduceIte]
              refine Finset.sum_congr rfl fun y _ => ?_
              simp [mem_layerSlice]
            · simp [mem_layerSlice, hx]
      _ = ∑ x ∈ layerSlice C b, ∑ y ∈ (layerSlice C b)ᶜ, m.count x y := by
            rw [← Finset.sum_filter]
            have h1 : Finset.univ.filter (fun x => x ∈ layerSlice C b) = layerSlice C b := by
              ext x; simp
            rw [h1]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [← Finset.sum_filter]
            congr 1; ext y; simp
  have hcross_ft :
      (∑ x : V, ∑ y : V,
        if (false, x) ∈ C ∧ (true, y) ∈ Cᶜ then
          (if x = s ∧ y = s then 5 - m.degree s else 0) else 0) =
        if (false, s) ∈ C ∧ (true, s) ∉ C then 5 - m.degree s else 0 := by
    have hinner : ∀ x : V,
        (∑ y : V, if (false, x) ∈ C ∧ (true, y) ∈ Cᶜ then
          (if x = s ∧ y = s then 5 - m.degree s else 0) else 0) =
        if x = s ∧ (false, s) ∈ C ∧ (true, s) ∉ C then 5 - m.degree s else 0 := by
      intro x
      by_cases hxs : x = s
      · subst hxs
        have heq :
            (fun y : V => if (false, x) ∈ C ∧ (true, y) ∈ Cᶜ then
              (if x = x ∧ y = x then 5 - m.degree x else 0) else 0) =
            fun y : V => if y = x then
              (if (false, x) ∈ C ∧ (true, x) ∉ C then 5 - m.degree x else 0) else 0 := by
          funext y
          by_cases hyx : y = x
          · subst hyx; by_cases h : (false, y) ∈ C ∧ (true, y) ∉ C <;> simp [h]
          · simp [hyx]
        rw [heq]
        simp
      · simp [hxs]
    simp_rw [hinner]
    have heq :
        (fun x : V => if x = s ∧ (false, s) ∈ C ∧ (true, s) ∉ C then 5 - m.degree s else 0) =
        fun x : V => if x = s then
          (if (false, s) ∈ C ∧ (true, s) ∉ C then 5 - m.degree s else 0) else 0 := by
      funext x
      by_cases hxs : x = s <;> simp [hxs]
    rw [heq]
    simp
  have hcross_tf :
      (∑ x : V, ∑ y : V,
        if (true, x) ∈ C ∧ (false, y) ∈ Cᶜ then
          (if x = s ∧ y = s then 5 - m.degree s else 0) else 0) =
        if (true, s) ∈ C ∧ (false, s) ∉ C then 5 - m.degree s else 0 := by
    have hinner : ∀ x : V,
        (∑ y : V, if (true, x) ∈ C ∧ (false, y) ∈ Cᶜ then
          (if x = s ∧ y = s then 5 - m.degree s else 0) else 0) =
        if x = s ∧ (true, s) ∈ C ∧ (false, s) ∉ C then 5 - m.degree s else 0 := by
      intro x
      by_cases hxs : x = s
      · subst hxs
        have heq :
            (fun y : V => if (true, x) ∈ C ∧ (false, y) ∈ Cᶜ then
              (if x = x ∧ y = x then 5 - m.degree x else 0) else 0) =
            fun y : V => if y = x then
              (if (true, x) ∈ C ∧ (false, x) ∉ C then 5 - m.degree x else 0) else 0 := by
          funext y
          by_cases hyx : y = x
          · subst hyx; by_cases h : (true, y) ∈ C ∧ (false, y) ∉ C <;> simp [h]
          · simp [hyx]
        rw [heq]
        simp
      · simp [hxs]
    simp_rw [hinner]
    have heq :
        (fun x : V => if x = s ∧ (true, s) ∈ C ∧ (false, s) ∉ C then 5 - m.degree s else 0) =
        fun x : V => if x = s then
          (if (true, s) ∈ C ∧ (false, s) ∉ C then 5 - m.degree s else 0) else 0 := by
      funext x
      by_cases hxs : x = s <;> simp [hxs]
    rw [heq]
    simp
  rw [hsum_cut, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib]
  simp only [double, ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true]
  rw [hlayer false, hlayer true, hcross_ft, hcross_tf]
  -- Combine the two mutually exclusive separation terms
  by_cases h0 : (false, s) ∈ C <;> by_cases h1 : (true, s) ∈ C <;>
    simp [SeparatesCopies, h0, h1] <;> omega

lemma cutCount_double_of_not_separates {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (s : V) (C : Finset (Bool × V)) (hnot : ¬ SeparatesCopies C s) :
    (m.double s).cutCount C =
      m.cutCount (layerSlice C false) + m.cutCount (layerSlice C true) := by
  rw [cutCount_double, if_neg hnot, add_zero]

/- ## Tutte pieces and final contradictory cut arrangement -/

/-- Tutte three-piece witness without requiring oddness (strengthened sufficient hypothesis):
a separator `U` and three pairwise disjoint nonempty pieces disjoint from `U`,
each with cut count in `{1, 3}` and all exterior neighbors in `U`. -/
def HasTutteThreePieces {V : Type*} [Fintype V] [DecidableEq V] (m : Multi V) : Prop :=
  ∃ (U : Finset V) (C : Fin 3 → Finset V),
    (Pairwise fun i j => Disjoint (C i) (C j)) ∧
    (∀ i, Disjoint (C i) U) ∧
    (∀ i, (C i).Nonempty) ∧
    (∀ i, m.cutCount (C i) = 1 ∨ m.cutCount (C i) = 3) ∧
    (∀ i, ∀ x ∈ C i, ∀ y ∉ C i, 0 < m.count x y → y ∈ U)

/-- Tutte three-odd-piece witness matching black box `(D)` verbatim. -/
def HasTutteThreeOddPieces {V : Type*} [Fintype V] [DecidableEq V] (m : Multi V) : Prop :=
  ∃ (U : Finset V) (C : Fin 3 → Finset V),
    (Pairwise fun i j => Disjoint (C i) (C j)) ∧
    (∀ i, Disjoint (C i) U) ∧
    (∀ i, (C i).Nonempty) ∧
    (∀ i, Odd (C i).card) ∧
    (∀ i, m.cutCount (C i) = 1 ∨ m.cutCount (C i) = 3) ∧
    (∀ i, ∀ x ∈ C i, ∀ y ∉ C i, 0 < m.count x y → y ∈ U)

lemma HasTutteThreeOddPieces.toPieces {V : Type*} [Fintype V] [DecidableEq V] {m : Multi V}
    (h : m.HasTutteThreeOddPieces) : m.HasTutteThreePieces := by
  obtain ⟨U, C, hdisj, hU, hne, _, hcut, hext⟩ := h
  exact ⟨U, C, hdisj, hU, hne, hcut, hext⟩

/-- Adapter constructing `HasTutteThreePieces` from three explicit pieces `C₁, C₂, C₃`. -/
lemma hasTutteThreePieces_of_three {V : Type*} [Fintype V] [DecidableEq V] {m : Multi V}
    (U C₁ C₂ C₃ : Finset V)
    (h12 : Disjoint C₁ C₂) (h13 : Disjoint C₁ C₃) (h23 : Disjoint C₂ C₃)
    (hU1 : Disjoint C₁ U) (hU2 : Disjoint C₂ U) (hU3 : Disjoint C₃ U)
    (hne1 : C₁.Nonempty) (hne2 : C₂.Nonempty) (hne3 : C₃.Nonempty)
    (hcut1 : m.cutCount C₁ = 1 ∨ m.cutCount C₁ = 3)
    (hcut2 : m.cutCount C₂ = 1 ∨ m.cutCount C₂ = 3)
    (hcut3 : m.cutCount C₃ = 1 ∨ m.cutCount C₃ = 3)
    (hext1 : ∀ x ∈ C₁, ∀ y ∉ C₁, 0 < m.count x y → y ∈ U)
    (hext2 : ∀ x ∈ C₂, ∀ y ∉ C₂, 0 < m.count x y → y ∈ U)
    (hext3 : ∀ x ∈ C₃, ∀ y ∉ C₃, 0 < m.count x y → y ∈ U) :
    m.HasTutteThreePieces := by
  refine ⟨U, ![C₁, C₂, C₃], ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Disjoint.symm]
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption

/-- Adapter constructing `HasTutteThreePieces` from a `Finset` of at least three pieces. -/
lemma hasTutteThreePieces_of_finset {V : Type*} [Fintype V] [DecidableEq V] {m : Multi V}
    (U : Finset V) (P : Finset (Finset V)) (hcard : 3 ≤ P.card)
    (hdisj : (P : Set (Finset V)).PairwiseDisjoint id)
    (hU : ∀ C ∈ P, Disjoint C U)
    (hne : ∀ C ∈ P, C.Nonempty)
    (hcut : ∀ C ∈ P, m.cutCount C = 1 ∨ m.cutCount C = 3)
    (hext : ∀ C ∈ P, ∀ x ∈ C, ∀ y ∉ C, 0 < m.count x y → y ∈ U) :
    m.HasTutteThreePieces := by
  obtain ⟨Q, hQP, hQcard⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin 3 ≃ Q := (Q.equivFinOfCardEq hQcard).symm
  let C : Fin 3 → Finset V := fun i => (e i).val
  have hmem : ∀ i, C i ∈ P := fun i => hQP (e i).property
  refine ⟨U, C, ?_, fun i => hU _ (hmem i), fun i => hne _ (hmem i),
    fun i => hcut _ (hmem i), fun i => hext _ (hmem i)⟩
  intro i j hij
  have hneC : C i ≠ C j := fun heq => hij (e.injective (Subtype.ext heq))
  exact hdisj (hmem i) (hmem j) hneC

/-- General verification of Kostochka's claim: at most one Tutte piece separates `(false, s)`
and `(true, s)` in `m.double s`. Since `m.degree s < 5`, the two copies of `s` are adjacent;
if a piece separates them, the copy outside that piece must lie in `U`, hence cannot belong
to any piece, while the copy inside cannot belong to any other piece by disjointness. -/
lemma at_most_one_separates_copies {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (s : V) (hs_lt : m.degree s < 5)
    (U : Finset (Bool × V)) {ι : Type*} (C : ι → Finset (Bool × V))
    (hdisj : Pairwise fun i j => Disjoint (C i) (C j))
    (hU : ∀ i, Disjoint (C i) U)
    (hext : ∀ i, ∀ x ∈ C i, ∀ y ∉ C i, 0 < (m.double s).count x y → y ∈ U)
    {i j : ι} (hi : SeparatesCopies (C i) s) (hj : SeparatesCopies (C j) s) :
    i = j := by
  by_contra hij
  have hadj01 : 0 < (m.double s).count (false, s) (true, s) := by
    simp [double]; omega
  have hadj10 : 0 < (m.double s).count (true, s) (false, s) := by
    simp [double]; omega
  rcases hi with ⟨h0i, h1ni⟩ | ⟨h1i, h0ni⟩
  · have h1U : (true, s) ∈ U := hext i (false, s) h0i (true, s) h1ni hadj01
    have h1nj : (true, s) ∉ C j := Finset.disjoint_right.mp (hU j) h1U
    have h0nj : (false, s) ∉ C j := Finset.disjoint_left.mp (hdisj hij) h0i
    rcases hj with ⟨h0j, _⟩ | ⟨h1j, _⟩
    · exact h0nj h0j
    · exact h1nj h1j
  · have h0U : (false, s) ∈ U := hext i (true, s) h1i (false, s) h0ni hadj10
    have h0nj : (false, s) ∉ C j := Finset.disjoint_right.mp (hU j) h0U
    have h1nj : (true, s) ∉ C j := Finset.disjoint_left.mp (hdisj hij) h1i
    rcases hj with ⟨h0j, _⟩ | ⟨h1j, _⟩
    · exact h0nj h0j
    · exact h1nj h1j

/-- Helper: in a graph with at most one deficient vertex `s`, `3 ≤ m.degree s`, and no 1-edge
cut with both sides ≥ 2, no cut of size 1 exists at all. -/
lemma cutCount_ne_one_of_min_deg_ge_three {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (s : V) (hs_ge : 3 ≤ m.degree s) (hdeg_other : ∀ v, v ≠ s → m.degree v = 5)
    (hno1 : ∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card → m.cutCount S ≠ 1)
    (S : Finset V) : m.cutCount S ≠ 1 := by
  by_cases h0 : S.card = 0
  · rw [Finset.card_eq_zero.mp h0, cutCount_empty]; omega
  · by_cases h1 : S.card = 1
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h1
      rw [cutCount_singleton]
      by_cases hvs : v = s
      · subst hvs; omega
      · rw [hdeg_other v hvs]; omega
    · by_cases hc0 : Sᶜ.card = 0
      · have hSu : S = Finset.univ := by
          have he : Sᶜ = ∅ := Finset.card_eq_zero.mp hc0
          rw [← compl_compl S, he, Finset.compl_empty]
        rw [hSu, cutCount_univ]; omega
      · by_cases hc1 : Sᶜ.card = 1
        · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc1
          rw [← cutCount_compl, hv, cutCount_singleton]
          by_cases hvs : v = s
          · subst hvs; omega
          · rw [hdeg_other v hvs]; omega
        · exact hno1 S (by omega) (by omega)

/-- Helper: in a graph where every `v ≠ s` has degree 5 and no 3-edge cut has both sides ≥ 2,
any cut of size 3 must be `{s}` or `{s}ᶜ` (and forces `m.degree s = 3`). -/
lemma cutCount_eq_three_cases {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (s : V) (hdeg_other : ∀ v, v ≠ s → m.degree v = 5)
    (hno3 : ∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card → m.cutCount S ≠ 3)
    {S : Finset V} (h3 : m.cutCount S = 3) :
    (S = {s} ∨ S = ({s} : Finset V)ᶜ) ∧ m.degree s = 3 := by
  by_cases h0 : S.card = 0
  · rw [Finset.card_eq_zero.mp h0, cutCount_empty] at h3; omega
  · by_cases h1 : S.card = 1
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h1
      rw [cutCount_singleton] at h3
      have hvs : v = s := by
        by_contra hne
        have := hdeg_other v hne
        omega
      subst hvs
      exact ⟨Or.inl rfl, h3⟩
    · by_cases hc0 : Sᶜ.card = 0
      · have hSu : S = Finset.univ := by
          have he : Sᶜ = ∅ := Finset.card_eq_zero.mp hc0
          rw [← compl_compl S, he, Finset.compl_empty]
        rw [hSu, cutCount_univ] at h3; omega
      · by_cases hc1 : Sᶜ.card = 1
        · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc1
          rw [← cutCount_compl, hv, cutCount_singleton] at h3
          have hvs : v = s := by
            by_contra hne
            have := hdeg_other v hne
            omega
          subst hvs
          have hS : S = ({v} : Finset V)ᶜ := by rw [← hv, compl_compl]
          exact ⟨Or.inr hS, h3⟩
        · exact absurd h3 (hno3 S (by omega) (by omega))

/-- Final contradictory cut arrangement in `m.double s` when `3 ≤ m.degree s < 5`:
under connectedness and the absence of 1- and 3-edge cuts with both sides ≥ 2 in `m`,
the doubled 5-regular multigraph `m.double s` cannot admit three Tutte pieces. -/
theorem not_hasTutteThreePieces_double {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (s : V)
    (hdeg_other : ∀ v, v ≠ s → m.degree v = 5)
    (hs_ge : 3 ≤ m.degree s) (hs_lt : m.degree s < 5)
    (hconn : ∀ S : Finset V, m.cutCount S = 0 → S = ∅ ∨ S = Finset.univ)
    (hno1 : ∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card → m.cutCount S ≠ 1)
    (hno3 : ∀ S : Finset V, 2 ≤ S.card → 2 ≤ Sᶜ.card → m.cutCount S ≠ 3) :
    ¬ (m.double s).HasTutteThreePieces := by
  rintro ⟨U, C, hdisj, hU, hne, hcut, hext⟩
  have hno1_all : ∀ S : Finset V, m.cutCount S ≠ 1 :=
    cutCount_ne_one_of_min_deg_ge_three m s hs_ge hdeg_other hno1
  -- Pick three distinct indices `i, j, k : Fin 3` such that `C i` and `C j` do not separate `s` and `s'`.
  have hex_nonsep : ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ¬ SeparatesCopies (C i) s ∧ ¬ SeparatesCopies (C j) s := by
    by_cases h0 : SeparatesCopies (C 0) s
    · refine ⟨1, 2, 0, by decide, by decide, by decide, ?_, ?_⟩
      · intro h1
        have := at_most_one_separates_copies m s hs_lt U C hdisj hU hext h0 h1
        exact absurd this (by decide)
      · intro h2
        have := at_most_one_separates_copies m s hs_lt U C hdisj hU hext h0 h2
        exact absurd this (by decide)
    · by_cases h1 : SeparatesCopies (C 1) s
      · refine ⟨0, 2, 1, by decide, by decide, by decide, h0, ?_⟩
        intro h2
        have := at_most_one_separates_copies m s hs_lt U C hdisj hU hext h1 h2
        exact absurd this (by decide)
      · exact ⟨0, 1, 2, by decide, by decide, by decide, h0, h1⟩
  obtain ⟨i, j, k, hij, hik, hjk, hns_i, hns_j⟩ := hex_nonsep
  -- Define the four canonical candidate pieces in `Bool × V`.
  let P₀ : Finset (Bool × V) := Finset.univ.filter fun p => p.1 = false ∧ p.2 ≠ s
  let P₁ : Finset (Bool × V) := Finset.univ.filter fun p => p.1 = true ∧ p.2 ≠ s
  let Q₀ : Finset (Bool × V) := Finset.univ.filter fun p => p.1 = true ∨ p.2 = s
  let Q₁ : Finset (Bool × V) := Finset.univ.filter fun p => p.1 = false ∨ p.2 = s
  -- Classify any piece `C r` that does not separate `(false, s)` and `(true, s)`.
  have hclassify : ∀ r : Fin 3, ¬ SeparatesCopies (C r) s →
      (C r = P₀ ∨ C r = P₁ ∨ C r = Q₀ ∨ C r = Q₁) ∧ m.degree s = 3 := by
    intro r hns
    have hdecomp := cutCount_double_of_not_separates m s (C r) hns
    have hcr := hcut r
    rw [hdecomp] at hcr
    have ha1 := hno1_all (layerSlice (C r) false)
    have hb1 := hno1_all (layerSlice (C r) true)
    have hpair :
        (m.cutCount (layerSlice (C r) false) = 3 ∧ m.cutCount (layerSlice (C r) true) = 0) ∨
        (m.cutCount (layerSlice (C r) false) = 0 ∧ m.cutCount (layerSlice (C r) true) = 3) := by
      omega
    have hiff : s ∈ layerSlice (C r) false ↔ s ∈ layerSlice (C r) true := by
      simpa [mem_layerSlice] using (not_separatesCopies_iff (C r) s).mp hns
    rcases hpair with ⟨h3, h0⟩ | ⟨h0, h3⟩
    · obtain ⟨hS0, hds⟩ := cutCount_eq_three_cases m s hdeg_other hno3 h3
      have hS1 := hconn (layerSlice (C r) true) h0
      refine ⟨?_, hds⟩
      rcases hS0 with hS0 | hS0
      · -- `layerSlice false = {s}`, so `s ∈ layerSlice true`, forcing `layerSlice true = univ`, hence `C r = Q₀`.
        have hs1 : s ∈ layerSlice (C r) true := hiff.mp (by simp [hS0])
        have hS1u : layerSlice (C r) true = Finset.univ := by
          rcases hS1 with hS1 | hS1
          · simp [hS1] at hs1
          · exact hS1
        refine Or.inr (Or.inr (Or.inl ?_))
        ext ⟨b, x⟩
        cases b
        · simp [Q₀, ← mem_layerSlice, hS0]
        · simp [Q₀, ← mem_layerSlice, hS1u]
      · -- `layerSlice false = {s}ᶜ`, so `s ∉ layerSlice true`, forcing `layerSlice true = ∅`, hence `C r = P₀`.
        have hs1 : s ∉ layerSlice (C r) true := fun h => by
          have := hiff.mpr h
          simp [hS0] at this
        have hS1e : layerSlice (C r) true = ∅ := by
          rcases hS1 with hS1 | hS1
          · exact hS1
          · simp [hS1] at hs1
        refine Or.inl ?_
        ext ⟨b, x⟩
        cases b
        · simp [P₀, ← mem_layerSlice, hS0]
        · simp [P₀, ← mem_layerSlice, hS1e]
    · obtain ⟨hS1, hds⟩ := cutCount_eq_three_cases m s hdeg_other hno3 h3
      have hS0 := hconn (layerSlice (C r) false) h0
      refine ⟨?_, hds⟩
      rcases hS1 with hS1 | hS1
      · -- `layerSlice true = {s}`, forcing `layerSlice false = univ`, hence `C r = Q₁`.
        have hs0 : s ∈ layerSlice (C r) false := hiff.mpr (by simp [hS1])
        have hS0u : layerSlice (C r) false = Finset.univ := by
          rcases hS0 with hS0 | hS0
          · simp [hS0] at hs0
          · exact hS0
        refine Or.inr (Or.inr (Or.inr ?_))
        ext ⟨b, x⟩
        cases b
        · simp [Q₁, ← mem_layerSlice, hS0u]
        · simp [Q₁, ← mem_layerSlice, hS1]
      · -- `layerSlice true = {s}ᶜ`, forcing `layerSlice false = ∅`, hence `C r = P₁`.
        have hs0 : s ∉ layerSlice (C r) false := fun h => by
          have := hiff.mp h
          simp [hS1] at this
        have hS0e : layerSlice (C r) false = ∅ := by
          rcases hS0 with hS0 | hS0
          · exact hS0
          · simp [hS0] at hs0
        refine Or.inr (Or.inl ?_)
        ext ⟨b, x⟩
        cases b
        · simp [P₁, ← mem_layerSlice, hS0e]
        · simp [P₁, ← mem_layerSlice, hS1]
  obtain ⟨hCi, hds⟩ := hclassify i hns_i
  obtain ⟨hCj, _⟩ := hclassify j hns_j
  -- Since `m.degree s = 3 > 0` and `m` is loopless, `s` has a neighbor `v ≠ s` in `m`.
  have hex_v : ∃ v : V, v ≠ s ∧ 0 < m.count v s := by
    have hpos_sum : 0 < ∑ w : V, m.count s w := by rw [← degree]; omega
    obtain ⟨v, _, hvpos⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos_sum)
    have hvs : v ≠ s := by
      intro heq; subst heq; exact hvpos (m.loopless v)
    exact ⟨v, hvs, by rw [m.symm v s]; exact Nat.pos_of_ne_zero hvpos⟩
  obtain ⟨v, hvs, hv_adj⟩ := hex_v
  -- Extract a witness `d ∈ C k` (which must avoid `C i`, `C j`, and `U`).
  obtain ⟨d, hdk⟩ := hne k
  have hdi : d ∉ C i := Finset.disjoint_right.mp (hdisj hik) hdk
  have hdj : d ∉ C j := Finset.disjoint_right.mp (hdisj hjk) hdk
  have hdU : d ∉ U := Finset.disjoint_left.mp (hU k) hdk
  have hdisj_ij : Disjoint (C i) (C j) := hdisj hij
  -- Helper lemmas ruling out impossible pairs of pieces.
  have h_not_same : ∀ {A : Finset (Bool × V)}, C i = A → C j = A → False := by
    intro A hA1 hA2
    obtain ⟨x, hx⟩ := hne i
    have hxj : x ∈ C j := by rw [hA2, ← hA1]; exact hx
    exact Finset.disjoint_left.mp hdisj_ij hx hxj
  have h_not_P0_Q1 : ∀ {x y : Fin 3}, Disjoint (C x) (C y) → C x = P₀ → C y = Q₁ → False := by
    intro x y hd h1 h2
    have hm1 : (false, v) ∈ C x := by rw [h1]; simp [P₀, hvs]
    have hm2 : (false, v) ∈ C y := by rw [h2]; simp [Q₁]
    exact Finset.disjoint_left.mp hd hm1 hm2
  have h_not_P1_Q0 : ∀ {x y : Fin 3}, Disjoint (C x) (C y) → C x = P₁ → C y = Q₀ → False := by
    intro x y hd h1 h2
    have hm1 : (true, v) ∈ C x := by rw [h1]; simp [P₁, hvs]
    have hm2 : (true, v) ∈ C y := by rw [h2]; simp [Q₀]
    exact Finset.disjoint_left.mp hd hm1 hm2
  have h_not_Q0_Q1 : ∀ {x y : Fin 3}, Disjoint (C x) (C y) → C x = Q₀ → C y = Q₁ → False := by
    intro x y hd h1 h2
    have hm1 : (false, s) ∈ C x := by rw [h1]; simp [Q₀]
    have hm2 : (false, s) ∈ C y := by rw [h2]; simp [Q₁]
    exact Finset.disjoint_left.mp hd hm1 hm2
  have h_not_P0_Q0 : ∀ {A B : Finset (Bool × V)}, (d ∉ A) → (d ∉ B) → A = P₀ → B = Q₀ → False := by
    intro A B hn1 hn2 h1 h2
    subst h1; subst h2
    rcases d with ⟨b, x⟩
    cases b <;> by_cases hxs : x = s <;> simp [P₀, Q₀, hxs] at hn1 hn2
  have h_not_P1_Q1 : ∀ {A B : Finset (Bool × V)}, (d ∉ A) → (d ∉ B) → A = P₁ → B = Q₁ → False := by
    intro A B hn1 hn2 h1 h2
    subst h1; subst h2
    rcases d with ⟨b, x⟩
    cases b <;> by_cases hxs : x = s <;> simp [P₁, Q₁, hxs] at hn1 hn2
  have h_not_P0_P1 : ∀ {x y : Fin 3}, d ∉ C x → d ∉ C y → C x = P₀ → C y = P₁ → False := by
    intro x y hnx hny h1 h2
    -- `(false, v) ∈ P₀` is adjacent to `(false, s) ∉ P₀`, so `(false, s) ∈ U`.
    have hs0_U : (false, s) ∈ U := by
      refine hext x (false, v) (by rw [h1]; simp [P₀, hvs]) (false, s)
        (by rw [h1]; simp [P₀]) ?_
      simpa [double] using hv_adj
    -- `(true, v) ∈ P₁` is adjacent to `(true, s) ∉ P₁`, so `(true, s) ∈ U`.
    have hs1_U : (true, s) ∈ U := by
      refine hext y (true, v) (by rw [h2]; simp [P₁, hvs]) (true, s)
        (by rw [h2]; simp [P₁]) ?_
      simpa [double] using hv_adj
    -- Now `d` lies in `P₀ ∪ P₁ ∪ {(false, s), (true, s)} = univ`, contradiction!
    rcases d with ⟨b, z⟩
    cases b
    · by_cases hzs : z = s
      · subst hzs; exact hdU hs0_U
      · exact hnx (by rw [h1]; simp [P₀, hzs])
    · by_cases hzs : z = s
      · subst hzs; exact hdU hs1_U
      · exact hny (by rw [h2]; simp [P₁, hzs])
  -- Exhaust all 16 combinations of `(C i, C j) ∈ {P₀, P₁, Q₀, Q₁}²`.
  rcases hCi with hi0 | hi1 | hi2 | hi3 <;> rcases hCj with hj0 | hj1 | hj2 | hj3
  · exact h_not_same hi0 hj0
  · exact h_not_P0_P1 hdi hdj hi0 hj1
  · exact h_not_P0_Q0 hdi hdj hi0 hj2
  · exact h_not_P0_Q1 hdisj_ij hi0 hj3
  · exact h_not_P0_P1 hdj hdi hj0 hi1
  · exact h_not_same hi1 hj1
  · exact h_not_P1_Q0 hdisj_ij hi1 hj2
  · exact h_not_P1_Q1 hdi hdj hi1 hj3
  · exact h_not_P0_Q0 hdj hdi hj0 hi2
  · exact h_not_P1_Q0 hdisj_ij.symm hj1 hi2
  · exact h_not_same hi2 hj2
  · exact h_not_Q0_Q1 hdisj_ij hi2 hj3
  · exact h_not_P0_Q1 hdisj_ij.symm hj0 hi3
  · exact h_not_P1_Q1 hdj hdi hj1 hi3
  · exact h_not_Q0_Q1 hdisj_ij.symm hj2 hi3
  · exact h_not_same hi3 hj3

end Multi

/- ## Explicit role hypotheses and main recursive theorems -/

/-- Transparent alias for the shared induction hypothesis `Multi.SmallerColorable` from
`MultiSmallCut`: every finite multigraph of maximum degree at most 5 on strictly fewer than
`n` vertices (in universe `u`) is 7-total-colorable. -/
abbrev SmallerColorable.{u} (n : ℕ) : Prop :=
  Multi.SmallerColorable.{u} n

/-- A vertex-minimal counterexample: maximum degree ≤ 5, not 7-total-colorable, while every
strictly smaller-order multigraph of maximum degree ≤ 5 is 7-total-colorable. -/
def IsMinimalCounterexample.{u} {V : Type u} [Fintype V] (m : Multi V) : Prop :=
  (∀ v, m.degree v ≤ 5) ∧ ¬ m.Colorable ∧ SmallerColorable.{u} (Fintype.card V)

namespace IsMinimalCounterexample

lemma induce_colorable.{u} {V : Type u} [Fintype V] {m : Multi V}
    (hmin : IsMinimalCounterexample.{u} m) (s : Set V) [Fintype s]
    (hlt : Fintype.card s < Fintype.card V) : (m.induce s).Colorable := by
  classical
  exact hmin.2.2 (m.induce s) hlt (fun x => le_trans (m.degree_induce_le s x) (hmin.1 x.val))

lemma colorable_of_le_induce.{u} {V : Type u} [Fintype V] {m : Multi V}
    (hmin : IsMinimalCounterexample.{u} m) (s : Set V) [Fintype s]
    (hlt : Fintype.card s < Fintype.card V) {m₁ : Multi s} (hle : m₁.Le (m.induce s)) :
    m₁.Colorable :=
  (hmin.induce_colorable s hlt).of_le hle

lemma connected.{u} {V : Type u} [Fintype V] [DecidableEq V] {m : Multi V}
    (hmin : IsMinimalCounterexample.{u} m) (S : Finset V) (hcut0 : m.cutCount S = 0) :
    S = ∅ ∨ S = Finset.univ := by
  by_contra hnot
  simp only [not_or] at hnot
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hnot.1
  have hScne : Sᶜ.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro heq
    apply hnot.2
    rw [← compl_compl S, heq, Finset.compl_empty])
  have hcard_set : ∀ (T : Finset V), Fintype.card (T : Set V) = T.card := fun T => by
    simp [Fintype.card_subtype]
  have hS_lt : Fintype.card (S : Set V) < Fintype.card V := by
    rw [hcard_set]
    have hsum : S.card + Sᶜ.card = Fintype.card V := Finset.card_add_card_compl S
    have : 0 < Sᶜ.card := Finset.card_pos.mpr hScne
    omega
  have hSc_lt : Fintype.card ((Sᶜ : Finset V) : Set V) < Fintype.card V := by
    rw [hcard_set]
    have hsum : S.card + Sᶜ.card = Fintype.card V := Finset.card_add_card_compl S
    have : 0 < S.card := Finset.card_pos.mpr hSne
    omega
  exact hmin.2.1 (m.colorable_of_cutCount_eq_zero S hcut0
    (hmin.induce_colorable (S : Set V) hS_lt)
    (hmin.induce_colorable ((Sᶜ : Finset V) : Set V) hSc_lt))

lemma min_degree_ge_three.{u} {V : Type u} [Fintype V] [DecidableEq V] {m : Multi V}
    (hmin : IsMinimalCounterexample.{u} m) (v : V) : 3 ≤ m.degree v := by
  by_contra hlt3
  have hle2 : m.degree v ≤ 2 := by omega
  have hcard_sub : Fintype.card ((({v}ᶜ : Finset V) : Set V)) < Fintype.card V := by
    have hcard_set : Fintype.card ((({v}ᶜ : Finset V) : Set V)) = ({v}ᶜ : Finset V).card := by
      rw [Fintype.card_subtype]
      congr 1; ext x; simp
    rw [hcard_set, Finset.card_compl, Finset.card_singleton]
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    omega
  exact hmin.2.1 (m.colorable_of_degree_le_two hmin.1 v hle2
    (hmin.induce_colorable ((({v}ᶜ : Finset V) : Set V)) hcard_sub))

/-- Any vertex-minimal counterexample extends (by adding edges between deficient vertices)
to a vertex-minimal counterexample on the same vertex set with at most one deficient vertex. -/
lemma exists_at_most_one_deficient.{u} {V : Type u} [Fintype V] [DecidableEq V] {m : Multi V}
    (hmin : IsMinimalCounterexample.{u} m) :
    ∃ m' : Multi V, m.Le m' ∧ IsMinimalCounterexample.{u} m' ∧
      (∀ a b, m'.degree a < 5 → m'.degree b < 5 → a = b) := by
  suffices hmain : ∀ d : ℕ, ∀ m₁ : Multi V, m.Le m₁ → IsMinimalCounterexample.{u} m₁ →
      5 * Fintype.card V - (∑ v : V, m₁.degree v) = d →
      ∃ m' : Multi V, m.Le m' ∧ IsMinimalCounterexample.{u} m' ∧
        (∀ a b, m'.degree a < 5 → m'.degree b < 5 → a = b) by
    exact hmain _ m (fun _ _ => le_rfl) hmin rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro m₁ hle hmin₁ hd
    by_cases htwo : ∃ a b : V, a ≠ b ∧ m₁.degree a < 5 ∧ m₁.degree b < 5
    · obtain ⟨a, b, hab, ha, hb⟩ := htwo
      let m₂ := m₁.addEdge a b hab
      have hle₂ : m.Le m₂ := fun x y => le_trans (hle x y) (m₁.le_addEdge a b hab x y)
      have hdeg₂ : ∀ v, m₂.degree v ≤ 5 := by
        intro v
        by_cases hva : v = a
        · subst hva; rw [Multi.degree_addEdge_left]; omega
        · by_cases hvb : v = b
          · subst hvb; rw [Multi.degree_addEdge_right]; omega
          · rw [Multi.degree_addEdge_of_ne m₁ a b v hab hva hvb]; exact hmin₁.1 v
      have hnc₂ : ¬ m₂.Colorable := fun hcol => hmin₁.2.1 hcol.of_addEdge
      have hmin₂ : IsMinimalCounterexample.{u} m₂ := ⟨hdeg₂, hnc₂, hmin₁.2.2⟩
      have hsum_le : (∑ v : V, m₂.degree v) ≤ 5 * Fintype.card V := by
        calc
          (∑ v : V, m₂.degree v) ≤ ∑ _v : V, 5 := Finset.sum_le_sum fun v _ => hdeg₂ v
          _ = 5 * Fintype.card V := by simp [mul_comm]
      have hsum_eq : (∑ v : V, m₂.degree v) = (∑ v : V, m₁.degree v) + 2 :=
        Multi.sum_degree_addEdge m₁ a b hab
      have hlt : 5 * Fintype.card V - (∑ v : V, m₂.degree v) < d := by omega
      exact ih _ hlt m₂ hle₂ hmin₂ rfl
    · refine ⟨m₁, hle, hmin₁, fun a b ha hb => ?_⟩
      by_contra hab
      exact htwo ⟨a, b, hab, ha, hb⟩

end IsMinimalCounterexample

/-- Role (A) (Theorem 2): every 5-regular multigraph whose support has a perfect matching
is 7-total-colorable. -/
def RegularMatchingColorable.{u} : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (m : Multi V),
    (∀ v, m.degree v = 5) → m.HasPerfectMatching → m.Colorable

/-- Role (B1) (Lemma 6, 1-edge cut): a 1-edge cut with both sides of order ≥ 2 implies
colorability under the smaller-order induction hypothesis. -/
def CutOneColorable.{u} : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (m : Multi V),
    SmallerColorable.{u} (Fintype.card V) →
    (∀ v, m.degree v ≤ 5) →
    ∀ s : Finset V, 2 ≤ s.card → 2 ≤ sᶜ.card → m.cutCount s = 1 → m.Colorable

/-- Role (B3) (Lemma 6, 3-edge hub cut): a 3-edge cut all incident to a single hub vertex,
with both sides of order ≥ 2, implies colorability under the smaller-order induction hypothesis. -/
def CutThreeHubColorable.{u} : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (m : Multi V),
    SmallerColorable.{u} (Fintype.card V) →
    (∀ v, m.degree v ≤ 5) →
    ∀ s : Finset V, 2 ≤ s.card → 2 ≤ sᶜ.card → m.cutCount s = 3 → m.HasCutHub s → m.Colorable

/-- Role (C-nonhub) (Lemma 8, non-hub 3-edge cut): a 3-edge cut with no hub and both sides ≥ 2
implies colorability under the smaller-order induction hypothesis. -/
def CutThreeNonHubColorable.{u} : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (m : Multi V),
    SmallerColorable.{u} (Fintype.card V) →
    (∀ v, m.degree v ≤ 5) →
    ∀ s : Finset V, 2 ≤ s.card → 2 ≤ sᶜ.card → m.cutCount s = 3 → ¬ m.HasCutHub s → m.Colorable

/-- Role (C) (full 3-edge cut, subsuming B3): any 3-edge cut with both sides of order ≥ 2
implies colorability under the smaller-order induction hypothesis. -/
def CutThreeColorable.{u} : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (m : Multi V),
    SmallerColorable.{u} (Fintype.card V) →
    (∀ v, m.degree v ≤ 5) →
    ∀ s : Finset V, 2 ≤ s.card → 2 ≤ sᶜ.card → m.cutCount s = 3 → m.Colorable

/-- Role (D') (strengthened Tutte black box, omitting the unused odd-cardinality condition). -/
def TutteThreePieces.{u} : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (m : Multi V),
    (∀ v, m.degree v = 5) → ¬ m.HasPerfectMatching → m.HasTutteThreePieces

/-- Role (D) (verbatim Tutte black box with odd nonempty pieces). -/
def TutteOddPieces.{u} : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (m : Multi V),
    (∀ v, m.degree v = 5) → ¬ m.HasPerfectMatching → m.HasTutteThreeOddPieces

lemma cutThreeColorable_of_hub_and_nonHub.{u}
    (hB3 : CutThreeHubColorable.{u}) (hC_nonhub : CutThreeNonHubColorable.{u}) :
    CutThreeColorable.{u} := by
  intro V _ _ m ih hdeg s hs1 hs2 hcut
  by_cases hhub : m.HasCutHub s
  · exact hB3 m ih hdeg s hs1 hs2 hcut hhub
  · exact hC_nonhub m ih hdeg s hs1 hs2 hcut hhub

lemma tutteThreePieces_of_odd.{u} (hD : TutteOddPieces.{u}) : TutteThreePieces.{u} :=
  fun m hreg hnpm => (hD m hreg hnpm).toPieces

/-- Core recursive theorem parameterized by an arbitrary matching predicate `PM` bridging
black boxes `(A)` and `(D)`. -/
theorem colorable_of_blackboxes_with_pm.{u}
    (PM : ∀ {W : Type u} [Fintype W] [DecidableEq W], Multi W → Prop)
    (hA : ∀ {W : Type u} [Fintype W] [DecidableEq W] (m : Multi W),
      (∀ v, m.degree v = 5) → PM m → m.Colorable)
    (hB1 : CutOneColorable.{u})
    (hC : CutThreeColorable.{u})
    (hD : ∀ {W : Type u} [Fintype W] [DecidableEq W] (m : Multi W),
      (∀ v, m.degree v = 5) → ¬ PM m → m.HasTutteThreePieces)
    {V : Type u} [Fintype V] (m : Multi V) (hdeg : ∀ v, m.degree v ≤ 5) :
    m.Colorable := by
  suffices hmain : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] (m : Multi W),
      Fintype.card W = n → (∀ v, m.degree v ≤ 5) → m.Colorable by
    exact hmain (Fintype.card V) m rfl hdeg
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih_n =>
    intro W _ m hcard hdeg
    classical
    have ih : SmallerColorable.{u} (Fintype.card W) := by
      intro U _ _ mU hlt hdegU
      exact ih_n (Fintype.card U) (hcard ▸ hlt) mU rfl hdegU
    -- Empty vertex set is trivially colorable.
    by_cases hEmpty : IsEmpty W
    · refine ⟨isEmptyElim, fun x => isEmptyElim x, ?_, ?_, ?_, ?_, ?_⟩ <;>
        intro x <;> exact isEmptyElim x
    have hNonempty : Nonempty W := not_isEmpty_iff.mp hEmpty
    -- Reduce by nested deficit induction to a graph with at most one deficient vertex.
    refine Multi.colorable_of_at_most_one_deficient ?_ m hdeg
    intro G hGdeg hGdef
    -- Identify the unique possible deficient vertex `s`.
    have hex_s : ∃ s : W, ∀ v, v ≠ s → G.degree v = 5 := by
      by_cases hlt5 : ∃ s : W, G.degree s < 5
      · obtain ⟨s, hs⟩ := hlt5
        refine ⟨s, fun v hvs => ?_⟩
        have hnotlt : ¬ G.degree v < 5 := fun hv => hvs (hGdef v s hv hs)
        have hle := hGdeg v
        omega
      · simp only [not_exists, not_lt] at hlt5
        obtain ⟨s⟩ := hNonempty
        exact ⟨s, fun v _ => le_antisymm (hGdeg v) (hlt5 v)⟩
    obtain ⟨s, hdeg_other⟩ := hex_s
    -- Proceed by contradiction: assume `G` is a minimal counterexample.
    by_contra hnc
    have hmin : IsMinimalCounterexample.{u} G := ⟨hGdeg, hnc, ih⟩
    have hconn : ∀ S : Finset W, G.cutCount S = 0 → S = ∅ ∨ S = Finset.univ :=
      hmin.connected
    have hs_ge : 3 ≤ G.degree s := hmin.min_degree_ge_three s
    -- 3. `G` has no 1-edge or 3-edge cut with both sides of order ≥ 2.
    have hno1 : ∀ S : Finset W, 2 ≤ S.card → 2 ≤ Sᶜ.card → G.cutCount S ≠ 1 :=
      fun S h1 h2 hcut1 => hnc (hB1 G ih hGdeg S h1 h2 hcut1)
    have hno3 : ∀ S : Finset W, 2 ≤ S.card → 2 ≤ Sᶜ.card → G.cutCount S ≠ 3 :=
      fun S h1 h2 hcut3 => hnc (hC G ih hGdeg S h1 h2 hcut3)
    -- 4. Split on whether `G` is already 5-regular (`G.degree s = 5`) or needs doubling.
    by_cases hreg_s : G.degree s = 5
    · have hreg : ∀ v, G.degree v = 5 := by
        intro v
        by_cases hvs : v = s
        · subst hvs; exact hreg_s
        · exact hdeg_other v hvs
      have hnpm : ¬ PM G := fun hpm => hnc (hA G hreg hpm)
      obtain ⟨_, C, _, _, _, hcutC, _⟩ := hD G hreg hnpm
      rcases hcutC 0 with h1 | h3
      · exact Multi.cutCount_ne_one_of_min_deg_ge_three G s hs_ge hdeg_other hno1 (C 0) h1
      · have hds := (Multi.cutCount_eq_three_cases G s hdeg_other hno3 h3).2
        omega
    · have hs_lt : G.degree s < 5 := by have := hGdeg s; omega
      have hH_reg : ∀ p : Bool × W, (G.double s).degree p = 5 :=
        G.degree_double s (hGdeg s) hdeg_other
      have hH_nc : ¬ (G.double s).Colorable := fun hcol => hnc (G.colorable_of_double s hcol)
      have hH_npm : ¬ PM (G.double s) := fun hpm => hH_nc (hA (G.double s) hH_reg hpm)
      have hH_tutte : (G.double s).HasTutteThreePieces := hD (G.double s) hH_reg hH_npm
      exact Multi.not_hasTutteThreePieces_double G s hdeg_other hs_ge hs_lt hconn hno1 hno3 hH_tutte

/-- Main recursive theorem using the concrete `HasPerfectMatching` predicate and the
strengthened Tutte black box (`TutteThreePieces`, omitting oddness). -/
theorem colorable_of_blackboxes.{u}
    (hA : RegularMatchingColorable.{u})
    (hB1 : CutOneColorable.{u})
    (hC : CutThreeColorable.{u})
    (hD : TutteThreePieces.{u})
    {V : Type u} [Fintype V] (m : Multi V) (hdeg : ∀ v, m.degree v ≤ 5) :
    m.Colorable :=
  colorable_of_blackboxes_with_pm (fun m => m.HasPerfectMatching) hA hB1 hC hD m hdeg

/-- Main recursive theorem using the verbatim Tutte black box `(D)` (`TutteOddPieces`). -/
theorem colorable_of_blackboxes_odd.{u}
    (hA : RegularMatchingColorable.{u})
    (hB1 : CutOneColorable.{u})
    (hC : CutThreeColorable.{u})
    (hD : TutteOddPieces.{u})
    {V : Type u} [Fintype V] (m : Multi V) (hdeg : ∀ v, m.degree v ≤ 5) :
    m.Colorable :=
  colorable_of_blackboxes hA hB1 hC (tutteThreePieces_of_odd hD) m hdeg

/-- Main recursive theorem with `(B)` and `(C)` explicitly split into 1-edge cuts,
3-edge hub cuts (Lemma 6), and 3-edge non-hub cuts (Lemma 8). -/
theorem colorable_of_blackboxes_split.{u}
    (hA : RegularMatchingColorable.{u})
    (hB1 : CutOneColorable.{u})
    (hB3 : CutThreeHubColorable.{u})
    (hC_nonhub : CutThreeNonHubColorable.{u})
    (hD : TutteOddPieces.{u})
    {V : Type u} [Fintype V] (m : Multi V) (hdeg : ∀ v, m.degree v ≤ 5) :
    m.Colorable :=
  colorable_of_blackboxes_odd hA hB1 (cutThreeColorable_of_hub_and_nonHub hB3 hC_nonhub) hD m hdeg

/-- Universe-polymorphic wrapper: if the black boxes `(A)`–`(D)` are supplied only at `Type 0`,
every finite multigraph of maximum degree ≤ 5 in ANY universe `u` is 7-total-colorable. -/
theorem colorable_of_blackboxes_type0.{u}
    (hA : RegularMatchingColorable.{0})
    (hB1 : CutOneColorable.{0})
    (hC : CutThreeColorable.{0})
    (hD : TutteOddPieces.{0})
    {V : Type u} [Fintype V] (m : Multi V) (hdeg : ∀ v, m.degree v ≤ 5) :
    m.Colorable := by
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  have hdeg' : ∀ i : Fin (Fintype.card V), (m.comap e).degree i ≤ 5 := by
    intro i
    rw [Multi.degree_comap]
    exact hdeg (e i)
  have hcol' : (m.comap e).Colorable :=
    colorable_of_blackboxes_odd.{0} hA hB1 hC hD (m.comap e) hdeg'
  exact (Multi.colorable_comap_iff m e).mp hcol'

/-- Universe-polymorphic wrapper for the split `(B1), (B3), (C-nonhub)` black boxes at `Type 0`. -/
theorem colorable_of_blackboxes_split_type0.{u}
    (hA : RegularMatchingColorable.{0})
    (hB1 : CutOneColorable.{0})
    (hB3 : CutThreeHubColorable.{0})
    (hC_nonhub : CutThreeNonHubColorable.{0})
    (hD : TutteOddPieces.{0})
    {V : Type u} [Fintype V] (m : Multi V) (hdeg : ∀ v, m.degree v ≤ 5) :
    m.Colorable :=
  colorable_of_blackboxes_type0 hA hB1 (cutThreeColorable_of_hub_and_nonHub hB3 hC_nonhub) hD m hdeg

/- ## Concrete assembly with the compiled `MultiSmallCut` and `MultiTutte` modules -/

/-- Role `(B1)` discharged directly from `MultiSmallCut.colorable_of_small_cut`. -/
theorem cutOneColorable_of_small_cut.{u} : CutOneColorable.{u} :=
  fun m ih hdeg s hs1 hs2 hcut1 =>
    Multi.colorable_of_small_cut m s (Or.inl hcut1) hs1 hs2 hdeg ih

/-- Role `(C)` discharged directly from `MultiSmallCut.colorable_of_small_cut`. -/
theorem cutThreeColorable_of_small_cut.{u} : CutThreeColorable.{u} :=
  fun m ih hdeg s hs1 hs2 hcut3 =>
    Multi.colorable_of_small_cut m s (Or.inr hcut3) hs1 hs2 hdeg ih

/-- Role `(D)` discharged directly from `MultiTutte.threeSmallOddCuts`. -/
theorem tutteOddPieces_of_threeSmallOddCuts.{u} : TutteOddPieces.{u} := by
  intro V _ _ m hreg hnpm
  obtain ⟨u, pieces, hcard, hdisj, hprops⟩ := Multi.threeSmallOddCuts m hreg hnpm
  obtain ⟨Q, hQP, hQcard⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin 3 ≃ Q := (Q.equivFinOfCardEq hQcard).symm
  let C : Fin 3 → Finset V := fun i => (e i).val
  have hmem : ∀ i, C i ∈ pieces := fun i => hQP (e i).property
  refine ⟨u, C, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hneC : C i ≠ C j := fun heq => hij (e.injective (Subtype.ext heq))
    exact hdisj (hmem i) (hmem j) hneC
  · intro i
    exact (hprops (C i) (hmem i)).2.1
  · intro i
    have hodd : Odd (C i).card := (hprops (C i) (hmem i)).1
    obtain ⟨k, hk⟩ := hodd
    exact Finset.card_pos.mp (by omega)
  · intro i
    exact (hprops (C i) (hmem i)).1
  · intro i
    exact (hprops (C i) (hmem i)).2.2.1
  · intro i x hx y hy hpos
    have hsub := (hprops (C i) (hmem i)).2.2.2 x hx
    have hnbr : y ∈ m.support.neighborFinset x := (m.support.mem_neighborFinset x y).mpr hpos
    exact hsub (Finset.mem_sdiff.mpr ⟨hnbr, hy⟩)

/-- Kostochka 1996, Theorem 3 reduced directly to Theorem 2 (black box `(A)` alone),
discharging `(B)`, `(C)`, and `(D)` via the compiled `MultiSmallCut` and `MultiTutte` modules. -/
theorem colorable_of_regular_matching.{u}
    (hA : RegularMatchingColorable.{u})
    {V : Type u} [Fintype V] (m : Multi V) (hdeg : ∀ v, m.degree v ≤ 5) :
    m.Colorable :=
  colorable_of_blackboxes_odd hA cutOneColorable_of_small_cut cutThreeColorable_of_small_cut
    tutteOddPieces_of_threeSmallOddCuts m hdeg

/-- Universe-polymorphic reduction to Theorem 2 (`RegularMatchingColorable.{0}` at `Type 0` alone). -/
theorem colorable_of_regular_matching_type0.{u}
    (hA : RegularMatchingColorable.{0})
    {V : Type u} [Fintype V] (m : Multi V) (hdeg : ∀ v, m.degree v ≤ 5) :
    m.Colorable :=
  colorable_of_blackboxes_type0 hA cutOneColorable_of_small_cut cutThreeColorable_of_small_cut
    tutteOddPieces_of_threeSmallOddCuts m hdeg

end MultFive

end


section -- FiveRegularSubdivision

/- An odd subdivision turns the auxiliary multigraph in Kostochka's Lemma 5
into a simple graph. Distinct edge labels get distinct pairs of new vertices,
including at a loop. An equitable edge split pulls back through the three-edge
paths. Loops contribute twice to the degree at their vertex. -/

namespace Kostochka.FiveRegular.Subdivision

open SimpleGraph Finset

variable {V E : Type*}

/-- `left` and `right` are the endpoints of a labeled edge. Repeated endpoint
pairs and equal endpoints are allowed. -/
structure Family (V E : Type*) where
  left : E → V
  right : E → V

abbrev Node (V E : Type*) := V ⊕ (E ⊕ E)

private def base (v : V) : Node V E := .inl v
private def lmid (e : E) : Node V E := .inr (.inl e)
private def rmid (e : E) : Node V E := .inr (.inr e)

private def connectedPair (D : Family V E) : Node V E → Node V E → Prop
  | .inl v, .inr (.inl e) | .inr (.inl e), .inl v => v = D.left e
  | .inl v, .inr (.inr e) | .inr (.inr e), .inl v => v = D.right e
  | .inr (.inl e), .inr (.inr f) | .inr (.inr f), .inr (.inl e) => e = f
  | _, _ => False

def graph (D : Family V E) : SimpleGraph (Node V E) where
  Adj := connectedPair D
  symm.symm := by
    rintro (u|u|u) (v|v|v) <;> exact id
  loopless.irrefl := by
    rintro (v|e|e) <;> exact id

private def leftEdge (D : Family V E) (e : E) : (graph D).edgeSet :=
  ⟨s(base (D.left e), lmid e), by exact Eq.refl _⟩
private def midEdge (D : Family V E) (e : E) : (graph D).edgeSet :=
  ⟨s(lmid e, rmid e), by exact Eq.refl _⟩
private def rightEdge (D : Family V E) (e : E) : (graph D).edgeSet :=
  ⟨s(base (D.right e), rmid e), by exact Eq.refl _⟩

/-- Enumerate all three types of edges. This is a bijection even for a
one-vertex loop or arbitrarily many parallel edges. -/
noncomputable def edgeEquiv (D : Family V E) : (E ⊕ (E ⊕ E)) ≃ (graph D).edgeSet := by
  classical
  let f : E ⊕ (E ⊕ E) → (graph D).edgeSet := Sum.elim (leftEdge D) (Sum.elim (midEdge D) (rightEdge D))
  apply Equiv.ofBijective f
  constructor
  · rintro (e|e|e) (e'|e'|e') h <;>
      have h' := congrArg Subtype.val h <;>
      simp_all [f, leftEdge, midEdge, rightEdge, base, lmid, rmid, Sym2.eq]
  · rintro ⟨⟨u,v⟩, hadj⟩
    have hh : (graph D).Adj u v := hadj
    rcases u with v₁ | e₁ | e₁ <;> rcases v with v₂ | e₂ | e₂ <;>
      simp only [graph, connectedPair] at hh <;> try contradiction
    · refine ⟨.inl e₂, Subtype.ext ?_⟩
      change s(base (D.left e₂),lmid e₂) = s(base v₁,lmid e₂)
      rw [hh]
    · refine ⟨.inr (.inr e₂), Subtype.ext ?_⟩
      change s(base (D.right e₂),rmid e₂) = s(base v₁,rmid e₂)
      rw [hh]
    · refine ⟨.inl e₁, Subtype.ext ?_⟩
      change s(base (D.left e₁),lmid e₁) = s(lmid e₁,base v₂)
      rw [hh, Sym2.eq_swap]
    · refine ⟨.inr (.inl e₁), Subtype.ext ?_⟩
      change s(lmid e₁,rmid e₁) = s(lmid e₁,rmid e₂)
      rw [hh]
    · refine ⟨.inr (.inr e₁), Subtype.ext ?_⟩
      change s(base (D.right e₁), rmid e₁) = s(rmid e₁, base v₂)
      rw [hh, Sym2.eq_swap]
    · refine ⟨.inr (.inl e₁), Subtype.ext ?_⟩
      change s(lmid e₁,rmid e₁) = s(rmid e₁,lmid e₂)
      rw [hh, Sym2.eq_swap]


@[simp] private theorem enum_left (D : Family V E) (e : E) :
    edgeEquiv D (.inl e) = leftEdge D e := rfl
@[simp] private theorem enum_mid (D : Family V E) (e : E) :
    edgeEquiv D (.inr (.inl e)) = midEdge D e := rfl
@[simp] private theorem enum_right (D : Family V E) (e : E) :
    edgeEquiv D (.inr (.inr e)) = rightEdge D e := rfl

instance (D : Family V E) [DecidableEq V] [DecidableEq E] : DecidableRel (graph D).Adj := by
  rintro (u|u|u) (v|v|v) <;> unfold graph <;> dsimp [connectedPair] <;> infer_instance

variable [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Incidences of color b at a vertex of a labeled multigraph. A loop
has two incidences with its unique endpoint. -/
def coloredDegree (D : Family V E) (f : E → Bool) (v : V) (b : Bool) : ℕ :=
  (∑ e, if v = D.left e ∧ f e = b then 1 else 0) +
  (∑ e, if v = D.right e ∧ f e = b then 1 else 0)

variable [Fintype V]

def simpleDegree {W : Type*} [DecidableEq W] (G : SimpleGraph W) [Fintype G.edgeSet]
    (f : G.edgeSet → Bool) (v : W) (b : Bool) : ℕ :=
  ∑ e, if v ∈ e.val ∧ f e = b then 1 else 0

private theorem count_base (D : Family V E) (f : (graph D).edgeSet → Bool) (v : V) (b : Bool) :
    simpleDegree (graph D) f (base v) b =
      (∑ e, if v = D.left e ∧ f (leftEdge D e) = b then 1 else 0) +
      (∑ e, if v = D.right e ∧ f (rightEdge D e) = b then 1 else 0) := by
  unfold simpleDegree
  rw [← (edgeEquiv D).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [leftEdge, midEdge, rightEdge, Sym2.mem_iff, base, lmid, rmid, Finset.sum_boole]
  congr 1 <;> symm <;> apply Finset.sum_boole

private theorem count_lmid (D : Family V E) (f : (graph D).edgeSet → Bool) (e : E) (b : Bool) :
    simpleDegree (graph D) f (lmid e) b =
      (if f (leftEdge D e) = b then 1 else 0) + (if f (midEdge D e) = b then 1 else 0) := by
  unfold simpleDegree
  rw [← (edgeEquiv D).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [leftEdge, midEdge, rightEdge, Sym2.mem_iff, base, lmid, rmid, ite_and]
  congr 2

private theorem count_rmid (D : Family V E) (f : (graph D).edgeSet → Bool) (e : E) (b : Bool) :
    simpleDegree (graph D) f (rmid e) b =
      (if f (midEdge D e) = b then 1 else 0) + (if f (rightEdge D e) = b then 1 else 0) := by
  unfold simpleDegree
  rw [← (edgeEquiv D).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [leftEdge, midEdge, rightEdge, Sym2.mem_iff, base, lmid, rmid, ite_and]
  congr 2

theorem pullback_balanced (D : Family V E) (f : (graph D).edgeSet → Bool)
    (h : ∀ v, simpleDegree (graph D) f v true = simpleDegree (graph D) f v false) :
    ∃ g : E → Bool, ∀ v, coloredDegree D g v true = coloredDegree D g v false := by
  have agree (e : E) : f (leftEdge D e) = f (rightEdge D e) := by
    have h₁ := h (lmid e)
    have h₂ := h (rmid e)
    simp only [count_lmid, count_rmid] at h₁ h₂
    cases hl : f (leftEdge D e) <;> cases hm : f (midEdge D e) <;>
      cases hr : f (rightEdge D e) <;> simp [hl, hm, hr] at *
  refine ⟨fun e => f (leftEdge D e), fun v => ?_⟩
  simpa only [count_base, ← agree, coloredDegree] using h (base v)


/-- An edge label connects its endpoints irrespective of the chosen ordering. -/
def Joined (D : Family V E) (v w : V) : Prop :=
  ∃ e, (v = D.left e ∧ w = D.right e) ∨ (w = D.left e ∧ v = D.right e)

omit [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V] in
private theorem endpoint_reachable (D : Family V E) (e : E) :
    (graph D).Reachable (base (D.left e)) (base (D.right e)) := by
  have h₁ : (graph D).Adj (base (D.left e)) (lmid e) := rfl
  have h₂ : (graph D).Adj (lmid e) (rmid e) := rfl
  have h₃ : (graph D).Adj (rmid e) (base (D.right e)) := rfl
  exact h₁.reachable.trans (h₂.reachable.trans h₃.reachable)

omit [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V] in
theorem preconnected (D : Family V E)
    (h : ∀ v w, Relation.ReflTransGen (Joined D) v w) : (graph D).Preconnected := by
  have hbase (v w : V) : (graph D).Reachable (base v) (base w) := by
    induction h v w with
    | refl => exact .refl _
    | tail _ hw ih =>
      rcases hw with ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ih.trans (endpoint_reachable D e)
      · exact ih.trans (endpoint_reachable D e).symm
  have attach (x : Node V E) : ∃ v, (graph D).Reachable x (base v) := by
    rcases x with v|e|e
    · exact ⟨v, .refl _⟩
    · exact ⟨D.left e, (show (graph D).Adj (lmid e) (base (D.left e)) from rfl).reachable⟩
    · exact ⟨D.right e, (show (graph D).Adj (rmid e) (base (D.right e)) from rfl).reachable⟩
  intro x y
  obtain ⟨v, hv⟩ := attach x
  obtain ⟨w, hw⟩ := attach y
  exact hv.trans ((hbase v w).trans hw.symm)

/-- Subdivision multiplies the edge count by three, preserving its parity. -/
theorem card_edges (D : Family V E) :
    Fintype.card (graph D).edgeSet = 3 * Fintype.card E := by
  rw [← Fintype.card_congr (edgeEquiv D)]
  simp [Fintype.card_sum]
  omega

private theorem simpleDegree_eq_subgraph_degree {W : Type*} [Fintype W] [DecidableEq W]
    (G H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (hle : H ≤ G)
    (color : G.edgeSet → Bool) (b : Bool) (spec : ∀ e, color e = b ↔ e.val ∈ H.edgeSet)
    (v : W) : simpleDegree G color v b = H.degree v := by
  classical
  unfold simpleDegree
  rw [← H.card_incidenceSet_eq_degree, Finset.sum_boole, Nat.cast_id, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact {
    toFun := fun e =>
      let hit := (Finset.mem_filter.mp e.property).2
      ⟨e.val.val, (spec _).mp hit.2, hit.1⟩
    invFun := fun e =>
      let edge : G.edgeSet := ⟨e.val, edgeSet_mono hle e.property.1⟩
      ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.property.2, (spec edge).mpr e.property.1⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem balanced_of_partition {W : Type*} [Fintype W] [DecidableEq W] (G H₁ H₂ : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H₁.Adj] [DecidableRel H₂.Adj]
    (cover : H₁ ⊔ H₂ = G) (disj : Disjoint H₁ H₂)
    (degrees : ∀ v, H₁.degree v = H₂.degree v) :
    ∃ f, ∀ v, simpleDegree G f v true = simpleDegree G f v false := by
  classical
  let f : G.edgeSet → Bool := fun e => decide (e.val ∈ H₁.edgeSet)
  have left_spec (e : G.edgeSet) : f e = true ↔ e.val ∈ H₁.edgeSet := by simp [f]
  have right_spec (e : G.edgeSet) : f e = false ↔ e.val ∈ H₂.edgeSet := by
    have hU : G.edgeSet ⊆ H₁.edgeSet ∪ H₂.edgeSet := by rw [← cover, edgeSet_sup]
    have hin : e.val ∈ H₁.edgeSet ∨ e.val ∈ H₂.edgeSet := hU e.property
    have hi : e.val ∈ H₁.edgeSet → e.val ∈ H₂.edgeSet → False :=
      fun h₁ h₂ => Set.disjoint_left.mp (disjoint_edgeSet.mpr disj) h₁ h₂
    simp only [f, decide_eq_false_iff_not]
    exact ⟨fun h => hin.resolve_left h, fun h h' => hi h' h⟩
  refine ⟨f, fun v => ?_⟩
  rw [simpleDegree_eq_subgraph_degree G H₁ (cover ▸ le_sup_left) f true left_spec,
      simpleDegree_eq_subgraph_degree G H₂ (cover ▸ le_sup_right) f false right_spec, degrees]

private theorem simpleDegree_const {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (v : W) : simpleDegree G (fun _ => true) v true = G.degree v := by
  apply simpleDegree_eq_subgraph_degree G G le_rfl
  exact fun e => ⟨fun _ => e.property, fun _ => rfl⟩

theorem even_degrees (D : Family V E)
    (h : ∀ v, Even (coloredDegree D (fun _ => true) v true)) :
    ∀ x, Even ((graph D).degree x) := by
  rintro (v|e|e) <;> rw [← simpleDegree_const]
  · change Even (simpleDegree (graph D) (fun _ => true) (base v) true)
    simpa [count_base, coloredDegree] using h v
  · change Even (simpleDegree (graph D) (fun _ => true) (lmid e) true)
    simp [count_lmid]
  · change Even (simpleDegree (graph D) (fun _ => true) (rmid e) true)
    simp [count_rmid]

end Kostochka.FiveRegular.Subdivision

end


section -- FiveRegularLayers

/- The Section 5 palette interface uses labeled edges throughout.
The original 5-regular graph can have parallel edges. -/

namespace Kostochka.FiveRegular

open Subdivision SimpleGraph

variable {V E : Type*}

def FamilyIncident (D : Family V E) (v : V) (e : E) : Prop :=
  v = D.left e ∨ v = D.right e

def FamilyMeet (D : Family V E) (e f : E) : Prop :=
  ∃ v, FamilyIncident D v e ∧ FamilyIncident D v f

inductive EdgePart where
  | matching
  | factor (side : Bool)
  | exceptional
  deriving DecidableEq

/-- The pairs of spokes required to have different colors by Section 5,
Stage 2(2)–(4). Both spokes belong to the factor for the specified side. -/
structure StageTwo (D : Family V E) (side : V → Bool) (part : E → EdgePart)
    (marked : V → Prop) (separate : Bool → E → E → Prop) where
  vertex : V → Fin 3
  edge : E → Fin 3
  properVertex : ∀ e, ¬marked (D.left e) → ¬marked (D.right e) →
    side (D.left e) = side (D.right e) → vertex (D.left e) ≠ vertex (D.right e)
  properEdge : ∀ b e f, part e = .factor b → part f = .factor b →
    e ≠ f → FamilyMeet D e f → edge e ≠ edge f
  properIncidence : ∀ b v e, side v = b → ¬marked v → part e = .factor b →
    FamilyIncident D v e → vertex v ≠ edge e
  properSpokes : ∀ b e f, separate b e f → edge e ≠ edge f

/-- Contracting vertices preserves edge labels, so two different original
edges stay different if their unordered endpoint pairs become the same. -/
def contracted (D : Family V E) {Q : Type*} (q : V → Q) (part : E → EdgePart)
    (b : Bool) : Family Q {e : E // part e = .factor b} :=
  ⟨fun e => q (D.left e.val), fun e => q (D.right e.val)⟩

/-- The ordinary side vertices are already properly colored on all original
same-side edges. Factor edges are colored properly after contracting the
selected opposite spoke endpoints. -/
structure ContractedPalette (D : Family V E) (side : V → Bool) (part : E → EdgePart)
    (marked : V → Prop) (b : Bool) {Q : Type*} (q : V → Q) where
  vertex : V → Fin 3
  edge : {e : E // part e = .factor b} → Fin 3
  properVertex : ∀ e, side (D.left e) = b → side (D.right e) = b →
    ¬marked (D.left e) → ¬marked (D.right e) → vertex (D.left e) ≠ vertex (D.right e)
  properEdge : ∀ e f, e ≠ f → FamilyMeet (contracted D q part b) e f → edge e ≠ edge f
  properIncidence : ∀ v e, side v = b → ¬marked v →
    FamilyIncident (contracted D q part b) (q v) e → vertex v ≠ edge e

/-- Stage 2 follows by pulling each factor's contracted partial coloring
back along its vertex map. In particular, sharing a contracted endpoint
forces the opposite-spoke inequality on the original component. -/
noncomputable def stageTwoOfContractions {D : Family V E} {side : V → Bool} {part : E → EdgePart}
    {marked : V → Prop} {separate : Bool → E → E → Prop} {Q : Bool → Type*}
    (q : (b : Bool) → V → Q b)
    (P : ∀ b, ContractedPalette D side part marked b (q b))
    (spokes : ∀ b e f, separate b e f → ∃ (he : part e = .factor b) (hf : part f = .factor b),
      e ≠ f ∧ FamilyMeet (contracted D (q b) part b) ⟨e, he⟩ ⟨f, hf⟩) :
    StageTwo D side part marked separate := by
  classical
  let vc (v : V) := (P (side v)).vertex v
  let ec (e : E) := match h : part e with
    | .factor b => (P b).edge ⟨e, h⟩
    | _ => 0
  have hcol (b : Bool) (e : E) (he : part e = .factor b) : ec e = (P b).edge ⟨e, he⟩ := by
    dsimp only [ec]
    split <;> rename_i h
    · have eq := EdgePart.factor.inj (h.symm.trans he)
      subst b
      rfl
    all_goals simp_all
  have incident (b : Bool) (v : V) (e : E) (he : part e = .factor b)
      (hv : FamilyIncident D v e) :
      FamilyIncident (contracted D (q b) part b) (q b v) ⟨e, he⟩ := by
    rcases hv with h | h
    · exact Or.inl (congrArg (q b) h)
    · exact Or.inr (congrArg (q b) h)
  refine ⟨vc, ec, ?_, ?_, ?_, ?_⟩
  · intro e hl hr hs
    intro hv
    apply (P (side (D.left e))).properVertex e rfl hs.symm hl hr
    exact hv.trans (congrArg (fun b => (P b).vertex (D.right e)) hs.symm)
  · intro b e f he hf hne hm
    obtain ⟨v, hve, hvf⟩ := hm
    rw [hcol b e he, hcol b f hf]
    exact (P b).properEdge _ _ (fun eq => hne (congrArg Subtype.val eq))
      ⟨q b v, incident _ _ _ _ hve, incident _ _ _ _ hvf⟩
  · intro b v e hs hfree he hv
    intro eq
    exact (P b).properIncidence v ⟨e, he⟩ hs hfree (incident _ _ _ _ hv)
      (((congrArg (fun d => (P d).vertex v) hs.symm).trans eq).trans (hcol b e he))
  · intro b e f h
    obtain ⟨he, hf, hn, hm⟩ := spokes b e f h
    rw [hcol b e he, hcol b f hf]
    exact (P b).properEdge _ _ (fun eq => hn (congrArg Subtype.val eq)) hm

/-- A total coloring with one distinct color for the given matching and
two disjoint triples for all other elements. An edge marked `none` is in
the matching. -/
structure CompletedLayers (D : Family V E) (side : V → Bool) (layer : E → Option Bool) where
  vertex : V → Fin 3
  edge : E → Fin 3
  properVertex : ∀ e, side (D.left e) = side (D.right e) →
    vertex (D.left e) ≠ vertex (D.right e)
  properEdge : ∀ b e f, layer e = some b → layer f = some b →
    e ≠ f → FamilyMeet D e f → edge e ≠ edge f
  properIncidence : ∀ v e, layer e = some (side v) → FamilyIncident D v e → vertex v ≠ edge e

private def palette (b : Bool) (c : Fin 3) : Fin 7 :=
  if b then ⟨c.val + 3, by omega⟩ else ⟨c.val, by omega⟩

private theorem palette_eq {b d : Bool} {c e : Fin 3} :
    palette b c = palette d e ↔ b = d ∧ c = e := by
  cases b <;> cases d <;> simp [palette, Fin.ext_iff] <;> omega

private theorem palette_ne_top (b : Bool) (c : Fin 3) : palette b c ≠ 6 := by
  cases b <;> simp [palette, Fin.ext_iff] <;> omega

/-- The standard total-coloring inequalities for a family of labeled edges. -/
def ProperTotal (D : Family V E) (vertex : V → Fin 7) (edge : E → Fin 7) : Prop :=
  (∀ e, vertex (D.left e) ≠ vertex (D.right e)) ∧
  (∀ e f, e ≠ f → FamilyMeet D e f → edge e ≠ edge f) ∧
  (∀ v e, FamilyIncident D v e → vertex v ≠ edge e)

theorem CompletedLayers.total {D : Family V E} {side : V → Bool} {layer : E → Option Bool}
    (P : CompletedLayers D side layer)
    (matching : ∀ e f, layer e = none → layer f = none → FamilyMeet D e f → e = f) :
    ∃ vertex edge, ProperTotal D vertex edge := by
  let ec e := match layer e with
    | some b => palette b (P.edge e)
    | none => 6
  refine ⟨fun v => palette (side v) (P.vertex v), ec, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨hs, hv⟩ := palette_eq.mp he
    exact P.properVertex e hs hv
  · intro e f hne hm he
    cases hl : layer e with
    | none =>
      cases hr : layer f with
      | none => exact hne (matching e f hl hr hm)
      | some d => exact palette_ne_top d _ (by simpa [ec, hl, hr] using he.symm)
    | some b =>
      cases hr : layer f with
      | none => exact palette_ne_top b _ (by simpa [ec, hl, hr] using he)
      | some d =>
        obtain ⟨rfl, h⟩ := palette_eq.mp (by simpa [ec, hl, hr] using he)
        exact P.properEdge b e f hl hr hne hm h
  · intro v e hm he
    cases hl : layer e with
    | none => exact palette_ne_top _ _ (by simpa [ec, hl] using he)
    | some b =>
      obtain ⟨h, h'⟩ := palette_eq.mp (by simpa [ec, hl] using he)
      exact P.properIncidence v e (h ▸ hl) hm h'

end Kostochka.FiveRegular

end


section -- MultiFamily

/- Convert between the multiplicity representation used for cut induction,
the labeled edges used in Section 5, and the board's total coloring. -/

namespace MultFive.Multi
open Finset SimpleGraph Kostochka.FiveRegular Subdivision
variable {V : Type*} (m : Multi V)

/-- Number of labeled edges above an unordered vertex pair. -/
def copies : Sym2 V → ℕ := Sym2.lift ⟨m.count,m.symm⟩

abbrev Edge := Σ p : Sym2 V, Fin (m.copies p)

noncomputable def family : Family V m.Edge where
  left e := e.1.out.1
  right e := e.1.out.2

theorem family_pair (e : m.Edge) : s(m.family.left e, m.family.right e) = e.1 := e.1.out_eq

theorem family_incident_iff (v : V) (e : m.Edge) : FamilyIncident m.family v e ↔ v ∈ e.1 := by
  rw [← m.family_pair e, Sym2.mem_iff]; rfl

theorem family_loopless (e : m.Edge) : m.family.left e ≠ m.family.right e := by
  intro eq
  have h : 0 < m.copies e.1 := Nat.zero_lt_of_lt e.2.isLt
  rw [← m.family_pair e, eq] at h
  exact (m.loopless _ ▸ h : 0 < 0).false

private noncomputable def bag (ec : m.Edge → Fin 7) (p : Sym2 V) : Finset (Fin 7) :=
  univ.image (fun i : Fin (m.copies p) => ec ⟨p,i⟩)

/-- A total coloring of the indexed edges colors every parallel copy of every pair. -/
theorem colorable_of_family (vc : V → Fin 7) (ec : m.Edge → Fin 7)
    (vertices : ∀ e, vc (m.family.left e) ≠ vc (m.family.right e))
    (edges : ∀ e f, e ≠ f → FamilyMeet m.family e f → ec e ≠ ec f)
    (avoids : ∀ v e, FamilyIncident m.family v e → vc v ≠ ec e) : m.Colorable := by
  classical
  refine ⟨vc, fun x y => m.bag ec s(x,y), ?_⟩
  constructor
  · intro x y; rw [Sym2.eq_swap]
  · intro x y
    unfold bag
    rw [card_image_of_injective]
    · exact Fintype.card_fin _
    · intro i j eq
      by_contra ne
      have diff : (⟨s(x,y),i⟩ : m.Edge) ≠ ⟨s(x,y),j⟩ := fun h => ne (by simpa using h)
      exact edges _ _ diff ⟨x, (m.family_incident_iff _ _).mpr (Sym2.mem_mk_left _ _),
        (m.family_incident_iff _ _).mpr (Sym2.mem_mk_left _ _)⟩ eq
  · intro x y hp
    let e : m.Edge := ⟨s(x,y), ⟨0, hp⟩⟩
    have h := vertices e
    obtain ⟨hx,hy⟩ | ⟨hy,hx⟩ := Sym2.eq_iff.mp (m.family_pair e)
    · simpa [hx,hy] using h
    · simpa [hx,hy] using h.symm
  · intro x y hx
    obtain ⟨i,_,hi⟩ := mem_image.mp hx
    exact avoids x ⟨s(x,y),i⟩ ((m.family_incident_iff _ _).mpr (Sym2.mem_mk_left _ _)) hi.symm
  · intro x y z ne
    apply Finset.disjoint_left.mpr
    intro hue h₁ h₂
    obtain ⟨i,_,e₁⟩ := Finset.mem_image.mp h₁
    obtain ⟨j,_,e₂⟩ := Finset.mem_image.mp h₂
    let e : m.Edge := ⟨s(x,y),i⟩
    let f : m.Edge := ⟨s(x,z),j⟩
    have diff : e ≠ f := by
      intro eq
      have pair : s(x,y) = s(x,z) := congrArg Sigma.fst eq
      rcases Sym2.eq_iff.mp pair with h | h <;> grind
    exact edges e f diff ⟨x, (m.family_incident_iff _ _).mpr (Sym2.mem_mk_left _ _),
      (m.family_incident_iff _ _).mpr (Sym2.mem_mk_left _ _)⟩ (e₁.trans e₂.symm)

end MultFive.Multi

namespace MultFive
open SimpleGraph

theorem simple_totalColorable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : (ofSimple G).Colorable) : G.TotalColorable 7 := by
  classical
  obtain ⟨vc,ec,valid⟩ := h
  let bag : Sym2 V → Finset (Fin 7) := Sym2.lift ⟨ec, valid.symmetric⟩
  have ne (e : G.edgeSet) : (bag e.val).Nonempty := by
    obtain ⟨p, hp⟩ := e
    induction p using Sym2.ind with
    | _ x y =>
      have hsz := valid.size x y
      change (ec x y).card = (if G.Adj x y then 1 else 0) at hsz
      apply Finset.card_pos.mp
      change 0 < (ec x y).card
      rw [hsz, if_pos (show G.Adj x y from hp)]
      decide
  let color (e : G.edgeSet) := (ne e).choose
  refine ⟨Sum.elim vc color, ?_, ?_, ?_⟩
  · intro x y xy
    exact valid.vertices x y (by simp [ofSimple,xy])
  · rintro ⟨e,he⟩ ⟨f,hf⟩ diff ⟨v,ve,vf⟩ eq
    obtain ⟨x,rfl⟩ := Sym2.mem_iff_exists.mp ve
    obtain ⟨y,rfl⟩ := Sym2.mem_iff_exists.mp vf
    change color ⟨s(v,x),he⟩ = color ⟨s(v,y),hf⟩ at eq
    have xy : x ≠ y := fun e => diff (Subtype.ext (congrArg (fun u => s(v,u)) e))
    exact (Finset.disjoint_left.mp (valid.disjoint v x y xy)) (ne ⟨s(v,x),he⟩).choose_spec
      (show color ⟨s(v,x),he⟩ ∈ ec v y from eq.symm ▸ (ne ⟨s(v,y),hf⟩).choose_spec)
  · rintro v ⟨e,he⟩ ve eq
    obtain ⟨x,rfl⟩ := Sym2.mem_iff_exists.mp ve
    change vc v = color ⟨s(v,x),he⟩ at eq
    exact valid.avoids v x (show vc v ∈ ec v x from eq.symm ▸ (ne ⟨s(v,x),he⟩).choose_spec)

end MultFive

end


section -- MultiClosure

/- The unrestricted maximum-degree-five bound for finite simple graphs
follows from the regular multigraph perfect-matching case of Kostochka. -/
namespace MultFive
universe u

theorem simple_of_regular_matching (color : RegularMatchingColorable.{u})
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (bound : ∀ v, G.degree v ≤ 5) : G.TotalColorable 7 := by
  apply simple_totalColorable G
  apply colorable_of_regular_matching color
  intro v
  simpa [degree_ofSimple] using bound v

end MultFive

end

open SimpleGraph MultFive

theorem OMA.solution :
    OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1.H2 := by
  classical
  intro V _ _ G _ degree uncolored
  by_contra noCounterexample
  apply uncolored
  apply simple_of_regular_matching _ G (fun v => degree ▸ G.degree_le_maxDegree v)
  intro W wFinite _ m regular matched
  by_contra noColor
  apply noCounterexample
  refine ⟨W, wFinite, m.support, m.count, m.symm, m.loopless, regular,
    fun _ _ => Iff.rfl, matched, ?_⟩
  rintro ⟨vc, ec, symmetric, size, vertices, avoids, disjoint⟩
  exact noColor ⟨vc, ec, ⟨symmetric, size, vertices, avoids, disjoint⟩⟩
