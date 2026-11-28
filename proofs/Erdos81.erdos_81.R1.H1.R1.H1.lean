import OMAReductions.R_Erdos81_erdos_81_R1_H1_R1
import Mathlib

/-!
A minimal separator of a chordal graph is a clique. A nonedge inside the
separator, together with shortest paths through the two sides, is a chordless
cycle of length at least four.
-/

open Finset SimpleGraph

namespace ChordalSeparator

lemma geodesic_isChordless {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) : p.IsChordless := by
  rw [Walk.isChordless_iff_forall_mem_edges]
  intro a b ha hb hab
  obtain ⟨i, hia, hi⟩ := Walk.mem_support_iff_exists_getVert.mp ha
  obtain ⟨j, hjb, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hb
  have hswap : s(a, b) ∈ p.edges := by
    rcases le_total i j with hij | hij
    · have hab' : G.Adj (p.getVert i) (p.getVert j) := by simpa [hia, hjb] using hab
      by_cases heq : j = i
      · exact (hab'.ne (by simp [heq, hia])).elim
      · have hlt : i < j := lt_of_le_of_ne hij (Ne.symm heq)
        by_cases hsucc : j = i + 1
        · refine (Walk.mk_mem_edges_iff_exists p).2 ⟨i, by omega, ?_⟩
          rw [hia, show p.getVert (i + 1) = b by rw [← hsucc, hjb]]
        · have hgap : i + 2 ≤ j := by omega
          have hadj : G.Adj (p.getVert i) (p.getVert j) := hab'
          let q := (p.take i).append (hadj.toWalk.append (p.drop j))
          have hlen : q.length = i + 1 + (p.length - j) := by
            simp only [q, Walk.length_append, Adj.length_toWalk, Walk.take_length,
              Walk.drop_length, min_eq_left hi, add_assoc]
          have hdist : G.dist u v ≤ q.length := dist_le q
          have : G.dist u v < p.length := by
            calc G.dist u v ≤ q.length := hdist
              _ = i + 1 + (p.length - j) := hlen
              _ < p.length := by omega
          exact (lt_irrefl _ (this.trans_le (by simp [hp]))).elim
    · have hba : G.Adj (p.getVert j) (p.getVert i) := by simpa [hia, hjb] using hab.symm
      by_cases heq : i = j
      · exact (hba.ne (by simp [heq, hjb])).elim
      · have hlt : j < i := lt_of_le_of_ne hij (Ne.symm heq)
        by_cases hsucc : i = j + 1
        · refine (Walk.mk_mem_edges_iff_exists p).2 ⟨j, by omega, ?_⟩
          rw [← hsucc, hia, hjb]
          exact Sym2.eq_swap
        · have hgap : j + 2 ≤ i := by omega
          let q := (p.take j).append (hba.toWalk.append (p.drop i))
          have hlen : q.length = j + 1 + (p.length - i) := by
            simp only [q, Walk.length_append, Adj.length_toWalk, Walk.take_length,
              Walk.drop_length, min_eq_left hj, add_assoc]
          have : G.dist u v < p.length := by
            calc G.dist u v ≤ q.length := dist_le q
              _ = j + 1 + (p.length - i) := hlen
              _ < p.length := by omega
          exact (lt_irrefl _ (this.trans_le (by simp [hp]))).elim
  exact hswap

lemma chordless_cycle_forbidden {V : Type*} {G : SimpleGraph V} (hG : G.IsChordal)
    {u : V} (p : G.Walk u u) (hc : p.IsCycle) (hcl : p.IsChordless) (hl : 4 ≤ p.length) : False := by
  let f : Fin p.length → V := fun i => p.getVert i.val
  have hinj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    exact hc.getVert_injOn'
      (by simp only [Set.mem_ofPred_eq]; have := a.isLt; omega)
      (by simp only [Set.mem_ofPred_eq]; have := b.isLt; omega) hab
  have hl0 : 0 < p.length := by omega
  have hmod (i : ℕ) (h : i < p.length) :
      p.getVert (i + 1) = p.getVert ((i + 1) % p.length) := by
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with heq | hlt
    · change i + 1 = p.length at heq
      rw [heq, Nat.mod_self, p.getVert_length, p.getVert_zero]
    · rw [Nat.mod_eq_of_lt hlt]
  have hind : p.toSubgraph.IsInduced := Walk.isInduced_toSubgraph.mpr hcl
  have hstep : ∀ a b : Fin p.length,
      G.Adj (f a) (f b) ↔
        b.val = (a.val + 1) % p.length ∨ a.val = (b.val + 1) % p.length := by
    intro a b
    constructor
    · intro h
      have ha := p.mem_verts_toSubgraph.mpr (p.getVert_mem_support a.val)
      have hb := p.mem_verts_toSubgraph.mpr (p.getVert_mem_support b.val)
      obtain ⟨i, he, hit⟩ := p.toSubgraph_adj_iff.mp (hind ha hb h)
      rw [hmod i hit] at he
      rcases Sym2.eq_iff.mp he with ⟨ha', hb'⟩ | ⟨hb', ha'⟩
      · have h₁ : i = a.val := hc.getVert_injOn'
          (by simp only [Set.mem_ofPred_eq]; omega)
          (by simp only [Set.mem_ofPred_eq]; have := a.isLt; omega) ha'
        have h₂ : (i + 1) % p.length = b.val := hc.getVert_injOn'
          (by simp only [Set.mem_ofPred_eq]; have := Nat.mod_lt (i + 1) hl0; omega)
          (by simp only [Set.mem_ofPred_eq]; have := b.isLt; omega) hb'
        exact Or.inl (h₂.symm.trans (by rw [h₁]))
      · have h₁ : i = b.val := hc.getVert_injOn'
          (by simp only [Set.mem_ofPred_eq]; omega)
          (by simp only [Set.mem_ofPred_eq]; have := b.isLt; omega) hb'
        have h₂ : (i + 1) % p.length = a.val := hc.getVert_injOn'
          (by simp only [Set.mem_ofPred_eq]; have := Nat.mod_lt (i + 1) hl0; omega)
          (by simp only [Set.mem_ofPred_eq]; have := a.isLt; omega) ha'
        exact Or.inr (h₂.symm.trans (by rw [h₁]))
    · rintro (h | h)
      · rw [show f b = p.getVert ((a.val + 1) % p.length) from by simp [f, h], ← hmod a.val a.isLt]
        simpa [f] using p.adj_getVert_succ a.isLt
      · rw [show f a = p.getVert ((b.val + 1) % p.length) from by simp [f, h], ← hmod b.val b.isLt]
        simpa [f] using (p.adj_getVert_succ b.isLt).symm
  have honeN : 1 < p.length := by omega
  let oneF : Fin p.length := ⟨1, honeN⟩
  have hone : oneF.val = 1 := rfl
  have hbridge : ∀ a b : Fin p.length,
      (b.val = (a.val + 1) % p.length ∨ a.val = (b.val + 1) % p.length) ↔
        (cycleGraph p.length).Adj a b := by
    have : NeZero p.length := ⟨by omega⟩
    intro a b
    rw [cycleGraph_adj']
    constructor
    · rintro (h | h)
      · right
        have hb : b = a + oneF := by
          apply Fin.ext
          rw [Fin.val_add, hone]
          exact h
        have hcancel : a + oneF - a = oneF := add_sub_cancel_left a oneF
        rw [hb, hcancel]
      · left
        have ha : a = b + oneF := by
          apply Fin.ext
          rw [Fin.val_add, hone]
          exact h
        have hcancel : b + oneF - b = oneF := add_sub_cancel_left b oneF
        rw [ha, hcancel]
    · rintro (h | h)
      · right
        have hsub : a - b = oneF := by
          apply Fin.ext
          rw [h, hone]
        have ha : a = b + oneF := sub_eq_iff_eq_add'.mp hsub
        have hval := congrArg Fin.val ha
        rwa [Fin.val_add, hone] at hval
      · left
        have hsub : b - a = oneF := by
          apply Fin.ext
          rw [h, hone]
        have hb : b = a + oneF := sub_eq_iff_eq_add'.mp hsub
        have hval := congrArg Fin.val hb
        rwa [Fin.val_add, hone] at hval
  have hfadj : ∀ i j : Fin p.length,
      G.Adj (f i) (f j) ↔ (cycleGraph p.length).Adj i j := by
    intro i j
    exact (hstep i j).trans (hbridge i j)
  exact hG p.length hl ⟨⟨⟨f, hinj⟩, hfadj _ _⟩⟩

variable {n : ℕ} (G : SimpleGraph (Fin n))

def inside (S C : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj x y := G.Adj x y ∧ x ∈ S ∧ y ∈ S ∧ x ∉ C ∧ y ∉ C
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

lemma inside_support {S C : Finset (Fin n)} {u v : Fin n} (w : (inside G S C).Walk u v) :
    u ∈ S ∧ u ∉ C → ∀ z ∈ w.support, z ∈ S ∧ z ∉ C := by
  induction w with
  | nil =>
    intro hu z hz
    simp only [Walk.support_nil, List.mem_singleton] at hz
    subst z
    exact hu
  | cons hxy q ih =>
    intro hu z hz
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hu
    · exact ih ⟨hxy.2.2.1, hxy.2.2.2.2⟩ z hz

lemma reachable_inside {S C : Finset (Fin n)} {a x : Fin n}
    (ha : a ∈ S ∧ a ∉ C) (h : (inside G S C).Reachable a x) : x ∈ S ∧ x ∉ C := by
  obtain ⟨w⟩ := h
  exact inside_support G w ha x w.end_mem_support

def sideGraph (H : SimpleGraph (Fin n)) (side : Set (Fin n)) (x y : Fin n) : SimpleGraph (Fin n) where
  Adj p q :=
    (H.Adj p q ∧ p ∈ side ∧ q ∈ side) ∨
    (p = x ∧ q ∈ side ∧ G.Adj x q) ∨
    (q = x ∧ p ∈ side ∧ G.Adj x p) ∨
    (p = y ∧ q ∈ side ∧ G.Adj y q) ∨
    (q = y ∧ p ∈ side ∧ G.Adj y p)
  symm := ⟨fun p q h => by
    rcases h with ⟨h1, h2, h3⟩ | ⟨rfl, h2, h3⟩ | ⟨rfl, h2, h3⟩ | ⟨rfl, h2, h3⟩ | ⟨rfl, h2, h3⟩
    · exact Or.inl ⟨h1.symm, h3, h2⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, h2, h3⟩))
    · exact Or.inr (Or.inl ⟨rfl, h2, h3⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h2, h3⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h2, h3⟩)))⟩
  loopless := ⟨fun _ h => by
    rcases h with ⟨h1, _, _⟩ | ⟨rfl, _, h3⟩ | ⟨rfl, _, h3⟩ | ⟨rfl, _, h3⟩ | ⟨rfl, _, h3⟩
    · exact h1.ne rfl
    · exact h3.ne rfl.symm
    · exact h3.ne rfl.symm
    · exact h3.ne rfl.symm
    · exact h3.ne rfl.symm⟩

lemma sideGraph_right {H : SimpleGraph (Fin n)} {side : Set (Fin n)} {x y p q : Fin n}
    (h : (sideGraph G H side x y).Adj p q) : q ∈ side ∨ q = x ∨ q = y := by
  rcases h with h | h | h | h | h
  · exact Or.inl h.2.2
  · exact Or.inl h.2.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inl h.2.1
  · exact Or.inr (Or.inr h.1)

lemma sideGraph_le {H : SimpleGraph (Fin n)} {side : Set (Fin n)} {x y : Fin n}
    (hH : H ≤ G) : sideGraph G H side x y ≤ G := by
  intro p q h
  rcases h with ⟨h1, _, _⟩ | ⟨rfl, _, h3⟩ | ⟨rfl, _, h3⟩ | ⟨rfl, _, h3⟩ | ⟨rfl, _, h3⟩
  · exact hH h1
  · exact h3
  · exact h3.symm
  · exact h3
  · exact h3.symm

lemma sideGraph_adj_left {H side x y v} (hv : v ∈ side) (hg : G.Adj x v) :
    (sideGraph G H side x y).Adj x v :=
  Or.inr (Or.inl ⟨rfl, hv, hg⟩)

lemma sideGraph_adj_right {H side x y v} (hv : v ∈ side) (hg : G.Adj y v) :
    (sideGraph G H side x y).Adj y v :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hv, hg⟩)))

lemma inside_le (S C : Finset (Fin n)) : inside G S C ≤ G := fun _ _ h => h.1

def toInside {S C : Finset (Fin n)} {u v : Fin n} (w : G.Walk u v)
    (hw : ∀ z ∈ w.support, z ∈ S ∧ z ∉ C) : (inside G S C).Walk u v :=
  w.transfer (inside G S C) fun e he => by
    induction e using Sym2.ind with
    | h p q =>
      rw [mem_edgeSet]
      have hpq : G.Adj p q := by
        have hs : s(p, q) ∈ G.edgeSet := w.edges_subset_edgeSet he
        rwa [mem_edgeSet] at hs
      have hp := hw p (w.fst_mem_support_of_mem_edges he)
      have hq := hw q (w.snd_mem_support_of_mem_edges he)
      exact ⟨hpq, hp.1, hq.1, hp.2, hq.2⟩

lemma exists_touch {S C : Finset (Fin n)} {a b c : Fin n} (w : G.Walk a b)
    (hwS : ∀ z ∈ w.support, z ∈ S) (honly : ∀ z ∈ w.support, z ∈ C → z = c)
    (hcmem : c ∈ w.support) (hcC : c ∈ C) (haC : a ∉ C) :
    ∃ p, G.Adj p c ∧ (inside G S C).Reachable a p := by
  let w1 := w.takeUntil c hcmem
  have hpen : ¬ w1.Nil := by
    intro hnil
    have heq : a = c := (Walk.nil_takeUntil w hcmem).1 hnil
    exact haC (heq ▸ hcC)
  have hadj : G.Adj w1.penultimate c := w1.adj_penultimate hpen
  have hpre : ∀ z ∈ w1.dropLast.support, z ∈ S ∧ z ∉ C := by
    intro z hz
    have hzdrop : z ∈ w1.support.dropLast := by simpa [Walk.support_dropLast hpen] using hz
    have hz1 : z ∈ w1.support := (List.dropLast_sublist w1.support).subset hzdrop
    have hzW : z ∈ w.support := (Walk.isSubwalk_takeUntil w hcmem).support_subset hz1
    refine ⟨hwS z hzW, ?_⟩
    intro hzC
    have hzc : z = c := honly z hzW hzC
    obtain ⟨k, hk, hkle⟩ := Walk.mem_support_iff_exists_getVert.mp hz
    have hklt : k < w1.length := by
      have hlen1 : w1.dropLast.length + 1 = w1.length := Walk.length_dropLast_add_one hpen
      omega
    have hne : w.getVert k ≠ c := Walk.getVert_lt_length_takeUntil_ne hcmem hklt
    have heqk : w1.dropLast.getVert k = w.getVert k := by
      rw [Walk.getVert_dropLast hklt, w.getVert_takeUntil hcmem (Nat.le_of_lt hklt)]
    exact hne (heqk.symm.trans (hk.trans hzc))
  exact ⟨w1.penultimate, hadj, (toInside G w1.dropLast hpre).reachable⟩

lemma sideGraph_support {H : SimpleGraph (Fin n)} {side : Set (Fin n)} {x y u v : Fin n}
    (p : (sideGraph G H side x y).Walk u v) :
    (u ∈ side ∨ u = x ∨ u = y) → ∀ z ∈ p.support, z ∈ side ∨ z = x ∨ z = y := by
  induction p with
  | nil =>
    intro hu z hz
    simp only [Walk.support_nil, List.mem_singleton] at hz
    subst z
    exact hu
  | cons hxy q ih =>
    intro hu z hz
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hu
    · exact ih (sideGraph_right G hxy) z hz

def walk_in_side {H : SimpleGraph (Fin n)} {side : Set (Fin n)} {x y u v : Fin n}
    (w : H.Walk u v) (hw : ∀ z ∈ w.support, z ∈ side) :
    (sideGraph G H side x y).Walk u v :=
  w.transfer (sideGraph G H side x y) fun e he => by
    induction e using Sym2.ind with
    | h p q =>
      rw [mem_edgeSet]
      have hpq : H.Adj p q := by
        have hs : s(p, q) ∈ H.edgeSet := w.edges_subset_edgeSet he
        rwa [mem_edgeSet] at hs
      exact Or.inl ⟨hpq, hw _ (w.fst_mem_support_of_mem_edges he),
        hw _ (w.snd_mem_support_of_mem_edges he)⟩

lemma side_path {H : SimpleGraph (Fin n)} {side : Set (Fin n)} {x y px py : Fin n}
    (hH : H ≤ G) (hclose : ∀ {u v}, u ∈ side → v ∈ side → G.Adj u v → H.Adj u v)
    (hx : x ∉ side) (hy : y ∉ side) (hna : ¬ G.Adj x y) (hnexy : x ≠ y)
    (hpxs : px ∈ side) (hpys : py ∈ side) (hpxa : G.Adj x px) (hpya : G.Adj y py)
    (w : H.Walk px py) (hw : ∀ z ∈ w.support, z ∈ side) :
    ∃ p : G.Walk x y, p.IsPath ∧ p.IsChordless ∧ 2 ≤ p.length ∧
      (∀ z ∈ p.support, z ∈ side ∨ z = x ∨ z = y) := by
  let SG := sideGraph G H side x y
  have hle : SG ≤ G := sideGraph_le G hH
  have hwSG : SG.Walk px py := walk_in_side G w hw
  have hxpx : SG.Adj x px := sideGraph_adj_left G hpxs hpxa
  have hpyp : SG.Adj py y := (sideGraph_adj_right G hpys hpya).symm
  let wxy : SG.Walk x y := hxpx.toWalk.append (hwSG.append hpyp.toWalk)
  have hreach : SG.Reachable x y := wxy.reachable
  have hnot : ¬ SG.Adj x y := by
    intro h
    rcases h with h | h | h | h | h
    · exact hx h.2.1
    · exact hy h.2.1
    · exact hnexy h.1.symm
    · exact hnexy h.1
    · exact hx h.2.1
  obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
  have hlen : 2 ≤ q.length := by
    rw [hq]
    exact Nat.succ_le_of_lt (hreach.one_lt_dist_of_ne_of_not_adj hnexy hnot)
  have hpath : q.IsPath := q.isPath_of_length_eq_dist hq
  have hchord : q.IsChordless := geodesic_isChordless q hq
  have hsupq : ∀ z ∈ q.support, z ∈ side ∨ z = x ∨ z = y :=
    sideGraph_support G q (Or.inr (Or.inl rfl))
  let p : G.Walk x y := q.mapLe hle
  have hpcl : p.IsChordless := by
    rw [Walk.isChordless_iff_forall_mem_edges]
    intro a b ha hb hab
    rw [Walk.support_mapLe_eq_support hle q] at ha hb
    rw [Walk.edges_mapLe_eq_edges hle q]
    apply hchord.mem_edges ha hb
    rcases hsupq a ha with haS | rfl | rfl
    · rcases hsupq b hb with hbS | rfl | rfl
      · exact Or.inl ⟨hclose haS hbS hab, haS, hbS⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, haS, hab.symm⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, haS, hab.symm⟩)))
    · rcases hsupq b hb with hbS | rfl | rfl
      · exact sideGraph_adj_left G hbS hab
      · exact (hab.ne rfl).elim
      · exact (hna hab).elim
    · rcases hsupq b hb with hbS | rfl | rfl
      · exact sideGraph_adj_right G hbS hab
      · exact (hna hab.symm).elim
      · exact (hab.ne rfl).elim
  refine ⟨p, (Walk.isPath_mapLe hle).mpr hpath, hpcl, ?_, ?_⟩
  · rw [show p.length = q.length from Walk.length_mapLe hle q]
    exact hlen
  · intro z hz
    rw [Walk.support_mapLe_eq_support hle q] at hz
    exact hsupq z hz

end ChordalSeparator

open ChordalSeparator

set_option maxHeartbeats 800000 in
theorem OMA.solution : OMA.R_Erdos81_erdos_81_R1_H1_R1.H1 := by
  classical
  intro n G hCh S C a b haS hbS hab separates hpack
  rw [isClique_iff]
  intro x hx y hy hxy
  by_contra hna
  rcases hpack with ⟨hsep, hmin⟩
  rcases hsep with ⟨hCS, haC, hbC, hhit⟩
  let H := inside G S C
  have hno : ¬ H.Reachable a b := by
    intro hreach
    obtain ⟨w⟩ := hreach
    have hw := inside_support G w ⟨haS, haC⟩
    let wG : G.Walk a b := w.map (Hom.ofLE (inside_le G S C))
    have hSw : ∀ z ∈ wG.support, z ∈ S := by
      intro z hz
      rw [Walk.support_map, Hom.coe_ofLE, List.mem_map] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      exact (hw z' hz').1
    obtain ⟨z, hz, hzC⟩ := hhit wG hSw
    rw [Walk.support_map, Hom.coe_ofLE, List.mem_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    exact (hw z' hz').2 hzC
  have havoid (c : Fin n) (hc : c ∈ C) :
      ∃ w : G.Walk a b, (∀ z ∈ w.support, z ∈ S) ∧ (∀ z ∈ w.support, z ∈ C → z = c) := by
    by_contra hbad
    have hsepE : separates (C.erase c) := by
      refine ⟨(erase_subset c C).trans hCS, ?_, ?_, ?_⟩
      · intro h
        exact haC (mem_of_mem_erase h)
      · intro h
        exact hbC (mem_of_mem_erase h)
      · intro w hw
        by_contra hmiss
        have honly : ∀ z ∈ w.support, z ∈ C → z = c := by
          intro z hz hzC
          by_contra hzne
          exact hmiss ⟨z, hz, mem_erase.mpr ⟨hzne, hzC⟩⟩
        exact hbad ⟨w, hw, honly⟩
    exact notMem_erase c C ((hmin (C.erase c) (erase_subset c C) hsepE) hc)
  let sideA : Set (Fin n) := {z | H.Reachable a z}
  let sideB : Set (Fin n) := {z | H.Reachable b z}
  have hdisjAB : ∀ z, z ∈ sideA → z ∈ sideB → False := by
    intro z hzA hzB
    exact hno (hzA.trans hzB.symm)
  have hxA : x ∉ sideA := by
    intro hxR
    exact (reachable_inside G ⟨haS, haC⟩ hxR).2 hx
  have hyA : y ∉ sideA := by
    intro hyR
    exact (reachable_inside G ⟨haS, haC⟩ hyR).2 hy
  have hxB : x ∉ sideB := by
    intro hxR
    exact (reachable_inside G ⟨hbS, hbC⟩ hxR).2 hx
  have hyB : y ∉ sideB := by
    intro hyR
    exact (reachable_inside G ⟨hbS, hbC⟩ hyR).2 hy
  have hcloseA : ∀ {u v}, u ∈ sideA → v ∈ sideA → G.Adj u v → H.Adj u v := by
    intro u v hu hv huv
    have hu' := reachable_inside G ⟨haS, haC⟩ hu
    have hv' := reachable_inside G ⟨haS, haC⟩ hv
    exact ⟨huv, hu'.1, hv'.1, hu'.2, hv'.2⟩
  have hcloseB : ∀ {u v}, u ∈ sideB → v ∈ sideB → G.Adj u v → H.Adj u v := by
    intro u v hu hv huv
    have hu' := reachable_inside G ⟨hbS, hbC⟩ hu
    have hv' := reachable_inside G ⟨hbS, hbC⟩ hv
    exact ⟨huv, hu'.1, hv'.1, hu'.2, hv'.2⟩
  have htouch (c : Fin n) (hc : c ∈ C) :
      (∃ p, G.Adj p c ∧ H.Reachable a p) ∧ (∃ p, G.Adj p c ∧ H.Reachable b p) := by
    obtain ⟨w, hwS, honly⟩ := havoid c hc
    have hcW : c ∈ w.support := by
      obtain ⟨z, hz, hzC⟩ := hhit w hwS
      exact (honly z hz hzC) ▸ hz
    refine ⟨exists_touch G w hwS honly hcW hc haC, ?_⟩
    have hwSr : ∀ z ∈ w.reverse.support, z ∈ S := by
      intro z hz
      rw [Walk.support_reverse, List.mem_reverse] at hz
      exact hwS z hz
    have honlyr : ∀ z ∈ w.reverse.support, z ∈ C → z = c := by
      intro z hz hzC
      rw [Walk.support_reverse, List.mem_reverse] at hz
      exact honly z hz hzC
    have hcR : c ∈ w.reverse.support := by
      rw [Walk.support_reverse, List.mem_reverse]
      exact hcW
    exact exists_touch G w.reverse hwSr honlyr hcR hc hbC
  obtain ⟨⟨px, hpx, hApx⟩, ⟨qx, hqx, hBqx⟩⟩ := htouch x hx
  obtain ⟨⟨py, hpy, hApy⟩, ⟨qy, hqy, hBqy⟩⟩ := htouch y hy
  obtain ⟨wA⟩ := hApx.symm.trans hApy
  have hwA : ∀ z ∈ wA.support, z ∈ sideA := by
    intro z hz
    exact hApx.trans (wA.takeUntil z hz).reachable
  obtain ⟨wB⟩ := hBqy.symm.trans hBqx
  have hwB : ∀ z ∈ wB.support, z ∈ sideB := by
    intro z hz
    exact hBqy.trans (wB.takeUntil z hz).reachable
  obtain ⟨pA, hpA, hclA, hlenA, hsupA⟩ := side_path G (inside_le G S C) hcloseA hxA hyA hna hxy
    hApx hApy hpx.symm hpy.symm wA hwA
  obtain ⟨pB, hpB, hclB, hlenB, hsupB⟩ := side_path G (inside_le G S C) hcloseB hyB hxB
    (fun h => hna h.symm) hxy.symm hBqy hBqx hqy.symm hqx.symm wB hwB
  have hx_tail : x ∉ pA.support.tail := by
    have hnodup := hpA.support_nodup
    rw [← pA.cons_tail_support, List.nodup_cons] at hnodup
    exact hnodup.1
  have hy_tail : y ∉ pB.support.tail := by
    have hnodup := hpB.support_nodup
    rw [← pB.cons_tail_support, List.nodup_cons] at hnodup
    exact hnodup.1
  have htails : pA.support.tail.Disjoint pB.support.tail := by
    intro z hzA hzB
    have hzAs : z ∈ pA.support := List.mem_of_mem_tail hzA
    have hzBs : z ∈ pB.support := List.mem_of_mem_tail hzB
    have hA := hsupA z hzAs
    have hB := hsupB z hzBs
    have hz_ne_x : z ≠ x := by
      intro hzx
      exact hx_tail (hzx ▸ hzA)
    have hz_ne_y : z ≠ y := by
      intro hzy
      exact hy_tail (hzy ▸ hzB)
    rcases hA with hzA' | hzA' | hzA'
    · rcases hB with hzB' | hzB' | hzB'
      · exact hdisjAB z hzA' hzB'
      · exact hz_ne_y hzB'
      · exact hz_ne_x hzB'
    · exact hz_ne_x hzA'
    · exact hz_ne_y hzA'
  have hcyc : (pA.append pB).IsCycle :=
    hpA.isCycle_append hpB htails (Or.inl (by omega))
  have hchord : (pA.append pB).IsChordless := by
    rw [Walk.isChordless_iff_forall_mem_edges]
    intro u v hu hv huv
    rw [Walk.mem_support_append_iff] at hu hv
    rw [Walk.edges_append]
    rcases hu with huA | huB
    · rcases hv with hvA | hvB
      · exact List.mem_append_left _ (hclA.mem_edges huA hvA huv)
      · by_cases huB' : u ∈ pB.support
        · exact List.mem_append_right _ (hclB.mem_edges huB' hvB huv)
        · by_cases hvA' : v ∈ pA.support
          · exact List.mem_append_left _ (hclA.mem_edges huA hvA' huv)
          · have huS : u ∈ sideA := by
              rcases hsupA u huA with h | h | h
              · exact h
              · exact (huB' (h ▸ pB.end_mem_support)).elim
              · exact (huB' (h ▸ pB.start_mem_support)).elim
            have hvS : v ∈ sideB := by
              rcases hsupB v hvB with h | h | h
              · exact h
              · exact (hvA' (h ▸ pA.end_mem_support)).elim
              · exact (hvA' (h ▸ pA.start_mem_support)).elim
            have hu' := reachable_inside G ⟨haS, haC⟩ huS
            have hv' := reachable_inside G ⟨hbS, hbC⟩ hvS
            have hHadj : H.Adj u v := ⟨huv, hu'.1, hv'.1, hu'.2, hv'.2⟩
            exact (hno (huS.trans (hHadj.reachable.trans hvS.symm))).elim
    · rcases hv with hvA | hvB
      · by_cases hvB' : v ∈ pB.support
        · exact List.mem_append_right _ (hclB.mem_edges huB hvB' huv)
        · by_cases huA' : u ∈ pA.support
          · exact List.mem_append_left _ (hclA.mem_edges huA' hvA huv)
          · have hvS : v ∈ sideA := by
              rcases hsupA v hvA with h | h | h
              · exact h
              · exact (hvB' (h ▸ pB.end_mem_support)).elim
              · exact (hvB' (h ▸ pB.start_mem_support)).elim
            have huS : u ∈ sideB := by
              rcases hsupB u huB with h | h | h
              · exact h
              · exact (huA' (h ▸ pA.end_mem_support)).elim
              · exact (huA' (h ▸ pA.start_mem_support)).elim
            have hv' := reachable_inside G ⟨haS, haC⟩ hvS
            have hu' := reachable_inside G ⟨hbS, hbC⟩ huS
            have hHadj : H.Adj u v := ⟨huv, hu'.1, hv'.1, hu'.2, hv'.2⟩
            exact (hno (hvS.trans (hHadj.symm.reachable.trans huS.symm))).elim
      · exact List.mem_append_right _ (hclB.mem_edges huB hvB huv)
  have hlen : 4 ≤ (pA.append pB).length := by
    rw [Walk.length_append]
    omega
  exact chordless_cycle_forbidden hCh (pA.append pB) hcyc hchord hlen
