import FormalConjectures.ErdosProblems.«151»
import Mathlib

/-! Extending a triangle-free clique-hitting subgraph one vertex at a time.
Credit: @ellisjr. The guarded deletion and Ramsey bounds are due to @sun-jiao
in the preceding reduction. The extension works for maximal cliques of every size.
The seven-vertex link test is finite after adjoining the isolated vertices to the
chosen set. Eight is the first link order for which an extension can fail.
The threshold-ten case is discharged by overlapping guards, refining
Patrick White’s observation on deleting an independent set with its guards. -/

namespace OMA.R_Erdos151_erdos_151_R3

open Finset SimpleGraph
open scoped Classical

/-- A triangle-free graph R on a link can be extended over its center when at most
seven link vertices have a neighbor in the link. Singletons are maximal cliques here. -/
def H1 : Prop := ∀ (n : ℕ) (G R : SimpleGraph (Fin n)) (N : Finset (Fin n)),
  R ≤ G → R.CliqueFree 3 → (N.filter fun x => ∃ y ∈ N, G.Adj x y).card ≤ 7 →
  ∃ A ⊆ N, R.IsIndepSet (A : Set (Fin n)) ∧
    ∀ q : Finset (Fin n), q.Nonempty →
      Maximal (fun t : Finset (Fin n) => t ⊆ N ∧ G.IsClique (t : Set (Fin n))) q →
      (∃ x ∈ q, x ∈ A) ∨ ∃ x ∈ q, ∃ y ∈ q, R.Adj x y

/-- It suffices to treat graphs in which every nonedge has a common neighbor and
every covered pair of neighborhoods leaves fewer than H vertices. At the remaining
Ramsey jumps there is a nonempty vertex set U. Every vertex
of U has a link inside U with at least eight nonisolated vertices and a
triangle-free choice of edges which cannot be extended over that vertex. -/
def H2 : Prop := ∀ (m : ℕ) (G : SimpleGraph (Fin (m+1))),
  (∀ u v, u ≠ v → ¬ G.Adj u v → ∃ w, G.Adj u w ∧ G.Adj v w) →
  (∀ (u v : Fin (m+1)) (C : Finset (Fin (m+1))),
    (∀ x y, G.Adj u x → ¬ G.Adj v x → G.Adj v y → ¬ G.Adj u y →
      G.Adj x y → x ∈ C ∨ y ∈ C) →
    (univ.filter (fun x => (G.Adj u x ∨ G.Adj v x) ∧ x ∉ C)).card < Erdos151.H (m+1)) →
  Erdos151.H (m+1) ≠ 10 → Erdos151.H (m+1) ≠ 11 →
  Erdos151.H m < Erdos151.H (m+1) →
  (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H (m+1)) →
  (∀ A B : Finset (Fin (m+1)), B.Nonempty → A ⊆ B →
    (∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A) →
    A.card + Erdos151.H (m+1 - B.card) < Erdos151.H (m+1)) →
  (∃ U : Finset (Fin (m+1)), U.Nonempty ∧ ∀ v ∈ U,
    let N := U.filter (G.Adj v)
    8 ≤ (N.filter fun x => ∃ y ∈ N, G.Adj x y).card ∧
    (2 ≤ ∑ x ∈ N, ((N.filter (G.Adj x)).card - 2)) ∧
    ∃ R : SimpleGraph (Fin (m+1)), R ≤ G ∧ R.CliqueFree 3 ∧
      ¬ ∃ A ⊆ N, R.IsIndepSet (A : Set (Fin (m+1))) ∧
        ∀ q : Finset (Fin (m+1)), q.Nonempty →
          Maximal (fun t : Finset (Fin (m+1)) =>
            t ⊆ N ∧ G.IsClique (t : Set (Fin (m+1)))) q →
          (∃ x ∈ q, x ∈ A) ∨ ∃ x ∈ q, ∃ y ∈ q, R.Adj x y) →
  G.cliqueTransversalNumber ≤ (m+1) - Erdos151.H (m+1)

/-- A finite local assertion. Only edges inside the at most nine vertices of N
matter. I is a choice of eight or more nonisolated vertices. The second and third
clauses select a pair in a blocked link and bound each exterior guard, using at most ten link vertices. -/
def H3 : Prop := (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (N I : Finset (Fin n)),
  N.card ≤ 9 → I ⊆ N → 8 ≤ I.card → (∀ x ∈ I, ∃ y ∈ N, G.Adj x y) →
  let Guard := fun D : Finset (Fin n) => D ⊆ N ∧
    ∀ q : Finset (Fin n), q.Nonempty →
      Maximal (fun t : Finset (Fin n) => t ⊆ N ∧ G.IsClique (t : Set (Fin n))) q →
      ∃ x ∈ q, x ∈ D
  (∃ D, Guard D ∧ D.card ≤ 5) ∨
    ((∀ a ∈ N, ∀ b ∈ N, a ≠ b → ∃ D, Guard D ∧ D.card ≤ 6 ∧ a ∈ D ∧ b ∈ D) ∧
     ∀ X ⊆ I, G.IsClique (X : Set (Fin n)) →
       ∃ x ∈ I, x ∉ X ∧ ∃ y ∈ I, y ∉ X ∧ x ≠ y ∧ ¬ G.Adj x y ∧
         ∃ a ∈ N, G.Adj x a ∧ G.Adj y a))  ∧
  (∀ (n : ℕ) (G R : SimpleGraph (Fin n)) (W N : Finset (Fin n)),
    W ⊆ N → N.card ≤ 10 → R ≤ G → R.CliqueFree 3 →
    (¬ ∃ A ⊆ W, R.IsIndepSet (A : Set (Fin n)) ∧
      ∀ q : Finset (Fin n), q.Nonempty →
        Maximal (fun t : Finset (Fin n) => t ⊆ W ∧ G.IsClique (t : Set (Fin n))) q →
        (∃ x ∈ q, x ∈ A) ∨ ∃ x ∈ q, ∃ y ∈ q, R.Adj x y) →
    let p := (N.filter fun a => ∃ b ∈ N, G.Adj a b).card
    let k := fun a => (N.filter (G.Adj a)).card
    let cost := fun a => if 4 ≤ k a then 3 else if 3 ≤ k a ∨ 9 ≤ p then 4 else 5
    ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧ ¬ G.Adj x y ∧ 2 ≤ k x ∧ 2 ≤ k y ∧
      cost x + cost y ≤ 8) ∧
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (N : Finset (Fin n)) (v : Fin n) (p : ℕ),
    N.card ≤ 10 → v ∈ N → 8 ≤ p → p ≤ (N.filter fun a => ∃ b ∈ N, G.Adj a b).card →
    let k := (N.filter (G.Adj v)).card
    2 ≤ k →
    ∃ D ⊆ (N.erase v).filter (fun z => ¬ G.Adj v z),
      D.card ≤ (if 4 ≤ k then 3 else if 3 ≤ k ∨ 9 ≤ p then 4 else 5) ∧
      ∀ q : Finset (Fin n), q.Nonempty →
        Maximal (fun t : Finset (Fin n) => t ⊆ N ∧ G.IsClique (t : Set (Fin n))) q →
          ∃ z ∈ q, z ∈ D ∨ G.Adj v z)


/-- Ramsey inputs: R(3,8) is at most 28, and Exoo's 39-vertex graph has
independence number nine. Exoo also gives 46 vertices of independence
number ten. Restriction gives the displayed inequalities. -/
def H4 : Prop := (∀ m, 28 ≤ m → 8 ≤ Erdos151.H m) ∧
  (∀ m, Erdos151.H m = 10 → 40 ≤ m) ∧ (∀ m, Erdos151.H m = 11 → 47 ≤ m)


/- The following Ramsey and deletion lemmas are reproduced from reduction R2. -/

lemma H_attained {n : ℕ} (F : SimpleGraph (Fin n)) (hF : F.CliqueFree 3) :
    ∃ s, F.IsNIndepSet (Erdos151.H n) s := by
  let sizes : Set ℕ :=
    {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s}
  have hnonempty : sizes.Nonempty :=
    ⟨0, fun _ _ => ⟨∅, by simp [SimpleGraph.isNIndepSet_iff]⟩⟩
  have hfinite : sizes.Finite := by
    refine (Set.finite_Iic n).subset ?_
    intro k hk
    obtain ⟨s, hs⟩ := hk F hF
    simpa [hs.card_eq] using Finset.card_le_univ s
  exact (hnonempty.csSup_mem hfinite) F hF

lemma H_le (n : ℕ) : Erdos151.H n ≤ n := by
  obtain ⟨s, hs⟩ := H_attained (⊥ : SimpleGraph (Fin n)) (cliqueFree_bot (by norm_num))
  simpa [hs.card_eq] using Finset.card_le_univ s

/-- Any vertex neighborhood misses every maximal clique, bounding `τ(G)` by `n - deg(v)`. -/
lemma neighborhood_bound {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (hv : Erdos151.H n ≤ (univ.filter (G.Adj v)).card) :
    cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  let N := univ.filter (G.Adj v)
  have hhit : G.IsCliqueTransversal Nᶜ := by
    intro t ht
    by_contra! h
    have hAdj (w : Fin n) (hw : w ∈ t) : G.Adj v w :=
      (mem_filter.mp (not_not.mp (by simpa only [mem_compl] using h w hw))).2
    have hc : G.IsClique (↑(insert v t) : Set (Fin n)) := by
      rw [coe_insert]
      exact ht.1.1.insert (fun w hw _ => hAdj w hw)
    have hv' : v ∈ t := ht.1.2 hc (subset_insert _ _) (mem_insert_self _ _)
    exact G.irrefl (hAdj v hv')
  refine (csInf_le' (show Nᶜ.card ∈ {k | ∃ T, G.IsCliqueTransversal T ∧ T.card = k}
    from ⟨Nᶜ, hhit, rfl⟩)).trans ?_
  rw [card_compl, Fintype.card_fin]
  exact Nat.sub_le_sub_left hv n

/-- Any triangle-free graph `F` with an edge inside every big maximal clique of `G` yields the bound. -/
lemma bound_of_hitting {n : ℕ} (G F : SimpleGraph (Fin n)) (hF : F.CliqueFree 3)
    (hit : ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v) :
    cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  obtain ⟨s, hs⟩ := H_attained F hF
  have htransversal : G.IsCliqueTransversal sᶜ := by
    intro t ht
    obtain ⟨u, hu, v, hv, huv⟩ := hit t ht
    by_cases hsu : u ∈ s
    · by_cases hsv : v ∈ s
      · exact (hs.isIndepSet hsu hsv huv.ne huv).elim
      · exact ⟨v, hv, mem_compl.mpr hsv⟩
    · exact ⟨u, hu, mem_compl.mpr hsu⟩
  apply csInf_le'
  exact ⟨sᶜ, htransversal, by rw [card_compl, Fintype.card_fin, hs.card_eq]⟩

lemma pullback_big_clique {m n : ℕ} (G : SimpleGraph (Fin n)) (e : Fin m ↪ Fin n)
    (t : Finset (Fin n)) (ht : G.IsBigMaximalClique t)
    (hr : ∀ x ∈ t, ∃ i, e i = x) :
    (G.comap e).IsBigMaximalClique (t.preimage e e.injective.injOn) := by
  let u := t.preimage e e.injective.injOn
  have heq : u.map e = t := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
      exact mem_preimage.mp hi
    · intro hx
      obtain ⟨i, rfl⟩ := hr x hx
      exact mem_map.mpr ⟨i, mem_preimage.mpr hx, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi j hj hij
    exact ht.1.1 (mem_preimage.mp hi) (mem_preimage.mp hj) (e.injective.ne hij)
  · intro w hw huw j hj
    have hc : G.IsClique (↑(w.map e) : Set (Fin n)) := by
      intro x hx y hy hxy
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
      obtain ⟨k, hk, rfl⟩ := mem_map.mp hy
      exact hw hi hk (fun h => hxy (congrArg e h))
    have hsub : t ⊆ w.map e := by
      rw [← heq]
      exact map_subset_map.mpr huw
    exact mem_preimage.mpr (ht.1.2 hc hsub (mem_map.mpr ⟨j, hj, rfl⟩))
  · have h := ht.2
    rwa [← heq, card_map] at h

/-- Guarded-block deletion inequality for arbitrary graphs. -/
lemma delete_block {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hAB : A ⊆ B)
    (guarded : ∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A)
    (e : Fin (n - B.card) ↪ Fin n)
    (cover : ∀ x, x ∉ B → ∃ i, e i = x) :
    G.cliqueTransversalNumber ≤ (G.comap e).cliqueTransversalNumber + (B.card - A.card) := by
  let F := G.comap e
  have hn : {k | ∃ T : Finset (Fin (n - B.card)), F.IsCliqueTransversal T ∧ T.card = k}.Nonempty := by
    refine ⟨univ.card, univ, ?_, rfl⟩
    intro t ht
    obtain ⟨x, _, hx, _, _⟩ := one_lt_card_iff.mp ht.2
    exact ⟨x, hx, mem_univ _⟩
  obtain ⟨T, hT, hsize⟩ := Nat.sInf_mem hn
  change T.card = F.cliqueTransversalNumber at hsize
  let U := T.map e ∪ (B \ A)
  have hU : G.IsCliqueTransversal U := by
    intro t ht
    by_cases hhit : ∃ y ∈ t, y ∈ B \ A
    · obtain ⟨y, hy, hmem⟩ := hhit
      exact ⟨y, hy, mem_union_right _ hmem⟩
    have hout (x) (hx : x ∈ t) : x ∉ B := by
      intro hb
      by_cases ha : x ∈ A
      · exact hhit (guarded t ht ⟨x, hx, ha⟩)
      · exact hhit ⟨x, hx, mem_sdiff.mpr ⟨hb, ha⟩⟩
    have hbig := pullback_big_clique G e t ht (fun x hx => cover x (hout x hx))
    obtain ⟨i, hi, hiT⟩ := hT _ hbig
    exact ⟨e i, mem_preimage.mp hi, mem_union_left _ (mem_map.mpr ⟨i, hiT, rfl⟩)⟩
  calc
    G.cliqueTransversalNumber ≤ U.card := csInf_le' ⟨U, hU, rfl⟩
    _ ≤ (T.map e).card + (B \ A).card := card_union_le _ _
    _ = _ := by rw [card_map, card_sdiff_of_subset hAB, hsize]


/-- A maximal clique through v restricts to a maximal clique of its link. -/
lemma erase_in_link {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (U q : Finset V) (v : V) (hv : v ∈ q) (hq : G.IsBigMaximalClique q) (hU : q ⊆ U) :
    (q.erase v).Nonempty ∧
    Maximal (fun t : Finset V => t ⊆ U.filter (G.Adj v) ∧ G.IsClique (t : Set V))
      (q.erase v) := by
  classical
  have hc := hq.2
  refine ⟨card_pos.mp (by rw [card_erase_of_mem hv]; omega), ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro x hx
    obtain ⟨hxv, hxq⟩ := mem_erase.mp hx
    exact mem_filter.mpr ⟨hU hxq, hq.1.1 hv hxq hxv.symm⟩
  · intro x hx y hy hxy
    exact hq.1.1 (mem_of_mem_erase hx) (mem_of_mem_erase hy) hxy
  · intro t ht hqt
    have hcl : G.IsClique (↑(insert v t) : Set V) := by
      rw [coe_insert]
      exact ht.2.insert (fun x hx _ => (mem_filter.mp (ht.1 hx)).2)
    have hsub : q ⊆ insert v t := by
      intro x hx
      by_cases he : x = v
      · exact mem_insert.mpr (Or.inl he)
      · exact mem_insert_of_mem (hqt (mem_erase.mpr ⟨he,hx⟩))
    intro x hx
    exact mem_erase.mpr ⟨(mem_filter.mp (ht.1 hx)).2.ne.symm,
      hq.1.2 hcl hsub (mem_insert_of_mem hx)⟩

/-- Add a star over v. Its leaves are independent in the old red graph. -/
lemma extend_star {V : Type} [DecidableEq V] (G R : SimpleGraph V) (U : Finset V)
    (v : V) (hv : v ∈ U) (A : Finset V) (hA : A ⊆ U.filter (G.Adj v))
    (indep : R.IsIndepSet (A : Set V)) (sub : R ≤ G) (tf : R.CliqueFree 3)
    (supp : ∀ ⦃x y⦄, R.Adj x y → x ∈ U.erase v ∧ y ∈ U.erase v)
    (hit : ∀ q, G.IsBigMaximalClique q → q ⊆ U.erase v → ∃ x ∈ q, ∃ y ∈ q, R.Adj x y)
    (link : ∀ q : Finset V, q.Nonempty →
      Maximal (fun t : Finset V => t ⊆ U.filter (G.Adj v) ∧ G.IsClique (t : Set V)) q →
        (∃ x ∈ q, x ∈ A) ∨ ∃ x ∈ q, ∃ y ∈ q, R.Adj x y) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.CliqueFree 3 ∧
      (∀ ⦃x y⦄, F.Adj x y → x ∈ U ∧ y ∈ U) ∧
      ∀ q, G.IsBigMaximalClique q → q ⊆ U → ∃ x ∈ q, ∃ y ∈ q, F.Adj x y := by
  classical
  have hN {x} (hx : x ∈ A) := (mem_filter.mp (hA hx)).2
  have hsU {x} (hx : x ∈ A) := (mem_filter.mp (hA hx)).1
  have hvA : v ∉ A := fun h => G.irrefl (hN h)
  let F : SimpleGraph V := {
    Adj := fun x y => R.Adj x y ∨ (x = v ∧ y ∈ A) ∨ (y = v ∧ x ∈ A)
    symm := ⟨fun _ _ e => e.elim (fun h => Or.inl h.symm)
      (fun h => Or.inr h.symm)⟩
    loopless := ⟨by
      intro x h
      rcases h with h | ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · exact R.irrefl h
      · exact hvA ha
      · exact hvA ha⟩
  }
  have old {x y} (hx : x ≠ v) (hy : y ≠ v) (exy : F.Adj x y) : R.Adj x y :=
    exy.resolve_right (fun h => h.elim (fun e => hx e.1) (fun e => hy e.1))
  have leaf {y} (e : F.Adj v y) : y ∈ A := by
    rcases e with e | ⟨_, ha⟩ | ⟨_, ha⟩
    · exact (notMem_erase v U (supp e).1).elim
    · exact ha
    · exact (hvA ha).elim
  have no_at {x y} (hx : F.Adj v x) (hy : F.Adj v y) (e : F.Adj x y) : False :=
    indep (leaf hx) (leaf hy) e.ne (old hx.ne.symm hy.ne.symm e)
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro x y e
    rcases e with e | ⟨rfl, ha⟩ | ⟨rfl, ha⟩
    · exact sub e
    · exact hN ha
    · exact (hN ha).symm
  · intro t ht
    obtain ⟨x,y,z,exy,exz,eyz,_⟩ := is3Clique_iff.mp ht
    by_cases hx : x = v
    · subst x; exact no_at exy exz eyz
    by_cases hy : y = v
    · subst y; exact no_at exy.symm eyz exz
    by_cases hz : z = v
    · subst z; exact no_at exz.symm eyz.symm exy
    exact tf _ (is3Clique_triple_iff.mpr ⟨old hx hy exy,old hx hz exz,old hy hz eyz⟩)
  · intro x y e
    rcases e with e | ⟨rfl, ha⟩ | ⟨rfl, ha⟩
    · exact ⟨mem_of_mem_erase (supp e).1, mem_of_mem_erase (supp e).2⟩
    · exact ⟨hv, hsU ha⟩
    · exact ⟨hsU ha, hv⟩
  · intro q hq hqU
    by_cases hvq : v ∈ q
    · obtain ⟨hne, hmax⟩ := erase_in_link G U q v hvq hq hqU
      rcases link (q.erase v) hne hmax with ⟨x,hx,ha⟩ | ⟨x,hx,y,hy,e⟩
      · exact ⟨v,hvq,x,mem_of_mem_erase hx,Or.inr (Or.inl ⟨rfl,ha⟩)⟩
      · exact ⟨x,mem_of_mem_erase hx,y,mem_of_mem_erase hy,Or.inl e⟩
    · obtain ⟨x,hx,y,hy,e⟩ := hit q hq (fun z hz =>
        mem_erase.mpr ⟨fun h => hvq (h ▸ hz), hqU hz⟩)
      exact ⟨x,hx,y,hy,Or.inl e⟩

/-- A least vertex set with no partial solution supplies a bad link at every vertex. -/
lemma obstructed_links {n : ℕ} (G : SimpleGraph (Fin n))
    (nohit : ¬ ∃ F : SimpleGraph (Fin n), F.CliqueFree 3 ∧
      ∀ q, G.IsBigMaximalClique q → ∃ x ∈ q, ∃ y ∈ q, F.Adj x y) :
    ∃ U : Finset (Fin n), U.Nonempty ∧ ∀ v ∈ U,
      let N := U.filter (G.Adj v)
      ∃ R : SimpleGraph (Fin n), R ≤ G ∧ R.CliqueFree 3 ∧
        ¬ ∃ A ⊆ N, R.IsIndepSet (A : Set (Fin n)) ∧
          ∀ q : Finset (Fin n), q.Nonempty →
            Maximal (fun t : Finset (Fin n) => t ⊆ N ∧ G.IsClique (t : Set (Fin n))) q →
            (∃ x ∈ q, x ∈ A) ∨ ∃ x ∈ q, ∃ y ∈ q, R.Adj x y := by
  classical
  let Good (U : Finset (Fin n)) : Prop := ∃ R : SimpleGraph (Fin n), R ≤ G ∧ R.CliqueFree 3 ∧
    (∀ ⦃x y⦄, R.Adj x y → x ∈ U ∧ y ∈ U) ∧
    ∀ q, G.IsBigMaximalClique q → q ⊆ U → ∃ x ∈ q, ∃ y ∈ q, R.Adj x y
  have hbad : ¬ Good univ := by
    rintro ⟨R,_,ht,_,hit⟩
    exact nohit ⟨R,ht,fun q hq => hit q hq (subset_univ _)⟩
  have hex : ∃ k, ∃ U : Finset (Fin n), U.card = k ∧ ¬ Good U := ⟨_,univ,rfl,hbad⟩
  obtain ⟨U, hu, bad⟩ := Nat.find_spec hex
  have hnon : U.Nonempty := by
    by_contra! he
    have hU : U = ∅ := by simpa using he
    apply bad
    refine ⟨⊥, bot_le, cliqueFree_bot (by norm_num), by simp, ?_⟩
    intro q hq hqU
    have hq0 : q = ∅ := by simpa [hU] using hqU
    have := hq.2
    simp [hq0] at this
  refine ⟨U,hnon,?_⟩
  intro v hv N
  have hsm : Good (U.erase v) := by
    by_contra h
    have hm := Nat.find_min' hex (show ∃ T : Finset (Fin n),
      T.card = (U.erase v).card ∧ ¬ Good T from ⟨_,rfl,h⟩)
    have he := Finset.card_erase_lt_of_mem hv
    omega
  obtain ⟨R,sub,tf,supp,hit⟩ := hsm
  have blocked : ¬ ∃ A ⊆ N, R.IsIndepSet (A : Set (Fin n)) ∧
        ∀ q : Finset (Fin n), q.Nonempty →
          Maximal (fun t : Finset (Fin n) => t ⊆ N ∧ G.IsClique (t : Set (Fin n))) q →
          (∃ x ∈ q, x ∈ A) ∨ ∃ x ∈ q, ∃ y ∈ q, R.Adj x y := by
    rintro ⟨A,hA,hi,hl⟩
    exact bad (extend_star G R U v hv A hA hi sub tf supp hit hl)
  exact ⟨R, sub, tf, blocked⟩

/-- A least vertex set with no partial solution supplies a bad link at every vertex. -/
lemma bad_core (hsmall : H1) {n : ℕ} (G : SimpleGraph (Fin n))
    (nohit : ¬ ∃ F : SimpleGraph (Fin n), F.CliqueFree 3 ∧
      ∀ q, G.IsBigMaximalClique q → ∃ x ∈ q, ∃ y ∈ q, F.Adj x y) :
    ∃ U : Finset (Fin n), U.Nonempty ∧ ∀ v ∈ U,
      let N := U.filter (G.Adj v)
      8 ≤ (N.filter fun x => ∃ y ∈ N, G.Adj x y).card ∧
      ∃ R : SimpleGraph (Fin n), R ≤ G ∧ R.CliqueFree 3 ∧
        ¬ ∃ A ⊆ N, R.IsIndepSet (A : Set (Fin n)) ∧
          ∀ q : Finset (Fin n), q.Nonempty →
            Maximal (fun t : Finset (Fin n) => t ⊆ N ∧ G.IsClique (t : Set (Fin n))) q →
            (∃ x ∈ q, x ∈ A) ∨ ∃ x ∈ q, ∃ y ∈ q, R.Adj x y := by
  obtain ⟨U, ne, core⟩ := obstructed_links G nohit
  refine ⟨U, ne, ?_⟩
  intro v hv N
  obtain ⟨R, sub, tf, blocked⟩ := core v hv
  refine ⟨?_, R, sub, tf, blocked⟩
  by_contra! small
  exact blocked (hsmall n G R N sub tf (by omega))

/-- Complementing an open neighborhood gives a transversal of this exact size. -/
lemma bound_by_degree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    G.cliqueTransversalNumber ≤ n - (univ.filter (G.Adj v)).card := by
  classical
  let N := univ.filter (G.Adj v)
  have hhit : G.IsCliqueTransversal Nᶜ := by
    intro t ht
    by_contra! h
    have hAdj (w : Fin n) (hw : w ∈ t) : G.Adj v w :=
      (mem_filter.mp (not_not.mp (by simpa only [mem_compl] using h w hw))).2
    have hc : G.IsClique (↑(insert v t) : Set (Fin n)) := by
      rw [coe_insert]
      exact ht.1.1.insert (fun w hw _ => hAdj w hw)
    have hv : v ∈ t := ht.1.2 hc (subset_insert _ _) (mem_insert_self _ _)
    exact G.irrefl (hAdj v hv)
  exact csInf_le' ⟨Nᶜ, hhit, by rw [card_compl, Fintype.card_fin]⟩

/-- The seven-vertex extension calculation suffices for a free eight-set
as soon as the triangle-free Ramsey bound guarantees an independent eight-set. -/
lemma bound_eight (hsmall : H1) {n : ℕ} (G : SimpleGraph (Fin n))
    (hRam : 8 ≤ Erdos151.H n) : G.cliqueTransversalNumber ≤ n - 8 := by
  classical
  by_cases hit : ∃ F : SimpleGraph (Fin n), F.CliqueFree 3 ∧
      ∀ q, G.IsBigMaximalClique q → ∃ x ∈ q, ∃ y ∈ q, F.Adj x y
  · obtain ⟨F, tf, meets⟩ := hit
    exact (bound_of_hitting G F tf meets).trans (Nat.sub_le_sub_left hRam n)
  obtain ⟨U, nonempty, core⟩ := bad_core hsmall G hit
  obtain ⟨v, hv⟩ := nonempty
  have eight := (core v hv).1
  have sub : ((U.filter (G.Adj v)).filter
      fun x => ∃ y ∈ U.filter (G.Adj v), G.Adj x y) ⊆ univ.filter (G.Adj v) := by
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (mem_filter.mp hx).1).2⟩
  exact (bound_by_degree G v).trans (Nat.sub_le_sub_left (eight.trans (card_le_card sub)) n)

/-- If two nonadjacent centers have guards with small union, the rest contains
eight free vertices, which can be combined with the two centers. -/
lemma two_guards (hsmall : H1) (hRam : ∀ m, 28 ≤ m → 8 ≤ Erdos151.H m)
    {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 40 ≤ n) {x y : Fin n}
    (hne : x ≠ y) (hxy : ¬ G.Adj x y) {D E : Finset (Fin n)}
    (hD : D ⊆ univ.filter (G.Adj x)) (hE : E ⊆ univ.filter (G.Adj y))
    (gx : ∀ t, G.IsBigMaximalClique t → x ∈ t → ∃ z ∈ t, z ∈ D)
    (gy : ∀ t, G.IsBigMaximalClique t → y ∈ t → ∃ z ∈ t, z ∈ E)
    (price : (D ∪ E).card ≤ 10) : G.cliqueTransversalNumber ≤ n - 10 := by
  classical
  let A : Finset (Fin n) := {x,y}
  let B := A ∪ (D ∪ E)
  have ca : A.card = 2 := by simp [A, hne]
  have hab : A ⊆ B := subset_union_left
  have cb : B.card ≤ 12 := by
    have h := card_union_le A (D ∪ E)
    change (A ∪ (D ∪ E)).card ≤ 12
    omega
  have avoid (z) (hz : z ∈ D ∪ E) : z ∉ A := by
    rcases mem_union.mp hz with hz | hz
    · have e := (mem_filter.mp (hD hz)).2
      intro h
      rcases mem_insert.mp h with rfl | h
      · exact G.irrefl e
      · rw [mem_singleton.mp h] at e
        exact hxy e
    · have e := (mem_filter.mp (hE hz)).2
      intro h
      rcases mem_insert.mp h with rfl | h
      · exact hxy e.symm
      · rw [mem_singleton.mp h] at e
        exact G.irrefl e
  have guarded (t) (ht : G.IsBigMaximalClique t) (meet : ∃ z ∈ t, z ∈ A) :
      ∃ z ∈ t, z ∈ B \ A := by
    obtain ⟨z, htZ, hz⟩ := meet
    have hit : ∃ w ∈ t, w ∈ D ∪ E := by
      rcases mem_insert.mp hz with rfl | hz
      · obtain ⟨w, hw, hd⟩ := gx t ht htZ
        exact ⟨w, hw, mem_union_left _ hd⟩
      · rw [mem_singleton.mp hz] at htZ
        obtain ⟨w, hw, he⟩ := gy t ht htZ
        exact ⟨w, hw, mem_union_right _ he⟩
    obtain ⟨w, hw, hu⟩ := hit
    exact ⟨w, hw, mem_sdiff.mpr ⟨mem_union_right _ hu, avoid w hu⟩⟩
  let W := Bᶜ
  have hW : Fintype.card (↥W) = n - B.card := by simp [W]
  let f := Fintype.equivFinOfCardEq hW
  let e := f.symm.toEmbedding.trans (Function.Embedding.subtype (· ∈ W))
  have cover (z : Fin n) (hz : z ∉ B) : ∃ i, e i = z := by
    let a : ↥W := ⟨z, mem_compl.mpr hz⟩
    exact ⟨f a, by simp [e, a]⟩
  have d := delete_block G A B hab guarded e cover
  have r := bound_eight hsmall (G.comap e) (hRam _ (by omega))
  have lower := card_le_card hab
  calc
    G.cliqueTransversalNumber ≤ (G.comap e).cliqueTransversalNumber + (B.card - A.card) := d
    _ ≤ (n - B.card - 8) + (B.card - A.card) := Nat.add_le_add_right r _
    _ = n - 10 := by omega

/-- The unrestricted threshold-ten case follows from the two local finite
assertions and the classical Ramsey inputs. No residual jump hypothesis is used. -/
lemma threshold_ten (hsmall : H1) (classify : H3) (ram : H4) {n : ℕ}
    (G : SimpleGraph (Fin n)) (hTen : Erdos151.H n = 10) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  classical
  by_contra failed
  have hn := ram.2.1 n hTen
  have fail10 : ¬ G.cliqueTransversalNumber ≤ n - 10 := by simpa [hTen] using failed
  let N (v : Fin n) := univ.filter (G.Adj v)
  have deg (v) : (N v).card ≤ 9 := by
    by_contra! h
    exact failed (neighborhood_bound G v (by change Erdos151.H n ≤ (N v).card; omega))
  have nohit : ¬ ∃ F : SimpleGraph (Fin n), F.CliqueFree 3 ∧
      ∀ q, G.IsBigMaximalClique q → ∃ x ∈ q, ∃ y ∈ q, F.Adj x y :=
    fun ⟨F, ht, h⟩ => failed (bound_of_hitting G F ht h)
  obtain ⟨U, nonempty, core⟩ := bad_core hsmall G nohit
  let W (v : Fin n) := U.filter (G.Adj v)
  let I (v : Fin n) := (W v).filter fun x => ∃ y ∈ W v, G.Adj x y
  have wSub (v) : W v ⊆ N v := by
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩
  have iSub (v) : I v ⊆ W v := filter_subset _ _
  have inU (v) : I v ⊆ U := (iSub v).trans (filter_subset _ _)
  have inN (v) : I v ⊆ N v := (iSub v).trans (wSub v)
  have noniso (v) (x) (hx : x ∈ I v) : ∃ y ∈ N v, G.Adj x y := by
    obtain ⟨y, hy, e⟩ := (mem_filter.mp hx).2
    exact ⟨y, wSub v hy, e⟩
  have notClique : ¬ G.IsClique (U : Set (Fin n)) := by
    intro hc
    obtain ⟨v, hv⟩ := nonempty
    obtain ⟨eight, R, _, _, blocked⟩ := core v hv
    change 8 ≤ (I v).card at eight
    obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (I v).card by omega)
    have haw := iSub v ha
    apply blocked
    refine ⟨{a}, singleton_subset_iff.mpr haw, ?_, ?_⟩
    · intro i hi j hj hij
      have hi' : i = a := mem_singleton.mp hi
      have hj' : j = a := mem_singleton.mp hj
      exact (hij (hi'.trans hj'.symm)).elim
    · intro q _ hq
      have wc : G.IsClique (W v : Set (Fin n)) := fun i hi j hj h =>
        hc (mem_filter.mp hi).1 (mem_filter.mp hj).1 h
      have hs : W v ⊆ q := hq.2 ⟨Subset.rfl, wc⟩ hq.1.1
      exact Or.inl ⟨a, hs haw, mem_singleton_self _⟩
  let Guard (v : Fin n) (D : Finset (Fin n)) := D ⊆ N v ∧
    ∀ q : Finset (Fin n), q.Nonempty →
      Maximal (fun t : Finset (Fin n) => t ⊆ N v ∧ G.IsClique (t : Set (Fin n))) q →
      ∃ z ∈ q, z ∈ D
  have meets {v D} (h : Guard v D) (t) (ht : G.IsBigMaximalClique t) (hv : v ∈ t) :
      ∃ z ∈ t, z ∈ D := by
    obtain ⟨ne, mx⟩ := erase_in_link G univ t v hv ht (subset_univ _)
    obtain ⟨z, hz, hd⟩ := h.2 (t.erase v) ne mx
    exact ⟨z, mem_of_mem_erase hz, hd⟩
  have expensive {x y : Fin n} (hne : x ≠ y) (hxy : ¬ G.Adj x y) {D E}
      (hd : Guard x D) (he : Guard y E) : 10 < (D ∪ E).card := by
    by_contra! low
    exact fail10 (two_guards hsmall ram.1 G hn hne hxy hd.1 he.1 (meets hd) (meets he) low)
  let Cheap (v : Fin n) := ∃ D, Guard v D ∧ D.card ≤ 5
  have cheapClique {x y : Fin n} (hx : Cheap x) (hy : Cheap y) (hne : x ≠ y) :
      G.Adj x y := by
    by_contra hxy
    obtain ⟨D, hd, cd⟩ := hx
    obtain ⟨E, he, ce⟩ := hy
    have hp := expensive hne hxy hd he
    have hu := card_union_le D E
    omega
  obtain ⟨v, hv, ordinary⟩ : ∃ v ∈ U, ¬ Cheap v := by
    by_contra! allCheap
    exact notClique (fun x hx y hy hxy => cheapClique (allCheap x hx) (allCheap y hy) hxy)
  have localCase (z) (hz : z ∈ U) (h : ¬ Cheap z) :=
    (classify.1 n G (N z) (I z) (deg z) (inN z) (core z hz).1 (noniso z)).resolve_left h
  let X := (I v).filter Cheap
  have xc : G.IsClique (X : Set (Fin n)) := fun x hx y hy hxy =>
    cheapClique (mem_filter.mp hx).2 (mem_filter.mp hy).2 hxy
  obtain ⟨x, hxi, hxx, y, hyi, hyx, hne, hxy, a, ha, exa, eya⟩ :=
    (localCase v hv ordinary).2 X (filter_subset _ _) xc
  have xOrd : ¬ Cheap x := fun h => hxx (mem_filter.mpr ⟨hxi, h⟩)
  have yOrd : ¬ Cheap y := fun h => hyx (mem_filter.mpr ⟨hyi, h⟩)
  have xv : v ∈ N x := mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (inN v hxi)).2.symm⟩
  have yv : v ∈ N y := mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (inN v hyi)).2.symm⟩
  have va : v ≠ a := (mem_filter.mp ha).2.ne
  obtain ⟨D, hd, cd, dv, da⟩ := (localCase x (inU v hxi) xOrd).1 v xv a
    (mem_filter.mpr ⟨mem_univ _, exa⟩) va
  obtain ⟨E, he, ce, ev, ea⟩ := (localCase y (inU v hyi) yOrd).1 v yv a
    (mem_filter.mpr ⟨mem_univ _, eya⟩) va
  have sub : ({v,a} : Finset (Fin n)) ⊆ D ∩ E := by
    intro b hb
    rcases mem_insert.mp hb with rfl | hb
    · exact mem_inter.mpr ⟨dv, ev⟩
    · rw [mem_singleton.mp hb]
      exact mem_inter.mpr ⟨da, ea⟩
  have two := card_le_card sub
  rw [card_pair va] at two
  have sum := card_union_add_card_inter D E
  have hp := expensive hne hxy hd he
  omega



/-- Two nonadjacent nonisolated link vertices can both be retained at the hub. -/
lemma omit_link_pair {V : Type} [DecidableEq V] (G : SimpleGraph V)
    {N q : Finset V} {x y : V} (xy : ¬ G.Adj x y)
    (wx : ∃ z ∈ N, G.Adj x z) (wy : ∃ z ∈ N, G.Adj y z)
    (_ne : q.Nonempty)
    (hq : Maximal (fun t : Finset V => t ⊆ N ∧ G.IsClique (t : Set V)) q) :
    ∃ z ∈ q, z ≠ x ∧ z ≠ y := by
  classical
  by_contra! miss
  have choices (z) (hz : z ∈ q) : z = x ∨ z = y := or_iff_not_imp_left.mpr (miss z hz)
  have singleton_bad (a : V) (allEq : ∀ z ∈ q, z = a) (w : ∃ z ∈ N, G.Adj a z) : False := by
    obtain ⟨b, hb, ab⟩ := w
    have larger : G.IsClique (↑(insert b q) : Set V) := by
      rw [coe_insert]
      exact hq.1.2.insert (fun z hz _ => (allEq z hz) ▸ ab.symm)
    have inq := hq.2 ⟨insert_subset hb hq.1.1, larger⟩ (subset_insert _ _) (mem_insert_self _ _)
    exact ab.ne (allEq b inq).symm
  by_cases hx : x ∈ q
  · apply singleton_bad x _ wx
    intro z hz
    rcases choices z hz with e | rfl
    · exact e
    by_contra h
    exact xy (hq.1.2 hx hz (fun eq => h eq.symm))
  · apply singleton_bad y _ wy
    intro z hz
    exact (choices z hz).resolve_left (fun e => hx (e ▸ hz))

/-- A guarded set of three costs at most nineteen vertices, leaving a free eight-set. -/
lemma three_in_block (small : H1) (ram : ∀ m, 28 ≤ m → 8 ≤ Erdos151.H m)
    {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 47 ≤ n) (A B : Finset (Fin n))
    (ab : A ⊆ B) (a3 : A.card = 3) (b19 : B.card ≤ 19)
    (guarded : ∀ q, G.IsBigMaximalClique q → (∃ z ∈ q, z ∈ A) → ∃ z ∈ q, z ∈ B \ A) :
    G.cliqueTransversalNumber ≤ n - 11 := by
  classical
  let W := Bᶜ
  have hW : Fintype.card (↥W) = n - B.card := by simp [W]
  let f := Fintype.equivFinOfCardEq hW
  let e := f.symm.toEmbedding.trans (Function.Embedding.subtype (· ∈ W))
  have cover (z : Fin n) (hz : z ∉ B) : ∃ i, e i = z := by
    let a : ↥W := ⟨z, mem_compl.mpr hz⟩
    exact ⟨f a, by simp [e, a]⟩
  have d := delete_block G A B ab guarded e cover
  have r := bound_eight small (G.comap e) (ram _ (by omega))
  have lower := card_le_card ab
  omega

/-- The full threshold-eleven case uses a hub and two nonadjacent neighbors. -/
lemma threshold_eleven (small : H1) (localFacts : H3) (ram : H4) {n : ℕ}
    (G : SimpleGraph (Fin n)) (eleven : Erdos151.H n = 11) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  classical
  by_contra fail
  have hn := ram.2.2 n eleven
  let N (v : Fin n) := univ.filter (G.Adj v)
  let P (v : Fin n) := (N v).filter fun a => ∃ b ∈ N v, G.Adj a b
  have deg (v) : (N v).card ≤ 10 := by
    by_contra! h
    exact fail (neighborhood_bound G v (by change Erdos151.H n ≤ (N v).card; omega))
  have nohit : ¬ ∃ F : SimpleGraph (Fin n), F.CliqueFree 3 ∧
      ∀ q, G.IsBigMaximalClique q → ∃ x ∈ q, ∃ y ∈ q, F.Adj x y :=
    fun ⟨F, tf, hits⟩ => fail (bound_of_hitting G F tf hits)
  obtain ⟨U, nonempty, core⟩ := bad_core small G nohit
  obtain ⟨v, hv, minimum⟩ := U.exists_min_image (fun z => (P z).card) nonempty
  let W := U.filter (G.Adj v)
  have wsub : W ⊆ N v := by
    intro z hz
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hz).2⟩
  obtain ⟨size, R, sub, tf, blocked⟩ := core v hv
  have p8 : 8 ≤ (P v).card := size.trans (card_le_card (by
    intro z hz
    obtain ⟨hw, y, hy, edge⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨wsub hw, y, wsub hy, edge⟩))
  let k (a : Fin n) := ((N v).filter (G.Adj a)).card
  let cost (a : Fin n) := if 4 ≤ k a then 3 else if 3 ≤ k a ∨ 9 ≤ (P v).card then 4 else 5
  obtain ⟨x, hx, y, hy, distinct, xy, kx, ky, price⟩ :=
    localFacts.2.1 n G R W (N v) wsub (deg v) sub tf blocked
  change cost x + cost y ≤ 8 at price
  have wing (a : Fin n) (ha : a ∈ W) (ka : 2 ≤ k a) :
      ∃ D ⊆ ((N a).erase v).filter (fun z => ¬ G.Adj v z),
        D.card ≤ cost a ∧ ∀ q, G.IsBigMaximalClique q → a ∈ q →
          ∃ z ∈ q, z ≠ a ∧ (z ∈ D ∨ G.Adj v z) := by
    have va : v ∈ N a := mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2.symm⟩
    have swap : (N a).filter (G.Adj v) = (N v).filter (G.Adj a) := by
      ext z
      simp [N, and_comm]
    have localGuard := localFacts.2.2 n G (N a) v (P v).card (deg a) va p8
      (minimum a (mem_filter.mp ha).1)
    dsimp only at localGuard
    rw [swap] at localGuard
    obtain ⟨D, ds, cd, hit⟩ := localGuard ka
    refine ⟨D, ds, cd, ?_⟩
    intro q hq aq
    obtain ⟨hne, hmax⟩ := erase_in_link G univ q a aq hq (subset_univ _)
    obtain ⟨z, hz, gz⟩ := hit (q.erase a) hne hmax
    exact ⟨z, mem_of_mem_erase hz, (mem_erase.mp hz).1, gz⟩
  obtain ⟨D, ds, cd, hitx⟩ := wing x hx kx
  obtain ⟨E, es, ce, hity⟩ := wing y hy ky
  have vx := (mem_filter.mp hx).2
  have vy := (mem_filter.mp hy).2
  let A : Finset (Fin n) := {v,x,y}
  let B := insert v (N v ∪ (D ∪ E))
  have a3 : A.card = 3 := by simp [A, vx.ne, vy.ne, distinct]
  have ab : A ⊆ B := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact mem_insert_self _ _
    rcases mem_insert.mp hz with rfl | hz
    · exact mem_insert_of_mem (mem_union_left _ (wsub hx))
    rw [mem_singleton.mp hz]
    exact mem_insert_of_mem (mem_union_left _ (wsub hy))
  have b19 : B.card ≤ 19 := by
    have h := card_insert_le v (N v ∪ (D ∪ E))
    have u := card_union_le (N v) (D ∪ E)
    have t := card_union_le D E
    have dv := deg v
    change (insert v (N v ∪ (D ∪ E))).card ≤ 19
    omega
  have guarded (q) (hq : G.IsBigMaximalClique q) (meet : ∃ z ∈ q, z ∈ A) :
      ∃ z ∈ q, z ∈ B \ A := by
    have safe {z : Fin n} (zb : z ∈ B) (zv : z ≠ v) (zx : z ≠ x) (zy : z ≠ y) :
        z ∈ B \ A := mem_sdiff.mpr ⟨zb, by simp [A, zv, zx, zy]⟩
    have exterior {z : Fin n} (zd : z ∈ D ∪ E) : z ∈ B \ A := by
      have h : z ≠ v ∧ ¬ G.Adj v z := by
        rcases mem_union.mp zd with hd | he
        · exact ⟨(mem_erase.mp (mem_filter.mp (ds hd)).1).1, (mem_filter.mp (ds hd)).2⟩
        · exact ⟨(mem_erase.mp (mem_filter.mp (es he)).1).1, (mem_filter.mp (es he)).2⟩
      exact safe (mem_insert_of_mem (mem_union_right _ zd)) h.1
        (fun e => h.2 (e ▸ vx)) (fun e => h.2 (e ▸ vy))
    have inside {z : Fin n} (vz : G.Adj v z) (zx : z ≠ x) (zy : z ≠ y) :
        z ∈ B \ A := safe (mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,vz⟩)))
          vz.ne.symm zx zy
    obtain ⟨a, aq, ha⟩ := meet
    rcases mem_insert.mp ha with atHub | ha
    · rw [atHub] at aq
      obtain ⟨ne, mx⟩ := erase_in_link G univ q v aq hq (subset_univ _)
      have neighbor (b : Fin n) (kb : 2 ≤ k b) : ∃ z ∈ N v, G.Adj b z := by
        obtain ⟨z, hz⟩ := card_pos.mp (show 0 < ((N v).filter (G.Adj b)).card from
          lt_of_lt_of_le (by decide : 0 < 2) kb)
        exact ⟨z, (mem_filter.mp hz).1, (mem_filter.mp hz).2⟩
      obtain ⟨z, hz, zx, zy⟩ := omit_link_pair G xy (neighbor x kx) (neighbor y ky) ne mx
      exact ⟨z, mem_of_mem_erase hz, inside (mem_filter.mp (mx.1.1 hz)).2 zx zy⟩
    rcases mem_insert.mp ha with rfl | ha
    · obtain ⟨z, zq, zx, zd | zv⟩ := hitx q hq aq
      · exact ⟨z, zq, exterior (mem_union_left _ zd)⟩
      refine ⟨z, zq, inside zv zx ?_⟩
      rintro rfl
      exact xy (hq.1.1 aq zq distinct)
    rw [mem_singleton.mp ha] at aq
    obtain ⟨z, zq, zy, ze | zv⟩ := hity q hq aq
    · exact ⟨z, zq, exterior (mem_union_right _ ze)⟩
    refine ⟨z, zq, inside zv ?_ zy⟩
    rintro rfl
    exact xy (hq.1.1 zq aq distinct)
  exact fail (by simpa [eleven] using three_in_block small ram.1 G hn A B ab a3 b19 guarded)


/-- In a triangle, none of the three edges can be a newly added edge whose endpoints
had no common neighbor. -/
lemma old_triangle_side {V : Type} (G : SimpleGraph V) (u v : V)
    (apart : ¬ ∃ w, G.Adj u w ∧ G.Adj v w) {x y z : V}
    (xy : (G ⊔ edge u v).Adj x y) (xz : (G ⊔ edge u v).Adj x z)
    (yz : (G ⊔ edge u v).Adj y z) : G.Adj x y := by
  have xnz := xz.ne
  have ynz := yz.ne
  change G.Adj x y ∨ (edge u v).Adj x y at xy
  change G.Adj x z ∨ (edge u v).Adj x z at xz
  change G.Adj y z ∨ (edge u v).Adj y z at yz
  rcases xy with old | added
  · exact old
  rcases (edge_adj ..).mp added with ⟨h | h, _⟩
  · obtain ⟨rfl, rfl⟩ := h
    have ax : G.Adj x z := xz.resolve_right (by simp [edge_adj, Ne.symm xnz, Ne.symm ynz])
    have ay : G.Adj y z := yz.resolve_right (by simp [edge_adj, Ne.symm xnz, Ne.symm ynz])
    exact (apart ⟨z, ax, ay⟩).elim
  · obtain ⟨rfl, rfl⟩ := h
    have ax : G.Adj x z := xz.resolve_right (by simp [edge_adj, Ne.symm xnz, Ne.symm ynz])
    have ay : G.Adj y z := yz.resolve_right (by simp [edge_adj, Ne.symm xnz, Ne.symm ynz])
    exact (apart ⟨z, ay, ax⟩).elim

/-- Every graph has a spanning extension with the same triangles in which every
nonedge has a common neighbor. Every original big maximal clique is still maximal. -/
lemma saturate_triangles {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ F : SimpleGraph (Fin n), G ≤ F ∧
      (∀ ⦃x y z⦄, F.Adj x y → F.Adj x z → F.Adj y z → G.Adj x y) ∧
      (∀ t, G.IsBigMaximalClique t → F.IsBigMaximalClique t) ∧
      (∀ u v, u ≠ v → ¬ F.Adj u v → ∃ w, F.Adj u w ∧ F.Adj v w) := by
  let P (F : SimpleGraph (Fin n)) : Prop :=
    ∀ ⦃x y z⦄, F.Adj x y → F.Adj x z → F.Adj y z → G.Adj x y
  have base : P G := by
    intro x y z h _ _
    exact h
  obtain ⟨F, gf, best⟩ := Finite.exists_le_maximal base
  have old : P F := best.1
  refine ⟨F, gf, old, ?_, ?_⟩
  · intro t ht
    refine ⟨⟨ht.1.1.mono gf, ?_⟩, ht.2⟩
    intro s hs ts x hx
    by_contra xt
    have allAdj (y) (hy : y ∈ t) : G.Adj x y := by
      obtain ⟨a, b, ha, hb, ab⟩ := one_lt_card_iff.mp ht.2
      have third : ∃ z ∈ t, y ≠ z := by
        by_cases ya : y = a
        · exact ⟨b, hb, ya ▸ ab⟩
        · exact ⟨a, ha, ya⟩
      obtain ⟨z, hz, yz⟩ := third
      exact old (hs hx (ts hy) (fun h => xt (h ▸ hy)))
        (hs hx (ts hz) (fun h => xt (h ▸ hz))) (hs (ts hy) (ts hz) yz)
    have bigger : G.IsClique (↑(insert x t) : Set (Fin n)) := by
      rw [coe_insert]
      exact ht.1.1.insert (fun y hy _ => allAdj y hy)
    exact xt (ht.1.2 bigger (subset_insert _ _) (mem_insert_self _ _))
  · intro u v uv missing
    by_contra apart
    have extP : P (F ⊔ edge u v) := by
      intro x y z xy xz yz
      exact old (old_triangle_side F u v apart xy xz yz)
        (old_triangle_side F u v apart xz xy yz.symm)
        (old_triangle_side F u v apart yz xy.symm xz.symm)
    exact (lt_sup_edge F u v uv missing).not_ge (best.2 extP le_sup_left)

lemma transversal_mono_cliques {n : ℕ} (G F : SimpleGraph (Fin n))
    (keep : ∀ t, G.IsBigMaximalClique t → F.IsBigMaximalClique t) :
    G.cliqueTransversalNumber ≤ F.cliqueTransversalNumber := by
  have ex : {k | ∃ T : Finset (Fin n), F.IsCliqueTransversal T ∧ T.card = k}.Nonempty := by
    refine ⟨univ.card, univ, ?_, rfl⟩
    intro t ht
    obtain ⟨x, _, hx, _, _⟩ := one_lt_card_iff.mp ht.2
    exact ⟨x, hx, mem_univ _⟩
  obtain ⟨T, hits, size⟩ := Nat.sInf_mem ex
  exact csInf_le' ⟨T, (fun t ht => hits t (keep t ht)), size⟩

/-- Guard several vertices simultaneously. Each protected vertex has a neighbor
that extends every retained clique through it. The guards for different vertices
may coincide. -/
lemma common_neighbor_guards {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (A D : Finset V) (sep : Disjoint A D)
    (witness : ∀ x ∈ A, ∃ v, G.Adj v x ∧
      ∀ y, G.Adj x y → ¬ G.Adj v y → y ∈ D) :
    ∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ (A ∪ D) \ A := by
  intro t ht ⟨x, xt, xa⟩
  obtain ⟨v, vx, guard⟩ := witness x xa
  by_contra miss
  have extend (y) (yt : y ∈ t) : G.Adj v y := by
    by_cases eq : x = y
    · exact eq ▸ vx
    by_contra vy
    have yd := guard y (ht.1.1 xt yt eq) vy
    exact miss ⟨y, yt, mem_sdiff.mpr
      ⟨mem_union_right _ yd, fun ya => Finset.disjoint_left.mp sep ya yd⟩⟩
  have bigger : G.IsClique (↑(insert v t) : Set V) := by
    rw [coe_insert]
    exact ht.1.1.insert (fun y hy _ => extend y hy)
  have vt := ht.1.2 bigger (subset_insert _ _) (mem_insert_self _ _)
  exact G.irrefl (extend v vt)

/-- A big maximal clique escapes every open neighborhood. -/
lemma escapes_neighbor {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (v : V) (t : Finset V) (ht : G.IsBigMaximalClique t) :
    ∃ x ∈ t, ¬ G.Adj v x := by
  by_contra! allAdj
  have bigger : G.IsClique (↑(insert v t) : Set V) := by
    rw [coe_insert]
    exact ht.1.1.insert (fun x hx _ => allAdj x hx)
  exact G.irrefl (allAdj v (ht.1.2 bigger (subset_insert _ _) (mem_insert_self _ _)))

/-- Two neighborhoods may be kept together after covering the edges between their
exclusive parts. Vertices in their intersection may all be kept. -/
lemma union_of_two_neighbors {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
    (C : Finset (Fin n))
    (cover : ∀ x y, G.Adj u x → ¬ G.Adj v x → G.Adj v y → ¬ G.Adj u y →
      G.Adj x y → x ∈ C ∨ y ∈ C) :
    let S := univ.filter (fun x => (G.Adj u x ∨ G.Adj v x) ∧ x ∉ C)
    G.cliqueTransversalNumber ≤ n - S.card := by
  let S := univ.filter (fun x => (G.Adj u x ∨ G.Adj v x) ∧ x ∉ C)
  have hits : G.IsCliqueTransversal Sᶜ := by
    intro t ht
    by_contra! miss
    have inside (x) (hx : x ∈ t) : (G.Adj u x ∨ G.Adj v x) ∧ x ∉ C := by
      have hs : x ∈ S := by simpa using miss x hx
      exact (mem_filter.mp hs).2
    obtain ⟨x, xt, xv⟩ := escapes_neighbor G v t ht
    obtain ⟨y, yt, yu⟩ := escapes_neighbor G u t ht
    obtain ⟨xu, xc⟩ := inside x xt
    obtain ⟨yv, yc⟩ := inside y yt
    have xy : x ≠ y := fun eq => yu (eq ▸ xu.resolve_right xv)
    exact (cover x y (xu.resolve_right xv) xv (yv.resolve_left yu) yu (ht.1.1 xt yt xy)).elim xc yc
  have bound : G.cliqueTransversalNumber ≤ Sᶜ.card := csInf_le' ⟨Sᶜ, hits, rfl⟩
  rw [card_compl, Fintype.card_fin] at bound
  exact bound


/-- The degrees at an endpoint set bound its number of edge incidences.
An allowance of one extra incidence still gives Hall's inequality by parity. -/
lemma distinct_endpoints {V : Type} [Fintype V] (L : SimpleGraph V)
    (small : ∀ t : Finset V, ∑ x ∈ t, Nat.card (L.neighborSet x) ≤ t.card * 2 + 1) :
    ∃ f : L.edgeSet → V, Function.Injective f ∧ ∀ e, f e ∈ (e.val : Sym2 V) := by
  classical
  let ends (e : L.edgeSet) := e.val.toFinset
  have hall (s : Finset L.edgeSet) : s.card ≤ (s.biUnion ends).card := by
    let t := s.biUnion ends
    let inc (e : L.edgeSet) (x : V) := x ∈ ends e
    have two (e) (he : e ∈ s) : 2 ≤ (t.bipartiteAbove inc e).card := by
      have eq : t.bipartiteAbove inc e = ends e := by
        ext x
        exact ⟨fun h => (mem_filter.mp h).2,
          fun h => mem_filter.mpr ⟨mem_biUnion.mpr ⟨e, he, h⟩, h⟩⟩
      rw [eq]
      exact (Sym2.card_toFinset_of_not_isDiag _ (L.not_isDiag_of_mem_edgeSet e.property)).ge
    have atMost (x : V) (_ : x ∈ t) : (s.bipartiteBelow inc x).card ≤ L.degree x := by
      rw [← L.card_incidenceFinset_eq_degree]
      apply card_le_card_of_injOn Subtype.val _ Subtype.val_injective.injOn
      intro e he
      apply (L.mem_incidenceFinset x e.val).mpr
      exact ⟨e.property, Sym2.mem_toFinset.mp (mem_filter.mp he).2⟩
    have count : s.card * 2 ≤ t.card * 2 + 1 := calc
      s.card * 2 = ∑ _e ∈ s, 2 := by simp
      _ ≤ ∑ e ∈ s, (t.bipartiteAbove inc e).card := sum_le_sum two
      _ = ∑ x ∈ t, (s.bipartiteBelow inc x).card := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow inc
      _ ≤ ∑ x ∈ t, L.degree x := sum_le_sum atMost
      _ = ∑ x ∈ t, Nat.card (L.neighborSet x) := by
        simp only [Nat.card_eq_fintype_card, L.card_neighborSet_eq_degree]
      _ ≤ _ := small t
    change s.card ≤ t.card
    omega
  obtain ⟨f, inj, good⟩ := (all_card_le_biUnion_card_iff_existsInjective' ends).mp hall
  exact ⟨f, inj, fun e => Sym2.mem_toFinset.mp (good e)⟩

set_option maxHeartbeats 2500000 in
/-- A link with at most one incidence in excess of degree two extends every retained-edge choice.
The representative of a retained edge is left out. The representative of every
other edge and every isolated vertex can be included. -/
lemma sparse_link_extension {n : ℕ} (G R : SimpleGraph (Fin n)) (N : Finset (Fin n))
    (sub : R ≤ G) (small : ∑ x ∈ N, ((N.filter (G.Adj x)).card - 2) ≤ 1) :
    ∃ A ⊆ N, R.IsIndepSet (A : Set (Fin n)) ∧
      ∀ q : Finset (Fin n), q.Nonempty →
        Maximal (fun t : Finset (Fin n) => t ⊆ N ∧ G.IsClique (t : Set (Fin n))) q →
        (∃ x ∈ q, x ∈ A) ∨ ∃ x ∈ q, ∃ y ∈ q, R.Adj x y := by
  classical
  let L : SimpleGraph (Fin n) := {
    Adj := fun x y => x ∈ N ∧ y ∈ N ∧ G.Adj x y
    symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
    loopless := ⟨fun _ h => G.irrefl h.2.2⟩ }
  let cost (x : Fin n) := (N.filter (G.Adj x)).card - 2
  have deg (x : Fin n) : L.degree x ≤ 2 + (if x ∈ N then cost x else 0) := by
    rw [← L.card_neighborFinset_eq_degree]
    by_cases hx : x ∈ N
    · have incl : L.neighborFinset x ⊆ N.filter (G.Adj x) := by
        intro y hy
        have h : L.Adj x y := (L.mem_neighborFinset _ _).mp hy
        exact mem_filter.mpr ⟨h.2.1, h.2.2⟩
      have := card_le_card incl
      simp only [if_pos hx, cost]
      omega
    · have empty : L.neighborFinset x = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        have h : L.Adj x y := (L.mem_neighborFinset _ _).mp hy
        exact hx h.1
      simp [empty, hx]
  have budget (t : Finset (Fin n)) : ∑ x ∈ t, L.degree x ≤ t.card * 2 + 1 := calc
    _ ≤ ∑ x ∈ t, (2 + (if x ∈ N then cost x else 0)) := sum_le_sum fun x _ => deg x
    _ = t.card * 2 + ∑ x ∈ t.filter (· ∈ N), cost x := by simp [sum_add_distrib, sum_filter]
    _ ≤ t.card * 2 + ∑ x ∈ N, cost x := Nat.add_le_add_left (sum_le_sum_of_subset
      (show t.filter (· ∈ N) ⊆ N from fun _ h => (mem_filter.mp h).2)) _
    _ ≤ _ := Nat.add_le_add_left small _
  have sizes (t : Finset (Fin n)) : ∑ x ∈ t, Nat.card (L.neighborSet x) ≤ t.card * 2 + 1 := by
    simpa only [Nat.card_eq_fintype_card, L.card_neighborSet_eq_degree] using budget t
  obtain ⟨f, inj, endpoint⟩ := distinct_endpoints L sizes
  let A := N.filter (fun x => ¬ ∃ e : L.edgeSet, e.val ∈ R.edgeSet ∧ f e = x)
  refine ⟨A, filter_subset _ _, ?_, ?_⟩
  · intro x hx y hy _ red
    have lx : L.Adj x y := ⟨(mem_filter.mp hx).1, (mem_filter.mp hy).1, sub red⟩
    let e : L.edgeSet := ⟨s(x, y), lx⟩
    have ends : f e = x ∨ f e = y := Sym2.mem_iff.mp (endpoint e)
    rcases ends with left | right
    · exact (mem_filter.mp hx).2 ⟨e, red, left⟩
    · exact (mem_filter.mp hy).2 ⟨e, red, right⟩
  · intro q ne maximal
    obtain ⟨only, rfl⟩ | nontrivial := ne.exists_eq_singleton_or_nontrivial
    · left
      refine ⟨only, mem_singleton_self _, mem_filter.mpr ⟨maximal.1.1 (mem_singleton_self _), ?_⟩⟩
      rintro ⟨e, _, h⟩
      have oe : only ∈ e.val := h ▸ endpoint e
      let y := Sym2.Mem.other oe
      have ly : L.Adj only y := by
        apply L.mem_edgeSet.mp
        rw [show s(only, y) = e.val from Sym2.other_spec oe]
        exact e.property
      have cl : G.IsClique (({y, only} : Finset (Fin n)) : Set (Fin n)) := by
        rw [coe_insert, coe_singleton]
        exact isClique_pair.mpr (fun _ => ly.2.2.symm)
      have subN : insert y {only} ⊆ N := insert_subset ly.2.1 maximal.1.1
      have yo := maximal.2 ⟨subN, cl⟩ (subset_insert _ _) (mem_insert_self y _)
      exact ly.ne ((mem_singleton.mp yo).symm)
    · obtain ⟨x, xt, y, yt, xy⟩ := nontrivial
      by_cases red : R.Adj x y
      · exact Or.inr ⟨x, xt, y, yt, red⟩
      have lx : L.Adj x y := ⟨maximal.1.1 xt, maximal.1.1 yt, maximal.1.2 xt yt xy⟩
      let e : L.edgeSet := ⟨s(x, y), lx⟩
      have ends : f e = x ∨ f e = y := Sym2.mem_iff.mp (endpoint e)
      have inq : f e ∈ q := ends.elim (fun h => h ▸ xt) (fun h => h ▸ yt)
      refine Or.inl ⟨f e, inq, mem_filter.mpr ⟨maximal.1.1 inq, ?_⟩⟩
      rintro ⟨d, dr, same⟩
      have de := inj same
      subst d
      exact red dr


/-- Failure to extend through a vertex forces at least two incidences beyond
degree two in its internal link. -/
lemma link_excess_of_obstruction {n : ℕ} (G R : SimpleGraph (Fin n)) (N : Finset (Fin n))
    (sub : R ≤ G)
    (blocked : ¬ ∃ A ⊆ N, R.IsIndepSet (A : Set (Fin n)) ∧
      ∀ q : Finset (Fin n), q.Nonempty →
        Maximal (fun t : Finset (Fin n) => t ⊆ N ∧ G.IsClique (t : Set (Fin n))) q →
        (∃ x ∈ q, x ∈ A) ∨ ∃ x ∈ q, ∃ y ∈ q, R.Adj x y) :
    2 ≤ ∑ x ∈ N, ((N.filter (G.Adj x)).card - 2) := by
  by_contra! small
  exact blocked (sparse_link_extension G R N sub (by omega))

/-- Every counterexample to the triangle-free hitting construction has an induced
core with link excess at least two at every vertex. -/
lemma dense_triangle_core {n : ℕ} (G : SimpleGraph (Fin n))
    (nohit : ¬ ∃ F : SimpleGraph (Fin n), F.CliqueFree 3 ∧
      ∀ q, G.IsBigMaximalClique q → ∃ x ∈ q, ∃ y ∈ q, F.Adj x y) :
    ∃ U : Finset (Fin n), U.Nonempty ∧ ∀ v ∈ U,
      let N := U.filter (G.Adj v)
      2 ≤ ∑ x ∈ N, ((N.filter (G.Adj x)).card - 2) := by
  obtain ⟨U, ne, core⟩ := obstructed_links G nohit
  refine ⟨U, ne, ?_⟩
  intro v hv N
  obtain ⟨R, sub, _, blocked⟩ := core v hv
  exact link_excess_of_obstruction G R N sub blocked

/-- A removable vertex at every nonempty induced subgraph suffices. -/
theorem bound_of_peelable_triangle_links {n : ℕ} (G : SimpleGraph (Fin n))
    (peel : ∀ U : Finset (Fin n), U.Nonempty → ∃ v ∈ U,
      let N := U.filter (G.Adj v)
      ∑ x ∈ N, ((N.filter (G.Adj x)).card - 2) ≤ 1) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  by_cases good : ∃ F : SimpleGraph (Fin n), F.CliqueFree 3 ∧
      ∀ q, G.IsBigMaximalClique q → ∃ x ∈ q, ∃ y ∈ q, F.Adj x y
  · obtain ⟨F, tf, hits⟩ := good
    exact bound_of_hitting G F tf hits
  obtain ⟨U, ne, core⟩ := dense_triangle_core G good
  obtain ⟨v, hv, low⟩ := peel U ne
  exact (Nat.not_succ_le_self 1 ((core v hv).trans low)).elim

/-- An all-orders sufficient condition: at any vertex, the incident edges' total
excess above two triangles is at most one. -/
theorem bound_of_sparse_triangle_links {n : ℕ} (G : SimpleGraph (Fin n))
    (few : ∀ v, let N := univ.filter (G.Adj v)
      ∑ x ∈ N, ((N.filter (G.Adj x)).card - 2) ≤ 1) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  apply bound_of_peelable_triangle_links G
  intro U ne
  obtain ⟨v, hv⟩ := ne
  refine ⟨v, hv, ?_⟩
  let N := U.filter (G.Adj v)
  let W := univ.filter (G.Adj v)
  have incl : N ⊆ W := by
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩
  have cmp : ∑ x ∈ N, ((N.filter (G.Adj x)).card - 2) ≤
      ∑ x ∈ W, ((W.filter (G.Adj x)).card - 2) := calc
    _ ≤ ∑ x ∈ N, ((W.filter (G.Adj x)).card - 2) := sum_le_sum fun x _ =>
      Nat.sub_le_sub_right (card_le_card (filter_subset_filter _ incl)) _
    _ ≤ _ := sum_le_sum_of_subset incl
  have low := few v
  change ∑ x ∈ W, ((W.filter (G.Adj x)).card - 2) ≤ 1 at low
  exact cmp.trans low

/-- In particular, the original inequality holds at every Ramsey threshold
whenever each edge belongs to at most two triangles. -/
theorem bound_of_two_triangles_per_edge {n : ℕ} (G : SimpleGraph (Fin n))
    (few : ∀ v x, G.Adj v x → (univ.filter (fun y => G.Adj v y ∧ G.Adj x y)).card ≤ 2) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  apply bound_of_sparse_triangle_links G
  intro v N
  have allZero (x) (hx : x ∈ N) : (N.filter (G.Adj x)).card - 2 = 0 := by
    have eq : N.filter (G.Adj x) = univ.filter (fun y => G.Adj v y ∧ G.Adj x y) := by
      ext y
      simp [N]
    rw [eq]
    exact Nat.sub_eq_zero_of_le (few v x (mem_filter.mp hx).2)
  rw [sum_eq_zero allZero]
  decide

/-- The leaf characterization of a finite forest is used for the edges in at
least three triangles. An internal link at one of its leaves has at most one
incidence beyond degree two. -/
theorem bound_of_forest_three_triangle_edges {n : ℕ} (G : SimpleGraph (Fin n))
    (few : ∀ v x, G.Adj v x →
      ((univ.filter (G.Adj v)).filter (G.Adj x)).card ≤ 3)
    (forest : ∀ U : Finset (Fin n), U.Nonempty → ∃ v ∈ U,
      ((U.filter (G.Adj v)).filter (fun x =>
        3 ≤ ((univ.filter (G.Adj v)).filter (G.Adj x)).card)).card ≤ 1) :
    G.cliqueTransversalNumber ≤ n - Erdos151.H n := by
  apply bound_of_peelable_triangle_links G
  intro U ne
  obtain ⟨v, hv, leaf⟩ := forest U ne
  refine ⟨v, hv, ?_⟩
  let N := U.filter (G.Adj v)
  let W := univ.filter (G.Adj v)
  have incl : N ⊆ W := fun x hx => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩
  have costs (x) (hx : x ∈ N) : (N.filter (G.Adj x)).card - 2 ≤
      (if 3 ≤ (W.filter (G.Adj x)).card then 1 else 0) := by
    have cmp := card_le_card (filter_subset_filter (G.Adj x) incl)
    have cap : (W.filter (G.Adj x)).card ≤ 3 := few v x (mem_filter.mp hx).2
    split <;> omega
  calc
    ∑ x ∈ N, ((N.filter (G.Adj x)).card - 2) ≤
        ∑ x ∈ N, (if 3 ≤ (W.filter (G.Adj x)).card then 1 else 0) := sum_le_sum costs
    _ = (N.filter (fun x => 3 ≤ (W.filter (G.Adj x)).card)).card := by simp
    _ ≤ 1 := leaf


theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos151.erdos_151 := by
  intro h1 h2 h3 h4 m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro original
    obtain ⟨G, _, _, keeps, twoSteps⟩ := saturate_triangles original
    apply (transversal_mono_cliques original G keeps).trans
    rcases m with _ | n
    · have : cliqueTransversalNumber G ≤ 0 := by
        apply csInf_le'
        refine ⟨∅, ?_, rfl⟩
        intro s hs
        obtain ⟨a, -, -, -⟩ := one_lt_card_iff.mp hs.2
        exact a.elim0
      omega
    · by_cases hblock : ∃ A B : Finset (Fin (n + 1)), B.Nonempty ∧ A ⊆ B ∧
          (∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A) ∧
          Erdos151.H (n + 1) ≤ A.card + Erdos151.H (n + 1 - B.card)
      · obtain ⟨A, B, hB, hAB, hg, hgain⟩ := hblock
        have hb : B.card ≤ n + 1 := by simpa using card_le_univ B
        have ha := card_le_card hAB
        have hbpos := card_pos.mpr hB
        let W := Bᶜ
        have hW : Fintype.card (↥W) = n + 1 - B.card := by simp [W]
        let f := Fintype.equivFinOfCardEq hW
        let e := f.symm.toEmbedding.trans (Function.Embedding.subtype (· ∈ W))
        have hcover (x : Fin (n + 1)) (hx : x ∉ B) : ∃ i, e i = x := by
          let z : ↥W := ⟨x, mem_compl.mpr hx⟩
          exact ⟨f z, by simp [e, z]⟩
        have hsmall := ih (n + 1 - B.card) (by omega) (G.comap e)
        have hdelete := delete_block G A B hAB hg e hcover
        have hH := H_le (n + 1 - B.card)
        omega
      have hstrict : ∀ A B : Finset (Fin (n + 1)), B.Nonempty → A ⊆ B →
          (∀ t, G.IsBigMaximalClique t → (∃ x ∈ t, x ∈ A) → ∃ y ∈ t, y ∈ B \ A) →
          A.card + Erdos151.H (n + 1 - B.card) < Erdos151.H (n + 1) := by
        intro A B hb hab hg
        exact lt_of_not_ge (fun h => hblock ⟨A, B, hb, hab, hg, h⟩)
      have hjump : Erdos151.H n < Erdos151.H (n + 1) := by
        have h0 := hstrict ∅ {0} (singleton_nonempty 0) (empty_subset _)
          (fun _ _ ⟨_, _, hx⟩ => (notMem_empty _ hx).elim)
        simpa using h0
      by_cases hlarge : ∃ v, Erdos151.H (n + 1) ≤ (univ.filter (G.Adj v)).card
      · obtain ⟨v, hv⟩ := hlarge
        exact neighborhood_bound G v hv
      have hdeg (v : Fin (n + 1)) : (univ.filter (G.Adj v)).card < Erdos151.H (n + 1) :=
        lt_of_not_ge (fun h => hlarge ⟨v, h⟩)
      by_cases hgood : ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
          ∀ q, G.IsBigMaximalClique q → ∃ x ∈ q, ∃ y ∈ q, F.Adj x y
      · obtain ⟨F,ht,hit⟩ := hgood
        exact bound_of_hitting G F ht hit
      by_cases hten : Erdos151.H (n + 1) = 10
      · exact threshold_ten h1 h3 h4 G hten
      by_cases eleven : Erdos151.H (n + 1) = 11
      · exact threshold_eleven h1 h3 h4 G eleven
      by_contra fail
      apply fail
      apply h2 n G twoSteps ?_ hten eleven hjump hdeg hstrict ?_
      · intro u v C cover
        by_contra! large
        exact fail ((union_of_two_neighbors G u v C cover).trans (Nat.sub_le_sub_left large _))
      · obtain ⟨U, ne, core⟩ := bad_core h1 G hgood
        refine ⟨U, ne, ?_⟩
        intro v hv N
        obtain ⟨eight, R, sub, tf, blocked⟩ := core v hv
        exact ⟨eight, link_excess_of_obstruction G R N sub blocked, R, sub, tf, blocked⟩

end OMA.R_Erdos151_erdos_151_R3
