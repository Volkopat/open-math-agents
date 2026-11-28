import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H2_R1

-- Credit: @LordMike
-- Port of reductions/Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H1.R1.H2.R1.H2.R1.lean by its author onto the identical hypothesis statement Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H2.R1.H2.

/-! The degree-five case of the (3,8) Ramsey bound reduces to classifying
maximal triangle-free graphs on the 22 non-neighbors of the root. Adjacency
rows below encode just the vertices strictly following the current vertex:
bit zero is its immediate successor. The representatives are taken from the
McKay-Zhang catalogue, distributed by Brendan McKay under CC BY 4.0:
https://users.cecs.anu.edu.au/~bdm/data/ramsey.html .
The five contact rows must meet every independent six-set at least four times
in total across rows (at most one row may miss the six-set). Integer-weighted
tests exclude all possible rows in each of the intervals below. -/

/-! The neighborhood argument adapts @sturdy4days, open-math-agents PR #13293.
The row-degree identity is from RamseyDeficiency in the R(3,9) reduction. -/
namespace E151Rows
open Finset SimpleGraph
open scoped Classical

lemma lift_card {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hi : Gᶜ.CliqueFree 8) (S : Finset (Gᶜ.neighborFinset v))
    (cl : ((G.induce ((Gᶜ.neighborFinset v : Finset V) : Set V))ᶜ).IsClique S) :
    S.card ≤ 6 := by
  classical
  let B := Gᶜ.neighborFinset v
  let f : B ↪ V := Function.Embedding.subtype _
  have free : Gᶜ.IsClique (S.map f) := by
    intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact ⟨hxy,(cl ha hb (fun h => hxy (congrArg f h))).2⟩
  have hv : v ∉ S.map f := by
    intro hm
    obtain ⟨b,_,eq⟩ := mem_map.mp hm
    exact ((Gᶜ.mem_neighborFinset _ _).mp b.2).ne eq.symm
  have ext : Gᶜ.IsClique (insert v (S.map f)) := free.insert (by
    intro b hb _
    obtain ⟨i,_,rfl⟩ := mem_map.mp hb
    exact (Gᶜ.mem_neighborFinset _ _).mp i.2)
  have lim : (insert v (S.map f)).card < 8 := lt_of_not_ge (fun h =>
    hi.mono h _ ⟨by simpa only [Finset.coe_insert] using ext,rfl⟩)
  rw [card_insert_of_notMem hv,card_map] at lim
  omega

theorem neighborhood_data {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 8) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set V)
    let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
    D.CliqueFree 3 ∧ Dᶜ.CliqueFree 7 ∧
      (∀ i, Dᶜ.IsClique (A i)) ∧
      (∀ (J : Finset N) (S : Finset B), Dᶜ.IsClique S → (∀ a ∈ J, Disjoint (A a) S) → J.card+S.card≤7) := by
  classical
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set V)
  let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
  let f : B ↪ V := Function.Embedding.subtype _
  let g : N ↪ V := Function.Embedding.subtype _
  let em : D ↪g G := SimpleGraph.Embedding.comap f G
  have nd (a : N) := (G.mem_neighborFinset v a.val).mp a.2
  have bd (a : B) := (Gᶜ.mem_neighborFinset v a.val).mp a.2
  have split (a : N) (b : B) : a.val≠b.val := fun eq => (bd b).2 (eq ▸ nd a)
  have nr (a b : N) : ¬G.Adj a.val b.val := by
    intro h
    exact G.isIndepSet_neighborSet_of_triangleFree ht v (nd a) (nd b) h.ne h
  change D.CliqueFree 3 ∧ Dᶜ.CliqueFree 7 ∧ (∀ i, Dᶜ.IsClique (A i)) ∧ _
  refine ⟨CliqueFree.comap em.isContained ht,?_,?_,?_⟩
  · intro S hS
    have h := lift_card G v hi S hS.isClique
    have eq := hS.card_eq
    omega
  · intro i a ha b hb hne
    refine ⟨hne,?_⟩
    intro h
    exact G.isIndepSet_neighborSet_of_triangleFree ht i.val (mem_filter.mp ha).2 (mem_filter.mp hb).2
      (Subtype.val_injective.ne hne) h
  · intro J S cl dis
    let X := J.map g
    let Y := S.map f
    have apart : Disjoint X Y := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨a,_,rfl⟩ := mem_map.mp hx
      obtain ⟨b,_,eq⟩ := mem_map.mp hy
      exact split a b eq.symm
    have sx : Gᶜ.IsClique X := by
      intro u hu w hw hne
      obtain ⟨a,_,rfl⟩ := mem_map.mp hu
      obtain ⟨b,_,rfl⟩ := mem_map.mp hw
      exact ⟨hne,nr a b⟩
    have sy : Gᶜ.IsClique Y := by
      intro u hu w hw hne
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
      exact ⟨hne,(cl ha hb (fun h => hne (congrArg f h))).2⟩
    have cross (u : V) (hu : u∈X) (w : V) (hw : w∈Y) : Gᶜ.Adj u w := by
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
      exact ⟨split a b,fun h => Finset.disjoint_left.mp (dis a ha) (mem_filter.mpr ⟨mem_univ _,h⟩) hb⟩
    have full : Gᶜ.IsClique (X ∪ Y) := by
      intro u hu w hw hne
      rcases hu with hu|hu <;> rcases hw with hw|hw
      · exact sx hu hw hne
      · exact cross _ hu _ hw
      · exact (cross _ hw _ hu).symm
      · exact sy hu hw hne
    have lim : (X ∪ Y).card < 8 := lt_of_not_ge (fun h =>
      hi.mono h _ ⟨by simpa only [Finset.coe_union] using full,rfl⟩)
    rw [card_union_of_disjoint apart,card_map,card_map] at lim
    omega

theorem row_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ht : G.CliqueFree 3) (v : Fin n) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let A (i : N) := (univ : Finset B).filter (fun x => G.Adj i.val x.val)
    ∀ i : N, (A i).card+1=G.degree i.val := by
  intro N B A i
  let f : B ↪ Fin n := ⟨Subtype.val,Subtype.val_injective⟩
  have root := (G.mem_neighborFinset ..).mp i.property
  have eq : (A i).map f=(G.neighborFinset i.val).erase v := by
    ext y
    constructor
    · intro h
      obtain ⟨x,hx,rfl⟩ := mem_map.mp h
      exact mem_erase.mpr ⟨((Gᶜ.mem_neighborFinset ..).mp x.property).ne.symm,
        (G.mem_neighborFinset ..).mpr (mem_filter.mp hx).2⟩
    · intro h
      obtain ⟨ne,ha⟩ := mem_erase.mp h
      have adj := (G.mem_neighborFinset ..).mp ha
      have notAdj : ¬G.Adj v y := fun hit =>
        G.isIndepSet_neighborSet_of_triangleFree ht v root hit adj.ne adj
      exact mem_map.mpr ⟨⟨y,(Gᶜ.mem_neighborFinset ..).mpr ⟨ne.symm,notAdj⟩⟩,
        mem_filter.mpr ⟨mem_univ _,adj⟩,rfl⟩
  rw [←card_map (f:=f) (s:=A i),eq,card_erase_add_one ((G.mem_neighborFinset ..).mpr root.symm)]
  rfl

/-- Each neighbor of a vertex of the antineighborhood is either in the
antineighborhood or in exactly one of the root's neighbor positions. -/
private theorem column_card {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (e : Fin d ≃ G.neighborFinset v) :
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin n))
    let A (i : Fin d) := (univ : Finset B).filter (fun x => G.Adj (e i).val x.val)
    ∀ x : B, D.degree x + (univ.filter (fun i => x ∈ A i)).card = G.degree x.val := by
  classical
  intro B D A x
  let f : B ↪ Fin n := Function.Embedding.subtype _
  let g : Fin d ↪ Fin n := e.toEmbedding.trans (Function.Embedding.subtype _)
  let X := (D.neighborFinset x).map f
  let Y := (univ.filter (fun i => x ∈ A i)).map g
  have root (i : Fin d) : G.Adj v (g i) := (G.mem_neighborFinset ..).mp (e i).2
  have anti (b : B) := (Gᶜ.mem_neighborFinset ..).mp b.2
  have dis : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro w hw hy
    obtain ⟨b,_,rfl⟩ := mem_map.mp hw
    obtain ⟨i,_,eq⟩ := mem_map.mp hy
    apply (anti b).2
    change G.Adj v (f b)
    rw [← eq]
    exact root i
  have cover : X ∪ Y = G.neighborFinset x.val := by
    ext w
    constructor
    · intro hw
      apply (G.mem_neighborFinset ..).mpr
      rcases mem_union.mp hw with h|h
      · obtain ⟨b,hb,rfl⟩ := mem_map.mp h
        exact (D.mem_neighborFinset ..).mp hb
      · obtain ⟨i,hi,rfl⟩ := mem_map.mp h
        exact ((mem_filter.mp (mem_filter.mp hi).2).2).symm
    · intro hw
      have adj := (G.mem_neighborFinset ..).mp hw
      by_cases hit : G.Adj v w
      · let j : G.neighborFinset v := ⟨w,(G.mem_neighborFinset ..).mpr hit⟩
        let i := e.symm j
        have ei : e i = j := e.apply_symm_apply j
        have eq : g i = w := congrArg Subtype.val ei
        apply mem_union_right
        refine mem_map.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,?_⟩,eq⟩
        apply mem_filter.mpr
        refine ⟨mem_univ _,?_⟩
        change G.Adj (g i) x.val
        rw [eq]
        exact adj.symm
      · have ne : v ≠ w := by
          rintro rfl
          exact (anti x).2 adj.symm
        let b : B := ⟨w,(Gᶜ.mem_neighborFinset ..).mpr ⟨ne,hit⟩⟩
        exact mem_union_left _ (mem_map.mpr ⟨b,(D.mem_neighborFinset ..).mpr adj,rfl⟩)
  have h := congrArg Finset.card cover
  rw [card_union_of_disjoint dis] at h
  simpa only [X,Y,card_map,SimpleGraph.card_neighborFinset_eq_degree] using h

theorem extract (G : SimpleGraph (Fin 28)) (tri : G.CliqueFree 3)
    (deg : ∀ x, 5 ≤ (univ.filter (G.Adj x)).card ∧ (univ.filter (G.Adj x)).card ≤ 7)
    (v : Fin 28) (hv : (univ.filter (G.Adj v)).card = 5)
    (noEight : ¬ ∃ S, G.IsNIndepSet 8 S)
    (rule : ∀ (V : Type) [Fintype V] [DecidableEq V] (D : SimpleGraph V)
      [DecidableRel D.Adj] (A : Fin 5 → Finset V), Fintype.card V = 22 →
      D.CliqueFree 3 → Dᶜ.CliqueFree 7 → (∀ i, Dᶜ.IsClique (A i)) →
      (∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6) →
      (∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) →
      (∀ (J : Finset (Fin 5)) (S : Finset V), Dᶜ.IsClique S →
        (∀ i ∈ J, Disjoint (A i) S) → J.card + S.card ≤ 7) →
      (∀ x, 5 ≤ D.degree x + (univ.filter (fun i => x ∈ A i)).card ∧
        D.degree x + (univ.filter (fun i => x ∈ A i)).card ≤ 7) → False) : False := by
  classical
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set (Fin 28))
  have hd : G.degree v = 5 := by simpa [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter] using hv
  have hrange (x : Fin 28) : 5 ≤ G.degree x ∧ G.degree x ≤ 7 := by
    simpa [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter] using deg x
  have hn : Fintype.card N = 5 := by rw [Fintype.card_coe]; exact hd
  let e : Fin 5 ≃ N := (Fintype.equivFinOfCardEq hn).symm
  let A (i : Fin 5) := (univ : Finset B).filter (fun x => G.Adj (e i).val x.val)
  have hb : Fintype.card B = 22 := by
    rw [Fintype.card_coe]
    change Gᶜ.degree v = 22
    rw [G.degree_compl, Fintype.card_fin, hd]
  have hc : Gᶜ.CliqueFree 8 := fun s hs => noEight ⟨s,G.isNClique_compl.mp hs⟩
  obtain ⟨ht,hi,rows,avoid⟩ := neighborhood_data G v tri hc
  have hap (J : Finset (Fin 5)) (S : Finset B) (cl : Dᶜ.IsClique S)
      (dis : ∀ i ∈ J, Disjoint (A i) S) : J.card + S.card ≤ 7 := by
    have h := avoid (J.map e.toEmbedding) S cl (by
      intro a ha
      obtain ⟨i,hi,rfl⟩ := mem_map.mp ha
      exact dis i hi)
    simpa only [card_map] using h
  apply rule B D A hb ht hi (fun i => rows (e i))
  · intro i
    have h := row_card G tri v (e i)
    change (A i).card + 1 = G.degree (e i).val at h
    obtain ⟨lo,up⟩ := hrange (e i).val
    omega
  · intro S hs
    have h := hap (univ.filter (fun i => Disjoint (A i) S)) S hs.isClique
      (fun i hi => (mem_filter.mp hi).2)
    rw [hs.card_eq] at h
    omega
  · exact hap
  · intro x
    have h := column_card G v e x
    change D.degree x + (univ.filter (fun i => x ∈ A i)).card = G.degree x.val at h
    rw [h]
    exact hrange x.val

end E151Rows

/-! Extend a triangle-free graph on a finite vertex set to a maximal one. -/
namespace E151D5

theorem maximal_extension {V : Type*} [Finite V] (D : SimpleGraph V)
    (hD : D.CliqueFree 3) (hI : Dᶜ.CliqueFree 7) :
    ∃ M : SimpleGraph V, D ≤ M ∧ M.CliqueFree 3 ∧ Mᶜ.CliqueFree 7 ∧
      ∀ K : SimpleGraph V, M ≤ K → K.CliqueFree 3 → K = M := by
  obtain ⟨M,hDM,hmax⟩ := Finite.exists_le_maximal (p := fun K : SimpleGraph V => K.CliqueFree 3) hD
  exact ⟨M,hDM,hmax.1,SimpleGraph.CliqueFree.anti (compl_le_compl hDM) hI,
    fun K hMK hK => le_antisymm (hmax.2 hK hMK) hMK⟩

end E151D5

/-! The independent-set enumeration and its proofs adapt GlueSeed.graph_rows
from @sturdy4days, open-math-agents PR #13293. -/
namespace E151Rows
open SimpleGraph Finset

theorem sandwich_rows {V : Type} [DecidableEq V]
    (L D U : SimpleGraph V) [DecidableRel L.Adj] [DecidableRel D.Adj] [DecidableRel U.Adj]
    (lower : L ≤ D) (upper : D ≤ U) (vs : List V) (nodup : vs.Nodup)
    (full : ∀ x : V, x ∈ vs) (A : Fin 5 → Finset V) (rows : ∀ i, Dᶜ.IsClique (A i))
    (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S →
      ((univ : Finset (Fin 5)).filter fun i => Disjoint (A i) S).card ≤ 1) :
    let bits := fun bs : List Bool => bs.foldr (fun b k => 2*k+b.toNat) 0
    let enc (G : SimpleGraph V) [DecidableRel G.Adj] (ws : List V) :=
      (ws.foldr (fun v (p : List V × List ℕ) =>
        (v::p.1, bits (p.1.map fun x => decide (G.Adj v x)) :: p.2)) ([],[])).2
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∃ R K : Fin 5 → Nat, (∀ i, (R i,K i) ∈ enum (enc L vs)) ∧
      (∀ i, 4 ≤ K i ∧ K i ≤ 6) ∧
      (∀ s, (s,6) ∈ enum (enc U vs) →
        ((univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) := by
  intro bits enc enum
  let mark (ws : List V) (S : Finset V) := bits (ws.map fun x => decide (x∈S))
  let ind0 (p : Nat × Nat) := (2*p.1,p.2)
  let ind1 (p : Nat × Nat) := (2*p.1+1,p.2+1)
  have enum_nil : enum [] = [(0,0)] := rfl
  have enum_cons (m : ℕ) (b : List ℕ) : enum (m::b) =
      (enum b).map ind0 ++ ((enum b).filter fun p=>m &&& p.1 == 0).map ind1 := rfl
  have enc_nil (G : SimpleGraph V) [DecidableRel G.Adj] : enc G [] = [] := rfl
  let foldPair (G : SimpleGraph V) [DecidableRel G.Adj] (ws : List V) : List V × List ℕ :=
    ws.foldr (fun v (p : List V × List ℕ) =>
      (v::p.1,bits (p.1.map fun x => decide (G.Adj v x))::p.2)) ([],[])
  have prefix_eq (G : SimpleGraph V) [DecidableRel G.Adj] (ws : List V) : (foldPair G ws).1 = ws := by
    induction ws with
    | nil => rfl
    | cons x ws ih => exact congrArg (x :: ·) ih
  have enc_cons (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (ws : List V) :
      enc G (a::ws) = bits (ws.map fun x => decide (G.Adj a x)) :: enc G ws := by
    change bits ((foldPair G ws).1.map fun x => decide (G.Adj a x)) :: (foldPair G ws).2 = _
    rw [prefix_eq]
  have bits_nil : bits [] = 0 := rfl
  have bits_cons (a : Bool) (l : List Bool) : bits (a::l) = 2*bits l+a.toNat := rfl
  have bit_form (b : Bool) (n : Nat) : Nat.bit b n = 2*n+b.toNat := by
    cases b <;> simp [Nat.bit, Nat.two_mul]
  have and_bit (a : Bool) (x : ℕ) (b : Bool) (y : ℕ) :
      Nat.bit a x &&& Nat.bit b y = Nat.bit (a && b) (x &&& y) := by
    apply Nat.eq_of_testBit_eq
    intro i
    cases i with
    | zero => cases a <;> cases b <;> simp [Nat.testBit_zero,bit_form]
    | succ i =>
      have half (c : Bool) (t : ℕ) : Nat.bit c t / 2 = t := by
        cases c <;> simp [bit_form]
        omega
      rw [Nat.testBit_and,Nat.testBit_succ,Nat.testBit_succ,Nat.testBit_succ,half,half,half,Nat.testBit_and]
  have and_mask (vs : List V) (f g : V → Bool) :
      bits (vs.map f) &&& bits (vs.map g) = 0 ↔ ∀ x∈vs, f x = true → g x = false := by
    induction vs with
    | nil => simp [bits_nil]
    | cons a l ih =>
      simp only [List.map_cons, bits_cons, ← bit_form, and_bit, List.forall_mem_cons]
      rw [bit_form]
      cases f a <;> cases g a <;> simp [ih]
  have mark_congr (vs : List V) (s t : Finset V)
      (h : ∀ x∈vs, x∈s ↔ x∈t) : mark vs s = mark vs t := by
    dsimp only [mark]
    congr 1
    exact List.map_congr_left (fun x hx => by simp only [h x hx])
  have sound (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) (hn : vs.Nodup) {p : Nat × Nat} (hp : p ∈ enum (enc G vs)) :
      ∃ S : Finset V, S ⊆ vs.toFinset ∧ Gᶜ.IsClique (S : Set V) ∧ p = (mark vs S,S.card) := by
    induction vs generalizing p with
    | nil =>
      simp [enc_nil,enum_nil] at hp
      exact ⟨∅,by simp,by simp,by simp [hp,mark,bits_nil]⟩
    | cons a l ih =>
      have hn' := List.nodup_cons.mp hn
      simp only [enc_cons,enum_cons,List.mem_append,List.mem_map,List.mem_filter] at hp
      rcases hp with ⟨q,hq,rfl⟩ | ⟨q,⟨hq,hd⟩,rfl⟩
      · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
        have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
        exact ⟨S,by simpa using hS.trans (Finset.subset_insert a _),hI,by simp [ind0,mark,bits_cons,ha]⟩
      · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
        have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
        have hz := (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈S))).mp (beq_iff_eq.mp hd)
        have hi : Gᶜ.IsClique (insert a S : Finset V) := by
          rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem ha]
          refine ⟨hI,fun x hx => ⟨?_,?_⟩⟩
          · exact fun e => ha (e ▸ hx)
          · intro adj
            have := hz x (List.mem_toFinset.mp (hS hx)) (by simpa using adj)
            exact (of_decide_eq_false this) hx
        have hm := mark_congr l (insert a S) S (by intro x hx; simp [show x ≠ a from fun e => hn'.1 (e ▸ hx)])
        refine ⟨insert a S, by simpa using Finset.insert_subset_insert a hS, hi, ?_⟩
        simp [ind1,mark,bits_cons,Finset.card_insert_of_notMem ha] at hm ⊢
        omega
  have complete (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) (hn : vs.Nodup) (S : Finset V)
      (hS : S ⊆ vs.toFinset) (hI : Gᶜ.IsClique (S : Set V)) :
      (mark vs S,S.card) ∈ enum (enc G vs) := by
    induction vs generalizing S with
    | nil =>
      have e : S=∅ := Finset.subset_empty.mp (by simpa using hS)
      simp [e,enc_nil,enum_nil,mark,bits_nil]
    | cons a l ih =>
      have hn' := List.nodup_cons.mp hn
      simp only [enc_cons,enum_cons,List.mem_append,List.mem_map,List.mem_filter]
      by_cases ha : a ∈ S
      · let T := S.erase a
        have hT : T ⊆ l.toFinset := by
          intro x hx
          have m := Finset.mem_erase.mp hx
          have h := List.mem_cons.mp (List.mem_toFinset.mp (hS m.2))
          exact List.mem_toFinset.mpr (h.resolve_left m.1)
        have hI' := hI.subset (show (T : Set V) ⊆ (S : Set V) from Finset.erase_subset ..)
        have hmark := mark_congr l S T (by intro x hx; simp [T,show x≠a from fun e => hn'.1 (e ▸ hx)])
        have hcard : T.card + 1 = S.card := Finset.card_erase_add_one ha
        right
        refine ⟨(mark l T,T.card),⟨ih hn'.2 T hT hI', ?_⟩,?_⟩
        · apply beq_iff_eq.mpr
          apply (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈T))).mpr
          intro x _ hx
          apply decide_eq_false
          intro hm
          have hmem := Finset.mem_erase.mp hm
          exact (hI ha hmem.2 hmem.1.symm).2 (of_decide_eq_true hx)
        · simp [ind1,mark,bits_cons,ha,hcard] at hmark ⊢
          omega
      · have hT : S ⊆ l.toFinset := by
          intro x hx
          have h := List.mem_cons.mp (List.mem_toFinset.mp (hS hx))
          exact List.mem_toFinset.mpr (h.resolve_left (fun e => ha (e ▸ hx)))
        exact Or.inl ⟨_,ih hn'.2 S hT hI,by simp [ind0,mark,bits_cons,ha]⟩
  refine ⟨fun i => mark vs (A i), fun i => (A i).card, ?_, size, ?_⟩
  · intro i
    apply complete L vs nodup _ (fun x _ => List.mem_toFinset.mpr (full x))
    exact fun _ ha _ hb hne => ⟨hne,fun h => (rows i ha hb hne).2 (lower h)⟩
  · intro s hs
    obtain ⟨S,_,cl,eq⟩ := sound U vs nodup hs
    have val := congrArg Prod.fst eq
    have scard := congrArg Prod.snd eq
    change s = mark vs S at val
    change 6 = S.card at scard
    subst s
    have cs : Dᶜ.IsNClique 6 S :=
      ⟨(fun _ ha _ hb hne => ⟨hne,fun h => (cl ha hb hne).2 (upper h)⟩),scard.symm⟩
    refine (card_le_card ?_).trans (cap S cs)
    intro i hi
    apply mem_filter.mpr
    refine ⟨mem_univ _,Finset.disjoint_left.mpr ?_⟩
    intro x hx hy
    have h := (and_mask vs _ _).mp (mem_filter.mp hi).2 x (full x) (by simpa using hx)
    exact (of_decide_eq_false h) hy

end E151Rows

/-! Transfer contact constraints along a labeling of the antineighborhood. -/
namespace E151Rows
open SimpleGraph Finset

/-- Relabel the child graph inside a specified supergraph, carrying its contact
sets and the disjointness bound to the same 22 vertex labels. -/
theorem transport {V : Type} [DecidableEq V] (D M : SimpleGraph V)
    (Q : SimpleGraph (Fin 22)) (f : Fin 22 ≃ V) (sub : D ≤ M)
    (label : ∀ i j, M.Adj (f i) (f j) ↔ Q.Adj i j)
    (free : Dᶜ.CliqueFree 7) (A : Fin 5 → Finset V)
    (rows : ∀ i, Dᶜ.IsClique (A i))
    (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S →
      (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1)
    (rule : ∀ (T : SimpleGraph (Fin 22)) [DecidableRel T.Adj]
      (R : Fin 5 → Finset (Fin 22)), T ≤ Q → Tᶜ.CliqueFree 7 →
      (∀ i, Tᶜ.IsClique (R i)) → (∀ i, 4 ≤ (R i).card ∧ (R i).card ≤ 6) →
      (∀ S, Tᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (R i) S)).card ≤ 1) →
      False) : False := by
  classical
  let T := D.comap f
  let R (i : Fin 5) := (A i).map f.symm.toEmbedding
  have memR (i : Fin 5) (x : Fin 22) : x ∈ R i ↔ f x ∈ A i := mem_map_equiv
  have liftSet {k : ℕ} (S : Finset (Fin 22)) (hS : Tᶜ.IsNClique k S) :
      Dᶜ.IsNClique k (S.map f.toEmbedding) := by
    refine ⟨?_,by simpa only [card_map] using hS.card_eq⟩
    intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact ⟨hxy,(hS.isClique ha hb (fun h => hxy (congrArg f h))).2⟩
  apply rule T R (fun {i j} h => (label i j).mp (sub h))
    (fun s hs => free _ (liftSet s hs))
  · intro i a ha b hb hne
    exact ⟨hne,(rows i ((memR i a).mp ha) ((memR i b).mp hb)
      (fun h => hne (f.injective h))).2⟩
  · intro i
    simpa only [R,card_map] using size i
  · intro S hs
    refine (card_le_card ?_).trans (cap _ (liftSet S hs))
    intro i hi
    refine mem_filter.mpr ⟨mem_univ _,disjoint_left.mpr ?_⟩
    intro x hx hy
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact disjoint_left.mp (mem_filter.mp hi).2 ((memR i b).mpr hx) hb

end E151Rows

namespace E151Rows
open SimpleGraph Finset

/-- Evaluate both graphs in the same vertex order.  The numeric certificate
only needs the row-size cap and the tests on independent six-sets. -/
theorem close_coded
    (bl bu : List Nat) (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22)) (rows : ∀ i, Dᶜ.IsClique (A i))
    (size : ∀ i, 4≤(A i).card ∧ (A i).card≤6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S →
      ((univ : Finset (Fin 5)).filter fun i => Disjoint (A i) S).card≤1) :
    let edge (b : List Nat) (i j : Fin 22) :=
      i < j ∧ (b.getD i.val 0).testBit (j.val - i.val - 1) = true
    let graph (b : List Nat) := SimpleGraph.fromRel (edge b)
    let dec (b : List Nat) (i j : Fin 22) : Decidable (i ≠ j ∧
        ((i < j ∧ (b.getD i.val 0).testBit (j.val - i.val - 1) = true) ∨
         (j < i ∧ (b.getD j.val 0).testBit (i.val - j.val - 1) = true))) :=
      inferInstance
    let bits := fun bs : List Bool => bs.foldr (fun b k => 2*k+b.toNat) 0
    let enc (b : List Nat) := ((List.finRange 22).foldr (fun v (p : List (Fin 22) × List ℕ) =>
      (v::p.1,bits (p.1.map fun x => @decide ((graph b).Adj v x) (dec b v x)) :: p.2)) ([],[])).2
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    (∀ R K : Fin 5 → Nat, (∀ i,(R i,K i) ∈ enum bl) → (∀ i,K i≤6) →
      (∀ s,(s,6)∈enum bu → ((univ : Finset (Fin 5)).filter fun i => R i &&& s=0).card≤1) → False) →
    (enc bl=bl ∧ enc bu=bu) → graph bl ≤ D → D ≤ graph bu → False := by
  intro edge graph dec bits enc enum forbidden valid lower upper
  obtain ⟨R,K,member,len,miss⟩ :=
    @sandwich_rows (Fin 22) _ (graph bl) D (graph bu) (dec bl) _ (dec bu)
      lower upper (List.finRange 22) (List.nodup_finRange 22) (List.mem_finRange) A rows size cap
  change ∀ i,(R i,K i) ∈ enum (enc bl) at member
  change ∀ s,(s,6)∈enum (enc bu) → _ at miss
  rw [valid.1] at member
  rw [valid.2] at miss
  exact forbidden R K member (fun i => (len i).2) miss

end E151Rows

/-! Graph intervals for a spanning subgraph with no independent seven-set. -/
namespace E151D5

theorem dead_upper {V : Type*} {D U : SimpleGraph V}
    (hDU : D ≤ U) (hI : Dᶜ.CliqueFree 7) (S : Finset V) (hcard : S.card = 7)
    (hnone : ∀ u ∈ S, ∀ v ∈ S, ¬ U.Adj u v) : False := by
  apply hI S
  exact ⟨fun u hu v hv huv => ⟨huv,fun h => hnone u hu v hv (hDU h)⟩,hcard⟩

theorem branch_lower {V : Type*} {P L D : SimpleGraph V} {x y : V}
    (hPD : P ≤ D) (hxy : D.Adj x y)
    (cert : ∀ u v, L.Adj u v → P.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x)) :
    L ≤ D := by
  intro u v h
  obtain old | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ := cert u v h
  · exact hPD old
  · exact hxy
  · exact hxy.symm

theorem branch_upper {V : Type*} {U D K : SimpleGraph V} {x y : V}
    (hDU : D ≤ U) (hxy : ¬ D.Adj x y)
    (cert : ∀ u v, U.Adj u v → K.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x)) :
    D ≤ K := by
  intro u v h
  obtain keep | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ := cert u v (hDU h)
  · exact keep
  · exact (hxy h).elim
  · exact (hxy h.symm).elim

end E151D5

namespace E151D5

theorem certify_root_mask {D L U : SimpleGraph (Fin 22)} [DecidableRel L.Adj] [DecidableRel U.Adj]
    (hDU : D ≤ U) (hI : Dᶜ.CliqueFree 7) (W : Fin 22 → Fin 22 → Nat)
    (hc : (List.finRange 22).all (fun x => (List.finRange 22).all (fun y =>
      if L.Adj x y then
        let S := (List.finRange 22).filter (fun v => (W x y).testBit v.val)
        S.length == 7 && S.all (fun u => S.all (fun v =>
          decide (¬U.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x))))
      else true)) = true) : L ≤ D := by
  intro x y hxy
  let S := (List.finRange 22).filter (fun v => (W x y).testBit v.val)
  have ok := List.all_eq_true.mp (List.all_eq_true.mp hc x (by simp)) y (by simp)
  rw [if_pos hxy] at ok
  change (S.length == 7 && S.all (fun u => S.all (fun v =>
    decide (¬U.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x))))) = true at ok
  obtain ⟨size,rows⟩ := Bool.and_eq_true_iff.mp ok
  by_contra no
  apply dead_upper (le_rfl : D ≤ D) hI S.toFinset
  · rw [List.toFinset_card_of_nodup]
    · exact eq_of_beq size
    · exact (List.nodup_finRange _).filter _
  · intro u hu v hv hedge
    have e := of_decide_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp rows u (List.mem_toFinset.mp hu)) v (List.mem_toFinset.mp hv))
    obtain absent | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ := e
    · exact absent (hDU hedge)
    · exact no hedge
    · exact no hedge.symm

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_8 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [1785856,937984,295872,99024,43170,43154,16788,4297,4865,1600,24,48,85,21,4,1,0,0,1,0,0,0] →
    (graph [737280,675840,295872,99024,43170,43154,16788,4297,4865,1600,24,48,85,21,4,1,0,0,1,0,0,0] ≤ D → D ≤ graph [1785856,937984,295872,99024,43170,43154,16788,4297,4865,1600,24,48,85,21,4,1,0,0,1,0,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_8_root
  change D ≤ graph [1785856,937984,295872,99024,43170,43154,16788,4297,4865,1600,24,48,85,21,4,1,0,0,1,0,0,0] at hDU
  let masks : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,127,0,0,0,0,0,0,191,0,0,0,0,319,0,0,0,8599,0,0,575,0,0,0,4715,0,2867,0,0,9415,5323,9875,5475,0,0,0,0,0,0,2359,2619,0,0,6499,10899,0,0,0,0,0,4207,0,4667,0,0,0,0,0,0,0,0,0,0,8351,0,8503,0,0,0,0,0,0,13507,0,16447,0,0,0,0,82029,2380424,0,0,2383360,0,0,549141,32831,0,0,0,0,0,1614148,163998,0,0,1617152,0,299562,0,0,0,65647,0,0,81981,0,0,0,0,86569,0,88353,0,598213,0,1163556,131231,0,0,0,0,163902,0,0,172310,0,0,174610,397514,0,2277912,0,0,266347,0,393422,0,295482,0,0,0,1380704,0,0,0,0,402626,0,0,0,0,0,532631,0,590029,0,540981,0,0,0,2761360,0,0,595137,0,0,0,0,0,984256,1114469,0,0,1380456,1098036,0,0,1712324,0,1333792,0,0,0,0,0,0,0,0,0,0,0,2228890,2760852,0,0,2146872,2429128,0,2664720,0,0,0,0,0,0,0,0,0,0,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [737280,675840,295872,99024,43170,43154,16788,4297,4865,1600,24,48,85,21,4,1,0,0,1,0,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  exact leaf_8_root lo hDU

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_10 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [1884160,888832,329504,82784,35114,34986,20772,5201,321,80,1097,280,24,3,16,4,2,2,1,0,0,0] →
    (graph [1884160,888832,329504,82784,35114,34986,4388,1105,321,80,1033,264,24,3,0,0,2,2,1,0,0,0] ≤ D → D ≤ graph [1884160,888832,329504,82784,35114,34986,20772,5201,321,80,1097,280,24,3,16,4,2,2,1,0,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_10_root
  change D ≤ graph [1884160,888832,329504,82784,35114,34986,20772,5201,321,80,1097,280,24,3,16,4,2,2,1,0,0,0] at hDU
  let masks : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,127,0,0,0,0,0,0,191,0,0,0,367,0,282929,0,0,2507,0,0,0,671,0,561714,1735,0,14083,0,0,0,1135,1687,0,0,0,0,0,0,0,2207,0,0,2411,0,0,0,0,11459,0,0,282677,561210,0,0,5475,6803,0,0,0,0,0,0,9415,10443,10899,9571,0,0,0,0,0,0,0,0,16447,0,0,0,0,0,147613,0,410133,279653,0,0,289089,32831,0,0,0,0,0,98414,0,622890,0,0,559258,0,566914,0,65647,0,0,0,98366,0,0,0,0,99974,0,0,595234,0,0,0,0,131231,0,0,0,147517,0,0,149833,0,0,0,399889,0,0,0,0,0,263271,0,278589,0,0,0,393877,0,0,0,0,0,0,0,0,1377380,0,526491,0,557118,0,0,0,590186,0,0,0,0,0,0,0,0,0,0,2754712,2890256,1311845,1115238,0,1130604,3707408,0,0,0,0,0,0,3422464,0,0,0,0,0,0,0,0,2230425,2623642,2261148,0,0,3428640,0,0,0,0,3421440,0,0,0,0,0,0,0,0,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [1884160,888832,329504,82784,35114,34986,4388,1105,321,80,1033,264,24,3,0,0,2,2,1,0,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  exact leaf_10_root lo hDU

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_28 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [1933312,864256,148620,82484,34831,33352,16528,10792,330,147,1312,25,162,7,16,8,2,1,1,0,0,0] →
    (graph [1933312,864256,148620,82484,34831,33352,16528,10280,330,147,1280,25,162,5,16,8,2,1,1,0,0,0] ≤ D → D ≤ graph [1933312,864256,148620,82484,34831,33352,16528,10792,330,147,1312,25,162,7,16,8,2,1,1,0,0,0] → False) →
    (graph [1933312,864256,148620,82468,34831,33352,16528,10280,330,147,1280,25,162,5,16,8,2,1,1,0,0,0] ≤ D → D ≤ graph [1933312,864256,148620,82468,34831,33352,16528,10792,330,147,1312,25,162,7,16,8,2,1,1,0,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_28_1 leaf_28_0
  change D ≤ graph [1933312,864256,148620,82484,34831,33352,16528,10792,330,147,1312,25,162,7,16,8,2,1,1,0,0,0] at hDU
  let masks : List Nat := [0,0,0,0,0,0,0,0,0,0,0,0,278949,0,3131,0,0,967,1259,12883,0,0,0,0,0,4255,0,0,0,0,0,0,280853,0,0,0,0,0,0,4639,0,995,0,0,0,0,0,3103,0,0,0,0,0,1507,13843,0,0,0,0,0,0,10595,3243,0,3418880,0,0,0,0,0,0,5291,0,0,4999,0,0,6175,0,0,12823,11291,0,0,0,8675,0,0,0,0,0,0,18463,0,0,0,0,279009,0,0,311829,0,0,53277,289809,0,36895,0,0,0,50345,0,0,295813,0,0,51229,0,0,0,69775,0,0,0,593950,0,0,0,0,0,0,722986,0,598370,0,0,134171,0,657438,0,0,0,0,0,663906,668178,0,0,0,0,0,0,0,0,263047,0,280605,0,0,0,0,0,0,0,0,299541,0,0,0,1376736,1451104,526367,0,0,0,0,0,0,594062,0,0,658458,0,0,0,2639900,2658332,0,0,1843552,1311201,1114594,3736324,1199144,3811344,0,0,0,0,0,0,0,1151680,0,0,0,0,0,0,0,2115613,2623518,0,0,0,3418400,3416896,2199692,0,0,2247704,0,0,0,0,0,0,0,0,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [1933312,864256,148620,82468,34831,33352,16528,10280,330,147,1280,25,162,5,16,8,2,1,1,0,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  by_cases splitroot : D.Adj 8 3
  · have lo1 : graph [1933312,864256,148620,82484,34831,33352,16528,10280,330,147,1280,25,162,5,16,8,2,1,1,0,0,0] ≤ D := by
      apply branch_lower lo splitroot
      dsimp only [graph]
      decide +kernel
    exact leaf_28_1 lo1 hDU
  · have hi0 : D ≤ graph [1933312,864256,148620,82468,34831,33352,16528,10792,330,147,1312,25,162,7,16,8,2,1,1,0,0,0] := by
      apply branch_upper hDU splitroot
      dsimp only [graph]
      decide +kernel
    exact leaf_28_0 lo hi0

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_63 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,672,328,82,16,8,2,1,1,0,0,0] →
    (graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,640,328,80,16,8,2,1,0,0,0,0] ≤ D → D ≤ graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,672,328,82,16,8,2,1,1,0,0,0] → False) →
    (graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,640,320,80,16,8,2,1,0,0,0,0] ≤ D → D ≤ graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,672,320,82,16,8,2,1,1,0,0,0] → False) →
    (graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,640,328,82,16,8,2,1,0,0,0,0] ≤ D → D ≤ graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,672,328,82,16,8,2,1,1,0,0,0] → False) →
    (graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,640,320,82,16,8,2,1,0,0,0,0] ≤ D → D ≤ graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,672,320,82,16,8,2,1,1,0,0,0] → False) →
    (graph [1728512,966656,266406,132619,37008,17441,1320,397,312,90,648,640,320,80,16,8,2,1,0,0,0,0] ≤ D → D ≤ graph [1728512,966656,266406,132619,37008,17441,1320,397,312,90,648,672,328,82,16,8,2,1,1,0,0,0] → False) →
    (graph [1728512,966656,266406,132619,37008,17441,1320,397,312,90,640,640,320,80,16,8,2,1,0,0,0,0] ≤ D → D ≤ graph [1728512,966656,266406,132619,37008,17441,1320,397,312,90,640,672,328,82,16,8,2,1,1,0,0,0] → False) →
    (graph [1728512,966656,266406,132619,37008,17441,1324,396,312,90,648,640,320,80,16,8,2,1,0,0,0,0] ≤ D → D ≤ graph [1728512,966656,266406,132619,37008,17441,1324,396,312,90,648,672,328,82,16,8,2,1,1,0,0,0] → False) →
    (graph [1728512,966656,266406,132619,37008,17441,1324,396,312,90,640,640,320,80,16,8,2,1,0,0,0,0] ≤ D → D ≤ graph [1728512,966656,266406,132619,37008,17441,1324,396,312,90,640,672,328,82,16,8,2,1,1,0,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_63_1111 leaf_63_1110 leaf_63_11011 leaf_63_11010 leaf_63_101 leaf_63_100 leaf_63_011 leaf_63_010
  change D ≤ graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,672,328,82,16,8,2,1,1,0,0,0] at hDU
  let masks : List Nat := [0,0,0,0,0,0,0,0,8407,2395,0,0,4775,1835,0,0,0,0,0,0,8435,0,0,0,4751,0,0,0,0,0,2383,0,0,0,0,0,0,0,0,0,1843,0,0,0,0,0,0,5647,0,0,0,3403,9395,0,0,0,0,0,0,0,3379,0,10439,0,6671,0,0,0,0,0,12467,0,6223,0,5899,0,0,0,0,0,0,10319,0,0,0,0,9523,12935,0,0,0,24775,0,0,280654,0,0,0,0,311602,283270,0,0,0,0,34571,0,299534,0,0,0,297290,311474,0,0,0,0,0,0,0,0,67663,0,0,0,591153,0,598213,0,721421,0,0,0,0,0,0,0,135695,0,0,663729,0,720973,0,657161,0,0,0,0,0,0,0,0,264271,0,0,0,0,0,0,0,0,0,296714,0,0,286918,0,0,1378380,1446412,0,532679,0,0,0,0,0,0,0,0,0,591949,659981,0,2646192,2655536,0,0,0,1116237,1312846,0,0,3424464,3801760,0,0,0,0,1150216,0,0,1140804,0,0,0,0,0,0,2629809,2121906,3424452,3735880,0,0,0,0,0,0,0,2189392,2257056,0,0,0,0,0,0,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [1728512,966656,266406,132619,37008,17441,1320,396,312,90,640,640,320,80,16,8,2,1,0,0,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  by_cases splitroot : D.Adj 8 7
  · have lo1 : graph [1728512,966656,266406,132619,37008,17441,1320,397,312,90,640,640,320,80,16,8,2,1,0,0,0,0] ≤ D := by
      apply branch_lower lo splitroot
      dsimp only [graph]
      decide +kernel
    by_cases split1 : D.Adj 9 6
    · have lo11 : graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,640,320,80,16,8,2,1,0,0,0,0] ≤ D := by
        apply branch_lower lo1 split1
        dsimp only [graph]
        decide +kernel
      by_cases split11 : D.Adj 14 10
      · have lo111 : graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,640,320,80,16,8,2,1,0,0,0,0] ≤ D := by
          apply branch_lower lo11 split11
          dsimp only [graph]
          decide +kernel
        by_cases split111 : D.Adj 16 12
        · have lo1111 : graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,640,328,80,16,8,2,1,0,0,0,0] ≤ D := by
            apply branch_lower lo111 split111
            dsimp only [graph]
            decide +kernel
          exact leaf_63_1111 lo1111 hDU
        · have hi1110 : D ≤ graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,672,320,82,16,8,2,1,1,0,0,0] := by
            apply branch_upper hDU split111
            dsimp only [graph]
            decide +kernel
          exact leaf_63_1110 lo111 hi1110
      · have hi110 : D ≤ graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,672,328,82,16,8,2,1,1,0,0,0] := by
          apply branch_upper hDU split11
          dsimp only [graph]
          decide +kernel
        by_cases split110 : D.Adj 15 13
        · have lo1101 : graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,640,320,82,16,8,2,1,0,0,0,0] ≤ D := by
            apply branch_lower lo11 split110
            dsimp only [graph]
            decide +kernel
          by_cases split1101 : D.Adj 16 12
          · have lo11011 : graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,640,328,82,16,8,2,1,0,0,0,0] ≤ D := by
              apply branch_lower lo1101 split1101
              dsimp only [graph]
              decide +kernel
            exact leaf_63_11011 lo11011 hi110
          · have hi11010 : D ≤ graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,672,320,82,16,8,2,1,1,0,0,0] := by
              apply branch_upper hi110 split1101
              dsimp only [graph]
              decide +kernel
            exact leaf_63_11010 lo1101 hi11010
        · have hi1100 : D ≤ graph [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,672,328,80,16,8,2,1,1,0,0,0] := by
            apply branch_upper hi110 split110
            dsimp only [graph]
            decide +kernel
          apply dead_upper hi1100 hI ([1,4,5,10,13,14,15].toFinset : Finset (Fin 22))
          · decide +kernel
          · dsimp only [graph]; decide +kernel
    · have hi10 : D ≤ graph [1728512,966656,266406,132619,37008,17441,1320,397,312,90,648,672,328,82,16,8,2,1,1,0,0,0] := by
        apply branch_upper hDU split1
        dsimp only [graph]
        decide +kernel
      by_cases split10 : D.Adj 14 10
      · have lo101 : graph [1728512,966656,266406,132619,37008,17441,1320,397,312,90,648,640,320,80,16,8,2,1,0,0,0,0] ≤ D := by
          apply branch_lower lo1 split10
          dsimp only [graph]
          decide +kernel
        exact leaf_63_101 lo101 hi10
      · have hi100 : D ≤ graph [1728512,966656,266406,132619,37008,17441,1320,397,312,90,640,672,328,82,16,8,2,1,1,0,0,0] := by
          apply branch_upper hi10 split10
          dsimp only [graph]
          decide +kernel
        exact leaf_63_100 lo1 hi100
  · have hi0 : D ≤ graph [1728512,966656,266406,132619,37008,17441,1324,396,312,90,648,672,328,82,16,8,2,1,1,0,0,0] := by
      apply branch_upper hDU splitroot
      dsimp only [graph]
      decide +kernel
    by_cases split0 : D.Adj 9 6
    · have lo01 : graph [1728512,966656,266406,132619,37008,17441,1324,396,312,90,640,640,320,80,16,8,2,1,0,0,0,0] ≤ D := by
        apply branch_lower lo split0
        dsimp only [graph]
        decide +kernel
      by_cases split01 : D.Adj 14 10
      · have lo011 : graph [1728512,966656,266406,132619,37008,17441,1324,396,312,90,648,640,320,80,16,8,2,1,0,0,0,0] ≤ D := by
          apply branch_lower lo01 split01
          dsimp only [graph]
          decide +kernel
        exact leaf_63_011 lo011 hi0
      · have hi010 : D ≤ graph [1728512,966656,266406,132619,37008,17441,1324,396,312,90,640,672,328,82,16,8,2,1,1,0,0,0] := by
          apply branch_upper hi0 split01
          dsimp only [graph]
          decide +kernel
        exact leaf_63_010 lo01 hi010
    · have hi00 : D ≤ graph [1728512,966656,266406,132619,37008,17441,1320,396,312,90,648,672,328,82,16,8,2,1,1,0,0,0] := by
        apply branch_upper hi0 split0
        dsimp only [graph]
        decide +kernel
      apply dead_upper hi00 hI ([6,7,8,9,18,20,21].toFinset : Finset (Fin 22))
      · decide +kernel
      · dsimp only [graph]; decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_138 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [2031616,145410,401921,24704,11376,34100,9041,11332,3649,2200,580,129,23,16,32,32,5,0,0,0,0,0] →
    (graph [2031616,145410,401921,24704,11376,34100,9041,3140,1601,2200,580,129,23,16,32,32,1,0,0,0,0,0] ≤ D → D ≤ graph [2031616,145410,401921,24704,11376,34100,9041,11332,3649,2200,580,129,23,16,32,32,5,0,0,0,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_138_root
  change D ≤ graph [2031616,145410,401921,24704,11376,34100,9041,11332,3649,2200,580,129,23,16,32,32,5,0,0,0,0,0] at hDU
  let masks : List Nat := [0,0,0,0,4219,8381,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,247,0,0,0,0,0,375,0,0,0,0,0,0,631,0,0,0,1863,0,0,0,0,1367,1639,0,3463,0,0,0,0,0,76169,2455,2727,3399,0,0,0,0,0,0,4215,0,0,0,0,0,0,0,0,72067,0,8375,0,0,0,0,24917,0,0,41637,27909,0,12473,0,16727,0,0,0,671860,0,24981,0,52741,0,0,20825,0,0,33447,0,0,41141,0,819812,0,43397,0,0,0,37545,0,0,0,0,67975,0,70035,70307,70979,0,0,0,0,0,0,0,0,0,131191,0,0,1188024,0,0,0,0,0,393830,934980,0,1183922,0,0,0,3606530,262759,0,0,791144,393334,0,0,1315490,2364738,0,0,0,0,958500,0,0,0,0,528505,655478,0,0,0,0,0,663732,672084,0,0,822788,0,0,0,0,0,0,0,1052851,0,1179830,0,0,0,1315426,0,0,0,1379842,0,0,0,3694616,0,0,0,0,0,2101587,0,2228566,0,0,2625656,0,0,0,2364994,0,0,0,0,0,2477056,0,0,0,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [2031616,145410,401921,24704,11376,34100,9041,3140,1601,2200,580,129,23,16,32,32,1,0,0,0,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  exact leaf_138_root lo hDU

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_146 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [1836036,459777,287744,27648,92208,53777,5284,5936,5476,1066,71,80,260,33,34,1,0,0,0,0,0,0] →
    (graph [1836036,459777,287744,27648,84016,21009,5284,5936,5476,1066,71,80,260,33,34,1,0,0,0,0,0,0] ≤ D → D ≤ graph [1836036,459777,287744,27648,92208,53777,5284,5936,5476,1066,71,80,260,33,34,1,0,0,0,0,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_146_root
  change D ≤ graph [1836036,459777,287744,27648,92208,53777,5284,5936,5476,1066,71,80,260,33,34,1,0,0,0,0,0,0] at hDU
  let masks : List Nat := [0,0,439,443,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,499,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,947,0,1987,0,0,0,0,0,0,1491,1955,0,0,0,0,18611,0,0,0,0,0,0,0,2490,527020,2100426,0,12595,0,0,0,0,340289,4533,0,0,268037,0,0,0,12597,0,0,0,0,8627,0,74531,75075,0,0,0,0,0,18618,0,0,49363,0,16819,0,0,0,0,155699,0,0,0,35034,0,49331,0,0,33235,50819,0,0,1226768,0,0,0,0,70437,0,74035,0,0,66467,0,0,0,2173002,0,0,213539,3507264,0,0,151605,141370,0,0,172115,147635,139571,0,3032576,0,0,0,0,0,0,0,329027,0,1312076,0,267045,0,263621,0,0,0,3450944,0,0,0,0,0,0,541349,2623114,0,0,526524,0,1868868,0,525228,0,0,0,0,3844096,0,0,0,0,0,1312069,1057114,0,0,0,1052988,0,1049052,0,3737096,0,0,0,0,1885188,0,0,0,0,0,2131139,0,2623116,0,2099418,0,0,0,2098634,0,0,0,3035648,0,0,0,0,0,0,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [1836036,459777,287744,27648,84016,21009,5284,5936,5476,1066,71,80,260,33,34,1,0,0,0,0,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  exact leaf_146_root lo hDU

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_161 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [1351681,368640,19526,6407,98376,12306,9364,4440,1571,2144,1108,200,337,84,1,0,1,0,4,1,0,0] →
    (graph [1351680,368640,19526,6407,98376,12306,9364,4440,1571,2144,1108,200,337,84,0,0,1,0,4,1,0,0] ≤ D → D ≤ graph [1351681,368640,19526,6407,98376,12306,9364,4440,1571,2144,1108,200,337,84,1,0,1,0,4,1,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_161_root
  change D ≤ graph [1351681,368640,19526,6407,98376,12306,9364,4440,1571,2144,1108,200,337,84,1,0,1,0,4,1,0,0] at hDU
  let masks : List Nat := [0,0,0,0,0,0,0,0,263381,263833,0,0,37221,141609,0,0,0,0,263373,0,0,0,0,0,0,0,41201,0,0,0,0,0,37233,0,0,0,0,0,263821,0,0,0,263889,0,140169,0,0,0,0,0,1056289,0,0,1051917,0,0,0,0,0,141873,0,72006,141705,0,0,0,0,0,0,1054989,0,0,0,37317,0,0,0,0,0,0,41413,0,0,0,0,0,0,0,534154,0,45169,1068553,0,89094,0,0,0,86130,542346,2124042,0,0,0,0,0,0,2130374,0,172425,0,0,0,0,0,172593,296133,1087749,0,0,0,102725,0,0,2165006,0,0,0,2163142,0,86578,0,0,0,2171234,0,0,0,2236810,1181965,0,0,0,172145,0,0,0,394889,0,1186081,0,0,0,3344672,0,787598,0,0,0,299121,0,0,295365,0,0,1313805,0,402057,0,0,0,0,787597,0,0,0,0,549426,0,0,2621838,0,0,544266,595014,0,0,0,0,0,0,0,3148046,0,0,1316369,0,1085765,1311885,0,0,0,0,0,1190153,0,0,0,0,0,1852936,3148045,0,0,0,2629842,0,0,0,0,2630282,2622606,0,2167110,0,0,0,0,0,2916548,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [1351680,368640,19526,6407,98376,12306,9364,4440,1571,2144,1108,200,337,84,0,0,1,0,4,1,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  exact leaf_161_root lo hDU

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_175 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [1359873,364544,6195,20642,20642,8515,2322,12804,6273,673,168,804,396,63,0,0,0,0,4,1,0,0] →
    (graph [1359873,364544,6195,20642,20642,8515,2322,4612,4225,673,168,772,388,63,0,0,0,0,4,1,0,0] ≤ D → D ≤ graph [1359873,364544,6195,20642,20642,8515,2322,12804,6273,673,168,804,396,63,0,0,0,0,4,1,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_175_root
  change D ≤ graph [1359873,364544,6195,20642,20642,8515,2322,12804,6273,673,168,804,396,63,0,0,0,0,4,1,0,0] at hDU
  let masks : List Nat := [10791,0,0,0,0,13389,0,0,10805,0,0,0,0,3310632,0,0,0,0,0,3228240,1057381,0,0,12997,0,0,10673,0,0,0,11557,0,0,0,12745,0,0,0,0,13001,0,0,0,0,11057,0,0,0,0,11569,0,0,13513,0,11813,0,0,0,10649,0,0,14917,0,0,0,0,0,0,0,0,12697,14885,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,49562,3228228,0,0,1327665,0,0,0,0,152649,280977,0,24985,49561,0,3310628,0,0,0,2655306,0,0,100914,0,0,561546,41370,0,330277,0,0,3260440,0,0,0,0,100658,0,2688070,0,0,76326,0,0,0,660550,0,0,3325976,0,0,151753,0,1442341,0,0,0,1188901,0,0,0,0,330278,0,278937,0,0,283329,0,0,0,1442853,0,0,272933,0,0,0,0,660549,0,0,0,557466,560418,0,0,0,2687558,0,0,0,537670,0,0,0,0,0,0,3154470,0,0,0,0,0,1327761,0,0,0,1059365,1061445,0,0,0,0,0,0,3802180,3154469,0,0,0,0,0,0,0,2655498,0,0,2107942,2110022,0,0,0,0,0,3473956,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [1359873,364544,6195,20642,20642,8515,2322,4612,4225,673,168,772,388,63,0,0,0,0,4,1,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  exact leaf_175_root lo hDU

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_181 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [63,757760,274816,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] →
    (graph [63,757760,274816,68352,81968,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] ≤ D → D ≤ graph [63,757760,274816,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] → False) →
    (graph [63,757760,270720,68352,81968,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] ≤ D → D ≤ graph [63,757760,270720,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] → False) →
    (graph [62,757760,274816,68352,82224,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] ≤ D → D ≤ graph [62,757760,274816,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] → False) →
    (graph [62,757760,270720,68352,82224,26660,8353,9888,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] ≤ D → D ≤ graph [62,757760,270720,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] → False) →
    (graph [62,757760,270720,68352,82224,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] ≤ D → D ≤ graph [62,757760,270720,84736,82224,26660,8865,1696,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] → False) →
    (graph [62,757760,274816,68352,82224,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] ≤ D → D ≤ graph [62,757760,274816,84736,82224,26660,8865,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] → False) →
    (graph [62,757760,270720,68352,82224,26660,8865,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] ≤ D → D ≤ graph [62,757760,270720,84736,82224,26660,8865,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] → False) →
    (graph [62,757760,270720,68352,82224,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] ≤ D → D ≤ graph [62,757760,270720,84736,82224,26660,8353,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] → False) →
    (graph [62,757760,270720,84736,81968,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] ≤ D → D ≤ graph [62,757760,274816,84736,81968,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] → False) →
    (graph [62,757760,270720,68352,81968,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] ≤ D → D ≤ graph [62,757760,274816,68352,81968,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] → False) →
    (graph [62,757760,270720,68352,81968,26660,8865,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] ≤ D → D ≤ graph [62,757760,274816,84736,81968,26660,8865,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] → False) →
    (graph [62,757760,270720,68352,81968,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] ≤ D → D ≤ graph [62,757760,274816,84736,81968,26660,8353,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] → False) →
    False := by
  intro graph D hI hDU leaf_181_11 leaf_181_10 leaf_181_0111 leaf_181_01101 leaf_181_01100 leaf_181_0101 leaf_181_01001 leaf_181_01000 leaf_181_0011 leaf_181_0010 leaf_181_0001 leaf_181_0000
  change D ≤ graph [63,757760,274816,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] at hDU
  let masks : List Nat := [0,1712389,0,526217,0,0,1132689,0,0,0,2111009,0,0,0,0,534337,0,0,0,0,0,0,0,0,0,0,0,254,0,0,0,0,0,382,0,0,0,0,0,0,638,0,0,0,0,0,0,1646,0,66746,0,0,0,0,0,0,0,2398,0,0,67770,0,0,0,528257,0,0,0,0,4286,0,0,12902,0,1053078,0,0,1136769,0,0,0,8814,0,0,0,534401,0,0,0,1222913,0,0,16574,0,0,0,0,2771016,0,1591681,0,0,0,0,2388481,0,0,0,35162,0,0,0,102578,0,2143745,0,0,0,0,1296385,0,0,65726,0,0,0,0,0,1280257,2445825,0,0,0,2208769,0,0,0,131422,0,0,0,2531424,0,1706369,0,3023361,2329601,0,1486849,0,0,0,0,0,270950,0,0,0,0,0,1396865,1483009,0,2373121,1525761,0,0,0,0,0,0,0,525134,0,0,655708,541356,0,0,0,0,0,0,2635265,0,0,1739009,1656961,0,0,0,0,0,1048990,0,1052854,1083730,0,0,0,1576321,0,0,0,0,0,0,0,0,0,0,2098794,2368100,0,2312216,0,0,0,2631425,0,0,0,0,0,0,0,0,0,0,0,3360769]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [62,757760,270720,68352,81968,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  by_cases splitroot : D.Adj 1 0
  · have lo1 : graph [63,757760,270720,68352,81968,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] ≤ D := by
      apply branch_lower lo splitroot
      dsimp only [graph]
      decide +kernel
    by_cases split1 : D.Adj 15 2
    · have lo11 : graph [63,757760,274816,68352,81968,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] ≤ D := by
        apply branch_lower lo1 split1
        dsimp only [graph]
        decide +kernel
      exact leaf_181_11 lo11 hDU
    · have hi10 : D ≤ graph [63,757760,270720,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] := by
        apply branch_upper hDU split1
        dsimp only [graph]
        decide +kernel
      exact leaf_181_10 lo1 hi10
  · have hi0 : D ≤ graph [62,757760,274816,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] := by
      apply branch_upper hDU splitroot
      dsimp only [graph]
      decide +kernel
    by_cases split0 : D.Adj 13 4
    · have lo01 : graph [62,757760,270720,68352,82224,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] ≤ D := by
        apply branch_lower lo split0
        dsimp only [graph]
        decide +kernel
      by_cases split01 : D.Adj 14 10
      · have lo011 : graph [62,757760,270720,68352,82224,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] ≤ D := by
          apply branch_lower lo01 split01
          dsimp only [graph]
          decide +kernel
        by_cases split011 : D.Adj 15 2
        · have lo0111 : graph [62,757760,274816,68352,82224,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] ≤ D := by
            apply branch_lower lo011 split011
            dsimp only [graph]
            decide +kernel
          exact leaf_181_0111 lo0111 hi0
        · have hi0110 : D ≤ graph [62,757760,270720,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] := by
            apply branch_upper hi0 split011
            dsimp only [graph]
            decide +kernel
          by_cases split0110 : D.Adj 21 7
          · have lo01101 : graph [62,757760,270720,68352,82224,26660,8353,9888,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] ≤ D := by
              apply branch_lower lo011 split0110
              dsimp only [graph]
              decide +kernel
            exact leaf_181_01101 lo01101 hi0110
          · have hi01100 : D ≤ graph [62,757760,270720,84736,82224,26660,8865,1696,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] := by
              apply branch_upper hi0110 split0110
              dsimp only [graph]
              decide +kernel
            exact leaf_181_01100 lo011 hi01100
      · have hi010 : D ≤ graph [62,757760,274816,84736,82224,26660,8865,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] := by
          apply branch_upper hi0 split01
          dsimp only [graph]
          decide +kernel
        by_cases split010 : D.Adj 15 2
        · have lo0101 : graph [62,757760,274816,68352,82224,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] ≤ D := by
            apply branch_lower lo01 split010
            dsimp only [graph]
            decide +kernel
          exact leaf_181_0101 lo0101 hi010
        · have hi0100 : D ≤ graph [62,757760,270720,84736,82224,26660,8865,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] := by
            apply branch_upper hi010 split010
            dsimp only [graph]
            decide +kernel
          by_cases split0100 : D.Adj 16 6
          · have lo01001 : graph [62,757760,270720,68352,82224,26660,8865,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] ≤ D := by
              apply branch_lower lo01 split0100
              dsimp only [graph]
              decide +kernel
            exact leaf_181_01001 lo01001 hi0100
          · have hi01000 : D ≤ graph [62,757760,270720,84736,82224,26660,8353,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] := by
              apply branch_upper hi0100 split0100
              dsimp only [graph]
              decide +kernel
            exact leaf_181_01000 lo01 hi01000
    · have hi00 : D ≤ graph [62,757760,274816,84736,81968,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] := by
        apply branch_upper hi0 split0
        dsimp only [graph]
        decide +kernel
      by_cases split00 : D.Adj 14 10
      · have lo001 : graph [62,757760,270720,68352,81968,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] ≤ D := by
          apply branch_lower lo split00
          dsimp only [graph]
          decide +kernel
        by_cases split001 : D.Adj 18 3
        · have lo0011 : graph [62,757760,270720,84736,81968,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] ≤ D := by
            apply branch_lower lo001 split001
            dsimp only [graph]
            decide +kernel
          exact leaf_181_0011 lo0011 hi00
        · have hi0010 : D ≤ graph [62,757760,274816,68352,81968,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] := by
            apply branch_upper hi00 split001
            dsimp only [graph]
            decide +kernel
          exact leaf_181_0010 lo001 hi0010
      · have hi000 : D ≤ graph [62,757760,274816,84736,81968,26660,8865,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] := by
          apply branch_upper hi00 split00
          dsimp only [graph]
          decide +kernel
        by_cases split000 : D.Adj 16 6
        · have lo0001 : graph [62,757760,270720,68352,81968,26660,8865,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] ≤ D := by
            apply branch_lower lo split000
            dsimp only [graph]
            decide +kernel
          exact leaf_181_0001 lo0001 hi000
        · have hi0000 : D ≤ graph [62,757760,274816,84736,81968,26660,8353,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] := by
            apply branch_upper hi000 split000
            dsimp only [graph]
            decide +kernel
          exact leaf_181_0000 lo hi0000

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_182 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [63,983552,417856,50752,54784,37444,1633,4167,1172,808,1106,45,192,192,66,1,2,1,0,0,0,0] →
    (graph [63,983552,155712,17984,54784,36932,1633,4167,1172,808,1106,45,192,192,64,1,2,1,0,0,0,0] ≤ D → D ≤ graph [63,983552,417856,50752,54784,37444,1633,4167,1172,808,1106,45,192,192,66,1,2,1,0,0,0,0] → False) →
    (graph [63,983552,155712,17984,54784,36932,1633,4167,1172,808,1104,45,192,192,64,1,2,1,0,0,0,0] ≤ D → D ≤ graph [63,983552,417856,50752,54784,37444,1633,4167,1172,808,1104,45,192,192,66,1,2,1,0,0,0,0] → False) →
    (graph [55,983552,155712,17984,54784,36932,1633,4167,1172,808,1106,45,192,192,64,1,2,1,0,0,0,0] ≤ D → D ≤ graph [55,983552,417856,50752,54784,37444,1633,4167,1172,808,1106,45,192,192,66,1,2,1,0,0,0,0] → False) →
    (graph [55,983552,155712,17984,54784,37444,1633,4167,1172,808,1104,45,192,192,64,1,2,1,0,0,0,0] ≤ D → D ≤ graph [55,983552,417856,50752,54784,37444,1633,4167,1172,808,1104,45,192,192,66,1,2,1,0,0,0,0] → False) →
    (graph [55,983552,155712,17984,54784,36932,1633,4167,1172,808,1104,45,192,192,64,1,2,1,0,0,0,0] ≤ D → D ≤ graph [55,983552,417856,50752,54784,36932,1633,4167,1172,808,1104,45,192,192,66,1,2,1,0,0,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_182_11 leaf_182_10 leaf_182_01 leaf_182_001 leaf_182_000
  change D ≤ graph [63,983552,417856,50752,54784,37444,1633,4167,1172,808,1106,45,192,192,66,1,2,1,0,0,0,0] at hDU
  let masks : List Nat := [176259,796805,0,2265225,0,0,0,0,0,0,600225,0,0,0,0,1066817,0,0,0,0,0,0,0,0,0,0,0,254,0,0,0,0,0,382,0,2265473,0,0,638,0,0,0,0,2298497,0,0,0,0,1150,0,0,0,601217,0,0,0,2174,0,0,0,0,0,0,265556,0,0,0,0,0,0,0,4286,4446,0,0,0,0,276628,0,0,0,8382,0,0,9334,0,192769,75314,0,0,0,0,0,0,49486,17526,0,0,192641,0,0,0,814081,0,0,0,0,0,0,33118,0,0,0,0,185089,1361153,829569,0,0,0,0,0,65726,0,0,0,66170,0,2298625,0,0,0,0,0,0,241793,0,0,168078,0,196794,0,3277640,0,0,0,1197825,731265,0,0,0,0,0,0,263510,0,3440968,0,265332,0,0,0,1328897,0,0,0,0,0,0,862337,438401,0,541798,0,0,527476,0,0,0,1852673,1641985,0,0,700545,0,0,0,0,0,0,0,1245738,1576036,0,1051256,0,0,3737729,0,0,0,0,1200897,1649665,0,0,0,0,0,0,0,2098010,0,0,0,2099832,0,0,0,0,3214849,0,0,2697345,2249473,0,0,0,0,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [55,983552,155712,17984,54784,36932,1633,4167,1172,808,1104,45,192,192,64,1,2,1,0,0,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  by_cases splitroot : D.Adj 4 0
  · have lo1 : graph [63,983552,155712,17984,54784,36932,1633,4167,1172,808,1104,45,192,192,64,1,2,1,0,0,0,0] ≤ D := by
      apply branch_lower lo splitroot
      dsimp only [graph]
      decide +kernel
    by_cases split1 : D.Adj 12 10
    · have lo11 : graph [63,983552,155712,17984,54784,36932,1633,4167,1172,808,1106,45,192,192,64,1,2,1,0,0,0,0] ≤ D := by
        apply branch_lower lo1 split1
        dsimp only [graph]
        decide +kernel
      exact leaf_182_11 lo11 hDU
    · have hi10 : D ≤ graph [63,983552,417856,50752,54784,37444,1633,4167,1172,808,1104,45,192,192,66,1,2,1,0,0,0,0] := by
        apply branch_upper hDU split1
        dsimp only [graph]
        decide +kernel
      exact leaf_182_10 lo1 hi10
  · have hi0 : D ≤ graph [55,983552,417856,50752,54784,37444,1633,4167,1172,808,1106,45,192,192,66,1,2,1,0,0,0,0] := by
      apply branch_upper hDU splitroot
      dsimp only [graph]
      decide +kernel
    by_cases split0 : D.Adj 12 10
    · have lo01 : graph [55,983552,155712,17984,54784,36932,1633,4167,1172,808,1106,45,192,192,64,1,2,1,0,0,0,0] ≤ D := by
        apply branch_lower lo split0
        dsimp only [graph]
        decide +kernel
      exact leaf_182_01 lo01 hi0
    · have hi00 : D ≤ graph [55,983552,417856,50752,54784,37444,1633,4167,1172,808,1104,45,192,192,66,1,2,1,0,0,0,0] := by
        apply branch_upper hi0 split0
        dsimp only [graph]
        decide +kernel
      by_cases split00 : D.Adj 15 5
      · have lo001 : graph [55,983552,155712,17984,54784,37444,1633,4167,1172,808,1104,45,192,192,64,1,2,1,0,0,0,0] ≤ D := by
          apply branch_lower lo split00
          dsimp only [graph]
          decide +kernel
        exact leaf_182_001 lo001 hi00
      · have hi000 : D ≤ graph [55,983552,417856,50752,54784,36932,1633,4167,1172,808,1104,45,192,192,66,1,2,1,0,0,0,0] := by
          apply branch_upper hi00 split00
          dsimp only [graph]
          decide +kernel
        exact leaf_182_000 lo hi000

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_183 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [63,829440,361504,173088,100928,12880,10785,8780,2380,295,548,130,257,1,9,1,5,1,0,1,0,0] →
    (graph [63,829440,361504,42016,100928,12368,10785,8268,2380,291,548,130,257,1,9,1,5,1,0,1,0,0] ≤ D → D ≤ graph [63,829440,361504,173088,100928,12880,10785,8780,2380,295,548,130,257,1,9,1,5,1,0,1,0,0] → False) →
    (graph [63,829440,361504,42016,100928,12368,10785,8268,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] ≤ D → D ≤ graph [63,829440,361504,173088,100928,12880,10785,8780,2376,295,548,130,257,1,9,1,5,1,0,1,0,0] → False) →
    (graph [62,829440,361504,42016,100928,12368,10785,8268,2380,291,548,130,257,1,9,1,5,1,0,1,0,0] ≤ D → D ≤ graph [62,829440,361504,173088,100928,12880,10785,8780,2380,295,548,130,257,1,9,1,5,1,0,1,0,0] → False) →
    (graph [62,829440,361504,42016,100928,12368,10785,8268,2376,295,548,130,257,1,9,1,5,1,0,1,0,0] ≤ D → D ≤ graph [62,829440,361504,173088,100928,12880,10785,8780,2376,295,548,130,257,1,9,1,5,1,0,1,0,0] → False) →
    (graph [62,829440,361504,42016,100928,12368,10785,8780,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] ≤ D → D ≤ graph [62,829440,361504,173088,100928,12880,10785,8780,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] → False) →
    (graph [62,829440,361504,42016,100928,12368,10785,8268,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] ≤ D → D ≤ graph [62,829440,361504,173088,100928,12880,10785,8268,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_183_11 leaf_183_10 leaf_183_01 leaf_183_001 leaf_183_0001 leaf_183_0000
  change D ≤ graph [63,829440,361504,173088,100928,12880,10785,8780,2380,295,548,130,257,1,9,1,5,1,0,1,0,0] at hDU
  let masks : List Nat := [0,154629,0,336265,0,0,533393,0,0,0,74657,0,0,0,0,2630465,0,0,0,0,0,0,0,0,0,0,0,254,0,0,382,0,0,0,0,0,0,0,0,638,0,0,0,0,0,0,0,0,0,0,1150,0,824449,0,2639617,0,0,0,0,2174,0,0,1349761,0,3230209,0,0,0,0,0,0,4286,5214,0,266650,0,0,0,0,8570,1122476,0,0,0,0,0,0,0,2893057,3319809,831617,0,0,0,18542,17014,0,0,82598,0,0,0,0,0,2188033,0,33886,0,0,0,0,0,0,827777,2793985,0,0,0,0,187393,0,0,0,0,65726,0,67694,0,0,0,72718,0,0,0,0,1413249,0,131702,0,164956,0,0,0,0,2761473,0,0,0,0,0,0,0,3351041,0,0,266398,0,0,262586,263514,0,0,336769,0,0,0,0,2901249,0,0,433153,0,0,689236,525658,0,525170,0,0,0,0,0,678913,0,0,0,0,598913,0,0,0,1114286,0,0,1085596,0,1196644,0,1123201,0,1203201,0,0,0,0,0,0,0,0,1872001,0,2114402,2245220,0,2106224,0,0,2171777,0,0,0,0,2251777,0,0,0,0,0,0,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [62,829440,361504,42016,100928,12368,10785,8268,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  by_cases splitroot : D.Adj 1 0
  · have lo1 : graph [63,829440,361504,42016,100928,12368,10785,8268,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] ≤ D := by
      apply branch_lower lo splitroot
      dsimp only [graph]
      decide +kernel
    by_cases split1 : D.Adj 11 8
    · have lo11 : graph [63,829440,361504,42016,100928,12368,10785,8268,2380,291,548,130,257,1,9,1,5,1,0,1,0,0] ≤ D := by
        apply branch_lower lo1 split1
        dsimp only [graph]
        decide +kernel
      exact leaf_183_11 lo11 hDU
    · have hi10 : D ≤ graph [63,829440,361504,173088,100928,12880,10785,8780,2376,295,548,130,257,1,9,1,5,1,0,1,0,0] := by
        apply branch_upper hDU split1
        dsimp only [graph]
        decide +kernel
      exact leaf_183_10 lo1 hi10
  · have hi0 : D ≤ graph [62,829440,361504,173088,100928,12880,10785,8780,2380,295,548,130,257,1,9,1,5,1,0,1,0,0] := by
      apply branch_upper hDU splitroot
      dsimp only [graph]
      decide +kernel
    by_cases split0 : D.Adj 11 8
    · have lo01 : graph [62,829440,361504,42016,100928,12368,10785,8268,2380,291,548,130,257,1,9,1,5,1,0,1,0,0] ≤ D := by
        apply branch_lower lo split0
        dsimp only [graph]
        decide +kernel
      exact leaf_183_01 lo01 hi0
    · have hi00 : D ≤ graph [62,829440,361504,173088,100928,12880,10785,8780,2376,295,548,130,257,1,9,1,5,1,0,1,0,0] := by
        apply branch_upper hi0 split0
        dsimp only [graph]
        decide +kernel
      by_cases split00 : D.Adj 12 9
      · have lo001 : graph [62,829440,361504,42016,100928,12368,10785,8268,2376,295,548,130,257,1,9,1,5,1,0,1,0,0] ≤ D := by
          apply branch_lower lo split00
          dsimp only [graph]
          decide +kernel
        exact leaf_183_001 lo001 hi00
      · have hi000 : D ≤ graph [62,829440,361504,173088,100928,12880,10785,8780,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] := by
          apply branch_upper hi00 split00
          dsimp only [graph]
          decide +kernel
        by_cases split000 : D.Adj 17 7
        · have lo0001 : graph [62,829440,361504,42016,100928,12368,10785,8780,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] ≤ D := by
            apply branch_lower lo split000
            dsimp only [graph]
            decide +kernel
          exact leaf_183_0001 lo0001 hi000
        · have hi0000 : D ≤ graph [62,829440,361504,173088,100928,12880,10785,8268,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] := by
            apply branch_upper hi000 split000
            dsimp only [graph]
            decide +kernel
          exact leaf_183_0000 lo hi0000

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_184 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [63,796736,345344,209920,90640,21072,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] →
    (graph [63,796736,83200,209920,90640,21072,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] ≤ D → D ≤ graph [63,796736,345344,209920,90640,21072,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] → False) →
    (graph [63,796736,83200,209920,90640,16976,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] ≤ D → D ≤ graph [63,796736,345344,209920,90640,16976,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] → False) →
    (graph [59,796736,83200,209920,90640,16976,6177,8270,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] ≤ D → D ≤ graph [59,796736,345344,209920,90640,21072,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] → False) →
    (graph [59,796736,83200,209920,90640,16976,6689,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] ≤ D → D ≤ graph [59,796736,345344,209920,90640,21072,6689,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] → False) →
    (graph [59,796736,83200,209920,90640,16976,6689,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] ≤ D → D ≤ graph [59,796736,345344,209920,90640,21072,6689,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] → False) →
    (graph [59,796736,83200,209920,90640,16976,6177,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] ≤ D → D ≤ graph [59,796736,345344,209920,90640,21072,6177,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] → False) →
    (graph [59,796736,83200,209920,90640,16976,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] ≤ D → D ≤ graph [59,796736,345344,209920,90640,21072,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_184_11 leaf_184_10 leaf_184_01 leaf_184_0011 leaf_184_0010 leaf_184_0001 leaf_184_0000
  change D ≤ graph [63,796736,345344,209920,90640,21072,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] at hDU
  let masks : List Nat := [725123,1343877,0,0,0,0,1089937,0,0,0,598433,0,0,0,0,2138945,0,0,0,0,0,0,0,0,0,0,0,254,0,382,0,0,0,0,0,0,0,0,0,0,638,0,0,295820,0,0,0,0,0,0,1150,0,1348737,2393857,0,0,0,2174,0,0,0,0,0,2140929,0,0,0,0,0,0,0,4286,5214,0,1347969,267790,0,0,0,10362,8572,0,0,0,0,0,0,0,2141697,0,733313,0,0,0,17006,149618,0,0,741505,2900737,0,0,0,0,2648577,0,33886,0,0,0,33148,0,0,0,0,0,0,0,0,2149889,0,0,0,65726,0,0,0,0,0,2695937,1266689,743425,0,0,0,1155457,0,0,196790,133242,0,0,0,0,729473,2248193,0,0,0,0,0,0,0,0,0,0,0,266398,0,263758,0,0,0,0,2379265,0,1352065,0,0,0,987265,0,0,790670,0,721074,0,526954,0,0,0,2641409,0,0,0,0,2663169,0,0,0,0,1118358,0,1081692,0,1114548,0,0,0,3187457,0,1203201,0,0,0,0,0,0,0,1646977,0,2116194,0,2106216,2238576,0,0,3187073,0,0,0,0,2251777,0,0,0,0,0,0,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [59,796736,83200,209920,90640,16976,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  by_cases splitroot : D.Adj 3 0
  · have lo1 : graph [63,796736,83200,209920,90640,16976,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] ≤ D := by
      apply branch_lower lo splitroot
      dsimp only [graph]
      decide +kernel
    by_cases split1 : D.Adj 18 5
    · have lo11 : graph [63,796736,83200,209920,90640,21072,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] ≤ D := by
        apply branch_lower lo1 split1
        dsimp only [graph]
        decide +kernel
      exact leaf_184_11 lo11 hDU
    · have hi10 : D ≤ graph [63,796736,345344,209920,90640,16976,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] := by
        apply branch_upper hDU split1
        dsimp only [graph]
        decide +kernel
      exact leaf_184_10 lo1 hi10
  · have hi0 : D ≤ graph [59,796736,345344,209920,90640,21072,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] := by
      apply branch_upper hDU splitroot
      dsimp only [graph]
      decide +kernel
    by_cases split0 : D.Adj 11 7
    · have lo01 : graph [59,796736,83200,209920,90640,16976,6177,8270,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] ≤ D := by
        apply branch_lower lo split0
        dsimp only [graph]
        decide +kernel
      exact leaf_184_01 lo01 hi0
    · have hi00 : D ≤ graph [59,796736,345344,209920,90640,21072,6689,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] := by
        apply branch_upper hi0 split0
        dsimp only [graph]
        decide +kernel
      by_cases split00 : D.Adj 16 6
      · have lo001 : graph [59,796736,83200,209920,90640,16976,6689,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] ≤ D := by
          apply branch_lower lo split00
          dsimp only [graph]
          decide +kernel
        by_cases split001 : D.Adj 17 15
        · have lo0011 : graph [59,796736,83200,209920,90640,16976,6689,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] ≤ D := by
            apply branch_lower lo001 split001
            dsimp only [graph]
            decide +kernel
          exact leaf_184_0011 lo0011 hi00
        · have hi0010 : D ≤ graph [59,796736,345344,209920,90640,21072,6689,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] := by
            apply branch_upper hi00 split001
            dsimp only [graph]
            decide +kernel
          exact leaf_184_0010 lo001 hi0010
      · have hi000 : D ≤ graph [59,796736,345344,209920,90640,21072,6177,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] := by
          apply branch_upper hi00 split00
          dsimp only [graph]
          decide +kernel
        by_cases split000 : D.Adj 17 15
        · have lo0001 : graph [59,796736,83200,209920,90640,16976,6177,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] ≤ D := by
            apply branch_lower lo split000
            dsimp only [graph]
            decide +kernel
          exact leaf_184_0001 lo0001 hi000
        · have hi0000 : D ≤ graph [59,796736,345344,209920,90640,21072,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] := by
            apply branch_upper hi000 split000
            dsimp only [graph]
            decide +kernel
          exact leaf_184_0000 lo hi0000

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_185 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [63,697344,303488,91648,82224,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] →
    (graph [63,697344,303488,75264,82224,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] ≤ D → D ≤ graph [63,697344,303488,91648,82224,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] → False) →
    (graph [63,697344,303488,75264,81968,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] ≤ D → D ≤ graph [63,697344,303488,91648,81968,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] → False) →
    (graph [62,697344,303488,75264,82224,25666,8594,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] ≤ D → D ≤ graph [62,697344,303488,91648,82224,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] → False) →
    (graph [62,697344,303488,75264,82224,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] ≤ D → D ≤ graph [62,697344,303488,91648,82224,25666,8338,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] → False) →
    (graph [62,697344,303488,75264,81968,25666,8594,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] ≤ D → D ≤ graph [62,697344,303488,91648,81968,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] → False) →
    (graph [62,697344,303488,75264,81968,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] ≤ D → D ≤ graph [62,697344,303488,91648,81968,25666,8338,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] → False) →
    False := by
  intro graph D hI hDU leaf_185_11 leaf_185_10 leaf_185_011 leaf_185_010 leaf_185_001 leaf_185_000
  change D ≤ graph [63,697344,303488,91648,82224,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] at hDU
  let masks : List Nat := [0,1577349,0,526217,0,0,1055121,0,0,0,2123297,0,0,0,0,534209,0,0,0,0,0,0,0,0,0,0,254,0,0,0,0,0,0,0,382,0,0,0,0,0,638,0,0,0,0,0,0,1646,0,3386,0,0,0,0,0,0,0,2366,0,0,0,67802,0,0,3882,0,0,4318,0,0,0,37180,0,0,0,2789889,2432001,0,0,0,0,8814,0,0,0,0,534401,0,0,2386945,1650817,0,0,0,16702,0,0,25190,1065366,0,0,0,0,1104129,0,0,33086,0,0,0,0,0,1087873,0,0,2411521,0,0,2286081,0,0,0,65758,0,0,336994,0,0,1120641,599681,0,0,0,0,2444289,1415169,0,139878,0,2822216,0,0,0,1773697,1741057,0,2254337,1480705,0,0,0,0,0,0,0,442420,0,0,0,0,1382529,1349889,2385409,0,0,0,0,0,0,0,0,0,525006,0,0,528604,557868,0,0,0,0,0,1579393,0,0,2647553,0,0,0,2958337,0,0,0,1048990,0,1065270,1511504,0,0,0,1647745,0,0,0,0,0,0,0,0,0,0,2098794,2237028,0,2410544,0,0,2631297,0,0,0,0,0,0,0,0,0,0,0,0,3446785]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [62,697344,303488,75264,81968,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  by_cases splitroot : D.Adj 1 0
  · have lo1 : graph [63,697344,303488,75264,81968,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] ≤ D := by
      apply branch_lower lo splitroot
      dsimp only [graph]
      decide +kernel
    by_cases split1 : D.Adj 13 4
    · have lo11 : graph [63,697344,303488,75264,82224,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] ≤ D := by
        apply branch_lower lo1 split1
        dsimp only [graph]
        decide +kernel
      exact leaf_185_11 lo11 hDU
    · have hi10 : D ≤ graph [63,697344,303488,91648,81968,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] := by
        apply branch_upper hDU split1
        dsimp only [graph]
        decide +kernel
      exact leaf_185_10 lo1 hi10
  · have hi0 : D ≤ graph [62,697344,303488,91648,82224,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] := by
      apply branch_upper hDU splitroot
      dsimp only [graph]
      decide +kernel
    by_cases split0 : D.Adj 13 4
    · have lo01 : graph [62,697344,303488,75264,82224,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] ≤ D := by
        apply branch_lower lo split0
        dsimp only [graph]
        decide +kernel
      by_cases split01 : D.Adj 15 6
      · have lo011 : graph [62,697344,303488,75264,82224,25666,8594,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] ≤ D := by
          apply branch_lower lo01 split01
          dsimp only [graph]
          decide +kernel
        exact leaf_185_011 lo011 hi0
      · have hi010 : D ≤ graph [62,697344,303488,91648,82224,25666,8338,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] := by
          apply branch_upper hi0 split01
          dsimp only [graph]
          decide +kernel
        exact leaf_185_010 lo01 hi010
    · have hi00 : D ≤ graph [62,697344,303488,91648,81968,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] := by
        apply branch_upper hi0 split0
        dsimp only [graph]
        decide +kernel
      by_cases split00 : D.Adj 15 6
      · have lo001 : graph [62,697344,303488,75264,81968,25666,8594,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] ≤ D := by
          apply branch_lower lo split00
          dsimp only [graph]
          decide +kernel
        exact leaf_185_001 lo001 hi00
      · have hi000 : D ≤ graph [62,697344,303488,91648,81968,25666,8338,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] := by
          apply branch_upper hi00 split00
          dsimp only [graph]
          decide +kernel
        exact leaf_185_000 lo hi000

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_186 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [63,831488,418816,50496,24912,21026,21026,2822,835,2068,517,548,145,3,2,9,2,0,4,1,0,0] →
    (graph [63,831488,418816,50496,24912,21026,21026,2822,835,2068,517,548,145,3,2,9,2,0,4,1,0,0] ≤ D → D ≤ graph [63,831488,418816,50496,24912,21026,21026,2822,835,2068,517,548,145,3,2,9,2,0,4,1,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_186_root
  change D ≤ graph [63,831488,418816,50496,24912,21026,21026,2822,835,2068,517,548,145,3,2,9,2,0,4,1,0,0] at hDU
  let masks : List Nat := [596227,301189,0,1059209,0,0,2118033,0,0,0,2642209,0,0,0,0,1321153,0,0,0,0,0,0,0,0,0,0,254,0,0,0,0,0,0,0,382,0,0,0,0,0,638,0,0,1321601,600833,0,0,0,1150,0,0,0,316545,2643201,0,0,0,0,0,2270,2670,0,0,0,0,265798,0,0,0,4414,0,0,5238,0,0,529958,0,0,0,0,8814,0,74042,0,0,0,0,0,730625,0,604417,0,17526,0,49372,0,0,0,0,0,443905,0,317569,0,3170689,0,32990,0,0,0,50292,0,0,2150785,0,0,0,0,1353857,0,0,0,65854,0,0,0,74346,1124737,0,0,0,0,0,0,2707713,3375128,0,139882,148596,0,0,0,0,1491073,2826497,0,0,731649,447489,0,0,0,0,0,0,0,264398,311508,263782,0,0,1321345,0,0,0,0,0,0,0,984577,0,0,0,0,598314,528694,0,525926,2642305,0,0,0,0,0,0,0,951809,0,0,0,0,1059018,1081564,0,0,3211576,0,0,0,0,1476097,0,3166593,0,0,0,0,0,0,1648897,0,2163002,2117940,0,0,0,3178712,0,0,2819585,0,3156353,0,0,0,0,0,0,2412673,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [63,831488,418816,50496,24912,21026,21026,2822,835,2068,517,548,145,3,2,9,2,0,4,1,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  exact leaf_186_root lo hDU

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_187 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [63,570368,145664,152096,114824,28706,7240,9120,422,661,1552,515,40,65,8,12,4,4,0,0,0,0] →
    (graph [63,570368,145664,152096,114824,28706,7240,9120,422,661,1552,515,40,65,8,12,4,4,0,0,0,0] ≤ D → D ≤ graph [63,570368,145664,152096,114824,28706,7240,9120,422,661,1552,515,40,65,8,12,4,4,0,0,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_187_root
  change D ≤ graph [63,570368,145664,152096,114824,28706,7240,9120,422,661,1552,515,40,65,8,12,4,4,0,0,0,0] at hDU
  let masks : List Nat := [1311619,2368261,0,1577353,0,0,216081,0,0,0,2138913,0,0,0,0,3179329,0,0,0,0,0,0,0,0,0,0,254,0,0,0,0,0,382,0,0,0,0,0,0,638,0,0,0,0,0,0,0,0,0,0,0,1150,0,525710,9782,0,0,2270,0,0,68210,0,0,1313665,0,0,0,4462,0,0,136252,0,0,0,0,2142977,0,547969,0,0,0,9278,0,0,8822,270998,0,0,0,470017,0,0,18650,148540,0,0,0,0,0,1593729,1165825,0,0,0,685057,0,98930,37228,0,0,0,0,51416,0,0,248833,0,0,0,0,0,0,66166,114808,0,0,0,1378945,2204417,0,0,0,2338817,0,0,0,0,132158,0,0,0,0,180344,674945,2273537,2335233,0,0,0,0,0,0,0,0,0,0,263326,0,270902,262870,0,0,0,0,0,1839489,0,806017,2401025,0,0,0,0,0,0,525470,660524,524750,0,0,1835905,0,0,0,0,0,2666753,740353,0,0,0,0,1049038,0,1050842,1085800,0,0,0,0,1592449,0,0,3187457,0,0,0,1296385,0,0,0,2098022,0,2101612,2196080,0,0,3408769,0,0,2765825,3246593,0,0,0,0,0,0,0,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [63,570368,145664,152096,114824,28706,7240,9120,422,661,1552,515,40,65,8,12,4,4,0,0,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  exact leaf_187_root lo hDU

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_188 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [63,937984,443392,57480,26760,33488,8596,4514,4450,2433,800,531,146,33,8,12,1,0,0,0,0,0] →
    (graph [63,937984,443392,57480,26760,33488,8596,4514,4450,2433,800,531,146,33,8,12,1,0,0,0,0,0] ≤ D → D ≤ graph [63,937984,443392,57480,26760,33488,8596,4514,4450,2433,800,531,146,33,8,12,1,0,0,0,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_188_root
  change D ≤ graph [63,937984,443392,57480,26760,33488,8596,4514,4450,2433,800,531,146,33,8,12,1,0,0,0,0,0] at hDU
  let masks : List Nat := [396419,594693,0,78601,0,0,150673,0,0,0,788897,0,0,0,0,790977,0,0,0,0,0,0,0,0,254,0,0,0,0,0,0,0,382,0,0,0,0,0,0,0,0,0,638,2742,0,0,0,0,0,0,1150,0,0,5454,34334,0,0,0,2622,0,0,2294,0,0,0,0,0,0,0,0,5214,4462,0,0,0,0,0,792961,0,0,9310,0,0,1123112,0,2372737,0,0,0,175122,0,0,16958,0,0,0,0,2245840,0,1592065,0,0,0,119308,1171969,0,0,0,0,0,33342,33886,183425,111361,0,0,0,0,0,0,0,65902,0,0,82492,0,0,856449,0,0,2208769,1641217,0,0,0,0,0,0,131318,140378,0,0,0,0,919937,1231361,0,0,2495617,0,0,0,3383297,0,0,262630,274762,393458,0,0,0,0,1837825,0,0,0,0,412801,2405377,0,0,0,524774,0,590188,542900,0,0,0,0,0,674945,0,0,602881,0,1624577,0,0,0,0,1090074,1065532,0,0,0,1900896,1837441,0,0,1231873,0,1127169,0,0,0,0,0,0,0,0,2106458,2147356,0,0,3014880,0,0,2888065,2208257,0,2247809,0,0,0,0,0,0,0,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [63,937984,443392,57480,26760,33488,8596,4514,4450,2433,800,531,146,33,8,12,1,0,0,0,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  exact leaf_188_root lo hDU

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_189 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [63,992,299776,143936,45584,9986,12386,13824,4544,2596,904,402,26,19,64,16,2,2,0,0,0,0] →
    (graph [47,992,299776,143936,45584,9986,12386,13824,4544,2596,904,402,26,19,64,16,2,2,0,0,0,0] ≤ D → D ≤ graph [63,992,299776,143936,45584,9986,12386,13824,4544,2596,904,402,26,19,64,16,2,2,0,0,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_189_root
  change D ≤ graph [63,992,299776,143936,45584,9986,12386,13824,4544,2596,904,402,26,19,64,16,2,2,0,0,0,0] at hDU
  let masks : List Nat := [3682307,10117,0,19337,0,0,7569,0,0,0,0,0,0,0,0,412225,0,0,0,0,0,0,598166,0,0,0,9652,0,0,1589518,0,0,0,0,17356,0,0,1188390,0,0,10036,0,0,0,0,0,2110514,0,7480,0,0,0,0,0,0,0,313418,19148,0,0,0,0,0,0,0,0,0,0,528796,0,0,0,39128,0,0,8065,0,0,0,0,0,532892,0,0,74964,0,0,0,0,12161,0,0,0,0,0,541084,1065772,0,0,0,0,20353,0,1855745,1270273,0,0,245830,0,0,2523234,0,0,40321,444929,0,0,0,2335745,0,0,0,0,1654798,0,1253414,0,0,75649,0,0,2329601,3747841,0,0,0,0,0,0,442442,2326610,0,0,206465,412417,0,0,0,2268161,0,0,0,0,0,0,1851406,0,823322,0,0,281473,0,0,2399233,0,0,1847553,0,0,1524225,0,0,0,0,0,0,1839146,835658,0,0,1852161,537985,2922497,0,0,0,0,0,3874817,0,0,0,0,0,1646614,0,1261638,1585537,0,0,1254913,1329921,0,0,0,3969025,0,0,0,0,0,0,2695190,2658330,0,0,0,2137217,3682561,2303489,0,0,0,0,2541569,0,0,0,0,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [47,992,299776,143936,45584,9986,12386,13824,4544,2596,904,402,26,19,64,16,2,2,0,0,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  exact leaf_189_root lo hDU

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
theorem interval_190 :
    let graph := fun (b : List Nat) => SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)
    ∀ (D : SimpleGraph (Fin 22)), Dᶜ.CliqueFree 7 → D ≤ graph [63,992,50704,152704,49936,49744,5890,14400,6664,2496,452,424,74,134,5,4,8,0,0,0,0,0] →
    (graph [63,992,50704,152704,49936,49744,5890,14400,6664,2496,452,424,74,134,5,4,8,0,0,0,0,0] ≤ D → D ≤ graph [63,992,50704,152704,49936,49744,5890,14400,6664,2496,452,424,74,134,5,4,8,0,0,0,0,0] → False) →
    False := by
  intro graph D hI hDU leaf_190_root
  change D ≤ graph [63,992,50704,152704,49936,49744,5890,14400,6664,2496,452,424,74,134,5,4,8,0,0,0,0,0] at hDU
  let masks : List Nat := [1454083,20229,0,34697,0,0,69009,0,0,0,11169,0,0,0,0,7873,0,0,0,0,0,0,168090,34204,0,0,0,0,0,606502,0,0,0,0,19300,0,0,1606158,0,0,34588,0,0,0,0,0,2196502,0,0,0,68916,0,0,0,0,0,2365522,0,7384,0,0,0,0,0,0,0,0,0,1054284,0,0,13032,0,0,8065,0,0,0,0,0,533292,0,139704,0,0,0,0,0,12161,0,0,0,0,0,541484,84276,0,0,20353,0,0,0,0,1339458,0,0,0,0,0,0,557868,1082956,0,0,0,0,36737,0,1224714,2736134,0,0,0,99612,0,0,2165844,0,0,69505,0,0,2330642,876578,0,0,0,0,1736718,0,0,0,1192010,0,0,140200,230785,407681,0,0,1990657,0,0,0,0,868390,925738,0,0,0,0,330160,277121,2444289,0,0,0,0,3575809,0,0,0,0,0,0,2719766,0,3686470,754049,0,0,558860,551681,1978369,0,0,0,0,0,0,0,0,0,0,1216538,1712170,0,1087105,1598209,0,0,1068612,0,0,0,0,4014081,0,0,0,0,0,0,3702798,0,2703398,0,2104528,2182401,3184129,0,0,0,3551233,0,0,0,0,0,0,0]
  let witness (x y : Fin 22) : Nat :=
    masks.getD ((max x.val y.val)*((max x.val y.val)-1)/2 + min x.val y.val) 0
  have lo : graph [63,992,50704,152704,49936,49744,5890,14400,6664,2496,452,424,74,134,5,4,8,0,0,0,0,0] ≤ D := by
    apply certify_root_mask hDU hI witness
    dsimp only [graph, witness, masks]
    decide +kernel
  exact leaf_190_root lo hDU

end E151D5

/-! Integer dual certificates for the five contact rows of a degree-five vertex. -/

namespace E151Screen

lemma impossible_of_dual {lower upper : List (Nat × Nat)} (tests : List (Nat × Nat)) (L : Nat)
    (valid : ∀ z ∈ tests, (z.1, 6) ∈ upper)
    (each : ∀ p ∈ lower, p.2 ≤ 6 → L ≤ (tests.map (fun z => if p.1 &&& z.1 = 0 then z.2 else 0)).sum)
    (gap : (tests.map Prod.snd).sum < 5*L)
    (R K : Fin 5 → Nat) (mem : ∀ i, (R i,K i) ∈ lower) (size : ∀ i, K i ≤ 6)
    (cap : ∀ s, (s,6) ∈ upper → ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) : False := by
  have total (xs : List (Nat × Nat)) (hx : ∀ z ∈ xs, (z.1,6) ∈ upper) :
      (∑ i, (xs.map (fun z => if R i &&& z.1 = 0 then z.2 else 0)).sum) ≤ (xs.map Prod.snd).sum := by
    induction xs with
    | nil => simp
    | cons z xs ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      have hc := cap z.1 (hx z (by simp))
      have eq : (∑ i : Fin 5, if R i &&& z.1 = 0 then z.2 else 0) =
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& z.1 = 0).card * z.2 := by
        rw [← Finset.sum_filter]
        simp
      rw [eq]
      apply Nat.add_le_add _ (ih (fun w hw => hx w (List.mem_cons_of_mem _ hw)))
      simpa using Nat.mul_le_mul_right z.2 hc
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5)))
    (fun i _ => each (R i,K i) (mem i) (size i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at h
  have h' := total tests valid
  omega



lemma decode_sound :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    let decode : List Nat → Nat → Nat → Bool := List.foldr (fun m f x k =>
      if x % 2 == 0 then f (x/2) k else (k != 0) && (m &&& (x/2) == 0) && f (x/2) (k-1))
      (fun x k => (x == 0) && (k == 0))
    ∀ b x k, decode b x k = true → (x,k) ∈ enum b := by
  intro enum decode b
  induction b with
  | nil =>
    intro x k h
    change ((x == 0) && (k == 0)) = true at h
    simp only [Bool.and_eq_true,beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [enum]
  | cons m b ih =>
    intro x k h
    change (if x % 2 == 0 then decode b (x/2) k else
      (k != 0) && (m &&& (x/2) == 0) && decode b (x/2) (k-1)) = true at h
    change (x,k) ∈ (enum b).map _ ++ ((enum b).filter _).map _
    split at h
    next he =>
      simp only [beq_iff_eq] at he
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨(x/2,k),ih _ _ h,Prod.ext (by dsimp; omega) rfl⟩
    next he =>
      simp only [beq_iff_eq] at he
      simp only [Bool.and_eq_true,bne_iff_ne,beq_iff_eq] at h
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨(x/2,k-1),List.mem_filter.mpr ⟨ih _ _ h.2,?_⟩,Prod.ext (by dsimp; omega) (by dsimp; omega)⟩
      simpa only [beq_iff_eq] using h.1.2

lemma pass_sound :
    let pass : Nat → List (Nat × Nat) → Nat → Bool := fun x => List.foldr (fun z f n =>
      if x &&& z.1 == 0 then if z.2 ≥ n then true else f (n-z.2) else f n) (fun n => n == 0)
    ∀ x w n, pass x w n = true → n ≤ (w.map (fun z => if x &&& z.1 = 0 then z.2 else 0)).sum := by
  intro pass x w
  induction w with
  | nil =>
    intro n h
    change (n == 0) = true at h
    simp_all
  | cons z w ih =>
    intro n h
    change (if x &&& z.1 == 0 then if z.2 ≥ n then true else pass x w (n-z.2) else pass x w n) = true at h
    simp only [List.map_cons,List.sum_cons]
    by_cases hz : x &&& z.1 = 0
    · simp only [hz,beq_self_eq_true,if_true] at h ⊢
      split at h
      next => omega
      next => have := ih _ h; omega
    · simp only [hz,if_false,zero_add] at ⊢
      apply ih _
      simpa [hz] using h


lemma screen (b c : List Nat) (tests : List (Nat × Nat)) (L : Nat) :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    let decode : List Nat → Nat → Nat → Bool := List.foldr (fun m f x k =>
      if x % 2 == 0 then f (x/2) k else (k != 0) && (m &&& (x/2) == 0) && f (x/2) (k-1))
      (fun x k => (x == 0) && (k == 0))
    let pass : Nat → List (Nat × Nat) → Nat → Bool := fun x => List.foldr (fun z f n =>
      if x &&& z.1 == 0 then if z.2 ≥ n then true else f (n-z.2) else f n) (fun n => n == 0)

    tests.all (fun z => decode c z.1 6) = true →
    (enum b).all (fun p => decide (p.2 > 6) || pass p.1 tests L) = true →
    (tests.map Prod.snd).sum < 5*L →
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum b) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum c →
        ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum decode pass valid each gap R K mem size cap
  apply impossible_of_dual tests L ?_ ?_ gap R K mem size cap
  · exact fun z hz => decode_sound c z.1 6 (List.all_eq_true.mp valid z hz)
  · intro p hp hk
    apply pass_sound p.1 tests L
    have hh := List.all_eq_true.mp each p hp
    simpa only [show decide (p.2 > 6) = false by simpa using hk,Bool.false_or] using hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_8_root :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [737280,675840,295872,99024,43170,43154,16788,4297,4865,1600,24,48,85,21,4,1,0,0,1,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [1785856,937984,295872,99024,43170,43154,16788,4297,4865,1600,24,48,85,21,4,1,0,0,1,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(532629,1),(532757,6),(606469,2),(16953,5),(86057,1),(69833,2),(542993,1),(22817,5),(70849,7),(591041,2),(33078,5),(172054,1),(139462,2),(266346,1),(266794,6),(426506,2),(43538,5),(297506,1),(140482,7),(394434,2),(49212,4),(196812,2),(696340,4),(1114468,2),(1098020,2),(721092,3),(1769540,5),(1655044,1),(1744900,1),(2228888,2),(2146840,2),(348200,4),(458952,3),(2556040,5),(2523656,1),(2445320,1),(2148880,1),(2672656,4),(2793488,2),(1100064,1),(1361952,4),(1396768,2),(1381440,6),(2761856,6),(1584384,5),(1624320,4),(2366976,5),(2411008,4),(3605504,1),(3459072,1),(3721216,1)]
  apply screen [737280,675840,295872,99024,43170,43154,16788,4297,4865,1600,24,48,85,21,4,1,0,0,1,0,0,0] [1785856,937984,295872,99024,43170,43154,16788,4297,4865,1600,24,48,85,21,4,1,0,0,1,0,0,0] tests 31 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_10_root :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [1884160,888832,329504,82784,35114,34986,4388,1105,321,80,1033,264,24,3,0,0,2,2,1,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [1884160,888832,329504,82784,35114,34986,20772,5201,321,80,1097,280,24,3,16,4,2,2,1,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(63,11),(207,7),(663,66),(1671,43),(363,66),(2251,3),(2379,43),(6675,42),(5411,42),(9411,3),(10563,98),(9859,98),(14595,56),(13827,56),(131277,35),(278581,123),(393749,131),(263269,131),(409669,36),(16745,10),(18761,118),(282673,121),(268817,118),(141505,47),(272705,72),(403521,30),(275969,10),(65742,35),(33430,10),(34438,118),(557114,123),(526490,131),(590122,131),(622730,36),(561202,121),(529698,118),(74946,47),(534146,72),(599170,30),(538882,10),(49212,255),(196812,241),(164500,249),(1147940,132),(1163300,11),(1458244,114),(2246680,132),(2277400,11),(82280,249),(2719880,114),(2658832,165),(2381840,42),(1331488,165),(1610784,42),(1123648,250),(2239104,250),(2636032,276),(3428608,108),(3744000,14),(1324544,276),(3707392,108),(3547648,14),(3391488,208)]
  apply screen [1884160,888832,329504,82784,35114,34986,4388,1105,321,80,1033,264,24,3,0,0,2,2,1,0,0,0] [1884160,888832,329504,82784,35114,34986,20772,5201,321,80,1097,280,24,3,16,4,2,2,1,0,0,0] tests 1205 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_28_1 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [1933312,864256,148620,82484,34831,33352,16528,10280,330,147,1280,25,162,5,16,8,2,1,1,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [1933312,864256,148620,82484,34831,33352,16528,10792,330,147,1312,25,162,7,16,8,2,1,1,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(4127,3),(4631,3),(3115,2),(1251,3),(9027,1),(18461,2),(263045,4),(278917,1),(280837,1),(37913,3),(17577,2),(273425,4),(312337,2),(263393,2),(271457,1),(272673,4),(263105,1),(271169,2),(312449,1),(526366,6),(69774,2),(593934,2),(657450,3),(720938,2),(725002,1),(66018,2),(590178,2),(534818,1),(533314,4),(537154,4),(2115612,4),(114828,3),(2211852,2),(2134548,3),(2626068,4),(2392596,3),(2377748,3),(2408468,3),(2687748,3),(2377988,1),(168984,8),(2265112,2),(2277400,1),(150568,7),(2822152,3),(2634256,2),(2762768,3),(1114592,1),(1638752,2),(1188960,5),(1320032,1),(1769568,4),(1130912,8),(1329440,4),(1714208,1),(1115072,3),(1311680,1),(103104,7),(1147584,1),(1344192,2),(1319744,5),(1581888,1),(1361024,2),(3416832,1),(3736320,1),(3680512,4),(3426560,3),(3811328,1),(3391488,2)]
  apply screen [1933312,864256,148620,82484,34831,33352,16528,10280,330,147,1280,25,162,5,16,8,2,1,1,0,0,0] [1933312,864256,148620,82484,34831,33352,16528,10792,330,147,1312,25,162,7,16,8,2,1,1,0,0,0] tests 38 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_28_0 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [1933312,864256,148620,82468,34831,33352,16528,10280,330,147,1280,25,162,5,16,8,2,1,1,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [1933312,864256,148620,82468,34831,33352,16528,10792,330,147,1312,25,162,7,16,8,2,1,1,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(4127,21),(5147,4),(483,4),(1251,13),(18461,4),(280597,11),(263045,16),(280837,7),(273425,20),(312337,22),(263393,11),(270689,9),(272673,5),(37569,10),(295617,8),(38081,26),(528414,10),(69774,11),(526606,9),(528918,13),(136218,2),(526634,17),(657450,15),(725002,18),(144402,1),(590178,6),(534818,5),(537154,35),(594498,6),(725058,3),(2115612,24),(82316,20),(114828,10),(2691084,17),(2134548,8),(2392596,27),(2377748,24),(2408468,3),(103044,3),(2687748,13),(2377988,4),(2200068,2),(2691588,10),(150552,6),(168984,14),(181272,16),(82344,9),(150568,19),(2634256,47),(2762768,11),(2764816,9),(1114592,15),(1311200,5),(1581408,8),(1638752,6),(1188960,27),(1320032,20),(1769568,12),(1329440,50),(1199136,14),(1311680,5),(103104,20),(1344192,18),(1581888,23),(1361024,13),(3416832,10),(3678976,6),(3736320,5),(3811328,19),(3391488,30)]
  apply screen [1933312,864256,148620,82468,34831,33352,16528,10280,330,147,1280,25,162,5,16,8,2,1,1,0,0,0] [1933312,864256,148620,82468,34831,33352,16528,10792,330,147,1312,25,162,7,16,8,2,1,1,0,0,0] tests 189 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_63_1111 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,640,328,80,16,8,2,1,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,672,328,82,16,8,2,1,1,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(2127,1),(4623,4),(6159,3),(4743,1),(1803,2),(1331,5),(9267,2),(4771,4),(15363,2),(589901,5),(532677,5),(135813,2),(143493,2),(526089,9),(532689,1),(590161,2),(144417,4),(264522,1),(39946,8),(278706,1),(278738,6),(264530,2),(266914,7),(1116236,4),(1638476,3),(1184268,6),(1315340,5),(1327300,9),(92228,3),(1315460,2),(159876,12),(1200260,2),(1116488,4),(1313096,2),(1344264,3),(101640,8),(1149192,2),(1217032,2),(2121904,9),(2375856,5),(2131248,9),(2687312,9),(92240,11),(101648,2),(2196752,1),(2753184,3),(2252960,3),(2623264,8),(169504,7),(2754080,1),(3424448,3),(3735872,4),(3801728,5),(3441408,6),(2827264,1)]
  apply screen [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,640,328,80,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,672,328,82,16,8,2,1,1,0,0,0] tests 47 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_63_1110 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,640,320,80,16,8,2,1,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,672,320,82,16,8,2,1,1,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(2127,16),(4623,10),(4743,10),(1803,16),(1331,24),(9267,24),(1827,9),(532677,23),(656005,1),(526089,45),(525617,4),(532689,2),(76817,18),(656033,3),(209921,31),(278726,17),(39946,37),(278706,26),(278738,6),(264530,11),(266914,13),(315426,1),(317442,7),(1116236,16),(1638476,13),(1184268,17),(1315340,17),(1704460,11),(1327300,51),(92228,1),(1704580,10),(159876,47),(1116488,20),(1313096,22),(1344264,6),(101640,21),(1217032,10),(105480,2),(2121904,20),(2375856,34),(2131248,16),(2622768,24),(2121936,4),(92240,33),(2187344,15),(2196752,8),(2753184,4),(2252960,2),(2623264,24),(2392864,1),(169504,43),(3424448,13),(3735872,36),(3801728,21),(3441408,42),(2827264,14),(1366016,2)]
  apply screen [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,640,320,80,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,672,320,82,16,8,2,1,1,0,0,0] tests 195 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_63_11011 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,640,328,82,16,8,2,1,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,672,328,82,16,8,2,1,1,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(4623,8),(6159,2),(8391,6),(8371,6),(1331,1),(9267,5),(4771,2),(15363,1),(589901,2),(532677,10),(590153,9),(526089,2),(526113,4),(144417,12),(264270,1),(30726,5),(264522,2),(295690,1),(34098,1),(295218,7),(24786,3),(264530,6),(26706,2),(266914,12),(56322,2),(1116236,12),(1638476,5),(1184268,11),(1327300,3),(1132612,5),(1184388,1),(1315460,10),(159876,9),(1331332,2),(1344264,13),(101640,15),(169480,2),(1217032,2),(2121904,7),(2629808,7),(2131248,6),(2392368,4),(2629840,2),(2687312,13),(92240,17),(2187344,1),(101648,2),(2753184,3),(2252960,3),(2131744,6),(2623264,1),(169504,11),(2262560,2),(3424448,7),(3735872,5),(3801728,9),(3441408,6)]
  apply screen [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,640,328,82,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,672,328,82,16,8,2,1,1,0,0,0] tests 63 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_63_11010 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,640,320,82,16,8,2,1,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,672,320,82,16,8,2,1,1,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(2127,2),(4623,19),(8391,24),(2379,11),(8371,37),(9267,23),(2387,6),(655885,4),(532677,59),(590153,10),(526089,26),(532657,1),(590161,17),(76817,3),(526113,11),(209921,32),(30726,46),(295690,4),(295218,33),(264530,13),(28834,4),(295714,24),(56322,11),(1116236,18),(1312844,29),(1184268,16),(1704460,24),(1327300,21),(1132612,6),(1184388,12),(1315460,42),(159876,41),(1116488,8),(1344264,54),(101640,58),(169480,5),(2121904,20),(2629808,24),(2131248,24),(2392368,29),(2121936,3),(2629840,26),(2687312,2),(92240,48),(101648,5),(2196752,14),(2753184,26),(2252960,3),(2131744,5),(169504,45),(2262560,7),(3424448,39),(3735872,32),(3801728,8),(3441408,27),(2827264,12)]
  apply screen [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,640,320,82,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,672,320,82,16,8,2,1,1,0,0,0] tests 231 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_63_101 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [1728512,966656,266406,132619,37008,17441,1320,397,312,90,648,640,320,80,16,8,2,1,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [1728512,966656,266406,132619,37008,17441,1320,397,312,90,648,672,328,82,16,8,2,1,1,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(6159,50),(9267,67),(15363,16),(720909,23),(524997,52),(532677,22),(663685,10),(729093,4),(526089,75),(532689,5),(76817,56),(144417,10),(262854,16),(30726,28),(262986,48),(39946,57),(278706,10),(264530,36),(266914,36),(315426,26),(1116236,54),(1638476,2),(1184268,46),(1704460,10),(1573572,26),(1327300,78),(92228,46),(1315460,14),(159876,32),(1200260,36),(1311560,22),(1313096,14),(101640,56),(1149192,26),(169480,23),(1217032,1),(2121904,66),(2375856,27),(2131248,59),(2622768,15),(2392368,14),(2408496,15),(2629840,8),(2375888,21),(2687312,32),(92240,54),(101648,23),(2688272,5),(2696208,24),(2753184,22),(159904,37),(2623264,45),(2392864,20),(169504,76),(2761760,11),(3408704,16),(3670848,24),(3735872,17),(3801728,18),(3441408,15),(2827264,29),(1366016,39),(3391488,74)]
  apply screen [1728512,966656,266406,132619,37008,17441,1320,397,312,90,648,640,320,80,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1320,397,312,90,648,672,328,82,16,8,2,1,1,0,0,0] tests 388 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_63_100 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [1728512,966656,266406,132619,37008,17441,1320,397,312,90,640,640,320,80,16,8,2,1,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [1728512,966656,266406,132619,37008,17441,1320,397,312,90,640,672,328,82,16,8,2,1,1,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(6159,18),(711,2),(843,2),(9267,13),(655885,2),(524997,9),(532677,9),(598085,1),(729093,1),(525129,2),(526089,8),(591113,1),(656905,3),(721929,4),(525617,1),(533553,3),(76817,1),(526113,13),(144417,3),(268302,1),(262854,5),(30726,5),(262986,11),(301066,1),(295218,1),(264530,13),(266914,13),(295714,1),(56322,4),(317442,5),(1311308,3),(1116236,9),(1312844,1),(1638476,1),(1184268,8),(1315340,1),(1769484,9),(1573572,2),(1327300,7),(92228,13),(1132612,4),(1184388,1),(1315460,2),(159876,9),(1200260,5),(1573704,5),(1313096,1),(1344264,5),(101640,9),(1149192,6),(169480,10),(1217032,5),(2121904,13),(2629808,5),(2131248,10),(2392368,5),(2147376,5),(2121936,4),(2629840,1),(2375888,2),(2687312,10),(92240,10),(2187344,1),(2196752,4),(93200,4),(117776,11),(2753184,10),(2252960,2),(2623264,1),(2392864,4),(169504,5),(185376,20),(3408576,10),(3670720,5),(3424448,7),(3408704,1),(3670848,8),(3735872,4),(3801728,4),(3441408,2),(2827264,8),(1366016,5),(3391488,5)]
  apply screen [1728512,966656,266406,132619,37008,17441,1320,397,312,90,640,640,320,80,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1320,397,312,90,640,672,328,82,16,8,2,1,1,0,0,0] tests 92 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_63_011 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [1728512,966656,266406,132619,37008,17441,1324,396,312,90,648,640,320,80,16,8,2,1,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [1728512,966656,266406,132619,37008,17441,1324,396,312,90,648,672,328,82,16,8,2,1,1,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(6159,88),(9267,101),(15363,12),(532677,7),(729093,29),(526089,95),(721929,1),(533553,1),(524753,54),(76817,50),(525217,69),(144417,102),(30726,34),(264522,9),(39946,89),(278706,15),(311346,31),(262610,54),(264530,37),(280658,47),(263074,54),(266914,45),(1116236,130),(1638476,47),(1184268,126),(1315340,51),(1316876,1),(1769484,27),(1327300,74),(92228,28),(1704580,40),(159876,103),(1116488,18),(1313096,51),(1344264,32),(101640,55),(169480,28),(1349640,16),(2121904,89),(2375856,67),(2622768,85),(2392368,24),(2408496,4),(2359760,28),(2687312,24),(92240,74),(2187344,31),(101648,72),(2196752,23),(2360224,3),(2753184,24),(159904,55),(2623264,33),(169504,74),(2262560,31),(3408320,6),(3670464,16),(3424448,58),(3735872,25),(3408768,16),(3801728,32),(3441408,40),(2827264,96),(1366016,62),(3391488,96)]
  apply screen [1728512,966656,266406,132619,37008,17441,1324,396,312,90,648,640,320,80,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1324,396,312,90,648,672,328,82,16,8,2,1,1,0,0,0] tests 608 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_63_010 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [1728512,966656,266406,132619,37008,17441,1324,396,312,90,640,640,320,80,16,8,2,1,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [1728512,966656,266406,132619,37008,17441,1324,396,312,90,640,672,328,82,16,8,2,1,1,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(4623,1),(6159,38),(9267,14),(467,1),(931,11),(13347,6),(655885,2),(532677,20),(729093,6),(590153,10),(526089,24),(721929,10),(525617,8),(533553,5),(524753,13),(75857,4),(76817,8),(525217,12),(144417,5),(264270,8),(266886,13),(30726,16),(264522,4),(311346,3),(262610,8),(264530,21),(263074,23),(266914,4),(299554,5),(315426,11),(31746,6),(56322,8),(1116236,30),(1312844,5),(1638476,2),(1184268,28),(1704460,11),(1769484,15),(1327300,19),(92228,8),(1315460,19),(159876,34),(1333252,17),(1638728,3),(1344264,21),(101640,34),(1149192,4),(169480,21),(1217032,8),(2121904,9),(2629808,14),(2375856,13),(2131248,22),(2622768,4),(2392368,13),(2408496,2),(2359760,15),(2121936,2),(2629840,2),(2375888,3),(2687312,17),(92240,13),(2187344,9),(2695248,2),(101648,10),(117776,34),(2360224,1),(2753184,21),(159904,9),(2252960,8),(169504,6),(2262560,11),(160800,18),(3408320,5),(3670464,9),(3424448,8),(3735872,6),(3408768,20),(3670912,7),(3801728,3),(3441408,3),(2319360,15),(2827264,18),(1366016,6),(3391488,24)]
  apply screen [1728512,966656,266406,132619,37008,17441,1324,396,312,90,640,640,320,80,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1324,396,312,90,640,672,328,82,16,8,2,1,1,0,0,0] tests 198 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_138_root :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [2031616,145410,401921,24704,11376,34100,9041,3140,1601,2200,580,129,23,16,32,32,1,0,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [2031616,145410,401921,24704,11376,34100,9041,11332,3649,2200,580,129,23,16,32,32,5,0,0,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(4499,9),(67971,4),(8373,3),(16725,5),(33445,11),(17733,8),(36357,2),(52229,2),(59397,4),(8377,1),(8601,11),(24857,1),(70025,4),(71177,9),(99849,2),(131190,6),(262758,5),(393318,3),(133510,12),(265734,1),(2101586,10),(2228562,3),(1053346,13),(267842,11),(663604,8),(671828,5),(819748,12),(696356,2),(803908,12),(190468,12),(444420,1),(528504,13),(3674136,11),(2646040,6),(1613864,5),(529992,8),(1118856,9),(2168072,4),(2187528,6),(1188016,10),(2244944,1),(2253072,11),(2777104,1),(1839648,4),(1868320,5),(1998880,6),(792128,4),(2888768,4),(2901056,4),(3031104,4),(1157248,11),(1222784,2),(2182400,6),(2255104,4),(364032,14),(1411584,4),(379904,3),(2444288,10)]
  apply screen [2031616,145410,401921,24704,11376,34100,9041,3140,1601,2200,580,129,23,16,32,32,1,0,0,0,0,0] [2031616,145410,401921,24704,11376,34100,9041,11332,3649,2200,580,129,23,16,32,32,5,0,0,0,0,0] tests 73 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_146_root :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [1836036,459777,287744,27648,84016,21009,5284,5936,5476,1066,71,80,260,33,34,1,0,0,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [1836036,459777,287744,27648,92208,53777,5284,5936,5476,1066,71,80,260,33,34,1,0,0,0,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(467,1),(8531,6),(17059,5),(33987,2),(74051,2),(18051,2),(50307,1),(4405,2),(469,1),(49301,1),(1477,3),(329025,3),(336193,5),(329473,11),(414209,10),(471041,1),(2234,1),(938,9),(2099402,2),(74058,1),(2131138,10),(2115202,4),(2147458,2),(2271234,10),(1484,8),(1083476,4),(51348,12),(1312068,1),(1344580,6),(542340,9),(575620,1),(1868804,7),(70440,10),(78120,3),(594472,2),(1115464,2),(1122632,7),(2623112,3),(1126664,1),(2688520,4),(3736584,7),(145456,11),(153648,3),(1091664,12),(1194000,5),(676384,7),(725536,4),(3441728,2),(3474496,1),(2639488,1),(2950656,6),(2803712,10),(1519616,9),(2035712,1),(3579904,3),(3612672,1)]
  apply screen [1836036,459777,287744,27648,84016,21009,5284,5936,5476,1066,71,80,260,33,34,1,0,0,0,0,0,0] [1836036,459777,287744,27648,92208,53777,5284,5936,5476,1066,71,80,260,33,34,1,0,0,0,0,0,0] tests 52 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_161_root :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [1351680,368640,19526,6407,98376,12306,9364,4440,1571,2144,1108,200,337,84,0,0,1,0,4,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [1351681,368640,19526,6407,98376,12306,9364,4440,1571,2144,1108,200,337,84,1,0,1,0,4,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(263365,4),(267333,1),(1054981,1),(1315845,1),(139657,1),(139913,6),(1442313,2),(393873,1),(267793,4),(1055009,7),(1181985,2),(70726,6),(2687046,2),(72710,1),(525962,5),(2629770,1),(2107658,1),(532690,4),(590930,1),(2107682,7),(2165026,2),(787596,3),(3148044,1),(2130372,1),(819396,2),(2195780,1),(2719812,1),(3213572,3),(3244292,4),(1381380,4),(1413124,1),(2760840,4),(3279112,3),(1068552,1),(804360,2),(1198600,1),(1458696,1),(3295240,4),(2777096,1),(102512,4),(156208,4),(565456,1),(884816,4),(950416,3),(284176,1),(934416,4),(869392,3),(2269472,5),(3309856,1),(1136672,5),(3229728,1),(2793600,2),(1397760,2)]
  apply screen [1351680,368640,19526,6407,98376,12306,9364,4440,1571,2144,1108,200,337,84,0,0,1,0,4,1,0,0] [1351681,368640,19526,6407,98376,12306,9364,4440,1571,2144,1108,200,337,84,1,0,1,0,4,1,0,0] tests 28 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_175_root :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [1359873,364544,6195,20642,20642,8515,2322,4612,4225,673,168,772,388,63,0,0,0,0,4,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [1359873,364544,6195,20642,20642,8515,2322,12804,6273,673,168,804,396,63,0,0,0,0,4,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(1057829,1),(1180709,4),(1441829,5),(12869,6),(268805,3),(8601,2),(1057865,2),(1196105,4),(13577,5),(10545,2),(264497,1),(1057329,5),(1327633,2),(11553,3),(268673,1),(283265,2),(413953,2),(11302,6),(2105926,1),(2163270,4),(2687046,5),(531462,3),(8602,2),(12490,2),(528586,1),(2106442,5),(2655242,2),(2105906,2),(2195506,4),(10898,5),(12994,3),(530818,1),(624770,2),(560386,2),(330276,10),(3154980,1),(3154500,1),(660548,10),(49560,8),(3194904,7),(544968,11),(3155016,4),(2768968,1),(689416,10),(297264,11),(3154480,4),(1409072,1),(344720,10),(3310624,6),(3228224,6),(1032192,8)]
  apply screen [1359873,364544,6195,20642,20642,8515,2322,4612,4225,673,168,772,388,63,0,0,0,0,4,1,0,0] [1359873,364544,6195,20642,20642,8515,2322,12804,6273,673,168,804,396,63,0,0,0,0,4,1,0,0] tests 42 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_181_11 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [63,757760,274816,68352,81968,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [63,757760,274816,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(526209,37),(527745,3),(1575297,10),(1591425,39),(1134721,18),(534273,20),(1214721,8),(1706241,11),(1220865,30),(2631169,18),(2198529,48),(2143233,9),(2328577,1),(1355777,15),(2531329,5),(3022849,3),(3031041,45),(126,48),(1048982,30),(12838,26),(9030,1),(2394,9),(67738,2),(68746,30),(102450,59),(35154,6),(1083666,12),(1150994,16),(5794,29),(46114,15),(36162,7),(42306,16),(525196,7),(541324,43),(1069204,2),(1458196,30),(21156,6),(274980,34),(533316,22),(663876,3),(925764,13),(1712388,27),(1974276,12),(84120,12),(215064,2),(2098792,11),(657736,22),(2624584,46),(2312200,14),(166224,23),(1132688,5),(1263632,3),(1280016,15),(2400352,4),(2380320,3),(2143264,2),(2445344,44),(2531392,23)]
  apply screen [63,757760,274816,68352,81968,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] [63,757760,274816,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] tests 211 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_181_10 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [63,757760,270720,68352,81968,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [63,757760,270720,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(526209,70),(527745,22),(1575297,12),(1132673,19),(1591425,72),(1134721,47),(534273,15),(1706241,11),(1220865,27),(1712385,50),(2631169,53),(2380289,17),(2900481,13),(2198529,89),(2143233,28),(2312193,25),(2770945,3),(1280001,37),(1355777,11),(2531329,41),(1974273,19),(3022849,4),(3031041,60),(126,110),(190,4),(1048982,65),(12838,25),(9030,18),(1089798,52),(2394,15),(3402,11),(3466,21),(68746,32),(102450,91),(35154,24),(1051026,31),(1083666,16),(1148946,5),(1150994,5),(5794,72),(70818,18),(13858,4),(46114,30),(42306,42),(525196,14),(541324,75),(282676,1),(1212692,11),(1331220,16),(1458196,49),(274980,96),(533316,12),(172356,4),(663876,5),(434244,52),(1712388,42),(84120,59),(2098792,27),(657736,34),(2624584,111),(2312200,34),(166224,56),(1280016,3),(2111008,3),(2445344,108),(2531392,30)]
  apply screen [63,757760,270720,68352,81968,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] [63,757760,270720,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] tests 456 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_181_0111 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,757760,274816,68352,82224,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,757760,274816,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(3459,14),(1051011,6),(36099,1),(42243,19),(1093635,13),(1575297,27),(1591425,26),(534273,23),(1706241,25),(1220865,27),(2631169,16),(2198529,28),(2143233,5),(1722369,17),(1280001,16),(2328577,3),(1974273,21),(3022849,3),(3031041,28),(126,6),(910,10),(4278,1),(1048982,14),(12838,2),(2394,25),(2458,4),(3466,9),(102450,75),(1051026,2),(1083666,10),(5794,70),(46114,13),(42306,13),(16572,4),(131420,53),(655692,3),(525196,26),(541324,17),(20660,15),(282676,21),(1458196,24),(274980,81),(533316,12),(925764,17),(1712388,31),(1974276,2),(84120,31),(215064,25),(527688,18),(657736,17),(2624584,16),(2754632,48),(2770952,5),(86192,2),(364592,8),(166224,33),(1214736,20),(1263632,1),(1280016,5),(2139232,8),(2111008,5),(2143264,11),(2200608,1),(2445344,77),(534336,19),(2531392,10),(3022912,11)]
  apply screen [62,757760,274816,68352,82224,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] [62,757760,274816,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] tests 250 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_181_01101 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,757760,270720,68352,82224,26660,8353,9888,4776,226,712,67,80,5,1,8,4,0,0,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,757760,270720,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(3459,6),(68739,15),(36099,14),(46083,5),(1093635,7),(526209,19),(527745,1),(1575297,16),(1591425,36),(534273,5),(1214721,10),(1706241,26),(1220865,31),(1712385,23),(2631169,30),(2900481,3),(2198529,5),(2770945,10),(2328577,16),(2531329,3),(3022849,4),(1982465,19),(3031041,21),(414,7),(1048982,25),(2458,7),(1706,1),(3402,16),(3466,1),(68746,5),(102450,57),(1051026,15),(5794,74),(46114,7),(36162,9),(42306,15),(16572,7),(131420,45),(655692,1),(525196,15),(541324,13),(20660,11),(282676,18),(1458196,28),(274980,67),(533316,23),(1712388,1),(1982468,8),(133464,29),(84120,14),(215064,10),(2098792,5),(657736,17),(2624584,31),(2754632,15),(526216,5),(527752,20),(2312200,23),(2770952,16),(86192,19),(166224,10),(1280016,18),(2139232,11),(2111008,6),(2380320,3),(2143264,14),(2200608,6),(2445344,68),(2531392,24),(3022912,22)]
  apply screen [62,757760,270720,68352,82224,26660,8353,9888,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] [62,757760,270720,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] tests 238 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_181_01100 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,757760,270720,68352,82224,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,757760,270720,84736,82224,26660,8865,1696,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(3459,33),(1051011,23),(36099,43),(42243,5),(1093635,24),(526209,26),(527745,7),(1575297,29),(2638465,33),(2165889,21),(2624641,1),(1591425,54),(534273,34),(1214721,20),(1706241,99),(1220865,48),(1712385,36),(2631169,57),(2198529,63),(2143233,22),(1722369,10),(2770945,35),(2328577,29),(2531329,44),(1974273,16),(1982465,26),(3031041,61),(414,43),(1048982,66),(1081622,4),(1089798,49),(2394,27),(2458,9),(3402,17),(3466,15),(102450,158),(35154,24),(1051026,30),(5794,176),(46114,25),(42306,62),(131420,76),(525132,37),(655692,28),(525196,39),(541324,75),(20660,28),(282676,29),(426068,111),(1069204,27),(1212692,15),(1458196,75),(21156,25),(274980,171),(307236,18),(533316,23),(925764,20),(1712388,41),(1982468,8),(133464,36),(84120,33),(215064,51),(2163880,13),(527688,33),(657736,75),(2624584,54),(2754632,34),(527752,11),(2638472,62),(2165896,71),(2181256,18),(2312200,15),(2770952,16),(86192,24),(364592,15),(166224,29),(1214736,28),(1263632,26),(1280016,31),(2139232,48),(2102944,1),(2118304,5),(2167968,15),(2183328,3),(2143264,36),(2200608,2),(2445344,175),(534336,26),(2531392,22),(3022912,60)]
  apply screen [62,757760,270720,68352,82224,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] [62,757760,270720,84736,82224,26660,8865,1696,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] tests 704 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_181_0101 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,757760,274816,68352,82224,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,757760,274816,84736,82224,26660,8865,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(3459,17),(1051011,11),(36099,15),(42243,16),(1093635,13),(1575297,55),(1591425,46),(534273,45),(1706241,36),(1220865,76),(2631169,31),(2198529,34),(1722369,22),(1280001,10),(2328577,30),(1355777,6),(1974273,32),(3022849,2),(3031041,30),(126,25),(4278,9),(1048982,19),(12838,27),(9030,7),(2394,31),(3466,15),(102450,111),(35154,24),(1051026,18),(1083666,20),(5794,96),(46114,19),(36162,8),(16572,11),(131420,78),(525132,2),(655692,6),(525196,40),(541324,42),(20660,8),(282676,28),(1069204,10),(1458196,35),(270948,6),(274980,136),(533316,15),(925764,19),(1712388,52),(1974276,12),(82104,2),(84120,64),(215064,33),(527688,21),(657736,27),(2624584,37),(2754632,75),(527752,3),(2770952,16),(364592,6),(166224,58),(1214736,16),(1280016,23),(1540112,13),(2139232,23),(87200,21),(2111008,5),(2119200,5),(2372128,1),(2143264,29),(2445344,128),(534336,33),(2531392,27),(3022912,17)]
  apply screen [62,757760,274816,68352,82224,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] [62,757760,274816,84736,82224,26660,8865,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] tests 428 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_181_01001 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,757760,270720,68352,82224,26660,8865,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,757760,270720,84736,82224,26660,8865,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(3459,4),(68739,6),(70787,1),(1093635,3),(527745,3),(85121,2),(1134721,14),(1706241,14),(1220865,7),(2631169,9),(2639361,1),(2182145,2),(2640897,2),(2198529,9),(2143233,3),(1280001,4),(2328577,3),(2572289,2),(3031041,9),(126,2),(32886,3),(1048982,10),(1081622,3),(41286,11),(2394,2),(3402,6),(102450,12),(35154,2),(1051026,1),(5794,16),(46114,1),(103458,1),(36162,3),(42306,9),(16572,6),(131420,9),(541324,12),(20660,4),(426068,13),(1069204,1),(1458196,9),(1474580,1),(270948,3),(274980,13),(533316,10),(663876,1),(925764,2),(1482756,1),(1982468,6),(82104,2),(133464,7),(84120,8),(215064,1),(2098792,3),(2180136,3),(657736,5),(2624584,4),(2754632,6),(527752,1),(542344,6),(543880,2),(2639368,5),(2182152,4),(2312200,6),(86192,1),(166224,4),(1132688,2),(1263632,1),(1280016,5),(1523728,2),(1540112,1),(2139232,6),(2200608,4),(2445344,15),(2461728,2),(534336,2),(2631232,1),(2531392,8),(3022912,6)]
  apply screen [62,757760,270720,68352,82224,26660,8865,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] [62,757760,270720,84736,82224,26660,8865,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] tests 79 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_181_01000 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,757760,270720,68352,82224,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,757760,270720,84736,82224,26660,8353,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(3459,9),(1051011,9),(36099,28),(42243,19),(1093635,14),(526209,25),(527745,2),(1575297,31),(542337,4),(85121,15),(1591425,61),(534273,20),(1214721,12),(1706241,37),(1220865,39),(1712385,40),(2631169,38),(2182145,55),(2640897,5),(2198529,19),(2143233,7),(1280001,18),(1355777,10),(2531329,19),(1974273,7),(1982465,19),(3031041,33),(414,15),(1048982,16),(12838,2),(45094,6),(1089798,39),(2394,15),(2458,21),(3402,20),(3466,8),(102450,106),(35154,31),(1051026,19),(5794,112),(46114,4),(42306,40),(16572,23),(131420,61),(525132,13),(525196,16),(541324,53),(282676,11),(426068,44),(1069204,30),(1458196,55),(1474580,2),(21156,5),(274980,136),(533316,47),(434244,14),(925764,3),(1712388,16),(1482756,22),(1974276,9),(133464,8),(198744,15),(84120,44),(215064,14),(2163816,21),(657736,64),(2624584,30),(2295880,9),(2754632,16),(526216,2),(527752,14),(542344,8),(2639368,24),(2312200,4),(2770952,45),(86192,5),(364592,4),(231504,15),(1214736,12),(1263632,14),(1280016,26),(2139232,24),(87200,17),(2111008,7),(2143264,8),(2445344,112),(534336,16),(2631232,4),(2198592,17),(2328640,11),(2531392,16),(3022912,24)]
  apply screen [62,757760,270720,68352,82224,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] [62,757760,270720,84736,82224,26660,8353,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] tests 452 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_181_0011 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,757760,270720,84736,81968,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,757760,274816,84736,81968,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(526209,5),(1591425,41),(1134721,15),(534273,7),(1706241,13),(1712385,3),(2631169,24),(2900481,17),(2198529,32),(2328577,4),(1355777,40),(2531329,9),(1974273,5),(3022849,4),(1982465,4),(3031041,12),(126,6),(1048982,17),(1052822,5),(1057046,20),(2458,7),(3402,3),(3466,19),(68746,15),(41074,5),(102450,38),(5794,42),(70818,1),(46114,6),(36162,1),(42306,32),(16572,17),(131420,30),(655692,1),(525196,11),(541324,25),(270452,8),(282676,13),(401492,2),(1069204,2),(1458196,32),(274980,34),(283172,9),(533316,2),(925764,23),(1712388,10),(1974276,2),(1982468,3),(82104,4),(133464,3),(84120,25),(215064,19),(2098792,20),(657736,8),(2624584,34),(2754632,9),(526216,20),(527752,6),(2312200,18),(2770952,16),(166224,11),(172368,12),(434256,9),(1214736,16),(1280016,2),(2111008,5),(2143264,10),(2200608,4),(2445344,41),(2531392,24),(3022912,1)]
  apply screen [62,757760,270720,84736,81968,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] [62,757760,274816,84736,81968,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] tests 199 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_181_0010 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,757760,270720,68352,81968,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,757760,274816,68352,81968,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(1051011,78),(5763,14),(68739,31),(36099,30),(42243,45),(1083651,14),(1093635,66),(526209,20),(527745,45),(1591425,87),(534273,37),(1214721,16),(1706241,7),(1220865,80),(2631169,74),(2900481,66),(2198529,70),(2143233,4),(2312193,51),(2770945,49),(2328577,25),(1355777,64),(2531329,46),(1974273,3),(3022849,22),(1982465,75),(3031041,16),(126,64),(414,46),(1048982,45),(1057046,37),(2394,3),(2458,22),(3402,75),(3466,16),(68746,66),(102450,161),(1083666,1),(5794,170),(46114,20),(42306,76),(262268,66),(16572,4),(131420,80),(409628,45),(655692,16),(917580,14),(525196,25),(541324,70),(933900,30),(20660,14),(282676,20),(1069204,6),(1188116,15),(1458196,76),(21156,4),(274980,161),(533316,24),(663876,40),(925764,1),(1712388,56),(84120,74),(215064,37),(2441256,14),(657736,7),(2624584,87),(3014728,78),(526216,51),(527752,49),(2900488,31),(2312200,20),(2770952,45),(166224,56),(172368,15),(434256,37),(1214736,40),(1280016,24),(2139232,6),(2143264,14),(2200608,4),(2445344,170),(2531392,45)]
  apply screen [62,757760,270720,68352,81968,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] [62,757760,274816,68352,81968,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] tests 722 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_181_0001 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,757760,270720,68352,81968,26660,8865,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,757760,274816,84736,81968,26660,8865,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(3459,7),(1051011,2),(1089795,3),(1093635,2),(526209,1),(527745,2),(85121,4),(1134721,12),(1706241,12),(1220865,4),(2110977,1),(2631169,9),(2639361,7),(2182145,3),(2198529,4),(2143233,2),(1263617,4),(1280001,4),(2328577,3),(3031041,6),(126,3),(8310,3),(8534,2),(1048982,9),(1057046,1),(2394,1),(2458,4),(3402,3),(3466,1),(102450,10),(35154,1),(41298,8),(5794,13),(70818,4),(46114,1),(36162,2),(42306,12),(16572,9),(131420,9),(525132,1),(655692,1),(541324,7),(282676,3),(401492,2),(1450004,5),(1458196,2),(274980,13),(533316,10),(795204,1),(1982468,6),(133464,3),(84120,6),(215064,1),(2098792,5),(83112,3),(2180136,8),(657736,7),(2624584,3),(2754632,7),(543880,5),(2182152,2),(2312200,9),(348208,2),(364592,1),(166224,4),(172368,3),(434256,7),(1132688,5),(1134736,3),(1280016,2),(1482768,3),(1523728,3),(1540112,2),(2139232,3),(2200608,3),(2445344,13),(2461728,3),(534336,5),(2631232,3),(2531392,4),(3022912,6)]
  apply screen [62,757760,270720,68352,81968,26660,8865,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] [62,757760,274816,84736,81968,26660,8865,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] tests 75 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_181_0000 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,757760,270720,68352,81968,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,757760,274816,84736,81968,26660,8353,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(3459,34),(1051011,35),(36099,22),(42243,54),(1093635,37),(526209,67),(1575297,28),(542337,10),(1591425,143),(534273,8),(1214721,18),(1706241,118),(1220865,85),(1712385,53),(2631169,83),(2639361,27),(2892289,24),(2182145,34),(2198529,51),(2143233,24),(1263617,4),(1280001,39),(2531329,8),(3022849,15),(1982465,30),(3031041,77),(414,1),(8534,34),(1048982,78),(1057046,47),(2394,25),(2458,42),(3402,27),(3466,38),(45106,4),(102450,201),(41298,45),(1051026,1),(1116306,2),(1083666,25),(5794,224),(46114,21),(42306,60),(16572,37),(131420,125),(525132,32),(525196,31),(541324,77),(20660,5),(282676,53),(401492,31),(1069204,29),(1188116,6),(1450004,22),(1458196,105),(21156,6),(274980,232),(533316,91),(925764,28),(1712388,31),(1982468,33),(198744,36),(84120,98),(2163816,48),(527688,36),(657736,132),(2624584,65),(2754632,50),(85128,37),(2639368,76),(2182152,20),(2312200,43),(2770952,54),(86192,5),(166224,13),(172368,1),(231504,26),(1132688,18),(1263632,4),(1280016,76),(1482768,52),(2139232,18),(87200,29),(2380320,11),(2143264,54),(2200608,3),(2445344,212),(534336,16),(2631232,13),(2198592,30),(2328640,25),(2531392,83),(3022912,13)]
  apply screen [62,757760,270720,68352,81968,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] [62,757760,274816,84736,81968,26660,8353,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] tests 875 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_182_11 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [63,983552,155712,17984,54784,36932,1633,4167,1172,808,1106,45,192,192,64,1,2,1,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [63,983552,417856,50752,54784,37444,1633,4167,1172,808,1106,45,192,192,66,1,2,1,0,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(307329,2),(209025,13),(696449,4),(1066753,4),(152321,7),(2233089,5),(1328385,7),(2396417,3),(1229057,3),(1117697,12),(2298369,3),(1838081,5),(812033,3),(3934209,7),(192513,1),(323585,1),(1753089,3),(126,8),(350,2),(12438,12),(25638,3),(4890,3),(197162,4),(135946,3),(67122,4),(1874,7),(77970,6),(18018,3),(204962,1),(18242,7),(152322,1),(184578,8),(263508,7),(265300,7),(272532,8),(274580,1),(279876,1),(311620,1),(827524,14),(2099800,6),(2164888,1),(2102040,8),(1245736,5),(3146568,2),(3148360,4),(2265224,10),(3277576,3),(3696,3),(1052256,2),(1576032,6),(1590368,5),(600224,12),(1066816,2),(1328448,1),(1360192,2),(3440960,7)]
  apply screen [63,983552,155712,17984,54784,36932,1633,4167,1172,808,1106,45,192,192,64,1,2,1,0,0,0,0] [63,983552,417856,50752,54784,37444,1633,4167,1172,808,1106,45,192,192,66,1,2,1,0,0,0,0] tests 55 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_182_10 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [63,983552,155712,17984,54784,36932,1633,4167,1172,808,1104,45,192,192,64,1,2,1,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [63,983552,417856,50752,54784,37444,1633,4167,1172,808,1104,45,192,192,66,1,2,1,0,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(796801,11),(209025,73),(2396289,1),(696449,7),(2785409,9),(22273,9),(1066753,27),(2233089,6),(1196801,10),(3277569,19),(283905,11),(1328385,41),(1229057,1),(1360129,2),(3440897,21),(1117697,41),(3213825,6),(3342849,6),(1838081,38),(291841,16),(3934209,5),(1753089,33),(126,7),(350,45),(12438,87),(17734,7),(858,3),(197162,31),(135946,22),(168202,1),(67122,17),(1874,15),(5906,32),(18018,21),(18242,31),(176258,2),(22274,11),(152322,7),(184578,31),(2172,20),(263508,23),(265300,8),(272532,30),(267540,6),(279876,3),(311620,19),(827524,77),(2098008,8),(2099800,26),(2164888,8),(2102040,39),(1051240,32),(1116712,2),(1245736,17),(3146568,4),(3178824,34),(3148360,19),(2265224,19),(3277576,17),(3309832,30),(3213832,8),(3342856,13),(1066592,6),(1590368,36),(600224,97),(729248,9),(1066816,1),(1328448,3),(3440960,6),(1838144,12),(3934272,39)]
  apply screen [63,983552,155712,17984,54784,36932,1633,4167,1172,808,1104,45,192,192,64,1,2,1,0,0,0,0] [63,983552,417856,50752,54784,37444,1633,4167,1172,808,1104,45,192,192,66,1,2,1,0,0,0,0] tests 287 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_182_01 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [55,983552,155712,17984,54784,36932,1633,4167,1172,808,1106,45,192,192,64,1,2,1,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [55,983552,417856,50752,54784,37444,1633,4167,1172,808,1106,45,192,192,66,1,2,1,0,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(2361489,4),(274577,2),(2363665,22),(69137,7),(273425,5),(209025,26),(152321,10),(2233089,3),(1196801,6),(1328385,15),(184577,4),(1229057,2),(1117697,17),(1838081,4),(812033,5),(3934209,19),(192513,2),(323585,6),(712705,2),(1753089,9),(126,5),(33102,21),(12438,21),(25638,14),(197162,20),(135946,9),(67122,11),(1874,14),(77970,1),(18018,8),(204962,4),(18242,4),(209026,8),(152322,10),(184578,12),(192514,8),(2172,2),(263508,9),(265300,25),(272532,7),(534692,3),(279876,4),(311620,6),(827524,32),(2099800,16),(2164888,5),(2102040,9),(1051240,12),(3146568,12),(2265224,34),(2233096,2),(3277576,1),(3342856,6),(1576032,17),(1590368,12),(600224,30),(1117728,6),(1066816,11),(1328448,1),(1360192,3),(3440960,5),(1884224,13)]
  apply screen [55,983552,155712,17984,54784,36932,1633,4167,1172,808,1106,45,192,192,64,1,2,1,0,0,0,0] [55,983552,417856,50752,54784,37444,1633,4167,1172,808,1106,45,192,192,66,1,2,1,0,0,0,0] tests 125 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_182_001 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [55,983552,155712,17984,54784,37444,1633,4167,1172,808,1104,45,192,192,64,1,2,1,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [55,983552,417856,50752,54784,37444,1633,4167,1172,808,1104,45,192,192,66,1,2,1,0,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(307329,41),(209025,204),(827521,35),(1066753,94),(1196801,77),(1328385,31),(2396417,72),(1229057,6),(3440897,48),(3213825,34),(3342849,23),(1838081,39),(291841,103),(3934209,54),(1753089,27),(3866625,11),(33102,136),(12438,229),(49478,67),(634,1),(858,1),(196778,23),(197162,87),(168202,78),(67122,23),(1874,27),(5906,70),(18018,72),(204962,100),(18242,77),(176258,21),(22274,57),(184578,71),(2172,70),(2236,1),(263508,74),(265300,36),(272532,17),(274580,29),(534692,77),(827524,227),(2680,14),(2098008,58),(2099800,37),(2102040,110),(1051240,104),(1245736,107),(3146568,38),(3178824,85),(3148360,105),(2265224,96),(3309832,168),(3213832,2),(69168,102),(1066592,48),(1576032,66),(1590368,93),(600224,260),(729248,31),(1117728,36),(1066816,4),(1328448,84),(1360192,56),(1838144,27),(3934272,77),(1884224,63),(3964992,38)]
  apply screen [55,983552,155712,17984,54784,37444,1633,4167,1172,808,1104,45,192,192,64,1,2,1,0,0,0,0] [55,983552,417856,50752,54784,37444,1633,4167,1172,808,1104,45,192,192,66,1,2,1,0,0,0,0] tests 896 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_182_000 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [55,983552,155712,17984,54784,36932,1633,4167,1172,808,1104,45,192,192,64,1,2,1,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [55,983552,417856,50752,54784,36932,1633,4167,1172,808,1104,45,192,192,66,1,2,1,0,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(272529,39),(2361489,15),(5905,45),(2102033,10),(267537,3),(2363665,65),(69137,119),(2165265,44),(273425,33),(796801,39),(176257,26),(307329,9),(209025,228),(696449,5),(729217,1),(2785409,9),(22273,15),(2233089,12),(1196801,74),(3277569,18),(1328385,124),(315649,43),(2396417,105),(1360129,11),(1117697,62),(3342849,49),(291841,44),(3934209,75),(1753089,5),(1884161,5),(3833857,68),(3964929,22),(350,56),(33102,109),(12438,240),(49254,32),(858,9),(4890,23),(164010,79),(197162,114),(135946,65),(168202,3),(67122,82),(1874,20),(5906,23),(71186,5),(18018,70),(172194,27),(204962,52),(188450,63),(18242,66),(176258,14),(22274,36),(184578,96),(2172,174),(263508,48),(265300,105),(272532,47),(311620,99),(827524,237),(68152,3),(2098008,24),(2099800,70),(2102040,78),(1051240,64),(1116712,1),(1245736,38),(3146568,131),(3178824,36),(3148360,46),(3277576,44),(3309832,130),(3213832,21),(3342856,21),(3696,3),(69168,11),(1066592,44),(1576032,64),(1590368,47),(1622112,42),(600224,277),(696480,31),(1117728,25),(1753120,111),(1066816,129),(1328448,25),(1360192,3),(1838144,50),(3934272,24),(3964992,68)]
  apply screen [55,983552,155712,17984,54784,36932,1633,4167,1172,808,1104,45,192,192,64,1,2,1,0,0,0,0] [55,983552,417856,50752,54784,36932,1633,4167,1172,808,1104,45,192,192,66,1,2,1,0,0,0,0] tests 1016 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_183_11 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [63,829440,361504,42016,100928,12368,10785,8268,2380,291,548,130,257,1,9,1,5,1,0,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [63,829440,361504,173088,100928,12880,10785,8780,2380,295,548,130,257,1,9,1,5,1,0,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(1380481,17),(2639105,10),(2884865,7),(2892033,14),(302081,2),(2395137,3),(676865,9),(1218561,3),(3229697,12),(3475457,8),(3317761,15),(126,5),(67630,8),(3150,3),(694,1),(16998,1),(82470,1),(84006,4),(19526,7),(23558,5),(263450,11),(328074,4),(333834,2),(525202,9),(786834,4),(790674,4),(787730,5),(791570,11),(82722,5),(541506,3),(542018,8),(1116204,10),(35916,8),(148068,14),(1132580,3),(166980,3),(1218564,14),(8568,5),(299160,1),(303256,11),(9072,1),(533328,2),(664144,6),(689232,7),(696400,1),(533392,4),(795024,1),(2106208,3),(2114400,1),(74656,1),(1122976,17),(3229728,2),(2639168,1),(2264128,1)]
  apply screen [63,829440,361504,42016,100928,12368,10785,8268,2380,291,548,130,257,1,9,1,5,1,0,1,0,0] [63,829440,361504,173088,100928,12880,10785,8780,2380,295,548,130,257,1,9,1,5,1,0,1,0,0] tests 64 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_183_10 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [63,829440,361504,42016,100928,12368,10785,8268,2376,291,548,130,257,1,9,1,5,1,0,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [63,829440,361504,173088,100928,12880,10785,8780,2376,295,548,130,257,1,9,1,5,1,0,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(1122945,139),(1347713,99),(1380481,325),(2362625,21),(2639105,105),(2892033,222),(2395137,99),(676865,233),(3229697,344),(3475457,74),(3317761,285),(126,133),(1118,163),(67630,24),(69774,49),(694,141),(16998,32),(82470,56),(19526,105),(23558,180),(263450,125),(328074,30),(265482,90),(329994,31),(525650,36),(525202,134),(790674,88),(787730,141),(791570,148),(84258,14),(541506,91),(542018,94),(1116204,270),(35916,23),(164948,101),(168980,164),(148068,176),(1196580,40),(1218564,125),(8568,117),(270744,60),(303256,184),(1349640,14),(533328,51),(664144,207),(689232,6),(696400,150),(795024,41),(827536,53),(2106208,34),(1122976,309),(2630464,22),(2116928,155),(2264128,16),(2769984,73)]
  apply screen [63,829440,361504,42016,100928,12368,10785,8268,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] [63,829440,361504,173088,100928,12880,10785,8780,2376,295,548,130,257,1,9,1,5,1,0,1,0,0] tests 1249 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_183_01 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,829440,361504,42016,100928,12368,10785,8268,2380,291,548,130,257,1,9,1,5,1,0,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,829440,361504,173088,100928,12880,10785,8780,2380,295,548,130,257,1,9,1,5,1,0,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(328067,3),(790659,5),(82691,10),(541955,19),(787715,25),(791555,29),(533377,10),(1122945,5),(1380481,70),(2639105,6),(2892033,75),(302081,3),(2395137,1),(676865,26),(1218561,5),(1349633,3),(3229697,60),(3475457,7),(2793473,18),(3317761,12),(3448833,13),(3481601,3),(67630,37),(69774,5),(694,7),(16998,9),(82470,36),(19526,11),(23558,60),(263450,38),(65962,4),(525650,6),(525202,18),(790674,14),(787730,20),(17250,1),(82722,7),(541506,13),(542018,24),(1116204,62),(35916,67),(131700,19),(164948,19),(148068,17),(149604,12),(1114788,14),(1132580,11),(150596,17),(166980,6),(1218564,75),(8568,57),(303256,70),(302088,5),(139888,2),(533328,16),(664144,17),(689232,12),(696400,16),(533392,45),(693264,6),(824336,10),(2106208,19),(2246752,4),(1122976,57),(3229728,28),(2639168,39),(2264128,18),(2793536,34)]
  apply screen [62,829440,361504,42016,100928,12368,10785,8268,2380,291,548,130,257,1,9,1,5,1,0,1,0,0] [62,829440,361504,173088,100928,12880,10785,8780,2380,295,548,130,257,1,9,1,5,1,0,1,0,0] tests 299 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_183_001 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,829440,361504,42016,100928,12368,10785,8268,2376,295,548,130,257,1,9,1,5,1,0,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,829440,361504,173088,100928,12880,10785,8780,2376,295,548,130,257,1,9,1,5,1,0,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(82691,11),(787715,12),(545795,18),(791555,4),(1122945,7),(823425,4),(1347713,6),(1380481,54),(2362625,1),(2892033,18),(3219969,5),(3228161,6),(676865,19),(693249,2),(824321,8),(2917377,2),(3229697,46),(3317761,13),(2924545,12),(126,10),(1118,5),(5150,1),(630,11),(694,9),(82470,6),(19526,3),(23558,21),(378,10),(1370,23),(263450,5),(329994,16),(525138,7),(525202,5),(790674,21),(787730,20),(791570,6),(82722,1),(84258,1),(541506,19),(19778,5),(542018,13),(33884,13),(37020,2),(1116204,54),(1118348,6),(131700,31),(168980,42),(148068,5),(1114788,9),(1131044,3),(1196580,13),(150596,11),(154628,11),(1218564,19),(270744,8),(303256,14),(300056,4),(302088,25),(1349640,1),(1382408,6),(139888,6),(533328,3),(664144,22),(696400,28),(533392,20),(795024,4),(823440,3),(827536,14),(693264,7),(2106208,27),(1122976,53),(3220000,1),(2116928,23),(2769472,8),(2264128,15),(2769984,9),(2786368,2),(2793536,16)]
  apply screen [62,829440,361504,42016,100928,12368,10785,8268,2376,295,548,130,257,1,9,1,5,1,0,1,0,0] [62,829440,361504,173088,100928,12880,10785,8780,2376,295,548,130,257,1,9,1,5,1,0,1,0,0] tests 201 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_183_0001 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,829440,361504,42016,100928,12368,10785,8780,2376,291,548,130,257,1,9,1,5,1,0,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,829440,361504,173088,100928,12880,10785,8780,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(82691,2),(791555,6),(1380481,44),(827521,3),(1384577,15),(2892033,23),(676353,16),(2761217,5),(2769409,2),(676865,12),(2769921,5),(2917377,1),(3229697,38),(3317761,11),(2924545,13),(3448833,1),(3481601,1),(126,2),(190,4),(1118,4),(7182,2),(630,5),(4758,20),(82470,1),(86534,1),(23558,35),(328074,34),(525650,20),(525202,8),(786834,2),(790674,9),(791570,6),(541506,20),(542018,8),(33884,11),(1116204,41),(35916,18),(1085580,10),(131700,11),(164948,21),(168980,16),(148068,23),(1114788,10),(1131044,5),(1196580,2),(150596,3),(1118852,5),(1200644,3),(154628,2),(1218564,7),(8568,19),(303256,26),(336264,8),(1349640,6),(664144,19),(696400,20),(533392,6),(795024,15),(823440,1),(827536,5),(693264,1),(824336,12),(2115936,11),(2237024,22),(1122976,30),(2639168,13),(2247744,20),(2264128,23),(2793536,9)]
  apply screen [62,829440,361504,42016,100928,12368,10785,8780,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] [62,829440,361504,173088,100928,12880,10785,8780,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] tests 167 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_183_0000 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,829440,361504,42016,100928,12368,10785,8268,2376,291,548,130,257,1,9,1,5,1,0,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,829440,361504,173088,100928,12880,10785,8268,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(82691,27),(541955,9),(545283,7),(545795,8),(791555,34),(664193,27),(1380481,105),(1220737,5),(2362625,11),(2639105,20),(2892033,64),(2769409,24),(676865,33),(824321,14),(2917377,10),(3229697,97),(2924545,4),(3448833,40),(126,40),(5150,13),(630,1),(4758,35),(16998,8),(86534,10),(23558,44),(263450,39),(67882,6),(3402,6),(265482,22),(329994,55),(525650,47),(525202,56),(786834,23),(787730,14),(791570,7),(82722,8),(541506,25),(19778,21),(542018,20),(33884,27),(1114284,9),(1116204,111),(35916,21),(131700,29),(164948,59),(135828,18),(168084,9),(168980,26),(148068,36),(149604,6),(1114788,21),(1131044,1),(150596,11),(166980,25),(1216644,56),(154628,18),(1136644,7),(1218564,33),(8568,66),(270744,23),(303256,41),(300056,14),(336264,19),(1384584,3),(302088,20),(1349640,10),(533328,17),(664144,2),(696400,32),(533392,17),(795024,8),(664208,18),(696464,48),(824336,19),(2106208,17),(2115936,39),(2237024,21),(2246752,4),(1122976,95),(2116928,25),(2639168,8),(2769472,7),(2247744,14),(2264128,51),(2769984,14),(2793536,55)]
  apply screen [62,829440,361504,42016,100928,12368,10785,8268,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] [62,829440,361504,173088,100928,12880,10785,8268,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] tests 454 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_184_11 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [63,796736,83200,209920,90640,21072,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [63,796736,345344,209920,90640,21072,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(2630401,3),(3186945,14),(3219713,3),(3473665,2),(2117121,2),(2377217,11),(2393601,7),(2140673,3),(2632193,1),(2900481,7),(154625,4),(1348609,14),(3294209,5),(677889,8),(2762753,3),(3358721,9),(126,1),(190,1),(1118,10),(263694,13),(16998,9),(280070,4),(283654,3),(348166,4),(7194,5),(526890,7),(790666,18),(200850,4),(138258,9),(149602,5),(543266,7),(737314,4),(154626,5),(872450,7),(380,9),(295692,2),(300044,1),(65972,1),(1082452,5),(1376644,8),(1332228,5),(1396740,7),(8568,4),(41368,16),(39960,8),(533288,7),(141424,14),(1249424,14),(2106208,14),(598432,17)]
  apply screen [63,796736,83200,209920,90640,21072,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] [63,796736,345344,209920,90640,21072,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] tests 69 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_184_10 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [63,796736,83200,209920,90640,16976,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [63,796736,345344,209920,90640,16976,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(1089921,12),(598401,15),(2630401,20),(3186945,195),(3219713,6),(2117121,46),(2377217,64),(2900481,63),(154625,45),(1201153,41),(1348609,105),(3294209,16),(677889,41),(1265665,5),(3358721,98),(126,34),(1118,37),(4254,10),(5150,5),(263694,64),(267278,35),(69782,15),(344102,73),(17990,35),(280070,23),(283654,26),(348166,51),(7194,27),(526890,40),(786986,41),(3658,16),(790666,93),(196786,44),(134226,106),(200850,55),(138258,68),(543266,1),(803362,14),(673826,66),(737314,28),(20034,30),(677890,56),(262956,23),(295692,20),(300044,7),(1082452,22),(1086484,39),(1332228,39),(1396740,41),(8568,60),(41368,152),(39960,113),(533288,4),(787240,32),(41800,12),(36424,1),(43592,27),(141424,3),(1089872,38),(1249424,40),(2106208,131),(598432,159),(2247744,21)]
  apply screen [63,796736,83200,209920,90640,16976,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] [63,796736,345344,209920,90640,16976,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] tests 570 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_184_01 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [59,796736,83200,209920,90640,16976,6177,8270,302,1220,292,336,257,17,1,9,0,1,0,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [59,796736,345344,209920,90640,21072,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(532873,12),(790665,10),(787209,2),(36361,17),(535049,2),(39945,8),(1347713,5),(856193,5),(3186945,29),(2900481,29),(154625,14),(1201153,10),(1332225,4),(1348609,12),(677889,14),(2762753,8),(1265665,1),(3358721,16),(126,11),(266382,6),(263694,28),(65718,16),(69782,7),(16998,16),(283654,13),(348166,6),(7194,7),(526890,25),(790666,1),(133234,9),(196786,4),(134226,13),(138258,18),(149602,3),(543266,5),(737314,12),(725122,6),(856194,6),(677890,7),(872450,5),(295308,3),(1082452,22),(1114516,4),(1086484,2),(1376644,22),(1332228,7),(35928,4),(43096,4),(41368,29),(39960,17),(36424,5),(43592,1),(141424,10),(1089872,4),(1122704,7),(1249424,17),(2106208,25),(2108000,4),(598432,37),(2117184,24),(3294272,19)]
  apply screen [59,796736,83200,209920,90640,16976,6177,8270,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] [59,796736,345344,209920,90640,21072,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] tests 138 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_184_0011 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [59,796736,83200,209920,90640,16976,6689,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [59,796736,345344,209920,90640,21072,6689,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(39945,2),(1089921,1),(665729,6),(856193,11),(2138881,1),(3186945,16),(2377217,3),(2140673,2),(2900481,17),(154625,9),(1201153,5),(1348609,3),(677889,6),(2762753,5),(3358721,3),(3489793,1),(5150,7),(65718,3),(69782,1),(16998,11),(17990,4),(280070,6),(283654,9),(348166,2),(526890,9),(3658,4),(196786,3),(134226,16),(200850,8),(149602,5),(543266,1),(737314,17),(20034,4),(661634,6),(856194,2),(154626,3),(677890,3),(295692,22),(300044,2),(1082452,9),(1114516,1),(1086484,2),(1376644,8),(1332228,1),(1348612,7),(1396740,9),(41368,16),(39064,6),(39960,5),(41800,3),(43592,10),(141424,3),(1089872,9),(1122704,4),(1249424,14),(2106208,20),(598432,16),(2133568,3),(3294272,25)]
  apply screen [59,796736,83200,209920,90640,16976,6689,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] [59,796736,345344,209920,90640,21072,6689,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] tests 83 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_184_0010 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [59,796736,83200,209920,90640,16976,6689,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [59,796736,345344,209920,90640,21072,6689,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(532873,6),(41737,2),(533257,2),(300041,1),(856193,34),(3186945,69),(3219713,10),(2117121,8),(2377217,12),(2393601,10),(2900481,29),(154625,19),(171009,18),(2247681,6),(1348609,23),(677889,15),(2762753,8),(126,5),(5150,4),(266382,6),(263694,43),(267278,2),(69782,28),(16998,40),(17990,14),(331910,2),(280070,39),(348166,19),(6298,17),(526890,19),(3658,15),(530570,12),(133234,6),(134226,30),(200850,26),(138258,10),(149602,1),(543266,9),(673826,1),(737314,41),(20034,2),(856194,6),(154626,35),(677890,15),(872450,15),(380,18),(295692,11),(1082452,23),(1114516,5),(1376644,3),(1332228,23),(1348612,9),(1396740,30),(41368,51),(533288,10),(41800,18),(36424,23),(141424,5),(1089872,7),(1213520,20),(174160,11),(1220688,2),(1122704,18),(1249424,21),(1217552,10),(2106208,67),(598432,70),(2695456,16),(2138944,5),(2117184,10),(3294272,34)]
  apply screen [59,796736,83200,209920,90640,16976,6689,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] [59,796736,345344,209920,90640,21072,6689,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] tests 251 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_184_0001 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [59,796736,83200,209920,90640,16976,6177,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [59,796736,345344,209920,90640,21072,6177,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(39049,2),(530569,3),(295689,2),(36361,6),(296457,1),(535049,5),(300041,3),(665729,3),(1347713,3),(725121,2),(856193,8),(3186945,9),(3219713,3),(2117121,1),(2377217,3),(2640385,3),(2900481,12),(154625,5),(1201153,3),(1348609,4),(677889,8),(2762753,2),(1265665,3),(3358721,7),(4254,8),(65654,6),(69782,1),(16998,6),(17990,6),(283654,10),(526890,9),(530570,1),(790666,2),(196722,4),(134226,8),(137362,4),(200850,3),(138258,5),(213090,2),(737314,11),(725122,1),(154626,4),(677890,2),(34380,4),(295692,14),(65908,1),(1114452,4),(1082452,6),(1086484,2),(1376644,2),(1380484,3),(1348612,3),(1396740,8),(35928,1),(43096,3),(41368,17),(39960,11),(141424,4),(1089872,2),(1089936,2),(1249424,11),(2106208,17),(598432,11),(2138944,4),(3219776,1),(2117184,6),(2133568,3),(2247744,1),(3294272,7),(3358784,7)]
  apply screen [59,796736,83200,209920,90640,16976,6177,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] [59,796736,345344,209920,90640,21072,6177,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] tests 70 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_184_0000 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [59,796736,83200,209920,90640,16976,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [59,796736,345344,209920,90640,21072,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(530569,45),(790665,4),(41737,4),(533257,19),(787209,16),(36361,45),(296457,16),(300041,20),(598401,8),(1122689,4),(665729,2),(856193,63),(1380481,10),(2138881,16),(3186945,91),(2117121,14),(2377217,16),(2900481,46),(154625,2),(171009,28),(2247681,1),(1201153,1),(1217537,8),(1348609,21),(3294209,7),(3425281,5),(677889,33),(872449,5),(2834433,34),(126,23),(4254,4),(5150,21),(266382,18),(263694,46),(65654,16),(69782,30),(16998,24),(82022,16),(17990,27),(331910,2),(280070,51),(283654,16),(2170,29),(6298,21),(526890,36),(3658,10),(530570,5),(196722,1),(134226,39),(200850,4),(138258,14),(543266,10),(673826,8),(737314,53),(150594,1),(661634,7),(725122,2),(154626,80),(677890,9),(872450,20),(380,9),(876,31),(34380,3),(295692,5),(300044,7),(1114452,19),(1082452,49),(1376644,12),(1332228,24),(1396740,69),(8568,4),(41304,5),(41368,86),(39960,29),(533288,17),(41800,8),(36424,4),(141424,4),(1089872,4),(1122640,9),(174160,8),(1122704,13),(1249424,54),(1217552,24),(2106208,98),(598432,99),(3219776,23),(2117184,35),(3294272,29),(3358784,46)]
  apply screen [59,796736,83200,209920,90640,16976,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] [59,796736,345344,209920,90640,21072,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] tests 411 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_185_11 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [63,697344,303488,75264,82224,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [63,697344,303488,91648,82224,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(526209,8),(1055105,5),(1577345,4),(534145,2),(1120385,2),(1642625,4),(1646721,11),(1100033,1),(2123265,2),(2631169,8),(2427905,10),(2696193,3),(2398209,2),(2430977,1),(2789377,12),(1773569,2),(1466369,5),(2564097,1),(1777665,5),(126,12),(1048982,6),(25126,6),(8902,4),(65754,5),(3466,3),(68746,3),(280626,18),(1116306,6),(19746,6),(26146,8),(287778,3),(74946,5),(336962,4),(528588,1),(528780,1),(180276,1),(1216532,10),(49956,17),(156196,1),(533188,1),(664132,9),(1577348,5),(6552,4),(39192,11),(2098792,1),(591048,4),(594120,8),(2688072,8),(2691144,2),(51504,3),(462928,9),(1382416,7),(1511440,1),(2378784,1),(2539552,11),(2434112,1)]
  apply screen [63,697344,303488,75264,82224,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] [63,697344,303488,91648,82224,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] tests 59 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_185_10 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [63,697344,303488,75264,81968,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [63,697344,303488,91648,81968,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(526209,79),(1055105,23),(599169,5),(1120385,2),(1642625,6),(1646721,37),(1100033,26),(1609985,19),(2631169,9),(2253313,5),(2761217,27),(2427905,51),(2696193,19),(2398209,35),(1382401,4),(2789377,40),(1511425,8),(1773569,10),(1466369,31),(1777665,22),(126,65),(8310,7),(1048982,5),(1056918,22),(1065238,7),(17190,6),(25126,30),(2458,3),(66762,10),(3466,16),(68746,31),(280626,71),(1116306,24),(1122450,24),(1067282,4),(1329170,3),(1378322,4),(19746,19),(26146,2),(74946,1),(336962,29),(525004,3),(525196,14),(528780,3),(561420,24),(139380,2),(1216532,35),(1204244,9),(49956,58),(664132,48),(1577348,15),(71832,23),(39192,19),(2098792,36),(591048,7),(594120,34),(2688072,29),(462928,18),(2378784,21),(2539552,43),(2560064,2)]
  apply screen [63,697344,303488,75264,81968,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] [63,697344,303488,91648,81968,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] tests 257 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_185_011 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,697344,303488,75264,82224,25666,8594,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,697344,303488,91648,82224,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(68739,4),(1122435,12),(534145,5),(1120385,1),(1642625,20),(1646721,1),(1100033,25),(1609985,3),(2631169,7),(2761217,6),(2427905,16),(1740801,10),(2789377,2),(1515521,5),(1777665,13),(126,2),(8902,6),(65754,18),(3466,10),(280626,26),(1116306,7),(26146,23),(74946,14),(4316,18),(557836,8),(180276,11),(1216532,5),(49956,29),(156196,6),(533188,11),(664132,11),(1577348,8),(1740804,3),(35128,3),(69848,5),(71832,3),(39192,15),(2098792,1),(526024,7),(591048,3),(594120,8),(2623048,8),(2688072,4),(2691144,15),(51504,2),(313392,1),(462928,26),(1120400,6),(1382416,2),(2498656,4),(2410528,1),(2539552,24),(534208,2),(599232,1),(2434112,6),(2822208,6),(2826304,4)]
  apply screen [62,697344,303488,75264,82224,25666,8594,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] [62,697344,303488,91648,82224,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] tests 101 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_185_010 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,697344,303488,75264,82224,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,697344,303488,91648,82224,25666,8338,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(3459,5),(68739,7),(1122435,17),(1067267,6),(330755,3),(1055105,6),(1577345,7),(534145,14),(1120385,7),(1646721,6),(1100033,9),(2631169,5),(2761217,7),(2427905,11),(2398209,4),(2430977,2),(1740801,12),(2789377,7),(1773569,3),(2822145,6),(1466369,2),(1777665,7),(2826241,1),(126,11),(16694,3),(1065238,2),(25126,5),(8902,4),(65754,5),(66762,5),(3466,7),(18738,1),(280626,25),(26146,25),(287778,3),(74946,9),(336962,4),(32892,7),(4316,10),(528588,3),(525196,5),(528780,3),(163956,4),(180276,5),(168020,5),(1053076,4),(1216532,7),(49956,20),(156196,9),(533188,11),(664132,5),(692292,6),(1577348,8),(69848,6),(6552,6),(71832,4),(39192,10),(591048,3),(594120,5),(2688072,9),(2658376,14),(2691144,2),(526216,4),(51504,3),(462928,16),(1120400,7),(1382416,6),(1511440,3),(2368608,3),(2410528,3),(2539552,26),(599232,7),(2434112,4),(2789440,3)]
  apply screen [62,697344,303488,75264,82224,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] [62,697344,303488,91648,82224,25666,8338,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] tests 104 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_185_001 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,697344,303488,75264,81968,25666,8594,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,697344,303488,91648,81968,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(526209,35),(1642625,19),(1646721,6),(1100033,35),(1609985,18),(2761217,2),(2785793,19),(2427905,28),(2430977,3),(2789377,5),(1773569,1),(1466369,18),(1777665,22),(126,15),(1048982,1),(1056918,30),(8902,6),(3370,7),(66762,2),(3466,19),(68746,2),(280626,35),(73938,1),(1116306,4),(26146,19),(74946,24),(4316,16),(525004,4),(528588,2),(525196,7),(561420,24),(139380,11),(180276,5),(1216532,22),(1204244,5),(49956,42),(533188,15),(664132,15),(1577348,1),(1740804,2),(35128,7),(69848,2),(6552,5),(71832,20),(39192,22),(2098792,18),(526024,2),(591048,6),(594120,4),(2623048,1),(2688072,15),(2691144,19),(462928,19),(467024,7),(1120400,5),(2368608,2),(2277920,6),(2378784,9),(2539552,35),(2434112,4),(2560064,5),(2564160,12),(2826304,16)]
  apply screen [62,697344,303488,75264,81968,25666,8594,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] [62,697344,303488,91648,81968,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] tests 158 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_185_000 :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [62,697344,303488,75264,81968,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [62,697344,303488,91648,81968,25666,8338,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(3459,9),(68739,19),(74883,47),(1116291,11),(1122435,72),(19715,10),(1067267,20),(526209,90),(1055105,43),(599169,9),(1120385,17),(1642625,32),(1087745,39),(1100033,47),(1609985,30),(2761217,42),(2785793,42),(2427905,62),(2398209,4),(2430977,30),(2527233,3),(1740801,34),(2789377,21),(1511425,33),(1773569,5),(2822145,18),(1777665,45),(126,82),(8406,17),(1056918,55),(25126,29),(65754,6),(66762,61),(3466,53),(280626,110),(73938,6),(19746,10),(26146,104),(336962,20),(32892,13),(4316,35),(528588,31),(525196,43),(528780,11),(561420,13),(168020,23),(1053076,2),(1216532,43),(1204244,13),(49956,130),(533188,19),(664132,61),(692292,30),(1577348,30),(1740804,4),(6552,28),(71832,37),(39192,37),(2098792,18),(591048,11),(594120,38),(2688072,28),(2658376,97),(526216,3),(313392,19),(462928,51),(1120400,16),(1382416,18),(1515536,16),(2378784,28),(2539552,124),(599232,20),(2434112,26),(2696256,11),(2527296,1),(2789440,8),(2560064,29),(2822208,19),(2564160,11),(2826304,2)]
  apply screen [62,697344,303488,75264,81968,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] [62,697344,303488,91648,81968,25666,8338,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] tests 517 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_186_root :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [63,831488,418816,50496,24912,21026,21026,2822,835,2068,517,548,145,3,2,9,2,0,4,1,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [63,831488,418816,50496,24912,21026,21026,2822,835,2068,517,548,145,3,2,9,2,0,4,1,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(1345665,2),(2691329,2),(797185,2),(807937,2),(3350529,2),(3325953,2),(126,2),(529446,2),(264774,2),(6534,2),(74282,1),(10826,1),(76298,1),(598306,1),(596226,1),(600322,1),(17524,1),(50260,1),(54292,1),(297156,1),(311492,1),(315524,1),(2163000,2),(1081560,2),(1188424,2),(1059208,2),(2245680,2),(2118032,2),(722464,2),(427584,2)]
  apply screen [63,831488,418816,50496,24912,21026,21026,2822,835,2068,517,548,145,3,2,9,2,0,4,1,0,0] [63,831488,418816,50496,24912,21026,21026,2822,835,2068,517,548,145,3,2,9,2,0,4,1,0,0] tests 11 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_187_root :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [63,570368,145664,152096,114824,28706,7240,9120,422,661,1552,515,40,65,8,12,4,4,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [63,570368,145664,152096,114824,28706,7240,9120,422,661,1552,515,40,65,8,12,4,4,0,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(1837185,1),(3674369,1),(2433537,1),(926721,1),(1165313,1),(2281473,1),(126,1),(787590,1),(271110,1),(3226,1),(330258,1),(1049538,1),(528780,1),(140340,1),(2109732,1),(53352,1),(1067208,1),(676872,1),(98928,1),(216080,1),(2334752,1),(3179328,1)]
  apply screen [63,570368,145664,152096,114824,28706,7240,9120,422,661,1552,515,40,65,8,12,4,4,0,0,0,0] [63,570368,145664,152096,114824,28706,7240,9120,422,661,1552,515,40,65,8,12,4,4,0,0,0,0] tests 6 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_188_root :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [63,937984,443392,57480,26760,33488,8596,4514,4450,2433,800,531,146,33,8,12,1,0,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [63,937984,443392,57480,26760,33488,8596,4514,4450,2433,800,531,146,33,8,12,1,0,0,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(919681,1),(856321,1),(1100289,1),(2143233,1),(3547137,1),(3751937,1),(126,1),(2854,1),(5318,1),(42010,1),(134290,1),(274754,1),(49692,1),(70412,1),(542884,1),(2175048,1),(1155592,1),(1198128,1),(2278416,1),(786912,1),(1639200,1),(2491584,1)]
  apply screen [63,937984,443392,57480,26760,33488,8596,4514,4450,2433,800,531,146,33,8,12,1,0,0,0,0,0] [63,937984,443392,57480,26760,33488,8596,4514,4450,2433,800,531,146,33,8,12,1,0,0,0,0,0] tests 6 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_189_root :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [47,992,299776,143936,45584,9986,12386,13824,4544,2596,904,402,26,19,64,16,2,2,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [63,992,299776,143936,45584,9986,12386,13824,4544,2596,904,402,26,19,64,16,2,2,0,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(3969,3),(639105,2),(1585409,3),(1458689,3),(2302977,3),(2398209,3),(126,2),(1589262,1),(598038,1),(213062,1),(1646598,1),(1654790,1),(561178,1),(311370,1),(835594,1),(1851402,1),(2195538,1),(2658322,1),(2719762,1),(3538978,3),(245826,1),(2326594,1),(3682306,1),(3936258,1),(3350530,1),(524700,1),(17100,1),(17292,1),(541068,1),(66772,1),(74900,1),(598164,1),(1057572,3),(82628,1),(213572,1),(10116,1),(206340,1),(1253892,1),(35032,1),(528792,1),(561304,1),(268584,3),(51400,1),(313416,1),(281352,1),(1327880,1),(1839368,1),(2110512,3),(36048,1),(99536,1),(7568,1),(13712,1),(2137104,1),(134752,3),(412224,1),(2264128,1),(2525248,1)]
  apply screen [47,992,299776,143936,45584,9986,12386,13824,4544,2596,904,402,26,19,64,16,2,2,0,0,0,0] [63,992,299776,143936,45584,9986,12386,13824,4544,2596,904,402,26,19,64,16,2,2,0,0,0,0] tests 17 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem leaf_190_root :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [63,992,50704,152704,49936,49744,5890,14400,6664,2496,452,424,74,134,5,4,8,0,0,0,0,0]) → (∀ i, K i ≤ 6) →
      (∀ s, (s,6) ∈ enum [63,992,50704,152704,49936,49744,5890,14400,6664,2496,452,424,74,134,5,4,8,0,0,0,0,0] →
          ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card ≤ 1) → False := by
  intro enum R K mem size cap
  let tests : List (Nat × Nat) := [(34689,1),(11137,1),(68993,1),(99713,1),(7809,1),(38529,1),(14977,1),(405633,3),(20225,1),(27393,1),(85249,1),(753921,3),(1597953,3),(3183617,3),(2443265,3),(3543041,1),(1974273,1),(3948545,1),(3833857,1),(3080193,1),(126,4),(1605646,1),(2195478,1),(606246,1),(3162182,1),(3686406,3),(167962,1),(663594,1),(1060938,1),(1736714,3),(458802,1),(2363474,1),(2555922,3),(286818,1),(925730,3),(3412034,3),(34076,1),(34572,3),(1082892,1),(67892,1),(2165780,1),(2196500,3),(19044,1),(541476,1),(606500,3),(20036,3),(2116676,1),(2182148,1),(5336,1),(164248,1),(168088,3),(8936,1),(9128,3),(533288,1),(1054280,1),(1061448,3),(1086984,1),(68016,3),(197040,1),(7376,3),(268496,1),(229776,1),(272608,1),(288864,3),(549664,1),(276672,1)]
  apply screen [63,992,50704,152704,49936,49744,5890,14400,6664,2496,452,424,74,134,5,4,8,0,0,0,0,0] [63,992,50704,152704,49936,49744,5890,14400,6664,2496,452,424,74,134,5,4,8,0,0,0,0,0] tests 22 ?_ ?_ ?_ R K mem size cap
  · decide +kernel
  · decide +kernel
  · decide +kernel

end E151Screen

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H2_R1_H2_R1
open SimpleGraph Finset

/-- Completeness of the maximal 22-vertex representatives for the edge range below. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (M : SimpleGraph V) [DecidableRel M.Adj],
    Fintype.card V = 22 → M.CliqueFree 3 → Mᶜ.CliqueFree 7 →
    (∀ N : SimpleGraph V, M ≤ N → N.CliqueFree 3 → N = M) → M.edgeFinset.card ≤ 64 →
    ∃ b ∈ ([
      [2031616,145410,401921,24704,11376,34100,9041,11332,3649,2200,580,129,23,16,32,32,5,0,0,0,0,0],
      [1836036,459777,287744,27648,92208,53777,5284,5936,5476,1066,71,80,260,33,34,1,0,0,0,0,0,0]] : List (List Nat)), ∃ f : Fin 22 ≃ V, ∀ i j,
      M.Adj (f i) (f j) ↔ (SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)).Adj i j

/-- Completeness of the maximal 22-vertex representatives for the edge range below. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (M : SimpleGraph V) [DecidableRel M.Adj],
    Fintype.card V = 22 → M.CliqueFree 3 → Mᶜ.CliqueFree 7 →
    (∀ N : SimpleGraph V, M ≤ N → N.CliqueFree 3 → N = M) → M.edgeFinset.card = 65 →
    ∃ b ∈ ([
      [1785856,937984,295872,99024,43170,43154,16788,4297,4865,1600,24,48,85,21,4,1,0,0,1,0,0,0],
      [1884160,888832,329504,82784,35114,34986,20772,5201,321,80,1097,280,24,3,16,4,2,2,1,0,0,0],
      [1933312,864256,148620,82484,34831,33352,16528,10792,330,147,1312,25,162,7,16,8,2,1,1,0,0,0],
      [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,672,328,82,16,8,2,1,1,0,0,0],
      [1351681,368640,19526,6407,98376,12306,9364,4440,1571,2144,1108,200,337,84,1,0,1,0,4,1,0,0],
      [1359873,364544,6195,20642,20642,8515,2322,12804,6273,673,168,804,396,63,0,0,0,0,4,1,0,0]] : List (List Nat)), ∃ f : Fin 22 ≃ V, ∀ i j,
      M.Adj (f i) (f j) ↔ (SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)).Adj i j

/-- Completeness of the maximal 22-vertex representatives for the edge range below. -/
def H3 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (M : SimpleGraph V) [DecidableRel M.Adj],
    Fintype.card V = 22 → M.CliqueFree 3 → Mᶜ.CliqueFree 7 →
    (∀ N : SimpleGraph V, M ≤ N → N.CliqueFree 3 → N = M) → 66 ≤ M.edgeFinset.card →
    ∃ b ∈ ([
      [63,757760,274816,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0],
      [63,983552,417856,50752,54784,37444,1633,4167,1172,808,1106,45,192,192,66,1,2,1,0,0,0,0],
      [63,829440,361504,173088,100928,12880,10785,8780,2380,295,548,130,257,1,9,1,5,1,0,1,0,0],
      [63,796736,345344,209920,90640,21072,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0],
      [63,697344,303488,91648,82224,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0],
      [63,831488,418816,50496,24912,21026,21026,2822,835,2068,517,548,145,3,2,9,2,0,4,1,0,0],
      [63,570368,145664,152096,114824,28706,7240,9120,422,661,1552,515,40,65,8,12,4,4,0,0,0,0],
      [63,937984,443392,57480,26760,33488,8596,4514,4450,2433,800,531,146,33,8,12,1,0,0,0,0,0],
      [63,992,299776,143936,45584,9986,12386,13824,4544,2596,904,402,26,19,64,16,2,2,0,0,0,0],
      [63,992,50704,152704,49936,49744,5890,14400,6664,2496,452,424,74,134,5,4,8,0,0,0,0,0]] : List (List Nat)), ∃ f : Fin 22 ≃ V, ∀ i j,
      M.Adj (f i) (f j) ↔ (SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (b.getD i.val 0).testBit (j.val-i.val-1) = true)).Adj i j

section CertificateApplications

private theorem screen_8 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([1785856,937984,295872,99024,43170,43154,16788,4297,4865,1600,24,48,85,21,4,1,0,0,1,0,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_8 D free upper
  · exact E151Rows.close_coded [737280,675840,295872,99024,43170,43154,16788,4297,4865,1600,24,48,85,21,4,1,0,0,1,0,0,0] [1785856,937984,295872,99024,43170,43154,16788,4297,4865,1600,24,48,85,21,4,1,0,0,1,0,0,0] D A rows size cap
      E151Screen.leaf_8_root (by decide +kernel)

private theorem screen_10 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([1884160,888832,329504,82784,35114,34986,20772,5201,321,80,1097,280,24,3,16,4,2,2,1,0,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_10 D free upper
  · exact E151Rows.close_coded [1884160,888832,329504,82784,35114,34986,4388,1105,321,80,1033,264,24,3,0,0,2,2,1,0,0,0] [1884160,888832,329504,82784,35114,34986,20772,5201,321,80,1097,280,24,3,16,4,2,2,1,0,0,0] D A rows size cap
      E151Screen.leaf_10_root (by decide +kernel)

private theorem screen_28 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([1933312,864256,148620,82484,34831,33352,16528,10792,330,147,1312,25,162,7,16,8,2,1,1,0,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_28 D free upper
  · exact E151Rows.close_coded [1933312,864256,148620,82484,34831,33352,16528,10280,330,147,1280,25,162,5,16,8,2,1,1,0,0,0] [1933312,864256,148620,82484,34831,33352,16528,10792,330,147,1312,25,162,7,16,8,2,1,1,0,0,0] D A rows size cap
      E151Screen.leaf_28_1 (by decide +kernel)
  · exact E151Rows.close_coded [1933312,864256,148620,82468,34831,33352,16528,10280,330,147,1280,25,162,5,16,8,2,1,1,0,0,0] [1933312,864256,148620,82468,34831,33352,16528,10792,330,147,1312,25,162,7,16,8,2,1,1,0,0,0] D A rows size cap
      E151Screen.leaf_28_0 (by decide +kernel)

private theorem screen_63 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,672,328,82,16,8,2,1,1,0,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_63 D free upper
  · exact E151Rows.close_coded [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,640,328,80,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,672,328,82,16,8,2,1,1,0,0,0] D A rows size cap
      E151Screen.leaf_63_1111 (by decide +kernel)
  · exact E151Rows.close_coded [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,640,320,80,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1324,397,312,90,648,672,320,82,16,8,2,1,1,0,0,0] D A rows size cap
      E151Screen.leaf_63_1110 (by decide +kernel)
  · exact E151Rows.close_coded [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,640,328,82,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,672,328,82,16,8,2,1,1,0,0,0] D A rows size cap
      E151Screen.leaf_63_11011 (by decide +kernel)
  · exact E151Rows.close_coded [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,640,320,82,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1324,397,312,90,640,672,320,82,16,8,2,1,1,0,0,0] D A rows size cap
      E151Screen.leaf_63_11010 (by decide +kernel)
  · exact E151Rows.close_coded [1728512,966656,266406,132619,37008,17441,1320,397,312,90,648,640,320,80,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1320,397,312,90,648,672,328,82,16,8,2,1,1,0,0,0] D A rows size cap
      E151Screen.leaf_63_101 (by decide +kernel)
  · exact E151Rows.close_coded [1728512,966656,266406,132619,37008,17441,1320,397,312,90,640,640,320,80,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1320,397,312,90,640,672,328,82,16,8,2,1,1,0,0,0] D A rows size cap
      E151Screen.leaf_63_100 (by decide +kernel)
  · exact E151Rows.close_coded [1728512,966656,266406,132619,37008,17441,1324,396,312,90,648,640,320,80,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1324,396,312,90,648,672,328,82,16,8,2,1,1,0,0,0] D A rows size cap
      E151Screen.leaf_63_011 (by decide +kernel)
  · exact E151Rows.close_coded [1728512,966656,266406,132619,37008,17441,1324,396,312,90,640,640,320,80,16,8,2,1,0,0,0,0] [1728512,966656,266406,132619,37008,17441,1324,396,312,90,640,672,328,82,16,8,2,1,1,0,0,0] D A rows size cap
      E151Screen.leaf_63_010 (by decide +kernel)

private theorem screen_138 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([2031616,145410,401921,24704,11376,34100,9041,11332,3649,2200,580,129,23,16,32,32,5,0,0,0,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_138 D free upper
  · exact E151Rows.close_coded [2031616,145410,401921,24704,11376,34100,9041,3140,1601,2200,580,129,23,16,32,32,1,0,0,0,0,0] [2031616,145410,401921,24704,11376,34100,9041,11332,3649,2200,580,129,23,16,32,32,5,0,0,0,0,0] D A rows size cap
      E151Screen.leaf_138_root (by decide +kernel)

private theorem screen_146 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([1836036,459777,287744,27648,92208,53777,5284,5936,5476,1066,71,80,260,33,34,1,0,0,0,0,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_146 D free upper
  · exact E151Rows.close_coded [1836036,459777,287744,27648,84016,21009,5284,5936,5476,1066,71,80,260,33,34,1,0,0,0,0,0,0] [1836036,459777,287744,27648,92208,53777,5284,5936,5476,1066,71,80,260,33,34,1,0,0,0,0,0,0] D A rows size cap
      E151Screen.leaf_146_root (by decide +kernel)

private theorem screen_161 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([1351681,368640,19526,6407,98376,12306,9364,4440,1571,2144,1108,200,337,84,1,0,1,0,4,1,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_161 D free upper
  · exact E151Rows.close_coded [1351680,368640,19526,6407,98376,12306,9364,4440,1571,2144,1108,200,337,84,0,0,1,0,4,1,0,0] [1351681,368640,19526,6407,98376,12306,9364,4440,1571,2144,1108,200,337,84,1,0,1,0,4,1,0,0] D A rows size cap
      E151Screen.leaf_161_root (by decide +kernel)

private theorem screen_175 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([1359873,364544,6195,20642,20642,8515,2322,12804,6273,673,168,804,396,63,0,0,0,0,4,1,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_175 D free upper
  · exact E151Rows.close_coded [1359873,364544,6195,20642,20642,8515,2322,4612,4225,673,168,772,388,63,0,0,0,0,4,1,0,0] [1359873,364544,6195,20642,20642,8515,2322,12804,6273,673,168,804,396,63,0,0,0,0,4,1,0,0] D A rows size cap
      E151Screen.leaf_175_root (by decide +kernel)

private theorem screen_181 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([63,757760,274816,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_181 D free upper
  · exact E151Rows.close_coded [63,757760,274816,68352,81968,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] [63,757760,274816,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] D A rows size cap
      E151Screen.leaf_181_11 (by decide +kernel)
  · exact E151Rows.close_coded [63,757760,270720,68352,81968,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] [63,757760,270720,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] D A rows size cap
      E151Screen.leaf_181_10 (by decide +kernel)
  · exact E151Rows.close_coded [62,757760,274816,68352,82224,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] [62,757760,274816,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] D A rows size cap
      E151Screen.leaf_181_0111 (by decide +kernel)
  · exact E151Rows.close_coded [62,757760,270720,68352,82224,26660,8353,9888,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] [62,757760,270720,84736,82224,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] D A rows size cap
      E151Screen.leaf_181_01101 (by decide +kernel)
  · exact E151Rows.close_coded [62,757760,270720,68352,82224,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] [62,757760,270720,84736,82224,26660,8865,1696,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] D A rows size cap
      E151Screen.leaf_181_01100 (by decide +kernel)
  · exact E151Rows.close_coded [62,757760,274816,68352,82224,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] [62,757760,274816,84736,82224,26660,8865,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] D A rows size cap
      E151Screen.leaf_181_0101 (by decide +kernel)
  · exact E151Rows.close_coded [62,757760,270720,68352,82224,26660,8865,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] [62,757760,270720,84736,82224,26660,8865,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] D A rows size cap
      E151Screen.leaf_181_01001 (by decide +kernel)
  · exact E151Rows.close_coded [62,757760,270720,68352,82224,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] [62,757760,270720,84736,82224,26660,8353,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] D A rows size cap
      E151Screen.leaf_181_01000 (by decide +kernel)
  · exact E151Rows.close_coded [62,757760,270720,84736,81968,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] [62,757760,274816,84736,81968,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] D A rows size cap
      E151Screen.leaf_181_0011 (by decide +kernel)
  · exact E151Rows.close_coded [62,757760,270720,68352,81968,26660,8353,1696,4776,226,712,67,80,5,1,8,4,0,0,0,1,0] [62,757760,274816,68352,81968,26660,8865,9888,4776,1250,712,67,80,5,1,8,4,0,0,0,1,0] D A rows size cap
      E151Screen.leaf_181_0010 (by decide +kernel)
  · exact E151Rows.close_coded [62,757760,270720,68352,81968,26660,8865,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] [62,757760,274816,84736,81968,26660,8865,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] D A rows size cap
      E151Screen.leaf_181_0001 (by decide +kernel)
  · exact E151Rows.close_coded [62,757760,270720,68352,81968,26660,8353,1696,4776,226,704,67,80,5,1,8,4,0,0,0,1,0] [62,757760,274816,84736,81968,26660,8353,9888,4776,1250,704,67,80,5,1,8,4,0,0,0,1,0] D A rows size cap
      E151Screen.leaf_181_0000 (by decide +kernel)

private theorem screen_182 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([63,983552,417856,50752,54784,37444,1633,4167,1172,808,1106,45,192,192,66,1,2,1,0,0,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_182 D free upper
  · exact E151Rows.close_coded [63,983552,155712,17984,54784,36932,1633,4167,1172,808,1106,45,192,192,64,1,2,1,0,0,0,0] [63,983552,417856,50752,54784,37444,1633,4167,1172,808,1106,45,192,192,66,1,2,1,0,0,0,0] D A rows size cap
      E151Screen.leaf_182_11 (by decide +kernel)
  · exact E151Rows.close_coded [63,983552,155712,17984,54784,36932,1633,4167,1172,808,1104,45,192,192,64,1,2,1,0,0,0,0] [63,983552,417856,50752,54784,37444,1633,4167,1172,808,1104,45,192,192,66,1,2,1,0,0,0,0] D A rows size cap
      E151Screen.leaf_182_10 (by decide +kernel)
  · exact E151Rows.close_coded [55,983552,155712,17984,54784,36932,1633,4167,1172,808,1106,45,192,192,64,1,2,1,0,0,0,0] [55,983552,417856,50752,54784,37444,1633,4167,1172,808,1106,45,192,192,66,1,2,1,0,0,0,0] D A rows size cap
      E151Screen.leaf_182_01 (by decide +kernel)
  · exact E151Rows.close_coded [55,983552,155712,17984,54784,37444,1633,4167,1172,808,1104,45,192,192,64,1,2,1,0,0,0,0] [55,983552,417856,50752,54784,37444,1633,4167,1172,808,1104,45,192,192,66,1,2,1,0,0,0,0] D A rows size cap
      E151Screen.leaf_182_001 (by decide +kernel)
  · exact E151Rows.close_coded [55,983552,155712,17984,54784,36932,1633,4167,1172,808,1104,45,192,192,64,1,2,1,0,0,0,0] [55,983552,417856,50752,54784,36932,1633,4167,1172,808,1104,45,192,192,66,1,2,1,0,0,0,0] D A rows size cap
      E151Screen.leaf_182_000 (by decide +kernel)

private theorem screen_183 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([63,829440,361504,173088,100928,12880,10785,8780,2380,295,548,130,257,1,9,1,5,1,0,1,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_183 D free upper
  · exact E151Rows.close_coded [63,829440,361504,42016,100928,12368,10785,8268,2380,291,548,130,257,1,9,1,5,1,0,1,0,0] [63,829440,361504,173088,100928,12880,10785,8780,2380,295,548,130,257,1,9,1,5,1,0,1,0,0] D A rows size cap
      E151Screen.leaf_183_11 (by decide +kernel)
  · exact E151Rows.close_coded [63,829440,361504,42016,100928,12368,10785,8268,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] [63,829440,361504,173088,100928,12880,10785,8780,2376,295,548,130,257,1,9,1,5,1,0,1,0,0] D A rows size cap
      E151Screen.leaf_183_10 (by decide +kernel)
  · exact E151Rows.close_coded [62,829440,361504,42016,100928,12368,10785,8268,2380,291,548,130,257,1,9,1,5,1,0,1,0,0] [62,829440,361504,173088,100928,12880,10785,8780,2380,295,548,130,257,1,9,1,5,1,0,1,0,0] D A rows size cap
      E151Screen.leaf_183_01 (by decide +kernel)
  · exact E151Rows.close_coded [62,829440,361504,42016,100928,12368,10785,8268,2376,295,548,130,257,1,9,1,5,1,0,1,0,0] [62,829440,361504,173088,100928,12880,10785,8780,2376,295,548,130,257,1,9,1,5,1,0,1,0,0] D A rows size cap
      E151Screen.leaf_183_001 (by decide +kernel)
  · exact E151Rows.close_coded [62,829440,361504,42016,100928,12368,10785,8780,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] [62,829440,361504,173088,100928,12880,10785,8780,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] D A rows size cap
      E151Screen.leaf_183_0001 (by decide +kernel)
  · exact E151Rows.close_coded [62,829440,361504,42016,100928,12368,10785,8268,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] [62,829440,361504,173088,100928,12880,10785,8268,2376,291,548,130,257,1,9,1,5,1,0,1,0,0] D A rows size cap
      E151Screen.leaf_183_0000 (by decide +kernel)

private theorem screen_184 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([63,796736,345344,209920,90640,21072,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_184 D free upper
  · exact E151Rows.close_coded [63,796736,83200,209920,90640,21072,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] [63,796736,345344,209920,90640,21072,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] D A rows size cap
      E151Screen.leaf_184_11 (by decide +kernel)
  · exact E151Rows.close_coded [63,796736,83200,209920,90640,16976,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] [63,796736,345344,209920,90640,16976,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] D A rows size cap
      E151Screen.leaf_184_10 (by decide +kernel)
  · exact E151Rows.close_coded [59,796736,83200,209920,90640,16976,6177,8270,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] [59,796736,345344,209920,90640,21072,6689,8270,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] D A rows size cap
      E151Screen.leaf_184_01 (by decide +kernel)
  · exact E151Rows.close_coded [59,796736,83200,209920,90640,16976,6689,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] [59,796736,345344,209920,90640,21072,6689,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] D A rows size cap
      E151Screen.leaf_184_0011 (by decide +kernel)
  · exact E151Rows.close_coded [59,796736,83200,209920,90640,16976,6689,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] [59,796736,345344,209920,90640,21072,6689,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] D A rows size cap
      E151Screen.leaf_184_0010 (by decide +kernel)
  · exact E151Rows.close_coded [59,796736,83200,209920,90640,16976,6177,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] [59,796736,345344,209920,90640,21072,6177,8262,302,1220,292,336,257,17,1,11,0,1,0,1,0,0] D A rows size cap
      E151Screen.leaf_184_0001 (by decide +kernel)
  · exact E151Rows.close_coded [59,796736,83200,209920,90640,16976,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] [59,796736,345344,209920,90640,21072,6177,8262,302,1220,292,336,257,17,1,9,0,1,0,1,0,0] D A rows size cap
      E151Screen.leaf_184_0000 (by decide +kernel)

private theorem screen_185 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([63,697344,303488,91648,82224,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_185 D free upper
  · exact E151Rows.close_coded [63,697344,303488,75264,82224,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] [63,697344,303488,91648,82224,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] D A rows size cap
      E151Screen.leaf_185_11 (by decide +kernel)
  · exact E151Rows.close_coded [63,697344,303488,75264,81968,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] [63,697344,303488,91648,81968,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] D A rows size cap
      E151Screen.leaf_185_10 (by decide +kernel)
  · exact E151Rows.close_coded [62,697344,303488,75264,82224,25666,8594,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] [62,697344,303488,91648,82224,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] D A rows size cap
      E151Screen.leaf_185_011 (by decide +kernel)
  · exact E151Rows.close_coded [62,697344,303488,75264,82224,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] [62,697344,303488,91648,82224,25666,8338,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] D A rows size cap
      E151Screen.leaf_185_010 (by decide +kernel)
  · exact E151Rows.close_coded [62,697344,303488,75264,81968,25666,8594,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] [62,697344,303488,91648,81968,25666,8594,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] D A rows size cap
      E151Screen.leaf_185_001 (by decide +kernel)
  · exact E151Rows.close_coded [62,697344,303488,75264,81968,25666,8338,9920,912,326,594,162,3,2,18,1,0,0,1,0,1,0] [62,697344,303488,91648,81968,25666,8338,9920,5008,1350,594,162,3,2,18,1,0,0,1,0,1,0] D A rows size cap
      E151Screen.leaf_185_000 (by decide +kernel)

private theorem screen_186 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([63,831488,418816,50496,24912,21026,21026,2822,835,2068,517,548,145,3,2,9,2,0,4,1,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_186 D free upper
  · exact E151Rows.close_coded [63,831488,418816,50496,24912,21026,21026,2822,835,2068,517,548,145,3,2,9,2,0,4,1,0,0] [63,831488,418816,50496,24912,21026,21026,2822,835,2068,517,548,145,3,2,9,2,0,4,1,0,0] D A rows size cap
      E151Screen.leaf_186_root (by decide +kernel)

private theorem screen_187 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([63,570368,145664,152096,114824,28706,7240,9120,422,661,1552,515,40,65,8,12,4,4,0,0,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_187 D free upper
  · exact E151Rows.close_coded [63,570368,145664,152096,114824,28706,7240,9120,422,661,1552,515,40,65,8,12,4,4,0,0,0,0] [63,570368,145664,152096,114824,28706,7240,9120,422,661,1552,515,40,65,8,12,4,4,0,0,0,0] D A rows size cap
      E151Screen.leaf_187_root (by decide +kernel)

private theorem screen_188 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([63,937984,443392,57480,26760,33488,8596,4514,4450,2433,800,531,146,33,8,12,1,0,0,0,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_188 D free upper
  · exact E151Rows.close_coded [63,937984,443392,57480,26760,33488,8596,4514,4450,2433,800,531,146,33,8,12,1,0,0,0,0,0] [63,937984,443392,57480,26760,33488,8596,4514,4450,2433,800,531,146,33,8,12,1,0,0,0,0,0] D A rows size cap
      E151Screen.leaf_188_root (by decide +kernel)

private theorem screen_189 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([63,992,299776,143936,45584,9986,12386,13824,4544,2596,904,402,26,19,64,16,2,2,0,0,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_189 D free upper
  · exact E151Rows.close_coded [47,992,299776,143936,45584,9986,12386,13824,4544,2596,904,402,26,19,64,16,2,2,0,0,0,0] [63,992,299776,143936,45584,9986,12386,13824,4544,2596,904,402,26,19,64,16,2,2,0,0,0,0] D A rows size cap
      E151Screen.leaf_189_root (by decide +kernel)

private theorem screen_190 (D : SimpleGraph (Fin 22)) [DecidableRel D.Adj]
    (A : Fin 5 → Finset (Fin 22))
    (upper : D ≤ SimpleGraph.fromRel (fun i j : Fin 22 => i < j ∧ (([63,992,50704,152704,49936,49744,5890,14400,6664,2496,452,424,74,134,5,4,8,0,0,0,0,0] : List Nat).getD i.val 0).testBit (j.val-i.val-1) = true)) (free : Dᶜ.CliqueFree 7)
    (rows : ∀ i, Dᶜ.IsClique (A i)) (size : ∀ i, 4 ≤ (A i).card ∧ (A i).card ≤ 6)
    (cap : ∀ S, Dᶜ.IsNClique 6 S → (univ.filter (fun i => Disjoint (A i) S)).card ≤ 1) :
    False := by
  apply E151D5.interval_190 D free upper
  · exact E151Rows.close_coded [63,992,50704,152704,49936,49744,5890,14400,6664,2496,452,424,74,134,5,4,8,0,0,0,0,0] [63,992,50704,152704,49936,49744,5890,14400,6664,2496,452,424,74,134,5,4,8,0,0,0,0,0] D A rows size cap
      E151Screen.leaf_190_root (by decide +kernel)

end CertificateApplications

theorem main : H1 → H2 → H3 → OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H2_R1.H2 := by
  classical
  intro h1 h2 h3 G tri degree root
  obtain ⟨v,hv⟩ := root
  by_contra noEight
  apply E151Rows.extract G tri degree v hv noEight
  intro V _ _ D _ A order htri hfree rows size cap _ _
  obtain ⟨M,sub,mtri,mfree,maximal⟩ := E151D5.maximal_extension D htri hfree
  by_cases low : M.edgeFinset.card ≤ 64
  · obtain ⟨b,hb,f,label⟩ := h1 V M order mtri mfree maximal low
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_138
    · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_146
  · by_cases mid : M.edgeFinset.card = 65
    · obtain ⟨b,hb,f,label⟩ := h2 V M order mtri mfree maximal mid
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_8
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_10
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_28
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_63
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_161
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_175
    · obtain ⟨b,hb,f,label⟩ := h3 V M order mtri mfree maximal (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_181
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_182
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_183
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_184
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_185
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_186
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_187
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_188
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_189
      · exact E151Rows.transport D M _ f sub label hfree A rows size cap screen_190

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H2_R1_H2_R1
