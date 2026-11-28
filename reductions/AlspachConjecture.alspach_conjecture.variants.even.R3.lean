import FormalConjectures.Wikipedia.AlspachConjecture
import Mathlib

/-! The square extension in Bryant–Horsley–Pettersson, Lemma 19.
Adding one pair to a cocktail-party graph adds one square for each old pair.
Induction thus eliminates every shorter list with enough squares.
Matching indexing and cycle transport are adapted from the registered R2 by @sturdy4days. -/
namespace OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R3
open SimpleGraph AlspachConjecture Finset
open scoped Classical

theorem extend {α : Type*} [Fintype α] [DecidableEq α] (C : Multiset (Cycle ((completeGraph α).comap (Prod.fst (β := Bool)))))
    (hc : IsCycleDecomposition ((completeGraph α).comap (Prod.fst (β := Bool))) C) :
    ∃ D : Multiset (Cycle ((completeGraph (Option α)).comap (Prod.fst (β := Bool)))), IsCycleDecomposition _ D ∧
      lengths D = lengths C + Multiset.replicate (Fintype.card α) 4 := by
  classical
  let G := ((completeGraph α).comap (Prod.fst (β := Bool)))
  let G' := ((completeGraph (Option α)).comap (Prod.fst (β := Bool)))
  let inc (p : α × Bool) : Option α × Bool := (some p.1,p.2)
  have inc_inj : Function.Injective inc := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    simpa [inc] using h
  let emb : G →g G' :=
    { toFun := inc, map_rel' := fun h eq => h (Option.some.inj eq) }
  let up (c : Cycle G) : Cycle G' :=
    ⟨inc c.base, c.walk.map emb, c.isCycle.map (f := emb) inc_inj⟩
  have paths (c : Cycle G) : (up c).edges = c.edges.map (Sym2.map inc) := by
    exact Walk.edges_map _ _
  have old (c : Cycle G) (x y : α × Bool) :
      s(inc x,inc y) ∈ (up c).edges ↔ s(x,y) ∈ c.edges := by
    rw [paths]; change Sym2.map inc s(x,y) ∈ List.map (Sym2.map inc) c.edges ↔ _
    exact List.mem_map_of_injective (Sym2.map.injective inc_inj)
  have fresh (c : Cycle G) (b : Bool) (y : Option α × Bool) :
      s((none,b),y) ∉ (up c).edges := by
    rw [paths]; intro h
    obtain ⟨p,_,eq⟩ := List.mem_map.mp h
    induction p using Sym2.ind with
    | h x z => simp [inc] at eq
  let w (i : α) : G'.Walk ((none : Option α),false) (none,false) :=
    .cons (v := (some i,false)) (by intro eq; cases eq)
      (.cons (v := (none,true)) (by intro eq; cases eq)
      (.cons (v := (some i,true)) (by intro eq; cases eq)
      (.cons (by intro eq; cases eq) .nil)))
  have cyc (i : α) : (w i).IsCycle := by
    rw [Walk.isCycle_def, Walk.isTrail_def]
    refine ⟨?_, (by intro eq; cases eq), ?_⟩
    · change ([s(((none : Option α),false),(some i,false)),s((some i,false),(none,true)),
          s((none,true),(some i,true)),s((some i,true),(none,false))] : List (Sym2 (Option α × Bool))).Nodup
      simp
    · change ([(some i,false), (none,true),(some i,true),(none,false)] : List (Option α × Bool)).Nodup
      simp
  let sq (i : α) : Cycle G' := ⟨_,w i,cyc i⟩
  have edges (i : α) : (sq i).edges =
      [s((none,false),(some i,false)),s((some i,false),(none,true)),
       s((none,true),(some i,true)),s((some i,true),(none,false))] := rfl
  have out (i : α) (b d : Bool) (j : α) :
      s((none,b),(some j,d)) ∈ (sq i).edges ↔ i=j := by
    cases b <;> cases d <;> simp [edges,eq_comm]
  have inside (i : α) (x y : α × Bool) : s(inc x,inc y) ∉ (sq i).edges := by
    simp [edges,inc]
  let D := C.map up + (Finset.univ : Finset α).val.map sq
  refine ⟨D, ?_, ?_⟩
  · intro e
    induction e using Sym2.ind with
    | h x y =>
      intro he
      have adj : x.1 ≠ y.1 := (SimpleGraph.mem_edgeFinset.mp he)
      change (Multiset.filter _ (C.map up + Finset.univ.val.map sq)).card = 1
      rw [Multiset.filter_add, Multiset.card_add, Multiset.filter_map, Multiset.filter_map,
        Multiset.card_map, Multiset.card_map]
      obtain ⟨ox,b⟩ := x
      obtain ⟨oy,d⟩ := y
      cases ox with
      | none =>
        cases oy with
        | none => exact False.elim (adj rfl)
        | some j => simp [fresh, out, Multiset.filter_eq']
      | some i =>
        cases oy with
        | none => rw [Sym2.eq_swap]; simp [fresh, out, Multiset.filter_eq']
        | some j =>
          change (Multiset.filter (fun c => s(inc (i,b),inc (j,d)) ∈ (up c).edges) C).card +
            (Multiset.filter (fun t => s(inc (i,b),inc (j,d)) ∈ (sq t).edges) Finset.univ.val).card = 1
          simpa [old,inside] using hc s((i,b),(j,d)) (G.mem_edgeFinset.mpr (by exact fun h => adj (congrArg some h)))
  · have len (c : Cycle G) : (up c).length=c.length := Walk.length_map _ _
    simp [D,lengths,Multiset.map_map,len,show ∀ i, (sq i).length=4 from fun i => rfl] <;> rfl

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem iso_decomposition [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [DecidableRel G.Adj] [DecidableRel H.Adj] (f : G ≃g H)
    {m : Multiset ℕ} {C : Multiset (Cycle G)}
    (hc : IsCycleDecomposition G C) (hl : lengths C = m) :
    ∃ D : Multiset (Cycle H), IsCycleDecomposition H D ∧ lengths D = m := by
  classical
  let move (c : Cycle G) : Cycle H :=
    ⟨f c.base, c.walk.map f.toHom, c.isCycle.map f.injective⟩
  have mem (c : Cycle G) (a b : V) :
      s(f a, f b) ∈ (move c).edges ↔ s(a, b) ∈ c.edges := by
    change s(f a, f b) ∈ (c.walk.map f.toHom).edges ↔ _
    rw [Walk.edges_map]
    change Sym2.map f s(a, b) ∈ List.map (Sym2.map f) c.edges ↔ s(a, b) ∈ c.edges
    exact List.mem_map_of_injective (Sym2.map.injective f.injective)
  refine ⟨C.map move, ?_, ?_⟩
  · intro e
    induction e using Sym2.ind with
    | h x y =>
      obtain ⟨a, rfl⟩ := f.surjective x
      obtain ⟨b, rfl⟩ := f.surjective y
      intro he
      have hxy : H.Adj (f a) (f b) := H.mem_edgeFinset.mp he
      have hab : s(a, b) ∈ G.edgeFinset := G.mem_edgeFinset.mpr (f.map_rel_iff.mp hxy)
      rw [Multiset.filter_map, Multiset.card_map]
      simpa [Function.comp_def, mem] using hc s(a, b) hab
  · have len (c : Cycle G) : (move c).length = c.length := Walk.length_map _ _
    simpa [lengths, Multiset.map_map, Function.comp_def, len] using hl

open Finset

theorem matching_iso {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (regular : ∀ v, G.degree v = 1)
    {k : ℕ} (hk : G.edgeFinset.card = k) :
    ∃ M : SimpleGraph (Fin k × Bool),
      (∀ x y, M.Adj x y ↔ x.1 = y.1 ∧ x.2 ≠ y.2) ∧ Nonempty (M ≃g G) := by
  let number : Fin k ≃ G.edgeFinset := (Finset.equivFinOfCardEq hk).symm
  let endpt (e : G.edgeFinset) : Bool ≃ e.val.toFinset :=
    finTwoEquiv.symm.trans (Finset.equivFinOfCardEq (G.card_toFinset_mem_edgeFinset e)).symm
  let f (p : Fin k × Bool) : V := (endpt (number p.1) p.2).val
  have incident (p : Fin k × Bool) : (number p.1).val ∈ G.incidenceFinset (f p) :=
    (G.mem_incidenceFinset _ _).mpr ⟨G.mem_edgeFinset.mp (number p.1).property,
      Sym2.mem_toFinset.mp (endpt (number p.1) p.2).property⟩
  have unique (x : V) : ∀ e ∈ G.incidenceFinset x, ∀ d ∈ G.incidenceFinset x, e = d := by
    apply card_le_one.mp
    rw [card_incidenceFinset_eq_degree,regular]
  have inj : Function.Injective f := by
    rintro ⟨i,a⟩ ⟨j,b⟩ eq
    have ie := incident (i,a)
    rw [eq] at ie
    have same : (number i).val = (number j).val := unique _ _ ie _ (incident (j,b))
    have ij := number.injective (Subtype.ext same)
    subst j
    have ab := (endpt (number i)).injective (Subtype.ext eq)
    exact congrArg (Prod.mk i) ab
  have surj : Function.Surjective f := by
    intro x
    obtain ⟨e,he⟩ := card_pos.mp (by rw [card_incidenceFinset_eq_degree,regular]; decide :
      0 < (G.incidenceFinset x).card)
    let E : G.edgeFinset := ⟨e,G.incidenceFinset_subset x he⟩
    obtain ⟨i,hi⟩ := number.surjective E
    have hx : x ∈ (number i).val.toFinset := by
      rw [hi]
      exact Sym2.mem_toFinset.mpr ((G.mem_incidenceFinset _ _).mp he).2
    exact ⟨(i,(endpt (number i)).symm ⟨x,hx⟩),congrArg Subtype.val ((endpt (number i)).apply_symm_apply _)⟩
  let e := Equiv.ofBijective f ⟨inj,surj⟩
  refine ⟨G.comap e,?_,⟨SimpleGraph.Iso.comap e G⟩⟩
  intro p q
  change G.Adj (f p) (f q) ↔ _
  constructor
  · intro h
    have edgep : s(f p,f q) ∈ G.incidenceFinset (f p) :=
      (G.mem_incidenceFinset _ _).mpr (G.mk'_mem_incidenceSet_left_iff.mpr h)
    have edgeq : s(f p,f q) ∈ G.incidenceFinset (f q) :=
      (G.mem_incidenceFinset _ _).mpr (G.mk'_mem_incidenceSet_right_iff.mpr h)
    have index : p.1 = q.1 := number.injective (Subtype.ext
      ((unique _ _ (incident p) _ edgep).trans (unique _ _ edgeq _ (incident q))))
    exact ⟨index,fun same => h.ne (congrArg f (Prod.ext index same))⟩
  · rintro ⟨index,different⟩
    have ne : f p ≠ f q := fun same => different (congrArg Prod.snd (inj same))
    have hi := (G.mem_incidenceFinset _ _).mp (incident p)
    have hj := (G.mem_incidenceFinset _ _).mp (incident q)
    rw [← index] at hj
    exact G.adj_of_mem_incidenceSet ne hi hj


theorem mass_identity (q : ℕ) (q1 : 1 ≤ q) (m : Multiset ℕ)
    (sum : m.sum=(q+q).choose 2-(q+q)/2) : m.sum+2*q=2*q*q := by
  have cs : (q+q).choose 2 = q*(q+q-1) := by
    rw [Nat.choose_two_right, show q+q=2*q by omega]
    rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0<2)]
  rw [cs,show (q+q)/2=q by omega] at sum
  have mass : m.sum+q=q*(q+q-1) := by
    have hh : q*1 ≤ q*(q+q-1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have sub : q+q-1+1=q+q := by omega
  nlinarith [congrArg (q*·) sub]

theorem relabel {α β : Type*} (f : α ≃ β) :
    Nonempty (((completeGraph α).comap (Prod.fst (β := Bool))) ≃g ((completeGraph β).comap (Prod.fst (β := Bool)))) :=
  ⟨{ toEquiv := f.prodCongr (Equiv.refl Bool), map_rel_iff' := f.injective.ne_iff }⟩

/-- Decompose an admissible matched complete graph when some cycle visits all but at most one vertex. -/
def H1 : Prop := ∀ (q : ℕ) (m : Multiset ℕ),
  (∀ k ∈ m, 3 ≤ k ∧ k ≤ 2*q) → m.sum+2*q=2*q*q →
  (∃ k ∈ m, 2*q ≤ k+1) →
    ∃ C : Multiset (Cycle ((completeGraph (Fin q)).comap (Prod.fst (β := Bool)))),
      IsCycleDecomposition _ C ∧ lengths C = m

/-- Decompose a graph with shorter cycles and too few squares to remove a pair of vertices. -/
def H2 : Prop := ∀ (q : ℕ) (m : Multiset ℕ),
  (∀ k ∈ m, 3 ≤ k ∧ k+2 ≤ 2*q) → m.sum+2*q=2*q*q →
  m.count 4 < q-1 →
    ∃ C : Multiset (Cycle ((completeGraph (Fin q)).comap (Prod.fst (β := Bool)))),
      IsCycleDecomposition _ C ∧ lengths C = m

theorem descend (long : H1) (short : H2) (q : ℕ) (m : Multiset ℕ)
    (bounds : ∀ k ∈ m, 3 ≤ k ∧ k ≤ 2*q) (mass : m.sum+2*q=2*q*q) : ∃ C : Multiset (Cycle ((completeGraph (Fin q)).comap (Prod.fst (β := Bool)))),
      IsCycleDecomposition _ C ∧ lengths C = m := by
  classical
  induction q generalizing m with
  | zero =>
    have empty : m=0 := Multiset.eq_zero_iff_forall_notMem.mpr (fun k hk => by have := bounds k hk; omega)
    refine ⟨0,fun e he => ?_,by simp [lengths,empty]⟩
    induction e using Sym2.ind with
    | h x y => exact Fin.elim0 x.1
  | succ q ih =>
    by_cases near : ∃ k ∈ m, 2*(q+1) ≤ k+1
    · exact long _ _ bounds mass near
    have low (k : ℕ) (hk : k ∈ m) : 3 ≤ k ∧ k+2 ≤ 2*(q+1) :=
      ⟨(bounds k hk).1,by by_contra! h; exact near ⟨k,hk,by omega⟩⟩
    by_cases few : m.count 4 < q
    · exact short _ _ low mass (by omega)
    let r := m - Multiset.replicate q 4
    have decomp : r + Multiset.replicate q 4 = m :=
      Multiset.sub_add_cancel (Multiset.le_count_iff_replicate_le.mp (by omega))
    have sum := congrArg Multiset.sum decomp
    simp only [Multiset.sum_add,Multiset.sum_replicate,smul_eq_mul] at sum
    obtain ⟨C,hc,hl⟩ := ih r (fun k hk => by
      have : k ∈ m := decomp ▸ Multiset.mem_add.mpr (Or.inl hk)
      have := low k this
      omega) (by nlinarith)
    obtain ⟨D,hd,ld⟩ := extend C hc
    have len : lengths D=m := by simpa [Fintype.card_fin,hl,decomp] using ld
    obtain ⟨f⟩ := relabel (Fintype.equivOfCardEq (by simp) : Option (Fin q) ≃ Fin (q+1))
    exact iso_decomposition f hd len

theorem main : H1 → H2 → type_of% @AlspachConjecture.alspach_conjecture.variants.even := by
  classical
  intro hl hs n hn I hi m hm hsum
  obtain ⟨q,rfl⟩ := hn
  have reg (v : Fin (q+q)) : I.spanningCoe.degree v=1 :=
    degree_eq_one_iff_existsUnique_adj.mpr (Subgraph.isPerfectMatching_iff.mp hi v)
  have count : I.spanningCoe.edgeFinset.card=q := by
    have sum := I.spanningCoe.sum_degrees_eq_twice_card_edges
    simp only [reg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at sum
    omega
  obtain ⟨A,ha,⟨f⟩⟩ := matching_iso I.spanningCoe reg count
  let g : ((completeGraph (Fin q)).comap (Prod.fst (β := Bool))) ≃g (completeGraph (Fin (q+q)) \ I.spanningCoe) :=
    { toEquiv := f.toEquiv
      map_rel_iff' := by
        intro x y
        change (f x ≠ f y ∧ ¬ I.spanningCoe.Adj (f x) (f y)) ↔ x.1 ≠ y.1
        rw [f.injective.ne_iff, f.map_rel_iff, ha]
        constructor
        · rintro ⟨ne, other⟩ eq
          exact other ⟨eq,fun t => ne (Prod.ext eq t)⟩
        · intro h
          exact ⟨fun eq => h (congrArg Prod.fst eq), fun z => h z.1⟩ }
  have mass : m.sum+2*q=2*q*q := by
    by_cases z : q=0
    · subst q; simpa using hsum
    · exact mass_identity q (by omega) m hsum
  obtain ⟨C,hc,len⟩ := descend hl hs q m (by simpa [two_mul] using hm) mass
  exact iso_decomposition g hc len

end OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R3
