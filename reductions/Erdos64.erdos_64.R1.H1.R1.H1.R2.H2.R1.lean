import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R2

/-!
In the rooted triangle-contraction step of PR #27543, every dyadic cycle
contains the whole orbit of the required vertex. In the transitive case
any dyadic witness therefore supplies a Hamiltonian cyclic labeling. A
single commuting point in the matching coordinates of PR #5246 gives a
hexagon through six specified vertices, each solving the rooted length
condition with 6 + 2 = 8. Credit: @wispiANt.
-/
namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R2_H2_R1
open SimpleGraph

/-- The forced orbit is proper. A suitable cycle only has to meet it. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (r : V),
    G.Connected → (∀ v, G.degree v = 3) →
    (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a,b)) →
    (∃ v, ∀ f : G ≃g G, f r ≠ v) →
    (∀ n, n = 3 ∨ n = 6 → ∀ c : (cycleGraph n).Copy G, ∀ f : G ≃g G, f r ∉ Set.range c) →
    (∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G) →
    (∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G, ∀ f : G ≃g G, f r ∈ Set.range c) →
    ∃ (n k : ℕ) (c : (cycleGraph n).Copy G) (f : G ≃g G),
      3 ≤ n ∧ 2 ≤ k ∧ f r ∈ Set.range c ∧ (n+1=2^k ∨ n+2=2^k)

/-- In cyclic labels the dyadic Hamiltonian cycle is already present.
The transitive residual has an automorphic image of the ring using a chord. -/
def H2 : Prop :=
  ∀ (t : ℕ), 6 ≤ t → ∀ (D : SimpleGraph (Fin (2^t))) [DecidableRel D.Adj],
    (∀ i, D.degree i = 3) → ∀ mate : Fin (2^t) → Fin (2^t),
    Function.Involutive mate → (∀ i, mate i ≠ i ∧ ¬ (cycleGraph (2^t)).Adj i (mate i)) →
    (∀ i j, D.Adj i j ↔ (cycleGraph (2^t)).Adj i j ∨ j = mate i) →
    (∀ i j, ∃ f : D ≃g D, f i = j) →
    (∃ (f : D ≃g D) (i j : Fin (2^t)), (cycleGraph (2^t)).Adj i j ∧
      ¬ (cycleGraph (2^t)).Adj (f i) (f j)) →
    (¬ cycleGraph 3 ⊑ D) → (¬ cycleGraph 6 ⊑ D) →
    (∀ j : ℕ, 2 ≤ j → j < t → ¬ cycleGraph (2^j) ⊑ D) →
    ∃ n k : ℕ, 3 ≤ n ∧ 2 ≤ k ∧ cycleGraph n ⊑ D ∧ (n+1=2^k ∨ n+2=2^k)

/-- A cyclic list gives a copy whose vertex set includes every entry.
The cyclic-index argument is adapted from PR #27543. -/
theorem rootedRing {V : Type*} (G : SimpleGraph V) (l : List V)
    (large : 3 ≤ l.length) (distinct : l.Nodup) (path : l.IsChain G.Adj)
    (close : ∀ h : l ≠ [], G.Adj (l.getLast h) (l.head h)) :
    ∃ c : (cycleGraph l.length).Copy G, ∀ v ∈ l, v ∈ Set.range c := by
  let : NeZero l.length := ⟨by omega⟩
  have pos : 1 < l.length := by omega
  have next (i : Fin l.length) : G.Adj (l.get i) (l.get (i+1)) := by
    have val : (i+1 : Fin l.length).val = (i.val+1) % l.length := by
      rw [Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt pos]
    by_cases inside : i.val+1 < l.length
    · have eq : (i+1 : Fin l.length).val = i.val+1 := val.trans (Nat.mod_eq_of_lt inside)
      simpa only [List.get_eq_getElem,eq] using path.getElem i.val inside
    · have last : i.val=l.length-1 := by omega
      have start : (i+1 : Fin l.length).val = 0 := by rw [val,show i.val+1=l.length by omega,Nat.mod_self]
      have h := close (List.length_pos_iff.mp (by omega))
      simpa only [List.get_eq_getElem,last,start,List.head_eq_getElem,List.getLast_eq_getElem] using h
  have adj {i j : Fin l.length} (h : (cycleGraph l.length).Adj i j) : G.Adj (l.get i) (l.get j) := by
    have diff : i-j=1 ∨ j-i=1 := by
      simpa only [Fin.ext_iff,Fin.val_one',Nat.mod_eq_of_lt pos] using cycleGraph_adj'.mp h
    rcases diff with e | e
    · have eq : i=j+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp e
      simpa only [eq] using (next j).symm
    · have eq : j=i+1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp e
      simpa only [eq] using next i
  refine ⟨⟨⟨l.get,fun h => adj h⟩,distinct.injective_get⟩,?_⟩
  intro v hv
  exact List.mem_iff_get.mp hv

/-- One commuting point, along with the three disjoint matchings at the
indicated vertices, suffices. The conclusion specifies all six possible roots. -/
theorem commutingHexagon {X : Type*} (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idEdge : ∀ x, G.Adj (false,x) (true,x))
    (pEdge : ∀ x, G.Adj (false,x) (true,p x))
    (qEdge : ∀ x, G.Adj (false,x) (true,q x))
    (x : X) (comm : p (q x) = q (p x)) :
    ∃ c : (cycleGraph 6).Copy G, ∀ v ∈ ([(false,x),(true,p x),(false,p x),
      (true,q (p x)),(false,q x),(true,q x)] : List (Bool × X)), v ∈ Set.range c := by
  let l : List (Bool × X) := [(false,x),(true,p x),(false,p x),(true,q (p x)),(false,q x),(true,q x)]
  have x₁ := (sep x).1
  have x₂ := (sep x).2.1
  have x₃ := (sep x).2.2
  have r₁ := (sep (p x)).2.1
  have r₂ : q (p x) ≠ q x := fun e => x₁ (q.injective e)
  have lastEdge : G.Adj (true,q (p x)) (false,q x) := comm ▸ (pEdge (q x)).symm
  exact rootedRing G l (by exact (by decide : 3 ≤ 6))
    (by simp [l,x₁.symm,x₂.symm,x₃,r₁.symm,r₂])
    (by simp [l,pEdge,idEdge,qEdge,(idEdge _).symm,lastEdge]) (by simpa [l] using (qEdge x).symm)

/-- In the globally commuting case every vertex is on a hexagon. -/
theorem everyRootOfCommuting {X : Type*} (G : SimpleGraph (Bool × X)) (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idEdge : ∀ x, G.Adj (false,x) (true,x)) (pEdge : ∀ x, G.Adj (false,x) (true,p x))
    (qEdge : ∀ x, G.Adj (false,x) (true,q x)) (comm : ∀ x, p (q x) = q (p x))
    (r : Bool × X) : ∃ c : (cycleGraph 6).Copy G, r ∈ Set.range c := by
  obtain ⟨b,y⟩ := r
  cases b with
  | false =>
    obtain ⟨c,h⟩ := commutingHexagon G p q sep idEdge pEdge qEdge y (comm y)
    exact ⟨c,h _ (by simp)⟩
  | true =>
    obtain ⟨c,h⟩ := commutingHexagon G p q sep idEdge pEdge qEdge (p.symm y) (comm _)
    exact ⟨c,h _ (by simp)⟩

/-- At most two vertices per defective permutation coordinate lack a rooted
hexagon. Charge a left vertex to itself and a right vertex to its p-preimage. -/
theorem uncoveredBound {X : Type} [Fintype X] [DecidableEq X] (G : SimpleGraph (Bool × X))
    (p q : Equiv.Perm X) (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idEdge : ∀ x, G.Adj (false,x) (true,x)) (pEdge : ∀ x, G.Adj (false,x) (true,p x))
    (qEdge : ∀ x, G.Adj (false,x) (true,q x)) :
    {r : Bool × X | ¬ ∃ c : (cycleGraph 6).Copy G, r ∈ Set.range c}.ncard ≤
      2 * {x : X | p (q x) ≠ q (p x)}.ncard := by
  classical
  let bad := {r : Bool × X | ¬ ∃ c : (cycleGraph 6).Copy G, r ∈ Set.range c}
  let defect := {x : X | p (q x) ≠ q (p x)}
  let f : Bool × X → Bool × X := fun r => (r.1,if r.1 then p.symm r.2 else r.2)
  have maps (r : Bool × X) (h : r ∈ bad) : f r ∈ (Set.univ : Set Bool) ×ˢ defect := by
    refine ⟨Set.mem_univ _,?_⟩
    obtain ⟨b,y⟩ := r
    cases b with
    | false =>
      change p (q y) ≠ q (p y)
      intro eq
      obtain ⟨c,roots⟩ := commutingHexagon G p q sep idEdge pEdge qEdge y eq
      exact h ⟨c,roots _ (by simp)⟩
    | true =>
      change p (q (p.symm y)) ≠ q (p (p.symm y))
      intro eq
      obtain ⟨c,roots⟩ := commutingHexagon G p q sep idEdge pEdge qEdge _ eq
      exact h ⟨c,roots _ (by simp)⟩
  have inj : Function.Injective f := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    cases i <;> cases j <;> simp_all [f]
  have bound := Set.ncard_le_ncard_of_injOn f maps inj.injOn
  simpa [bad,defect,Set.ncard_prod] using bound

private theorem backToRoot {V : Type} {G : SimpleGraph V} {r : V} {n : ℕ}
    (c : (cycleGraph n).Copy G) (f : G ≃g G) (hit : f r ∈ Set.range c) :
    ∃ d : (cycleGraph n).Copy G, r ∈ Set.range d := by
  obtain ⟨i,hi⟩ := hit
  exact ⟨f.symm.toCopy.comp c,i,by change f.symm (c i) = r; rw [hi]; exact f.symm_apply_apply r⟩

theorem forcedOrbit {V : Type} {G : SimpleGraph V} {r : V} {n : ℕ}
    (forced : ∀ c : (cycleGraph n).Copy G, r ∈ Set.range c) (c : (cycleGraph n).Copy G)
    (f : G ≃g G) : f r ∈ Set.range c := by
  obtain ⟨i,hi⟩ := forced (f.symm.toCopy.comp c)
  exact ⟨i,(f.symm_apply_eq.mp hi)⟩

theorem forcedOrbitBound {V : Type} [Fintype V] {G : SimpleGraph V} {r : V} {n : ℕ}
    (forced : ∀ c : (cycleGraph n).Copy G, r ∈ Set.range c) (c : (cycleGraph n).Copy G) :
    {v | ∃ f : G ≃g G, f r = v}.ncard ≤ n := by
  have sub : {v | ∃ f : G ≃g G, f r = v} ⊆ Set.range c := by
    rintro _ ⟨f,rfl⟩
    exact forcedOrbit forced c f
  have card : (Set.range (fun i : Fin n => c i)).ncard = Nat.card (Fin n) :=
    Set.ncard_range_of_injective (f := fun i : Fin n => c i) c.injective
  exact (Set.ncard_le_ncard sub).trans_eq (card.trans (Nat.card_fin n))

/-- The edges outside a spanning ring in a cubic graph give a perfect matching. -/
theorem chordMatching {n : ℕ} (large : 3 ≤ n) (D : SimpleGraph (Fin n)) [DecidableRel D.Adj]
    (ring : cycleGraph n ≤ D) (deg : ∀ i, D.degree i = 3) :
    ∃ mate : Fin n → Fin n, Function.Involutive mate ∧
      (∀ i, mate i ≠ i ∧ ¬ (cycleGraph n).Adj i (mate i)) ∧
      ∀ i j, D.Adj i j ↔ (cycleGraph n).Adj i j ∨ j = mate i := by
  classical
  have rd (i : Fin n) : (cycleGraph n).degree i = 2 := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le' large
    exact cycleGraph_degree_three_le
  have unique (i : Fin n) : ∃ j, ∀ u, (D.Adj i u ∧ ¬ (cycleGraph n).Adj i u) ↔ u = j := by
    have sub : (cycleGraph n).neighborFinset i ⊆ D.neighborFinset i := by
      intro j h
      exact (D.mem_neighborFinset ..).2 (ring (((cycleGraph n).mem_neighborFinset ..).1 h))
    have card : ((D.neighborFinset i) \ ((cycleGraph n).neighborFinset i)).card = 1 := by
      rw [Finset.card_sdiff_of_subset sub,card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,deg,rd]
    obtain ⟨j,hj⟩ := Finset.card_eq_one.mp card
    exact ⟨j,fun u => by simpa using Finset.ext_iff.mp hj u⟩
  choose mate spec using unique
  have chord (i) := (spec i (mate i)).2 rfl
  refine ⟨mate,fun i => (Eq.symm ((spec _ _).1 ⟨(chord i).1.symm,fun h => (chord i).2 h.symm⟩)),?_,?_⟩
  · exact fun i => ⟨(chord i).1.ne.symm,(chord i).2⟩
  · intro i j
    constructor
    · intro h
      by_cases e : (cycleGraph n).Adj i j
      · exact Or.inl e
      · exact Or.inr ((spec i j).1 ⟨h,e⟩)
    · rintro (h | rfl)
      · exact ring h
      · exact (chord i).1

/-- Check one row of a matching search. Each possible chord partner either
remains for a later row or has an explicit cycle using the known chords. -/
private theorem certificateRow {n : ℕ} (D : SimpleGraph (Fin n)) (mate : Fin n → Fin n)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph n).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph n).Adj i j ∨ j = mate i)
    (a : Fin n) (known : List (Fin n × Fin n)) (pending : List (Fin n))
    (routes : List (List (Fin n))) (fixed : ∀ e ∈ known, mate e.1 = e.2)
    (fresh : ∀ e ∈ known, a ≠ e.1 ∧ a ≠ e.2)
    (cert : ∀ j : Fin n, j ∉ pending → j ≠ a → ¬ (cycleGraph n).Adj a j →
      (∀ e ∈ known, j ≠ e.1 ∧ j ≠ e.2) →
      let l := routes.getD j.val []
      (l.length = 3 ∨ l.length = 6 ∨ l.length = 7 ∨ (l.length = 4 ∧ 4 < n) ∨ (l.length = 8 ∧ 8 < n)) ∧
      l.Nodup ∧ ∀ i k : Fin l.length, (cycleGraph l.length).Adj i k →
        (cycleGraph n).Adj (l.get i) (l.get k) ∨
        (l.get i,l.get k) ∈ (a,j)::known ∨ (l.get k,l.get i) ∈ (a,j)::known) :
    (∃ m, (m = 3 ∨ m = 6 ∨ m = 7 ∨ (m = 4 ∧ 4 < n) ∨ (m = 8 ∧ 8 < n)) ∧ cycleGraph m ⊑ D) ∨
      mate a ∈ pending := by
  by_cases wait : mate a ∈ pending
  · exact Or.inr wait
  have free (e) (he : e ∈ known) : mate a ≠ e.1 ∧ mate a ≠ e.2 := by
    have fix := fixed e he
    have h := fresh e he
    refine ⟨fun eq => h.2 ((inv a).symm.trans ((congrArg mate eq).trans fix)),
      fun eq => h.1 (inv.injective (eq.trans fix.symm))⟩
  let l := routes.getD (mate a).val []
  obtain ⟨size,unique,links⟩ := cert (mate a) wait (chord a).1 (chord a).2 free
  have marked (i j : Fin n) (h : (i,j) ∈ (a,mate a)::known) : D.Adj i j := by
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact (edges _ _).2 (Or.inr rfl)
    · exact (edges _ _).2 (Or.inr (fixed _ h).symm)
  refine Or.inl ⟨l.length,size,⟨⟨⟨l.get,?_⟩,unique.injective_get⟩⟩⟩
  intro i j adj
  exact (links i j adj).elim (fun h => (edges _ _).2 (Or.inl h))
    (fun h => h.elim (marked _ _) (fun rev => (marked _ _ rev).symm))

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private theorem small4 (D : SimpleGraph (Fin 4)) (mate : Fin 4 → Fin 4)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 4).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 4).Adj i j ∨ j = mate i) :
    ∃ m, (m = 3 ∨ m = 6 ∨ m = 7 ∨ (m = 4 ∧ 4 < 4) ∨ (m = 8 ∧ 8 < 4)) ∧ cycleGraph m ⊑ D := by
  obtain done | next := certificateRow D mate inv chord edges 0 [] []
    [[],[],[0,1,2],[]] (by simp) (by decide) (by decide)
  · exact done
  · simp at next

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private theorem small8 (D : SimpleGraph (Fin 8)) (mate : Fin 8 → Fin 8)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 8).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 8).Adj i j ∨ j = mate i) :
    ∃ m, (m = 3 ∨ m = 6 ∨ m = 7 ∨ (m = 4 ∧ 4 < 8) ∨ (m = 8 ∧ 8 < 8)) ∧ cycleGraph m ⊑ D := by
  obtain done | next := certificateRow D mate inv chord edges 0 [] [4]
    [[],[],[0,1,2],[0,1,2,3],
      [],[0,5,6,7],[0,6,7],[]] (by simp) (by decide) (by decide)
  · exact done
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at next
    have h0 := next
    obtain done | next := certificateRow D mate inv chord edges 1 [(0,4)] []
      [[],[],[],[1,2,3],
        [],[0,1,5,4],[0,1,6,7],[0,1,7]] (by simp_all) (by decide) (by decide)
    · exact done
    · simp at next

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private theorem small16 (D : SimpleGraph (Fin 16)) (mate : Fin 16 → Fin 16)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 16).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 16).Adj i j ∨ j = mate i) :
    ∃ m, (m = 3 ∨ m = 6 ∨ m = 7 ∨ (m = 4 ∧ 4 < 16) ∨ (m = 8 ∧ 8 < 16)) ∧ cycleGraph m ⊑ D := by
  obtain done | next := certificateRow D mate inv chord edges 0 [] [4, 8, 12]
    [[],[],[0,1,2],[0,1,2,3],
      [],[0,1,2,3,4,5],[0,1,2,3,4,5,6],[0,1,2,3,4,5,6,7],
      [],[0,9,10,11,12,13,14,15],[0,10,11,12,13,14,15],[0,11,12,13,14,15],
      [],[0,13,14,15],[0,14,15],[]] (by simp) (by decide) (by decide)
  · exact done
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at next
    rcases next with h0 | h0 | h0
    · obtain done | next := certificateRow D mate inv chord edges 1 [(0,4)] []
        [[],[],[],[1,2,3],
          [],[0,1,5,4],[1,2,3,4,5,6],[0,1,7,6,5,4],
          [0,1,8,7,6,5,4],[0,1,9,8,7,6,5,4],[0,1,10,11,12,13,14,15],[0,1,11,12,13,14,15],
          [0,1,12,13,14,15],[0,4,3,2,1,13,14,15],[0,1,14,15],[0,1,15]] (by simp_all) (by decide) (by decide)
      · exact done
      · simp at next
    · obtain done | next := certificateRow D mate inv chord edges 1 [(0,8)] []
        [[],[],[],[1,2,3],
          [1,2,3,4],[0,1,5,6,7,8],[1,2,3,4,5,6],[0,1,7,8],
          [],[0,1,9,8],[0,1,10,11,12,13,14,15],[0,1,11,10,9,8],
          [0,1,12,13,14,15],[0,1,13,12,11,10,9,8],[0,1,14,15],[0,1,15]] (by simp_all) (by decide) (by decide)
      · exact done
      · simp at next
    · obtain done | next := certificateRow D mate inv chord edges 1 [(0,12)] [5]
        [[],[],[],[1,2,3],
          [1,2,3,4],[],[1,2,3,4,5,6],[1,2,3,4,5,6,7],
          [0,1,8,9,10,11,12],[0,1,9,10,11,12],[0,1,10,11,12,13,14,15],[0,1,11,12],
          [],[0,1,13,12],[0,1,14,15],[0,1,15]] (by simp_all) (by decide) (by decide)
      · exact done
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at next
        have h1 := next
        obtain done | next := certificateRow D mate inv chord edges 2 [(0,12),(1,5)] []
          [[],[],[],[],
            [2,3,4],[],[1,2,6,5],[2,3,4,5,6,7],
            [1,2,8,7,6,5],[0,1,2,9,10,11,12],[0,1,2,10,11,12],[0,1,2,11,12,13,14,15],
            [],[0,1,2,13,14,15],[0,1,2,14,13,12],[0,1,2,15]] (by simp_all) (by decide) (by decide)
        · exact done
        · simp at next

/-- Every cubic Hamiltonian chord diagram at orders 4, 8 and 16 has a
triangle, a hexagon, a heptagon, or a strictly shorter dyadic cycle. -/
theorem smallRingResult {t : ℕ} (ht : 2 ≤ t) (upper : t ≤ 4)
    (D : SimpleGraph (Fin (2^t))) [DecidableRel D.Adj]
    (ring : cycleGraph (2^t) ≤ D) (cubic : ∀ i, D.degree i = 3) :
    ∃ m, (m = 3 ∨ m = 6 ∨ m = 7 ∨ (m = 4 ∧ 4 < 2^t) ∨ (m = 8 ∧ 8 < 2^t)) ∧ cycleGraph m ⊑ D := by
  have large : 3 ≤ 2^t := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) ht
    omega
  obtain ⟨mate,inv,chord,edges⟩ := chordMatching large D ring cubic
  rcases (show t = 2 ∨ t = 3 ∨ t = 4 by omega) with rfl | rfl | rfl
  exacts [small4 D mate inv chord edges,small8 D mate inv chord edges,small16 D mate inv chord edges]

/-- At a search node the possible new partners are split into explicit cycle
witnesses and recursively excluded extensions of the partial matching.
The low five bits encode the first vertex, the next five encode the second,
and a final leading one records the length. -/
private theorem row32 (D : SimpleGraph (Fin 32)) (mate : Fin 32 → Fin 32)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 32).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 32).Adj i j ∨ j = mate i)
    (noCycle : ¬ ∃ m ∈ [3,4,6,7,8,14,15,16], cycleGraph m ⊑ D)
    (a : Fin 32) (known : List (Fin 32 × Fin 32)) (pending : List (Fin 32))
    (routes : Array Nat)
    (fresh : ∀ e ∈ known, a ≠ e.1 ∧ a ≠ e.2)
    (cert : ∀ j : Fin 32, j ∉ pending → j ≠ a → ¬ (cycleGraph 32).Adj a j →
      (∀ e ∈ known, j ≠ e.1 ∧ j ≠ e.2) →
      let l := (List.range (((routes[j.val]?).getD 1).log2 / 5)).map fun i =>
        Fin.ofNat 32 (((routes[j.val]?).getD 1) >>> (5*i))
      let link := fun x y => (cycleGraph 32).Adj x y ∨ (x,y) ∈ (a,j)::known ∨ (y,x) ∈ (a,j)::known
      l.length ∈ [3,4,6,7,8,14,15,16] ∧ l.Nodup ∧ l.IsChain link ∧
        link (l.getLastD 0) (l.headD 0))
    (children : ∀ b ∈ pending, ¬ (∀ e ∈ (a,b)::known, mate e.1 = e.2)) :
    ¬ (∀ e ∈ known, mate e.1 = e.2) := by
  intro fixed
  by_cases wait : mate a ∈ pending
  · apply children (mate a) wait
    exact List.forall_mem_cons.mpr ⟨rfl,fixed⟩
  have free (e) (he : e ∈ known) : mate a ≠ e.1 ∧ mate a ≠ e.2 := by
    have fix := fixed e he
    have h := fresh e he
    exact ⟨fun eq => h.2 ((inv a).symm.trans ((congrArg mate eq).trans fix)),
      fun eq => h.1 (inv.injective (eq.trans fix.symm))⟩
  obtain ⟨size,distinct,chain,close⟩ := cert (mate a) wait (chord a).1 (chord a).2 free
  let l := (List.range (((routes[(mate a).val]?).getD 1).log2 / 5)).map fun i =>
        Fin.ofNat 32 (((routes[(mate a).val]?).getD 1) >>> (5*i))
  have marked (i j : Fin 32) (h : (i,j) ∈ (a,mate a)::known) : D.Adj i j := by
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact (edges _ _).2 (Or.inr rfl)
    · exact (edges _ _).2 (Or.inr (fixed _ h).symm)
  have link (i j : Fin 32) (h : (cycleGraph 32).Adj i j ∨ (i,j) ∈ (a,mate a)::known ∨
      (j,i) ∈ (a,mate a)::known) : D.Adj i j :=
    h.elim (fun adj => (edges _ _).2 (Or.inl adj))
      (fun e => e.elim (marked _ _) (fun rev => (marked _ _ rev).symm))
  change l.length ∈ _ at size
  have large : 3 ≤ l.length := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at size
    omega
  obtain ⟨d,_⟩ := rootedRing D l large distinct (chain.imp link) (by
    intro h
    have hc : D.Adj (l.getLastD 0) (l.headD 0) := link _ _ close
    simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h,
      List.headD_eq_head?_getD, List.head?_eq_some_head h, Option.getD_some] using hc)
  exact noCycle ⟨_,size,⟨d⟩⟩

private theorem partnerCons {α : Type} {P : α → Prop} {b : α} {bs : List α}
    (first : P b) (rest : ∀ x ∈ bs, P x) : ∀ x ∈ b::bs, P x :=
  List.forall_mem_cons.mpr ⟨first,rest⟩

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem partner4 (D : SimpleGraph (Fin 32)) (mate : Fin 32 → Fin 32)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 32).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 32).Adj i j ∨ j = mate i)
    (noCycle : ¬ ∃ m ∈ [3,4,6,7,8,14,15,16], cycleGraph m ⊑ D) :
    ¬ (∀ e ∈ ([(0,4)] : List (Fin 32 × Fin 32)), mate e.1 = e.2) := by
  have r0 := row32 D mate inv chord edges noCycle 31 [(30,22),(1,10),(0,4)] []
    #[1,1,1082338,2064515,1,39865877535,1240239996101,1213407200,1351943199,2065615188144871076866046,1,1600739731316115430367,1636366325489689756703,49926371972898643490187,1636641510217099435293100,1334154526637990297568,2299600830650928336502749,71862525957841510531037,2359954738187457974898,1732959199,1941035130836118471711,2095829,1,2064118,2126942888958,68683722585,2042462173,2056006654943,2062239,64447,1,1] (by decide) (by decide +kernel) (by simp)
  have r1 := row32 D mate inv chord edges noCycle 31 [(30,26),(1,10),(0,4)] []
    #[1,1,1082338,2064515,1,39865877535,1240239996101,1213407200,1351943199,1242528229344,1,1488241922079,1636366325489689756703,49926371972898643490187,1636641510217099435293100,2169536734845940023294,2299600830650928336502749,71862525957841510531037,2359954738187457974898,1948622366891842172194847,1941035130836118471711,50004996180729978878977,63141829630,1973182462,2126942888958,68683722585,1,1929214,2062239,64447,1,1] (by decide) (by decide +kernel) (by simp)
  have r2 := row32 D mate inv chord edges noCycle 30 [(1,10),(0,4)] [22,26]
    #[1,1,2112884834,1107233857,1,1204772927652,1107237028,35431618724,35466977578,2112881993,1,1598282724821386167294,48707696751512962150762,1597643903132756592244107,1334154526637990312928,2260603223566585459899324,70643850736455795637180,2321871137519154384465,1909624759807490774926334,1562656130647812176897,50004996180729979173889,2026617581060528199992318,1,2091474771933,67575343928,2007825340,1,2028414,63390,1,1,1] (by decide) (by decide +kernel) (partnerCons r0 (partnerCons r1 (by simp)))
  have r3 := row32 D mate inv chord edges noCycle 21 [(22,18),(30,26),(1,11),(0,4)] []
    #[1,1,1255567509822931492565,38958294980427208363073,1,1405171842361644940839637,1909624759807499570468499,59675773743984361592467,1979118731504422070568,2029133555711130931866953,38996378581095511971147,1,63410423615972841620844,1736793601718,1772261718708,57599936015,1696093843,1624789,1,53877,1,1,1,55991,1825464,1739081966326,1,64250207957,2020538537883,2020538537918,1,2171993740948231905049] (by decide) (by decide +kernel) (by simp)
  have r4 := row32 D mate inv chord edges noCycle 22 [(30,26),(1,11),(0,4)] [18]
    #[1,1,2321871137519133888543,1293615081694216119030,1,1285701130058681848370307,1217446718138350246052,1948622366891842447071924,60894448965370076486324,2017202332172725661001,1218636830659234748747,1,1218636830659234748811,64629098837358522969485,2068131162795472735023534,1807729835733,58708314672,1730730676,1,1757814,54934,1,1,1,57048,1859289,1,1903914841,65358586614,2056006654908,1,63141829630] (by decide) (by decide +kernel) (partnerCons r3 (by simp))
  have r5 := row32 D mate inv chord edges noCycle 30 [(1,11),(0,4)] [26]
    #[1,1,2112884834,1107233857,1,1204772927652,1107237028,35431618724,1242528250848,67612224841,1108343115,1,48707696751512962150762,1597643903132756592244107,1594920829950,2260603223566585459899324,70643850736455795637180,2321871137519154384465,59675773743974457672702,1948622366891832543151102,1941035130836118176766,63331799408141505954814,2065615188144871076561918,2091474771933,67575343928,2007825340,1,2028414,63390,1,1,1] (by decide) (by decide +kernel) (partnerCons r4 (by simp))
  have r6 := row32 D mate inv chord edges noCycle 3 [(30,26),(1,12),(0,4)] []
    #[1,1,1,1,1,36965,1216614,1100655859876,1245815014,44299392131,1382112431433,1208004963,1,1486488928918767277255,1109506476,1444169449445987364929669,1788700728162904118403,54801072858441502017039,1792631938554470940658224,1951138341542445213253763,1246665439373670668176449,38958294980427208363073,1293615081694216119030,65769149850912936035395,1678155091952045077040193,2163590893370,1,2163590893434,1134943989858,37649154013,1,2064515] (by decide) (by decide +kernel) (by simp)
  have r7 := row32 D mate inv chord edges noCycle 30 [(1,12),(0,4)] [26]
    #[1,1,2112884834,1107233857,1,1204772927652,1107237028,35431618724,1242528250848,2163591228745,47625239553,1598282724821386167294,1,1597643903132756592244107,35466983852,2260603223566585459899324,70643850736455795637180,2321871137519154384465,1864867929488499016702,60894448965359064187902,1987619973976174311375870,1979118731504421733374,64550474629527220814846,2091474771933,67575343928,2007825340,1,2028414,63390,1,1,1] (by decide) (by decide +kernel) (partnerCons r6 (by simp))
  have r8 := row32 D mate inv chord edges noCycle 2 [(1,13),(0,4)] []
    #[1,1,1,1,1,1182789,1074862244,1211178181,43191013474,1346644314408,1522903105,1240250856480,1486913,1,1410321727974583337093,1750617127494600527970,53582397637055787123182,1753634331470128064054799,1561741281345,2416593651903956966279200,75518551621998655178784,1255567509822931492565,2321871137519133888543,1363684443102158756721696,2093369533509332841506,68206500293684365833250,2221605616482242583278626,1133835611201,36541823932,2146338848,2112884834,1082338] (by decide) (by decide +kernel) (by simp)
  have r9 := row32 D mate inv chord edges noCycle 5 [(2,18),(3,11),(1,24),(0,4)] []
    #[1,1,1,1,1,1,1,39079,1284264,1245818185,1315088680,1,1453048665483,1178776971,37720896907,1736793296994,39865895472,1245809233,1,57238423301212931804753,1870627152723156693865074,1171592499826,1285701130058681848370307,40178160314333807744131,1,35503871800,2020514794629,1444169449116771575329637,35432362148,1107260580,1204772927652,39865877535] (by decide) (by decide +kernel) (by simp)
  have r10 := row32 D mate inv chord edges noCycle 5 [(2,26),(3,11),(1,24),(0,4)] []
    #[1,1,1,1,1,1,1,39079,1284264,1245818185,1315088680,1,1453048665483,1178776971,37720896907,1490805036163,69425175515070080389218,2169536734845939650658,1864867929499511299269,57238423301212931804753,1870627152723156693865074,1600739731316115412099,1285701130058681848370307,40178160314333807744131,1,35503871800,1,1144133498,35432362148,1107260580,1204772927652,39865877535] (by decide) (by decide +kernel) (by simp)
  have r11 := row32 D mate inv chord edges noCycle 2 [(3,11),(1,24),(0,4)] [18,26]
    #[1,1,1,1,1,1182789,1313464462434,1211178181,43191013474,1346644314408,1387618,1,1453154,1676906932652722610210,1410321727974583337093,1750617127494600527970,53582397637055787123182,1753634331470128064054799,1,2416593651903956966279200,75518551621998655178784,1255567509822931492565,2321871137519133888543,1115927,1,1084216,1,1133835611201,36541823932,2146338848,2112884834,1082338] (by decide) (by decide +kernel) (partnerCons r9 (partnerCons r10 (by simp)))
  have r12 := row32 D mate inv chord edges noCycle 2 [(5,9),(3,25),(1,24),(0,4)] []
    #[1,1,1,1,1,1,1074862244,1211178181,43191013474,1,1245808969,44370562181,1678155091952045077062754,68206500293684365833283,1410321727974583337093,1750617127494600527970,53582397637055787123182,1753634331470128064054799,1524572529979507674245,2416593651903956966279200,75518551621998655178784,1255567509822931492565,2321871137519133888543,1115927,1,1,1149785,1133835611201,36541823932,2146338848,2112884834,1082338] (by decide) (by decide +kernel) (by simp)
  have r13 := row32 D mate inv chord edges noCycle 5 [(3,25),(1,24),(0,4)] [9]
    #[1,1,1182789,1,1,1,1,39079,1284264,1,1315088680,46516149445,1453048665483,1717152699036387953642629,54879697066272838421637,2131453134177636422787,1834145520289415784595589,58535722730429184245893,1864867929499511299269,57238423301212931804753,1870627152723156693865074,1845486193797,1285701130058681848370307,40178160314333807744131,1,1,2020514794629,1940755587,65358564485,1107260580,1204772927652,39865877535] (by decide) (by decide +kernel) (partnerCons r12 (by simp))
  have r14 := row32 D mate inv chord edges noCycle 3 [(1,24),(0,4)] [11,25]
    #[1,1,1,1,1,36965,1216614,1100655859876,1245815014,44299392131,1382112431433,1,2143610402313556830063681,1486488928918767277255,47567645737530643584199,1444169449445987364929669,1788700728162904118403,54801072858441502017039,1792631938554470940658224,1951138341542445213253763,1246665439373670668176449,38958294980427208363073,1293615081694216119030,1211883552,1,1,1109519160,1133835611236,1134943989858,37649154013,1107233857,2064515] (by decide) (by decide +kernel) (partnerCons r11 (partnerCons r13 (by simp)))
  have r15 := row32 D mate inv chord edges noCycle 24 [(23,19),(30,20),(1,25),(0,4)] []
    #[1,1,1115960,1078059809,1,1369781121946544368440,41395682614214915791012,1363658297817715575626949,1902951530167814890263,2026617581060528200278774,63331799408141506274038,2093369533509332841867,1636366325489689757496,53582397637055787108152,1249181414024273434426137,55383179031,1730724631,1878666069783,60925071986,1,1,1825464,57048,1,1,1,59162,1926939,2093761955640,1973188507,1,2126942888958] (by decide) (by decide +kernel) (by simp)
  have r16 := row32 D mate inv chord edges noCycle 23 [(30,20),(1,25),(0,4)] [19]
    #[1,1,1240263844896,1176561431,1,40178160314333807744131,1324661843654877305870500,1445948322149279880919,1987619973976185323675349,62113124186755791380181,2055285932841029251434,1598282724821386192663,52363722415670072239895,1249181414024273434435353,67066449279737549831639,2095826539991798432247,1843197952758,59816693329,1765367509,1,1,55991,1,1,1,1,1893114,1914134558619,1938551674,66466965271,1,1869272031] (by decide) (by decide +kernel) (partnerCons r15 (by simp))
  have r17 := row32 D mate inv chord edges noCycle 24 [(23,19),(30,21),(1,25),(0,4)] []
    #[1,1,1115960,1078059809,1,1369781121946544368440,41395682614214915791012,1363658297817715575626949,1902951530167814890263,2026617581060528200278774,63331799408141506274038,2093369533509332841867,1636366325489689757496,53582397637055787108152,1249181414024273434426137,55383179031,1730724631,1878666069783,60925071986,1,1692439,1,57048,1,1,1,59162,1926939,2093761955640,1973188507,1,2126942888958] (by decide) (by decide +kernel) (by simp)
  have r18 := row32 D mate inv chord edges noCycle 23 [(30,21),(1,25),(0,4)] [19]
    #[1,1,1914145046562,1176561431,1,40178160314333807744131,1324661843654877305870500,1217446718138349754532,1987619973976185323675349,62113124186755791380181,2055285932841029251434,1598282724821386192663,52363722415670072239895,1249181414024273434435353,1948622367257379149380276,60894449294587426962100,1843197952758,59816693329,1765367509,1,1791639,1,1,1,1,1,1893114,59817031579,1938551674,66466965271,1,1871479839] (by decide) (by decide +kernel) (partnerCons r17 (by simp))
  have r19 := row32 D mate inv chord edges noCycle 30 [(1,25),(0,4)] [20,21]
    #[1,1,2162411004962,1107233857,1,1204772927652,1107237028,35431618724,1257987325324587559713,40255594409666355784481,1288179021108637298715425,1598282724821386167294,48707696751512962150762,1597643903132756592244107,1334154526637990312928,2260603223566585459899324,70643850736455795637180,2321871137519154384465,59754397951787988550654,1905408536634834682878,1,1,1880953488382,2091474771933,67575343928,1,2112882490,2028414,63390,1,1,1] (by decide) (by decide +kernel) (partnerCons r16 (partnerCons r18 (by simp)))
  have r20 := row32 D mate inv chord edges noCycle 1 [(0,4)] [10,11,12,13,24,25]
    #[1,1,1,34851,1,1049764,1176541348,42082634817,1311176197383,1242528228384,1,1,1,1,1712533526826296937537,52363722415670072229325,1714636724385785187451374,1870627152723156693848065,2377596044819614089675807,74299876400612940284959,1218636830659234749108,2377596044819613433827359,71862525957134436302813,2245703935440004874205,1,1,2197879121952,35466999707,2111702047,2129196616769,1081281,33761] (by decide) (by decide +kernel) (partnerCons r2 (partnerCons r5 (partnerCons r7 (partnerCons r8 (partnerCons r14 (partnerCons r19 (by simp)))))))
  exact r20

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem partner8 (D : SimpleGraph (Fin 32)) (mate : Fin 32 → Fin 32)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 32).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 32).Adj i j ∨ j = mate i)
    (noCycle : ¬ ∃ m ∈ [3,4,6,7,8,14,15,16], cycleGraph m ⊑ D) :
    ¬ (∀ e ∈ ([(0,8)] : List (Fin 32 × Fin 32)), mate e.1 = e.2) := by
  have r0 := row32 D mate inv chord edges noCycle 1 [(31,27),(2,13),(0,8)] []
    #[1,1,1,34851,1148964,1248043009,1176541348,42082634817,1,1319968,1522903074,1351953440,1083820,1,1712533526826296937537,52363722415670072229325,1714636724385785187451374,48804414498,2377596044819614089675807,74299876400612940284959,1218636830659234749108,1522164663614673570649120,2260603222842541607198751,2056006632479,67647596379,2007794719,2197879121952,1,2111702047,2010022943,1081281,1] (by decide) (by decide +kernel) (by simp)
  have r1 := row32 D mate inv chord edges noCycle 31 [(2,13),(0,8)] [27]
    #[1,33761,1,1207060111391,1108316258,39865877535,1240239996101,1286175,1,1351711,2164699607402,1453629471,1636366325489689756703,1,1636641510217099435293100,36541808077,2299600830650928336502749,71862525957841510531037,2359954738187457974898,1902951530167814889503,62113124186755791364127,1522164663614673570650080,2017202332172725322783,65769149850912935707679,2126942888958,68683722585,2042462173,1,2062239,64447,1,1] (by decide) (by decide +kernel) (partnerCons r0 (by simp))
  have r2 := row32 D mate inv chord edges noCycle 1 [(3,12),(2,14),(0,8)] []
    #[1,1,1,1,1148964,1248043009,1176541348,42082634817,1,1319968,45479278657,1351953440,1,1488961,1,52363722415670072229325,1714636724385785187451374,1559774242,2377596044819614089675807,74299876400612940284959,1218636830659234749108,1522164663614673570649120,2017202332172725652545,52442346623501408633923,2143610402313556830063681,2377596043986612181508127,2197879121952,35466999707,2111702047,42692944559516758259075,1081281,33761] (by decide) (by decide +kernel) (by simp)
  have r3 := row32 D mate inv chord edges noCycle 3 [(2,14),(0,8)] [12]
    #[1,34851,1,1,1,36965,1216614,1176535303,1,44299392131,1382112431433,1557539938,1,1520738,1,1522786,1788700728162904118403,54801072858441502017039,1792631938554470940658224,1597209398370,1246665439373670668176449,38958294980427208363073,1293615081694216119030,2416593651903935978609920,75518551621976559131904,2131453134177636431939,69425175515070080727107,2260603223566585459882051,1134943989858,37649154013,1107233857,1207060111391] (by decide) (by decide +kernel) (partnerCons r2 (by simp))
  have r4 := row32 D mate inv chord edges noCycle 3 [(1,24),(2,22),(0,8)] []
    #[1,1,1,1,1,36965,1216614,1176535303,1,44299392131,1382112431433,1100655995176,2143610402313556830063681,66987825072298650930241,1714990533321026176067,56019748079819553495107,1788700728162904118403,54801072858441502017039,1792631938554470940658224,1834634338,1246665439373670668176449,38958294980427208363073,1,1117942,1,1938544707,63141828675,2056006654019,1134943989858,37649154013,1107233857,1207060111391] (by decide) (by decide +kernel) (by simp)
  have r5 := row32 D mate inv chord edges noCycle 5 [(30,7),(1,29),(2,22),(0,8)] []
    #[1,1,1,36965,1,1,1,1,1,1275708080393,1315088680,46516149445,1453048665483,48786320630126914566376,1324661842858194749536420,1524572529967244575752,48786320959330891924488,1561162270699001966822408,1864867929499511299269,57238423301212931804753,1870627152723156693865074,1144133302,1,40178160314333807744131,1369781121946544368440,1880953622626,1278020088698,67575321799,1248066492,1,1,39865877535] (by decide) (by decide +kernel) (by simp)
  have r6 := row32 D mate inv chord edges noCycle 30 [(1,29),(2,22),(0,8)] [7]
    #[1,1,1,1107233857,38757499902,1204772927652,1136123878365,1,1,1138697472,1418986494,1598282724821386167294,48707696751512962150762,1597643903132756592244107,1753634331470128064038846,2260603223566585459899324,70643850736455795637180,2321871137519154384465,2260603223566585911314364,68206500294111164035962,1809995301886,67612216021,1,2091474771933,67575343928,2007825340,2022825821182,2028414,63390,1,1,1] (by decide) (by decide +kernel) (partnerCons r5 (by simp))
  have r7 := row32 D mate inv chord edges noCycle 1 [(2,22),(0,8)] [24,29]
    #[1,1,1,34851,1148964,2416593651903956310430752,1176541348,42082634817,1,1319968,50004996180729978869825,1351953440,43262521376,1384400696352,1712533526826296937537,52363722415670072229325,1714636724385785187451374,1878666069026,2377596044819614089675807,74299876400612940284959,1218636830659234749108,1084117,1,1115894,1,1836868642,2197879121952,35466999707,2111702047,1,1081281,33761] (by decide) (by decide +kernel) (partnerCons r4 (partnerCons r6 (by simp)))
  have r8 := row32 D mate inv chord edges noCycle 1 [(2,23),(0,8)] []
    #[1,1,1,34851,1148964,1248043009,1176541348,42082634817,1,1319968,1600159877783359323855937,1351953440,1638823331984419019841,1384400696352,1712533526826296937537,52363722415670072229325,1714636724385785187451374,1327176627866617042885346,2377596044819614089675807,74299876400612940284959,1218636830659234749108,1522164663614673570649120,1793089,1,1115927,2377596043986612181508127,2197879121952,35466999707,2111702047,1366174224847899964759107,1081281,33761] (by decide) (by decide +kernel) (by simp)
  have r9 := row32 D mate inv chord edges noCycle 3 [(1,23),(31,22),(2,30),(0,8)] []
    #[1,1,1,1,1,36965,1216614,1176535303,1,44299392131,1382112431433,1100655995176,52442346623501408633923,2055285932841029241921,1756150306120730032470083,56098372287657755539523,1788700728162904118403,54801072858441502017039,1792631938554470940658224,1774549959747,1246665439373670668176449,38958294980427208363073,1,1,1949612115011,1871481921,63141807171,2111728738,1134943989858,37649154013,1,1] (by decide) (by decide +kernel) (by simp)
  have r10 := row32 D mate inv chord edges noCycle 1 [(31,22),(2,30),(0,8)] [23]
    #[1,1,1,34851,1148964,2163590991970,1176541348,42082634817,1,1319968,2065615188144871076856863,1351953440,45130295294760321092741,1366174235277301612804163,1712533526826296937537,52363722415670072229325,1714636724385785187451374,1873143127373759460079681,2377596044819614089675807,74299876400612940284959,1218636830659234749108,1522164663614673570649120,1,1,2113987318,2162411004962,2197879121952,35466999707,2111702047,2029633,1,1] (by decide) (by decide +kernel) (partnerCons r9 (by simp))
  have r11 := row32 D mate inv chord edges noCycle 29 [(31,23),(2,30),(0,8)] []
    #[1,2029633,1,37649154013,1169338365059,1144133566,36612250558,1107260648,1,2079293705,1560199124153082609629,47489021530128320998729,1558646296048414789382506,2055285932841029269471,2221605616482242583295899,69425175515070080743323,2283787536850850794032,1486488929311205030880,47567645737958549421024,1914134198239,68683454167,1802239965,2056006654908,1,1973188507,1938554845,1994589,62333,1,1,1,1] (by decide) (by decide +kernel) (by simp)
  have r12 := row32 D mate inv chord edges noCycle 31 [(2,30),(0,8)] [22,23]
    #[1,33761,1,2063458,1108316258,39865877535,1240239996101,1171591995390,1,1351711,1169313541118,1453629471,1636366325489689756703,49926371972898643490187,1636641510217099435293100,1792631938554470940642271,2299600830650928336502749,71862525957841510531037,2359954738187457974898,2299600830650928754363357,69425175515462519191451,2169536735202910369691,1,1,2126942888958,68683722585,2042462173,2058293937183,2062239,64447,1,1] (by decide) (by decide +kernel) (partnerCons r10 (partnerCons r11 (by simp)))
  have r13 := row32 D mate inv chord edges noCycle 2 [(0,8)] [13,14,22,23,30]
    #[1,1,1,1,35908,1182789,1141907686,1211178181,1,1346644314408,1074866472,34395760936,1384400685088,1,1,1750617127494600527970,53582397637055787123182,1753634331470128064054799,1486488929311204640800,2416593651903956966279200,75518551621998655178784,1255567509822931492565,1,1,1327176627900061188974338,42692944559517690848323,2321871111487844753439,1133835611201,36541823932,2146338848,1,1082338] (by decide) (by decide +kernel) (partnerCons r1 (partnerCons r3 (partnerCons r7 (partnerCons r8 (partnerCons r12 (by simp))))))
  exact r13

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem partner9 (D : SimpleGraph (Fin 32)) (mate : Fin 32 → Fin 32)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 32).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 32).Adj i j ∨ j = mate i)
    (noCycle : ¬ ∃ m ∈ [3,4,6,7,8,14,15,16], cycleGraph m ⊑ D) :
    ¬ (∀ e ∈ ([(0,9)] : List (Fin 32 × Fin 32)), mate e.1 = e.2) := by
  have r0 := row32 D mate inv chord edges noCycle 3 [(2,14),(20,4),(0,9)] []
    #[1,34851,1,1,1,36965,1216614,42153804867,1245815014,1,1382112431433,1557539938,1100656029001,1520738,1,1632677515395,1788700728162904118403,54801072858441502017039,1792631938554470940658224,1151635,1,38958294980427208363073,1293615081694216119030,1869271171,60925071491,1810018100324,69425175515070080727107,2260603223566585459882051,1134943989858,37649154013,1107233857,1405171842361644488359012] (by decide) (by decide +kernel) (by simp)
  have r1 := row32 D mate inv chord edges noCycle 2 [(20,4),(0,9)] [14]
    #[1,1,1,1,1,1182789,36541079782,1211178181,43191013474,1,1562656130647811821666,1386580000,44370888736,1169314622861,1,1750617127494600527970,53582397637055787123182,1753634331470128064054799,1144148594,2416593651903956966279200,1,1255567509822931492565,1834618978,59816677474,1810018076772,2377596044022931533341727,74299875567611032118303,1133835611201,36541823932,2146338848,2321871137519154368610,1082338] (by decide) (by decide +kernel) (partnerCons r0 (by simp))
  have r2 := row32 D mate inv chord edges noCycle 10 [(11,7),(20,12),(0,9)] []
    #[1,1353760,1346644314443,1382112431433,45407770788,1315088680,1252714,1,42250,1,1,1,1,1453389,1348932679051,1488272845,52058042730,1630389250608,1421234802,1246665439373670668193097,1,56098372287230647841198,1717152699036387501153644,2055285932841029251434,63331799408141506274038,2065615188144871076882199,2224121589970626090835306,1480651081880862907541800,46270346308776965843240,1560199124153082609629,2321871137519154377066,1385503] (by decide) (by decide +kernel) (by simp)
  have r3 := row32 D mate inv chord edges noCycle 3 [(1,17),(11,27),(20,12),(0,9)] []
    #[1,1,1,1,1,36965,1216614,42153804867,1245815014,1,1382112431433,1,1,1701325474881,49912775747,1636641510217113914658444,1788700728162904118403,1,1792631938554470940658224,1109511761,1,38958294980427208363073,1293615081694216119030,1636366325489690466996,2416593651903249892221216,75518551621256113004832,2359954737409447665952,1,1134943989858,37649154013,1107233857,1293633677202354938911] (by decide) (by decide +kernel) (by simp)
  have r4 := row32 D mate inv chord edges noCycle 1 [(11,27),(20,12),(0,9)] [17]
    #[1,1,1,34851,1148964,39937385473,1176541348,42082634817,1311176197383,1,1353760,1,1,44370900000,1712533526826296937537,52363722415670072229325,1714636724385785187451374,1,2377596044819614089675807,74299876400612940284959,1,48786320959344263975968,1561162270699016447252512,1675639117301442311609012,51145047194284358133595,1219903724633079541593,2197879121952,1,2111702047,1219903724633079541661,1081281,33761] (by decide) (by decide +kernel) (partnerCons r3 (by simp))
  have r5 := row32 D mate inv chord edges noCycle 11 [(20,12),(0,9)] [7,27]
    #[1,1990135948626788088808812,1386580000,46515881027,1417580548458,46516149445,1349725513,1,1385739,1,1,1,1,45421,1487214,1632677515659,1522909678,53166421387,1665857367633,1692043,1,1757579,2019659338667453850955,1869271435,2093369533509332841867,64550474629527221167895,2104612795229213953485624,1,1519648688964106272517449,47489021530128320998729,1598282724821386167294,2359954738187457974667] (by decide) (by decide +kernel) (partnerCons r2 (partnerCons r4 (by simp)))
  have r6 := row32 D mate inv chord edges noCycle 17 [(19,7),(21,25),(20,16),(0,9)] []
    #[1,1247884114595056383087121,1753634331470128064054799,54801072858441502017039,1826784328831207708836,1753634331470128516551183,52363722416097977712077,1,1764991536,1,1630389250608,53166421387,1557546511,1561741381201,1588689,49649,1,1,1,1,1,1,1730730676,59816693329,1878666069783,1,57599936345,1843197964121,46270346308776965850707,2286207352329302429265,2321871137519154384465,71862525957841510531037] (by decide) (by decide +kernel) (by simp)
  have r7 := row32 D mate inv chord edges noCycle 19 [(21,25),(20,16),(0,9)] [7]
    #[1,74299876400612940284959,2416593651903956966279200,1327176628192959187632787,1831629545638813817261649,57238423301212931804753,1902951530167814889702,1,1246665439373670668193033,1,1246665439373670668193097,1665857367668,1701325484658,55383178701,1626820177,1557139,1,51763,1,1,1,1,1757814,1732962071,1800004342,1,1949602303833,1800007513,57600274265,2095826539611624724183,67066449279702081885911,2068131162795473390584469] (by decide) (by decide +kernel) (partnerCons r6 (by simp))
  have r8 := row32 D mate inv chord edges noCycle 22 [(21,29),(20,16),(0,9)] []
    #[1,1561162270699016447252512,2129196518101,1293615081694216119030,38996378581095511953506,1285701130058681848370307,1788700728162904136372,1948622366891842447071924,60894448965370076486324,1,2341076328785205675731669,2019659338667453850955,1665857378996,56562727408,1626823348,1807729835733,1,1730730676,1629051572,1757814,1,1,1,1,57048,1859289,1975416502,1903914841,65358586614,1,2030293,2065615188144871076865055] (by decide) (by decide +kernel) (by simp)
  have r9 := row32 D mate inv chord edges noCycle 21 [(20,16),(0,9)] [25,29]
    #[1,48786320959344263975968,1255567509822931492565,38958294980427208363073,1247884114595056383070306,1788700728162904118964,1909624759807499570468499,59675773743984361592467,1979118731504422070568,1,1981575737999151300906,38958294980427208371529,52058043060,1626814132,1772261718708,57599936015,1,1590964,1723989,53877,1,1,1,55991,1825464,1,1869278008,64250207957,2020538537883,1,2026617581060528200254462,48786320959344263976928] (by decide) (by decide +kernel) (partnerCons r7 (partnerCons r8 (by simp)))
  have r10 := row32 D mate inv chord edges noCycle 17 [(18,8),(21,13),(20,24),(0,9)] []
    #[1,2095826540002954234484,1753634331470128064054799,54801072858441502017039,1826784328831207708836,1349719602,1600159877782931418186761,1624327,1,1,1630389250608,53166421387,1557546511,1,1588689,49649,1,1,1,51763,1,1,1730730676,59816693329,1,1765361464,60996242036,2263119161026171948474961,47489021530128321016370,1484031922816510031410,2321871137519154384465,71862525957841510531037] (by decide) (by decide +kernel) (by simp)
  have r11 := row32 D mate inv chord edges noCycle 18 [(21,13),(20,24),(0,9)] [8]
    #[1,2377596044819614089675807,2095826540002953742964,1792631938554470940658224,56019748079827216910896,1864867929499511299269,45130295295194877940338,1448405328650659713650,1,1,1455337165426,1665857367633,54274800044,1,1698321838,1622514,50706,1,1,1,1,1,1736793601718,1765367509,1,1914134186808,1765370680,56491895608,2019659338655191251381,64629098837345185544629,2068131162795459362666933,2359954738187457974898] (by decide) (by decide +kernel) (partnerCons r10 (by simp))
  have r12 := row32 D mate inv chord edges noCycle 21 [(20,24),(0,9)] [13]
    #[1,48786320959344263975968,1255567509822931492565,38958294980427208363073,1247884114595056383070306,1402655868873261433283221,1909624759807499570468499,59675773743984361592467,1979118731504422070568,1,57238423301640837287505,1788700728555341499985,1246665439373670667922761,1,1772261718708,57599936015,1696093843,1703613849301,1723989,53877,1,1,1,55991,1,1726264,1869278008,64250207957,2020538537883,1951890568884,2026617581060528200254462,48786320959344263976928] (by decide) (by decide +kernel) (partnerCons r11 (by simp))
  have r13 := row32 D mate inv chord edges noCycle 4 [(6,27),(12,8),(19,11),(20,28),(0,9)] []
    #[1,1148964,35908,1,1,1,1,1250439,1,1,45407770788,1,1,43191013804,1560199124165346249323,1795147913205073706850468,57317047509044268210340,1826784328831207708836,56019748079827216910896,1,1,1247884114595056383070306,38996378581095511953506,1331697556462612866839,40974968667,1940756644,2182608009727115948788890,1,1,1169338365059,38757499902,1108316258] (by decide) (by decide +kernel) (by simp)
  have r14 := row32 D mate inv chord edges noCycle 6 [(12,8),(19,11),(20,28),(0,9)] [27]
    #[1,1176541348,36541079782,1216614,38022,1,1,1,1,1,1282683242,1,1,1488516782508,1349728684,43191351724,1526273153256,1600159877782931418186761,1488516782675,1,1,1909624759807499570468499,2248159780458017807028,1324661843654877305870500,41395682614214915791012,1407864721515336331097,2171993740214556565734,1,1,2129196785894,67612483814,1240239996101] (by decide) (by decide +kernel) (partnerCons r13 (by simp))
  have r15 := row32 D mate inv chord edges noCycle 12 [(19,11),(20,28),(0,9)] [8]
    #[1,1488266241,44370888736,1100656029001,1558646296377631031512426,1453048665483,47624528102,1384362346,1,1,44364,1,1,1,46478,1521039,1629048172,1557546511,54274800044,1,1,1246665439373670667922761,1732958603,55454686603,1774549983627,2131453134177636432300,65769149850912936061752,2143610402313556830089049,1,1558646296048414789382506,48707696751512962150762,1636366325489689756703] (by decide) (by decide +kernel) (partnerCons r14 (by simp))
  have r16 := row32 D mate inv chord edges noCycle 21 [(19,15),(20,28),(0,9)] []
    #[1,48786320959344263975968,1255567509822931492565,38958294980427208363073,1247884114595056383070306,1750617127494600545939,1909624759807499570468499,59675773743984361592467,1979118731504422070568,1,1981575737999151300906,38958294980427208371529,55454348751,1592186515,1772261718708,1,1696093843,1594414739,1723989,1,1,1,1,55991,1825464,1940779669,1869278008,64250207957,1,1996468,2026617581060528200254462,2044690100] (by decide) (by decide +kernel) (by simp)
  have r17 := row32 D mate inv chord edges noCycle 19 [(20,28),(0,9)] [11,15]
    #[1,74299876400612940284959,2416593651903956966279200,60894448965370076202051,1831629545638813817261649,57238423301212931804753,1902951530167814889702,1445948322149280182931,1246665439373670668193033,1,1246665439373670668193097,1,1701325484658,55383178701,1626820177,1,1656339,51763,1,1,1,53877,1757814,1916422451859,1800004342,62033450643,1949602303833,1962643,1,2028179,1902951530167814882302,2146366099] (by decide) (by decide +kernel) (partnerCons r15 (partnerCons r16 (by simp)))
  have r18 := row32 D mate inv chord edges noCycle 20 [(0,9)] [4,12,16,24,28]
    #[1,1218636830659234749108,75518551621998655178784,1246665439373670668176449,1,1870627152723156693865074,58457098522598646698610,1941035130836118480135,38958294980427208380681,1,38958294980427208380745,1246665439373670668184905,1,1736793601683,56491557358,1661457010,1,1690164,52820,1,1,1,54934,1791639,1,1834641175,63141829300,1985070420858,1,1987619973976185323421661,48786320959344263986144,1941035130836118479903] (by decide) (by decide +kernel) (partnerCons r1 (partnerCons r5 (partnerCons r9 (partnerCons r12 (partnerCons r17 (by simp))))))
  exact r18

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem partner10 (D : SimpleGraph (Fin 32)) (mate : Fin 32 → Fin 32)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 32).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 32).Adj i j ∨ j = mate i)
    (noCycle : ¬ ∃ m ∈ [3,4,6,7,8,14,15,16], cycleGraph m ⊑ D) :
    ¬ (∀ e ∈ ([(0,10)] : List (Fin 32 × Fin 32)), mate e.1 = e.2) := by
  have r0 := row32 D mate inv chord edges noCycle 4 [(2,25),(21,5),(0,10)] []
    #[1,1148964,1,1,1,1,38022,1250439,2026617581060528200261765,1280451847,1,1417580548458,1240239974764,2182608009397899706667106,68206500293684365824098,1753074133989329766500,1668145632420,1826784328831207708836,56019748079827216910896,1831629545638813817261649,1185460,1,38996378581095511953506,1331697556462612866839,1903908004,1,1845486217349,1144155993,38758312828,1169338365059,38757499902,1108316258] (by decide) (by decide +kernel) (by simp)
  have r1 := row32 D mate inv chord edges noCycle 2 [(21,5),(0,10)] [25]
    #[1,1,1,1,35908,1,2029133555711130931857605,1211178181,43191013474,1346644314408,1,63331799408141505989765,1074868586,48732897314,1100667597162,1750617127494600527970,53582397637055787123182,1753634331470128064054799,1171592499826,2416593651903956966279200,75518551621998655178784,1,1144133302,36612265687,1275708858069,1,2416593651070955058111808,1133835611201,36541823932,2146338848,2321871137519153877090,1082338] (by decide) (by decide +kernel) (partnerCons r0 (by simp))
  have r2 := row32 D mate inv chord edges noCycle 19 [(20,28),(21,17),(0,10)] []
    #[1,74299876400612940284959,2416593651903956966279200,1902951530167814587459,1831629545638813817261649,57238423301212931804753,1902951530167814889702,1750617127494614668848,47489021530128321016467,1951138341542445213253961,1,1951138341542445213253963,1701325484658,55383178701,1626820177,1594414739,1656339,1,1,1,1,1,1757814,1916422451859,1800004342,62033450643,1949602303833,1962643,1,2028179,1703624503957,2057742939335744374454] (by decide) (by decide +kernel) (by simp)
  have r3 := row32 D mate inv chord edges noCycle 20 [(21,17),(0,10)] [28]
    #[1,1218636830659234749108,75518551621998655178784,1246665439373670668176449,1366174235277302064236212,1870627152723156693865074,58457098522598646698610,1941035130836118480135,1990135948626788088817960,38958294980427208380714,1,62191748394587127775563,1701325484693,1736793601683,56491557358,1661457010,1590964,1,52820,1,1,1,54934,1791639,1703613849301,1834641175,63141829300,1985070420858,1,62113124186755791093725,2133910140279928314616,68285124501087796779768] (by decide) (by decide +kernel) (partnerCons r2 (by simp))
  have r4 := row32 D mate inv chord edges noCycle 19 [(22,14),(21,25),(0,10)] []
    #[1,74299876400612940284959,2416593651903956966279200,2133910140636897595029,1831629545638813817261649,57238423301212931804753,1902951530167814889702,46348970516580592834195,1486488929318963304083,1951138341542445213253961,1,1951138341542445213253963,1701325484658,55383178701,1,1732958671,1656339,51763,1,1,1,1,1,1772261718743,1800004342,1,1949602303833,1800007513,57600274265,2057742939323494841814,65847774058730900438486,2107128769879802239270358] (by decide) (by decide +kernel) (by simp)
  have r5 := row32 D mate inv chord edges noCycle 22 [(21,25),(0,10)] [14]
    #[1,50004996180729978869792,2065615188144871076855842,1293615081694216119030,38996378581095511953506,1285701130058681848370307,1441653474831704403044022,1948622366891842447071924,60894448965370076486324,2017202332172725661001,1,58457098523026552181362,1826784329223645090418,64629098837358523264397,1,1807729835733,58708314672,1730730676,1739081966326,1757814,54934,1,1,1,57048,1,1760089,1903914841,65358586614,2056006654908,1987358685909,64550474629527221151775] (by decide) (by decide +kernel) (partnerCons r4 (by simp))
  have r6 := row32 D mate inv chord edges noCycle 21 [(0,10)] [5,17,25]
    #[1,1562656130647811839008,1255567509822931492565,38958294980427208363073,1247884114595056383070306,1,1909624759807499570468499,59675773743984361592467,1979118731504422070568,1217446718138350261546,1,1217446718138350261610,63410423615972841630060,2029133555711130932161933,1772261718708,57599936015,1696093843,1,1723989,53877,1,1,1,55991,1825464,1,1869278008,64250207957,2020538537883,2026617581060528199991261,63331799408141506249726,1979118731504422070303] (by decide) (by decide +kernel) (partnerCons r1 (partnerCons r3 (partnerCons r5 (by simp))))
  exact r6

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem partner11 (D : SimpleGraph (Fin 32)) (mate : Fin 32 → Fin 32)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 32).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 32).Adj i j ∨ j = mate i)
    (noCycle : ¬ ∃ m ∈ [3,4,6,7,8,14,15,16], cycleGraph m ⊑ D) :
    ¬ (∀ e ∈ ([(0,11)] : List (Fin 32 × Fin 32)), mate e.1 = e.2) := by
  have r0 := row32 D mate inv chord edges noCycle 29 [(30,26),(21,1),(0,11)] []
    #[1,1,2146338848,37649154013,1169338365059,1598282724849095637984,1407864722226986937309,1257987326043925478401,40255594410351333964801,1210183806939931213687775,1560199124153082609629,1,1558646296048414789382506,35432347019,2221605616482242583295899,69425175515070080743323,2283787536850850794032,1600739731328236092384,51223671402126706047968,1774527217629,66537391796,1,2056006654908,66466965271,1973188507,1895389,1,62333,1,1,1,64447] (by decide) (by decide +kernel) (by simp)
  have r1 := row32 D mate inv chord edges noCycle 30 [(21,1),(0,11)] [26]
    #[1,1,2378905245374039985902626,1107233857,38757499902,1204772927652,2338598437735250225403102,1133811869003,46516173792,2112892233,1600159877783359323145214,1,48707696751512962150762,1597643903132756592244107,46587673568,2260603223566585459899324,70643850736455795637180,2321871137519154384465,1739081155582,55453975550,2112882356,1,1108343509,2091474771933,67575343928,2007825340,1,2028414,63390,1,1,1] (by decide) (by decide +kernel) (partnerCons r0 (by simp))
  have r2 := row32 D mate inv chord edges noCycle 10 [(8,28),(21,5),(0,11)] []
    #[1,1419296,1445948322469289883528,1382112431433,45407770788,1,1331697556462592370885,1351914,1,1,1,1,44364,1453389,45051671087783688348935,1488272845,52058042730,1630389250608,2245703936182547196200,1951138341542445213253994,1277996346005,1,1453048665782,2055285932841029251434,63331799408141506274038,2065615188144871076882199,2042439976,1480651081880862907541800,1,1560199124153082609629,1351973820,2064746] (by decide) (by decide +kernel) (by simp)
  have r3 := row32 D mate inv chord edges noCycle 8 [(21,5),(0,11)] [28]
    #[1,1311176197383,43191013474,1245815014,2026617581060528200261765,1,40136,1,1,1,42250,1,1638823331984418445544,1418999179,49841285416,1559453016558,46270346308754869796360,1480651081880155833483816,1843197648069,43191031443,1349719732,1,60894448965370076486324,1987619973976185323675349,1277996850901,1402655868873261433266406,43832995902289419772134,1484031922816510031771,1,2129196853544,46516173792,1453630432] (by decide) (by decide +kernel) (partnerCons r2 (by simp))
  have r4 := row32 D mate inv chord edges noCycle 19 [(20,8),(21,17),(0,11)] []
    #[1,74299876400612940284959,2416593651903956966279200,1382112431732,1831629545638813817261649,57238423301212931804753,1902951530167814889702,1750617127494614668848,1,1723688,1951138341542445213253994,1,1701325484658,55383178701,1626820177,1594414739,1656339,1,1,1,1,1,1757814,1663688405,1800004342,62033450643,1949602303833,2263119161026171948475027,71941112974656569320083,2286207352329302418067,1873154991307952027312789,2057742939335744374454] (by decide) (by decide +kernel) (by simp)
  have r5 := row32 D mate inv chord edges noCycle 23 [(20,28),(21,17),(0,11)] []
    #[1,65769149850912936045569,1639157484867702200436768,41395682614207157163735,1331697556462612866839,40178160314333807744131,1324661843654877305870500,1826784328831207726805,1987619973976185323675349,62113124186755791380181,2055285932841029251434,1,60894448965383448522644,1902951530180078563220,57671106065,1661460181,1843197952758,1,1765367509,1916422451859,1,1,1,1,1,58105,1893114,1869271963,1,66466965271,2091474771933,51223671402115693764576] (by decide) (by decide +kernel) (by simp)
  have r6 := row32 D mate inv chord edges noCycle 20 [(21,17),(0,11)] [8,28]
    #[1,1218636830659234749108,75518551621998655178784,1246665439373670668176449,1366174235277302064236212,1870627152723156693865074,58457098522598646698610,1941035130836118480135,1,1990135948626788088819017,62191748394587127775594,1,1701325484693,1736793601683,56491557358,1661457010,1590964,1,52820,1,1,1,54934,1791639,1703613849301,1834641175,63141829300,1985070420858,1,1941035130836118175709,2133910140279928314616,68285124501087796779768] (by decide) (by decide +kernel) (partnerCons r4 (partnerCons r5 (by simp)))
  have r7 := row32 D mate inv chord edges noCycle 22 [(21,25),(0,11)] []
    #[1,1600739731316115429408,64550474629527221141538,1293615081694216119030,38996378581095511953506,1285701130058681848370307,1441653474831704403044022,1948622366891842447071924,60894448965370076486324,2017202332172725661001,1948622366891842899568308,1,1826784329223645090418,1217446718138350253451,64629098837358523298222,1807729835733,58708314672,1730730676,1739081966326,1757814,54934,1,1,1,57048,1,1760089,1903914841,65358586614,2056006654908,1987358685909,1600739731316115430368] (by decide) (by decide +kernel) (by simp)
  have r8 := row32 D mate inv chord edges noCycle 2 [(1,13),(22,6),(21,31),(0,11)] []
    #[1,1,1,1,35908,1182789,1,1211178181,43191013474,1346644314408,1522903105,1,1486913,1,34395862411,1750617127494600527970,53582397637055787123182,1753634331470128064054799,1561741281345,2416593651903956966279200,75518551621998655178784,1,1,36541814487,2093369533509332841506,68206500293684365833250,2221605616482242583278626,1133835611201,36541823932,2146338848,1366174235277301612804163,1] (by decide) (by decide +kernel) (by simp)
  have r9 := row32 D mate inv chord edges noCycle 1 [(22,6),(21,31),(0,11)] [13]
    #[1,1,1,34851,1148964,1218636830659234748613,1,42082634817,1311176197383,1561162270699016447261697,1419296,1,1049995,1,1712533526826296937537,52363722415670072229325,1714636724385785187451374,1703613758465,2377596044819614089675807,74299876400612940284959,1218636830659234749108,1,1,1311176197878,2143610402313556830071809,1985070431233,2197879121952,35466999707,2111702047,43911620073408965937252,1081281,1] (by decide) (by decide +kernel) (partnerCons r8 (by simp))
  have r10 := row32 D mate inv chord edges noCycle 22 [(21,31),(0,11)] [6]
    #[1,1600739731316115429408,2113964757,1293615081694216119030,38996378581095511953506,1285701130058681848370307,1,1948622366891842447071924,60894448965370076486324,2017202332172725661001,2324328144013883648725,1,2380112019470216855925461,1217446718138350253451,64629098837358523298222,1807729835733,58708314672,1730730676,2171993740948231905049,1757814,54934,1,1,1,57048,1859289,2022826802870,1903914841,65358586614,2056006654908,2095829,1] (by decide) (by decide +kernel) (partnerCons r9 (by simp))
  have r11 := row32 D mate inv chord edges noCycle 21 [(0,11)] [1,5,17,25,31]
    #[1,1,1255567509822931492565,38958294980427208363073,1247884114595056383070306,1,1909624759807499570468499,59675773743984361592467,1979118731504422070568,63410423615972841631049,1981575737999151300970,1,1217446718138350261643,38958294980427208373643,1772261718708,57599936015,1696093843,1,1723989,53877,1,1,1,55991,1825464,1,1869278008,64250207957,2020538537883,63331799408141505953757,1600739731316115438560,1] (by decide) (by decide +kernel) (partnerCons r1 (partnerCons r3 (partnerCons r6 (partnerCons r7 (partnerCons r10 (by simp))))))
  exact r11

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem partner12 (D : SimpleGraph (Fin 32)) (mate : Fin 32 → Fin 32)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 32).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 32).Adj i j ∨ j = mate i)
    (noCycle : ¬ ∃ m ∈ [3,4,6,7,8,14,15,16], cycleGraph m ⊑ D) :
    ¬ (∀ e ∈ ([(0,12)] : List (Fin 32 × Fin 32)), mate e.1 = e.2) := by
  have r0 := row32 D mate inv chord edges noCycle 22 [(3,19),(2,13),(1,5),(0,12)] []
    #[1,1,1,1,38996378581095511953506,1,1207060616851,1948622366891842447071924,60894448965370076486324,2017202332172725661001,2019659338667453854058,2068131162795472734729611,1,1,40178160314333807761869,1807729835733,58708314672,1730730676,1324661843654877305887315,1,54934,1,1,1,57048,1859289,2171993740205690049206,1903914841,65358586614,2056006654908,1638823331984419027936,2017202332172725322783] (by decide) (by decide +kernel) (by simp)
  have r1 := row32 D mate inv chord edges noCycle 3 [(2,13),(1,5),(0,12)] [19]
    #[1,1,1,1,1,1,1216614,1109499077,1245815014,44299392131,1382112431433,1074859372,1,1,1117645,1448405328642886927526,1788700728162904118403,54801072858441502017039,1792631938554470940658224,1,1246665439373670668176449,38958294980427208363073,1293615081694216119030,2359954738187437478944,1676906932652722610274,68206500293684365833283,2221605616482242583278659,1366174235277288692183907,1134943989858,37649154013,1107233857,2113967235] (by decide) (by decide +kernel) (partnerCons r0 (by simp))
  have r2 := row32 D mate inv chord edges noCycle 22 [(3,19),(2,25),(1,5),(0,12)] []
    #[1,1,1,1,38996378581095511953506,1,1207060616851,1948622366891842447071924,60894448965370076486324,2017202332172725661001,2019659338667453854058,1257987325301383454489,1,41474269631029974881939,1217446718138350254508,1807729835733,58708314672,1730730676,1324661843654877305887315,1,54934,1,1,1,57048,1,2171993740205690049206,1903914841,65358586614,2056006654908,1638823331984419027936,1880953521183] (by decide) (by decide +kernel) (by simp)
  have r3 := row32 D mate inv chord edges noCycle 3 [(2,25),(1,5),(0,12)] [19]
    #[1,1,1,1,1,1,1216614,1109499077,1245815014,44299392131,1382112431433,1074859372,1,1176535437,49840915523,1448405328642886927526,1788700728162904118403,54801072858441502017039,1792631938554470940658224,1,1246665439373670668176449,38958294980427208363073,1293615081694216119030,2359954738187437478944,1149752,1,1118041,1366174235277288692183907,1134943989858,37649154013,1107233857,2113967235] (by decide) (by decide +kernel) (partnerCons r2 (by simp))
  have r4 := row32 D mate inv chord edges noCycle 4 [(3,19),(2,26),(1,5),(0,12)] []
    #[1,1,1,1,1,1,38022,1250439,1136123976901,1280451847,45407770788,1417580548458,1,38757499277,1772261718147,48786320958916358478056,1483167056530330241533094,1826784328831207708836,56019748079827216910896,1,1151635,1247884114595056383070306,38996378581095511953506,1331697556462612866839,1949602303076,1112696642,1,1219921157921959668869,1134943989893,1169338365059,38757499902,1108316258] (by decide) (by decide +kernel) (by simp)
  have r5 := row32 D mate inv chord edges noCycle 3 [(2,26),(1,5),(0,12)] [19]
    #[1,1,1,1,1,1,1216614,1109499077,1245815014,44299392131,1382112431433,1074859372,1,1176535437,49840915523,1448405328642886927526,1788700728162904118403,54801072858441502017039,1792631938554470940658224,1,1246665439373670668176449,38958294980427208363073,1293615081694216119030,2359954738187437478944,1275731961921,1149785,1,1118074,1134943989858,37649154013,1107233857,2197879121987] (by decide) (by decide +kernel) (partnerCons r4 (by simp))
  have r6 := row32 D mate inv chord edges noCycle 2 [(1,5),(0,12)] [13,25,26]
    #[1,1,1,1,35908,1,1083589,1211178181,43191013474,1346644314408,1277996345409,1523710039072,1,1,1490487328,1750617127494600527970,53582397637055787123182,1753634331470128064054799,1909624759807499570451490,2416593651903956966279200,75518551621998655178784,1255567509822931492565,2416593651903956310430752,73081201178520151163902,2283787536108308431870,1,1,1133835611201,36541823932,2146338848,1334154526637977237571,1082338] (by decide) (by decide +kernel) (partnerCons r1 (partnerCons r3 (partnerCons r5 (by simp))))
  have r7 := row32 D mate inv chord edges noCycle 11 [(1,10),(0,12)] []
    #[1,1,1387585,1074859372,1417580548458,46516149445,1349725513,1100930620780,1385739,43307,1,1,1,45421,1487214,1558646296048414133534058,1522909678,53166421387,1665857367633,1951138341542445213254027,62191748394587127775627,1981575737999151301003,2019659338667453842763,1756150306120730377486733,2093369533509332841867,64550474629527221167895,2104612795229213953485624,1133835611500,1519648688964106272517449,47489021530128320998729,1598282724821386167294,1421343] (by decide) (by decide +kernel) (by simp)
  have r8 := row32 D mate inv chord edges noCycle 3 [(2,6),(1,21),(0,12)] []
    #[1,1,1,1,1,36965,1,1117414,1245815014,44299392131,1382112431433,1313464462434,1,1176535437,49840915523,1100656130476,1788700728162904118403,54801072858441502017039,1792631938554470940658224,1948622366891842447054915,1246665439373670668176449,1,1293615081694216119030,1246665439373670012328001,37649832696,1204794646297,2416593651105110854806912,1366174235277288692183907,1134943989858,37649154013,1107233857,2283787536850830299134] (by decide) (by decide +kernel) (by simp)
  have r9 := row32 D mate inv chord edges noCycle 4 [(3,7),(2,13),(1,21),(0,12)] []
    #[1,1,1,1,1,1,38022,1,1151239,1280451847,45407770788,1417580548458,1,1,1594909296740,1144143309,36612619725,1826784328831207708836,56019748079827216910896,1831629545638813817261649,1109496469,1,38996378581095511953506,1331697556462612866839,1247884114595055727221858,1717152699036387953643618,2359954737444915611680,1981575737972550241345,63410423615945133231169,1169338365059,38757499902,1108316258] (by decide) (by decide +kernel) (by simp)
  have r10 := row32 D mate inv chord edges noCycle 3 [(2,13),(1,21),(0,12)] [7]
    #[1,1,1,1,1,36965,1216614,1,1245815014,44299392131,1382112431433,1074859372,1,1,1117645,1100656130476,1788700728162904118403,54801072858441502017039,1792631938554470940658224,1799982145,1246665439373670668176449,1,1293615081694216119030,1109515989,1676906932652722610274,68206500293684365833283,2221605616482242583278659,1366174235277288692183907,1134943989858,37649154013,1107233857,2283787536850830299134] (by decide) (by decide +kernel) (partnerCons r9 (by simp))
  have r11 := row32 D mate inv chord edges noCycle 2 [(1,21),(0,12)] [6,13]
    #[1,1,1,1,35908,1182789,1,1211178181,43191013474,1346644314408,1488259104,2377596044819613434097695,1,1,1490487328,1750617127494600527970,53582397637055787123182,1753634331470128064054799,1799997505,2416593651903956966279200,75518551621998655178784,1,1084117,52442346623501408634912,1903907874,62033450018,2020538536994,1133835611201,36541823932,2146338848,1334154526637977237571,1082338] (by decide) (by decide +kernel) (partnerCons r8 (partnerCons r10 (by simp)))
  have r12 := row32 D mate inv chord edges noCycle 4 [(3,7),(1,22),(0,12)] []
    #[1,1,35908,1,1,1,38022,1,1151239,1280451847,45407770788,1417580548458,1,38757499277,1594909296740,64550474629516208868417,2017202332160604998721,1826784328831207708836,56019748079827216910896,1831629545638813817261649,35503887030,1247884114595056383070306,1,1331697556462612866839,1247884114595055727221858,75518551621291580950560,2359954737444915611680,2210077306077482064996,2019659338639745453121,1169338365059,38757499902,1108316258] (by decide) (by decide +kernel) (by simp)
  have r13 := row32 D mate inv chord edges noCycle 3 [(1,22),(0,12)] [7]
    #[1,1,1,1,1,36965,1216614,1,1245815014,44299392131,1382112431433,1074859372,1,1176535437,49840915523,1100656130476,1788700728162904118403,54801072858441502017039,1792631938554470940658224,58708298817,1246665439373670668176449,38958294980427208363073,1,1678155091952045076351008,1836846145,58779798593,1136147620598,1366174235277288692183907,1134943989858,37649154013,1107233857,1324686836017815880118303] (by decide) (by decide +kernel) (partnerCons r12 (by simp))
  have r14 := row32 D mate inv chord edges noCycle 1 [(0,12)] [5,10,21,22]
    #[1,1,1,34851,1148964,1,1176541348,42082634817,1311176197383,1488266272,1,1453088,1,1455136,1712533526826296937537,52363722415670072229325,1714636724385785187451374,1526273164320,2377596044819614089675807,74299876400612940284959,1218636830659234749108,1,1,2055285932841029251073,66987825072298650939393,2182608009397899706675201,2197879121952,35466999707,2111702047,1327176628192958769755170,1081281,33761] (by decide) (by decide +kernel) (partnerCons r6 (partnerCons r7 (partnerCons r11 (partnerCons r13 (by simp)))))
  exact r14

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem partner16 (D : SimpleGraph (Fin 32)) (mate : Fin 32 → Fin 32)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 32).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 32).Adj i j ∨ j = mate i)
    (noCycle : ¬ ∃ m ∈ [3,4,6,7,8,14,15,16], cycleGraph m ⊑ D) :
    ¬ (∀ e ∈ ([(0,16)] : List (Fin 32 × Fin 32)), mate e.1 = e.2) := by
  have r0 := row32 D mate inv chord edges noCycle 5 [(2,25),(3,11),(0,16)] []
    #[1,1372238127306293886977,1,1,1,1,1,39079,1284264,1245818185,1315088680,1,1453048665483,1178776971,37720896907,1100655760880,1,1275708080657,1864867929499511299269,57238423301212931804753,1870627152723156693865074,1600739731316115412099,1285701130058681848370307,40178160314333807744131,1369781121946544368440,1,1245809466,36612271961,46348970187356592074918,1218636804627925118050,1204772927652,39865877535] (by decide) (by decide +kernel) (by simp)
  have r1 := row32 D mate inv chord edges noCycle 4 [(1,10),(2,30),(3,11),(0,16)] []
    #[1,1,1,1,1,1,38022,1250439,43262183524,1280451847,1,1,1421443,1136124146026,1455863939,46587657347,1,1826784328831207708836,56019748079827216910896,1831629545638813817261649,2321871137519154368610,1247884114595056383070306,38996378581095511953506,1331697556462612866839,1639157484867702200459395,1246665439372963594118465,2162410983522,36612993982,2111705186,1169338365059,1,1108316258] (by decide) (by decide +kernel) (by simp)
  have r2 := row32 D mate inv chord edges noCycle 1 [(2,30),(3,11),(0,16)] [10]
    #[1,1,1,1,1148964,2163590991970,1176541348,42082634817,1311176197383,1109503305,1,1,45130295294760321092741,1366174235277301612804163,1712533526826296937537,52363722415670072229325,1,1050160,2377596044819614089675807,74299876400612940284959,1218636830659234749108,1843197952001,64550474629527221144641,1639157484867702200435779,2323155464781879304226,2162411004962,2197879121952,35466999707,2111702047,2029633,1,33761] (by decide) (by decide +kernel) (partnerCons r1 (by simp))
  have r3 := row32 D mate inv chord edges noCycle 2 [(3,11),(0,16)] [25,30]
    #[1,1,1,1,35908,1182789,1313464462434,1211178181,43191013474,1346644314408,1387618,1,1453154,48804397090,1557539938,1750617127494600527970,1,1753634331470128064054799,1074874928,2416593651903956966279200,75518551621998655178784,1255567509822931492565,2017202332172725660770,65769149850912936045666,1639157484867702200459331,1,2169536734845940006946,1133835611201,36541823932,2146338848,1,1082338] (by decide) (by decide +kernel) (partnerCons r0 (partnerCons r2 (by simp)))
  have r4 := row32 D mate inv chord edges noCycle 31 [(1,25),(3,12),(0,16)] []
    #[1,1,1082338,1,1108316258,39865877535,1240239996101,2283787510819541164030,73081200346225317225470,2377596043986612181508415,1455326037023,37649153388,1,49926371972898643490187,1636641510217099435293100,2064911,1,71862525957841510531037,2359954738187457974898,1730723871,56491556895,1668145633248,35466731289,1871479839,2126942888958,1,2042462173,2007794719,2062239,64447,1,1] (by decide) (by decide +kernel) (by simp)
  have r5 := row32 D mate inv chord edges noCycle 1 [(3,12),(0,16)] [25]
    #[1,1,1,1,1148964,1372238127306293886977,1176541348,42082634817,1311176197383,35504139593,1421216833,1665857367072,1,1525137409,1712533526826296937537,52363722415670072229325,1,1050160,2377596044819614089675807,74299876400612940284959,1218636830659234749108,1843197952001,2017202332172725652545,52442346623501408633923,2143610402313556830063681,1,2197879121952,35466999707,2111702047,1834145520289416583476256,1081281,33761] (by decide) (by decide +kernel) (partnerCons r4 (by simp))
  have r6 := row32 D mate inv chord edges noCycle 13 [(2,25),(3,23),(0,16)] []
    #[1,1525137409,1,1,2182608009397899706667106,2055285932841029244035,1488516782508,48732906759,1418999179,1522115523484779560397,1453389,45421,1,1,1,47535,1,1210183806939930557822512,1592183344,55383178701,1736793601683,1296070925969686714071,38958294980427208112624,1,1674449926157993347896,1,2169536734845940022733,66987825072298650955609,2182608009397899706692474,2129197022669,1597643903132756592244107,49926371972898643490187] (by decide) (by decide +kernel) (by simp)
  have r7 := row32 D mate inv chord edges noCycle 5 [(4,8),(2,30),(3,23),(0,16)] []
    #[1,2359954738187437478944,1,1,1,1,1,39079,1,1185064,1315088680,46516149445,1453048665483,1384400696484,2104612795229213678608515,1100655760880,1,1275708080657,1864867929499511299269,57238423301212931804753,1870627152723156693865074,2026617581060528200261765,1285701130058681848370307,1,1369781121946544368440,1285701130058681192521859,39866590010,1275730880347,67574599778,1144133566,1,39865877535] (by decide) (by decide +kernel) (by simp)
  have r8 := row32 D mate inv chord edges noCycle 1 [(4,13),(2,30),(3,23),(0,16)] []
    #[1,1,1,1,1,2359954738187437478944,1176541348,42082634817,1311176197383,43911619747883784845732,1136124146026,38757510541,1109496236,1,1712533526826296937537,52363722415670072229325,1,1050160,2377596044819614089675807,74299876400612940284959,1218636830659234749108,1843197952001,1676906932652721866852,1,2143610402313556829801537,2162411004962,2197879121952,35466999707,2111702047,2029633,1,33761] (by decide) (by decide +kernel) (by simp)
  have r9 := row32 D mate inv chord edges noCycle 4 [(2,30),(3,23),(0,16)] [8,13]
    #[1,1148964,1,1,1,1,38022,1250439,1,1280451847,45407770788,1417580548458,2055285932841029251203,1,1100655770096,38757499407,1,1826784328831207708836,56019748079827216910896,1831629545638813817261649,1869271171,1247884114595056383070306,38996378581095511953506,1,1151767,57317047509044244351008,1973181540,64250207332,2091474771044,1169338365059,1,1108316258] (by decide) (by decide +kernel) (partnerCons r7 (partnerCons r8 (by simp)))
  have r10 := row32 D mate inv chord edges noCycle 2 [(3,23),(0,16)] [25,30]
    #[1,1,1,1,35908,1182789,1246665439373670012328001,1211178181,43191013474,1346644314408,1600159877783359323855970,51223671402115693763682,1638823331984419019874,48804397090,1141916142,1750617127494600527970,1,1753634331470128064054799,1914134186051,2416593651903956966279200,75518551621998655178784,1255567509822931492565,1117942,1,1149719,1,1871505475,1133835611201,36541823932,2146338848,1,1082338] (by decide) (by decide +kernel) (partnerCons r6 (partnerCons r9 (by simp)))
  have r11 := row32 D mate inv chord edges noCycle 2 [(13,25),(3,24),(0,16)] []
    #[1,1,1,1,35908,1182789,74299876399905866056735,1211178181,43191013474,1346644314408,1255567509822931120490,1639157484867702200459362,52442346623501408657506,1,1141916142,1750617127494600527970,1,1753634331470128064054799,1074874928,2416593651903956966279200,75518551621998655178784,1255567509822931492565,1288179021108616311399158,1826914,1,1,2169536734845940006946,1133835611201,36541823932,2146338848,2358953704212219381248,1082338] (by decide) (by decide +kernel) (by simp)
  have r12 := row32 D mate inv chord edges noCycle 13 [(3,24),(0,16)] [25]
    #[1,1525137409,48804397090,1,2093369533509332841603,66987825072298650932355,1488516782508,48732906759,1418999179,1522115523484779560397,1453389,45421,1,1,1,47535,1,1210183806939930557822512,1592183344,55383178701,1736793601683,53582397637055787851477,1296070925969686715128,1217446718138349959664,1,1,2169536734845940022733,66987825072298650955609,2182608009397899706692474,2129197022669,1597643903132756592244107,49926371972898643490187] (by decide) (by decide +kernel) (partnerCons r11 (by simp))
  have r13 := row32 D mate inv chord edges noCycle 2 [(1,22),(3,27),(0,16)] []
    #[1,1,1,1,35908,1182789,1410321727974597460002,1211178181,43191013474,1346644314408,64550474629527221151809,2017202332172725660737,1665857357856,48804397090,2260603223566585459882051,1750617127494600527970,1,1753634331470128064054799,58708314177,2416593651903956966279200,75518551621998655178784,1255567509822931492565,1,1793089,2007818307,1836868673,1118074,1,36541823932,2146338848,2111728738,1082338] (by decide) (by decide +kernel) (by simp)
  have r14 := row32 D mate inv chord edges noCycle 1 [(3,27),(0,16)] [22]
    #[1,1,1,1,1148964,1372238127306293886977,1176541348,42082634817,1311176197383,2359954712156148343840,75518550788996747012128,1665857367072,47696035841,1525137409,1712533526826296937537,52363722415670072229325,1,1050160,2377596044819614089675807,74299876400612940284959,1218636830659234749108,1843197952001,1,2056006632515,37649934171,1940753473,2197879121952,1,2111702047,1834145520289416583476256,1081281,33761] (by decide) (by decide +kernel) (partnerCons r13 (by simp))
  have r15 := row32 D mate inv chord edges noCycle 3 [(0,16)] [11,12,23,24,27]
    #[1,34851,1,1,1,36965,1216614,1448405328642900493379,1245815014,44299392131,1382112431433,1,1,1665857062944,37649138158,1176535567,1,54801072858441502017039,1792631938554470940658224,1100656265776,1246665439373670668176449,38958294980427208363073,1293615081694216119030,1,1,1791157734657632602144,57317047509044267419680,1,1134943989858,37649154013,1107233857,1831629545638813817245664] (by decide) (by decide +kernel) (partnerCons r3 (partnerCons r5 (partnerCons r10 (partnerCons r12 (partnerCons r14 (by simp))))))
  exact r15

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem partner20 (D : SimpleGraph (Fin 32)) (mate : Fin 32 → Fin 32)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 32).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 32).Adj i j ∨ j = mate i)
    (noCycle : ¬ ∃ m ∈ [3,4,6,7,8,14,15,16], cycleGraph m ⊑ D) :
    ¬ (∀ e ∈ ([(0,20)] : List (Fin 32 × Fin 32)), mate e.1 = e.2) := by
  have r0 := row32 D mate inv chord edges noCycle 1 [(11,2),(10,14),(21,9),(0,20)] []
    #[1,1,1,34851,1148964,1987619973976185048798240,1176541348,42082634817,1311176197383,1,1,1,1453121,1557170538,1,52363722415670072229325,1714636724385785187451374,1765360672,2377596044819614089675807,74299876400612940284959,1,1,2017202332172725660737,1869271041,60925071361,1985070419969,2197879121952,35466999707,2111702047,1639157484867701505487906,1081281,33761] (by decide) (by decide +kernel) (by simp)
  have r1 := row32 D mate inv chord edges noCycle 11 [(10,14),(21,9),(0,20)] [2]
    #[1,1407864721872305595655,1,1600739731316114719811,1417580548458,46516149445,1349725513,1676906932652708470124,1385739,1,1,1,1,45421,1,1388014,1522909678,53166421387,1665857367633,1597209398634,1,1,37818243966872829942452,1802218825,2093369533509332841867,64550474629527221167895,2104612795229213953485624,2260603223566585459882315,1519648688964106272517449,47489021530128320998729,1598282724821386167294,1519648688964105616669001] (by decide) (by decide +kernel) (partnerCons r0 (by simp))
  have r2 := row32 D mate inv chord edges noCycle 8 [(1,5),(10,31),(21,9),(0,20)] []
    #[1,1,43191013474,1245815014,1136123976901,1,40136,1,1,1,1,1385739,1675665299776901769549096,1418999179,49841285416,1559453016558,1668145632552,53237929256,1698321704,1951138341542445213264168,1,1,60894448965370076486324,1987619973976185323675349,1802232073,1402655868873261433266406,43832995902289419772134,1484031922816510031771,45408483295,2079303976,1134943280325,1] (by decide) (by decide +kernel) (by simp)
  have r3 := row32 D mate inv chord edges noCycle 1 [(10,31),(21,9),(0,20)] [5]
    #[1,1,1,34851,1148964,1,1176541348,42082634817,1311176197383,1,1,2029133555711130931866953,2113974634,67647222122,1712533526826296937537,52363722415670072229325,1714636724385785187451374,1765360672,2377596044819614089675807,74299876400612940284959,1,1,1600159877783359323833375,1869271041,60925071361,1985070419969,2197879121952,35466999707,2111702047,2341088229910414520602625,1081281,1] (by decide) (by decide +kernel) (partnerCons r2 (by simp))
  have r4 := row32 D mate inv chord edges noCycle 10 [(21,9),(0,20)] [14,31]
    #[1,38996378581095511971114,1285701130058681848386858,1382112431433,45407770788,1315088680,1678155091952044624550219,1351914,42250,1,1,1,44364,1453389,1,1488272845,52058042730,1630389250608,1799997769,2107128769879781907179190,1,1,1759561,2055285932841029251434,63331799408141506274038,2065615188144871076882199,1845486217545,1480651081880862907541800,46270346308776965843240,1560199124153082609629,1562656130647811818494,1] (by decide) (by decide +kernel) (partnerCons r1 (partnerCons r3 (by simp)))
  have r5 := row32 D mate inv chord edges noCycle 24 [(23,27),(21,10),(0,20)] []
    #[1,60925071361,1169326529272,49926371972923098259157,1560199124176430030549,1369781121946544368440,41395682614214915791012,1363658297817715575626949,57671426346,2026617581060528200278774,1,2093369533509332841867,2026617581060528652775158,60894448965797981969076,1902951530560252271284,1753074133277679185656,1562656130655570484949,1878666069783,60925071986,1800004342,1,1,57048,1,1,1,59162,1,1827739,1973188507,67575343928,2126942888958] (by decide) (by decide +kernel) (by simp)
  have r6 := row32 D mate inv chord edges noCycle 23 [(21,10),(0,20)] [27]
    #[1,1869271041,36541454039,1810017388576,1331697556462612866839,40178160314333807744131,1324661843654877305870500,45407788757,1987619973976185323675349,62113124186755791380181,1,1210183806939930558192308,1421237973,45479288533,1845475324266,2146126376963045604246007,1843197952758,59816693329,1765367509,2104600894104005108597395,1,1,1,1,1,58105,1893114,1,1938551674,66466965271,2091474771933,1767596000] (by decide) (by decide +kernel) (partnerCons r5 (by simp))
  have r7 := row32 D mate inv chord edges noCycle 18 [(19,15),(22,1),(21,25),(0,20)] []
    #[1,1,1288179021108616311029362,1792631938554470940658224,56019748079827216910896,1864867929499511299269,1826790214885004416210,1181820123965120069236,37818243966873139428980,1210183806939930832682612,1630389250643,1665857367633,54274800044,1592183344,1523314,1,50706,1,1,1,1,1,1,1765367509,60925071986,1,1799998297,62104620693,1739060149180,54345629661,2029133555711130513981044,2359954738187457974898] (by decide) (by decide +kernel) (by simp)
  have r8 := row32 D mate inv chord edges noCycle 19 [(22,1),(21,25),(0,20)] [15]
    #[1,1,2416593651903956966279200,1074859636,1831629545638813817261649,57238423301212931804753,1902951530167814889702,1445948322172627637907,47489021530151668471443,1558646296048438136854163,1560199124153083319955,1181820123964775935604,1701325484658,55383178701,1626820177,1,1656339,51763,1,1,1,1,1,1732962071,1800004342,1,1949602303833,2058294887059,65430061715,2079294099,1774549238782,35466629814] (by decide) (by decide +kernel) (partnerCons r7 (by simp))
  have r9 := row32 D mate inv chord edges noCycle 10 [(23,7),(22,13),(21,25),(0,20)] []
    #[1,65847774058743164380423,1941035130836118472736,1382112431433,45407770788,1315088680,2104612795229213953468615,1,42250,1,1,1,44364,1,1714990533321025626410,1488272845,52058042730,1630389250608,1181820123964775942772,1455337199251,1,1,1,1,63331799408141506274038,1,1348933084951,1480651081880862907541800,46270346308776965843240,1560199124153082609629,1562656130647811818494,2019659338667454180749] (by decide) (by decide +kernel) (by simp)
  have r10 := row32 D mate inv chord edges noCycle 23 [(22,13),(21,25),(0,20)] [7]
    #[1,1869271041,36541454039,2210077305689641539386,1331697556462612866839,40178160314333807744131,1324661843654877305870500,1,1987619973976185323675349,62113124186755791380181,2055285932841029251434,1902951530167829030580,1825196,1,1793485,2146126376963045604246007,1843197952758,59816693329,1765367509,1732962071,1,1,1,1,1,1,1893114,1802235737,1938551674,66466965271,2091474771933,1767596000] (by decide) (by decide +kernel) (partnerCons r9 (by simp))
  have r11 := row32 D mate inv chord edges noCycle 18 [(23,7),(22,14),(21,25),(0,20)] []
    #[1,2377596044819614089675807,1765345312,1792631938554470940658224,56019748079827216910896,1864867929499511299269,1739081866470,1,1914134186247,1524572530227784897138,1181820123964775942772,1665857367633,54274800044,1592183344,1,1622514,50706,1,1,1,1,1,1,1,60925071986,1,1799998297,62104620693,1739060149180,54345629661,2112901746,2359954738187457974898] (by decide) (by decide +kernel) (by simp)
  have r12 := row32 D mate inv chord edges noCycle 23 [(22,14),(21,25),(0,20)] [7]
    #[1,1869271041,36541454039,2210077305689641539386,1331697556462612866839,40178160314333807744131,1324661843654877305870500,1,1987619973976185323675349,62113124186755791380181,2055285932841029251434,1902951530167829030580,1985059666645,1825229,1,1793518,1843197952758,59816693329,1765367509,1772261718743,1,1,1,1,1,1,1893114,1802235737,1938551674,66466965271,2091474771933,1767596000] (by decide) (by decide +kernel) (partnerCons r11 (by simp))
  have r13 := row32 D mate inv chord edges noCycle 22 [(21,25),(0,20)] [1,13,14]
    #[1,1,1074879156,1293615081694216119030,38996378581095511953506,1285701130058681848370307,1441653474831704403044022,1948622366891842447071924,60894448965370076486324,2017202332172725661001,1948622366891842899568308,58457098523026552181362,1826784329223645090418,1,1,1807729835733,58708314672,1730730676,2095826540002974223063,1757814,1,1,1,1,57048,1,1760089,1903914841,65358586614,2056006654908,1987358685909,1133560751796] (by decide) (by decide +kernel) (partnerCons r8 (partnerCons r10 (partnerCons r12 (by simp))))
  have r14 := row32 D mate inv chord edges noCycle 31 [(21,30),(0,20)] []
    #[1,33761,1082338,2338598437735270557224958,1108316258,39865877535,1240239996101,1483167056530330694045727,47567645737958549082143,1524572529979508248607,1562656130647811839967,1288179021108616966623233,1636366325489689756703,49926371972898643490187,1636641510217099435293100,1807729836000,2299600830650928336502749,71862525957841510531037,2359954738187457974898,2065043,1,1,2064085,1767596000,2126942888958,68683722585,2042462173,1810292961248,2062239,64447,1,1] (by decide) (by decide +kernel) (by simp)
  have r15 := row32 D mate inv chord edges noCycle 21 [(0,20)] [9,10,25,30]
    #[1,1050292,1255567509822931492565,38958294980427208363073,1247884114595056383070306,1100655761076,1909624759807499570468499,59675773743984361592467,1979118731504422070568,1,1,1598282724821386166933,52363722415670072214165,1714636724385785187435157,1772261718708,57599936015,1696093843,2107128769879781907449526,1723989,53877,1,1,1,55991,1825464,1,1869278008,64250207957,2020538537883,1107261108,1,1081012] (by decide) (by decide +kernel) (partnerCons r4 (partnerCons r6 (partnerCons r13 (partnerCons r14 (by simp)))))
  exact r15

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem partner21 (D : SimpleGraph (Fin 32)) (mate : Fin 32 → Fin 32)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 32).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 32).Adj i j ∨ j = mate i)
    (noCycle : ¬ ∃ m ∈ [3,4,6,7,8,14,15,16], cycleGraph m ⊑ D) :
    ¬ (∀ e ∈ ([(0,21)] : List (Fin 32 × Fin 32)), mate e.1 = e.2) := by
  have r0 := row32 D mate inv chord edges noCycle 12 [(9,17),(10,6),(0,21)] []
    #[1,47489021530140584690217,1484031922828739068457,45478940838,1280455018,1453048665483,1,1384362346,1526273164584,1,1,1,1,1,46478,1521039,1488266800,1,54274800044,1701325484658,37818243966872829932181,1,52363722415670072214198,1210183806939930557832917,66987825072290892294508,2131453134177636432300,65769149850912936061752,2143610402313556830089049,1407864721515336315242,1558646296048414789382506,48707696751512962150762,1636366325489689756703] (by decide) (by decide +kernel) (by simp)
  have r1 := row32 D mate inv chord edges noCycle 8 [(9,29),(10,6),(0,21)] []
    #[1,1311176197383,43191013474,1245815014,1213409576,1284264,1,1,1,1,1,1385739,1282683242,1418999179,49841285416,1559453016558,1834145520289416583476520,58535722730429983126824,1867324935994240562472,1444181350571196662314282,1638823331984404879691,1,60894448965370076486324,1987619973976185323675349,2126942888201,1402655868873261433266406,43832995902289419772134,1484031922816510031771,1331697556462592370885,1,1352669,1522164663614673570649119] (by decide) (by decide +kernel) (by simp)
  have r2 := row32 D mate inv chord edges noCycle 9 [(10,6),(0,21)] [17,29]
    #[1,1311176197418,1346644314408,44299392131,1280451847,1218889,1,41193,1,1,1,43307,1419564,1313464562026,1453636012,50949664073,1594921133583,1,1522115523484779729522,1714990532928588819853,54879697065844932947341,1,2017202332172725661001,62113124186755791380181,2026617581060528200278774,2185123984012183121074505,1441653474831704403027207,45051671088490762577159,1522115523484780067772,1,1561162270699016447230974,48786320959344263975967] (by decide) (by decide +kernel) (partnerCons r0 (partnerCons r1 (by simp)))
  have r3 := row32 D mate inv chord edges noCycle 11 [(10,14),(0,21)] []
    #[1,1407864721872305595655,1979118731504422062112,51223671402115693020227,1417580548458,46516149445,1349725513,1348932679051,1385739,43307,1,1,1,45421,1,1388014,1522909678,53166421387,1665857367633,1597209398634,1181820123964775935637,1,1181820123964775935701,51145047194284357342935,2093369533509332841867,64550474629527221167895,2104612795229213953485624,2260603223566585459882315,1519648688964106272517449,47489021530128320998729,1598282724821386167294,1519648688964105616669001] (by decide) (by decide +kernel) (by simp)
  have r4 := row32 D mate inv chord edges noCycle 9 [(8,19),(11,27),(10,20),(0,21)] []
    #[1,1247884114595056383086921,1346644314408,44299392131,1280451847,53661021844459218053484,1318089,41193,1,1,1,1,1419564,1638635415658031803243,1453636012,50949664073,1594921133583,1663684937,1689896,1,1,1,2017202332172725661001,62113124186755791380181,2026617581060528200278774,1985070420297,1441653474831704403027207,1,1522115523484780067772,2077076809,67575328073,48786320959344263975967] (by decide) (by decide +kernel) (by simp)
  have r5 := row32 D mate inv chord edges noCycle 8 [(11,27),(10,20),(0,21)] [19]
    #[1,1311176197383,43191013474,1245815014,1331697556462612359464,1284264,40136,1,1,1,1,1,2263119161026171948474763,1418999179,49841285416,1559453016558,1668145621288,53237917992,1351963250,1,1,1,60894448965370076486324,1987619973976185323675349,1384401201976,1402655868873261433266406,43832995902289419772134,1,1351954300,43262537629,1488517560219,1522164663614673570649119] (by decide) (by decide +kernel) (partnerCons r4 (by simp))
  have r6 := row32 D mate inv chord edges noCycle 11 [(10,20),(0,21)] [27]
    #[1,1990135948626788088808810,1979118731504422062112,51223671402115693020227,1417580548458,46516149445,1349725513,1753074133596892410286,1385739,43307,1,1,1,45421,1487214,1632677515595,1522909678,53166421387,1665857367633,1723754,1,1,1181820123964775935701,1767595370,2093369533509332841867,64550474629527221167895,2104612795229213953485624,1,1519648688964106272517449,47489021530128320998729,1598282724821386167294,1943492137330847743338] (by decide) (by decide +kernel) (partnerCons r5 (by simp))
  have r7 := row32 D mate inv chord edges noCycle 18 [(19,15),(10,22),(0,21)] []
    #[1,2377596044819614089675807,57599920160,1792631938554470940658224,56019748079827216910896,1864867929499511299269,1181820123976896597653,37818243966883842215573,1384412533362,54346307913,1,1665857367633,54274800044,1592183344,1523314,1,50706,1,1,1,52820,1,1,1765367509,60925071986,1914134186808,1217446718130591616661,2207620335126382591602,2057742938943321133750,65847774058316366992054,2029133555711130513981044,2359954738187457974898] (by decide) (by decide +kernel) (by simp)
  have r8 := row32 D mate inv chord edges noCycle 19 [(10,22),(0,21)] [15]
    #[1,74299876400612940284959,2416593651903956966279200,34395508373,1831629545638813817261649,57238423301212931804753,1902951530167814889702,1348932949651,43262891667,1732958537,1,1834634602,1701325484658,55383178701,1626820177,1,1656339,51763,1,1,1,1,1,1951112159066985754569431,1800004342,62033450643,1949602303833,1909624759807514050882419,1843208846304,35432353429,1732936702,2380112019470216856295059] (by decide) (by decide +kernel) (partnerCons r7 (by simp))
  have r9 := row32 D mate inv chord edges noCycle 3 [(2,13),(11,1),(10,26),(0,21)] []
    #[1,1,1,1,1,36965,1216614,1348932568131,1245815014,44299392131,1,1,1486946,1,49841275971,1136135714187,1788700728162904118403,54801072858441502017039,1792631938554470940658224,34395508373,1246665439373670668176449,1,1293615081694216119030,57670731808,1676906932652722610274,68206500293684365833283,1,1246665438540668760009057,1134943989858,37649154013,1107233857,70643850735748722457532] (by decide) (by decide +kernel) (by simp)
  have r10 := row32 D mate inv chord edges noCycle 2 [(11,1),(10,26),(0,21)] [13]
    #[1,1,1,1,35908,1182789,1313464462370,1211178181,43191013474,1346644314408,1,1,1421377,1,1455863873,1750617127494600527970,53582397637055787123182,1753634331470128064054799,57599920160,2416593651903956966279200,75518551621998655178784,1,1600739731316115429441,1802209312,57671419936,1100679503573,1,1133835611201,36541823932,2146338848,1410321727583267392645,1082338] (by decide) (by decide +kernel) (partnerCons r9 (by simp))
  have r11 := row32 D mate inv chord edges noCycle 11 [(10,26),(0,21)] [1]
    #[1,1,1979118731504422062112,51223671402115693020227,1417580548458,46516149445,1349725513,2224121589970626090835306,1385739,43307,1,1,1,45421,1487214,1753074133989329791307,1522909678,53166421387,1665857367633,37818243966872829939349,1181820123964775935637,1,1181820123964775935701,1871505739,2093369533509332841867,64550474629527221167895,1,1388410,1519648688964106272517449,47489021530128320998729,1598282724821386167294,2197879122251] (by decide) (by decide +kernel) (partnerCons r10 (by simp))
  have r12 := row32 D mate inv chord edges noCycle 10 [(0,21)] [6,14,20,22,26]
    #[1,1979118731504422070304,63331799408141506250784,1382112431433,45407770788,1315088680,1,1351914,42250,1,1,1,44364,1453389,1,1488272845,52058042730,1630389250608,49926371972898643169906,1181820123964775943829,1,1,1,2055285932841029251434,63331799408141506274038,2065615188144871076882199,1,1480651081880862907541800,46270346308776965843240,1560199124153082609629,50004996180729978848254,1562656130647811839007] (by decide) (by decide +kernel) (partnerCons r2 (partnerCons r3 (partnerCons r6 (partnerCons r8 (partnerCons r11 (by simp))))))
  exact r12

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem partner22 (D : SimpleGraph (Fin 32)) (mate : Fin 32 → Fin 32)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 32).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 32).Adj i j ∨ j = mate i)
    (noCycle : ¬ ∃ m ∈ [3,4,6,7,8,14,15,16], cycleGraph m ⊑ D) :
    ¬ (∀ e ∈ ([(0,22)] : List (Fin 32 × Fin 32)), mate e.1 = e.2) := by
  have r0 := row32 D mate inv chord edges noCycle 9 [(10,18),(11,7),(0,22)] []
    #[1,1561162270699016447252481,1346644314408,44299392131,1280451847,1248046409,1318089,1,1,1,1,1,1419564,1561741281609,1453636012,50949664073,1594921133583,1624393,1,1689929,1348943333707,1676906932652708470124,1,62113124186755791380181,2026617581060528200278774,1522115523484779765529,1441653474831704403027207,45051671088490762577159,1522115523484780067772,1369781121946523872486,74299876400612940302665,1561162270699016447252511] (by decide) (by decide +kernel) (by simp)
  have r1 := row32 D mate inv chord edges noCycle 10 [(11,7),(0,22)] [18]
    #[1,50004996180729978869761,1346644314443,1382112431433,45407770788,1315088680,1252714,1,42250,1,1,1,44364,1453389,1348932679051,1488272845,52058042730,1630389250608,1,49926371972898643203731,1753074133596892410286,56098372287230647841198,1,2055285932841029251434,63331799408141506274038,2065615188144871076882199,2224121589970626090835306,1480651081880862907541800,46270346308776965843240,1560199124153082609629,1600159877783359323833342,64550474629527221152736] (by decide) (by decide +kernel) (partnerCons r0 (by simp))
  have r2 := row32 D mate inv chord edges noCycle 9 [(12,4),(11,15),(0,22)] []
    #[1,1561162270699016447252481,1346644314408,44299392131,1,1386590341,1318089,41193,1,1,1,1,1,1417580548493,1453636012,1,1594921133583,1453639183,46516487695,1676906932640458937484,53661021844873751499916,1717152699036373473236108,1,62113124186755791380181,2026617581060528200278774,1753074133989329773899,1441653474831704403027207,45051671088490762577159,1522115523484780067772,73158635274545436011849,2323138031500757806409,1561162270699016447252511] (by decide) (by decide +kernel) (by simp)
  have r3 := row32 D mate inv chord edges noCycle 12 [(11,15),(0,22)] [4]
    #[1,46270346309169403242792,1445948322540609186088,52442346623501407880259,1,1453048665483,47624528102,1384362346,1384400796076,1419564,44364,1,1,1,46478,1,1421839,1557546511,54274800044,1701325484658,1632677515659,52363722415670072214229,1,37818243966872829932278,1675639117301442310855416,2131453134177636432300,65769149850912936061752,2143610402313556830089049,2299600830650928336485740,1558646296048414789382506,48707696751512962150762,1636366325489689756703] (by decide) (by decide +kernel) (partnerCons r2 (by simp))
  have r4 := row32 D mate inv chord edges noCycle 26 [(24,15),(11,27),(0,22)] []
    #[1,2197879121952,2020538515490,1792631938554470940666680,56019748079827216919352,1372238127306293895994,1313464463226,1445948322149280183162,43832995902289419772134,1441653474831704403027207,1388410,1,65769149850912936061752,2169536734845940022733,1557540730,1,1490805048155,1906132495,63141560882,1949602303833,63141829300,1869278008,1,1893114,1,1,1,1,61276,1994589,1636641510217099435309915,2042462173] (by decide) (by decide +kernel) (by simp)
  have r5 := row32 D mate inv chord edges noCycle 24 [(11,27),(0,22)] [15]
    #[1,51145047194284358133595,1836845088,37649144568,1880931534880,1369781121946544368440,41395682614214915791012,1363658297817715575626949,1384401201976,2026617581060528200278774,63331799408141506274038,1,1906142572,60996562317,2056006350219,1,2026617581389745550752790,1878666069783,60925071986,1800004342,1941035130836119055160,1825464,1,1,1,1,59162,1,1639157484867702200460187,1973188507,67575343928,2126942888958] (by decide) (by decide +kernel) (partnerCons r4 (by simp))
  have r6 := row32 D mate inv chord edges noCycle 11 [(0,22)] [7,15,27]
    #[1,2017202332172725660704,51223671402115693740066,1639157484867702199682115,1417580548458,46516149445,1349725513,1,1385739,43307,1,1,1,45421,1487214,1,1522909678,53166421387,1665857367633,1636641510217099435005587,51145047194284357343924,1598282724821386166997,1,1181820123964775935734,2093369533509332841867,64550474629527221167895,2104612795229213953485624,1,1519648688964106272517449,47489021530128320998729,1598282724821386167294,2017202332172725661664] (by decide) (by decide +kernel) (partnerCons r1 (partnerCons r3 (partnerCons r5 (by simp))))
  exact r6

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem partner23 (D : SimpleGraph (Fin 32)) (mate : Fin 32 → Fin 32)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 32).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 32).Adj i j ∨ j = mate i)
    (noCycle : ¬ ∃ m ∈ [3,4,6,7,8,14,15,16], cycleGraph m ⊑ D) :
    ¬ (∀ e ∈ ([(0,23)] : List (Fin 32 × Fin 32)), mate e.1 = e.2) := by
  have r0 := row32 D mate inv chord edges noCycle 5 [(1,25),(2,18),(11,3),(0,23)] []
    #[1,1,1,1,1,1,1,39079,1284264,1245818185,1315088680,1,1453048665483,1178776971,37720896907,1736793296994,39865895472,1245809233,1,57238423301212931804753,1870627152723156693865074,1171592499826,1285701130058681848370307,1,1369781121946544368440,1,35503871833,1136123899737,46348970187356592074918,1218636804627925118050,1204772927652,39865877535] (by decide) (by decide +kernel) (by simp)
  have r1 := row32 D mate inv chord edges noCycle 1 [(2,18),(11,3),(0,23)] [25]
    #[1,1,1,1,1148964,1909624759807499570451490,1176541348,42082634817,1311176197383,1109503305,2104612795229213953468448,1,1638823331984419019777,1561741281345,1712533526826296937537,52363722415670072229325,1714636724385785187451374,1083985,1,74299876400612940284959,1218636830659234749108,1799997505,1082102,1,1050391,1,2197879121952,35466999707,2111702047,2283787536850850793537,1081281,33761] (by decide) (by decide +kernel) (partnerCons r0 (by simp))
  have r2 := row32 D mate inv chord edges noCycle 1 [(2,30),(11,3),(0,23)] []
    #[1,1,1,1,1148964,2163590991970,1176541348,42082634817,1311176197383,1109503305,2104612795229213953468448,1,45130295294760321092741,1366174235277301612804163,1712533526826296937537,52363722415670072229325,1714636724385785187451374,1873143127373759460079681,2377596044819614089675807,74299876400612940284959,1218636830659234749108,1979118731504422063169,1082102,1,1050391,2162411004962,2197879121952,35466999707,2111702047,2029633,1,33761] (by decide) (by decide +kernel) (by simp)
  have r3 := row32 D mate inv chord edges noCycle 2 [(11,3),(0,23)] [18,30]
    #[1,1,1,1,35908,1182789,1313464462434,1211178181,43191013474,1346644314408,1387618,1,1453154,1676906932652722585634,1557539938,1750617127494600527970,53582397637055787123182,1753634331470128064054799,1,2416593651903956966279200,75518551621998655178784,1255567509822931492565,2017202332172725660770,1,1639157484867702200459331,1074882327,36541555514,1133835611201,36541823932,2146338848,1,1082338] (by decide) (by decide +kernel) (partnerCons r1 (partnerCons r2 (by simp)))
  have r4 := row32 D mate inv chord edges noCycle 8 [(10,30),(12,16),(11,7),(0,23)] []
    #[1,1311176197383,43191013474,1245815014,1242528327976,1284264,40136,1,1,1,1,1,1,1418999179,49841285416,1559453016558,1,47624528432,1523984910896,74299876400612940292394,1943492137330847721768,1979118731504422070568,60894448965370076486324,1,2143610402313556830072040,1402655868873261433266406,43832995902289419772134,1484031922816510031771,1402655868873260777417958,41395682613507841562788,1,1454341383] (by decide) (by decide +kernel) (by simp)
  have r5 := row32 D mate inv chord edges noCycle 10 [(12,16),(11,7),(0,23)] [30]
    #[1,2104612795229213953468448,1346644314443,1382112431433,45407770788,1315088680,1252714,1,42250,1,1,1,1,1453389,1421230574,1488272845,1,1630389250608,1488276016,47624866352,1753074133596892410286,56098372287230647841198,1717152699036387501153644,1,63331799408141506274038,2065615188144871076882199,2224121589970626090835306,1480651081880862907541800,46270346308776965843240,1560199124153082609629,1,2104612795229213953469408] (by decide) (by decide +kernel) (partnerCons r4 (by simp))
  have r6 := row32 D mate inv chord edges noCycle 13 [(12,20),(11,7),(0,23)] []
    #[1,1990135948626788088808876,1676906932652722585634,1346644325771,46587319495,1315091851,1488516782508,1,1418999179,1317320075,1453389,1,1,1,1,47535,1554864,1663685005,1592183344,55383178701,1,1725868,1714636724385785187435254,1,1210183806939930557822743,1810018100652,2169536734845940022733,66987825072298650955609,2182608009397899706692474,1445948322149280167307,1597643903132756592244107,49926371972898643490187] (by decide) (by decide +kernel) (by simp)
  have r7 := row32 D mate inv chord edges noCycle 12 [(11,7),(0,23)] [16,20]
    #[1,1638823331984419019777,65769149850912936036384,42082635147,1315082635,1453048665483,47624528102,1,1286539,1419564,44364,1,1,1,46478,1521039,1,1557546511,54274800044,1701325484658,1,1675639117301442310856405,37818243966872829932247,1,37818243966872829932311,2131453134177636432300,65769149850912936061752,2143610402313556830089049,1445948322149280182667,1558646296048414789382506,48707696751512962150762,1636366325489689756703] (by decide) (by decide +kernel) (partnerCons r5 (partnerCons r6 (by simp)))
  have r8 := row32 D mate inv chord edges noCycle 8 [(9,31),(12,4),(11,15),(0,23)] []
    #[1,1311176197383,43191013474,1245815014,1,1284264,40136,1,1,1,42250,1,1,1418999179,49841285416,1,1453629967,51020834123,1912140734458102336683304,75518551621998655196425,2359954738187457974537,1979118731504422070568,60894448965370076486324,1,1753074133989329216843,1402655868873261433266406,43832995902289419772134,1484031922816510031771,2146365705,1249181414024980508500704,1320958,1] (by decide) (by decide +kernel) (by simp)
  have r9 := row32 D mate inv chord edges noCycle 9 [(12,4),(11,15),(0,23)] [31]
    #[1,1136124112201,1346644314408,44299392131,1,1386590341,1318089,41193,1,1,1,1,1,1417580548493,1453636012,1,1594921133583,1453639183,46516487695,1676906932640458937484,53661021844873751499916,1717152699036373473236108,2017202332172725661001,1,2026617581060528200278774,1753074133989329773899,1441653474831704403027207,45051671088490762577159,1522115523484780067772,73158635274545436011849,2323138031500757806409,1] (by decide) (by decide +kernel) (partnerCons r8 (by simp))
  have r10 := row32 D mate inv chord edges noCycle 12 [(11,15),(0,23)] [4]
    #[1,46270346309169403242792,1445948322540609186088,2104612795229213953198112,1,1453048665483,47624528102,1384362346,1384400796076,1419564,44364,1,1,1,46478,1,1421839,1557546511,54274800044,1701325484658,1632677515659,1675639117301442310856405,37818243966872829932247,1,37818243966872829932311,2131453134177636432300,65769149850912936061752,2143610402313556830089049,2299600830650928336485740,1558646296048414789382506,48707696751512962150762,1636366325489689756703] (by decide) (by decide +kernel) (partnerCons r9 (by simp))
  have r11 := row32 D mate inv chord edges noCycle 4 [(1,25),(3,31),(10,2),(11,19),(0,23)] []
    #[1,1,1,1,1,1,38022,1250439,1211181352,1280451847,1,1,1144140138,36612518250,1455336919138,68206500293684365495361,2131453134177636060225,1826784328831207708836,56019748079827216910896,1,1562656130647811821666,1247884114595056383070306,38996378581095511953506,1,34395493143,1,1109496665,68683721859,2146365571,1169338365059,38757499902,1] (by decide) (by decide +kernel) (by simp)
  have r12 := row32 D mate inv chord edges noCycle 1 [(3,31),(10,2),(11,19),(0,23)] [25]
    #[1,1,1,1,1148964,1277996345409,1176541348,42082634817,1311176197383,1353793,1,1,1638823331984419019777,1372238127306279779428,1712533526826296937537,52363722415670072229325,1714636724385785187451374,1598282724821386184275,2377596044819614089675807,1,1218636830659234749108,2283787536850830299134,1082102,1,1050391,1,2197879121952,35466999707,2111702047,2079296577,1081281,1] (by decide) (by decide +kernel) (partnerCons r11 (by simp))
  have r13 := row32 D mate inv chord edges noCycle 3 [(10,2),(11,19),(0,23)] [31]
    #[1,34851,1,1,1,36965,1216614,1317316675,1245815014,44299392131,1,1,2104612795229213953198112,1421227106,45479278690,1455336930402,1788700728162904118403,54801072858441502017039,1792631938554470940658224,1,1246665439373670668176449,38958294980427208363073,1293615081694216119030,1,1176535800,34395514647,1916421638176,1246665438540668760008769,1134943989858,37649154013,1107233857,1] (by decide) (by decide +kernel) (partnerCons r12 (by simp))
  have r14 := row32 D mate inv chord edges noCycle 12 [(10,6),(11,19),(0,23)] []
    #[1,1638823331984419019777,65769149850912936036384,45478940838,1280455018,1453048665483,1,1384362346,1282683242,1419564,1,1,1,1,46478,1521039,1629048172,1557546511,54274800044,1,1692043,1675639117301442310856405,1732958603,1,37818243966872829932311,2131453134177636432300,65769149850912936061752,2143610402313556830089049,1407864721515336315242,1558646296048414789382506,48707696751512962150762,1636366325489689756703] (by decide) (by decide +kernel) (by simp)
  have r15 := row32 D mate inv chord edges noCycle 10 [(11,19),(0,23)] [2,6]
    #[1,2104612795229213953468448,1,1382112431433,45407770788,1315088680,1,1351914,42250,1,1,1,44364,1453389,1597209398634,1488272845,52058042730,1630389250608,1658218,1,1723754,1560199124153082601173,1834634602,1,63331799408141506274038,2065615188144871076882199,49926371972898643239738,1480651081880862907541800,46270346308776965843240,1560199124153082609629,2321871137519154384234,2104612795229213953469408] (by decide) (by decide +kernel) (partnerCons r13 (partnerCons r14 (by simp)))
  have r16 := row32 D mate inv chord edges noCycle 14 [(25,5),(11,27),(0,23)] []
    #[1,1712533526826296937537,1756150306120730829557858,68206500293684365823109,1714990533321026200740,1,2131453134177636432069,1523984899533,49841285416,1453636012,2260603223566585459882315,1,46478,1,1,1,48592,1588689,1867324935994239988142,1626820177,56491557358,1772261718708,1712533526826297647862,1,2056006350219,1,1557540730,1,68206500293684365849466,2221605616482242583295899,1490805553051,1636641510217099435293100] (by decide) (by decide +kernel) (by simp)
  have r17 := row32 D mate inv chord edges noCycle 25 [(11,27),(0,23)] [5]
    #[1,1219903724633079541593,1074882327,34395514647,1985046677604,1,1407864721515336331097,42614321806803611720901,1402655868873261433266406,1386606425,2065615188144871076882199,1,2131453134177636432300,1522921305,49841303385,1490805057371,2026617581426064902554358,63331799737358856717046,1914134186808,62033450643,1834641175,1979118731504422088537,1859289,1,1,1,1,1,1960764,62032740317,2007825340,68683722585] (by decide) (by decide +kernel) (partnerCons r16 (by simp))
  have r18 := row32 D mate inv chord edges noCycle 11 [(0,23)] [3,7,15,19,27]
    #[1,65769149850912936045600,2104612795229213953460256,1,1417580548458,46516149445,1349725513,1,1385739,43307,1,1,1,45421,1487214,1,1522909678,53166421387,1665857367633,1,1636641510217099435039412,37818243966872829941463,1598282724821386167030,1,2093369533509332841867,64550474629527221167895,2104612795229213953485624,1,1519648688964106272517449,47489021530128320998729,1598282724821386167294,65769149850912936046560] (by decide) (by decide +kernel) (partnerCons r3 (partnerCons r7 (partnerCons r10 (partnerCons r15 (partnerCons r17 (by simp))))))
  exact r18

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem partner24 (D : SimpleGraph (Fin 32)) (mate : Fin 32 → Fin 32)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 32).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 32).Adj i j ∨ j = mate i)
    (noCycle : ¬ ∃ m ∈ [3,4,6,7,8,14,15,16], cycleGraph m ⊑ D) :
    ¬ (∀ e ∈ ([(0,24)] : List (Fin 32 × Fin 32)), mate e.1 = e.2) := by
  have r0 := row32 D mate inv chord edges noCycle 2 [(31,22),(1,5),(0,24)] []
    #[1,1,1,1,35908,1,1083589,1211178181,43191013474,1346644314408,1277996345409,2065615188144871076594719,2143610402313556830062624,53661021844887123525666,1714990533321026175010,1750617127494600527970,53582397637055787123182,1753634331470128064054799,1909624759807499570451490,2416593651903956966279200,75518551621998655178784,1255567509822931492565,1,1141931735,1,1880953521183,1906116640,1133835611201,36541823932,2146338848,2163590991970,1] (by decide) (by decide +kernel) (by simp)
  have r1 := row32 D mate inv chord edges noCycle 31 [(1,5),(0,24)] [22]
    #[1,1,1082338,2113967235,1108316258,1,1240239996101,1108319429,35466255557,1277996366849,1405171843085688793522177,2143610402313556830072800,1636366325489689756703,49926371972898643490187,1636641510217099435293100,1372238127306293902337,2299600830650928336502749,71862525957841510531037,2359954738187457974898,1949602303968,60925072352,1903908832,1,2065175,1,68683722585,2042462173,2007818271,2062239,64447,1,1] (by decide) (by decide +kernel) (partnerCons r0 (by simp))
  have r2 := row32 D mate inv chord edges noCycle 30 [(3,31),(1,9),(0,24)] []
    #[1,1,2063458,1,38757499902,1204772927652,1178770399,37720629215,1108343049,1,2112881962,1598282724821386167294,48707696751512962150762,1597643903132756592244107,2093369533509332859872,2260603223566585459899324,70643850736455795637180,2321871137519154384465,1524572529979508620289,48786320959344264313857,1949602315232,35432094456,1836844030,2091474771933,1,2007825340,1973158910,2028414,63390,1,1,1] (by decide) (by decide +kernel) (by simp)
  have r3 := row32 D mate inv chord edges noCycle 3 [(1,9),(0,24)] [31]
    #[1,1,1,1,1,36965,1216614,1176544519,1245815014,1,1382112431433,1109503305,35504139593,1419868802113,66987825072298650601504,2093369533509332469792,1788700728162904118403,54801072858441502017039,1792631938554470940658224,1524572529979508231233,1246665439373670668176449,38958294980427208363073,1293615081694216119030,1176535831,1,1074859832,60995766304,2359954712156148343840,1134943989858,37649154013,1107233857,1] (by decide) (by decide +kernel) (partnerCons r2 (by simp))
  have r4 := row32 D mate inv chord edges noCycle 4 [(3,11),(30,2),(1,10),(0,24)] []
    #[1,1,1,1,1,1,38022,1250439,43262183524,1280451847,1,1,1421443,1136124146026,1455863939,46587657347,1490805047427,1826784328831207708836,56019748079827216910896,1831629545638813817261649,2321871137519154368610,1247884114595056383070306,38996378581095511953506,1331697556462612866839,1,34395493176,1100655782712,36612993982,2111705186,1169338365059,1,1108316258] (by decide) (by decide +kernel) (by simp)
  have r5 := row32 D mate inv chord edges noCycle 3 [(30,2),(1,10),(0,24)] [11]
    #[1,1,1,1,1,36965,1216614,37649458439,1245815014,44299392131,1,1,1421216833,45479267393,1204782739886,2093369533509332469792,1788700728162904118403,54801072858441502017039,1792631938554470940658224,2321871137519154383970,1246665439373670668176449,38958294980427208363073,1293615081694216119030,1176535831,1,1074859832,67575343202,2111728738,1134943989858,37649154013,1,2063458] (by decide) (by decide +kernel) (partnerCons r4 (by simp))
  have r6 := row32 D mate inv chord edges noCycle 28 [(2,25),(30,18),(1,10),(0,24)] []
    #[1,1,1,1134943989858,38758312828,1987357872226,1909624759807499570475966,59675773743984361599934,1486488929311204670396,1522115523484780067772,1,1519648688964106272517449,52363722415670073027452,2182608009397899706692474,68206500293684365849466,2245703936182547203599,2044676656,2143610402313984734659673,1,2093369533866301195353,2111722098,2020538537883,65358586614,1938551674,1,1,61276,1,1,1,1,2062239] (by decide) (by decide +kernel) (by simp)
  have r7 := row32 D mate inv chord edges noCycle 2 [(30,18),(1,10),(0,24)] [25]
    #[1,1,1,1,35908,1182789,41045764130,1211178181,43191013474,1346644314408,1,1387585,2143610402313556830062624,1522903074,45479278657,1750617127494600527970,53582397637055787123182,1753634331470128064054799,1,2416593651903956966279200,75518551621998655178784,1255567509822931492565,50004996180729978869825,1600159877783359323855937,1,1,1906116640,1133835611201,36541823932,2146338848,1,1082338] (by decide) (by decide +kernel) (partnerCons r6 (by simp))
  have r8 := row32 D mate inv chord edges noCycle 30 [(1,10),(0,24)] [2,18]
    #[1,1,1,1107233857,38757499902,1204772927652,2245703910151237573597,71862525124839602331613,35466977578,2112881993,1,1598282724821386167294,48707696751512962150762,1597643903132756592244107,2093369533509332859872,2260603223566585459899324,70643850736455795637180,2321871137519154384465,1,1562656130647812176897,1949602315232,35432094456,1836844030,2091474771933,1,2007825340,1973158910,2028414,63390,1,1,1] (by decide) (by decide +kernel) (partnerCons r5 (partnerCons r7 (by simp)))
  have r9 := row32 D mate inv chord edges noCycle 3 [(23,2),(1,17),(0,24)] []
    #[1,1,1,1,1,36965,1216614,1448405328642901050435,1245815014,44299392131,1382112431433,65769149850912936045666,2055285932841029251170,1701325474881,49912775747,1176552975,1788700728162904118403,1,1792631938554470940658224,59816692834,1246665439373670668176449,38958294980427208363073,1293615081694216119030,1,1,1074859832,1871505506,64250207299,1134943989858,37649154013,1107233857,2117164800] (by decide) (by decide +kernel) (by simp)
  have r10 := row32 D mate inv chord edges noCycle 6 [(4,12),(23,7),(1,17),(0,24)] []
    #[1,1,1255567509822931492070,1216614,1,1,1,1,40136,1318089,2104612795229213953468615,1349725513,1,1488516782508,1213413804,38829275564,1136123877905,1,1739081866470,1902951530167814889702,58457098522598646698610,1909624759807499570468499,1253110,1,1,1407864721515336331097,1973181670,64250207462,1916422451399,47567645408741233226951,1255567483791621861507,1240239996101] (by decide) (by decide +kernel) (by simp)
  have r11 := row32 D mate inv chord edges noCycle 2 [(4,28),(23,7),(1,17),(0,24)] []
    #[1,1,1,1,1,1182789,1255567509822931492070,1,43191013474,1346644314408,1217446692107040630849,38958294147425300196417,1701325484097,48804414498,1559774242,1750617127494600527970,53582397637055787123182,1,1083985,2416593651903956966279200,75518551621998655178784,1255567509822931492565,1171591995126,1,1,38758312828,1906116640,1133835611201,1,2146338848,1873143127373759460079681,1082338] (by decide) (by decide +kernel) (by simp)
  have r12 := row32 D mate inv chord edges noCycle 4 [(23,7),(1,17),(0,24)] [12,28]
    #[1,1,35908,1,1,1,38022,1,2107128769879781251584263,1280451847,45407770788,1417580548458,1,65769149850912935777479,1701325179969,38757516815,1211172400,1,56019748079827216910896,1831629545638813817261649,1136124382801,1247884114595056383070306,38996378581095511953506,1,1,38829023001,1346645092119,58535722730429982313537,1,1169338365059,38757499902,1108316258] (by decide) (by decide +kernel) (partnerCons r10 (partnerCons r11 (by simp)))
  have r13 := row32 D mate inv chord edges noCycle 23 [(1,17),(0,24)] [2,7]
    #[1,1,1,1176535831,1331697556462612866839,40178160314333807744131,1324661843654877305870500,1,1987619973976185323675349,62113124186755791380181,2055285932841029251434,1598282724821386167063,52363722415670072214295,1210183806939930557822712,38996378581095511703057,2057742939335723894287,1843197952758,1,1765367509,2057742939335723894355,1791639,55991,1,1,1,58105,1893114,2058294887191,1938551674,66466965271,2091474771933,2065175] (by decide) (by decide +kernel) (partnerCons r9 (partnerCons r12 (by simp)))
  have r14 := row32 D mate inv chord edges noCycle 3 [(2,6),(1,22),(0,24)] []
    #[1,1,1,1,1,36965,1,1117414,1245815014,44299392131,1382112431433,1313464462434,2017202332172725652545,2143610402313556829767712,66987825072298650601504,2093369533509332469792,1788700728162904118403,54801072858441502017039,1792631938554470940658224,58708298817,1246665439373670668176449,38958294980427208363073,1,1246665439373670012328001,1,1074859832,1136147620598,1951889721376,1134943989858,37649154013,1107233857,2164699370627] (by decide) (by decide +kernel) (by simp)
  have r15 := row32 D mate inv chord edges noCycle 2 [(1,22),(0,24)] [6]
    #[1,1,1,1,35908,1182789,1,1211178181,43191013474,1346644314408,64550474629527221151809,2017202332172725660737,2143610402313556830062624,53661021844887123525666,1714990533321026175010,1750617127494600527970,53582397637055787123182,1753634331470128064054799,58708314177,2416593651903956966279200,75518551621998655178784,1255567509822931492565,1,1793089,1,1836868673,63141828642,1133835611201,36541823932,2146338848,2163615717410,1082338] (by decide) (by decide +kernel) (partnerCons r14 (by simp))
  have r16 := row32 D mate inv chord edges noCycle 1 [(0,24)] [5,9,10,17,22]
    #[1,1,1,34851,1148964,1,1176541348,42082634817,1311176197383,1,1,2143610402313556830071840,52442346623501408657409,1676906932652722610177,1712533526826296937537,52363722415670072229325,1714636724385785187451374,1,2377596044819614089675807,74299876400612940284959,1218636830659234749108,1802231809,1,1082135,1,1050424,2197879121952,35466999707,2111702047,2126942887937,1081281,33761] (by decide) (by decide +kernel) (partnerCons r1 (partnerCons r3 (partnerCons r8 (partnerCons r13 (partnerCons r15 (by simp))))))
  exact r16

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem partner28 (D : SimpleGraph (Fin 32)) (mate : Fin 32 → Fin 32)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 32).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 32).Adj i j ∨ j = mate i)
    (noCycle : ¬ ∃ m ∈ [3,4,6,7,8,14,15,16], cycleGraph m ⊑ D) :
    ¬ (∀ e ∈ ([(0,28)] : List (Fin 32 × Fin 32)), mate e.1 = e.2) := by
  have r0 := row32 D mate inv chord edges noCycle 27 [(26,18),(29,6),(0,28)] []
    #[1,35466999707,1133835611201,1074859900,1213429659,1909624759807499570452346,1,1448405328642901068635,1484031922816510031771,45051671088490762577159,1480651081880862907541800,1181820123964775935868,2143610402313556830089049,66987825072298650955609,2207620335514243613166,1594411867,1788700728162904143771,1960529,1,1928818,1985070420858,64250207957,1903914841,1914134186843,1926939,60219,1,1,1,1,2028414,1962015] (by decide) (by decide +kernel) (by simp)
  have r1 := row32 D mate inv chord edges noCycle 27 [(26,22),(29,6),(0,28)] []
    #[1,35466999707,1133835611201,1074859900,1213429659,1100655761276,1,1347477799835,1484031922816510031771,45051671088490762577159,1480651081880862907541800,2017202332172725661562,2143610402313556830089049,66987825072298650955609,2207620335514243613166,1792631938554471774127003,1788700728162904143771,45130295295187119304605,58708315002,1834635130,1985070420858,64250207957,1,1793914,1926939,60219,1,1,1,1,2028414,1962015] (by decide) (by decide +kernel) (by simp)
  have r2 := row32 D mate inv chord edges noCycle 26 [(29,6),(0,28)] [18,22]
    #[1,2197879121952,2042431520,65357842464,66466943142,1975416005,1,1445948322149280183162,43832995902289419772134,1441653474831704403027207,1181820123964775951228,2104612795229213953485624,65769149850912936061752,2169536734845940022733,1753634331470154735580026,1410321727974597816221,45130295295187119599517,1870627152723156694659962,1,1949602303833,63141829300,1869278008,1,1893114,59162,1,1,1,1,1,1975387134,2042462173] (by decide) (by decide +kernel) (partnerCons r0 (partnerCons r1 (by simp)))
  have r3 := row32 D mate inv chord edges noCycle 17 [(18,14),(26,22),(29,7),(0,28)] []
    #[1,1249181414024273434425937,1753634331470128064054799,54801072858441502017039,1826784328831207708836,1873143127373759460056261,73081201179227225408711,1,58535722730429983126760,1594921133618,1630389250608,53166421387,1557546511,1489489,1,49649,1,1,1,51763,1690164,1597209498226,1,59816693329,1878666069783,1878666069818,1,2019659338275017543317,1,1,2321871137519154384465,71862525957841510531037] (by decide) (by decide +kernel) (by simp)
  have r4 := row32 D mate inv chord edges noCycle 18 [(26,22),(29,7),(0,28)] [14]
    #[1,2377596044819614089675807,2245703936182547187744,1792631938554470940658224,56019748079827216910896,1864867929499511299269,2283787536850850793671,1,2283787536850850793735,59754397951815697997065,1912140734458102335906090,1665857367633,54274800044,1592183344,1,1622514,50706,1,1,1,52820,1723989,1,1765367509,60925071986,1914134186808,1,58708315002,1,1,2169536734845954130843,2359954738187457974898] (by decide) (by decide +kernel) (partnerCons r3 (by simp))
  have r5 := row32 D mate inv chord edges noCycle 26 [(29,7),(0,28)] [22]
    #[1,2197879121952,2042431520,65357842464,1100655782780,63213313221,2077092039,1,43832995902289419772134,1441653474831704403027207,1453049443194,2104612795229213953485624,65769149850912936061752,2169536734845940022733,54801072858467065164666,1792631938554496503804794,1788700728162904896378,58457098522598647460730,1909624759807499571229562,1949602303833,63141829300,1869278008,1,1893114,59162,1,1,1,1,1,1975387134,2042462173] (by decide) (by decide +kernel) (partnerCons r4 (by simp))
  have r6 := row32 D mate inv chord edges noCycle 31 [(26,22),(29,8),(0,28)] []
    #[1,33761,1082338,2093762054176,1108316258,39865877535,1240239996101,1104060671,1,1334154527380531577923,2079303976,1288179021108616966893569,1636366325489689756703,49926371972898643490187,1636641510217099435293100,1795147913205073706872863,2299600830650928336502749,71862525957841510531037,2359954738187457974898,60894448965370076493791,1522164663614673570660317,2022826802870,1,2022826802934,2126942888958,68683722585,1,1962015,1,1,1,1] (by decide) (by decide +kernel) (by simp)
  have r7 := row32 D mate inv chord edges noCycle 26 [(29,8),(0,28)] [22]
    #[1,2197879121952,2042431520,65357842464,1100655782780,2022826056901,43191725981,1445948322149280183162,1,1441653474831704403027207,66466949416,2104612795229213953485624,65769149850912936061752,2169536734845940022733,1712533526850751722362,56019748079851671679866,1831629545638838272029562,1826784328831208452986,59675773743984362320762,1949602303833,63141829300,1869278008,1,1893114,59162,1,1,1,1,1,1975387134,2042462173] (by decide) (by decide +kernel) (partnerCons r6 (by simp))
  have r8 := row32 D mate inv chord edges noCycle 30 [(29,9),(0,28)] []
    #[1,1081281,2044659744,1107233857,38757499902,1204772927652,1384356829,1133811869628,1352669,1,1257987325301403611137,1598282724821386167294,48707696751512962150762,1597643903132756592244107,1419868814301,2260603223566585459899324,70643850736455795637180,2321871137519154384465,2169536734845954130843,1246653538248461823322044,1941035130836118480830,63331799408141506258878,2065615188144871076865982,2091474771933,67575343928,2007825340,1975387134,2028414,1,1,1,1] (by decide) (by decide +kernel) (by simp)
  have r9 := row32 D mate inv chord edges noCycle 16 [(25,13),(26,15),(29,20),(0,28)] []
    #[1,1714636724385785187451374,53582397637055787123182,1788700728162904118403,2185123984012183121444301,2171993740205689542159,45051671088490762594800,1480651081880862907558384,1873143127373744979649808,1594921133583,52058042730,1522909678,62191748394159222310483,1,48592,1,1,1,50706,1656339,1,1696093843,58708314672,1843197952758,1525138201,1,1,2058284026416,1,1,70643850736455795637180,2299600830650928336502749] (by decide) (by decide +kernel) (by simp)
  have r10 := row32 D mate inv chord edges noCycle 18 [(25,17),(26,15),(29,20),(0,28)] []
    #[1,2377596044819614089675807,2245703936182547187744,1792631938554470940658224,56019748079827216910896,1864867929499511299269,2185123984012183121074769,1445948322149280174706,73158635274537677376116,1558646296048414789390962,60973073173188040863058,1665857367633,54274800044,1592183344,1692920625,1,50706,1,1,1,1,1723989,1836869170,1765367509,60925071986,1,1,1594411898,1,1,2169536734845954130843,2359954738187457974898] (by decide) (by decide +kernel) (by simp)
  have r11 := row32 D mate inv chord edges noCycle 25 [(26,15),(29,20),(0,28)] [13,17]
    #[1,2042455072,1288179021108616311029593,41474269631029974613849,1334154526637990297433,1943492136583729021853,1407864721515336331097,42614321806803611720901,1402655868873261433266406,1181820123964776442748,2065615188144871076882199,64550474629527221167895,2131453134177636432300,1,1523545,1,1926671,1,1914134186808,62033450643,1,62104958613,1859289,58105,1,1,1,60219,1,1,2007825340,68683722585] (by decide) (by decide +kernel) (partnerCons r9 (partnerCons r10 (by simp)))
  have r12 := row32 D mate inv chord edges noCycle 25 [(26,16),(29,20),(0,28)] []
    #[1,2042455072,34396236668,1327176628192959187632985,57238423301212931789626,1788700728162904119098,1407864721515336331097,42614321806803611720901,1402655868873261433266406,1181820123964776442748,2065615188144871076882199,64550474629527221167895,2131453134177636432300,1626814266,74341418765442671529629,1894927,1,1926704,1914134186808,62033450643,1,62104958613,1859289,58105,1,1,1,60219,1,1,2007825340,68683722585] (by decide) (by decide +kernel) (by simp)
  have r13 := row32 D mate inv chord edges noCycle 26 [(29,20),(0,28)] [15,16]
    #[1,2197879121952,2042431520,65357842464,1100655782780,2378893344249538215106205,2182608009760137874117850,1445948322149280183162,43832995902289419772134,1441653474831704403027207,1181820123964775951228,2104612795229213953485624,65769149850912936061752,2169536734845940022733,1714990533329892176762,1,1,1703614018426,54346576762,1949602303833,1,1869278008,58708652922,1893114,59162,1,1,1,1,1,1975387134,2042462173] (by decide) (by decide +kernel) (partnerCons r11 (partnerCons r12 (by simp)))
  have r14 := row32 D mate inv chord edges noCycle 20 [(19,15),(26,16),(29,21),(0,28)] []
    #[1,1218636830659234749108,75518551621998655178784,1246665439373670668176449,1750617127494600528531,1870627152723156693865074,58457098522598646698610,1941035130836118480135,1484031922816510031540,48707696751512962168500,2341076328785205675731605,50949664403,1592177299,1736793601683,56491557358,1,1,1690164,52820,1,1,1,54934,1791639,1951890568884,1834641175,1,1985070420858,1,1,2062004,2014302909] (by decide) (by decide +kernel) (by simp)
  have r15 := row32 D mate inv chord edges noCycle 19 [(26,16),(29,21),(0,28)] [15]
    #[1,74299876400612940284959,2416593651903956966279200,1293615081694215816787,1831629545638813817261649,57238423301212931804753,1902951530167814889702,1445948322149280175763,47489021530128321009299,2341076328785205675740821,62191748394194690256211,1943492137318584070515,1701325484658,55383178701,1626820177,1,1,51763,1,1,1,1,1757814,1772262090519,1800004342,62033450643,1,1730724699,1,1,1133824858044,2146358931] (by decide) (by decide +kernel) (partnerCons r14 (by simp))
  have r16 := row32 D mate inv chord edges noCycle 20 [(19,15),(26,17),(29,21),(0,28)] []
    #[1,1218636830659234749108,75518551621998655178784,1246665439373670668176449,1750617127494600528531,1870627152723156693865074,58457098522598646698610,1941035130836118480135,1484031922816510031540,48707696751512962168500,2341076328785205675731605,50949664403,1592177299,1736793601683,56491557358,1,1557139,1,52820,1,1,1,54934,1791639,1951890568884,1834641175,1,1985070420858,1,1,2062004,2014302909] (by decide) (by decide +kernel) (by simp)
  have r17 := row32 D mate inv chord edges noCycle 19 [(26,17),(29,21),(0,28)] [15]
    #[1,74299876400612940284959,2416593651903956966279200,2245703936182546696224,1831629545638813817261649,57238423301212931804753,1902951530167814889702,1445948322149280175763,47489021530128321009299,2341076328785205675740821,1792631938920007642966576,56019748409044567386672,1701325484658,55383178701,1626820177,1,1656339,1,1,1,1,1,1757814,55383516951,1800004342,62033450643,1,1732966299,1,1,1772272612286,2146358931] (by decide) (by decide +kernel) (partnerCons r16 (by simp))
  have r18 := row32 D mate inv chord edges noCycle 26 [(29,21),(0,28)] [16,17]
    #[1,2197879121952,2042431520,65357842464,2323138031516203604669,74340417007798069222077,2378893344248852128717501,1445948322149280183162,43832995902289419772134,1441653474831704403027207,1181820123964775951228,2104612795229213953485624,65769149850912936061752,2169536734845940022733,54879697066280596042618,1753074133997087388538,1,1,1739082101626,1949602303833,63141829300,1,1975416502,1893114,59162,1,1,1,1,1,2020538537918,2042462173] (by decide) (by decide +kernel) (partnerCons r15 (partnerCons r17 (by simp)))
  have r19 := row32 D mate inv chord edges noCycle 29 [(0,28)] [6,7,8,9,20,21]
    #[1,1995808,2146338848,37649154013,1169338365059,1100655761340,1,1,1,1,1560199124153082609629,47489021530128320998729,1558646296048414789382506,1714636724385785187435421,2221605616482242583295899,69425175515070080743323,2283787536850850794032,2221605616482243035759515,66987825072726522883929,2093369533901736669017,1,1,2056006654908,66466965271,1973188507,1987357736925,1994589,62333,1,1,1,64447] (by decide) (by decide +kernel) (partnerCons r2 (partnerCons r5 (partnerCons r7 (partnerCons r8 (partnerCons r13 (partnerCons r18 (by simp)))))))
  exact r19

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- Every cubic Hamiltonian chord diagram on 32 vertices has a cycle of
one of these eight lengths, all at most half the circumference. -/
theorem ring32 (D : SimpleGraph (Fin 32)) (mate : Fin 32 → Fin 32)
    (inv : Function.Involutive mate)
    (chord : ∀ i, mate i ≠ i ∧ ¬ (cycleGraph 32).Adj i (mate i))
    (edges : ∀ i j, D.Adj i j ↔ (cycleGraph 32).Adj i j ∨ j = mate i) :
    ∃ m ∈ [3,4,6,7,8,14,15,16], cycleGraph m ⊑ D := by
  by_contra noCycle
  have r196 := row32 D mate inv chord edges noCycle 0 [] [4,8,9,10,11,12,16,20,21,22,23,24,28]
    #[1,1,33794,1115139,1,1141904515,40974256160,1275708080358,1,1,1,1,1,1674449926157993347104,51145047194284357335468,1675639117301442310847949,1,2338598437735271213073406,73081201179227225392126,1217446718138350261907,1,1,1,1,1,2162411004959,35432362874,2077066238,1,2096032,65472,1] (by decide) (by decide +kernel) (partnerCons (partner4 D mate inv chord edges noCycle) (partnerCons (partner8 D mate inv chord edges noCycle) (partnerCons (partner9 D mate inv chord edges noCycle) (partnerCons (partner10 D mate inv chord edges noCycle) (partnerCons (partner11 D mate inv chord edges noCycle) (partnerCons (partner12 D mate inv chord edges noCycle) (partnerCons (partner16 D mate inv chord edges noCycle) (partnerCons (partner20 D mate inv chord edges noCycle) (partnerCons (partner21 D mate inv chord edges noCycle) (partnerCons (partner22 D mate inv chord edges noCycle) (partnerCons (partner23 D mate inv chord edges noCycle) (partnerCons (partner24 D mate inv chord edges noCycle) (partnerCons (partner28 D mate inv chord edges noCycle) (by simp))))))))))))))
  exact r196 (by simp)


private theorem ringDirections {n : ℕ} (x y : Fin (n+3)) :
    (cycleGraph (n+3)).Adj x y ↔ y = x+1 ∨ y = x-1 := by
  rw [cycleGraph_adj]
  constructor
  · rintro (h|h)
    · right
      rw [eq_sub_iff_add_eq]
      simpa [add_comm] using (sub_eq_iff_eq_add.mp h).symm
    · left
      simpa [add_comm] using sub_eq_iff_eq_add.mp h
  · rintro (rfl|rfl)
    · right
      simp [sub_eq_add_neg,add_comm,add_left_comm]
    · left
      simp [sub_eq_add_neg,add_comm]

/-- A bijection preserving the edges of a labeled ring is a rotation or a reflection. -/
theorem ringAffine {n : ℕ} (f : Fin (n+3) → Fin (n+3)) (inj : Function.Injective f)
    (pres : ∀ i j, (cycleGraph (n+3)).Adj i j → (cycleGraph (n+3)).Adj (f i) (f j)) :
    (∀ i, f i = f 0 + i) ∨ (∀ i, f i = f 0 - i) := by
  have two : (2 : Fin (n+3)) ≠ 0 := ne_of_beq_false rfl
  have steps (i) := (ringDirections _ _).mp (pres i (i+1) ((ringDirections _ _).mpr (Or.inl rfl)))
  have forward (g : Fin (n+3) → Fin (n+3)) (gi : Function.Injective g)
      (step : ∀ i, g (i+1) = g i+1 ∨ g (i+1) = g i-1)
      (first : g 1 = g 0+1) : ∀ i, g i = g 0+i := by
    have run (k : ℕ) : g (Fin.ofNat (n+3) k) = g 0 + Fin.ofNat (n+3) k ∧
        g (Fin.ofNat (n+3) k+1) = g (Fin.ofNat (n+3) k)+1 := by
      induction k with
      | zero => simpa using first
      | succ k ih =>
        rw [show Fin.ofNat (n+3) (k+1) = Fin.ofNat (n+3) k + 1 by
          apply Fin.ext
          simp [Fin.ofNat,Fin.val_add,Nat.add_mod]]
        refine ⟨by rw [ih.2,ih.1,add_assoc],?_⟩
        rcases step (Fin.ofNat (n+3) k+1) with h | back
        · exact h
        · rw [ih.2,add_sub_cancel_right] at back
          have eq := gi back
          have eq' : Fin.ofNat (n+3) k + 2 = Fin.ofNat (n+3) k + 0 := by simpa [add_assoc,show (1:Fin (n+3))+1=2 from rfl] using eq
          exact (two (add_left_cancel eq')).elim
    intro i
    simpa using (run i.val).1
  rcases steps 0 with pos | neg
  · exact Or.inl (forward f inj steps (by simpa using pos))
  · right
    have rev (i : Fin (n+3)) : -f (i+1) = -f i+1 ∨ -f (i+1) = -f i-1 := by
      rcases steps i with h|h
      · right; rw [h]; simp [sub_eq_add_neg,add_comm]
      · left; rw [h]; simp [sub_eq_add_neg,add_comm]
    have first : -f 1 = -f 0+1 := by
      rw [show f 1 = f 0-1 by simpa using neg]
      simp [sub_eq_add_neg,add_comm]
    intro i
    have h := congrArg Neg.neg (forward (fun j => -f j) (fun _ _ e => inj (neg_injective e)) rev first i)
    simpa [sub_eq_add_neg,add_comm] using h

/-- Transitivity of ring-preserving symmetries forces the two-step rotation. -/
theorem ringShiftTwo {n : ℕ} (D : SimpleGraph (Fin (n+3)))
    (trans : ∀ i j, ∃ f : D ≃g D, f i = j)
    (pres : ∀ (f : D ≃g D) i j, (cycleGraph (n+3)).Adj i j →
      (cycleGraph (n+3)).Adj (f i) (f j)) :
    ∃ s : D ≃g D, ∀ i, s i = i+2 := by
  obtain ⟨f,hf⟩ := trans 0 1
  obtain ⟨g,hg⟩ := trans 0 2
  have twice (u : D ≃g D) (hu : ∀ i, u i = i+1) :
      ∃ s : D ≃g D, ∀ i, s i = i+2 := by
    refine ⟨u.trans u,fun i => ?_⟩
    change u (u i) = i+2
    rw [hu,hu,add_assoc]
    rfl
  rcases ringAffine f f.injective (pres f) with rot | flip
  · exact twice f (fun i => by rw [rot i,hf,add_comm (1 : Fin (n+3)) i])
  rcases ringAffine g g.injective (pres g) with rot | flip'
  · exact ⟨g,fun i => by rw [rot i,hg,add_comm (2 : Fin (n+3)) i]⟩
  apply twice (f.trans g)
  intro i
  change g (f i) = i+1
  rw [flip' (f i),flip i,hf,hg,sub_sub_eq_add_sub,
    show (2 : Fin (n+3)) = 1+1 from rfl]
  rw [add_comm (1+1 : Fin (n+3)) i,← add_assoc,add_sub_cancel_right]

/-- A chord and its translate by two close a hexagon, except when the
two short arcs overlap and the original chord already closes a triangle. -/
theorem shiftedChords {n : ℕ} (D : SimpleGraph (Fin (n+3)))
    (ring : cycleGraph (n+3) ≤ D) (j : Fin (n+3))
    (outside : ¬ (cycleGraph (n+3)).Adj 0 j) (chord : D.Adj 0 j)
    (shift : D.Adj 2 (j+2)) : cycleGraph 3 ⊑ D ∨ cycleGraph 6 ⊑ D := by
  have step (i : Fin (n+3)) : D.Adj i (i+1) := ring ((ringDirections _ _).2 (Or.inl rfl))
  have z : (0 : Fin (n+3)).val = 0 := rfl
  have o : (1 : Fin (n+3)).val = 1 := rfl
  have t : (2 : Fin (n+3)).val = 2 := rfl
  have sum : (j+1).val = (j.val+1) % (n+3) := Fin.val_add ..
  have sum' : (j+2).val = (j.val+2) % (n+3) := Fin.val_add ..
  have low : 1 < j.val := by
    by_contra! h
    rcases (show j.val = 0 ∨ j.val = 1 by omega) with e|e
    · exact chord.ne (Fin.ext e.symm)
    · exact outside ((ringDirections _ _).2 (Or.inl (Fin.ext e)))
  have high : j.val+1 < n+3 := by
    by_contra! h
    have h' : j.val+1 = n+3 := by have := j.isLt; omega
    have wrap : j+1=0 := Fin.ext (by rw [sum,h',Nat.mod_self,z])
    exact outside ((ringDirections j 0).2 (Or.inl wrap.symm)).symm
  have v := sum.trans (Nat.mod_eq_of_lt high)
  have first : D.Adj 0 1 := by simpa using step 0
  have second : D.Adj 1 2 := step 1
  have far : D.Adj (j+1) (j+2) := by
    simpa only [add_assoc,show (1 : Fin (n+3))+1 = 2 from rfl] using step (j+1)
  by_cases short : j.val = 2
  · have eq : j = 2 := Fin.ext short
    obtain ⟨c,_⟩ := rootedRing D [0,1,2] (by exact Nat.le_refl 3)
      (by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,
                     List.nodup_nil,not_false_eq_true,and_true,not_or,Fin.ext_iff,z,o,t]
          decide)
      (by simpa using And.intro first second) (by simpa [eq] using chord.symm)
    exact Or.inl ⟨c⟩
  by_cases back : j.val+2 = n+3
  · have wrap : j+2=0 := Fin.ext (by rw [sum',back,Nat.mod_self,z])
    obtain ⟨c,_⟩ := rootedRing D [j,j+1,0] (by exact Nat.le_refl 3)
      (by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,
                     List.nodup_nil,not_false_eq_true,and_true,not_or,Fin.ext_iff,z,v]
          omega)
      (by simpa using And.intro (step j) (wrap ▸ far : D.Adj (j+1) 0))
      (by simpa using chord)
    exact Or.inl ⟨c⟩
  have w := sum'.trans (Nat.mod_eq_of_lt (by omega))
  obtain ⟨c,_⟩ := rootedRing D [0,1,2,j+2,j+1,j] (by exact (by decide : 3 ≤ 6))
    (by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,
                   List.nodup_nil,not_false_eq_true,and_true,not_or,Fin.ext_iff,z,o,t,w,v]
        omega)
    (by simpa using And.intro first ⟨second,shift,far.symm,(step j).symm⟩)
    (by simpa using chord.symm)
  exact Or.inr ⟨c⟩

/-- In a transitive graph extending the ring, one extra edge suffices:
unless a triangle or a hexagon exists, an automorphism carries a ring edge
outside the ring. Its image of the spanning cycle is a second Hamiltonian cycle. -/
theorem movedRingEdge {n : ℕ} (large : 3 ≤ n) (D : SimpleGraph (Fin n))
    (ring : cycleGraph n ≤ D) (trans : ∀ i j, ∃ f : D ≃g D, f i = j)
    (extra : ∃ a b, D.Adj a b ∧ ¬ (cycleGraph n).Adj a b)
    (noTri : ¬ cycleGraph 3 ⊑ D) (noHex : ¬ cycleGraph 6 ⊑ D) :
    ∃ (f : D ≃g D) (i j : Fin n), (cycleGraph n).Adj i j ∧ ¬ (cycleGraph n).Adj (f i) (f j) := by
  obtain ⟨k,h⟩ : ∃ k, n = k+3 := ⟨n-3,by omega⟩
  subst n
  by_contra! pres
  obtain ⟨a,b,edge,off⟩ := extra
  obtain ⟨u,hu⟩ := trans a 0
  have atZero : D.Adj 0 (u b) := hu ▸ u.map_rel_iff.mpr edge
  have outside : ¬ (cycleGraph (k+3)).Adj 0 (u b) := by
    intro inside
    rw [← hu] at inside
    exact off (by simpa using pres u.symm _ _ inside)
  obtain ⟨s,hs⟩ := ringShiftTwo D trans pres
  have shifted : D.Adj 2 (u b+2) := by simpa only [hs,zero_add] using s.map_rel_iff.mpr atZero
  exact (shiftedChords D ring (u b) outside atZero shifted).elim noTri noHex

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R2.H2 := by
  intro partialOrbits hamilton V G _ _ r conn cubic bridges triangles witness forced
  classical
  rcases witness with ⟨t,ht,⟨c⟩⟩
  by_cases hex : ∃ (d : (cycleGraph 6).Copy G) (f : G ≃g G), f r ∈ Set.range d
  · obtain ⟨d,f,h⟩ := hex
    obtain ⟨e,hit⟩ := backToRoot d f h
    exact ⟨6,3,e,by decide,by decide,hit,Or.inr rfl⟩
  have away (n : ℕ) (short : n = 3 ∨ n = 6) (d : (cycleGraph n).Copy G) (f : G ≃g G) :
      f r ∉ Set.range d := by
    intro h
    rcases short with rfl | rfl
    · obtain ⟨e,hit⟩ := backToRoot d f h
      exact triangles e hit
    · exact hex ⟨d,f,h⟩
  by_cases trans : ∀ v, ∃ f : G ≃g G, f r = v
  · have onto (k : ℕ) (hk : 2 ≤ k) (d : (cycleGraph (2^k)).Copy G) :
        Function.Surjective d := by
      intro v
      obtain ⟨f,rfl⟩ := trans v
      exact forcedOrbit (forced k hk) d f
    let e := Equiv.ofBijective c ⟨c.injective,onto t ht c⟩
    let D := G.comap e
    let iso : D ≃g G := Iso.comap e G
    have ring : cycleGraph (2^t) ≤ D := fun _ _ h => c.toHom.map_adj h
    have deg (i) : D.degree i = 3 := (iso.degree_eq i).symm.trans (cubic _)
    have sym (i j) : ∃ f : D ≃g D, f i = j := by
      obtain ⟨u,hu⟩ := trans (iso i)
      obtain ⟨v,hv⟩ := trans (iso j)
      refine ⟨((iso.trans u.symm).trans v).trans iso.symm,?_⟩
      change iso.symm (v (u.symm (iso i))) = j
      rw [← hu,u.symm_apply_apply,hv,iso.symm_apply_apply]
    have exclude (n : ℕ) (short : n = 3 ∨ n = 6) : ¬ cycleGraph n ⊑ D := by
      rintro ⟨d⟩
      have pos : 0 < n := by rcases short with rfl | rfl <;> decide
      let i : Fin n := ⟨0,pos⟩
      obtain ⟨f,hf⟩ := trans (iso (d i))
      exact away n short (iso.toCopy.comp d) f ⟨i,hf.symm⟩
    have noshort (j : ℕ) (hj : 2 ≤ j) (lt : j < t) : ¬ cycleGraph (2^j) ⊑ D := by
      rintro ⟨d⟩
      let d' := iso.toCopy.comp d
      have eq := Fintype.card_congr (Equiv.ofBijective d' ⟨d'.injective,onto j hj d'⟩)
      have eq' := Fintype.card_congr e
      have power : (2:ℕ)^j = 2^t := by simpa using eq.trans eq'.symm
      exact (Nat.pow_lt_pow_right (by decide : 1 < 2) lt).ne power
    have large : 3 ≤ 2^t := by
      have h := Nat.pow_le_pow_right (by decide : 0 < 2) ht
      omega
    obtain ⟨mate,inv,chord,edges⟩ := chordMatching large D ring deg
    have goal : ∃ n k : ℕ, 3 ≤ n ∧ 2 ≤ k ∧ cycleGraph n ⊑ D ∧ (n+1=2^k ∨ n+2=2^k) := by
      by_cases big : 6 ≤ t
      · have extra : ∃ a b, D.Adj a b ∧ ¬ (cycleGraph (2^t)).Adj a b :=
          ⟨0,mate 0,(edges _ _).2 (Or.inr rfl),(chord 0).2⟩
        have tri := exclude 3 (Or.inl rfl)
        have hexFree := exclude 6 (Or.inr rfl)
        exact hamilton t big D deg mate inv chord edges sym
          (movedRingEdge large D ring sym extra tri hexFree) tri hexFree noshort
      · by_cases five : t = 5
        · subst t
          obtain ⟨m,hm,copy⟩ := ring32 D mate inv chord edges
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
          rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact (exclude 3 (Or.inl rfl) copy).elim
          · exact (noshort 2 (by decide) (by decide) copy).elim
          · exact (exclude 6 (Or.inr rfl) copy).elim
          · exact ⟨7,3,by decide,by decide,copy,Or.inl rfl⟩
          · exact (noshort 3 (by decide) (by decide) copy).elim
          · exact ⟨14,4,by decide,by decide,copy,Or.inr rfl⟩
          · exact ⟨15,4,by decide,by decide,copy,Or.inl rfl⟩
          · exact (noshort 4 (by decide) (by decide) copy).elim
        obtain ⟨m,cases,copy⟩ := smallRingResult ht (by omega) D ring deg
        rcases cases with rfl | rfl | rfl | ⟨rfl,lt⟩ | ⟨rfl,lt⟩
        · exact (exclude 3 (Or.inl rfl) copy).elim
        · exact (exclude 6 (Or.inr rfl) copy).elim
        · exact ⟨7,3,by decide,by decide,copy,Or.inl rfl⟩
        · have less : 2 < t := by
            by_contra! h
            exact lt.not_ge (Nat.pow_le_pow_right (by decide : 0 < 2) h)
          exact (noshort 2 (by decide) less copy).elim
        · have less : 3 < t := by
            by_contra! h
            exact lt.not_ge (Nat.pow_le_pow_right (by decide : 0 < 2) h)
          exact (noshort 3 (by decide) less copy).elim
    obtain ⟨n,k,hn,hk,⟨d⟩,lengths⟩ := goal
    let i : Fin n := ⟨0,by omega⟩
    obtain ⟨f,hf⟩ := trans (iso (d i))
    obtain ⟨d',hit⟩ := backToRoot (iso.toCopy.comp d) f ⟨i,hf.symm⟩
    exact ⟨n,k,d',hn,hk,hit,lengths⟩
  · push Not at trans
    obtain ⟨n,k,d,f,hn,hk,hit,lengths⟩ := partialOrbits V G r conn cubic bridges trans away
      ⟨t,ht,⟨c⟩⟩ (fun k hk => forcedOrbit (forced k hk))
    obtain ⟨d',h⟩ := backToRoot d f hit
    exact ⟨n,k,d',hn,hk,h,lengths⟩

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R2_H2_R1
