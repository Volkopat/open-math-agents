import OMAReductions.R_Erdos64_erdos_64_R3_H2_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
Contract the prescribed edge in the bipartite marked problem of PR #2529. PR #31004 motivates the marked bipartite case.
The contraction has one fewer vertex and becomes bipartite upon deletion of its
merged vertex. Every even simple cycle lifts at unchanged length, avoiding the
mark. The interior path between the two neighbors of the merged vertex has even
length, so both ends use the same original terminal. In particular a bipartite
counterexample to marked-edge avoidance would refute the ordinary conjecture.
Credit: @wispiANt.
-/
namespace OMA.R_Erdos64_erdos_64_R3_H2_R1_H1_R2
open SimpleGraph
open scoped Classical

def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (r : V),
    (∀ v, 3 ≤ G.degree v) → 4 ≤ G.degree r →
    (∃ color : V → Bool, ∀ u v, u ≠ r → v ≠ r → G.Adj u v → color u ≠ color v) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k

def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (a b : V),
    G.Adj b a → 3 ≤ G.minDegree →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ u ∈ S, u ≠ z) → (∃ v, v ∉ S) →
      ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, G.Adj u v) →
    (¬ ∃ color : V → Bool, ∀ u v, G.Adj u v → color u ≠ color v) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧
      ((c.length = 2^k ∧ s(b,a) ∉ c.edges) ∨ (c.length + 1 = 2^k ∧ s(b,a) ∈ c.edges))

/-- On a walk avoiding the exceptional vertex, endpoint colors agree exactly at even length. -/
theorem colorParity {V : Type} {K : SimpleGraph V} (z : V) (color : V → Bool)
    (proper : ∀ u v, u ≠ z → v ≠ z → K.Adj u v → color u ≠ color v)
    {u v : V} (p : K.Walk u v) (away : z ∉ p.support) :
    (color u = color v ↔ p.length % 2 = 0) := by
  induction p with
  | nil => simp
  | @cons u v w uv p ih =>
    have av : z ∉ p.support := fun h => away (by simp [h])
    have cu := proper u v (fun e => away (by simp [e]))
      (fun e => av (e ▸ p.start_mem_support)) uv
    have h := ih av
    simp only [Walk.length_cons]
    cases h₁ : color u <;> cases h₂ : color v <;> cases h₃ : color w <;>
      simp [h₁,h₂,h₃] at cu h ⊢ <;> omega

private theorem interiorEdges {V : Type} {K F : SimpleGraph V} {z : V}
    (awayEdge : ∀ u v, u ≠ z → v ≠ z → K.Adj u v → F.Adj u v)
    {u v : V} (p : K.Walk u v) (away : z ∉ p.support) :
    ∀ e ∈ p.edges, e ∈ F.edgeSet := by
  rintro ⟨i,j⟩ he
  exact awayEdge _ _ (fun h => away (h ▸ p.fst_mem_support_of_mem_edges he))
    (fun h => away (h ▸ p.snd_mem_support_of_mem_edges he)) (p.edges_subset_edgeSet he)

private theorem liftAt {V : Type} {K F : SimpleGraph V} {z u v : V}
    (zu : K.Adj z u) (vz : K.Adj v z) (p : K.Walk u v)
    (hc : (Walk.cons zu (p.concat vz)).IsCycle) (fu : F.Adj z u) (fv : F.Adj v z)
    (inside : ∀ e ∈ p.edges, e ∈ F.edgeSet) :
    ∃ d : F.Walk z z, d.IsCycle ∧ d.length = (Walk.cons zu (p.concat vz)).length := by
  let c := Walk.cons zu (p.concat vz)
  have valid : ∀ e ∈ c.edges, e ∈ F.edgeSet := by
    intro e he
    simp only [c,Walk.edges_cons,Walk.edges_concat,List.mem_cons,List.concat_eq_append,List.mem_append,
      List.not_mem_nil,or_false] at he
    rcases he with rfl | he | rfl
    · exact fu
    · exact inside _ he
    · exact fv
  exact ⟨c.transfer F valid,hc.transfer valid,c.length_transfer valid⟩

private theorem splitCycle {V : Type} (K F J : SimpleGraph V) (z : V) (color : V → Bool)
    (proper : ∀ u v, u ≠ z → v ≠ z → K.Adj u v → color u ≠ color v)
    (both : ∀ u v, u ≠ z → v ≠ z → K.Adj u v → F.Adj u v ∧ J.Adj u v)
    (star : ∀ u, K.Adj z u → (if color u then F.Adj z u else J.Adj z u))
    {w : V} (c : K.Walk w w) (hc : c.IsCycle) (even : c.length % 2 = 0) :
    (∃ w, ∃ d : F.Walk w w, d.IsCycle ∧ d.length = c.length) ∨
    (∃ w, ∃ d : J.Walk w w, d.IsCycle ∧ d.length = c.length) := by
  classical
  by_cases hz : z ∈ c.support
  · let rot := c.rotate z hz
    have rc : rot.IsCycle := hc.rotate hz
    have rl : rot.length = c.length := c.length_rotate _ _
    clear_value rot
    cases rot with
    | nil => exact (rc.not_nil .nil).elim
    | @cons _ u _ zu tail =>
      have tp : tail.IsPath := (Walk.cons_isCycle_iff ..).mp rc |>.1
      have nz : ¬ tail.Nil := by
        intro h
        exact zu.ne.symm h.eq
      have vz := tail.adj_penultimate nz
      let p := tail.dropLast
      have hp : p.concat vz = tail := Walk.concat_dropLast vz
      have away := ((Walk.concat_isPath_iff vz).mp (hp ▸ tp)).2
      have hlen := tail.length_dropLast_add_one nz
      have pe : p.length % 2 = 0 := by
        change tail.dropLast.length % 2 = 0
        rw [Walk.length_cons] at rl
        omega
      have same := (colorParity z color proper p away).2 pe
      have h₁ := star u zu
      have h₂ := star _ vz.symm
      have cyc : (Walk.cons zu (p.concat vz)).IsCycle := by rwa [hp]
      have len : (Walk.cons zu (p.concat vz)).length = c.length := by rwa [hp]
      cases h : color u
      · rw [← same,h] at h₂
        rw [h] at h₁
        obtain ⟨d,hd,dl⟩ := liftAt zu vz p cyc h₁ (show J.Adj _ _ from h₂).symm
          (interiorEdges (fun i j ia ja e => (both i j ia ja e).2) p away)
        exact Or.inr ⟨z,d,hd,dl.trans len⟩
      · rw [← same,h] at h₂
        rw [h] at h₁
        obtain ⟨d,hd,dl⟩ := liftAt zu vz p cyc h₁ (show F.Adj _ _ from h₂).symm
          (interiorEdges (fun i j ia ja e => (both i j ia ja e).1) p away)
        exact Or.inl ⟨z,d,hd,dl.trans len⟩
  · have valid := interiorEdges (fun i j ia ja e => (both i j ia ja e).1) c hz
    exact Or.inl ⟨w,c.transfer F valid,hc.transfer valid,c.length_transfer valid⟩

private theorem liftChart {V W : Type} (G : SimpleGraph V) (f : W → V)
    (inj : Function.Injective f) {a b : V} (miss : (∀ t, f t ≠ a) ∨ (∀ t, f t ≠ b))
    {w : W} (d : (G.comap f).Walk w w) (hd : d.IsCycle) :
    ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = d.length ∧ s(b,a) ∉ c.edges ∧ (a ∉ c.support ∨ b ∉ c.support) := by
  let hom : G.comap f →g G := ⟨f,fun h => h⟩
  let c := d.map hom
  have fresh (i : V) (h : ∀ t, f t ≠ i) : i ∉ c.support := by
    rw [show c.support = d.support.map hom from d.support_map hom]
    rintro hit
    obtain ⟨t,_,eq⟩ := List.mem_map.mp hit
    exact h t eq
  have omits := miss.imp (fresh a) (fresh b)
  exact ⟨_,c,hd.map inj,d.length_map hom,fun h => omits.elim
    (fun ha => ha (c.snd_mem_support_of_mem_edges h))
    (fun hb => hb (c.fst_mem_support_of_mem_edges h)),omits⟩

/-- Contract any edge of a two-colored graph of minimum degree three. Every even
simple cycle of the smaller graph lifts to a simple cycle avoiding that edge. -/
theorem contractMarked {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (ba : G.Adj b a) (floor : ∀ t, 3 ≤ G.degree t)
    (col : V → Bool) (proper : ∀ u v, G.Adj u v → col u ≠ col v) :
    let W := {t : V // t ≠ a}
    ∃ (K : SimpleGraph W) (z : W), Fintype.card W < Fintype.card V ∧
      (∀ t, 3 ≤ K.degree t) ∧ 4 ≤ K.degree z ∧
      (∃ color : W → Bool, ∀ u v, u ≠ z → v ≠ z → K.Adj u v → color u ≠ color v) ∧
      ∀ w (c : K.Walk w w), c.IsCycle → c.length % 2 = 0 →
        ∃ v, ∃ d : G.Walk v v, d.IsCycle ∧ d.length = c.length ∧ s(b,a) ∉ d.edges ∧
          (a ∉ d.support ∨ b ∉ d.support) := by
  classical
  let W := {t : V // t ≠ a}
  let z : W := ⟨b,ba.ne⟩
  let f (t : W) := t.val
  let g (t : W) := if t = z then a else t.val
  let π (v : V) : W := if h : v = a then z else ⟨v,h⟩
  have fa (t : W) : f t ≠ a := t.property
  have gb (t : W) : g t ≠ b := by
    by_cases h : t = z
    · simpa [g,h] using ba.ne.symm
    · simpa [g,h] using (fun e => h (Subtype.ext e) : t.val ≠ b)
  have gi : Function.Injective g := by
    intro t u eq
    by_cases ht : t = z <;> by_cases hu : u = z
    · exact ht.trans hu.symm
    · exact (u.property (by simpa [g,ht,hu] using eq.symm)).elim
    · exact (t.property (by simpa [g,ht,hu] using eq)).elim
    · exact Subtype.ext (by simpa [g,ht,hu] using eq)
  let F := G.comap f
  let J := G.comap g
  let K := F ⊔ J
  let : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  let color (t : W) := decide (col t.val = col a)
  have abCol := proper b a ba
  have common (v : V) (av : G.Adj a v) (bv : G.Adj b v) : False := by
    have ac := proper a v av
    have bc := proper b v bv
    cases h₁ : col a <;> cases h₂ : col b <;> cases h₃ : col v <;> simp_all
  have away {t u : W} (ht : t ≠ z) (hu : u ≠ z) (e : K.Adj t u) : G.Adj t.val u.val := by
    rcases e with h | h
    · exact h
    · simpa [J,comap_adj,g,ht,hu] using h
  have both (t u : W) (ht : t ≠ z) (hu : u ≠ z) (e : K.Adj t u) : F.Adj t u ∧ J.Adj t u := by
    have h := away ht hu e
    exact ⟨h,by simpa [J,comap_adj,g,ht,hu] using h⟩
  have colorOK (t u : W) (ht : t ≠ z) (hu : u ≠ z) (e : K.Adj t u) : color t ≠ color u := by
    have h := proper _ _ (away ht hu e)
    cases h₁ : col t.val <;> cases h₂ : col u.val <;> cases h₃ : col a <;> simp_all [color]
  have star (u : W) (e : K.Adj z u) : (if color u then F.Adj z u else J.Adj z u) := by
    have uz := e.ne.symm
    rcases e with h | h
    · have bad := proper b u h
      have eq : col u.val = col a := by
        cases h₁ : col u.val <;> cases h₂ : col a <;> cases h₃ : col b <;> simp_all
      simpa [color,eq] using h
    · have au : G.Adj a u.val := by simpa [J,comap_adj,g,uz] using h
      have ne := (proper a u au).symm
      simpa [color,ne] using h
  have adjFold (t : W) (ht : t ≠ z) (v : V) (tv : G.Adj t.val v) : K.Adj t (π v) := by
    by_cases va : v = a
    · subst v
      right
      simpa [J,comap_adj,π,g,ht] using tv
    · left
      simpa [F,comap_adj,f,π,va] using tv
  have off (t : W) (ht : t ≠ z) : 3 ≤ K.degree t := by
    have maps : Set.MapsTo π (G.neighborFinset t.val) (K.neighborFinset t) := by
      intro w hw
      exact (K.mem_neighborFinset ..).2 (adjFold t ht w ((G.mem_neighborFinset ..).1 hw))
    have inj : (↑(G.neighborFinset t.val) : Set V).InjOn π := by
      intro u hu v hv eq
      have tu := (G.mem_neighborFinset ..).1 hu
      have tv := (G.mem_neighborFinset ..).1 hv
      have e := congrArg Subtype.val eq
      by_cases ua : u = a <;> by_cases va : v = a
      · exact ua.trans va.symm
      · have bv : b = v := by simpa [π,ua,va,z] using e
        exact (common t (ua ▸ tu.symm) (bv ▸ tv.symm)).elim
      · have ub : u = b := by simpa [π,ua,va,z] using e
        exact (common t (va ▸ tv.symm) (ub ▸ tu.symm)).elim
      · simpa [π,ua,va] using e
    have bound := Finset.card_le_card_of_injOn π maps inj
    simpa only [card_neighborFinset_eq_degree] using (floor t).trans bound
  let A := (G.neighborFinset a).erase b
  let B := (G.neighborFinset b).erase a
  have aN (v) (hv : v ∈ A) : v ≠ b ∧ G.Adj a v := by simpa [A] using hv
  have bN (v) (hv : v ∈ B) : v ≠ a ∧ G.Adj b v := by simpa [B] using hv
  have outsideA {v} (h : v ∈ A ∪ B) : v ≠ a :=
    (Finset.mem_union.mp h).elim (fun hv => (aN v hv).2.ne.symm) (fun hv => (bN v hv).1)
  have distinct : Disjoint A B := Finset.disjoint_left.mpr fun _ hv hw => common _ (aN _ hv).2 (bN _ hw).2
  have rootMaps : Set.MapsTo π (↑(A ∪ B) : Set V) (K.neighborFinset z) := by
    intro v hv
    have va := outsideA hv
    apply (K.mem_neighborFinset ..).2
    rcases Finset.mem_union.mp hv with ha | hb
    · obtain ⟨vb,av⟩ := aN v ha
      have vz : (⟨v,va⟩ : W) ≠ z := fun e => vb (congrArg Subtype.val e)
      right
      simpa [J,comap_adj,π,g,va,vz] using av
    · left
      simpa [F,comap_adj,f,z,π,va] using (bN v hb).2
  have rootInj : (↑(A ∪ B) : Set V).InjOn π := by
    intro t ht u hu eq
    simpa [π,outsideA ht,outsideA hu] using congrArg Subtype.val eq
  have count := Finset.card_le_card_of_injOn π rootMaps rootInj
  have ac : A.card = G.degree a - 1 := by
    rw [show A = _ from rfl, Finset.card_erase_of_mem ((G.mem_neighborFinset a b).2 ba.symm),
      card_neighborFinset_eq_degree]
  have bc : B.card = G.degree b - 1 := by
    rw [show B = _ from rfl, Finset.card_erase_of_mem ((G.mem_neighborFinset b a).2 ba),
      card_neighborFinset_eq_degree]
  rw [Finset.card_union_of_disjoint distinct,ac,bc,card_neighborFinset_eq_degree] at count
  have root : 4 ≤ K.degree z := by
    have := floor a
    have := floor b
    omega
  refine ⟨K,z,Fintype.card_lt_of_injective_of_notMem f Subtype.val_injective
    (b := a) (fun ⟨u,h⟩ => fa u h),fun t => ?_,root,⟨color,colorOK⟩,?_⟩
  · by_cases h : t = z
    · exact h ▸ (by omega : 3 ≤ K.degree z)
    · exact off t h
  · intro w c hc he
    rcases splitCycle K F J z color colorOK (fun u v hu hv e => both u v hu hv e) star c hc he
        with ⟨_,d,hd,dl⟩ | ⟨_,d,hd,dl⟩
    · obtain ⟨v,p,hp,pl,miss⟩ := liftChart G f Subtype.val_injective (Or.inl fa) d hd (b := b)
      exact ⟨v,p,hp,pl.trans dl,miss⟩
    · obtain ⟨v,p,hp,pl,miss⟩ := liftChart G g gi (Or.inr gb) d hd (a := a)
      exact ⟨v,p,hp,pl.trans dl,miss⟩


/-- Failure of marked avoidance already supplies a smaller counterexample
to the ordinary (unmarked) conjecture. No connectivity hypothesis is needed. -/
theorem smallerCounterexample {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (ba : G.Adj b a) (floor : ∀ v, 3 ≤ G.degree v)
    (col : V → Bool) (proper : ∀ u v, G.Adj u v → col u ≠ col v)
    (obstruction : ∀ k v (c : G.Walk v v), 2 ≤ k → c.IsCycle → c.length = 2^k → s(b,a) ∈ c.edges) :
    let W := {v : V // v ≠ a}
    ∃ K : SimpleGraph W, Fintype.card W < Fintype.card V ∧ 3 ≤ K.minDegree ∧
      ∀ k w (c : K.Walk w w), 2 ≤ k → c.IsCycle → c.length ≠ 2^k := by
  classical
  obtain ⟨K,z,lt,deg,_,_,lift⟩ := contractMarked G ba floor col proper
  have : Nonempty {v : V // v ≠ a} := ⟨z⟩
  refine ⟨K,lt,K.le_minDegree_of_forall_le_degree 3 deg,?_⟩
  intro k w c hk hc hl
  have even : c.length % 2 = 0 := by
    rw [hl,show k = (k-1)+1 by omega,pow_succ]
    omega
  obtain ⟨v,d,hd,dl,miss,_⟩ := lift w c hc even
  exact miss (obstruction k v d hk hd (dl.trans hl))

/-- A verified order bound for the ordinary conjecture gives edge avoidance
one order higher for bipartite graphs. The numerical bound is an input. -/
theorem avoidBelow (n : ℕ)
    (small : ∀ (W : Type) (K : SimpleGraph W) [Fintype W] [DecidableRel K.Adj],
      Fintype.card W ≤ n → 3 ≤ K.minDegree →
      ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V}
    (ba : G.Adj b a) (floor : ∀ v, 3 ≤ G.degree v) (size : Fintype.card V ≤ n+1)
    (col : V → Bool) (proper : ∀ u v, G.Adj u v → col u ≠ col v) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k ∧ s(b,a) ∉ c.edges ∧
      (a ∉ c.support ∨ b ∉ c.support) := by
  classical
  obtain ⟨K,z,lt,deg,_,_,lift⟩ := contractMarked G ba floor col proper
  have : Nonempty {t : V // t ≠ a} := ⟨z⟩
  obtain ⟨k,w,c,hk,hc,hl⟩ := small _ K (by omega) (K.le_minDegree_of_forall_le_degree 3 deg)
  have even : c.length % 2 = 0 := by
    rw [hl,show k = (k-1)+1 by omega,pow_succ]
    omega
  obtain ⟨v,d,hd,dl,miss⟩ := lift w c hc even
  exact ⟨k,v,d,hk,hd,dl.trans hl,miss⟩

/-- A side of a two-edge cut with two nonadjacent opposite-color terminals.
Close the side by a virtual edge, then find a cycle avoiding it. The other
side of the cut is unrestricted. Ducoffe–Dumitru (arXiv:2609.28594) report the
ordinary bound n = 40; that external computation is not used as a Lean axiom. -/
theorem cycleOnBank (n : ℕ)
    (small : ∀ (W : Type) (K : SimpleGraph W) [Fintype W] [DecidableRel K.Adj],
      Fintype.card W ≤ n → 3 ≤ K.minDegree →
      ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V}
    (nonedge : ¬ G.Adj a b) (da : 2 ≤ G.degree a) (db : 2 ≤ G.degree b)
    (interior : ∀ t, t ≠ a → t ≠ b → 3 ≤ G.degree t) (size : Fintype.card V ≤ n+1)
    (col : V → Bool) (opposite : col a ≠ col b)
    (proper : ∀ u v, G.Adj u v → col u ≠ col v) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
  classical
  have ab : a ≠ b := fun e => opposite (congrArg col e)
  let K := G ⊔ fromEdgeSet {s(b,a)}
  have adj (u v : V) : K.Adj u v ↔ G.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a) :=
    OMA.R_Erdos64_erdos_64_R3_H2_R1.adjacent_or_mark ab
  have ba : K.Adj b a := (adj b a).2 (Or.inr (Or.inr ⟨rfl,rfl⟩))
  have mono : G ≤ K := le_sup_left
  have gain {x y : V} (xy : K.Adj x y) (old : ¬ G.Adj x y) : G.degree x + 1 ≤ K.degree x := by
    have sub : insert y (G.neighborFinset x) ⊆ K.neighborFinset x := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact (K.mem_neighborFinset ..).2 xy
      · exact (K.mem_neighborFinset ..).2 (mono ((G.mem_neighborFinset ..).1 ht))
    have bound := Finset.card_le_card sub
    rwa [Finset.card_insert_of_notMem (fun h => old ((G.mem_neighborFinset ..).1 h)),
      card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at bound
  have deg (t : V) : 3 ≤ K.degree t := by
    by_cases h : t = a
    · subst t
      have := gain ba.symm nonedge
      omega
    by_cases h' : t = b
    · subst t
      have := gain ba (fun e => nonedge e.symm)
      omega
    exact (interior t h h').trans (G.degree_le_of_le mono)
  have colorOK (u v : V) (h : K.Adj u v) : col u ≠ col v := by
    rcases (adj u v).1 h with h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    exacts [proper _ _ h,opposite,opposite.symm]
  obtain ⟨k,v,c,hk,hc,hl,miss,_⟩ := avoidBelow n small K ba deg size col colorOK
  have valid := OMA.R_Erdos64_erdos_64_R3_H2_R1.forgetAddedEdge c miss
  exact ⟨k,v,c.transfer G valid,hk,hc.transfer valid,(c.length_transfer valid).trans hl⟩

private theorem oneLost {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Set V) [DecidablePred (· ∈ W)] (v : W) (d : V) (hd : d ∉ W)
    (vd : G.Adj v d) (only : ∀ t, G.Adj v t → t ∉ W → t = d) :
    (G.induce W).degree v + 1 = G.degree v.val := by
  classical
  let e := Function.Embedding.subtype W
  have eq : G.neighborFinset v.val = insert d (((G.induce W).neighborFinset v).map e) := by
    ext t
    simp only [mem_neighborFinset,Finset.mem_insert,Finset.mem_map]
    constructor
    · intro h
      by_cases ht : t ∈ W
      · exact Or.inr ⟨⟨t,ht⟩,h,rfl⟩
      · exact Or.inl (only t h ht)
    · rintro (rfl | ⟨w,hw,rfl⟩)
      · exact vd
      · exact hw
  have fresh : d ∉ ((G.induce W).neighborFinset v).map e := by
    rintro h
    obtain ⟨w,_,hw⟩ := Finset.mem_map.mp h
    exact hd (hw ▸ w.property)
  rw [← G.card_neighborFinset_eq_degree v.val,eq,Finset.card_insert_of_notMem fresh,Finset.card_map,
    card_neighborFinset_eq_degree]


private theorem networkDegrees {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Set V) [DecidablePred (· ∈ W)] (x y : W) (xy : x ≠ y) (dx dy : V)
    (dxo : dx ∉ W) (dyo : dy ∉ W) (xd : G.Adj x dx) (yd : G.Adj y dy)
    (ports : ∀ u : W, ∀ v ∉ W, G.Adj u v → (u = x ∧ v = dx) ∨ (u = y ∧ v = dy))
    (cub : ∀ u : W, G.degree u.val = 3) :
    (G.induce W).degree x = 2 ∧ (G.induce W).degree y = 2 ∧
      ∀ u, u ≠ x → u ≠ y → (G.induce W).degree u = 3 := by
  classical
  constructor
  · have h := oneLost G W x dx dxo xd (fun t ht out =>
      (ports x t out ht).elim And.right (fun e => (xy e.1).elim))
    rw [cub] at h
    omega
  constructor
  · have h := oneLost G W y dy dyo yd (fun t ht out =>
      (ports y t out ht).elim (fun e => (xy e.1.symm).elim) And.right)
    rw [cub] at h
    omega
  · intro u ux uy
    rw [degree_induce_of_neighborSet_subset (show G.neighborSet u.val ⊆ W by
      intro t ht
      by_contra out
      exact (ports u t out ht).elim (fun h => ux h.1) (fun h => uy h.1))]
    exact cub u


/-- In a cubic cut side, adjacency between the deficient terminals can also
be handled. Delete both terminals; their exits either form a square with
them or give a smaller side with nonadjacent terminals. -/
theorem cycleOnCubicBank (n : ℕ)
    (small : ∀ (W : Type) (K : SimpleGraph W) [Fintype W] [DecidableRel K.Adj],
      Fintype.card W ≤ n → 3 ≤ K.minDegree →
      ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V}
    (da : G.degree a = 2) (db : G.degree b = 2)
    (interior : ∀ t, t ≠ a → t ≠ b → G.degree t = 3) (size : Fintype.card V ≤ n+1)
    (col : V → Bool) (opposite : col a ≠ col b)
    (proper : ∀ u v, G.Adj u v → col u ≠ col v) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
  classical
  by_cases edge : G.Adj a b
  · have second {i j : V} (ij : G.Adj i j) (deg : G.degree i = 2) :
        ∃ x, x ≠ j ∧ G.Adj i x ∧ ∀ t, G.Adj i t → t = j ∨ t = x := by
      have je := (G.mem_neighborFinset ..).2 ij
      have card : ((G.neighborFinset i).erase j).card = 1 := by
        rw [Finset.card_erase_of_mem je,card_neighborFinset_eq_degree,deg]
      obtain ⟨x,hx⟩ := Finset.card_eq_one.mp card
      have spec (t : V) : t ≠ j ∧ G.Adj i t ↔ t = x := by
        simpa using (show t ∈ (G.neighborFinset i).erase j ↔ t ∈ ({x} : Finset V) by rw [hx])
      exact ⟨x,((spec x).2 rfl).1,((spec x).2 rfl).2,fun t h => or_iff_not_imp_left.mpr
        (fun tj => (spec t).1 ⟨tj,h⟩)⟩
    obtain ⟨x,xb,ax,atA⟩ := second edge da
    obtain ⟨y,ya,by',atB⟩ := second edge.symm db
    have ac := proper _ _ ax
    have bc := proper _ _ by'
    have diff : col x ≠ col y := by
      cases h₁ : col a <;> cases h₂ : col b <;> cases h₃ : col x <;> cases h₄ : col y <;> simp_all
    have xy : x ≠ y := fun h => diff (congrArg col h)
    by_cases link : G.Adj x y
    · let c : G.Walk a a := .cons ax (.cons link (.cons by'.symm (.cons edge.symm .nil)))
      refine ⟨2,a,c,by decide,?_,rfl⟩
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      constructor
      · simp [c,Walk.cons_isPath_iff,ax.ne.symm,xb,xy,by'.ne.symm,ya,edge.ne.symm]
      · exact (by decide : 3 ≤ 4)
    let W : Set V := {t | t ≠ a ∧ t ≠ b}
    let X : W := ⟨x,ax.ne.symm,xb⟩
    let Y : W := ⟨y,ya,by'.ne.symm⟩
    have ports (u : W) (v : V) (out : v ∉ W) (uv : G.Adj u v) :
        (u = X ∧ v = a) ∨ (u = Y ∧ v = b) := by
      by_cases va : v = a
      · subst v
        rcases atA _ uv.symm with h | h
        · exact (u.property.2 h).elim
        · exact Or.inl ⟨Subtype.ext h,rfl⟩
      have vb : v = b := by by_contra h; exact out ⟨va,h⟩
      subst v
      rcases atB _ uv.symm with h | h
      · exact (u.property.1 h).elim
      · exact Or.inr ⟨Subtype.ext h,rfl⟩
    obtain ⟨dx,dy,others⟩ := networkDegrees G W X Y (fun h => xy (congrArg Subtype.val h))
      a b (fun h => h.1 rfl) (fun h => h.2 rfl) ax.symm by'.symm ports (fun u => interior u u.property.1 u.property.2)
    obtain ⟨k,v,c,hk,hc,hl⟩ := cycleOnBank n small (G.induce W) (a := X) (b := Y) link
      dx.ge dy.ge (fun t tx ty => (others t tx ty).ge)
      ((Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans size)
      (fun t => col t.val) diff (fun u v h => proper u v h)
    exact ⟨k,v.val,c.map (Embedding.induce W).toHom,hk,hc.map Subtype.val_injective,(c.length_map _).trans hl⟩
  · exact cycleOnBank n small G edge da.ge db.ge (fun t ha hb => (interior t ha hb).ge)
      size col opposite proper


private theorem sumNeighbors {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq V] (S : Finset V) (u : V) :
    (∑ v ∈ S, if G.Adj u v then 1 else 0) = (G.neighborFinset u ∩ S).card := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,smul_eq_mul,mul_one]
  congr 1
  ext v
  simp [and_comm]

private theorem oneTerm {V : Type} (S : Finset V) (d : V → ℕ) (one : ∑ u ∈ S, d u = 1) :
    ∃ x ∈ S, d x = 1 ∧ ∀ y ∈ S, y ≠ x → d y = 0 := by
  classical
  obtain ⟨x,hx,pos⟩ : ∃ x ∈ S, d x ≠ 0 := by
    by_contra! h
    have h0 := Finset.sum_eq_zero h
    omega
  have p := S.sum_erase_add d hx
  have dx : d x = 1 := by omega
  refine ⟨x,hx,dx,?_⟩
  intro y hy ne
  have q := (S.erase x).sum_erase_add d (Finset.mem_erase.mpr ⟨ne,hy⟩)
  omega

/-- Two outgoing incidences in a cubic bipartite side belong to distinct
vertices of opposite colors. Counting degrees in each class determines this
even when the endpoints of the cut have not been specified. -/
theorem twoDeficits {V : Type} [Fintype V] (K : SimpleGraph V) [DecidableRel K.Adj]
    (col : V → Bool) (proper : ∀ u v, K.Adj u v → col u ≠ col v) (d : V → ℕ)
    (cubic : ∀ u, K.degree u + d u = 3) (cut : ∑ u, d u = 2) :
    ∃ a b, col a ≠ col b ∧ K.degree a = 2 ∧ K.degree b = 2 ∧
      ∀ u, u ≠ a → u ≠ b → K.degree u = 3 := by
  classical
  let L := Finset.univ.filter (fun u => col u = false)
  have left (u : V) : u ∈ L ↔ col u = false := by simp [L]
  have right (u : V) : u ∈ Lᶜ ↔ col u ≠ false := by simp [L]
  have row (u : V) (ul : u ∈ L) :
      (∑ v ∈ Lᶜ, if K.Adj u v then 1 else 0) = K.degree u := by
    rw [sumNeighbors,Finset.inter_eq_left.mpr,card_neighborFinset_eq_degree]
    intro v hv
    exact (right v).2 (fun vl => proper u v ((K.mem_neighborFinset ..).1 hv) (((left u).1 ul).trans vl.symm))
  have column (v : V) (vr : v ∈ Lᶜ) :
      (∑ u ∈ L, if K.Adj u v then 1 else 0) = K.degree v := by
    simp_rw [show ∀ u, K.Adj u v ↔ K.Adj v u from fun u => K.adj_comm u v]
    rw [sumNeighbors,Finset.inter_eq_left.mpr,card_neighborFinset_eq_degree]
    intro u hu
    apply (left u).2
    have e := proper v u ((K.mem_neighborFinset ..).1 hu)
    have ne := (right v).1 vr
    cases h₁ : col v <;> cases h₂ : col u <;> simp_all
  have balance : (∑ u ∈ L, K.degree u) = ∑ v ∈ Lᶜ, K.degree v := by
    rw [← Finset.sum_congr rfl row,Finset.sum_comm]
    exact Finset.sum_congr rfl column
  have counts (T : Finset V) : (∑ u ∈ T, K.degree u) + (∑ u ∈ T, d u) = T.card * 3 := by
    rw [← Finset.sum_add_distrib]
    simp [cubic]
  have hL := counts L
  have hR := counts Lᶜ
  have total := L.sum_add_sum_compl d
  have dl : ∑ u ∈ L, d u = 1 := by omega
  have dr : ∑ u ∈ Lᶜ, d u = 1 := by omega
  obtain ⟨a,al,ad,ao⟩ := oneTerm L d dl
  obtain ⟨b,br,bd,bo⟩ := oneTerm Lᶜ d dr
  have ac := cubic a
  have bc := cubic b
  refine ⟨a,b,fun e => (right b).1 br (e ▸ (left a).1 al),by omega,by omega,?_⟩
  intro u ua ub
  have du : d u = 0 := by
    by_cases h : u ∈ L
    · exact ao u h ua
    · exact bo u (Finset.mem_compl.mpr h) ub
  have := cubic u
  omega

/-- A small bipartite side of an actual two-edge cut contains a dyadic cycle.
Only vertices on the chosen side must have ambient degree three. -/
theorem cycleInsideTwoEdgeCut (n : ℕ)
    (small : ∀ (W : Type) (K : SimpleGraph W) [Fintype W] [DecidableRel K.Adj],
      Fintype.card W ≤ n → 3 ≤ K.minDegree →
      ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (cubic : ∀ u ∈ S, G.degree u = 3) (size : S.card ≤ n+1)
    (cut : (∑ u ∈ S, ∑ v ∈ Sᶜ, if G.Adj u v then 1 else 0) = 2)
    (col : S → Bool) (proper : ∀ u v : S, G.Adj u.val v.val → col u ≠ col v) :
    ∃ (k : ℕ) (u : S) (c : (G.induce (S : Set V)).Walk u u), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
  classical
  let K := G.induce (S : Set V)
  let d (u : V) := ∑ v ∈ Sᶜ, if G.Adj u v then 1 else 0
  have row (u : S) : K.degree u = ∑ v ∈ S, if G.Adj u.val v then 1 else 0 := by
    rw [sumNeighbors,← card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun w _ => w.val)
    · intro w hw
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset ..).2 ((K.mem_neighborFinset ..).1 hw),w.property⟩
    · intro w _ v _ h
      exact Subtype.ext h
    · intro v hv
      obtain ⟨uv,vs⟩ := Finset.mem_inter.mp hv
      exact ⟨⟨v,vs⟩,(K.mem_neighborFinset ..).2 ((G.mem_neighborFinset ..).1 uv),rfl⟩
  have deg (u : S) : K.degree u + d u = 3 := by
    rw [row]
    change (∑ v ∈ S, if G.Adj u.val v then 1 else 0) +
      (∑ v ∈ Sᶜ, if G.Adj u.val v then 1 else 0) = 3
    rw [Finset.sum_add_sum_compl,sumNeighbors,Finset.inter_univ,card_neighborFinset_eq_degree,cubic u u.property]
  have total : ∑ u : S, d u = 2 := (S.sum_subtype (fun _ => Iff.rfl) d).symm.trans cut
  obtain ⟨a,b,ab,da,db,others⟩ := twoDeficits K col proper (fun u => d u.val) deg total
  exact cycleOnCubicBank n small K da db others (by simpa using size) col ab proper

/-- Taking the smaller side doubles the range of the ordinary order bound
for cubic bipartite graphs having a two-edge cut. -/
theorem cubicBipartiteTwoEdgeCut (n : ℕ)
    (small : ∀ (W : Type) (K : SimpleGraph W) [Fintype W] [DecidableRel K.Adj],
      Fintype.card W ≤ n → 3 ≤ K.minDegree →
      ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (cubic : ∀ u, G.degree u = 3) (size : Fintype.card V ≤ 2*n+3)
    (cut : (∑ u ∈ S, ∑ v ∈ Sᶜ, if G.Adj u v then 1 else 0) = 2)
    (col : V → Bool) (proper : ∀ u v, G.Adj u v → col u ≠ col v) :
    ∃ (k : ℕ) (u : V) (c : G.Walk u u), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
  classical
  have solve (T : Finset V) (bound : T.card ≤ n+1)
      (edges : (∑ u ∈ T, ∑ v ∈ Tᶜ, if G.Adj u v then 1 else 0) = 2) :
      ∃ (k : ℕ) (u : V) (c : G.Walk u u), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
    obtain ⟨k,u,c,hk,hc,hl⟩ := cycleInsideTwoEdgeCut n small G T (fun u _ => cubic u)
      bound edges (fun u => col u.val) (fun u v h => proper u v h)
    exact ⟨k,u.val,c.map (Embedding.induce (T : Set V)).toHom,hk,hc.map Subtype.val_injective,
      (c.length_map _).trans hl⟩
  by_cases h : S.card ≤ n+1
  · exact solve S h cut
  · apply solve Sᶜ (by rw [Finset.card_compl]; omega)
    rw [compl_compl,Finset.sum_comm]
    convert cut using 1
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    simp only [G.adj_comm v u]

/-- A cubic bipartite counterexample with a two-edge cut would force an
ordinary counterexample on fewer than half as many vertices. -/
theorem counterexampleBelowHalf {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (cubic : ∀ u, G.degree u = 3)
    (cut : (∑ u ∈ S, ∑ v ∈ Sᶜ, if G.Adj u v then 1 else 0) = 2)
    (col : V → Bool) (proper : ∀ u v, G.Adj u v → col u ≠ col v)
    (bad : ¬ ∃ (k : ℕ) (u : V) (c : G.Walk u u), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k) :
    ∃ (W : Type) (_ : Fintype W) (K : SimpleGraph W) (_ : DecidableRel K.Adj),
      Fintype.card W ≤ Fintype.card V / 2 - 1 ∧ 3 ≤ K.minDegree ∧
      ¬ ∃ (k : ℕ) (u : W) (c : K.Walk u u), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
  classical
  by_contra noSmaller
  apply bad
  apply cubicBipartiteTwoEdgeCut (Fintype.card V / 2 - 1) _ G S cubic (by omega) cut col proper
  intro W K finite dec order degree
  by_contra badK
  exact noSmaller ⟨W,finite,K,dec,order,degree,badK⟩

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R3_H2_R1.H1 := by
  intro smaller odd V G _ _ a b ba min cuts
  classical
  by_cases h : ∃ col : V → Bool, ∀ u v, G.Adj u v → col u ≠ col v
  · obtain ⟨col,proper⟩ := h
    obtain ⟨K,z,_,floor,high,colors,lift⟩ :=
      contractMarked G ba (fun t => min.trans (G.minDegree_le_degree t)) col proper
    obtain ⟨k,w,c,hk,hc,hl⟩ := smaller _ K z floor high colors
    have even : c.length % 2 = 0 := by
      rw [hl,show k = (k-1)+1 by omega,pow_succ]
      omega
    obtain ⟨v,d,hd,dl,miss,_⟩ := lift w c hc even
    exact ⟨k,v,d,hk,hd,Or.inl ⟨dl.trans hl,miss⟩⟩
  · exact odd V G a b ba min cuts h

end OMA.R_Erdos64_erdos_64_R3_H2_R1_H1_R2
