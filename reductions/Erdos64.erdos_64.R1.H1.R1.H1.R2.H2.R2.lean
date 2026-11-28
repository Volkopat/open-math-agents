import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R2
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.GroupTheory.Sylow
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic.IntervalCases

/-!
Reduce the forced-root step of PR #27543 by rerouting a dyadic cycle along a
third internally disjoint path. The rebuilt cycles are tracked with exact
vertex ranges. The transitive case is discharged here using Chad Mazzola's
merged half-order and rooted asymmetry proof from PR #28718
(ff36b7b18d9e661ecc638cda828fffeb38bec073). The site allows only Mathlib
imports after the parent import, so its necessary lemmas are included.
-/
namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R2_H2_R2
open SimpleGraph

/-- Proper root orbit of at most two vertices. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (r : V),
    G.Connected → (∀ v, G.degree v = 3) →
    (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a,b)) →
    (∃ v, ∀ f : G ≃g G, f r ≠ v) →
    (∀ n, n = 3 ∨ n = 6 → ∀ c : (cycleGraph n).Copy G, ∀ f : G ≃g G, f r ∉ Set.range c) →
    (∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G) →
    (∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G, ∀ f : G ≃g G, f r ∈ Set.range c) →
    ({v | ∃ f : G ≃g G, f r=v}.ncard ≤ 2) →
    (let dyadic := fun d : ℕ => ∃ k : ℕ, 2 ≤ k ∧ d = 2^k
     let near := fun d : ℕ => 3 ≤ d ∧ ∃ k : ℕ, 2 ≤ k ∧ (d+1=2^k ∨ d+2=2^k)
     ∀ (x y : V) (A B P : List V), (x::y::(A++B++P)).Nodup →
       (∀ L ∈ [A,B,P], (x::(L++[y])).IsChain G.Adj) →
       dyadic (A.length+B.length+2) →
       (near (A.length+P.length+2) →
         (∀ f : G ≃g G, f r ∈ B) ∧ ¬ near (B.length+P.length+2)) ∧
       (dyadic (A.length+P.length+2) → dyadic (B.length+P.length+2) →
         ∀ f : G ≃g G, f r = x ∨ f r = y)) →
    ∃ (n k : ℕ) (c : (cycleGraph n).Copy G) (f : G ≃g G),
      3 ≤ n ∧ 2 ≤ k ∧ f r ∈ Set.range c ∧ (n+1=2^k ∨ n+2=2^k)

/-- Proper root orbit of at least three vertices. -/
def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (r : V),
    G.Connected → (∀ v, G.degree v = 3) →
    (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a,b)) →
    (∃ v, ∀ f : G ≃g G, f r ≠ v) →
    (∀ n, n = 3 ∨ n = 6 → ∀ c : (cycleGraph n).Copy G, ∀ f : G ≃g G, f r ∉ Set.range c) →
    (∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G) →
    (∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G, ∀ f : G ≃g G, f r ∈ Set.range c) →
    (3 ≤ {v | ∃ f : G ≃g G, f r=v}.ncard) →
    (∀ (k : ℕ), 2 ≤ k → ∀ (c : (cycleGraph (2^k)).Copy G) (x y : Fin (2^k)),
      (x=y ∨ 3 ≤ k) → ¬ (∀ j, (∃ f : G ≃g G, f r=c j) ↔ j≠x ∧ j≠y)) →
    (∀ (k : ℕ), 3 ≤ k → ∀ (c : (cycleGraph (2^k)).Copy G) (B : Finset (Fin (2^k))),
      B.card = 3 → ¬ (∀ j, (∃ f : G ≃g G, f r = c j) ↔ j ∉ B)) →
    (let O : Set V := {v | ∃ f : G ≃g G, f r = v}
     ∀ (k : ℕ), 4 ≤ k → ∀ (c : (cycleGraph (2^k)).Copy G) (B : Finset (Fin (2^k))),
       B.card = 4 → (∀ j, c j ∈ O ↔ j ∉ B) →
       {i | i ∉ B ∧ i+1 ∈ B}.ncard ≠ 2 ∧
       (Nat.card (G.induce O).ConnectedComponent = 1 ∨
         (Nat.card (G.induce O).ConnectedComponent = 3 ∧ Even k ∧ 6 ≤ k))) →
    (∀ (k d : ℕ), 2 ≤ k → 1 ≤ d → d+3 ≤ 2^k →
      ∀ (c : (cycleGraph (2^k)).Copy G) (start : Fin (2^k)),
        (∀ i : Fin (2^k), (∃ g : G ≃g G, g r = c (i+start)) ↔ d ≤ i.val) →
        ∀ s : ℕ, 2 ≤ s → d+2 ≠ 2^s ∧ d+3 ≠ 2^s ∧ d+4 ≠ 2^s) →
    (let dyadic := fun d : ℕ => ∃ k : ℕ, 2 ≤ k ∧ d = 2^k
     let near := fun d : ℕ => 3 ≤ d ∧ ∃ k : ℕ, 2 ≤ k ∧ (d+1=2^k ∨ d+2=2^k)
     ∀ (x y : V) (A B P : List V), (x::y::(A++B++P)).Nodup →
       (∀ L ∈ [A,B,P], (x::(L++[y])).IsChain G.Adj) →
       dyadic (A.length+B.length+2) →
       (near (A.length+P.length+2) →
         (∀ f : G ≃g G, f r ∈ B) ∧ 3 ≤ B.length ∧ ¬ near (B.length+P.length+2)) ∧
       (dyadic (A.length+P.length+2) → ¬ dyadic (B.length+P.length+2))) →
    ∃ (n k : ℕ) (c : (cycleGraph n).Copy G) (f : G ≃g G),
      3 ≤ n ∧ 2 ≤ k ∧ f r ∈ Set.range c ∧ (n+1=2^k ∨ n+2=2^k)

/-- The cyclic-list argument of PR #27543, with an exact vertex range. -/
theorem exactRing {V : Type*} (G : SimpleGraph V) (l : List V)
    (large : 3 ≤ l.length) (distinct : l.Nodup) (path : l.IsChain G.Adj)
    (close : ∀ h : l ≠ [], G.Adj (l.getLast h) (l.head h)) :
    ∃ c : (cycleGraph l.length).Copy G, ∀ v, v ∈ l ↔ v ∈ Set.range c := by
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
  intro v
  exact List.mem_iff_get

private theorem orbitPathEndpoints {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (conn : G.Connected) (cubic : ∀ v, G.degree v = 3)
    (proper : ∃ v, ∀ f : G ≃g G, f r ≠ v)
    (l : List V) (large : 3 ≤ l.length) (distinct : l.Nodup)
    (chain : l.IsChain G.Adj) (covers : ∀ v, v ∈ l ↔ ∃ f : G ≃g G, f r = v) :
    ∀ h : l ≠ [], G.Adj (l.getLast h) (l.head h) := by
  classical
  have root : r ∈ l := (covers _).mpr ⟨SimpleGraph.Iso.refl, rfl⟩
  have invariant (f : G ≃g G) (v : V) : f v ∈ l ↔ v ∈ l := by
    rw [covers,covers]
    constructor
    · rintro ⟨g,h⟩
      exact ⟨g.trans f.symm,by change f.symm (g r)=v; rw [h,f.symm_apply_apply]⟩
    · rintro ⟨g,h⟩
      exact ⟨g.trans f,by change f (g r)=f v; rw [h]⟩
  have move (x y : V) (hx : x∈l) (hy : y∈l) : ∃ f : G ≃g G, f x=y := by
    obtain ⟨g,hg⟩ := (covers _).mp hx
    obtain ⟨h,hh⟩ := (covers _).mp hy
    exact ⟨g.symm.trans h,by change h (g.symm x)=y; rw [←hg,g.symm_apply_apply,hh]⟩
  obtain ⟨outside,ho⟩ := proper
  have exitEdge : ∃ x∈l, ∃ z, z∉l ∧ G.Adj x z := by
    by_contra! closed
    obtain ⟨walk⟩ := conn.preconnected r outside
    have follow {a b : V} (p : G.Walk a b) (ha : a∈l) : b∈l := by
      induction p with
      | nil => exact ha
      | cons e _ ih =>
        apply ih
        by_contra missing
        exact closed _ ha _ missing e
    obtain ⟨f,h⟩ := (covers _).mp (follow walk root)
    exact ho f h
  obtain ⟨u,hu,z,hz,uz⟩ := exitEdge
  have third (x : V) (hx : x∈l) : ∃ w, w∉l ∧ G.Adj x w := by
    obtain ⟨f,eq⟩ := move u x hu hx
    exact ⟨f z,fun h => hz ((invariant f z).mp h),eq ▸ f.map_rel_iff.mpr uz⟩
  have sat (x a b w : V) (hx : x∈l) (ha : a∈l) (hb : b∈l) (hw : w∈l)
      (xa : G.Adj x a) (xb : G.Adj x b) (xw : G.Adj x w) (ab : a≠b) :
      w=a ∨ w=b := by
    by_contra! h
    obtain ⟨t,ht,xt⟩ := third x hx
    have subset : ({a,b,w,t} : Finset V) ⊆ G.neighborFinset x := by
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl|rfl|rfl <;> simpa
    have bound := Finset.card_le_card subset
    have at' : a≠t := fun e => ht (e ▸ ha)
    have bt : b≠t := fun e => ht (e ▸ hb)
    have wt : w≠t := fun e => ht (e ▸ hw)
    simp [ab,Ne.symm h.1,Ne.symm h.2,at',bt,wt,cubic] at bound
  let e := l.get
  have mem (i : Fin l.length) : e i ∈ l := List.get_mem ..
  have inj : Function.Injective e := distinct.injective_get
  let i₀ : Fin l.length := ⟨0,by omega⟩
  let i₁ : Fin l.length := ⟨1,by omega⟩
  let i₂ : Fin l.length := ⟨2,by omega⟩
  let last : Fin l.length := ⟨l.length-1,by omega⟩
  have step (i j : Fin l.length) (h : j.val=i.val+1) : G.Adj (e i) (e j) := by
    simpa only [e,List.get_eq_getElem,h] using chain.getElem i.val (by omega)
  obtain ⟨f,hf⟩ := move (e i₁) (e i₀) (mem _) (mem _)
  have pair (i : Fin l.length) (hi : G.Adj (e i₁) (e i)) :
      G.Adj (e i₀) (f (e i)) := hf ▸ f.map_rel_iff.mpr hi
  have other : ∃ j : Fin l.length, j≠i₁ ∧ G.Adj (e i₀) (e j) := by
    have find (i : Fin l.length) : ∃ j, e j = f (e i) :=
      List.mem_iff_get.mp ((invariant f _).mpr (mem i))
    obtain ⟨a,ha⟩ := find i₀
    obtain ⟨b,hb⟩ := find i₂
    by_cases h : a=i₁
    · refine ⟨b,?_,hb ▸ pair _ (step i₁ i₂ rfl)⟩
      intro eq
      have same := inj (f.injective (ha.symm.trans ((eq.trans h.symm) ▸ hb)))
      exact (by decide : (0:ℕ)≠2) (congrArg Fin.val same)
    · exact ⟨a,h,ha ▸ pair _ (step i₀ i₁ rfl).symm⟩
  obtain ⟨j,ne,edge⟩ := other
  have endpt : j=last := by
    by_contra h
    have pos : j.val≠0 := fun eq => edge.ne (congrArg e (Fin.ext eq.symm))
    have mid : j.val≠1 := fun eq => ne (Fin.ext eq)
    have top : j.val≠l.length-1 := fun eq => h (Fin.ext eq)
    let a : Fin l.length := ⟨j.val-1,by omega⟩
    let b : Fin l.length := ⟨j.val+1,by omega⟩
    have ab : e a≠e b := by
      intro q
      have t := congrArg Fin.val (inj q)
      dsimp [a,b] at t
      omega
    rcases sat _ _ _ _ (mem j) (mem a) (mem b) (mem i₀)
        (step a j (by dsimp [a]; omega)).symm (step j b rfl) edge.symm ab with q|q <;>
      have t := congrArg Fin.val (inj q) <;> dsimp [a,b,i₀] at t <;> omega
  have close (h : l≠[]) : G.Adj (l.getLast h) (l.head h) := by
    subst j
    simpa [e,last,i₀,List.getLast_eq_getElem,List.head_eq_getElem] using edge.symm
  exact close

/-- A simple path spanning a proper automorphism orbit in a connected cubic
graph closes up as soon as it has at least three vertices. -/
theorem orbitPathCloses {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (conn : G.Connected) (cubic : ∀ v, G.degree v = 3)
    (proper : ∃ v, ∀ f : G ≃g G, f r ≠ v)
    (l : List V) (large : 3 ≤ l.length) (distinct : l.Nodup)
    (chain : l.IsChain G.Adj) (covers : ∀ v, v ∈ l ↔ ∃ f : G ≃g G, f r = v) :
    ∃ c : (cycleGraph l.length).Copy G, r ∈ Set.range c := by
  obtain ⟨c,h⟩ := exactRing G l large distinct chain (orbitPathEndpoints G r conn cubic proper l
    large distinct chain covers)
  exact ⟨c,(h _).mp ((covers r).mpr ⟨SimpleGraph.Iso.refl,rfl⟩)⟩

/-- A cyclic interval of orbit vertices can be read from any starting label.
If its length is one or two below a power of two, closing the interval gives
the required cycle through the original root. -/
theorem orbitIntervalSolves {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (conn : G.Connected) (cubic : ∀ v, G.degree v = 3)
    (proper : ∃ v, ∀ f : G ≃g G, f r ≠ v)
    {n m k : ℕ} (c : (cycleGraph n).Copy G) (start : Fin n)
    (large : 3 ≤ m) (fits : m ≤ n) (hk : 2 ≤ k) (near : m+1 = 2^k ∨ m+2 = 2^k)
    (hit : ∀ f : G ≃g G, f r ∈ Set.range c)
    (interval : ∀ i : Fin n, (∃ f : G ≃g G, f r = c (i+start)) ↔ i.val < m) :
    ∃ (d t : ℕ) (w : (cycleGraph d).Copy G),
      3 ≤ d ∧ 2 ≤ t ∧ r ∈ Set.range w ∧ (d+1 = 2^t ∨ d+2 = 2^t) := by
  let : NeZero n := ⟨by omega⟩
  let label (i : Fin m) : Fin n := ⟨i.val,lt_of_lt_of_le i.isLt fits⟩
  let v (i : Fin m) := c (label i + start)
  let l := List.ofFn v
  have len : l.length = m := List.length_ofFn
  have unique : Function.Injective v := by
    intro i j h
    exact Fin.ext (congrArg (Fin.val (n := n)) (add_right_cancel (c.injective h) : label i = label j))
  have clean : l.Nodup := List.nodup_ofFn_ofInjective unique
  have path : l.IsChain G.Adj := by
    apply List.isChain_iff_getElem.mpr
    intro j hj
    have hj' : j+1 < m := by omega
    let a : Fin m := ⟨j,by omega⟩
    let b : Fin m := ⟨j+1,hj'⟩
    have e : (cycleGraph n).Adj (label a) (label b) :=
      pathGraph_le_cycleGraph (pathGraph_adj.mpr (Or.inl rfl))
    have rot : (cycleGraph n).Adj (label a+start) (label b+start) := by
      simpa only [cycleGraph_adj',add_sub_add_right_eq_sub] using e
    simpa [l,v,a,b] using c.toHom.map_rel' rot
  have covers (x : V) : x ∈ l ↔ ∃ f : G ≃g G, f r = x := by
    rw [show l = List.ofFn v from rfl,List.mem_ofFn']
    constructor
    · rintro ⟨j,rfl⟩
      exact (interval (label j)).mpr j.isLt
    · rintro ⟨f,rfl⟩
      obtain ⟨j,hj⟩ := hit f
      have eq : j-start+start = j := sub_add_cancel .. 
      have lt := (interval (j-start)).mp ⟨f,by rw [eq,hj]⟩
      exact ⟨⟨(j-start).val,lt⟩,by change c (j-start+start) = f r; rw [eq,hj]⟩
  obtain ⟨w,hw⟩ := orbitPathCloses G r conn cubic proper l (by omega) clean path covers
  exact ⟨l.length,k,w,by omega,hk,hw,by simpa [len] using near⟩

/-- One omitted label, or two consecutive omitted labels, on a dyadic
cycle force the rooted target whenever at least three orbit vertices remain. -/
theorem omittedBlockSolves {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (conn : G.Connected) (cubic : ∀ v, G.degree v = 3)
    (proper : ∃ v, ∀ f : G ≃g G, f r ≠ v)
    {k d : ℕ} (hk : 2 ≤ k) (gap : d = 1 ∨ d = 2) (large : 3 ≤ 2^k-d)
    (c : (cycleGraph (2^k)).Copy G) (q : Fin (2^k))
    (hit : ∀ f : G ≃g G, f r ∈ Set.range c)
    (orbit : ∀ j, (∃ f : G ≃g G, f r = c j) ↔ j ≠ q ∧ (d = 2 → j ≠ q+1)) :
    ∃ (n t : ℕ) (w : (cycleGraph n).Copy G),
      3 ≤ n ∧ 2 ≤ t ∧ r ∈ Set.range w ∧ (n+1 = 2^t ∨ n+2 = 2^t) := by
  let a : Fin (2^k) := ⟨2^k-d,by omega⟩
  let start := q-a
  have first : a+start = q := by simp [start]
  apply orbitIntervalSolves G r conn cubic proper c start (m := 2^k-d) large
    (by omega) hk (by omega) hit
  intro i
  rw [orbit,←first]
  have h (hd : d = 2) : (a+1 : Fin (2^k)).val = 2^k-1 := by
    have one : (1 : Fin (2^k)).val = 1 := by rw [Fin.val_one',Nat.mod_eq_of_lt (by omega)]
    rw [Fin.val_add,one]
    change (2^k-d+1) % (2^k) = 2^k-1
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have eq : a+start+1 = (a+1)+start := by abel
  rw [eq]
  simp only [ne_eq,add_left_inj,Fin.ext_iff]
  change (¬ i.val = 2^k-d) ∧ (d = 2 → ¬ i.val = (a+1).val) ↔ i.val < 2^k-d
  rcases gap with hd|hd
  · omega
  · rw [h hd]
    omega

private theorem cycleOfComponentOrder {S : Type} [Fintype S] (K : SimpleGraph S)
    (degree : ∀ x, (K.neighborSet x).ncard = 2) (a : S) :
    3 ≤ (K.connectedComponentMk a).supp.ncard ∧ cycleGraph (K.connectedComponentMk a).supp.ncard ⊑ K := by
  classical
  let A := K.connectedComponentMk a
  have cyc : K.IsCycles := fun {x} _ => degree x
  obtain ⟨p,hp,verts⟩ := cyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := A) (v := a) rfl (Set.nonempty_of_ncard_ne_zero (by rw [degree]; decide))
  have support : {x | x ∈ p.support.tail}=A.supp := by
    ext x
    rw [←verts,Walk.mem_verts_toSubgraph]
    change x ∈ p.support.tail ↔ x ∈ p.support
    cases p with
    | nil => exact (hp.not_nil .nil).elim
    | cons e q => simp [Walk.support_cons]; rintro rfl; exact q.end_mem_support
  have size : p.length = A.supp.ncard := by
    rw [←support]
    have ht := hp.support_nodup
    have eq : ({x | x ∈ p.support.tail} : Set S) = ↑p.support.tail.toFinset := by ext; simp
    rw [eq,Set.ncard_coe_finset,List.toFinset_card_of_nodup ht,List.length_tail,Walk.length_support]
    omega
  obtain ⟨c⟩ := (cycleGraph_isContained_iff hp.three_le_length).mpr ⟨a,p,hp,rfl⟩
  exact ⟨size ▸ hp.three_le_length,size ▸ ⟨c⟩⟩

/-- A transitive graph of degree two covered by two connected components has
a cycle of either the full order or half the order. -/
private theorem componentRing {S : Type} [Fintype S] (K : SimpleGraph S)
    (trans : ∀ x y : S, ∃ f : K ≃g K, f x = y)
    (degree : ∀ x, (K.neighborSet x).ncard = 2)
    (a b : S) (cover : ∀ x, K.Reachable a x ∨ K.Reachable b x) :
    ∃ (n : ℕ) (_c : (cycleGraph n).Copy K),
      3 ≤ n ∧ (n = Fintype.card S ∨ n+n = Fintype.card S) := by
  classical
  let A := K.connectedComponentMk a
  let B := K.connectedComponentMk b
  have union : A.supp ∪ B.supp = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rcases cover x with h|h
    · exact Or.inl (ConnectedComponent.sound h.symm)
    · exact Or.inr (ConnectedComponent.sound h.symm)
  obtain ⟨f,hf⟩ := trans a b
  have maps : f.connectedComponentEquiv A = B := by
    change K.connectedComponentMk (f a) = K.connectedComponentMk b
    rw [hf]
  have equal : A.supp.ncard = B.supp.ncard := by
    have e := ConnectedComponent.isoEquivSupp f A
    rw [←maps]
    exact Nat.card_congr e
  have count : A.supp.ncard = Fintype.card S ∨ A.supp.ncard+A.supp.ncard = Fintype.card S := by
    by_cases h : A = B
    · left
      rw [←h,Set.union_self] at union
      simp [union]
    · right
      have dis : Disjoint A.supp B.supp := Set.disjoint_left.mpr fun _ ha hb =>
        h (ConnectedComponent.eq_of_common_vertex ha hb)
      have cnt := Set.ncard_union_eq dis (Set.toFinite _) (Set.toFinite _)
      rw [union,Set.ncard_univ,equal] at cnt
      rw [equal]
      simpa only [Nat.card_eq_fintype_card] using cnt.symm
  obtain ⟨large,⟨c⟩⟩ := cycleOfComponentOrder K degree a
  exact ⟨_,c,large,count⟩

/-- Compress the two runs of orbit vertices into one indexed list with a
single possible missing edge. The missing edge may occur anywhere. -/
private theorem twoRunSolves {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (cubic : ∀ v, G.degree v = 3) {m k : ℕ} (hm : 6 ≤ m) (hk : 3 ≤ k)
    (total : m+2 = 2^k) (e : Fin m ↪ V) (t : ℕ)
    (rangeOrbit : ∀ v, v ∈ Set.range e ↔ ∃ f : G ≃g G, f r = v)
    (step : ∀ (i j : Fin m), i.val+1 = j.val → j.val ≠ t → G.Adj (e i) (e j))
    (external : ∃ (i : Fin m) (z : V), G.Adj (e i) z ∧ z ∉ Set.range e) :
    ∃ (n s : ℕ) (w : (cycleGraph n).Copy G),
      3 ≤ n ∧ 2 ≤ s ∧ r ∈ Set.range w ∧ (n+1 = 2^s ∨ n+2 = 2^s) := by
  classical
  let K := G.comap e
  let E := Equiv.ofInjective e e.injective
  have lift (f : G ≃g G) : ∃ g : K ≃g K, ∀ i, e (g i) = f (e i) := by
    have inv (v : V) : v ∈ Set.range e ↔ f v ∈ Set.range e := by
      rw [rangeOrbit,rangeOrbit]
      constructor
      · rintro ⟨g,h⟩
        exact ⟨g.trans f,by change f (g r) = f v; rw [h]⟩
      · rintro ⟨g,h⟩
        exact ⟨g.trans f.symm,by change f.symm (g r) = v; rw [h,f.symm_apply_apply]⟩
    let g := E.trans ((f.toEquiv.subtypeEquiv inv).trans E.symm)
    have hg (i) : e (g i) = f (e i) := Equiv.apply_ofInjective_symm e.injective _
    exact ⟨⟨g,by intro i j; change G.Adj (e (g i)) (e (g j)) ↔ _; rw [hg,hg]; exact f.map_rel_iff⟩,hg⟩
  have trans (i j : Fin m) : ∃ g : K ≃g K, g i = j := by
    obtain ⟨f,hf⟩ := (rangeOrbit _).mp ⟨i,rfl⟩
    obtain ⟨g,hg⟩ := (rangeOrbit _).mp ⟨j,rfl⟩
    obtain ⟨h,hh⟩ := lift (f.symm.trans g)
    apply Exists.intro h
    apply e.injective
    rw [hh]
    change g (f.symm (e i)) = e j
    rw [←hf,f.symm_apply_apply,hg]
  have same (i j : Fin m) : K.degree i = K.degree j := by
    obtain ⟨g,rfl⟩ := trans i j
    exact (g.degree_eq i).symm
  obtain ⟨u,z,uz,hz⟩ := external
  have upper : K.degree u < 3 := by
    let T := (K.neighborFinset u).map e
    have sub : T ⊆ G.neighborFinset (e u) := by
      intro x hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
      exact (G.mem_neighborFinset _ _).mpr ((K.mem_neighborFinset _ _).mp hv)
    have missing : z ∉ T := fun h => by
      obtain ⟨v,_,eq⟩ := Finset.mem_map.mp h
      exact hz ⟨v,eq⟩
    have h := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨sub,fun eq => missing (eq ▸ (G.mem_neighborFinset _ _).mpr uz)⟩)
    simpa [T,cubic] using h
  let j := if t ≤ 2 then 3 else 0
  have h₁ : j+1 ≠ t := by dsimp [j]; split <;> omega
  have h₂ : j+2 ≠ t := by dsimp [j]; split <;> omega
  have fit : j+2 < m := by dsimp [j]; split <;> omega
  let a : Fin m := ⟨j,by omega⟩
  let b : Fin m := ⟨j+1,by omega⟩
  let c : Fin m := ⟨j+2,fit⟩
  have ab : K.Adj a b := step a b rfl h₁
  have bc : K.Adj b c := step b c rfl h₂
  have ac : a ≠ c := fun eq => by have h := congrArg Fin.val eq; dsimp [a,c] at h; omega
  have lower : 2 ≤ K.degree b := by
    have sub : ({a,c} : Finset _) ⊆ K.neighborFinset b := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact (K.mem_neighborFinset _ _).mpr ab.symm
      · obtain rfl := Finset.mem_singleton.mp hx
        exact (K.mem_neighborFinset _ _).mpr bc
    simpa [ac] using Finset.card_le_card sub
  have degree (x : Fin m) : (K.neighborSet x).ncard = 2 := by
    have hx := same b x
    have hu := same u x
    rw [Set.ncard_eq_toFinset_card']
    change K.degree x = 2
    omega
  let p : Fin m := ⟨0,by omega⟩
  let q : Fin m := ⟨min t (m-1),by omega⟩
  have cover (x : Fin m) : K.Reachable p x ∨ K.Reachable q x := by
    obtain ⟨i,hi⟩ := x
    induction i with
    | zero => exact Or.inl .rfl
    | succ i ih =>
      by_cases h : i+1 = t
      · right
        have eq : q=⟨i+1,hi⟩ := Fin.ext (by dsimp [q]; omega)
        rw [eq]
      · have edge : K.Adj ⟨i,by omega⟩ ⟨i+1,hi⟩ := step _ _ rfl h
        exact (ih (by omega)).imp (·.trans edge.reachable) (·.trans edge.reachable)
  obtain ⟨n,w,hn,count⟩ := componentRing K trans degree p q cover
  let emb : K.Copy G := ⟨⟨e,fun h => h⟩,e.injective⟩
  let v := w ⟨0,by omega⟩
  obtain ⟨f,hf⟩ := (rangeOrbit _).mp ⟨v,rfl⟩
  have hit : f r ∈ Set.range (emb.comp w) := ⟨⟨0,by omega⟩,hf.symm⟩
  let w' := f.symm.toCopy.comp (emb.comp w)
  obtain ⟨idx,hi⟩ := hit
  have hit' : r ∈ Set.range w' := ⟨idx,by change f.symm ((emb.comp w) idx) = r; rw [hi,f.symm_apply_apply]⟩
  simp only [Fintype.card_fin] at count
  rcases count with h|h
  · exact ⟨n,k,w',hn,by omega,hit',Or.inr (by omega)⟩
  · obtain ⟨s,rfl⟩ : ∃ s, k = s+1 := ⟨k-1,by omega⟩
    rw [pow_succ] at total
    exact ⟨n,s,w',hn,by omega,hit',Or.inl (by omega)⟩

/-- Any two omitted labels on a dyadic cycle of order at least eight force
a cycle through the root of the required length. -/
theorem twoOmissionsSolve {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (cubic : ∀ v, G.degree v = 3) {k : ℕ} (hk : 3 ≤ k)
    (c : (cycleGraph (2^k)).Copy G) (x y : Fin (2^k)) (hne : x ≠ y)
    (hit : ∀ f : G ≃g G, f r ∈ Set.range c)
    (omits : ∀ j, (∃ f : G ≃g G, f r = c j) ↔ j ≠ x ∧ j ≠ y) :
    ∃ (n s : ℕ) (w : (cycleGraph n).Copy G),
      3 ≤ n ∧ 2 ≤ s ∧ r ∈ Set.range w ∧ (n+1 = 2^s ∨ n+2 = 2^s) := by
  have big : 8 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  let m := 2^k-2
  have hm : 6 ≤ m := by dsimp [m]; omega
  have total : m+2 = 2^k := by dsimp [m]; omega
  let q := y-x
  have nonzero : q ≠ 0 := sub_ne_zero.mpr hne.symm
  have pos : 0 < q.val := by
    by_contra! h
    exact nonzero (Fin.ext (by simpa using h))
  let t := q.val-1
  let label (i : Fin m) : Fin (2^k) :=
    ⟨if i.val < t then i.val+1 else i.val+2,by split <;> omega⟩
  have labels (i : Fin m) : (label i).val ≠ 0 ∧ (label i).val ≠ q.val := by
    dsimp [label,t]; split <;> omega
  have inject : Function.Injective label := by
    intro i j h
    have eq := congrArg Fin.val h
    apply Fin.ext
    dsimp [label] at eq
    split at eq <;> split at eq <;> omega
  let e : Fin m ↪ V := ⟨fun i => c (label i+x),fun _ _ h =>
    inject (add_right_cancel (c.injective h))⟩
  have onto (j : Fin (2^k)) (h₀ : j.val ≠ 0) (hq : j.val ≠ q.val) : ∃ i, label i = j := by
    by_cases h : j.val < q.val
    · refine ⟨⟨j.val-1,by omega⟩,Fin.ext ?_⟩
      dsimp [label,t]; split <;> omega
    · refine ⟨⟨j.val-2,by omega⟩,Fin.ext ?_⟩
      dsimp [label,t]; split <;> omega
  have rot (j : Fin (2^k)) : (∃ f : G ≃g G, f r = c (j+x)) ↔ j ≠ 0 ∧ j ≠ q := by
    rw [omits]
    have h : q+x = y := sub_add_cancel ..
    nth_rw 1 [←h]
    simp
  have covers (v : V) : v ∈ Set.range e ↔ ∃ f : G ≃g G, f r = v := by
    constructor
    · rintro ⟨i,rfl⟩
      exact (rot _).mpr ⟨fun h => (labels i).1 (congrArg Fin.val h),
        fun h => (labels i).2 (congrArg Fin.val h)⟩
    · rintro ⟨f,rfl⟩
      obtain ⟨j,eq⟩ := hit f
      have good := (rot (j-x)).mp ⟨f,by simpa using eq.symm⟩
      obtain ⟨i,hi⟩ := onto (j-x) (fun h => good.1 (Fin.ext h)) (fun h => good.2 (Fin.ext h))
      exact ⟨i,by change c (label i+x) = f r; rw [hi,sub_add_cancel,eq]⟩
  have edge (a b : Fin (2^k)) (h : a.val+1 = b.val) : G.Adj (c (a+x)) (c (b+x)) := by
    have base : (cycleGraph (2^k)).Adj a b := pathGraph_le_cycleGraph (pathGraph_adj.mpr (Or.inl h))
    apply c.toHom.map_rel'
    simpa only [cycleGraph_adj',add_sub_add_right_eq_sub] using base
  apply twoRunSolves G r cubic hm hk total e t covers
  · intro i j h hj
    apply edge
    dsimp [label]
    split <;> split <;> omega
  · let i : Fin m := ⟨0,by omega⟩
    let a : Fin (2^k) := ⟨(label i).val-1,by have := (label i).isLt; omega⟩
    have pred : a.val+1 = (label i).val := by have := (labels i).1; dsimp [a]; omega
    refine ⟨i,c (a+x),(edge a _ pred).symm,?_⟩
    intro inside
    have avoid := (rot a).mp ((covers _).mp inside)
    by_cases h : 0 < t
    · apply avoid.1
      apply Fin.ext
      simp [a,label,i,h]
    · apply avoid.2
      apply Fin.ext
      simp [a,label,i,show ¬0 < t from h]
      dsimp [t] at h
      omega

/-- A cubic graph cannot share an outside neighbor between two vertices of
an orbit of order coprime to six if the orbit contains an edge. -/
theorem privateOutsideNeighbor {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : V) (cubic : ∀ v, G.degree v = 3)
    (O : Set V) (orb : ∀ v, v ∈ O ↔ ∃ f : G ≃g G, f r = v)
    (odd : ¬ 2 ∣ O.ncard) (third : ¬ 3 ∣ O.ncard)
    (edge : ∃ a ∈ O, ∃ b ∈ O, G.Adj a b)
    {z x y : V} (hz : z ∉ O) (hx : x ∈ O) (hy : y ∈ O)
    (zx : G.Adj z x) (zy : G.Adj z y) : x = y := by
  classical
  by_contra ne
  let T : Set V := {v | ∃ f : G ≃g G, f z = v}
  have inv (r₀ : V) (S : Set V) (hS : ∀ v, v ∈ S ↔ ∃ f : G ≃g G, f r₀ = v)
      (f : G ≃g G) (v : V) : v ∈ S ↔ f v ∈ S := by
    rw [hS,hS]
    constructor
    · rintro ⟨g,h⟩
      exact ⟨g.trans f,by change f (g r₀) = f v; rw [h]⟩
    · rintro ⟨g,h⟩
      exact ⟨g.trans f.symm,by change f.symm (g r₀) = v; rw [h,f.symm_apply_apply]⟩
  have hT (v) : v ∈ T ↔ ∃ f : G ≃g G, f z = v := Iff.rfl
  have move (a b : V) (ha : a ∈ O) (hb : b ∈ O) : ∃ f : G ≃g G, f a = b := by
    obtain ⟨f,hf⟩ := (orb _).mp ha
    obtain ⟨g,hg⟩ := (orb _).mp hb
    exact ⟨f.symm.trans g,by change g (f.symm a) = b; rw [←hf,f.symm_apply_apply,hg]⟩
  let N (S : Set V) (v : V) := S.toFinset.filter (G.Adj v)
  have transfer (s : V) (S : Set V) (hS : ∀ v, v ∈ S ↔ ∃ f : G ≃g G, f s = v)
      (f : G ≃g G) (v : V) : (N S (f v)).card = (N S v).card := by
    have eq : (N S v).map f.toEquiv.toEmbedding = N S (f v) := by
      ext w
      obtain ⟨u,rfl⟩ := f.surjective w
      constructor
      · intro h
        obtain ⟨b,hb,eq⟩ := Finset.mem_map.mp h
        obtain rfl : b = u := f.injective eq
        exact Finset.mem_filter.mpr ⟨Set.mem_toFinset.mpr ((inv s S hS f b).mp
          (Set.mem_toFinset.mp (Finset.mem_filter.mp hb).1)),f.map_rel_iff.mpr (Finset.mem_filter.mp hb).2⟩
      · intro h
        exact Finset.mem_map.mpr ⟨u,Finset.mem_filter.mpr ⟨Set.mem_toFinset.mpr
          ((inv s S hS f u).mpr (Set.mem_toFinset.mp (Finset.mem_filter.mp h).1)),
          f.map_rel_iff.mp (Finset.mem_filter.mp h).2⟩,rfl⟩
    rw [←eq,Finset.card_map]
  let h := (N O x).card
  let d := (N O z).card
  have reg (a : V) (ha : a ∈ O) : (N O a).card = h := by
    obtain ⟨f,rfl⟩ := move x a hx ha
    exact transfer r O orb f x
  have uniform (a : V) (ha : a ∈ T) : (N O a).card = d := by
    obtain ⟨f,rfl⟩ := ha
    exact transfer r O orb f z
  have internal (a : O) : (G.induce O).degree a = h := by
    rw [←reg a a.property,←card_neighborFinset_eq_degree,←Finset.card_map
      (f := Function.Embedding.subtype (· ∈ O)),map_neighborFinset_induce]
    congr 1
    ext v
    simp [N,and_comm]
  have evenSum := (G.induce O).sum_degrees_eq_twice_card_edges
  simp only [internal,Finset.sum_const,Finset.card_univ,smul_eq_mul] at evenSum
  have size : Fintype.card O = O.ncard := by rw [Set.ncard_eq_toFinset_card',Set.toFinset_card]
  have pos : 0 < h := by
    obtain ⟨a,ha,b,hb,ab⟩ := edge
    rw [←reg a ha]
    exact Finset.card_pos.mpr ⟨b,by simp [N,hb,ab]⟩
  have notOne : h ≠ 1 := by
    intro hh
    apply odd
    exact ⟨_,by simpa [size,hh] using evenSum⟩
  have dis (v : V) (hv : v ∈ T) : v ∉ O := by
    obtain ⟨f,rfl⟩ := hv
    exact fun h => hz ((inv r O orb f z).mpr h)
  have sub (v : V) (S : Set V) : N S v ⊆ G.neighborFinset v := by
    intro a ha
    exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp ha).2
  have boundary : (N T x).card = 1 := by
    have disjoint : Disjoint (N O x) (N T x) := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      exact dis v (by simpa using (Finset.mem_filter.mp hw).1)
        (by simpa using (Finset.mem_filter.mp hv).1)
    have bound := Finset.card_le_card (Finset.union_subset (sub x O) (sub x T))
    rw [Finset.card_union_of_disjoint disjoint,card_neighborFinset_eq_degree,cubic,reg x hx] at bound
    have mem : z ∈ T := ⟨SimpleGraph.Iso.refl,rfl⟩
    have lower := Finset.card_pos.mpr (show (N T x).Nonempty from ⟨z,by simp [N,mem,zx.symm]⟩)
    omega
  have one (a : V) (ha : a ∈ O) : (N T a).card = 1 := by
    obtain ⟨f,rfl⟩ := move x a hx ha
    exact (transfer z T hT f x).trans boundary
  have small : d ≤ 3 := (Finset.card_le_card (sub z O)).trans_eq (cubic z)
  have pair : ({x,y} : Finset V) ⊆ N O z := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · simp [N,hx,zx]
    · obtain rfl := Finset.mem_singleton.mp ha
      simp [N,hy,zy]
  have two : 2 ≤ d := by simpa [ne,d] using Finset.card_le_card pair
  have count : O.ncard = T.toFinset.card * d := calc
    O.ncard = ∑ a ∈ O.toFinset, (N T a).card := by
      rw [Finset.sum_congr rfl (g := fun _ => 1) (fun a ha => one a (by simpa using ha))]
      simp [Set.ncard_eq_toFinset_card']
    _ = ∑ b ∈ T.toFinset, (N O b).card := by
      simp only [N,Finset.card_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      simp [adj_comm]
    _ = _ := by
      rw [Finset.sum_congr rfl (g := fun _ => d) (fun b hb => uniform b (by simpa using hb))]
      simp
  have divides : d ∣ O.ncard := ⟨_,count.trans (Nat.mul_comm ..)⟩
  rcases (show d=2 ∨ d=3 by omega) with hd|hd
  · exact odd (hd ▸ divides)
  · exact third (hd ▸ divides)

/-- On a dyadic cycle, any three labels outside the forced root orbit must
constitute a single cyclic interval. -/
theorem threeOmissionsConsecutive {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : V) (cubic : ∀ v, G.degree v = 3)
    {k : ℕ} (hk : 3 ≤ k) (c : (cycleGraph (2^k)).Copy G)
    (hit : ∀ f : G ≃g G, f r ∈ Set.range c)
    (B : Finset (Fin (2^k))) (size : B.card = 3)
    (omits : ∀ j, (∃ f : G ≃g G, f r = c j) ↔ j ∉ B) :
    ∃ q ∈ B, q-1 ∈ B ∧ q+1 ∈ B := by
  classical
  have big : 8 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  let O : Set V := {v | ∃ f : G ≃g G, f r = v}
  have covers : Bᶜ.map c.toEmbedding = O.toFinset := by
    ext v
    simp only [Finset.mem_map,Finset.mem_compl,Set.mem_toFinset]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact (omits j).mpr hj
    · rintro ⟨f,rfl⟩
      obtain ⟨j,hj⟩ := hit f
      exact ⟨j,(omits j).mp ⟨f,hj.symm⟩,hj⟩
  have order : O.ncard + 3 = 2^k := by
    rw [Set.ncard_eq_toFinset_card',←covers,Finset.card_map,Finset.card_compl,Fintype.card_fin,size]
    omega
  have next (i : Fin (2^k)) : G.Adj (c i) (c (i+1)) := by
    apply c.toHom.map_rel'
    rw [cycleGraph_adj']
    right
    simp [Nat.mod_eq_of_lt (show 1 < 2^k by omega)]
  have touch : ∃ i : Fin (2^k), i ∉ B ∧ i+1 ∉ B := by
    by_contra! no
    let shift : Fin (2^k) ↪ Fin (2^k) := ⟨(·+1),fun _ _ => add_right_cancel⟩
    have sub : Bᶜ.map shift ⊆ B := by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
      exact no i (Finset.mem_compl.mp hi)
    have h := Finset.card_le_card sub
    rw [Finset.card_map,Finset.card_compl,Fintype.card_fin,size] at h
    omega
  obtain ⟨i,hi,hj⟩ := touch
  have internal : ∃ a ∈ O, ∃ b ∈ O, G.Adj a b :=
    ⟨_,(omits _).mpr hi,_,(omits _).mpr hj,next i⟩
  have odd : ¬ 2 ∣ O.ncard := by
    have he : 2 ∣ 2^k := dvd_pow_self 2 (by omega)
    omega
  have third : ¬ 3 ∣ O.ncard := by
    have hp : ¬ 3 ∣ 2^k := fun h =>
      (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have nonisolated (j : Fin (2^k)) (hj : j ∈ B) : j-1 ∈ B ∨ j+1 ∈ B := by
    by_contra! isolated
    have left := (omits _).mpr isolated.1
    have right := (omits _).mpr isolated.2
    have outside : c j ∉ O := fun h => (omits j).mp h hj
    have zl : G.Adj (c j) (c (j-1)) := by simpa using (next (j-1)).symm
    have eq := c.injective (privateOutsideNeighbor G r cubic O (fun _ => Iff.rfl)
      odd third internal outside left right zl (next j))
    have small : (1+1 : Fin (2^k)) = 0 := by
      have h := sub_eq_iff_eq_add.mp eq
      apply add_left_cancel (a := j)
      simpa [add_assoc] using h.symm
    have h := congrArg Fin.val small
    simp only [Fin.val_add,Fin.val_one',Fin.val_zero] at h
    rw [Nat.mod_eq_of_lt (show 1 < 2^k by omega),Nat.mod_eq_of_lt (by omega)] at h
    omega
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
  obtain ⟨u,hu,hv⟩ : ∃ u ∈ B, u+1 ∈ B := by
    rcases nonisolated a ha with h|h
    · exact ⟨a-1,h,by simpa using ha⟩
    · exact ⟨a,ha,h⟩
  have extra : ∃ w ∈ B, w ≠ u ∧ w ≠ u+1 := by
    by_contra! h
    have sub : B ⊆ {u,u+1} := by
      intro w hw
      by_cases eq : w=u
      · simp [eq]
      · simp [h w hw eq]
    have bound := Finset.card_le_card sub
    have pair := Finset.card_insert_le u ({u+1} : Finset _)
    simp only [Finset.card_singleton] at pair
    omega
  obtain ⟨w,hw,hwu,hwv⟩ := extra
  have all : B = {w,u,u+1} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · simpa [Finset.insert_subset_iff] using And.intro hw (And.intro hu hv)
    · have hne : u ≠ u+1 := by simp [show k ≠ 0 by omega]
      simp [size,hwu,hwv,hne]
  have decideSide := nonisolated w hw
  rw [all] at decideSide
  simp only [Finset.mem_insert,Finset.mem_singleton] at decideSide
  rcases decideSide with (h|h|h)|(h|h|h)
  · exact False.elim ((by simp [show k ≠ 0 by omega] : w-1 ≠ w) h)
  · exact False.elim (hwv (sub_eq_iff_eq_add.mp h))
  · exact ⟨u+1,hv,by simpa using hu,by rw [←sub_eq_iff_eq_add.mp h]; exact hw⟩
  · exact False.elim ((by simp [show k ≠ 0 by omega] : w+1 ≠ w) h)
  · exact ⟨u,hu,by simpa [←h] using hw,hv⟩
  · exact False.elim (hwu (add_right_cancel h))

/-- On an odd orbit, copies of an edge carrying an exterior four-edge
detour must meet. Comparing the two detours forces a short cycle. -/
private theorem oddDetour {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (O : Set V) (orb : ∀ v, v ∈ O ↔ ∃ f : G ≃g G, f r = v)
    (cubic : ∀ v, G.degree v = 3) (odd : ¬ 2 ∣ O.ncard) (large : 3 < O.ncard)
    (forced : ∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G, ∀ f : G ≃g G, f r ∈ Set.range c)
    (six : ∀ c : (cycleGraph 6).Copy G, ∀ f : G ≃g G, f r ∉ Set.range c)
    (a₀ b₀ : O) (edge : G.Adj a₀ b₀) (p q s : V)
    (hp : p ∉ O) (hq : q ∉ O) (hs : s ∉ O) (ps : p ≠ s)
    (ap : G.Adj a₀ p) (pq : G.Adj p q) (qs : G.Adj q s) (sb : G.Adj s b₀) : False := by
  classical
  let J : SimpleGraph O := {
    Adj := fun a b => G.Adj a b ∧ ∃ p q s : V, p ∉ O ∧ q ∉ O ∧ s ∉ O ∧ p ≠ s ∧
      G.Adj a p ∧ G.Adj p q ∧ G.Adj q s ∧ G.Adj s b
    symm := ⟨by
      rintro a b ⟨e,p,q,s,hp,hq,hs,ps,h₁,h₂,h₃,h₄⟩
      exact ⟨e.symm,s,q,p,hs,hq,hp,ps.symm,h₄.symm,h₃.symm,h₂.symm,h₁.symm⟩⟩
    loopless := ⟨fun _ h => h.1.ne rfl⟩ }
  have pos (a : O) : 0 < J.degree a := by
    obtain ⟨f,hf⟩ := (orb _).mp a₀.property
    obtain ⟨g,hg⟩ := (orb _).mp a.property
    let t := f.symm.trans g
    have move : t a₀ = a := by change g (f.symm a₀) = a; rw [←hf,f.symm_apply_apply,hg]
    have inv (x : V) : t x ∈ O ↔ x ∈ O := by
      rw [orb,orb]
      constructor
      · rintro ⟨w,h⟩
        exact ⟨w.trans t.symm,by change t.symm (w r) = x; rw [h,t.symm_apply_apply]⟩
      · rintro ⟨w,h⟩
        exact ⟨w.trans t,by change t (w r) = t x; rw [h]⟩
    apply (J.degree_pos_iff_exists_adj a).mpr
    refine ⟨⟨t b₀,(inv _).mpr b₀.property⟩,?_,t p,t q,t s,fun h => hp ((inv _).mp h),
      fun h => hq ((inv _).mp h),fun h => hs ((inv _).mp h),t.injective.ne ps,?_,
      t.map_rel_iff.mpr pq,t.map_rel_iff.mpr qs,t.map_rel_iff.mpr sb⟩
    · exact move ▸ t.map_rel_iff.mpr edge
    · exact move ▸ t.map_rel_iff.mpr ap
  have branching : ∃ a, 1 < J.degree a := by
    by_contra! h
    have all (a : O) : J.degree a = 1 := by have := pos a; have := h a; omega
    have count := J.sum_degrees_eq_twice_card_edges
    simp only [all,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,Set.fintypeCard_eq_ncard] at count
    exact odd ⟨_,count⟩
  obtain ⟨a,ha⟩ := branching
  obtain ⟨b,hb,c,hc,bc⟩ := Finset.one_lt_card.mp ha
  obtain ⟨ab,u,v,w,hu,hv,hw,uw,au,uv,vw,wb⟩ := (J.mem_neighborFinset a b).mp hb
  obtain ⟨ac,U,V',W,hU,hV,hW,UW,aU,UV,VW,Wc⟩ := (J.mem_neighborFinset a c).mp hc
  have hbc : (b : V) ≠ c := fun h => bc (Subtype.ext h)
  have same : U = u := by
    by_contra ne
    have sub : ({(b:V),(c:V),U,u} : Finset V) ⊆ G.neighborFinset a := by
      intro y hy
      simp only [Finset.mem_insert,Finset.mem_singleton] at hy
      rcases hy with h|h|h|h <;> subst y <;> simpa
    have bound := Finset.card_le_card sub
    have out (z : V) (hz : z ∉ O) (j : O) : (j : V) ≠ z := fun eq => hz (eq ▸ j.property)
    simp [hbc,out _ hU,out _ hu,ne,cubic] at bound
  subst U
  have extra : ∃ y ∈ O, y ≠ a ∧ y ≠ b ∧ y ≠ c := by
    by_contra! no
    have sub : O ⊆ ({(a:V),(b:V),(c:V)} : Set V) := by
      intro y hy
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      by_cases e : y=a
      · exact Or.inl e
      by_cases f : y=b
      · exact Or.inr (Or.inl f)
      exact Or.inr (Or.inr (no y hy e f))
    have bound := Set.ncard_le_ncard sub
    have card : ({(a:V),(b:V),(c:V)} : Set V).ncard = 3 := by simp [ab.ne,ac.ne,hbc]
    omega
  obtain ⟨y,hy,ya,yb,yc⟩ := extra
  have out {z : V} (hz : z ∉ O) (j : O) : (j : V) ≠ z := fun eq => hz (eq ▸ j.property)
  have noty {z : V} (hz : z ∉ O) : y ≠ z := fun eq => hz (eq ▸ hy)
  have reject (l : List V) (sz : l.length=4 ∨ l.length=6 ∨ l.length=8) (hl : l.Nodup)
      (path : l.IsChain G.Adj) (close : ∀ h : l ≠ [], G.Adj (l.getLast h) (l.head h))
      (contains : (a:V) ∈ l) (missing : y ∉ l) : False := by
    obtain ⟨d,hd⟩ := exactRing G l (by rcases sz with h|h|h <;> omega) hl path close
    obtain ⟨f,hf⟩ := (orb _).mp hy
    obtain ⟨g,hg⟩ := (orb _).mp a.property
    rcases sz with h|h|h
    · have hit : f r ∈ Set.range d := by
        revert d
        rw [h]
        exact fun d _ => forced 2 (by decide) d f
      exact missing ((hd _).mpr (hf ▸ hit))
    · have hit := (hd _).mp contains
      rw [←hg] at hit
      revert d hit
      rw [h]
      exact fun d _ h' => six d g h'
    · have hit : f r ∈ Set.range d := by
        revert d
        rw [h]
        exact fun d _ => forced 3 (by decide) d f
      exact missing ((hd _).mpr (hf ▸ hit))
  have outside := And.intro (out hu) (And.intro (out hv) (And.intro (out hw) (And.intro (out hV) (out hW))))
  obtain ⟨nu,nv,nw,nV,nW⟩ := outside
  by_cases ww : w = W
  · subst W
    apply reject [a,b,w,c] (by simp) _ _ _ (by simp) (by simp [ya,yb,yc,noty hw])
    · simp [ab.ne,ac.ne,hbc,nw,Ne.symm (nw c)]
    · simp [ab,wb.symm,Wc]
    · simpa using ac.symm
  by_cases vW : v = W
  · subst W
    apply reject [a,u,v,c] (by simp) _ _ _ (by simp) (by simp [ya,yc,noty hu,noty hv])
    · simp [ac.ne,nu,nv,uv.ne,Ne.symm (nu c),Ne.symm (nv c)]
    · simp [au,uv,Wc]
    · simpa using ac.symm
  by_cases Vw : V' = w
  · subst V'
    apply reject [a,u,w,b] (by simp) _ _ _ (by simp) (by simp [ya,yb,noty hu,noty hw])
    · simp [ab.ne,nu,nw,uw,Ne.symm (nu b),Ne.symm (nw b)]
    · simp [au,UV,wb]
    · simpa using ab.symm
  by_cases vv : v = V'
  · subst V'
    apply reject [a,b,w,v,W,c] (by simp) _ _ _ (by simp) (by simp [ya,yb,yc,noty hw,noty hv,noty hW])
    · simp [ab.ne,ac.ne,hbc,nw,nv,nW,ww,vW,vw.ne.symm,Ne.symm (nw c),Ne.symm (nv c),Ne.symm (nW c)]
    · simp [ab,wb.symm,vw.symm,VW,Wc]
    · simpa using ac.symm
  apply reject [a,b,w,v,u,V',W,c] (by simp) _ _ _ (by simp)
    (by simp [ya,yb,yc,noty hu,noty hv,noty hw,noty hV,noty hW])
  · simp [ab.ne,ac.ne,hbc,nw,nv,nW,nu,nV,ww,vW,vv,Ne.symm Vw,vw.ne.symm,uw.symm,
      uv.ne.symm,UW,UV.ne,VW.ne,Ne.symm (nw c),Ne.symm (nv c),Ne.symm (nu c),Ne.symm (nV c),Ne.symm (nW c)]
  · simp [ab,wb.symm,vw.symm,uv.symm,UV,VW,Wc]
  · simpa using ac.symm

section

open Fin.NatCast
/-- Three omissions in any positions are incompatible with the forced-orbit
and no-rooted-hexagon assumptions. -/
theorem threeOmissionsSolve {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : V) (conn : G.Connected) (cubic : ∀ v, G.degree v = 3)
    (proper : ∃ v, ∀ f : G ≃g G, f r ≠ v)
    (forced : ∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G, ∀ f : G ≃g G, f r ∈ Set.range c)
    (six : ∀ c : (cycleGraph 6).Copy G, ∀ f : G ≃g G, f r ∉ Set.range c)
    {k : ℕ} (hk : 3 ≤ k) (c : (cycleGraph (2^k)).Copy G)
    (B : Finset (Fin (2^k))) (size : B.card = 3)
    (omits : ∀ j, (∃ f : G ≃g G, f r = c j) ↔ j ∉ B) : False := by
  classical
  let n := 2^k
  have big : 8 ≤ n := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  let : NeZero n := ⟨by omega⟩
  obtain ⟨q,hq,hl,hr⟩ := threeOmissionsConsecutive G r cubic hk c (forced k (by omega) c) B size omits
  let start := q-1
  let F (i : ℕ) := c ((i : Fin n)+start)
  let O : Set V := {v | ∃ f : G ≃g G, f r = v}
  have inj (i j : ℕ) (hi : i < n) (hj : j < n) (h : F i = F j) : i = j := by
    have h' := congrArg Fin.val (add_right_cancel (c.injective h) : (i : Fin n) = j)
    simpa [Fin.val_natCast,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using h'
  have zero : (0 : Fin n)+start = q-1 := zero_add _
  have one : (1 : Fin n)+start = q := by dsimp [start]; abel
  have two : (2 : Fin n)+start = q+1 := by dsimp [start]; rw [show (2 : Fin n)=1+1 by norm_num]; abel
  have mem (i : ℕ) (hi : i < n) : F i ∈ O ↔ 3 ≤ i := by
    change (∃ f : G ≃g G, f r = c _) ↔ _
    rw [omits]
    have distinct (i j : ℕ) (hi : i < n) (hj : j < n) (h : i ≠ j) :
        (i : Fin n)+start ≠ (j : Fin n)+start := fun eq => h (inj i j hi hj (congrArg c eq))
    have h01 := distinct 0 1 (by omega) (by omega) (by decide)
    have h02 := distinct 0 2 (by omega) (by omega) (by decide)
    have h12 := distinct 1 2 (by omega) (by omega) (by decide)
    have setEq : B = {(0 : Fin n)+start,1+start,2+start} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · simpa [Finset.insert_subset_iff,zero,one,two] using And.intro hl (And.intro hq hr)
      · simp only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat] at h01 h02 h12
        rw [size,Finset.card_insert_of_notMem,Finset.card_insert_of_notMem,Finset.card_singleton]
        · exact Finset.notMem_singleton.mpr h12
        · exact fun h => (Finset.mem_insert.mp h).elim h01 (fun e => h02 (Finset.mem_singleton.mp e))
    rw [setEq]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    constructor
    · rintro ⟨a,b,d⟩
      by_contra! low
      interval_cases i <;> simp_all
    · intro h
      exact ⟨distinct i 0 hi (by omega) (by omega),distinct i 1 hi (by omega) (by omega),
        distinct i 2 hi (by omega) (by omega)⟩
  have next (i : ℕ) : G.Adj (F i) (F (i+1)) := by
    apply c.toHom.map_rel'
    rw [cycleGraph_adj']
    right
    simp [Nat.cast_add,add_sub_add_right_eq_sub,show 0 < k by omega]
  let m := n-3
  let f (j : Fin m) := F (j.val+3)
  let l := List.ofFn f
  have len : l.length = m := List.length_ofFn
  have fit (j : Fin m) : j.val+3 < n := by have := j.isLt; dsimp [m] at this; omega
  have clean : l.Nodup := List.nodup_ofFn_ofInjective (by
    intro i j h
    have eq := inj _ _ (fit i) (fit j) h
    exact Fin.ext (by omega))
  have path : l.IsChain G.Adj := by
    apply List.isChain_iff_getElem.mpr
    intro i hi
    simpa [l,f,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next (i+3)
  have covers (v : V) : v ∈ l ↔ v ∈ O := by
    rw [show l = List.ofFn f from rfl,List.mem_ofFn']
    constructor
    · rintro ⟨j,rfl⟩
      exact (mem _ (fit j)).mpr (by omega)
    · rintro ⟨g,rfl⟩
      obtain ⟨j,hj⟩ := forced k (by omega) c g
      let i := (j-start).val
      have eq : F i = g r := by
        change c (((j-start).val : Fin n)+start) = g r
        simpa using hj
      have hi : i < n := (j-start).isLt
      have lower := (mem i hi).mp (eq ▸ (show g r ∈ O from ⟨g,rfl⟩))
      refine ⟨⟨i-3,by dsimp [m]; omega⟩,?_⟩
      change F (i-3+3) = g r
      rwa [Nat.sub_add_cancel lower]
  have ml : 3 ≤ m := by dsimp [m]; omega
  have ne : l ≠ [] := List.length_pos_iff.mp (by omega)
  have e := orbitPathEndpoints G r conn cubic proper l (by omega) clean path covers ne
  have last : G.Adj (F (n-1)) (F 3) := by
    rw [List.getLast_eq_getElem,List.head_eq_getElem] at e
    simpa [l,f,show m-1+3 = n-1 by dsimp [m]; omega] using e
  have endStep := next (n-1)
  have wrap : F n = F 0 := by simp [F]
  rw [show n-1+1 = n by omega,wrap] at endStep
  have siz : O.ncard = m := by
    have eq : O.toFinset = l.toFinset := by ext v; simpa using (covers v).symm
    rw [Set.ncard_eq_toFinset_card',eq,List.toFinset_card_of_nodup clean,len]
  have odd : ¬ 2 ∣ O.ncard := by
    have he : 2 ∣ 2^k := dvd_pow_self 2 (by omega)
    change 2 ∣ n at he
    dsimp [m] at siz
    omega
  apply oddDetour G r O (fun _ => Iff.rfl) cubic odd (by dsimp [m] at siz; omega)
    forced six ⟨F (n-1),(mem (n-1) (by omega)).mpr (by omega)⟩ ⟨F 3,(mem 3 (by omega)).mpr (by omega)⟩
    last (F 0) (F 1) (F 2)
  · simp [mem 0 (by omega)]
  · simp [mem 1 (by omega)]
  · simp [mem 2 (by omega)]
  · exact fun eq => (by decide : (0:ℕ) ≠ 2) (inj _ _ (by omega) (by omega) eq)
  · exact endStep
  · exact next 0
  · exact next 1
  · exact next 2

end

/-- Two paths from x to y with disjoint interiors give a cycle whose
vertex set is exactly their union. Lists contain only interior vertices. -/
theorem twoArmCycle {V : Type*} (G : SimpleGraph V) (x y : V) (A B : List V)
    (distinct : (x::y::(A++B)).Nodup)
    (left : (x::(A++[y])).IsChain G.Adj) (right : (x::(B++[y])).IsChain G.Adj)
    (large : 3 ≤ A.length+B.length+2) :
    ∃ c : (cycleGraph (A.length+B.length+2)).Copy G,
      ∀ z, z ∈ Set.range c ↔ z=x ∨ z=y ∨ z∈A ∨ z∈B := by
  let l := x :: (A ++ y :: B.reverse)
  have back : (y :: (B.reverse ++ [x])).IsChain G.Adj := by
    have h := List.isChain_reverse.mpr (right.imp (fun _ _ e => e.symm))
    simpa using h
  have join := List.IsChain.append_overlap (l₁ := x::A) (l₂ := [y])
    (l₃ := B.reverse++[x]) left back (by simp)
  have closed : (l++[x]).IsChain G.Adj := by
    simpa [l,List.append_assoc] using join
  have size : l.length = A.length+B.length+2 := by simp [l]; omega
  have nd : l.Nodup := by
    simp only [List.nodup_cons,List.nodup_append',List.mem_append,List.mem_cons,
      not_or] at distinct
    simp only [l,List.nodup_cons,List.nodup_append',List.mem_cons,List.mem_append,
      List.mem_reverse,List.nodup_reverse,not_or,List.disjoint_cons_right,List.disjoint_reverse_right]
    tauto
  obtain ⟨c,hc⟩ := exactRing G l (size ▸ large) nd closed.left_of_append (by
    intro ne
    exact closed.rel_getLast_head_of_append ne (by simp))
  have claim : ∃ c : (cycleGraph l.length).Copy G, ∀ z, z∈Set.range c ↔
      z=x ∨ z=y ∨ z∈A ∨ z∈B := by
    refine ⟨c,fun z => (hc z).symm.trans ?_⟩
    simp only [l,List.mem_cons,List.mem_append,List.mem_reverse]
    tauto
  rwa [size] at claim

/-- In a rooted obstruction, every successful-length reroute confines the
entire forced orbit to the discarded interior. If all three pairwise cycles
are dyadic, the orbit is contained in the two common endpoints. -/
theorem thetaObstruction {V : Type} (G : SimpleGraph V) (r : V)
    (forced : ∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G,
      ∀ f : G ≃g G, f r ∈ Set.range c)
    (obstruction : ¬ ∃ (n k : ℕ) (c : (cycleGraph n).Copy G) (f : G ≃g G),
      3 ≤ n ∧ 2 ≤ k ∧ f r ∈ Set.range c ∧ (n+1=2^k ∨ n+2=2^k)) :
     let dyadic := fun d : ℕ => ∃ k : ℕ, 2 ≤ k ∧ d = 2^k
     let near := fun d : ℕ => 3 ≤ d ∧ ∃ k : ℕ, 2 ≤ k ∧ (d+1=2^k ∨ d+2=2^k)
     ∀ (x y : V) (A B P : List V), (x::y::(A++B++P)).Nodup →
       (∀ L ∈ [A,B,P], (x::(L++[y])).IsChain G.Adj) →
       dyadic (A.length+B.length+2) →
       (near (A.length+P.length+2) →
         (∀ f : G ≃g G, f r ∈ B) ∧ ¬ near (B.length+P.length+2)) ∧
       (dyadic (A.length+P.length+2) → dyadic (B.length+P.length+2) →
         ∀ f : G ≃g G, f r = x ∨ f r = y) := by
  dsimp only
  intro x y A B P clean paths base
  have pieces := clean
  simp only [List.nodup_cons,List.mem_cons,List.mem_append,not_or,List.nodup_append',
    List.disjoint_append_left] at pieces
  have ab : (x::y::(A++B)).Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.mem_append,not_or,List.nodup_append']
    tauto
  have ap : (x::y::(A++P)).Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.mem_append,not_or,List.nodup_append']
    tauto
  have bp : (x::y::(B++P)).Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.mem_append,not_or,List.nodup_append']
    tauto
  have hab := twoArmCycle G x y A B ab (paths A (by simp)) (paths B (by simp))
  have hap := twoArmCycle G x y A P ap (paths A (by simp)) (paths P (by simp))
  have hbp := twoArmCycle G x y B P bp (paths B (by simp)) (paths P (by simp))
  have covers (d : ℕ) (s : V → Prop) (dyad : ∃ k : ℕ, 2 ≤ k ∧ d=2^k)
      (build : 3 ≤ d → ∃ c : (cycleGraph d).Copy G, ∀ z, z ∈ Set.range c ↔ s z) :
      ∀ f : G ≃g G, s (f r) := by
    obtain ⟨k,hk,rfl⟩ := dyad
    have big : 4 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    obtain ⟨c,hc⟩ := build (by omega)
    exact fun f => (hc _).mp (forced k hk c f)
  have misses (d : ℕ) (s : V → Prop)
      (near : 3 ≤ d ∧ ∃ k : ℕ, 2 ≤ k ∧ (d+1=2^k ∨ d+2=2^k))
      (build : 3 ≤ d → ∃ c : (cycleGraph d).Copy G, ∀ z, z ∈ Set.range c ↔ s z) :
      ∀ f : G ≃g G, ¬ s (f r) := by
    obtain ⟨hd,k,hk,e⟩ := near
    obtain ⟨c,hc⟩ := build hd
    exact fun f h => obstruction ⟨d,k,c,f,hd,hk,(hc _).mpr h,e⟩
  have original := covers _ _ base hab
  constructor
  · intro near
    have excluded := misses _ _ near hap
    have confined (f : G ≃g G) : f r ∈ B := by
      rcases original f with h | h | h | h
      · exact (excluded f (Or.inl h)).elim
      · exact (excluded f (Or.inr (Or.inl h))).elim
      · exact (excluded f (Or.inr (Or.inr (Or.inl h)))).elim
      · exact h
    refine ⟨confined,?_⟩
    intro other
    let f : G ≃g G := RelIso.refl _
    exact misses _ _ other hbp f (Or.inr (Or.inr (Or.inl (confined f))))
  · intro da db f
    have h₁ := original f
    have h₂ := covers _ _ da hap f
    have h₃ := covers _ _ db hbp f
    have sepAB : A.Disjoint B := List.disjoint_of_nodup_append ab.of_cons.of_cons
    have sepAP : A.Disjoint P := List.disjoint_of_nodup_append ap.of_cons.of_cons
    have sepBP : B.Disjoint P := List.disjoint_of_nodup_append bp.of_cons.of_cons
    by_cases xeq : f r = x
    · exact Or.inl xeq
    by_cases yeq : f r = y
    · exact Or.inr yeq
    simp only [xeq,yeq,false_or] at h₁ h₂ h₃
    rcases h₁ with a|b
    · exact (h₃.elim (sepAB a) (sepAP a)).elim
    · exact (h₂.elim (fun a => sepAB a b) (sepBP b)).elim

/-- Counting possible images of the root inside a discarded path interior. -/
theorem orbitBoundOnList {V : Type} [Fintype V] (G : SimpleGraph V) (r : V) (B : List V)
    (h : ∀ f : G ≃g G, f r ∈ B) :
    {v | ∃ f : G ≃g G, f r=v}.ncard ≤ B.length := by
  classical
  have sub : {v | ∃ f : G ≃g G, f r=v} ⊆ (B.toFinset : Set V) := by
    rintro _ ⟨f,rfl⟩
    exact List.mem_toFinset.mpr (h f)
  calc
    _ ≤ (B.toFinset : Set V).ncard := Set.ncard_le_ncard sub
    _ = B.toFinset.card := Set.ncard_coe_finset _
    _ ≤ B.length := List.toFinset_card_le _

/-- An ear saving one or two edges on a dyadic cycle gives the required
length whenever the retained cycle has at least three vertices. -/
theorem savedEdges {a b p k : ℕ} (base : a+b+2=2^k) (large : 3 ≤ a+p+2)
    (hk : 2 ≤ k) (save : b=p+1 ∨ b=p+2) :
    3 ≤ a+p+2 ∧ ∃ j : ℕ, 2 ≤ j ∧ ((a+p+2)+1=2^j ∨ (a+p+2)+2=2^j) := by
  exact ⟨large,k,hk,by omega⟩

/-- The rerouted copy solves the rooted step if its length is one or two
below the original power and the discarded interior cannot hold the orbit.
The other reroute having a target length suffices at any orbit size. -/
theorem bypassSolves {V : Type} [Fintype V] (G : SimpleGraph V) (r x y : V)
    (A B P : List V) (clean : (x::y::(A++B++P)).Nodup)
    (paths : ∀ L ∈ [A,B,P], (x::(L++[y])).IsChain G.Adj)
    (forced : ∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G,
      ∀ f : G ≃g G, f r ∈ Set.range c)
    {k : ℕ} (hk : 2 ≤ k) (base : A.length+B.length+2=2^k)
    (large : 3 ≤ A.length+P.length+2) (save : B.length=P.length+1 ∨ B.length=P.length+2)
    (hit : B.length < {v | ∃ f : G ≃g G, f r=v}.ncard ∨
      (3 ≤ B.length+P.length+2 ∧ ∃ j : ℕ, 2 ≤ j ∧
        ((B.length+P.length+2)+1=2^j ∨ (B.length+P.length+2)+2=2^j))) :
    ∃ (n k : ℕ) (c : (cycleGraph n).Copy G) (f : G ≃g G),
      3 ≤ n ∧ 2 ≤ k ∧ f r ∈ Set.range c ∧ (n+1=2^k ∨ n+2=2^k) := by
  by_contra h
  obtain ⟨confined,other⟩ := (thetaObstruction G r forced h x y A B P clean paths
    ⟨k,hk,base⟩).1 (savedEdges base large hk save)
  exact hit.elim (fun small => small.not_ge (orbitBoundOnList G r B confined)) other

/-- On any dyadic cycle of length at least four, a chord spanning two
edges settles the rooted step. At length at least eight, a chord spanning
three edges suffices if the forced orbit has at least three vertices. -/
theorem shortChordSolves {V : Type} [Fintype V] (G : SimpleGraph V) (r x y : V)
    (A B : List V) (clean : (x::y::(A++B)).Nodup)
    (left : (x::(A++[y])).IsChain G.Adj) (right : (x::(B++[y])).IsChain G.Adj)
    (chord : G.Adj x y)
    (forced : ∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G,
      ∀ f : G ≃g G, f r ∈ Set.range c)
    {k : ℕ} (hk : 2 ≤ k) (base : A.length+B.length+2=2^k)
    (short : B.length=1 ∨ (B.length=2 ∧ 3 ≤ k ∧ 3 ≤ {v | ∃ f : G ≃g G, f r=v}.ncard)) :
    ∃ (n k : ℕ) (c : (cycleGraph n).Copy G) (f : G ≃g G),
      3 ≤ n ∧ 2 ≤ k ∧ f r ∈ Set.range c ∧ (n+1=2^k ∨ n+2=2^k) := by
  have four : 4 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0<2) hk
  refine bypassSolves G r x y A B [] (by simpa using clean) ?_ forced hk base ?_ ?_ ?_
  · simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
    exact ⟨left,right,by simpa using chord⟩
  · change 3 ≤ A.length+0+2
    rcases short with h|⟨h,three,_⟩
    · omega
    · have eight : 8 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0<2) three
      omega
  · change B.length=0+1 ∨ B.length=0+2
    exact short.imp_right And.left
  · rcases short with h|⟨h,_,orb⟩
    · right
      simp only [List.length_nil,add_zero,h]
      exact ⟨by decide,2,by decide,Or.inl rfl⟩
    · exact Or.inl (by omega)

/-- Equal component sizes and the degree bound in an induced proper orbit of
a connected cubic graph. Every component with at least three vertices yields
a cycle of exactly its order through the root. -/
private theorem orbitComponentData {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (conn : G.Connected) (cubic : ∀ v, G.degree v = 3)
    (O : Set V) (orb : ∀ v, v ∈ O ↔ ∃ f : G ≃g G, f r = v) (proper : ∃ v, v ∉ O) :
    ∃ n : ℕ, O.ncard = Nat.card (G.induce O).ConnectedComponent * n ∧
      (3 ≤ n → (∀ v : O, ((G.induce O).neighborSet v).ncard = 2) ∧ ∃ c : (cycleGraph n).Copy G, r ∈ Set.range c) := by
  classical
  let K := G.induce O
  let a : O := ⟨r,(orb _).mpr ⟨SimpleGraph.Iso.refl,rfl⟩⟩
  let A := K.connectedComponentMk a
  have trans (x y : O) : ∃ g : K ≃g K, g x = y := by
    obtain ⟨f,hf⟩ := (orb _).mp x.property
    obtain ⟨h,hh⟩ := (orb _).mp y.property
    let t := f.symm.trans h
    have inv (v : V) : v ∈ O ↔ t v ∈ O := by
      rw [orb,orb]
      constructor
      · rintro ⟨g,e⟩
        exact ⟨g.trans t,by change t (g r) = t v; rw [e]⟩
      · rintro ⟨g,e⟩
        exact ⟨g.trans t.symm,by change t.symm (g r) = v; rw [e,t.symm_apply_apply]⟩
    refine ⟨⟨t.toEquiv.subtypeEquiv inv,fun {_ _} => t.map_rel_iff⟩,Subtype.ext ?_⟩
    change h (f.symm x) = y
    rw [←hf,f.symm_apply_apply,hh]
  have equal (D : K.ConnectedComponent) : D.supp.ncard = A.supp.ncard := by
    obtain ⟨v,rfl⟩ := D.exists_rep
    obtain ⟨f,h⟩ := trans a v
    have eq : f.connectedComponentEquiv A = K.connectedComponentMk v := by
      change K.connectedComponentMk (f a) = _
      rw [h]
    change (K.connectedComponentMk v).supp.ncard = _
    rw [←eq]
    exact Nat.card_congr (ConnectedComponent.isoEquivSupp f A).symm
  have count := Fintype.card_congr (Equiv.sigmaFiberEquiv K.connectedComponentMk)
  rw [Fintype.card_sigma,Set.fintypeCard_eq_ncard] at count
  have fiber (D : K.ConnectedComponent) :
      Fintype.card {x // K.connectedComponentMk x = D} = A.supp.ncard := by
    rw [←Nat.card_eq_fintype_card]
    change Nat.card D.supp = _
    exact (Nat.card_coe_set_eq D.supp).trans (equal D)
  simp only [fiber,Finset.sum_const,Finset.card_univ,smul_eq_mul] at count
  refine ⟨A.supp.ncard,by simpa [Nat.card_eq_fintype_card] using count.symm,?_⟩
  intro three
  have exits : ∃ u ∈ O, ∃ w ∉ O, G.Adj u w := by
    by_contra! closed
    obtain ⟨v,hv⟩ := proper
    obtain ⟨p⟩ := conn.preconnected r v
    have follow {x y : V} (q : G.Walk x y) (hx : x ∈ O) : y ∈ O := by
      induction q with
      | nil => exact hx
      | cons e _ ih => apply ih; by_contra h; exact closed _ hx _ h e
    exact hv (follow p a.property)
  obtain ⟨u,hu,w,hw,e⟩ := exits
  let b : O := ⟨u,hu⟩
  have bound : K.degree b < 3 := by
    have strict : G.neighborFinset u ∩ O.toFinset ⊂ G.neighborFinset u := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.inter_subset_left,fun eq => hw ?_⟩
      have h := (G.mem_neighborFinset u w).mpr e
      rw [←eq] at h
      exact Set.mem_toFinset.mp (Finset.mem_inter.mp h).2
    have small := Finset.card_lt_card strict
    rw [←map_neighborFinset_induce (G := G) b,Finset.card_map,card_neighborFinset_eq_degree,
      card_neighborFinset_eq_degree,cubic] at small
    exact small
  have reg (v : O) : K.degree v = K.degree b := by
    obtain ⟨f,h⟩ := trans b v
    rw [←h,f.degree_eq]
  have lower : 2 ≤ K.degree b := by
    by_contra! low
    have close {x y : O} (q : K.Walk x y) : x = y ∨ K.Adj x y := by
      induction q with
      | nil => exact Or.inl rfl
      | @cons x v y e _ ih =>
        rcases ih with rfl|vy
        · exact Or.inr e
        by_cases xy : x = y
        · exact Or.inl xy
        have sub : ({x,y} : Finset O) ⊆ K.neighborFinset v := by
          simp [Finset.insert_subset_iff,e.symm,vy]
        have h := Finset.card_le_card sub
        simp [xy,reg] at h
        omega
    have sub : A.supp.toFinset ⊆ insert a (K.neighborFinset a) := by
      intro y hy
      have hym : y ∈ A.supp := Set.mem_toFinset.mp hy
      obtain ⟨p⟩ := ConnectedComponent.exact (A.mem_supp_iff y |>.mp hym).symm
      rcases close p with h|h
      · exact Finset.mem_insert.mpr (Or.inl h.symm)
      · exact Finset.mem_insert.mpr (Or.inr ((K.mem_neighborFinset _ _).mpr h))
    have h := Finset.card_le_card sub
    have upper := Finset.card_insert_le a (K.neighborFinset a)
    rw [card_neighborFinset_eq_degree,reg] at upper
    rw [Set.ncard_eq_toFinset_card'] at three
    omega
  have degree (v : O) : (K.neighborSet v).ncard = 2 := by
    rw [Set.ncard_eq_toFinset_card']
    change K.degree v = 2
    rw [reg]; omega
  obtain ⟨_,⟨c⟩⟩ := cycleOfComponentOrder K degree a
  let embed : K.Copy G := ⟨⟨Subtype.val,fun h => h⟩,Subtype.val_injective⟩
  let j : Fin A.supp.ncard := ⟨0,by omega⟩
  obtain ⟨g,hg⟩ := (orb _).mp (c j).property
  let d := g.symm.toCopy.comp (embed.comp c)
  have hit : r ∈ Set.range d := ⟨j,by change g.symm (c j) = r; rw [←hg,g.symm_apply_apply]⟩
  exact ⟨degree,d,hit⟩

/-- The common component order of a proper root orbit gives a rooted cycle
when that order is at least three. -/
theorem orbitComponentOrder {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (conn : G.Connected) (cubic : ∀ v, G.degree v = 3)
    (O : Set V) (orb : ∀ v, v ∈ O ↔ ∃ f : G ≃g G, f r = v) (proper : ∃ v, v ∉ O) :
    ∃ n : ℕ, O.ncard = Nat.card (G.induce O).ConnectedComponent * n ∧
      (3 ≤ n → ∃ c : (cycleGraph n).Copy G, r ∈ Set.range c) := by
  obtain ⟨n,h,more⟩ := orbitComponentData G r conn cubic O orb proper
  exact ⟨n,h,fun hn => (more hn).2⟩

open Fin.NatCast in
/-- Each component of the orbit on a cycle has its own exit label. Heading
forward, take an edge from a label in that component to an omitted label. -/
theorem componentsLeOmissions {V : Type} (G : SimpleGraph V) {n : ℕ} (hn : 2 ≤ n)
    (c : (cycleGraph n).Copy G) (O : Set V) (covered : O ⊆ Set.range c)
    (B : Finset (Fin n)) (omits : ∀ j, c j ∈ O ↔ j ∉ B) (nonempty : B.Nonempty) :
    Nat.card (G.induce O).ConnectedComponent ≤ B.card := by
  classical
  let : NeZero n := ⟨by omega⟩
  let K := G.induce O
  have step (i : Fin n) : G.Adj (c i) (c (i+1)) := by
    apply c.toHom.map_rel'
    rw [cycleGraph_adj']
    right
    simp [Nat.mod_eq_of_lt (show 1 < n by omega)]
  have exitLabel (D : K.ConnectedComponent) : ∃ b : B, ∃ v : O,
      c (b.val-1) = v ∧ K.connectedComponentMk v = D := by
    let P (i : Fin n) := ∃ v : O, c i = v ∧ K.connectedComponentMk v = D
    obtain ⟨v,hv⟩ := D.exists_rep
    obtain ⟨j,hj⟩ := covered v.property
    have start : P j := ⟨v,hj,hv⟩
    have exits : ∃ i, P i ∧ ¬ P (i+1) := by
      by_contra! closed
      obtain ⟨b,hb⟩ := nonempty
      have all (m : ℕ) : P (j+(m : Fin n)) := by
        induction m with
        | zero => simpa using start
        | succ m ih => simpa [Nat.cast_add,add_assoc] using closed _ ih
      have atB : P b := by simpa using all (b-j).val
      obtain ⟨w,hw,_⟩ := atB
      exact (omits b).mp (hw ▸ w.property) hb
    obtain ⟨i,⟨w,hw,comp⟩,outside⟩ := exits
    have bad : i+1 ∈ B := by
      by_contra good
      let u : O := ⟨c (i+1),(omits _).mpr good⟩
      have adj : K.Adj w u := by change G.Adj (w : V) (c (i+1)); rw [←hw]; exact step i
      exact outside ⟨u,rfl,(ConnectedComponent.sound adj.reachable).symm.trans comp⟩
    exact ⟨⟨i+1,bad⟩,w,by simpa using hw,comp⟩
  choose b v label comp using exitLabel
  have inj : Function.Injective b := by
    intro i j h
    have eq : v i = v j := Subtype.ext ((label i).symm.trans (h ▸ label j))
    rw [←comp i,←comp j,eq]
  simpa using Nat.card_le_card_of_injective _ inj

/-- For four omissions on a dyadic cycle of order at least sixteen, only
one component or three equal components remain. Three requires even
exponent at least six. -/
private theorem fourOmissionData {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : V) (conn : G.Connected) (cubic : ∀ v, G.degree v = 3)
    (O : Set V) (orb : ∀ v, v ∈ O ↔ ∃ f : G ≃g G, f r = v) (proper : ∃ v, v ∉ O)
    (forced : ∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G, O ⊆ Set.range c)
    (noNear : ∀ (n k : ℕ) (c : (cycleGraph n).Copy G), 3 ≤ n → 2 ≤ k →
      r ∈ Set.range c → ¬ (n+1=2^k ∨ n+2=2^k))
    {k : ℕ} (hk : 4 ≤ k) (c : (cycleGraph (2^k)).Copy G)
    (B : Finset (Fin (2^k))) (size : B.card = 4) (omits : ∀ j, c j ∈ O ↔ j ∉ B) :
    (∀ v : O, ((G.induce O).neighborSet v).ncard = 2) ∧
    (Nat.card (G.induce O).ConnectedComponent = 1 ∨
      (Nat.card (G.induce O).ConnectedComponent = 3 ∧ Even k ∧ 6 ≤ k)) := by
  classical
  have big : 16 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have covered := forced k (by omega) c
  have eq : Bᶜ.map c.toEmbedding = O.toFinset := by
    ext v
    simp only [Finset.mem_map,Finset.mem_compl,Set.mem_toFinset]
    constructor
    · rintro ⟨j,h,rfl⟩
      exact (omits j).mpr h
    · intro h
      obtain ⟨j,rfl⟩ := covered h
      exact ⟨j,(omits j).mp h,rfl⟩
  have total : O.ncard+4 = 2^k := by
    rw [Set.ncard_eq_toFinset_card',←eq,Finset.card_map,Finset.card_compl,Fintype.card_fin,size]
    omega
  obtain ⟨n,order,ring⟩ := orbitComponentData G r conn cubic O orb proper
  let t := Nat.card (G.induce O).ConnectedComponent
  change O.ncard = t*n at order
  have cap : t ≤ 4 := size ▸ componentsLeOmissions G (by omega) c O covered B omits
    (Finset.card_pos.mp (by omega))
  have nLarge : 3 ≤ n := by
    by_contra! small
    have bound := Nat.mul_le_mul cap (show n ≤ 2 by omega)
    omega
  obtain ⟨degree,w,hit⟩ := ring nLarge
  refine ⟨degree,?_⟩
  have few : t ≠ 0 := by intro h; rw [h,zero_mul] at order; omega
  change t = 1 ∨ t = 3 ∧ Even k ∧ 6 ≤ k
  interval_cases t
  · contradiction
  · exact Or.inl rfl
  · exfalso
    obtain ⟨s,rfl⟩ : ∃ s, k=s+1 := ⟨k-1,by omega⟩
    rw [pow_succ] at total
    exact noNear n s w nLarge (by omega) hit (Or.inr (by omega))
  · have parity : Even k := by
      by_contra h
      obtain ⟨b,hb⟩ := (Nat.not_even_iff_odd.mp h)
      have modFour (j : ℕ) : 4^j % 3 = 1 := by
        induction j with
        | zero => decide
        | succ j ih => rw [pow_succ,Nat.mul_mod,ih]
      have modTwo : 2^k % 3 = 2 := by
        rw [hb,pow_succ,pow_mul,Nat.mul_mod]
        change (4^b % 3 * (2 % 3)) % 3 = 2
        rw [modFour]
      omega
    have notFour : k ≠ 4 := by
      rintro rfl
      norm_num at total
      have eqn : n=4 := by omega
      subst n
      have upper := Set.ncard_le_ncard (forced 2 (by decide) w)
      rw [Set.ncard_range_of_injective (f := (w : Fin 4 → V)) w.injective] at upper
      simp at upper
      omega
    exact Or.inr ⟨rfl,parity,by obtain ⟨b,h⟩ := parity; omega⟩
  · exfalso
    obtain ⟨s,rfl⟩ : ∃ s, k=s+2 := ⟨k-2,by omega⟩
    rw [pow_add] at total
    exact noNear n s w nLarge (by omega) hit (Or.inl (by omega))

/-- With four omissions only one component or three equal components survive. -/
theorem fourOmissionComponents {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : V) (conn : G.Connected) (cubic : ∀ v, G.degree v = 3)
    (O : Set V) (orb : ∀ v, v ∈ O ↔ ∃ f : G ≃g G, f r = v) (proper : ∃ v, v ∉ O)
    (forced : ∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G, O ⊆ Set.range c)
    (noNear : ∀ (n k : ℕ) (c : (cycleGraph n).Copy G), 3 ≤ n → 2 ≤ k →
      r ∈ Set.range c → ¬ (n+1=2^k ∨ n+2=2^k))
    {k : ℕ} (hk : 4 ≤ k) (c : (cycleGraph (2^k)).Copy G)
    (B : Finset (Fin (2^k))) (size : B.card = 4) (omits : ∀ j, c j ∈ O ↔ j ∉ B) :
    Nat.card (G.induce O).ConnectedComponent = 1 ∨
      (Nat.card (G.induce O).ConnectedComponent = 3 ∧ Even k ∧ 6 ≤ k) := (fourOmissionData G r conn cubic O orb proper forced noNear hk c B size omits).2

/-- Cancelling the common edges of two cycle unions preserves the cycle-union
property when their union has maximum degree at most three. -/
theorem cancelCycles {V : Type*} [Finite V] (C D : SimpleGraph V)
    (hc : C.IsCycles) (hd : D.IsCycles)
    (subcubic : ∀ v, ((C ⊔ D).neighborSet v).ncard ≤ 3) :
    (symmDiff C D).IsCycles := by
  classical
  intro v nonempty
  let A := C.neighborSet v
  let B := D.neighborSet v
  have eq : (symmDiff C D).neighborSet v = (A \ B) ∪ (B \ A) := by
    rw [symmDiff_def,neighborSet_sup,neighborSet_sdiff,neighborSet_sdiff]
  rw [eq] at nonempty ⊢
  have count := Set.ncard_union_eq (show Disjoint (A \ B) (B \ A) from
    Set.disjoint_left.mpr fun _ h k => h.2 k.1)
  have nz := nonempty.ncard_pos
  have cap := subcubic v
  rw [neighborSet_sup] at cap
  change (A ∪ B).ncard ≤ 3 at cap
  have a : A.ncard = 0 ∨ A.ncard = 2 := by
    by_cases h : A.Nonempty
    · exact Or.inr (hc h)
    · exact Or.inl (by rw [Set.not_nonempty_iff_eq_empty.mp h]; simp)
  have b : B.ncard = 0 ∨ B.ncard = 2 := by
    by_cases h : B.Nonempty
    · exact Or.inr (hd h)
    · exact Or.inl (by rw [Set.not_nonempty_iff_eq_empty.mp h]; simp)
  have ab := Set.ncard_sdiff_add_ncard A B
  have ba := Set.ncard_sdiff_add_ncard B A
  rw [Set.union_comm B A] at ba
  have ub := Set.ncard_union_le A B
  omega

/-- A two-regular graph on eight vertices has a triangle, square, or octagon. -/
theorem eightRing {V : Type} [Fintype V] (K : SimpleGraph V)
    (reg : ∀ v, (K.neighborSet v).ncard = 2) (eight : Fintype.card V = 8) :
    ∃ n, (n = 3 ∨ n = 4 ∨ n = 8) ∧ cycleGraph n ⊑ K := by
  classical
  by_contra! no
  have bound (v : V) : 5 ≤ (K.connectedComponentMk v).supp.ncard := by
    obtain ⟨low,w⟩ := cycleOfComponentOrder K reg v
    by_contra! small
    exact (no (K.connectedComponentMk v).supp.ncard (by omega)).false w.some
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  let A := K.connectedComponentMk a
  have all : A.supp = Set.univ := by
    apply Set.eq_univ_of_forall
    intro b
    by_contra outside
    let B := K.connectedComponentMk b
    have dis : Disjoint A.supp B.supp := Set.disjoint_left.mpr fun _ ha hb =>
      outside ((A.mem_supp_iff b).mpr (ConnectedComponent.eq_of_common_vertex ha hb).symm)
    have count := Set.ncard_union_eq dis
    have cap := Set.ncard_le_ncard (Set.subset_univ (A.supp ∪ B.supp))
    have ha := bound a
    have hb := bound b
    change 5 ≤ A.supp.ncard at ha
    change 5 ≤ B.supp.ncard at hb
    simp only [Set.ncard_univ,Nat.card_eq_fintype_card,eight] at cap
    omega
  obtain ⟨_,ring⟩ := cycleOfComponentOrder K reg a
  change cycleGraph A.supp.ncard ⊑ K at ring
  rw [all,Set.ncard_univ,Nat.card_eq_fintype_card,eight] at ring
  exact (no 8 (by simp)).false ring.some

/-- Four omitted labels and four retained labels next to an omission leave a
cycle of length three, four or eight after cancelling all internal ring edges.
Every triangle produced by this construction meets the retained set. -/
theorem fourBoundaryRing {n : ℕ} (hn : 9 ≤ n) (H : SimpleGraph (Fin n))
    (subcubic : ∀ v, (H.neighborSet v).ncard ≤ 3) (ring : cycleGraph n ≤ H)
    (S : Set (Fin n)) (internal : ∀ i ∈ S, (H.neighborSet i ∩ S).ncard = 2)
    (four : Sᶜ.ncard = 4)
    (boundary : {i | i ∈ S ∧ ∃ j, (cycleGraph n).Adj i j ∧ j ∉ S}.ncard = 4) :
    ∃ m, ∃ c : (cycleGraph m).Copy H, (m = 3 ∨ m = 4 ∨ m = 8) ∧
      (m = 3 → ∃ i, c i ∈ S) := by
  classical
  let C := cycleGraph n
  let D : SimpleGraph (Fin n) :=
    { Adj := fun i j => i ∈ S ∧ j ∈ S ∧ H.Adj i j
      symm := ⟨fun _ _ h => ⟨h.2.1,h.1,h.2.2.symm⟩⟩
      loopless := ⟨fun _ h => H.loopless.irrefl _ h.2.2⟩ }
  let K := symmDiff C D
  have base (i) : (C.neighborSet i).ncard = 2 := by
    obtain ⟨t,ht⟩ : ∃ t, n=t+3 := ⟨n-3,by omega⟩
    subst n
    rw [Set.ncard_eq_toFinset_card']
    exact cycleGraph_degree_three_le
  have inside (i) (hi : i ∈ S) : D.neighborSet i = H.neighborSet i ∩ S := by
    ext j
    change (i ∈ S ∧ j ∈ S ∧ H.Adj i j) ↔ H.Adj i j ∧ j ∈ S
    tauto
  have leH : C ⊔ D ≤ H := sup_le ring (fun _ _ h => h.2.2)
  have cycles : K.IsCycles := by
    apply cancelCycles C D (fun {i} _ => base i) _ (fun i =>
      (Set.ncard_le_ncard (show (C ⊔ D).neighborSet i ⊆ H.neighborSet i from
        fun _ h => leH h)).trans (subcubic i))
    intro i h
    obtain ⟨j,hj⟩ := h
    rw [inside i hj.1]
    exact internal i hj.1
  have diff (i j) : K.Adj i j ↔
      (C.Adj i j ∧ ¬ D.Adj i j) ∨ (D.Adj i j ∧ ¬ C.Adj i j) := Iff.rfl
  have supp : K.support = Sᶜ ∪ {i | i ∈ S ∧ ∃ j, C.Adj i j ∧ j ∉ S} := by
    ext i
    by_cases hi : i ∈ S
    · simp only [Set.mem_union,Set.mem_compl_iff,hi,not_true_eq_false,false_or,
        Set.mem_ofPred_eq,true_and]
      constructor
      · intro h
        by_contra! closed
        have sub : C.neighborSet i ⊆ D.neighborSet i :=
          fun j edge => ⟨hi,closed j edge,ring edge⟩
        have eq := Set.eq_of_subset_of_ncard_le sub (by rw [inside i hi,internal i hi,base])
        obtain ⟨j,hj⟩ := h
        rcases (diff i j).mp hj with ⟨a,b⟩|⟨a,b⟩
        · exact b (sub a)
        · exact b (eq.ge a)
      · rintro ⟨j,hj,out⟩
        exact ⟨j,(diff i j).mpr (Or.inl ⟨hj,fun d => out d.2.1⟩)⟩
    · have pos := (Set.ncard_pos (Set.toFinite (C.neighborSet i))).mp (by rw [base]; decide)
      obtain ⟨j,hj⟩ := pos
      exact iff_of_true ⟨j,(diff i j).mpr (Or.inl ⟨hj,fun d => hi d.1⟩)⟩ (Or.inl hi)
  have size : K.support.ncard = 8 := by
    have dis : Disjoint Sᶜ {i | i ∈ S ∧ ∃ j, C.Adj i j ∧ j ∉ S} :=
      Set.disjoint_left.mpr fun _ h k => h k.1
    rw [supp,Set.ncard_union_eq dis,four,boundary]
  let J := K.induce K.support
  have reg (i : K.support) : (J.neighborSet i).ncard = 2 := by
    rw [Set.ncard_eq_toFinset_card']
    change (K.induce K.support).degree i = 2
    rw [degree_induce_support]
    exact (Set.ncard_eq_toFinset_card' _).symm.trans (cycles i.property)
  obtain ⟨m,hm,⟨w⟩⟩ := eightRing J reg (by rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]; exact size)
  have kle : K ≤ H := (show K ≤ C ⊔ D from symmDiff_le_sup).trans leH
  let emb : J.Copy H := ⟨⟨Subtype.val,fun h => kle h⟩,Subtype.val_injective⟩
  refine ⟨m,emb.comp w,hm,?_⟩
  rintro rfl
  by_contra! miss
  have baseEdge (a b : Fin 3) (e : (cycleGraph 3).Adj a b) :
      C.Adj (w a).val (w b).val := by
    have h : K.Adj (w a).val (w b).val := w.toHom.map_rel' e
    rcases (diff _ _).mp h with h|h
    · exact h.1
    · exact (miss a h.1.1).elim
  have e := baseEdge 0 1 (by decide)
  have f := baseEdge 1 2 (by decide)
  have g := baseEdge 2 0 (by decide)
  have step (x y : Fin n) (edge : C.Adj x y) :
      x.val+1=y.val ∨ y.val+1=x.val ∨ x.val+1=n ∧ y.val=0 ∨ y.val+1=n ∧ x.val=0 := by
    have delta (a b : Fin n) (h : (a-b).val=1) :
        b.val+1=a.val ∨ b.val+1=n ∧ a.val=0 := by
      have eq := Fin.intCast_val_sub_eq_sub_add_ite a b
      rw [h] at eq
      split at eq <;> omega
    rcases cycleGraph_adj'.mp edge with h|h
    · rcases delta _ _ h with h|h <;> tauto
    · rcases delta _ _ h with h|h <;> tauto
  have h₁ := step _ _ e
  have h₂ := step _ _ f
  have h₃ := step _ _ g
  omega

/-- If each retained label has two retained neighbours in the ambient
subcubic graph, the boundary has two distinct endpoints for each gap. -/
theorem cyclicBoundaryCount {t : ℕ} (H : SimpleGraph (Fin (t+3)))
    (subcubic : ∀ v, (H.neighborSet v).ncard ≤ 3) (ring : cycleGraph (t+3) ≤ H)
    (S : Set (Fin (t+3))) (internal : ∀ i ∈ S, (H.neighborSet i ∩ S).ncard = 2) :
    {i | i ∈ S ∧ ∃ j, (cycleGraph (t+3)).Adj i j ∧ j ∉ S}.ncard =
      2 * {i | i ∈ S ∧ i+1 ∉ S}.ncard := by
  classical
  let A : Set (Fin (t+3)) := {i | i ∈ S ∧ i+1 ∉ S}
  let B : Set (Fin (t+3)) := {i | i ∈ S ∧ i-1 ∉ S}
  let e : Fin (t+3) ≃ Fin (t+3) := Equiv.addRight 1
  let T := e ⁻¹' S
  have shift (U : Set (Fin (t+3))) : (e ⁻¹' U).ncard = U.ncard :=
    Set.ncard_preimage_of_injective_subset_range e.injective (by simp [e.surjective.range_eq])
  have same : A.ncard = B.ncard := by
    have bs : e ⁻¹' B = T \ S := by
      ext i
      change (i+1 ∈ S ∧ i+1-1 ∉ S) ↔ i+1 ∈ S ∧ i ∉ S
      simp
    have ht := shift S
    change T.ncard = S.ncard at ht
    have ab := Set.ncard_sdiff_add_ncard S T
    have ba := Set.ncard_sdiff_add_ncard T S
    rw [Set.union_comm T S] at ba
    change (S \ T).ncard = B.ncard
    rw [← shift B,bs]
    omega
  have union : {i | i ∈ S ∧ ∃ j, (cycleGraph (t+3)).Adj i j ∧ j ∉ S} = A ∪ B := by
    ext i
    have pair (j : Fin (t+3)) : (cycleGraph (t+3)).Adj i j ↔ j=i-1 ∨ j=i+1 := by
      change j ∈ (cycleGraph (t+3)).neighborSet i ↔ _
      rw [cycleGraph_neighborSet]
      rfl
    change (_ ∧ _) ↔ (_ ∧ _) ∨ (_ ∧ _)
    simp only [pair]
    grind
  have dis : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro i ha hb
    have h₁ := ha.1
    have out : (cycleGraph (t+3)).neighborSet i ⊆ H.neighborSet i \ S := by
      intro j hj
      refine ⟨ring hj,?_⟩
      rw [cycleGraph_neighborSet] at hj
      rcases hj with h|h
      · exact h ▸ hb.2
      · exact h ▸ ha.2
    have base : ((cycleGraph (t+3)).neighborSet i).ncard = 2 := by
      rw [Set.ncard_eq_toFinset_card']; exact cycleGraph_degree_three_le
    have low := Set.ncard_le_ncard out
    have eq := Set.ncard_sdiff_add_ncard_of_subset
      (show H.neighborSet i ∩ S ⊆ H.neighborSet i from Set.inter_subset_left)
    have diff : H.neighborSet i \ (H.neighborSet i ∩ S) = H.neighborSet i \ S := by
      ext; simp only [Set.mem_sdiff,Set.mem_inter_iff]; tauto
    rw [diff,internal i h₁] at eq
    have cap := subcubic i
    omega
  rw [union,Set.ncard_union_eq dis,←same]
  change A.ncard+A.ncard=2*A.ncard
  omega

/-- In the forced-orbit case a square or octagon is too short to cover the
orbit, and a triangle meeting the orbit transports to the root. -/
theorem fourOmissionBoundary {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (cubic : ∀ v, G.degree v = 3) (O : Set V) (reg : ∀ v : O,
      ((G.induce O).neighborSet v).ncard = 2)
    (away : ∀ c : (cycleGraph 3).Copy G, ∀ v ∈ O, v ∉ Set.range c)
    (forced : ∀ s : ℕ, 2 ≤ s → ∀ c : (cycleGraph (2^s)).Copy G, O ⊆ Set.range c)
    {k : ℕ} (hk : 4 ≤ k) (c : (cycleGraph (2^k)).Copy G)
    (B : Finset (Fin (2^k))) (size : B.card = 4) (omits : ∀ j, c j ∈ O ↔ j ∉ B) :
    {i | i ∉ B ∧ i+1 ∈ B}.ncard ≠ 2 := by
  classical
  intro two
  let S : Set (Fin (2^k)) := (↑B : Set _)ᶜ
  let H := G.comap c
  have big : 16 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have cover := forced k (by omega) c
  have im : c '' S = O := by
    ext v
    constructor
    · rintro ⟨j,h,rfl⟩
      exact (omits j).mpr h
    · intro h
      obtain ⟨j,rfl⟩ := cover h
      exact ⟨j,(omits j).mp h,rfl⟩
  have many : 8 < O.ncard := by
    rw [← im,Set.ncard_image_of_injective (f := (c : Fin (2^k) → V)) _ c.injective,Set.ncard_compl]
    simp only [Set.ncard_coe_finset,Nat.card_eq_fintype_card,Fintype.card_fin,size]
    omega
  have cap (i) : (H.neighborSet i).ncard ≤ 3 := by
    have sub : c '' H.neighborSet i ⊆ G.neighborSet (c i) := by
      rintro _ ⟨j,h,rfl⟩
      exact h
    have h := Set.ncard_le_ncard sub
    rw [Set.ncard_image_of_injective (f := (c : Fin (2^k) → V)) _ c.injective,Set.ncard_eq_toFinset_card' (G.neighborSet _)] at h
    exact h.trans (le_of_eq (cubic _))
  have degree (i) (hi : i ∈ S) : (H.neighborSet i ∩ S).ncard = 2 := by
    let v : O := ⟨c i,(omits i).mpr hi⟩
    have eq : c '' (H.neighborSet i ∩ S) =
        Subtype.val '' ((G.induce O).neighborSet v) := by
      ext z
      constructor
      · rintro ⟨j,h,rfl⟩
        exact ⟨⟨c j,(omits j).mpr h.2⟩,h.1,rfl⟩
      · rintro ⟨⟨z,hz⟩,h,rfl⟩
        obtain ⟨j,rfl⟩ := cover hz
        exact ⟨j,⟨h,(omits j).mp hz⟩,rfl⟩
    have h := congrArg Set.ncard eq
    rwa [Set.ncard_image_of_injective (f := (c : Fin (2^k) → V)) _ c.injective,
      Set.ncard_image_of_injective _ Subtype.val_injective,reg] at h
  have count {n : ℕ} [NeZero n] (hn : 3 ≤ n) (L : SimpleGraph (Fin n))
      (cap : ∀ v, (L.neighborSet v).ncard ≤ 3) (base : cycleGraph n ≤ L)
      (T : Set (Fin n)) (reg : ∀ i ∈ T, (L.neighborSet i ∩ T).ncard = 2) :
      {i | i ∈ T ∧ ∃ j, (cycleGraph n).Adj i j ∧ j ∉ T}.ncard =
        2 * {i | i ∈ T ∧ i+1 ∉ T}.ncard := by
    obtain ⟨t,rfl⟩ : ∃ t, n=t+3 := ⟨n-3,by omega⟩
    exact cyclicBoundaryCount L cap base T reg
  have four := count (by omega : 3 ≤ 2^k) H cap (fun _ _ h => c.toHom.map_rel' h) S degree
  have starts : {i | i ∈ S ∧ i+1 ∉ S}.ncard = 2 := by simpa [S] using two
  rw [starts] at four
  obtain ⟨m,w,hm,touch⟩ := fourBoundaryRing (by omega : 9 ≤ 2^k) H cap
    (fun _ _ h => c.toHom.map_rel' h) S degree (by simpa [S] using size) four
  let embed : H.Copy G := ⟨⟨c,fun h => h⟩,c.injective⟩
  let d := embed.comp w
  have small {s : ℕ} (hs : 2 ≤ s) (eq : m=2^s) : False := by
    have sub : O ⊆ Set.range d := by subst m; exact forced s hs _
    have h := Set.ncard_le_ncard sub
    rw [Set.ncard_range_of_injective (f := (d : Fin m → V)) d.injective] at h
    simp only [Nat.card_eq_fintype_card,Fintype.card_fin] at h
    omega
  rcases hm with rfl|h|h
  · obtain ⟨i,hit⟩ := touch rfl
    exact away d _ ((omits _).mpr hit) ⟨i,rfl⟩
  · exact small (s := 2) (by decide) h
  · exact small (s := 3) (by decide) h

open Fin.NatCast in
/-- A single omitted interval of length d gives a cycle of length d+2
meeting the orbit and missing another orbit vertex. -/
theorem omittedIntervalRing {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (conn : G.Connected) (cubic : ∀ v, G.degree v = 3)
    (proper : ∃ v, ∀ f : G ≃g G, f r ≠ v) {n d : ℕ} (hd : 1 ≤ d) (room : d+3 ≤ n)
    (c : (cycleGraph n).Copy G) (start : Fin n)
    (covered : ∀ g : G ≃g G, g r ∈ Set.range c)
    (interval : ∀ i : Fin n, (∃ g : G ≃g G, g r = c (i+start)) ↔ d ≤ i.val) :
    ∃ (w : (cycleGraph (d+2)).Copy G) (g h : G ≃g G), g r ∈ Set.range w ∧ h r ∉ Set.range w := by
  classical
  let : NeZero n := ⟨by omega⟩
  let F (i : ℕ) := c ((i : Fin n)+start)
  have inj (i j : ℕ) (hi : i < n) (hj : j < n) (h : F i = F j) : i = j := by
    have h' := congrArg Fin.val (add_right_cancel (c.injective h) : (i : Fin n) = j)
    simpa [Fin.val_natCast,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using h'
  have mem (i : ℕ) (hi : i < n) : (∃ g : G ≃g G, g r = F i) ↔ d ≤ i := by
    simpa [F,Fin.val_natCast,Nat.mod_eq_of_lt hi] using interval (i : Fin n)
  have next (i : ℕ) : G.Adj (F i) (F (i+1)) := by
    apply c.toHom.map_rel'
    rw [cycleGraph_adj']
    right
    simp [Nat.cast_add,add_sub_add_right_eq_sub,Nat.mod_eq_of_lt (show 1 < n by omega)]
  let m := n-d
  let f (j : Fin m) := F (j.val+d)
  let l := List.ofFn f
  have len : l.length = m := List.length_ofFn
  have fit (j : Fin m) : j.val+d < n := by have := j.isLt; dsimp [m] at this; omega
  have clean : l.Nodup := List.nodup_ofFn_ofInjective (by
    intro i j h
    have eq := inj _ _ (fit i) (fit j) h
    exact Fin.ext (by omega))
  have path : l.IsChain G.Adj := by
    apply List.isChain_iff_getElem.mpr
    intro i hi
    simpa [l,f,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next (i+d)
  have covers (v : V) : v ∈ l ↔ ∃ g : G ≃g G, g r = v := by
    rw [show l = List.ofFn f from rfl,List.mem_ofFn']
    constructor
    · rintro ⟨j,rfl⟩
      exact (mem _ (fit j)).mpr (by omega)
    · rintro ⟨g,rfl⟩
      obtain ⟨j,hj⟩ := covered g
      let i := (j-start).val
      have eq : F i = g r := by change c (((j-start).val : Fin n)+start) = g r; simpa using hj
      have hi : i < n := (j-start).isLt
      have lower := (mem i hi).mp ⟨g,eq.symm⟩
      refine ⟨⟨i-d,by dsimp [m]; omega⟩,?_⟩
      change F (i-d+d) = g r
      rwa [Nat.sub_add_cancel lower]
  have ml : 3 ≤ m := by dsimp [m]; omega
  have ne : l ≠ [] := List.length_pos_iff.mp (by omega)
  have e := orbitPathEndpoints G r conn cubic proper l (by omega) clean path covers ne
  have chord : G.Adj (F (n-1)) (F d) := by
    rw [List.getLast_eq_getElem,List.head_eq_getElem] at e
    simpa [l,f,show m-1+d = n-1 by dsimp [m]; omega] using e
  let A := List.ofFn (fun i : Fin d => F i.val)
  have apart {i j : ℕ} (hi : i < n) (hj : j < n) (ne : i ≠ j) : F i ≠ F j :=
    fun h => ne (inj _ _ hi hj h)
  have outside (i : ℕ) (hi : i < n) (lo : d ≤ i) : F i ∉ A := by
    intro h
    obtain ⟨j,hj⟩ := (List.mem_ofFn' _ _).mp h
    exact apart (lt_trans j.isLt (by omega)) hi (by omega) hj
  have nd : (F (n-1)::F d::(A++[])).Nodup := by
    have unique : A.Nodup := List.nodup_ofFn_ofInjective (by
      intro i j h
      exact Fin.ext (inj i j (lt_trans i.isLt (by omega)) (lt_trans j.isLt (by omega)) h))
    simp [apart (i := n-1) (j := d) (by omega) (by omega) (by omega),
      outside (n-1) (by omega) (by omega),outside d (by omega) le_rfl,unique]
  have segment : A++[F d] = List.ofFn (fun i : Fin (d+1) => F i.val) := by
    rw [List.ofFn_succ',List.concat_eq_append]
    rfl
  have detour : (F (n-1)::(A++[F d])).IsChain G.Adj := by
    rw [segment]
    apply List.isChain_iff_getElem.mpr
    intro i hi
    cases i with
    | zero =>
      have wrap := next (n-1)
      rw [show n-1+1=n by omega,show F n = F 0 by simp [F]] at wrap
      simpa using wrap
    | succ i => simpa only [List.getElem_cons_succ,List.getElem_ofFn] using next i
  obtain ⟨w,range⟩ := twoArmCycle G (F (n-1)) (F d) A [] nd detour (by simpa using chord)
    (by simp [A]; omega)
  obtain ⟨g,hg⟩ := (mem d (by omega)).mpr le_rfl
  obtain ⟨h,hh⟩ := (mem (d+1) (by omega)).mpr (by omega)
  have inW := (range _).mpr (Or.inr (Or.inl hg))
  have miss : h r ∉ Set.range w := by
    rw [hh,range]
    simp [apart (i := d+1) (j := n-1) (by omega) (by omega) (by omega),
      apart (i := d+1) (j := d) (by omega) (by omega) (by omega),outside (d+1) (by omega) (by omega)]
  have length : A.length+[].length (α := V)+2 = d+2 := by simp [A]
  rw [←length]
  exact ⟨w,g,h,inW,miss⟩

private theorem backToRoot {V : Type} {G : SimpleGraph V} {r : V} {n : ℕ}
    (c : (cycleGraph n).Copy G) (f : G ≃g G) (hit : f r ∈ Set.range c) :
    ∃ d : (cycleGraph n).Copy G, r ∈ Set.range d := by
  obtain ⟨i,hi⟩ := hit
  exact ⟨f.symm.toCopy.comp c,i,by change f.symm (c i) = r; rw [hi]; exact f.symm_apply_apply r⟩


namespace HalfOrder
open Function Fin.NatCast MulAction

/-- Four cyclically adjacent vertices with distinct opposite pairs form a square. -/
theorem square_of_four {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (da : G.Adj d a)
    (ac : a ≠ c) (bd : b ≠ d) : cycleGraph 4 ⊑ G := by
  obtain ⟨c₄,_⟩ := exactRing G [a,b,c,d] (by simp)
    (by simp [ab.ne,ac,da.ne.symm,bc.ne,bd,cd.ne])
    (by simp [ab,bc,cd]) (by simpa using da)
  exact ⟨c₄⟩

/-- If every copy of a cycle uses r, then every automorphic image of r
lies in every copy, without a transitivity assumption. -/
theorem orbit_on_cycle {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (r : V) (hit : ∀ c : (cycleGraph n).Copy G, r ∈ Set.range c)
    (c : (cycleGraph n).Copy G) (g : G ≃g G) : g r ∈ Set.range c := by
  obtain ⟨i,hi⟩ := hit (g.symm.toCopy.comp c)
  refine ⟨i,?_⟩
  change g.symm (c i) = r at hi
  simpa using congrArg g hi

/-- In a vertex-transitive graph, a length whose every cycle visits one
vertex can only be the full graph order. -/
theorem transitive_cycle_spans {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (r : V) (transitive : ∀ x, ∃ g : G ≃g G, g r = x)
    (hit : ∀ c : (cycleGraph n).Copy G, r ∈ Set.range c)
    (c : (cycleGraph n).Copy G) : n = Fintype.card V := by
  have onto : Surjective c := by
    intro x
    obtain ⟨g,rfl⟩ := transitive x
    exact orbit_on_cycle r hit c g
  simpa using Fintype.card_congr (Equiv.ofBijective c ⟨fun _ _ h => c.injective h,onto⟩)

/-- A vertex-transitive graph of order other than a power of two has a
dyadic cycle avoiding any specified vertex as soon as one such cycle exists. -/
theorem avoiding_cycle {V : Type*} [Fintype V] {G : SimpleGraph V}
    (r : V) (transitive : ∀ x, ∃ g : G ≃g G, g r = x)
    {k : ℕ} (proper : 2^k ≠ Fintype.card V) (someCycle : cycleGraph (2^k) ⊑ G) :
    ∃ c : (cycleGraph (2^k)).Copy G, r ∉ Set.range c := by
  classical
  by_contra! hit
  exact proper (transitive_cycle_spans r transitive hit someCycle.some)

private theorem cycle_of_period {U Z : Type*} {H : SimpleGraph U} (f : Z → Z)
    (label : Z ↪ U) (adj : ∀ z, H.Adj (label z) (label (f z))) (z : Z)
    (large : 3 ≤ minimalPeriod f z) : cycleGraph (minimalPeriod f z) ⊑ H := by
  let t := minimalPeriod f z
  let : NeZero t := ⟨by change 3 ≤ t at large; omega⟩
  let v (i : Fin t) := label (f^[i.val] z)
  have inj : Injective v := by
    intro i j eq
    exact Fin.ext ((iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp
      (label.injective eq))
  have step (i : Fin t) : H.Adj (v i) (v (i + 1)) := by
    have h1 : 1 < t := by change 3 ≤ t at large; omega
    have hi : (i + 1 : Fin t).val = (i.val + 1) % t := by
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt h1]
    change H.Adj (label (f^[i.val] z)) (label (f^[(i + 1 : Fin t).val] z))
    rw [hi, iterate_mod_minimalPeriod_eq, iterate_succ_apply']
    exact adj _
  change cycleGraph t ⊑ H
  refine ⟨⟨⟨v, ?_⟩, inj⟩⟩
  intro i j h
  have h1 : 1 < t := by change 3 ≤ t at large; omega
  have h' : i - j = 1 ∨ j - i = 1 := by
    simpa only [Fin.ext_iff, Fin.val_one', Nat.mod_eq_of_lt h1] using cycleGraph_adj'.mp h
  rcases h' with h' | h'
  · have eq : i = j + 1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h'
    simpa only [eq] using (step j).symm
  · have eq : j = i + 1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h'
    simpa only [eq] using step i

/-- A graph covering with fibers of size at most two lifts a simple n-cycle
to a simple n-cycle or 2n-cycle. Local bijectivity is only needed along
the edges of the base cycle. -/
theorem lift_two {U V : Type*} [Fintype U] {G : SimpleGraph U} {B : SimpleGraph V}
    (q : U → V) (onto : Surjective q)
    (small : ∀ v, Nat.card {u : U // q u=v} ≤ 2) {n : ℕ} (large : 3≤n)
    (c : (cycleGraph n).Copy B)
    (liftEdge : ∀ (u : U) (v : V), B.Adj (q u) v → ∃! w : U, G.Adj u w ∧ q w = v) :
    cycleGraph n ⊑ G ∨ cycleGraph (2*n) ⊑ G := by
  classical
  let : NeZero n := ⟨by omega⟩
  have edge (i : Fin n) : B.Adj (c i) (c (i+1)) := by
    apply c.toHom.map_rel'
    apply cycleGraph_adj'.mpr
    right
    simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  let Fiber (i : Fin n) := {u : U // q u=c i}
  let D := Σ i : Fin n, Fiber i
  have next (z : D) : ∃! w : U, G.Adj z.2.val w ∧ q w=c (z.1+1) := by
    apply liftEdge
    rw [z.2.property]
    exact edge z.1
  let f (z : D) : D := ⟨z.1+1,(next z).choose,(next z).choose_spec.1.2⟩
  let label : D ↪ U := ⟨fun z => z.2.val,by
    rintro ⟨i,a,ha⟩ ⟨j,b,hb⟩ (rfl : a=b)
    obtain rfl := c.injective (ha.symm.trans hb)
    rfl⟩
  have adj (z : D) : G.Adj (label z) (label (f z)) := (next z).choose_spec.1.1
  have inject : Injective f := by
    intro x y h
    have phase : x.1=y.1 := add_right_cancel (congrArg Sigma.fst h : x.1+1=y.1+1)
    have eq : label (f x)=label (f y) := congrArg label h
    apply label.injective
    have same : q (label (f x))=c (x.1+1) := (f x).2.property
    have choices := liftEdge (label (f x)) (c x.1) (same ▸ (edge x.1).symm)
    apply choices.unique
    · exact ⟨(adj x).symm,x.2.property⟩
    · exact ⟨eq ▸ (adj y).symm,y.2.property.trans (congrArg c phase.symm)⟩
  obtain ⟨a,ha⟩ := onto (c 0)
  let start : D := ⟨0,a,ha⟩
  let t := minimalPeriod f start
  have pos : 0<t := by
    apply minimalPeriod_pos_of_mem_periodicPts
    exact inject.mem_periodicPts _
  have tick (m : ℕ) : (f^[m] start).1=(m : Fin n) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [iterate_succ_apply']
      change (f^[m] start).1+1 = _
      rw [ih,Nat.cast_succ]
  have period : n ∣ t := by
    apply Fin.natCast_eq_zero.mp
    exact (tick t).symm.trans (congrArg Sigma.fst (iterate_minimalPeriod (f := f) (x := start)))
  have bound : t ≤ 2*n := by
    apply (minimalPeriod_le_card (f := f) (x := start)).trans
    change Fintype.card (Σ i : Fin n, Fiber i) ≤ 2*n
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _i : Fin n, 2 := Finset.sum_le_sum (fun i _ => by
        simpa only [Nat.card_eq_fintype_card,Fiber] using small (c i))
      _ = _ := by simp [mul_comm]
  obtain ⟨m,hm⟩ := period
  have choices : t=n ∨ t=2*n := by
    by_cases two : 3 ≤ m
    · have low : n*3 ≤ n*m := Nat.mul_le_mul_left n two
      omega
    · interval_cases m <;> simp_all [Nat.mul_comm]
  have lift := cycle_of_period f label adj start (show 3≤t by rcases choices with h|h <;> omega)
  exact choices.elim (fun h => Or.inl (h ▸ lift)) (fun h => Or.inr (h ▸ lift))

/-- Three signed edges on the leaves of a claw force a square in a binary cover
of a tetrahedron. At one leaf, the two incident signs agree. -/
theorem claw_square {V : Type*} {G : SimpleGraph V} (t : V → V) {v a b c : V}
    (va : G.Adj v a) (vb : G.Adj v b) (vc : G.Adj v c)
    (ab : a≠b) (bc : b≠c) (ca : c≠a)
    (na : v≠t a) (nb : v≠t b) (nc : v≠t c)
    (dab : G.Adj a b ∨ (G.Adj a (t b) ∧ G.Adj (t a) b))
    (dbc : G.Adj b c ∨ (G.Adj b (t c) ∧ G.Adj (t b) c))
    (dca : G.Adj c a ∨ (G.Adj c (t a) ∧ G.Adj (t c) a)) : cycleGraph 4 ⊑ G := by
  rcases dab with u|u <;> rcases dbc with w|w <;> rcases dca with z|z
  · exact square_of_four va u w vc.symm vb.ne ca.symm
  · exact square_of_four va u w vc.symm vb.ne ca.symm
  · exact square_of_four vc z u vb.symm va.ne bc.symm
  · exact square_of_four vb w.1 z.2 va.symm nc ab.symm
  · exact square_of_four vb w z va.symm vc.ne ab.symm
  · exact square_of_four vc z.1 u.2 vb.symm na bc.symm
  · exact square_of_four va u.1 w.2 vc.symm nb ca.symm
  · exact square_of_four va u.1 w.2 vc.symm nb ca.symm

/-- Every two-sheeted cover of K4 contains a square. -/
theorem square_over_four {V W : Type*} [Fintype W] {G : SimpleGraph V} {B : SimpleGraph W}
    [DecidableRel B.Adj] (order : Fintype.card W=4) (cubic : ∀ w, B.degree w=3)
    (t : V → V) (twice : ∀ x,t (t x)=x) (sym : ∀ a b,G.Adj a b → G.Adj (t a) (t b))
    (q : V → W) (onto : Surjective q) (pair : ∀ x y, q x=q y ↔ x=y ∨ x=t y)
    (lift : ∀ x y, B.Adj (q x) y → ∃ w, G.Adj x w ∧ q w=y) : cycleGraph 4 ⊑ G := by
  classical
  let E := (Fintype.equivFinOfCardEq order).symm
  have allAdj (i j : Fin 4) (diff : i ≠ j) : B.Adj (E i) (E j) :=
    ((B.degree_eq_card_sub_one (E i)).mp (by rw [cubic,order]))
      (fun h => diff (E.injective h))
  obtain ⟨v,hv⟩ := onto (E 0)
  have leaves (i : Fin 4) (h : i≠0) : ∃ a, G.Adj v a ∧ q a=E i := by
    apply lift
    rw [hv]
    exact allAdj _ _ h.symm
  obtain ⟨a,va,ha⟩ := leaves 1 (by decide)
  obtain ⟨b,vb,hb⟩ := leaves 2 (by decide)
  obtain ⟨c,vc,hc⟩ := leaves 3 (by decide)
  have qt (x : V) : q (t x)=q x := (pair _ _).mpr (Or.inr rfl)
  have different {x y : V} {i j : Fin 4} (hx : q x=E i) (hy : q y=E j) (diff : i≠j) :
      x≠y ∧ x≠t y := by
    have neq : q x≠q y := fun h => diff (E.injective (hx.symm.trans (h.trans hy)))
    exact ⟨fun h => neq (congrArg q h),fun h => neq ((congrArg q h).trans (qt y))⟩
  have signs {x y : V} {i j : Fin 4} (hx : q x=E i) (hy : q y=E j) (diff : i≠j) :
      G.Adj x y ∨ (G.Adj x (t y) ∧ G.Adj (t x) y) := by
    obtain ⟨w,adj,hw⟩ := lift x (q y) (by rw [hx,hy]; exact allAdj i j diff)
    rcases (pair w y).mp hw with rfl | rfl
    · exact Or.inl adj
    · exact Or.inr ⟨adj,(twice y) ▸ sym _ _ adj⟩
  exact claw_square t va vb vc (different ha hb (by decide)).1 (different hb hc (by decide)).1
    (different hc ha (by decide)).1 (different hv ha (by decide)).2 (different hv hb (by decide)).2
    (different hv hc (by decide)).2 (signs ha hb (by decide)) (signs hb hc (by decide))
    (signs hc ha (by decide))

/-- For a free involution, its pairs are the fibers of a two-to-one map. -/
theorem pair_projection {V : Type} [Fintype V] (t : V → V) (twice : ∀ x, t (t x)=x)
    (free : ∀ x, t x ≠ x) :
    ∃ (W : Type) (_ : Fintype W) (q : V → W), Surjective q ∧
      (∀ x y, q x=q y ↔ x=y ∨ x=t y) ∧ Fintype.card V = Fintype.card W * 2 ∧
      (∀ w, Nat.card {x : V // q x=w}=2) := by
  classical
  let block (x : V) : Set V := {x,t x}
  let W := Set.range block
  let q (x : V) : W := ⟨block x,⟨x,rfl⟩⟩
  have onto : Surjective q := by rintro ⟨_,x,rfl⟩; exact ⟨x,rfl⟩
  have pair (x y : V) : q x=q y ↔ x=y ∨ x=t y := by
    constructor
    · intro h
      have s : x∈block x := Set.mem_insert _ _
      rw [show block x=block y from congrArg Subtype.val h] at s
      exact s
    · rintro (rfl | rfl)
      · rfl
      · apply Subtype.ext
        change ({t y,t (t y)} : Set V)={y,t y}
        rw [twice]
        exact Set.pair_comm _ _
  let : Finite W := Finite.of_surjective q onto
  let : Fintype W := Fintype.ofFinite W
  have fiber (w : W) : Nat.card {x : V // q x=w}=2 := by
    obtain ⟨x,rfl⟩ := onto w
    let f (b : Bool) : {z : V // q z=q x} := if b then
      ⟨t x,(pair _ _).mpr (Or.inr rfl)⟩ else ⟨x,rfl⟩
    have inj : Injective f := by
      intro i j same
      have eq := congrArg Subtype.val same
      cases i <;> cases j <;> simp_all [f,free x,(free x).symm]
    have sur : Surjective f := by
      rintro ⟨z,hz⟩
      rcases (pair z x).mp hz with rfl | rfl
      · exact ⟨false,rfl⟩
      · exact ⟨true,rfl⟩
    exact (Nat.card_congr (Equiv.ofBijective f ⟨inj,sur⟩)).symm.trans (by simp [Nat.card_eq_fintype_card])
  refine ⟨W,inferInstance,q,onto,pair,?_,fiber⟩
  rw [←Fintype.card_congr (Equiv.sigmaFiberEquiv q),Fintype.card_sigma]
  have size (w : W) : Fintype.card {x : V // q x=w}=2 := by
    simpa only [Nat.card_eq_fintype_card] using fiber w
  simp [size]

/-- If the number of points is a power of two, every Sylow 2-subgroup of a
finite transitive group is still transitive on those points. -/
theorem sylow_transitive {A V : Type*} [Group A] [Finite A] [Finite V] [MulAction A V]
    [IsPretransitive A V] (S : Sylow 2 A) {k : ℕ} (card : Nat.card V=2^k) :
    IsPretransitive S V := by
  classical
  constructor
  intro x y
  let H := stabilizer A x
  have eq : H.index=2^k := (index_stabilizer_of_transitive A x).trans card
  have hd : 2^k ∣ H.relIndex S.1 * S.1.index := by
    rw [← Subgroup.inf_relIndex_right,Subgroup.relIndex_mul_index (show H ⊓ S.1 ≤ S.1 from inf_le_right),←eq]
    exact Subgroup.index_dvd_of_le (show H ⊓ S.1 ≤ H from inf_le_left)
  have d : 2^k ∣ H.relIndex S.1 :=
    (Nat.prime_two.coprime_pow_of_not_dvd S.not_dvd_index).symm.dvd_of_dvd_mul_right hd
  have idx : H.relIndex S.1 = (stabilizer S x).index := rfl
  have count : Nat.card V ≤ (orbit S x).ncard := by
    rw [card,←index_stabilizer S x,←idx]
    apply Nat.le_of_dvd _ d
    rw [idx,index_stabilizer S x]
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨x,1,one_smul _ _⟩
  have full : orbit S x=Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    simpa using count
  have mem : y ∈ orbit S x := full ▸ Set.mem_univ y
  exact mem

/-- A nontrivial faithful transitive permutation 2-group contains a central
involution which moves every point. -/
theorem central_pair {V : Type*} [Finite V] (A : Subgroup (Equiv.Perm V))
    [Nontrivial A] (two : IsPGroup 2 A) (transitive : ∀ x y, ∃ g : A, g.val x=y) :
    ∃ t : A, (∀ v, t.val (t.val v)=v) ∧ (∀ v,t.val v≠v) ∧
      (∀ (g : A) v, g.val (t.val v)=t.val (g.val v)) := by
  classical
  let Z := Subgroup.center A
  let : Nontrivial Z := two.center_nontrivial
  obtain ⟨j,pj,card⟩ := (two.to_subgroup Z).nontrivial_iff_card.mp (inferInstance : Nontrivial Z)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (card ▸ dvd_pow_self 2 pj.ne')
  have commute (g : A) (v : V) : g.val (z.val.val v) = z.val.val (g.val v) :=
    congrArg (fun h : A => h.val v) (Subgroup.mem_center_iff.mp z.property g)
  have sq : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have invol (v : V) : z.val.val (z.val.val v)=v := congrArg (fun g : Z => g.val.val v)
    (show z*z=1 by simpa [pow_two] using sq)
  refine ⟨z.val,invol,?_,commute⟩
  intro x fixed
  have ident : z=1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro y
    obtain ⟨g,rfl⟩ := transitive x y
    exact (commute g x).symm.trans (congrArg g.val fixed)
  simp [ident] at hz

/-- An invariant partition gives a quotient action that is again a transitive
permutation 2-group. The only required compatibility is equality of fibers. -/
theorem descend {V W : Type*} (A : Subgroup (Equiv.Perm V)) (two : IsPGroup 2 A)
    (transitive : ∀ x y, ∃ g : A, g.val x=y)
    (q : V → W) (onto : Surjective q) (respects : ∀ (g : A) x y, q x=q y → q (g.val x)=q (g.val y)) :
    ∃ D : Subgroup (Equiv.Perm W), IsPGroup 2 D ∧ (∀ x y, ∃ g : D,g.val x=y) ∧
      ∀ d : D, ∃ g : A, ∀ x, d.val (q x)=q (g.val x) := by
  classical
  let s := surjInv onto
  have qs := rightInverse_surjInv onto
  let f (g : A) (w : W) := q (g.val (s w))
  have equiv (g : A) (v : V) : f g (q v)=q (g.val v) := respects _ _ _ (qs _)
  have mul (g h : A) (w : W) : f g (f h w)=f (g*h) w := by
    obtain ⟨x,rfl⟩ := onto w
    exact (congrArg (f g) (equiv h x)).trans
      ((equiv g (h.val x)).trans (equiv (g*h) x).symm)
  have one (w : W) : f 1 w=w := qs _
  let perm (g : A) : Equiv.Perm W :=
    ⟨f g,f g⁻¹,fun w => (mul _ _ w).trans (by rw [inv_mul_cancel]; exact one w),
      fun w => (mul _ _ w).trans (by rw [mul_inv_cancel]; exact one w)⟩
  let hom : A →* Equiv.Perm W :=
    ⟨⟨perm,Equiv.ext one⟩,fun g h => Equiv.ext (fun w => (mul g h w).symm)⟩
  refine ⟨hom.range,two.of_surjective hom.rangeRestrict hom.rangeRestrict_surjective,?_,?_⟩
  · intro x y
    obtain ⟨a,rfl⟩ := onto x
    obtain ⟨b,rfl⟩ := onto y
    obtain ⟨g,hg⟩ := transitive a b
    exact ⟨hom.rangeRestrict g,(equiv g a).trans (congrArg q hg)⟩
  · rintro ⟨_,g,rfl⟩
    exact ⟨g,equiv g⟩

/-- In a square-free graph of minimum degree three a central free involution
of a transitive group gives a two-sheeted cover preserving the minimum degree. -/
theorem binary_quotient {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (degree : ∀ v, 3 ≤ G.degree v) (nosq : ¬cycleGraph 4 ⊑ G)
    (P : Subgroup (Equiv.Perm V)) [Nontrivial P] (two : IsPGroup 2 P)
    (transitive : ∀ x y, ∃ g : P, g.val x=y)
    (auto : ∀ (g : P) x y, G.Adj x y → G.Adj (g.val x) (g.val y)) :
    ∃ (W : Type) (_ : Fintype W) (B : SimpleGraph W) (_ : DecidableRel B.Adj)
      (D : Subgroup (Equiv.Perm W)), Fintype.card V=Fintype.card W*2 ∧
      (∀ w, 3 ≤ B.degree w) ∧ IsPGroup 2 D ∧ (∀ x y, ∃ d : D, d.val x=y) ∧
      (∀ (d : D) x y, B.Adj x y → B.Adj (d.val x) (d.val y)) ∧
      Fintype.card W ≠ 4 ∧
      ∀ n : ℕ, 3 ≤ n → cycleGraph n ⊑ B → cycleGraph n ⊑ G ∨ cycleGraph (2*n) ⊑ G := by
  classical
  obtain ⟨h,twice,free,commuting⟩ := central_pair P two transitive
  let t : V → V := h.val
  have sym (x y : V) : G.Adj x y → G.Adj (t x) (t y) := auto h x y
  obtain ⟨W,fw,q,onto,pair,card,fib⟩ := pair_projection t twice free
  let : Fintype W := fw
  have fixed (x : V) : q (t x)=q x := (pair _ _).mpr (Or.inr rfl)
  have noLoops (x : V) : ¬ G.Adj x (t x) := by
    intro loop
    have loops (y : V) : G.Adj y (t y) := by
      obtain ⟨g,rfl⟩ := transitive x y
      change G.Adj (g.val x) (h.val (g.val x))
      rw [←commuting g x]
      exact auto g x (t x) loop
    have other : ∃ y, G.Adj x y ∧ y≠t x := by
      by_contra! only
      have incl : G.neighborFinset x ⊆ {t x} := fun z hz =>
        Finset.mem_singleton.mpr (only z ((G.mem_neighborFinset _ _).mp hz))
      have bound := Finset.card_le_card incl
      rw [card_neighborFinset_eq_degree,Finset.card_singleton] at bound
      have := degree x
      omega
    obtain ⟨y,xy,neq⟩ := other
    have diff : x≠t y := fun eq => neq ((twice y).symm.trans (congrArg t eq.symm))
    exact nosq (square_of_four xy (loops y) (sym x y xy).symm loop.symm diff neq)
  have edgesDistinct {x y : V} (xy : G.Adj x y) : q x≠q y := by
    intro eq
    rcases (pair _ _).mp eq with rfl|rfl
    · exact xy.ne rfl
    · exact noLoops y xy.symm
  have neighborInj {x y z : V} (xy : G.Adj x y) (xz : G.Adj x z) (eq : q y=q z) : y=z := by
    rcases (pair _ _).mp eq with done|rfl
    · exact done
    · have across : G.Adj z (t x) := (show G.Adj (t x) z from (twice z) ▸ sym _ _ xy).symm
      exact (nosq (square_of_four xz across (sym _ _ xz) xy.symm (free x).symm (free z).symm)).elim
  let B := G.map q
  have lift (x : V) (w : W) (edge : B.Adj (q x) w) :
      ∃! y, G.Adj x y ∧ q y=w := by
    obtain ⟨_,a,b,ab,ha,hb⟩ := (map_adj' q G _ _).mp edge
    have existsLift : ∃ y, G.Adj x y ∧ q y=w := by
      rcases (pair _ _).mp ha with rfl|rfl
      · exact ⟨b,ab,hb⟩
      · exact ⟨t b,(twice x) ▸ sym _ _ ab,(fixed b).trans hb⟩
    obtain ⟨y,xy,hy⟩ := existsLift
    exact ⟨y,⟨xy,hy⟩,fun z hz => neighborInj hz.1 xy (hz.2.trans hy.symm)⟩
  have deg (w : W) : 3 ≤ B.degree w := by
    obtain ⟨v,rfl⟩ := onto w
    have nbr : B.neighborFinset (q v)=(G.neighborFinset v).image q := by
      ext y
      simp only [mem_neighborFinset,Finset.mem_image]
      constructor
      · intro adj
        exact (lift v y adj).exists
      · rintro ⟨u,vu,rfl⟩
        exact (map_adj' q G _ _).mpr ⟨edgesDistinct vu,v,u,vu,rfl,rfl⟩
    suffices inj : Set.InjOn q (G.neighborFinset v) by
      rw [←card_neighborFinset_eq_degree,nbr,Finset.card_image_of_injOn inj,card_neighborFinset_eq_degree]
      exact degree v
    exact fun _ hx _ hy eq => neighborInj ((mem_neighborFinset _ _ _).mp hx)
      ((mem_neighborFinset _ _ _).mp hy) eq
  have respects (g : P) (x y : V) (eq : q x=q y) : q (g.val x)=q (g.val y) := by
    apply (pair _ _).mpr
    rcases (pair _ _).mp eq with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr (commuting g y)
  obtain ⟨D,twoD,transD,desc⟩ := descend P two transitive q onto respects
  have autoD (d : D) (x y : W) (xy : B.Adj x y) : B.Adj (d.val x) (d.val y) := by
    obtain ⟨g,act⟩ := desc d
    obtain ⟨neq,a,b,ab,rfl,rfl⟩ := (map_adj' q G _ _).mp xy
    exact (map_adj' q G _ _).mpr ⟨fun eq => neq (d.val.injective eq),
      g.val a,g.val b,auto g _ _ ab,(act _).symm,(act _).symm⟩
  have notFour (size : Fintype.card W=4) : False := by
    have exactDeg (w : W) : B.degree w=3 := by
      have upper := B.degree_lt_card_verts w
      have lower := deg w
      omega
    exact nosq (square_over_four (G := G) (B := B) size exactDeg t twice sym q onto pair
      (fun x y e => (lift x y e).exists))
  refine ⟨W,fw,B,inferInstance,D,card,deg,twoD,transD,autoD,notFour,?_⟩
  rintro n large ⟨c⟩
  exact lift_two q onto (fun w => (fib w).le) large c lift


/-- At order 2^(m+3) a transitive 2-group guarantees a dyadic cycle on at
most half of the vertices, assuming only minimum degree three. -/
theorem short_of_two (m : ℕ) : ∀ (V : Type) [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj], Fintype.card V=2^(m+3) → (∀ v, 3 ≤ G.degree v) →
    ∀ P : Subgroup (Equiv.Perm V), IsPGroup 2 P → (∀ x y, ∃ g : P, g.val x=y) →
    (∀ (g : P) x y, G.Adj x y → G.Adj (g.val x) (g.val y)) →
    ∃ d : ℕ, 2 ≤ d ∧ 2^d ≤ 2^(m+2) ∧ cycleGraph (2^d) ⊑ G := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro V _ G _ order degree P two transitive auto
    have four : 4 ≤ 2^(m+2) := Nat.pow_le_pow_right (by decide : 0<2) (show 2 ≤ m+2 by omega)
    by_cases square : cycleGraph 4 ⊑ G
    · exact ⟨2,by decide,four,square⟩
    classical
    have large : 8 ≤ Fintype.card V := order ▸
      Nat.pow_le_pow_right (by decide : 0<2) (show 3 ≤ m+3 by omega)
    let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨x,y,distinct⟩ := exists_pair_ne V
    obtain ⟨g,move⟩ := transitive x y
    let : Nontrivial P := ⟨g,1,fun eq => distinct (by simpa [eq] using move)⟩
    obtain ⟨W,fw,B,db,D,cards,degreeB,twoD,transD,autoD,notFour,lifts⟩ :=
      binary_quotient degree square P two transitive auto
    let : Fintype W := fw
    let : DecidableRel B.Adj := db
    have next : Fintype.card W=2^(m+2) := by
      rw [order,show m+3=m+2+1 by omega,pow_succ] at cards
      omega
    cases m with
    | zero => exact (notFour next).elim
    | succ j =>
      obtain ⟨d,hd,small,cycle⟩ := ih j (by omega) W B next degreeB D twoD transD autoD
      have low : 4 ≤ 2^d := Nat.pow_le_pow_right (by decide : 0<2) hd
      have upper : 2^(j.succ+2)=2^(j+2)*2 := pow_succ 2 (j+2)
      rcases lifts _ (by omega) cycle with c|c
      · exact ⟨d,hd,by rw [upper]; omega,c⟩
      · refine ⟨d+1,by omega,by rw [upper,pow_succ]; omega,?_⟩
        rwa [pow_succ'] 

/-- Form the full permutation group of graph automorphisms and take a
transitive Sylow subgroup on a power-of-two number of vertices. -/
theorem short_of_transitive {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (degree : ∀ v, 3 ≤ G.degree v) (transitive : ∀ x y, ∃ g : G ≃g G, g x=y)
    {m : ℕ} (order : Fintype.card V=2^(m+3)) :
    ∃ d : ℕ, 2 ≤ d ∧ 2^d ≤ 2^(m+2) ∧ cycleGraph (2^d) ⊑ G := by
  classical
  let A : Subgroup (Equiv.Perm V) :=
    { carrier := {g | ∀ u v, G.Adj (g u) (g v) ↔ G.Adj u v}
      mul_mem' := fun hg hh u v => (hg _ _).trans (hh u v)
      one_mem' := fun _ _ => Iff.rfl
      inv_mem' := fun {g} hg u v => by simpa using (hg (g.symm u) (g.symm v)).symm }
  let : MulAction.IsPretransitive A V := ⟨fun u v => by
    obtain ⟨g,h⟩ := transitive u v
    exact ⟨⟨g.toEquiv,fun _ _ => g.map_rel_iff⟩,h⟩⟩
  let S : Sylow 2 A := Classical.choice inferInstance
  have strans := sylow_transitive (V := V) S (k := m+3) (by simpa [Nat.card_eq_fintype_card] using order)
  let P := S.1.map A.subtype
  have twoP : IsPGroup 2 P := S.2.map A.subtype
  have transP (u v : V) : ∃ g : P, g.val u=v := by
    obtain ⟨s,hs⟩ := strans.exists_smul_eq u v
    exact ⟨⟨s.val.val,s.val,s.property,rfl⟩,hs⟩
  apply short_of_two m V G order degree P twoP transP
  rintro ⟨_,g,_,rfl⟩ u v uv
  exact (g.property u v).mpr uv

/-- If a vertex-transitive graph of minimum degree three has order greater
than four and has any dyadic cycle, each vertex can be avoided by one. -/
theorem avoids_each_vertex {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (degree : ∀ v, 3 ≤ G.degree v) (transitive : ∀ x y, ∃ g : G ≃g G, g x=y)
    (big : 4 < Fintype.card V) (has : ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G)
    (r : V) : ∃ (k : ℕ) (c : (cycleGraph (2^k)).Copy G), 2 ≤ k ∧ r ∉ Set.range c := by
  obtain ⟨k,hk,w⟩ := has
  by_cases spanning : 2^k=Fintype.card V
  · have three : 3 ≤ k := by
      by_contra! small
      have : k=2 := by omega
      subst k
      omega
    obtain ⟨m,rfl⟩ : ∃ m, k=m+3 := ⟨k-3,by omega⟩
    obtain ⟨d,hd,small,cycle⟩ := short_of_transitive G degree transitive spanning.symm
    have proper : 2^d≠Fintype.card V := by
      rw [←spanning,show m+3=m+2+1 by omega,pow_succ]
      have positive : 0<2^(m+2) := Nat.two_pow_pos _
      omega
    obtain ⟨c,avoid⟩ := avoiding_cycle r (transitive r) proper cycle
    exact ⟨d,c,hd,avoid⟩
  · obtain ⟨c,avoid⟩ := avoiding_cycle r (transitive r) spanning w
    exact ⟨k,c,hk,avoid⟩

/-- In the rooted triangle-contraction branch, vertex transitivity is
impossible. At order four the unique degree-three graph is complete. -/
theorem rooted_obstruction_asymmetric {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (degree : ∀ v, 3 ≤ G.degree v) (r : V)
    (noneThrough : ∀ c : (cycleGraph 3).Copy G, r ∉ Set.range c)
    (has : ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ G)
    (hit : ∀ k : ℕ, 2 ≤ k → ∀ c : (cycleGraph (2^k)).Copy G, r ∈ Set.range c) :
    ¬∀ x y, ∃ g : G ≃g G, g x=y := by
  intro sym
  by_cases big : 4 < Fintype.card V
  · obtain ⟨k,c,hk,avoid⟩ := avoids_each_vertex G degree sym big has r
    exact avoid (hit k hk c)
  · have lower := degree r
    have upper := G.degree_lt_card_verts r
    have four : Fintype.card V=4 := by omega
    let e := (Fin.castSuccEmb : Fin 3 ↪ Fin 4).trans (Fintype.equivFinOfCardEq four).symm.toEmbedding
    have universal (u : V) : G.IsUniversal u := by
      apply (G.degree_eq_card_sub_one u).mp
      have := degree u
      have := G.degree_lt_card_verts u
      omega
    let c : (cycleGraph 3).Copy G :=
      ⟨⟨e,fun h => universal _ (fun eq => h.ne (e.injective eq))⟩,e.injective⟩
    obtain ⟨g,hg⟩ := sym (c 0) r
    exact noneThrough (g.toCopy.comp c) ⟨0,hg⟩

end HalfOrder

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R2.H2 := by
  intro small large V G _ _ r conn cubic bridges triangles witness forced
  classical
  by_contra unsolved
  have obstruction : ¬ ∃ (n k : ℕ) (c : (cycleGraph n).Copy G) (f : G ≃g G),
      3 ≤ n ∧ 2 ≤ k ∧ f r ∈ Set.range c ∧ (n+1=2^k ∨ n+2=2^k) := by
    rintro ⟨n,k,c,f,hn,hk,hit,h⟩
    obtain ⟨d,hd⟩ := backToRoot c f hit
    exact unsolved ⟨n,k,d,hn,hk,hd,h⟩
  have asym := HalfOrder.rooted_obstruction_asymmetric G (fun v => (cubic v).ge)
    r triangles witness forced
  have proper : ∃ v, ∀ f : G ≃g G, f r ≠ v := by
    by_contra! all
    apply asym
    intro x y
    obtain ⟨a,ha⟩ := all x
    obtain ⟨b,hb⟩ := all y
    exact ⟨a.symm.trans b,by change b (a.symm x)=y; rw [← ha,a.symm_apply_apply,hb]⟩
  have away (n : ℕ) (h : n=3 ∨ n=6) (c : (cycleGraph n).Copy G) (f : G ≃g G) :
      f r ∉ Set.range c := by
    intro hit
    obtain ⟨d,hd⟩ := backToRoot c f hit
    rcases h with rfl|rfl
    · exact triangles d hd
    · exact unsolved ⟨6,3,d,by decide,by decide,hd,Or.inr rfl⟩
  have images (k : ℕ) (hk : 2 ≤ k) (c : (cycleGraph (2^k)).Copy G) (f : G ≃g G) :
      f r ∈ Set.range c := HalfOrder.orbit_on_cycle r (forced k hk) c f
  have rule := thetaObstruction G r images obstruction
  by_cases few : {v | ∃ f : G ≃g G, f r=v}.ncard ≤ 2
  · exact obstruction (small V G r conn cubic bridges proper away witness images few rule)
  apply obstruction
  apply large V G r conn cubic bridges proper away witness images (by omega)
  · intro k hk c x y valid omits
    by_cases eq : x=y
    · subst y
      have big : 4≤2^k := Nat.pow_le_pow_right (by decide : 0<2) hk
      apply unsolved (omittedBlockSolves G r conn cubic proper (d := 1) hk
        (Or.inl rfl) (by omega) c x (images k hk c) ?_)
      intro j
      simpa using omits j
    · exact unsolved (twoOmissionsSolve G r cubic (valid.resolve_left eq)
        c x y eq (images k hk c) omits)
  · intro k hk c B size omits
    exact threeOmissionsSolve G r conn cubic proper images (away 6 (Or.inr rfl))
      hk c B size omits
  · intro O k hk c B size omits
    obtain ⟨v,hv⟩ := proper
    have cover (s : ℕ) (hs : 2 ≤ s) (w : (cycleGraph (2^s)).Copy G) : O ⊆ Set.range w := by
      rintro z ⟨g,rfl⟩
      exact images s hs w g
    obtain ⟨reg,count⟩ := fourOmissionData G r conn cubic O (fun _ => Iff.rfl)
      ⟨v,fun ⟨f,h⟩ => hv f h⟩ cover
      (fun n s w hn hs hit near => unsolved ⟨n,s,w,hn,hs,hit,near⟩) hk c B size omits
    refine ⟨fourOmissionBoundary G cubic O reg ?_ cover hk c B size omits,count⟩
    rintro w z ⟨g,rfl⟩
    exact away 3 (Or.inl rfl) w g
  · intro k d hk hd room c start interval s hs
    obtain ⟨w,g,h,hit,miss⟩ := omittedIntervalRing G r conn cubic proper hd room c start
      (images k hk c) interval
    constructor
    · intro eq
      revert w
      rw [eq]
      exact fun w _ no => no (images s hs w h)
    · constructor
      · intro eq
        exact obstruction ⟨d+2,s,w,g,by omega,hs,hit,Or.inl eq⟩
      · intro eq
        exact obstruction ⟨d+2,s,w,g,by omega,hs,hit,Or.inr eq⟩
  dsimp only
  intro x y A B P clean paths base
  obtain ⟨miss,both⟩ := rule x y A B P clean paths base
  constructor
  · intro near
    obtain ⟨inside,noOther⟩ := miss near
    have bound := orbitBoundOnList G r B inside
    exact ⟨inside,by omega,noOther⟩
  · intro a b
    have inside (f : G ≃g G) : f r ∈ [x,y] := by simpa using both a b f
    exact few (orbitBoundOnList G r [x,y] inside)

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R2_H2_R2
