import OMAReductions.R_Erdos64_erdos_64_R3
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! Pruning a block with a movable exceptional vertex. Degree and lifting
arguments adapt PR 466 by @JamesSlash; the cut-side induction adapts
PR 2088 by @Hennyrick. The bank lemma applies to the cuts in PR 21911.
Credit: @wispiANt. -/
namespace OMA.R_Erdos64_erdos_64_R3_H2_R2
open SimpleGraph

def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    Nonempty V → (∀ x, G.degree x = 3) →
    (∀ (a : V) (S : Set V), a ∈ S → (∃ x ∈ S, x ≠ a) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ ∃ y ∉ S, G.Adj x y) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (r : V),
    G.degree r = 2 → (∀ x, x ≠ r → 3 ≤ G.degree x) →
    (∀ (a : V) (S : Set V), a ∈ S → (∃ x ∈ S, x ≠ a) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ ∃ y ∉ S, G.Adj x y) →
    (∀ a b, G.Adj a b → G.degree a ≤ 3 ∨ G.degree b ≤ 3) →
    (∀ x, G.Adj r x → G.degree x = 3) →
    (∀ w, w ≠ r → ∃ x, G.Adj w x ∧ G.degree x = 3) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

theorem delete_edge_degree {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b : V)
    (x : V) (lower : 3 ≤ G.degree x) (room : x = a ∨ x = b → 3 < G.degree x) :
    3 ≤ (G.deleteEdges {s(a, b)}).degree x := by
  let H := G.deleteEdges {s(a, b)}
  change 3 ≤ H.degree x
  let removed : Finset V := if x = a then {b} else if x = b then {a} else ∅
  have inclusion : G.neighborFinset x ⊆ H.neighborFinset x ∪ removed := by
    intro y hy
    have adj := (G.mem_neighborFinset x y).mp hy
    apply Finset.mem_union.mpr
    by_cases h : s(x, y) = s(a, b)
    · right
      rcases (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (a, b))).mp h with hd | hd
      · have hx : x = a := congrArg Prod.fst hd
        have hyb : y = b := congrArg Prod.snd hd
        simp [removed, hx, hyb]
      · have hx : x = b := congrArg Prod.fst hd
        have hya : y = a := congrArg Prod.snd hd
        by_cases hab : a = b <;> simp [removed, hx, hya, hab, eq_comm]
    · left
      apply (H.mem_neighborFinset x y).mpr
      exact SimpleGraph.deleteEdges_adj.mpr ⟨adj, by simpa using h⟩
  have cardinal : G.degree x ≤ H.degree x + removed.card := by
    simpa only [card_neighborFinset_eq_degree] using
      (Finset.card_le_card inclusion).trans (Finset.card_union_le _ _)
  have loss : removed.card ≤ 1 := by
    dsimp [removed]
    split
    · simp
    · split <;> simp
  by_cases endpoints : x = a ∨ x = b
  · have larger := room endpoints
    omega
  · have noLoss : removed.card = 0 := by simp [removed, (not_or.mp endpoints).1,
      (not_or.mp endpoints).2]
    omega

theorem induce_edge_bound {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Set V) [DecidablePred (· ∈ S)] :
    (G.induce S).edgeFinset.card ≤ G.edgeFinset.card := by
  classical
  have mapped := SimpleGraph.map_edgeFinset_induce (s := S) (G := G)
  rw [← Finset.card_map (f := (Function.Embedding.subtype (· ∈ S)).sym2Map), mapped]
  exact Finset.card_le_card Finset.inter_subset_left

theorem puncture_degree {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : V) (x : {y : V // y ≠ r}) (lo : 3 ≤ G.degree x.val)
    (room : G.Adj x.val r → 3 < G.degree x.val) :
    3 ≤ (G.induce {y : V | y ≠ r}).degree x := by
  classical
  let S : Set V := {y | y ≠ r}
  let H := G.induce S
  change 3 ≤ H.degree x
  by_cases hx : G.Adj x.val r
  · have erased : (H.neighborFinset x).map (.subtype (· ∈ S)) =
        (G.neighborFinset x.val).erase r := by
      rw [SimpleGraph.map_neighborFinset_induce]
      ext y
      simp [S, and_comm]
    have cards := congrArg Finset.card erased
    rw [Finset.card_map, card_neighborFinset_eq_degree,
      Finset.card_erase_of_mem ((G.mem_neighborFinset x.val r).mpr hx),
      card_neighborFinset_eq_degree] at cards
    have := room hx
    omega
  · have unchanged : H.degree x = G.degree x.val :=
      SimpleGraph.degree_induce_of_neighborSet_subset (fun y hy eq => hx (eq ▸ hy))
    omega

theorem solve_rooted (solid : H1) (deficient : H2) (n : ℕ) :
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (r : V),
    Fintype.card V + G.edgeFinset.card = n → (∃ x : V, x ≠ r) →
    (∀ x, x ≠ r → 3 ≤ G.degree x) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V G finite dec r size nontrivial high
    classical
    have other (v : V) : ∃ x : V, x ≠ v := by
      obtain ⟨w, hw⟩ := nontrivial
      by_cases vr : v = r
      · exact ⟨w, vr ▸ hw⟩
      · exact ⟨r, Ne.symm vr⟩
    have erase (a b pivot : V) (ab : G.Adj a b)
        (degrees : ∀ x, x ≠ pivot → 3 ≤ G.degree x)
        (room : ∀ x, x ≠ pivot → x = a ∨ x = b → 3 < G.degree x) :
        ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
      let D := G.deleteEdges {s(a,b)}
      have erased : D.edgeFinset = G.edgeFinset.erase s(a,b) := by
        ext e
        simp [D, edgeSet_deleteEdges, and_comm]
      have strict : D.edgeFinset.card < G.edgeFinset.card := by
        rw [erased]
        exact Finset.card_erase_lt_of_mem (G.mem_edgeFinset.mpr ab)
      obtain ⟨k, v, c, hk, hc, hl⟩ := ih _ (by omega : Fintype.card V + D.edgeFinset.card < n)
        V D pivot rfl (other pivot)
        (fun x hx => delete_edge_degree G a b x (degrees x hx) (room x hx))
      let incl : D ≤ G := G.deleteEdges_le _
      exact ⟨k, v, c.mapLe incl, hk, hc.mapLe incl, by simpa using hl⟩
    have drop (w : V) (t : {x : V // x ≠ w}) (another : ∃ x, x ≠ t)
        (keep : ∀ x : {v : V // v ≠ w}, x ≠ t →
          3 ≤ G.degree x.val ∧ (G.Adj x.val w → 3 < G.degree x.val)) :
        ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
      let S : Set V := {v | v ≠ w}
      have smaller : Fintype.card S < Fintype.card V :=
        Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
          (b := w) (fun ⟨x, eq⟩ => x.property eq)
      have edges := induce_edge_bound G S
      obtain ⟨k,v,c,hk,hc,hl⟩ := ih _ (by omega : Fintype.card S + (G.induce S).edgeFinset.card < n)
        S (G.induce S) t rfl another (fun x xt =>
          puncture_degree G w x (keep x xt).1 (keep x xt).2)
      let incl : G.induce S →g G := ⟨Subtype.val, fun h => h⟩
      exact ⟨k, v.val, c.map incl, hk, hc.map Subtype.val_injective, by simpa using hl⟩
    by_cases heavy : ∃ a b, G.Adj a b ∧ 3 < G.degree a ∧ 3 < G.degree b
    · obtain ⟨a,b,ab,ha,hb⟩ := heavy
      exact erase a b r ab high (fun x _ e => e.elim (fun q => q ▸ ha) (fun q => q ▸ hb))
    have independent (a b : V) (ab : G.Adj a b) : G.degree a ≤ 3 ∨ G.degree b ≤ 3 := by
      by_contra! bad
      exact heavy ⟨a,b,ab,bad⟩
    by_cases block : (∀ (a : V) (S : Set V), a ∈ S → (∃ x ∈ S, x ≠ a) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ ∃ y ∉ S, G.Adj x y)
    · by_cases low : G.degree r < 3
      · by_cases pair : ∃ x y, x ≠ y ∧ G.Adj r x ∧ G.degree x = 3 ∧ G.Adj r y ∧ G.degree y = 3
        · obtain ⟨x,y,xy,rx,dx,ry,dy⟩ := pair
          have eq : G.neighborFinset r = {x,y} := by
            symm
            apply Finset.eq_of_subset_of_card_le
            · simp [Finset.insert_subset_iff, (G.mem_neighborFinset r x).mpr rx,
                (G.mem_neighborFinset r y).mpr ry]
            · rw [card_neighborFinset_eq_degree, Finset.card_pair xy]
              exact Nat.le_of_lt_succ low
          have degree : G.degree r = 2 := by rw [← card_neighborFinset_eq_degree, eq]; simp [xy]
          by_cases covered : ∀ w, w ≠ r → ∃ x, G.Adj w x ∧ G.degree x = 3
          · apply deficient V G r degree high block independent _ covered
            intro w rw'
            have member := (G.mem_neighborFinset r w).mpr rw'
            rw [eq] at member
            rcases Finset.mem_insert.mp member with h | h
            · exact h ▸ dx
            · have eqw := Finset.mem_singleton.mp h
              exact eqw ▸ dy
          · push Not at covered
            obtain ⟨w, wr, none⟩ := covered
            let S : Set V := {v | v ≠ w}
            let t : S := ⟨r, Ne.symm wr⟩
            have enough : 1 < (G.neighborFinset w).card := by
              rw [card_neighborFinset_eq_degree]
              exact (by decide : 1 < 3).trans_le (high w wr)
            obtain ⟨u, hu, ur⟩ := Finset.exists_mem_ne enough r
            have wu := (G.mem_neighborFinset w u).mp hu
            have other' : (⟨u, wu.ne.symm⟩ : S) ≠ t := fun h => ur (congrArg Subtype.val h)
            apply drop w t ⟨_, other'⟩
            intro v vt
            have lo := high v.val (fun e => vt (Subtype.ext e))
            refine ⟨lo, fun adj => ?_⟩
            have ne := none v.val adj.symm
            omega
        · let S : Set V := {v | v ≠ r}
          obtain ⟨w, wr⟩ := nontrivial
          have choose : ∃ t : S, ∀ x : S, G.Adj r x.val → G.degree x.val = 3 → x = t := by
            by_cases existsCubic : ∃ v, G.Adj r v ∧ G.degree v = 3
            · obtain ⟨t,rt,dt⟩ := existsCubic
              refine ⟨⟨t, rt.ne.symm⟩, ?_⟩
              intro x rx dx
              apply Subtype.ext
              exact Classical.byContradiction (fun ne => pair ⟨x.val,t,ne,rx,dx,rt,dt⟩)
            · exact ⟨⟨w,wr⟩, fun x rx dx => (existsCubic ⟨x.val,rx,dx⟩).elim⟩
          obtain ⟨t, unique⟩ := choose
          have many : 1 < (G.neighborFinset t.val).card := by
            rw [card_neighborFinset_eq_degree]
            exact (by decide : 1 < 3).trans_le (high t.val t.property)
          obtain ⟨v,hv,vr⟩ := Finset.exists_mem_ne many r
          have tv := (G.mem_neighborFinset t.val v).mp hv
          have different : (⟨v,vr⟩ : S) ≠ t := fun h => tv.ne.symm (congrArg Subtype.val h)
          apply drop r t ⟨_, different⟩
          intro x xt
          have lo := high x.val x.property
          refine ⟨lo, fun adj => ?_⟩
          have ne : G.degree x.val ≠ 3 := fun dx => xt (unique x adj.symm dx)
          omega
      · have allHigh (x : V) : 3 ≤ G.degree x := by
          by_cases eq : x = r
          · subst x
            omega
          · exact high x eq
        by_cases cubic : ∀ x, G.degree x = 3
        · exact solid V G ⟨r⟩ cubic block
        · obtain ⟨a, ha⟩ := not_forall.mp cubic
          have da : 3 < G.degree a := lt_of_le_of_ne (allHigh a) (Ne.symm ha)
          obtain ⟨b, ab⟩ := (G.degree_pos_iff_exists_adj a).mp (by omega)
          exact erase a b b ab (fun x _ => allHigh x) (by
            intro x xb h
            exact h.elim (fun e => e ▸ da) (fun e => (xb e).elim))
    push Not at block
    obtain ⟨a, S, ha, ⟨u, hu, hua⟩, ⟨v, hv⟩, separated⟩ := block
    have shrink (T : Set V) (atop : a ∈ T) (b : V) (hb : b ∈ T) (hba : b ≠ a)
        (miss : ∃ z : V, z ∉ T) (away : ∀ x ∈ T, x ≠ a → x ≠ r)
        (closedSide : ∀ x ∈ T, x ≠ a → G.neighborSet x ⊆ T) :
        ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
      let H := G.induce T
      let pivot : T := ⟨a, atop⟩
      obtain ⟨z, hz⟩ := miss
      have smaller : Fintype.card T < Fintype.card V :=
        Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
          (b := z) (fun ⟨x, eq⟩ => hz (eq ▸ x.property))
      have other : ∃ x : T, x ≠ pivot :=
        ⟨⟨b, hb⟩, fun h => hba (congrArg Subtype.val h)⟩
      have inherited (x : T) (hx : x ≠ pivot) : 3 ≤ H.degree x := by
        have ne : x.val ≠ a := fun h => hx (Subtype.ext h)
        change 3 ≤ (G.induce T).degree x
        rw [degree_induce_of_neighborSet_subset (closedSide x.val x.property ne)]
        exact high x.val (away x.val x.property ne)
      have edges : H.edgeFinset.card ≤ G.edgeFinset.card := induce_edge_bound G T
      obtain ⟨k, x, c, hk, hc, hl⟩ := ih _ (by omega : Fintype.card T + H.edgeFinset.card < n) T H pivot rfl other inherited
      let lift : H →g G := ⟨Subtype.val, fun h => h⟩
      exact ⟨k, x.val, c.map lift, hk, hc.map Subtype.val_injective, by simpa using hl⟩
    by_cases rootHere : r ∈ S
    · let T : Set V := {x | x = a ∨ x ∉ S}
      refine shrink T (Or.inl rfl) v (Or.inr hv) (fun eq => hv (eq ▸ ha)) ⟨u, ?_⟩ ?_ ?_
      · intro h
        exact h.elim hua (fun hn => hn hu)
      · intro x hx hxa hxr
        exact (hx.resolve_left hxa) (hxr ▸ rootHere)
      · intro x hx hxa y hxy
        by_cases hya : y = a
        · exact Or.inl hya
        · right
          intro hy
          exact separated y hy hya x (hx.resolve_left hxa) (G.adj_symm hxy)
    · apply shrink S ha u hu hua ⟨v, hv⟩
      · intro x hx _ hxr
        exact rootHere (hxr ▸ hx)
      · intro x hx hxa y hxy
        by_contra hy
        exact separated x hx hxa y hy hxy

/-- A cut side inherits the rooted obligation. Deleting the distinguished
edge loses at most one neighbor at either high-degree endpoint. -/
theorem cycle_in_bank (solid : H1) (deficient : H2) {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b z : V) (S : Set V)
    (floor : 3 ≤ G.minDegree) (ha : 3 < G.degree a) (hb : 3 < G.degree b)
    (hz : z ∈ S) (other : ∃ x ∈ S, x ≠ z)
    (cross : ∀ x ∈ S, x ≠ z → ∀ y ∉ S, G.Adj x y → s(x,y) = s(a,b)) :
    ∃ (k : ℕ) (v : S) (c : (G.induce S).Walk v v),
      2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  classical
  let D := G.deleteEdges {s(a,b)}
  let t : S := ⟨z,hz⟩
  obtain ⟨x, hx, xz⟩ := other
  have nontrivial : (⟨x,hx⟩ : S) ≠ t := fun eq => xz (congrArg Subtype.val eq)
  have high (v : S) (vt : v ≠ t) : 3 ≤ (D.induce S).degree v := by
    have vz : v.val ≠ z := fun eq => vt (Subtype.ext eq)
    have closedSide : D.neighborSet v.val ⊆ S := by
      intro y adj
      by_contra outside
      obtain ⟨edge, kept⟩ := SimpleGraph.deleteEdges_adj.mp adj
      exact kept (Set.mem_singleton_iff.mpr (cross v.val v.property vz y outside edge))
    rw [degree_induce_of_neighborSet_subset closedSide]
    exact delete_edge_degree G a b v.val (floor.trans (G.minDegree_le_degree _))
      (fun e => e.elim (fun q => q ▸ ha) (fun q => q ▸ hb))
  obtain ⟨k,v,c,hk,hc,len⟩ := solve_rooted solid deficient _ S (D.induce S) t rfl ⟨_,nontrivial⟩ high
  have incl : D.induce S ≤ G.induce S := fun _ _ adj => (G.deleteEdges_le _) adj
  exact ⟨k,v,c.mapLe incl,hk,hc.mapLe incl,by simpa using len⟩

/-- With both terminal hypotheses, the cut from PR 21911 gives a dyadic
cycle on each bank. Their vertex sets can intersect only at the cut vertex. -/
theorem cycles_on_both_banks (solid : H1) (deficient : H2) {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b z : V) (S : Set V)
    (floor : 3 ≤ G.minDegree) (ha : 3 < G.degree a) (hb : 3 < G.degree b)
    (hz : z ∈ S) (inside : ∃ x ∈ S, x ≠ z) (outside : ∃ y, y ∉ S)
    (cross : ∀ x ∈ S, x ≠ z → ∀ y ∉ S, G.Adj x y → s(x,y) = s(a,b)) :
    (∃ (k : ℕ) (v : S) (c : (G.induce S).Walk v v),
      2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k) ∧
    (∃ (k : ℕ) (v : {v : V // v = z ∨ v ∉ S})
        (c : (G.induce {w : V | w = z ∨ w ∉ S}).Walk v v),
      2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k) := by
  classical
  refine ⟨cycle_in_bank solid deficient G a b z S floor ha hb hz inside cross, ?_⟩
  obtain ⟨y, hy⟩ := outside
  apply cycle_in_bank solid deficient G a b z {w : V | w = z ∨ w ∉ S} floor ha hb (Or.inl rfl)
    ⟨y, Or.inr hy, fun e => hy (e ▸ hz)⟩
  intro u hu uz v hv adj
  have uout : u ∉ S := hu.resolve_left uz
  have vin : v ∈ S := Classical.byContradiction (fun no => hv (Or.inr no))
  have vz : v ≠ z := fun e => hv (Or.inl e)
  exact Sym2.eq_swap.trans (cross v vin vz u uout adj.symm)

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R3.H2 := by
  intro solid deficient V G finite dec r degree high _
  obtain ⟨w, rw'⟩ := (G.degree_pos_iff_exists_adj r).mp (by omega)
  exact solve_rooted solid deficient _ V G r rfl ⟨w,rw'.ne.symm⟩ high

end OMA.R_Erdos64_erdos_64_R3_H2_R2
