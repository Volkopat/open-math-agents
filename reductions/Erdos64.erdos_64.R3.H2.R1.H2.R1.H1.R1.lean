import OMAReductions.R_Erdos64_erdos_64_R3_H2_R1_H2_R1

/-!
Remove the maximal degree-two ear containing the marked edge. Its length is two
or three, since every unmarked vertex has degree at least three. A triangle
through the mark closes immediately, as does a four-cycle. In the smaller graph
the terminals are the only possible degree defects. The cut condition for a
virtual edge between the terminals is expressed by testing banks containing both
terminals (the separating vertex can be assigned to either bank). A path between them closes
along the ear. Either the resulting length or its successor may be dyadic.
-/
-- Credit: @wispiANt. Builds on PRs #2529 and #5859.
namespace OMA.R_Erdos64_erdos_64_R3_H2_R1_H2_R1_H1_R1

open SimpleGraph
open scoped Classical
open OMA.R_Erdos64_erdos_64_R3_H2_R1 (degreeTwo_neighbours)

def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (x y : V),
    x ≠ y → ¬ G.Adj x y → (∀ t, G.Adj x t → ¬ G.Adj t y) → (∀ v, 2 ≤ G.degree v) → (∀ v, v ≠ x → v ≠ y → 3 ≤ G.degree v) →
    (∀ S : Finset V, S.Nonempty → ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ 2) →
    (∀ (z : V) (S : Set V), z ∈ S → x ∈ S → y ∈ S → (∃ u ∈ S, u ≠ z) →
      (∃ v, v ∉ S) → ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, G.Adj u v) →
    (∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k) ∨
      ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧
        (p.length + 2 = 2^k ∨ p.length + 3 = 2^k)

def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (x y : V),
    x ≠ y → ¬ G.Adj x y → (∀ v, 2 ≤ G.degree v) → (∀ v, v ≠ x → v ≠ y → 3 ≤ G.degree v) →
    (∀ S : Finset V, S.Nonempty → ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ 2) →
    (∀ (z : V) (S : Set V), z ∈ S → x ∈ S → y ∈ S → (∃ u ∈ S, u ≠ z) →
      (∃ v, v ∉ S) → ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, G.Adj u v) →
    (∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k) ∨
      ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧
        (p.length + 3 = 2^k ∨ p.length + 4 = 2^k)

/-- Specify the second neighbor relative to a prescribed incident edge. -/
theorem otherNeighbor {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {r b : V} (rb : G.Adj r b) (hr : G.degree r = 2) :
    ∃ x, x ≠ b ∧ G.Adj r x ∧ ∀ t, G.Adj r t → t = b ∨ t = x := by
  obtain ⟨u,v,uv,ru,rv,only⟩ := degreeTwo_neighbours G r hr
  have allN (t) (rt : G.Adj r t) : t = u.val ∨ t = v.val :=
    (only ⟨t, rt.ne.symm⟩ rt).imp (congrArg Subtype.val) (congrArg Subtype.val)
  have ne : u.val ≠ v.val := fun h => uv (Subtype.ext h)
  rcases allN b rb with h | h
  · subst b
    exact ⟨_,ne.symm,rv,allN⟩
  · subst b
    exact ⟨_,ne,ru,fun t ht => (allN t ht).symm⟩

private theorem restrictPeel {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Set V) [Fintype W]
    (peel : ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ 2)
    (S : Finset W) (hS : S.Nonempty) :
    ∃ v ∈ S, (S.filter ((G.induce W).Adj v)).card ≤ 2 := by
  classical
  let e := Function.Embedding.subtype W
  obtain ⟨v,hv,deg⟩ := peel (S.map e) hS.map
  obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hv
  refine ⟨w,hw,?_⟩
  rw [Finset.filter_map,Finset.card_map] at deg
  exact deg

private theorem restrictCuts {V : Type} (G : SimpleGraph V) (W : Set V) (x y : W)
    (boundary : ∀ t, t ∉ W → ∀ u : W, G.Adj t u → u = x ∨ u = y)
    (cuts : ∀ (z : V) (S : Set V), z ∈ S → (∃ u ∈ S, u ≠ z) → (∃ v, v ∉ S) →
      ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, G.Adj u v)
    (z : W) (S : Set W) (hz : z ∈ S) (hx : x ∈ S) (hy : y ∈ S)
    (hu : ∃ u ∈ S, u ≠ z) (hv : ∃ v, v ∉ S) :
    ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, (G.induce W).Adj u v := by
  classical
  let T : Set V := {v | ∀ h : v ∈ W, (⟨v,h⟩ : W) ∈ S}
  obtain ⟨u,us,uz⟩ := hu
  obtain ⟨v,vs⟩ := hv
  obtain ⟨a,ha,az,b,hb,ab⟩ := cuts z T (fun _ => hz)
    ⟨u,fun _ => us,fun h => uz (Subtype.ext h)⟩ ⟨v,fun h => vs (h v.property)⟩
  have bw : b ∈ W := by by_contra h; exact hb (fun h' => (h h').elim)
  let b' : W := ⟨b,bw⟩
  have bs : b' ∉ S := fun h => hb (fun _ => h)
  have aw : a ∈ W := by
    by_contra h
    rcases boundary a h b' ab with e | e
    · exact bs (e ▸ hx)
    · exact bs (e ▸ hy)
  exact ⟨⟨a,aw⟩,ha aw,fun h => az (congrArg Subtype.val h),b',bs,ab⟩

private theorem loseOne {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Set V) [DecidablePred (· ∈ W)] (v : W) (d : V)
    (only : ∀ t, G.Adj v t → t ∉ W → t = d) :
    G.degree v.val ≤ (G.induce W).degree v + 1 := by
  classical
  let f (n : G.neighborSet v.val) : Option ((G.induce W).neighborSet v) :=
    if h : n.val ∈ W then some ⟨⟨n.val,h⟩,n.property⟩ else none
  have inj : Function.Injective f := by
    intro n m eq
    apply Subtype.ext
    by_cases hn : n.val ∈ W <;> by_cases hm : m.val ∈ W
    · have e := Option.some.inj (by simpa only [f,dif_pos hn,dif_pos hm] using eq)
      exact congrArg (fun u : (G.induce W).neighborSet v => u.val.val) e
    · simp [f,hn,hm] at eq
    · simp [f,hn,hm] at eq
    · exact (only _ n.property hn).trans (only _ m.property hm).symm
  simpa only [Fintype.card_option,card_neighborSet_eq_degree] using Fintype.card_le_of_injective f inj

private theorem markedClose {V : Type} {G : SimpleGraph V} {r b x : V} (rb : G.Adj r b)
    (rx : G.Adj r x) (bx : b ≠ x) (p : G.Walk b x) (hp : p.IsPath) (hr : r ∉ p.support) :
    ∃ c : G.Walk r r, c.IsCycle ∧ c.length = p.length + 2 ∧ s(r,b) ∈ c.edges := by
  have pos : 0 < p.length := by
    by_contra! h
    exact bx ((Walk.length_eq_zero_iff.mp (by omega : p.length = 0)).eq)
  refine ⟨.cons rb (p.concat rx.symm),?_,by simp [Nat.add_assoc],by simp⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · rw [Walk.tail_cons]
    exact (Walk.isPath_copy _ _ _).mpr (hp.concat hr rx.symm)
  · simp only [Walk.length_cons,Walk.length_concat]
    omega

private theorem avoids {V : Type} {G : SimpleGraph V} {W : Set V} {u v : W}
    (p : (G.induce W).Walk u v) {z : V} (hz : z ∉ W) :
    z ∉ (p.map (Embedding.induce (G := G) W).toHom).support := by
  rw [Walk.support_map]
  rintro h
  obtain ⟨t,_,ht⟩ := List.mem_map.mp h
  exact hz (ht ▸ t.property)

private theorem oriented (two : H1) (three : H2) {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r b : V} (rb : G.Adj r b)
    (rd : G.degree r = 2) (floor : ∀ v, 2 ≤ G.degree v)
    (high : ∀ v, v ≠ r → v ≠ b → 3 ≤ G.degree v)
    (cuts : ∀ (z : V) (S : Set V), z ∈ S → (∃ u ∈ S, u ≠ z) → (∃ v, v ∉ S) →
      ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, G.Adj u v)
    (peel : ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ 2) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧
      (c.length = 2^k ∨ (c.length + 1 = 2^k ∧ s(r,b) ∈ c.edges)) := by
  classical
  obtain ⟨x,xb,rx,atR⟩ := otherNeighbor G rb rd
  let Goal := ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧
    (c.length = 2^k ∨ (c.length + 1 = 2^k ∧ s(r,b) ∈ c.edges))
  have finish (p : G.Walk b x) (hp : p.IsPath) (hr : r ∉ p.support) (k : ℕ) (hk : 2 ≤ k)
      (len : p.length + 2 = 2^k ∨ p.length + 3 = 2^k) : Goal := by
    obtain ⟨c,hc,hl,mark⟩ := markedClose rb rx xb.symm p hp hr
    exact ⟨k,r,c,hk,hc,len.elim (fun e => Or.inl (hl.trans e))
      (fun e => Or.inr ⟨by omega,mark⟩)⟩
  have survives {W : Set V} {u : W} {k : ℕ} (c : (G.induce W).Walk u u)
      (hk : 2 ≤ k) (hc : c.IsCycle) (hl : c.length = 2^k) : Goal :=
    ⟨k,u.val,c.map (Embedding.induce W).toHom,hk,hc.map Subtype.val_injective,
      Or.inl ((c.length_map _).trans hl)⟩
  by_cases bx : G.Adj b x
  · apply finish bx.toWalk bx.isPath_toWalk _ 2 (by decide) (Or.inr (by rfl))
    simp [Adj.toWalk,rb.ne,rx.ne]
  by_cases bd : G.degree b = 2
  · obtain ⟨y,yr,by',atB⟩ := otherNeighbor G rb.symm bd
    have yx : y ≠ x := fun e => bx (e ▸ by')
    by_cases link : G.Adj y x
    · let q : G.Walk b x := .cons by' link.toWalk
      have qp : q.IsPath := (Walk.cons_isPath_iff ..).mpr
        ⟨link.isPath_toWalk,by simp [Adj.toWalk,by'.ne,xb.symm]⟩
      exact finish q qp (by simp [q,Adj.toWalk,rb.ne,yr.symm,rx.ne]) 2
        (by decide) (Or.inl rfl)
    let W : Set V := {v | v ≠ r ∧ v ≠ b}
    let X : W := ⟨x,rx.ne.symm,xb⟩
    let Y : W := ⟨y,yr,by'.ne.symm⟩
    have boundary (t : V) (ht : t ∉ W) (u : W) (tu : G.Adj t u) : u = Y ∨ u = X := by
      change ¬ (_ ∧ _) at ht
      by_cases e : t = r
      · subst t
        rcases atR _ tu with h | h
        · exact (u.property.2 h).elim
        · exact Or.inr (Subtype.ext h)
      · have h : t = b := by by_contra n; exact ht ⟨e,n⟩
        subst t
        rcases atB _ tu with h | h
        · exact (u.property.1 h).elim
        · exact Or.inl (Subtype.ext h)
    have low (u : W) : 2 ≤ (G.induce W).degree u := by
      have h := high u u.property.1 u.property.2
      have loss := loseOne G W u (if u = X then r else b) (by
        intro t ut ht
        by_cases ur : u = X
        · rw [if_pos ur]
          by_contra tr
          have tb : t = b := by by_contra n; exact ht ⟨tr,n⟩
          exact bx (by simpa only [tb,ur] using ut.symm)
        · rw [if_neg ur]
          by_contra tb
          have tr : t = r := by by_contra n; exact ht ⟨n,tb⟩
          rcases atR _ (tr ▸ ut.symm) with e | e
          · exact u.property.2 e
          · exact ur (Subtype.ext e))
      omega
    have others (u : W) (uy : u ≠ Y) (ux : u ≠ X) : 3 ≤ (G.induce W).degree u := by
      rw [degree_induce_of_neighborSet_subset (show G.neighborSet u.val ⊆ W by
        intro t ut; by_contra ht
        exact (boundary t ht u (show G.Adj t u from (show G.Adj u t from ut).symm)).elim uy ux)]
      exact high u u.property.1 u.property.2
    rcases three W (G.induce W) Y X (fun h => yx (congrArg Subtype.val h)) link low others
        (restrictPeel G W peel) (restrictCuts G W Y X boundary cuts) with hc | hp
    · obtain ⟨_,_,c,hk,hc,hl⟩ := hc
      exact survives c hk hc hl
    · obtain ⟨k,p,hk,hp,hl⟩ := hp
      let q : G.Walk y x := p.map (Embedding.induce (G := G) W).toHom
      have qb : b ∉ q.support := avoids p (fun h => h.2 rfl)
      have qr : r ∉ q.support := avoids p (fun h => h.1 rfl)
      have ql : q.length = p.length := p.length_map _
      apply finish (.cons by' q) ((Walk.cons_isPath_iff ..).mpr ⟨hp.map Subtype.val_injective,qb⟩)
        (by simpa only [Walk.support_cons,List.mem_cons,not_or] using And.intro rb.ne qr) k hk
      simp only [Walk.length_cons]
      omega
  · let W : Set V := {v | v ≠ r}
    let B : W := ⟨b,rb.ne.symm⟩
    let X : W := ⟨x,rx.ne.symm⟩
    have boundary (t : V) (ht : t ∉ W) (u : W) (tu : G.Adj t u) : u = B ∨ u = X := by
      have e : t = r := by simpa [W] using ht
      exact (atR _ (e ▸ tu)).imp Subtype.ext Subtype.ext
    have low (u : W) : 2 ≤ (G.induce W).degree u := by
      have loss := loseOne G W u r (fun t _ ht => by simpa [W] using ht)
      by_cases ub : u.val = b
      · rw [ub] at loss
        have := floor b
        omega
      · have := high u u.property ub
        omega
    have others (u : W) (ub : u ≠ B) (ux : u ≠ X) : 3 ≤ (G.induce W).degree u := by
      rw [degree_induce_of_neighborSet_subset (show G.neighborSet u.val ⊆ W by
        intro t ut; by_contra ht
        exact (boundary t ht u (show G.Adj t u from (show G.Adj u t from ut).symm)).elim ub ux)]
      exact high u u.property (fun h => ub (Subtype.ext h))
    by_cases shared : ∃ t : W, (G.induce W).Adj B t ∧ (G.induce W).Adj t X
    · obtain ⟨t,bt,tx⟩ := shared
      have e : G.Adj b t := bt
      have f : G.Adj t x := tx
      let q : G.Walk b x := .cons e f.toWalk
      have qp : q.IsPath := (Walk.cons_isPath_iff ..).mpr
        ⟨f.isPath_toWalk,by simp [Adj.toWalk,e.ne,xb.symm]⟩
      exact finish q qp (by simp [q,Adj.toWalk,rb.ne,t.property.symm,rx.ne]) 2
        (by decide) (Or.inl rfl)
    have separated (t : W) (bt : (G.induce W).Adj B t) (tx : (G.induce W).Adj t X) : False :=
      shared ⟨t,bt,tx⟩
    rcases two W (G.induce W) B X (fun h => xb (congrArg Subtype.val h.symm)) bx separated low others
        (restrictPeel G W peel) (restrictCuts G W B X boundary cuts) with hc | hp
    · obtain ⟨_,_,c,hk,hc,hl⟩ := hc
      exact survives c hk hc hl
    · obtain ⟨k,p,hk,hp,hl⟩ := hp
      exact finish (p.map (Embedding.induce W).toHom) (hp.map Subtype.val_injective)
        (avoids p (by simp [W])) k hk ((congrArg (fun n : ℕ => n + 2 = 2^k ∨ n + 3 = 2^k)
          (p.length_map (Embedding.induce W).toHom)).mpr hl)

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R3_H2_R1_H2_R1.H1 := by
  intro two three V G _ _ a b ba floor high cuts peel
  classical
  obtain ⟨v,_,hv⟩ := peel Finset.univ ⟨a,Finset.mem_univ a⟩
  rw [← G.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree] at hv
  have lo := floor v
  have vd : G.degree v = 2 := by omega
  by_cases vb : v = b
  · subst v
    exact oriented two three G ba vd floor (fun u ub ua => high u ua ub) cuts peel
  · have va : v = a := by by_contra h; have := high v h vb; omega
    subst v
    simpa only [Sym2.eq_swap] using oriented two three G ba.symm vd floor high cuts peel

end OMA.R_Erdos64_erdos_64_R3_H2_R1_H2_R1_H1_R1
