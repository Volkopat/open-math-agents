import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1

/-!
Delete the root, or its whole triangle if its two neighbors are adjacent.
The remaining network has two degree-two terminals and cubic interior. It is
connected, and each cut keeping both terminals on one side has at least two
crossing edges. In the triangle case two different routes close a terminal
path, giving consecutive possible lengths.
Credit: @wispiANt. Builds on PR #592 and the degree-two construction in #2529.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H2_R1
open SimpleGraph
open scoped Classical

def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (x y : V),
    x ≠ y → ¬ G.Adj x y → G.degree x = 2 → G.degree y = 2 →
    (∀ v, v ≠ x → v ≠ y → G.degree v = 3) →
    (∀ (S : Set V), S.Nonempty → Sᶜ.Nonempty → ∀ a b : V,
      ∃ u ∈ S, ∃ v ∉ S, G.Adj u v ∧ ((x ∈ S ↔ y ∈ S) → s(u,v) ≠ s(a,b))) →
    (∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k) ∨
      ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ p.length + 2 = 2^k

def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (x y : V),
    x ≠ y → ¬ G.Adj x y → G.degree x = 2 → G.degree y = 2 →
    (∀ v, v ≠ x → v ≠ y → G.degree v = 3) →
    (∀ (S : Set V), S.Nonempty → Sᶜ.Nonempty → ∀ a b : V,
      ∃ u ∈ S, ∃ v ∉ S, G.Adj u v ∧ ((x ∈ S ↔ y ∈ S) → s(u,v) ≠ s(a,b))) →
    (∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k) ∨
      ∃ (k : ℕ) (p : G.Walk x y), 2 ≤ k ∧ p.IsPath ∧ (p.length + 3 = 2^k ∨ p.length + 4 = 2^k)

theorem crossWalk {V : Type} {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
    (S : Set V) (ha : a ∈ S) (hb : b ∉ S) : ∃ u ∈ S, ∃ v ∉ S, G.Adj u v := by
  induction p with
  | nil => exact (hb ha).elim
  | @cons u v w uv p ih =>
    by_cases hv : v ∈ S
    · exact ih hv hb
    · exact ⟨u,ha,v,hv,uv⟩

private theorem crossing {V : Type} (G : SimpleGraph V) (conn : G.Connected)
    (safe : ∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a,b))
    (T : Set V) (hi : T.Nonempty) (ho : Tᶜ.Nonempty) (a b : V) :
    ∃ u ∈ T, ∃ v ∉ T, G.Adj u v ∧ s(u,v) ≠ s(a,b) := by
  classical
  obtain ⟨i,hi⟩ := hi
  obtain ⟨o,ho⟩ := ho
  by_cases adj : G.Adj a b
  · obtain ⟨p⟩ := (conn.connected_delete_edge_of_not_isBridge (safe adj)).preconnected i o
    obtain ⟨u,hu,v,hv,e⟩ := crossWalk p T hi ho
    obtain ⟨uv,diff⟩ := deleteEdges_adj.mp e
    exact ⟨u,hu,v,hv,uv,diff⟩
  · obtain ⟨p⟩ := conn.preconnected i o
    obtain ⟨u,hu,v,hv,e⟩ := crossWalk p T hi ho
    exact ⟨u,hu,v,hv,e,fun h => adj (show s(a,b) ∈ G.edgeSet from h ▸ e)⟩

private theorem networkCuts {V : Type} (G : SimpleGraph V) (conn : G.Connected)
    (safe : ∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a,b))
    (W : Set V) (x y : W) (dx dy : V)
    (ports : ∀ u : W, ∀ v ∉ W, G.Adj u v → (u = x ∧ v = dx) ∨ (u = y ∧ v = dy))
    (S : Set W) (hi : S.Nonempty) (ho : Sᶜ.Nonempty) (a b : W) :
    ∃ u ∈ S, ∃ v ∉ S, (G.induce W).Adj u v ∧ ((x ∈ S ↔ y ∈ S) → s(u,v) ≠ s(a,b)) := by
  classical
  let T : Set V := {v | if h : v ∈ W then (⟨v,h⟩ : W) ∈ S else x ∈ S}
  have inside (u : W) : u.val ∈ T ↔ u ∈ S := by simp [T,u.property]
  have outside (v : V) (hv : v ∉ W) : v ∈ T ↔ x ∈ S := by simp [T,hv]
  obtain ⟨i,hi⟩ := hi
  obtain ⟨o,ho⟩ := ho
  let side := x ∈ S ↔ y ∈ S
  let l : V := if side then a else y
  let r : V := if side then b else dy
  obtain ⟨u,hu,v,hv,uv,diff⟩ := crossing G conn safe T ⟨i,(inside i).2 hi⟩
    ⟨o,fun h => ho ((inside o).1 h)⟩ l r
  have stay (w : W) (t : V) (ht : t ∉ W) (wt : G.Adj w t)
      (across : ¬ (w.val ∈ T ↔ t ∈ T)) (ne : s(w.val,t) ≠ s(l,r)) : False := by
    rw [inside, outside t ht] at across
    rcases ports w t ht wt with ⟨rfl,_⟩ | ⟨rfl,rfl⟩
    · exact across Iff.rfl
    · have ns : ¬ side := fun h => across (Iff.symm h)
      exact ne (by simp [l,r,ns])
  have uw : u ∈ W := by
    by_contra un
    by_cases vw : v ∈ W
    · exact stay ⟨v,vw⟩ u un uv.symm (fun h => hv (h.mpr hu)) (by rwa [Sym2.eq_swap])
    · exact hv ((outside v vw).2 ((outside u un).1 hu))
  have vw : v ∈ W := by
    by_contra vn
    exact stay ⟨u,uw⟩ v vn uv (fun h => hv (h.mp hu)) diff
  refine ⟨⟨u,uw⟩,(inside _).1 hu,⟨v,vw⟩,fun h => hv ((inside _).2 h),uv,?_⟩
  intro hs eq
  have e := congrArg (Sym2.map (Subtype.val : W → V)) eq
  exact diff (by simpa [l,r,show side from hs] using e)

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

private theorem exits {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {v r b : V} (vr : G.Adj v r) (vb : G.Adj v b) (rb : r ≠ b) (h : G.degree v = 3) :
    ∃ x, x ≠ r ∧ x ≠ b ∧ G.Adj v x ∧ ∀ t, G.Adj v t → t = r ∨ t = b ∨ t = x := by
  classical
  let N := G.neighborFinset v
  have nr : r ∈ N := by simpa [N] using vr
  have nb : b ∈ N.erase r := Finset.mem_erase.mpr ⟨rb.symm,by simpa [N] using vb⟩
  have card : ((N.erase r).erase b).card = 1 := by
    rw [Finset.card_erase_of_mem nb,Finset.card_erase_of_mem nr]
    simp [N,h]
  obtain ⟨x,hx⟩ := Finset.card_eq_one.mp card
  have spec (t : V) : (t ≠ b ∧ t ≠ r ∧ G.Adj v t) ↔ t = x := by
    simpa [N] using (show t ∈ (N.erase r).erase b ↔ t ∈ ({x} : Finset V) by rw [hx])
  obtain ⟨xb,xr,vx⟩ := (spec x).2 rfl
  exact ⟨x,xr,xb,vx,fun t ht => by
    by_cases tr : t = r
    · exact Or.inl tr
    by_cases tb : t = b
    · exact Or.inr (Or.inl tb)
    exact Or.inr (Or.inr ((spec t).1 ⟨tb,tr,ht⟩))⟩

private theorem closePath {V : Type} {G : SimpleGraph V} {r a b : V} (ha : G.Adj r a)
    (hb : G.Adj r b) (p : G.Walk a b) (hp : p.IsPath) (hr : r ∉ p.support)
    (hab : a ≠ b) :
    ∃ c : G.Walk r r, c.IsCycle ∧ c.length = p.length + 2 := by
  have hlen : 0 < p.length := by
    by_contra! h
    exact hab ((Walk.length_eq_zero_iff.mp (by omega : p.length = 0)).eq)
  refine ⟨.cons ha (p.concat hb.symm), ?_, by simp [Nat.add_assoc]⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · rw [Walk.tail_cons]
    exact (Walk.isPath_copy _ _ _).mpr (hp.concat hr hb.symm)
  · simp only [Walk.length_cons, Walk.length_concat]
    omega

private theorem avoids {V : Type} {G : SimpleGraph V} {W : Set V} {u v : W}
    (p : (G.induce W).Walk u v) {z : V} (hz : z ∉ W) :
    z ∉ (p.map (Embedding.induce (G := G) W).toHom).support := by
  rw [Walk.support_map]
  rintro h
  obtain ⟨t,_,ht⟩ := List.mem_map.mp h
  exact hz (ht ▸ t.property)

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

private theorem triangleLift {V : Type} {G : SimpleGraph V} {a b r x y : V}
    (ab : G.Adj a b) (ar : G.Adj a r) (br : G.Adj b r) (ax : G.Adj a x) (by' : G.Adj b y)
    (xb : x ≠ b) (xr : x ≠ r) (p : G.Walk x y) (hp : p.IsPath)
    (aFresh : a ∉ p.support) (bFresh : b ∉ p.support) (rFresh : r ∉ p.support)
    (k : ℕ) (hk : 2 ≤ k) (len : p.length + 3 = 2^k ∨ p.length + 4 = 2^k) :
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
  let q := p.concat by'.symm
  have qp : q.IsPath := hp.concat bFresh by'.symm
  have qa : a ∉ q.support := by simp [q,Walk.support_concat,aFresh,ab.ne]
  rcases len with h | h
  · obtain ⟨c,hc,hl⟩ := closePath ax ab q qp qa xb
    have l : q.length = p.length + 1 := p.length_concat _
    exact ⟨k,a,c,hk,hc,by omega⟩
  · have qr : r ∉ q.support := by simp [q,Walk.support_concat,rFresh,br.ne.symm]
    obtain ⟨c,hc,hl⟩ := closePath ax ar (q.concat br) (qp.concat qr br)
      (by simp [Walk.support_concat,qa,ar.ne]) xr
    have l : (q.concat br).length = p.length + 2 := by simp [q,Nat.add_assoc]
    exact ⟨k,a,c,hk,hc,by omega⟩

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1.H2 := by
  intro plain triangle V G _ _ conn r rd cub safe
  classical
  have card : (G.neighborFinset r).card = 2 := (G.card_neighborFinset_eq_degree r).trans rd
  obtain ⟨a,b,ab,eq⟩ := Finset.card_eq_two.mp card
  have atR (t : V) : G.Adj r t ↔ t = a ∨ t = b := by
    rw [← G.mem_neighborFinset,eq]
    simp
  have ra := (atR a).2 (Or.inl rfl)
  have rb := (atR b).2 (Or.inr rfl)
  have survives {W : Set V} {u : W} {k : ℕ} (c : (G.induce W).Walk u u)
      (hk : 2 ≤ k) (hc : c.IsCycle) (hl : c.length = 2^k) :
      ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k :=
    ⟨k,u.val,c.map (Embedding.induce W).toHom,hk,hc.map Subtype.val_injective,
      (c.length_map _).trans hl⟩
  by_cases edge : G.Adj a b
  · obtain ⟨x,xr,xb,ax,atA⟩ := exits G ra.symm edge rb.ne (cub a ra.ne.symm)
    obtain ⟨y,yr,ya,by',atB⟩ := exits G rb.symm edge.symm ra.ne (cub b rb.ne.symm)
    by_cases same : x = y
    · subst y
      exact triangleLift edge ra.symm rb.symm ax by' xb xr .nil Walk.IsPath.nil
        (by simp [ax.ne]) (by simp [xb.symm]) (by simp [xr.symm]) 2 (by decide) (Or.inr rfl)
    by_cases link : G.Adj x y
    · exact triangleLift edge ra.symm rb.symm ax by' xb xr link.toWalk link.isPath_toWalk
        (by simp [ax.ne,ya.symm]) (by simp [xb.symm,by'.ne])
        (by simp [xr.symm,yr.symm]) 2 (by decide) (Or.inl rfl)
    let W : Set V := {u | u ≠ r ∧ u ≠ a ∧ u ≠ b}
    let X : W := ⟨x,xr,ax.ne.symm,xb⟩
    let Y : W := ⟨y,yr,ya,by'.ne.symm⟩
    have ports (u : W) (v : V) (vo : v ∉ W) (uv : G.Adj u v) :
        (u = X ∧ v = a) ∨ (u = Y ∧ v = b) := by
      by_cases e : v = r
      · subst v
        exact ((atR u).1 uv.symm).elim (fun h => (u.property.2.1 h).elim)
          (fun h => (u.property.2.2 h).elim)
      by_cases f : v = a
      · subst v
        rcases atA u uv.symm with h | h | h
        · exact (u.property.1 h).elim
        · exact (u.property.2.2 h).elim
        · exact Or.inl ⟨Subtype.ext h,rfl⟩
      have g : v = b := by by_contra n; exact vo ⟨e,f,n⟩
      subst v
      rcases atB u uv.symm with h | h | h
      · exact (u.property.1 h).elim
      · exact (u.property.2.1 h).elim
      · exact Or.inr ⟨Subtype.ext h,rfl⟩
    have xy : X ≠ Y := fun e => same (congrArg Subtype.val e)
    obtain ⟨dx,dy,interior⟩ := networkDegrees G W X Y xy a b (fun h => h.2.1 rfl)
      (fun h => h.2.2 rfl) ax.symm by'.symm ports (fun u => cub u u.property.1)
    rcases triangle W (G.induce W) X Y xy link dx dy interior (networkCuts G conn safe W X Y a b ports)
        with cycle | path
    · obtain ⟨_,_,c,hk,hc,hl⟩ := cycle
      exact survives c hk hc hl
    · obtain ⟨k,p,hk,hp,hl⟩ := path
      let proj := (Embedding.induce (G := G) W).toHom
      exact triangleLift edge ra.symm rb.symm ax by' xb xr (p.map proj) (hp.map Subtype.val_injective)
        (avoids p (fun h => h.2.1 rfl)) (avoids p (fun h => h.2.2 rfl)) (avoids p (fun h => h.1 rfl))
        k hk ((congrArg (fun n : ℕ => n + 3 = 2^k ∨ n + 4 = 2^k) (p.length_map proj)).mpr hl)
  · let W : Set V := {u | u ≠ r}
    let A : W := ⟨a,ra.ne.symm⟩
    let B : W := ⟨b,rb.ne.symm⟩
    have ports (u : W) (v : V) (vo : v ∉ W) (uv : G.Adj u v) :
        (u = A ∧ v = r) ∨ (u = B ∧ v = r) := by
      have e : v = r := by simpa [W] using vo
      subst v
      exact ((atR u).1 uv.symm).imp (fun h => ⟨Subtype.ext h,rfl⟩) (fun h => ⟨Subtype.ext h,rfl⟩)
    have ne : A ≠ B := fun e => ab (congrArg Subtype.val e)
    obtain ⟨dx,dy,interior⟩ := networkDegrees G W A B ne r r (by simp [W]) (by simp [W])
      ra.symm rb.symm ports (fun u => cub u u.property)
    rcases plain W (G.induce W) A B ne edge dx dy interior (networkCuts G conn safe W A B r r ports)
        with cycle | path
    · obtain ⟨_,_,c,hk,hc,hl⟩ := cycle
      exact survives c hk hc hl
    · obtain ⟨k,p,hk,hp,hl⟩ := path
      let proj := (Embedding.induce (G := G) W).toHom
      obtain ⟨c,hc,cl⟩ := closePath ra rb (p.map proj) (hp.map Subtype.val_injective)
        (avoids p (by simp [W])) ab
      exact ⟨k,r,c,hk,hc,cl.trans ((congrArg (· + 2) (p.length_map proj)).trans hl)⟩

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H2_R1
