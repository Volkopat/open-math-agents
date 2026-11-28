import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1
-- Written on the Wall II, Graph 189. Integration by @ali-hamdan-007.
-- R2 by @carl2sheriff, with R1 path and metric arguments by
-- @computerfreak97 (PR 2971) and philipsaint's Dirac formalization.
-- Sources and credits are in github.com/ali-hamdan-007/open-math-agents,
-- research/parallel-lean-results, research/graph189/full/direct/continuation.
section
open SimpleGraph
open scoped BigOperators
namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
lemma degree_pair [DecidableRel G.Adj] [Nontrivial V] (x y : V) (hne : x ≠ y) :
    secondSmallestDegree G ≤ G.degree x ∨ secondSmallestDegree G ≤ G.degree y := by
  classical
  let ds := degreeSequence G
  have hlen : 2 ≤ ds.length := by
    simpa [ds, degreeSequence] using Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))
  obtain ⟨a,b,l,heq⟩ : ∃ a b l, ds = a :: b :: l := by
    cases h : ds with
    | nil => simp [h] at hlen
    | cons a tail =>
      cases hh : tail with
      | nil => simp [h, hh] at hlen
      | cons b l => exact ⟨a,b,l,rfl⟩
  have hs : ds.Pairwise (· ≤ ·) := by simp [ds, degreeSequence]
  rw [heq] at hs
  have hlow : ∀ t ∈ l, b ≤ t := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1
  have hnil : l.filter (fun t => decide (t < b)) = [] := by
    simpa [List.filter_eq_nil_iff] using hlow
  have hct : (ds.filter (fun t => decide (t < b))).length ≤ 1 := by
    rw [heq]
    by_cases h : a < b <;> simp [h,hnil]
  have hcoeds : (↑ds : Multiset ℕ) = Finset.univ.val.map (fun v : V => G.degree v) := by
    simp [ds, degreeSequence]
  let low := Finset.univ.filter (fun v : V => G.degree v < b)
  have hl : low.card ≤ 1 := by
    change (Multiset.filter (fun t => G.degree t < b) Finset.univ.val).card ≤ 1
    have hct' : (Multiset.filter (fun t => t < b) (↑ds : Multiset ℕ)).card ≤ 1 := hct
    rw [hcoeds, Multiset.filter_map, Multiset.card_map] at hct'
    exact hct'
  have hb : secondSmallestDegree G = b := by
    change ds.getD 1 0 = b
    simp [heq]
  rw [hb]
  by_contra! h
  exact hne (Finset.card_le_one.mp hl x (by simpa [low] using h.1) y (by simpa [low] using h.2))
end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
end
section
namespace Graph189CutSides
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem connected_after_smaller_deletion (T : Finset V) (ht : T.card < G.vertexConnectivity) :
    (G.induce {u : V | u ∉ T}).Connected := by
  classical
  by_contra bad
  have hn := Fintype.one_lt_card (α := V)
  have bound : G.vertexConnectivity ≤ T.card := by
    unfold vertexConnectivity
    rw [if_neg (by omega : ¬ Fintype.card V ≤ 1)]
    exact Nat.sInf_le ⟨T,rfl,Or.inl bad⟩
  omega
end Graph189CutSides
end
section
namespace Graph189RootedPath
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {z u : V}
theorem exists_rooted_longest [Fintype V] (G : SimpleGraph V) (z : V) :
    ∃ (v : V) (P : G.Walk z v), P.IsPath ∧
      ∀ {b} (Q : G.Walk z b), Q.IsPath → Q.length ≤ P.length := by
  classical
  let Good (m : ℕ) := ∃ (v : V) (P : G.Walk z v), P.IsPath ∧ P.length = m
  have base : Good 0 := ⟨z,.nil,by simp,rfl⟩
  obtain ⟨v,P,hp,hlen⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  refine ⟨v,P,hp,?_⟩
  intro b Q hQ
  rw [hlen]
  have card := hQ.support_nodup.length_le_card
  have size := Q.length_support
  exact Nat.le_findGreatest (by omega) (show Good Q.length from ⟨b,Q,hQ,rfl⟩)
end Graph189RootedPath
end
section
namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
theorem degree_induce_filter {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (S : Set V) [Fintype S] [DecidablePred (· ∈ S)] (x : S) :
    (G.induce S).degree x = ((G.neighborFinset x.val).filter (fun v => v ∈ S)).card := by
  classical
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have same : ((G.induce S).neighborFinset x).map f =
      (G.neighborFinset x.val).filter (fun y => y ∈ S) := by
    ext y
    constructor
    · intro hy
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hy
      exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
        (((G.induce S).mem_neighborFinset _ _).mp hu),u.property⟩
    · intro hy
      obtain ⟨he,hs⟩ := mem_filter.mp hy
      exact mem_map.mpr ⟨⟨y,hs⟩,((G.induce S).mem_neighborFinset _ _).mpr
        ((G.mem_neighborFinset _ _).mp he),rfl⟩
  have card := congrArg Finset.card same
  rwa [card_map,(G.induce S).card_neighborFinset_eq_degree] at card
end Graph189ExteriorDegreeCycle
end
section
namespace Graph189
open SimpleGraph Finset
private theorem append_chain {V : Type*} {G : SimpleGraph V} {L R : List V}
    {a b : V} (hl : L.IsChain G.Adj) (hr : R.IsChain G.Adj)
    (ha : L.getLast? = some a) (hb : R.head? = some b) (h : G.Adj a b) :
    (L ++ R).IsChain G.Adj := by
  apply hl.append hr
  intro x hx y hy
  rw [ha] at hx
  rw [hb] at hy
  have hax : a = x := by simpa using hx
  have hby : b = y := by simpa using hy
  exact hax ▸ hby ▸ h
private theorem reverse_chain {V : Type*} {G : SimpleGraph V} {L : List V}
    (h : L.IsChain G.Adj) : L.reverse.IsChain G.Adj :=
  List.isChain_reverse.mpr (h.imp fun _ _ h => h.symm)
private theorem split_at_pair {V : Type*} (l : List V) (i : ℕ) (hi : i + 1 < l.length) :
    ∃ P Q, l = P ++ l[i]'(by omega) :: l[i + 1] :: Q := by
  refine ⟨l.take i, l.drop (i + 2), ?_⟩
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons (by omega : i < l.length), List.drop_eq_getElem_cons hi]
private theorem trace_of_list {V : Type*} [DecidableEq V] {G : SimpleGraph V} (l : List V)
    (hn : l.Nodup) (hc : l.IsChain G.Adj) (hall : ∀ z : V, z ∈ l) (hne : l ≠ []) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  let p := Walk.ofSupport l hne hc
  have hs : p.support = l := Walk.support_ofSupport hne hc
  exact ⟨_, _, p, (Walk.IsPath.mk' (by rwa [hs])).isHamiltonian_of_mem (fun z => by
    rw [hs]
    exact hall z)⟩
private theorem trace_of_permuted_chain {V : Type*} [DecidableEq V] {G : SimpleGraph V} {l W : List V}
    (hn : l.Nodup) (hall : ∀ z : V, z ∈ l) (h : W.Perm l) (hc : W.IsChain G.Adj)
    (x : V) : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hm (z : V) : z ∈ W := h.mem_iff.mpr (hall z)
  exact trace_of_list W (h.nodup_iff.mpr hn) hc hm (List.ne_nil_of_mem (hm x))
private theorem augmented_chain_excluding {V : Type*} {G : SimpleGraph V} {l : List V}
    {x y : V} (hc : l.IsChain (G ⊔ edge x y).Adj) (h : x ∉ l ∨ y ∉ l) :
    l.IsChain G.Adj := by
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro a b P Q he
  have ha : a ∈ l := by rw [he]; simp
  have hb : b ∈ l := by rw [he]; simp
  have hab := List.isChain_iff_forall_rel_of_append_cons_cons.mp hc he
  rcases hab with hab | hab
  · exact hab
  · have hr := (edge_adj x y a b).mp hab
    rcases hr.1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (h.elim (fun hn => hn ha) (fun hn => hn hb)).elim
    · exact (h.elim (fun hn => hn hb) (fun hn => hn ha)).elim
private theorem repair_left {V : Type*} {G : SimpleGraph V} {L R : List V}
    {x y u v : V} (hl : L.IsChain G.Adj) (hr : R.IsChain G.Adj)
    (hx : L.getLast? = some x) (hy : R.head? = some y)
    (hxu : G.Adj x u) (hyv : G.Adj y v)
    {P Q : List V} (hcut : L = P ++ u :: v :: Q) :
    ∃ W : List V, W.Perm (L ++ R) ∧ W.IsChain G.Adj := by
  let L₁ := P ++ [u]
  let L₂ := v :: Q
  have hl12 : L = L₁ ++ L₂ := by simpa [L₁,L₂,List.append_assoc] using hcut
  have hl₁ : L₁.IsChain G.Adj := (hl12 ▸ hl).left_of_append
  have hl₂ : L₂.IsChain G.Adj := (hl12 ▸ hl).right_of_append
  have hx₂ : L₂.getLast? = some x := by
    rw [hl12, List.getLast?_append_of_ne_nil _ (by simp [L₂])] at hx
    exact hx
  have hv₂ : L₂.head? = some v := by simp [L₂]
  have hrevH : L₂.reverse.head? = some x := by rwa [List.head?_reverse]
  have hrevL : L₂.reverse.getLast? = some v := by rwa [List.getLast?_reverse]
  have hlast : L₁.getLast? = some u := by simp [L₁]
  refine ⟨L₁ ++ (L₂.reverse ++ R), ?_, ?_⟩
  · apply (((List.reverse_perm L₂).append_right R).append_left L₁).trans
    exact List.Perm.of_eq ((List.append_assoc L₁ L₂ R).symm.trans
      (congrArg (· ++ R) hl12.symm))
  · have hjoin := append_chain (reverse_chain hl₂) hr hrevL hy hyv.symm
    apply append_chain hl₁ hjoin hlast _ hxu.symm
    simp [hrevH]
private theorem repair_right {V : Type*} {G : SimpleGraph V} {L R : List V}
    {x y u v : V} (hl : L.IsChain G.Adj) (hr : R.IsChain G.Adj)
    (hx : L.getLast? = some x) (hy : R.head? = some y)
    (hxu : G.Adj x u) (hyv : G.Adj y v)
    {P Q : List V} (hcut : R = P ++ u :: v :: Q) :
    ∃ W : List V, W.Perm (L ++ R) ∧ W.IsChain G.Adj := by
  have hy' : R.reverse.getLast? = some y := by rwa [List.getLast?_reverse]
  have hx' : L.reverse.head? = some x := by rwa [List.head?_reverse]
  have hcut' : R.reverse = Q.reverse ++ v :: u :: P.reverse := by
    rw [hcut]
    simp [List.reverse_append, List.reverse_cons, List.append_assoc]
  obtain ⟨W, hW, hc⟩ :=
    repair_left (reverse_chain hr) (reverse_chain hl) hy' hx' hyv hxu hcut'
  refine ⟨W, hW.trans ?_, hc⟩
  rw [← List.reverse_append]
  exact List.reverse_perm _
private theorem split_closure {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (hd : Fintype.card V ≤ G.degree x + G.degree y + 1)
    (P Q : List V) (hn : (P ++ x :: y :: Q).Nodup)
    (hc : (P ++ x :: y :: Q).IsChain (G ⊔ edge x y).Adj)
    (hall : ∀ z : V, z ∈ P ++ x :: y :: Q) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let L := P ++ [x]
  let R := y :: Q
  let l := L ++ R
  have hLRe : l = P ++ x :: y :: Q := by simp [l,L,R,List.append_assoc]
  rw [← hLRe] at hn hc hall
  have hno_x : x ∉ R := by
    intro h
    exact (List.nodup_append.mp hn).2.2 x (by simp [L]) x h rfl
  have hno_y : y ∉ L := by
    intro h
    exact (List.nodup_append.mp hn).2.2 y h y (by simp [R]) rfl
  have hl := augmented_chain_excluding (x := x) (y := y) hc.left_of_append (Or.inr hno_y)
  have hr := augmented_chain_excluding (x := x) (y := y) hc.right_of_append (Or.inl hno_x)
  have hx : L.getLast? = some x := by simp [L]
  have hy : R.head? = some y := by simp [R]
  have hLe : L ≠ [] := by simp [L]
  have hRe : R ≠ [] := by simp [R]
  let s := L.head hLe
  let t := R.getLast hRe
  have hs : L.head? = some s := List.head?_eq_some_head hLe
  have ht : R.getLast? = some t := List.getLast?_eq_some_getLast hRe
  have hst : l.head? = some s := by simp [l,hs]
  have htt : l.getLast? = some t := by simp [l,ht]
  by_cases hxt : G.Adj x t
  · apply trace_of_permuted_chain hn hall ((List.reverse_perm R).append_left L) _ x
    apply append_chain hl (reverse_chain hr) hx _ hxt
    rwa [List.head?_reverse]
  by_cases hys : G.Adj y s
  · apply trace_of_permuted_chain hn hall ((List.reverse_perm L).append_right R) _ x
    apply append_chain (reverse_chain hl) hr _ hy hys.symm
    rwa [List.getLast?_reverse]
  have hlen : l.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup hn]
    have he : l.toFinset = univ := by ext z; simp [hall]
    simp [he]
  let I := Fin (l.length - 1)
  let u (i : I) : V := l[i.val]'(by have := i.isLt; omega)
  let v (i : I) : V := l[i.val+1]'(by have := i.isLt; omega)
  let S : Finset I := univ.filter fun i => G.Adj x (u i)
  let T : Finset I := univ.filter fun i => G.Adj y (v i)
  have hS : G.degree x ≤ S.card := by
    have hsub : G.neighborFinset x ⊆ S.image u := by
      intro z hz
      have hzx := (mem_neighborFinset G x z).mp hz
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hall z)
      have hjlt : j < l.length - 1 := by
        by_contra! hh
        have hj' : j + 1 = l.length := by omega
        have hz : l[j] = t := by
          have hlne : l ≠ [] := List.ne_nil_of_mem (hall x)
          have hget : l.getLast hlne = t := List.getLast_of_getLast?_eq_some htt
          rw [List.getLast_eq_getElem] at hget
          have he : j = l.length - 1 := by omega
          exact he ▸ hget
        exact hxt (hz ▸ hzx)
      refine mem_image.mpr ⟨⟨j,hjlt⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      exact hzx
    exact (card_le_card hsub).trans card_image_le
  have hT : G.degree y ≤ T.card := by
    have hsub : G.neighborFinset y ⊆ T.image v := by
      intro z hz
      have hzy := (mem_neighborFinset G y z).mp hz
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hall z)
      have hj0 : 0 < j := by
        by_contra! hh
        have he : j = 0 := by omega
        have hlne : l ≠ [] := List.ne_nil_of_mem (hall x)
        have hget : l.head hlne = s := List.head_of_head?_eq_some hst
        rw [List.head_eq_getElem] at hget
        subst j
        exact hys (hget ▸ hzy)
      have hjlt : j - 1 < l.length - 1 := by omega
      let i : I := ⟨j - 1, hjlt⟩
      have hi : v i = l[j] := by
        change l[j - 1 + 1]'(by omega) = l[j]
        congr 1
        omega
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi.symm ▸ hzy⟩, hi⟩
    exact (card_le_card hsub).trans card_image_le
  have hpidx : P.length < l.length - 1 := by rw [hLRe]; simp
  let i₀ : I := ⟨P.length, hpidx⟩
  have hu₀ : u i₀ = x := by
    change (L ++ R)[P.length]'(by simp [L, R]) = x
    rw [List.getElem_append_left (by simp [L]), List.getElem_append_right le_rfl]
    simp
  have hv₀ : v i₀ = y := by
    change (L ++ R)[P.length + 1]'(by simp [L, R]) = y
    rw [List.getElem_append_right (by simp [L])]
    simp [L, R]
  have hout : i₀ ∉ S ∪ T := by
    simp [S,T,hu₀,hv₀]
  have hcap : (S ∪ T).card < l.length - 1 := by
    have hne : S ∪ T ≠ (univ : Finset I) := fun h => hout (h ▸ mem_univ _)
    have hh := card_lt_card (ssubset_univ_iff.mpr hne)
    simpa [I] using hh
  obtain ⟨i, hiS, hiT⟩ : ∃ i, i ∈ S ∧ i ∈ T := by
    by_contra! h
    have hdis : Disjoint S T := disjoint_left.mpr h
    have hcard := card_union_of_disjoint hdis
    omega
  have hxu : G.Adj x (u i) := (mem_filter.mp hiS).2
  have hyv : G.Adj y (v i) := (mem_filter.mp hiT).2
  have hin : i.val ≠ P.length := by
    intro h
    have hi0 : i = i₀ := Fin.ext h
    exact hout (mem_union_left _ (hi0 ▸ hiS))
  have hit := i.isLt
  have hLv : L.length = P.length + 1 := by simp [L]
  rcases lt_or_gt_of_ne hin with hbefore | hafter
  · have hixy : i.val + 1 < L.length := by omega
    obtain ⟨A,B,hAB⟩ := split_at_pair L i.val hixy
    have hu : u i = L[i.val]'(by omega) := List.getElem_append_left (by omega)
    have hv : v i = L[i.val+1] := List.getElem_append_left hixy
    rw [← hu, ← hv] at hAB
    obtain ⟨W, hw, hWc⟩ := repair_left hl hr hx hy hxu hyv hAB
    exact trace_of_permuted_chain hn hall hw hWc x
  · let j := i.val - L.length
    have hlen' : l.length = L.length + R.length := List.length_append
    have hj : j + 1 < R.length := by dsimp [j]; omega
    obtain ⟨A,B,hAB⟩ := split_at_pair R j hj
    have hu : u i = R[j]'(by omega) := List.getElem_append_right (by omega)
    have hv : v i = R[j+1] := by
      unfold v
      change (L ++ R)[i.val+1] = R[j+1]
      rw [List.getElem_append_right (by omega)]
      congr 1
      dsimp [j]
      omega
    rw [← hu, ← hv] at hAB
    obtain ⟨W, hw, hWc⟩ := repair_right hl hr hx hy hxu hyv hAB
    exact trace_of_permuted_chain hn hall hw hWc x
theorem traceable_of_sup_edge {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (_hne : x ≠ y) (_hxy : ¬ G.Adj x y)
    (hd : Fintype.card V ≤ G.degree x + G.degree y + 1)
    (hpath : ∃ a b : V, ∃ p : (G ⊔ edge x y).Walk a b, p.IsHamiltonian) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a,b,p,hp⟩ := hpath
  let l := p.support
  have hn := hp.isPath.support_nodup
  have hall := hp.mem_support
  have hc := p.isChain_adj_support
  by_cases hG : l.IsChain G.Adj
  · exact trace_of_list l hn hG hall p.support_ne_nil
  obtain ⟨i, hi, hbad⟩ := List.exists_not_getElem_of_not_isChain hG
  obtain ⟨P,Q,he⟩ := split_at_pair l i hi
  have hu : (G ⊔ edge x y).Adj l[i] l[i+1] :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp hc he
  rcases hu with h | h
  · exact (hbad h).elim
  have hh := (edge_adj x y _ _).mp h
  rcases hh.1 with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · rw [hx,hy] at he
    exact split_closure hd P Q (he ▸ hn) (he ▸ hc) (he ▸ hall)
  · rw [hx,hy] at he
    have hc' : l.IsChain (G ⊔ edge y x).Adj := by simpa only [edge_comm y x] using hc
    exact split_closure (by omega) P Q (he ▸ hn) (he ▸ hc') (he ▸ hall)
end Graph189
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y a b : V}
theorem gap_length_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (A J B : List V) (split : p.support = A ++ J ++ B)
    (q : G.Walk a b) (hq : q.IsPath) (disjoint : List.Disjoint q.support p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj b z) :
    q.support.length ≤ J.length := by
  classical
  let L := (A ++ q.support) ++ B
  have pnd := hp.support_nodup
  have pc := p.isChain_adj_support
  rw [split] at pnd pc disjoint
  have ca := pc.left_of_append.left_of_append
  have cb := pc.right_of_append
  have qsHead : q.support.head? = some a := by
    rw [List.head?_eq_some_head q.support_ne_nil, q.head_support]
  have qsLast : q.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast q.support_ne_nil, q.getLast_support]
  have first : (A++q.support).IsChain G.Adj := by
    apply ca.append q.isChain_adj_support
    intro z hz w hw
    rw [qsHead] at hw
    have same : a=w := by simpa using hw
    exact same ▸ left z hz
  have chain : L.IsChain G.Adj := by
    apply first.append cb
    intro z hz w hw
    have last : (A++q.support).getLast? = some b := by
      simp [List.getLast?_append,qsLast]
    rw [last] at hz
    have same : b=z := by simpa using hz
    exact same ▸ right w hw
  have nd : L.Nodup := by
    refine List.Nodup.append ?_ pnd.of_append_right ?_
    · apply List.Nodup.append pnd.of_append_left.of_append_left hq.support_nodup
      rw [List.disjoint_left]
      intro z hzA hzQ
      exact List.disjoint_left.mp disjoint hzQ (by simp [hzA])
    · rw [List.disjoint_left]
      intro z hz hzB
      rcases List.mem_append.mp hz with hzA | hzQ
      · exact List.disjoint_left.mp pnd.disjoint (by simp [hzA]) hzB
      · exact List.disjoint_left.mp disjoint hzQ (by simp [hzB])
  have hn : L≠[] := by simp [L,q.support_ne_nil]
  let r := Walk.ofSupport L hn chain
  have rs : r.support = L := Walk.support_ofSupport hn chain
  have rlen := longest r (Walk.IsPath.mk' (by rwa [rs]))
  have lhs := r.length_support
  have rhs := p.length_support
  rw [rs] at lhs
  rw [split] at rhs
  simp only [L,List.length_append] at lhs rhs
  omega
end Graph189ExteriorGap
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y a b : V}
theorem prefix_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (i : Fin p.support.length) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (contact : G.Adj b p.support[i.val]) : q.support.length ≤ i.val := by
  let L := p.support
  have head : (L.drop i.val).head? = some L[i.val] := by
    simp [List.head?_drop]
  have gap := gap_length_of_detour p hp longest [] (L.take i.val) (L.drop i.val)
    (by simp [L]) q hq disjoint (by simp) (by
      intro z hz
      rw [head] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact)
  have small := List.length_take_le i.val L
  omega
theorem suffix_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (i : Fin p.support.length) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (contact : G.Adj p.support[i.val] a) : i.val + 1 + q.support.length ≤ p.support.length := by
  let L := p.support
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have gap := gap_length_of_detour p hp longest (L.take (i.val+1)) (L.drop (i.val+1)) []
    (by simp [L]) q hq disjoint (by
      intro z hz
      rw [last] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact) (by simp)
  simp only [L,List.length_drop] at gap
  have hi := i.isLt
  omega
theorem interval_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (i j : Fin p.support.length) (hij : i < j) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (left : G.Adj p.support[i.val] a) (right : G.Adj b p.support[j.val]) :
    i.val+1+q.support.length ≤ j.val := by
  let L := p.support
  let gap := j.val-(i.val+1)
  have ij : i.val+1+gap=j.val := by
    change i.val < j.val at hij
    dsimp [gap]
    omega
  have split : L = L.take (i.val+1) ++ (L.drop (i.val+1)).take gap ++ L.drop j.val := by
    rw [←List.take_add,ij,List.take_append_drop]
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have head : (L.drop j.val).head? = some L[j.val] := by
    simp [List.head?_drop]
  have bound := gap_length_of_detour p hp longest _ _ _ split q hq disjoint (by
    intro z hz
    rw [last] at hz
    have eq : L[i.val] = z := by simpa using hz
    exact eq ▸ left) (by
    intro z hz
    rw [head] at hz
    have eq : L[j.val] = z := by simpa using hz
    exact eq ▸ right)
  have small := List.length_take_le gap (L.drop (i.val+1))
  omega
end Graph189ExteriorGap
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
theorem omitted_contact_internal (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i : Fin p.support.length) (contact : G.Adj p.support[i.val] a) :
    0 < i.val ∧ i.val + 1 < p.support.length := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  have h₁ := prefix_of_detour p hp longest i q hq hd contact.symm
  have h₂ := suffix_of_detour p hp longest i q hq hd contact
  simp only [q,Walk.support_nil,List.length_singleton] at h₁ h₂
  omega
theorem omitted_contact_spacing (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i j : Fin p.support.length) (ordered : i < j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] a) :
    i.val+2 ≤ j.val := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  exact interval_of_detour p hp longest i j ordered q hq hd first second.symm
theorem adjacent_omitted_contact_spacing (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    (i j : Fin p.support.length) (ordered : i < j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] b) :
    i.val+3 ≤ j.val := by
  let q : G.Walk a b := Walk.cons ab Walk.nil
  have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,ab.ne])
  have hd : List.Disjoint q.support p.support := by
    rw [List.disjoint_left]
    intro z hz h
    rcases (show z=a ∨ z=b by simpa [q] using hz) with rfl | rfl
    · exact ha h
    · exact hb h
  exact interval_of_detour p hp longest i j ordered q hq hd first second.symm
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
def crossIndices (A B : Finset ℕ) : Finset ℕ :=
  (A.image (fun i => i-1) ∪ (A∩B).image (fun i => i+1)) ∪ (B \ A)
private theorem card_crossIndices (A B : Finset ℕ) (positive : ∀ i∈A, 0 < i)
    (separated : ∀ i∈A, ∀ j∈B, i=j ∨ i+3 ≤ j ∨ j+3 ≤ i) :
    (crossIndices A B).card = A.card+B.card := by
  have dis₁ : Disjoint (A.image (fun i => i-1)) ((A∩B).image (fun i => i+1)) := by
    rw [Finset.disjoint_left]
    intro t ht hw
    obtain ⟨i,hi,ei⟩ := Finset.mem_image.mp ht
    obtain ⟨j,hj,ej⟩ := Finset.mem_image.mp hw
    have := positive i hi
    rcases separated i hi j (Finset.mem_inter.mp hj).2 with h | h | h <;> omega
  have dis₂ : Disjoint (A.image (fun i => i-1) ∪ (A∩B).image (fun i => i+1)) (B \ A) := by
    rw [Finset.disjoint_left]
    intro t ht hw
    have hb := (Finset.mem_sdiff.mp hw).1
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      have := positive i hi
      rcases separated i hi t hb with h | h | h <;> omega
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      rcases separated i (Finset.mem_inter.mp hi).1 t hb with h | h | h <;> omega
  have inj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj heq
    change i-1=j-1 at heq
    have := positive i hi
    have := positive j hj
    omega
  have cover : (B \ A) ∪ (A∩B) = B := by ext t; simp; tauto
  have dis : Disjoint (B \ A) (A∩B) := Finset.disjoint_left.mpr
    (fun _ h₁ h₂ => (Finset.mem_sdiff.mp h₁).2 (Finset.mem_inter.mp h₂).1)
  have hc := Finset.card_union_of_disjoint dis
  rw [cover] at hc
  rw [crossIndices,Finset.card_union_of_disjoint dis₂,Finset.card_union_of_disjoint dis₁,
    Finset.card_image_of_injOn inj,Finset.card_image_of_injective _
      (show Function.Injective (fun i : ℕ => i+1) by intro i j h; change i+1=j+1 at h; omega)]
  omega
noncomputable def contactPositions (p : G.Walk x y) (a : V) : Finset ℕ := by
  classical
  exact (Finset.range p.support.length).filter (fun i => G.Adj (p.getVert i) a)
theorem mem_contactPositions (p : G.Walk x y) (a : V) (i : ℕ) :
    i∈contactPositions p a ↔ i < p.support.length ∧ G.Adj (p.getVert i) a := by
  classical
  simp [contactPositions]
theorem get_at (p : G.Walk x y) {i : ℕ} (hi : i < p.support.length) :
    p.support[i] = p.getVert i := (p.getVert_eq_support_getElem (by
      have := p.length_support
      omega)).symm
theorem two_step_metric {a b z : V} (different : a≠b) (missing : ¬G.Adj a b)
    (az : G.Adj a z) (bz : G.Adj b z) : G.dist a b = 2 := by
  have h := SimpleGraph.edist_eq_two_iff.mpr ⟨different,missing,⟨z,az,bz⟩⟩
  simp [SimpleGraph.dist,h]
theorem cross_position_witnesses [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    let A := contactPositions p a
    let B := contactPositions p b
    (crossIndices A B).card=A.card+B.card ∧
    (∀ i∈crossIndices A B, i < p.support.length ∧ G.dist a (p.getVert i)=2) := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  have inside (i : ℕ) (h : i∈A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨hi,hc⟩ := (mem_contactPositions p a i).mp h
    exact omitted_contact_internal p hp longest ha ⟨i,hi⟩ (by simpa [get_at] using hc)
  have own (i j : ℕ) (hi : i∈A) (hj : j∈A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact omitted_contact_spacing p hp longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  have separate (i : ℕ) (hi : i∈A) (j : ℕ) (hj : j∈B) : i=j ∨ i+3 ≤ j ∨ j+3 ≤ i := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p b j).mp hj
    rcases lt_trichotomy i j with lt | same | gt
    · exact Or.inr (Or.inl (adjacent_omitted_contact_spacing p hp longest ha hb ab
        ⟨i,ri⟩ ⟨j,rj⟩ lt (by simpa [get_at] using ci) (by simpa [get_at] using cj)))
    · exact Or.inl same
    · exact Or.inr (Or.inr (adjacent_omitted_contact_spacing p hp longest hb ha ab.symm
        ⟨j,rj⟩ ⟨i,ri⟩ gt (by simpa [get_at] using cj) (by simpa [get_at] using ci)))
  have shell (i : ℕ) (hi : i∈crossIndices A B) : i < p.support.length ∧ G.dist a (p.getVert i)=2 := by
    have different (j : ℕ) : a≠p.getVert j := fun eq => ha (eq ▸ p.getVert_mem_support j)
    have ls := p.length_support
    have via (i j : ℕ) (hpi : i < p.support.length) (hj : j∈A) (no : i∉A)
        (ij : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i)=2 := by
      have hc := ((mem_contactPositions p a j).mp hj).2
      exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hpi,h.symm⟩)) hc.symm ij
    rcases Finset.mem_union.mp hi with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        obtain ⟨pos,back⟩ := inside j hj
        have inrange : j-1 < p.support.length := by omega
        refine ⟨inrange,via (j-1) j inrange hj (fun hi => ?_) ?_⟩
        · have aux := own (j-1) j hi hj (by omega)
          omega
        · have edge := p.adj_getVert_succ (i := j-1) (by omega)
          rwa [show j-1+1=j by omega] at edge
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        have jA := (Finset.mem_inter.mp hj).1
        obtain ⟨_,back⟩ := inside j jA
        refine ⟨back,via (j+1) j back jA (fun hi => ?_) ?_⟩
        · have aux := own j (j+1) jA hi (by omega)
          omega
        · exact (p.adj_getVert_succ (i := j) (by omega)).symm
    · obtain ⟨hB,hA⟩ := Finset.mem_sdiff.mp h
      obtain ⟨ri,ci⟩ := (mem_contactPositions p b i).mp hB
      exact ⟨ri,two_step_metric (different _) (fun h => hA ((mem_contactPositions p a i).mpr ⟨ri,h.symm⟩)) ab ci⟩
  exact ⟨card_crossIndices A B (fun i h => (inside i h).1) separate,shell⟩
theorem cross_positions_le_path_shell [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    (contactPositions p a).card + (contactPositions p b).card ≤
      (p.support.toFinset.filter (fun z => G.dist a z=2)).card := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  obtain ⟨count,shell⟩ := cross_position_witnesses p hp longest ha hb ab
  change (crossIndices A B).card=A.card+B.card at count
  have inj : Set.InjOn p.getVert ((crossIndices A B : Finset ℕ) : Set ℕ) := by
    intro i hi j hj same
    exact hp.getVert_injOn (by change i ≤ p.length; have := (shell i hi).1; have := p.length_support; omega)
      (by change j ≤ p.length; have := (shell j hj).1; have := p.length_support; omega) same
  have incl : (crossIndices A B).image p.getVert ⊆ p.support.toFinset.filter (fun z => G.dist a z=2) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support i),(shell i hi).2⟩
  have bound := Finset.card_le_card incl
  rw [Finset.card_image_of_injOn inj,count] at bound
  exact bound
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
theorem contact_card_neighbors (p : G.Walk x y) (hp : p.IsPath) (a : V) :
    (contactPositions p a).card = (G.neighborFinset a ∩ p.support.toFinset).card := by
  classical
  have inj : Set.InjOn p.getVert ((contactPositions p a : Finset ℕ) : Set ℕ) := by
    intro i hi j hj h
    have il := ((mem_contactPositions p a i).mp hi).1
    have jl := ((mem_contactPositions p a j).mp hj).1
    have ls := p.length_support
    exact hp.getVert_injOn (by change i ≤ p.length; omega) (by change j ≤ p.length; omega) h
  have eq : (contactPositions p a).image p.getVert = G.neighborFinset a ∩ p.support.toFinset := by
    ext z
    constructor
    · intro hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      have nb := ((mem_contactPositions p a i).mp hi).2.symm
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a _).mpr nb,List.mem_toFinset.mpr (p.getVert_mem_support i)⟩
    · intro hz
      obtain ⟨hadj,hm⟩ := Finset.mem_inter.mp hz
      have hza := ((G.mem_neighborFinset a z).mp hadj).symm
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hm)
      have eql : p.getVert i=z := (get_at p hi).symm.trans he
      exact Finset.mem_image.mpr ⟨i,(mem_contactPositions p a i).mpr ⟨hi,eql ▸ hza⟩,eql⟩
  rw [←eq,Finset.card_image_of_injOn inj]
theorem exterior_contact_degree (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+1+((G.neighborFinset b \ p.support.toFinset) ∩ G.neighborFinset a).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let D := B \ P
  let C := D ∩ A
  let X := (D.erase a) \ A
  let Q := P.filter (fun z => G.dist a z=2)
  have acol := cross_positions_le_path_shell p hp longest ha hb ab
  rw [contact_card_neighbors p hp a,contact_card_neighbors p hp b] at acol
  change (A∩P).card+(B∩P).card ≤ Q.card at acol
  have ain : a∈D := Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab.symm,
    fun h => ha (List.mem_toFinset.mp h)⟩
  have inter : (D.erase a) ∩ A = C := by
    ext z
    simp only [C,Finset.mem_inter,Finset.mem_erase]
    constructor
    · rintro ⟨⟨_,hd⟩,hA⟩
      exact ⟨hd,hA⟩
    · rintro ⟨hd,hA⟩
      exact ⟨⟨fun eq => G.irrefl (eq ▸ (G.mem_neighborFinset a z).mp hA),hd⟩,hA⟩
  have part₁ := Finset.card_sdiff_add_card_inter B P
  have part₂ := Finset.card_erase_add_one ain
  have part₃ := Finset.card_sdiff_add_card_inter (D.erase a) A
  rw [inter] at part₃
  change X.card+C.card=(D.erase a).card at part₃
  have shell (z : V) (hz : z∈X) : G.dist a z=2 := by
    obtain ⟨hD,hA⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨ne,hd⟩ := Finset.mem_erase.mp hD
    have hzB := (Finset.mem_sdiff.mp hd).1
    exact two_step_metric ne.symm (fun hadj => hA ((G.mem_neighborFinset a z).mpr hadj)) ab
      ((G.mem_neighborFinset b z).mp hzB).symm
  have dis : Disjoint Q X := Finset.disjoint_left.mpr (by
    intro z hQ hX
    have dm := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hX).1).2
    exact (Finset.mem_sdiff.mp dm).2 (Finset.mem_filter.mp hQ).1)
  have incl : Q ∪ X ⊆ Finset.univ.filter (fun z => G.dist a z=2) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hz with h | h
    · exact (Finset.mem_filter.mp h).2
    · exact shell z h
  have total := (Finset.card_le_card incl).trans quota
  rw [Finset.card_union_of_disjoint dis] at total
  change D.card+(B∩P).card=B.card at part₁
  change (A∩P).card+B.card ≤ k+1+C.card
  omega
theorem cross_contact_degree (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+(G.neighborFinset a \ p.support.toFinset).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let C := (B \ P) ∩ A
  have bound := exterior_contact_degree p hp longest ha hb ab quota
  change (A∩P).card+G.degree b ≤ k+1+C.card at bound
  have absent : b∉C := by
    intro h
    have nb := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).1).1
    exact G.irrefl ((G.mem_neighborFinset _ _).mp nb)
  have share : insert b C ⊆ A \ P := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | h
    · exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab,
        fun h => hb (List.mem_toFinset.mp h)⟩
    · obtain ⟨hD,hA⟩ := Finset.mem_inter.mp h
      exact Finset.mem_sdiff.mpr ⟨hA,(Finset.mem_sdiff.mp hD).2⟩
  have count := Finset.card_le_card share
  rw [Finset.card_insert_of_notMem absent] at count
  change (A∩P).card+G.degree b ≤ k+(A \ P).card
  omega
theorem half_degree_outside_longest (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree b) :
    G.degree a ≤ 2*(G.neighborFinset a \ p.support.toFinset).card := by
  have cross := cross_contact_degree p hp longest ha hb ab quota
  have parts := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  change (G.neighborFinset a).card ≤ 2*(G.neighborFinset a \ p.support.toFinset).card
  omega
end Graph189ExteriorGap
end
section
namespace Graph189ExteriorGap
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
theorem single_positions_lt_path_shell (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (ha : a ∉ p.support) (touch : (contactPositions p a).Nonempty) :
    (contactPositions p a).card + 1 ≤
      (p.support.toFinset.filter (fun v => G.dist a v = 2)).card := by
  classical
  let A := contactPositions p a
  let m := A.max' touch
  have hm : m ∈ A := Finset.max'_mem _ _
  have internal (i : ℕ) (hi : i ∈ A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    exact omitted_contact_internal p hp longest ha ⟨i,ri⟩ (by simpa [get_at] using ci)
  have spaced (i j : ℕ) (hi : i ∈ A) (hj : j ∈ A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact omitted_contact_spacing p hp longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  let B := A.image (fun i => i-1)
  let W := insert (m+1) B
  have different (i : ℕ) : a ≠ p.getVert i := fun eq => ha (eq ▸ p.getVert_mem_support i)
  have ls := p.length_support
  have via (i j : ℕ) (hi : i < p.support.length) (hj : j ∈ A) (no : i ∉ A)
      (edge : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i) = 2 := by
    have c := ((mem_contactPositions p a j).mp hj).2
    exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hi,h.symm⟩)) c.symm edge
  have valid (i : ℕ) (hi : i ∈ W) : i < p.support.length ∧ G.dist a (p.getVert i) = 2 := by
    rcases mem_insert.mp hi with rfl|h
    · have ht := (internal m hm).2
      refine ⟨ht,via _ m ht hm (fun mem => ?_) ((p.adj_getVert_succ (i:=m) (by omega)).symm)⟩
      have := spaced m (m+1) hm mem (by omega)
      omega
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      obtain ⟨positive,back⟩ := internal j hj
      have lim : j-1 < p.support.length := by omega
      refine ⟨lim,via _ j lim hj (fun mem => ?_) ?_⟩
      · have := spaced (j-1) j mem hj (by omega)
        omega
      · have edge := p.adj_getVert_succ (i:=j-1) (by omega)
        rwa [show j-1+1=j by omega] at edge
  have maxoutside : m+1 ∉ B := by
    intro h
    obtain ⟨i,hi,eq⟩ := mem_image.mp h
    have lim : i ≤ m := Finset.le_max' _ _ hi
    omega
  have predinj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj eq
    have := (internal i hi).1
    have := (internal j hj).1
    change i-1=j-1 at eq
    omega
  have nodeinj : Set.InjOn p.getVert (W : Set ℕ) := by
    intro i hi j hj eq
    exact hp.getVert_injOn (by change i ≤ p.length; have := (valid i hi).1; omega)
      (by change j ≤ p.length; have := (valid j hj).1; omega) eq
  have sub : W.image p.getVert ⊆ p.support.toFinset.filter (fun v => G.dist a v = 2) := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support _),(valid i hi).2⟩
  have count := card_le_card sub
  rw [card_image_of_injOn nodeinj,show W = insert (m+1) B from rfl,card_insert_of_notMem maxoutside,
    show B = A.image (fun i => i-1) from rfl,card_image_of_injOn predinj] at count
  exact count
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
theorem adjacent_ambient_degree_sum (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    G.degree a + G.degree b ≤ k+2*(G.neighborFinset a \ p.support.toFinset).card := by
  have cross := cross_contact_degree p hp longest ha hb ab quota
  have parts := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  change (G.neighborFinset a).card + G.degree b ≤ k+2*(G.neighborFinset a \ p.support.toFinset).card
  omega
theorem nonisolated_exterior_half (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (ha : a∉p.support) (nonisolated : (G.neighborFinset a \ p.support.toFinset).Nonempty)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree a) (minimum : ∀ v : V, 3 ≤ G.degree v)
    (uniqueLow : ∀ u v : V, G.degree u < k → G.degree v < k → u=v) :
    (∃ b : V, b∉p.support ∧ G.Adj a b ∧ k ≤ G.degree b) ∧
      G.degree a ≤ 2*(G.neighborFinset a \ p.support.toFinset).card := by
  let E := G.neighborFinset a \ p.support.toFinset
  have member (z : V) (hz : z∈E) : z∉p.support ∧ G.Adj a z :=
    ⟨fun h => (Finset.mem_sdiff.mp hz).2 (List.mem_toFinset.mpr h),
      (G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hz).1⟩
  obtain ⟨w,hw⟩ := nonisolated
  obtain ⟨hwo,aw⟩ := member w hw
  have sum := adjacent_ambient_degree_sum p hp longest ha hwo aw quota
  have card : 1 < E.card := by
    change G.degree a + G.degree w ≤ k + 2*E.card at sum
    have := minimum w
    omega
  obtain ⟨s,hs,t,ht,ne⟩ := Finset.one_lt_card.mp card
  have good : ∃ b∈E, k ≤ G.degree b := by
    by_cases highS : k ≤ G.degree s
    · exact ⟨s,hs,highS⟩
    · refine ⟨t,ht,?_⟩
      by_contra! lowT
      exact ne (uniqueLow s t (by omega) lowT)
  obtain ⟨b,hb,highB⟩ := good
  obtain ⟨off,adj⟩ := member b hb
  exact ⟨⟨b,off,adj,highB⟩,half_degree_outside_longest p hp longest ha off adj quota highB⟩
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
def ExteriorRoute (p : G.Walk x y) (a b : V) (k : ℕ) : Prop :=
  ∃ q : G.Walk a b, q.IsPath ∧ List.Disjoint q.support p.support ∧ k ≤ q.support.length
theorem longest_matched_route_order (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    {j middle left right : ℕ} (mark : Fin (j+1) ↪o Fin p.support.length)
    (port : Fin (j+1) → V) (contacts : ∀ i, G.Adj p.support[(mark i).val] (port i))
    (inner : ∀ i : Fin j, ExteriorRoute p (port i.castSucc) (port i.succ) middle)
    (before : ∃ a, ExteriorRoute p a (port 0) left)
    (after : ∃ b, ExteriorRoute p (port (Fin.last j)) b right) :
    left + j*(middle+1) + 1 + right ≤ p.support.length := by
  obtain ⟨a,q,hq,hdis,hlen⟩ := before
  have hfirst := prefix_of_detour p hp longest (mark 0) q hq hdis (contacts 0).symm
  obtain ⟨b,r,hr,hother,hend⟩ := after
  have hlast := suffix_of_detour p hp longest (mark (Fin.last j)) r hr hother (contacts _)
  have spread (i : Fin j) : (mark i.castSucc).val + 1 + middle ≤ (mark i.succ).val := by
    obtain ⟨t,ht,hd,hm⟩ := inner i
    have bound := interval_of_detour p hp longest _ _ (mark.strictMono i.castSucc_lt_succ)
      t ht hd (contacts _) (contacts _).symm
    omega
  have positions : ∀ i : Fin (j+1), left+i.val*(middle+1) ≤ (mark i).val := by
    intro i
    induction i using Fin.induction with
    | zero => simpa using hlen.trans hfirst
    | succ i ih =>
      have step := spread i
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.succ_mul] at ih ⊢
      omega
  have last := positions (Fin.last j)
  simp only [Fin.val_last] at last
  omega
theorem card_outside_add_path [Fintype V] [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (W : Finset V) (outside : ∀ z∈W, z∉p.support) :
    W.card+p.support.length ≤ Fintype.card V := by
  have dis : Disjoint W p.support.toFinset := Finset.disjoint_left.mpr (by
    intro z hz h
    exact outside z hz (List.mem_toFinset.mp h))
  have bound := (W ∪ p.support.toFinset).card_le_univ
  rw [Finset.card_union_of_disjoint dis,List.toFinset_card_of_nodup hp.support_nodup] at bound
  exact bound
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
theorem high_exterior_half (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (ha : a∉p.support) {k : ℕ}
    (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree a) (minimum : ∀ v : V, 3 ≤ G.degree v)
    (uniqueLow : ∀ u v : V, G.degree u < k → G.degree v < k → u=v) :
    (∃ b : V, b∉p.support ∧ G.Adj a b ∧ k ≤ G.degree b) ∧
      G.degree a ≤ 2*(G.neighborFinset a \ p.support.toFinset).card := by
  classical
  apply nonisolated_exterior_half p hp longest ha _ quota high minimum uniqueLow
  by_contra! empty
  have parts := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  rw [empty,Finset.card_empty,zero_add] at parts
  have num := contact_card_neighbors p hp a
  have min := minimum a
  change 3 ≤ (G.neighborFinset a).card at min
  have touch : (contactPositions p a).Nonempty := Finset.card_pos.mp (by omega)
  have shift := single_positions_lt_path_shell p hp longest ha touch
  have sub : p.support.toFinset.filter (fun z => G.dist a z=2) ⊆
      Finset.univ.filter (fun z => G.dist a z=2) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2⟩
  have size := (Finset.card_le_card sub).trans quota
  change k ≤ (G.neighborFinset a).card at high
  omega
end Graph189ExteriorGap
end
section
namespace Graph189ExteriorGap
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
theorem double_positions_le_path_shell (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (ha : a ∉ p.support) (wide : ∀ i∈contactPositions p a, ∀ j∈contactPositions p a, i < j → i+3 ≤ j) :
    2 * (contactPositions p a).card ≤
      (p.support.toFinset.filter (fun v => G.dist a v = 2)).card := by
  classical
  let A := contactPositions p a
  have internal (i : ℕ) (hi : i ∈ A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    exact omitted_contact_internal p hp longest ha ⟨i,ri⟩ (by simpa [get_at] using ci)
  have spaced (i j : ℕ) (hi : i ∈ A) (hj : j ∈ A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact omitted_contact_spacing p hp longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  let B := A.image (fun i => i-1)
  let F := A.image (fun i => i+1)
  let W := F ∪ B
  have different (i : ℕ) : a ≠ p.getVert i := fun eq => ha (eq ▸ p.getVert_mem_support i)
  have ls := p.length_support
  have via (i j : ℕ) (hi : i < p.support.length) (hj : j ∈ A) (no : i ∉ A)
      (edge : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i) = 2 := by
    have c := ((mem_contactPositions p a j).mp hj).2
    exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hi,h.symm⟩)) c.symm edge
  have valid (i : ℕ) (hi : i ∈ W) : i < p.support.length ∧ G.dist a (p.getVert i) = 2 := by
    rcases mem_union.mp hi with h|h
    · obtain ⟨m,hm,rfl⟩ := mem_image.mp h
      have ht := (internal m hm).2
      refine ⟨ht,via _ m ht hm (fun mem => ?_) ((p.adj_getVert_succ (i:=m) (by omega)).symm)⟩
      have := spaced m (m+1) hm mem (by omega)
      omega
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      obtain ⟨positive,back⟩ := internal j hj
      have lim : j-1 < p.support.length := by omega
      refine ⟨lim,via _ j lim hj (fun mem => ?_) ?_⟩
      · have := spaced (j-1) j mem hj (by omega)
        omega
      · have edge := p.adj_getVert_succ (i:=j-1) (by omega)
        rwa [show j-1+1=j by omega] at edge
  have disjoint : Disjoint F B := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨i,hi,ei⟩ := mem_image.mp hv
    obtain ⟨j,hj,ej⟩ := mem_image.mp hw
    have := (internal j hj).1
    change i+1=v at ei
    change j-1=v at ej
    have := wide i hi j hj (by omega)
    omega
  have predinj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj eq
    have := (internal i hi).1
    have := (internal j hj).1
    change i-1=j-1 at eq
    omega
  have nodeinj : Set.InjOn p.getVert (W : Set ℕ) := by
    intro i hi j hj eq
    exact hp.getVert_injOn (by change i ≤ p.length; have := (valid i hi).1; omega)
      (by change j ≤ p.length; have := (valid j hj).1; omega) eq
  have sub : W.image p.getVert ⊆ p.support.toFinset.filter (fun v => G.dist a v = 2) := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support _),(valid i hi).2⟩
  have count := card_le_card sub
  rw [card_image_of_injOn nodeinj,show W = F ∪ B from rfl,card_union_of_disjoint disjoint,
    show B = A.image (fun i => i-1) from rfl,card_image_of_injOn predinj,
    show F = A.image (fun i => i+1) from rfl,card_image_of_injective _ (show Function.Injective (fun i : ℕ => i+1) by
      intro i j eq; change i+1=j+1 at eq; omega)] at count
  change 2*A.card ≤ _
  omega
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
private theorem replace_position (p : G.Walk x y) (hp : p.IsPath) (A B : List V)
    (mid a : V) (split : p.support=A++mid::B) (outside : a∉p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj a z) :
    ∃ u v, ∃ q : G.Walk u v, q.IsPath ∧ q.length=p.length ∧
      q.support.toFinset=insert a (p.support.toFinset.erase mid) := by
  have nd := hp.support_nodup
  have chain := p.isChain_adj_support
  rw [split] at nd chain outside
  have ndA := nd.of_append_left
  have ndMB := nd.of_append_right
  have ndB := (List.nodup_cons.mp ndMB).2
  have midB := (List.nodup_cons.mp ndMB).1
  have midA : mid∉A := fun h => List.disjoint_left.mp nd.disjoint h (by simp)
  have aA : a∉A := fun h => outside (List.mem_append_left _ h)
  have aB : a∉B := fun h => outside (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  let L := A++a::B
  have fresh : L.Nodup := by
    refine List.Nodup.append ndA (List.nodup_cons.mpr ⟨aB,ndB⟩) ?_
    rw [List.disjoint_left]
    intro z hz hz'
    rcases List.mem_cons.mp hz' with rfl | inB
    · exact aA hz
    · exact List.disjoint_left.mp nd.disjoint hz (List.mem_cons_of_mem _ inB)
  have rightChain : (a::B).IsChain G.Adj := chain.right_of_append.of_cons.cons right
  have adjacent : L.IsChain G.Adj := by
    apply chain.left_of_append.append rightChain
    intro z hz w hw
    have same : a=w := by simpa using hw
    exact same ▸ left z hz
  have hn : L≠[] := by simp [L]
  let q := Walk.ofSupport L hn adjacent
  have qs : q.support=L := Walk.support_ofSupport hn adjacent
  refine ⟨_,_,q,Walk.IsPath.mk' (by rwa [qs]),?_,?_⟩
  · have ql := q.length_support
    have pl := p.length_support
    rw [qs] at ql
    rw [split] at pl
    simp only [L,List.length_append,List.length_cons] at ql pl
    omega
  · ext z
    simp only [qs,split,L,List.mem_toFinset,Finset.mem_insert,Finset.mem_erase,List.mem_append,List.mem_cons]
    by_cases eq : z=mid
    · subst z
      simp [midA,midB]
    · simp [eq]
      tauto
theorem swap_contact_midpoint (p : G.Walk x y) (hp : p.IsPath) {a : V} (outside : a∉p.support)
    (i : ℕ) (lastValid : i+2 < p.support.length)
    (left : G.Adj (p.getVert i) a) (right : G.Adj (p.getVert (i+2)) a) :
    ∃ u v, ∃ q : G.Walk u v, q.IsPath ∧ q.length=p.length ∧
      q.support.toFinset=insert a (p.support.toFinset.erase (p.getVert (i+1))) := by
  let L := p.support
  let A := L.take (i+1)
  let B := L.drop (i+2)
  have mid : i+1 < L.length := by dsimp [L]; omega
  have first : i < L.length := by dsimp [L]; omega
  have pl : L=A++L[i+1]::B := by
    change L=L.take (i+1)++L[i+1]::L.drop (i+2)
    rw [←List.drop_eq_getElem_cons mid,List.take_append_drop]
  have lastA : A.getLast?=some L[i] :=
    (congrArg List.getLast? (List.take_succ_eq_append_getElem first)).trans List.getLast?_concat
  have firstB : B.head?=some L[i+2] := by simp [B,List.head?_drop]
  have changed := replace_position p hp A B L[i+1] a pl outside (by
    intro z hz
    rw [lastA] at hz
    have eq : L[i]=z := by simpa using hz
    exact eq ▸ (by simpa [L,get_at] using left)) (by
    intro z hz
    rw [firstB] at hz
    have eq : L[i+2]=z := by simpa using hz
    exact eq ▸ (by simpa [L,get_at] using right.symm))
  simpa [L,get_at] using changed
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189TerminalLeafClosure
variable {V : Type*}
def terminalAdj (G : SimpleGraph V) (u v : V) : V ⊕ Bool → V ⊕ Bool → Prop
  | .inl a, .inl b => G.Adj a b
  | .inl a, .inr leaf => a = (if leaf then v else u)
  | .inr leaf, .inl a => a = (if leaf then v else u)
  | .inr _, .inr _ => False
def terminalLeaves (G : SimpleGraph V) (u v : V) : SimpleGraph (V ⊕ Bool) where
  Adj := terminalAdj G u v
  symm := by
    constructor
    intro a b h
    cases a <;> cases b
    · exact G.adj_symm h
    · exact h
    · exact h
    · exact h
  loopless := by
    constructor
    intro a
    cases a with
    | inl a => exact G.irrefl
    | inr l => exact id
instance terminalDecidable (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (u v : V) :
    DecidableRel (terminalLeaves G u v).Adj := by
  intro a b
  cases a <;> cases b <;> simp only [terminalLeaves,terminalAdj] <;> infer_instance
theorem core_degree_le [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v z : V) : G.degree z ≤ (terminalLeaves G u v).degree (.inl z) := by
  classical
  have inc : (G.neighborFinset z).image (Sum.inl : V → V ⊕ Bool) ⊆
      (terminalLeaves G u v).neighborFinset (.inl z) := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    simp only [SimpleGraph.mem_neighborFinset] at hc ⊢
    exact hc
  have h := Finset.card_le_card inc
  rw [Finset.card_image_of_injective _ (fun _ _ h => Sum.inl.inj h)] at h
  exact h
theorem terminalLeaves_sup_edge (G : SimpleGraph V) (u v a b : V) :
    terminalLeaves (G ⊔ edge a b) u v =
      terminalLeaves G u v ⊔ edge (.inl a) (.inl b) := by
  ext x y
  cases x <;> cases y <;> simp [terminalLeaves,terminalAdj,SimpleGraph.edge_adj]
theorem leaf_traceable_of_core_edge [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u v a b : V) (hne : a≠b) (hab : ¬G.Adj a b)
    (degree : Fintype.card V + 1 ≤ G.degree a + G.degree b)
    (path : ∃ x y, ∃ p : (terminalLeaves (G ⊔ edge a b) u v).Walk x y, p.IsHamiltonian) :
    ∃ x y, ∃ p : (terminalLeaves G u v).Walk x y, p.IsHamiltonian := by
  rw [terminalLeaves_sup_edge] at path
  apply Graph189.traceable_of_sup_edge (G := terminalLeaves G u v) (x := .inl a) (y := .inl b)
  · exact fun h => hne (Sum.inl.inj h)
  · exact hab
  · have ha := core_degree_le G u v a
    have hb := core_degree_le G u v b
    simp only [Fintype.card_sum, Fintype.card_bool]
    omega
  · exact path
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} {G : SimpleGraph V} {u v : V}
theorem neighbor_of_leaf {y : V ⊕ Bool} {l : Bool}
    (h : (terminalLeaves G u v).Adj y (.inr l)) :
    y = .inl (if l then v else u) := by
  cases y with
  | inl y => exact congrArg Sum.inl h
  | inr y => exact False.elim h
theorem leaf_not_interior {a b : V ⊕ Bool} (p : (terminalLeaves G u v).Walk a b)
    (hp : p.IsPath) {i : ℕ} (hpos : 0 < i) (hbefore : i < p.length)
    {l : Bool} (atLeaf : p.getVert i = .inr l) : False := by
  have hi : i-1+1=i := by omega
  have left := p.adj_getVert_succ (i := i-1) (by omega)
  rw [hi,atLeaf] at left
  have right := (p.adj_getVert_succ hbefore).symm
  rw [atLeaf] at right
  have same : p.getVert (i-1) = p.getVert (i+1) :=
    (neighbor_of_leaf left).trans (neighbor_of_leaf right).symm
  have bad : i-1=i+1 := hp.getVert_injOn
      (show i-1 ≤ p.length by omega) (show i+1 ≤ p.length by omega) same
  omega
theorem hamiltonian_leaf_at_end [DecidableEq V] {a b : V ⊕ Bool}
    (p : (terminalLeaves G u v).Walk a b) (hp : p.IsHamiltonian) (l : Bool) :
    a = .inr l ∨ b = .inr l := by
  obtain ⟨i,hi⟩ := hp.getVert_surjective (Sum.inr l)
  by_cases hz : i=0
  · left
    simpa [hz] using hi
  by_cases small : i < p.length
  · exact False.elim (leaf_not_interior p hp.isPath (i := i) (Nat.pos_of_ne_zero hz) small hi)
  · right
    rwa [p.getVert_of_length_le (by omega)] at hi
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
private theorem strip_oriented
    (p : (terminalLeaves G u v).Walk (.inr false) (.inr true)) (hp : p.IsHamiltonian) :
    ∃ q : G.Walk u v, q.IsHamiltonian := by
  have nonnil : ¬p.Nil := Walk.not_nil_of_ne (by simp)
  have first : p.snd = .inl u := neighbor_of_leaf (p.adj_snd nonnil).symm
  have qnn : ¬p.tail.Nil := Walk.not_nil_of_ne (by rw [first]; simp)
  have last : p.tail.penultimate = .inl v := neighbor_of_leaf (p.tail.adj_penultimate qnn)
  let t := p.tail.dropLast
  have parts : (.inr false) :: (t.support ++ [.inr true]) = p.support := by
    rw [show t.support ++ [.inr true] = p.tail.support from Walk.support_dropLast_concat qnn]
    exact Walk.cons_support_tail nonnil
  have nd := hp.isPath.support_nodup
  rw [←parts] at nd
  have ndf := List.nodup_cons.mp nd
  have core : ∀ z∈t.support, ∃ w : V, z = Sum.inl w := by
    intro z hz
    cases z with
    | inl w => exact ⟨w,rfl⟩
    | inr l =>
      cases l
      · exact (ndf.1 (List.mem_append_left _ hz)).elim
      · exact (List.disjoint_left.mp ndf.2.disjoint hz (by simp)).elim
  let project : V ⊕ Bool → V := Sum.elim id (fun l => if l then v else u)
  let L := t.support.map project
  have hn : L ≠ [] := by simp [L, t.support_ne_nil]
  have chain : L.IsChain G.Adj := by
    apply (List.isChain_map project).2
    apply t.isChain_adj_support.imp_of_mem_imp
    intro a b ha hb hab
    obtain ⟨i,rfl⟩ := core a ha
    obtain ⟨j,rfl⟩ := core b hb
    exact hab
  have nodup : L.Nodup := by
    apply List.Nodup.map_on _ ndf.2.of_append_left
    intro a ha b hb h
    obtain ⟨i,rfl⟩ := core a ha
    obtain ⟨j,rfl⟩ := core b hb
    exact congrArg Sum.inl h
  have all (w : V) : w ∈ L := by
    have hw := hp.mem_support (.inl w)
    rw [←parts] at hw
    have hmem : Sum.inl w ∈ t.support := by simpa using hw
    exact List.mem_map.mpr ⟨.inl w,hmem,rfl⟩
  let q := Walk.ofSupport L hn chain
  have qs : q.support = L := Walk.support_ofSupport hn chain
  have qh : q.IsHamiltonian := (Walk.IsPath.mk' (by rwa [qs])).isHamiltonian_of_mem
    (fun w => by rw [qs]; exact all w)
  have hstart : L.head hn = u := by
    simp [L,List.head_map,t,project,first]
  have hfinish : L.getLast hn = v := by
    simp [L,List.getLast_map,t,project,last]
  exact ⟨q.copy hstart hfinish, fun w => by simpa [Walk.support_copy] using qh w⟩
theorem prescribed_of_leaf_traceable
    (path : ∃ x y, ∃ p : (terminalLeaves G u v).Walk x y, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  obtain ⟨x,y,p,hp⟩ := path
  rcases hamiltonian_leaf_at_end p hp false with hx | hy
  · subst x
    rcases hamiltonian_leaf_at_end p hp true with hf | hy
    · simp at hf
    · subst y
      exact strip_oriented p hp
  · subst y
    rcases hamiltonian_leaf_at_end p hp true with hx | hf
    · subst x
      apply strip_oriented p.reverse
      intro w
      simpa using hp w
    · simp at hf
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
def oldEmbedding (G : SimpleGraph V) (u v : V) : G →g terminalLeaves G u v where
  toFun := Sum.inl
  map_rel' := fun h => h
theorem leaf_traceable_of_prescribed {p : G.Walk u v} (hp : p.IsHamiltonian) :
    ∃ x y, ∃ q : (terminalLeaves G u v).Walk x y, q.IsHamiltonian := by
  let h₁ : (terminalLeaves G u v).Adj (.inr false) (.inl u) := rfl
  let h₂ : (terminalLeaves G u v).Adj (.inl v) (.inr true) := rfl
  let q := Walk.cons h₁ ((p.map (oldEmbedding G u v)).concat h₂)
  have qs : q.support = Sum.inr false :: (p.support.map Sum.inl ++ [Sum.inr true]) := by
    simp [q,oldEmbedding]
    intro a ha
    rfl
  have mapped : (p.support.map (Sum.inl : V → V⊕Bool)).Nodup :=
    hp.isPath.support_nodup.map (fun _ _ h => Sum.inl.inj h)
  have nd : q.support.Nodup := by
    rw [qs]
    simp [List.nodup_append',mapped]
  refine ⟨_,_,q,(Walk.IsPath.mk' nd).isHamiltonian_of_mem ?_⟩
  intro w
  rw [qs]
  cases w with
  | inl z => simp [hp.mem_support z]
  | inr l => cases l <;> simp
theorem prescribed_of_sup_edge [Fintype V] [DecidableRel G.Adj] {a b : V}
    (distinct : a≠b) (missing : ¬G.Adj a b)
    (degree : Fintype.card V+1 ≤ G.degree a+G.degree b)
    (path : ∃ p : (G⊔edge a b).Walk u v, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  obtain ⟨p,hp⟩ := path
  exact prescribed_of_leaf_traceable (leaf_traceable_of_core_edge G u v a b distinct missing degree
    (leaf_traceable_of_prescribed hp))
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem prescribed_of_supergraph {G H : SimpleGraph V} [DecidableRel G.Adj] (incl : G ≤ H)
    (degree : ∀ a b, H.Adj a b → ¬G.Adj a b → Fintype.card V+1 ≤ G.degree a+G.degree b)
    {u v : V} (path : ∃ p : H.Walk u v, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  suffices all : ∀ J : SimpleGraph V, G ≤ J → J ≤ H → ∃ p : J.Walk u v, p.IsHamiltonian by
    exact all G le_rfl incl
  intro J
  induction J using WellFoundedGT.induction with
  | ind J ih =>
    intro lower upper
    by_cases eq : J=H
    · subst J
      exact path
    have missing : ∃ a b, H.Adj a b ∧ ¬J.Adj a b := by
      by_contra! all
      exact eq (le_antisymm upper fun a b hab => all a b hab)
    obtain ⟨a,b,hab,hnot⟩ := missing
    have hEdge : edge a b ≤ H := by
      intro i j hij
      obtain ⟨h,_⟩ := (edge_adj a b i j).mp hij
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hab
      · exact hab.symm
    have strict : J < J⊔edge a b := by
      apply lt_of_le_of_ne le_sup_left
      intro same
      have key : (J⊔edge a b).Adj a b := Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab.ne⟩)
      exact hnot (same.symm ▸ key)
    apply prescribed_of_sup_edge hab.ne hnot _ (ih _ strict (lower.trans le_sup_left) (sup_le upper hEdge))
    exact (degree _ _ hab (fun h => hnot (lower h))).trans
      (Nat.add_le_add (degree_le_of_le (v := a) lower) (degree_le_of_le (v := b) lower))
theorem complete_prescribed (u v : V) (hne : u ≠ v) :
    ∃ p : (⊤ : SimpleGraph V).Walk u v, p.IsHamiltonian := by
  classical
  let M := ((Finset.univ.erase u).erase v).toList
  let L := u :: (M ++ [v])
  have nd : L.Nodup := by
    simp [L,M,List.nodup_append',Finset.nodup_toList,hne]
  have chain : L.IsChain (⊤ : SimpleGraph V).Adj := by
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro x y A B eq
    apply (top_adj _ _).mpr
    intro same
    subst y
    rw [eq] at nd
    have tail := nd.of_append_right
    exact (List.nodup_cons.mp tail).1 (by simp)
  have hn : L ≠ [] := by simp [L]
  let p := Walk.ofSupport L hn chain
  have ps : p.support = L := Walk.support_ofSupport hn chain
  have ph : p.IsHamiltonian := (Walk.IsPath.mk' (by rwa [ps])).isHamiltonian_of_mem (by
    intro z
    rw [ps]
    by_cases hzu : z=u
    · simp [L,hzu]
    by_cases hzv : z=v <;> simp [L,M,hzu,hzv])
  have hs : L.head hn = u := by simp [L]
  have he : L.getLast hn = v := by simp [L]
  exact ⟨p.copy hs he, fun z => by simpa [Walk.support_copy] using ph z⟩
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y a b : V}
theorem splice_support (p : G.Walk x y) (hp : p.IsPath)
    (A J B : List V) (split : p.support = A ++ J ++ B)
    (q : G.Walk a b) (hq : q.IsPath) (disjoint : List.Disjoint q.support p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj b z) :
    ∃ u v, ∃ r : G.Walk u v, r.IsPath ∧ r.support = A ++ q.support ++ B := by
  classical
  let L := (A ++ q.support) ++ B
  have pnd := hp.support_nodup
  have pc := p.isChain_adj_support
  rw [split] at pnd pc disjoint
  have ca := pc.left_of_append.left_of_append
  have cb := pc.right_of_append
  have qsHead : q.support.head? = some a := by
    rw [List.head?_eq_some_head q.support_ne_nil, q.head_support]
  have qsLast : q.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast q.support_ne_nil, q.getLast_support]
  have first : (A++q.support).IsChain G.Adj := by
    apply ca.append q.isChain_adj_support
    intro z hz w hw
    rw [qsHead] at hw
    have same : a=w := by simpa using hw
    exact same ▸ left z hz
  have chain : L.IsChain G.Adj := by
    apply first.append cb
    intro z hz w hw
    have last : (A++q.support).getLast? = some b := by
      simp [List.getLast?_append,qsLast]
    rw [last] at hz
    have same : b=z := by simpa using hz
    exact same ▸ right w hw
  have nd : L.Nodup := by
    refine List.Nodup.append ?_ pnd.of_append_right ?_
    · apply List.Nodup.append pnd.of_append_left.of_append_left hq.support_nodup
      rw [List.disjoint_left]
      intro z hzA hzQ
      exact List.disjoint_left.mp disjoint hzQ (by simp [hzA])
    · rw [List.disjoint_left]
      intro z hz hzB
      rcases List.mem_append.mp hz with hzA | hzQ
      · exact List.disjoint_left.mp pnd.disjoint (by simp [hzA]) hzB
      · exact List.disjoint_left.mp disjoint hzQ (by simp [hzB])
  have hn : L≠[] := by simp [L,q.support_ne_nil]
  let r := Walk.ofSupport L hn chain
  have rs : r.support = L := Walk.support_ofSupport hn chain
  exact ⟨_,_,r,Walk.IsPath.mk' (by rwa [rs]),rs⟩
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}
omit [Fintype V] in
theorem route_of_induced_hamilton (p : G.Walk x y) (K : Finset V)
    (outside : ∀ z∈K, z∉p.support) {a b : K}
    {q : (G.induce (K : Set V)).Walk a b} (hq : q.IsHamiltonian) :
    ExteriorRoute p a.val b.val K.card := by
  let e := SimpleGraph.Embedding.induce (G := G) (K : Set V)
  let r := q.map e.toHom
  refine ⟨r, hq.isPath.map e.injective, ?_, ?_⟩
  · rw [List.disjoint_left]
    intro z hz hp
    change z∈(q.map e.toHom).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    exact outside w.val w.property hp
  · change K.card≤(q.map e.toHom).support.length
    rw [Walk.support_map,List.length_map,hq.length_support]
    simp
theorem exterior_hamilton_connected_matching (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (K : Finset V) (size : 1 < K.card) (outside : ∀ z∈K, z∉p.support)
    (hconn : ∀ a b : K, a≠b → ∃ q : (G.induce (K : Set V)).Walk a b, q.IsHamiltonian)
    (marks : Finset (Fin p.support.length)) (nonempty : marks.Nonempty)
    (attach : marks ↪ K) (contacts : ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val) :
    (marks.card+2)*K.card + marks.card ≤ Fintype.card V := by
  classical
  obtain ⟨j,hj⟩ : ∃ j : ℕ, marks.card=j+1 := ⟨marks.card-1, by
    have := Finset.card_pos.mpr nonempty
    omega⟩
  let iso := marks.orderIsoOfFin hj
  let M := marks.orderEmbOfFin hj
  let T := fun i : Fin (j+1) => attach (iso i)
  have touching (i : Fin (j+1)) : G.Adj p.support[(M i).val] (T i).val := contacts (iso i)
  have inj : Function.Injective T := attach.injective.comp iso.injective
  have route (a b : K) (ne : a≠b) : ExteriorRoute p a.val b.val K.card := by
    obtain ⟨q,hq⟩ := hconn a b ne
    exact route_of_induced_hamilton p K outside hq
  have another (w : K) : ∃ z : K, z≠w := by
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp size
    by_cases eq : a=w.val
    · exact ⟨⟨b,hb⟩,fun h => hab (eq.trans (congrArg Subtype.val h).symm)⟩
    · exact ⟨⟨a,ha⟩,fun h => eq (congrArg Subtype.val h)⟩
  have inner (i : Fin j) : ExteriorRoute p (T i.castSucc).val (T i.succ).val K.card :=
    route _ _ (inj.ne (ne_of_lt i.castSucc_lt_succ))
  obtain ⟨a,ha⟩ := another (T 0)
  obtain ⟨b,hb⟩ := another (T (Fin.last j))
  have bound := longest_matched_route_order p hp longest M (fun i => (T i).val) touching inner
    ⟨a.val,route _ _ ha⟩ ⟨b.val,route _ _ hb.symm⟩
  have total := card_outside_add_path p hp K outside
  rw [hj]
  simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul] at bound ⊢
  omega
end Graph189ExteriorGap
end
section
open Finset
namespace Graph189ExteriorGap
variable {L R : Type*} [Fintype L] [DecidableEq L] [DecidableEq R]
theorem hall_at_least (neighbors : L → Finset R) (s : ℕ) (small : s ≤ Fintype.card L)
    (hall : ∀ T : Finset L, T.card ≤ (T.biUnion neighbors).card + (Fintype.card L-s)) :
    ∃ U : Finset L, s ≤ U.card ∧ ∃ f : U ↪ R, ∀ u, f u ∈ neighbors u.val := by
  classical
  let d := Fintype.card L-s
  let choices := fun u : L => (neighbors u).disjSum (Finset.univ : Finset (Fin d))
  have full (T : Finset L) : T.card ≤ (T.biUnion choices).card := by
    by_cases empty : T=∅
    · simp [empty]
    obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have eq : T.biUnion choices = (T.biUnion neighbors).disjSum (Finset.univ : Finset (Fin d)) := by
      ext k
      cases k with
      | inl x => simp [choices]
      | inr y =>
        simp [choices]
        exact ⟨u,hu⟩
    rw [eq,Finset.card_disjSum,Finset.card_univ,Fintype.card_fin]
    exact hall T
  obtain ⟨f,hf,acceptable⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' choices).mp full
  let U := (Finset.univ : Finset L).filter (fun u => ∃ r : R, f u = Sum.inl r)
  have real (u : U) : ∃ r : R, f u.val = Sum.inl r := (Finset.mem_filter.mp u.property).2
  let g := fun u : U => (real u).choose
  have hg (u : U) : f u.val = Sum.inl (g u) := (real u).choose_spec
  have gi : Function.Injective g := by
    intro u v eq
    apply Subtype.ext
    apply hf
    exact (hg u).trans ((congrArg Sum.inl eq).trans (hg v).symm)
  let D := (Finset.univ : Finset L) \ U
  have dummy (u : D) : ∃ i : Fin d, f u.val = Sum.inr i := by
    cases eq : f u.val with
    | inr j => exact ⟨j,rfl⟩
    | inl r => exact ((Finset.mem_sdiff.mp u.property).2 (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,r,eq⟩)).elim
  let index := fun u : D => (dummy u).choose
  have di : Function.Injective index := by
    intro u v eq
    apply Subtype.ext
    apply hf
    exact (dummy u).choose_spec.trans ((congrArg Sum.inr eq).trans (dummy v).choose_spec.symm)
  have cap := Fintype.card_le_of_injective index di
  change Fintype.card D ≤ Fintype.card (Fin d) at cap
  simp only [Fintype.card_coe,Fintype.card_fin] at cap
  have part := Finset.card_sdiff_add_card_inter (Finset.univ : Finset L) U
  simp only [Finset.univ_inter,Finset.card_univ] at part
  change D.card+U.card=Fintype.card L at part
  refine ⟨U,by dsimp [d] at cap; omega,⟨g,gi⟩,?_⟩
  intro u
  have spec := acceptable u.val
  rw [hg] at spec
  simpa [choices] using spec
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
private theorem closed_mem_end {W : Type*} {H : SimpleGraph W} {S : Set W} {a b : W}
    (closed : ∀ u∈S, ∀ v, H.Adj u v → v∈S) (walk : H.Walk a b) (ha : a∈S) : b∈S := by
  induction walk with
  | nil => exact ha
  | cons h q ih => exact ih (closed _ ha _ h)
omit [Fintype V] in
theorem matching_at_buffered_boundary (P K F : Finset V) (apart : Disjoint P K)
    (fP : Disjoint F P) (fK : Disjoint F K)
    (boundary : ∀ u∈K, ∀ v∉K, G.Adj u v → v∈P ∨ v∈F)
    {s : ℕ} (smallP : s ≤ P.card) (smallK : s ≤ K.card)
    (connected : ∀ cut : Finset V, cut.card < s+F.card → (G.induce {u : V | u∉cut}).Connected) :
    ∃ A : Finset V, A⊆P ∧ s ≤ A.card ∧ ∃ f : A ↪ K, ∀ u, G.Adj u.val (f u).val := by
  classical
  let links := fun u : P => K.attach.filter (fun v => G.Adj u.val v.val)
  have hall (T : Finset P) : T.card ≤ (T.biUnion links).card+(Fintype.card P-s) := by
    let A := T.image (fun u : P => u.val)
    let N := T.biUnion links
    let B := N.image (fun v : K => v.val)
    let base := (P \ A) ∪ B
    let cut := base ∪ F
    have aP : A⊆P := by
      intro z hz
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hz
      exact u.property
    have bK : B⊆K := by
      intro z hz
      obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hz
      exact v.property
    have ca : A.card=T.card := Finset.card_image_of_injective _ Subtype.val_injective
    have cb : B.card=N.card := Finset.card_image_of_injective _ Subtype.val_injective
    have tP : T.card ≤ P.card := by simpa using T.card_le_univ
    by_contra! bad
    change (T.biUnion links).card+(Fintype.card P-s) < T.card at bad
    change N.card+(Fintype.card P-s) < T.card at bad
    simp only [Fintype.card_coe] at bad
    have shortBase : base.card < s := by
      have bound := Finset.card_union_le (P \ A) B
      rw [Finset.card_sdiff_of_subset aP,ca,cb] at bound
      change ((P \ A) ∪ B).card < s
      omega
    have short : cut.card < s+F.card := (Finset.card_union_le base F).trans_lt (Nat.add_lt_add_right shortBase _)
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < (K \ B).card by
      rw [Finset.card_sdiff_of_subset bK,cb]
      omega)
    obtain ⟨vK,vB⟩ := Finset.mem_sdiff.mp hv
    have uA : u.val∈A := Finset.mem_image.mpr ⟨u,hu,rfl⟩
    have uSafe : u.val∉cut := by
      intro h
      rcases Finset.mem_union.mp h with core | barrier
      · rcases Finset.mem_union.mp core with h | h
        · exact (Finset.mem_sdiff.mp h).2 uA
        · exact Finset.disjoint_left.mp apart u.property (bK h)
      · exact Finset.disjoint_left.mp fP barrier u.property
    have vSafe : v∉cut := by
      intro h
      rcases Finset.mem_union.mp h with core | barrier
      · rcases Finset.mem_union.mp core with h | h
        · exact Finset.disjoint_left.mp apart (Finset.mem_sdiff.mp h).1 vK
        · exact vB h
      · exact Finset.disjoint_left.mp fK barrier vK
    let H := G.induce {z : V | z∉cut}
    let S : Set {z : V // z∉cut} := {z | z.val∈K}
    have closed : ∀ z∈S, ∀ w, H.Adj z w → w∈S := by
      intro z zk w edge
      change z.val∈K at zk
      change w.val∈K
      by_contra wk
      have ambient : G.Adj z.val w.val := edge
      have wp : w.val∈P := (boundary z.val zk w.val wk ambient).resolve_right
        (fun barrier => w.property (Finset.mem_union_right _ barrier))
      have wa : w.val∈A := by
        by_contra no
        exact w.property (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨wp,no⟩)))
      obtain ⟨t,ht,teq⟩ := Finset.mem_image.mp wa
      let zk' : K := ⟨z.val,zk⟩
      have hit : zk'∈N := Finset.mem_biUnion.mpr ⟨t,ht,Finset.mem_filter.mpr
        ⟨Finset.mem_attach _ _,show G.Adj t.val z.val by rw [teq]; exact ambient.symm⟩⟩
      exact z.property (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨zk',hit,rfl⟩)))
    obtain ⟨walk⟩ := (connected cut short).preconnected ⟨v,vSafe⟩ ⟨u.val,uSafe⟩
    have uk := closed_mem_end (S := S) closed walk (show (⟨v,vSafe⟩ : {z : V // z∉cut})∈S from vK)
    exact Finset.disjoint_left.mp apart u.property uk
  obtain ⟨U,wide,f,acceptable⟩ := hall_at_least links s (by simpa using smallP) hall
  let A := U.image (fun u : P => u.val)
  have fromA (z : A) : ∃ u : U, u.val.val=z.val := by
    obtain ⟨t,ht,eq⟩ := Finset.mem_image.mp z.property
    exact ⟨⟨t,ht⟩,eq⟩
  let pick := fun z : A => (fromA z).choose
  have pickEq (z : A) : (pick z).val.val=z.val := (fromA z).choose_spec
  have pi : Function.Injective pick := by
    intro z w h
    apply Subtype.ext
    exact (pickEq z).symm.trans ((congrArg (fun u : U => u.val.val) h).trans (pickEq w))
  let assign := (⟨pick,pi⟩ : A ↪ U).trans f
  refine ⟨A,?_,?_,assign,?_⟩
  · intro v hv
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hv
    exact t.property
  · simpa [A,Finset.card_image_of_injective _ Subtype.val_injective] using wide
  · intro z
    have adj := (Finset.mem_filter.mp (acceptable (pick z))).2
    change G.Adj (pick z).val.val (assign z).val at adj
    rwa [pickEq] at adj
omit [Fintype V] in
theorem matching_at_component_boundary (P K : Finset V) (apart : Disjoint P K)
    (boundary : ∀ u∈K, ∀ v∉K, G.Adj u v → v∈P)
    {s : ℕ} (smallP : s ≤ P.card) (smallK : s ≤ K.card)
    (connected : ∀ cut : Finset V, cut.card < s → (G.induce {u : V | u∉cut}).Connected) :
    ∃ A : Finset V, A⊆P ∧ s ≤ A.card ∧ ∃ f : A ↪ K, ∀ u, G.Adj u.val (f u).val := by
  apply matching_at_buffered_boundary P K ∅ apart (by simp) (by simp)
    (fun u hu v hv e => Or.inl (boundary u hu v hv e)) smallP smallK
  simpa using connected
end Graph189ExteriorGap
end
section
open Finset SimpleGraph
namespace Graph189DenseExteriorOrder
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] {x y : V}
theorem neighbors_on_path (p : G.Walk x y) (W : Finset V)
    (boundary : ∀ w ∈ W, ∀ v, G.Adj w v → v ∉ W → v ∈ p.support)
    {w : V} (hw : w ∈ W) :
    G.degree w+1 ≤ W.card+((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card := by
  classical
  let R := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)
  let P := R.image (fun i => p.support[i.val])
  have sub : insert w (G.neighborFinset w) ⊆ W ∪ P := by
    intro v hv
    rcases mem_insert.mp hv with rfl | h
    · exact mem_union_left _ hw
    have edge := (G.mem_neighborFinset _ _).mp h
    by_cases vw : v ∈ W
    · exact mem_union_left _ vw
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp (boundary w hw v edge vw)
    exact mem_union_right _ (mem_image.mpr ⟨⟨i,hi⟩,
      mem_filter.mpr ⟨mem_univ _,by simpa only [eq] using edge.symm⟩,eq⟩)
  have h := (card_le_card sub).trans (card_union_le W P)
  rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree] at h
  exact h.trans (Nat.add_le_add_left card_image_le _)
end Graph189DenseExteriorOrder
end
section
open SimpleGraph Finset
namespace Graph189CutSides
variable {V : Type*} [Fintype V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem connectivity_le_degree (z : V) : G.vertexConnectivity ≤ G.degree z := by
  classical
  let S := G.neighborFinset z
  have sz : S.card=G.degree z := G.card_neighborFinset_eq_degree z
  have convention : G.vertexConnectivity ≤ Fintype.card V-1 := by
    unfold vertexConnectivity
    rw [if_neg (not_le.mpr (Fintype.one_lt_card (α:=V)))]
    exact Nat.sInf_le ⟨univ.erase z,by simp,Or.inr (by simp)⟩
  by_contra! fail
  have conn := connected_after_smaller_deletion (G:=G) S (sz ▸ fail)
  let W := {v : V | v ∉ S}
  let z' : W := ⟨z, show z ∉ G.neighborFinset z by simp⟩
  have card : 1 < Fintype.card W := by
    have same : W = ((Sᶜ : Finset V) : Set V) := by ext v; simp [W]
    rw [Fintype.card_congr (Equiv.setCongr same)]
    change 1 < Fintype.card (Sᶜ : Finset V)
    rw [Fintype.card_coe,Finset.card_compl]
    omega
  let _ : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp card
  obtain ⟨w,edge⟩ := conn.preconnected.exists_adj_of_nontrivial z'
  exact w.property ((G.mem_neighborFinset z w.val).mpr edge)
end Graph189CutSides
end
section
open SimpleGraph Finset
namespace Graph189FourTerminalGap
open Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {a b : V}
theorem impossible_of_exact_length (p : G.Walk a b) (hp : p.IsPath) {x : V} (outside : x ∉ p.support)
    {i j lo hi m : ℕ} (left : 0 < i) (spaced : i+2 ≤ j) (right : j+1 < p.support.length)
    (marks : contactPositions p x = {i,j})
    (bound : hi ≤ p.support.length) (size : lo+m=hi)
    (unmarked : ∀ h ∈ Ico lo hi, h ≠ i ∧ h ≠ j)
    (via : ∀ h ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert h) w)
    (quota : (univ.filter (fun y => G.dist x y=2)).card ≤ m+1) : False := by
  classical
  let J := Ico lo hi
  let W : Finset ℕ := {i-1,i+1,j-1,j+1}
  have skipI : ¬(lo ≤ i ∧ i < hi) := fun h => (unmarked i (mem_Ico.mpr h)).1 rfl
  have skipJ : ¬(lo ≤ j ∧ j < hi) := fun h => (unmarked j (mem_Ico.mpr h)).2 rfl
  have pair : ∃ u ∈ W, ∃ v ∈ W, u≠v ∧ u∉J ∧ v∉J := by
    by_cases before : hi ≤ i
    · refine ⟨j-1,by simp [W],j+1,by simp [W],by omega,?_,?_⟩ <;> simp [J] <;> omega
    by_cases after : j < lo
    · refine ⟨i-1,by simp [W],i+1,by simp [W],by omega,?_,?_⟩ <;> simp [J] <;> omega
    refine ⟨i-1,by simp [W],j+1,by simp [W],by omega,?_,?_⟩ <;> simp [J] <;> omega
  obtain ⟨u,hu,v,hv,ne,uout,vout⟩ := pair
  have mark {h : ℕ} (m : h=i ∨ h=j) : G.Adj x (p.getVert h) := by
    have hm : h ∈ contactPositions p x := by simpa [marks] using m
    exact ((mem_contactPositions p x h).mp hm).2.symm
  have charge (h : ℕ) (hh : h < p.support.length) (missing : h≠i ∧ h≠j)
      (link : ∃ w, G.Adj x w ∧ G.Adj (p.getVert h) w) : G.dist x (p.getVert h)=2 := by
    obtain ⟨w,hx,hw⟩ := link
    have different : x ≠ p.getVert h := fun eq => outside (eq ▸ p.getVert_mem_support h)
    apply two_step_metric different _ hx hw
    intro adj
    have hm := (mem_contactPositions p x h).mpr ⟨hh,adj.symm⟩
    rw [marks] at hm
    simp only [mem_insert,mem_singleton,missing.1,missing.2,or_self] at hm
  have shifts (h : ℕ) (hh : h∈W) : h < p.support.length ∧ G.dist x (p.getVert h)=2 := by
    have len := p.length_support
    have before (t : ℕ) (pos : 0 < t) (range : t < p.support.length) (hit : t=i ∨ t=j)
        (miss : t-1≠i ∧ t-1≠j) : G.dist x (p.getVert (t-1))=2 := by
      have step := p.adj_getVert_succ (i:=t-1) (by omega)
      rw [show t-1+1=t by omega] at step
      exact charge _ (by omega) miss ⟨_,mark hit,step⟩
    have after (t : ℕ) (range : t+1 < p.support.length) (hit : t=i ∨ t=j)
        (miss : t+1≠i ∧ t+1≠j) : G.dist x (p.getVert (t+1))=2 :=
      charge _ range miss ⟨_,mark hit,(p.adj_getVert_succ (i:=t) (by omega)).symm⟩
    simp only [W,mem_insert,mem_singleton] at hh
    rcases hh with rfl|rfl|rfl|rfl
    · exact ⟨by omega,before i left (by omega) (Or.inl rfl) (by omega)⟩
    · exact ⟨by omega,after i (by omega) (Or.inl rfl) (by omega)⟩
    · exact ⟨by omega,before j (by omega) (by omega) (Or.inr rfl) (by omega)⟩
    · exact ⟨right,after j right (Or.inr rfl) (by omega)⟩
  let T := insert u (insert v J)
  have good (h : ℕ) (hh : h ∈ T) : h < p.support.length ∧ G.dist x (p.getVert h)=2 := by
    rcases mem_insert.mp hh with rfl | hrest
    · exact shifts _ hu
    rcases mem_insert.mp hrest with rfl | member
    · exact shifts _ hv
    have r := (mem_Ico.mp member).2.trans_le bound
    exact ⟨r,charge _ r (unmarked _ member) (via _ member)⟩
  have count : T.card=m+2 := by
    have jcard : J.card=hi-lo := Nat.card_Ico _ _
    rw [show T=insert u (insert v J) from rfl,card_insert_of_notMem (by simpa [ne] using uout),
      card_insert_of_notMem vout,jcard]
    omega
  have inj : Set.InjOn p.getVert (T : Set ℕ) := by
    intro h hh e he eq
    have := (good _ hh).1
    have := (good _ he).1
    have := p.length_support
    exact hp.getVert_injOn (by change h ≤ p.length; omega) (by change e ≤ p.length; omega) eq
  have sub : T.image p.getVert ⊆ univ.filter (fun y => G.dist x y=2) := by
    intro w hw
    obtain ⟨e,he,rfl⟩ := mem_image.mp hw
    exact mem_filter.mpr ⟨mem_univ _,(good _ he).2⟩
  have large := (card_le_card sub).trans quota
  rw [card_image_of_injOn inj,count] at large
  omega
end Graph189FourTerminalGap
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {a b x y : V}
theorem protected_swap_neighbors_with_route (p : G.Walk a b) (hp : p.IsPath) (z : V)
    (A J B : List V) (split : p.support=A++J++B) (kept : z ∈ A ∨ z ∈ B)
    (q : G.Walk x y) (hq : q.IsPath) (dis : List.Disjoint q.support p.support)
    (size : q.support.length=J.length)
    (left : ∀ v∈A.getLast?, G.Adj v x) (right : ∀ v∈B.head?, G.Adj y v)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → z ∈ r.support → q.support ⊆ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {c : V} (contact : c ∈ A ∨ c ∈ B) (neighbor : ∃ v ∈ J, G.Adj c v) :
    ∀ v ∈ J, G.Adj c v := by
  obtain ⟨i,j,r,hr,e⟩ := splice_support p hp A J B split q hq dis left right
  have nd := hp.support_nodup
  rw [split] at nd
  have separated (v : V) (hv : v ∈ J) : v ∉ r.support := by
    rw [e]
    intro h
    rcases List.mem_append.mp h with mid | last
    · rcases List.mem_append.mp mid with first | new
      · exact List.disjoint_left.mp nd.of_append_left.disjoint first hv
      · exact List.disjoint_left.mp dis new (by simp [split,hv])
    · exact List.disjoint_left.mp nd.disjoint (by simp [hv]) last
  have length : r.length=p.length := by
    have h := r.length_support
    have g := p.length_support
    rw [split] at g
    rw [e] at h
    simp only [List.length_append,size] at h g
    omega
  have keep (v : V) (h : v∈A ∨ v∈B) : v∈r.support := by
    rw [e]
    rcases h with h | h <;> simp [h]
  obtain ⟨v,hv,edge⟩ := neighbor
  exact fun w hw => uniform r hr (keep z kept) (fun v hv => by rw [e]; simp [hv]) length c (keep c contact)
    v (separated v hv) w (separated w hw) edge
theorem protected_swap_neighbors (p : G.Walk a b) (hp : p.IsPath) (z : V)
    (A J B : List V) (split : p.support=A++J++B) (kept : z ∈ A ∨ z ∈ B)
    (q : G.Walk x y) (hq : q.IsPath) (dis : List.Disjoint q.support p.support)
    (size : q.support.length=J.length)
    (left : ∀ v∈A.getLast?, G.Adj v x) (right : ∀ v∈B.head?, G.Adj y v)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → z ∈ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {c : V} (contact : c ∈ A ∨ c ∈ B) (neighbor : ∃ v ∈ J, G.Adj c v) :
    ∀ v ∈ J, G.Adj c v := by
  apply protected_swap_neighbors_with_route p hp z A J B split kept q hq dis size left right _ contact neighbor
  exact fun r hr hz _ => uniform r hr hz
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {a b x y : V}
theorem interval_exchange_witnesses_with_route (p : G.Walk a b) (hp : p.IsPath) (t : Fin p.support.length)
    (M : Finset (Fin p.support.length)) (q : G.Walk x y) (hq : q.IsPath)
    (dis : List.Disjoint q.support p.support)
    (touch : ∀ i ∈ M, G.Adj p.support[i.val] x ∧ G.Adj p.support[i.val] y)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → p.support[t.val] ∈ r.support → q.support ⊆ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {lo hi : ℕ} (nonempty : lo < hi) (bound : hi ≤ p.support.length) (size : hi-lo=q.support.length)
    (safe : t.val < lo ∨ hi ≤ t.val) (lower : lo=0 ∨ ∃ i∈M, i.val+1=lo)
    (upper : hi=p.support.length ∨ ∃ i∈M, i.val=hi) (one : 0 < lo ∨ hi < p.support.length) :
    ∀ i ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert i) w := by
  let L := p.support
  let A := L.take lo
  let J := (L.drop lo).take (hi-lo)
  let B := L.drop hi
  have split : p.support=A++J++B := by
    change L=L.take lo++(L.drop lo).take (hi-lo)++L.drop hi
    rw [←List.take_add, Nat.add_sub_of_le nonempty.le,List.take_append_drop]
  have kept (i : Fin L.length) (s : i.val < lo ∨ hi ≤ i.val) : L[i.val]∈A ∨ L[i.val]∈B := by
    rcases s with u|v
    · exact Or.inl (List.mem_take_iff_getElem.mpr ⟨i.val,lt_min u i.isLt,rfl⟩)
    · exact Or.inr (List.mem_drop_iff_getElem.mpr
        ⟨i.val-hi,by have := i.isLt; omega,by simp [Nat.add_sub_of_le v]⟩)
  have inside (i : ℕ) (u : lo ≤ i) (v : i < hi) : p.getVert i ∈ J := by
    have ri : i < L.length := v.trans_le bound
    apply List.mem_take_iff_getElem.mpr
    refine ⟨i-lo,?_,?_⟩
    · rw [List.length_drop]
      exact lt_min (Nat.sub_lt_sub_right u v) (Nat.sub_lt_sub_right u ri)
    · simpa only [List.getElem_drop, Nat.add_sub_of_le u] using get_at p ri
  have left : ∀ v∈A.getLast?, G.Adj v x := by
    intro v hv
    rcases lower with h | ⟨i,mem,e⟩
    · simp [A,h] at hv
    · have last : A.getLast? = some L[i.val] := by
        change (L.take lo).getLast? = _
        rw [←e]
        exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
          (l:=L) (i:=i.val) i.isLt)).trans List.getLast?_concat
      have same : L[i.val]=v := by simpa [last] using hv
      exact same ▸ (touch i mem).1
  have right : ∀ v∈B.head?, G.Adj y v := by
    intro v hv
    rcases upper with h | ⟨i,mem,e⟩
    · simp [B,L,h] at hv
    · have first : B.head?=some L[i.val] := by simp [B,←e,List.head?_drop]
      have same : L[i.val]=v := by simpa [first] using hv
      exact same ▸ (touch i mem).2.symm
  have length : q.support.length=J.length := by
    simp only [J,List.length_take,List.length_drop]
    rw [min_eq_left (Nat.sub_le_sub_right bound lo)]
    exact size.symm
  have witness : ∃ c, (c∈A ∨ c∈B) ∧ G.Adj x c ∧ ∃ v∈J, G.Adj c v := by
    rcases one with first|last
    · obtain zero | ⟨i,mem,e⟩ := lower
      · omega
      have edge := p.adj_getVert_succ (i:=i.val) (by have := p.length_support; omega)
      rw [e] at edge
      refine ⟨L[i.val],kept i (Or.inl (by omega)),(touch i mem).1.symm,
        p.getVert lo,inside lo le_rfl nonempty,?_⟩
      change G.Adj p.support[i.val] _
      rw [get_at p i.isLt]
      exact edge
    · obtain tail | ⟨i,mem,e⟩ := upper
      · omega
      have edge := p.adj_getVert_succ (i:=hi-1) (by have := p.length_support; omega)
      rw [show hi-1+1=hi by omega] at edge
      refine ⟨L[i.val],kept i (Or.inr e.ge),(touch i mem).1.symm,
        p.getVert (hi-1),inside _ (by omega) (by omega),?_⟩
      change G.Adj p.support[i.val] _
      rw [get_at p i.isLt,e]
      exact edge.symm
  obtain ⟨c,hc,cx,neighbor⟩ := witness
  have all := protected_swap_neighbors_with_route p hp _ A J B split (kept t safe) q hq dis length left right uniform hc neighbor
  intro i h
  exact ⟨c,cx,(all _ (inside i (mem_Ico.mp h).1 (mem_Ico.mp h).2)).symm⟩
theorem interval_exchange_witnesses (p : G.Walk a b) (hp : p.IsPath) (t : Fin p.support.length)
    (M : Finset (Fin p.support.length)) (q : G.Walk x y) (hq : q.IsPath)
    (dis : List.Disjoint q.support p.support)
    (touch : ∀ i ∈ M, G.Adj p.support[i.val] x ∧ G.Adj p.support[i.val] y)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → p.support[t.val] ∈ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {lo hi : ℕ} (nonempty : lo < hi) (bound : hi ≤ p.support.length) (size : hi-lo=q.support.length)
    (safe : t.val < lo ∨ hi ≤ t.val) (lower : lo=0 ∨ ∃ i∈M, i.val+1=lo)
    (upper : hi=p.support.length ∨ ∃ i∈M, i.val=hi) (one : 0 < lo ∨ hi < p.support.length) :
    ∀ i ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert i) w := by
  apply interval_exchange_witnesses_with_route p hp t M q hq dis touch _ nonempty bound size safe lower upper one
  exact fun r hr hz _ => uniform r hr hz
end Graph189ExteriorGap
end
section
open Finset SimpleGraph
namespace Graph189ExteriorAttachment
theorem extra_port {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (p : G.Walk x y) (W : Finset V) (j : ℕ) (many : j < W.card)
    (rows : ∀ w ∈ W, j ≤ ((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card)
    (cover : j < (W.biUnion (fun w => (univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w))).card) :
    ∃ marks : Finset (Fin p.support.length), marks.card = j+1 ∧
      ∃ attach : marks ↪ W, ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val := by
  classical
  let N (w : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)
  let F (w : W) := N w.val
  have size : Fintype.card W = W.card := Fintype.card_coe W
  have whole : (univ.biUnion F).card = (W.biUnion N).card := by
    congr 1
    ext i
    constructor
    · intro hi
      obtain ⟨w,_,hw⟩ := mem_biUnion.mp hi
      exact mem_biUnion.mpr ⟨w.val,w.property,hw⟩
    · intro hi
      obtain ⟨w,hw,edge⟩ := mem_biUnion.mp hi
      exact mem_biUnion.mpr ⟨⟨w,hw⟩,mem_univ _,edge⟩
  have hall (T : Finset W) : T.card ≤ (T.biUnion F).card + (Fintype.card W-(j+1)) := by
    by_cases all : T=univ
    · rw [all,card_univ,whole,size]
      change j < (W.biUnion N).card at cover
      omega
    rcases T.eq_empty_or_nonempty with rfl | ⟨w,hw⟩
    · simp
    have proper : T.card < W.card := by
      by_contra! h
      exact all (Finset.eq_of_subset_of_card_le (subset_univ _) (by simpa using h))
    have incl : F w ⊆ T.biUnion F := fun i hi => mem_biUnion.mpr ⟨w,hw,hi⟩
    have lower := (rows w.val w.property).trans (card_le_card incl)
    omega
  obtain ⟨U,large,f,edge⟩ := Graph189ExteriorGap.hall_at_least F (j+1) (by omega) hall
  obtain ⟨B,sub,cardB⟩ := exists_subset_card_eq large
  let inc : B ↪ U := ⟨fun b => ⟨b.val,sub b.property⟩,
    fun _ _ e => Subtype.ext (congrArg (fun w : U => w.val) e)⟩
  let pos := inc.trans f
  let M := (univ : Finset B).image pos
  let chosen (b : B) : M := ⟨pos b,mem_image_of_mem _ (mem_univ _)⟩
  have bij : Function.Bijective chosen := by
    constructor
    · intro u v eq
      exact pos.injective (congrArg Subtype.val eq)
    · intro i
      obtain ⟨b,_,eq⟩ := mem_image.mp i.property
      exact ⟨b,Subtype.ext eq⟩
  let equiv := Equiv.ofBijective chosen bij
  let vertex : B ↪ W := ⟨Subtype.val,Subtype.val_injective⟩
  have card : M.card = B.card := by simpa using Fintype.card_congr equiv.symm
  refine ⟨M,card.trans cardB,equiv.symm.toEmbedding.trans vertex,?_⟩
  intro i
  have value : pos (equiv.symm i) = i.val := congrArg Subtype.val (equiv.apply_symm_apply i)
  have adj := (mem_filter.mp (edge (inc (equiv.symm i)))).2
  change G.Adj p.support[(pos (equiv.symm i)).val] (equiv.symm i).val.val at adj
  exact (congrArg (fun index : Fin p.support.length =>
    G.Adj (p.support.get index) (equiv.symm i).val.val) value).mp adj
end Graph189ExteriorAttachment
end
section
open SimpleGraph Finset
namespace Graph189LayerCover
variable {V : Type*} [Fintype V]
noncomputable def layer (G : SimpleGraph V) (z : V) (n : ℕ) : Finset V := by
  classical
  exact univ.filter (fun v => G.dist z v = n)
@[simp] theorem in_layer {G : SimpleGraph V} {z y : V} {n : ℕ} :
    y ∈ layer G z n ↔ G.dist z y = n := by classical simp [layer]
private theorem minimal_cover (A B : Finset V) (R : V → V → Prop)
    (hc : ∀ b ∈ B, ∃ a ∈ A, R a b) :
    ∃ T ⊆ A, (∀ b ∈ B, ∃ a ∈ T, R a b) ∧
      ∀ a ∈ T, ∃ b ∈ B, R a b ∧ ∀ a' ∈ T, a' ≠ a → ¬ R a' b := by
  classical
  let covers (S : Finset V) := ∀ b ∈ B, ∃ a ∈ S, R a b
  let family := A.powerset.filter covers
  have ha : A ∈ family := mem_filter.mpr ⟨mem_powerset.mpr (fun _ h => h), hc⟩
  obtain ⟨T,hT,hmin⟩ := family.exists_min_image Finset.card ⟨A,ha⟩
  obtain ⟨hsub,hcovers⟩ := mem_filter.mp hT
  have hsub' := mem_powerset.mp hsub
  refine ⟨T,hsub',hcovers,?_⟩
  intro a haT
  have missing : ¬ covers (T.erase a) := by
    intro h
    have hs : T.erase a ∈ family := mem_filter.mpr
      ⟨mem_powerset.mpr ((erase_subset a T).trans hsub'),h⟩
    exact (not_le_of_gt (card_erase_lt_of_mem haT)) (hmin _ hs)
  change ¬ (∀ b ∈ B, ∃ a' ∈ T.erase a, R a' b) at missing
  push Not at missing
  obtain ⟨b,hb,hprivate⟩ := missing
  obtain ⟨x,hx,hxb⟩ := hcovers b hb
  have hxa : x = a := by
    by_contra h
    exact hprivate x (mem_erase.mpr ⟨h,hx⟩) hxb
  exact ⟨b,hb,hxa ▸ hxb,fun a' ha' hdiff => hprivate a' (mem_erase.mpr ⟨hdiff,ha'⟩)⟩
omit [Fintype V] in
private theorem predecessor {G : SimpleGraph V} {z y : V} {d : ℕ}
    (h : G.dist z y = d+1) : ∃ p, G.dist z p = d ∧ G.Adj p y := by
  have hr : G.dist y z = d+1 := by rwa [dist_comm]
  have hpos : G.Reachable y z := Reachable.of_dist_ne_zero (by omega)
  obtain ⟨walk,hlen⟩ := hpos.exists_walk_length_eq_dist
  cases walk with
  | nil => simp at h
  | cons hy tail =>
    rename_i p
    have hlen' : tail.length = d := by rw [Walk.length_cons,hr] at hlen; omega
    have hle : G.dist z p ≤ d := by rw [dist_comm]; exact hlen' ▸ G.dist_le tail
    have ht := hy.diff_dist_adj (u := z)
    exact ⟨p,by omega,hy.symm⟩
omit [Fintype V] in
private theorem dist_two {G : SimpleGraph V} {x y q : V}
    (hne : x ≠ y) (hna : ¬G.Adj x y) (h1 : G.Adj x q) (h2 : G.Adj q y) :
    G.dist x y = 2 := by
  let w : G.Walk x y := .cons h1 (.cons h2 .nil)
  have hlo := w.reachable.one_lt_dist_of_ne_of_not_adj hne hna
  have hhi : G.dist x y ≤ 2 := G.dist_le w
  omega
omit [Fintype V] in
private theorem second_step {G : SimpleGraph V} (hc : G.Connected) (z y : V)
    (h : 2 ≤ G.dist z y) : ∃ b, G.dist z b = 2 ∧ G.dist z y = 2 + G.dist b y := by
  generalize hd : G.dist z y = d at h ⊢
  induction d using Nat.strong_induction_on generalizing y with
  | h d ih =>
    by_cases e : d=2
    · exact ⟨y,hd.trans e,by simp [e]⟩
    · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d≠0 by omega)
      obtain ⟨p,hp,hpy⟩ := predecessor hd
      obtain ⟨b,hb,split⟩ := ih m (by omega) p hp (by omega)
      have up := hc.dist_triangle (u:=b) (v:=p) (w:=y)
      rw [dist_eq_one_iff_adj.mpr hpy] at up
      have low := hc.dist_triangle (u:=z) (v:=b) (w:=y)
      exact ⟨b,hb,by omega⟩
theorem order_of_cover (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (z : V) (k : ℕ) (cap : ∀ v, G.distEven v ≤ k+1) (R : Finset V)
    (arms : ∀ a ∈ R, G.Adj z a)
    (covers : ∀ b ∈ layer G z 2, ∃ a ∈ R, G.Adj a b) :
    ∃ t ≤ R.card, t ≤ k+1 ∧ Fintype.card V ≤ 1+G.degree z+k+t*(k+1-t) := by
  classical
  obtain ⟨T,hTR,hTc,hTp⟩ := minimal_cover R (layer G z 2) G.Adj covers
  let port (a : V) : V := if h : a ∈ T then (hTp a h).choose else z
  have hp (a : V) (h : a ∈ T) : G.dist z (port a) = 2 ∧ G.Adj a (port a) ∧
      ∀ a' ∈ T, a' ≠ a → ¬ G.Adj a' (port a) := by
    simpa [port,h] using (hTp a h).choose_spec
  have hA (a : V) (h : a ∈ T) : G.dist z a = 1 := dist_eq_one_iff_adj.mpr (arms a (hTR h))
  let evenSet (a : V) := (univ.filter (fun v => Even (G.dist a v))).erase a
  have quota (a : V) : (evenSet a).card ≤ k := by
    have self : a ∈ univ.filter (fun v => Even (G.dist a v)) := by simp
    have bound := cap a
    change (univ.filter (fun v => Even (G.dist a v))).card ≤ k+1 at bound
    unfold evenSet
    rw [card_erase_of_mem self]
    omega
  have evenMem {a v : V} (n : a ≠ v) (ev : Even (G.dist a v)) : v ∈ evenSet a :=
    mem_erase.mpr ⟨Ne.symm n, mem_filter.mpr ⟨mem_univ _,ev⟩⟩
  let F := univ.filter (fun v => 3 ≤ G.dist z v ∧ ¬ Even (G.dist z v))
  let W (a : V) := F.filter (fun c => c ∈ evenSet a)
  have cov : F ⊆ T.biUnion W := by
    intro c hcF
    obtain ⟨far,odd⟩ := (mem_filter.mp hcF).2
    obtain ⟨b,hb,hsplit⟩ := second_step hc z c (by omega)
    obtain ⟨a,ha,hab⟩ := hTc b (in_layer.mpr hb)
    have upper := hc.dist_triangle (u:=a) (v:=b) (w:=c)
    rw [dist_eq_one_iff_adj.mpr hab] at upper
    have lower := hc.dist_triangle (u:=z) (v:=a) (w:=c)
    have unit := hA a ha
    have distinct : a ≠ c := by rintro rfl; omega
    have even : Even (G.dist a c) := by rw [Nat.even_iff] at odd ⊢; omega
    exact mem_biUnion.mpr ⟨a,ha,mem_filter.mpr ⟨hcF,evenMem distinct even⟩⟩
  have row (a : V) (ha : a ∈ T) : (W a).card + T.card ≤ k+1 := by
    let f (j : V) := if G.Adj a j then port j else j
    have hzj (j : V) (hj : j ∈ T) : G.dist z (f j) ≤ 2 := by
      by_cases h : G.Adj a j <;> simp [f,h,(hp j hj).1,hA j hj]
    have finj : Set.InjOn f ↑(T.erase a) := by
      intro j hj l hl hEq
      obtain ⟨_,hjT⟩ := mem_erase.mp hj
      obtain ⟨_,hlT⟩ := mem_erase.mp hl
      by_cases hjA : G.Adj a j <;> by_cases hlA : G.Adj a l <;> simp [f,hjA,hlA] at hEq
      · by_contra hne
        exact (hp l hlT).2.2 j hjT hne (hEq ▸ (hp j hjT).2.1)
      · have h1 := (hp j hjT).1; have h2 := hA l hlT; rw [hEq] at h1; omega
      · have h1 := (hp l hlT).1; have h2 := hA j hjT; rw [hEq] at h2; omega
      · exact hEq
    let E := (T.erase a).image f
    have heq : E.card = (T.erase a).card := card_image_of_injOn finj
    have hdis : Disjoint (W a) E := by
      apply Finset.disjoint_left.mpr
      intro x hx hw
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hw
      have h1 := (mem_filter.mp (mem_filter.mp hx).1).2.1
      have h2 := hzj j (mem_erase.mp hj).2
      omega
    have incl : W a ∪ E ⊆ evenSet a := by
      intro x hx
      rcases mem_union.mp hx with hw|he
      · exact (mem_filter.mp hw).2
      · obtain ⟨j,hj,rfl⟩ := mem_image.mp he
        obtain ⟨hne,hj⟩ := mem_erase.mp hj
        suffices hd : G.dist a (f j) = 2 by
          apply evenMem _ (by simp [hd])
          intro eq
          rw [← eq, SimpleGraph.dist_self] at hd
          omega
        by_cases haj : G.Adj a j
        · simp only [f,if_pos haj]
          have hza := hA a ha
          have hzj' := (hp j hj).1
          apply dist_two _ ((hp j hj).2.2 a ha hne.symm) haj (hp j hj).2.1
          rintro heq'; rw [heq'] at hza; omega
        · simp only [f,if_neg haj]
          exact dist_two hne.symm haj (dist_eq_one_iff_adj.mp (hA a ha)).symm
            (dist_eq_one_iff_adj.mp (hA j hj))
    have hcount := (card_le_card incl).trans (quota a)
    rw [card_union_of_disjoint hdis,heq] at hcount
    have he := card_erase_add_one ha
    omega
  have hsize : T.card ≤ k+1 := by
    rcases T.eq_empty_or_nonempty with he|⟨a,ha⟩
    · simp [he]
    · have := row a ha; omega
  have farCount : F.card ≤ T.card*(k+1-T.card) := by
    calc F.card ≤ (T.biUnion W).card := card_le_card cov
         _ ≤ ∑ a ∈ T, (W a).card := card_biUnion_le
         _ ≤ ∑ _ ∈ T, (k+1-T.card) := sum_le_sum (fun a ha => by have := row a ha; omega)
         _ = T.card*(k+1-T.card) := by simp
  have all : (univ : Finset V) ⊆ (({z} ∪ G.neighborFinset z) ∪ evenSet z) ∪ F := by
    intro v hv
    by_cases same : v = z
    · subst v; simp
    by_cases adj : G.Adj z v
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ ((G.mem_neighborFinset z v).mpr adj)))
    by_cases e : Even (G.dist z v)
    · exact mem_union_left _ (mem_union_right _ (evenMem (Ne.symm same) e))
    have pos := (hc z v).one_lt_dist_of_ne_of_not_adj (Ne.symm same) adj
    exact mem_union_right _ (mem_filter.mpr ⟨hv,by rw [Nat.even_iff] at e; omega, e⟩)
  have one := card_union_le ({z} : Finset V) (G.neighborFinset z)
  have two := card_union_le ({z} ∪ G.neighborFinset z) (evenSet z)
  have three := card_union_le (({z} ∪ G.neighborFinset z) ∪ evenSet z) F
  have hcard := card_le_card all
  rw [card_univ] at hcard
  simp only [card_singleton,G.card_neighborFinset_eq_degree] at one
  exact ⟨T.card,card_le_card hTR,hsize,by have h := quota z; omega⟩
end Graph189LayerCover
end
section
open SimpleGraph Finset
namespace Graph189LayerCutoff
variable {V : Type*} [Fintype V]
private theorem row_mono {a t k : ℕ} (hta : t ≤ a) (ha : 2*a ≤ k+1) :
    t*(k+1-t) ≤ a*(k+1-a) := by
  have ht : t ≤ k+1 := by omega
  have hak : a ≤ k+1 := by omega
  have hsum : a+t ≤ k+1 := by omega
  have h : 0 ≤ (a-t : ℤ) * ((k:ℤ)+1-a-t) :=
    mul_nonneg (by omega) (by omega)
  zify [ht, hak]
  nlinarith
theorem order_of_small_cover (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (z : V) (k : ℕ) (cap : ∀ v, G.distEven v ≤ k+1) (R : Finset V)
    (arms : ∀ a ∈ R, G.Adj z a)
    (covers : ∀ b ∈ Graph189LayerCover.layer G z 2, ∃ a ∈ R, G.Adj a b)
    (hs : 2*R.card ≤ k+1) :
    Fintype.card V ≤ 1+G.degree z+k+R.card*(k+1-R.card) := by
  obtain ⟨t, hta, _, horder⟩ := Graph189LayerCover.order_of_cover G hc z k cap R arms covers
  exact horder.trans (Nat.add_le_add_left (row_mono hta hs) _)
theorem order_of_small_degree (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (z : V) (k : ℕ) (cap : ∀ v, G.distEven v ≤ k+1) (hs : 2*G.degree z ≤ k+1) :
    Fintype.card V ≤ 1+G.degree z+k+G.degree z*(k+1-G.degree z) := by
  classical
  have covers : ∀ b ∈ Graph189LayerCover.layer G z 2, ∃ a ∈ G.neighborFinset z, G.Adj a b := by
    intro b hb
    have two := Graph189LayerCover.in_layer.mp hb
    obtain ⟨walk, hlen⟩ := (hc b z).exists_walk_length_eq_dist
    have hdist : G.dist b z = 2 := by rwa [dist_comm]
    rw [hdist] at hlen
    cases walk with
    | nil => simp at hlen
    | cons e walk =>
      rename_i a
      have hlen' : walk.length = 1 := by rw [Walk.length_cons] at hlen; omega
      have hle : G.dist z a ≤ 1 := by rw [dist_comm]; exact hlen' ▸ G.dist_le walk
      have had := e.diff_dist_adj (u := z)
      exact ⟨a, (G.mem_neighborFinset z a).mpr (dist_eq_one_iff_adj.mp (by omega)), e.symm⟩
  simpa only [G.card_neighborFinset_eq_degree] using
    (order_of_small_cover G hc z k cap (G.neighborFinset z)
      (fun a ha => (G.mem_neighborFinset z a).mp ha) covers (by simpa using hs))
end Graph189LayerCutoff
end
section
open SimpleGraph Finset
namespace Graph189ParentConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem two_of_deletions (hc : G.Connected) (order : 3 ≤ Fintype.card V)
    (deletion : ∀ z : V, (G.induce {v : V | v≠z}).Connected) : 2 ≤ G.vertexConnectivity := by
  classical
  let M : Set ℕ := {j | ∃ S : Finset V, S.card=j ∧
    (¬(G.induce ((S : Set V)ᶜ)).Connected ∨ S.card=Fintype.card V-1)}
  have h : G.vertexConnectivity=sInf M := by
    unfold vertexConnectivity
    rw [if_neg (by omega : ¬Fintype.card V≤1)]
  obtain ⟨z⟩ := hc.nonempty
  have ex : M.Nonempty := ⟨_,univ.erase z,rfl,Or.inr (by simp)⟩
  rw [h]
  obtain ⟨T,sz,bad|full⟩ := Nat.sInf_mem ex
  · by_contra! small
    apply bad
    change (G.induce {v : V | v∉T}).Connected
    by_cases empty : T=∅
    · subst T
      rw [show {v : V | v∉(∅ : Finset V)}=Set.univ by ext; simp]
      exact hc.map G.induceUnivIso.symm.toHom G.induceUnivIso.symm.surjective
    obtain ⟨v,rfl⟩ := card_eq_one.mp (show T.card=1 by
      have := card_pos.mpr (nonempty_iff_ne_empty.mpr empty)
      omega)
    rw [show {w : V | w∉({v} : Finset V)}={w : V | w≠v} by ext; simp]
    exact deletion v
  · omega
end Graph189ParentConnectivity
end
section
open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189ThreeRegularMinimum
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem longest_path (z : V) :
    ∃ x y : V, ∃ p : G.Walk x y, p.IsPath ∧
      ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length := by
  classical
  let Good (n : ℕ) := ∃ x y : V, ∃ p : G.Walk x y, p.IsPath ∧ p.length = n
  have base : Good 0 := ⟨z,z,.nil,by simp,rfl⟩
  obtain ⟨x,y,p,hp,hlen⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  refine ⟨x,y,p,hp,?_⟩
  intro u v r hr
  rw [hlen]
  have card := hr.support_nodup.length_le_card
  have size := r.length_support
  exact Nat.le_findGreatest (by omega) (show Good r.length from ⟨u,v,r,hr,rfl⟩)
end Graph189ThreeRegularMinimum
end
section
open Finset SimpleGraph
namespace Graph189FiveExteriorRoots
variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
theorem extend_edge (degrees : ∀ w, 3 ≤ H.degree w) {u a : W} (ua : H.Adj u a) :
    ∃ b c, H.Adj a b ∧ H.Adj b c ∧ u≠b ∧ u≠c ∧ a≠c := by
  classical
  obtain ⟨b,hb,bu⟩ := exists_mem_ne (show 1 < (H.neighborFinset a).card by
    rw [H.card_neighborFinset_eq_degree]; have := degrees a; omega) u
  have ab := (H.mem_neighborFinset _ _).mp hb
  obtain ⟨c,hc⟩ := exists_mem_notMem_of_card_lt_card (s:={u,a}) (t:=H.neighborFinset b) (by
    rw [card_pair ua.ne,H.card_neighborFinset_eq_degree]
    exact degrees b)
  exact ⟨b,c,ab,(H.mem_neighborFinset _ _).mp hc.1,bu.symm,fun e => hc.2 (by simp [e]),fun e => hc.2 (by simp [e])⟩
omit [DecidableEq W] in
theorem four_from (degrees : ∀ w, 3 ≤ H.degree w) (u : W) :
    ∃ v, ∃ q : H.Walk u v, q.IsPath ∧ 4 ≤ q.support.length := by
  classical
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < (H.neighborFinset u).card by
    rw [H.card_neighborFinset_eq_degree]; have := degrees u; omega)
  have ua := (H.mem_neighborFinset _ _).mp ha
  obtain ⟨b,c,ab,bc,ub,uc,ac⟩ := extend_edge H degrees ua
  let q : H.Walk u c := .cons ua (.cons ab (.cons bc .nil))
  exact ⟨c,q,Walk.IsPath.mk' (by simp [q,ua.ne,ab.ne,bc.ne,ub,uc,ac]),by simp [q]⟩
private theorem last_neighbors (degrees : ∀ w, 3 ≤ H.degree w) {u a b c : W}
    (short : ¬ ∃ v, ∃ q : H.Walk u v, q.IsPath ∧ 5 ≤ q.support.length)
    (ua : H.Adj u a) (ab : H.Adj a b) (bc : H.Adj b c) (ub : u≠b) (uc : u≠c) (ac : a≠c) :
    H.neighborFinset c={u,a,b} := by
  classical
  apply eq_of_subset_of_card_le
  · intro w hw
    by_contra skip
    have cw := (H.mem_neighborFinset _ _).mp hw
    have wu : w≠u := fun e => skip (by simp [e])
    have wa : w≠a := fun e => skip (by simp [e])
    have wb : w≠b := fun e => skip (by simp [e])
    let q : H.Walk u w := .cons ua (.cons ab (.cons bc (.cons cw .nil)))
    exact short ⟨w,q,Walk.IsPath.mk' (by simp [q,ua.ne,ab.ne,bc.ne,cw.ne,ub,uc,ac,wu.symm,wa.symm,wb.symm]),by simp [q]⟩
  · simpa [ua.ne,ub,ab.ne] using degrees c
private theorem tetrahedron (degrees : ∀ w, 3 ≤ H.degree w) {u a : W}
    (short : ¬ ∃ v, ∃ q : H.Walk u v, q.IsPath ∧ 5 ≤ q.support.length) (ua : H.Adj u a) :
    ∃ b c, u≠b ∧ u≠c ∧ a≠b ∧ a≠c ∧ b≠c ∧ H.Adj u b ∧ H.Adj u c ∧
      H.neighborFinset a={u,b,c} ∧ H.neighborFinset b={u,a,c} ∧ H.neighborFinset c={u,a,b} := by
  classical
  obtain ⟨b,c,ab,bc,ub,uc,ac⟩ := extend_edge H degrees ua
  have Nc := last_neighbors H degrees short ua ab bc ub uc ac
  have ucE : H.Adj u c := ((H.mem_neighborFinset _ _).mp (by rw [Nc]; simp)).symm
  have acE : H.Adj a c := ((H.mem_neighborFinset _ _).mp (by rw [Nc]; simp)).symm
  have Nb := last_neighbors H degrees short ua acE bc.symm uc ub ab.ne
  have ubE : H.Adj u b := ((H.mem_neighborFinset _ _).mp (by rw [Nb]; simp)).symm
  have Na := last_neighbors H degrees short ubE bc acE.symm uc ua.ne ab.ne.symm
  exact ⟨b,c,ub,uc,ab.ne,ac,bc.ne,ubE,ucE,Na,Nb,Nc⟩
theorem deficient (connected : H.Connected) (degrees : ∀ w, 3 ≤ H.degree w) (u : W)
    (short : ¬ ∃ v, ∃ q : H.Walk u v, q.IsPath ∧ 5 ≤ q.support.length) :
    (∀ v, v≠u → H.Adj u v ∧ H.degree v=3) ∧ (Fintype.card W=4 ∨ 7 ≤ Fintype.card W) := by
  classical
  let T := insert u (H.neighborFinset u)
  have closed (v : W) (hv : v∈T) (w : W) (edge : H.Adj v w) : w∈T := by
    rcases mem_insert.mp hv with rfl|near
    · exact mem_insert_of_mem ((H.mem_neighborFinset _ _).mpr edge)
    have uv := (H.mem_neighborFinset _ _).mp near
    obtain ⟨b,c,_,_,_,_,_,ub,uc,Nv,_,_⟩ := tetrahedron H degrees short uv
    have hit := (H.mem_neighborFinset _ _).mpr edge
    rw [Nv] at hit
    simp only [mem_insert,mem_singleton] at hit
    rcases hit with rfl|rfl|rfl
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem ((H.mem_neighborFinset _ _).mpr ub)
    · exact mem_insert_of_mem ((H.mem_neighborFinset _ _).mpr uc)
  have universal (v : W) (vu : v≠u) : H.Adj u v := by
    have inside : v∈T := by
      by_contra missing
      obtain ⟨w⟩ := connected u v
      obtain ⟨e,_,ein,eout⟩ := w.exists_boundary_dart (T : Set W) (mem_insert_self _ _) missing
      exact eout (closed _ ein _ e.adj)
    exact (H.mem_neighborFinset _ _).mp ((mem_insert.mp inside).resolve_left vu)
  have deg (v : W) (vu : v≠u) : H.degree v=3 := by
    have edge := universal v vu
    obtain ⟨b,c,ub,uc,_,_,bc,_,_,Nv,_,_⟩ := tetrahedron H degrees short edge
    rw [←H.card_neighborFinset_eq_degree,Nv]
    simp [ub,uc,bc]
  refine ⟨fun v h => ⟨universal v h,deg v h⟩,?_⟩
  by_cases four : Fintype.card W=4
  · exact Or.inl four
  apply Or.inr
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < (H.neighborFinset u).card by
    rw [H.card_neighborFinset_eq_degree]; have := degrees u; omega)
  have ua := (H.mem_neighborFinset _ _).mp ha
  obtain ⟨b,c,ub,uc,ab,ac,bc,_,_,Na,Nb,Nc⟩ := tetrahedron H degrees short ua
  let B : Finset W := {u,a,b,c}
  have size : B.card=4 := by simp [B,ua.ne,ub,uc,ab,ac,bc]
  have lb := B.card_le_univ
  obtain ⟨x,hx⟩ := exists_mem_notMem_of_card_lt_card (s:=B) (t:=univ) (by rw [card_univ]; omega)
  have bound (t : W) (Hxt : H.Adj x t) (ht : t∈B) : t=u := by
    have no : x≠u ∧ x≠a ∧ x≠b ∧ x≠c := by simpa [B] using hx.2
    have hit := (H.mem_neighborFinset _ _).mpr Hxt.symm
    simp only [B,mem_insert,mem_singleton] at ht
    rcases ht with rfl|rfl|rfl|rfl
    · rfl
    all_goals simp_all
  have inc : insert x (H.neighborFinset x \ {u}) ⊆ Bᶜ := by
    intro t ht
    apply mem_compl.mpr
    rcases mem_insert.mp ht with rfl|inN
    · exact hx.2
    · intro tB
      obtain ⟨ed,tu⟩ := mem_sdiff.mp inN
      exact tu (mem_singleton.mpr (bound t ((H.mem_neighborFinset _ _).mp ed) tB))
  have cBound := card_le_card inc
  rw [card_insert_of_notMem (by simp),card_compl,size] at cBound
  have rem := card_sdiff_add_card_inter (H.neighborFinset x) ({u} : Finset W)
  have cap := card_le_card (inter_subset_right (s₁:=H.neighborFinset x) (s₂:={u}))
  rw [card_singleton] at cap
  rw [H.card_neighborFinset_eq_degree] at rem
  have := degrees x
  omega
end Graph189FiveExteriorRoots
end
section
open Finset SimpleGraph
namespace Graph189DenseExteriorOrder
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] {x y : V}
theorem component_internal_degree (p : G.Walk x y) (W : Finset V)
    (outside : ∀ w ∈ W, w ∉ p.support)
    (boundary : ∀ w ∈ W, ∀ v, G.Adj w v → v ∉ W → v ∈ p.support)
    (a : W) : (G.induce (W : Set V)).degree a =
      (G.neighborFinset a.val \ p.support.toFinset).card := by
  classical
  have same : (G.neighborFinset a.val).filter (fun v => v ∈ (W : Set V)) =
      G.neighborFinset a.val \ p.support.toFinset := by
    ext v
    simp only [mem_filter,mem_sdiff,List.mem_toFinset,mem_coe]
    constructor
    · intro h
      exact ⟨h.1,outside v h.2⟩
    · intro h
      refine ⟨h.1,?_⟩
      by_contra no
      exact h.2 (boundary a a.property v ((G.mem_neighborFinset _ _).mp h.1) no)
  rw [Graph189ExteriorDegreeCycle.degree_induce_filter,same]
end Graph189DenseExteriorOrder
end
section
open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FourExterior
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
theorem exterior_component (p : G.Walk a b) {v : V} (off : v∉p.support) :
    ∃ W : Finset V, v∈W ∧ (G.induce (W : Set V)).Connected ∧
      (∀ w∈W, w∉p.support) ∧ (∀ w∈W, ∀ z, G.Adj w z → z∉W → z∈p.support) := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  let H := G.induce (E : Set V)
  let x : E := ⟨v,by simpa [E] using off⟩
  let C := H.connectedComponentMk x
  let emb : E ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let W := C.supp.toFinset.map emb
  have mem {z : V} : z∈W ↔ ∃ t : E, t∈C.supp ∧ t.val=z := by simp [W,emb]
  let f : C.toSimpleGraph →g G.induce (W : Set V) := {
    toFun := fun t => ⟨t.val.val,mem.mpr ⟨t.val,t.property,rfl⟩⟩
    map_rel' := fun h => h }
  refine ⟨W,mem.mpr ⟨x,rfl,rfl⟩,C.connected_toSimpleGraph.map f ?_,?_,?_⟩
  · intro w
    obtain ⟨t,ht,e⟩ := mem.mp w.property
    exact ⟨⟨t,ht⟩,Subtype.ext e⟩
  · intro w hw
    obtain ⟨t,_,rfl⟩ := mem.mp hw
    exact fun h => (mem_compl.mp t.property) (List.mem_toFinset.mpr h)
  · intro w hw z edge absent
    by_contra missing
    let z' : E := ⟨z,by simpa [E] using missing⟩
    obtain ⟨t,ht,rfl⟩ := mem.mp hw
    have near : H.Adj t z' := edge
    exact absent (mem.mpr ⟨z',C.mem_supp_of_adj_mem_supp ht near,rfl⟩)
omit [Fintype V] [DecidableRel G.Adj] in
theorem two_ports (p : G.Walk a b) (hp : p.IsPath)
    (W : Finset V) (outside : ∀ w∈W, w∉p.support)
    (boundary : ∀ w∈W, ∀ z, G.Adj w z → z∉W → z∈p.support)
    (size : 2 ≤ W.card) (space : 2 ≤ p.support.length)
    (cuts : ∀ U : Finset V, U.card<2 → (G.induce {v : V | v∉U}).Connected) :
    ∃ (i j : Fin p.support.length) (u v : W), i < j ∧ u≠v ∧
      G.Adj p.support[i.val] u.val ∧ G.Adj p.support[j.val] v.val := by
  classical
  obtain ⟨A,sub,sz,f,links⟩ := matching_at_component_boundary (G:=G) p.support.toFinset W
    (disjoint_left.mpr (fun _ h hw => outside _ hw (List.mem_toFinset.mp h)))
    (fun w hw z hz edge => List.mem_toFinset.mpr (boundary w hw z edge hz))
    (by rwa [List.toFinset_card_of_nodup hp.support_nodup]) size cuts
  obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp sz
  let X : A := ⟨x,hx⟩
  let Y : A := ⟨y,hy⟩
  have diff : f X ≠ f Y := fun e => ne (congrArg Subtype.val (f.injective e))
  obtain ⟨i,hi,ei⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp (sub hx))
  obtain ⟨j,hj,ej⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp (sub hy))
  let I : Fin p.support.length := ⟨i,hi⟩
  let J : Fin p.support.length := ⟨j,hj⟩
  have eI : G.Adj p.support[I.val] (f X).val := by simpa [I,ei] using links X
  have eJ : G.Adj p.support[J.val] (f Y).val := by simpa [J,ej] using links Y
  have distinct : i≠j := by rintro rfl; exact ne (ei.symm.trans ej)
  rcases lt_or_gt_of_ne distinct with lt|gt
  · exact ⟨I,J,f X,f Y,lt,diff,eI,eJ⟩
  · exact ⟨J,I,f Y,f X,gt,diff.symm,eJ,eI⟩
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem mapped {W : Finset V} (p : G.Walk a b) (outside : ∀ z∈W, z∉p.support)
    {u v : W} (q : (G.induce (W : Set V)).Walk u v) (hq : q.IsPath) :
    ∃ r : G.Walk u.val v.val, r.IsPath ∧ List.Disjoint r.support p.support ∧ r.support.length=q.support.length := by
  let inc := (Embedding.induce (G:=G) (W : Set V)).toHom
  have ds : List.Disjoint (q.map inc).support p.support := by
    rw [Walk.support_map,List.disjoint_left]
    intro z hz
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hz
    exact outside t.val t.property
  have len : (q.map inc).support.length=q.support.length := by rw [Walk.support_map,List.length_map]
  exact ⟨q.map inc,hq.map Subtype.val_injective,ds,len⟩
theorem detour_order (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (W : Finset V) (outside : ∀ z∈W, z∉p.support)
    {i j : Fin p.support.length} {u v : W}
    (ij : i < j) (left : G.Adj p.support[i.val] u.val) (right : G.Adj p.support[j.val] v.val)
    (t d : ℕ)
    (tails : ∀ z : W, ∃ w, ∃ q : (G.induce (W : Set V)).Walk z w, q.IsPath ∧ t ≤ q.support.length)
    (inner : ∃ q : (G.induce (W : Set V)).Walk u v, q.IsPath ∧ d ≤ q.support.length) :
    2*t+d+2 ≤ p.support.length := by
  obtain ⟨_,q,hq,l⟩ := tails u
  obtain ⟨r,hr,dis,len⟩ := mapped p outside q hq
  have rc : List.Disjoint r.reverse.support p.support := by simpa [Walk.support_reverse] using dis
  have f := prefix_of_detour p hp longest i r.reverse hr.reverse rc left.symm
  rw [Walk.support_reverse,List.length_reverse,len] at f
  obtain ⟨_,q',hq',l'⟩ := tails v
  obtain ⟨r',hr',dis',len'⟩ := mapped p outside q' hq'
  have g := suffix_of_detour p hp longest j r' hr' dis' right
  rw [len'] at g
  obtain ⟨q'',hq'',l''⟩ := inner
  obtain ⟨r'',hr'',dis'',len''⟩ := mapped p outside q'' hq''
  have h := interval_of_detour p hp longest i j ij r'' hr'' dis'' left right.symm
  rw [len''] at h
  omega
end Graph189FourExterior
end
section
open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FivePortOrder
variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
theorem three_between (size : Fintype.card W ≤ 7) (degrees : ∀ w, 3 ≤ H.degree w) (u v : W) (ne : u≠v) :
    ∃ q : H.Walk u v, q.IsPath ∧ 3 ≤ q.support.length := by
  classical
  let K := H.deleteEdges {s(u,v)}
  let N (r : W) := insert r (H.neighborFinset r)
  have three (r : W) : 4 ≤ (N r).card := by
    rw [show N r=insert r (H.neighborFinset r) from rfl,card_insert_of_notMem (by simp),H.card_neighborFinset_eq_degree]
    have := degrees r
    omega
  have keep {r z : W} (ru : r≠u) (rv : r≠v) (edge : H.Adj r z) : K.Adj r z :=
    SimpleGraph.deleteEdges_adj.mpr ⟨edge,by simp [ru,rv]⟩
  have oneSide {r : W} (ru : r≠u) (rv : r≠v) (z : W) (hz : z∈N r) : K.Reachable r z := by
    rcases mem_insert.mp hz with rfl|on
    · exact Reachable.rfl
    · exact (keep ru rv ((H.mem_neighborFinset _ _).mp on)).reachable
  obtain ⟨c,hc,cv⟩ := exists_mem_ne (show 1 < (H.neighborFinset u).card by have := degrees u; rw [H.card_neighborFinset_eq_degree]; omega) v
  obtain ⟨d,hd,du⟩ := exists_mem_ne (show 1 < (H.neighborFinset v).card by have := degrees v; rw [H.card_neighborFinset_eq_degree]; omega) u
  have uc := (H.mem_neighborFinset _ _).mp hc
  have vd := (H.mem_neighborFinset _ _).mp hd
  have uc' := (keep uc.ne.symm cv uc.symm).reachable.symm
  have vd' := (keep du vd.ne.symm vd.symm).reachable.symm
  have reach : K.Reachable u v := by
    by_contra no
    have dis : Disjoint (N c) (N d) := disjoint_left.mpr (by
      intro z h₁ h₂
      exact no ((uc'.trans (oneSide uc.ne.symm cv z h₁)).trans
        (vd'.trans (oneSide du vd.ne.symm z h₂)).symm))
    have count := (N c ∪ N d).card_le_univ
    rw [card_union_of_disjoint dis] at count
    have := three c
    have := three d
    omega
  obtain ⟨q,hq⟩ := reach.exists_isPath
  have zero : q.length≠0 := fun eq => ne (Walk.exists_length_eq_zero_iff.mp ⟨q,eq⟩)
  have one : q.length≠1 := by
    intro eq
    have edge := Walk.adj_of_length_eq_one eq
    simp [K] at edge
  let incl : K ≤ H := deleteEdges_le _
  refine ⟨q.mapLe incl,hq.mapLe incl,?_⟩
  rw [Walk.length_support,Walk.length_mapLe]
  omega
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem mapped {W : Finset V} (p : G.Walk a b) (outside : ∀ z∈W, z∉p.support)
    {u v : W} (q : (G.induce (W : Set V)).Walk u v) (hq : q.IsPath) :
    ∃ r : G.Walk u.val v.val, r.IsPath ∧ List.Disjoint r.support p.support ∧ r.support.length=q.support.length := by
  let inc := (Embedding.induce (G:=G) (W : Set V)).toHom
  have ds : List.Disjoint (q.map inc).support p.support := by
    rw [Walk.support_map,List.disjoint_left]
    intro z hz
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hz
    exact outside t.val t.property
  have len : (q.map inc).support.length=q.support.length := by rw [Walk.support_map,List.length_map]
  exact ⟨q.map inc,hq.map Subtype.val_injective,ds,len⟩
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem order (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (W : Finset V) (outside : ∀ z∈W, z∉p.support)
    {i j : Fin p.support.length} {u v : W}
    (ij : i < j) (left : G.Adj p.support[i.val] u.val) (right : G.Adj p.support[j.val] v.val)
    (l s d : ℕ)
    (leftTail : ∃ w, ∃ q : (G.induce (W : Set V)).Walk u w, q.IsPath ∧ l ≤ q.support.length)
    (rightTail : ∃ w, ∃ q : (G.induce (W : Set V)).Walk v w, q.IsPath ∧ s ≤ q.support.length)
    (inner : ∃ q : (G.induce (W : Set V)).Walk u v, q.IsPath ∧ d ≤ q.support.length) :
    l+s+d+2 ≤ p.support.length := by
  obtain ⟨_,q,hq,l⟩ := leftTail
  obtain ⟨r,hr,dis,len⟩ := mapped p outside q hq
  have rc : List.Disjoint r.reverse.support p.support := by simpa [Walk.support_reverse] using dis
  have f := prefix_of_detour p hp longest i r.reverse hr.reverse rc left.symm
  rw [Walk.support_reverse,List.length_reverse,len] at f
  obtain ⟨_,q',hq',l'⟩ := rightTail
  obtain ⟨r',hr',dis',len'⟩ := mapped p outside q' hq'
  have g := suffix_of_detour p hp longest j r' hr' dis' right
  rw [len'] at g
  obtain ⟨q'',hq'',l''⟩ := inner
  obtain ⟨r'',hr'',dis'',len''⟩ := mapped p outside q'' hq''
  have h := interval_of_detour p hp longest i j ij r'' hr'' dis'' left right.symm
  rw [len''] at h
  omega
end Graph189FivePortOrder
end
section
open Finset SimpleGraph Graph189ExteriorGap Graph189FourExterior
namespace Graph189FiveTiedExterior
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
theorem four_omissions (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (cuts : ∀ U : Finset V, U.card<2 → (G.induce {v : V | v∉U}).Connected)
    (minimum : ∀ w, 5 ≤ G.degree w) (quota : ∀ w, (univ.filter (fun t => G.dist w t=2)).card ≤ 5)
    (limit : Fintype.card V ≤ 20) {x : V} (miss : x∉p.support) : (p.support.toFinsetᶜ : Finset V).card=4 := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card=4
  obtain ⟨W,xW,conn,out,bd⟩ := exterior_component p miss
  let H := G.induce (W : Set V)
  have raw (w : V) (off : w∉p.support) : 3 ≤ (G.neighborFinset w \ p.support.toFinset).card := by
    have v := minimum w
    have h := (high_exterior_half p hp maximal off (quota w) v
      (fun t => by have := minimum t; omega) (fun t _ th _ => by have := minimum t; omega)).2
    omega
  have deg (w : W) : 3 ≤ H.degree w := by
    change 3 ≤ (G.induce (W : Set V)).degree w
    rw [Graph189DenseExteriorOrder.component_internal_degree p W out bd]
    exact raw w (out _ w.property)
  have large : 4 ≤ W.card := by
    let x' : W := ⟨x,xW⟩
    have lower := deg x'
    have ub := H.degree_lt_card_verts x'
    change H.degree x' < Fintype.card W at ub
    rw [Fintype.card_coe] at ub
    omega
  have sub : W ⊆ E := fun t ht => by simpa [E] using out t ht
  have le := card_le_card sub
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  have space : 2 ≤ p.support.length := by
    obtain ⟨y,hy⟩ := card_pos.mp (show 0 < (G.neighborFinset x).card by
      rw [G.card_neighborFinset_eq_degree]; have := minimum x; omega)
    have e := (G.mem_neighborFinset _ _).mp hy
    have bound := maximal e.toWalk e.isPath_toWalk
    rw [e.length_toWalk] at bound
    have := p.length_support
    omega
  obtain ⟨i,j,u,v,ij,ne,left,right⟩ := two_ports p hp W out bd (by omega) space cuts
  by_cases small : W.card ≤ 5
  · have routes (s t : W) (diff : s≠t) : ∃ q : H.Walk s t, q.IsPath ∧ W.card ≤ q.support.length := by
      obtain ⟨q,hq⟩ := Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top (by
        intro w y _ _
        change Fintype.card W+1 ≤ H.degree w+H.degree y
        rw [Fintype.card_coe]
        have := deg w
        have := deg y
        omega) (Graph189TerminalLeafClosure.complete_prescribed s t diff)
      exact ⟨q,hq.isPath,by rw [hq.length_support]; change W.card ≤ Fintype.card W; rw [Fintype.card_coe]⟩
    have tails (s : W) : ∃ t, ∃ q : H.Walk s t, q.IsPath ∧ W.card ≤ q.support.length := by
      by_cases eq : s=u
      · exact ⟨v,routes s v (eq ▸ ne)⟩
      · exact ⟨u,routes s u eq⟩
    have length := detour_order p hp maximal W out ij left right W.card W.card tails (routes u v ne)
    have four : W.card=4 := by omega
    by_contra diff
    obtain ⟨z,hz⟩ := card_pos.mp (show 0 < (E \ W).card by rw [card_sdiff_of_subset sub]; omega)
    obtain ⟨zE,zW⟩ := mem_sdiff.mp hz
    let N := G.neighborFinset z \ p.support.toFinset
    have incl : insert z N ⊆ E \ W := by
      intro t ht
      rcases mem_insert.mp ht with rfl|member
      · exact hz
      obtain ⟨edge,off⟩ := mem_sdiff.mp member
      refine mem_sdiff.mpr ⟨mem_compl.mpr off,fun tw => ?_⟩
      have bad := bd t tw z ((G.mem_neighborFinset _ _).mp edge).symm zW
      exact (mem_compl.mp zE) (List.mem_toFinset.mpr bad)
    have bound := card_le_card incl
    have notself : z∉N := fun h => G.irrefl ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp h).1)
    rw [card_insert_of_notMem notself,card_sdiff_of_subset sub] at bound
    have lower : 3 ≤ N.card := raw z (by simpa [E] using zE)
    omega
  have near : ∃ q : H.Walk u v, q.IsPath ∧ 2 ≤ q.support.length := by
    obtain ⟨q,hq⟩ := conn.exists_isPath u v
    have nz : q.length≠0 := fun h => ne (Walk.exists_length_eq_zero_iff.mp ⟨q,h⟩)
    exact ⟨q,hq,by have := q.length_support; omega⟩
  let Good (w : W) := ∃ t, ∃ q : H.Walk w t, q.IsPath ∧ 5 ≤ q.support.length
  have other (s t : W) (st : s≠t) (bad : ¬Good s) : 7 ≤ W.card ∧ Good t := by
    obtain ⟨all,size⟩ := Graph189FiveExteriorRoots.deficient H conn deg s bad
    change Fintype.card W=4 ∨ 7 ≤ Fintype.card W at size
    rw [Fintype.card_coe] at size
    refine ⟨by omega,?_⟩
    by_contra second
    obtain ⟨univT,_⟩ := Graph189FiveExteriorRoots.deficient H conn deg t second
    have nb : H.neighborFinset t=univ.erase t := by
      ext w
      simp only [H.mem_neighborFinset,mem_erase,mem_univ,and_true]
      exact ⟨fun e => e.ne.symm,fun h => (univT w h).1⟩
    have nc := congrArg Finset.card nb
    rw [H.card_neighborFinset_eq_degree,card_erase_of_mem (mem_univ t),card_univ,Fintype.card_coe] at nc
    have th := (all t st.symm).2
    omega
  have far (bound : W.card ≤ 7) := Graph189FivePortOrder.three_between H
    (by change Fintype.card W ≤ 7; rwa [Fintype.card_coe]) deg u v ne
  have rooted := Graph189FiveExteriorRoots.four_from H deg
  by_cases first : Good u
  · by_cases second : Good v
    · have len := Graph189FivePortOrder.order p hp maximal W out ij left right 5 5 2 first second near
      have more := Graph189FivePortOrder.order p hp maximal W out ij left right 5 5 3 first second (far (by omega))
      omega
    · have bs := (other v u ne.symm second).1
      have len := Graph189FivePortOrder.order p hp maximal W out ij left right 5 4 2 first (rooted v) near
      have more := Graph189FivePortOrder.order p hp maximal W out ij left right 5 4 3 first (rooted v) (far (by omega))
      omega
  · obtain ⟨bs,second⟩ := other u v ne first
    have len := Graph189FivePortOrder.order p hp maximal W out ij left right 4 5 2 (rooted u) second near
    have more := Graph189FivePortOrder.order p hp maximal W out ij left right 4 5 3 (rooted u) second (far (by omega))
    omega
end Graph189FiveTiedExterior
end
section
open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189OrdinaryTwoMarks
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
theorem exterior_degree (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {m : ℕ} (room : 3 ≤ m) (minimum : ∀ v, m+1 ≤ G.degree v)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w = 2)).card ≤ m+1)
    (x : (p.support.toFinsetᶜ : Finset V)) :
    m+1 ≤ 2*(G.induce ((p.support.toFinsetᶜ : Finset V) : Set V)).degree x := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  have outside : x.val ∉ p.support := fun h => (mem_compl.mp x.property) (List.mem_toFinset.mpr h)
  have half := (high_exterior_half p hp longest outside (quota _) (minimum _)
    (fun v => by have := minimum v; omega) (fun u _ hu _ => by have := minimum u; omega)).2
  change m+1 ≤ 2*(G.induce (E : Set V)).degree x
  rw [Graph189ExteriorDegreeCycle.degree_induce_filter]
  have same : (G.neighborFinset x.val).filter (fun v => v ∈ (E : Set V)) =
      G.neighborFinset x.val \ p.support.toFinset := by ext v; simp [E]
  rw [same]
  have := minimum x.val
  omega
theorem two_marks (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {m : ℕ} (room : 3 ≤ m) (minimum : ∀ v, m+1 ≤ G.degree v)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w = 2)).card ≤ m+1)
    (order : Fintype.card V ≤ 4*m+4) (size : (p.support.toFinsetᶜ : Finset V).card = m) :
    let E := (p.support.toFinsetᶜ : Finset V)
    (∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian) ∧
      ∃ M : Finset (Fin p.support.length), M.card=2 ∧
        ∀ w∈E, ∀ i : Fin p.support.length, G.Adj p.support[i.val] w ↔ i∈M := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card=m at size
  have out (w : V) (hw : w ∈ E) : w ∉ p.support :=
    fun h => (mem_compl.mp hw) (List.mem_toFinset.mpr h)
  let H := G.induce (E : Set V)
  have routes (x y : E) (ne : x≠y) : ∃ q : H.Walk x y, q.IsHamiltonian := by
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _
      (Graph189TerminalLeafClosure.complete_prescribed x y ne)
    intro u v _ _
    have du := exterior_degree p hp longest room minimum quota u
    have dv := exterior_degree p hp longest room minimum quota v
    change m+1 ≤ 2*H.degree u at du
    change m+1 ≤ 2*H.degree v at dv
    change Fintype.card E+1 ≤ H.degree u + H.degree v
    rw [Fintype.card_coe,size]
    omega
  let N (w : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)
  let A := E.biUnion N
  have rows (w : V) (hw : w ∈ E) : 2 ≤ (N w).card := by
    have d := Graph189DenseExteriorOrder.neighbors_on_path p E
      (fun _ _ v _ no => by simpa [E] using no) hw
    change G.degree w+1 ≤ E.card+(N w).card at d
    have := minimum w
    omega
  have bound : A.card ≤ 2 := by
    by_contra! extra
    obtain ⟨B,n,f,edge⟩ := Graph189ExteriorAttachment.extra_port p E 2 (by omega) rows extra
    have bd := exterior_hamilton_connected_matching p hp longest E (by omega) out routes B
      (card_pos.mp (by omega)) f edge
    rw [n,size] at bd
    omega
  have sub {w : V} (hw : w∈E) : N w ⊆ A := fun _ hi => mem_biUnion.mpr ⟨w,hw,hi⟩
  have same {w : V} (hw : w∈E) : N w=A := eq_of_subset_of_card_le (sub hw) (bound.trans (rows w hw))
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < E.card by omega)
  exact ⟨routes,A,le_antisymm bound ((rows w hw).trans (card_le_card (sub hw))),fun v hv i => by
    rw [← same hv]
    simp [N]⟩
end Graph189OrdinaryTwoMarks
end
section
open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189OrdinaryTwoMarks
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
theorem exclude (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {m : ℕ} (room : 3 ≤ m) (minimum : ∀ v, m+1 ≤ G.degree v)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w = 2)).card ≤ m+1)
    (order : Fintype.card V ≤ 4*m+4) (size : (p.support.toFinsetᶜ : Finset V).card = m) : False := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card=m at size
  obtain ⟨routes,M,card,contacts⟩ := two_marks p hp longest room minimum quota order size
  obtain ⟨u,v,une,pair⟩ := card_eq_two.mp card
  obtain ⟨i,j,ij,pair⟩ : ∃ i j : Fin p.support.length, i < j ∧ M={i,j} := by
    rcases lt_or_gt_of_ne une with h|h
    · exact ⟨u,v,h,pair⟩
    · exact ⟨v,u,h,by simpa [Finset.pair_comm] using pair⟩
  have first : i∈M := by simp [pair]
  have last : j∈M := by simp [pair]
  obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp (show 1 < E.card by omega)
  let X : E := ⟨x,hx⟩
  let Y : E := ⟨y,hy⟩
  have out {w : V} (hw : w∈E) : w∉p.support := by simpa [E] using hw
  obtain ⟨w,hw⟩ := routes X Y (fun h => ne (congrArg Subtype.val h))
  let inc := (Embedding.induce (G:=G) (E : Set V)).toHom
  let q := w.map inc
  have hq : q.IsPath := hw.isPath.map Subtype.val_injective
  have dis : List.Disjoint q.support p.support := by
    apply List.disjoint_left.mpr
    intro z hz
    rw [show q.support=w.support.map inc from Walk.support_map _ _] at hz
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hz
    exact out c.property
  have qlen : q.support.length=m := by
    change (w.map inc).support.length=m
    rw [Walk.support_map,List.length_map,hw.length_support]
    change Fintype.card E=m
    rwa [Fintype.card_coe]
  have touch (t : Fin p.support.length) (ht : t∈M) : G.Adj p.support[t.val] x ∧ G.Adj p.support[t.val] y :=
    ⟨(contacts x hx t).mpr ht,(contacts y hy t).mpr ht⟩
  have front := prefix_of_detour p hp longest i q hq dis (touch i first).2.symm
  have middle := interval_of_detour p hp longest i j ij q hq dis (touch i first).1 (touch j last).2.symm
  have back := suffix_of_detour p hp longest j q hq dis (touch j last).1
  rw [qlen] at front middle back
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  have tight : i.val=m ∨ p.support.length-(j.val+1)=m ∨ j.val-(i.val+1)=m := by omega
  have marks (t : Fin p.support.length) : G.Adj p.support[t.val] x ↔ t.val=i.val ∨ t.val=j.val := by
    rw [contacts x hx t,pair]
    simp only [mem_insert,mem_singleton,Fin.ext_iff]
  have naturalMarks : contactPositions p x = {i.val,j.val} := by
    ext l
    constructor
    · intro h
      obtain ⟨hl,edge⟩ := (mem_contactPositions p x l).mp h
      have value := (marks ⟨l,hl⟩).mp (by simpa only [get_at] using edge)
      simpa only [mem_insert,mem_singleton] using value
    · intro h
      rcases mem_insert.mp h with rfl|other
      · exact (mem_contactPositions p x i.val).mpr ⟨i.isLt,by simpa only [get_at] using (touch i first).1⟩
      obtain rfl := mem_singleton.mp other
      exact (mem_contactPositions p x j.val).mpr ⟨j.isLt,by simpa only [get_at] using (touch j last).1⟩
  have uniform (t : Fin p.support.length) {c d} (r : G.Walk c d) (hr : r.IsPath) (_ : p.support[t.val] ∈ r.support)
      (same : r.length=p.length) (z : V) (hz : z∈r.support) (u : V) (hu : u∉r.support)
      (v : V) (hv : v∉r.support) (edge : G.Adj z u) : G.Adj z v := by
    have count := card_add_card_compl r.support.toFinset
    rw [List.toFinset_card_of_nodup hr.support_nodup] at count
    have len : r.support.length=p.support.length := by rw [r.length_support,same,←p.length_support]
    obtain ⟨_,N,_,common⟩ := two_marks r hr (fun t h => by rw [same]; exact longest t h)
      room minimum quota order (by omega)
    obtain ⟨l,hl,value⟩ := List.mem_iff_getElem.mp hz
    let pos : Fin r.support.length := ⟨l,hl⟩
    rw [←value] at edge ⊢
    exact (common v (by simpa using hv) pos).mpr ((common u (by simpa using hu) pos).mp edge)
  rcases tight with tightLeft|tightRight|tightMiddle
  · have via := interval_exchange_witnesses p hp j M q hq dis touch (uniform j)
      (lo:=0) (hi:=i.val) (by omega) i.isLt.le (by omega) (Or.inr ij.le) (Or.inl rfl)
      (Or.inr ⟨i,first,rfl⟩) (Or.inr i.isLt)
    apply Graph189FourTerminalGap.impossible_of_exact_length p hp (out hx)
      (by omega) (by omega) (by omega) naturalMarks i.isLt.le (by omega : 0+m=i.val) _ via (quota x)
    intro l hl
    have := mem_Ico.mp hl
    omega
  · have via := interval_exchange_witnesses p hp i M q hq dis touch (uniform i)
      (lo:=j.val+1) (hi:=p.support.length) (by omega) le_rfl (by omega) (Or.inl (by omega))
      (Or.inr ⟨j,last,rfl⟩) (Or.inl rfl) (Or.inl (by omega))
    apply Graph189FourTerminalGap.impossible_of_exact_length p hp (out hx)
      (by omega) (by omega) (by omega) naturalMarks le_rfl (by omega : j.val+1+m=p.support.length) _ via (quota x)
    intro l hl
    have := mem_Ico.mp hl
    omega
  · have via := interval_exchange_witnesses p hp i M q hq dis touch (uniform i)
      (lo:=i.val+1) (hi:=j.val) (by omega) j.isLt.le (by omega) (Or.inl (by omega))
      (Or.inr ⟨i,first,rfl⟩) (Or.inr ⟨j,last,rfl⟩) (Or.inl (by omega))
    apply Graph189FourTerminalGap.impossible_of_exact_length p hp (out hx)
      (by omega) (by omega) (by omega) naturalMarks j.isLt.le (by omega : i.val+1+m=j.val) _ via (quota x)
    intro l hl
    have := mem_Ico.mp hl
    omega
end Graph189OrdinaryTwoMarks
end
section
namespace Graph189RootedOneLow
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
private theorem degree_if_confined {r a : V} (P : H.Walk r a) (v : V)
    (mem : v ∈ P.support) (all : ∀ z, H.Adj v z → z∈P.support) : H.degree v < P.support.length := by
  classical
  have cover : H.neighborFinset v ⊆ P.support.toFinset.erase v := by
    intro z hz
    have e := (H.mem_neighborFinset _ _).mp hz
    exact mem_erase.mpr ⟨e.ne.symm,List.mem_toFinset.mpr (all z e)⟩
  have small := card_le_card cover
  rw [H.card_neighborFinset_eq_degree] at small
  have erase := card_erase_add_one (List.mem_toFinset.mpr mem)
  have bound := List.toFinset_card_le P.support
  omega
theorem rooted_path (r : V) {d : ℕ} (start : ∃ b,H.Adj r b)
    (pair : ∀ a b : V, a≠b → d ≤ H.degree a ∨ d ≤ H.degree b) :
    ∃ b, ∃ P : H.Walk r b, P.IsPath ∧ d+1 ≤ P.support.length := by
  classical
  obtain ⟨v,P,hp,maximal⟩ := Graph189RootedPath.exists_rooted_longest H r
  have terminal {a : V} (Q : H.Walk r a) (hq : Q.IsPath) (equal : Q.length=P.length) :
      H.degree a < Q.support.length := by
    apply degree_if_confined (P:=Q) a Q.end_mem_support
    intro t edge
    by_contra no
    have ext := maximal (Q.concat edge) (hq.concat no edge)
    rw [Walk.length_concat,equal] at ext
    omega
  obtain ⟨b,e⟩ := start
  have one := maximal e.toWalk e.isPath_toWalk
  have pos : 0 < P.length := by
    have len1 : 1 ≤ P.length := by simpa using one
    omega
  have nn := Walk.not_nil_iff_lt_length.mpr pos
  have edge := P.adj_penultimate nn
  by_cases high : d ≤ H.degree v
  · exact ⟨v,P,hp,by have := terminal P hp rfl; omega⟩
  have predHigh := (pair v P.penultimate edge.ne.symm).resolve_left high
  by_cases all : ∀ b, H.Adj P.penultimate b → b∈P.support
  · have inside : P.penultimate∈P.support := by
      have h := P.dropLast.end_mem_support
      rw [P.support_dropLast nn] at h
      exact List.mem_of_mem_dropLast h
    have small := degree_if_confined P P.penultimate inside all
    exact ⟨v,P,hp,by omega⟩
  obtain ⟨b,adj⟩ := not_forall.mp all
  have hit : H.Adj P.penultimate b := Classical.byContradiction (fun miss => adj (fun h => (miss h).elim))
  have outside : b∉P.support := fun h => adj (fun _ => h)
  have less : b ≠ v := fun eq => outside (eq.symm ▸ P.end_mem_support)
  have hb := (pair v b less.symm).resolve_left high
  let Q := P.dropLast.concat hit
  have safe : b∉P.dropLast.support := by
    rw [P.support_dropLast nn]
    exact fun h => outside (List.mem_of_mem_dropLast h)
  have hq : Q.IsPath := hp.dropLast.concat safe hit
  have equal : Q.length=P.length := by
    simpa [Q] using P.length_dropLast_add_one nn
  have bound := terminal Q hq equal
  exact ⟨b,Q,hq,by omega⟩
end Graph189RootedOneLow
end
section
open SimpleGraph Finset
namespace Graph189FiveOneLowRoots
variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
private theorem confined {u a b c : W} (short : ¬∃ v, ∃ p : H.Walk u v, p.IsPath ∧ 5 ≤ p.support.length)
    (ua : H.Adj u a) (ab : H.Adj a b) (bc : H.Adj b c) (ub : u≠b) (uc : u≠c) (ac : a≠c) :
    H.neighborFinset c ⊆ {u,a,b} := by
  intro w hw
  by_contra skip
  have cw := (H.mem_neighborFinset _ _).mp hw
  have wu : w≠u := fun e => skip (by simp [e])
  have wa : w≠a := fun e => skip (by simp [e])
  have wb : w≠b := fun e => skip (by simp [e])
  let q : H.Walk u w := .cons ua (.cons ab (.cons bc (.cons cw .nil)))
  exact short ⟨w,q,Walk.IsPath.mk' (by simp [q,ua.ne,ab.ne,bc.ne,cw.ne,ub,uc,ac,wu.symm,wa.symm,wb.symm]),by simp [q]⟩
omit [DecidableEq W] in
private theorem high_neighbor (low : ∀ v, 2 ≤ H.degree v)
    (pair : ∀ a b, a≠b → 3 ≤ H.degree a ∨ 3 ≤ H.degree b) (u : W) :
    ∃ a, H.Adj u a ∧ 3 ≤ H.degree a := by
  obtain ⟨a,ha,b,hb,ab⟩ := one_lt_card.mp (show 1 < (H.neighborFinset u).card from low u)
  rcases pair a b ab with high|high
  · exact ⟨a,(H.mem_neighborFinset _ _).mp ha,high⟩
  · exact ⟨b,(H.mem_neighborFinset _ _).mp hb,high⟩
theorem five_from (low : ∀ v, 2 ≤ H.degree v)
    (pair : ∀ a b, a≠b → 3 ≤ H.degree a ∨ 3 ≤ H.degree b)
    (room : 5 ≤ Fintype.card W) (bound : Fintype.card W ≤ 6) (u : W) :
    ∃ v, ∃ p : H.Walk u v, p.IsPath ∧ 5 ≤ p.support.length := by
  classical
  by_contra short
  obtain ⟨a,ua,highA⟩ := high_neighbor H low pair u
  have rem : 2 ≤ ((H.neighborFinset a).erase u).card := by
    have eq := card_erase_add_one ((H.mem_neighborFinset a u).mpr ua.symm)
    rw [H.card_neighborFinset_eq_degree] at eq
    omega
  obtain ⟨b₁,h₁,b₂,h₂,ne⟩ := one_lt_card.mp rem
  obtain ⟨b,ub,ab,highB⟩ : ∃ b, u≠b ∧ H.Adj a b ∧ 3 ≤ H.degree b := by
    rcases pair _ _ ne with h|h
    · exact ⟨_,(mem_erase.mp h₁).1.symm,(H.mem_neighborFinset _ _).mp (mem_erase.mp h₁).2,h⟩
    · exact ⟨_,(mem_erase.mp h₂).1.symm,(H.mem_neighborFinset _ _).mp (mem_erase.mp h₂).2,h⟩
  obtain ⟨c,hc⟩ := exists_mem_notMem_of_card_lt_card (s:={u,a}) (t:=H.neighborFinset b)
    (by rw [card_pair ua.ne,H.card_neighborFinset_eq_degree]; exact highB)
  have bc := (H.mem_neighborFinset _ _).mp hc.1
  have uc : u≠c := fun e => hc.2 (by simp [e])
  have ac : a≠c := fun e => hc.2 (by simp [e])
  have Nc := confined H short ua ab bc ub uc ac
  have edgeAC : H.Adj a c := by
    by_contra no
    have sub : H.neighborFinset c ⊆ {u,b} := by
      intro v hv
      have h := Nc hv
      simp only [mem_insert,mem_singleton] at h ⊢
      rcases h with rfl|rfl|rfl
      · exact Or.inl rfl
      · exact (no ((H.mem_neighborFinset _ _).mp hv).symm).elim
      · exact Or.inr rfl
    have eq : H.neighborFinset c={u,b} := eq_of_subset_of_card_le sub (by rw [card_pair ub]; exact low c)
    have ucE : H.Adj u c := ((H.mem_neighborFinset _ _).mp (by rw [eq]; simp)).symm
    have Na := confined H short ucE bc.symm ab.symm ub ua.ne ac.symm
    have full : H.neighborFinset a={u,c,b} := eq_of_subset_of_card_le Na (by simpa [uc,ub,bc.ne.symm] using highA)
    exact no ((H.mem_neighborFinset _ _).mp (by rw [full]; simp))
  have Nb := confined H short ua edgeAC bc.symm uc ub ab.ne
  have Nb' : H.neighborFinset b={u,a,c} := eq_of_subset_of_card_le Nb (by simpa [ua.ne,uc,ac] using highB)
  have ubE : H.Adj u b := ((H.mem_neighborFinset _ _).mp (by rw [Nb']; simp)).symm
  have Na := confined H short ubE bc edgeAC.symm uc ua.ne ab.ne.symm
  let T : Finset W := {u,a,b,c}
  have size : T.card=4 := by simp [T,ua.ne,ub,uc,ab.ne,ac,bc.ne]
  have boundary (x : W) (outside : x∉T) (t : W) (edge : H.Adj x t) (inside : t∈T) : t=u := by
    have no : x≠u ∧ x≠a ∧ x≠b ∧ x≠c := by simpa [T] using outside
    have e := (H.mem_neighborFinset _ _).mpr edge.symm
    simp only [T,mem_insert,mem_singleton] at inside
    rcases inside with rfl|rfl|rfl|rfl
    · rfl
    · have := Na e
      simp_all
    · have := Nb e
      simp_all
    · have := Nc e
      simp_all
  have debit (x : W) (ox : x∉T) : H.degree x ≤ Tᶜ.card := by
    have inc : insert x (H.neighborFinset x \ {u}) ⊆ Tᶜ := by
      intro t ht
      apply mem_compl.mpr
      rcases mem_insert.mp ht with rfl|inN
      · exact ox
      · intro hT
        obtain ⟨ed,tu⟩ := mem_sdiff.mp inN
        exact tu (mem_singleton.mpr (boundary x ox t ((H.mem_neighborFinset _ _).mp ed) hT))
    have cnt := card_le_card inc
    rw [card_insert_of_notMem (by simp)] at cnt
    have parts := card_sdiff_add_card_inter (H.neighborFinset x) ({u} : Finset W)
    have cap := card_le_card (inter_subset_right (s₁:=H.neighborFinset x) (s₂:={u}))
    rw [card_singleton] at cap
    rw [H.card_neighborFinset_eq_degree] at parts
    omega
  obtain ⟨x,hx⟩ := card_pos.mp (show 0 < Tᶜ.card by rw [card_compl,size]; omega)
  have dx := debit x (mem_compl.mp hx)
  have lx := low x
  obtain ⟨s,hs,t,ht,st⟩ := one_lt_card.mp (show 1 < Tᶜ.card by omega)
  have d₁ := debit s (mem_compl.mp hs)
  have d₂ := debit t (mem_compl.mp ht)
  have either := pair _ _ st
  rw [card_compl,size] at d₁ d₂
  omega
end Graph189FiveOneLowRoots
end
section
open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveOneLowRoutes
variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
theorem three_between (size : Fintype.card W ≤ 7) (degrees : ∀ w, 2 ≤ H.degree w)
    (pair : ∀ a b, a≠b → 3 ≤ H.degree a ∨ 3 ≤ H.degree b) (u v : W) (ne : u≠v) :
    ∃ q : H.Walk u v, q.IsPath ∧ 3 ≤ q.support.length := by
  classical
  let K := H.deleteEdges {s(u,v)}
  let N (r : W) := insert r (H.neighborFinset r)
  have three (r : W) (high : 3 ≤ H.degree r) : 4 ≤ (N r).card := by
    rw [show N r=insert r (H.neighborFinset r) from rfl,card_insert_of_notMem (by simp),H.card_neighborFinset_eq_degree]
    have := degrees r
    omega
  have keep {r z : W} (ru : r≠u) (rv : r≠v) (edge : H.Adj r z) : K.Adj r z :=
    SimpleGraph.deleteEdges_adj.mpr ⟨edge,by simp [ru,rv]⟩
  have oneSide {r : W} (ru : r≠u) (rv : r≠v) (z : W) (hz : z∈N r) : K.Reachable r z := by
    rcases mem_insert.mp hz with rfl|on
    · exact Reachable.rfl
    · exact (keep ru rv ((H.mem_neighborFinset _ _).mp on)).reachable
  have port (s t : W) : ∃ c ∈ H.neighborFinset s, c≠t ∧ 3 ≤ H.degree c := by
    by_cases high : 3 ≤ H.degree s
    · have lb : 2 ≤ ((H.neighborFinset s).erase t).card := by
        by_cases near : t∈H.neighborFinset s
        · have sz := card_erase_add_one near
          rw [H.card_neighborFinset_eq_degree] at sz
          omega
        · rw [erase_eq_of_notMem near,H.card_neighborFinset_eq_degree]
          omega
      obtain ⟨a,ha,b,hb,ab⟩ := one_lt_card.mp lb
      rcases pair a b ab with qa|qb
      · exact ⟨a,(mem_erase.mp ha).2,(mem_erase.mp ha).1,qa⟩
      · exact ⟨b,(mem_erase.mp hb).2,(mem_erase.mp hb).1,qb⟩
    · obtain ⟨a,ha,ne⟩ := exists_mem_ne (show 1 < (H.neighborFinset s).card from degrees s) t
      exact ⟨a,ha,ne,(pair s a ((H.mem_neighborFinset _ _).mp ha).ne).resolve_left high⟩
  obtain ⟨c,hc,cv,dC⟩ := port u v
  obtain ⟨d,hd,du,dD⟩ := port v u
  have uc := (H.mem_neighborFinset _ _).mp hc
  have vd := (H.mem_neighborFinset _ _).mp hd
  have uc' := (keep uc.ne.symm cv uc.symm).reachable.symm
  have vd' := (keep du vd.ne.symm vd.symm).reachable.symm
  have reach : K.Reachable u v := by
    by_contra no
    have dis : Disjoint (N c) (N d) := disjoint_left.mpr (by
      intro z h₁ h₂
      exact no ((uc'.trans (oneSide uc.ne.symm cv z h₁)).trans
        (vd'.trans (oneSide du vd.ne.symm z h₂)).symm))
    have count := (N c ∪ N d).card_le_univ
    rw [card_union_of_disjoint dis] at count
    have := three c dC
    have := three d dD
    omega
  obtain ⟨q,hq⟩ := reach.exists_isPath
  have zero : q.length≠0 := fun eq => ne (Walk.exists_length_eq_zero_iff.mp ⟨q,eq⟩)
  have one : q.length≠1 := by
    intro eq
    have edge := Walk.adj_of_length_eq_one eq
    simp [K] at edge
  let incl : K ≤ H := deleteEdges_le _
  refine ⟨q.mapLe incl,hq.mapLe incl,?_⟩
  rw [Walk.length_support,Walk.length_mapLe]
  omega
end Graph189FiveOneLowRoutes
end
section
open Finset SimpleGraph Graph189ExteriorGap Graph189FourExterior
namespace Graph189FiveLowComponent
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
theorem classify (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (cuts : ∀ U : Finset V, U.card<2 → (G.induce {v : V | v∉U}).Connected)
    (z : V) (low : 3 ≤ G.degree z) (high : ∀ w, w≠z → 5 ≤ G.degree w)
    (retain : ∀ w, w≠z → w∉p.support → 3 ≤ (G.neighborFinset w \ p.support.toFinset).card)
    (quota : ∀ w, (univ.filter (fun t => G.dist w t=2)).card ≤ 5)
    (limit : Fintype.card V ≤ 19) {x : V} (xz : x≠z) (miss : x∉p.support) :
    (p.support.toFinsetᶜ : Finset V).card=4 ∨
      ((p.support.toFinsetᶜ : Finset V).card=5 ∧ z∉p.support ∧ G.neighborFinset z ⊆ p.support.toFinset) := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card=4 ∨ E.card=5 ∧ _ ∧ _
  obtain ⟨W,xW,conn,out,bd⟩ := exterior_component p miss
  let H := G.induce (W : Set V)
  have deg (w : W) (wz : w.val≠z) : 3 ≤ H.degree w := by
    change 3 ≤ (G.induce (W : Set V)).degree w
    rw [Graph189DenseExteriorOrder.component_internal_degree p W out bd]
    exact retain w wz (out _ w.property)
  have large : 4 ≤ W.card := by
    let x' : W := ⟨x,xW⟩
    have lower := deg x' xz
    have ub := H.degree_lt_card_verts x'
    change H.degree x' < Fintype.card W at ub
    rw [Fintype.card_coe] at ub
    omega
  let _ : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe]; omega)
  have all (w : W) : 2 ≤ H.degree w := by
    by_cases wz : w.val=z
    · obtain ⟨v,hv⟩ := conn.preconnected.exists_adj_of_nontrivial w
      have vz : v.val≠z := fun e => hv.ne (Subtype.ext (wz.trans e.symm))
      have l := half_degree_outside_longest p hp maximal (out w.val w.property) (out v.val v.property)
        (show G.Adj w.val v.val from hv) (quota w.val) (high v.val vz)
      change 2 ≤ (G.induce (W : Set V)).degree w
      rw [Graph189DenseExteriorOrder.component_internal_degree p W out bd]
      have dw : 3 ≤ G.degree w.val := wz ▸ low
      omega
    · exact (deg w wz).trans' (by decide)
  have pair (u v : W) (ne : u≠v) : 3 ≤ H.degree u ∨ 3 ≤ H.degree v := by
    by_cases uz : u.val=z
    · exact Or.inr (deg v (fun e => ne (Subtype.ext (uz.trans e.symm))))
    · exact Or.inl (deg u uz)
  have sub : W ⊆ E := fun t ht => by simpa [E] using out t ht
  have le := card_le_card sub
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  have space : 2 ≤ p.support.length := by
    obtain ⟨y,hy⟩ := card_pos.mp (show 0 < (G.neighborFinset x).card by
      rw [G.card_neighborFinset_eq_degree]; have := high x xz; omega)
    have e := (G.mem_neighborFinset _ _).mp hy
    have bound := maximal e.toWalk e.isPath_toWalk
    rw [e.length_toWalk] at bound
    have := p.length_support
    omega
  obtain ⟨i,j,u,v,ij,ne,left,right⟩ := two_ports p hp W out bd (by omega) space cuts
  have base : ∃ q : H.Walk u v, q.IsPath ∧ 2 ≤ q.support.length := by
    obtain ⟨q,hq⟩ := conn.exists_isPath u v
    have nz : q.length≠0 := fun h => ne (Walk.exists_length_eq_zero_iff.mp ⟨q,h⟩)
    exact ⟨q,hq,by have := q.length_support; omega⟩
  have path4 (w : W) := Graph189RootedOneLow.rooted_path (H:=H) w
    (conn.preconnected.exists_adj_of_nontrivial w) pair
  have bound := detour_order p hp maximal W out ij left right 4 2 path4 base
  have more := Graph189FiveOneLowRoutes.three_between H (by change Fintype.card W ≤ 7; rw [Fintype.card_coe]; omega) all pair u v ne
  have bound' := detour_order p hp maximal W out ij left right 4 3 path4 more
  have four : W.card=4 := by
    by_contra other
    have paths := Graph189FiveOneLowRoots.five_from H all pair
      (by change 5 ≤ Fintype.card W; rw [Fintype.card_coe]; omega)
      (by change Fintype.card W ≤ 6; rw [Fintype.card_coe]; omega)
    have impossible := detour_order p hp maximal W out ij left right 5 3 paths more
    omega
  have clique (s t : W) (ne : s≠t) : H.Adj s t := by
    have full (w : W) (wz : w.val≠z) : H.neighborFinset w=univ.erase w := by
      apply eq_of_subset_of_card_le (fun a h => mem_erase.mpr ⟨((H.mem_neighborFinset _ _).mp h).ne.symm,mem_univ _⟩)
      rw [card_erase_of_mem (mem_univ w),card_univ,H.card_neighborFinset_eq_degree]
      rw [Fintype.card_coe,four]
      exact deg w wz
    by_cases sz : s.val=z
    · have f := full t (fun e => ne (Subtype.ext (sz.trans e.symm)))
      exact ((H.mem_neighborFinset _ _).mp (f ▸ mem_erase.mpr ⟨ne,mem_univ _⟩)).symm
    · exact (H.mem_neighborFinset _ _).mp ((full s sz) ▸ mem_erase.mpr ⟨ne.symm,mem_univ _⟩)
  have top : (⊤ : SimpleGraph W) ≤ H := fun s t e => clique s t e.ne
  obtain ⟨q,hq⟩ := Graph189TerminalLeafClosure.complete_prescribed u v ne
  have inner : ∃ q : H.Walk u v, q.IsPath ∧ 4 ≤ q.support.length := by
    refine ⟨q.mapLe top,hq.isPath.mapLe top,?_⟩
    rw [Walk.length_support,Walk.length_mapLe,←q.length_support,hq.length_support,Fintype.card_coe,four]
  have fullLen := detour_order p hp maximal W out ij left right 4 4 path4 inner
  by_cases equal : E.card=4
  · exact Or.inl equal
  have five : E.card=5 := by omega
  have only (t : V) (tE : t∈E) (tW : t∉W) : t=z := by
    by_contra diff
    let N := G.neighborFinset t \ p.support.toFinset
    have inc : N ⊆ E \ W := by
      intro w hw
      obtain ⟨edge,off⟩ := mem_sdiff.mp hw
      refine mem_sdiff.mpr ⟨mem_compl.mpr off,fun wW => ?_⟩
      have bad := bd w wW t ((G.mem_neighborFinset _ _).mp edge).symm tW
      exact (mem_compl.mp tE) (List.mem_toFinset.mpr bad)
    have highT : 3 ≤ N.card := retain t diff (by simpa [E] using tE)
    have count := card_le_card inc
    rw [card_sdiff_of_subset sub] at count
    omega
  obtain ⟨t,ht⟩ := card_pos.mp (show 0 < (E \ W).card by rw [card_sdiff_of_subset sub]; omega)
  obtain ⟨tE,tW⟩ := mem_sdiff.mp ht
  obtain rfl := only t tE tW
  refine Or.inr ⟨five,by simpa [E] using tE,?_⟩
  intro w hw
  by_contra off
  have wE : w∈E := mem_compl.mpr off
  have edge := (G.mem_neighborFinset _ _).mp hw
  by_cases wW : w∈W
  · exact (mem_compl.mp tE) (List.mem_toFinset.mpr (bd w wW t edge.symm tW))
  · exact edge.ne (only w wE wW).symm
end Graph189FiveLowComponent
end
section
open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveLowMarks
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
theorem data (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (z : V) (degree : ∀ v, v≠z → 5 ≤ G.degree v)
    (retained : ∀ v, v≠z → v∉p.support → 3 ≤ (G.neighborFinset v \ p.support.toFinset).card)
    (order : Fintype.card V ≤ 19) (size : (p.support.toFinsetᶜ : Finset V).card = 4) :
    let E := (p.support.toFinsetᶜ : Finset V)
    (∀ u v : E, u≠v → ∃ q : (G.induce (E : Set V)).Walk u v, q.IsHamiltonian) ∧
    ∃ M : Finset (Fin p.support.length), M.card=2 ∧
      ∀ v∈E, v≠z → ∀ i : Fin p.support.length, G.Adj p.support[i.val] v ↔ i∈M := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  let H := G.induce (E : Set V)
  change E.card=4 at size
  have out {x : V} (hx : x∈E) : x∉p.support := by simpa [E] using hx
  have completeRow {x : V} (hx : x∈E) (nz : x≠z) :
      G.neighborFinset x \ p.support.toFinset=E.erase x := by
    have sub : G.neighborFinset x \ p.support.toFinset ⊆ E.erase x := by
      intro y hy
      obtain ⟨edge,off⟩ := mem_sdiff.mp hy
      exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp edge).ne.symm,mem_compl.mpr off⟩
    apply eq_of_subset_of_card_le sub
    rw [card_erase_of_mem hx,size]
    exact retained x nz (out hx)
  have links {x y : E} (ne : x≠y) (xz : x.val≠z) : H.Adj x y := by
    have inRow : y.val∈G.neighborFinset x.val \ p.support.toFinset := by
      rw [completeRow x.property xz]
      exact mem_erase.mpr ⟨fun e => ne (Subtype.ext e.symm),y.property⟩
    exact (G.mem_neighborFinset _ _).mp (mem_sdiff.mp inRow).1
  have allAdj {x y : E} (ne : x≠y) : H.Adj x y := by
    by_cases xz : x.val=z
    · exact (links ne.symm (fun yz => ne (Subtype.ext (xz.trans yz.symm)))).symm
    · exact links ne xz
  have eqTop : H=⊤ := by
    ext x y
    exact ⟨fun h => h.ne,fun h => allAdj h⟩
  have routes (x y : E) (ne : x≠y) : ∃ q : H.Walk x y, q.IsHamiltonian := by
    rw [eqTop]
    exact Graph189TerminalLeafClosure.complete_prescribed x y ne
  let K := E.erase z
  have ksize : 2 < K.card := by
    by_cases hz : z∈E
    · have cnt := card_erase_add_one hz
      change 2 < (E.erase z).card
      omega
    · simp [K,erase_eq_of_notMem hz,size]
  let N (v : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] v)
  let A := K.biUnion N
  have rows (v : V) (hv : v∈K) : 2 ≤ (N v).card := by
    obtain ⟨vz,vE⟩ := mem_erase.mp hv
    have lower := degree v vz
    have amount := Graph189DenseExteriorOrder.neighbors_on_path p E
      (fun _ _ t _ absent => by simpa [E] using absent) vE
    change G.degree v+1 ≤ E.card+(N v).card at amount
    omega
  have bound : A.card ≤ 2 := by
    by_contra! extra
    obtain ⟨B,n,f,edge⟩ := Graph189ExteriorAttachment.extra_port p K 2 ksize rows extra
    let inc : K ↪ E := ⟨fun w => ⟨w.val,(mem_erase.mp w.property).2⟩,fun _ _ h => Subtype.ext (congrArg (fun w : E => w.val) h)⟩
    have deb := exterior_hamilton_connected_matching p hp maximal E (by omega) (fun _ hw => out hw) routes
      B (card_pos.mp (by omega)) (f.trans inc) (fun i => edge i)
    rw [size,n] at deb
    omega
  have sub (v : V) (hv : v∈K) : N v ⊆ A := fun _ hi => mem_biUnion.mpr ⟨v,hv,hi⟩
  have same (v : V) (hv : v∈K) : N v=A := eq_of_subset_of_card_le (sub v hv) (bound.trans (rows v hv))
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < K.card by omega)
  refine ⟨routes,A,le_antisymm bound ((rows w hw).trans (card_le_card (sub w hw))),?_⟩
  intro v vE vz i
  rw [←same v (mem_erase.mpr ⟨vz,vE⟩)]
  simp [N]
end Graph189FiveLowMarks
end
section
open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveLowExchange
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
theorem no_four_through (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (z : V) (on : z∈p.support) (high : ∀ w, w≠z → 5 ≤ G.degree w)
    (retain : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length=p.length →
      ∀ w, w≠z → w∉r.support → 3 ≤ (G.neighborFinset w \ r.support.toFinset).card)
    (quota : ∀ w, (univ.filter (fun t => G.dist w t=2)).card ≤ 5)
    (order : Fintype.card V ≤ 19) (size : (p.support.toFinsetᶜ : Finset V).card=4) : False := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card=4 at size
  obtain ⟨routes,M,card,links⟩ := Graph189FiveLowMarks.data p hp longest z high (retain p hp rfl) order size
  have contacts (v : V) (hv : v∈E) := links v hv (fun e => (mem_compl.mp hv) (List.mem_toFinset.mpr (e ▸ on)))
  obtain ⟨u,v,une,pair⟩ := card_eq_two.mp card
  obtain ⟨i,j,ij,pair⟩ : ∃ i j : Fin p.support.length, i < j ∧ M={i,j} := by
    rcases lt_or_gt_of_ne une with h|h
    · exact ⟨u,v,h,pair⟩
    · exact ⟨v,u,h,by simpa [Finset.pair_comm] using pair⟩
  have first : i∈M := by simp [pair]
  have last : j∈M := by simp [pair]
  obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp (show 1 < E.card by omega)
  let X : E := ⟨x,hx⟩
  let Y : E := ⟨y,hy⟩
  have out {w : V} (hw : w∈E) : w∉p.support := by simpa [E] using hw
  obtain ⟨w,hw⟩ := routes X Y (fun h => ne (congrArg Subtype.val h))
  let inc := (Embedding.induce (G:=G) (E : Set V)).toHom
  let q := w.map inc
  have hq : q.IsPath := hw.isPath.map Subtype.val_injective
  have dis : List.Disjoint q.support p.support := by
    apply List.disjoint_left.mpr
    intro z hz
    rw [show q.support=w.support.map inc from Walk.support_map _ _] at hz
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hz
    exact out c.property
  have qlen : q.support.length=4 := by
    change (w.map inc).support.length=4
    rw [Walk.support_map,List.length_map,hw.length_support]
    change Fintype.card E=4
    rwa [Fintype.card_coe]
  have touch (t : Fin p.support.length) (ht : t∈M) : G.Adj p.support[t.val] x ∧ G.Adj p.support[t.val] y :=
    ⟨(contacts x hx t).mpr ht,(contacts y hy t).mpr ht⟩
  have front := prefix_of_detour p hp longest i q hq dis (touch i first).2.symm
  have middle := interval_of_detour p hp longest i j ij q hq dis (touch i first).1 (touch j last).2.symm
  have back := suffix_of_detour p hp longest j q hq dis (touch j last).1
  rw [qlen] at front middle back
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  obtain ⟨n,nr,ev⟩ := List.mem_iff_getElem.mp on
  let t : Fin p.support.length := ⟨n,nr⟩
  have tight : (i.val=4 ∧ i.val ≤ n) ∨
      (p.support.length-(j.val+1)=4 ∧ n ≤ j.val) ∨
      (j.val-(i.val+1)=4 ∧ (n < i.val+1 ∨ j.val ≤ n)) := by omega
  have marks (t : Fin p.support.length) : G.Adj p.support[t.val] x ↔ t.val=i.val ∨ t.val=j.val := by
    rw [contacts x hx t,pair]
    simp only [mem_insert,mem_singleton,Fin.ext_iff]
  have naturalMarks : contactPositions p x = {i.val,j.val} := by
    ext l
    constructor
    · intro h
      obtain ⟨hl,edge⟩ := (mem_contactPositions p x l).mp h
      have value := (marks ⟨l,hl⟩).mp (by simpa only [get_at] using edge)
      simpa only [mem_insert,mem_singleton] using value
    · intro h
      rcases mem_insert.mp h with rfl|other
      · exact (mem_contactPositions p x i.val).mpr ⟨i.isLt,by simpa only [get_at] using (touch i first).1⟩
      obtain rfl := mem_singleton.mp other
      exact (mem_contactPositions p x j.val).mpr ⟨j.isLt,by simpa only [get_at] using (touch j last).1⟩
  have uniform {c d} (r : G.Walk c d) (hr : r.IsPath) (keep : p.support[t.val] ∈ r.support)
      (same : r.length=p.length) (w : V) (hw : w∈r.support) (u : V) (hu : u∉r.support)
      (v : V) (hv : v∉r.support) (edge : G.Adj w u) : G.Adj w v := by
    have count := card_add_card_compl r.support.toFinset
    rw [List.toFinset_card_of_nodup hr.support_nodup] at count
    have len : r.support.length=p.support.length := by rw [r.length_support,same,←p.length_support]
    have retained : z∈r.support := by simpa only [t,ev] using keep
    obtain ⟨_,N,_,common⟩ := Graph189FiveLowMarks.data r hr (fun q h => by rw [same]; exact longest q h)
      z high (retain r hr same) order (by omega)
    obtain ⟨l,hl,value⟩ := List.mem_iff_getElem.mp hw
    let pos : Fin r.support.length := ⟨l,hl⟩
    rw [←value] at edge ⊢
    exact (common v (by simpa using hv) (fun e => hv (e ▸ retained)) pos).mpr
      ((common u (by simpa using hu) (fun e => hu (e ▸ retained)) pos).mp edge)
  rcases tight with ⟨tightLeft,safe⟩|⟨tightRight,safe⟩|⟨tightMiddle,safe⟩
  · have via := interval_exchange_witnesses p hp t M q hq dis touch uniform
      (lo:=0) (hi:=i.val) (by omega) i.isLt.le (by omega) (Or.inr safe) (Or.inl rfl)
      (Or.inr ⟨i,first,rfl⟩) (Or.inr i.isLt)
    apply Graph189FourTerminalGap.impossible_of_exact_length p hp (out hx)
      (by omega) (by omega) (by omega) naturalMarks i.isLt.le (by omega : 0+4=i.val) _ via (quota x)
    intro l hl
    have := mem_Ico.mp hl
    omega
  · have via := interval_exchange_witnesses p hp t M q hq dis touch uniform
      (lo:=j.val+1) (hi:=p.support.length) (by omega) le_rfl (by omega) (Or.inl (by change n < j.val+1; omega))
      (Or.inr ⟨j,last,rfl⟩) (Or.inl rfl) (Or.inl (by omega))
    apply Graph189FourTerminalGap.impossible_of_exact_length p hp (out hx)
      (by omega) (by omega) (by omega) naturalMarks le_rfl (by omega : j.val+1+4=p.support.length) _ via (quota x)
    intro l hl
    have := mem_Ico.mp hl
    omega
  · have via := interval_exchange_witnesses p hp t M q hq dis touch uniform
      (lo:=i.val+1) (hi:=j.val) (by omega) j.isLt.le (by omega) safe
      (Or.inr ⟨i,first,rfl⟩) (Or.inr ⟨j,last,rfl⟩) (Or.inl (by omega))
    apply Graph189FourTerminalGap.impossible_of_exact_length p hp (out hx)
      (by omega) (by omega) (by omega) naturalMarks j.isLt.le (by omega : i.val+1+4=j.val) _ via (quota x)
    intro l hl
    have := mem_Ico.mp hl
    omega
end Graph189FiveLowExchange
end
section
open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189FiveLowInsertion
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
theorem isolated (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {z : V} (off : z∉p.support) (all : G.neighborFinset z ⊆ p.support.toFinset)
    (quota : (univ.filter (fun w => G.dist z w=2)).card < 2*G.degree z) :
    ∃ c d, ∃ q : G.Walk c d, q.IsPath ∧ q.length=p.length ∧ z∈q.support := by
  classical
  by_contra no
  have wide (i : ℕ) (hi : i∈contactPositions p z) (j : ℕ) (hj : j∈contactPositions p z) (ij : i < j) : i+3 ≤ j := by
    obtain ⟨ir,ic⟩ := (mem_contactPositions p z i).mp hi
    obtain ⟨jr,jc⟩ := (mem_contactPositions p z j).mp hj
    have spaced := omitted_contact_spacing p hp maximal off ⟨i,ir⟩ ⟨j,jr⟩ ij
      (by simpa [get_at] using ic) (by simpa [get_at] using jc)
    by_contra! small
    have eq : j=i+2 := by change i+2 ≤ j at spaced; omega
    obtain ⟨c,d,q,hq,same,supp⟩ := swap_contact_midpoint p hp off i (eq ▸ jr) ic (eq ▸ jc)
    apply no ⟨c,d,q,hq,same,?_⟩
    apply List.mem_toFinset.mp
    rw [supp]
    exact mem_insert_self _ _
  have costs := double_positions_le_path_shell p hp maximal off wide
  rw [contact_card_neighbors p hp,inter_eq_left.mpr all,G.card_neighborFinset_eq_degree] at costs
  have sub : p.support.toFinset.filter (fun v => G.dist z v=2) ⊆ univ.filter (fun v => G.dist z v=2) :=
    fun w hw => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hw).2⟩
  have := card_le_card sub
  omega
theorem tetrahedron (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {z : V} (old : z∉p.support) (high : ∀ w, w≠z → 5 ≤ G.degree w)
    (retain : ∀ w, w≠z → w∉p.support → 3 ≤ (G.neighborFinset w \ p.support.toFinset).card)
    (order : Fintype.card V ≤ 19) (size : (p.support.toFinsetᶜ : Finset V).card=4) :
    ∃ c d, ∃ q : G.Walk c d, q.IsPath ∧ q.length=p.length ∧ z∈q.support := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card=4 at size
  obtain ⟨routes,M,card,links⟩ := Graph189FiveLowMarks.data p hp maximal z high retain order size
  obtain ⟨u,v,une,pair⟩ := card_eq_two.mp card
  obtain ⟨i,j,ij,pair⟩ : ∃ i j : Fin p.support.length, i < j ∧ M={i,j} := by
    rcases lt_or_gt_of_ne une with h|h
    · exact ⟨u,v,h,pair⟩
    · exact ⟨v,u,h,by simpa [Finset.pair_comm] using pair⟩
  have first : i∈M := by simp [pair]
  have last : j∈M := by simp [pair]
  have zE : z∈E := by simpa [E] using old
  have many := card_erase_add_one zE
  obtain ⟨x,hx,y,hy,xy⟩ := one_lt_card.mp (show 1 < (E.erase z).card by omega)
  obtain ⟨xz,xE⟩ := mem_erase.mp hx
  obtain ⟨yz,yE⟩ := mem_erase.mp hy
  have get {x y : V} (hx : x∈E) (hy : y∈E) (ne : x≠y) :
      ∃ q : G.Walk x y, q.IsPath ∧ List.Disjoint q.support p.support ∧ q.support.length=4 := by
    let X : E := ⟨x,hx⟩
    let Y : E := ⟨y,hy⟩
    obtain ⟨r,hr⟩ := routes X Y (fun eq => ne (congrArg Subtype.val eq))
    obtain ⟨q,hq,dis,lower⟩ := route_of_induced_hamilton p E (fun _ hw => by simpa [E] using hw) hr
    have sub : q.support.toFinset ⊆ E := by
      intro t ht
      apply mem_compl.mpr
      exact fun on => (List.disjoint_left.mp dis (List.mem_toFinset.mp ht)) (List.mem_toFinset.mp on)
    have ub := card_le_card sub
    rw [List.toFinset_card_of_nodup hq.support_nodup] at ub
    exact ⟨q,hq,dis,by omega⟩
  obtain ⟨q,hq,dis,qlen⟩ := get xE yE xy
  have xi := (links x xE xz i).mpr first
  have yi := (links y yE yz i).mpr first
  have xj := (links x xE xz j).mpr last
  have yj := (links y yE yz j).mpr last
  have front := prefix_of_detour p hp maximal i q hq dis yi.symm
  have middle := interval_of_detour p hp maximal i j ij q hq dis xi yj.symm
  have back := suffix_of_detour p hp maximal j q hq dis xj
  rw [qlen] at front middle back
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  have tight : i.val=4 ∨ p.support.length=j.val+1+4 := by omega
  rcases tight with L|R
  · obtain ⟨s,hs,sd,sl⟩ := get zE xE xz.symm
    obtain ⟨c,d,r,hr,supp⟩ := splice_support p hp [] (p.support.take i.val) (p.support.drop i.val)
      (by simp) s hs sd (by simp) (by
        intro v hv
        have head : (p.support.drop i.val).head?=some p.support[i.val] := by simp [List.head?_drop]
        have value : p.support[i.val]=v := by simpa only [head,Option.mem_def,Option.some.injEq] using hv
        exact value ▸ xi.symm)
    have len := congrArg List.length supp
    simp only [List.length_append,List.length_nil,List.length_drop,sl] at len
    refine ⟨c,d,r,hr,by have := p.length_support; have := r.length_support; omega,?_⟩
    rw [supp,List.nil_append,List.mem_append]
    exact Or.inl s.start_mem_support
  · obtain ⟨s,hs,sd,sl⟩ := get xE zE xz
    obtain ⟨c,d,r,hr,supp⟩ := splice_support p hp (p.support.take (j.val+1)) (p.support.drop (j.val+1)) []
      (by simp) s hs sd (by
        intro v hv
        have last' : (p.support.take (j.val+1)).getLast?=some p.support[j.val] :=
          (congrArg List.getLast? (List.take_succ_eq_append_getElem j.isLt)).trans List.getLast?_concat
        have value : p.support[j.val]=v := by simpa only [last',Option.mem_def,Option.some.injEq] using hv
        exact value ▸ xj) (by simp)
    have len := congrArg List.length supp
    simp only [List.length_append,List.length_nil,List.length_take,sl] at len
    refine ⟨c,d,r,hr,by have := p.length_support; have := r.length_support; omega,?_⟩
    rw [supp,List.append_nil,List.mem_append]
    exact Or.inr s.end_mem_support
end Graph189FiveLowInsertion
end
section
open SimpleGraph Finset Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189FiveHighMinimum
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem low_traceable
    (cuts : ∀ U : Finset V, U.card<2 → (G.induce {v : V | v∉U}).Connected)
    (z : V) (low : 3 ≤ G.degree z) (high : ∀ w, w≠z → 5 ≤ G.degree w)
    (quota : ∀ w, (univ.filter (fun t => G.dist w t=2)).card ≤ 5) (order : Fintype.card V ≤ 19) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨a,b,p,hp,longest⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  have uniq (u v : V) (hu : G.degree u<5) (hv : G.degree v<5) : u=v := by
    have uz : u=z := by by_contra no; have := high u no; omega
    have vz : v=z := by by_contra no; have := high v no; omega
    exact uz.trans vz.symm
  have minD (w : V) : 3 ≤ G.degree w := by
    by_cases e : w=z
    · exact e ▸ low
    · exact (high w e).trans' (by decide)
  have raw {c d} (r : G.Walk c d) (hr : r.IsPath) (len : r.length=p.length)
      (w : V) (ne : w≠z) (absent : w∉r.support) : 3 ≤ (G.neighborFinset w \ r.support.toFinset).card := by
    have h := high w ne
    have half := (high_exterior_half r hr (fun q hq => len ▸ longest q hq) absent (quota w) h minD uniq).2
    omega
  have through {c d} (r : G.Walk c d) (hr : r.IsPath) (len : r.length=p.length) (inside : z∈r.support) :
      r.IsHamiltonian := by
    apply hr.isHamiltonian_of_mem
    intro w
    by_contra off
    have wz : w≠z := fun e => off (e ▸ inside)
    have mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ r.length :=
      fun q hq => len ▸ longest q hq
    rcases Graph189FiveLowComponent.classify r hr mx cuts z low high (raw r hr len) quota order wz off with four|solo
    · exact Graph189FiveLowExchange.no_four_through r hr mx z inside high
        (fun q hq same => raw q hq (same.trans len)) quota order four
    · exact solo.2.1 inside
  by_cases on : z∈p.support
  · exact ⟨a,b,p,through p hp rfl on⟩
  have charge := quota z
  have insertZ (all : G.neighborFinset z ⊆ p.support.toFinset) :
      ∃ c d, ∃ q : G.Walk c d, q.IsPath ∧ q.length=p.length ∧ z∈q.support :=
    Graph189FiveLowInsertion.isolated p hp longest on all (by omega)
  suffices h : ∃ c d, ∃ q : G.Walk c d, q.IsPath ∧ q.length=p.length ∧ z∈q.support by
    obtain ⟨c,d,q,hq,l,keep⟩ := h
    exact ⟨c,d,q,through q hq l keep⟩
  by_cases other : ∃ w, w≠z ∧ w∉p.support
  · obtain ⟨w,wz,off⟩ := other
    rcases Graph189FiveLowComponent.classify p hp longest cuts z low high (raw p hp rfl) quota order wz off with four|solo
    · exact Graph189FiveLowInsertion.tetrahedron p hp longest on high (raw p hp rfl) order four
    · exact insertZ solo.2.2
  · apply insertZ
    intro w hw
    apply List.mem_toFinset.mpr
    by_contra absent
    exact other ⟨w,((G.mem_neighborFinset _ _).mp hw).ne.symm,absent⟩
end Graph189FiveHighMinimum
end
section
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ModerateForDesk
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem five (hc : G.Connected) (point : ∀v,G.distEven v≤1+G.secondSmallestDegree)
    (conn : 2 ≤ G.vertexConnectivity) (k5 : G.secondSmallestDegree=5)
    (lower : 2*G.secondSmallestDegree+6 < Fintype.card V)
    (upper : Fintype.card V≤3*G.secondSmallestDegree+2) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have fd := Graph189CutSides.connectivity_le_degree (G:=G) z
  have localCap (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by simpa only [Nat.add_comm] using point v
  have three : 3 ≤ G.degree z := by
    by_contra! low
    have bd := Graph189LayerCutoff.order_of_small_degree G hc z _ localCap (by omega)
    rw [k5,show G.degree z=2 by omega] at bd
    omega
  have quota (v : V) : (univ.filter (fun w => G.dist v w=2)).card≤5 := by
    let T := univ.filter (fun w => G.dist v w=2)
    have no : v∉T := by simp [T]
    have sub : insert v T⊆univ.filter (fun w => Even (G.dist v w)) := by
      intro w hw
      rcases mem_insert.mp hw with rfl|h
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp h).2]; decide⟩
    have count := card_le_card sub
    rw [card_insert_of_notMem no] at count
    change T.card+1 ≤ G.distEven v at count
    change T.card≤5
    have := point v
    omega
  have cuts (U : Finset V) (h : U.card<2) := Graph189CutSides.connected_after_smaller_deletion (G:=G) U (h.trans_le conn)
  by_cases low : G.degree z<5
  · exact Graph189FiveHighMinimum.low_traceable cuts z three (fun x ne => by
      have := degree_pair (G:=G) x z ne
      omega) quota (by omega)
  have min (v : V) : 5 ≤ G.degree v := by have := G.minDegree_le_degree v; omega
  obtain ⟨a,b,p,hp,mx⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  refine ⟨a,b,p,hp.isHamiltonian_of_mem (fun x => ?_)⟩
  by_contra miss
  have size := Graph189FiveTiedExterior.four_omissions p hp mx cuts min quota (by omega) miss
  exact Graph189OrdinaryTwoMarks.exclude p hp mx (m:=4) (by decide) min quota (by omega) size
end Graph189ModerateForDesk
end
section
open SimpleGraph Finset
namespace Graph189ModerateSplitProofs
theorem five : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1.H2 := by
  intro V _ _ _ G _ hc point lower uncut upper wide degree
  have conn := Graph189ParentConnectivity.two_of_deletions hc (by omega) uncut
  exact Graph189ModerateForDesk.five hc point conn degree wide upper
end Graph189ModerateSplitProofs
end
theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1.H2 := Graph189ModerateSplitProofs.five
