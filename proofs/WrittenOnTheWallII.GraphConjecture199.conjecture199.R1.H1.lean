import OMAReductions.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1

/-!
A connected graph with vertex connectivity at least two and no induced tree
on five vertices has a Hamiltonian path. The longest-path argument supplies
an independent set of size four. According to whether its vertices have
common neighbors, the proof assembles paths through their neighborhoods or
through a maximal set of vertices at pairwise distance at least three.
-/

open SimpleGraph
open scoped BigOperators
namespace OMA.ConnectivityTwo
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma diameter_tree [Nonempty V] (hc : G.Connected) :
    G.diam + 1 ≤ G.largestInducedTreeSize := by
  obtain ⟨x,y,he⟩ := G.exists_dist_eq_diam
  obtain ⟨p,hp,hshort⟩ := hc.exists_path_of_dist x y
  have hT := p.induce_support_isTree_of_length_eq_dist hshort
  have h := card_le_largestInducedTreeSize hT
  rw [List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support, hshort, he] at h
  exact h

lemma induced_star (v : V) (Q : Finset V) (hI : G.IsIndepSet (Q : Set V))
    (hn : ∀ x ∈ Q, G.Adj v x) : (G.induce ((insert v Q : Finset V) : Set V)).IsTree := by
  induction Q using Finset.induction_on with
  | empty =>
    have he : (({v} : Finset V) : Set V) = {v} := by simp
    simp only [Finset.insert_empty]
    rw [he]
    letI : Nonempty ↥({v} : Set V) := ⟨⟨v,by simp⟩⟩
    letI : Subsingleton ↥({v} : Set V) := ⟨fun a b => Subtype.ext
      ((Set.mem_singleton_iff.mp a.property).trans (Set.mem_singleton_iff.mp b.property).symm)⟩
    exact IsTree.of_subsingleton
  | @insert x Q hx ih =>
    have hvx := hn x (Finset.mem_insert_self x Q)
    have hI' : G.IsIndepSet (Q : Set V) := fun _ ha _ hb hne =>
      hI (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hb) hne
    have hT := ih hI' (fun y hy => hn y (Finset.mem_insert_of_mem hy))
    rw [Finset.insert_comm]
    apply hT.induce_insert_of_unique_adj (by simpa [hvx.ne.symm] using hx) (Finset.mem_insert_self _ _) hvx.symm
    intro y hy hxy
    rcases Finset.mem_insert.mp hy with h | h
    · exact h
    · exact False.elim (hI (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem h) hxy.ne hxy)

lemma independent_neighbors_size (v : V) (Q : Finset V) (hI : G.IsIndepSet (Q : Set V))
    (hn : ∀ x ∈ Q, G.Adj v x) : Q.card+1 ≤ G.largestInducedTreeSize := by
  have h := card_le_largestInducedTreeSize (induced_star v Q hI hn)
  have hv : v ∉ Q := fun hv => (hn v hv).ne rfl
  simpa only [Finset.card_insert_of_notMem hv] using h


lemma induced_path_on_four {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hac : ¬G.Adj a c) (hbd : ¬G.Adj b d) (had : ¬G.Adj a d)
    (hneac : a ≠ c) (hnebd : b ≠ d) (hnead : a ≠ d) : (G.induce (↑({d,b,a,c} : Finset V) : Set V)).IsTree := by
  let Q : Finset V := {a,c}
  have hI : G.IsIndepSet (Q : Set V) := by
    intro x hx y hy hxy h
    simp [Q] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hxy rfl
    · exact hac h
    · exact hac h.symm
    · exact hxy rfl
  have hN (x : V) (hx : x ∈ Q) : G.Adj b x := by
    rcases (show x = a ∨ x = c by simpa [Q] using hx) with rfl | rfl
    · exact hab.symm
    · exact hbc
  have hT := induced_star b Q hI hN
  have hd : d ∉ insert b Q := by simp [Q,Ne.symm hnebd,Ne.symm hnead,Ne.symm hcd.ne]
  have hT' := hT.induce_insert_of_unique_adj hd
    (show c ∈ insert b Q by simp [Q]) hcd.symm (by
      intro y hy h
      simp [Q] at hy
      rcases hy with rfl | rfl | rfl
      · exact False.elim (hbd h.symm)
      · exact False.elim (had h.symm)
      · rfl)
  exact hT'


lemma getD_zero (l : List V) (hl : l ≠ []) (d : V) : l.getD 0 d = l.head hl := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => rfl

lemma getD_last (l : List V) (hl : l ≠ []) (d : V) : l.getD (l.length - 1) d = l.getLast hl := by
  rw [List.getLast_eq_getElem, List.getD_eq_getElem]

lemma detour_longer (A B D R : List V) (hB : B ≠ []) (hR : R ≠ [])
    (hc : (A++B++D).IsChain G.Adj) (hnd : (A++B++D).Nodup) (hrc : R.IsChain G.Adj)
    (hrn : R.Nodup) (hout : ∀ x ∈ R, x ∉ A++B++D)
    (joinAR : ∀ a ∈ A.getLast?, ∀ r ∈ R.head?, G.Adj a r)
    (joinRB : ∀ r ∈ R.getLast?, ∀ b ∈ B.getLast?, G.Adj r b)
    (joinBD : ∀ b ∈ B.head?, ∀ d ∈ D.head?, G.Adj b d) :
    ∃ l : List V, l.Nodup ∧ l.IsChain G.Adj ∧ (A++B++D).length < l.length := by
  have hAB := (List.isChain_append.mp hc).1
  have hA := (List.isChain_append.mp hAB).1
  have hBc := (List.isChain_append.mp hAB).2.1
  have hDc := (List.isChain_append.mp hc).2.1
  have hAR := List.isChain_append.mpr ⟨hA,hrc,joinAR⟩
  have hrev : B.reverse.IsChain G.Adj := by
    rw [List.isChain_reverse]
    exact hBc.imp (fun _ _ h => h.symm)
  have hRB : (A++R++B.reverse).IsChain G.Adj := by
    refine List.isChain_append.mpr ⟨hAR,hrev,?_⟩
    rw [List.getLast?_append_of_ne_nil _ hR,List.head?_reverse]
    exact joinRB
  have hfinal : (A++R++B.reverse++D).IsChain G.Adj := by
    refine List.isChain_append.mpr ⟨hRB,hDc,?_⟩
    rw [List.getLast?_append_of_ne_nil _ (by simpa using hB),List.getLast?_reverse]
    exact joinBD
  have hperm : (A++R++B.reverse++D).Perm (A++B++D++R) := by
    have h₁ : (A++R++B.reverse++D).Perm (A++R++B++D) :=
      ((List.reverse_perm B).append_left (A++R)).append_right D
    have h₂ : (A++R++B++D).Perm (A++B++D++R) := by
      simpa only [List.append_assoc] using (List.perm_append_comm (l₁ := R) (l₂ := B++D)).append_left A
    exact h₁.trans h₂
  have hnd' : (A++B++D++R).Nodup := by
    refine List.nodup_append.mpr ⟨hnd,hrn,?_⟩
    intro x hx y hy h
    exact hout y hy (h ▸ hx)
  exact ⟨_,hperm.nodup_iff.mpr hnd',hfinal,by
    have hpos := List.length_pos_iff_ne_nil.mpr hR
    simp only [List.length_append,List.length_reverse]
    omega⟩

lemma subsegments (l : List V) (d : V) (i j : ℕ) (hij : i < j) (hj : j < l.length) :
    let A := l.take (i+1)
    let B := (l.drop (i+1)).take (j-i)
    let D := l.drop (j+1)
    A ++ B ++ D = l ∧ A.getLast? = some (l.getD i d) ∧
      B.head? = some (l.getD (i+1) d) ∧ B.getLast? = some (l.getD j d) ∧
      D.head? = l[j+1]? := by
  dsimp only
  have h1 : i < l.length := by omega
  have h2 : i+1 < l.length := by omega
  have hmid : 0 < j-i := by omega
  constructor
  · rw [List.append_assoc,← show i+1+(j-i) = j+1 by omega,List.drop_take_append_drop,List.take_append_drop]
  constructor
  · rw [List.getLast?_take,List.getD_eq_getElem _ _ h1]
    simp [List.getElem?_eq_getElem h1]
  constructor
  · rw [List.head?_take,List.head?_drop,List.getD_eq_getElem _ _ h2]
    simp [hmid.ne',List.getElem?_eq_getElem h2]
  constructor
  · rw [List.getLast?_take]
    simp only [List.length_drop,List.getElem?_drop]
    have hm : min (j-i) (l.length-(i+1)) = j-i := Nat.min_eq_left (by omega)
    rw [if_neg hmid.ne',show i+1+(j-i-1) = j by omega,List.getElem?_eq_getElem hj,List.getD_eq_getElem _ _ hj]
    rfl
  · exact List.head?_drop

lemma large_independent_on_longest [Nontrivial V]
    (l : List V) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ p : List V, p.Nodup → p.IsChain G.Adj → p.length ≤ l.length)
    (w0 : V) (hw0 : w0 ∉ l) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ G.vertexConnectivity + 2 ≤ I.card := by
  classical
  let q := l.head hne
  let z := l.getLast hne
  let v (i : ℕ) := l.getD i q
  let m := l.length
  have hm : 0 < m := List.length_pos_iff_ne_nil.mpr hne
  have hv0 : v 0 = q := getD_zero _ hne _
  have hvz : v (m-1) = z := getD_last _ hne _
  have vmem (i : ℕ) (hi : i < m) : v i ∈ l := by
    dsimp only [v]
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _
  have vinj (i j : ℕ) (hi : i < m) (hj : j < m) (he : v i = v j) : i=j := by
    dsimp only [v] at he
    rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj] at he
    exact hnd.getElem_inj_iff.mp he
  have hfirst (x : V) (hqx : G.Adj q x) : x ∈ l := by
    by_contra hx
    have h := hmax (x::l) (List.nodup_cons.mpr ⟨hx,hnd⟩)
      (List.IsChain.cons_of_ne_nil hne hch hqx.symm)
    simp at h
  have hlast (x : V) (hzx : G.Adj z x) : x ∈ l := by
    by_contra hx
    have hrev : l.reverse.IsChain G.Adj := by
      rw [List.isChain_reverse]; exact hch.imp (fun _ _ h => h.symm)
    have hr : l.reverse ≠ [] := by simpa using hne
    have hadj : G.Adj x (l.reverse.head hr) := by simpa [z] using hzx.symm
    have h := hmax (x::l.reverse) (List.nodup_cons.mpr ⟨by simpa using hx,(List.reverse_perm l).nodup_iff.mpr hnd⟩)
      (List.IsChain.cons_of_ne_nil hr hrev hadj)
    simp at h
  let W := {x : V // x ∉ l}
  let H : SimpleGraph W := G.induce {x | x ∉ l}
  let c := H.connectedComponentMk ⟨w0,hw0⟩
  let U (x : V) := ∃ hx : x ∉ l, H.connectedComponentMk ⟨x,hx⟩ = c
  have hu0 : U w0 := ⟨hw0,rfl⟩
  have unite (a b : V) (ha : U a) (hb : U b) : ∃ R : List V, R.Nodup ∧ R.IsChain G.Adj ∧
      R.head? = some a ∧ R.getLast? = some b ∧ ∀ x ∈ R, x ∉ l := by
    obtain ⟨ha,ea⟩ := ha
    obtain ⟨hb,eb⟩ := hb
    have hr : H.Reachable ⟨a,ha⟩ ⟨b,hb⟩ := ConnectedComponent.eq.mp (ea.trans eb.symm)
    obtain ⟨p⟩ := hr
    let f : H ↪g G := SimpleGraph.Embedding.induce {x | x ∉ l}
    let t := p.toPath.val
    let r := t.map f.toHom
    have ht : t.IsPath := p.toPath.property
    have hp : r.IsPath := ht.map f.injective
    refine ⟨r.support,hp.support_nodup,r.isChain_adj_support,by rw [List.head?_eq_some_head r.support_ne_nil,r.head_support]; rfl,
      by rw [List.getLast?_eq_some_getLast r.support_ne_nil,r.getLast_support]; rfl,?_⟩
    intro x hx
    change x ∈ (t.map f.toHom).support at hx
    rw [Walk.support_map] at hx
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
    exact u.property
  let X := (Finset.range (m-1)).filter (fun i => ∃ x, U x ∧ G.Adj (v i) x)
  have Xbound {i : ℕ} (hi : i ∈ X) : i < m-1 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have Xadj {i : ℕ} (hi : i ∈ X) : ∃ x, U x ∧ G.Adj (v i) x := (Finset.mem_filter.mp hi).2
  have cross {i j : ℕ} (hi : i ∈ X) (hj : j ∈ X) (hij : i < j) : ¬G.Adj (v (i+1)) (v (j+1)) := by
    intro hadj
    obtain ⟨x,hx,hix⟩ := Xadj hi
    obtain ⟨y,hy,hjy⟩ := Xadj hj
    obtain ⟨R,hrn,hrc,hrh,hrt,hro⟩ := unite x y hx hy
    obtain ⟨hs,hA,hB,hB',hD⟩ := subsegments l q i j hij (by have := Xbound hj; omega)
    have hj1 : j+1 < l.length := by have := Xbound hj; dsimp only [m] at *; omega
    rw [List.getElem?_eq_getElem hj1] at hD
    have hrne : R ≠ [] := by intro h; simp [h] at hrh
    have hbne : (l.drop (i+1)).take (j-i) ≠ [] := by intro h; simp [h] at hB
    have jAR : ∀ a ∈ (l.take (i+1)).getLast?, ∀ r ∈ R.head?, G.Adj a r := by
      intro a ha r hr
      rw [hA] at ha
      rw [hrh] at hr
      simp only [Option.mem_some_iff] at ha hr
      subst a; subst r
      exact hix
    have jRB : ∀ r ∈ R.getLast?, ∀ b ∈ ((l.drop (i+1)).take (j-i)).getLast?, G.Adj r b := by
      intro r hr b hb
      rw [hrt] at hr
      rw [hB'] at hb
      simp only [Option.mem_some_iff] at hr hb
      subst r; subst b
      exact hjy.symm
    have jBD : ∀ b ∈ ((l.drop (i+1)).take (j-i)).head?, ∀ d ∈ (l.drop (j+1)).head?, G.Adj b d := by
      rw [hB,hD]
      intro b hb d hd
      simp only [Option.mem_some_iff] at hb hd
      subst b; subst d
      simpa only [v,List.getD_eq_getElem _ _ hj1] using hadj
    obtain ⟨L,hLn,hLc,hLL⟩ := detour_longer _ _ _ _ hbne hrne (hs.symm ▸ hch) (hs.symm ▸ hnd)
      hrc hrn (hs.symm ▸ hro) jAR jRB jBD
    have h := hmax L hLn hLc
    rw [hs] at hLL
    omega

  have no_front {i : ℕ} (hi : i ∈ X) : ¬G.Adj q (v (i+1)) := by
    intro hh
    obtain ⟨x,⟨hx,_⟩,hax⟩ := Xadj hi
    have hi1 : i < l.length := by have := Xbound hi; dsimp only [m] at *; omega
    have hi2 : i+1 < l.length := by have := Xbound hi; dsimp only [m] at *; omega
    let B := l.take (i+1)
    let D := l.drop (i+1)
    have hs : ([] : List V) ++ B ++ D = l := by simp [B,D]
    have hhB : B.head? = some q := by
      rw [show B.head? = _ from List.head?_take]
      simp [List.head?_eq_some_head hne,q]
    have htB : B.getLast? = some (v i) := by
      rw [show B.getLast? = _ from List.getLast?_take]
      simp [v,List.getD_eq_getElem _ _ hi1,List.getElem?_eq_getElem hi1]
    have hhD : D.head? = some (v (i+1)) := by
      rw [show D.head? = _ from List.head?_drop]
      simp [v,List.getD_eq_getElem _ _ hi2,List.getElem?_eq_getElem hi2]
    have hBne : B ≠ [] := by intro he; simp [he] at hhB
    have jRB : ∀ r ∈ [x].getLast?, ∀ b ∈ B.getLast?, G.Adj r b := by
      simpa [htB] using hax.symm
    have jBD : ∀ b ∈ B.head?, ∀ d ∈ D.head?, G.Adj b d := by simpa [hhB,hhD] using hh
    obtain ⟨L,hLn,hLc,hLL⟩ := detour_longer [] B D [x] hBne (by simp) (hs.symm ▸ hch)
      (hs.symm ▸ hnd) (List.isChain_singleton _) (List.nodup_singleton _) (by
        intro a ha
        simp only [List.mem_singleton] at ha
        subst a
        rw [hs]
        exact hx)
      (by simp) jRB jBD
    rw [hs] at hLL
    exact (not_lt_of_ge (hmax _ hLn hLc)) hLL
  have no_external {i : ℕ} (hi : i ∈ X) {x : V} (hx : U x) : ¬G.Adj (v (i+1)) x := by
    intro he
    have hir := Xbound hi
    by_cases hlast' : i+1 = m-1
    · rw [hlast',hvz] at he
      exact hx.choose (hlast _ he)
    · have hi' : i+1 ∈ X := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega),x,hx,he⟩
      have h2 : i+1+1 < l.length := by dsimp only [m] at *; omega
      have had := List.isChain_iff_getElem.mp hch (i+1) h2
      apply cross hi hi' (by omega)
      simpa only [v,List.getD_eq_getElem _ _ h2,List.getD_eq_getElem _ _ (by omega : i+1 < l.length)] using had

  let T := X.image v
  have hsub (a : V) (ha : a ∈ T) : a ∈ l := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact vmem i (by have := Xbound hi; omega)
  have hqT : q ∉ T := by
    intro hqt
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hqt
    obtain ⟨x,hx,hadj⟩ := Xadj hi
    rw [he] at hadj
    exact hx.choose (hfirst _ hadj)
  have hconn : G.vertexConnectivity ≤ T.card := by
    rw [vertexConnectivity,if_neg (by have := Fintype.one_lt_card (α := V); omega)]
    refine csInf_le' ⟨T,rfl,Or.inl ?_⟩
    intro hh
    let a : ↥((T : Set V)ᶜ) := ⟨w0,fun ha => hw0 (hsub _ ha)⟩
    let b : ↥((T : Set V)ᶜ) := ⟨q,hqT⟩
    obtain ⟨p⟩ := hh a b
    have hnq : ¬U q := fun h => h.choose (List.head_mem hne)
    obtain ⟨ed,_,h1,h2⟩ := p.exists_boundary_dart {x | U x.val} hu0 hnq
    have he : G.Adj ed.fst.val ed.snd.val := ed.adj
    by_cases hin : ed.snd.val ∈ l
    · obtain ⟨j,hj,hej⟩ := List.getElem_of_mem hin
      have hvj : v j = ed.snd.val := by simpa only [v,List.getD_eq_getElem _ _ hj] using hej
      have hjm : j < m := hj
      by_cases hlj : j=m-1
      · rw [← hvj,hlj,hvz] at he
        exact h1.choose (hlast _ he.symm)
      · have hjX : j ∈ X := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega),ed.fst.val,h1,hvj.symm ▸ he.symm⟩
        exact ed.snd.property (Finset.mem_image.mpr ⟨j,hjX,hvj⟩)
    · obtain ⟨hn,hf⟩ := h1
      have he' : H.Adj ⟨ed.fst.val,hn⟩ ⟨ed.snd.val,hin⟩ := he
      exact h2 ⟨hin,(ConnectedComponent.connectedComponentMk_eq_of_adj he').symm.trans hf⟩
  let Y := X.image (fun i => v (i+1))
  have hY : Y.card = X.card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj he
    change v (i+1) = v (j+1) at he
    have h := vinj _ _ (by have := Xbound hi; omega) (by have := Xbound hj; omega) he
    omega
  have qY : q ∉ Y := by
    intro h
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
    have h' := vinj (i+1) 0 (by have := Xbound hi; omega) hm (he.trans hv0.symm)
    omega
  have wY : w0 ∉ Y := by
    intro h
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
    exact hw0 (he ▸ vmem (i+1) (by have := Xbound hi; omega))
  have wq : w0 ≠ q := fun h => hw0 (h ▸ List.head_mem hne)
  have hIndY : G.IsIndepSet (Y : Set V) := by
    intro u hu w hw hne
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    have hneij : i ≠ j := by rintro rfl; exact hne rfl
    rcases lt_or_gt_of_ne hneij with h | h
    · exact cross hi hj h
    · exact fun ha => cross hj hi h ha.symm
  have hqInd : G.IsIndepSet (↑(insert q Y) : Set V) := by
    intro a ha b hb hn hadj
    rcases Finset.mem_insert.mp ha with rfl | ha <;> rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hn rfl
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
      exact no_front hi hadj
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      exact no_front hi hadj.symm
    · exact hIndY ha hb hn hadj
  have hwfree {x : V} (hx : x ∈ insert q Y) : ¬G.Adj w0 x := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact fun h => hw0 (hfirst _ h.symm)
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact fun h => no_external hi hu0 h.symm
  refine ⟨insert w0 (insert q Y),?_,?_⟩
  · intro a ha b hb hn had
    rcases Finset.mem_insert.mp ha with rfl | ha <;> rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hn rfl
    · exact hwfree hb had
    · exact hwfree ha had.symm
    · exact hqInd ha hb hn had
  · have hw : w0 ∉ insert q Y := by simp [wq,wY]
    rw [Finset.card_insert_of_notMem hw,Finset.card_insert_of_notMem qY,hY]
    have hT : T.card ≤ X.card := Finset.card_image_le
    omega


-- The path version of the Chvátal–Erdős theorem, obtained by insertions and path rotations.
lemma independent_of_nontrace [Nontrivial V]
    (hno : ¬∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ G.vertexConnectivity + 2 ≤ I.card := by
  classical
  obtain ⟨v0⟩ := (inferInstance : Nonempty V)
  let P (n : ℕ) := ∃ l : List V, (l.Nodup ∧ l.IsChain G.Adj) ∧ l.length = n
  have h1 : P 1 := ⟨[v0],⟨by simp,List.isChain_singleton _⟩,rfl⟩
  let M := Nat.findGreatest P (Fintype.card V)
  have h1n : 1 ≤ Fintype.card V := Fintype.card_pos
  obtain ⟨l,⟨hnd,hch⟩,hl⟩ : P M := Nat.findGreatest_spec h1n h1
  have hM : 1 ≤ M := Nat.le_findGreatest h1n h1
  have hne : l ≠ [] := by rintro rfl; simp at hl; omega
  have hmax (p : List V) (hp : p.Nodup) (hc : p.IsChain G.Adj) : p.length ≤ l.length := by
    rw [hl]
    exact Nat.le_findGreatest hp.length_le_card ⟨p,⟨hp,hc⟩,rfl⟩
  by_cases hall : ∀ w, w ∈ l
  · exfalso
    apply hno
    have he : l.toFinset = Finset.univ := by ext w; simp [hall w]
    have hlen := List.toFinset_card_of_nodup hnd
    rw [he,Finset.card_univ] at hlen
    let p := Walk.ofSupport l hne hch
    have hp : p.IsPath := Walk.IsPath.mk' (by simpa [p,Walk.support_ofSupport] using hnd)
    exact ⟨_,_,p,Walk.isHamiltonian_iff_isPath_and_length_eq.mpr
      ⟨hp,by simp only [p,Walk.length_ofSupport]; omega⟩⟩
  · push Not at hall
    obtain ⟨w,hw⟩ := hall
    exact large_independent_on_longest l hne hnd hch hmax w hw

lemma attach_independent (T L : Finset V) (hT : (G.induce (T : Set V)).IsTree)
    (hd : Disjoint T L) (hI : G.IsIndepSet (L : Set V))
    (hU : ∀ x ∈ L, ∃! y, y ∈ T ∧ G.Adj x y) : (G.induce ((T ∪ L : Finset V) : Set V)).IsTree := by
  induction L using Finset.induction_on with
  | empty => rw [Finset.union_empty]; exact hT
  | @insert x L hx ih =>
    have hD := Finset.disjoint_insert_right.mp hd
    have hIL : G.IsIndepSet (L : Set V) := fun _ ha _ hb hne =>
      hI (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hb) hne
    have hG := ih hD.2 hIL (fun y hy => hU y (Finset.mem_insert_of_mem hy))
    obtain ⟨a,ha,hu⟩ := hU x (Finset.mem_insert_self _ _)
    rw [Finset.union_insert]
    apply hG.induce_insert_of_unique_adj (by simp [hD.1,hx]) (Finset.mem_union_left _ ha.1) ha.2
    intro b hb h
    rcases Finset.mem_union.mp hb with hbt | hbl
    · exact hu b ⟨hbt,h⟩
    · exact False.elim (hI (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hbl) h.ne h)

section Bipartite
variable [Nontrivial V] [DecidableRel G.Adj] (C : V → Bool)
variable (proper : ∀ ⦃x y⦄, G.Adj x y → C x ≠ C y)
variable (treeBound : G.largestInducedTreeSize ≤ G.vertexConnectivity + 2)

end Bipartite

lemma double_star_size [DecidableRel G.Adj]
    {a b : V} (ab : G.Adj a b) (I : Finset V) (hI : G.IsIndepSet (I : Set V)) (ha : a ∉ I) (hb : b ∉ I)
    (h : ∀ x ∈ I, (G.Adj a x ∧ ¬G.Adj b x) ∨ (G.Adj b x ∧ ¬G.Adj a x)) :
    I.card+2 ≤ G.largestInducedTreeSize := by
  let T : Finset V := {a,b}
  have tree : (G.induce (T : Set V)).IsTree := induced_star a {b} (by
    intro u hu v hv hn
    exact False.elim (hn ((Finset.mem_singleton.mp hu).trans (Finset.mem_singleton.mp hv).symm))) (by
      intro u hu
      exact (Finset.mem_singleton.mp hu) ▸ ab)
  have dis : Disjoint T I := by
    apply Finset.disjoint_left.mpr
    intro x hx hxI
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact ha (hx ▸ hxI)
    · exact hb ((Finset.mem_singleton.mp hx) ▸ hxI)
  have unique (x : V) (hx : x ∈ I) : ∃! y, y ∈ T ∧ G.Adj x y := by
    rcases h x hx with h | h
    · refine ⟨a,⟨by simp [T],h.1.symm⟩,?_⟩
      rintro y ⟨hy,he⟩
      rcases Finset.mem_insert.mp hy with hh | hh
      · exact hh
      · exact (h.2 ((Finset.mem_singleton.mp hh) ▸ he.symm)).elim
    · refine ⟨b,⟨by simp [T],h.1.symm⟩,?_⟩
      rintro y ⟨hy,he⟩
      rcases Finset.mem_insert.mp hy with hh | hh
      · exact (h.2 (hh ▸ he.symm)).elim
      · exact Finset.mem_singleton.mp hh
  have size := card_le_largestInducedTreeSize (attach_independent T I tree dis hI unique)
  have Tsize : T.card=2 := by simp [T,ab.ne]
  rw [Finset.card_union_of_disjoint dis,Tsize] at size
  omega

lemma tree_with_private_leaves (T L : Finset V) (hT : (G.induce (T : Set V)).IsTree)
    (hI : G.IsIndepSet (L : Set V)) (hD : Disjoint T L)
    (hU : ∀ y ∈ L, ∃! z, z ∈ T ∧ G.Adj y z) : T.card+L.card ≤ G.largestInducedTreeSize := by
  simpa only [Finset.card_union_of_disjoint hD] using card_le_largestInducedTreeSize (attach_independent T L hT hD hI hU)

lemma path3_rows [DecidableRel G.Adj] (I : Finset V) (hi : G.IsIndepSet (I : Set V))
    {a w b : V} (aw : G.Adj a w) (wb : G.Adj w b) (ab : ¬G.Adj a b) (ne : a ≠ b) :
    let R (c : V) := I.filter (G.Adj c)
    3 + (((R a \ R b) ∪ (R b \ R a)) \ R w).card ≤ G.largestInducedTreeSize := by
  classical
  intro R
  let L := ((R a \ R b) ∪ (R b \ R a)) \ R w
  let T : Finset V := {w,a,b}
  have side (c d z : V) (h : z ∈ R c \ R d) : z ∈ I ∧ G.Adj c z ∧ ¬G.Adj d z := by
    obtain ⟨hc,hd⟩ := Finset.mem_sdiff.mp h
    obtain ⟨hz,e⟩ := Finset.mem_filter.mp hc
    exact ⟨hz,e,fun h' => hd (Finset.mem_filter.mpr ⟨hz,h'⟩)⟩
  have leaves (z : V) (hz : z ∈ L) : z ∈ I ∧ ¬G.Adj w z ∧
      ((G.Adj a z ∧ ¬G.Adj b z) ∨ (G.Adj b z ∧ ¬G.Adj a z)) := by
    obtain ⟨hab,hw⟩ := Finset.mem_sdiff.mp hz
    rcases Finset.mem_union.mp hab with hz | hz
    · obtain ⟨hz,hh⟩ := side _ _ _ hz
      exact ⟨hz,fun e => hw (Finset.mem_filter.mpr ⟨hz,e⟩),Or.inl hh⟩
    · obtain ⟨hz,hh⟩ := side _ _ _ hz
      exact ⟨hz,fun e => hw (Finset.mem_filter.mpr ⟨hz,e⟩),Or.inr hh⟩
  have pair : G.IsIndepSet (↑({a,b} : Finset V) : Set V) := by
    intro x hx y hy hne e
    simp at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      first | exact hne rfl | exact ab e | exact ab e.symm
  have ht : (G.induce (T : Set V)).IsTree := induced_star w {a,b} pair (by
    intro t ht; simp at ht; rcases ht with rfl | rfl
    · exact aw.symm
    · exact wb)
  have dis : Disjoint T L := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨_,nw,which⟩ := leaves z hz'
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with he | he | he
    · rw [he] at which
      rcases which with h | h
      · exact h.2 wb.symm
      · exact h.2 aw
    · exact nw (he ▸ aw.symm)
    · exact nw (he ▸ wb)
  have single (z : V) (hz : z ∈ L) : ∃! y, y ∈ T ∧ G.Adj z y := by
    obtain ⟨_,nw,which⟩ := leaves z hz
    rcases which with h | h
    · refine ⟨a,⟨by simp [T],h.1.symm⟩,?_⟩
      rintro y ⟨hy,e⟩
      simp only [T,Finset.mem_insert,Finset.mem_singleton] at hy
      rcases hy with he | he | he
      · exact (nw (he ▸ e.symm)).elim
      · exact he
      · exact (h.2 (he ▸ e.symm)).elim
    · refine ⟨b,⟨by simp [T],h.1.symm⟩,?_⟩
      rintro y ⟨hy,e⟩
      simp only [T,Finset.mem_insert,Finset.mem_singleton] at hy
      rcases hy with he | he | he
      · exact (nw (he ▸ e.symm)).elim
      · exact (h.2 (he ▸ e.symm)).elim
      · exact he
  have h := tree_with_private_leaves T L ht (fun _ h _ h' => hi (leaves _ h).1 (leaves _ h').1) dis single
  have card : T.card = 3 := by simp [T,aw.ne.symm,wb.ne,ne]
  simpa only [card,L] using h

lemma row_distance_packing [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected) (ht : G.largestInducedTreeSize ≤ 4)
    (I : Finset V) (hi : G.IsIndepSet (I : Set V)) (s : ℕ) (max : ∀ v, (I.filter (G.Adj v)).card ≤ s)
    (a b : V) : ((I.filter (G.Adj a)) ∪ (I.filter (G.Adj b))).card ≤ s+1 := by
  classical
  let R (v : V) := I.filter (G.Adj v)
  change (R a ∪ R b).card ≤ s+1
  have nw {v : V} (hv : v ∈ I) : R v=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx =>
    hi hv (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2.ne (Finset.mem_filter.mp hx).2)
  have algebra (U W : Finset V) (hu : U.card ≤ s) (hw : W.card ≤ s)
      (d : (U \ W).card + (W \ U).card ≤ 2) : (U ∪ W).card ≤ s+1 := by
    have u := Finset.card_sdiff_add_card_inter U W
    have w := Finset.card_sdiff_add_card_inter W U
    rw [Finset.inter_comm W U] at w
    have eq := Finset.card_union_add_card_inter U W
    omega
  have adj {u v : V} (e : G.Adj u v) : (R u ∪ R v).card ≤ s+1 := by
    by_cases hu : u ∈ I
    · rw [nw hu,Finset.empty_union]; have h : (R v).card ≤ s := max v; omega
    by_cases hv : v ∈ I
    · rw [nw hv,Finset.union_empty]; have h : (R u).card ≤ s := max u; omega
    let L := (R u \ R v) ∪ (R v \ R u)
    have inI : L ⊆ I := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h <;> exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).1
    have eq : ∀ x ∈ L, (G.Adj u x ∧ ¬G.Adj v x) ∨ (G.Adj v x ∧ ¬G.Adj u x) := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · obtain ⟨h1,h2⟩ := Finset.mem_sdiff.mp h
        exact Or.inl ⟨(Finset.mem_filter.mp h1).2,fun y => h2 (Finset.mem_filter.mpr ⟨inI hx,y⟩)⟩
      · obtain ⟨h1,h2⟩ := Finset.mem_sdiff.mp h
        exact Or.inr ⟨(Finset.mem_filter.mp h1).2,fun y => h2 (Finset.mem_filter.mpr ⟨inI hx,y⟩)⟩
    have dis : Disjoint (R u \ R v) (R v \ R u) := Finset.disjoint_left.mpr fun _ h h' =>
      (Finset.mem_sdiff.mp h).2 (Finset.mem_sdiff.mp h').1
    have bound := double_star_size e L (fun _ h _ h' => hi (inI h) (inI h'))
      (fun h => hu (inI h)) (fun h => hv (inI h)) eq
    change L.card+2 ≤ _ at bound
    rw [show L.card=_ from Finset.card_union_of_disjoint dis] at bound
    exact algebra _ _ (max u) (max v) (by omega)
  by_cases same : a=b
  · subst b; rw [Finset.union_idempotent]; exact (max a).trans (by omega)
  by_cases e : G.Adj a b
  · exact adj e
  by_cases overlap : (R a ∩ R b).Nonempty
  · obtain ⟨w,hw⟩ := overlap
    obtain ⟨hwa,hwb⟩ := Finset.mem_inter.mp hw
    obtain ⟨wi,aw⟩ := Finset.mem_filter.mp hwa
    have wb := (Finset.mem_filter.mp hwb).2.symm
    have diff := path3_rows I hi aw wb e same
    change 3+(((R a \ R b) ∪ (R b \ R a)) \ R w).card ≤ _ at diff
    have dis : Disjoint (R a \ R b) (R b \ R a) := Finset.disjoint_left.mpr fun _ h h' =>
      (Finset.mem_sdiff.mp h).2 (Finset.mem_sdiff.mp h').1
    rw [nw wi,Finset.sdiff_empty,Finset.card_union_of_disjoint dis] at diff
    exact algebra _ _ (max a) (max b) (by omega)
  have dis : Disjoint (R a) (R b) := Finset.disjoint_left.mpr fun x ha hb => overlap ⟨x,Finset.mem_inter.mpr ⟨ha,hb⟩⟩
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a b
  have fst := diameter_tree hc
  have diam := G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u := a) (v := b)
  have d0 : G.dist a b ≠ 0 := fun h => same (hc.dist_eq_zero_iff.mp h)
  have d1 : G.dist a b ≠ 1 := fun h => e (dist_eq_one_iff_adj.mp h)
  have possibility : p.length=2 ∨ p.length=3 := by omega
  rcases possibility with d | d
  · let w := p.getVert 1
    have aw := p.adj_getVert_succ (i := 0) (by omega)
    rw [p.getVert_zero] at aw
    have wb := p.adj_getVert_succ (i := 1) (by omega)
    rw [p.getVert_of_length_le (by omega : p.length ≤ 1+1)] at wb
    have diff := path3_rows I hi aw wb e same
    change 3+(((R a \ R b) ∪ (R b \ R a)) \ R w).card ≤ _ at diff
    rw [Finset.sdiff_eq_self_of_disjoint dis,Finset.sdiff_eq_self_of_disjoint dis.symm] at diff
    have h := Finset.card_sdiff_add_card_inter (R a ∪ R b) (R w)
    have lim := Finset.card_le_card (Finset.inter_subset_right (s₁ := R a ∪ R b) (s₂ := R w))
    have mx : (R w).card ≤ s := max w
    omega
  · let u := p.getVert 1
    let v := p.getVert 2
    have au : G.Adj a u := p.getVert_zero ▸ p.adj_getVert_succ (i := 0) (by omega)
    have uv : G.Adj u v := p.adj_getVert_succ (i := 1) (by omega)
    have vb : G.Adj v b := p.getVert_of_length_le (by omega : p.length ≤ 2+1) ▸ p.adj_getVert_succ (i := 2) (by omega)
    let q : G.Walk a b := .cons au (.cons uv (.cons vb .nil))
    have qs : q.length=G.dist a b := by change 3 = _; omega
    let T := q.support.toFinset
    have tree := q.induce_support_isTree_of_length_eq_dist qs
    have tcard : T.card=4 := by
      rw [show T.card=q.support.length from List.toFinset_card_of_nodup (q.isPath_of_length_eq_dist qs).support_nodup,Walk.length_support]
      rfl
    have sub : R a ∪ R b ⊆ R u ∪ R v := by
      intro x hx
      by_contra h
      have part : x ∈ I := by rcases Finset.mem_union.mp hx with h | h <;> exact (Finset.mem_filter.mp h).1
      have nu : ¬G.Adj x u := fun qu => h (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨part,qu.symm⟩))
      have nv : ¬G.Adj x v := fun qv => h (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨part,qv.symm⟩))
      have tm (z : V) : z ∈ T ↔ z=a ∨ z=u ∨ z=v ∨ z=b := by simp [T,q]
      have notin : x ∉ T := by
        intro hx
        rcases (tm _).mp hx with eq | eq | eq | eq
        · exact nu (eq ▸ au)
        · exact nv (eq ▸ uv)
        · exact nu (eq ▸ uv.symm)
        · exact nv (eq ▸ vb.symm)
      have one : ∃! z, z ∈ T ∧ G.Adj x z := by
        rcases Finset.mem_union.mp hx with ha | hb
        · have nb : ¬G.Adj x b := fun ex => Finset.disjoint_left.mp dis ha (Finset.mem_filter.mpr ⟨part,ex.symm⟩)
          refine ⟨a,⟨(tm _).mpr (Or.inl rfl),(Finset.mem_filter.mp ha).2.symm⟩,?_⟩
          rintro y ⟨hy,ex⟩
          rcases (tm _).mp hy with eq | eq | eq | eq
          · exact eq
          · exact (nu (eq ▸ ex)).elim
          · exact (nv (eq ▸ ex)).elim
          · exact (nb (eq ▸ ex)).elim
        · have na : ¬G.Adj x a := fun ex => Finset.disjoint_left.mp dis (Finset.mem_filter.mpr ⟨part,ex.symm⟩) hb
          refine ⟨b,⟨(tm _).mpr (by tauto),(Finset.mem_filter.mp hb).2.symm⟩,?_⟩
          rintro y ⟨hy,ex⟩
          rcases (tm _).mp hy with eq | eq | eq | eq
          · exact (na (eq ▸ ex)).elim
          · exact (nu (eq ▸ ex)).elim
          · exact (nv (eq ▸ ex)).elim
          · exact eq
      obtain ⟨z,hz,uniq⟩ := one
      have h5 := card_le_largestInducedTreeSize (tree.induce_insert_of_unique_adj notin hz.1 hz.2
        (fun y hy hyx => uniq y ⟨hy,hyx⟩))
      rw [Finset.card_insert_of_notMem notin,tcard] at h5
      omega
    exact (Finset.card_le_card sub).trans (adj uv)

lemma row_replacement {A B : Finset V} (close : (A \ B).card + (B \ A).card ≤ 2)
    (large : B.card ≤ A.card) {x : V} (hxB : x ∈ B) (hxA : x ∉ A) :
    ∃ z ∈ A, z ∉ B ∧ B = insert x (A.erase z) := by
  have hx : x ∈ B \ A := Finset.mem_sdiff.mpr ⟨hxB,hxA⟩
  have bpos := Finset.card_pos.mpr (show (B \ A).Nonempty from ⟨x,hx⟩)
  have a := Finset.card_sdiff_add_card_inter A B
  have b := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at b
  have ac : (A \ B).card=1 := by omega
  have bc : (B \ A).card=1 := by omega
  obtain ⟨z,az⟩ := Finset.card_eq_one.mp ac
  obtain ⟨y,by'⟩ := Finset.card_eq_one.mp bc
  have xy : x=y := Finset.mem_singleton.mp (by' ▸ hx)
  subst y
  have hz := Finset.mem_sdiff.mp (show z ∈ A \ B from az ▸ Finset.mem_singleton_self _)
  refine ⟨z,hz.1,hz.2,?_⟩
  ext t
  rw [Finset.mem_insert,Finset.mem_erase]
  constructor
  · intro ht
    by_cases hta : t ∈ A
    · exact Or.inr ⟨fun he => hz.2 (he ▸ ht),hta⟩
    · exact Or.inl (Finset.mem_singleton.mp (by' ▸ Finset.mem_sdiff.mpr ⟨ht,hta⟩))
  · rintro (he | ⟨htz,hta⟩)
    · exact he ▸ hxB
    · by_contra h
      exact htz (Finset.mem_singleton.mp (az ▸ Finset.mem_sdiff.mpr ⟨hta,h⟩))

lemma replacement_omissions {A B D : Finset V} {x y z w : V} (hx : x ∉ A) (hy : y ∉ A)
    (hz : z ∈ A) (hw : w ∈ A) (hxy : x ≠ y)
    (hb : B=insert x (A.erase z)) (hd : D=insert y (A.erase w))
    (close : (B \ D).card+(D \ B).card≤2) : z=w := by
  by_contra hzw
  have xw : x ≠ w := fun e => hx (e ▸ hw)
  have yz : y ≠ z := fun e => hy (e ▸ hz)
  have xz : x ≠ z := fun e => hx (e ▸ hz)
  have yw : y ≠ w := fun e => hy (e ▸ hw)
  have sub : ({x,w} : Finset V) ⊆ B \ D := by
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · rw [ht]; simp [hb,hd,hxy,hx]
    · rw [Finset.mem_singleton.mp ht]; simp [hb,hd,hw,Ne.symm hzw,Ne.symm yw]
  have sub' : ({y,z} : Finset V) ⊆ D \ B := by
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · rw [ht]; simp [hb,hd,Ne.symm hxy,hy]
    · rw [Finset.mem_singleton.mp ht]; simp [hb,hd,hz,hzw,Ne.symm xz]
  have h := Finset.card_le_card sub
  have h' := Finset.card_le_card sub'
  simp [xw,yz] at h h'
  omega

lemma path_from_spanning_list [Nontrivial V] (l : List V) (hne : l ≠ []) (hn : l.Nodup)
    (hch : l.IsChain G.Adj) (hall : ∀ x, x ∈ l) : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have he : l.toFinset = Finset.univ := by ext x; simp [hall x]
  have hlen := List.toFinset_card_of_nodup hn
  rw [he,Finset.card_univ] at hlen
  let p := Walk.ofSupport l hne hch
  have hp : p.IsPath := Walk.IsPath.mk' (by simpa [p,Walk.support_ofSupport] using hn)
  exact ⟨_,_,p,Walk.isHamiltonian_iff_isPath_and_length_eq.mpr
    ⟨hp,by simp only [p,Walk.length_ofSupport]; omega⟩⟩

-- If the next clique vertex sees a vertex of the independent side on the path,
-- insert it next to that vertex. Its other neighbor on the path is in the clique.
lemma chain_blocks {W : Type*} (F : W → List V) (ord : List W) (hord : ord.Nodup)
    (hne : ∀ i, F i ≠ []) (hn : ∀ i, (F i).Nodup) (ch : ∀ i, (F i).IsChain G.Adj)
    (separate : ∀ i j, i ≠ j → (F i).Disjoint (F j))
    (cross : ∀ i j, i ≠ j → ∀ u ∈ (F i).getLast?, ∀ v ∈ (F j).head?, G.Adj u v) :
    (ord.flatMap F).Nodup ∧ (ord.flatMap F).IsChain G.Adj := by
  refine ⟨List.nodup_flatMap.mpr ⟨fun i _ => hn i,hord.imp (fun {i j} h => separate i j h)⟩,?_⟩
  change ((ord.map F).flatten).IsChain G.Adj
  have h : [] ∉ ord.map F := by
    intro hh
    obtain ⟨i,_,hi⟩ := List.mem_map.mp hh
    exact hne i hi
  apply (List.isChain_flatten h).mpr
  refine ⟨?_,?_⟩
  · intro l hl
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hl
    exact ch i
  · apply List.Pairwise.isChain
    apply List.pairwise_map.mpr
    exact hord.imp fun {i j} hij => cross i j hij

lemma last_in_block {W : Type*} (F : W → List V) (ord : List W) (v : V)
    (hv : v ∈ (ord.flatMap F).getLast?) : ∃ i ∈ ord, v ∈ (F i).getLast? := by
  induction ord with
  | nil => simp at hv
  | cons i t ih =>
    by_cases he : t.flatMap F = []
    · have h : v ∈ (F i).getLast? := by simpa [List.flatMap_cons,he] using hv
      exact ⟨i,by simp,h⟩
    · have hv' : v ∈ (t.flatMap F).getLast? := by simpa [List.flatMap_cons,List.getLast?_append_of_ne_nil _ he] using hv
      obtain ⟨j,hj,hv''⟩ := ih hv'
      exact ⟨j,List.mem_cons_of_mem _ hj,hv''⟩

lemma p4_single (ht : G.largestInducedTreeSize ≤ 4) {a b c d x : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d)
    (ac : ¬G.Adj a c) (bd : ¬G.Adj b d) (ad : ¬G.Adj a d)
    (neac : a ≠ c) (nebd : b ≠ d) (nead : a ≠ d)
    (out : x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d)
    (one : ∃! y, (y=a ∨ y=b ∨ y=c ∨ y=d) ∧ G.Adj x y) : False := by
  let T : Finset V := {d,b,a,c}
  have tree : (G.induce (T : Set V)).IsTree := induced_path_on_four ab bc cd ac bd ad neac nebd nead
  have mem (y : V) : y ∈ T ↔ y=a ∨ y=b ∨ y=c ∨ y=d := by
    simp only [T,Finset.mem_insert,Finset.mem_singleton]
    tauto
  obtain ⟨y,⟨hy,xy⟩,uq⟩ := one
  have out' : x ∉ T := by rw [mem]; tauto
  have tree' := tree.induce_insert_of_unique_adj out' ((mem y).mpr hy) xy (fun z hz ez => uq z ⟨(mem z).mp hz,ez⟩)
  have n := card_le_largestInducedTreeSize tree'
  have tc : T.card=4 := by simp [T,ab.ne.symm,bc.ne,cd.ne.symm,neac,nead.symm,nebd.symm]
  rw [Finset.card_insert_of_notMem out',tc] at n
  omega

def Remote (G : SimpleGraph V) (a b : V) : Prop :=
  a ≠ b ∧ ¬G.Adj a b ∧ ∀ v, G.Adj a v → ¬G.Adj b v

lemma remote_flip {a b : V} (h : Remote G a b) : Remote G b a :=
  ⟨h.1.symm,fun e => h.2.1 e.symm,fun v e e' => h.2.2 v e' e⟩

lemma remote_edge [Nontrivial V] (hc : G.Connected) (ht : G.largestInducedTreeSize ≤ 4)
    {a b : V} (h : Remote G a b) : ∃ x y, G.Adj a x ∧ G.Adj x y ∧ G.Adj b y := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a b
  have d := G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=a) (v:=b)
  have dt := diameter_tree hc
  have d0 : G.dist a b ≠ 0 := fun e => h.1 (hc.dist_eq_zero_iff.mp e)
  have d1 : G.dist a b ≠ 1 := fun e => h.2.1 (dist_eq_one_iff_adj.mp e)
  have d2 : p.length ≠ 2 := by
    intro two
    have ax := p.adj_getVert_succ (i:=0) (by omega)
    have xb := p.adj_getVert_succ (i:=1) (by omega)
    rw [p.getVert_zero] at ax
    rw [p.getVert_of_length_le (by omega : p.length ≤ 1+1)] at xb
    exact h.2.2 _ ax xb.symm
  have l : p.length=3 := by omega
  have ax := p.adj_getVert_succ (i:=0) (by omega)
  have xy := p.adj_getVert_succ (i:=1) (by omega)
  have yb := p.adj_getVert_succ (i:=2) (by omega)
  rw [p.getVert_zero] at ax
  rw [p.getVert_of_length_le (by omega : p.length ≤ 2+1)] at yb
  exact ⟨_,_,ax,xy,yb.symm⟩

-- A cross edge x-y between neighborhoods of remote i,j yields i-x-y-j.
lemma cross_single (ht : G.largestInducedTreeSize ≤ 4) {i j x y z : V}
    (far : Remote G i j) (ix : G.Adj i x) (xy : G.Adj x y) (jy : G.Adj j y)
    (out : z ≠ i ∧ z ≠ x ∧ z ≠ y ∧ z ≠ j)
    (one : ∃! t, (t=i ∨ t=x ∨ t=y ∨ t=j) ∧ G.Adj z t) : False := by
  exact p4_single ht ix xy jy.symm (fun iy => far.2.2 y iy jy) (fun xj => far.2.2 x ix xj.symm)
    far.2.1 (fun eq => far.2.1 (eq ▸ jy.symm)) (fun eq => far.2.1 (eq ▸ ix)) far.1 out one

lemma cross_parallel (ht : G.largestInducedTreeSize ≤ 4) {i j x y z : V}
    (far : Remote G i j) (ix : G.Adj i x) (xy : G.Adj x y) (jy : G.Adj j y)
    (ni : z ≠ i) (nj : z ≠ j) (zi : ¬G.Adj z i) (zj : ¬G.Adj z j) :
    G.Adj z x ↔ G.Adj z y := by
  have side {i j x y : V} (far : Remote G i j) (ix : G.Adj i x) (xy : G.Adj x y) (jy : G.Adj j y)
      (ni : z ≠ i) (nj : z ≠ j) (zi : ¬G.Adj z i) (zj : ¬G.Adj z j) (zx : G.Adj z x) : G.Adj z y := by
    by_contra zy
    apply cross_single ht far ix xy jy ⟨ni,zx.ne,fun e => zj (e ▸ jy.symm),nj⟩
    refine ⟨x,⟨by tauto,zx⟩,?_⟩
    rintro w ⟨h,e⟩
    rcases h with rfl | rfl | rfl | rfl <;> tauto
  exact ⟨side far ix xy jy ni nj zi zj,side (remote_flip far) jy xy.symm ix nj ni zj zi⟩

lemma cross_sibling (ht : G.largestInducedTreeSize ≤ 4) {i j x y z : V}
    (far : Remote G i j) (ix : G.Adj i x) (xy : G.Adj x y) (jy : G.Adj j y)
    (jz : G.Adj j z) (xz : ¬G.Adj x z) : G.Adj y z := by
  by_contra yz
  have ni : z ≠ i := fun e => far.2.1 (e ▸ jz.symm)
  have nx : z ≠ x := fun e => far.2.2 x ix (e ▸ jz)
  have ny : z ≠ y := fun e => xz (e ▸ xy)
  have zi : ¬G.Adj z i := fun e => far.2.2 z e.symm jz
  apply cross_single ht far ix xy jy ⟨ni,nx,ny,jz.ne.symm⟩
  refine ⟨j,⟨by tauto,jz.symm⟩,?_⟩
  rintro w ⟨h,e⟩
  rcases h with rfl | rfl | rfl | rfl
  · exact (zi e).elim
  · exact (xz e.symm).elim
  · exact (yz e.symm).elim
  · rfl

-- Between three different remote branches, two cross edges incident on
-- the middle branch always have adjacent outer endpoints.
lemma cross_triangle (ht : G.largestInducedTreeSize ≤ 4) {i j k a b c d : V}
    (ij : Remote G i j) (jk : Remote G j k) (ik : Remote G i k)
    (ia : G.Adj i a) (jb : G.Adj j b) (jc : G.Adj j c) (kd : G.Adj k d)
    (ab : G.Adj a b) (cd : G.Adj c d) : G.Adj a d := by
  have foreign {i j k a : V} (ik : Remote G i k) (jk : Remote G j k) (ka : G.Adj k a) :
      a ≠ i ∧ a ≠ j ∧ ¬G.Adj a i ∧ ¬G.Adj a j := by
    exact ⟨fun e => ik.2.1 (e ▸ ka.symm),fun e => jk.2.1 (e ▸ ka.symm),
      fun e => ik.2.2 a e.symm ka,fun e => jk.2.2 a e.symm ka⟩
  obtain ⟨di,dj,dni,dnj⟩ := foreign ik jk kd
  obtain ⟨aj,ak,anj,ank⟩ := foreign (remote_flip ij) (remote_flip ik) ia
  have pa := cross_parallel ht ij ia ab jb di dj dni dnj
  have pb := cross_parallel ht jk jc cd kd aj ak anj ank
  by_contra ad
  have ac : ¬G.Adj a c := fun e => ad (pb.mp e)
  have db : ¬G.Adj d b := fun e => ad (pa.mpr e).symm
  have bc := cross_sibling ht ij ia ab jb jc ac
  -- i-a-b-c-d is now an induced five-vertex path.
  have ib : ¬G.Adj i b := fun e => ij.2.2 b e jb
  have ic : ¬G.Adj i c := fun e => ij.2.2 c e jc
  have nib : i ≠ b := fun e => ij.2.1 (e ▸ jb.symm)
  have nac : a ≠ c := fun e => ij.2.2 c (e ▸ ia) jc
  have nic : i ≠ c := fun e => ij.2.1 (e ▸ jc.symm)
  apply p4_single ht ia ab bc ib ac ic nib nac nic ⟨di,fun e => ik.2.2 a ia (e ▸ kd),
    fun e => jk.2.2 b jb (e ▸ kd),cd.ne.symm⟩
  refine ⟨c,⟨by tauto,cd.symm⟩,?_⟩
  rintro w ⟨h,e⟩
  rcases h with rfl | rfl | rfl | rfl
  · exact (dni e).elim
  · exact (ad e.symm).elim
  · exact (db e).elim
  · rfl

def IsHigh (G : SimpleGraph V) (J : Finset V) (i : J) (x : V) : Prop :=
  G.Adj i.val x ∧ ∃ j : J, i ≠ j ∧ ∃ y, G.Adj j.val y ∧ G.Adj x y

def IsLow (G : SimpleGraph V) (J : Finset V) (i : J) (x : V) : Prop :=
  x=i.val ∨ G.Adj i.val x ∧ ¬IsHigh G J i x

def IsRest (G : SimpleGraph V) (J : Finset V) (z : V) : Prop :=
  ∀ i : J, z ≠ i.val ∧ ¬G.Adj i.val z

lemma index_third {W : Type*} [Fintype W] [DecidableEq W] (h : 3 ≤ Fintype.card W) (i j : W) :
    ∃ k : W, k ≠ i ∧ k ≠ j := by
  by_contra! no
  have sub : (Finset.univ : Finset W) ⊆ {i,j} := by
    intro x _
    by_cases hi : x=i
    · simp [hi]
    · simp [no x hi]
  have bound := Finset.card_le_card sub
  have ct := Finset.card_insert_le i ({j} : Finset W)
  simp only [Finset.card_univ,Finset.card_singleton] at *
  omega

section PackClass
variable [Nontrivial V] {J : Finset V} (hc : G.Connected) (ht : G.largestInducedTreeSize ≤ 4)
variable (far : ∀ i j : J, i ≠ j → Remote G i.val j.val)
variable (three : 3 ≤ Fintype.card J)

include hc ht far in
lemma high_coverage {i k : J} (ik : i ≠ k) {x : V} (hx : IsHigh G J i x) :
    ∃ y, G.Adj k.val y ∧ G.Adj x y := by
  obtain ⟨ix,j,ij,b,jb,xb⟩ := hx
  by_cases jk : j=k
  · exact ⟨b,jk ▸ jb,xb⟩
  obtain ⟨c,d,jc,cd,kd⟩ := remote_edge hc ht (far j k jk)
  exact ⟨d,kd,cross_triangle ht (far i j ij) (far j k jk) (far i k ik) ix jb jc kd xb cd⟩

include hc ht far three in
lemma high_join {i k : J} (ik : i ≠ k) {x y : V} (hx : IsHigh G J i x) (hy : IsHigh G J k y) :
    G.Adj x y := by
  obtain ⟨j,ji,jk⟩ := index_third three i k
  obtain ⟨b,jb,xb⟩ := high_coverage hc ht far ji.symm hx
  obtain ⟨c,jc,yc⟩ := high_coverage hc ht far jk.symm hy
  exact cross_triangle ht (far i j ji.symm) (far j k jk) (far i k ik) hx.1 jb jc hy.1 xb yc.symm

include far in
lemma low_away {i j : J} (ij : i ≠ j) {z y : V} (lz : IsLow G J i z) (jy : G.Adj j.val y) :
    ¬G.Adj z y := by
  rcases lz with rfl | ⟨iz,nz⟩
  · exact fun e => (far i j ij).2.2 y e jy
  · exact fun e => nz ⟨iz,j,ij,y,jy,e⟩

include ht far in
lemma low_high {i : J} {x z : V} (hx : IsHigh G J i x) (lz : IsLow G J i z) :
    G.Adj x z := by
  rcases lz with rfl | ⟨iz,nz⟩
  · exact hx.1.symm
  obtain ⟨ix,j,ij,y,jy,xy⟩ := hx
  have yz : ¬G.Adj y z := fun e => nz ⟨iz,j,ij,y,jy,e.symm⟩
  exact cross_sibling ht (far j i ij.symm) jy xy.symm ix iz yz

include far in
lemma low_misses_index {i j : J} (ij : i ≠ j) {z : V} (lz : IsLow G J i z) :
    ¬G.Adj j.val z ∧ z ≠ j.val := by
  have f := far i j ij
  rcases lz with rfl | ⟨iz,_⟩
  · exact ⟨fun e => f.2.1 e.symm,f.1⟩
  · exact ⟨f.2.2 z iz,fun e => f.2.1 (e ▸ iz)⟩

include hc ht far three in
lemma each_high (i : J) : ∃ h, IsHigh G J i h := by
  obtain ⟨j,ji,_⟩ := index_third three i i
  obtain ⟨x,y,ix,xy,jy⟩ := remote_edge hc ht (far i j ji.symm)
  exact ⟨x,ix,j,ji.symm,y,jy,xy⟩

include hc ht far three in
lemma low_clique (i : J) {z w : V} (lz : IsLow G J i z) (lw : IsLow G J i w) (zw : z ≠ w) :
    G.Adj z w := by
  obtain ⟨j,ji,_⟩ := index_third three i i
  obtain ⟨x,hx⟩ := each_high hc ht far three i
  obtain ⟨y,hy⟩ := each_high hc ht far three j
  have yx := high_join hc ht far three ji hy hx
  have xz := low_high ht far hx lz
  have xw := low_high ht far hx lw
  have zy := low_away far ji.symm lz hy.1
  have wy := low_away far ji.symm lw hy.1
  have ⟨jz,zj'⟩ := low_misses_index far ji.symm lz
  have ⟨jw,wj'⟩ := low_misses_index far ji.symm lw
  have jx : ¬G.Adj j.val x := (far i j ji.symm).2.2 x hx.1
  have jx' : j.val ≠ x := fun e => (far i j ji.symm).2.1 (e ▸ hx.1)
  have yz' : y ≠ z := fun e => jz (e ▸ hy.1)
  by_contra no
  apply p4_single ht hy.1 yx xz jx (fun e => zy e.symm) jz jx' yz' zj'.symm
    ⟨wj',fun e => jw (e ▸ hy.1),xw.ne.symm,zw.symm⟩
  refine ⟨x,⟨by tauto,xw.symm⟩,?_⟩
  rintro t ⟨h,e⟩
  rcases h with rfl | rfl | rfl | rfl
  · exact (jw e.symm).elim
  · exact (wy e).elim
  · rfl
  · exact (no e.symm).elim
end PackClass

lemma no_induced_five_path (ht : G.largestInducedTreeSize ≤ 4) {a b c d e : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (de : G.Adj d e)
    (ac : ¬G.Adj a c) (ad : ¬G.Adj a d) (ae : ¬G.Adj a e)
    (bd : ¬G.Adj b d) (be : ¬G.Adj b e) (ce : ¬G.Adj c e) : False := by
  apply p4_single ht ab bc cd ac bd ad (fun eq => ad (eq ▸ cd))
    (fun eq => ad (eq ▸ ab)) (fun eq => bd (eq ▸ ab.symm))
    ⟨fun eq => ad (eq ▸ de.symm),fun eq => ce (eq ▸ bc.symm),fun eq => be (eq ▸ bc),de.ne.symm⟩
  refine ⟨d,⟨by tauto,de.symm⟩,?_⟩
  rintro t ⟨h,et⟩
  rcases h with rfl | rfl | rfl | rfl
  · exact (ae et.symm).elim
  · exact (be et.symm).elim
  · exact (ce et.symm).elim
  · rfl

section RestClass
variable [Nontrivial V] {J : Finset V} (hc : G.Connected) (ht : G.largestInducedTreeSize ≤ 4)
variable (far : ∀ i j : J, i ≠ j → Remote G i.val j.val) (three : 3 ≤ Fintype.card J)

include hc ht far three in
lemma rest_high_iff {i j : J} {x y z : V} (hx : IsHigh G J i x) (hy : IsHigh G J j y)
    (hz : IsRest G J z) : G.Adj z x ↔ G.Adj z y := by
  have move {i j : J} (ij : i ≠ j) {x y : V} (hx : IsHigh G J i x) (hy : IsHigh G J j y) :
      G.Adj z x ↔ G.Adj z y := by
    exact cross_parallel ht (far i j ij) hx.1 (high_join hc ht far three ij hx hy) hy.1 (hz i).1 (hz j).1
      (fun e => (hz i).2 e.symm) (fun e => (hz j).2 e.symm)
  obtain ⟨k,ki,kj⟩ := index_third three i j
  obtain ⟨w,hw⟩ := each_high hc ht far three k
  exact (move ki.symm hx hw).trans (move kj hw hy)

include hc ht far three in
lemma rest_low_disjoint {i : J} {z l : V} (hz : IsRest G J z) (hl : IsLow G J i l) :
    ¬G.Adj z l := by
  intro zl
  have il : G.Adj i.val l := by
    rcases hl with rfl | h
    · exact ((hz i).2 zl.symm).elim
    · exact h.1
  obtain ⟨j,ji,_⟩ := index_third three i i
  obtain ⟨x,hx⟩ := each_high hc ht far three i
  obtain ⟨y,hy⟩ := each_high hc ht far three j
  have xy := high_join hc ht far three ji.symm hx hy
  have xl := low_high ht far hx hl
  have ly := low_away far ji.symm hl hy.1
  have jl := (low_misses_index far ji.symm hl).1
  have jx := (far i j ji.symm).2.2 x hx.1
  have zy : G.Adj z y := by
    by_contra zy
    have zx : ¬G.Adj z x := fun e => zy ((rest_high_iff hc ht far three hx hy hz).mp e)
    exact no_induced_five_path ht zl xl.symm xy hy.1.symm zx zy (fun e => (hz j).2 e.symm)
      ly (fun e => jl e.symm) (fun e => jx e.symm)
  exact no_induced_five_path ht il zl.symm zy hy.1.symm (hz i).2 ((far j i ji).2.2 y hy.1)
    (far i j ji.symm).2.1 ly (fun e => jl e.symm) (fun e => (hz j).2 e.symm)

include hc ht far three in
lemma rest_high_join (maximal : ∀ z, IsRest G J z → ∃ i : J, ∃ x, G.Adj i.val x ∧ G.Adj z x)
    {i : J} {z x : V} (hz : IsRest G J z) (hx : IsHigh G J i x) : G.Adj z x := by
  obtain ⟨j,y,jy,zy⟩ := maximal z hz
  by_cases hy : IsHigh G J j y
  · exact (rest_high_iff hc ht far three hy hx hz).mp zy
  · exact (rest_low_disjoint hc ht far three hz (Or.inr ⟨jy,hy⟩) zy).elim
end RestClass

section BoundClass
variable [Nontrivial V] {J : Finset V} (hc : G.Connected) (ht : G.largestInducedTreeSize ≤ 4)
variable (far : ∀ i j : J, i ≠ j → Remote G i.val j.val) (three : 3 ≤ Fintype.card J)

lemma branch_cases (J : Finset V) (w : V) :
    IsRest G J w ∨ ∃ i : J, IsLow G J i w ∨ IsHigh G J i w := by
  classical
  by_cases h : IsRest G J w
  · exact Or.inl h
  right
  unfold IsRest at h
  push_neg at h
  obtain ⟨i,hi⟩ := h
  by_cases eq : w=i.val
  · exact ⟨i,Or.inl (Or.inl eq)⟩
  by_cases high : IsHigh G J i w
  · exact ⟨i,Or.inr high⟩
  · exact ⟨i,Or.inl (Or.inr ⟨hi eq,high⟩)⟩

include hc ht far three in
lemma low_boundary {i : J} {x y : V} (lx : IsLow G J i x) (xy : G.Adj x y) (ly : ¬IsLow G J i y) :
    IsHigh G J i y := by
  rcases branch_cases (G:=G) J y with h | ⟨j,lj | hj⟩
  · exact (rest_low_disjoint hc ht far three h lx xy.symm).elim
  · by_cases ij : i=j
    · exact (ly (ij ▸ lj)).elim
    rcases lj with eq | ⟨jy,_⟩
    · exact ((low_misses_index far ij lx).1 (eq ▸ xy.symm)).elim
    · exact (low_away far ij lx jy xy).elim
  · by_cases ij : i=j
    · exact ij ▸ hj
    · exact (low_away far ij lx hj.1 xy).elim

include hc ht far three in
lemma high_size [DecidableRel G.Adj] (i : J) (S : Finset V) (hs : ∀ y, y ∈ S ↔ IsHigh G J i y) :
    G.vertexConnectivity ≤ S.card := by
  classical
  obtain ⟨j,ji,_⟩ := index_third three i i
  have ij := far i j ji.symm
  have ni : i.val ∉ S := fun e => ((hs _).mp e).1.ne rfl
  have nj : j.val ∉ S := fun e => ij.2.1 ((hs _).mp e).1
  rw [vertexConnectivity,if_neg (by have := Fintype.one_lt_card (α := V); omega)]
  refine csInf_le' ⟨S,rfl,Or.inl ?_⟩
  intro hconn
  let a : ↥((S : Set V)ᶜ) := ⟨i.val,ni⟩
  let b : ↥((S : Set V)ᶜ) := ⟨j.val,nj⟩
  obtain ⟨p⟩ := hconn a b
  have ha : IsLow G J i a.val := Or.inl rfl
  have hb : ¬IsLow G J i b.val := by
    rintro (h | ⟨e,_⟩)
    · exact ij.1 h.symm
    · exact ij.2.1 e
  obtain ⟨ed,_,h1,h2⟩ := p.exists_boundary_dart {w | IsLow G J i w.val} ha hb
  exact ed.snd.property ((hs _).mpr (low_boundary hc ht far three h1 ed.adj h2))

def SmallTriple (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

include ht in
lemma smalltriple_of_star (T : Finset V) {o r : V} (ro : G.Adj r o)
    (all : ∀ x ∈ T, x ≠ r ∧ ¬G.Adj r x ∧ G.Adj o x) : SmallTriple G T := by
  classical
  intro a ha b hb c hc ab ac bc
  by_contra! no
  obtain ⟨ar,ra,oa⟩ := all a ha
  obtain ⟨br,rb,ob⟩ := all b hb
  obtain ⟨cr,rc,oc⟩ := all c hc
  let I : Finset V := {r,a,b,c}
  have ind : G.IsIndepSet (I : Set V) := by
    intro x hx y hy ne e
    simp only [I,Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | exact ne rfl | exact ra e | exact rb e | exact rc e | exact ra e.symm | exact rb e.symm | exact rc e.symm |
        exact no.1 e | exact no.1 e.symm | exact no.2.1 e | exact no.2.1 e.symm | exact no.2.2 e | exact no.2.2 e.symm
  have h := independent_neighbors_size o I ind (by
    intro x hx
    simp only [I,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ro.symm
    · exact oa
    · exact ob
    · exact oc)
  have co : I.card=4 := by simp [I,ar.symm,br.symm,cr.symm,ab,ac,bc]
  omega

include hc ht far three in
lemma high_small (i : J) (S : Finset V) (hs : ∀ y ∈ S, IsHigh G J i y) : SmallTriple G S := by
  obtain ⟨j,ji,_⟩ := index_third three i i
  obtain ⟨o,ho⟩ := each_high hc ht far three j
  apply smalltriple_of_star ht S ho.1
  intro x hx
  have ix := hs x hx
  have ij := far i j ji.symm
  exact ⟨fun e => ij.2.1 (e ▸ ix.1),ij.2.2 x ix.1,high_join hc ht far three ji ho ix⟩

include hc ht far three in
lemma rest_small (maximal : ∀ z, IsRest G J z → ∃ i : J, ∃ x, G.Adj i.val x ∧ G.Adj z x)
    (S : Finset V) (hs : ∀ y ∈ S, IsRest G J y) : SmallTriple G S := by
  have nonempty : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨i⟩ := nonempty
  obtain ⟨o,ho⟩ := each_high hc ht far three i
  apply smalltriple_of_star ht S ho.1
  intro x hx
  obtain ⟨xni,nx⟩ := hs x hx i
  exact ⟨xni,nx,(rest_high_join hc ht far three maximal (hs x hx) ho).symm⟩
end BoundClass

structure PathPair (G : SimpleGraph V) (T : Finset V) where
  first : List V
  second : List V
  nodup : (first++second).Nodup
  path₁ : first.IsChain G.Adj
  path₂ : second.IsChain G.Adj
  covers : ∀ x, x ∈ first++second ↔ x ∈ T
  nonempty : 2 ≤ T.card → first ≠ [] ∧ second ≠ []

lemma clique_list_chain {T : Finset V} (c : G.IsClique (T : Set V)) : T.toList.IsChain G.Adj := by
  apply List.Pairwise.isChain
  exact (Finset.nodup_toList T).imp_of_mem (fun hx hy ne =>
    c (Finset.mem_toList.mp hx) (Finset.mem_toList.mp hy) ne)

lemma small_two_cover (T : Finset V) (st : SmallTriple G T) : Nonempty (PathPair G T) := by
  classical
  by_cases emp : T=∅
  · subst T
    exact ⟨⟨[],[],by simp,by simp,by simp,by simp,by simp⟩⟩
  obtain ⟨w,hw⟩ := Finset.nonempty_iff_ne_empty.mpr emp
  let good (p : List V) := p.Nodup ∧ p.IsChain G.Adj ∧ ∀ x ∈ p, x ∈ T
  let P (n : ℕ) := ∃ p : List V, p.length=n ∧ good p
  have one : P 1 := ⟨[w],rfl,by simp,by simp,by simpa using hw⟩
  have size : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨w⟩
  obtain ⟨p,len,nd,pc,sub⟩ := Nat.findGreatest_spec size one
  have atLeast := Nat.le_findGreatest (P:=P) size one
  cases p with
  | nil => simp at len; omega
  | cons a p =>
    let Q := T \ (a::p).toFinset
    have aT : a ∈ T := sub a (by simp)
    have nonneighbor (x : V) (hx : x ∈ Q) : ¬G.Adj x a := by
      intro e
      obtain ⟨xt,nx⟩ := Finset.mem_sdiff.mp hx
      have out : x ∉ a::p := fun h => nx (List.mem_toFinset.mpr h)
      let l := x::a::p
      have ln : l.Nodup := List.nodup_cons.mpr ⟨out,nd⟩
      have g : good l := ⟨ln,List.isChain_cons_cons.mpr ⟨e,pc⟩,by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact xt
        · exact sub v hv⟩
      have larger := Nat.le_findGreatest (P:=P) ln.length_le_card (show P l.length from ⟨l,rfl,g⟩)
      change (a::p).length+1 ≤ _ at larger
      omega
    by_cases qe : Q=∅
    · have exact_mem (x : V) : x ∈ a::p ↔ x ∈ T := by
        refine ⟨sub x,fun ht => ?_⟩
        by_contra no
        have : x ∈ Q := Finset.mem_sdiff.mpr ⟨ht,fun h => no (List.mem_toFinset.mp h)⟩
        simp [qe] at this
      refine ⟨⟨[a],p,nd,by simp,pc.tail,exact_mem,?_⟩⟩
      intro many
      refine ⟨by simp,?_⟩
      rintro rfl
      have sub : T ⊆ {a} := fun x hx => by simpa using (exact_mem x).mpr hx
      have le := Finset.card_le_card sub
      simp at le
      omega
    · have clique : G.IsClique (Q : Set V) := by
        intro x hx y hy xy
        have hxa := nonneighbor x hx
        have hya := nonneighbor y hy
        have ax : a ≠ x := fun e => (Finset.mem_sdiff.mp hx).2 (List.mem_toFinset.mpr (by simp [e]))
        have ay : a ≠ y := fun e => (Finset.mem_sdiff.mp hy).2 (List.mem_toFinset.mpr (by simp [e]))
        rcases st a aT x (Finset.mem_sdiff.mp hx).1 y (Finset.mem_sdiff.mp hy).1 ax ay xy with e | e | e
        · exact (hxa e.symm).elim
        · exact (hya e.symm).elim
        · exact e
      refine ⟨⟨a::p,Q.toList,List.nodup_append.mpr ⟨nd,Finset.nodup_toList _,?_⟩,pc,clique_list_chain clique,?_,?_⟩⟩
      · intro x hx y hy eq
        exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hy)).2 (List.mem_toFinset.mpr (eq ▸ hx))
      · intro x
        simp only [List.mem_append,Finset.mem_toList,Q,Finset.mem_sdiff,List.mem_toFinset]
        tauto
      · intro _
        exact ⟨by simp,fun no => qe (by simpa using congrArg List.toFinset no)⟩

lemma low_not_high {J : Finset V} {i : J} {x : V} (h : IsLow G J i x) : ¬IsHigh G J i x := by
  rcases h with rfl | h
  · exact fun h => h.1.ne rfl
  · exact h.2

lemma branch_in_closed_neighborhood {J : Finset V} {i : J} {x : V} (h : IsLow G J i x ∨ IsHigh G J i x) :
    x=i.val ∨ G.Adj i.val x := by
  rcases h with (h | h) | h
  · exact Or.inl h
  · exact Or.inr h.1
  · exact Or.inr h.1

structure BranchPath (G : SimpleGraph V) (J : Finset V) (i : J) where
  vertices : List V
  nonempty : vertices ≠ []
  nodup : vertices.Nodup
  chain : vertices.IsChain G.Adj
  covers : ∀ x, x ∈ vertices ↔ IsLow G J i x ∨ IsHigh G J i x
  startHigh : ∀ x ∈ vertices.head?, IsHigh G J i x
  endHigh : ∀ x ∈ vertices.getLast?, IsHigh G J i x

lemma branch_path [Nontrivial V] [DecidableRel G.Adj] {J : Finset V}
    (hc : G.Connected) (ht : G.largestInducedTreeSize ≤ 4) (far : ∀ i j : J, i ≠ j → Remote G i.val j.val)
    (three : 3 ≤ Fintype.card J) (hk : 2 ≤ G.vertexConnectivity) (i : J) : Nonempty (BranchPath G J i) := by
  classical
  let H := Finset.univ.filter (IsHigh G J i)
  let L := Finset.univ.filter (IsLow G J i)
  have high (y : V) : y ∈ H ↔ IsHigh G J i y := by simp [H]
  have low (y : V) : y ∈ L.toList ↔ IsLow G J i y := by simp [L]
  obtain ⟨C⟩ := small_two_cover H (high_small hc ht far three i H (fun y h => (high y).mp h))
  have highMem (y : V) : y ∈ C.first ∨ y ∈ C.second ↔ IsHigh G J i y := by
    rw [← List.mem_append,C.covers,high]
  obtain ⟨fne,sne⟩ := C.nonempty (hk.trans (high_size hc ht far three i H high))
  have lne : L.toList ≠ [] := List.ne_nil_of_mem ((low _).mpr (Or.inl rfl : IsLow G J i i.val))
  have lc : L.toList.IsChain G.Adj := clique_list_chain (by
    intro x hx y hy ne
    exact low_clique hc ht far three i ((Finset.mem_filter.mp hx).2) ((Finset.mem_filter.mp hy).2) ne)
  have fHigh (x : V) (hx : x ∈ C.first) := (highMem x).mp (Or.inl hx)
  have sHigh (x : V) (hx : x ∈ C.second) := (highMem x).mp (Or.inr hx)
  let m := C.first ++ L.toList
  have p₁ : m.IsChain G.Adj := C.path₁.append lc (fun x hx y hy =>
    low_high ht far (fHigh x (List.mem_of_mem_getLast? hx)) ((low y).mp (List.mem_of_mem_head? hy)))
  have mne : m ≠ [] := by simp [m,lne]
  have last : m.getLast?=L.toList.getLast? := List.getLast?_append_of_ne_nil _ lne
  have first : m.head?=C.first.head? := List.head?_append_of_ne_nil _ fne
  let l := m++C.second
  have ch : l.IsChain G.Adj := p₁.append C.path₂ (by
    intro x hx y hy
    rw [last] at hx
    exact (low_high ht far (sHigh y (List.mem_of_mem_head? hy)) ((low x).mp (List.mem_of_mem_getLast? hx))).symm)
  have separate (x : V) (hx : x ∈ L.toList) {y : V} (hy : IsHigh G J i y) : x ≠ y :=
    fun e => low_not_high ((low x).mp hx) (e ▸ hy)
  obtain ⟨nf,ns,between⟩ := List.nodup_append.mp C.nodup
  have mn : m.Nodup := List.nodup_append.mpr ⟨nf,Finset.nodup_toList _,fun x hx y hy =>
    (separate y hy (fHigh x hx)).symm⟩
  have ln : l.Nodup := List.nodup_append.mpr ⟨mn,ns,by
    intro x hx y hy
    rcases List.mem_append.mp hx with hx | hx
    · exact between _ hx _ hy
    · exact separate x hx (sHigh y hy)⟩
  refine ⟨⟨l,by simp [l,sne],ln,ch,?_,?_,?_⟩⟩
  · intro x
    simp only [l,m,List.mem_append,low,←highMem]
    tauto
  · intro x hx
    rw [show l.head?=m.head? from List.head?_append_of_ne_nil _ mne,first] at hx
    exact fHigh x (List.mem_of_mem_head? hx)
  · intro x hx
    rw [show l.getLast?=C.second.getLast? from List.getLast?_append_of_ne_nil _ sne] at hx
    exact sHigh x (List.mem_of_mem_getLast? hx)

lemma first_in_block {W : Type*} (F : W → List V) (ord : List W) (hne : ∀ i, F i ≠ [])
    {v : V} (hv : v ∈ (ord.flatMap F).head?) : ∃ i ∈ ord, v ∈ (F i).head? := by
  cases ord with
  | nil => simp at hv
  | cons i t =>
    rw [List.flatMap_cons,List.head?_append_of_ne_nil _ (hne i)] at hv
    exact ⟨i,by simp,hv⟩

lemma trace_remote_packing [Nontrivial V] [DecidableRel G.Adj] {J : Finset V}
    (hc : G.Connected) (ht : G.largestInducedTreeSize ≤ 4) (far : ∀ i j : J, i ≠ j → Remote G i.val j.val)
    (three : 3 ≤ Fintype.card J) (hk : 2 ≤ G.vertexConnectivity)
    (maximal : ∀ z, IsRest G J z → ∃ i : J, ∃ x, G.Adj i.val x ∧ G.Adj z x) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let F (i : J) := (branch_path hc ht far three hk i).some
  let ord := (Finset.univ : Finset J).toList
  let m := ord.flatMap (fun i => (F i).vertices)
  have om (i : J) : i ∈ ord := by simp [ord]
  have sep (i j : J) (ne : i ≠ j) : (F i).vertices.Disjoint (F j).vertices := by
    apply List.disjoint_left.mpr
    intro x hx hy
    have a := branch_in_closed_neighborhood ((F i).covers x |>.mp hx)
    have b := branch_in_closed_neighborhood ((F j).covers x |>.mp hy)
    have ij := far i j ne
    rcases a with a | a <;> rcases b with b | b
    · exact ij.1 (a.symm.trans b)
    · exact ij.2.1 (a ▸ b.symm)
    · exact ij.2.1 (b ▸ a)
    · exact ij.2.2 x a b
  have ⟨mn,mc⟩ := chain_blocks (fun i => (F i).vertices) ord (Finset.nodup_toList _)
    (fun i => (F i).nonempty) (fun i => (F i).nodup) (fun i => (F i).chain) sep
    (fun _ _ ij u hu v hv => high_join hc ht far three ij ((F _).endHigh u hu) ((F _).startHigh v hv))
  have mcover (x : V) : x ∈ m ↔ ∃ i : J, IsLow G J i x ∨ IsHigh G J i x := by
    simp only [m,List.mem_flatMap,om,true_and]
    exact exists_congr (fun i => (F i).covers x)
  have mne : m ≠ [] := by
    obtain ⟨i⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card J)
    exact List.ne_nil_of_mem ((mcover _).mpr ⟨i,Or.inl (Or.inl rfl)⟩)
  let Z := Finset.univ.filter (IsRest G J)
  have zm (v : V) : v ∈ Z ↔ IsRest G J v := by simp [Z]
  obtain ⟨C⟩ := small_two_cover Z (rest_small hc ht far three maximal Z (fun x h => (zm _).mp h))
  have zcover (x : V) : x ∈ C.first ∨ x ∈ C.second ↔ IsRest G J x := by rw [←List.mem_append,C.covers,zm]
  have exc (z : V) (hz : IsRest G J z) {x : V} (hx : x ∈ m) : z ≠ x := by
    rintro rfl
    obtain ⟨i,hi⟩ := (mcover z).mp hx
    rcases branch_in_closed_neighborhood hi with e | e
    · exact (hz i).1 e
    · exact (hz i).2 e
  let mid := C.first++m
  have mc' : mid.IsChain G.Adj := C.path₁.append mc (by
    intro x hx y hy
    obtain ⟨j,_,hj⟩ := first_in_block _ ord (fun i => (F i).nonempty) hy
    exact rest_high_join hc ht far three maximal ((zcover x).mp (Or.inl (List.mem_of_mem_getLast? hx))) ((F j).startHigh y hj))
  let l := mid++C.second
  have ch : l.IsChain G.Adj := mc'.append C.path₂ (by
    intro x hx y hy
    rw [show mid.getLast?=m.getLast? from List.getLast?_append_of_ne_nil _ mne] at hx
    obtain ⟨j,_,hj⟩ := last_in_block _ ord _ hx
    exact (rest_high_join hc ht far three maximal ((zcover y).mp (Or.inr (List.mem_of_mem_head? hy))) ((F j).endHigh x hj)).symm)
  obtain ⟨nf,ns,dis⟩ := List.nodup_append.mp C.nodup
  have midn : mid.Nodup := List.nodup_append.mpr ⟨nf,mn,fun x hx _ hy => exc x ((zcover x).mp (Or.inl hx)) hy⟩
  have nd : l.Nodup := List.nodup_append.mpr ⟨midn,ns,by
    intro x hx y hy
    rcases List.mem_append.mp hx with hx | hx
    · exact dis x hx y hy
    · exact (exc y ((zcover y).mp (Or.inr hy)) hx).symm⟩
  apply path_from_spanning_list l (by simp [l,mid,mne]) nd ch
  intro v
  have h := branch_cases (G:=G) J v
  rw [←zcover,←mcover] at h
  simp only [l,mid,List.mem_append]
  tauto


def RemoteSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Remote G i j

lemma trace_remote_set [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected) (ht : G.largestInducedTreeSize ≤ 4)
    (hk : 2 ≤ G.vertexConnectivity) (T : Finset V) (rt : RemoteSet G T) (three : 3 ≤ T.card) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let F := Finset.univ.filter (RemoteSet G)
  have mem (U : Finset V) : U ∈ F ↔ RemoteSet G U := by simp [F]
  obtain ⟨J,hJ,max⟩ := Finset.exists_max_image F Finset.card ⟨T,(mem T).mpr rt⟩
  have far := (mem J).mp hJ
  apply trace_remote_packing (J:=J) hc ht (fun i j ne => far _ i.property _ j.property (fun e => ne (Subtype.ext e)))
    (by simpa using three.trans (max T ((mem T).mpr rt))) hk
  intro z hz
  by_contra! no
  have out : z ∉ J := fun h => (hz ⟨z,h⟩).1 rfl
  have extra (i : V) (hi : i ∈ J) : Remote G i z := by
    let j : J := ⟨i,hi⟩
    exact ⟨(hz j).1.symm,(hz j).2,no j⟩
  have extended : RemoteSet G (insert z J) := by
    intro i hi j hj ij
    rcases Finset.mem_insert.mp hi with ei | hI <;> rcases Finset.mem_insert.mp hj with ej | hJ
    · exact (ij (ei.trans ej.symm)).elim
    · rw [ei]; exact remote_flip (extra _ hJ)
    · rw [ej]; exact extra _ hI
    · exact far _ hI _ hJ ij
  have bound := max _ ((mem _).mpr extended)
  rw [Finset.card_insert_of_notMem out] at bound
  omega

lemma adjacent_rows_four [DecidableRel G.Adj]
    (ht : G.largestInducedTreeSize ≤ 4) (I : Finset V)
    (hi : G.IsIndepSet (I : Set V))
    {a c : V} (ha : a ∉ I) (hc : c ∉ I) (e : G.Adj a c) 
 :
    (I.filter (G.Adj a) \ I.filter (G.Adj c)).card + (I.filter (G.Adj c) \ I.filter (G.Adj a)).card ≤ 2 := by
  by_cases hne : c=a
  · simp [hne]
  let R (c : V) := I.filter (G.Adj c)
  have independent (T : Finset V) (sub : T ⊆ I) : G.IsIndepSet (T : Set V) :=
    fun _ h _ h' => hi (sub h) (sub h')
  let P := R a \ R c
  let Q := R c \ R a
  have inside : P ∪ Q ⊆ I := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz <;> exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).1
  have h1 : a ∉ P ∪ Q := fun hz => ha (inside hz)
  have h2 : c ∉ P ∪ Q := fun hz => hc (inside hz)
  have separate (z : V) (hz : z ∈ P ∪ Q) : (G.Adj a z ∧ ¬G.Adj c z) ∨ (G.Adj c z ∧ ¬G.Adj a z) := by
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨hra,hrc⟩ := Finset.mem_sdiff.mp hz
      obtain ⟨hi,haz⟩ := Finset.mem_filter.mp hra
      exact Or.inl ⟨haz,fun h => hrc (Finset.mem_filter.mpr ⟨hi,h⟩)⟩
    · obtain ⟨hrc,hra⟩ := Finset.mem_sdiff.mp hz
      obtain ⟨hi,hcz⟩ := Finset.mem_filter.mp hrc
      exact Or.inr ⟨hcz,fun h => hra (Finset.mem_filter.mpr ⟨hi,h⟩)⟩
  have card := double_star_size e _ (independent _ inside) h1 h2 separate
  have dis : Disjoint P Q := Finset.disjoint_left.mpr fun _ hp hq => (Finset.mem_sdiff.mp hp).2 (Finset.mem_sdiff.mp hq).1
  rw [Finset.card_union_of_disjoint dis] at card
  change P.card+Q.card ≤ 2
  omega

lemma touching_rows_four [DecidableRel G.Adj] (ht : G.largestInducedTreeSize ≤ 4)
    (I : Finset V) (hi : G.IsIndepSet (I : Set V)) {a b : V} {w : V}
    (wi : w ∈ I) (aw : G.Adj a w) (bw : G.Adj b w) :
    (I.filter (G.Adj a) \ I.filter (G.Adj b)).card+(I.filter (G.Adj b) \ I.filter (G.Adj a)).card ≤ 2 := by
  by_cases same : a=b
  · simp [same]
  by_cases e : G.Adj a b
  · exact adjacent_rows_four ht I hi (fun ha => hi ha wi aw.ne aw) (fun hb => hi hb wi bw.ne bw) e
  have no : I.filter (G.Adj w)=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun y hy =>
    hi wi (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2.ne (Finset.mem_filter.mp hy).2)
  have bnd := path3_rows I hi aw bw.symm e same
  dsimp only at bnd
  rw [no,Finset.sdiff_empty,Finset.card_union_of_disjoint (Finset.disjoint_left.mpr
    (fun _ ha hb => (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1))] at bnd
  omega

lemma disjoint_row_conflict [DecidableRel G.Adj] (ht : G.largestInducedTreeSize ≤ 4)
    (I : Finset V) (hi : G.IsIndepSet (I : Set V)) {a b : V} (e : G.Adj a b)
    (large : 2 ≤ (I.filter (G.Adj a)).card) {j : V} (ji : j ∈ I) (bj : G.Adj b j)
    (dis : ∀ w ∈ I.filter (G.Adj a), ¬G.Adj b w) : False := by
  let A := I.filter (G.Adj a)
  let B := I.filter (G.Adj b)
  have na : a ∉ I := by
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (by omega : 0 < (I.filter (G.Adj a)).card)
    obtain ⟨ui,au⟩ := Finset.mem_filter.mp hu
    exact fun ai => hi ai ui au.ne au
  have nb : b ∉ I := fun bi => hi bi ji bj.ne bj
  have d : Disjoint A B := Finset.disjoint_left.mpr (fun w hw hb => dis w hw (Finset.mem_filter.mp hb).2)
  have bound := adjacent_rows_four ht I hi na nb e
  change (A \ B).card+(B \ A).card ≤ 2 at bound
  rw [Finset.sdiff_eq_self_of_disjoint d,Finset.sdiff_eq_self_of_disjoint d.symm] at bound
  have pos := Finset.card_pos.mpr (show B.Nonempty from ⟨j,Finset.mem_filter.mpr ⟨ji,bj⟩⟩)
  change 2 ≤ A.card at large
  omega

lemma exterior_mixed_row [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected) (ht : G.largestInducedTreeSize ≤ 4)
    (I : Finset V) (hi : G.IsIndepSet (I : Set V)) {a : V} (large : 2 ≤ (I.filter (G.Adj a)).card)
    {j : V} (ji : j ∈ I) (aj : ¬G.Adj a j) : ∃ b, G.Adj b j ∧ ∃ w ∈ I.filter (G.Adj a), G.Adj b w := by
  classical
  by_contra! no
  have aout : a ∉ I := by
    obtain ⟨w,hw⟩ := Finset.card_pos.mp (by omega : 0 < (I.filter (G.Adj a)).card)
    obtain ⟨wi,aw⟩ := Finset.mem_filter.mp hw
    exact fun ai => hi ai wi aw.ne aw
  have remote : Remote G a j := by
    refine ⟨fun e => aout (e ▸ ji),aj,?_⟩
    intro b ab jb
    exact disjoint_row_conflict ht I hi ab large ji jb.symm (no b jb.symm)
  obtain ⟨u,v,au,uv,jv⟩ := remote_edge hc ht remote
  have rowA (w : V) (wa : w ∈ I.filter (G.Adj a)) : G.Adj u w := by
    obtain ⟨wi,aw⟩ := Finset.mem_filter.mp wa
    have vw := no v jv.symm w (Finset.mem_filter.mpr ⟨wi,aw⟩)
    have jw : ¬G.Adj j w := fun e => hi ji wi e.ne e
    by_contra uw
    apply cross_single ht remote au uv jv ⟨aw.ne.symm,fun e => vw (e ▸ uv.symm),fun e => jw (e ▸ jv),fun e => aj (e ▸ aw)⟩
    refine ⟨a,⟨by tauto,aw.symm⟩,?_⟩
    rintro t ⟨h,e⟩
    rcases h with rfl | rfl | rfl | rfl
    · rfl
    · exact (uw e.symm).elim
    · exact (vw e.symm).elim
    · exact (jw e.symm).elim
  -- Use the original large row and the single label j as exclusive leaves
  -- at the adjacent vertices u,v. The fact that u misses j follows from remoteness.
  let A := I.filter (G.Adj a)
  let B := I.filter (G.Adj u)
  let D := I.filter (G.Adj v)
  have uout : u ∉ I := by
    obtain ⟨w,hw⟩ := Finset.card_pos.mp (by omega : 0 < (I.filter (G.Adj a)).card)
    exact fun h => hi h (Finset.mem_filter.mp hw).1 (rowA w hw).ne (rowA w hw)
  have vout : v ∉ I := fun h => hi ji h jv.ne jv
  have bound := adjacent_rows_four ht I hi uout vout uv
  change (B \ D).card+(D \ B).card ≤ 2 at bound
  have sub : A ⊆ B \ D := fun w hw => Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,rowA w hw⟩,
    fun h => no v jv.symm w hw (Finset.mem_filter.mp h).2⟩
  have pos := Finset.card_pos.mpr (show (D \ B).Nonempty from ⟨j,Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨ji,jv.symm⟩,
    fun h => remote.2.2 u au (Finset.mem_filter.mp h).2.symm⟩⟩)
  have count := Finset.card_le_card sub
  change 2 ≤ A.card at large
  omega

lemma remote_of_five_independent [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected)
    (ht : G.largestInducedTreeSize ≤ 4) (I : Finset V) (hi : G.IsIndepSet (I : Set V)) (five : 5 ≤ I.card) :
    ∃ J : Finset V, 3 ≤ J.card ∧ ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Remote G i j := by
  classical
  let R (v : V) := I.filter (G.Adj v)
  obtain ⟨a,_,max⟩ := Finset.exists_max_image Finset.univ (fun v : V => (R v).card) Finset.univ_nonempty
  let A := R a
  let E := I \ A
  have mx (v : V) : (R v).card ≤ A.card := max _ (Finset.mem_univ _)
  have bound (u v : V) : (R u ∪ R v).card ≤ A.card+1 := row_distance_packing hc ht I hi A.card mx u v
  have aI : A ⊆ I := Finset.filter_subset _ _
  have size : A.card ≤ 3 := by
    have h := independent_neighbors_size a A (fun _ h _ h' => hi (aI h) (aI h'))
      (fun x hx => (Finset.mem_filter.mp hx).2)
    omega
  have ecard : E.card+A.card=I.card := Finset.card_sdiff_add_card_eq_card aI
  have exterior (v : V) : (R v \ A).card ≤ 1 := by
    have h := bound v a
    change (R v ∪ A).card ≤ A.card+1 at h
    have eq := Finset.card_sdiff_add_card (R v) A
    omega
  have rE (u : V) (hu : u ∈ E) (v : V) (hv : v ∈ E) (ne : u ≠ v) : Remote G u v := by
    obtain ⟨ui,ua⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨vi,va⟩ := Finset.mem_sdiff.mp hv
    refine ⟨ne,hi ui vi ne,?_⟩
    intro x ux vx
    have um : u ∈ R x \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨ui,ux.symm⟩,ua⟩
    have vm : v ∈ R x \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨vi,vx.symm⟩,va⟩
    have sub : ({u,v} : Finset V) ⊆ R x \ A := by simpa [Finset.insert_subset_iff] using And.intro um vm
    have bc := Finset.card_le_card sub
    simp [ne] at bc
    have h := exterior x
    omega
  by_cases plenty : 3 ≤ E.card
  · exact ⟨E,plenty,rE⟩
  have ea : E.card=2 := by omega
  have aa : 2 ≤ A.card := by omega
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < E.card)
  have ecount := Finset.card_erase_of_mem hx
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (by omega : 0 < (E.erase x).card)
  obtain ⟨yx,hy⟩ := Finset.mem_erase.mp hy
  have mixed {j b w : V} (ej : j ∈ E) (bj : G.Adj b j) (wa : w ∈ A) (bw : G.Adj b w) :
      ∃ t ∈ A, t ∉ R b ∧ R b=insert j (A.erase t) := by
    obtain ⟨ji,ja⟩ := Finset.mem_sdiff.mp ej
    obtain ⟨wi,aw⟩ := Finset.mem_filter.mp wa
    exact row_replacement (touching_rows_four ht I hi wi aw bw) (mx b) (Finset.mem_filter.mpr ⟨ji,bj⟩) ja
  have full (j : V) (ej : j ∈ E) : ∃ b t, t ∈ A ∧ R b=insert j (A.erase t) := by
    obtain ⟨ji,ja⟩ := Finset.mem_sdiff.mp ej
    obtain ⟨b,bj,w,wa,bw⟩ := exterior_mixed_row hc ht I hi aa ji (fun aj => ja (Finset.mem_filter.mpr ⟨ji,aj⟩))
    obtain ⟨t,ta,_,e⟩ := mixed ej bj wa bw
    exact ⟨b,t,ta,e⟩
  have fcard {j t b : V} (ej : j ∈ E) (ta : t ∈ A) (h : R b=insert j (A.erase t)) : (R b).card=A.card := by
    have ja := (Finset.mem_sdiff.mp ej).2
    rw [h,Finset.card_insert_of_notMem (fun h => ja (Finset.mem_erase.mp h).2),Finset.card_erase_of_mem ta]
    omega
  have agree {j k b d t w : V} (ej : j ∈ E) (ek : k ∈ E) (jk : j ≠ k) (ta : t ∈ A) (wa : w ∈ A)
      (brow : R b=insert j (A.erase t)) (drow : R d=insert k (A.erase w)) : t=w := by
    have bu := bound b d
    have ub := bound d b
    have b1 := Finset.card_sdiff_add_card (R b) (R d)
    have b2 := Finset.card_sdiff_add_card (R d) (R b)
    have cb := fcard ej ta brow
    have cd := fcard ek wa drow
    exact replacement_omissions (Finset.mem_sdiff.mp ej).2 (Finset.mem_sdiff.mp ek).2 ta wa jk brow drow (by omega)
  obtain ⟨c,z,za,crow⟩ := full x hx
  obtain ⟨d,w,wa,drow⟩ := full y hy
  have zw := agree hx hy yx.symm za wa crow drow
  subst w
  have rz (j : V) (ej : j ∈ E) : Remote G z j := by
    obtain ⟨ji,ja⟩ := Finset.mem_sdiff.mp ej
    have zj : z ≠ j := fun h => ja (h ▸ za)
    refine ⟨zj,hi (aI za) ji zj,?_⟩
    intro b zb jb
    obtain ⟨t,ta,tn,brow⟩ := mixed ej jb.symm za zb.symm
    have tz : t=z := by
      by_cases jx : j=x
      · exact agree ej hy (jx ▸ yx.symm) ta za brow drow
      · exact agree ej hx jx ta za brow crow
    exact tn (Finset.mem_filter.mpr ⟨tz ▸ aI za,tz ▸ zb.symm⟩)
  have zo : z ∉ E := fun ze => (Finset.mem_sdiff.mp ze).2 za
  refine ⟨insert z E,by rw [Finset.card_insert_of_notMem zo,ea],?_⟩
  intro i hi j hj ij
  rcases Finset.mem_insert.mp hi with ei | hI <;> rcases Finset.mem_insert.mp hj with ej | hJ
  · exact (ij (ei.trans ej.symm)).elim
  · rw [ei]; exact rz _ hJ
  · rw [ej]; exact remote_flip (rz _ hI)
  · exact rE _ hI _ hJ ij


section PairClass
variable [Nontrivial V] {J : Finset V} (hc : G.Connected) (ht : G.largestInducedTreeSize ≤ 4)
variable (far : ∀ i j : J, i ≠ j → Remote G i.val j.val) (two : 2 ≤ Fintype.card J)

lemma another_of_two {W : Type*} [Fintype W] (two : 2 ≤ Fintype.card W) (i : W) : ∃ j, j ≠ i := by
  letI : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp two
  exact exists_ne i

include hc ht far in
lemma cross_representatives {i j : J} (ij : i ≠ j) :
    ∃ x y, IsHigh G J i x ∧ IsHigh G J j y ∧ G.Adj x y := by
  obtain ⟨x,y,ix,xy,jy⟩ := remote_edge hc ht (far i j ij)
  exact ⟨x,y,⟨ix,j,ij,y,jy,xy⟩,⟨jy,i,ij.symm,x,ix,xy.symm⟩,xy⟩

include ht far in
lemma rest_same_high {i : J} {z x y : V} (rz : IsRest G J z) (hx : IsHigh G J i x) (hy : IsHigh G J i y)
    (zx : G.Adj z x) : G.Adj z y := by
  obtain ⟨iy,k,ik,d,kd,yd⟩ := hy
  have f := far i k ik
  have external {a b : V} (ia : G.Adj i.val a) (ab : G.Adj a b) (kb : G.Adj k.val b) : G.Adj z a ↔ G.Adj z b :=
    cross_parallel ht f ia ab kb (rz i).1 (rz k).1 (fun e => (rz i).2 e.symm) (fun e => (rz k).2 e.symm)
  by_contra zy
  have zd := fun e => zy ((external iy yd kd).mpr e)
  have xd : ¬G.Adj x d := fun e => zd ((external hx.1 e kd).mp zx)
  have yx := cross_sibling ht (remote_flip f) kd yd.symm iy hx.1 (fun e => xd e.symm)
  exact no_induced_five_path ht zx yx.symm yd kd.symm zy zd (fun e => (rz k).2 e.symm) xd
    (fun e => f.2.2 x hx.1 e.symm) (fun e => f.2.2 y iy e.symm)

include hc ht far in
lemma rest_high_transfer {i j : J} {z x y : V} (rz : IsRest G J z) (hx : IsHigh G J i x) (hy : IsHigh G J j y)
    (zx : G.Adj z x) : G.Adj z y := by
  by_cases same : i=j
  · subst j; exact rest_same_high ht far rz hx hy zx
  obtain ⟨a,b,ha,hb,ab⟩ := cross_representatives hc ht far same
  have za := rest_same_high ht far rz hx ha zx
  have zb := (cross_parallel ht (far i j same) ha.1 ab hb.1 (rz i).1 (rz j).1
    (fun e => (rz i).2 e.symm) (fun e => (rz j).2 e.symm)).mp za
  exact rest_same_high ht far rz hb hy zb

include hc ht far two in
lemma high_small_two (i : J) (S : Finset V) (hs : ∀ y ∈ S, IsHigh G J i y) : SmallTriple G S := by
  intro a ha b hb c hc' ab ac bc
  by_contra! no
  obtain ⟨ia,j,ij,w,jw,aw⟩ := hs a ha
  have ib := (hs b hb).1
  have ic := (hs c hc').1
  have f := far i j ij
  have wb : G.Adj w b := by
    by_contra n
    exact no.1 (cross_sibling ht (remote_flip f) jw aw.symm ia ib n)
  have wc : G.Adj w c := by
    by_contra n
    exact no.2.1 (cross_sibling ht (remote_flip f) jw aw.symm ia ic n)
  let T : Finset V := {a,b,c}
  have triple : SmallTriple G T := smalltriple_of_star ht T jw (by
    intro t ht'
    have adjacent (t : V) (it : G.Adj i.val t) (wt : G.Adj w t) :
        t ≠ j.val ∧ ¬G.Adj j.val t ∧ G.Adj w t := ⟨fun e => f.2.1 (e ▸ it),f.2.2 t it,wt⟩
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at ht'
    rcases ht' with rfl | rfl | rfl
    · exact adjacent _ ia aw.symm
    · exact adjacent _ ib wb
    · exact adjacent _ ic wc)
  rcases triple a (by simp [T]) b (by simp [T]) c (by simp [T]) ab ac bc with e | e | e
  · exact no.1 e
  · exact no.2.1 e
  · exact no.2.2 e
include hc ht far two in
lemma low_clique_two (i : J) {z w : V} (lz : IsLow G J i z) (lw : IsLow G J i w) (zw : z ≠ w) :
    G.Adj z w := by
  obtain ⟨j,ji⟩ := another_of_two two i
  obtain ⟨x,y,hx,hy,xy⟩ := cross_representatives hc ht far ji.symm
  have yx := xy.symm
  have xz := low_high ht far hx lz
  have xw := low_high ht far hx lw
  have zy := low_away far ji.symm lz hy.1
  have wy := low_away far ji.symm lw hy.1
  have ⟨jz,zj'⟩ := low_misses_index far ji.symm lz
  have ⟨jw,wj'⟩ := low_misses_index far ji.symm lw
  have jx : ¬G.Adj j.val x := (far i j ji.symm).2.2 x hx.1
  have jx' : j.val ≠ x := fun e => (far i j ji.symm).2.1 (e ▸ hx.1)
  have yz' : y ≠ z := fun e => jz (e ▸ hy.1)
  by_contra no
  apply p4_single ht hy.1 yx xz jx (fun e => zy e.symm) jz jx' yz' zj'.symm
    ⟨wj',fun e => jw (e ▸ hy.1),xw.ne.symm,zw.symm⟩
  refine ⟨x,⟨by tauto,xw.symm⟩,?_⟩
  rintro t ⟨h,e⟩
  rcases h with rfl | rfl | rfl | rfl
  · exact (jw e.symm).elim
  · exact (wy e).elim
  · rfl
  · exact (no e.symm).elim

include hc ht far two in
lemma rest_low_disjoint_two {i : J} {z l : V} (hz : IsRest G J z) (hl : IsLow G J i l) :
    ¬G.Adj z l := by
  intro zl
  have il : G.Adj i.val l := by
    rcases hl with rfl | h
    · exact ((hz i).2 zl.symm).elim
    · exact h.1
  obtain ⟨j,ji⟩ := another_of_two two i
  obtain ⟨x,y,hx,hy,xy⟩ := cross_representatives hc ht far ji.symm
  have xl := low_high ht far hx hl
  have ly := low_away far ji.symm hl hy.1
  have jl := (low_misses_index far ji.symm hl).1
  have jx := (far i j ji.symm).2.2 x hx.1
  have zy : G.Adj z y := by
    by_contra zy
    have zx : ¬G.Adj z x := fun e => zy (rest_high_transfer hc ht far hz hx hy e)
    exact no_induced_five_path ht zl xl.symm xy hy.1.symm zx zy (fun e => (hz j).2 e.symm)
      ly (fun e => jl e.symm) (fun e => jx e.symm)
  exact no_induced_five_path ht il zl.symm zy hy.1.symm (hz i).2 ((far j i ji).2.2 y hy.1)
    (far i j ji.symm).2.1 ly (fun e => jl e.symm) (fun e => (hz j).2 e.symm)


include hc ht far two in
lemma rest_high_join_two (maximal : ∀ z, IsRest G J z → ∃ i : J, ∃ x, G.Adj i.val x ∧ G.Adj z x)
    {i : J} {z x : V} (hz : IsRest G J z) (hx : IsHigh G J i x) : G.Adj z x := by
  obtain ⟨j,y,jy,zy⟩ := maximal z hz
  by_cases hy : IsHigh G J j y
  · exact rest_high_transfer hc ht far hz hy hx zy
  · exact (rest_low_disjoint_two hc ht far two hz (Or.inr ⟨jy,hy⟩) zy).elim

include hc ht far two in
lemma low_boundary_two {i : J} {x y : V} (lx : IsLow G J i x) (xy : G.Adj x y) (ly : ¬IsLow G J i y) :
    IsHigh G J i y := by
  rcases branch_cases (G:=G) J y with h | ⟨j,lj | hj⟩
  · exact (rest_low_disjoint_two hc ht far two h lx xy.symm).elim
  · by_cases ij : i=j
    · exact (ly (ij ▸ lj)).elim
    rcases lj with eq | ⟨jy,_⟩
    · exact ((low_misses_index far ij lx).1 (eq ▸ xy.symm)).elim
    · exact (low_away far ij lx jy xy).elim
  · by_cases ij : i=j
    · exact ij ▸ hj
    · exact (low_away far ij lx hj.1 xy).elim


include hc ht far two in
lemma high_size_two [DecidableRel G.Adj] (i : J) (S : Finset V) (hs : ∀ y, y ∈ S ↔ IsHigh G J i y) :
    G.vertexConnectivity ≤ S.card := by
  classical
  obtain ⟨j,ji⟩ := another_of_two two i
  have ij := far i j ji.symm
  have ni : i.val ∉ S := fun e => ((hs _).mp e).1.ne rfl
  have nj : j.val ∉ S := fun e => ij.2.1 ((hs _).mp e).1
  rw [vertexConnectivity,if_neg (by have := Fintype.one_lt_card (α := V); omega)]
  refine csInf_le' ⟨S,rfl,Or.inl ?_⟩
  intro hconn
  let a : ↥((S : Set V)ᶜ) := ⟨i.val,ni⟩
  let b : ↥((S : Set V)ᶜ) := ⟨j.val,nj⟩
  obtain ⟨p⟩ := hconn a b
  have ha : IsLow G J i a.val := Or.inl rfl
  have hb : ¬IsLow G J i b.val := by
    rintro (h | ⟨e,_⟩)
    · exact ij.1 h.symm
    · exact ij.2.1 e
  obtain ⟨ed,_,h1,h2⟩ := p.exists_boundary_dart {w | IsLow G J i w.val} ha hb
  exact ed.snd.property ((hs _).mpr (low_boundary_two hc ht far two h1 ed.adj h2))


include hc ht far two in
lemma rest_small_two (maximal : ∀ z, IsRest G J z → ∃ i : J, ∃ x, G.Adj i.val x ∧ G.Adj z x)
    (S : Finset V) (hs : ∀ y ∈ S, IsRest G J y) : SmallTriple G S := by
  have nonempty : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨i⟩ := nonempty
  obtain ⟨j,ji⟩ := another_of_two two i
  obtain ⟨o,_,ho,_,_⟩ := cross_representatives hc ht far ji.symm
  apply smalltriple_of_star ht S ho.1
  intro x hx
  obtain ⟨xni,nx⟩ := hs x hx i
  exact ⟨xni,nx,(rest_high_join_two hc ht far two maximal (hs x hx) ho).symm⟩

end PairClass

lemma rooted_two_cover (T : Finset V) (st : SmallTriple G T) (many : 2 ≤ T.card)
    (w : V) (hw : w ∈ T) : ∃ C : PathPair G T, C.first.head?=some w := by
  classical
  let good (p : List V) := p.Nodup ∧ p.IsChain G.Adj ∧ p.getLast?=some w ∧ ∀ x ∈ p, x ∈ T
  let P (n : ℕ) := ∃ p : List V, p.length=n ∧ good p
  have one : P 1 := ⟨[w],rfl,by simp,by simp,rfl,by simpa using hw⟩
  have size : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨w⟩
  obtain ⟨p,len,nd,pc,last,sub⟩ := Nat.findGreatest_spec size one
  have atLeast := Nat.le_findGreatest (P:=P) size one
  cases p with
  | nil => simp at len; omega
  | cons a p =>
    let Q := T \ (a::p).toFinset
    have aT : a ∈ T := sub a (by simp)
    have nonneighbor (x : V) (hx : x ∈ Q) : ¬G.Adj x a := by
      intro e
      obtain ⟨xt,nx⟩ := Finset.mem_sdiff.mp hx
      have out : x ∉ a::p := fun h => nx (List.mem_toFinset.mpr h)
      let l := x::a::p
      have ln : l.Nodup := List.nodup_cons.mpr ⟨out,nd⟩
      have g : good l := ⟨ln,List.isChain_cons_cons.mpr ⟨e,pc⟩,by simpa [l] using last,by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact xt
        · exact sub v hv⟩
      have larger := Nat.le_findGreatest (P:=P) ln.length_le_card (show P l.length from ⟨l,rfl,g⟩)
      change (a::p).length+1 ≤ _ at larger
      omega
    by_cases qe : Q=∅
    · have exact_mem (x : V) : x ∈ a::p ↔ x ∈ T := by
        refine ⟨sub x,fun ht => ?_⟩
        by_contra no
        have : x ∈ Q := Finset.mem_sdiff.mpr ⟨ht,fun h => no (List.mem_toFinset.mp h)⟩
        simp [qe] at this
      have pne : p ≠ [] := by
        rintro rfl
        have sub : T ⊆ {a} := fun x hx => by simpa using (exact_mem x).mpr hx
        have le := Finset.card_le_card sub
        simp at le
        omega
      have head : p.reverse.head?=some w := by
        rw [List.head?_reverse,←List.getLast?_cons_of_ne_nil (x:=a) pne]
        exact last
      refine ⟨⟨p.reverse,[a],?_,List.isChain_reverse.mpr (pc.tail.imp (fun _ _ e => e.symm)),by simp,?_,?_⟩,head⟩
      · exact List.nodup_append.mpr ⟨(by simpa using (List.nodup_cons.mp nd).2),by simp,by
          intro x hx y hy eq
          have ya : y=a := by simpa using hy
          exact (List.nodup_cons.mp nd).1 ((eq.trans ya) ▸ List.mem_reverse.mp hx)⟩
      · intro x
        simp only [List.mem_append,List.mem_reverse,List.mem_singleton,←exact_mem,List.mem_cons]
        tauto
      · exact fun _ => ⟨fun h => pne (by simpa using congrArg List.reverse h),by simp⟩
    · have clique : G.IsClique (Q : Set V) := by
        intro x hx y hy xy
        have hxa := nonneighbor x hx
        have hya := nonneighbor y hy
        have ax : a ≠ x := fun e => (Finset.mem_sdiff.mp hx).2 (List.mem_toFinset.mpr (by simp [e]))
        have ay : a ≠ y := fun e => (Finset.mem_sdiff.mp hy).2 (List.mem_toFinset.mpr (by simp [e]))
        rcases st a aT x (Finset.mem_sdiff.mp hx).1 y (Finset.mem_sdiff.mp hy).1 ax ay xy with e | e | e
        · exact (hxa e.symm).elim
        · exact (hya e.symm).elim
        · exact e
      have head : (a::p).reverse.head?=some w := by rw [List.head?_reverse]; exact last
      refine ⟨⟨(a::p).reverse,Q.toList,List.nodup_append.mpr ⟨(List.nodup_reverse.mpr nd),Finset.nodup_toList _,?_⟩,
        List.isChain_reverse.mpr (pc.imp (fun _ _ e => e.symm)),clique_list_chain clique,?_,?_⟩,head⟩
      · intro x hx y hy eq
        exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hy)).2 (List.mem_toFinset.mpr (eq ▸ List.mem_reverse.mp hx))
      · intro x
        simp only [List.mem_append,List.mem_reverse,Finset.mem_toList,Q,Finset.mem_sdiff,List.mem_toFinset]
        tauto
      · intro _
        exact ⟨by simp,fun no => qe (by simpa using congrArg List.toFinset no)⟩

lemma rooted_branch [Nontrivial V] [DecidableRel G.Adj] {J : Finset V}
    (hc : G.Connected) (ht : G.largestInducedTreeSize ≤ 4) (far : ∀ i j : J, i ≠ j → Remote G i.val j.val)
    (two : 2 ≤ Fintype.card J) (hk : 2 ≤ G.vertexConnectivity) (i : J) (r : V) (hr : IsHigh G J i r) : ∃ B : BranchPath G J i, B.vertices.head?=some r := by
  classical
  let H := Finset.univ.filter (IsHigh G J i)
  let L := Finset.univ.filter (IsLow G J i)
  have high (y : V) : y ∈ H ↔ IsHigh G J i y := by simp [H]
  have low (y : V) : y ∈ L.toList ↔ IsLow G J i y := by simp [L]
  have enough := hk.trans (high_size_two hc ht far two i H high)
  obtain ⟨C,target⟩ := rooted_two_cover H (high_small_two hc ht far two i H (fun y h => (high y).mp h)) enough r ((high r).mpr hr)
  have highMem (y : V) : y ∈ C.first ∨ y ∈ C.second ↔ IsHigh G J i y := by
    rw [← List.mem_append,C.covers,high]
  obtain ⟨fne,sne⟩ := C.nonempty enough
  have lne : L.toList ≠ [] := List.ne_nil_of_mem ((low _).mpr (Or.inl rfl : IsLow G J i i.val))
  have lc : L.toList.IsChain G.Adj := clique_list_chain (by
    intro x hx y hy ne
    exact low_clique_two hc ht far two i ((Finset.mem_filter.mp hx).2) ((Finset.mem_filter.mp hy).2) ne)
  have fHigh (x : V) (hx : x ∈ C.first) := (highMem x).mp (Or.inl hx)
  have sHigh (x : V) (hx : x ∈ C.second) := (highMem x).mp (Or.inr hx)
  let m := C.first ++ L.toList
  have p₁ : m.IsChain G.Adj := C.path₁.append lc (fun x hx y hy =>
    low_high ht far (fHigh x (List.mem_of_mem_getLast? hx)) ((low y).mp (List.mem_of_mem_head? hy)))
  have mne : m ≠ [] := by simp [m,lne]
  have last : m.getLast?=L.toList.getLast? := List.getLast?_append_of_ne_nil _ lne
  have first : m.head?=C.first.head? := List.head?_append_of_ne_nil _ fne
  let l := m++C.second
  have ch : l.IsChain G.Adj := p₁.append C.path₂ (by
    intro x hx y hy
    rw [last] at hx
    exact (low_high ht far (sHigh y (List.mem_of_mem_head? hy)) ((low x).mp (List.mem_of_mem_getLast? hx))).symm)
  have separate (x : V) (hx : x ∈ L.toList) {y : V} (hy : IsHigh G J i y) : x ≠ y :=
    fun e => low_not_high ((low x).mp hx) (e ▸ hy)
  obtain ⟨nf,ns,between⟩ := List.nodup_append.mp C.nodup
  have mn : m.Nodup := List.nodup_append.mpr ⟨nf,Finset.nodup_toList _,fun x hx y hy =>
    (separate y hy (fHigh x hx)).symm⟩
  have ln : l.Nodup := List.nodup_append.mpr ⟨mn,ns,by
    intro x hx y hy
    rcases List.mem_append.mp hx with hx | hx
    · exact between _ hx _ hy
    · exact separate x hx (sHigh y hy)⟩
  refine ⟨⟨l,by simp [l,sne],ln,ch,?_,?_,?_⟩,?_⟩
  · intro x
    simp only [l,m,List.mem_append,low,←highMem]
    tauto
  · intro x hx
    rw [show l.head?=m.head? from List.head?_append_of_ne_nil _ mne,first] at hx
    exact fHigh x (List.mem_of_mem_head? hx)
  · intro x hx
    rw [show l.getLast?=C.second.getLast? from List.getLast?_append_of_ne_nil _ sne] at hx
    exact sHigh x (List.mem_of_mem_getLast? hx)

  · change l.head? = some r
    rw [show l.head?=m.head? from List.head?_append_of_ne_nil _ mne,first,target]

lemma finish_with_rest [Nontrivial V] {J : Finset V} (hc : G.Connected) (ht : G.largestInducedTreeSize ≤ 4)
    (far : ∀ i j : J, i ≠ j → Remote G i.val j.val) (two : 2 ≤ Fintype.card J)
    (maximal : ∀ z, IsRest G J z → ∃ i : J, ∃ x, G.Adj i.val x ∧ G.Adj z x)
    (m : List V) (mne : m ≠ []) (mn : m.Nodup) (mc : m.IsChain G.Adj)
    (mcover : ∀ x, x ∈ m ↔ ∃ i : J, IsLow G J i x ∨ IsHigh G J i x)
    (start : ∀ x ∈ m.head?, ∃ i : J, IsHigh G J i x) (finish : ∀ x ∈ m.getLast?, ∃ i : J, IsHigh G J i x) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let Z := Finset.univ.filter (IsRest G J)
  have zm (v : V) : v ∈ Z ↔ IsRest G J v := by simp [Z]
  obtain ⟨C⟩ := small_two_cover Z (rest_small_two hc ht far two maximal Z (fun x h => (zm _).mp h))
  have zcover (x : V) : x ∈ C.first ∨ x ∈ C.second ↔ IsRest G J x := by rw [←List.mem_append,C.covers,zm]
  have exc (z : V) (hz : IsRest G J z) {x : V} (hx : x ∈ m) : z ≠ x := by
    rintro rfl
    obtain ⟨i,hi⟩ := (mcover z).mp hx
    rcases branch_in_closed_neighborhood hi with e | e
    · exact (hz i).1 e
    · exact (hz i).2 e
  let mid := C.first++m
  have mc' : mid.IsChain G.Adj := C.path₁.append mc (by
    intro x hx y hy
    obtain ⟨j,hj⟩ := start y hy
    exact rest_high_join_two hc ht far two maximal ((zcover x).mp (Or.inl (List.mem_of_mem_getLast? hx))) hj)
  let l := mid++C.second
  have ch : l.IsChain G.Adj := mc'.append C.path₂ (by
    intro x hx y hy
    rw [show mid.getLast?=m.getLast? from List.getLast?_append_of_ne_nil _ mne] at hx
    obtain ⟨j,hj⟩ := finish x hx
    exact (rest_high_join_two hc ht far two maximal ((zcover y).mp (Or.inr (List.mem_of_mem_head? hy))) hj).symm)
  obtain ⟨nf,ns,dis⟩ := List.nodup_append.mp C.nodup
  have midn : mid.Nodup := List.nodup_append.mpr ⟨nf,mn,fun x hx _ hy => exc x ((zcover x).mp (Or.inl hx)) hy⟩
  have nd : l.Nodup := List.nodup_append.mpr ⟨midn,ns,by
    intro x hx y hy
    rcases List.mem_append.mp hx with hx | hx
    · exact dis x hx y hy
    · exact (exc y ((zcover y).mp (Or.inr hy)) hx).symm⟩
  apply path_from_spanning_list l (by simp [l,mid,mne]) nd ch
  intro v
  have h := branch_cases (G:=G) J v
  rw [←zcover,←mcover] at h
  simp only [l,mid,List.mem_append]
  tauto

lemma trace_two_packing [Nontrivial V] [DecidableRel G.Adj] {J : Finset V} (hc : G.Connected)
    (ht : G.largestInducedTreeSize ≤ 4) (far : ∀ i j : J, i ≠ j → Remote G i.val j.val)
    (ks : Fintype.card J = 2) (hk : 2 ≤ G.vertexConnectivity)
    (maximal : ∀ z, IsRest G J z → ∃ i : J, ∃ x, G.Adj i.val x ∧ G.Adj z x) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have two : 2 ≤ Fintype.card J := by omega
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card J)
  obtain ⟨j,ji⟩ := another_of_two two i
  have all (k : J) : k=i ∨ k=j := by
    by_contra! no
    have h := Finset.card_le_univ ({j,i,k} : Finset J)
    have sz : J.card=2 := by simpa using ks
    simp [ji,no.1.symm,no.2.symm] at h
    omega
  obtain ⟨x,y,hx,hy,xy⟩ := cross_representatives hc ht far ji.symm
  obtain ⟨B,bRoot⟩ := rooted_branch hc ht far two hk i x hx
  obtain ⟨D,dRoot⟩ := rooted_branch hc ht far two hk j y hy
  let m := B.vertices.reverse++D.vertices
  have mne : m ≠ [] := by simp [m,D.nonempty]
  have mn : m.Nodup := List.nodup_append.mpr ⟨by simpa using B.nodup,D.nodup,by
    intro p hp q hq eq
    have b := branch_in_closed_neighborhood ((B.covers p).mp (List.mem_reverse.mp hp))
    have d := branch_in_closed_neighborhood ((D.covers q).mp hq)
    subst q
    have ij := far i j ji.symm
    rcases b with b | b <;> rcases d with d | d
    · exact ij.1 (b.symm.trans d)
    · exact ij.2.1 (b ▸ d.symm)
    · exact ij.2.1 (d ▸ b)
    · exact ij.2.2 p b d⟩
  have mc : m.IsChain G.Adj := (List.isChain_reverse.mpr (B.chain.imp (fun _ _ e => e.symm))).append D.chain (by
    intro p hp q hq
    rw [List.getLast?_reverse,bRoot] at hp
    rw [dRoot] at hq
    exact Option.mem_some_iff.mp hp ▸ Option.mem_some_iff.mp hq ▸ xy)
  apply finish_with_rest hc ht far two maximal m mne mn mc
  · intro z
    simp only [m,List.mem_append,List.mem_reverse,B.covers,D.covers]
    constructor
    · rintro (h | h)
      · exact ⟨i,h⟩
      · exact ⟨j,h⟩
    · rintro ⟨k,h⟩
      rcases all k with e | e
      · exact Or.inl (e ▸ h)
      · exact Or.inr (e ▸ h)
  · intro z hz
    rw [show m.head?=B.vertices.reverse.head? from List.head?_append_of_ne_nil _ (by simpa using B.nonempty),
      List.head?_reverse] at hz
    exact ⟨i,B.endHigh z hz⟩
  · intro z hz
    rw [show m.getLast?=D.vertices.getLast? from List.getLast?_append_of_ne_nil _ D.nonempty] at hz
    exact ⟨j,D.endHigh z hz⟩

lemma trace_remote_pair_set [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected) (ht : G.largestInducedTreeSize ≤ 4)
    (hk : 2 ≤ G.vertexConnectivity) (T : Finset V) (rt : RemoteSet G T) (two : 2 ≤ T.card) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let F := Finset.univ.filter (RemoteSet G)
  have mem (U : Finset V) : U ∈ F ↔ RemoteSet G U := by simp [F]
  obtain ⟨J,hJ,max⟩ := Finset.exists_max_image F Finset.card ⟨T,(mem T).mpr rt⟩
  have far := (mem J).mp hJ
  have ji : ∀ i j : J, i ≠ j → Remote G i.val j.val := fun i j ne => far _ i.property _ j.property (fun e => ne (Subtype.ext e))
  have jtwo : 2 ≤ Fintype.card J := by simpa using two.trans (max T ((mem T).mpr rt))
  have maximal : ∀ z, IsRest G J z → ∃ i : J, ∃ x, G.Adj i.val x ∧ G.Adj z x := by
    intro z hz
    by_contra! no
    have out : z ∉ J := fun h => (hz ⟨z,h⟩).1 rfl
    have extra (i : V) (hi : i ∈ J) : Remote G i z := by
      let j : J := ⟨i,hi⟩
      exact ⟨(hz j).1.symm,(hz j).2,no j⟩
    have extended : RemoteSet G (insert z J) := by
      intro i hi j hj ij
      rcases Finset.mem_insert.mp hi with ei | hI <;> rcases Finset.mem_insert.mp hj with ej | hJ
      · exact (ij (ei.trans ej.symm)).elim
      · rw [ei]; exact remote_flip (extra _ hJ)
      · rw [ej]; exact extra _ hI
      · exact far _ hI _ hJ ij
    have bound := max _ ((mem _).mpr extended)
    rw [Finset.card_insert_of_notMem out] at bound
    omega
  by_cases three : 3 ≤ Fintype.card J
  · exact trace_remote_packing hc ht ji three hk maximal
  · exact trace_two_packing hc ht ji (by omega) hk maximal


abbrev Four := Fin 4

def missingRow (i : Four) : Finset Four := Finset.univ.erase i

lemma full_of_three (A : Finset Four) (h : A.card=3) : ∃ i : Four, A=missingRow i := by decide +revert

lemma three_full_labels (H : Finset Four) (x : Four) (hx : x ∈ H)
    (others : ∀ i : Four, i ≠ x → ∃ j ∈ H, j ≠ x ∧ j ≠ i) : 3 ≤ H.card := by decide +revert

lemma no_medium_rows (H B : Finset Four) (count : 3 ≤ H.card) (size : B.card=2)
    (near : ∀ i ∈ H, (B ∩ missingRow i).Nonempty →
      (B \ missingRow i).card+(missingRow i \ B).card≤2) : False := by
  revert H B
  decide

lemma different_full_masks (i j : Four) (h : i ≠ j) :
    ((missingRow i) ∩ (missingRow j)).Nonempty ∧
      2 ≤ ((missingRow i) \ (missingRow j)).card+((missingRow j) \ (missingRow i)).card := by decide +revert

lemma full_single_near (i j : Four) (h : i ≠ j) :
    ((missingRow i) ∩ {j}).Nonempty ∧
      2 ≤ ((missingRow i) \ {j}).card+(({j} : Finset Four) \ (missingRow i)).card := by decide +revert

lemma spare_labels (i j : Four) (h : i ≠ j) : ∃ p q : Four, p ≠ q ∧ p ≠ i ∧ p ≠ j ∧ q ≠ i ∧ q ≠ j := by decide +revert

lemma full_labels_away (H : Finset Four) (h : 3 ≤ H.card) (i : Four) : ∃ j ∈ H, j ≠ i := by decide +revert

lemma exceptional_label (H : Finset Four) (size : 3 ≤ H.card) : ∃ j : Four, ∀ i, i ≠ j → i ∈ H := by decide +revert

lemma full_pair_row (i j : Four) (B : Finset Four) (ij : i ≠ j) (ii : i ∈ B) (jj : j ∈ B) (size : B.card≤3)
    (near : (missingRow i \ B).card+(B \ missingRow i).card≤2) :
    ∃ t, B=missingRow t ∧ t ≠ i ∧ t ≠ j := by decide +revert

structure FourParts (G : SimpleGraph V) where
  low : Four → Finset V
  high : Four → Finset V
  covers : ∀ x, ∃ i, x ∈ low i ∨ x ∈ high i
  lowApart : ∀ i j, i ≠ j → Disjoint (low i) (low j)
  highApart : ∀ i j, i ≠ j → Disjoint (high i) (high j)
  apart : ∀ i j, Disjoint (low i) (high j)
  lowNonempty : ∀ i, (low i).Nonempty
  enough : ∃ t : Four, ∀ i, i ≠ t → (high i).Nonempty
  lowClique : ∀ i, G.IsClique (↑(low i) : Set V)
  highSmall : ∀ i, SmallTriple G (high i)
  cross : ∀ i j, i ≠ j → ∀ x ∈ high i, ∀ y ∈ high j, G.Adj x y
  joins : ∀ i j, i ≠ j → ∀ x ∈ high i, ∀ y ∈ low j, G.Adj x y

lemma rows_one_apart [DecidableRel G.Adj] (ht : G.largestInducedTreeSize ≤ 4) (I : Finset V)
    (hi : G.IsIndepSet (I : Set V)) {a b w : V} (wi : w ∈ I) (aw : G.Adj a w) (bw : G.Adj b w)
    (ab : ¬G.Adj a b) : (I.filter (G.Adj a) \ I.filter (G.Adj b)).card+
      (I.filter (G.Adj b) \ I.filter (G.Adj a)).card ≤ 1 := by
  by_cases same : a=b
  · simp [same]
  have no : I.filter (G.Adj w)=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun y hy =>
    hi wi (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2.ne (Finset.mem_filter.mp hy).2)
  have bnd := path3_rows I hi aw bw.symm ab same
  dsimp only at bnd
  rw [no,Finset.sdiff_empty,Finset.card_union_of_disjoint (Finset.disjoint_left.mpr
    (fun _ ha hb => (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1))] at bnd
  omega

lemma four_independent_structure [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected) (ht : G.largestInducedTreeSize ≤ 4)
    (I : Finset V) (hi : G.IsIndepSet (I : Set V)) (sz : I.card=4)
    (dom : ∀ v, v ∈ I ∨ ∃ z ∈ I, G.Adj v z)
    (pair : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∃ x, G.Adj x i ∧ G.Adj x j) : Nonempty (FourParts G) := by
  classical
  let iso := Fintype.equivOfCardEq (show Fintype.card (↥I) = Fintype.card Four by simpa [Four] using sz)
  let l : Four ↪ V := iso.symm.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
  have li (i : Four) : l i ∈ I := (iso.symm i).property
  have label (z : V) (hz : z ∈ I) : ∃ i : Four, l i=z := ⟨iso ⟨z,hz⟩,by simp [l]⟩
  let R (v : V) := Finset.univ.filter (fun i : Four => G.Adj v (l i))
  have mem (v : V) (i : Four) : i ∈ R v ↔ G.Adj v (l i) := by simp [R]
  have mapped (v : V) : (R v).map l=I.filter (G.Adj v) := by
    ext z
    constructor
    · rintro h
      obtain ⟨i,hI,eq⟩ := Finset.mem_map.mp h
      rw [←eq]
      exact Finset.mem_filter.mpr ⟨li i,(mem v i).mp hI⟩
    · rintro h
      obtain ⟨zi,e⟩ := Finset.mem_filter.mp h
      obtain ⟨i,eq⟩ := label z zi
      exact Finset.mem_map.mpr ⟨i,(mem v i).mpr (eq ▸ e),eq⟩
  have diff (u v : V) : (R u \ R v).card=(I.filter (G.Adj u) \ I.filter (G.Adj v)).card := by
    rw [←mapped,←mapped,←Finset.map_sdiff,Finset.card_map]
  have sizes (v : V) : (R v).card=(I.filter (G.Adj v)).card := by rw [←mapped,Finset.card_map]
  have limit (v : V) : (R v).card ≤ 3 := by
    let W := I.filter (G.Adj v)
    have h := independent_neighbors_size v W (fun _ h _ h' => hi (Finset.mem_filter.mp h).1 (Finset.mem_filter.mp h').1)
      (fun _ h => (Finset.mem_filter.mp h).2)
    have eq : (R v).card = W.card := sizes v
    omega
  have close (a b : V) (inter : (R a ∩ R b).Nonempty) : (R a \ R b).card+(R b \ R a).card≤2 := by
    obtain ⟨w,hw⟩ := inter
    obtain ⟨ha,hb⟩ := Finset.mem_inter.mp hw
    rw [diff,diff]
    exact touching_rows_four ht I hi (li w) ((mem _ _).mp ha) ((mem _ _).mp hb)
  have forced (a b : V) (inter : (R a ∩ R b).Nonempty) (dist : 2 ≤ (R a \ R b).card+(R b \ R a).card) : G.Adj a b := by
    by_contra ab
    obtain ⟨w,hw⟩ := inter
    obtain ⟨ha,hb⟩ := Finset.mem_inter.mp hw
    rw [diff,diff] at dist
    have := rows_one_apart ht I hi (li w) ((mem _ _).mp ha) ((mem _ _).mp hb) ab
    omega
  have common (i j : Four) (ij : i ≠ j) : ∃ v, i ∈ R v ∧ j ∈ R v := by
    obtain ⟨v,vi,vj⟩ := pair _ (li i) _ (li j) (l.injective.ne ij)
    exact ⟨v,(mem _ _).mpr vi,(mem _ _).mpr vj⟩
  have existsFull : ∃ a, (R a).card=3 := by
    by_contra! none
    have all (v : V) : (I.filter (G.Adj v)).card≤2 := by have := limit v; have := none v; rw [←sizes]; omega
    obtain ⟨a,a0,a1⟩ := common 0 1 (by decide)
    obtain ⟨b,b2,b3⟩ := common 2 3 (by decide)
    have bounds := row_distance_packing hc ht I hi 2 all a b
    rw [←mapped,←mapped,←Finset.map_union,Finset.card_map] at bounds
    have eq : R a ∪ R b=Finset.univ := Finset.eq_univ_of_forall (fun t => by
      fin_cases t
      · exact Finset.mem_union_left _ a0
      · exact Finset.mem_union_left _ a1
      · exact Finset.mem_union_right _ b2
      · exact Finset.mem_union_right _ b3)
    rw [eq] at bounds
    exact (by decide : ¬(Finset.univ : Finset Four).card≤2+1) bounds
  let Hot := Finset.univ.filter (fun i : Four => ∃ v, R v=missingRow i)
  have hot (i : Four) : i ∈ Hot ↔ ∃ v, R v=missingRow i := by simp [Hot]
  obtain ⟨a,ha⟩ := existsFull
  obtain ⟨x,hx⟩ := full_of_three (R a) ha
  have many : 3 ≤ Hot.card := by
    apply three_full_labels Hot x ((hot x).mpr ⟨a,hx⟩)
    intro i ix
    obtain ⟨b,bi,bx⟩ := common i x ix
    have am : i ∈ R a := by simp [hx,missingRow,ix]
    have near := close a b ⟨i,Finset.mem_inter.mpr ⟨am,bi⟩⟩
    rw [hx] at near
    obtain ⟨t,e,tx,ti⟩ := full_pair_row x i (R b) ix.symm bx bi (limit b) near
    exact ⟨t,(hot t).mpr ⟨b,e⟩,tx,ti⟩
  have noTwo (v : V) : (R v).card ≠ 2 := by
    intro size
    apply no_medium_rows Hot (R v) many size
    intro i hh near
    obtain ⟨u,hu⟩ := (hot i).mp hh
    rw [←hu] at near ⊢
    exact close v u near
  have empty (i : Four) : R (l i)=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun j h =>
    hi (li i) (li j) ((mem _ _).mp h).ne ((mem _ _).mp h))
  let H (i : Four) := Finset.univ.filter (fun v => R v=missingRow i)
  let L (i : Four) := insert (l i) (Finset.univ.filter (fun v => R v={i}))
  have hmem (v : V) (i : Four) : v ∈ H i ↔ R v=missingRow i := by simp [H]
  have lmem (v : V) (i : Four) : v ∈ L i ↔ v=l i ∨ R v={i} := by simp [L]
  have sc (i : Four) : (missingRow i).card=3 := by fin_cases i <;> decide
  have hcross {i j : Four} (ij : i ≠ j) {u v : V} (hu : u ∈ H i) (hv : v ∈ H j) : G.Adj u v := by
    have d := different_full_masks i j ij
    rw [←(hmem _ _).mp hu,←(hmem _ _).mp hv] at d
    exact forced _ _ d.1 d.2
  have hlow {i j : Four} (ij : i ≠ j) {u v : V} (hu : u ∈ H i) (hv : v ∈ L j) : G.Adj u v := by
    have uh := (hmem _ _).mp hu
    rcases (lmem _ _).mp hv with eq | eq
    · rw [eq,←mem,uh]; simp [missingRow,ij.symm]
    · have d := full_single_near i j ij
      rw [←uh,←eq] at d
      exact forced _ _ d.1 d.2
  have hnonempty (i : Four) : (H i).Nonempty ↔ i ∈ Hot := by
    rw [hot]
    exact exists_congr (fun v => hmem v i)
  have uniqueHigh {i j : Four} (h : missingRow i=missingRow j) : i=j := by
    by_contra ne
    have h1 : j ∈ missingRow i := by simp [missingRow,Ne.symm ne]
    rw [h] at h1
    simpa [missingRow] using h1
  refine ⟨⟨L,H,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro v
    rcases dom v with vi | ⟨z,zi,vz⟩
    · obtain ⟨i,rfl⟩ := label v vi
      exact ⟨i,Or.inl ((lmem _ _).mpr (Or.inl rfl))⟩
    obtain ⟨j,lj⟩ := label z zi
    have pos := Finset.card_pos.mpr (show (R v).Nonempty from ⟨j,(mem _ _).mpr (lj ▸ vz)⟩)
    have vals : (R v).card=1 ∨ (R v).card=3 := by have := noTwo v; have := limit v; omega
    rcases vals with size | size
    · obtain ⟨i,ii⟩ := Finset.card_eq_one.mp size
      exact ⟨i,Or.inl ((lmem _ _).mpr (Or.inr ii))⟩
    · obtain ⟨i,ii⟩ := full_of_three _ size
      exact ⟨i,Or.inr ((hmem _ _).mpr ii)⟩
  · intro i j ij
    apply Finset.disjoint_left.mpr
    intro v lv l'v
    rcases (lmem _ _).mp lv with e | e <;> rcases (lmem _ _).mp l'v with d | d
    · exact ij (l.injective (e.symm.trans d))
    · rw [e,empty] at d; simp at d
    · rw [d,empty] at e; simp at e
    · exact ij (Finset.singleton_inj.mp (e.symm.trans d))
  · intro i j ij
    exact Finset.disjoint_left.mpr fun v u w => ij (uniqueHigh (((hmem _ _).mp u).symm.trans ((hmem _ _).mp w)))
  · intro i j
    apply Finset.disjoint_left.mpr
    intro v hv hh
    have card := congrArg Finset.card ((hmem _ _).mp hh)
    rw [sc] at card
    rcases (lmem _ _).mp hv with eq | eq
    · rw [eq,empty] at card; simp at card
    · rw [eq] at card; simp at card
  · intro i; exact ⟨l i,(lmem _ _).mpr (Or.inl rfl)⟩
  · obtain ⟨t,h⟩ := exceptional_label Hot many
    exact ⟨t,fun i it => (hnonempty i).mpr (h i it)⟩
  · intro i u hu v hv uv
    have lu (w : V) (hw : w ∈ L i) (h : w ≠ l i) : G.Adj w (l i) := by
      rw [←mem,(lmem _ _ |>.mp hw).resolve_left h]; simp
    by_cases ueq : u=l i
    · exact ueq ▸ (lu v hv (fun ev => uv (ueq.trans ev.symm))).symm
    by_cases veq : v=l i
    · exact veq ▸ lu u hu (fun eu => uv (eu.trans veq.symm))
    have uone := ((lmem _ _).mp hu).resolve_left ueq
    have vone := ((lmem _ _).mp hv).resolve_left veq
    obtain ⟨j,jh,ji⟩ := full_labels_away Hot many i
    obtain ⟨o,ho⟩ := (hnonempty j).mpr jh
    obtain ⟨p,q,pq,pi,pj,qi,qj⟩ := spare_labels i j ji.symm
    have op : G.Adj o (l p) := (mem _ _).mp (by rw [(hmem _ _).mp ho]; simp [missingRow,pj])
    have oq : G.Adj o (l q) := (mem _ _).mp (by rw [(hmem _ _).mp ho]; simp [missingRow,qj])
    have miss {w : V} (one : R w={i}) {k : Four} (ki : k ≠ i) : ¬G.Adj w (l k) := by
      rw [←mem,one]; simpa using ki
    have out {w : V} (one : R w={i}) (k : Four) : w ≠ l k := by
      rintro rfl
      rw [empty] at one; simp at one
    let T : Finset V := {u,v,l q}
    have small : SmallTriple G T := smalltriple_of_star ht T op.symm (by
      intro t ht'
      simp only [T,Finset.mem_insert,Finset.mem_singleton] at ht'
      rcases ht' with e | e | e
      · rw [e]; exact ⟨out uone p,fun a => miss uone pi a.symm,hlow ji ho hu⟩
      · rw [e]; exact ⟨out vone p,fun a => miss vone pi a.symm,hlow ji ho hv⟩
      · rw [e]; exact ⟨l.injective.ne pq.symm,hi (li p) (li q) (l.injective.ne pq),oq⟩)
    rcases small u (by simp [T]) v (by simp [T]) (l q) (by simp [T]) uv (out uone q) (out vone q) with e | e | e
    · exact e
    · exact (miss uone qi e).elim
    · exact (miss vone qi e).elim
  · intro i
    obtain ⟨j,jh,ji⟩ := full_labels_away Hot many i
    obtain ⟨o,ho⟩ := (hnonempty j).mpr jh
    have oi := hlow ji ho ((lmem (l i) i).mpr (Or.inl rfl))
    apply smalltriple_of_star ht (H i) oi.symm
    intro v hv
    have vh := (hmem _ _).mp hv
    refine ⟨?_,?_,hcross ji ho hv⟩
    · rintro rfl
      rw [empty] at vh
      have := congrArg Finset.card vh
      rw [sc] at this
      simp at this
    · intro e
      have m := (mem _ _).mpr e.symm
      rw [vh] at m
      simpa [missingRow] using m
  · exact fun _ _ ij _ hu _ hv => hcross ij hu hv
  · exact fun _ _ ij _ hu _ hv => hlow ij hu hv

structure SmallBlock (G : SimpleGraph V) (H L : Finset V) where
  vertices : List V
  nonempty : vertices ≠ []
  nodup : vertices.Nodup
  chain : vertices.IsChain G.Adj
  covers : ∀ x, x ∈ vertices ↔ x ∈ H ∨ x ∈ L
  finish : H.Nonempty → ∀ x ∈ vertices.getLast?, x ∈ H

lemma small_block (H L : Finset V) (hl : Disjoint H L) (ln : L.Nonempty) (small : SmallTriple G H)
    (cl : G.IsClique (L : Set V)) (join : ∀ x ∈ H, ∀ y ∈ L, G.Adj x y) : Nonempty (SmallBlock G H L) := by
  classical
  obtain ⟨C⟩ := small_two_cover H small
  have members (x : V) : x ∈ C.first ∨ x ∈ C.second ↔ x ∈ H := by rw [←List.mem_append,C.covers]
  have rep : ∃ p q : List V, (p++q).Nodup ∧ p.IsChain G.Adj ∧ q.IsChain G.Adj ∧
      (∀ x, x ∈ p ∨ x ∈ q ↔ x ∈ H) ∧ (H.Nonempty → q ≠ []) := by
    by_cases e : C.second=[]
    · refine ⟨[],C.first,by simpa [e] using C.nodup,by simp,C.path₁,?_,?_⟩
      · intro x; simpa [e] using members x
      · rintro ⟨x,hx⟩ h
        have := (members x).mpr hx
        simp [e,h] at this
    · exact ⟨C.first,C.second,C.nodup,C.path₁,C.path₂,members,fun _ => e⟩
  obtain ⟨p,q,nd,pc,qc,mem,sne⟩ := rep
  have lne : L.toList ≠ [] := by obtain ⟨x,h⟩ := ln; exact List.ne_nil_of_mem (Finset.mem_toList.mpr h)
  let m := p++L.toList
  have mne : m ≠ [] := by simp [m,lne]
  have p1 : m.IsChain G.Adj := pc.append (clique_list_chain cl) (fun x hx y hy =>
    join _ ((mem x).mp (Or.inl (List.mem_of_mem_getLast? hx))) _ (Finset.mem_toList.mp (List.mem_of_mem_head? hy)))
  let l := m++q
  have chain : l.IsChain G.Adj := p1.append qc (by
    intro x hx y hy
    rw [show m.getLast?=L.toList.getLast? from List.getLast?_append_of_ne_nil _ lne] at hx
    exact (join _ ((mem y).mp (Or.inr (List.mem_of_mem_head? hy))) _ (Finset.mem_toList.mp (List.mem_of_mem_getLast? hx))).symm)
  obtain ⟨pn,qn,between⟩ := List.nodup_append.mp nd
  have mn : m.Nodup := List.nodup_append.mpr ⟨pn,Finset.nodup_toList _,by
    intro x hx y hy e
    exact Finset.disjoint_left.mp hl ((mem x).mp (Or.inl hx)) (e ▸ Finset.mem_toList.mp hy)⟩
  have nodup : l.Nodup := List.nodup_append.mpr ⟨mn,qn,by
    intro x hx y hy e
    rcases List.mem_append.mp hx with hx | hx
    · exact between x hx y hy e
    · exact Finset.disjoint_left.mp hl ((mem y).mp (Or.inr hy)) (e ▸ Finset.mem_toList.mp hx)⟩
  refine ⟨⟨l,by simp [l,mne],nodup,chain,?_,?_⟩⟩
  · intro x; simp only [l,m,List.mem_append,Finset.mem_toList,←mem]; tauto
  · intro h x hx
    rw [show l.getLast?=q.getLast? from List.getLast?_append_of_ne_nil _ (sne h)] at hx
    exact (mem x).mp (Or.inr (List.mem_of_mem_getLast? hx))

lemma trace_four_parts [Nontrivial V] (P : FourParts G) : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨t,hh⟩ := P.enough
  let π := Equiv.swap (3 : Four) t
  let σ : Four ≃ Four := Equiv.swap (0 : Four) 2 |>.trans (Equiv.swap (1 : Four) 3)
  have sig (i : Four) : i ≠ σ i := by fin_cases i <;> decide
  have edge (i j : Four) (next : (i : ℕ)+1=j.val) : i ≠ j ∧ i ≠ σ j ∧ i ≠ 3 := by
    fin_cases i <;> fin_cases j <;> first | decide | contradiction
  let H (i : Four) := P.high (π i)
  let L (i : Four) := P.low (π (σ i))
  have make (i : Four) : Nonempty (SmallBlock G (H i) (L i)) :=
    small_block _ _ (P.apart _ _).symm (P.lowNonempty _) (P.highSmall _) (P.lowClique _)
      (P.joins _ _ (π.injective.ne (sig i)))
  let F (i : Four) := (make i).some
  let ord : List Four := [0,1,2,3]
  have all (i : Four) : i ∈ ord := by fin_cases i <;> decide
  have sep (i j : Four) (ij : i ≠ j) : ((F i).vertices).Disjoint ((F j).vertices) := by
    apply List.disjoint_left.mpr
    intro v hv hj
    rcases ((F i).covers v).mp hv with a | a <;> rcases ((F j).covers v).mp hj with b | b
    · exact Finset.disjoint_left.mp (P.highApart _ _ (π.injective.ne ij)) a b
    · exact Finset.disjoint_left.mp (P.apart _ _) b a
    · exact Finset.disjoint_left.mp (P.apart _ _) a b
    · exact Finset.disjoint_left.mp (P.lowApart _ _ (π.injective.ne (σ.injective.ne ij))) a b
  let l := ord.flatMap (fun i => (F i).vertices)
  have nd : l.Nodup := List.nodup_flatMap.mpr ⟨fun i _ => (F i).nodup,
    (show ord.Nodup by decide).imp (fun {i j} hij => sep i j hij)⟩
  have ch : l.IsChain G.Adj := by
    change ((ord.map (fun i => (F i).vertices)).flatten).IsChain G.Adj
    have ne : [] ∉ ord.map (fun i => (F i).vertices) := by
      intro h
      obtain ⟨i,_,eq⟩ := List.mem_map.mp h
      exact (F i).nonempty eq
    apply (List.isChain_flatten ne).mpr
    refine ⟨?_,?_⟩
    · intro B hb
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
      exact (F i).chain
    · have step (i j : Four) (next : (i : ℕ)+1=j.val) :
          ∀ x ∈ (F i).vertices.getLast?, ∀ y ∈ (F j).vertices.head?, G.Adj x y := by
        obtain ⟨ij,isj,i3⟩ := edge i j next
        have it : π i ≠ t := fun e => i3 (π.injective (e.trans (Equiv.swap_apply_left (3 : Four) t).symm))
        intro x hx y hy
        have h1 := (F i).finish (hh _ it) x hx
        rcases ((F j).covers y).mp (List.mem_of_mem_head? hy) with h2 | h2
        · exact P.cross _ _ (π.injective.ne ij) _ h1 _ h2
        · exact P.joins _ _ (π.injective.ne isj) _ h1 _ h2
      simp only [ord,List.map_cons,List.map_nil,List.isChain_cons_cons,List.isChain_singleton,and_true]
      exact ⟨step 0 1 rfl,step 1 2 rfl,step 2 3 rfl⟩
  have covers (v : V) : v ∈ l := by
    obtain ⟨i,hi | hi⟩ := P.covers v
    · let j := σ.symm (π.symm i)
      have m : v ∈ L j := by simpa [j,L] using hi
      exact List.mem_flatMap.mpr ⟨j,all j,((F j).covers v).mpr (Or.inr m)⟩
    · let j := π.symm i
      have m : v ∈ H j := by simpa [j,H] using hi
      exact List.mem_flatMap.mpr ⟨j,all j,((F j).covers v).mpr (Or.inl m)⟩
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  exact path_from_spanning_list l (List.ne_nil_of_mem (covers v)) nd ch covers


lemma trace_tree_four [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected)
    (ht : G.largestInducedTreeSize ≤ 4) (hk : 2 ≤ G.vertexConnectivity) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_contra path
  have noBig (T : Finset V) (hT : G.IsIndepSet (T : Set V)) : T.card ≤ 4 := by
    by_contra! big
    obtain ⟨J,three,remote⟩ := remote_of_five_independent hc ht T hT big
    exact path (trace_remote_set hc ht hk J remote three)
  obtain ⟨I,hi,isize⟩ := independent_of_nontrace path
  have sz : I.card=4 := by have := noBig I hi; omega
  have dom (v : V) : v ∈ I ∨ ∃ z ∈ I, G.Adj v z := by
    by_contra! fail
    obtain ⟨vs,no⟩ := fail
    have ind : G.IsIndepSet (↑(insert v I) : Set V) := by
      intro x hx y hy ne e
      rcases Finset.mem_insert.mp hx with ex | hx' <;> rcases Finset.mem_insert.mp hy with ey | hy'
      · exact ne (ex.trans ey.symm)
      · exact no y hy' (ex ▸ e)
      · exact no x hx' (ey ▸ e.symm)
      · exact hi hx' hy' ne e
    have bound := noBig (insert v I) ind
    rw [Finset.card_insert_of_notMem vs,sz] at bound
    omega
  have common (i : V) (ii : i ∈ I) (j : V) (ji : j ∈ I) (ij : i ≠ j) : ∃ x, G.Adj x i ∧ G.Adj x j := by
    by_contra! none
    have rem : Remote G i j := ⟨ij,hi ii ji ij,fun v vi vj => none v vi.symm vj.symm⟩
    let T : Finset V := {i,j}
    have rt : RemoteSet G T := by
      intro a ha b hb ab
      simp only [T,Finset.mem_insert,Finset.mem_singleton] at ha hb
      rcases ha with ea | ea <;> rcases hb with eb | eb
      · exact (ab (ea.trans eb.symm)).elim
      · rw [ea,eb]; exact rem
      · rw [ea,eb]; exact remote_flip rem
      · exact (ab (ea.trans eb.symm)).elim
    exact path (trace_remote_pair_set hc ht hk T rt (by simp [T,ij]))
  obtain ⟨parts⟩ := four_independent_structure hc ht I hi sz dom common
  exact path (trace_four_parts parts)


end OMA.ConnectivityTwo

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1.H1 := by
  classical
  intro V _ _ G hk ht v w _ _ vw _ _ _ _ _ _ _ _ _ _ _
  letI : Nontrivial V := ⟨v,w,vw⟩
  have cut := OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1.connected_of_card_lt_vertexConnectivity (G:=G) (∅ : Finset V) (by simp [hk])
  have setEq : (((∅ : Finset V) : Set V)ᶜ) = Set.univ := by ext x; simp
  rw [setEq] at cut
  exact OMA.ConnectivityTwo.trace_tree_four ((SimpleGraph.induceUnivIso G).connected_iff.mp cut) ht (by omega)
