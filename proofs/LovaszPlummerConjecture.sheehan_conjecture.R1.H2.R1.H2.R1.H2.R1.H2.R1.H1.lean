import OMAReductions.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1_H2_R1_H2_R1

/-! Rejoining two or three path segments of a Hamiltonian cycle. -/

namespace OMA.CycleExchange

open SimpleGraph LovaszPlummerConjecture

private theorem splice_hamiltonian {V : Type} {G : SimpleGraph V} {v w : V}
    {p : G.Walk v v} {q : G.Walk w w} (hp : LovaszPlummerConjecture.IsHamiltonianCycle G p)
    (perm : q.support.tail.Perm p.support.tail) (hq : ¬ q.Nil) :
    LovaszPlummerConjecture.IsHamiltonianCycle G q := by
  have law : 3 ≤ q.length := by
    have h := perm.length_eq
    rw [List.length_tail, List.length_tail, Walk.length_support, Walk.length_support] at h
    have hp3 := hp.1.three_le_length
    omega
  refine ⟨Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, law⟩, ?_⟩
  · rw [Walk.isPath_def, q.support_tail_of_not_nil hq]
    exact perm.nodup_iff.mpr hp.1.support_nodup
  · intro x
    apply (q.mem_support_iff).mpr
    right
    apply perm.mem_iff.mpr
    rcases (p.mem_support_iff).mp (hp.2 x) with rfl | hx
    · rw [← p.support_tail_of_not_nil hp.1.not_nil]
      exact p.tail.end_mem_support
    · exact hx

private theorem two_swap {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {a b c d : V} (ab : G.Adj a b) (cd : G.Adj c d)
    (ac : G.Adj a c) (bd : G.Adj b d) (P : G.Walk b c) (Q : G.Walk d a)
    (oldCycle : LovaszPlummerConjecture.IsHamiltonianCycle G
      (Walk.cons ab (P.append (.cons cd Q))))
    (ac_ne : s(a,b) ≠ s(a,c)) (bd_ne : s(a,b) ≠ s(b,d)) :
    let old := Walk.cons ab (P.append (.cons cd Q))
    let new := Walk.cons ac (P.reverse.append (.cons bd Q))
    LovaszPlummerConjecture.IsHamiltonianCycle G new ∧
    new.edges.toFinset ≠ old.edges.toFinset ∧
    ∀ f : Sym2 V, f ≠ s(a,b) → f ≠ s(c,d) → f ≠ s(a,c) → f ≠ s(b,d) →
      (f ∈ new.edges ↔ f ∈ old.edges) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply splice_hamiltonian oldCycle
    · simp only [Walk.support_cons, List.tail_cons, Walk.support_append, Walk.support_reverse]
      exact (List.reverse_perm P.support).append_right Q.support
    · simp
  · have nodup := oldCycle.1.isTrail.edges_nodup
    simp only [Walk.edges_cons, Walk.edges_append, List.nodup_cons, List.mem_append,
      List.mem_cons] at nodup
    intro same
    have memOld : s(a,b) ∈ (Walk.cons ab (P.append (.cons cd Q))).edges.toFinset := by simp
    rw [← same] at memOld
    simp only [List.mem_toFinset, Walk.edges_cons, Walk.edges_append, Walk.edges_reverse,
      List.mem_cons, List.mem_append, List.mem_reverse] at memOld
    grind
  · intro f h1 h2 h3 h4
    simp [Walk.edges_append, h1, h2, h3, h4]

private theorem three_swap {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {a b c d e f : V} (ab : G.Adj a b) (cd : G.Adj c d) (ef : G.Adj e f)
    (ad : G.Adj a d) (eb : G.Adj e b) (cf : G.Adj c f)
    (P : G.Walk b c) (Q : G.Walk d e) (R : G.Walk f a)
    (oldCycle : LovaszPlummerConjecture.IsHamiltonianCycle G
      (Walk.cons ab (P.append (.cons cd (Q.append (.cons ef R))))))
    (ad_ne : s(a,b) ≠ s(a,d)) (eb_ne : s(a,b) ≠ s(e,b))
    (cf_ne : s(a,b) ≠ s(c,f)) :
    let old := Walk.cons ab (P.append (.cons cd (Q.append (.cons ef R))))
    let new := Walk.cons ad (Q.append (.cons eb (P.append (.cons cf R))))
    LovaszPlummerConjecture.IsHamiltonianCycle G new ∧
    new.edges.toFinset ≠ old.edges.toFinset ∧
    ∀ x : Sym2 V, x ≠ s(a,b) → x ≠ s(c,d) → x ≠ s(e,f) →
      x ≠ s(a,d) → x ≠ s(e,b) → x ≠ s(c,f) → (x ∈ new.edges ↔ x ∈ old.edges) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply splice_hamiltonian oldCycle
    · simp only [Walk.support_cons, List.tail_cons, Walk.support_append, ← List.append_assoc]
      exact (List.perm_append_comm).append_right R.support
    · simp
  · have nodup := oldCycle.1.isTrail.edges_nodup
    simp only [Walk.edges_cons, Walk.edges_append, List.nodup_cons, List.mem_append,
      List.mem_cons] at nodup
    intro same
    have memOld : s(a,b) ∈ (Walk.cons ab (P.append (.cons cd (Q.append (.cons ef R))))).edges.toFinset := by simp
    rw [← same] at memOld
    simp only [List.mem_toFinset, Walk.edges_cons, Walk.edges_append, List.mem_cons, List.mem_append] at memOld
    grind
  · intro x h1 h2 h3 h4 h5 h6
    simp [Walk.edges_append, h1, h2, h3, h4, h5, h6]
    tauto


private theorem split_dart {V : Type} {G : SimpleGraph V} {u v a b : V} (p : G.Walk u v)
    (ab : G.Adj a b) (h : ⟨(a,b),ab⟩ ∈ p.darts) :
    ∃ P : G.Walk u a, ∃ Q : G.Walk b v, p = P.append (.cons ab Q) := by
  obtain ⟨P,Q,h⟩ := (Walk.isSubwalk_toWalk_iff_mem_darts p ab).mpr h
  refine ⟨P,Q,?_⟩
  rw [h, ← Walk.append_assoc]
  rfl

private theorem rebase {V : Type} {G : SimpleGraph V} {v a b : V}
    {p : G.Walk v v} (hp : LovaszPlummerConjecture.IsHamiltonianCycle G p)
    (ab : G.Adj a b) (h : ⟨(a,b),ab⟩ ∈ p.darts) :
    ∃ Q : G.Walk b a, LovaszPlummerConjecture.IsHamiltonianCycle G (.cons ab Q) ∧
      (.cons ab Q : G.Walk a a).darts.Perm p.darts := by
  obtain ⟨A,B,rfl⟩ := split_dart p ab h
  refine ⟨B.append A, splice_hamiltonian hp ?_ (by simp), ?_⟩
  · rw [Walk.tail_support_append]
    simp only [Walk.support_cons, List.tail_cons, Walk.support_append]
    exact List.perm_append_comm
  · simp only [Walk.darts_cons, Walk.darts_append]
    change ((_ :: B.darts) ++ A.darts).Perm _
    exact List.perm_append_comm

private theorem same_start_of_darts {V : Type} {G : SimpleGraph V} {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) {d e : G.Dart}
    (hd : d ∈ p.darts) (he : e ∈ p.darts) (h : d.fst = e.fst) : d = e := by
  apply List.inj_on_of_nodup_map (f := fun f : G.Dart => f.fst) _ hd he h
  rw [Walk.map_fst_darts]
  exact hp.nodup_dropLast_support

private theorem same_end_of_darts {V : Type} {G : SimpleGraph V} {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) {d e : G.Dart}
    (hd : d ∈ p.darts) (he : e ∈ p.darts) (h : d.snd = e.snd) : d = e := by
  apply List.inj_on_of_nodup_map (f := fun f : G.Dart => f.snd) _ hd he h
  rw [Walk.map_snd_darts]
  exact hp.support_nodup


private def localExchange {V : Type} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (S : Set V) : Prop :=
  ∃ w : V, ∃ q : G.Walk w w, LovaszPlummerConjecture.IsHamiltonianCycle G q ∧
    q.edges.toFinset ≠ p.edges.toFinset ∧
    ∀ f : Sym2 V, (∃ x ∈ f, x ∉ S) → (f ∈ q.edges ↔ f ∈ p.edges)

private theorem avoid_cut {V : Type} {S : Set V} {a b : V} {f : Sym2 V}
    (out : ∃ x ∈ f, x ∉ S) (ha : a ∈ S) (hb : b ∈ S) : f ≠ s(a,b) := by
  rintro rfl
  obtain ⟨x, hx, bad⟩ := out
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  · exact bad ha
  · exact bad hb

private theorem edge_perm_of_dart_perm {V : Type} {G : SimpleGraph V} {u v x y : V}
    {p : G.Walk u v} {q : G.Walk x y} (h : p.darts.Perm q.darts) :
    p.edges.Perm q.edges := by
  simpa only [Walk.edges_eq_map_darts] using h.map SimpleGraph.Dart.edge

private theorem localExchange_congr {V : Type} [DecidableEq V] {G : SimpleGraph V} {v w : V}
    {p : G.Walk v v} {q : G.Walk w w} {S : Set V} (h : p.edges.Perm q.edges)
    (hp : localExchange p S) : localExchange q S := by
  have fEq : p.edges.toFinset = q.edges.toFinset := by
    ext f
    simpa using h.mem_iff
  obtain ⟨u,r,cyc,diff,pres⟩ := hp
  refine ⟨u,r,cyc,?_,fun f out => (pres f out).trans h.mem_iff⟩
  simpa only [fEq] using diff

private theorem two_from_darts {V : Type} [DecidableEq V] {G : SimpleGraph V} {v a b c d : V}
    {p : G.Walk v v} {S : Set V} (hp : LovaszPlummerConjecture.IsHamiltonianCycle G p)
    (ab : G.Adj a b) (cd : G.Adj c d) (ac : G.Adj a c) (bd : G.Adj b d)
    (hAB : ⟨(a,b),ab⟩ ∈ p.darts) (hCD : ⟨(c,d),cd⟩ ∈ p.darts)
    (bc : b ≠ c) (ad : a ≠ d) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) :
    localExchange p S := by
  obtain ⟨T,hT,perm⟩ := rebase hp ab hAB
  have hmember := perm.mem_iff.mpr hCD
  simp only [Walk.darts_cons, List.mem_cons] at hmember
  have cut : ⟨(c,d),cd⟩ ∈ T.darts := by
    refine hmember.resolve_left ?_
    intro h
    exact ac.ne (congrArg (fun edge : G.Dart => edge.fst) h).symm
  obtain ⟨P,Q,rfl⟩ := split_dart T cd cut
  have ac_ne : s(a,b) ≠ s(a,c) := by
    intro h
    rcases (Sym2.mk_eq_mk_iff (p := (a,b)) (q := (a,c))).mp h with h|h
    · exact bc (congrArg Prod.snd h)
    · exact ac.ne (congrArg Prod.fst h)
  have bd_ne : s(a,b) ≠ s(b,d) := by
    intro h
    rcases (Sym2.mk_eq_mk_iff (p := (a,b)) (q := (b,d))).mp h with h|h
    · exact ab.ne (congrArg Prod.fst h)
    · exact ad (congrArg Prod.fst h)
  obtain ⟨cyc,ne,edges⟩ := two_swap ab cd ac bd P Q hT ac_ne bd_ne
  apply localExchange_congr (edge_perm_of_dart_perm perm)
  exact ⟨a, Walk.cons ac (P.reverse.append (.cons bd Q)), cyc, ne, fun f out =>
    edges f (avoid_cut out ha hb) (avoid_cut out hc hd) (avoid_cut out ha hc) (avoid_cut out hb hd)⟩

private theorem three_ordered {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {a b c d e f : V} {S : Set V} (ab : G.Adj a b) (cd : G.Adj c d) (ef : G.Adj e f)
    (ad : G.Adj a d) (eb : G.Adj e b) (cf : G.Adj c f) (af : G.Adj a f)
    (P : G.Walk b c) (Q : G.Walk d e) (R : G.Walk f a)
    (cyc : LovaszPlummerConjecture.IsHamiltonianCycle G
      (Walk.cons ab (P.append (.cons cd (Q.append (.cons ef R))))))
    (bd : b ≠ d) (ae : a ≠ e) (ac : a ≠ c)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) (he : e ∈ S) (hf : f ∈ S) :
    localExchange (Walk.cons ab (P.append (.cons cd (Q.append (.cons ef R))))) S := by
  have ad_ne : s(a,b) ≠ s(a,d) := by
    intro h
    rcases (Sym2.mk_eq_mk_iff (p := (a,b)) (q := (a,d))).mp h with h|h
    · exact bd (congrArg Prod.snd h)
    · exact ad.ne (congrArg Prod.fst h)
  have eb_ne : s(a,b) ≠ s(e,b) := by
    intro h
    rcases (Sym2.mk_eq_mk_iff (p := (a,b)) (q := (e,b))).mp h with h|h
    · exact ae (congrArg Prod.fst h)
    · exact ab.ne (congrArg Prod.fst h)
  have cf_ne : s(a,b) ≠ s(c,f) := by
    intro h
    rcases (Sym2.mk_eq_mk_iff (p := (a,b)) (q := (c,f))).mp h with h|h
    · exact ac (congrArg Prod.fst h)
    · exact af.ne (congrArg Prod.fst h)
  obtain ⟨ham,ne,edges⟩ := three_swap ab cd ef ad eb cf P Q R cyc ad_ne eb_ne cf_ne
  exact ⟨a, Walk.cons ad (Q.append (.cons eb (P.append (.cons cf R)))), ham, ne,
    fun x out => edges x (avoid_cut out ha hb) (avoid_cut out hc hd) (avoid_cut out he hf)
      (avoid_cut out ha hd) (avoid_cut out he hb) (avoid_cut out hc hf)⟩

private theorem orientation_cases : ∀ (dir : Fin 3 → Bool) (r : Fin 3 → Fin 3),
    (∀ i, dir i = true) ∨ (∀ i, dir i = false) ∨
    (∃ i j, dir i = true ∧ dir j = false ∧ r i ≠ r j) ∨
    ∃ i j, i ≠ j ∧ dir i = dir j ∧ r i = r j := by decide +kernel


private theorem uniform_from_darts {V : Type} [DecidableEq V] {G : SimpleGraph V} {v : V}
    {p : G.Walk v v} {S : Set V} (hp : LovaszPlummerConjecture.IsHamiltonianCycle G p)
    (u w : Fin 3 → V) (injU : Function.Injective u) (injW : Function.Injective w)
    (adj : ∀ i j, G.Adj (u i) (w j))
    (hu : ∀ i, u i ∈ S) (hw : ∀ i, w i ∈ S)
    (inside : ∀ i, (⟨(u i,w i),adj i i⟩ : G.Dart) ∈ p.darts) :
    localExchange p S := by
  let cut (i : Fin 3) : G.Dart := ⟨(u i,w i),adj i i⟩
  have injCut : Function.Injective cut := fun i j eq => injU (congrArg (fun edge : G.Dart => edge.fst) eq)
  obtain ⟨T,hT,perm⟩ := rebase hp (adj 0 0) (inside 0)
  apply localExchange_congr (edge_perm_of_dart_perm perm)
  have inTail (i : Fin 3) (ne : i ≠ 0) : cut i ∈ T.darts := by
    have h := perm.mem_iff.mpr (inside i)
    change cut i ∈ cut 0 :: T.darts at h
    exact (List.mem_cons.mp h).resolve_left (injCut.ne ne)
  have h1 := inTail 1 (by decide)
  have h2 := inTail 2 (by decide)
  obtain ⟨P,R,rfl⟩ := split_dart T (adj 1 1) h1
  simp only [Walk.darts_append, Walk.darts_cons, List.mem_append, List.mem_cons] at h2
  change cut 2 ∈ P.darts ∨ cut 2 = cut 1 ∨ cut 2 ∈ R.darts at h2
  rcases h2 with h2 | h2 | h2
  · obtain ⟨A,B,rfl⟩ := split_dart P (adj 2 2) h2
    simp only [← Walk.append_assoc, Walk.cons_append] at hT ⊢
    exact three_ordered (adj 0 0) (adj 2 2) (adj 1 1)
      (adj 0 2) (adj 1 0) (adj 2 1) (adj 0 1)
      A B R hT (injW.ne (by decide)) (injU.ne (by decide)) (injU.ne (by decide))
      (hu 0) (hw 0) (hu 2) (hw 2) (hu 1) (hw 1)
  · exact ((by decide : (2 : Fin 3) ≠ 1) (injCut h2)).elim
  · obtain ⟨B,C,rfl⟩ := split_dart R (adj 2 2) h2
    exact three_ordered (adj 0 0) (adj 1 1) (adj 2 2)
      (adj 0 1) (adj 2 0) (adj 1 2) (adj 0 2)
      P B C hT (injW.ne (by decide)) (injU.ne (by decide)) (injU.ne (by decide))
      (hu 0) (hw 0) (hu 1) (hw 1) (hu 2) (hw 2)

private theorem orient_and_exchange {V : Type} [DecidableEq V] {G : SimpleGraph V} {v : V}
    {p : G.Walk v v} {S : Set V} (hp : LovaszPlummerConjecture.IsHamiltonianCycle G p)
    (l r : Fin 3 ↪ V) (adj : ∀ i j, G.Adj (l i) (r j))
    (hl : ∀ i, l i ∈ S) (hr : ∀ j, r j ∈ S)
    (j : Fin 3 → Fin 3) (dir : Fin 3 → Bool)
    (selected : ∀ i,
      (dir i = true → (⟨(l i,r (j i)),adj i (j i)⟩ : G.Dart) ∈ p.darts) ∧
      (dir i = false → (⟨(r (j i),l i),(adj i (j i)).symm⟩ : G.Dart) ∈ p.darts)) :
    localExchange p S := by
  have noRepeat : ∀ i k, dir i = dir k → j i = j k → i = k := by
    intro i k sameDir sameRight
    cases h : dir i
    · have hk := sameDir.symm.trans h
      have eq := same_start_of_darts hp.1 ((selected i).2 h) ((selected k).2 hk)
        (congrArg r sameRight)
      exact l.injective (congrArg (fun edge : G.Dart => edge.snd) eq)
    · have hk := sameDir.symm.trans h
      have eq := same_end_of_darts hp.1 ((selected i).1 h) ((selected k).1 hk)
        (congrArg r sameRight)
      exact l.injective (congrArg (fun edge : G.Dart => edge.fst) eq)
  rcases orientation_cases dir j with uni | uni | ⟨i,k,hi,hk,jik⟩ | ⟨i,k,ik,sameDir,sameRight⟩
  · have jin : Function.Injective j := fun i k eq => noRepeat i k ((uni i).trans (uni k).symm) eq
    exact uniform_from_darts hp l (r ∘ j) l.injective (r.injective.comp jin)
      (fun i k => adj i (j k)) hl (fun i => hr (j i)) (fun i => (selected i).1 (uni i))
  · have jin : Function.Injective j := fun i k eq => noRepeat i k ((uni i).trans (uni k).symm) eq
    exact uniform_from_darts hp (r ∘ j) l (r.injective.comp jin) l.injective
      (fun i k => (adj k (j i)).symm) (fun i => hr (j i)) hl (fun i => (selected i).2 (uni i))
  · have ik : i ≠ k := by
      intro eq
      subst k
      simp [hi] at hk
    exact two_from_darts hp (adj i (j i)) (adj k (j k)).symm
      (adj i (j k)) (adj k (j i)).symm ((selected i).1 hi) ((selected k).2 hk)
      (r.injective.ne jik) (l.injective.ne ik) (hl i) (hr (j i)) (hr (j k)) (hl k)
  · exact (ik (noRepeat i k sameDir sameRight)).elim

private theorem local_k33_exchange {V : Type} [DecidableEq V] {G : SimpleGraph V} {v : V}
    {p : G.Walk v v} {S : Set V} (hp : LovaszPlummerConjecture.IsHamiltonianCycle G p)
    (l r : Fin 3 ↪ V) (adj : ∀ i j, G.Adj (l i) (r j))
    (hl : ∀ i, l i ∈ S) (hr : ∀ j, r j ∈ S)
    (touch : ∀ i, ∃ j, s(l i,r j) ∈ p.edges) :
    localExchange p S := by
  classical
  choose j mem using touch
  have select i :
      ∃ dir : Bool,
        (dir = true → (⟨(l i,r (j i)),adj i (j i)⟩ : G.Dart) ∈ p.darts) ∧
        (dir = false → (⟨(r (j i),l i),(adj i (j i)).symm⟩ : G.Dart) ∈ p.darts) := by
    rcases (Walk.isSubwalk_toWalk_iff_mem_edges (adj i (j i))).mpr (mem i) with fwd | rev
    · exact ⟨true, fun _ => (Walk.isSubwalk_toWalk_iff_mem_darts ..).mp fwd, by simp⟩
    · exact ⟨false, by simp, fun _ => (Walk.isSubwalk_toWalk_iff_mem_darts ..).mp rev⟩
  choose dir sel using select
  exact orient_and_exchange hp l r adj hl hr j dir sel

end OMA.CycleExchange

theorem OMA.solution : OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1_H2_R1_H2_R1.H1 := by
  intro V _ _ G _ v p hp l r adj touch
  let S : Set V := Set.range l ∪ Set.range r
  have notMarked (z : V) (h : ∀ i, z ≠ l i ∧ z ≠ r i) : z ∉ S := by
    rintro (⟨i,e⟩ | ⟨i,e⟩)
    · exact (h i).1 e.symm
    · exact (h i).2 e.symm
  obtain ⟨w,q,hq,ne,agrees⟩ := OMA.CycleExchange.local_k33_exchange
    (S := S) hp l r adj (fun i => Or.inl ⟨i,rfl⟩) (fun i => Or.inr ⟨i,rfl⟩) touch
  refine ⟨w,q,hq,ne,?_⟩
  intro x y h
  apply agrees
  rcases h with hx | hy
  · exact ⟨x, Sym2.mem_iff.mpr (Or.inl rfl), notMarked x hx⟩
  · exact ⟨y, Sym2.mem_iff.mpr (Or.inr rfl), notMarked y hy⟩