import OMAReductions.R_SnakeInBox_coil_small_dimensions_R1
import Mathlib

/-! Decode induced paths by introducing new axes in order of first use. A coordinate
permutation fixing the previously used axes leaves the whole path history unchanged.
The omitted cycle vertex has code 1 and cannot touch an internal vertex of the
remaining path. This adapts @marcusbuffett’s dimension-six path search and
@dk8827’s induced-path tail and endpoint arguments. -/
namespace SixCoil
open SimpleGraph Finset symmDiff SnakeInBox

variable {V : Type} {G : SimpleGraph V}

private theorem no_neighbors_of_not_mem {a b x : V} (p : G.Walk a b)
    (hx : x ∉ p.support) : p.toSubgraph.neighborSet x = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact hx (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hy))

private theorem start_neighbors {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.toSubgraph.neighborSet a = if p.Nil then ∅ else {p.snd} := by
  cases p with
  | nil => simp [neighborSet_singletonSubgraph]
  | cons h p =>
    rw [Walk.cons_isPath_iff] at hp
    simp [Subgraph.neighborSet_sup, no_neighbors_of_not_mem p hp.2]

private theorem tail_induced {a b c : V} (h : G.Adj a b) (p : G.Walk b c)
    (hp : (Walk.cons h p).IsPath) (hi : (Walk.cons h p).toSubgraph.IsInduced) :
    p.toSubgraph.IsInduced := by
  have ha := ((Walk.cons_isPath_iff h p).mp hp).2
  intro x hx y hy hxy
  have hfull : (Walk.cons h p).toSubgraph.Adj x y :=
    hi ((Walk.cons h p).mem_verts_toSubgraph.mpr (by simp [p.mem_verts_toSubgraph.mp hx]))
      ((Walk.cons h p).mem_verts_toSubgraph.mpr (by simp [p.mem_verts_toSubgraph.mp hy])) hxy
  rw [Walk.toSubgraph, Subgraph.sup_adj] at hfull
  refine hfull.resolve_left ?_
  have hxa : x ≠ a := fun e => ha (e ▸ p.mem_verts_toSubgraph.mp hx)
  have hya : y ≠ a := fun e => ha (e ▸ p.mem_verts_toSubgraph.mp hy)
  simp [subgraphOfAdj_adj, Sym2.eq, hxa.symm, hya.symm]

private theorem cube_adj {n : ℕ} (a b : Finset (Fin n)) :
    (SnakeInBox.Hypercube n).Adj a b ↔ (a ∆ b).card = 1 := by
  rw [SnakeInBox.Hypercube, SimpleGraph.fromRel_adj, symmDiff_comm b a, or_self]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rintro rfl
  simp at h


abbrev Vtx := Finset (Fin 6)
private def code (v : Vtx) : ℕ := ∑ i ∈ v, 2^i.val
private def star (x : ℕ) : ℕ := (1 <<< x) ||| (1 <<< (x ^^^ 1)) ||| (1 <<< (x ^^^ 2)) |||
  (1 <<< (x ^^^ 4)) ||| (1 <<< (x ^^^ 8)) ||| (1 <<< (x ^^^ 16)) ||| (1 <<< (x ^^^ 32))
private theorem flipCode : ∀ (v : Vtx) (i : Fin 6),
    code (v ∆ {i}) = code v ^^^ (2^i.val) := by decide +kernel

private theorem codeInj : Function.Injective code := by
  have decode : ∀ x : Vtx, Finset.univ.filter (fun i : Fin 6 => (code x).testBit i.val) = x := by
    decide +kernel
  intro x y h
  rw [← decode x, ← decode y, h]

private theorem starSpec (x y : ℕ) : (star x).testBit y = true ↔
    x = y ∨ ∃ i : Fin 6, x ^^^ 2^i.val = y := by
  simp [star,Nat.testBit_or,Nat.shiftLeft_eq,Nat.testBit_two_pow,Fin.exists_fin_succ,or_assoc]

private theorem blocks (x y : Vtx) : (star (code x)).testBit (code y) = true ↔
    x = y ∨ (x ∆ y).card = 1 := by
  rw [starSpec]
  constructor
  · rintro (he | ⟨i,hi⟩)
    · exact Or.inl (codeInj he)
    · rw [← flipCode] at hi
      rw [← codeInj hi, symmDiff_symmDiff_cancel_left]
      simp
  · rintro (rfl | h)
    · exact Or.inl rfl
    · obtain ⟨i,hi⟩ := Finset.card_eq_one.mp h
      refine Or.inr ⟨i,?_⟩
      rw [← flipCode,← hi,symmDiff_symmDiff_cancel_left]

private def Small (u : ℕ) (v : Vtx) := ∀ i ∈ v, i.val < u

private structure Frame where
  f : Vtx ↪ Vtx
  dist : ∀ x y, (f x ∆ f y).card = (x ∆ y).card

private theorem mapDiff (e : Equiv.Perm (Fin 6)) (x y : Vtx) :
    (x ∆ y).map e.toEmbedding = x.map e.toEmbedding ∆ y.map e.toEmbedding := by
  simp only [Finset.symmDiff_def, Finset.map_union, Finset.map_sdiff]

private def changeFrame (e : Equiv.Perm (Fin 6)) (f : Frame) : Frame where
  f := f.f.trans ⟨Finset.map e.toEmbedding, Finset.map_injective _⟩
  dist x y := by
    change ((f.f x).map _ ∆ (f.f y).map _).card = _
    rw [← mapDiff, Finset.card_map, f.dist]

private theorem normalize (f : Frame) {u : ℕ} {a b : Vtx} (h : (Hypercube 6).Adj a b) :
    ∃ (g : Frame) (i : Fin 6), i.val ≤ u ∧
    (∀ z, Small u (f.f z) → g.f z = f.f z) ∧ g.f b = g.f a ∆ {i} := by
  obtain ⟨j,hj⟩ := card_eq_one.mp ((f.dist a b).trans ((cube_adj _ _).mp h))
  have hb : f.f b = f.f a ∆ {j} := by rw [← hj, symmDiff_symmDiff_cancel_left]
  by_cases hjlt : j.val ≤ u
  · exact ⟨f,j,hjlt,fun _ _ => rfl,hb⟩
  let i : Fin 6 := ⟨u, by omega⟩
  let e := Equiv.swap j i
  refine ⟨changeFrame e f,i,le_rfl,?_,?_⟩
  · intro z hz
    change (f.f z).map e.toEmbedding = f.f z
    apply Finset.ext
    intro c
    have fixed (t : Fin 6) (ht : t ∈ f.f z) : e t = t := by
      have := hz t ht
      exact Equiv.swap_apply_of_ne_of_ne (by intro eq; subst t; omega)
        (by intro eq; subst t; change u < u at this; omega)
    constructor
    · intro ht
      obtain ⟨t,ht,he⟩ := Finset.mem_map.mp ht
      change e t = c at he
      rwa [← he, fixed t ht]
    · intro ht
      exact Finset.mem_map.mpr ⟨c,ht,fixed c ht⟩
  · change (f.f b).map e.toEmbedding = (f.f a).map e.toEmbedding ∆ {i}
    rw [hb,mapDiff,Finset.map_singleton]
    simp [e]

private def history (f : Frame) : List Vtx → ℕ
  | [] => 0
  | h :: hs => history f hs ||| star (code (f.f h))

private theorem history_congr (f g : Frame) (hs : List Vtx)
    (he : ∀ z ∈ hs, f.f z = g.f z) : history f hs = history g hs := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    simp only [history, ih (fun z hz => he z (by simp [hz])), he h (by simp)]

private theorem clear (f : Frame) {hs : List Vtx} {x : Vtx}
    (hc : ∀ z ∈ hs, z ≠ x ∧ ¬ (Hypercube 6).Adj z x) :
    (history f hs).testBit (code (f.f x)) = false := by
  induction hs with
  | nil => simp [history]
  | cons z hs ih =>
    rw [history,Nat.testBit_or,ih (fun y hy => hc y (by simp [hy])),Bool.false_or]
    apply Bool.eq_false_iff.mpr
    intro ht
    rcases (blocks _ _).mp ht with he | ha
    · exact (hc z (by simp)).1 (f.f.injective he)
    · rw [f.dist] at ha
      exact (hc z (by simp)).2 ((cube_adj _ _).mpr ha)

-- Number of introduced coordinate axes, current vertex, and closed neighborhoods of past vertices.
private abbrev State := ℕ × ℕ × ℕ
private def next (s : State) : List State :=
  let (u,x,ban) := s
  (List.range (min 6 (u+1))).filterMap fun i =>
    let y := x ^^^ (2^i)
    if ban.testBit y then none else some (max u (i+1), y, ban ||| star x)
private def freeByte (b : ℕ) : ℕ := (0x112122312232334122323342334344512232334233434452334344534454556122323342334344523343445344545562334344534454556344545564556566712232334233434452334344534454556233434453445455634454556455656672334344534454556344545564556566734454556455656674556566756676778 >>> (4*(b%256)))%16
private def freeBytes : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1,b => freeByte b + freeBytes k (b >>> 8)

private theorem byteCount (b : ℕ) :
    freeByte b = ∑ i ∈ Finset.range 8, if b.testBit i then 0 else 1 := by
  have tab : ∀ v : Fin 256, freeByte v.val = ∑ i ∈ Finset.range 8,
      if v.val.testBit i then 0 else 1 := by decide +kernel
  let v : Fin 256 := ⟨b%256,Nat.mod_lt _ (by decide)⟩
  calc
    freeByte b = freeByte v.val := by simp [freeByte,v]
    _ = _ := (tab v).trans (Finset.sum_congr rfl (by
      intro i hi
      change (if (b % 2^8).testBit i then _ else _) = _
      rw [Nat.testBit_mod_two_pow b 8 i]; simp [Finset.mem_range.mp hi]))

private theorem freeCount (k b : ℕ) : freeBytes k b =
    ∑ i ∈ Finset.range (8*k), if b.testBit i then 0 else 1 := by
  induction k generalizing b with
  | zero => simp [freeBytes]
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm (8*k), Finset.sum_range_add, freeBytes, byteCount, ih]
    simp only [Nat.testBit_shiftRight]

private theorem fits {a b : Vtx} (p : (Hypercube 6).Walk a b) (hp : p.IsPath)
    (f : Frame) (hs : List Vtx)
    (hc : ∀ x ∈ p.support, x ≠ a → ∀ z ∈ hs, z ≠ x ∧ ¬ (Hypercube 6).Adj z x) :
    p.length ≤ freeBytes 8 (history f hs) := by
  have limit : ∀ x : Vtx, code x < 64 := by decide +kernel
  let E := p.support.toFinset.erase a
  have hcard : E.card = p.length := by
    simp [E,Finset.card_erase_of_mem, List.toFinset_card_of_nodup hp.support_nodup]
  let A := (Finset.range 64).filter (fun i => (history f hs).testBit i = false)
  have sub : E.image (fun v => code (f.f v)) ⊆ A := by
    intro y hy
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (limit _), clear f (hc v (List.mem_toFinset.mp hm) hne)⟩
  have hh := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ (fun _ _ he => f.f.injective (codeInj he)),hcard] at hh
  convert hh using 1
  rw [freeCount]
  simp only [A, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases (history f hs).testBit i <;> decide

private def inner (s : State) := (next s).filter (fun t => !(star 1).testBit t.2.1)
private def allowed (k : ℕ) (s : State) := if k = 0 then next s else inner s

private def dfs : ℕ → State → Bool
  | 0, _ => true
  | k+1, s => decide (k ≤ freeBytes 8 (s.2.2 ||| star s.2.1)) && (allowed k s).any (dfs k)

private theorem complete {k : ℕ} {a b : Vtx} (p : (Hypercube 6).Walk a b)
    (hp : p.IsPath) (hi : p.toSubgraph.IsInduced) (hk : k ≤ p.length)
    (f : Frame) (u : ℕ) (hs : List Vtx) (hu : ∀ z ∈ a::hs, Small u (f.f z))
    (o : Vtx) (hu0 : 0 < u) (ho : f.f o = {0})
    (outer : ∀ x ∈ p.support, x ≠ a → x ≠ b → o ≠ x ∧ ¬ (Hypercube 6).Adj o x)
    (hc : ∀ x ∈ p.support, x ≠ a → ∀ z ∈ hs, z ≠ x ∧ ¬ (Hypercube 6).Adj z x) :
    dfs k (u, code (f.f a), history f hs) = true := by
  induction k generalizing a b f u hs with
  | zero => rfl
  | succ k ih =>
    cases p with
    | nil => simp at hk
    | @cons a b c h p =>
      obtain ⟨hpath, ha⟩ := (Walk.cons_isPath_iff h p).mp hp
      obtain ⟨g,i,hidx,hfix,hflip⟩ := normalize f (u := u) h
      have he (z) (hz : z ∈ a::hs) := hfix z (hu z hz)
      have hstart := he a (by simp)
      have hgo : g.f o = {0} := (hfix o (by
        rw [ho]
        intro j hj
        have := Finset.mem_singleton.mp hj
        subst j
        exact hu0)).trans ho
      have hhist := history_congr g f hs (fun z hz => he z (by simp [hz]))
      have hcode : code (g.f b) = code (f.f a) ^^^ 2^i.val := by rw [hflip, flipCode,hstart]
      have safe := clear g (hc b (by simp) h.ne.symm)
      have htail : ∀ x ∈ p.support, x ≠ b → ∀ z ∈ a::hs, z ≠ x ∧ ¬(Hypercube 6).Adj z x := by
        intro x hx hxb z hz
        have hxa : x ≠ a := fun e => ha (e ▸ hx)
        rcases List.mem_cons.mp hz with hz | hz
        · subst z
          refine ⟨hxa.symm,?_⟩
          intro hax
          have hf := hi (Walk.start_mem_verts_toSubgraph (Walk.cons h p))
            ((Walk.cons h p).mem_verts_toSubgraph.mpr (by simp [hx])) hax
          change x ∈ (Walk.cons h p).toSubgraph.neighborSet a at hf
          rw [start_neighbors _ hp] at hf
          exact hxb (by simpa using hf)
        · exact hc x (by simp [hx]) hxa z hz
      apply Bool.and_eq_true_iff.mpr
      refine ⟨decide_eq_true ?_, ?_⟩
      · have bound := fits p hpath g (a::hs) htail
        simp only [history,hhist,hstart] at bound
        exact (show k ≤ p.length by simpa using hk).trans bound
      let st : State := (max u (i.val+1), code (g.f b), history g (a::hs))
      have hnext : st ∈ next (u,code (f.f a),history f hs) := by
        apply List.mem_filterMap.mpr
        refine ⟨i.val, List.mem_range.mpr (lt_min i.isLt (by omega)),?_⟩
        simp only [st,←hcode,←hhist,safe,Bool.false_eq_true,if_false,history,hstart]
      apply List.any_eq_true.mpr
      refine ⟨st,?_,?_⟩
      · by_cases hk0 : k = 0
        · simpa [allowed,hk0] using hnext
        · rw [allowed,if_neg hk0]
          apply List.mem_filter.mpr
          refine ⟨hnext,?_⟩
          have hnn : ¬ p.Nil := by
            intro hnil
            have := Walk.length_eq_zero_iff.mpr hnil
            simp only [Walk.length_cons] at hk
            omega
          obtain ⟨hne,hnadj⟩ := outer b (by simp) h.ne.symm (hpath.nil_iff_eq.not.mp hnn)
          have hf : code (g.f o) = 1 := by simp [hgo,code]
          change (!(star 1).testBit (code (g.f b))) = true
          rw [Bool.not_eq_true',← hf]
          apply Bool.eq_false_iff.mpr
          intro hit
          rcases (blocks _ _).mp hit with he | adj
          · exact hne (g.f.injective he)
          · exact hnadj ((cube_adj _ _).mpr ((g.dist o b) ▸ adj))
      apply ih p hpath (tail_induced h p hp hi) (by simpa using hk)
      · intro z hz t ht
        rcases List.mem_cons.mp hz with hz | hz
        · subst z
          rw [hflip] at ht
          rcases Finset.mem_union.mp (Finset.symmDiff_subset_union ht) with ht | ht
          · rw [hstart] at ht
            exact (hu a (by simp) t ht).trans_le (le_max_left ..)
          · have := Finset.mem_singleton.mp ht
            subst t
            exact (Nat.lt_succ_self _).trans_le (le_max_right ..)
        · rw [he z hz] at ht
          exact (hu z hz t ht).trans_le (le_max_left ..)
      · exact hu0.trans_le (le_max_left ..)
      · exact hgo
      · intro x hx _ hxc
        exact outer x (by simp [hx]) (fun he => ha (he ▸ hx)) hxc
      · exact htail

private def fringe : ℕ → State → List State
  | 0, s => [s]
  | h+1, s => (inner s).flatMap (fringe h)

private theorem cut (h d : ℕ) (hd0 : 0 < d) (s : State) (hp : dfs (d+h) s = true) :
    ∃ t ∈ fringe h s, dfs d t = true := by
  induction h generalizing s with
  | zero => exact ⟨s,by simp [fringe],hp⟩
  | succ h ih =>
    obtain ⟨v,hv,hh⟩ := List.any_eq_true.mp (Bool.and_eq_true_iff.mp hp).2
    obtain ⟨t,ht,hd⟩ := ih v hh
    change v ∈ allowed (d+h) s at hv
    rw [allowed,if_neg (show d+h ≠ 0 by omega)] at hv
    exact ⟨t,List.mem_flatMap.mpr ⟨v,hv,ht⟩,hd⟩

-- Partition the seven-edge frontier into groups of four. The coverage equality
-- and all depth-19 searches are computed by the kernel.
private def rootState : State := (1,0,0)
private def group (i : ℕ) := (((fringe 7 rootState).drop (4*i)).take 4)
private def passed (i : ℕ) := (group i).all fun t => !(dfs 19 t)

private theorem group0 : passed 0 = true := by decide +kernel
private theorem group1 : passed 1 = true := by decide +kernel
private theorem group2 : passed 2 = true := by decide +kernel
private theorem group3 : passed 3 = true := by decide +kernel
private theorem group4 : passed 4 = true := by decide +kernel
private theorem group5 : passed 5 = true := by decide +kernel
private theorem group6 : passed 6 = true := by decide +kernel
private theorem group7 : passed 7 = true := by decide +kernel
private theorem group8 : passed 8 = true := by decide +kernel
private theorem group9 : passed 9 = true := by decide +kernel
private theorem group10 : passed 10 = true := by decide +kernel
private theorem group11 : passed 11 = true := by decide +kernel
private theorem group12 : passed 12 = true := by decide +kernel
private theorem group13 : passed 13 = true := by decide +kernel
private theorem group14 : passed 14 = true := by decide +kernel
private theorem group15 : passed 15 = true := by decide +kernel
private theorem group16 : passed 16 = true := by decide +kernel
private theorem group17 : passed 17 = true := by decide +kernel
private theorem group18 : passed 18 = true := by decide +kernel
private theorem group19 : passed 19 = true := by decide +kernel
private theorem group20 : passed 20 = true := by decide +kernel
private theorem group21 : passed 21 = true := by decide +kernel
private theorem group22 : passed 22 = true := by decide +kernel
private theorem group23 : passed 23 = true := by decide +kernel
private theorem group24 : passed 24 = true := by decide +kernel
private theorem group25 : passed 25 = true := by decide +kernel
private theorem group26 : passed 26 = true := by decide +kernel
private theorem group27 : passed 27 = true := by decide +kernel
private theorem group28 : passed 28 = true := by decide +kernel
private theorem checked : dfs 26 (1,0,0) = false := by
  have cover : fringe 7 rootState = (List.range 29).flatMap group := by decide +kernel
  have all : (List.range 29).all passed = true := by
    have hr : List.range 29 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28] := by decide
    rw [hr]
    simp only [List.all_cons,List.all_nil,group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,Bool.true_and]
  apply Bool.eq_false_iff.mpr
  intro hh
  obtain ⟨t,ht,hd⟩ := cut 7 19 (by decide) rootState hh
  rw [cover] at ht
  obtain ⟨i,hi,hit⟩ := List.mem_flatMap.mp ht
  have ok := List.all_eq_true.mp all i hi
  simpa [hd] using List.all_eq_true.mp ok t hit

private lemma evenCycle {a : Vtx} (p : (Hypercube 6).Walk a a) : Even p.length := by
  have different : ∀ x y : Vtx, (x ∆ y).card = 1 →
      decide (Even x.card) ≠ decide (Even y.card) := by decide +kernel
  let c : (Hypercube 6).Coloring Bool :=
    Coloring.mk (fun x => decide (Even x.card)) (fun h => different _ _ ((cube_adj _ _).mp h))
  exact (c.even_length_iff_congr p).mpr Iff.rfl

private lemma cycleBound {u : Vtx} (p : (Hypercube 6).Walk u u)
    (hc : p.IsCycle) (hi : p.toSubgraph.IsInduced) : p.length ≤ 26 := by
  have he := evenCycle p
  cases p with
  | nil => simp
  | @cons a b c h q =>
    have hq : q.IsPath := by simpa using hc.isPath_tail
    have hlen := hc.three_le_length
    have hn : ¬ q.Nil := by
      intro hz
      have := Walk.length_eq_zero_iff.mpr hz
      simp_all
    let e := q.adj_penultimate hn
    have spec := q.concat_dropLast e
    have hnot : u ∉ q.dropLast.support := by
      have hnodup := hq.support_nodup
      rw [← spec, Walk.support_concat, List.nodup_append] at hnodup
      exact fun hx => hnodup.2.2 u hx u (by simp) rfl
    have hsub : q.dropLast.toSubgraph ≤ (Walk.cons h q).toSubgraph := by
      change _ ≤ _ ⊔ q.toSubgraph
      apply le_trans _ le_sup_right
      conv_rhs => rw [← spec, Walk.concat_eq_append, Walk.toSubgraph_append]
      exact le_sup_left
    have hind : q.dropLast.toSubgraph.IsInduced := by
      intro x hx y hy hxy
      have hxa : x ≠ u := fun hh => hnot (hh ▸ q.dropLast.mem_verts_toSubgraph.mp hx)
      have hya : y ≠ u := fun hh => hnot (hh ▸ q.dropLast.mem_verts_toSubgraph.mp hy)
      have hf := hi (hsub.1 hx) (hsub.1 hy) hxy
      rw [Walk.toSubgraph, Subgraph.sup_adj] at hf
      have hr : q.toSubgraph.Adj x y := hf.resolve_left (by
        simp [subgraphOfAdj_adj, Sym2.eq, hxa.symm, hya.symm])
      rw [← spec, Walk.concat_eq_append, Walk.toSubgraph_append, Subgraph.sup_adj] at hr
      exact hr.resolve_right (by simp [Walk.toSubgraph, subgraphOfAdj_adj, Sym2.eq, hxa, hya, hxa.symm, hya.symm])
    by_contra! hlarge
    have hlong : 26 ≤ q.dropLast.length := by
      rw [Walk.length_dropLast]
      simp only [Walk.length_cons] at he hlarge
      obtain ⟨m,hm⟩ := he
      omega
    let f : Frame := ⟨⟨fun x => x ∆ b, fun _ _ => symmDiff_left_inj.mp⟩, fun x y => by
      change ((x ∆ b) ∆ (y ∆ b)).card = _
      rw [← symmDiff_assoc, symmDiff_right_comm x b y, symmDiff_symmDiff_cancel_right]⟩
    obtain ⟨g,i,hle,hfix,hflip⟩ := normalize f (u := 0) h.symm
    have hi0 : i = 0 := Fin.ext (by omega)
    have hstart : g.f b = ∅ := by
      apply (hfix b (by change Small 0 (b ∆ b); simp [Small])).trans
      change b ∆ b = ∅
      simp
    have hgo : g.f u = {0} := by simpa [hi0,hstart,Finset.symmDiff_def] using hflip
    have extFree : ∀ x ∈ q.dropLast.support, x ≠ b → x ≠ q.penultimate →
        u ≠ x ∧ ¬ (Hypercube 6).Adj u x := by
      intro x hx hxb hxl
      refine ⟨fun he => hnot (he ▸ hx),?_⟩
      intro adj
      have hall := hi (Walk.start_mem_verts_toSubgraph (Walk.cons h q))
        (hsub.1 (q.dropLast.mem_verts_toSubgraph.mpr hx)) adj
      change x ∈ (Walk.cons h q).toSubgraph.neighborSet u at hall
      rw [hc.neighborSet_toSubgraph_endpoint] at hall
      simpa [Walk.penultimate_cons_of_not_nil h q hn,hxb,hxl] using hall
    have hf := complete q.dropLast hq.dropLast hind hlong g 1 [] (by
      intro z hz
      have hz' : z = b := by simpa using hz
      simp [hz',hstart,Small]) u (by decide) hgo extFree (by simp)
    simpa [hstart,code,history,checked] using hf

end SixCoil

theorem OMA.solution : OMA.R_SnakeInBox_coil_small_dimensions_R1.H2 := by
  apply csSup_le'
  rintro k ⟨S, hi, u, p, hc, rfl, rfl⟩
  exact SixCoil.cycleBound p hc hi
