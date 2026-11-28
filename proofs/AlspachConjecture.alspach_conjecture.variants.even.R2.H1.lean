import OMAReductions.R_AlspachConjecture_alspach_conjecture_variants_even_R2

/-!
# Decompositions of complete graphs minus a perfect matching at even orders up to fourteen

For each positive even order n at most 14 we pick the opposite-pair perfect
matching J on Fin n (pairing i with i + n / 2) and construct cycle decompositions
of K_n \ J for every admissible multiset of cycle lengths.

- Orders 2 and 4 are immediate (0 edges and a single 4-cycle).
- Orders 6, 8, and 10 (12, 24, and 40 edges) use direct hex-encoded certificate
  tables (5, 42, and 511 partitions).
- Order 12 (60 edges) splits K_12 \ J into complementary 30-edge triangle-packable
  even subgraphs (each realizing all 213 partitions of 30). For the 351 partitions
  with no subset summing to 30, a 4-cycle symmetric difference yields a (28, 32)
  split whose two small libraries cover 314 cases, leaving 37 direct certificates.
- Order 14 (84 edges) splits K_14 \ J into two isomorphic 6-regular 42-edge
  subgraphs swapped by an explicit permutation of Fin 14, realizing all 1442
  partitions of 42 via a single table plus graph transport. For the 1399
  partitions with no subset summing to 42, a 4-cycle symmetric difference yields
  a (40, 44) split whose two libraries cover 1335 cases, leaving 64 direct
  certificates.

Credit: The hex-encoded cycle verifier, bitmap packing, subset-sum bitset
splitting, and screened library verification architecture are adapted from
@Deldor14's odd-order proof (AlspachConjecture.alspach_conjecture.R1.H1).
-/
namespace OMA.AlspachEvenFinite

open SimpleGraph AlspachConjecture
open scoped Classical

private abbrev K (n : Nat) := completeGraph (Fin n)

private def matchSubgraph (n : Nat) (hn : Even n) (hpos : 0 < n) : (K n).Subgraph where
  verts := Set.univ
  Adj u v := u.val + n / 2 = v.val ∨ v.val + n / 2 = u.val
  adj_sub {u v} h := by
    intro heq
    subst heq
    obtain ⟨r, hr⟩ := hn
    omega
  edge_vert _ := trivial
  symm := ⟨fun _ _ h => Or.symm h⟩

private theorem matchSubgraph_perfect (n : Nat) (hn : Even n) (hpos : 0 < n) :
    (matchSubgraph n hn hpos).IsPerfectMatching := by
  rw [Subgraph.isPerfectMatching_iff]
  obtain ⟨r, hr⟩ := hn
  intro v
  by_cases hv : v.val < n / 2
  · refine ⟨⟨v.val + n / 2, by omega⟩, Or.inl rfl, ?_⟩
    intro y hy
    ext
    rcases hy with h | h <;> dsimp at h ⊢ <;> omega
  · refine ⟨⟨v.val - n / 2, by omega⟩, Or.inr (by dsimp; omega), ?_⟩
    intro y hy
    ext
    rcases hy with h | h <;> dsimp at h ⊢ <;> omega

private def chain {n : Nat} (a b : Fin n) : List (Fin n) → Bool
  | [] => a != b
  | x::xs => (a != x) && chain x b xs

private def trail {n : Nat} (a b : Fin n) : (l : List (Fin n)) → chain a b l = true → (K n).Walk a b
  | [], h => .cons (by simpa [chain] using h) .nil
  | x::xs, h => .cons (by simpa [chain] using (Bool.and_eq_true_iff.mp h).1)
      (trail x b xs ((Bool.and_eq_true_iff.mp h).2))

private def arcs {n : Nat} (a b : Fin n) : List (Fin n) → List (Fin n × Fin n)
  | [] => [(a,b)]
  | x::xs => (a,x)::arcs x b xs

private lemma trail_length {n : Nat} (a b : Fin n) (l : List (Fin n)) (h) :
    (trail a b l h).length=l.length+1 := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => simp [trail,ih]

private lemma trail_support {n : Nat} (a b : Fin n) (l : List (Fin n)) (h) :
    (trail a b l h).support=a::(l++[b]) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => simp [trail,ih]

private lemma trail_edges {n : Nat} (a b : Fin n) (l : List (Fin n)) (h) :
    (trail a b l h).edges=(arcs a b l).map (fun p => s(p.1,p.2)) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => simp [trail,arcs,ih]

private abbrev Code (n : Nat) := Fin n × List (Fin n)

private def good {n : Nat} (c : Code n) : Bool :=
  chain c.1 c.1 c.2 && decide ((c.2++[c.1]).Nodup) && decide (3≤c.2.length+1)

private def cyc {n : Nat} (c : Code n) (h : good c=true) : Cycle (K n) := by
  have facts := Bool.and_eq_true_iff.mp h
  have hface := Bool.and_eq_true_iff.mp facts.1
  refine ⟨c.1, trail c.1 c.1 c.2 hface.1, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_,?_⟩⟩
  · apply (Walk.isPath_def _).mpr
    rw [Walk.support_tail_of_not_nil _ (by simp [← Walk.length_eq_zero_iff,trail_length]),trail_support]
    simpa using of_decide_eq_true hface.2
  · rw [trail_length]
    exact of_decide_eq_true facts.2

private lemma cyc_length {n : Nat} (c : Code n) (h : good c=true) :
    (cyc c h).length=c.2.length+1 := trail_length ..

private lemma cyc_edges {n : Nat} (c : Code n) (h : good c=true) :
    (cyc c h).edges=(arcs c.1 c.1 c.2).map (fun p => s(p.1,p.2)) := trail_edges ..

private def key {n : Nat} (p : Fin n × Fin n) :=
  Nat.pair (min p.1.val p.2.val) (max p.1.val p.2.val)

private theorem key_iff {n : Nat} (p q : Fin n × Fin n) :
    key p=key q ↔ s(p.1,p.2)=s(q.1,q.2) := by
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  simp only [key,Nat.pair_eq_pair,Sym2.eq_iff,Fin.ext_iff]
  omega

private def bitmap {n : Nat} : List (Fin n × Fin n) → Nat
  | [] => 0
  | p::ps => (1 <<< key p) ||| bitmap ps

private lemma read_bitmap {n : Nat} (ps : List (Fin n × Fin n)) (q : Fin n × Fin n) :
    (bitmap ps).testBit (key q)=true ↔ s(q.1,q.2) ∈ ps.map (fun p => s(p.1,p.2)) := by
  induction ps with
  | nil => simp [bitmap]
  | cons p ps ih =>
    rw [bitmap,Nat.testBit_or,Bool.or_eq_true_iff]
    have bit : (1 <<< key p).testBit (key q) = decide (key p=key q) := by
      rw [Nat.shiftLeft_eq,one_mul,Nat.testBit_two_pow]
    rw [bit, decide_eq_true_eq, key_iff,ih,List.map_cons,List.mem_cons]
    exact or_congr_left eq_comm

private def pack {n : Nat} : List (Code n) → Option Nat
  | [] => some 0
  | c::cs => do
    let rest ← pack cs
    let b := bitmap (arcs c.1 c.1 c.2)
    if good c && (b &&& rest == 0) then some (b ||| rest) else none

private lemma packed {n : Nat} (cs : List (Code n)) (k : Nat) (hc : pack cs=some k) :
    ∃ C : Multiset (Cycle (K n)), lengths C = ((cs.map fun c => c.2.length+1) : List Nat) ∧
      ∀ q : Fin n × Fin n, (C.filter fun c => s(q.1,q.2) ∈ c.edges).card =
        (k.testBit (key q)).toNat := by
  classical
  induction cs generalizing k with
  | nil =>
    have z : k=0 := by simpa [pack,eq_comm] using hc
    exact ⟨0,rfl,fun q => by simp [z]⟩
  | cons c cs ih =>
    cases h : pack cs with
    | none => simp [pack,h] at hc
    | some r =>
      let bits := bitmap (arcs c.1 c.1 c.2)
      have facts : (good c=true ∧ bits &&& r=0) ∧ bits ||| r=k := by
        simpa [pack,h,bits] using hc
      obtain ⟨⟨cgood,dis⟩,get'⟩ := facts
      have get := get'.symm
      obtain ⟨C,lens,count⟩ := ih r h
      refine ⟨cyc c cgood ::ₘ C,?_,?_⟩
      · simpa [lengths,cyc_length] using congrArg (Multiset.cons (c.2.length+1)) lens
      · intro q
        have mem : s(q.1,q.2) ∈ (cyc c cgood).edges ↔ bits.testBit (key q)=true := by
          rw [cyc_edges]; exact (read_bitmap _ _).symm
        have distinct := congrArg (fun m : Nat => m.testBit (key q)) dis
        rw [get,Nat.testBit_or]
        by_cases own : bits.testBit (key q)=true
        · have zero : r.testBit (key q)=false := by simpa [own] using distinct
          rw [Multiset.filter_cons_of_pos (p:=fun v : Cycle (K n) => s(q.1,q.2) ∈ v.edges) C (mem.mpr own),Multiset.card_cons,count]
          simp [own,zero]
        · rw [Multiset.filter_cons_of_neg (p:=fun v : Cycle (K n) => s(q.1,q.2) ∈ v.edges) C (fun e => own (mem.mp e)),count]
          simp [own]

private def minusMatch (n : Nat) : Nat :=
  bitmap ((List.finRange n).flatMap fun a =>
    ((List.finRange n).filter fun b =>
      (b != a) && !((a.val + n / 2 == b.val) || (b.val + n / 2 == a.val))).map (fun b => (a,b)))

private lemma minusMatch_iff {n : Nat} (a b : Fin n) :
    (minusMatch n).testBit (key (a,b)) = true ↔
      a ≠ b ∧ ¬ (a.val + n / 2 = b.val ∨ b.val + n / 2 = a.val) := by
  rw [minusMatch, read_bitmap]
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, hxy, heq⟩ := List.mem_map.mp h
    obtain ⟨x', _, hxy'⟩ := List.mem_flatMap.mp hxy
    obtain ⟨y', hy', hpair⟩ := List.mem_map.mp hxy'
    cases hpair
    simp only [List.mem_filter, List.mem_finRange, true_and, Bool.and_eq_true, bne_iff_ne,
      Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hy'
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hy'.1.symm, fun hm => hm.elim hy'.2.1 hy'.2.2⟩
    · exact ⟨hy'.1, fun hm => hm.elim hy'.2.2 hy'.2.1⟩
  · rintro ⟨hne, hnm⟩
    apply List.mem_map.mpr
    refine ⟨(a, b), List.mem_flatMap.mpr ⟨a, by simp, ?_⟩, rfl⟩
    apply List.mem_map.mpr
    refine ⟨b, ?_, rfl⟩
    simp only [List.mem_filter, List.mem_finRange, true_and, Bool.and_eq_true, bne_iff_ne,
      Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨hne.symm, fun h => hnm (Or.inl h), fun h => hnm (Or.inr h)⟩

private def digit {n : Nat} (hn : 0<n) (z : Nat) : Fin n :=
  ⟨(z%16)%n,Nat.mod_lt _ hn⟩

private def digits {n : Nat} (hn : 0<n) : Nat → Nat → List (Fin n)
  | 0,_ => []
  | k+1,z => digit hn z :: digits hn k (z >>> 4)

private lemma digits_length {n : Nat} (hn : 0<n) (k z : Nat) : (digits hn k z).length=k := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => simp [digits,ih]

private def decode {n : Nat} (hn : 0<n) : List Nat → Nat → List (Code n)
  | [],_ => []
  | d::ds,z => (digit hn z,digits hn (d-1) (z >>> 4)) :: decode hn ds (z >>> (4*d))

private lemma decode_lengths {n : Nat} (hn : 0<n) (ds : List Nat) (z : Nat) (hd : ∀ d∈ds,0<d) :
    (decode hn ds z).map (fun c => c.2.length+1)=ds := by
  induction ds generalizing z with
  | nil => rfl
  | cons d ds ih =>
    simp only [decode,List.map_cons,digits_length]
    rw [ih _ (fun e he => hd e (List.mem_cons_of_mem _ he))]
    have := hd d (List.mem_cons_self ..)
    congr 1
    omega

private def Covers (n mask : Nat) (m : Multiset Nat) : Prop :=
  ∃ C : Multiset (Cycle (K n)), lengths C=m ∧ ∀ q : Fin n × Fin n,
    (C.filter fun c => s(q.1,q.2) ∈ c.edges).card=(mask.testBit (key q)).toNat

private def Realizes (n : Nat) (m : Multiset Nat) : Prop :=
  ∃ J : (K n).Subgraph, J.IsPerfectMatching ∧
    ∃ C : Multiset (Cycle (K n \ J.spanningCoe)),
      IsCycleDecomposition (K n \ J.spanningCoe) C ∧ lengths C = m

private theorem realizes_of_cover {n : Nat} (hn : Even n) (hpos : 0 < n) {m : Multiset Nat}
    (h : Covers n (minusMatch n) m) : Realizes n m := by
  classical
  let J := matchSubgraph n hn hpos
  let H := K n \ J.spanningCoe
  obtain ⟨C, hlen, hcnt⟩ := h
  have hadj : ∀ a b : Fin n, H.Adj a b ↔ (minusMatch n).testBit (key (a,b)) = true := by
    intro a b
    rw [minusMatch_iff]
    simp [H, J, matchSubgraph]
  have hsub : ∀ c ∈ C, ∀ e ∈ c.walk.edges, e ∈ H.edgeSet := by
    intro c hc e he
    induction e using Sym2.ind with
    | _ a b =>
      have hpos_card : 0 < (C.filter fun v => s(a,b) ∈ v.edges).card :=
        Multiset.card_pos_iff_exists_mem.mpr ⟨c, Multiset.mem_filter.mpr ⟨hc, he⟩⟩
      rw [hcnt (a,b)] at hpos_card
      have htb : (minusMatch n).testBit (key (a,b)) = true := by
        cases hb : (minusMatch n).testBit (key (a,b)) <;> simp_all
      exact (hadj a b).mpr htb
  let lift : ∀ c : Cycle (K n), (∀ e ∈ c.walk.edges, e ∈ H.edgeSet) → Cycle H := fun c hc =>
    ⟨c.base, c.walk.transfer H hc, by
      rw [Walk.isCycle_iff_isPath_tail_and_le_length]
      have hc' := Walk.isCycle_iff_isPath_tail_and_le_length.mp c.isCycle
      constructor
      · rw [Walk.isPath_def, Walk.support_tail_of_not_nil _ (by
            have := hc'.2; rw [← Walk.length_eq_zero_iff, Walk.length_transfer]; omega),
          Walk.support_transfer]
        have hp := (Walk.isPath_def _).mp hc'.1
        rw [Walk.support_tail_of_not_nil _ (by
            have := hc'.2; rw [← Walk.length_eq_zero_iff]; omega)] at hp
        exact hp
      · rw [Walk.length_transfer]
        exact hc'.2⟩
  let D : Multiset (Cycle H) := C.attach.map fun c => lift c.1 (hsub c.1 c.2)
  refine ⟨J, matchSubgraph_perfect n hn hpos, D, ?_, ?_⟩
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : H.Adj a b := by simpa [H, SimpleGraph.mem_edgeFinset] using he
      have htb : (minusMatch n).testBit (key (a,b)) = true := (hadj a b).mp hab
      have hcard : (D.filter fun d => s(a,b) ∈ d.edges).card =
          (C.filter fun c => s(a,b) ∈ c.edges).card := by
        dsimp only [D]
        rw [Multiset.filter_map, Multiset.card_map]
        have h1 : C.attach.filter ((fun d : Cycle H => s(a,b) ∈ d.edges) ∘
            fun c : {x // x ∈ C} => lift c.1 (hsub c.1 c.2)) =
            C.attach.filter (fun c : {x // x ∈ C} => s(a,b) ∈ c.1.edges) := by
          apply Multiset.filter_congr
          intro c _
          change s(a,b) ∈ (c.1.walk.transfer H (hsub c.1 c.2)).edges ↔ s(a,b) ∈ c.1.walk.edges
          rw [Walk.edges_transfer]
        rw [h1]
        have hattach : (C.filter fun c => s(a,b) ∈ c.edges) =
            (C.attach.filter fun c : {x // x ∈ C} => s(a,b) ∈ c.1.edges).map Subtype.val := by
          conv_lhs => rw [← Multiset.attach_map_val C]
          rw [Multiset.filter_map]
          rfl
        rw [hattach, Multiset.card_map]
      rw [hcard, hcnt (a,b), htb]
      rfl
  · have hlenD : lengths D = lengths C := by
      dsimp only [lengths, D]
      rw [Multiset.map_map]
      have hfn : ((fun d : Cycle H => d.length) ∘ fun c : {x // x ∈ C} => lift c.1 (hsub c.1 c.2)) =
          fun c : {x // x ∈ C} => c.1.length := by
        funext c
        exact Walk.length_transfer c.1.walk (hsub c.1 c.2)
      rw [hfn]
      conv_rhs => rw [← Multiset.attach_map_val C]
      rw [Multiset.map_map]
      rfl
    exact hlenD.trans hlen

private theorem raw_cover {n : Nat} (hn : 0<n) (mask : Nat) (ds : List Nat) (z : Nat)
    (pos : ∀ d∈ds,0<d) (ok : pack (decode hn ds z)=some mask) : Covers n mask ds := by
  obtain ⟨C,hl,hc⟩ := packed _ _ ok
  exact ⟨C,hl.trans (congrArg (fun l : List Nat => (l : Multiset Nat)) (decode_lengths hn ds z pos)),hc⟩

private theorem union_cover {n a b : Nat} {s t : Multiset Nat} (dis : a &&& b=0)
    (A : Covers n a s) (B : Covers n b t) : Covers n (a ||| b) (s+t) := by
  classical
  obtain ⟨C,lc,hc⟩ := A
  obtain ⟨D,ld,hd⟩ := B
  refine ⟨C+D,by simpa [lengths] using congrArg₂ (·+·) lc ld,?_⟩
  intro q
  rw [Multiset.filter_add,Multiset.card_add,hc,hd,Nat.testBit_or]
  have h := congrArg (fun z : Nat => z.testBit (key q)) dis
  change (a &&& b).testBit (key q) = Nat.testBit 0 (key q) at h
  rw [Nat.testBit_and,Nat.zero_testBit] at h
  cases ha : a.testBit (key q) <;> cases hb : b.testBit (key q) <;> simp_all

private def partitions (n : Nat) : Nat → Nat → Nat → List (List Nat)
  | 0,_,t => if t=0 then [[]] else []
  | fuel+1,lo,t =>
    if t=0 then [[]] else
    (List.range (n+1)).flatMap (fun d => if lo≤d ∧ d≤t then
      (partitions n fuel d (t-d)).map (d::·) else [])

private theorem in_partitions {n lo t fuel : Nat} (l : List Nat) (hs : l.Pairwise (·≤·))
    (hr : ∀ d∈l,lo≤d ∧ d≤n) (hl : l.length≤fuel) (ht : l.sum=t) (hlo : 0<lo) :
    l ∈ partitions n fuel lo t := by
  induction fuel generalizing l lo t with
  | zero =>
    have : l=[] := List.length_eq_zero_iff.mp (by omega)
    subst l
    simp_all [partitions]
  | succ fuel ih =>
    cases l with
    | nil => simp_all [partitions]
    | cons d ds =>
      have hdl := hr d (List.mem_cons_self ..)
      have hlen : ds.length≤fuel := by simpa using hl
      have hsum : d+ds.sum=t := by simpa using ht
      have htpos : t≠0 := by omega
      rw [partitions,if_neg htpos]
      apply List.mem_flatMap.mpr
      refine ⟨d,List.mem_range.mpr (by omega),?_⟩
      rw [if_pos (show lo≤d ∧ d≤t by omega)]
      apply List.mem_map.mpr
      obtain ⟨hbefore,hs'⟩ := List.pairwise_cons.mp hs
      exact ⟨ds,ih ds hs' (fun e he => ⟨hbefore e he,(hr e (List.mem_cons_of_mem _ he)).2⟩)
        hlen (by omega) (by omega),rfl⟩

private def sums : List Nat → Nat
  | [] => 1
  | d::ds => let f := sums ds; f ||| (f <<< d)

private theorem split_sum (ds : List Nat) (k : Nat) (h : (sums ds).testBit k=true) :
    ∃ a b : Multiset Nat, (ds : Multiset Nat)=a+b ∧ a.sum=k := by
  induction ds generalizing k with
  | nil =>
    have eq : k=0 := by
      rw [show sums []=2^0 by rfl,Nat.testBit_two_pow,decide_eq_true_eq] at h
      exact h.symm
    exact ⟨0,0,by simp,by simp [eq]⟩
  | cons d ds ih =>
    rw [sums,Nat.testBit_or,Bool.or_eq_true_iff] at h
    rcases h with h|h
    · obtain ⟨a,b,e,s⟩ := ih k h
      exact ⟨a,d::ₘ b,by change d ::ₘ (ds : Multiset Nat) = _; rw [e]; simp,s⟩
    · rw [Nat.testBit_shiftLeft,Bool.and_eq_true_iff] at h
      obtain ⟨a,b,e,s⟩ := ih (k-d) h.2
      have d_le := of_decide_eq_true h.1
      exact ⟨d::ₘ a,b,by change d ::ₘ (ds : Multiset Nat) = _; rw [e]; simp,by simp [s]; omega⟩

private def selected (k : Option Nat) (l : List Nat) : Bool :=
  match k with
  | none => true
  | some q => !(sums l).testBit q

private def certs {n : Nat} (hn : 0<n) (mask : Nat) (front : List Nat) (k : Option Nat) :
    List (List Nat) → List Nat → Bool
  | [],zs => zs.isEmpty
  | l::ls,zs =>
    let ds := front.reverse++l
    if selected k ds then
      match zs with
      | [] => false
      | z::zs' => (pack (decode hn ds z) == some mask) && certs hn mask front k ls zs'
    else certs hn mask front k ls zs

private def Region (n mask : Nat) (front : List Nat) (fuel lo t : Nat) (k : Option Nat) : Prop :=
  ∀ ds ∈ partitions n fuel lo t, (∀ d ∈ front.reverse++ds,0<d) →
    selected k (front.reverse++ds) = true → Covers n mask ((front.reverse++ds : List Nat) : Multiset Nat)

private theorem certs_sound {n : Nat} {hn : 0<n} {front : List Nat} (mask : Nat) (k : Option Nat)
    (ls : List (List Nat)) (zs : List Nat) (ok : certs hn mask front k ls zs=true) :
    ∀ l∈ls, (∀ j∈front.reverse++l,0<j) → selected k (front.reverse++l)=true →
      Covers n mask ((front.reverse++l : List Nat) : Multiset Nat) := by
  induction ls generalizing zs with
  | nil => simp
  | cons l ls ih =>
    by_cases hc : selected k (front.reverse++l)=true
    · cases zs with
      | nil => simp [certs,hc] at ok
      | cons z zs =>
        obtain ⟨this,rest⟩ := Bool.and_eq_true_iff.mp (show _ from (by simpa only [certs,if_pos hc] using ok))
        intro d hd hpos hsel
        rcases List.mem_cons.mp hd with rfl|hm
        · exact raw_cover hn mask _ z hpos (eq_of_beq this)
        · exact ih zs rest d hm hpos hsel
    · have ht : certs hn mask front k ls zs=true := by simpa [certs,hc] using ok
      intro d hd hp hs
      rcases List.mem_cons.mp hd with rfl|hm
      · exact False.elim (hc hs)
      · exact ih zs ht d hm hp hs

private theorem of_certs {n : Nat} {hn : 0<n} {front : List Nat} {fuel lo t : Nat} {mask : Nat}
    {k : Option Nat} (zs : List Nat) (ok : certs hn mask front k (partitions n fuel lo t) zs=true) :
    Region n mask front fuel lo t k := certs_sound mask k _ _ ok

private theorem split_region {n mask lo t fuel : Nat} {front : List Nat} {k : Option Nat} (ht : 0<t)
    (kids : ∀ d : Nat, lo≤d → d≤n → d≤t → Region n mask (d::front) fuel d (t-d) k) :
    Region n mask front (fuel+1) lo t k := by
  intro ds hm hp sel
  rw [partitions,if_neg ht.ne'] at hm
  obtain ⟨d,hd,hd'⟩ := List.mem_flatMap.mp hm
  by_cases h : lo≤d ∧ d≤t
  · rw [if_pos h] at hd'
    obtain ⟨ds',hs,rfl⟩ := List.mem_map.mp hd'
    simpa using kids d h.1 (by simpa using hd) h.2 ds' hs (by simpa using hp) (by simpa using sel)
  · simp [h] at hd'

private theorem absent_region {n mask lo t fuel : Nat} {front : List Nat} {k : Option Nat}
    (empty : partitions n fuel lo t = []) : Region n mask front fuel lo t k := by
  intro ds h
  simp [empty] at h

private theorem top_region {n mask t : Nat} {k : Option Nat}
    (all : Region n mask [] t 3 t k) (m : Multiset Nat) (bound : ∀ d∈m,3≤d ∧ d≤n)
    (total : m.sum=t) (sel : selected k (m.sort (·≤·))=true) : Covers n mask m := by
  let l := m.sort (·≤·)
  have e : (l : Multiset Nat)=m := Multiset.sort_eq ..
  have ls : l.sum=t := by convert total using 1; exact congrArg Multiset.sum e
  have lim (d : Nat) (hd : d∈l) : 3≤d ∧ d≤n := bound d (by simpa [l] using hd)
  have length_le_sum (xs : List Nat) (pos : ∀ d∈xs,0<d) : xs.length≤xs.sum := by
    induction xs with
    | nil => simp
    | cons a as ih =>
      have h := ih (fun d hd => pos d (List.mem_cons_of_mem _ hd))
      have ha := pos a (List.mem_cons_self ..)
      simp only [List.length_cons,List.sum_cons]
      omega
  have hl := length_le_sum l (fun d hd => by have := lim d hd; omega)
  have has := in_partitions l (Multiset.pairwise_sort ..) lim (hl.trans_eq ls) ls (by decide)
  have done := all l has (by simpa using fun d hd => (by have := lim d hd; omega : 0<d)) (by simpa [l] using sel)
  simpa [e] using done

private theorem patched {n p q left right total : Nat} (hn : Even n) (hpos : 0 < n)
    (parts : left+right=total) (union : p ||| q=minusMatch n) (dis : p &&& q=0)
    (A : Region n p [] left 3 left none) (B : Region n q [] right 3 right none)
    (others : Region n (minusMatch n) [] total 3 total (some left))
    (m : Multiset Nat) (bound : ∀ d∈m,3≤d ∧ d≤n) (sm : m.sum=total) : Realizes n m := by
  apply realizes_of_cover hn hpos
  let l := m.sort (·≤·)
  by_cases hit : (sums l).testBit left=true
  · obtain ⟨a,b,e,sa⟩ := split_sum l left hit
    have ab : m=a+b := (Multiset.sort_eq m (·≤·)).symm.trans e
    have aa := top_region A a (fun d hd => bound d (ab ▸ Multiset.mem_add.mpr (Or.inl hd))) sa rfl
    have sb : b.sum=right := by rw [ab,Multiset.sum_add,sa] at sm; omega
    have bb := top_region B b (fun d hd => bound d (ab ▸ Multiset.mem_add.mpr (Or.inr hd))) sb rfl
    rw [ab,←union]
    exact union_cover dis aa bb
  · exact top_region others m bound sm (by simpa [selected,l] using hit)

private lemma can_zero (l : List Nat) : (sums l).testBit 0=true := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    rw [sums,Nat.testBit_or,Bool.or_eq_true_iff]
    exact Or.inl ih

private lemma can_total (l : List Nat) : (sums l).testBit l.sum=true := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    rw [sums,Nat.testBit_or,Bool.or_eq_true_iff]
    apply Or.inr
    simpa [Nat.testBit_shiftLeft] using ih

private theorem extend_sum (u v : List Nat) (k h : Nat) (hu : (sums u).testBit k=true)
    (hv : (sums v).testBit h=true) : (sums (u++v)).testBit (k+h)=true := by
  induction u generalizing k with
  | nil =>
    have z : k=0 := by
      rw [show sums []=2^0 by rfl,Nat.testBit_two_pow,decide_eq_true_eq] at hu
      exact hu.symm
    simpa [z] using hv
  | cons d ds ih =>
    rw [sums,Nat.testBit_or,Bool.or_eq_true_iff] at hu
    rw [List.cons_append,sums,Nat.testBit_or,Bool.or_eq_true_iff]
    rcases hu with hu|hu
    · exact Or.inl (ih k hu)
    · rw [Nat.testBit_shiftLeft,Bool.and_eq_true_iff] at hu
      have le := of_decide_eq_true hu.1
      right
      rw [Nat.testBit_shiftLeft,Bool.and_eq_true_iff]
      exact ⟨decide_eq_true (by omega),by rw [show k+h-d=(k-d)+h by omega];exact ih _ hu.2⟩

private lemma partition_sum {n fuel lo t : Nat} {l : List Nat} (hm : l∈partitions n fuel lo t) : l.sum=t := by
  induction fuel generalizing l lo t with
  | zero =>
    by_cases h : t=0
    · simp_all [partitions]
    · simp [partitions,h] at hm
  | succ fuel ih =>
    by_cases h : t=0
    · simp_all [partitions]
    · rw [partitions,if_neg h] at hm
      obtain ⟨d,_,in'⟩ := List.mem_flatMap.mp hm
      split at in'
      next cond =>
        obtain ⟨ds,hs,rfl⟩ := List.mem_map.mp in'
        have ht := ih hs
        simp only [List.sum_cons]
        omega
      next => simp at in'

private lemma pruned_left {n mask fuel lo t k : Nat} {front : List Nat}
    (h : (sums front.reverse).testBit k=true) : Region n mask front fuel lo t (some k) := by
  intro ds _ _ sel
  have ht : (sums (front.reverse++ds)).testBit k=true := by simpa using extend_sum _ ds k 0 h (can_zero ds)
  simp [selected,ht] at sel

private lemma pruned_right {n mask fuel lo t k j : Nat} {front : List Nat}
    (sum : j+t=k) (h : (sums front.reverse).testBit j=true) : Region n mask front fuel lo t (some k) := by
  intro ds hm _ sel
  have ht := extend_sum _ ds j ds.sum h (can_total ds)
  rw [partition_sum hm,sum] at ht
  simp [selected,ht] at sel

private lemma push_sum (u : List Nat) (d : Nat) : sums (u++[d]) = sums u ||| (sums u <<< d) := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    simp only [List.cons_append,sums,ih,Nat.shiftLeft_or_distrib,←Nat.shiftLeft_add]
    rw [Nat.add_comm d a]
    ac_rfl

private def screened (n k : Nat) : Nat → Nat → Nat → Nat → List (List Nat)
  | 0,_,t,b => if t=0 ∧ b.testBit k=false then [[]] else []
  | fuel+1,lo,t,b =>
    if b.testBit k || (decide (t≤k) && b.testBit (k-t)) then [] else
    if t=0 then [[]] else
    (List.range (n+1)).flatMap (fun d => if lo≤d ∧ d≤t then
      (screened n k fuel d (t-d) (b ||| (b <<< d))).map (d::·) else [])

private theorem available_branch {n fuel lo t k : Nat} {front ds : List Nat}
    (part : ds∈partitions n fuel lo t) (sel : selected (some k) (front.reverse++ds)=true) :
    (sums front.reverse).testBit k=false ∧
      ¬(t≤k ∧ (sums front.reverse).testBit (k-t)=true) := by
  have miss : (sums (front.reverse++ds)).testBit k=false := by simpa [selected] using sel
  have first : (sums front.reverse).testBit k=false := by
    cases h : (sums front.reverse).testBit k with
    | false => rfl
    | true =>
      have res := extend_sum _ ds k 0 h (can_zero ds)
      simp [miss] at res
  have last : ¬(t≤k ∧ (sums front.reverse).testBit (k-t)=true) := by
    rintro ⟨le,h⟩
    have res := extend_sum _ ds (k-t) ds.sum h (can_total ds)
    rw [partition_sum part,Nat.sub_add_cancel le,miss] at res
    contradiction
  exact ⟨first,last⟩

private theorem screened_complete {n fuel lo t k : Nat} {front ds : List Nat}
    (part : ds∈partitions n fuel lo t) (sel : selected (some k) (front.reverse++ds)=true) :
    ds∈screened n k fuel lo t (sums front.reverse) := by
  induction fuel generalizing front lo t ds with
  | zero =>
    have first := (available_branch part sel).1
    by_cases h : t=0
    · simpa [screened,h,first] using (show ds=[] by simpa [partitions,h] using part)
    · simp [partitions,h] at part
  | succ fuel ih =>
    obtain ⟨first,last⟩ := available_branch part sel
    simp only [screened,first,Bool.false_or]
    have no : (decide (t≤k) && (sums front.reverse).testBit (k-t))=false := by
      simpa using last
    rw [no,if_neg (by decide : ¬false=true)]
    by_cases h : t=0
    · simpa [h] using (show ds=[] by simpa [partitions,h] using part)
    rw [if_neg h]
    rw [partitions,if_neg h] at part
    obtain ⟨d,hd,hin⟩ := List.mem_flatMap.mp part
    refine List.mem_flatMap.mpr ⟨d,hd,?_⟩
    split at hin
    next cond =>
      rw [if_pos cond]
      obtain ⟨ls,hm,rfl⟩ := List.mem_map.mp hin
      apply List.mem_map.mpr
      refine ⟨ls,?_,rfl⟩
      have hm' : selected (some k) ((d::front).reverse++ls)=true := by simpa using sel
      rw [←push_sum,←List.reverse_cons]
      exact ih hm hm'
    next => simp at hin

private theorem empty_screened {n mask k fuel lo t : Nat} {front : List Nat}
    (empty : screened n k fuel lo t (sums front.reverse) = []) :
    Region n mask front fuel lo t (some k) := by
  intro ds hm _ hs
  have h := screened_complete hm hs
  simp [empty] at h

private theorem of_screened {n : Nat} {hn : 0<n} {front : List Nat} {mask : Nat}
    {k fuel lo t : Nat} (zs : List Nat)
    (ok : certs hn mask front none (screened n k fuel lo t (sums front.reverse)) zs=true) :
    Region n mask front fuel lo t (some k) := by
  intro ds hm hp hs
  exact certs_sound mask none _ zs ok ds (screened_complete hm hs) hp rfl

private def Library (n mask : Nat) (lists : List (List Nat)) : Prop :=
  ∀ ds ∈ lists, (∀ d∈ds,0<d) → Covers n mask ds

private lemma library_append {n mask : Nat} {A B : List (List Nat)}
    (ha : Library n mask A) (hb : Library n mask B) : Library n mask (A ++ B) := by
  intro ds hm hp
  rcases List.mem_append.mp hm with h | h
  · exact ha ds h hp
  · exact hb ds h hp

private theorem check_library {n mask : Nat} (hn : 0<n) (lists : List (List Nat)) (zs : List Nat)
    (h : certs hn mask [] none lists zs=true) : Library n mask lists := by
  intro ds hm pos
  exact certs_sound mask none lists zs h ds hm pos rfl

private def alternate {n : Nat} (hn : 0<n) (mask : Nat) (A B : List (List Nat)) (ds : List Nat) (z : Nat) : Bool :=
  if z%2=0 then pack (decode hn ds (z/2)) == some mask
  else match A[(z/2)%512]?, B[z/1024]? with
    | some a,some b => (a++b).insertionSort (·≤·) == ds.insertionSort (·≤·)
    | _,_ => false

private lemma alternate_ok {n p q mask : Nat} (hn : 0<n) (dis : p &&& q=0) (fullset : p ||| q=mask)
    {A B : List (List Nat)} (ha : Library n p A) (hb : Library n q B) (ds : List Nat) (z : Nat)
    (hp : ∀ d∈ds,0<d) (ok : alternate hn mask A B ds z=true) : Covers n mask ds := by
  by_cases even : z%2=0
  · exact raw_cover hn mask ds (z/2) hp (by simpa [alternate,even] using ok)
  · cases aa : A[(z/2)%512]? with
    | none => simp [alternate,even,aa] at ok
    | some a =>
      cases bb : B[z/1024]? with
      | none => simp [alternate,even,aa,bb] at ok
      | some b =>
        have e : (a++b).insertionSort (·≤·)=ds.insertionSort (·≤·) := by simpa [alternate,even,aa,bb] using ok
        have perm : (a++b).Perm ds := by
          exact (List.perm_insertionSort (·≤·) _).symm.trans (e ▸ (List.perm_insertionSort (·≤·) ds))
        have ma := List.mem_of_getElem? aa
        have mb := List.mem_of_getElem? bb
        have u := ha a ma (fun x hx => hp x (perm.mem_iff.mp (List.mem_append_left _ hx)))
        have v := hb b mb (fun x hx => hp x (perm.mem_iff.mp (List.mem_append_right _ hx)))
        have eq : (a : Multiset Nat)+(b : Multiset Nat)=(ds : Multiset Nat) := Quot.sound perm
        rw [←eq,←fullset]
        exact union_cover dis u v

private def with_library {n : Nat} (hn : 0<n) (mask : Nat) (A B : List (List Nat)) (front : List Nat) (k : Option Nat) :
    List (List Nat) → List Nat → Bool
  | [],zs => zs.isEmpty
  | l::ls,zs =>
    let ds := front.reverse++l
    if selected k ds then
      match zs with
      | [] => false
      | z::zs' => alternate hn mask A B ds z && with_library hn mask A B front k ls zs'
    else with_library hn mask A B front k ls zs

private theorem library_sound {n : Nat} {hn : 0<n} {front : List Nat} {mask p q : Nat} {A B : List (List Nat)}
    (dis : p &&& q=0) (un : p ||| q=mask) (ha : Library n p A) (hb : Library n q B) (k : Option Nat)
    (ls : List (List Nat)) (zs : List Nat) (ok : with_library hn mask A B front k ls zs=true) :
    ∀ l∈ls, (∀ j∈front.reverse++l,0<j) → selected k (front.reverse++l)=true →
      Covers n mask ((front.reverse++l : List Nat) : Multiset Nat) := by
  induction ls generalizing zs with
  | nil => simp
  | cons l ls ih =>
    by_cases hc : selected k (front.reverse++l)=true
    · cases zs with
      | nil => simp [with_library,hc] at ok
      | cons z zs =>
        obtain ⟨this,rest⟩ := Bool.and_eq_true_iff.mp (show _ from (by simpa only [with_library,if_pos hc] using ok))
        intro d hd hpos hsel
        rcases List.mem_cons.mp hd with rfl|hm
        · exact alternate_ok hn dis un ha hb _ z hpos this
        · exact ih zs rest d hm hpos hsel
    · have ht : with_library hn mask A B front k ls zs=true := by simpa [with_library,hc] using ok
      intro d hd hp hs
      rcases List.mem_cons.mp hd with rfl|hm
      · exact False.elim (hc hs)
      · exact ih zs ht d hm hp hs

private theorem from_screened {n : Nat} {hn : 0<n} {front : List Nat} {mask p q : Nat} {A B : List (List Nat)}
    {k fuel lo t : Nat} (dis : p &&& q=0) (un : p ||| q=mask)
    (ha : Library n p A) (hb : Library n q B) (zs : List Nat)
    (ok : with_library hn mask A B front none (screened n k fuel lo t (sums front.reverse)) zs=true) :
    Region n mask front fuel lo t (some k) := by
  intro ds hm hp hs
  apply library_sound dis un ha hb none _ zs ok ds (screened_complete hm hs) hp
  rfl

private def moveCycle {n : Nat} (f : K n ≃g K n) (c : Cycle (K n)) : Cycle (K n) :=
  ⟨f c.base,c.walk.map f.toHom,c.isCycle.map f.injective⟩

private lemma moveMem {n : Nat} (f : K n ≃g K n) (c : Cycle (K n)) (a b : Fin n) :
    s(f a,f b) ∈ (moveCycle f c).edges ↔ s(a,b) ∈ c.edges := by
  change s(f a,f b) ∈ (c.walk.map f.toHom).edges ↔ _
  rw [Walk.edges_map]
  change Sym2.map f s(a,b) ∈ List.map (Sym2.map f) c.edges ↔ s(a,b) ∈ c.edges
  exact List.mem_map_of_injective (Sym2.map.injective f.injective)

private theorem moveCover {n a b : Nat} (f : K n ≃g K n)
    (bits : ∀ x y : Fin n, a.testBit (key (x,y))=b.testBit (key (f x,f y)))
    {m : Multiset Nat} (h : Covers n a m) : Covers n b m := by
  classical
  obtain ⟨C,hl,hc⟩ := h
  refine ⟨C.map (moveCycle f),?_,?_⟩
  · have len (c : Cycle (K n)) : (moveCycle f c).length=c.length := Walk.length_map _ _
    simpa [lengths,Multiset.map_map,Function.comp_def,len] using hl
  · rintro ⟨x,y⟩
    obtain ⟨v,rfl⟩ := f.surjective x
    obtain ⟨w,rfl⟩ := f.surjective y
    rw [Multiset.filter_map,Multiset.card_map,←bits]
    simpa [Function.comp_def,moveMem] using hc (v,w)

private theorem verified2 (m : Multiset Nat) (bound : ∀ d∈m,3≤d ∧ d≤2) (sm : m.sum=0) :
    Realizes 2 m := by
  have hm0 : m = 0 := by
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro k hk
    have := bound k hk
    omega
  subst hm0
  refine ⟨matchSubgraph 2 (by decide) (by decide), matchSubgraph_perfect 2 (by decide) (by decide), 0, ?_, Multiset.map_zero _⟩
  intro e he
  exfalso
  induction e using Sym2.ind with
  | _ u v =>
    have h : (K 2 \ (matchSubgraph 2 (by decide) (by decide)).spanningCoe).Adj u v := by
      simpa [SimpleGraph.mem_edgeFinset] using he
    have hne : u.val ≠ v.val := Fin.val_ne_of_ne h.1
    have hnm : ¬ (u.val + 1 = v.val ∨ v.val + 1 = u.val) := h.2
    omega

private abbrev n4_mask : Nat := 0xa22

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n4_root : Region 4 n4_mask [] 4 3 4 none :=
  of_certs (hn:=by decide) [
  0x3210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem verified4 (m : Multiset Nat) (bound : ∀ d∈m,3≤d ∧ d≤4)
    (sm : m.sum=4) : Realizes 4 m :=
  realizes_of_cover (by decide) (by decide)
    (show Covers 4 (minusMatch 4) m from
      top_region (show Region 4 (minusMatch 4) [] 4 3 4 none from n4_root) m bound sm rfl)

private abbrev n6_mask : Nat := 0x360d0c32

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n6_root : Region 6 n6_mask [] 12 3 12 none :=
  of_certs (hn:=by decide) [
  0x432531540210,
  0x513240543210,
  0x532404513210,
  0x543153204210,
  0x513420453210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem verified6 (m : Multiset Nat) (bound : ∀ d∈m,3≤d ∧ d≤6)
    (sm : m.sum=12) : Realizes 6 m :=
  realizes_of_cover (by decide) (by decide)
    (show Covers 6 (minusMatch 6) m from
      top_region (show Region 6 (minusMatch 6) [] 12 3 12 none from n6_root) m bound sm rfl)

private abbrev n8_mask : Nat := 0xee03b03a0e0e32

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n8_root : Region 8 n8_mask [] 24 3 24 none :=
  of_certs (hn:=by decide) [
  0x654752423741631760530210,
  0x752361645742431760530210,
  0x756324716542431760530210,
  0x754265237461431760530210,
  0x714325606754724631530210,
  0x745236175642314760530210,
  0x745632752461314760530210,
  0x725436175642314760530210,
  0x725461756342314760530210,
  0x657437254164231760530210,
  0x714523606572431764530210,
  0x743652675423147160530210,
  0x657437645223147160530210,
  0x713425607546327614530210,
  0x725643175423607614530210,
  0x713254607634275614530210,
  0x752346170654276314530210,
  0x754632765241743160530210,
  0x567436423571472506130210,
  0x714632505674357246130210,
  0x724635056743257146130210,
  0x742365057643527146130210,
  0x536742756432507146130210,
  0x753461765243270654130210,
  0x617423507256413067543210,
  0x725341607564231674503210,
  0x753246163472507654130210,
  0x574376524631716054203210,
  0x725314606743571654203210,
  0x472563157643170654203210,
  0x743652467531170654203210,
  0x764352756143170654203210,
  0x643172507536142076543210,
  0x657437645271350614203210,
  0x643172507635420756143210,
  0x716342506457207653143210,
  0x725436075024617653143210,
  0x617254307564207631453210,
  0x725643075420617631453210,
  0x725436146570276031453210,
  0x746352657130761420543210,
  0x527461306357142076543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem verified8 (m : Multiset Nat) (bound : ∀ d∈m,3≤d ∧ d≤8)
    (sm : m.sum=24) : Realizes 8 m :=
  realizes_of_cover (by decide) (by decide)
    (show Covers 8 (minusMatch 8) m from
      top_region (show Region 8 (minusMatch 8) [] 24 3 24 none from n8_root) m bound sm rfl)

private abbrev n10_mask : Nat := 0x3de00f700f603d03c0f0e32

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_3_3_3 : Region 10 n10_mask [3,3,3,3,3] 35 3 25 none :=
  of_certs (hn:=by decide) [
  0x9281758965864973542632741531980760430210,
  0x9645781865973952842632741531980760430210,
  0x9657829185648973542632741531980760430210,
  0x9578296581648973542632741531980760430210,
  0x6987543210763971315658814952642740930820,
  0x9687584652918973542632741531980760430210,
  0x9375642819786548952632741531980760430210,
  0x9375468187965925842632741531980760430210,
  0x9375681879645925842632741531980760430210,
  0x9786856495739281542632741531980760430210,
  0x9375648297865918542632741531980760430210,
  0x9648573978652918542632741531980760430210,
  0x8795649685732918542632741531980760430210,
  0x8579649286573918542632741531980760430210,
  0x9876543210796420851913537952826714840630,
  0x9736254818759642865932741531980760430210,
  0x5963784297546281865932741531980760430210,
  0x9684573978564259281632741531980760430210,
  0x9685739784564259281632741531980760430210,
  0x8795496573586429281632741531980760430210,
  0x9876543210314208260971815753936864952740,
  0x9375246818796549285632741531980760430210,
  0x8469375297865429185632741531980760430210,
  0x9375642818795486925632741531980760430210,
  0x9375864287965491825632741531980760430210,
  0x9648573978654291825632741531980760430210,
  0x9375682879645918425632741531980760430210,
  0x9174632580862937541987659842531760430210,
  0x9548737965862546329281741531980760430210,
  0x8795496573862546329281741531980760430210,
  0x9876543210847041306420862925963537971851,
  0x9375426818796459285632741531980760430210,
  0x6937584268795463259281741531980760430210,
  0x9648573687954263259281741531980760430210,
  0x6937584297865463259281741531980760430210,
  0x6975842937865463259281741531980760430210,
  0x9568736975425846329281741531980760430210,
  0x9876543210857314208251864740603935962971,
  0x9236574817395826419786542531980760430210,
  0x7845963792658642593281741531980760430210,
  0x8796549573628642593281741531980760430210,
  0x9876543210753142064730971815952826963840,
  0x9375624818795463296852741531980760430210,
  0x9876543210817530631420962825864973951740,
  0x9375264818796542958632741531980760430210,
  0x6937845297564281958632741531980760430210,
  0x9375268187965429584632741531980760430210,
  0x9586297468754563293718241531980760430210,
  0x9362584717865964597328241531980760430210,
  0x9574863287965462593718241531980760430210,
  0x9587462869754632593718241531980760430210,
  0x9574862879654632593718241531980760430210,
  0x8695749785624632593718241531980760430210,
  0x9876543210753142084714630962825973951860,
  0x9362548719586473279658241531980760430210,
  0x8579647865493625923718241531980760430210,
  0x9876543210631420815309371975852926864740,
  0x9236548719586473796258241531980760430210,
  0x9564873293685471796258241531980760430210,
  0x9236548719685739746258241531980760430210,
  0x9374856268719547963258241531980760430210,
  0x9574863978546296523718241531980760430210,
  0x8756495863974529628173241531980760430210,
  0x9876543210748608264031420971815753936952,
  0x9364752819785629684573241531980760430210,
  0x9364758187926549682573241531980760430210,
  0x9364758287965491862573241531980760430210,
  0x9785463965748291862573241531980760430210,
  0x8639571420987654321097481962825640703531,
  0x9375482871965974625863241531980760430210,
  0x9523647180937586241879654928531760430210,
  0x9876543210685314208264751963730804952971,
  0x9632574817395826419786542315980760430210,
  0x8426593719682574197854632315980760430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_3_3_4 : Region 10 n10_mask [4,3,3,3,3] 35 4 24 none :=
  of_certs (hn:=by decide) [
  0x9786857464539562937182514231980760430210,
  0x9748536278659645937182514231980760430210,
  0x9574862879654635937182514231980760430210,
  0x8695749785624635937182514231980760430210,
  0x8579647865492635937182514231980760430210,
  0x9876543210631420847186407530962825973951,
  0x9364752819784562968537154231980760430210,
  0x9364875297456281968537154231980760430210,
  0x8657497853954629637182514231980760430210,
  0x9876543210736403142085748251953962971860,
  0x9364752819785629684537154231980760430210,
  0x9364758187926549682537154231980760430210,
  0x9364758287965491862537154231980760430210,
  0x9785463965748291862537154231980760430210,
  0x8697531420987654321084629371740603952851,
  0x9357462818795486925637154231980760430210,
  0x9358746286975491825637154231980760430210,
  0x9684753978546291825637154231980760430210,
  0x9647582879354918625637154231980760430210,
  0x9236547180937586241879649528531760430210,
  0x7859649756829354817362514231980760430210,
  0x9876543210685314208196308462973952751740,
  0x8295364719375862418796542315980760430210,
  0x9876543210817463075314206840962825973951,
  0x9264735818793654286957142315980760430210,
  0x9357468284596371978562412315980760430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_3_3_5 : Region 10 n10_mask [5,3,3,3,3] 35 5 23 none :=
  of_certs (hn:=by decide) [
  0x9635847197865739258264154231980760430210,
  0x7485963978653719258264154231980760430210,
  0x8695749785639253718264154231980760430210,
  0x9876543210685314209648182630973952751740,
  0x9635284718573926419786542315980760430210,
  0x9876543210753142048263096471973952851860,
  0x9284635718569374197862542315980760430210,
  0x9284653718695741879362542315980760430210,
  0x9537468196571482879362542315980760430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_3_3_6 : Region 10 n10_mask [6,3,3,3,3] 35 6 22 none :=
  of_certs (hn:=by decide) [
  0x9876543210819370471530631420975852926864,
  0x8296354719375841978625642315980760430210,
  0x9635847193754182978625642315980760430210,
  0x9684537182957418793625642315980760430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_3_3_7 : Region 10 n10_mask [7,3,3,3,3] 35 7 21 none :=
  of_certs (hn:=by decide) [
  0x7485963782935197526418654231980760430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_3_3_8 : Region 10 n10_mask [8,3,3,3,3] 35 8 20 none :=
  of_certs (hn:=by decide) [
  0x8697531420987654321084629371740603852951] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_3_3_9 : Region 10 n10_mask [9,3,3,3,3] 35 9 19 none :=
  of_certs (hn:=by decide) [
  0x9263517480825739641978654231985760430210] (by rfl)

private theorem n10_3_3_3_3 : Region 10 n10_mask [3,3,3,3] 36 3 28 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n10_3_3_3_3_3
  · exact n10_3_3_3_3_4
  · exact n10_3_3_3_3_5
  · exact n10_3_3_3_3_6
  · exact n10_3_3_3_3_7
  · exact n10_3_3_3_3_8
  · exact n10_3_3_3_3_9
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_3_4 : Region 10 n10_mask [4,3,3,3] 36 4 27 none :=
  of_certs (hn:=by decide) [
  0x9847563978659286452735142319180760430210,
  0x8965748793659286452735142319180760430210,
  0x9687598563974826452735142319180760430210,
  0x9876543210314208574825173608640953962971,
  0x7392846517968549875362542319180760430210,
  0x9364758269784529865371542319180760430210,
  0x7392846518697598745362542319180760430210,
  0x9364758287965498625371542319180760430210,
  0x9785463965748298625371542319180760430210,
  0x9574682879654893625371542319180760430210,
  0x9356247180928573641978695485231760430210,
  0x9357468287954896256371542319180760430210,
  0x9647582879354986256371542319180760430210,
  0x7859649754829862536371542319180760430210,
  0x9876543210685314207463093718251975962840,
  0x5937862417469285318975463259180760430210,
  0x9876543210753142085263096828471973951640,
  0x7539628419587364279865423159180760430210,
  0x7368295419647853897562423159180760430210,
  0x8593746297863542896571423159180760430210,
  0x9657482879359862573641542319180760430210,
  0x8569749357829862573641542319180760430210,
  0x9876543210753142069740826309371864952851,
  0x7582936416984735297865423159180760430210,
  0x9876543210471530631420825709581864973962,
  0x7582936417489653978625423159180760430210,
  0x9653748275893641978625423159180760430210,
  0x9357468285697149873625423159180760430210,
  0x7369285419847539786256423159180760430210,
  0x9637458298417539786256423159180760430210,
  0x9684753958736279825416423159180760430210,
  0x8697531420987654321074826309371952851640,
  0x9362571480965824731978645329815760430210,
  0x7396258419245786319746532809815760430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_3_5 : Region 10 n10_mask [5,3,3,3] 36 5 26 none :=
  of_certs (hn:=by decide) [
  0x9756829874584625963715324193180760430210,
  0x9876543210631420952818574071530864973962,
  0x9285463716984752978653241593180760430210,
  0x9846375296285471978653241593180760430210,
  0x9284563717589649786253241593180760430210,
  0x9285647189637549786253241593180760430210,
  0x8475962978645298563713241593180760430210,
  0x9647358289175497862563241593180760430210,
  0x9647582984537197862563241593180760430210,
  0x8697531420987654321084637162930852951740,
  0x9175236480826953741978654289315760430210,
  0x9173652480826957419786453289315760430210,
  0x9573628419652471809786453289315760430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_3_6 : Region 10 n10_mask [6,3,3,3] 36 6 25 none :=
  of_certs (hn:=by decide) [
  0x9645873719865974825362415923180760430210,
  0x9253647180937586241879654982315760430210,
  0x9173526480936875427965814982315760430210,
  0x9253647819375426808569714982315760430210,
  0x9253647816809754285693714982315760430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_3_7 : Region 10 n10_mask [7,3,3,3] 36 7 24 none :=
  of_certs (hn:=by decide) [
  0x9264537180965874179368259842315760430210,
  0x8296453719086574187936259842315760430210,
  0x9368745296285371975641809842315760430210] (by rfl)

private theorem n10_3_3_3 : Region 10 n10_mask [3,3,3] 37 3 31 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n10_3_3_3_3
  · exact n10_3_3_3_4
  · exact n10_3_3_3_5
  · exact n10_3_3_3_6
  · exact n10_3_3_3_7
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_4 : Region 10 n10_mask [4,3,3] 37 4 30 none :=
  of_certs (hn:=by decide) [
  0x7958649876573693528451423191708260430210,
  0x8697598765473693528451423191708260430210,
  0x9876543210857469539251817041306420973862,
  0x8647392518796598457635423191708260430210,
  0x9374685269875397654815423191708260430210,
  0x9857463968735297654815423191708260430210,
  0x9374685278965976354815423191708260430210,
  0x9587463798653769254815423191708260430210,
  0x7859649865739763524815423191708260430210,
  0x9876543210685314203719825184704630975962,
  0x5293768418569742319875463591708260430210,
  0x6987453976857392564815423191708260430210,
  0x7689546978537392564815423191708260430210,
  0x9876543210753142082630796493716840952851,
  0x8673952419647853289754631591708260430210,
  0x9876543210471530631420695292818570864973,
  0x8637592419647853897654231591708260430210,
  0x9685374287593641897654231591708260430210,
  0x9573684298764537965814231591708260430210,
  0x8695747893692537856415423191708260430210,
  0x9876543210631420826407153085749681973952,
  0x8529736419684753987654231591708260430210,
  0x9684735285793641987654231591708260430210,
  0x8652937418579649876354231591708260430210,
  0x8639574179846538769254231591708260430210,
  0x9584763968735289756414231591708260430210,
  0x8635974189675487392564231591708260430210,
  0x6847953896754187392564231591708260430210,
  0x8697531420987654321048263093717460952851,
  0x9241856370968475231987645397158260430210,
  0x9185246370968475329876541397158260430210,
  0x9247536819648523709876541397158260430210,
  0x7896475863976529548153241931708260430210,
  0x9876543210748517536082640314206819973952,
  0x9257364817968549876532415931708260430210,
  0x9637485268197549876532415931708260430210,
  0x9573648179865487692532415931708260430210,
  0x7459863975648187692532415931708260430210,
  0x8697531420987654321062840746309371952851,
  0x7648953796854781925632415931708260430210,
  0x9184632570768539241789654973158260430210,
  0x9186325470935876428965714973158260430210,
  0x9235467819368524708965714973158260430210,
  0x9364257819867453285690714973158260430210,
  0x8759649854739763515681429231708260430210,
  0x9184253670739586417896547923158260430210,
  0x9376425819536841707896547923158260430210,
  0x9185246370968745389567147923158260430210,
  0x9185463709687425389567147923158260430210,
  0x5873964295367481986541707923158260430210,
  0x9814563709648753867192597423158260430210,
  0x9375648178963541867092597423158260430210,
  0x7481932560829517364097586241309876543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_5 : Region 10 n10_mask [5,3,3] 37 5 29 none :=
  of_certs (hn:=by decide) [
  0x9253684717896597645824159318073260430210,
  0x9536487179865476925824159318073260430210,
  0x6487953986547176925824159318073260430210,
  0x6847953698754671925824159318073260430210,
  0x9364257180928674531879659841573260430210,
  0x8795649685429825716741539318073260430210,
  0x9253647180957682418796548931573260430210,
  0x9536824719257641808796548931573260430210,
  0x9175364280967845279568148931573260430210,
  0x9746352819087654286957148931573260430210,
  0x9635784295286471976541808931573260430210,
  0x9352467180965478285791498631573260430210,
  0x9256471808769354285791498631573260430210,
  0x9356742819648752580971498631573260430210,
  0x9356784296475281580971498631573260430210,
  0x8296547176809358791425984631573260430210,
  0x9285364170847391526086975423198765430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_6 : Region 10 n10_mask [6,3,3] 37 6 28 none :=
  of_certs (hn:=by decide) [
  0x9876543210964852819370471530631420975862,
  0x9257364817908654876935982415713260430210,
  0x9357468197365480876925982415713260430210,
  0x9374658169784537680925982415713260430210,
  0x9685473975648298763519524180713260430210,
  0x9256318470857391426087964532986715430210,
  0x8192536470937584260879654132986715430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_7 : Region 10 n10_mask [7,3,3] 37 7 27 none :=
  of_certs (hn:=by decide) [
  0x8146529370917485326086975429876315430210,
  0x8146529370917584260869745329876315430210,
  0x9375642818692541709748532609876315430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_3_8 : Region 10 n10_mask [8,3,3] 37 8 26 none :=
  of_certs (hn:=by decide) [
  0x8192537460863975428569071498762315430210,
  0x9375246818297453608569071498762315430210] (by rfl)

private theorem n10_3_3 : Region 10 n10_mask [3,3] 38 3 34 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n10_3_3_3
  · exact n10_3_3_4
  · exact n10_3_3_5
  · exact n10_3_3_6
  · exact n10_3_3_7
  · exact n10_3_3_8
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_4 : Region 10 n10_mask [4,3] 38 4 33 none :=
  of_certs (hn:=by decide) [
  0x8967593478637564295328451917082604130210,
  0x8765432105748795393628251917041306420986,
  0x5873964279865743695328451917082604130210,
  0x5879642739865743695328451917082604130210,
  0x5879642893765743695328451917082604130210,
  0x9856735796428743695328451917082604130210,
  0x9876543210753142068598471925182604630973,
  0x8673924515847963298756435917082604130210,
  0x9687427593698537564328451917082604130210,
  0x9876543210631420715305847695292818640973,
  0x8639247517964853987654325917082604130210,
  0x5896374295786432976534815917082604130210,
  0x8765432104715306314208469685292819370975,
  0x9635874275986439765234815917082604130210,
  0x9586473579634298765324815917082604130210,
  0x8796598673753649543284251917082604130210,
  0x9876543210753608264031420685984719251973,
  0x8765432106314209264071530584789529681973,
  0x9586473269875439765324815917082604130210,
  0x9586473269875397654324815917082604130210,
  0x6479853968754376592324815917082604130210,
  0x7968531420987654321082630957384719251640,
  0x7859643798654763925324815917082604130210,
  0x9364258170923486751789654973582604130210,
  0x9185246370968475329876543971582604130210,
  0x9247536819648523709876543971582604130210,
  0x9253684707581964398765423971582604130210,
  0x9247635818975486937564329517082604130210,
  0x5897463296875376543924819517082604130210,
  0x6479853968754376523924819517082604130210,
  0x6985743978653764523924819517082604130210,
  0x9236458170937684251789659743582604130210,
  0x7589647865439763529324819517082604130210,
  0x9186342570964785328976549371582604130210,
  0x9246357819685234708976549371582604130210,
  0x9876543210815263075314206974059289371864,
  0x9736425819684753298765439071582604130210,
  0x5869374298754632976534819071582604130210,
  0x9186342570964785389765492371582604130210,
  0x9637425819578643289765439071582604130210,
  0x9574236817964853987654329071582604130210,
  0x4796853295736481987654329071582604130210,
  0x9364758178695438976524329071582604130210,
  0x9362518470829653714097685423198756430210,
  0x8793645289675684359247195180732604130210,
  0x6978543986753648259247195180732604130210,
  0x8967549785638643529247195180732604130210,
  0x9174365280935876428975496815732604130210,
  0x9256347819357642808695489715732604130210,
  0x9175243680964785389765492815732604130210,
  0x9746352819086754385692498715732604130210,
  0x9253674819758643569082498715732604130210,
  0x9345768297463581809652498715732604130210,
  0x9876543210819370471530631420697525928864,
  0x9246357819768543690825984715732604130210,
  0x9368754297643581690825984715732604130210,
  0x9754368291876538096425984715732604130210,
  0x9578643976548298524719635180732604130210,
  0x9251846370853917426086975432987654130210,
  0x8192536470937584260869715432987654130210,
  0x9246357818679546908258937157432604130210,
  0x9763548168759246908258937157432604130210,
  0x9786352957648196542808937157432604130210,
  0x8697531420987654321071526309374819582640,
  0x8192536470937584260879654329867154130210,
  0x8452963709358742609756432819867154130210,
  0x9185234670847539260879654298637154130210,
  0x9876543210471526306853142064807392819975,
  0x9264735819367524808796543298607154130210,
  0x9253674817580964397865423982607154130210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_5 : Region 10 n10_mask [5,3] 38 5 32 none :=
  of_certs (hn:=by decide) [
  0x9753682698458762593471951807324064130210,
  0x6897539654828762593471951807324064130210,
  0x9175263480968745389765928157324064130210,
  0x9354762816579084386925987157324064130210,
  0x9175263480798654876935928157324064130210,
  0x9263574819768543690825987157324064130210,
  0x9354768297563481809625987157324064130210,
  0x9675348279186548093625987157324064130210,
  0x9263457819768536908259847157324064130210,
  0x9754368291876538096259847157324064130210,
  0x9786543926758196352809847157324064130210,
  0x9263518470856917324098675439782564130210,
  0x9184253670856293740869754329871564130210,
  0x9263584708693752409765432819871564130210,
  0x8596347189765487392625190875324064130210,
  0x6795843896547187392625190875324064130210,
  0x8697531420987654321092648171593063740852,
  0x9184352670823695740978654289371564130210,
  0x9182536740693758429786543298071564130210,
  0x9362574819673582409786543298071564130210,
  0x9185263740486975329876543928071564130210,
  0x9347625819637542809786532984071564130210,
  0x9362475818096735297865432984071564130210,
  0x8547936295673481869251709875324064130210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_6 : Region 10 n10_mask [6,3] 38 6 31 none :=
  of_certs (hn:=by decide) [
  0x8295671893746978536451908752340624130210,
  0x8192536470957682340879654893715624130210,
  0x9182573640967485329786543980715624130210,
  0x9632574819285376409786543980715624130210,
  0x9285367407569184397864523980715624130210,
  0x9186325740796485398765439280715624130210,
  0x9253746816908754397658239840715624130210,
  0x9346875296374581976532809840715624130210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_7 : Region 10 n10_mask [7,3] 38 7 30 none :=
  of_certs (hn:=by decide) [
  0x9263574816780954869371598234076524130210,
  0x9536478192675480869371598234076524130210,
  0x7482915360958173264086975241309876543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_8 : Region 10 n10_mask [8,3] 38 8 29 none :=
  of_certs (hn:=by decide) [
  0x8436925170953741826097586423198765403210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_3_9 : Region 10 n10_mask [9,3] 38 9 28 none :=
  of_certs (hn:=by decide) [
  0x9182463570843795260968547132987651403210] (by rfl)

private theorem n10_3 : Region 10 n10_mask [3] 39 3 37 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n10_3_3
  · exact n10_3_4
  · exact n10_3_5
  · exact n10_3_6
  · exact n10_3_7
  · exact n10_3_8
  · exact n10_3_9
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_4_4 : Region 10 n10_mask [4,4] 38 4 32 none :=
  of_certs (hn:=by decide) [
  0x9765987396826352857454319180714064203210,
  0x9358476298759637865254319180714064203210,
  0x9567482869758937635254319180714064203210,
  0x8695749765828937635254319180714064203210,
  0x8695748976582937635254319180714064203210,
  0x9876543210631420968597538462925181704730,
  0x5692847319768543987536259180714064203210,
  0x8547396297684352987563159180714064203210,
  0x7896597682952638537454319180714064203210,
  0x9876543210826403142096859753847191527360,
  0x5679284319685739874536259180714064203210,
  0x9748536286937529876543159180714064203210,
  0x9365748279685398762543159180714064203210,
  0x9684753973658298762543159180714064203210,
  0x7968531420987654321095738471915282604630,
  0x5674829318697598735436259180714064203210,
  0x9736548296785398625743159180714064203210,
  0x9654873976358298625743159180714064203210,
  0x9765482968735893625743159180714064203210,
  0x9152637480829675431978658935714064203210,
  0x9578639735828962545674319180714064203210,
  0x9134576280963748529786539815714064203210,
  0x9267584319637452809786539815714064203210,
  0x9136257480967358297865439815714064203210,
  0x9345762809748635278569139815714064203210,
  0x9374856296875431976352809815714064203210,
  0x8963745297685784356291593180714064203210,
  0x6789543796853748256291593180714064203210,
  0x8967547958638743526291593180714064203210,
  0x9137456280976348529875396815714064203210,
  0x9263754819674352809786589315714064203210,
  0x9136257480796854398765392815714064203210,
  0x9263574817809654397682589315714064203210,
  0x9265374816879543769082589315714064203210,
  0x9745368296573481908762589315714064203210,
  0x9876543210819370471530631420968597528264,
  0x9263745819087653796825984315714064203210,
  0x9365478192673580796825984315714064203210,
  0x9374568269187538097625984315714064203210,
  0x9684753973658298762519543180714064203210,
  0x9362518470829653714097685431987564203210,
  0x9263517480937682541856970431987564203210,
  0x9753682698458762593471951807314064203210,
  0x6897539654828762593471951807314064203210,
  0x9175263480968745389765928157314064203210,
  0x9354762816579084386925987157314064203210,
  0x9175263480798654876935928157314064203210,
  0x9263574819768543690825987157314064203210,
  0x9354768297563481809625987157314064203210,
  0x9675348279186548093625987157314064203210,
  0x9263457819768536908259847157314064203210,
  0x9754368291876538096259847157314064203210,
  0x9786543926758196352809847157314064203210,
  0x9136257480735692814097685439871564203210,
  0x9184362570829653740976854139871564203210,
  0x9367452819265843708697531409871564203210,
  0x8596347189765487392625190875314064203210,
  0x6795843896547187392625190875314064203210,
  0x8192563470935826714086975498731564203210,
  0x9362547180928675341856970498731564203210,
  0x9263574180867934528569170498731564203210,
  0x8629357419763452808569170498731564203210,
  0x7182963540937568418097625987431564203210,
  0x9284563717539681408097625987431564203210,
  0x7193568408296754180973625987431564203210,
  0x8547936295673481869251709875314064203210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_4_5 : Region 10 n10_mask [5,4] 38 5 31 none :=
  of_certs (hn:=by decide) [
  0x7985648675482937963519526081340714203210,
  0x9153748260697854986756392581340714203210,
  0x9378254606974853986756291581340714203210,
  0x8547396297846352986756091581340714203210,
  0x9375284607968549876356291581340714203210,
  0x9364758279684539876256091581340714203210,
  0x9684573859746298763526091581340714203210,
  0x9374658286975498763526091581340714203210,
  0x9685473975648298763526091581340714203210,
  0x8251937460926758134087965498635714203210,
  0x8475291360973582640987654396815714203210,
  0x9135476280973648529875604396815714203210,
  0x8293754609876253406584791396815714203210,
  0x9586473698753791826452908651340714203210,
  0x9182537460857629340879654986315714203210,
  0x9182543760935784627965804986315714203210,
  0x9265347819376452808579604986315714203210,
  0x9647352819087654385792604986315714203210,
  0x6291853740978456376908259864315714203210,
  0x8293657407691845387906259864315714203210,
  0x9635748293785260976540819864315714203210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_4_6 : Region 10 n10_mask [6,4] 38 6 30 none :=
  of_certs (hn:=by decide) [
  0x9586739874629754819652807153406314203210,
  0x9182675340937468528796549807156314203210,
  0x9374625819286753408796549807156314203210,
  0x9182673540974685287569349807156314203210,
  0x9267345818647935287569049807156314203210,
  0x9375846296745281978653409807156314203210,
  0x9264735819786543769082598407156314203210,
  0x9653478293754681809762598407156314203210,
  0x8152937460719582634096875314208976543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_4_7 : Region 10 n10_mask [7,4] 38 7 29 none :=
  of_certs (hn:=by decide) [
  0x9574628196784528093715986340765314203210,
  0x9286415370817459362096785243189756043210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_4_8 : Region 10 n10_mask [8,4] 38 8 28 none :=
  of_certs (hn:=by decide) [
  0x9281536470859371426096875431897652043210,
  0x8296351470937185460957862431897652043210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_4_9 : Region 10 n10_mask [9,4] 38 9 27 none :=
  of_certs (hn:=by decide) [
  0x9736452817485392608695713409876514203210] (by rfl)

private theorem n10_4 : Region 10 n10_mask [4] 39 4 36 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n10_4_4
  · exact n10_4_5
  · exact n10_4_6
  · exact n10_4_7
  · exact n10_4_8
  · exact n10_4_9
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_5 : Region 10 n10_mask [5] 39 5 35 none :=
  of_certs (hn:=by decide) [
  0x6785498653974829637195180752603142043210,
  0x9876543210869747395191852753608264031420,
  0x8293564718679549873651908752603142043210,
  0x8295647186793549873651908752603142043210,
  0x8296547189376487953651908752603142043210,
  0x9376482896547187953651908752603142043210,
  0x8293645170918473526086975987653142043210,
  0x8295671893746978536451908752603142043210,
  0x8192536470937548260869715987653142043210,
  0x8192537460845793628690715987653142043210,
  0x9736452818475392608690715987653142043210,
  0x9362574817908645382960715987653142043210,
  0x7598649637829765819354807152603142043210,
  0x8192635470937584606978259867153142043210,
  0x9284563709357460818796259867153142043210,
  0x8192635470937856079648259867153142043210,
  0x8293645707481965387906259867153142043210,
  0x9365478296485370975260819867153142043210,
  0x9263745819784653769082598607153142043210,
  0x9356478296375481809762598607153142043210,
  0x7392815460917485263086975314209876543210,
  0x9182645730974865387692598071563142043210,
  0x9284657309186745387962598071563142043210,
  0x9284657309687453819762598071563142043210,
  0x9375648296874530819762598071563142043210,
  0x9653748268197549087625893071563142043210,
  0x7391482560926475813087963542098671543210,
  0x9586473967548189251709782630653142043210,
  0x7392581460917482653086975420987631543210,
  0x7391825460847926530968571420987631543210,
  0x9173562480825793641968547029876031543210,
  0x9745362818465293709685714209876031543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_6 : Region 10 n10_mask [6] 39 6 34 none :=
  of_certs (hn:=by decide) [
  0x4578192630976853690825984715731420643210,
  0x4579286309187653809625984715731420643210,
  0x9368754097653082819625984715731420643210,
  0x8296754097865308193625984715731420643210,
  0x9584763975628186925409871530731420643210,
  0x7639258140917482653086975420987315643210,
  0x7639182540847926530968571420987315643210,
  0x8562937140918476352086975429870315643210,
  0x9176352480856293741869754029870315643210,
  0x9256374818267935409685714209870315643210,
  0x9147352680936758425698170497820315643210,
  0x9268537419367524805698170497820315643210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_7 : Region 10 n10_mask [7] 39 7 33 none :=
  of_certs (hn:=by decide) [
  0x9152863740784629531967580398142076543210,
  0x9263517480968257319587640398142076543210,
  0x9268475319637152809587640398142076543210,
  0x9285367406481975296803715893142076543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_8 : Region 10 n10_mask [8] 39 8 32 none :=
  of_certs (hn:=by decide) [
  0x8469375168291740879526309853142076543210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n10_10 : Region 10 n10_mask [10] 39 10 30 none :=
  of_certs (hn:=by decide) [
  0x7392518460471958263086975314209876543210] (by rfl)

private theorem n10_root : Region 10 n10_mask [] 40 3 40 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n10_3
  · exact n10_4
  · exact n10_5
  · exact n10_6
  · exact n10_7
  · exact n10_8
  · exact absent_region (by rfl)
  · exact n10_10

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem verified10 (m : Multiset Nat) (bound : ∀ d∈m,3≤d ∧ d≤10)
    (sm : m.sum=40) : Realizes 10 m :=
  realizes_of_cover (by decide) (by decide)
    (show Covers 10 (minusMatch 10) m from
      top_region (show Region 10 (minusMatch 10) [] 40 3 40 none from n10_root) m bound sm rfl)

private abbrev n12a_mask : Nat := 0x4a800149002660093003801e016020c00
private abbrev n12b_mask : Nat := 0xb16002a600188006800c20200280d0232
private abbrev n12_mask : Nat := 0xfbe003ef003ee00fb00fa03e03e0f0e32
private abbrev n12_28_mask : Nat := 0x4a800149002660090003801e016020a00
private abbrev n12_32_mask : Nat := 0xb16002a600188006b00c20200280d0432

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_3_3_3 : Region 12 n12a_mask [3,3,3] 27 3 21 none :=
  of_certs (hn:=by decide) [
  0xb94847981416b6272363a315a80950,
  0xb6a37294b874632981641531a80950,
  0x73a62b632b94874981641531a80950,
  0x89b273a61847b64632941531a80950,
  0x9874b4629b61a63732841531a80950,
  0xa6b94873b274632981641531a80950,
  0xa6b48739b274632981641531a80950,
  0xa6b473b94872632981641531a80950,
  0xa8749b261350b64841915a63732980,
  0x7849b63b2746a32981641531a80950,
  0x784b639b2746a32981641531a80950,
  0x9874b26a3519b64732841631a80950,
  0xa6473b987294b61632841531a80950,
  0x89b4723a6178463b26941531a80950,
  0xb94873a6274b632981641531a80950,
  0xb9473a62784b632981641531a80950,
  0x789b634b276a329481641531a80950,
  0xb987473a62b6329481641531a80950,
  0x9874b23a619b643726841531a80950,
  0xb49873a6274632b916841531a80950,
  0xb9873a6274b6329481641531a80950,
  0xb987362b6a32749481641531a80950,
  0xb9873a6274632b4916841531a80950,
  0xb987362746a32b4916841531a80950,
  0x789b63b46a32947261841531a80950,
  0xa3519b264780b6a894732841631950,
  0x9872b46a3516b94732814631a80950,
  0x9b26a374817894b632614531a80950,
  0xb49873a629b6327481614531a80950,
  0x73a62b984b63294618741531a80950,
  0x984b273619b64a3268741531a80950,
  0x94b2736189b64a3268741531a80950,
  0xb946372b61984a3268741531a80950,
  0xb98463273a62b49168741531a80950,
  0xb94632984b61a37268741531a80950,
  0xa6b472351980b9462a873841631950,
  0x9b48726a351b647329814631a80950,
  0x9b26a374817894632b614531a80950,
  0xb98473a6278194632b614531a80950,
  0x789463a6b239b48162741531a80950,
  0x94872b6a35164732b9814631a80950,
  0x9b6a327481789463b2614531a80950,
  0x94b6a37816489b2372614531a80950,
  0xa6b498739b23648172614531a80950,
  0x94b6a378189b264723614531a80950,
  0xa6b49873819b264723614531a80950,
  0x7894b639b26481614723a531a80950,
  0xa35194b62780b98a64732814631950,
  0x94b6278a351b980a64732814631950] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_3_3_4 : Region 12 n12a_mask [4,3,3] 27 4 20 none :=
  of_certs (hn:=by decide) [
  0x9b6498417813b472623a3615a80950,
  0x84b2735198746a329b614631a80950,
  0x946a35172b63b98487416231a80950,
  0xb6a372946351b98487416231a80950,
  0xa6b947235180a873b4629841631950,
  0x9b6351a6473b487289416231a80950,
  0x9b27846a35174b6398146231a80950,
  0x9b2746a351784b6398146231a80950,
  0xb9846a3726b4915378146231a80950,
  0xb946a372984b635178146231a80950,
  0x74b63b9462872313a6159841a80950,
  0x9472b6a35178463b98146231a80950,
  0x94b6a378189b274635146231a80950,
  0xa6b49873819b274635146231a80950,
  0x946a378189b274b635146231a80950,
  0xa6498739b27481b635146231a80950,
  0xa64b273519806b948a327814631950,
  0x94872b6a35189b4732614631a80950,
  0x9b6a32748137894b26154631a80950] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_3_3_5 : Region 12 n12a_mask [5,3,3] 27 5 19 none :=
  of_certs (hn:=by decide) [
  0x984b6a3519b2748736146231a80950,
  0x94b6378189b2746a35146231a80950,
  0x7894b639b274816a35146231a80950,
  0x8473a61b278949b635146231a80950,
  0xa351946b27806a84732b9814631950,
  0x94872b6a35189b4736146231a80950,
  0x849b273a619874b635146231a80950] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_3_3_6 : Region 12 n12a_mask [6,3,3] 27 6 18 none :=
  of_certs (hn:=by decide) [
  0x873a61b63194b98472326415a80950,
  0xa62b49153780748a326b9814631950,
  0x53a6b2789419b47361846231a80950,
  0x9874b6a3516372b941846231a80950,
  0x9874b6351b9416a372846231a80950] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_3_3_7 : Region 12 n12a_mask [7,3,3] 27 7 17 none :=
  of_certs (hn:=by decide) [
  0x984b273a61536b9418746231a80950,
  0x94b273a61536b98418746231a80950] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_3_3_8 : Region 12 n12a_mask [8,3,3] 27 8 16 none :=
  of_certs (hn:=by decide) [
  0x94b63781b98461323a627415a80950] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_3_3_12 : Region 12 n12a_mask [12,3,3] 27 12 12 none :=
  of_certs (hn:=by decide) [
  0xa64b273591809b623a874150984631] (by rfl)

private theorem n12a_3_3 : Region 12 n12a_mask [3,3] 28 3 24 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n12a_3_3_3
  · exact n12a_3_3_4
  · exact n12a_3_3_5
  · exact n12a_3_3_6
  · exact n12a_3_3_7
  · exact n12a_3_3_8
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact n12a_3_3_12

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_3_4 : Region 12 n12a_mask [4,3] 28 4 23 none :=
  of_certs (hn:=by decide) [
  0xa635180b946a873b47298416231950,
  0xa63780a81539b64b47298416231950,
  0xa3519462780b984b6328a614731950,
  0xb63728a351a648098749b416231950,
  0xa6b9153780a8463b47289416231950,
  0xa372b49806b91538a6487416231950,
  0xa372b9806b491538a6487416231950,
  0xa3519b48098a64b637287416231950,
  0xb498a3726b9153a648087416231950,
  0xb98a37294b6351a648087416231950,
  0x9b273518a6b49a3648087416231950,
  0xa6b273519480a89b46378146231950,
  0x948a6b27351a089b46378146231950,
  0xa372b649806a84b915378146231950,
  0x94b63a819b27853741a64806231950,
  0xa894b6372b91853741a64806231950,
  0xa894739b6351b41872a64806231950,
  0xa6b273519480a87463b98146231950,
  0x948a6b27351a087463b98146231950,
  0xa649153780a8472b63b98146231950,
  0x9478a6351a372b6480b98146231950,
  0xa36b2749180b98a648735146231950,
  0xa6b2749180b98a3648735146231950,
  0x9472b6a81b980a3648735146231950,
  0xa374b91809872b648a635146231950,
  0x946b2781a374b9808a635146231950,
  0xa372b61849509b478a623514631980] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_3_5 : Region 12 n12a_mask [5,3] 28 5 22 none :=
  of_certs (hn:=by decide) [
  0x7849b62b473298a6153641a3180950,
  0xb9487274b62398a6153641a3180950,
  0xa6b273519480b9874a361846231950,
  0x9b6a8472351789463b2614a3180950,
  0x9b23748a617894b6263514a3180950,
  0x94b278a616b98473263514a3180950,
  0x9b23748a61789462b63514a3180950,
  0x94b278a6189b6374623514a3180950,
  0xb6a894729b487361623514a3180950,
  0xb946a8728916374b623514a3180950,
  0xa62b491537806b98a3274184631950,
  0x53a89b62741a6194b2378084631950] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_3_6 : Region 12 n12a_mask [6,3] 28 6 21 none :=
  of_certs (hn:=by decide) [
  0x98a374b619b2784623514a63180950,
  0x94872b61b98a374623514a63180950,
  0xb948a329874b613726415a63180950,
  0xa635194b27806b98a3741846231950,
  0xa6b4915378063a89b2741846231950] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_3_7 : Region 12 n12a_mask [7,3] 28 7 20 none :=
  of_certs (hn:=by decide) [
  0xa615372b49809b63a8418746231950,
  0x6a894b273519b63a08418746231950,
  0x98a6372b41a3516b94808746231950] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_3_8 : Region 12 n12a_mask [8,3] 28 8 19 none :=
  of_certs (hn:=by decide) [
  0xa615372b4808a36b94198746231950,
  0x6a84b2735180a36b94198746231950] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_3_9 : Region 12 n12a_mask [9,3] 28 9 18 none :=
  of_certs (hn:=by decide) [
  0x6b498a351b91487362a64723180950] (by rfl)

private theorem n12a_3 : Region 12 n12a_mask [3] 29 3 27 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n12a_3_3
  · exact n12a_3_4
  · exact n12a_3_5
  · exact n12a_3_6
  · exact n12a_3_7
  · exact n12a_3_8
  · exact n12a_3_9
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_4 : Region 12 n12a_mask [4] 29 4 26 none :=
  of_certs (hn:=by decide) [
  0xb9487273646a326b419531a8908150,
  0x78463b94726a326b419531a8908150,
  0xb6a35948727463b9146231a8908150,
  0xb6a35947278463b9146231a8908150,
  0xb6359472a64873b9146231a8908150,
  0xa6b49539b2784173646231a8908150,
  0x9b6a3741b2784953646231a8908150,
  0xa6b487372b914953646231a8908150,
  0xa6b473b948729536416231a8908150,
  0xa872b4613590749b63a62398418150,
  0x6a359b2784194b62317463a8908150,
  0x784b953a62b61947326413a8908150,
  0xb6a3594729b48732616413a8908150,
  0xa6b48739b2749536146231a8908150,
  0xa6b473b948729536146231a8908150,
  0xa8416b273590b9874913646a328150,
  0x6a359b278416b473264913a8908150,
  0xb6a359487274b916326413a8908150,
  0x9b4873a616b27495326413a8908150,
  0x784b953a627491632b6413a8908150,
  0x9b4873a6162749532b6413a8908150,
  0x74953a629b4873612b6413a8908150,
  0xb4873a62749163259b6413a8908150,
  0xa6b2735184909b478a326146318950,
  0x8a6b9472351a3784b2619046318950,
  0xb6a89487364b953262741a31908150,
  0x6a359872b41647326b913a84908150,
  0x748a6b9532789463b2614a31908150,
  0x78a6b49536489b2372614a31908150,
  0x7846b953b498a63272614a31908150,
  0xb63594872b98a64732614a31908150,
  0x6a84b9539872b64732614a31908150,
  0x6a84953789b4626b23741a31908150,
  0xa359b4162780b6a894732648139150,
  0xa3784162b9074b6a89532649138150,
  0xa846b953b27894732614a631908150,
  0xa84b953b649872732614a631908150,
  0xa872b4163590a6b984732649138150,
  0xa3784b26190746a895326b94138150,
  0xb46a359872a8473261906b94138150,
  0xa872b4163590a6b947326489138150,
  0xa3784b261907498a63259b64138150,
  0x98a374b26178490a63259b64138150,
  0xa3784b61906a89472359b264138150,
  0x7894b6a32a8473619059b264138150] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_5 : Region 12 n12a_mask [5] 29 5 25 none :=
  of_certs (hn:=by decide) [
  0xb6a8478953746329b26194180a3150,
  0x6a874b9532b63724891694180a3150,
  0xb98a64732784b623591694180a3150,
  0x74b98a62b6487323591694180a3150,
  0x74b98a63872b6423591694180a3150,
  0x789b463b6a847223591694180a3150,
  0xa8162b473590789b6a326491384150,
  0x95378a62b4174809b63298164a3150,
  0x9b236a8741953726b48098164a3150,
  0xb6a87326489532749169b4180a3150,
  0xa8162b473590789b632a6491384150,
  0x95374b26a817809463289b614a3150,
  0x953726b481b9087463298a614a3150,
  0x953274b6a81780946389b2614a3150,
  0x95374b6a8164809b239872614a3150,
  0x9b4736a819532b64809872614a3150,
  0x9472b6a81b908736489532614a3150] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_6 : Region 12 n12a_mask [6] 29 6 24 none :=
  of_certs (hn:=by decide) [
  0xa89473b648729532619b4180a63150,
  0xa6b41872359094736189b2648a3150,
  0x953a8472b616498732b90814a63150,
  0x948a372b6164789532b90814a63150,
  0x94b273a8195326478089b614a63150,
  0x98a374b26178495326b90814a63150,
  0x9b6473a8159084b239872614a63150,
  0x6b498a32953784619b274180a63150,
  0xa816b4723590873a62b94150984631] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_7 : Region 12 n12a_mask [7] 29 7 23 none :=
  of_certs (hn:=by decide) [
  0x94b273a817809b648953614a623150,
  0x9b473a81946b27808953614a623150,
  0xa6b2735941809b478a361509846231] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_8 : Region 12 n12a_mask [8] 29 8 22 none :=
  of_certs (hn:=by decide) [
  0xa6184b2735908a36b9415098746231,
  0x872b4953a61a89b637415090846231] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_9 : Region 12 n12a_mask [9] 29 9 21 none :=
  of_certs (hn:=by decide) [
  0xa816372b495053a6b9841908746231,
  0x6a372b489518a0536b941908746231] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12a_10 : Region 12 n12a_mask [10] 29 10 20 none :=
  of_certs (hn:=by decide) [
  0x948a372b61a6359b41809874623150] (by rfl)

private theorem n12a_root : Region 12 n12a_mask [] 30 3 30 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n12a_3
  · exact n12a_4
  · exact n12a_5
  · exact n12a_6
  · exact n12a_7
  · exact n12a_8
  · exact n12a_9
  · exact n12a_10
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_3_3_3 : Region 12 n12b_mask [3,3,3] 27 3 21 none :=
  of_certs (hn:=by decide) [
  0x976a75658a92524b83b70430ba1201,
  0xa79685765b83a92542ba1b70430210,
  0x86975a765b83a92542ba1b70430210,
  0xb1a586970ba7657b83a92542430210,
  0xa9656857a792b83542ba1b70430210,
  0x9a7685427965b83a52ba1b70430210,
  0xa758692a9765b83542ba1b70430210,
  0xa97685a75692b83542ba1b70430210,
  0x7ba129685430a97765a52420b83b01,
  0xa768542a9756925b83ba1b70430210,
  0xa976857a2456925b83ba1b70430210,
  0xb3865429a708b75967a52ba1430210,
  0xa7685a975256924b83ba1b70430210,
  0xb3856792a19ab8675a542b70430210,
  0xb386975a18ba76592a542b70430210,
  0xba5796838b1a76592a542b70430210,
  0xb38670b857a965a792542ba1430210,
  0xb7683b8570a965a792542ba1430210,
  0xb3865792a19a76b85a542b70430210,
  0xb385769a1ab865792a542b70430210,
  0xb85769a1ab3865792a542b70430210,
  0x8ba9675b3865a1792a542b70430210,
  0xab3867929a75658b1a542b70430210,
  0xba9768392a75658b1a542b70430210,
  0x8ba976a75692b385a1542b70430210,
  0x7b1a296583408ba976a57542b30210,
  0xb38692457a18ba9765a25b70430210,
  0x9683ba75428b1a9765a25b70430210,
  0x9ab867542b385697a1a25b70430210,
  0xb79a168579652a542ba70b83430210,
  0xb386542a19a76b85a9752b70430210,
  0xb38679a1ab8579652a542b70430210,
  0xb8679a1ab38579652a542b70430210,
  0xb3869a1ba75897652a542b70430210,
  0xba9683b857a197652a542b70430210,
  0x7b1a296583408ba769a57542b30210,
  0xb38697542a18ba765a925b70430210,
  0xab386975428b1a765a925b70430210,
  0xb385697a1768ba245a925b70430210,
  0xba76839a25796542b85a1b70430210,
  0xb38679245a18ba7569a25b70430210,
  0xb3867542a18ba965a7925b70430210,
  0xb385769a168ba245a7925b70430210,
  0xba967583b86542a1a7925b70430210,
  0xb386579a18ba245a76925b70430210,
  0xba9756838b1a245a76925b70430210,
  0xba97583967a542b8652a1b70430210,
  0x79652a1b83409ab768542a75b30210,
  0xb79683452a19ab8567042a75b30210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_3_3_4 : Region 12 n12b_mask [4,3,3] 27 4 20 none :=
  of_certs (hn:=by decide) [
  0x8b76a97585439652ba217a10b30420,
  0xb38679a1b8579652a542ba70430210,
  0xb8679a1b38579652a542ba70430210,
  0xb76583b869a19752a542ba70430210,
  0x758692a1b340ba97a567b830542210,
  0xb869a157b3897652a542ba70430210,
  0xb38697542a18b765a925ba70430210,
  0xb3867542a1a97b856925ba70430210,
  0xa97b38542a1b86756925ba70430210,
  0xa97b8542b38675a16925ba70430210,
  0xa975256924b7683b85a1ba70430210,
  0xa97b386542a1b8576925ba70430210,
  0xa97b38542a1b86576925ba70430210,
  0xb79a56838b1a24576925ba70430210,
  0xb38675a169a2458b7925ba70430210,
  0xa967542b3865a18b7925ba70430210,
  0x79652a1b83409a768542ab75b30210,
  0xb38542967a1a970b8652ab75430210,
  0xb3865297a1b8542a9670ab75430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_3_3_5 : Region 12 n12b_mask [5,3,3] 27 5 19 none :=
  of_certs (hn:=by decide) [
  0x9683ba542a765297b1ab8570430210,
  0x9683ba52a7654297b1ab8570430210,
  0x967a542ba2568397b1ab8570430210,
  0xab3865297a542967b1ab8570430210,
  0x7b1a529683408ba97657a245b30210,
  0xb3869245a708b1a97657ba25430210,
  0xb869245a7083b1a97657ba25430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_3_3_6 : Region 12 n12b_mask [6,3,3] 27 6 18 none :=
  of_certs (hn:=by decide) [
  0x9a7b86976542b385a1ba2570430210,
  0x79652a1b8340ab76857a9245b30210,
  0xb3869a245708b1a765ab7925430210,
  0xb869a2457083b1a765ab7925430210,
  0xb385769a1b86542a70ab7925430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_3_3_7 : Region 12 n12b_mask [7,3,3] 27 7 17 none :=
  of_certs (hn:=by decide) [
  0xb38542a9707a1b865ab76925430210,
  0xb386579a18b07a245ab76925430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_3_3_8 : Region 12 n12b_mask [8,3,3] 27 8 16 none :=
  of_certs (hn:=by decide) [
  0xb769a58397ab8652b1a24570430210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_3_3_12 : Region 12 n12b_mask [12,3,3] 27 12 12 none :=
  of_certs (hn:=by decide) [
  0x43b1a758692038ba97654210a52b70] (by rfl)

private theorem n12b_3_3 : Region 12 n12b_mask [3,3] 28 3 24 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n12b_3_3_3
  · exact n12b_3_3_4
  · exact n12b_3_3_5
  · exact n12b_3_3_6
  · exact n12b_3_3_7
  · exact n12b_3_3_8
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact n12b_3_3_12

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_3_4 : Region 12 n12b_mask [4,3] 28 4 23 none :=
  of_certs (hn:=by decide) [
  0x79ab34068579652a542b7a1b830210,
  0xa97685b342a9652b7a17540b830210,
  0x768529ab3407965a245b7a1b830210,
  0xa968597652ba243b7a17540b830210,
  0x97685ab342a96527b1a7540b830210,
  0x9685ab342a976527b1a7540b830210,
  0x965ab342a9768527b1a7540b830210,
  0x9685ab342a765297b1a7540b830210,
  0x965ab342a7685297b1a7540b830210,
  0x9a76852b7965a1b342a7540b830210,
  0xab7968567a925243b1a7540b830210,
  0x796852a1b3409ab7542a765b830210,
  0xb34297685a1569ab7047a25b830210,
  0xb7685429a13ba5697047a25b830210,
  0xba768543a296597b1a75240b830210,
  0xba76543a2968597b1a75240b830210,
  0x869a75ab7652b345a179240b830210,
  0x768529a1b340ab79657a245b830210,
  0x75869a1b340567ba24a7925b830210,
  0x75869ab340567b1a24a7925b830210,
  0xb768542a17569ab340a7925b830210,
  0xb34586792a17ba965a70425b830210,
  0xb3458679a17ba2965a70425b830210,
  0xb758692a1679ab345a70425b830210,
  0xb758692a167ab345a970425b830210,
  0xba768543b75692a1a970425b830210,
  0x79683b1a2540b8567a92430ab75210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_3_5 : Region 12 n12b_mask [5,3] 28 5 22 none :=
  of_certs (hn:=by decide) [
  0xb7a968379256b85a1ba24075430210,
  0xb796839a7652b85a1ba24075430210,
  0xb1a2579683408b765a92457ab30210,
  0xb385a769240ab865297b1a75430210,
  0xb85a769240ab3865297b1a75430210,
  0x967ab3852a568b04297b1a75430210,
  0xb38697a2409ab852567b1a75430210,
  0x9683b7a528ba9765240b1a75430210,
  0xb769a58397ab8652240b1a75430210,
  0xab3867929a7b8565240b1a75430210,
  0x76583b1a9240b8697a54307ba25210,
  0xb8567a92430b38697045a17ba25210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_3_6 : Region 12 n12b_mask [6,3] 28 6 21 none :=
  of_certs (hn:=by decide) [
  0xa7b3856928ba976540b1a752430210,
  0xab3867929a7b856540b1a752430210,
  0xb79a583b8692a1ba76540752430210,
  0x796583b1a240b867a54307ba925210,
  0x769a1b38540b8657a2430ab7925210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_3_7 : Region 12 n12b_mask [7,3] 28 7 20 none :=
  of_certs (hn:=by decide) [
  0x792a1b865430ba967583a7b0425210,
  0xb1a29765830b869a7543ab70425210,
  0xb3856792a1b869a75430ab70425210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_3_8 : Region 12 n12b_mask [8,3] 28 8 19 none :=
  of_certs (hn:=by decide) [
  0xb1a968345708ba29765a7b30425210,
  0xb1a2968570679ab8345a7b30425210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_3_9 : Region 12 n12b_mask [9,3] 28 9 18 none :=
  of_certs (hn:=by decide) [
  0x9683b7a52ba9765430b857042a1210] (by rfl)

private theorem n12b_3 : Region 12 n12b_mask [3] 29 3 27 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n12b_3_3
  · exact n12b_3_4
  · exact n12b_3_5
  · exact n12b_3_6
  · exact n12b_3_7
  · exact n12b_3_8
  · exact n12b_3_9
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_4 : Region 12 n12b_mask [4] 29 4 26 none :=
  of_certs (hn:=by decide) [
  0xab34528675a965b7a1b83079204210,
  0xba543a96528675b7a1b83079204210,
  0xab34586792a9657b1ab83075204210,
  0xab3458692a97657b1ab83075204210,
  0xba968543a297657b1ab83075204210,
  0xba96543a5867927b1ab83075204210,
  0xba768543a296597b1ab83075204210,
  0xba76543a2968597b1ab83075204210,
  0xba9683a56792b85430b7a175204210,
  0x768b1a925430b7a5837965ba204210,
  0xb86792a5430ba965837b1a75204210,
  0xa543b867928569ab037b1a75204210,
  0xab3856792b869a54307b1a75204210,
  0xba76830b8543a5692b79a175204210,
  0xba7683b85430a5692b79a175204210,
  0x7a1b86925430b7583a9765ba204210,
  0xb1a297658309a7b86b345a75204210,
  0xb8692a5430ba7658397b1a75204210,
  0xa543b86928567ab0397b1a75204210,
  0xb7a29658308ba976543b1a75204210,
  0xba29768309a7b856543b1a75204210,
  0xa7b85692ba976830543b1a75204210,
  0xab3867929a7b8565430b1a75204210,
  0x7968b1a25430b38567a920ab754210,
  0xb867a925430b38569702a1ab754210,
  0xba768392a5697b1ab8570345204210,
  0xb8692a75430ba58397b1a765204210,
  0xb3856792a19a7b865ab07345204210,
  0xa57b386928ba9765a1b07345204210,
  0xb79a5683ab857692a1b07345204210,
  0xa7b3856928ba9765a1b07345204210,
  0xab3867929a7b8565a1b07345204210,
  0xa58b792b3867a1ba96570345204210,
  0xb1a5438679207a9658b307ba254210,
  0x79a1b865430b385a769207ba254210,
  0xb86792a19ab756a58307b345204210,
  0x79ab865b7692a1a58307b345204210,
  0x792a1b865430ba967583a7b0254210,
  0xb1a29765830b869a7543ab70254210,
  0xb3856792a1b869a75430ab70254210,
  0xb1a2968345708ba9765a7b30254210,
  0xb1a968345708ba29765a7b30254210,
  0xb1a2968570679ab8345a7b30254210,
  0xb1a2968570679ab345a7b830254210,
  0xba9768543b1a296570a7b830254210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_5 : Region 12 n12b_mask [5] 29 5 25 none :=
  of_certs (hn:=by decide) [
  0x7a965b8543ab79276830b0421a5201,
  0xb38692a5408ba7597b1a7652034210,
  0xb8692a54083ba7597b1a7652034210,
  0xa7b386929ab045758b1a7652034210,
  0xa7b386929ab857540b1a7652034210,
  0xba97583a7b8692540b1a7652034210,
  0x45683b1a7920b85a96707ba2534210,
  0x79a1b386540b85a769207ba2534210,
  0xb38567a920b8697045a17ba2534210,
  0x792a540ab3869758b1ab7652034210,
  0x7692a1b3854079ab865a7b02534210,
  0xb38692a75408b1a9765ab702534210,
  0xb3856792a17a968b045ab702534210,
  0xb386792a5407b1a9658ba702534210,
  0xb3865792a1a967b0458ba702534210,
  0xa57b38692b1a9765408ba702534210,
  0xa7b38569279a1b045ab86702534210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_6 : Region 12 n12b_mask [6] 29 6 24 none :=
  of_certs (hn:=by decide) [
  0x79a540857b03ab8692a76521b34201,
  0x457b1a2968308ba765a97025b34210,
  0x457ba2968308b1a765a97025b34210,
  0x4567a1b8308692ab75a97025b34210,
  0xb758692a14567ab830a97025b34210,
  0x45a1b768308ba297569a7025b34210,
  0x45ab768308b1a297569a7025b34210,
  0x9768ba527a965830b75402a1b34210,
  0x7b1a296583403b8679a54210ba7520] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_7 : Region 12 n12b_mask [7] 29 7 23 none :=
  of_certs (hn:=by decide) [
  0x7b1a96540a2976857ab3025b834210,
  0x7569ab30a7685402a1b7925b834210,
  0x7b1a296583403b8679a5420ba75210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_8 : Region 12 n12b_mask [8] 29 8 22 none :=
  of_certs (hn:=by decide) [
  0x7b1a296583403b8679a520ba754210,
  0x43b7685a920b83079652a1ba754210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_9 : Region 12 n12b_mask [9] 29 9 21 none :=
  of_certs (hn:=by decide) [
  0x456792a1b830b7a96852075ab34210,
  0xb1a2976854038b7a9652075ab34210] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12b_10 : Region 12 n12b_mask [10] 29 10 20 none :=
  of_certs (hn:=by decide) [
  0x792a568b30a967b04521ba75834201] (by rfl)

private theorem n12b_root : Region 12 n12b_mask [] 30 3 30 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n12b_3
  · exact n12b_4
  · exact n12b_5
  · exact n12b_6
  · exact n12b_7
  · exact n12b_8
  · exact n12b_9
  · exact n12b_10
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

private def lib12_28 : List (List Nat) := [
  [7,7,7,7],
  [6,11,11],
  [5,11,12],
  [7,9,12],
  [4,4,4,4,4,8],
  [3,3,11,11],
  [4,8,8,8],
  [8,9,11],
  [7,10,11],
  [4,4,4,4,12],
  [8,8,12],
  [4,5,7,12],
  [4,4,4,8,8],
  [9,9,10],
  [8,10,10],
  [3,4,9,12],
  [3,8,8,9],
  [3,5,8,12],
  [6,6,6,10],
  [4,4,9,11],
  [4,4,4,7,9],
  [5,5,5,5,8],
  [4,4,4,5,11],
  [3,4,4,4,4,4,5],
  [3,4,4,4,4,9],
  [3,4,4,8,9],
  [5,5,8,10],
  [5,5,9,9],
  [5,5,7,11],
  [4,6,9,9],
  [4,4,4,4,5,7],
  [4,5,5,5,9],
  [5,5,6,6,6],
  [4,7,7,10],
  [3,7,8,10],
  [4,4,10,10],
  [3,4,10,11],
  [3,5,10,10],
  [5,7,8,8],
  [3,5,5,7,8],
  [3,5,5,5,10],
  [3,5,5,5,5,5],
  [3,4,5,8,8],
  [4,4,5,7,8],
  [4,4,5,6,9],
  [4,4,5,5,5,5],
  [3,4,4,4,5,8]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem lib12_28_proof : Library 12 n12_28_mask lib12_28 :=
  check_library (hn:=by decide) lib12_28 [
    0x6478953b48a372a6b91509416230,
    0x6274b98a351a6b23784190649503,
    0xa61984b2735059b623a874164903,
    0xa35162784b90b6a8947326419503,
    0xa8736150b946b4726a3298419530,
    0xa64872b95306b473a89051623941,
    0xb6a894729b487361a32641509530,
    0xa3784b26190746a895326b941503,
    0xa3784162b9074b6a895326491503,
    0xa846372b915098746a326b419530,
    0xa872b4163590a6b9847326491503,
    0xa6b237849150a89b463726149530,
    0x749b6a32a87361504b2698419530,
    0xa374b2619078a6495326b9841503,
    0xb46a359872a8473261906b941503,
    0xa36b278415906a89b47329164530,
    0x94b278a616b98473263a09514530,
    0xa3784b2615907498a6326b914530,
    0xb46a359872749b638a0914516230,
    0xa3726489150b9478a632b6149530,
    0xa874b61509b27364a32698419530,
    0xb648a372b98749536194150a6230,
    0xa872b946150b6374a32698419530,
    0xb487273646a329b615941a890530,
    0x9b4873a616b2347265941a890530,
    0x59b263741784b6a329164a890530,
    0x9b273a84616b47895390514a6230,
    0xa8746b953984b2736190514a6230,
    0x953a8472b61789b46390514a6230,
    0xb63a894729b48732616a05149530,
    0xb478a326150a9b64736298419530,
    0x73a849b62b463278914a61509530,
    0x74b953b6487298a36194150a6230,
    0x9b23748a617894b6263a05149530,
    0x98a374b2617849b6326a09514530,
    0x94b2378a61a36b98415072649530,
    0x59b6273a841b47890a6329164530,
    0x6a32748951a87362b4906b914530,
    0xa846b95394b273617890514a6230,
    0xb463a8726b9473289514a6190530,
    0x5987236b41a84739b264a6190530,
    0x74b63b9462a327859841a6190530,
    0xb4873a62632749516b914a890530,
    0xb463a8726b94732a051698419530,
    0xb9463a8726b4732a051698419530,
    0x74b63b9462a3278a615098419530,
    0xb4873a6274632b9165941a890530] (by rfl)

private def lib12_32_0 : List (List Nat) := [
  [8,8,8,8],
  [4,4,4,4,4,4,4,4],
  [8,12,12],
  [5,9,9,9],
  [4,4,12,12],
  [3,5,12,12],
  [10,11,11],
  [4,4,4,4,4,4,8],
  [4,4,4,4,4,12],
  [9,11,12],
  [10,10,12],
  [4,7,7,7,7],
  [7,8,8,9],
  [5,7,8,12],
  [5,8,8,11],
  [5,5,10,12],
  [5,5,5,5,12],
  [3,4,4,4,4,4,4,5],
  [7,7,9,9],
  [4,6,11,11],
  [5,5,11,11],
  [4,8,8,12],
  [3,4,7,7,11],
  [6,6,9,11],
  [3,3,4,11,11],
  [4,4,4,4,4,5,7],
  [6,8,9,9],
  [4,9,9,10],
  [4,4,4,4,8,8],
  [3,7,11,11],
  [7,7,7,11],
  [4,4,8,8,8],
  [4,5,11,12],
  [5,5,5,5,5,7],
  [3,4,4,7,7,7],
  [5,5,5,6,11],
  [5,7,10,10],
  [5,5,5,7,10],
  [3,7,10,12],
  [4,5,6,6,11],
  [5,5,6,6,10],
  [3,3,3,3,9,11],
  [7,7,8,10],
  [6,6,10,10],
  [4,4,4,4,7,9],
  [4,4,4,4,5,11],
  [3,6,6,6,11],
  [3,5,5,7,12],
  [3,3,3,11,12],
  [5,6,10,11],
  [3,7,7,7,8],
  [5,5,5,5,6,6],
  [3,9,9,11],
  [6,6,6,6,8],
  [6,7,9,10],
  [6,7,8,11],
  [4,4,7,7,10],
  [3,3,3,3,3,3,3,11],
  [3,6,11,12],
  [6,6,8,12]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem lib12_32_0_proof : Library 12 n12_32_mask lib12_32_0 :=
  check_library (hn:=by decide) lib12_32_0 [
    0xb85a7921b769a180ba25704386542013,
    0x8b767965ba7058025a24a921b1834013,
    0x792a1b386540b769a58134208ba75210,
    0x8692a7b31b1a97658038ba5702445210,
    0x83b1a56792407ba968543120a752b810,
    0x8692a5431b70b381a97652408ba75210,
    0x792a1b86540b769a520813ba75834210,
    0xa568b7929a768543ab31b18075204210,
    0xb792a13456809a76b85ab38175204210,
    0x7692a581b340b79a13865208ba754210,
    0x7b318692a5408b1a976520ba75834210,
    0xa58b792b3867a1ba9657052081344210,
    0xa29657b31a976804581ba7025b834210,
    0xb13429a57680ba796583b81a20745210,
    0xb31a2975680b769a581ab83420745210,
    0xb1a9765834208692a57b31ab80745210,
    0xb1342a975680ba583b7a187692045210,
    0xb79a168579652a5428b31ba708340210,
    0x85792ab31867b1a54069a7025b834210,
    0xba9765431809683b1a57028b7a254210,
    0xb342a976581b75a1386920ab80745210,
    0xb7a296543180b38579a1ab8670254210,
    0xb186542a970a758b31ab769258340210,
    0xb18692a7540a97658b31ab7025834210,
    0xb8692a7543183ba9765240a185b70210,
    0xa967b8568345a792ab31b18075204210,
    0x8569a7b31b1a297540ab867025834210,
    0xb7a9654380b85792a13ab18670254210,
    0x8679a543a7b85692b31ab18075204210,
    0xb769a543180a1b386570428ba7925210,
    0x813ba297540b7685a169a7025b834210,
    0xb7a96583b86792a1ba54318075204210,
    0x8692a5431b70b381a9765208ba754210,
    0xba9768192a567b31ab85708342045210,
    0xa967542b792581b865a13ba708340210,
    0xb31865a2970b769a1ab8578342045210,
    0xba76924381b31a975680b85a20745210,
    0x8692a57b318ba9765a1b078342045210,
    0xb13869a2457081a567b3408ba7925210,
    0xb3457a29681a97b8531ab08765204210,
    0x85692a7b318ba9765a1b078342045210,
    0xb34296857a15679ab804a25831b70210,
    0x81ba297540a5867b3169a7025b834210,
    0xa297658b31b1869a7540ab7025834210,
    0xa543867928b7a965b31ab18075204210,
    0xa297b865431ba583967ab18075204210,
    0xb3457a29681a97b8531ab08765240210,
    0xb1345a297680ba96583b7a1875240210,
    0x7b381a296540ba976852431a75b80210,
    0xb86975a24319a76583b02ba180745210,
    0xb869a543857ab131a29708b765240210,
    0xa56792ba96817b31ab85708342045210,
    0xb345792a180b7a965831ab8670425210,
    0x8692ab31a54079758b1ab76520834210,
    0xb18679a540a29657b318ba7025834210,
    0xb186792a540a9657b318ba7025834210,
    0x8b792a5431ba9658367a1b0875204210,
    0x8b345769210a97865a52b70204ba1813,
    0x83b1a5429670ba9756813408b7a25210,
    0xb318692a7540b85679a1ab7025834210] (by rfl)

private def lib12_32_1 : List (List Nat) := [
  [5,6,6,6,9],
  [3,3,3,3,3,6,11],
  [3,5,5,5,7,7],
  [3,3,4,7,7,8],
  [4,4,4,6,7,7],
  [4,6,10,12],
  [4,4,6,7,11],
  [5,6,6,7,8],
  [3,3,5,7,7,7],
  [5,7,9,11],
  [5,6,7,7,7],
  [5,5,7,7,8],
  [3,3,4,4,4,7,7],
  [6,6,6,7,7],
  [6,7,7,12],
  [3,3,7,8,11],
  [3,5,7,7,10],
  [3,3,7,7,12],
  [3,3,4,4,7,11],
  [4,6,7,7,8]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem lib12_32_1_proof : Library 12 n12_32_mask lib12_32_1 :=
  check_library (hn:=by decide) lib12_32_1 [
    0xa7b3856928ba9765a1b0781342045210,
    0x86975a1b3408ba76592a542831b70210,
    0x867a543ab8569297b1ab318075240210,
    0x8675ab31697a2458b1a9258340b70210,
    0xb79a543ab8569276831ab18075204210,
    0xba543186792083b1a965708b7a254210,
    0x8b7a2965431ba976835a1b0875204210,
    0xab3867929a7b8565a1b0781342045210,
    0xba97583967a542b8652a181340b70210,
    0xb3429a7658086975ab13b81a20745210,
    0xa58b792b3867a1ba9657081342045210,
    0xa2967b318ba9756a581b078342045210,
    0xb8679a1ba758139652a5428340b70210,
    0x869ab31792a540758b1ab76520834210,
    0xb3186792a540b7569a18ba7025834210,
    0xb8692a75431ba976583a180425b70210,
    0x8b792a5431ba9658367a1b0875240210,
    0x83b1a75692408ba54318679a25b70210,
    0xa2457968b31ba76581a9258340b70210,
    0xa2967b318ba9756a581b078345204210] (by rfl)

private def lib12_32 : List (List Nat) :=
  lib12_32_0 ++ lib12_32_1

private theorem lib12_32_proof : Library 12 n12_32_mask lib12_32 :=
  library_append (lib12_32_0_proof) lib12_32_1_proof

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_3_3 : Region 12 n12_mask [3,3] 58 3 54 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  58379,58371,41995,62467,49163,24587,41987,22539,47115,49155,
  29707,53259,73729,79873,24579,64513,24577,24593,69633,23563,
  78849,76801,30731,9227,10251,6155] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_3_4 : Region 12 n12_mask [4,3] 58 4 53 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  1071,1073,17417,17427,1075,17433,1055,1059,1057,17421,
  4143,7199,17429,7201,8223,47,5129,8225,28707,5139,
  49,2097,93,5145,34883,31775,4127,31779,4131,34817,
  34833,51,2099,5143,85,5133,
  0x124e74c9630a10936f44a2c61516d2ea628417530eca86421670c54b22e80,
  22531,22529,11333,22545,
  0x10936f44a2c61516d2ea628417530eca86420e765230c8168e4d43470b2a0,
  31,2079,10271,
  0x14d648b06f236744b290ec35168eac65216f52c86a3015730c4e0a8260420,
  6217] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_3_5 : Region 12 n12_mask [5,3] 58 5 52 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  83,63489,81,48129,48135,79,5125,77825,5121,5127,
  35,75,5141,5135] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_3_6 : Region 12 n12_mask [6,3] 58 6 51 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  47107,59395,29699,53251] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_3_7 : Region 12 n12_mask [7,3] 58 7 50 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  51201,38913,29697,51217,
  0x10936f44a2c61516d2ea628417530eca86421674c8e54b0c522e7036812a0,
  38919,29713,69,12321] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_3_8 : Region 12 n12_mask [8,3] 58 8 49 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  33,2081] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_3_9 : Region 12 n12_mask [9,3] 58 9 48 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  0xe765234b0c810936f44a2c61516d2ea628417530eca8642168e4d47032a0] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_3_10 : Region 12 n12_mask [10,3] 58 10 47 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  0x122c568eb47014d630924a6e17144f2c682a14f72b0c84637530eca806420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_3_11 : Region 12 n12_mask [11,3] 58 11 46 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  0x14364c6e92b01686b4d0324e12d6f47084a15172ea8c2657530eca2806420] (by rfl)

private theorem n12quick_3 : Region 12 n12_mask [3] 59 3 57 (some 30) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n12quick_3_3
  · exact n12quick_3_4
  · exact n12quick_3_5
  · exact n12quick_3_6
  · exact n12quick_3_7
  · exact n12quick_3_8
  · exact n12quick_3_9
  · exact n12quick_3_10
  · exact n12quick_3_11
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_4_4 : Region 12 n12_mask [4,4] 58 4 52 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  0x1570f734d512b0ceb6f2908e76744c6a52ca2c863634124e10280a8406420,
  1033,1085,1043,1069,1065,1049,25609,8201,1063,25619,
  46089,45065,1037,8211,25625,1029,1031,1045,1039,7191,
  46105,45081,7181,4105,8231,25613,8215,7173,7175,7189,
  7183,4115,13321,14345,8197,12297,8199,9,2057,9225,
  61,13331,28677,28679,19,28687,2067,9235,13337,4119,
  45,2093,65537,11335,41,2089,25,2073,9241,
  0xb24f67430c813654e90a2c61516d2ea628417530eca86420d4a5692306e0,
  3163,27711,3161,87,21527,32781,3111,3143,4101,67585,
  27707,57345,57361,18471,31751,
  0x168f4d2b076d092eb45730ec8743516e6c3217524ca300e4a6280a8406420,
  4103,21517,39,4117,4111] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_4_5 : Region 12 n12_mask [5,4] 58 5 51 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  16407,3135,
  0x10936f44a2c61516d2ea628417530eca86420c967564d02e70a124e814b22,
  15383,19521,39941,19513,27703,
  0x168e702c52b410923456ec6a12d4770e4a28172f50ac8637530cea8406420,
  32773,39939,3131,32771,23,2071,10263,
  0x14764ec8b1216e92b44c701690d4e6a5235172cae0863752f02ca28406420,
  14349,21509,
  0x165470aec921690cb24e1432d4f66a81035172e6c4b7530e862ca28406420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_4_6 : Region 12 n12_mask [6,4] 58 6 50 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  19493,66563,19459,80897,11267,18491,19473] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_4_7 : Region 12 n12_mask [7,4] 58 7 49 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  11265,11281,11293,
  0x164f2d068b43690e6d44b21476e8c523013714eca097530a2cea628406420,
  6211,12301,21511,
  0x168c6f0b254364ecb4703216f410d2875172e8a4d753080a2cea628406420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_4_8 : Region 12 n12_mask [8,4] 58 8 48 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  13,2061,9229,
  0xe5632b470c810936f44a2c61516d2ea628417530eca8642124d430a168e6] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_4_9 : Region 12 n12_mask [9,4] 58 9 47 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  0x1654c8e70b23290d674e5614312ea97152c4a0f74a2c68130eca628406420,
  27675,
  0x10936f44a2c61516d2ea628417530eca864212b4306e4c808e0b0d4776522] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_4_10 : Region 12 n12_mask [10,4] 58 10 46 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  0x16542c6e92b014a76c90324e136f470c482a1714d2ea8637530eca4086420,
  0x128ea6d4563014a9076c324e17146f2c82a14f72b0c48637530eca4086420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_4_11 : Region 12 n12_mask [11,4] 58 11 45 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  0x143652a8e6d0128d670b44e16f4d23086a15172eac48277530ec2a4086420] (by rfl)

private theorem n12quick_4 : Region 12 n12_mask [4] 59 4 56 (some 30) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n12quick_4_4
  · exact n12quick_4_5
  · exact n12quick_4_6
  · exact n12quick_4_7
  · exact n12quick_4_8
  · exact n12quick_4_9
  · exact n12quick_4_10
  · exact n12quick_4_11
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_5 : Region 12 n12_mask [5] 59 5 55 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  35905,52229,33795,33793,33799,14379,3115,16389,52227,16387,
  16385,16391,20537,43,35877,40965,35843,37891,37889,
  0x1516d2ea628417530eca8642129670a10324c80e4a2c610d4e972b456e742,
  37895,14389,3125,3127,
  0x123674a4c8f014d2964e702a16f452b082c615172eca637530cea84086420,
  15365,20485,40963,26679,15363,20483,72705,15361,
  0x10936f44a2c61516d2ea628417530eca86420e7430a12364e8168d072b4c4,
  57,15367,20497,53,61443,50213,68609,23557,44037,50179,
  71681,70659,36867,3075,13313,36865,
  0x1456306e8ad210ec9674324a16f4b290c615172e4d7530a2cea6284086420,
  13319,36871,77,13333,
  0x12b46e5630c810936f44a2c61516d2ea628417530eca86420e9670a14c522,
  5,14365,3087,3101,2053,3099,
  0x1432cae764901296d4702a4e170b254e82c616f350c8a635730ec40a86420,
  9221,10245,6149,
  0x1654c8e70b2308b476d24e1296f430c6a15172ea4c2617530eca284086420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_6 : Region 12 n12_mask [6] 59 6 54 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  54273,55333,54287,74753,23555,6181,60417,44039,23573,75777,
  56321,30723,18435,56349,
  0x1632ace90741692f4b0c6d36543009516e6124d7530e4a2cea62840a86420,
  55323,26639,26653,26651,
  0x16e92d0b452af4d67033096346e15172e4c817524a2c610eca62840a86420,
  9219,10243,6147] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_7 : Region 12 n12_mask [7] 59 7 53 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  30721,43009,2049,10241,6145,30749,18447,43035,18459,
  0x10c743296e4a12b44ce7630814d2570e82a6172f50ac841753062cea86420,
  7,17,12303,12317,12315,
  0x166e912d456cf074b23296f430a15172e4c817524a2c610ca62840ea86420,
  2055,10247,
  0x16744e90ad232b4c856e701692f430c6a15370ec4a28175124062cea86420,
  6161] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_8 : Region 12 n12_mask [8] 59 8 52 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  21,15,29,27,
  0x14d07692e56d308e7434f65230a17152a4c8174a2c6130ea62840eca86420,
  2069,9237] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_9 : Region 12 n12_mask [9] 59 9 51 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  0x16546eb2c903670d4324e814f6930a4c617152e0a2d74a6284130eca86420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n12quick_12 : Region 12 n12_mask [12] 59 12 48 (some 30) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib12_28_proof lib12_32_proof [
  0x124d4368e70a0e5674b230c810936f44a2c61516d2ea628417530eca86420] (by rfl)

private theorem n12quick_root : Region 12 n12_mask [] 60 3 60 (some 30) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n12quick_3
  · exact n12quick_4
  · exact n12quick_5
  · exact n12quick_6
  · exact n12quick_7
  · exact n12quick_8
  · exact n12quick_9
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact n12quick_12

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem verified12 (m : Multiset Nat) (bound : ∀ d∈m,3≤d ∧ d≤12)
    (sm : m.sum=60) : Realizes 12 m :=
  patched (left:=30) (right:=30) (total:=60) (p:=n12a_mask) (q:=n12b_mask)
    (by decide) (by decide) (by decide) (by rfl) (by decide) n12a_root n12b_root
    (show Region 12 (minusMatch 12) [] 60 3 60 (some 30) from n12quick_root) m bound sm

private abbrev n14a_mask : Nat := 0x103e00019d0006c200273001c400cc00b001000e040620
private abbrev n14b_mask : Nat := 0x2f40000e4200091c00184002320031004c02f0300b0812
private abbrev n14_mask : Nat := 0x3f7e000fdf000fde003f7003f600fd00fc03f03e0f0e32
private abbrev n14_40_mask : Nat := 0x103e00019d0006c200273001c400cc00b001000e040010
private abbrev n14_44_mask : Nat := 0x2f40000e4200091c00184002320031004c02f0300b0e22

private def perm14Fun : Fin 14 → Fin 14
  | ⟨0,_⟩ => ⟨1,by decide⟩ | ⟨1,_⟩ => ⟨2,by decide⟩ | ⟨2,_⟩ => ⟨3,by decide⟩ | ⟨3,_⟩ => ⟨0,by decide⟩
  | ⟨4,_⟩ => ⟨5,by decide⟩ | ⟨5,_⟩ => ⟨11,by decide⟩ | ⟨6,_⟩ => ⟨13,by decide⟩ | ⟨7,_⟩ => ⟨8,by decide⟩
  | ⟨8,_⟩ => ⟨9,by decide⟩ | ⟨9,_⟩ => ⟨10,by decide⟩ | ⟨10,_⟩ => ⟨7,by decide⟩ | ⟨11,_⟩ => ⟨12,by decide⟩
  | ⟨12,_⟩ => ⟨4,by decide⟩ | ⟨13,_⟩ => ⟨6,by decide⟩

private def inv14Fun : Fin 14 → Fin 14
  | ⟨0,_⟩ => ⟨3,by decide⟩ | ⟨1,_⟩ => ⟨0,by decide⟩ | ⟨2,_⟩ => ⟨1,by decide⟩ | ⟨3,_⟩ => ⟨2,by decide⟩
  | ⟨4,_⟩ => ⟨12,by decide⟩ | ⟨5,_⟩ => ⟨4,by decide⟩ | ⟨6,_⟩ => ⟨13,by decide⟩ | ⟨7,_⟩ => ⟨10,by decide⟩
  | ⟨8,_⟩ => ⟨7,by decide⟩ | ⟨9,_⟩ => ⟨8,by decide⟩ | ⟨10,_⟩ => ⟨9,by decide⟩ | ⟨11,_⟩ => ⟨5,by decide⟩
  | ⟨12,_⟩ => ⟨11,by decide⟩ | ⟨13,_⟩ => ⟨6,by decide⟩

private def perm14 : Fin 14 ≃ Fin 14 where
  toFun := perm14Fun
  invFun := inv14Fun
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def perm14Graph : K 14 ≃g K 14 where
  toEquiv := perm14
  map_rel_iff' := perm14.injective.ne_iff

private theorem complementary14 (A : Region 14 n14a_mask [] 42 3 42 none) :
    Region 14 n14b_mask [] 42 3 42 none := by
  intro ds hm hp hs
  apply moveCover perm14Graph _ (A ds hm hp hs)
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_3_3 : Region 14 n14a_mask [3,3,3,3,3,3,3] 35 3 21 none :=
  of_certs (hn:=by decide) [
  0xc74a46769b68b95c82a9152142d873d13db0a50c30,
  0xd47c82b68976b95a64873c42a91d31521db0a50c30,
  0xd4782c837b68976b95a64c42a91d31521db0a50c30,
  0xd4a697c82b86b95764873c42a91d31521db0a50c30,
  0x9b87b6958673c74a64c82d42a91d31521db0a50c30,
  0xd4796b828c76b95a64873c42a91d31521db0a50c30,
  0xd4a6b8297c86b95764873c42a91d31521db0a50c30,
  0xb8c796d4a682b95764873c42a91d31521db0a50c30,
  0xa4d3197c8250873c03b86b95db0d21c42a51a96764,
  0xd479b82c867b695a64873c42a91d31521db0a50c30,
  0xd4a682c79b8b695764873c42a91d31521db0a50c30,
  0xd4a6b597c829b86746873c42a91d31521db0a50c30,
  0xb8c76a6974d4682b95873c42a91d31521db0a50c30,
  0xd4a6b97c8295b86746873c42a91d31521db0a50c30,
  0xd4a695b82b97c86746873c42a91d31521db0a50c30,
  0xd4a69b82b597c86746873c42a91d31521db0a50c30,
  0xd4a682b978b6958c73764c42a91d31521db0a50c30,
  0xc8b97d4682b695a674873c42a91d31521db0a50c30,
  0xd46b597c829b86a476873c42a91d31521db0a50c30,
  0xd46b97c8295b86a476873c42a91d31521db0a50c30,
  0xd4695b82b97c86a476873c42a91d31521db0a50c30,
  0xb68c795d469b82a476873c42a91d31521db0a50c30,
  0xc73195286bd4a09b87d30c83b50d21c42a51a96764,
  0xd4a67c8295b86b9746873c42a91d31521db0a50c30,
  0xb8c7695a4d286b9746873c42a91d31521db0a50c30,
  0xd2c4a68b5973183d42c78b96764a91521db0a50c30,
  0x9b8c76795b64d4a682873c42a91d31521db0a50c30,
  0xd4a6b59738c28b9642876c74a91d31521db0a50c30,
  0xd4a6b597c82738b964876c42a91d31521db0a50c30,
  0xd4a6b97c82738b5964876c42a91d31521db0a50c30,
  0xa695b8c74d46b97382876c42a91d31521db0a50c30,
  0xd4682b978b695a6748c73c42a91d31521db0a50c30,
  0xd4a695b82b97687468c73c42a91d31521db0a50c30,
  0xd4a69b82b597687468c73c42a91d31521db0a50c30,
  0xd469b82b59786a4768c73c42a91d31521db0a50c30,
  0xa4d2c7386b5919b87c428a96764d31521db0a50c30,
  0xd4a678295b86b97468c73c42a91d31521db0a50c30,
  0xb87695d4a682b97468c73c42a91d31521db0a50c30,
  0xd4a695b837c2b9786c428764a91d31521db0a50c30,
  0xd4a6b597c829b83768746c42a91d31521db0a50c30,
  0xd4a6b97c8295b83768746c42a91d31521db0a50c30,
  0xd4a6b97827c8b59648376c42a91d31521db0a50c30,
  0xc876a495b86b9746c7382d42a91d31521db0a50c30,
  0xd4a6b597c829b87683746c42a91d31521db0a50c30,
  0xd4a6b97c8295b87683746c42a91d31521db0a50c30,
  0xd4a6b978295b8c7683746c42a91d31521db0a50c30,
  0x7c8b5964d4a67382b9786c42a91d31521db0a50c30,
  0xa695b8c74b97386782d46c42a91d31521db0a50c30,
  0xd4a67c82b5973869b8746c42a91d31521db0a50c30,
  0xb68c795a69b874d467382c42a91d31521db0a50c30,
  0xa19768b52d4c30c742150c82db0d31b96a95a64873,
  0xa95b647c82d31d4a68b91976873c42521db0a50c30,
  0xd4a6b597c831d28b96473876c42a91521db0a50c30,
  0xd4a6b597c837469b82d13876c42a91521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_3_4 : Region 14 n14a_mask [4,3,3,3,3,3,3] 35 4 20 none :=
  of_certs (hn:=by decide) [
  0xd4c282466a47b879b6958c73a91d31521db0a50c30,
  0xa695b874b976c837d4c28642a91d31521db0a50c30,
  0xa6b59749b876c837d4c28642a91d31521db0a50c30,
  0xb87695a6b974c837d4c28642a91d31521db0a50c30,
  0xd4a695b837c2b9768c478642a91d31521db0a50c30,
  0xc876a4d2c749b837b6958642a91d31521db0a50c30,
  0xd4a69b837c2b59768c478642a91d31521db0a50c30,
  0xd4a6b597c29b83768c478642a91d31521db0a50c30,
  0xd4a6b97c295b83768c478642a91d31521db0a50c30,
  0xc8b596a4d46b97c283768742a91d31521db0a50c30,
  0xc8764d47c26824a8b973b695a91d31521db0a50c30,
  0xd4a6b597c29b8764c8378642a91d31521db0a50c30,
  0xd4a6b97c295b8764c8378642a91d31521db0a50c30,
  0xc879b6a495b8376c2d478642a91d31521db0a50c30,
  0xc795b6a4d2c87469b8378642a91d31521db0a50c30,
  0xc79b6a48b596738c2d478642a91d31521db0a50c30,
  0xc7386b5912d4a0528c30b978db0d31c42a51a96764,
  0xa4d2c8376b5918b9a6429786c74d31521db0a50c30,
  0xd4a6b59738c28b967c427864a91d31521db0a50c30,
  0xd4a6b9738c28b5967c427864a91d31521db0a50c30,
  0xd4c7695b828c24a6b9737864a91d31521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_3_5 : Region 14 n14a_mask [5,3,3,3,3,3,3] 35 5 19 none :=
  of_certs (hn:=by decide) [
  0x8c4a6b97395b86d47c287642a91d31521db0a50c30,
  0xc8b596a4b97386d47c287642a91d31521db0a50c30,
  0xc8b96a486b5973d47c287642a91d31521db0a50c30,
  0xa4db683c791250b8730d28c0b95d31c42a51a96764,
  0xc8b96a4b59786374d28c7642a91d31521db0a50c30,
  0xa4d2c8376b5918b9642a9786c74d31521db0a50c30,
  0xd4a6b59738c2c78b96476824a91d31521db0a50c30,
  0xd4a6b9738c2c78b596476824a91d31521db0a50c30,
  0xd4a6b978c2c738b596476824a91d31521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_3_6 : Region 14 n14a_mask [6,3,3,3,3,3,3] 35 6 18 none :=
  of_certs (hn:=by decide) [
  0xb87695c79b64d4a6828c2473a91d31521db0a50c30,
  0xd4a6b59738c278b964c76824a91d31521db0a50c30,
  0xd4a695b87c2c86b974673824a91d31521db0a50c30,
  0xd4a69b87c2c86b5974673824a91d31521db0a50c30,
  0xc78b596a4d479b68c2673824a91d31521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_3_7 : Region 14 n14a_mask [7,3,3,3,3,3,3] 35 7 17 none :=
  of_certs (hn:=by decide) [
  0xd4795b68c2c78b964a673824a91d31521db0a50c30,
  0xd479b68c2c78b5964a673824a91d31521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_3_8 : Region 14 n14a_mask [8,3,3,3,3,3,3] 35 8 16 none :=
  of_certs (hn:=by decide) [
  0xd4a678c2b6824c798b596473a91d31521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_3_10 : Region 14 n14a_mask [10,3,3,3,3,3,3] 35 10 14 none :=
  of_certs (hn:=by decide) [
  0xc31d25974a68b05bd4673821b96c42d03a50a91c87] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_3_11 : Region 14 n14a_mask [11,3,3,3,3,3,3] 35 11 13 none :=
  of_certs (hn:=by decide) [
  0xa9647c8b52d31d4a6b973821876c42951db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_3_12 : Region 14 n14a_mask [12,3,3,3,3,3,3] 35 12 12 none :=
  of_certs (hn:=by decide) [
  0xa9b647c82d31b83796a4d125876c42951db0a50c30] (by rfl)

private theorem n14a_3_3_3_3_3_3 : Region 14 n14a_mask [3,3,3,3,3,3] 36 3 24 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14a_3_3_3_3_3_3_3
  · exact n14a_3_3_3_3_3_3_4
  · exact n14a_3_3_3_3_3_3_5
  · exact n14a_3_3_3_3_3_3_6
  · exact n14a_3_3_3_3_3_3_7
  · exact n14a_3_3_3_3_3_3_8
  · exact absent_region (by rfl)
  · exact n14a_3_3_3_3_3_3_10
  · exact n14a_3_3_3_3_3_3_11
  · exact n14a_3_3_3_3_3_3_12
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_4 : Region 14 n14a_mask [4,3,3,3,3,3] 36 4 23 none :=
  of_certs (hn:=by decide) [
  0xa95b8749b67c837d4c28642a691d31521db0a50c30,
  0xa9b87495b67c837d4c28642a691d31521db0a50c30,
  0xd4a95b837c29b678c478642a691d31521db0a50c30,
  0xb8795a9b64d4c828673c742a691d31521db0a50c30,
  0xd4a95b67c29b8378c478642a691d31521db0a50c30,
  0xd4a9b67c295b8378c478642a691d31521db0a50c30,
  0xc78b59a4d2c83749b678642a691d31521db0a50c30,
  0xc876b59a4d2c749b8378642a691d31521db0a50c30,
  0xc76b59a4d2c8749b8378642a691d31521db0a50c30,
  0xc78b9a4d4738c295b678642a691d31521db0a50c30,
  0xa6b597c824d130c4a50d3c29b86764512a91873db0,
  0xc76b9a4d2c87495b8378642a691d31521db0a50c30,
  0xa4d2c7386b591c8b964a9768742d31521db0a50c30,
  0xd4a95b6837c2c8b97647824a691d31521db0a50c30,
  0xd4a9b6837c2c8b597647824a691d31521db0a50c30,
  0x86b59a4c73d2c8b97647824a691d31521db0a50c30,
  0xc86b59a4b9738d47c287642a691d31521db0a50c30,
  0xc86b9a4b59738d47c287642a691d31521db0a50c30,
  0xa4d2c8376b591a9b8697c468742d31521db0a50c30,
  0xb68795c8b9a4d47382c7642a691d31521db0a50c30,
  0xd4a95b6837c2c8b97467824a691d31521db0a50c30,
  0xd4a95b687c2c8b976473824a691d31521db0a50c30,
  0xd4a9b687c2c8b5976473824a691d31521db0a50c30,
  0xc876b59a4d468b97c273824a691d31521db0a50c30,
  0xd4a95b687c2c8b974673824a691d31521db0a50c30,
  0xd4a9b687c2c8b5974673824a691d31521db0a50c30,
  0xd4a9b87c2c86b5974673824a691d31521db0a50c30,
  0x8b59a4c73d2c876479b6824a691d31521db0a50c30,
  0xc78b59a4d46738c279b6824a691d31521db0a50c30,
  0xc3152879bd46a0a596b8c748673d21d03b50a91c42,
  0xd4a6b597c2831d3769b8c427864a91521db0a50c30,
  0xd4c28b596731d38c79b6a427864a91521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_5 : Region 14 n14a_mask [5,3,3,3,3,3] 36 5 22 none :=
  of_certs (hn:=by decide) [
  0xd4c7682b59a68b973c8742a4691d31521db0a50c30,
  0xd4c7828c2476b6a958b973a4691d31521db0a50c30,
  0xa4d2c876b591a9b8697c4683742d31521db0a50c30,
  0xd4c76a95b82b973868c247a4691d31521db0a50c30,
  0xd4c795b682a9b83768c247a4691d31521db0a50c30,
  0xd4c79b682a95b83768c247a4691d31521db0a50c30,
  0xd4795b68c2a9b876c42837a4691d31521db0a50c30,
  0xd479b68c2a95b876c42837a4691d31521db0a50c30,
  0x8b59a67386b97c428c2d47a4691d31521db0a50c30,
  0xc86b9742a95b876c4d2837a4691d31521db0a50c30,
  0xc28b9731d46a50b69524a05bd21d30c74876a91c83,
  0xd2c4a6b597831d469b8c7376824a91521db0a50c30,
  0xd38795b6a4c27c8b964d1376824a91521db0a50c30,
  0xd4a6b597c83d2c469b873176824a91521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_6 : Region 14 n14a_mask [6,3,3,3,3,3] 36 6 21 none :=
  of_certs (hn:=by decide) [
  0xd4a9b87c2c86974673824a6b591d31521db0a50c30,
  0xd479b8c2c7869a4673824a6b591d31521db0a50c30,
  0xc879a4282d4c768b96473a6b591d31521db0a50c30,
  0xc8764a59bd2130d4796a0d38251b50c42c73a91b86,
  0xa4d2c8376b591c78b9a64796824d31521db0a50c30,
  0xd4a95b6738c2c78b91a64796824d31521db0a50c30,
  0xd4a9b6738c2c78b591a64796824d31521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_7 : Region 14 n14a_mask [7,3,3,3,3,3] 36 7 20 none :=
  of_certs (hn:=by decide) [
  0xa4d2c8376b59178b9a64c796824d31521db0a50c30,
  0xa4d2c786b591c8b9a6746973824d31521db0a50c30,
  0xd4a95b687c2c8b91a6746973824d31521db0a50c30,
  0xd476a9b8c2a4c786b5916973824d31521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_8 : Region 14 n14a_mask [8,3,3,3,3,3] 36 8 19 none :=
  of_certs (hn:=by decide) [
  0xa64d2c78b91c86b5974a9673824d31521db0a50c30,
  0xd4795b68c2c78b91a64a9673824d31521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_9 : Region 14 n14a_mask [9,3,3,3,3,3] 36 9 18 none :=
  of_certs (hn:=by decide) [
  0x8b9a67c428c2d46973a4786b591d31521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_3_13 : Region 14 n14a_mask [13,3,3,3,3,3] 36 13 14 none :=
  of_certs (hn:=by decide) [
  0xdb82c4697315a0d38c74a6b9521876d42a91b50c30] (by rfl)

private theorem n14a_3_3_3_3_3 : Region 14 n14a_mask [3,3,3,3,3] 37 3 27 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14a_3_3_3_3_3_3
  · exact n14a_3_3_3_3_3_4
  · exact n14a_3_3_3_3_3_5
  · exact n14a_3_3_3_3_3_6
  · exact n14a_3_3_3_3_3_7
  · exact n14a_3_3_3_3_3_8
  · exact n14a_3_3_3_3_3_9
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact n14a_3_3_3_3_3_13
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_4 : Region 14 n14a_mask [4,3,3,3,3] 37 4 26 none :=
  of_certs (hn:=by decide) [
  0xa9b876b5968c46d382c742d4a19731521db0a50c30,
  0xa9b86d38c2b695c7648742d4a19731521db0a50c30,
  0xd38b9a67c2b596c8748642d4a19731521db0a50c30,
  0xd38b967c2b59a6c8748642d4a19731521db0a50c30,
  0xc8b9a674c2d387b6958642d4a19731521db0a50c30,
  0xa9b8c76d3874c2b6958642d4a19731521db0a50c30,
  0xc86b521973d4a0c783b950d130db82c42a51a96764,
  0xd38647c2b59a69b8768c42d4a19731521db0a50c30,
  0xd3874c2c8b967b6a958642d4a19731521db0a50c30,
  0xd38b5967c24a1d4c82b9a678649731521db0a50c30,
  0xa9b876c74682d24c83b695d4a19731521db0a50c30,
  0xd38b5967c4a1d2c874b9a686429731521db0a50c30,
  0xd38c76b59a1a478b96d4c286429731521db0a50c30,
  0xd38c76b9a1a478b596d4c286429731521db0a50c30,
  0xa695b8c74d3876b9a1d4c286429731521db0a50c30,
  0xc78b964b59a6d38c286742d4a19731521db0a50c30,
  0xc8b964d387c2b6a9586742d4a19731521db0a50c30,
  0xd386b59a47c29b876a1d468c429731521db0a50c30,
  0xd4c78b596a1a9b674d38c286429731521db0a50c30,
  0xd3876b59a1a4c8b96d47c286429731521db0a50c30,
  0xd38b596a1b9a4c876d47c286429731521db0a50c30,
  0xd4c8b596a1a9b674d387c286429731521db0a50c30,
  0xd4c8b96a1a95b674d387c286429731521db0a50c30,
  0xc8b596a4d476b9a1d387c286429731521db0a50c30,
  0xd4a9b68395b8c76a1d2c4687429731521db0a50c30,
  0xc312d479b86a50b69524a0c764db51c82873a91d30,
  0xd3824c76b59a1d4a69b8c278649731521db0a50c30,
  0xd3876b59a4c2d1a69b8c7468249731521db0a50c30,
  0xd3876b9a4c2d47c8b596a168249731521db0a50c30,
  0x9b8c76b59a6d4783c4682d24a19731521db0a50c30,
  0xd386b59a4c29b876c7428d46a19731521db0a50c30,
  0xd386b9a4c295b876c7428d46a19731521db0a50c30,
  0xd386b9a4295b8c7674c28d46a19731521db0a50c30,
  0xc786b9a48b596742c2d38d46a19731521db0a50c30,
  0xc4a95b6829b8c76742d38d46a19731521db0a50c30,
  0xc86b59a49b82c76742d38d46a19731521db0a50c30,
  0xb8c769586b9a42d2c4783d46a19731521db0a50c30,
  0xc764a59bd12830d4796a052d31c873b50b86a91c42,
  0xd38c2476b59a1c78b96a4d28649731521db0a50c30,
  0xd387c46b59a1d2c8b96a4768249731521db0a50c30,
  0xd4a695b87c2c83d1a9b64768249731521db0a50c30,
  0xa9b68c7495b8763d4c28d246a19731521db0a50c30,
  0xb8c7695a9b68743d4c28d246a19731521db0a50c30,
  0xa59b64c7821d3086a4735b8c31c250db0d42a91976,
  0xd3824c76b59a1a69b874d2c8649731521db0a50c30,
  0xd2c8746b59a1d38b96a4c768249731521db0a50c30,
  0xd2c8746b9a1d38b596a4c768249731521db0a50c30,
  0xd4a695b8c2d38746b9a1c768249731521db0a50c30,
  0xd3876b59a4c27c8b964d1a68249731521db0a50c30,
  0xd3876b9a4c27c8b5964d1a68249731521db0a50c30,
  0xd38b9647c2c876b59a4d1a68249731521db0a50c30,
  0xd4a9b687c2c8b596746a1d38249731521db0a50c30,
  0xc786b59a4d4769b8c26a1d38249731521db0a50c30,
  0xd38c791524a6b0a95bd4c28731b968764d21a50c30,
  0xa6bd378c42591d4a97c28315b0b968764d21a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_5 : Region 14 n14a_mask [5,3,3,3,3] 37 5 25 none :=
  of_certs (hn:=by decide) [
  0x87c42d2c83d4a91a13769746bb8695521db0a50c30,
  0x8b59a67c42b9786c2d38d4691a4731521db0a50c30,
  0x86b597c42a9b876c2d38d4691a4731521db0a50c30,
  0x86b97c42a95b876c2d38d4691a4731521db0a50c30,
  0xc795b682a9b876c42d38d4691a4731521db0a50c30,
  0xb876a95c79b682c42d38d4691a4731521db0a50c30,
  0xa59b64c7821d3086a473c3150c8b52db0d42a91976,
  0xa42d38c76b591c469b82a9786d4731521db0a50c30,
  0xd3824c76b591d469b8c2a9786a4731521db0a50c30,
  0xc795b64d382d19a68c429b876a4731521db0a50c30,
  0xc79a683d42d28c46b5919b876a4731521db0a50c30,
  0xb68c795a9b8763d4c28d24691a4731521db0a50c30,
  0xa4c2d3876b591a97c869b8246d4731521db0a50c30,
  0xc76a95b83d42d19b682978c46a4731521db0a50c30,
  0xd4c76a95b83b91d2c86978246a4731521db0a50c30,
  0xd4c76a9b83b591d2c86978246a4731521db0a50c30,
  0xd4c76a95b8391d2c86b978246a4731521db0a50c30,
  0xd4c7695b83b91d2c86a978246a4731521db0a50c30,
  0xd4c769b83d2c86b591a978246a4731521db0a50c30,
  0xd4c769b83a91d2c86b5978246a4731521db0a50c30,
  0xd315a6b97428c0a46952db830d4c21c73b50a91876,
  0xa4d25b968c731d38b6a974c2187642951db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_6 : Region 14 n14a_mask [6,3,3,3,3] 37 6 24 none :=
  of_certs (hn:=by decide) [
  0xa9b674d4c873c79682d246a1b83195521db0a50c30,
  0xa4d382c76b91a95b86978c46d24731521db0a50c30,
  0xc76b9a4d382a195b86978c46d24731521db0a50c30,
  0xa4d386b591a9b82c76978c46d24731521db0a50c30,
  0xc76a95b82a4d386b91978c46d24731521db0a50c30,
  0xa4d386b591a9b8c769782c46d24731521db0a50c30,
  0xa4d386b91a95b8c769782c46d24731521db0a50c30,
  0xd4697c83c4a9b682a678b591d24731521db0a50c30,
  0xdb96a5137428c0a4c2597830d467c3b86b50a91d21,
  0xa4c2d3876b591d46a9b8c731796824521db0a50c30,
  0xd4a95b67c831d378b91a64c2796824521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_7 : Region 14 n14a_mask [7,3,3,3,3] 37 7 23 none :=
  of_certs (hn:=by decide) [
  0xd2c86b591a4d3876b97c428a964731521db0a50c30,
  0xd4a678c2d386b591b97c428a964731521db0a50c30,
  0xdb96a5137428c0c3d467952a4c7830d21b50a91b86,
  0xa95b6874c2d31d4a67c8b916973824521db0a50c30,
  0xd2c4a678b591a9b68c74d316973824521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_8 : Region 14 n14a_mask [8,3,3,3,3] 37 8 22 none :=
  of_certs (hn:=by decide) [
  0xa4db68213c7950d25b8730c83d19b0c42a51a96764,
  0xa64795b8c2d31d4c786b91a9673824521db0a50c30,
  0xd3795b68c4a1d2c78b9a6476913824521db0a50c30,
  0xd46a95b87c2d379b68c4a176913824521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_9 : Region 14 n14a_mask [9,3,3,3,3] 37 9 21 none :=
  of_certs (hn:=by decide) [
  0xd2c86b5974a1d378b9a64c76913824521db0a50c30,
  0xd4a6b5978c273d1a9b864c76913824521db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_3_10 : Region 14 n14a_mask [10,3,3,3,3] 37 10 20 none :=
  of_certs (hn:=by decide) [
  0xd4c76a9b83d2c87964a1b682473195521db0a50c30] (by rfl)

private theorem n14a_3_3_3_3 : Region 14 n14a_mask [3,3,3,3] 38 3 30 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14a_3_3_3_3_3
  · exact n14a_3_3_3_3_4
  · exact n14a_3_3_3_3_5
  · exact n14a_3_3_3_3_6
  · exact n14a_3_3_3_3_7
  · exact n14a_3_3_3_3_8
  · exact n14a_3_3_3_3_9
  · exact n14a_3_3_3_3_10
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_4_4 : Region 14 n14a_mask [4,4,3,3,3] 37 4 25 none :=
  of_certs (hn:=by decide) [
  0x9b831a6796b59c864d473c782d251a421db0a50c30,
  0xd476a9b83b5968c46c782d2519731a421db0a50c30,
  0xd4769b83b59a68c46c782d2519731a421db0a50c30,
  0xc8b9a64d38674b596c782d2519731a421db0a50c30,
  0xd4c259a6b87318c769746d3829b51a421db0a50c30,
  0xc8b9674b59a683d46c782d2519731a421db0a50c30,
  0xc8b964d47683b59a6c782d2519731a421db0a50c30,
  0xd476a9b8c251c7864b596d3829731a421db0a50c30,
  0xd47c86a9b51c25964b876d3829731a421db0a50c30,
  0xd2c4786951d38c764b9a68b529731a421db0a50c30,
  0xd47c86951c2d38764b9a68b529731a421db0a50c30,
  0x9b8c76b59a6d4783c4682d2519731a421db0a50c30,
  0xd4769b8c251b6a9587c46d3829731a421db0a50c30,
  0xd4c86a9b51967c25b8746d3829731a421db0a50c30,
  0xd4c86a951b967c25b8746d3829731a421db0a50c30,
  0xc86a9b52d4c76951b8746d3829731a421db0a50c30,
  0xd4c86a951b67c259b8746d3829731a421db0a50c30,
  0xd4c86b519a67c259b8746d3829731a421db0a50c30,
  0xc8b9a64c786b52d476951d3829731a421db0a50c30,
  0xdb5a97c8642130b82d1a0a674d4c3c250b96951873,
  0xd382c746a9b51d4c86952b8769731a421db0a50c30,
  0xd382c76a9b51d4c8b695287469731a421db0a50c30,
  0xd28c76a9b51c4d38b695287469731a421db0a50c30,
  0xc8b97b6a95d4783c468296731d251a421db0a50c30,
  0xd3876a9b51b8c46d47c2869529731a421db0a50c30,
  0xd38c46b51a9b876d47c2869529731a421db0a50c30,
  0xd3876b51a9b8c46d47c2869529731a421db0a50c30,
  0xc8b9a674c2d387d46b51869529731a421db0a50c30,
  0xa9b8c76d3874c2d46b51869529731a421db0a50c30,
  0xdb5a97c8642130a1d250c28b0a674d4c3b96951873,
  0xd47c259a6b831d37968278c469b51a421db0a50c30,
  0xd382c76a9b51d4c86952b87469731a421db0a50c30,
  0xd4c286a9b51d38c76952b87469731a421db0a50c30,
  0xd4c86a9b52d382c76951b87469731a421db0a50c30,
  0x86a9b52b8c4767c2d38d469519731a421db0a50c30,
  0xd47c259a6b831d37682978c469b51a421db0a50c30,
  0xd4c2876a9b51d386952b8c7469731a421db0a50c30,
  0xd382c76a951d4c86b529b87469731a421db0a50c30,
  0xd382c76b51d4c86a9529b87469731a421db0a50c30,
  0xd4c876a9b529683d15b82c7469731a421db0a50c30,
  0xd4c86a9b51b83d2c7695287469731a421db0a50c30,
  0xd4c769b83d2c86a951b5287469731a421db0a50c30,
  0xd4c869b51b83d2c76a95287469731a421db0a50c30,
  0xdb96a5137428c0a4d12597830c764d3c2b50a91b86,
  0xd382c746a9b51952d4c8b67319786a421db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_4_5 : Region 14 n14a_mask [5,4,3,3,3] 37 5 24 none :=
  of_certs (hn:=by decide) [
  0xd386a97c278c46b952896b51d4731a421db0a50c30,
  0xd38764c2a97c86b952896b51d4731a421db0a50c30,
  0xa9b8c76d3864c27952896b51d4731a421db0a50c30,
  0xa4d1386b97c250c8764d37425b821a695db0a91c30,
  0xc8b9a647c2d3867952896b51d4731a421db0a50c30,
  0xd38b9a647c251b68795c4d2896731a421db0a50c30,
  0x9a67c2d38b51b978c4695286d4731a421db0a50c30,
  0x97c2d386b518c46a9529b876d4731a421db0a50c30,
  0xd386b597c28c46a91529b876d4731a421db0a50c30,
  0xc8b96486a952d2c783976b51d4731a421db0a50c30,
  0x9a67c2d38b5186b952978c46d4731a421db0a50c30,
  0xd38b59a67c286b9152978c46d4731a421db0a50c30,
  0x9a67c28b51d386b952978c46d4731a421db0a50c30,
  0xc76a95b829b683d251978c46d4731a421db0a50c30,
  0xd38c76b952b86a9159782c46d4731a421db0a50c30,
  0x9a67c8b519b683d259782c46d4731a421db0a50c30,
  0xc8b59a64d38697c29b678251d4731a421db0a50c30,
  0xdb5a97c8642130a674c3d250c28b0d4a1b96951873,
  0xd382c479a6b51952d468c7319b876a421db0a50c30,
  0xd4c25b6837919513d28c746a9b876a421db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_4_6 : Region 14 n14a_mask [6,4,3,3,3] 37 6 23 none :=
  of_certs (hn:=by decide) [
  0xc4d3876b952a97c86b51d28964731a421db0a50c30,
  0xd4c8b6a95183d2c7679b528964731a421db0a50c30,
  0xd4c879b51c2d38b676a9528964731a421db0a50c30,
  0xd386b97c2a95b876c4d1528964731a421db0a50c30,
  0xd4c79b83d2c86b5176a9528964731a421db0a50c30,
  0xdb96a5137428c0a4d3c7950c46b52b830d21a91876,
  0xd4c73825b6a9159768c2d319b8746a421db0a50c30,
  0xd382c79a6b51952d4c867319b8746a421db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_4_7 : Region 14 n14a_mask [7,4,3,3,3] 37 7 22 none :=
  of_certs (hn:=by decide) [
  0xd4c76b8391d2c876a9b5285964731a421db0a50c30,
  0xdb5a97c8642130a1d3c250c4d28b0a674b96951873,
  0x9a6b5287c4d31d2c8679519b83746a421db0a50c30,
  0xd4c7825b6a9159768c2d319b83746a421db0a50c30,
  0xd4c25b68791d28c76a95139b83746a421db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_4_8 : Region 14 n14a_mask [8,4,3,3,3] 37 8 21 none :=
  of_certs (hn:=by decide) [
  0x5b9a682d4c731c8b6795291d38746a421db0a50c30,
  0xd382c79a6b51d4c8769528b913746a421db0a50c30,
  0xd28c79a6b51c4d38769528b913746a421db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_4_9 : Region 14 n14a_mask [9,4,3,3,3] 37 9 20 none :=
  of_certs (hn:=by decide) [
  0xd4c879a6b52c7691d3828b9513746a421db0a50c30,
  0xd38c796b52d4c2876a918b9513746a421db0a50c30] (by rfl)

private theorem n14a_3_3_3_4 : Region 14 n14a_mask [4,3,3,3] 38 4 29 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14a_3_3_3_4_4
  · exact n14a_3_3_3_4_5
  · exact n14a_3_3_3_4_6
  · exact n14a_3_3_3_4_7
  · exact n14a_3_3_3_4_8
  · exact n14a_3_3_3_4_9
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_5 : Region 14 n14a_mask [5,3,3,3] 38 5 28 none :=
  of_certs (hn:=by decide) [
  0xd4c76b51a9b86d38c287952a473196421db0a50c30,
  0xd386b51a9b876c4d28c7952a473196421db0a50c30,
  0xd386b9a47c251b8795c4d28a673196421db0a50c30,
  0xc8b9a4867952d2c783a6b51d473196421db0a50c30,
  0xd38b9a67c251b68795c4d28a473196421db0a50c30,
  0xd4c879a6b5183d2c76b9528a473196421db0a50c30,
  0xd4c86a9b51b83d2c7679528a473196421db0a50c30,
  0xd4c79a683d2c876b51b9528a473196421db0a50c30,
  0xc4d3876b952a97c86b51d28a473196421db0a50c30,
  0xd4c8b6a95183d2c7679b528a473196421db0a50c30,
  0xd4c879b51c2d38b676a9528a473196421db0a50c30,
  0xd386b97c2a95b876c4d1528a473196421db0a50c30,
  0xd4c79b83d2c86b5176a9528a473196421db0a50c30,
  0xdb96a5137428c0c46b87952c7683a4d30b50a91d21,
  0xa4c8679b52d31d478b6a951c283796421db0a50c30,
  0xd25976b8c4a15b9a6874d31c283796421db0a50c30,
  0xd2c478b9a1d386a4c795285b673196421db0a50c30,
  0xd38b9a4c2d1a6874c795285b673196421db0a50c30,
  0xd386a4c2d478b9a1c795285b673196421db0a50c30,
  0xd4a687c2b9a1d38c4795285b673196421db0a50c30,
  0xdb5a97c8642130a4c3d250d476a1c28b0b96951873,
  0xd38c259b674a1d4c79a6828b513796421db0a50c30,
  0xd386b597c4a1d2c8b9a67482513796421db0a50c30,
  0xd4c76a95b83d2c86b974a182513796421db0a50c30,
  0xc79b682d25b8c4d3876a159a473196421db0a50c30,
  0xdb96a5137428c0d467952d387c21a4c30b50a91b86,
  0xd386b52c479a1d4a67c828b9513796421db0a50c30,
  0xd38795b6a4c2d1a9b8c74682513796421db0a50c30,
  0xd4a6b597c83c2d1a9b874682513796421db0a50c30,
  0xd3876b59a4c2d1a68c749b82513796421db0a50c30,
  0xd4a95b687c2c83d1a6749b82513796421db0a50c30,
  0xd4a9b687c2d38b5976a14c82513796421db0a50c30,
  0xd4c876b9a1c2d38b5974a682513796421db0a50c30,
  0xd1382c4796b5a0b8c73d246a1950db9a4876521c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_6 : Region 14 n14a_mask [6,3,3,3] 38 6 27 none :=
  of_certs (hn:=by decide) [
  0xd4a9b87c2c869745b6a19d38251376421db0a50c30,
  0xd479b8c2c7869a45b6a19d38251376421db0a50c30,
  0xd4a9683c478b52d28c791a6b951376421db0a50c30,
  0xdb5a97c8642130b82c4a0d476a1c3d250b96951873,
  0xa4c2d38796b51d47c8b916a9528376421db0a50c30,
  0xd38795b6a4c2d1a9b8c74691528376421db0a50c30,
  0xd4a6b597c83c2d1a9b874691528376421db0a50c30,
  0xa47c2d3869b51d4c8791b6a9528376421db0a50c30,
  0xd2c4786b59a1d38b96a4c791528376421db0a50c30,
  0xd38b596a4c2d1a9b6874c791528376421db0a50c30,
  0xd386b9a4c2d478b596a1c791528376421db0a50c30,
  0xd4a695b87c2b9a1d386c4791528376421db0a50c30,
  0xd4a69b87c2b59a1d386c4791528376421db0a50c30,
  0xc786b59a4d2c8b96a1d47915283376421db0a50c30,
  0xd387c24a6915b0a9528c4db673179b864d21a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_7 : Region 14 n14a_mask [7,3,3,3] 38 7 26 none :=
  of_certs (hn:=by decide) [
  0x9b6a4d2c7831c8b597469a1528d376421db0a50c30,
  0xd4a695b87c2c831a9746b91528d376421db0a50c30,
  0xd4a95b87c2c831a69746b91528d376421db0a50c30,
  0xd4a69b87c2b59a1386c4791528d376421db0a50c30,
  0xc786b59a4974d2c831b96a1528d376421db0a50c30,
  0xa4c7386bd21950c879b524d130d3c28b0a51a96764,
  0xa9b67c4d38251d2c8b596a47319786421db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_8 : Region 14 n14a_mask [8,3,3,3] 38 8 25 none :=
  of_certs (hn:=by decide) [
  0xd4c795b82c869a152b6a47319d3876421db0a50c30,
  0xc379b821d46a508674c2db513b69524a0c87a91d30,
  0xa4d382c796b51d259a68c47319b876421db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_9 : Region 14 n14a_mask [9,3,3,3] 38 9 24 none :=
  of_certs (hn:=by decide) [
  0xdb5a97c8642130a674d3c250c4a1d28b0b96951873,
  0xa95b6874c2d31d4a697c82519b8376421db0a50c30,
  0xd2c4786b59a1d4a697c825139b8376421db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_10 : Region 14 n14a_mask [10,3,3,3] 38 10 23 none :=
  of_certs (hn:=by decide) [
  0x52c786b9a4d31d28c4796a195b8376421db0a50c30,
  0xd4a9b687c251a6974c82d3195b8376421db0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_3_11 : Region 14 n14a_mask [11,3,3,3] 38 11 22 none :=
  of_certs (hn:=by decide) [
  0xd2c4786b9a1d4a679152837c8b5964213db0a50c30] (by rfl)

private theorem n14a_3_3_3 : Region 14 n14a_mask [3,3,3] 39 3 33 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14a_3_3_3_3
  · exact n14a_3_3_3_4
  · exact n14a_3_3_3_5
  · exact n14a_3_3_3_6
  · exact n14a_3_3_3_7
  · exact n14a_3_3_3_8
  · exact n14a_3_3_3_9
  · exact n14a_3_3_3_10
  · exact n14a_3_3_3_11
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_4_4 : Region 14 n14a_mask [4,4,3,3] 38 4 28 none :=
  of_certs (hn:=by decide) [
  0xd4c282478c76a469b6a5db839731d1a0b950521c30,
  0xd476a9b0b5968c46db83c782d2519731a421a50c30,
  0xd4769b0b59a68c46db83c782d2519731a421a50c30,
  0xc86952d478b0b9a6c764d382db519731a421a50c30,
  0xd38c476a95b09b86bd46c782d2519731a421a50c30,
  0xd469b0b59a68c476db83c782d2519731a421a50c30,
  0xd38c476a9b095b86bd46c782d2519731a421a50c30,
  0xd38c4769b0a95b86bd46c782d2519731a421a50c30,
  0xd386a95b09b8c476bd46c782d2519731a421a50c30,
  0xc8b9a674d38695b0bd46c782d2519731a421a50c30,
  0xdb96468c47b6a95d38b0c782d2519731a421a50c30,
  0xdb9a674c8395b86b0d46c782d2519731a421a50c30,
  0xd386a95b09bd476b8c46c782d2519731a421a50c30,
  0xdb59a6839b0d476b8c46c782d2519731a421a50c30,
  0xdb59a683b0d4769b8c46c782d2519731a421a50c30,
  0xdb9a683d4695b0b8c476c782d2519731a421a50c30,
  0xd13746a952c8b0db67c49786d3829b51a421a50c30,
  0xd382c746a95b0db968c4b876d2519731a421a50c30,
  0xd47c286a95b0c83db964b876d2519731a421a50c30,
  0xd47c286a9b0c83db5964b876d2519731a421a50c30,
  0xc74db9a682d38c4695b0b876d2519731a421a50c30,
  0xdb9a67c8395b8674c28d46b0d2519731a421a50c30,
  0xdb59a6839b8c7674c28d46b0d2519731a421a50c30,
  0xa9b8c76db5968374c28d46b0d2519731a421a50c30,
  0xd13874c259a6b097c8673d46db829b51a421a50c30,
  0xdb67c83a95b869b0d46c4782d2519731a421a50c30,
  0xd382c746a95b0db68c49b876d2519731a421a50c30,
  0xd382c76a95b09bd4c86b8746d2519731a421a50c30,
  0xd4c286a95b09bd38c76b8746d2519731a421a50c30,
  0xd4c86a95b09bd382c76b8746d2519731a421a50c30,
  0xc8b96486a952d2c783d476b0db519731a421a50c30,
  0xd382c76a95b0bd4c869b8746d2519731a421a50c30,
  0xd4c286a95b0bd38c769b8746d2519731a421a50c30,
  0xd4c86a95b0bd382c769b8746d2519731a421a50c30,
  0xdb59a68c4d382c76b09b8746d2519731a421a50c30,
  0xd4c86a95b09b82c76bd38746d2519731a421a50c30,
  0xd4c86a9b095b82c76bd38746d2519731a421a50c30,
  0x7c8b9a64c4db6782d38695b0d2519731a421a50c30,
  0xd4c8251379a6b0d38b5967c28746db91a421a50c30,
  0xd2c476a9138b08c73d46b9529786db51a421a50c30,
  0xc74d38b6a952d28c467319b09786db51a421a50c30,
  0xdb9a6783b8c46d47c286952d15b09731a421a50c30,
  0xc8b9a64bd3876d47c286952d15b09731a421a50c30,
  0xd15287c46a9b0b8695bd476d38c29731a421a50c30,
  0xa9b876d47c83db64c286952d15b09731a421a50c30,
  0xc74d38b6a952db968278c46d15b09731a421a50c30,
  0x83d4c76a952db968c2b8746d15b09731a421a50c30,
  0xc76a9bd382d4c86952b8746d15b09731a421a50c30,
  0xd4c86a952db967c283b8746d15b09731a421a50c30,
  0x83d4c76a952db68c29b8746d15b09731a421a50c30,
  0xc83db6a952d4c76829b8746d15b09731a421a50c30,
  0xd4c86a952c76bd3829b8746d15b09731a421a50c30,
  0xc4d386952a9b8c76bd28746d15b09731a421a50c30,
  0xdb9a68c4d38b67c29528746d15b09731a421a50c30,
  0xd4c286a97315b0d38c76952b8746db91a421a50c30,
  0xd3874c259a6b0d15b967c828bd469731a421a50c30,
  0xd28c476a9b51c783d0b69528bd469731a421a50c30,
  0xdb59a687c29b8c463d1528d476b09731a421a50c30,
  0xdb59a68c29b87c463d1528d476b09731a421a50c30,
  0xc8b59a64db9687c23d1528d476b09731a421a50c30,
  0xd2c78b516a9bd38c469528d476b09731a421a50c30,
  0xd1374c259a68b0db697c83782d469b51a421a50c30,
  0xd152c4786a9b0bd38c7695b82d469731a421a50c30,
  0xd28c476a9b51c783db69528b0d469731a421a50c30,
  0xc783db6a952d28c4769b518b0d469731a421a50c30,
  0xc8b9a64db687c2d476951d3825b09731a421a50c30,
  0xd1374c259a68b0db67c839782d469b51a421a50c30,
  0xd3874c259a6b0db967c828b51d469731a421a50c30,
  0xd38b9a67c251b0d4c8695bd287469731a421a50c30,
  0xc4d386a9b52967c8b0d15bd287469731a421a50c30,
  0xd38b9a67c251bd4c8695b0d287469731a421a50c30,
  0xc4d386a9b52967c8bd15b0d287469731a421a50c30,
  0xd4c7695b83db9a68c251b0d287469731a421a50c30,
  0xd4c86a95b09b83d2c76bd15287469731a421a50c30,
  0xb67c4d382591a0db8c24a6973150b9a57864d21c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_4_5 : Region 14 n14a_mask [5,4,3,3] 38 5 27 none :=
  of_certs (hn:=by decide) [
  0xdb9a683b8c46d47c28795296731d15b0a421a50c30,
  0xd47c83db64c2a9b868795296731d15b0a421a50c30,
  0xc4783db6a952c8b9764d2896731d15b0a421a50c30,
  0xd38b9a647c2db68c47952896731d15b0a421a50c30,
  0xd38b9a64c2db68c747952896731d15b0a421a50c30,
  0xdb9a68c74c2d38b647952896731d15b0a421a50c30,
  0xdb9a6874c2d38b64c7952896731d15b0a421a50c30,
  0xd46b97c83c2db8746a952896731d15b0a421a50c30,
  0xdb9a6874d38b64c2c7952896731d15b0a421a50c30,
  0xd46b87c2a9bd386c47952896731d15b0a421a50c30,
  0xdb5a97c8642130a674c250d3782c38b0d4a1b96951,
  0x59a6bd4c28731d38c746918b976d25b0a421a50c30,
  0x952db68c4731c79a64d3829b876d15b0a421a50c30,
  0x83db64c79529a68c2d47319b876d15b0a421a50c30,
  0xdb68c7952a9b8763d4c28964731d15b0a421a50c30,
  0xd4c79b838c2db676a9528964731d15b0a421a50c30,
  0xdb978c48b6a952d2c7683964731d15b0a421a50c30,
  0xdb5a97c8642130a478250d376a1c38b0d4c2b96951,
  0x59a6bd4c28731d38c76918b9746d25b0a421a50c30,
  0x9528c4db6731d386a97c29b8746d15b0a421a50c30,
  0x9a67c4d2831c86bd379529b8746d15b0a421a50c30,
  0x59a6bd4c28731d3867919b8c746d25b0a421a50c30,
  0x9528c4db6731d38697c2a9b8746d15b0a421a50c30,
  0x9a6782c4d31db68c79529b83746d15b0a421a50c30,
  0xc4db6879529a67c82d319b83746d15b0a421a50c30,
  0xc4d3876a952db697c828b913746d15b0a421a50c30,
  0xc79a6bd382d4c8769528b913746d15b0a421a50c30,
  0xdb6a978c4d38b967c2952864731d15b0a421a50c30,
  0xd3825197c4a6b0a95bd2c8647319b876d421a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_4_6 : Region 14 n14a_mask [6,4,3,3] 38 6 26 none :=
  of_certs (hn:=by decide) [
  0xdb9a68c2b87c46379528d47691d315b0a421a50c30,
  0xc8b9a64db687c2379528d47691d315b0a421a50c30,
  0xdb5a97c8642130d376a1b874a0c38250d4c2b96951,
  0x528c4db6a9731d3867c29b8746d195b0a421a50c30,
  0x837c4db6a952d19768c29b8746d315b0a421a50c30,
  0xd4c28376a91db68c79529b8746d315b0a421a50c30,
  0xdb6a9738c2d4c76825919b8746d315b0a421a50c30,
  0xc8374db6a952d1976829b87c46d315b0a421a50c30,
  0x87c4db6a952d19768c29b83746d315b0a421a50c30,
  0xd4c2876a91db68c79529b83746d315b0a421a50c30,
  0xd4c78b6a918c2db97695283746d315b0a421a50c30,
  0xdb9a687c4d2c8b679195283746d315b0a421a50c30,
  0xd3825197c4a6b0a95bd2c867319b8746d421a50c30,
  0xa4c76bd382591d2c86a97315b09b8746d421a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_4_7 : Region 14 n14a_mask [7,4,3,3] 38 7 25 none :=
  of_certs (hn:=by decide) [
  0x9a68c2d4731db679519b87c46d3825b0a421a50c30,
  0xd4c78b6a918c2db9769513746d3825b0a421a50c30,
  0xdb9a687c4d2c8b67919513746d3825b0a421a50c30,
  0xd4c78b6918c2db976a9513746d3825b0a421a50c30,
  0xd382c476a915b0d259b68c731978bd46a421a50c30,
  0xd382c76a915b0d259b68c4731978bd46a421a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_4_8 : Region 14 n14a_mask [8,4,3,3] 38 8 24 none :=
  of_certs (hn:=by decide) [
  0xdb6a9783c768b952d28c4691d47315b0a421a50c30,
  0xd4c251379a68b0d38c76b5919bd28746a421a50c30,
  0xd376a9152c8b0d4c795b68319bd28746a421a50c30,
  0xd4c25976b831d37c86a915b09bd28746a421a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_4_9 : Region 14 n14a_mask [9,4,3,3] 38 9 23 none :=
  of_certs (hn:=by decide) [
  0xd4c2513879a6b0db5967c828b91d3746a421a50c30,
  0xd319a687c25b0d4c8b679519bd283746a421a50c30,
  0xd4c25b876a91597c86b0d319bd283746a421a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_4_10 : Region 14 n14a_mask [10,4,3,3] 38 10 22 none :=
  of_certs (hn:=by decide) [
  0xc4d3879a6b52967c8b0d1582db913746a421a50c30,
  0xd38b697c251d4c876a95b082db913746a421a50c30] (by rfl)

private theorem n14a_3_3_4 : Region 14 n14a_mask [4,3,3] 39 4 32 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14a_3_3_4_4
  · exact n14a_3_3_4_5
  · exact n14a_3_3_4_6
  · exact n14a_3_3_4_7
  · exact n14a_3_3_4_8
  · exact n14a_3_3_4_9
  · exact n14a_3_3_4_10
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_5 : Region 14 n14a_mask [5,3,3] 39 5 31 none :=
  of_certs (hn:=by decide) [
  0xdb67c4a9b86d38c287952a473196421d15b0a50c30,
  0xc783db6a9528b976c4d28a473196421d15b0a50c30,
  0xd4c76a9b83bd2c8679528a473196421d15b0a50c30,
  0xd4c79a683bd2c876b9528a473196421d15b0a50c30,
  0xdb9a68c4d38b67c279528a473196421d15b0a50c30,
  0xdb68c7952a9b8763d4c28a473196421d15b0a50c30,
  0xd4c79b838c2db676a9528a473196421d15b0a50c30,
  0xdb978c48b6a952d2c7683a473196421d15b0a50c30,
  0xdb96a5137428c0b64c250c7683b87954a03da91d21,
  0xa4c8b67952d31db9a6874c283796421d15b0a50c30,
  0xa4768b952d31db6a978c4c283796421d15b0a50c30,
  0xdb6a4c87952d31a9b8674c283796421d15b0a50c30,
  0xdb9a4c83b67c28d47952a6873196421d15b0a50c30,
  0xdb67c83d4a9b82c47952a6873196421d15b0a50c30,
  0xdb5a97c8642130d376a1a4c250d4782c38b0b96951,
  0xa4c259786bd31a9b8c764d283796421d15b0a50c30,
  0xc83db674a952d4c79b8286a13796421d15b0a50c30,
  0xc76b9a4d382db8c4795286a13796421d15b0a50c30,
  0xd4c8b67952db9a47c28386a13796421d15b0a50c30,
  0xc74d38b6a952db976828c4a13796421d15b0a50c30,
  0xd3876b9a4c28bd47952c86a13796421d15b0a50c30,
  0xd38b9a67c286bd479528c4a13796421d15b0a50c30,
  0xdb8c76a952b974d38682c4a13796421d15b0a50c30,
  0xdb9a68c74d38b6795282c4a13796421d15b0a50c30,
  0xc3786b951d24a0d382c791a5b052130db8c4a96764,
  0xa4c769b83d251db59a68c2473197821d46b0a50c30,
  0xdb9a4c2d38c748b6952a68791376421d15b0a50c30,
  0xa6b83d47c2591c879a469bd28376421d15b0a50c30,
  0xa47c2d38b691db978c46a9528376421d15b0a50c30,
  0xa6874c2db91d38c79a4b69528376421d15b0a50c30,
  0xa683d4c791a9bd2c874b69528376421d15b0a50c30,
  0xd38b69a47c2db978c46a19528376421d15b0a50c30,
  0xdb69a4c783d2c8b9746a19528376421d15b0a50c30,
  0xdb6974c83d4a9b87c26a19528376421d15b0a50c30,
  0xd4c796b83a9bd2c8674a19528376421d15b0a50c30,
  0xdb5a97c8642130b82c3d4a150c476a0d2591b96873,
  0xa4d259b67c8319a68bd374c21879642d15b0a50c30,
  0xc74db6a952d379b8268c4a193876421d15b0a50c30,
  0xd479a6b829bd37c8652c4a193876421d15b0a50c30,
  0xdb968c74d379a4c2a6b825913876421d15b0a50c30,
  0xdb5a97c8642130c3d476a150b82c4a0d2591b96873,
  0xa952d4c8b6731c79bd386a428746912d15b0a50c30,
  0xd38b6a4c7952a9bd42c867318746912d15b0a50c30,
  0xdb5a97c8642130b82c4a150c3d476a0d2591b96873,
  0xa46b8c73d2591c4db9a678247968312d15b0a50c30,
  0xa64d37c28b91db678c4a95247968312d15b0a50c30,
  0xa6bd387c42591d4a9768c28b9647312d15b0a50c30,
  0xa6783d4c2591db68c79a428b9647312d15b0a50c30,
  0xc83db679a42a687c4d25918b9647312d15b0a50c30,
  0xa6bd4c28791d38c769a4259b8647312d15b0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_6 : Region 14 n14a_mask [6,3,3] 39 6 30 none :=
  of_certs (hn:=by decide) [
  0xa68c74db69a178b913c4d382976425d215b0a50c30,
  0xd38b952c76a1bd4c8679a428964731d215b0a50c30,
  0xd3867c259a19bd4c87b6a428964731d215b0a50c30,
  0xdb68c259a1b97c4d3876a428964731d215b0a50c30,
  0xd4c79b683db8c259a176a428964731d215b0a50c30,
  0xc4db687952a9b8c763d1a428964731d215b0a50c30,
  0xdb86a97c4b952c8763d1a428964731d215b0a50c30,
  0xd4c79b83c876a952db6824a1964731d215b0a50c30,
  0xdb5a97c8642130c4a1d38250d473c2b876a0b96951,
  0xa46bd387c2591d4c8b9a6731796824d215b0a50c30,
  0xa673d4c28b9196bd138c7425a97864d215b0a50c30,
  0xdb6a978c49b82c7683d1a469524731d215b0a50c30,
  0xdb9678c4c79a6b8283d1a469524731d215b0a50c30,
  0xdb5a97c8642130b82d4a150d3c2591c476a0b96873,
  0xa678b952c4d31db68c74a916973824d215b0a50c30,
  0xa46bd382c791d4c8b9a67317869524d215b0a50c30,
  0xdb5a97c8642130c2d478b0a6738250d3c4a1b96951,
  0xd3786b952c4a1db8c79a6476913824d215b0a50c30,
  0xd382c79b64a19a68bd4731c8769524d215b0a50c30,
  0xa9b8c764d31c4a6bd1978273869524d215b0a50c30,
  0xd382c476b9a1db8c796a4687319524d215b0a50c30,
  0xc79b6a4d382c8bd1a9674687319524d215b0a50c30,
  0xc4d379b682db8c74a6919a13876425d215b0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_7 : Region 14 n14a_mask [7,3,3] 39 7 29 none :=
  of_certs (hn:=by decide) [
  0xc79b86a4bd2c8763d19528a964731d4215b0a50c30,
  0xdb5a97c8642130c476a150d3c2591b82d4a0b96873,
  0xa4c795286bd31d2c876a919b83746d4215b0a50c30,
  0xdb687952c4a19a67c82d319b83746d4215b0a50c30,
  0xdb687c259a1d28c4a679139b83746d4215b0a50c30,
  0xa4c795286bd31d2c87691a9b83746d4215b0a50c30,
  0xc4a6bd387952d1a967c828b913746d4215b0a50c30,
  0xdb69782c4a1d38c76a9528b913746d4215b0a50c30,
  0xd38b697c4a1a9bd2c876825913746d4215b0a50c30,
  0xd38b6a97c2db9678c4a1825913746d4215b0a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_8 : Region 14 n14a_mask [8,3,3] 39 8 28 none :=
  of_certs (hn:=by decide) [
  0xd2c4a96b8731db97c86476a19524d38215b0a50c30,
  0xd2c478b69a1db97c86a467319524d38215b0a50c30,
  0xd479a6b8c2db9687c4a167319524d38215b0a50c30,
  0xd47c8b69a1c2db97864a67319524d38215b0a50c30,
  0xd1382c4769b5a0b68c73d24a1950db879a64521c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_9 : Region 14 n14a_mask [9,3,3] 39 9 27 none :=
  of_certs (hn:=by decide) [
  0xd4a9b6782db8c796a1864c25913d374215b0a50c30,
  0xd382519a4c76b0a695b8c2d4731db9786421a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_10 : Region 14 n14a_mask [10,3,3] 39 10 26 none :=
  of_certs (hn:=by decide) [
  0xd4c731a96825b0d2c8b6a479519bd3876421a50c30,
  0x59a6b8c2d4731d1a4c796825b09bd3876421a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_11 : Region 14 n14a_mask [11,3,3] 39 11 25 none :=
  of_certs (hn:=by decide) [
  0xd4c7315286a9b0d2c8b6974a195bd3876421a50c30,
  0xd2c8b596a4731a97c4db682519b0d3876421a50c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_3_12 : Region 14 n14a_mask [12,3,3] 39 12 24 none :=
  of_certs (hn:=by decide) [
  0xd47c8259b6a1768bd2c4a913d387964215b0a50c30] (by rfl)

private theorem n14a_3_3 : Region 14 n14a_mask [3,3] 40 3 36 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14a_3_3_3
  · exact n14a_3_3_4
  · exact n14a_3_3_5
  · exact n14a_3_3_6
  · exact n14a_3_3_7
  · exact n14a_3_3_8
  · exact n14a_3_3_9
  · exact n14a_3_3_10
  · exact n14a_3_3_11
  · exact n14a_3_3_12
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_4_4_4 : Region 14 n14a_mask [4,4,4,3] 38 4 27 none :=
  of_certs (hn:=by decide) [
  0xd25a9b0b695a674c864db83c7829731d421a150c30,
  0xa9b67483d0ba695c864c782db529731d421a150c30,
  0xd382c74a9b08b67a695c864db529731d421a150c30,
  0xa6b95a9674d38b0c864c782db529731d421a150c30,
  0xd2c874a9b06bd38a695c7648b529731d421a150c30,
  0xdb9a478c26b0d38a695c7648b529731d421a150c30,
  0xdb9a4783c2d0b68a695c7648b529731d421a150c30,
  0xd2c76a9b0bd38695a46c8748b529731d421a150c30,
  0xd386a9b0bd2c7695a46c8748b529731d421a150c30,
  0xdb9a683d2c76b095a46c8748b529731d421a150c30,
  0xd2c4783195a6b0db973c867a9648b52d421a150c30,
  0xc8b9a64b0d38695a476c782db529731d421a150c30,
  0xd382c74a596b0a9b8768c46db529731d421a150c30,
  0xd2c4786a59b0bd38c769a468b529731d421a150c30,
  0xd38c4a596b0a9bd2c7687468b529731d421a150c30,
  0xdb695a4c83a9b0d2c7687468b529731d421a150c30,
  0xc4a96782b95a68c746d38b0db529731d421a150c30,
  0xa968c74c28764b95a6d38b0db529731d421a150c30,
  0xd382c74a596b0a9b8678c46db529731d421a150c30,
  0xc876a4c74682d259b0b69a5db839731d421a150c30,
  0xd387c46a59b0bd2c869a4768b529731d421a150c30,
  0xd2c4786a9b0bd38c7695a468b529731d421a150c30,
  0xd2c4a596b0a9bd38768c7468b529731d421a150c30,
  0xdb95a6783d2c4a96b08c7468b529731d421a150c30,
  0xd38c76a59b09a4786bd2c468b529731d421a150c30,
  0xd38c76a9b095a4786bd2c468b529731d421a150c30,
  0xd3876a9b095a47c86bd2c468b529731d421a150c30,
  0xd2c86a9b095a4c76bd387468b529731d421a150c30,
  0xc87695a4d386a9b0bd2c7468b529731d421a150c30,
  0xd2c4a5913876b0db9a68c7397468b52d421a150c30,
  0xd382c746a95b0db968c4a52b8769731d421a150c30,
  0xd28c7469a5b0c4a683db952b8769731d421a150c30,
  0xdb9a683b8c7695a46c4782d25b09731d421a150c30,
  0xdb9683c74a52b6a95c8764d28b09731d421a150c30,
  0xc74a596bd382a9b8678c46d25b09731d421a150c30,
  0xc76a59bd3829a4c86b8746d25b09731d421a150c30,
  0xdb95a67c839a4c286b8746d25b09731d421a150c30,
  0xdb9a67c8395a4c286b8746d25b09731d421a150c30,
  0xdb695a4c83a9b87682c746d25b09731d421a150c30,
  0xdb69a4c83a59b87682c746d25b09731d421a150c30,
  0xc8b695a4db9a678382c746d25b09731d421a150c30,
  0xc4a59682a9b8c76bd38746d25b09731d421a150c30,
  0xd2c4a5913876b0db968c73a97468b52d421a150c30,
  0xd3825a4c769b0db59a68c2b87469731d421a150c30,
  0xd382c76a95b0db968c4a52b87469731d421a150c30,
  0xc7683db9a52d28c4a695b0b87469731d421a150c30,
  0xdb9a67c838b5a47c46952d286b09731d421a150c30,
  0xdb9a6783c8b5a47c46952d286b09731d421a150c30,
  0xc8b5a64db96783c74a952d286b09731d421a150c30,
  0xd2c83195a476b0db96873a97c468b52d421a150c30,
  0xd38259a4c76b0db5a68c29b87469731d421a150c30,
  0xd382c76a95b0db68c4a529b87469731d421a150c30,
  0xd382c76a5b0db68c4a9529b87469731d421a150c30,
  0xd38259a4c76b0db968c2a5b87469731d421a150c30,
  0xd3867c4a95b0a69b8c25bd287469731d421a150c30,
  0xd2c4a5968b0a9bd38c76b5287469731d421a150c30,
  0xdb95a67c83d2c4a968b0b5287469731d421a150c30,
  0xd38c769a5b0a4c2db86b95287469731d421a150c30,
  0xd2c4a968b0a5bd38c76b95287469731d421a150c30,
  0xdb6a47c83c468b9a52d287695b09731d421a150c30,
  0xd4c25a687319b0d38c76b59a4217964db82a150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_4_4_5 : Region 14 n14a_mask [5,4,4,3] 38 5 26 none :=
  of_certs (hn:=by decide) [
  0xdb8c7395a6ba9764c478296831d25b0d421a150c30,
  0xdb64a597c83a9b8674c2896731d25b0d421a150c30,
  0xdb6a597c838b9a4764c2896731d25b0d421a150c30,
  0xdb6a97c838b95a4764c2896731d25b0d421a150c30,
  0xa6b8c795db9a478364c2896731d25b0d421a150c30,
  0xdb9a47c8395a687b64c2896731d25b0d421a150c30,
  0xdb9a4783c86a597b64c2896731d25b0d421a150c30,
  0xc8b95a4db64783c79a68296731d25b0d421a150c30,
  0xd2c8319746a5b0c78b9a46bd3786952d421a150c30,
  0x95a47c286bd318c46a9739b876d25b0d421a150c30,
  0xc4795a6bd3827c864a9139b876d25b0d421a150c30,
  0xc479a6bd3827c864a59139b876d25b0d421a150c30,
  0xdb9a4c83795a68b67c28964731d25b0d421a150c30,
  0xc8795a4db9a683b67c28964731d25b0d421a150c30,
  0xd2c4678319a5b0a6b974c8bd3786952d421a150c30,
  0x95a47c286bd318b9a673978c46d25b0d421a150c30,
  0xc4a5973db6828c76a9139b8746d25b0d421a150c30,
  0xc4a973db6828c76a59139b8746d25b0d421a150c30,
  0xdb6a597c839a4c2867319b8746d25b0d421a150c30,
  0x95a4c876bd31a97c2869b83746d25b0d421a150c30,
  0x9a4c876bd31a597c2869b83746d25b0d421a150c30,
  0xc73db9a682b8c4a59769138746d25b0d421a150c30,
  0xdb6a597c839a4c28768b913746d25b0d421a150c30,
  0xdb6a97c83c4a5967828b913746d25b0d421a150c30,
  0xd2c7468319a5b08c4a6bd379529b876d421a150c30,
  0x95a47c2db6831d379a64c825b09b876d421a150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_4_4_6 : Region 14 n14a_mask [6,4,4,3] 38 6 25 none :=
  of_certs (hn:=by decide) [
  0xc86a974a5b964db87c2952831d376b0d421a150c30,
  0x96a5bd2c47831a9b864c79528d376b0d421a150c30,
  0x9a5bd2c46831a69b874c79528d376b0d421a150c30,
  0xdb5a47968c2c78b9a64319528d376b0d421a150c30,
  0xdb96a478c2c79a5b864319528d376b0d421a150c30,
  0x9bd2c4a6831c79a5b87469528d376b0d421a150c30,
  0x9a5bd2c831b97c4a687469528d376b0d421a150c30,
  0xdb86a97c29b5a4c8317469528d376b0d421a150c30,
  0xdb879a4c26a5b9138c7469528d376b0d421a150c30,
  0xd286a4c73195b0c83db679a529b8746d421a150c30,
  0xd2c768319a5b08c4a6bd379529b8746d421a150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_4_4_7 : Region 14 n14a_mask [7,4,4,3] 38 7 24 none :=
  of_certs (hn:=by decide) [
  0xdb86a597c29a4c876b913746d3825b0d421a150c30,
  0xc78b695a48c2db976a913746d3825b0d421a150c30,
  0xc87695a4db6a97c29b864731d3825b0d421a150c30,
  0xd3195287c4a6b0db5a9768c29b83746d421a150c30,
  0xd3197c286a5b0db678c4a9529b83746d421a150c30,
  0x9a52c786bd31d28c4a6795b09b83746d421a150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_4_4_8 : Region 14 n14a_mask [8,4,4,3] 38 8 23 none :=
  of_certs (hn:=by decide) [
  0xd3197c4a5286b0db9a678c295b83746d421a150c30,
  0xd387952c4a6b0db5a967c828b913746d421a150c30,
  0xd382c769a5b0db6a4c879528b913746d421a150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_4_4_9 : Region 14 n14a_mask [9,4,4,3] 38 9 22 none :=
  of_certs (hn:=by decide) [
  0xd3825a4c796b0db9a678c28b5913746d421a150c30,
  0xd25a4c8769b0c79a6bd3828b5913746d421a150c30,
  0xc783db96a52d28c4a976b08b5913746d421a150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_4_4_10 : Region 14 n14a_mask [10,4,4,3] 38 10 21 none :=
  of_certs (hn:=by decide) [
  0xdb5a4c79683a9b0d2c876b825913746d421a150c30] (by rfl)

private theorem n14a_3_4_4 : Region 14 n14a_mask [4,4,3] 39 4 31 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14a_3_4_4_4
  · exact n14a_3_4_4_5
  · exact n14a_3_4_4_6
  · exact n14a_3_4_4_7
  · exact n14a_3_4_4_8
  · exact n14a_3_4_4_9
  · exact n14a_3_4_4_10
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_4_5 : Region 14 n14a_mask [5,4,3] 39 5 30 none :=
  of_certs (hn:=by decide) [
  0x8c742d4c21db913b83769786aa4695d25b0a150c30,
  0xc4a59bd382c76b879a68d473196421d25b0a150c30,
  0xdb95a4c83b6a97867c28d473196421d25b0a150c30,
  0xdb9a4c83b6a597867c28d473196421d25b0a150c30,
  0xdb9a4c83795a68b67c28d473196421d25b0a150c30,
  0xc8795a4db9a683b67c28d473196421d25b0a150c30,
  0xdb5a97c8642130c3d2508b673c4782b96a0d4a1951,
  0xd4a59b67c2831c86a9748bd3796421d25b0a150c30,
  0xd4a9b67c2831c86a59748bd3796421d25b0a150c30,
  0xd4a9b67c831c286a59748bd3796421d25b0a150c30,
  0xdb6a597c83d4a9b8673182c4796421d25b0a150c30,
  0xa68c7958b9a473d4c28db673196421d25b0a150c30,
  0xdb682c4a59731a9b876c83d4796421d25b0a150c30,
  0xc76b95a4d382c86a9748bd13796421d25b0a150c30,
  0xc76b9a4d382c86a59748bd13796421d25b0a150c30,
  0xd4a9b67c83c286a59748bd13796421d25b0a150c30,
  0xc795a6bd3828b9a4768c4d13796421d25b0a150c30,
  0xc79a6bd3828b95a4768c4d13796421d25b0a150c30,
  0xdb9a47683c795a6b828c4d13796421d25b0a150c30,
  0xdb6a97c838b95a47682c4d13796421d25b0a150c30,
  0xdb5a97c8642130c28b674a150d2591b96a0d4c3873,
  0xd25a4c769b831c86a95bd374287912d46b0a150c30,
  0xa97c8678b964c4d382db6731a42195d25b0a150c30,
  0xd47c28b6a591c879a469bd38376421d25b0a150c30,
  0xc4db6a59782a9b8c74691d38376421d25b0a150c30,
  0xd4c8b6a591a9bd3874697c28376421d25b0a150c30,
  0xdb95a4c83d478b6a91697c28376421d25b0a150c30,
  0xdb6a597c838b91d4769a4c28376421d25b0a150c30,
  0xdb6a59783c8b91d4769a4c28376421d25b0a150c30,
  0xa96b8c74c4db9782d386a591376421d25b0a150c30,
  0xdb5a97c8642130c2d4769150d3c4a18b952b6a0873,
  0x95a46bd387c21d4c8b9a6731796824d25b0a150c30,
  0xd37c8b64a591c4db9a678312796824d25b0a150c30,
  0x9bd47c83195a6b8769a4c28d376421d25b0a150c30,
  0xa6b8c7959bd4783169a4c28d376421d25b0a150c30,
  0xdb5a97c8642130a476b9150d2596a1c28b0d4c3873,
  0xdb64a597c2831d4c8b9a6737869124d25b0a150c30,
  0xc4a5976bd3827c8b9a64d137869124d25b0a150c30,
  0xdb5a97c8642130c2d1a6b0a47691508b952d4c3873,
  0xd37c28b64a591db9a678c479683124d25b0a150c30,
  0xdb6782c4a591d37c8b9a6479683124d25b0a150c30,
  0xc73d46a9b82db678c4a59179683124d25b0a150c30,
  0xd47c28b6a591c83db9764a96873124d25b0a150c30,
  0xd47c8b6a591c283db9764a96873124d25b0a150c30,
  0xdb9a467c83d4c2869731a6b8742195d25b0a150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_4_6 : Region 14 n14a_mask [6,4,3] 39 6 29 none :=
  of_certs (hn:=by decide) [
  0xd4c76a59b83bd2c8679a428964731d125b0a150c30,
  0xd4c795a683bd2c876b9a428964731d125b0a150c30,
  0xdb95a68c4b83d2c7679a428964731d125b0a150c30,
  0xd4c79a683bd2c876b95a428964731d125b0a150c30,
  0xdb9a68c4d38b67c2795a428964731d125b0a150c30,
  0xdb5a97c8642130a6b82d150a47691c259b0d4c3873,
  0x95a46bd2c7831d4c8b9a673796824d125b0a150c30,
  0xd46a59b837c2db678c4a913796824d125b0a150c30,
  0xd4c79b838c2db67695a4289a64731d125b0a150c30,
  0xdb5a97c8642130a4769150d28b6a1c259b0d4c3873,
  0x95a476b8c2d31db9a687c46973824d125b0a150c30,
  0x95a6b87c4d31a9bd2c86746973824d125b0a150c30,
  0xdb95a4768c29a6b87c4d316973824d125b0a150c30,
  0x95a6b874c2d31db97c864a9673824d125b0a150c30,
  0xd3786b95a4c2db8c79a6476913824d125b0a150c30,
  0xd4c8b6a5973a9bd2c786476913824d125b0a150c30,
  0xd4795a6b8c2a9bd37864c76913824d125b0a150c30,
  0xdb95a46873d479a6b8c2c76913824d125b0a150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_4_7 : Region 14 n14a_mask [7,4,3] 39 7 28 none :=
  of_certs (hn:=by decide) [
  0xb8c79a6db96874c467382d24a591d3125b0a150c30,
  0xdb5a97c8642130c476952c3d28b0a6b9150d4a1873,
  0xd2c738b64a591db9678c479a6824d3125b0a150c30,
  0xd2c8b674a591db9a687c46973824d3125b0a150c30,
  0xd4c78b6a591a9bd2c86746973824d3125b0a150c30,
  0xd2c478b6a591db97c864a9673824d3125b0a150c30,
  0xd47c8b6a591c2db97864a9673824d3125b0a150c30,
  0xdb95a687c4d2c8b64791a9673824d3125b0a150c30,
  0xdb6879a4c27c8b95a64d19673824d3125b0a150c30,
  0xd38691a47c25b0a9bd28c4673150a6b8795d421c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_4_8 : Region 14 n14a_mask [8,4,3] 39 8 27 none :=
  of_certs (hn:=by decide) [
  0xd4c79a6b8319bd2c87682195a46d37425b0a150c30,
  0xd4c796b831a9bd2c87682195a46d37425b0a150c30,
  0xd4a59b682db8c76a9187964c213d37425b0a150c30,
  0xd47c283196a5b0d376b8c4a9521db978642a150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_4_9 : Region 14 n14a_mask [9,4,3] 39 9 26 none :=
  of_certs (hn:=by decide) [
  0xd138259a4c76b0c86a5b973d42db8746912a150c30,
  0xd4a59b67c2831d379a68c425b0db8746912a150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_4_10 : Region 14 n14a_mask [10,4,3] 39 10 25 none :=
  of_certs (hn:=by decide) [
  0xdb5a97c8642130b82c4769150c3d259b6a0d4a1873,
  0xd387952c4a6b0d19a5b8c7642869bd47312a150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_4_11 : Region 14 n14a_mask [11,4,3] 39 11 24 none :=
  of_certs (hn:=by decide) [
  0xd3825a64c79b0c876b591d42db869a47312a150c30,
  0xd4c7825a6b91d38c246795b0db869a47312a150c30] (by rfl)

private theorem n14a_3_4 : Region 14 n14a_mask [4,3] 40 4 35 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14a_3_4_4
  · exact n14a_3_4_5
  · exact n14a_3_4_6
  · exact n14a_3_4_7
  · exact n14a_3_4_8
  · exact n14a_3_4_9
  · exact n14a_3_4_10
  · exact n14a_3_4_11
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_5 : Region 14 n14a_mask [5,3] 40 5 34 none :=
  of_certs (hn:=by decide) [
  0xdb69a4c83a5b86c795287642d4731b91a0d2150c30,
  0xdb6a4c839a5b86c795287642d4731b91a0d2150c30,
  0xc8b69a4db5a683c795287642d4731b91a0d2150c30,
  0xd25a476913c8b0d1a6ba973083d42c2150c7864b95,
  0xdb5a683b8c796c4a95287642d4731b91a0d2150c30,
  0xdb6974a52c831b86a95d4c7387642b91a0d2150c30,
  0xc4a96783db52a68c795b8246d4731b91a0d2150c30,
  0xdb597c4a683a96b8c2578246d4731b91a0d2150c30,
  0xdb6a597c83b869a4c2578246d4731b91a0d2150c30,
  0xa68795c769a4c8b642db5283d4731b91a0d2150c30,
  0xc4a6bd387952b869a57c8246d4731b91a0d2150c30,
  0xc795a6bd3829a4c8768b5246d4731b91a0d2150c30,
  0xdb6a597c839a4c28768b5246d4731b91a0d2150c30,
  0xdb6a97c83c4a5967828b5246d4731b91a0d2150c30,
  0xc4a96bd382a5b8c768795246d4731b91a0d2150c30,
  0xdb69a4c83a5b82c768795246d4731b91a0d2150c30,
  0xb8c769a5c4687952db6a4283d4731b91a0d2150c30,
  0xc46a195bd287305a0b683c21a9674d4250c8b97d31,
  0xd4a52c796b831db59a64c87376824b91a0d2150c30,
  0xc796b83d4a52db59a64c873176824b91a0d2150c30,
  0xc783db6a952b8c4a5697428d46731b91a0d2150c30,
  0xdb59a4c783a6b8c25697428d46731b91a0d2150c30,
  0xdb59a4c83a6b87c25697428d46731b91a0d2150c30,
  0xdb69a4c83a52c786b597428d46731b91a0d2150c30,
  0xdb6a4c83c7869a52b597428d46731b91a0d2150c30,
  0xdb5a97c8642130b82c4a150c376a0d4783d2591b96,
  0xdb6479a52c831d4a695b873c76824b91a0d2150c30,
  0xc83db6a4795278b5a964d13c76824b91a0d2150c30,
  0xd4c79683a52c876b59a428db64731b91a0d2150c30,
  0xdb5a97c8642130c3d4a150b8376a0c4782d2591b96,
  0xd46b5a97c2831db8c4a6737869524b91a0d2150c30,
  0xc4679a5bd3827c8b6a4d137869524b91a0d2150c30,
  0xd46b5a97c83db82c4a67317869524b91a0d2150c30,
  0xd46b5a97c2831db86a473c8769524b91a0d2150c30,
  0xc79a5b64d38274a68bd13c8769524b91a0d2150c30,
  0xc73db5a46828b6a974d13c8769524b91a0d2150c30,
  0xdb68c4a97317c28b5a64d38769524b91a0d2150c30,
  0xc4679a5b82db6a47c831d37869524b91a0d2150c30,
  0xc4a5b96782a97c86bd3746d42591b831a0d2150c30,
  0xc79b5a6829a4c876bd3746d42591b831a0d2150c30,
  0xb97c86a5c4a96782bd3746d42591b831a0d2150c30,
  0xb68c79a5a4c28769bd3746d42591b831a0d2150c30,
  0xdb5a97c8642130c374a150c4d382b876a052d19b96,
  0xd3782c46b5a91db97c86a4769524b831a0d2150c30,
  0xd3782c4a6b91db5a97c864769524b831a0d2150c30,
  0xc73d4a9b682db5a64c8791769524b831a0d2150c30,
  0xa9b6874db5a6738c79642d4c2591b831a0d2150c30,
  0xdb5a97c8642130d476952a6b9150d3c4a1b0c28873,
  0xd3782c46b5a91db968c74a679524b831a0d2150c30,
  0xd47c286b5a91c873db964a679524b831a0d2150c30,
  0xd47c86b5a91c2873db964a679524b831a0d2150c30,
  0xdb5a64c28791a9b68c74d3769524b831a0d2150c30,
  0xdb682c74a91c879b5a64d3769524b831a0d2150c30,
  0xc46a5b9782db68c74a91d3769524b831a0d2150c30,
  0xdb5a6978c4a9b682c74673d19524b831a0d2150c30,
  0xb96a1d3c478250db5a97c8642130c2d4a08b673951,
  0xd382c746a5b91db879a4c869524b6731a0d2150c30,
  0xc79b5a64d382c8bd19a47869524b6731a0d2150c30,
  0xc79b5a4d382c8bd19a647869524b6731a0d2150c30,
  0xc46a9bd382d4a5b8c7917869524b6731a0d2150c30,
  0xdb5a4c287917c8b9a64d3869524b6731a0d2150c30,
  0xdb82c74a91c879b5a64d3869524b6731a0d2150c30,
  0xdb5a978c4c74a69b82d38642591b6731a0d2150c30,
  0xb691d38c7425a0a682c4db59731a9b8764d2150c30,
  0xdb52c86a91b97c4d387695a428b64731a0d2150c30,
  0xdb86a97c4d38c25b917695a428b64731a0d2150c30,
  0xb52c74d38691a0db8c46a59731a9b67824d2150c30,
  0xdb8374c25a691b597c864d31a0a9b67824d2150c30,
  0xb591d382c764a0a96bd4c873179b86a524d2150c30,
  0xd382c7469b5a19a0bd4c86731a6b879524d2150c30,
  0xdb5a97c8642130b674c3d1a0c2d4a69150b9528873,
  0xdb5a9764c2831d4a0b968c7378b6a19524d2150c30,
  0xc4679a5bd382b968c731d4a078b6a19524d2150c30,
  0xd47c2869b5a1c83db0a9764a6b87319524d2150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_6 : Region 14 n14a_mask [6,3] 40 6 33 none :=
  of_certs (hn:=by decide) [
  0xd4c769b83bd2c8679a528a64731d195b0a42150c30,
  0xd4c79b838c2db6769a528a64731d195b0a42150c30,
  0xdb978c48b69a52d2c7683a64731d195b0a42150c30,
  0xdb5a97c8642130c4a1950d473c2d38251b876a0b96,
  0xa52d4c8b69731db9a678382c746d195b0a42150c30,
  0xa52c8769bd31d4c79a682b83746d195b0a42150c30,
  0xa96782c4d31db97c86a52b83746d195b0a42150c30,
  0xa52c4db697831a9b8c7682d3746d195b0a42150c30,
  0xa9b67c4d2831c8796a528bd3746d195b0a42150c30,
  0xa97c286bd31d4c876a529b83746d195b0a42150c30,
  0x87c4db6a52a9768c2d319b83746d195b0a42150c30,
  0xa96b87c4d318c2db976a5283746d195b0a42150c30,
  0xa9687c4d31a52c8b976bd283746d195b0a42150c30,
  0xdb6a978c4d38b967c2a52864731d195b0a42150c30,
  0xb64c795283d1a0968c2db5a4731a9b876d42150c30,
  0x95a68c2d4731db679a19b87c46d3825b0a42150c30,
  0xd4c78b695a18c2db976a913746d3825b0a42150c30,
  0xdb86a597c49a1d2c876b913746d3825b0a42150c30,
  0xd4c78b69a18c2db976a5913746d3825b0a42150c30,
  0xdb6a978c4d2c7695a18b913746d3825b0a42150c30,
  0xd382c476a195b0d25a9b68c731978bd46a42150c30,
  0xd2c47386b95a1d319a67c825b0978bd46a42150c30,
  0xdb95a67839a1d2c47c8b69137d46825b0a42150c30,
  0xd4c259731a68b0d38c76b5a919bd28746a42150c30,
  0xa52c4d38b6791d0b59a68c7319bd28746a42150c30,
  0xd4c2597831a6b0db5a967c828b91d3746a42150c30,
  0xa9786b52c4d31d0b8c76a5919bd283746a42150c30,
  0xa5976b8c4d31d19a687c25b09bd283746a42150c30,
  0xd4c25a19786b0bd38c76a959b82d13746a42150c30,
  0xc4d3879a6b52a1d0b8c769582db913746a42150c30,
  0xdb95a6874c2a97c8b64d31d19673825b0a42150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_7 : Region 14 n14a_mask [7,3] 40 7 32 none :=
  of_certs (hn:=by decide) [
  0xd2c478b95a1db679a4c869137d3825b0a642150c30,
  0xd4c78b69a18c2db9764a59137d3825b0a642150c30,
  0xdb879a4c2d476b95a1c869137d3825b0a642150c30,
  0xd479b68c29a1db876c4a59137d3825b0a642150c30,
  0xd31a952c4786b0d4a5b8c76919bd2837a642150c30,
  0xd1a4c259678b09a5b68c74d319bd2837a642150c30,
  0xdb8c79a4a59b6831d19674c2d37825b0a642150c30,
  0xd38c2591a476b0db5a9687c49b82d137a642150c30,
  0xd38b67952c4a1d0b5a968c7482db9137a642150c30,
  0xc4d38b679a52d1a47c8695b082db9137a642150c30,
  0xd382c47691a5b0db68c79a48b952d137a642150c30,
  0xd382c4769b5a1d0b68c79a48bd259137a642150c30,
  0xc769b5a4d382c86b0d1a9748bd259137a642150c30,
  0xd38697c4a5b0b9a1d2c8764db8259137a642150c30,
  0xd386b97c4a1d2c8769a5b04db8259137a642150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_8 : Region 14 n14a_mask [8,3] 40 8 31 none :=
  of_certs (hn:=by decide) [
  0xd3874c25b691a0db9a67c8295a4d137b8642150c30,
  0xd38796b52c4a1db95a67c824d0a9137b8642150c30,
  0xd382c769b5a1db6a4c879524d0a9137b8642150c30,
  0xd38796b52c4a1db9a67c824d0a59137b8642150c30,
  0xd25b9678c4a1c79a6bd3824d0a59137b8642150c30,
  0xd38c79a6b52db96782c4a14d0a59137b8642150c30,
  0xd38c796b5a1a9bd4c28764a0d259137b8642150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_9 : Region 14 n14a_mask [9,3] 40 9 30 none :=
  of_certs (hn:=by decide) [
  0xd4c796a5b831a9bd2c8746b0a19528d37642150c30,
  0xd4c79a5b831a69bd2c8746b0a19528d37642150c30,
  0xdb9a6874c2d4a5b8c791b6952831a0d37642150c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_11 : Region 14 n14a_mask [11,3] 40 11 28 none :=
  of_certs (hn:=by decide) [
  0xb67c4d382591a0d2c8b96a473150db5a9786421c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_12 : Region 14 n14a_mask [12,3] 40 12 27 none :=
  of_certs (hn:=by decide) [
  0xd137c4a52869b0a6b8c2d479150a95bd3876421c30] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_3_13 : Region 14 n14a_mask [13,3] 40 13 26 none :=
  of_certs (hn:=by decide) [
  0x95a6b8c2d4731d1a4c796825b0a9bd387642150c30] (by rfl)

private theorem n14a_3 : Region 14 n14a_mask [3] 41 3 39 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14a_3_3
  · exact n14a_3_4
  · exact n14a_3_5
  · exact n14a_3_6
  · exact n14a_3_7
  · exact n14a_3_8
  · exact n14a_3_9
  · exact absent_region (by rfl)
  · exact n14a_3_11
  · exact n14a_3_12
  · exact n14a_3_13
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_4_4_4 : Region 14 n14a_mask [4,4,4,4] 38 4 26 none :=
  of_certs (hn:=by decide) [
  0xdb6973b5a9a674c783d4c286429521c8b0d1a05130,
  0xb69a5db973a674c783d4c286429521c8b0d1a05130,
  0x86a5bd4c73b9769a46d3c287429521c8b0d1a05130,
  0xdb976a4c2b5a96c783d47386429521c8b0d1a05130,
  0xdb5a6973b9a476c387d4c286429521c8b0d1a05130,
  0xa5b6974db9a673c387d4c286429521c8b0d1a05130,
  0xdb5a97c8642130b876a691d152c283d374c4a0b950,
  0xdb9783c2a5b69c76a4d47386429521c8b0d1a05130,
  0xd4a9783c2db67b96a5c47386429521c8b0d1a05130,
  0x96b5a4d387c21db952a679c4738642c8b0d1a05130,
  0xb679a5db96a4d387c2c47386429521c8b0d1a05130,
  0xd4a5b96837c2db64c3a97687429521c8b0d1a05130,
  0xdb5a69783c2b9a4c764d3786429521c8b0d1a05130,
  0xd4a5b697c2a9bd38764c3786429521c8b0d1a05130,
  0xd4a6b9783db5a967c24c3786429521c8b0d1a05130,
  0xdb976a4b5a96c4783d37c286429521c8b0d1a05130,
  0xb679a5db96a4c4783d37c286429521c8b0d1a05130,
  0xc37869a5bd42c76a479b64d3829521c8b0d1a05130,
  0xc4db5a69783a9b674c2d3786429521c8b0d1a05130,
  0xc4db6a9783a5b9674c2d3786429521c8b0d1a05130,
  0xc4a6b9783db5a9674c2d3786429521c8b0d1a05130,
  0xdb96a4c783b5a9764d2c3786429521c8b0d1a05130,
  0xdb5a69783b9a4c764d2c3786429521c8b0d1a05130,
  0xc796b5a4db9a67834d2c3786429521c8b0d1a05130,
  0xc769b5a4d2c38749a6bd3786429521c8b0d1a05130,
  0xdb5a97c8642130c28374a0b876a691d4c3d152b950,
  0x9b5a6783c4d21c73db69529a478642c8b0d1a05130,
  0xc3d4a5b69782db9a683742c7649521c8b0d1a05130,
  0xc374db9a682b69783d24a5c7649521c8b0d1a05130,
  0xc4a683b5a96db974d37c2876429521c8b0d1a05130,
  0xdb974a683c2b5a96d4c73876429521c8b0d1a05130,
  0xc4db5a9683a6b974d37c2876429521c8b0d1a05130,
  0xc4db9a683a5b6974d37c2876429521c8b0d1a05130,
  0xdb5a6974c4a9b683d37c2876429521c8b0d1a05130,
  0xc79b5a683bd4a96d374c2876429521c8b0d1a05130,
  0xc796b5a4a9bd386d473c2876429521c8b0d1a05130,
  0xa5b6974db9a683d4c3782c76429521c8b0d1a05130,
  0xdb5a97c8642130b96a150d2591b876d473c382c4a0,
  0x9a5b6783c4d21c74a69529bd378642c8b0d1a05130,
  0xd4a5b69783c2db9a64c73768249521c8b0d1a05130,
  0xdb5a964c783c2d4a6b973768249521c8b0d1a05130,
  0xdb5a9683b974a6d4c782c376429521c8b0d1a05130,
  0xa5b6974db9a683d4c782c376429521c8b0d1a05130,
  0xdb5a97c8642130c259b0a69150b876c473d382d4a1,
  0x96b5a4c783d21db9a674952c378642c8b0d1a05130,
  0xd4a5b69783c2db9a6473c768249521c8b0d1a05130,
  0xd4a5b9687c3c2db6a9746738249521c8b0d1a05130,
  0xd4a5b697c3db9a6874c26738249521c8b0d1a05130,
  0xd37869b5a4c2db6a97467c38249521c8b0d1a05130,
  0xdb5a96874c3d2c79b64a6738249521c8b0d1a05130,
  0xd46b5a97c3c2db96874a6738249521c8b0d1a05130,
  0xdb5a6874c3d2c79b64a96738249521c8b0d1a05130,
  0xd4a5b67c3db96874c26a9738249521c8b0d1a05130,
  0xc3d4678219a5b0db6a4c8379529b86c742d1a05130,
  0x95a4c8376bd21c3d46a97825b09b86c742d1a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_4_4_5 : Region 14 n14a_mask [5,4,4,4] 38 5 25 none :=
  of_certs (hn:=by decide) [
  0xb6a95db974c7683d3782c4a5296421c8b0d1a05130,
  0xd479a5b683c76a482c37db95296421c8b0d1a05130,
  0xc4db9a683a5b674d37c28795296421c8b0d1a05130,
  0xc4a9b683db5a674d37c28795296421c8b0d1a05130,
  0xdb9a6873b5a476d4c382c795296421c8b0d1a05130,
  0xc76b9a4db5a683d473c28795296421c8b0d1a05130,
  0xdb5a97c8642130c4a150d2591b96a0b876d473c382,
  0xc8b5a97642130b96a150db683d2591c473c782d4a0,
  0xd3c4a9786b52db95a674c283796421c8b0d1a05130,
  0xdb68795a4c3d25b9a674c283796421c8b0d1a05130,
  0xdb5976a4c3d4786b9a52c283796421c8b0d1a05130,
  0xdb9a683b5a476d4c782c3795296421c8b0d1a05130,
  0xc8b5a97642130d386b0a69150db952c473c782d4a1,
  0xd3c4a59b6782c74db529a683796421c8b0d1a05130,
  0xd4a95b687c3a679bd254c283796421c8b0d1a05130,
  0xd4a9b687c3c2db5a67495283796421c8b0d1a05130,
  0xd4a95b687c3c2db9746a5283796421c8b0d1a05130,
  0xd4a9b687c3c2db59746a5283796421c8b0d1a05130,
  0xd4a5b97c3c4786a9526bd283796421c8b0d1a05130,
  0xd4a5b97c3c2db68746a95283796421c8b0d1a05130,
  0xc4783d2196a5b0c376bd4a952c8b978642d1a05130,
  0x9a5b6783d4c21db8c374a6952c0b978642d1a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_4_4_6 : Region 14 n14a_mask [6,4,4,4] 38 6 24 none :=
  of_certs (hn:=by decide) [
  0x86b973d3c782db52c459674a9a6421c8b0d1a05130,
  0x83db967c4a52b687954d2c379a6421c8b0d1a05130,
  0xd4a5b9687c39a6bd25c47382976421c8b0d1a05130,
  0xdb5a9687c39b6a4d25c47382976421c8b0d1a05130,
  0xc7869b5a4c3db6a952d47382976421c8b0d1a05130,
  0xc74a5b9683d4c2873db6a952976421c8b0d1a05130,
  0xc3db96a52b6874a95d4c7382976421c8b0d1a05130,
  0xd4c79b52db6782c35968374a9a6421c8b0d1a05130,
  0xc4783d2196a5b0c76bd4a9529b8c378642d1a05130,
  0x9a5b6874d3c21db96a4c7382597642c8b0d1a05130,
  0xd4c379b5a682c783db64a952476912c8b0d1a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_4_4_7 : Region 14 n14a_mask [7,4,4,4] 38 7 23 none :=
  of_certs (hn:=by decide) [
  0xc4a5b9673d47c283db6a9529786421c8b0d1a05130,
  0xdb5a9673c4a6b952d47c3829786421c8b0d1a05130,
  0xdb5a97c8642130c28769150d38b952c473d4a1b6a0,
  0x95b6a4c783d21c374db96825a97642c8b0d1a05130,
  0xd4c7386a9b52c3db6795a428746912c8b0d1a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_4_4_8 : Region 14 n14a_mask [8,4,4,4] 38 8 22 none :=
  of_certs (hn:=by decide) [
  0xdb5a97c8642130c478b952c3769150d382d4a1b6a0,
  0xc8b5a97642130bd2869150c4a6b952c783d374d1a0,
  0xd3c7864a9b52c4db697382476a5912c8b0d1a05130,
  0xd3786b9a4c2bd4697c3825476a5912c8b0d1a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_4_4_9 : Region 14 n14a_mask [9,4,4,4] 38 9 21 none :=
  of_certs (hn:=by decide) [
  0xd4c7386a9b52c3db697428764a5912c8b0d1a05130,
  0xd4c73869b52c3db6a97428764a5912c8b0d1a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_4_4_10 : Region 14 n14a_mask [10,4,4,4] 38 10 20 none :=
  of_certs (hn:=by decide) [
  0xd4a9b687c2c4796a528395bd376421c8b0d1a05130] (by rfl)

private theorem n14a_4_4_4 : Region 14 n14a_mask [4,4,4] 39 4 30 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14a_4_4_4_4
  · exact n14a_4_4_4_5
  · exact n14a_4_4_4_6
  · exact n14a_4_4_4_7
  · exact n14a_4_4_4_8
  · exact n14a_4_4_4_9
  · exact n14a_4_4_4_10
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_4_5 : Region 14 n14a_mask [5,4,4] 39 5 29 none :=
  of_certs (hn:=by decide) [
  0xd4a9b87c395a674c837db68296421c25b0d1a05130,
  0xd4a597c38b9a674c837db68296421c25b0d1a05130,
  0xa678b95d4a97c34c837db68296421c25b0d1a05130,
  0xb59782c46a1d30d25a09a421db674c05139b868c73,
  0xa678b95c83d479a4c37db68296421c25b0d1a05130,
  0x95a6b83c74d21c869a4bd37987642c25b0d1a05130,
  0xd4a59b67c382c86a9748bd3796421c25b0d1a05130,
  0xdb95a6874c3d28c79a46b83796421c25b0d1a05130,
  0xd4c795a682a9bd3c8746b83796421c25b0d1a05130,
  0xa68b95c879a4db67c3d4738296421c25b0d1a05130,
  0xd3c4a59b6782db8c749a683796421c25b0d1a05130,
  0xdb68795a4c3a9b8c764d283796421c25b0d1a05130,
  0xdb86a597c3b9a4c8764d283796421c25b0d1a05130,
  0xc8b6795a4db9a687c34d283796421c25b0d1a05130,
  0xdb6a5978c38b9a476c4d283796421c25b0d1a05130,
  0xdb6a978c38b95a476c4d283796421c25b0d1a05130,
  0xa67c8b95db6874c3d4a9738296421c25b0d1a05130,
  0xdb5a97c8642130c2d3769150c47838b952d4a1b6a0,
  0x967c38b5a4d21c86a9bd374287952c46b0d1a05130,
  0xc76a4d38b952db5a968c374287912c46b0d1a05130,
  0xdb69a4c3782a59b86c74d38976421c25b0d1a05130,
  0xc4db95a683a96b874c73d28976421c25b0d1a05130,
  0xc4a596b83db9a6874c73d28976421c25b0d1a05130,
  0xc78b695a4a9bd386c374d28976421c25b0d1a05130,
  0xc78b69a4db95a683c374d28976421c25b0d1a05130,
  0xdb5a97c8642130c38769150d374a18b952d4c2b6a0,
  0x95a46b87c3d218c4db9a673796824c25b0d1a05130,
  0x9a46b87c3d218c4db95a673796824c25b0d1a05130,
  0xc8b695a4a9bd376d47c3829786421c25b0d1a05130,
  0xdb5a97c8642130c3769150d3874a18b952d4c2b6a0,
  0x95a476b8c3d21db9a687c46973824c25b0d1a05130,
  0xdb64a597c382d4c8b9a6737869124c25b0d1a05130,
  0xd4a5976b8c3db9a64c73827869124c25b0d1a05130,
  0x95a6b874c3d21db97c864a9673824c25b0d1a05130,
  0xd3c795a46b8286a9bd473c8769124c25b0d1a05130,
  0xc795a4db683d28b9a6473c8769124c25b0d1a05130,
  0xdb64a97c382d4c8b9673786a59124c25b0d1a05130,
  0xd4a976b8c3db964c7382786a59124c25b0d1a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_4_6 : Region 14 n14a_mask [6,4,4] 39 6 28 none :=
  of_certs (hn:=by decide) [
  0xdb69a478c3a59b867c2d46973821c425b0d1a05130,
  0xdb95a68c3b874a967c2d46973821c425b0d1a05130,
  0xa596b874db9a68c37c2d46973821c425b0d1a05130,
  0xd4a968c3a59b876bd2c746973821c425b0d1a05130,
  0xdb5a97c8642130c38b9150876952d374a1d4c2b6a0,
  0x95a4db6738c21d3c79a6829b8746c425b0d1a05130,
  0xc3795a4db682d38c76a9129b8746c425b0d1a05130,
  0xdb6a59738c29a4d3c768219b8746c425b0d1a05130,
  0x78b9a64a4db695d3768c297c3821c425b0d1a05130,
  0xdb5a97c8642130c4738b0a6b9150876952d3c2d4a1,
  0x95a4db6738c21d3c79682a9b8746c425b0d1a05130,
  0x95a4db678c21d3c79a6829b83746c425b0d1a05130,
  0xc795a4db682d3c876a9129b83746c425b0d1a05130,
  0x95a4db678c21d3c79682a9b83746c425b0d1a05130,
  0xd4a5976b8c3a9bd2c78691283746c425b0d1a05130,
  0xdb6a5978c3d4a9b867c291283746c425b0d1a05130,
  0xdb86a597c39a4d2c876b91283746c425b0d1a05130,
  0xc4a52d197386b0d3c8b5967421a0db9a64c7825130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_4_7 : Region 14 n14a_mask [7,4,4] 39 7 27 none :=
  of_certs (hn:=by decide) [
  0x95a4d376b8c21db9a6829783c46c7425b0d1a05130,
  0xc4db95a67382d3c86912b879a46c7425b0d1a05130,
  0xc4db9a67382d3c8b69128795a46c7425b0d1a05130,
  0xd376a9b8c296bd4c38218795a46c7425b0d1a05130,
  0xc4db9a67382d3c86912b8795a46c7425b0d1a05130,
  0xc4db6a9783d2c8b967382195a46c7425b0d1a05130,
  0xd4a96b8c3db97864c295a673821c7425b0d1a05130,
  0xd4738c2591a6b0d3c78b5a96421db97682c4a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_4_8 : Region 14 n14a_mask [8,4,4] 39 8 26 none :=
  of_certs (hn:=by decide) [
  0xd46a59b8c3c2db6874a9673824c79125b0d1a05130,
  0xc46a9b873d4a5968c276bd3824c79125b0d1a05130,
  0xc4d3782196a5b0db683c74a952c8b97642d1a05130,
  0x95a6bd47c3821c4a96873d25b0c8b97642d1a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_4_9 : Region 14 n14a_mask [9,4,4] 39 9 25 none :=
  of_certs (hn:=by decide) [
  0xdb5a97c8642130c3d28769150c4738b952d4a1b6a0,
  0xc7386a4d259b08c3db5a97642c478b6912d1a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_4_10 : Region 14 n14a_mask [10,4,4] 39 10 24 none :=
  of_certs (hn:=by decide) [
  0xdb5a97c8642130d259b874a1c283769150d4c3b6a0,
  0xc4d3769a528b0db97c386a42c8746b5912d1a05130,
  0x5a683c79bd42c4a9673d28b0c8746b5912d1a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_4_11 : Region 14 n14a_mask [11,4,4] 39 11 23 none :=
  of_certs (hn:=by decide) [
  0x86a973c4db52d38c0b96742c78b64a5912d1a05130] (by rfl)

private theorem n14a_4_4 : Region 14 n14a_mask [4,4] 40 4 34 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14a_4_4_4
  · exact n14a_4_4_5
  · exact n14a_4_4_6
  · exact n14a_4_4_7
  · exact n14a_4_4_8
  · exact n14a_4_4_9
  · exact n14a_4_4_10
  · exact n14a_4_4_11
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_5 : Region 14 n14a_mask [5,4] 40 5 33 none :=
  of_certs (hn:=by decide) [
  0xc786b9a4a5976db8c383742d4691d25b0c21a05130,
  0xc76b9a4a59786db8c383742d4691d25b0c21a05130,
  0xd3c76b824a591a97869bd468c473d25b0c21a05130,
  0xa68b95c879a4db67c383742d4691d25b0c21a05130,
  0x86a59bd3c742c879a46b837d4691d25b0c21a05130,
  0xdb68795a4c3a9b8c7642837d4691d25b0c21a05130,
  0xdb86a597c3b9a4c87642837d4691d25b0c21a05130,
  0xc8b6795a4db9a687c342837d4691d25b0c21a05130,
  0xdb95a4768c3b879a6c42837d4691d25b0c21a05130,
  0xdb6a5978c38b9a476c42837d4691d25b0c21a05130,
  0xdb6a978c38b95a476c42837d4691d25b0c21a05130,
  0xc8b95a674bd3c7869a42837d4691d25b0c21a05130,
  0xa67c8b95db6874c39a42837d4691d25b0c21a05130,
  0xdb5a97c8642130c2874a1508b673d2591b96a0d4c3,
  0xd3c42876a5b91db8c74a95296837d46b0c21a05130,
  0x876a4c3db952d19a5b8c74296837d46b0c21a05130,
  0xdb9a6874c3b8c796738246d4a591d25b0c21a05130,
  0xdb9a687c3b8c4796738246d4a591d25b0c21a05130,
  0xc8b6a974db9687c3738246d4a591d25b0c21a05130,
  0xdb6874c3a9b8c769738246d4a591d25b0c21a05130,
  0xdb5a97c8642130c3769150d2c4a1d47838b952b6a0,
  0xd3c7428b6a5918c4db9673a97864d25b0c21a05130,
  0xd3c78b64a5918c4db9a673796824d25b0c21a05130,
  0x8c4db95a673d3c78b64a91796824d25b0c21a05130,
  0xc8769a4c79b6838bd3742d46a591d25b0c21a05130,
  0xdb5a97c8642130d376952a6b9150c3874c28b0d4a1,
  0xd3c7428b6a591db9678c4a973864d25b0c21a05130,
  0xd3c8b674a591db9a687c46973824d25b0c21a05130,
  0xd4c78b6a591a9bd3c86746973824d25b0c21a05130,
  0xd3c478b6a591db97c864a9673824d25b0c21a05130,
  0xd47c8b6a591c3db97864a9673824d25b0c21a05130,
  0xdb95a687c4d3c8b64791a9673824d25b0c21a05130,
  0xdb6879a4c37c8b95a64d19673824d25b0c21a05130,
  0xc83791d246a5b0d3c478b69521a0db9a4c76825130,
  0xdb9a47c8295a687b64c38d37691d425b0c21a05130,
  0xdb9a4782c86a597b64c38d37691d425b0c21a05130,
  0xc8795a4c746b83db9a682d37691d425b0c21a05130,
  0xdb5a97c8642130a6b9150876952d374a138b0cd4c2,
  0xd28b673c4a591db964783a97c86d425b0c21a05130,
  0xdb6795a4c382d19a68c739b8746d425b0c21a05130,
  0xdb6a597c382d19a4c86739b8746d425b0c21a05130,
  0xc8b5a97642130d19b6a0bd4a150d374c269528c783,
  0xdb6795a4c382d1968c73a9b8746d425b0c21a05130,
  0xdb68795a4c3a91d28c769b83746d425b0c21a05130,
  0xdb6879a4c3d28c76a5919b83746d425b0c21a05130,
  0xdb695a4c7828c3d1976a9b83746d425b0c21a05130,
  0xd3867c4a91bd28795a69b8c3746d425b0c21a05130,
  0xdb968c47397c38b64ad2876a591d425b0c21a05130,
  0xc286473d19a5b0a6bd4c38795219b8c76d24a05130,
  0xd4c378b6a591a97c864769bd24d3825b0c21a05130,
  0xc86bd4a5973c78b9a647691d24d3825b0c21a05130,
  0xc86bd4a973c78b95a647691d24d3825b0c21a05130,
  0xc86bd4a97378b95a64c7691d24d3825b0c21a05130,
  0xdb68795a4c8b9a6473c7691d24d3825b0c21a05130,
  0xd1952837c4a6b0d3c8b5a96742db97864c21a05130,
  0xd247c38b6a591d3769a4c825b0db97864c21a05130,
  0xc4db9a68391d28c76b8795a46d37425b0c21a05130,
  0xd19a64c37825b0d4a59b67c837968bd24c21a05130,
  0xd25a47c38b691d0b59a64c873db976824c21a05130,
  0xdb5a97c8642130c4d3769150d2c3874a19528bb6a0,
  0xd283c746a5b91d0b68c4a973db8769524c21a05130,
  0xd2837c4a6b91d3c86479a5b0db8769524c21a05130,
  0xd283c7964a5b0d4c8b9a673786bd19524c21a05130,
  0xd46a5b97c382d0b8c4a9673786bd19524c21a05130,
  0xd476a59b8c3db69a4c7382d19786425b0c21a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_6 : Region 14 n14a_mask [6,4] 40 6 32 none :=
  of_certs (hn:=by decide) [
  0xdb9a67c38c2d4796b837864a52d195b0c421a05130,
  0xb8c79a6db967834d2c37864a52d195b0c421a05130,
  0xdb5a97c86421303c4d28d374a1c259b0a69150b876,
  0xd2c38746a5b91db869a4c79528d376b0c421a05130,
  0xc796b83d4a52db9a67828c3746d195b0c421a05130,
  0xc8769bd4a52d3c79a682b83746d195b0c421a05130,
  0xdb97c86a52d4a96782c3b83746d195b0c421a05130,
  0xc38796bd4a52a9b8c7682d3746d195b0c421a05130,
  0xc3db6879a52d4a67c829b83746d195b0c421a05130,
  0xc79a4db682d3c876a529b83746d195b0c421a05130,
  0xd4a96b87c38c2db976a5283746d195b0c421a05130,
  0xd4a9687c3c8b976a52bd283746d195b0c421a05130,
  0xc286473d19a5b0db6a4c3879529b8c76d421a05130,
  0xdb682c374a591c46a9783d25b09b8c76d421a05130,
  0xc86bd4a597391d2c76a9b8746d3825b0c421a05130,
  0xdb68c795a491d2c376a9b8746d3825b0c421a05130,
  0xd4a5967c2db68c3791a9b8746d3825b0c421a05130,
  0xd2c786a91bd4a59769b8c3746d3825b0c421a05130,
  0xd195a473c286b0d38c76a9b52978bd46c421a05130,
  0xd2c38674a5b918c73d0b6a952978bd46c421a05130,
  0xc79a6b83db9678c2d374a591d46825b0c421a05130,
  0xd19674a52c38b0db59a68c73b9782d46c421a05130,
  0xd4a52c38b6791d0b59a68c739bd28746c421a05130,
  0xd38b67c25a91d4a68c3795b09bd28746c421a05130,
  0xdb5a97c8642130874a6b952b837691502d1a0cd4c3,
  0xd4a52c38796b0db59a67c828b91d3746c421a05130,
  0xc3d4a9786b52a67c8b0d1959bd283746c421a05130,
  0xc3d4a9786b52a67c8bd1959b0d283746c421a05130,
  0xc8679a4db52d3c78b6a5919b0d283746c421a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_7 : Region 14 n14a_mask [7,4] 40 7 31 none :=
  of_certs (hn:=by decide) [
  0xdb5a6978c38b9a476c4d2837d1952c0b6421a05130,
  0xdb9a678c3974a5b86c4d2837d1952c0b6421a05130,
  0xc8b5a974d4a687c3db967382d1952c0b6421a05130,
  0xd1952873c4a6b0db5a9768c29b83d46c7421a05130,
  0xd473c28b5a691d3867c4a9529bd0c87b6421a05130,
  0xd3c74a5b9682c4db8376a95291d0c87b6421a05130,
  0xdb5a97c8642130b83769150c259b6a0a1d2874d4c3,
  0xd3c28b5a47691d4c786a9529bd0c837b6421a05130,
  0xd3c74a5b9682c4db876a95291d0c837b6421a05130,
  0xd3c28b5a47691db9a687c4952d0c837b6421a05130,
  0xd3c4a678b952db5a968c7491d0c2837b6421a05130,
  0xd4a5b9687c3db8c476a95291d0c2837b6421a05130,
  0xd4a5b9678c3c2db86a974c0d1952837b6421a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_8 : Region 14 n14a_mask [8,4] 40 8 30 none :=
  of_certs (hn:=by decide) [
  0xd19a68374c25b0db6978c3b95a4d28c76421a05130,
  0xd2c3874a5b691d0b9a68c4bd379528c76421a05130,
  0xd4a5b69783c2db9a68c473b0d19528c76421a05130,
  0xdb5a6974c83d4a9b6873c2b0d19528c76421a05130,
  0xd4796a5b83c2db9a4c8736b0d19528c76421a05130,
  0xc4db5a69783d2c8b9a4736b0d19528c76421a05130,
  0xd4a596b8c3db9a6874c2d1973825b0c76421a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_9 : Region 14 n14a_mask [9,4] 40 9 29 none :=
  of_certs (hn:=by decide) [
  0xd4c796a5b83a9bd2c8746b0d19528c376421a05130,
  0xdb5a6978c4d38b9a47c26b0d19528c376421a05130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_10 : Region 14 n14a_mask [10,4] 40 10 28 none :=
  of_certs (hn:=by decide) [
  0xc28691d374a5b0d4c3876b9521a0db8c79a6425130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_11 : Region 14 n14a_mask [11,4] 40 11 27 none :=
  of_certs (hn:=by decide) [
  0xc246783d1a95b0d4c379b6825a0db8c74a69125130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_4_12 : Region 14 n14a_mask [12,4] 40 12 26 none :=
  of_certs (hn:=by decide) [
  0xd1a96b524783c0b973d4c286a0db8c764a59125130,
  0xd425b9a6873c0d382c4796b0a1db8c764a59125130] (by rfl)

private theorem n14a_4 : Region 14 n14a_mask [4] 41 4 38 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14a_4_4
  · exact n14a_4_5
  · exact n14a_4_6
  · exact n14a_4_7
  · exact n14a_4_8
  · exact n14a_4_9
  · exact n14a_4_10
  · exact n14a_4_11
  · exact n14a_4_12
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_5_5 : Region 14 n14a_mask [5,5] 40 5 32 none :=
  of_certs (hn:=by decide) [
  0xa9b8c7695a47c4683d3782db691d42c0b51a052130,
  0xc8b9a4a64795c7683d3782db691d42c0b51a052130,
  0xd3c764a59b82a97864c837db691d42c0b51a052130,
  0xd3c76a59b829a4c8746837db691d42c0b51a052130,
  0xd3c4a59782c8b9a6746837db691d42c0b51a052130,
  0xd3c4a9782c8b95a6746837db691d42c0b51a052130,
  0xd3c795a6828b9a4764c837db691d42c0b51a052130,
  0xa59b8c764c3d28749a6837db691d42c0b51a052130,
  0xa59b8c74d3c467829a6837db691d42c0b51a052130,
  0xa67c8b9582d3c479a46837db691d42c0b51a052130,
  0xdb5a97c8642130c3d4a1508b673c4782d2591b96a0,
  0xd28b673c4a591db9647c83a9786d42c0b51a052130,
  0xdb64a597c382d19a68c4739b876d42c0b51a052130,
  0xdb6a974c382d37c864a5919b876d42c0b51a052130,
  0xdb9a47c8295a687b64c38d37691d42c0b51a052130,
  0xdb9a4782c86a597b64c38d37691d42c0b51a052130,
  0xc8795a4c746b83db9a682d37691d42c0b51a052130,
  0xdb5a97c8642130b96a150c3d4a08b673c4782d2591,
  0xd28b673c4a591db964783a97c86d42c0b51a052130,
  0xdb6795a4c382d19a68c739b8746d42c0b51a052130,
  0xdb6a597c382d19a4c86739b8746d42c0b51a052130,
  0xd473c28b6a591db967838c79a46d24c0b51a052130,
  0xdb6795a4c382d1968c73a9b8746d42c0b51a052130,
  0xdb68795a4c3a91d28c769b83746d42c0b51a052130,
  0xdb6879a4c3d28c76a5919b83746d42c0b51a052130,
  0xdb695a4c7828c3d1976a9b83746d42c0b51a052130,
  0xd3867c4a91bd28795a69b8c3746d42c0b51a052130,
  0xdb968c47397c38b64ad2876a591d42c0b51a052130,
  0xd19a5b642873c0a674c2d38b95197c86bd4a052130,
  0xdb697c42a9b8768c3746d4a591d382c0b51a052130,
  0xc86a973db67c429b8746d4a591d382c0b51a052130,
  0xdb5a97c8642130d2c4a1c376b0a69150d47838b952,
  0xd24c378b6a591a968c74db9764d382c0b51a052130,
  0xdb95a6873c42a96b8c74d19764d382c0b51a052130,
  0xdb95a687c42a96b8c374d19764d382c0b51a052130,
  0xc4a596b873db9a68c742d19764d382c0b51a052130,
  0xd4c378b6a591a97c864769bd24d382c0b51a052130,
  0xc86bd4a5973c78b9a647691d24d382c0b51a052130,
  0xc86bd4a973c78b95a647691d24d382c0b51a052130,
  0xc86bd4a97378b95a64c7691d24d382c0b51a052130,
  0xdb68795a4c8b9a6473c7691d24d382c0b51a052130,
  0xd286b915a473c0c76a95b83d42c87964bd1a052130,
  0x9a67c24d38b51d286b95a473c0c87964bd1a052130,
  0xd476a59b8c3c7869a491d2837db642c0b51a052130,
  0xd4a59687c3c8b9a67491d2837db642c0b51a052130,
  0xc8b95a674d4a9687c391d2837db642c0b51a052130,
  0xd4a9b87c3c86a5974691d2837db642c0b51a052130,
  0xd15b6a974283c0db8695a4c73d2c8764b91a052130,
  0xd2837c4a96b51c3db86a59742d0c8764b91a052130,
  0xa96b8c74c4db9783d286a591d37642c0b51a052130,
  0xd195a6b83742c0d3c4a96782db97c864b51a052130,
  0xd374a596b82c0db9a6783c42d197c864b51a052130,
  0xdb695a4c3782d38b9a6742c0d197c864b51a052130,
  0xd195a6b83742c0d4a9687c3c82db9764b51a052130,
  0xd2c38b674a591db9a64c873d0c796824b51a052130,
  0xd3876b95a4c2c8bd19a6473d0c796824b51a052130,
  0xd374a59b68c2c0db879a64d1967c3824b51a052130,
  0xd374a9b68c2db8795a64c0d1967c3824b51a052130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_5_6 : Region 14 n14a_mask [6,5] 40 6 31 none :=
  of_certs (hn:=by decide) [
  0xb8c79a586bd476a4c37d24691d382c0b951a052130,
  0xd2473c86b5a91c796a4db8764d382c0b951a052130,
  0xd4c378b5a691a97c86476bd24d382c0b951a052130,
  0xd4c78b5a691a973c86476bd24d382c0b951a052130,
  0xd4c3786a91a5b8c796476bd24d382c0b951a052130,
  0xc864db5a973c78b6a47691d24d382c0b951a052130,
  0xc86bd4a973c78b5a647691d24d382c0b951a052130,
  0xdb8c79a64c4a5b68737691d24d382c0b951a052130,
  0xc86b5a473db879a64c7691d24d382c0b951a052130,
  0xc28374d195a6b0d3c768b9a42c87964db51a052130,
  0xc28673d4a59b0d19a6b83c742c87964db51a052130,
  0xd476a5b8c3c7869a491d2837db642c0b951a052130,
  0xd4a9687c3c8b5a67491d2837db642c0b951a052130,
  0xc8b5a974d4a687c3d2837691db642c0b951a052130,
  0xd196b5a42837c0db86a974c3d2c8764b951a052130,
  0xd2837c4a5b691c3db86a9742d0c8764b951a052130,
  0xd3c479a5b682db837c24a691d0c8764b951a052130,
  0xd196b5a47382c0db86a97c4678c3d24b951a052130,
  0xd2c38b5a64791db69a4c873d0c76824b951a052130,
  0xd38796b5a4c2c8bd19a6473d0c76824b951a052130,
  0xd2c374a5b8691db6a978c467c0d3824b951a052130,
  0xd2c478b5a691a973d0c864db67c3824b951a052130,
  0xd479a5b68c2db873c4a69167c0d3824b951a052130,
  0xd4796a5b8c3a91d2c7864c0db673824b951a052130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_5_7 : Region 14 n14a_mask [7,5] 40 7 30 none :=
  of_certs (hn:=by decide) [
  0xc4db9a683a5b8764c791d28d3742c0b6951a052130,
  0xa5b8c764c4db97836a91d28d3742c0b6951a052130,
  0xd19b5a467382c0db86a97c478c3d24b6951a052130,
  0xd2c38b5a46791db9a68c473d0c7824b6951a052130,
  0xd38679b5a4c2c8bd19a6473d0c7824b6951a052130,
  0xd19b5a647382c0d4a978c3c768bd24b6951a052130,
  0xd2c38b5a64791db9a4c873d0c76824b6951a052130,
  0xd3c8674a5b91c2db879a64d0c73824b6951a052130,
  0xdb5a97468c3d2c4a678b91d0c73824b6951a052130,
  0xd2c4678b5a91a68c0d374db97c3824b6951a052130,
  0xd3768b9a4c278c0db5a64d197c3824b6951a052130,
  0xd4a5b97c82d3c4786a91db837642c0b6951a052130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_5_8 : Region 14 n14a_mask [8,5] 40 8 29 none :=
  of_certs (hn:=by decide) [
  0xd3c24786a5b91db8c79a46b0d2837c46951a052130,
  0xd3c24a5b8791db9a68c746b0d2837c46951a052130,
  0xd3c8b5a4791c2d0b9a6876bd42837c46951a052130,
  0xd3c8b5a4791c2db9a6876b0d42837c46951a052130,
  0xdb974a68c3d2c78b5a916b0d42837c46951a052130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_5_9 : Region 14 n14a_mask [9,5] 40 9 28 none :=
  of_certs (hn:=by decide) [
  0xd4c79a68b0a5bd3c8746b91d2837c246951a052130,
  0xc378691d24a5b0d382c476b951a0db8c79a6452130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_5_10 : Region 14 n14a_mask [10,5] 40 10 27 none :=
  of_certs (hn:=by decide) [
  0xc2d1973864a5b0d3c478b6951a0db9a67c82452130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_5_11 : Region 14 n14a_mask [11,5] 40 11 26 none :=
  of_certs (hn:=by decide) [
  0xc2d374a15968b0d1978c46b5a0db9a67c382452130,
  0xd374c8691a5b0d15978b64a0c2db9a67c382452130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_5_12 : Region 14 n14a_mask [12,5] 40 12 25 none :=
  of_certs (hn:=by decide) [
  0xb597468c3d1a096b87c2d4a51c0db9a67382452130] (by rfl)

private theorem n14a_5 : Region 14 n14a_mask [5] 41 5 37 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14a_5_5
  · exact n14a_5_6
  · exact n14a_5_7
  · exact n14a_5_8
  · exact n14a_5_9
  · exact n14a_5_10
  · exact n14a_5_11
  · exact n14a_5_12
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_6 : Region 14 n14a_mask [6] 41 6 36 none :=
  of_certs (hn:=by decide) [
  0xa68b95c46783d47c82d379a1db52c0b69150a42130,
  0xd3c4678b95a1a97c864d2837db52c0b69150a42130,
  0xd3c768b95a1a978c464d2837db52c0b69150a42130,
  0xd3c86795a1a9b87c464d2837db52c0b69150a42130,
  0xc78b95a64d3c8679a14d2837db52c0b69150a42130,
  0xd3c78b95a19a68c4764d2837db52c0b69150a42130,
  0xd3c78b9a195a68c4764d2837db52c0b69150a42130,
  0x7c8b9a64d4c37682d38795a1db52c0b69150a42130,
  0xd1a9b5283764c0db86a597c38c2d47b69150a42130,
  0xd2c386479b5a18bd4c76a9528c0d37b69150a42130,
  0xd476a95b83c2db97c46825a18c0d37b69150a42130,
  0xd3c78b5a19a68c4764d2837db952c0b69150a42130,
  0xc8b5a974d3c786a164d2837db952c0b69150a42130,
  0xdb5a97c8642130c376b9150d2596a1c4d382b874a0,
  0xd3c259b8746a1db5a9768c4c0d2837b69150a42130,
  0xd3c4795b86a1db9a52c8764c0d2837b69150a42130,
  0xdb5a97c8642130b952d1a0c3769150a6b874c4d382,
  0xd38b952c746a1db5a978c4682d0c37b69150a42130,
  0xd3c46879b5a19a67c8bd254d0c2837b69150a42130,
  0xd3c786a9b52db8c46795a14d0c2837b69150a42130,
  0xd3c4768b95a1d2c879a64c0db52837b69150a42130,
  0xd476a59b8c3c2d1a97864c0db52837b69150a42130,
  0xdb9a647c82d4c378b5a1d3867952c0b69150a42130,
  0xd478b9a1c86a5976bd2c37d3825b0c469150a42130,
  0xc476a1d38259b0b68c79a58bd2c37d469150a42130,
  0xd4783c259b6a1db5a97c8268b0d37c469150a42130,
  0xc3d4786a9b52a1d0b8c7956bd2837c469150a42130,
  0xc3d478b9a52d1a68c795b06bd2837c469150a42130,
  0xd47c38259a6b0db9768c28b5a1d37c469150a42130,
  0xc3d4786a9b52a1db8c7956b0d2837c469150a42130,
  0xd3c795a68b0b9a1d2c8764db52837c469150a42130,
  0xd3c8679a5b0b87c2d1a64db952837c469150a42130,
  0xd3c8b679a1d2c786a5b04db952837c469150a42130,
  0xd4c38679a5b0b8c2d1a673db9528c7469150a42130,
  0xd4c3876b9a1a5b0d2c86bd379528c7469150a42130,
  0xd4c386b9a1d2c876a5b0bd379528c7469150a42130,
  0xd4c386b9a1a5bd2c876b0d379528c7469150a42130,
  0xc473869b52d1a0bd3c28764a9150a6b8c795d42130,
  0xdb95a68c2d38b679a1d4c7825b0c37469150a42130,
  0xc2d3874691a5b0d4c376a9b825197c86bd05a42130,
  0xd47386a19b52c0d3c46b879a51967c82db05a42130,
  0xa6b9783d4c251d19a5b86473c0967c82db05a42130,
  0xdb96a1528374c0d3c768b5a91978c2d46b05a42130,
  0xd38b5a19674c0db9a6873c25197c82d46b05a42130,
  0xd4c2876b95a1c79a683d25b0db8c37469150a42130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_7 : Region 14 n14a_mask [7] 41 7 35 none :=
  of_certs (hn:=by decide) [
  0xc86b9a4db873c2d4795a1d3825b0c769150a642130,
  0xd1a952c47386b0db978c3b5a4d28c769150a642130,
  0xd2c47386b59a1d0b978c3bd4a528c769150a642130,
  0xd2c3874a95b0d4c86b973bd1a528c769150a642130,
  0xd2c4a9786b0d1a5b8c3743db9528c769150a642130,
  0xd2c47386b5a1d0b978c3bd4a9528c769150a642130,
  0xd2c3874a9b0d1a5b68c4bd379528c769150a642130,
  0xd4c386b9a1d2c874a5b0bd379528c769150a642130,
  0xd4c386b9a1a5bd2c874b0d379528c769150a642130,
  0xc4769b5283d1a0d2c378b64a9150a68c795bd42130,
  0xd3879b5a4c2d0b68c74bd1a9528c3769150a642130,
  0xd2c786b9a1c4a5b0d38bd479528c3769150a642130,
  0xd38b9a4c2db68795a1d47c825b0c3769150a642130,
  0xc2d4738691a5b0d3c4a9b67825197c8bd05a642130,
  0xd38674a19b52c0d4c378b69a5197c82db05a642130,
  0xa9b6783d4c251d1968b5a473c097c82db05a642130,
  0xd19b68374a52c0a9678c4db5197c3d28b05a642130,
  0xd19a5b68374c0a4db9678c25197c3d28b05a642130,
  0xd3869b51a47c0c4db825a97391d2c876b05a642130,
  0x869bd37c4a52d479a15b83c091d2c876b05a642130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_8 : Region 14 n14a_mask [8] 41 8 34 none :=
  of_certs (hn:=by decide) [
  0xd4c879b6a1a95bd37452c38b0ad2869150c7642130,
  0xdb9a478c3d4c25b6a159738b0ad2869150c7642130,
  0xb52c4d197386a0a478c3db6951a9b82d05c7642130,
  0xd38c25b6a4791bd4c3786951a0a9b82d05c7642130,
  0xd3879152c4a6b0c869a5bd4739b82d1a05c7642130,
  0xd4c387915a6b0db52c869a4739b82d1a05c7642130,
  0xd152c47386a9b0d4a596b8c3bd28791a05c7642130,
  0xd387952c4a6b0c8b9a51d473bd28691a05c7642130,
  0xd4a9b873c251d38c4795a6b0bd28691a05c7642130,
  0xd4795a6b83c28c4a9b0d152bd378691a05c7642130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_9 : Region 14 n14a_mask [9] 41 9 33 none :=
  of_certs (hn:=by decide) [
  0xd374a6b91528c0c4db5a968397c2d1a05b87642130,
  0xd4a6b915283c0db5a968c47397c2d1a05b87642130,
  0x9bd374c86a51d4a96b5283c097c2d1a05b87642130,
  0xd374a6b9528c0c4d15a9683bd2c791a05b87642130,
  0xd4a6b95283c0d15a968c473bd2c791a05b87642130,
  0xd3c4795b6a1db9a52837c0a4d2c869150b87642130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_10 : Region 14 n14a_mask [10] 41 10 32 none :=
  of_certs (hn:=by decide) [
  0xb96837c2d1a0db6a5974c3a4d0c825195b87642130,
  0xdb95a6837c2b6974c3d1a0a4d0c825195b87642130] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14a_14 : Region 14 n14a_mask [14] 41 14 28 none :=
  of_certs (hn:=by decide) [
  0xc38259b674d1a0b873d2c4a69150db5a97c8642130] (by rfl)

private theorem n14a_root : Region 14 n14a_mask [] 42 3 42 none := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14a_3
  · exact n14a_4
  · exact n14a_5
  · exact n14a_6
  · exact n14a_7
  · exact n14a_8
  · exact n14a_9
  · exact n14a_10
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact absent_region (by rfl)
  · exact n14a_14

private def lib14_40_0 : List (List Nat) := [
  [10,10,10,10],
  [8,8,8,8,8],
  [4,12,12,12],
  [13,13,14],
  [5,5,5,5,5,5,5,5],
  [5,5,10,10,10],
  [4,9,9,9,9],
  [9,9,9,13],
  [5,5,5,5,5,5,10],
  [5,5,5,5,10,10],
  [12,14,14],
  [4,4,4,4,4,8,12],
  [8,8,12,12],
  [5,8,8,8,11],
  [4,4,4,4,4,4,8,8],
  [7,7,13,13],
  [4,4,4,4,4,4,4,12],
  [7,10,10,13],
  [8,8,11,13],
  [4,4,4,4,4,4,4,4,8],
  [4,4,4,4,4,4,4,4,4,4],
  [5,11,12,12],
  [7,11,11,11],
  [7,7,7,7,12],
  [7,7,12,14],
  [7,9,12,12],
  [6,8,13,13],
  [9,9,11,11],
  [3,12,12,13],
  [4,10,13,13],
  [9,10,10,11],
  [5,9,13,13],
  [5,9,12,14],
  [6,6,14,14],
  [8,10,11,11],
  [5,7,7,7,14],
  [5,11,11,13],
  [5,8,9,9,9],
  [4,4,6,13,13],
  [8,9,9,14],
  [3,9,9,9,10],
  [4,5,5,13,13],
  [4,4,4,14,14],
  [3,11,12,14],
  [5,5,5,11,14],
  [4,11,12,13],
  [5,5,8,11,11],
  [3,10,13,14],
  [5,5,5,12,13],
  [4,11,11,14],
  [9,9,10,12],
  [5,10,11,14],
  [3,11,13,13],
  [6,6,7,7,14],
  [6,6,7,7,7,7],
  [5,7,14,14],
  [5,7,7,7,7,7],
  [4,4,4,4,11,13],
  [4,7,7,11,11],
  [4,4,7,7,7,11]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem lib14_40_0_proof : Library 14 n14_40_mask lib14_40_0 :=
  check_library (hn:=by decide) lib14_40_0 [
    0xc86a9bd473d2c796b5a0a4c0b82591d387642051,
    0xc78b69a4db5a68c3d47382c0d259b0a197642051,
    0xd4c2876b95a1c79a683d25b0db8c37469150a420,
    0xc25a1d473869b0d28b6a4c79150a95bd3c876420,
    0xb6a95db974c867387c42d38b0c25a0a4691d2051,
    0xd4c79a5b82db68c374a1d3876952c0b9150a6420,
    0xdb95a68c2d38b679a1d4c7825b0c37469150a420,
    0xc4782d1a596b0db97c86a4a0d3c25195b8376420,
    0xd4a976b8c2c387469528db5a1d37c0b9150a6420,
    0xc4db5a9783d2c8b674a169528d37c0b9150a6420,
    0xc38259b674d1a0b873d2c4a69150db5a97c86420,
    0x83d4c79a6b52db9673c28746a591c8b0d150a420,
    0x87c3d4a69b52db68c47951a0a91d2c05b8376420,
    0xd3879b5a4c2d0b68c74bd1a9528c3769150a6420,
    0xdb9a67c4d3796b528746c382a591c8b0d150a420,
    0xd2c3874a6b591bd4c7968251a0a9b8c05d376420,
    0xa52c7864db91b695a976c473d382c8b0d150a420,
    0xd387952c4a6b0d15a9b8c74bd28691a05c376420,
    0xd4c79b68251a0a695bd3c874a91d2c05b8376420,
    0xc764d382b9a69786c473db52a591c8b0d150a420,
    0xa974d4c3c738b876a6958642d2c0b520db91a051,
    0x869bd37c4a52d479a15b83c091d2c876b05a6420,
    0xd2c478b9a51d4a68c795b0db691a05283c376420,
    0xd387c259b6a1bd479a54c82d0ab869150c376420,
    0xb52d47c38691a0db6a4c287951a9b8c05d376420,
    0xc4783db69a52d4a68c7915b09b82d1a05c376420,
    0xd38c25b6a4791bd4c3786951a0a9b82d05c76420,
    0xdb95a6874c3b697c82d1a0a4d0c25195b8376420,
    0xb597468c3d1a096b87c2d4a51c0db9a673824520,
    0xa6b9783d4c251d19a5b86473c0967c82db05a420,
    0xb6974c3d1a0a59bd2c786a4d0c825195b8376420,
    0xa9b6783d4c251d1968b5a473c097c82db05a6420,
    0xd38674a19b52c0d4c378b69a5197c82db05a6420,
    0xc382d195a476b0d378b964c251a0a97c865bd420,
    0x8c3d4a6b952d15a96874c0bd2c791a05b8376420,
    0xd1a952c47386b0db978c3b5a4d28c769150a6420,
    0xd3869b51a47c0c4db825a97391d2c876b05a6420,
    0xd38b9a4c2db68795a1d47c825b0c3769150a6420,
    0xa52c4db683791c3d28746a95b09b8c76d150a420,
    0xd1a95b8c376420c25a6b974bd2869150c783d4a0,
    0xd4c79a68b0a5bd3c8746b91d2837c246951a0520,
    0xa673c4d28b591d38746b9a52c097c86bd150a420,
    0xb64c387952d1a0c28bd374a691508c76b9a5d420,
    0xc2d374a15968b0d1978c46b5a0db9a67c3824520,
    0xd4a195b67382c0d3c478b9a52c8697bd150a6420,
    0xd38b5a19674c0db9a6873c25197c82d46b05a420,
    0xd3c8b679a52db59687c4a14d0c2837b9150a6420,
    0xc2d1973864a5b0d3c478b6951a0db9a67c824520,
    0xd4a95b67382c0d3c478b91a52c8697bd150a6420,
    0xdb96a1528374c0d3c768b5a91978c2d46b05a420,
    0xb6974c82d1a0a59bd3c786a4d0c25195b8376420,
    0xd19b68374a52c0a9678c4db5197c3d28b05a6420,
    0xd374c8691a5b0d15978b64a0c2db9a67c3824520,
    0xd1a952c47386b0db978c3b5a4d28a69150c76420,
    0xc86b9a4db873c2d4795a1d3825b0a69150c76420,
    0xc4769b5283d1a0d2c378b64a9150a68c795bd420,
    0xc86b9a4db873c2d4795a1d3825b0c769150a6420,
    0xa67382c4db591d3c786b9a529746c8b0d150a420,
    0xc3d478b9a52d1a68c795b06bd2837c469150a420,
    0xa674d3c8b91bd2c7869a52837c4695b0d150a420] (by rfl)

private def lib14_40_1 : List (List Nat) := [
  [4,4,10,11,11],
  [5,6,6,6,6,11],
  [4,4,5,5,9,13],
  [5,6,6,11,12],
  [5,6,7,11,11],
  [4,4,7,11,14],
  [7,8,12,13],
  [4,4,8,11,13],
  [3,3,11,11,12],
  [3,4,4,7,11,11],
  [8,9,11,12],
  [5,5,5,5,7,13],
  [3,9,14,14],
  [3,3,10,11,13],
  [3,4,11,11,11],
  [5,10,12,13],
  [7,7,7,8,11],
  [6,9,12,13],
  [4,4,4,6,9,13],
  [6,6,6,9,13],
  [6,6,6,11,11],
  [6,6,6,6,6,10],
  [6,6,7,10,11],
  [8,9,10,13],
  [4,7,8,10,11],
  [3,3,4,4,4,11,11],
  [3,5,5,5,11,11],
  [6,10,11,13],
  [5,5,6,11,13],
  [4,4,4,5,5,5,13],
  [4,6,8,11,11],
  [4,6,8,9,13],
  [3,7,7,11,12],
  [6,11,11,12],
  [3,5,10,11,11],
  [3,4,4,4,11,14],
  [3,3,5,7,11,11],
  [3,4,4,4,4,7,7,7],
  [4,6,6,12,12],
  [4,6,6,6,6,6,6],
  [3,4,4,4,4,10,11],
  [3,5,7,7,7,11],
  [3,5,5,13,14],
  [5,5,5,6,8,11],
  [5,5,5,7,7,11],
  [5,6,8,10,11],
  [4,6,6,6,6,12],
  [4,6,6,6,7,11],
  [4,6,7,11,12],
  [4,4,4,4,6,7,11],
  [5,7,7,10,11],
  [5,6,6,10,13],
  [3,3,5,5,11,13],
  [4,4,4,4,10,14],
  [3,8,9,9,11],
  [4,4,4,6,11,11],
  [5,5,6,6,6,6,6],
  [4,6,6,11,13],
  [5,5,7,10,13],
  [4,4,4,4,7,7,10]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem lib14_40_1_proof : Library 14 n14_40_mask lib14_40_1 :=
  check_library (hn:=by decide) lib14_40_1 [
    0xd4c8b679a52a687c3db5919b0c283746d150a420,
    0xd3c768b95a19a4c874d2837db52c0b69150a6420,
    0xa682c374db591d38c79a528b967c46b0d150a420,
    0xd4c28679b5a1db83c74a9528c0d37b69150a6420,
    0xc3d478b9a52db59768c4a1c0d2837b69150a6420,
    0xc4d28376a195b0c3db6879a529b8c746d150a420,
    0xa6b52c83d4791db0a4c786951a9b82d05c376420,
    0xc4d286791a5b0c783db6a9529b8c3746d150a420,
    0xd3c874a6b951d2c79a5b864c0a19673824db0520,
    0xdb59a6874c39b67c2d4a516973824c8b0d1a0520,
    0x9b6a4d3c8251c0db5a9687497c2d1a05b8376420,
    0xdb683c25974a1b8769a5c4d28d37c0b9150a6420,
    0xc378691d24a5b0d382c476b951a0db8c79a64520,
    0xa4673d2c8b591d4c786b9a51796a0c3824db0520,
    0xdb6a5974c83d4a9b8673c2c78246915b0d1a0520,
    0xd19a5b68374c0a4db9678c25197c3d28b05a6420,
    0xc74a59bd382d1a978c46b52d0ab869150c376420,
    0xd4c387915a6b0db52c869a4739b82d1a05c76420,
    0xa52c74d386b91db59a6782973c46c8b0d150a420,
    0xd259b68c374a1d0b5a9783bd4c28a69150c76420,
    0xd473c8b95a1d2c4a9786b03db528a69150c76420,
    0xdb8379a4c2d478c36b9528d1a5b0a69150c76420,
    0xd2c4a9786b0d1a5b8c3743db9528a69150c76420,
    0x9a6bd3c478251d0c869b5a497c2d1a05b8376420,
    0xd3c795a68b0b9a1d2c8764db52837c469150a420,
    0xd3c796a5b82d42c8376b918746a951c4a0db0520,
    0xdb6a974c382d37c864a5919b876d42c0b51a0520,
    0xd387952c4a6b0c8b9a51d473bd28691a05c76420,
    0xd283c4796b5a1c768bd4a9528c0d37b9150a6420,
    0xa52c38674db91b6a9597c46d3782c8b0d150a420,
    0xd3c786a9b52db8c46795a14d0c2837b69150a420,
    0xd38b952c746a1db5a978c4682d0c37b69150a420,
    0xd38679b5a4c2c8bd19a6473d0c7824b6951a0520,
    0xd4795a6b83c28c4a9b0d152bd378691a05c76420,
    0xd374a9b68c2db8795a64c0d1967c3824b51a0520,
    0xc3d287915a46b08c4db59a6739b86c742d1a0520,
    0xd4c876b5a91d3c7951a6829b83746c24a0db0520,
    0xc79b6a4db59673d4783c286429a51c8b0d1a0520,
    0xd476a95b83c2db97c46825a18c0d37b69150a420,
    0xa68b95c46783d47c82d379a1db52c0b69150a420,
    0xc3d4a6b9782db59683742c7649a51c8b0d1a0520,
    0xd476a59b8c3c7869a491d2837db642c0b51a0520,
    0xd19a5b642873c0a674c2d38b95197c86bd4a0520,
    0xd479a5b83c2c86bd1a4769528d37c0b9150a6420,
    0xd4a5b6783c29a1db86c479528d37c0b9150a6420,
    0xdb59768c4a1a9b87c3d254d0c2837b69150a6420,
    0xd3c4678b95a1a97c864d2837db52c0b69150a420,
    0xd3c768b95a1a978c464d2837db52c0b69150a420,
    0xd3c4795b86a1db9a52c8764c0d2837b69150a420,
    0xd4c38769b52c79a682bd3746a591c8b0d150a420,
    0xd2c4a9786b0d1a5b8c3743db9528c769150a6420,
    0xdb952c38674a1d4c79a5b828c0d37b69150a6420,
    0xd283c746b5a91a68c4d379519b876c24a0db0520,
    0xc46a1952d378b0db5a968c74b976c382d150a420,
    0xd3c8b5a4791c2db9a6876b0d42837c46951a0520,
    0xdb5a967c382d3786b952c4a19746c8b0d150a420,
    0xdb87c4b674a5c86973d259a1d382c0b9150a6420,
    0xd2c386479b5a18bd4c76a9528c0d37b69150a420,
    0xd3c2596b874a1db5a9768c4c0d2837b9150a6420,
    0xd4c79a6b529bd387682c3746a591c8b0d150a420] (by rfl)

private def lib14_40_2 : List (List Nat) := [
  [5,5,5,6,6,6,7],
  [4,5,5,8,9,9],
  [4,8,9,9,10],
  [4,4,4,9,9,10],
  [3,5,7,11,14]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem lib14_40_2_proof : Library 14 n14_40_mask lib14_40_2 :=
  check_library (hn:=by decide) lib14_40_2 [
    0xc4a5b83d2c874679528db69a1d37c0b9150a6420,
    0xdb59768c4d2c38b6a19a528746d37c0b9150a420,
    0xd4c386b9a1a5bd2c876b0d379528c7469150a420,
    0xa5bd387691b97c4d286a952c3746c8b0d150a420,
    0xd15b6a974283c0db8695a4c73d2c8764b91a0520] (by rfl)

private def lib14_40 : List (List Nat) :=
  lib14_40_0 ++ lib14_40_1 ++ lib14_40_2

private theorem lib14_40_proof : Library 14 n14_40_mask lib14_40 :=
  library_append (library_append (lib14_40_0_proof) lib14_40_1_proof) lib14_40_2_proof

private def lib14_44_0 : List (List Nat) := [
  [11,11,11,11],
  [5,13,13,13],
  [8,12,12,12],
  [3,8,11,11,11],
  [8,9,9,9,9],
  [10,11,11,12],
  [7,12,12,13],
  [4,4,4,4,4,4,4,4,4,4,4],
  [6,6,6,13,13],
  [4,7,11,11,11],
  [8,11,11,14],
  [3,5,12,12,12],
  [8,10,13,13],
  [4,4,9,9,9,9],
  [9,9,13,13],
  [7,11,13,13],
  [4,4,12,12,12],
  [5,5,8,13,13],
  [9,11,12,12],
  [4,10,10,10,10],
  [4,4,4,4,4,12,12],
  [10,10,12,12],
  [10,10,11,13],
  [5,11,14,14],
  [4,4,4,4,4,8,8,8],
  [6,12,13,13],
  [9,11,11,13],
  [4,4,10,13,13],
  [5,6,11,11,11],
  [5,7,8,12,12],
  [6,6,6,6,7,13],
  [4,13,13,14],
  [8,11,12,13],
  [4,8,8,8,8,8],
  [5,5,5,5,12,12],
  [3,4,4,4,4,4,4,4,13],
  [3,8,9,12,12],
  [3,4,4,4,4,4,4,4,4,4,5],
  [5,5,10,12,12],
  [8,8,8,9,11],
  [4,4,4,4,4,4,4,7,9],
  [4,4,4,4,4,4,4,5,11],
  [7,8,8,8,13],
  [4,4,4,8,12,12],
  [7,9,9,9,10],
  [10,10,10,14],
  [3,4,4,4,4,4,4,4,4,9],
  [3,8,8,11,14],
  [3,3,8,8,11,11],
  [3,8,8,8,8,9],
  [8,8,14,14],
  [3,5,9,9,9,9],
  [3,4,4,4,4,4,5,8,8],
  [3,10,10,10,11],
  [4,4,4,4,4,4,9,11],
  [4,5,5,5,5,5,5,5,5],
  [4,4,4,4,4,4,7,13],
  [4,4,4,4,4,4,4,4,5,7],
  [6,8,10,10,10],
  [4,9,9,9,13]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem lib14_44_0_proof : Library 14 n14_44_mask lib14_44_0 :=
  check_library (hn:=by decide) lib14_44_0 [
    0xcda2b398571635d7acb140948ab7261308d9c6543210,
    0xc658a2b349d719845dca7b13608dabc9357214062301,
    0xca2b35849d7189cbad543160936cd8a72140b7562301,
    0xb7d56ca8493cda754362b18d9cba2716098532140310,
    0xbc6357da27bac9d5618dc1b3940627a8413098543210,
    0x6ca85d7b39417a2bcd90631bad80435721c984562301,
    0x9361ca2b7d5806cb317a8d940badc984357214562301,
    0xdcbad8a7d985b753c931b172ca265634948061403210,
    0x7b2a85dc6394198dac1b357260d9cba7456130843210,
    0xb7d56ca8493cda754362b18d9cba2716098531403210,
    0x9ca2b3548d71604985dabc631cd93408a721b7562301,
    0xb7dca8945361b39d856c17a29cbad572348062140310,
    0x853617dabc940b3145d8906ca2cd9348a721b7562301,
    0x9cba7d854adc653b72ca89362b19d571348061403210,
    0x935d7b16ca840bcd98063417a23bad85721c94562301,
    0x9485d7bac1360b3408d9c617a2bcda89357214562301,
    0xa8dc65493b72ca7d985362b19cbad571348061403210,
    0xca7d8945362b193bcd58a271607bad9c658413043210,
    0x7d936cb2a841985dca7b3160bad80435721c94562301,
    0xb34589dca2c63948d7b19cbad571608a726531403210,
    0xa8d9c6543b72ca7d589362b1dcba7531948061403210,
    0x93b7d8ac6140bcd5806317a2bad9435721c984562301,
    0x93617a2bcd5806ca8d7b3140bad9435721c984562301,
    0xc63ba8049d5721b7dac9845623017a2bcd8534193160,
    0xbc658d93b7dc98a25da72634cab17531948061403210,
    0x7d8a2bc9365419485dca7b3160bad980435721c62301,
    0x93b7acd5841607d98a2bc631bad80435721c94562301,
    0xc63945d8a72b19d7bca2653480badc98571361403210,
    0xbc98d57a261b271cda84939d7bac6358065413043210,
    0xca849365d7b18d9cb357a260cdab2716985413043210,
    0x8a7d9c65432109857130948d53adcb72cab36162b140,
    0x945362b71cad806c93ba27d5841bcd98a75604312301,
    0x7d5489ca2b3614906cbad8531cd93408a721b7562301,
    0x98ab7d54bca75843cd9362b18da271609c6531403210,
    0xbc635498d7a2b39dca856271dab759c1608413043210,
    0xc9d8ab2634571bca7d56c9853ad72b32194806140310,
    0xcbad849365717ac9d543b162cd7b2a80698532140310,
    0xadc98d758935d6543ab72bc62ca71b32194806140310,
    0xbc62a8d94571b27adc165893d7bac906358413043210,
    0x8d7ac1b394056c9dab27bcd5361762a8413098543210,
    0xa85439d72bc98da7c65db362cab17531948061403210,
    0xad85439cb72d98a7c65db362cab17531948061403210,
    0x8dac1b2753940b7a89c63dcba26179d5841306543210,
    0xab7dc9854362c6539d8a72b1bcad5713948061403210,
    0xc635da72b1bacd8049389cb7162a9d75841306543210,
    0x936cb2a85d71408dca7b3160bad9435721c984562301,
    0xbc63458a2dc98dab79d537562ca71b32194806140310,
    0x8d75493b1ca26065d9cb7a843cdab271698532140310,
    0xad58936cb72c9d8a7562b1dcab341794532160840310,
    0xbcd7a8493d562bac975436c1b8da2716098532140310,
    0x9453617a2bcd806c93ba85d72140cad98431b7562301,
    0xb75dca893bc658d7a2bad9453619c172348062140310,
    0x6cbad853b7dc98a29345d7562ca71b32194806140310,
    0x7abcd5843629d8ac1b754da2b39061789c6532140310,
    0xa8543bc9d72b7ad89362c65dcab17531948061403210,
    0xabc98dca759d854b7da2c6271b165393480631403210,
    0xc65439d8a27b1dabc985cd7ab3627531948061403210,
    0xbc9d8a793458dc65ad72b362cab17531948061403210,
    0x7abcd85361b1ca89d57262ad7b39409c654130843210,
    0xc634985da72b18d9cab754dcb3906178a26531403210] (by rfl)

private def lib14_44_1 : List (List Nat) := [
  [4,4,4,8,8,8,8],
  [5,9,9,9,12],
  [5,5,5,5,5,5,5,9],
  [4,4,6,10,10,10],
  [8,8,9,9,10],
  [4,7,7,13,13],
  [9,10,11,14],
  [4,4,4,4,8,8,12],
  [6,8,8,11,11],
  [9,10,12,13],
  [6,10,14,14],
  [5,5,11,11,12],
  [5,7,8,8,8,8],
  [4,4,4,4,5,7,8,8],
  [5,5,5,9,9,11],
  [3,5,5,5,5,5,8,8],
  [4,4,4,7,8,8,9],
  [3,5,5,5,13,13],
  [4,6,10,10,14],
  [5,5,5,8,8,13],
  [3,3,5,5,5,5,5,13],
  [5,5,5,6,9,14],
  [5,5,5,5,5,6,13],
  [9,9,12,14],
  [3,8,10,10,13],
  [4,4,4,5,9,9,9],
  [4,4,8,8,8,12],
  [4,4,5,5,5,5,5,11],
  [4,5,5,5,5,9,11],
  [3,4,4,4,4,8,8,9],
  [7,7,7,7,7,9],
  [5,5,5,5,5,8,11],
  [8,9,13,14],
  [4,5,5,5,5,5,6,9],
  [7,7,7,9,14],
  [3,4,4,4,8,8,13],
  [4,4,4,4,4,7,8,9],
  [3,4,4,4,4,4,8,13],
  [3,3,3,5,5,5,5,5,5,5],
  [3,7,10,12,12],
  [7,9,14,14],
  [3,3,8,10,10,10],
  [3,5,5,5,5,5,5,5,6],
  [5,5,5,7,10,12],
  [4,4,4,4,7,8,13],
  [3,4,8,8,8,13],
  [3,4,7,10,10,10],
  [8,8,8,10,10],
  [5,6,7,13,13],
  [5,5,5,5,5,5,6,8],
  [5,5,5,5,5,5,14],
  [3,4,5,8,8,8,8],
  [4,4,5,5,5,5,5,5,6],
  [4,4,9,13,14],
  [8,8,8,8,12],
  [3,5,5,5,5,5,5,11],
  [5,7,10,10,12],
  [3,7,7,7,10,10],
  [4,4,4,4,4,5,7,12],
  [4,7,8,8,8,9]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem lib14_44_1_proof : Library 14 n14_44_mask lib14_44_1 :=
  check_library (hn:=by decide) lib14_44_1 [
    0x7bad9c65bca7d893cd5362b158a27134948061403210,
    0xc635849da7b1d89cab275dcb3906178a265413043210,
    0x9d758ac63bcda78945db3562ba2719c1608413043210,
    0xb7ad589c63ca8d7562b19dcba2713493548061403210,
    0x8d7ab1c94056cd93b27bcad5361762a8413098543210,
    0xc936548d7a2b18acb349d57260cdab71698531403210,
    0x985dc63b2a71408acb7d93160bad8435721c94562301,
    0xb3456c98da72d7b1ca85bcd9362a7531948061403210,
    0xca8d93572b163b7ad58940dcba26179c654130843210,
    0x93617a2bcd5806ca89d7b3140bad8435721c94562301,
    0x84935dca2b71609cb3658da72140ba89d75431c62301,
    0xc65493b2ad71bac9d857261dcb7a8906358413043210,
    0x9d7bca84ba756c93cd5362b18da27160985413043210,
    0xbacd85635d7a8934d9cb72ac62b17531948061403210,
    0xb398dc657a28acb7d945dab1726359c1608413043210,
    0x8d9cba7598adc654d7b35ca2b1723619348062140310,
    0xb7d58ac639dcba753d89c1b2a7265431948061403210,
    0xc65da8943b271b7548d9ca2361dcba79358062140310,
    0x936c1b27ad5480bacd758943bc9d8a26176531403210,
    0xb39456cd8a27189dacb75d7ab26359c1608413043210,
    0xc654398d7a2b1dabc9cd58a7b3627532194160840310,
    0x8ab7d9c65432109857261307ad841bcd53ca2b163940,
    0xbc639458da271d98ab7acd57b35629c1608413043210,
    0x98435d71b2ac608a7bcd9361403bad85721c94562301,
    0xcba8d54936271b2ac9d7561cda7b3480698532140310,
    0x89d7abc65a8dc93b72cad5362b175431948061403210,
    0xc65498da72b18ac93b75dcba26359d71348061403210,
    0x758ad9cb362dcab78945db2a71c65319348061403210,
    0xcb2a8d9457189cd7ab35dac65b726193480631403210,
    0xbc9d758a26cd89345dab72635ca71b32194806140310,
    0xc985d72b17adc635bca26178ab39409d841306543210,
    0xbca7d8945628ad93b75dc635ba2719c1608413043210,
    0x8dac9453b27160985d7abc63140cd9348a21b7562301,
    0xba7d89453d9ca85dcb2ac6571b726193480631403210,
    0x85da72b1c63940ba89cd753bca26179d841306543210,
    0xc654398da2b718abc9d75dca72635b32194806140310,
    0x89da7bc65dc93b2a8726345dcab17531948061403210,
    0xc6345d98a2b719cbad853cd7a7562b32194806140310,
    0xadc987bc659d8537ab32ca2b15d71494360621840310,
    0xc639458d7ab19cad572b3480bcd98a26176532140310,
    0x9485dac172b3608d9c612ab75340bcd7a89314562301,
    0x98acb7d563c9d857a2b13badc6271494532160840310,
    0xd98ab7ad857c945dbc653ca2b1723619348062140310,
    0xb2ac65498d717a85dcb3627bad9359c1608413043210,
    0xc65439d8a72b1d7bac985dcb362a7531948061403210,
    0xb39456cd8a27189dacb75d7ab26359c1234806140310,
    0xb7d8936ca2cda85723b19cba7126549d534806140310,
    0xb39dac65728d7ab1c940bcd5361762a8413098543210,
    0xc62ab3948d5719cad72b163580bcd98a765413043210,
    0x9da7bc63dca8578945db3562ba2719c1608413043210,
    0x8ab7d9c6543210bca718dc14ad572b26136394098530,
    0xba85dc63ad89cb72ca7562b19d712354934806140310,
    0x8acd75d9cba8945d7b362b2a71c65319348061403210,
    0x9362b71cad5480ba27d856c9431bcd98a75361403210,
    0x8d756cab3940ad9c1b27bcd5361762a8413098543210,
    0xca7d89453b18ab75d9c65bcda2723619348062140310,
    0xb2a8dc936571cad53b7261cba7d94806985413043210,
    0xa8549dcb72ca75d893b1dab26179c634806532140310,
    0xad7b34589c62bcd8a729365dcab17531948061403210,
    0xbcd7a8493d562bac975436c1b8da2716098531403210] (by rfl)

private def lib14_44_2 : List (List Nat) := [
  [4,5,8,13,14],
  [7,7,10,10,10],
  [6,7,7,11,13],
  [6,11,13,14],
  [6,9,9,10,10],
  [3,3,5,5,5,5,5,5,8],
  [4,4,4,4,8,9,11],
  [3,9,9,9,14],
  [3,4,4,4,4,4,9,12],
  [5,9,10,10,10],
  [5,5,5,5,5,7,12],
  [3,4,4,4,5,12,12],
  [6,6,8,8,8,8],
  [4,4,8,8,9,11],
  [5,7,9,9,14],
  [5,7,7,7,9,9],
  [7,8,8,9,12],
  [4,5,5,5,5,6,14],
  [3,7,10,10,14],
  [6,9,9,9,11],
  [7,7,7,10,13],
  [3,4,4,5,8,8,12],
  [5,8,8,11,12],
  [4,6,7,7,7,13],
  [6,6,7,12,13],
  [7,7,9,9,12],
  [3,8,8,12,13],
  [4,4,7,8,8,13],
  [5,5,7,9,9,9],
  [4,4,4,4,4,4,4,4,4,8],
  [3,7,7,9,9,9],
  [3,5,5,5,5,8,13],
  [5,5,5,5,6,9,9],
  [3,3,8,8,8,14],
  [5,5,5,5,11,13],
  [5,5,5,5,8,8,8],
  [3,5,5,7,12,12],
  [3,3,3,3,8,8,8,8],
  [3,5,6,10,10,10],
  [3,3,3,8,8,8,11],
  [3,4,4,4,5,8,8,8],
  [4,4,4,9,9,14],
  [3,6,8,8,8,11],
  [3,3,6,8,8,8,8],
  [5,8,8,9,14],
  [3,3,3,5,10,10,10],
  [3,4,4,4,4,5,8,12],
  [4,4,5,7,8,8,8],
  [5,5,6,14,14],
  [4,4,5,7,12,12],
  [4,4,4,4,9,9,10],
  [3,4,4,10,10,13],
  [4,4,4,4,4,5,8,11],
  [3,4,4,9,12,12],
  [4,4,5,10,10,11],
  [7,10,13,14],
  [4,5,5,5,11,14],
  [6,6,6,6,9,11],
  [7,8,9,10,10],
  [3,5,8,8,8,12]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem lib14_44_2_proof : Library 14 n14_44_mask lib14_44_2 :=
  check_library (hn:=by decide) lib14_44_2 [
    0x93456cd71b2a80cad94853b7261d89cba75631403210,
    0xb2ac985d71badc1627538a7bc639409d841306543210,
    0x65d72ac1b3940bc9d8a75362cdab7169854130843210,
    0x85493b2acd71609cb7a8d563140bad98435721c62301,
    0xacb7d85362c98ad572b1ab39406179dc654130843210,
    0xba7d8563adc989345dacb72c62b17532194160840310,
    0xb34589cad72d8a7b1c65bcd9362a7531948061403210,
    0x84572b1cad9360ba7d58943bcd8a26179c6532140310,
    0xb75436c98da27dcba8562d935ca71b32194806140310,
    0x9485d7bc63c98da753b19dcab271608a265413043210,
    0xbcd8a754936289dac65d7b35ba2719c1608413043210,
    0xb7d9c63458a2cbad89356271dca75b32194806140310,
    0x6cbad853b75d9ca2cd7a894193b17260456130843210,
    0xb39c658da727b1ca8945dcba26359d71348061403210,
    0x8ab7d9c6543210941cd5360485726130d893b2abca71,
    0xb7acd8493bc9d75362ad56c1b8a27160985413043210,
    0x8da72b36c94098ac1b753dcba26179d5841306543210,
    0x8ab7d9c6543210984130ad857bcd53ca26163940b271,
    0x936c1b27ad5480bacd758943bc9d8a26176532140310,
    0xa89cb7d5362b1cad8572ab39406179dc654130843210,
    0x85da72b36c94098ab1cd753bca26179d841306543210,
    0xb3456c98da72d7b1ca85bcd9362a7532194806140310,
    0xca27d58493b1bcd98a75362bad806179c65413043210,
    0xcb39458da7261d98ab75dca2b179c634806531403210,
    0x8a7d9c654321062b75d894130cdab361bca271935840,
    0x85d7ac1b39406cdab2753bc98a26179d841306543210,
    0xc948d563b2a71bcad93457261cd7ba80698532140310,
    0xb39456cd8a27189dacb75d7ab26359c1348061403210,
    0xb7a89dc63abc945d72cad8562b193571608413043210,
    0xb7a8dc939d586543ad72bc62cab17531948061403210,
    0xcd98a27b1dacb26175ba7d854939c634806532140310,
    0xc6549d8a723b1d7bac985dcb2a753619348062140310,
    0x9dcb7a854b398d7562dac635ba2719c1608413043210,
    0x8ab7d9c6543210cb2639419853b16048d57130dcaa72,
    0xb39456cd8a271bca7d985362dab759c1608413043210,
    0x9d8ac654b7ad5893bcd75362ba2719c1608413043210,
    0xb2a8d7549c616589dabc1723dca7b359348062140310,
    0xbac65d93bc98d7a2cda8534194572360b71621840310,
    0xb7ad589c63cb2a8d75619dcab1723493548062140310,
    0xb3456c9d7a28dac1b75dcba893594172360621840310,
    0x8d9cba7598adc653b7d54362ca271b32194806140310,
    0x8ab7d9c6543210627adc140948d571309853bca2b361,
    0xca8d94572b1da7b3985dcba26179c653480632140310,
    0xba85dc63bc98d7a2cad94571b7265341932160840310,
    0x84935dc1b7a260bcad98572d8ab36179c65413043210,
    0x98ad7bc653c9d857a2b15dcab3271494360621840310,
    0xa8d7bc934562bad98572dc635ca71b32194806140310,
    0xb75dac63ba7d8562cd98a271bc945319348061403210,
    0x94857adcb261308ab7d9c654321063b14098d53ca271,
    0xc945627d8ab16cb2ad985713dca7b359348061403210,
    0xb7ac658d93da89c1b27bcd54362a7531948061403210,
    0xc9d8a726543b1acb7d58932badc63571294806140310,
    0xb36589cda72a8d7bc629345dcab17531948061403210,
    0x7ba8d5439c62ca7d985632b1adcb3571294806140310,
    0xc9d7a8563b17b2acd8945dabc6271359348061403210,
    0x8d5349ca2b7160936c1bad758403bcd98a7214562301,
    0x8ab7d9c6543210985da7261303571bcd84163940bca2,
    0x8d9c654321062a894130dcba75cad7b1b36172935840,
    0xba8936cd728da7b1c94053bca26179d5841306543210,
    0xc65498da2b71dc93ba857acb16359d72348062140310] (by rfl)

private def lib14_44_3 : List (List Nat) := [
  [4,4,4,5,7,8,12],
  [4,6,7,13,14],
  [6,7,7,7,7,10],
  [7,8,8,10,11],
  [7,7,8,8,14],
  [4,4,7,8,9,12],
  [3,4,4,8,12,13],
  [7,7,7,7,8,8],
  [6,6,6,6,6,6,8],
  [3,4,4,4,8,9,12],
  [6,8,8,8,14],
  [3,3,10,14,14],
  [5,8,10,10,11],
  [3,4,5,5,9,9,9],
  [4,4,4,4,5,5,9,9],
  [5,5,8,8,9,9],
  [5,6,8,12,13],
  [5,6,10,10,13],
  [3,4,4,8,8,8,9],
  [4,5,6,9,10,10],
  [3,3,7,10,10,11],
  [5,6,6,6,8,13],
  [6,6,8,12,12],
  [3,3,4,4,10,10,10],
  [4,4,4,4,5,9,14],
  [6,7,7,10,14],
  [3,3,4,10,10,14],
  [3,3,4,7,7,10,10],
  [4,5,7,8,8,12],
  [3,13,14,14],
  [3,4,5,9,9,14],
  [3,4,5,8,12,12],
  [3,4,8,8,9,12],
  [6,6,6,6,8,12],
  [3,3,5,10,10,13],
  [3,5,8,8,10,10],
  [4,4,4,7,12,13],
  [3,3,7,7,10,14],
  [3,3,7,7,7,7,10],
  [4,4,8,9,9,10],
  [4,4,4,9,11,12],
  [3,9,10,10,12],
  [4,5,5,9,9,12],
  [3,7,8,8,8,10],
  [6,7,8,9,14],
  [3,3,3,5,6,8,8,8],
  [3,3,3,5,8,8,14],
  [4,7,9,10,14],
  [3,5,10,13,13],
  [3,6,7,14,14],
  [3,4,6,10,10,11],
  [3,6,10,11,14],
  [3,6,7,7,10,11],
  [3,3,3,4,4,7,10,10],
  [3,3,3,6,8,8,13],
  [4,7,7,7,9,10],
  [4,7,7,7,7,12],
  [3,7,9,12,13],
  [3,3,3,7,8,10,10],
  [3,4,4,6,7,10,10]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem lib14_44_3_proof : Library 14 n14_44_mask lib14_44_3 :=
  check_library (hn:=by decide) lib14_44_3 [
    0xc6539d8a72b1d7bac985dcb362a75431948061403210,
    0x9436ca2b17d580c93bad8457261bcd98a76531403210,
    0xbac9d75362a8dcb72ad56c1761b39409854130843210,
    0x8da7b36c94098ac1b2753dcba26179d5841306543210,
    0x8ad572b1c63940b7ac9853dcba26179d841306543210,
    0xb39456ca8d7189dcb2a75dab726359c1348061403210,
    0xb3456c9d8a271cab7d5893621bcda753294806140310,
    0xda7bc985c63572b1dca26178ab39409d841306543210,
    0x98543210d7bc659cad84b357a2cd93618ab140627130,
    0xcb2a85439d717bad89c65dca72635b32194806140310,
    0x63572b1ca8d940b7ad5893dcba26179c654130843210,
    0x62bcad894175308ab7d9c65432109361cd5840a72b31,
    0xca27d5893b1bcd8a75362bad94806179c65413043210,
    0xb7a89dc63abc945d72cad8562b175321934806140310,
    0xbacd985635da7bc9348d72ac62b17531948061403210,
    0x9d7abc654b758dac93dc1b263598a271608413043210,
    0xcb72ad9485361b3908d57ac62dc98ab1765413043210,
    0xc639485da72b1bac908d753bcd98a261765413043210,
    0xbacd98572a8d7b362ad539c17bc65432194806140310,
    0xba7d56c943cad98572b1bcd8a2617935480631403210,
    0xb39c657d8a289da7bc145dcab1726359432160840310,
    0xb27a84935dc61c98dab71cb362a9d758065413043210,
    0x62ba758941308ad9c654321093b7d840cd5361acb172,
    0xba275d9c61dac17b2658bcd7a8945343219360840310,
    0x8ab7d9c6543210948dcb130ca271da759853b3626140,
    0x635d8a72b1c940acb39d7562cdab7169854130843210,
    0x8ab7d9c654321075dca2b361627ad841309853cb1940,
    0xb3589cd7a2bca8d57261bad9417c6543219360840310,
    0xc65498da72b18ac93b75dcba26179d53480631403210,
    0x849d571ca2b3609358dcba726140b7da89c654321301,
    0x8ab7d9c6543210b2ad89361627584130bcd53ca71940,
    0x7ba8dc945362c6589d7a23b1bcad5712934806140310,
    0xb39456ca8d7189dcb2a75dab726359c1234806140310,
    0x8ad9c654321048d57130b7dca2ba7261bc1493985360,
    0xc9d8a726543b1acb7d58932badc63571294160840310,
    0xb7ad856c93cb2a894571dcab16359d72348062140310,
    0xb2ac654398d71c9d58ab72631bcda753948061403210,
    0x8ab7d9c6543210627ad84130b35dca27589361cb1940,
    0xb7d56ca8938dcba75d9c1b2a72635419432160840310,
    0xb756c98da28ac1b3945dcba726359d71348061403210,
    0xca758d9362b1b7da89c65435dcba2713948061403210,
    0xcd589362a7b1bca8d94572dab34806179c6532140310,
    0xcd894562ab71bc9da8572d7ac61b3593480631403210,
    0xa8549dcb72d893ba75dac62b179c1634806532140310,
    0x6c1b3572a8d940b7dac93625dcba7169854130843210,
    0x89dabc65b7d8ac93cd57a2b172354194360621840310,
    0x8ab7d9c65432109853b26048d5713063941dcaa72cb1,
    0x8ab7d9c6543210627589413093b2ad840bcd5361ca71,
    0xc63945d8a2b719d7acb1653480badc98572362140310,
    0x948dacb26175308ab7d9c6543210cd5893163b140a72,
    0xca8d94327b1ba7d589c62adcb3657129354806140310,
    0x8ab7d9c6543210627ad584130b2acd89361cb3571940,
    0xb39c658da727dc1ba8945bca26179d53480632140310,
    0xb7d9c658a2cbad894571dca7235b3419360621840310,
    0xc6572ba8d9341da7bc985dca23b17945360621840310,
    0xbacd849362bc9da75437d56c1b8a2716098531403210,
    0xbca7548d9362badc9437d56c1b8a2716098531403210,
    0x9d572ac1b3480bcd7a8549362bad89c6176532140310,
    0xb7549cd8a2cb3985da716cab14359d72360621840310,
    0x98d7bac653c9d58a72b1dcb362a75432194806140310] (by rfl)

private def lib14_44_4 : List (List Nat) := [
  [3,3,3,7,7,7,7,7],
  [3,3,3,7,7,10,11],
  [3,3,3,7,14,14],
  [3,6,7,7,7,7,7],
  [5,6,8,8,8,9],
  [4,6,7,7,10,10],
  [5,6,9,10,14],
  [3,3,3,8,13,14],
  [3,3,5,8,8,8,9],
  [3,3,8,8,9,13],
  [4,4,4,4,7,7,7,7],
  [5,8,8,10,13],
  [3,3,3,10,11,14],
  [4,4,7,7,7,7,8],
  [3,3,3,4,10,10,11],
  [6,7,7,8,8,8],
  [4,5,5,9,10,11],
  [6,7,10,10,11],
  [7,7,8,9,13],
  [6,8,8,9,13],
  [3,3,3,4,7,7,7,10],
  [3,3,3,4,7,10,14],
  [6,7,7,7,8,9],
  [3,6,7,7,7,14],
  [3,3,3,7,7,7,14],
  [3,4,6,7,7,7,10],
  [3,6,8,13,14],
  [3,6,7,8,10,10],
  [3,3,3,3,3,8,8,13],
  [3,6,6,8,8,13],
  [4,4,7,9,10,10],
  [3,5,8,14,14],
  [6,6,7,8,8,9],
  [4,4,4,4,7,7,14],
  [3,4,6,7,10,14],
  [3,5,6,8,8,14],
  [3,5,6,6,8,8,8],
  [5,7,7,8,8,9],
  [3,4,4,4,4,12,13],
  [4,4,4,4,7,9,12],
  [3,3,3,3,3,5,8,8,8]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem lib14_44_4_proof : Library 14 n14_44_mask lib14_44_4 :=
  check_library (hn:=by decide) lib14_44_4 [
    0x8dabc6598acd54c9357b1b3417a29d72360621840310,
    0xbc65498da71cd58a2b3417bac9359d72360621840310,
    0x62bcad571489308ab7d9c6543210cd85361a72b31940,
    0x8dcba75b7dac62c98a271b1654939d53480632140310,
    0xba75d8493bcd98a27dac62b179c16358065413043210,
    0xa8549dcb72ca75d893b1dab26179c634806531403210,
    0x8ab7d9c6543210627589413093b2ad840cd5361bca71,
    0x9458dac172b360b7d56c98a23419dcba753621840310,
    0xbacd98572a8d7b362ad539c17bc65432194160840310,
    0xcb72a89d56341ba758dc93dac62b1794532160840310,
    0x89dac65ba7d543a8dcb72c9362b17531948061403210,
    0xca7d5849362b1a89dcb3572bad806179c65413043210,
    0x941cd758a2b36098da7bc65435d9cab1723621840310,
    0x98abcd54d7ac639d857b2ab3562719c1348061403210,
    0xb756cda894358d7a2bc14d9cab172359360621840310,
    0x6cab7d53bcda7562c9d8a27161b39409854130843210,
    0xcd9458ab271ad89cb7562d7ac61b3593480631403210,
    0xc9d8ab26571bca27d5361cda7b394069854130843210,
    0x85da72b36c94098ac1b753dcba26179d841306543210,
    0x6357b1ca8d940b27ad5893dcba26179c654130843210,
    0x98ad7bc6548d9c175dca2b35ba723419360621840310,
    0x8ab7d9c65432106275d841307a2b3619853dcacb1940,
    0xbacd75362a8d9cb72ad56c1761b39409854130843210,
    0x8ab7d9c6543210b26394198dc1604857130d53bcaa72,
    0x8ab7d9c654321062b394198d53604857130dcaa72cb1,
    0xb7acd98563d8ab275da26c17bc943219354806140310,
    0x93456cd71b2a80cad94853b7261d89cba75632140310,
    0xb7ad856c93ca894572b1dcba26179d53480632140310,
    0xcba27d8936541d906ca857adc9435b32b71621840310,
    0xc6572a8d943b1da7bc985dcab2617935480632140310,
    0xb7ac658d93bcd75498a2dab1726359c1348061403210,
    0x948dacb26175308ab7d9c6543210cd5893b163140a72,
    0x9c65432108d7b394062a84130bcd536189da75cab271,
    0x8ab7d9c6543210941726048dc130da759853bca2b361,
    0x8ab7d9c654321062a7584130cad5361bcd893b271940,
    0x8ab7d9c6543210cad893619485713062b140bcd53a72,
    0xba8dc943bc65d7a2cad98571b7236193548062140310,
    0xbc9da756248dcab397d536c1b8a27160985413043210,
    0xb2ac654398d71c9d58a7b3621dcba753294806140310,
    0xc9345d8a72b189d7bac65dcb362a7531948061403210,
    0xd7abc985a8dc6572cad9354194360b32b71621840310] (by rfl)

private def lib14_44 : List (List Nat) :=
  lib14_44_0 ++ lib14_44_1 ++ lib14_44_2 ++ lib14_44_3 ++ lib14_44_4

private theorem lib14_44_proof : Library 14 n14_44_mask lib14_44 :=
  library_append (library_append (library_append (library_append (lib14_44_0_proof) lib14_44_1_proof) lib14_44_2_proof) lib14_44_3_proof) lib14_44_4_proof

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_3_3_3_3_3 : Region 14 n14_mask [3,3,3,3,3,3,3] 77 3 63 (some 42) :=
  empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_3_3_3_3_4 : Region 14 n14_mask [4,3,3,3,3,3,3] 77 4 62 (some 42) :=
  empty_screened (by rfl)

private theorem n14quick_3_3_3_3_3_3 : Region 14 n14_mask [3,3,3,3,3,3] 78 3 66 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_3_3_3_3_3_3_3
  · exact n14quick_3_3_3_3_3_3_4
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_3_3_3_4 : Region 14 n14_mask [4,3,3,3,3,3] 78 4 65 (some 42) :=
  empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_3_3_3_5 : Region 14 n14_mask [5,3,3,3,3,3] 78 5 64 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  286723] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_3_3_3_8 : Region 14 n14_mask [8,3,3,3,3,3] 78 8 61 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  274435] (by rfl)

private theorem n14quick_3_3_3_3_3 : Region 14 n14_mask [3,3,3,3,3] 79 3 69 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_3_3_3_3_3_3
  · exact n14quick_3_3_3_3_3_4
  · exact n14quick_3_3_3_3_3_5
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact n14quick_3_3_3_3_3_8
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_3_3_4 : Region 14 n14_mask [4,3,3,3,3] 79 4 68 (some 42) :=
  empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_3_3_5 : Region 14 n14_mask [5,3,3,3,3] 79 5 67 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  160795] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_3_3_6 : Region 14 n14_mask [6,3,3,3,3] 79 6 66 (some 42) :=
  empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_3_3_8 : Region 14 n14_mask [8,3,3,3,3] 79 8 64 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  160771,160805] (by rfl)

private theorem n14quick_3_3_3_3 : Region 14 n14_mask [3,3,3,3] 80 3 72 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_3_3_3_3_3
  · exact n14quick_3_3_3_3_4
  · exact n14quick_3_3_3_3_5
  · exact n14quick_3_3_3_3_6
  · exact empty_screened (by rfl)
  · exact n14quick_3_3_3_3_8
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_3_4 : Region 14 n14_mask [4,3,3,3] 80 4 71 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  238593,266241,267265,260097] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_3_5 : Region 14 n14_mask [5,3,3,3] 80 5 70 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  100361,100369,100371,100363,100353,168979,168971,230403,231427,162843,
  168961] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_3_6 : Region 14 n14_mask [6,3,3,3] 80 6 69 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  239619] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_3_7 : Region 14 n14_mask [7,3,3,3] 80 7 68 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  245761,270337,246785,243713,247809] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_3_8 : Region 14 n14_mask [8,3,3,3] 80 8 67 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  162819,252931,162853] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_3_10 : Region 14 n14_mask [10,3,3,3] 80 10 65 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  258049] (by rfl)

private theorem n14quick_3_3_3 : Region 14 n14_mask [3,3,3] 81 3 75 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_3_3_3_3
  · exact n14quick_3_3_3_4
  · exact n14quick_3_3_3_5
  · exact n14quick_3_3_3_6
  · exact n14quick_3_3_3_7
  · exact n14quick_3_3_3_8
  · exact empty_screened (by rfl)
  · exact n14quick_3_3_3_10
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_4_4 : Region 14 n14_mask [4,4,3,3] 80 4 70 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  9387,171,3211,207907,207873] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_4_5 : Region 14 n14_mask [5,4,3,3] 80 5 69 (some 42) :=
  empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_4_7 : Region 14 n14_mask [7,4,3,3] 80 7 67 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  212003,211969,210979,9353] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_4_8 : Region 14 n14_mask [8,4,3,3] 80 8 66 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  3221] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_4_10 : Region 14 n14_mask [10,4,3,3] 80 10 64 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  210945,19603] (by rfl)

private theorem n14quick_3_3_4 : Region 14 n14_mask [4,3,3] 81 4 74 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_3_3_4_4
  · exact n14quick_3_3_4_5
  · exact empty_screened (by rfl)
  · exact n14quick_3_3_4_7
  · exact n14quick_3_3_4_8
  · exact empty_screened (by rfl)
  · exact n14quick_3_3_4_10
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_5 : Region 14 n14_mask [5,3,3] 81 5 73 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  128009,81929,128017,81937,128019,81939,103433,81931,128001,81921,
  103443,3245,219147,49245,103435,225,166939,193,253955,156699,
  49179,49225,3261,219137] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_6 : Region 14 n14_mask [6,3,3] 81 6 72 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  166915,166949] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_7 : Region 14 n14_mask [7,3,3] 81 7 71 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  223267,223233,222243,222209,204835,49197,103459,204801,195619] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_8 : Region 14 n14_mask [8,3,3] 81 8 70 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  156675,254979,49155,156709,49189,49221,103425,3177] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_10 : Region 14 n14_mask [10,3,3] 81 10 68 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  195585,46227,147,5257] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_3_11 : Region 14 n14_mask [11,3,3] 81 11 67 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  137] (by rfl)

private theorem n14quick_3_3 : Region 14 n14_mask [3,3] 82 3 78 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_3_3_3
  · exact n14quick_3_3_4
  · exact n14quick_3_3_5
  · exact n14quick_3_3_6
  · exact n14quick_3_3_7
  · exact n14quick_3_3_8
  · exact empty_screened (by rfl)
  · exact n14quick_3_3_10
  · exact n14quick_3_3_11
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_4_4_4 : Region 14 n14_mask [4,4,4,3] 80 4 69 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  37929,47145,37927,35881,37921,47143,37917,35879,47137,37911,
  47133,35873,53287,134185,35869,47127,53281,91175,35863,131105,
  53277,170017,99357,131101,7225,53271,37893,50217,99351,36905,
  37891,37913,97309,91159,190497,47109,163863,11303,47107,97303,
  36903,35845,113693,144407,11297,35843,50209,35865,36897,113687,
  53253,50205,107543,36893,99333,131077,53251,53273,11287,99331,
  131075,99353,91141,20537,169987,163845,134149,195,9407,91139,
  284675,91161,97285,193541,201,163843,134147,144389,9355,97283,
  193539,97305,202757,44089,177157,191] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_4_4_5 : Region 14 n14_mask [5,4,4,3] 80 5 68 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  197645,144387,113669,216069,215053] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_4_4_6 : Region 14 n14_mask [6,4,4,3] 80 6 67 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  244737] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_4_4_7 : Region 14 n14_mask [7,4,4,3] 80 7 66 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  3191,3203,175139,139] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_4_4_8 : Region 14 n14_mask [8,4,4,3] 80 8 65 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  202755,190467,177155,107525,217093,3193] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_4_4_9 : Region 14 n14_mask [9,4,4,3] 80 9 64 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  13393,13457] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_4_4_10 : Region 14 n14_mask [10,4,4,3] 80 10 63 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  175105] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_4_4_12 : Region 14 n14_mask [12,4,4,3] 80 12 61 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  16441] (by rfl)

private theorem n14quick_3_4_4 : Region 14 n14_mask [4,4,3] 81 4 73 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_3_4_4_4
  · exact n14quick_3_4_4_5
  · exact n14quick_3_4_4_6
  · exact n14quick_3_4_4_7
  · exact n14quick_3_4_4_8
  · exact n14quick_3_4_4_9
  · exact n14quick_3_4_4_10
  · exact empty_screened (by rfl)
  · exact n14quick_3_4_4_12
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_4_5 : Region 14 n14_mask [5,4,3] 81 5 72 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  159749,197647,113667,216067,183301,52237,215055,11269] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_4_6 : Region 14 n14_mask [6,4,3] 81 6 71 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  271361,280577,235521] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_4_7 : Region 14 n14_mask [7,4,3] 81 7 70 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  108575,9401,3189,153613,108579,242693,108545,108551,101381,9303] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_4_8 : Region 14 n14_mask [8,4,3] 81 8 69 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  107523,217091,107545,50181,149509,36869,3171] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_4_9 : Region 14 n14_mask [9,4,3] 81 9 68 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  130061,60497,214029,226309] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_4_10 : Region 14 n14_mask [10,4,3] 81 10 67 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  19551,19561,5269] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_4_11 : Region 14 n14_mask [11,4,3] 81 11 66 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  149] (by rfl)

private theorem n14quick_3_4 : Region 14 n14_mask [4,3] 82 4 77 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_3_4_4
  · exact n14quick_3_4_5
  · exact n14quick_3_4_6
  · exact n14quick_3_4_7
  · exact n14quick_3_4_8
  · exact n14quick_3_4_9
  · exact n14quick_3_4_10
  · exact n14quick_3_4_11
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_5 : Region 14 n14_mask [5,3] 82 5 76 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  104457,117769,104465,76809,154633,117777,104467,76817,78857,154641,
  117779,104459,76819,78865,86025,54281,104449,76811,78867,86033,
  117761,161811,76801,78859,154625,54291,161803,220171,3161,78849,
  173,11377,11335,159795,159765,48221,3165,52299,86027,52287,
  11329,54283,205,11307,282627,281603,165915,161793,11311,203,
  11313,11315,249,183299,50203,277507,48155,11267,3099,220161,
  48201,11289,52303,36907,3175,3145,52239,52279,52231,233473,
  189,11285] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_6 : Region 14 n14_mask [6,3] 82 6 75 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  275459,248833,269313,237569,273409,234497,165891,272387,165925,236545] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_7 : Region 14 n14_mask [7,3] 82 7 74 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  119839,101423,119843,3225,119809,119815,101425,
  0x9b0a127654395ab22e704c81b3708e4a2c61950d2ea628417530eca86421a7900d6b4d9a37294fa5996e,
  153615,153655,101427,141347,54303,185,228353,48173,86051,3117,
  0x18d4f2ba9167931af6b4983a5572cfb596d0a9307a185635b904e7217522e8c6a10ea2c4680ca48260420,
  45137,141313,54307,141319,101397,
  0x1a5836728eb0d41a7890f2d6b4351ab38164ec9b3718f44c6a995b6e650122db97530680a2eca48260420,
  6201] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_8 : Region 14 n14_mask [8,3] 82 8 73 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  50179,48131,149507,50213,36867,3075,214019,48165,149529,36889,
  48197,3109,4325,65617,3141,4177,4241,94303,2193,86017,
  3079,2135,2153,2105] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_9 : Region 14 n14_mask [9,3] 82 9 72 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  0x1af58d730b1b38f74a989b714d27b492b6583907a54361b966e50c1522e8c6a12ea2c46810eca48260420,
  130063,14417,130103,130055,226325,26719,
  0x1a5634b26e90d8189aaf2d6714583af5370a8c7b18f614922a77b59304e2c0bb974c468130eca48260420,
  70713,18519,26681,18489,
  0x1af6d4a907385b0af8d2945635189ab66e32173a7834e50c195b712e8c6a1b9752a2c46810eca48260420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_10 : Region 14 n14_mask [10,3] 82 10 71 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  54273,46175,54279,21591,22585,21561,95,5207,5225,5177,
  0x18f6d27a90b458d5165aea92363ab3894e701b367942e50c191b752e8c6a1b96a2c4681530eca48260420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_3_11 : Region 14 n14_mask [11,3] 82 11 70 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  87,105,57,
  0x1a9072f4b6d85a6f714d2a98390bae9456321b387742e50c1b59728c6a11b8ea2c46817530eca48260420] (by rfl)

private theorem n14quick_3 : Region 14 n14_mask [3] 83 3 81 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_3_3
  · exact n14quick_3_4
  · exact n14quick_3_5
  · exact n14quick_3_6
  · exact n14quick_3_7
  · exact n14quick_3_8
  · exact n14quick_3_9
  · exact n14quick_3_10
  · exact n14quick_3_11
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_4_4_4 : Region 14 n14_mask [4,4,4,4,4,4] 78 4 60 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  7209,7207,58409,7201,42025,41001,7197,58407,57385,7191,
  55337,58401,42023,40999,24617,7283,20521,58397,42017,57383,
  40993,68649,55335,58391,42013,40989,57377,24615,7303,20519,
  55329,74791,120865,42007,57373,40983,24609,55325,7259,7173,
  120861,7195,7211,98333,57367,7219,7171,7205,7193,55319,
  73769,29737,176151,43049,98327,6185,24599,39977,32809,2089,
  18473,74775,58373,152603,152619,77853,106519,189473,61469,24691,
  152601,129047,20595,16417,58371,29735,145447,41989,43047,77847,
  6183,40965,61463,39975,32807,2087,18471,73761,29729,41987,
  42009,40963,43041,40985,57349,33821,24711,88087,39969,32801,
  2081,55301,73757,29725,120837,145437,176133,57347,121879,6173,
  98309,33815,55299,32797,24581,18461,20571,20485] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_4_4_5 : Region 14 n14_mask [5,4,4,4,4,4] 78 5 59 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  198669,120835,74757,24603,20507,208909,20523] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_4_4_7 : Region 14 n14_mask [7,4,4,4,4,4] 78 7 57 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  98307,43031,98329,106501,20531] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_4_4_8 : Region 14 n14_mask [8,4,4,4,4,4] 78 8 56 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  24579,24613,20483,39959,20517,68613,129029] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_4_4_9 : Region 14 n14_mask [9,4,4,4,4,4] 78 9 55 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  174093,13397] (by rfl)

private theorem n14quick_4_4_4_4_4 : Region 14 n14_mask [4,4,4,4,4] 79 4 64 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_4_4_4_4_4_4
  · exact n14quick_4_4_4_4_4_5
  · exact empty_screened (by rfl)
  · exact n14quick_4_4_4_4_4_7
  · exact n14quick_4_4_4_4_4_8
  · exact n14quick_4_4_4_4_4_9
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_4_5 : Region 14 n14_mask [5,4,4,4,4] 79 5 63 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  198671,74755,74777,184325,68635,68651,87053,208911] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_4_6 : Region 14 n14_mask [6,4,4,4,4] 79 6 62 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  219] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_4_7 : Region 14 n14_mask [7,4,4,4,4] 79 7 61 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  256045,279597,239,106499,285699,106521,77829,9301,221189] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_4_8 : Region 14 n14_mask [8,4,4,4,4] 79 8 60 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  68611,129027,68645,61445,129049,2163,44037] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_4_9 : Region 14 n14_mask [9,4,4,4,4] 79 9 59 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  164877,174095,60501,225285] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_4_10 : Region 14 n14_mask [10,4,4,4,4] 79 10 58 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  227] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_4_11 : Region 14 n14_mask [11,4,4,4,4] 79 11 57 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  115] (by rfl)

private theorem n14quick_4_4_4_4 : Region 14 n14_mask [4,4,4,4] 80 4 68 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_4_4_4_4_4
  · exact n14quick_4_4_4_4_5
  · exact n14quick_4_4_4_4_6
  · exact n14quick_4_4_4_4_7
  · exact n14quick_4_4_4_4_8
  · exact n14quick_4_4_4_4_9
  · exact n14quick_4_4_4_4_10
  · exact n14quick_4_4_4_4_11
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_5 : Region 14 n14_mask [5,4,4,4] 80 5 67 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  1203,14515,87115,13395,31869,27731,1181,184323,171013,173061,
  61467,44059,87119,44075,87055,87047,1271,1109] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_6 : Region 14 n14_mask [6,4,4,4] 80 6 66 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  66637,14493,231,31821] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_7 : Region 14 n14_mask [7,4,4,4] 80 7 65 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  9335,9347,77827,221187,77849,150533,44083,9337,
  0xd67a9234590a17ab382e704c815b3708e4a2c61b950d2ea6284197530eca86421278fb016f4b8d49a562] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_8 : Region 14 n14_mask [8,4,4,4] 80 8 64 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  61443,61477,44035,225283,44069,88069,136197,224269,4181] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_9 : Region 14 n14_mask [9,4,4,4] 80 9 63 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  13325,164879,27661,164871,115771,
  0x17ab382e704c815b3708e4a2c61b950d2ea6284197530eca86420d67234590a1294b63b018f4da987af64] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_10 : Region 14 n14_mask [10,4,4,4] 80 10 62 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  27707] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_11 : Region 14 n14_mask [11,4,4,4] 80 11 61 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  85,
  0x1a548eb0736d83ab5092ce7856189b0f2ac76341b3916f4c4a77b58e50122bb97530c862ec280a8406420,
  16475] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_4_12 : Region 14 n14_mask [12,4,4,4] 80 12 60 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  16389] (by rfl)

private theorem n14quick_4_4_4 : Region 14 n14_mask [4,4,4] 81 4 72 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_4_4_4_4
  · exact n14quick_4_4_4_5
  · exact n14quick_4_4_4_6
  · exact n14quick_4_4_4_7
  · exact n14quick_4_4_4_8
  · exact n14quick_4_4_4_9
  · exact n14quick_4_4_4_10
  · exact n14quick_4_4_4_11
  · exact n14quick_4_4_4_12
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_5 : Region 14 n14_mask [5,4,4] 81 5 71 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  114697,89097,114705,89105,114707,89107,64521,89099,114689,89089,
  64531,1149,178187,64523,4221,227341,14461,31827,1101,171011,
  173059,212997,88091,16411,13387,122893,13377,13375,115775,27711,
  178177,16427] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_6 : Region 14 n14_mask [6,4,4] 81 6 70 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  9397,64547,15437,14413,64573,26701,64513,77] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_7 : Region 14 n14_mask [7,4,4] 81 7 69 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  259117,10359,119,9385,27679,150531,189443,150553,121861,10371,
  16517,276481,16435,27683,131] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_8 : Region 14 n14_mask [8,4,4] 81 8 68 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  88067,136195,88101,16387,136217,16421,16409,13391,224271,115791,
  16525,10361,135] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_9 : Region 14 n14_mask [9,4,4] 81 9 67 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  13327,13413,13333,13319,27663,115719] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_10 : Region 14 n14_mask [10,4,4] 81 10 66 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  27649,121,27655] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_4_11 : Region 14 n14_mask [11,4,4] 81 11 65 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  0xd67a9234590a17ab382e704c815b3708e4a2c61b950d2ea6284197530eca8642127894b63b018f4daf64] (by rfl)

private theorem n14quick_4_4 : Region 14 n14_mask [4,4] 82 4 76 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_4_4_4
  · exact n14quick_4_4_5
  · exact n14quick_4_4_6
  · exact n14quick_4_4_7
  · exact n14quick_4_4_8
  · exact n14quick_4_4_9
  · exact n14quick_4_4_10
  · exact n14quick_4_4_11
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_5 : Region 14 n14_mask [5,4] 82 5 75 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  56329,56337,95241,140297,90121,56339,95249,56409,140305,90129,
  56331,95251,56423,79881,90131,56321,95243,180243,79889,90123,
  19473,95233,133125,180235,140289,17491,90113,19475,34821,203787,
  105477,1267,19545,1107,79883,151565,199693,17421,122943,17467,
  227343,14419,262145,19467,38917,72709,1207,203777,138253,212995,
  73733,29701,137229,118789,33819,33835,167949,145413,60491,122895,
  1269,122887,62477,60481,1037,31807,19559,1083] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_6 : Region 14 n14_mask [6,4] 82 6 74 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  199,213,215,235,197,146463,146433,146439,66613,250881,
  185345,217,185351,14519,181,31797,79933,
  0xd6fa7234590a17ab382e704c815b3708e4a2c61b950d2ea6284197530eca86421298763b00b65a958f4c,
  79873,19631,
  0x1a72caf6550983a92b078ed436185b0d6b48e3214fb3966c8a501b59172e4c2b9b7530e680ca628406420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_7 : Region 14 n14_mask [7,4] 82 7 73 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  92173,241709,9369,66591,96269,240641,66595,9265,10357,148493,
  66561,5237,117,66567,121859,33925,121881,43013,139269,169,
  0xd6fa9234590a17ab382e704c815b3708e4a2c61b950d2ea6284197530eca86421a7894b632765b018f4c,
  45069,102413,232449,19491,31779,15419,9237,6149] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_8 : Region 14 n14_mask [8,4] 82 8 72 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  33795,33829,33817,33933,116827,116741,39941,65549,51213,4109,
  94221,12301,31823,94267,
  0x17ab382e704c815b3708e4a2c61b950d2ea6284197530eca86420d67234590a101294b63b65a78d4faf88,
  12347,10339,
  0x1a5092d6b4e783a6d512ae985618f3ab0762c941b59370ec4a991b6e54320db9752680a2f0ca628406420,
  32773,2053] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_9 : Region 14 n14_mask [9,4] 82 9 71 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  85005,14349,70669,60437,60423,14395,85091,19517,26683,70661,
  26629,18437] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_10 : Region 14 n14_mask [10,4] 82 10 70 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  19457,31745,22587,22533,21509,5219,59,5211,5125] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_11 : Region 14 n14_mask [11,4] 82 11 69 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  99,91,5] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_4_13 : Region 14 n14_mask [13,4] 82 13 67 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  31751] (by rfl)

private theorem n14quick_4 : Region 14 n14_mask [4] 83 4 80 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_4_4
  · exact n14quick_4_5
  · exact n14quick_4_6
  · exact n14quick_4_7
  · exact n14quick_4_8
  · exact n14quick_4_9
  · exact n14quick_4_10
  · exact n14quick_4_11
  · exact empty_screened (by rfl)
  · exact n14quick_4_13
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_5_5_5 : Region 14 n14_mask [5,5,5,5] 80 5 64 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  63497,111625,112649,83977,93193,63505,111633,155657,158729,112657,
  157705,82953,83985,80905,93201,75785,63507,111635,155665,172041,
  158737,17417,63577,112659,157713,82961,83987,80913,93203,75793,
  63499,23561,1033,59401,126985,71689,109577,12297,67593,46089,
  22537,82963,83979,80915,93195,75795,63489,23569,1041,111617,
  126993,71697,17551,109585,12305,67601,112641,22545,82955,83969,
  133167,133169,133171,34927,1167,80907,93185,17505,75787,132115,
  34881,23571,1043,34859,59411,155649,71699,34863,34865,12431,
  34867,158721,12307,67603,46099,157697,34837,1121] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_5_5_6 : Region 14 n14_mask [6,5,5,5] 80 6 63 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  28905,72827,241,28849,72831,72833,207,82945,201739] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_5_5_7 : Region 14 n14_mask [7,5,5,5] 80 7 62 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  105519,105521,
  0x189a730b4ed65ab2d956708e5b36af186c943af714ca92381b793451b8e36152e6a4c10c2a06284086420,
  105523,209,39023,1261,
  0x1a54367092ead816f87a94d2b0583ab5136c8e593b1614ec6a97b590e720c4bb97522f0c2a06284086420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_5_5_8 : Region 14 n14_mask [8,5,5,5] 80 8 61 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  80897,17471,196619,12385,10329] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_5_5_9 : Region 14 n14_mask [9,5,5,5] 80 9 60 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  75777,14433,132107,38977,
  0x14b6f8d29a705ab2789516ce5b734e90ac58395b12ea8c761b390e6a56341b974c122f0c2a06284086420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_5_5_10 : Region 14 n14_mask [10,5,5,5] 80 10 59 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  23563,1035,38955] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_5_5_11 : Region 14 n14_mask [11,5,5,5] 80 11 58 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  89,97,72747] (by rfl)

private theorem n14quick_5_5_5 : Region 14 n14_mask [5,5,5] 81 5 69 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_5_5_5_5
  · exact n14quick_5_5_5_6
  · exact n14quick_5_5_5_7
  · exact n14quick_5_5_5_8
  · exact n14quick_5_5_5_9
  · exact n14quick_5_5_5_10
  · exact n14quick_5_5_5_11
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_5_6 : Region 14 n14_mask [6,5,5] 81 6 68 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  28795,28799,28801,28699,59403,126987,172033,177,28715] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_5_7 : Region 14 n14_mask [7,5,5] 81 7 67 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  1137,38959,1095,17439,38961,
  0x189a72d0b4f65ab2f8d670945b5316ae8c783951aeca92361b73904a6e341b974c130e4c2a06284086420,
  17443,151567,151607,38963,72749,1135] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_5_8 : Region 14 n14_mask [8,5,5] 81 8 66 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  109579,23579,199695,10333,62539,1099,17409,93,17429,17415] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_5_9 : Region 14 n14_mask [9,5,5] 81 9 65 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  0x1a92b6f14d879172fab49a385752d181a543673b596cae33b8ec8b0174e904a6c1306e4c2a06284086420,
  62527,67595,1089,1087] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_5_10 : Region 14 n14_mask [10,5,5] 81 10 64 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  46091,22539,38933,1175] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_5_11 : Region 14 n14_mask [11,5,5] 81 11 63 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  23625] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_5_12 : Region 14 n14_mask [12,5,5] 81 12 62 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  0x1a34d2b08e76581a9278d70eb45b18372f48ca793af6150c4a97b58ec70122bb975304e2c0a6284086420] (by rfl)

private theorem n14quick_5_5 : Region 14 n14_mask [5,5] 82 5 74 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_5_5_5
  · exact n14quick_5_5_6
  · exact n14quick_5_5_7
  · exact n14quick_5_5_8
  · exact n14quick_5_5_9
  · exact n14quick_5_5_10
  · exact n14quick_5_5_11
  · exact n14quick_5_5_12
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_6 : Region 14 n14_mask [6,5] 82 6 73 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  28835,5243,123,8305,8263,205855,28837,8303,205831,1183,
  1133,1131,110645,135195,223,5247,127,1091,25713,25671,
  110623,200735,5249,129,110613,110599,249859,194587,69659,69705,
  211,200711,1077,251905,1179,201729] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_7 : Region 14 n14_mask [7,5] 82 7 72 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  29743,118831,113,1071,2119,138255,138295,21575,
  0x1a78950ed2b65a92f6d0b45818d4ebb072163b39166e8a14395b7308c4fb97522f04a2c60ca6284086420,
  71,283651,29747,
  0x1a94b2f16d838f56bb1296793a54cfb5972d0af07a185635b908e7217522e4c8a104a2c60ca6284086420,
  118835,221,1073,1055,73731,29699,29721,2159,1157,
  0x1af90d374bb6f134d8993b14ed67b492b6583945a72361b970ae3412e704c8a108e4a2c60ca6284086420,
  137231,137271,118805,1059,
  0x18728eb0d43a5618f2d6ba709458372b41b0ec9b3914f66c4a995b704e6122db975300a2eca6284086420,
  23597,
  0x1a7092b4f8d656fb2d0a985436ba3914ce72149b67922e50195b172e8c4a1b97530ea2c60ca6284086420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_8 : Region 14 n14_mask [8,5] 82 8 71 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  167939,116763,39963,23555,10267,2075,27,4171,167951,257025,
  23589,4161,4159,1103,1191,2113,196609,12439,10343,10313,
  2091] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_9 : Region 14 n14_mask [9,5] 82 9 70 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  0x1632785aeb490c1a98f4d30b67a38d7152ba19572e7193b6e3451b964c8a1528e4a2c610eca6284086420,
  62479,62519,62471,1039,132157,1125,132097,21569,
  0x1a8af8d350765ab1894d6e7236b291ae38541a793634e50c195b712e8c4a1b974a2c6130eca6284086420,
  18475] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_10 : Region 14 n14_mask [10,5] 82 10 69 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  23553,1025,21547,103,151,5163] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_11 : Region 14 n14_mask [11,5] 82 11 68 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  73,43] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_12 : Region 14 n14_mask [12,5] 82 12 67 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  1045] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_5_13 : Region 14 n14_mask [13,5] 82 13 66 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  1031] (by rfl)

private theorem n14quick_5 : Region 14 n14_mask [5] 83 5 79 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_5_5
  · exact n14quick_5_6
  · exact n14quick_5_7
  · exact n14quick_5_8
  · exact n14quick_5_9
  · exact n14quick_5_10
  · exact n14quick_5_11
  · exact n14quick_5_12
  · exact n14quick_5_13
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_6 : Region 14 n14_mask [6] 83 6 78 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  30829,30827,192543,30787,192519,181315,8351,8301,8299,30773,
  163,8259,30767,30769,30751,218143,30741,30727,218119,8245,
  181269,8347,8239,8241,8223,8325,142403,8207,5281,161,
  8213,8199,15469,6253,15467,6251,147487,124981,206879,278531,
  165,15427,147477,147463,
  0xd6729a34590a17ab382e704c815b3708e4a2c61b950d2ea6284197530eca864212365b016f8d4baf4986,
  135171,135205,126005,206855,25653,18499,
  0x17ab382e704c815b3708e4a2c61b950d2ea6284197530eca86420d67234590a101294b63baf4d89a78f64,
  25755,22595,
  0x1a58716af294c3a72cb50e9836193ab08ce76541b18d6f4320995b72a6104fb97530c4a2ec62840a86420,
  186403,186369,124959,25647,268291,209955,261123,209921,124929,124935,
  25649,25631,229379,69677,59427,15413,6197,263169,71715,194563,
  265219,69635,125955,69669,69701,14389,59453,26677,59393,53,
  142337,142357,25615,126977,71741,71681,125953,175,5307,187,
  125959,25621,25607,
  0x3a6d0eb299404cf42a1277908581a8714d2e3655af833016c8a56e8260d9b34b0957386e5aac211b6a64] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_7 : Region 14 n14_mask [7] 83 7 77 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  92163,191533,92175,92215,92161,143391,15407,6191,191491,2095,
  0x1a930f4b6d87a57518f2b71a3934cfb5972d08fa18943673b8506ea1722e4c8144a2c610a62840ca86420,
  123935,21551,47,96259,188461,153,
  0x1ab516f389b2d74f187af8d52b63b7309438595b0ce921b96506ea16722e4c8144a2c610a62840ca86420,
  96271,96311,96257,143361,143367,15409,15391,6193,6175,188419,
  264195,187437,12319,32799,2097,2079,
  0x1a78563490ed2a1a98f30d6b45b14d936eb53a38166fb7590722fb9704c81528e4a2c610a62840ca86420,
  148495,148535,123965,6195,123905,123911,22559,21553,
  0x1a9870d4f36a5ab512ce765836f93a6c50941b18d6344e92195b70eb22c81b975260a2f0a62840ca86420,
  49,43011,139267,102403,6147,139289,43009,187393,51245,6169,
  182333,182273,2099,12323,10285,
  0x1b97530eca8642151a78f72afa992765493a58163583b6d0a1522e704c8108e4a2c60d2ea62841b4d916a,
  45071,
  0x1658d2f0ba94387af6d4b309738f51a0b45a381673b75906e33b9704c81528e4a2c610cea62840ca86420,
  45157,45111,45117,102415,45057,102455,102401,21555,179201,15361,
  5165,179207,45,15381,15367,6165,6151,
  0x165870ba8d2f4345a76d188eb216b4d83b26e5018f71b4922c6a1b73950ec4a281b9753084062eca86420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_8 : Region 14 n14_mask [8] 83 8 76 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  116739,39939,51203,94211,10243,32771,2051,26627,18435,3,
  51237,39937,51367,109569,51269,10277,2085,2073,4175,65551,
  4237,65637,4165,65597,51215,65537,18457,10309,37,4111,
  4197,4151,4157,4097,4117,4103,12303,94215,12289,69,
  12309,12295,10247,32789,32775,
  0x1a5094d8e72b636d2eb07a983413ab518764e8c1b16f45922c6a195b730ec4a281b975284062f0ca86420,
  2069,2055,
  0x185ab4c7092f638d650b3a6e9417189a344ea721b14f87722a4c17b5930ec280bb9752c84062f0ca86420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_9 : Region 14 n14_mask [9] 83 9 75 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  0x16f89a72b0d45af5138d6ba38773491a594a16337a1906e35b9704c81528e4a2c60d2ea628410eca86420,
  0x1a98d0b34f678fab6d5127a39365491a594a16337a1906e35b9704c81528e4a2c60d2ea628410eca86420,
  0x1ab136f4d89af93490d67b1456b2783a594a16337a1906e35b9704c81528e4a2c60d2ea628410eca86420,
  0x195b70d2ea62841b97530eca864213908e4a2c618d4baf7298f49b2b67658327b00d63a550a142e704c80,
  85007,14351,70671,85047,84999,14343,67585,67591,70677,70663,
  0x170ae987a54d234f6583ab290c16d8fa952704a1b1936b42e6c8197b512e4c2a61b9566284130eca86420,
  26645,26631,18453,18439,
  0x187a50d492eb6384e916d2ba3416fa993506c4a1b18f456722c8195b730a2e60db974a6284130eca86420,
  0x1a34b6506d28f816d0987ab2e5419149af6722c5b163934c80a595b730a2e60db974ea6284130eca86420,
  0x1ab456c7098f23a76b2d148e5816fa927904c341b163934c80a595b730a2e60db974ea6284130eca86420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_10 : Region 14 n14_mask [10] 83 10 74 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  46081,22529,46087,22549,22535,21525,21511,
  0x172d0987a4eb436d4e92ba3850191a952f66c4a1af94570722c8193b750a2e60db96a62841530eca86420,
  0x1a72b4d08e583618f29ab6542c701af498772c50a3b39516c80a591b7522e60db96ea62841530eca86420,
  5141,5127,
  0x1a5872b4e90d63892fab654c70167a94392c50a1b37158e4a2c8191b7522e60db96ea62841530eca86420,
  0x1ab66d2e9438501a7098e56d4b234fa9278170c5b195362c80a593b750a2e60db96ea62841530eca86420,
  0x1ab28f456d0783a916b4c72e58167af89432c501b195362c80a593b750a2e60db96ea62841530eca86420,
  0x1908e54b2c7a361ab658f528d01af71498722c5b3834d670a09957b04a2e60db972ea62841530eca86420,
  0x1a6d092b654f81ab52c8e590163af71498722c5b3834d670a09957b04a2e60db972ea62841530eca86420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_11 : Region 14 n14_mask [11] 83 11 73 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  21,7,
  0x1a388e54b2d67016ba9058f4c7236fa7812950c5b371942c80a5975b0a2e60db92ea628417530eca86420,
  0x1a714d6b28e5838f654ba90c721af4987632c501b371942c80a5975b0a2e60db92ea628417530eca86420,
  0x1a3456b278e8d019092d67ab4e5af71498122c5b36394c70a09975b04a2e60db92ea628417530eca86420,
  0x1a790d6b28e543ab4f85672c901af71498122c5b36394c70a09975b04a2e60db92ea628417530eca86420,
  0x1ab6728f4590c18fa34b36c907a571498122e7b38374c50a09b596e4a2c611b8d2ea628417530eca86420] (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem n14quick_12 : Region 14 n14_mask [12] 83 12 72 (some 42) :=
  from_screened (hn:=by decide) (by decide) (by rfl) lib14_40_proof lib14_44_proof [
  0x129ab516d86e31a72b658f4c136fa543890a1593a36704c8197b48e4a2c61b90d2ea628417530eca86420] (by rfl)

private theorem n14quick_root : Region 14 n14_mask [] 84 3 84 (some 42) := by
  apply split_region (by decide)
  intro d hlo hn ht
  interval_cases d
  · exact n14quick_3
  · exact n14quick_4
  · exact n14quick_5
  · exact n14quick_6
  · exact n14quick_7
  · exact n14quick_8
  · exact n14quick_9
  · exact n14quick_10
  · exact n14quick_11
  · exact n14quick_12
  · exact empty_screened (by rfl)
  · exact empty_screened (by rfl)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem verified14 (m : Multiset Nat) (bound : ∀ d∈m,3≤d ∧ d≤14)
    (sm : m.sum=84) : Realizes 14 m :=
  patched (left:=42) (right:=42) (total:=84) (p:=n14a_mask) (q:=n14b_mask)
    (by decide) (by decide) (by decide) (by rfl) (by decide) n14a_root (complementary14 n14a_root)
    (show Region 14 (minusMatch 14) [] 84 3 84 (some 42) from n14quick_root) m bound sm

end OMA.AlspachEvenFinite

open OMA.AlspachEvenFinite

theorem OMA.solution : OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.H1 := by
  intro n hn hpos upper m hm hs
  obtain ⟨k, hk⟩ := hn
  have hcases : n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 ∨ n = 12 ∨ n = 14 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact verified2 m hm hs
  · exact verified4 m hm hs
  · exact verified6 m hm hs
  · exact verified8 m hm hs
  · exact verified10 m hm hs
  · exact verified12 m hm hs
  · exact verified14 m hm hs
