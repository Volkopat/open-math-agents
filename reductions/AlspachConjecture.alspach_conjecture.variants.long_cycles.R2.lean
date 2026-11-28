import FormalConjectures.Wikipedia.AlspachConjecture
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Multiset.Filter
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Mathlib.Data.Multiset.AddSub

/-!
# Odd complete graphs and unit transfers between long cycles

The residual construction at each cycle count has at most one prescribed length strictly
between the two endpoints. A second residual asks for a transfer of one unit between two
prescribed lengths, under the assumption that no realization admits a triangular detour.
The cycle surgery below handles any realization with such a detour.

Bryant and Horsley, “Decompositions of complete graphs into long cycles”, Bull. Lond. Math.
Soc. 41 (2009), 927–934, studied methods for changing cycle lengths. Here multiset induction
uses the potential ∑ x (n − x), and the displayed triangular exchange preserves edge counts.
The all-Hamilton proof adapts the Walecki construction in the accepted long-cycles R1.H1.
The finite bitmap interpretation adapts @Deldor14’s accepted construction (OMA PR #4844).
The finite tables contain explicit decompositions. The larger tables were constructed by
replacing pairs of Walecki cycles by three cycles and exchanging triangular detours.
-/

open Multiset
namespace LongCycleRedistribution

/-- Two endpoint multiplicities suffice if every entry is an endpoint. -/
theorem endpoint_counts (L : Multiset ℕ) (a b : ℕ) (ends : ∀x ∈ L, x=a ∨ x=b) :
    ∃ i j, L=replicate i a+replicate j b := by
  let S := L.filter (· = a)
  let T := L.filter (fun x => ¬x=a)
  have hs : S=replicate S.card a := eq_replicate_card.mpr (fun x hx => (mem_filter.mp hx).2)
  have ht : T=replicate T.card b := eq_replicate_card.mpr (fun x hx =>
    (ends x (mem_filter.mp hx).1).resolve_left (mem_filter.mp hx).2)
  exact ⟨S.card,T.card,by rw [←hs,←ht]; exact (filter_add_not _ _).symm⟩

/-- Either all entries are maximal, a boundary profile has one distinguished
smaller entry, or two internal entries are available for redistribution. -/
theorem profile (L : Multiset ℕ) (a b : ℕ) (bound : ∀x ∈ L, a ≤ x ∧ x ≤ b) :
    (∀x ∈ L, x=b) ∨
    (∃ i j c, a ≤ c ∧ c < b ∧ L=c ::ₘ (replicate i a+replicate j b)) ∨
    (∃ x y R, a < x ∧ x ≤ y ∧ y < b ∧ L=x ::ₘ y ::ₘ R) := by
  classical
  by_cases allMax : ∀x ∈ L,x=b
  · exact Or.inl allMax
  right
  obtain ⟨z,hz,hzb⟩ : ∃z ∈ L,z≠b := by simpa only [not_forall,exists_prop] using allMax
  have choose : ∃c ∈ L, c < b ∧ ((∃x ∈ L,a < x ∧ x < b) → a < c) := by
    by_cases mid : ∃x ∈ L,a < x ∧ x < b
    · obtain ⟨x,hx,hl,hh⟩ := mid
      exact ⟨x,hx,hh,fun _ => hl⟩
    · exact ⟨z,hz,lt_of_le_of_ne (bound z hz).2 hzb,fun h => (mid h).elim⟩
  obtain ⟨c,hc,cb,first⟩ := choose
  have ac := (bound c hc).1
  obtain ⟨S,rfl⟩ := exists_cons_of_mem hc
  by_cases other : ∃y ∈ S,a < y ∧ y < b
  · right
    obtain ⟨y,hy,ay,yb⟩ := other
    have ca := first ⟨y,mem_cons_of_mem hy,ay,yb⟩
    obtain ⟨R,rfl⟩ := exists_cons_of_mem hy
    rcases le_total c y with h | h
    · exact ⟨c,y,R,ca,h,yb,rfl⟩
    · exact ⟨y,c,R,ay,h,cb,cons_swap ..⟩
  · left
    obtain ⟨i,j,eq⟩ := endpoint_counts S a b (fun y hy => by
      have := bound y (mem_cons_of_mem hy)
      by_contra! H
      exact other ⟨y,hy,by omega,by omega⟩)
    exact ⟨i,j,c,ac,cb,by rw [eq]⟩

/-- A numerical inequality proving termination for inverse unit transfers. -/
theorem potential_step (b x y : ℕ) (hx : 0 < x) (xy : x ≤ y) (yb : y < b) :
    (x-1)*(b-(x-1)) + (y+1)*(b-(y+1)) < x*(b-x) + y*(b-y) := by
  have h0 : 1 ≤ x := by omega
  have h1 : x-1 ≤ b := by omega
  have h2 : y+1 ≤ b := by omega
  have h3 : x ≤ b := by omega
  have h4 : y ≤ b := by omega
  zify [h0,h1,h2,h3,h4]
  nlinarith

/-- All profiles follow from the boundary profiles and repacking two specified
cycle lengths by one. The repacking is allowed to use all the edges. -/
theorem of_boundary_and_transfers (a b budget : ℕ) (P : Multiset ℕ → Prop)
    (allMax : ∀ L : Multiset ℕ, (∀x ∈ L,x=b) → L.sum=budget → P L)
    (boundary : ∀ i j c : ℕ, a ≤ c → c < b → c+i*a+j*b=budget →
      P (c ::ₘ (replicate i a+replicate j b)))
    (move : ∀ (R : Multiset ℕ) (s t : ℕ), a ≤ s → s+2 ≤ t → t ≤ b →
      (∀x ∈ R,a ≤ x ∧ x ≤ b) → s+t+R.sum=budget →
      P (s ::ₘ t ::ₘ R) → P ((s+1) ::ₘ (t-1) ::ₘ R)) :
    ∀ L : Multiset ℕ, (∀x ∈ L,a ≤ x ∧ x ≤ b) → L.sum=budget → P L := by
  classical
  let cost (L : Multiset ℕ) := (L.map fun x => x*(b-x)).sum
  suffices go : ∀ v (L : Multiset ℕ), cost L=v → (∀x ∈ L,a ≤ x ∧ x ≤ b) →
      L.sum=budget → P L from fun L h hsum => go (cost L) L rfl h hsum
  intro v
  induction v using Nat.strong_induction_on with
  | h v ih =>
    intro L hv hb hs
    rcases profile L a b hb with same | ⟨i,j,c,hc,hcb,rfl⟩ | ⟨x,y,R,ax,xy,yb,rfl⟩
    · exact allMax L same hs
    · apply boundary i j c hc hcb
      simpa [Multiset.sum_add,add_assoc,add_left_comm,add_comm] using hs
    · have inside : ∀ u ∈ R, a ≤ u ∧ u ≤ b := fun u hu =>
        hb u (mem_cons_of_mem (mem_cons_of_mem hu))
      have shifted : cost ((x-1) ::ₘ (y+1) ::ₘ R) < v := by
        rw [←hv]
        dsimp [cost]
        simp only [Multiset.map_cons,Multiset.sum_cons]
        have less := potential_step b x y (by omega) xy yb
        omega
      have hsum : x + y + R.sum=budget := by simpa [add_assoc] using hs
      have lower := ih _ shifted ((x-1) ::ₘ (y+1) ::ₘ R) rfl (by
        intro u hu
        rcases Multiset.mem_cons.mp hu with rfl | hu
        · omega
        rcases Multiset.mem_cons.mp hu with rfl | hu
        · omega
        exact inside u hu) (by simp only [Multiset.sum_cons]; omega)
      have result := move R (x-1) (y+1) (by omega) (by omega) (by omega) inside (by omega) lower
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ x)] using result

end LongCycleRedistribution

namespace LongCycleRedistribution

/-- Budget and cycle count determine the two endpoint multiplicities and the
distinguished smaller cycle, including when its length equals the lower end. -/
theorem boundary_unique {a b c c' i j i' j' : ℕ}
    (ac : a ≤ c) (cb : c < b) (ac' : a ≤ c') (cb' : c'<b)
    (card : i+j=i'+j') (total : c+i*a+j*b=c'+i'*a+j'*b) :
    i=i' ∧ j=j' ∧ c=c' := by
  have ab : a ≤ b := by omega
  have gap : 0 < b-a := by omega
  have rem₁ : c-a < b-a := by omega
  have rem₂ : c'-a < b-a := by omega
  have digit : (c-a)+(b-a)*j = (c'-a)+(b-a)*j' := by
    have mult := congrArg (fun t : ℕ => t*a) card
    zify [ac,ac',ab] at *
    nlinarith
  have residue := congrArg (fun t => t%(b-a)) digit
  have cEq : c-a=c'-a := by simpa [Nat.mod_eq_of_lt rem₁,Nat.mod_eq_of_lt rem₂] using residue
  rw [cEq] at digit
  have jEq : j=j' := Nat.mul_left_cancel gap (Nat.add_left_cancel digit)
  exact ⟨by omega,jEq,by omega⟩
end LongCycleRedistribution

open SimpleGraph Multiset
namespace LongCycleRedistribution

/-- Replace an edge of one cycle by a two-edge detour cut from a second cycle.
The vertex on the detour must lie outside the first cycle. Edges of the other
cycles are untouched, and all individual edge multiplicities are preserved. -/
theorem triangle_switch {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {x v y : V} (xy : G.Adj x y) (xv : G.Adj x v) (vy : G.Adj v y)
    (P Q : G.Walk y x) (hp : P.IsPath) (hq : Q.IsPath)
    (outside : v ∉ P.support) (pLong : 1 ≤ P.length) (qLong : 2 ≤ Q.length)
    (A B : Cycle G) (oldA : A.edges = s(x,y) :: P.edges)
    (oldB : B.edges = s(x,v) :: s(v,y) :: Q.edges) :
    ∃ C D : Cycle G, C.length=A.length+1 ∧ D.length+1=B.length ∧
      ∀ (R : Multiset (Cycle G)) (e : Sym2 V),
        ((C ::ₘ D ::ₘ R).filter fun z => e∈z.edges).card =
        ((A ::ₘ B ::ₘ R).filter fun z => e∈z.edges).card := by
  classical
  let U := Walk.cons xv (Walk.cons vy P)
  let W := Walk.cons xy Q
  have uc : U.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨?_, by simp [U]; omega⟩
    simpa [U] using (Walk.cons_isPath_iff vy P).mpr ⟨hp,outside⟩
  have wc : W.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    exact ⟨by simpa [W] using hq, by simp [W]; omega⟩
  let C : Cycle G := ⟨x,U,uc⟩
  let D : Cycle G := ⟨x,W,wc⟩
  have len (z : Cycle G) : z.edges.length=z.length := z.walk.length_edges
  have la := congrArg List.length oldA
  have lb := congrArg List.length oldB
  simp only [List.length_cons, Walk.length_edges, len] at la lb
  refine ⟨C,D,?_,?_,?_⟩
  · change P.length+1+1=A.length+1
    omega
  · change Q.length+1+1=B.length
    omega
  have equal : (C.edges:Multiset (Sym2 V)) + (D.edges:Multiset (Sym2 V)) =
      (A.edges:Multiset (Sym2 V)) + (B.edges:Multiset (Sym2 V)) := by
    rw [oldA,oldB]
    change (s(x,v) ::ₘ s(v,y) ::ₘ (P.edges:Multiset (Sym2 V))) +
        (s(x,y) ::ₘ (Q.edges:Multiset (Sym2 V))) =
      (s(x,y) ::ₘ (P.edges:Multiset (Sym2 V))) + (s(x,v) ::ₘ s(v,y) ::ₘ (Q.edges:Multiset (Sym2 V)))
    simp only [←Multiset.singleton_add]
    ac_rfl
  intro R e
  have countEdge (c : Cycle G) : (c.edges : Multiset (Sym2 V)).count e = if e∈c.edges then 1 else 0 := by
    by_cases h : e∈c.edges
    · rw [if_pos h]
      exact Multiset.count_eq_one_of_mem c.isCycle.isTrail.edges_nodup h
    · exact (Multiset.count_eq_zero.mpr h).trans (if_neg h).symm
  have addOne (c : Cycle G) (S : Multiset (Cycle G)) :
      ((c ::ₘ S).filter fun z => e∈z.edges).card =
        (if e∈c.edges then 1 else 0) + (S.filter fun z => e∈z.edges).card := by
    by_cases h : e∈c.edges <;> simp [h,Nat.add_comm]
  have val := congrArg (Multiset.count e) equal
  simp only [Multiset.count_add, countEdge] at val
  simp only [addOne,← Nat.add_assoc,val]
end LongCycleRedistribution

/- Walecki's decomposition of an odd complete graph, adapted from the accepted
proof of AlspachConjecture.alspach_conjecture.variants.long_cycles.R1.H1. -/
namespace LongCycleRedistribution
open SimpleGraph AlspachConjecture
set_option maxHeartbeats 2500000 in
theorem all_hamilton :
  ∀ (n : ℕ), Odd n → 5 ≤ n → ∀ m : Multiset ℕ,
    (∀ x ∈ m, x = n) → m.sum = n.choose 2 →
      ∃ C : Multiset (Cycle (completeGraph (Fin n))),
        IsCycleDecomposition (completeGraph (Fin n)) C ∧ lengths C = m := by
  let walkTo {V : Type} {G : SimpleGraph V} (f : ℕ → V) (N : ℕ)
      (h : ∀ t, t < N → G.Adj (f t) (f (t + 1))) (m : ℕ) : m ≤ N → G.Walk (f 0) (f m) :=
    Nat.rec (motive := fun j => j ≤ N → G.Walk (f 0) (f j)) (fun _ => Walk.nil)
      (fun j prev hj => (prev (by omega)).concat (h j (by omega))) m
  have walkTo_zero {V : Type} {G : SimpleGraph V} (f : ℕ → V) (N : ℕ)
      (h : ∀ t, t < N → G.Adj (f t) (f (t + 1))) (hm : 0 ≤ N) :
      walkTo f N h 0 hm = Walk.nil := rfl
  have walkTo_succ {V : Type} {G : SimpleGraph V} (f : ℕ → V) (N : ℕ)
      (h : ∀ t, t < N → G.Adj (f t) (f (t + 1))) (m : ℕ) (hm : m+1 ≤ N) :
      walkTo f N h (m+1) hm = (walkTo f N h m (by omega)).concat (h m (by omega)) := rfl

  have walkTo_support {V : Type} {G : SimpleGraph V} (f : ℕ → V) (N : ℕ)
      (h : ∀ t, t < N → G.Adj (f t) (f (t + 1))) (m : ℕ) (hm : m ≤ N) :
      (walkTo f N h m hm).support = (List.range (m + 1)).map f := by
    induction m with
    | zero => simp [walkTo_zero]
    | succ m ih =>
      rw [walkTo_succ f N h m hm, Walk.support_concat, ih (by omega), List.range_succ (n := m + 1), List.map_append]
      simp

  have walkTo_edges {V : Type} {G : SimpleGraph V} (f : ℕ → V) (N : ℕ)
      (h : ∀ t, t < N → G.Adj (f t) (f (t + 1))) (m : ℕ) (hm : m ≤ N) :
      (walkTo f N h m hm).edges = (List.range m).map (fun t => s(f t, f (t + 1))) := by
    induction m with
    | zero => simp [walkTo_zero]
    | succ m ih =>
      rw [walkTo_succ f N h m hm, Walk.edges_concat, ih (by omega), List.range_succ, List.map_append]
      simp

  have walkTo_length {V : Type} {G : SimpleGraph V} (f : ℕ → V) (N : ℕ)
      (h : ∀ t, t < N → G.Adj (f t) (f (t + 1))) (m : ℕ) (hm : m ≤ N) :
      (walkTo f N h m hm).length = m := by
    induction m with
    | zero => simp [walkTo_zero]
    | succ m ih => rw [walkTo_succ f N h m hm, Walk.length_concat, ih (by omega)]


  let wal (k i t : ℕ) : ℕ :=
    if 2 * k ≤ t then 2 * k
    else if t % 2 = 1 then i + (t + 1) / 2
    else if t / 2 ≤ i then i - t / 2
    else i + 2 * k - t / 2

  have wal_lt (k i t : ℕ) (hi : i < k) : wal k i t < 2 * k + 1 := by
    unfold wal
    split_ifs <;> omega

  have wal_inj (k i t u : ℕ) (hi : i < k) (ht : t ≤ 2 * k) (hu : u ≤ 2 * k)
      (h : wal k i t = wal k i u) : t = u := by
    unfold wal at h
    split_ifs at h <;> omega


  let col (k a b : ℕ) : ℕ :=
    if a = 2 * k then (if b < k then b else b - k)
    else if b = 2 * k then (if a < k then a else a - k)
    else if a + b < 2 * k then (a + b) / 2
    else (a + b - 2 * k) / 2

  have col_comm (k a b : ℕ) : col k a b = col k b a := by
    unfold col
    split_ifs <;> omega

  have col_step (k i t : ℕ) (hi : i < k) (ht : t < 2 * k) :
      col k (wal k i t) (wal k i (t + 1)) = i := by
    unfold col wal
    split_ifs <;> omega

  have col_close (k i : ℕ) (hi : i < k) :
      col k (wal k i (2 * k)) (wal k i 0) = i := by
    unfold col wal
    split_ifs <;> omega


  let wv (k : ℕ) (i : Fin k) (t : ℕ) : Fin (2 * k + 1) := ⟨wal k i t, wal_lt k i t i.2⟩

  have wv_inj (k : ℕ) (i : Fin k) (t u : ℕ) (ht : t ≤ 2 * k) (hu : u ≤ 2 * k)
      (h : wv k i t = wv k i u) : t = u :=
    wal_inj k i t u i.2 ht hu (congrArg Fin.val h)

  have wv_adj (k : ℕ) (i : Fin k) :
      ∀ t, t < 2 * k → (completeGraph (Fin (2 * k + 1))).Adj (wv k i t) (wv k i (t + 1)) := by
    intro t ht
    rw [completeGraph_eq_top, top_adj]
    intro h
    have := wv_inj k i t (t + 1) (by omega) (by omega) h
    omega

  have wv_close (k : ℕ) (hk : 1 ≤ k) (i : Fin k) :
      (completeGraph (Fin (2 * k + 1))).Adj (wv k i (2 * k)) (wv k i 0) := by
    rw [completeGraph_eq_top, top_adj]
    intro h
    have := wv_inj k i (2 * k) 0 le_rfl (by omega) h
    omega


  let hpath (k : ℕ) (i : Fin k) :
      (completeGraph (Fin (2 * k + 1))).Walk (wv k i 0) (wv k i (2 * k)) :=
    walkTo (wv k i) (2 * k) (wv_adj k i) (2 * k) le_rfl


  let cyc (k : ℕ) (hk : 1 ≤ k) (i : Fin k) : SimpleGraph.Cycle (completeGraph (Fin (2 * k + 1))) := {
    base := wv k i (2 * k)
    walk := Walk.cons (wv_close k hk i) (hpath k i)
    isCycle := by
      rw [Walk.cons_isCycle_iff]
      constructor
      · rw [Walk.isPath_def]
        dsimp only [hpath]
        rw [walkTo_support]
        apply List.Nodup.map_on
        · intro x hx y hy hxy
          rw [List.mem_range] at hx hy
          exact wv_inj k i x y (by omega) (by omega) hxy
        · exact List.nodup_range
      · dsimp only [hpath]
        rw [walkTo_edges, List.mem_map]
        rintro ⟨t, ht, he⟩
        rw [List.mem_range] at ht
        rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have := wv_inj k i t (2 * k) (by omega) le_rfl h1
          omega
        · have h3 := wv_inj k i t 0 (by omega) (by omega) h1
          have h4 := wv_inj k i (t + 1) (2 * k) (by omega) le_rfl h2
          omega

  }

  have cyc_edges (k : ℕ) (hk : 1 ≤ k) (i : Fin k) :
      (cyc k hk i).edges = s(wv k i (2 * k), wv k i 0) ::
        (List.range (2 * k)).map (fun t => s(wv k i t, wv k i (t + 1))) := by
    simp only [SimpleGraph.Cycle.edges, cyc, Walk.edges_cons, hpath, walkTo_edges]

  have cyc_length (k : ℕ) (hk : 1 ≤ k) (i : Fin k) : (cyc k hk i).length = 2 * k + 1 := by
    simp only [SimpleGraph.Cycle.length, cyc, Walk.length_cons, hpath, walkTo_length]


  let colS (k : ℕ) : Sym2 (Fin (2 * k + 1)) → ℕ :=
    Sym2.lift ⟨fun a b => col k a b, fun a b => col_comm k a b⟩

  have colS_of_mem (k : ℕ) (hk : 1 ≤ k) (i : Fin k) (e : Sym2 (Fin (2 * k + 1)))
      (he : e ∈ (cyc k hk i).edges) : colS k e = i := by
    rw [cyc_edges k hk i, List.mem_cons, List.mem_map] at he
    rcases he with rfl | ⟨t, ht, rfl⟩
    · simp only [colS, Sym2.lift_mk]
      exact col_close k i i.2
    · rw [List.mem_range] at ht
      simp only [colS, Sym2.lift_mk]
      exact col_step k i t i.2 ht

  have cyc_nodup (k : ℕ) (hk : 1 ≤ k) (i : Fin k) : (cyc k hk i).edges.Nodup :=
    (cyc k hk i).isCycle.edges_nodup

  have choose_two_odd (k : ℕ) : (2 * k + 1).choose 2 = k * (2 * k + 1) := by
    rw [Nat.choose_two_right, show (2 * k + 1) * (2 * k + 1 - 1) = 2 * (k * (2 * k + 1)) by
      rw [show 2 * k + 1 - 1 = 2 * k by omega]; ring, Nat.mul_div_cancel_left _ (by norm_num)]
  intro n hn hn5 m hm hsum
  obtain ⟨k, rfl⟩ := hn
  have hk : 1 ≤ k := by omega
  have hm' : m = Multiset.replicate k (2 * k + 1) := by
    have h1 : m = Multiset.replicate (Multiset.card m) (2 * k + 1) :=
      Multiset.eq_replicate.mpr ⟨rfl, hm⟩
    have h2 : Multiset.card m = k := by
      rw [h1, Multiset.sum_replicate, smul_eq_mul, choose_two_odd] at hsum
      exact Nat.eq_of_mul_eq_mul_right (by omega) hsum
    rw [h1, h2]
  refine ⟨(Finset.univ : Finset (Fin k)).val.map (cyc k hk), ?_, ?_⟩
  · intro e he
    classical
    -- every edge lies on some cycle, by counting
    have hex : ∃ i, e ∈ (cyc k hk i).edges := by
      let S : Fin k → Finset (Sym2 (Fin (2 * k + 1))) := fun i => (cyc k hk i).edges.toFinset
      have hsub : Finset.univ.biUnion S ⊆ (completeGraph (Fin (2 * k + 1))).edgeFinset := by
        intro x hx
        rw [Finset.mem_biUnion] at hx
        obtain ⟨i, -, hx⟩ := hx
        rw [List.mem_toFinset] at hx
        rw [mem_edgeFinset]
        exact Walk.edges_subset_edgeSet _ hx
      have hdisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint S := by
        intro i _ j _ hij
        rw [Function.onFun, Finset.disjoint_left]
        intro x hxi hxj
        rw [List.mem_toFinset] at hxi hxj
        apply hij
        apply Fin.ext
        rw [← colS_of_mem k hk i x hxi, ← colS_of_mem k hk j x hxj]
      have hcard : (Finset.univ.biUnion S).card = k * (2 * k + 1) := by
        rw [Finset.card_biUnion hdisj]
        have : ∀ i, (S i).card = 2 * k + 1 := by
          intro i
          simp only [S]
          rw [List.toFinset_card_of_nodup (cyc_nodup k hk i), SimpleGraph.Cycle.edges,
            Walk.length_edges]
          exact cyc_length k hk i
        simp [this]
      have hcardE : (completeGraph (Fin (2 * k + 1))).edgeFinset.card = k * (2 * k + 1) := by
        rw [← choose_two_odd]
        convert card_edgeFinset_top_eq_card_choose_two (V := Fin (2 * k + 1)) using 1
        simp
      have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcardE])
      have he' : e ∈ Finset.univ.biUnion S := by
        rw [heq]
        convert he
      rw [Finset.mem_biUnion] at he'
      obtain ⟨i, -, hi⟩ := he'
      exact ⟨i, List.mem_toFinset.mp hi⟩
    obtain ⟨i0, hi0⟩ := hex
    rw [Multiset.filter_map, Multiset.card_map, Multiset.card_eq_one]
    refine ⟨i0, ?_⟩
    rw [Multiset.Nodup.ext (Multiset.Nodup.filter _ Finset.univ.nodup) (Multiset.nodup_singleton _)]
    intro i
    simp only [Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and,
      Multiset.mem_singleton, Function.comp]
    constructor
    · intro hi
      apply Fin.ext
      rw [← colS_of_mem k hk i e hi, ← colS_of_mem k hk i0 e hi0]
    · rintro rfl
      exact hi0
  · rw [hm', lengths, Multiset.map_map]
    have : (SimpleGraph.Cycle.length ∘ cyc k hk) = fun _ => 2 * k + 1 := by
      funext i
      exact cyc_length k hk i
    rw [this, Multiset.map_const']
    simp

end LongCycleRedistribution

open SimpleGraph AlspachConjecture
namespace AlspachLongFinite

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem checked_rows (n : ℕ) (hn : 0 < n) (tab : List (List ℕ × List (List ℕ))) (keys : List (List ℕ)) :
    let vertex (a : ℕ) : Fin n := ⟨a % n, Nat.mod_lt _ hn⟩
    let code (xs : List ℕ) : Fin n × List (Fin n) :=
      (vertex (xs.headD 0), xs.tail.map vertex)
    let arcs (a b : Fin n) (l : List (Fin n)) := (a :: l).zip (l ++ [b])
    let chain (a b : Fin n) (l : List (Fin n)) := (arcs a b l).all fun p => p.1 != p.2
    let good (c : Fin n × List (Fin n)) :=
      chain c.1 c.1 c.2 && decide ((c.2 ++ [c.1]).Nodup) && decide (3 ≤ c.2.length + 1)
    let key (p : Fin n × Fin n) := Nat.pair (min p.1.val p.2.val) (max p.1.val p.2.val)
    let bitmap (ps : List (Fin n × Fin n)) :=
      ps.foldr (fun p rest => (1 <<< key p) ||| rest) 0
    let pack (cs : List (Fin n × List (Fin n))) : Option ℕ :=
      cs.foldr (fun c r => r.bind fun rest =>
        let bits := bitmap (arcs c.1 c.1 c.2)
        if good c && (bits &&& rest == 0) then some (bits ||| rest) else none) (some 0)
    let full := bitmap ((List.finRange n).flatMap fun a =>
      ((List.finRange n).filter (a < ·)).map (fun b => (a,b)))
    let rowOK (row : List ℕ × List (List ℕ)) :=
      let cs := row.2.map code
      (pack cs == some full) && (cs.map (fun c => c.2.length + 1) == row.1)
    tab.map Prod.fst=keys → tab.all rowOK=true → ∀ xs ∈ keys,
      ∃ C : Multiset (Cycle (completeGraph (Fin n))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro vertex code arcs chain good key bitmap pack full rowOK cover valid xs membership
  have arcStep (a b x : Fin n) (xs : List (Fin n)) :
      arcs a b (x :: xs) = (a,x) :: arcs x b xs := rfl
  have chainStep (a b x : Fin n) (xs : List (Fin n)) :
      chain a b (x :: xs) = ((a != x) && chain x b xs) := rfl
  have walk (a b : Fin n) (l : List (Fin n)) (ok : chain a b l = true) :
      ∃ w : (completeGraph (Fin n)).Walk a b, w.length = l.length+1 ∧
        w.support = a :: (l ++ [b]) ∧ w.edges = (arcs a b l).map (fun p => s(p.1,p.2)) := by
    induction l generalizing a with
    | nil =>
      have adj : a ≠ b := by simpa [chain,arcs] using ok
      exact ⟨.cons adj .nil,rfl,rfl,rfl⟩
    | cons x xs ih =>
      rw [chainStep,Bool.and_eq_true] at ok
      obtain ⟨w,wl,ws,we⟩ := ih x ok.2
      have adj : a ≠ x := by simpa using ok.1
      refine ⟨.cons adj w, ?_, ?_, ?_⟩
      · simp [wl]
      · simp [ws]
      · simp [we,arcStep]
  have cycleOf (c : Fin n × List (Fin n)) (h : good c = true) :
      ∃ z : Cycle (completeGraph (Fin n)), z.length = c.2.length+1 ∧
        z.edges = (arcs c.1 c.1 c.2).map (fun p => s(p.1,p.2)) := by
    have facts := Bool.and_eq_true_iff.mp h
    have hface := Bool.and_eq_true_iff.mp facts.1
    obtain ⟨w,wl,ws,we⟩ := walk c.1 c.1 c.2 hface.1
    refine ⟨⟨c.1,w,Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_,?_⟩⟩,wl,we⟩
    · apply (Walk.isPath_def _).mpr
      rw [Walk.support_tail_of_not_nil _ (by simp [← Walk.length_eq_zero_iff,wl]),ws]
      simpa using of_decide_eq_true hface.2
    · rw [wl]
      exact of_decide_eq_true facts.2
  have key_iff (p q : Fin n × Fin n) : key p = key q ↔ s(p.1,p.2) = s(q.1,q.2) := by
    rcases p with ⟨a,b⟩
    rcases q with ⟨c,d⟩
    simp only [key,Nat.pair_eq_pair,Sym2.eq_iff,Fin.ext_iff]
    omega
  have readBitmap (ps : List (Fin n × Fin n)) (q : Fin n × Fin n) :
      (bitmap ps).testBit (key q) = true ↔ s(q.1,q.2) ∈ ps.map (fun p => s(p.1,p.2)) := by
    induction ps with
    | nil => simp [bitmap]
    | cons p ps ih =>
      change ((1 <<< key p) ||| bitmap ps).testBit (key q) = true ↔ _
      rw [Nat.testBit_or,Bool.or_eq_true_iff]
      have bit : (1 <<< key p).testBit (key q) = decide (key p = key q) := by
        rw [Nat.shiftLeft_eq,one_mul,Nat.testBit_two_pow]
      rw [bit,decide_eq_true_eq,key_iff,ih,List.map_cons,List.mem_cons]
      exact or_congr_left eq_comm
  have packed (cs : List (Fin n × List (Fin n))) (k : ℕ) (hc : pack cs = some k) :
      ∃ C : Multiset (Cycle (completeGraph (Fin n))), lengths C = ((cs.map fun c => c.2.length+1) : List ℕ) ∧
        ∀ q : Fin n × Fin n, (C.filter fun c => s(q.1,q.2) ∈ c.edges).card =
          (k.testBit (key q)).toNat := by
    classical
    induction cs generalizing k with
    | nil =>
      have z : k = 0 := (Option.some.inj (show (some 0 : Option ℕ) = some k from hc)).symm
      exact ⟨0,rfl,fun q => by simp [z]⟩
    | cons c cs ih =>
      change (pack cs).bind (fun rest =>
        let bits := bitmap (arcs c.1 c.1 c.2)
        if good c && (bits &&& rest == 0) then some (bits ||| rest) else none) = some k at hc
      cases h : pack cs with
      | none => simp [h] at hc
      | some r =>
        let bits := bitmap (arcs c.1 c.1 c.2)
        have facts : (good c = true ∧ bits &&& r = 0) ∧ bits ||| r = k := by
          simpa [h,bits] using hc
        obtain ⟨⟨cgood,dis⟩,get'⟩ := facts
        obtain ⟨z,zl,ze⟩ := cycleOf c cgood
        obtain ⟨C,lens,count⟩ := ih r h
        refine ⟨z ::ₘ C,?_,?_⟩
        · simpa [lengths,zl] using congrArg (Multiset.cons (c.2.length+1)) lens
        · intro q
          have mem : s(q.1,q.2) ∈ z.edges ↔ bits.testBit (key q) = true := by
            rw [ze]
            exact (readBitmap _ _).symm
          have distinct := congrArg (fun a : ℕ => a.testBit (key q)) dis
          rw [← get',Nat.testBit_or]
          by_cases own : bits.testBit (key q) = true
          · have zero : r.testBit (key q) = false := by simpa [own] using distinct
            rw [Multiset.filter_cons_of_pos (p:=fun v : Cycle (completeGraph (Fin n)) => s(q.1,q.2) ∈ v.edges) C (mem.mpr own),Multiset.card_cons,count]
            simp [own,zero]
          · rw [Multiset.filter_cons_of_neg (p:=fun v : Cycle (completeGraph (Fin n)) => s(q.1,q.2) ∈ v.edges) C (fun e => own (mem.mp e)),count]
            simp [own]
  have fullHasLt (a b : Fin n) (hab : a < b) : full.testBit (key (a,b)) = true := by
    apply (readBitmap _ _).mpr
    apply List.mem_map.mpr
    refine ⟨(a,b),List.mem_flatMap.mpr ⟨a,by simp,?_⟩,rfl⟩
    exact List.mem_map.mpr ⟨b,by simp [hab],rfl⟩
  have fullHas (a b : Fin n) (hab : a ≠ b) : full.testBit (key (a,b)) = true := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact fullHasLt _ _ h
    · simpa [key,min_comm,max_comm] using fullHasLt b a h
  rw [← cover,List.mem_map] at membership
  obtain ⟨⟨ds,paths⟩,hin,hds⟩ := membership
  change ds = xs at hds
  have ok := List.all_eq_true.mp valid _ hin
  have facts : pack (paths.map code) = some full ∧
      (paths.map code).map (fun c => c.2.length+1) = xs := by
    rw [← hds]
    simpa [rowOK] using ok
  obtain ⟨C,hl,count⟩ := packed _ _ facts.1
  refine ⟨C,?_,hl.trans (congrArg (fun l : List ℕ => (l : Multiset ℕ)) facts.2)⟩
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    intro he
    have hab : a ≠ b := SimpleGraph.mem_edgeFinset.mp he
    simpa [fullHas a b hab] using count (a,b)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem fast_keys (n lo total : ℕ) (hlo : 0 < lo) (keys : List (List ℕ))
    (good : ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin n))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ)) :
    let parts : ℕ → ℕ → ℕ → List (List ℕ) := fun depth =>
      Nat.rec (fun _ t => if t=0 then [[]] else []) (fun _ prev low t =>
        if t=0 then [[]] else
          ((List.range (min n (t/2)+1-low)).flatMap fun j =>
            let d := low+j
            (prev d (t-d)).map (d :: ·)) ++ (if low ≤ t ∧ t ≤ n then [[t]] else [])) depth
    keys=parts (total/lo) lo total → ∀ m : Multiset ℕ, (∀ k∈m,lo ≤ k ∧ k ≤ n) → m.sum=total →
      ∃ C : Multiset (Cycle (completeGraph (Fin n))), IsCycleDecomposition _ C ∧ lengths C=m := by
  intro parts cover m bounds budget
  have sound (fuel low t : ℕ) (ys : List ℕ) (hl : 0 < low) (sorted : ys.Pairwise (·≤·))
      (hb : ∀k∈ys, low ≤ k ∧ k ≤ n) (hs : ys.sum=t) (len : ys.length ≤ fuel) : ys∈parts fuel low t := by
    induction fuel generalizing low t ys with
    | zero =>
      cases ys with
      | nil =>
        have z : t=0 := by simpa using hs.symm
        simp [parts,z]
      | cons d ds => simp at len
    | succ fuel ih =>
      cases ys with
      | nil => simp_all [parts]
      | cons d ds =>
        have bd := hb d (List.mem_cons_self ..)
        have rest : ds.length ≤ fuel := by simpa using len
        have weight : d+ds.sum=t := by simpa using hs
        have pos : t≠0 := by omega
        change d::ds ∈ (if t=0 then [[]] else _ ++ _)
        rw [if_neg pos, List.mem_append]
        cases ds with
        | nil =>
          right
          have eq : d=t := by simpa using weight
          subst t
          simp [bd.1,bd.2]
        | cons e es =>
          left
          obtain ⟨before,later⟩ := List.pairwise_cons.mp sorted
          have de : d ≤ e := before e (List.mem_cons_self ..)
          have sum : d+(e+es.sum)=t := by simpa only [List.sum_cons] using weight
          let j := d-low
          have dj : low+j=d := by dsimp [j]; omega
          apply List.mem_flatMap.mpr
          refine ⟨j,List.mem_range.mpr (by dsimp [j]; omega),?_⟩
          dsimp only
          rw [dj]
          exact List.mem_map.mpr ⟨e::es, ih d (t-d) _ (by omega) later
            (fun k h => ⟨before k h,(hb k (List.mem_cons_of_mem _ h)).2⟩) (by omega) rest,rfl⟩
  let xs := m.sort (·≤·)
  have eqm : (xs : Multiset ℕ)=m := Multiset.sort_eq ..
  have sum : xs.sum=total := by
    convert budget using 1
    exact congrArg Multiset.sum eqm
  have bound (k : ℕ) (hk : k∈xs) := bounds k (by simpa [xs] using hk)
  have weight (ys : List ℕ) (yes : ∀k∈ys,lo ≤ k) : ys.length*lo ≤ ys.sum := by
    induction ys with
    | nil => simp
    | cons d ds ih =>
      have head := yes d (List.mem_cons_self ..)
      have tail := ih (fun k h => yes k (List.mem_cons_of_mem _ h))
      simp only [List.length_cons,Nat.add_mul,one_mul,List.sum_cons]
      omega
  have len : xs.length ≤ total/lo := (Nat.le_div_iff_mul_le hlo).mpr (sum ▸ weight xs (fun k h => (bound k h).1))
  have hit := sound _ lo total xs hlo (Multiset.pairwise_sort ..) bound sum len
  rw [← cover] at hit
  obtain ⟨C,hC,he⟩ := good xs hit
  exact ⟨C,hC,he.trans eqm⟩

theorem together {α : Type} {P : α→Prop} {S T : List α} (hS : ∀ x∈S, P x) (hT : ∀x∈T, P x) :
    ∀x∈S++T,P x :=
  fun x hx => (List.mem_append.mp hx).elim (hS x) (hT x)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem table_sound (n lo total : ℕ) (hn : 0 < n) (hlo : 0 < lo)
    (tab : List (List ℕ × List (List ℕ))) :
    let vertex (a : ℕ) : Fin n := ⟨a % n, Nat.mod_lt _ hn⟩
    let code (xs : List ℕ) : Fin n × List (Fin n) :=
      (vertex (xs.headD 0), xs.tail.map vertex)
    let arcs (a b : Fin n) (l : List (Fin n)) := (a :: l).zip (l ++ [b])
    let chain (a b : Fin n) (l : List (Fin n)) := (arcs a b l).all fun p => p.1 != p.2
    let good (c : Fin n × List (Fin n)) :=
      chain c.1 c.1 c.2 && decide ((c.2 ++ [c.1]).Nodup) && decide (3 ≤ c.2.length + 1)
    let key (p : Fin n × Fin n) := Nat.pair (min p.1.val p.2.val) (max p.1.val p.2.val)
    let bitmap (ps : List (Fin n × Fin n)) :=
      ps.foldr (fun p rest => (1 <<< key p) ||| rest) 0
    let pack (cs : List (Fin n × List (Fin n))) : Option ℕ :=
      cs.foldr (fun c r => r.bind fun rest =>
        let bits := bitmap (arcs c.1 c.1 c.2)
        if good c && (bits &&& rest == 0) then some (bits ||| rest) else none) (some 0)
    let full := bitmap ((List.finRange n).flatMap fun a =>
      ((List.finRange n).filter (a < ·)).map (fun b => (a,b)))
    let rowOK (row : List ℕ × List (List ℕ)) :=
      let cs := row.2.map code
      (pack cs == some full) && (cs.map (fun c => c.2.length + 1) == row.1)
    let parts : ℕ → ℕ → ℕ → List (List ℕ) := fun depth =>
      Nat.rec (fun _ t => if t=0 then [[]] else []) (fun _ prev low t =>
        if t=0 then [[]] else
          ((List.range (min n (t/2)+1-low)).flatMap fun j =>
            let d := low+j
            (prev d (t-d)).map (d :: ·)) ++ (if low ≤ t ∧ t ≤ n then [[t]] else [])) depth
    tab.map Prod.fst = parts (total/lo) lo total → tab.all rowOK = true →
    ∀ m : Multiset ℕ, (∀ k ∈ m, lo ≤ k ∧ k ≤ n) → m.sum = total →
      ∃ C : Multiset (Cycle (completeGraph (Fin n))),
        IsCycleDecomposition (completeGraph (Fin n)) C ∧ lengths C = m := by
  intro vertex code arcs chain good key bitmap pack full rowOK parts cover valid m bounds hsum
  exact fast_keys n lo total hlo (tab.map Prod.fst)
    (checked_rows n hn tab _ rfl valid) cover m bounds hsum

end AlspachLongFinite

open SimpleGraph AlspachConjecture

namespace AlspachLongFinite

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem complete_5 (m : Multiset ℕ) (hb : ∀ k ∈ m, 5 ≤ k ∧ k ≤ 5)
    (hs : m.sum = 10) : ∃ C : Multiset (Cycle (completeGraph (Fin 5))),
      IsCycleDecomposition (completeGraph (Fin 5)) C ∧ lengths C = m := by
  let tab : List (List ℕ × List (List ℕ)) := [
    ([5,5],[[4,0,3,1,2],[4,1,0,2,3]]) ]
  exact table_sound 5 5 10 (by decide) (by decide) tab
    (by decide +kernel) (by decide +kernel) m hb hs

end AlspachLongFinite

open SimpleGraph AlspachConjecture

namespace AlspachLongFinite

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem complete_7 (m : Multiset ℕ) (hb : ∀ k ∈ m, 6 ≤ k ∧ k ≤ 7)
    (hs : m.sum = 21) : ∃ C : Multiset (Cycle (completeGraph (Fin 7))),
      IsCycleDecomposition (completeGraph (Fin 7)) C ∧ lengths C = m := by
  let tab : List (List ℕ × List (List ℕ)) := [
    ([7,7,7],[[6,0,5,1,4,2,3],[6,1,0,2,5,3,4],[6,2,1,3,0,4,5]]) ]
  exact table_sound 7 6 21 (by decide) (by decide) tab
    (by decide +kernel) (by decide +kernel) m hb hs

end AlspachLongFinite

open SimpleGraph AlspachConjecture

namespace AlspachLongFinite

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem complete_9 (m : Multiset ℕ) (hb : ∀ k ∈ m, 7 ≤ k ∧ k ≤ 9)
    (hs : m.sum = 36) : ∃ C : Multiset (Cycle (completeGraph (Fin 9))),
      IsCycleDecomposition (completeGraph (Fin 9)) C ∧ lengths C = m := by
  let tab : List (List ℕ × List (List ℕ)) := [
    ([7,7,7,7,8],[[4,6,3,0,7,1,5],[8,2,4,7,3,5,0],[6,2,7,5,8,3,1],[1,4,8,7,6,0,2],[8,6,5,2,3,4,0,1]]),
    ([9,9,9,9],[[4,0,7,1,5,8,6,3,2],[6,2,0,1,3,7,8,4,5],[6,1,2,8,3,0,5,7,4],[2,7,6,0,8,1,4,3,5]]) ]
  exact table_sound 9 7 36 (by decide) (by decide) tab
    (by decide +kernel) (by decide +kernel) m hb hs

end AlspachLongFinite

open SimpleGraph AlspachConjecture

namespace AlspachLongFinite

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem complete_11 (m : Multiset ℕ) (hb : ∀ k ∈ m, 8 ≤ k ∧ k ≤ 11)
    (hs : m.sum = 55) : ∃ C : Multiset (Cycle (completeGraph (Fin 11))),
      IsCycleDecomposition (completeGraph (Fin 11)) C ∧ lengths C = m := by
  let tab : List (List ℕ × List (List ℕ)) := [
    ([8,8,8,9,11,11],[[3,7,2,8,4,9,5,10],[1,4,10,0,8,3,6,9],[1,2,9,7,10,6,5,0],[7,6,0,3,2,4,5,8,1],[6,8,9,3,5,1,10,2,0,7,4],[2,5,7,8,10,9,0,4,3,1,6]]),
    ([8,8,8,10,10,11],[[1,4,5,7,3,6,0,10],[2,4,9,5,0,8,1,6],[9,2,7,10,5,3,4,8],[2,10,8,6,5,1,9,7,0,3],[8,2,1,0,4,10,3,9,6,7],[9,10,6,4,7,1,3,8,5,2,0]]),
    ([8,8,9,9,10,11],[[7,0,4,2,8,10,5,1],[10,9,7,4,1,3,8,6],[6,3,2,9,0,10,7,5,4],[3,7,2,5,8,0,1,6,9],[1,8,9,5,6,2,0,3,4,10],[1,9,4,8,7,6,0,5,3,10,2]]),
    ([8,8,9,10,10,10],[[6,0,4,5,10,9,3,7],[8,6,1,10,7,9,2,0],[2,1,8,10,6,4,9,5,3],[7,4,8,9,0,5,2,10,3,1],[7,2,6,5,1,0,10,4,3,8],[9,6,3,0,7,5,8,2,4,1]]),
    ([8,9,9,9,9,11],[[4,9,0,8,7,1,10,3],[6,4,1,0,10,7,3,2,5],[8,5,1,2,9,10,6,7,4],[8,9,7,0,6,3,5,10,2],[3,8,6,1,9,5,4,2,0],[1,8,10,4,0,5,7,2,6,9,3]]),
    ([8,9,9,9,10,10],[[2,0,6,10,3,9,1,7],[0,7,4,9,2,6,5,8,10],[0,9,6,8,2,5,1,3,4],[0,1,10,4,5,7,9,8,3],[5,3,6,4,2,1,8,7,10,9],[0,8,4,1,6,7,3,2,10,5]]),
    ([9,9,9,9,9,10],[[6,4,5,1,3,10,7,8,9],[2,10,9,3,4,0,5,6,7],[1,2,4,7,0,10,8,3,6],[1,8,6,10,5,2,3,0,9],[0,1,4,9,7,3,5,8,2],[6,0,8,4,10,1,7,5,9,2]]),
    ([11,11,11,11,11],[[0,1,9,2,8,3,7,4,6,5,10],[1,2,0,3,9,4,8,5,7,6,10],[2,3,1,4,0,5,9,6,8,7,10],[3,4,2,5,1,6,0,7,9,8,10],[4,5,3,6,2,7,1,8,0,9,10]]) ]
  exact table_sound 11 8 55 (by decide) (by decide) tab
    (by decide +kernel) (by decide +kernel) m hb hs

end AlspachLongFinite

open SimpleGraph AlspachConjecture

namespace AlspachLongFinite

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem complete_13 (m : Multiset ℕ) (hb : ∀ k ∈ m, 9 ≤ k ∧ k ≤ 13)
    (hs : m.sum = 78) : ∃ C : Multiset (Cycle (completeGraph (Fin 13))),
      IsCycleDecomposition (completeGraph (Fin 13)) C ∧ lengths C = m := by
  let rows : List (List ℕ × List ℕ) := [
    ([9,9,9,9,9,9,11,13],[9046678929514,9999966646341,12163390575876,6676535416196,2516957794631,2244288584804,3774766462015820,7325421698118945036]),
    ([9,9,9,9,9,9,12,12],[5715871894604,3586635530377,2483770594401,5646848337216,3722670318628,8830865216836,363885582069636481,399696816488285352]),
    ([9,9,9,9,9,10,10,13],[11100751922472,415683028171,322492893413,3337564227847,12174256774344,320142904131652,358591350612075,7099973470480803843]),
    ([9,9,9,9,9,10,11,12],[1278100966407,2582758165736,13200827518217,7870564630665,13581827713060,143289879671051,8279465634309314,228602933203573896]),
    ([9,9,9,9,9,11,11,11],[3505947476328,13203977641028,6600538719530,10318734656612,5888502956170,2571937348065419,4756561668181313,256405298028677]),
    ([9,9,9,9,10,10,10,12],[3510402162695,8874576877803,12267842575497,1242733480169,13230823024998,179263479548297,74090576910475,299806213929013318]),
    ([9,9,9,9,10,10,11,11],[10076232713290,2509745820995,4510052259206,12267634760812,389402444472327,143146270044170,4820645597845836,3420936292577344]),
    ([9,9,9,10,10,10,10,11],[1519650934027,207513521316,12311828239588,224438952043623,79405398560106,40963325404170,216981861343556,8238721560481889]),
    ([9,9,9,12,13,13,13],[4651723468096,8865121183779,5643628218475,370598301582503138,2499533226882737508,3647150751654948870,1491087306554186946]),
    ([9,9,10,10,10,10,10,10],[5877897766156,4777188926536,394868868284483,81573484470277,216954942104940,40960041093260,212287588958536,252900665338216]),
    ([9,9,10,11,13,13,13],[11239136821318,13582977892386,429987704507745,9265727631628576,2606670635352555909,8077639220106240161,6023707554387077131]),
    ([9,9,10,12,12,13,13],[3309578853580,12176401113290,147513941270816,299607030892630178,48598664207536230,12975227870091779116,11785994073945420033]),
    ([9,9,11,11,12,13,13],[219220872232,12403905731714,13587941161966858,10563387579763848,228570986974413991,80054389725993098,183742928322404740]),
    ([9,9,11,12,12,12,13],[11380765962272,11202423164196,10146439366913186,366031037316403564,146722139105636645,181414335858583846,10423876178605705323]),
    ([9,9,12,12,12,12,12],[6977343462732,2474079785251,397513180048535779,299636025847950342,361662510425997414,292782361981035843,442871296655655234]),
    ([9,10,10,10,13,13,13],[4675115069635,152840950582604,11042599251141,292539051715622,146588277861951713,9406026557039191169,434993292555522377]),
    ([9,10,10,11,12,13,13],[9013125546211,365084341771424,215816750670049,1130720011660483,182441078904204419,9627886981873992868,8506572134215065636]),
    ([9,10,10,12,12,12,13],[2416323103752,398095191021860,392843687496064,229977264652191780,48662195691757706,299678879079071937,5800998140114115972]),
    ([9,10,11,11,11,13,13],[10072102345832,144386439807010,4715054938269064,4506975512768683,430194975347906,3505074856295208198,8156134581266128901]),
    ([9,10,11,11,12,12,13],[353408226408,365348547366983,391473595156583,6831269375780903,362936947110581283,152183691199709222,9488317063137243201]),
    ([9,10,11,12,12,12,12],[8046701192193,188094136594662,433354785893605,189153528435322145,80266934435905637,261316875610394976,292745155691186470]),
    ([9,11,11,11,11,12,13],[5748949001323,4763362683846818,9077818395001957,5991384933806086,1456139946532034,193697946589537636,10557779346292181320]),
    ([9,11,11,11,12,12,12],[5845719983211,4763362683846818,9077818395001957,1456139946532034,329930604571630666,193697946589537636,188386237834407942]),
    ([10,10,10,10,12,13,13],[322307275066440,144214641115170,141089716777131,13472584008898,254879205771550725,4653702759363948776,3505074856295208198]),
    ([10,10,10,11,11,13,13],[144214641115170,141093166619013,13472584008898,10321266018061384,7964975180357637,4653702759363948776,3505074856295208198]),
    ([10,10,10,11,12,12,13],[148855089070242,189158150972772,45504373300418,5886923777313995,290490188374017125,191518578958217222,10557787834221300040]),
    ([10,10,10,12,12,12,12],[148855089070242,187230554501126,45504373300418,290490188374017125,188381802171272395,329930869830814024,193697946589768708]),
    ([10,10,11,11,11,12,13],[183966603682923,187230554501126,4763362683846818,9077818395001957,1456139946532034,193697946589537636,10557779346292181320]),
    ([10,10,11,11,12,12,12],[148855083870213,187063039461483,9077818395001957,1456139946532034,329930604571630666,78110654868858212,188386237834407942]),
    ([10,11,11,11,11,11,13],[148855089070242,9077818395001957,5886923777313995,6053060830930276,5991384933806086,1456139946532034,10557779346292181320]),
    ([10,11,11,11,11,12,12],[187063039461483,4763362683846818,9077818395001957,6053060830930276,1456139946532034,329930604571630666,188386237834407942]),
    ([11,11,11,11,11,11,12],[4763362683846818,5886931317852267,10175296287508808,6053060831128580,5984955367763974,1312141768498370,290490188374017125]),
    ([13,13,13,13,13,13],[7175646292128138252,8365758813012232236,9555871333494066252,10745983442061693036,11935673750481114252,12693440707138033836]) ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map (fun i => (k >>> (5*i)) % 32)
  let tab : List (List ℕ × List (List ℕ)) :=
    rows.map (fun z => (z.1, List.zipWith decode z.1 z.2))
  exact table_sound 13 9 78 (by decide) (by decide) tab
    (by decide +kernel) (by decide +kernel) m hb hs

end AlspachLongFinite

open SimpleGraph AlspachConjecture
namespace AlspachLongFinite

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_15_0 :
    let keys : List (List ℕ) := [
    [10,10,10,10,10,10,10,10,10,15],
    [10,10,10,10,10,10,10,10,11,14],
    [10,10,10,10,10,10,10,10,12,13],
    [10,10,10,10,10,10,10,11,11,13],
    [10,10,10,10,10,10,10,11,12,12],
    [10,10,10,10,10,10,11,11,11,12],
    [10,10,10,10,10,10,15,15,15],
    [10,10,10,10,10,11,11,11,11,11],
    [10,10,10,10,10,11,14,15,15],
    [10,10,10,10,10,12,13,15,15],
    [10,10,10,10,10,12,14,14,15],
    [10,10,10,10,10,13,13,14,15],
    [10,10,10,10,10,13,14,14,14],
    [10,10,10,10,11,11,13,15,15],
    [10,10,10,10,11,11,14,14,15],
    [10,10,10,10,11,12,12,15,15],
    [10,10,10,10,11,12,13,14,15],
    [10,10,10,10,11,12,14,14,14],
    [10,10,10,10,11,13,13,13,15],
    [10,10,10,10,11,13,13,14,14],
    [10,10,10,10,12,12,12,14,15],
    [10,10,10,10,12,12,13,13,15],
    [10,10,10,10,12,12,13,14,14],
    [10,10,10,10,12,13,13,13,14] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 15))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [500559451129888,117829489701952,462179592902019,224586459350144,259806075225248,190468186377346,365523362842880,401666687076640,331377603186913,15361574622554369465550],
    [117829489701952,462179592902019,224586459350144,259806075225248,190468186377346,365523362842880,401666687076640,331377603186913,16014668519049248,480049206954824047822],
    [115595100457312,469707328394627,224756995523712,259766511244302,190468186377346,365524637911296,151940108624908,329900135452898,258126996950027296,14990342731701883329],
    [117829489701952,469707328394627,224586459350144,259806075225248,190468186377346,365523362842880,331366774511751,16014668519049248,12540275057723680,15001879933012417742],
    [117829349606464,224586459677824,259806075225248,190468186377346,365523362842880,401666687076640,331366774511751,14789746768549251,512469392609578016,468808747906768078],
    [117829349606464,224586459677824,259806075225248,190468186377346,365523362842880,331366774511751,14789746768549251,12853333986452492,14648872984124622,512469392609578016],
    [111475014468672,324431206562048,504852344382721,436885452491072,472969520646496,437817427856705,8566537024524928844814,11003887467295888411726,12222562688200566968430],
    [117829349606464,224586459677824,259806075225248,365523362842880,401666687083532,16014668518722592,14789746768549251,6094981964075394,10603736784376034,14648872984124622],
    [497328328875040,322306562229504,182977688601728,395151132624192,505986040473890,13877252208179555,480049206954824047822,9785212245910643279918,12222562688200566968430],
    [500427149878304,401403823561024,470701847123265,111475008281664,324392642318792,516966328797790465,11936096375195996270,11003887467295888411726,15361574622554369465550],
    [154149778981952,502729422353537,259969138197696,466340144317824,397344779745602,194120230939727968,420038669281408423054,492308786623586375854,8566537024524928844814],
    [117829489701952,462179592902019,472999717471488,423705108974880,433664056007874,16396768763704608800,14231728077384325294,343871483353000610894,12222562688200566968430],
    [497259609398304,322505181049896,433664131578211,224586459350144,259806075225248,6241261250870185090,340479280171352852526,458106515912869943470,480049206954823949518],
    [433664131505611,190602138453120,395151166178624,505986040473890,15908943338450957,10320165491606784,48495172740421806,9785212245910643279918,12222562688200566968430],
    [497328328875040,182977688601728,395151132624192,505986040473890,10313809991350528,13877252208179555,305787882684707602497,480049206954824047822,12222562688200566968430],
    [462179592902019,183838936468512,395151122310240,505986045773090,14649929780958414,512399024123643008,120657253997381642,12222562688200566968430,13434216613283497184430],
    [497154350166029,433664131505611,395151132599616,499323343537442,5855286044755072,330245295854486784,48495172740422030,340479280171352852526,12222562688200566968430],
    [154149778981952,189367700621408,401639676646592,353254899125472,8352211723781316,514794928490022272,267704282016404026414,420033857584285979790,479663841089188699342],
    [497154479326464,433664131505611,224586459253796,259806075225248,10320165501744160,6241250556703607938,10639977505354778670,14316179132247048398,444273703296722736589],
    [120098236040480,256474109524006,189437399244930,400580094893058,15074514134336768,13883969185969899712,9445530941853697038,343871483352996512878,492308779127925843118],
    [322306260239616,433664131505611,190602138453120,505986040473890,509264208768053261,404629528416388416,1515474148138190,381955253096819003502,9785212245910643279918],
    [187066632011816,433664131578211,224586459350144,259806075225248,509198303697798528,469889835394571470,6241257162061319298,10640147062365095982,14659408235232522016942],
    [154149778981952,189367700621408,401639676646592,353254899125472,514794928490022272,267270766446412996,14989503595890777294,267704282016404026414,420033857584285979790],
    [154150044207392,189367538751595,190703293697088,331241237912611,370823634659543296,16473437578210706816,11939507712059052142,14989495043700823270,267808034361331233838] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 15 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_15_1 :
    let keys : List (List ℕ) := [
    [10,10,10,10,13,13,13,13,13],
    [10,10,10,11,11,11,12,15,15],
    [10,10,10,11,11,11,13,14,15],
    [10,10,10,11,11,11,14,14,14],
    [10,10,10,11,11,12,12,14,15],
    [10,10,10,11,11,12,13,13,15],
    [10,10,10,11,11,12,13,14,14],
    [10,10,10,11,11,13,13,13,14],
    [10,10,10,11,12,12,12,13,15],
    [10,10,10,11,12,12,12,14,14],
    [10,10,10,11,12,12,13,13,14],
    [10,10,10,11,12,13,13,13,13],
    [10,10,10,12,12,12,12,12,15],
    [10,10,10,12,12,12,12,13,14],
    [10,10,10,12,12,12,13,13,13],
    [10,10,10,15,15,15,15,15],
    [10,10,11,11,11,11,11,15,15],
    [10,10,11,11,11,11,12,14,15],
    [10,10,11,11,11,11,13,13,15],
    [10,10,11,11,11,11,13,14,14],
    [10,10,11,11,11,12,12,13,15],
    [10,10,11,11,11,12,12,14,14],
    [10,10,11,11,11,12,13,13,14],
    [10,10,11,11,11,13,13,13,13] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 15))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [154143638527040,502729422353537,423705108974880,400580094893250,6205187648141798496,15436302276060291079,8365829180715598862,13020202297837293002,15384650647981922597],
    [433664131505611,190602138453120,395151156913472,15908943338450957,10320165491606784,16191553295156514,1515474148138190,10895336965483291280840,12222562688200566968430],
    [433664131505611,190602138453120,505986040473890,15908943338450957,10320165491606784,12644672772277568,48495172740421806,381955253096819003502,9785212245910643279918],
    [497328328875040,182977688601728,505986040473890,10313809991350528,13877252208179555,12644672738723136,305787882684707602497,381955253096819003502,480049206954824047822],
    [433664131505611,190602138453120,505986040473890,15908943338450957,10320165491606784,404629528416388416,1515474148138190,381955253096819003502,9785212245910643279918],
    [500659239814157,401403823561024,392599079134465,13624198104913217,10380564554201344,335807762997973102,3652878287199607872,444811939948960974,12222562688200700103758],
    [500659239814157,401403823561024,111475008281664,10380564554201344,16155197774931201,481998559351444801,11936096375195996270,343867149309924379726,13883553228022521038],
    [500659239814157,401403823561024,392599079134465,13624198104913217,10380564554201344,3652878287199607872,10745848415935136878,444811939948960974,381955084006271880270],
    [502729422353537,466340144317824,397344779745602,8316090834912448,157849375088876608,194120230939727968,444071864363488398,15384649581987074245,8566537024524928844814],
    [433664131505611,182977688601728,505986040473890,12644672738723136,509264208768053261,330041620866054400,1515474148138190,305787882684707602497,381955253096819003502],
    [500659239814157,401403823561024,392599079134465,10380564554201344,481998559351444801,114139695621151808,11936096375195996270,444811939948960974,343867149309924379726],
    [190569055852640,434791656883392,397344779745602,14922685999356992,480770299441290374,5051180002851226848,16473437711421050912,8365758813012309038,14203694625888307342],
    [401403823561024,324392642328832,392599079134465,511417054684807588,435974339357222957,114139695621151808,335807762997973102,13900373123405038,12222562688200700103758],
    [189367700621408,353020956576992,469838590121166,160306979734325664,397910237792869568,267270766446412996,443921498833630372,16473437711354692992,267704282016404013102],
    [190569055852640,434791656883392,397344779745602,477525951979423753,443865156178577550,480770299441290374,5051180002851226848,16473437711421050912,8365758813012309038],
    [436885452491072,472969520646496,437817427856705,8566537024524928844814,9785212245910643279918,11003887467295888411726,12222562688200566968430,13441237417005072618638],
    [500559459200032,462179592902019,3770539187418176,5882845966992512,12644835913928000,16191553295156514,14649929780958414,12222562688200566968430,13434216613283497184430],
    [433664131505611,190602138453120,15908943338450957,10320165491606784,12644837021197632,16191553295156514,1515474148138190,340479280171352852526,12222562688200566968430],
    [466340144317824,397344779745602,4932792971527232,6066257216477280,16087341515060353,8316090834912448,14210299659798287502,15384649582193515654,8566537024524928844814],
    [182977688601728,505986040473890,15914506524001293,10313809991350528,13877252208179555,12644672738723136,433861038375705806,305787882684707602497,381955253096819003502],
    [401403823561024,392599079134465,15981782958900237,13624198104913217,10380564554201344,335807762997973102,13900373123405038,3652878287199607872,12222562688200700103758],
    [182977688601728,505986040473890,10313809991350528,13877252208179555,12644672738723136,509264208768053261,1515474148138190,305787882684707602497,381955253096819003502],
    [500659239814157,401403823561024,3566862097259584,10380564554201344,16155197774931201,481998559351444801,11936096375195996270,444811939948960974,343867149309924379726],
    [190569055852640,434791656883392,14922685999356992,12715032949504322,15024071857540326,5051180002851226848,16473437711421050912,8365758813012309038,14203694625888307342] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 15 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_15_2 :
    let keys : List (List ℕ) := [
    [10,10,11,11,12,12,12,12,15],
    [10,10,11,11,12,12,12,13,14],
    [10,10,11,11,12,12,13,13,13],
    [10,10,11,12,12,12,12,12,14],
    [10,10,11,12,12,12,12,13,13],
    [10,10,11,14,15,15,15,15],
    [10,10,12,12,12,12,12,12,13],
    [10,10,12,13,15,15,15,15],
    [10,10,12,14,14,15,15,15],
    [10,10,13,13,14,15,15,15],
    [10,10,13,14,14,14,15,15],
    [10,10,14,14,14,14,14,15],
    [10,11,11,11,11,11,11,14,15],
    [10,11,11,11,11,11,12,13,15],
    [10,11,11,11,11,11,12,14,14],
    [10,11,11,11,11,11,13,13,14],
    [10,11,11,11,11,12,12,12,15],
    [10,11,11,11,11,12,12,13,14],
    [10,11,11,11,11,12,13,13,13],
    [10,11,11,11,12,12,12,12,14],
    [10,11,11,11,12,12,12,13,13],
    [10,11,11,12,12,12,12,12,13],
    [10,11,11,13,15,15,15,15],
    [10,11,11,14,14,15,15,15] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 15))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [434791656883392,397344779745602,16087341515060353,14922685999356992,157849375088903392,194120230939727968,444071864364599438,480770299437096070,8566537024524928844814],
    [324392642328832,392599079134465,12844922356930880,13624198104913217,511417054684807588,335807762997973102,13900373123405038,3652878287199607872,381955084006271781966],
    [324392642328832,392599079134465,12844922356930880,13624198104913217,511417054684807588,13900373123405038,3652878287199607872,10745848415935138894,11936096375195993198],
    [324392642328832,392599079134465,12844922356930880,511417054684807588,435974339357222957,114139695621151808,335807762997973102,13900373123405038,381955084006271781966],
    [190569055852640,434791656883392,12715032951859267,477525951979423753,261429962906612782,443865156178577550,480770299441290374,5051180002851226848,16473437711421050912],
    [295024840639680,330246583879904,9476076777703585,458106507351016216750,8566537024524928844814,9785212245910643279918,11003887467295888411726,15361574622554369465550],
    [324395863554304,392599079134465,512675061569696901,411391184503642432,114139695621151808,337004965578047630,370852532108430414,13900372959730894,13951178859431134626],
    [293823211209856,332443702987936,299886751100897505,11867281027469838478,8566537024524928844814,9785212245910643279918,14659408235232522016942,15361574622554369465550],
    [155410475780416,437823769644353,484320997287198977,267704282016404026382,305787876329182824494,11003887263606393310286,12222562688200566968430,13441237409509412085902],
    [155410475780416,437823769644353,15498271913190719745,9555871135286954030,267704282016404026382,11003887263606393310286,12222562688200566968430,13441237409509412085902],
    [155075272058892,437823769644353,15498271913190367275,267704282016404026382,305787876329182824494,343871476987691306062,12222562688200566968430,13441237409509412085902],
    [224586057682957,259806075487392,199720228920473619586,340484705995683071182,420038677843262149774,458106515912869943470,13883557860308423910,8566537024524928844814],
    [462179592902019,16017902694401152,3770539187418176,5882845966992768,8312760100490560,16191553295156514,14637878136280270,379758415670383022190,13434216613283497184430],
    [397344779745602,4932792971527392,6066257216477280,16087341515060353,13913333017248960,14922685999356992,444071864363488398,15384649582193515654,8566537024524928844814],
    [462179592902019,16017902694401152,3770539187418176,5882845966992768,8312760100490560,14637878136280270,517217011840124194,379758415670383022190,447708785391972846766],
    [437718507226304,6094946497009760,10391770216412289,14922927267088393,13876944880964043,15024085816184038,5051180002851226848,13020193740292139075,267704281974786393102],
    [397344779745602,4932792971527392,16087341515060353,13913333017248960,14922685999356992,194120230939727968,444071864363488398,480770299437096070,8566537024524928844814],
    [392599079134465,15981782958900237,12844922356930880,13624198104913217,10380564554201344,335807762997973102,13900373123405038,3652878287199607872,381955084006271781966],
    [392599079134465,15981782958900237,12844922356930880,13624198104913217,10380564554201344,13900373123405038,3652878287199607872,10745848415935138894,11936096375195993198],
    [387377363553510,13913669066982592,14922884608040000,12715032945244482,157851770640664615,195144666539169888,514794928481907841,261430128489694222,454518228028425834702],
    [434791656883392,6094946497009760,12715032951859267,13876944880961678,477525951979423753,261429962906612782,480770299441290374,5051180002851226848,16473437711421050912],
    [387377363553510,13913669066982592,14922884608040000,157851770640664615,195144666539169888,514794928481907841,406881054247565634,261430128489694222,14203694625888307342],
    [295024840639680,10569998373357792,9476076777703585,14231728077380130990,8566537024524928844814,9785212245910643279918,11003887467295888411726,15361574622554369465550],
    [296127395203233,9440556402050240,10569998373357792,267704282248624112654,455415298476167272622,9785212245910643279918,11003887467295888411726,15361574622554369465550] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 15 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_15_3 :
    let keys : List (List ℕ) := [
    [10,11,12,12,12,12,12,12,12],
    [10,11,12,12,15,15,15,15],
    [10,11,12,13,14,15,15,15],
    [10,11,12,14,14,14,15,15],
    [10,11,13,13,13,15,15,15],
    [10,11,13,13,14,14,15,15],
    [10,11,13,14,14,14,14,15],
    [10,11,14,14,14,14,14,14],
    [10,12,12,12,14,15,15,15],
    [10,12,12,13,13,15,15,15],
    [10,12,12,13,14,14,15,15],
    [10,12,12,14,14,14,14,15],
    [10,12,13,13,13,14,15,15],
    [10,12,13,13,14,14,14,15],
    [10,12,13,14,14,14,14,14],
    [10,13,13,13,13,13,15,15],
    [10,13,13,13,13,14,14,15],
    [10,13,13,13,14,14,14,14],
    [11,11,11,11,11,11,11,13,15],
    [11,11,11,11,11,11,11,14,14],
    [11,11,11,11,11,11,12,12,15],
    [11,11,11,11,11,11,12,13,14],
    [11,11,11,11,11,11,13,13,13],
    [11,11,11,11,11,12,12,12,14] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 15))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [324395863554304,12563170532301057,512675061569696901,411391184503642432,435974339453846946,114139695621151808,337004965578047630,370852532108430414,13900372959730894],
    [469535597592970,15135031165255937,448331538036395329,261429956690654222,9785212042235439581230,11003887263606121803854,13332687392846534217838,13444541967349834846666],
    [296127562975393,9440556402050240,338239947951704288,15001537717333040334,455415298476167272622,8566537031955971608590,9785212245910643279918,11003887467295885330884],
    [330005269812295,9440556402050240,303234624486773761,305532438844695218222,455415298476167272622,480049206954660371662,8566537031955971608590,11003887467295920884164],
    [293823211209856,9371460971202785,10893130334974648480,11867281027469838478,15001879933012319438,8566537024524928844814,9785212245910643279918,14659408235232522016942],
    [437823769644353,13666209357891904,15498271913190719745,9555871135286954030,267704282016404026382,343871476987691306062,12222562688200566968430,13441237409509412085902],
    [292793460656353,9402342766118016,10893515259510923424,305783548642090551342,381955084006267717774,458106507351016216750,480049206720581576910,8566537024524928844814],
    [257573620483264,3843113327166528,198639154347362390114,302395679503049720846,334648111316141737070,420038677843262149774,458117458183870093486,480049206954824045806],
    [469535594643850,484320997288184065,448331538036395329,261429956690654222,420141936479682433482,9785212042235439581230,11003887263606121803854,13332687392846534217838],
    [293823211209856,299886751078549729,370852532108432462,10893130334974648480,15001879933012319438,8566537024524928844814,9785212245910643279918,14659408235232522016942],
    [330005269812295,302096466855560384,303234624486773761,15001537717370789070,305532438844695218222,455415298476167272622,8566537031955971608590,11003887467295920884164],
    [155410475780108,484320997280121089,448331538036395329,267704282016404026382,305787876329182824494,343871476987691306062,381955084006267719790,13441237409509412085902],
    [293823211441184,299642530704066785,10893130334974648480,11867281027469838478,15001879698769946830,267704283082597109774,9785073725037729548334,14659408235232522016942],
    [182977688601728,404634748882027840,16580150574244465057,8365764111669199886,340479280171352852936,381955084006267717774,420038669281408519342,15361574622554369465550],
    [292793460590817,300874968649994249,11936096375195866254,311686682571772659872,267704282016393888782,340479280171352852526,458106507351016216750,480060157856397302990],
    [390365357414816,11575456531687388320,8084290540723668164,7247774047777587655,10749221703622176846,15421840598264714446,9785212245910643279918,14551346611871290764430],
    [182977688601728,12948144873527346496,16580150574244465057,8365764111669199886,11936101659275593870,340479280171352852936,420038669281408519342,15361574622554369465550],
    [182977688601728,12948144873527346496,16580150574244465057,11936101659275593870,264314338134389228558,340479280171352852936,420038669281408519342,480049206954824047822],
    [13976242715297795,10427911200872459,5954244576556161,5882882581145632,6058454133585186,11575934773824654,14644441611800901,8365766542944702478,14428135023278453460288],
    [8347907959886880,16126859247917216,16022299440461154,13663675494959424,15135026870029664,14010429479292225,10494124522213411,305787882684999010350,420038669281412617358],
    [13976242715297795,10427916625577152,5882882581145632,6058454133585186,11587761681271950,14644441614754949,190535826449797185,261430204467023886,14428135023278453460288],
    [13976242715297795,10427916625577152,5954246785011777,5856457688157216,6058454133585186,11587761676029070,468633892235093125,8365766516851904526,445503082606650230080],
    [8347907959886880,16126951946390688,16022299440461154,15946498594417673,10494124522213411,13876944885197966,13985191194166298944,14172201758025289025,9555871135286954030],
    [16051016857298317,14789746972866947,8312760100267104,16163031620003881,13662978432899173,402267607003465738,188251070944871808,370886540929435758,4655680024875373774] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 15 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_15_4 :
    let keys : List (List ℕ) := [
    [11,11,11,11,11,12,12,13,13],
    [11,11,11,11,12,12,12,12,13],
    [11,11,11,12,12,12,12,12,12],
    [11,11,11,12,15,15,15,15],
    [11,11,11,13,14,15,15,15],
    [11,11,11,14,14,14,15,15],
    [11,11,12,12,14,15,15,15],
    [11,11,12,13,13,15,15,15],
    [11,11,12,13,14,14,15,15],
    [11,11,12,14,14,14,14,15],
    [11,11,13,13,13,14,15,15],
    [11,11,13,13,14,14,14,15],
    [11,11,13,14,14,14,14,14],
    [11,12,12,12,13,15,15,15],
    [11,12,12,12,14,14,15,15],
    [11,12,12,13,13,14,15,15],
    [11,12,12,13,14,14,14,15],
    [11,12,12,14,14,14,14,14],
    [11,12,13,13,13,13,15,15],
    [11,12,13,13,13,14,14,15],
    [11,12,13,13,14,14,14,14],
    [11,13,13,13,13,13,14,15],
    [11,13,13,13,13,14,14,14],
    [12,12,12,12,12,15,15,15] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 15))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [13976242715297795,10427916625577152,5954246785011777,6058454133585186,14644441614754949,188252242596662304,370808373805911182,13921969231456666944,8365766516851904526],
    [4932792961206311,13913669066982592,14922884608040000,15024076152507622,195144666539169888,514794928481907841,406881054247565634,261430128489694222,14203694625888307342],
    [16017902367965485,14789746972866947,8312760100490251,120657253997381642,188251070944871808,517217011840124194,370857816188160110,437215309857888357,4541406455796942],
    [9374585704383680,10567890551048416,9475732071940481,335949566485630030,8566537031955971608590,9785212245910643279918,14659408235232522016942,15349242914854038384846],
    [9440556402050240,10569998373357792,9476076777703585,14231728077380130990,267704282248624112654,9785212245910643279918,11003887467295888411726,15361574622554369465550],
    [9440556402050240,10569998373357792,9476076844812449,343871483352996416590,455415298476167272622,480049206954660371662,8566537031955971608590,9785212245910643279918],
    [15025139028656522,15135031165255937,448331538036395329,261429956690654222,420141936479682433482,9785212042235439581230,11003887263606121803854,13332687392846534217838],
    [9402342766118016,9369390741063905,468808740586560718,10893130334974648480,11936096375195866190,8566537024524928844814,9785212245910643279918,14659408235232522016942],
    [9440556402050240,9476076844812449,338239947951704288,15001537717333040334,343871483352996416590,455415298476167272622,8566537031955971608590,9785212245910643279918],
    [9440556402050240,10560168633993440,303234624486773761,305787882684999010350,343871483352997530052,455415298476167272622,480049206954660371662,8566537031955971608590],
    [3843151981872192,8209241712559296,6207473564799897698,9449858619620623374,15001537984896177390,334648111316152222830,13441237690984388788366,14659480292757840468142],
    [13666209357891904,14010360759815489,15498271913190719745,9555871135286954030,267704282016404026382,343871476987691306062,420038669047169127566,12222562688200566968430],
    [3843151981872192,8209241712559296,6207473564799897698,302395679503049720846,334648111316141737070,420038677843262149774,458117458183870093486,480049206954824045806],
    [9402342766118016,299886751078549729,370852532108432462,468808740586560718,10893130334974648480,8566537024524928844814,9785212245910643279918,14659408235232522016942],
    [8354204374697164,477532307623817221,406881054257002818,335811988808567886,267808075905767998478,302397932437842692142,13441237417005072618638,14659408235232522016942],
    [10569998369196256,302096466855560384,303234624486773761,10745983854781237700,15001537717370789070,455415298476167272622,8566537031955971608590,9785212245910643279918],
    [10560168633865287,302096466855560384,303234624486773761,15001537717370789070,305532438844695218222,343871483352999528900,455415298476167272622,8566537031955971608590],
    [5855286042657920,404622930227962912,518129705445139521,264314331769550710798,340479280171352852936,381955084006267717774,454729589113548281291,480049206720781884622],
    [14010360558488897,480804447748948362,15498271913190686977,8365758813012309006,11936096375195866222,13129435514990076046,9785212042235439581230,11003887263606121803854],
    [5855286042657920,404634748882027840,16550944378884105281,14210299659798383790,15001537710018272462,340479280171352852936,381955084006267717774,8458058820300455707662],
    [5855286042657920,518129705445139521,12947933767294813504,8259822867798459406,340479280171352852936,381955084006267717774,454729589113548281291,480049206720781884622],
    [8354204576023756,15281033852394450949,13020193735895623810,8369002174454212622,9449935388639496238,10745983642179243086,420141943975342871694,14551418671567618578606],
    [5855286042657920,12947933767294813504,16550944378884105281,14210299659798383790,15001537710018272462,264314338134389589006,340479280171352852936,381955084006267717774],
    [411238278236451008,361733016704496800,252634074099909828,335913117034852430,469889835394667726,8566537024524604802062,9785212245910643279918,13441237417005072618638] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 15 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_15_5 :
    let keys : List (List ℕ) := [
    [12,12,12,12,13,14,15,15],
    [12,12,12,12,14,14,14,15],
    [12,12,12,13,13,13,15,15],
    [12,12,12,13,13,14,14,15],
    [12,12,12,13,14,14,14,14],
    [12,12,13,13,13,13,14,15],
    [12,12,13,13,13,14,14,14],
    [12,13,13,13,13,13,13,15],
    [12,13,13,13,13,13,14,14],
    [13,13,13,13,13,13,13,14],
    [15,15,15,15,15,15,15] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 15))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [267334546496849100,477532307623817221,406881054257002818,335811988808567886,8369002165114930190,302397932437842692142,13441237417005072618638,14659408235232522016942],
    [267334546496849100,477532307623817221,406881054257002818,335811988808567886,267808069283677775886,302397932437842692142,458106199253521143982,13441237417005072618638],
    [480804447748948362,484320997280121089,448331538036395329,8365758813012309006,11936096375195866222,13129435514990076046,9785212042235439581230,11003887263606121803854],
    [300874968649994249,299501793215645921,370852532108432526,9740593754904070304,15421840598264714446,267704282016393888782,340479280171352852526,14182495049092492893358],
    [300874968649994249,299501793215645921,370852532108432526,9740593754904070304,267704282016393888782,340479280171352852526,458117458252586491054,480049206954824045774],
    [267334546496849100,477532307623817221,13020193735895628098,8369002174454212622,9449935388639496238,10745983642179243086,420141943975342871694,14551418671567618578606],
    [361733009099044064,447299198390480014,13126207415485957312,8178969420540064964,15386903582980873422,267704282008105944078,305787882547268552878,343871483344242904142],
    [405433991961982240,11575456531687388320,8084290540723668164,7247774323372852238,10749221703617982542,14209991562303214734,15036474732629367022,9785212245910643279918],
    [195176825228461184,12937054203924481344,8257671354622817326,8437886844580923848,14210299659802482123,433862105708628174,530564818376024196109,379752992879034830958],
    [12973784283302016288,11575456531687388320,8084290540723668164,7247774323372852238,10749221703620364334,14209991562303214734,15036474732629367022,305787882684707602510],
    [8566537024524928844814,9785212245910643279918,11003887467295888411726,12222562688200566968430,13441237417005072618638,14659408235232522016942,15361574622554369465550] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 15 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem complete_15 (m : Multiset ℕ) (hb : ∀ k∈m,10 ≤ k ∧ k ≤ 15) (hs : m.sum=105) :
    ∃ C : Multiset (Cycle (completeGraph (Fin 15))), IsCycleDecomposition _ C ∧ lengths C=m := by
  exact fast_keys 15 10 105 (by decide) _ (together (together bucket_15_0 (together bucket_15_1 bucket_15_2)) (together bucket_15_3 (together bucket_15_4 bucket_15_5))) (by decide +kernel) m hb hs

end AlspachLongFinite

open SimpleGraph AlspachConjecture
namespace AlspachLongFinite

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_0 :
    let keys : List (List ℕ) := [
    [11,11,11,11,11,11,11,11,11,11,11,15],
    [11,11,11,11,11,11,11,11,11,11,12,14],
    [11,11,11,11,11,11,11,11,11,11,13,13],
    [11,11,11,11,11,11,11,11,11,12,12,13],
    [11,11,11,11,11,11,11,11,12,12,12,12],
    [11,11,11,11,11,11,11,11,14,17,17],
    [11,11,11,11,11,11,11,11,15,16,17],
    [11,11,11,11,11,11,11,11,16,16,16],
    [11,11,11,11,11,11,11,12,13,17,17],
    [11,11,11,11,11,11,11,12,14,16,17],
    [11,11,11,11,11,11,11,12,15,15,17],
    [11,11,11,11,11,11,11,12,15,16,16],
    [11,11,11,11,11,11,11,13,13,16,17],
    [11,11,11,11,11,11,11,13,14,15,17],
    [11,11,11,11,11,11,11,13,14,16,16],
    [11,11,11,11,11,11,11,13,15,15,16],
    [11,11,11,11,11,11,11,14,14,14,17],
    [11,11,11,11,11,11,11,14,14,15,16],
    [11,11,11,11,11,11,11,14,15,15,15],
    [11,11,11,11,11,11,12,12,12,17,17],
    [11,11,11,11,11,11,12,12,13,16,17],
    [11,11,11,11,11,11,12,12,14,15,17],
    [11,11,11,11,11,11,12,12,14,16,16],
    [11,11,11,11,11,11,12,12,15,15,16] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [18441289374702624,18169822989820931,18409542384650248,8037507660814496,11581684539560128,13868534711002369,16237801565915520,17459426763310496,17213204954778692,6132434139717090,12715241468176420,16767240391040302231649],
    [18306119370213408,3840979907951680,17117686018739328,15812162958501024,11732213736671521,13985001056208128,14078427240315233,17043747990902211,13834338203675746,15026284749033760,374344370616341696,563140705667669957643],
    [18306119537985568,3840979907951680,17115247510914176,15812162958501024,11698261584843968,11732213736671521,13985001056208128,14078427240315233,17043747990902211,13834344388012387,17598147052114680843,15386915920240873760],
    [18306119537985568,3840979907951680,17115247510914176,15812162958501024,11697948083782848,11732213736671521,13985001056208128,14078427240315233,17043747990902211,442699020460271971,413502457689346272,15386915920240873760],
    [18305920599665696,15180413971730816,3952997920048192,8413952947520704,11827975131595904,11662741275674913,17244915593610496,16164002588793120,543179951938311553,196237893650844802,406887927372716192,515848507520823713],
    [18306119537985568,3840979907951680,17115247510914176,15812162958501024,14020252102035776,15205566339385696,17043747990902211,13834344389383491,460500387025627753793,13763827619908865049563248,15011751046044887147451536],
    [14820470013035727,7050320352216192,10560098643969120,15981785117952384,17182284143694850,17031899182929347,16903113842866245,16333696509742465,16983697988519922439695,615462085418661457239072,15011751046282615734768784],
    [18306119537985568,3840979907951680,15812162958501024,13877089906427136,14078427240315233,17352879297203593,10353456232704067,15035209551844480,573970954498984962461984,430225855526421788692592,508114809258847090479312],
    [18306119537985568,8424770687370432,15173758790741376,17244915593610496,16164002588793120,13978237528129889,16120265860025761,545399935709091267,3902832357303958592,12515904193210442754067536,16259673896283106895337648],
    [18306157999425568,3840979907951680,11732213736671521,17244915593610496,16164002588696768,12921951802822880,16120265859772833,545399935709091267,383318370584393455904,388867065201193845296208,17507007027171720241060016],
    [18306119537985568,3840979907951680,17115252755860516,15812162958501024,14021499527733568,13834331504159075,14053069914606913,484670643120671072,17713968451873373656515,15770037833423061619856,13763827619908865049563248],
    [3840979907951680,17152762708133056,16090669251835104,13702641155836224,15147051704944992,17043747990909379,16050985688762785,449709263653408065,19188411855908781497376,391121999520219743161424,469117220188902559683728],
    [18342272166855936,3840979900040672,11827975131595904,16332391878822272,17043748055029187,12703113210370208,16304738602756204,11830365172852139393,17878453005629993986,469117220188668483966096,13763827619908865049563248],
    [18306295438391328,3840979907951680,17152762708133056,16093908295983328,17043747990909379,16050985688739917,15206426342426945,15421537341296223584,448998163754111811904,12214388485801676640291,15089563844089827368735888],
    [18306119279653920,3840979908403264,16093908295531744,11765328639101408,12892202595485984,17043747987920323,9228383774181473,10929679062417908161,310406464768112231616,426645888977759950113293,547093969599116093856976],
    [18310418609015840,6160025010774404,10665754843382848,9060395719758944,17152762877908006,16093908295983328,16054151959523745,17300970916425086081,18079304528236349829315,17096686892187893538000,508098668366344448252080],
    [18310515501960224,6160015315742848,12612747406915746,11837382188219488,16118066443420864,10702000274779394,9546204872507745,333675514005041580256,566278474502979895425,9742485943617789455,17507007017319029795887627],
    [18306119279653920,3840979908403264,16093908295531744,11765328639101408,12892202595485984,17043747987920323,9228383774181473,310406464768112231616,349746738028568748481,13332684030554998441040,547093969599116093856976],
    [3840979907951680,7257200336667776,8384200370830496,17244915593610496,16164266604501280,7291318330036289,16120265464459265,598483713339139720608,18304257332801902613955,15878587789339171887280,17097106861415163141328],
    [18310418609015840,6160025010843776,11697948083782848,11732213736671521,17244915593610496,16164002588793120,547580302606840961,413502457689346272,515848507520823713,11267980766511471239628848,17507007027171720240995536],
    [18310418609015840,6160025010843776,12917306621723712,16332391878822272,17459426763310496,10323525609172226,361991506865044576,547580302606840961,16696052329586429313,469223462047814711874704,13763827619908865049563248],
    [3840979900040672,11827975131595904,16332394971866496,17043748055029187,12703113210370208,16304738602756204,586952709339579648,369698911651629441,572107185748539028482,14659913130895726449808,13763827619908865049563248],
    [18306119537985568,3840979907951680,10569861031888000,9447359632313504,16332391878822272,17459426763310496,545399935709091267,521751635187535233,310548332623141800161,430119613122152032798864,508114809258847090479280],
    [18310418609015840,6160025010843776,15168115267961920,18335942752607617,11765328639101184,12892202595485984,547580302606840961,341549548847729921,14397123583827092350048,17725065960999392290000,430115175061979531382896] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_1 :
    let keys : List (List ℕ) := [
    [11,11,11,11,11,11,12,13,13,15,17],
    [11,11,11,11,11,11,12,13,13,16,16],
    [11,11,11,11,11,11,12,13,14,14,17],
    [11,11,11,11,11,11,12,13,14,15,16],
    [11,11,11,11,11,11,12,13,15,15,15],
    [11,11,11,11,11,11,12,14,14,14,16],
    [11,11,11,11,11,11,12,14,14,15,15],
    [11,11,11,11,11,11,13,13,13,14,17],
    [11,11,11,11,11,11,13,13,13,15,16],
    [11,11,11,11,11,11,13,13,14,14,16],
    [11,11,11,11,11,11,13,13,14,15,15],
    [11,11,11,11,11,11,13,14,14,14,15],
    [11,11,11,11,11,11,14,14,14,14,14],
    [11,11,11,11,11,12,12,12,12,16,17],
    [11,11,11,11,11,12,12,12,13,15,17],
    [11,11,11,11,11,12,12,12,13,16,16],
    [11,11,11,11,11,12,12,12,14,14,17],
    [11,11,11,11,11,12,12,12,14,15,16],
    [11,11,11,11,11,12,12,12,15,15,15],
    [11,11,11,11,11,12,12,13,13,14,17],
    [11,11,11,11,11,12,12,13,13,15,16],
    [11,11,11,11,11,12,12,13,14,14,16],
    [11,11,11,11,11,12,12,13,14,15,15],
    [11,11,11,11,11,12,12,14,14,14,15] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [3840979900040672,11827975131595904,16332391878822272,17043748055029187,12703113210370208,16304738602756204,586952709339579648,11830365172852139393,17878453005629993986,14659913130895726449808,13763827619908865049563248],
    [18310418609015840,9060395719758944,11698261584839872,11764958567336225,17112121693287553,12921784388227296,197120800353169536,10921736323797652544,17664811173667680451,547107419291305904348368,567202110751980553279751],
    [18306157999425568,3840979941506112,11732213736671521,17244915593610496,12921951802822880,16120265859772833,517248075626094784,17452797942753007043,383318370584393455904,452421985165526469712,17507007027171720241060016],
    [18307087794775072,3840979907951680,10569861031888000,9447359632313504,16332391878822272,17459426763310496,521751635187535233,17452797941712819651,310548332623141800161,15878587789331651596464,430119613122152032798864],
    [18269835395925007,3840979638716736,14085124566136992,14020252343044104,15147051713176928,13985999705312577,545405336599900323,10825993185264764032,9931678288561890729249,13441237706375401998480,518132807623127636240],
    [18306157999425568,3840979941506112,11732213736671521,17244915593610496,12921951802822880,16120265859772833,517248075626094784,383318370584393455904,558489534168096227779,452421985165526469712,547093969599116257533125],
    [18306157999425568,3840979941506112,11732213736671521,17244915593610496,12921951802822880,16120265859772833,517248075626094784,383318370584393455904,558489534168096227779,14477503525296847038544,17096686549965063068869],
    [18310418596760608,10665754843382848,9052831611262048,11274816899516709,17382733554036931,12921784388227296,6307555516648534144,11978710900112660493,17344605861139717520,560732120037689036842,17433810346687240740183248],
    [18310418596760608,9060398030861472,11765169659316513,17112186278229121,17250792158703811,12921784388227296,6307865611301425155,10921728732346680384,11978710905545458880,17096686549972382031056,567202110443883058110704],
    [3811366108445760,8418351827190976,15180410857432448,16155573590694176,17043747990909091,16120472696632705,17658805563539103755,15317029560990894433,598843970325112230944,419959767265909443664,508114423892981455132848],
    [18307087794775072,3840979907951680,10569861031888000,9447359632313504,16332391878822272,17459426763310496,17452797941712819651,16446479917569609089,310548332623141800161,13441237917481634531472,15878587789331651596464],
    [18310418596464000,3772843461870656,9504536384472256,10535950020118752,17111884463453313,18545877532813761,17450612051353605568,201851699699048001664,312815931282868865185,494003232132763359408,17096674507289081943280],
    [14894205780475009,6103475290386560,3772843461936192,9505635896104976,17281446484287536,3462577211609537,160546818930077153293,348592699309484548320,312815996563281351712,127270822781224292528,533816214790446781680],
    [3840979907951680,10569861031888000,9447359632313504,11697948083782848,11732213736671521,585788259888990240,545399935709091267,303269856072435937,413502457689346272,547093969599122536307920,18150467544063377704952048],
    [11827975131595904,16332394971866496,17043748055029187,12703113210370208,16304738602756204,586952709339579648,122911356801301568,369698911651629441,17878349554641844640,14659913130895726449808,13763827619908865049563248],
    [3840979907951680,10569861031888000,9447359632313504,11697948083782848,11732213736671521,545399935709091267,303269856072435937,413502457689346272,18745224316447687695,547093969599122536307920,16580249843940084359408],
    [18306157999425568,11732213736671521,17244915593610496,12921951802822880,16120265859772833,122911356868410432,517248075626094784,545399935709091267,383318370584393455904,452421985165526469712,17507007027171720241060016],
    [11836635836988512,16332391878822272,17459426763310496,10701999939235074,16292945860038017,585933395488541728,413353811895161920,547580302606840961,202232453872442816640,13441237910067251021936,469223462047814711874704],
    [18310418596464000,3772843461870656,9504536384472256,10535950020118752,17111884463453313,545331626605971904,593468081050040361,305484307889338529,6459244219860069396608,15808103428248430581936,17096674507289081943280],
    [3840979907951680,15180105033024896,16237831863436608,17457261935894635,17043747990902211,585795825215550496,189583685746525312,12121666180907012387,16590452169267945537,458117941143244215440,13763827619908865049563248],
    [8418351827190976,15180410848126336,16155573590694176,17043747990909091,14958036680655201,121963713103182912,515848507520824705,18708280725754418208,17658805563539103755,12225882755334389402704,508114423892981455132848],
    [8418351827190976,15180410848126336,16155573590694176,17043747990909091,16120472696632705,121963713103182912,478657173780965729,17658805563539103755,598843970325112230944,419959767265909443664,508114423892981455132848],
    [18310418609015840,6160025010843776,9060395719758944,11697959894942912,17111884456113281,341292199850509376,413502457689346272,12014493723748731173,564978266782263849155,17008331896998582197456,18227007118384301285616],
    [9472643185083408,7285924986925184,15168115267961920,16166549065959648,13736388218587424,581492230730227073,305483372660197537,559608672078430057601,496200988483558543568,569594314665183451399,9973206080038521482400] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_2 :
    let keys : List (List ℕ) := [
    [11,11,11,11,11,12,13,13,13,13,17],
    [11,11,11,11,11,12,13,13,13,14,16],
    [11,11,11,11,11,12,13,13,13,15,15],
    [11,11,11,11,11,12,13,13,14,14,15],
    [11,11,11,11,11,12,13,14,14,14,14],
    [11,11,11,11,11,13,13,13,13,13,16],
    [11,11,11,11,11,13,13,13,13,14,15],
    [11,11,11,11,11,13,13,13,14,14,14],
    [11,11,11,11,11,13,17,17,17,17],
    [11,11,11,11,11,14,16,17,17,17],
    [11,11,11,11,11,15,15,17,17,17],
    [11,11,11,11,11,15,16,16,17,17],
    [11,11,11,11,11,16,16,16,16,17],
    [11,11,11,11,12,12,12,12,12,15,17],
    [11,11,11,11,12,12,12,12,12,16,16],
    [11,11,11,11,12,12,12,12,13,14,17],
    [11,11,11,11,12,12,12,12,13,15,16],
    [11,11,11,11,12,12,12,12,14,14,16],
    [11,11,11,11,12,12,12,12,14,15,15],
    [11,11,11,11,12,12,12,13,13,13,17],
    [11,11,11,11,12,12,12,13,13,14,16],
    [11,11,11,11,12,12,12,13,13,15,15],
    [11,11,11,11,12,12,12,13,14,14,15],
    [11,11,11,11,12,12,12,14,14,14,14] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [18310418609046912,3630902442132544,17041613659640845,11697817087280320,15142869379844385,413502457689346049,6307865611104033806,17522569683417544001,18995448069876885633,16681722593989079248,15011751046044887147451536],
    [3811366108445760,8418351827190976,15180410857432448,16155573590694176,16120472696632705,545399935678525603,18713875040916542496,17658805563539103755,15317029560990894433,419959767265909443664,508114423892981455132848],
    [18307087794775072,3840979907951680,10569861031888000,16332391878822272,17459426763310496,302315613268937888,17452797941712819651,9704499815072139489,16446479917569609089,13441237917481634531472,15878587789331651596464],
    [18342272154253327,14825033643296771,11731974137940257,17069271907807683,17185689317809163,339158111055250560,11978699080762295488,9704635393311317027,309570765700078963872,568403860196182725862,51967146400665673968],
    [9472643185083408,7285924986925184,15168115267961920,16166549065959648,13736388218587424,305483372660197537,18607751383372471681,311662690001203796128,559608672078430057601,496200988483558543568,569594314665183451399],
    [11762030104217856,16229216292248864,18233381856805231,16973547586328003,16055598356505708,18702614905894351904,3834258015860601312,17816528521232684100,16539892296234279393,14206014593274679408,391122179664204837981264],
    [18306295430323232,7257200336667776,17352879399900611,17149404447377569,14080534082981185,3933135997261528128,8158600693505499296,15510581016833329504,17309634727800772848,459408163931746994496,14733554337273053614605],
    [18310418596463631,6160025010843776,10665752792175680,9060396122412128,11697127745225920,12014912694587230497,17522569683027473537,13234330445872762080,562996682852370755779,421249902122379680976,531582499812774453488],
    [9583486262385696,18169822989820192,11697948083782848,11732213736684833,10390603032858050,13225117497651564768,11267980766511471239628848,12515904193210442754067536,17507007027171720240995536,18150467544063377704952048],
    [9583486262385696,18169822989820192,3772843461870656,17041613659641280,18545877532873153,564042364786724736450,547107419291305904348368,12515904193210442754067536,13763827619908865049563248,16259673896283106895337648],
    [9583518582643744,18169822989820192,3772843461870656,17041613659641280,18545877300089281,18049353590795047177666,17097106852853309414608,12515904193210442754067536,13763827619908865049563248,16259673896283106895337648],
    [18306119537985568,3840979907951680,10569861031888000,9447359632313504,17043916632495555,9931678288562078877921,430119613122152032798864,547093969599116093856976,16259673896283106895337648,18150467544063377704952048],
    [17176893981885835,18135596124013696,5924490186132527,15174607474885952,11751760037291116,569570937870815212975430,469112787520975762723984,497559956691261987101040,264690075610194822603279,11267980765148076821186608],
    [16332394971866496,17043748055029187,12703113210370208,16304738602756204,586952709339579648,122911356801301568,378495204211393664,369698911651629441,558698423582243232,14659913130895726449808,13763827619908865049563248],
    [3840979907951680,10569861031888000,9447359632313504,11732213736671521,585788259888595983,374334339080684736,545399935709091267,303269856072435937,413502457689346272,547093969599122536307920,16580249843940084359408],
    [3840979907951680,15171550531913088,17457261935894635,17043747990902211,585795825215550496,189583685746525312,519609648222078272,378811627515154723,16590452169267945537,458117941143244215440,13763827619908865049563248],
    [3840979907951680,9447359632313504,11697949493068992,11732213736671521,585788259888595983,338235563891065984,545399935709091267,303269856072435937,13232078646059076832,17096686549972579259622,16580249843940084359408],
    [9472643185083408,15168115267961920,18335986512764289,9546355226904737,187429910081745024,304358095703999680,340425722236635360,546492542009586817,450113969146967696480,496200988483558543568,567202121702882126536944],
    [18306119279645728,3840979907951680,10566761411871872,9477188034347079,302315269863312544,519585458966267200,545399935709091267,449563166014441889,420142437037521275024,18094532507224960666976,15362032046014042739920],
    [3840979907951680,15171550531913088,17043747990902211,16201613217798401,189583638368653664,558632381948436587,378811627515154723,18745505791424410656,16627508743106505184,14316320900656501904,13763827619908865049563248],
    [14824965997561859,11697948096267456,11732213736671521,17185690480742624,338235563891065984,545399935709091267,303269856072435937,9674086430474964128,17762620631326921958,599847178125926498671,16580249843940084359408],
    [18306157999425568,11732213736671521,17244915593610496,12921951802822880,122911356868410432,517248075626094784,515848507520823713,11978698850581911840,17452797942690922947,14477503525296847038544,17096686549965063068869],
    [6160025010843776,9060395719758944,11697959894942912,17111884456113281,585933395488803872,341292199850509376,413502457689346272,12014493723748731173,564978266782263849155,569593962821466661104,17008331896998582197456],
    [18306119279641613,3840949769209312,9447352183228576,13839732180257185,341581334023603328,555292140796821955,303199648354928865,529664394177328481600,565441893588428499970,420147862851485272208,14340976687695795408] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_3 :
    let keys : List (List ℕ) := [
    [11,11,11,11,12,12,13,13,13,13,16],
    [11,11,11,11,12,12,13,13,13,14,15],
    [11,11,11,11,12,12,13,13,14,14,14],
    [11,11,11,11,12,12,17,17,17,17],
    [11,11,11,11,12,13,13,13,13,13,15],
    [11,11,11,11,12,13,13,13,13,14,14],
    [11,11,11,11,12,13,16,17,17,17],
    [11,11,11,11,12,14,15,17,17,17],
    [11,11,11,11,12,14,16,16,17,17],
    [11,11,11,11,12,15,15,16,17,17],
    [11,11,11,11,12,15,16,16,16,17],
    [11,11,11,11,12,16,16,16,16,16],
    [11,11,11,11,13,13,13,13,13,13,14],
    [11,11,11,11,13,13,15,17,17,17],
    [11,11,11,11,13,13,16,16,17,17],
    [11,11,11,11,13,14,14,17,17,17],
    [11,11,11,11,13,14,15,16,17,17],
    [11,11,11,11,13,14,16,16,16,17],
    [11,11,11,11,13,15,15,15,17,17],
    [11,11,11,11,13,15,15,16,16,17],
    [11,11,11,11,13,15,16,16,16,16],
    [11,11,11,11,14,14,14,16,17,17],
    [11,11,11,11,14,14,15,15,17,17],
    [11,11,11,11,14,14,15,16,16,17] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [5717819466756224,3952997920048192,17459426764359072,16304738766491009,269130150129746112,514582861327735938,18749868655745502240,16627331851853564288,17522569641379433892,16590533462192167088,469101079296400081130640],
    [14824965997561859,11697949493068992,17043747990909379,17185690479598603,375186537815574817,303265619055741153,18745224316435085327,10823786156190172288,9674086430474964128,568403860341137872102,51967153896326111472],
    [18342272154253327,14825033643296771,11731974137940257,17185689317809163,546216704206942659,303269856040978657,10853059553768080512,11978699080762295488,309570765700078963872,568403860196182725862,1623973325020799216],
    [18305920599665696,15180413971730816,3772843461870656,17041613659641280,543179951938311553,593468081050030529,12515904193210442754067536,13763827619908865049563248,15011751046044887147451536,16259673896283106895337648],
    [14824965997561859,11697949493068992,17043747990909379,17185690479598603,375186537815574817,18745224316435085327,10823786156190172288,9674086430474964128,9704635394307918049,17762620631326921958,51967153896326111472],
    [14824965997561859,11835666222613696,11724586794191137,17043747991066051,338243317380942976,9663953331313380512,9704499809783716961,17598173208966634507,17762620635621889254,599847178125926512655,1623973559264289008],
    [9583486262385696,4973583049728288,15812162958501024,13834344389388643,550822558317317570,17526010025908146688,547093969599116257533136,11267980766511471239628848,13763827619908865049563248,16259673896283106895337648],
    [6160025010843776,3952997920048192,8413952947520704,16093908223409250,547580302606840961,599995796983422159904,17096686892187893538000,15011751046044887147451536,16259673896283106895337648,18150467544063377704952048],
    [8418184323470368,18135661890677952,13985001056208128,14078427240315233,543185694274005185,492381309448613933344,391228248442628667903056,567202110751980553279728,11267980766511471239628848,16259673896283106895337648],
    [18092776334208463,12533447307344960,2747826935344513,13519983874312336,552201373908087817,12065615231147927843296,7538141117099640239216,380567148352514399670320,11491195261913439270906114,530567995017976406547728],
    [8418184323470368,18135661890677952,13985001056208128,14078427240315233,543185694274005185,15756201902351418798368,391228248442628667903056,508114809258847094577328,567202110751980553279728,11267980766511471239628848],
    [18135661890677952,16332391878822272,17459431058277792,16304731250298241,543185554929497281,282463801792054429910336,315490280101797449173040,391117567978186410593360,469117220188902723357860,508114808950749595310256],
    [14824965997561859,11835666222613696,11724586794191137,17043747991066051,10823786156190182528,9663953331313380512,9704499809783716961,17598173208966634507,17762620635621889254,50749166410998000,599847178125926512655],
    [9574896327793696,11827975131595904,11662741275674913,12715247730397381,18884063221307939104,17626321860549840322,17725065960999387177200,11267980766511471239628848,13763827619908865049563248,17507007027171720240995536],
    [8418184323470368,18135661890677952,16974552949208385,16201686428361121,16696540481144789312,17876236222752623968,391121999520219743161424,544266620703954633399504,11267980766511471239628848,15011751046044887147451536],
    [18088554689375424,5038383564325984,2753739090208961,18376558111036899,6242353272540150848,277250821712053962176,553453071385013429511,15011751046044887147451536,16259673896283106895337648,17507007027171720240995536],
    [8461023611848864,18135661890546880,10569861031888000,9477050595805409,9674099624606012448,556222150807423199425,17725065960999392290055,547093980550017830788304,11267980766511471239628848,16259673896283106895337648],
    [8418184355022144,18135665279675584,5924490179609728,15180105033024896,12121666175734260834,556222150876142676161,348653096418289954850864,469118320158993529616528,508109044343226561075376,530567995006082699501071],
    [9583518571267392,18169822989820297,10151077230318660,8413952941229248,6279612596827029569,18049353590795047177666,15878587779710761179312,18227006977646808832240,13648127332981548541938186,16943163847814913799200976],
    [18088554689375424,13985001056208128,14078427240315233,16974552946062529,8664092576548197408,15756201902351418798368,17725065960999392289991,391228248275204563928176,508114809258847094577328,11195822656633460021528624],
    [1200056086736064,13985001056208128,14078427367029089,16974552946062529,8620251876146972160,15756202968814212755744,349869458019795625672784,391228248275204563928176,508114809258847094577328,567202110751980553279728],
    [12600647264535566,18203666144527680,17244915593839872,12844924572801312,530896891843759587747,528228871701323068455,534284589151666052304,391122006275619184217168,11267980766511471239628848,13763827619908865049563248],
    [9574896323771424,18451297966693664,11697719489333537,12822959977797669,387579055376275965056,569593972449507189968,18050402759909633854914,13370770993512683999344,11267980766511471239628848,17161648202608219331368176],
    [8418077284832288,18135661890677952,7010900704887280,15812162958501024,556222150876142676161,453401266340844863843,18188934468617566854598,469117220188902559683728,508114820209748663736496,11267973848982443598547184] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_4 :
    let keys : List (List ℕ) := [
    [11,11,11,11,14,14,16,16,16,16],
    [11,11,11,11,14,15,15,15,16,17],
    [11,11,11,11,14,15,15,16,16,16],
    [11,11,11,11,15,15,15,15,15,17],
    [11,11,11,11,15,15,15,15,16,16],
    [11,11,11,12,12,12,12,12,12,14,17],
    [11,11,11,12,12,12,12,12,12,15,16],
    [11,11,11,12,12,12,12,12,13,13,17],
    [11,11,11,12,12,12,12,12,13,14,16],
    [11,11,11,12,12,12,12,12,13,15,15],
    [11,11,11,12,12,12,12,12,14,14,15],
    [11,11,11,12,12,12,12,13,13,13,16],
    [11,11,11,12,12,12,12,13,13,14,15],
    [11,11,11,12,12,12,12,13,14,14,14],
    [11,11,11,12,12,12,13,13,13,13,15],
    [11,11,11,12,12,12,13,13,13,14,14],
    [11,11,11,12,12,12,16,17,17,17],
    [11,11,11,12,12,13,13,13,13,13,14],
    [11,11,11,12,12,13,15,17,17,17],
    [11,11,11,12,12,13,16,16,17,17],
    [11,11,11,12,12,14,14,17,17,17],
    [11,11,11,12,12,14,15,16,17,17],
    [11,11,11,12,12,14,16,16,16,17],
    [11,11,11,12,12,15,15,15,17,17] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [8418077284832288,18135661890677952,7010900704887280,15812162958501024,556222150876142676161,453401266340844863843,352124572579862498248944,469117220188902559683728,508114820209748663736496,582045552566911795109318],
    [16332391878822272,17459426763310496,17111881175118977,16304731257481313,201851699561645612128,19199865503376099880992,11003887467296358139952,13441237706375401998448,508114809258847090383024,15011751046044887147451536],
    [16332391878822272,17459426763310496,17111881175118977,16304731257481313,201851702923531263072,19199865503376099880992,11003887467296358139952,430119613122152032798832,469112781583372454565008,508114809258847090383024],
    [9476075508793519,17313471966492800,18373225088455712,17393359395298433,8379881683166179099840,16864012579036915470405,14553652694642769106064,15872715095417405184176,16767405933586129622256,530568111859811939991660],
    [8418077284832288,18135661890677952,7010900704887280,15812162958501024,17799108828036622362817,14501749799975275266403,14659913130903204990096,15878588131560924518576,352124572579862498248944,582045552566911795109318],
    [18310418596760608,11697959894942912,11716890212796709,197120800344780928,341292199850509376,289932663293645920,551736588560150723,413502457689346272,556244147038888176,560732120037694977153,17433810346687240740183248],
    [3840979907951680,9447359632313504,11732213736671521,585788259888595983,338235563891065984,374334339080684736,545399935709091267,303269856072435937,413502457689346272,17096686549972579259622,16580249843940084359408],
    [6160025010843776,9060395719758944,11697959894942912,585933395488803872,341292199850509376,374940486809684261,547580302595273857,413502457689346272,17655570834023428291,17799812705244356848,17433810346687240740183248],
    [3840979907951680,11697949493068992,11732213736671521,585788259888595983,338235563891065984,302315200952077472,545399935709091267,303269856072435937,13232078646059076832,534271454695194367206,16580249843940084359408],
    [9472643185083397,12612741900571712,17289037872215169,197120800347000839,370474307792813152,551837298995536384,517248082837479625,342463998127746306,16507152240666345889,13185185568500984385648,17097106852853309505744],
    [18306119279645728,3840979907951680,10566761411871872,302315269863312544,519585458966267200,545399935709091267,303269856072024135,449563166014441889,570125637200886631776,420142437037521275024,15362032046014042739920],
    [14824965997561859,11732213736671521,17185690480742624,338235563891065984,374334339080684736,545399935709091267,303269856072435937,18745224316435071343,9674086430474964128,17762620631326921958,16580249843940084359408],
    [14824965997561859,11697949493068992,17043747990909379,338243317380942976,375186537815574817,303265619055741153,549942095344933899,18745224316435085327,9674086430474964128,568403860341137872102,51967153896326111472],
    [14824965997561859,11835666222613696,11724586794191137,338243317380942976,302095605916961952,545399935709091267,303265619055741153,17762620635621889254,599847178125926512655,563141542686932179979,1623973559264289008],
    [14824965997561859,11697949493068992,17043747990909379,338243317380942976,375186537815574817,303265619055741153,18745224316435085327,9674086430474964128,17598177747267591179,17762620635621889254,51967153896326111472],
    [14824965997561859,11835666222613696,11724586794191137,338243317380942976,302095605916961952,545399935709091267,9704499809783716961,17598173208966634507,17762620635621889254,599847178125926512655,1623973559264289008],
    [8418184323470368,18135661890677952,16237831863436608,558632381961211232,543185694374668481,518453965707544993,391121999520219743161424,11267980766511471239628848,15011751046044887147451536,17507007027171720240995536],
    [11724586794191137,16901739392537830,37799077290224,378741319124026560,545399935714100675,18774739804076048815,10823786156190182528,9663953331313380512,9704499809783716961,17598173208966634507,485784479307071457283],
    [8418184323470368,18135661890677952,11662741275674913,378495204377855104,410321702186260640,17381942217027266753,14659913130903242642576,11267980766511471239628848,17507007027171720240995536,18150897934213446403097840],
    [8418184323470368,18135661890677952,16974552949208385,558632381961211232,518453965707544993,16696540481144789312,391121999520219743161424,544266620703954633399504,11267980766511471239628848,15011751046044887147451536],
    [12600647264536000,9511190496773312,17255031255439521,582517312719396896,340422547254413536,530896855283960947213,553764206787427508464,11267980766511471239628848,12515904193210442754067536,17502750826342577233632464],
    [18135661890546880,10569861031888000,9477050595805409,270752755579163680,302315613268937888,556222150807423199425,17725065960999392290055,547093980550017830788304,11267980766511471239628848,16259673896283106895337648],
    [18088554689375424,13985001056208128,16974552946062529,269382871129592864,450509675744967009,492381309448479715616,391228248275204563928176,508114809258847094577328,567202110751980553279728,11195822656633460021528624],
    [18092776334208463,17256292934627337,12533447307344960,87930461941312897,446991448008722576,12065615231147927843296,11892723386016064344112,7538141117099640239216,11491195261913439270906114,530567995017976406547728] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_5 :
    let keys : List (List ℕ) := [
    [11,11,11,12,12,15,15,16,16,17],
    [11,11,11,12,12,15,16,16,16,16],
    [11,11,11,12,13,13,13,13,13,13,13],
    [11,11,11,12,13,13,14,17,17,17],
    [11,11,11,12,13,13,15,16,17,17],
    [11,11,11,12,13,13,16,16,16,17],
    [11,11,11,12,13,14,14,16,17,17],
    [11,11,11,12,13,14,15,15,17,17],
    [11,11,11,12,13,14,15,16,16,17],
    [11,11,11,12,13,14,16,16,16,16],
    [11,11,11,12,13,15,15,15,16,17],
    [11,11,11,12,13,15,15,16,16,16],
    [11,11,11,12,14,14,14,15,17,17],
    [11,11,11,12,14,14,14,16,16,17],
    [11,11,11,12,14,14,15,15,16,17],
    [11,11,11,12,14,14,15,16,16,16],
    [11,11,11,12,14,15,15,15,15,17],
    [11,11,11,12,14,15,15,15,16,16],
    [11,11,11,12,15,15,15,15,15,16],
    [11,11,11,13,13,13,13,17,17,17],
    [11,11,11,13,13,13,14,16,17,17],
    [11,11,11,13,13,13,15,15,17,17],
    [11,11,11,13,13,13,15,16,16,17],
    [11,11,11,13,13,13,16,16,16,16] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [8418184323470368,13985001056208128,14078427240315233,578833815498304704,543185694274005185,15756201902351418798368,12225882763832145871984,508114809258847094577328,567202110751980553279728,11267980766511471239628848],
    [13985001056208128,14078427367029089,16974552946062529,269382871129592864,577660808390159552,15756202968814212755744,349869458019795625672784,391228248275204563928176,508114809258847094577328,567202110751980553279728],
    [11835666222613696,11724586794191137,17043747991066051,474398903821109251,18774739804075636751,10823786156190182528,9663953331313380512,9704499809783716961,17598173208966634507,17762620635621889254,50749166410998000],
    [18135661890677952,10569861031888000,9477050595805409,302315613268937888,8664088178533238208,17381942219979008193,553453071385013429511,11267980766511471239628848,16259673896283106895337648,17507007027171720240995536],
    [9574896327793696,11827975131595904,11662741275674913,406887927372716069,18884063221307939104,17626321860549840322,17725065960999387177200,430119613122152036896880,11267980766511471239628848,17507007027171720240995536],
    [8418184323470368,18135661890677952,16974552949208385,518453965704339873,16696540481144789312,17876236222752623968,391121999520219743161424,469117220188902723359888,544266620703954633399504,11267980766511471239628848],
    [9574896327793696,11827975131595904,11662741275674913,406887927372716069,18884063221307939104,564075086247176342978,553908311281230849264,430119613122152036896880,11267980766511471239628848,17507007027171720240995536],
    [16976815249961088,15168115267961920,18335980366240129,547580302606840961,18749868655632220335,451026992747923285088,13441099457947132563568,518132807623127638256,15011751046044887147451536,16259673896283106895337648],
    [8461023611848864,18135661890546880,9477050595805409,338235553025721472,9674099624606012448,556222150807423199425,17725065960999392290055,508114809258846926805168,547093980550017830788304,11267980766511471239628848],
    [18135661890677952,7010900704887280,15812162958501024,269378473083081760,17381942214879783105,453401266340844863843,352124572579862498248944,469117220188902559683728,508114820209748663736496,582045552566911795109318],
    [13985001056208128,14078427240315233,16974552946062529,578833815498304704,8664092576548197408,15756201902351418798368,12225882763832145871984,17725065960999392289991,508114809258847094577328,11195822656633460021528624],
    [8418184323471392,18135661890677952,17457157006167392,518453965704339873,16302379984341992768,17799108833262799365281,14659913130903210103952,352124398953483832657968,391121999520219743161424,544266620703954633399504],
    [9583518571267200,18169822989820297,10151082404774980,262867331887662272,561840208918392245698,200947602964025017346,569593962821462563056,13328249348614792808970,16259673896283106895337648,16943163847814913799200976],
    [3840979907951680,17152762708133056,16050983541279137,545399935709091267,599849436633481944096,527364985371795657952,531510371781401910480,391122006037826336064624,469117220188902559683728,16299703330923056622344368],
    [9574896323771424,18451297966693664,12822959977797669,374329848469391649,387579055376275965056,569593972449507189968,18050402759909633854914,13370770993512683999344,352124398953483476142128,17161648202608219331368176],
    [8418077284832288,18135661890677952,15812162958501024,224348822556386800,556222150876142676161,453401266340844863843,14659913121274999706768,352124572579862498248944,508114820209748663736496,582045552566911795109318],
    [17245956049437952,2762351480812865,16190841440803239,269381898354071872,529662036824268506240,18943729180217073380544,11003893130914071347280,11892651328654260994160,15401099797479203936432,17507007027445699355843080],
    [8418077284832288,18135661890677952,15812162958501024,224348822556386800,556222150876142676161,14501749799975275266403,14659913121274999706768,15878588131560924518576,352124572579862498248944,582045552566911795109318],
    [18310418596760608,6159516018517260,15812157427097703,437104425923787105,14551572987331067773072,17943283307177528374401,15757062029685376061728,13444557985200684994672,15878587789606530516144,341569541064496333815888],
    [18270698905744847,12533445063640128,11506951227063392,17670442761423302665,2814085980117905455,10958841401072397570,14320329756526151824,12178148747280460789449840,13539404531508109409094157,530567995017976406547728],
    [18270698614069679,12533445063640128,11506951227063392,17670442761423302665,2814085980117905455,10958841401072397570,458231137827181201552,391122006037826336064624,13539404531508109409094157,530567995017976406547728],
    [8418311226332544,18135661879143616,11827975098041472,11830365172852139052,17381942217027266753,13130294509557651616,14659913130903242642576,17096674507288918269136,12513399801948026611762697,18150897934213446403097840],
    [8418311056557440,18135661890677952,11662741275674913,11871681453427360896,17381942217027266753,13130294509557651616,14659913130903242642576,387648389979808667273264,547093584233250622184656,18150897934213446403097840],
    [18135661890869263,5924490037003392,15172304939517984,8592034982542017920,17381942212731974982,12121651123825414435,349869458126414918259760,469117220188902723359888,497559969042042783374544,16580249843940084359408] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_6 :
    let keys : List (List ℕ) := [
    [11,11,11,13,13,14,14,15,17,17],
    [11,11,11,13,13,14,14,16,16,17],
    [11,11,11,13,13,14,15,15,16,17],
    [11,11,11,13,13,14,15,16,16,16],
    [11,11,11,13,13,15,15,15,15,17],
    [11,11,11,13,13,15,15,15,16,16],
    [11,11,11,13,14,14,14,14,17,17],
    [11,11,11,13,14,14,14,15,16,17],
    [11,11,11,13,14,14,14,16,16,16],
    [11,11,11,13,14,14,15,15,15,17],
    [11,11,11,13,14,14,15,15,16,16],
    [11,11,11,13,14,15,15,15,15,16],
    [11,11,11,13,15,15,15,15,15,15],
    [11,11,11,14,14,14,14,14,16,17],
    [11,11,11,14,14,14,14,15,15,17],
    [11,11,11,14,14,14,14,15,16,16],
    [11,11,11,14,14,14,15,15,15,16],
    [11,11,11,14,14,15,15,15,15,15],
    [11,11,12,12,12,12,12,12,12,13,17],
    [11,11,12,12,12,12,12,12,12,14,16],
    [11,11,12,12,12,12,12,12,12,15,15],
    [11,11,12,12,12,12,12,12,13,13,16],
    [11,11,12,12,12,12,12,12,13,14,15],
    [11,11,12,12,12,12,12,12,14,14,14] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [6159516025790848,13877461420940324,14078155643238753,18749868655633730592,17522569683418910977,492381096484977938720,420142444451904784496,11011854159115316199504,16259673896283106895337648,18150467544063377704952048],
    [9517790442626080,18169820995651872,15173813778364800,17626321865884995010,14210304062152458593,277253354815045665984,496309074874451761328,391122006029328579595344,567202110751980553279751,11267980766511471239628848],
    [12533445063640128,11312234589731936,10323525242330466,18709195377927559183,15544743737304584576,556217367998487860577,12222562485006866973808,518132807634742581520,469223462047814843009168,13539404531508109409422416],
    [12533445063640128,11312234589731936,10701999941492066,18709195377916182959,17670442761423302665,556216408191438859649,14663396410371112863888,391122006037826336064624,423106391609628419034192,16580249844311762704656],
    [18092776334208463,17256292934627337,12533447307344960,2813774782122007937,14303726031435106448,12065615231147927843296,11221870372962343168258,11892723386016064344112,7538141117099640239216,530567995017976406547728],
    [18310418609015852,6160024912310400,9511202173715648,10893507292375007712,9775533036961728673,17943111314971105014913,15881890395987690855600,16580249743851202582791,352230641358286328170544,543640537347254523270352],
    [18135661890677952,15168115338945600,18406355259169153,17596807605397915072,556222148840632920071,451026968418300634208,530896710150338517168,555026295536438482160,12519299547041509918411856,15011751046044887147451536],
    [9574896323771424,11697719489333537,12822959977797669,18884063221315214624,387579055376275965056,564075086247176342978,569593972449507189968,13370770993512683999344,536556999665633356551408,11267980766511471239628848],
    [11765156840409344,16974552974665769,17290375677054209,16335976943831976224,275843556445060666752,592725828064773319872,553814451470897161456,352124398953782332885040,391121789865044222280816,547093584233250622184656],
    [12533445063640128,11312234589731936,10323525242330466,18709195377927559183,497285788677871800704,556217367998487860577,12222562485006866973808,14663406269482499475600,518132807634742581520,13539404531508109409422416],
    [18270698614069263,12533445063640128,11312234589731936,10958847940025888002,497280099936843862400,556216096994315382145,13222217760652250221648,14663406269482499475600,391122006037826336064624,16580249844311762704656],
    [18441467989559552,15167945721291840,18335942752615649,17305131127911191760,313750135667077199881,18049353589600925366337,12222561596899808283728,13441099211656527941744,15878587779677606323376,460707954682270189003872],
    [18161919208753408,15139290637997088,16994474950598896,17626321866149236162,10049023891368987508041,18020743098781591109825,14289319410909837476193,12220333166838715327536,12114186703370955342125,15435865936268832772272],
    [11765328639101184,12883406502463776,17290379972021505,276134069741954434432,591524669885556894912,556221839851801352233,341669189315904670213,553908311281231008968,391122006037826336064624,17506994695464019909914832],
    [17244927308143872,12575544219801888,9446289136992675,421037275332845023246,596319801926564152640,528228871831505209761,381956176101362404432,11003887475862297183748,16693618886922351285456,13763833204372402988978288],
    [12533445063640128,11312234589731936,10323525242330466,598694252093681893551,497431979743900897664,556217367998487860577,381955077656459478128,518132807634742581520,241220515747188487654480,469223462047814843009168],
    [8418283444279616,15206357656773696,15143001346088070,592749648984193472527,337209453471835861040,556222151039653287233,14394817358211756506208,11892688449000767095920,14659912910168931767440,16580249843940419903728],
    [8418283444283408,15206357656773696,15143001346088070,592749648984193472527,371543853464545264752,10790702511108275810352,17799108833268905191617,14394817358211756506208,14659912910168931767440,518132807623138121991],
    [16332391878822272,17459426772747680,197120800146600064,413353811899614272,361991600481909856,547376824236225665,342463998127746306,513952490074738049,406959180974557296,18749868655640710176,15011751046044887147451536],
    [3840881123703872,16893350145037763,262451445719182368,547687985115630628,505989214668792992,304358469558900752,340422547248061696,434893390852827491,305485407400954017,568403850306859998416,508114809258853369256112],
    [12612741900571712,17034843245289984,303124925595616261,370474307792813152,411037586298478793,553006287296771201,342463997727350120,366250707793228846,410194013176498288,6475035004386156843015,17097106852853309505735],
    [14824965997561859,11732213736671521,585788259888595983,338235563891065984,374334339080684736,545399935709091267,303269856072435937,549942095383763979,9674086430474964128,17762620631326921958,16580249843940084359408],
    [12612741900571712,17289037872215169,303124584471823365,197120800347000839,370474307792813152,551837298995536384,517248082837479625,342463998127746306,16507152240666345889,534284589151665922054,13185185568500984385648],
    [9472643185380384,9325520993072291,374344239718696128,376478664396087330,547587894184850561,552025349177127107,413460431345195136,15812184434317584,201851699561645612128,349495562361833034816,533816213726373780688] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_7 :
    let keys : List (List ℕ) := [
    [11,11,12,12,12,12,12,13,13,13,15],
    [11,11,12,12,12,12,12,13,13,14,14],
    [11,11,12,12,12,12,13,13,13,13,14],
    [11,11,12,12,12,12,15,17,17,17],
    [11,11,12,12,12,12,16,16,17,17],
    [11,11,12,12,12,13,13,13,13,13,13],
    [11,11,12,12,12,13,14,17,17,17],
    [11,11,12,12,12,13,15,16,17,17],
    [11,11,12,12,12,13,16,16,16,17],
    [11,11,12,12,12,14,14,16,17,17],
    [11,11,12,12,12,14,15,15,17,17],
    [11,11,12,12,12,14,15,16,16,17],
    [11,11,12,12,12,14,16,16,16,16],
    [11,11,12,12,12,15,15,15,16,17],
    [11,11,12,12,12,15,15,16,16,16],
    [11,11,12,12,13,13,13,17,17,17],
    [11,11,12,12,13,13,14,16,17,17],
    [11,11,12,12,13,13,15,15,17,17],
    [11,11,12,12,13,13,15,16,16,17],
    [11,11,12,12,13,13,16,16,16,16],
    [11,11,12,12,13,14,14,15,17,17],
    [11,11,12,12,13,14,14,16,16,17],
    [11,11,12,12,13,14,15,15,16,17],
    [11,11,12,12,13,14,15,16,16,16] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [14824965997561859,17043747990909379,338243317380942976,302095605916961952,378741319123764416,375186537815574817,303265619055741153,18745224316435085327,17598177747267591179,17762620635621889254,51967153896326111472],
    [12844924571984073,17289037872215169,403607740831798336,370474307792813152,551837298995536384,342463998127746306,366251176170488225,9699986703099462661,6307865616502362119,412037049015655762032,534284589151665922054],
    [9472643185380384,9325520993072291,374344239718696128,547587894184850561,552025349177127107,413460431345195136,6307865611301425376,10921736323797652544,16681756678718397648,505990136137554192,385514162466481217570],
    [18306119537985568,3840979907951680,548887581016884416,515005065002983648,545399935709091267,513631542039677345,13332687408254718968944,15011751046044887147451536,16259673896283106895337648,17507007027171720240995536],
    [9583486262385696,3952997920048192,581434335674249504,269246494112482496,550822558317317570,196237893650844802,391117567978186410593360,547093969599122536307920,16259673896283106895337648,18150467544063377704952048],
    [11835666545935552,16901739392537830,375175851936942369,545399935714100675,1656280193376496,18774739804076048815,15180764978345969667,10823786156190182528,9663953331313380512,9704499809783716961,17598173208966634507],
    [18269636715949088,11312237510016096,413353811899614272,543179951938311553,342463998127746306,15544743737304584576,420034350639144407152,12515904193210442754067536,15011751046044887278586000,18398857950067760880195856],
    [9582661628664864,15812162958501024,159145861498288416,550822723640004034,442699020460439907,17526010025908146688,14551356111484085145712,547093969599116257533136,11267980766511471239628848,16259673896283106895337648],
    [9583486262385696,3952997920048192,581434335674249504,269246494112482496,196237893650844802,17626321866140847554,391117567978186410593360,529473870244216093973712,583264227788297510002928,16259673896283106895337648],
    [3840979907951680,16093908281343200,585790458912245792,545399935709091267,513631707634993569,562896274271578920969,416646481507619308656,469117219880805228188816,16259513990622816887848112,17507007027171720240995536],
    [18124808640759040,17398850380893536,306671560396342281,519610619636516160,332499297038142914,530897276670683908513,13441237910067251024964,18202373209905640414416,11267980766511471239628848,12515904193210442754067536],
    [9583486262385984,3952997920048192,581434335674249504,269246494112482496,196237893650844802,564032302056307330498,18227006810286802018544,508114808950749595310256,529473870244216093973712,12515762175301965138997328],
    [18305951840995360,16050990863583649,122911357054464064,515005065189670112,545399935709091267,562896300704955144201,426645997063802172064066,469117219880805228188816,508109812206957790182576,547093969607678111161552],
    [13985001056208128,14078427240315233,270752862617801760,578833815498304704,543185694274005185,15756201902351418798368,12225882763832145871984,17725065960999392289991,508114809258847094577328,11267980766511471239628848],
    [18305951840995360,16050990863583649,122911357054464064,515005065189670112,545399935709091267,18019280801957225207817,13332680890299291124034,469117219880805228188816,508109812206957790182576,547093969607678111161552],
    [18270698905744847,11506951227063392,401070242036497472,87940186878684545,17670442761423302665,10958841401072397570,14320329756526151824,12178148747280460789449840,13539404531508109409094157,530567995017976406547728],
    [8421448498615680,18135661879143616,378495203140535424,369830021101069356,17381942217027266753,13130294509557651616,458122285340726236304,547093584233250622184656,12513399801948026611762697,18150897934213446403097840],
    [18135661890677952,11553090989113409,269385959242630528,370990045380838528,17381942217027266753,13130294509557651616,14659913130903242642576,17096674507288918269136,12513399801948026611770416,18150897934213446403097840],
    [8418184323471392,18135661890677952,521766890035774784,518453965704339873,17876236222752623968,17381942219989391521,14659913130903210103952,391121999520219743161424,544266620703954633399504,11267980766511471239628848],
    [18135661890677952,16974552949208385,269382871129592864,518453965704339873,16696540481144789312,17876236222752623968,349869458116851505563696,391121999520219743161424,469117220188902723359888,544266620703954633399504],
    [16329263879062848,10390596812705218,518454371716172193,444072345874934946,17670348300025597280,314039531624093418505,598484661160043316480,18202373209900402835664,11267980766511471239628848,12515904193219989528939600],
    [16974552974665769,17290375677054209,376485430200305920,519335052506794272,8620111138895500672,592725828064773319872,553814451470897161456,391121789865044222280816,547093584233250622184656,11267980766511471239628848],
    [9582661628664864,4973308171827488,513459921782940832,442699020460439907,17626324064908250562,560832320829297562112,14551356111484085145712,17096686549965063068880,352230641358286328170544,16259673896283106895337648],
    [8418184323471392,18135661890677952,558629018117868896,518453965704339873,16302379984341992768,556222151039660532897,14659913130903210103952,352124398953483832657968,391121999520219743161424,544266620703954633399504] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_8 :
    let keys : List (List ℕ) := [
    [11,11,12,12,13,15,15,15,15,17],
    [11,11,12,12,13,15,15,15,16,16],
    [11,11,12,12,14,14,14,14,17,17],
    [11,11,12,12,14,14,14,15,16,17],
    [11,11,12,12,14,14,14,16,16,16],
    [11,11,12,12,14,14,15,15,15,17],
    [11,11,12,12,14,14,15,15,16,16],
    [11,11,12,12,14,15,15,15,15,16],
    [11,11,12,12,15,15,15,15,15,15],
    [11,11,12,13,13,13,13,16,17,17],
    [11,11,12,13,13,13,14,15,17,17],
    [11,11,12,13,13,13,14,16,16,17],
    [11,11,12,13,13,13,15,15,16,17],
    [11,11,12,13,13,13,15,16,16,16],
    [11,11,12,13,13,14,14,14,17,17],
    [11,11,12,13,13,14,14,15,16,17],
    [11,11,12,13,13,14,14,16,16,16],
    [11,11,12,13,13,14,15,15,15,17],
    [11,11,12,13,13,14,15,15,16,16],
    [11,11,12,13,13,15,15,15,15,16],
    [11,11,12,13,14,14,14,14,16,17],
    [11,11,12,13,14,14,14,15,15,17],
    [11,11,12,13,14,14,14,15,16,16],
    [11,11,12,13,14,14,15,15,15,16] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [18092776334208463,12533447307344960,552201380253806601,87930461941308801,14303726031435106448,12065615231147927843296,11221870372962343168258,11892723386016064344112,7538141117099640239216,530567995017976406547728],
    [18135661890677952,17457157006167392,269385070152849440,518453965704339873,16302379984341992768,17799108833262799365281,12222417481711732427856,14659913130903210103952,352124398953483832657968,544266620703954633399504],
    [5038383564325984,18376558111032495,81186056673864896,195073539924068864,276826424111813170624,90234526071612942537,496200988489799571632,553453071385013429511,15011751046044887147451536,17507007027171720240995536],
    [9574896323771424,12822959977797669,590126975666036000,374329848469391649,387579055376275965056,564075086247176342978,569593972449507189968,13370770993512683999344,352124398953483476142128,17161648202608219331368176],
    [8456628911281184,18135661890546885,293308414014196965,303265619317557473,457979224827035160585,496205868416842698960,534271607518685991142,569570142425868116863169,352119960893844070860848,567202110751980553279760],
    [12533445063640128,11312234589731936,584662355661592591,330352807754575106,497285788677871800704,556217367998487860577,12222562485006866973808,14663406269482499475600,518132807634742581520,13539404531508109409422416],
    [18135661890677952,17457157006167392,269385070152849440,518453965704339873,521676159498943890752,556222151039462480161,12222417481711732427856,14659913130903210103952,352124398953483832657968,544266620703954633399504],
    [18310418609046543,6160026014331008,547580300687946881,514653219428211842,129503654131864339520,14658794583463940953232,15878587789338966366384,17096686620341323437296,518132816184981331152,268552822023260571436224],
    [11312237516401760,18197070259399938,584662295520673967,401082260332512320,15912963203608696066432,17798915103818100419969,11892723386007771284592,7542717848343228287280,14659918539668466075792,518132807760566589712],
    [12533445063640128,11506951227063392,584662355650229711,17670442761423302665,2814085980117905455,10958841401072397570,14320329756526151824,391122006037826336064624,13539404531508109409094157,530567995017976406547728],
    [6159516025790848,13877461420940324,450510604591249761,18749868655633730592,17522569683418910977,15386909265155560576,420142444451904784496,11011854159115316199504,16259673896283106895337648,18150467544063377704952048],
    [3952997920048192,17111881175118977,197120800344780928,18749868655633533984,8615887813840733376,16480162020771076165,534271465380871675088,469117220188902723261584,567202110751980557440240,16259673896283106895337648],
    [8418311056557440,18135661890677952,369698911651629345,11871681453427360896,17381942217027266753,13130294509557651616,12220254591671872784432,14659913130903242642576,547093584233250622184656,18150897934213446403097840],
    [8418184323471392,18135661890677952,518453965704339873,16302379984341992768,17876236222752623968,17381942219989391521,14659913130903210103952,352124398953483832657968,391121999520219743161424,544266620703954633399504],
    [5038383564325984,18376558111032495,81186056673864896,6242353277570615808,2819828939734034633,276826424111813170624,496200988475878676656,553453071385013429511,15011751046044887147451536,17507007027171720240995536],
    [8461023611848864,18135661890546880,338235553025721472,9674099624606012448,9704142813108702433,556222150807423199425,496205879111081662640,17725065960999392290055,547093980550017830788304,11267980766511471239628848],
    [3952997920048192,17111881175118977,585933395490802720,6307865611031818368,16480162020771076165,275695108315606942912,534271465380871674032,469117220188902723261584,508114809258847090479312,567202110751980557440240],
    [16974552974665769,17290375677054209,376485430200305920,8620111138895500672,16335976943831976224,592725828064773319872,11003887263920025503792,12222568114506401186928,17722062436381560579312,17506994695464019909914832],
    [17183491020101664,16237801470330176,543259216540145953,18570918770567918784,17876128774521728007,530896860879963496865,11003887474727401392176,14401658713871276414096,391116449993147339376912,547093969599116257531120],
    [15168115271836736,18335942752615649,590152330060989696,17626321865075494338,17305541579946239184,10040006491813017860105,12222561596899808283728,13441099211656527941744,15878587779476685461680,460707954682466942755936],
    [18135627530808512,10569861032053792,270752755578177696,17381968779017627841,309571187987392398464,310532570027680402657,496205879111081662640,553908311281231009063,547093980550017830788304,11267980766511471239628848],
    [15168115267961920,18335942752615649,590126975665873184,17626321866149236162,313750202869156808128,450232142598064481376,553453071385008314608,12222561596899808283728,13441099211656527941744,16259673896283106895337648],
    [18135661890677952,17457157006167392,518453965704339873,8620322244894201888,521676159498943890752,556222151039462480161,458122285340725315728,12222417481711732427856,352124398953483832657968,544266620703954633399504],
    [15168115267961920,18335942752615649,590126975665873184,17626321866149236162,313750202869156808128,553453071385008314608,14394817740817878656096,12222561596899808283728,13441099211656527941744,508114809258847090479312] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_9 :
    let keys : List (List ℕ) := [
    [11,11,12,13,14,15,15,15,15,15],
    [11,11,12,14,14,14,14,14,15,17],
    [11,11,12,14,14,14,14,14,16,16],
    [11,11,12,14,14,14,14,15,15,16],
    [11,11,12,14,14,14,15,15,15,15],
    [11,11,12,17,17,17,17,17,17],
    [11,11,13,13,13,13,13,15,17,17],
    [11,11,13,13,13,13,13,16,16,17],
    [11,11,13,13,13,13,14,14,17,17],
    [11,11,13,13,13,13,14,15,16,17],
    [11,11,13,13,13,13,14,16,16,16],
    [11,11,13,13,13,13,15,15,15,17],
    [11,11,13,13,13,13,15,15,16,16],
    [11,11,13,13,13,14,14,14,16,17],
    [11,11,13,13,13,14,14,15,15,17],
    [11,11,13,13,13,14,14,15,16,16],
    [11,11,13,13,13,14,15,15,15,16],
    [11,11,13,13,13,15,15,15,15,15],
    [11,11,13,13,14,14,14,14,15,17],
    [11,11,13,13,14,14,14,14,16,16],
    [11,11,13,13,14,14,14,15,15,16],
    [11,11,13,13,14,14,15,15,15,15],
    [11,11,13,14,14,14,14,14,14,17],
    [11,11,13,14,14,14,14,14,15,16] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [18270696735021071,11312237516401760,232233589017807952,10958847940025888002,491485157987510915456,13142670359936374178880,17798925062126178577793,11892723386007776399395,14659918539668466075792,518132807760566589712],
    [15168115267973184,17152736915240129,580340155018292416,603307240133635546497,450230981513743344736,346179580363030957136,529202274771005479088,559182741884397459728,8577031511994003690528,15011792371075067899122832],
    [15168115271836736,17254717691499824,576782296546557153,313750202869156808128,604315985981964624166,564042299682415818817,420034349030515478640,496205868114925197488,460707954682466942755936,391121964617322631040080],
    [17244927308143872,9446289136992675,402408491359410464,421037275332845023246,596319811651443852608,528228871831505209761,381956176101362404432,11003887475862297183748,16693618886922351285456,430119786747997958770800],
    [15168115271836736,18335942752615649,590126975665873184,313750202869156808128,564042299675028917698,553764196093158139088,14397123583827092350048,12222561596899808283728,13441099211656527941744,15878587779476685461680],
    [16332391878822272,17459426763310496,521751635288198529,10020057339812499188843536,11267980766511471239628848,12515904193210442754067536,13763827619908865049563248,15011751046044887147451536,16259673896283106895337648],
    [1247097855869104,5038383564144736,8365767400596323680,18924489823215454223,2819828596136646703,18784774980533456130,15505904556246798533,17096674507289081943280,15011751046044887147451536,530567995006082701827280],
    [3952997920048192,17111881175118977,18749868655633533984,6307865611031818368,8615887813840733376,16480162020771076165,16695983293152239824,469117220188902723261584,567202110751980557440240,16259673896283106895337648],
    [11765328840427776,10673423401491560,8664088178870785056,18570911074094290272,13192640144398689286,17309634727531320615,556222150944895707329,378562880838615173168,12519303950164117372897801,17507007027171720240995536],
    [17183491020101637,16237801470330176,17876128774521728007,17375462823837374753,16590526902498859265,11935926818474855824,594269400658173401120,11003887474727401392176,547093969599116257531120,14747298523004593054585346],
    [3952997920048192,17111881175118977,18749868655633533984,6307865611031818368,8615887813840733376,16480162020771076165,534271465380871674032,469117220188902723261584,508114809258847090479312,567202110751980557440240],
    [16976815252180999,18335745996692865,18749868655641723055,15532150070938151970,17522566323310179457,556244147038757104,14407416565267181112352,13554116122016055696496,15878431631467594520752,15011751046044887147451536],
    [17183491020101664,16237801470330176,18570918770567918784,17876128774521728007,17375462823837374753,16590526902502105505,12222389062285854355536,14401658713871276414096,352124399191276844484656,547093969599116257531120],
    [5924490179547151,11828551708976236,18570882581173475360,15538798000304328000,15506422693786425520,562852461069674262539,556222709736482813254,561978761512602477840,469112787212871988778128,11267980766511471239628848],
    [12600515000534464,9511190496746528,18640554007020700864,10893623111578683616,14236376576390636045,553777651647754149025,564982708643579502832,11003887537664778403905,12222562688714854665296,17502750826342577330197712],
    [17183491020101637,16237801470330176,17876128774521728007,17375462823837374753,11935926818474855824,594269400658173401120,530896860879963496865,11003887474727401392176,460853078843880845251074,547093969599116257531120],
    [17183491020101664,16237801470330176,18570918770567918784,17876128774521728007,17375462823837374753,530896860879963496865,11003887474727401392176,12222389062285854355536,14401658713871276414096,547093969599116257531120],
    [17184649554991107,16093908281343200,12877132982848357760,18640554141627680064,16590524571582742947,16830678369280659425697,11003892884623463619632,13332680890648126066186,14663233188994348061840,17096674199191586774224],
    [5924490179547151,11828551708976236,18570882581173475360,15538798000304328000,562852460964544381290,556222709736482813254,496205526201168697520,561978761512602477840,14659953134468082013328,11267980766511471239628848],
    [16237801470330176,17071169006054407,17595894804584104112,16590526902498859265,594269260915198506176,556222151039462480161,343871483585231293488,533816214790419518704,391116450002214113578384,460853078844052643942914],
    [17183491020101637,16237801470330176,17876128774521728007,17375462823837374753,594269400658173401120,530896860879963496865,381949658191195385936,11003887474727401392176,14401658713871276414096,547093969599116257531120],
    [18270696735021071,11312237516401760,10958847940025888002,7431474848576179280,491485157987510915456,16191650242512591120,13142670359936374178880,17798925062126178577793,11892723386007776399395,14659918539668466075792],
    [16237801462104367,17071169006054407,16154459221945226384,563068633746691331312,594269260915198506176,556222151039462480161,530896860887543552257,343871483585231293488,450051834512969668098,12515726400070851637611920],
    [9583486262543808,1586050196734444,16693799395501710726,601984172091979872544,565165916002515456013,562958186610732469698,453323796951318604898,420038685738614722672,11003886385078042956848,543085189399566681839024] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_10 :
    let keys : List (List ℕ) := [
    [11,11,13,14,14,14,14,15,15,15],
    [11,11,13,16,17,17,17,17,17],
    [11,11,14,14,14,14,14,14,14,16],
    [11,11,14,14,14,14,14,14,15,15],
    [11,11,14,15,17,17,17,17,17],
    [11,11,14,16,16,17,17,17,17],
    [11,11,15,15,16,17,17,17,17],
    [11,11,15,16,16,16,17,17,17],
    [11,11,16,16,16,16,16,17,17],
    [11,12,12,12,12,12,12,12,12,12,17],
    [11,12,12,12,12,12,12,12,12,13,16],
    [11,12,12,12,12,12,12,12,12,14,15],
    [11,12,12,12,12,12,12,12,13,13,15],
    [11,12,12,12,12,12,12,12,13,14,14],
    [11,12,12,12,12,12,12,13,13,13,14],
    [11,12,12,12,12,12,13,13,13,13,13],
    [11,12,12,12,12,12,14,17,17,17],
    [11,12,12,12,12,12,15,16,17,17],
    [11,12,12,12,12,12,16,16,16,17],
    [11,12,12,12,12,13,13,17,17,17],
    [11,12,12,12,12,13,14,16,17,17],
    [11,12,12,12,12,13,15,15,17,17],
    [11,12,12,12,12,13,15,16,16,17],
    [11,12,12,12,12,13,16,16,16,16] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [15168115271836736,18335942752615649,17626321865075494338,604313374609027597568,381955049903119008880,420034350364266500176,553764196093158139088,10040006491813017860105,14397123583827092350048,15878587779476685461680],
    [12892202595485984,10673514701098241,12047530879182113024,465643604147944127795312,10020057339812499188843536,11267980766511471239628848,12515904193210442754067536,17507007027171720240995536,18150467544063377704952048],
    [18372018271501353,6170770978934790,423343118486134489409,497069301582536224769,530536643354893497455,18957943568104230027,378562677164417826860,384256662874108595723,553907934184147726576,469223462047814711874704],
    [15168115271836736,18335942752615649,604313374609027597568,563966999860645105090,450152250843320460384,371647604481253835888,420034350364266500176,553764196093158267406,10040006491813017860105,15878587779476685461680],
    [11827975131696256,11662741275674913,416653237624391271584,14659913130903210136720,10020057339812499188843536,11267980766511471239628848,13763827619908865180697712,17507007027171720240995536,18150467544063377704952048],
    [12892202595485984,10673514701098241,385518663078042077440,391228248442628667903056,465643604147944127795312,10020057339812499188843536,11267980766511471239628848,17507007027171720240995536,18150467544063377704952048],
    [10598680136615040,9447362914654368,9937152413914416810209,17725065961266950021360,349869458116851505563696,10060086774452448915850256,13691774637556955540951152,16259673896283106991902896,17507007027164224580462800],
    [11827975131696256,11662741275674913,13332891476569228510368,313126791869140600062992,469117220188902723261584,544266620703954633399504,11267980766511471239628848,13763827619908865180697712,18150467544063377704952048],
    [9435018874104096,18169822989820105,577579314896645948607938,387648389979808667338240,508114808950749595310256,547093969599116257434832,567202110751980553281776,12515909749254563405332560,13763827619908865049563248],
    [16151073334238370,190811597702180077,486569361293131072,542910438216867885,124413290619371778,193947811485658592,15904518751924451,109745772410830992,447140049718611233,544282798802934988,13763827619908865049595984],
    [16904351439655240,197120490172887168,413354184413619264,378761351694531680,304417843196429504,340422547250219232,547580301592867969,342464008725831745,296650818754644129,18749870982509431840,547093969599116093859024],
    [17289037872215169,303124584471823365,197120800347000839,403607740831798336,370474307792813152,551837298995536384,517248082837479625,342463998127746306,366251176170488225,534284589151665922054,13185185568500984385648],
    [16119022446022049,122174617389664736,373850690174391488,375468252001837121,83496031509292544,519123565237445643,545149246963586499,504842210265701584,9666248943706816544,9702141403462765648,13549642757107188374541],
    [17289037872215169,197120800347000839,403607740831798336,370474307792813152,551837298995536384,517248082837479625,342463998127746306,366251176170488225,9699986703099462661,412037049015655762032,534284589151665922054],
    [10566761411871872,122911353605719520,302315269863312544,519585458966267200,552201309453921282,545399935709091267,303270017099106529,18783747003730002957,14385980696030164014,433861038375703760,420142437037521275024],
    [16901739392537830,586710618877657519,378741329559454912,375175851936942369,545399935714100675,1656280193376496,15180764978345969667,10823786156190182528,9663953331313380512,9704499809783716961,17598173208966634507],
    [18135661890677952,269381898351052160,519609648222078272,582413653483291663,543185694374668481,518453965707544993,534271420568457975024,11267980766511471239628848,12515904193210442754067536,15011751046044887147451536],
    [16974373498066305,584633573741505568,485773241790763392,413353811899614272,361991600481909856,342463998127746306,13441099220686860357744,567202110751980553279760,12515904193210442754067536,15011751046044887278586000],
    [3840979907951680,585790458912245792,548888406660257801,515005065002983648,545399935709091267,513631707634993569,426645997064151007006218,469117219880805228188816,508109812206963027744944,17507007027171720240995536],
    [17111884396344449,585799156017269792,341304154988254272,289932736987346080,552025349177127107,6307865611301425155,13126207829820082288,16259673896283106895337648,17507007027171720240995536,18150467544063377704952048],
    [18269636715949088,413353811899614272,361991369426091104,543179951938311553,342463998127746306,15544743737304584576,420034350639144407152,391122006275619184217168,15011751046044887278586000,18398857950067760880195856],
    [3952997920048192,197120800344780928,269246494179591360,547580302606840961,515005063149096005,18749868655633533984,17096686892187893538000,17725065960999392420080,15011751046044887147451536,16259673896283106895337648],
    [18135661890677952,269381898351088672,521766890035774784,543185694374668481,518453965704339873,17876236222752623968,14659913130903210103952,391121999520219743161424,544266620703954633399504,11267980766511471239628848],
    [18135661890677952,269382871129592864,521766890035774784,543185694374668481,518453965704339873,17876236222752623968,349869458116851505563696,391121999520219743161424,469117220188902723359888,544266620703954633399504] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_11 :
    let keys : List (List ℕ) := [
    [11,12,12,12,12,14,14,15,17,17],
    [11,12,12,12,12,14,14,16,16,17],
    [11,12,12,12,12,14,15,15,16,17],
    [11,12,12,12,12,14,15,16,16,16],
    [11,12,12,12,12,15,15,15,15,17],
    [11,12,12,12,12,15,15,15,16,16],
    [11,12,12,12,13,13,13,16,17,17],
    [11,12,12,12,13,13,14,15,17,17],
    [11,12,12,12,13,13,14,16,16,17],
    [11,12,12,12,13,13,15,15,16,17],
    [11,12,12,12,13,13,15,16,16,16],
    [11,12,12,12,13,14,14,14,17,17],
    [11,12,12,12,13,14,14,15,16,17],
    [11,12,12,12,13,14,14,16,16,16],
    [11,12,12,12,13,14,15,15,15,17],
    [11,12,12,12,13,14,15,15,16,16],
    [11,12,12,12,13,15,15,15,15,16],
    [11,12,12,12,14,14,14,14,16,17],
    [11,12,12,12,14,14,14,15,15,17],
    [11,12,12,12,14,14,14,15,16,16],
    [11,12,12,12,14,14,15,15,15,16],
    [11,12,12,12,14,15,15,15,15,15],
    [11,12,12,13,13,13,13,15,17,17],
    [11,12,12,13,13,13,13,16,16,17] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [5038383564325984,578997816574487744,195073539924081728,88119643629594825,588049859553039843,277250812789227853248,553453071385013429511,15878587789331487922352,15011751046044887147451536,17507007027171720240995536],
    [15173745058882944,306671871684844576,581154960783221024,269527995958592704,444072001942012257,564042299716775559618,343975235700409763888,387654191778347442277456,508220492671405285054640,18150467544063377704952048],
    [9582661628664864,158095695502424352,513459921782940832,550822627028405698,442699020460439907,560832320829297562112,14551356111484085145712,17096686549965063068880,352230641358286328170544,16259673896283106895337648],
    [6061691735475328,413421258751947808,582385072723166528,485411575785948544,378801586955363426,530890347550551064995,17725053918316091185392,352124398953483832658433,430119613122152036896880,469223462047814711874704],
    [3676053157971072,585801454028522850,582564562329502729,545399935709091266,406956791804600480,12252499310575362246945,14589429296519573706896,16838432123312402504912,17725125986905245287664,13691667423449363199889520],
    [17213141394296258,306645172117275968,158095695502424352,513459921782940832,442699020460439907,17946634266537521987597,14551356111484085145712,17082118873059181272272,352230641358286328170544,508114808950749595310256],
    [15168115267961920,269385070152848416,580341180501694944,586751568479722881,17381942184521118913,14069742501928019040,13015868504002301008,572603127698450266923248,15011751046044887147451536,16259673896283106895337648],
    [18135661879143616,269486352125465984,378495203140535424,369830021101069356,17381942217027266753,13130294509557651616,458122285340726236304,17096674507288918269136,12513399801948026611762697,18150897934213446403097840],
    [16237831535101248,549871712646273056,580341180501701824,518453965704339873,17876128774521728007,17375462823837374753,450051834808477386896,352124399191276844484656,391117359414775437701200,17507007027171720240995536],
    [18135661890677952,269385959242630528,370990045380838528,369698911651629345,17381942217027266753,13130294509557651616,14659913130903242642576,17096674507288918269136,391043743810875831617584,18150897934213446403097840],
    [18135661890677952,521766890035774784,543185694374668481,518453965704339873,8620251876147008544,17876236222752623968,14659913130903210103952,349869458116851505563696,391121999520219743161424,544266620703954633399504],
    [18161092524024096,269527995958592704,485560281303721344,444072001942012257,17626321866149236162,314031996605280861504,381882955956410721328,496309065012133107888,12404934136907118152878601,18150467544063377704952048],
    [18135661890546880,270752755578177696,338235553025721472,543185694139787457,9674099624606012448,310532570027680402657,496205879111081662640,17725065960999392290055,547093980550017830788304,11267980766511471239628848],
    [18135661890677952,549871712646273056,558629024197356551,518453965704339873,16302379984013657408,556222151039462480161,458122285340725315728,352124398953483832657968,391117359414775437701200,544266620703954633399504],
    [17244915593610496,411172380557225998,402408491374090528,302281386675834309,16620868135325642817,420039767423817158768,19082155130126571373888,12040298430685799025744,16693618886922351285456,11081341048307427435775492],
    [9407596710823232,158095695502424352,513459921782940832,442699020460439907,17626324243174559170,560832320829297562112,14551356111484085145712,17096686549965063068880,352230641358286328170544,508114808950749595310256],
    [6160026014331008,585933395489490959,547580300687946881,514653219428211842,4046989191620760608,14658794583463940953232,15878587789338966366384,17096686620341323437296,518132816184981331152,268552822023260571436224],
    [10569861032053792,270752755578177696,580341211580116160,543185694139787457,309571187987392398464,310532570027680402657,496205879111081662640,553908311281231009063,547093980550017830788304,11267980766511471239628848],
    [17111884490018209,197115262985842784,126360494596720644,269233504214582464,599995771558692228128,535294830675716315205,458122278442975204496,15878587789331651662032,17725056204240426610000,17507007027655739529500841],
    [18135661890677952,549871712646273056,558629024197356551,518453965704339873,521676159498943890752,556222151039462480161,458122285340725315728,12222417481711732427856,352124398953483832657968,544266620703954633399504],
    [8411753920070848,585933395490868256,126360494596720644,547580302606840961,496205868416614114448,553908311288684125552,6461062548063582957664,17129434581282323535941,17096686892187990104233,469117220188908999053520],
    [11312237516401760,584662295520673967,401082260332512320,342456243430075650,16191650242512591120,15912963203608696066432,17798915103818100419969,11892723386007771284592,7542717848343420505168,14659918539668466075792],
    [16237703766246720,584457652154107136,332499297038142914,9813495495868515337,17670441626443713888,16590539890721294753,13126208896550245444,18202373209900402835664,11267980766511471239628848,12515904193210442754067536],
    [8456456945833997,547580302606840961,293056476668627361,18750146961324737920,6307865716358254599,16480188709966448800,16585924041886506192,469081426684938840806544,546615472247382831470093,11271380587913368755505200] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_12 :
    let keys : List (List ℕ) := [
    [11,12,12,13,13,13,14,14,17,17],
    [11,12,12,13,13,13,14,15,16,17],
    [11,12,12,13,13,13,14,16,16,16],
    [11,12,12,13,13,13,15,15,15,17],
    [11,12,12,13,13,13,15,15,16,16],
    [11,12,12,13,13,14,14,14,16,17],
    [11,12,12,13,13,14,14,15,15,17],
    [11,12,12,13,13,14,14,15,16,16],
    [11,12,12,13,13,14,15,15,15,16],
    [11,12,12,13,13,15,15,15,15,15],
    [11,12,12,13,14,14,14,14,15,17],
    [11,12,12,13,14,14,14,14,16,16],
    [11,12,12,13,14,14,14,15,15,16],
    [11,12,12,13,14,14,15,15,15,15],
    [11,12,12,14,14,14,14,14,14,17],
    [11,12,12,14,14,14,14,14,15,16],
    [11,12,12,14,14,14,14,15,15,15],
    [11,12,12,16,17,17,17,17,17],
    [11,12,13,13,13,13,13,14,17,17],
    [11,12,13,13,13,13,13,15,16,17],
    [11,12,13,13,13,13,13,16,16,16],
    [11,12,13,13,13,13,14,14,16,17],
    [11,12,13,13,13,13,14,15,15,17],
    [11,12,13,13,13,13,14,15,16,16] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [16237703766246720,584457652154107136,332499297038142914,9813495495868515337,17670441626443713888,16590539890721294753,420038684689601598532,568824162809387588816,11267980766511471239628848,12515904193210442754067536],
    [16237831535101248,549871712646273056,518453965704339873,18570918770567918784,17876128774521728007,17375462823837374753,450051834808477386896,12222389062285854355536,352124399191276844484656,17507007027171720240995536],
    [18135661890677952,549871712646273056,518453965704339873,16302379984013657408,17876128774521728007,17375462823837374753,458122285340725315728,352124398953483832657968,391117359414775437701200,544266620703954633399504],
    [18335745996692865,543258087998754823,485379693031435298,18749868655641723055,17522566323310179457,556244147038757104,14407416565267181112352,13554116122016055696496,15878431631467594520752,15011751046044887147451536],
    [18135661890677952,549871712646273056,518453965704339873,16302379984013657408,17876128774521728007,17375462823837374753,11003887474727757809712,14403860805065146337424,391117359414775437701200,544266620703954633399504],
    [16237801470330176,549871712643252400,546277408400059399,17375462823837374753,16590526902498859265,594269400658173401120,343871483585231293488,381949658191195344272,547093969599116257531120,14747298523004593054585346],
    [16237801470330176,549871712643252400,546277408400059399,17375462823837374753,16590526902498859265,594269400658173401120,343871483585231293488,12222389062560732220816,17082118873293420500208,14747298523004593054585346],
    [17457157006167392,580341183662959808,518453965704339873,8620322244894201888,17381942219983100193,521676159498943890752,458122285340725315728,12222417481711732427856,352124398953483832657968,544266620703954633399504],
    [17111884490018209,126360494596720644,269233504214582464,18749867685373643808,6307866638630006880,535294830675716315205,14659913130903406220432,15878587789331651662032,17725056204240426610000,547093969599116190423209],
    [16093908281343200,402408305636705664,549904630282229763,18640546651204715840,16590524571582742947,16830678369280659425697,11003892884623463619632,13332680890648126066186,14663233188994348061840,17096674199191586774224],
    [12575265355440320,411172380557225998,551837298995535885,16408101614599123009,309536139639012101573,376259333678971259984,420039767733054804080,521660999396146681040,19082155130126571373888,11081333116280714823808048],
    [8411753920070848,585933395490868256,126360494596720644,17522569719702467713,201908205654585389152,535294830675716315205,496205868416614114448,553908311287573753168,469117220188908999053520,547093969599116190423209],
    [16237801470330176,549871712643253253,558629024197356551,16590526902498859265,556222151039462480161,343871483585231293488,523439921248957895920,19016616349286352198112,12222389376849259072912,460853078844052643942914],
    [18335942752615649,590126975665873184,485379688574788672,17626321866149236162,313750202869156808128,553453071385008314608,14394817740817878656096,12222561596899808283728,13441099211656527941744,15878587789331651596496],
    [16237801462104367,546277408199781383,504826850685752464,563068633746691331312,594269260915198506176,556222151039462480161,530896860887543552257,343871483585231293488,450051834512969668098,12515726400070851637611920],
    [12575265355440320,411172380557225998,551837298995535885,309536139639012101573,525059251666945159233,376259333678971259984,420039767733054804080,521660999396146681040,19082155130126571373888,346291907759607107367984],
    [15168115267642432,590126975665873184,586750168083701089,313750202869156808128,564042299675028917698,450232142598064481376,553764196093156169968,12222561596899808283728,13441099211656527941744,15878587779476685461680],
    [11662741275674913,378495204214277248,406887927372716192,469117220188902723261584,10020057339812499188843536,11267980766511471239628848,13763827619908865049563248,17507007027171720240995536,18150467544063377704952048],
    [14898777763888417,306671734246120480,11976741025206047936,8437885512715450626,13225323246612912256,17727692169332038864,17309631796525311239,595388374876888959264,11267980766511471239628848,12178148747518253640844400],
    [16237703766246720,332499297038142914,9813495495868515337,18702644868922443008,17670441626443713888,16590539890721294753,13126208896550245444,18202373209900402835664,391122006038124672617552,11267980766511471239628848],
    [18135661890546885,270612114727572512,14311850775844848768,9660795638944828576,17381901327601674433,9704499818457663713,16695987734953727206,352119960893844070860848,508114809258847090479312,567202110751980553279760],
    [16093908281328864,545399935709091267,18745294685117842560,3933163323130001472,16436207358611786145,13020196181932805442,563102284541585425600,534271454695194367216,469117220188902559683728,16259513990622816887848112],
    [16237801470330176,546277408400059399,17595894804584104112,18570918770567918784,17375462823837374753,16590526902498859265,343871483585231293488,12222389062560732220816,17082118873293420500208,14747298523004593054585346],
    [16237801470330176,546277408400059399,17595894804584104112,18570918770567918784,17375462823837374753,16590526902498859265,343871483585231293488,17082118873293420500208,391116450002214113578384,460853078844052643942914] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_13 :
    let keys : List (List ℕ) := [
    [11,12,13,13,13,13,15,15,15,16],
    [11,12,13,13,13,14,14,14,15,17],
    [11,12,13,13,13,14,14,14,16,16],
    [11,12,13,13,13,14,14,15,15,16],
    [11,12,13,13,13,14,15,15,15,15],
    [11,12,13,13,14,14,14,14,14,17],
    [11,12,13,13,14,14,14,14,15,16],
    [11,12,13,13,14,14,14,15,15,15],
    [11,12,13,14,14,14,14,14,14,16],
    [11,12,13,14,14,14,14,14,15,15],
    [11,12,13,15,17,17,17,17,17],
    [11,12,13,16,16,17,17,17,17],
    [11,12,14,14,14,14,14,14,14,15],
    [11,12,14,14,17,17,17,17,17],
    [11,12,14,15,16,17,17,17,17],
    [11,12,14,16,16,16,17,17,17],
    [11,12,15,15,15,17,17,17,17],
    [11,12,15,15,16,16,17,17,17],
    [11,12,15,16,16,16,16,17,17],
    [11,12,16,16,16,16,16,16,17],
    [11,13,13,13,13,13,13,13,17,17],
    [11,13,13,13,13,13,13,14,16,17],
    [11,13,13,13,13,13,13,15,15,17],
    [11,13,13,13,13,13,13,15,16,16] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [16332391878822272,558701656425935877,9812644785157119296,18596958745063065888,17626009439260020162,16446479917670272385,11003887467295316903984,14551362866883526201456,15878587779717203630256,391122006037826172390480],
    [12575265355440320,411172380557225998,17658793567857148334,16408101614599123009,11758104200926497872,309536139639012101573,420039767733054804080,521660999396146681040,19082155130126571373888,11081333116280714823808048],
    [17152762842350784,547580302606840961,18749868655633335680,16480188719195201696,16433957541164485025,201851702923460218887,496201330698872821936,534271078352783940816,352124398953473095239728,469081426670846110513296],
    [16237801470330176,549871712643253253,18570918770567918784,17876128774521728007,17375462823837374753,530896860879963496865,381949658191195385936,11003887474727401392176,14401658713871276414096,547093969599116257531120],
    [11312237516401760,584662295520673967,12834639023176975424,10958847940025888002,7431474848576179280,16191650242512591120,15912963203608696066432,17798925062126178577793,11892723386007771284592,14659918539668466075792],
    [5924490179547151,377746021432829036,18570882581173475360,17381959679256835398,599745949111963484522,497241456790922628416,458123535452127562928,496205526201168762000,561978761512864781608,11267980766511471239628848],
    [8383891188647104,485560281110490400,9813499897007095104,17626321866149236162,595127237467805328768,454729729988920295777,381882955956410721328,496205868108646420656,17725065960998351085808,387654191506419235260937],
    [11312237516401760,584662295520673967,10958847940025888002,7431474848576179280,491485157987510915456,410708448741734777920,16191650242512591120,17798925062126178577793,11892723386007771284592,14659918539668466075792],
    [16994474950598896,267340869770744864,17626321866149236162,314031996704226983232,595127237467805131040,563148221836924715201,446551193065615475041,381882955956477830192,482370810498967113904,387654227535048651915565],
    [8383891188647104,306671871781480457,18597726170869368064,497213390266529326464,564032302056315719106,454729729988920617985,378562880838615173168,496205869483035955376,12226056118282440772105,17725065960998351085808],
    [11662741275674913,378495204214277248,13020413675762227360,14659913130903210136720,10020057339812499188843536,11267980766511471239628848,13763827619908865049563248,17507007027171720240995536,18150467544063377704952048],
    [14050703223898432,472262413883050336,14356824912973499713,313126791869140956578832,391122006037826336064610,11267980766511471239628848,13763827619908865049563248,15011751046044887147451536,18150467544063377704952048],
    [18517019644144680,552020264563679616,422202476325414933730,378428931770352536640,333775469893249117442,347297870331960830032,454764497989384940656,447636814692873381989,1623977723067310576,17798919606073372781953],
    [12892202595485984,341546250312846593,385518663078042077440,452421985165526469712,10020057339812499188843536,11267980766511471239628848,14900595332734212089449995,17507007027171720240995536,18150467544063377704952048],
    [12892202595485984,341546250312846593,385518663078042077440,13438929813057050807376,465643604147944127795312,10020057339812499188843536,11267980766511471239628848,17507007027171720240995536,18150467544063377704952048],
    [11662741275674913,378495204214283392,416652858642785305760,313126791869140600062992,469117220188902723261584,544266620703954633399504,11267980766511471239628848,13763827619908865180697712,18150467544063377704952048],
    [10598680136615040,302315613268948128,9937152413914416810209,10933420557654373173296,17725065961266950021360,10060086774452448915850256,13691774637556955540951152,16259673896283106991902896,17507007027164224580462800],
    [14053414620369130,448648067265151296,15475094778119792406880,13332687408254718968930,427864672284986966085744,567202110751980553183472,10019803523455107016918032,11267980766511471239628848,15011751046044887147451536],
    [11662741275674913,378495204214287488,13332891476569228510368,313126791869140600062992,469117220188902723261584,544266620703954633399504,567202110751746313887984,11267980766511471239628848,13763827619908865180697712],
    [18169822989820105,301920603971333408,577579314896645948607938,387648389979808667338240,388872621245314496561232,508114808950749595310256,547093969599116257434832,567202110751980553281776,13763827619908865049563248],
    [16090358807494849,12877065781883962752,18640546651204715840,9598727176583283721,16585853870945864195,16436209345394744736,10854064551526272007,16696007458556124368,13879338822844217077868042,16257308162392053738738832],
    [3840979895846368,18752221806338354208,9739459057168909504,10893550543809153248,17769348232403726510,9588567557241243809,15506280898662471856,16191992214419938786,533011068357059340898512,13652671906052832224192592],
    [18380648874022370,8650825965021301184,2597958211610187904,15288854644167589376,7107036841916837984,15220349258567228592,17295408180101423334,2562098231948692756521,17096853559492455047376,15011751046044887147451536],
    [12962356525474848,17629487081656956268,12864993070030329870,16410563277079253409,10567982652536750160,12076733525730395655,14211393648236467693,16693164054113026315472,610636955842234697614656,460743572742484083084741] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_14 :
    let keys : List (List ℕ) := [
    [11,13,13,13,13,13,14,14,15,17],
    [11,13,13,13,13,13,14,14,16,16],
    [11,13,13,13,13,13,14,15,15,16],
    [11,13,13,13,13,13,15,15,15,15],
    [11,13,13,13,13,14,14,14,14,17],
    [11,13,13,13,13,14,14,14,15,16],
    [11,13,13,13,13,14,14,15,15,15],
    [11,13,13,13,14,14,14,14,14,16],
    [11,13,13,13,14,14,14,14,15,15],
    [11,13,13,14,14,14,14,14,14,15],
    [11,13,13,14,17,17,17,17,17],
    [11,13,13,15,16,17,17,17,17],
    [11,13,13,16,16,16,17,17,17],
    [11,13,14,14,14,14,14,14,14,14],
    [11,13,14,14,16,17,17,17,17],
    [11,13,14,15,15,17,17,17,17],
    [11,13,14,15,16,16,17,17,17],
    [11,13,14,16,16,16,16,17,17],
    [11,13,15,15,15,16,17,17,17],
    [11,13,15,15,16,16,16,17,17],
    [11,13,15,16,16,16,16,16,17],
    [11,13,16,16,16,16,16,16,16],
    [11,14,14,14,15,17,17,17,17],
    [11,14,14,14,16,16,17,17,17] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [7152843907697922,13258956948993647660,18635161003779983850,10741264555248452014,12877071718341154830,16301906239493937584,442805393479022609576,525058970192195137605,13554121547908402712685,11081332977856895196935216],
    [12847123606542350,13258955987591078956,18635161003779983850,10741264540216066478,13847524568450840613,7324452955456905296,525058970192195137605,521660999663809108400,346291655558027974620208,433731889533068886805925],
    [8383891188647104,9813499897007089673,18597726170869368064,15537928995535693184,17626321866149236162,15506433414024892592,381882955956410721328,14551351359645449464833,17725065960998351085808,387654191506419235260937],
    [12575544219801888,13157414857178394638,17658803739380916237,6278557957904023971,16507152244734537793,10745983864104105008,19082233661645073646912,12222597625696827247696,13441243573135208419440,16693151980676693890256],
    [5924490179547151,18570882581173475360,15538795526403165504,17381959679256835398,12088160583758783596,599745949111963484522,458123535452127562928,496205526201168762000,561978761512864781608,11267980766511471239628848],
    [8383891188647104,9813499897007095104,18597726170868916512,15537928995535693184,17626321866149236162,454729729988920295777,381882955956410721328,496205868108646420656,17725065960998351085808,387654191506419235260937],
    [18274103539828740,8613636013752321216,17522569514617779201,16727963732326586437,17799506740329487728,457758754910751493296,517064292292115044521,19199864689878151300480,6461062548063582957664,15878587789331651662032],
    [17463654925506569,18749868655633335680,17522569684268987521,16433957541294508449,201851702923460218887,527366039014238298272,458082519036125615568,496205834298500192432,534271078352783907332,352124398953473095239728],
    [18274103539828740,17522569514617779201,16727963732326586437,17799506740329487728,275636352440262460608,457758754910751493296,496205868416614109392,517064292292115044521,19199864689878151300480,6461062548063582957664],
    [18310418609016192,17564429013128249801,10857204947796598944,201851702923460218887,560722229896607600682,525886641308672854433,458082519036125615568,496205526201168697520,534271078352783907332,11003887467296034129968],
    [13985931898370401,14354635682174174464,15386915920233632032,460412350360230006960,10020057339812499188843536,11267980766511471239628848,12515904193210442754067536,13763827619908865049563248,18150467544063377704952048],
    [14050703223898432,15112397244257610080,14356824912973499713,13332687408254718968930,313126791869140956578832,11267980766511471239628848,13763827619908865049563248,15011751046044887147451536,18150467544063377704952048],
    [9574722478245184,18884063221307935008,17626321866140847554,352124398953483476238384,508114808977378392545456,547107419291305904348368,12515904193210442754067536,13763827619908865049563248,18150467544063377704952048],
    [8461100741985472,11791778603273127040,595388761934785487904,496954431302809225600,562961435797754383810,454729737614603332833,346107444971162306608,382058836402541533264,496309072976076216492,553908311118834706601],
    [11827975131696160,13020400658823649440,378571685529803819297,343975269819629963312,460923545762084878914704,10020057339822062617792528,13763827619908865049563248,17507007027171720240995536,18150897934213446403097840],
    [12892202595487008,10929480010011053313,385518663078042077440,14477503525296847038544,17096686549971341843664,10020057339812499188843536,11267980766511471239628848,14900595332734212089449995,18150467544063377704952048],
    [12892062103080224,12047530879182113024,349743360320353996033,17725065959933199196400,468969501980249917833577,465643604147944127795312,10019915321904038233310224,11267980766511471239628848,17507007027198309440923856],
    [3772843461981248,18990978188731290048,558419797849126647840,313126791869140599651376,391121999520219743161424,508114809258847090479301,547093969599122536307920,13763827619908865049563248,15011751046044887147451536],
    [15168112117727522,10537313176870198657,14389809355496081499232,12222562688682073002082,15878587789331651596496,466862278806379889267856,10020057339812499188843536,13803857054548814907704432,18664452632953660858734832],
    [15168112117720128,18776035098936745345,14389811954647684260960,15878587789331651596496,431370532954650465865840,466862278806379889267856,583264227788297606568176,10020057339812499188843536,12515904193210442754067536],
    [9447359632323744,10679422684646966400,9854464238017311148257,314377705184032956318736,355743346407059263326256,431369553658991780892784,508114809258847090479280,567202110760542400618736,17507007027164224580462800],
    [18124808511332553,9661459327082769696,577579314896645948607938,387648389979808667338240,388872621245314496561232,430119613122152032798864,508114808950749595310256,547093969599116257434832,567202110751980553281776],
    [12892062103080224,385518663078042077440,349743360320353996033,457978029277587810384,17725065959933199196400,10019915321904038233310224,11267980766511471239628848,14900595332734212089449995,17507007027198309440923856],
    [17459325736954925,527468606819863500128,523967255025213050241,530355188779951797424,313126792106933968405520,469117220188902723261584,12404748470652707304408589,12515904193219989523765328,13879414888755040917459056] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_15 :
    let keys : List (List ℕ) := [
    [11,14,14,15,15,16,17,17,17],
    [11,14,14,15,16,16,16,17,17],
    [11,14,14,16,16,16,16,16,17],
    [11,14,15,15,15,15,17,17,17],
    [11,14,15,15,15,16,16,17,17],
    [11,14,15,15,16,16,16,16,17],
    [11,14,15,16,16,16,16,16,16],
    [11,15,15,15,15,15,16,17,17],
    [11,15,15,15,15,16,16,16,17],
    [11,15,15,15,16,16,16,16,16],
    [12,12,12,12,12,12,12,12,12,12,16],
    [12,12,12,12,12,12,12,12,12,13,15],
    [12,12,12,12,12,12,12,12,12,14,14],
    [12,12,12,12,12,12,12,12,13,13,14],
    [12,12,12,12,12,12,12,13,13,13,13],
    [12,12,12,12,12,12,13,17,17,17],
    [12,12,12,12,12,12,14,16,17,17],
    [12,12,12,12,12,12,15,15,17,17],
    [12,12,12,12,12,12,15,16,16,17],
    [12,12,12,12,12,12,16,16,16,16],
    [12,12,12,12,12,13,13,16,17,17],
    [12,12,12,12,12,13,14,15,17,17],
    [12,12,12,12,12,13,14,16,16,17],
    [12,12,12,12,12,13,15,15,16,17] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [12892202595487008,385518663078042077440,349743360320353996033,14477503525296847038544,17096686549971341843664,567202110443883058110704,10020057339812499188843536,11267980766511471239628848,14900595332734212089449995],
    [12892202595487008,385518663078042077440,349743360320353996033,14477503525296847038544,313122353809501194781712,547093969599082939001040,567202110443883058110704,11267980766511471239628848,14900595332734212089449995],
    [3772843461981248,558419797849126647840,607711306032578105792,313126791869140599651376,391121999520219743161424,430119613122152032702576,508114809258847090479301,547093969599122536307920,15011751046044887147451536],
    [18169822989819910,314031855867792490798,18049353589696609291714,13441237706381680775280,17097106852853309414416,17725065960999424827632,11267980766511471239628848,12515904193210442754067536,16259673896283106895337648],
    [9447359632323744,341741519487465784448,9854464238017311148257,11116986195172163323952,17725065961266950021360,314377705184032956318736,431369553658991780892784,16259673896283106991902896,17507007027164224580462800],
    [9447359632323744,341741519487465784448,9854464238017311148257,11116986195172163323952,314377705184032956318736,431369553658991780892784,508114809258847090479280,567202110760542400618736,17507007027164224580462800],
    [15168115267962146,598664781974862207361,12222568114495500094544,461850177107611064116320,348650782895133615497232,465501586222424082494576,463288048746017349341707,432556873475104489740813,583264144779801898817808],
    [14079731929791841,14699146938722286608896,13072346664808122295309,9785212042235453979680,11003887263610787858480,14404997948580044182029,391122006038124672617552,13763827619908865049563248,18150467544063377704952048],
    [9440556404126880,9937150327175833454817,12146250280375662642192,11151461419587161109552,15878587789331651596464,355632665896579294659712,546627803937893795473616,582047856160596198367472,13839388762255308098703472],
    [15168115267962146,19151477634108243745153,12222568114495500094544,13517402296097019402765,461850177107611064116320,348650782895133615497232,465501586222424082494576,463288048746017349341707,583264144779801898817808],
    [190811597702180077,486569361293131072,542910438216867885,124413290619371778,516834346695892130,193947811485658592,15904518751924451,109745772410830992,447140049718611233,544282798802934988,430119613113121700417616],
    [590263031437532192,114110941732479040,338245216838452352,306606663742370976,504868775783375914,558632390444035533,545399935709091267,303254462909235265,518452007203441057,16681756712201622736,13441237909785053137040],
    [293199419709721632,197120800353169632,329270000222245952,54578733294660612,374365343040505024,552025349177127107,413632125507911846,521749467434849520,15812184434317584,385521082792668308514,560476540759205557505],
    [298902446644704270,114072523504097760,225613752738874496,256791262065333760,188324839491406176,555396801926203553,435170397776881703,449629096812918928,17452791446341230019,17374888948760947911,459421466150816555328],
    [303124844251224080,341304019600315456,374342481103428640,375352774347464738,547587832611770657,552025244723851459,413460431345195136,6323418139853921376,18889481197944217700,17775083620356234754,505990136137554191],
    [584633573741505568,485773250316833152,120730990783398976,545234932729034176,87935886480814127,593468081050030529,16590522508755705029,12515904193210442754067536,13763827619908865049563248,15011751046044887147451536],
    [585799320469571008,580341180501694479,341304154988254272,289931740546765920,543185390505732289,548314804186686664,565273960549830439107,547093969599116257434832,12515904193210442754067536,16259673896283106895337648],
    [402162027755275584,582517319161840896,126495933441549376,255735695297479872,518454034497290659,195956418609953922,12226056390210647788624,17725486263880322851056,14825111328112389933601936,17507007027171720240995536],
    [402162027916789056,582517319161840896,126495933441549376,255735695297479872,518454034497290659,195956418673753218,17725486263880322851056,391122006037826336064592,469117220188668483966096,17507007027171720240995536],
    [585790458912245792,122911357054464064,549703419654346761,515005065189670112,545399935709091267,513631707362462113,426645997063802172064066,469117219880805228188816,508109812206957790182576,547093969607678111161552],
    [306671871684844576,581154960783221024,269527995958592704,485560281303721344,444072001942012257,17626321866149236162,11933842373637834800,508220492671405285054640,12404934136907118152878601,18150467544063377704952048],
    [402162027916789056,582517319161840896,126495933441549376,255735695297479872,518454034497290659,6270605395518143618,382064262194082743376,17725486263880322851056,14825111328112389933601936,17507007027171720240995536],
    [306671871684844576,581154960783221024,269527995958592704,485560281303721344,444072001942012257,17626321866149236162,343975235700409763888,387654191778347442277456,508220492671405285054640,18150467544063377704952048],
    [584633605176100896,122911357054464064,550014306567100425,545399935709091267,513631473320298913,16480155793055300832,15878431631467430942896,17096686550246219750608,469117219880805228188816,13652671906052832224198978] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_16 :
    let keys : List (List ℕ) := [
    [12,12,12,12,12,13,15,16,16,16],
    [12,12,12,12,12,14,14,14,17,17],
    [12,12,12,12,12,14,14,15,16,17],
    [12,12,12,12,12,14,14,16,16,16],
    [12,12,12,12,12,14,15,15,15,17],
    [12,12,12,12,12,14,15,15,16,16],
    [12,12,12,12,12,15,15,15,15,16],
    [12,12,12,12,13,13,13,15,17,17],
    [12,12,12,12,13,13,13,16,16,17],
    [12,12,12,12,13,13,14,14,17,17],
    [12,12,12,12,13,13,14,15,16,17],
    [12,12,12,12,13,13,14,16,16,16],
    [12,12,12,12,13,13,15,15,15,17],
    [12,12,12,12,13,13,15,15,16,16],
    [12,12,12,12,13,14,14,14,16,17],
    [12,12,12,12,13,14,14,15,15,17],
    [12,12,12,12,13,14,14,15,16,16],
    [12,12,12,12,13,14,15,15,15,16],
    [12,12,12,12,13,15,15,15,15,15],
    [12,12,12,12,14,14,14,14,15,17],
    [12,12,12,12,14,14,14,14,16,16],
    [12,12,12,12,14,14,14,15,15,16],
    [12,12,12,12,14,14,15,15,15,15],
    [12,12,12,13,13,13,13,14,17,17] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [584633605176100896,122911357054464064,550014306567100425,545399935709091267,513631473320298913,16480155793055300832,15878431631467430942896,426645997064151007006218,469117219880805228188816,547093969599122536307920],
    [584634743005413679,122903801074549824,376452181750095040,152537803093444897,555292134416455107,423493088422173740256,458231137823828912272,16188648872356387088,12367043407606683324693584,17204909696528462981020880],
    [413421258751947808,582385072723166528,193974135535210502,485411575785948544,378801586955363426,530890347550551064995,454730082175725670512,17725053918316091185392,352124398953483832658433,15015150785530070779990539],
    [582527075864317248,437323366029034752,518454034497094051,399078954270598176,373104332401442945,411635909887391114253,461321903452963682657,352124398953483476240432,426648310586968896508016,567202110751980389605616],
    [585826544899949583,122907067236269120,374300666137779392,473141168821242145,555292134416455107,423493088422173740256,12222562696113099506768,16801538644793030350032,518036754287161450736,15011756584620508222498960],
    [306645172117275968,158095695502424352,513459921782940832,550822627028405698,442699020460439907,533816214783099411664,17946634266537521987597,14551356111484085145712,352230641358286328170544,508114808950749595310256],
    [306609027723369504,579993876504289568,486651821539231040,558635785615685677,517930564852064333,18049353590795060478402,11003748777932627478576,14551362625225207482512,17095568486318232214736,430045754017825625843792],
    [581154960783221024,269527995958592704,485560281303721344,444072001942012257,9813499893915026752,17626321866149236162,11933842373637834800,15881890087883919988912,12404934136907118152878601,18150467544063377704952048],
    [117556870525748288,378495204214277248,374202511278999841,545404333421998531,18746457901853873167,13020098287723747360,13161145911304425584,468929432690342187141264,16582555686949298053360,17507007027171720240995536],
    [581154960783221024,269527995958592704,485560281303721344,444072001942012257,9813499893915026752,17626321866149236162,381882955956410721328,496309065012133107888,12404934136907118152878601,18150467544063377704952048],
    [584457652154107136,512759562683843904,552201306131139936,332499297038142914,9813495495868515337,16590539890721294753,568824162809387588816,13441237910067251024964,391122006275619184217168,11267980766511471239628848],
    [549871712646273056,580341180501701824,521766889707439424,518453965704339873,17876128774521728007,17375462823837374753,450051834808477386896,352124399191276844484656,391117359414775437701200,544266620703954633399504],
    [585801454028534816,117556870499056704,374202511278999841,545399935709091267,12111846534856871945,13020400286235238560,13370771246166114898032,14659912602272258103440,17725100898014680319216,17245381853026181733063888],
    [299821982963276832,270755228102591680,485307393629330816,550822558308906094,18605898810462046496,14210303893507883361,12222562688714854665296,17725065960999392289992,349875014153615820458032,507745874377373940651408],
    [270752755578177696,580341211580116160,338235553025721472,543185694139787457,9674099624606012448,310532570027680402657,496205879111081662640,553908311281231009063,547093980550017830788304,11267980766511471239628848],
    [411172380557225998,551837298995535885,402408491374090528,302281386675834309,16620868135325642817,420039767423817158768,521660999396146681040,19082155130126571373888,12040298430685799025744,11081341048307427435775492],
    [549871712646273056,580341183662959808,558629024197356551,518453965704339873,17381942219983100193,521676159498943890752,458122285340725315728,12222417481711732427856,352124398953483832657968,544266620703954633399504],
    [299821982963276832,270755228102591680,485307393629330816,550822558308906094,18605898810462046496,454729724592025452897,10933594192530631559216,12222562688714854665296,17725065960999392289992,507745874377373940651408],
    [585511183026598016,548888750257641481,339013668300103918,484182117336619184,10495932754810077264,6067899185744091226496,18120910062578821074986,16828372521867867665455,14658640613554078726657,16988493152545735416324],
    [267340869762450624,549935279434474881,482425035412312240,540891974376562928,314031996704226983232,595127237467805131040,564042299716775559618,381882955956410721328,14289638178099695201312,12404935281126920135196973],
    [585933395490868256,126360494596720644,269233504214582464,547580302606840961,201851699553010724960,527364914943727081541,496205868416614114448,553908311288684125552,469117220188908999053520,547093980550015683335472],
    [582517321309324608,514723315517463553,518453892861960707,513631706552863136,412068255451147928960,563102524236129933315,534272238673828517072,13332680890648126065744,14663233188994348192912,355736646131609687296225],
    [126360494596720644,269176125430170816,547580303680582657,521761227898362025,201908205654585389152,535294830675716315205,19199864689878151300480,14648280157143952329904,15878587789331651662032,17725056204240426610000],
    [306671734246120480,375186747953528097,263683963758950658,11976741025206047936,13225323246612912256,17727692169332038864,17309634727799596295,595388374876888959264,11267980766511471239628848,12178148747518253640844400] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_17 :
    let keys : List (List ℕ) := [
    [12,12,12,13,13,13,13,15,16,17],
    [12,12,12,13,13,13,13,16,16,16],
    [12,12,12,13,13,13,14,14,16,17],
    [12,12,12,13,13,13,14,15,15,17],
    [12,12,12,13,13,13,14,15,16,16],
    [12,12,12,13,13,13,15,15,15,16],
    [12,12,12,13,13,14,14,14,15,17],
    [12,12,12,13,13,14,14,14,16,16],
    [12,12,12,13,13,14,14,15,15,16],
    [12,12,12,13,13,14,15,15,15,15],
    [12,12,12,13,14,14,14,14,14,17],
    [12,12,12,13,14,14,14,14,15,16],
    [12,12,12,13,14,14,14,15,15,15],
    [12,12,12,14,14,14,14,14,14,16],
    [12,12,12,14,14,14,14,14,15,15],
    [12,12,12,15,17,17,17,17,17],
    [12,12,12,16,16,17,17,17,17],
    [12,12,13,13,13,13,13,13,17,17],
    [12,12,13,13,13,13,13,14,16,17],
    [12,12,13,13,13,13,13,15,15,17],
    [12,12,13,13,13,13,13,15,16,16],
    [12,12,13,13,13,13,14,14,15,17],
    [12,12,13,13,13,13,14,14,16,16],
    [12,12,13,13,13,13,14,15,15,16] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [585933395490802720,126495933441549376,547580302606840961,6307865611031818368,8615472134859785408,16480162020771076165,15506433388019190928,17096686892187990104240,567202110751980557440240,15011751046044887144370384],
    [581434266954766624,263683963758950658,413291351456651392,9813495495868587040,12047674605096211648,12005975934809423137,17309634717902219527,349869458116851505563696,391122006275619187459184,547107419291305904348368],
    [584457652154107136,512759562683843904,332499297038142914,9813495495868515337,17670441626443713888,16590539890721294753,420038684689601598532,568824162809387588816,391122006275619184217168,11267980766511471239628848],
    [543258087998754823,485379692798772288,586751371719679361,18749868655641723055,17522569683418559617,556244147038757104,450231760061704997920,13554116122016055696496,15878431631467594520752,15011751046044887147451536],
    [549871712646273056,580341180501701824,518453965704339873,16302379984013657408,17876128774521728007,17375462823837374753,450051834808477386896,11003887474727757809712,391117359414775437701200,544266620703954633399504],
    [299821982963276832,270755228102591680,550822558308906094,18605898810462046496,15529829338976722304,14210303893507883361,9864627387001365071920,12222562688714854665296,17725065960999392289992,507745874377373940651408],
    [269592669576135872,485560281110490400,444072001942012257,18597805270064440704,17626321866149236162,314031996605280861504,381882955956410721328,496205868108646420656,17725065960998351085808,12404934136907118152878601],
    [585933395490868256,269233504214582464,547580302606840961,4047869870129580036,15506421627364680848,201851699553010724960,527364914943727081541,566100270920630539504,469117220188908999053520,547093980550015683335472],
    [585933395490868256,126495933441549376,547580302606840961,8615472134859785408,16480162020771076165,201851699553010724992,496205868416614114448,17096686892187990104240,17725065960992076469488,469117220188908999053520],
    [269385059751991616,486603516886230080,484576043074690182,10537795418650292272,17381942219989357889,592749648984193472527,14394817358211756506208,11892688449000767095920,14659913130903210103952,518132807623131734256],
    [413421258751947808,582385072723166506,485411575785948544,6207172337126736077,530890347550551064995,369527317210694192514,378562880574474684929,454730082175725670512,553907925319331125488,15015150785530070779990539],
    [414550080283248000,402408491374090254,444812067888172485,11758104200926497872,564143586751502614958,525059463600997271713,423566298381695389805,521660999663809108400,19082404867870703453504,346291655558027974620208],
    [126360494596720644,269176125430170816,547580303680582657,16696017077134432425,201908205654585389152,535294830675716315205,458122278442879749296,19199864689878151300480,15878587789331651662032,17725056204240426610000],
    [519609646912438575,546277408199781383,504826850685752464,563068633746691331312,594269260915198506176,556222151039462480161,530896860887543552257,343871483585231293488,450051834512969668098,391116450002214113578384],
    [585933395488518272,197606921923211271,548888406660257801,560722229896607600682,525886641308672854433,458082519036125615568,496205526201168697520,534271078352783907332,11117777866543288554510,11003887467296034129968],
    [378495204214277248,369698911651629345,406887927372716192,11007207780239816001584,10020057339812499188843536,13763827619908865049563248,14749553464386709849478288,17507007027171720240995536,18150467544063377704952048],
    [378495204214277248,369698911651629345,406887927372716192,352230641358286328170544,469117220188902723261584,10020057339812499188843536,13763827619908865049563248,17507007027171720240995536,18150467544063377704952048],
    [81184891723946112,477776609582089696,8650825964748966336,7113728229165314144,2495569766567225545,18821821897176552930,15220349258567228592,17870333284066698502,15011751046044887147451536,17507178044920273930820816],
    [411178293041203488,547580302606840968,18749868655633335680,6307539023974117504,10929617825847020801,14210304022376974448,16695970897648162000,385521080872973043968,352124399191276387401808,18150467544063377704952048],
    [304358095536227520,475525905368985774,18743214607083613216,3905935043579086304,10893550543809091808,9588567557241276577,505989898676937186,15917679034104614590640,16656595886158104400080,13652671906052832224192592],
    [581434266954766624,263683963758950658,9813495495868587040,12047674605096211648,12005975934809423137,13225323246612844768,17309634717902219527,12222562696113099506800,349869458116851505563696,547107419291305904348368],
    [581181414689513760,444072001942012257,8624895878255248576,15537928995535693184,17626321866149236162,15509658281629159600,314031996605280861504,381882955956410721328,17725065960998351085808,12404934136907118152878601],
    [547580302606840961,484571612010618064,18749868655633335680,17564429191272765453,16480188719195201696,16433957541164485025,201851702923460218887,533804172107087747248,352124398953473095239728,469081426670846110513296],
    [585933395490868256,547580302606840961,4047869870129580036,8615472134859785408,16480162020771076165,15506421627364680848,201851699553010724960,17096686892187990104240,18115208669453769512176,469117220188908999053520] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_18 :
    let keys : List (List ℕ) := [
    [12,12,13,13,13,13,15,15,15,15],
    [12,12,13,13,13,14,14,14,14,17],
    [12,12,13,13,13,14,14,14,15,16],
    [12,12,13,13,13,14,14,15,15,15],
    [12,12,13,13,14,14,14,14,14,16],
    [12,12,13,13,14,14,14,14,15,15],
    [12,12,13,14,14,14,14,14,14,15],
    [12,12,13,14,17,17,17,17,17],
    [12,12,13,15,16,17,17,17,17],
    [12,12,13,16,16,16,17,17,17],
    [12,12,14,14,14,14,14,14,14,14],
    [12,12,14,14,16,17,17,17,17],
    [12,12,14,15,15,17,17,17,17],
    [12,12,14,15,16,16,17,17,17],
    [12,12,14,16,16,16,16,17,17],
    [12,12,15,15,15,16,17,17,17],
    [12,12,15,15,16,16,16,17,17],
    [12,12,15,16,16,16,16,16,17],
    [12,12,16,16,16,16,16,16,16],
    [12,13,13,13,13,13,13,13,16,17],
    [12,13,13,13,13,13,13,14,15,17],
    [12,13,13,13,13,13,13,14,16,16],
    [12,13,13,13,13,13,13,15,15,16],
    [12,13,13,13,13,13,14,14,14,17] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [269371876013446188,584526979389490304,18570917776054223279,17381942217027266753,16590311431777552801,15400427580057261200,19084528238888069642668,12114005669262948042800,12225882763831979117065,17094450644933030195408],
    [413421014140138528,582385072723166506,6207172337126736077,15533415674458506624,11547728662834187650,530890347550551064995,378562880574474684929,454730082175725670512,553907925319331125488,15015150785530070779990539],
    [269592669576135872,485560281110490400,9813499897007095104,17626321866149236162,14210304062152458593,595127237467805328768,381882955956410721328,496205868108646420656,17725065960998351085808,387654191506419235260937],
    [126360494596720644,269176125430170816,17522569514617779201,16727963732326586437,16696359292743456937,201908205654585389152,457758754910751493296,19199864689878151300480,15878587789331651662032,17725056204240426610000],
    [306671560396342720,50753606295490028,18812005382456883488,16693799395501710726,565165916002515456013,562958186610732469698,453323796951318604898,343871449533685765168,420038685738614722672,543085189399566681839024],
    [126360494596720644,269176125430170816,17522569514617779201,16727963732326586437,201908205654585389152,457758754910751493296,517064292292115044521,569584215690543607120,19199864689878151300480,15878587789331651662032],
    [585933395488518272,197606921923211271,17564429013128249801,347430558329477767328,560722229896607600682,525886641308672854433,458082519036125615568,496205526201168697520,534271078352783907332,11003887467296034129968],
    [448582365097460992,447549822655248737,15386915920233632032,460412350360230006960,10020057339812499188843536,11267980766511471239628848,12515904193210442754067536,13763827619908865049563248,18150467544063377704952048],
    [378495204214277248,369698911651629345,13020413675762227360,14659913130903210136720,352230641358286328170544,10020057339812499188843536,13763827619908865049563248,17507007027171720240995536,18150467544063377704952048],
    [120730990783398976,593468081050030529,17450618682785207744,391121999520219743161424,508114809258847090479301,547093969599122536307920,10020057339812499188843536,13763827619908865049563248,15011751046044887147451536],
    [368493081352275072,270755228102591680,595388761934785487904,496954431302809225600,562961435797754383810,454729737614603332833,346107444966830713904,382058836402541533264,496309072976076216492,553908311118834706601],
    [378495277425953920,373207720817854753,416654363524298114208,492813682294274495632,544266620703954633399504,10020057339812499188843536,11267980766511471239628848,13763827619908865180697712,18150467544063377704952048],
    [412550483055545632,341546250312846593,385518663078042077440,14477503525296847038544,17096686549971341843664,10020057339812499188843536,11267980766511471239628848,14900595332734212089449995,18150467544063377704952048],
    [448648067265151296,449709267851812161,483596711816243523936,13332687408254718968930,427864672284986966085744,567202110751980553183472,10019803523455107016918032,11267980766511471239628848,15011751046044887147451536],
    [120730990783398976,593468081050030528,558419797849126647840,313126791869140599651376,391121999520219743161424,508114809258847090479301,547093969599122536307920,13763827619908865049563248,15011751046044887147451536],
    [448648067265151296,449709267851811946,15475094778119792406880,9714745344766251598864,13332687408254718968930,427864672284986966085744,11267980766511471239628848,15011751046044887147451536,18150467544063377701872880],
    [448648067265151296,449709267851811946,15475094778119792406880,13332687408254718968930,313126791869140956578832,427864672284986966085744,567202110751980553183472,11267980766511471239628848,15011751046044887147451536],
    [545330839188190400,593468072290167232,9455372943476865304624,126626961201269388164128,391122006037826336066640,421925938678291557909616,469116998607622912543920,508114809258847090479301,17507007027171720240995536],
    [301920603971333408,579993876504289481,577579314896645948607938,387648389979808667338240,388872621245314496561232,430119613122152032798864,508114808950749595310256,547093969599116257434832,567202110751980553281776],
    [81184891723946112,8650825964748966336,15288851506630067680,7113728229165314144,2495569766567225545,18821821897176552930,15220349258567228592,17870333284066698502,469117220188902723261584,17507178044920273930820816],
    [228889154858028290,13258955987591078956,18635161003779983850,10741264555248452014,12877071718341154830,13837669709471220904,16301906239493937584,525058970192195137605,13554121547908402712685,11081332977856895196935216],
    [547580302606840961,18749868655633335680,17564429191272765453,16480188719195201696,16433957541164485025,15506291584339775696,16681380378346494128,201851702923460218887,352124398953473095239728,469081426670846110513296],
    [590123459021080000,11976733049653105856,15256348430080386090,8437885512715450626,13225323246612912256,17727683612708674062,17295408489175518448,19052427996060446696456,12222562696113106846832,349869458116851505563696],
    [582385072723166506,13229472452691702816,6207172337126736077,15533415674458506624,11547728662834187650,14210308702620160112,530890347550551064995,378562880574474684929,553907925319331125488,15015150785530070779990539] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_19 :
    let keys : List (List ℕ) := [
    [12,13,13,13,13,13,14,14,15,16],
    [12,13,13,13,13,13,14,15,15,15],
    [12,13,13,13,13,14,14,14,14,16],
    [12,13,13,13,13,14,14,14,15,15],
    [12,13,13,13,14,14,14,14,14,15],
    [12,13,13,13,17,17,17,17,17],
    [12,13,13,14,14,14,14,14,14,14],
    [12,13,13,14,16,17,17,17,17],
    [12,13,13,15,15,17,17,17,17],
    [12,13,13,15,16,16,17,17,17],
    [12,13,13,16,16,16,16,17,17],
    [12,13,14,14,15,17,17,17,17],
    [12,13,14,14,16,16,17,17,17],
    [12,13,14,15,15,16,17,17,17],
    [12,13,14,15,16,16,16,17,17],
    [12,13,14,16,16,16,16,16,17],
    [12,13,15,15,15,15,17,17,17],
    [12,13,15,15,15,16,16,17,17],
    [12,13,15,15,16,16,16,16,17],
    [12,13,15,16,16,16,16,16,16],
    [12,14,14,14,14,17,17,17,17],
    [12,14,14,14,15,16,17,17,17],
    [12,14,14,14,16,16,16,17,17],
    [12,14,14,15,15,15,17,17,17] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [547580302606840961,18749868655633335680,17564429191272765453,16480188719195201696,16433957541164485025,15506291584339775696,201851702923460218887,533804172107088009392,11003887263610787858480,469081426670846110513296],
    [548888410955225097,18749868655633335680,16480188719195201696,17522569683418910762,16433957541294508449,15506422693622847664,201851702923460218887,11003887263610787858480,14658640609156019697808,17096674507289086111952],
    [189583685745508463,18570882581173475360,15538795526403165504,17381959679256835398,12088160583758783596,599745949111963484522,458123535452127562928,496205526201168762000,561978761512864781608,352124398953483476142128],
    [548888410955225097,18749868655633335680,16480188719195201696,17522569684268987521,16295336272446491041,201851702923460218887,458082519036125615568,496205834298500192432,11003887467296034129968,17096674507289085034632],
    [189583685745508463,3972432238845559824,17381959679256835398,12088160583758783596,599745949111963484522,497207782872932453696,343871483585242335280,496205526201168762000,561978761607328704681,14403861718458432556208],
    [543179951938311553,18742051356933457344,15540180901488111617,17308542945805508848,11267980766511471239628848,12515904193210442754067536,13763827619908865049563248,15011756584620508222498960,16259673896283106895337648],
    [189583685745508463,3972499583932761104,17381959679256835398,599745949111963484522,497205427925184187712,386821138680281075074,343871483585242335280,236762269849496915120,496205526201168762000,561978761607328704681],
    [378495204214277248,11830365172815890721,13020400658823649440,343975269819629963312,460923545762084878914704,10020057339812499188843536,13763827619908865049563248,17507007027171720240995536,18150897934213446403097840],
    [378495204214277248,11830365172815890721,13022208078738757792,12261587231240408335881,14403860805065152500880,10020057339812499188843536,13691667415857027104182384,17507007027171720240995536,18150897934213446403097840],
    [378495204214277248,11830365172815890721,13022208078738757792,12261587231240408335881,460923545762084682830992,567215560444170200097008,10020057339812499188843536,13691667415857027104182384,17507007027171720240995536],
    [448265772422400522,14390696571257982272,13020202547113103394,495238014647157810835808,310871851032520038580720,352124398953483426937904,427864672284986966085744,15011751046044887147451536,530567995006082900829424],
    [341546250312846593,13201471603020467488,385518663078042077440,457978029277587810384,17096686549971341843664,10020057339812499188843536,11267980766511471239628848,14900595332734212089449995,18150467544063377704952048],
    [378495204214277248,13020400658823649440,378571685529803819297,343975269819629963312,313126791869439456805904,460923545762084878914704,13763827619908865049563248,17507007027171720240995536,18150897934213446403097840],
    [378495204214277248,13022208078738757792,378571685529803819297,12261587231240408335881,14403860805065152500880,313126791869439456805904,13691667415857027104182384,17507007027171720240995536,18150897934213446403097840],
    [448648067265151296,14390696571257982273,483596711816243523936,13332687408254718968930,313126791869140956578832,427864672284986966085744,567202110751980553183472,11267980766511471239628848,15011751046044887147451536],
    [370990040922303616,11967593852037499169,416652858642788390944,313126792106933981582352,387648389979808667273264,469117220188902723261584,544266620703954633399504,567202110751746313887984,13691669510030853962597488],
    [485379688574788672,18708274436714436993,14432745977018807821408,14659913121040923989136,15878585537531837911248,18227007118384297187600,11156825052654905318219792,12515904193210442754067536,13763827619908865049563248],
    [449709267851811946,14344504717516816704,15475094778119792406880,9714745344766251598864,13332687408254718968930,352124398953483832657968,427864672284986966085744,15011751046044887147451536,18150467544063377701872880],
    [449709267851811946,14344504717516816704,9714745344766251139568,13332687408254718968930,495238014647157810835808,352124398953483426937904,427864672284986966085744,16580249843940081280240,15011751046044887147451536],
    [545330839188190400,18990978313285341632,15878431631467594617029,126626961201269388164128,302571934194823763265584,391122006037826336066640,421925938678291557909616,469117220193300769868976,547093969599116261629136],
    [161228339616941152,199757556682073413696,602989251408702150114,384263171983985938544,496205879378640605360,10020057339812499188384240,15011751046044887144372368,17507007027171720240995536,530567995006082699508976],
    [378495204214277248,378571685529803819297,416652821082192091296,343975269819629963312,14403860805065152500880,313126791869439456805904,13763827619908865049563248,17507007027171720240995536,18150897934213446403097840],
    [302315613268948128,347297906888886289536,310535947724234688737,553907935214935580912,349869457844939941557296,508114809258847023370416,547093969598882018139462,10060086774452448915850256,13691774637556955540951152],
    [437319147364598240,313754706468771703072,370388677959328349280,18049353590945001934274,15878587780543074767045,16580249843940084359408,12515904193210442754067536,13763827619908865049563248,17507437417321788939147776] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_20 :
    let keys : List (List ℕ) := [
    [12,14,14,15,15,16,16,17,17],
    [12,14,14,15,16,16,16,16,17],
    [12,14,14,16,16,16,16,16,16],
    [12,14,15,15,15,15,16,17,17],
    [12,14,15,15,15,16,16,16,17],
    [12,14,15,15,16,16,16,16,16],
    [12,15,15,15,15,15,15,17,17],
    [12,15,15,15,15,15,16,16,17],
    [12,15,15,15,15,16,16,16,16],
    [13,13,13,13,13,13,13,13,15,17],
    [13,13,13,13,13,13,13,13,16,16],
    [13,13,13,13,13,13,13,14,14,17],
    [13,13,13,13,13,13,13,14,15,16],
    [13,13,13,13,13,13,13,15,15,15],
    [13,13,13,13,13,13,14,14,14,16],
    [13,13,13,13,13,13,14,14,15,15],
    [13,13,13,13,13,14,14,14,14,15],
    [13,13,13,13,14,14,14,14,14,14],
    [13,13,13,13,16,17,17,17,17],
    [13,13,13,14,15,17,17,17,17],
    [13,13,13,14,16,16,17,17,17],
    [13,13,13,15,15,16,17,17,17],
    [13,13,13,15,16,16,16,17,17],
    [13,13,13,16,16,16,16,16,17] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [378495204214277248,378571685529803819297,416652821082192091296,12261587231240408335881,14403860805065152500880,313126791869439456805904,427864672284986966085744,17507007027171720240995536,18150897934213446403097840],
    [120730990770926656,558419797849126647840,607711306032578105792,9785212245919983025200,391121999520219743161424,430119613122152032702576,508114809258847090479301,547093969599122536307920,14673995600660795526155440],
    [120730990770926656,558419797849126647840,607711306032578105792,313126791869140599651376,391121999520219743161424,430119613122152032702576,469117220188902723357872,508114809258847090479301,547093969599122536307920],
    [437319147364598240,370388677959328349280,10040150607000694500640,18049353590945001934274,15878587780543074767045,16580249843940084359408,388867065201193845296208,13763827619908865049563248,17507437417321788939147776],
    [120730990770926656,607711306032578105792,17869433531172052731072,9785212245919983025200,13441237910067245813872,391121999520219743161424,508114809258847090479301,547093969599122536307920,14673995600660795526155440],
    [120730990770926656,607711306032578105792,17869433531172052731072,13441237910067245813872,313126791869140599651376,391121999520219743161424,469117220188902723357872,508114809258847090479301,547093969599122536307920],
    [372932574195490944,11221889948733657878861,12113978447219092622625,13332893652343798701216,5062855896149856945168,13505873078856184932877,18227007118384133513456,13350509872200160149311600,17306772628253457048113360],
    [306678131810579616,11113520809268098466944,9937150327175833454817,12146250280375662642192,11151461419587161109552,18188995269687539605744,508114809258847090479280,546627803937893795473616,13839388762255308098703472],
    [329291037038353793,15904918331958223119424,14389809499237701160064,12222562688682073001025,15878587789372290112005,348650782895465791194128,431370526436511424054384,466862278806379889267856,583264227788297606568176],
    [18752221804941543777,3936510262924279855,10929579342841714816,15503799377190820933,13123705925599864912,15256376224085445104,16479810167214611664,16191993352387017922,15582027186847698324495,10023668360872503221126336],
    [8650825964748966336,2597958211610187904,15288851506630067680,7113728229165314144,2495569766567225545,18821821897176552930,15220349258567228592,17870332914660843750,469117220188902723261584,547099313903758560338128],
    [18752221804941543777,3936510262924279855,10929579342841714816,15503799377190820933,13123705925608180816,15256376224085445104,16191993352387017922,486938341099074685967,527353925358121557200,10023668360872503221126336],
    [18996648672182251648,17564429324416751625,10857204948224089102,16295336272446491041,10495932754810077264,14315078719878925776,15509316374151436464,560722229896606224426,6067899185744091226496,543631780881463533322376],
    [18851371401889251588,8613636013920093376,17520521392984372225,16480162361369565253,14316321201208757424,15112267633074970832,17799494986038973680,19199864689878151300480,6461443312307536146528,16546046402448192606512],
    [18996648672182251648,17564429324416751625,10857204948224089102,16295336272446491041,14315078719878925776,15509316374151436464,560722229896606224426,335869848153912475728,530898962253184450696,194172773943810920227200],
    [18996648672182251648,17564429324416751625,10857204948224089102,16295336272446491041,14315078719878925776,15509316374151436464,560722229896606224426,335869848153912475728,6067899185744091226496,16988766792101903155336],
    [18996648672182251648,17564429324416751625,16295336272446491041,14315078719878925776,15509316374151436464,347430558329483729934,560722229896606224426,335869848153912475728,530898962253184450696,6067899636678007136640],
    [17520521392984372225,16480162361369565253,15112267633074970832,17799494986038973680,599995765931956602240,201920103538629029984,602229652732953821444,275636352440262460608,458122285340597226672,517063950076506019120],
    [15313934436886972800,17878349554641843648,16374422323632344449,16585642559594008752,433731716187055354613872,10020057339812499188843536,12404748465843078470641165,12515904193219989523765328,15011751046044887144372368],
    [15313934436886972800,17878349554641843648,16374422323632344449,530896720005304651952,13441099211656930594928,10020057339812499188843536,12404748465843078470641165,12515904193219989523765328,15011751046044887144372368],
    [17878349554641843648,16374422323632344449,16585642559594008752,490045901953667762560,391122006038875349293136,433731716187055354613872,10020057339812499188843536,12404748465843078470641165,15011751046044887144372368],
    [11943739047301710976,11830365172815890721,13022208078738757792,12261587231240408335881,17725486263646079361264,460923545762084682830992,10020057339812499188843536,12591468803075397837270128,17507007027171720240995536],
    [11943739047301710976,11830365172815890721,13022208078738757792,12261587231240408335881,393483400096106182414448,460923545762084682830992,567215560444170200097008,10020057339812499188843536,17507007027171720240995536],
    [12047530879182113024,13201471603020499232,10929480010011062369,313122353809501194781712,352124398953483476142128,465643604147944127795312,547093969600182450628816,570241944455681689198832,15007024063368002512437609] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_21 :
    let keys : List (List ℕ) := [
    [13,13,14,14,14,17,17,17,17],
    [13,13,14,14,15,16,17,17,17],
    [13,13,14,14,16,16,16,17,17],
    [13,13,14,15,15,15,17,17,17],
    [13,13,14,15,15,16,16,17,17],
    [13,13,14,15,16,16,16,16,17],
    [13,13,14,16,16,16,16,16,16],
    [13,13,15,15,15,15,16,17,17],
    [13,13,15,15,15,16,16,16,17],
    [13,13,15,15,16,16,16,16,16],
    [13,14,14,14,14,16,17,17,17],
    [13,14,14,14,15,15,17,17,17],
    [13,14,14,14,15,16,16,17,17],
    [13,14,14,14,16,16,16,16,17],
    [13,14,14,15,15,15,16,17,17],
    [13,14,14,15,15,16,16,16,17],
    [13,14,14,15,16,16,16,16,16],
    [13,14,15,15,15,15,15,17,17],
    [13,14,15,15,15,15,16,16,17],
    [13,14,15,15,15,16,16,16,16],
    [13,15,15,15,15,15,15,16,17],
    [13,15,15,15,15,15,16,16,16],
    [14,14,14,14,14,15,17,17,17],
    [14,14,14,14,14,16,16,17,17] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [18703634186357487040,11939338901556140112,490045901953667762560,523975136324560948609,530680547236953300144,10020057339812499188384240,12404748465843078470641165,13879414917985771347641456,15011751046044887144372368],
    [11871681453263783040,11933876492858034224,378571685529803819297,416652821082192091296,14403860805065152500880,313126791869439456805904,13763827619908865049563248,17507007027171720240995536,18150897934213446403097840],
    [11792118449104597120,11967593852037499169,416652858642788390944,305891633966967985168,387648389979808667273264,469117220188902723261584,567202110751746313887984,13691669510030853962597488,17416531862526548279205072],
    [13994212708344709600,11830090026598939744,313754706468771703072,18049353590945001934274,15878587780543074767045,16580249843940084359408,12515904193210442754067536,13763827619908865049563248,17507437417321788939147776],
    [11871681453263783040,11830365172806369345,416652821082192091296,12261587231240408343600,14403860805065152500880,313126791869439456805904,427864672284986966085744,17507007027171720240995536,18150897934213446403097840],
    [15532146808552962338,10537313176870198657,496205868417884066000,14389809355496081499232,348650782895465791194128,391122006037826336066625,431370526436511424054384,466862278806379889267856,18664452632953660858734832],
    [12047530879182113024,13201471603020499232,349743360320353996033,313122353809501194781712,352124398953483476142128,468969501980249917833577,465643604147944127795312,547093969600182450628816,570241944455681689198832],
    [9804515817737760032,13994212715658527200,18049353590945001934274,11852437694698517314656,15878587780816715257893,16580249843940084359408,388867065201193845296208,13763827619902502223286384,17507437417321788939147776],
    [9813495504357786630,17309634727532339440,19005239345292693742786,18049353589696609291714,13441237910067447236752,352230641358286328170544,387650703502941532228816,536557275853326207065104,16259673896283106895337648],
    [12047387852442634496,10929480010011062369,13518306921492994197792,14551362629623253993584,313122353809501194781712,351936616863420635940912,468969501980250085605737,547093969600182450628816,570241944455681689198832],
    [18703634186357487040,490045901953667762560,523975136324560948609,382058844849794291792,530680547236953300144,433731716187055354613872,10020057339812499188384240,12404748465843078470641165,15011751046044887144372368],
    [18990978313518066112,123628534553324356928,420038684689601466480,534284589151862037712,17869433531172052731072,15878587779710924853445,9682301893882516703624240,12515903984647031781165488,14522879651627687068503216],
    [11871681453263783040,378571685529803819297,416652821082192091296,383174600976262760496,14403860805065152500880,313126791869439456805904,427864672284986966085744,17507007027171720240995536,18150897934213446403097840],
    [11967593852037499169,377347798269884215424,416652858642788390944,305891633966967985168,387648389979808667273264,469117220188902723261584,544266620703954633399504,567202110751746313887984,13691669510030853962597488],
    [13994212715658527200,370388677959328349280,496205868150522351813,10040150607000694500640,18049353590945001934274,16580249843940084359408,388867065201193845296208,13763827619908865049563248,17507437417321788939147776],
    [3863391704669653024,607711306032578105792,420038684689601466480,17869433531172052731072,14659913131170768030896,391121999520219743161424,508114809258847090479301,547093969599122536307920,9682301893882516703624240],
    [10537313176870198657,497028697873694794816,496205868417884066000,14389809355496081499232,348650782895465791194128,391122006037826336066625,431370526436511424054384,466862278806379889267856,583264227788297606568176],
    [14345553035215872074,460502290280255432715,15476187957863107331456,9932647509137617355248,11077537997147419787339,13370771008905842690192,14659913130903210104944,11267980766520988548545584,530567995006082900829424],
    [10537473648659537281,570014275336811092208,15904918331958223119424,14389809499237701160064,11966510362310913035329,13441092702547822642288,348650782895465791194128,492837602559206456695301,15011751046044887147451536],
    [3863391704669653024,607711306032578105792,17869433531172052731072,13185185583696611184752,14659913131170768030896,302571934191259689761840,391121999520219743161424,508114809258847090479301,547093969599122536307920],
    [10537473648659537281,15904918331958223119424,14389809499237701160064,11966510362310913035329,13441092702547822642288,15878587789372290112005,18227007118390672529648,348650782895465791194128,15011751046044887147451536],
    [10537473648659537281,15904918331958223119424,14389809499237701160064,11966510362310913035329,15878587789372290112005,18227007118390672529648,348650782895465791194128,431370526436511424054384,466862278806379889267856],
    [314032736543290404128,594012481165078864329,422344521333445006480,496200238609112111280,534284589151665921232,18049353590520177659330,12404748479353877355070976,11347154264203588789078538,18150467544063377704952048],
    [314031856139449336841,593913729540396679362,564042299678019040366,420038684689602611344,553908311281034797296,352230641358286328170544,536557275853326207065104,12404822512080184215112912,16259673896283106895337648] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem bucket_17_22 :
    let keys : List (List ℕ) := [
    [14,14,14,14,15,15,16,17,17],
    [14,14,14,14,15,16,16,16,17],
    [14,14,14,14,16,16,16,16,16],
    [14,14,14,15,15,15,15,17,17],
    [14,14,14,15,15,15,16,16,17],
    [14,14,14,15,15,16,16,16,16],
    [14,14,15,15,15,15,15,16,17],
    [14,14,15,15,15,15,16,16,16],
    [14,15,15,15,15,15,15,15,17],
    [14,15,15,15,15,15,15,16,16],
    [15,15,15,15,15,15,15,15,16],
    [17,17,17,17,17,17,17,17] ]
    ∀ xs∈keys, ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=(xs : Multiset ℕ) := by
  intro keys
  let codes : List (List ℕ) := [
    [123628534553324356928,607711306032578105792,420038684689601466480,534284589151862037712,17869433531172052731072,15878587779710924853445,453839996038047772904624,9682301893882516703624240,12515903984647031781165488],
    [123628534553324718112,607711306032578105792,420038684689601466480,534284589151862037712,17869433531172052731072,391121999520219743161424,453839996038047772904624,508114809258847090479301,9682301893882516703624240],
    [459129754720945834506,483632740613262476672,416646593657805342178,455919973412576103588,471591238735128982203810,310871851045404940468717,358097823958215280298032,427864672284986966085744,16580600272790629917936],
    [459057697126907906570,460502290280255432715,346173062410856867915,15476187957863107331456,9932647509137617355248,13370771008905842690192,14659913130903210104944,11267980766520988548545584,530567995006082900829424],
    [607711306032578105792,420038684689601466480,534284589151862037712,3956113105706390979904,17869433531172052731072,15878587779710924853445,391121999520219743161424,453839996038047772904624,9682301893882516703624240],
    [335661337947790384513,449681546851178161280,481286721584428718597,15904918331958223119424,11966510362310913035329,348650782895465791194128,431370526436511424054384,466862278806379889267856,583694617933971251728624],
    [335661337947790384513,449681546851178161280,15904918331958223119424,11966510362310913035329,13441092702547822642288,15401175090701718919685,18240456810436601616624,348650782895465791194128,15011751046044887147451536],
    [335661337947790384513,449681546851178161280,15904918331958223119424,11966510362310913035329,13480328951147387815024,15401175090701718788613,348650782895465791194128,466862278806379889267856,583694617933971251728624],
    [416646490071822766115,8865365531379954128909,16875685973920023057632,16830678369285868751265,12114012186869020852304,14659912910168931767440,15878431631467562089648,17082118873293420502224,10020057339812499188843536],
    [497031052900397302094,14432818034612845847648,10895336965472925032464,14546924569450750480816,9936428093098637279587,13517392505083413010541,18227004524636367264016,612849559352908700883329,391122179664237213910498],
    [8832547729740612666570,18020430148910881738761,14551351359629085228481,9785073522428733690896,12152096025330520722512,14659912602071435678864,16971556283924534663600,17760841457161835130096,353375318777484668831792],
    [10020057339812499188843536,11267980766511471239628848,12515904193210442754067536,13763827619908865049563248,15011751046044887147451536,16259673896283106895337648,17507007027171720240995536,18150467544063377704952048] ]
  let decode (l k : ℕ) : List ℕ := (List.range l).map fun i => (k >>> (5*i)) % 32
  let tab := List.zipWith (fun ls xs => (ls, List.zipWith decode ls xs)) keys codes
  exact checked_rows 17 (by decide) tab keys (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem complete_17 (m : Multiset ℕ) (hb : ∀ k∈m,11 ≤ k ∧ k ≤ 17) (hs : m.sum=136) :
    ∃ C : Multiset (Cycle (completeGraph (Fin 17))), IsCycleDecomposition _ C ∧ lengths C=m := by
  exact fast_keys 17 11 136 (by decide) _ (together (together (together (together bucket_17_0 bucket_17_1) (together bucket_17_2 (together bucket_17_3 bucket_17_4))) (together (together bucket_17_5 (together bucket_17_6 bucket_17_7)) (together bucket_17_8 (together bucket_17_9 bucket_17_10)))) (together (together (together bucket_17_11 (together bucket_17_12 bucket_17_13)) (together bucket_17_14 (together bucket_17_15 bucket_17_16))) (together (together bucket_17_17 (together bucket_17_18 bucket_17_19)) (together bucket_17_20 (together bucket_17_21 bucket_17_22))))) (by decide +kernel) m hb hs

end AlspachLongFinite

namespace OMA.R_AlspachConjecture_alspach_conjecture_variants_long_cycles_R2
open SimpleGraph AlspachConjecture Multiset
/-- For each cycle count, at most one boundary profile containing a shorter
cycle can meet the total length: every remaining length is the minimum or the order. -/
def H1 : Prop := ∀ (n : ℕ), Odd n → 17 < n → ∀ i j c : ℕ,
    let a := (n+5)/2
    a ≤ c → c < n → c+i*a+j*n=n.choose 2 →
    ∃ C : Multiset (Cycle (completeGraph (Fin n))), IsCycleDecomposition _ C ∧
      lengths C=c ::ₘ (Multiset.replicate i a + Multiset.replicate j n)

/-- The unit redistribution step when no source decomposition exhibits a
triangle detour. A triangle in any suitable realization already certifies the step. -/
def H2 : Prop := ∀ (n : ℕ), Odd n → 17 < n → ∀ (R : Multiset ℕ) (s t : ℕ),
    let a := (n+5)/2
    let G := completeGraph (Fin n)
    a ≤ s → s+2 ≤ t → t ≤ n → (∀x∈R,a ≤ x ∧ x ≤ n) → s+t+R.sum=n.choose 2 →
    (∃ C : Multiset (Cycle G), IsCycleDecomposition G C ∧ lengths C=s ::ₘ t ::ₘ R) →
    ¬(∃ (x v y : Fin n) (P Q : G.Walk y x) (A B : Cycle G) (D : Multiset (Cycle G)),
      P.IsPath ∧ Q.IsPath ∧ v ∉ P.support ∧
      A.edges = s(x,y) :: P.edges ∧ B.edges = s(x,v) :: s(v,y) :: Q.edges ∧
      A.length=s ∧ B.length=t ∧ lengths D=R ∧ IsCycleDecomposition G (A ::ₘ B ::ₘ D)) →
    ∃ C : Multiset (Cycle G), IsCycleDecomposition G C ∧ lengths C=(s+1) ::ₘ (t-1) ::ₘ R

theorem large_from_hypotheses
    (ham : ∀ (n : ℕ), Odd n → 17 < n → ∀ L : Multiset ℕ, (∀x∈L,x=n) → L.sum=n.choose 2 →
      ∃ C : Multiset (Cycle (completeGraph (Fin n))), IsCycleDecomposition _ C ∧ lengths C=L)
    (border : H1) (transfer : H2) (n : ℕ) (odd : Odd n) (large : 17 < n)
    (L : Multiset ℕ) (bounds : ∀x ∈ L,(n+5)/2 ≤ x ∧ x ≤ n) (budget : L.sum=n.choose 2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n))), IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  let G := completeGraph (Fin n)
  let real (M : Multiset ℕ) := ∃ C : Multiset (Cycle G), IsCycleDecomposition G C ∧ lengths C=M
  apply LongCycleRedistribution.of_boundary_and_transfers ((n+5)/2) n (n.choose 2) real
      (ham n odd large) (border n odd large) ?_ L bounds budget
  intro R s t sLow apart tHigh rest cost old
  by_cases pivot : (∃ (x v y : Fin n) (P Q : G.Walk y x) (A B : Cycle G) (D : Multiset (Cycle G)),
      P.IsPath ∧ Q.IsPath ∧ v ∉ P.support ∧
      A.edges = s(x,y) :: P.edges ∧ B.edges = s(x,v) :: s(v,y) :: Q.edges ∧
      A.length=s ∧ B.length=t ∧ lengths D=R ∧ IsCycleDecomposition G (A ::ₘ B ::ₘ D))
  · obtain ⟨x,v,y,P,Q,A,B,D,hp,hq,outside,ae,be,alen,blen,dlen,cover⟩ := pivot
    have xy : G.Adj x y := A.walk.adj_of_mem_edges (show s(x,y)∈A.edges by rw [ae]; simp)
    have xv : G.Adj x v := B.walk.adj_of_mem_edges (show s(x,v)∈B.edges by rw [be]; simp)
    have vy : G.Adj v y := B.walk.adj_of_mem_edges (show s(v,y)∈B.edges by rw [be]; simp)
    have first := congrArg List.length ae
    have second := congrArg List.length be
    have edgeLen (z : Cycle G) : z.edges.length=z.length := z.walk.length_edges
    simp only [List.length_cons,Walk.length_edges,edgeLen,alen,blen] at first second
    obtain ⟨A',B',a'len,b'len,immutable⟩ := LongCycleRedistribution.triangle_switch
      xy xv vy P Q hp hq outside (by omega) (by omega) A B ae be
    refine ⟨A' ::ₘ B' ::ₘ D, fun e he => (immutable D e).trans (cover e he),?_⟩
    have aform : A'.length=s+1 := by omega
    have bform : B'.length=t-1 := by omega
    simp only [lengths, Multiset.map_cons] at dlen ⊢
    rw [aform,bform,dlen]
  · exact transfer n odd large R s t sLow apart tHigh rest cost old pivot

end OMA.R_AlspachConjecture_alspach_conjecture_variants_long_cycles_R2

namespace OMA.R_AlspachConjecture_alspach_conjecture_variants_long_cycles_R2
open SimpleGraph AlspachConjecture

theorem main : H1 → H2 → type_of% @AlspachConjecture.alspach_conjecture.variants.long_cycles := by
  intro h₁ h₂ n hn m hm hsum
  by_cases hn' : 17 < n
  · exact large_from_hypotheses (fun k h hk => LongCycleRedistribution.all_hamilton k h (by omega))
      h₁ h₂ n hn hn' m hm hsum
  · have valid : n=1 ∨ n=3 ∨ n=5 ∨ n=7 ∨ n=9 ∨ n=11 ∨ n=13 ∨ n=15 ∨ n=17 := by
      obtain ⟨j,hj⟩ := hn
      omega
    rcases valid with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact AlspachConjecture.alspach_conjecture.variants.one m hm hsum
    · exact AlspachConjecture.alspach_conjecture.variants.three m (fun x hx => ⟨le_trans (by decide : 3 ≤ (3+5)/2) (hm x hx).1,(hm x hx).2⟩) hsum
    · exact AlspachLongFinite.complete_5 m hm hsum
    · exact AlspachLongFinite.complete_7 m hm hsum
    · exact AlspachLongFinite.complete_9 m hm hsum
    · exact AlspachLongFinite.complete_11 m hm hsum
    · exact AlspachLongFinite.complete_13 m hm hsum
    · exact AlspachLongFinite.complete_15 m hm hsum
    · exact AlspachLongFinite.complete_17 m hm hsum

end OMA.R_AlspachConjecture_alspach_conjecture_variants_long_cycles_R2
