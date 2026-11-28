import OMAReductions.R_opg_caccetta_haggkvist_conjecture_R1

/-!
# Rooted separators and integral triangle descent for Caccetta–Häggkvist

This reduction refines H2 (minimum outdegree at least three) of the parent
reduction. It supplies two proved ways to find a short cycle and gives
structural information for the remaining cases. The conjecture for unrestricted
digraphs stays open; the full known degree-three theorem is not invoked.

* Search backwards from a prescribed root of outdegree d. If all of the first
  t external layers have at least r vertices and none reaches a successor,
  the ball and the d successors occupy at least 1+tr+d vertices. Otherwise
  there is a short rooted cycle or a layer separating the root from all
  its successors. This includes the classical high-connectivity case.
* In the absence of a short cycle, the far side of the cut contains a minimal
  set S with fewer than r external out-neighbours. Its induced digraph is
  strongly connected, and S has more vertices than the cycle budget. Erasing
  any vertex of S shows that S has exactly r−1 exits. A deficient subset
  argument gives Hall representatives for any collection of fewer than |S|
  exits even after one specified representative is forbidden.
* In a digon- and triangle-free host of order n and minimum outdegree r, take
  r successors of a vertex of high indegree. Their induced minimum outdegree
  is at least 3r+1−n. With u=n+1 and v=r+1 the descent (u,v) ↦ (v,3v−u)
  preserves u²−3uv+v². If this integer is at most −2, the process cannot
  terminate at a loopless singleton. The resulting finite-order criterion
  includes the nine-vertex degree-three case.
* In an r-in/r-out regular graph, count the arcs leaving a shortest cycle
  within S, then do the same in the reversed graph on the other side of its
  exits E. A shortest cycle has no chord. When r=3 and |E|=2 the two counts
  yield 10(K+1) ≤ 3(n+2), contradicting n ≤ 3K. This proves the CH bound for
  every 3-in/3-out regular digraph, regardless of order or connectivity.
* Thin arcs to exact outdegree and pass to a sink strongly connected component.
  The unresolved steps separate degree three from higher degrees. Both retain
  the symmetric-subgraph exclusion from the parent and the certified regions.

References: J.-C. Bermond, 1-graphes réguliers minimaux de girth donné,
Cahiers du CERO 17 (1975), 125–135 (the 3-regular case); L. Caccetta and R. Häggkvist, On minimal digraphs with given girth
(1978); Y. O. Hamidoune, A note on minimal directed graphs with given girth (1987),
https://doi.org/10.1016/0095-8956(87)90009-8; J. Shen and D. A. Gregory,
On the girth of digraphs with high connectivity, Ars Combinatoria 60 (2001),
201–207 (distance-layer argument for full connectivity); M. B. Nathanson,
The Caccetta–Häggkvist conjecture and additive number theory, Theorem 4
(neighbourhood induction). Stronger asymptotic triangle bounds are known:
J. Hladký, D. Král' and S. Norin, https://doi.org/10.1007/s00493-015-2662-5.
-/

-- Credit: @qtyan0721
-- Agent: codex
-- Model: gpt-6.2-astra


namespace OMA.CHDensity

open OMA.S_opg_caccetta_haggkvist_conjecture
open OMA.R_opg_caccetta_haggkvist_conjecture_R1
open Finset

variable {V : Type}

private theorem walk_two (G : Digraph V) (hloop : ∀ x, ¬ G.Adj x x)
    {a b : V} (hab : G.Adj a b) (hba : G.Adj b a) :
    ∃ k, k ≤ 2 ∧ HasDirectedCycleOfLength G k := by
  let f (i : ℕ) : V := if i = 1 then b else a
  apply cycle_of_closed_walk G hloop 2 f (by decide) (by simp [f])
  intro i hi
  interval_cases i <;> simp_all [f]

private theorem walk_three (G : Digraph V) (hloop : ∀ x, ¬ G.Adj x x)
    {a b z : V} (hab : G.Adj a b) (hbz : G.Adj b z) (hza : G.Adj z a) :
    ∃ k, k ≤ 3 ∧ HasDirectedCycleOfLength G k := by
  let f (i : ℕ) : V := if i = 1 then b else if i = 2 then z else a
  apply cycle_of_closed_walk G hloop 3 f (by decide) (by simp [f])
  intro i hi
  interval_cases i <;> simp_all [f]

/-- Counting the in-neighbors of v, chosen successors, and the exterior
successors of b. In girth at least four all three parts avoid v and each other. -/
theorem count_successor_neighborhood (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (T B : Finset V) {v b : V} (hv : v ∈ T)
    (Bsub : B ⊆ T) (hedge : ∀ x ∈ B, G.Adj v x) (hbB : b ∈ B)
    (hno : ¬ ∃ k, k ≤ 3 ∧ HasDirectedCycleOfLength G k) :
    (T.filter (fun x => G.Adj x v)).card + B.card + (T.filter (G.Adj b)).card + 1 ≤
      T.card + (B.filter (G.Adj b)).card := by
  classical
  have hvb := hedge b hbB
  let A := T.filter (fun y => G.Adj y v)
  let N := T.filter (G.Adj b)
  let W := N \ B
  have hpart : W.card + (B.filter (G.Adj b)).card = N.card := by
    have heq : N ∩ B = B.filter (G.Adj b) := by
      ext x
      constructor
      · intro h
        obtain ⟨hN, hB⟩ := Finset.mem_inter.mp h
        exact Finset.mem_filter.mpr ⟨hB, (Finset.mem_filter.mp hN).2⟩
      · intro h
        obtain ⟨hB, hbx⟩ := Finset.mem_filter.mp h
        exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Bsub hB, hbx⟩, hB⟩
    rw [← heq]
    exact Finset.card_sdiff_add_card_inter N B
  have nodigon {x y : V} (hxy : G.Adj x y) (hyx : G.Adj y x) : False := by
    obtain ⟨k, hk, hcycle⟩ := walk_two G hloop hxy hyx
    exact hno ⟨k, by omega, hcycle⟩
  have AB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact nodigon (Finset.mem_filter.mp hx).2 (hedge x hy)
  have AW : Disjoint A W := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hbx : G.Adj b x := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hy).1).2
    exact hno (walk_three G hloop hvb hbx (Finset.mem_filter.mp hx).2)
  have BW : Disjoint B W := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 hx
  have hvA : v ∉ A := fun h => hloop v (Finset.mem_filter.mp h).2
  have hvB : v ∉ B := fun h => hloop v (hedge v h)
  have hvW : v ∉ W := fun h => nodigon hvb (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2
  have hsum : A.card + B.card + W.card + 1 ≤ T.card := by
    have hsubset : insert v (A ∪ B ∪ W) ⊆ T := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_union] at hx
      rcases hx with h | (h | h) | h
      · exact h ▸ hv
      · exact (Finset.mem_filter.mp h).1
      · exact Bsub h
      · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).1
    have h := Finset.card_le_card hsubset
    simpa only [Finset.card_insert_of_notMem (show v ∉ A ∪ B ∪ W by simp [hvA, hvB, hvW]),
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨AW,BW⟩),
      Finset.card_union_of_disjoint AB] using h
  change A.card + B.card + N.card + 1 ≤ _
  omega

/-- A digraph with no digon or directed triangle and minimum outdegree r
contains r vertices whose internal minimum outdegree is at least 3r+1−n.
The conclusion is in additive form and also holds inside a specified region. -/
theorem next_neighborhood (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (S : Finset V) (hS : S.Nonempty) (r : ℕ)
    (hdegree : ∀ x ∈ S, r ≤ (S.filter (G.Adj x)).card)
    (hno : ¬ ∃ k, k ≤ 3 ∧ HasDirectedCycleOfLength G k) :
    ∃ B ⊆ S, B.card = r ∧ ∀ x ∈ B, 3*r+1 ≤ S.card + (B.filter (G.Adj x)).card := by
  classical
  obtain ⟨v, hv, hin⟩ : ∃ v ∈ S, r ≤ (S.filter (fun y => G.Adj y v)).card := by
    by_contra! h
    exact (lt_irrefl _) (Finset.card_nsmul_lt_card_nsmul_of_le_of_lt G.Adj hS hdegree h)
  obtain ⟨B, hB, heq⟩ := Finset.exists_subset_card_eq (hdegree v hv)
  have Bsub : B ⊆ S := hB.trans (Finset.filter_subset _ _)
  refine ⟨B, Bsub, heq, ?_⟩
  intro b hb
  have hcnt := count_successor_neighborhood G hloop S B hv Bsub
    (fun x hx => (Finset.mem_filter.mp (hB hx)).2) hb hno
  have hout := hdegree b (Bsub hb)
  omega



/-- An integral density certificate. Shifting order and degree by one, the
successor-neighborhood step sends (u,v) to (v,3v−u) and preserves the
binary quadratic form u²−3uv+v². Values at most −2 force descent. -/
theorem triangle_of_integral_density (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (S : Finset V) (hS : S.Nonempty) (r : ℕ)
    (hdegree : ∀ x ∈ S, r ≤ (S.filter (G.Adj x)).card)
    (hquad : ((S.card : ℤ) + 1)^2 + ((r : ℤ) + 1)^2 + 2 ≤
      3 * ((S.card : ℤ) + 1) * ((r : ℤ) + 1)) :
    ∃ k, k ≤ 3 ∧ HasDirectedCycleOfLength G k := by
  classical
  by_contra hno
  suffices claim : ∀ (n : ℕ) (T : Finset V) (d : ℕ), T.card = n → T.Nonempty →
      (∀ x ∈ T, d ≤ (T.filter (G.Adj x)).card) →
      ((n : ℤ) + 1)^2 + ((d : ℤ) + 1)^2 + 2 ≤ 3*((n : ℤ)+1)*((d : ℤ)+1) → False by
    exact claim _ S r rfl hS hdegree hquad
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T d hT hne hdeg hform
    obtain ⟨x, hx⟩ := hne
    have hproper : T.filter (G.Adj x) ⊂ T := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.filter_subset _ _, fun heq => hloop x (Finset.mem_filter.mp (heq ▸ hx)).2⟩
    have hdlt : d < n := (hdeg x hx).trans_lt (hT ▸ Finset.card_lt_card hproper)
    let u : ℤ := n+1
    let v : ℤ := d+1
    change u^2 + v^2 + 2 ≤ 3*u*v at hform
    have hu : 0 < u := by dsimp [u]; omega
    have hv : 0 < v := by dsimp [v]; omega
    have hdpos : 0 < d := by
      by_contra! hz
      have hv1 : v = 1 := by dsimp [v]; omega
      rw [hv1] at hform
      nlinarith [sq_nonneg (2*u-3)]
    have hnext : 2 ≤ 3*v-u := by
      by_contra! h
      by_cases hneg : 3*v ≤ u
      · nlinarith [mul_nonneg (sub_nonneg.mpr hneg) hu.le, sq_nonneg v]
      · have heq : u = 3*v-1 := by omega
        rw [heq] at hform
        nlinarith [sq_nonneg (2*v-3)]
    obtain ⟨B, _, hB, hcore⟩ := next_neighborhood G hloop T ⟨x,hx⟩ d hdeg hno
    let d' := 3*d+1-n
    have hnd : n + d' = 3*d+1 := by dsimp [u,v] at hnext; dsimp [d']; omega
    have hd' : (d' : ℤ)+1 = 3*v-u := by dsimp [v,u]; omega
    refine ih d hdlt B d' hB (Finset.card_pos.mp (hB ▸ hdpos)) ?_ ?_
    · intro b hb
      have h1 := hcore b hb
      omega
    · change v^2 + ((d':ℤ)+1)^2 + 2 ≤ 3*v*((d':ℤ)+1)
      rw [hd']
      nlinarith only [hform]


variable [Fintype V]

/-- An integer certificate for the whole graph. All boundary comparisons
are exact and can be checked using integer arithmetic. -/
theorem triangle_of_integral_min_outdegree [Nonempty V] (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (r : ℕ) (hdegree : ∀ x, r ≤ outdegree G x)
    (hquad : ((Fintype.card V : ℤ) + 1)^2 + ((r : ℤ) + 1)^2 + 2 ≤
      3 * ((Fintype.card V : ℤ) + 1) * ((r : ℤ) + 1)) :
    ∃ k, k ≤ 3 ∧ HasDirectedCycleOfLength G k := by
  apply triangle_of_integral_density G hloop Finset.univ Finset.univ_nonempty r
    (fun x _ => hdegree x)
  simpa only [Finset.card_univ] using hquad

/-- The classical Caccetta–Häggkvist triangle density threshold also
holds relative to the n−1 possible neighbors, as a corollary of descent. -/
theorem triangle_of_golden_density [Nonempty V] (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (r : ℕ) (hdegree : ∀ x, r ≤ outdegree G x)
    (hsize : (3 - Real.sqrt 5) / 2 * (Fintype.card V - 1 : ℝ) < r) :
    ∃ k, k ≤ 3 ∧ HasDirectedCycleOfLength G k := by
  let n := Fintype.card V
  let c : ℝ := (3 - Real.sqrt 5)/2
  let a : ℝ := n-1
  let u : ℝ := a+2
  let v : ℝ := r+1
  let w : ℝ := c*a+1
  have hn : 1 ≤ n := Fintype.card_pos
  obtain ⟨x⟩ := ‹Nonempty V›
  have hr : r < n := (hdegree x).trans_lt (outdegree_lt_card G hloop x)
  have ha : 0 ≤ a := by dsimp [a]; exact sub_nonneg.mpr (by exact_mod_cast hn)
  have hu : 0 < u := by dsimp [u]; linarith
  have hwv : w < v := by dsimp [w, v]; linarith only [show c*a < r from hsize]
  have hvu : v ≤ u := by
    have h : (r : ℝ) ≤ n := by exact_mod_cast hr.le
    dsimp [v, u, a]
    linarith
  have he := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hs := Real.sqrt_nonneg (5:ℝ)
  have hc : (1:ℝ)/4 < c := by dsimp [c]; nlinarith [sq_nonneg (Real.sqrt 5 - 5/2)]
  have hroot : c^2 = 3*c-1 := by dsimp [c]; nlinarith
  have heval : w^2 - 3*u*w + u^2 = (1-4*c)*a-1 := by
    dsimp [w,u]
    nlinarith only [congrArg (fun t : ℝ => t*a^2) hroot]
  have hneg := mul_nonpos_of_nonpos_of_nonneg (show 1-4*c ≤ 0 by linarith) ha
  have hmono := mul_neg_of_pos_of_neg (sub_pos.mpr hwv) (show v+w-3*u < 0 by linarith)
  have hfinal : u^2+v^2-3*u*v < -1 := by nlinarith only [heval,hneg,hmono]
  have hreal : ((n:ℝ)+1)^2 + ((r:ℝ)+1)^2 - 3*((n:ℝ)+1)*((r:ℝ)+1) < -1 := by
    dsimp [u,a,v] at hfinal
    linarith only [hfinal]
  have hint : ((n:ℤ)+1)^2 + ((r:ℤ)+1)^2 - 3*((n:ℤ)+1)*((r:ℤ)+1) < -1 := by
    exact_mod_cast hreal
  apply triangle_of_integral_min_outdegree G hloop r hdegree
  change ((n:ℤ)+1)^2 + ((r:ℤ)+1)^2 + 2 ≤ 3*((n:ℤ)+1)*((r:ℤ)+1)
  omega

/-- The degree-three triangle case, including all nine-vertex hosts. -/
theorem triangle_of_three_outneighbors [Nonempty V] (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (hdegree : ∀ x, 3 ≤ outdegree G x)
    (hsize : Fintype.card V ≤ 9) :
    ∃ k, k ≤ 3 ∧ HasDirectedCycleOfLength G k := by
  obtain ⟨x⟩ := ‹Nonempty V›
  have hmin := (hdegree x).trans_lt (outdegree_lt_card G hloop x)
  apply triangle_of_integral_min_outdegree G hloop 3 hdegree
  have hmax : (Fintype.card V : ℤ) ≤ 9 := by exact_mod_cast hsize
  have hlow : (4:ℤ) ≤ Fintype.card V := by exact_mod_cast hmin
  norm_num
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlow) (sub_nonpos.mpr hmax)]

end OMA.CHDensity


namespace OMA.CHConnectivity
open OMA.S_opg_caccetta_haggkvist_conjecture
open OMA.R_opg_caccetta_haggkvist_conjecture_R1

variable {V : Type} [Fintype V]

omit [Fintype V] in
private theorem add_arc {G : Digraph V} {x y z : V} {k : ℕ}
    (e : G.Adj x y) (f : ℕ → V) (hz : f 0 = y) (hk : f k = z)
    (hs : ∀ j < k, G.Adj (f j) (f (j+1))) :
    ∃ g : ℕ → V, g 0 = x ∧ g (k+1) = z ∧ ∀ j < k+1, G.Adj (g j) (g (j+1)) := by
  let g : ℕ → V
    | 0 => x
    | j+1 => f j
  refine ⟨g, rfl, hk, ?_⟩
  intro j hj
  cases j with
  | zero => simpa [g, hz] using e
  | succ j => exact hs j (by omega)

omit [Fintype V] in
/-- Deleting an external in-boundary prevents any vertex outside a region from
reaching the region along surviving arcs. -/
theorem inBoundary_separates (G : Digraph V) (A F : Finset V)
    (hF : ∀ x, x ∈ F ↔ x ∉ A ∧ ∃ y ∈ A, G.Adj x y) {x y : V}
    (hx : x ∉ A) (hy : y ∈ A) :
    ¬ Relation.ReflTransGen (fun a b => a ∉ F ∧ b ∉ F ∧ G.Adj a b) x y := by
  intro path
  induction path with
  | refl => exact hx hy
  | @tail a b p e ih =>
    by_cases ha : a ∈ A
    · exact ih ha
    · exact e.1 ((hF a).mpr ⟨ha, b, hy, e.2.2⟩)

open scoped Classical in
/-- If the degree and growth budget cover the order, then either the prescribed
root has a short simple cycle or one of its reverse distance layers is small.
This layer avoids, and separates from the root, every one of its successors. -/
theorem rooted_cycle_or_small_layer (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (v : V) (r t : ℕ)
    (hsize : Fintype.card V ≤ outdegree G v + t*r)
    (B : ℕ → Finset V) (F : Finset V → Finset V)
    (hzero : B 0 = {v}) (hsucc : ∀ i, B (i+1) = B i ∪ F (B i))
    (hF : ∀ (A : Finset V) x, x ∈ F A ↔ x ∉ A ∧ ∃ y ∈ A, G.Adj x y) :
    (∃ k, k ≤ t+1 ∧ 2 ≤ k ∧ ∃ c : Fin k → V, Function.Injective c ∧
      (∀ i, G.Adj (c i) (c (finRotate k i))) ∧ v ∈ Set.range c) ∨
    ∃ i < t, (F (B i)).card < r ∧ v ∉ F (B i) ∧
      ∀ x, G.Adj v x → x ∉ F (B i) ∧
        ¬ Relation.ReflTransGen (fun a b => a ∉ (F (B i)) ∧ b ∉ (F (B i)) ∧ G.Adj a b) x v := by
  classical
  apply or_iff_not_imp_left.mpr
  intro hc
  have monoB : Monotone B := by
    apply monotone_nat_of_le_succ
    intro i
    rw [hsucc]
    exact Finset.subset_union_left
  have root_mem (i : ℕ) : v ∈ B i := monoB (Nat.zero_le i) (by simp [hzero])
  have walk (i : ℕ) {x : V} (hx : x ∈ B i) :
      ∃ k ≤ i, ∃ f : ℕ → V, f 0 = x ∧ f k = v ∧ ∀ j < k, G.Adj (f j) (f (j+1)) := by
    induction i generalizing x with
    | zero =>
      have hv : x = v := by simpa [hzero] using hx
      exact ⟨0, le_rfl, fun _ => x, rfl, hv, by simp⟩
    | succ i ih =>
      rw [hsucc] at hx
      rcases Finset.mem_union.mp hx with ha | hf
      · obtain ⟨k, hk, p⟩ := ih ha
        exact ⟨k, by omega, p⟩
      · obtain ⟨y, hy, e⟩ := ((hF _ _).mp hf).2
        obtain ⟨k, hk, f, h0, h1, hs⟩ := ih hy
        exact ⟨k+1, by omega, add_arc e f h0 h1 hs⟩
  have hout {x : V} (e : G.Adj v x) : x ∉ B t := by
    intro hx
    obtain ⟨k, hk, f, h0, h1, hs⟩ := walk t hx
    obtain ⟨g, hg, hret, hstep⟩ := add_arc e f h0 h1 hs
    obtain ⟨l, hl, htwo, c, hi, hadj, hm⟩ :=
      cycle_through_of_closed_walk G hloop (k+1) g (by omega) (hret.trans hg.symm) hstep
    exact hc ⟨l, by omega, htwo, c, hi, hadj, hg ▸ hm⟩
  have small : ∃ i < t, (F (B i)).card < r := by
    by_contra! h
    have grow (i : ℕ) (hi : i ≤ t) : 1 + i*r ≤ (B i).card := by
      induction i with
      | zero => simp [hzero]
      | succ i ih =>
        have hd : Disjoint (B i) (F (B i)) :=
          Finset.disjoint_left.mpr fun _ hx hf => ((hF _ _).mp hf).1 hx
        rw [hsucc, Finset.card_union_of_disjoint hd, Nat.succ_mul]
        have := ih (by omega)
        have := h i (by omega)
        omega
    let S := Finset.univ.filter (fun x => G.Adj v x)
    have hd : Disjoint S (B t) :=
      Finset.disjoint_left.mpr fun _ hx => hout (Finset.mem_filter.mp hx).2
    have hu := Finset.card_le_univ (S ∪ B t)
    rw [Finset.card_union_of_disjoint hd] at hu
    have hS : S.card = outdegree G v := rfl
    have := grow t le_rfl
    omega
  obtain ⟨i, hi, hf⟩ := small
  refine ⟨i, hi, hf, fun h => ((hF _ _).mp h).1 (root_mem i), ?_⟩
  intro x e
  have hnext : x ∉ B (i+1) := fun hx => hout e (monoB hi hx)
  rw [hsucc] at hnext
  refine ⟨fun h => hnext (Finset.mem_union_right _ h), ?_⟩
  exact inBoundary_separates G (B i) (F (B i)) (hF _) (fun h =>
    hnext (Finset.mem_union_left _ h)) (root_mem i)

/-- A canonical small separator exists when the prescribed root has no short
cycle. The separator can be chosen disjoint from the entire out-neighborhood. -/
theorem rooted_cycle_or_small_separator (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (v : V) (r t : ℕ)
    (hsize : Fintype.card V ≤ outdegree G v + t*r) :
    (∃ k, k ≤ t+1 ∧ 2 ≤ k ∧ ∃ c : Fin k → V, Function.Injective c ∧
      (∀ i, G.Adj (c i) (c (finRotate k i))) ∧ v ∈ Set.range c) ∨
    ∃ F : Finset V, F.card < r ∧ v ∉ F ∧ ∀ x, G.Adj v x → x ∉ F ∧
      ¬ Relation.ReflTransGen (fun a b => a ∉ F ∧ b ∉ F ∧ G.Adj a b) x v := by
  classical
  let boundary (A : Finset V) := Finset.univ.filter (fun x => x ∉ A ∧ ∃ y ∈ A, G.Adj x y)
  let B : ℕ → Finset V := Nat.rec {v} (fun _ A => A ∪ boundary A)
  rcases rooted_cycle_or_small_layer G hloop v r t hsize B boundary rfl
      (fun _ => rfl) (by intro A x; simp [boundary]) with hc | ⟨i, _, hs⟩
  · exact Or.inl hc
  · exact Or.inr ⟨boundary (B i), hs⟩

theorem rooted_cycle_of_connectivity_budget (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (v : V) (r t : ℕ)
    (hdeg : 0 < outdegree G v) (hconn : (∀ (F : Finset V), F.card < r → ∀ x ∉ F, ∀ y ∉ F,
      Relation.ReflTransGen (fun a b => a ∉ F ∧ b ∉ F ∧ G.Adj a b) x y))
    (hsize : Fintype.card V ≤ outdegree G v + t*r) : ∃ k, k ≤ t+1 ∧ 2 ≤ k ∧ ∃ c : Fin k → V, Function.Injective c ∧
      (∀ i, G.Adj (c i) (c (finRotate k i))) ∧ v ∈ Set.range c := by
  classical
  rcases rooted_cycle_or_small_separator G hloop v r t hsize with hc | ⟨F, hf, hv, hsep⟩
  · exact hc
  · obtain ⟨x, hx⟩ := Finset.card_pos.mp hdeg
    have e := (Finset.mem_filter.mp hx).2
    obtain ⟨hx', hn⟩ := hsep x e
    exact False.elim (hn (hconn _ hf x hx' v hv))

/-- Every specified root of outdegree at least r lies on a short cycle when
deleting fewer than r vertices preserves strong connectivity. -/
theorem rooted_cycle_of_strong_connectivity (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (v : V) (r : ℕ) (hr : 0 < r)
    (hdeg : r ≤ outdegree G v) (hconn : (∀ (F : Finset V), F.card < r → ∀ x ∉ F, ∀ y ∉ F,
      Relation.ReflTransGen (fun a b => a ∉ F ∧ b ∉ F ∧ G.Adj a b) x y)) :
    ∃ k, k ≤ ⌈(Fintype.card V : ℚ) / r⌉₊ ∧ 2 ≤ k ∧ ∃ c : Fin k → V, Function.Injective c ∧
      (∀ i, G.Adj (c i) (c (finRotate k i))) ∧ v ∈ Set.range c := by
  let K := ⌈(Fintype.card V : ℚ) / r⌉₊
  have hq : (Fintype.card V : ℚ) / r ≤ (K : ℚ) := Nat.le_ceil _
  have hmul : Fintype.card V ≤ K*r := by
    exact_mod_cast (div_le_iff₀ (show (0 : ℚ) < r by exact_mod_cast hr)).mp hq
  have hp := (outdegree_lt_card G hloop v)
  have hK : 0 < K := by
    by_contra! h
    have h0 : K = 0 := by omega
    rw [h0, Nat.zero_mul] at hmul
    omega
  let t := K - 1
  have ht : t+1 = K := by dsimp [t]; omega
  have hbudget : Fintype.card V ≤ outdegree G v + t*r := by
    rw [← ht, Nat.succ_mul] at hmul
    omega
  have hc := rooted_cycle_of_connectivity_budget G hloop v r t (by omega) hconn hbudget
  rw [ht] at hc
  exact hc

end OMA.CHConnectivity


namespace OMA.CHAtom

open OMA.S_opg_caccetta_haggkvist_conjecture

variable {V : Type} [Fintype V]

/- The set function B denotes the exterior out-neighborhood. Its exact
membership condition is supplied to the lemmas that use adjacency. -/
variable {G : Digraph V} {B : Finset V → Finset V}
variable (hB : ∀ {S : Finset V} {y : V}, y ∈ B S ↔ y ∉ S ∧ ∃ x ∈ S, G.Adj x y)

omit [Fintype V] in
/-- A given small-boundary region contains an atom. Any vertex outside the
region with no incoming arc from it remains exterior to the atom and its exits. -/
theorem exists_atom_subset (B : Finset V → Finset V) (r : ℕ) (T : Finset V)
    (hT : T.Nonempty) (hcut : (B T).card < r) :
    ∃ S ⊆ T, S.Nonempty ∧ (B S).card < r ∧
      ∀ U : Finset V, U.Nonempty → U ⊂ S → r ≤ (B U).card := by
  classical
  let C := T.powerset.filter (fun U => U.Nonempty ∧ (B U).card < r)
  have ht : T ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl T), hT, hcut⟩
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image C Finset.card ⟨T, ht⟩
  obtain ⟨hsub, hne, hbound⟩ := Finset.mem_filter.mp hS
  refine ⟨S, Finset.mem_powerset.mp hsub, hne, hbound, ?_⟩
  intro U hU hUS
  by_contra! hlt
  have hUC : U ∈ C := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (hUS.subset.trans (Finset.mem_powerset.mp hsub)), hU, hlt⟩
  exact (Finset.card_lt_card hUS).not_ge (hmin U hUC)

include hB

omit [Fintype V] in
/-- The subgraph induced by an atom is strongly connected: no nonempty proper
subset can send all its outgoing arcs outside the atom. -/
theorem atom_induced_reachable {r : ℕ} {S : Finset V}
    (hS : S.Nonempty ∧ (B S).card < r ∧
      ∀ U : Finset V, U.Nonempty → U ⊂ S → r ≤ (B U).card) (x y : {u // u ∈ S}) :
    Relation.ReflTransGen (fun a b : {u // u ∈ S} => G.Adj a.1 b.1) x y := by
  classical
  let R := fun u : V => ∃ v : {u // u ∈ S}, v.val = u ∧
    Relation.ReflTransGen (fun a b : {u // u ∈ S} => G.Adj a.1 b.1) x v
  let U := S.filter R
  have hxu : x.1 ∈ U := Finset.mem_filter.mpr ⟨x.2, x, rfl, .refl⟩
  have hyu : y.1 ∈ U := by
    by_contra h
    have hsub : U ⊂ S := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.filter_subset _ _, fun eq => h (eq.ge y.2)⟩
    have hex : B U ⊆ B S := by
      intro w hw
      obtain ⟨hwu, z, hz, e⟩ := hB.mp hw
      obtain ⟨hzs, v, hv, path⟩ := Finset.mem_filter.mp hz
      refine hB.mpr ⟨?_, z, hzs, e⟩
      intro hws
      have evw : G.Adj v.val w := by simpa only [hv] using e
      have hpath : Relation.ReflTransGen (fun a b : S => G.Adj a.val b.val) x ⟨w, hws⟩ :=
        path.tail evw
      exact hwu (Finset.mem_filter.mpr ⟨hws, ⟨w, hws⟩, rfl, hpath⟩)
    exact (hS.2.2 U ⟨x.1, hxu⟩ hsub).not_gt
      (lt_of_le_of_lt (Finset.card_le_card hex) hS.2.1)
  obtain ⟨v, hv, path⟩ := (Finset.mem_filter.mp hyu).2
  have hvy : v = y := Subtype.ext hv
  simpa only [hvy] using path

open scoped Classical in
/-- Deleting one vertex from an atom exposes that vertex and preserves every old
exit. Consequently the atom has exactly r − 1 exits. -/
theorem atom_erase_exits [DecidableRel G.Adj] {r : ℕ} {S : Finset V}
    (hS : S.Nonempty ∧ (B S).card < r ∧
      ∀ U : Finset V, U.Nonempty → U ⊂ S → r ≤ (B U).card)
    (hloop : ∀ x, ¬ G.Adj x x) (hdegree : ∀ x, r ≤ outdegree G x)
    (x : V) (hx : x ∈ S) :
    (B S).card + 1 = r ∧ B (S.erase x) = insert x (B S) := by
  classical
  have hlt : (B S).card < (Finset.univ.filter (G.Adj x)).card :=
    hS.2.1.trans_le (hdegree x)
  obtain ⟨y, hy, hyo⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hxy := (Finset.mem_filter.mp hy).2
  have hys : y ∈ S := by
    by_contra hn
    exact hyo (hB.mpr ⟨hn, x, hx, hxy⟩)
  have hyx : y ≠ x := by
    rintro rfl
    exact hloop _ hxy
  have hne : (S.erase x).Nonempty := ⟨y, Finset.mem_erase.mpr ⟨hyx, hys⟩⟩
  have he := hS.2.2 _ hne (Finset.erase_ssubset hx)
  have hi : B (S.erase x) ⊆ insert x (B S) := by
    intro w hw
    obtain ⟨hwe, v, hv, e⟩ := hB.mp hw
    by_cases h : w = x
    · exact Finset.mem_insert.mpr (Or.inl h)
    · refine Finset.mem_insert.mpr (Or.inr (hB.mpr ⟨?_, v, (Finset.mem_erase.mp hv).2, e⟩))
      exact fun hws => hwe (Finset.mem_erase.mpr ⟨h, hws⟩)
  have hxout : x ∉ B S := fun h => (hB.mp h).1 hx
  have hcard := Finset.card_le_card hi
  have hci := Finset.card_insert_of_notMem hxout
  rw [hci] at hcard
  have hlt' := hS.2.1
  exact ⟨by omega, Finset.eq_of_subset_of_card_le hi (by rw [hci]; omega)⟩

/-- Every exit receives arcs from two distinct vertices of the atom. -/
theorem atom_two_predecessors [DecidableRel G.Adj] {r : ℕ} {S : Finset V}
    (hS : S.Nonempty ∧ (B S).card < r ∧
      ∀ U : Finset V, U.Nonempty → U ⊂ S → r ≤ (B U).card)
    (hloop : ∀ x, ¬ G.Adj x x) (hdegree : ∀ x, r ≤ outdegree G x)
    {z : V} (hz : z ∈ B S) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ G.Adj x z ∧ G.Adj y z := by
  classical
  obtain ⟨_, x, hx, ex⟩ := hB.mp hz
  have hz' : z ∈ B (S.erase x) := by
    rw [(atom_erase_exits hB hS hloop hdegree x hx).2]
    exact Finset.mem_insert_of_mem hz
  obtain ⟨_, y, hy, ey⟩ := hB.mp hz'
  obtain ⟨hne, hys⟩ := Finset.mem_erase.mp hy
  exact ⟨x, hx, y, hys, Ne.symm hne, ex, ey⟩

omit [Fintype V] in
open scoped Classical in
/-- Strict Hall expansion until the whole atom is exhausted. This does not
require a degree or looplessness assumption. -/
theorem atom_feeders_card {r : ℕ} {S F : Finset V} (hA : S.Nonempty ∧ (B S).card < r ∧
      ∀ U : Finset V, U.Nonempty → U ⊂ S → r ≤ (B U).card)
    (hF : F.Nonempty) (hFS : F ⊆ B S) :
    min S.card (F.card + 1) ≤ (S.filter (fun x => ∃ z ∈ F, G.Adj x z)).card := by
  classical
  let P := S.filter (fun x => ∃ z ∈ F, G.Adj x z)
  by_cases h : S ⊆ P
  · exact (min_le_left _ _).trans (Finset.card_le_card h)
  obtain ⟨f, hf⟩ := hF
  obtain ⟨_, t, hts, htf⟩ := hB.mp (hFS hf)
  have htp : t ∈ P := Finset.mem_filter.mpr ⟨hts, f, hf, htf⟩
  have hprop : S \ P ⊂ S := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.sdiff_subset, fun eq => (Finset.mem_sdiff.mp (eq.ge hts : t ∈ S \ P)).2 htp⟩
  have hsmall := hA.2.2 (S \ P) (Finset.sdiff_nonempty.mpr h) hprop
  have hcontain : B (S \ P) ⊆ P ∪ (B S \ F) := by
    intro y hy
    obtain ⟨hyn, u, hu, huy⟩ := hB.mp hy
    obtain ⟨hus, hup⟩ := Finset.mem_sdiff.mp hu
    by_cases hys : y ∈ S
    · exact Finset.mem_union_left _ (by
        by_contra hyP
        exact hyn (Finset.mem_sdiff.mpr ⟨hys, hyP⟩))
    · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨hB.mpr ⟨hys, u, hus, huy⟩, ?_⟩)
      intro hyF
      exact hup (Finset.mem_filter.mpr ⟨hus, y, hyF, huy⟩)
  have hbound := hsmall.trans ((Finset.card_le_card hcontain).trans (Finset.card_union_le _ _))
  have hcount := Finset.card_sdiff_add_card_eq_card hFS
  have hcut := hA.2.1
  change min S.card (F.card + 1) ≤ P.card
  omega

omit [Fintype V] in
open scoped Classical in
/-- An arbitrary set of fewer than |S| exits admits distinct incoming
representatives in the atom, even after one prescribed vertex is forbidden. -/
theorem atom_match_exits_avoiding_one {r : ℕ} {S F : Finset V}
    (hA : S.Nonempty ∧ (B S).card < r ∧
      ∀ U : Finset V, U.Nonempty → U ⊂ S → r ≤ (B U).card)
    (hFS : F ⊆ B S) (hsize : F.card < S.card) (v : V) :
    ∃ f : {z // z ∈ F} → V, Function.Injective f ∧
      ∀ z, f z ∈ S ∧ f z ≠ v ∧ G.Adj (f z) z.1 := by
  classical
  let t := fun z : {z // z ∈ F} => (S.filter (fun x => G.Adj x z.val)).erase v
  have hall (A : Finset {z // z ∈ F}) : A.card ≤ (A.biUnion t).card := by
    by_cases hAn : A.Nonempty
    · let Z := A.image Subtype.val
      have hZF : Z ⊆ F := by
        intro z hz
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
        exact a.2
      have hcard : Z.card = A.card := Finset.card_image_of_injective _ Subtype.val_injective
      have hstrict := atom_feeders_card hB hA (hAn.image Subtype.val) (hZF.trans hFS)
      have hZS := (Finset.card_le_card hZF).trans_lt hsize
      change min S.card (Z.card+1) ≤ (S.filter (fun x => ∃ z ∈ Z, G.Adj x z)).card at hstrict
      rw [min_eq_right (by omega)] at hstrict
      have hsub : (S.filter (fun x => ∃ z ∈ Z, G.Adj x z)).erase v ⊆ A.biUnion t := by
        intro x hx
        obtain ⟨hxv, hxp⟩ := Finset.mem_erase.mp hx
        obtain ⟨hxs, z, hz, e⟩ := Finset.mem_filter.mp hxp
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_erase.mpr ⟨hxv, Finset.mem_filter.mpr ⟨hxs, e⟩⟩⟩
      have hle := Finset.card_le_card hsub
      by_cases hv : v ∈ S.filter (fun x => ∃ z ∈ Z, G.Adj x z)
      · have := Finset.card_erase_add_one hv
        omega
      · rw [Finset.erase_eq_of_notMem hv] at hle
        omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hAn]
  obtain ⟨f, hfi, hf⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  refine ⟨f, hfi, fun z => ?_⟩
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp (hf z)
  obtain ⟨hs, he⟩ := Finset.mem_filter.mp hmem
  exact ⟨hs, hne, he⟩

/-- A nonempty region with fewer than r exits already contains a cycle of
length at most its own cardinality, with every vertex of the cycle in the region. -/
theorem region_cycle [DecidableRel G.Adj] {r : ℕ} {S : Finset V}
    (hloop : ∀ x, ¬ G.Adj x x) (hd : ∀ x, r ≤ outdegree G x)
    (hs : S.Nonempty) (hcut : (B S).card < r) :
    ∃ k, k ≤ S.card ∧ 2 ≤ k ∧ ∃ c : Fin k → V, Function.Injective c ∧
      (∀ i, G.Adj (c i) (c (finRotate k i))) ∧ ∀ i, c i ∈ S := by
  classical
  let D : Digraph S := ⟨fun x y => G.Adj x.1 y.1⟩
  obtain ⟨s, hsm⟩ := hs
  let : Nonempty S := ⟨⟨s, hsm⟩⟩
  have hpos (x : S) : 1 ≤ outdegree D x := by
    have hlt : (B S).card < (Finset.univ.filter (G.Adj x.1)).card :=
      hcut.trans_le (hd x.1)
    obtain ⟨y, hy, hn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have exy := (Finset.mem_filter.mp hy).2
    have hys : y ∈ S := by
      by_contra h
      exact hn (hB.mpr ⟨h, x.1, x.2, exy⟩)
    exact Finset.card_pos.mpr ⟨⟨y, hys⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, exy⟩⟩
  obtain ⟨k, hk, ht, c, hi, he⟩ :=
    OMA.R_opg_caccetta_haggkvist_conjecture_R1.cycle_of_min_outdegree_pos D (fun x => hloop x.1) hpos
  exact ⟨k, by simpa using hk, ht, fun i => (c i).1, Subtype.val_injective.comp hi,
    he, fun i => (c i).2⟩

end OMA.CHAtom


namespace OMA.CHCore

open OMA.S_opg_caccetta_haggkvist_conjecture

variable {V : Type} [Fintype V]

/-- A finite nonempty digraph contains a nonempty sink component.  Choosing
a smallest nonempty out-closed set avoids a separate condensation graph. -/
theorem exists_sink_component [Nonempty V] (G : Digraph V) :
    ∃ S : Finset V, S.Nonempty ∧ (∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S) ∧
      ∀ x y : S, Relation.ReflTransGen (fun a b : S => G.Adj a.1 b.1) x y := by
  classical
  let family := (Finset.univ : Finset (Finset V)).filter fun S =>
    S.Nonempty ∧ (∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S)
  have hf : (Finset.univ : Finset V) ∈ family :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.univ_nonempty, fun _ _ _ _ => Finset.mem_univ _⟩
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image family Finset.card ⟨_, hf⟩
  obtain ⟨hne, hclosed⟩ := (Finset.mem_filter.mp hS).2
  refine ⟨S, hne, hclosed, ?_⟩
  intro x y
  let A := (Finset.univ : Finset S).filter fun z =>
    Relation.ReflTransGen (fun a b : S => G.Adj a.1 b.1) x z
  let e : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let T := A.map e
  have hmem (z : S) : e z ∈ T ↔ Relation.ReflTransGen (fun a b : S => G.Adj a.1 b.1) x z := by
    simp [T, A]
  have hsub : T ⊆ S := by
    intro z hz
    obtain ⟨z', _, rfl⟩ := Finset.mem_map.mp hz
    exact z'.2
  have hT : ∀ u ∈ T, ∀ v, G.Adj u v → v ∈ T := by
    intro u hu v huv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hu
    let w : S := ⟨v, hclosed _ z.2 _ huv⟩
    exact (hmem w).mpr (((Finset.mem_filter.mp hz).2).tail (show G.Adj z.1 w.1 from huv))
  have hTf : T ∈ family := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨_, (hmem x).mpr .refl⟩, hT⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (hmin _ hTf)
  apply (hmem y).mp
  rw [heq]
  exact y.2

/-- Restriction to an out-closed set preserves every individual outdegree. -/
theorem outdegree_induced_of_closed (G : Digraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S) (x : S) :
    @outdegree S _ ⟨fun a b => G.Adj a.1 b.1⟩ (fun a b => ‹DecidableRel G.Adj› a.1 b.1) x =
      outdegree G x.1 := by
  classical
  unfold outdegree
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro y hy
    have hadj := (Finset.mem_filter.mp hy).2
    exact ⟨⟨y, hS _ x.2 _ hadj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩, rfl⟩

/-- Thin each out-neighborhood independently to exactly its prescribed size. -/
theorem exists_thinning (G : Digraph V) [DecidableRel G.Adj] (d : V → ℕ)
    (hd : ∀ v, d v ≤ outdegree G v) :
    ∃ (D : Digraph V) (decD : DecidableRel D.Adj),
      (∀ x y, D.Adj x y → G.Adj x y) ∧ ∀ x, @outdegree V _ D decD x = d x := by
  classical
  choose N hsub hcard using fun x => Finset.exists_subset_card_eq (hd x)
  let D : Digraph V := ⟨fun x y => y ∈ N x⟩
  let : DecidableRel D.Adj := fun x y => inferInstanceAs (Decidable (y ∈ N x))
  refine ⟨D, inferInstance, ?_, ?_⟩
  · intro x y h
    exact (Finset.mem_filter.mp (hsub x h)).2
  · intro x
    simpa [outdegree, D] using hcard x

/-- Every digraph with minimum outdegree at least r contains a strongly
connected r-outregular subgraph. Its edges and vertices embed into the host. -/
theorem exists_strong_regular_core [Nonempty V] (G : Digraph V) [DecidableRel G.Adj]
    (r : ℕ) (hd : ∀ x, r ≤ outdegree G x) :
    ∃ (S : Finset V) (_ : Nonempty S) (D : Digraph S) (decD : DecidableRel D.Adj),
      (∀ x y, Relation.ReflTransGen D.Adj x y) ∧ (∀ x, @outdegree S _ D decD x = r) ∧
      ∀ x y, D.Adj x y → G.Adj x.1 y.1 := by
  obtain ⟨B, hB, hBG, hdeg⟩ := exists_thinning G (fun _ => r) hd
  let : DecidableRel B.Adj := hB
  obtain ⟨S, hS, hcl, hstrong⟩ := exists_sink_component B
  refine ⟨S, hS.to_subtype, ⟨fun x y => B.Adj x.1 y.1⟩, fun x y => hB x.1 y.1, hstrong, ?_, ?_⟩
  · intro x
    exact (outdegree_induced_of_closed B S hcl x).trans (hdeg x.1)
  · intro x y hxy
    exact hBG _ _ hxy

omit [Fintype V] in
/-- Injectively mapping the arcs preserves every length of a simple cycle. -/
theorem map_cycle {W : Type} {D : Digraph W} {G : Digraph V} (e : W ↪ V)
    (he : ∀ x y, D.Adj x y → G.Adj (e x) (e y)) {k : ℕ}
    (hc : HasDirectedCycleOfLength D k) : HasDirectedCycleOfLength G k := by
  obtain ⟨h, c, hi, ha⟩ := hc
  exact ⟨h, e ∘ c, e.injective.comp hi, fun i => he _ _ (ha i)⟩

/-- The numerical CH bound is monotone under embeddings of subgraphs. -/
theorem lift_short_cycle {W : Type} [Fintype W] {D : Digraph W} {G : Digraph V}
    (e : W ↪ V) (he : ∀ x y, D.Adj x y → G.Adj (e x) (e y)) (r : ℕ)
    (h : ∃ k, k ≤ ⌈(Fintype.card W : ℚ) / r⌉₊ ∧ HasDirectedCycleOfLength D k) :
    ∃ k, k ≤ ⌈(Fintype.card V : ℚ) / r⌉₊ ∧ HasDirectedCycleOfLength G k := by
  obtain ⟨k, hk, hc⟩ := h
  have hcard : (Fintype.card W : ℚ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_le_of_injective e e.injective
  exact ⟨k, hk.trans (Nat.ceil_le_ceil (div_le_div_of_nonneg_right hcard (by positivity))),
    map_cycle e he hc⟩

end OMA.CHCore


namespace OMA.CHReciprocity

open OMA.S_opg_caccetta_haggkvist_conjecture

variable {V : Type} [Fintype V]

/-- The total indegree equals the total outdegree, so some vertex has at
least r predecessors when every vertex has at least r successors. -/
theorem exists_indegree_ge [Nonempty V] (G : Digraph V) [DecidableRel G.Adj]
    (r : ℕ) (hdeg : ∀ x, r ≤ outdegree G x) :
    ∃ x : V, r ≤ (Finset.univ.filter fun y => G.Adj y x).card := by
  classical
  by_contra! h
  exact (lt_irrefl _) (Finset.card_nsmul_lt_card_nsmul_of_le_of_lt G.Adj
    (s := Finset.univ) (t := Finset.univ) Finset.univ_nonempty
    (fun x _ => hdeg x) (fun x _ => h x))

/-- The reciprocal neighbours at some vertex cover the excess of twice the
minimum outdegree over the other available vertices. -/
theorem exists_many_reciprocal [Nonempty V] (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (r : ℕ) (hdeg : ∀ x, r ≤ outdegree G x) :
    ∃ x : V, 2*r + 1 ≤ Fintype.card V +
      (Finset.univ.filter fun y => G.Adj x y ∧ G.Adj y x).card := by
  classical
  obtain ⟨x, hx⟩ := exists_indegree_ge G r hdeg
  let A := Finset.univ.filter fun y => G.Adj x y
  let B := Finset.univ.filter fun y => G.Adj y x
  have hu : A ∪ B ⊆ Finset.univ.erase x := by
    intro y hy
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    rcases Finset.mem_union.mp hy with h | h <;> exact hloop _ (Finset.mem_filter.mp h).2
  have hi : A ∩ B = Finset.univ.filter (fun y => G.Adj x y ∧ G.Adj y x) := by
    ext; simp [A, B]
  have hab := Finset.card_union_add_card_inter A B
  have hm := Finset.card_le_card hu
  rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ] at hm
  rw [hi] at hab
  have ha : r ≤ A.card := hdeg x
  change r ≤ B.card at hx
  exact ⟨x, by have := Fintype.card_pos (α := V); omega⟩

/-- Half the vertices as outgoing neighbours force a directed two-cycle. -/
theorem digon_of_double_degree [Nonempty V] (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (r : ℕ) (hdeg : ∀ x, r ≤ outdegree G x)
    (hsize : Fintype.card V ≤ 2*r) : HasDirectedCycleOfLength G 2 := by
  classical
  obtain ⟨x, hx⟩ := exists_many_reciprocal G hloop r hdeg
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter
    (fun y => G.Adj x y ∧ G.Adj y x)).card by omega)
  obtain ⟨hxy, hyx⟩ := (Finset.mem_filter.mp hy).2
  have hne : x ≠ y := by rintro rfl; exact hloop _ hxy
  let c : Fin 2 → V := ![x, y]
  refine ⟨by decide, c, ?_, ?_⟩
  · intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [c]
  · intro i
    fin_cases i
    · exact hxy
    · exact hyx

/-- In a finite r-outregular digraph, a global lower bound of r on indegrees
forces every indegree to equal r. -/
theorem indegree_eq_of_regular_lower (G : Digraph V) [DecidableRel G.Adj]
    (r : ℕ) (hout : ∀ x, outdegree G x = r)
    (hin : ∀ x, r ≤ (Finset.univ.filter (fun y => G.Adj y x)).card) (x : V) :
    (Finset.univ.filter (fun y => G.Adj y x)).card = r := by
  classical
  have hs : (∑ v : V, (Finset.univ.filter (fun y => G.Adj y v)).card) =
      ∑ _v : V, r := by
    calc
      _ = ∑ v : V, outdegree G v :=
        (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj).symm
      _ = _ := by simp_rw [hout]
  refine le_antisymm ?_ (hin x)
  by_contra! h
  exact (ne_of_lt (Finset.sum_lt_sum (fun v _ => hin v) ⟨x, Finset.mem_univ _, h⟩)) hs.symm

end OMA.CHReciprocity

namespace OMA.CHObstruction

open OMA.S_opg_caccetta_haggkvist_conjecture
open OMA.R_opg_caccetta_haggkvist_conjecture_R1
open OMA.CHAtom
open OMA.CHConnectivity

variable {V : Type} [Fintype V]

/-- A root cut yields a minimal outward-deficient region separated from the
root. The root is neither in the region nor one of its exits. -/
theorem region_away_of_cut (G : Digraph V) (v x : V) (F : Finset V)
    (hx : x ∉ F) (hv : v ∉ F)
    (hcut : ¬ Relation.ReflTransGen (fun a b => a ∉ F ∧ b ∉ F ∧ G.Adj a b) x v)
    (B : Finset V → Finset V)
    (hB : ∀ {A : Finset V} {y : V}, y ∈ B A ↔ y ∉ A ∧ ∃ a ∈ A, G.Adj a y)
    {r : ℕ} (hF : F.card < r) :
    ∃ S : Finset V, v ∉ S ∧ v ∉ B S ∧ S.Nonempty ∧ (B S).card < r ∧
      ∀ U : Finset V, U.Nonempty → U ⊂ S → r ≤ (B U).card := by
  classical
  let R (a b : V) := a ∉ F ∧ b ∉ F ∧ G.Adj a b
  let T := Finset.univ.filter (fun z => z ∉ F ∧ Relation.ReflTransGen R x z)
  have hT : T.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, .refl⟩⟩
  have outside : B T ⊆ F := by
    intro z hz
    obtain ⟨hne, y, hy, e⟩ := hB.mp hz
    obtain ⟨hyf, hp⟩ := (Finset.mem_filter.mp hy).2
    by_contra hzf
    exact hne (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzf, hp.tail ⟨hyf, hzf, e⟩⟩)
  have hvt : v ∉ T := fun h => hcut (Finset.mem_filter.mp h).2.2
  obtain ⟨S, hst, hs, hc, hmin⟩ := exists_atom_subset B r T hT
    ((Finset.card_le_card outside).trans_lt hF)
  refine ⟨S, fun h => hvt (hst h), ?_, hs, hc, hmin⟩
  intro h
  obtain ⟨_, y, hy, e⟩ := hB.mp h
  exact hv (outside (hB.mpr ⟨hvt, y, hst hy, e⟩))

open scoped Classical in
/-- In the absence of the CH cycle, *every* root misses a strongly connected
minimal region and all its exits. The region has more than the cycle budget
many vertices and exactly r-1 exits. -/
theorem atom_away_from_each_root (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (r : ℕ) (hr : 0 < r) (hd : ∀ x, r ≤ outdegree G x)
    (K : ℕ) (hbudget : Fintype.card V ≤ K*r)
    (hn : ¬ ∃ k ≤ K, HasDirectedCycleOfLength G k) (v : V) :
    ∃ S E : Finset V, K < S.card ∧ E.card + 1 = r ∧ v ∉ S ∧ v ∉ E ∧
      (∀ y, y ∈ E ↔ y ∉ S ∧ ∃ x ∈ S, G.Adj x y) ∧
      (∀ U : Finset V, U.Nonempty → U ⊂ S →
        r ≤ (Finset.univ.filter (fun y => y ∉ U ∧ ∃ x ∈ U, G.Adj x y)).card) ∧
      ∀ x y : S, Relation.ReflTransGen (fun a b : S => G.Adj a.1 b.1) x y := by
  classical
  have hnon : 0 < K := by
    by_contra! hh
    rw [show K = 0 by omega, Nat.zero_mul] at hbudget
    have hc := Fintype.card_pos_iff.mpr (show Nonempty V from ⟨v⟩)
    omega
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnon.ne'
  rw [Nat.succ_mul] at hbudget
  rcases rooted_cycle_or_small_separator G hloop v r t (by have := hd v; omega) with
    ⟨k, hk, h2, c, hi, he, _⟩ | ⟨F, hF, hv, hsep⟩
  · exact (hn ⟨k, hk, h2, c, hi, he⟩).elim
  have hpos : 0 < (Finset.univ.filter (G.Adj v)).card := hr.trans_le (hd v)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  obtain ⟨hxf, hxc⟩ := hsep x (Finset.mem_filter.mp hx).2
  let B (U : Finset V) := Finset.univ.filter (fun y => y ∉ U ∧ ∃ a ∈ U, G.Adj a y)
  have memB {U : Finset V} {y : V} : y ∈ B U ↔ y ∉ U ∧ ∃ a ∈ U, G.Adj a y := by simp [B]
  obtain ⟨S, hvS, hvE, hs, hcut, hmin⟩ := region_away_of_cut G v x F hxf hv hxc B memB hF
  have hAtom := And.intro hs (And.intro hcut hmin)
  obtain ⟨z, hz⟩ := hs
  have he := (atom_erase_exits memB hAtom hloop hd z hz).1
  refine ⟨S, B S, ?_, he, hvS, hvE, fun _ => memB, hmin, atom_induced_reachable memB hAtom⟩
  by_contra! hcard
  obtain ⟨k, hk, htwo, c, hi, hadj, _⟩ := region_cycle memB hloop hd ⟨z, hz⟩ hcut
  exact hn ⟨k, hk.trans hcard, htwo, c, hi, hadj⟩

end OMA.CHObstruction


namespace OMA.CHChord

open OMA.S_opg_caccetta_haggkvist_conjecture
open OMA.R_opg_caccetta_haggkvist_conjecture_R1

open scoped Fin.NatCast in
/-- A chord from i to j closes the forward segment from j to i. On a shortest
cycle that segment must use every other arc, so j is the successor of i. -/
theorem shortest_cycle_only_successor {V : Type} (G : Digraph V)
    (hloop : ∀ x, ¬ G.Adj x x) (k : ℕ) (hk : 2 ≤ k)
    (c : Fin k → V) (he : ∀ i, G.Adj (c i) (c (finRotate k i)))
    (hshort : ∀ l, HasDirectedCycleOfLength G l → k ≤ l)
    {i j : Fin k} (chord : G.Adj (c i) (c j)) : j = finRotate k i := by
  classical
  let : NeZero k := ⟨by omega⟩
  let d := (i - j).val
  have hc : (d : Fin k) = i - j := by
    apply Fin.ext
    simp [d]
  have hji : j + (d : Fin k) = i := by rw [hc, add_comm, sub_add_cancel]
  let f (t : ℕ) := if t = d+1 then c j else c (j + (t : Fin k))
  have hzero : f 0 = c j := by simp [f]
  have hedge (t : ℕ) (ht : t < d+1) : G.Adj (f t) (f (t+1)) := by
    by_cases h : t = d
    · subst t
      simpa [f, hji] using chord
    · have hlt : t ≠ d+1 := by omega
      have hlt' : t+1 ≠ d+1 := by omega
      simpa only [f, if_neg hlt, if_neg hlt', Nat.cast_add, Nat.cast_one, ← add_assoc,
        finRotate_apply] using he (j + (t : Fin k))
  obtain ⟨l, hl, hcycle⟩ := cycle_of_closed_walk G hloop (d+1) f (by omega)
    (by simp [f, hzero]) hedge
  have hdk : d < k := (i-j).isLt
  have hlen := hshort l hcycle
  have heq : d+1 = k := by omega
  have hsum : (d : Fin k) + 1 = 0 := by
    rw [← Nat.cast_one (R := Fin k), ← Nat.cast_add, heq, Fin.natCast_self]
  rw [finRotate_apply, ← hji, add_assoc, hsum, add_zero]

variable {V : Type} [Fintype V]

open scoped Classical in
/-- A short-boundary region contains a chordless induced cycle. The vertex
set exceeds K when the ambient graph has girth greater than K. -/
theorem chordless_region (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (S E : Finset V) (hs : S.Nonempty)
    (hboundary : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S ∨ y ∈ E)
    (r : ℕ) (hcut : E.card < r) (hmin : ∀ x, r ≤ outdegree G x)
    (K : ℕ) (hn : ¬ ∃ k ≤ K, HasDirectedCycleOfLength G k) :
    ∃ C ⊆ S, K < C.card ∧ ∀ x ∈ C, (C.filter (G.Adj x)).card ≤ 1 := by
  classical
  let D : Digraph S := ⟨fun x y => G.Adj x.1 y.1⟩
  obtain ⟨s, hsm⟩ := hs
  let : Nonempty S := ⟨⟨s, hsm⟩⟩
  have hpos (x : S) : 1 ≤ outdegree D x := by
    have hlt : E.card < (Finset.univ.filter (G.Adj x.1)).card := hcut.trans_le (hmin x.1)
    obtain ⟨y, hy, hye⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have e := (Finset.mem_filter.mp hy).2
    have hys := (hboundary x.1 x.2 y e).resolve_right hye
    exact Finset.card_pos.mpr ⟨⟨y, hys⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e⟩⟩
  have hl : ∀ x : S, ¬ D.Adj x x := fun x => hloop x.1
  obtain ⟨t, _, ht⟩ := cycle_of_min_outdegree_pos D hl hpos
  have hex : ∃ k, HasDirectedCycleOfLength D k := ⟨t, ht⟩
  let k := Nat.find hex
  obtain ⟨hk, c, hi, he⟩ := Nat.find_spec hex
  let a : Fin k → V := fun i => (c i).1
  have hai : Function.Injective a := Subtype.val_injective.comp hi
  let C := Finset.univ.image a
  have hcard : C.card = k := by simp [C, Finset.card_image_of_injective _ hai]
  refine ⟨C, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (c i).2
  · rw [hcard]
    by_contra! h
    exact hn ⟨k, h, hk, a, hai, he⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    have hsub : C.filter (G.Adj (a i)) ⊆ {a (finRotate k i)} := by
      intro y hy
      obtain ⟨hyC, hxy⟩ := Finset.mem_filter.mp hy
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyC
      exact Finset.mem_singleton.mpr (congrArg a (shortest_cycle_only_successor
        D hl k hk c he (fun _ h => Nat.find_min' hex h) hxy))
    exact (Finset.card_le_card hsub).trans (by simp)


/-- A region with fewer than r exits consumes a definite number of vertices
when the shortest cycle is long. Count the arcs from a shortest chordless
cycle to the other vertices of the region and its exits. -/
theorem region_incidence_bound (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (S E : Finset V) (hs : S.Nonempty)
    (hboundary : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S ∨ y ∈ E)
    (r d K : ℕ) (hcut : E.card < r) (hmin : ∀ x, r ≤ outdegree G x)
    (hmax : ∀ y, (Finset.univ.filter (fun x => G.Adj x y)).card ≤ d)
    (hn : ¬ ∃ k ≤ K, HasDirectedCycleOfLength G k) :
    (r - 1 + d) * (K + 1) ≤ d * (S.card + E.card) := by
  classical
  obtain ⟨C, hCS, hlong, hchord⟩ := chordless_region G hloop S E hs hboundary r hcut hmin K hn
  let T := (S \ C) ∪ E
  have hout (x : V) (hx : x ∈ C) : r - 1 ≤ (T.filter (G.Adj x)).card := by
    have hcover : Finset.univ.filter (G.Adj x) ⊆ C.filter (G.Adj x) ∪ T.filter (G.Adj x) := by
      intro y hy
      have hxy := (Finset.mem_filter.mp hy).2
      by_cases hcy : y ∈ C
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hcy, hxy⟩)
      · apply Finset.mem_union_right _
        apply Finset.mem_filter.mpr
        refine ⟨?_, hxy⟩
        rcases hboundary x (hCS hx) y hxy with hsy | hey
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hsy, hcy⟩)
        · exact Finset.mem_union_right _ hey
    have hdeg : r ≤ (Finset.univ.filter (G.Adj x)).card := hmin x
    have hu := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have hch := hchord x hx
    omega
  have hin (y : V) (_hy : y ∈ T) : (C.filter (fun x => G.Adj x y)).card ≤ d := by
    apply le_trans (Finset.card_le_card ?_) (hmax y)
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  have hcount : C.card * (r - 1) ≤ T.card * d := Finset.card_mul_le_card_mul G.Adj hout hin
  have htotal : T.card + C.card ≤ S.card + E.card := by
    have he : T.card ≤ (S \ C).card + E.card := Finset.card_union_le _ _
    have hsc := Finset.card_sdiff_add_card_eq_card hCS
    omega
  calc
    (r - 1 + d) * (K + 1) ≤ (r - 1 + d) * C.card := Nat.mul_le_mul_left _ hlong
    _ = C.card * (r - 1) + C.card * d := by rw [Nat.mul_comm, Nat.mul_add]
    _ ≤ T.card * d + C.card * d := Nat.add_le_add_right hcount _
    _ = d * (T.card + C.card) := by rw [← Nat.add_mul, Nat.mul_comm]
    _ ≤ d * (S.card + E.card) := Nat.mul_le_mul_left _ htotal

end OMA.CHChord


namespace OMA.CHReverse

open OMA.S_opg_caccetta_haggkvist_conjecture

/-- Reversal preserves each simple cycle length. Negation on the cyclic index
set reverses the traversal and retains injectivity. -/
theorem reverse_cycle {V : Type} {G D : Digraph V}
    (hrev : ∀ x y, D.Adj x y ↔ G.Adj y x) {k : ℕ}
    (hc : HasDirectedCycleOfLength D k) : HasDirectedCycleOfLength G k := by
  obtain ⟨hk, c, hi, hadj⟩ := hc
  let : NeZero k := ⟨by omega⟩
  refine ⟨hk, fun i => c (-i), hi.comp neg_injective, ?_⟩
  intro i
  have h := (hrev _ _).mp (hadj (-(finRotate k i)))
  have he : finRotate k (-(finRotate k i)) = -i := by
    simp only [finRotate_apply, neg_add_rev]
    abel
  rwa [he] at h

/-- The same forbidden exit set separates the complementary region in the
reversed digraph. No arcs from S to its exterior beyond E are permitted. -/
theorem complement_boundary_subset {V : Type} {G : Digraph V} (S E R : Finset V)
    (hR : ∀ x, x ∈ R ↔ x ∉ S ∧ x ∉ E)
    (hboundary : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S ∨ y ∈ E) :
    ∀ x ∈ R, ∀ y, G.Adj y x → y ∈ R ∨ y ∈ E := by
  intro x hx y hyx
  by_cases hy : y ∈ E
  · exact Or.inr hy
  apply Or.inl <| (hR y).mpr ⟨?_, hy⟩
  intro hys
  exact (hboundary y hys x hyx).elim ((hR x).mp hx).1 ((hR x).mp hx).2

end OMA.CHReverse

namespace OMA.CHRegular

open OMA.S_opg_caccetta_haggkvist_conjecture
open OMA.CHObstruction OMA.CHReverse OMA.CHChord

variable {V : Type} [Fintype V]

open scoped Classical in
/-- Apply the shortest-cycle incidence count on both sides of a directed
separator in an in- and outregular graph. Each side may send its outgoing
arcs to the separator, once the second side is read in reverse. -/
theorem paired_region_incidence (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (S E : Finset V) (hs : S.Nonempty)
    (hdis : Disjoint S E) (hv : ∃ v, v ∉ S ∧ v ∉ E)
    (hb : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S ∨ y ∈ E)
    (r K : ℕ) (hcut : E.card < r) (hout : ∀ x, outdegree G x = r)
    (hin : ∀ x, (Finset.univ.filter (fun y => G.Adj y x)).card = r)
    (hn : ¬ ∃ k ≤ K, HasDirectedCycleOfLength G k) :
    2 * ((r - 1 + r) * (K + 1)) ≤ r * (Fintype.card V + E.card) := by
  classical
  let R := (S ∪ E)ᶜ
  have memR (x : V) : x ∈ R ↔ x ∉ S ∧ x ∉ E := by simp [R]
  obtain ⟨v, hvs, hve⟩ := hv
  have hrne : R.Nonempty := ⟨v, (memR v).mpr ⟨hvs, hve⟩⟩
  have hRcard : S.card + E.card + R.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_add_card_compl _
  let D : Digraph V := ⟨fun x y => G.Adj y x⟩
  let : DecidableRel D.Adj := fun x y => ‹DecidableRel G.Adj› y x
  have hminD (x : V) : r ≤ outdegree D x := (hin x).ge
  have hmaxD (x : V) : (Finset.univ.filter (fun y => D.Adj y x)).card ≤ r := (hout x).le
  have hnD : ¬ ∃ k ≤ K, HasDirectedCycleOfLength D k := by
    rintro ⟨k, hk, hc⟩
    exact hn ⟨k, hk, reverse_cycle (G := G) (D := D) (fun _ _ => Iff.rfl) hc⟩
  have forward := region_incidence_bound G hloop S E hs hb r r K hcut
    (fun x => (hout x).ge) (fun x => (hin x).le) hn
  have backward := region_incidence_bound D hloop R E hrne
    (complement_boundary_subset S E R memR hb) r r K hcut hminD hmaxD hnD
  calc
    2 * ((r - 1 + r) * (K + 1)) =
        (r - 1 + r) * (K + 1) + (r - 1 + r) * (K + 1) := two_mul _
    _ ≤ r * (S.card + E.card) + r * (R.card + E.card) := Nat.add_le_add forward backward
    _ = r * (Fintype.card V + E.card) := by
      rw [← Nat.mul_add, ← hRcard]
      congr 1
      omega

open scoped Classical in
/-- A particular separator of size below three sharpens the cubic bound:
one of its two sides gives a simple cycle of length at most 3(n+|E|)/10. -/
theorem cubic_cycle_of_separator (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (S E : Finset V) (hs : S.Nonempty)
    (hdis : Disjoint S E) (hv : ∃ v, v ∉ S ∧ v ∉ E)
    (hb : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S ∨ y ∈ E) (hcut : E.card < 3)
    (hout : ∀ x, outdegree G x = 3)
    (hin : ∀ x, (Finset.univ.filter (fun y => G.Adj y x)).card = 3) :
    ∃ k, 10 * k ≤ 3 * (Fintype.card V + E.card) ∧ HasDirectedCycleOfLength G k := by
  let K := (3 * (Fintype.card V + E.card)) / 10
  have short : ∃ k ≤ K, HasDirectedCycleOfLength G k := by
    by_contra hn
    have hp := paired_region_incidence G hloop S E hs hdis hv hb 3 K hcut hout hin hn
    dsimp [K] at hp
    omega
  obtain ⟨k, hk, hc⟩ := short
  dsimp [K] at hk
  exact ⟨k, by omega, hc⟩

open scoped Classical in
/-- A two-sided incidence criterion for short cycles, uniform in the common
degree and the cycle budget. The numerical conditions only involve n, r and K. -/
theorem cycle_of_regular_budget [Nonempty V] (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (r K : ℕ) (hr : 0 < r)
    (hout : ∀ x, outdegree G x = r)
    (hin : ∀ x, (Finset.univ.filter (fun y => G.Adj y x)).card = r)
    (hbudget : Fintype.card V ≤ K * r)
    (hstrict : r * (Fintype.card V + (r - 1)) < 2 * ((r - 1 + r) * (K + 1))) :
    ∃ k ≤ K, HasDirectedCycleOfLength G k := by
  classical
  by_contra hn
  let v : V := Classical.choice inferInstance
  obtain ⟨S, E, hsize, he, hvs, hve, hm, _⟩ :=
    atom_away_from_each_root G hloop r hr (fun x => (hout x).ge) K hbudget hn v
  have hs : S.Nonempty := Finset.card_pos.mp (by omega)
  have hdis : Disjoint S E := by
    apply Finset.disjoint_left.mpr
    intro x hx hxE
    exact ((hm x).mp hxE).1 hx
  have hb : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S ∨ y ∈ E := by
    intro x hx y hy
    by_cases h : y ∈ S
    · exact Or.inl h
    · exact Or.inr ((hm y).mpr ⟨h, x, hx, hy⟩)
  have hp := paired_region_incidence G hloop S E hs hdis ⟨v, hvs, hve⟩ hb r K
    (by omega) hout hin hn
  have hE : E.card = r - 1 := by omega
  rw [hE] at hp
  exact (Nat.not_le_of_lt hstrict) hp

open scoped Classical in
/-- A finite nonempty loopless digraph with three incoming and three outgoing
arcs at each vertex has a simple cycle of length at most ceil(n/3). -/
theorem cycle_of_degree_three_regular [Nonempty V] (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ x, ¬ G.Adj x x) (hout : ∀ x, outdegree G x = 3)
    (hin : ∀ x, (Finset.univ.filter (fun y => G.Adj y x)).card = 3) :
    ∃ k, k ≤ ⌈(Fintype.card V : ℚ) / 3⌉₊ ∧ HasDirectedCycleOfLength G k := by
  classical
  let K := ⌈(Fintype.card V : ℚ) / 3⌉₊
  have hbudget : Fintype.card V ≤ K * 3 := by
    exact_mod_cast (div_le_iff₀ (show (0 : ℚ) < 3 by decide)).mp
      (Nat.le_ceil ((Fintype.card V : ℚ) / 3))
  apply cycle_of_regular_budget G hloop 3 K (by decide) hout hin hbudget
  omega

end OMA.CHRegular

namespace OMA.R_opg_caccetta_haggkvist_conjecture_R1_H2_R1
open OMA.S_opg_caccetta_haggkvist_conjecture
open OMA.R_opg_caccetta_haggkvist_conjecture_R1
open OMA.CHCore OMA.CHObstruction OMA.CHReciprocity OMA.CHDensity

open scoped Classical in
/-- The remaining degree-three case, in strong exactly-outregular digraphs
of order at least ten, with a vertex of indegree at most two and a large two-exit region away
from each root. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj],
    (∀ x, ¬ G.Adj x x) → (∀ x, outdegree G x = 3) →
    (∀ x y, Relation.ReflTransGen G.Adj x y) →
    10 ≤ Fintype.card V →
     (∃ x : V, (Finset.univ.filter (fun y => G.Adj y x)).card ≤ 2) →
    (¬ ∃ k ≤ 3, HasDirectedCycleOfLength G k) →
    (∀ v : V, ∃ S E : Finset V, ⌈(Fintype.card V : ℚ) / 3⌉₊ < S.card ∧
      E.card + 1 = 3 ∧ v ∉ S ∧ v ∉ E ∧
      (∀ y, y ∈ E ↔ y ∉ S ∧ ∃ x ∈ S, G.Adj x y) ∧
      (∀ U : Finset V, U.Nonempty → U ⊂ S →
        3 ≤ (Finset.univ.filter (fun y => y ∉ U ∧ ∃ x ∈ U, G.Adj x y)).card) ∧
      ∀ x y : S, Relation.ReflTransGen (fun a b : S => G.Adj a.1 b.1) x y) →
    (∀ (W : Type) [Fintype W] (D : Digraph W) [DecidableRel D.Adj]
      (v : W) (F : Finset W) (e : W ↪ V),
      (∀ w, ¬ D.Adj w w) → (∀ w, ∃ σ : D.Adj ≃r D.Adj, σ v = w) →
      3 ≤ outdegree D v → F.card * ⌈(Fintype.card W : ℚ) / 3⌉₊ < Fintype.card W →
      ¬ (∀ x ∉ F, ∀ y ∉ F, D.Adj x y → G.Adj (e x) (e y))) →
    ∃ k, k ≤ ⌈(Fintype.card V : ℚ) / 3⌉₊ ∧ HasDirectedCycleOfLength G k

open scoped Classical in
/-- The sparse higher-degree case, subject to the same structural certificate
at every root and outside the integral triangle-forcing region. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj] (r : ℕ), 4 ≤ r →
    (∀ x, ¬ G.Adj x x) → (∀ x, outdegree G x = r) →
    (∀ x y, Relation.ReflTransGen G.Adj x y) →
    3 * ((Fintype.card V : ℤ) + 1) * ((r : ℤ) + 1) ≤
      ((Fintype.card V : ℤ) + 1)^2 + ((r : ℤ) + 1)^2 + 1 →

    (¬ ∃ k ≤ 3, HasDirectedCycleOfLength G k) →
    (∀ v : V, ∃ S E : Finset V, ⌈(Fintype.card V : ℚ) / r⌉₊ < S.card ∧
      E.card + 1 = r ∧ v ∉ S ∧ v ∉ E ∧
      (∀ y, y ∈ E ↔ y ∉ S ∧ ∃ x ∈ S, G.Adj x y) ∧
      (∀ U : Finset V, U.Nonempty → U ⊂ S →
        r ≤ (Finset.univ.filter (fun y => y ∉ U ∧ ∃ x ∈ U, G.Adj x y)).card) ∧
      ∀ x y : S, Relation.ReflTransGen (fun a b : S => G.Adj a.1 b.1) x y) →
    (∀ (W : Type) [Fintype W] (D : Digraph W) [DecidableRel D.Adj]
      (v : W) (F : Finset W) (e : W ↪ V),
      (∀ w, ¬ D.Adj w w) → (∀ w, ∃ σ : D.Adj ≃r D.Adj, σ v = w) →
      r ≤ outdegree D v → F.card * ⌈(Fintype.card W : ℚ) / r⌉₊ < Fintype.card W →
      ¬ (∀ x ∉ F, ∀ y ∉ F, D.Adj x y → G.Adj (e x) (e y))) →
    ∃ k, k ≤ ⌈(Fintype.card V : ℚ) / r⌉₊ ∧ HasDirectedCycleOfLength G k

theorem main : H1 → H2 → OMA.R_opg_caccetta_haggkvist_conjecture_R1.H2 := by
  classical
  intro hthree hmore V _ _ G _ r hr hloop hd hexcluded
  obtain ⟨S, hS, D, hD, hstrong, hreg, hmap⟩ := exists_strong_regular_core G r hd
  let : Nonempty S := hS
  let : DecidableRel D.Adj := hD
  let emb : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  apply lift_short_cycle emb hmap r
  have hl (x : S) : ¬ D.Adj x x := fun e => hloop x.1 (hmap x x e)
  have hmin (x : S) : r ≤ outdegree D x := (hreg x).ge
  have hrq : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by omega)
  let K := ⌈(Fintype.card S : ℚ) / r⌉₊
  have hk : Fintype.card S ≤ K*r := by
    exact_mod_cast (div_le_iff₀ hrq).mp (Nat.le_ceil ((Fintype.card S : ℚ) / r))
  have hrcard := (hmin (Classical.choice hS)).trans_lt (outdegree_lt_card D hl _)
  have hK2 : 2 ≤ K := by
    have h : (1 : ℕ) < ⌈(Fintype.card S : ℚ) / r⌉₊ := Nat.lt_ceil.mpr (by
      apply (lt_div_iff₀ hrq).mpr
      simpa using (show (r : ℚ) < Fintype.card S by exact_mod_cast hrcard))
    exact h
  by_cases hhalf : Fintype.card S ≤ 2*r
  · exact ⟨2, hK2, digon_of_double_degree D hl r hmin hhalf⟩
  have hK3 : 3 ≤ K := by
    apply Nat.lt_ceil.mpr
    apply (lt_div_iff₀ hrq).mpr
    exact_mod_cast (show 2*r < Fintype.card S by omega)
  by_contra hn
  have hn3 : ¬ ∃ k ≤ 3, HasDirectedCycleOfLength D k :=
    fun ⟨k, h, hc⟩ => hn ⟨k, h.trans hK3, hc⟩
  have hw := atom_away_from_each_root D hl r (by omega) hmin K hk hn
  have hsym : (∀ (W : Type) [Fintype W] (A : Digraph W) [DecidableRel A.Adj]
      (v : W) (F : Finset W) (e : W ↪ S),
      (∀ w, ¬ A.Adj w w) → (∀ w, ∃ σ : A.Adj ≃r A.Adj, σ v = w) →
      r ≤ outdegree A v → F.card * ⌈(Fintype.card W : ℚ) / r⌉₊ < Fintype.card W →
      ¬ (∀ x ∉ F, ∀ y ∉ F, A.Adj x y → D.Adj (e x) (e y))) := by
    intro W _ A _ w F e hlA htr hdeg hsmall hadj
    exact hexcluded W A w F (e.trans emb) hlA htr hdeg hsmall
      (fun a ha b hb he => hmap _ _ (hadj a ha b hb he))
  have hsparse : ¬ (((Fintype.card S : ℤ)+1)^2 + ((r : ℤ)+1)^2 + 2 ≤
      3*((Fintype.card S : ℤ)+1)*((r : ℤ)+1)) :=
    fun h => hn3 (triangle_of_integral_min_outdegree D hl r hmin h)
  by_cases heq : r = 3
  · subst r
    have horder : 10 ≤ Fintype.card S := by
      by_contra! h
      exact hn3 (triangle_of_three_outneighbors D hl hmin (by omega))
    have hlow : ∃ x : S, (Finset.univ.filter (fun y => D.Adj y x)).card ≤ 2 := by
      by_contra! hall
      have heqin := indegree_eq_of_regular_lower D 3 hreg (fun x => by have := hall x; omega)
      exact hn (OMA.CHRegular.cycle_of_degree_three_regular D hl hreg heqin)
    exact hn (hthree S D hl hreg hstrong horder hlow hn3 hw hsym)
  · exact hn (hmore S D r (by omega) hl hreg hstrong (by omega) hn3 hw hsym)

end OMA.R_opg_caccetta_haggkvist_conjecture_R1_H2_R1
