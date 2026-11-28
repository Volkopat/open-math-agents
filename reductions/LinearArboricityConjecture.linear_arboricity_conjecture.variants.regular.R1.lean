import FormalConjectures.Wikipedia.LinearArboricityConjecture
import Mathlib

/-! The regular form of the linear arboricity conjecture, with the easy half proved.
Akiyama, Exoo and Harary, Covering and packing in graphs IV.
https://doi.org/10.1002/net.3230110108
Lower bound: degrees in the parts of a decomposition sum to the degree, each at most 2.
If the degree were exactly 2k, every part would be 2-regular, which an acyclic finite graph
is not (a longest path ends at a vertex with one neighbour).
So la(G) is at least (Δ + 2) / 2, and the regular conjecture is equivalent to the upper bound.
The cases Δ = 1 (G is a matching), Δ = 2 (maximum spanning forest plus a matching) and Δ = 3
(the accepted cubic proof, reused here) are proved. H1 and H2 are the remaining upper bound
for even and odd Δ ≥ 4: la(G) ≤ k + 1 when Δ = 2k or Δ = 2k + 1. -/

open Finset SimpleGraph LinearArboricityConjecture

namespace OMA.R_LinearArboricityConjecture_linear_arboricity_conjecture_variants_regular_R1

def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
    2 ≤ k → (∀ v, G.degree v = 2 * k) → HasLinearForestDecomposition G (k + 1)

def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
    2 ≤ k → (∀ v, G.degree v = 2 * k + 1) → HasLinearForestDecomposition G (k + 1)

variable {V : Type}

/-- Degree via the instance equals the ncard of the neighbour set. -/
lemma degree_eq_ncard (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = (G.neighborSet v).ncard := by
  calc
    _ = ((G.neighborFinset v : Finset V) : Set V).ncard := by rw [Set.ncard_coe_finset]; rfl
    _ = _ := congrArg Set.ncard (G.coe_neighborFinset v)

/-- In a decomposition, the degree of `v` in `G` is the sum of its degrees in the parts. -/
lemma ncard_eq_sum [Fintype V] {G : SimpleGraph V} {k : ℕ} {D : Fin k → SimpleGraph V}
    (hle : ∀ i, D i ≤ G) (hD : ∀ u v, G.Adj u v ↔ ∃! i, (D i).Adj u v) (v : V) :
    (G.neighborSet v).ncard = ∑ i, ((D i).neighborSet v).ncard := by
  classical
  have key (H : SimpleGraph V) : (H.neighborSet v).ncard = ∑ w, if H.Adj v w then 1 else 0 := by
    rw [Set.ncard_eq_toFinset_card', ← Finset.card_filter]
    congr 1
    ext w
    simp
  rw [key]
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.card_filter]
  by_cases h : G.Adj v w
  · rw [if_pos h]
    obtain ⟨i, hi, hu⟩ := (hD v w).mp h
    symm
    rw [Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hj => hu j hj, fun hj => hj ▸ hi⟩
  · rw [if_neg h]
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _ hj
    exact h (hle j hj)

/-- A finite nonempty acyclic graph has a vertex without two distinct neighbours. -/
lemma not_all_two_nbrs [Finite V] [Nonempty V] {F : SimpleGraph V} (hF : F.IsAcyclic) :
    ¬ ∀ v, ∃ x y, x ≠ y ∧ F.Adj v x ∧ F.Adj v y := by
  intro h
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length F
  obtain ⟨x, y, hxy, hx, hy⟩ := h u
  have hw : ∃ w, F.Adj u w ∧ w ≠ p.snd := by
    by_cases hxs : x = p.snd
    · exact ⟨y, hy, fun hys => hxy (hxs.trans hys.symm)⟩
    · exact ⟨x, hx, hxs⟩
  obtain ⟨w, huw, hws⟩ := hw
  by_cases hsupp : w ∈ p.support
  · exact hws (hF.eq_snd_of_adj_start hp huw hsupp)
  · have hp' : (Walk.cons huw.symm p).IsPath := Walk.IsPath.cons hp hsupp
    have := hmax _ _ _ hp'
    simp only [Walk.length_cons] at this
    omega

/-- A linear forest has at most two neighbours at each vertex. -/
lemma lf_ncard_le {F : SimpleGraph V} (hF : IsLinearForest F) (v : V) :
    (F.neighborSet v).ncard ≤ 2 := hF.2 v

/-- **Lower bound**: a nonempty `Δ`-regular graph (`0 < Δ`) decomposed into `k` linear forests
satisfies `Δ < 2k`. -/
theorem lower_bound [Fintype V] [Nonempty V] {G : SimpleGraph V} {Δ k : ℕ} (hΔ : 0 < Δ)
    (hreg : ∀ v, (G.neighborSet v).ncard = Δ) (h : HasLinearForestDecomposition G k) :
    Δ < 2 * k := by
  obtain ⟨D, hDf, hD⟩ := h
  have hsum (v : V) : Δ = ∑ i, ((D i).neighborSet v).ncard :=
    (hreg v).symm.trans (ncard_eq_sum (fun i => (hDf i).2) hD v)
  have hle (v : V) : Δ ≤ 2 * k := by
    rw [hsum v]
    calc
      _ ≤ ∑ _i : Fin k, 2 := Finset.sum_le_sum fun i _ => (hDf i).1.2 v
      _ = 2 * k := by simp [mul_comm]
  have v0 : V := Classical.arbitrary V
  rcases (hle v0).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hk : 0 < k := by omega
  let i0 : Fin k := ⟨0, hk⟩
  have htwo (v : V) : ((D i0).neighborSet v).ncard = 2 := by
    by_contra hne
    have hlt : ((D i0).neighborSet v).ncard < 2 := lt_of_le_of_ne ((hDf i0).1.2 v) hne
    have : ∑ i, ((D i).neighborSet v).ncard < ∑ _i : Fin k, 2 :=
      Finset.sum_lt_sum (fun i _ => (hDf i).1.2 v) ⟨i0, Finset.mem_univ _, hlt⟩
    have h2 : ∑ _i : Fin k, 2 = 2 * k := by simp [mul_comm]
    have := hsum v
    omega
  apply not_all_two_nbrs (hDf i0).1.1
  intro v
  obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.mp (htwo v)
  refine ⟨x, y, hxy, ?_, ?_⟩
  · have : x ∈ (D i0).neighborSet v := by rw [hs]; simp
    exact this
  · have : y ∈ (D i0).neighborSet v := by rw [hs]; simp
    exact this

/-- `sInf` bookkeeping: a decomposition into `m` forests plus a lower bound pins down `la`. -/
lemma la_eq_of {G : SimpleGraph V} {m : ℕ} (hdec : HasLinearForestDecomposition G m)
    (hlow : ∀ k, HasLinearForestDecomposition G k → m ≤ k) : linearArboricity G = m :=
  le_antisymm (Nat.sInf_le hdec)
    (hlow _ (Nat.sInf_mem (s := {k | HasLinearForestDecomposition G k}) ⟨m, hdec⟩))

/-- Every decomposition of a `Δ`-regular graph uses at least `(Δ + 2) / 2` forests. -/
theorem regular_lower [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (hΔ : 0 < Δ) (hreg : ∀ v, G.degree v = Δ) {k : ℕ}
    (h : HasLinearForestDecomposition G k) : (Δ + 2) / 2 ≤ k := by
  have := lower_bound hΔ (fun v => (degree_eq_ncard G v).symm.trans (hreg v)) h
  omega

/-- The regular variant follows from a decomposition into `(Δ + 2) / 2` linear forests. -/
theorem regular_of_decomp [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (hΔ : 0 < Δ) (hreg : ∀ v, G.degree v = Δ)
    (hdec : HasLinearForestDecomposition G ((Δ + 2) / 2)) :
    linearArboricity G = (Δ + 2) / 2 :=
  la_eq_of hdec fun _ hk => regular_lower G Δ hΔ hreg hk

/-- `la(G) > Δ/2` as stated in the docstring, unconditionally, given any decomposition. -/
theorem regular_la_ge [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (hΔ : 0 < Δ) (hreg : ∀ v, G.degree v = Δ)
    (hex : ∃ k, HasLinearForestDecomposition G k) :
    (Δ + 2) / 2 ≤ linearArboricity G :=
  regular_lower G Δ hΔ hreg (Nat.sInf_mem (s := {k | HasLinearForestDecomposition G k}) hex)

/-- A linear forest decomposes into one linear forest. -/
lemma decomp_one_of_lf {G : SimpleGraph V} (hG : IsLinearForest G) :
    HasLinearForestDecomposition G 1 := by
  refine ⟨fun _ => G, fun _ => ⟨hG, le_rfl⟩, fun u v => ⟨fun h => ⟨0, h, fun j _ => Subsingleton.elim _ _⟩,
    fun ⟨_, h, _⟩ => h⟩⟩

/-- A 1-regular graph (all neighbour sets of size one) is a linear forest. -/
lemma lf_of_one_regular [Finite V] {G : SimpleGraph V} (hreg : ∀ v, (G.neighborSet v).ncard = 1) :
    IsLinearForest G := by
  refine ⟨fun v p hp => ?_, fun v => by rw [hreg v]; omega⟩
  have hfin : (G.neighborSet v).Finite := Set.toFinite _
  have hs : ({p.snd, p.penultimate} : Set V) ⊆ G.neighborSet v := by
    intro x hx
    rcases hx with rfl | hx
    · exact p.adj_snd hp.not_nil
    · simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact (p.adj_penultimate hp.not_nil).symm
  have := Set.ncard_le_ncard hs hfin
  rw [Set.ncard_pair hp.snd_ne_penultimate, hreg v] at this
  omega

/-- The case `Δ = 1` of the regular variant. -/
theorem regular_one [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 1) : linearArboricity G = 1 := by
  have h1 : ∀ v, (G.neighborSet v).ncard = 1 := fun v => (degree_eq_ncard G v).symm.trans (hreg v)
  exact regular_of_decomp G 1 one_pos hreg (decomp_one_of_lf (lf_of_one_regular h1))


section Small

open scoped Classical

variable {V : Type} [Fintype V]

omit [Fintype V] in
private lemma card_neighbors (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    (G.neighborFinset v).card = (G.neighborSet v).ncard := by
  calc
    _ = ((G.neighborFinset v : Finset V) : Set V).ncard := by rw [Set.ncard_coe_finset]
    _ = _ := congrArg Set.ncard (G.coe_neighborFinset v)

omit [Fintype V] in
private lemma degreeN_eq_degree (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    (G.neighborSet v).ncard = G.degree v := (card_neighbors G v).symm

private lemma degreeN_pos_of_adj (G : SimpleGraph V) {v w : V} (h : G.Adj v w) :
    0 < (G.neighborSet v).ncard := by
  rw [← card_neighbors G v]
  exact Finset.card_pos.mpr ⟨w, (G.mem_neighborFinset v w).mpr h⟩

private lemma neighbor_subset {G H : SimpleGraph V} (h : G ≤ H) (v : V) :
    G.neighborFinset v ⊆ H.neighborFinset v := by
  intro w hw
  exact (H.mem_neighborFinset v w).mpr (h ((G.mem_neighborFinset v w).mp hw))

private lemma degree_le_of_le {G H : SimpleGraph V} (h : G ≤ H) (v : V) :
    (G.neighborSet v).ncard ≤ (H.neighborSet v).ncard := by
  simpa only [card_neighbors] using Finset.card_le_card (neighbor_subset h v)

private lemma degree_sup_le (G H : SimpleGraph V) (v : V) :
    ((G ⊔ H).neighborSet v).ncard ≤ (G.neighborSet v).ncard + (H.neighborSet v).ncard := by
  rw [← card_neighbors, neighborFinset_sup]
  simpa only [card_neighbors] using
    Finset.card_union_le (G.neighborFinset v) (H.neighborFinset v)

private lemma degree_sdiff (G H : SimpleGraph V) (h : H ≤ G) (v : V) :
    ((G \ H).neighborSet v).ncard = (G.neighborSet v).ncard - (H.neighborSet v).ncard := by
  rw [← card_neighbors, neighborFinset_sdiff, Finset.card_sdiff_of_subset (neighbor_subset h v)]
  simp only [card_neighbors]

private lemma add_edge_degree_le (G : SimpleGraph V) (a b v : V) :
    ((G ⊔ SimpleGraph.edge a b).neighborSet v).ncard ≤ (G.neighborSet v).ncard + 1 := by
  apply (degree_sup_le G (SimpleGraph.edge a b) v).trans
  apply Nat.add_le_add_left
  rw [← card_neighbors (SimpleGraph.edge a b) v, Finset.card_le_one]
  intro x hx y hy
  have hx' := (mem_neighborFinset _ v x).mp hx
  have hy' := (mem_neighborFinset _ v y).mp hy
  rw [SimpleGraph.edge_adj] at hx' hy'
  rcases hx'.1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases hy'.1 with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;> grind

private lemma add_edge_degree_unchanged (G : SimpleGraph V) (a b v : V)
    (ha : v ≠ a) (hb : v ≠ b) :
    ((G ⊔ SimpleGraph.edge a b).neighborSet v).ncard = (G.neighborSet v).ncard := by
  have he : (SimpleGraph.edge a b).neighborFinset v = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h := (mem_neighborFinset _ v x).mp hx
    rw [SimpleGraph.edge_adj] at h
    rcases h.1 with ⟨h, _⟩ | ⟨h, _⟩
    · exact ha h
    · exact hb h
  rw [← card_neighbors, neighborFinset_sup, he, Finset.union_empty,
    card_neighbors]

private lemma degree_two_of_neighbors (G : SimpleGraph V) {v x y : V}
    (hx : G.Adj v x) (hy : G.Adj v y) (hne : x ≠ y) :
    2 ≤ (G.neighborSet v).ncard := by
  rw [← card_neighbors]
  have h : ({x, y} : Finset V) ⊆ G.neighborFinset v := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, mem_neighborFinset, hx, hy,
      and_self]
  have hc := Finset.card_le_card h
  have hne' : x ∉ ({y} : Finset V) := by simpa only [Finset.mem_singleton] using hne
  rw [Finset.card_insert_of_notMem hne', Finset.card_singleton] at hc
  exact hc

private lemma neighbors_eq (G : SimpleGraph V) {v x y : V}
    (h : (G.neighborSet v).ncard ≤ 1) (hx : G.Adj v x) (hy : G.Adj v y) : x = y := by
  by_contra hne
  have := degree_two_of_neighbors G hx hy hne
  omega

private lemma neighbor_eq_of_degree_two (G : SimpleGraph V) {v a b c : V}
    (h : (G.neighborSet v).ncard ≤ 2) (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) : c = a ∨ c = b := by
  by_contra! hne
  have hs : ({c, a, b} : Finset V) ⊆ G.neighborFinset v := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, mem_neighborFinset, ha, hb, hc,
      and_self]
  have hc' := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem (by simp [hne.1, hne.2]),
    Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using hab),
    Finset.card_singleton, card_neighbors] at hc'
  omega

private lemma cycle_degree (G : SimpleGraph V) {v : V}
    {p : G.Walk v v} (hc : p.IsCycle) : 2 ≤ (G.neighborSet v).ncard :=
  degree_two_of_neighbors G (p.adj_snd hc.not_nil) (p.adj_penultimate hc.not_nil).symm
    hc.snd_ne_penultimate

private lemma path_component_closed (G : SimpleGraph V) (hmax : ∀ v, (G.neighborSet v).ncard ≤ 2)
    {a b : V} (hab : a ≠ b) (ha : (G.neighborSet a).ncard ≤ 1) (hb : (G.neighborSet b).ncard ≤ 1)
    {p : G.Walk a b} (hp : p.IsPath)
    {x y : V} (hx : x ∈ p.support) (hxy : G.Adj x y) : y ∈ p.support := by
  obtain ⟨i, rfl, hi⟩ := (Walk.mem_support_iff_exists_getVert.mp hx)
  have hpn : ¬ p.Nil := Walk.not_nil_of_ne hab
  have hpl : 0 < p.length := Walk.not_nil_iff_lt_length.mp hpn
  rcases i with _ | i
  · simp only [Walk.getVert_zero] at hxy
    have he := neighbors_eq G ha hxy (p.adj_snd hpn)
    rw [he]
    exact p.getVert_mem_support 1
  by_cases hend : i + 1 = p.length
  · have hxe : p.getVert (i + 1) = b := by rw [hend, Walk.getVert_length]
    rw [hxe] at hxy
    have he := neighbors_eq G hb hxy (p.adj_penultimate hpn).symm
    rw [he]
    exact p.getVert_mem_support (p.length - 1)
  have hi₁ : i < p.length := by omega
  have hi₂ : i + 1 < p.length := by omega
  have hprev := (p.adj_getVert_succ hi₁).symm
  have hnext := p.adj_getVert_succ hi₂
  have hne : p.getVert i ≠ p.getVert (i + 1 + 1) := by
    intro he
    have hh := hp.getVert_injOn (show i ∈ {j | j ≤ p.length} from hi₁.le)
      (show i + 1 + 1 ∈ {j | j ≤ p.length} from by exact Nat.succ_le_of_lt hi₂) he
    omega
  rcases neighbor_eq_of_degree_two G (hmax _) hprev hnext hxy hne with he | he
  · rw [he]; exact p.getVert_mem_support i
  · rw [he]; exact p.getVert_mem_support (i + 1 + 1)

private lemma reachable_low_degree_unique (G : SimpleGraph V) (hmax : ∀ v, (G.neighborSet v).ncard ≤ 2)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (ha : (G.neighborSet a).ncard ≤ 1)
    (hb : (G.neighborSet b).ncard ≤ 1) (hc : (G.neighborSet c).ncard ≤ 1)
    (habR : G.Reachable a b) (hacR : G.Reachable a c) : b = c := by
  obtain ⟨p, hp⟩ := habR.exists_isPath
  have hclosed {x y : V} (hx : x ∈ p.support) (hxy : G.Adj x y) : y ∈ p.support :=
    path_component_closed G hmax hab ha hb hp hx hxy
  obtain ⟨q⟩ := hacR
  have hmem {x y : V} (q : G.Walk x y) (hx : x ∈ p.support) : y ∈ p.support := by
    induction q with
    | nil => exact hx
    | cons hadj q ih => exact ih (hclosed hx hadj)
  obtain ⟨i, hci, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (hmem q p.start_mem_support)
  by_cases hi0 : i = 0
  · exact (hac ((by simpa only [hi0, Walk.getVert_zero] using hci : a = c))).elim
  by_cases hie : i = p.length
  · simpa only [hie, Walk.getVert_length] using hci
  have hi₁ : i - 1 < p.length := by omega
  have hi₂ : i < p.length := lt_of_le_of_ne hi hie
  have hprev := (p.adj_getVert_succ hi₁).symm
  rw [show i - 1 + 1 = i by omega, hci] at hprev
  have hnext := p.adj_getVert_succ hi₂
  rw [hci] at hnext
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro he
    have hh := hp.getVert_injOn (show i - 1 ∈ {j | j ≤ p.length} from hi₁.le)
      (show i + 1 ∈ {j | j ≤ p.length} from Nat.succ_le_of_lt hi₂) he
    omega
  have hh := degree_two_of_neighbors G hprev hnext hne
  omega

private lemma maximum_subgraph (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : ∃ B ≤ G, P B) :
    ∃ B ≤ G, P B ∧ ∀ C ≤ G, P C → C.edgeSet.ncard ≤ B.edgeSet.ncard := by
  let S : Set ℕ := {m | ∃ B ≤ G, P B ∧ B.edgeSet.ncard = m}
  have hS : S.Nonempty := by
    obtain ⟨B, hB, hBP⟩ := hP
    exact ⟨B.edgeSet.ncard, B, hB, hBP, rfl⟩
  have hbound : BddAbove S := by
    refine ⟨G.edgeSet.ncard, ?_⟩
    rintro m ⟨B, hB, hBP, rfl⟩
    exact Set.ncard_le_ncard (edgeSet_mono hB)
  obtain ⟨B, hB, hBP, hBc⟩ := Nat.sSup_mem hS hbound
  refine ⟨B, hB, hBP, fun C hC hCP => ?_⟩
  rw [hBc]
  exact le_csSup hbound ⟨C, hC, hCP, rfl⟩

private lemma hall_neighbors (G : SimpleGraph V) (hreg : ∀ v, (G.neighborSet v).ncard = 3)
    (U : Set V) :
    ∃ f : U → V, Function.Injective f ∧ ∀ u : U, G.Adj u.val (f u) := by
  let t (u : U) := G.neighborFinset (u : V)
  have hHall (S : Finset U) : S.card ≤ (S.biUnion t).card := by
    let W := S.biUnion t
    have hs (u : U) (hu : u ∈ S) : t u ⊆ W :=
      fun w hw => Finset.mem_biUnion.mpr ⟨u, hu, hw⟩
    have hs₃ (u : U) : (t u).card = 3 := by
      simp only [t, card_neighbors G, hreg]
    have hsum :
        (∑ u ∈ S, (t u).card) = ∑ w ∈ W, (S.filter (fun u => w ∈ t u)).card := by
      calc
        _ = ∑ u ∈ S, ∑ w ∈ W, if w ∈ t u then 1 else 0 := by
          refine Finset.sum_congr rfl fun u hu => ?_
          have he : W.filter (fun w => w ∈ t u) = t u := by
            ext w
            exact ⟨fun h => (Finset.mem_filter.mp h).2,
              fun h => Finset.mem_filter.mpr ⟨hs u hu h, h⟩⟩
          rw [← Finset.card_filter, he]
        _ = _ := by rw [Finset.sum_comm]; simp only [Finset.card_filter]
    have hdeg (w : V) : (S.filter (fun u => w ∈ t u)).card ≤ 3 := by
      let S' := S.filter (fun u => w ∈ t u)
      have himage : S'.image Subtype.val ⊆ G.neighborFinset w := by
        intro y hy
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
        exact (G.mem_neighborFinset w u.val).mpr
          ((G.mem_neighborFinset u.val w).mp (Finset.mem_filter.mp hu).2).symm
      have hh := Finset.card_le_card himage
      rw [Finset.card_image_of_injective _ Subtype.val_injective,
        card_neighbors G, hreg] at hh
      exact hh
    have hupper : (∑ w ∈ W, (S.filter (fun u => w ∈ t u)).card) ≤ W.card * 3 := by
      simpa only [Finset.sum_const, Nat.nsmul_eq_mul] using
        (Finset.sum_le_sum fun w (_ : w ∈ W) => hdeg w)
    simp only [hs₃, Finset.sum_const, Nat.nsmul_eq_mul] at hsum
    change S.card ≤ W.card
    omega
  obtain ⟨f, hf, htf⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall
  exact ⟨f, hf, fun u => (G.mem_neighborFinset u.val (f u)).mp (htf u)⟩

private lemma initial_forest (G : SimpleGraph V) (hreg : ∀ v, (G.neighborSet v).ncard = 3) :
    ∃ B ≤ G, B.IsAcyclic ∧ (∀ v, (B.neighborSet v).ncard ≤ 2) ∧ (∀ v, ((G \ B).neighborSet v).ncard ≤ 2) := by
  obtain ⟨M, hMG, hM, hMmax⟩ := maximum_subgraph G (fun M => ∀ v, (M.neighborSet v).ncard ≤ 1)
    ⟨⊥, bot_le, fun v => by simp⟩
  let U : Set V := {v | (M.neighborSet v).ncard = 0}
  have independent {a b : V} (ha : a ∈ U) (hb : b ∈ U) : ¬ G.Adj a b := by
    intro hab
    let M' := M ⊔ SimpleGraph.edge a b
    have hM'le : M' ≤ G := sup_le hMG ((edge_le_iff (G := G)).mpr (Or.inr hab))
    have hdeg (v : V) : (M'.neighborSet v).ncard ≤ 1 := by
      by_cases hva : v = a
      · subst v
        exact (add_edge_degree_le M a b a).trans (by change (M.neighborSet a).ncard + 1 ≤ 1; rw [show (M.neighborSet a).ncard = 0 from ha])
      by_cases hvb : v = b
      · subst v
        exact (add_edge_degree_le M a b b).trans (by change (M.neighborSet b).ncard + 1 ≤ 1; rw [show (M.neighborSet b).ncard = 0 from hb])
      exact (add_edge_degree_unchanged M a b v hva hvb).le.trans (hM v)
    have hnot : ¬ M.Adj a b := by
      intro h
      exact (degreeN_pos_of_adj M h).ne' ha
    have hincr := Set.ncard_lt_ncard (edgeSet_strict_mono (lt_sup_edge M (s := a) (t := b) hab.ne hnot))
    exact (hMmax M' hM'le hdeg).not_gt hincr
  obtain ⟨f, hf, hfa⟩ := hall_neighbors G hreg U
  have hout (u : U) : f u ∉ U := fun h => independent u.property h (hfa u)
  let Rel (x y : V) : Prop := ∃ hx : x ∈ U, f ⟨x, hx⟩ = y
  let F := SimpleGraph.fromRel Rel
  have hFG : F ≤ G := by
    intro x y hxy
    rw [SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with ⟨hx, he⟩ | ⟨hy, he⟩
    · exact he ▸ hfa ⟨x, hx⟩
    · exact (he ▸ hfa ⟨y, hy⟩).symm
  have hFD (x : V) : (F.neighborSet x).ncard ≤ 1 := by
    rw [← card_neighbors, Finset.card_le_one]
    intro y hy z hz
    have hy' := (F.mem_neighborFinset x y).mp hy
    have hz' := (F.mem_neighborFinset x z).mp hz
    rw [SimpleGraph.fromRel_adj] at hy' hz'
    rcases hy'.2 with ⟨hx, hxy⟩ | ⟨hy, hyx⟩ <;>
      rcases hz'.2 with ⟨hx', hxz⟩ | ⟨hz, hzx⟩
    · exact hxy.symm.trans hxz
    · exact (hout ⟨z, hz⟩ (hzx.symm ▸ hx)).elim
    · exact (hout ⟨y, hy⟩ (hyx.symm ▸ hx')).elim
    · exact congrArg Subtype.val (hf (hyx.trans hzx.symm))
  let B := M ⊔ F
  have hBG : B ≤ G := sup_le hMG hFG
  have hB₂ (x : V) : (B.neighborSet x).ncard ≤ 2 := by
    have hh := degree_sup_le M F x
    change (B.neighborSet x).ncard ≤ (M.neighborSet x).ncard + (F.neighborSet x).ncard at hh
    have hm := hM x
    have hf := hFD x
    omega
  have hB₁ (x : V) : 1 ≤ (B.neighborSet x).ncard := by
    by_cases hx : x ∈ U
    · have hadj : F.Adj x (f ⟨x, hx⟩) := by
        exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨(hfa ⟨x, hx⟩).ne, Or.inl ⟨hx, rfl⟩⟩
      have hpos : 0 < (F.neighborSet x).ncard := degreeN_pos_of_adj F hadj
      exact hpos.trans_le (degree_le_of_le le_sup_right x)
    · have hpos : 0 < (M.neighborSet x).ncard := Nat.pos_of_ne_zero hx
      exact hpos.trans_le (degree_le_of_le le_sup_left x)
  have hacyc : B.IsAcyclic := by
    intro v p hp
    have hu (x : V) (hx : x ∈ p.support) : x ∉ U := by
      intro hxu
      have hcyc : (p.rotate x hx).IsCycle := (Walk.isCycle_rotate hx).mpr hp
      have hx2 := cycle_degree B hcyc
      have hx0 : (M.neighborSet x).ncard = 0 := hxu
      have hh := degree_sup_le M F x
      change (B.neighborSet x).ncard ≤ (M.neighborSet x).ncard + (F.neighborSet x).ncard at hh
      have hF := hFD x
      omega
    have hM_adj {a b : V} (ha : a ∉ U) (hb : b ∉ U) (hab : B.Adj a b) : M.Adj a b := by
      rcases hab with hM | hF
      · exact hM
      · rw [SimpleGraph.fromRel_adj] at hF
        rcases hF.2 with ⟨ha', _⟩ | ⟨hb', _⟩
        · exact (ha ha').elim
        · exact (hb hb').elim
    have hv := hu v p.start_mem_support
    have hsnd := hu p.snd (p.getVert_mem_support 1)
    have hpen := hu p.penultimate (p.getVert_mem_support (p.length - 1))
    have he := neighbors_eq M (hM v)
      (hM_adj hv hsnd (p.adj_snd hp.not_nil))
      (hM_adj hv hpen (p.adj_penultimate hp.not_nil).symm)
    exact hp.snd_ne_penultimate he
  refine ⟨B, hBG, hacyc, hB₂, fun x => ?_⟩
  rw [degree_sdiff G B hBG, hreg]
  have := hB₁ x
  omega

private lemma two_forests (G : SimpleGraph V) (hreg : ∀ v, (G.neighborSet v).ncard = 3) :
    ∃ B ≤ G, IsLinearForest B ∧ IsLinearForest (G \ B) := by
  obtain ⟨B, hBG, ⟨hBacyc, hB₂, hR₂⟩, hmax⟩ := maximum_subgraph G
    (fun H => H.IsAcyclic ∧ (∀ v, (H.neighborSet v).ncard ≤ 2) ∧ ∀ v, ((G \ H).neighborSet v).ncard ≤ 2)
    (initial_forest G hreg)
  refine ⟨B, hBG, ⟨hBacyc, hB₂⟩, ?_, hR₂⟩
  let R := G \ B
  by_contra hn
  have hcycles : ∃ (u : V) (p : R.Walk u u), p.IsCycle := by
    simpa only [SimpleGraph.IsAcyclic, not_forall, not_not] using hn
  obtain ⟨u, p, hp⟩ := hcycles
  have cycle_vertex (x : V) (hx : x ∈ p.support) : (B.neighborSet x).ncard ≤ 1 := by
    have hi : (p.rotate x hx).IsCycle := (Walk.isCycle_rotate hx).mpr hp
    have hde := cycle_degree R hi
    change 2 ≤ ((G \ B).neighborSet x).ncard at hde
    rw [degree_sdiff G B hBG, hreg] at hde
    omega
  have hu := cycle_vertex u p.start_mem_support
  have hv := cycle_vertex p.snd (p.getVert_mem_support 1)
  have hw := cycle_vertex p.penultimate (p.getVert_mem_support (p.length - 1))
  have huv : R.Adj u p.snd := p.adj_snd hp.not_nil
  have huw : R.Adj u p.penultimate := (p.adj_penultimate hp.not_nil).symm
  have hedge : ∃ v, R.Adj u v ∧ (B.neighborSet v).ncard ≤ 1 ∧ ¬ B.Reachable u v := by
    by_cases hr : B.Reachable u p.snd
    · refine ⟨p.penultimate, huw, hw, ?_⟩
      intro hr'
      exact hp.snd_ne_penultimate
        (reachable_low_degree_unique B hB₂ huv.ne huw.ne hu hv hw hr hr')
    · exact ⟨p.snd, huv, hv, hr⟩
  obtain ⟨v, huv, hv, hr⟩ := hedge
  have hab : G.Adj u v ∧ ¬ B.Adj u v := huv
  let B' := B ⊔ SimpleGraph.edge u v
  have hB'G : B' ≤ G := sup_le hBG ((edge_le_iff (G := G)).mpr (Or.inr hab.1))
  have hB'acyc : B'.IsAcyclic := hBacyc.sup_edge_of_not_reachable hr
  have hB'₂ (x : V) : (B'.neighborSet x).ncard ≤ 2 := by
    by_cases hx : x = u
    · subst x
      exact (add_edge_degree_le B u v u).trans (by omega)
    by_cases hx' : x = v
    · subst x
      exact (add_edge_degree_le B u v v).trans (by omega)
    exact (add_edge_degree_unchanged B u v x hx hx').le.trans (hB₂ x)
  have hR'₂ (x : V) : ((G \ B').neighborSet x).ncard ≤ 2 := by
    have hle : G \ B' ≤ G \ B := fun _ _ e => ⟨e.1, fun hb => e.2 (Or.inl hb)⟩
    exact (degree_le_of_le hle x).trans (hR₂ x)
  have hincr := Set.ncard_lt_ncard (edgeSet_strict_mono (lt_sup_edge B (s := u) (t := v) hab.1.ne hab.2))
  exact (hmax B' hB'G ⟨hB'acyc, hB'₂, hR'₂⟩).not_gt hincr

omit [Fintype V] in
private lemma two_decomposition_of (G B : SimpleGraph V) (hBG : B ≤ G)
    (hB : IsLinearForest B) (hR : IsLinearForest (G \ B)) :
    HasLinearForestDecomposition G 2 := by
  let D (i : Fin 2) : SimpleGraph V := if i = 0 then B else G \ B
  have hsub (i : Fin 2) : D i ≤ G := by
    unfold D
    split_ifs
    · exact hBG
    · exact fun _ _ e => e.1
  refine ⟨D, fun i => ⟨?_, hsub i⟩, ?_⟩
  · unfold D
    split_ifs
    · exact hB
    · exact hR
  intro u v
  constructor
  · intro hu
    by_cases h : B.Adj u v
    · refine ⟨0, by simpa only [D, if_pos rfl] using h, ?_⟩
      intro j hj
      by_contra hn
      have hr : (G \ B).Adj u v := by simpa only [D, if_neg hn] using hj
      exact hr.2 h
    · have hRuv : (G \ B).Adj u v := ⟨hu, h⟩
      refine ⟨1, by simpa only [D, if_neg (by decide : (1 : Fin 2) ≠ 0)] using hRuv, ?_⟩
      intro j hj
      have hj01 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
      rcases hj01 j with rfl | hj'
      · exact (h (by simpa only [D, if_pos rfl] using hj)).elim
      · exact hj'
  · rintro ⟨i, hi, _⟩
    exact hsub i hi


private lemma two_regular_forests (G : SimpleGraph V) (hreg : ∀ v, (G.neighborSet v).ncard = 2) :
    ∃ B ≤ G, IsLinearForest B ∧ IsLinearForest (G \ B) := by
  obtain ⟨B, hBG, hBacyc, hmax⟩ := maximum_subgraph G (fun H => H.IsAcyclic)
    ⟨⊥, bot_le, isAcyclic_bot⟩
  have hR1 (v : V) : ((G \ B).neighborSet v).ncard ≤ 1 := by
    by_contra hlt
    have hlt' : 1 < ((G \ B).neighborSet v).ncard := by
      change ¬ ((G \ B).neighborSet v).ncard ≤ 1 at hlt
      omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.one_lt_ncard_iff_nontrivial.mp hlt'
    have hx' : G.Adj v x ∧ ¬ B.Adj v x := hx
    have hy' : G.Adj v y ∧ ¬ B.Adj v y := hy
    have hnoB (z : V) : ¬ B.Adj v z := fun hz => by
      rcases neighbor_eq_of_degree_two G (hreg v).le hx'.1 hy'.1 (hBG hz) hxy with rfl | rfl
      · exact hx'.2 hz
      · exact hy'.2 hz
    have hnr : ¬ B.Reachable v x := by
      rintro ⟨q⟩
      cases q with
      | nil => exact hx'.1.ne rfl
      | cons h _ => exact hnoB _ h
    let B' := B ⊔ SimpleGraph.edge v x
    have hB'G : B' ≤ G := sup_le hBG ((edge_le_iff (G := G)).mpr (Or.inr hx'.1))
    have hB'acyc : B'.IsAcyclic := hBacyc.sup_edge_of_not_reachable hnr
    have hincr := Set.ncard_lt_ncard
      (edgeSet_strict_mono (lt_sup_edge B (s := v) (t := x) hx'.1.ne hx'.2))
    exact (hmax B' hB'G hB'acyc).not_gt hincr
  refine ⟨B, hBG, ⟨hBacyc, fun v => (degree_le_of_le hBG v).trans (hreg v).le⟩,
    ⟨?_, fun v => (hR1 v).trans (by norm_num)⟩⟩
  intro v q hq
  have h2 := cycle_degree (G \ B) hq
  have h1 := hR1 v
  omega

private lemma cubic_decomposition (G : SimpleGraph V) (hreg : ∀ v, (G.neighborSet v).ncard = 3) :
    HasLinearForestDecomposition G 2 := by
  obtain ⟨B, hBG, hB, hR⟩ := two_forests G hreg
  exact two_decomposition_of G B hBG hB hR

private lemma two_regular_decomposition (G : SimpleGraph V) (hreg : ∀ v, (G.neighborSet v).ncard = 2) :
    HasLinearForestDecomposition G 2 := by
  obtain ⟨B, hBG, hB, hR⟩ := two_regular_forests G hreg
  exact two_decomposition_of G B hBG hB hR

end Small

theorem main : H1 → H2 →
    type_of% @LinearArboricityConjecture.linear_arboricity_conjecture.variants.regular := by
  intro h1 h2 V _ _ G _ Δ hΔ hreg
  have hn (v : V) : (G.neighborSet v).ncard = Δ := (degree_eq_ncard G v).symm.trans (hreg v)
  rcases (show Δ = 1 ∨ Δ = 2 ∨ Δ = 3 ∨ 4 ≤ Δ by omega) with rfl | rfl | rfl | h4
  · exact regular_one G hreg
  · exact regular_of_decomp G 2 hΔ hreg (two_regular_decomposition G hn)
  · exact regular_of_decomp G 3 hΔ hreg (cubic_decomposition G hn)
  · obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' Δ
    · subst hk
      have he : (2 * k + 2) / 2 = k + 1 := by omega
      exact regular_of_decomp G (2 * k) hΔ hreg (he ▸ h1 G k (by omega) hreg)
    · subst hk
      have he : (2 * k + 1 + 2) / 2 = k + 1 := by omega
      exact regular_of_decomp G (2 * k + 1) hΔ hreg (he ▸ h2 G k (by omega) hreg)

end OMA.R_LinearArboricityConjecture_linear_arboricity_conjecture_variants_regular_R1
