import OMAReductions.R_Erdos642_erdos_642_variants_upper_bound_n_log_pow_eight_R1
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
Proof of Step `Erdos642.erdos_642.variants.upper_bound_n_log_pow_eight.R1.H1` (DMMS24, Lemma 2.4).
Credit: @PrimordialAA

Extracts a 100-almost-regular bipartite `1 / (10 * log n)`-edge-expander of average degree at least
`d(G) / (600 * log n)` via local max-cut, a density-maximizing min-degree bipartite subgraph,
Pyber's matching decomposition (Bucic et al., arXiv:1809.01468 Lemma 2.1), and a single-shot
potential maximizer.
-/

namespace OMA.Erdos642H1

open SimpleGraph Filter Real
open scoped Classical

section GraphHelpers

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Induced subgraph of `G` on a vertex subset `U`, kept as a graph on `V` supported on `U`. -/
def induceOn (G : SimpleGraph V) (U : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ U ∧ v ∈ U
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

omit [Fintype V] [DecidableEq V] in
lemma induceOn_le (G : SimpleGraph V) (U : Finset V) : induceOn G U ≤ G :=
  fun _ _ h => h.1

omit [Fintype V] [DecidableEq V] in
lemma induceOn_support (G : SimpleGraph V) (U : Finset V) {u v : V}
    (h : (induceOn G U).Adj u v) : u ∈ U ∧ v ∈ U := h.2

omit [DecidableEq V] in
lemma mem_induceOn_edgeFinset {G : SimpleGraph V} {U : Finset V} {u v : V} :
    s(u, v) ∈ (induceOn G U).edgeFinset ↔ G.Adj u v ∧ u ∈ U ∧ v ∈ U := by
  rw [mem_edgeFinset, mem_edgeSet]; rfl

/-- Edges of `G` with one endpoint in `S` and the other in `T`. -/
noncomputable def cutEdges (G : SimpleGraph V) (S T : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∃ u v : V, u ∈ S ∧ v ∈ T ∧ e = s(u, v))

lemma mem_cutEdges_mk {G : SimpleGraph V} {S T : Finset V} {u v : V} :
    s(u, v) ∈ cutEdges G S T ↔
      G.Adj u v ∧ ((u ∈ S ∧ v ∈ T) ∨ (v ∈ S ∧ u ∈ T)) := by
  simp only [cutEdges, Finset.mem_filter, mem_edgeFinset, mem_edgeSet]
  constructor
  · rintro ⟨hadj, a, b, ha, hb, heq⟩
    refine ⟨hadj, ?_⟩
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
  · rintro ⟨hadj, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩
    · exact ⟨hadj, u, v, hu, hv, rfl⟩
    · exact ⟨hadj, v, u, hv, hu, Sym2.eq_swap⟩

lemma edgeFinset_eq_induce_union_cut {G : SimpleGraph V} {U S : Finset V}
    (hsupp : ∀ u v, G.Adj u v → u ∈ U ∧ v ∈ U) (_hSU : S ⊆ U) :
    G.edgeFinset.card =
      (induceOn G S).edgeFinset.card +
      (induceOn G (U \ S)).edgeFinset.card +
      (cutEdges G S (U \ S)).card := by
  set E1 := (induceOn G S).edgeFinset
  set E2 := (induceOn G (U \ S)).edgeFinset
  set E3 := cutEdges G S (U \ S)
  have hd12 : Disjoint E1 E2 := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    refine Sym2.inductionOn e (fun u v h1 h2 => ?_) h1 h2
    rw [mem_induceOn_edgeFinset] at h1 h2
    exact (Finset.mem_sdiff.mp h2.2.1).2 h1.2.1
  have hd13 : Disjoint E1 E3 := by
    rw [Finset.disjoint_left]
    intro e h1 h3
    refine Sym2.inductionOn e (fun u v h1 h3 => ?_) h1 h3
    rw [mem_induceOn_edgeFinset] at h1
    have h3' := mem_cutEdges_mk.mp h3
    rcases h3'.2 with ⟨_, hv⟩ | ⟨_, hu⟩
    · exact (Finset.mem_sdiff.mp hv).2 h1.2.2
    · exact (Finset.mem_sdiff.mp hu).2 h1.2.1
  have hd23 : Disjoint E2 E3 := by
    rw [Finset.disjoint_left]
    intro e h2 h3
    refine Sym2.inductionOn e (fun u v h2 h3 => ?_) h2 h3
    rw [mem_induceOn_edgeFinset] at h2
    have h3' := mem_cutEdges_mk.mp h3
    rcases h3'.2 with ⟨hu, _⟩ | ⟨hv, _⟩
    · exact (Finset.mem_sdiff.mp h2.2.1).2 hu
    · exact (Finset.mem_sdiff.mp h2.2.2).2 hv
  have hunion : G.edgeFinset = E1 ∪ E2 ∪ E3 := by
    ext e
    refine Sym2.inductionOn e (fun u v => ?_)
    simp only [Finset.mem_union, E1, E2, E3, mem_induceOn_edgeFinset, mem_cutEdges_mk]
    rw [mem_edgeFinset, mem_edgeSet]
    constructor
    · intro hadj
      obtain ⟨huU, hvU⟩ := hsupp u v hadj
      by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
      · exact Or.inl (Or.inl ⟨hadj, hu, hv⟩)
      · exact Or.inr ⟨hadj, Or.inl ⟨hu, Finset.mem_sdiff.mpr ⟨hvU, hv⟩⟩⟩
      · exact Or.inr ⟨hadj, Or.inr ⟨hv, Finset.mem_sdiff.mpr ⟨huU, hu⟩⟩⟩
      · exact Or.inl (Or.inr ⟨hadj, Finset.mem_sdiff.mpr ⟨huU, hu⟩, Finset.mem_sdiff.mpr ⟨hvU, hv⟩⟩)
    · rintro ((⟨h, _, _⟩ | ⟨h, _, _⟩) | ⟨h, _⟩) <;> exact h
  rw [hunion, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩),
    Finset.card_union_of_disjoint hd12]

lemma edgeFinset_erase_add_degree {G : SimpleGraph V} {U : Finset V} {v : V}
    (hsupp : ∀ x y, G.Adj x y → x ∈ U ∧ y ∈ U) (hv : v ∈ U) :
    (induceOn G (U.erase v)).edgeFinset.card + G.degree v = G.edgeFinset.card := by
  have h1 := edgeFinset_eq_induce_union_cut hsupp (Finset.singleton_subset_iff.mpr hv)
  have hsdiff : U \ {v} = U.erase v := by
    ext x; simp [Finset.mem_sdiff, Finset.mem_erase, and_comm]
  rw [hsdiff] at h1
  have hsing : (induceOn G {v}).edgeFinset.card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro e he
    refine Sym2.inductionOn e (fun a b he => ?_) he
    rw [mem_induceOn_edgeFinset, Finset.mem_singleton, Finset.mem_singleton] at he
    obtain ⟨hadj, rfl, hbv⟩ := he
    exact G.loopless.irrefl a (hbv ▸ hadj)
  have hcut : (cutEdges G {v} (U.erase v)).card = G.degree v := by
    rw [← card_neighborFinset_eq_degree]
    symm
    refine Finset.card_bij (fun w _ => s(v, w)) ?_ ?_ ?_
    · intro w hw
      have hadj : G.Adj v w := (mem_neighborFinset G v w).mp hw
      have hwU : w ∈ U := (hsupp v w hadj).2
      have hne : w ≠ v := fun h => G.loopless.irrefl v (h ▸ hadj)
      exact mem_cutEdges_mk.mpr ⟨hadj, Or.inl ⟨Finset.mem_singleton_self v,
        Finset.mem_erase.mpr ⟨hne, hwU⟩⟩⟩
    · intro w1 _ w2 _ heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨_, rfl⟩ | ⟨h1, h2⟩
      · rfl
      · exact h2.trans h1
    · intro e he
      refine Sym2.inductionOn e (fun a b he => ?_) he
      obtain ⟨hadj, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩ := mem_cutEdges_mk.mp he
      · rw [Finset.mem_singleton] at ha
        rw [ha] at hadj
        exact ⟨b, (mem_neighborFinset G v b).mpr hadj, by rw [ha]⟩
      · rw [Finset.mem_singleton] at hb
        rw [hb] at hadj
        exact ⟨a, (mem_neighborFinset G v a).mpr hadj.symm, by rw [hb, Sym2.eq_swap]⟩
  omega

lemma bipartite_edge_card_eq_sum_degree {G : SimpleGraph V} {A B : Finset V}
    (hdisj : Disjoint A B)
    (hbip : ∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (v ∈ A ∧ u ∈ B)) :
    G.edgeFinset.card = ∑ b ∈ B, G.degree b := by
  have htwice := G.sum_degrees_eq_twice_card_edges
  have hsupp : ∀ v, v ∉ A ∪ B → G.degree v = 0 := by
    intro v hv
    rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    have hadj := (mem_neighborFinset G v w).mp hw
    rcases hbip v w hadj with ⟨h, _⟩ | ⟨_, h⟩
    · exact hv (Finset.mem_union_left B h)
    · exact hv (Finset.mem_union_right A h)
  have hsum_all : ∑ v : V, G.degree v = (∑ a ∈ A, G.degree a) + (∑ b ∈ B, G.degree b) := by
    rw [← Finset.sum_union hdisj]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro v _ hv
    exact hsupp v hv
  have hsum_eq : ∑ a ∈ A, G.degree a = ∑ b ∈ B, G.degree b := by
    have hA : ∑ a ∈ A, G.degree a =
        ∑ a ∈ A, ∑ b ∈ B, if G.Adj a b then 1 else 0 := by
      refine Finset.sum_congr rfl (fun a ha => ?_)
      rw [← card_neighborFinset_eq_degree, Finset.sum_boole, Nat.cast_id]
      congr 1
      ext b
      simp only [mem_neighborFinset, Finset.mem_filter]
      constructor
      · intro hadj
        refine ⟨?_, hadj⟩
        rcases hbip a b hadj with ⟨_, hb⟩ | ⟨_, haB⟩
        · exact hb
        · exact absurd ha (Finset.disjoint_right.mp hdisj haB)
      · exact fun h => h.2
    have hB : ∑ b ∈ B, G.degree b =
        ∑ b ∈ B, ∑ a ∈ A, if G.Adj a b then 1 else 0 := by
      refine Finset.sum_congr rfl (fun b hb => ?_)
      rw [← card_neighborFinset_eq_degree, Finset.sum_boole, Nat.cast_id]
      congr 1
      ext a
      simp only [mem_neighborFinset, Finset.mem_filter]
      constructor
      · intro hadj
        refine ⟨?_, hadj.symm⟩
        rcases hbip b a hadj with ⟨hbA, _⟩ | ⟨ha, _⟩
        · exact absurd hbA (Finset.disjoint_right.mp hdisj hb)
        · exact ha
      · exact fun h => h.2.symm
    rw [hA, hB, Finset.sum_comm]
  omega

end GraphHelpers

section Step1MaxCut

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Step 1: Every finite graph contains a bipartite subgraph with at least half as many edges. -/
lemma exists_bipartite_maxCut (G : SimpleGraph V) :
    ∃ A : Finset V, ∃ G₀ : SimpleGraph V,
      G₀ ≤ G ∧
      (∀ u v, G₀.Adj u v → (u ∈ A ↔ v ∉ A)) ∧
      G.edgeFinset.card ≤ 2 * G₀.edgeFinset.card := by
  let cutCard (S : Finset V) : ℕ := (cutEdges G S Sᶜ).card
  obtain ⟨A, -, hAmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset V)) cutCard
    ⟨∅, Finset.mem_univ _⟩
  obtain ⟨G₀, hG₀adj⟩ : ∃ G₀ : SimpleGraph V, ∀ u v, G₀.Adj u v ↔ G.Adj u v ∧ (u ∈ A ↔ v ∉ A) :=
    ⟨{ Adj := fun u v => G.Adj u v ∧ (u ∈ A ↔ v ∉ A)
       symm := ⟨fun _ _ ⟨h, hiff⟩ => ⟨h.symm, by tauto⟩⟩
       loopless := ⟨fun v ⟨h, _⟩ => G.loopless.irrefl v h⟩ }, fun _ _ => Iff.rfl⟩
  have hG₀_le : G₀ ≤ G := fun u v h => ((hG₀adj u v).mp h).1
  have hdeg : ∀ v : V, G.degree v ≤ 2 * G₀.degree v := by
    intro v
    let A' : Finset V := if v ∈ A then A.erase v else insert v A
    have hv_flip : ∀ w : V, w ≠ v → (w ∈ A' ↔ w ∈ A) := by
      intro w hw
      dsimp only [A']
      split_ifs <;> simp [Finset.mem_erase, Finset.mem_insert, hw]
    have hv_self : v ∈ A' ↔ v ∉ A := by
      dsimp only [A']
      split_ifs with h <;> simp [Finset.mem_erase, Finset.mem_insert, h]
    let E_keep := (cutEdges G A Aᶜ).filter (fun e => v ∉ e)
    let E_out := (cutEdges G A Aᶜ).filter (fun e => v ∈ e)
    let E_in := (cutEdges G A' A'ᶜ).filter (fun e => v ∈ e)
    have hkeep_eq : (cutEdges G A' A'ᶜ).filter (fun e => v ∉ e) = E_keep := by
      ext e
      refine Sym2.inductionOn e (fun a b => ?_)
      simp only [E_keep, Finset.mem_filter, mem_cutEdges_mk, Finset.mem_compl, Sym2.mem_iff, not_or]
      constructor
      · rintro ⟨⟨hadj, hside⟩, ha, hb⟩
        refine ⟨⟨hadj, ?_⟩, ha, hb⟩
        rw [hv_flip a (Ne.symm ha), hv_flip b (Ne.symm hb)] at hside
        exact hside
      · rintro ⟨⟨hadj, hside⟩, ha, hb⟩
        refine ⟨⟨hadj, ?_⟩, ha, hb⟩
        rw [hv_flip a (Ne.symm ha), hv_flip b (Ne.symm hb)]
        exact hside
    have hsplitA : cutCard A = E_out.card + E_keep.card := by
      dsimp only [cutCard, E_out, E_keep]
      exact (Finset.card_filter_add_card_filter_not (s := cutEdges G A Aᶜ) (fun e => v ∈ e)).symm
    have hsplitA' : cutCard A' = E_in.card + E_keep.card := by
      dsimp only [cutCard, E_in]
      rw [← hkeep_eq]
      exact (Finset.card_filter_add_card_filter_not (s := cutEdges G A' A'ᶜ) (fun e => v ∈ e)).symm
    have hle : E_in.card ≤ E_out.card := by
      have hm := hAmax A' (Finset.mem_univ A')
      omega
    have hout_eq : E_out.card = G₀.degree v := by
      rw [← card_neighborFinset_eq_degree]
      symm
      refine Finset.card_bij (fun w _ => s(v, w)) ?_ ?_ ?_
      · intro w hw
        have hadj := (hG₀adj v w).mp ((mem_neighborFinset G₀ v w).mp hw)
        refine Finset.mem_filter.mpr ⟨mem_cutEdges_mk.mpr ⟨hadj.1, ?_⟩, Sym2.mem_mk_left v w⟩
        simp only [Finset.mem_compl]
        by_cases hvA : v ∈ A
        · exact Or.inl ⟨hvA, hadj.2.mp hvA⟩
        · exact Or.inr ⟨by_contra (fun hwA => hvA (hadj.2.mpr hwA)), hvA⟩
      · intro w1 _ w2 _ heq
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨_, rfl⟩ | ⟨h1, h2⟩
        · rfl
        · exact h2.trans h1
      · intro e he
        refine Sym2.inductionOn e (fun a b he => ?_) he
        simp only [E_out, Finset.mem_filter, mem_cutEdges_mk, Finset.mem_compl, Sym2.mem_iff] at he
        rcases he.2 with rfl | rfl
        · refine ⟨b, (mem_neighborFinset G₀ v b).mpr ((hG₀adj v b).mpr ⟨he.1.1, ?_⟩), rfl⟩
          rcases he.1.2 with ⟨ha, hb⟩ | ⟨hb, ha⟩
          · exact ⟨fun _ => hb, fun _ => ha⟩
          · exact ⟨fun h => absurd h ha, fun h => absurd hb h⟩
        · refine ⟨a, (mem_neighborFinset G₀ v a).mpr ((hG₀adj v a).mpr ⟨he.1.1.symm, ?_⟩), Sym2.eq_swap⟩
          rcases he.1.2 with ⟨ha, hb⟩ | ⟨hb, ha⟩
          · exact ⟨fun h => absurd h hb, fun h => absurd ha h⟩
          · exact ⟨fun _ => ha, fun _ => hb⟩
    have hin_eq : E_in.card = (G.neighborFinset v \ G₀.neighborFinset v).card := by
      symm
      refine Finset.card_bij (fun w _ => s(v, w)) ?_ ?_ ?_
      · intro w hw
        rw [Finset.mem_sdiff, mem_neighborFinset, mem_neighborFinset] at hw
        have hwv : w ≠ v := fun h => G.loopless.irrefl v (h ▸ hw.1)
        refine Finset.mem_filter.mpr ⟨mem_cutEdges_mk.mpr ⟨hw.1, ?_⟩, Sym2.mem_mk_left v w⟩
        simp only [Finset.mem_compl]
        have hnot : ¬ (v ∈ A ↔ w ∉ A) := fun h => hw.2 ((hG₀adj v w).mpr ⟨hw.1, h⟩)
        have h1 := hv_self
        have h2 := hv_flip w hwv
        by_cases hvA : v ∈ A
        · have hwA : w ∈ A := by_contra (fun hw' => hnot ⟨fun _ => hw', fun _ => hvA⟩)
          exact Or.inr ⟨h2.mpr hwA, fun hv' => (h1.mp hv') hvA⟩
        · have hwA : w ∉ A := fun hw' => hnot ⟨fun h => absurd h hvA, fun h => absurd hw' h⟩
          exact Or.inl ⟨h1.mpr hvA, fun hw' => hwA (h2.mp hw')⟩
      · intro w1 _ w2 _ heq
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨_, rfl⟩ | ⟨h1, h2⟩
        · rfl
        · exact h2.trans h1
      · intro e he
        refine Sym2.inductionOn e (fun a b he => ?_) he
        simp only [E_in, Finset.mem_filter, mem_cutEdges_mk, Finset.mem_compl, Sym2.mem_iff] at he
        rcases he.2 with rfl | rfl
        · have hne : b ≠ v := fun h => G.loopless.irrefl v (h ▸ he.1.1)
          have h1 := hv_self
          have h2 := hv_flip b hne
          have hside := he.1.2
          refine ⟨b, Finset.mem_sdiff.mpr ⟨(mem_neighborFinset G v b).mpr he.1.1, ?_⟩, rfl⟩
          rw [mem_neighborFinset]
          intro h0
          have hiff := ((hG₀adj v b).mp h0).2
          rcases hside with ⟨ha', hb'⟩ | ⟨hb', ha'⟩
          · exact hb' (h2.mpr (by_contra (fun hb => (h1.mp ha') (hiff.mpr hb))))
          · exact (hiff.mp (by_contra (fun ha => ha' (h1.mpr ha)))) (h2.mp hb')
        · have hne : a ≠ v := fun h => G.loopless.irrefl v (h ▸ he.1.1.symm)
          have h1 := hv_self
          have h2 := hv_flip a hne
          have hside := he.1.2
          refine ⟨a, Finset.mem_sdiff.mpr ⟨(mem_neighborFinset G v a).mpr he.1.1.symm, ?_⟩,
            Sym2.eq_swap⟩
          rw [mem_neighborFinset]
          intro h0
          have hiff := ((hG₀adj v a).mp h0).2
          rcases hside with ⟨ha', hb'⟩ | ⟨hb', ha'⟩
          · exact (hiff.mp (by_contra (fun hb => hb' (h1.mpr hb)))) (h2.mp ha')
          · exact ha' (h2.mpr (by_contra (fun ha => (h1.mp hb') (hiff.mpr ha))))
    have hsub : G₀.neighborFinset v ⊆ G.neighborFinset v := fun w hw =>
      (mem_neighborFinset G v w).mpr (hG₀_le ((mem_neighborFinset G₀ v w).mp hw))
    have hdiff := Finset.card_sdiff_add_card_eq_card hsub
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hdiff
    omega
  refine ⟨A, G₀, hG₀_le, fun u v h => ((hG₀adj u v).mp h).2, ?_⟩
  have hsum : ∑ v : V, G.degree v ≤ ∑ v : V, 2 * G₀.degree v :=
    Finset.sum_le_sum (fun v _ => hdeg v)
  rw [← Finset.mul_sum, G.sum_degrees_eq_twice_card_edges, G₀.sum_degrees_eq_twice_card_edges]
    at hsum
  omega

end Step1MaxCut

section Step2MinDegree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Step 2: From a bipartite graph with positive edge count, extract a bipartite induced subgraph
    with parts `A₁, B₁` (`|B₁| ≤ |A₁|`) and minimum degree at least `e(G₀) / |V|`. -/
lemma exists_minDegree_bipartite (G₀ : SimpleGraph V) (A : Finset V)
    (hbip : ∀ u v, G₀.Adj u v → (u ∈ A ↔ v ∉ A))
    (hepos : 0 < G₀.edgeFinset.card) :
    ∃ A₁ B₁ : Finset V, ∃ G₁ : SimpleGraph V,
      Disjoint A₁ B₁ ∧
      B₁.card ≤ A₁.card ∧
      A₁.Nonempty ∧
      G₁ ≤ G₀ ∧
      (∀ u v, G₁.Adj u v → (u ∈ A₁ ∧ v ∈ B₁) ∨ (v ∈ A₁ ∧ u ∈ B₁)) ∧
      (∀ v ∈ A₁ ∪ B₁, (G₀.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ≤ (G₁.degree v : ℝ)) := by
  have hVpos : 0 < Fintype.card V := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp hepos
    have hneV : Nonempty V := Sym2.inductionOn e (fun u _ => ⟨u⟩)
    exact Fintype.card_pos_iff.mpr hneV
  let nonEmptySubs : Finset (Finset V) := Finset.univ.filter Finset.Nonempty
  have huniv_mem : (Finset.univ : Finset V) ∈ nonEmptySubs :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hVpos)⟩
  let dens (U : Finset V) : ℝ := ((induceOn G₀ U).edgeFinset.card : ℝ) / (U.card : ℝ)
  obtain ⟨U, hUmem, hUmax⟩ := Finset.exists_max_image nonEmptySubs dens ⟨Finset.univ, huniv_mem⟩
  have hUne : U.Nonempty := (Finset.mem_filter.mp hUmem).2
  let G₁ := induceOn G₀ U
  have hG₁_univ : induceOn G₀ Finset.univ = G₀ := by
    ext u v; simp [induceOn]
  have hdens_ge : (G₀.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ≤ dens U := by
    have hm := hUmax Finset.univ huniv_mem
    dsimp only [dens] at hm ⊢
    rwa [hG₁_univ, Finset.card_univ] at hm
  have hUpos : (0 : ℝ) < U.card := by exact_mod_cast hUne.card_pos
  have hG₁_pos : 0 < G₁.edgeFinset.card := by
    have h0 : (0 : ℝ) < (G₀.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) := by positivity
    have h1 : (0 : ℝ) < (G₁.edgeFinset.card : ℝ) / (U.card : ℝ) := lt_of_lt_of_le h0 hdens_ge
    have h2 : (0 : ℝ) < G₁.edgeFinset.card := (div_pos_iff_of_pos_right hUpos).mp h1
    exact_mod_cast h2
  have hU2 : 2 ≤ U.card := by
    by_contra hlt
    have h1 : U.card = 1 := by have := hUne.card_pos; omega
    obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨e, he⟩ := Finset.card_pos.mp hG₁_pos
    refine Sym2.inductionOn e (fun a b he => ?_) he
    rw [mem_induceOn_edgeFinset, Finset.mem_singleton, Finset.mem_singleton] at he
    obtain ⟨hadj, rfl, hbw⟩ := he
    exact G₀.loopless.irrefl a (hbw ▸ hadj)
  have hdeg : ∀ v ∈ U, dens U ≤ (G₁.degree v : ℝ) := by
    intro v hv
    have hne' : (U.erase v).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hv]; omega
    have hmem' : U.erase v ∈ nonEmptySubs :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne'⟩
    have hm := hUmax (U.erase v) hmem'
    have hcard_er : (U.erase v).card = U.card - 1 := Finset.card_erase_of_mem hv
    have hcard_pos' : (0 : ℝ) < (U.erase v).card := by exact_mod_cast hne'.card_pos
    have hind_er : induceOn G₁ (U.erase v) = induceOn G₀ (U.erase v) := by
      ext x y
      simp only [induceOn, G₁]
      constructor
      · rintro ⟨⟨hadj, _, _⟩, hx, hy⟩; exact ⟨hadj, hx, hy⟩
      · rintro ⟨hadj, hx, hy⟩
        exact ⟨⟨hadj, Finset.mem_of_mem_erase hx, Finset.mem_of_mem_erase hy⟩, hx, hy⟩
    have hedge_er := edgeFinset_erase_add_degree (G := G₁) (U := U) (v := v)
      (fun _ _ h => h.2) hv
    rw [hind_er] at hedge_er
    have hreal_er : ((induceOn G₀ (U.erase v)).edgeFinset.card : ℝ) =
        (G₁.edgeFinset.card : ℝ) - (G₁.degree v : ℝ) := by
      have : (induceOn G₀ (U.erase v)).edgeFinset.card + G₁.degree v = G₁.edgeFinset.card := hedge_er
      have : ((induceOn G₀ (U.erase v)).edgeFinset.card : ℝ) + (G₁.degree v : ℝ) =
          (G₁.edgeFinset.card : ℝ) := by exact_mod_cast this
      linarith
    have hcard_real : ((U.erase v).card : ℝ) = (U.card : ℝ) - 1 := by
      rw [hcard_er, Nat.cast_sub (by omega : 1 ≤ U.card)]; simp
    dsimp only [dens] at hm ⊢
    rw [hreal_er, hcard_real] at hm
    rw [div_le_div_iff₀ (by linarith) hUpos] at hm
    have hmul : (G₁.edgeFinset.card : ℝ) ≤ (G₁.degree v : ℝ) * (U.card : ℝ) := by nlinarith
    exact (div_le_iff₀ hUpos).mpr hmul
  let UA := U ∩ A
  let UB := U \ A
  have hdisj : Disjoint UA UB := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx2).2 (Finset.mem_inter.mp hx1).2
  have hunion : UA ∪ UB = U := by
    ext x; simp only [UA, UB, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have hbipU : ∀ u v, G₁.Adj u v → (u ∈ UA ∧ v ∈ UB) ∨ (v ∈ UA ∧ u ∈ UB) := by
    intro u v ⟨hadj, hu, hv⟩
    have hiff := hbip u v hadj
    by_cases huA : u ∈ A
    · exact Or.inl ⟨Finset.mem_inter.mpr ⟨hu, huA⟩, Finset.mem_sdiff.mpr ⟨hv, hiff.mp huA⟩⟩
    · have hvA : v ∈ A := by tauto
      exact Or.inr ⟨Finset.mem_inter.mpr ⟨hv, hvA⟩, Finset.mem_sdiff.mpr ⟨hu, huA⟩⟩
  by_cases hcmp : UB.card ≤ UA.card
  · have hAne : UA.Nonempty := by
      rw [← Finset.card_pos]
      have : U.card = UA.card + UB.card := by rw [← hunion, Finset.card_union_of_disjoint hdisj]
      omega
    refine ⟨UA, UB, G₁, hdisj, hcmp, hAne, induceOn_le G₀ U, hbipU, fun v hv => ?_⟩
    rw [hunion] at hv
    exact hdens_ge.trans (hdeg v hv)
  · have hcmp' : UA.card ≤ UB.card := by omega
    have hBne : UB.Nonempty := by
      rw [← Finset.card_pos]
      have : U.card = UA.card + UB.card := by rw [← hunion, Finset.card_union_of_disjoint hdisj]
      omega
    refine ⟨UB, UA, G₁, hdisj.symm, hcmp', hBne, induceOn_le G₀ U,
      fun u v h => (hbipU u v h).elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
        (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩), fun v hv => ?_⟩
    rw [Finset.union_comm, hunion] at hv
    exact hdens_ge.trans (hdeg v hv)

end Step2MinDegree

section Step3Pyber

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Single step of Pyber's matching decomposition via Hall's Marriage Theorem. -/
lemma pyber_step (G : SimpleGraph V) (A₀ B₀ : Finset V)
    (hdisj : Disjoint A₀ B₀)
    (hcard : B₀.card ≤ A₀.card)
    (hAne : A₀.Nonempty)
    (hbip : ∀ u v, G.Adj u v → (u ∈ A₀ ∧ v ∈ B₀) ∨ (v ∈ A₀ ∧ u ∈ B₀))
    (hdeg : ∀ a ∈ A₀, 1 ≤ G.degree a) :
    ∃ A₁ B₁ : Finset V, ∃ M G' : SimpleGraph V,
      A₁ ⊆ A₀ ∧ B₁ ⊆ B₀ ∧
      B₁.Nonempty ∧
      A₁.card = B₁.card ∧
      M ≤ G ∧ G' ≤ G ∧
      (∀ u v, M.Adj u v → ¬ G'.Adj u v) ∧
      (∀ u v, M.Adj u v → (u ∈ A₁ ∧ v ∈ B₁) ∨ (v ∈ A₁ ∧ u ∈ B₁)) ∧
      (∀ a ∈ A₁, M.degree a = 1) ∧
      (∀ b ∈ B₁, M.degree b = 1) ∧
      (∀ u v, G'.Adj u v → (u ∈ A₁ ∧ v ∈ B₁) ∨ (v ∈ A₁ ∧ u ∈ B₁)) ∧
      (∀ a ∈ A₁, G.degree a - 1 ≤ G'.degree a) := by
  let N (X : Finset V) : Finset V := X.biUnion (fun a => G.neighborFinset a)
  have hN_sub : ∀ X ⊆ A₀, N X ⊆ B₀ := by
    intro X hX b hb
    obtain ⟨a, haX, hba⟩ := Finset.mem_biUnion.mp hb
    have hadj := (mem_neighborFinset G a b).mp hba
    rcases hbip a b hadj with ⟨_, hbB⟩ | ⟨_, haB⟩
    · exact hbB
    · exact absurd (hX haX) (Finset.disjoint_right.mp hdisj haB)
  let cands : Finset (Finset V) :=
    A₀.powerset.filter (fun X => X.Nonempty ∧ (N X).card ≤ X.card)
  have hA₀_mem : A₀ ∈ cands := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset_self A₀, hAne, ?_⟩
    exact (Finset.card_le_card (hN_sub A₀ (Finset.Subset.refl _))).trans hcard
  obtain ⟨A₁, hA₁mem, hA₁min⟩ := Finset.exists_min_image cands Finset.card ⟨A₀, hA₀_mem⟩
  have hA₁sub : A₁ ⊆ A₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp hA₁mem).1
  have hA₁ne : A₁.Nonempty := (Finset.mem_filter.mp hA₁mem).2.1
  have hNA₁_le : (N A₁).card ≤ A₁.card := (Finset.mem_filter.mp hA₁mem).2.2
  let B₁ : Finset V := N A₁
  have hB₁sub : B₁ ⊆ B₀ := hN_sub A₁ hA₁sub
  have hB₁ne : B₁.Nonempty := by
    obtain ⟨a, ha⟩ := hA₁ne
    have hpos : 0 < (G.neighborFinset a).card := by
      rw [card_neighborFinset_eq_degree]; exact hdeg a (hA₁sub ha)
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
    exact ⟨b, Finset.mem_biUnion.mpr ⟨a, ha, hb⟩⟩
  have hA₁eqB₁ : A₁.card = B₁.card := by
    apply le_antisymm _ hNA₁_le
    by_contra hlt
    have hlt' : B₁.card < A₁.card := Nat.lt_of_not_le hlt
    have hA₁2 : 2 ≤ A₁.card := by have := hB₁ne.card_pos; omega
    obtain ⟨a, ha⟩ := hA₁ne
    let A' := A₁.erase a
    have hA'ne : A'.Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem ha]; omega
    have hA'card : A'.card = A₁.card - 1 := Finset.card_erase_of_mem ha
    have hNA'_le : (N A').card ≤ A'.card := by
      have hsub : N A' ⊆ B₁ := Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.erase_subset a A₁)
      have := Finset.card_le_card hsub
      omega
    have hA'mem : A' ∈ cands :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ((Finset.erase_subset a A₁).trans hA₁sub),
        hA'ne, hNA'_le⟩
    have hmin := hA₁min A' hA'mem
    omega
  -- Hall's condition on A₁
  let t : A₁ → Finset V := fun a => G.neighborFinset a.val
  have hHall : ∀ s : Finset A₁, s.card ≤ (s.biUnion t).card := by
    intro s
    let X : Finset V := s.map ⟨Subtype.val, Subtype.val_injective⟩
    have hXcard : X.card = s.card := Finset.card_map _
    have hXsub : X ⊆ A₁ := by
      intro x hx
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
      exact a.property
    have hNX : s.biUnion t = N X := by
      ext b
      simp only [Finset.mem_biUnion, N, X, Finset.mem_map, Function.Embedding.coeFn_mk, t]
      constructor
      · rintro ⟨a, ha, hb⟩; exact ⟨a.val, ⟨a, ha, rfl⟩, hb⟩
      · rintro ⟨x, ⟨a, ha, rfl⟩, hb⟩; exact ⟨a, ha, hb⟩
    rw [hNX, ← hXcard]
    by_cases hXe : X = ∅
    · rw [hXe]; simp
    · have hXne : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr hXe
      by_cases hXeq : X = A₁
      · rw [hXeq, hA₁eqB₁]
      · have hXlt : X.card < A₁.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hXsub, hXeq⟩)
        by_contra hgt
        have hle : (N X).card ≤ X.card := Nat.le_of_not_lt (by omega)
        have hXmem : X ∈ cands :=
          Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hXsub.trans hA₁sub), hXne, hle⟩
        have hmin := hA₁min X hXmem
        omega
  obtain ⟨f, hfinj, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  have hfB₁ : ∀ a : A₁, f a ∈ B₁ := fun a => Finset.mem_biUnion.mpr ⟨a.val, a.property, hfmem a⟩
  have hf_img_eq : (Finset.univ : Finset A₁).image f = B₁ := by
    refine Finset.eq_of_subset_of_card_le (fun b hb => ?_) ?_
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb; exact hfB₁ a
    · rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_coe, hA₁eqB₁]
  have hf_surj : ∀ b ∈ B₁, ∃ a : A₁, f a = b := by
    intro b hb
    rw [← hf_img_eq] at hb
    obtain ⟨a, _, hab⟩ := Finset.mem_image.mp hb
    exact ⟨a, hab⟩
  have hdisj₁ : Disjoint A₁ B₁ := hdisj.mono hA₁sub hB₁sub
  obtain ⟨M, hMadj⟩ : ∃ M : SimpleGraph V, ∀ u v, M.Adj u v ↔
      ∃ a : A₁, (u = a.val ∧ v = f a) ∨ (v = a.val ∧ u = f a) :=
    ⟨{ Adj := fun u v => ∃ a : A₁, (u = a.val ∧ v = f a) ∨ (v = a.val ∧ u = f a)
       symm := ⟨fun _ _ ⟨a, h⟩ => ⟨a, h.symm⟩⟩
       loopless := ⟨fun v ⟨a, h⟩ => by
         rcases h with ⟨rfl, hv⟩ | ⟨rfl, hv⟩
         · exact G.loopless.irrefl a.val (hv ▸ (mem_neighborFinset G a.val (f a)).mp (hfmem a))
         · exact G.loopless.irrefl a.val (hv ▸ (mem_neighborFinset G a.val (f a)).mp (hfmem a))⟩ },
     fun _ _ => Iff.rfl⟩
  obtain ⟨G', hG'adj⟩ : ∃ G' : SimpleGraph V, ∀ u v, G'.Adj u v ↔
      G.Adj u v ∧ ¬ M.Adj u v ∧ ((u ∈ A₁ ∧ v ∈ B₁) ∨ (v ∈ A₁ ∧ u ∈ B₁)) :=
    ⟨{ Adj := fun u v => G.Adj u v ∧ ¬ M.Adj u v ∧
         ((u ∈ A₁ ∧ v ∈ B₁) ∨ (v ∈ A₁ ∧ u ∈ B₁))
       symm := ⟨fun _ _ ⟨h1, h2, h3⟩ => ⟨h1.symm, fun hm => h2 hm.symm, h3.symm⟩⟩
       loopless := ⟨fun v ⟨h1, _, _⟩ => G.loopless.irrefl v h1⟩ },
     fun _ _ => Iff.rfl⟩
  have hM_le : M ≤ G := by
    intro u v h
    obtain ⟨a, ha⟩ := (hMadj u v).mp h
    rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (mem_neighborFinset G a.val (f a)).mp (hfmem a)
    · exact ((mem_neighborFinset G a.val (f a)).mp (hfmem a)).symm
  have hM_bip : ∀ u v, M.Adj u v → (u ∈ A₁ ∧ v ∈ B₁) ∨ (v ∈ A₁ ∧ u ∈ B₁) := by
    intro u v h
    obtain ⟨a, ha⟩ := (hMadj u v).mp h
    rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨a.property, hfB₁ a⟩
    · exact Or.inr ⟨a.property, hfB₁ a⟩
  have hM_degA : ∀ a ∈ A₁, M.degree a = 1 := by
    intro a ha
    rw [← card_neighborFinset_eq_degree]
    have heq : M.neighborFinset a = {f ⟨a, ha⟩} := by
      ext v
      simp only [mem_neighborFinset, Finset.mem_singleton, hMadj]
      constructor
      · rintro ⟨a', ⟨h1, rfl⟩ | ⟨h1, h2⟩⟩
        · have : a' = ⟨a, ha⟩ := Subtype.ext h1.symm
          rw [this]
        · exact absurd (h2 ▸ hfB₁ a') (Finset.disjoint_left.mp hdisj₁ ha)
      · rintro rfl
        exact ⟨⟨a, ha⟩, Or.inl ⟨rfl, rfl⟩⟩
    rw [heq, Finset.card_singleton]
  have hM_degB : ∀ b ∈ B₁, M.degree b = 1 := by
    intro b hb
    obtain ⟨a, rfl⟩ := hf_surj b hb
    rw [← card_neighborFinset_eq_degree]
    have heq : M.neighborFinset (f a) = {a.val} := by
      ext v
      simp only [mem_neighborFinset, Finset.mem_singleton, hMadj]
      constructor
      · rintro ⟨a', ⟨h1, h2⟩ | ⟨rfl, h2⟩⟩
        · exact absurd (h1 ▸ hfB₁ a) (Finset.disjoint_left.mp hdisj₁ a'.property)
        · have : a' = a := hfinj h2.symm
          rw [this]
      · rintro rfl
        exact ⟨a, Or.inr ⟨rfl, rfl⟩⟩
    rw [heq, Finset.card_singleton]
  have hG'_degA : ∀ a ∈ A₁, G.degree a - 1 ≤ G'.degree a := by
    intro a ha
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    have hsub : G.neighborFinset a \ M.neighborFinset a ⊆ G'.neighborFinset a := by
      intro v hv
      rw [Finset.mem_sdiff, mem_neighborFinset, mem_neighborFinset] at hv
      rw [mem_neighborFinset, hG'adj]
      refine ⟨hv.1, hv.2, Or.inl ⟨ha, Finset.mem_biUnion.mpr ⟨a, ha, (mem_neighborFinset G a v).mpr hv.1⟩⟩⟩
    have hMsub : M.neighborFinset a ⊆ G.neighborFinset a := fun v hv =>
      (mem_neighborFinset G a v).mpr (hM_le ((mem_neighborFinset M a v).mp hv))
    have hdiff := Finset.card_sdiff_add_card_eq_card hMsub
    have hM1 : (M.neighborFinset a).card = 1 := by
      rw [card_neighborFinset_eq_degree]; exact hM_degA a ha
    have hle := Finset.card_le_card hsub
    omega
  exact ⟨A₁, B₁, M, G', hA₁sub, hB₁sub, hB₁ne, hA₁eqB₁, hM_le, fun u v h => ((hG'adj u v).mp h).1,
    fun u v hm hg => ((hG'adj u v).mp hg).2.1 hm, hM_bip, hM_degA, hM_degB,
    fun u v h => ((hG'adj u v).mp h).2.2, hG'_degA⟩

/-- Iterating Pyber's step `k` times yields nested sets and `k` edge-disjoint perfect matchings. -/
lemma pyber_matchings (G : SimpleGraph V) (A₀ B₀ : Finset V) (k : ℕ)
    (hdisj : Disjoint A₀ B₀)
    (hcard : B₀.card ≤ A₀.card)
    (hAne : A₀.Nonempty)
    (hbip : ∀ u v, G.Adj u v → (u ∈ A₀ ∧ v ∈ B₀) ∨ (v ∈ A₀ ∧ u ∈ B₀))
    (hdeg : ∀ a ∈ A₀, k ≤ G.degree a) :
    ∃ (As Bs : ℕ → Finset V) (Ms : ℕ → SimpleGraph V),
      As 0 = A₀ ∧ Bs 0 = B₀ ∧
      (∀ i, i < k → As (i + 1) ⊆ As i ∧ Bs (i + 1) ⊆ Bs i) ∧
      (∀ i, 1 ≤ i → i ≤ k →
        (Bs i).Nonempty ∧ (As i).card = (Bs i).card ∧
        Ms i ≤ G ∧
        (∀ u v, (Ms i).Adj u v → (u ∈ As i ∧ v ∈ Bs i) ∨ (v ∈ As i ∧ u ∈ Bs i)) ∧
        (∀ a ∈ As i, (Ms i).degree a = 1) ∧
        (∀ b ∈ Bs i, (Ms i).degree b = 1)) ∧
      (∀ i j, 1 ≤ i → i < j → j ≤ k → ∀ u v, (Ms i).Adj u v → ¬ (Ms j).Adj u v) := by
  induction k generalizing G A₀ B₀ with
  | zero =>
    refine ⟨fun _ => A₀, fun _ => B₀, fun _ => ⊥, rfl, rfl, fun _ h => by omega,
      fun _ h1 h2 => by omega, fun _ _ h1 h2 h3 => by omega⟩
  | succ k ih =>
    have hdeg1 : ∀ a ∈ A₀, 1 ≤ G.degree a := fun a ha => by have := hdeg a ha; omega
    obtain ⟨A₁, B₁, M₁, G', hA₁sub, hB₁sub, hB₁ne, hA₁eqB₁, hM₁le, hG'le, hM₁G',
      hM₁bip, hM₁degA, hM₁degB, hG'bip, hG'deg⟩ :=
      pyber_step G A₀ B₀ hdisj hcard hAne hbip hdeg1
    have hdisj₁ : Disjoint A₁ B₁ := hdisj.mono hA₁sub hB₁sub
    have hA₁ne : A₁.Nonempty := by
      rw [← Finset.card_pos, hA₁eqB₁]; exact hB₁ne.card_pos
    have hdeg' : ∀ a ∈ A₁, k ≤ G'.degree a := fun a ha => by
      have h1 := hdeg a (hA₁sub ha)
      have h2 := hG'deg a ha
      omega
    obtain ⟨As', Bs', Ms', hAs0, hBs0, hanti', hprop', hdisjM'⟩ :=
      ih G' A₁ B₁ hdisj₁ (le_of_eq hA₁eqB₁.symm) hA₁ne hG'bip hdeg'
    let As : ℕ → Finset V := fun i => match i with | 0 => A₀ | r + 1 => As' r
    let Bs : ℕ → Finset V := fun i => match i with | 0 => B₀ | r + 1 => Bs' r
    let Ms : ℕ → SimpleGraph V := fun i => match i with | 0 => ⊥ | 1 => M₁ | r + 2 => Ms' (r + 1)
    refine ⟨As, Bs, Ms, rfl, rfl, ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        dsimp only [As, Bs]
        rw [hAs0, hBs0]
        exact ⟨hA₁sub, hB₁sub⟩
      | succ r => exact hanti' r (by omega)
    · intro i hi1 hik
      cases i with
      | zero => omega
      | succ r =>
        cases r with
        | zero =>
          dsimp only [As, Bs, Ms]
          rw [hAs0, hBs0]
          exact ⟨hB₁ne, hA₁eqB₁, hM₁le, hM₁bip, hM₁degA, hM₁degB⟩
        | succ r' =>
          dsimp only [As, Bs, Ms]
          obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hprop' (r' + 1) (by omega) (by omega)
          exact ⟨p1, p2, p3.trans hG'le, p4, p5, p6⟩
    · intro i j hi1 hij hjk u v hMi hMj
      cases i with
      | zero => omega
      | succ r =>
        cases j with
        | zero => omega
        | succ s =>
          cases r with
          | zero =>
            cases s with
            | zero => omega
            | succ s' =>
              dsimp only [Ms] at hMi hMj
              have hle := (hprop' (s' + 1) (by omega) (by omega)).2.2.1
              exact hM₁G' u v hMi (hle hMj)
          | succ r' =>
            cases s with
            | zero => omega
            | succ s' =>
              dsimp only [Ms] at hMi hMj
              exact hdisjM' (r' + 1) (s' + 1) (by omega) (by omega) (by omega) u v hMi hMj

lemma antitone_of_step {α : Type*} {f : ℕ → Finset α} {k : ℕ}
    (h : ∀ i, i < k → f (i + 1) ⊆ f i) : ∀ {i j}, i ≤ j → j ≤ k → f j ⊆ f i := by
  intro i j hij hjk
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact Finset.Subset.refl _
  | succ m ih =>
    by_cases him : i ≤ m
    · exact (h m (by omega)).trans (ih him (by omega))
    · have : i = m + 1 := by omega
      subst this; exact Finset.Subset.refl _

end Step3Pyber

section Step4Regularize

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Step 4 (Bucic et al. arXiv:1809.01468 Lemma 2.1): Extract a bipartite subgraph `G₂` on `V₂`
    with `Δ(G₂) ≤ x + 1` and `2*(x+1) ≤ 3 * d(G₂)` where `x = (δ - 1) / L`. -/
lemma exists_regularized_bipartite (G₁ : SimpleGraph V) (A₁ B₁ : Finset V) (δ L : ℕ)
    (hdisj : Disjoint A₁ B₁)
    (hcard : B₁.card ≤ A₁.card)
    (hAne : A₁.Nonempty)
    (hbip : ∀ u v, G₁.Adj u v → (u ∈ A₁ ∧ v ∈ B₁) ∨ (v ∈ A₁ ∧ u ∈ B₁))
    (hdeg : ∀ a ∈ A₁, δ ≤ G₁.degree a)
    (hδ : 1 ≤ δ)
    (hLpos : 1 ≤ L)
    (hLpow : Fintype.card V ≤ 2 ^ L) :
    let x := (δ - 1) / L
    ∃ V₂ : Finset V, ∃ G₂ : SimpleGraph V,
      V₂.Nonempty ∧
      G₂ ≤ G₁ ∧
      (∀ u v, G₂.Adj u v → u ∈ V₂ ∧ v ∈ V₂) ∧
      (∀ v, G₂.degree v ≤ x + 1) ∧
      (2 * ((x + 1 : ℕ) : ℝ) / 3 ≤ 2 * (G₂.edgeFinset.card : ℝ) / (V₂.card : ℝ)) := by
  intro x
  obtain ⟨As, Bs, Ms, hAs0, hBs0, hstep, hprop, hdisjM⟩ :=
    pyber_matchings G₁ A₁ B₁ δ hdisj hcard hAne hbip hdeg
  have hAanti : ∀ {i j}, i ≤ j → j ≤ δ → As j ⊆ As i :=
    antitone_of_step (fun i hi => (hstep i hi).1)
  have hBanti : ∀ {i j}, i ≤ j → j ≤ δ → Bs j ⊆ Bs i :=
    antitone_of_step (fun i hi => (hstep i hi).2)
  have hLx : 1 + L * x ≤ δ := by
    have hmul : L * x ≤ δ - 1 := Nat.mul_div_le (δ - 1) L
    omega
  -- Pigeonhole: find j < L with |Bs (1 + j*x)| ≤ 2 * |Bs (1 + (j+1)*x)|
  have hex_j : ∃ j < L, (Bs (1 + j * x)).card ≤ 2 * (Bs (1 + (j + 1) * x)).card := by
    by_contra hno
    push Not at hno
    have hgrow : ∀ r ≤ L, 2 ^ r * (Bs (1 + L * x)).card ≤ (Bs (1 + (L - r) * x)).card := by
      intro r hr
      induction r with
      | zero => simp
      | succ r ih =>
        have hrL : r < L := by omega
        have hih := ih (by omega)
        have hlt := hno (L - (r + 1)) (by omega)
        have heq : L - (r + 1) + 1 = L - r := by omega
        rw [heq] at hlt
        rw [pow_succ', mul_assoc]
        omega
    have hstrict : 2 ^ L * (Bs (1 + L * x)).card < (Bs 1).card := by
      have h1 := hgrow (L - 1) (by omega)
      have heq1 : L - (L - 1) = 1 := by omega
      rw [heq1, one_mul] at h1
      have h0 := hno 0 (by omega)
      simp only [zero_mul, add_zero, zero_add, one_mul] at h0
      have hpow : 2 ^ L = 2 * 2 ^ (L - 1) := by
        conv_lhs => rw [show L = (L - 1) + 1 by omega, pow_succ']
      rw [hpow, mul_assoc]
      omega
    have hneL : 1 ≤ (Bs (1 + L * x)).card :=
      (hprop (1 + L * x) (by omega) hLx).1.card_pos
    have hB1le : (Bs 1).card ≤ Fintype.card V := Finset.card_le_univ _
    have : Fintype.card V ≤ 2 ^ L * (Bs (1 + L * x)).card :=
      hLpow.trans (Nat.le_mul_of_pos_right _ hneL)
    omega
  obtain ⟨j, hjL, hBq⟩ := hex_j
  set q := 1 + j * x with hqdef
  have hq1 : 1 ≤ q := by omega
  have hqx : q + x ≤ δ := by
    have : (j + 1) * x ≤ L * x := Nat.mul_le_mul_right x (by omega)
    have : q + x = 1 + (j + 1) * x := by rw [hqdef]; ring
    omega
  have hqδ : q ≤ δ := le_trans (Nat.le_add_right q x) hqx
  have hBq' : (Bs q).card ≤ 2 * (Bs (q + x)).card := by
    have : q + x = 1 + (j + 1) * x := by rw [hqdef]; ring
    rwa [this]
  let Aq := As q
  let Bqx := Bs (q + x)
  let V₂ := Aq ∪ Bqx
  have hdisj₂ : Disjoint Aq Bqx :=
    hdisj.mono ((hAanti (Nat.zero_le q) hqδ).trans (by rw [hAs0]))
      ((hBanti (Nat.zero_le (q + x)) hqx).trans (by rw [hBs0]))
  have hBqx_ne : Bqx.Nonempty := (hprop (q + x) (Nat.le_trans hq1 (Nat.le_add_right q x)) hqx).1
  have hV₂_ne : V₂.Nonempty := hBqx_ne.mono Finset.subset_union_right
  obtain ⟨G₂, hG₂adj⟩ : ∃ G₂ : SimpleGraph V, ∀ u v, G₂.Adj u v ↔
      ((u ∈ Aq ∧ v ∈ Bqx) ∨ (v ∈ Aq ∧ u ∈ Bqx)) ∧
      ∃ r ∈ Finset.Icc q (q + x), (Ms r).Adj u v :=
    ⟨{ Adj := fun u v =>
         ((u ∈ Aq ∧ v ∈ Bqx) ∨ (v ∈ Aq ∧ u ∈ Bqx)) ∧
         ∃ r ∈ Finset.Icc q (q + x), (Ms r).Adj u v
       symm := ⟨fun _ _ ⟨h1, r, hr, hadj⟩ => ⟨h1.symm, r, hr, hadj.symm⟩⟩
       loopless := ⟨fun v ⟨_, r, hr, hadj⟩ => (Ms r).loopless.irrefl v hadj⟩ },
     fun _ _ => Iff.rfl⟩
  have hG₂_le : G₂ ≤ G₁ := by
    intro u v h
    obtain ⟨_, r, hr, hadj⟩ := (hG₂adj u v).mp h
    have hr1 : 1 ≤ r := by have := (Finset.mem_Icc.mp hr).1; omega
    have hrδ : r ≤ δ := by have := (Finset.mem_Icc.mp hr).2; omega
    exact (hprop r hr1 hrδ).2.2.1 hadj
  have hG₂_bip : ∀ u v, G₂.Adj u v → (u ∈ Aq ∧ v ∈ Bqx) ∨ (v ∈ Aq ∧ u ∈ Bqx) :=
    fun u v h => ((hG₂adj u v).mp h).1
  have hG₂_supp : ∀ u v, G₂.Adj u v → u ∈ V₂ ∧ v ∈ V₂ := by
    intro u v h
    rcases hG₂_bip u v h with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact ⟨Finset.mem_union_left _ hu, Finset.mem_union_right _ hv⟩
    · exact ⟨Finset.mem_union_right _ hu, Finset.mem_union_left _ hv⟩
  have hdeg_le : ∀ v, G₂.degree v ≤ x + 1 := by
    intro v
    rw [← card_neighborFinset_eq_degree]
    have hsub : G₂.neighborFinset v ⊆ (Finset.Icc q (q + x)).biUnion (fun r => (Ms r).neighborFinset v) := by
      intro w hw
      obtain ⟨_, r, hr, hadj⟩ := (hG₂adj v w).mp ((mem_neighborFinset G₂ v w).mp hw)
      exact Finset.mem_biUnion.mpr ⟨r, hr, (mem_neighborFinset (Ms r) v w).mpr hadj⟩
    have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 : ∑ r ∈ Finset.Icc q (q + x), ((Ms r).neighborFinset v).card ≤
        ∑ _r ∈ Finset.Icc q (q + x), 1 := by
      refine Finset.sum_le_sum (fun r hr => ?_)
      rw [card_neighborFinset_eq_degree]
      have hr1 : 1 ≤ r := by have := (Finset.mem_Icc.mp hr).1; omega
      have hrδ : r ≤ δ := by have := (Finset.mem_Icc.mp hr).2; omega
      have hp := hprop r hr1 hrδ
      by_cases hvA : v ∈ As r
      · rw [hp.2.2.2.2.1 v hvA]
      · by_cases hvB : v ∈ Bs r
        · rw [hp.2.2.2.2.2 v hvB]
        · have : (Ms r).degree v = 0 := by
            rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero,
              Finset.eq_empty_iff_forall_notMem]
            intro w hw
            rcases hp.2.2.2.1 v w ((mem_neighborFinset (Ms r) v w).mp hw) with ⟨h, _⟩ | ⟨_, h⟩
            · exact hvA h
            · exact hvB h
          omega
    have h3 : (∑ _r ∈ Finset.Icc q (q + x), 1) = x + 1 := by
      rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc, add_assoc, Nat.add_sub_cancel_left]
    omega
  have hdegB : ∀ b ∈ Bqx, G₂.degree b = x + 1 := by
    intro b hb
    rw [← card_neighborFinset_eq_degree]
    have heq : G₂.neighborFinset b = (Finset.Icc q (q + x)).biUnion (fun r => (Ms r).neighborFinset b) := by
      ext w
      simp only [mem_neighborFinset, Finset.mem_biUnion, hG₂adj]
      constructor
      · rintro ⟨_, r, hr, hadj⟩; exact ⟨r, hr, hadj⟩
      · rintro ⟨r, hr, hadj⟩
        have hrq : q ≤ r := (Finset.mem_Icc.mp hr).1
        have hrqx : r ≤ q + x := (Finset.mem_Icc.mp hr).2
        have hrδ : r ≤ δ := le_trans hrqx hqx
        have hp := hprop r (by omega) hrδ
        have hbr : b ∈ Bs r := hBanti hrqx hqx hb
        have hdisj_r : Disjoint (As r) (Bs r) :=
          hdisj.mono ((hAanti (Nat.zero_le r) hrδ).trans (by rw [hAs0]))
            ((hBanti (Nat.zero_le r) hrδ).trans (by rw [hBs0]))
        have hwAr : w ∈ As r := by
          rcases hp.2.2.2.1 b w hadj with ⟨hbA, _⟩ | ⟨hwA, _⟩
          · exact absurd hbA (Finset.disjoint_right.mp hdisj_r hbr)
          · exact hwA
        exact ⟨Or.inr ⟨hAanti hrq hrδ hwAr, hb⟩, r, hr, hadj⟩
    rw [heq, Finset.card_biUnion]
    · have hsum : ∑ r ∈ Finset.Icc q (q + x), ((Ms r).neighborFinset b).card =
          ∑ _r ∈ Finset.Icc q (q + x), 1 := by
        refine Finset.sum_congr rfl (fun r hr => ?_)
        have hr1 : 1 ≤ r := by have := (Finset.mem_Icc.mp hr).1; omega
        have hrqx : r ≤ q + x := (Finset.mem_Icc.mp hr).2
        rw [card_neighborFinset_eq_degree]
        exact (hprop r hr1 (le_trans hrqx hqx)).2.2.2.2.2 b (hBanti hrqx hqx hb)
      rw [hsum, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc, add_assoc, Nat.add_sub_cancel_left]
    · intro r1 hr1 r2 hr2 hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      have h1 := (mem_neighborFinset (Ms r1) b w).mp hw1
      have h2 := (mem_neighborFinset (Ms r2) b w).mp hw2
      have hr1' := Finset.mem_Icc.mp hr1
      have hr2' := Finset.mem_Icc.mp hr2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hdisjM r1 r2 (by omega) hlt (by omega) b w h1 h2
      · exact hdisjM r2 r1 (by omega) hgt (by omega) b w h2 h1
  have hedge : G₂.edgeFinset.card = (x + 1) * Bqx.card := by
    rw [bipartite_edge_card_eq_sum_degree hdisj₂ hG₂_bip]
    rw [Finset.sum_congr rfl hdegB, Finset.sum_const, smul_eq_mul, mul_comm]
  have hV₂card : V₂.card ≤ 3 * Bqx.card := by
    rw [Finset.card_union_of_disjoint hdisj₂]
    have hAqeq : Aq.card = (Bs q).card := (hprop q hq1 hqδ).2.1
    change Aq.card + (Bs (q + x)).card ≤ 3 * (Bs (q + x)).card
    omega
  refine ⟨V₂, G₂, hV₂_ne, hG₂_le, hG₂_supp, hdeg_le, ?_⟩
  have hV₂pos : (0 : ℝ) < V₂.card := by exact_mod_cast hV₂_ne.card_pos
  have hBpos : (0 : ℝ) < Bqx.card := by exact_mod_cast hBqx_ne.card_pos
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hV₂pos]
  have h1 : (G₂.edgeFinset.card : ℝ) = ((x + 1 : ℕ) : ℝ) * (Bqx.card : ℝ) := by
    exact_mod_cast hedge
  have h2 : (V₂.card : ℝ) ≤ 3 * (Bqx.card : ℝ) := by exact_mod_cast hV₂card
  rw [h1]
  nlinarith

end Step4Regularize

section Step5Expander

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Step 5: Single-shot maximizer of `2 * e(G₂[U]) * |U| ^ (-(1 + α))` extracts a dense,
    minimum-degree-controlled edge-expanding induced subgraph. -/
lemma extract_expander (G₂ : SimpleGraph V) (V₂ : Finset V) (α : ℝ)
    (hV₂ne : V₂.Nonempty)
    (hsupp : ∀ u v, G₂.Adj u v → u ∈ V₂ ∧ v ∈ V₂)
    (hepos : 0 < G₂.edgeFinset.card)
    (hα : 0 < α) :
    ∃ U : Finset V,
      U ⊆ V₂ ∧ U.Nonempty ∧
      let H := induceOn G₂ U
      let dH : ℝ := 2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ)
      let d₂ : ℝ := 2 * (G₂.edgeFinset.card : ℝ) / (V₂.card : ℝ)
      (d₂ * (V₂.card : ℝ) ^ (-α) ≤ dH) ∧
      (∀ v ∈ U, dH / 2 ≤ (H.degree v : ℝ)) ∧
      (∀ S ⊆ U, 2 * S.card ≤ U.card →
        ((1 - (2 : ℝ) ^ (-α)) / 2) * dH * (S.card : ℝ) ≤
          ((cutEdges H S (U \ S)).card : ℝ)) := by
  let nonEmptySubs : Finset (Finset V) := V₂.powerset.filter Finset.Nonempty
  have hV₂mem : V₂ ∈ nonEmptySubs :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset_self V₂, hV₂ne⟩
  let Φ (U : Finset V) : ℝ :=
    (2 * ((induceOn G₂ U).edgeFinset.card : ℝ)) * (U.card : ℝ) ^ (-(1 + α))
  obtain ⟨U, hUmem, hUmax⟩ := Finset.exists_max_image nonEmptySubs Φ ⟨V₂, hV₂mem⟩
  have hUsub : U ⊆ V₂ := Finset.mem_powerset.mp (Finset.mem_filter.mp hUmem).1
  have hUne : U.Nonempty := (Finset.mem_filter.mp hUmem).2
  set H := induceOn G₂ U with hHdef
  have hUpos : (0 : ℝ) < U.card := by exact_mod_cast hUne.card_pos
  have hV₂pos : (0 : ℝ) < V₂.card := by exact_mod_cast hV₂ne.card_pos
  have hΦ_eq : ∀ W : Finset V, W.Nonempty →
      Φ W = (2 * ((induceOn G₂ W).edgeFinset.card : ℝ) / (W.card : ℝ)) * (W.card : ℝ) ^ (-α) := by
    intro W hW
    have hWp : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
    dsimp only [Φ]
    rw [show -(1 + α) = -1 + (-α) by ring, Real.rpow_add hWp, Real.rpow_neg_one]
    ring
  have hG₂_eq : induceOn G₂ V₂ = G₂ := by
    ext u v
    simp only [induceOn]
    exact ⟨fun h => h.1, fun h => ⟨h, hsupp u v h⟩⟩
  have hΦ_ge : Φ V₂ ≤ Φ U := hUmax V₂ hV₂mem
  -- 1. Average degree bound
  have hd_ge : (2 * (G₂.edgeFinset.card : ℝ) / (V₂.card : ℝ)) * (V₂.card : ℝ) ^ (-α) ≤
      2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ) := by
    rw [hΦ_eq V₂ hV₂ne, hΦ_eq U hUne, hG₂_eq] at hΦ_ge
    have hUge1 : (1 : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast hUne.card_pos
    have hUpow : (U.card : ℝ) ^ (-α) ≤ 1 := by
      rw [Real.rpow_neg hUpos.le]
      exact inv_le_one_of_one_le₀ (Real.one_le_rpow hUge1 hα.le)
    have hHnn : 0 ≤ 2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ) := by positivity
    calc (2 * (G₂.edgeFinset.card : ℝ) / (V₂.card : ℝ)) * (V₂.card : ℝ) ^ (-α)
        ≤ (2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ)) * (U.card : ℝ) ^ (-α) := hΦ_ge
      _ ≤ (2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hUpow hHnn
      _ = 2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ) := mul_one _
  have hHpos : 0 < H.edgeFinset.card := by
    have h0 : (0 : ℝ) < (2 * (G₂.edgeFinset.card : ℝ) / (V₂.card : ℝ)) * (V₂.card : ℝ) ^ (-α) := by
      positivity
    have h1 : (0 : ℝ) < 2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ) := lt_of_lt_of_le h0 hd_ge
    have h2 : (0 : ℝ) < H.edgeFinset.card := by
      have := (div_pos_iff_of_pos_right hUpos).mp h1
      linarith
    exact_mod_cast h2
  have hU2 : 2 ≤ U.card := by
    by_contra hlt
    have h1 : U.card = 1 := by have := hUne.card_pos; omega
    obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨e, he⟩ := Finset.card_pos.mp hHpos
    refine Sym2.inductionOn e (fun a b he => ?_) he
    rw [hHdef, mem_induceOn_edgeFinset, Finset.mem_singleton, Finset.mem_singleton] at he
    obtain ⟨hadj, rfl, hbw⟩ := he
    exact G₂.loopless.irrefl a (hbw ▸ hadj)
  -- Helper: Φ(W) ≤ Φ(U) implies 2*e(W) ≤ dH * |W| * (|W| / |U|)^α
  have hsub_bound : ∀ W ⊆ U, W.Nonempty →
      2 * ((induceOn H W).edgeFinset.card : ℝ) ≤
        (2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ)) * (W.card : ℝ) *
          ((W.card : ℝ) / (U.card : ℝ)) ^ α := by
    intro W hWU hWne
    have hWmem : W ∈ nonEmptySubs :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hWU.trans hUsub), hWne⟩
    have hm := hUmax W hWmem
    have hWpos : (0 : ℝ) < W.card := by exact_mod_cast hWne.card_pos
    have hind : induceOn H W = induceOn G₂ W := by
      ext x y
      simp only [induceOn, H]
      exact ⟨fun ⟨⟨h, _, _⟩, hx, hy⟩ => ⟨h, hx, hy⟩,
        fun ⟨h, hx, hy⟩ => ⟨⟨h, hWU hx, hWU hy⟩, hx, hy⟩⟩
    rw [hind]
    rw [hΦ_eq W hWne, hΦ_eq U hUne] at hm
    have hpowW : 0 < (W.card : ℝ) ^ α := Real.rpow_pos_of_pos hWpos α
    have hdiv : ((W.card : ℝ) / (U.card : ℝ)) ^ α = (W.card : ℝ) ^ α * (U.card : ℝ) ^ (-α) := by
      rw [Real.div_rpow hWpos.le hUpos.le, Real.rpow_neg hUpos.le, div_eq_mul_inv]
    rw [hdiv]
    have hm' : (2 * ((induceOn G₂ W).edgeFinset.card : ℝ) / (W.card : ℝ)) ≤
        (2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ)) * (U.card : ℝ) ^ (-α) * (W.card : ℝ) ^ α := by
      rw [Real.rpow_neg hWpos.le] at hm
      have := mul_le_mul_of_nonneg_right hm hpowW.le
      rw [mul_assoc, inv_mul_cancel₀ hpowW.ne', mul_one] at this
      exact this
    have hmul := (div_le_iff₀ hWpos).mp hm'
    linarith
  -- 2. Minimum degree bound
  have hminDeg : ∀ v ∈ U, (2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ)) / 2 ≤ (H.degree v : ℝ) := by
    intro v hv
    have hne' : (U.erase v).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hv]; omega
    have hb := hsub_bound (U.erase v) (Finset.erase_subset v U) hne'
    have hratio_le : ((U.erase v).card : ℝ) / (U.card : ℝ) ≤ 1 := by
      rw [div_le_one hUpos]
      exact_mod_cast Finset.card_le_card (Finset.erase_subset v U)
    have hratio_nn : 0 ≤ ((U.erase v).card : ℝ) / (U.card : ℝ) := by positivity
    have hpow_le : (((U.erase v).card : ℝ) / (U.card : ℝ)) ^ α ≤ 1 :=
      Real.rpow_le_one hratio_nn hratio_le hα.le
    have hHnn : 0 ≤ (2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ)) * ((U.erase v).card : ℝ) := by
      positivity
    have hb' : 2 * ((induceOn H (U.erase v)).edgeFinset.card : ℝ) ≤
        (2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ)) * ((U.erase v).card : ℝ) :=
      hb.trans (by nlinarith)
    have hedge_er := edgeFinset_erase_add_degree (G := H) (U := U) (v := v) (fun _ _ h => h.2) hv
    have hreal_er : ((induceOn H (U.erase v)).edgeFinset.card : ℝ) =
        (H.edgeFinset.card : ℝ) - (H.degree v : ℝ) := by
      have : ((induceOn H (U.erase v)).edgeFinset.card : ℝ) + (H.degree v : ℝ) =
          (H.edgeFinset.card : ℝ) := by exact_mod_cast hedge_er
      linarith
    have hcard_er : ((U.erase v).card : ℝ) = (U.card : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem hv, Nat.cast_sub (by omega : 1 ≤ U.card)]; simp
    rw [hreal_er, hcard_er] at hb'
    have hmul : (2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ)) * ((U.card : ℝ) - 1) =
        2 * (H.edgeFinset.card : ℝ) - 2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ) := by
      field_simp [hUpos.ne']
    rw [hmul] at hb'
    linarith
  -- 3. Edge expansion bound
  have hexp : ∀ S ⊆ U, 2 * S.card ≤ U.card →
      ((1 - (2 : ℝ) ^ (-α)) / 2) * (2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ)) * (S.card : ℝ) ≤
        ((cutEdges H S (U \ S)).card : ℝ) := by
    intro S hSU hScard
    by_cases hSe : S = ∅
    · subst hSe; simp
    · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSe
      have hTne : (U \ S).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff_of_subset hSU]
        have := hSne.card_pos; omega
      have hbS := hsub_bound S hSU hSne
      have hbT := hsub_bound (U \ S) Finset.sdiff_subset hTne
      have hratioS : (S.card : ℝ) / (U.card : ℝ) ≤ (1 : ℝ) / 2 := by
        rw [div_le_div_iff₀ hUpos (by norm_num : (0 : ℝ) < 2)]
        have : (2 : ℝ) * (S.card : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast hScard
        linarith
      have hpowS : ((S.card : ℝ) / (U.card : ℝ)) ^ α ≤ (2 : ℝ) ^ (-α) := by
        have h1 : ((S.card : ℝ) / (U.card : ℝ)) ^ α ≤ ((1 : ℝ) / 2) ^ α :=
          Real.rpow_le_rpow (by positivity) hratioS hα.le
        have h2 : ((1 : ℝ) / 2) ^ α = (2 : ℝ) ^ (-α) := by
          rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        rwa [h2] at h1
      have hratioT : ((U \ S).card : ℝ) / (U.card : ℝ) ≤ 1 := by
        rw [div_le_one hUpos]
        exact_mod_cast Finset.card_le_card Finset.sdiff_subset
      have hpowT : (((U \ S).card : ℝ) / (U.card : ℝ)) ^ α ≤ 1 :=
        Real.rpow_le_one (by positivity) hratioT hα.le
      set dH : ℝ := 2 * (H.edgeFinset.card : ℝ) / (U.card : ℝ) with hdHdef
      have hdHnn : 0 ≤ dH := by positivity
      have hbS' : 2 * ((induceOn H S).edgeFinset.card : ℝ) ≤ dH * (S.card : ℝ) * (2 : ℝ) ^ (-α) :=
        hbS.trans (mul_le_mul_of_nonneg_left hpowS (by positivity))
      have hbT' : 2 * ((induceOn H (U \ S)).edgeFinset.card : ℝ) ≤ dH * ((U \ S).card : ℝ) := by
        have hmulT := mul_le_mul_of_nonneg_left hpowT (by positivity : 0 ≤ dH * ((U \ S).card : ℝ))
        rw [mul_one] at hmulT
        exact hbT.trans hmulT
      have hsplit := edgeFinset_eq_induce_union_cut (G := H) (U := U) (S := S)
        (fun _ _ h => h.2) hSU
      have hsplitR : (H.edgeFinset.card : ℝ) =
          ((induceOn H S).edgeFinset.card : ℝ) +
          ((induceOn H (U \ S)).edgeFinset.card : ℝ) +
          ((cutEdges H S (U \ S)).card : ℝ) := by exact_mod_cast hsplit
      have hcardST : (S.card : ℝ) + ((U \ S).card : ℝ) = (U.card : ℝ) := by
        have := Finset.card_sdiff_add_card_eq_card hSU
        have : ((U \ S).card : ℝ) + (S.card : ℝ) = (U.card : ℝ) := by exact_mod_cast this
        linarith
      have h2eH : 2 * (H.edgeFinset.card : ℝ) = dH * (U.card : ℝ) := by
        rw [hdHdef]; field_simp [hUpos.ne']
      have hmulST : dH * (S.card : ℝ) + dH * ((U \ S).card : ℝ) = dH * (U.card : ℝ) := by
        rw [← mul_add, hcardST]
      have hlhs : ((1 - (2 : ℝ) ^ (-α)) / 2) * dH * (S.card : ℝ) =
          (dH * (S.card : ℝ) - dH * (S.card : ℝ) * (2 : ℝ) ^ (-α)) / 2 := by ring
      linarith
  exact ⟨U, hUsub, hUne, hd_ge, hminDeg, hexp⟩

end Step5Expander

section AnalyticBounds

lemma ten_le_log_of_ge {n : ℕ} (hn : 30000 ≤ n) : (10 : ℝ) ≤ Real.log n := by
  have h1 : Real.exp 1 < (2.72 : ℝ) := by
    have := Real.exp_one_lt_d9; linarith
  have h10 : Real.exp 10 < (30000 : ℝ) := by
    have he : Real.exp 10 = (Real.exp 1) ^ 10 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    have hpow : (Real.exp 1) ^ 10 < (2.72 : ℝ) ^ 10 :=
      pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
    have hnum : (2.72 : ℝ) ^ 10 < 30000 := by norm_num
    linarith
  have hnR : (30000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hexp_le : Real.exp 10 ≤ (n : ℝ) := by linarith
  have := Real.log_le_log (Real.exp_pos 10) hexp_le
  rwa [Real.log_exp] at this

lemma nat_log_two_succ_le {n : ℕ} (hn : 30000 ≤ n) :
    ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 2 * Real.log n := by
  have hlog10 := ten_le_log_of_ge hn
  have hn0 : n ≠ 0 := by omega
  have hpow : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hn0
  have hlogpow : ((Nat.log 2 n : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
    have := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 n)) hpow
    rwa [Real.log_pow] at this
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  push_cast
  nlinarith

lemma rpow_neg_one_third_log_ge {n : ℕ} (hn : 30000 ≤ n) :
    (1 : ℝ) / 2 ≤ (n : ℝ) ^ (-(1 / (3 * Real.log n))) := by
  have hlog10 := ten_le_log_of_ge hn
  have hlogpos : 0 < Real.log n := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have heq : (n : ℝ) ^ (-(1 / (3 * Real.log n))) = Real.exp (-(1 / 3 : ℝ)) := by
    rw [Real.rpow_def_of_pos hnpos]
    congr 1
    field_simp [hlogpos.ne']
  rw [heq, Real.exp_neg]
  rw [one_div]
  refine inv_anti₀ (Real.exp_pos _) ?_
  have he1 : Real.exp 1 < 8 := by
    have := Real.exp_one_lt_d9; linarith
  have h3 : (Real.exp (1 / 3 : ℝ)) ^ 3 < (2 : ℝ) ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
    exact he1
  by_contra hgt
  rw [not_le] at hgt
  have : (2 : ℝ) ^ 3 < (Real.exp (1 / 3 : ℝ)) ^ 3 :=
    pow_lt_pow_left₀ hgt (by norm_num) (by norm_num)
  linarith

lemma expansion_const_ge {n : ℕ} (hn : 30000 ≤ n) :
    1 / (10 * Real.log n) ≤ (1 - (2 : ℝ) ^ (-(1 / (3 * Real.log n)))) / 2 := by
  have hlog10 := ten_le_log_of_ge hn
  have hlogpos : 0 < Real.log n := by linarith
  set y : ℝ := Real.log 2 / (3 * Real.log n) with hydef
  have hlog2_lo : (0.693 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlog2_hi : Real.log 2 < (0.7 : ℝ) := by
    have := Real.log_two_lt_d9; linarith
  have hy_pos : 0 < y := by positivity
  have h2pow : (2 : ℝ) ^ (-(1 / (3 * Real.log n))) = Real.exp (-y) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [hydef]; ring
  rw [h2pow]
  have hexp_ge : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hinv_le : Real.exp (-y) ≤ 1 / (1 + y) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by linarith) hexp_ge
  have h1my : y / (1 + y) ≤ 1 - Real.exp (-y) := by
    have hsub : 1 - 1 / (1 + y) = y / (1 + y) := by
      field_simp [show (1 + y : ℝ) ≠ 0 by linarith]
      ring
    linarith
  have hy_hi : y < (0.05 : ℝ) := by
    rw [hydef, div_lt_iff₀ (by linarith : (0 : ℝ) < 3 * Real.log n)]
    nlinarith
  have hstep : 1 / (5 * Real.log n) ≤ y / (1 + y) := by
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 5 * Real.log n) (by linarith : (0 : ℝ) < 1 + y)]
    have hy_mul : 3 * Real.log n * y = Real.log 2 := by
      rw [hydef]; field_simp [hlogpos.ne']
    nlinarith
  have hhalf : 1 / (10 * Real.log n) = (1 / (5 * Real.log n)) / 2 := by ring
  linarith

end AnalyticBounds

section Reindex

/-- Reindex an induced subgraph `H₀` supported on `U : Finset (Fin n)` to a `SimpleGraph (Fin m)`
    with `m = U.card`, preserving injectivity, bipartiteness, degrees, edge count, and cuts. -/
lemma reindex_expander {n : ℕ} (G G₀ H₀ : SimpleGraph (Fin n))
    (A U : Finset (Fin n)) (c : ℝ)
    (hUne : U.Nonempty)
    (hH₀leG : H₀ ≤ G)
    (hH₀leG₀ : H₀ ≤ G₀)
    (hG₀bip : ∀ u v, G₀.Adj u v → (u ∈ A ↔ v ∉ A))
    (hH₀supp : ∀ u v, H₀.Adj u v → u ∈ U ∧ v ∈ U)
    (hregH₀ : ∀ u ∈ U, ∀ v ∈ U, H₀.degree u ≤ 100 * H₀.degree v)
    (hexpU : ∀ S ⊆ U, 2 * S.card ≤ U.card →
      c * (2 * (H₀.edgeFinset.card : ℝ) / (U.card : ℝ)) * (S.card : ℝ) ≤
        ((cutEdges H₀ S (U \ S)).card : ℝ)) :
    ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ ∃ H : SimpleGraph (Fin m), ∃ f : H →g G,
      Function.Injective f ∧ H.IsBipartite ∧
      (∀ u v : Fin m, (H.neighborSet u).ncard ≤ 100 * (H.neighborSet v).ncard) ∧
      (2 * (H₀.edgeFinset.card : ℝ) / (U.card : ℝ) = 2 * (H.edgeSet.ncard : ℝ) / (m : ℝ)) ∧
      (∀ S : Finset (Fin m), 2 * S.card ≤ m →
        c * (2 * (H.edgeSet.ncard : ℝ) / (m : ℝ)) * (S.card : ℝ) ≤
          ({e ∈ H.edgeSet | ∃ u v : Fin m, u ∈ S ∧ v ∉ S ∧ e = s(u, v)}.ncard : ℝ)) := by
  let m : ℕ := U.card
  let e : Fin m ≃ U := U.equivFin.symm
  let emb : Fin m ↪ Fin n :=
    ⟨fun i => (e i).val, fun i j hij => e.injective (Subtype.ext hij)⟩
  have hemb_symm : ∀ (w : Fin n) (hw : w ∈ U), emb (e.symm ⟨w, hw⟩) = w := by
    intro w hw
    change (e (e.symm ⟨w, hw⟩)).val = w
    simp
  obtain ⟨H, hHadj⟩ : ∃ H : SimpleGraph (Fin m), ∀ i j, H.Adj i j ↔ H₀.Adj (emb i) (emb j) :=
    ⟨{ Adj := fun i j => H₀.Adj (emb i) (emb j)
       symm := ⟨fun _ _ h => h.symm⟩
       loopless := ⟨fun i h => H₀.loopless.irrefl _ h⟩ },
     fun _ _ => Iff.rfl⟩
  let f : H →g G := ⟨emb, fun h => hH₀leG ((hHadj _ _).mp h)⟩
  have hfinj : Function.Injective f := emb.injective
  have hH_bip : H.IsBipartite := by
    refine ⟨SimpleGraph.Coloring.mk (fun i => if emb i ∈ A then (0 : Fin 2) else 1) ?_⟩
    intro i j hij
    have h0 : G₀.Adj (emb i) (emb j) := hH₀leG₀ ((hHadj i j).mp hij)
    have hiff := hG₀bip (emb i) (emb j) h0
    split_ifs <;> simp_all
  have hdeg_eq : ∀ i : Fin m, (H.neighborSet i).ncard = H₀.degree (emb i) := by
    intro i
    rw [← SimpleGraph.coe_neighborFinset, Set.ncard_coe_finset, ← card_neighborFinset_eq_degree]
    refine Finset.card_bij (fun j _ => emb j) ?_ ?_ ?_
    · intro j hj
      exact (mem_neighborFinset H₀ _ _).mpr ((hHadj i j).mp ((mem_neighborFinset H i j).mp hj))
    · intro j1 _ j2 _ heq; exact emb.injective heq
    · intro w hw
      have hadj := (mem_neighborFinset H₀ _ _).mp hw
      have hwU : w ∈ U := (hH₀supp _ _ hadj).2
      refine ⟨e.symm ⟨w, hwU⟩, ?_, hemb_symm w hwU⟩
      rw [mem_neighborFinset, hHadj, hemb_symm w hwU]
      exact hadj
  have hedge_eq : H.edgeSet.ncard = H₀.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    refine Finset.card_bij (fun x _ => Sym2.map emb x) ?_ ?_ ?_
    · intro x hx
      refine Sym2.inductionOn x (fun i j hx => ?_) hx
      rw [Sym2.map_mk, mem_edgeFinset, mem_edgeSet]
      exact (hHadj i j).mp (mem_edgeFinset.mp hx)
    · intro x1 _ x2 _ heq; exact Sym2.map.injective emb.injective heq
    · intro y hy
      refine Sym2.inductionOn y (fun u v hy => ?_) hy
      have hadj : H₀.Adj u v := mem_edgeFinset.mp hy
      obtain ⟨huU, hvU⟩ := hH₀supp u v hadj
      refine ⟨s(e.symm ⟨u, huU⟩, e.symm ⟨v, hvU⟩), ?_, by rw [Sym2.map_mk, hemb_symm, hemb_symm]⟩
      rw [mem_edgeFinset, mem_edgeSet, hHadj, hemb_symm, hemb_symm]
      exact hadj
  refine ⟨m, hUne.card_pos, ?_, H, f, hfinj, hH_bip, ?_, ?_, ?_⟩
  · have : U.card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    rwa [Fintype.card_fin] at this
  · intro i j
    rw [hdeg_eq i, hdeg_eq j]
    exact hregH₀ (emb i) (e i).property (emb j) (e j).property
  · rw [hedge_eq]
  · intro S hScard
    let S' : Finset (Fin n) := S.map emb
    have hS'sub : S' ⊆ U := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      exact (e i).property
    have hS'card : S'.card = S.card := Finset.card_map emb
    have hcut_eq :
        ({e ∈ H.edgeSet | ∃ u v : Fin m, u ∈ S ∧ v ∉ S ∧ e = s(u, v)}).ncard =
        (cutEdges H₀ S' (U \ S')).card := by
      let C : Finset (Sym2 (Fin m)) :=
        H.edgeFinset.filter (fun x => ∃ u v : Fin m, u ∈ S ∧ v ∉ S ∧ x = s(u, v))
      have hCset : (C : Set (Sym2 (Fin m))) =
          {x ∈ H.edgeSet | ∃ u v : Fin m, u ∈ S ∧ v ∉ S ∧ x = s(u, v)} := by
        ext x; simp [C]
      rw [← hCset, Set.ncard_coe_finset]
      refine Finset.card_bij (fun x _ => Sym2.map emb x) ?_ ?_ ?_
      · intro x hx
        refine Sym2.inductionOn x (fun i j hx => ?_) hx
        simp only [C, Finset.mem_filter, mem_edgeFinset, mem_edgeSet] at hx
        obtain ⟨hadj, a, b, ha, hb, heq⟩ := hx
        rw [Sym2.map_mk, mem_cutEdges_mk]
        refine ⟨(hHadj i j).mp hadj, ?_⟩
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine Or.inl ⟨Finset.mem_map.mpr ⟨i, ha, rfl⟩, Finset.mem_sdiff.mpr ⟨(e j).property, ?_⟩⟩
          intro hm
          obtain ⟨k, hk, hkeq⟩ := Finset.mem_map.mp hm
          exact hb ((emb.injective hkeq) ▸ hk)
        · refine Or.inr ⟨Finset.mem_map.mpr ⟨j, ha, rfl⟩, Finset.mem_sdiff.mpr ⟨(e i).property, ?_⟩⟩
          intro hm
          obtain ⟨k, hk, hkeq⟩ := Finset.mem_map.mp hm
          exact hb ((emb.injective hkeq) ▸ hk)
      · intro x1 _ x2 _ heq; exact Sym2.map.injective emb.injective heq
      · intro y hy
        refine Sym2.inductionOn y (fun u v hy => ?_) hy
        obtain ⟨hadj, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩ := mem_cutEdges_mk.mp hy
        · obtain ⟨i, hiS, rfl⟩ := Finset.mem_map.mp hu
          obtain ⟨hvU, hvnot⟩ := Finset.mem_sdiff.mp hv
          let j : Fin m := e.symm ⟨v, hvU⟩
          have hjb : emb j = v := hemb_symm v hvU
          have hjnot : j ∉ S := fun hjS => hvnot (Finset.mem_map.mpr ⟨j, hjS, hjb⟩)
          refine ⟨s(i, j), Finset.mem_filter.mpr ⟨mem_edgeFinset.mpr ((hHadj i j).mpr (by rw [hjb]; exact hadj)),
            i, j, hiS, hjnot, rfl⟩, by rw [Sym2.map_mk, hjb]⟩
        · obtain ⟨j, hjS, rfl⟩ := Finset.mem_map.mp hv
          obtain ⟨huU, hunot⟩ := Finset.mem_sdiff.mp hu
          let i : Fin m := e.symm ⟨u, huU⟩
          have hib : emb i = u := hemb_symm u huU
          have hinot : i ∉ S := fun hiS => hunot (Finset.mem_map.mpr ⟨i, hiS, hib⟩)
          refine ⟨s(j, i), Finset.mem_filter.mpr ⟨mem_edgeFinset.mpr ((hHadj j i).mpr (by rw [hib]; exact hadj.symm)),
            j, i, hjS, hinot, rfl⟩, by rw [Sym2.map_mk, hib, Sym2.eq_swap]⟩
    rw [hedge_eq, hcut_eq]
    have h1 := hexpU S' hS'sub (by rwa [hS'card])
    rwa [hS'card] at h1

end Reindex

end OMA.Erdos642H1

open SimpleGraph Filter Real OMA.Erdos642H1
open scoped Classical

theorem OMA.solution : OMA.R_Erdos642_erdos_642_variants_upper_bound_n_log_pow_eight_R1.H1 := by
  refine eventually_atTop.mpr ⟨30000, fun n hn G havg => ?_⟩
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog10 : (10 : ℝ) ≤ Real.log n := ten_le_log_of_ge hn
  have hlogpos : 0 < Real.log n := by linarith
  set d₀ : ℝ := 2 * (G.edgeSet.ncard : ℝ) / (n : ℝ) with hd₀def
  have hd₀_ge : (100 : ℝ) ≤ d₀ := by nlinarith
  have hG_ncard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  -- Step 1: Bipartite max-cut subgraph G₀
  obtain ⟨A, G₀, hG₀le, hG₀bip, hG₀edges⟩ := exists_bipartite_maxCut G
  have hG₀pos : 0 < G₀.edgeFinset.card := by
    have hGe : (0 : ℝ) < (G.edgeFinset.card : ℝ) := by
      rw [← hG_ncard]
      have : (0 : ℝ) < 2 * (G.edgeSet.ncard : ℝ) / (n : ℝ) := by linarith
      have := (div_pos_iff_of_pos_right hnpos).mp this
      linarith
    have hGeN : 0 < G.edgeFinset.card := by exact_mod_cast hGe
    omega
  -- Step 2: Min-degree bipartite induced subgraph G₁
  obtain ⟨A₁, B₁, G₁, hdisj₁, hcard₁, hA₁ne, hG₁le, hG₁bip, hG₁deg⟩ :=
    exists_minDegree_bipartite G₀ A hG₀bip hG₀pos
  set δ : ℕ := Nat.ceil (d₀ / 4) with hδdef
  have hδ_ge_real : d₀ / 4 ≤ (δ : ℝ) := Nat.le_ceil _
  have hδ_pos : 1 ≤ δ := by
    have : (1 : ℝ) ≤ (δ : ℝ) := by linarith
    exact_mod_cast this
  have hG₁deg_δ : ∀ a ∈ A₁, δ ≤ G₁.degree a := by
    intro a ha
    have h1 := hG₁deg a (Finset.mem_union_left B₁ ha)
    have h2 : d₀ / 4 ≤ (G₀.edgeFinset.card : ℝ) / (Fintype.card (Fin n) : ℝ) := by
      rw [Fintype.card_fin, hd₀def, hG_ncard]
      have hR : (G.edgeFinset.card : ℝ) ≤ 2 * (G₀.edgeFinset.card : ℝ) := by exact_mod_cast hG₀edges
      rw [div_div]
      rw [div_le_div_iff₀ (by positivity) hnpos]
      nlinarith
    exact Nat.ceil_le.mpr (h2.trans h1)
  -- Step 4 (using Step 3): Regularized bipartite subgraph G₂
  set L : ℕ := Nat.log 2 n + 1 with hLdef
  have hLpos : 1 ≤ L := by omega
  have hLpow : Fintype.card (Fin n) ≤ 2 ^ L := by
    rw [Fintype.card_fin]
    exact (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n).le
  obtain ⟨V₂, G₂, hV₂ne, hG₂le, hG₂supp, hG₂deg, hG₂avg⟩ :=
    exists_regularized_bipartite G₁ A₁ B₁ δ L hdisj₁ hcard₁ hA₁ne hG₁bip hG₁deg_δ hδ_pos hLpos hLpow
  set x : ℕ := (δ - 1) / L with hxdef
  have hx1_ge : d₀ / (10 * Real.log n) ≤ ((x + 1 : ℕ) : ℝ) := by
    have hLreal : (L : ℝ) ≤ 2 * Real.log n := nat_log_two_succ_le hn
    have hLposR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
    have hdiv : ((δ - 1 : ℕ) : ℝ) / (L : ℝ) < ((x + 1 : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hLposR]
      have hlt : δ - 1 < (x + 1) * L := by
        have := Nat.lt_div_mul_add (a := δ - 1) (b := L) (by omega : 0 < L)
        rw [add_mul, one_mul]
        exact this
      exact_mod_cast hlt
    have hδ1 : d₀ / 5 ≤ ((δ - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hδ_pos]; simp; linarith
    have hstep : d₀ / (10 * Real.log n) ≤ ((δ - 1 : ℕ) : ℝ) / (L : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hLposR]
      nlinarith
    linarith
  have hd₂_ge : d₀ / (15 * Real.log n) ≤ 2 * (G₂.edgeFinset.card : ℝ) / (V₂.card : ℝ) := by
    have hfrac : d₀ / (15 * Real.log n) = 2 * (d₀ / (10 * Real.log n)) / 3 := by ring
    linarith
  have hG₂pos : 0 < G₂.edgeFinset.card := by
    have hV₂pos : (0 : ℝ) < (V₂.card : ℝ) := by exact_mod_cast hV₂ne.card_pos
    have h0 : (0 : ℝ) < d₀ / (15 * Real.log n) := by positivity
    have h1 : (0 : ℝ) < 2 * (G₂.edgeFinset.card : ℝ) / (V₂.card : ℝ) := lt_of_lt_of_le h0 hd₂_ge
    have h2 : (0 : ℝ) < (G₂.edgeFinset.card : ℝ) := by
      have := (div_pos_iff_of_pos_right hV₂pos).mp h1; linarith
    exact_mod_cast h2
  -- Step 5: Extract expander H₀ on U ⊆ V₂
  set α : ℝ := 1 / (3 * Real.log n) with hαdef
  have hαpos : 0 < α := by positivity
  obtain ⟨U, hUV₂, hUne, hdH_ge_V₂, hminDeg, hexpU⟩ :=
    extract_expander G₂ V₂ α hV₂ne hG₂supp hG₂pos hαpos
  set H₀ := induceOn G₂ U with hH₀def
  set dH₀ : ℝ := 2 * (H₀.edgeFinset.card : ℝ) / (U.card : ℝ) with hdH₀def
  set d₂ : ℝ := 2 * (G₂.edgeFinset.card : ℝ) / (V₂.card : ℝ) with hd₂def
  have hV₂_pow : (1 : ℝ) / 2 ≤ (V₂.card : ℝ) ^ (-α) := by
    have hV₂le : (V₂.card : ℝ) ≤ (n : ℝ) := by
      have : V₂.card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    have hV₂pos : (0 : ℝ) < (V₂.card : ℝ) := by exact_mod_cast hV₂ne.card_pos
    have hmono : (n : ℝ) ^ (-α) ≤ (V₂.card : ℝ) ^ (-α) := by
      rw [Real.rpow_neg hnpos.le, Real.rpow_neg hV₂pos.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hV₂pos α) (Real.rpow_le_rpow hV₂pos.le hV₂le hαpos.le)
    exact (rpow_neg_one_third_log_ge hn).trans hmono
  have hdH₀_ge_half_d₂ : d₂ / 2 ≤ dH₀ := by
    have hd₂nn : 0 ≤ d₂ := by positivity
    have h1 : d₂ * (1 / 2 : ℝ) ≤ d₂ * (V₂.card : ℝ) ^ (-α) :=
      mul_le_mul_of_nonneg_left hV₂_pow hd₂nn
    linarith
  have hdH₀_ge_d₀ : d₀ / (600 * Real.log n) ≤ dH₀ := by
    have hfrac : d₀ / (30 * Real.log n) = (d₀ / (15 * Real.log n)) / 2 := by ring
    have h1 : d₀ / (30 * Real.log n) ≤ dH₀ := by linarith
    have h2 : d₀ / (600 * Real.log n) ≤ d₀ / (30 * Real.log n) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    exact h2.trans h1
  have hregH₀ : ∀ u ∈ U, ∀ v ∈ U, H₀.degree u ≤ 100 * H₀.degree v := by
    intro u hu v hv
    have hdu_le : (H₀.degree u : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by
      have h1 : H₀.degree u ≤ G₂.degree u := by
        rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
        exact Finset.card_le_card (fun w hw =>
          (mem_neighborFinset G₂ u w).mpr ((induceOn_le G₂ U) ((mem_neighborFinset H₀ u w).mp hw)))
      exact_mod_cast h1.trans (hG₂deg u)
    have hdv_ge : dH₀ / 2 ≤ (H₀.degree v : ℝ) := hminDeg v hv
    have hR : (H₀.degree u : ℝ) ≤ 100 * (H₀.degree v : ℝ) := by linarith
    exact_mod_cast hR
  -- Reindex U to Fin m
  have hexpU' : ∀ S ⊆ U, 2 * S.card ≤ U.card →
      (1 / (10 * Real.log n)) * dH₀ * (S.card : ℝ) ≤ ((cutEdges H₀ S (U \ S)).card : ℝ) := by
    intro S hSU hScard
    have h1 := hexpU S hSU hScard
    have h2 := expansion_const_ge hn
    have hdHnn : 0 ≤ dH₀ := by positivity
    have hSnn : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hdHnn) hSnn).trans h1
  have hH₀_le_G₀ : H₀ ≤ G₀ := (induceOn_le G₂ U).trans (hG₂le.trans hG₁le)
  have hH₀_le_G : H₀ ≤ G := hH₀_le_G₀.trans hG₀le
  obtain ⟨m, hmpos, hmle, H, f, hfinj, hH_bip, hH_reg, hH_avg, hH_exp⟩ :=
    reindex_expander G G₀ H₀ A U (1 / (10 * Real.log n)) hUne hH₀_le_G hH₀_le_G₀ hG₀bip
      (fun _ _ h => h.2) hregH₀ hexpU'
  refine ⟨m, hmpos, hmle, H, f, hfinj, hH_bip, hH_reg, ?_, hH_exp⟩
  rw [← hH_avg]
  exact hdH₀_ge_d₀
