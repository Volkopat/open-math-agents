import FormalConjectures.ErdosProblems.«23»
import Mathlib

/-!
Reduction of Erdős Problem 23 to the middle density range.

Compared with reduction R1, the dense range `e ≥ 5 n^2 = N^2/5` is now proved
here, by the neighbourhood-cut averaging argument of Erdős, Faudree, Pach and
Spencer (1988, How to make a graph bipartite, JCTB 45): a triangle-free graph
on `N` vertices with `e` edges has a vertex `v` such that at most
`e - 4 e^2 / N^2` edges avoid the neighbourhood of `v`.  With the side
`S = N(v)` (no edge inside it, as the graph is triangle-free) and `N = 5n`,
`e ≥ 5 n^2`, this gives at most `n^2` same-side edges, since
`(e - 5 n^2) (4 e - 5 n^2) ≥ 0`.  The sparse range `e ≤ 2 n^2` uses the
max-cut bound `H2`; the remaining case is a maximal triangle-free graph with
`2 n^2 ≤ e < 5 n^2` edges, which is `H1`.
-/

namespace OMA.R_Erdos23_erdos_23_R2

open SimpleGraph Finset
open scoped Classical

/-- Middle density range of the maximal case: a maximal triangle-free graph on
`5n` vertices with `2 n^2 ≤ e < 5 n^2` edges has a vertex partition with at
most `n^2` same-side edges. -/
def H1 : Prop :=
  ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
    ∀ (K : SimpleGraph V), K.CliqueFree 3 →
      (∀ L : SimpleGraph V, K ≤ L → L.CliqueFree 3 → L = K) →
      2 * n ^ 2 ≤ K.edgeFinset.card → K.edgeFinset.card < 5 * n ^ 2 →
      ∃ S : Finset V,
        (K.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ n ^ 2

/-- Elementary max-cut bound: every finite graph has a vertex partition with
at most half of its edges on one side. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    ∃ S : Finset V,
      (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤
        G.edgeFinset.card / 2

section
variable {V : Type*} [Fintype V] [DecidableEq V]

-- Both ends of an edge lie on the same side of `S` iff its two endpoints do.
omit [Fintype V] in
lemma same_mk (S : Finset V) (u v : V) :
    (∀ x ∈ s(u, v), ∀ y ∈ s(u, v), (x ∈ S ↔ y ∈ S)) ↔ (u ∈ S ↔ v ∈ S) := by
  simp only [Sym2.mem_iff]
  constructor
  · intro h
    exact h u (Or.inl rfl) v (Or.inr rfl)
  · rintro h x (rfl | rfl) y (rfl | rfl) <;> tauto

-- Deleting the same-side edges of a partition leaves a bipartite subgraph.
lemma cut_graph (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
      (G.edgeFinset \ H.edgeFinset).card =
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card := by
  let H : SimpleGraph V :=
    { Adj := fun u v => G.Adj u v ∧ ¬ (u ∈ S ↔ v ∈ S)
      symm := ⟨fun u v h => ⟨h.1.symm, fun h' => h.2 h'.symm⟩⟩
      loopless := ⟨fun u h => h.2 Iff.rfl⟩ }
  have hH : ∀ u v, H.Adj u v ↔ (G.Adj u v ∧ ¬ (u ∈ S ↔ v ∈ S)) := fun _ _ => Iff.rfl
  refine ⟨H, fun u v h => ((hH u v).1 h).1, ?_, ?_⟩
  · refine ⟨Coloring.mk (fun v => if v ∈ S then (0 : Fin 2) else 1) ?_⟩
    intro u v h
    have h2 := ((hH u v).1 h).2
    clear h hH
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp_all
  · congr 1
    ext e
    induction e using Sym2.ind with
    | h x y =>
      simp only [Finset.mem_sdiff, mem_edgeFinset, mem_edgeSet, Finset.mem_filter, same_mk, hH]
      tauto

end

lemma tri {V : Type} {K : SimpleGraph V} (hK : K.CliqueFree 3) {a b c : V}
    (hab : K.Adj a b) (hac : K.Adj a c) (hbc : K.Adj b c) : False :=
  hK {a, b, c} (is3Clique_triple_iff.2 ⟨hab, hac, hbc⟩)

-- Averaging over neighbourhood cuts (Erdős–Faudree–Pach–Spencer).
lemma key {V : Type} [Fintype V] [Nonempty V] (K : SimpleGraph V) (hK : K.CliqueFree 3) :
    ∃ v : V, Fintype.card V ^ 2 *
        (K.edgeFinset.filter (fun e => ∀ x ∈ e, x ∉ K.neighborFinset v)).card
      + 4 * K.edgeFinset.card ^ 2 ≤ Fintype.card V ^ 2 * K.edgeFinset.card := by
  set N := Fintype.card V with hN
  set E := K.edgeFinset.card with hE
  set f : V → ℕ := fun v =>
    (K.edgeFinset.filter (fun e => ∀ x ∈ e, x ∉ K.neighborFinset v)).card with hf
  -- edges meeting N(v) number at least the degree sum over N(v)
  have hg : ∀ v, f v + ∑ u ∈ K.neighborFinset v, K.degree u ≤ E := by
    intro v
    have hsub : (K.neighborFinset v).biUnion (fun u => K.incidenceFinset u) ⊆
        K.edgeFinset.filter (fun e => ¬ ∀ x ∈ e, x ∉ K.neighborFinset v) := by
      intro e he
      rw [mem_biUnion] at he
      obtain ⟨u, hu, heu⟩ := he
      rw [mem_incidenceFinset] at heu
      rw [mem_filter, mem_edgeFinset]
      exact ⟨heu.1, fun h => h u heu.2 hu⟩
    have hdisj : (K.neighborFinset v : Set V).PairwiseDisjoint
        (fun u => K.incidenceFinset u) := by
      intro a ha b hb hab
      rw [Function.onFun, Finset.disjoint_left]
      intro e hea heb
      rw [mem_incidenceFinset] at hea heb
      have he : e = s(a, b) := (Sym2.mem_and_mem_iff hab).1 ⟨hea.2, heb.2⟩
      have hadj : K.Adj a b := by
        have := hea.1
        rw [he] at this
        exact this
      have ha' : K.Adj v a := (mem_neighborFinset _ _ _).1 (Finset.mem_coe.1 ha)
      have hb' : K.Adj v b := (mem_neighborFinset _ _ _).1 (Finset.mem_coe.1 hb)
      exact tri hK ha' hb' hadj
    have hcard := card_biUnion hdisj
    simp only [card_incidenceFinset_eq_degree] at hcard
    have h1 := card_le_card hsub
    have h2 := card_filter_add_card_filter_not (s := K.edgeFinset)
      (fun e => ∀ x ∈ e, x ∉ K.neighborFinset v)
    simp only [hf]
    omega
  have hsw : ∑ v, ∑ u ∈ K.neighborFinset v, K.degree u = ∑ u, K.degree u ^ 2 := by
    calc ∑ v, ∑ u ∈ K.neighborFinset v, K.degree u
        = ∑ v, ∑ u, if K.Adj v u then K.degree u else 0 := by
          refine sum_congr rfl fun v _ => ?_
          rw [neighborFinset_eq_filter, sum_filter]
      _ = ∑ u, ∑ v, if K.Adj v u then K.degree u else 0 := sum_comm
      _ = ∑ u, K.degree u ^ 2 := by
          refine sum_congr rfl fun u _ => ?_
          rw [← sum_filter, sum_const, smul_eq_mul, sq]
          congr 1
          rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
          congr 1
          ext w
          simp [adj_comm]
  have hsum : ∑ v, f v + ∑ u, K.degree u ^ 2 ≤ N * E := by
    rw [← hsw, ← sum_add_distrib]
    calc ∑ v, (f v + ∑ u ∈ K.neighborFinset v, K.degree u) ≤ ∑ _v : V, E :=
          sum_le_sum fun v _ => hg v
      _ = N * E := by rw [sum_const, card_univ, smul_eq_mul]
  have hcs : (2 * E) ^ 2 ≤ N * ∑ u, K.degree u ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset V)) (f := fun u => K.degree u)
    rw [card_univ, sum_degrees_eq_twice_card_edges] at this
    exact this
  obtain ⟨v, -, hv⟩ := exists_min_image (univ : Finset V) f univ_nonempty
  have hmin : N * f v ≤ ∑ w, f w := by
    calc N * f v = ∑ _w : V, f v := by rw [sum_const, card_univ, smul_eq_mul]
      _ ≤ ∑ w, f w := sum_le_sum fun w _ => hv w (mem_univ w)
  refine ⟨v, ?_⟩
  change N ^ 2 * f v + 4 * E ^ 2 ≤ N ^ 2 * E
  have a1 := Nat.mul_le_mul_left N hmin
  have a2 := Nat.mul_le_mul_left N hsum
  nlinarith

-- Dense range (Erdős–Faudree–Pach–Spencer): a neighbourhood is a good side.
lemma dense (n : ℕ) {V : Type} [Fintype V] (hcard : Fintype.card V = 5 * n)
    (K : SimpleGraph V) (hK : K.CliqueFree 3) (hd : 5 * n ^ 2 ≤ K.edgeFinset.card) :
    ∃ S : Finset V,
      (K.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ n ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.1 (by simpa using hcard)
    refine ⟨∅, ?_⟩
    have : K.edgeFinset = ∅ := by
      apply eq_empty_of_forall_notMem
      intro e
      induction e using Sym2.ind with
      | h x y => exact isEmptyElim x
    simp [this]
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨v, hv⟩ := key K hK
  refine ⟨K.neighborFinset v, ?_⟩
  have hsub : K.edgeFinset.filter
        (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ K.neighborFinset v ↔ y ∈ K.neighborFinset v)) ⊆
      K.edgeFinset.filter (fun e => ∀ x ∈ e, x ∉ K.neighborFinset v) := by
    intro e he
    rw [mem_filter] at he ⊢
    obtain ⟨he1, he2⟩ := he
    refine ⟨he1, ?_⟩
    induction e using Sym2.ind with
    | h x y =>
      rw [same_mk] at he2
      rw [mem_edgeFinset, mem_edgeSet] at he1
      simp only [mem_neighborFinset] at he2 ⊢
      have hx : ¬ K.Adj v x := fun h => tri hK h (he2.1 h) he1
      have hy : ¬ K.Adj v y := fun h => tri hK (he2.2 h) h he1
      intro z hz
      rcases Sym2.mem_iff.1 hz with rfl | rfl
      · exact hx
      · exact hy
  refine (card_le_card hsub).trans ?_
  rw [hcard] at hv
  set F := (K.edgeFinset.filter (fun e => ∀ x ∈ e, x ∉ K.neighborFinset v)).card
  set E := K.edgeFinset.card
  by_contra hc
  rw [not_le] at hc
  have b1 : (5 * n) ^ 2 * (n ^ 2 + 1) ≤ (5 * n) ^ 2 * F :=
    Nat.mul_le_mul_left _ hc
  have hnat : (5 * n) ^ 2 * (n ^ 2 + 1) + 4 * E ^ 2 ≤ (5 * n) ^ 2 * E := by linarith
  have hz : ((5 * n : ℕ) : ℤ) ^ 2 * ((n : ℤ) ^ 2 + 1) + 4 * (E : ℤ) ^ 2 ≤
      ((5 * n : ℕ) : ℤ) ^ 2 * (E : ℤ) := by exact_mod_cast hnat
  have hd' : (5 : ℤ) * n ^ 2 ≤ E := by exact_mod_cast hd
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  push_cast at hz
  nlinarith [mul_nonneg (sub_nonneg.2 hd') (by linarith : (0 : ℤ) ≤ 4 * E - 5 * n ^ 2),
    mul_pos hn' hn']

theorem main : H1 → H2 → type_of% @Erdos23.erdos_23 := by
  intro h1 h2 n V instV hcard G hG
  classical
  by_cases hs : G.edgeFinset.card ≤ 2 * n ^ 2
  · obtain ⟨S, hS⟩ := h2 V G
    obtain ⟨H, hle, hbip, hdiff⟩ := cut_graph G S
    refine ⟨H, hle, hbip, ?_⟩
    rw [hdiff]
    exact hS.trans (Nat.div_le_of_le_mul hs)
  · obtain ⟨K, hGK, hKmax⟩ :=
      Finite.exists_le_maximal (p := fun L : SimpleGraph V => L.CliqueFree 3) hG
    have hKcf : K.CliqueFree 3 := hKmax.1
    have hmax : ∀ L : SimpleGraph V, K ≤ L → L.CliqueFree 3 → L = K :=
      fun L hKL hLcf => le_antisymm (hKmax.2 hLcf hKL) hKL
    have hKlow : 2 * n ^ 2 ≤ K.edgeFinset.card :=
      (by omega : 2 * n ^ 2 ≤ G.edgeFinset.card).trans
        (Finset.card_le_card (edgeFinset_mono hGK))
    have hpart : ∃ S : Finset V,
        (K.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ n ^ 2 := by
      by_cases hd : K.edgeFinset.card < 5 * n ^ 2
      · exact h1 n V hcard K hKcf hmax hKlow hd
      · exact dense n hcard K hKcf (not_lt.1 hd)
    obtain ⟨S, hS⟩ := hpart
    obtain ⟨H, hle, hbip, hdiff⟩ := cut_graph G S
    refine ⟨H, hle, hbip, ?_⟩
    rw [hdiff]
    exact (Finset.card_le_card (Finset.filter_subset_filter _ (edgeFinset_mono hGK))).trans hS

end OMA.R_Erdos23_erdos_23_R2
