import OMAReductions.R_Erdos80_erdos_80_parts_ii_R1
import Mathlib

/-!
# Proof of `Erdos80.erdos_80.parts.ii.R1.H1`

For `1 / 4 < c < 1 / 2`, every graph on `n` vertices with at least `c * n ^ 2` edges contains an
edge lying in at least `(4 * c - 1) * n` triangles, proved via double counting of degrees and
Cauchy-Schwarz:
  `4 * E ^ 2 = (∑ deg v) ^ 2 ≤ n * ∑ (deg v) ^ 2 = (n / 2) * ∑_{u ~ v} (deg u + deg v)
    ≤ n * E * (n + bookNumber G)`.
Since the complete graph `⊤` on `Fin n` is admissible for all sufficiently large `n` when `c < 1 / 2`,
the infimum `Erdos80.f c n` satisfies `(4 * c - 1) * n ≤ Erdos80.f c n` eventually, which dominates
`Real.log n`.

Attribution: Classical double-counting / Cauchy-Schwarz book bound (Erdos-Rothschild / Edwards).
-/

namespace Erdos80R1H1

open Filter Finset SimpleGraph

private lemma card_commonNeighbors_le_trianglesContaining
    {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    {u v : α} (huv : G.Adj u v) :
    #(G.neighborFinset u ∩ G.neighborFinset v) ≤ #(G.trianglesContaining s(u, v)) := by
  classical
  let f : α → Finset α := fun w => {u, v, w}
  have hinj : Set.InjOn f ↑(G.neighborFinset u ∩ G.neighborFinset v) := by
    intro w₁ hw₁ w₂ hw₂ hEq
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe,
      SimpleGraph.mem_neighborFinset] at hw₁ hw₂
    have hw₁u : w₁ ≠ u := (G.ne_of_adj hw₁.1).symm
    have hw₁v : w₁ ≠ v := (G.ne_of_adj hw₁.2).symm
    have hmem : w₁ ∈ f w₂ := by
      rw [← hEq]
      simp [f]
    simp only [f, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact (hw₁u rfl).elim
    · exact (hw₁v rfl).elim
    · rfl
  have hmaps : Set.MapsTo f ↑(G.neighborFinset u ∩ G.neighborFinset v)
      ↑(G.trianglesContaining s(u, v)) := by
    intro w hw
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe,
      SimpleGraph.mem_neighborFinset] at hw
    have huvne : u ≠ v := G.ne_of_adj huv
    have huwne : u ≠ w := G.ne_of_adj hw.1
    have hvwne : v ≠ w := G.ne_of_adj hw.2
    simp only [Finset.mem_coe, SimpleGraph.trianglesContaining, Finset.mem_filter,
      SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro a ha b hb hab
      simp only [f, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact (hab rfl).elim
      · exact huv
      · exact hw.1
      · exact huv.symm
      · exact (hab rfl).elim
      · exact hw.2
      · exact hw.1.symm
      · exact hw.2.symm
      · exact (hab rfl).elim
    · dsimp [f]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hvwne]
      · simp [huvne, huwne]
    · intro x hx
      simp only [Sym2.mem_toFinset, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl <;> simp [f]
  exact Finset.card_le_card_of_injOn f hmaps hinj

private lemma deg_add_deg_le_card_add_bookNumber
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u v : Fin n} (huv : G.Adj u v) :
    G.degree u + G.degree v ≤ n + Erdos80.bookNumber G := by
  have hunion : #(G.neighborFinset u ∪ G.neighborFinset v) ≤ n := by
    calc #(G.neighborFinset u ∪ G.neighborFinset v)
        ≤ #(Finset.univ : Finset (Fin n)) := Finset.card_le_univ _
      _ = n := by simp
  have hinter : #(G.neighborFinset u ∩ G.neighborFinset v) ≤ #(G.trianglesContaining s(u, v)) :=
    card_commonNeighbors_le_trianglesContaining G huv
  have hsup : #(G.trianglesContaining s(u, v)) ≤ Erdos80.bookNumber G := by
    unfold Erdos80.bookNumber
    exact Finset.le_sup (f := fun e => #(G.trianglesContaining e))
      (G.mem_edgeFinset.mpr huv)
  have hci := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hci
  omega

private lemma four_card_edges_le_mul_add_bookNumber
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hE : 0 < #G.edgeFinset) :
    4 * #G.edgeFinset ≤ n * (n + Erdos80.bookNumber G) := by
  have hsum_deg : ∑ u : Fin n, G.degree u = 2 * #G.edgeFinset :=
    G.sum_degrees_eq_twice_card_edges
  have hsum_left :
      ∑ u : Fin n, ∑ v ∈ G.neighborFinset u, G.degree u = ∑ u : Fin n, (G.degree u) ^ 2 := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, smul_eq_mul, sq]
  have hsum_right :
      ∑ u : Fin n, ∑ v ∈ G.neighborFinset u, G.degree v = ∑ v : Fin n, (G.degree v) ^ 2 := by
    have h1 :
        ∑ u : Fin n, ∑ v ∈ G.neighborFinset u, G.degree v =
          ∑ u : Fin n, ∑ v : Fin n, if G.Adj u v then G.degree v else 0 := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext v
      simp [SimpleGraph.mem_neighborFinset]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    have h2 :
        ∑ u : Fin n, (if G.Adj u v then G.degree v else 0) =
          ∑ _u ∈ G.neighborFinset v, G.degree v := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext u
      simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]
    rw [h2, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, smul_eq_mul, sq]
  have hdouble :
      2 * ∑ u : Fin n, (G.degree u) ^ 2 ≤ (2 * #G.edgeFinset) * (n + Erdos80.bookNumber G) := by
    calc 2 * ∑ u : Fin n, (G.degree u) ^ 2
        = (∑ u : Fin n, ∑ v ∈ G.neighborFinset u, G.degree u) +
            (∑ u : Fin n, ∑ v ∈ G.neighborFinset u, G.degree v) := by
              rw [hsum_left, hsum_right, two_mul]
      _ = ∑ u : Fin n, ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [← Finset.sum_add_distrib]
      _ ≤ ∑ u : Fin n, ∑ _v ∈ G.neighborFinset u, (n + Erdos80.bookNumber G) := by
            refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v hv => ?_
            exact deg_add_deg_le_card_add_bookNumber G ((G.mem_neighborFinset u v).mp hv)
      _ = ∑ u : Fin n, G.degree u * (n + Erdos80.bookNumber G) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, smul_eq_mul]
      _ = (∑ u : Fin n, G.degree u) * (n + Erdos80.bookNumber G) := by
            rw [← Finset.sum_mul]
      _ = (2 * #G.edgeFinset) * (n + Erdos80.bookNumber G) := by rw [hsum_deg]
  have hsq : ∑ u : Fin n, (G.degree u) ^ 2 ≤ #G.edgeFinset * (n + Erdos80.bookNumber G) := by
    nlinarith
  have hcs : (∑ u : Fin n, G.degree u) ^ 2 ≤ n * ∑ u : Fin n, (G.degree u) ^ 2 := by
    have hnn : (0 : ℝ) ≤ ∑ u : Fin n, ∑ v : Fin n, ((G.degree u : ℝ) - (G.degree v : ℝ)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hexpand :
        (∑ u : Fin n, ∑ v : Fin n, ((G.degree u : ℝ) - (G.degree v : ℝ)) ^ 2) =
          2 * (n : ℝ) * (∑ u : Fin n, (G.degree u : ℝ) ^ 2) -
            2 * (∑ u : Fin n, (G.degree u : ℝ)) ^ 2 := by
      have hsub : ∀ u v : Fin n, ((G.degree u : ℝ) - (G.degree v : ℝ)) ^ 2 =
          (G.degree u : ℝ) ^ 2 - 2 * (G.degree u : ℝ) * (G.degree v : ℝ) +
            (G.degree v : ℝ) ^ 2 := fun _ _ => by ring
      simp_rw [hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [← Finset.mul_sum]
      ring
    have hcsR : (∑ u : Fin n, (G.degree u : ℝ)) ^ 2 ≤
        (n : ℝ) * ∑ u : Fin n, (G.degree u : ℝ) ^ 2 := by linarith
    exact_mod_cast hcsR
  have hmul : (2 * #G.edgeFinset) ^ 2 ≤ n * (#G.edgeFinset * (n + Erdos80.bookNumber G)) := by
    calc (2 * #G.edgeFinset) ^ 2
        = (∑ u : Fin n, G.degree u) ^ 2 := by rw [hsum_deg]
      _ ≤ n * ∑ u : Fin n, (G.degree u) ^ 2 := hcs
      _ ≤ n * (#G.edgeFinset * (n + Erdos80.bookNumber G)) := Nat.mul_le_mul_left n hsq
  have hmul' : #G.edgeFinset * (4 * #G.edgeFinset) ≤
      #G.edgeFinset * (n * (n + Erdos80.bookNumber G)) := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left hmul' hE

private lemma top_admissible {c : ℝ} {n : ℕ} (hn3 : 3 ≤ n)
    (hn : 1 ≤ (1 - 2 * c) * (n : ℝ)) [DecidableRel (⊤ : SimpleGraph (Fin n)).Adj] :
    Erdos80.Admissible c (⊤ : SimpleGraph (Fin n)) := by
  constructor
  · have hdeg : ∀ u : Fin n, (⊤ : SimpleGraph (Fin n)).degree u = n - 1 := by
      intro u
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      have heq : (⊤ : SimpleGraph (Fin n)).neighborFinset u = Finset.univ.erase u := by
        ext v
        simp [ne_comm]
      rw [heq, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
    have htwice : 2 * #(⊤ : SimpleGraph (Fin n)).edgeFinset = n * (n - 1) := by
      rw [← (⊤ : SimpleGraph (Fin n)).sum_degrees_eq_twice_card_edges]
      simp [hdeg]
    have htwiceR : 2 * (#(⊤ : SimpleGraph (Fin n)).edgeFinset : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
      have h1 : (2 * #(⊤ : SimpleGraph (Fin n)).edgeFinset : ℝ) = ((n * (n - 1) : ℕ) : ℝ) := by
        exact_mod_cast htwice
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h1
      exact h1
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  · intro e he
    rcases e with ⟨u, v⟩
    have huv : (⊤ : SimpleGraph (Fin n)).Adj u v :=
      (⊤ : SimpleGraph (Fin n)).mem_edgeFinset.mp he
    have huvne : u ≠ v := (⊤ : SimpleGraph (Fin n)).ne_of_adj huv
    have hlt : #({u, v} : Finset (Fin n)) < #(Finset.univ : Finset (Fin n)) := by
      rw [Finset.card_pair huvne, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hwu : w ≠ u := fun h => hw (by simp [h])
    have hwv : w ≠ v := fun h => hw (by simp [h])
    have hmem : w ∈ (⊤ : SimpleGraph (Fin n)).neighborFinset u ∩
        (⊤ : SimpleGraph (Fin n)).neighborFinset v := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.top_adj]
      exact ⟨hwu.symm, hwv.symm⟩
    have hpos : 0 < #((⊤ : SimpleGraph (Fin n)).trianglesContaining s(u, v)) :=
      lt_of_lt_of_le (Finset.card_pos.mpr ⟨w, hmem⟩)
        (card_commonNeighbors_le_trianglesContaining (⊤ : SimpleGraph (Fin n)) huv)
    exact Finset.card_pos.mp hpos

private lemma lower_bound_f {c : ℝ} (hc1 : 1 / 4 < c) {n : ℕ} (hn3 : 3 ≤ n)
    (hn : 1 ≤ (1 - 2 * c) * (n : ℝ)) :
    (4 * c - 1) * (n : ℝ) ≤ (Erdos80.f c n : ℝ) := by
  classical
  have hne : {m | ∃ G : SimpleGraph (Fin n), Erdos80.Admissible c G ∧
      Erdos80.bookNumber G = m}.Nonempty :=
    ⟨_, ⊤, @top_admissible c n hn3 hn (fun _ _ => Classical.propDecidable _), rfl⟩
  have hmem := Nat.sInf_mem hne
  obtain ⟨G, hGadm, hGbook⟩ := hmem
  rw [← Erdos80.f] at hGbook
  have hpos_n : (0 : ℝ) < (n : ℝ) := by positivity
  have hE_real : c * (n : ℝ) ^ 2 ≤ (#G.edgeFinset : ℝ) := hGadm.1
  have hE_pos : 0 < #G.edgeFinset := by
    by_contra h0
    have hzero : #G.edgeFinset = 0 := by omega
    rw [hzero, Nat.cast_zero] at hE_real
    have : 0 < c * (n : ℝ) ^ 2 := by positivity
    linarith
  have hbound : 4 * #G.edgeFinset ≤ n * (n + Erdos80.bookNumber G) :=
    four_card_edges_le_mul_add_bookNumber G hE_pos
  have hboundR : 4 * (#G.edgeFinset : ℝ) ≤ (n : ℝ) * ((n : ℝ) + (Erdos80.bookNumber G : ℝ)) := by
    exact_mod_cast hbound
  rw [hGbook] at hboundR
  nlinarith

end Erdos80R1H1

theorem OMA.solution : OMA.R_Erdos80_erdos_80_parts_ii_R1.H1 := by
  intro c hc1 hc2
  have h4c : 0 < 4 * c - 1 := by linarith
  have h12c : 0 < 1 - 2 * c := by linarith
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 / (4 * c - 1), ?_⟩
  let N : ℕ := max 3 (Nat.ceil (1 / (1 - 2 * c)))
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hn3 : 3 ≤ n := le_trans (le_max_left _ _) hn
  have hnceil : Nat.ceil (1 / (1 - 2 * c)) ≤ n := le_trans (le_max_right _ _) hn
  have hn12 : 1 ≤ (1 - 2 * c) * (n : ℝ) := by
    have h1 : 1 / (1 - 2 * c) ≤ (n : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hnceil)
    have h2 := mul_le_mul_of_nonneg_left h1 h12c.le
    rwa [mul_one_div_cancel h12c.ne'] at h2
  have hf := Erdos80R1H1.lower_bound_f hc1 hn3 hn12
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hlog_le : Real.log (n : ℝ) ≤ (n : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hn_pos]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog_nn,
    abs_of_nonneg (Nat.cast_nonneg _)]
  have hmul : (n : ℝ) ≤ 1 / (4 * c - 1) * (Erdos80.f c n : ℝ) := by
    rw [one_div_mul_eq_div, le_div_iff₀ h4c]
    linarith
  exact le_trans hlog_le hmul
