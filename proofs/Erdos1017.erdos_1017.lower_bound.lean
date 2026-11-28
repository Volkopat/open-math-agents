import FormalConjectures.ErdosProblems.«1017»
import Mathlib

/-!
Erdős Problem 1017, lower bound. Write `a = n / 2`, `q = n - a`, `p = q / 2`.
For `q * a < k ≤ q * a + p * (q - p)` we prove `f n k ≥ 2 * (q * a) - k`
(with `q * a = ⌊n^2/4⌋`), which is sharp for `K_4`-free graphs; otherwise the bound is `1`.
Construction: the complete bipartite graph between a part of size `q` and a part of size `a`,
plus `k - q * a` edges of a complete bipartite graph inside the part of size `q`.
The graph is 3-colourable, so the cliques of an edge partition are edges and triangles, and
each triangle uses its own edge inside the big part.
-/

namespace OMA.Helpers

open SimpleGraph

theorem exists_partition {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P := by
  classical
  refine ⟨Finset.univ.filter (fun s => ∃ u v, G.Adj u v ∧ s = {u, v}), ⟨?_, ?_⟩⟩
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨u, v, huv, rfl⟩ := hs
    refine ⟨by rw [Finset.card_pair huv.ne], ?_⟩
    rw [Finset.coe_pair, SimpleGraph.isClique_pair]
    exact fun _ => huv
  · intro u v huv
    refine ⟨{u, v}, ⟨?_, by simp, by simp⟩, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨u, v, huv, rfl⟩
    · rintro s ⟨hs, hu, hv⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      obtain ⟨a, b, hab, rfl⟩ := hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      have hne := huv.ne
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact absurd rfl hne
      · rfl
      · exact Finset.pair_comm _ _
      · exact absurd rfl hne

theorem le_f {n k t : ℕ} (G : SimpleGraph (Fin n)) (hG : G.edgeSet.ncard = k)
    (h : ∀ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P → t ≤ P.card) :
    t ≤ Erdos1017.f n k := by
  have hne : {m : ℕ | ∀ H : SimpleGraph (Fin n), H.edgeSet.ncard = k →
      ∃ P : Finset (Finset (Fin n)), H.IsCliqueEdgePartition P ∧ P.card ≤ m}.Nonempty := by
    refine ⟨Fintype.card (Finset (Fin n)), fun H _ => ?_⟩
    obtain ⟨P, hP⟩ := exists_partition H
    exact ⟨P, hP, Finset.card_le_univ P⟩
  obtain ⟨P, hP, hle⟩ := Nat.sInf_mem hne G hG
  exact (h P hP).trans hle

theorem graph_of {n : ℕ} (E : Finset (Sym2 (Fin n))) (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = E.card ∧ ∀ u v, G.Adj u v ↔ s(u, v) ∈ E := by
  refine ⟨SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n))), ?_, ?_⟩
  · rw [SimpleGraph.edgeSet_fromEdgeSet]
    have : (E : Set (Sym2 (Fin n))) \ Sym2.diagSet = E := by
      ext e
      simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
      exact ⟨fun h => h.1, fun h => ⟨h, hE e h⟩⟩
    rw [this, Set.ncard_coe_finset]
  · intro u v
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨fun h => h.1, fun h => ⟨h, fun huv => hE _ h (Sym2.mk_isDiag_iff.mpr huv)⟩⟩

theorem card_cross {V : Type*} [DecidableEq V] (S T : Finset V) (h : Disjoint S T) :
    ((S ×ˢ T).image (fun p : V × V => s(p.1, p.2))).card = S.card * T.card := by
  rw [Finset.card_image_of_injOn, Finset.card_product]
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hab hab'
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd hab.1 (Finset.disjoint_right.mp h hab'.2)

theorem key {V : Type*} [Fintype V] [DecidableEq V] (c : V → Fin 3) (G : SimpleGraph V)
    (E : Finset (Sym2 V)) (hE : ∀ u v, G.Adj u v ↔ s(u, v) ∈ E)
    (hc : ∀ u v, G.Adj u v → c u ≠ c v) (P : Finset (Finset V))
    (hP : G.IsCliqueEdgePartition P) (X : Finset (Sym2 V)) (hXE : X ⊆ E)
    (hX : ∀ u v, s(u, v) ∈ E → c u ≠ 2 → c v ≠ 2 → s(u, v) ∈ X) :
    E.card ≤ P.card + 2 * X.card := by
  classical
  have hinj : ∀ s ∈ P, Set.InjOn c (s : Set V) := by
    intro s hs u hu v hv huv
    by_contra hne
    exact hc u v ((hP.1 s hs).2 hu hv hne) huv
  have hcard : ∀ s ∈ P, s.card ≤ 3 := by
    intro s hs
    have := Finset.card_le_card_of_injOn c (fun x _ => Finset.mem_univ (c x)) (hinj s hs)
    simpa using this
  have h1 : E ⊆ P.biUnion (fun s => s.offDiag.image Sym2.mk.uncurry) := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      have hadj := (hE u v).mpr he
      obtain ⟨s, ⟨hs, hu, hv⟩, _⟩ := hP.2 u v hadj
      rw [Finset.mem_biUnion]
      refine ⟨s, hs, ?_⟩
      rw [Finset.mem_image]
      exact ⟨(u, v), Finset.mem_offDiag.mpr ⟨hu, hv, hadj.ne⟩, rfl⟩
  have h2 : E.card ≤ ∑ s ∈ P, s.card.choose 2 := by
    refine (Finset.card_le_card h1).trans (Finset.card_biUnion_le.trans ?_)
    exact Finset.sum_le_sum (fun s _ => (Sym2.card_image_offDiag s).le)
  have h3 : ∑ s ∈ P, s.card.choose 2 ≤ ∑ s ∈ P, (1 + 2 * (if s.card = 3 then 1 else 0)) := by
    refine Finset.sum_le_sum (fun s hs => ?_)
    have h2 := (hP.1 s hs).1
    have h3 := hcard s hs
    interval_cases s.card <;> simp
  have h4 : ∑ s ∈ P, (1 + 2 * (if s.card = 3 then 1 else 0))
      = P.card + 2 * (P.filter (fun s => s.card = 3)).card := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.card_filter]
    simp
  have h5 : (P.filter (fun s => s.card = 3)).card ≤ X.card := by
    refine Finset.card_le_card_of_forall_subsingleton (fun s e => ∀ v ∈ e, v ∈ s) ?_ ?_
    · intro s hs
      rw [Finset.mem_filter] at hs
      have himg : s.image c = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [Finset.card_image_of_injOn (hinj s hs.1), hs.2]
        rfl
      have h0 : (0 : Fin 3) ∈ s.image c := himg ▸ Finset.mem_univ _
      have h1 : (1 : Fin 3) ∈ s.image c := himg ▸ Finset.mem_univ _
      obtain ⟨u, hu, hcu⟩ := Finset.mem_image.mp h0
      obtain ⟨v, hv, hcv⟩ := Finset.mem_image.mp h1
      have huv : u ≠ v := by
        rintro rfl
        rw [hcu] at hcv
        exact absurd hcv (by decide)
      have hadj : G.Adj u v := (hP.1 s hs.1).2 hu hv huv
      refine ⟨s(u, v), hX u v ((hE u v).mp hadj) (by rw [hcu]; decide) (by rw [hcv]; decide), ?_⟩
      intro w hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hu
      · exact hv
    · intro e he s1 hs1 s2 hs2
      have hs1 : s1 ∈ P.filter (fun s => s.card = 3) ∧ ∀ v ∈ e, v ∈ s1 := hs1
      have hs2 : s2 ∈ P.filter (fun s => s.card = 3) ∧ ∀ v ∈ e, v ∈ s2 := hs2
      rw [Finset.mem_filter] at hs1 hs2
      induction e using Sym2.ind with
      | h u v =>
        have hadj : G.Adj u v := (hE u v).mpr (hXE he)
        obtain ⟨s, _, huniq⟩ := hP.2 u v hadj
        rw [huniq s1 ⟨hs1.1.1, hs1.2 u (Sym2.mem_mk_left u v), hs1.2 v (Sym2.mem_mk_right u v)⟩,
          huniq s2 ⟨hs2.1.1, hs2.2 u (Sym2.mem_mk_left u v), hs2.2 v (Sym2.mem_mk_right u v)⟩]
  omega

end OMA.Helpers

def OMA.answer : ℕ → ℕ → ℕ := fun n k =>
  if k ≤ (n - n / 2) * (n / 2) + ((n - n / 2) / 2) * ((n - n / 2) - (n - n / 2) / 2)
  then 2 * ((n - n / 2) * (n / 2)) - k else 1

namespace OMA.Helpers

theorem bound_one {n k : ℕ} (hk : k ≤ n.choose 2) (hk0 : 0 < k) : 1 ≤ Erdos1017.f n k := by
  classical
  have hT : ((Finset.univ : Finset (Fin n)).offDiag.image Sym2.mk.uncurry).card = n.choose 2 := by
    rw [Sym2.card_image_offDiag, Finset.card_univ, Fintype.card_fin]
  obtain ⟨E, hET, hEc⟩ := Finset.exists_subset_card_eq (hT ▸ hk)
  have hdiag : ∀ e ∈ E, ¬ e.IsDiag := by
    intro e he
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp (hET he)
    exact fun h => (Finset.mem_offDiag.mp huv).2.2 (Sym2.mk_isDiag_iff.mp h)
  obtain ⟨G, hG, hadj⟩ := graph_of E hdiag
  refine le_f G (hG.trans hEc) (fun P hP => ?_)
  obtain ⟨e, he⟩ := Finset.card_pos.mp (hEc ▸ hk0)
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨s, ⟨hs, _, _⟩, _⟩ := hP.2 u v ((hadj u v).mpr he)
    exact Finset.card_pos.mpr ⟨s, hs⟩

theorem bound_main {n k a q p : ℕ} (hq : q + a = n) (hp : p ≤ q)
    (hk1 : q * a ≤ k) (hk2 : k ≤ q * a + p * (q - p)) : 2 * (q * a) - k ≤ Erdos1017.f n k := by
  classical
  obtain ⟨C2, -, hC2⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := a) (by simp; omega)
  have hA : (C2ᶜ).card = q := by rw [Finset.card_compl, hC2, Fintype.card_fin]; omega
  obtain ⟨C0, hC0A, hC0⟩ := Finset.exists_subset_card_eq (s := C2ᶜ) (n := p) (by omega)
  have hC1 : (C2ᶜ \ C0).card = q - p := by
    have := Finset.card_sdiff_add_card_eq_card hC0A
    omega
  let c : Fin n → Fin 3 := fun v => if v ∈ C2 then 2 else if v ∈ C0 then 0 else 1
  let B : Finset (Sym2 (Fin n)) := (C2ᶜ ×ˢ C2).image (fun p : Fin n × Fin n => s(p.1, p.2))
  let X0 : Finset (Sym2 (Fin n)) :=
    (C0 ×ˢ (C2ᶜ \ C0)).image (fun p : Fin n × Fin n => s(p.1, p.2))
  have hBc : B.card = q * a := by
    rw [card_cross _ _ disjoint_compl_left, hA, hC2]
  have hX0c : X0.card = p * (q - p) := by
    rw [card_cross _ _ Finset.disjoint_sdiff, hC0, hC1]
  have hBmem : ∀ e ∈ B, ∃ u v, e = s(u, v) ∧ c u ≠ 2 ∧ c v = 2 := by
    intro e he
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.mem_product, Finset.mem_compl] at huv
    refine ⟨u, v, rfl, ?_, ?_⟩
    · simp only [c, if_neg huv.1]; split_ifs <;> decide
    · simp only [c, if_pos huv.2]
  have hX0mem : ∀ e ∈ X0, ∃ u v, e = s(u, v) ∧ c u = 0 ∧ c v = 1 := by
    intro e he
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.mem_product, Finset.mem_sdiff, Finset.mem_compl] at huv
    have hu2 : u ∉ C2 := Finset.mem_compl.mp (hC0A huv.1)
    refine ⟨u, v, rfl, ?_, ?_⟩
    · simp only [c, if_neg hu2, if_pos huv.1]
    · simp only [c, if_neg huv.2.1, if_neg huv.2.2]
  have hdisj : Disjoint B X0 := by
    rw [Finset.disjoint_left]
    intro e heB heX
    obtain ⟨u, v, rfl, hu, hv⟩ := hBmem e heB
    obtain ⟨u', v', heq, hu', hv'⟩ := hX0mem _ heX
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hv] at hv'; exact absurd hv' (by decide)
    · rw [hv] at hu'; exact absurd hu' (by decide)
  have hTc : (B ∪ X0).card = q * a + p * (q - p) := by
    rw [Finset.card_union_of_disjoint hdisj, hBc, hX0c]
  obtain ⟨E, hBE, hET, hEc⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_union_left (s₁ := B) (s₂ := X0)) (hBc ▸ hk1) (hTc ▸ hk2)
  have hEmem : ∀ e ∈ E, ∃ u v, e = s(u, v) ∧ c u ≠ c v := by
    intro e he
    rcases Finset.mem_union.mp (hET he) with h | h
    · obtain ⟨u, v, rfl, hu, hv⟩ := hBmem e h
      exact ⟨u, v, rfl, fun h => hu (h.trans hv)⟩
    · obtain ⟨u, v, rfl, hu, hv⟩ := hX0mem e h
      exact ⟨u, v, rfl, by rw [hu, hv]; decide⟩
  have hcol : ∀ u v, s(u, v) ∈ E → c u ≠ c v := by
    intro u v he
    obtain ⟨u', v', heq, hne⟩ := hEmem _ he
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne
    · exact hne.symm
  have hdiag : ∀ e ∈ E, ¬ e.IsDiag := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      intro h
      exact hcol u v he (congrArg c (Sym2.mk_isDiag_iff.mp h))
  obtain ⟨G, hG, hadj⟩ := graph_of E hdiag
  refine le_f G (hG.trans hEc) (fun P hP => ?_)
  have hkey := key c G E hadj (fun u v h => hcol u v ((hadj u v).mp h)) P hP (E \ B)
    Finset.sdiff_subset (by
      intro u v he hu hv
      refine Finset.mem_sdiff.mpr ⟨he, fun hB => ?_⟩
      obtain ⟨u', v', heq, hu', hv'⟩ := hBmem _ hB
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hv hv'
      · exact hu hv')
  have := Finset.card_sdiff_add_card_eq_card hBE
  omega

end OMA.Helpers

theorem OMA.solution : Erdos1017.erdos_1017.lower_bound.answer = OMA.answer → type_of% @Erdos1017.erdos_1017.lower_bound := by
  intro h
  rw [h]
  intro n k hk hnk
  unfold OMA.answer
  split_ifs with hif
  · refine OMA.Helpers.bound_main (a := n / 2) (q := n - n / 2) (p := (n - n / 2) / 2)
      (by omega) (by omega) ?_ hif
    have h2 : n = 2 * (n / 2) ∨ n = 2 * (n / 2) + 1 := by omega
    generalize n / 2 = a at h2 ⊢
    rcases h2 with rfl | rfl
    · have : 2 * a - a = a := by omega
      rw [this]; nlinarith
    · have : 2 * a + 1 - a = a + 1 := by omega
      rw [this]; nlinarith
  · exact OMA.Helpers.bound_one hk (by omega)
