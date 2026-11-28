import FormalConjectures.Paper.RingelConjecture

-- Reduction RingelConjecture.ringel_conjecture.R1 of Ringel's conjecture.
-- Proved below: Rosa's theorem (A. Rosa, On certain valuations of the vertices of a graph, 1967):
-- the Graceful Tree Conjecture implies Ringel's conjecture, via the cyclic decomposition of K_{2n+1}.
-- A graceful labelling f : V -> {0..n} of a tree with n edges gives the 2n+1 cyclic copies
-- g_i(v) = (f v + i) mod (2n+1). They are pairwise edge-disjoint: if an edge lies in copies i and j,
-- the two preimage edges have the same signed label difference (both differences lie in [-n, n] and
-- agree mod 2n+1), so by gracefulness they are the same tree edge; the same orientation forces
-- i = j, the opposite orientation forces 2 (f u - f v) = 0, impossible for an edge. The copies then
-- cover K_{2n+1} by counting: (2n+1) * n edges = choose (2n+1) 2.
-- H1: the Graceful Tree Conjecture, verbatim in the form of GracefulLabeling.graceful_tree_conjecture.
-- H2: the edge count of K_{2n+1}, (2n+1) * n = choose (2n+1) 2 (same as step H3 of
--     Arxiv.2001.02665.ringel_conjecture_large.R1, already proved on the site).

namespace OMA.R_RingelConjecture_ringel_conjecture_R1

open SimpleGraph

/-- H1, the Graceful Tree Conjecture (Ringel-Kotzig): every tree with m edges has an injective
labelling by 0..m whose edge differences are exactly 1..m. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj], T.IsTree →
    ∃ f : V → ℕ,
      Function.Injective f ∧
      (∀ v, f v ≤ T.edgeFinset.card) ∧
      T.edgeFinset.image (fun e =>
        e.lift ⟨fun u v => Int.natAbs ((f u : ℤ) - (f v : ℤ)),
                fun u v => by
                  show ((f u : ℤ) - f v).natAbs = ((f v : ℤ) - f u).natAbs
                  rw [← Int.natAbs_neg, neg_sub]⟩) = Finset.Icc 1 T.edgeFinset.card

/-- H2, the number of edges of the complete graph of odd order 2n+1. -/
def H2 : Prop := ∀ n : ℕ, (2 * n + 1) * n = Nat.choose (2 * n + 1) 2

lemma int_zero_of_dvd (m x : ℤ) (h : m ∣ x) (h1 : x < m) (h2 : -m < x) : x = 0 :=
  Int.eq_zero_of_abs_lt_dvd h (abs_lt.mpr ⟨h2, h1⟩)

theorem main : H1 → H2 → type_of% @RingelConjecture.ringel_conjecture := by
  intro h1 h2 V _ T hT n hn
  classical
  have : Fintype V := Fintype.ofFinite V
  obtain ⟨f, hfinj, hfle, himg⟩ := h1 T hT
  have hcardE : T.edgeFinset.card = n := by
    rw [← hn, ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [hcardE] at hfle himg
  -- gracefulness: the difference map is injective on edges
  have key : ∀ D : Sym2 V → ℕ, T.edgeFinset.image D = Finset.Icc 1 n →
      Set.InjOn D (T.edgeFinset : Set (Sym2 V)) := by
    intro D hD
    apply Finset.injOn_of_card_image_eq
    rw [hD, Nat.card_Icc, hcardE]
    omega
  have hinjOn := key _ himg
  have hm : 0 < 2 * n + 1 := by omega
  -- the cyclic copies
  have gin : ∀ i : ℕ, Function.Injective
      (fun v : V => (⟨(f v + i) % (2 * n + 1), Nat.mod_lt _ hm⟩ : Fin (2 * n + 1))) := by
    intro i v w hvw
    have h := congrArg Fin.val hvw
    simp only at h
    have h' : f v % (2 * n + 1) = f w % (2 * n + 1) := Nat.ModEq.add_right_cancel' i h
    rw [Nat.mod_eq_of_lt (by have := hfle v; omega),
      Nat.mod_eq_of_lt (by have := hfle w; omega)] at h'
    exact hfinj h'
  let g : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)) := fun i => ⟨_, gin i.val⟩
  have hg : ∀ (i : Fin (2 * n + 1)) (v : V), ((g i v : Fin (2 * n + 1)) : ℕ) = (f v + i.val) % (2 * n + 1) :=
    fun _ _ => rfl
  have hdisj : Pairwise (fun i j => Disjoint (T.map (g i)).edgeSet (T.map (g j)).edgeSet) := by
    intro i j hij
    rw [Set.disjoint_left]
    refine Sym2.ind (fun x y => ?_)
    intro he1 he2
    rw [mem_edgeSet, map_adj] at he1 he2
    obtain ⟨u, v, huv, rfl, rfl⟩ := he1
    obtain ⟨u', v', huv', hx, hy⟩ := he2
    have hx' := congrArg Fin.val hx
    have hy' := congrArg Fin.val hy
    rw [hg, hg] at hx' hy'
    have d1 := (Nat.modEq_iff_dvd.mp hx')
    have d2 := (Nat.modEq_iff_dvd.mp hy')
    push_cast at d1 d2
    have hu := hfle u
    have hv := hfle v
    have hu' := hfle u'
    have hv' := hfle v'
    have hi := i.isLt
    have hj := j.isLt
    have d3 := dvd_sub d1 d2
    have z := int_zero_of_dvd _ _ d3 (by omega) (by omega)
    have hdiff : ((f u : ℤ) - f v) = (f u' : ℤ) - f v' := by omega
    have hs : s(u, v) = s(u', v') := by
      apply hinjOn (by simpa using huv) (by simpa using huv')
      simp only [Sym2.lift_mk, hdiff]
    rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have z2 := int_zero_of_dvd _ _ d1 (by omega) (by omega)
      apply hij
      apply Fin.ext
      omega
    · have hfe : f u = f v := by omega
      exact huv.ne (hfinj hfe)
  refine ⟨g, hdisj, ?_⟩
  -- every copy has n edges
  have hcopy : ∀ i : Fin (2 * n + 1), (T.map (g i)).edgeSet.ncard = n := by
    intro i
    rw [SimpleGraph.edgeSet_map, Set.ncard_image_of_injective _ (g i).sym2Map.injective,
      hn]
  have hfin : ∀ i : Fin (2 * n + 1), ((T.map (g i)).edgeSet).Finite :=
    fun i => Set.finite_univ.subset (Set.subset_univ _)
  have hdisj' : Pairwise (Function.onFun Disjoint fun i : Fin (2 * n + 1) => (T.map (g i)).edgeSet) :=
    hdisj
  have hsup : (⨆ i, T.map (g i)).edgeSet = ⋃ i, (T.map (g i)).edgeSet := SimpleGraph.edgeSet_iSup
  have hleft : ((⨆ i, T.map (g i)).edgeSet).ncard = (2 * n + 1) * n := by
    rw [hsup, Set.ncard_iUnion_of_finite hfin hdisj', finsum_eq_sum_of_fintype,
      Finset.sum_const_nat (fun i _ => hcopy i), Finset.card_univ, Fintype.card_fin]
  have htop : ((⊤ : SimpleGraph (Fin (2 * n + 1))).edgeSet).ncard
      = Nat.choose (2 * n + 1) 2 := by
    rw [SimpleGraph.edgeSet_top, Set.ncard_eq_toFinset_card', Set.toFinset_card,
      Sym2.card_diagSet_compl, Fintype.card_fin]
  rw [← SimpleGraph.edgeSet_inj]
  have hsub : (⨆ i, T.map (g i)).edgeSet ⊆ (⊤ : SimpleGraph (Fin (2 * n + 1))).edgeSet :=
    SimpleGraph.edgeSet_mono le_top
  have heq : ((⨆ i, T.map (g i)).edgeSet).ncard
      = ((⊤ : SimpleGraph (Fin (2 * n + 1))).edgeSet).ncard := by
    rw [hleft, htop, h2 n]
  exact Set.eq_of_subset_of_ncard_le hsub (le_of_eq heq.symm)

end OMA.R_RingelConjecture_ringel_conjecture_R1
