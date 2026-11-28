import FormalConjectures.ErdosProblems.«165»

/-! The upper-bound step is restricted to graphs of minimal edge set at extremal order. -/

-- Reduction Erdos165.erdos_165.variants.conjecture.R2 of Erdős Problem 165 — conjecture
-- Credit: @Pixelstorm44

namespace OMA.R_Erdos165_erdos_165_variants_conjecture_R2

open Filter SimpleGraph

/-- The lower estimate of Hefty, Horn, King and Pfender. -/
def H1 : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
    (1 - ε) * ((k : ℝ) ^ 2 / (2 * Real.log k)) ≤ (classicalRamsey 3 k : ℝ)

/-- It suffices to bound the order of edge-minimal graphs avoiding an independent
k-set in which each independent set has a disjoint independent (k-1)-set. -/
def H2 : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 3 →
      Minimal (fun H : SimpleGraph (Fin n) ↦ H.IndepSetFree k) G →
      (∀ S : Finset (Fin n), G.IsIndepSet S →
        ∃ T : Finset (Fin n), Disjoint S T ∧ G.IsNIndepSet (k - 1) T) →
      (n : ℝ) + 1 ≤ (1 + ε) * ((k : ℝ) ^ 2 / (2 * Real.log k))

/-- Maximal order forces independent sets to have disjoint maximum witnesses. -/
lemma avoid_at_extremal_order {n k : ℕ} (hr : classicalRamsey 3 k = n + 1)
    {G : SimpleGraph (Fin n)} (hg : G.CliqueFree 3) (hi : G.IndepSetFree k)
    (S : Finset (Fin n)) (hs : G.IsIndepSet S) :
    ∃ T : Finset (Fin n), Disjoint S T ∧ G.IsNIndepSet (k - 1) T := by
  classical
  let A := {m : ℕ | ∀ C : SimpleGraph (Fin m),
    (completeGraph (Fin 3)).IsContained C ∨ (completeGraph (Fin k)).IsContained Cᶜ}
  have hr' : sInf A = n + 1 := hr
  have hA : A.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h] at hr'
    simp at hr'
  have hmem : n + 1 ∈ A := hr' ▸ Nat.sInf_mem hA
  let F : SimpleGraph (Option (Fin n)) := {
    Adj
      | none, none => False
      | some x, none | none, some x => x ∈ S
      | some x, some y => G.Adj x y
    symm := by
      constructor
      rintro (_ | x) (_ | y) h <;> first | exact h | exact G.adj_symm h
    loopless := by
      constructor
      rintro (_ | x)
      · exact id
      · exact G.loopless.irrefl x }
  let e := SimpleGraph.Embedding.comap (finSuccEquiv n).toEmbedding F
  have hor := hmem (F.comap (finSuccEquiv n))
  have hfree : F.CliqueFree 3 := by
    intro U hU
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.mp hU
    cases a <;> cases b <;> cases c <;> simp only [F] at hab hac hbc
    all_goals first
      | contradiction
      | exact hs hab hac hbc.ne hbc
      | exact hs hab hbc hac.ne hac
      | exact hs hac hbc hab.ne hab
      | exact hg _ (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)
  obtain ⟨U, hU⟩ : ∃ U, F.IsNIndepSet k U := by
    have hn : ¬ F.IndepSetFree k := by
      intro hf
      rcases hor with ht | ha
      · exact ((not_cliqueFree_iff_top_isContained 3).mpr (ht.trans e.isContained)) hfree
      · exact ((not_cliqueFree_iff_top_isContained k).mpr
          (ha.trans (SimpleGraph.Embedding.complEquiv e).isContained)) (F.cliqueFree_compl.mpr hf)
    simpa only [IndepSetFree, not_forall, not_not] using hn
  have hold : G.IsIndepSet U.eraseNone := by
    intro a ha b hb hab
    exact hU.isIndepSet (Finset.mem_eraseNone.mp ha) (Finset.mem_eraseNone.mp hb)
      (fun h => hab (Option.some.inj h))
  have hnew : none ∈ U := by
    by_contra h
    exact hi U.eraseNone ⟨hold, (Finset.card_eraseNone_of_not_mem h).trans hU.card_eq⟩
  refine ⟨U.eraseNone, Finset.disjoint_left.mpr ?_, hold, ?_⟩
  · intro x hx hxU
    exact hU.isIndepSet hnew (Finset.mem_eraseNone.mp hxU) (by simp) hx
  · rw [Finset.card_eraseNone_of_mem hnew, hU.card_eq]

lemma extremal_witness {n k : ℕ} (hr : classicalRamsey 3 k = n + 1) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧
      Minimal (fun H : SimpleGraph (Fin n) ↦ H.IndepSetFree k) G ∧
      ∀ S : Finset (Fin n), G.IsIndepSet S →
        ∃ T : Finset (Fin n), Disjoint S T ∧ G.IsNIndepSet (k - 1) T := by
  classical
  have hlt : n < classicalRamsey 3 k := by omega
  unfold classicalRamsey graphRamsey at hlt
  have h := Nat.notMem_of_lt_sInf hlt
  simp only [Set.mem_ofPred_eq, not_forall, not_or] at h
  obtain ⟨C, hc, hi⟩ := h
  have hc' : C.CliqueFree 3 := by
    by_contra hn
    exact hc ((not_cliqueFree_iff_top_isContained 3).mp hn)
  have hi' : C.IndepSetFree k := by
    apply C.cliqueFree_compl.mp
    by_contra hn
    exact hi ((not_cliqueFree_iff_top_isContained k).mp hn)
  obtain ⟨G, hGC, hm⟩ := exists_minimal_le_of_wellFoundedLT
    (fun H : SimpleGraph (Fin n) ↦ H.IndepSetFree k) C hi'
  have hg := hc'.anti hGC
  exact ⟨G, hg, hm, avoid_at_extremal_order hr hg hm.prop⟩

theorem main : H1 → H2 → type_of% @Erdos165.erdos_165.variants.conjecture := by
  intro hlo hup
  apply Asymptotics.isEquivalent_of_tendsto_one
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : 0 < ε / 2 := by positivity
  filter_upwards [hlo (ε / 2) he, hup (ε / 2) he, eventually_ge_atTop (2 : ℕ)]
    with k hl hu hk
  have hk' : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hlog := Real.log_pos hk'
  have hg : 0 < ((k : ℝ) ^ 2 / (2 * Real.log k)) := by positivity
  have upper : (classicalRamsey 3 k : ℝ) ≤ (1 + ε / 2) * ((k : ℝ) ^ 2 / (2 * Real.log k)) := by
    cases hr : classicalRamsey 3 k with
    | zero => simp only [Nat.cast_zero]; positivity
    | succ n =>
      obtain ⟨G, ht, hm, ha⟩ := extremal_witness hr
      simpa only [Nat.cast_succ] using hu n G ht hm ha
  have lo := (le_div_iff₀ hg).mpr hl
  have up := (div_le_iff₀ hg).mpr upper
  change Dist.dist ((classicalRamsey 3 k : ℝ) / ((k : ℝ) ^ 2 / (2 * Real.log k))) 1 < ε
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end OMA.R_Erdos165_erdos_165_variants_conjecture_R2
