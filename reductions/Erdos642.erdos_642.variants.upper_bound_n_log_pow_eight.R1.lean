import FormalConjectures.ErdosProblems.«642»
import Mathlib.Data.List.Sym

/-! The regular-expander reduction for the upper bound on Erdős Problem 642. -/

namespace Erdos642

open SimpleGraph

variable {V W : Type*} {H : SimpleGraph V} {G : SimpleGraph W}

theorem isChord_map (f : H →g G) (hf : Function.Injective f)
    {u v : V} (c : H.Walk u v) (e : Sym2 V) :
    c.IsChord e → (c.map f).IsChord (Sym2.map f e) := by
  refine Sym2.inductionOn e ?_
  intro a b he
  obtain ⟨hab, hn, ha, hb⟩ := Walk.isChord_sym2Mk.mp he
  rw [Sym2.map_mk, Walk.isChord_sym2Mk]
  refine ⟨f.map_adj hab, ?_, ?_, ?_⟩
  · rw [Walk.edges_map]
    intro hedges
    obtain ⟨e', he', heq⟩ := List.mem_map.mp hedges
    have heq' : e' = s(a, b) := Sym2.map.injective hf (heq.trans (Sym2.map_mk f a b).symm)
    exact hn (heq' ▸ he')
  · rw [Walk.support_map]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  · rw [Walk.support_map]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩

private theorem finite_chords {u v : W} (c : G.Walk u v) :
    {e : Sym2 W | c.IsChord e}.Finite := by
  refine c.support.sym2.finite_toSet.subset ?_
  intro e
  refine Sym2.inductionOn e ?_
  intro a b he
  obtain ⟨_, _, ha, hb⟩ := Walk.isChord_sym2Mk.mp he
  exact List.mk_mem_sym2 ha hb

theorem cyclesHaveMoreVerticesThanChords_of_injective_hom
    (f : H →g G) (hf : Function.Injective f)
    (hG : CyclesHaveMoreVerticesThanChords G) : CyclesHaveMoreVerticesThanChords H := by
  intro v c hc
  have hcard : {e : Sym2 V | c.IsChord e}.ncard ≤
      {e : Sym2 W | (c.map f).IsChord e}.ncard :=
    Set.ncard_le_ncard_of_injOn (Sym2.map f) (isChord_map f hf c)
      (Sym2.map.injective hf).injOn (finite_chords (c.map f))
  have hlt := hG (f v) (c.map f) (hc.map hf)
  rw [Walk.length_map] at hlt
  exact hcard.trans_lt hlt

end Erdos642

namespace OMA.R_Erdos642_erdos_642_variants_upper_bound_n_log_pow_eight_R1

open Filter Asymptotics

/-- The almost-regular bipartite expander extracted in DMMS24, Lemma 2.4. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
    Real.log n ^ 2 ≤ 2 * (G.edgeSet.ncard : ℝ) / n →
      ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ ∃ H : SimpleGraph (Fin m), ∃ f : H →g G,
        Function.Injective f ∧ H.IsBipartite ∧
        (∀ u v : Fin m, (H.neighborSet u).ncard ≤ 100 * (H.neighborSet v).ncard) ∧
        (2 * (G.edgeSet.ncard : ℝ) / n) / (600 * Real.log n) ≤
          2 * (H.edgeSet.ncard : ℝ) / m ∧
        (∀ S : Finset (Fin m), 2 * S.card ≤ m →
          (1 / (10 * Real.log n)) * (2 * (H.edgeSet.ncard : ℝ) / m) * S.card ≤
            ({e ∈ H.edgeSet | ∃ u v : Fin m, u ∈ S ∧ v ∉ S ∧ e = s(u, v)}.ncard : ℝ))

/-- The random-walk argument in DMMS24, Section 3, restricted to the extracted graphs. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m → m ≤ n → ∀ H : SimpleGraph (Fin m),
    H.IsBipartite →
    (∀ u v : Fin m, (H.neighborSet u).ncard ≤ 100 * (H.neighborSet v).ncard) →
    Real.log n ^ 7 / 600 ≤ 2 * (H.edgeSet.ncard : ℝ) / m →
    (∀ S : Finset (Fin m), 2 * S.card ≤ m →
      (1 / (10 * Real.log n)) * (2 * (H.edgeSet.ncard : ℝ) / m) * S.card ≤
        ({e ∈ H.edgeSet | ∃ u v : Fin m, u ∈ S ∧ v ∉ S ∧ e = s(u, v)}.ncard : ℝ)) →
    ¬ Erdos642.CyclesHaveMoreVerticesThanChords H

theorem main : H1 → H2 → type_of% @Erdos642.erdos_642.variants.upper_bound_n_log_pow_eight := by
  intro hextract hforce
  have hnlarge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [hextract, hforce, hnlarge, eventually_ge_atTop (1 : ℕ)]
    with n hclean hcycle hlog hn
  simp only [Real.norm_natCast, Real.norm_of_nonneg (show 0 ≤ (n : ℝ) * Real.log n ^ 8 by positivity),
    one_mul]
  obtain ⟨G, hG, hm⟩ := Erdos642.exists_maxEdges n
  rw [← hm]
  by_contra! hedges
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hlogPos : 0 < Real.log n := zero_lt_one.trans_le hlog
  have hratio : Real.log n ^ 8 ≤ (G.edgeSet.ncard : ℝ) / n :=
    (le_div_iff₀ hnpos).mpr (by simpa only [mul_comm] using hedges.le)
  have havg : Real.log n ^ 8 ≤ 2 * (G.edgeSet.ncard : ℝ) / n :=
    hratio.trans (div_le_div_of_nonneg_right
      (by linarith only [show 0 ≤ (G.edgeSet.ncard : ℝ) by positivity]) hnpos.le)
  have hpow : Real.log n ^ 2 ≤ Real.log n ^ 8 := pow_le_pow_right₀ hlog (by decide)
  obtain ⟨m, hmpos, hmle, H, f, hf, hbp, hreg, hd, hexp⟩ := hclean G (hpow.trans havg)
  have hnormalize : Real.log n ^ 8 / (600 * Real.log n) = Real.log n ^ 7 / 600 := by
    field_simp [hlogPos.ne']
  have hdegree : Real.log n ^ 7 / 600 ≤ 2 * (H.edgeSet.ncard : ℝ) / m := by
    rw [← hnormalize]
    exact (div_le_div_of_nonneg_right havg (by positivity : 0 ≤ 600 * Real.log n)).trans hd
  exact hcycle m hmpos hmle H hbp hreg hdegree hexp (Erdos642.cyclesHaveMoreVerticesThanChords_of_injective_hom f hf hG)

end OMA.R_Erdos642_erdos_642_variants_upper_bound_n_log_pow_eight_R1
