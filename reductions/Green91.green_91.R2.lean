import FormalConjectures.GreensOpenProblems.«91»

-- Reduction Green91.green_91.R2. Credit: @a5teri5k
-- Even-to-odd transfer from Section 2 of Ferber, Kwan, Narayanan, Sah and Sawhney,
-- Friendly bisections of random graphs (arXiv:2105.13337). An even bisection can lose
-- at most the vertices of margin one. The two errors of 1/400 leave a 1/200
-- reserve for the added vertex and the required 99/100 fraction.
namespace OMA.R_Green91_green_91_R2

open Filter Green91 MeasureTheory
open scoped Topology Classical

/-- The strict friendly-bisection estimate on even orders, with slack for adding a vertex. -/
def H1 : Prop :=
  Tendsto (fun k : ℕ ↦ prob (2 * k) fun G ↦ ∃ s : Finset (Fin (2 * k)),
    s.card = k ∧ 399 * (2 * k) ≤ 400 * numFriendly G s) atTop (𝓝 1)

/-- A uniform small-margin estimate on even orders. Only vertices of margin one can be lost. -/
def H2 : Prop :=
  Tendsto (fun k : ℕ ↦ prob (2 * k) fun G ↦ ∃ s : Finset (Fin (2 * k)),
    s.card = k ∧ 2 * k < 400 * (Finset.univ.filter fun v ↦ friendliness G s v = 1).card)
    atTop (𝓝 0)

open MeasureTheory.Measure ProbabilityTheory

lemma coordinate_marginal {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (μ : β → Measure Prop) [∀ b, IsProbabilityMeasure (μ b)] :
    (infinitePi μ).map (fun (x : β → Prop) a ↦ x (f a)) = infinitePi (fun a ↦ μ (f a)) := by
  let e := Equiv.ofInjective f hf
  let E := MeasurableEquiv.piCongrLeft (fun _ : Set.range f ↦ Prop) e
  have hcomp : (fun (x : β → Prop) a ↦ x (f a)) =
      E.symm ∘ (Set.range f).domRestrict := by
    funext x a
    change x (f a) = (Equiv.piCongrLeft (fun _ : Set.range f ↦ Prop) e).symm
      ((Set.range f).domRestrict x) a
    rw [Equiv.piCongrLeft_symm_apply]
    rfl
  rw [hcomp, ← Measure.map_map E.symm.measurable (by fun_prop), infinitePi_map_restrict',
    ← infinitePi_map_piCongrLeft (fun i : Set.range f ↦ μ i.val) e]
  exact E.map_symm_map

lemma delete_zero_law (n : ℕ) (p : unitInterval) :
    (SimpleGraph.binomialRandom (Fin (n + 1)) p).map (fun G ↦ G.comap Fin.succ) =
      SimpleGraph.binomialRandom (Fin n) p := by
  let μ (m : ℕ) (i : Sym2 (Fin m)) : Measure Prop :=
    unitInterval.toNNReal p • Measure.dirac (¬ i.IsDiag) +
    unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False
  let graph (m : ℕ) (x : Sym2 (Fin m) → Prop) := SimpleGraph.fromEdgeSet {i | x i}
  have hg (m : ℕ) : Measurable (graph m) :=
    SimpleGraph.measurable_fromEdgeSet.comp MeasurableEquiv.setOfPred.measurable
  have law (m : ℕ) : SimpleGraph.binomialRandom (Fin m) p = (infinitePi (μ m)).map (graph m) := by
    rw [SimpleGraph.binomialRandom_eq_map, setBernoulli_eq_map]
    change ((infinitePi (μ m)).map (fun x : Sym2 (Fin m) → Prop ↦ {i | x i})).map
      SimpleGraph.fromEdgeSet = _
    exact Measure.map_map SimpleGraph.measurable_fromEdgeSet
      (show Measurable (fun x : Sym2 (Fin m) → Prop ↦ {i | x i}) from MeasurableEquiv.setOfPred.measurable)
  let f : Sym2 (Fin n) → Sym2 (Fin (n + 1)) := Sym2.map Fin.succ
  have hf : Function.Injective f := Sym2.map.injective (Fin.succ_injective _)
  let r (x : Sym2 (Fin (n + 1)) → Prop) (i : Sym2 (Fin n)) := x (f i)
  have hr : Measurable r := measurable_pi_lambda _ fun i ↦ measurable_pi_apply (f i)
  have hc : Measurable (fun G : SimpleGraph (Fin (n + 1)) ↦ G.comap Fin.succ) :=
    SimpleGraph.measurable_iff_adj.mpr fun _ _ ↦ by simp only [SimpleGraph.comap_adj]; fun_prop
  have hcomm : (fun G : SimpleGraph (Fin (n + 1)) ↦ G.comap Fin.succ) ∘ graph (n + 1) =
      graph n ∘ r := by
    funext x
    ext u v
    simp [graph, SimpleGraph.fromEdgeSet_adj, r, f]
  have hμ : (fun i ↦ μ (n + 1) (f i)) = μ n := by
    funext i
    simp [μ, f, Sym2.isDiag_map (Fin.succ_injective n)]
  let (i : Sym2 (Fin (n + 1))) : IsProbabilityMeasure (μ (n + 1) i) := by
    dsimp [μ]
    infer_instance
  rw [law, law, Measure.map_map hc (hg _), hcomm, ← Measure.map_map (hg _) hr,
    coordinate_marginal f hf, hμ]

/-- The event on the induced graph has its usual even-order probability. -/
lemma delete_zero_prob (n : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    prob (n + 1) (fun G ↦ P (G.comap Fin.succ)) = prob n P := by
  let s := {G | P G}
  have hs : MeasurableSet s := by
    have h := (Set.toFinite (SimpleGraph.edgeSet '' s)).measurableSet
    simpa only [Set.preimage_image_eq _ SimpleGraph.edgeSet_injective] using
      h.preimage SimpleGraph.measurable_edgeSet
  have hc : Measurable (fun G : SimpleGraph (Fin (n + 1)) ↦ G.comap Fin.succ) :=
    SimpleGraph.measurable_iff_adj.mpr fun _ _ ↦ by simp only [SimpleGraph.comap_adj]; fun_prop
  unfold prob
  rw [← delete_zero_law n, Measure.map_apply hc hs]
  rfl

lemma margin_after_extension {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (s : Finset (Fin n)) (v : Fin n) :
    friendliness (G.comap Fin.succ) s v - 1 ≤
      friendliness G (s.map (Fin.succEmb n)) v.succ := by
  have hm (w : Fin n) : w.succ ∈ s.map (Fin.succEmb n) ↔ w ∈ s :=
    Finset.mem_map' (Fin.succEmb n)
  unfold friendliness
  rw [Fin.card_filter_univ_succ' (fun w ↦ G.Adj v.succ w ∧
    (w ∈ s.map (Fin.succEmb n) ↔ v.succ ∈ s.map (Fin.succEmb n))),
    Fin.card_filter_univ_succ' (fun w ↦ G.Adj v.succ w ∧
    ¬ (w ∈ s.map (Fin.succEmb n) ↔ v.succ ∈ s.map (Fin.succEmb n)))]
  simp only [hm, SimpleGraph.comap_adj]
  split_ifs <;> omega

lemma friendly_after_extension {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (s : Finset (Fin n)) :
    numFriendly (G.comap Fin.succ) s ≤
      numFriendly G (s.map (Fin.succEmb n)) +
      (Finset.univ.filter fun v ↦ friendliness (G.comap Fin.succ) s v = 1).card := by
  let strong := Finset.univ.filter fun v ↦ 1 < friendliness (G.comap Fin.succ) s v
  let marginal := Finset.univ.filter fun v ↦ friendliness (G.comap Fin.succ) s v = 1
  have hsplit : (Finset.univ.filter fun v ↦ 0 < friendliness (G.comap Fin.succ) s v) ⊆
      strong ∪ marginal := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [strong, marginal, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hlift : strong.map (Fin.succEmb n) ⊆
      Finset.univ.filter (fun v ↦ 0 < friendliness G (s.map (Fin.succEmb n)) v) := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    have h := margin_after_extension G s v
    have hv' := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change 0 < friendliness G _ v.succ; omega⟩
  have hcard := Finset.card_le_card hlift
  rw [Finset.card_map] at hcard
  exact (Finset.card_le_card hsplit).trans <|
    (Finset.card_union_le strong marginal).trans (Nat.add_le_add_right hcard _)

theorem main : H1 → H2 → type_of% @Green91.green_91 := by
  intro heven hexception
  let E (k : ℕ) (G : SimpleGraph (Fin (2 * k))) := ∃ s : Finset (Fin (2 * k)),
    s.card = k ∧ 399 * (2 * k) ≤ 400 * numFriendly G s
  let B (k : ℕ) (G : SimpleGraph (Fin (2 * k))) := ∃ s : Finset (Fin (2 * k)),
    s.card = k ∧ 2 * k < 400 * (Finset.univ.filter fun v ↦ friendliness G s v = 1).card
  let T (n : ℕ) (G : SimpleGraph (Fin n)) := ∃ s : Finset (Fin n),
    s.card = n / 2 ∧ (99 / 100 : ℝ) * n ≤ numFriendly G s
  let p (k : ℕ) := prob (2 * k) (E k) - prob (2 * k) (B k)
  have he : Tendsto (fun k ↦ prob (2 * k) (E k)) atTop (𝓝 1) := heven
  have hb : Tendsto (fun k ↦ prob (2 * k) (B k)) atTop (𝓝 0) := hexception
  have hp : Tendsto p atTop (𝓝 1) := by
    simpa only [p, tsub_zero] using ENNReal.Tendsto.sub he hb (Or.inl (by simp))
  have he' (k) : p k ≤ prob (2 * k) (T (2 * k)) := by
    refine tsub_le_self.trans ?_
    apply measure_mono
    rintro G ⟨s, hs, h⟩
    refine ⟨s, by omega, ?_⟩
    have hh : 99 * (2 * k) ≤ 100 * numFriendly G s := by omega
    have hr : (99 : ℝ) * ((2 * k : ℕ) : ℝ) ≤ 100 * (numFriendly G s : ℝ) := by exact_mod_cast hh
    linarith
  -- The unused 1/200 covers the extra vertex precisely when k is at least 99.
  have ho (k : ℕ) (hk : 99 ≤ k) : p k ≤ prob (2 * k + 1) (T (2 * k + 1)) := by
    let P (G : SimpleGraph (Fin (2 * k))) := E k G ∧ ¬ B k G
    have hdiff : p k ≤ prob (2 * k) P := le_measure_sdiff
    refine hdiff.trans ?_
    rw [← delete_zero_prob (2 * k) P]
    apply measure_mono
    rintro G ⟨⟨s, hs, h⟩, hb'⟩
    have hthin : 400 * (Finset.univ.filter fun v ↦ friendliness (G.comap Fin.succ) s v = 1).card ≤
        2 * k := le_of_not_gt fun hbad ↦ hb' ⟨s, hs, hbad⟩
    have hlift := friendly_after_extension G s
    refine ⟨s.map (Fin.succEmb _), by rw [Finset.card_map, hs]; omega, ?_⟩
    have hh : 99 * (2 * k + 1) ≤ 100 * numFriendly G (s.map (Fin.succEmb _)) := by omega
    have hr : (99 : ℝ) * ((2 * k + 1 : ℕ) : ℝ) ≤
        100 * (numFriendly G (s.map (Fin.succEmb _)) : ℝ) := by exact_mod_cast hh
    linarith
  change Tendsto (fun n ↦ prob n (T n)) atTop (𝓝 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (hp.comp (Nat.tendsto_div_const_atTop (by decide : 2 ≠ 0))) tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 198] with n hn
    change p (n / 2) ≤ prob n (T n)
    generalize h : n / 2 = k
    rcases (show n = 2 * k ∨ n = 2 * k + 1 by omega) with rfl | rfl
    · exact he' k
    · exact ho k (by omega)
  · exact Eventually.of_forall fun _ ↦ prob_le_one

end OMA.R_Green91_green_91_R2
