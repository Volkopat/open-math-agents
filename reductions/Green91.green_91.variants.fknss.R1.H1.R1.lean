import OMAReductions.R_Green91_green_91_variants_fknss_R1

/-! The finite-trajectory argument of Section 2 of Ferber--Kwan--Narayanan--Sah--Sawhney
(https://arxiv.org/abs/2105.13337), and the odd-order transfer. -/

/- Restricting a binomial random graph to an embedded vertex set preserves its law. -/

namespace OMA.FriendlyBisection

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ProbabilityTheory

private noncomputable def draw {T : Type*} (p : I) (e : Sym2 T) : Measure Prop :=
  toNNReal p • Measure.dirac (¬ e.IsDiag) + toNNReal (σ p) • Measure.dirac False

private def assemble {T : Type*} (u : Sym2 T → Prop) : SimpleGraph T :=
  SimpleGraph.fromEdgeSet {e | u e}

private theorem measurable_assemble {T : Type*} [Countable T] : Measurable (@assemble T) :=
  SimpleGraph.measurable_fromEdgeSet.comp MeasurableEquiv.setOfPred.measurable

private theorem draw_assemble (T : Type*) [Countable T] (p : I) :
    SimpleGraph.binomialRandom T p = Measure.map assemble (infinitePi (draw p)) := by
  rw [SimpleGraph.binomialRandom_eq_map, setBernoulli_eq_map]
  have hSet : Measurable (fun u : Sym2 T → Prop => {i | u i}) :=
    MeasurableEquiv.setOfPred.measurable
  rw [Measure.map_map SimpleGraph.measurable_fromEdgeSet hSet]
  rfl

theorem binomialRandom_map_comap {V W : Type*} [Finite V] [Finite W]
    (f : V ↪ W) (p : I) :
    Measure.map (SimpleGraph.comap f) (SimpleGraph.binomialRandom W p) =
      SimpleGraph.binomialRandom V p := by
  classical
  let restrict (u : Sym2 W → Prop) (e : Sym2 V) := u (f.sym2Map e)
  have hR : Measurable restrict := by fun_prop
  have hC : Measurable (SimpleGraph.comap f) := by
    have hfun : SimpleGraph.comap f = assemble ∘
        (restrict ∘ (⇑MeasurableEquiv.setOfPred.symm ∘ SimpleGraph.edgeSet)) := by
      funext G
      ext v w
      change G.Adj (f v) (f w) ↔ (assemble (fun e => f.sym2Map e ∈ G.edgeSet)).Adj v w
      rw [assemble, SimpleGraph.fromEdgeSet_adj]
      simp only [Set.mem_ofPred_eq, Function.Embedding.sym2Map, Function.Embedding.coeFn_mk,
        Sym2.map_mk, SimpleGraph.mem_edgeSet]
      exact ⟨fun hadj => ⟨hadj, fun heq => hadj.ne (congrArg f heq)⟩, And.left⟩
    rw [hfun]
    exact measurable_assemble.comp (hR.comp (MeasurableEquiv.setOfPred.symm.measurable.comp
      SimpleGraph.measurableEmbedding_edgeSet.measurable))
  have hcomp : SimpleGraph.comap f ∘ assemble = assemble ∘ restrict := by
    funext u
    ext v w
    simp only [Function.comp_apply, SimpleGraph.comap_adj, assemble,
      SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq, restrict,
      Function.Embedding.sym2Map, Function.Embedding.coeFn_mk, Sym2.map_mk, ne_eq, f.injective.eq_iff]
  have hMarginal (e : Sym2 V) : draw p (f.sym2Map e) = draw p e := by
    have hDiag : (f.sym2Map e).IsDiag ↔ e.IsDiag := Sym2.isDiag_map f.injective
    simp only [draw, hDiag]
  let : ∀ e : Sym2 W, IsProbabilityMeasure (draw p e) := fun e => by
    constructor
    simp [draw]
  rw [draw_assemble W, draw_assemble V, Measure.map_map hC measurable_assemble, hcomp,
    ← Measure.map_map measurable_assemble hR]
  unfold restrict
  rw [Measure.map_infinitePi_infinitePi_of_inj f.sym2Map.injective]
  simp_rw [hMarginal]

end OMA.FriendlyBisection

/- Probability bookkeeping for finitely many graph events and for deleting one vertex. -/

namespace OMA.FriendlyBisection

open Green91 Filter MeasureTheory unitInterval
open scoped Topology Classical

private theorem graphEventMeasurable {n : ℕ} (P : SimpleGraph (Fin n) → Prop) :
    MeasurableSet {G | P G} := by
  let : MeasurableSingletonClass (SimpleGraph (Fin n)) := ⟨fun G => by
    have h := SimpleGraph.measurable_edgeSet
      (measurableSet_singleton (G.edgeSet : Set (Sym2 (Fin n))))
    have he : (SimpleGraph.edgeSet : SimpleGraph (Fin n) → Set (Sym2 (Fin n))) ⁻¹'
        {G.edgeSet} = {G} := by
      ext K
      simp [SimpleGraph.edgeSet_injective.eq_iff]
    exact he ▸ h⟩
  exact (Set.to_countable _).measurableSet

theorem prob_monotone {n : ℕ} {P Q : SimpleGraph (Fin n) → Prop}
    (h : ∀ G, P G → Q G) : prob n P ≤ prob n Q :=
  measure_mono h

theorem prob_le_one_event {n : ℕ} (P : SimpleGraph (Fin n) → Prop) : prob n P ≤ 1 :=
  prob_le_one

theorem prob_comap_castSucc {n : ℕ} (P : SimpleGraph (Fin n) → Prop) :
    prob (n + 1) (fun G => P (G.comap Fin.castSucc)) = prob n P := by
  let p : I := ⟨1 / 2, by norm_num⟩
  let f : SimpleGraph (Fin (n + 1)) → SimpleGraph (Fin n) := SimpleGraph.comap Fin.castSucc
  have hf : Measurable f := SimpleGraph.measurable_iff_adj.mpr fun v w => by
    change Measurable (fun G : SimpleGraph (Fin (n + 1)) => G.Adj v.castSucc w.castSucc)
    fun_prop
  rw [show prob (n + 1) (fun G => P (G.comap Fin.castSucc)) =
      SimpleGraph.binomialRandom (Fin (n + 1)) p (f ⁻¹' {G | P G}) from rfl]
  rw [← Measure.map_apply hf (graphEventMeasurable P)]
  rw [show Measure.map f (SimpleGraph.binomialRandom (Fin (n + 1)) p) =
      SimpleGraph.binomialRandom (Fin n) p from binomialRandom_map_comap Fin.castSuccEmb p]
  rfl

theorem high_mono {N : ℕ → ℕ}
    {P Q : ∀ j, SimpleGraph (Fin (N j)) → Prop}
    (himp : ∀ᶠ j in atTop, ∀ G, P j G → Q j G)
    (hP : Tendsto (fun j => prob (N j) (P j)) atTop (𝓝 1)) :
    Tendsto (fun j => prob (N j) (Q j)) atTop (𝓝 1) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' hP tendsto_const_nhds
    (himp.mono fun _ h => prob_monotone h)
    (Eventually.of_forall fun _ => prob_le_one_event _)

private theorem prob_inter_lower {n : ℕ} (P Q : SimpleGraph (Fin n) → Prop) :
    1 - ((1 - prob n P) + (1 - prob n Q)) ≤ prob n (fun G => P G ∧ Q G) := by
  let U : Set (SimpleGraph (Fin n)) := {G | P G}
  let V : Set (SimpleGraph (Fin n)) := {G | Q G}
  let μ := SimpleGraph.binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩
  have hU : MeasurableSet U := graphEventMeasurable P
  have hV : MeasurableSet V := graphEventMeasurable Q
  change 1 - ((1 - μ U) + (1 - μ V)) ≤ μ (U ∩ V)
  have hUnion : μ (U ∩ V)ᶜ ≤ μ Uᶜ + μ Vᶜ := by
    rw [Set.compl_inter]
    exact measure_union_le Uᶜ Vᶜ
  rw [prob_compl_eq_one_sub (hU.inter hV), prob_compl_eq_one_sub hU,
      prob_compl_eq_one_sub hV] at hUnion
  apply tsub_le_iff_right.mpr
  rw [add_comm]
  exact tsub_le_iff_right.mp hUnion

theorem high_inter {N : ℕ → ℕ}
    {P Q : ∀ j, SimpleGraph (Fin (N j)) → Prop}
    (hP : Tendsto (fun j => prob (N j) (P j)) atTop (𝓝 1))
    (hQ : Tendsto (fun j => prob (N j) (Q j)) atTop (𝓝 1)) :
    Tendsto (fun j => prob (N j) (fun G => P j G ∧ Q j G)) atTop (𝓝 1) := by
  have hConst : Tendsto (fun _ : ℕ => (1 : ENNReal)) atTop (𝓝 1) := tendsto_const_nhds
  have hcP : Tendsto (fun j => 1 - prob (N j) (P j)) atTop (𝓝 0) := by
    simpa only [tsub_self] using ENNReal.Tendsto.sub hConst hP (Or.inl ENNReal.one_ne_top)
  have hcQ : Tendsto (fun j => 1 - prob (N j) (Q j)) atTop (𝓝 0) := by
    simpa only [tsub_self] using ENNReal.Tendsto.sub hConst hQ (Or.inl ENNReal.one_ne_top)
  have hsum : Tendsto (fun j => (1 - prob (N j) (P j)) + (1 - prob (N j) (Q j))) atTop
      (𝓝 0) := by simpa only [add_zero] using hcP.add hcQ
  have hlow : Tendsto
      (fun j => 1 - ((1 - prob (N j) (P j)) + (1 - prob (N j) (Q j)))) atTop (𝓝 1) := by
    simpa only [tsub_zero] using ENNReal.Tendsto.sub hConst hsum (Or.inl ENNReal.one_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hConst
    (Eventually.of_forall fun j => prob_inter_lower (P j) (Q j))
    (Eventually.of_forall fun j => prob_le_one_event (fun G => P j G ∧ Q j G))

theorem tendsto_even_odd (f : ℕ → ENNReal)
    (he : Tendsto (fun m => f (2 * m)) atTop (𝓝 1))
    (ho : Tendsto (fun m => f (2 * m + 1)) atTop (𝓝 1)) :
    Tendsto f atTop (𝓝 1) := by
  have hhalf : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro m
    filter_upwards [eventually_ge_atTop (2 * m)] with n hn
    omega
  rw [Filter.tendsto_def]
  intro U hU
  filter_upwards [(he.comp hhalf).eventually hU, (ho.comp hhalf).eventually hU] with n hne hno
  change U (f n)
  by_cases h : n % 2 = 0
  · have hn : 2 * (n / 2) = n := by omega
    simpa only [Function.comp_apply, hn] using hne
  · have hn : 2 * (n / 2) + 1 = n := by omega
    simpa only [Function.comp_apply, hn] using hno

end OMA.FriendlyBisection

/- The deterministic part of the finite swapping argument. -/

namespace OMA.FriendlyBisection

open Green91
open scoped BigOperators Classical

private noncomputable def normalizedScore {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) : ℝ :=
  (∑ v, (friendliness G s v : ℝ)) / ((n : ℝ) * Real.sqrt n)

private noncomputable def badLeft {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun v => ¬ 0 < friendliness G s v ∧ v ∈ s).card

private noncomputable def badRight {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun v => ¬ 0 < friendliness G s v ∧ v ∉ s).card

theorem friendliness_partition {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n)) :
    numFriendly G s + badLeft G s + badRight G s = n := by
  let bad : Finset (Fin n) := Finset.univ.filter fun v => ¬ 0 < friendliness G s v
  have hone := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun v => 0 < friendliness G s v)
  have htwo := Finset.card_filter_add_card_filter_not (s := bad) (p := fun v => v ∈ s)
  have hone' : numFriendly G s + bad.card = n := by simpa [numFriendly, bad] using hone
  have htwo' : badLeft G s + badRight G s = bad.card := by
    simpa [Finset.filter_filter, bad, badLeft, badRight, and_comm] using htwo
  omega

/-- The first selection consists of the least friendly vertices of the given side,
    using the vertex ordering for ties. -/
private def lowest {n : ℕ} (G : SimpleGraph (Fin n)) (s side selected : Finset (Fin n)) : Prop :=
  selected ⊆ side ∧
    ∀ u ∈ selected, ∀ v ∈ side, v ∉ selected →
      friendliness G s u < friendliness G s v ∨
      (friendliness G s u = friendliness G s v ∧ u ≤ v)

/-- A possible outcome of one alpha-swap, including its arbitrary random second choice. -/
private def swapStep {n : ℕ} (α : ℝ) (G : SimpleGraph (Fin n)) (s t : Finset (Fin n)) : Prop :=
  ∃ A B : Finset (Fin n),
    A.card = ⌊α * (n : ℝ)⌋₊ ∧ B.card = A.card ∧
    lowest G s s A ∧ lowest G s (Finset.univ \ s) B ∧
    let s' := (s \ A) ∪ B
    ∃ C D : Finset (Fin n),
      C.card = ⌊α ^ 4 * (n : ℝ)⌋₊ ∧ D.card = C.card ∧
      C ⊆ s' ∧ D ⊆ Finset.univ \ s' ∧ t = (s' \ C) ∪ D

/-- A uniform gain cannot occur at every step inside the bounded score window. -/
theorem enough_steps (score l r : ℕ → ℝ) (γ β E : ℝ) (T : ℕ)
    (ht : 2 * γ < (T : ℝ) * β) (hr : ∀ j ≤ T, |score j| ≤ γ)
    (hg : ∀ j < T, E < l j → E < r j → score j + β ≤ score (j + 1)) :
    ∃ j < T, l j ≤ E ∨ r j ≤ E := by
  by_contra! h
  have hsteps : ∀ j ≤ T, score 0 + (j : ℝ) * β ≤ score j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hlt : j < T := by omega
      have hprevious := ih hlt.le
      have hnext := hg j hlt (h j hlt).1 (h j hlt).2
      push_cast
      linarith
  have hmin := (abs_le.mp (hr 0 (Nat.zero_le _))).1
  have hmax := (abs_le.mp (hr T le_rfl)).2
  linarith [hsteps T le_rfl]

theorem friendly_of_balanced_small_side {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) (E : ℝ)
    (hE : (badLeft G s : ℝ) ≤ E ∨ (badRight G s : ℝ) ≤ E)
    (hdiff : |(badLeft G s : ℝ) - (badRight G s : ℝ)| ≤ E) :
    (n : ℝ) - 3 * E ≤ numFriendly G s := by
  have hcount : (numFriendly G s : ℝ) + badLeft G s + badRight G s = n := by
    exact_mod_cast friendliness_partition G s
  have hh := abs_le.mp hdiff
  rcases hE with hl | hr <;> linarith

end OMA.FriendlyBisection

/- Extending a bisection by one vertex preserves all margins at least two. -/

namespace OMA.FriendlyBisection

open Green91
open scoped BigOperators Classical

private noncomputable def tieCount {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun v => friendliness G s v = 1).card

private noncomputable def signedContribution {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) (v w : Fin n) : ℤ :=
  if G.Adj v w then if (w ∈ s ↔ v ∈ s) then 1 else -1 else 0

private theorem friendliness_sum {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) (v : Fin n) :
    friendliness G s v = ∑ w, signedContribution G s v w := by
  unfold friendliness
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hAdj : G.Adj v w <;> by_cases hSide : (w ∈ s ↔ v ∈ s) <;>
    simp [signedContribution, hAdj, hSide]

private theorem friendliness_drops_at_most_one {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (s : Finset (Fin n)) (v : Fin n) :
    friendliness (G.comap Fin.castSucc) s v - 1 ≤
      friendliness G (s.map Fin.castSuccEmb) v.castSucc := by
  have hmem (x : Fin n) : x.castSucc ∈ s.map Fin.castSuccEmb ↔ x ∈ s := by
    change Fin.castSuccEmb x ∈ s.map Fin.castSuccEmb ↔ x ∈ s
    exact Finset.mem_map' Fin.castSuccEmb
  rw [friendliness_sum, friendliness_sum, Fin.sum_univ_castSucc]
  have heq : (∑ w : Fin n, signedContribution G (s.map Fin.castSuccEmb) v.castSucc w.castSucc) =
      ∑ w, signedContribution (G.comap Fin.castSucc) s v w := by
    apply Finset.sum_congr rfl
    intro w _
    simp only [signedContribution, hmem, SimpleGraph.comap_adj]
  rw [heq]
  have hLast : -1 ≤ signedContribution G (s.map Fin.castSuccEmb) v.castSucc (Fin.last n) := by
    unfold signedContribution
    split_ifs <;> norm_num
  omega

theorem friendly_extension {n : ℕ} (G : SimpleGraph (Fin (n + 1))) (s : Finset (Fin n)) :
    numFriendly (G.comap Fin.castSucc) s ≤
      numFriendly G (s.map Fin.castSuccEmb) + tieCount (G.comap Fin.castSucc) s := by
  let G' := G.comap Fin.castSucc
  let F : Finset (Fin n) := Finset.univ.filter (fun v => 0 < friendliness G' s v)
  let R : Finset (Fin n) := Finset.univ.filter (fun v => 1 < friendliness G' s v)
  let T : Finset (Fin n) := Finset.univ.filter (fun v => friendliness G' s v = 1)
  have hR : F.filter (fun v => 1 < friendliness G' s v) = R := by
    ext v
    simp only [F, R, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hT : F.filter (fun v => ¬ 1 < friendliness G' s v) = T := by
    ext v
    simp only [F, T, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hsplit : R.card + T.card = F.card := by
    rw [← hR, ← hT]
    exact Finset.card_filter_add_card_filter_not (s := F) _
  have hR' : R.map Fin.castSuccEmb ⊆
      Finset.univ.filter (fun v => 0 < friendliness G (s.map Fin.castSuccEmb) v) := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    have hv' : 1 < friendliness (G.comap Fin.castSucc) s v := (Finset.mem_filter.mp hv).2
    have hdrop := friendliness_drops_at_most_one G s v
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change 0 < friendliness G (s.map Fin.castSuccEmb) v.castSucc
    omega
  have hcard := Finset.card_le_card hR'
  rw [Finset.card_map] at hcard
  change F.card ≤ _ + T.card
  rw [← hsplit]
  exact Nat.add_le_add_right hcard _

end OMA.FriendlyBisection

namespace OMA.R_Green91_green_91_variants_fknss_R1_H1_R1

open Green91 Filter OMA.FriendlyBisection
open scoped Topology Classical

private def successful {n : ℕ} (error : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ s : Finset (Fin n), s.card = n / 2 ∧ (n : ℝ) - error * n ≤ numFriendly G s

/-- The uniform score range, in the normalization by (n^{3/2}) of Lemma 2.1. -/
def H1 : Prop := ∃ γ : ℝ, 0 < γ ∧
  Tendsto (fun m : ℕ => prob (2 * m) fun G => ∀ s : Finset (Fin (2 * m)),
    s.card = m → |normalizedScore G s| ≤ γ) atTop (𝓝 1)

/-- The uniform gain when both sides have many unfriendly vertices, from Lemma 2.3. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
  ∃ α β : ℝ, 0 < α ∧ α < 1 / 4 ∧ 0 < β ∧
    Tendsto (fun m : ℕ => prob (2 * m) fun G =>
      ∀ s t : Finset (Fin (2 * m)), s.card = m → swapStep α G s t →
        ε * (2 * m : ℕ) < badLeft G s → ε * (2 * m : ℕ) < badRight G s →
        normalizedScore G s + β ≤ normalizedScore G t) atTop (𝓝 1)

/-- With high probability the graph admits a fixed-length trajectory whose two unfriendly counts
stay close. Applying Lemma 2.4 at times 1 through (T+1) gives this projected event. -/
def H3 : Prop := ∀ α : ℝ, 0 < α → α < 1 / 4 → ∀ ε : ℝ, 0 < ε → ∀ T : ℕ,
  Tendsto (fun m : ℕ => prob (2 * m) fun G =>
    ∃ s : ℕ → Finset (Fin (2 * m)),
      (∀ j ≤ T, (s j).card = m ∧
        |(badLeft G (s j) : ℝ) - (badRight G (s j) : ℝ)| ≤ ε * (2 * m : ℕ)) ∧
      (∀ j < T, swapStep α G (s j) (s (j + 1)))) atTop (𝓝 1)

/-- Uniform smallness of the fraction of vertices with margin exactly one on even graphs.
This anti-concentration estimate is the parity observation in Section 2. -/
def H4 : Prop := ∀ ε : ℝ, 0 < ε →
  Tendsto (fun m : ℕ => prob (2 * m) fun G => ∀ s : Finset (Fin (2 * m)),
    s.card = m → (tieCount G s : ℝ) ≤ ε * (2 * m : ℕ)) atTop (𝓝 1)

theorem even_success (hWin : H1) (hGain : H2) (hPath : H3)
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1 / 4) :
    Tendsto (fun m : ℕ => prob (2 * m) (successful (3 * ε))) atTop (𝓝 1) := by
  obtain ⟨γ, _, hwindow⟩ := hWin
  obtain ⟨α, β, hα, hαsmall, hβ, hgain⟩ := hGain ε hε hεsmall
  obtain ⟨T, hT⟩ := exists_nat_gt (2 * γ / β)
  have hsteps := (div_lt_iff₀ hβ).mp hT
  have hpath := hPath α hα hαsmall ε hε T
  refine high_mono ?_ (high_inter hwindow (high_inter hgain hpath))
  apply Eventually.of_forall
  intro m G ⟨hwin, hg, s, hs, hswaps⟩
  let E := ε * (2 * m : ℕ)
  obtain ⟨j, hj, hside⟩ := enough_steps
    (fun j => normalizedScore G (s j)) (fun j => badLeft G (s j)) (fun j => badRight G (s j))
    γ β E T hsteps (fun j hj => hwin (s j) (hs j hj).1)
    (fun j hj hl hr => hg (s j) (s (j + 1)) (hs j hj.le).1 (hswaps j hj) hl hr)
  have hcount := friendly_of_balanced_small_side G (s j) E hside (hs j hj.le).2
  refine ⟨s j, (hs j hj.le).1.trans (by omega), ?_⟩
  simpa only [E, mul_assoc] using hcount

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green91_green_91_variants_fknss_R1.H1 := by
  intro hWin hGain hPath hTie k
  let η : ℝ := 1 / ((k : ℝ) + 1)
  let ε : ℝ := η / 8
  have hη : 0 < η := by positivity
  have hηle : η ≤ 1 := by
    dsimp [η]
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    have : (0 : ℝ) ≤ k := by positivity
    linarith
  have hε : 0 < ε := by positivity
  have hεsmall : ε < 1 / 4 := by dsimp [ε]; linarith
  have hηeq : η = 8 * ε := by dsimp [ε]; ring
  have heven := even_success hWin hGain hPath hε hεsmall
  let f (n : ℕ) := prob n (successful η)
  change Tendsto f atTop (𝓝 1)
  apply tendsto_even_odd f
  · unfold f
    refine high_mono ?_ heven
    apply Eventually.of_forall
    intro m G ⟨s, hs, hcount⟩
    refine ⟨s, hs, ?_⟩
    rw [hηeq]
    have hh : 0 ≤ ε * ((2 * m : ℕ) : ℝ) := by positivity
    nlinarith
  · let P (m : ℕ) (G : SimpleGraph (Fin (2 * m))) : Prop :=
      successful (3 * ε) G ∧ ∀ s : Finset (Fin (2 * m)),
        s.card = m → (tieCount G s : ℝ) ≤ ε * (2 * m : ℕ)
    have hP : Tendsto (fun m => prob (2 * m) (P m)) atTop (𝓝 1) :=
      high_inter heven (hTie ε hε)
    have hPull : Tendsto
        (fun m => prob (2 * m + 1) (fun G => P m (G.comap Fin.castSucc))) atTop (𝓝 1) := by
      simpa only [prob_comap_castSucc] using hP
    unfold f
    refine high_mono ?_ hPull
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / (2 * ε))
    filter_upwards [eventually_ge_atTop M] with m hm
    intro G ⟨⟨s, hs, hf⟩, ht⟩
    refine ⟨s.map Fin.castSuccEmb, ?_, ?_⟩
    · rw [Finset.card_map, hs]
      omega
    · have ht' := ht s (hs.trans (by omega))
      have hf' : (numFriendly (G.comap Fin.castSucc) s : ℝ) ≤
          (numFriendly G (s.map Fin.castSuccEmb) : ℝ) + tieCount (G.comap Fin.castSucc) s := by
        exact_mod_cast friendly_extension G s
      have hm' : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hM' := (div_lt_iff₀ (by positivity : 0 < 2 * ε)).mp hM
      have hlarge : 1 ≤ ε * ((2 * m : ℕ) : ℝ) := by
        push_cast
        nlinarith [mul_nonneg (sub_nonneg.mpr hm') hε.le]
      push_cast [hηeq]
      push_cast at hf ht'
      push_cast at hlarge
      nlinarith

end OMA.R_Green91_green_91_variants_fknss_R1_H1_R1
