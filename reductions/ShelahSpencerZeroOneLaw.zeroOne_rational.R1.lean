import FormalConjectures.Paper.ShelahSpencerZeroOneLaw

/-!
Reduction of `ShelahSpencerZeroOneLaw.zeroOne_rational` (Shelah and Spencer,
*Zero-one laws for sparse random graphs*, J. Amer. Math. Soc. 1 (1988), 97-115, Theorem 2)
to two unconditional, disjoint sparse-random-graph definability hypotheses from Shelah-Spencer:
`H1` (Section 3, unit-fraction rational exponents `1 / q` for `q >= 2`) and
`H2` (Section 4, general coprime rational exponents `p / q` for `2 <= p < q`),
each asserting the existence of first-order graph formulas `(valid, dom, lt, mem)` whose
interpreted linear orders `(D_a, <_a)` satisfy `UNIV` with respect to the definable membership
predicate `mem` and oscillate in size modulo 100 across `[10, 40]` vs outside `[10, 40]` along
two subsequences of `n` with `G(n, n^(-p/q))` probability at least `3/4`.

In `main`, we prove completely from scratch in Lean 4:
1. Coprime rational decomposition `alpha = p / q` (`1 <= p < q`, `Nat.Coprime p q`),
   discrete measurability of all sets of `SimpleGraph (Fin n)`, disjoint-event probability
   complement bounds (`>= 3/4` implies complement `<= 1/4`), and `ENNReal` non-convergence.
2. Finite linear order enumeration `Fin D.card -> Fin n`, unique min/max/immediate-successor
   characterization, deterministic mod-100 counter soundness by induction on `D.card`, and
   completeness under `UNIV` via 7-bit slice encoding.
3. Exact 7-bit binary arithmetic and compact ripple-carry increment-mod-100 circuit semantics
   compiled into `FirstOrder.Language.graph.BoundedFormula`.
4. Full first-order graph sentence compiler building `phi : FirstOrder.Language.graph.Sentence`
   from `(valid, dom, lt, mem)` and combining soundness, completeness, and measure bounds to
   deduce `ShelahSpencerZeroOneLaw.zeroOne_rational`.
-/

namespace OMA.R_ShelahSpencerZeroOneLaw_zeroOne_rational_R1

/- Shelah-Spencer (1988) Section 3: for every unit-fraction rational exponent alpha = 1 / q
(q >= 2), there exist first-order graph formulas (valid, dom, lt, mem) in k parameters whose
interpreted nonempty linear orders (D_a, <_a) satisfy UNIV with respect to mem and oscillate
in size modulo 100 between [10, 40] and outside [10, 40] with G(n, n^(-1/q)) probability >= 3/4. -/
def H1 : Prop :=
  ∀ (q : ℕ), 2 ≤ q → ∀ (hα : (0 : ℝ) < (1 : ℝ) / (q : ℝ)),
    ∃ (k : ℕ)
      (valid_φ : FirstOrder.Language.graph.Formula (Fin k))
      (dom_φ : FirstOrder.Language.graph.Formula (Fin (k + 1)))
      (lt_φ : FirstOrder.Language.graph.Formula (Fin (k + 2)))
      (mem_φ : FirstOrder.Language.graph.Formula (Fin (k + 2))),
      let ok (n : ℕ) (G : SimpleGraph (Fin n)) (a : Fin k → Fin n) (D : Finset (Fin n)) : Prop :=
        let lt (x y : Fin n) :=
          @FirstOrder.Language.Formula.Realize _ _ G.structure _ lt_φ (Fin.snoc (Fin.snoc a x) y)
        @FirstOrder.Language.Formula.Realize _ _ G.structure _ valid_φ a ∧
        (∀ x, x ∈ D ↔ @FirstOrder.Language.Formula.Realize _ _ G.structure _ dom_φ (Fin.snoc a x)) ∧
        D.Nonempty ∧
        (∀ x ∈ D, ¬ lt x x) ∧
        (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, lt x y → lt y z → lt x z) ∧
        (∀ x ∈ D, ∀ y ∈ D, lt x y ∨ x = y ∨ lt y x)
      Filter.Frequently (fun n : ℕ =>
        (3 : ENNReal) / 4 ≤ ShelahSpencerZeroOneLaw.sparseRandomGraph n ((1 : ℝ) / (q : ℝ)) hα
          {G | ∃ a D, ok n G a D ∧
            (∀ S ⊆ D, ∃ v, ∀ x ∈ D,
              @FirstOrder.Language.Formula.Realize _ _ G.structure _ mem_φ
                (Fin.snoc (Fin.snoc a v) x) ↔ x ∈ S) ∧
            10 ≤ (D.card - 1) % 100 ∧ (D.card - 1) % 100 ≤ 40}) Filter.atTop ∧
      Filter.Frequently (fun n : ℕ =>
        (3 : ENNReal) / 4 ≤ ShelahSpencerZeroOneLaw.sparseRandomGraph n ((1 : ℝ) / (q : ℝ)) hα
          {G | ∀ a D, ok n G a D →
            ¬ (10 ≤ (D.card - 1) % 100 ∧ (D.card - 1) % 100 ≤ 40)}) Filter.atTop

/- Shelah-Spencer (1988) Section 4: for every non-unit coprime rational exponent alpha = p / q
(2 <= p < q, Nat.Coprime p q), there exist first-order graph formulas (valid, dom, lt, mem) in
k parameters whose interpreted nonempty linear orders (D_a, <_a) satisfy UNIV with respect to mem
and oscillate in size modulo 100 between [10, 40] and outside [10, 40] with G(n, n^(-p/q))
probability >= 3/4. -/
def H2 : Prop :=
  ∀ (p q : ℕ), 2 ≤ p → p < q → Nat.Coprime p q → ∀ (hα : (0 : ℝ) < (p : ℝ) / (q : ℝ)),
    ∃ (k : ℕ)
      (valid_φ : FirstOrder.Language.graph.Formula (Fin k))
      (dom_φ : FirstOrder.Language.graph.Formula (Fin (k + 1)))
      (lt_φ : FirstOrder.Language.graph.Formula (Fin (k + 2)))
      (mem_φ : FirstOrder.Language.graph.Formula (Fin (k + 2))),
      let ok (n : ℕ) (G : SimpleGraph (Fin n)) (a : Fin k → Fin n) (D : Finset (Fin n)) : Prop :=
        let lt (x y : Fin n) :=
          @FirstOrder.Language.Formula.Realize _ _ G.structure _ lt_φ (Fin.snoc (Fin.snoc a x) y)
        @FirstOrder.Language.Formula.Realize _ _ G.structure _ valid_φ a ∧
        (∀ x, x ∈ D ↔ @FirstOrder.Language.Formula.Realize _ _ G.structure _ dom_φ (Fin.snoc a x)) ∧
        D.Nonempty ∧
        (∀ x ∈ D, ¬ lt x x) ∧
        (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, lt x y → lt y z → lt x z) ∧
        (∀ x ∈ D, ∀ y ∈ D, lt x y ∨ x = y ∨ lt y x)
      Filter.Frequently (fun n : ℕ =>
        (3 : ENNReal) / 4 ≤ ShelahSpencerZeroOneLaw.sparseRandomGraph n ((p : ℝ) / (q : ℝ)) hα
          {G | ∃ a D, ok n G a D ∧
            (∀ S ⊆ D, ∃ v, ∀ x ∈ D,
              @FirstOrder.Language.Formula.Realize _ _ G.structure _ mem_φ
                (Fin.snoc (Fin.snoc a v) x) ↔ x ∈ S) ∧
            10 ≤ (D.card - 1) % 100 ∧ (D.card - 1) % 100 ≤ 40}) Filter.atTop ∧
      Filter.Frequently (fun n : ℕ =>
        (3 : ENNReal) / 4 ≤ ShelahSpencerZeroOneLaw.sparseRandomGraph n ((p : ℝ) / (q : ℝ)) hα
          {G | ∀ a D, ok n G a D →
            ¬ (10 ≤ (D.card - 1) % 100 ∧ (D.card - 1) % 100 ≤ 40)}) Filter.atTop

/- ============================================================================
   Part 1: Rational Decomposition, Graph Measurability, and ENNReal Non-Convergence
   ============================================================================ -/

/- Every rational real number in (0, 1) has a reduced fraction representation p / q
with 1 <= p < q and Nat.Coprime p q. -/
lemma rat_coprime_repr {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (hrat : ¬ Irrational α) :
    ∃ p q : ℕ, 1 ≤ p ∧ p < q ∧ Nat.Coprime p q ∧ α = (p : ℝ) / (q : ℝ) := by
  have hmem : α ∈ Set.range ((↑) : ℚ → ℝ) := by
    by_contra hnot
    exact hrat hnot
  rcases hmem with ⟨r, rfl⟩
  have hnum_pos : 0 < r.num := by
    have hden_pos : (0 : ℝ) < (r.den : ℝ) := Nat.cast_pos.mpr r.den_pos
    rw [Rat.cast_def] at h0
    have hnumR : (0 : ℝ) < (r.num : ℝ) := by
      have := mul_pos h0 hden_pos
      rwa [div_mul_cancel₀ _ (ne_of_gt hden_pos)] at this
    exact_mod_cast hnumR
  let p : ℕ := r.num.natAbs
  let q : ℕ := r.den
  have hp_eq : (p : ℤ) = r.num := Int.natAbs_of_nonneg (le_of_lt hnum_pos)
  have hp_pos : 1 ≤ p := by omega
  have hcast_eq : (r : ℝ) = (p : ℝ) / (q : ℝ) := by
    rw [Rat.cast_def]
    have hnum_eq : (r.num : ℝ) = (p : ℝ) := by exact_mod_cast hp_eq.symm
    rw [hnum_eq]
  have hp_lt_q : p < q := by
    rw [hcast_eq] at h1
    have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr r.den_pos
    have hR : (p : ℝ) < (q : ℝ) := (div_lt_one hq_pos).mp h1
    exact_mod_cast hR
  exact ⟨p, q, hp_pos, hp_lt_q, r.reduced, hcast_eq⟩

/- Every subset of SimpleGraph (Fin n) is measurable for the adjacency sigma-algebra. -/
lemma measurableSet_simpleGraph {n : ℕ} (S : Set (SimpleGraph (Fin n))) : MeasurableSet S := by
  have hsingle : ∀ G : SimpleGraph (Fin n), MeasurableSet ({G} : Set (SimpleGraph (Fin n))) := by
    intro G
    have heq : ({G} : Set (SimpleGraph (Fin n))) =
        ⋂ u : Fin n, ⋂ v : Fin n, {H : SimpleGraph (Fin n) | H.Adj u v ↔ G.Adj u v} := by
      ext H
      simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · rintro rfl u v; rfl
      · intro h
        ext u v
        exact h u v
    rw [heq]
    apply MeasurableSet.iInter
    intro u
    apply MeasurableSet.iInter
    intro v
    have hm : Measurable (fun H : SimpleGraph (Fin n) => H.Adj u v) :=
      (measurable_pi_apply v).comp ((measurable_pi_apply u).comp SimpleGraph.measurable_adj)
    have hpre : {H : SimpleGraph (Fin n) | H.Adj u v ↔ G.Adj u v} =
        (fun H : SimpleGraph (Fin n) => H.Adj u v) ⁻¹' {P : Prop | P ↔ G.Adj u v} := rfl
    rw [hpre]
    exact hm (MeasurableSet.of_discrete)
  have hfin : S.Finite := Set.toFinite S
  have hunion : S = ⋃ G ∈ S, ({G} : Set (SimpleGraph (Fin n))) := by
    ext G; simp
  rw [hunion]
  exact hfin.measurableSet_biUnion (fun G _ => hsingle G)

/- Under sparseRandomGraph, if A and B are disjoint and P(B) >= 3/4, then P(A) <= 1/4. -/
lemma prob_le_quarter_of_disjoint_three_quarters {n : ℕ} {α : ℝ} (hα : 0 < α)
    {A B : Set (SimpleGraph (Fin n))} (hdisj : Disjoint A B)
    (hB : (3 : ENNReal) / 4 ≤ ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα B) :
    ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα A ≤ (1 : ENNReal) / 4 := by
  let μ := ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα
  have hprob : MeasureTheory.IsProbabilityMeasure μ := by
    dsimp only [μ, ShelahSpencerZeroOneLaw.sparseRandomGraph]
    infer_instance
  have hsum_le : μ A + μ B ≤ 1 := by
    calc
      μ A + μ B = μ (A ∪ B) := (MeasureTheory.measure_union hdisj (measurableSet_simpleGraph B)).symm
      _ ≤ μ Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.measure_univ
  have hadd : μ A + (3 : ENNReal) / 4 ≤ (1 : ENNReal) / 4 + (3 : ENNReal) / 4 := by
    have h1eq : (1 : ENNReal) / 4 + (3 : ENNReal) / 4 = 1 := by
      rw [← ENNReal.add_div, show (1 : ENNReal) + 3 = 4 by norm_num,
        ENNReal.div_self (by norm_num) (by norm_num)]
    rw [h1eq]
    exact le_trans (add_le_add le_rfl hB) hsum_le
  have hne : ((3 : ENNReal) / 4) ≠ ⊤ := by
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  exact (ENNReal.add_le_add_iff_right hne).mp hadd

/- A sequence in ENNReal that is frequently >= 3/4 and frequently <= 1/4 cannot converge
to any limit b : ENNReal. -/
lemma not_tendsto_of_frequently_ge_le (u : ℕ → ENNReal)
    (hhi : Filter.Frequently (fun n => (3 : ENNReal) / 4 ≤ u n) Filter.atTop)
    (hlo : Filter.Frequently (fun n => u n ≤ (1 : ENNReal) / 4) Filter.atTop) :
    ∀ b : ENNReal, ¬ Filter.Tendsto u Filter.atTop (nhds b) := by
  intro b htend
  have hb_ge : (3 : ENNReal) / 4 ≤ b := ge_of_tendsto_of_frequently htend hhi
  have hb_le : b ≤ (1 : ENNReal) / 4 := le_of_tendsto_of_frequently htend hlo
  have hbad : (3 : ENNReal) / 4 ≤ (1 : ENNReal) / 4 := le_trans hb_ge hb_le
  have h4pos : (4 : ENNReal) ≠ 0 := by norm_num
  have h4top : (4 : ENNReal) ≠ ⊤ := by norm_num
  have hmul : (3 : ENNReal) / 4 * 4 ≤ (1 : ENNReal) / 4 * 4 := by gcongr
  rw [ENNReal.div_mul_cancel h4pos h4top, ENNReal.div_mul_cancel h4pos h4top] at hmul
  norm_num at hmul

/- ============================================================================
   Part 2: Finite Linear Order Enumeration and Mod-100 Counter Soundness / Completeness
   ============================================================================ -/

/- Every nonempty finite set with an irreflexive, transitive, trichotomous relation has
a minimum element. -/
lemma exists_min_of_linord {α : Type*} [DecidableEq α] (lt : α → α → Prop)
    (D : Finset α) (hne : D.Nonempty)
    (hirr : ∀ x ∈ D, ¬ lt x x)
    (htrans : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, lt x y → lt y z → lt x z)
    (htrich : ∀ x ∈ D, ∀ y ∈ D, lt x y ∨ x = y ∨ lt y x) :
    ∃ x₀ ∈ D, ∀ y ∈ D, y ≠ x₀ → lt x₀ y := by
  induction D using Finset.induction_on with
  | empty => exact absurd hne Finset.not_nonempty_empty
  | insert a s ha ih =>
    by_cases hs : s.Nonempty
    · have hirr_s : ∀ x ∈ s, ¬ lt x x := fun x hx => hirr x (Finset.mem_insert_of_mem hx)
      have htrans_s : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, lt x y → lt y z → lt x z :=
        fun x hx y hy z hz => htrans x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
          z (Finset.mem_insert_of_mem hz)
      have htrich_s : ∀ x ∈ s, ∀ y ∈ s, lt x y ∨ x = y ∨ lt y x :=
        fun x hx y hy => htrich x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
      obtain ⟨x₀, hx₀, hmin⟩ := ih hs hirr_s htrans_s htrich_s
      rcases htrich a (Finset.mem_insert_self a s) x₀ (Finset.mem_insert_of_mem hx₀) with hax | heq | hxa
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro y hy hya
        rcases Finset.mem_insert.mp hy with rfl | hys
        · exact absurd rfl hya
        · by_cases hyx : y = x₀
          · rw [hyx]; exact hax
          · exact htrans a (Finset.mem_insert_self a s) x₀ (Finset.mem_insert_of_mem hx₀) y
              (Finset.mem_insert_of_mem hys) hax (hmin y hys hyx)
      · exact absurd heq.symm (fun h => ha (h ▸ hx₀))
      · refine ⟨x₀, Finset.mem_insert_of_mem hx₀, ?_⟩
        intro y hy hyx
        rcases Finset.mem_insert.mp hy with rfl | hys
        · exact hxa
        · exact hmin y hys hyx
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      refine ⟨a, Finset.mem_singleton_self a, ?_⟩
      intro y hy hya
      exact absurd (Finset.mem_singleton.mp hy) hya

/- Strictly increasing enumeration of any finite strict linear order (D, lt) by Fin D.card. -/
lemma exists_strictMono_enum {α : Type*} [DecidableEq α] (lt : α → α → Prop) :
    ∀ (m : ℕ) (D : Finset α), D.card = m →
      (∀ x ∈ D, ¬ lt x x) →
      (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, lt x y → lt y z → lt x z) →
      (∀ x ∈ D, ∀ y ∈ D, lt x y ∨ x = y ∨ lt y x) →
      ∃ f : Fin m → α,
        (∀ i, f i ∈ D) ∧
        (∀ x ∈ D, ∃ i, f i = x) ∧
        (∀ i j : Fin m, i < j → lt (f i) (f j)) := by
  intro m
  induction m with
  | zero =>
    intro D hcard _ _ _
    have hD : D = ∅ := Finset.card_eq_zero.mp hcard
    subst hD
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun x hx => False.elim (Finset.notMem_empty x hx),
      fun i => Fin.elim0 i⟩
  | succ m ih =>
    intro D hcard hirr htrans htrich
    have hne : D.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x₀, hx₀, hmin⟩ := exists_min_of_linord lt D hne hirr htrans htrich
    let D' : Finset α := D.erase x₀
    have hcard' : D'.card = m := by
      dsimp only [D']
      rw [Finset.card_erase_of_mem hx₀, hcard]
      omega
    have hsub : D' ⊆ D := Finset.erase_subset x₀ D
    obtain ⟨f', hf'_mem, hf'_surj, hf'_mono⟩ := ih D' hcard'
      (fun x hx => hirr x (hsub hx))
      (fun x hx y hy z hz => htrans x (hsub hx) y (hsub hy) z (hsub hz))
      (fun x hx y hy => htrich x (hsub hx) y (hsub hy))
    let f : Fin (m + 1) → α := Fin.cons x₀ f'
    refine ⟨f, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp only [f, Fin.cons_zero]; exact hx₀
      · intro j; simp only [f, Fin.cons_succ]; exact hsub (hf'_mem j)
    · intro x hx
      by_cases hxx₀ : x = x₀
      · exact ⟨0, by simp [f, hxx₀]⟩
      · have hx' : x ∈ D' := Finset.mem_erase.mpr ⟨hxx₀, hx⟩
        obtain ⟨j, hj⟩ := hf'_surj x hx'
        exact ⟨j.succ, by simp [f, hj]⟩
    · intro i j hij
      refine Fin.cases (motive := fun i => ∀ j : Fin (m + 1), i < j → lt (f i) (f j)) ?_ ?_ i j hij
      · intro j hj
        refine Fin.cases (motive := fun j => (0 : Fin (m + 1)) < j → lt (f 0) (f j)) ?_ ?_ j hj
        · intro h0; exact absurd h0 (lt_irrefl _)
        · intro j' _
          simp only [f, Fin.cons_zero, Fin.cons_succ]
          have hmem : f' j' ∈ D' := hf'_mem j'
          exact hmin (f' j') (hsub hmem) (Finset.mem_erase.mp hmem).1
      · intro i' j hij'
        refine Fin.cases (motive := fun j => i'.succ < j → lt (f i'.succ) (f j)) ?_ ?_ j hij'
        · intro h0; exact absurd h0 (Nat.not_lt_zero _)
        · intro j' hlt
          simp only [f, Fin.cons_succ]
          exact hf'_mono i' j' (Fin.succ_lt_succ_iff.mp hlt)

/- Deterministic soundness of any mod-100 counter on a nonempty finite strict linear order:
starting at 0 on the minimum and incrementing mod 100 along immediate successors forces the
value at the maximum to equal (D.card - 1) % 100. -/
lemma counter_sound_mod100 {α : Type*} [DecidableEq α] (lt : α → α → Prop)
    (D : Finset α) (hne : D.Nonempty)
    (hirr : ∀ x ∈ D, ¬ lt x x)
    (htrans : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, lt x y → lt y z → lt x z)
    (htrich : ∀ x ∈ D, ∀ y ∈ D, lt x y ∨ x = y ∨ lt y x)
    (c : α → ℕ)
    (hc_min : ∀ x ∈ D, (∀ y ∈ D, ¬ lt y x) → c x = 0)
    (hc_step : ∀ x ∈ D, ∀ y ∈ D,
      (lt x y ∧ ∀ z ∈ D, ¬ (lt x z ∧ lt z y)) → c y = (c x + 1) % 100)
    (hc_max : ∀ x ∈ D, (∀ y ∈ D, ¬ lt x y) → 10 ≤ c x ∧ c x ≤ 40) :
    10 ≤ (D.card - 1) % 100 ∧ (D.card - 1) % 100 ≤ 40 := by
  obtain ⟨f, hf_mem, hf_surj, hf_mono⟩ := exists_strictMono_enum lt D.card D rfl hirr htrans htrich
  have hf_lt_iff : ∀ i j : Fin D.card, lt (f i) (f j) ↔ i < j := by
    intro i j
    constructor
    · intro hlt
      rcases lt_trichotomy i j with h | rfl | h
      · exact h
      · exact absurd hlt (hirr _ (hf_mem i))
      · exact absurd (htrans _ (hf_mem i) _ (hf_mem j) _ (hf_mem i) hlt (hf_mono j i h))
          (hirr _ (hf_mem i))
    · exact hf_mono i j
  have hpos : 0 < D.card := Finset.card_pos.mpr hne
  have hval : ∀ (r : ℕ) (hr : r < D.card), c (f ⟨r, hr⟩) = r % 100 := by
    intro r
    induction r with
    | zero =>
      intro hr
      have hmin0 : ∀ y ∈ D, ¬ lt y (f ⟨0, hr⟩) := by
        intro y hy hlt
        obtain ⟨j, rfl⟩ := hf_surj y hy
        have hj := (hf_lt_iff j ⟨0, hr⟩).mp hlt
        exact Nat.not_lt_zero j.val hj
      rw [hc_min (f ⟨0, hr⟩) (hf_mem _) hmin0]
    | succ r ih =>
      intro hr
      have hr0 : r < D.card := by omega
      have hsucc : lt (f ⟨r, hr0⟩) (f ⟨r + 1, hr⟩) ∧
          ∀ z ∈ D, ¬ (lt (f ⟨r, hr0⟩) z ∧ lt z (f ⟨r + 1, hr⟩)) := by
        refine ⟨hf_mono ⟨r, hr0⟩ ⟨r + 1, hr⟩ (by show r < r + 1; omega), ?_⟩
        intro z hz ⟨h1, h2⟩
        obtain ⟨k, rfl⟩ := hf_surj z hz
        have hk1 : r < k.val := (hf_lt_iff ⟨r, hr0⟩ k).mp h1
        have hk2 : k.val < r + 1 := (hf_lt_iff k ⟨r + 1, hr⟩).mp h2
        omega
      rw [hc_step (f ⟨r, hr0⟩) (hf_mem _) (f ⟨r + 1, hr⟩) (hf_mem _) hsucc, ih hr0]
      simp [Nat.add_mod]
  have hlast_lt : D.card - 1 < D.card := by omega
  have hmax_last : ∀ y ∈ D, ¬ lt (f ⟨D.card - 1, hlast_lt⟩) y := by
    intro y hy hlt
    obtain ⟨j, rfl⟩ := hf_surj y hy
    have hj : D.card - 1 < j.val := (hf_lt_iff ⟨D.card - 1, hlast_lt⟩ j).mp hlt
    have hj_lt : j.val < D.card := j.isLt
    omega
  have hres := hc_max (f ⟨D.card - 1, hlast_lt⟩) (hf_mem _) hmax_last
  rwa [hval (D.card - 1) hlast_lt] at hres

/- ============================================================================
   Part 3: 7-Bit Binary Arithmetic and Ripple-Carry Circuit Lemmas
   ============================================================================ -/

/- Expressing Nat.testBit in terms of division by 2^i and remainder mod 2. -/
lemma testBit_eq_mod_two (x i : ℕ) : x.testBit i = ((x / 2 ^ i) % 2 != 0) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]

/- Reconstructing a natural number < 2^k from its lowest k bits. -/
lemma sum_testBit_prefix (m : ℕ) :
    ∀ k : ℕ, (∑ b : Fin k, if m.testBit b.val then 2 ^ b.val else 0) = m % 2 ^ k := by
  intro k
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    have hmod : m % 2 ^ (k + 1) = m % 2 ^ k + (if m.testBit k then 2 ^ k else 0) := by
      rw [testBit_eq_mod_two]
      have hdiv : m % 2 ^ (k + 1) = m % 2 ^ k + 2 ^ k * ((m / 2 ^ k) % 2) := by
        have h1 : m = 2 ^ k * (m / 2 ^ k) + m % 2 ^ k := (Nat.div_add_mod m (2 ^ k)).symm
        have h2 : m / 2 ^ k = 2 * (m / 2 ^ k / 2) + (m / 2 ^ k) % 2 :=
          (Nat.div_add_mod (m / 2 ^ k) 2).symm
        have h3 : m = 2 ^ (k + 1) * (m / 2 ^ k / 2) + (m % 2 ^ k + 2 ^ k * ((m / 2 ^ k) % 2)) := by
          calc
            m = 2 ^ k * (m / 2 ^ k) + m % 2 ^ k := h1
            _ = 2 ^ k * (2 * (m / 2 ^ k / 2) + (m / 2 ^ k) % 2) + m % 2 ^ k :=
              congrArg (fun t => 2 ^ k * t + m % 2 ^ k) h2
            _ = 2 ^ (k + 1) * (m / 2 ^ k / 2) + (m % 2 ^ k + 2 ^ k * ((m / 2 ^ k) % 2)) := by
              rw [pow_succ']
              ring
        have hlt : m % 2 ^ k + 2 ^ k * ((m / 2 ^ k) % 2) < 2 ^ (k + 1) := by
          have ha : m % 2 ^ k < 2 ^ k := Nat.mod_lt m (Nat.two_pow_pos k)
          have hb : (m / 2 ^ k) % 2 ≤ 1 := by omega
          have hmul : 2 ^ k * ((m / 2 ^ k) % 2) ≤ 2 ^ k * 1 := Nat.mul_le_mul_left (2 ^ k) hb
          rw [pow_succ']
          omega
        conv_lhs => rw [h3]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      rw [hdiv]
      have hmod2 : (m / 2 ^ k) % 2 = 0 ∨ (m / 2 ^ k) % 2 = 1 := by omega
      rcases hmod2 with h0 | h1
      · simp [h0]
      · simp [h1]
    exact hmod.symm

/- Any k-bit sum is strictly less than 2^k. -/
lemma bitVal_prefix_lt : ∀ (k : ℕ) (P : ℕ → Prop) [DecidablePred P],
    (∑ b : Fin k, if P b.val then 2 ^ b.val else 0) < 2 ^ k := by
  intro k P _
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, pow_succ']
    simp only [Fin.val_castSucc, Fin.val_last]
    split_ifs <;> omega

/- Extracting bit j of a k-bit sum when j < k. -/
lemma testBit_bitVal_prefix : ∀ (k : ℕ) (P : ℕ → Prop) [DecidablePred P] (j : ℕ),
    j < k →
    (∑ b : Fin k, if P b.val then 2 ^ b.val else 0).testBit j = decide (P j) := by
  intro k P _
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    set s := ∑ b : Fin k, if P b.val then 2 ^ b.val else 0
    have hs_lt : s < 2 ^ k := bitVal_prefix_lt k P
    by_cases hjk : j < k
    · have hadd : (s + if P k then 2 ^ k else 0).testBit j = s.testBit j := by
        split_ifs with hPk
        · rw [testBit_eq_mod_two, testBit_eq_mod_two]
          have hpow : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by
            rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hjk)]
          have heven : 2 ∣ 2 ^ (k - j) := by
            have hk1 : 1 ≤ k - j := by omega
            have : 2 ^ (k - j) = 2 * 2 ^ (k - j - 1) := by
              rw [← pow_succ', Nat.sub_add_cancel hk1]
            exact ⟨2 ^ (k - j - 1), this⟩
          have hdiv : (s + 2 ^ k) / 2 ^ j = s / 2 ^ j + 2 ^ (k - j) := by
            rw [hpow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j)]
          rw [hdiv]
          rcases heven with ⟨t, ht⟩
          rw [ht, Nat.add_mul_mod_self_left]
        · simp
      rw [hadd, ih j hjk]
    · have hjeq : j = k := by omega
      subst hjeq
      rw [testBit_eq_mod_two]
      split_ifs with hPk
      · have hdiv : (s + 2 ^ j) / 2 ^ j = 1 := by
          have : (s + 2 ^ j) / 2 ^ j = s / 2 ^ j + 1 := Nat.add_div_right s (Nat.two_pow_pos j)
          rw [this, Nat.div_eq_of_lt hs_lt]
        rw [hdiv]
        simp [hPk]
      · rw [add_zero, Nat.div_eq_of_lt hs_lt]
        simp [hPk]

/- Equality of a 7-bit sum with a constant c < 128 is equivalent to bitwise agreement. -/
lemma bitVal7_eq_const_iff (P : Fin 7 → Prop) [DecidablePred P] {c : ℕ} (hc : c < 128) :
    (∑ b : Fin 7, if P b then 2 ^ b.val else 0) = c ↔
      ∀ b : Fin 7, P b ↔ c.testBit b.val = true := by
  let P' : ℕ → Prop := fun j => if h : j < 7 then P ⟨j, h⟩ else False
  have hsum_eq : (∑ b : Fin 7, if P b then 2 ^ b.val else 0) =
      ∑ b : Fin 7, if P' b.val then 2 ^ b.val else 0 := by
    apply Finset.sum_congr rfl
    intro b _
    have hb : b.val < 7 := b.isLt
    simp only [P', hb, dite_true]
  constructor
  · intro heq b
    have htb := testBit_bitVal_prefix 7 P' b.val b.isLt
    rw [← hsum_eq, heq] at htb
    have hP' : P' b.val ↔ P b := by simp [P', b.isLt]
    rw [← hP']
    cases h : c.testBit b.val
    · simp only [Bool.false_eq_true, iff_false]
      intro hPb
      simp [hPb] at htb
      rw [h] at htb
      exact Bool.noConfusion htb
    · simp only [iff_true]
      by_contra hPb
      simp [hPb] at htb
      rw [h] at htb
      exact Bool.noConfusion htb
  · intro hall
    have h1 : (∑ b : Fin 7, if P b then 2 ^ b.val else 0) =
        ∑ b : Fin 7, if c.testBit b.val then 2 ^ b.val else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hPb : P b
      · have hcb : c.testBit b.val = true := (hall b).mp hPb
        simp [hPb, hcb]
      · have hcb : c.testBit b.val = false := by
          cases h : c.testBit b.val
          · rfl
          · exact absurd ((hall b).mpr h) hPb
        simp [hPb, hcb]
    rw [h1, sum_testBit_prefix c 7, Nat.mod_eq_of_lt (by omega : c < 2 ^ 7)]

/- Recursive bit-comparison equivalence for u < c on k bits. -/
lemma bitVal_prefix_lt_step {k : ℕ} (P : ℕ → Prop) [DecidablePred P] (c : ℕ) :
    (∑ b : Fin (k + 1), if P b.val then 2 ^ b.val else 0) < c % 2 ^ (k + 1) ↔
      if c.testBit k then
        ¬ P k ∨ (∑ b : Fin k, if P b.val then 2 ^ b.val else 0) < c % 2 ^ k
      else
        ¬ P k ∧ (∑ b : Fin k, if P b.val then 2 ^ b.val else 0) < c % 2 ^ k := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  set s := ∑ b : Fin k, if P b.val then 2 ^ b.val else 0
  have hs_lt : s < 2 ^ k := bitVal_prefix_lt k P
  have hc_lt : c % 2 ^ k < 2 ^ k := Nat.mod_lt c (Nat.two_pow_pos k)
  have hc_split : c % 2 ^ (k + 1) = c % 2 ^ k + (if c.testBit k then 2 ^ k else 0) := by
    have h1 := sum_testBit_prefix c (k + 1)
    rw [Fin.sum_univ_castSucc] at h1
    simp only [Fin.val_castSucc, Fin.val_last] at h1
    rw [sum_testBit_prefix c k] at h1
    exact h1.symm
  rw [hc_split]
  by_cases hck : c.testBit k = true
  · simp only [hck, ↓reduceIte]
    by_cases hPk : P k
    · simp only [hPk, ↓reduceIte, not_true_eq_false, false_or]
      constructor <;> intro h <;> omega
    · simp only [hPk, ↓reduceIte, add_zero, not_false_eq_true, true_or, iff_true]
      omega
  · have hckf : c.testBit k = false := Bool.eq_false_iff.mpr hck
    simp only [hckf, Bool.false_eq_true, ↓reduceIte, add_zero]
    by_cases hPk : P k
    · simp only [hPk, ↓reduceIte, not_true_eq_false, false_and, iff_false]
      omega
    · simp only [hPk, ↓reduceIte, add_zero, not_false_eq_true, true_and]

/- Ripple-carry increment-by-1 equivalence on k bits when the input value is < 2^k - 1. -/
lemma bitVal_prefix_succ_iff : ∀ (k : ℕ) (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q],
    (∑ b : Fin k, if P b.val then 2 ^ b.val else 0) + 1 < 2 ^ k →
    ((∑ b : Fin k, if Q b.val then 2 ^ b.val else 0) =
      (∑ b : Fin k, if P b.val then 2 ^ b.val else 0) + 1 ↔
      ∀ b : Fin k, Q b.val ↔
        ((P b.val ∧ ¬ ∀ j : Fin k, j < b → P j.val) ∨
         (¬ P b.val ∧ ∀ j : Fin k, j < b → P j.val))) := by
  intro k P Q _ _
  have hall_carry : ∀ (m : ℕ),
      (∑ b : Fin m, if P b.val then 2 ^ b.val else 0) + 1 = 2 ^ m ↔
      ∀ j : Fin m, P j.val := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Fin.sum_univ_castSucc, pow_succ']
      simp only [Fin.val_castSucc, Fin.val_last]
      set s := ∑ b : Fin m, if P b.val then 2 ^ b.val else 0
      have hs_lt : s < 2 ^ m := bitVal_prefix_lt m P
      constructor
      · intro heq j
        have hPm : P m := by
          by_contra hnot
          simp only [hnot, ↓reduceIte, add_zero] at heq
          omega
        simp only [hPm, ↓reduceIte] at heq
        have hs_eq : s + 1 = 2 ^ m := by omega
        have hall_m := (ih.mp hs_eq)
        refine Fin.lastCases hPm (fun i => hall_m i) j
      · intro hall
        have hPm : P m := hall (Fin.last m)
        have hs_eq : s + 1 = 2 ^ m := ih.mpr (fun i => hall i.castSucc)
        simp only [hPm, ↓reduceIte]
        omega
  have hcarry_step : ∀ (m : ℕ),
      ((∑ b : Fin m, if Q b.val then 2 ^ b.val else 0) =
        ((∑ b : Fin m, if P b.val then 2 ^ b.val else 0) + 1) % 2 ^ m) ↔
      (∀ b : Fin m, Q b.val ↔
        ((P b.val ∧ ¬ ∀ j : Fin m, j < b → P j.val) ∨
         (¬ P b.val ∧ ∀ j : Fin m, j < b → P j.val))) := by
    intro m
    induction m with
    | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty, pow_zero, Nat.mod_one, true_iff]
      intro b; exact Fin.elim0 b
    | succ m ih =>
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      set sp := ∑ b : Fin m, if P b.val then 2 ^ b.val else 0
      set sq := ∑ b : Fin m, if Q b.val then 2 ^ b.val else 0
      have hsp_lt : sp < 2 ^ m := bitVal_prefix_lt m P
      have hsq_lt : sq < 2 ^ m := bitVal_prefix_lt m Q
      have hcarry_m : (sp + 1 = 2 ^ m) ↔ (∀ j : Fin m, P j.val) := hall_carry m
      have hsplit_eq :
          (sq + if Q m then 2 ^ m else 0) = ((sp + if P m then 2 ^ m else 0) + 1) % 2 ^ (m + 1) ↔
          (sq = (sp + 1) % 2 ^ m ∧
            (Q m ↔ (P m ∧ ¬ (sp + 1 = 2 ^ m)) ∨ (¬ P m ∧ (sp + 1 = 2 ^ m)))) := by
        rw [pow_succ']
        have h2m : 0 < 2 ^ m := Nat.two_pow_pos m
        by_cases hC : sp + 1 = 2 ^ m
        · have hmod_low : (sp + 1) % 2 ^ m = 0 := by rw [hC, Nat.mod_self]
          by_cases hPm : P m
          · have hrhs : (sp + 2 ^ m + 1) % (2 * 2 ^ m) = 0 := by
              have : sp + 2 ^ m + 1 = 2 * 2 ^ m := by omega
              rw [this, Nat.mod_self]
            by_cases hQm : Q m
            · simp only [hPm, hQm, ↓reduceIte, hrhs, hmod_low]
              exact ⟨fun h => by omega,
                fun ⟨_, h⟩ => (h.mp trivial).elim (fun a => absurd hC a.2) (fun a => False.elim (a.1 trivial))⟩
            · simp only [hPm, hQm, ↓reduceIte, add_zero, hrhs, hmod_low]
              exact ⟨fun h => ⟨h, ⟨False.elim,
                fun h1 => h1.elim (fun a => a.2 hC) (fun a => a.1 trivial)⟩⟩, fun h => h.1⟩
          · have hrhs : (sp + 1) % (2 * 2 ^ m) = 2 ^ m := by
              rw [hC, Nat.mod_eq_of_lt (by omega)]
            by_cases hQm : Q m
            · simp only [hPm, hQm, ↓reduceIte, add_zero, hrhs, hmod_low]
              exact ⟨fun h => ⟨by omega, ⟨fun _ => Or.inr ⟨not_false, hC⟩, fun _ => trivial⟩⟩,
                fun ⟨hsq0, _⟩ => by omega⟩
            · simp only [hPm, hQm, ↓reduceIte, add_zero, hrhs, hmod_low]
              exact ⟨fun h => by omega, fun ⟨_, h⟩ => False.elim (h.mpr (Or.inr ⟨not_false, hC⟩))⟩
        · have hmod_low : (sp + 1) % 2 ^ m = sp + 1 := Nat.mod_eq_of_lt (by omega)
          by_cases hPm : P m
          · have hrhs : (sp + 2 ^ m + 1) % (2 * 2 ^ m) = sp + 1 + 2 ^ m := by
              rw [Nat.mod_eq_of_lt (by omega)]; omega
            by_cases hQm : Q m
            · simp only [hPm, hQm, ↓reduceIte, hrhs, hmod_low]
              exact ⟨fun h => ⟨by omega, ⟨fun _ => Or.inl ⟨trivial, hC⟩, fun _ => trivial⟩⟩,
                fun ⟨hsq, _⟩ => by omega⟩
            · simp only [hPm, hQm, ↓reduceIte, add_zero, hrhs, hmod_low]
              exact ⟨fun h => by omega, fun ⟨_, h⟩ => False.elim (h.mpr (Or.inl ⟨trivial, hC⟩))⟩
          · have hrhs : (sp + 1) % (2 * 2 ^ m) = sp + 1 := Nat.mod_eq_of_lt (by omega)
            by_cases hQm : Q m
            · simp only [hPm, hQm, ↓reduceIte, add_zero, hrhs, hmod_low]
              exact ⟨fun h => by omega,
                fun ⟨_, h⟩ => (h.mp trivial).elim (fun a => False.elim a.1) (fun a => False.elim (hC a.2))⟩
            · simp only [hPm, hQm, ↓reduceIte, add_zero, hrhs, hmod_low]
              exact ⟨fun h => ⟨h, ⟨False.elim,
                fun h1 => h1.elim (fun a => a.1) (fun a => hC a.2)⟩⟩, fun h => h.1⟩
      rw [hsplit_eq, ih, hcarry_m]
      constructor
      · rintro ⟨hlow, htop⟩ b
        refine Fin.lastCases ?_ ?_ b
        · simp only [Fin.val_last]
          have hlt_last : (∀ j : Fin (m + 1), j < Fin.last m → P j.val) ↔ (∀ j : Fin m, P j.val) := by
            constructor
            · intro h j; exact h j.castSucc (Fin.castSucc_lt_last j)
            · intro h j hj
              exact h ⟨j.val, hj⟩
          rw [hlt_last]
          exact htop
        · intro i
          simp only [Fin.val_castSucc]
          have hlt_i : (∀ j : Fin (m + 1), j < i.castSucc → P j.val) ↔
              (∀ j : Fin m, j < i → P j.val) := by
            constructor
            · intro h j hj; exact h j.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hj)
            · intro h j hj
              have hjm : j.val < m := lt_trans hj i.isLt
              exact h ⟨j.val, hjm⟩ hj
          rw [hlt_i]
          exact hlow i
      · intro hall
        refine ⟨?_, ?_⟩
        · intro i
          have hi := hall i.castSucc
          simp only [Fin.val_castSucc] at hi
          have hlt_i : (∀ j : Fin (m + 1), j < i.castSucc → P j.val) ↔
              (∀ j : Fin m, j < i → P j.val) := by
            constructor
            · intro h j hj; exact h j.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hj)
            · intro h j hj
              have hjm : j.val < m := lt_trans hj i.isLt
              exact h ⟨j.val, hjm⟩ hj
          rwa [hlt_i] at hi
        · have hlast := hall (Fin.last m)
          simp only [Fin.val_last] at hlast
          have hlt_last : (∀ j : Fin (m + 1), j < Fin.last m → P j.val) ↔ (∀ j : Fin m, P j.val) := by
            constructor
            · intro h j; exact h j.castSucc (Fin.castSucc_lt_last j)
            · intro h j hj
              exact h ⟨j.val, hj⟩
          rwa [hlt_last] at hlast
  intro hlt
  have hmod : ((∑ b : Fin k, if P b.val then 2 ^ b.val else 0) + 1) % 2 ^ k =
      (∑ b : Fin k, if P b.val then 2 ^ b.val else 0) + 1 := Nat.mod_eq_of_lt hlt
  rw [← hmod]
  exact hcarry_step k

/- ============================================================================
   Part 4: First-Order Graph BoundedFormula Compiler for 7-Bit Counter & Sentence
   ============================================================================ -/

/- Indexing lemmas for Fin.snoc on natural-number indices. -/
lemma snoc_apply_lt {α : Type*} {m : ℕ} (xs : Fin m → α) (x : α) {i : ℕ} (hi : i < m)
    (hi' : i < m + 1 := Nat.lt_succ_of_lt hi) :
    Fin.snoc (α := fun _ => α) xs x (⟨i, hi'⟩ : Fin (m + 1)) = xs ⟨i, hi⟩ := by
  have h : (⟨i, hi'⟩ : Fin (m + 1)) = (⟨i, hi⟩ : Fin m).castSucc := rfl
  rw [h, Fin.snoc_castSucc]

lemma snoc_apply_eq {α : Type*} {m : ℕ} (xs : Fin m → α) (x : α)
    (hm : m < m + 1 := Nat.lt_succ_self m) :
    Fin.snoc (α := fun _ => α) xs x (⟨m, hm⟩ : Fin (m + 1)) = x := by
  have h : (⟨m, hm⟩ : Fin (m + 1)) = Fin.last m := rfl
  rw [h, Fin.snoc_last]

lemma snoc2_0 {α : Type*} {m : ℕ} (xs : Fin m → α) (x y : α)
    (hm : m < m + 2 := by omega) :
    (Fin.snoc (Fin.snoc xs x) y : Fin (m + 2) → α) ⟨m, hm⟩ = x := by
  rw [snoc_apply_lt _ y (Nat.lt_succ_self m), snoc_apply_eq xs x]

lemma snoc3_0 {α : Type*} {m : ℕ} (xs : Fin m → α) (x y z : α)
    (hm : m < m + 3 := by omega) :
    (Fin.snoc (Fin.snoc (Fin.snoc xs x) y) z : Fin (m + 3) → α) ⟨m, hm⟩ = x := by
  rw [snoc_apply_lt _ z (by omega), snoc_apply_lt _ y (Nat.lt_succ_self m), snoc_apply_eq xs x]

lemma snoc3_1 {α : Type*} {m : ℕ} (xs : Fin m → α) (x y z : α)
    (hm : m + 1 < m + 3 := by omega) :
    (Fin.snoc (Fin.snoc (Fin.snoc xs x) y) z : Fin (m + 3) → α) ⟨m + 1, hm⟩ = y := by
  rw [snoc_apply_lt _ z (Nat.lt_succ_self (m + 1)), snoc_apply_eq _ y]

/- Embedding a Formula (Fin m) into BoundedFormula Empty l via an index map idx : Fin m -> Fin l. -/
lemma realize_embedFormula {m l : ℕ} (ψ : FirstOrder.Language.graph.Formula (Fin m))
    (idx : Fin m → Fin l) {n : ℕ} (G : SimpleGraph (Fin n)) (xs : Fin l → Fin n) :
    @FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
      Empty l (FirstOrder.Language.BoundedFormula.relabel (fun i => (Sum.inr (idx i) : Empty ⊕ Fin l)) ψ)
      Empty.elim xs ↔
    @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure
      (Fin m) ψ (fun i => xs (idx i)) := by
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  rw [FirstOrder.Language.BoundedFormula.realize_relabel, FirstOrder.Language.Formula.Realize]
  have hsub : xs ∘ Fin.natAdd l = (default : Fin 0 → Fin n) := Subsingleton.elim _ _
  have hfn : (Sum.elim Empty.elim (xs ∘ Fin.castAdd 0) ∘ fun i : Fin m => (Sum.inr (idx i) : Empty ⊕ Fin l)) =
      (fun i => xs (idx i)) := by
    funext i
    rfl
  rw [hsub, hfn]

/- Compiling constant equality (bitVal P = c) into a BoundedFormula Empty l. -/
lemma exists_eqConst_bf {l : ℕ} (c : ℕ) (hc : c < 128)
    (P : Fin 7 → FirstOrder.Language.graph.BoundedFormula Empty l) :
    ∃ ψ : FirstOrder.Language.graph.BoundedFormula Empty l,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (xs : Fin l → Fin n),
        @FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
          Empty l ψ Empty.elim xs ↔
        (∑ b : Fin 7,
          @ite ℕ (@FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
              Empty l (P b) Empty.elim xs) (Classical.propDecidable _) (2 ^ b.val) 0) = c := by
  let lit : Fin 7 → FirstOrder.Language.graph.BoundedFormula Empty l :=
    fun b => if c.testBit b.val then P b else (P b).not
  let ψ : FirstOrder.Language.graph.BoundedFormula Empty l :=
    (List.finRange 7).map lit |>.foldr (· ⊓ ·) ⊤
  refine ⟨ψ, ?_⟩
  intro n G xs
  classical
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  rw [bitVal7_eq_const_iff (fun b => (P b).Realize Empty.elim xs) hc]
  dsimp only [ψ]
  rw [FirstOrder.Language.BoundedFormula.realize_foldr_inf]
  constructor
  · intro hall b
    have hmem : lit b ∈ (List.finRange 7).map lit :=
      List.mem_map.mpr ⟨b, List.mem_finRange b, rfl⟩
    have hreal := hall (lit b) hmem
    dsimp only [lit] at hreal
    cases hcb : c.testBit b.val
    · simp only [hcb, Bool.false_eq_true, ↓reduceIte,
        FirstOrder.Language.BoundedFormula.realize_not] at hreal
      simp [hreal]
    · simp only [hcb, ↓reduceIte] at hreal
      simp [hreal]
  · intro hbits φ hφ
    rcases List.mem_map.mp hφ with ⟨b, _, rfl⟩
    dsimp only [lit]
    have hb := hbits b
    cases hcb : c.testBit b.val
    · simp only [Bool.false_eq_true, ↓reduceIte,
        FirstOrder.Language.BoundedFormula.realize_not]
      intro hPb
      have := hb.mp hPb
      rw [hcb] at this
      exact Bool.noConfusion this
    · simp only [↓reduceIte]
      exact hb.mpr hcb

/- Compiling constant strict inequality (bitVal P < c) into a BoundedFormula Empty l. -/
lemma exists_ltConst_bf {l : ℕ} (c : ℕ) (hc : c < 128)
    (P : Fin 7 → FirstOrder.Language.graph.BoundedFormula Empty l) :
    ∃ ψ : FirstOrder.Language.graph.BoundedFormula Empty l,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (xs : Fin l → Fin n),
        @FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
          Empty l ψ Empty.elim xs ↔
        (∑ b : Fin 7,
          @ite ℕ (@FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
              Empty l (P b) Empty.elim xs) (Classical.propDecidable _) (2 ^ b.val) 0) < c := by
  have hrec : ∀ (k : ℕ) (hk : k ≤ 7),
      ∃ ψ : FirstOrder.Language.graph.BoundedFormula Empty l,
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (xs : Fin l → Fin n),
          @FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
            Empty l ψ Empty.elim xs ↔
          (∑ b : Fin k,
            @ite ℕ (@FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
                Empty l (P ⟨b.val, by omega⟩) Empty.elim xs) (Classical.propDecidable _) (2 ^ b.val) 0) < c % 2 ^ k := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨⊥, ?_⟩
      intro n G xs
      let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
      simp [Nat.mod_one]
    | succ k ih =>
      intro hk
      obtain ⟨ψ₀, hψ₀⟩ := ih (by omega)
      let pk := P ⟨k, by omega⟩
      let ψ : FirstOrder.Language.graph.BoundedFormula Empty l :=
        if c.testBit k then pk.not ⊔ ψ₀ else pk.not ⊓ ψ₀
      refine ⟨ψ, ?_⟩
      intro n G xs
      classical
      let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
      let P' : ℕ → Prop := fun j => if hj : j < 7 then (P ⟨j, hj⟩).Realize Empty.elim xs else False
      have hstep := bitVal_prefix_lt_step (k := k) P' c
      have hsum_k1 :
          (∑ b : Fin (k + 1), if (P ⟨b.val, by omega⟩).Realize Empty.elim xs then 2 ^ b.val else 0) =
          (∑ b : Fin (k + 1), if P' b.val then 2 ^ b.val else 0) := by
        apply Finset.sum_congr rfl
        intro b _
        have hb : b.val < 7 := by omega
        simp only [P', hb, dite_true]
      have hsum_k :
          (∑ b : Fin k, if (P ⟨b.val, by omega⟩).Realize Empty.elim xs then 2 ^ b.val else 0) =
          (∑ b : Fin k, if P' b.val then 2 ^ b.val else 0) := by
        apply Finset.sum_congr rfl
        intro b _
        have hb : b.val < 7 := by omega
        simp only [P', hb, dite_true]
      have hPk : P' k ↔ pk.Realize Empty.elim xs := by
        have hk7 : k < 7 := by omega
        simp only [P', hk7, dite_true, pk]
      rw [hsum_k1, hstep, ← hsum_k, hPk]
      dsimp only [ψ]
      cases hck : c.testBit k
      · simp only [Bool.false_eq_true, ↓reduceIte,
          FirstOrder.Language.BoundedFormula.realize_inf,
          FirstOrder.Language.BoundedFormula.realize_not, hψ₀ n G xs]
      · simp only [↓reduceIte,
          FirstOrder.Language.BoundedFormula.realize_sup,
          FirstOrder.Language.BoundedFormula.realize_not, hψ₀ n G xs]
  obtain ⟨ψ, hψ⟩ := hrec 7 le_rfl
  refine ⟨ψ, ?_⟩
  intro n G xs
  classical
  have hmod : c % 2 ^ 7 = c := Nat.mod_eq_of_lt (by omega)
  rw [hψ n G xs, hmod]

/- Compiling 7-bit ripple-carry increment (bitVal Q = bitVal P + 1, assuming bitVal P < 127)
into a BoundedFormula Empty l. -/
lemma exists_eqSucc_bf {l : ℕ}
    (P Q : Fin 7 → FirstOrder.Language.graph.BoundedFormula Empty l) :
    ∃ ψ : FirstOrder.Language.graph.BoundedFormula Empty l,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (xs : Fin l → Fin n),
        (∑ b : Fin 7,
          @ite ℕ (@FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
              Empty l (P b) Empty.elim xs) (Classical.propDecidable _) (2 ^ b.val) 0) < 127 →
        (@FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
            Empty l ψ Empty.elim xs ↔
         (∑ b : Fin 7,
            @ite ℕ (@FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
                Empty l (Q b) Empty.elim xs) (Classical.propDecidable _) (2 ^ b.val) 0) =
         (∑ b : Fin 7,
            @ite ℕ (@FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
                Empty l (P b) Empty.elim xs) (Classical.propDecidable _) (2 ^ b.val) 0) + 1) := by
  let carry : Fin 7 → FirstOrder.Language.graph.BoundedFormula Empty l :=
    fun b => ((List.finRange 7).filter (fun j => decide (j < b))).map P |>.foldr (· ⊓ ·) ⊤
  let bitEq : Fin 7 → FirstOrder.Language.graph.BoundedFormula Empty l :=
    fun b => (Q b).iff ((P b ⊓ (carry b).not) ⊔ ((P b).not ⊓ carry b))
  let ψ : FirstOrder.Language.graph.BoundedFormula Empty l :=
    (List.finRange 7).map bitEq |>.foldr (· ⊓ ·) ⊤
  refine ⟨ψ, ?_⟩
  intro n G xs hlt127
  classical
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  let P' : ℕ → Prop := fun j => if hj : j < 7 then (P ⟨j, hj⟩).Realize Empty.elim xs else False
  let Q' : ℕ → Prop := fun j => if hj : j < 7 then (Q ⟨j, hj⟩).Realize Empty.elim xs else False
  have hsumP : (∑ b : Fin 7, if (P b).Realize Empty.elim xs then 2 ^ b.val else 0) =
      ∑ b : Fin 7, if P' b.val then 2 ^ b.val else 0 := by
    apply Finset.sum_congr rfl; intro b _; simp only [P', b.isLt, dite_true]
  have hsumQ : (∑ b : Fin 7, if (Q b).Realize Empty.elim xs then 2 ^ b.val else 0) =
      ∑ b : Fin 7, if Q' b.val then 2 ^ b.val else 0 := by
    apply Finset.sum_congr rfl; intro b _; simp only [Q', b.isLt, dite_true]
  have hsucc := bitVal_prefix_succ_iff 7 P' Q' (by rw [← hsumP]; omega)
  rw [hsumQ, hsumP, hsucc]
  have hcarry_real : ∀ b : Fin 7,
      (carry b).Realize Empty.elim xs ↔ ∀ j : Fin 7, j < b → P' j.val := by
    intro b
    dsimp only [carry]
    rw [FirstOrder.Language.BoundedFormula.realize_foldr_inf]
    constructor
    · intro h j hj
      have hmem : P j ∈ ((List.finRange 7).filter (fun j => decide (j < b))).map P := by
        refine List.mem_map.mpr ⟨j, ?_, rfl⟩
        exact List.mem_filter.mpr ⟨List.mem_finRange j, decide_eq_true hj⟩
      have hjr := h (P j) hmem
      simp only [P', j.isLt, dite_true]
      exact hjr
    · intro h φ hφ
      rcases List.mem_map.mp hφ with ⟨j, hjf, rfl⟩
      have hjlt : j < b := of_decide_eq_true (List.mem_filter.mp hjf).2
      have hPj := h j hjlt
      simp only [P', j.isLt, dite_true] at hPj
      exact hPj
  dsimp only [ψ]
  rw [FirstOrder.Language.BoundedFormula.realize_foldr_inf]
  constructor
  · intro hall b
    have hmem : bitEq b ∈ (List.finRange 7).map bitEq :=
      List.mem_map.mpr ⟨b, List.mem_finRange b, rfl⟩
    have hb := hall (bitEq b) hmem
    simp only [bitEq, FirstOrder.Language.BoundedFormula.realize_iff,
      FirstOrder.Language.BoundedFormula.realize_sup,
      FirstOrder.Language.BoundedFormula.realize_inf,
      FirstOrder.Language.BoundedFormula.realize_not, hcarry_real b] at hb
    simp only [P', Q', b.isLt, dite_true]
    exact hb
  · intro hall φ hφ
    rcases List.mem_map.mp hφ with ⟨b, _, rfl⟩
    have hb := hall b
    simp only [P', Q', b.isLt, dite_true] at hb
    simp only [bitEq, FirstOrder.Language.BoundedFormula.realize_iff,
      FirstOrder.Language.BoundedFormula.realize_sup,
      FirstOrder.Language.BoundedFormula.realize_inf,
      FirstOrder.Language.BoundedFormula.realize_not, hcarry_real b]
    exact hb

/- Compiling increment-mod-100 (bitVal Q = (bitVal P + 1) % 100, assuming bitVal P < 100)
into a BoundedFormula Empty l. -/
lemma exists_incMod100_bf {l : ℕ}
    (P Q : Fin 7 → FirstOrder.Language.graph.BoundedFormula Empty l) :
    ∃ ψ : FirstOrder.Language.graph.BoundedFormula Empty l,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (xs : Fin l → Fin n),
        (∑ b : Fin 7,
          @ite ℕ (@FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
              Empty l (P b) Empty.elim xs) (Classical.propDecidable _) (2 ^ b.val) 0) < 100 →
        (@FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
            Empty l ψ Empty.elim xs ↔
         (∑ b : Fin 7,
            @ite ℕ (@FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
                Empty l (Q b) Empty.elim xs) (Classical.propDecidable _) (2 ^ b.val) 0) =
         ((∑ b : Fin 7,
            @ite ℕ (@FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
                Empty l (P b) Empty.elim xs) (Classical.propDecidable _) (2 ^ b.val) 0) + 1) % 100) := by
  obtain ⟨eq99, heq99⟩ := exists_eqConst_bf 99 (by omega) P
  obtain ⟨eq0, heq0⟩ := exists_eqConst_bf 0 (by omega) Q
  obtain ⟨lt99, hlt99⟩ := exists_ltConst_bf 99 (by omega) P
  obtain ⟨succPQ, hsuccPQ⟩ := exists_eqSucc_bf P Q
  refine ⟨(eq99 ⊓ eq0) ⊔ (lt99 ⊓ succPQ), ?_⟩
  intro n G xs hlt100
  classical
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  simp only [FirstOrder.Language.BoundedFormula.realize_sup,
    FirstOrder.Language.BoundedFormula.realize_inf, heq99 n G xs, heq0 n G xs, hlt99 n G xs,
    hsuccPQ n G xs (by omega)]
  set u := ∑ b : Fin 7, if (P b).Realize Empty.elim xs then 2 ^ b.val else 0
  set w := ∑ b : Fin 7, if (Q b).Realize Empty.elim xs then 2 ^ b.val else 0
  constructor
  · rintro (⟨hu, hw⟩ | ⟨hu, hw⟩)
    · rw [hu, hw]
    · rw [hw, Nat.mod_eq_of_lt (by omega)]
  · intro hw
    by_cases hu99 : u = 99
    · left
      refine ⟨hu99, ?_⟩
      rw [hw, hu99]
    · right
      have hu_lt : u < 99 := by omega
      refine ⟨hu_lt, ?_⟩
      rw [hw, Nat.mod_eq_of_lt (by omega)]

/- Compiling the full 7-bit counter sentence over definable (valid, dom, lt, mem) formulas
with exact semantic characterization in every finite simple graph G on Fin n. -/
lemma exists_counter_sentence (k : ℕ)
    (valid_φ : FirstOrder.Language.graph.Formula (Fin k))
    (dom_φ : FirstOrder.Language.graph.Formula (Fin (k + 1)))
    (lt_φ : FirstOrder.Language.graph.Formula (Fin (k + 2)))
    (mem_φ : FirstOrder.Language.graph.Formula (Fin (k + 2))) :
    ∃ φ : FirstOrder.Language.graph.Sentence,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        @FirstOrder.Language.Sentence.Realize FirstOrder.Language.graph (Fin n) G.structure φ ↔
        ∃ (a : Fin k → Fin n) (D : Finset (Fin n)),
          @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin k) valid_φ a ∧
          (∀ x : Fin n, x ∈ D ↔
            @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin (k + 1)) dom_φ (Fin.snoc a x)) ∧
          D.Nonempty ∧
          (∀ x ∈ D, ¬ @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin (k + 2)) lt_φ (Fin.snoc (Fin.snoc a x) x)) ∧
          (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
            @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin (k + 2)) lt_φ (Fin.snoc (Fin.snoc a x) y) →
            @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin (k + 2)) lt_φ (Fin.snoc (Fin.snoc a y) z) →
            @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin (k + 2)) lt_φ (Fin.snoc (Fin.snoc a x) z)) ∧
          (∀ x ∈ D, ∀ y ∈ D,
            @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin (k + 2)) lt_φ (Fin.snoc (Fin.snoc a x) y) ∨
            x = y ∨
            @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin (k + 2)) lt_φ (Fin.snoc (Fin.snoc a y) x)) ∧
          ∃ v : Fin 7 → Fin n,
            let c : Fin n → ℕ := fun x => ∑ b : Fin 7,
              @ite ℕ (@FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin (k + 2)) mem_φ (Fin.snoc (Fin.snoc a (v b)) x))
                (Classical.propDecidable _) (2 ^ b.val) 0
            (∀ x ∈ D, c x < 100) ∧
            (∀ x ∈ D, (∀ y ∈ D, ¬ @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin (k + 2)) lt_φ (Fin.snoc (Fin.snoc a y) x)) → c x = 0) ∧
            (∀ x ∈ D, ∀ y ∈ D,
              (@FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin (k + 2)) lt_φ (Fin.snoc (Fin.snoc a x) y) ∧
               ∀ z ∈ D, ¬ (@FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin (k + 2)) lt_φ (Fin.snoc (Fin.snoc a x) z) ∧
                 @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin (k + 2)) lt_φ (Fin.snoc (Fin.snoc a z) y))) →
              c y = (c x + 1) % 100) ∧
            (∀ x ∈ D, (∀ y ∈ D, ¬ @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin (k + 2)) lt_φ (Fin.snoc (Fin.snoc a x) y)) →
              10 ≤ c x ∧ c x ≤ 40) := by
  let idxK : ∀ {l : ℕ}, k ≤ l → Fin k → Fin l := fun h i => ⟨i.val, by omega⟩
  let idx1 : ∀ {l : ℕ}, k ≤ l → Fin l → Fin (k + 1) → Fin l :=
    fun h ix => Fin.snoc (idxK h) ix
  let idx2 : ∀ {l : ℕ}, k ≤ l → Fin l → Fin l → Fin (k + 2) → Fin l :=
    fun h ix iy => Fin.snoc (Fin.snoc (idxK h) ix) iy
  let domAt : ∀ {l : ℕ}, k ≤ l → Fin l → FirstOrder.Language.graph.BoundedFormula Empty l :=
    fun {l} h ix => FirstOrder.Language.BoundedFormula.relabel (fun i => (Sum.inr (idx1 h ix i) : Empty ⊕ Fin l)) dom_φ
  let ltAt : ∀ {l : ℕ}, k ≤ l → Fin l → Fin l → FirstOrder.Language.graph.BoundedFormula Empty l :=
    fun {l} h ix iy => FirstOrder.Language.BoundedFormula.relabel (fun i => (Sum.inr (idx2 h ix iy i) : Empty ⊕ Fin l)) lt_φ
  let memAt : ∀ {l : ℕ}, k ≤ l → Fin l → Fin l → FirstOrder.Language.graph.BoundedFormula Empty l :=
    fun {l} h iv ix => FirstOrder.Language.BoundedFormula.relabel (fun i => (Sum.inr (idx2 h iv ix i) : Empty ⊕ Fin l)) mem_φ
  have hdomAt : ∀ {l n : ℕ} {h : k ≤ l} (ix : Fin l) (G : SimpleGraph (Fin n)) (xs : Fin l → Fin n),
      @FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
        Empty l (domAt h ix) Empty.elim xs ↔
      @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure
        (Fin (k + 1)) dom_φ (Fin.snoc (fun i : Fin k => xs (idxK h i)) (xs ix)) := by
    intro l n h ix G xs
    dsimp only [domAt]
    rw [realize_embedFormula]
    have hfn : (fun i : Fin (k + 1) => xs (idx1 h ix i)) =
        Fin.snoc (fun i : Fin k => xs (idxK h i)) (xs ix) := by
      funext i
      refine Fin.lastCases ?_ ?_ i
      · simp [idx1]
      · intro j; simp [idx1]
    rw [hfn]
  have hltAt : ∀ {l n : ℕ} {h : k ≤ l} (ix iy : Fin l) (G : SimpleGraph (Fin n)) (xs : Fin l → Fin n),
      @FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
        Empty l (ltAt h ix iy) Empty.elim xs ↔
      @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure
        (Fin (k + 2)) lt_φ (Fin.snoc (Fin.snoc (fun i : Fin k => xs (idxK h i)) (xs ix)) (xs iy)) := by
    intro l n h ix iy G xs
    dsimp only [ltAt]
    rw [realize_embedFormula]
    have hfn : (fun i : Fin (k + 2) => xs (idx2 h ix iy i)) =
        Fin.snoc (Fin.snoc (fun i : Fin k => xs (idxK h i)) (xs ix)) (xs iy) := by
      funext i
      refine Fin.lastCases ?_ ?_ i
      · simp [idx2]
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · simp [idx2]
        · intro r; simp [idx2]
    rw [hfn]
  have hmemAt : ∀ {l n : ℕ} {h : k ≤ l} (iv ix : Fin l) (G : SimpleGraph (Fin n)) (xs : Fin l → Fin n),
      @FirstOrder.Language.BoundedFormula.Realize FirstOrder.Language.graph (Fin n) G.structure
        Empty l (memAt h iv ix) Empty.elim xs ↔
      @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure
        (Fin (k + 2)) mem_φ (Fin.snoc (Fin.snoc (fun i : Fin k => xs (idxK h i)) (xs iv)) (xs ix)) := by
    intro l n h iv ix G xs
    dsimp only [memAt]
    rw [realize_embedFormula]
    have hfn : (fun i : Fin (k + 2) => xs (idx2 h iv ix i)) =
        Fin.snoc (Fin.snoc (fun i : Fin k => xs (idxK h i)) (xs iv)) (xs ix) := by
      funext i
      refine Fin.lastCases ?_ ?_ i
      · simp [idx2]
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · simp [idx2]
        · intro r; simp [idx2]
    rw [hfn]
  let valid_bf : FirstOrder.Language.graph.BoundedFormula Empty k :=
    FirstOrder.Language.BoundedFormula.relabel (fun i => (Sum.inr i : Empty ⊕ Fin k)) valid_φ
  let nonempty_bf : FirstOrder.Language.graph.BoundedFormula Empty k :=
    (domAt (l := k + 1) (by omega) ⟨k, by omega⟩).ex
  let irrefl_bf : FirstOrder.Language.graph.BoundedFormula Empty k :=
    ((domAt (l := k + 1) (by omega) ⟨k, by omega⟩).imp
      (ltAt (l := k + 1) (by omega) ⟨k, by omega⟩ ⟨k, by omega⟩).not).all
  let trans_bf : FirstOrder.Language.graph.BoundedFormula Empty k :=
    (((domAt (l := k + 3) (by omega) ⟨k, by omega⟩ ⊓
       domAt (l := k + 3) (by omega) ⟨k + 1, by omega⟩ ⊓
       domAt (l := k + 3) (by omega) ⟨k + 2, by omega⟩ ⊓
       ltAt (l := k + 3) (by omega) ⟨k, by omega⟩ ⟨k + 1, by omega⟩ ⊓
       ltAt (l := k + 3) (by omega) ⟨k + 1, by omega⟩ ⟨k + 2, by omega⟩).imp
      (ltAt (l := k + 3) (by omega) ⟨k, by omega⟩ ⟨k + 2, by omega⟩))).all.all.all
  let trich_bf : FirstOrder.Language.graph.BoundedFormula Empty k :=
    (((domAt (l := k + 2) (by omega) ⟨k, by omega⟩ ⊓
       domAt (l := k + 2) (by omega) ⟨k + 1, by omega⟩).imp
      (ltAt (l := k + 2) (by omega) ⟨k, by omega⟩ ⟨k + 1, by omega⟩ ⊔
       FirstOrder.Language.Term.bdEqual
         (FirstOrder.Language.Term.var (Sum.inr ⟨k, by omega⟩))
         (FirstOrder.Language.Term.var (Sum.inr ⟨k + 1, by omega⟩)) ⊔
       ltAt (l := k + 2) (by omega) ⟨k + 1, by omega⟩ ⟨k, by omega⟩))).all.all
  let Px8 : Fin 7 → FirstOrder.Language.graph.BoundedFormula Empty (k + 8) :=
    fun b => memAt (l := k + 8) (by omega) ⟨k + b.val, by omega⟩ ⟨k + 7, by omega⟩
  obtain ⟨lt100_x, hlt100_x⟩ := exists_ltConst_bf 100 (by omega) Px8
  obtain ⟨eq0_x, heq0_x⟩ := exists_eqConst_bf 0 (by omega) Px8
  obtain ⟨lt10_x, hlt10_x⟩ := exists_ltConst_bf 10 (by omega) Px8
  obtain ⟨lt41_x, hlt41_x⟩ := exists_ltConst_bf 41 (by omega) Px8
  let isMin_x : FirstOrder.Language.graph.BoundedFormula Empty (k + 8) :=
    ((domAt (l := k + 9) (by omega) ⟨k + 8, by omega⟩).imp
      (ltAt (l := k + 9) (by omega) ⟨k + 8, by omega⟩ ⟨k + 7, by omega⟩).not).all
  let isMax_x : FirstOrder.Language.graph.BoundedFormula Empty (k + 8) :=
    ((domAt (l := k + 9) (by omega) ⟨k + 8, by omega⟩).imp
      (ltAt (l := k + 9) (by omega) ⟨k + 7, by omega⟩ ⟨k + 8, by omega⟩).not).all
  let cond_lt100 : FirstOrder.Language.graph.BoundedFormula Empty (k + 7) :=
    ((domAt (l := k + 8) (by omega) ⟨k + 7, by omega⟩).imp lt100_x).all
  let cond_min : FirstOrder.Language.graph.BoundedFormula Empty (k + 7) :=
    ((domAt (l := k + 8) (by omega) ⟨k + 7, by omega⟩).imp (isMin_x.imp eq0_x)).all
  let cond_max : FirstOrder.Language.graph.BoundedFormula Empty (k + 7) :=
    ((domAt (l := k + 8) (by omega) ⟨k + 7, by omega⟩).imp (isMax_x.imp (lt10_x.not ⊓ lt41_x))).all
  let Px9 : Fin 7 → FirstOrder.Language.graph.BoundedFormula Empty (k + 9) :=
    fun b => memAt (l := k + 9) (by omega) ⟨k + b.val, by omega⟩ ⟨k + 7, by omega⟩
  let Py9 : Fin 7 → FirstOrder.Language.graph.BoundedFormula Empty (k + 9) :=
    fun b => memAt (l := k + 9) (by omega) ⟨k + b.val, by omega⟩ ⟨k + 8, by omega⟩
  obtain ⟨inc_xy, hinc_xy⟩ := exists_incMod100_bf Px9 Py9
  let isSucc_xy : FirstOrder.Language.graph.BoundedFormula Empty (k + 9) :=
    ltAt (l := k + 9) (by omega) ⟨k + 7, by omega⟩ ⟨k + 8, by omega⟩ ⊓
      ((domAt (l := k + 10) (by omega) ⟨k + 9, by omega⟩).imp
        (ltAt (l := k + 10) (by omega) ⟨k + 7, by omega⟩ ⟨k + 9, by omega⟩ ⊓
         ltAt (l := k + 10) (by omega) ⟨k + 9, by omega⟩ ⟨k + 8, by omega⟩).not).all
  let cond_step : FirstOrder.Language.graph.BoundedFormula Empty (k + 7) :=
    (((domAt (l := k + 9) (by omega) ⟨k + 7, by omega⟩ ⊓
       domAt (l := k + 9) (by omega) ⟨k + 8, by omega⟩ ⊓
       isSucc_xy).imp inc_xy)).all.all
  let counter_body : FirstOrder.Language.graph.BoundedFormula Empty (k + 7) :=
    cond_lt100 ⊓ cond_min ⊓ cond_step ⊓ cond_max
  let counter_bf : FirstOrder.Language.graph.BoundedFormula Empty k :=
    counter_body.ex.ex.ex.ex.ex.ex.ex
  let full_body : FirstOrder.Language.graph.BoundedFormula Empty k :=
    valid_bf ⊓ nonempty_bf ⊓ irrefl_bf ⊓ trans_bf ⊓ trich_bf ⊓ counter_bf
  refine ⟨full_body.exs, ?_⟩
  intro n G
  classical
  let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
  rw [FirstOrder.Language.Sentence.Realize, FirstOrder.Language.BoundedFormula.realize_exs,
    Subsingleton.elim (default : Empty → Fin n) Empty.elim]
  have hvalid : ∀ a : Fin k → Fin n,
      valid_bf.Realize Empty.elim a ↔ valid_φ.Realize a := by
    intro a
    exact realize_embedFormula valid_φ id G a
  have hprefix1 : ∀ (a : Fin k → Fin n) (x : Fin n),
      (fun i : Fin k => (Fin.snoc a x : Fin (k + 1) → Fin n) (idxK (l := k + 1) (by omega) i)) = a := by
    intro a x; funext i; exact snoc_apply_lt a x i.isLt
  have hprefix2 : ∀ (a : Fin k → Fin n) (x y : Fin n),
      (fun i : Fin k => (Fin.snoc (Fin.snoc a x) y : Fin (k + 2) → Fin n) (idxK (l := k + 2) (by omega) i)) = a := by
    intro a x y; funext i
    rw [snoc_apply_lt _ y (by omega), snoc_apply_lt a x i.isLt]
  have hprefix3 : ∀ (a : Fin k → Fin n) (x y z : Fin n),
      (fun i : Fin k => (Fin.snoc (Fin.snoc (Fin.snoc a x) y) z : Fin (k + 3) → Fin n) (idxK (l := k + 3) (by omega) i)) = a := by
    intro a x y z; funext i
    rw [snoc_apply_lt _ z (by omega), snoc_apply_lt _ y (by omega), snoc_apply_lt a x i.isLt]
  have hsnoc7_a : ∀ (a : Fin k → Fin n) (v0 v1 v2 v3 v4 v5 v6 : Fin n) (i : Fin k),
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc a v0) v1) v2) v3) v4) v5) v6 : Fin (k + 7) → Fin n)
        ⟨i.val, by omega⟩ = a i := by
    intro a v0 v1 v2 v3 v4 v5 v6 i
    rw [snoc_apply_lt _ v6 (by omega), snoc_apply_lt _ v5 (by omega),
      snoc_apply_lt _ v4 (by omega), snoc_apply_lt _ v3 (by omega),
      snoc_apply_lt _ v2 (by omega), snoc_apply_lt _ v1 (by omega),
      snoc_apply_lt a v0 i.isLt]
  have hsnoc7_v : ∀ (a : Fin k → Fin n) (v : Fin 7 → Fin n) (b : Fin 7),
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc a (v 0)) (v 1)) (v 2)) (v 3)) (v 4)) (v 5)) (v 6) : Fin (k + 7) → Fin n)
        ⟨k + b.val, by omega⟩ = v b := by
    intro a v b
    fin_cases b
    · simp only [add_zero]
      rw [snoc_apply_lt _ (v 6) (by omega), snoc_apply_lt _ (v 5) (by omega),
        snoc_apply_lt _ (v 4) (by omega), snoc_apply_lt _ (v 3) (by omega),
        snoc_apply_lt _ (v 2) (by omega), snoc_apply_lt _ (v 1) (by omega),
        snoc_apply_eq a (v 0)]
      rfl
    · dsimp only
      rw [snoc_apply_lt _ (v 6) (by omega), snoc_apply_lt _ (v 5) (by omega),
        snoc_apply_lt _ (v 4) (by omega), snoc_apply_lt _ (v 3) (by omega),
        snoc_apply_lt _ (v 2) (by omega), snoc_apply_eq _ (v 1)]
      rfl
    · dsimp only
      rw [snoc_apply_lt _ (v 6) (by omega), snoc_apply_lt _ (v 5) (by omega),
        snoc_apply_lt _ (v 4) (by omega), snoc_apply_lt _ (v 3) (by omega),
        snoc_apply_eq _ (v 2)]
      rfl
    · dsimp only
      rw [snoc_apply_lt _ (v 6) (by omega), snoc_apply_lt _ (v 5) (by omega),
        snoc_apply_lt _ (v 4) (by omega), snoc_apply_eq _ (v 3)]
      rfl
    · dsimp only
      rw [snoc_apply_lt _ (v 6) (by omega), snoc_apply_lt _ (v 5) (by omega),
        snoc_apply_eq _ (v 4)]
      rfl
    · dsimp only
      rw [snoc_apply_lt _ (v 6) (by omega), snoc_apply_eq _ (v 5)]
      rfl
    · dsimp only
      rw [snoc_apply_eq _ (v 6)]
      rfl
  have hbody_iff : ∀ a : Fin k → Fin n,
      let D : Finset (Fin n) := Finset.univ.filter fun x => dom_φ.Realize (Fin.snoc a x)
      full_body.Realize Empty.elim a ↔
        valid_φ.Realize a ∧
        D.Nonempty ∧
        (∀ x ∈ D, ¬ lt_φ.Realize (Fin.snoc (Fin.snoc a x) x)) ∧
        (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
          lt_φ.Realize (Fin.snoc (Fin.snoc a x) y) →
          lt_φ.Realize (Fin.snoc (Fin.snoc a y) z) →
          lt_φ.Realize (Fin.snoc (Fin.snoc a x) z)) ∧
        (∀ x ∈ D, ∀ y ∈ D,
          lt_φ.Realize (Fin.snoc (Fin.snoc a x) y) ∨ x = y ∨ lt_φ.Realize (Fin.snoc (Fin.snoc a y) x)) ∧
        ∃ v : Fin 7 → Fin n,
          let c : Fin n → ℕ := fun x => ∑ b : Fin 7,
            if mem_φ.Realize (Fin.snoc (Fin.snoc a (v b)) x) then 2 ^ b.val else 0
          (∀ x ∈ D, c x < 100) ∧
          (∀ x ∈ D, (∀ y ∈ D, ¬ lt_φ.Realize (Fin.snoc (Fin.snoc a y) x)) → c x = 0) ∧
          (∀ x ∈ D, ∀ y ∈ D,
            (lt_φ.Realize (Fin.snoc (Fin.snoc a x) y) ∧
             ∀ z ∈ D, ¬ (lt_φ.Realize (Fin.snoc (Fin.snoc a x) z) ∧
               lt_φ.Realize (Fin.snoc (Fin.snoc a z) y))) →
            c y = (c x + 1) % 100) ∧
          (∀ x ∈ D, (∀ y ∈ D, ¬ lt_φ.Realize (Fin.snoc (Fin.snoc a x) y)) →
            10 ≤ c x ∧ c x ≤ 40) := by
    intro a D
    have hmemD : ∀ x : Fin n, x ∈ D ↔ dom_φ.Realize (Fin.snoc a x) := by
      intro x; simp [D]
    have hne_iff : nonempty_bf.Realize Empty.elim a ↔ D.Nonempty := by
      dsimp only [nonempty_bf]
      rw [FirstOrder.Language.BoundedFormula.realize_ex]
      constructor
      · rintro ⟨x, hx⟩
        rw [hdomAt (h := by omega), hprefix1, snoc_apply_eq] at hx
        exact ⟨x, (hmemD x).mpr hx⟩
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        rw [hdomAt (h := by omega), hprefix1, snoc_apply_eq]
        exact (hmemD x).mp hx
    have hirr_iff : irrefl_bf.Realize Empty.elim a ↔
        ∀ x ∈ D, ¬ lt_φ.Realize (Fin.snoc (Fin.snoc a x) x) := by
      dsimp only [irrefl_bf]
      simp only [FirstOrder.Language.BoundedFormula.realize_all,
        FirstOrder.Language.BoundedFormula.realize_imp,
        FirstOrder.Language.BoundedFormula.realize_not, hdomAt, hltAt, hprefix1, snoc_apply_eq,
        hmemD]
    have htrans_iff : trans_bf.Realize Empty.elim a ↔
        ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
          lt_φ.Realize (Fin.snoc (Fin.snoc a x) y) →
          lt_φ.Realize (Fin.snoc (Fin.snoc a y) z) →
          lt_φ.Realize (Fin.snoc (Fin.snoc a x) z) := by
      dsimp only [trans_bf]
      simp only [FirstOrder.Language.BoundedFormula.realize_all,
        FirstOrder.Language.BoundedFormula.realize_imp,
        FirstOrder.Language.BoundedFormula.realize_inf, hdomAt, hltAt, hprefix3,
        snoc3_0, snoc3_1, snoc_apply_eq, hmemD]
      constructor
      · intro h x hx y hy z hz hxy hyz
        exact h x y z ⟨⟨⟨⟨hx, hy⟩, hz⟩, hxy⟩, hyz⟩
      · intro h x y z ⟨⟨⟨⟨hx, hy⟩, hz⟩, hxy⟩, hyz⟩
        exact h x hx y hy z hz hxy hyz
    have htrich_iff : trich_bf.Realize Empty.elim a ↔
        ∀ x ∈ D, ∀ y ∈ D,
          lt_φ.Realize (Fin.snoc (Fin.snoc a x) y) ∨ x = y ∨ lt_φ.Realize (Fin.snoc (Fin.snoc a y) x) := by
      dsimp only [trich_bf]
      simp only [FirstOrder.Language.BoundedFormula.realize_all,
        FirstOrder.Language.BoundedFormula.realize_imp,
        FirstOrder.Language.BoundedFormula.realize_inf,
        FirstOrder.Language.BoundedFormula.realize_sup,
        FirstOrder.Language.BoundedFormula.realize_bdEqual,
        FirstOrder.Language.Term.realize_var, Sum.elim_inr,
        hdomAt, hltAt, hprefix2, snoc2_0, snoc_apply_eq, hmemD]
      constructor
      · intro h x hx y hy
        rcases h x y ⟨hx, hy⟩ with (hxy | hxy) | hyx
        · exact Or.inl hxy
        · exact Or.inr (Or.inl hxy)
        · exact Or.inr (Or.inr hyx)
      · intro h x y ⟨hx, hy⟩
        rcases h x hx y hy with hxy | hxy | hyx
        · exact Or.inl (Or.inl hxy)
        · exact Or.inl (Or.inr hxy)
        · exact Or.inr hyx
    have hcounter_iff : counter_bf.Realize Empty.elim a ↔
        ∃ v : Fin 7 → Fin n,
          let c : Fin n → ℕ := fun x => ∑ b : Fin 7,
            if mem_φ.Realize (Fin.snoc (Fin.snoc a (v b)) x) then 2 ^ b.val else 0
          (∀ x ∈ D, c x < 100) ∧
          (∀ x ∈ D, (∀ y ∈ D, ¬ lt_φ.Realize (Fin.snoc (Fin.snoc a y) x)) → c x = 0) ∧
          (∀ x ∈ D, ∀ y ∈ D,
            (lt_φ.Realize (Fin.snoc (Fin.snoc a x) y) ∧
             ∀ z ∈ D, ¬ (lt_φ.Realize (Fin.snoc (Fin.snoc a x) z) ∧
               lt_φ.Realize (Fin.snoc (Fin.snoc a z) y))) →
            c y = (c x + 1) % 100) ∧
          (∀ x ∈ D, (∀ y ∈ D, ¬ lt_φ.Realize (Fin.snoc (Fin.snoc a x) y)) →
            10 ≤ c x ∧ c x ≤ 40) := by
      have hex7 : counter_bf.Realize Empty.elim a ↔
          ∃ v : Fin 7 → Fin n,
            counter_body.Realize Empty.elim
              (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc a (v 0)) (v 1)) (v 2)) (v 3)) (v 4)) (v 5)) (v 6)) := by
        dsimp only [counter_bf]
        simp only [FirstOrder.Language.BoundedFormula.realize_ex]
        constructor
        · rintro ⟨v0, v1, v2, v3, v4, v5, v6, h⟩
          let v : Fin 7 → Fin n := fun b =>
            match b.val with
            | 0 => v0 | 1 => v1 | 2 => v2 | 3 => v3 | 4 => v4 | 5 => v5 | _ => v6
          exact ⟨v, h⟩
        · rintro ⟨v, h⟩
          exact ⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, h⟩
      rw [hex7]
      apply exists_congr
      intro v
      set av : Fin (k + 7) → Fin n :=
        Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc a (v 0)) (v 1)) (v 2)) (v 3)) (v 4)) (v 5)) (v 6)
      have hav_a : ∀ i : Fin k, av ⟨i.val, by omega⟩ = a i := hsnoc7_a a (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
      have hav_v : ∀ b : Fin 7, av ⟨k + b.val, by omega⟩ = v b := hsnoc7_v a v
      have hpref8 : ∀ x : Fin n,
          (fun i : Fin k => (Fin.snoc av x : Fin (k + 8) → Fin n) (idxK (l := k + 8) (by omega) i)) = a := by
        intro x; funext i; rw [snoc_apply_lt av x (by omega)]; exact hav_a i
      have hpref9 : ∀ x y : Fin n,
          (fun i : Fin k => (Fin.snoc (Fin.snoc av x) y : Fin (k + 9) → Fin n) (idxK (l := k + 9) (by omega) i)) = a := by
        intro x y; funext i
        rw [snoc_apply_lt _ y (by omega), snoc_apply_lt av x (by omega)]; exact hav_a i
      have hpref10 : ∀ x y z : Fin n,
          (fun i : Fin k => (Fin.snoc (Fin.snoc (Fin.snoc av x) y) z : Fin (k + 10) → Fin n) (idxK (l := k + 10) (by omega) i)) = a := by
        intro x y z; funext i
        rw [snoc_apply_lt _ z (by omega), snoc_apply_lt _ y (by omega), snoc_apply_lt av x (by omega)]
        exact hav_a i
      have hPx8_eq : ∀ (x : Fin n) (b : Fin 7),
          (Px8 b).Realize Empty.elim (Fin.snoc av x) ↔ mem_φ.Realize (Fin.snoc (Fin.snoc a (v b)) x) := by
        intro x b
        dsimp only [Px8]
        rw [hmemAt (h := by omega), hpref8 x, snoc_apply_lt av x (by omega), hav_v b, snoc_apply_eq av x]
      have hPx9_eq : ∀ (x y : Fin n) (b : Fin 7),
          (Px9 b).Realize Empty.elim (Fin.snoc (Fin.snoc av x) y) ↔
            mem_φ.Realize (Fin.snoc (Fin.snoc a (v b)) x) := by
        intro x y b
        dsimp only [Px9]
        rw [hmemAt (h := by omega), hpref9 x y, snoc_apply_lt _ y (by omega), snoc_apply_lt av x (by omega),
          hav_v b, snoc_apply_lt _ y (by omega), snoc_apply_eq av x]
      have hPy9_eq : ∀ (x y : Fin n) (b : Fin 7),
          (Py9 b).Realize Empty.elim (Fin.snoc (Fin.snoc av x) y) ↔
            mem_φ.Realize (Fin.snoc (Fin.snoc a (v b)) y) := by
        intro x y b
        dsimp only [Py9]
        rw [hmemAt (h := by omega), hpref9 x y, snoc_apply_lt _ y (by omega), snoc_apply_lt av x (by omega),
          hav_v b, snoc_apply_eq _ y]
      let c : Fin n → ℕ := fun x => ∑ b : Fin 7,
        if mem_φ.Realize (Fin.snoc (Fin.snoc a (v b)) x) then 2 ^ b.val else 0
      have hsum8 : ∀ x : Fin n,
          (∑ b : Fin 7, if (Px8 b).Realize Empty.elim (Fin.snoc av x) then 2 ^ b.val else 0) = c x := by
        intro x; apply Finset.sum_congr rfl; intro b _; simp only [hPx8_eq x b]
      have hsum9x : ∀ x y : Fin n,
          (∑ b : Fin 7, if (Px9 b).Realize Empty.elim (Fin.snoc (Fin.snoc av x) y) then 2 ^ b.val else 0) = c x := by
        intro x y; apply Finset.sum_congr rfl; intro b _; simp only [hPx9_eq x y b]
      have hsum9y : ∀ x y : Fin n,
          (∑ b : Fin 7, if (Py9 b).Realize Empty.elim (Fin.snoc (Fin.snoc av x) y) then 2 ^ b.val else 0) = c y := by
        intro x y; apply Finset.sum_congr rfl; intro b _; simp only [hPy9_eq x y b]
      have h100_iff : cond_lt100.Realize Empty.elim av ↔ ∀ x ∈ D, c x < 100 := by
        dsimp only [cond_lt100]
        simp only [FirstOrder.Language.BoundedFormula.realize_all,
          FirstOrder.Language.BoundedFormula.realize_imp, hdomAt, hpref8, snoc_apply_eq,
          hlt100_x n G, hsum8, hmemD]
      have hmin_iff : cond_min.Realize Empty.elim av ↔
          ∀ x ∈ D, (∀ y ∈ D, ¬ lt_φ.Realize (Fin.snoc (Fin.snoc a y) x)) → c x = 0 := by
        dsimp only [cond_min, isMin_x]
        simp only [FirstOrder.Language.BoundedFormula.realize_all,
          FirstOrder.Language.BoundedFormula.realize_imp,
          FirstOrder.Language.BoundedFormula.realize_not, hdomAt, hltAt, hpref8, hpref9,
          snoc2_0, snoc_apply_eq, heq0_x n G, hsum8, hmemD]
      have hmax_iff : cond_max.Realize Empty.elim av ↔
          ∀ x ∈ D, (∀ y ∈ D, ¬ lt_φ.Realize (Fin.snoc (Fin.snoc a x) y)) → 10 ≤ c x ∧ c x ≤ 40 := by
        dsimp only [cond_max, isMax_x]
        simp only [FirstOrder.Language.BoundedFormula.realize_all,
          FirstOrder.Language.BoundedFormula.realize_imp,
          FirstOrder.Language.BoundedFormula.realize_inf,
          FirstOrder.Language.BoundedFormula.realize_not, hdomAt, hltAt, hpref8, hpref9,
          snoc2_0, snoc_apply_eq, hlt10_x n G, hlt41_x n G, hsum8, hmemD]
        refine forall_congr' fun x => imp_congr_right fun _ => imp_congr_right fun _ => ?_
        omega
      have hstep_iff : (∀ x ∈ D, c x < 100) →
          (cond_step.Realize Empty.elim av ↔
            ∀ x ∈ D, ∀ y ∈ D,
              (lt_φ.Realize (Fin.snoc (Fin.snoc a x) y) ∧
               ∀ z ∈ D, ¬ (lt_φ.Realize (Fin.snoc (Fin.snoc a x) z) ∧
                 lt_φ.Realize (Fin.snoc (Fin.snoc a z) y))) →
              c y = (c x + 1) % 100) := by
        intro h100
        dsimp only [cond_step, isSucc_xy]
        simp only [FirstOrder.Language.BoundedFormula.realize_all,
          FirstOrder.Language.BoundedFormula.realize_imp,
          FirstOrder.Language.BoundedFormula.realize_inf,
          FirstOrder.Language.BoundedFormula.realize_not, hdomAt, hltAt, hpref9, hpref10,
          snoc2_0, snoc3_0, snoc_apply_eq, hmemD]
        constructor
        · intro h x hx y hy hsucc
          have hinc := h x y ⟨⟨hx, hy⟩, hsucc⟩
          rw [hinc_xy n G (Fin.snoc (Fin.snoc av x) y) (by rw [hsum9x]; exact h100 x ((hmemD x).mpr hx)),
            hsum9x, hsum9y] at hinc
          exact hinc
        · intro h x y ⟨⟨hx, hy⟩, hsucc⟩
          rw [hinc_xy n G (Fin.snoc (Fin.snoc av x) y) (by rw [hsum9x]; exact h100 x ((hmemD x).mpr hx)),
            hsum9x, hsum9y]
          exact h x hx y hy hsucc
      dsimp only [counter_body]
      simp only [FirstOrder.Language.BoundedFormula.realize_inf, h100_iff, hmin_iff, hmax_iff]
      constructor
      · rintro ⟨⟨⟨h100, hmin⟩, hst⟩, hmax⟩
        exact ⟨h100, hmin, (hstep_iff h100).mp hst, hmax⟩
      · rintro ⟨h100, hmin, hst, hmax⟩
        exact ⟨⟨⟨h100, hmin⟩, (hstep_iff h100).mpr hst⟩, hmax⟩
    dsimp only [full_body]
    simp only [FirstOrder.Language.BoundedFormula.realize_inf, hvalid, hne_iff, hirr_iff,
      htrans_iff, htrich_iff, hcounter_iff, and_assoc]
  constructor
  · rintro ⟨a, ha⟩
    let D : Finset (Fin n) := Finset.univ.filter fun x => dom_φ.Realize (Fin.snoc a x)
    have hspec := (hbody_iff a).mp ha
    exact ⟨a, D, hspec.1, fun x => by simp [D], hspec.2⟩
  · rintro ⟨a, D, hval, hD, hrest⟩
    refine ⟨a, (hbody_iff a).mpr ?_⟩
    have hDeq : D = Finset.univ.filter fun x => dom_φ.Realize (Fin.snoc a x) := by
      ext x; simp [hD]
    rw [← hDeq]
    exact ⟨hval, hrest⟩

/- ============================================================================
   Part 5: Combining UNIV Completeness, Counter Soundness, and Measure Bounds
   ============================================================================ -/

/- From any definable (valid, dom, lt, mem) interpretation with UNIV and oscillating size
mod 100 along two subsequences (each with G(n, n^(-alpha)) probability >= 3/4), produce a
first-order graph sentence whose probability fails to converge to any b : ENNReal. -/
lemma exists_oscillating_sentence_of_univ_linord {α : ℝ} (hα : 0 < α)
    (k : ℕ)
    (valid_φ : FirstOrder.Language.graph.Formula (Fin k))
    (dom_φ : FirstOrder.Language.graph.Formula (Fin (k + 1)))
    (lt_φ : FirstOrder.Language.graph.Formula (Fin (k + 2)))
    (mem_φ : FirstOrder.Language.graph.Formula (Fin (k + 2)))
    (hHigh : Filter.Frequently (fun n : ℕ =>
      (3 : ENNReal) / 4 ≤ ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα
        {G : SimpleGraph (Fin n) | ∃ (a : Fin k → Fin n) (D : Finset (Fin n)),
          (let lt (x y : Fin n) :=
             @FirstOrder.Language.Formula.Realize _ _ G.structure _ lt_φ (Fin.snoc (Fin.snoc a x) y)
           @FirstOrder.Language.Formula.Realize _ _ G.structure _ valid_φ a ∧
           (∀ x, x ∈ D ↔ @FirstOrder.Language.Formula.Realize _ _ G.structure _ dom_φ (Fin.snoc a x)) ∧
           D.Nonempty ∧
           (∀ x ∈ D, ¬ lt x x) ∧
           (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, lt x y → lt y z → lt x z) ∧
           (∀ x ∈ D, ∀ y ∈ D, lt x y ∨ x = y ∨ lt y x)) ∧
          (∀ (S : Finset (Fin n)), S ⊆ D → ∃ v, ∀ x ∈ D,
            @FirstOrder.Language.Formula.Realize _ _ G.structure _ mem_φ
              (Fin.snoc (Fin.snoc a v) x) ↔ x ∈ S) ∧
          10 ≤ (D.card - 1) % 100 ∧ (D.card - 1) % 100 ≤ 40}) Filter.atTop)
    (hLow : Filter.Frequently (fun n : ℕ =>
      (3 : ENNReal) / 4 ≤ ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα
        {G : SimpleGraph (Fin n) | ∀ (a : Fin k → Fin n) (D : Finset (Fin n)),
          (let lt (x y : Fin n) :=
             @FirstOrder.Language.Formula.Realize _ _ G.structure _ lt_φ (Fin.snoc (Fin.snoc a x) y)
           @FirstOrder.Language.Formula.Realize _ _ G.structure _ valid_φ a ∧
           (∀ x, x ∈ D ↔ @FirstOrder.Language.Formula.Realize _ _ G.structure _ dom_φ (Fin.snoc a x)) ∧
           D.Nonempty ∧
           (∀ x ∈ D, ¬ lt x x) ∧
           (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, lt x y → lt y z → lt x z) ∧
           (∀ x ∈ D, ∀ y ∈ D, lt x y ∨ x = y ∨ lt y x)) →
          ¬ (10 ≤ (D.card - 1) % 100 ∧ (D.card - 1) % 100 ≤ 40)}) Filter.atTop) :
    ∃ φ : FirstOrder.Language.graph.Sentence,
      ∀ b : ENNReal,
        ¬ Filter.Tendsto (fun n =>
          ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα
            {G | @FirstOrder.Language.Sentence.Realize FirstOrder.Language.graph (Fin n) G.structure φ})
          Filter.atTop (nhds b) := by
  classical
  obtain ⟨φ, hφ⟩ := exists_counter_sentence k valid_φ dom_φ lt_φ mem_φ
  refine ⟨φ, ?_⟩
  apply not_tendsto_of_frequently_ge_le
  · refine hHigh.mono ?_
    intro n hn
    refine le_trans hn (MeasureTheory.measure_mono ?_)
    intro G hG
    rw [Set.mem_ofPred_eq, hφ n G]
    rcases hG with ⟨a, D, ⟨hval, hD, hne, hirr, htrans, htrich⟩, hUNIV, hres_lo, hres_hi⟩
    let _ : FirstOrder.Language.graph.Structure (Fin n) := G.structure
    let lt : Fin n → Fin n → Prop := fun x y => lt_φ.Realize (Fin.snoc (Fin.snoc a x) y)
    obtain ⟨f, hf_mem, hf_surj, hf_mono⟩ := exists_strictMono_enum lt D.card D rfl hirr htrans htrich
    have hf_lt_iff : ∀ i j : Fin D.card, lt (f i) (f j) ↔ i < j := by
      intro i j
      constructor
      · intro hlt
        rcases lt_trichotomy i j with h | rfl | h
        · exact h
        · exact absurd hlt (hirr _ (hf_mem i))
        · exact absurd (htrans _ (hf_mem i) _ (hf_mem j) _ (hf_mem i) hlt (hf_mono j i h))
            (hirr _ (hf_mem i))
      · exact hf_mono i j
    have hf_inj : Function.Injective f := by
      intro i j heq
      rcases lt_trichotomy i j with h | h | h
      · exact absurd (heq ▸ hf_mono i j h) (hirr _ (hf_mem j))
      · exact h
      · exact absurd (heq ▸ hf_mono j i h) (hirr _ (hf_mem j))
    let rank : Fin n → ℕ := fun x =>
      if hx : x ∈ D then (Classical.choose (hf_surj x hx)).val else 0
    have hrank_f : ∀ i : Fin D.card, rank (f i) = i.val := by
      intro i
      have hiD : f i ∈ D := hf_mem i
      simp only [rank, hiD, dite_true]
      have hspec := Classical.choose_spec (hf_surj (f i) hiD)
      exact congrArg Fin.val (hf_inj hspec)
    have hbit_ex : ∀ b : Fin 7, ∃ v : Fin n, ∀ x ∈ D,
        mem_φ.Realize (Fin.snoc (Fin.snoc a v) x) ↔ (rank x % 100).testBit b.val = true := by
      intro b
      let Sb : Finset (Fin n) := D.filter fun x => (rank x % 100).testBit b.val = true
      have hSb_sub : Sb ⊆ D := Finset.filter_subset _ D
      obtain ⟨v, hv⟩ := hUNIV Sb hSb_sub
      refine ⟨v, fun x hx => ?_⟩
      rw [hv x hx]
      simp [Sb, hx]
    let v : Fin 7 → Fin n := fun b => Classical.choose (hbit_ex b)
    have hv_spec : ∀ b : Fin 7, ∀ x ∈ D,
        mem_φ.Realize (Fin.snoc (Fin.snoc a (v b)) x) ↔ (rank x % 100).testBit b.val = true :=
      fun b => Classical.choose_spec (hbit_ex b)
    have hc_eq : ∀ x ∈ D,
        (∑ b : Fin 7, if mem_φ.Realize (Fin.snoc (Fin.snoc a (v b)) x) then 2 ^ b.val else 0) =
          rank x % 100 := by
      intro x hx
      have h1 : (∑ b : Fin 7, if mem_φ.Realize (Fin.snoc (Fin.snoc a (v b)) x) then 2 ^ b.val else 0) =
          ∑ b : Fin 7, if (rank x % 100).testBit b.val then 2 ^ b.val else 0 := by
        apply Finset.sum_congr rfl
        intro b _
        by_cases hm : mem_φ.Realize (Fin.snoc (Fin.snoc a (v b)) x)
        · simp [hm, (hv_spec b x hx).mp hm]
        · have hbf : (rank x % 100).testBit b.val = false := by
            cases h : (rank x % 100).testBit b.val
            · rfl
            · exact absurd ((hv_spec b x hx).mpr h) hm
          simp [hm, hbf]
      rw [h1, sum_testBit_prefix (rank x % 100) 7,
        Nat.mod_eq_of_lt (by have := Nat.mod_lt (rank x) (by norm_num : 0 < 100); omega)]
    refine ⟨a, D, hval, hD, hne, hirr, htrans, htrich, v, ?_, ?_, ?_, ?_⟩
    · intro x hx
      dsimp only
      rw [hc_eq x hx]
      exact Nat.mod_lt _ (by norm_num)
    · intro x hx hmin
      dsimp only
      rw [hc_eq x hx]
      obtain ⟨i, rfl⟩ := hf_surj x hx
      have hi0 : i.val = 0 := by
        by_contra hne0
        have hpos : 0 < D.card := Finset.card_pos.mpr hne
        have hlt : lt (f ⟨0, hpos⟩) (f i) := hf_mono ⟨0, hpos⟩ i (by show 0 < i.val; omega)
        exact hmin (f ⟨0, hpos⟩) (hf_mem _) hlt
      rw [hrank_f i, hi0]
    · intro x hx y hy ⟨hxy, hno_mid⟩
      dsimp only
      rw [hc_eq x hx, hc_eq y hy]
      obtain ⟨i, rfl⟩ := hf_surj x hx
      obtain ⟨j, rfl⟩ := hf_surj y hy
      have hij : i.val < j.val := (hf_lt_iff i j).mp hxy
      have hj_eq : j.val = i.val + 1 := by
        by_contra hne1
        have hmid_lt : i.val + 1 < D.card := lt_trans (by omega : i.val + 1 < j.val) j.isLt
        have h1 : lt (f i) (f ⟨i.val + 1, hmid_lt⟩) := hf_mono i ⟨i.val + 1, hmid_lt⟩ (by show i.val < i.val + 1; omega)
        have h2 : lt (f ⟨i.val + 1, hmid_lt⟩) (f j) := hf_mono ⟨i.val + 1, hmid_lt⟩ j (by show i.val + 1 < j.val; omega)
        exact hno_mid (f ⟨i.val + 1, hmid_lt⟩) (hf_mem _) ⟨h1, h2⟩
      rw [hrank_f i, hrank_f j, hj_eq]
      simp [Nat.add_mod]
    · intro x hx hmax
      dsimp only
      rw [hc_eq x hx]
      obtain ⟨i, rfl⟩ := hf_surj x hx
      have hi_last : i.val = D.card - 1 := by
        by_contra hne_last
        have hlast_lt : D.card - 1 < D.card := by have := Finset.card_pos.mpr hne; omega
        have hlt : lt (f i) (f ⟨D.card - 1, hlast_lt⟩) :=
          hf_mono i ⟨D.card - 1, hlast_lt⟩ (by show i.val < D.card - 1; have := i.isLt; omega)
        exact hmax (f ⟨D.card - 1, hlast_lt⟩) (hf_mem _) hlt
      rw [hrank_f i, hi_last]
      exact ⟨hres_lo, hres_hi⟩
  · refine hLow.mono ?_
    intro n hn
    apply prob_le_quarter_of_disjoint_three_quarters hα _ hn
    rw [Set.disjoint_left]
    intro G hGφ hGlow
    rw [Set.mem_ofPred_eq, hφ n G] at hGφ
    rcases hGφ with ⟨a, D, hval, hD, hne, hirr, htrans, htrich, v, _, hmin, hstep, hmax⟩
    have hnot := hGlow a D ⟨hval, hD, hne, hirr, htrans, htrich⟩
    let lt : Fin n → Fin n → Prop := fun x y =>
      @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin (k + 2)) lt_φ (Fin.snoc (Fin.snoc a x) y)
    let c : Fin n → ℕ := fun x => ∑ b : Fin 7,
      if @FirstOrder.Language.Formula.Realize FirstOrder.Language.graph (Fin n) G.structure (Fin (k + 2)) mem_φ (Fin.snoc (Fin.snoc a (v b)) x)
      then 2 ^ b.val else 0
    exact hnot (counter_sound_mod100 lt D hne hirr htrans htrich c hmin hstep hmax)

/- ============================================================================
   Part 6: Main Reduction Theorem
   ============================================================================ -/

/- Deduction of ShelahSpencerZeroOneLaw.zeroOne_rational from H1 (unit-fraction exponents 1/q)
and H2 (general coprime rational exponents p/q, 2 <= p < q). -/
theorem main : H1 → H2 → type_of% @ShelahSpencerZeroOneLaw.zeroOne_rational := by
  intro hH1 hH2 α hα hrat
  obtain ⟨p, q, hp1, hpq, hcop, hα_eq⟩ := rat_coprime_repr hα.1 hα.2 hrat
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  by_cases hp : p = 1
  · subst hp
    have hq2 : 2 ≤ q := by omega
    have hα1 : (0 : ℝ) < (1 : ℝ) / (q : ℝ) := by positivity
    obtain ⟨k, valid_φ, dom_φ, lt_φ, mem_φ, hHigh, hLow⟩ := hH1 q hq2 hα1
    obtain ⟨φ, hφ⟩ := exists_oscillating_sentence_of_univ_linord hα1 k valid_φ dom_φ lt_φ mem_φ hHigh hLow
    refine ⟨φ, ?_⟩
    have hmeas_eq : ∀ n : ℕ,
        ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα.1 =
        ShelahSpencerZeroOneLaw.sparseRandomGraph n ((1 : ℝ) / (q : ℝ)) hα1 := by
      intro n
      have h1 : α = (1 : ℝ) / (q : ℝ) := by simpa using hα_eq
      subst h1
      rfl
    simpa only [hmeas_eq] using hφ
  · have hp2 : 2 ≤ p := by omega
    have hαpq : (0 : ℝ) < (p : ℝ) / (q : ℝ) := by positivity
    obtain ⟨k, valid_φ, dom_φ, lt_φ, mem_φ, hHigh, hLow⟩ := hH2 p q hp2 hpq hcop hαpq
    obtain ⟨φ, hφ⟩ := exists_oscillating_sentence_of_univ_linord hαpq k valid_φ dom_φ lt_φ mem_φ hHigh hLow
    refine ⟨φ, ?_⟩
    have hmeas_eq : ∀ n : ℕ,
        ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα.1 =
        ShelahSpencerZeroOneLaw.sparseRandomGraph n ((p : ℝ) / (q : ℝ)) hαpq := by
      intro n
      subst hα_eq
      rfl
    simpa only [hmeas_eq] using hφ

end OMA.R_ShelahSpencerZeroOneLaw_zeroOne_rational_R1
