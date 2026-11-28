import OMAReductions.R_Erdos61_erdos_61_R1

-- Step Erdos61.erdos_61.R1.H1: hypothesis H1 of reduction Erdos61.erdos_61.R1
-- Credit: @Ezekia1
-- Elementary Ramsey bound: for k ≥ 1, every set of at least k ^ m vertices contains a clique of
-- size m + 1 or an independent set of size k (induction on m: a vertex with at least k ^ (m - 1)
-- neighbours, or else a greedy independent set). With k = ⌈n ^ (1 / (m + 1))⌉ and n large this
-- gives the exponent c = 1 / (m + 1) for the complete graph on m + 1 vertices. The edgeless case
-- is the same statement for the complement graph. For m = 0 the hypothesis is never satisfied.

namespace OMA.E61H1

open Finset

/-- A greedy independent set inside a vertex set in which all degrees are below `D`. -/
theorem greedy {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hD : 0 < D) : ∀ (k : ℕ) (S : Finset V),
    (∀ v ∈ S, (S.filter (G.Adj v)).card < D) → k * D ≤ S.card →
    ∃ T : Finset V, T ⊆ S ∧ T.card = k ∧ G.IsIndepSet (T : Set V) := by
  intro k
  induction k with
  | zero =>
    intro S _ _
    exact ⟨∅, empty_subset S, card_empty, by simp⟩
  | succ k ih =>
    intro S hdeg hcard
    have hSpos : 0 < S.card := by
      have : D ≤ (k + 1) * D := Nat.le_mul_of_pos_left D (Nat.succ_pos k)
      omega
    obtain ⟨v, hv⟩ := card_pos.mp hSpos
    have hsub : S ⊆ (S.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)) ∪
        insert v (S.filter (G.Adj v)) := by
      intro w hw
      by_cases h1 : w = v
      · rw [h1]
        exact mem_union_right _ (mem_insert_self v _)
      · by_cases h2 : G.Adj v w
        · exact mem_union_right _ (mem_insert_of_mem (mem_filter.mpr ⟨hw, h2⟩))
        · exact mem_union_left _ (mem_filter.mpr ⟨hw, h1, h2⟩)
    have hc1 := card_le_card hsub
    have hc2 := card_union_le (S.filter (fun w => w ≠ v ∧ ¬ G.Adj v w))
      (insert v (S.filter (G.Adj v)))
    have hc3 := card_insert_le v (S.filter (G.Adj v))
    have hc4 := hdeg v hv
    have hk : k * D ≤ (S.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).card := by
      have : (k + 1) * D = k * D + D := Nat.succ_mul k D
      omega
    have hdeg' : ∀ u ∈ S.filter (fun w => w ≠ v ∧ ¬ G.Adj v w),
        ((S.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).filter (G.Adj u)).card < D := by
      intro u hu
      refine lt_of_le_of_lt (card_le_card ?_) (hdeg u (mem_filter.mp hu).1)
      exact filter_subset_filter _ (filter_subset _ _)
    obtain ⟨T, hTS, hTc, hTi⟩ := ih _ hdeg' hk
    have hvT : v ∉ T := fun h => (mem_filter.mp (hTS h)).2.1 rfl
    refine ⟨insert v T, ?_, ?_, ?_⟩
    · intro w hw
      rcases mem_insert.mp hw with h | h
      · rw [h]
        exact hv
      · exact (mem_filter.mp (hTS h)).1
    · rw [card_insert_of_notMem hvT, hTc]
    · intro a ha b hb hab
      rw [mem_coe, mem_insert] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · rw [ha]
        exact (mem_filter.mp (hTS hb)).2.2
      · rw [hb]
        exact fun h => (mem_filter.mp (hTS ha)).2.2 h.symm
      · exact hTi (mem_coe.mpr ha) (mem_coe.mpr hb) hab

/-- A set of at least `k ^ m` vertices contains a clique of size `m + 1` or an independent set
of size `k`. -/
theorem ramsey {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 0 < k) : ∀ (m : ℕ) (S : Finset V), k ^ m ≤ S.card →
    (∃ T : Finset V, T ⊆ S ∧ T.card = m + 1 ∧ G.IsClique (T : Set V)) ∨
    (∃ T : Finset V, T ⊆ S ∧ T.card = k ∧ G.IsIndepSet (T : Set V)) := by
  intro m
  induction m with
  | zero =>
    intro S hS
    rw [pow_zero] at hS
    obtain ⟨v, hv⟩ := card_pos.mp hS
    exact Or.inl ⟨{v}, singleton_subset_iff.mpr hv, card_singleton v, by simp⟩
  | succ m ih =>
    intro S hS
    by_cases h : ∃ v ∈ S, k ^ m ≤ (S.filter (G.Adj v)).card
    · obtain ⟨v, hv, hvc⟩ := h
      rcases ih _ hvc with ⟨T, hTS, hTc, hTq⟩ | ⟨T, hTS, hTc, hTi⟩
      · have hvT : v ∉ T := fun h => G.irrefl (mem_filter.mp (hTS h)).2
        refine Or.inl ⟨insert v T, ?_, ?_, ?_⟩
        · intro w hw
          rcases mem_insert.mp hw with h | h
          · rw [h]
            exact hv
          · exact (mem_filter.mp (hTS h)).1
        · rw [card_insert_of_notMem hvT, hTc]
        · intro a ha b hb hab
          rw [mem_coe, mem_insert] at ha hb
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact absurd (ha.trans hb.symm) hab
          · rw [ha]
            exact (mem_filter.mp (hTS hb)).2
          · rw [hb]
            exact ((mem_filter.mp (hTS ha)).2).symm
          · exact hTq (mem_coe.mpr ha) (mem_coe.mpr hb) hab
      · exact Or.inr ⟨T, hTS.trans (filter_subset _ _), hTc, hTi⟩
    · have h' : ∀ v ∈ S, (S.filter (G.Adj v)).card < k ^ m := fun v hv =>
        lt_of_not_ge (fun hge => h ⟨v, hv, hge⟩)
      refine Or.inr (greedy G (k ^ m) (pow_pos hk m) k S h' ?_)
      rw [← pow_succ']
      exact hS

/-- A clique of size `M` gives an induced copy of the complete graph. -/
theorem top_of_clique {n M : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (hT : T.card = M) (hq : G.IsClique (T : Set (Fin n))) :
    ∃ g : Fin M ↪ Fin n, (⊤ : SimpleGraph (Fin M)) = G.comap g := by
  refine ⟨(T.orderEmbOfFin hT).toEmbedding, ?_⟩
  ext a b
  change a ≠ b ↔ G.Adj (T.orderEmbOfFin hT a) (T.orderEmbOfFin hT b)
  constructor
  · intro hab
    exact hq (mem_coe.mpr (T.orderEmbOfFin_mem hT a)) (mem_coe.mpr (T.orderEmbOfFin_mem hT b))
      (fun h => hab ((T.orderEmbOfFin hT).injective h))
  · intro h hab
    rw [hab] at h
    exact G.irrefl h

/-- An independent set of size `M` gives an induced copy of the edgeless graph. -/
theorem bot_of_indep {n M : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (hT : T.card = M) (hi : G.IsIndepSet (T : Set (Fin n))) :
    ∃ g : Fin M ↪ Fin n, (⊥ : SimpleGraph (Fin M)) = G.comap g := by
  refine ⟨(T.orderEmbOfFin hT).toEmbedding, ?_⟩
  ext a b
  change False ↔ G.Adj (T.orderEmbOfFin hT a) (T.orderEmbOfFin hT b)
  constructor
  · exact False.elim
  · intro h
    exact hi (mem_coe.mpr (T.orderEmbOfFin_mem hT a)) (mem_coe.mpr (T.orderEmbOfFin_mem hT b))
      (G.ne_of_adj h) h

theorem rpow_fact (m n : ℕ) : ((n : ℝ) ^ (1 / ((m : ℝ) + 1))) ^ (m + 1) = n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  have h : 1 / ((m : ℝ) + 1) * ((m + 1 : ℕ) : ℝ) = 1 := by
    push_cast
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  rw [h, Real.rpow_one]

theorem ceil_pow_le (m n : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hxpow : x ^ (m + 1) = n)
    (hn : (2 ^ m) ^ (m + 1) ≤ n) : ⌈x⌉₊ ^ m ≤ n ∧ 0 < ⌈x⌉₊ := by
  have hx2 : (2 : ℝ) ^ m ≤ x := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    have h1 : x ^ (m + 1) < ((2 : ℝ) ^ m) ^ (m + 1) :=
      pow_lt_pow_left₀ hlt hx0 (Nat.succ_ne_zero m)
    have h2 : (((2 ^ m) ^ (m + 1) : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    push_cast at h2
    linarith
  have hx1 : 1 ≤ x := le_trans (one_le_pow₀ (by norm_num)) hx2
  have hceil : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  constructor
  · have h3 : ((⌈x⌉₊ : ℝ)) ^ m ≤ (2 * x) ^ m :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) m
    have h4 : (2 * x) ^ m ≤ x ^ (m + 1) := by
      rw [mul_pow, pow_succ']
      exact mul_le_mul_of_nonneg_right hx2 (pow_nonneg hx0 m)
    have h5 : ((⌈x⌉₊ ^ m : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      linarith
    exact Nat.cast_le.mp h5
  · exact Nat.ceil_pos.mpr (by linarith)

/-- For large `n`, a graph on `n` vertices has a clique of size `m + 1` or an independent set of
size at least `n ^ (1 / (m + 1))`. -/
theorem key (m : ℕ) : ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n),
    (∃ T : Finset (Fin n), T.card = m + 1 ∧ G.IsClique (T : Set (Fin n))) ∨
    (n : ℝ) ^ (1 / ((m : ℝ) + 1)) ≤ G.indepNum := by
  refine Filter.eventually_atTop.mpr ⟨(2 ^ m) ^ (m + 1), fun n hn G => ?_⟩
  classical
  obtain ⟨hk1, hk2⟩ := ceil_pow_le m n _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (rpow_fact m n) hn
  have hcard : ⌈(n : ℝ) ^ (1 / ((m : ℝ) + 1))⌉₊ ^ m ≤ (univ : Finset (Fin n)).card := by
    rw [card_univ, Fintype.card_fin]
    exact hk1
  rcases ramsey G _ hk2 m univ hcard with ⟨T, -, hTc, hTq⟩ | ⟨T, -, hTc, hTi⟩
  · exact Or.inl ⟨T, hTc, hTq⟩
  · right
    have h1 : T.card ≤ G.indepNum := hTi.card_le_indepNum
    have h2 : (n : ℝ) ^ (1 / ((m : ℝ) + 1)) ≤ ⌈(n : ℝ) ^ (1 / ((m : ℝ) + 1))⌉₊ := Nat.le_ceil _
    have h3 : ((T.card : ℕ) : ℝ) ≤ (G.indepNum : ℝ) := Nat.cast_le.mpr h1
    rw [hTc] at h3
    exact h2.trans h3

end OMA.E61H1

open OMA.E61H1 in
theorem OMA.solution : OMA.R_Erdos61_erdos_61_R1.H1 := by
  intro m
  rcases m with _ | m
  · constructor
    · refine ⟨1, one_pos, Filter.Eventually.of_forall fun n G hG => ?_⟩
      exact absurd ⟨Function.Embedding.ofIsEmpty, by ext a; exact a.elim0⟩ hG
    · refine ⟨1, one_pos, Filter.Eventually.of_forall fun n G hG => ?_⟩
      exact absurd ⟨Function.Embedding.ofIsEmpty, by ext a; exact a.elim0⟩ hG
  · have hc : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    constructor
    · refine ⟨1 / ((m : ℝ) + 1), hc, ?_⟩
      unfold Erdos61.IsErdosHajnalLowerBound
      filter_upwards [key m] with n hn G hG
      rcases hn G with ⟨T, hTc, hTq⟩ | h
      · exact absurd (top_of_clique G T hTc hTq) hG
      · exact Or.inl h
    · refine ⟨1 / ((m : ℝ) + 1), hc, ?_⟩
      unfold Erdos61.IsErdosHajnalLowerBound
      filter_upwards [key m] with n hn G hG
      rcases hn Gᶜ with ⟨T, hTc, hTq⟩ | h
      · exact absurd (bot_of_indep G T hTc (by rwa [SimpleGraph.isClique_compl] at hTq)) hG
      · rw [SimpleGraph.indepNum_compl] at h
        exact Or.inr h
