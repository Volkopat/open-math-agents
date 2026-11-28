import OMAReductions.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1

-- Reduction Erdos556.erdos_556.variants.benevides_skokan_large_even.R1.H1.R1
-- of step Erdos556.erdos_556.variants.benevides_skokan_large_even.R1.H1
-- Credit: @tgg6956g2z-bot

/-!
# Reducing EC1 absorption (`R1.H1`) via vertex cleaning and hub classification

We discharge the `(1 - α)`-density Markov cleaning and the 8-case pigeonhole classification
of every atypical vertex into either a colour hub (adjacent in colour `i` to at least `20d`
vertices in each of the two matched pairs of colour `i`) or a block-aligned vertex (missing
at most `40d` designated-colour edges to every partner block), splitting `R1.H1` into:

* `H1`: Single-colour two-hub bridge lemma — two hubs linking two `d`-almost-complete
  bipartite pairs of size `≈ 2m` each force `C_{2m}`.
* `H2`: Cleaned EC1 endgame with at most one hub per colour.
-/

open Filter SimpleGraph Finset

namespace OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1_H1_R1

/-- Single-colour two-hub bridge lemma: two distinct vertices outside four pairwise-disjoint
blocks `B 0, B 1, B 2, B 3` (each of size at least `m - 4d`) that each have at least `20d`
neighbours in `B 0 ∪ B 1` and at least `20d` neighbours in `B 2 ∪ B 3`, where `(B 0, B 1)`
and `(B 2, B 3)` are `d`-almost-complete, yield `C_{2m}`. -/
def H1 : Prop :=
  ∀ (m d : ℕ) (G : SimpleGraph (Fin (4 * m))) [DecidableRel G.Adj]
    (B : Fin 4 → Finset (Fin (4 * m))) (x y : Fin (4 * m)),
    2 ≤ m → 1 ≤ d → 100 * d ≤ m →
    Pairwise (fun i j => Disjoint (B i) (B j)) →
    (∀ j, m - 4 * d ≤ (B j).card) →
    (∀ u ∈ B 0, ((B 1).filter (fun v => ¬ G.Adj u v)).card ≤ d) →
    (∀ u ∈ B 1, ((B 0).filter (fun v => ¬ G.Adj u v)).card ≤ d) →
    (∀ u ∈ B 2, ((B 3).filter (fun v => ¬ G.Adj u v)).card ≤ d) →
    (∀ u ∈ B 3, ((B 2).filter (fun v => ¬ G.Adj u v)).card ≤ d) →
    x ≠ y → (∀ j, x ∉ B j ∧ y ∉ B j) →
    20 * d ≤ ((B 0 ∪ B 1).filter (G.Adj x)).card →
    20 * d ≤ ((B 2 ∪ B 3).filter (G.Adj x)).card →
    20 * d ≤ ((B 0 ∪ B 1).filter (G.Adj y)).card →
    20 * d ≤ ((B 2 ∪ B 3).filter (G.Adj y)).card →
    cycleGraph (2 * m) ⊑ G

/-- Cleaned EC1 endgame with at most one hub per colour: four core blocks `B 0 .. B 3` of
size at least `m - 4d` (`d`-almost-complete across all six designated EC1 pairs), extended
to pairwise-disjoint blocks `P 0 .. P 3` (missing at most `40d` edges to each partner core)
plus hub sets `H 0, H 1, H 2` of size at most `1` covering `Fin (4 * m)`. -/
def H2 : Prop :=
  ∀ (m d : ℕ) (c : Fin 3 → SimpleGraph (Fin (4 * m))) [∀ i, DecidableRel (c i).Adj]
    (B P : Fin 4 → Finset (Fin (4 * m))) (H : Fin 3 → Finset (Fin (4 * m))),
    2 ≤ m → 1 ≤ d → 100 * d ≤ m →
    (⊤ : SimpleGraph (Fin (4 * m))).IsEdgeColouring c →
    Pairwise (fun i j => Disjoint (P i) (P j)) →
    (∀ j, B j ⊆ P j ∧ m - 4 * d ≤ (B j).card) →
    (∀ i, (H i).card ≤ 1) →
    (∀ v : Fin (4 * m), (∃ j, v ∈ P j) ∨ (∃ i, v ∈ H i)) →
    let col : Fin 4 → Fin 4 → Fin 3 := fun j k =>
      if (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0) ∨ (j = 2 ∧ k = 3) ∨ (j = 3 ∧ k = 2) then 0
      else if (j = 0 ∧ k = 3) ∨ (j = 3 ∧ k = 0) ∨ (j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1) then 1
      else 2
    (∀ j k, j ≠ k → ∀ u ∈ B j, ((B k).filter (fun v => ¬ (c (col j k)).Adj u v)).card ≤ d) →
    (∀ j k, j ≠ k → ∀ u ∈ P j, ((B k).filter (fun v => ¬ (c (col j k)).Adj u v)).card ≤ 40 * d) →
    (∀ x ∈ H 0, 20 * d ≤ ((B 0 ∪ B 1).filter ((c 0).Adj x)).card ∧
      20 * d ≤ ((B 2 ∪ B 3).filter ((c 0).Adj x)).card) →
    (∀ x ∈ H 1, 20 * d ≤ ((B 0 ∪ B 3).filter ((c 1).Adj x)).card ∧
      20 * d ≤ ((B 1 ∪ B 2).filter ((c 1).Adj x)).card) →
    (∀ x ∈ H 2, 20 * d ≤ ((B 0 ∪ B 2).filter ((c 2).Adj x)).card ∧
      20 * d ≤ ((B 1 ∪ B 3).filter ((c 2).Adj x)).card) →
    ∃ i, cycleGraph (2 * m) ⊑ c i

lemma natCard_eq_filter_card {N : ℕ} (P : Fin N → Prop) [DecidablePred P] :
    Nat.card {v : Fin N // P v} = (Finset.univ.filter P).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma natCard_edges_eq_sum {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (f : Fin N → Fin 4) (S T : Finset (Fin 4)) :
    Nat.card {e : Fin N × Fin N // f e.1 ∈ S ∧ f e.2 ∈ T ∧ G.Adj e.1 e.2} =
      ∑ x ∈ Finset.univ.filter (fun v : Fin N => f v ∈ S),
        ((Finset.univ.filter (fun v : Fin N => f v ∈ T)).filter (G.Adj x)).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let X := Finset.univ.filter (fun v : Fin N => f v ∈ S)
  let Y := Finset.univ.filter (fun v : Fin N => f v ∈ T)
  have hsub : Finset.univ.filter (fun e : Fin N × Fin N => f e.1 ∈ S ∧ f e.2 ∈ T ∧ G.Adj e.1 e.2) =
      (X.sigma (fun x => Y.filter (G.Adj x))).map
        ⟨fun p => (p.1, p.2), fun a b h => by
          rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
          simp only [Prod.mk.injEq] at h
          exact Sigma.ext h.1 (heq_of_eq h.2)⟩ := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_sigma, X, Y]
    constructor
    · rintro ⟨hu, hv, huv⟩; exact ⟨⟨u, v⟩, ⟨hu, hv, huv⟩, rfl⟩
    · rintro ⟨⟨u', v'⟩, ⟨hu', hv', huv⟩, h⟩
      cases h
      exact ⟨hu', hv', huv⟩
  rw [hsub, Finset.card_map, Finset.card_sigma]

lemma natCard_edges_eq_sum_swap {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (f : Fin N → Fin 4) (S T : Finset (Fin 4)) :
    Nat.card {e : Fin N × Fin N // f e.1 ∈ S ∧ f e.2 ∈ T ∧ G.Adj e.1 e.2} =
      ∑ y ∈ Finset.univ.filter (fun v : Fin N => f v ∈ T),
        ((Finset.univ.filter (fun v : Fin N => f v ∈ S)).filter (G.Adj y)).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let X := Finset.univ.filter (fun v : Fin N => f v ∈ S)
  let Y := Finset.univ.filter (fun v : Fin N => f v ∈ T)
  have hsub : Finset.univ.filter (fun e : Fin N × Fin N => f e.1 ∈ S ∧ f e.2 ∈ T ∧ G.Adj e.1 e.2) =
      (Y.sigma (fun y => X.filter (G.Adj y))).map
        ⟨fun p => (p.2, p.1), fun a b h => by
          rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
          simp only [Prod.mk.injEq] at h
          exact Sigma.ext h.2 (heq_of_eq h.1)⟩ := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_sigma, X, Y]
    constructor
    · rintro ⟨hu, hv, huv⟩; exact ⟨⟨v, u⟩, ⟨hv, hu, huv.symm⟩, rfl⟩
    · rintro ⟨⟨v', u'⟩, ⟨hv', hu', hvu⟩, h⟩
      cases h
      exact ⟨hu', hv', hvu.symm⟩
  rw [hsub, Finset.card_map, Finset.card_sigma]

lemma bad_card_le_of_dense {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (X Y : Finset (Fin N)) (d : ℕ) (hd : 0 < d) (α : ℝ)
    (hα : α * (X.card : ℝ) * (Y.card : ℝ) ≤ (d : ℝ) * (d : ℝ))
    (hdense : (1 - α) * (X.card : ℝ) * (Y.card : ℝ) ≤
      ∑ x ∈ X, ((Y.filter (G.Adj x)).card : ℝ)) :
    (X.filter (fun x => d < (Y.filter (fun y => ¬ G.Adj x y)).card)).card ≤ d := by
  classical
  let bad := X.filter (fun x => d < (Y.filter (fun y => ¬ G.Adj x y)).card)
  have hpart : ∀ x ∈ X, (Y.filter (G.Adj x)).card + (Y.filter (fun y => ¬ G.Adj x y)).card = Y.card :=
    fun x _ => Finset.card_filter_add_card_filter_not (G.Adj x)
  have hsum_nat : (∑ x ∈ X, (Y.filter (G.Adj x)).card) +
      (∑ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card) = X.card * Y.card := by
    rw [← Finset.sum_add_distrib]
    calc ∑ x ∈ X, ((Y.filter (G.Adj x)).card + (Y.filter (fun y => ¬ G.Adj x y)).card)
        = ∑ _x ∈ X, Y.card := Finset.sum_congr rfl hpart
      _ = X.card * Y.card := by simp
  have hsum_real : (∑ x ∈ X, ((Y.filter (fun y => ¬ G.Adj x y)).card : ℝ)) ≤
      (d : ℝ) * (d : ℝ) := by
    have h1 : ((∑ x ∈ X, (Y.filter (G.Adj x)).card : ℕ) : ℝ) +
        ((∑ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card : ℕ) : ℝ) =
        (X.card : ℝ) * (Y.card : ℝ) := by exact_mod_cast hsum_nat
    push_cast at h1
    linarith
  have hmiss_nat : ∑ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card ≤ d * d := by
    exact_mod_cast hsum_real
  have hlow : bad.card * (d + 1) ≤ ∑ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card := by
    calc bad.card * (d + 1) = ∑ _x ∈ bad, (d + 1) := by simp
      _ ≤ ∑ x ∈ bad, (Y.filter (fun y => ¬ G.Adj x y)).card := by
        apply Finset.sum_le_sum
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  change bad.card ≤ d
  by_contra! h
  have hle : (d + 1) * (d + 1) ≤ d * d :=
    (Nat.mul_le_mul_right (d + 1) h).trans (hlow.trans hmiss_nat)
  nlinarith only [hle]

lemma miss_le_of_two_small {N : ℕ} (c : Fin 3 → SimpleGraph (Fin N)) [∀ i, DecidableRel (c i).Adj]
    (hc : (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c) (S : Finset (Fin N)) (x : Fin N) (hx : x ∉ S)
    (k0 k1 k2 : Fin 3) (h01 : k0 ≠ k1) (h02 : k0 ≠ k2) (h12 : k1 ≠ k2)
    (D : ℕ) (h1 : (S.filter ((c k1).Adj x)).card < D) (h2 : (S.filter ((c k2).Adj x)).card < D) :
    (S.filter (fun y => ¬ (c k0).Adj x y)).card ≤ 2 * D := by
  have hsub : S.filter (fun y => ¬ (c k0).Adj x y) ⊆
      S.filter ((c k1).Adj x) ∪ S.filter ((c k2).Adj x) := by
    intro y hy
    have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
    have hno0 : ¬ (c k0).Adj x y := (Finset.mem_filter.mp hy).2
    have hne : x ≠ y := fun h => hx (h ▸ hyS)
    have hedge : (⊤ : SimpleGraph (Fin N)).Adj x y := hne
    rw [hc.1, SimpleGraph.iSup_adj] at hedge
    obtain ⟨k, hk⟩ := hedge
    have hk_cases : k = k0 ∨ k = k1 ∨ k = k2 := by
      fin_cases k <;> fin_cases k0 <;> fin_cases k1 <;> fin_cases k2 <;> simp_all
    rcases hk_cases with rfl | rfl | rfl
    · exact (hno0 hk).elim
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyS, hk⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hyS, hk⟩)
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

set_option maxHeartbeats 4000000 in
theorem main :
    H1 → H2 →
    OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1.H1 := by
  classical
  intro h1 h2
  refine ⟨1 / 100000000, by norm_num, fun α hα_pos hα_le => ?_⟩
  filter_upwards [eventually_ge_atTop 20000] with n hn heven
  obtain ⟨m, hm_eq⟩ := heven
  have hn2m : n = 2 * m := by omega
  subst hn2m
  have hm_ge : 10000 ≤ m := by omega
  rw [show 2 * (2 * m) = 4 * m by omega]
  intro c hc f hcards hdense
  letI : ∀ i, DecidableRel (c i).Adj := fun i => Classical.decRel _
  let col : Fin 4 → Fin 4 → Fin 3 := fun j k =>
    if (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0) ∨ (j = 2 ∧ k = 3) ∨ (j = 3 ∧ k = 2) then 0
    else if (j = 0 ∧ k = 3) ∨ (j = 3 ∧ k = 0) ∨ (j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1) then 1
    else 2
  let W : Fin 4 → Finset (Fin (4 * m)) := fun j => Finset.univ.filter (fun v => f v = j)
  have hdisW : Pairwise (fun i j : Fin 4 => Disjoint (W i) (W j)) := by
    intro i j hij
    refine Finset.disjoint_left.mpr fun x hx hy => hij ?_
    exact (Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2
  let d : ℕ := m / 1000
  have hd_pos : 1 ≤ d := by dsimp [d]; omega
  have h100d : 100 * d ≤ m := by dsimp [d]; omega
  have h500d : 500 * d ≤ m := by dsimp [d]; omega
  have hW_sing (j : Fin 4) : Finset.univ.filter (fun v : Fin (4 * m) => f v ∈ ({j} : Finset (Fin 4))) = W j := by
    ext v; simp [W]
  have hW_low (j : Fin 4) : m - d ≤ (W j).card := by
    have h0 := hcards j
    rw [natCard_eq_filter_card] at h0
    push_cast at h0
    have hR : (m : ℝ) - (d : ℝ) ≤ ((W j).card : ℝ) := by
      have hdR : (m : ℝ) / 2000 ≤ (d : ℝ) := by
        have : m ≤ 2000 * d := by dsimp [d]; omega
        have : (m : ℝ) ≤ 2000 * (d : ℝ) := by exact_mod_cast this
        linarith
      have halpha : α * (m : ℝ) ≤ (1 / 100000000 : ℝ) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hα_le (Nat.cast_nonneg m)
      linarith only [h0, hdR, halpha, Nat.cast_nonneg (α := ℝ) m]
    have hN : m ≤ (W j).card + d := by exact_mod_cast (by linarith : (m : ℝ) ≤ ((W j).card : ℝ) + (d : ℝ))
    omega
  have hα_cap (X Y : Finset (Fin (4 * m))) : α * (X.card : ℝ) * (Y.card : ℝ) ≤ (d : ℝ) * (d : ℝ) := by
    have hX : (X.card : ℝ) ≤ 4 * (m : ℝ) := by exact_mod_cast (by simpa using Finset.card_le_univ X : X.card ≤ 4 * m)
    have hY : (Y.card : ℝ) ≤ 4 * (m : ℝ) := by exact_mod_cast (by simpa using Finset.card_le_univ Y : Y.card ≤ 4 * m)
    have hd_ge : (m : ℝ) / 2000 ≤ (d : ℝ) := by
      have : m ≤ 2000 * d := by dsimp [d]; omega
      have : (m : ℝ) ≤ 2000 * (d : ℝ) := by exact_mod_cast this
      linarith
    have h1' : α * (X.card : ℝ) * (Y.card : ℝ) ≤ (1 / 100000000 : ℝ) * (4 * (m : ℝ)) * (4 * (m : ℝ)) := by
      gcongr
    have h2' : (1 / 100000000 : ℝ) * (4 * (m : ℝ)) * (4 * (m : ℝ)) ≤ ((m : ℝ) / 2000) * ((m : ℝ) / 2000) := by
      linarith only [sq_nonneg (m : ℝ)]
    have h3' : ((m : ℝ) / 2000) * ((m : ℝ) / 2000) ≤ (d : ℝ) * (d : ℝ) :=
      mul_self_le_mul_self (by positivity) hd_ge
    exact h1'.trans (h2'.trans h3')
  have hdense_jk (j k : Fin 4) (hjk : j ≠ k) :
      (1 - α) * ((W j).card : ℝ) * ((W k).card : ℝ) ≤
        ∑ x ∈ W j, (((W k).filter ((c (col j k)).Adj x)).card : ℝ) := by
    fin_cases j <;> fin_cases k <;> try exact (hjk rfl).elim
    · have h := hdense 0 {0} {1} (by simp)
      rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum, hW_sing 0, hW_sing 1] at h
      push_cast at h
      simpa [col] using h
    · have h := hdense 2 {0} {2} (by simp)
      rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum, hW_sing 0, hW_sing 2] at h
      push_cast at h
      simpa [col] using h
    · have h := hdense 1 {0} {3} (by simp)
      rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum, hW_sing 0, hW_sing 3] at h
      push_cast at h
      simpa [col] using h
    · have h := hdense 0 {0} {1} (by simp)
      rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum_swap, hW_sing 0, hW_sing 1] at h
      push_cast at h
      rw [mul_right_comm (1 - α)] at h
      simpa [col] using h
    · have h := hdense 1 {1} {2} (by simp)
      rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum, hW_sing 1, hW_sing 2] at h
      push_cast at h
      simpa [col] using h
    · have h := hdense 2 {1} {3} (by simp)
      rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum, hW_sing 1, hW_sing 3] at h
      push_cast at h
      simpa [col] using h
    · have h := hdense 2 {0} {2} (by simp)
      rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum_swap, hW_sing 0, hW_sing 2] at h
      push_cast at h
      rw [mul_right_comm (1 - α)] at h
      simpa [col] using h
    · have h := hdense 1 {1} {2} (by simp)
      rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum_swap, hW_sing 1, hW_sing 2] at h
      push_cast at h
      rw [mul_right_comm (1 - α)] at h
      simpa [col] using h
    · have h := hdense 0 {2} {3} (by simp)
      rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum, hW_sing 2, hW_sing 3] at h
      push_cast at h
      simpa [col] using h
    · have h := hdense 1 {0} {3} (by simp)
      rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum_swap, hW_sing 0, hW_sing 3] at h
      push_cast at h
      rw [mul_right_comm (1 - α)] at h
      simpa [col] using h
    · have h := hdense 2 {1} {3} (by simp)
      rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum_swap, hW_sing 1, hW_sing 3] at h
      push_cast at h
      rw [mul_right_comm (1 - α)] at h
      simpa [col] using h
    · have h := hdense 0 {2} {3} (by simp)
      rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum_swap, hW_sing 2, hW_sing 3] at h
      push_cast at h
      rw [mul_right_comm (1 - α)] at h
      simpa [col] using h
  let B : Fin 4 → Finset (Fin (4 * m)) := fun j =>
    (W j).filter (fun x => ∀ k : Fin 4, j ≠ k → ((W k).filter (fun y => ¬ (c (col j k)).Adj x y)).card ≤ d)
  have hB_sub (j : Fin 4) : B j ⊆ W j := Finset.filter_subset _ _
  have hdisB : Pairwise (fun i j : Fin 4 => Disjoint (B i) (B j)) :=
    fun i j hij => (hdisW hij).mono (hB_sub i) (hB_sub j)
  have hB_card (j : Fin 4) : m - 4 * d ≤ (B j).card := by
    have hbad_sub : (W j) \ (B j) ⊆ (Finset.univ.erase j).biUnion
        (fun k => (W j).filter (fun x => d < ((W k).filter (fun y => ¬ (c (col j k)).Adj x y)).card)) := by
      intro x hx
      have hxW : x ∈ W j := (Finset.mem_sdiff.mp hx).1
      have hxnot : x ∉ B j := (Finset.mem_sdiff.mp hx).2
      have hex : ∃ k : Fin 4, j ≠ k ∧ d < ((W k).filter (fun y => ¬ (c (col j k)).Adj x y)).card := by
        by_contra hall; push_neg at hall
        exact hxnot (Finset.mem_filter.mpr ⟨hxW, hall⟩)
      obtain ⟨k, hjk, hlt⟩ := hex
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩,
        Finset.mem_filter.mpr ⟨hxW, hlt⟩⟩
    have hcard_bad : ((W j) \ (B j)).card ≤ 3 * d := by
      calc ((W j) \ (B j)).card
          ≤ ∑ k ∈ Finset.univ.erase j,
              ((W j).filter (fun x => d < ((W k).filter (fun y => ¬ (c (col j k)).Adj x y)).card)).card :=
            (Finset.card_le_card hbad_sub).trans Finset.card_biUnion_le
        _ ≤ ∑ _k ∈ Finset.univ.erase j, d := by
          apply Finset.sum_le_sum
          intro k hk
          have hjk : j ≠ k := (Finset.mem_erase.mp hk).1.symm
          exact bad_card_le_of_dense (c (col j k)) (W j) (W k) d hd_pos α (hα_cap _ _) (hdense_jk j k hjk)
        _ = 3 * d := by simp
    have hs := Finset.card_sdiff_add_card_eq_card (hB_sub j)
    have hWl := hW_low j
    omega
  have hB_miss (j k : Fin 4) (hjk : j ≠ k) (u : Fin (4 * m)) (hu : u ∈ B j) :
      ((B k).filter (fun v => ¬ (c (col j k)).Adj u v)).card ≤ d :=
    (Finset.card_le_card (Finset.filter_subset_filter _ (hB_sub k))).trans
      ((Finset.mem_filter.mp hu).2 k hjk)
  let core : Finset (Fin (4 * m)) := B 0 ∪ B 1 ∪ B 2 ∪ B 3
  let L : Finset (Fin (4 * m)) := Finset.univ \ core
  let H : Fin 3 → Finset (Fin (4 * m)) := fun i =>
    if i = 0 then L.filter (fun x => 20 * d ≤ ((B 0 ∪ B 1).filter ((c 0).Adj x)).card ∧
      20 * d ≤ ((B 2 ∪ B 3).filter ((c 0).Adj x)).card)
    else if i = 1 then L.filter (fun x => 20 * d ≤ ((B 0 ∪ B 3).filter ((c 1).Adj x)).card ∧
      20 * d ≤ ((B 1 ∪ B 2).filter ((c 1).Adj x)).card)
    else L.filter (fun x => 20 * d ≤ ((B 0 ∪ B 2).filter ((c 2).Adj x)).card ∧
      20 * d ≤ ((B 1 ∪ B 3).filter ((c 2).Adj x)).card)
  by_cases hH0 : 2 ≤ (H 0).card
  · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < (H 0).card)
    simp only [H, Fin.reduceEq, if_true, if_false] at hx hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    refine ⟨0, h1 m d (c 0) B x y (by omega) hd_pos h100d hdisB hB_card
      (hB_miss 0 1 (by decide)) (hB_miss 1 0 (by decide))
      (hB_miss 2 3 (by decide)) (hB_miss 3 2 (by decide)) hxy ?_
      hx'.2.1 hx'.2.2 hy'.2.1 hy'.2.2⟩
    intro j
    have hxnot : x ∉ core := (Finset.mem_sdiff.mp hx'.1).2
    have hynot : y ∉ core := (Finset.mem_sdiff.mp hy'.1).2
    fin_cases j <;> simp [core] at hxnot hynot ⊢ <;> tauto
  by_cases hH1 : 2 ≤ (H 1).card
  · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < (H 1).card)
    simp only [H, Fin.reduceEq, if_true, if_false] at hx hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    let B' : Fin 4 → Finset (Fin (4 * m)) := ![B 0, B 3, B 1, B 2]
    have hdisB' : Pairwise (fun i j : Fin 4 => Disjoint (B' i) (B' j)) := by
      intro i j hij; fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
      all_goals exact hdisB (by decide)
    have hB'card : ∀ j, m - 4 * d ≤ (B' j).card := by
      intro j; fin_cases j <;> exact hB_card _
    refine ⟨1, h1 m d (c 1) B' x y (by omega) hd_pos h100d hdisB' hB'card
      (hB_miss 0 3 (by decide)) (hB_miss 3 0 (by decide))
      (hB_miss 1 2 (by decide)) (hB_miss 2 1 (by decide)) hxy ?_
      hx'.2.1 hx'.2.2 hy'.2.1 hy'.2.2⟩
    intro j
    have hxnot : x ∉ core := (Finset.mem_sdiff.mp hx'.1).2
    have hynot : y ∉ core := (Finset.mem_sdiff.mp hy'.1).2
    fin_cases j <;> simp [core, B'] at hxnot hynot ⊢ <;> tauto
  by_cases hH2 : 2 ≤ (H 2).card
  · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < (H 2).card)
    simp only [H, Fin.reduceEq, if_true, if_false] at hx hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    let B' : Fin 4 → Finset (Fin (4 * m)) := ![B 0, B 2, B 1, B 3]
    have hdisB' : Pairwise (fun i j : Fin 4 => Disjoint (B' i) (B' j)) := by
      intro i j hij; fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
      all_goals exact hdisB (by decide)
    have hB'card : ∀ j, m - 4 * d ≤ (B' j).card := by
      intro j; fin_cases j <;> exact hB_card _
    refine ⟨2, h1 m d (c 2) B' x y (by omega) hd_pos h100d hdisB' hB'card
      (hB_miss 0 2 (by decide)) (hB_miss 2 0 (by decide))
      (hB_miss 1 3 (by decide)) (hB_miss 3 1 (by decide)) hxy ?_
      hx'.2.1 hx'.2.2 hy'.2.1 hy'.2.2⟩
    intro j
    have hxnot : x ∉ core := (Finset.mem_sdiff.mp hx'.1).2
    have hynot : y ∉ core := (Finset.mem_sdiff.mp hy'.1).2
    fin_cases j <;> simp [core, B'] at hxnot hynot ⊢ <;> tauto
  push_neg at hH0 hH1 hH2
  let L0 : Finset (Fin (4 * m)) := L \ (H 0 ∪ H 1 ∪ H 2)
  have halign : ∀ x ∈ L0, ∃ j : Fin 4, ∀ k : Fin 4, j ≠ k →
      ((B k).filter (fun y => ¬ (c (col j k)).Adj x y)).card ≤ 40 * d := by
    intro x hx
    have hxL : x ∈ L := (Finset.mem_sdiff.mp hx).1
    have hxnotH : x ∉ H 0 ∪ H 1 ∪ H 2 := (Finset.mem_sdiff.mp hx).2
    have hxnotB : ∀ j, x ∉ B j := by
      have hxnot : x ∉ core := (Finset.mem_sdiff.mp hxL).2
      intro j; fin_cases j <;> simp [core] at hxnot <;> tauto
    have hno0 : ((B 0 ∪ B 1).filter ((c 0).Adj x)).card < 20 * d ∨
        ((B 2 ∪ B 3).filter ((c 0).Adj x)).card < 20 * d := by
      by_contra h; push_neg at h
      exact hxnotH (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp only [H, Fin.reduceEq, if_true, if_false]; exact Finset.mem_filter.mpr ⟨hxL, h⟩)))
    have hno1 : ((B 0 ∪ B 3).filter ((c 1).Adj x)).card < 20 * d ∨
        ((B 1 ∪ B 2).filter ((c 1).Adj x)).card < 20 * d := by
      by_contra h; push_neg at h
      exact hxnotH (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp only [H, Fin.reduceEq, if_true, if_false]; exact Finset.mem_filter.mpr ⟨hxL, h⟩)))
    have hno2 : ((B 0 ∪ B 2).filter ((c 2).Adj x)).card < 20 * d ∨
        ((B 1 ∪ B 3).filter ((c 2).Adj x)).card < 20 * d := by
      by_contra h; push_neg at h
      exact hxnotH (Finset.mem_union_right _ (by simp only [H, Fin.reduceEq, if_true, if_false]; exact Finset.mem_filter.mpr ⟨hxL, h⟩))
    have hsub_deg (k : Fin 3) (j1 j2 : Fin 4) (h : ((B j1 ∪ B j2).filter ((c k).Adj x)).card < 20 * d) :
        ((B j1).filter ((c k).Adj x)).card < 20 * d ∧ ((B j2).filter ((c k).Adj x)).card < 20 * d :=
      ⟨lt_of_le_of_lt (Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_left)) h,
       lt_of_le_of_lt (Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_right)) h⟩
    have hcontra (j : Fin 4) (h0 : ((B j).filter ((c 0).Adj x)).card < 20 * d)
        (h1' : ((B j).filter ((c 1).Adj x)).card < 20 * d)
        (h2' : ((B j).filter ((c 2).Adj x)).card < 20 * d) : False := by
      have hcov : B j ⊆ (B j).filter ((c 0).Adj x) ∪ (B j).filter ((c 1).Adj x) ∪ (B j).filter ((c 2).Adj x) := by
        intro y hy
        have hne : x ≠ y := fun h => hxnotB j (h ▸ hy)
        have hedge : (⊤ : SimpleGraph (Fin (4 * m))).Adj x y := hne
        rw [hc.1, SimpleGraph.iSup_adj] at hedge
        obtain ⟨k, hk⟩ := hedge
        fin_cases k
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hy, hk⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy, hk⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy, hk⟩)
      have hsum := (Finset.card_le_card hcov).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
      have hBj := hB_card j
      omega
    rcases hno0 with h0a | h0b <;> rcases hno1 with h1a | h1b <;> rcases hno2 with h2a | h2b
    · exact (hcontra 0 (hsub_deg 0 0 1 h0a).1 (hsub_deg 1 0 3 h1a).1 (hsub_deg 2 0 2 h2a).1).elim
    · refine ⟨2, fun k hk => ?_⟩
      fin_cases k <;> try exact (hk rfl).elim
      · simpa [col, ← Nat.mul_assoc] using (miss_le_of_two_small c hc (B 0) x (hxnotB 0) 2 0 1 (by decide) (by decide) (by decide) (20 * d)
          (hsub_deg 0 0 1 h0a).1 (hsub_deg 1 0 3 h1a).1)
      · simpa [col, ← Nat.mul_assoc] using (miss_le_of_two_small c hc (B 1) x (hxnotB 1) 1 0 2 (by decide) (by decide) (by decide) (20 * d)
          (hsub_deg 0 0 1 h0a).2 (hsub_deg 2 1 3 h2b).1)
      · simpa [col, ← Nat.mul_assoc] using (miss_le_of_two_small c hc (B 3) x (hxnotB 3) 0 1 2 (by decide) (by decide) (by decide) (20 * d)
          (hsub_deg 1 0 3 h1a).2 (hsub_deg 2 1 3 h2b).2)
    · refine ⟨3, fun k hk => ?_⟩
      fin_cases k <;> try exact (hk rfl).elim
      · simpa [col, ← Nat.mul_assoc] using (miss_le_of_two_small c hc (B 0) x (hxnotB 0) 1 0 2 (by decide) (by decide) (by decide) (20 * d)
          (hsub_deg 0 0 1 h0a).1 (hsub_deg 2 0 2 h2a).1)
      · simpa [col, ← Nat.mul_assoc] using (miss_le_of_two_small c hc (B 1) x (hxnotB 1) 2 0 1 (by decide) (by decide) (by decide) (20 * d)
          (hsub_deg 0 0 1 h0a).2 (hsub_deg 1 1 2 h1b).1)
      · simpa [col, ← Nat.mul_assoc] using (miss_le_of_two_small c hc (B 2) x (hxnotB 2) 0 1 2 (by decide) (by decide) (by decide) (20 * d)
          (hsub_deg 1 1 2 h1b).2 (hsub_deg 2 0 2 h2a).2)
    · exact (hcontra 1 (hsub_deg 0 0 1 h0a).2 (hsub_deg 1 1 2 h1b).1 (hsub_deg 2 1 3 h2b).1).elim
    · refine ⟨1, fun k hk => ?_⟩
      fin_cases k <;> try exact (hk rfl).elim
      · simpa [col, ← Nat.mul_assoc] using (miss_le_of_two_small c hc (B 0) x (hxnotB 0) 0 1 2 (by decide) (by decide) (by decide) (20 * d)
          (hsub_deg 1 0 3 h1a).1 (hsub_deg 2 0 2 h2a).1)
      · simpa [col, ← Nat.mul_assoc] using (miss_le_of_two_small c hc (B 2) x (hxnotB 2) 1 0 2 (by decide) (by decide) (by decide) (20 * d)
          (hsub_deg 0 2 3 h0b).1 (hsub_deg 2 0 2 h2a).2)
      · simpa [col, ← Nat.mul_assoc] using (miss_le_of_two_small c hc (B 3) x (hxnotB 3) 2 0 1 (by decide) (by decide) (by decide) (20 * d)
          (hsub_deg 0 2 3 h0b).2 (hsub_deg 1 0 3 h1a).2)
    · exact (hcontra 3 (hsub_deg 0 2 3 h0b).2 (hsub_deg 1 0 3 h1a).2 (hsub_deg 2 1 3 h2b).2).elim
    · exact (hcontra 2 (hsub_deg 0 2 3 h0b).1 (hsub_deg 1 1 2 h1b).2 (hsub_deg 2 0 2 h2a).2).elim
    · refine ⟨0, fun k hk => ?_⟩
      fin_cases k <;> try exact (hk rfl).elim
      · simpa [col, ← Nat.mul_assoc] using (miss_le_of_two_small c hc (B 1) x (hxnotB 1) 0 1 2 (by decide) (by decide) (by decide) (20 * d)
          (hsub_deg 1 1 2 h1b).1 (hsub_deg 2 1 3 h2b).1)
      · simpa [col, ← Nat.mul_assoc] using (miss_le_of_two_small c hc (B 2) x (hxnotB 2) 2 0 1 (by decide) (by decide) (by decide) (20 * d)
          (hsub_deg 0 2 3 h0b).1 (hsub_deg 1 1 2 h1b).2)
      · simpa [col, ← Nat.mul_assoc] using (miss_le_of_two_small c hc (B 3) x (hxnotB 3) 1 0 2 (by decide) (by decide) (by decide) (20 * d)
          (hsub_deg 0 2 3 h0b).2 (hsub_deg 2 1 3 h2b).2)
  let cls : Fin (4 * m) → Fin 4 := fun x =>
    if hx : x ∈ L0 then Classical.choose (halign x hx) else 0
  let P : Fin 4 → Finset (Fin (4 * m)) := fun j => B j ∪ L0.filter (fun x => cls x = j)
  refine h2 m d c B P H (by omega) hd_pos h100d hc ?_ ?_ ?_ ?_ hB_miss ?_ ?_ ?_ ?_
  · intro i j hij
    refine Finset.disjoint_left.mpr fun x hxi hxj => ?_
    rcases Finset.mem_union.mp hxi with hBi | hLi <;> rcases Finset.mem_union.mp hxj with hBj | hLj
    · exact Finset.disjoint_left.mp (hdisB hij) hBi hBj
    · have hxnot : x ∉ core := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hLj).1).1).2
      fin_cases i <;> simp [core] at hxnot <;> tauto
    · have hxnot : x ∉ core := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hLi).1).1).2
      fin_cases j <;> simp [core] at hxnot <;> tauto
    · exact hij ((Finset.mem_filter.mp hLi).2.symm.trans (Finset.mem_filter.mp hLj).2)
  · intro j; exact ⟨Finset.subset_union_left, hB_card j⟩
  · intro i
    fin_cases i
    · exact Nat.lt_succ_iff.mp hH0
    · exact Nat.lt_succ_iff.mp hH1
    · exact Nat.lt_succ_iff.mp hH2
  · intro v
    by_cases hvc : v ∈ core
    · simp only [core, Finset.mem_union] at hvc
      rcases hvc with ((h0 | h1') | h2') | h3'
      · exact Or.inl ⟨0, Finset.mem_union_left _ h0⟩
      · exact Or.inl ⟨1, Finset.mem_union_left _ h1'⟩
      · exact Or.inl ⟨2, Finset.mem_union_left _ h2'⟩
      · exact Or.inl ⟨3, Finset.mem_union_left _ h3'⟩
    · have hvL : v ∈ L := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvc⟩
      by_cases hvH : v ∈ H 0 ∪ H 1 ∪ H 2
      · simp only [Finset.mem_union] at hvH
        rcases hvH with (h0 | h1') | h2'
        · exact Or.inr ⟨0, h0⟩
        · exact Or.inr ⟨1, h1'⟩
        · exact Or.inr ⟨2, h2'⟩
      · have hvL0 : v ∈ L0 := Finset.mem_sdiff.mpr ⟨hvL, hvH⟩
        exact Or.inl ⟨cls v, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvL0, rfl⟩)⟩
  · intro j k hjk u hu
    rcases Finset.mem_union.mp hu with huB | huL
    · exact (hB_miss j k hjk u huB).trans (by omega)
    · have huL0 : u ∈ L0 := (Finset.mem_filter.mp huL).1
      have hcls : cls u = j := (Finset.mem_filter.mp huL).2
      have hspec := Classical.choose_spec (halign u huL0)
      have heq : Classical.choose (halign u huL0) = j := by simpa [cls, huL0] using hcls
      rw [heq] at hspec
      exact hspec k hjk
  · intro x hx; simp only [H, Fin.reduceEq, if_true, if_false] at hx; exact (Finset.mem_filter.mp hx).2
  · intro x hx; simp only [H, Fin.reduceEq, if_true, if_false] at hx; exact (Finset.mem_filter.mp hx).2
  · intro x hx; simp only [H, Fin.reduceEq, if_true, if_false] at hx; exact (Finset.mem_filter.mp hx).2

end OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1_H1_R1
