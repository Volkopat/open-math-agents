import OMAReductions.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2_H1_R1

-- Reduction Erdos556.erdos_556.variants.benevides_skokan_large_even.R1.H3.R1
-- of step Erdos556.erdos_556.variants.benevides_skokan_large_even.R1.H3
-- Credit: @LordMike
-- Port of reductions/Erdos556.erdos_556.variants.benevides_skokan_large_even.R1.H3.R1.lean by its author onto the identical hypothesis statement Erdos556.erdos_556.variants.benevides_skokan_large_even.R2.H1.R1.H2.

/-!
# Reducing EC3 absorption (`R1.H3`) to three single-colour graph lemmas

We discharge the 3-colour vertex cleaning, pigeonhole classification, maximal red/blue
matching extraction inside `A'`, and all EC3 block-size arithmetic directly in `main`,
reducing `R1.H3` to three standalone single-colour graph lemmas:

* `H1`: Dense bipartite cycle with bounded exceptions (Hall's theorem, as in `R2.H2`).
* `H2`: Greedy matching-spliced dense bipartite cycle.
* `H3`: Green clique + dense bipartite alternating-path absorption.
-/

open Filter SimpleGraph Finset

namespace OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2_H1_R1_H2_R1

private lemma natCard_eq_filter_card {N : ℕ} (P : Fin N → Prop) [DecidablePred P] :
    Nat.card {v : Fin N // P v} = (Finset.univ.filter P).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

private lemma natCard_edges_eq_sum {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
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

private lemma natCard_edges_eq_sum_swap {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
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

private lemma bad_card_le_of_dense {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (X Y : Finset (Fin N)) (d : ℕ) (hd : 0 < d) (δ : ℝ)
    (hδ : δ * (X.card : ℝ) * (Y.card : ℝ) ≤ (d : ℝ) * (d : ℝ))
    (hdense : (1 - δ) * (X.card : ℝ) * (Y.card : ℝ) ≤
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
 
private lemma exists_maximal_matching {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) (K : ℕ) :
    (∃ u v : Fin K → V, Function.Injective u ∧ Function.Injective v ∧
      (∀ i, u i ∈ A ∧ v i ∈ A ∧ G.Adj (u i) (v i)) ∧ (∀ i j, u i ≠ v j)) ∨
    (∃ M ⊆ A, M.card ≤ 2 * (K - 1) ∧
      ∀ x ∈ A \ M, ∀ y ∈ A \ M, ¬ G.Adj x y) := by
  classical
  have haux : ∀ k : ℕ, k ≤ K →
      (∃ u v : Fin k → V, Function.Injective u ∧ Function.Injective v ∧
        (∀ i, u i ∈ A ∧ v i ∈ A ∧ G.Adj (u i) (v i)) ∧ (∀ i j, u i ≠ v j)) ∨
      (∃ M ⊆ A, M.card ≤ 2 * (K - 1) ∧ ∀ x ∈ A \ M, ∀ y ∈ A \ M, ¬ G.Adj x y) := by
    intro k
    induction k with
    | zero =>
      intro _
      left
      exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨u, v, hu, hv, huv, hdisj⟩ | hmax
      · let U : Finset V := Finset.univ.image u
        let W : Finset V := Finset.univ.image v
        let M : Finset V := U ∪ W
        have hMA : M ⊆ A := by
          intro z hz
          rcases Finset.mem_union.mp hz with h | h
          · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h; exact (huv i).1
          · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h; exact (huv i).2.1
        have hMcard : M.card ≤ 2 * k := by
          change (U ∪ W).card ≤ 2 * k
          have h1 := Finset.card_union_le U W
          have h2 : U.card ≤ k := (Finset.card_image_le).trans (by simp)
          have h3 : W.card ≤ k := (Finset.card_image_le).trans (by simp)
          omega
        by_cases hedge : ∃ x ∈ A \ M, ∃ y ∈ A \ M, G.Adj x y
        · obtain ⟨x, hx, y, hy, hxy⟩ := hedge
          have hxA : x ∈ A := (Finset.mem_sdiff.mp hx).1
          have hxM : x ∉ M := (Finset.mem_sdiff.mp hx).2
          have hyA : y ∈ A := (Finset.mem_sdiff.mp hy).1
          have hyM : y ∉ M := (Finset.mem_sdiff.mp hy).2
          have hne : x ≠ y := G.ne_of_adj hxy
          left
          refine ⟨Fin.snoc u x, Fin.snoc v y, ?_, ?_, ?_, ?_⟩
          · intro a b hab
            revert hab
            refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b <;> intro hab
            · rfl
            · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
              exact (hxM (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b', Finset.mem_univ _, hab.symm⟩))).elim
            · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
              exact (hxM (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a', Finset.mem_univ _, hab⟩))).elim
            · simp only [Fin.snoc_castSucc] at hab
              exact congrArg Fin.castSucc (hu hab)
          · intro a b hab
            revert hab
            refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b <;> intro hab
            · rfl
            · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
              exact (hyM (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b', Finset.mem_univ _, hab.symm⟩))).elim
            · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
              exact (hyM (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a', Finset.mem_univ _, hab⟩))).elim
            · simp only [Fin.snoc_castSucc] at hab
              exact congrArg Fin.castSucc (hv hab)
          · intro i
            refine Fin.lastCases ?_ (fun i' => ?_) i
            · simpa [Fin.snoc_last] using ⟨hxA, hyA, hxy⟩
            · simpa [Fin.snoc_castSucc] using huv i'
          · intro a b hab
            revert hab
            refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b <;> intro hab
            · simp only [Fin.snoc_last] at hab; exact hne hab
            · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
              exact hxM (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b', Finset.mem_univ _, hab.symm⟩))
            · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
              exact hyM (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a', Finset.mem_univ _, hab⟩))
            · simp only [Fin.snoc_castSucc] at hab
              exact hdisj a' b' hab
        · push_neg at hedge
          right
          exact ⟨M, hMA, by omega, hedge⟩
      · exact Or.inr hmax
  exact haux K le_rfl

/-- Single-colour dense bipartite cycle with bounded exceptions. -/
def H1 : Prop :=
  ∀ (m d : ℕ) (G : SimpleGraph (Fin (4 * m))) [DecidableRel G.Adj]
    (A B₀ B : Finset (Fin (4 * m))),
    2 ≤ m → 1 ≤ d → 100 * d ≤ m →
    Disjoint A B → B₀ ⊆ B →
    m + 10 * d ≤ A.card → m ≤ B.card → m ≤ B₀.card + m / 20 →
    (∀ x ∈ B₀, (A.filter (fun y => ¬ G.Adj x y)).card ≤ d) →
    (∀ x ∈ B, A.card ≤ 4 * (A.filter (G.Adj x)).card) →
    cycleGraph (2 * m) ⊑ G

/-- Single-colour matching-spliced dense bipartite cycle. -/
def H2 : Prop :=
  ∀ (m d : ℕ) (G : SimpleGraph (Fin (4 * m))) [DecidableRel G.Adj]
    (A B₀ : Finset (Fin (4 * m))),
    2 ≤ m → 1 ≤ d → 100 * d ≤ m →
    Disjoint A B₀ →
    B₀.card < m → m ≤ B₀.card + m / 20 →
    2 * m + 10 * d ≤ A.card + B₀.card →
    (∀ x ∈ B₀, (A.filter (fun y => ¬ G.Adj x y)).card ≤ d) →
    (∀ x ∈ A, (B₀.filter (fun y => ¬ G.Adj x y)).card ≤ d) →
    (∃ u v : Fin (2 * (m - B₀.card)) → Fin (4 * m),
      Function.Injective u ∧ Function.Injective v ∧
      (∀ i, u i ∈ A ∧ v i ∈ A ∧ G.Adj (u i) (v i)) ∧
      (∀ i j, u i ≠ v j)) →
    cycleGraph (2 * m) ⊑ G

/-- Single-colour clique with dense bipartite alternating-path absorption. -/
def H3 : Prop :=
  ∀ (m d : ℕ) (G : SimpleGraph (Fin (4 * m))) [DecidableRel G.Adj]
    (A Q D₀ D : Finset (Fin (4 * m))),
    2 ≤ m → 1 ≤ d → 100 * d ≤ m →
    Disjoint A Q → Disjoint A D → Disjoint Q D → D₀ ⊆ D →
    D.card ≤ D₀.card + 10 * d →
    (∀ x ∈ A, ∀ y ∈ A, x ≠ y → G.Adj x y) →
    9 * m ≤ 10 * A.card →
    2 * m ≤ A.card + Q.card + D.card →
    m + 10 * d ≤ A.card + Q.card →
    m + 10 * d ≤ A.card + D₀.card →
    (∀ q ∈ Q, A.card ≤ 3 * (A.filter (G.Adj q)).card ∧
      (D₀.filter (fun y => ¬ G.Adj q y)).card ≤ d) →
    (∀ x ∈ D₀, (Q.filter (fun y => ¬ G.Adj x y)).card ≤ d ∧
      (A.filter (fun y => ¬ G.Adj x y)).card ≤ d) →
    (∀ x ∈ D, A.card ≤ 4 * (A.filter (G.Adj x)).card) →
    cycleGraph (2 * m) ⊑ G

section

set_option maxHeartbeats 4000000 in
theorem main :
    H1 → H2 → H3 →
    OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2_H1_R1.H2 := by
  classical
  intro h1 h2 h3
  refine ⟨1 / 100, by norm_num, fun μ hμ_pos hμ_le => ?_⟩
  let δ₀ : ℝ := μ * μ / 10000000000
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (20000 / μ)
  filter_upwards [eventually_ge_atTop (2 * max M₀ 2000)] with n hn heven
  obtain ⟨m, hm_eq⟩ := heven
  have hn2m : n = 2 * m := by omega
  subst hn2m
  have hm_ge_2000 : 2000 ≤ m := by omega
  have hm_ge_M0 : M₀ ≤ m := by omega
  have hμm_upper : μ * (m : ℝ) ≤ (m : ℝ) / 100 := by
    calc
      μ * (m : ℝ) ≤ (1 / 100 : ℝ) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hμ_le (Nat.cast_nonneg m)
      _ = _ := by ring
  have hm_mu : (20000 : ℝ) < μ * (m : ℝ) := by
    have h1' : (20000 : ℝ) / μ < (m : ℝ) := lt_of_lt_of_le hM₀ (by exact_mod_cast hm_ge_M0)
    simpa only [mul_comm (m : ℝ) μ] using (div_lt_iff₀ hμ_pos).mp h1'
  rw [show 2 * (2 * m) = 4 * m by omega]
  intro δ hδ_pos hδ_le c hc f hsizes hdense
  letI : ∀ i, DecidableRel (c i).Adj := fun i => Classical.decRel _
  let W : Fin 4 → Finset (Fin (4 * m)) := fun j => Finset.univ.filter (fun v => f v = j)
  have hdisW : ∀ i j : Fin 4, i ≠ j → Disjoint (W i) (W j) := by
    intro i j hij
    refine Finset.disjoint_left.mpr fun x hx hy => hij ?_
    exact (Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2
  have hsumW : (W 0).card + (W 1).card + (W 2).card + (W 3).card = 4 * m := by
    have huniv : Finset.univ = W 0 ∪ W 1 ∪ W 2 ∪ W 3 := by
      ext v
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff, W]
      generalize f v = j
      fin_cases j <;> decide
    have h01 : Disjoint (W 0) (W 1) := hdisW 0 1 (by decide)
    have h01_2 : Disjoint (W 0 ∪ W 1) (W 2) :=
      Finset.disjoint_union_left.mpr ⟨hdisW 0 2 (by decide), hdisW 1 2 (by decide)⟩
    have h012_3 : Disjoint (W 0 ∪ W 1 ∪ W 2) (W 3) :=
      Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr
        ⟨hdisW 0 3 (by decide), hdisW 1 3 (by decide)⟩, hdisW 2 3 (by decide)⟩
    have hc4 : (Finset.univ : Finset (Fin (4 * m))).card = 4 * m := by simp
    rw [huniv, Finset.card_union_of_disjoint h012_3, Finset.card_union_of_disjoint h01_2,
      Finset.card_union_of_disjoint h01] at hc4
    exact hc4
  have ha_eq (j : Fin 4) : (Nat.card {v : Fin (4 * m) // f v = j} : ℝ) = ((W j).card : ℝ) := by
    rw [natCard_eq_filter_card]
  have hW_sing (j : Fin 4) : Finset.univ.filter (fun v : Fin (4 * m) => f v ∈ ({j} : Finset (Fin 4))) = W j := by
    ext v; simp [W]
  rcases hsizes with ⟨hmin012, ha3_low, hdom, ha03_up⟩
  simp only [ha_eq, Nat.cast_mul, Nat.cast_ofNat] at hmin012 ha3_low hdom ha03_up
  have h2m_div : ((2 * m : ℕ) : ℝ) / 2 = (m : ℝ) := by push_cast; ring
  have ha0_low : (1 - 4 / 5 * μ) * (m : ℝ) ≤ (W 0).card := by
    have := le_trans hmin012 (min_le_left _ _); linarith [h2m_div]
  have ha1_low : (1 - 4 / 5 * μ) * (m : ℝ) ≤ (W 1).card := by
    have := le_trans hmin012 (le_trans (min_le_right _ _) (min_le_left _ _)); linarith [h2m_div]
  have ha2_low : (1 - 4 / 5 * μ) * (m : ℝ) ≤ (W 2).card := by
    have := le_trans hmin012 (le_trans (min_le_right _ _) (min_le_right _ _)); linarith [h2m_div]
  have ha3_low' : μ * (m : ℝ) ≤ (W 3).card := by linarith [h2m_div]
  have ha0_ge1 : ((W 1).card : ℝ) + μ * (m : ℝ) ≤ (W 0).card := by
    have := le_max_left ((W 1).card : ℝ) (max ((W 2).card : ℝ) ((W 3).card : ℝ)); linarith [h2m_div]
  have ha0_ge2 : ((W 2).card : ℝ) + μ * (m : ℝ) ≤ (W 0).card := by
    have := le_trans (le_max_left ((W 2).card : ℝ) ((W 3).card : ℝ)) (le_max_right ((W 1).card : ℝ) _); linarith [h2m_div]
  have ha0_ge3 : ((W 3).card : ℝ) + μ * (m : ℝ) ≤ (W 0).card := by
    have := le_trans (le_max_right ((W 2).card : ℝ) ((W 3).card : ℝ)) (le_max_right ((W 1).card : ℝ) _); linarith [h2m_div]
  have ha03_up' : ((W 0).card : ℝ) + ((W 3).card : ℝ) ≤ (2 + 3 / 5 * μ) * (m : ℝ) := by
    have : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    linarith
  have ha12_low : (2 - 3 / 5 * μ) * (m : ℝ) ≤ ((W 1).card : ℝ) + ((W 2).card : ℝ) := by
    have hsumR : ((W 0).card : ℝ) + ((W 1).card : ℝ) + ((W 2).card : ℝ) + ((W 3).card : ℝ) = 4 * (m : ℝ) := by
      exact_mod_cast hsumW
    linarith
  let d : ℕ := Nat.floor (μ * (m : ℝ) / 1000)
  have hd_pos : 1 ≤ d := by
    have : (1 : ℝ) ≤ μ * (m : ℝ) / 1000 := by linarith
    apply Nat.le_floor
    exact_mod_cast this
  have hd_upper : (d : ℝ) ≤ μ * (m : ℝ) / 1000 := Nat.floor_le (by positivity)
  have hd_lower : μ * (m : ℝ) / 2000 ≤ (d : ℝ) := by
    have hlt := Nat.lt_floor_add_one (μ * (m : ℝ) / 1000)
    linarith
  have h100d : 100 * d ≤ m := by
    have : (100 * d : ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast this
  have hpair_dense (k : Fin 3) (i j : Fin 4)
      (hmem : (k, ({i} : Finset (Fin 4)), ({j} : Finset (Fin 4))) ∈
        ([(0, {0}, {1}), (0, {2}, {3}), (1, {0}, {3}), (1, {1}, {2}), (2, {0}, {2}), (2, {1}, {3})] :
          List (Fin 3 × Finset (Fin 4) × Finset (Fin 4)))) :
      (1 - δ) * ((W i).card : ℝ) * ((W j).card : ℝ) ≤
        ∑ x ∈ W i, (((W j).filter ((c k).Adj x)).card : ℝ) ∧
      (1 - δ) * ((W j).card : ℝ) * ((W i).card : ℝ) ≤
        ∑ y ∈ W j, (((W i).filter ((c k).Adj y)).card : ℝ) := by
    have h0 := hdense k {i} {j} hmem
    have h1 := h0
    rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum, hW_sing i, hW_sing j] at h0
    rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum_swap, hW_sing i, hW_sing j] at h1
    push_cast at h0 h1
    exact ⟨h0, by linarith⟩
  have hδ_cap (X Y : Finset (Fin (4 * m))) : δ * (X.card : ℝ) * (Y.card : ℝ) ≤ (d : ℝ) * (d : ℝ) := by
    have hX : (X.card : ℝ) ≤ 4 * (m : ℝ) := by exact_mod_cast (by simpa using Finset.card_le_univ X : X.card ≤ 4 * m)
    have hY : (Y.card : ℝ) ≤ 4 * (m : ℝ) := by exact_mod_cast (by simpa using Finset.card_le_univ Y : Y.card ≤ 4 * m)
    have h1 : δ * (X.card : ℝ) * (Y.card : ℝ) ≤ δ₀ * (4 * (m : ℝ)) * (4 * (m : ℝ)) := by
      gcongr
    have h2 : δ₀ * (4 * (m : ℝ)) * (4 * (m : ℝ)) ≤ (μ * (m : ℝ) / 2000) * (μ * (m : ℝ) / 2000) := by
      dsimp only [δ₀]; linarith only [sq_nonneg (μ * (m : ℝ))]
    have h3 : (μ * (m : ℝ) / 2000) * (μ * (m : ℝ) / 2000) ≤ (d : ℝ) * (d : ℝ) :=
      mul_self_le_mul_self (by positivity) hd_lower
    exact h1.trans (h2.trans h3)
  have hd01 := hpair_dense 0 0 1 (by simp)
  have hd13 := hpair_dense 1 0 3 (by simp)
  have hd22 := hpair_dense 2 0 2 (by simp)
  let A_bad1 := (W 0).filter (fun x => d < ((W 1).filter (fun y => ¬ (c 0).Adj x y)).card)
  let A_bad2 := (W 0).filter (fun x => d < ((W 2).filter (fun y => ¬ (c 2).Adj x y)).card)
  let A_bad3 := (W 0).filter (fun x => d < ((W 3).filter (fun y => ¬ (c 1).Adj x y)).card)
  have hAb1 : A_bad1.card ≤ d := bad_card_le_of_dense (c 0) (W 0) (W 1) d hd_pos δ (hδ_cap _ _) hd01.1
  have hAb2 : A_bad2.card ≤ d := bad_card_le_of_dense (c 2) (W 0) (W 2) d hd_pos δ (hδ_cap _ _) hd22.1
  have hAb3 : A_bad3.card ≤ d := bad_card_le_of_dense (c 1) (W 0) (W 3) d hd_pos δ (hδ_cap _ _) hd13.1
  let A' := (W 0) \ (A_bad1 ∪ A_bad2 ∪ A_bad3)
  have hA'_sub : A' ⊆ W 0 := Finset.sdiff_subset
  have hA'_card : (W 0).card ≤ A'.card + 3 * d := by
    have h1 := Finset.card_sdiff_add_card_inter (W 0) (A_bad1 ∪ A_bad2 ∪ A_bad3)
    change A'.card + _ = _ at h1
    have h2 : ((W 0) ∩ (A_bad1 ∪ A_bad2 ∪ A_bad3)).card ≤ (A_bad1 ∪ A_bad2 ∪ A_bad3).card :=
      Finset.card_le_card Finset.inter_subset_right
    have h3 := (Finset.card_union_le (A_bad1 ∪ A_bad2) A_bad3).trans
      (Nat.add_le_add_right (Finset.card_union_le A_bad1 A_bad2) _)
    omega
  let B₀ := (W 1).filter (fun x => ((W 0).filter (fun y => ¬ (c 0).Adj x y)).card ≤ d)
  let C₀ := (W 2).filter (fun x => ((W 0).filter (fun y => ¬ (c 2).Adj x y)).card ≤ d)
  let D₀ := (W 3).filter (fun x => ((W 0).filter (fun y => ¬ (c 1).Adj x y)).card ≤ d)
  have hB0_card : (W 1).card ≤ B₀.card + d := by
    have hbad := bad_card_le_of_dense (c 0) (W 1) (W 0) d hd_pos δ (hδ_cap _ _) hd01.2
    have hsum := Finset.card_filter_add_card_filter_not (s := W 1)
      (fun x => ((W 0).filter (fun y => ¬ (c 0).Adj x y)).card ≤ d)
    change B₀.card + _ = _ at hsum
    have hnot : ((W 1).filter (fun x => ¬ ((W 0).filter (fun y => ¬ (c 0).Adj x y)).card ≤ d)).card ≤ d := by
      simpa only [not_le] using hbad
    omega
  have hC0_card : (W 2).card ≤ C₀.card + d := by
    have hbad := bad_card_le_of_dense (c 2) (W 2) (W 0) d hd_pos δ (hδ_cap _ _) hd22.2
    have hsum := Finset.card_filter_add_card_filter_not (s := W 2)
      (fun x => ((W 0).filter (fun y => ¬ (c 2).Adj x y)).card ≤ d)
    change C₀.card + _ = _ at hsum
    have hnot : ((W 2).filter (fun x => ¬ ((W 0).filter (fun y => ¬ (c 2).Adj x y)).card ≤ d)).card ≤ d := by
      simpa only [not_le] using hbad
    omega
  have hD0_card : (W 3).card ≤ D₀.card + d := by
    have hbad := bad_card_le_of_dense (c 1) (W 3) (W 0) d hd_pos δ (hδ_cap _ _) hd13.2
    have hsum := Finset.card_filter_add_card_filter_not (s := W 3)
      (fun x => ((W 0).filter (fun y => ¬ (c 1).Adj x y)).card ≤ d)
    change D₀.card + _ = _ at hsum
    have hnot : ((W 3).filter (fun x => ¬ ((W 0).filter (fun y => ¬ (c 1).Adj x y)).card ≤ d)).card ≤ d := by
      simpa only [not_le] using hbad
    omega
  have hA'_ge_m : m + 100 * d ≤ A'.card := by
    have hR : (m : ℝ) + 100 * (d : ℝ) ≤ (A'.card : ℝ) := by
      have : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
      linarith
    exact_mod_cast hR
  let outA := Finset.univ \ A'
  let Ball := outA.filter (fun x => A'.card ≤ 3 * (A'.filter ((c 0).Adj x)).card)
  let Call := outA.filter (fun x => A'.card ≤ 3 * (A'.filter ((c 2).Adj x)).card)
  let Dall := outA.filter (fun x => A'.card ≤ 3 * (A'.filter ((c 1).Adj x)).card)
  have hB0_sub_Ball : B₀ ⊆ Ball := by
    intro x hx
    have hx1 : x ∈ W 1 := (Finset.mem_filter.mp hx).1
    have hxmiss : (A'.filter (fun y => ¬ (c 0).Adj x y)).card ≤ d :=
      (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hx).2
    have hpart := Finset.card_filter_add_card_filter_not (s := A') ((c 0).Adj x)
    have hxout : x ∈ outA := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun hxA => Finset.disjoint_left.mp (hdisW 0 1 (by decide)) (hA'_sub hxA) hx1⟩
    exact Finset.mem_filter.mpr ⟨hxout, by omega⟩
  have hC0_sub_Call : C₀ ⊆ Call := by
    intro x hx
    have hx2 : x ∈ W 2 := (Finset.mem_filter.mp hx).1
    have hxmiss : (A'.filter (fun y => ¬ (c 2).Adj x y)).card ≤ d :=
      (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hx).2
    have hpart := Finset.card_filter_add_card_filter_not (s := A') ((c 2).Adj x)
    have hxout : x ∈ outA := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun hxA => Finset.disjoint_left.mp (hdisW 0 2 (by decide)) (hA'_sub hxA) hx2⟩
    exact Finset.mem_filter.mpr ⟨hxout, by omega⟩
  have hD0_sub_Dall : D₀ ⊆ Dall := by
    intro x hx
    have hx3 : x ∈ W 3 := (Finset.mem_filter.mp hx).1
    have hxmiss : (A'.filter (fun y => ¬ (c 1).Adj x y)).card ≤ d :=
      (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hx).2
    have hpart := Finset.card_filter_add_card_filter_not (s := A') ((c 1).Adj x)
    have hxout : x ∈ outA := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun hxA => Finset.disjoint_left.mp (hdisW 0 3 (by decide)) (hA'_sub hxA) hx3⟩
    exact Finset.mem_filter.mpr ⟨hxout, by omega⟩
  have hB0_m20 : m ≤ B₀.card + m / 20 := by
    have hR : (m : ℝ) ≤ (B₀.card : ℝ) + (m : ℝ) / 25 := by
      have : ((W 1).card : ℝ) ≤ (B₀.card : ℝ) + (d : ℝ) := by exact_mod_cast hB0_card
      linarith
    have hN : 25 * m ≤ 25 * B₀.card + m := by exact_mod_cast (by linarith : 25 * (m : ℝ) ≤ 25 * (B₀.card : ℝ) + (m : ℝ))
    omega
  have hC0_m20 : m ≤ C₀.card + m / 20 := by
    have hR : (m : ℝ) ≤ (C₀.card : ℝ) + (m : ℝ) / 25 := by
      have : ((W 2).card : ℝ) ≤ (C₀.card : ℝ) + (d : ℝ) := by exact_mod_cast hC0_card
      linarith
    have hN : 25 * m ≤ 25 * C₀.card + m := by exact_mod_cast (by linarith : 25 * (m : ℝ) ≤ 25 * (C₀.card : ℝ) + (m : ℝ))
    omega
  by_cases hBall : m ≤ Ball.card
  · refine ⟨0, h1 m d (c 0) A' B₀ Ball (by omega) hd_pos h100d
      (Finset.disjoint_sdiff.mono_right (Finset.filter_subset _ _)) hB0_sub_Ball
      (by omega) hBall hB0_m20 ?_ ?_⟩
    · intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hx).2
    · intro x hx
      have := (Finset.mem_filter.mp hx).2; omega
  by_cases hCall : m ≤ Call.card
  · refine ⟨2, h1 m d (c 2) A' C₀ Call (by omega) hd_pos h100d
      (Finset.disjoint_sdiff.mono_right (Finset.filter_subset _ _)) hC0_sub_Call
      (by omega) hCall hC0_m20 ?_ ?_⟩
    · intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hx).2
    · intro x hx
      have := (Finset.mem_filter.mp hx).2; omega
  push_neg at hBall hCall
  have hB0_lt : B₀.card < m := lt_of_le_of_lt (Finset.card_le_card hB0_sub_Ball) hBall
  have hC0_lt : C₀.card < m := lt_of_le_of_lt (Finset.card_le_card hC0_sub_Call) hCall
  have hW1_le : (W 1).card ≤ m + d := by omega
  have hW2_le : (W 2).card ≤ m + d := by omega
  have ha0_ge_high : (1 + 7 / 10 * μ) * (m : ℝ) ≤ (W 0).card := by
    have : (1 - 3 / 10 * μ) * (m : ℝ) ≤ max ((W 1).card : ℝ) ((W 2).card : ℝ) := by
      rcases le_total ((W 1).card : ℝ) ((W 2).card : ℝ) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    rcases le_total ((W 1).card : ℝ) ((W 2).card : ℝ) with h | h
    · rw [max_eq_right h] at this; linarith
    · rw [max_eq_left h] at this; linarith
  have hA'B0_sum : 2 * m + 10 * d ≤ A'.card + B₀.card := by
    have hR : 2 * (m : ℝ) + 10 * (d : ℝ) ≤ (A'.card : ℝ) + (B₀.card : ℝ) := by
      have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
      have h2' : ((W 1).card : ℝ) ≤ (B₀.card : ℝ) + (d : ℝ) := by exact_mod_cast hB0_card
      have h3' : ((W 2).card : ℝ) ≤ (m : ℝ) + (d : ℝ) := by exact_mod_cast hW2_le
      linarith
    exact_mod_cast hR
  have hA'C0_sum : 2 * m + 10 * d ≤ A'.card + C₀.card := by
    have hR : 2 * (m : ℝ) + 10 * (d : ℝ) ≤ (A'.card : ℝ) + (C₀.card : ℝ) := by
      have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
      have h2' : ((W 2).card : ℝ) ≤ (C₀.card : ℝ) + (d : ℝ) := by exact_mod_cast hC0_card
      have h3' : ((W 1).card : ℝ) ≤ (m : ℝ) + (d : ℝ) := by exact_mod_cast hW1_le
      linarith
    exact_mod_cast hR
  rcases exists_maximal_matching (c 0) A' (2 * (m - B₀.card)) with hm0 | ⟨M₀, hM0_sub, hM0_card, hM0_max⟩
  · refine ⟨0, h2 m d (c 0) A' B₀ (by omega) hd_pos h100d
      (Finset.disjoint_left.mpr fun x hxA hxB =>
        Finset.disjoint_left.mp (hdisW 0 1 (by decide)) (hA'_sub hxA) (Finset.mem_filter.mp hxB).1)
      hB0_lt hB0_m20 hA'B0_sum ?_ ?_ hm0⟩
    · intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hx).2
    · intro x hx
      have hx_not : x ∉ A_bad1 := fun h => (Finset.mem_sdiff.mp hx).2
        (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      have hx0 : x ∈ W 0 := hA'_sub hx
      have hle : ((W 1).filter (fun y => ¬ (c 0).Adj x y)).card ≤ d := by
        by_contra hlt; push_neg at hlt
        exact hx_not (Finset.mem_filter.mpr ⟨hx0, hlt⟩)
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans hle
  rcases exists_maximal_matching (c 2) A' (2 * (m - C₀.card)) with hm2 | ⟨M₂, hM2_sub, hM2_card, hM2_max⟩
  · refine ⟨2, h2 m d (c 2) A' C₀ (by omega) hd_pos h100d
      (Finset.disjoint_left.mpr fun x hxA hxC =>
        Finset.disjoint_left.mp (hdisW 0 2 (by decide)) (hA'_sub hxA) (Finset.mem_filter.mp hxC).1)
      hC0_lt hC0_m20 hA'C0_sum ?_ ?_ hm2⟩
    · intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hx).2
    · intro x hx
      have hx_not : x ∉ A_bad2 := fun h => (Finset.mem_sdiff.mp hx).2
        (Finset.mem_union_left _ (Finset.mem_union_right _ h))
      have hx0 : x ∈ W 0 := hA'_sub hx
      have hle : ((W 2).filter (fun y => ¬ (c 2).Adj x y)).card ≤ d := by
        by_contra hlt; push_neg at hlt
        exact hx_not (Finset.mem_filter.mpr ⟨hx0, hlt⟩)
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans hle
  let M := M₀ ∪ M₂
  let A'' := A' \ M
  have hM_sub : M ⊆ A' := Finset.union_subset hM0_sub hM2_sub
  have hrBC : ((m - B₀.card : ℕ) : ℝ) + ((m - C₀.card : ℕ) : ℝ) ≤
      3 / 5 * μ * (m : ℝ) + 2 * (d : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hB0_lt), Nat.cast_sub (le_of_lt hC0_lt)]
    have hB : ((W 1).card : ℝ) ≤ (B₀.card : ℝ) + (d : ℝ) := by exact_mod_cast hB0_card
    have hC : ((W 2).card : ℝ) ≤ (C₀.card : ℝ) + (d : ℝ) := by exact_mod_cast hC0_card
    linarith only [hB, hC, ha12_low]
  have hBDeficit : ((m - B₀.card : ℕ) : ℝ) ≤ 3 / 5 * μ * (m : ℝ) + 2 * (d : ℝ) := by
    linarith only [hrBC, Nat.cast_nonneg (α := ℝ) (m - C₀.card)]
  have hCDeficit : ((m - C₀.card : ℕ) : ℝ) ≤ 3 / 5 * μ * (m : ℝ) + 2 * (d : ℝ) := by
    linarith only [hrBC, Nat.cast_nonneg (α := ℝ) (m - B₀.card)]
  have hM_card : (M.card : ℝ) ≤ 12 / 5 * μ * (m : ℝ) + 8 * (d : ℝ) := by
    have h1' : M.card ≤ 4 * (m - B₀.card) + 4 * (m - C₀.card) := by
      have hUnion : M.card ≤ M₀.card + M₂.card := Finset.card_union_le M₀ M₂
      omega
    have h2' : (M.card : ℝ) ≤ 4 * ((m - B₀.card : ℕ) : ℝ) + 4 * ((m - C₀.card : ℕ) : ℝ) := by
      exact_mod_cast h1'
    linarith only [h2', hrBC]
  have hA''_card_add : A''.card + M.card = A'.card := Finset.card_sdiff_add_card_eq_card hM_sub
  have hA''_90 : 9 * m ≤ 10 * A''.card := by
    have hR : 9 * (m : ℝ) ≤ 10 * (A''.card : ℝ) := by
      have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
      have h2' : (A''.card : ℝ) + (M.card : ℝ) = (A'.card : ℝ) := by exact_mod_cast hA''_card_add
      linarith
    exact_mod_cast hR
  let X₀ := M.filter (fun x => A''.card ≤ 3 * (A''.filter ((c 0).Adj x)).card)
  let X₂ := M.filter (fun x => A''.card ≤ 3 * (A''.filter ((c 2).Adj x)).card)
  let Q := M \ (X₀ ∪ X₂)
  by_cases hBX0 : m ≤ Ball.card + X₀.card
  · obtain ⟨X₀', hX0'_sub, hX0'_card⟩ := Finset.exists_subset_card_eq (show m - Ball.card ≤ X₀.card by omega)
    have hX0'_A' : X₀' ⊆ A' := hX0'_sub.trans ((Finset.filter_subset _ _).trans hM_sub)
    have hX0'_disj_A'' : Disjoint X₀' A'' :=
      Finset.disjoint_left.mpr fun x hx hA'' => (Finset.mem_sdiff.mp hA'').2
        (Finset.mem_filter.mp (hX0'_sub hx)).1
    have hdisj_BX : Disjoint Ball X₀' :=
      Finset.disjoint_left.mpr fun x hxB hxX => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hxB).1).2 (hX0'_A' hxX)
    have hArem_card : m + 10 * d ≤ (A' \ X₀').card := by
      have hsub := Finset.card_sdiff_add_card_eq_card hX0'_A'
      have hR : (m : ℝ) + 10 * (d : ℝ) ≤ ((A' \ X₀').card : ℝ) := by
        have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
        have h2' : ((A' \ X₀').card : ℝ) + (X₀'.card : ℝ) = (A'.card : ℝ) := by exact_mod_cast hsub
        have h3' : (X₀'.card : ℝ) ≤ ((m - B₀.card : ℕ) : ℝ) := by
          have : B₀.card ≤ Ball.card := Finset.card_le_card hB0_sub_Ball
          exact_mod_cast (show X₀'.card ≤ m - B₀.card by omega)
        have h4' : ((m - B₀.card : ℕ) : ℝ) ≤ 3 / 5 * μ * (m : ℝ) + 2 * (d : ℝ) := hBDeficit
        linarith
      exact_mod_cast hR
    refine ⟨0, h1 m d (c 0) (A' \ X₀') B₀ (Ball ∪ X₀') (by omega) hd_pos h100d
      (Finset.disjoint_union_right.mpr ⟨Finset.disjoint_sdiff.mono Finset.sdiff_subset (Finset.filter_subset _ _),
        Finset.sdiff_disjoint⟩)
      (hB0_sub_Ball.trans Finset.subset_union_left) hArem_card
      (by rw [Finset.card_union_of_disjoint hdisj_BX]; omega) hB0_m20 ?_ ?_⟩
    · intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.sdiff_subset.trans hA'_sub))).trans
        (Finset.mem_filter.mp hx).2
    · intro x hx
      rcases Finset.mem_union.mp hx with hxB | hxX
      · have hdeg := (Finset.mem_filter.mp hxB).2
        have hdiff : (A'.filter ((c 0).Adj x)).card ≤ ((A' \ X₀').filter ((c 0).Adj x)).card + X₀'.card := by
          have hsub : A'.filter ((c 0).Adj x) ⊆ (A' \ X₀').filter ((c 0).Adj x) ∪ X₀' := by
            intro y hy
            by_cases hyX : y ∈ X₀'
            · exact Finset.mem_union_right _ hyX
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
                ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hy).1, hyX⟩, (Finset.mem_filter.mp hy).2⟩)
          exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hsubA := Finset.card_sdiff_add_card_eq_card hX0'_A'
        have hX0'_small : 12 * X₀'.card ≤ A'.card := by
          have hR : 12 * (X₀'.card : ℝ) ≤ (A'.card : ℝ) := by
            have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
            have h2' : (X₀'.card : ℝ) ≤ ((m - B₀.card : ℕ) : ℝ) := by
              have : B₀.card ≤ Ball.card := Finset.card_le_card hB0_sub_Ball
              exact_mod_cast (show X₀'.card ≤ m - B₀.card by omega)
            have h3' : ((m - B₀.card : ℕ) : ℝ) ≤ 3 / 5 * μ * (m : ℝ) + 2 * (d : ℝ) := hBDeficit
            linarith
          exact_mod_cast hR
        omega
      · have hdeg := (Finset.mem_filter.mp (hX0'_sub hxX)).2
        have hA''_sub : A'' ⊆ A' \ X₀' := Finset.subset_sdiff.mpr ⟨Finset.sdiff_subset, hX0'_disj_A''.symm⟩
        have hmono : (A''.filter ((c 0).Adj x)).card ≤ ((A' \ X₀').filter ((c 0).Adj x)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ hA''_sub)
        have hA'le : 3 * (A' \ X₀').card ≤ 4 * A''.card := by
          have hR : 3 * ((A' \ X₀').card : ℝ) ≤ 4 * (A''.card : ℝ) := by
            have h1' : (A' \ X₀').card ≤ A'.card := Finset.card_le_card Finset.sdiff_subset
            have h2' : (A''.card : ℝ) + (M.card : ℝ) = (A'.card : ℝ) := by exact_mod_cast hA''_card_add
            have h3' : ((A' \ X₀').card : ℝ) ≤ (A'.card : ℝ) := by exact_mod_cast h1'
            have h4' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
            linarith
          exact_mod_cast hR
        omega
  by_cases hCX2 : m ≤ Call.card + X₂.card
  · obtain ⟨X₂', hX2'_sub, hX2'_card⟩ := Finset.exists_subset_card_eq (show m - Call.card ≤ X₂.card by omega)
    have hX2'_A' : X₂' ⊆ A' := hX2'_sub.trans ((Finset.filter_subset _ _).trans hM_sub)
    have hX2'_disj_A'' : Disjoint X₂' A'' :=
      Finset.disjoint_left.mpr fun x hx hA'' => (Finset.mem_sdiff.mp hA'').2
        (Finset.mem_filter.mp (hX2'_sub hx)).1
    have hdisj_CX : Disjoint Call X₂' :=
      Finset.disjoint_left.mpr fun x hxC hxX => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hxC).1).2 (hX2'_A' hxX)
    have hArem_card : m + 10 * d ≤ (A' \ X₂').card := by
      have hsub := Finset.card_sdiff_add_card_eq_card hX2'_A'
      have hR : (m : ℝ) + 10 * (d : ℝ) ≤ ((A' \ X₂').card : ℝ) := by
        have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
        have h2' : ((A' \ X₂').card : ℝ) + (X₂'.card : ℝ) = (A'.card : ℝ) := by exact_mod_cast hsub
        have h3' : (X₂'.card : ℝ) ≤ ((m - C₀.card : ℕ) : ℝ) := by
          have : C₀.card ≤ Call.card := Finset.card_le_card hC0_sub_Call
          exact_mod_cast (show X₂'.card ≤ m - C₀.card by omega)
        have h4' : ((m - C₀.card : ℕ) : ℝ) ≤ 3 / 5 * μ * (m : ℝ) + 2 * (d : ℝ) := hCDeficit
        linarith
      exact_mod_cast hR
    refine ⟨2, h1 m d (c 2) (A' \ X₂') C₀ (Call ∪ X₂') (by omega) hd_pos h100d
      (Finset.disjoint_union_right.mpr ⟨Finset.disjoint_sdiff.mono Finset.sdiff_subset (Finset.filter_subset _ _),
        Finset.sdiff_disjoint⟩)
      (hC0_sub_Call.trans Finset.subset_union_left) hArem_card
      (by rw [Finset.card_union_of_disjoint hdisj_CX]; omega) hC0_m20 ?_ ?_⟩
    · intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.sdiff_subset.trans hA'_sub))).trans
        (Finset.mem_filter.mp hx).2
    · intro x hx
      rcases Finset.mem_union.mp hx with hxC | hxX
      · have hdeg := (Finset.mem_filter.mp hxC).2
        have hdiff : (A'.filter ((c 2).Adj x)).card ≤ ((A' \ X₂').filter ((c 2).Adj x)).card + X₂'.card := by
          have hsub : A'.filter ((c 2).Adj x) ⊆ (A' \ X₂').filter ((c 2).Adj x) ∪ X₂' := by
            intro y hy
            by_cases hyX : y ∈ X₂'
            · exact Finset.mem_union_right _ hyX
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
                ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hy).1, hyX⟩, (Finset.mem_filter.mp hy).2⟩)
          exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hsubA := Finset.card_sdiff_add_card_eq_card hX2'_A'
        have hX2'_small : 12 * X₂'.card ≤ A'.card := by
          have hR : 12 * (X₂'.card : ℝ) ≤ (A'.card : ℝ) := by
            have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
            have h2' : (X₂'.card : ℝ) ≤ ((m - C₀.card : ℕ) : ℝ) := by
              have : C₀.card ≤ Call.card := Finset.card_le_card hC0_sub_Call
              exact_mod_cast (show X₂'.card ≤ m - C₀.card by omega)
            have h3' : ((m - C₀.card : ℕ) : ℝ) ≤ 3 / 5 * μ * (m : ℝ) + 2 * (d : ℝ) := hCDeficit
            linarith
          exact_mod_cast hR
        omega
      · have hdeg := (Finset.mem_filter.mp (hX2'_sub hxX)).2
        have hA''_sub : A'' ⊆ A' \ X₂' := Finset.subset_sdiff.mpr ⟨Finset.sdiff_subset, hX2'_disj_A''.symm⟩
        have hmono : (A''.filter ((c 2).Adj x)).card ≤ ((A' \ X₂').filter ((c 2).Adj x)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ hA''_sub)
        have hA'le : 3 * (A' \ X₂').card ≤ 4 * A''.card := by
          have hR : 3 * ((A' \ X₂').card : ℝ) ≤ 4 * (A''.card : ℝ) := by
            have h1' : (A' \ X₂').card ≤ A'.card := Finset.card_le_card Finset.sdiff_subset
            have h2' : (A''.card : ℝ) + (M.card : ℝ) = (A'.card : ℝ) := by exact_mod_cast hA''_card_add
            have h3' : ((A' \ X₂').card : ℝ) ≤ (A'.card : ℝ) := by exact_mod_cast h1'
            have h4' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
            linarith
          exact_mod_cast hR
        omega
  push_neg at hBX0 hCX2
  have houtA_cover : outA ⊆ Ball ∪ Call ∪ Dall := by
    intro x hx
    have hxA : x ∉ A' := (Finset.mem_sdiff.mp hx).2
    have hcov : A' ⊆ A'.filter ((c 0).Adj x) ∪ A'.filter ((c 2).Adj x) ∪ A'.filter ((c 1).Adj x) := by
      intro y hy
      have hne : x ≠ y := fun h => hxA (h ▸ hy)
      have hedge : (⊤ : SimpleGraph (Fin (4 * m))).Adj x y := hne
      rw [hc.1, SimpleGraph.iSup_adj] at hedge
      obtain ⟨k, hk⟩ := hedge
      fin_cases k
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hy, hk⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy, hk⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy, hk⟩))
    have hsum := (Finset.card_le_card hcov).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    by_cases h0 : A'.card ≤ 3 * (A'.filter ((c 0).Adj x)).card
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h0⟩))
    by_cases h2 : A'.card ≤ 3 * (A'.filter ((c 2).Adj x)).card
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h2⟩))
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, by omega⟩)
  have h4m_sum : A'.card + outA.card = 4 * m := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A')
    change outA.card + A'.card = _ at this
    simpa only [Nat.add_comm A'.card outA.card, Finset.card_univ, Fintype.card_fin] using this
  have hQ_card : A'.card ≤ A''.card + Q.card + X₀.card + X₂.card := by
    have h1' := Finset.card_sdiff_add_card_eq_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _) : X₀ ∪ X₂ ⊆ M)
    change Q.card + _ = _ at h1'
    have h2' := Finset.card_union_le X₀ X₂
    omega
  have htotal_green : 2 * m ≤ A''.card + Q.card + Dall.card := by
    have h1' := (Finset.card_le_card houtA_cover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    omega
  have hAQ_ge : m + 10 * d ≤ A''.card + Q.card := by
    have hR : (m : ℝ) + 10 * (d : ℝ) ≤ (A''.card : ℝ) + (Q.card : ℝ) := by
      have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
      have h2' : (A'.card : ℝ) ≤ (A''.card : ℝ) + (Q.card : ℝ) + (X₀.card : ℝ) + (X₂.card : ℝ) := by
        exact_mod_cast hQ_card
      have h3' : (X₀.card : ℝ) + (X₂.card : ℝ) ≤ ((m - B₀.card : ℕ) : ℝ) + ((m - C₀.card : ℕ) : ℝ) := by
        have hb : B₀.card ≤ Ball.card := Finset.card_le_card hB0_sub_Ball
        have hc' : C₀.card ≤ Call.card := Finset.card_le_card hC0_sub_Call
        exact_mod_cast (show X₀.card + X₂.card ≤ (m - B₀.card) + (m - C₀.card) by omega)
      linarith
    exact_mod_cast hR
  have hAD0_ge : m + 10 * d ≤ A''.card + D₀.card := by
    have hTotal : ((W 0).card : ℝ) + ((W 1).card : ℝ) +
        ((W 2).card : ℝ) + ((W 3).card : ℝ) = 4 * (m : ℝ) := by exact_mod_cast hsumW
    have hCleanA : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
    have hMatching : (A''.card : ℝ) + (M.card : ℝ) = (A'.card : ℝ) := by exact_mod_cast hA''_card_add
    have hW1 : ((W 1).card : ℝ) ≤ (m : ℝ) + (d : ℝ) := by exact_mod_cast hW1_le
    have hW2 : ((W 2).card : ℝ) ≤ (m : ℝ) + (d : ℝ) := by exact_mod_cast hW2_le
    have hCleanD : ((W 3).card : ℝ) ≤ (D₀.card : ℝ) + (d : ℝ) := by exact_mod_cast hD0_card
    have hR : (m : ℝ) + 10 * (d : ℝ) ≤ (A''.card : ℝ) + (D₀.card : ℝ) := by
      linarith only [hTotal, hCleanA, hMatching, hW1, hW2, hCleanD, hM_card, hd_upper, hμm_upper]
    exact_mod_cast hR
  have hDall_le : Dall.card ≤ D₀.card + 10 * d := by
    have hsub : Dall \ D₀ ⊆ (W 0 \ A') ∪ (W 1 \ B₀) ∪ (W 2 \ C₀) ∪ (W 3 \ D₀) := by
      intro x hx
      have hxDall : x ∈ Dall := (Finset.mem_sdiff.mp hx).1
      have hxnotD0 : x ∉ D₀ := (Finset.mem_sdiff.mp hx).2
      have hxout : x ∈ outA := (Finset.mem_filter.mp hxDall).1
      have hxnotA' : x ∉ A' := (Finset.mem_sdiff.mp hxout).2
      have hxdeg1 : A'.card ≤ 3 * (A'.filter ((c 1).Adj x)).card := (Finset.mem_filter.mp hxDall).2
      have hcase : x ∈ W 0 ∨ x ∈ W 1 ∨ x ∈ W 2 ∨ x ∈ W 3 := by
        simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
        generalize f x = j
        fin_cases j <;> decide
      rcases hcase with hx0 | hx1 | hx2 | hx3
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx0, hxnotA'⟩)))
      · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx1, fun hxB0 => ?_⟩)))
        have hmiss : (A'.filter (fun y => ¬ (c 0).Adj x y)).card ≤ d :=
          (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hxB0).2
        have hdisj01 : A'.filter ((c 1).Adj x) ⊆ A'.filter (fun y => ¬ (c 0).Adj x y) := by
          intro y hy
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, fun h0 =>
            SimpleGraph.disjoint_left.mp (hc.2 0 1 (by decide)) x y h0 (Finset.mem_filter.mp hy).2⟩
        have := Finset.card_le_card hdisj01
        omega
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx2, fun hxC0 => ?_⟩))
        have hmiss : (A'.filter (fun y => ¬ (c 2).Adj x y)).card ≤ d :=
          (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hxC0).2
        have hdisj21 : A'.filter ((c 1).Adj x) ⊆ A'.filter (fun y => ¬ (c 2).Adj x y) := by
          intro y hy
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, fun h2 =>
            SimpleGraph.disjoint_left.mp (hc.2 2 1 (by decide)) x y h2 (Finset.mem_filter.mp hy).2⟩
        have := Finset.card_le_card hdisj21
        omega
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx3, hxnotD0⟩)
    have h1' := Finset.card_sdiff_add_card_eq_card hD0_sub_Dall
    have h2' := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
    have hs0 := Finset.card_sdiff_add_card_eq_card hA'_sub
    have hs1 := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ (W 1) : B₀ ⊆ W 1)
    have hs2 := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ (W 2) : C₀ ⊆ W 2)
    have hs3 := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ (W 3) : D₀ ⊆ W 3)
    change (W 1 \ B₀).card + B₀.card = (W 1).card at hs1
    change (W 2 \ C₀).card + C₀.card = (W 2).card at hs2
    change (W 3 \ D₀).card + D₀.card = (W 3).card at hs3
    omega
  refine ⟨1, h3 m d (c 1) A'' Q D₀ Dall (by omega) hd_pos h100d
    (Finset.sdiff_disjoint.mono_right Finset.sdiff_subset)
    (Finset.disjoint_sdiff.mono Finset.sdiff_subset (Finset.filter_subset _ _))
    (Finset.disjoint_sdiff.mono (Finset.sdiff_subset.trans hM_sub) (Finset.filter_subset _ _))
    hD0_sub_Dall hDall_le ?_ hA''_90 htotal_green hAQ_ge hAD0_ge ?_ ?_ ?_⟩
  · intro x hx y hy hne
    have hxM0 : x ∈ A' \ M₀ := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
      fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ h)⟩
    have hyM0 : y ∈ A' \ M₀ := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1,
      fun h => (Finset.mem_sdiff.mp hy).2 (Finset.mem_union_left _ h)⟩
    have hxM2 : x ∈ A' \ M₂ := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
      fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_right _ h)⟩
    have hyM2 : y ∈ A' \ M₂ := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1,
      fun h => (Finset.mem_sdiff.mp hy).2 (Finset.mem_union_right _ h)⟩
    have hno0 : ¬ (c 0).Adj x y := hM0_max x hxM0 y hyM0
    have hno2 : ¬ (c 2).Adj x y := hM2_max x hxM2 y hyM2
    have hedge : (⊤ : SimpleGraph (Fin (4 * m))).Adj x y := hne
    rw [hc.1, SimpleGraph.iSup_adj] at hedge
    obtain ⟨k, hk⟩ := hedge
    fin_cases k
    · exact (hno0 hk).elim
    · exact hk
    · exact (hno2 hk).elim
  · intro q hq
    have hqM : q ∈ M := (Finset.mem_sdiff.mp hq).1
    have hqnot : q ∉ X₀ ∪ X₂ := (Finset.mem_sdiff.mp hq).2
    have hqA' : q ∈ A' := hM_sub hqM
    have hqnotA'' : q ∉ A'' := fun h => (Finset.mem_sdiff.mp h).2 hqM
    have hcov : A'' ⊆ A''.filter ((c 0).Adj q) ∪ A''.filter ((c 2).Adj q) ∪ A''.filter ((c 1).Adj q) := by
      intro y hy
      have hne : q ≠ y := fun h => hqnotA'' (h ▸ hy)
      have hedge : (⊤ : SimpleGraph (Fin (4 * m))).Adj q y := hne
      rw [hc.1, SimpleGraph.iSup_adj] at hedge
      obtain ⟨k, hk⟩ := hedge
      fin_cases k
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hy, hk⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy, hk⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy, hk⟩))
    have hsum := (Finset.card_le_card hcov).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    have h0lt : 3 * (A''.filter ((c 0).Adj q)).card < A''.card := by
      by_contra hge; push_neg at hge
      exact hqnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hqM, hge⟩))
    have h2lt : 3 * (A''.filter ((c 2).Adj q)).card < A''.card := by
      by_contra hge; push_neg at hge
      exact hqnot (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hqM, hge⟩))
    have hqnot3 : q ∉ A_bad3 := fun h => (Finset.mem_sdiff.mp hqA').2 (Finset.mem_union_right _ h)
    have hqmiss : ((W 3).filter (fun y => ¬ (c 1).Adj q y)).card ≤ d := by
      by_contra hlt; push_neg at hlt
      exact hqnot3 (Finset.mem_filter.mpr ⟨hA'_sub hqA', hlt⟩)
    exact ⟨by omega, (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans hqmiss⟩
  · intro x hx
    have hxmiss : ((W 0).filter (fun y => ¬ (c 1).Adj x y)).card ≤ d := (Finset.mem_filter.mp hx).2
    exact ⟨(Finset.card_le_card (Finset.filter_subset_filter _ ((Finset.sdiff_subset.trans hM_sub).trans hA'_sub))).trans hxmiss,
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.sdiff_subset.trans hA'_sub))).trans hxmiss⟩
  · intro x hx
    have hdeg := (Finset.mem_filter.mp hx).2
    have hdiff : (A'.filter ((c 1).Adj x)).card ≤ (A''.filter ((c 1).Adj x)).card + M.card := by
      have hsub : A'.filter ((c 1).Adj x) ⊆ A''.filter ((c 1).Adj x) ∪ M := by
        intro y hy
        by_cases hyM : y ∈ M
        · exact Finset.mem_union_right _ hyM
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hy).1, hyM⟩, (Finset.mem_filter.mp hy).2⟩)
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hMsmall : 12 * M.card ≤ A''.card := by
      have hR : 12 * (M.card : ℝ) ≤ (A''.card : ℝ) := by
        have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
        have h2' : (A''.card : ℝ) + (M.card : ℝ) = (A'.card : ℝ) := by exact_mod_cast hA''_card_add
        linarith
      exact_mod_cast hR
    omega

end

end OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2_H1_R1_H2_R1
