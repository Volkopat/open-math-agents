import OMAReductions.R_Erdos626_erdos_626_variants_h_even_conjecture_R1_H2_R1

-- Step Erdos626.erdos_626.variants.h_even_conjecture.R1.H2.R1.H1: hypothesis H1 of reduction Erdos626.erdos_626.variants.h_even_conjecture.R1.H2.R1
-- Credit: @KevinBigham

/-!
# Proof of `Erdos626.erdos_626.variants.h_even_conjecture.R1.H2.R1.H1`

We prove that for every `ε > 0` and all sufficiently large `n`, there exists a graph on `Fin n`
with girth strictly greater than `4` (no 3-cycles and no 4-cycles) and chromatic number at least
`n ^ (1 / 3 - ε)`, following the Krivelevich (1995) / Spencer (1977) method of deleting a maximal
edge-disjoint collection of short cycles from the Erdős–Rényi random graph `G(n, p)` with
`p = n ^ (-2 / 3 - δ)`.
-/

namespace Erdos626H4Lower

open Finset Filter SimpleGraph
open scoped BigOperators Classical

/- ## Section 1: Finite product probability weight on subsets -/

private noncomputable def binomWeight {α : Type*} [DecidableEq α]
    (U : Finset α) (p : ℝ) (E : Finset α) : ℝ :=
  p ^ E.card * (1 - p) ^ (U.card - E.card)

private lemma binomWeight_nonneg {α : Type*} [DecidableEq α]
    {U E : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binomWeight U p E := by
  unfold binomWeight
  have h1 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  positivity

private lemma powerset_insert_disjoint {α : Type*} [DecidableEq α]
    {a : α} {U : Finset α} (ha : a ∉ U) :
    Disjoint U.powerset (U.powerset.image (insert a)) := by
  rw [Finset.disjoint_left]
  intro E hE1 hE2
  obtain ⟨E', _, rfl⟩ := Finset.mem_image.mp hE2
  exact ha ((Finset.mem_powerset.mp hE1) (Finset.mem_insert_self a E'))

private lemma powerset_insert_eq {α : Type*} [DecidableEq α]
    {a : α} {U : Finset α} :
    (insert a U).powerset = U.powerset ∪ U.powerset.image (insert a) := by
  ext E
  simp only [Finset.mem_powerset, Finset.mem_union, Finset.mem_image]
  constructor
  · intro hE
    by_cases haE : a ∈ E
    · right
      refine ⟨E.erase a, ?_, Finset.insert_erase haE⟩
      intro x hx
      obtain ⟨hne, hxE⟩ := Finset.mem_erase.mp hx
      exact (Finset.mem_insert.mp (hE hxE)).resolve_left hne
    · left
      intro x hx
      rcases Finset.mem_insert.mp (hE hx) with rfl | hxU
      · exact (haE hx).elim
      · exact hxU
  · rintro (hE | ⟨E', hE', rfl⟩)
    · exact hE.trans (Finset.subset_insert a U)
    · exact Finset.insert_subset_insert a hE'

private lemma sum_binomWeight_eq_one {α : Type*} [DecidableEq α]
    (U : Finset α) (p : ℝ) :
    ∑ E ∈ U.powerset, binomWeight U p E = 1 := by
  induction U using Finset.induction with
  | empty =>
    simp [binomWeight]
  | insert a U ha ih =>
    rw [powerset_insert_eq, Finset.sum_union (powerset_insert_disjoint ha)]
    have h1 :
        ∑ E ∈ U.powerset, binomWeight (insert a U) p E =
        (1 - p) * ∑ E ∈ U.powerset, binomWeight U p E := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E hE
      have hEU : E ⊆ U := Finset.mem_powerset.mp hE
      have hle : E.card ≤ U.card := Finset.card_le_card hEU
      unfold binomWeight
      rw [Finset.card_insert_of_notMem ha, Nat.succ_sub hle, pow_succ]
      ring
    have h2 :
        ∑ E ∈ U.powerset.image (insert a), binomWeight (insert a U) p E =
        p * ∑ E ∈ U.powerset, binomWeight U p E := by
      have hinj : ∀ E₁ ∈ U.powerset, ∀ E₂ ∈ U.powerset,
          insert a E₁ = insert a E₂ → E₁ = E₂ := by
        intro E₁ h1' E₂ h2' heq
        have ha1 : a ∉ E₁ := fun h => ha (Finset.mem_powerset.mp h1' h)
        have ha2 : a ∉ E₂ := fun h => ha (Finset.mem_powerset.mp h2' h)
        have := congrArg (fun s => Finset.erase s a) heq
        simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
      rw [Finset.sum_image (fun E₁ h1' E₂ h2' h =>
        hinj E₁ (Finset.mem_coe.mp h1') E₂ (Finset.mem_coe.mp h2') h), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E hE
      have haE : a ∉ E := fun h => ha (Finset.mem_powerset.mp hE h)
      unfold binomWeight
      rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haE,
        Nat.succ_sub_succ, pow_succ]
      ring
    rw [h1, h2, ih]
    ring

private lemma sum_binomWeight_superset {α : Type*} [DecidableEq α]
    (U : Finset α) (p : ℝ) :
    ∀ F : Finset α, F ⊆ U →
      ∑ E ∈ U.powerset.filter (fun E => F ⊆ E), binomWeight U p E = p ^ F.card := by
  induction U using Finset.induction with
  | empty =>
    intro F hF
    have hF0 : F = ∅ := Finset.subset_empty.mp hF
    subst hF0
    simp [binomWeight]
  | insert a U ha ih =>
    intro F hF
    rw [powerset_insert_eq, Finset.filter_union,
      Finset.sum_union (Finset.disjoint_filter_filter (powerset_insert_disjoint ha))]
    by_cases haF : a ∈ F
    · have hleft : (U.powerset.filter (fun E => F ⊆ E)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro E hE
        obtain ⟨hEU, hFE⟩ := Finset.mem_filter.mp hE
        exact ha (Finset.mem_powerset.mp hEU (hFE haF))
      rw [hleft, Finset.sum_empty, zero_add]
      have hF' : F.erase a ⊆ U := by
        intro x hx
        obtain ⟨hne, hxF⟩ := Finset.mem_erase.mp hx
        exact (Finset.mem_insert.mp (hF hxF)).resolve_left hne
      have hfilt :
          (U.powerset.image (insert a)).filter (fun E => F ⊆ E) =
          (U.powerset.filter (fun E => F.erase a ⊆ E)).image (insert a) := by
        ext E
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_powerset]
        constructor
        · rintro ⟨⟨E', hE'U, rfl⟩, hFE⟩
          refine ⟨E', ⟨hE'U, ?_⟩, rfl⟩
          intro x hx
          obtain ⟨hne, hxF⟩ := Finset.mem_erase.mp hx
          exact (Finset.mem_insert.mp (hFE hxF)).resolve_left hne
        · rintro ⟨E', ⟨hE'U, hF'E'⟩, rfl⟩
          refine ⟨⟨E', hE'U, rfl⟩, ?_⟩
          intro x hx
          by_cases hxa : x = a
          · subst hxa; exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hF'E' (Finset.mem_erase.mpr ⟨hxa, hx⟩))
      rw [hfilt]
      have hinj : ∀ E₁ ∈ U.powerset.filter (fun E => F.erase a ⊆ E),
          ∀ E₂ ∈ U.powerset.filter (fun E => F.erase a ⊆ E),
          insert a E₁ = insert a E₂ → E₁ = E₂ := by
        intro E₁ h1' E₂ h2' heq
        have ha1 : a ∉ E₁ := fun h => ha (Finset.mem_powerset.mp (Finset.mem_filter.mp h1').1 h)
        have ha2 : a ∉ E₂ := fun h => ha (Finset.mem_powerset.mp (Finset.mem_filter.mp h2').1 h)
        have := congrArg (fun s => Finset.erase s a) heq
        simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
      rw [Finset.sum_image (fun E₁ h1' E₂ h2' h =>
        hinj E₁ (Finset.mem_coe.mp h1') E₂ (Finset.mem_coe.mp h2') h)]
      have hterm :
          ∑ E ∈ U.powerset.filter (fun E => F.erase a ⊆ E), binomWeight (insert a U) p (insert a E) =
          p * ∑ E ∈ U.powerset.filter (fun E => F.erase a ⊆ E), binomWeight U p E := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro E hE
        have haE : a ∉ E := fun h => ha (Finset.mem_powerset.mp (Finset.mem_filter.mp hE).1 h)
        unfold binomWeight
        rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haE,
          Nat.succ_sub_succ, pow_succ]
        ring
      rw [hterm, ih (F.erase a) hF']
      have hcard : F.card = (F.erase a).card + 1 := (Finset.card_erase_add_one haF).symm
      rw [hcard, pow_succ]
      ring
    · have hFU : F ⊆ U := by
        intro x hx
        rcases Finset.mem_insert.mp (hF hx) with rfl | hxU
        · exact (haF hx).elim
        · exact hxU
      have h1 :
          ∑ E ∈ U.powerset.filter (fun E => F ⊆ E), binomWeight (insert a U) p E =
          (1 - p) * ∑ E ∈ U.powerset.filter (fun E => F ⊆ E), binomWeight U p E := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro E hE
        have hle : E.card ≤ U.card := Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hE).1)
        unfold binomWeight
        rw [Finset.card_insert_of_notMem ha, Nat.succ_sub hle, pow_succ]
        ring
      have hfilt :
          (U.powerset.image (insert a)).filter (fun E => F ⊆ E) =
          (U.powerset.filter (fun E => F ⊆ E)).image (insert a) := by
        ext E
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_powerset]
        constructor
        · rintro ⟨⟨E', hE'U, rfl⟩, hFE⟩
          refine ⟨E', ⟨hE'U, ?_⟩, rfl⟩
          intro x hx
          rcases Finset.mem_insert.mp (hFE hx) with rfl | hxE'
          · exact (haF hx).elim
          · exact hxE'
        · rintro ⟨E', ⟨hE'U, hFE'⟩, rfl⟩
          exact ⟨⟨E', hE'U, rfl⟩, hFE'.trans (Finset.subset_insert a E')⟩
      rw [h1, hfilt]
      have hinj : ∀ E₁ ∈ U.powerset.filter (fun E => F ⊆ E),
          ∀ E₂ ∈ U.powerset.filter (fun E => F ⊆ E),
          insert a E₁ = insert a E₂ → E₁ = E₂ := by
        intro E₁ h1' E₂ h2' heq
        have ha1 : a ∉ E₁ := fun h => ha (Finset.mem_powerset.mp (Finset.mem_filter.mp h1').1 h)
        have ha2 : a ∉ E₂ := fun h => ha (Finset.mem_powerset.mp (Finset.mem_filter.mp h2').1 h)
        have := congrArg (fun s => Finset.erase s a) heq
        simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
      rw [Finset.sum_image (fun E₁ h1' E₂ h2' h =>
        hinj E₁ (Finset.mem_coe.mp h1') E₂ (Finset.mem_coe.mp h2') h)]
      have h2 :
          ∑ E ∈ U.powerset.filter (fun E => F ⊆ E), binomWeight (insert a U) p (insert a E) =
          p * ∑ E ∈ U.powerset.filter (fun E => F ⊆ E), binomWeight U p E := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro E hE
        have haE : a ∉ E := fun h => ha (Finset.mem_powerset.mp (Finset.mem_filter.mp hE).1 h)
        unfold binomWeight
        rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haE,
          Nat.succ_sub_succ, pow_succ]
        ring
      rw [h2, ih F hFU]
      ring

private lemma sum_binomWeight_pow_inter {α : Type*} [DecidableEq α]
    (U : Finset α) (p r : ℝ) :
    ∀ M : Finset α, M ⊆ U →
      ∑ E ∈ U.powerset, binomWeight U p E * r ^ (E ∩ M).card =
        (1 - p + p * r) ^ M.card := by
  induction U using Finset.induction with
  | empty =>
    intro M hM
    have hM0 : M = ∅ := Finset.subset_empty.mp hM
    subst hM0
    simp [binomWeight]
  | insert a U ha ih =>
    intro M hM
    rw [powerset_insert_eq, Finset.sum_union (powerset_insert_disjoint ha)]
    have hinj : ∀ E₁ ∈ U.powerset, ∀ E₂ ∈ U.powerset,
        insert a E₁ = insert a E₂ → E₁ = E₂ := by
      intro E₁ h1' E₂ h2' heq
      have ha1 : a ∉ E₁ := fun h => ha (Finset.mem_powerset.mp h1' h)
      have ha2 : a ∉ E₂ := fun h => ha (Finset.mem_powerset.mp h2' h)
      have := congrArg (fun s => Finset.erase s a) heq
      simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
    rw [Finset.sum_image (fun E₁ h1' E₂ h2' h =>
      hinj E₁ (Finset.mem_coe.mp h1') E₂ (Finset.mem_coe.mp h2') h)]
    by_cases haM : a ∈ M
    · have hM' : M.erase a ⊆ U := by
        intro x hx
        obtain ⟨hne, hxM⟩ := Finset.mem_erase.mp hx
        exact (Finset.mem_insert.mp (hM hxM)).resolve_left hne
      have h1 :
          ∑ E ∈ U.powerset, binomWeight (insert a U) p E * r ^ (E ∩ M).card =
          (1 - p) * ∑ E ∈ U.powerset, binomWeight U p E * r ^ (E ∩ M.erase a).card := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro E hE
        have hEU := Finset.mem_powerset.mp hE
        have haE : a ∉ E := fun h => ha (hEU h)
        have hinter : E ∩ M = E ∩ M.erase a := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_erase]
          exact ⟨fun ⟨hxE, hxM⟩ => ⟨hxE, fun hxa => haE (hxa ▸ hxE), hxM⟩,
            fun ⟨hxE, _, hxM⟩ => ⟨hxE, hxM⟩⟩
        unfold binomWeight
        rw [hinter, Finset.card_insert_of_notMem ha, Nat.succ_sub (Finset.card_le_card hEU), pow_succ]
        ring
      have h2 :
          ∑ E ∈ U.powerset, binomWeight (insert a U) p (insert a E) * r ^ (insert a E ∩ M).card =
          (p * r) * ∑ E ∈ U.powerset, binomWeight U p E * r ^ (E ∩ M.erase a).card := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro E hE
        have hEU := Finset.mem_powerset.mp hE
        have haE : a ∉ E := fun h => ha (hEU h)
        have hinter : insert a E ∩ M = insert a (E ∩ M.erase a) := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro ⟨rfl | hxE, hxM⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hxE, fun hxa => haE (hxa ▸ hxE), hxM⟩
          · rintro (rfl | ⟨hxE, _, hxM⟩)
            · exact ⟨Or.inl rfl, haM⟩
            · exact ⟨Or.inr hxE, hxM⟩
        have haInter : a ∉ E ∩ M.erase a := fun h => haE (Finset.mem_inter.mp h).1
        unfold binomWeight
        rw [hinter, Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haE,
          Finset.card_insert_of_notMem haInter, Nat.succ_sub_succ, pow_succ, pow_succ]
        ring
      rw [h1, h2, ih (M.erase a) hM']
      have hcard : M.card = (M.erase a).card + 1 := (Finset.card_erase_add_one haM).symm
      rw [hcard, pow_succ]
      ring
    · have hMU : M ⊆ U := by
        intro x hx
        rcases Finset.mem_insert.mp (hM hx) with rfl | hxU
        · exact (haM hx).elim
        · exact hxU
      have h1 :
          ∑ E ∈ U.powerset, binomWeight (insert a U) p E * r ^ (E ∩ M).card =
          (1 - p) * ∑ E ∈ U.powerset, binomWeight U p E * r ^ (E ∩ M).card := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro E hE
        unfold binomWeight
        rw [Finset.card_insert_of_notMem ha,
          Nat.succ_sub (Finset.card_le_card (Finset.mem_powerset.mp hE)), pow_succ]
        ring
      have h2 :
          ∑ E ∈ U.powerset, binomWeight (insert a U) p (insert a E) * r ^ (insert a E ∩ M).card =
          p * ∑ E ∈ U.powerset, binomWeight U p E * r ^ (E ∩ M).card := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro E hE
        have haE : a ∉ E := fun h => ha (Finset.mem_powerset.mp hE h)
        have hinter : insert a E ∩ M = E ∩ M := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_insert]
          exact ⟨fun ⟨hx, hxM⟩ => ⟨hx.resolve_left (fun hxa => haM (hxa ▸ hxM)), hxM⟩,
            fun ⟨hxE, hxM⟩ => ⟨Or.inr hxE, hxM⟩⟩
        unfold binomWeight
        rw [hinter, Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haE,
          Nat.succ_sub_succ, pow_succ]
        ring
      rw [h1, h2, ih M hMU]
      ring

private lemma chernoff_lower_tail {α : Type*} [DecidableEq α]
    (U M : Finset α) (hMU : M ⊆ U) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let μ := (M.card : ℝ) * p
    ∑ E ∈ U.powerset.filter (fun E => ((E ∩ M).card : ℝ) < μ / 2), binomWeight U p E ≤
      Real.exp (- μ / 8) := by
  intro μ
  have hlog2 : Real.log 2 < 7 / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hbase_le : (1 : ℝ) - p / 2 ≤ Real.exp (- p / 2) := by
    have := Real.add_one_le_exp (- p / 2)
    linarith
  have hmgf : ∑ E ∈ U.powerset, binomWeight U p E * ((1 / 2 : ℝ) ^ (E ∩ M).card) ≤
      Real.exp (- μ / 2) := by
    have heq := sum_binomWeight_pow_inter U p (1 / 2) M hMU
    have h1 : (1 - p + p * (1 / 2 : ℝ)) = 1 - p / 2 := by ring
    rw [heq, h1]
    calc
      (1 - p / 2) ^ M.card ≤ (Real.exp (- p / 2)) ^ M.card :=
        pow_le_pow_left₀ (by linarith) hbase_le M.card
      _ = Real.exp ((M.card : ℝ) * (- p / 2)) := by rw [← Real.exp_nat_mul]
      _ = Real.exp (- μ / 2) := by congr 1; dsimp [μ]; ring
  have hmarkov :
      ((1 / 2 : ℝ) ^ (μ / 2)) *
        (∑ E ∈ U.powerset.filter (fun E => ((E ∩ M).card : ℝ) < μ / 2), binomWeight U p E) ≤
      ∑ E ∈ U.powerset, binomWeight U p E * ((1 / 2 : ℝ) ^ (E ∩ M).card) := by
    rw [Finset.mul_sum]
    calc
      ∑ E ∈ U.powerset.filter (fun E => ((E ∩ M).card : ℝ) < μ / 2),
          ((1 / 2 : ℝ) ^ (μ / 2)) * binomWeight U p E
        ≤ ∑ E ∈ U.powerset.filter (fun E => ((E ∩ M).card : ℝ) < μ / 2),
            binomWeight U p E * ((1 / 2 : ℝ) ^ (E ∩ M).card) := by
          apply Finset.sum_le_sum
          intro E hE
          have hlt : ((E ∩ M).card : ℝ) < μ / 2 := (Finset.mem_filter.mp hE).2
          have hpow : (1 / 2 : ℝ) ^ (μ / 2) ≤ (1 / 2 : ℝ) ^ ((E ∩ M).card : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hlt.le
          rw [Real.rpow_natCast] at hpow
          have hw := binomWeight_nonneg (U := U) (E := E) hp0 hp1
          nlinarith
      _ ≤ ∑ E ∈ U.powerset, binomWeight U p E * ((1 / 2 : ℝ) ^ (E ∩ M).card) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun E _ _ => mul_nonneg (binomWeight_nonneg hp0 hp1) (by positivity))
  have h2pow : (1 / 2 : ℝ) ^ (μ / 2) = Real.exp (- (Real.log 2) * (μ / 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2), Real.log_div (by norm_num) (by norm_num),
      Real.log_one, zero_sub]
  have hpos2 : 0 < Real.exp (- (Real.log 2) * (μ / 2)) := Real.exp_pos _
  have hstep :
      ∑ E ∈ U.powerset.filter (fun E => ((E ∩ M).card : ℝ) < μ / 2), binomWeight U p E ≤
      Real.exp (- μ / 2) / Real.exp (- (Real.log 2) * (μ / 2)) := by
    rw [le_div_iff₀ hpos2, mul_comm, ← h2pow]
    exact hmarkov.trans hmgf
  rw [← Real.exp_sub] at hstep
  have hμ0 : 0 ≤ μ := by dsimp [μ]; positivity
  have hexp : - μ / 2 - - (Real.log 2) * (μ / 2) ≤ - μ / 8 := by nlinarith
  exact hstep.trans (Real.exp_le_exp.mpr hexp)

/- ## Section 2: Elementary symmetric polynomial bound `e_m(f) ≤ (∑ f)^m / m!` -/

private lemma sum_powersetCard_prod_le {α : Type*} [DecidableEq α]
    (U : Finset α) (m : ℕ) (f : α → ℝ) (hf : ∀ x ∈ U, 0 ≤ f x) :
    (m.factorial : ℝ) * ∑ C ∈ U.powersetCard m, ∏ x ∈ C, f x ≤
      (∑ x ∈ U, f x) ^ m := by
  let tup := Fintype.piFinset (fun _ : Fin m => U)
  let inj := tup.filter Function.Injective
  have hpow : ∑ σ ∈ tup, ∏ i : Fin m, f (σ i) = (∑ x ∈ U, f x) ^ m := by
    have h2 : ∑ σ ∈ tup, ∏ i : Fin m, f (σ i) =
        ∏ _i : Fin m, ∑ x ∈ U, f x := by
      simpa [tup] using (Finset.prod_univ_sum (t := fun _ : Fin m => U)
        (f := fun (_ : Fin m) (x : α) => f x)).symm
    rw [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hle : ∑ σ ∈ inj, ∏ i : Fin m, f (σ i) ≤ ∑ σ ∈ tup, ∏ i : Fin m, f (σ i) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro σ hσ _
    exact Finset.prod_nonneg fun i _ => hf (σ i) (Fintype.mem_piFinset.mp hσ i)
  have hfib :
      ∑ σ ∈ inj, ∏ i : Fin m, f (σ i) =
      ∑ C ∈ U.powersetCard m,
        ∑ σ ∈ inj.filter (fun σ => Finset.univ.image σ = C), ∏ i : Fin m, f (σ i) := by
    symm
    apply Finset.sum_fiberwise_of_maps_to
    intro σ hσ
    obtain ⟨hσtup, hσinj⟩ := Finset.mem_filter.mp hσ
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact Fintype.mem_piFinset.mp hσtup i
    · rw [Finset.card_image_of_injective _ hσinj, Finset.card_univ, Fintype.card_fin]
  have hfiber_val : ∀ C ∈ U.powersetCard m,
      ∑ σ ∈ inj.filter (fun σ => Finset.univ.image σ = C), ∏ i : Fin m, f (σ i) =
      (m.factorial : ℝ) * ∏ x ∈ C, f x := by
    intro C hC
    obtain ⟨hCU, hCcard⟩ := Finset.mem_powersetCard.mp hC
    have hconst : ∀ σ ∈ inj.filter (fun σ => Finset.univ.image σ = C),
        ∏ i : Fin m, f (σ i) = ∏ x ∈ C, f x := by
      intro σ hσ
      obtain ⟨hσinj, hσimg⟩ := Finset.mem_filter.mp hσ
      rw [← hσimg, Finset.prod_image (fun i _ j _ h => (Finset.mem_filter.mp hσinj).2 h)]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcard_eq : (inj.filter (fun σ => Finset.univ.image σ = C)).card = m.factorial := by
      have heq_card : Fintype.card (Fin m) = Fintype.card C := by
        rw [Fintype.card_fin, Fintype.card_coe, hCcard]
      let e0 : Fin m ≃ C := Fintype.equivOfCardEq heq_card
      have hm_perm : m.factorial = Fintype.card (Equiv.Perm (Fin m)) := by
        rw [Fintype.card_perm, Fintype.card_fin]
      rw [hm_perm]
      symm
      rw [← Finset.card_univ]
      apply Finset.card_bij (fun (π : Equiv.Perm (Fin m)) _ => fun i : Fin m => (e0 (π i)).val)
      · intro π _
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
        · exact Fintype.mem_piFinset.mpr fun i => hCU (e0 (π i)).property
        · intro i j hij
          exact π.injective (e0.injective (Subtype.ext hij))
        · ext x
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, rfl⟩; exact (e0 (π i)).property
          · intro hx
            refine ⟨π.symm (e0.symm ⟨x, hx⟩), ?_⟩
            simp
      · intro π₁ _ π₂ _ hfun
        ext i
        have hi := congrFun hfun i
        exact congrArg Fin.val (e0.injective (Subtype.ext hi))
      · intro σ hσ
        obtain ⟨hσinj', hσimg⟩ := Finset.mem_filter.mp hσ
        have hσinj : Function.Injective σ := (Finset.mem_filter.mp hσinj').2
        have hmemC : ∀ i : Fin m, σ i ∈ C := fun i =>
          hσimg ▸ Finset.mem_image_of_mem σ (Finset.mem_univ i)
        let g : Fin m → Fin m := fun i => e0.symm ⟨σ i, hmemC i⟩
        have hginj : Function.Injective g := by
          intro i j hij
          have h1 := congrArg e0 hij
          simp only [g, Equiv.apply_symm_apply] at h1
          exact hσinj (congrArg Subtype.val h1)
        let π : Equiv.Perm (Fin m) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hginj)
        refine ⟨π, Finset.mem_univ _, ?_⟩
        funext i
        change (e0 (g i)).val = σ i
        simp [g]
    exact_mod_cast hcard_eq
  rw [hfib, Finset.sum_congr rfl hfiber_val, ← Finset.mul_sum] at hle
  exact hle.trans hpow.le

private lemma factorial_div_bound (W : ℝ) (hW : 0 ≤ W) (m : ℕ) (hm : 1 ≤ m) :
    W ^ m / (m.factorial : ℝ) ≤ (Real.exp 1 * W / (m : ℝ)) ^ m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hfac_pos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hexp := Real.pow_div_factorial_le_exp (m : ℝ) hmpos.le m
  have hexp_eq : Real.exp (m : ℝ) = (Real.exp 1) ^ m := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hexp_eq] at hexp
  have hinv : (1 : ℝ) / (m.factorial : ℝ) ≤ (Real.exp 1 / (m : ℝ)) ^ m := by
    rw [div_pow, div_le_div_iff₀ hfac_pos (pow_pos hmpos m), one_mul]
    have h1 := (div_le_iff₀ hfac_pos).mp hexp
    linarith
  calc
    W ^ m / (m.factorial : ℝ) = W ^ m * (1 / (m.factorial : ℝ)) := by ring
    _ ≤ W ^ m * (Real.exp 1 / (m : ℝ)) ^ m := mul_le_mul_of_nonneg_left hinv (pow_nonneg hW m)
    _ = (Real.exp 1 * W / (m : ℝ)) ^ m := by rw [← mul_pow]; congr 1; ring

/- ## Section 3: Graph edges, short cycles, and girth > 4 -/

private lemma sum_union_le' {α : Type*} [DecidableEq α]
    {s t : Finset α} {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ (∑ x ∈ s, f x) + ∑ x ∈ t, f x := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have hnn : 0 ≤ ∑ x ∈ s ∩ t, f x := Finset.sum_nonneg fun x _ => hf x
  linarith

private lemma sum_biUnion_le' {α β : Type*} [DecidableEq β]
    {s : Finset α} {t : α → Finset β} {f : β → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact (sum_union_le' hf).trans (add_le_add le_rfl ih)

private def allEdges (n : ℕ) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter (fun e => ¬ e.IsDiag)

private def edgesInside {n : ℕ} (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  (allEdges n).filter (fun e => ∀ v ∈ e, v ∈ S)

private lemma edgesInside_subset {n : ℕ} (S : Finset (Fin n)) :
    edgesInside S ⊆ allEdges n := Finset.filter_subset _ _

private lemma card_edgesInside {n : ℕ} (S : Finset (Fin n)) :
    (edgesInside S).card = S.card.choose 2 := by
  rw [← Finset.card_powersetCard 2 S]
  apply Finset.card_bij (fun e _ => Finset.univ.filter (fun v => v ∈ e))
  · intro e he
    obtain ⟨hnd, hin⟩ := Finset.mem_filter.mp he
    have hdiag : ¬ e.IsDiag := (Finset.mem_filter.mp hnd).2
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro v hv
      exact hin v (Finset.mem_filter.mp hv).2
    · refine Sym2.inductionOn e ?_ hdiag
      intro a b hab
      have hne : a ≠ b := by simpa [Sym2.mk_isDiag_iff] using hab
      have hpair : Finset.univ.filter (fun v => v ∈ s(a, b)) = ({a, b} : Finset (Fin n)) := by
        ext v
        simp [Sym2.mem_iff]
      rw [hpair, Finset.card_pair hne]
  · intro e₁ he₁ e₂ he₂ heq
    have hd1 : ¬ e₁.IsDiag := (Finset.mem_filter.mp (Finset.mem_filter.mp he₁).1).2
    have hd2 : ¬ e₂.IsDiag := (Finset.mem_filter.mp (Finset.mem_filter.mp he₂).1).2
    refine Sym2.inductionOn e₁ ?_ hd1 heq
    intro a₁ b₁ h1
    refine Sym2.inductionOn e₂ ?_ hd2
    intro a₂ b₂ h2 heq'
    have hmem : ∀ v, v ∈ s(a₁, b₁) ↔ v ∈ s(a₂, b₂) := fun v => by
      have := Finset.ext_iff.mp heq' v
      simpa using this
    exact Sym2.ext hmem
  · intro P hP
    obtain ⟨hPS, hPcard⟩ := Finset.mem_powersetCard.mp hP
    obtain ⟨a, b, hne, rfl⟩ := Finset.card_eq_two.mp hPcard
    refine ⟨s(a, b), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simpa [Sym2.mk_isDiag_iff] using hne
      · intro v hv
        rcases Sym2.mem_iff.mp hv with hva | hvb
        · rw [hva]; exact hPS (Finset.mem_insert_self a {b})
        · rw [hvb]; exact hPS (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    · ext v
      simp [Sym2.mem_iff]

private def isTri {n : ℕ} (F : Finset (Sym2 (Fin n))) : Prop :=
  ∃ a b c : Fin n, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ F = {s(a, b), s(b, c), s(c, a)}

private def isQuad {n : ℕ} (F : Finset (Sym2 (Fin n))) : Prop :=
  ∃ a b c d : Fin n,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    F = {s(a, b), s(b, c), s(c, d), s(d, a)}

private def isShortCycle {n : ℕ} (F : Finset (Sym2 (Fin n))) : Prop :=
  isTri F ∨ isQuad F

private lemma tri_card {n : ℕ} {F : Finset (Sym2 (Fin n))} (h : isTri F) : F.card = 3 := by
  obtain ⟨a, b, c, hab, hbc, hac, rfl⟩ := h
  have h1 : s(a, b) ≠ s(b, c) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab h1
    · exact hac h1
  have h2 : s(a, b) ≠ s(c, a) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hac h1
    · exact hbc h2
  have h3 : s(b, c) ≠ s(c, a) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hbc h1
    · exact hab h1.symm
  rw [Finset.card_insert_of_notMem (by simp [h1, h2]),
    Finset.card_insert_of_notMem (by simp [h3]), Finset.card_singleton]

private lemma quad_card {n : ℕ} {F : Finset (Sym2 (Fin n))} (h : isQuad F) : F.card = 4 := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := h
  have hne : ∀ u₁ v₁ u₂ v₂ : Fin n,
      (u₁ ≠ u₂ ∨ v₁ ≠ v₂) → (u₁ ≠ v₂ ∨ v₁ ≠ u₂) → s(u₁, v₁) ≠ s(u₂, v₂) := by
    intro u₁ v₁ u₂ v₂ h1 h2 heq
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1.elim (fun h => h rfl) (fun h => h rfl)
    · exact h2.elim (fun h => h rfl) (fun h => h rfl)
  have h12 : s(a, b) ≠ s(b, c) := hne _ _ _ _ (Or.inl hab) (Or.inl hac)
  have h13 : s(a, b) ≠ s(c, d) := hne _ _ _ _ (Or.inl hac) (Or.inl had)
  have h14 : s(a, b) ≠ s(d, a) := hne _ _ _ _ (Or.inl had) (Or.inr hbd)
  have h23 : s(b, c) ≠ s(c, d) := hne _ _ _ _ (Or.inl hbc) (Or.inl hbd)
  have h24 : s(b, c) ≠ s(d, a) := hne _ _ _ _ (Or.inl hbd) (Or.inl hab.symm)
  have h34 : s(c, d) ≠ s(d, a) := hne _ _ _ _ (Or.inl hcd) (Or.inl hac.symm)
  rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
    Finset.card_insert_of_notMem (by simp [h23, h24]),
    Finset.card_insert_of_notMem (by simp [h34]), Finset.card_singleton]

private lemma shortCycle_subset_allEdges {n : ℕ} {F : Finset (Sym2 (Fin n))}
    (h : isShortCycle F) : F ⊆ allEdges n := by
  rcases h with ⟨a, b, c, hab, hbc, hac, rfl⟩ | ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases he with rfl | rfl | rfl <;> simp [hab, hbc, hac.symm]
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [hab, hbc, hcd, had.symm]

private lemma shortCycle_card_le_four {n : ℕ} {F : Finset (Sym2 (Fin n))}
    (h : isShortCycle F) : F.card ≤ 4 := by
  rcases h with h3 | h4
  · rw [tri_card h3]; omega
  · rw [quad_card h4]

private def graphOfEdges {n : ℕ} (E : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ s(u, v) ∈ E
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by rwa [Sym2.eq_swap]⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

private lemma egirth_gt_four_of_no_shortCycle {n : ℕ} {E : Finset (Sym2 (Fin n))}
    (hno : ∀ F, isShortCycle F → ¬ (F ⊆ E)) :
    (4 : ℕ∞) < (graphOfEdges E).egirth := by
  have h5 : (5 : ℕ∞) ≤ (graphOfEdges E).egirth := by
    rw [SimpleGraph.le_egirth]
    intro a w hw
    have hge3 : 3 ≤ w.length := by
      have := SimpleGraph.le_egirth.mp (graphOfEdges E).three_le_egirth a w hw
      exact_mod_cast this
    by_contra hlt
    have hlt5 : w.length < 5 := by
      by_contra hge5
      exact hlt (by exact_mod_cast (show 5 ≤ w.length by omega))
    rcases (show w.length = 3 ∨ w.length = 4 by omega) with hlen3 | hlen4
    · rcases w with _ | ⟨h1, w1⟩
      · simp at hlen3
      rcases w1 with _ | ⟨h2, w2⟩
      · simp at hlen3
      rcases w2 with _ | ⟨h3, w3⟩
      · simp at hlen3
      rcases w3 with _ | ⟨h4, w4⟩
      · rename_i b c
        have hab : a ≠ b := h1.1
        have hbc : b ≠ c := h2.1
        have hca : c ≠ a := h3.1
        apply hno {s(a, b), s(b, c), s(c, a)} (Or.inl ⟨a, b, c, hab, hbc, hca.symm, rfl⟩)
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact h1.2
        · exact h2.2
        · exact h3.2
      · simp at hlen3
    · rcases w with _ | ⟨h1, w1⟩
      · simp at hlen4
      rcases w1 with _ | ⟨h2, w2⟩
      · simp at hlen4
      rcases w2 with _ | ⟨h3, w3⟩
      · simp at hlen4
      rcases w3 with _ | ⟨h4, w4⟩
      · simp at hlen4
      rcases w4 with _ | ⟨h5, w5⟩
      · rename_i b c d
        have hnodup := hw.support_nodup
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.tail_cons, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
          not_or] at hnodup
        obtain ⟨⟨hbc, hbd, hba⟩, ⟨hcd, hca⟩, hda, _⟩ := hnodup
        apply hno {s(a, b), s(b, c), s(c, d), s(d, a)}
          (Or.inr ⟨a, b, c, d, Ne.symm hba, Ne.symm hca, Ne.symm hda, hbc, hbd, hcd, rfl⟩)
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl | rfl
        · exact h1.2
        · exact h2.2
        · exact h3.2
        · exact h4.2
      · simp at hlen4
  exact lt_of_lt_of_le (by decide : (4 : ℕ∞) < 5) h5

private noncomputable def shortCyclesTouching {n : ℕ} (S : Finset (Fin n)) :
    Finset (Finset (Sym2 (Fin n))) :=
  (allEdges n).powerset.filter (fun F => isShortCycle F ∧ (F ∩ edgesInside S).Nonempty)

private lemma tri_weight_sum_le {n : ℕ} (S : Finset (Fin n)) :
    ((shortCyclesTouching S).filter isTri).card ≤ S.card ^ 2 * n := by
  let f : (Fin n × Fin n × Fin n) → Finset (Sym2 (Fin n)) :=
    fun t => {s(t.1, t.2.1), s(t.2.1, t.2.2), s(t.2.2, t.1)}
  have hsub : (shortCyclesTouching S).filter isTri ⊆
      (S ×ˢ S ×ˢ (Finset.univ : Finset (Fin n))).image f := by
    intro F hF
    obtain ⟨hFT, htri⟩ := Finset.mem_filter.mp hF
    obtain ⟨_, _, e, he⟩ := Finset.mem_filter.mp hFT
    obtain ⟨heF, heS⟩ := Finset.mem_inter.mp he
    have heIn : ∀ v ∈ e, v ∈ S := (Finset.mem_filter.mp heS).2
    obtain ⟨a, b, c, _, _, _, rfl⟩ := htri
    simp only [Finset.mem_insert, Finset.mem_singleton] at heF
    rw [Finset.mem_image]
    rcases heF with rfl | rfl | rfl
    · refine ⟨(a, b, c), Finset.mem_product.mpr ⟨heIn a (Sym2.mem_mk_left a b),
        Finset.mem_product.mpr ⟨heIn b (Sym2.mem_mk_right a b), Finset.mem_univ c⟩⟩, rfl⟩
    · refine ⟨(b, c, a), Finset.mem_product.mpr ⟨heIn b (Sym2.mem_mk_left b c),
        Finset.mem_product.mpr ⟨heIn c (Sym2.mem_mk_right b c), Finset.mem_univ a⟩⟩, ?_⟩
      ext x; simp [f]; tauto
    · refine ⟨(c, a, b), Finset.mem_product.mpr ⟨heIn c (Sym2.mem_mk_left c a),
        Finset.mem_product.mpr ⟨heIn a (Sym2.mem_mk_right c a), Finset.mem_univ b⟩⟩, ?_⟩
      ext x; simp [f]; tauto
  calc
    ((shortCyclesTouching S).filter isTri).card
      ≤ ((S ×ˢ S ×ˢ (Finset.univ : Finset (Fin n))).image f).card := Finset.card_le_card hsub
    _ ≤ (S ×ˢ S ×ˢ (Finset.univ : Finset (Fin n))).card := Finset.card_image_le
    _ = S.card ^ 2 * n := by
        simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        ring

private lemma quad_weight_sum_le {n : ℕ} (S : Finset (Fin n)) :
    ((shortCyclesTouching S).filter isQuad).card ≤ S.card ^ 2 * n ^ 2 := by
  let f : (Fin n × Fin n × Fin n × Fin n) → Finset (Sym2 (Fin n)) :=
    fun t => {s(t.1, t.2.1), s(t.2.1, t.2.2.1), s(t.2.2.1, t.2.2.2), s(t.2.2.2, t.1)}
  have hsub : (shortCyclesTouching S).filter isQuad ⊆
      (S ×ˢ S ×ˢ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))).image f := by
    intro F hF
    obtain ⟨hFT, hquad⟩ := Finset.mem_filter.mp hF
    obtain ⟨_, _, e, he⟩ := Finset.mem_filter.mp hFT
    obtain ⟨heF, heS⟩ := Finset.mem_inter.mp he
    have heIn : ∀ v ∈ e, v ∈ S := (Finset.mem_filter.mp heS).2
    obtain ⟨a, b, c, d, _, _, _, _, _, _, rfl⟩ := hquad
    simp only [Finset.mem_insert, Finset.mem_singleton] at heF
    rw [Finset.mem_image]
    rcases heF with rfl | rfl | rfl | rfl
    · refine ⟨(a, b, c, d), Finset.mem_product.mpr ⟨heIn a (Sym2.mem_mk_left a b),
        Finset.mem_product.mpr ⟨heIn b (Sym2.mem_mk_right a b),
          Finset.mem_product.mpr ⟨Finset.mem_univ c, Finset.mem_univ d⟩⟩⟩, rfl⟩
    · refine ⟨(b, c, d, a), Finset.mem_product.mpr ⟨heIn b (Sym2.mem_mk_left b c),
        Finset.mem_product.mpr ⟨heIn c (Sym2.mem_mk_right b c),
          Finset.mem_product.mpr ⟨Finset.mem_univ d, Finset.mem_univ a⟩⟩⟩, ?_⟩
      ext x; simp [f]; tauto
    · refine ⟨(c, d, a, b), Finset.mem_product.mpr ⟨heIn c (Sym2.mem_mk_left c d),
        Finset.mem_product.mpr ⟨heIn d (Sym2.mem_mk_right c d),
          Finset.mem_product.mpr ⟨Finset.mem_univ a, Finset.mem_univ b⟩⟩⟩, ?_⟩
      ext x; simp [f]; tauto
    · refine ⟨(d, a, b, c), Finset.mem_product.mpr ⟨heIn d (Sym2.mem_mk_left d a),
        Finset.mem_product.mpr ⟨heIn a (Sym2.mem_mk_right d a),
          Finset.mem_product.mpr ⟨Finset.mem_univ b, Finset.mem_univ c⟩⟩⟩, ?_⟩
      ext x; simp [f]; tauto
  calc
    ((shortCyclesTouching S).filter isQuad).card
      ≤ ((S ×ˢ S ×ˢ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))).image f).card :=
        Finset.card_le_card hsub
    _ ≤ (S ×ˢ S ×ˢ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))).card :=
        Finset.card_image_le
    _ = S.card ^ 2 * n ^ 2 := by
        simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        ring

private lemma shortCyclesTouching_weight_le {n : ℕ} (S : Finset (Fin n)) {p : ℝ} (hp0 : 0 ≤ p) :
    ∑ F ∈ shortCyclesTouching S, p ^ F.card ≤
      (S.card : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (S.card : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4 := by
  have hcov : shortCyclesTouching S ⊆
      (shortCyclesTouching S).filter isTri ∪ (shortCyclesTouching S).filter isQuad := by
    intro F hF
    rcases (Finset.mem_filter.mp hF).2.1 with h3 | h4
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hF, h3⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hF, h4⟩)
  calc
    ∑ F ∈ shortCyclesTouching S, p ^ F.card
      ≤ ∑ F ∈ (shortCyclesTouching S).filter isTri ∪ (shortCyclesTouching S).filter isQuad,
          p ^ F.card :=
        Finset.sum_le_sum_of_subset_of_nonneg hcov (fun _ _ _ => pow_nonneg hp0 _)
    _ ≤ (∑ F ∈ (shortCyclesTouching S).filter isTri, p ^ F.card) +
        (∑ F ∈ (shortCyclesTouching S).filter isQuad, p ^ F.card) :=
        sum_union_le' (fun _ => pow_nonneg hp0 _)
    _ = (((shortCyclesTouching S).filter isTri).card : ℝ) * p ^ 3 +
        (((shortCyclesTouching S).filter isQuad).card : ℝ) * p ^ 4 := by
        congr 1
        · rw [Finset.sum_congr rfl (fun F hF => by rw [tri_card (Finset.mem_filter.mp hF).2]),
            Finset.sum_const, nsmul_eq_mul]
        · rw [Finset.sum_congr rfl (fun F hF => by rw [quad_card (Finset.mem_filter.mp hF).2]),
            Finset.sum_const, nsmul_eq_mul]
    _ ≤ (S.card : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (S.card : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4 := by
        have h3 : (((shortCyclesTouching S).filter isTri).card : ℝ) ≤ (S.card : ℝ) ^ 2 * (n : ℝ) := by
          exact_mod_cast tri_weight_sum_le S
        have h4 : (((shortCyclesTouching S).filter isQuad).card : ℝ) ≤ (S.card : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
          exact_mod_cast quad_weight_sum_le S
        gcongr

/- ## Section 4: Edge-disjoint cycle union bound and deterministic extraction -/

private def hasDisjointCycles {n : ℕ} (S : Finset (Fin n)) (m : ℕ)
    (E : Finset (Sym2 (Fin n))) : Prop :=
  ∃ C ∈ (shortCyclesTouching S).powersetCard m,
    (C : Set (Finset (Sym2 (Fin n)))).PairwiseDisjoint id ∧ ∀ F ∈ C, F ⊆ E

private lemma prob_hasDisjointCycles_le {n : ℕ} (S : Finset (Fin n)) (m : ℕ)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ E ∈ (allEdges n).powerset.filter (hasDisjointCycles S m), binomWeight (allEdges n) p E ≤
      (∑ F ∈ shortCyclesTouching S, p ^ F.card) ^ m / (m.factorial : ℝ) := by
  let Dfam : Finset (Finset (Finset (Sym2 (Fin n)))) :=
    ((shortCyclesTouching S).powersetCard m).filter
      (fun (C : Finset (Finset (Sym2 (Fin n)))) => (C : Set (Finset (Sym2 (Fin n)))).PairwiseDisjoint id)
  have hsub :
      (allEdges n).powerset.filter (hasDisjointCycles S m) ⊆
      Dfam.biUnion (fun C => (allEdges n).powerset.filter (fun E => C.biUnion id ⊆ E)) := by
    intro E hE
    obtain ⟨hEp, C, hCm, hCdisj, hCE⟩ := Finset.mem_filter.mp hE
    refine Finset.mem_biUnion.mpr ⟨C, Finset.mem_filter.mpr ⟨hCm, hCdisj⟩,
      Finset.mem_filter.mpr ⟨hEp, ?_⟩⟩
    intro e he
    obtain ⟨F, hFC, heF⟩ := Finset.mem_biUnion.mp he
    exact hCE F hFC heF
  have hunion :
      ∑ E ∈ (allEdges n).powerset.filter (hasDisjointCycles S m), binomWeight (allEdges n) p E ≤
      ∑ C ∈ Dfam,
        ∑ E ∈ (allEdges n).powerset.filter (fun E => C.biUnion id ⊆ E),
          binomWeight (allEdges n) p E := by
    calc
      ∑ E ∈ (allEdges n).powerset.filter (hasDisjointCycles S m), binomWeight (allEdges n) p E
        ≤ ∑ E ∈ Dfam.biUnion (fun C => (allEdges n).powerset.filter (fun E => C.biUnion id ⊆ E)),
            binomWeight (allEdges n) p E :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => binomWeight_nonneg hp0 hp1)
      _ ≤ ∑ C ∈ Dfam,
            ∑ E ∈ (allEdges n).powerset.filter (fun E => C.biUnion id ⊆ E),
              binomWeight (allEdges n) p E :=
          sum_biUnion_le' (fun _ => binomWeight_nonneg hp0 hp1)
  have heval : ∀ C ∈ Dfam,
      ∑ E ∈ (allEdges n).powerset.filter (fun E => C.biUnion id ⊆ E),
        binomWeight (allEdges n) p E =
      ∏ F ∈ C, p ^ F.card := by
    intro C hC
    obtain ⟨hCm, hCdisj⟩ := Finset.mem_filter.mp hC
    have hCU : C.biUnion id ⊆ allEdges n := by
      intro e he
      obtain ⟨F, hFC, heF⟩ := Finset.mem_biUnion.mp he
      have hFT : F ∈ shortCyclesTouching S := (Finset.mem_powersetCard.mp hCm).1 hFC
      exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hFT).1) heF
    rw [sum_binomWeight_superset (allEdges n) p (C.biUnion id) hCU,
      Finset.card_biUnion (fun F₁ h1 F₂ h2 hne => hCdisj h1 h2 hne),
      Finset.prod_pow_eq_pow_sum]
    rfl
  have hle_all :
      ∑ C ∈ Dfam, ∏ F ∈ C, p ^ F.card ≤
      ∑ C ∈ (shortCyclesTouching S).powersetCard m, ∏ F ∈ C, p ^ F.card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Finset.prod_nonneg fun _ _ => pow_nonneg hp0 _)
  have hfac_pos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hsym := sum_powersetCard_prod_le (shortCyclesTouching S) m (fun F => p ^ F.card)
    (fun _ _ => pow_nonneg hp0 _)
  calc
    ∑ E ∈ (allEdges n).powerset.filter (hasDisjointCycles S m), binomWeight (allEdges n) p E
      ≤ ∑ C ∈ Dfam, ∏ F ∈ C, p ^ F.card := by rw [← Finset.sum_congr rfl heval]; exact hunion
    _ ≤ ∑ C ∈ (shortCyclesTouching S).powersetCard m, ∏ F ∈ C, p ^ F.card := hle_all
    _ ≤ (∑ F ∈ shortCyclesTouching S, p ^ F.card) ^ m / (m.factorial : ℝ) :=
        (le_div_iff₀' hfac_pos).mpr hsym

private lemma exists_girth_gt_four_no_indep {n t m : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (_ht : 1 ≤ t) (_htn : t ≤ n)
    (hmu : let μ := (t.choose 2 : ℝ) * p
      0 < μ ∧ m = Nat.ceil (μ / 8))
    (hprob :
      let μ := (t.choose 2 : ℝ) * p
      ((n.choose t : ℕ) : ℝ) *
        (Real.exp (- μ / 8) +
          (Real.exp 1 * ((t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) / (m : ℝ)) ^ m) < 1) :
    ∃ H : SimpleGraph (Fin n), (4 : ℕ∞) < H.egirth ∧
      ∀ S : Finset (Fin n), S.card = t → ∃ u ∈ S, ∃ v ∈ S, H.Adj u v := by
  set μ := (t.choose 2 : ℝ) * p
  obtain ⟨hμpos, hm_eq⟩ := hmu
  have hm1 : 1 ≤ m := by
    rw [hm_eq]
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      have := Nat.le_ceil (μ / 8)
      rw [h0] at this
      simp at this
      linarith)
  let sets := (Finset.univ : Finset (Fin n)).powersetCard t
  let badA (S : Finset (Fin n)) :=
    (allEdges n).powerset.filter (fun E => ((E ∩ edgesInside S).card : ℝ) < μ / 2)
  let badB (S : Finset (Fin n)) :=
    (allEdges n).powerset.filter (hasDisjointCycles S m)
  let badAll := sets.biUnion (fun S => badA S ∪ badB S)
  have hbad_lt_one : ∑ E ∈ badAll, binomWeight (allEdges n) p E < 1 := by
    have hper : ∀ S ∈ sets,
        ∑ E ∈ badA S ∪ badB S, binomWeight (allEdges n) p E ≤
        Real.exp (- μ / 8) +
          (Real.exp 1 * ((t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) / (m : ℝ)) ^ m := by
      intro S hS
      have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
      have hA : ∑ E ∈ badA S, binomWeight (allEdges n) p E ≤ Real.exp (- μ / 8) := by
        have hch := chernoff_lower_tail (allEdges n) (edgesInside S) (edgesInside_subset S) hp0 hp1
        dsimp only at hch
        rw [card_edgesInside S, hScard] at hch
        exact hch
      have hB : ∑ E ∈ badB S, binomWeight (allEdges n) p E ≤
          (Real.exp 1 * ((t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) / (m : ℝ)) ^ m := by
        set W := ∑ F ∈ shortCyclesTouching S, p ^ F.card
        have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => pow_nonneg hp0 _
        have hWle : W ≤ (t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4 := by
          simpa [hScard] using shortCyclesTouching_weight_le S hp0
        calc
          ∑ E ∈ badB S, binomWeight (allEdges n) p E
            ≤ W ^ m / (m.factorial : ℝ) := prob_hasDisjointCycles_le S m hp0 hp1
          _ ≤ (Real.exp 1 * W / (m : ℝ)) ^ m := factorial_div_bound W hW0 m hm1
          _ ≤ (Real.exp 1 * ((t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) / (m : ℝ)) ^ m := by
              apply pow_le_pow_left₀ (by positivity)
              gcongr
      calc
        ∑ E ∈ badA S ∪ badB S, binomWeight (allEdges n) p E
          ≤ (∑ E ∈ badA S, binomWeight (allEdges n) p E) +
            (∑ E ∈ badB S, binomWeight (allEdges n) p E) :=
          sum_union_le' (fun _ => binomWeight_nonneg hp0 hp1)
        _ ≤ _ := add_le_add hA hB
    have hsets_card : sets.card = n.choose t := by
      simp [sets]
    calc
      ∑ E ∈ badAll, binomWeight (allEdges n) p E
        ≤ ∑ S ∈ sets, ∑ E ∈ badA S ∪ badB S, binomWeight (allEdges n) p E :=
          sum_biUnion_le' (fun _ => binomWeight_nonneg hp0 hp1)
      _ ≤ ∑ _S ∈ sets, (Real.exp (- μ / 8) +
            (Real.exp 1 * ((t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) / (m : ℝ)) ^ m) :=
          Finset.sum_le_sum hper
      _ = ((n.choose t : ℕ) : ℝ) *
            (Real.exp (- μ / 8) +
              (Real.exp 1 * ((t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) / (m : ℝ)) ^ m) := by
          rw [Finset.sum_const, hsets_card, nsmul_eq_mul]
      _ < 1 := hprob
  have hexists_good : ∃ E ∈ (allEdges n).powerset, E ∉ badAll := by
    by_contra hnone
    push Not at hnone
    have hsub : (allEdges n).powerset ⊆ badAll := hnone
    have h1 : (1 : ℝ) ≤ ∑ E ∈ badAll, binomWeight (allEdges n) p E := by
      rw [← sum_binomWeight_eq_one (allEdges n) p]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => binomWeight_nonneg hp0 hp1)
    linarith
  obtain ⟨E, hEp, hEgood⟩ := hexists_good
  have hE_all : E ⊆ allEdges n := Finset.mem_powerset.mp hEp
  let shortInE := (allEdges n).powerset.filter (fun F => isShortCycle F ∧ F ⊆ E)
  let validColls : Finset (Finset (Finset (Sym2 (Fin n)))) :=
    shortInE.powerset.filter
      (fun (C : Finset (Finset (Sym2 (Fin n)))) => (C : Set (Finset (Sym2 (Fin n)))).PairwiseDisjoint id)
  have hvalid_ne : validColls.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩⟩
    simp
  obtain ⟨C, hCmem, hCmax⟩ := Finset.exists_max_image validColls Finset.card hvalid_ne
  obtain ⟨hCsub, hCdisj⟩ := Finset.mem_filter.mp hCmem
  let E' := E \ C.biUnion id
  refine ⟨graphOfEdges E', ?_, ?_⟩
  · apply egirth_gt_four_of_no_shortCycle
    intro F hFshort hFE'
    have hFE : F ⊆ E := hFE'.trans Finset.sdiff_subset
    have hFinE : F ∈ shortInE :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (shortCycle_subset_allEdges hFshort), hFshort, hFE⟩
    have hFdisj : ∀ F' ∈ C, Disjoint F F' := by
      intro F' hF'C
      rw [Finset.disjoint_left]
      intro e heF heF'
      exact (Finset.mem_sdiff.mp (hFE' heF)).2 (Finset.mem_biUnion.mpr ⟨F', hF'C, heF'⟩)
    have hFnotC : F ∉ C := by
      intro hFC
      have hFne : F.Nonempty := by
        rcases hFshort with h3 | h4
        · exact Finset.card_pos.mp (by rw [tri_card h3]; omega)
        · exact Finset.card_pos.mp (by rw [quad_card h4]; omega)
      obtain ⟨e, he⟩ := hFne
      exact Finset.disjoint_left.mp (hFdisj F hFC) he he
    have hins_mem : insert F C ∈ validColls := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hFinE
        (Finset.mem_powerset.mp hCsub)), ?_⟩
      intro X hX Y hY hXY
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hX hY
      rcases hX with rfl | hXC <;> rcases hY with rfl | hYC
      · exact (hXY rfl).elim
      · exact hFdisj Y hYC
      · exact (hFdisj X hXC).symm
      · exact hCdisj hXC hYC hXY
    have hle := hCmax (insert F C) hins_mem
    rw [Finset.card_insert_of_notMem hFnotC] at hle
    omega
  · intro S hScard
    have hSmem : S ∈ sets := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hScard⟩
    have hnotA : E ∉ badA S := fun h => hEgood (Finset.mem_biUnion.mpr ⟨S, hSmem, Finset.mem_union_left _ h⟩)
    have hnotB : E ∉ badB S := fun h => hEgood (Finset.mem_biUnion.mpr ⟨S, hSmem, Finset.mem_union_right _ h⟩)
    have hEcard_ge : μ / 2 ≤ ((E ∩ edgesInside S).card : ℝ) := by
      by_contra hlt
      push Not at hlt
      exact hnotA (Finset.mem_filter.mpr ⟨hEp, hlt⟩)
    let CS := C.filter (fun F => (F ∩ edgesInside S).Nonempty)
    have hCS_lt : CS.card < m := by
      by_contra hge
      push Not at hge
      obtain ⟨C', hC'sub, hC'card⟩ := Finset.exists_subset_card_eq hge
      apply hnotB
      refine Finset.mem_filter.mpr ⟨hEp, C', ?_, ?_, ?_⟩
      · refine Finset.mem_powersetCard.mpr ⟨?_, hC'card⟩
        intro F hF
        have hFCS := hC'sub hF
        obtain ⟨hFC, hFne⟩ := Finset.mem_filter.mp hFCS
        have hFinE := Finset.mem_powerset.mp hCsub hFC
        obtain ⟨hFp, hFshort, _⟩ := Finset.mem_filter.mp hFinE
        exact Finset.mem_filter.mpr ⟨hFp, hFshort, hFne⟩
      · intro X hX Y hY hXY
        exact hCdisj (Finset.mem_filter.mp (hC'sub hX)).1 (Finset.mem_filter.mp (hC'sub hY)).1 hXY
      · intro F hF
        have hFC := (Finset.mem_filter.mp (hC'sub hF)).1
        exact (Finset.mem_filter.mp (Finset.mem_powerset.mp hCsub hFC)).2.2
    have hcov_card : (E ∩ edgesInside S ∩ C.biUnion id).card ≤ 4 * CS.card := by
      have hsub : E ∩ edgesInside S ∩ C.biUnion id ⊆ CS.biUnion id := by
        intro e he
        obtain ⟨heES, heC⟩ := Finset.mem_inter.mp he
        obtain ⟨_, heS⟩ := Finset.mem_inter.mp heES
        obtain ⟨F, hFC, heF⟩ := Finset.mem_biUnion.mp heC
        exact Finset.mem_biUnion.mpr ⟨F, Finset.mem_filter.mpr ⟨hFC, ⟨e, Finset.mem_inter.mpr ⟨heF, heS⟩⟩⟩, heF⟩
      calc
        (E ∩ edgesInside S ∩ C.biUnion id).card ≤ (CS.biUnion id).card := Finset.card_le_card hsub
        _ ≤ ∑ F ∈ CS, F.card := Finset.card_biUnion_le
        _ ≤ ∑ _F ∈ CS, 4 := by
            apply Finset.sum_le_sum
            intro F hF
            have hFC := (Finset.mem_filter.mp hF).1
            exact shortCycle_card_le_four (Finset.mem_filter.mp (Finset.mem_powerset.mp hCsub hFC)).2.1
        _ = 4 * CS.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hlt_strict : 4 * (CS.card : ℝ) < μ / 2 := by
      have hle_m1 : CS.card ≤ m - 1 := by omega
      have hm1_lt : ((m - 1 : ℕ) : ℝ) < μ / 8 := by
        by_contra hge
        push Not at hge
        have hceil : Nat.ceil (μ / 8) ≤ m - 1 := Nat.ceil_le.mpr hge
        omega
      have hCS_le : (CS.card : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hle_m1
      linarith
    have hrem_ne : (E' ∩ edgesInside S).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have hsub : E ∩ edgesInside S ⊆ E ∩ edgesInside S ∩ C.biUnion id := by
        intro e he
        obtain ⟨heE, heS⟩ := Finset.mem_inter.mp he
        refine Finset.mem_inter.mpr ⟨he, ?_⟩
        by_contra hnotC
        have heE' : e ∈ E' := Finset.mem_sdiff.mpr ⟨heE, hnotC⟩
        have : e ∈ E' ∩ edgesInside S := Finset.mem_inter.mpr ⟨heE', heS⟩
        rw [hemp] at this
        exact Finset.notMem_empty e this
      have hle1 : (E ∩ edgesInside S).card ≤ 4 * CS.card :=
        (Finset.card_le_card hsub).trans hcov_card
      have hle1R : ((E ∩ edgesInside S).card : ℝ) ≤ 4 * (CS.card : ℝ) := by exact_mod_cast hle1
      linarith
    obtain ⟨e, he⟩ := hrem_ne
    obtain ⟨heE', heS⟩ := Finset.mem_inter.mp he
    have heAll : e ∈ allEdges n := (Finset.mem_filter.mp heS).1
    have heDiag : ¬ e.IsDiag := (Finset.mem_filter.mp heAll).2
    have heIn : ∀ v ∈ e, v ∈ S := (Finset.mem_filter.mp heS).2
    refine Sym2.inductionOn e ?_ heE' heDiag heIn
    intro u v huv hnd hin
    have hne : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using hnd
    exact ⟨u, hin u (Sym2.mem_mk_left u v), v, hin v (Sym2.mem_mk_right u v), ⟨hne, huv⟩⟩

private lemma chromaticNumber_lower_of_no_indep {n t : ℕ} {H : SimpleGraph (Fin n)}
    (ht : 1 ≤ t)
    (hno : ∀ S : Finset (Fin n), S.card = t → ∃ u ∈ S, ∃ v ∈ S, H.Adj u v) :
    ∃ c : ℕ, H.chromaticNumber = (c : ℕ∞) ∧ (n : ℝ) / (t : ℝ) ≤ (c : ℝ) := by
  have hle_n : H.chromaticNumber ≤ (n : ℕ∞) := by
    simpa [Fintype.card_fin] using H.chromaticNumber_le_card
  have hne_top : H.chromaticNumber ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n) hle_n
  let c := H.chromaticNumber.toNat
  have hc_eq : H.chromaticNumber = (c : ℕ∞) := (ENat.natCast_toNat hne_top).symm
  have hcol : H.Colorable c := SimpleGraph.colorable_of_chromaticNumber_ne_top hne_top
  obtain ⟨col⟩ := hcol
  have hclass_lt : ∀ i : Fin c, (Finset.univ.filter (fun v : Fin n => col v = i)).card < t := by
    intro i
    by_contra hge
    push Not at hge
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hge
    obtain ⟨u, huS, v, hvS, hadj⟩ := hno S hScard
    have hu : col u = i := (Finset.mem_filter.mp (hSsub huS)).2
    have hv : col v = i := (Finset.mem_filter.mp (hSsub hvS)).2
    exact col.valid hadj (hu.trans hv.symm)
  have hsum : n ≤ c * t := by
    calc
      n = (Finset.univ : Finset (Fin n)).card := by simp
      _ = ∑ i : Fin c, (Finset.univ.filter (fun v : Fin n => col v = i)).card := by
          rw [Finset.card_eq_sum_card_fiberwise (f := col) (t := Finset.univ)
            (fun _ _ => Finset.mem_univ _)]
      _ ≤ ∑ _i : Fin c, t := Finset.sum_le_sum fun i _ => (hclass_lt i).le
      _ = c * t := by simp
  refine ⟨c, hc_eq, ?_⟩
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  rw [div_le_iff₀ htpos]
  exact_mod_cast hsum

private lemma le_h_of_graph {n c : ℕ} {H : SimpleGraph (Fin n)}
    (hgirth : (4 : ℕ∞) < H.egirth) (hchi : H.chromaticNumber = (c : ℕ∞)) :
    c ≤ Erdos626.h 4 n := by
  unfold Erdos626.h
  apply le_csSup
  · refine ⟨n, ?_⟩
    rintro k ⟨G, -, hG⟩
    have hle := G.chromaticNumber_le_card
    rw [hG, Fintype.card_fin] at hle
    exact_mod_cast hle
  · exact ⟨H, hgirth, hchi⟩

end Erdos626H4Lower

theorem OMA.solution :
    OMA.R_Erdos626_erdos_626_variants_h_even_conjecture_R1_H2_R1.H1 := by
  open Erdos626H4Lower Filter Real in
  intro ε hε
  set δ : ℝ := min (ε / 4) (1 / 24)
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ_eps : δ ≤ ε / 4 := min_le_left _ _
  have hδ_small : δ ≤ 1 / 24 := min_le_right _ _
  have hlim_log : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ δ) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hδpos).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlim_pow_neg : Tendsto (fun n : ℕ => (n : ℝ) ^ (- 3 * δ)) atTop (nhds 0) := by
    simpa [Function.comp_def, neg_mul] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < 3 * δ)).comp tendsto_natCast_atTop_atTop
  have hlim_pow_half : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 3 - δ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < (1 : ℝ) / 3 - δ)).comp tendsto_natCast_atTop_atTop
  have hlim_t : Tendsto (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) / 3 + 2 * δ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < (2 : ℝ) / 3 + 2 * δ)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (100 : ℕ),
      hlim_log.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 256)),
      hlim_pow_neg.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 1000)),
      hlim_pow_half.eventually (eventually_ge_atTop (1 : ℝ)),
      hlim_t.eventually (eventually_ge_atTop (16 : ℝ))]
    with n hn100 hlog_small hneg_small hnp_ge1 ht_large
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  set p : ℝ := (n : ℝ) ^ (- (2 : ℝ) / 3 - δ)
  have hp0 : 0 ≤ p := Real.rpow_nonneg hn_pos.le _
  have hp_pos : 0 < p := Real.rpow_pos_of_pos hn_pos _
  have hp1 : p ≤ 1 := by
    have : (n : ℝ) ^ (- (2 : ℝ) / 3 - δ) ≤ (n : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn_ge1 (by linarith)
    simpa using this
  set t : ℕ := ⌊(n : ℝ) ^ ((2 : ℝ) / 3 + 2 * δ)⌋₊
  have ht_le_real : (t : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3 + 2 * δ) := Nat.floor_le (by positivity)
  have ht_gt_real : (n : ℝ) ^ ((2 : ℝ) / 3 + 2 * δ) - 1 < (t : ℝ) := by
    have := Nat.lt_floor_add_one ((n : ℝ) ^ ((2 : ℝ) / 3 + 2 * δ))
    linarith
  have ht_ge8 : 8 ≤ t := by
    have h1 : (15 : ℝ) < (t : ℝ) := by linarith
    have h2 : (8 : ℝ) < (t : ℝ) := by linarith
    have : 8 < t := by exact_mod_cast h2
    omega
  have ht_half : (1 / 2 : ℝ) * (n : ℝ) ^ ((2 : ℝ) / 3 + 2 * δ) ≤ (t : ℝ) := by linarith
  have htn : t ≤ n := by
    have h1 : (t : ℝ) ≤ (n : ℝ) := by
      calc
        (t : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3 + 2 * δ) := ht_le_real
        _ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn_ge1 (by linarith)
        _ = (n : ℝ) := Real.rpow_one _
    exact_mod_cast h1
  set μ : ℝ := (t.choose 2 : ℝ) * p
  have hchoose_lb : (t : ℝ) ^ 2 / 4 ≤ (t.choose 2 : ℝ) := by
    have hnat : t * (t - 1) = 2 * t.choose 2 := by
      have := Nat.choose_two_right t
      have hdvd : 2 ∣ t * (t - 1) := Nat.even_mul_pred_self t |>.two_dvd
      rw [this, Nat.mul_div_cancel' hdvd]
    have hcast : (t : ℝ) * ((t : ℝ) - 1) = 2 * (t.choose 2 : ℝ) := by
      have h1 : ((t * (t - 1) : ℕ) : ℝ) = ((2 * t.choose 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast [Nat.cast_sub (show 1 ≤ t by omega)] at h1
      exact h1
    have ht8R : (8 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_ge8
    nlinarith
  have hμ_lb : (t : ℝ) ^ 2 * p / 4 ≤ μ := by
    dsimp [μ]
    nlinarith
  have hμ_pos : 0 < μ := by
    have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
    have : 0 < (t : ℝ) ^ 2 * p / 4 := by positivity
    linarith
  set m : ℕ := Nat.ceil (μ / 8)
  have hm_ge : μ / 8 ≤ (m : ℝ) := Nat.le_ceil _
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hm_lb : (t : ℝ) ^ 2 * p / 32 ≤ (m : ℝ) := by linarith
  have hnp_eq : (n : ℝ) * p = (n : ℝ) ^ ((1 : ℝ) / 3 - δ) := by
    calc
      (n : ℝ) * p = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (- (2 : ℝ) / 3 - δ) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ (1 + (- (2 : ℝ) / 3 - δ)) := (Real.rpow_add hn_pos _ _).symm
      _ = (n : ℝ) ^ ((1 : ℝ) / 3 - δ) := by congr 1; ring
  have hnp_ge1' : 1 ≤ (n : ℝ) * p := by rwa [hnp_eq]
  have hn2p3 : (n : ℝ) ^ 2 * p ^ 3 = (n : ℝ) ^ (- 3 * δ) := by
    calc
      (n : ℝ) ^ 2 * p ^ 3
        = (n : ℝ) ^ ((2 : ℕ) : ℝ) * ((n : ℝ) ^ (- (2 : ℝ) / 3 - δ)) ^ ((3 : ℕ) : ℝ) := by
            rw [Real.rpow_natCast, Real.rpow_natCast]
      _ = (n : ℝ) ^ ((2 : ℕ) : ℝ) * (n : ℝ) ^ ((- (2 : ℝ) / 3 - δ) * ((3 : ℕ) : ℝ)) := by
            rw [← Real.rpow_mul hn_pos.le]
      _ = (n : ℝ) ^ (((2 : ℕ) : ℝ) + (- (2 : ℝ) / 3 - δ) * ((3 : ℕ) : ℝ)) :=
            (Real.rpow_add hn_pos _ _).symm
      _ = (n : ℝ) ^ (- 3 * δ) := by congr 1; push_cast; ring
  have hbase_B :
      Real.exp 1 * ((t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) / (m : ℝ) ≤
        Real.exp (-1) := by
    have hnum_le :
        (t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4 ≤
        2 * (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4 := by
      have h1 : (t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 * 1 ≤ (t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 * ((n : ℝ) * p) :=
        mul_le_mul_of_nonneg_left hnp_ge1' (by positivity)
      linarith
    have he1_le : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
    have hinv_e : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos 1) he1_le
    have hquot :
        Real.exp 1 * ((t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) / (m : ℝ) ≤
        192 * ((n : ℝ) ^ 2 * p ^ 3) := by
      rw [div_le_iff₀ hm_pos]
      have h1 : Real.exp 1 * ((t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) ≤
          3 * (2 * (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) := by
        calc
          Real.exp 1 * ((t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4)
            ≤ 3 * ((t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) :=
              mul_le_mul_of_nonneg_right he1_le (by positivity)
          _ ≤ 3 * (2 * (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) :=
              mul_le_mul_of_nonneg_left hnum_le (by norm_num)
      have h2 : 3 * (2 * (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) =
          192 * ((n : ℝ) ^ 2 * p ^ 3) * ((t : ℝ) ^ 2 * p / 32) := by ring
      have h3 : 192 * ((n : ℝ) ^ 2 * p ^ 3) * ((t : ℝ) ^ 2 * p / 32) ≤
          192 * ((n : ℝ) ^ 2 * p ^ 3) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hm_lb (by positivity)
      linarith
    have hneg_lt : (n : ℝ) ^ (- 3 * δ) < 1 / 1000 := hneg_small
    rw [hn2p3] at hquot
    linarith
  have hB_pow :
      (Real.exp 1 * ((t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) / (m : ℝ)) ^ m ≤
        Real.exp (- μ / 8) := by
    calc
      (Real.exp 1 * ((t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) / (m : ℝ)) ^ m
        ≤ (Real.exp (-1)) ^ m := pow_le_pow_left₀ (by positivity) hbase_B m
      _ = Real.exp (- (m : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp (- μ / 8) := Real.exp_le_exp.mpr (by linarith)
  have hprob :
      ((n.choose t : ℕ) : ℝ) *
        (Real.exp (- μ / 8) +
          (Real.exp 1 * ((t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) / (m : ℝ)) ^ m) < 1 := by
    have hchoose_le : ((n.choose t : ℕ) : ℝ) ≤ (n : ℝ) ^ t := by
      have hnat : n.choose t ≤ n ^ t := by
        calc
          n.choose t ≤ n.descFactorial t := by
            rw [Nat.descFactorial_eq_factorial_mul_choose]
            exact Nat.le_mul_of_pos_left _ (Nat.factorial_pos t)
          _ ≤ n ^ t := Nat.descFactorial_le_pow n t
      exact_mod_cast hnat
    have hnt_exp : (n : ℝ) ^ t = Real.exp ((t : ℝ) * Real.log (n : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hn_pos, mul_comm]
    have htp_lb : (1 / 2 : ℝ) * (n : ℝ) ^ δ ≤ (t : ℝ) * p := by
      have h1 : (n : ℝ) ^ ((2 : ℝ) / 3 + 2 * δ) * p = (n : ℝ) ^ δ := by
        calc
          (n : ℝ) ^ ((2 : ℝ) / 3 + 2 * δ) * (n : ℝ) ^ (- (2 : ℝ) / 3 - δ)
            = (n : ℝ) ^ (((2 : ℝ) / 3 + 2 * δ) + (- (2 : ℝ) / 3 - δ)) :=
              (Real.rpow_add hn_pos _ _).symm
          _ = (n : ℝ) ^ δ := by congr 1; ring
      have h2 := mul_le_mul_of_nonneg_right ht_half hp0
      linarith
    have hlog_lt : Real.log (n : ℝ) < (1 / 256 : ℝ) * (n : ℝ) ^ δ := by
      have hpow_pos : (0 : ℝ) < (n : ℝ) ^ δ := Real.rpow_pos_of_pos hn_pos δ
      exact (div_lt_iff₀ hpow_pos).mp hlog_small
    have hlog2_lt : Real.log 2 < Real.log (n : ℝ) :=
      Real.log_lt_log (by norm_num) (by exact_mod_cast (show 2 < n by omega))
    have ht_ge8R : (8 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_ge8
    have hexp_neg : Real.log 2 + (t : ℝ) * Real.log (n : ℝ) < μ / 8 := by
      have h1 : (t : ℝ) * Real.log (n : ℝ) < (t : ℝ) * ((1 / 256 : ℝ) * (n : ℝ) ^ δ) :=
        mul_lt_mul_of_pos_left hlog_lt (by linarith only [ht_ge8R])
      have h2 : (t : ℝ) * ((1 / 256 : ℝ) * (n : ℝ) ^ δ) ≤ (t : ℝ) * ((1 / 128 : ℝ) * ((t : ℝ) * p)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith only [ht_ge8R])
        linarith only [htp_lb]
      have h3 : Real.log 2 < (t : ℝ) * Real.log (n : ℝ) := by
        have hln_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
        nlinarith only [hlog2_lt, ht_ge8R, hln_pos]
      have h4 : (t : ℝ) * ((1 / 128 : ℝ) * ((t : ℝ) * p)) = (t : ℝ) ^ 2 * p / 128 := by ring
      have h5 : 0 ≤ (t : ℝ) ^ 2 * p := by positivity
      linarith only [h1, h2, h3, h4, h5, hμ_lb]
    calc
      ((n.choose t : ℕ) : ℝ) *
        (Real.exp (- μ / 8) +
          (Real.exp 1 * ((t : ℝ) ^ 2 * (n : ℝ) * p ^ 3 + (t : ℝ) ^ 2 * (n : ℝ) ^ 2 * p ^ 4) / (m : ℝ)) ^ m)
        ≤ (n : ℝ) ^ t * (2 * Real.exp (- μ / 8)) := by
          apply mul_le_mul hchoose_le (by linarith only [hB_pow]) (by positivity) (by positivity)
      _ = Real.exp (Real.log 2 + (t : ℝ) * Real.log (n : ℝ) - μ / 8) := by
          rw [hnt_exp, show Real.exp (Real.log 2 + (t : ℝ) * Real.log (n : ℝ) - μ / 8) =
            Real.exp (Real.log 2) * Real.exp ((t : ℝ) * Real.log (n : ℝ)) * Real.exp (- μ / 8) by
              rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring,
            Real.exp_log (by norm_num)]
          ring
      _ < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith only [hexp_neg])
      _ = 1 := Real.exp_zero
  obtain ⟨H, hgirth, hnoindep⟩ :=
    exists_girth_gt_four_no_indep hp0 hp1 (by omega) htn ⟨hμ_pos, rfl⟩ hprob
  obtain ⟨c, hchi, hc_lb⟩ := chromaticNumber_lower_of_no_indep (by omega) hnoindep
  have hch : c ≤ Erdos626.h 4 n := le_h_of_graph hgirth hchi
  have hc_real : (c : ℝ) ≤ (Erdos626.h 4 n : ℝ) := by exact_mod_cast hch
  have hpow_le : (n : ℝ) ^ ((1 : ℝ) / 3 - ε) ≤ (n : ℝ) / (t : ℝ) := by
    have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
    calc
      (n : ℝ) ^ ((1 : ℝ) / 3 - ε)
        ≤ (n : ℝ) ^ ((1 : ℝ) / 3 - 2 * δ) :=
          Real.rpow_le_rpow_of_exponent_le hn_ge1 (by linarith)
      _ = (n : ℝ) ^ (1 - ((2 : ℝ) / 3 + 2 * δ)) := by congr 1; ring
      _ = (n : ℝ) ^ (1 : ℝ) / (n : ℝ) ^ ((2 : ℝ) / 3 + 2 * δ) := Real.rpow_sub hn_pos _ _
      _ = (n : ℝ) / (n : ℝ) ^ ((2 : ℝ) / 3 + 2 * δ) := by rw [Real.rpow_one]
      _ ≤ (n : ℝ) / (t : ℝ) :=
          div_le_div_of_nonneg_left hn_pos.le ht_pos ht_le_real
  exact hpow_le.trans (hc_lb.trans hc_real)
