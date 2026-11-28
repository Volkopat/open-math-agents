import FormalConjectures.ErdosProblems.«1086»

-- Reduction Erdos1086.erdos_1086.variants.raz_sharir.R1 of Erdős Problem 1086 — raz sharir
-- Credit: @B221393
-- Proves scale invariance (reducing arbitrary positive area a to unit area 1) and splits
-- unit-area triangles into rich-line triangles (H1) and poor-line triangles (H2) at the
-- Raz-Sharir threshold n^(5/9).

namespace OMA.R_Erdos1086_erdos_1086_variants_raz_sharir_R1

open Filter Asymptotics
open scoped EuclideanGeometry

/-- Rich-line unit-area triangles: unit-area triangles having at least one side whose affine line
contains at least `n^(5/9)` points of `P`. -/
def H1 : Prop :=
  open scoped Classical in
  ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Finset ℝ²,
    (((P.powersetCard 3).filter fun T =>
      (∃ p q r : ℝ², T = {p, q, r} ∧ |EuclideanGeometry.triangle_area p q r| = 1) ∧
      (∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧
        ((P.card : ℝ) ^ (5 / 9 : ℝ)) ≤
          ((P.filter fun w => w ∈ affineSpan ℝ ({u, v} : Set ℝ²)).card : ℝ))).card : ℝ) ≤
      C * (P.card : ℝ) ^ (20 / 9 : ℝ)

/-- Poor-line unit-area triangles: unit-area triangles whose every side line contains fewer than
`n^(5/9)` points of `P` (the generic Raz-Sharir polynomial-partitioning core). -/
def H2 : Prop :=
  open scoped Classical in
  ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Finset ℝ²,
    (((P.powersetCard 3).filter fun T =>
      (∃ p q r : ℝ², T = {p, q, r} ∧ |EuclideanGeometry.triangle_area p q r| = 1) ∧
      ¬ (∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧
        ((P.card : ℝ) ^ (5 / 9 : ℝ)) ≤
          ((P.filter fun w => w ∈ affineSpan ℝ ({u, v} : Set ℝ²)).card : ℝ))).card : ℝ) ≤
      C * (P.card : ℝ) ^ (20 / 9 : ℝ)

lemma triangle_area_smul (t : ℝ) (p q r : ℝ²) :
    EuclideanGeometry.triangle_area (t • p) (t • q) (t • r) =
      t ^ 2 * EuclideanGeometry.triangle_area p q r := by
  simp only [EuclideanGeometry.triangle_area, vsub_eq_sub, ← smul_sub,
    map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

lemma abs_triangle_area_inv_sqrt {a : ℝ} (ha : 0 < a) (p q r : ℝ²) :
    |EuclideanGeometry.triangle_area ((Real.sqrt a)⁻¹ • p) ((Real.sqrt a)⁻¹ • q)
      ((Real.sqrt a)⁻¹ • r)| = 1 ↔ |EuclideanGeometry.triangle_area p q r| = a := by
  rw [triangle_area_smul, abs_mul, abs_of_nonneg (sq_nonneg _), inv_pow, Real.sq_sqrt ha.le]
  constructor
  · intro h
    calc |EuclideanGeometry.triangle_area p q r|
        = a * (a⁻¹ * |EuclideanGeometry.triangle_area p q r|) := by
          rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
      _ = a := by rw [h, mul_one]
  · intro h
    rw [h, inv_mul_cancel₀ ha.ne']

lemma triangleAreaCount_scale_to_one (P : Finset ℝ²) {a : ℝ} (ha : 0 < a) :
    Erdos1086.triangleAreaCount P a =
      Erdos1086.triangleAreaCount (P.image ((Real.sqrt a)⁻¹ • ·)) 1 := by
  classical
  let t : ℝ := (Real.sqrt a)⁻¹
  have ht : t ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 ha).ne'
  have hinj : Function.Injective (fun x : ℝ² => t • x) := smul_right_injective ℝ² ht
  unfold Erdos1086.triangleAreaCount
  refine Finset.card_bij (fun T _ => T.image (t • ·)) ?_ ?_ ?_
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hT ⊢
    obtain ⟨⟨hTP, hTcard⟩, p, q, r, rfl, harea⟩ := hT
    refine ⟨⟨Finset.image_subset_image hTP, ?_⟩, t • p, t • q, t • r, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj, hTcard]
    · simp
    · exact (abs_triangle_area_inv_sqrt ha p q r).2 harea
  · intro T₁ _ T₂ _ heq
    exact Finset.image_injective hinj heq
  · intro T' hT'
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hT'
    obtain ⟨⟨hT'P, hT'card⟩, p', q', r', hT'eq, harea'⟩ := hT'
    obtain ⟨T, hTP, rfl⟩ := Finset.subset_image_iff.1 hT'P
    have hTcard : T.card = 3 := by
      rwa [Finset.card_image_of_injective _ hinj] at hT'card
    have hp' : p' ∈ T.image (t • ·) := by rw [hT'eq]; simp
    have hq' : q' ∈ T.image (t • ·) := by rw [hT'eq]; simp
    have hr' : r' ∈ T.image (t • ·) := by rw [hT'eq]; simp
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hp'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hq'
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hr'
    have hTeq : T = {p, q, r} := by
      apply Finset.image_injective hinj
      simpa using hT'eq
    refine ⟨T, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨hTP, hTcard⟩, p, q, r, hTeq, (abs_triangle_area_inv_sqrt ha p q r).1 harea'⟩

lemma unit_area_bound_of_hyp (h1 : H1) (h2 : H2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Finset ℝ²,
      (Erdos1086.triangleAreaCount P 1 : ℝ) ≤ C * (P.card : ℝ) ^ (20 / 9 : ℝ) := by
  classical
  obtain ⟨C₁, hC₁, hH₁⟩ := h1
  obtain ⟨C₂, hC₂, hH₂⟩ := h2
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun P => ?_⟩
  let S := (P.powersetCard 3).filter fun T =>
    ∃ p q r : ℝ², T = {p, q, r} ∧ |EuclideanGeometry.triangle_area p q r| = 1
  let rich : Finset ℝ² → Prop := fun T =>
    ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧
      ((P.card : ℝ) ^ (5 / 9 : ℝ)) ≤
        ((P.filter fun w => w ∈ affineSpan ℝ ({u, v} : Set ℝ²)).card : ℝ)
  have hsplit : S.card = (S.filter rich).card + (S.filter fun T => ¬ rich T).card :=
    (Finset.card_filter_add_card_filter_not rich).symm
  have hS1 : S.filter rich = (P.powersetCard 3).filter fun T =>
      (∃ p q r : ℝ², T = {p, q, r} ∧ |EuclideanGeometry.triangle_area p q r| = 1) ∧ rich T := by
    ext T; simp only [S, Finset.mem_filter, and_assoc]
  have hS2 : (S.filter fun T => ¬ rich T) = (P.powersetCard 3).filter fun T =>
      (∃ p q r : ℝ², T = {p, q, r} ∧ |EuclideanGeometry.triangle_area p q r| = 1) ∧ ¬ rich T := by
    ext T; simp only [S, Finset.mem_filter, and_assoc]
  have hbound1 : ((S.filter rich).card : ℝ) ≤ C₁ * (P.card : ℝ) ^ (20 / 9 : ℝ) := by
    rw [hS1]; exact hH₁ P
  have hbound2 : ((S.filter fun T => ¬ rich T).card : ℝ) ≤ C₂ * (P.card : ℝ) ^ (20 / 9 : ℝ) := by
    rw [hS2]; exact hH₂ P
  have hcount : (Erdos1086.triangleAreaCount P 1 : ℝ) = (S.card : ℝ) := by
    unfold Erdos1086.triangleAreaCount
    congr 1
  rw [hcount, hsplit, Nat.cast_add]
  linarith

theorem main : H1 → H2 → type_of% @Erdos1086.erdos_1086.variants.raz_sharir := by
  intro h1 h2
  obtain ⟨C, hC, hU⟩ := unit_area_bound_of_hyp h1 h2
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hg : (Erdos1086.g n : ℝ) ≤ C * (n : ℝ) ^ (20 / 9 : ℝ) := by
    unfold Erdos1086.g
    by_cases hne : {m : ℕ | ∃ (P : Finset ℝ²) (a : ℝ),
        P.card = n ∧ 0 < a ∧ Erdos1086.triangleAreaCount P a = m}.Nonempty
    · have hle : ∀ m ∈ {m : ℕ | ∃ (P : Finset ℝ²) (a : ℝ),
          P.card = n ∧ 0 < a ∧ Erdos1086.triangleAreaCount P a = m},
          (m : ℝ) ≤ C * (n : ℝ) ^ (20 / 9 : ℝ) := by
        rintro m ⟨P, a, hPcard, ha, rfl⟩
        rw [triangleAreaCount_scale_to_one P ha]
        have hinj : Function.Injective (fun x : ℝ² => (Real.sqrt a)⁻¹ • x) :=
          smul_right_injective ℝ² (inv_ne_zero (Real.sqrt_pos.2 ha).ne')
        have hcard : (P.image ((Real.sqrt a)⁻¹ • ·)).card = n := by
          rw [Finset.card_image_of_injective _ hinj, hPcard]
        simpa [hcard] using hU (P.image ((Real.sqrt a)⁻¹ • ·))
      have hnat : ∀ m ∈ {m : ℕ | ∃ (P : Finset ℝ²) (a : ℝ),
          P.card = n ∧ 0 < a ∧ Erdos1086.triangleAreaCount P a = m},
          m ≤ ⌊C * (n : ℝ) ^ (20 / 9 : ℝ)⌋₊ := fun m hm =>
        Nat.le_floor (hle m hm)
      have hsup : sSup {m : ℕ | ∃ (P : Finset ℝ²) (a : ℝ),
          P.card = n ∧ 0 < a ∧ Erdos1086.triangleAreaCount P a = m} ≤
          ⌊C * (n : ℝ) ^ (20 / 9 : ℝ)⌋₊ := csSup_le hne hnat
      exact (Nat.cast_le.2 hsup).trans (Nat.floor_le (by positivity))
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, csSup_empty]
      simp only [Nat.bot_eq_zero, Nat.cast_zero]
      positivity
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  exact hg

end OMA.R_Erdos1086_erdos_1086_variants_raz_sharir_R1
