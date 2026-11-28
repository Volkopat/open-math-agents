import FormalConjectures.GreensOpenProblems.«29»

/-! Shorter proof of `Green29.green_29.variant` via density increment. -/

open Finset
open scoped Pointwise

private lemma invA {G : Type*} [Group G] {A : Finset G} {K : ℝ}
    (hA : IsApproximateSubgroup K (A : Set G)) {x : G} (hx : x ∈ A) : x⁻¹ ∈ A := by
  change x⁻¹ ∈ (A : Set G); rw [← hA.inv_eq_self]; simpa using hx

private lemma popular {G : Type*} [Group G] [DecidableEq G] {A B : Finset G} {K t : ℝ}
    (hK : 1 ≤ K) (ht : 0 < t) (hA : IsApproximateSubgroup K (A : Set G)) (hB : B ⊆ A)
    (hsize : t * A.card ≤ B.card) :
    ∃ S : Finset G, t ^ 2 / 2 * A.card ≤ S.card ∧
      ∀ g ∈ S, t ^ 2 / (2 * K) * A.card ≤ (B ∩ g • B).card := by
  classical
  let T := A * A; let q := t ^ 2 / (2 * K) * A.card; let f (g : G) : ℝ := (B ∩ g • B).card
  let S := T.filter fun g => q ≤ f g
  refine ⟨S, ?_, fun _ hg => (mem_filter.mp hg).2⟩
  have hpos : 0 < (A.card : ℝ) := by exact_mod_cast card_pos.mpr ⟨1, hA.one_mem⟩
  have hT : (T.card : ℝ) ≤ K * A.card := hA.card_mul_self_le
  have hsum : ∑ g ∈ T, f g = (B.card : ℝ) ^ 2 := by
    have h : ∑ g ∈ A * A, (B ∩ g • B).card = B.card ^ 2 := by
      simp_rw [card_inter_smul, ← card_mul_inv_eq_convolution_inv]
      rw [← card_eq_sum_card_fiberwise, card_product, sq]
      intro p hp; obtain ⟨hx, hy⟩ := mem_product.mp hp
      exact mul_mem_mul (hB hx) (invA hA (hB hy))
    dsimp [T, f]; exact_mod_cast h
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsplit : (B.card : ℝ) ^ 2 ≤ S.card * (A.card : ℝ) + T.card * q := by
    rw [← hsum, ← sum_filter_add_sum_filter_not T fun g => q ≤ f g]
    refine add_le_add ((sum_le_sum (g := fun _ => (A.card : ℝ)) fun g _ => by
        dsimp [f]; exact_mod_cast card_le_card ((inter_subset_left (s₂ := g • B)).trans hB)).trans_eq
        (by simp [S])) <|
      (sum_le_sum fun g hg => (lt_of_not_ge (mem_filter.mp hg).2).le).trans <| by
        simpa using mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_le T _) hq
  have hq' : K * (A.card : ℝ) * q = t ^ 2 / 2 * (A.card : ℝ) ^ 2 := by dsimp [q]; field_simp
  have hb2 := mul_self_le_mul_self (by positivity : 0 ≤ t * (A.card : ℝ)) hsize
  have hright := mul_le_mul_of_nonneg_right hT hq; rw [hq'] at hright
  exact le_of_mul_le_mul_right (a := (A.card : ℝ)) (by nlinarith) hpos

private lemma finish {G : Type*} [Group G] [DecidableEq G] {A B S : Finset G} {K : ℝ}
    (hA : IsApproximateSubgroup K (A : Set G)) (hB : B ⊆ A) (hne : B.Nonempty)
    (hs : ∀ g ∈ S, ((B * A).card : ℝ) - A.card / 16 ≤ ((B ∩ g • B) * A).card) :
    S ^ 8 ⊆ A ^ 4 := by
  let D := B * A
  have hD : A.card ≤ D.card := by
    obtain ⟨b, hb⟩ := hne
    simpa using card_le_card (show b • A ⊆ D from fun z hz => by
      obtain ⟨a, ha, rfl⟩ := mem_smul_finset.mp hz; exact mul_mem_mul hb ha)
  have hloss (g : G) (hg : g ∈ S) : ((D \ g • D).card : ℝ) ≤ A.card / 16 := by
    have sub : (B ∩ g • B) * A ⊆ D ∩ g • D := subset_inter (mul_subset_mul_right inter_subset_left) <|
      by change _ ⊆ g • (B * A); rw [← smul_mul_assoc]; exact mul_subset_mul_right inter_subset_right
    have h1 : (((B ∩ g • B) * A).card : ℝ) ≤ (D ∩ g • D).card := by exact_mod_cast card_le_card sub
    have h2 : ((D \ g • D).card : ℝ) + (D ∩ g • D).card = D.card := by
      exact_mod_cast card_sdiff_add_card_inter D (g • D)
    have := hs g hg; linarith
  have lpow : ∀ (k : ℕ) (w : G), w ∈ S ^ k → ((D \ w • D).card : ℝ) ≤ k * (A.card / 16) := by
    intro k; induction k with
    | zero => intro w hw; simp only [pow_zero, mem_one] at hw; subst w; simp
    | succ k ih =>
      intro w hw; rw [pow_succ] at hw; obtain ⟨g, hg, z, hz, rfl⟩ := mem_mul.mp hw
      have hmul : (D \ (g * z) • D).card ≤ (D \ g • D).card + (D \ z • D).card :=
        (card_le_card (show D \ (g * z) • D ⊆ (D \ g • D) ∪ g • (D \ z • D) from by
          rw [mul_smul, smul_finset_sdiff]; intro x hx; simp only [mem_sdiff, mem_union] at *; tauto)).trans <|
          (card_union_le ..).trans (by simp)
      have hh : ((D \ (g * z) • D).card : ℝ) ≤ (D \ g • D).card + (D \ z • D).card := by
        exact_mod_cast hmul
      push_cast; linarith [ih g hg, hloss z hz]
  intro w hw
  have hh := lpow 8 w hw
  have hpos : 0 < (A.card : ℝ) := by exact_mod_cast card_pos.mpr ⟨1, hA.one_mem⟩
  have hlt : (D \ w • D).card < D.card := by
    have hD' : (A.card : ℝ) ≤ D.card := by exact_mod_cast hD
    exact_mod_cast (show ((D \ w • D).card : ℝ) < D.card by norm_num at hh; linarith)
  have hi : (D ∩ w • D).Nonempty := card_pos.mp (by have := card_sdiff_add_card_inter D (w • D); omega)
  obtain ⟨z, hz⟩ := hi
  obtain ⟨x, hx, hxz⟩ := mem_smul_finset.mp (mem_inter.mp hz).2
  obtain ⟨a, ha, b, hb, hab⟩ := mem_mul.mp (mem_inter.mp hz).1
  obtain ⟨c, hc, d, hd, hcd⟩ := mem_mul.mp hx
  have eq : w = a * b * (d⁻¹ * c⁻¹) := by
    change w * x = z at hxz; rw [← mul_inv_rev, hcd, hab, ← hxz]; simp
  rw [eq, show 4 = 2 + 2 by decide, pow_add, sq]
  exact mul_mem_mul (mul_mem_mul (hB ha) hb) (mul_mem_mul (invA hA hd) (invA hA (hB hc)))

private lemma descent (K : ℝ) (hK : 1 ≤ K) (m : ℕ) :
    ∀ t : ℝ, 0 < t → ∃ c : ℝ, 0 < c ∧
      ∀ {G : Type*} [Group G] [DecidableEq G] (A B : Finset G),
        IsApproximateSubgroup K (A : Set G) → B ⊆ A →
        t * A.card ≤ B.card → ((B * A).card : ℝ) ≤ m * A.card / 16 →
        ∃ S : Finset G, c * A.card ≤ S.card ∧ S ^ 8 ⊆ A ^ 4 := by
  induction m with
  | zero =>
    intro t ht; refine ⟨1, one_pos, fun A B hA _ hsize hbudget => ?_⟩
    have hpos : 0 < (A.card : ℝ) := by exact_mod_cast card_pos.mpr ⟨1, hA.one_mem⟩
    have hb : B.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos ht hpos).trans_le hsize)
    have hd : 0 < ((B * A).card : ℝ) := by exact_mod_cast card_pos.mpr (hb.mul ⟨1, hA.one_mem⟩)
    simp only [Nat.cast_zero, zero_mul, zero_div] at hbudget; linarith
  | succ m ih =>
    intro t ht
    obtain ⟨c, hc, ih⟩ := ih _ (by positivity : 0 < t ^ 2 / (2 * K))
    refine ⟨min (t ^ 2 / 2) c, lt_min (by positivity) hc, fun A B hA hB hsize hbudget => ?_⟩
    obtain ⟨S, hS, hpop⟩ := popular hK ht hA hB hsize
    have hpos : 0 < (A.card : ℝ) := by exact_mod_cast card_pos.mpr ⟨1, hA.one_mem⟩
    have hb : B.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos ht hpos).trans_le hsize)
    by_cases h : ∀ g ∈ S, ((B * A).card : ℝ) - A.card / 16 ≤ ((B ∩ g • B) * A).card
    · exact ⟨S, (mul_le_mul_of_nonneg_right (min_le_left ..) hpos.le).trans hS, finish hA hB hb h⟩
    push Not at h; obtain ⟨g, hg, hsmall⟩ := h
    obtain ⟨S', hs', hp'⟩ := ih A (B ∩ g • B) hA (inter_subset_left.trans hB) (hpop g hg)
      (by push_cast at hbudget; linarith)
    exact ⟨S', (mul_le_mul_of_nonneg_right (min_le_right ..) hpos.le).trans hs', hp'⟩

theorem OMA.solution : type_of% @Green29.green_29.variant := by
  intro K hK
  obtain ⟨m, hm⟩ := exists_nat_ge (16 * K)
  obtain ⟨c, hc, h⟩ := descent K hK m 1 one_pos
  exact ⟨c, hc, fun A hA => h A A hA Subset.rfl (by simp) <| by
    have := hA.card_mul_self_le
    nlinarith [mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)]⟩
