import FormalConjectures.ErdosProblems.«587»

/-! Divisor descent for the Nguyen–Vu bound on square-sum-free sets. -/

namespace OMA.R_Erdos587_erdos_587_variants_nguyen_vu_R1

open scoped BigOperators

lemma interval_subset_sums (a k x : ℕ) (hk : 0 < k) (hx : x ≤ k * k) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc a (a + 2 * k) ∧ S.card = k ∧
      (∑ s ∈ S, s) = (∑ i ∈ Finset.range k, (a + i)) + x := by
  let q := x / k
  let r := x % k
  have hq : q ≤ k := Nat.div_le_of_le_mul hx
  have hr : r < k := Nat.mod_lt _ hk
  have hqr : k * q + r = x := by simpa [q, r, Nat.add_comm] using (Nat.mod_add_div x k)
  let f := fun i : ℕ => a + q + i
  have hinj : Function.Injective f := by
    intro i j h
    exact Nat.add_left_cancel h
  let block := (Finset.range (k + 1)).image f
  let missing := f (k - r)
  have hmem : missing ∈ block := by
    apply Finset.mem_image_of_mem
    exact Finset.mem_range.mpr (by omega)
  have hblock : block ⊆ Finset.Icc a (a + 2 * k) := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    have hi' := Finset.mem_range.mp hi
    change a + q + i ∈ Finset.Icc a (a + 2 * k)
    exact Finset.mem_Icc.mpr ⟨(Nat.le_add_right a q).trans (Nat.le_add_right _ i), by omega⟩
  have hcard : block.card = k + 1 := by simp [block, Finset.card_image_of_injective _ hinj]
  refine ⟨block.erase missing, (Finset.erase_subset _ _).trans hblock, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem hmem, hcard]
    omega
  · have hsum : (∑ s ∈ block, s) = (∑ i ∈ Finset.range k, (a + i)) + k * q + f k := by
      rw [show block = (Finset.range (k + 1)).image f from rfl,
        Finset.sum_image (fun _ _ _ _ h => hinj h), Finset.sum_range_succ]
      have hshift : (∑ i ∈ Finset.range k, f i) = (∑ i ∈ Finset.range k, (a + i)) + k * q := by
        simp only [f, show ∀ i, a + q + i = a + i + q by omega, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
      rw [hshift]
    have herase := Finset.sum_erase_add block (fun s : ℕ => s) hmem
    change (∑ s ∈ block.erase missing, s) + missing = _ at herase
    rw [hsum] at herase
    change (∑ s ∈ block.erase missing, s) + (a + q + (k - r)) =
      (∑ i ∈ Finset.range k, (a + i)) + k * q + (a + q + k) at herase
    omega

lemma next_weighted_square (p base k : ℕ) (hp : 0 < p)
    (hweight : 4 * p ≤ k * k) (hbase : 16 * p * base ≤ (k * k) * (k * k)) :
    ∃ z : ℕ, base < p * (z * z) ∧ p * (z * z) ≤ base + k * k := by
  let r := (base / p).sqrt
  have hrsq : p * (r * r) ≤ base := by
    simpa only [Nat.mul_comm p] using (Nat.le_div_iff_mul_le hp).mp (Nat.sqrt_le (base / p))
  have hright : base < p * ((r + 1) * (r + 1)) := by
    rw [Nat.mul_comm p]
    exact (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_sqrt (base / p))
  have hsquare : (4 * (p * r)) * (4 * (p * r)) ≤ (k * k) * (k * k) := by
    calc
      _ = 16 * p * (p * (r * r)) := by ring
      _ ≤ 16 * p * base := Nat.mul_le_mul_left _ hrsq
      _ ≤ _ := hbase
  have hrad : 4 * (p * r) ≤ k * k := by nlinarith only [hsquare]
  refine ⟨r + 1, hright, ?_⟩
  calc
    p * ((r + 1) * (r + 1)) = p * (r * r) + 2 * (p * r) + p := by ring
    _ ≤ base + k * k := by omega

lemma square_in_progression_sums (a k p N : ℕ) (hk : 0 < k) (hp : 0 < p)
    (hspan : p * (a + 2 * k) ≤ N) (hdense : 16 * N ≤ k * k * k) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc a (a + 2 * k) ∧ S.Nonempty ∧
      ∃ z : ℕ, (∑ s ∈ S, s) = p * (z * z) := by
  let base := ∑ i ∈ Finset.range k, (a + i)
  have hsum : p * base ≤ k * N := by
    unfold base
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _i ∈ Finset.range k, N := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact (Nat.mul_le_mul_left p (show a + i ≤ a + 2 * k by omega)).trans hspan
      _ = _ := by simp
  have hweight : 4 * p ≤ k * k := by
    have hsmall : p * (2 * k) ≤ N :=
      (Nat.mul_le_mul_left p (Nat.le_add_left _ _)).trans hspan
    have hscale : (4 * p) * k ≤ (k * k) * k := by nlinarith [hsmall, hdense]
    exact Nat.le_of_mul_le_mul_right hscale hk
  have hbase : 16 * p * base ≤ (k * k) * (k * k) := by
    calc
      _ = 16 * (p * base) := by ring
      _ ≤ 16 * (k * N) := Nat.mul_le_mul_left _ hsum
      _ = k * (16 * N) := by ring
      _ ≤ k * (k * k * k) := Nat.mul_le_mul_left _ hdense
      _ = _ := by ring
  obtain ⟨z, hzlo, hzhi⟩ := next_weighted_square p base k hp hweight hbase
  obtain ⟨S, hS, hcard, hvalue⟩ := interval_subset_sums a k (p * (z * z) - base) hk (by omega)
  change (∑ s ∈ S, s) = base + (p * (z * z) - base) at hvalue
  exact ⟨S, hS, Finset.card_pos.mp (hcard ▸ hk), z, by omega⟩

-- The remaining estimate concerns sets with neither a nearly common divisor
-- nor a long interval of consecutive multiples.
def H1 : Prop :=
  ∃ᵉ (D > 0) (C > 0), ∀ᶠ N : ℕ in Filter.atTop,
    ∀ p : ℕ, 0 < p → ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 (N / p) →
      (∀ d : ℕ, 2 ≤ d → B.card ≤ 2 * (N.log2 + 1) * (B.filter (fun b => ¬ d ∣ b)).card) →
      (∀ a k d : ℕ, 0 < k → 0 < d → 16 * N ≤ k * k * k →
        ¬ (Finset.Icc a (a + 2 * k)).image (fun b => d * b) ⊆ B) →
      (∀ S ⊆ B, S.Nonempty → ∀ z : ℕ, (∑ b ∈ S, b) ≠ p * (z * z)) →
      (B.card : ℝ) ≤ C * Real.nthRoot 3 N * (N : ℝ).log ^ D

-- Dividing a subset by a common factor leaves at least half the original elements
-- and makes it costly to impose any further common divisor.
def H2 : Prop :=
  ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N →
    ∃ p : ℕ, 0 < p ∧ ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 (N / p) ∧
      B.image (fun b => p * b) ⊆ A ∧ A.card ≤ 2 * B.card ∧
      ∀ d : ℕ, 2 ≤ d → B.card ≤ 2 * (N.log2 + 1) * (B.filter (fun b => ¬ d ∣ b)).card

theorem main : H1 → H2 → type_of% @Erdos587.erdos_587.variants.nguyen_vu := by
  rintro ⟨D, hD, C, hC, hbound⟩ hcore
  refine ⟨D, hD, 2 * C, by positivity, ?_⟩
  filter_upwards [hbound] with N hN
  let candidates := (Finset.Icc 1 N).powerset.filter (fun A =>
    ∀ S ⊆ A, S ≠ ⊥ → ¬ IsSquare (∑ a ∈ S, a))
  change ((candidates.sup Finset.card : ℕ) : ℝ) ≤ _
  have hzero : (∅ : Finset ℕ) ∈ candidates := by simp [candidates]
  obtain ⟨A, hA, hmax⟩ := Finset.exists_mem_eq_sup candidates ⟨_, hzero⟩ Finset.card
  obtain ⟨hsub, hsquare⟩ := Finset.mem_filter.mp hA
  obtain ⟨p, hp, B, hB, himage, hsize, hrobust⟩ := hcore N A (Finset.mem_powerset.mp hsub)
  have hweighted : ∀ S ⊆ B, S.Nonempty → ∀ z : ℕ, (∑ b ∈ S, b) ≠ p * (z * z) := by
    intro S hSB hS z hz
    let f : ℕ → ℕ := fun b => p * b
    have hinj : Function.Injective f := fun _ _ h => Nat.eq_of_mul_eq_mul_left hp h
    have hSA : S.image f ⊆ A := (Finset.image_mono f hSB).trans himage
    apply hsquare (S.image f) hSA (hS.image f).ne_empty
    refine ⟨p * z, ?_⟩
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    change (∑ b ∈ S, p * b) = (p * z) * (p * z)
    rw [← Finset.mul_sum, hz]
    ring
  have hnolong : ∀ a k d : ℕ, 0 < k → 0 < d → 16 * N ≤ k * k * k →
      ¬ (Finset.Icc a (a + 2 * k)).image (fun b => d * b) ⊆ B := by
    intro a k d hk hd hdense hrun
    have hend : a + 2 * k ∈ Finset.Icc a (a + 2 * k) := by simp
    have hlast := (Finset.mem_Icc.mp (hB (hrun (Finset.mem_image_of_mem _ hend)))).2
    have hspan : p * d * (a + 2 * k) ≤ N := by
      simpa only [Nat.mul_assoc, Nat.mul_comm _ p] using (Nat.le_div_iff_mul_le hp).mp hlast
    obtain ⟨T, hT, hTne, z, hsum⟩ :=
      square_in_progression_sums a k (p * d) N hk (Nat.mul_pos hp hd) hspan hdense
    let f : ℕ → ℕ := fun b => d * b
    have hinj : Function.Injective f := fun _ _ h => Nat.eq_of_mul_eq_mul_left hd h
    apply hweighted (T.image f) ((Finset.image_mono f hT).trans hrun) (hTne.image f) (d * z)
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    change (∑ b ∈ T, d * b) = p * (d * z * (d * z))
    rw [← Finset.mul_sum, hsum]
    ring
  have hsmall := hN p hp B hB hrobust hnolong hweighted
  rw [hmax]
  calc
    (A.card : ℝ) ≤ 2 * (B.card : ℝ) := by exact_mod_cast hsize
    _ ≤ 2 * (C * Real.nthRoot 3 N * (N : ℝ).log ^ D) := by linarith
    _ = _ := by ring

end OMA.R_Erdos587_erdos_587_variants_nguyen_vu_R1
