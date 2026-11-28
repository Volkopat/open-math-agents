import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

/-!
# Erdős 3 on the 4-adic blocks from summable extremal densities

The target is step H1 of reduction R2 of Erdős 142 (pull request 3320): every set supported on
the blocks (4 * 4^j, 5 * 4^j] with divergent reciprocal sum contains k-term progressions for
every k ≥ 3. This file proves the converse of the packing argument of R2: if the normalized
extremal numbers r_k(4^j) / 4^j are summable, then a k-progression-free set on the blocks has
convergent reciprocal sum, since its piece in block j is a translate of a k-progression-free
subset of [1, 4^j] whose reciprocals sum to at most r_k(4^j) / (4 * 4^j).

The two hypotheses separate the lengths. The three-term case H1 is a known theorem: it follows
from the Bloom–Sisask bound and from the Kelley–Meka bound, which is already formalized in this
repository (proofs/Erdos3.erdos_3.variants.kelley_meka.lean). The case of length at least four,
H2, is the genuinely hard part; it follows from the quasipolynomial bounds of the 2026 OpenAI
preprint Quasipolynomial Bounds for Arithmetic Progressions. The summability formulation is the
one recorded by Green and Tao (New bounds for Szemerédi's theorem III), referring to Tao and Vu,
Additive Combinatorics, Exercise 10.0.6. The progression-freeness criterion below follows the
lemma apFree_iff of reduction R3 of Erdős 142 (pull request 7180).
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1

open Erdos142 Filter

/-- The three-term extremal densities on the scales 4^j are summable. -/
def H1 : Prop := Summable (fun j : ℕ ↦ (r 3 (4 ^ j) : ℝ) / (4 : ℝ) ^ j)

/-- The same summability holds for every progression length at least four. -/
def H2 : Prop := ∀ k : ℕ, 4 ≤ k → Summable (fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j)

/-- A finite set with no progression in the explicit sense is progression free. -/
lemma free_of_noAP {V : Finset ℕ} {k : ℕ} (hk : 1 < k)
    (hno : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ V) :
    (V : Set ℕ).IsAPOfLengthFree k := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  intro T hsub hT
  obtain ⟨a, d, hcard, hterms⟩ := hT
  have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
    rw [hterms]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  have hd : 0 < d := by
    by_contra! h
    have he : d = 0 := Nat.eq_zero_of_le_zero h
    have hs : T = {a} := by
      apply Set.Subset.antisymm
      · rw [hterms, he]
        rintro _ ⟨i, -, rfl⟩
        simp
      · apply Set.singleton_subset_iff.mpr
        simpa using hmem 0 (by omega)
    rw [hs] at hcard
    exact hk'.ne (by simpa using hcard)
  exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

/-- The block index of an element of the block (4 * 4^j, 5 * 4^j]. -/
lemma log_of_mem_block {j x : ℕ} (h1 : 4 * 4 ^ j < x) (h2 : x ≤ 5 * 4 ^ j) :
    Nat.log 4 x - 1 = j := by
  have hlow : 4 ^ (j + 1) ≤ x := by rw [pow_succ]; omega
  have hhigh : x < 4 ^ (j + 1 + 1) := by
    have : 5 * 4 ^ j < 4 ^ (j + 1 + 1) := by rw [pow_succ, pow_succ]; omega
    omega
  rw [Nat.log_eq_of_pow_le_of_lt_pow hlow hhigh]
  omega

/-- A progression-free set meets each block in at most the extremal number of elements. -/
lemma block_card_le {A : Set ℕ} {k : ℕ} (hk : 1 < k)
    (hno : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A) (j : ℕ) (U : Finset ℕ)
    (hU : ∀ x ∈ U, x ∈ A ∧ 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) :
    U.card ≤ r k (4 ^ j) := by
  classical
  let V := U.image (fun x ↦ x - 4 * 4 ^ j)
  have hinj : Set.InjOn (fun x ↦ x - 4 * 4 ^ j) U := by
    intro x hx y hy hxy
    have := (hU x hx).2.1
    have := (hU y hy).2.1
    simp only at hxy
    omega
  have hcard : V.card = U.card := Finset.card_image_of_injOn hinj
  have hsub : V ⊆ Finset.Icc 1 (4 ^ j) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨-, h1, h2⟩ := hU x hx
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hfree : (V : Set ℕ).IsAPOfLengthFree k := by
    apply free_of_noAP hk
    rintro ⟨b, d, hd, hb⟩
    refine hno ⟨b + 4 * 4 ^ j, d, hd, fun i hi ↦ ?_⟩
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp (hb i hi)
    have h1 := (hU x hx).2.1
    have he : b + 4 * 4 ^ j + i * d = x := by omega
    rw [he]
    exact (hU x hx).1
  rw [← hcard]
  exact OMA.R_Erdos142_erdos_142_variants_lower_R2.card_le_maxCard hsub hfree

/-- Summable block densities force the reciprocal sum of a progression-free set supported on
the blocks to converge. -/
lemma summable_of_blocks {A : Set ℕ} {k : ℕ} (hk : 1 < k)
    (hA : ∀ x ∈ A, ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j)
    (hno : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A)
    (hs : Summable (fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j)) :
    Summable (A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹)) := by
  classical
  set f := A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹)
  have hf : ∀ n, 0 ≤ f n := fun n ↦
    Set.indicator_nonneg (fun m _ ↦ inv_nonneg.mpr (Nat.cast_nonneg m)) n
  set g : ℕ → ℝ := fun j ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j
  have hg : ∀ j, 0 ≤ g j := fun j ↦ by positivity
  apply summable_of_sum_range_le hf (c := ∑' j, g j)
  intro M
  let blk : ℕ → ℕ := fun x ↦ Nat.log 4 x - 1
  rw [← Finset.sum_fiberwise_of_maps_to (g := blk) (t := (Finset.range M).image blk)
    (fun x hx ↦ Finset.mem_image_of_mem blk hx)]
  refine le_trans ?_ (hs.sum_le_tsum ((Finset.range M).image blk) (fun j _ ↦ hg j))
  apply Finset.sum_le_sum
  intro j _
  let U := (Finset.range M).filter (fun x ↦ x ∈ A ∧ blk x = j)
  have hU : ∀ x ∈ U, x ∈ A ∧ 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j := by
    intro x hx
    obtain ⟨-, hxA, hxj⟩ := Finset.mem_filter.mp hx
    obtain ⟨j', h1, h2⟩ := hA x hxA
    have := log_of_mem_block h1 h2
    have hj : j' = j := by rw [← this]; exact hxj
    subst hj
    exact ⟨hxA, h1, h2⟩
  have hcardU := block_card_le hk hno j U hU
  have hpos : (0 : ℝ) < 4 * (4 : ℝ) ^ j := by positivity
  calc ∑ x ∈ (Finset.range M).filter (fun x ↦ blk x = j), f x
      = ∑ x ∈ U, f x := by
        refine (Finset.sum_subset (fun x hx ↦ ?_) (fun x hx hxU ↦ ?_)).symm
        · obtain ⟨h1, -, h3⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨h1, h3⟩
        · obtain ⟨h1, h3⟩ := Finset.mem_filter.mp hx
          have hxA : x ∉ A := fun hxA ↦ hxU (Finset.mem_filter.mpr ⟨h1, hxA, h3⟩)
          simp [f, Set.indicator_of_notMem hxA]
    _ ≤ ∑ _x ∈ U, (4 * (4 : ℝ) ^ j)⁻¹ := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨hxA, h1, -⟩ := hU x hx
        simp only [f, Set.indicator_of_mem hxA]
        apply inv_anti₀ hpos
        exact_mod_cast h1.le
    _ = (U.card : ℝ) * (4 * (4 : ℝ) ^ j)⁻¹ := by simp
    _ ≤ (r k (4 ^ j) : ℝ) * (4 * (4 : ℝ) ^ j)⁻¹ := by
        gcongr
    _ ≤ g j := by
        simp only [g, div_eq_mul_inv]
        gcongr
        linarith [pow_pos (by norm_num : (0 : ℝ) < 4) j]

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2.H1 := by
  intro h1 h2 A hA hns k hk
  by_contra hno
  apply hns
  have hs : Summable (fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j) := by
    rcases eq_or_lt_of_le hk with rfl | hk4
    · exact h1
    · exact h2 k hk4
  exact summable_of_blocks (by omega) hA hno hs

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1
