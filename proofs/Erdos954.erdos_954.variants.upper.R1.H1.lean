import OMAReductions.R_Erdos954_erdos_954_variants_upper_R1

/-!
Induct on the number of indices in a gap. The upper half of the gap is
already long enough to fit the first few terms of Rosen's sequence. Adding one
of those terms to each index in the lower half gives a rectangle of pairs whose
sums lie in the original gap. This is the interval-counting argument in the
reduction by @LordMike.
-/

open Erdos954 Finset
open OMA.R_Erdos954_erdos_954_variants_upper_R1

namespace OMA.Erdos954Growth

private noncomputable abbrev pairs (n x : ℕ) :=
  (range (n + 1) ×ˢ range (n + 1)).filter
    fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ 1 ≤ p.2 ∧ rosen p.1 + rosen p.2 ≤ x

private theorem memPairs {n x : ℕ} {p : ℕ × ℕ} :
    p ∈ pairs n x ↔ p.1 ≤ n ∧ p.2 ≤ n ∧ p.1 ≤ p.2 ∧ 1 ≤ p.2 ∧
      rosen p.1 + rosen p.2 ≤ x := by
  simp [pairs, and_assoc]

private theorem pairsMonoIndex {m n x : ℕ} (h : m ≤ n) : pairs m x ⊆ pairs n x := by
  intro p hp
  obtain ⟨h₀, h₁, h₂⟩ := memPairs.mp hp
  exact memPairs.mpr ⟨h₀.trans h, h₁.trans h, h₂⟩

private theorem pairsMonoSum {n x y : ℕ} (h : x ≤ y) : pairs n x ⊆ pairs n y := by
  intro p hp
  obtain ⟨h₀, h₁, h₂, h₃, h₄⟩ := memPairs.mp hp
  exact memPairs.mpr ⟨h₀, h₁, h₂, h₃, h₄.trans h⟩

private theorem rosenUpper (r : ℕ) : rosen r ≤ r ^ 2 + 1 := by
  rcases r with _ | _ | k
  · simp [rosen_zero]
  · simp [rosen_one]
  rw [rosen_add_two]
  apply Nat.sInf_le
  apply Nat.lt_succ_of_le
  simpa only [← pow_two] using pairCount_le_sq rosen (k + 1) ((k + 2) ^ 2 + 1)

private theorem pairCountAtMost {n : ℕ} (hn : 2 ≤ n) :
    (pairs n (rosen n)).card ≤ rosen n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hsub : pairs (k + 2) (rosen (k + 2)) ⊆
      insert (0, k + 2) (pairs (k + 1) (rosen (k + 2))) := by
    intro p hp
    obtain ⟨h₀, h₁, h₂, h₃, h₄⟩ := memPairs.mp hp
    by_cases h : p.2 = k + 2
    · rw [h] at h₄
      have hz : rosen p.1 = rosen 0 := by rw [rosen_zero]; omega
      exact mem_insert.mpr (Or.inl (Prod.ext (rosen_strictMono.injective hz) h))
    · exact mem_insert_of_mem (memPairs.mpr ⟨by omega, by omega, h₂, h₃, h₄⟩)
  have h₀ := card_le_card hsub
  have h₁ := card_insert_le (a := (0, k + 2)) (s := pairs (k + 1) (rosen (k + 2)))
  have h₂ := rosen_spec k
  change (pairs (k + 1) (rosen (k + 2))).card < rosen (k + 2) at h₂
  omega

private theorem pairCountAtLeast {m n : ℕ} (hmn : m ≤ n) :
    rosen m ≤ (pairs n (rosen m)).card := by
  apply le_trans _ (card_le_card (pairsMonoIndex hmn))
  rcases m with _ | _ | k
  · simp [rosen_zero]
  · rw [rosen_one]
    exact card_pos.mpr ⟨(0, 1), by simp [rosen_zero, rosen_one]⟩
  exact le_pairCount_of_le k (rosen (k + 2)) le_rfl

private theorem pairsInGap {m n : ℕ} (hmn : m ≤ n) (hn : 2 ≤ n) :
    (pairs n (rosen n) \ pairs n (rosen m)).card ≤ rosen n - rosen m := by
  rw [card_sdiff_of_subset (pairsMonoSum (rosen_strictMono.monotone hmn))]
  have h₀ := pairCountAtMost hn
  have h₁ := pairCountAtLeast hmn
  omega

private theorem allGaps (M : ℕ) : ∀ n : ℕ, M ≤ n →
    M ^ 2 ≤ 100 * (rosen n - rosen (n - M)) := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro n hn
    by_cases hM : M ≤ 100
    · have hs := rosen_strictMono.add_le_nat M (n - M)
      rw [Nat.add_sub_of_le hn] at hs
      rw [pow_two]
      apply Nat.mul_le_mul hM
      omega
    let r := M / 22
    let h := M / 2
    have hr : 4 ≤ r := by dsimp [r]; omega
    have hfit : 10 * r + 2 ≤ h := by dsimp [r, h]; omega
    have hsmall : h < M := by dsimp [h]; omega
    have hgap := ih h hsmall n (hsmall.le.trans hn)
    have hsq := Nat.pow_le_pow_left hfit 2
    have hcalc : 100 * (r ^ 2 + 1) ≤ (10 * r + 2) ^ 2 := by nlinarith
    have hroom₀ := ((Nat.mul_le_mul_left 100 (rosenUpper r)).trans hcalc).trans (hsq.trans hgap)
    have hroom : rosen r ≤ rosen n - rosen (n - h) := by omega
    have hsum : rosen r + rosen (n - h) ≤ rosen n := by
      have hz := rosen_strictMono.monotone (Nat.sub_le n h)
      omega
    let S := Icc 1 r ×ˢ Icc (n - M + r + 1) (n - h)
    have hsub : S ⊆ pairs n (rosen n) \ pairs n (rosen (n - M)) := by
      intro p hp
      change p ∈ Icc 1 r ×ˢ Icc (n - M + r + 1) (n - h) at hp
      obtain ⟨ha, hb⟩ := mem_product.mp hp
      obtain ⟨hp₀, hp₁⟩ := mem_Icc.mp ha
      obtain ⟨hp₂, hp₃⟩ := mem_Icc.mp hb
      have h₀ := rosen_strictMono.monotone hp₁
      have h₁ := rosen_strictMono.monotone hp₃
      have h₂ : rosen (n - M) < rosen p.2 := rosen_strictMono (by omega)
      refine mem_sdiff.mpr ⟨memPairs.mpr ⟨by omega, by omega, by omega,
        by omega, by omega⟩, ?_⟩
      intro hp'
      have := (memPairs.mp hp').2.2.2.2
      omega
    have hc : S.card = r * (M - h - r) := by
      have h₁ : n - h + 1 - (n - M + r + 1) = M - h - r := by dsimp [r, h]; omega
      simp only [S, card_product, Nat.card_Icc, Nat.add_sub_cancel, h₁]
    have hcount := (card_le_card hsub).trans (pairsInGap (Nat.sub_le n M) (by omega))
    rw [hc] at hcount
    have hrM : M ≤ 30 * r := by dsimp [r]; omega
    have hhM : M ≤ 3 * (M - h - r) := by dsimp [h, r]; omega
    have hprod := Nat.mul_le_mul hrM hhM
    calc
      M ^ 2 ≤ 90 * (r * (M - h - r)) := by
        rw [pow_two]
        calc
          _ ≤ (30 * r) * (3 * (M - h - r)) := hprod
          _ = _ := by ring
      _ ≤ 100 * (rosen n - rosen (n - M)) := by
        exact Nat.mul_le_mul (by decide) hcount

end OMA.Erdos954Growth

theorem OMA.solution : OMA.R_Erdos954_erdos_954_variants_upper_R1.H1 := by
  intro k
  simpa [rosen_zero] using OMA.Erdos954Growth.allGaps k k le_rfl
