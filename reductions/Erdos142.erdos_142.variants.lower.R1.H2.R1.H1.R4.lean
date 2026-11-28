import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1

/-!
# Iterating proper progression restrictions

Write the potential as log(log N) − C p^β. A sparse set only needs a proper
subprogression of positive occupancy whose potential is at least as large.
Repeat until p ≤ T. The integer length strictly decreases at each restriction,
and the one-based affine maps compose, so the terminal set is the pullback
along a single progression in the original interval. Starting at p > T + 1
gives the desired unit gain.
-/

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R4 of step Erdos142.erdos_142.variants.lower.R1.H2.R1.H1
-- Credit: @Pixelstorm44

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R4

/-- For four terms, find any shorter occupied progression preserving the potential. -/
def H1 : Prop :=
  ∃ (β C T B : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
    ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) →
      let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
      T < p → B ≤ Real.log (Real.log (N : ℝ)) - C * p ^ β →
        ∃ a q M : ℕ, 0 < q ∧ 2 ≤ M ∧ M < N ∧
          (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
          let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
          let u := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
          0 < U.card ∧
            Real.log (Real.log (N : ℝ)) - C * p ^ β ≤ Real.log (Real.log (M : ℝ)) - C * u ^ β

/-- For longer progressions the same local test allows arbitrarily small density gains. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ (β C T B : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
    ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
      let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
      T < p → B ≤ Real.log (Real.log (N : ℝ)) - C * p ^ β →
        ∃ a q M : ℕ, 0 < q ∧ 2 ≤ M ∧ M < N ∧
          (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
          let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
          let u := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
          0 < U.card ∧
            Real.log (Real.log (N : ℝ)) - C * p ^ β ≤ Real.log (Real.log (M : ℝ)) - C * u ^ β

/-- One-based affine maps compose at every positive inner index. -/
private lemma compose_map (a q b r i : ℕ) (hb : 1 ≤ b) :
    a + (b + (i - 1) * r - 1) * q =
      (a + (b - 1) * q) + (i - 1) * (r * q) := by
  rw [show b + (i - 1) * r - 1 = b - 1 + (i - 1) * r by omega]
  ring

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.H1 := by
  intro hfour hlong k hk
  have hlocal : ∃ (β C T B : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
    ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
      let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
      T < p → B ≤ Real.log (Real.log (N : ℝ)) - C * p ^ β →
        ∃ a q M : ℕ, 0 < q ∧ 2 ≤ M ∧ M < N ∧
          (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
          let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
          let u := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
          0 < U.card ∧
            Real.log (Real.log (N : ℝ)) - C * p ^ β ≤ Real.log (Real.log (M : ℝ)) - C * u ^ β := by
    rcases (show k = 4 ∨ 5 ≤ k by omega) with rfl | hfive
    · exact hfour
    · exact hlong k hfive
  obtain ⟨β, C, T, B, hβ, hβ1, hC, shrink⟩ := hlocal
  refine ⟨β, C, T + 1, B, hβ, hβ1, hC, ?_⟩
  intro R hBR N S hN hs hcard hfree
  let par (n : ℕ) (s : Finset ℕ) := max 2 (Real.log (2 * (n : ℝ) / (s.card : ℝ)))
  let value (n : ℕ) (s : Finset ℕ) := Real.log (Real.log (n : ℝ)) - C * (par n s) ^ β
  let pull (a q m : ℕ) (s : Finset ℕ) :=
    (Finset.Icc 1 m).filter (fun i ↦ a + (i - 1) * q ∈ s)
  let fits (a q m n : ℕ) := ∀ i ∈ Finset.Icc 1 m, a + (i - 1) * q ∈ Finset.Icc 1 n
  have terminal (n : ℕ) (s : Finset ℕ) (hn : 2 ≤ n) (hsub : s ⊆ Finset.Icc 1 n)
      (hpos : 0 < s.card) (hf : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ s)
      (hv : R ≤ value n s) :
      ∃ a q m : ℕ, 0 < q ∧ 2 ≤ m ∧ fits a q m n ∧
        0 < (pull a q m s).card ∧ par m (pull a q m s) ≤ T ∧ R ≤ value m (pull a q m s) := by
    induction n using Nat.strong_induction_on generalizing s with
    | h n ih =>
      by_cases hsmall : par n s ≤ T
      · have hid (i : ℕ) (hi : i ∈ Finset.Icc 1 n) : 1 + (i - 1) * 1 = i := by
          have := (Finset.mem_Icc.mp hi).1
          omega
        have hsame : pull 1 1 n s = s := by
          ext i
          constructor
          · intro hi
            obtain ⟨hi, hmem⟩ := Finset.mem_filter.mp hi
            simpa only [hid i hi] using hmem
          · intro hi
            exact Finset.mem_filter.mpr ⟨hsub hi, (hid i (hsub hi)).symm ▸ hi⟩
        exact ⟨1, 1, n, by decide, hn, fun i hi ↦ (hid i hi).symm ▸ hi,
          hsame.symm ▸ hpos, hsame.symm ▸ hsmall, hsame.symm ▸ hv⟩
      · obtain ⟨a, q, m, hq, hm, hmn, hfit, hcount, hg⟩ :=
          shrink n s hn hsub hpos hf (lt_of_not_ge hsmall) (hBR.trans hv)
        let u := pull a q m s
        obtain ⟨b, r, l, hr, hl, hinner, hcount', hp', hv'⟩ :=
          ih m hmn u hm (Finset.filter_subset _ _) hcount
            (OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.progression_preimage_free hk hq hf) (hv.trans hg)
        have hb : 1 ≤ b := by
          have hfirst := hinner 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
          simpa using (Finset.mem_Icc.mp hfirst).1
        have heq : pull b r l u = pull (a + (b - 1) * q) (r * q) l s := by
          ext i
          simp only [pull, u, Finset.mem_filter]
          constructor
          · rintro ⟨hi, hj, hmem⟩
            exact ⟨hi, (compose_map a q b r i hb) ▸ hmem⟩
          · rintro ⟨hi, hmem⟩
            exact ⟨hi, hinner i hi, (compose_map a q b r i hb).symm ▸ hmem⟩
        refine ⟨a + (b - 1) * q, r * q, l, Nat.mul_pos hr hq, hl, ?_, heq ▸ hcount',
          heq ▸ hp', heq ▸ hv'⟩
        intro i hi
        exact (compose_map a q b r i hb) ▸ hfit _ (hinner i hi)
  change T + 1 < par N S → C * (par N S) ^ β + R ≤ _ → _
  intro hlarge hbudget
  obtain ⟨a, q, m, hq, hm, hfit, hpos, hsmall, hv⟩ :=
    terminal N S hN hs hcard hfree (by dsimp [value]; linarith)
  refine ⟨a, q, m, hq, hm, hfit, hpos, ?_, ?_⟩
  · change par m (pull a q m S) + 1 ≤ par N S
    linarith
  · exact (le_sub_iff_add_le'.mp hv)

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R4
