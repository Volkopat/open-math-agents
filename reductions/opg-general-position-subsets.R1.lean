import OMAStatements.S_opg_general_position_subsets

/-!
Theorems 1 and 3 of Thang Pham, Le Quang-Ham and Boqing Xue,
"General-position sets and linear hypergraphs," arXiv:2610.34254v1.

The first hypothesis is the independent-set estimate for a finite linear
hypergraph. The second constructs such a hypergraph from the line traces of
a planar point set, using the collinear-triple estimate in Lemma 10.
-/

namespace OMA.R_opg_general_position_subsets_R1

open OMA.S_opg_general_position_subsets
open scoped Classical

def H1 : Prop :=
  ∃ (c : ℝ) (_ : 0 < c) (N₀ : ℕ),
    ∀ (A : Finset P) (E : Finset (Finset P)), N₀ ≤ A.card →
      (∀ B ∈ E, B ⊆ A ∧ B.card ≤ Nat.sqrt A.card) →
      (∀ B ∈ E, ∀ D ∈ E, B ≠ D → (B ∩ D).card ≤ 1) →
      ((∑ B ∈ E, B.card.choose 3 : ℕ) : ℝ) ≤
        73728 * (A.card : ℝ) ^ 2 * Real.log A.card →
      ∃ I ⊆ A, c * Real.sqrt A.card ≤ I.card ∧
        ∀ B ∈ E, (I ∩ B).card ≤ 2

def H2 : Prop :=
  ∀ (A : Finset P),
    (∀ B ⊆ A, Collinear ℝ (B : Set P) → B.card ≤ Nat.sqrt A.card) →
    ∃ E : Finset (Finset P),
      (∀ B ∈ E, B ⊆ A ∧ B.card ≤ Nat.sqrt A.card) ∧
      (∀ B ∈ E, ∀ D ∈ E, B ≠ D → (B ∩ D).card ≤ 1) ∧
      ((∑ B ∈ E, B.card.choose 3 : ℕ) : ℝ) ≤
        73728 * (A.card : ℝ) ^ 2 * Real.log A.card ∧
      ∀ I ⊆ A, (∀ B ∈ E, (I ∩ B).card ≤ 2) → GeneralPosition I

theorem main : H1 → H2 → type_of% @OMA.S_opg_general_position_subsets.main := by
  classical
  rintro ⟨c, hc, N₀, select⟩ geometry
  let C : ℝ := max 1 (max (N₀ : ℝ) ((c⁻¹) ^ 2))
  have hC : 1 ≤ C := le_max_left _ _
  have hCN : (N₀ : ℝ) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCc : (c⁻¹) ^ 2 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, ?_⟩
  intro n A hA
  have hnSq : (n : ℝ) ^ 2 ≤ A.card := by
    calc
      _ = 1 * (n : ℝ) ^ 2 := by simp
      _ ≤ C * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg _)
      _ ≤ _ := hA
  have hnNat : n ^ 2 ≤ A.card := by exact_mod_cast hnSq
  have hnCard : n ≤ A.card := (Nat.le_self_pow (by decide : 2 ≠ 0) n).trans hnNat
  by_cases hsmall : n ≤ 2
  · refine Or.inr ?_
    obtain ⟨I, hI, hnI⟩ := Finset.exists_subset_card_eq hnCard
    refine ⟨I, hI, hnI, ?_⟩
    intro T hT hcard
    have hle := Finset.card_le_card hT
    omega
  by_cases hcol : ∃ T ⊆ A, T.card = n ∧ Collinear ℝ (T : Set P)
  · exact Or.inl hcol
  have hthreshold : N₀ ≤ A.card := by
    have hnReal : (1 : ℝ) ≤ n := by
      exact_mod_cast (show 1 ≤ n by omega)
    have hcA : C ≤ A.card := by
      calc
        _ = C * 1 := by simp
        _ ≤ C * (n : ℝ) ^ 2 := by
          exact mul_le_mul_of_nonneg_left (by nlinarith) (zero_le_one.trans hC)
        _ ≤ _ := hA
    exact_mod_cast hCN.trans hcA
  have hcap : ∀ B ⊆ A, Collinear ℝ (B : Set P) → B.card ≤ Nat.sqrt A.card := by
    intro B hB hBcol
    by_contra! hlarge
    have hnb : n ≤ B.card := (Nat.le_sqrt'.mpr hnNat).trans hlarge.le
    obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hnb
    exact hcol ⟨T, hT.trans hB, hTcard, hBcol.subset (by exact_mod_cast hT)⟩
  obtain ⟨E, hedges, hlinear, htriple, hgp⟩ := geometry A hcap
  obtain ⟨I, hI, hsize, hind⟩ := select A E hthreshold hedges hlinear htriple
  have hsquared : (c⁻¹ * (n : ℝ)) ^ 2 ≤ A.card := by
    calc
      _ = (c⁻¹) ^ 2 * (n : ℝ) ^ 2 := by ring
      _ ≤ C * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hCc (sq_nonneg _)
      _ ≤ _ := hA
  have hroot : c⁻¹ * (n : ℝ) ≤ Real.sqrt A.card :=
    Real.le_sqrt_of_sq_le hsquared
  have hnI : n ≤ I.card := by
    have scaled := mul_le_mul_of_nonneg_left hroot hc.le
    have scale_eq : c * (c⁻¹ * (n : ℝ)) = n := by field_simp
    rw [scale_eq] at scaled
    exact_mod_cast scaled.trans hsize
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hnI
  have gpI := hgp I hI hind
  exact Or.inr ⟨T, hT.trans hI, hTcard, fun U hU => gpI U (hU.trans hT)⟩

end OMA.R_opg_general_position_subsets_R1
