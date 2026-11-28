import OMAReductions.R_Green26_green_26_variants_open_R1
import Mathlib

-- Step Green26.green_26.variants.open.R1.H3: hypothesis H3 of reduction Green26.green_26.variants.open.R1
-- Credit: @ivillar. Alon's permanent lemma via Mathlib's combinatorial Nullstellensatz: f = prod_i ((M x)_i - b_i) has coefficient perm(M) != 0 at the all-ones monomial, of top degree n, so f does not vanish on {0,1}^n.

/-! Step Green26.green_26.variants.open.R1.H3. -/

open MvPolynomial Finset

namespace P8Alon

variable {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The linear form `∑ j, M i j X j`. -/
noncomputable def L (M : Matrix ι ι F) (i : ι) : MvPolynomial ι F := ∑ j, C (M i j) * X j

/-- The all-ones exponent vector. -/
noncomputable def tt (ι : Type) [Fintype ι] [DecidableEq ι] : ι →₀ ℕ := ∑ j : ι, Finsupp.single j 1

private lemma sum_apply (p : ι → ι →₀ ℕ) (j : ι) :
    (∑ i, p i) j = ∑ i, p i j :=
  map_sum (Finsupp.applyAddHom j) _ _

lemma tt_apply (j : ι) : tt ι j = 1 := by
  simp [tt, sum_apply, Finsupp.single_apply]

lemma tt_degree : (tt ι).degree = Fintype.card ι := by
  rw [tt, map_sum]
  simp

lemma totalDegree_L (M : Matrix ι ι F) (i : ι) : (L M i).totalDegree ≤ 1 := by
  unfold L
  apply totalDegree_finsetSum_le
  intro j _
  calc (C (M i j) * X j : MvPolynomial ι F).totalDegree
      ≤ (C (M i j) : MvPolynomial ι F).totalDegree + (X j : MvPolynomial ι F).totalDegree :=
        totalDegree_mul _ _
    _ = 1 := by rw [totalDegree_C, totalDegree_X, zero_add]

lemma totalDegree_prod_L (M : Matrix ι ι F) (u : Finset ι) :
    (∏ i ∈ u, L M i).totalDegree ≤ u.card := by
  calc (∏ i ∈ u, L M i).totalDegree ≤ ∑ i ∈ u, (L M i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ _i ∈ u, 1 := Finset.sum_le_sum (fun i _ => totalDegree_L M i)
    _ = u.card := by simp

lemma sum_single_eq_tt_iff (φ : ι → ι) :
    (∑ i, Finsupp.single (φ i) 1 : ι →₀ ℕ) = tt ι ↔ Function.Bijective φ := by
  rw [Function.bijective_iff_existsUnique, Finsupp.ext_iff]
  simp only [tt_apply, sum_apply, Finsupp.single_apply]
  exact forall_congr' fun j => by
    rw [← Finset.card_filter, Finset.card_eq_one_iff_existsUnique]
    simp

lemma coeff_prod_L (M : Matrix ι ι F) : (∏ i, L M i).coeff (tt ι) = M.permanent := by
  simp only [L]
  rw [Finset.prod_univ_sum, coeff_sum]
  have hterm : ∀ φ : ι → ι, (∏ i, C (M i (φ i)) * X (φ i) : MvPolynomial ι F) =
      C (∏ i, M i (φ i)) * monomial (∑ i, Finsupp.single (φ i) 1) 1 := by
    intro φ
    rw [Finset.prod_mul_distrib, ← map_prod, monomial_sum_one]
    rfl
  simp only [hterm, coeff_C_mul, coeff_monomial, Fintype.piFinset_univ]
  have h2 : ∀ φ : ι → ι, (∏ i, M i (φ i)) * (if (∑ i, Finsupp.single (φ i) 1 : ι →₀ ℕ) = tt ι then (1 : F) else 0) =
      if Function.Bijective φ then ∏ i, M i (φ i) else 0 := by
    intro φ
    simp only [sum_single_eq_tt_iff]
    split_ifs <;> simp
  simp only [h2]
  rw [← Finset.sum_filter, ← Matrix.permanent_transpose]
  unfold Matrix.permanent
  symm
  exact Finset.sum_bij' (fun (σ : Equiv.Perm ι) _ => (σ : ι → ι))
    (fun (φ : ι → ι) hφ => (Equiv.ofBijective φ (Finset.mem_filter.mp hφ).2 : Equiv.Perm ι))
    (fun σ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.bijective⟩)
    (fun φ _ => Finset.mem_univ _)
    (fun σ _ => Equiv.ext fun _ => rfl)
    (fun φ _ => rfl)
    (fun σ _ => rfl)

theorem alon : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F),
    M.permanent ≠ 0 → ∀ b : ι → F,
      ∃ x : ι → F, (∀ j, x j = 0 ∨ x j = 1) ∧ ∀ i, M.mulVec x i ≠ b i := by
  intro F _ ι _ _ M hM b
  classical
  let f : MvPolynomial ι F := ∏ i, (L M i + C (-b i))
  have hcoeff : f.coeff (tt ι) = M.permanent := by
    simp only [f]
    rw [Finset.prod_add, coeff_sum]
    rw [Finset.sum_eq_single (univ : Finset ι)]
    · simp [coeff_prod_L]
    · intro u _ hu
      apply coeff_eq_zero_of_totalDegree_lt
      have hlt : u.card < Fintype.card ι := by
        apply Finset.card_lt_card
        exact Finset.ssubset_univ_iff.mpr hu
      calc ((∏ i ∈ u, L M i) * ∏ i ∈ univ \ u, C (-b i)).totalDegree
          ≤ (∏ i ∈ u, L M i).totalDegree + (∏ i ∈ univ \ u, (C (-b i) : MvPolynomial ι F)).totalDegree :=
            totalDegree_mul _ _
        _ ≤ u.card + 0 := by
            gcongr
            · exact totalDegree_prod_L M u
            · rw [← map_prod, totalDegree_C]
        _ < (tt ι).degree := by rw [tt_degree]; omega
    · intro h
      exact absurd (Finset.mem_powerset.mpr (Finset.subset_univ _)) h
  have hdeg : f.totalDegree = (tt ι).degree := by
    apply le_antisymm
    · rw [tt_degree]
      calc f.totalDegree ≤ ∑ i, (L M i + C (-b i)).totalDegree := totalDegree_finsetProd _ _
        _ ≤ ∑ _i : ι, 1 := by
            apply Finset.sum_le_sum
            intro i _
            calc (L M i + C (-b i)).totalDegree ≤ max (L M i).totalDegree (C (-b i) : MvPolynomial ι F).totalDegree :=
                  totalDegree_add _ _
              _ ≤ 1 := max_le (totalDegree_L M i) (by rw [totalDegree_C]; omega)
        _ = Fintype.card ι := by simp
    · apply le_totalDegree
      rw [mem_support_iff, hcoeff]
      exact hM
  let S : ι → Finset F := fun _ => {0, 1}
  obtain ⟨s, hsS, hs⟩ := combinatorial_nullstellensatz_exists_eval_nonzero f (tt ι)
    (by rw [hcoeff]; exact hM) hdeg S (by
      intro i
      rw [tt_apply]
      simp [S, Finset.card_insert_of_notMem])
  refine ⟨s, fun j => by simpa [S] using hsS j, ?_⟩
  intro i hi
  apply hs
  simp only [f, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [L, map_add, map_sum, map_mul, eval_C, eval_X]
  rw [← hi]
  simp [Matrix.mulVec, dotProduct]

end P8Alon

theorem OMA.solution : OMA.R_Green26_green_26_variants_open_R1.H3 :=
  P8Alon.alon
