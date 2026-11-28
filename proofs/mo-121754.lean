import OMAStatements.S_mo_121754
import Mathlib

-- Problem: mo-121754, a semimagic square with line sum s is a sum of s permutation matrices,
-- phrased with an s-element index set M: the entries can be realized by sets T i j of indices
-- such that every index occurs exactly once in every row and in every column.
-- Credit: @ivillar, merged proof #13410. The Birkhoff decomposition and induction are retained.
-- Standard positive-sum and permutation-sum APIs replace the manual finite-sum arguments.
--
-- Induction on s. For s + 1, Birkhoff's theorem (in Mathlib) applied to X / (s + 1) gives a
-- permutation tau with X i (tau i) > 0 for all i. Subtract its permutation matrix, apply the
-- induction hypothesis to the remaining index set, and give the removed index the permutation
-- tau.

universe u

namespace MO121754

lemma perm_entry {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (σ.permMatrix ℚ) i j = if σ i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def]

lemma exists_perm (n s : ℕ) (X : Fin n → Fin n → ℕ) (hrow : ∀ i, ∑ j, X i j = s + 1)
    (hcol : ∀ j, ∑ i, X i j = s + 1) : ∃ τ : Equiv.Perm (Fin n), ∀ i, 1 ≤ X i (τ i) := by
  have hs : ((s : ℚ) + 1) ≠ 0 := by positivity
  have hmem : (Matrix.of fun i j => (X i j : ℚ) / (s + 1)) ∈ doublyStochastic ℚ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · simp only [Matrix.of_apply]
      positivity
    · simp only [Matrix.of_apply]
      rw [← Finset.sum_div, ← Nat.cast_sum, hrow i]
      push_cast
      exact div_self hs
    · simp only [Matrix.of_apply]
      rw [← Finset.sum_div, ← Nat.cast_sum, hcol j]
      push_cast
      exact div_self hs
  obtain ⟨w, hw0, hw1, hw⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hmem
  obtain ⟨τ, _, hτ⟩ := (Finset.sum_pos_iff_of_nonneg (fun σ _ => hw0 σ)).mp
    (by rw [hw1]; norm_num)
  refine ⟨τ, fun i => ?_⟩
  by_contra hlt
  have hX0 : X i (τ i) = 0 := by omega
  have hentry := congrFun (congrFun hw i) (τ i)
  simp only [Matrix.sum_apply, Matrix.smul_apply, perm_entry, smul_eq_mul] at hentry
  simp only [Matrix.of_apply, hX0, Nat.cast_zero, zero_div] at hentry
  have hge : w τ ≤ ∑ σ : Equiv.Perm (Fin n), w σ * (if σ i = τ i then 1 else 0) := by
    have h := Finset.single_le_sum
      (f := fun σ : Equiv.Perm (Fin n) => w σ * (if σ i = τ i then (1 : ℚ) else 0))
      (fun σ _ => mul_nonneg (hw0 σ) (by split_ifs <;> norm_num)) (Finset.mem_univ τ)
    simpa using h
  linarith

lemma decomp (n : ℕ) : ∀ (s : ℕ) (X : Fin n → Fin n → ℕ) (M : Type u) [Fintype M],
    Fintype.card M = s → (∀ i, ∑ j, X i j = s) → (∀ j, ∑ i, X i j = s) →
    ∃ σ : M → Equiv.Perm (Fin n),
      ∀ i j, (Finset.univ.filter (fun m => σ m i = j)).card = X i j := by
  intro s
  induction s with
  | zero =>
    intro X M _ hM hrow _
    have hX : ∀ i j, X i j = 0 := fun i j =>
      (Finset.sum_eq_zero_iff.mp (hrow i)) j (Finset.mem_univ j)
    have hempty : IsEmpty M := Fintype.card_eq_zero_iff.mp hM
    refine ⟨fun _ => 1, fun i j => ?_⟩
    rw [hX i j]
    simp
  | succ s ih =>
    intro X M _ hM hrow hcol
    classical
    obtain ⟨τ, hτ⟩ := exists_perm n s X hrow hcol
    have hne : Nonempty M := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨m0⟩ := hne
    have hM' : Fintype.card {m : M // m ≠ m0} = s := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hM]
      omega
    have hX' : ∀ i j, (X i j - (if τ i = j then 1 else 0)) + (if τ i = j then 1 else 0)
        = X i j := by
      intro i j
      split_ifs with h
      · have h1 := hτ i
        rw [h] at h1
        omega
      · omega
    have hrow' : ∀ i, ∑ j, (X i j - (if τ i = j then 1 else 0)) = s := by
      intro i
      have h1 : ∑ j, ((X i j - (if τ i = j then 1 else 0)) + (if τ i = j then 1 else 0))
          = s + 1 := by
        rw [← hrow i]
        exact Finset.sum_congr rfl fun j _ => hX' i j
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq] at h1
      simp at h1
      exact h1
    have hcol' : ∀ j, ∑ i, (X i j - (if τ i = j then 1 else 0)) = s := by
      intro j
      have h1 : ∑ i, ((X i j - (if τ i = j then 1 else 0)) + (if τ i = j then 1 else 0))
          = s + 1 := by
        rw [← hcol j]
        exact Finset.sum_congr rfl fun i _ => hX' i j
      have h2 : ∑ i, (if τ i = j then 1 else 0) = 1 := by
        simpa using Equiv.sum_comp τ (fun i => if i = j then (1 : ℕ) else 0)
      rw [Finset.sum_add_distrib, h2] at h1
      omega
    obtain ⟨σ', hσ'⟩ := ih (fun i j => X i j - (if τ i = j then 1 else 0))
      {m : M // m ≠ m0} hM' hrow' hcol'
    refine ⟨fun m => if h : m = m0 then τ else σ' ⟨m, h⟩, fun i j => ?_⟩
    rw [Finset.card_filter, Fintype.sum_eq_add_sum_subtype_ne _ m0]
    have h1 : (∑ m : {m : M // m ≠ m0},
        (if (if h : (m : M) = m0 then τ else σ' ⟨(m : M), h⟩) i = j then 1 else 0))
        = (Finset.univ.filter (fun m : {m : M // m ≠ m0} => σ' m i = j)).card := by
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [dif_neg m.property]
    rw [h1, hσ' i j]
    simp only [dif_pos]
    have h2 := hX' i j
    omega

end MO121754

theorem OMA.solution : type_of% @OMA.S_mo_121754.main := by
  intro n s X M _ hM hrow hcol
  classical
  obtain ⟨σ, hσ⟩ := MO121754.decomp n s X M hM hrow hcol
  refine ⟨fun i j => Finset.univ.filter (fun m => σ m i = j), hσ, ?_, ?_⟩
  · intro i m
    refine ⟨σ m i, by simp, fun j hj => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hj.symm
  · intro j m
    refine ⟨(σ m).symm j, by simp, fun i hi => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [← hi]
    simp
