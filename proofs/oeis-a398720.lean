import OMAStatements.S_oeis_a398720

-- Problem: A398720, T(n, n(n-1)/2) = n! for odd n (complements are permutation matrices).
-- Credit: @bnb9001

namespace OMA_A398720_Proof

open Finset OMA.S_oeis_a398720

theorem totOnes_eq_sum {n : ℕ} (M : Fin n → Fin n → Bool) : totOnes M = ∑ i, rowOnes M i := by
  unfold totOnes rowOnes
  rw [card_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [card_filter]

/-- the matrix of a permutation's complement -/
def pm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Fin n → Fin n → Bool := fun i j => decide (σ i ≠ j)

theorem row_pm {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : rowOnes (pm σ) i = n - 1 := by
  unfold rowOnes pm
  have : (univ.filter fun j => decide (σ i ≠ j) = true) = univ.erase (σ i) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq, mem_erase, ne_eq, and_true]
    constructor <;> intro h h' <;> exact h h'.symm
  rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

theorem col_pm {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin n) : colOnes (pm σ) j = n - 1 := by
  unfold colOnes pm
  have : (univ.filter fun i => decide (σ i ≠ j) = true) = univ.erase (σ.symm j) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq, mem_erase, ne_eq, and_true]
    constructor
    · intro h hi; apply h; rw [hi]; simp
    · intro h hi; apply h; rw [← hi]; simp
  rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

theorem pm_injective {n : ℕ} : Function.Injective (pm (n := n)) := by
  intro σ τ h
  ext i
  have := congrFun (congrFun h i) (σ i)
  simp only [pm, ne_eq, not_true_eq_false, decide_false] at this
  have h2 : ¬ (τ i ≠ σ i) := by simpa using this.symm
  push_neg at h2
  rw [h2]

theorem even_sub_one {n : ℕ} (hn : Odd n) : Even (n - 1) := by
  rcases hn with ⟨t, rfl⟩; exact ⟨t, by omega⟩

/-- complement counts -/
theorem compl_row {n : ℕ} (M : Fin n → Fin n → Bool) (i : Fin n) :
    (univ.filter fun j => M i j = false).card = n - rowOnes M i := by
  unfold rowOnes
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (p := fun j => M i j = true)
  simp only [Bool.not_eq_true, card_univ, Fintype.card_fin] at h
  omega

theorem compl_col {n : ℕ} (M : Fin n → Fin n → Bool) (j : Fin n) :
    (univ.filter fun i => M i j = false).card = n - colOnes M j := by
  unfold colOnes
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (p := fun i => M i j = true)
  simp only [Bool.not_eq_true, card_univ, Fintype.card_fin] at h
  omega

theorem rowOnes_le {n : ℕ} (M : Fin n → Fin n → Bool) (i : Fin n) : rowOnes M i ≤ n := by
  unfold rowOnes
  calc _ ≤ (univ : Finset (Fin n)).card := card_le_card (filter_subset _ _)
    _ = n := by simp

theorem colOnes_le {n : ℕ} (M : Fin n → Fin n → Bool) (j : Fin n) : colOnes M j ≤ n := by
  unfold colOnes
  calc _ ≤ (univ : Finset (Fin n)).card := card_le_card (filter_subset _ _)
    _ = n := by simp

/-- each of `n` naturals at least 1 summing to `n` equals 1 -/
theorem all_one {n : ℕ} (c : Fin n → ℕ) (h1 : ∀ i, 1 ≤ c i) (hs : ∑ i, c i = n) : ∀ i, c i = 1 := by
  have hsub : ∑ i, (c i - 1) = 0 := by
    have : ∑ i, (c i - 1) + ∑ _i : Fin n, 1 = ∑ i, c i := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun i _ => Nat.sub_add_cancel (h1 i)
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
    omega
  intro i
  have := (sum_eq_zero_iff.mp hsub) i (mem_univ _)
  have := h1 i
  omega

theorem colTot {n : ℕ} (M : Fin n → Fin n → Bool) : totOnes M = ∑ j, colOnes M j := by
  unfold totOnes colOnes
  rw [card_filter, Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [card_filter]

theorem surj {n : ℕ} (hn : Odd n) (M : Fin n → Fin n → Bool)
    (htot : totOnes M = 2 * (n * (n - 1) / 2)) (hr : ∀ i, Even (rowOnes M i))
    (hc : ∀ j, Even (colOnes M j)) : ∃ σ : Equiv.Perm (Fin n), pm σ = M := by
  have hev : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    have : Even (n * (n - 1)) := (even_sub_one hn).mul_left n
    obtain ⟨t, ht⟩ := this; omega
  rw [hev] at htot
  -- complement row counts are odd, hence ≥ 1, and sum to n
  have hrow1 : ∀ i, 1 ≤ n - rowOnes M i := by
    intro i
    have := rowOnes_le M i
    rcases hr i with ⟨t, ht⟩; rcases hn with ⟨u, hu⟩; omega
  have hcol1 : ∀ j, 1 ≤ n - colOnes M j := by
    intro j
    have := colOnes_le M j
    rcases hc j with ⟨t, ht⟩; rcases hn with ⟨u, hu⟩; omega
  have hsumr : ∑ i, (n - rowOnes M i) = n := by
    have h := totOnes_eq_sum M
    have hadd : ∑ i, (n - rowOnes M i) + ∑ i, rowOnes M i = ∑ _i : Fin n, n := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun i _ => Nat.sub_add_cancel (rowOnes_le M i)
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hadd
    have : n * n = n * (n - 1) + n := by
      rcases hn with ⟨u, hu⟩; subst hu
      rw [show 2 * u + 1 - 1 = 2 * u by omega]; ring
    omega
  have hsumc : ∑ j, (n - colOnes M j) = n := by
    have h := colTot M
    have hadd : ∑ j, (n - colOnes M j) + ∑ j, colOnes M j = ∑ _j : Fin n, n := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => Nat.sub_add_cancel (colOnes_le M j)
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hadd
    have : n * n = n * (n - 1) + n := by
      rcases hn with ⟨u, hu⟩; subst hu
      rw [show 2 * u + 1 - 1 = 2 * u by omega]; ring
    omega
  have hr1 := all_one _ hrow1 hsumr
  have hc1 := all_one _ hcol1 hsumc
  have hrowc : ∀ i, (univ.filter fun j => M i j = false).card = 1 := fun i => by
    rw [compl_row]; exact hr1 i
  have hcolc : ∀ j, (univ.filter fun i => M i j = false).card = 1 := fun j => by
    rw [compl_col]; exact hc1 j
  choose f hf using fun i => card_eq_one.mp (hrowc i)
  have hfM : ∀ i j, M i j = false ↔ j = f i := by
    intro i j
    have := congrArg (fun s => j ∈ s) (hf i)
    simpa using this
  have hinj : Function.Injective f := by
    intro i i' h
    obtain ⟨a, ha⟩ := card_eq_one.mp (hcolc (f i))
    have hi : i ∈ (univ.filter fun x => M x (f i) = false) := by simp [(hfM i (f i)).mpr rfl]
    have hi' : i' ∈ (univ.filter fun x => M x (f i) = false) := by simp [h, (hfM i' (f i')).mpr rfl]
    rw [ha] at hi hi'
    simp at hi hi'
    rw [hi, hi']
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  refine ⟨σ, ?_⟩
  funext i j
  simp only [pm, σ, Equiv.ofBijective_apply, ne_eq]
  by_cases hj : j = f i
  · subst hj; simp [(hfM i (f i)).mpr rfl]
  · have : M i j ≠ false := fun h => hj ((hfM i j).mp h)
    simp only [Bool.not_eq_false] at this
    simp [this, Ne.symm hj]

end OMA_A398720_Proof

open Finset OMA.S_oeis_a398720 OMA_A398720_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a398720.main := by
  intro n hn
  unfold T
  have hev : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    have : Even (n * (n - 1)) := (even_sub_one hn).mul_left n
    obtain ⟨t, ht⟩ := this; omega
  have hset : (univ.filter fun M : Fin n → Fin n → Bool =>
      totOnes M = 2 * (n * (n - 1) / 2) ∧ (∀ i, Even (rowOnes M i)) ∧ ∀ j, Even (colOnes M j)) =
      (univ : Finset (Equiv.Perm (Fin n))).image pm := by
    ext M
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact surj hn M h1 h2 h3
    · rintro ⟨σ, rfl⟩
      refine ⟨?_, fun i => by rw [row_pm]; exact even_sub_one hn,
        fun j => by rw [col_pm]; exact even_sub_one hn⟩
      rw [hev, totOnes_eq_sum]
      simp [row_pm]
  rw [hset, card_image_of_injective _ pm_injective, card_univ, Fintype.card_perm, Fintype.card_fin]
