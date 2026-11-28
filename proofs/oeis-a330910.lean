import OMAStatements.S_oeis_a330910

namespace OMA.S_oeis_a330910

open Finset PowerSeries




/-- Subsets of {1..n} that are nonempty with gaps at least 5. -/
def nsets (n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 n).powerset.filter fun S => S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S, x < y → x + 5 ≤ y

lemma nsets_card (n : ℕ) : (nsets n).card = (sets n).card + n := by
  have hsplit : nsets n = sets n ∪ (Icc 1 n).powerset.filter (fun S => S.card = 1) := by
    ext S
    simp only [nsets, sets, mem_filter, mem_powerset, mem_union]
    constructor
    · rintro ⟨hS, hne, hv⟩
      rcases Nat.lt_or_ge S.card 2 with h | h
      · right
        exact ⟨hS, by have := hne.card_pos; omega⟩
      · left; exact ⟨hS, h, hv⟩
    · rintro (⟨hS, h2, hv⟩ | ⟨hS, h1⟩)
      · exact ⟨hS, card_pos.mp (by omega), hv⟩
      · refine ⟨hS, card_pos.mp (by omega), ?_⟩
        obtain ⟨z, rfl⟩ := card_eq_one.mp h1
        intro x hx y hy hxy
        simp at hx hy; omega
  have hdisj : Disjoint (sets n) ((Icc 1 n).powerset.filter (fun S => S.card = 1)) := by
    rw [disjoint_left]
    intro S h1 h2
    simp only [sets, mem_filter] at h1 h2
    omega
  rw [hsplit, card_union_of_disjoint hdisj, ← powersetCard_eq_filter, card_powersetCard,
    Nat.card_Icc, Nat.add_sub_cancel, Nat.choose_one_right]

lemma sets_succ5 (n : ℕ) : (sets (n + 5)).card = (sets (n + 4)).card + (nsets n).card := by
  have hIcc : Icc 1 (n + 5) = insert (n + 5) (Icc 1 (n + 4)) := by
    ext x; simp only [mem_insert, mem_Icc]; omega
  have hnot : n + 5 ∉ Icc 1 (n + 4) := by simp
  have hpow := powerset_insert (Icc 1 (n + 4)) (n + 5)
  unfold sets
  rw [hIcc, hpow, filter_union]
  have hdisj : Disjoint ((Icc 1 (n + 4)).powerset.filter fun S => 2 ≤ S.card ∧
      ∀ x ∈ S, ∀ y ∈ S, x < y → x + 5 ≤ y)
      (((Icc 1 (n + 4)).powerset.image (insert (n + 5))).filter fun S => 2 ≤ S.card ∧
      ∀ x ∈ S, ∀ y ∈ S, x < y → x + 5 ≤ y) := by
    rw [disjoint_left]
    intro S h1 h2
    simp only [mem_filter, mem_powerset, mem_image] at h1 h2
    obtain ⟨T, -, rfl⟩ := h2.1
    have := h1.1 (mem_insert_self _ _)
    simp at this
  rw [card_union_of_disjoint hdisj]
  congr 1
  rw [filter_image, card_image_of_injOn]
  · congr 1
    ext T
    simp only [mem_filter, mem_powerset, nsets]
    constructor
    · rintro ⟨hT, h2, hv⟩
      have hTn : T ⊆ Icc 1 n := by
        intro x hx
        have h1 := hT hx
        simp only [mem_Icc] at h1 ⊢
        have := hv x (mem_insert_of_mem hx) (n + 5) (mem_insert_self _ _) (by omega)
        omega
      refine ⟨hTn, ?_, fun x hx y hy hxy => hv x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy⟩
      rw [← card_pos]
      have := card_insert_le (n + 5) T
      omega
    · rintro ⟨hT, hne, hv⟩
      refine ⟨hT.trans (Icc_subset_Icc_right (by omega)), ?_, ?_⟩
      · rw [card_insert_of_notMem (fun h => by have := hT h; simp at this)]
        have := hne.card_pos
        omega
      · intro x hx y hy hxy
        rw [mem_insert] at hx hy
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · omega
        · have := hT hy; simp at this; omega
        · have := hT hx; simp at this; omega
        · exact hv x hx y hy hxy
  · intro T hT U hU hTU
    simp only [coe_filter, Set.mem_ofPred_eq, mem_powerset] at hT hU
    have hT' : n + 5 ∉ T := fun h => by have := hT.1 h; simp at this
    have hU' : n + 5 ∉ U := fun h => by have := hU.1 h; simp at this
    rw [← erase_insert hT', ← erase_insert hU', hTU]

lemma step (m : ℕ) : a (m + 5) = a (m + 4) + a m + (m + 5) := by
  unfold a
  rw [show m + 5 + 5 = (m + 5) + 5 by ring, sets_succ5, nsets_card,
    show m + 5 + 4 = m + 4 + 5 by ring]
  ring

lemma a_small : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 6 ∧ a 4 = 10 := by
  unfold a sets
  decide +kernel

/-- Barker's recurrence: a(n) = 3a(n-1) - 3a(n-2) + a(n-3) + a(n-5) - 2a(n-6) + a(n-7) for n > 6. -/
theorem recurrence : ∀ n : ℕ, 6 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) +
    a (n - 5) - 2 * a (n - 6) + a (n - 7) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have h0 := step (m + 2)
  have h1 := step (m + 1)
  have h2 := step m
  simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 5 = m + 2 by omega,
    show m + 7 - 6 = m + 1 by omega, show m + 7 - 7 = m by omega]
  rw [show m + 2 + 5 = m + 7 by ring, show m + 2 + 4 = m + 6 by ring] at h0
  rw [show m + 1 + 5 = m + 6 by ring, show m + 1 + 4 = m + 5 by ring] at h1
  push_cast [h0, h1, h2]
  ring

lemma coeff_gf (n : ℕ) : coeff n gf = (a n : ℚ) := by simp [gf]

/-- Barker's g.f.: x / ((1 - x)^2 (1 - x + x^2) (1 - x^2 - x^3)), as an identity in Q[[x]]. -/
theorem gf_eq : gf = X * ((1 - X) ^ 2 * (1 - X + X ^ 2) * (1 - X ^ 2 - X ^ 3))⁻¹ := by
  have hden : constantCoeff ((1 - X) ^ 2 * (1 - X + X ^ 2) * (1 - X ^ 2 - X ^ 3) : ℚ⟦X⟧) ≠ 0 := by
    simp
  have key : gf * ((1 - X) ^ 2 * (1 - X + X ^ 2) * (1 - X ^ 2 - X ^ 3)) = X := by
    have e : gf * ((1 - X) ^ 2 * (1 - X + X ^ 2) * (1 - X ^ 2 - X ^ 3)) =
        gf - gf * X ^ 1 - gf * X ^ 1 - gf * X ^ 1 + gf * X ^ 2 + gf * X ^ 2 + gf * X ^ 2 -
        gf * X ^ 3 - gf * X ^ 5 + gf * X ^ 6 + gf * X ^ 6 - gf * X ^ 7 := by ring
    rw [e]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_gf, coeff_X]
    obtain ⟨h0, h1, h2, h3, h4⟩ := a_small
    have h5 : a 5 = 15 := by have := step 0; norm_num at this; omega
    have h6 : a 6 = 22 := by have := step 1; norm_num at this; omega
    rcases Nat.lt_or_ge n 7 with hn | hn
    · interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6] <;> norm_num
    · have hr := recurrence n (by omega)
      have hq : (a n : ℚ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) + a (n - 5) -
          2 * a (n - 6) + a (n - 7) := by exact_mod_cast hr
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
        show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, if_true,
        show n ≠ 1 by omega, if_false]
      linarith
  calc gf = gf * (((1 - X) ^ 2 * (1 - X + X ^ 2) * (1 - X ^ 2 - X ^ 3)) *
        ((1 - X) ^ 2 * (1 - X + X ^ 2) * (1 - X ^ 2 - X ^ 3))⁻¹) := by
          rw [PowerSeries.mul_inv_cancel _ hden, mul_one]
    _ = (gf * ((1 - X) ^ 2 * (1 - X + X ^ 2) * (1 - X ^ 2 - X ^ 3))) *
        ((1 - X) ^ 2 * (1 - X + X ^ 2) * (1 - X ^ 2 - X ^ 3))⁻¹ := (mul_assoc gf _ _).symm
    _ = X * ((1 - X) ^ 2 * (1 - X + X ^ 2) * (1 - X ^ 2 - X ^ 3))⁻¹ := by rw [key]

/-- Both of Barker's conjectures. -/
theorem conjecture :
    gf = X * ((1 - X) ^ 2 * (1 - X + X ^ 2) * (1 - X ^ 2 - X ^ 3))⁻¹ ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) +
      a (n - 5) - 2 * a (n - 6) + a (n - 7)) :=
  ⟨gf_eq, recurrence⟩

/-- Control from the entry's example: a(6) = 22 (subsets of {1, ..., 11}). -/
example : a 6 = 22 := by
  have h := step 1
  obtain ⟨h0, h1, h2, h3, h4⟩ := a_small
  have h5 := step 0
  norm_num at h h5
  omega

end OMA.S_oeis_a330910

theorem OMA.solution : type_of% @OMA.S_oeis_a330910.main :=
  OMA.S_oeis_a330910.conjecture
