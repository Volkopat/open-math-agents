import OMAStatements.S_oeis_a269469

/-!
# A269469: five-letter words with unequal successive repeated values

Count good words by summing out one letter at a time from the right (`total`). With `m = n + 1`
letters: for fixed `a, b, c, d` with no constant triple, the last letter is free unless `c = d` or
`a = b = d`, where it must avoid `d`; summing over `d`, `c`, `b`, `a` gives `m^5 - 3 m^3 + m^2 + m`
(`count_eq`). That polynomial vanishes at `m = 1`, so `terms j` is the stated quintic for every
`j` (`terms_eq`). The recurrence is its sixth difference, and the generating function is checked
coefficientwise (`gf`).
-/

namespace A269469P
open OMA.S_oeis_a269469 Finset

theorem sum_ite_fin (m : ℕ) (c : Fin m) (u v : ℚ) :
    ∑ x : Fin m, (if x = c then u else v) = u + (m - 1) * v := by
  have : ∀ x : Fin m, (if x = c then u else v) = v + (if x = c then u - v else 0) := by
    intro x; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun x _ => this x), sum_add_distrib, sum_const, card_univ,
    Fintype.card_fin, Finset.sum_ite_eq' univ c (fun _ => u - v), if_pos (mem_univ c)]
  simp only [nsmul_eq_mul]; ring

theorem sum_const_fin (m : ℕ) (v : ℚ) : ∑ _x : Fin m, v = m * v := by
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem total (n : ℕ) : ∑ a : Fin (n + 1), ∑ b : Fin (n + 1), ∑ c : Fin (n + 1),
    ∑ d : Fin (n + 1), ∑ e : Fin (n + 1),
    (if (a = b ∧ b = c) ∨ (b = c ∧ c = d) ∨ (c = d ∧ d = e) ∨ (a = b ∧ a = d ∧ d = e)
      then (0 : ℚ) else 1) =
    ((n : ℚ) + 1) ^ 5 - 3 * (n + 1) ^ 3 + (n + 1) ^ 2 + (n + 1) := by
  have he : ∀ a b c d : Fin (n + 1), ∑ e : Fin (n + 1),
      (if (a = b ∧ b = c) ∨ (b = c ∧ c = d) ∨ (c = d ∧ d = e) ∨ (a = b ∧ a = d ∧ d = e)
        then (0 : ℚ) else 1) =
      if (a = b ∧ b = c) ∨ (b = c ∧ c = d) then (0 : ℚ)
      else if c = d ∨ (a = b ∧ a = d) then (n : ℚ) else (n : ℚ) + 1 := by
    intro a b c d
    by_cases h1 : (a = b ∧ b = c) ∨ (b = c ∧ c = d)
    · rw [if_pos h1]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [if_pos (by tauto)]
    · rw [if_neg h1]
      by_cases h2 : c = d ∨ (a = b ∧ a = d)
      · rw [if_pos h2]
        have : ∀ e : Fin (n + 1), (if (a = b ∧ b = c) ∨ (b = c ∧ c = d) ∨ (c = d ∧ d = e) ∨
            (a = b ∧ a = d ∧ d = e) then (0 : ℚ) else 1) = if e = d then 0 else 1 := by
          intro e
          by_cases hed : e = d
          · subst hed; rw [if_pos rfl, if_pos (by tauto)]
          · rw [if_neg hed, if_neg]
            intro h; rcases h with h | h | h | h
            · exact h1 (Or.inl h)
            · exact h1 (Or.inr h)
            · exact hed h.2.symm
            · exact hed h.2.2.symm
        rw [Finset.sum_congr rfl (fun e _ => this e), sum_ite_fin]; push_cast; ring
      · rw [if_neg h2]
        have : ∀ e : Fin (n + 1), (if (a = b ∧ b = c) ∨ (b = c ∧ c = d) ∨ (c = d ∧ d = e) ∨
            (a = b ∧ a = d ∧ d = e) then (0 : ℚ) else 1) = 1 := by
          intro e
          rw [if_neg]
          intro h; rcases h with h | h | h | h
          · exact h1 (Or.inl h)
          · exact h1 (Or.inr h)
          · exact h2 (Or.inl h.1)
          · exact h2 (Or.inr ⟨h.1, h.2.1⟩)
        rw [Finset.sum_congr rfl (fun e _ => this e), sum_const_fin]; push_cast; ring
  have hd : ∀ a b c : Fin (n + 1), ∑ d : Fin (n + 1),
      (if (a = b ∧ b = c) ∨ (b = c ∧ c = d) then (0 : ℚ)
        else if c = d ∨ (a = b ∧ a = d) then (n : ℚ) else (n : ℚ) + 1) =
      if a = b ∧ b = c then (0 : ℚ) else if b = c then (n : ℚ) * (n + 1)
        else if a = b then (n : ℚ) ^ 2 + 2 * n - 1 else (n : ℚ) ^ 2 + 2 * n := by
    intro a b c
    by_cases hab : a = b <;> by_cases hbc : b = c
    · subst hab; subst hbc
      rw [if_pos ⟨rfl, rfl⟩]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [if_pos (Or.inl ⟨rfl, rfl⟩)]
    · subst hab
      rw [if_neg (by tauto), if_neg hbc, if_pos rfl]
      have hca : c ≠ a := fun h => hbc h.symm
      have : ∀ d : Fin (n + 1), (if (a = a ∧ a = c) ∨ (a = c ∧ c = d) then (0 : ℚ)
          else if c = d ∨ (a = a ∧ a = d) then (n : ℚ) else (n : ℚ) + 1) =
          ((n : ℚ) + 1) - (if d = c then 1 else 0) - (if d = a then 1 else 0) := by
        intro d
        rw [if_neg (by tauto)]
        by_cases hdc : d = c
        · subst hdc
          rw [if_pos (Or.inl rfl), if_pos rfl, if_neg hca]; ring
        · by_cases hda : d = a
          · subst hda
            rw [if_pos (Or.inr ⟨rfl, rfl⟩), if_neg hdc, if_pos rfl]; ring
          · rw [if_neg (by rintro (h | h); exact hdc h.symm; exact hda h.2.symm), if_neg hdc,
              if_neg hda]; ring
      rw [Finset.sum_congr rfl (fun d _ => this d), sum_sub_distrib, sum_sub_distrib, sum_const_fin,
        Finset.sum_ite_eq' univ c (fun _ => (1 : ℚ)), Finset.sum_ite_eq' univ a (fun _ => (1 : ℚ)),
        if_pos (mem_univ c), if_pos (mem_univ a)]
      push_cast; ring
    · subst hbc
      rw [if_neg (by tauto), if_pos rfl]
      have : ∀ d : Fin (n + 1), (if (a = b ∧ b = b) ∨ (b = b ∧ b = d) then (0 : ℚ)
          else if b = d ∨ (a = b ∧ a = d) then (n : ℚ) else (n : ℚ) + 1) =
          if d = b then 0 else (n : ℚ) + 1 := by
        intro d
        by_cases hdb : d = b
        · subst hdb; rw [if_pos (Or.inr ⟨rfl, rfl⟩), if_pos rfl]
        · rw [if_neg (by rintro (h | h); exact hab h.1; exact hdb h.2.symm), if_neg hdb,
            if_neg (by rintro (h | h); exact hdb h.symm; exact hab h.1)]
      rw [Finset.sum_congr rfl (fun d _ => this d), sum_ite_fin]; push_cast; ring
    · rw [if_neg (by tauto), if_neg hbc, if_neg hab]
      have : ∀ d : Fin (n + 1), (if (a = b ∧ b = c) ∨ (b = c ∧ c = d) then (0 : ℚ)
          else if c = d ∨ (a = b ∧ a = d) then (n : ℚ) else (n : ℚ) + 1) =
          if d = c then (n : ℚ) else (n : ℚ) + 1 := by
        intro d
        rw [if_neg (by tauto)]
        by_cases hdc : d = c
        · subst hdc; rw [if_pos (Or.inl rfl), if_pos rfl]
        · rw [if_neg (by rintro (h | h); exact hdc h.symm; exact hab h.1), if_neg hdc]
      rw [Finset.sum_congr rfl (fun d _ => this d), sum_ite_fin]; push_cast; ring
  have hc : ∀ a b : Fin (n + 1), ∑ c : Fin (n + 1),
      (if a = b ∧ b = c then (0 : ℚ) else if b = c then (n : ℚ) * (n + 1)
        else if a = b then (n : ℚ) ^ 2 + 2 * n - 1 else (n : ℚ) ^ 2 + 2 * n) =
      if a = b then (n : ℚ) * ((n : ℚ) ^ 2 + 2 * n - 1)
        else (n : ℚ) * (n + 1) + n * ((n : ℚ) ^ 2 + 2 * n) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      have : ∀ c : Fin (n + 1), (if a = a ∧ a = c then (0 : ℚ) else if a = c then (n : ℚ) * (n + 1)
          else if a = a then (n : ℚ) ^ 2 + 2 * n - 1 else (n : ℚ) ^ 2 + 2 * n) =
          if c = a then 0 else (n : ℚ) ^ 2 + 2 * n - 1 := by
        intro c
        by_cases hca : c = a
        · subst hca; rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
        · have hac : ¬ a = c := fun h => hca h.symm
          rw [if_neg (by tauto), if_neg hac, if_pos rfl, if_neg hca]
      rw [Finset.sum_congr rfl (fun c _ => this c), sum_ite_fin, if_pos rfl]; push_cast; ring
    · have : ∀ c : Fin (n + 1), (if a = b ∧ b = c then (0 : ℚ) else if b = c then (n : ℚ) * (n + 1)
          else if a = b then (n : ℚ) ^ 2 + 2 * n - 1 else (n : ℚ) ^ 2 + 2 * n) =
          if c = b then (n : ℚ) * (n + 1) else (n : ℚ) ^ 2 + 2 * n := by
        intro c
        by_cases hcb : c = b
        · subst hcb; rw [if_neg (by tauto), if_pos rfl, if_pos rfl]
        · have hbc : ¬ b = c := fun h => hcb h.symm
          rw [if_neg (by tauto), if_neg hbc, if_neg hab, if_neg hcb]
      rw [Finset.sum_congr rfl (fun c _ => this c), sum_ite_fin, if_neg hab]; push_cast; ring
  have hb : ∀ a : Fin (n + 1), ∑ b : Fin (n + 1),
      (if a = b then (n : ℚ) * ((n : ℚ) ^ 2 + 2 * n - 1)
        else (n : ℚ) * (n + 1) + n * ((n : ℚ) ^ 2 + 2 * n)) =
      (n : ℚ) * ((n : ℚ) ^ 2 + 2 * n - 1) + n * ((n : ℚ) * (n + 1) + n * ((n : ℚ) ^ 2 + 2 * n)) := by
    intro a
    have : ∀ b : Fin (n + 1), (if a = b then (n : ℚ) * ((n : ℚ) ^ 2 + 2 * n - 1)
        else (n : ℚ) * (n + 1) + n * ((n : ℚ) ^ 2 + 2 * n)) =
        if b = a then (n : ℚ) * ((n : ℚ) ^ 2 + 2 * n - 1)
        else (n : ℚ) * (n + 1) + n * ((n : ℚ) ^ 2 + 2 * n) := by
      intro b; by_cases h : b = a
      · subst h; simp
      · rw [if_neg (fun e => h e.symm), if_neg h]
    rw [Finset.sum_congr rfl (fun b _ => this b), sum_ite_fin]; push_cast; ring
  simp only [he, hd, hc, hb, sum_const_fin]
  push_cast; ring

theorem total' (n : ℕ) : ∑ a : Fin (n + 1), ∑ b : Fin (n + 1), ∑ c : Fin (n + 1),
    ∑ d : Fin (n + 1), ∑ e : Fin (n + 1),
    (if ¬((a = b ∧ b = c) ∨ (b = c ∧ c = d) ∨ (c = d ∧ d = e) ∨ (a = b ∧ a = d ∧ d = e))
      then (1 : ℚ) else 0) =
    ((n : ℚ) + 1) ^ 5 - 3 * (n + 1) ^ 3 + (n + 1) ^ 2 + (n + 1) := by
  rw [← total n]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ =>
    sum_congr rfl fun d _ => sum_congr rfl fun e _ => ?_
  exact ite_not _ _ _

theorem count_eq (n : ℕ) :
    (count n : ℚ) = ((n : ℚ) + 1) ^ 5 - 3 * (n + 1) ^ 3 + (n + 1) ^ 2 + (n + 1) := by
  classical
  unfold count
  rw [Finset.card_filter]
  push_cast
  simp only [Fintype.sum_prod_type, bad]
  convert total' n using 10
  all_goals first | ring1 | congr

theorem terms_eq (j : ℕ) :
    terms j = (j : ℤ) ^ 5 + 5 * j ^ 4 + 7 * j ^ 3 + 2 * j ^ 2 - j := by
  cases j with
  | zero => rfl
  | succ k =>
    have h := count_eq (k + 1)
    have : ((count (k + 1) : ℤ) : ℚ) =
        ((((k + 1 : ℕ) : ℤ) ^ 5 + 5 * ((k + 1 : ℕ) : ℤ) ^ 4 + 7 * ((k + 1 : ℕ) : ℤ) ^ 3 +
          2 * ((k + 1 : ℕ) : ℤ) ^ 2 - ((k + 1 : ℕ) : ℤ) : ℤ) : ℚ) := by
      rw [Int.cast_natCast, h]; push_cast; ring
    rw [terms]; exact_mod_cast this

theorem terms_succ (n : ℕ) : terms (n + 1) = ((n : ℤ) + 1) ^ 5 + 5 * (n + 1) ^ 4 +
    7 * (n + 1) ^ 3 + 2 * (n + 1) ^ 2 - (n + 1) := by
  rw [terms_eq]; push_cast; ring

theorem recur (n : ℕ) : terms (n + 7) = 6 * terms (n + 6) - 15 * terms (n + 5) +
    20 * terms (n + 4) - 15 * terms (n + 3) + 6 * terms (n + 2) - terms (n + 1) := by
  simp only [terms_eq]; push_cast; ring

open PowerSeries in
theorem gf : ((1 : PowerSeries ℤ) - X) ^ 6 * PowerSeries.mk terms =
    (2 * X * (7 + 45 * X + 9 * X ^ 2 - X ^ 3) : PowerSeries ℤ) := by
  have e1 : ((1 - X) ^ 6 : PowerSeries ℤ) =
      1 - C 6 * X ^ 1 + C 15 * X ^ 2 - C 20 * X ^ 3 + C 15 * X ^ 4 - C 6 * X ^ 5 + X ^ 6 := by
    simp only [map_ofNat, pow_one]; ring
  have e2 : (2 * X * (7 + 45 * X + 9 * X ^ 2 - X ^ 3) : PowerSeries ℤ) =
      C 14 * X ^ 1 + C 90 * X ^ 2 + C 18 * X ^ 3 - C 2 * X ^ 4 := by
    simp only [map_ofNat, pow_one]; ring
  rw [e1, e2]
  ext k
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add, coeff_C_mul, coeff_X_pow_mul',
    coeff_mk, coeff_X_pow]
  rcases Nat.lt_or_ge k 6 with h | h
  · interval_cases k <;> simp [terms_eq]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega, show 3 ≤ j + 6 by omega,
      show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega, ↓reduceIte,
      show j + 6 ≠ 1 by omega, show j + 6 ≠ 2 by omega, show j + 6 ≠ 3 by omega,
      show j + 6 ≠ 4 by omega,
      show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
      show j + 6 - 3 = j + 3 by omega, show j + 6 - 4 = j + 2 by omega,
      show j + 6 - 5 = j + 1 by omega, show j + 6 - 6 = j by omega, terms_eq]
    push_cast; ring

end A269469P

theorem OMA.solution : type_of% @OMA.S_oeis_a269469.main :=
  ⟨A269469P.terms_succ, A269469P.recur, A269469P.gf⟩
