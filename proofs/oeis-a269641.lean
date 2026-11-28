import OMAStatements.S_oeis_a269641

/-!
# A269641: four-letter words with prescribed successive repetitions

Split the indicator of `¬ two w ∨ allowedPair w` as the indicator of `¬ two w` plus that of
`allowedPair w` (an allowed pair has two repetitions). Words with at most one repetition number
`(n + 1) n^2 (n + 3)` (`notwo`, by summing out one letter at a time). Allowed pairs correspond to
pairs `(a, c)` in `0, …, n` with `c = a + 2` or `a = c + 1`, which number `2 n - 1` for `n ≥ 1`
(`pairs`, `ap_total`). Hence `count n = n^2 (n + 1) (n + 3) + 2 n - 1` for `n ≥ 1` (`count_eq`),
which gives the closed form and the recurrence. In the generating function the coefficients of
index at least six are fifth differences of the quartic; the first six are computed directly,
using `terms 0 = 0` (`gf`).
-/

namespace A269641P
open OMA.S_oeis_a269641 Finset

theorem sum_ite_fin (m : ℕ) (c : Fin m) (u v : ℚ) :
    ∑ x : Fin m, (if x = c then u else v) = u + (m - 1) * v := by
  have : ∀ x : Fin m, (if x = c then u else v) = v + (if x = c then u - v else 0) := by
    intro x; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun x _ => this x), sum_add_distrib, sum_const, card_univ,
    Fintype.card_fin, Finset.sum_ite_eq' univ c (fun _ => u - v), if_pos (mem_univ c)]
  simp only [nsmul_eq_mul]; ring

theorem notwo (n : ℕ) : ∑ a : Fin (n + 1), ∑ b : Fin (n + 1), ∑ c : Fin (n + 1), ∑ d : Fin (n + 1),
    (if (a = b ∧ b = c) ∨ (b = c ∧ c = d) ∨ (a = b ∧ c = d) then (0 : ℚ) else 1) =
    (n + 1) * n ^ 2 * (n + 3) := by
  have hd : ∀ a b c : Fin (n + 1), ∑ d : Fin (n + 1),
      (if (a = b ∧ b = c) ∨ (b = c ∧ c = d) ∨ (a = b ∧ c = d) then (0 : ℚ) else 1) =
      if a = b ∧ b = c then (0 : ℚ) else if b = c ∨ a = b then (n : ℚ) else (n : ℚ) + 1 := by
    intro a b c
    by_cases h1 : a = b ∧ b = c
    · simp [h1]
    · by_cases h2 : b = c ∨ a = b
      · have : ∀ d : Fin (n + 1), (if (a = b ∧ b = c) ∨ (b = c ∧ c = d) ∨ (a = b ∧ c = d) then (0 : ℚ) else 1)
            = if d = c then 0 else 1 := by
          intro d
          by_cases hd : d = c
          · subst hd; rw [if_pos rfl, if_pos (by tauto)]
          · rw [if_neg hd, if_neg]; intro h; rcases h with h | h | h
            · exact h1 h
            · exact hd h.2.symm
            · exact hd h.2.symm
        rw [Finset.sum_congr rfl (fun d _ => this d), sum_ite_fin, if_neg h1, if_pos h2]; push_cast; ring
      · have : ∀ d : Fin (n + 1), (if (a = b ∧ b = c) ∨ (b = c ∧ c = d) ∨ (a = b ∧ c = d) then (0 : ℚ) else 1)
            = 1 := by
          intro d; rw [if_neg]; intro h; rcases h with h | h | h
          · exact h1 h
          · exact h2 (Or.inl h.1)
          · exact h2 (Or.inr h.1)
        rw [Finset.sum_congr rfl (fun d _ => this d), if_neg h1, if_neg h2]
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]; push_cast; ring
  have hc : ∀ a b : Fin (n + 1), ∑ c : Fin (n + 1),
      (if a = b ∧ b = c then (0 : ℚ) else if b = c ∨ a = b then (n : ℚ) else (n : ℚ) + 1) =
      if a = b then (n : ℚ) * n else (n : ℚ) + n * (n + 1) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      have : ∀ c : Fin (n + 1), (if a = a ∧ a = c then (0 : ℚ) else if a = c ∨ a = a then (n : ℚ) else (n : ℚ) + 1)
          = if c = a then (0 : ℚ) else (n : ℚ) := by
        intro c; by_cases h : c = a
        · subst h; simp
        · have : ¬ a = c := fun e => h e.symm
          simp [this, h]
      rw [Finset.sum_congr rfl (fun c _ => this c), sum_ite_fin, if_pos rfl]; push_cast; ring
    · have : ∀ c : Fin (n + 1), (if a = b ∧ b = c then (0 : ℚ) else if b = c ∨ a = b then (n : ℚ) else (n : ℚ) + 1)
          = if c = b then (n : ℚ) else (n : ℚ) + 1 := by
        intro c; by_cases h : c = b
        · subst h; simp [hab]
        · have : ¬ b = c := fun e => h e.symm
          simp [this, hab, h]
      rw [Finset.sum_congr rfl (fun c _ => this c), sum_ite_fin, if_neg hab]; push_cast; ring
  have hb : ∀ a : Fin (n + 1), ∑ b : Fin (n + 1), (if a = b then (n : ℚ) * n else n + n * (n + 1)) =
      n * n + n * (n + n * (n + 1)) := by
    intro a
    have : ∀ b : Fin (n + 1), (if a = b then (n : ℚ) * n else n + n * (n + 1)) =
        if b = a then (n : ℚ) * n else n + n * (n + 1) := by
      intro b; by_cases h : b = a
      · subst h; simp
      · have : ¬ a = b := fun e => h e.symm
        simp [this, h]
    rw [Finset.sum_congr rfl (fun b _ => this b), sum_ite_fin]; push_cast; ring
  simp only [hd, hc, hb, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

theorem pairs (n : ℕ) (hn : 1 ≤ n) : ∑ a ∈ range (n + 1), ∑ c ∈ range (n + 1),
    (if c = a + 2 ∨ a = c + 1 then (1 : ℚ) else 0) = 2 * n - 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  | succ k hk ih =>
    have e1 : ∀ a ∈ range (k + 1), ∑ c ∈ range (k + 1 + 1),
        (if c = a + 2 ∨ a = c + 1 then (1 : ℚ) else 0) =
        ∑ c ∈ range (k + 1), (if c = a + 2 ∨ a = c + 1 then (1 : ℚ) else 0) +
          (if a = k - 1 then 1 else 0) := by
      intro a ha
      have := mem_range.1 ha
      rw [sum_range_succ]
      congr 1
      by_cases h : a = k - 1
      · rw [if_pos (Or.inl (by omega)), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    rw [sum_range_succ, Finset.sum_congr rfl e1, sum_add_distrib, ih,
      Finset.sum_ite_eq' (range (k + 1)) (k - 1) (fun _ => (1 : ℚ)), if_pos (mem_range.2 (by omega))]
    have e3 : ∑ c ∈ range (k + 1 + 1), (if c = k + 1 + 2 ∨ k + 1 = c + 1 then (1 : ℚ) else 0) = 1 := by
      have : ∀ c ∈ range (k + 1 + 1), (if c = k + 1 + 2 ∨ k + 1 = c + 1 then (1 : ℚ) else 0) =
          if c = k then 1 else 0 := by
        intro c hc
        have := mem_range.1 hc
        by_cases h : c = k
        · rw [if_pos (Or.inr (by omega)), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (range (k + 1 + 1)) k (fun _ => (1 : ℚ)),
        if_pos (mem_range.2 (by omega))]
    rw [e3]; push_cast; ring

theorem fin_to_range (n : ℕ) (g : ℕ → ℕ → ℚ) :
    ∑ a : Fin (n + 1), ∑ c : Fin (n + 1), g a.val c.val =
      ∑ a ∈ range (n + 1), ∑ c ∈ range (n + 1), g a c := by
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ c : Fin (n + 1), g a c.val)]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun c => g a c) (n + 1)

theorem ap_total (n : ℕ) (hn : 1 ≤ n) : ∑ a : Fin (n + 1), ∑ b : Fin (n + 1), ∑ c : Fin (n + 1),
    ∑ d : Fin (n + 1),
      (if a = b ∧ c = d ∧ (c.val = a.val + 2 ∨ a.val = c.val + 1) then (1 : ℚ) else 0) = 2 * n - 1 := by
  have hap : ∀ a b : Fin (n + 1), ∑ c : Fin (n + 1), ∑ d : Fin (n + 1),
      (if a = b ∧ c = d ∧ (c.val = a.val + 2 ∨ a.val = c.val + 1) then (1 : ℚ) else 0) =
      if a = b then ∑ c : Fin (n + 1), (if c.val = a.val + 2 ∨ a.val = c.val + 1 then (1 : ℚ) else 0)
      else 0 := by
    intro a b
    by_cases hb : a = b
    · rw [if_pos hb]
      refine Finset.sum_congr rfl fun c _ => ?_
      have : ∀ d : Fin (n + 1), (if a = b ∧ c = d ∧ (c.val = a.val + 2 ∨ a.val = c.val + 1) then (1 : ℚ) else 0)
          = if d = c then (if c.val = a.val + 2 ∨ a.val = c.val + 1 then (1 : ℚ) else 0) else 0 := by
        intro d
        by_cases hd : d = c
        · subst hd; simp [hb]
        · have : ¬ c = d := fun e => hd e.symm
          simp [this, hd]
      rw [Finset.sum_congr rfl (fun d _ => this d), Finset.sum_ite_eq' univ c, if_pos (mem_univ c)]
    · rw [if_neg hb]; simp [hb]
  have : ∀ a : Fin (n + 1), ∑ b : Fin (n + 1), ∑ c : Fin (n + 1), ∑ d : Fin (n + 1),
      (if a = b ∧ c = d ∧ (c.val = a.val + 2 ∨ a.val = c.val + 1) then (1 : ℚ) else 0) =
      ∑ c : Fin (n + 1), (if c.val = a.val + 2 ∨ a.val = c.val + 1 then (1 : ℚ) else 0) := by
    intro a
    rw [Finset.sum_congr rfl (fun b _ => hap a b), Finset.sum_ite_eq univ a, if_pos (mem_univ a)]
  rw [Finset.sum_congr rfl (fun a _ => this a)]
  rw [fin_to_range n (fun a c => if c = a + 2 ∨ a = c + 1 then (1 : ℚ) else 0)]
  exact pairs n hn

theorem count_eq (n : ℕ) (hn : 1 ≤ n) :
    (count n : ℚ) = (n : ℚ) ^ 2 * (n + 1) * (n + 3) + 2 * n - 1 := by
  classical
  unfold count
  rw [Finset.card_filter]
  push_cast
  have split : ∀ w : Word n, (if ¬ two w ∨ allowedPair w then (1 : ℚ) else 0) =
      (if two w then 0 else 1) + (if allowedPair w then 1 else 0) := by
    rintro ⟨a, b, c, d⟩
    simp only [two, allowedPair]
    by_cases h1 : (a = b ∧ b = c) ∨ (b = c ∧ c = d) ∨ (a = b ∧ c = d) <;>
      by_cases h2 : a = b ∧ c = d ∧ (c.val = a.val + 2 ∨ a.val = c.val + 1) <;>
      simp only [h1, h2, not_true_eq_false, not_false_eq_true, or_false, if_true,
        if_false] <;> norm_num
  rw [Finset.sum_congr rfl (fun w _ => split w), sum_add_distrib]
  simp only [Fintype.sum_prod_type, two, allowedPair]
  have A := notwo n
  have B := ap_total n hn
  convert congrArg₂ (· + ·) A B using 12
  all_goals first | ring1 | congr

theorem terms_eq (j : ℕ) (hj : 1 ≤ j) :
    terms j = (j : ℤ) ^ 4 + 4 * j ^ 3 + 3 * j ^ 2 + 2 * j - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have h := count_eq (k + 1) hj
  have : ((count (k + 1) : ℤ) : ℚ) =
      ((((k + 1 : ℕ) : ℤ) ^ 4 + 4 * ((k + 1 : ℕ) : ℤ) ^ 3 + 3 * ((k + 1 : ℕ) : ℤ) ^ 2 +
        2 * ((k + 1 : ℕ) : ℤ) - 1 : ℤ) : ℚ) := by
    rw [Int.cast_natCast, h]; push_cast; ring
  rw [terms]; exact_mod_cast this

theorem terms_succ (n : ℕ) :
    terms (n + 1) = ((n : ℤ) + 1) ^ 4 + 4 * (n + 1) ^ 3 + 3 * (n + 1) ^ 2 + 2 * (n + 1) - 1 := by
  rw [terms_eq (n + 1) (by omega)]; push_cast; ring

theorem recur (n : ℕ) : terms (n + 6) = 5 * terms (n + 5) - 10 * terms (n + 4) +
    10 * terms (n + 3) - 5 * terms (n + 2) + terms (n + 1) := by
  rw [terms_eq (n + 6) (by omega), terms_eq (n + 5) (by omega), terms_eq (n + 4) (by omega),
    terms_eq (n + 3) (by omega), terms_eq (n + 2) (by omega), terms_eq (n + 1) (by omega)]
  push_cast; ring

open PowerSeries in
theorem gf : ((1 : PowerSeries ℤ) - X) ^ 5 * PowerSeries.mk terms =
    (X * (3 - X) * (3 + 7 * X + X ^ 2 + X ^ 3) : PowerSeries ℤ) := by
  have e1 : ((1 - X) ^ 5 : PowerSeries ℤ) =
      1 - C 5 * X ^ 1 + C 10 * X ^ 2 - C 10 * X ^ 3 + C 5 * X ^ 4 - X ^ 5 := by
    simp only [map_ofNat, pow_one]; ring
  have e2 : (X * (3 - X) * (3 + 7 * X + X ^ 2 + X ^ 3) : PowerSeries ℤ) =
      C 9 * X ^ 1 + C 18 * X ^ 2 - C 4 * X ^ 3 + C 2 * X ^ 4 - X ^ 5 := by
    simp only [map_ofNat, pow_one]; ring
  rw [e1, e2]
  ext k
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add, coeff_C_mul, coeff_X_pow_mul',
    coeff_mk, coeff_X_pow]
  have t0 : terms 0 = 0 := rfl
  rcases Nat.lt_or_ge k 6 with h | h
  · interval_cases k <;>
      simp [t0, terms_eq 1 (by norm_num), terms_eq 2 (by norm_num), terms_eq 3 (by norm_num),
        terms_eq 4 (by norm_num), terms_eq 5 (by norm_num)]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega, show 3 ≤ j + 6 by omega,
      show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega, ↓reduceIte, show j + 6 ≠ 1 by omega,
      show j + 6 ≠ 2 by omega, show j + 6 ≠ 3 by omega, show j + 6 ≠ 4 by omega,
      show j + 6 ≠ 5 by omega,
      show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
      show j + 6 - 3 = j + 3 by omega, show j + 6 - 4 = j + 2 by omega,
      show j + 6 - 5 = j + 1 by omega]
    rw [terms_eq (j + 6) (by omega), terms_eq (j + 5) (by omega), terms_eq (j + 4) (by omega),
      terms_eq (j + 3) (by omega), terms_eq (j + 2) (by omega), terms_eq (j + 1) (by omega)]
    push_cast; ring

end A269641P

theorem OMA.solution : type_of% @OMA.S_oeis_a269641.main :=
  ⟨A269641P.terms_succ, A269641P.recur, A269641P.gf⟩
