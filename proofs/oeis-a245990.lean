import OMAStatements.S_oeis_a245990

-- Credit: @RiverMint78
-- A valid word has two possible extensions, plus one more when the first two digits agree.

open OMA.S_oeis_a245990

lemma words_cons_valid {m : ℕ} (c : Fin 4) (w : Fin (m+2) → Fin 4) :
    isValid (m+3) (Fin.cons c w) ↔
      isValid (m+2) w ∧ (c : ℕ) + (w 0 : ℕ) ≠ 3 ∧ (c : ℕ) + (w 1 : ℕ) ≠ 3 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij hdist
      simpa only [Fin.cons_succ] using
        h i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij) (by simpa using hdist)
    · simpa only [Fin.cons_zero, Fin.cons_succ] using
        h 0 (0 : Fin (m+2)).succ (by change 0 < 0 + 1; decide) (by simp)
    · simpa only [Fin.cons_zero, Fin.cons_succ] using
        h 0 (1 : Fin (m+2)).succ (by change 0 < (1 : Fin (m+2)).val + 1; omega)
          (by change (1 : Fin (m+2)).val + 1 - 0 ≤ 2; simp)
  · rintro ⟨hw, hzero, hone⟩ i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · intro _ hdist
        simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ] at hdist
        have hj : j = 0 ∨ j = 1 := by
          rcases (show j.val = 0 ∨ j.val = 1 by omega) with hj | hj
          · exact Or.inl (Fin.ext (by simpa using hj))
          · exact Or.inr (Fin.ext (by simpa using hj))
        rcases hj with rfl | rfl
        · simpa only [Fin.cons_zero, Fin.cons_succ] using hzero
        · simpa only [Fin.cons_zero, Fin.cons_succ] using hone
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · intro hij hdist
        simpa only [Fin.cons_succ] using
          hw i j (Fin.succ_lt_succ_iff.mp hij) (by simpa using hdist)

open OMA.S_oeis_a245990

def wordsWeight {k : ℕ} (w : Fin k → Fin 4) : ℕ := if isValid k w then 1 else 0

def wordsTotal (k : ℕ) : ℕ := ∑ w : Fin k → Fin 4, wordsWeight w

lemma words_heads {m : ℕ} (f : (Fin (m + 1) → Fin 4) → ℕ) :
    (∑ w, f w) = ∑ w : Fin m → Fin 4, ∑ c : Fin 4, f (Fin.cons c w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 4)).sum_comp f, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

lemma words_finite_choices : ∀ u v : Fin 4, u.val + v.val ≠ 3 →
    (∑ c : Fin 4, ∑ d : Fin 4,
      if (c.val + u.val ≠ 3 ∧ c.val + v.val ≠ 3) ∧
        d.val + c.val ≠ 3 ∧ d.val + u.val ≠ 3 then 1 else 0) =
    2 * (∑ c : Fin 4, if c.val + u.val ≠ 3 ∧ c.val + v.val ≠ 3 then 1 else 0) + 1 := by
  decide

lemma words_children_two {m : ℕ} (w : Fin (m + 2) → Fin 4) :
    (∑ c : Fin 4, ∑ d : Fin 4, wordsWeight (Fin.cons d (Fin.cons c w))) =
    2 * (∑ c : Fin 4, wordsWeight (Fin.cons c w)) + wordsWeight w := by
  simp only [wordsWeight, words_cons_valid, Fin.cons_zero, Fin.cons_one]
  by_cases hw : isValid (m + 2) w
  · have huv : (w 0).val + (w 1).val ≠ 3 := hw 0 1 (by change (0 : ℕ) < (↑(1 : Fin (m + 2)) : ℕ); simp) (by simp)
    simp only [and_iff_right hw, if_pos hw]
    exact words_finite_choices (w 0) (w 1) huv
  · simp [hw]

lemma words_total_rec (m : ℕ) :
    wordsTotal (m + 4) = 2 * wordsTotal (m + 3) + wordsTotal (m + 2) := by
  calc
    wordsTotal (m + 4) =
        ∑ w : Fin (m + 2) → Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
          wordsWeight (Fin.cons d (Fin.cons c w)) :=
      (words_heads wordsWeight).trans (words_heads _)
    _ = ∑ w : Fin (m + 2) → Fin 4,
          (2 * (∑ c : Fin 4, wordsWeight (Fin.cons c w)) + wordsWeight w) :=
      Finset.sum_congr rfl (fun w _ => words_children_two w)
    _ = 2 * wordsTotal (m + 3) + wordsTotal (m + 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      unfold wordsTotal
      rw [words_heads (m := m + 2) wordsWeight]

lemma words_a (k : ℕ) : a (k + 1) = wordsTotal (k + 3) := by
  simp only [a, wordsTotal, wordsWeight, Finset.card_filter]

lemma words_recurrence (n : ℕ) (hn : 3 ≤ n) : a n = 2 * a (n-1) + a (n-2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  convert! words_total_rec (k + 1) using 1 <;>
    simp only [show 3 + k = k + 2 + 1 by omega, show k + 2 + 1 - 1 = k + 1 + 1 by omega,
      show k + 2 + 1 - 2 = k + 1 by omega, words_a]

open OMA.S_oeis_a245990 PowerSeries

lemma words_gf (h1 : a 1 = 28) (h2 : a 2 = 68)
    (hr : ∀ n : ℕ, 3 ≤ n → a n = 2 * a (n - 1) + a (n - 2)) :
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 2 * X - X ^ 2) = 4 * X * (7 + 3 * X) := by
  let F : PowerSeries ℚ := mk (fun n => (a n : ℚ))
  change F * (1 - 2 * X - X ^ 2) = _
  have hleft : F * (1 - 2 * X - X ^ 2) = F - F * X - F * X - F * X * X := by ring
  have hright : 4 * X * (7 + 3 * (X : PowerSeries ℚ)) =
      C (28 : ℚ) * X + C (12 : ℚ) * X * X := by
    simp only [map_ofNat]
    ring
  rw [hleft, hright]
  ext n
  rcases n with _ | _ | _ | n
  · simp [F, a]
  · simp [F, coeff_succ_mul_X, h1, show a 0 = 0 from rfl]
  · norm_num [F, coeff_succ_mul_X, coeff_C, h1, h2, show a 0 = 0 from rfl]
  · have h := hr (n + 3) (by omega)
    have hz : (a (n + 3) : ℚ) = 2 * a (n + 2) + a (n + 1) := by exact_mod_cast h
    simp only [map_sub, map_add, coeff_succ_mul_X, F, coeff_mk, coeff_succ_C]
    linarith

open OMA.S_oeis_a245990

lemma words_initial : a 1 = 28 ∧ a 2 = 68 := by decide

lemma words_power_step (r : ℝ) (h : r^2 = 2*r+1) (k : ℕ) :
    r^(k+3) = 2*r^(k+2)+r^(k+1) := by
  linear_combination (norm := (simp only [pow_succ]; ring)) r^(k+1) * h

lemma words_closed (hr : ∀ n : ℕ, 3 ≤ n → a n = 2*a (n-1)+a (n-2)) :
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = Real.sqrt 2 *
        ((1 - Real.sqrt 2) ^ n * (-4 + 3 * Real.sqrt 2) +
         (1 + Real.sqrt 2) ^ n * (4 + 3 * Real.sqrt 2)) := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hm : (1 - Real.sqrt 2)^2 = 2*(1 - Real.sqrt 2)+1 := by nlinarith
  have hp : (1 + Real.sqrt 2)^2 = 2*(1 + Real.sqrt 2)+1 := by nlinarith
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    match n with
    | 0 => omega
    | 1 =>
      rw [words_initial.1]
      push_cast
      simp only [pow_one]
      nlinarith
    | 2 =>
      rw [words_initial.2]
      push_cast
      rw [hm, hp]
      nlinarith
    | k+3 =>
      rw [hr (k+3) (by omega)]
      push_cast
      rw [ih (k+2) (by omega) (by omega), ih (k+1) (by omega) (by omega),
        words_power_step _ hm, words_power_step _ hp]
      ring

theorem OMA.solution : type_of% @OMA.S_oeis_a245990.main :=
  ⟨words_recurrence, words_gf words_initial.1 words_initial.2 words_recurrence,
    words_closed words_recurrence⟩
