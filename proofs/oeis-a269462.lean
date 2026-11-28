import OMAStatements.S_oeis_a269462

open OMA.S_oeis_a269462 PowerSeries

-- A word of length n + 1 is a first letter followed by a word of length n.
private theorem card_cons {α : Type} [Fintype α] [DecidableEq α] (n : ℕ) (P : List α → Bool) :
    (Finset.univ.filter fun x : Fin (n + 1) → α => P (List.ofFn x) = true).card =
      ∑ c : α, (Finset.univ.filter fun x : Fin n → α => P (c :: List.ofFn x) = true).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ, Fin.consEquiv]

private theorem sum_one {α : Type} [Fintype α] [DecidableEq α] (p : α) (A B : ℕ) :
    ∑ c : α, (if c = p then A else B) = A + (Fintype.card α - 1) * B := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), if_pos rfl,
    Finset.sum_congr rfl (fun c hc => if_neg (Finset.ne_of_mem_erase hc)), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul]

private theorem sum_two {α : Type} [Fintype α] [DecidableEq α] (p q : α) (h : q ≠ p)
    (A B C : ℕ) : ∑ c : α, (if c = p then A else if c = q then B else C) =
      A + B + (Fintype.card α - 2) * C := by
  have hq : q ∈ Finset.univ.erase p := Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), if_pos rfl,
    ← Finset.add_sum_erase _ _ hq, if_neg h, if_pos rfl,
    Finset.sum_congr rfl (fun c hc => by
      rw [if_neg (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)),
        if_neg (Finset.ne_of_mem_erase hc)]),
    Finset.sum_const, Finset.card_erase_of_mem hq,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul,
    Nat.sub_sub, add_assoc]

-- Counts of the completions of length n from the three kinds of state: no repeat yet; the
-- last repeated value equals the current letter; it differs from the current letter.
private def cnt (k : ℕ) : ℕ → ℕ × ℕ × ℕ
  | 0 => (1, 1, 1)
  | n + 1 => ((k - 1) * (cnt k n).1 + (cnt k n).2.1, (k - 1) * (cnt k n).2.2,
      2 * (cnt k n).2.1 + (k - 2) * (cnt k n).2.2)

private def cls {α : Type} [DecidableEq α] (k n : ℕ) : Option α → α → ℕ
  | none, _ => (cnt k n).1
  | some q, p => if q = p then (cnt k n).2.1 else (cnt k n).2.2

private def F {α : Type} [Fintype α] [DecidableEq α] (r : Option α) (p : α) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → α => ok r p (List.ofFn x) = true).card

private theorem F_eq {α : Type} [Fintype α] [DecidableEq α] (n : ℕ) :
    ∀ (r : Option α) (p : α), F r p n = cls (Fintype.card α) n r p := by
  induction n with
  | zero =>
    intro r p
    cases r with
    | none => simp [F, ok, cls, cnt]
    | some q => by_cases h : q = p <;> simp [F, ok, cls, cnt, h]
  | succ n ih =>
    intro r p
    have key : ∀ c : α, (Finset.univ.filter fun x : Fin n → α =>
        ok r p (c :: List.ofFn x) = true).card =
        if c = p then (if r = some c then 0 else F (some c) c n) else F r c n := by
      intro c
      by_cases hc : c = p
      · subst hc
        by_cases hr : r = some c <;> simp [ok, hr, F]
      · simp [ok, hc, F]
    rw [F, card_cons, Finset.sum_congr rfl (fun c _ => key c)]
    simp only [ih]
    cases r with
    | none =>
      rw [Finset.sum_congr rfl (g := fun c => if c = p then (cnt (Fintype.card α) n).2.1
          else (cnt (Fintype.card α) n).1) (by intro c _; by_cases hc : c = p <;> simp [hc, cls]),
        sum_one]
      simp only [cls, cnt]
      ring
    | some q =>
      by_cases hq : q = p
      · subst hq
        rw [Finset.sum_congr rfl (g := fun c => if c = q then 0
            else (cnt (Fintype.card α) n).2.2)
            (by
              intro c _
              by_cases hc : c = q
              · simp [hc]
              · simp [hc, cls, Ne.symm hc]), sum_one]
        simp [cls, cnt]
      · rw [Finset.sum_congr rfl (g := fun c => if c = p then (cnt (Fintype.card α) n).2.1
            else if c = q then (cnt (Fintype.card α) n).2.1 else (cnt (Fintype.card α) n).2.2)
            (by
              intro c _
              by_cases hc : c = p
              · subst hc; simp [cls, hq]
              · by_cases hcq : c = q
                · subst hcq; simp [cls, hc]
                · simp [hc, hcq, cls, Ne.symm hcq]), sum_two p q hq]
        simp only [cls, if_neg hq, cnt]
        ring

private theorem a_succ (n : ℕ) : a (n + 1) = 4 * (cnt 4 n).1 := by
  rw [a, card_cons]
  have h : ∀ c : Fin 4, (Finset.univ.filter fun x : Fin n → Fin 4 =>
      valid (c :: List.ofFn x) = true).card = (cnt (Fintype.card (Fin 4)) n).1 :=
    fun c => F_eq (α := Fin 4) n none c
  simp [h]

private theorem cnt_rec (n : ℕ) :
    (cnt 4 (n + 3)).1 + 18 * (cnt 4 n).1 = 5 * (cnt 4 (n + 2)).1 := by
  simp only [cnt]
  norm_num
  ring

private theorem a_rec (n : ℕ) : a (n + 4) + 18 * a (n + 1) = 5 * a (n + 3) := by
  rw [a_succ, a_succ, a_succ]
  have := cnt_rec n
  omega

private theorem a1 : a 1 = 4 := by rw [a_succ]; rfl
private theorem a2 : a 2 = 16 := by rw [a_succ]; rfl
private theorem a3 : a 3 = 60 := by rw [a_succ]; rfl

private theorem gf :
    (1 - 3 * X) * (1 - 2 * X - 6 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (4 * X * (1 - X - 5 * X ^ 2) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 3 * X) * (1 - 2 * X - 6 * X ^ 2) * s =
      s - (s * C (5 : ℤ)) * X ^ 1 + (s * C (18 : ℤ)) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (4 * X * (1 - X - 5 * X ^ 2) : PowerSeries ℤ) =
      C (4 : ℤ) * X ^ 1 - C (4 : ℤ) * X ^ 2 - C (20 : ℤ) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n) with h | h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · subst h; simp [a2, a3]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have := a_rec m
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 3 = m + 1 by omega]
    simp
    omega

private noncomputable def R (n : ℕ) : ℝ :=
  (-28 * 3 ^ n + (49 - 17 * Real.sqrt 7) * (1 - Real.sqrt 7) ^ n +
    (1 + Real.sqrt 7) ^ n * (49 + 17 * Real.sqrt 7)) / 63

private theorem root_step (x : ℝ) (h : x ^ 2 = 2 * x + 6) (j : ℕ) :
    x ^ (j + 3) = 5 * x ^ (j + 2) - 18 * x ^ j := by
  linear_combination (x ^ j * (x - 3)) * h

private theorem R_rec (j : ℕ) : R (j + 4) = 5 * R (j + 3) - 18 * R (j + 1) := by
  have hs : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h1 := root_step (1 - Real.sqrt 7) (by linear_combination hs) (j + 1)
  have h2 := root_step (1 + Real.sqrt 7) (by linear_combination hs) (j + 1)
  have h3 : (3 : ℝ) ^ (j + 1 + 3) = 5 * 3 ^ (j + 1 + 2) - 18 * 3 ^ (j + 1) := by ring
  unfold R
  rw [show j + 4 = j + 1 + 3 by ring, show j + 3 = j + 1 + 2 by ring, h1, h2, h3]
  ring

private theorem closed (m : ℕ) :
    (a (m + 1) : ℝ) = R (m + 1) ∧ (a (m + 2) : ℝ) = R (m + 2) ∧ (a (m + 3) : ℝ) = R (m + 3) := by
  have hs : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [a1, R, eq_div_iff (by norm_num)]; push_cast; linear_combination (-34) * hs
    · rw [a2, R, eq_div_iff (by norm_num)]; push_cast; linear_combination (-166) * hs
    · rw [a3, R, eq_div_iff (by norm_num)]; push_cast
      linear_combination (-(34 * Real.sqrt 7 ^ 2 + 634)) * hs
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hr : ((a (m + 4) : ℕ) : ℝ) + 18 * (a (m + 1) : ℝ) = 5 * (a (m + 3) : ℝ) := by
      exact_mod_cast a_rec m
    rw [show m + 1 + 3 = m + 4 by ring, R_rec]
    rw [show m + 1 + 2 = m + 3 by ring] at h3
    linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a269462.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [(closed m).1, R]
