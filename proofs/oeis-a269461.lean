import OMAStatements.S_oeis_a269461

open OMA.S_oeis_a269461 PowerSeries

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

private theorem a_succ (n : ℕ) : a (n + 1) = 3 * (cnt 3 n).1 := by
  rw [a, card_cons]
  have h : ∀ c : Fin 3, (Finset.univ.filter fun x : Fin n → Fin 3 =>
      valid (c :: List.ofFn x) = true).card = (cnt (Fintype.card (Fin 3)) n).1 :=
    fun c => F_eq (α := Fin 3) n none c
  simp [h]

private theorem cnt_rec (n : ℕ) :
    (cnt 3 (n + 3)).1 + 8 * (cnt 3 n).1 = 3 * (cnt 3 (n + 2)).1 + 2 * (cnt 3 (n + 1)).1 := by
  simp only [cnt]
  norm_num
  ring

private theorem a_rec (n : ℕ) : a (n + 4) + 8 * a (n + 1) = 3 * a (n + 3) + 2 * a (n + 2) := by
  rw [a_succ, a_succ, a_succ, a_succ]
  have := cnt_rec n
  omega

private theorem a1 : a 1 = 3 := by rw [a_succ]; rfl
private theorem a2 : a 2 = 9 := by rw [a_succ]; rfl
private theorem a3 : a 3 = 24 := by rw [a_succ]; rfl

private theorem gf :
    (1 - 2 * X) * (1 - X - 4 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (3 * X * (1 - 3 * X ^ 2) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 2 * X) * (1 - X - 4 * X ^ 2) * s =
      s - (s * C (3 : ℤ)) * X ^ 1 - (s * C (2 : ℤ)) * X ^ 2 + (s * C (8 : ℤ)) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (3 * X * (1 - 3 * X ^ 2) : PowerSeries ℤ) = C (3 : ℤ) * X ^ 1 - C (9 : ℤ) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n) with h | h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · subst h; simp [a1, a2, a3]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have := a_rec m
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega]
    simp
    omega

private noncomputable def S (n : ℕ) : ℝ :=
  -51 * 4 ^ (1 + n) + (255 - 57 * Real.sqrt 17) * (1 - Real.sqrt 17) ^ n +
    3 * (1 + Real.sqrt 17) ^ n * (85 + 19 * Real.sqrt 17)

private theorem root_step (y : ℝ) (h : y ^ 2 = 2 * y + 16) (j : ℕ) :
    y ^ (j + 3) = 6 * y ^ (j + 2) + 8 * y ^ (j + 1) - 64 * y ^ j := by
  linear_combination (y ^ j * (y - 4)) * h

private theorem S_rec (j : ℕ) : S (j + 4) = 6 * S (j + 3) + 8 * S (j + 2) - 64 * S (j + 1) := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h1 := root_step (1 - Real.sqrt 17) (by linear_combination hs) (j + 1)
  have h2 := root_step (1 + Real.sqrt 17) (by linear_combination hs) (j + 1)
  unfold S
  rw [show j + 4 = j + 1 + 3 by ring, show j + 3 = j + 1 + 2 by ring,
    show j + 2 = j + 1 + 1 by ring, h1, h2]
  ring

private theorem closed (m : ℕ) :
    (a (m + 1) : ℝ) * (272 * 2 ^ (m + 1)) = S (m + 1) ∧
    (a (m + 2) : ℝ) * (272 * 2 ^ (m + 2)) = S (m + 2) ∧
    (a (m + 3) : ℝ) * (272 * 2 ^ (m + 3)) = S (m + 3) := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [a1, S]; push_cast; linear_combination (-114) * hs
    · rw [a2, S]; push_cast; linear_combination (-738) * hs
    · rw [a3, S]; push_cast; linear_combination (-114 * Real.sqrt 17 ^ 2 - 3810) * hs
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hr : ((a (m + 4) : ℕ) : ℝ) + 8 * (a (m + 1) : ℝ) =
        3 * (a (m + 3) : ℝ) + 2 * (a (m + 2) : ℝ) := by
      exact_mod_cast a_rec m
    rw [show m + 1 + 3 = m + 4 by ring, S_rec, ← h1, ← h2, ← h3]
    rw [show m + 1 + 2 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring]
    linear_combination (272 * 2 ^ (m + 4) : ℝ) * hr

theorem OMA.solution : type_of% @OMA.S_oeis_a269461.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := (closed m).1
  have hz : (2 : ℝ) ^ (-4 - ((m + 1 : ℕ) : ℤ)) = ((2 : ℝ) ^ (m + 1) * 16)⁻¹ := by
    rw [show (-4 - ((m + 1 : ℕ) : ℤ)) = -(((m + 1 : ℕ) : ℤ) + 4) by ring, zpow_neg,
      zpow_add₀ two_ne_zero, zpow_natCast]
    norm_num
  rw [hz, ← S, ← h]
  field_simp
  ring
