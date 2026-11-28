import OMAStatements.S_oeis_a268941

open OMA.S_oeis_a268941 PowerSeries

-- A word of length n + 1 is a first letter followed by a word of length n.
private theorem card_cons {α : Type} [Fintype α] [DecidableEq α] (n : ℕ) (P : List α → Bool) :
    (Finset.univ.filter fun x : Fin (n + 1) → α => P (List.ofFn x) = true).card =
      ∑ c : α, (Finset.univ.filter fun x : Fin n → α => P (c :: List.ofFn x) = true).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ, Fin.consEquiv]

private theorem sum_one (p : Fin 6) (A B : ℕ) :
    ∑ c : Fin 6, (if c = p then A else B) = A + 5 * B := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), if_pos rfl,
    Finset.sum_congr rfl (fun c hc => if_neg (Finset.ne_of_mem_erase hc)), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul]
  simp

-- Counts of the completions of length n from the states: no repeat yet; and, after a repeat
-- with value r at current letter p, the difference p - r being 0, 1, or anything else.
private def cnt : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 1, 1, 1)
  | n + 1 => (5 * (cnt n).1 + (cnt n).2.1, (cnt n).2.2.1 + 4 * (cnt n).2.2.2,
      2 * (cnt n).2.1 + 4 * (cnt n).2.2.2, (cnt n).2.1 + (cnt n).2.2.1 + 3 * (cnt n).2.2.2)

private def cls (n : ℕ) (d : Fin 6) : ℕ :=
  if d = 0 then (cnt n).2.1 else if d = 1 then (cnt n).2.2.1 else (cnt n).2.2.2

private def F (r : Option (Fin 6)) (p : Fin 6) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 6 => ok r p (List.ofFn x) = true).card

private theorem F_some (n : ℕ) : ∀ q p : Fin 6, F (some q) p n = cls n (p - q) := by
  induction n with
  | zero =>
    intro q p
    simp only [F, cls, cnt]
    split_ifs <;> simp [ok]
  | succ n ih =>
    intro q p
    have key : ∀ c : Fin 6, (Finset.univ.filter fun x : Fin n → Fin 6 =>
        ok (some q) p (c :: List.ofFn x) = true).card =
        if c = p then (if c = q + 1 then F (some c) c n else 0) else F (some q) c n := by
      intro c
      by_cases hc : c = p
      · subst hc
        by_cases hr : c = q + 1 <;> simp [ok, hr, F]
      · simp [ok, hc, F]
    rw [F, card_cons, Finset.sum_congr rfl (fun c _ => key c)]
    simp only [ih]
    obtain ⟨d, rfl⟩ : ∃ d, p = d + q := ⟨p - q, (sub_add_cancel p q).symm⟩
    rw [← Equiv.sum_comp (Equiv.addRight q), add_comm q 1]
    simp only [Equiv.coe_addRight, add_left_inj, add_sub_cancel_right, sub_self]
    fin_cases d <;> simp [Fin.sum_univ_six, cls, cnt] <;> ring

private theorem F_none (n : ℕ) : ∀ p : Fin 6, F none p n = (cnt n).1 := by
  induction n with
  | zero => intro p; simp [F, ok, cnt]
  | succ n ih =>
    intro p
    have key : ∀ c : Fin 6, (Finset.univ.filter fun x : Fin n → Fin 6 =>
        ok none p (c :: List.ofFn x) = true).card =
        if c = p then (cnt n).2.1 else (cnt n).1 := by
      intro c
      by_cases hc : c = p
      · subst hc
        have := F_some n c c
        simp only [sub_self, cls] at this
        simpa [ok, F] using this
      · rw [if_neg hc, ← ih c]
        simp [ok, hc, F]
    rw [F, card_cons, Finset.sum_congr rfl (fun c _ => key c), sum_one]
    simp only [cnt]
    ring

private theorem a_succ (n : ℕ) : a (n + 1) = 6 * (cnt n).1 := by
  rw [a, card_cons]
  have h : ∀ c : Fin 6, (Finset.univ.filter fun x : Fin n → Fin 6 =>
      valid (c :: List.ofFn x) = true).card = (cnt n).1 :=
    fun c => F_none n c
  simp [h]

private theorem cnt_rec (n : ℕ) :
    (cnt (n + 3)).1 + 14 * (cnt (n + 1)).1 + 30 * (cnt n).1 = 9 * (cnt (n + 2)).1 := by
  simp only [cnt]
  ring

private theorem a_rec (n : ℕ) :
    a (n + 4) + 14 * a (n + 2) + 30 * a (n + 1) = 9 * a (n + 3) := by
  rw [a_succ, a_succ, a_succ, a_succ]
  have := cnt_rec n
  omega

private theorem a1 : a 1 = 6 := by rw [a_succ]; rfl
private theorem a2 : a 2 = 36 := by rw [a_succ]; rfl
private theorem a3 : a 3 = 210 := by rw [a_succ]; rfl

private theorem gf :
    (1 - 5 * X) * (1 - 4 * X - 6 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (6 * X * (1 - 3 * X - 5 * X ^ 2) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 5 * X) * (1 - 4 * X - 6 * X ^ 2) * s =
      s - (s * C (9 : ℤ)) * X ^ 1 + (s * C (14 : ℤ)) * X ^ 2 + (s * C (30 : ℤ)) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (6 * X * (1 - 3 * X - 5 * X ^ 2) : PowerSeries ℤ) =
      C (6 : ℤ) * X ^ 1 - C (18 : ℤ) * X ^ 2 - C (30 : ℤ) * X ^ 3 := by
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
  -12 * 5 ^ (1 + n) + (35 - 11 * Real.sqrt 10) * (2 - Real.sqrt 10) ^ n +
    (2 + Real.sqrt 10) ^ n * (35 + 11 * Real.sqrt 10)

private theorem root_step (y : ℝ) (h : y ^ 2 = 4 * y + 6) (j : ℕ) :
    y ^ (j + 3) = 9 * y ^ (j + 2) - 14 * y ^ (j + 1) - 30 * y ^ j := by
  linear_combination (y ^ j * (y - 5)) * h

private theorem S_rec (j : ℕ) : S (j + 4) = 9 * S (j + 3) - 14 * S (j + 2) - 30 * S (j + 1) := by
  have hs : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have h1 := root_step (2 - Real.sqrt 10) (by linear_combination hs) (j + 1)
  have h2 := root_step (2 + Real.sqrt 10) (by linear_combination hs) (j + 1)
  unfold S
  rw [show j + 4 = j + 1 + 3 by ring, show j + 3 = j + 1 + 2 by ring,
    show j + 2 = j + 1 + 1 by ring, h1, h2]
  ring

private theorem closed (m : ℕ) :
    (a (m + 1) : ℝ) * 10 = S (m + 1) ∧ (a (m + 2) : ℝ) * 10 = S (m + 2) ∧
    (a (m + 3) : ℝ) * 10 = S (m + 3) := by
  have hs : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [a1, S]; push_cast; linear_combination (-22) * hs
    · rw [a2, S]; push_cast; linear_combination (-158) * hs
    · rw [a3, S]; push_cast; linear_combination (-22 * Real.sqrt 10 ^ 2 - 904) * hs
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hr : ((a (m + 4) : ℕ) : ℝ) + 14 * (a (m + 2) : ℝ) + 30 * (a (m + 1) : ℝ) =
        9 * (a (m + 3) : ℝ) := by
      exact_mod_cast a_rec m
    rw [show m + 1 + 3 = m + 4 by ring, S_rec]
    rw [show m + 1 + 2 = m + 3 by ring] at h3
    rw [show m + 1 + 1 = m + 2 by ring] at h2
    linear_combination (10 : ℝ) * hr + 9 * h3 - 14 * h2 - 30 * h1

theorem OMA.solution : type_of% @OMA.S_oeis_a268941.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [eq_div_iff (by norm_num), (closed m).1, S]
