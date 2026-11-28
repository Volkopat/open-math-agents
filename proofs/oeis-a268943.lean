import OMAStatements.S_oeis_a268943

open OMA.S_oeis_a268943 PowerSeries

-- A word of length n + 1 is a first letter followed by a word of length n.
private theorem card_cons {α : Type} [Fintype α] [DecidableEq α] (n : ℕ) (P : List α → Bool) :
    (Finset.univ.filter fun x : Fin (n + 1) → α => P (List.ofFn x) = true).card =
      ∑ c : α, (Finset.univ.filter fun x : Fin n → α => P (c :: List.ofFn x) = true).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ, Fin.consEquiv]

private theorem sum_one (p : Fin 8) (A B : ℕ) :
    ∑ c : Fin 8, (if c = p then A else B) = A + 7 * B := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), if_pos rfl,
    Finset.sum_congr rfl (fun c hc => if_neg (Finset.ne_of_mem_erase hc)), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul]
  simp

-- Counts of the completions of length n from the states: no repeat yet; and, after a repeat
-- with value r at current letter p, the difference p - r being 0, 1, or anything else.
private def cnt : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 1, 1, 1)
  | n + 1 => (7 * (cnt n).1 + (cnt n).2.1, (cnt n).2.2.1 + 6 * (cnt n).2.2.2,
      2 * (cnt n).2.1 + 6 * (cnt n).2.2.2, (cnt n).2.1 + (cnt n).2.2.1 + 5 * (cnt n).2.2.2)

private def cls (n : ℕ) (d : Fin 8) : ℕ :=
  if d = 0 then (cnt n).2.1 else if d = 1 then (cnt n).2.2.1 else (cnt n).2.2.2

private def F (r : Option (Fin 8)) (p : Fin 8) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 8 => ok r p (List.ofFn x) = true).card

private theorem F_some (n : ℕ) : ∀ q p : Fin 8, F (some q) p n = cls n (p - q) := by
  induction n with
  | zero =>
    intro q p
    simp only [F, cls, cnt]
    split_ifs <;> simp [ok]
  | succ n ih =>
    intro q p
    have key : ∀ c : Fin 8, (Finset.univ.filter fun x : Fin n → Fin 8 =>
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
    fin_cases d <;> simp [Fin.sum_univ_eight, cls, cnt] <;> ring

private theorem F_none (n : ℕ) : ∀ p : Fin 8, F none p n = (cnt n).1 := by
  induction n with
  | zero => intro p; simp [F, ok, cnt]
  | succ n ih =>
    intro p
    have key : ∀ c : Fin 8, (Finset.univ.filter fun x : Fin n → Fin 8 =>
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

private theorem a_succ (n : ℕ) : a (n + 1) = 8 * (cnt n).1 := by
  rw [a, card_cons]
  have h : ∀ c : Fin 8, (Finset.univ.filter fun x : Fin n → Fin 8 =>
      valid (c :: List.ofFn x) = true).card = (cnt n).1 :=
    fun c => F_none n c
  simp [h]

private theorem cnt_rec (n : ℕ) :
    (cnt (n + 3)).1 + 34 * (cnt (n + 1)).1 + 56 * (cnt n).1 = 13 * (cnt (n + 2)).1 := by
  simp only [cnt]
  ring

private theorem a_rec (n : ℕ) :
    a (n + 4) + 34 * a (n + 2) + 56 * a (n + 1) = 13 * a (n + 3) := by
  rw [a_succ, a_succ, a_succ, a_succ]
  have := cnt_rec n
  omega

private theorem a1 : a 1 = 8 := by rw [a_succ]; rfl
private theorem a2 : a 2 = 64 := by rw [a_succ]; rfl
private theorem a3 : a 3 = 504 := by rw [a_succ]; rfl

private theorem gf :
    (1 - 7 * X) * (1 - 6 * X - 8 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (8 * X * (1 - 5 * X - 7 * X ^ 2) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 7 * X) * (1 - 6 * X - 8 * X ^ 2) * s =
      s - (s * C (13 : ℤ)) * X ^ 1 + (s * C (34 : ℤ)) * X ^ 2 + (s * C (56 : ℤ)) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (8 * X * (1 - 5 * X - 7 * X ^ 2) : PowerSeries ℤ) =
      C (8 : ℤ) * X ^ 1 - C (40 : ℤ) * X ^ 2 - C (56 : ℤ) * X ^ 3 := by
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

private noncomputable def R (n : ℕ) : ℝ :=
  (-272 * 7 ^ n + (153 - 37 * Real.sqrt 17) * (3 - Real.sqrt 17) ^ n +
    (3 + Real.sqrt 17) ^ n * (153 + 37 * Real.sqrt 17)) / 34

private theorem root_step (x : ℝ) (h : x ^ 2 = 6 * x + 8) (j : ℕ) :
    x ^ (j + 3) = 13 * x ^ (j + 2) - 34 * x ^ (j + 1) - 56 * x ^ j := by
  linear_combination (x ^ j * (x - 7)) * h

private theorem R_rec (j : ℕ) :
    R (j + 4) = 13 * R (j + 3) - 34 * R (j + 2) - 56 * R (j + 1) := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h1 := root_step (3 - Real.sqrt 17) (by linear_combination hs) (j + 1)
  have h2 := root_step (3 + Real.sqrt 17) (by linear_combination hs) (j + 1)
  have h3 : (7 : ℝ) ^ (j + 1 + 3) =
      13 * 7 ^ (j + 1 + 2) - 34 * 7 ^ (j + 1 + 1) - 56 * 7 ^ (j + 1) := by ring
  unfold R
  rw [show j + 4 = j + 1 + 3 by ring, show j + 3 = j + 1 + 2 by ring,
    show j + 2 = j + 1 + 1 by ring, h1, h2, h3]
  ring

private theorem closed (m : ℕ) :
    (a (m + 1) : ℝ) = R (m + 1) ∧ (a (m + 2) : ℝ) = R (m + 2) ∧ (a (m + 3) : ℝ) = R (m + 3) := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [a1, R, eq_div_iff (by norm_num)]; push_cast; linear_combination (-74) * hs
    · rw [a2, R, eq_div_iff (by norm_num)]; push_cast; linear_combination (-750) * hs
    · rw [a3, R, eq_div_iff (by norm_num)]; push_cast
      linear_combination (-(74 * Real.sqrt 17 ^ 2 + 6010)) * hs
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hr : ((a (m + 4) : ℕ) : ℝ) + 34 * (a (m + 2) : ℝ) + 56 * (a (m + 1) : ℝ) =
        13 * (a (m + 3) : ℝ) := by
      exact_mod_cast a_rec m
    rw [show m + 1 + 3 = m + 4 by ring, R_rec]
    rw [show m + 1 + 2 = m + 3 by ring] at h3
    rw [show m + 1 + 1 = m + 2 by ring] at h2
    linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a268943.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [(closed m).1, R]
