import OMAStatements.S_oeis_a269613

open OMA.S_oeis_a269613 PowerSeries

-- A word of length n + 1 is a first letter followed by a word of length n.
private theorem card_cons {α : Type} [Fintype α] [DecidableEq α] (n : ℕ) (P : List α → Bool) :
    (Finset.univ.filter fun x : Fin (n + 1) → α => P (List.ofFn x) = true).card =
      ∑ c : α, (Finset.univ.filter fun x : Fin n → α => P (c :: List.ofFn x) = true).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ, Fin.consEquiv]

private theorem sum_one (p : Fin 3) (A B : ℕ) :
    ∑ c : Fin 3, (if c = p then A else B) = A + 2 * B := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), if_pos rfl,
    Finset.sum_congr rfl (fun c hc => if_neg (Finset.ne_of_mem_erase hc)), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul]
  simp

-- On 0..2 the allowed differences 2, 0, -1 are exactly the residues other than 1 mod 3.
private theorem cond_iff (c v : Fin 3) :
    ((c.val : ℤ) - v.val = 2 ∨ (c.val : ℤ) - v.val = 0 ∨ (c.val : ℤ) - v.val = -1) ↔
      c ≠ v + 1 := by
  revert c v
  decide

private theorem ok_rep (q c : Fin 3) (l : List (Fin 3)) :
    ok (some q) c (c :: l) = (decide (c ≠ q + 1) && ok (some c) c l) := by
  simp only [ok, if_true, Option.all_some]
  congr 1
  exact decide_eq_decide.mpr (cond_iff c q)

-- Counts of the completions of length n from the states: no repeat yet; and, after a repeat
-- with value r at current letter p, the difference p - r being 0, 1 or 2 mod 3.
private def cnt : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 1, 1, 1)
  | n + 1 => (2 * (cnt n).1 + (cnt n).2.1, (cnt n).2.1 + (cnt n).2.2.1 + (cnt n).2.2.2,
      (cnt n).2.1 + (cnt n).2.2.2, 2 * (cnt n).2.1 + (cnt n).2.2.1)

private def cls (n : ℕ) (d : Fin 3) : ℕ :=
  if d = 0 then (cnt n).2.1 else if d = 1 then (cnt n).2.2.1 else (cnt n).2.2.2

private def F (r : Option (Fin 3)) (p : Fin 3) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 3 => ok r p (List.ofFn x) = true).card

private theorem F_some (n : ℕ) : ∀ q p : Fin 3, F (some q) p n = cls n (p - q) := by
  induction n with
  | zero =>
    intro q p
    simp only [F, cls, cnt]
    split_ifs <;> simp [ok]
  | succ n ih =>
    intro q p
    have key : ∀ c : Fin 3, (Finset.univ.filter fun x : Fin n → Fin 3 =>
        ok (some q) p (c :: List.ofFn x) = true).card =
        if c = p then (if c = q + 1 then 0 else F (some c) c n) else F (some q) c n := by
      intro c
      by_cases hc : c = p
      · subst hc
        by_cases hr : c = q + 1 <;> simp [ok_rep, hr, F]
      · simp [ok, hc, F]
    rw [F, card_cons, Finset.sum_congr rfl (fun c _ => key c)]
    simp only [ih]
    obtain ⟨d, rfl⟩ : ∃ d, p = d + q := ⟨p - q, (sub_add_cancel p q).symm⟩
    rw [← Equiv.sum_comp (Equiv.addRight q), add_comm q 1]
    simp only [Equiv.coe_addRight, add_left_inj, add_sub_cancel_right, sub_self]
    fin_cases d <;> simp [Fin.sum_univ_three, cls, cnt] <;> ring

private theorem F_none (n : ℕ) : ∀ p : Fin 3, F none p n = (cnt n).1 := by
  induction n with
  | zero => intro p; simp [F, ok, cnt]
  | succ n ih =>
    intro p
    have key : ∀ c : Fin 3, (Finset.univ.filter fun x : Fin n → Fin 3 =>
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

private theorem a_succ (n : ℕ) : a (n + 1) = 3 * (cnt n).1 := by
  rw [a, card_cons]
  have h : ∀ c : Fin 3, (Finset.univ.filter fun x : Fin n → Fin 3 =>
      valid (c :: List.ofFn x) = true).card = (cnt n).1 :=
    fun c => F_none n c
  simp [h]

private theorem cnt_rec (n : ℕ) :
    (cnt (n + 3)).1 + 2 * (cnt (n + 1)).1 + 4 * (cnt n).1 = 4 * (cnt (n + 2)).1 := by
  simp only [cnt]
  ring

private theorem a_rec (n : ℕ) :
    a (n + 4) + 2 * a (n + 2) + 4 * a (n + 1) = 4 * a (n + 3) := by
  rw [a_succ, a_succ, a_succ, a_succ]
  have := cnt_rec n
  omega

private theorem a1 : a 1 = 3 := by rw [a_succ]; rfl
private theorem a2 : a 2 = 9 := by rw [a_succ]; rfl
private theorem a3 : a 3 = 27 := by rw [a_succ]; rfl

private theorem gf :
    (1 - 2 * X) * (1 - 2 * X - 2 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (3 * X * (1 - X - X ^ 2) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 2 * X) * (1 - 2 * X - 2 * X ^ 2) * s =
      s - (s * C (4 : ℤ)) * X ^ 1 + (s * C (2 : ℤ)) * X ^ 2 + (s * C (4 : ℤ)) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (3 * X * (1 - X - X ^ 2) : PowerSeries ℤ) =
      C (3 : ℤ) * X ^ 1 - C (3 : ℤ) * X ^ 2 - C (3 : ℤ) * X ^ 3 := by
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
  -3 * 2 ^ n + (3 - 2 * Real.sqrt 3) * (1 - Real.sqrt 3) ^ n +
    (1 + Real.sqrt 3) ^ n * (3 + 2 * Real.sqrt 3)

private theorem root_step (y : ℝ) (h : y ^ 2 = 2 * y + 2) (j : ℕ) :
    y ^ (j + 3) = 4 * y ^ (j + 2) - 2 * y ^ (j + 1) - 4 * y ^ j := by
  linear_combination (y ^ j * (y - 2)) * h

private theorem S_rec (j : ℕ) : S (j + 4) = 4 * S (j + 3) - 2 * S (j + 2) - 4 * S (j + 1) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h1 := root_step (1 - Real.sqrt 3) (by linear_combination hs) (j + 1)
  have h2 := root_step (1 + Real.sqrt 3) (by linear_combination hs) (j + 1)
  unfold S
  rw [show j + 4 = j + 1 + 3 by ring, show j + 3 = j + 1 + 2 by ring,
    show j + 2 = j + 1 + 1 by ring, h1, h2]
  ring

private theorem closed (m : ℕ) :
    (a (m + 1) : ℝ) * 4 = S (m + 1) ∧ (a (m + 2) : ℝ) * 4 = S (m + 2) ∧
    (a (m + 3) : ℝ) * 4 = S (m + 3) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [a1, S]; push_cast; linear_combination (-4) * hs
    · rw [a2, S]; push_cast; linear_combination (-14) * hs
    · rw [a3, S]; push_cast; linear_combination (-4 * Real.sqrt 3 ^ 2 - 42) * hs
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hr : ((a (m + 4) : ℕ) : ℝ) + 2 * (a (m + 2) : ℝ) + 4 * (a (m + 1) : ℝ) =
        4 * (a (m + 3) : ℝ) := by
      exact_mod_cast a_rec m
    rw [show m + 1 + 3 = m + 4 by ring, S_rec]
    rw [show m + 1 + 2 = m + 3 by ring] at h3
    rw [show m + 1 + 1 = m + 2 by ring] at h2
    linear_combination (4 : ℝ) * hr + 4 * h3 - 2 * h2 - 4 * h1

theorem OMA.solution : type_of% @OMA.S_oeis_a269613.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [eq_div_iff (by norm_num), (closed m).1, S]
