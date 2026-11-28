import OMAStatements.S_oeis_a334513

/-!
# OEIS A334513: minimal eventual period of Rule 25 on a cyclic ring

For `n ≥ 10`, stage 6 is stage 4 shifted by one cell, giving eventual period `2n`; three ON cells
pin any even-step shift and five consecutive OFF cells rule out any odd-step match.
-/

namespace OMA.S_oeis_a334513

open PowerSeries Fin.NatCast

private def mask (n : ℕ) : ℕ → ℕ → Bool
  | 0, i => decide (i = 0)
  | 1, i => !decide (i = n - 1 ∨ i = 0)
  | 2, i => decide (i = n - 1 ∨ i = 1)
  | 3, i => !decide (i = n - 2 ∨ i = n - 1 ∨ i = 0 ∨ i = 1)
  | 4, i => decide (i = n - 2 ∨ i = n - 1 ∨ i = 0 ∨ i = 2)
  | 5, i => !decide (i = n - 3 ∨ i = n - 1 ∨ i = 0 ∨ i = 1 ∨ i = 2)
  | _, i => decide (i = n - 1 ∨ i = 0 ∨ i = 1 ∨ i = 3)

private lemma pred_mod {n : ℕ} (i : Fin n) :
    (i.1 + n - 1) % n = if i.1 = 0 then n - 1 else i.1 - 1 := by
  split_ifs with h
  · rw [h, zero_add, Nat.mod_eq_of_lt (by omega)]
  · rw [show i.1 + n - 1 = i.1 - 1 + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private lemma succ_mod {n : ℕ} (i : Fin n) :
    (i.1 + 1) % n = if i.1 + 1 = n then 0 else i.1 + 1 := by
  split_ifs with h
  · simp [h]
  · exact Nat.mod_eq_of_lt (by omega)

private lemma state_mask {n : ℕ} (hn : 10 ≤ n) (t : ℕ) : t ≤ 6 →
    state 25 n t = fun i => mask n t i.1 := by
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    funext i; rw [state, ih (by omega)]
    simp only [step, pred_mod, succ_mod]
    have hi := i.2; have : t < 6 := by omega
    rcases (by omega : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 ∨ i.1 = 3 ∨
        i.1 = n - 1 ∨ i.1 = n - 2 ∨ i.1 = n - 3 ∨ i.1 = n - 4 ∨ (4 ≤ i.1 ∧ i.1 + 4 < n)) with
      h | h | h | h | h | h | h | h | ⟨h, h'⟩ <;> interval_cases t <;>
      simp (disch := omega) only [mask, if_pos, if_neg, true_or, or_true,
        decide_eq_true, decide_eq_false] <;> decide

private lemma ep_min {n T P : ℕ} (hn : n ≠ 0) (hp : 0 < P)
    (hper : state 25 n (T + P) = state 25 n T)
    (hmin : ∀ r, 0 < r → r < P → state 25 n (T + r) ≠ state 25 n T) : a n = P := by
  have per : Function.Periodic (fun j => state 25 n (T + j)) P := fun j => by
    induction j with
    | zero => simpa using hper
    | succ j ih =>
      dsimp only
      rw [show T + (j + 1 + P) = (T + (j + P)) + 1 by omega, show T + (j + 1) = (T + j) + 1 by omega]
      exact congrArg (step 25 n) ih
  have mem : P ∈ {p | 0 < p ∧ EventualPeriod 25 n p} :=
    ⟨hp, T, fun t ht => by obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ht; simpa [add_assoc] using per j⟩
  rw [a, if_neg hn]
  refine le_antisymm (Nat.sInf_le mem) (le_csInf ⟨P, mem⟩ fun r ⟨hr, U, hU⟩ => ?_)
  by_contra! hlt
  refine hmin r hr hlt ?_
  calc state 25 n (T + r)
      = state 25 n (T + (r + U * P)) := (per.nat_mul U r).symm
    _ = state 25 n (T + U * P + r) := by congr 1; omega
    _ = state 25 n (T + U * P) := hU _ (by nlinarith)
    _ = state 25 n T := by simpa using per.nat_mul U 0

private lemma ep_tab {n P : ℕ} (hn : n ≠ 0) (hp : 0 < P) (T : ℕ) (tb : List ℕ)
    (h0 : ∀ i : Fin n, decide (i.1 = 0) = (tb.getD 0 0).testBit i.1)
    (hs : ∀ j : Fin (T + P), ∀ i : Fin n,
      step 25 n (fun k => (tb.getD j.1 0).testBit k.1) i = (tb.getD (j.1 + 1) 0).testBit i.1)
    (hc : tb.getD (T + P) 0 = tb.getD T 0)
    (hm : ∀ r : Fin P, 0 < r.1 → ∃ i : Fin n,
      (tb.getD (T + r.1) 0).testBit i.1 ≠ (tb.getD T 0).testBit i.1) : a n = P := by
  have tab (t : ℕ) (ht : t ≤ T + P) : state 25 n t = fun i => (tb.getD t 0).testBit i.1 := by
    induction t with
    | zero => exact funext h0
    | succ t ih => change step 25 n (state 25 n t) = _; rw [ih (by omega)]; exact funext (hs ⟨t, by omega⟩)
  refine ep_min hn hp (by rw [tab (T + P) le_rfl, tab T (by omega), hc]) fun r hr hlt h => ?_
  obtain ⟨i, hi⟩ := hm ⟨r, hlt⟩ hr
  exact hi (by simpa [tab (T + r) (by omega), tab T (by omega)] using congrFun h i)

private lemma step_shift {n : ℕ} [NeZero n] (hn : 10 ≤ n) (x : Fin n → Bool) (s i : Fin n) :
    step 25 n (fun j => x (j + s)) i = step 25 n x (i + s) := by
  have prv (j : Fin n) : (⟨(j.1 + n - 1) % n, Nat.mod_lt _ (Fin.pos j)⟩ : Fin n) = j - 1 := by
    ext; simp only [Fin.sub_def, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]; congr 1; omega
  have nxt (j : Fin n) : (⟨(j.1 + 1) % n, Nat.mod_lt _ (Fin.pos j)⟩ : Fin n) = j + 1 := by
    ext; simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
  unfold step
  rw [prv i, prv (i + s), nxt i, nxt (i + s)]
  dsimp only
  rw [show i - 1 + s = i + s - 1 by abel, show i + 1 + s = i + s + 1 by abel]

private lemma tail_law (n : ℕ) (hn : 10 ≤ n) : a n = 2 * n := by
  let _ : NeZero n := ⟨by omega⟩
  have h4 := congrFun (state_mask hn 4 (by decide))
  have h5 := congrFun (state_mask hn 5 (by decide))
  have h6 := congrFun (state_mask hn 6 (by decide))
  have slide (t : ℕ) : ∀ i : Fin n, state 25 n (6 + t) i = state 25 n (4 + t) (i - 1) := by
    induction t with
    | zero =>
      intro i; rw [h6, h4]
      have : (i - 1).1 = if i.1 = 0 then n - 1 else i.1 - 1 := by
        rw [← pred_mod i, Fin.sub_def, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
        exact congrArg (· % n) (by omega)
      simp only [mask, decide_eq_decide, this]; split_ifs <;> omega
    | succ t ih =>
      intro i; change step 25 n (state 25 n (6 + t)) i = step 25 n (state 25 n (4 + t)) (i - 1)
      rw [funext ih]; simpa [sub_eq_add_neg] using step_shift hn (state 25 n (4 + t)) (-1) i
  have ev (k : ℕ) : ∀ i : Fin n, state 25 n (4 + 2 * k) i = state 25 n 4 (i - (k : Fin n)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      intro i; rw [show 4 + 2 * (k + 1) = 6 + 2 * k by omega, slide, ih, Nat.cast_succ]
      congr 1; abel
  have od (k : ℕ) (i : Fin n) : state 25 n (4 + (2 * k + 1)) i = state 25 n 5 (i - (k : Fin n)) := by
    change step 25 n (state 25 n (4 + 2 * k)) i = step 25 n (state 25 n 4) (i - (k : Fin n))
    rw [funext (ev k)]; simpa [sub_eq_add_neg] using step_shift hn (state 25 n 4) (-(k : Fin n)) i
  refine ep_min (T := 4) (by omega) (by omega) ?_ fun r hr hlt h => ?_
  · ext i; simpa [show (n : Fin n) = 0 by ext; simp] using ev n i
  · let k := r / 2
    let s : Fin n := -(k : Fin n)
    obtain ⟨sv, hsv⟩ : ∃ sv, s.1 = sv := ⟨s.1, rfl⟩
    have hs : sv < n := hsv ▸ s.2
    have am (c : ℕ) (hc : c < n) : (⟨c, hc⟩ + s).1 = if c + sv < n then c + sv else c + sv - n := by
      show (c + s.1) % n = _; rw [hsv]
      split_ifs with hlt'
      · exact Nat.mod_eq_of_lt hlt'
      · conv_lhs => rw [show c + sv = c + sv - n + n by omega]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rcases (by omega : r = 2 * k ∨ r = 2 * k + 1) with hr2 | hr2
    · rw [hr2] at h
      have e (c : ℕ) (hc : c < n) (ho : c = n - 2 ∨ c = n - 1 ∨ c = 0 ∨ c = 2) :
          let v := if c + sv < n then c + sv else c + sv - n
          v = n - 2 ∨ v = n - 1 ∨ v = 0 ∨ v = 2 := by
        have ec : state 25 n 4 (⟨c, hc⟩ + s) = state 25 n 4 ⟨c, hc⟩ := by
          simpa [s, sub_eq_add_neg] using (ev k ⟨c, hc⟩).symm.trans (congrFun h ⟨c, hc⟩)
        rwa [h4, h4, mask, mask, am, decide_eq_true ho, decide_eq_true_eq] at ec
      have e0 := e 0 (by omega) (by omega); have e2 := e 2 (by omega) (by omega)
      have en := e (n - 1) (by omega) (by omega)
      dsimp only at e0 e2 en
      have s0 : sv = 0 := by split_ifs at e0 e2 en <;> omega
      have : (k : Fin n) = 0 := neg_eq_zero.mp (Fin.ext (hsv.trans s0))
      have : k = 0 := by simpa [Fin.ext_iff, Fin.val_natCast, Nat.mod_eq_of_lt (by dsimp [k]; omega : k < n)] using this
      omega
    · rw [hr2] at h
      have e (c : ℕ) (hc : c < n) (ho : ¬(c = n - 2 ∨ c = n - 1 ∨ c = 0 ∨ c = 2)) :
          let v := if c + sv < n then c + sv else c + sv - n
          v = n - 3 ∨ v = n - 1 ∨ v = 0 ∨ v = 1 ∨ v = 2 := by
        have ec : state 25 n 5 (⟨c, hc⟩ + s) = state 25 n 4 ⟨c, hc⟩ := by
          simpa [s, sub_eq_add_neg] using (od k ⟨c, hc⟩).symm.trans (congrFun h ⟨c, hc⟩)
        rw [h5, h4, mask, mask, am, decide_eq_false ho, Bool.not_eq_false', decide_eq_true_eq] at ec
        exact ec
      have e3 := e 3 (by omega) (by omega); have e4 := e 4 (by omega) (by omega)
      have e5 := e 5 (by omega) (by omega); have e6 := e 6 (by omega) (by omega)
      have e7 := e 7 (by omega) (by omega)
      dsimp only at e3 e4 e5 e6 e7
      split_ifs at e3 e4 e5 e6 e7 <;> omega

private lemma sm (n : ℕ) (hn : n < 10) : a n = ([0, 2, 2, 3, 2, 15, 15, 21, 16, 9] : List ℕ).getD n 0 := by
  interval_cases n
  · rfl
  · exact ep_tab (by decide) (by decide) 0 [1, 0, 1] (by decide) (by decide) rfl (by decide)
  · exact ep_tab (by decide) (by decide) 1 [1, 0, 3, 0] (by decide) (by decide) rfl (by decide)
  · exact ep_tab (by decide) (by decide) 0 [1, 2, 4, 1] (by decide) (by decide) rfl (by decide)
  · exact ep_tab (by decide) (by decide) 3 [1, 6, 10, 0, 15, 0] (by decide) (by decide) rfl (by decide)
  · exact ep_tab (by decide) (by decide) 0 [1, 14, 18, 4, 25, 10, 16, 7, 9, 2, 28, 5, 8, 19, 20, 1] (by decide) (by decide) rfl (by decide)
  · exact ep_tab (by decide) (by decide) 0 [1, 30, 34, 12, 53, 16, 39, 40, 3, 29, 4, 57, 10, 48, 23, 1] (by decide) (by decide) rfl (by decide)
  · exact ep_tab (by decide) (by decide) 2 [1, 62, 66, 28, 101, 40, 67, 92, 5, 56, 75, 80, 7, 57, 10, 112, 23, 33, 14, 114, 20, 97, 46, 66] (by decide) (by decide) rfl (by decide)
  · exact ep_tab (by decide) (by decide) 4 [1, 126, 130, 60, 197, 88, 139, 176, 23, 97, 46, 194, 92, 133, 184, 11, 113, 22, 226, 44, 197] (by decide) (by decide) rfl (by decide)
  · exact ep_tab (by decide) (by decide) 4 [1, 254, 258, 124, 389, 184, 267, 368, 23, 225, 46, 450, 92, 389] (by decide) (by decide) rfl (by decide)

end OMA.S_oeis_a334513

open OMA.S_oeis_a334513 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a334513.main := by
  have rec_law (n : ℕ) (hn : 11 < n) : (a n : ℤ) = 2 * a (n - 1) - a (n - 2) := by
    rw [tail_law n (by omega), tail_law (n - 1) (by omega), tail_law (n - 2) (by omega)]; omega
  refine ⟨tail_law, rec_law, ?_⟩
  have gp (B : ℤ⟦X⟧) (n : ℕ) :
      coeff n (B * (1 - X) ^ 2) = coeff n B - 2 * coeff n (B * X ^ 1) + coeff n (B * X ^ 2) := by
    rw [show B * (1 - X) ^ 2 = B - C (2 : ℤ) * (B * X ^ 1) + B * X ^ 2 by simp only [map_ofNat]; ring]
    simp only [map_sub, map_add, coeff_C_mul]
  have gr (n : ℕ) :
      coeff n (X * (2 - 2 * X + X ^ 2 - 2 * X ^ 3 + 14 * X ^ 4 - 13 * X ^ 5 + 6 * X ^ 6 - 11 * X ^ 7 -
        2 * X ^ 8 + 18 * X ^ 9 - 9 * X ^ 10) : ℤ⟦X⟧) =
      coeff n (C (2 : ℤ) * X ^ 1 - C (2 : ℤ) * X ^ 2 + X ^ 3 - C (2 : ℤ) * X ^ 4 + C (14 : ℤ) * X ^ 5 -
        C (13 : ℤ) * X ^ 6 + C (6 : ℤ) * X ^ 7 - C (11 : ℤ) * X ^ 8 - C (2 : ℤ) * X ^ 9 +
        C (18 : ℤ) * X ^ 10 - C (9 : ℤ) * X ^ 11) := by
    congr 1; simp only [map_ofNat]; ring
  ext n; rw [gp, gr]
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_mk, coeff_X_pow, coeff_C]
  rcases Nat.lt_or_ge 11 n with big | small
  · simp (disch := omega) only [if_neg, if_pos]; linarith [rec_law n big]
  · have val (k : ℕ) : a k = if k < 10 then ([0, 2, 2, 3, 2, 15, 15, 21, 16, 9] : List ℕ).getD k 0 else 2 * k := by
      split_ifs with h <;> [exact sm _ h; exact tail_law _ (by omega)]
    interval_cases n <;> norm_num [val, List.getD]
