import OMAStatements.S_oeis_a204238

-- Problem: A204238: Determinant of the n-th principal submatrix of A204237.
-- Upstream: formal-conjectures statements/oeis-a204238.lean:0 (declaration OMA.S_oeis_a204238.main)
-- Credit: @a5teri5k (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Matrix PowerSeries

namespace OMA.A204238

open OMA.S_oeis_a204238

lemma entry {n : ℕ} (i j : Fin n) :
    principalMatrix n i j =
      if i.val ≤ j.val then 3 * (j.val : ℚ) - i.val + 2 else 3 * (i.val : ℚ) - j.val + 2 := by
  unfold principalMatrix
  split_ifs with h
  · have : (i.val : ℚ) ≤ j.val := by exact_mod_cast h
    rw [max_eq_right (by linarith)]; ring
  · have : (j.val : ℚ) ≤ i.val := by exact_mod_cast (by omega : j.val ≤ i.val)
    rw [max_eq_left (by linarith)]; ring

def G (m : ℕ) (u v : Fin (m + 2) → ℚ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ := fun i j =>
  if i.val = 0 then u j else if i.val = 1 then v j else if j.val + 1 = i.val then 4 else 0

lemma det_G (m : ℕ) : ∀ u v : Fin (m + 2) → ℚ,
    (G m u v).det = (-4) ^ m * (u 0 * v (Fin.last _) - u (Fin.last _) * v 0) := by
  induction m with
  | zero =>
    intro u v
    rw [Matrix.det_fin_two]
    simp [G]
  | succ m ih =>
    intro u v
    set p : Fin (m + 3) := ⟨m + 1, by omega⟩ with hp
    rw [Matrix.det_succ_row _ (Fin.last _), Finset.sum_eq_single p]
    · have hsub : (G (m + 1) u v).submatrix (Fin.last (m + 2)).succAbove p.succAbove =
          G m (fun k => u (p.succAbove k)) (fun k => v (p.succAbove k)) := by
        ext i k
        have hk : (p.succAbove k).val + 1 = i.val ↔ k.val + 1 = i.val := by
          have := i.isLt
          have := k.isLt
          unfold Fin.succAbove
          split_ifs with h
          · simp
          · simp only [Fin.lt_def, Fin.val_castSucc, hp] at h
            simp only [Fin.val_succ]
            omega
        simp only [Matrix.submatrix_apply, G, Fin.succAbove_last, Fin.val_castSucc, hk]
      rw [hsub, ih]
      have h0 : p.succAbove 0 = 0 := Fin.succAbove_ne_zero_zero (by simp [hp, Fin.ext_iff])
      have hl : p.succAbove (Fin.last (m + 1)) = Fin.last (m + 2) :=
        Fin.succAbove_ne_last_last (by simp [hp, Fin.ext_iff])
      have h4 : G (m + 1) u v (Fin.last (m + 2)) p = 4 := by
        simp [G, hp]
      have hs : ((-1 : ℚ) ^ ((Fin.last (m + 2) : ℕ) + (p : ℕ))) = -1 := by
        rw [hp]; simp only [Fin.val_last]; exact Odd.neg_one_pow ⟨m + 1, by ring⟩
      rw [h0, hl, h4, hs]
      ring
    · intro j _ hj
      have hj' : j.val ≠ m + 1 := fun h => hj (Fin.ext (by simp [hp, h]))
      simp [G, hj']
    · intro h; exact absurd (Finset.mem_univ p) h

def B1 (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ := fun i j =>
  if i.val = 0 then 3 * (j.val : ℚ) + 2 else if i.val ≤ j.val then -1 else 3

lemma det_principal (m : ℕ) : (principalMatrix (m + 1)).det = (B1 m).det := by
  apply Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1)
  · intro j
    simp [entry, B1]
  · intro i j
    simp only [entry, B1, Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> first | (exfalso; omega) | (push_cast; ring1) |
      (obtain hij : (j : ℕ) = (i : ℕ) := by omega
       rw [hij]; push_cast; ring)

lemma det_B1 (m : ℕ) :
    (B1 (m + 1)).det = (G m (fun j => 3 * (j.val : ℚ) + 2)
      (fun j => if j.val = 0 then 3 else -1)).det := by
  apply Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun i => if i.val = 0 then 0 else 1)
  · intro j
    simp [G, B1]
  · intro i j
    simp only [G, B1, Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> first | (exfalso; omega) | norm_num

lemma closed (n : ℕ) (hn : 1 ≤ n) : 16 * a n = (-4) ^ n * (1 - 9 * n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases m with _ | m
  · simp [a, entry]
    norm_num
  · unfold a
    rw [det_principal, det_B1, det_G]
    simp only [Fin.val_zero, Fin.val_last]
    push_cast
    simp
    ring

lemma rec (n : ℕ) (hn : 3 ≤ n) : a n = -8 * a (n - 1) - 16 * a (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have h3 := closed (k + 3) (by omega)
  have h2 := closed (k + 2) (by omega)
  have h1 := closed (k + 1) (by omega)
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
  push_cast at h1 h2 h3
  linear_combination (1 / 16 : ℚ) * h3 + (1 / 2 : ℚ) * h2 + h1

lemma gf : generatingFunction = -(X * (X - C 2)) * ((C 4 * X + 1) ^ 2)⁻¹ := by
  have hc : constantCoeff ((C 4 * X + 1 : PowerSeries ℚ) ^ 2) ≠ 0 := by simp
  rw [PowerSeries.eq_mul_inv_iff_mul_eq hc]
  have e1 : generatingFunction * (C 4 * X + 1 : PowerSeries ℚ) ^ 2 =
      C 16 * (X * (X * generatingFunction)) + C 8 * (X * generatingFunction) +
        generatingFunction := by
    simp only [map_ofNat]; ring
  have e2 : -(X * (X - C 2) : PowerSeries ℚ) = C 2 * X - X ^ 2 := by
    simp only [map_ofNat]; ring
  have a1 : a 1 = 2 := by have := closed 1 le_rfl; norm_num at this; linarith
  have a2 : a 2 = -17 := by have := closed 2 (by norm_num); norm_num at this; linarith
  rw [e1, e2]
  ext n
  rcases n with _ | _ | _ | k
  · simp [generatingFunction]
  · simp [generatingFunction, a1]
  · simp [generatingFunction, coeff_X_pow, a1, a2]
    norm_num
  · have hr := rec (k + 3) (by omega)
    simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega] at hr
    simp [generatingFunction, coeff_X_pow]
    linarith

end OMA.A204238

theorem OMA.solution : type_of% @OMA.S_oeis_a204238.main :=
  ⟨OMA.A204238.rec, OMA.A204238.gf⟩
