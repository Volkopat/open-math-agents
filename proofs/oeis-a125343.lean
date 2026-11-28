import OMAStatements.S_oeis_a125343

-- Problem: A125343: Number of base 6 circular n-digit numbers with adjacent digits differing by 4 or less.
-- Upstream: formal-conjectures statements/oeis-a125343.lean:0 (declaration OMA.S_oeis_a125343.main)
-- Credit: @lettucrisp (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


namespace OMA.A125343Proof
open OMA.S_oeis_a125343 Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Weight of a path `v 0 → v 1 → ⋯ → v m`. -/
def pathW (A : Matrix ι ι ℕ) (m : ℕ) (v : Fin (m + 1) → ι) : ℕ :=
  ∏ i : Fin m, A (v i.castSucc) (v i.succ)

lemma snoc_zero' (m : ℕ) (v : Fin (m + 1) → ι) (z : ι) :
    (Fin.snoc v z : Fin (m + 2) → ι) 0 = v 0 := by
  have := Fin.snoc_castSucc (α := fun _ => ι) (p := v) (x := z) 0
  simpa using this

lemma pathW_snoc (A : Matrix ι ι ℕ) (m : ℕ) (v : Fin (m + 1) → ι) (z : ι) :
    pathW A (m + 1) (Fin.snoc v z) = pathW A m v * A (v (Fin.last m)) z := by
  simp only [pathW, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last,
    Fin.succ_castSucc]

lemma pow_apply_eq (A : Matrix ι ι ℕ) (m : ℕ) (x y : ι) :
    (A ^ m) x y = ∑ v : Fin (m + 1) → ι,
      if v 0 = x ∧ v (Fin.last m) = y then pathW A m v else 0 := by
  induction m generalizing y with
  | zero =>
    rw [pow_zero, Matrix.one_apply, ← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    simp only [pathW, Finset.univ_eq_empty, Finset.prod_empty]
    by_cases h : x = y
    · subst h; simp [Fin.last]
    · rw [if_neg h]; symm; apply Finset.sum_eq_zero; intro z _
      simp only [Equiv.funUnique_symm_apply, Fin.last]
      split_ifs with hz
      · exact absurd (hz.1.symm.trans hz.2) h
      · rfl
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih]
    calc _ = ∑ v : Fin (m + 1) → ι,
          if v 0 = x then pathW A m v * A (v (Fin.last m)) y else 0 := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro v _
          by_cases hx : v 0 = x
          · simp [hx, ite_mul]
          · simp [hx]
      _ = _ := by
          symm
          rw [← (Fin.snocEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro v _
          simp only [Fin.snocEquiv, Equiv.coe_fn_mk, snoc_zero', Fin.snoc_last, pathW_snoc]
          by_cases hx : v 0 = x
          · simp [hx]
          · simp [hx]

/-- The adjacency matrix of the digit relation. -/
def A : Matrix (Fin 6) (Fin 6) ℕ := Matrix.of fun x y => if adjOk x y then 1 else 0

lemma trace_pow (m : ℕ) : (A ^ (m + 1)).trace =
    ∑ v : Fin (m + 1) → Fin 6, pathW A m v * A (v (Fin.last m)) (v 0) := by
  simp only [Matrix.trace, Matrix.diag, pow_apply_eq]
  rw [Finset.sum_comm]
  calc _ = ∑ u : Fin (m + 2) → Fin 6,
        if u (Fin.last (m + 1)) = u 0 then pathW A (m + 1) u else 0 := by
        apply Finset.sum_congr rfl; intro u _
        by_cases h : u (Fin.last (m + 1)) = u 0
        · rw [if_pos h]; simp [h]
        · rw [if_neg h]; apply Finset.sum_eq_zero; intro x _
          split_ifs with hx
          · exact absurd (hx.2.trans hx.1.symm) h
          · rfl
    _ = _ := by
        rw [← (Fin.snocEquiv (fun _ => Fin 6)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
        apply Finset.sum_congr rfl; intro v _
        simp only [Fin.snocEquiv, Equiv.coe_fn_mk, snoc_zero', Fin.snoc_last, pathW_snoc]
        rw [Finset.sum_ite_eq']; simp

lemma count_eq (m : ℕ) : a (m + 1) = (A ^ (m + 1)).trace := by
  rw [trace_pow, a, Finset.card_filter]
  apply Finset.sum_congr rfl; intro v _
  have key : pathW A m v * A (v (Fin.last m)) (v 0) =
      ∏ i : Fin (m + 1), (if adjOk (v i) (v ⟨(i.val + 1) % (m + 1), Nat.mod_lt _ (by omega)⟩)
        then 1 else 0) := by
    rw [Fin.prod_univ_castSucc, pathW]
    congr 1
    · apply Finset.prod_congr rfl; intro j _
      have : (⟨((Fin.castSucc j).val + 1) % (m + 1), Nat.mod_lt _ (by omega)⟩ : Fin (m + 1)) =
          j.succ := by
        ext; simp [Nat.mod_eq_of_lt (show j.val + 1 < m + 1 by omega)]
      rw [this]; rfl
    · have : (⟨((Fin.last m).val + 1) % (m + 1), Nat.mod_lt _ (by omega)⟩ : Fin (m + 1)) = 0 := by
        ext; simp
      rw [this]; rfl
  rw [key, Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies]
  rfl

lemma A_rel : A ^ 4 + A ^ 2 + 4 • A = 6 • A ^ 3 := by decide

lemma tr1 : (A ^ 1).trace = 6 := by decide
lemma tr2 : (A ^ 2).trace = 34 := by decide
lemma tr3 : (A ^ 3).trace = 186 := by decide

lemma trace_rec (k : ℕ) : (A ^ (k + 4)).trace + (A ^ (k + 2)).trace + 4 * (A ^ (k + 1)).trace =
    6 * (A ^ (k + 3)).trace := by
  have h := congrArg (fun M => (A ^ k * M).trace) A_rel
  simp only [mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
    ← pow_add] at h
  rw [← pow_succ] at h
  exact h

lemma a0 : a 0 = 1 := by decide

lemma a_rec (k : ℕ) : a (k + 4) + a (k + 2) + 4 * a (k + 1) = 6 * a (k + 3) := by
  rw [count_eq, count_eq, count_eq, count_eq]
  exact trace_rec k

lemma a1 : a 1 = 6 := by rw [count_eq 0]; exact tr1
lemma a2 : a 2 = 34 := by rw [count_eq 1]; exact tr2
lemma a3 : a 3 = 186 := by rw [count_eq 2]; exact tr3

noncomputable def lm : ℝ := (5 - Real.sqrt 41) / 2
noncomputable def lp : ℝ := (5 + Real.sqrt 41) / 2
noncomputable def b (n : ℕ) : ℝ := 1 + lm ^ n + lp ^ n

lemma s41 : Real.sqrt 41 ^ 2 = 41 := Real.sq_sqrt (by norm_num)

lemma root_lm : lm ^ 2 = 5 * lm + 4 := by
  unfold lm; nlinarith [s41]
lemma root_lp : lp ^ 2 = 5 * lp + 4 := by
  unfold lp; nlinarith [s41]

lemma b_rec (n : ℕ) : b (n + 3) = 6 * b (n + 2) - b (n + 1) - 4 * b n := by
  unfold b
  have hm : lm ^ (n + 3) = 6 * lm ^ (n + 2) - lm ^ (n + 1) - 4 * lm ^ n := by
    linear_combination (lm ^ n * (lm - 1)) * root_lm
  have hp : lp ^ (n + 3) = 6 * lp ^ (n + 2) - lp ^ (n + 1) - 4 * lp ^ n := by
    linear_combination (lp ^ n * (lp - 1)) * root_lp
  rw [hm, hp]; ring

lemma b1 : b 1 = 6 := by unfold b lm lp; ring
lemma b2 : b 2 = 34 := by
  unfold b; rw [root_lm, root_lp]; unfold lm lp; ring
lemma b3 : b 3 = 186 := by
  have := b_rec 0
  rw [b1, b2] at this
  have h0 : b 0 = 3 := by unfold b; norm_num
  rw [h0] at this; linarith

lemma closed (k : ℕ) : (a (k + 1) : ℝ) = b (k + 1) ∧ (a (k + 2) : ℝ) = b (k + 2) ∧
    (a (k + 3) : ℝ) = b (k + 3) := by
  induction k with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> simp [a1, a2, a3, b1, b2, b3]
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have r := a_rec k
    have r' : (a (k + 4) : ℝ) = 6 * a (k + 3) - a (k + 2) - 4 * a (k + 1) := by
      have : ((a (k + 4) + a (k + 2) + 4 * a (k + 1) : ℕ) : ℝ) = ((6 * a (k + 3) : ℕ) : ℝ) := by
        rw [r]
      push_cast at this; linarith
    have br := b_rec (k + 1)
    rw [show k + 1 + 3 = k + 4 by ring, show k + 1 + 2 = k + 3 by ring,
      show k + 1 + 1 = k + 2 by ring] at br
    rw [show k + 1 + 3 = k + 4 by ring, r', h1, h2, h3, br]

end OMA.A125343Proof

open OMA.A125343Proof PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a125343.main := by
  refine ⟨?_, ?_, ?_⟩
  · ext n
    have e1 : ((1 - X) * (1 - 5 * X - 4 * X ^ 2) : PowerSeries ℚ) =
        1 - C 6 * X ^ 1 + X ^ 2 + C 4 * X ^ 3 := by
      have h6 : (6 : PowerSeries ℚ) = C 6 := (map_ofNat C 6).symm
      have h4 : (4 : PowerSeries ℚ) = C 4 := (map_ofNat C 4).symm
      rw [← h6, ← h4]; ring
    have e2 : (1 - X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ) = 1 - X ^ 2 - C 8 * X ^ 3 := by
      have h8 : (8 : PowerSeries ℚ) = C 8 := (map_ofNat C 8).symm
      rw [← h8]
    rw [e1, e2]
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (C _), coeff_C_mul,
      mul_comm (PowerSeries.mk _) (X ^ _), PowerSeries.coeff_X_pow_mul', coeff_mk, coeff_one,
      coeff_X_pow, coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> simp [a0, a1, a2, a3] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have r := a_rec k
      have r' : ((OMA.S_oeis_a125343.a (k + 4) + OMA.S_oeis_a125343.a (k + 2) + 4 * OMA.S_oeis_a125343.a (k + 1) : ℕ) : ℚ) = ((6 * OMA.S_oeis_a125343.a (k + 3) : ℕ) : ℚ) := by
        rw [r]
      push_cast at r'
      simp only [show ¬ (k + 4 = 0) by omega, show ¬ (k + 4 = 2) by omega,
        show ¬ (k + 4 = 3) by omega, if_false, if_true, show 1 ≤ k + 4 by omega,
        show 2 ≤ k + 4 by omega, show 3 ≤ k + 4 by omega,
        show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
        show k + 4 - 3 = k + 1 by omega]
      linarith
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [(closed k).1]; rfl
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have r := a_rec k
    simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
      show k + 4 - 3 = k + 1 by omega]
    omega
