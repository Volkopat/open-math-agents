import OMAStatements.S_oeis_a233106

/-!
Count suffixes in three stages, according to whether the letters 1 and 2 have appeared.
Once both have appeared there are five continuations at every step. After the first 1,
three choices stay in that stage and the letter 2 advances to the final stage. Before
the first 1 the only possible letters are 0 and 1, respectively staying and advancing.
-/

open OMA.S_oeis_a233106 PowerSeries

private def count (n : ℕ) (q : List (Fin 6) → Bool) : ℚ :=
  ∑ x : Fin n → Fin 6, if q (List.ofFn x) then 1 else 0

private theorem count_succ (n : ℕ) (q : List (Fin 6) → Bool) :
    count (n + 1) q = ∑ c : Fin 6, count n (fun l => q (c :: l)) := by
  unfold count
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Fin 6)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_cons]

private theorem count_false (n : ℕ) : count n (fun _ => false) = 0 := by simp [count]

private theorem count_step (n : ℕ) (p : Fin 6) (s t : Bool) :
    count (n+1) (ok p s t) =
      ∑ c : Fin 6, if (c.val + p.val ≠ 5 ∧ (s = true ∨ ¬ (c.val = 2 ∨ c.val = 3 ∨ c.val = 4)) ∧
        (t = true ∨ c.val ≠ 3)) then
        count n (ok c (s || decide (c.val = 1)) (t || decide (c.val = 2))) else 0 := by
  rw [count_succ]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : c.val + p.val = 5 <;> cases s <;> cases t <;>
    simp [ok, h, Bool.and_assoc, count, apply_ite] <;> split_ifs <;> simp_all

private theorem counts (n : ℕ) :
    (∀ p : Fin 6, count n (ok p true true) = 5^n) ∧
    (∀ p : Fin 6, p ≠ 2 → p ≠ 3 → count n (ok p true false) = (5^n+3^n)/2) ∧
    count n (ok 0 false false) = (5^n+2*3^n+5)/8 := by
  induction n with
  | zero => norm_num [count, ok]
  | succ n ih =>
    rcases ih with ⟨both, one, neither⟩
    have one1 := one 1 (by decide) (by decide)
    refine ⟨?_, ?_, ?_⟩
    · intro p
      rw [count_step]
      fin_cases p <;> norm_num [Fin.sum_univ_succ, both, pow_succ] <;> ring
    · intro p h2 h3
      rw [count_step]
      fin_cases p <;> first
        | exact (h2 rfl).elim
        | exact (h3 rfl).elim
        | norm_num [Fin.sum_univ_succ, both, pow_succ]
          simp (disch := decide) only [one]
          ring
    · rw [count_step]
      norm_num [Fin.sum_univ_succ, neither, one1, pow_succ]
      ring

private theorem wordsClosed (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (75 + 10 * 3^n + 3 * 5^n)/120 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have ha : (a (j+1) : ℚ) = count (j+1) valid := by
    simp [a, count, Finset.sum_boole]
  rw [ha, count_succ]
  norm_num [Fin.sum_univ_succ, valid, count_false, (counts j).2.2, pow_succ]
  ring

private theorem enumeratorGF
    (h : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (75 + 10 * 3^n + 3 * 5^n) / 120) :
    type_of% @OMA.S_oeis_a233106.main := by
  refine ⟨?_, h⟩
  let D : ℚ⟦X⟧ := (1-X)*(1-3*X)*(1-5*X)
  have hd : constantCoeff D ≠ 0 := by simp [D]
  have hdgf : gf * D = X * (1-7*X+11*X^2) := by
    rw [show gf * D = gf - C 9 * (gf * X^1) + C 23 * (gf * X^2) - C 15 * (gf * X^3) by
          simp only [D, map_ofNat]; ring]
    rw [show (X : ℚ⟦X⟧) * (1-7*X+11*X^2) = X^1 - C 7 * X^2 + C 11 * X^3 by
          simp only [map_ofNat]; ring]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, gf, coeff_mk]
    by_cases hn : n ≤ 3
    · interval_cases n <;> norm_num [h]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
      simp (disch := omega) only [coeff_C, if_pos, if_neg, zero_mul, mul_zero, add_zero, sub_zero,
        show k+4-1 = k+3 by omega, show k+4-2 = k+2 by omega, show k+4-3 = k+1 by omega, h]
      simp only [pow_succ]
      ring
  change gf = _ * D⁻¹
  rw [← hdgf, mul_assoc, PowerSeries.mul_inv_cancel _ hd, mul_one]

theorem OMA.solution : type_of% @OMA.S_oeis_a233106.main := enumeratorGF wordsClosed
