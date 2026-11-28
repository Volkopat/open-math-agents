import OMAStatements.S_oeis_a201347
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

-- Credit for the original proof: @jleguina.

namespace OMA.S_oeis_a201347

open PowerSeries

private abbrev Row := Fin 2 × Fin 2

private def step (r : Row) (t s0 s1 : Bool) (w : Row) : Bool :=
  decide (r.1 < w.1 ∨ (r.1 = w.1 ∧ r.2 ≤ w.2)) && (t || decide (w.1 ≤ w.2)) &&
    (s0 || decide (w.1 = r.1)) && (s1 || decide (w.2 = r.2))

private def N (r : Row) (t s0 s1 : Bool) (m : ℕ) : ℕ :=
  ∑ y : Fin m → Row, if ok r t s0 s1 (List.ofFn y) = true then 1 else 0

private lemma sum_cons (m : ℕ) (f : List Row → ℕ) :
    ∑ x : Fin (m + 1) → Row, f (List.ofFn x) =
      ∑ c : Row, ∑ y : Fin m → Row, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Row).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ]

private lemma N_succ (r : Row) (t s0 s1 : Bool) (m : ℕ) :
    N r t s0 s1 (m + 1) = ∑ w : Row, if step r t s0 s1 w = true then
      N w (t || decide (w.1 < w.2)) (decide (w.1 = w.2) || decide (w.1 = r.1))
        (decide (w.2 = w.1) || decide (w.2 = r.2)) m else 0 := by
  unfold N
  rw [sum_cons m (fun l => if ok r t s0 s1 l = true then 1 else 0)]
  apply Finset.sum_congr rfl
  intro w _
  change (∑ y : Fin m → Row, if (step r t s0 s1 w && ok w _ _ _ (List.ofFn y)) = true
    then 1 else 0) = _
  by_cases h : step r t s0 s1 w = true
  · simp [h]
  · simp [Bool.eq_false_iff.mpr h]

/-- Suffix counts along the four successive blocks. Only the states reached by
a valid first row are needed. -/
private lemma counts (m : ℕ) :
    (∀ t, N (1,1) t true true m = 1) ∧
    N (1,0) true true true m = m + 1 ∧
    N (1,0) true false false m = m ∧
    N (0,1) true true true m = 1 + (m+1).choose 2 ∧
    N (0,1) true false false m = (if m = 0 then 0 else 1 + m.choose 2) ∧
    N (0,1) true true false m = (if m = 0 then 0 else 2 + m.choose 2) ∧
    N (0,0) false true true m = (if m = 0 then 1 else m.choose 3 + 3*m - 1) := by
  induction m with
  | zero => simp [N, ok]
  | succ m ih =>
    obtain ⟨h11,h10,h10new,h01,_,h01left,h00⟩ := ih
    refine ⟨fun t => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [N_succ, step, Fintype.sum_prod_type, Fin.sum_univ_two, h11, h10, h10new,
      h01, h01left, h00, Nat.choose_succ_succ, Nat.choose_one_right]
    all_goals try omega
    split_ifs <;> simp_all <;> omega

private lemma a_succ (m : ℕ) :
    a (m+1) = N (0,0) false true true m + N (0,1) true false false m + N (1,1) false true true m := by
  unfold a
  rw [Finset.card_filter, sum_cons m (fun l => if valid l = true then 1 else 0)]
  simp [valid, Fintype.sum_prod_type, Fin.sum_univ_two, N, add_assoc]

private lemma a_one : a 1 = 2 := by
  rw [a_succ]
  obtain ⟨h1,_,_,_,h5,_,h7⟩ := counts 0
  simp [h1,h5,h7]

private lemma a_two (n : ℕ) : a (n+2) = (n+2).choose 3 + 3*n + 4 := by
  rw [show n+2 = (n+1)+1 by omega, a_succ]
  obtain ⟨h1,_,_,_,h5,_,h7⟩ := counts (n+1)
  simp only [h1,h5,h7, Nat.add_one_ne_zero, if_false, Nat.choose_succ_succ']
  omega


private noncomputable def binomial (d : ℕ) : ℚ⟦X⟧ :=
  mk fun n => ((d+n).choose d : ℚ)

private lemma gf_mul :
    gf * (1 - X) ^ 4 = X * (2 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 + X ^ 4) := by
  have hseries : gf = X + X^1 * binomial 0 + C 3 * (X^2 * binomial 1) + X^3 * binomial 3 := by
    ext n
    simp only [gf, coeff_mk, map_add, coeff_X, coeff_X_pow_mul', coeff_C_mul,
      binomial, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, zero_add]
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num [a_one, a_two 0]
    · have hf := a_two (n-2)
      rw [Nat.sub_add_cancel (by omega : 2 ≤ n)] at hf
      simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show 1 ≤ n by omega,
        show 2 ≤ n by omega, h, hf, show 3 + (n-3) = n by omega,
        Nat.cast_sub (show 2 ≤ n by omega)]
      ring
  have hb (d : ℕ) : binomial d * (1-X)^(d+1) = 1 :=
    mk_add_choose_mul_one_sub_pow_eq_one ℚ d
  rw [hseries]
  calc
    _ = X*(1-X)^4 + X*(binomial 0 * (1-X)^(0+1))*(1-X)^3 +
        C 3*X^2*(binomial 1 * (1-X)^(1+1))*(1-X)^2 +
        X^3*(binomial 3 * (1-X)^(3+1)) := by ring
    _ = _ := by rw [hb 0, hb 1, hb 3]; simp only [map_ofNat]; ring

private lemma recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m+6 := ⟨n-6, by omega⟩
  have hc (m : ℕ) : (a (m+2) : ℤ) = ((m+2).choose 3 : ℤ) + 3*m + 4 := by
    exact_mod_cast a_two m
  change (a ((m+1+1+1+1)+2) : ℤ) = 4*a ((m+1+1+1)+2) - 6*a ((m+1+1)+2) +
    4*a ((m+1)+2) - a (m+2)
  simp only [hc]
  have p3 (j : ℕ) :
      ((j+1).choose 3 : ℤ) = (j.choose 2 : ℤ) + j.choose 3 := by
    exact_mod_cast Nat.choose_succ_succ' j 2
  have p2 (j : ℕ) :
      ((j+1).choose 2 : ℤ) = j + (j.choose 2 : ℤ) := by
    exact_mod_cast (Nat.choose_succ_succ' j 1).trans (by rw [Nat.choose_one_right])
  change (((m+2+1+1+1+1).choose 3 : ℕ) : ℤ) + _ + _ = _
  simp only [p3, p2, Nat.cast_add, Nat.cast_one]
  ring

/-- The entry's first nineteen terms. -/
example : a 1 = 2 ∧ a 2 = 4 ∧ a 3 = 8 ∧ a 4 = 14 ∧ a 5 = 23 ∧ a 6 = 36 ∧ a 7 = 54 ∧ a 8 = 78 ∧
    a 9 = 109 ∧ a 10 = 148 ∧ a 11 = 196 ∧ a 12 = 254 ∧ a 13 = 323 ∧ a 14 = 404 ∧ a 15 = 498 ∧
    a 16 = 606 ∧ a 17 = 729 ∧ a 18 = 868 ∧ a 19 = 1024 := by
  refine ⟨a_one, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact (a_two _).trans (by decide)

set_option maxRecDepth 20000 in
/-- Direct enumeration of the 256 arrays with four rows. -/
example : a 4 = 14 := by decide

end OMA.S_oeis_a201347

open OMA.S_oeis_a201347 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a201347.main := by
  refine ⟨?_, recurrence⟩
  have h : constantCoeff ((1 - X)^4 : ℚ⟦X⟧) ≠ 0 := by simp
  calc
    gf = gf * ((1 - X)^4 * ((1 - X)^4)⁻¹) := by rw [PowerSeries.mul_inv_cancel _ h, mul_one]
    _ = _ := by rw [← mul_assoc, gf_mul]
