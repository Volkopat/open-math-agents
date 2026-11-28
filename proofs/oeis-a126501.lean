import OMAStatements.S_oeis_a126501
import Mathlib

open OMA.S_oeis_a126501


namespace P126501

theorem a_sum (n : ℕ) : a n = ∑ f : Fin n → Fin 6, if good f then 1 else 0 := by
  rw [a, Finset.card_filter]

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Fin 6) → ℕ) :
    ∑ f, F f = ∑ x : Fin 6, ∑ g : Fin n → Fin 6, F (Fin.cons x g) := by
  rw [← (Fin.consEquiv (fun _ => Fin 6)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem ofFn_cons {n : ℕ} (x : Fin 6) (g : Fin n → Fin 6) :
    List.ofFn (Fin.cons x g : Fin (n + 1) → Fin 6) = x :: List.ofFn g := by
  simp [List.ofFn_succ]

theorem good_cons_cons {n : ℕ} (x y : Fin 6) (h : Fin n → Fin 6) :
    good (Fin.cons x (Fin.cons y h : Fin (n + 1) → Fin 6) : Fin (n + 2) → Fin 6) ↔
      near x y ∧ good (Fin.cons y h : Fin (n + 1) → Fin 6) := by
  unfold good
  rw [ofFn_cons, ofFn_cons]
  exact List.isChain_cons_cons

/-- Good tuples of length `n + 1` starting with `x`. -/
def G (n : ℕ) (x : Fin 6) : ℕ := ∑ g : Fin n → Fin 6, if good (Fin.cons x g : Fin (n + 1) → Fin 6) then 1 else 0

theorem a_succ (n : ℕ) : a (n + 1) = ∑ x, G n x := by
  rw [a_sum, sum_cons]; rfl

theorem G_succ (n : ℕ) (x : Fin 6) : G (n + 1) x = ∑ y, if near x y then G n y else 0 := by
  rw [G, sum_cons]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [good_cons_cons]
  split_ifs with hxy
  · simp [hxy, G]
  · simp [hxy]

theorem a0 : a 0 = 1 := by
  rw [a_sum, Fintype.sum_unique]
  simp [good]

theorem G0 (x : Fin 6) : G 0 x = 1 := by
  rw [G, Fintype.sum_unique]
  simp [good]

theorem Gs (n : ℕ) :
    G (n + 1) 0 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 ∧
    G (n + 1) 1 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 + G n 5 ∧
    G (n + 1) 2 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 + G n 5 ∧
    G (n + 1) 3 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 + G n 5 ∧
    G (n + 1) 4 = G n 0 + G n 1 + G n 2 + G n 3 + G n 4 + G n 5 ∧
    G (n + 1) 5 = G n 1 + G n 2 + G n 3 + G n 4 + G n 5 := by
  simp only [G_succ, Fin.sum_univ_six]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [near]

theorem arec (n : ℕ) : a (n + 2) = 5 * a (n + 1) + 4 * a n := by
  rcases n with _ | n
  · have h1 : a 2 = ∑ x, G 1 x := a_succ 1
    have h0 : a 1 = ∑ x, G 0 x := a_succ 0
    have E := Gs 0
    simp only [Fin.sum_univ_six] at h1 h0
    simp only [zero_add] at E
    simp only [G0] at E h0
    show a 2 = 5 * a 1 + 4 * a 0
    rw [a0]
    omega
  · have h2 : a (n + 3) = ∑ x, G (n + 2) x := a_succ (n + 2)
    have h1 : a (n + 2) = ∑ x, G (n + 1) x := a_succ (n + 1)
    have h0 : a (n + 1) = ∑ x, G n x := a_succ n
    have E := Gs (n + 1)
    have F := Gs n
    simp only [show n + 1 + 1 = n + 2 from rfl] at E
    simp only [Fin.sum_univ_six] at h2 h1 h0
    show a (n + 3) = 5 * a (n + 2) + 4 * a (n + 1)
    omega

noncomputable def K (n : ℕ) : ℝ := (2 : ℝ) ^ (-1 - (n : ℤ))

theorem K_succ (n : ℕ) : K (n + 1) = K n / 2 := by
  rw [K, K, show -1 - ((n + 1 : ℕ) : ℤ) = (-1 - (n : ℤ)) + (-1) by push_cast; ring,
    zpow_add₀ (two_ne_zero), zpow_neg_one]
  ring

noncomputable def cl (n : ℕ) : ℝ :=
  K n * ((5 - Real.sqrt 41) ^ n * (-7 + Real.sqrt 41) + (5 + Real.sqrt 41) ^ n * (7 + Real.sqrt 41)) /
    Real.sqrt 41

theorem cl_rec (n : ℕ) : cl (n + 2) = 5 * cl (n + 1) + 4 * cl n := by
  have hs : Real.sqrt 41 ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 41 ≠ 0 := by positivity
  rw [cl, cl, cl, K_succ, K_succ]
  generalize hp : (5 - Real.sqrt 41) = p
  generalize hq : (5 + Real.sqrt 41) = q
  have hp2 : p ^ 2 = 10 * p + 16 := by rw [← hp]; linear_combination hs
  have hq2 : q ^ 2 = 10 * q + 16 := by rw [← hq]; linear_combination hs
  field_simp
  rw [pow_succ, pow_succ, pow_succ, pow_succ]
  linear_combination (K n * p ^ n * (-7 + Real.sqrt 41)) * hp2 + (K n * q ^ n * (7 + Real.sqrt 41)) * hq2

theorem cl0 : cl 0 = 1 := by
  have hs0 : Real.sqrt 41 ≠ 0 := by positivity
  rw [cl, K]
  norm_num
  field_simp
  ring

theorem cl1 : cl 1 = 6 := by
  have hs : Real.sqrt 41 ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 41 ≠ 0 := by positivity
  rw [cl, show (1 : ℕ) = 0 + 1 from rfl, K_succ, K]
  norm_num
  field_simp
  linear_combination 0 * hs

theorem eq_cl (n : ℕ) : (a n : ℝ) = cl n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      rw [a0, cl0]; norm_num
    | 1, _ =>
      have h0 := a_succ 0
      simp only [Fin.sum_univ_six, G0] at h0
      rw [h0, cl1]; norm_num
    | k + 2, ih =>
      rw [arec, cl_rec, ← ih k (by omega), ← ih (k + 1) (by omega)]
      push_cast; ring

end P126501

theorem OMA.solution : type_of% @OMA.S_oeis_a126501.main := by
  intro n
  rw [P126501.eq_cl, P126501.cl, P126501.K]
