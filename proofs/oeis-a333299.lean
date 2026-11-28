import OMAStatements.S_oeis_a333299
import Mathlib

namespace A333299Aux

open OMA.S_oeis_a333299 in
lemma run_none (l : List Move) : run l none = none := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    show run l (next none m) = none
    exact ih

open OMA.S_oeis_a333299 in
lemma ofFn_cons' (k : ℕ) (m : Move) (w : Fin k → Move) :
    List.ofFn (Fin.cons (α := fun _ => Move) m w) = m :: List.ofFn w := by
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

open OMA.S_oeis_a333299 in
open Classical in
noncomputable def F (k : ℕ) (s : State) : ℚ :=
  ∑ w : Fin k → Move, if run (List.ofFn w) s ≠ none then 1 else 0

open OMA.S_oeis_a333299 in
lemma sum_cons_split (k : ℕ) (g : (Fin (k + 1) → Move) → ℚ) :
    ∑ x, g x = ∑ m : Move, ∑ w : Fin k → Move, g (Fin.cons (α := fun _ => Move) m w) := by
  calc ∑ x, g x
      = ∑ p : Move × (Fin k → Move), g (Fin.consEquiv (fun _ : Fin (k + 1) => Move) p) :=
        (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 1) => Move)) g).symm
    _ = ∑ m : Move, ∑ w : Fin k → Move, g (Fin.cons (α := fun _ => Move) m w) :=
        Fintype.sum_prod_type _

open OMA.S_oeis_a333299 in
lemma F_succ (k : ℕ) (s : State) : F (k + 1) s = ∑ m : Move, F k (next s m) := by
  unfold F
  rw [sum_cons_split]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [ofFn_cons']
  rfl

open OMA.S_oeis_a333299 in
lemma F_none (k : ℕ) : F k none = 0 := by
  unfold F
  refine Finset.sum_eq_zero (fun w _ => ?_)
  exact if_neg (fun h => h (run_none _))

open OMA.S_oeis_a333299 in
lemma F_zero (t : Move) : F 0 (some t) = 1 := by
  unfold F
  rw [Fintype.sum_unique]
  exact if_pos (by rw [List.ofFn_zero]; exact Option.some_ne_none t)

open OMA.S_oeis_a333299 in
def cnt : ℕ → State → ℕ
  | 0, none => 0
  | 0, some _ => 1
  | _ + 1, none => 0
  | k + 1, some t => ∑ m : Move, cnt k (next (some t) m)

open OMA.S_oeis_a333299 in
lemma F_eq (k : ℕ) : ∀ s : State, F k s = (cnt k s : ℚ) := by
  induction k with
  | zero =>
    intro s
    cases s with
    | none =>
      rw [F_none]
      exact Nat.cast_zero.symm
    | some t =>
      rw [F_zero]
      exact Nat.cast_one.symm
  | succ k ih =>
    intro s
    cases s with
    | none =>
      rw [F_none]
      exact Nat.cast_zero.symm
    | some t =>
      rw [F_succ]
      show ∑ m : Move, F k (next (some t) m) = ((∑ m : Move, cnt k (next (some t) m) : ℕ) : ℚ)
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl (fun m _ => ih _)

open OMA.S_oeis_a333299 in
lemma vec_rec (h : ℕ) : ∀ s : State, cnt (h + 4) s
    = 8 * cnt (h + 3) s + 12 * cnt (h + 2) s + 8 * cnt (h + 1) s + 2 * cnt h s := by
  induction h with
  | zero => decide +kernel
  | succ h ih =>
    intro s
    cases s with
    | none => rfl
    | some t =>
      show (∑ m : Move, cnt (h + 4) (next (some t) m))
        = 8 * (∑ m : Move, cnt (h + 3) (next (some t) m))
          + 12 * (∑ m : Move, cnt (h + 2) (next (some t) m))
          + 8 * (∑ m : Move, cnt (h + 1) (next (some t) m))
          + 2 * (∑ m : Move, cnt h (next (some t) m))
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => ih _)

open OMA.S_oeis_a333299 in
lemma a_succ (k : ℕ) : a (k + 1) = ((∑ m : Move, cnt k (some m) : ℕ) : ℚ) := by
  unfold a
  rw [sum_cons_split, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← F_eq]
  unfold F
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [ofFn_cons']
  exact if_congr Iff.rfl rfl rfl

open OMA.S_oeis_a333299 in
lemma a_zero : a 0 = 1 := by
  unfold a
  rw [Fintype.sum_unique]
  exact if_pos (by rw [List.ofFn_zero]; exact True.intro)

open OMA.S_oeis_a333299 in
lemma tot_vals : (∑ m : Move, cnt 0 (some m)) = 12 ∧ (∑ m : Move, cnt 1 (some m)) = 114 ∧
    (∑ m : Move, cnt 2 (some m)) = 1068 ∧ (∑ m : Move, cnt 3 (some m)) = 10011 := by
  decide +kernel

open OMA.S_oeis_a333299 in
lemma a_vals : a 1 = 12 ∧ a 2 = 114 ∧ a 3 = 1068 ∧ a 4 = 10011 := by
  obtain ⟨t0, t1, t2, t3⟩ := tot_vals
  have h1 : a 1 = ((∑ m : Move, cnt 0 (some m) : ℕ) : ℚ) := a_succ 0
  have h2 : a 2 = ((∑ m : Move, cnt 1 (some m) : ℕ) : ℚ) := a_succ 1
  have h3 : a 3 = ((∑ m : Move, cnt 2 (some m) : ℕ) : ℚ) := a_succ 2
  have h4 : a 4 = ((∑ m : Move, cnt 3 (some m) : ℕ) : ℚ) := a_succ 3
  rw [t0] at h1
  rw [t1] at h2
  rw [t2] at h3
  rw [t3] at h4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]; norm_num
  · rw [h2]; norm_num
  · rw [h3]; norm_num
  · rw [h4]; norm_num

open OMA.S_oeis_a333299 in
lemma a_rec (h : ℕ) : a (h + 5) = 8 * a (h + 4) + 12 * a (h + 3) + 8 * a (h + 2) + 2 * a (h + 1) := by
  have e5 : a (h + 5) = ((∑ m : Move, cnt (h + 4) (some m) : ℕ) : ℚ) := a_succ (h + 4)
  have e4 : a (h + 4) = ((∑ m : Move, cnt (h + 3) (some m) : ℕ) : ℚ) := a_succ (h + 3)
  have e3 : a (h + 3) = ((∑ m : Move, cnt (h + 2) (some m) : ℕ) : ℚ) := a_succ (h + 2)
  have e2 : a (h + 2) = ((∑ m : Move, cnt (h + 1) (some m) : ℕ) : ℚ) := a_succ (h + 1)
  have e1 : a (h + 1) = ((∑ m : Move, cnt h (some m) : ℕ) : ℚ) := a_succ h
  have key : (∑ m : Move, cnt (h + 4) (some m))
      = 8 * (∑ m : Move, cnt (h + 3) (some m)) + 12 * (∑ m : Move, cnt (h + 2) (some m))
        + 8 * (∑ m : Move, cnt (h + 1) (some m)) + 2 * (∑ m : Move, cnt h (some m)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun m _ => vec_rec h (some m))
  rw [e5, e4, e3, e2, e1]
  exact_mod_cast key

end A333299Aux

open OMA.S_oeis_a333299 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a333299.main := by
  obtain ⟨v1, v2, v3, v4⟩ := A333299Aux.a_vals
  have v0 := A333299Aux.a_zero
  refine ⟨?_, ?_⟩
  · have key : PowerSeries.mk a * denominator = (1 + X) ^ 4 := by
      unfold denominator
      have hD : (1 - 8 * X - 12 * X ^ 2 - 8 * X ^ 3 - 2 * X ^ 4 : PowerSeries ℚ)
          = C 1 * X ^ 0 + C (-8) * X ^ 1 + C (-12) * X ^ 2 + C (-8) * X ^ 3 + C (-2) * X ^ 4 := by
        simp only [map_neg, map_ofNat, map_one]; ring
      have hN : ((1 + X) ^ 4 : PowerSeries ℚ)
          = C 1 * X ^ 0 + C 4 * X ^ 1 + C 6 * X ^ 2 + C 4 * X ^ 3 + C 1 * X ^ 4 := by
        simp only [map_ofNat, map_one]; ring
      rw [hD, hN]
      ext n
      simp only [mul_add, map_add, ← mul_assoc, PowerSeries.coeff_mul_X_pow',
        PowerSeries.coeff_mul_C, PowerSeries.coeff_mk, PowerSeries.coeff_C]
      rcases n with _ | _ | _ | _ | _ | n
      · norm_num [v0, v1, v2, v3, v4]
      · norm_num [v0, v1, v2, v3, v4]
      · norm_num [v0, v1, v2, v3, v4]
      · norm_num [v0, v1, v2, v3, v4]
      · norm_num [v0, v1, v2, v3, v4]
      · have h := A333299Aux.a_rec n
        simp
        linarith
    exact (PowerSeries.eq_mul_inv_iff_mul_eq (by norm_num [denominator])).mpr key
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have h := A333299Aux.a_rec m
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    exact h
