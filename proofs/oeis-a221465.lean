import OMAStatements.S_oeis_a221465
import Mathlib

namespace OMA.A221465Proof

open OMA.S_oeis_a221465

theorem pred_iff {α : Type} (x : Fin 6 → α) :
    (∀ i : Fin 6, ∃ j : Fin 6, (j.val + 1 = i.val ∨ i.val + 1 = j.val) ∧ x i ≠ x j) ↔
      (x 1 ≠ x 0 ∧ ¬ (x 1 = x 2 ∧ x 2 = x 3) ∧ ¬ (x 2 = x 3 ∧ x 3 = x 4) ∧ x 5 ≠ x 4) := by
  simp only [Fin.forall_fin_succ, Fin.exists_fin_succ, IsEmpty.forall_iff]
  simp
  constructor
  · rintro ⟨h0, -, h2, h3, -, h5⟩
    exact ⟨fun h => h0 h.symm, fun h h' => h2.elim (· h.symm) (· h'),
      fun h h' => h3.elim (· h.symm) (· h'), h5⟩
  · rintro ⟨h1, h2, h3, h5⟩
    refine ⟨fun h => h1 h.symm, Or.inl h1, ?_, ?_, Or.inr fun h' => h5 h'.symm, h5⟩
    · by_cases h : x 2 = x 1
      · exact Or.inr (h2 h.symm)
      · exact Or.inl h
    · by_cases h : x 3 = x 2
      · exact Or.inr (h3 h.symm)
      · exact Or.inl h

def e6 (α : Type) : (Fin 6 → α) ≃ α × α × α × α × α × α where
  toFun x := (x 0, x 1, x 2, x 3, x 4, x 5)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv p := rfl

theorem e6_symm {α : Type} (p : α × α × α × α × α × α) :
    (e6 α).symm p = ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2] := rfl

theorem card_last {n : ℕ} (P : Prop) [Decidable P] (d : Fin (n + 1)) :
    (Finset.univ.filter fun e : Fin (n + 1) => P ∧ ¬ e = d).card = if P then n else 0 := by
  by_cases hP : P
  · simp [hP, Finset.filter_ne']
  · simp [hP]

theorem sum_e {n : ℕ} (c d : Fin (n + 1)) :
    (∑ e : Fin (n + 1), if ¬ (c = d ∧ d = e) then n else 0) =
      if c = d then n * n else (n + 1) * n := by
  by_cases h : c = d
  · subst h
    simp [Finset.sum_ite, Finset.filter_ne]
  · simp [h]

theorem sum_d {n : ℕ} (b c : Fin (n + 1)) :
    (∑ d : Fin (n + 1), if ¬ (b = c ∧ c = d) then (if c = d then n * n else (n + 1) * n) else 0) =
      if b = c then n * ((n + 1) * n) else n * n + n * ((n + 1) * n) := by
  by_cases h : b = c
  · subst h
    simp [Finset.sum_ite, Finset.filter_ne]
    exact Or.inl fun x hx h => hx h.symm
  · simp [h]
    rw [Finset.sum_ite]
    simp [Finset.filter_eq, Finset.filter_ne]

theorem sum_c {n : ℕ} (b : Fin (n + 1)) :
    (∑ c : Fin (n + 1), if b = c then n * ((n + 1) * n) else n * n + n * ((n + 1) * n)) =
      n * ((n + 1) * n) + n * (n * n + n * ((n + 1) * n)) := by
  rw [Finset.sum_ite]
  simp [Finset.filter_eq, Finset.filter_ne]

theorem sum_outer {n : ℕ} (K : ℕ) :
    (∑ b : Fin (n + 1), if b ≠ 0 then K else 0) = n * K := by
  rw [Finset.sum_ite]
  simp [Finset.filter_ne']

theorem a_eq (n : ℕ) : a n = n ^ 5 + 3 * n ^ 4 + n ^ 3 := by
  unfold a
  rw [Finset.card_filter, ← (e6 (Fin (n + 1))).symm.sum_comp]
  simp only [pred_iff, e6_symm, Fintype.sum_prod_type]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ← and_assoc, Finset.sum_boole, Nat.cast_id]
  simp only [card_last]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [sum_e, sum_d, sum_c, sum_outer]
  ring

theorem coeff_a (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.mk (fun n => (a n : ℤ))) =
      (k : ℤ) ^ 5 + 3 * (k : ℤ) ^ 4 + (k : ℤ) ^ 3 := by
  simp [a_eq]

theorem gf : (1 - PowerSeries.X) ^ 6 * PowerSeries.mk (fun n => (a n : ℤ)) =
      PowerSeries.X * (5 + 58 * PowerSeries.X + 60 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3
        - PowerSeries.X ^ 4) := by
  have h : (1 - PowerSeries.X : PowerSeries ℤ) ^ 6 =
      1 - PowerSeries.C 6 * PowerSeries.X ^ 1 + PowerSeries.C 15 * PowerSeries.X ^ 2
        - PowerSeries.C 20 * PowerSeries.X ^ 3 + PowerSeries.C 15 * PowerSeries.X ^ 4
        - PowerSeries.C 6 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 := by
    simp only [map_ofNat]
    ring
  have h2 : (PowerSeries.X * (5 + 58 * PowerSeries.X + 60 * PowerSeries.X ^ 2
      - 2 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4) : PowerSeries ℤ) =
      PowerSeries.C 5 * PowerSeries.X ^ 1 + PowerSeries.C 58 * PowerSeries.X ^ 2
        + PowerSeries.C 60 * PowerSeries.X ^ 3 - PowerSeries.C 2 * PowerSeries.X ^ 4
        - PowerSeries.X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [h, h2]
  ext k
  simp only [sub_mul, add_mul, mul_assoc, one_mul, map_sub, map_add,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow, coeff_a]
  rcases k with _ | _ | _ | _ | _ | _ | k
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · have h1 : ¬ (k + 1 + 1 + 1 + 1 + 1 + 1 = 1) := by omega
    have h2 : ¬ (k + 1 + 1 + 1 + 1 + 1 + 1 = 2) := by omega
    have h3 : ¬ (k + 1 + 1 + 1 + 1 + 1 + 1 = 3) := by omega
    have h4 : ¬ (k + 1 + 1 + 1 + 1 + 1 + 1 = 4) := by omega
    have h5 : ¬ (k + 1 + 1 + 1 + 1 + 1 + 1 = 5) := by omega
    simp only [h1, h2, h3, h4, h5, if_false, show 1 ≤ k + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      show 2 ≤ k + 1 + 1 + 1 + 1 + 1 + 1 by omega, show 3 ≤ k + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      show 4 ≤ k + 1 + 1 + 1 + 1 + 1 + 1 by omega, show 5 ≤ k + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      show 6 ≤ k + 1 + 1 + 1 + 1 + 1 + 1 by omega, if_true]
    push_cast
    ring

theorem recur (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4)
        + 6 * a (n - 5) - a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  simp only [a_eq, show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
    show m + 6 - 5 = m + 1 by omega, show m + 6 - 6 = m by omega]
  push_cast
  ring

end OMA.A221465Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a221465.main :=
  ⟨OMA.A221465Proof.recur, OMA.A221465Proof.gf⟩
