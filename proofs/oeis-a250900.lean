import OMAStatements.S_oeis_a250900
import Mathlib

namespace OMA.S_oeis_a250900

open Matrix

abbrev V := Fin 3 → Fin 3

instance (p q r s : ℕ) : Decidable (Blk p q r s) := by unfold Blk; infer_instance

def R (x y : V) : Prop := ∀ j : Fin 2,
  Blk (x j.castSucc) (y j.castSucc) (x j.succ) (y j.succ)

instance : DecidableRel R := fun x y => by unfold R; infer_instance

def M : Matrix V V ℤ := fun v w => if R v w then 1 else 0

abbrev Wk (m : ℕ) := {x : Fin (m + 1) → V // ∀ i : Fin m, R (x i.castSucc) (x i.succ)}

noncomputable def S (m : ℕ) (v : V) : ℕ := Nat.card {y : Wk m // y.1 0 = v}

theorem S_succ (m : ℕ) (v : V) :
    S (m + 1) v = ∑ w, if R v w then S m w else 0 := by
  unfold S
  have e : {y : Wk (m + 1) // y.1 0 = v} ≃ {p : Wk m // R v (p.1 0)} :=
    { toFun := fun z => ⟨⟨fun j => z.1.1 j.succ, fun i => z.1.2 i.succ⟩, by
        have h : R (z.1.1 0) (z.1.1 1) := z.1.2 0
        rw [z.2] at h
        exact h⟩
      invFun := fun p => ⟨⟨Fin.cons v p.1.1, by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using p.2
        · simpa using p.1.2 j⟩, rfl⟩
      left_inv := fun z => by
        apply Subtype.ext; apply Subtype.ext
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [z.2]
        · simp
      right_inv := fun p => by
        apply Subtype.ext; apply Subtype.ext
        funext i
        simp }
  rw [Nat.card_congr e]
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (fun p : {p : Wk m // R v (p.1 0)} => p.1.1 0))]
  rw [Nat.card_sigma]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases h : R v w
  · rw [if_pos h]
    exact Nat.card_congr ⟨fun p => ⟨p.1.1, p.2⟩, fun y => ⟨⟨y.1, by rw [y.2]; exact h⟩, y.2⟩,
      fun p => rfl, fun p => rfl⟩
  · rw [if_neg h]
    have : IsEmpty {p : {p : Wk m // R v (p.1 0)} // p.1.1 0 = w} :=
      ⟨fun p => h (p.2 ▸ p.1.2)⟩
    exact Nat.card_of_isEmpty

theorem S_zero (v : V) : S 0 v = 1 := by
  unfold S
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨⟨⟨fun _ => v, fun i => i.elim0⟩, rfl⟩⟩⟩
  apply Subtype.ext; apply Subtype.ext
  funext i
  have : i = 0 := Fin.fin_one_eq_zero i
  subst this
  rw [a.2, b.2]

def u (k : ℕ) : V → ℤ := (M ^ k).mulVec (fun _ => 1)

theorem S_eq (m : ℕ) (v : V) : (S m v : ℤ) = u m v := by
  induction m generalizing v with
  | zero => simp [S_zero, u]
  | succ m ih =>
    rw [S_succ]
    unfold u at *
    rw [pow_succ', ← mulVec_mulVec]
    change _ = ∑ w, M v w * (M ^ m *ᵥ fun _ => (1:ℤ)) w
    push_cast
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have hM : M v w = if R v w then 1 else 0 := rfl
    rw [hM]
    split_ifs
    · simp [ih]
    · simp

theorem a_eq (n : ℕ) : (a n : ℤ) = ∑ v, u n v := by
  have e1 : a n = Nat.card (Wk n) := by
    unfold a
    exact Nat.card_congr ((Equiv.piComm _).subtypeEquiv (fun x => ⟨fun h j i => h i j, fun h i j => h j i⟩))
  have e2 : Nat.card (Wk n) = ∑ v, S n v := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (fun y : Wk n => y.1 0))]
    rw [Nat.card_sigma]
    rfl
  rw [e1, e2]
  push_cast
  exact Finset.sum_congr rfl (fun v _ => S_eq n v)

theorem key : u 7 = (10:ℤ) • u 6 - (40:ℤ) • u 5 + (82:ℤ) • u 4 - (91:ℤ) • u 3 + (52:ℤ) • u 2 - (12:ℤ) • u 1 := by
  unfold u M
  decide +kernel

theorem rec_u (m : ℕ) : u (m + 7) = (10:ℤ) • u (m + 6) - (40:ℤ) • u (m + 5) + (82:ℤ) • u (m + 4)
    - (91:ℤ) • u (m + 3) + (52:ℤ) • u (m + 2) - (12:ℤ) • u (m + 1) := by
  have h : ∀ k, u (m + k) = (M ^ m).mulVec (u k) := by
    intro k; unfold u; rw [pow_add, ← mulVec_mulVec]
  rw [h, h, h, h, h, h, h, key]
  rw [mulVec_sub, mulVec_add, mulVec_sub, mulVec_add, mulVec_sub, mulVec_smul, mulVec_smul, mulVec_smul,
    mulVec_smul, mulVec_smul, mulVec_smul]

theorem rec_a (m : ℕ) : (a (m + 7) : ℤ) = 10 * a (m + 6) - 40 * a (m + 5) + 82 * a (m + 4)
    - 91 * a (m + 3) + 52 * a (m + 2) - 12 * a (m + 1) := by
  simp only [a_eq]
  rw [rec_u]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

theorem a1 : a 1 = 125 := by
  have h : (a 1 : ℤ) = 125 := by rw [a_eq]; unfold u M; decide +kernel
  exact_mod_cast h
theorem a2 : a 2 = 431 := by
  have h : (a 2 : ℤ) = 431 := by rw [a_eq]; unfold u M; decide +kernel
  exact_mod_cast h
theorem a3 : a 3 = 1325 := by
  have h : (a 3 : ℤ) = 1325 := by rw [a_eq]; unfold u M; decide +kernel
  exact_mod_cast h
theorem a4 : a 4 = 3867 := by
  have h : (a 4 : ℤ) = 3867 := by rw [a_eq]; unfold u M; decide +kernel
  exact_mod_cast h
theorem a5 : a 5 = 11029 := by
  have h : (a 5 : ℤ) = 11029 := by rw [a_eq]; unfold u M; decide +kernel
  exact_mod_cast h
theorem a6 : a 6 = 31215 := by
  have h : (a 6 : ℤ) = 31215 := by rw [a_eq]; unfold u M; decide +kernel
  exact_mod_cast h

theorem rec_q (m : ℕ) : (a (m + 7) : ℚ) = 10 * a (m + 6) - 40 * a (m + 5) + 82 * a (m + 4)
    - 91 * a (m + 3) + 52 * a (m + 2) - 12 * a (m + 1) := by
  exact_mod_cast rec_a m

theorem closed : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 23 / 2 - 2 ^ (4 + n) + 7 * 3 ^ (2 + n) / 2 + 2 * (n : ℚ) + 3 * 2 ^ (3 + n) * (n : ℚ) + (n : ℚ) ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h7 : 7 ≤ n
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
      rw [rec_q, ih (m + 6) (by omega) (by omega), ih (m + 5) (by omega) (by omega),
        ih (m + 4) (by omega) (by omega), ih (m + 3) (by omega) (by omega),
        ih (m + 2) (by omega) (by omega), ih (m + 1) (by omega) (by omega)]
      push_cast
      ring
    · interval_cases n
      · rw [a1]; norm_num
      · rw [a2]; norm_num
      · rw [a3]; norm_num
      · rw [a4]; norm_num
      · rw [a5]; norm_num
      · rw [a6]; norm_num

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have hQ : (((1 - PowerSeries.X) ^ 3 * (1 - 2 * PowerSeries.X) ^ 2 * (1 - 3 * PowerSeries.X)) : PowerSeries ℚ)
      = 1 - PowerSeries.C (10:ℚ) * PowerSeries.X + PowerSeries.C (40:ℚ) * PowerSeries.X ^ 2
        - PowerSeries.C (82:ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (91:ℚ) * PowerSeries.X ^ 4
        - PowerSeries.C (52:ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (12:ℚ) * PowerSeries.X ^ 6 := by
    simp only [map_ofNat]; ring
  have hN : (PowerSeries.X * (125 - 819 * PowerSeries.X + 2015 * PowerSeries.X ^ 2 - 2393 * PowerSeries.X ^ 3 + 1392 * PowerSeries.X ^ 4 - 324 * PowerSeries.X ^ 5) : PowerSeries ℚ)
      = PowerSeries.C (125:ℚ) * PowerSeries.X - PowerSeries.C (819:ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (2015:ℚ) * PowerSeries.X ^ 3
        - PowerSeries.C (2393:ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (1392:ℚ) * PowerSeries.X ^ 5
        - PowerSeries.C (324:ℚ) * PowerSeries.X ^ 6 := by
    simp only [map_ofNat]; ring
  rw [hQ, hN]
  have hex : A * (1 - PowerSeries.C (10:ℚ) * PowerSeries.X + PowerSeries.C (40:ℚ) * PowerSeries.X ^ 2
        - PowerSeries.C (82:ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (91:ℚ) * PowerSeries.X ^ 4
        - PowerSeries.C (52:ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (12:ℚ) * PowerSeries.X ^ 6)
      = A - PowerSeries.C (10:ℚ) * (A * PowerSeries.X) + PowerSeries.C (40:ℚ) * (A * PowerSeries.X ^ 2)
        - PowerSeries.C (82:ℚ) * (A * PowerSeries.X ^ 3) + PowerSeries.C (91:ℚ) * (A * PowerSeries.X ^ 4)
        - PowerSeries.C (52:ℚ) * (A * PowerSeries.X ^ 5) + PowerSeries.C (12:ℚ) * (A * PowerSeries.X ^ 6) := by ring
  rw [hex]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X, hA, PowerSeries.coeff_mk]
  by_cases h7 : 7 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have h' := rec_q m
    have e1 : m + 7 - 1 = m + 6 := by omega
    have e2 : m + 7 - 2 = m + 5 := by omega
    have e3 : m + 7 - 3 = m + 4 := by omega
    have e4 : m + 7 - 4 = m + 3 := by omega
    have e5 : m + 7 - 5 = m + 2 := by omega
    have e6 : m + 7 - 6 = m + 1 := by omega
    simp [e1, e2, e3, e4, e5, e6, h', show m + 7 ≠ 1 by omega, show m + 7 ≠ 2 by omega, show m + 7 ≠ 3 by omega,
      show m + 7 ≠ 4 by omega, show m + 7 ≠ 5 by omega, show m + 7 ≠ 6 by omega,
      show m + 6 ≠ 0 by omega, show m + 5 ≠ 0 by omega, show m + 4 ≠ 0 by omega, show m + 3 ≠ 0 by omega,
      show m + 2 ≠ 0 by omega, show m + 1 ≠ 0 by omega]
    ring
  · interval_cases n <;> simp [a1, a2, a3, a4, a5, a6] <;> norm_num

end OMA.S_oeis_a250900

theorem OMA.solution : type_of% @OMA.S_oeis_a250900.main := by
  refine ⟨?_, OMA.S_oeis_a250900.gf, OMA.S_oeis_a250900.closed⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have h := OMA.S_oeis_a250900.rec_a m
  have e1 : m + 7 - 1 = m + 6 := by omega
  have e2 : m + 7 - 2 = m + 5 := by omega
  have e3 : m + 7 - 3 = m + 4 := by omega
  have e4 : m + 7 - 4 = m + 3 := by omega
  have e5 : m + 7 - 5 = m + 2 := by omega
  have e6 : m + 7 - 6 = m + 1 := by omega
  rw [e1, e2, e3, e4, e5, e6]
  exact h
