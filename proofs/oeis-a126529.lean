import OMAStatements.S_oeis_a126529
import Mathlib

namespace OMA.Helpers_a126529
open OMA.S_oeis_a126529

def T : ℕ → Fin 8 → ℤ
  | 0, _ => 1
  | n + 1, d => ∑ e : Fin 8, if near d e then T n e else 0

theorem sum_cons {n : ℕ} (f : (Fin (n + 1) → Fin 8) → ℤ) :
    ∑ y, f y = ∑ v : Fin 8, ∑ z : Fin n → Fin 8, f (Fin.cons v z) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 8) _ _ (fun p => rfl)).symm

theorem cnt : ∀ n (d : Fin 8), (((Finset.univ : Finset (Fin (n + 1) → Fin 8)).filter
    (fun g => (List.ofFn g).IsChain near ∧ g 0 = d)).card : ℤ) = T n d := by
  intro n
  induction n with
  | zero =>
    intro d
    rw [Finset.card_filter, Nat.cast_sum, sum_cons]
    simp [T, Finset.sum_ite_eq']
  | succ n ih =>
    intro d
    rw [Finset.card_filter, Nat.cast_sum, sum_cons, T]
    rw [Finset.sum_eq_single d (fun b _ hb => by
      refine Finset.sum_eq_zero (fun z _ => ?_)
      simp [hb]) (by simp)]
    have key : ∀ z : Fin (n + 1) → Fin 8,
        ((if (List.ofFn (Fin.cons d z : Fin (n + 2) → Fin 8)).IsChain near ∧
          (Fin.cons d z : Fin (n + 2) → Fin 8) 0 = d then 1 else 0 : ℕ) : ℤ) =
        ∑ e : Fin 8, if near d e then (if (List.ofFn z).IsChain near ∧ z 0 = e then 1 else 0) else 0 := by
      intro z
      rw [Finset.sum_eq_single (z 0) (fun b _ hb => by split_ifs <;> simp_all [eq_comm])
        (by simp)]
      simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.isChain_cons_cons]
      by_cases h1 : near d (z 0) <;> by_cases h2 : (List.ofFn fun i => z i.succ).IsChain near <;>
        simp [h1]
    rw [Finset.sum_congr rfl (fun z _ => key z), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    split_ifs with h
    · rw [← ih e, Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl (fun z _ => by split_ifs <;> simp)
    · simp

theorem a_succ (n : ℕ) : (a (n + 1) : ℤ) = ∑ d : Fin 8, T n d := by
  rw [← Finset.sum_congr rfl (fun d _ => cnt n d), a,
    Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := Finset.univ) (by simp)]
  push_cast
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.filter_filter]

theorem Tsucc (n : ℕ) (d : Fin 8) : T (n + 1) d = ∑ e : Fin 8, if near d e then T n e else 0 := rfl

theorem Trec : ∀ n (d : Fin 8), T (n + 3) d = 7 * T (n + 2) d + 3 * T (n + 1) d - 4 * T n d := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    intro d
    rw [Tsucc (n + 3), Tsucc (n + 2), Tsucc (n + 1), Tsucc n, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    split_ifs
    · exact ih e
    · ring

theorem a0 : (a 0 : ℤ) = 1 := by decide

theorem a1 : (a 1 : ℤ) = 8 := by rw [a_succ]; decide
theorem a2 : (a 2 : ℤ) = 58 := by rw [a_succ]; decide
theorem a3 : (a 3 : ℤ) = 426 := by rw [a_succ]; decide

theorem rec (n : ℕ) (hn : 2 < n) : (a n : ℤ) = 7 * a (n - 1) + 3 * a (n - 2) - 4 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rcases m with _ | m
  · simp only [zero_add, show 3 - 2 = 1 by rfl, show 3 - 1 = 2 by rfl, Nat.sub_self]
    rw [a3, a2, a1, a0]; norm_num
  · rw [show m + 1 + 3 - 1 = m + 2 + 1 by omega, show m + 1 + 3 - 2 = m + 1 + 1 by omega,
      show m + 1 + 3 - 3 = m + 1 by omega, show m + 1 + 3 = m + 3 + 1 by omega,
      a_succ, a_succ, a_succ, a_succ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun d _ => Trec m d)

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 7 * X - 3 * X ^ 2 + 4 * X ^ 3) = 1 + X - X ^ 2 := by
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have hD : A * (1 - 7 * X - 3 * X ^ 2 + 4 * X ^ 3 : PowerSeries ℚ) =
      A - C (7 : ℚ) * (A * X ^ 1) - C (3 : ℚ) * (A * X ^ 2) + C (4 : ℚ) * (A * X ^ 3) := by
    simp only [map_ofNat]; ring
  have hN : (1 + X - X ^ 2 : PowerSeries ℚ) = 1 + X ^ 1 - X ^ 2 := by ring
  rw [hD, hN]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_one, coeff_X_pow]
  have q0 : (a 0 : ℚ) = 1 := by exact_mod_cast a0
  have q1 : (a 1 : ℚ) = 8 := by exact_mod_cast a1
  have q2 : (a 2 : ℚ) = 58 := by exact_mod_cast a2
  rcases Nat.lt_or_ge k 3 with h | h
  · interval_cases k <;> simp [q0, q1, q2] <;> norm_num
  · have r := rec k h
    have r' : (a k : ℚ) = 7 * a (k - 1) + 3 * a (k - 2) - 4 * a (k - 3) := by exact_mod_cast r
    simp only [show 1 ≤ k by omega, show 2 ≤ k by omega, show 3 ≤ k by omega, if_true,
      show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, if_false]
    linear_combination r'

end OMA.Helpers_a126529

theorem OMA.solution : type_of% @OMA.S_oeis_a126529.main :=
  ⟨OMA.Helpers_a126529.gf, OMA.Helpers_a126529.rec⟩
