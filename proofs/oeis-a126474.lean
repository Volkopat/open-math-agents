import OMAStatements.S_oeis_a126474
import Mathlib

/-! The digit-chain transfer is from @Mapika's proof in PR #31827. -/

namespace OMA.A126474Proof

open OMA.S_oeis_a126474
open PowerSeries

def cnt (n : ℕ) (v : Fin 6) : ℕ :=
  (Finset.univ.filter fun g : Fin n → Fin 6 => (v :: List.ofFn g).IsChain near).card

private def transfer (u : Fin 6 → ℤ) (v : Fin 6) : ℤ :=
  ∑ w ∈ Finset.univ.filter (near v), u w

def V : ℕ → Fin 6 → ℤ
  | 0 => fun _ => 1
  | n + 1 => transfer (V n)

theorem sum_cons (n : ℕ) (F : (Fin (n + 1) → Fin 6) → ℕ) :
    ∑ f, F f = ∑ x, ∑ g : Fin n → Fin 6, F (Fin.cons x g) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 6)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem a_succ (n : ℕ) : a (n + 1) = ∑ v, cnt n v := by
  unfold a cnt
  simp only [Finset.card_filter]
  rw [sum_cons n]
  simp only [List.ofFn_cons]

theorem cnt_succ (n : ℕ) (v : Fin 6) :
    cnt (n + 1) v = ∑ w ∈ Finset.univ.filter (near v), cnt n w := by
  unfold cnt
  simp only [Finset.card_filter]
  rw [sum_cons n, Finset.sum_filter]
  simp only [List.ofFn_cons, List.isChain_cons_cons]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : near v w <;> simp [h]

theorem cnt_zero (v : Fin 6) : cnt 0 v = 1 := by
  simp [cnt]

theorem cnt_eq (n : ℕ) : ∀ v, (cnt n v : ℤ) = V n v := by
  induction n with
  | zero => intro v; simp [cnt_zero, V]
  | succ n ih =>
    intro v
    rw [cnt_succ, V, transfer]
    push_cast
    simp only [ih]

theorem V_base : ∀ v, V 3 v = 5 * V 2 v + V 1 v - 2 * V 0 v := by
  decide

theorem V_rec (n : ℕ) : ∀ v, V (n + 3) v = 5 * V (n + 2) v + V (n + 1) v - 2 * V n v := by
  induction n with
  | zero => exact V_base
  | succ n ih =>
    intro v
    change transfer (V (n + 3)) v =
      5 * transfer (V (n + 2)) v + transfer (V (n + 1)) v - 2 * transfer (V n) v
    simp only [transfer, ih, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem aV (n : ℕ) : (a (n + 1) : ℤ) = ∑ v, V n v := by
  rw [a_succ]
  push_cast
  exact Finset.sum_congr rfl (fun v _ => cnt_eq n v)

theorem a0 : a 0 = 1 := by
  simp [a]

theorem vals : (a 1 : ℤ) = 6 ∧ (a 2 : ℤ) = 30 ∧ (a 3 : ℤ) = 154 := by
  rw [aV, aV, aV]
  decide

theorem rec_shift (n : ℕ) : (a (n + 3) : ℤ) = 5 * a (n + 2) + a (n + 1) - 2 * a n := by
  cases n with
  | zero => norm_num [a0, vals.1, vals.2.1, vals.2.2]
  | succ n =>
    change (a (n + 3 + 1) : ℤ) = 5 * a (n + 2 + 1) + a (n + 1 + 1) - 2 * a (n + 1)
    simp only [aV, V_rec n, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem recZ (n : ℕ) (hn : 2 < n) : (a n : ℤ) = 5 * a (n - 1) + a (n - 2) - 2 * a (n - 3) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  simpa [Nat.add_sub_assoc] using rec_shift j

end OMA.A126474Proof

open OMA.S_oeis_a126474 OMA.A126474Proof PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a126474.main := by
  refine ⟨recZ, ?_⟩
  ext k
  have e1 : ∀ A : PowerSeries ℚ, A * (1 - 5 * X - X ^ 2 + 2 * X ^ 3) =
      A - C (5 : ℚ) * (A * X ^ 1) - A * X ^ 2 + C (2 : ℚ) * (A * X ^ 3) := by
    intro A
    simp only [map_ofNat]
    ring
  have e2 : (1 + X - X ^ 2 : PowerSeries ℚ) = C (1 : ℚ) + C (1 : ℚ) * X ^ 1 - C (1 : ℚ) * X ^ 2 := by
    rw [map_one]
    ring
  rw [e1, e2]
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, coeff_C, coeff_mk]
  obtain ⟨v1, v2, v3⟩ := vals
  have q1 : (a 1 : ℚ) = 6 := by exact_mod_cast v1
  have q2 : (a 2 : ℚ) = 30 := by exact_mod_cast v2
  rcases (show k ≤ 2 ∨ 3 ≤ k by omega) with hk | hk
  · interval_cases k <;> simp [a0, q1, q2] <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hq : (a (j + 3) : ℚ) = 5 * a (j + 2) + a (j + 1) - 2 * a j := by
      exact_mod_cast rec_shift j
    simp (disch := omega) [Nat.add_sub_assoc]
    rw [hq]
    ring
