import OMAStatements.S_oeis_a221464
import Mathlib

/-!
Proof sketch. The neighbor condition with `x 0 = 0` reduces to `x 1 ≠ 0`, `x 3 ≠ x 4` and
`¬(x 2 = x 1 ∧ x 2 = x 3)`. The map `x ↦ (x 1, (x 2 - x 1, x 3 - x 1), x 4 - x 3)` is a bijection
onto `{b ≠ 0} × {(u, v) ≠ (0, 0)} × {w ≠ 0}`, so `a n = n * (n * (n + 2)) * n = n ^ 4 + 2 n ^ 3`.
The recurrence is then a polynomial identity. For the g.f., multiplying `mk p` by `1 - X` gives
`mk (Δ p) + C (p (-1))`; five steps reach the zero sequence and leave a polynomial in `X`.
-/

namespace R221464
open OMA.S_oeis_a221464

theorem v0 {α : Type*} (a b c d e : α) : ![a, b, c, d, e] 0 = a := rfl
theorem v1 {α : Type*} (a b c d e : α) : ![a, b, c, d, e] 1 = b := rfl
theorem v2 {α : Type*} (a b c d e : α) : ![a, b, c, d, e] 2 = c := rfl
theorem v3 {α : Type*} (a b c d e : α) : ![a, b, c, d, e] 3 = d := rfl
theorem v4 {α : Type*} (a b c d e : α) : ![a, b, c, d, e] 4 = e := rfl

theorem fin5_cases : ∀ i : Fin 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  decide

theorem cond_iff {n : ℕ} (x : Fin 5 → Fin (n + 1)) :
    (x 0 = 0 ∧ ∀ i : Fin 5, ∃ j : Fin 5, (j.val + 1 = i.val ∨ i.val + 1 = j.val) ∧ x i ≠ x j) ↔
    (x 0 = 0 ∧ x 1 ≠ 0 ∧ x 3 ≠ x 4 ∧ ¬(x 2 = x 1 ∧ x 2 = x 3)) := by
  have k0 : ∀ j : Fin 5, (j.val + 1 = (0 : Fin 5).val ∨ (0 : Fin 5).val + 1 = j.val) → j = 1 := by
    decide
  have k2 : ∀ j : Fin 5, (j.val + 1 = (2 : Fin 5).val ∨ (2 : Fin 5).val + 1 = j.val) →
      j = 1 ∨ j = 3 := by
    decide
  have k4 : ∀ j : Fin 5, (j.val + 1 = (4 : Fin 5).val ∨ (4 : Fin 5).val + 1 = j.val) → j = 3 := by
    decide
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_, ?_, ?_⟩
    · obtain ⟨j, hj, hx⟩ := h 0
      rw [k0 j hj, h0] at hx
      exact fun e => hx e.symm
    · obtain ⟨j, hj, hx⟩ := h 4
      rw [k4 j hj] at hx
      exact fun e => hx e.symm
    · obtain ⟨j, hj, hx⟩ := h 2
      rcases k2 j hj with rfl | rfl
      · exact fun e => hx e.1
      · exact fun e => hx e.2
  · rintro ⟨h0, h1, h34, h2⟩
    refine ⟨h0, fun i => ?_⟩
    rcases fin5_cases i with rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, by decide, by rw [h0]; exact fun e => h1 e.symm⟩
    · exact ⟨0, by decide, by rw [h0]; exact h1⟩
    · by_cases e : x 2 = x 1
      · exact ⟨3, by decide, fun e' => h2 ⟨e, e'⟩⟩
      · exact ⟨1, by decide, e⟩
    · by_cases e : x 3 = x 2
      · exact ⟨4, by decide, h34⟩
      · exact ⟨2, by decide, e⟩
    · exact ⟨3, by decide, fun e => h34 e.symm⟩

theorem card_a (n : ℕ) : a n = n * (n * (n + 2) * n) := by
  have hsq : (n + 1) * (n + 1) - 1 = n * (n + 2) := by
    rw [show (n + 1) * (n + 1) = n * (n + 2) + 1 by ring, Nat.add_sub_cancel]
  have hT : (((Finset.univ : Finset (Fin (n + 1))).erase 0) ×ˢ
      (((Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).erase (0, 0)) ×ˢ
        ((Finset.univ : Finset (Fin (n + 1))).erase 0))).card = n * (n * (n + 2) * n) := by
    rw [Finset.card_product, Finset.card_product,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (n + 1))),
      Finset.card_erase_of_mem (Finset.mem_univ ((0, 0) : Fin (n + 1) × Fin (n + 1))),
      Finset.card_univ, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.add_sub_cancel,
      hsq]
  rw [← hT]
  unfold a
  refine Finset.card_nbij'
    (fun x : Fin 5 → Fin (n + 1) =>
      ((x 1, (x 2 - x 1, x 3 - x 1), x 4 - x 3) : Fin (n + 1) × (Fin (n + 1) × Fin (n + 1)) × Fin (n + 1)))
    (fun p : Fin (n + 1) × (Fin (n + 1) × Fin (n + 1)) × Fin (n + 1) =>
      (![0, p.1, p.2.1.1 + p.1, p.2.1.2 + p.1, p.2.2 + (p.2.1.2 + p.1)] : Fin 5 → Fin (n + 1)))
    ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨h0, h1, h34, h2⟩ := (cond_iff x).1 (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
    refine Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_erase.2 ⟨h1, Finset.mem_univ _⟩,
      Finset.mem_product.2 ⟨Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩,
        Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩⟩⟩)
    · show (x 2 - x 1, x 3 - x 1) ≠ (0, 0)
      intro e
      obtain ⟨e1, e2⟩ := Prod.mk.inj e
      exact h2 ⟨sub_eq_zero.1 e1, (sub_eq_zero.1 e1).trans (sub_eq_zero.1 e2).symm⟩
    · show x 4 - x 3 ≠ 0
      exact fun e => h34 (sub_eq_zero.1 e).symm
  · rintro ⟨b, ⟨u, v⟩, w⟩ hp
    obtain ⟨hb, huvw⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hp)
    obtain ⟨huv, hw⟩ := Finset.mem_product.1 huvw
    have hb' : b ≠ 0 := (Finset.mem_erase.1 hb).1
    have huv' : (u, v) ≠ (0, 0) := (Finset.mem_erase.1 huv).1
    have hw' : w ≠ 0 := (Finset.mem_erase.1 hw).1
    refine Finset.mem_coe.2 (Finset.mem_filter.2
      ⟨Finset.mem_univ _, (cond_iff _).2 ⟨rfl, hb', ?_, ?_⟩⟩)
    · show v + b ≠ w + (v + b)
      intro e
      apply hw'
      have h : w = w + (v + b) - (v + b) := (add_sub_cancel_right w (v + b)).symm
      rw [h, ← e, sub_self]
    · show ¬(u + b = b ∧ u + b = v + b)
      rintro ⟨e1, e2⟩
      apply huv'
      have hu : u = 0 := add_right_cancel (e1.trans (zero_add b).symm)
      have hv : v = 0 := add_right_cancel ((e2.symm.trans e1).trans (zero_add b).symm)
      rw [hu, hv]
  · intro x hx
    have h0 : x 0 = 0 := ((cond_iff x).1 (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2).1
    funext k
    rcases fin5_cases k with rfl | rfl | rfl | rfl | rfl <;>
      simp only [v0, v1, v2, v3, v4, sub_add_cancel, h0]
  · rintro ⟨b, ⟨u, v⟩, w⟩ _
    simp only [v1, v2, v3, v4, add_sub_cancel_right]

theorem a_eq (n : ℕ) : (a n : ℤ) = (n : ℤ) ^ 4 + 2 * (n : ℤ) ^ 3 := by
  rw [card_a]
  push_cast
  ring

theorem D (f g : ℕ → ℤ) (c : ℤ) (h0 : g 0 = f 0 - c) (hs : ∀ k : ℕ, g (k + 1) = f (k + 1) - f k) :
    (1 - PowerSeries.X) * PowerSeries.mk f = PowerSeries.mk g + PowerSeries.C c := by
  ext k
  rcases k with _ | k
  · rw [sub_mul, one_mul, map_sub, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_C, h0]
    ring
  · rw [sub_mul, one_mul, map_sub, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_C, hs]
    simp

end R221464

theorem OMA.solution : type_of% @OMA.S_oeis_a221464.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 5 = m + 1 by omega, show m + 6 - 6 = m by omega]
    simp only [R221464.a_eq]
    push_cast
    ring
  · have hA : PowerSeries.mk (fun n => (OMA.S_oeis_a221464.a n : ℤ)) =
        PowerSeries.mk (fun n : ℕ => (n : ℤ) ^ 4 + 2 * (n : ℤ) ^ 3) :=
      congrArg PowerSeries.mk (funext R221464.a_eq)
    have e1 : (1 - PowerSeries.X) * PowerSeries.mk (fun n : ℕ => (n : ℤ) ^ 4 + 2 * (n : ℤ) ^ 3) =
        PowerSeries.mk (fun n : ℕ => 4 * (n : ℤ) ^ 3 - 2 * (n : ℤ) + 1) + PowerSeries.C (-1) :=
      R221464.D _ _ _ (by norm_num) (fun k => by push_cast; ring)
    have e2 : (1 - PowerSeries.X) * PowerSeries.mk (fun n : ℕ => 4 * (n : ℤ) ^ 3 - 2 * (n : ℤ) + 1) =
        PowerSeries.mk (fun n : ℕ => 12 * (n : ℤ) ^ 2 - 12 * (n : ℤ) + 2) + PowerSeries.C (-1) :=
      R221464.D _ _ _ (by norm_num) (fun k => by push_cast; ring)
    have e3 : (1 - PowerSeries.X) * PowerSeries.mk (fun n : ℕ => 12 * (n : ℤ) ^ 2 - 12 * (n : ℤ) + 2) =
        PowerSeries.mk (fun n : ℕ => 24 * (n : ℤ) - 24) + PowerSeries.C 26 :=
      R221464.D _ _ _ (by norm_num) (fun k => by push_cast; ring)
    have e4 : (1 - PowerSeries.X) * PowerSeries.mk (fun n : ℕ => 24 * (n : ℤ) - 24) =
        PowerSeries.mk (fun _ : ℕ => (24 : ℤ)) + PowerSeries.C (-48) :=
      R221464.D _ _ _ (by norm_num) (fun k => by push_cast; ring)
    have e5 : (1 - PowerSeries.X) * PowerSeries.mk (fun _ : ℕ => (24 : ℤ)) =
        PowerSeries.mk (fun _ : ℕ => (0 : ℤ)) + PowerSeries.C 24 :=
      R221464.D _ _ _ (by norm_num) (fun k => by norm_num)
    have hz : PowerSeries.mk (fun _ : ℕ => (0 : ℤ)) = 0 := by
      ext k
      simp
    simp only [map_neg, map_one, map_ofNat] at e1 e2 e3 e4 e5
    linear_combination (1 - PowerSeries.X) ^ 5 * hA + (1 - PowerSeries.X) ^ 4 * e1 +
      (1 - PowerSeries.X) ^ 3 * e2 + (1 - PowerSeries.X) ^ 2 * e3 + (1 - PowerSeries.X) * e4 + e5 + hz
