import FormalConjectures.ErdosProblems.«945»

/-!
# Erdős Problem 945 — equivalence

Direct proof of `Erdos945Prop ↔ Erdos945Constant` via `Filter.eventually_atTop`,
`filter_upwards`, and `Real.tendsto_log_atTop`.
-/

open Erdos945 Filter Real

theorem OMA.solution : type_of% @Erdos945.erdos_945.variants.equivalence := by
  refine ⟨?_, ?_⟩
  · rintro ⟨O, hO, hF⟩
    obtain ⟨c, hc⟩ := hO.bound
    obtain ⟨Y, hY⟩ := eventually_atTop.mp (hc.and hF)
    set K := max c 0
    set C := K + 1
    have hK : 0 ≤ K := le_max_right _ _
    refine ⟨C, by linarith, ?_⟩
    filter_upwards [eventually_ge_atTop Y, eventually_ge_atTop 2,
      tendsto_log_atTop.eventually_ge_atTop ((C + 1) ^ K + 1)] with x hYx hx2 hL
    have hL1 : 1 ≤ log x := by linarith [one_le_rpow (by linarith : 1 ≤ C + 1) hK]
    have hLC : 0 ≤ log x ^ C := rpow_nonneg (by linarith) C
    set y := x + log x ^ C
    obtain ⟨hOy, hFy⟩ := hY y (by linarith)
    have hxy : (⌊x⌋₊ : ℝ) + ⌊log x ^ C⌋₊ ≤ y :=
      add_le_add (Nat.floor_le (by linarith)) (Nat.floor_le hLC)
    by_contra hno
    have hmem {m} (hm : m ∈ Set.Ioc ⌊x⌋₊ (⌊x⌋₊ + ⌊log x ^ C⌋₊)) : (m : ℝ) ∈ Set.Icc x y :=
      ⟨((Nat.floor_lt (by linarith)).mp hm.1).le, le_trans (by exact_mod_cast hm.2) hxy⟩
    have : (⌊log x ^ C⌋₊ : ℝ) ≤ F y := Nat.cast_le.mpr <| le_csSup
      ⟨⌊y⌋₊, fun _ ⟨n, h, _⟩ => Nat.le_floor (by linarith [Nat.cast_nonneg (α := ℝ) n])⟩
      ⟨⌊x⌋₊, hxy, fun a ha b hb hτ => by by_contra hab; exact hno ⟨a, b, hab, hmem ha, hmem hb, hτ⟩⟩
    have hly : 1 ≤ log y := by linarith [log_le_log (by linarith : 0 < x) (by linarith : x ≤ y)]
    have hyx : y ≤ x ^ (C + 1) := by
      have : log x ^ C ≤ x ^ C := rpow_le_rpow (by linarith)
        (by linarith [log_le_sub_one_of_pos (by linarith : 0 < x)]) (by linarith)
      have : x ≤ x ^ C := by
        simpa using rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ x) (by linarith : (1 : ℝ) ≤ C)
      rw [rpow_add_one (by linarith)]; nlinarith
    have : (F y : ℝ) ≤ (C + 1) ^ K * log x ^ K := calc
      _ ≤ log y ^ O y := hFy
      _ ≤ log y ^ K := rpow_le_rpow_of_exponent_le hly
          (by simp at hOy; linarith [le_abs_self (O y), le_max_left c 0])
      _ ≤ ((C + 1) * log x) ^ K := rpow_le_rpow (by linarith)
          (by rw [← log_rpow (by linarith)]; exact log_le_log (by linarith) hyx) hK
      _ = (C + 1) ^ K * log x ^ K := mul_rpow (by linarith) (by linarith)
    nlinarith [Nat.lt_floor_add_one (log x ^ C),
      rpow_add_one (by linarith : log x ≠ 0) K, one_le_rpow hL1 hK]
  · rintro ⟨C, hC, h⟩
    obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp h
    set X := max X₀ 1
    refine ⟨fun _ => C + 1, Asymptotics.isBigO_const_const _ one_ne_zero _, ?_⟩
    filter_upwards [eventually_ge_atTop X, tendsto_log_atTop.eventually_ge_atTop (X + 1)] with x hx hL
    have hX1 : 1 ≤ X := le_max_right _ _
    have : 0 ≤ log x ^ C := rpow_nonneg (by linarith) C
    have : (F x : ℝ) ≤ X + log x ^ C := (Nat.le_floor_iff (by linarith)).mp <|
      csSup_le' fun k ⟨n, hnk, hinj⟩ => Nat.le_floor <| by
        by_contra hcon
        set x' := max ((n : ℝ) + 1) X
        have : log x' ^ C ≤ log x ^ C := rpow_le_rpow
          (log_nonneg (le_trans hX1 (le_max_right _ _)))
          (log_le_log (by linarith [le_max_right ((n : ℝ) + 1) X]) (max_le (by linarith) hx)) hC.le
        obtain ⟨a, b, hab, ha, hb, hτ⟩ := hX₀ x' (le_trans (le_max_left _ _) (le_max_right _ _))
        have : x' ≤ n + X := max_le (by linarith) (by linarith [Nat.cast_nonneg (α := ℝ) n])
        have hmem {m : ℕ} (hm : (m : ℝ) ∈ Set.Icc x' (x' + log x' ^ C)) : m ∈ Set.Ioc n (n + k) := by
          refine ⟨?_, ?_⟩ <;> rify <;> linarith [hm.1, hm.2, le_max_left ((n : ℝ) + 1) X]
        exact hab (hinj (hmem ha) (hmem hb) hτ)
    nlinarith [rpow_add_one (by linarith : log x ≠ 0) C, one_le_rpow (by linarith : 1 ≤ log x) hC.le]
