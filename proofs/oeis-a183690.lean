import OMAStatements.S_oeis_a183690
import Mathlib

open OMA.S_oeis_a183690
open PowerSeries

namespace P183690

def c (h : ℕ) (r : Row) : ℤ := ((extensions h r).length : ℤ)

theorem cs (h : ℕ) (r : Row) : c (h + 1) r = ((neighbors r).map (c h)).sum := by
  simp only [c, extensions, List.length_flatMap, List.length_map]
  push_cast [Nat.cast_list_sum]
  simp [List.map_map, Function.comp_def]
  rfl

theorem lsum (l : List Row) (f g k : Row → ℤ) (hl : ∀ s ∈ l, f s = 5 * g s + 8 * k s) :
    (l.map f).sum = 5 * (l.map g).sum + 8 * (l.map k).sum := by
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hl s (by simp), ih (fun x hx => hl x (by simp [hx]))]
    ring

set_option maxRecDepth 100000 in
theorem base : ∀ r : Row, c 3 r = 5 * c 2 r + 8 * c 1 r := by decide +kernel

theorem rec_all : ∀ h : ℕ, ∀ r : Row, c (h + 3) r = 5 * c (h + 2) r + 8 * c (h + 1) r := by
  intro h
  induction h with
  | zero => exact base
  | succ h ih =>
    intro r
    rw [show h + 1 + 3 = (h + 3) + 1 by omega, show h + 1 + 2 = (h + 2) + 1 by omega,
      show h + 1 + 1 = (h + 1) + 1 by omega, cs (h + 3), cs (h + 2), cs (h + 1)]
    exact lsum _ _ _ _ (fun s _ => ih s)

theorem a_eq (h : ℕ) : (a h : ℤ) = (rows.map (c h)).sum := by
  simp only [a, c, List.length_flatMap, List.length_map]
  push_cast [Nat.cast_list_sum]
  simp [List.map_map, Function.comp_def]
  rfl

theorem arec (h : ℕ) : (a (h + 3) : ℤ) = 5 * a (h + 2) + 8 * a (h + 1) := by
  rw [a_eq, a_eq, a_eq]
  exact lsum _ _ _ _ (fun s _ => rec_all h s)

end P183690

theorem OMA.solution : type_of% @OMA.S_oeis_a183690.main := by
  have v1 : (a 1 : ℤ) = 50 := by decide +kernel
  have v2 : (a 2 : ℤ) = 314 := by decide +kernel
  constructor
  · have hp : ((1 - 5 * X - 8 * X ^ 2) : PowerSeries ℚ) = 1 - C 5 * X ^ 1 - C 8 * X ^ 2 := by
      simp only [map_ofNat, pow_one]
    have hq : ∀ F : PowerSeries ℚ, F * (1 - C 5 * X ^ 1 - C 8 * X ^ 2) = F - C 5 * (F * X ^ 1) - C 8 * (F * X ^ 2) :=
      fun F => by ring
    have hr : (2 * X * (25 + 32 * X) : PowerSeries ℚ) = C 50 * X ^ 1 + C 64 * X ^ 2 := by
      simp only [map_ofNat]; ring
    rw [hp, hq, hr]
    clear hp hq hr
    ext n
    simp only [series, map_sub, map_add, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow, coeff_C]
    rcases Nat.lt_or_ge n 3 with hn | hn
    · have v1' : (a 1 : ℚ) = 50 := by exact_mod_cast v1
      have v2' : (a 2 : ℚ) = 314 := by exact_mod_cast v2
      interval_cases n <;> simp [v1', v2'] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have h := P183690.arec m
      have h' : (a (m + 3) : ℚ) = 5 * a (m + 2) + 8 * a (m + 1) := by exact_mod_cast h
      simp (disch := omega) only [if_pos, if_neg]
      rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
      linarith
  · set s := Real.sqrt 57 with hsdef
    have hs : s ^ 2 = 57 := Real.sq_sqrt (by norm_num)
    have hs0 : s ≠ 0 := by positivity
    set g : ℕ → ℝ := fun n => (5 - s) ^ n * (-15 + 2 * s) + (5 + s) ^ n * (15 + 2 * s) with hg
    have grec : ∀ m, g (m + 3) = 10 * g (m + 2) + 32 * g (m + 1) := by
      intro m
      simp only [hg, pow_succ]
      linear_combination ((5 - s) ^ m * (5 - s) * (-15 + 2 * s) + (5 + s) ^ m * (5 + s) * (15 + 2 * s)) * hs
    have key : ∀ n, 1 ≤ n → (a n : ℝ) = g n / (2 ^ (n - 1) * s) := by
      intro n hn
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        rcases (by omega : n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | h3
        · have : (a 1 : ℝ) = 50 := by exact_mod_cast v1
          rw [this]; simp only [hg]; field_simp; ring
        · have : (a 2 : ℝ) = 314 := by exact_mod_cast v2
          rw [this]; simp only [hg]; field_simp; linear_combination (-4 * s) * hs
        · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
          have h := P183690.arec m
          have h' : (a (m + 3) : ℝ) = 5 * a (m + 2) + 8 * a (m + 1) := by exact_mod_cast h
          rw [h', ih (m + 2) (by omega) (by omega), ih (m + 1) (by omega) (by omega), grec m,
            show m + 3 - 1 = m + 2 by omega, show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega]
          field_simp
          ring
    intro n hn
    rw [key n hn]
