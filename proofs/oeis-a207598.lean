import OMAStatements.S_oeis_a207598
import Mathlib

namespace A207598Aux

def RS : List ℕ := [25, 27, 28, 29, 30, 31, 51, 54, 55, 57, 59, 60, 61, 62, 63, 76, 77, 78, 79, 89, 91, 92, 93, 94, 95, 102, 103, 108, 109, 110, 111, 115, 118, 119, 121, 123, 124, 125, 126, 127]

open OMA.S_oeis_a207598 in
lemma rows_eq : rows 7 0 2 = RS := by decide +kernel

open OMA.S_oeis_a207598 in
def cnt (rs : List ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | h + 1, r => ((below rs r).map (cnt rs h)).sum

open OMA.S_oeis_a207598 in
lemma cnt_succ (rs : List ℕ) (h r : ℕ) :
    cnt rs (h + 1) r = ((below rs r).map (cnt rs h)).sum := rfl

open OMA.S_oeis_a207598 in
lemma len_tails (rs : List ℕ) (h : ℕ) : ∀ r : ℕ, (tails rs h r).length = cnt rs h r := by
  induction h with
  | zero =>
    intro r
    simp [tails, cnt]
  | succ h ih =>
    intro r
    rw [cnt_succ, tails, List.length_flatMap]
    congr 1
    refine List.map_congr_left (fun s _ => ?_)
    simp only [List.length_map, ih]

lemma flat_len (rs : List ℕ) (T : List (List ℕ)) :
    (rs.flatMap fun r => T.map (r :: ·)).length = rs.length * T.length := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    rw [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons]
    ring

open OMA.S_oeis_a207598 in
lemma sum_lin (rs : List ℕ) (h : ℕ)
    (hP : ∀ s ∈ rs, cnt rs (h + 5) s + 10 * cnt rs (h + 3) s + 5 * cnt rs (h + 1) s
      = 5 * cnt rs (h + 4) s + 10 * cnt rs (h + 2) s + cnt rs h s) :
    ∀ l : List ℕ, (∀ s ∈ l, s ∈ rs) →
      (l.map (cnt rs (h + 5))).sum + 10 * (l.map (cnt rs (h + 3))).sum
          + 5 * (l.map (cnt rs (h + 1))).sum
        = 5 * (l.map (cnt rs (h + 4))).sum + 10 * (l.map (cnt rs (h + 2))).sum
          + (l.map (cnt rs h)).sum := by
  intro l
  induction l with
  | nil =>
    intro _
    simp
  | cons s l ih =>
    intro hl
    have h1 := hP s (hl s List.mem_cons_self)
    have h2 := ih (fun t ht => hl t (List.mem_cons_of_mem _ ht))
    simp only [List.map_cons, List.sum_cons]
    omega

open OMA.S_oeis_a207598 in
lemma allP (rs : List ℕ)
    (hb : ∀ s ∈ rs, cnt rs 5 s + 10 * cnt rs 3 s + 5 * cnt rs 1 s
      = 5 * cnt rs 4 s + 10 * cnt rs 2 s + cnt rs 0 s) :
    ∀ h : ℕ, ∀ s ∈ rs, cnt rs (h + 5) s + 10 * cnt rs (h + 3) s + 5 * cnt rs (h + 1) s
      = 5 * cnt rs (h + 4) s + 10 * cnt rs (h + 2) s + cnt rs h s := by
  intro h
  induction h with
  | zero => exact hb
  | succ h ih =>
    intro r _
    have key := sum_lin rs h ih (below rs r) (fun s hs => (List.mem_filter.mp hs).1)
    rw [← cnt_succ, ← cnt_succ, ← cnt_succ, ← cnt_succ, ← cnt_succ, ← cnt_succ] at key
    exact key

lemma base : ∀ s ∈ RS, cnt RS 5 s + 10 * cnt RS 3 s + 5 * cnt RS 1 s
      = 5 * cnt RS 4 s + 10 * cnt RS 2 s + cnt RS 0 s := by decide +kernel

lemma mem_full : (2 ^ 7 - 1) ∈ RS := by decide +kernel

open OMA.S_oeis_a207598 in
lemma a_succ (n : ℕ) : a (n + 1) = ((RS.length * cnt RS n (2 ^ 7 - 1) : ℕ) : ℤ) := by
  have h : a (n + 1) = (((rows 7 0 2).flatMap fun r =>
      (tails (rows 7 0 2) n (2 ^ 7 - 1)).map (r :: ·)).length : ℤ) := rfl
  rw [h, flat_len, len_tails, rows_eq]

open OMA.S_oeis_a207598 in
lemma vals : a 0 = 0 ∧ a 1 = 40 ∧ a 2 = 1600 ∧ a 3 = 9240 ∧ a 4 = 30400 ∧ a 5 = 75400 :=
  ⟨rfl, (a_succ 0).trans (by decide +kernel), (a_succ 1).trans (by decide +kernel),
    (a_succ 2).trans (by decide +kernel), (a_succ 3).trans (by decide +kernel),
    (a_succ 4).trans (by decide +kernel)⟩

open OMA.S_oeis_a207598 in
lemma a_rec (n : ℕ) : a (n + 6) = 5 * a (n + 5) - 10 * a (n + 4) + 10 * a (n + 3)
    - 5 * a (n + 2) + a (n + 1) := by
  have hP := allP RS base n (2 ^ 7 - 1) mem_full
  have h6 : a (n + 6) = ((RS.length * cnt RS (n + 5) (2 ^ 7 - 1) : ℕ) : ℤ) := a_succ (n + 5)
  have h5 : a (n + 5) = ((RS.length * cnt RS (n + 4) (2 ^ 7 - 1) : ℕ) : ℤ) := a_succ (n + 4)
  have h4 : a (n + 4) = ((RS.length * cnt RS (n + 3) (2 ^ 7 - 1) : ℕ) : ℤ) := a_succ (n + 3)
  have h3 : a (n + 3) = ((RS.length * cnt RS (n + 2) (2 ^ 7 - 1) : ℕ) : ℤ) := a_succ (n + 2)
  have h2 : a (n + 2) = ((RS.length * cnt RS (n + 1) (2 ^ 7 - 1) : ℕ) : ℤ) := a_succ (n + 1)
  have h1 : a (n + 1) = ((RS.length * cnt RS n (2 ^ 7 - 1) : ℕ) : ℤ) := a_succ n
  rw [h6, h5, h4, h3, h2, h1]
  have hZ : ((cnt RS (n + 5) (2 ^ 7 - 1) : ℕ) : ℤ) + 10 * ((cnt RS (n + 3) (2 ^ 7 - 1) : ℕ) : ℤ)
      + 5 * ((cnt RS (n + 1) (2 ^ 7 - 1) : ℕ) : ℤ)
      = 5 * ((cnt RS (n + 4) (2 ^ 7 - 1) : ℕ) : ℤ) + 10 * ((cnt RS (n + 2) (2 ^ 7 - 1) : ℕ) : ℤ)
        + ((cnt RS n (2 ^ 7 - 1) : ℕ) : ℤ) := by
    exact_mod_cast hP
  push_cast
  linear_combination ((RS.length : ℕ) : ℤ) * hZ

end A207598Aux

open OMA.S_oeis_a207598 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a207598.main := by
  refine ⟨?_, A207598Aux.a_rec⟩
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := A207598Aux.vals
  have hD : ((1 : PowerSeries ℤ) - X) ^ 5
      = C 1 * X ^ 0 + C (-5) * X ^ 1 + C 10 * X ^ 2 + C (-10) * X ^ 3 + C 5 * X ^ 4
        + C (-1) * X ^ 5 := by
    simp only [map_neg, map_ofNat, map_one]; ring
  have hN : (40 * X * (1 + 35 * X + 41 * X ^ 2 - 5 * X ^ 3) : PowerSeries ℤ)
      = C (40) * X ^ 1 + C (1400) * X ^ 2 + C (1640) * X ^ 3 + C (-200) * X ^ 4 := by
    simp only [map_neg, map_ofNat, map_one]; ring
  rw [hD, hN]
  ext n
  simp only [mul_add, map_add, ← mul_assoc, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_C,
    PowerSeries.coeff_mk, PowerSeries.coeff_C]
  rcases n with _ | _ | _ | _ | _ | _ | n
  · simp [v0]
  · simp [v0, v1]
  · simp [v0, v1, v2]
  · simp [v0, v1, v2, v3]
  · simp [v0, v1, v2, v3, v4]
  · simp [v0, v1, v2, v3, v4, v5]
  · have h := A207598Aux.a_rec n
    simp
    linarith
