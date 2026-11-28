import OMAStatements.S_oeis_a198908
import Mathlib

open OMA.S_oeis_a198908 Finset

namespace OMA.P_oeis_a198908

def S (f : ℕ → ℕ → ℕ → ℤ) (t a b : ℕ) : ℤ :=
  let old := range (t+2)
  (∑ y ∈ old.erase b, f t b y) +
  (∑ x ∈ (old.erase a).erase b, ∑ y ∈ (old.erase b).erase x, f t x y) +
  (if t+2 < 8 then
     (∑ y ∈ old.erase b, f (t+1) (t+2) y) +
     (∑ x ∈ old.erase a, f (t+1) x (t+2)) else 0) +
  (if t+3 < 8 then f (t+2) (t+2) (t+3) else 0)

theorem ext_succ (n t a b : ℕ) : extensions 8 (n + 1) t a b = S (extensions 8 n) t a b := rfl

def InR (t a b : ℕ) : Prop := t < 7 ∧ a < 8 ∧ b < 8

theorem S_congr (f g : ℕ → ℕ → ℕ → ℤ) (h : ∀ t a b, InR t a b → f t a b = g t a b)
    (t a b : ℕ) (hr : InR t a b) : S f t a b = S g t a b := by
  obtain ⟨ht, ha, hb⟩ := hr
  have m1 : ∀ y ∈ (range (t + 2)).erase b, y < 8 := by
    intro y hy; have := (mem_range.mp (mem_of_mem_erase hy)); omega
  have m2 : ∀ x ∈ ((range (t + 2)).erase a).erase b, x < 8 := by
    intro y hy; have := (mem_range.mp (mem_of_mem_erase (mem_of_mem_erase hy))); omega
  have m3 : ∀ x, ∀ y ∈ ((range (t + 2)).erase b).erase x, y < 8 := by
    intro x y hy; have := (mem_range.mp (mem_of_mem_erase (mem_of_mem_erase hy))); omega
  have m4 : ∀ x ∈ (range (t + 2)).erase a, x < 8 := by
    intro y hy; have := (mem_range.mp (mem_of_mem_erase hy)); omega
  unfold S
  simp only
  congr 1
  congr 1
  congr 1
  · exact sum_congr rfl fun y hy => h _ _ _ ⟨ht, hb, m1 y hy⟩
  · exact sum_congr rfl fun x hx => sum_congr rfl fun y hy => h _ _ _ ⟨ht, m2 x hx, m3 x y hy⟩
  · split_ifs with h2
    · congr 1
      · exact sum_congr rfl fun y hy => h _ _ _ ⟨by omega, by omega, m1 y hy⟩
      · exact sum_congr rfl fun x hx => h _ _ _ ⟨by omega, m4 x hx, by omega⟩
    · rfl
  · split_ifs with h3
    · exact h _ _ _ ⟨by omega, by omega, by omega⟩
    · rfl

theorem S_lin (f₁ f₂ f₃ f₄ f₅ f₆ : ℕ → ℕ → ℕ → ℤ) (c₁ c₂ c₃ c₄ c₅ c₆ : ℤ) (t a b : ℕ) :
    S (fun t a b => c₁ * f₁ t a b + c₂ * f₂ t a b + c₃ * f₃ t a b + c₄ * f₄ t a b + c₅ * f₅ t a b +
      c₆ * f₆ t a b) t a b =
    c₁ * S f₁ t a b + c₂ * S f₂ t a b + c₃ * S f₃ t a b + c₄ * S f₄ t a b + c₅ * S f₅ t a b +
      c₆ * S f₆ t a b := by
  unfold S
  simp only [sum_add_distrib, ← mul_sum]
  split_ifs <;> ring

def L3 (v : List (List (List ℤ))) (t a b : ℕ) : ℤ := ((v.getD t []).getD a []).getD b 0

def mk3 (f : ℕ → ℕ → ℕ → ℤ) : List (List (List ℤ)) :=
  (List.range 7).map fun t => (List.range 8).map fun a => (List.range 8).map fun b => f t a b

theorem L3_mk3 (f : ℕ → ℕ → ℕ → ℤ) (t a b : ℕ) (hr : InR t a b) : L3 (mk3 f) t a b = f t a b := by
  obtain ⟨ht, ha, hb⟩ := hr
  unfold L3 mk3
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht,
    List.getElem?_range ha, List.getElem?_range hb, Option.map_some, Option.getD_some]

def cv : ℕ → List (List (List ℤ))
  | 0 => mk3 (fun _ _ _ => 1)
  | n + 1 => mk3 (S (L3 (cv n)))

theorem comp_eq : ∀ n t a b, InR t a b → extensions 8 n t a b = L3 (cv n) t a b
  | 0, t, a, b, hr => by rw [cv, L3_mk3 _ _ _ _ hr]; rfl
  | n + 1, t, a, b, hr => by
    rw [ext_succ, cv, L3_mk3 _ _ _ _ hr]
    exact S_congr _ _ (fun t a b h => comp_eq n t a b h) t a b hr

def baseOK : Bool :=
  (List.range 7).all fun t => (List.range 8).all fun a => (List.range 8).all fun b =>
    L3 (cv 8) t a b == 88 * L3 (cv 7) t a b - 2613 * L3 (cv 6) t a b + 33232 * L3 (cv 5) t a b - 184531 * L3 (cv 4) t a b + 400344 * L3 (cv 3) t a b - 246519 * L3 (cv 2) t a b

set_option maxHeartbeats 0 in
theorem base_ok : baseOK = true := by decide +kernel

theorem rec_all : ∀ k t a b, InR t a b → extensions 8 (k + 8) t a b = 88 * extensions 8 (k + 7) t a b - 2613 * extensions 8 (k + 6) t a b + 33232 * extensions 8 (k + 5) t a b - 184531 * extensions 8 (k + 4) t a b + 400344 * extensions 8 (k + 3) t a b - 246519 * extensions 8 (k + 2) t a b := by
  intro k
  induction k with
  | zero =>
    intro t a b hr
    obtain ⟨ht, ha, hb⟩ := hr
    have h := List.all_eq_true.mp base_ok t (by simpa using ht)
    have h2 := List.all_eq_true.mp h a (by simpa using ha)
    have h3 := List.all_eq_true.mp h2 b (by simpa using hb)
    simp only [comp_eq 2 t a b ⟨ht, ha, hb⟩, comp_eq 3 t a b ⟨ht, ha, hb⟩, comp_eq 4 t a b ⟨ht, ha, hb⟩, comp_eq 5 t a b ⟨ht, ha, hb⟩, comp_eq 6 t a b ⟨ht, ha, hb⟩, comp_eq 7 t a b ⟨ht, ha, hb⟩, comp_eq 8 t a b ⟨ht, ha, hb⟩, Nat.zero_add]
    simpa using h3
  | succ k ih =>
    intro t a b hr
    simp only [show k + 1 + 8 = (k + 8) + 1 by omega, show k + 1 + 7 = (k + 7) + 1 by omega,
      show k + 1 + 6 = (k + 6) + 1 by omega, show k + 1 + 5 = (k + 5) + 1 by omega,
      show k + 1 + 4 = (k + 4) + 1 by omega, show k + 1 + 3 = (k + 3) + 1 by omega,
      show k + 1 + 2 = (k + 2) + 1 by omega, ext_succ]
    rw [S_congr _ _ ih t a b hr]
    have := S_lin (extensions 8 (k + 7)) (extensions 8 (k + 6)) (extensions 8 (k + 5))
      (extensions 8 (k + 4)) (extensions 8 (k + 3)) (extensions 8 (k + 2))
      88 (-2613) 33232 (-184531) 400344 (-246519) t a b
    rw [show (fun t a b => 88 * extensions 8 (k + 7) t a b - 2613 * extensions 8 (k + 6) t a b + 33232 * extensions 8 (k + 5) t a b - 184531 * extensions 8 (k + 4) t a b + 400344 * extensions 8 (k + 3) t a b - 246519 * extensions 8 (k + 2) t a b) =
      (fun t a b => 88 * extensions 8 (k + 7) t a b + (-2613) * extensions 8 (k + 6) t a b +
        33232 * extensions 8 (k + 5) t a b + (-184531) * extensions 8 (k + 4) t a b +
        400344 * extensions 8 (k + 3) t a b + (-246519) * extensions 8 (k + 2) t a b) from by
      funext t a b; ring]
    rw [this]; ring

theorem sv (m : ℕ) : OMA.S_oeis_a198908.sequence (m + 1) = L3 (cv m) 0 0 1 := comp_eq m 0 0 1 ⟨by norm_num, by norm_num, by norm_num⟩

def F (j : ℕ) : ℤ := 1036945 + 344344*3^j + 75465*7^j + 12040*13^j + 2795*21^j + 91*43^j

end OMA.P_oeis_a198908

open OMA.P_oeis_a198908 in
set_option maxHeartbeats 0 in
theorem OMA.solution : type_of% @OMA.S_oeis_a198908.main := by
  have key : ∀ m, 2817360 * OMA.S_oeis_a198908.sequence (m + 1) = F (m + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases Nat.lt_or_ge m 8 with h | h
      · rw [sv]; unfold F; interval_cases m <;> decide +kernel
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
        have r := rec_all k 0 0 1 ⟨by norm_num, by norm_num, by norm_num⟩
        have e : ∀ j, OMA.S_oeis_a198908.sequence (j + 1) = extensions 8 j 0 0 1 := fun j => rfl
        rw [e, r]
        have i7 := ih (k + 7) (by omega); have i6 := ih (k + 6) (by omega)
        have i5 := ih (k + 5) (by omega); have i4 := ih (k + 4) (by omega)
        have i3 := ih (k + 3) (by omega); have i2 := ih (k + 2) (by omega)
        rw [e] at i7 i6 i5 i4 i3 i2
        unfold F at *
        simp only [pow_succ, pow_add] at *
        linear_combination 88 * i7 - 2613 * i6 + 33232 * i5 - 184531 * i4 + 400344 * i3 - 246519 * i2
  refine ⟨fun m => by rw [key]; rfl, ?_⟩
  intro n
  rcases Nat.lt_or_ge n 9 with h | h
  · interval_cases n <;> simp only [delayed, numerator] <;> simp (disch := omega) only [if_pos, if_neg, Nat.sub_zero] <;>
      simp only [OMA.S_oeis_a198908.sequence, sv] <;> decide +kernel
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    have r := rec_all k 0 0 1 ⟨by norm_num, by norm_num, by norm_num⟩
    have hz : numerator (k + 9) = 0 := by
      unfold numerator
      simp only [show k + 9 ≠ 1 by omega, show k + 9 ≠ 2 by omega, show k + 9 ≠ 3 by omega, show k + 9 ≠ 4 by omega, show k + 9 ≠ 5 by omega, show k + 9 ≠ 6 by omega, if_false]
    rw [hz]
    simp only [delayed, show 0 ≤ k + 9 by omega, show 1 ≤ k + 9 by omega, show 2 ≤ k + 9 by omega, show 3 ≤ k + 9 by omega, show 4 ≤ k + 9 by omega, show 5 ≤ k + 9 by omega, show 6 ≤ k + 9 by omega, if_true,
      show k + 9 - 0 = (k + 8) + 1 by omega, show k + 9 - 1 = (k + 7) + 1 by omega, show k + 9 - 2 = (k + 6) + 1 by omega, show k + 9 - 3 = (k + 5) + 1 by omega, show k + 9 - 4 = (k + 4) + 1 by omega, show k + 9 - 5 = (k + 3) + 1 by omega, show k + 9 - 6 = (k + 2) + 1 by omega]
    have e : ∀ j, OMA.S_oeis_a198908.sequence (j + 1) = extensions 8 j 0 0 1 := fun j => rfl
    simp only [e]
    linarith
