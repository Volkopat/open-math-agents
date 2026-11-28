import OMAStatements.S_oeis_a267812
import Mathlib

namespace CAOEISA267812Aux

def F (t : ℕ) (i : ℤ) : Prop :=
  (((t : ℤ) = 0) ∧ ((i = 0))) ∨
  (((t : ℤ) = 1) ∧ (¬((-1 ≤ i ∧ i ≤ 0)))) ∨
  ((2 ≤ (t : ℤ) ∧ (t : ℤ) % 1 = 0) ∧ (¬(i = 0)))

lemma Fph0 (t : ℕ) (i : ℤ) (hg : (t : ℤ) = 0) :
    F t i ↔ ((i = 0)) := by
  unfold F
  constructor
  · intro h
    rcases h with h | h | h
    · exact h.2
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
  · intro h0
    have h := And.intro hg h0
    exact Or.inl h

lemma Fph1 (t : ℕ) (i : ℤ) (hg : (t : ℤ) = 1) :
    F t i ↔ (¬((-1 ≤ i ∧ i ≤ 0))) := by
  unfold F
  constructor
  · intro h
    rcases h with h | h | h
    · exact absurd h.1 (by omega)
    · exact h.2
    · exact absurd h.1 (by omega)
  · intro h0
    have h := And.intro hg h0
    exact Or.inr (Or.inl h)

lemma Fph2 (t : ℕ) (i : ℤ) (hg : 2 ≤ (t : ℤ) ∧ (t : ℤ) % 1 = 0) :
    F t i ↔ (¬(i = 0)) := by
  unfold F
  constructor
  · intro h
    rcases h with h | h | h
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact h.2
  · intro h0
    have h := And.intro hg h0
    exact Or.inr (Or.inr (h))

open OMA.S_oeis_a267812 in
lemma rule_step (b1 b2 b3 : Bool) (P1 P2 P3 Q : Prop) (h1 : b1 = true ↔ P1) (h2 : b2 = true ↔ P2)
    (h3 : b3 = true ↔ P3)
    (H0 : ¬P1 → ¬P2 → ¬P3 → Q) (H1 : ¬P1 → ¬P2 → P3 → ¬Q)
    (H2 : ¬P1 → P2 → ¬P3 → ¬Q) (H3 : ¬P1 → P2 → P3 → Q)
    (H4 : P1 → ¬P2 → ¬P3 → Q) (H5 : P1 → ¬P2 → P3 → ¬Q)
    (H6 : P1 → P2 → ¬P3 → Q) (H7 : P1 → P2 → P3 → Q) :
    ruleOut 217 b1 b2 b3 = true ↔ Q := by
  cases b1 <;> cases b2 <;> cases b3
  · exact ⟨fun _ => H0 (fun h => Bool.false_ne_true (h1.mpr h)) (fun h => Bool.false_ne_true (h2.mpr h)) (fun h => Bool.false_ne_true (h3.mpr h)), fun _ => by decide⟩
  · exact ⟨fun h => absurd h (by decide), fun q => absurd q (H1 (fun h => Bool.false_ne_true (h1.mpr h)) (fun h => Bool.false_ne_true (h2.mpr h)) (h3.mp rfl))⟩
  · exact ⟨fun h => absurd h (by decide), fun q => absurd q (H2 (fun h => Bool.false_ne_true (h1.mpr h)) (h2.mp rfl) (fun h => Bool.false_ne_true (h3.mpr h)))⟩
  · exact ⟨fun _ => H3 (fun h => Bool.false_ne_true (h1.mpr h)) (h2.mp rfl) (h3.mp rfl), fun _ => by decide⟩
  · exact ⟨fun _ => H4 (h1.mp rfl) (fun h => Bool.false_ne_true (h2.mpr h)) (fun h => Bool.false_ne_true (h3.mpr h)), fun _ => by decide⟩
  · exact ⟨fun h => absurd h (by decide), fun q => absurd q (H5 (h1.mp rfl) (fun h => Bool.false_ne_true (h2.mpr h)) (h3.mp rfl))⟩
  · exact ⟨fun _ => H6 (h1.mp rfl) (h2.mp rfl) (fun h => Bool.false_ne_true (h3.mpr h)), fun _ => by decide⟩
  · exact ⟨fun _ => H7 (h1.mp rfl) (h2.mp rfl) (h3.mp rfl), fun _ => by decide⟩

set_option maxHeartbeats 4000000 in
open OMA.S_oeis_a267812 in
lemma cell_iff : ∀ (t : ℕ) (i : ℤ), cell 217 t i = true ↔ F t i := by
  intro t
  induction t with
  | zero =>
    intro i
    rw [cell]
    simp only [decide_eq_true_eq]
    rw [Fph0 0 i (by omega)]
  | succ t ih =>
    intro i
    rw [cell]
    rcases (by omega : ((t : ℤ) = 0) ∨ ((t : ℤ) = 1) ∨ (2 ≤ (t : ℤ) ∧ (t : ℤ) % 1 = 0)) with hg | hg | hg
    · have hg' : ((t + 1 : ℕ) : ℤ) = 1 := by omega
      rw [Fph1 (t + 1) i hg']
      apply rule_step _ _ _ _ _ _ _ ((ih (i - 1)).trans (Fph0 t (i - 1) hg))
        ((ih i).trans (Fph0 t i hg)) ((ih (i + 1)).trans (Fph0 t (i + 1) hg)) <;> omega
    · have hg' : 2 ≤ ((t + 1 : ℕ) : ℤ) ∧ ((t + 1 : ℕ) : ℤ) % 1 = 0 := by omega
      rw [Fph2 (t + 1) i hg']
      apply rule_step _ _ _ _ _ _ _ ((ih (i - 1)).trans (Fph1 t (i - 1) hg))
        ((ih i).trans (Fph1 t i hg)) ((ih (i + 1)).trans (Fph1 t (i + 1) hg)) <;> omega
    · have hg' : 2 ≤ ((t + 1 : ℕ) : ℤ) ∧ ((t + 1 : ℕ) : ℤ) % 1 = 0 := by omega
      rw [Fph2 (t + 1) i hg']
      apply rule_step _ _ _ _ _ _ _ ((ih (i - 1)).trans (Fph2 t (i - 1) hg))
        ((ih i).trans (Fph2 t i hg)) ((ih (i + 1)).trans (Fph2 t (i + 1) hg)) <;> omega

open OMA.S_oeis_a267812 in
def wd (t j : ℕ) : ℤ := if cell 217 t ((j : ℤ) - t) = true then (2 : ℤ) ^ (2 * t - j) else 0

open OMA.S_oeis_a267812 in
lemma a_wd (t : ℕ) : a t = ∑ j ∈ Finset.range (2 * t + 1), wd t j := rfl

lemma wd_pos (t j : ℕ) (h : F t ((j : ℤ) - t)) : wd t j = (2 : ℤ) ^ (2 * t - j) := by
  unfold wd
  rw [if_pos ((cell_iff _ _).mpr h)]

lemma wd_zero (t j : ℕ) (h : ¬ F t ((j : ℤ) - t)) : wd t j = 0 := by
  unfold wd
  rw [if_neg (fun hc => h ((cell_iff _ _).mp hc))]

lemma wd_congr (t t' j j' e : ℕ) (h : F t' ((j' : ℤ) - t') ↔ F t ((j : ℤ) - t))
    (he : 2 * t' - j' = e + (2 * t - j)) : wd t' j' = 2 ^ e * wd t j := by
  by_cases hf : F t ((j : ℤ) - t)
  · rw [wd_pos t' j' (h.mpr hf), wd_pos t j hf, he, pow_add]
  · rw [wd_zero t' j' (fun h' => hf (h.mp h')), wd_zero t j hf, mul_zero]


lemma sum_cutZ (f g : ℕ → ℤ) (c : ℤ) (A e B s1 s2 s3 : ℕ)
    (h1 : ∀ j, j < A → f (s1 + j) = c * g j)
    (h2 : ∀ x, x < B → f (s1 + A + s2 + x) = c * g (A + e + x)) :
    ∑ j ∈ Finset.range (s1 + A + s2 + B + s3), f j =
      c * (∑ j ∈ Finset.range (A + e + B), g j) - c * (∑ k ∈ Finset.range e, g (A + k))
        + (∑ k ∈ Finset.range s1, f k + ∑ k ∈ Finset.range s2, f (s1 + A + k)
        + ∑ k ∈ Finset.range s3, f (s1 + A + s2 + B + k)) := by
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add,
    Finset.sum_range_add g (A + e) B, Finset.sum_range_add g A e]
  rw [Finset.sum_congr rfl (fun x hx => h1 x (Finset.mem_range.mp hx)),
    Finset.sum_congr rfl (fun x hx => h2 x (Finset.mem_range.mp hx)), ← Finset.mul_sum, ← Finset.mul_sum]
  ring

set_option maxHeartbeats 4000000 in
open OMA.S_oeis_a267812 in
lemma stepd0 (t : ℕ) (h0 : 2 ≤ t) :
    a (t + 1) = 2 ^ 1 * a t + (2 : ℤ) ^ (2 * t + 2) + (2 : ℤ) ^ (0) := by
  have e1 : a (t + 1) = ∑ j ∈ Finset.range (1 + (2 * t + 1) + 1 + (0) + 0), wd (t + 1) j := by
    rw [a_wd, show 2 * (t + 1) + 1 = 1 + (2 * t + 1) + 1 + (0) + 0 from by omega]
  have e2 : a t = ∑ j ∈ Finset.range ((2 * t + 1) + 0 + (0)), wd t j := by
    rw [a_wd, show 2 * t + 1 = (2 * t + 1) + 0 + (0) from by omega]
  rw [e1, e2, sum_cutZ (wd (t + 1)) (wd t) (2 ^ 1) (2 * t + 1) 0 (0) 1 1 0
    (fun j hj => wd_congr _ _ _ _ 1 (((Fph2 (t + 1) _ (by omega)).trans (by omega)).trans (Fph2 t _ (by omega)).symm) (by omega))
    (fun x hx => wd_congr _ _ _ _ 1 (((Fph2 (t + 1) _ (by omega)).trans (by omega)).trans (Fph2 t _ (by omega)).symm) (by omega))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v1 : wd (t + 1) (0) = 2 ^ (2 * t + 2) :=
    (wd_pos _ _ ((Fph2 (t + 1) _ (by omega)).mpr (by omega))).trans
      (congrArg (fun x : ℕ => (2 : ℤ) ^ x) (by omega))
  have v2 : wd (t + 1) (1 + (2 * t + 1) + 0) = 2 ^ (0) :=
    (wd_pos _ _ ((Fph2 (t + 1) _ (by omega)).mpr (by omega))).trans
      (congrArg (fun x : ℕ => (2 : ℤ) ^ x) (by omega))
  rw [v1, v2]
  ring

open OMA.S_oeis_a267812 in
lemma ad0 : a 0 = 1 := by
  rw [a_wd, show 2 * 0 + 1 = 1 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : wd 0 0 = 2 ^ 0 := wd_pos _ _ ((Fph0 0 _ (by omega)).mpr (by omega))
  rw [v0]
  norm_num

open OMA.S_oeis_a267812 in
lemma av0 : (a 0 : ℚ) = 1 := by
  rw [ad0]
  norm_num

open OMA.S_oeis_a267812 in
lemma ad1 : a 1 = 1 := by
  rw [a_wd, show 2 * 1 + 1 = 3 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : wd 1 0 = 0 := wd_zero _ _ (fun h => by
    have h' := (Fph1 1 _ (by omega)).mp h
    omega)
  have v1 : wd 1 1 = 0 := wd_zero _ _ (fun h => by
    have h' := (Fph1 1 _ (by omega)).mp h
    omega)
  have v2 : wd 1 2 = 2 ^ 0 := wd_pos _ _ ((Fph1 1 _ (by omega)).mpr (by omega))
  rw [v0, v1, v2]
  norm_num

open OMA.S_oeis_a267812 in
lemma av1 : (a 1 : ℚ) = 1 := by
  rw [ad1]
  norm_num

open OMA.S_oeis_a267812 in
lemma ad2 : a 2 = 27 := by
  rw [a_wd, show 2 * 2 + 1 = 5 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : wd 2 0 = 2 ^ 4 := wd_pos _ _ ((Fph2 2 _ (by omega)).mpr (by omega))
  have v1 : wd 2 1 = 2 ^ 3 := wd_pos _ _ ((Fph2 2 _ (by omega)).mpr (by omega))
  have v2 : wd 2 2 = 0 := wd_zero _ _ (fun h => by
    have h' := (Fph2 2 _ (by omega)).mp h
    omega)
  have v3 : wd 2 3 = 2 ^ 1 := wd_pos _ _ ((Fph2 2 _ (by omega)).mpr (by omega))
  have v4 : wd 2 4 = 2 ^ 0 := wd_pos _ _ ((Fph2 2 _ (by omega)).mpr (by omega))
  rw [v0, v1, v2, v3, v4]
  norm_num

open OMA.S_oeis_a267812 in
lemma av2 : (a 2 : ℚ) = 27 := by
  rw [ad2]
  norm_num

open OMA.S_oeis_a267812 in
lemma ad3 : a 3 = 119 := by
  rw [a_wd, show 2 * 3 + 1 = 7 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : wd 3 0 = 2 ^ 6 := wd_pos _ _ ((Fph2 3 _ (by omega)).mpr (by omega))
  have v1 : wd 3 1 = 2 ^ 5 := wd_pos _ _ ((Fph2 3 _ (by omega)).mpr (by omega))
  have v2 : wd 3 2 = 2 ^ 4 := wd_pos _ _ ((Fph2 3 _ (by omega)).mpr (by omega))
  have v3 : wd 3 3 = 0 := wd_zero _ _ (fun h => by
    have h' := (Fph2 3 _ (by omega)).mp h
    omega)
  have v4 : wd 3 4 = 2 ^ 2 := wd_pos _ _ ((Fph2 3 _ (by omega)).mpr (by omega))
  have v5 : wd 3 5 = 2 ^ 1 := wd_pos _ _ ((Fph2 3 _ (by omega)).mpr (by omega))
  have v6 : wd 3 6 = 2 ^ 0 := wd_pos _ _ ((Fph2 3 _ (by omega)).mpr (by omega))
  rw [v0, v1, v2, v3, v4, v5, v6]
  norm_num

open OMA.S_oeis_a267812 in
lemma av3 : (a 3 : ℚ) = 119 := by
  rw [ad3]
  norm_num

open OMA.S_oeis_a267812 in
lemma ad4 : a 4 = 495 := by
  rw [a_wd, show 2 * 4 + 1 = 9 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : wd 4 0 = 2 ^ 8 := wd_pos _ _ ((Fph2 4 _ (by omega)).mpr (by omega))
  have v1 : wd 4 1 = 2 ^ 7 := wd_pos _ _ ((Fph2 4 _ (by omega)).mpr (by omega))
  have v2 : wd 4 2 = 2 ^ 6 := wd_pos _ _ ((Fph2 4 _ (by omega)).mpr (by omega))
  have v3 : wd 4 3 = 2 ^ 5 := wd_pos _ _ ((Fph2 4 _ (by omega)).mpr (by omega))
  have v4 : wd 4 4 = 0 := wd_zero _ _ (fun h => by
    have h' := (Fph2 4 _ (by omega)).mp h
    omega)
  have v5 : wd 4 5 = 2 ^ 3 := wd_pos _ _ ((Fph2 4 _ (by omega)).mpr (by omega))
  have v6 : wd 4 6 = 2 ^ 2 := wd_pos _ _ ((Fph2 4 _ (by omega)).mpr (by omega))
  have v7 : wd 4 7 = 2 ^ 1 := wd_pos _ _ ((Fph2 4 _ (by omega)).mpr (by omega))
  have v8 : wd 4 8 = 2 ^ 0 := wd_pos _ _ ((Fph2 4 _ (by omega)).mpr (by omega))
  rw [v0, v1, v2, v3, v4, v5, v6, v7, v8]
  norm_num

open OMA.S_oeis_a267812 in
lemma av4 : (a 4 : ℚ) = 495 := by
  rw [ad4]
  norm_num


open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end CAOEISA267812Aux

set_option maxHeartbeats 4000000 in
open OMA.S_oeis_a267812 CAOEISA267812Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a267812.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    rcases Nat.lt_or_ge n 5 with h | h
    · omega
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
      rw [show m + 5 - 1 = m + 4 from by omega, show m + 5 - 2 = m + 3 from by omega, show m + 5 - 3 = m + 2 from by omega]
      have hz : a (m + 5) = 7 * a (m + 4) - 14 * a (m + 3) + 8 * a (m + 2) := by
        have s0 := stepd0 (m + 2) (by omega)
        have s1 := stepd0 (m + 3) (by omega)
        have s2 := stepd0 (m + 4) (by omega)
        linear_combination (4) * s0 + (-5) * s1 + (1) * s2
      exact_mod_cast hz
  · have hD : (((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X)) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-7) * PowerSeries.X ^ 1 + PowerSeries.C 14 * PowerSeries.X ^ 2 + PowerSeries.C (-8) * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : ((1 - 6 * PowerSeries.X + 34 * PowerSeries.X ^ 2 - 64 * PowerSeries.X ^ 3 + 32 * PowerSeries.X ^ 4) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-6) * PowerSeries.X ^ 1 + PowerSeries.C 34 * PowerSeries.X ^ 2 + PowerSeries.C (-64) * PowerSeries.X ^ 3 + PowerSeries.C 32 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n
      · norm_num [av0]
      · norm_num [av0, av1]
      · norm_num [av0, av1, av2]
      · norm_num [av0, av1, av2, av3]
      · norm_num [av1, av2, av3, av4]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
      rw [if_pos (show 0 ≤ m + 5 from by omega), if_pos (show 1 ≤ m + 5 from by omega), if_pos (show 2 ≤ m + 5 from by omega), if_pos (show 3 ≤ m + 5 from by omega)]
      rw [if_neg (show ¬ (m + 5 = 0) from by omega), if_neg (show ¬ (m + 5 = 1) from by omega), if_neg (show ¬ (m + 5 = 2) from by omega), if_neg (show ¬ (m + 5 = 3) from by omega), if_neg (show ¬ (m + 5 = 4) from by omega)]
      rw [show m + 5 - 3 = m + 2 from by omega, show m + 5 - 2 = m + 3 from by omega, show m + 5 - 1 = m + 4 from by omega, show m + 5 - 0 = m + 5 from by omega]
      have hz : (1) * a (m + 5) + (-7) * a (m + 4) + (14) * a (m + 3) + (-8) * a (m + 2) = 0 := by
        have s0 := stepd0 (m + 2) (by omega)
        have s1 := stepd0 (m + 3) (by omega)
        have s2 := stepd0 (m + 4) (by omega)
        linear_combination (4) * s0 + (-5) * s1 + (1) * s2
      have hq : ((((1) * a (m + 5) + (-7) * a (m + 4) + (14) * a (m + 3) + (-8) * a (m + 2) : ℤ)) : ℚ) = 0 := by
        rw [hz]
        norm_num
      push_cast at hq
      linarith
