import OMAStatements.S_oeis_a270454
import Mathlib

namespace A270454Aux

lemma toNat_spec (x : Bool) : (x.toNat = 0 ∧ x = false) ∨ (x.toNat = 1 ∧ x = true) := by
  cases x <;> simp

/-- Lattice points of the diamond of radius `t` in the parity class of `t`, inside the window. -/
lemma cntD (t : ℕ) :
    ((Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1)).filter (fun p : ℕ × ℕ =>
      ((p.1 : ℤ) - t) + ((p.2 : ℤ) - t) ≤ t ∧ ((p.1 : ℤ) - t) - ((p.2 : ℤ) - t) ≤ t ∧
      ((p.2 : ℤ) - t) - ((p.1 : ℤ) - t) ≤ t ∧ -((p.1 : ℤ) - t) - ((p.2 : ℤ) - t) ≤ t ∧
      (((p.1 : ℤ) - t) + ((p.2 : ℤ) - t) + t) % 2 = 0)).card = (t + 1) * (t + 1) := by
  have hc : (Finset.range (t + 1) ×ˢ Finset.range (t + 1)).card = (t + 1) * (t + 1) := by
    rw [Finset.card_product, Finset.card_range]
  rw [← hc]
  refine Finset.card_bij' (fun (p : ℕ × ℕ) _ => ((p.1 + p.2 - t) / 2, (p.1 + t - p.2) / 2))
    (fun (q : ℕ × ℕ) _ => (q.1 + q.2, q.1 + t - q.2)) ?_ ?_ ?_ ?_
  · rintro ⟨I, J⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  · rintro ⟨u, v⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq ⊢
    omega
  · rintro ⟨I, J⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨u, v⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
    simp only [Prod.mk.injEq]
    omega

/-- The diamond of radius `t` in the parity class of `t`. -/
def D (t : ℕ) (i j : ℤ) : Prop :=
  i + j ≤ t ∧ i - j ≤ t ∧ j - i ≤ t ∧ -i - j ≤ t ∧ (i + j + t) % 2 = 0

/-- Closed form of the stages of Rule 163 as a proposition. -/
def P (t : ℕ) (i j : ℤ) : Prop := (t % 2 = 1 ∧ ¬D t i j) ∨ (t % 2 = 0 ∧ D t i j)

/-- Closed form of the stages of Rule 163 as a Boolean. -/
def Fb (t : ℕ) (i j : ℤ) : Bool :=
  decide ((t % 2 = 1 ∧ ¬(i + j ≤ t ∧ i - j ≤ t ∧ j - i ≤ t ∧ -i - j ≤ t ∧ (i + j + t) % 2 = 0)) ∨
  (t % 2 = 0 ∧ (i + j ≤ t ∧ i - j ≤ t ∧ j - i ≤ t ∧ -i - j ≤ t ∧ (i + j + t) % 2 = 0)))

lemma Fb_iff (t : ℕ) (i j : ℤ) : Fb t i j = true ↔ P t i j := by
  unfold Fb P D
  exact decide_eq_true_iff

lemma bool_out (t : ℕ) (i j : ℤ) (h : ¬D t i j) : Fb t i j = decide (t % 2 = 1) := by
  rw [Bool.eq_iff_iff, Fb_iff, decide_eq_true_eq]
  unfold P
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · exact h1
    · exact absurd h2 h
  · intro h1
    exact Or.inl ⟨h1, h⟩

lemma bool_in (t : ℕ) (i j : ℤ) (h : D t i j) : Fb t i j = decide (t % 2 = 0) := by
  rw [Bool.eq_iff_iff, Fb_iff, decide_eq_true_eq]
  unfold P
  constructor
  · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
    · exact absurd h h2
    · exact h1
  · intro h1
    exact Or.inr ⟨h1, h⟩

set_option maxHeartbeats 4000000 in
open OMA.S_oeis_a270454 in
lemma cellF (t : ℕ) : ∀ i j : ℤ, cell 163 t i j = Fb t i j := by
  induction t with
  | zero =>
    intro i j
    show decide (i = 0 ∧ j = 0) = Fb 0 i j
    unfold Fb
    apply decide_eq_decide.mpr
    omega
  | succ t ih =>
    intro i j
    show Nat.testBit 163 ((cell 163 t i j).toNat + 2 * ((cell 163 t (i + 1) j).toNat +
      (cell 163 t (i - 1) j).toNat + (cell 163 t i (j + 1)).toNat +
      (cell 163 t i (j - 1)).toNat)) = Fb (t + 1) i j
    rw [ih i j, ih (i + 1) j, ih (i - 1) j, ih i (j + 1), ih i (j - 1)]
    rcases Int.emod_two_eq_zero_or_one (i + j + t) with hpar | hpar
    · have n1 : ¬D t (i + 1) j := by unfold D; omega
      have n2 : ¬D t (i - 1) j := by unfold D; omega
      have n3 : ¬D t i (j + 1) := by unfold D; omega
      have n4 : ¬D t i (j - 1) := by unfold D; omega
      have n5 : ¬D (t + 1) i j := by unfold D; omega
      rw [bool_out _ _ _ n1, bool_out _ _ _ n2, bool_out _ _ _ n3, bool_out _ _ _ n4,
        bool_out _ _ _ n5]
      by_cases d0 : D t i j
      · rw [bool_in _ _ _ d0]
        rcases Nat.mod_two_eq_zero_or_one t with ht | ht
        · rw [ht, show (t + 1) % 2 = 1 from by omega]
          decide
        · rw [ht, show (t + 1) % 2 = 0 from by omega]
          decide
      · rw [bool_out _ _ _ d0]
        rcases Nat.mod_two_eq_zero_or_one t with ht | ht
        · rw [ht, show (t + 1) % 2 = 1 from by omega]
          decide
        · rw [ht, show (t + 1) % 2 = 0 from by omega]
          decide
    · have n0 : ¬D t i j := by unfold D; omega
      rw [bool_out _ _ _ n0]
      by_cases d1 : D t (i + 1) j <;> by_cases d2 : D t (i - 1) j <;>
        by_cases d3 : D t i (j + 1) <;> by_cases d4 : D t i (j - 1) <;>
        by_cases d5 : D (t + 1) i j <;>
        (first | rw [bool_in _ _ _ d1] | rw [bool_out _ _ _ d1]) <;>
        (first | rw [bool_in _ _ _ d2] | rw [bool_out _ _ _ d2]) <;>
        (first | rw [bool_in _ _ _ d3] | rw [bool_out _ _ _ d3]) <;>
        (first | rw [bool_in _ _ _ d4] | rw [bool_out _ _ _ d4]) <;>
        (first | rw [bool_in _ _ _ d5] | rw [bool_out _ _ _ d5]) <;>
        rcases Nat.mod_two_eq_zero_or_one t with ht | ht <;>
        (first
          | (rw [ht, show (t + 1) % 2 = 1 from by omega]; decide)
          | (rw [ht, show (t + 1) % 2 = 0 from by omega]; decide)
          | (exfalso; unfold D at *; omega))

open OMA.S_oeis_a270454 in
lemma on_card (t : ℕ) : onCount 163 t =
    ((Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1)).filter (fun p : ℕ × ℕ =>
      Fb t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t) = true)).card := by
  unfold onCount
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cellF]

open OMA.S_oeis_a270454 in
lemma on_even (t : ℕ) (hp : t % 2 = 0) : onCount 163 t = (t + 1) * (t + 1) := by
  rw [on_card, ← cntD t]
  congr 1
  apply Finset.filter_congr
  rintro ⟨I, J⟩ hp'
  simp only [Fb, decide_eq_true_eq]
  omega

open OMA.S_oeis_a270454 in
lemma on_odd (t : ℕ) (hp : t % 2 = 1) :
    onCount 163 t + (t + 1) * (t + 1) = (2 * t + 1) * (2 * t + 1) := by
  rw [on_card, ← cntD t]
  have hc := Finset.card_filter_add_card_filter_not
    (s := Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1))
    (fun p : ℕ × ℕ => ((p.1 : ℤ) - t) + ((p.2 : ℤ) - t) ≤ t ∧
      ((p.1 : ℤ) - t) - ((p.2 : ℤ) - t) ≤ t ∧
      ((p.2 : ℤ) - t) - ((p.1 : ℤ) - t) ≤ t ∧ -((p.1 : ℤ) - t) - ((p.2 : ℤ) - t) ≤ t ∧
      (((p.1 : ℤ) - t) + ((p.2 : ℤ) - t) + t) % 2 = 0)
  rw [Finset.card_product, Finset.card_range] at hc
  have e : (Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1)).filter (fun p : ℕ × ℕ =>
      Fb t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t) = true) =
      (Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1)).filter (fun p : ℕ × ℕ =>
        ¬(((p.1 : ℤ) - t) + ((p.2 : ℤ) - t) ≤ t ∧ ((p.1 : ℤ) - t) - ((p.2 : ℤ) - t) ≤ t ∧
        ((p.2 : ℤ) - t) - ((p.1 : ℤ) - t) ≤ t ∧ -((p.1 : ℤ) - t) - ((p.2 : ℤ) - t) ≤ t ∧
        (((p.1 : ℤ) - t) + ((p.2 : ℤ) - t) + t) % 2 = 0)) := by
    apply Finset.filter_congr
    rintro ⟨I, J⟩ hp'
    simp only [Fb, decide_eq_true_eq]
    omega
  rw [e]
  omega

open OMA.S_oeis_a270454 in
lemma onQ0 (t : ℕ) (h0 : 0 ≤ t) (hp : t % 2 = 0) :
    ((onCount 163 t : ℤ) : ℚ) = ((t : ℚ) + 1) ^ 2 := by
  rw [on_even t hp]
  push_cast
  ring

open OMA.S_oeis_a270454 in
lemma onQ1 (t : ℕ) (h0 : 1 ≤ t) (hp : t % 2 = 1) :
    ((onCount 163 t : ℤ) : ℚ) = (2 * (t : ℚ) + 1) ^ 2 - ((t : ℚ) + 1) ^ 2 := by
  have h := on_odd t hp
  have h2 : ((onCount 163 t : ℤ) : ℚ) + ((t : ℚ) + 1) * ((t : ℚ) + 1) =
      (2 * (t : ℚ) + 1) * (2 * (t : ℚ) + 1) := by
    exact_mod_cast h
  linarith


open OMA.S_oeis_a270454 in
lemma aC0 (n : ℕ) (h0 : 0 ≤ n) (hp : n % 2 = 0) : (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + (2 : ℚ) * (n : ℚ) + (1 : ℚ) := by
  unfold a
  rw [onQ0 n (by omega) hp]
  ring

open OMA.S_oeis_a270454 in
lemma aC1 (n : ℕ) (h0 : 1 ≤ n) (hp : n % 2 = 1) : (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (3 : ℚ) * (n : ℚ) ^ 2 + (2 : ℚ) * (n : ℚ) + (0 : ℚ) := by
  unfold a
  rw [onQ1 n (by omega) hp]
  ring

open OMA.S_oeis_a270454 in
lemma av0 : (a 0 : ℚ) = 1 := by
  rw [aC0 0 (by norm_num) (by norm_num)]
  norm_num

open OMA.S_oeis_a270454 in
lemma av1 : (a 1 : ℚ) = 5 := by
  rw [aC1 1 (by norm_num) (by norm_num)]
  norm_num

open OMA.S_oeis_a270454 in
lemma av2 : (a 2 : ℚ) = 9 := by
  rw [aC0 2 (by norm_num) (by norm_num)]
  norm_num

open OMA.S_oeis_a270454 in
lemma av3 : (a 3 : ℚ) = 33 := by
  rw [aC1 3 (by norm_num) (by norm_num)]
  norm_num

open OMA.S_oeis_a270454 in
lemma av4 : (a 4 : ℚ) = 25 := by
  rw [aC0 4 (by norm_num) (by norm_num)]
  norm_num

open OMA.S_oeis_a270454 in
lemma av5 : (a 5 : ℚ) = 85 := by
  rw [aC1 5 (by norm_num) (by norm_num)]
  norm_num

open OMA.S_oeis_a270454 in
lemma av6 : (a 6 : ℚ) = 49 := by
  rw [aC0 6 (by norm_num) (by norm_num)]
  norm_num

open OMA.S_oeis_a270454 in
lemma rec_gen (m : ℕ) : (1 : ℚ) * (a (m + 7) : ℚ) + (-3 : ℚ) * (a (m + 5) : ℚ) + (3 : ℚ) * (a (m + 3) : ℚ) + (-1 : ℚ) * (a (m + 1) : ℚ) = 0 := by
  rcases (show m % 2 = 0 ∨ m % 2 = 1 by omega) with h | h
  · rw [aC1 (m + 7) (by omega) (by omega),
      aC1 (m + 5) (by omega) (by omega),
      aC1 (m + 3) (by omega) (by omega),
      aC1 (m + 1) (by omega) (by omega)]
    push_cast
    ring
  · rw [aC0 (m + 7) (by omega) (by omega),
      aC0 (m + 5) (by omega) (by omega),
      aC0 (m + 3) (by omega) (by omega),
      aC0 (m + 1) (by omega) (by omega)]
    push_cast
    ring

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A270454Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a270454 A270454Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a270454.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rcases Nat.lt_or_ge n 1 with hs | hs
    · interval_cases n <;> norm_num [av0, av1, av2, av3, av4, av5, av6]
    · rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h
      · have h1 : (-1 : ℚ) ^ n = 1 := Even.neg_one_pow (by rw [Nat.even_iff]; omega)
        rw [aC0 n (by omega) h]
        rw [h1]
        ring
      · have h1 : (-1 : ℚ) ^ n = -1 := Odd.neg_one_pow (by rw [Nat.odd_iff]; omega)
        rw [aC1 n (by omega) h]
        rw [h1]
        ring
  · intro n hpar
    rcases Nat.lt_or_ge n 1 with hs | hs
    · interval_cases n <;> first | (exfalso; revert hpar; decide) | norm_num [av0, av1, av2, av3, av4, av5, av6]
    · rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h
      · have h1 : (-1 : ℚ) ^ n = 1 := Even.neg_one_pow (by rw [Nat.even_iff]; omega)
        rw [aC0 n (by omega) h]
        ring
      · exfalso
        obtain ⟨k, hk⟩ := hpar
        omega
  · intro n hpar
    rcases Nat.lt_or_ge n 1 with hs | hs
    · interval_cases n <;> first | (exfalso; revert hpar; decide) | norm_num [av0, av1, av2, av3, av4, av5, av6]
    · rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h
      · exfalso
        obtain ⟨k, hk⟩ := hpar
        omega
      · have h1 : (-1 : ℚ) ^ n = -1 := Odd.neg_one_pow (by rw [Nat.odd_iff]; omega)
        rw [aC1 n (by omega) h]
        ring
  · intro n hn
    rcases Nat.lt_or_ge n 7 with hs | hs
    · interval_cases n <;> norm_num [av0, av1, av2, av3, av4, av5, av6]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
      rw [show j + 6 - 2 = j + 4 from by omega, show j + 6 - 4 = j + 2 from by omega, show j + 6 - 6 = j from by omega]
      rcases (show j % 2 = 0 ∨ j % 2 = 1 by omega) with h | h
      · rw [aC0 (j + 6) (by omega) (by omega), aC0 (j + 4) (by omega) (by omega), aC0 (j + 2) (by omega) (by omega), aC0 (j) (by omega) (by omega)]
        push_cast
        ring
      · rw [aC1 (j + 6) (by omega) (by omega), aC1 (j + 4) (by omega) (by omega), aC1 (j + 2) (by omega) (by omega), aC1 (j) (by omega) (by omega)]
        push_cast
        ring
  · have hD : (((1 - X) ^ 3 * (1 + X) ^ 3 : PowerSeries ℚ)) = C (1 : ℚ) * X ^ 0 + C (-3 : ℚ) * X ^ 2 + C (3 : ℚ) * X ^ 4 + C (-1 : ℚ) * X ^ 6 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : (1 + 5 * X + 6 * X ^ 2 + 18 * X ^ 3 + X ^ 4 + X ^ 5 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (5 : ℚ) * X ^ 1 + C (6 : ℚ) * X ^ 2 + C (18 : ℚ) * X ^ 3 + C (1 : ℚ) * X ^ 4 + C (1 : ℚ) * X ^ 5 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 7 with hs | hs
    · interval_cases n <;> norm_num [av0, av1, av2, av3, av4, av5, av6]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
      rw [if_pos (show 0 ≤ m + 7 by omega),
        if_pos (show 2 ≤ m + 7 by omega),
        if_pos (show 4 ≤ m + 7 by omega),
        if_pos (show 6 ≤ m + 7 by omega),
        if_neg (show ¬ (m + 7 = 0) by omega),
        if_neg (show ¬ (m + 7 = 1) by omega),
        if_neg (show ¬ (m + 7 = 2) by omega),
        if_neg (show ¬ (m + 7 = 3) by omega),
        if_neg (show ¬ (m + 7 = 4) by omega),
        if_neg (show ¬ (m + 7 = 5) by omega)]
      rw [show m + 7 - 2 = m + 5 from by omega,
        show m + 7 - 4 = m + 3 from by omega,
        show m + 7 - 6 = m + 1 from by omega]
      rw [show m + 7 - 0 = m + 7 from by omega]
      have hrec := rec_gen m
      linarith
