import OMAStatements.S_oeis_a273146

open OMA.S_oeis_a273146
open Finset
open scoped BigOperators

namespace Rule597

-- Away from the seed, the configuration depends only on Manhattan distance.
private def radial (t d : ℕ) : Bool :=
  if t = 0 then decide (d = 0)
  else if t ≤ d then true
  else if t % 4 = 0 then decide (d % 4 = 0)
  else if t % 4 = 1 then decide (d % 4 ≠ 0)
  else if t % 4 = 2 then decide (d % 4 = 2)
  else decide (d % 4 ≠ 2)

private theorem center (t : ℕ) :
    (597 : ℕ).testBit ((radial t 0).toNat + 2 * (4 * (radial t 1).toNat)) =
      radial (t + 1) 0 := by
  rcases t with _ | _ | t
  · decide
  · decide
  · have ht : (t + 2) % 4 < 4 := Nat.mod_lt _ (by decide)
    have hh : (t + 2 + 1) % 4 = ((t + 2) % 4 + 1) % 4 := by omega
    interval_cases h : (t + 2) % 4 <;>
      simp [radial, h, hh, show ¬ t + 2 ≤ 1 by omega] <;> decide

private theorem step (t d m : ℕ) (hd : 0 < d) (hm : m = 1 ∨ m = 2)
    (hm' : m = 2 → 2 ≤ d) :
    (597 : ℕ).testBit ((radial t d).toNat + 2 *
      (m * (radial t (d - 1)).toNat + (4 - m) * (radial t (d + 1)).toNat)) =
      radial (t + 1) d := by
  rcases hm with rfl | rfl
  all_goals
    by_cases ht : t = 0
    · subst t
      have hpos : d ≠ 0 := by omega
      have hle : 1 ≤ d := by omega
      by_cases hd' : d - 1 = 0 <;> simp [radial, hpos, hle, hd'] <;> decide
    by_cases hfar : t + 1 ≤ d
    · simp [radial, ht, hfar, show t ≤ d by omega, show t ≤ d - 1 by omega,
        show t ≤ d + 1 by omega] <;> decide
    have ha : t % 4 < 4 := Nat.mod_lt _ (by decide)
    have hb : d % 4 < 4 := Nat.mod_lt _ (by decide)
    have hn : (t + 1) % 4 = (t % 4 + 1) % 4 := by omega
    have hl : (d - 1) % 4 = (d % 4 + 3) % 4 := by omega
    have hr : (d + 1) % 4 = (d % 4 + 1) % 4 := by omega
    interval_cases ht4 : t % 4 <;> interval_cases hd4 : d % 4
    all_goals
      by_cases h0 : t ≤ d <;> by_cases h1 : t ≤ d + 1
      all_goals first | omega | (
        have hh : ¬ t ≤ d - 1 := by omega
        simp [radial, ht, hfar, h0, h1, hh, ht4, hd4, hn, hl, hr] <;> decide)

private theorem absNeighbors (z : ℤ) :
    (z = 0 ∧ (z + 1).natAbs = 1 ∧ (z - 1).natAbs = 1) ∨
    (0 < z.natAbs ∧
      (((z + 1).natAbs = z.natAbs + 1 ∧ (z - 1).natAbs = z.natAbs - 1) ∨
       ((z - 1).natAbs = z.natAbs + 1 ∧ (z + 1).natAbs = z.natAbs - 1))) := by
  rcases lt_trichotomy z 0 with h | rfl | h
  · right
    refine ⟨by omega, Or.inr ⟨?_, ?_⟩⟩ <;> omega
  · decide
  · right
    refine ⟨by omega, Or.inl ⟨?_, ?_⟩⟩ <;> omega

private theorem cell_radial (t : ℕ) (i j : ℤ) :
    cell 597 t i j = radial t (i.natAbs + j.natAbs) := by
  induction t generalizing i j with
  | zero => simp [cell, radial]
  | succ t ih =>
    simp only [cell, ih]
    rcases absNeighbors i with ⟨rfl, hi, hi'⟩ | ⟨hi, hi'⟩ <;>
      rcases absNeighbors j with ⟨rfl, hj, hj'⟩ | ⟨hj, hj'⟩
    · convert center t using 2 <;> simp <;> omega
    · rcases hj' with ⟨hj₁, hj₂⟩ | ⟨hj₁, hj₂⟩ <;>
        simp only [Int.natAbs_zero, hi, hi', hj₁, hj₂, Nat.zero_add] <;>
        rw [show 1 + j.natAbs = j.natAbs + 1 by omega] <;>
        convert step t j.natAbs 1 hj (Or.inl rfl) (by omega) using 2 <;> omega
    · rcases hi' with ⟨hi₁, hi₂⟩ | ⟨hi₁, hi₂⟩ <;>
        simp only [Int.natAbs_zero, hj, hj', hi₁, hi₂, Nat.add_zero] <;>
        convert step t i.natAbs 1 hi (Or.inl rfl) (by omega) using 2 <;> omega
    · rcases hi' with ⟨hi₁, hi₂⟩ | ⟨hi₁, hi₂⟩ <;>
        rcases hj' with ⟨hj₁, hj₂⟩ | ⟨hj₁, hj₂⟩ <;>
        simp only [hi₁, hi₂, hj₁, hj₂] <;>
        (let d := i.natAbs + j.natAbs
         have h1 : i.natAbs + 1 + j.natAbs = d + 1 := by dsimp [d]; omega
         have h3 : i.natAbs + (j.natAbs + 1) = d + 1 := by dsimp [d]; omega
         have h4 : i.natAbs - 1 + j.natAbs = d - 1 := by dsimp [d]; omega
         have h5 : i.natAbs + (j.natAbs - 1) = d - 1 := by dsimp [d]; omega
         simp only [h1, h3, h4, h5]
         convert step t d 2 (by dsimp [d]; omega) (Or.inr rfl) (by dsimp [d]; omega) using 2 <;> dsimp [d] <;> omega)

private theorem sum_signed (t : ℕ) (f : ℕ → ℤ) :
    (∑ i ∈ range (2*t+1), f ((i : ℤ)-t).natAbs) =
    f 0 + 2 * ∑ i ∈ range t, f (i+1) := by
  rw [show 2*t+1 = t+(t+1) by omega, sum_range_add]
  have hleft : (∑ i ∈ range t, f ((i : ℤ)-t).natAbs) =
      ∑ i ∈ range t, f (i+1) := by
    calc
      _ = ∑ i ∈ range t, f ((t-1-i)+1) := by
        apply sum_congr rfl
        intro i hi
        have hi' := mem_range.mp hi
        congr 1
        omega
      _ = _ := sum_range_reflect (fun i => f (i+1)) t
  have hright : (∑ i ∈ range (t+1), f (((t+i : ℕ) : ℤ)-t).natAbs) =
      ∑ i ∈ range (t+1), f i := by
    simp
  rw [hleft, hright, sum_range_succ']
  ring

private theorem sum_triangle (t : ℕ) (f : ℕ → ℤ)
    (hf : ∀ d, t ≤ d → f d = 0) :
    (∑ i ∈ range t, ∑ j ∈ range t, f (i+j)) =
      ∑ d ∈ range t, ((d : ℤ)+1) * f d := by
  induction t generalizing f with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ', sum_range_succ' (fun d => ((d : ℤ)+1) * f d)]
    simp only [Nat.cast_zero, zero_add, one_mul]
    have hshift : (∑ i ∈ range t, ∑ j ∈ range (t+1), f (i+1+j)) =
        ∑ i ∈ range t, ∑ j ∈ range t, (fun d => f (d+1)) (i+j) := by
      apply sum_congr rfl
      intro i hi
      rw [sum_range_succ]
      rw [hf _ (by omega), add_zero]
      apply sum_congr rfl
      intro j hj
      rw [show i+1+j = i+j+1 by omega]
    rw [hshift, ih (fun d => f (d+1)) (by intro d hd; exact hf _ (by omega))]
    rw [sum_range_succ' f, ← add_assoc, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro i hi
    push_cast
    ring

private def weight (d : ℕ) : ℤ := if d = 0 then 1 else 4*d

-- Group the square by Manhattan distance. The support condition makes
-- each nonzero-radius shell complete, with four points per unit of radius.
private theorem sum_diamond (t : ℕ) (f : ℕ → ℤ) (hf : ∀ d, t ≤ d → f d = 0) :
    (∑ i ∈ range (2*t+1), ∑ j ∈ range (2*t+1),
      f (((i : ℤ)-t).natAbs+((j : ℤ)-t).natAbs)) =
      ∑ d ∈ range t, weight d * f d := by
  have hsigned (i : ℕ) := sum_signed t (fun b => f (((i : ℤ)-t).natAbs+b))
  simp_rw [hsigned]
  rw [sum_signed t (fun b => f (b+0)+2*∑ j ∈ range t, f (b+(j+1)))]
  simp only [Nat.add_zero, Nat.zero_add]
  rw [sum_add_distrib, ← mul_sum]
  have hxy : (∑ i ∈ range t, ∑ j ∈ range t, f (i+1+(j+1))) =
      ∑ d ∈ range t, ((d : ℤ)+1) * f (d+2) := by
    rw [← sum_triangle t (fun d => f (d+2)) (by intro d hd; exact hf _ (by omega))]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [show i+1+(j+1) = i+j+2 by omega]
  rw [hxy]
  have hs : (∑ d ∈ range t, ((d : ℤ)+1) * f (d+2)) =
      ∑ d ∈ range t, (d : ℤ) * f (d+1) := by
    let g := fun d : ℕ => (d : ℤ) * f (d+1)
    have e₁ := sum_range_succ' g t
    have e₂ := sum_range_succ g t
    rw [e₂] at e₁
    have hz := hf (t+1) (by omega)
    simp [g, hz] at e₁
    exact e₁.symm
  rw [hs]
  have hweight : (∑ d ∈ range t, weight d * f d) =
      f 0 + ∑ d ∈ range t, (4*((d : ℤ)+1))*f (d+1) := by
    let g := fun d => weight d * f d
    have e₁ := sum_range_succ' g t
    have e₂ := sum_range_succ g t
    rw [e₂] at e₁
    have hzero : g 0 = f 0 := by simp [g, weight]
    have ht : g t = 0 := by simp [g, hf t le_rfl]
    rw [ht, add_zero, hzero, add_comm] at e₁
    simpa only [g, weight, Nat.succ_ne_zero, if_false, Nat.cast_add, Nat.cast_one] using e₁
  rw [hweight]
  have hmul : (∑ d ∈ range t, (4*((d : ℤ)+1))*f (d+1)) =
      4 * ((∑ d ∈ range t, (d : ℤ)*f (d+1)) + ∑ d ∈ range t, f (d+1)) := by
    rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl (fun d _ => by ring)
  rw [hmul]
  ring

private def off (t d : ℕ) : ℤ :=
  if t % 4 = 0 then (if d % 4 = 0 then 0 else 1)
  else if t % 4 = 1 then (if d % 4 = 0 then 1 else 0)
  else if t % 4 = 2 then (if d % 4 = 2 then 0 else 1)
  else (if d % 4 = 2 then 1 else 0)

private def count (t : ℕ) : ℤ :=
  (2*(t : ℤ)+1)^2 - ∑ d ∈ range t, weight d * off t d

private theorem count_eq (t : ℕ) : (onCount 597 t : ℤ) = count t := by
  rcases t with _ | t
  · decide
  · let f := fun d => if d < t+1 then off (t+1) d else 0
    have hf : ∀ d, t+1 ≤ d → f d = 0 := by
      intro d hd
      exact if_neg (Nat.not_lt.mpr hd)
    have hcell (d : ℕ) : (if radial (t+1) d then (1 : ℤ) else 0) = 1 - f d := by
      by_cases hd : d < t+1
      · simp only [radial, f, hd, if_true, Nat.succ_ne_zero, if_false,
          show ¬ t+1 ≤ d by omega]
        by_cases ht0 : (t+1)%4 = 0
        · by_cases h : d%4 = 0 <;> simp [off, ht0, h]
        · by_cases ht1 : (t+1)%4 = 1
          · by_cases h : d%4 = 0 <;> simp [off, ht1, h]
          · by_cases ht2 : (t+1)%4 = 2 <;>
              by_cases h : d%4 = 2 <;> simp [off, ht0, ht1, ht2, h]
      · simp only [radial, f, hd, if_false, Nat.succ_ne_zero, Nat.le_of_not_gt hd,
          if_true, sub_zero]
    unfold onCount count
    push_cast
    simp only [cell_radial, hcell]
    simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
    have hdiamond := sum_diamond (t+1) f hf
    push_cast at hdiamond
    rw [hdiamond]
    have hs : (∑ d ∈ range (t+1), weight d * f d) =
        ∑ d ∈ range (t+1), weight d * off (t+1) d := by
      apply sum_congr rfl
      intro d hd
      simp only [f, if_pos (mem_range.mp hd)]
    rw [hs]
    push_cast
    ring

-- The four-step difference is affine on each parity class of time.
private theorem count_delta (t : ℕ) :
    count (t+4) - count t =
      if t % 2 = 0 then 20*(t : ℤ)+56 else 28*(t : ℤ)+68 := by
  rcases t with _ | t
  · decide
  · have ho (d : ℕ) : off (t+1+4) d = off (t+1) d := by
      simp [off, show (t+1+4)%4 = (t+1)%4 by omega]
    unfold count
    simp only [ho]
    rw [sum_range_add _ (t+1) 4]
    simp only [sum_range_succ, sum_range_zero, zero_add]
    have h0 : (t+1+0)%4 = (t+1)%4 := by omega
    have h1 : (t+1+1)%4 = ((t+1)%4+1)%4 := by omega
    have h2 : (t+1+2)%4 = ((t+1)%4+2)%4 := by omega
    have h3 : (t+1+3)%4 = ((t+1)%4+3)%4 := by omega
    have hp : (t+1)%2 = ((t+1)%4)%2 := by omega
    have ht : (t+1)%4 < 4 := Nat.mod_lt _ (by decide)
    interval_cases h : (t+1)%4 <;>
      norm_num [off, weight, h0, h1, h2, h3, hp, h,
        show t+1+0 ≠ 0 by omega, show t+1+1 ≠ 0 by omega,
        show t+1+2 ≠ 0 by omega, show t+1+3 ≠ 0 by omega] <;> ring

private theorem a_step (t : ℕ) : a (t+1) = a t + count (t+1) := by
  unfold a
  rw [sum_range_succ, count_eq]

private theorem recurrence (n : ℕ) (hn : 9 ≤ n) :
    a n = a (n-1) + 2*a (n-2) - 2*a (n-3) - 2*a (n-6) + 2*a (n-7) + a (n-8) - a (n-9) := by
  let t := n-9
  have he : n = t+9 := by dsimp [t]; omega
  rw [he]
  have h₁ := count_delta (t+1)
  have h₂ := count_delta (t+3)
  have h₃ := count_delta (t+5)
  rw [show (t+3)%2 = (t+1)%2 by omega] at h₂
  rw [show (t+5)%2 = (t+1)%2 by omega] at h₃
  have ha₁ := a_step t
  have ha₃ := a_step (t+2)
  have ha₇ := a_step (t+6)
  have ha₉ := a_step (t+8)
  have hc : count (t+9) - count (t+5) - 2*(count (t+7)-count (t+3)) +
      (count (t+5)-count (t+1)) = 0 := by
    change count (t+5+4) - count (t+5) - 2*(count (t+3+4)-count (t+3)) +
      (count (t+1+4)-count (t+1)) = 0
    rw [h₁,h₂,h₃]
    split <;> push_cast <;> ring
  rw [show t+9-1 = t+8 by omega, show t+9-2 = t+7 by omega,
    show t+9-3 = t+6 by omega, show t+9-6 = t+3 by omega,
    show t+9-7 = t+2 by omega, show t+9-8 = t+1 by omega,
    show t+9-9 = t by omega]
  linarith only [hc, ha₁, ha₃, ha₇, ha₉]

private theorem initial : ∀ n < 9, a n = ([1,9,29,70,127,231,347,540,733] : List ℤ)[n]! := by
  intro n hn
  interval_cases n <;> norm_num [a, count_eq, count, off, weight, sum_range_succ]

open PowerSeries in
private theorem generating :
    (PowerSeries.mk (fun n => (a n : ℚ))) *
      ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 + X ^ 2) : PowerSeries ℚ) =
      1 + 8 * X + 18 * X ^ 2 + 25 * X ^ 3 + 17 * X ^ 4 + 22 * X ^ 5 + 4 * X ^ 6 + X ^ 7 := by
  have hden : ((1 - X)^4 * (1 + X)^3 * (1 + X^2) : PowerSeries ℚ) =
      1-X^1-2*X^2+2*X^3+2*X^6-2*X^7-X^8+X^9 := by ring
  have hnume : (1 + 8 * X + 18 * X ^ 2 + 25 * X ^ 3 + 17 * X ^ 4 +
      22 * X ^ 5 + 4 * X ^ 6 + X ^ 7 : PowerSeries ℚ) =
      1 + (8 : ℕ) • X^1 + (18 : ℕ) • X^2 + (25 : ℕ) • X^3 +
      (17 : ℕ) • X^4 + (22 : ℕ) • X^5 + (4 : ℕ) • X^6 + X^7 := by
    simp [nsmul_eq_mul]
  rw [hden,hnume]
  ext n
  simp only [two_mul, mul_add, mul_sub, mul_one, map_add, map_sub, map_nsmul, coeff_mk,
    coeff_mul_X_pow', coeff_one, coeff_X_pow]
  by_cases hn : 9 ≤ n
  · have hrec := recurrence n hn
    have hr : (a n : ℚ) = a (n-1) + 2*a (n-2) - 2*a (n-3) -
        2*a (n-6) + 2*a (n-7) + a (n-8) - a (n-9) := by exact_mod_cast hrec
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
      show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      show n ≠ 6 by omega, show n ≠ 7 by omega, show 1 ≤ n by omega,
      show 2 ≤ n by omega, show 3 ≤ n by omega, show 6 ≤ n by omega,
      show 7 ≤ n by omega, show 8 ≤ n by omega, hn]
    linarith only [hr]
  · interval_cases n <;> norm_num [initial]

end Rule597

theorem OMA.solution : type_of% @OMA.S_oeis_a273146.main := by
  refine ⟨?_, Rule597.generating⟩
  intro n hn
  exact_mod_cast Rule597.recurrence n hn
