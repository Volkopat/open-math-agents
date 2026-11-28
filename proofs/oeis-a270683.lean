import OMAStatements.S_oeis_a270683
import Mathlib
/-!
Proof of the conjectures of the statement oeis-a270683 (OEIS A270683), Rule 190.

Method: stage t of the automaton is described exactly by an explicit region of the plane
(defined by linear inequalities and a parity condition); one step of the rule maps the description
at t to the one at t + 1 (a case split on the five cells of the neighbourhood, closed by omega).
The ON cells of the square are then counted row by row in closed form, and every conjecture
reduces to a polynomial identity in n and (-1)^n.
-/

namespace OMA.CA_a270683

open OMA.S_oeis_a270683 PowerSeries

def nxt (code : ℕ) (g : ℤ → ℤ → Bool) : ℤ → ℤ → Bool := fun i j =>
  code.testBit ((g i j).toNat + 2 * ((g (i + 1) j).toNat + (g (i - 1) j).toNat +
    (g i (j + 1)).toNat + (g i (j - 1)).toNat))

theorem cell_succ (code t : ℕ) : cell code (t + 1) = nxt code (cell code t) := by
  funext i j
  rfl

/-- The diamond `|x| + |y| ≤ t`. -/
abbrev Dm (t : ℕ) (x y : ℤ) : Prop :=
  x + y ≤ t ∧ x - y ≤ t ∧ -x + y ≤ t ∧ -x - y ≤ t

/-- The even cells of the smaller diamond `|x| + |y| ≤ t - 2`. -/
abbrev Ev (t : ℕ) (x y : ℤ) : Prop :=
  x + y + 2 ≤ t ∧ x - y + 2 ≤ t ∧ -x + y + 2 ≤ t ∧ -x - y + 2 ≤ t ∧ (x + y) % 2 = 0

/-- Stage `t` of Rule 190: the diamond of radius `t` without the even cells at distance at most `t - 2`. -/
def F (t : ℕ) (x y : ℤ) : Bool := decide (Dm t x y ∧ ¬ Ev t x y)

set_option maxHeartbeats 4000000 in
theorem stepF (t : ℕ) (x y : ℤ) : nxt 190 (F t) x y = F (t + 1) x y := by
  simp only [nxt]
  cases h0 : F t x y <;> cases h1 : F t (x + 1) y <;> cases h2 : F t (x - 1) y <;>
    cases h3 : F t x (y + 1) <;> cases h4 : F t x (y - 1) <;>
    simp only [F, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true,
      Bool.toNat_false, Nat.testBit_eq_decide_div_mod_eq] at h0 h1 h2 h3 h4 ⊢ <;>
    norm_num <;> push_cast at * <;> omega

theorem cellF (t : ℕ) : cell 190 t = F t := by
  induction t with
  | zero =>
    funext x y
    show decide (x = 0 ∧ y = 0) = F 0 x y
    simp only [F]
    apply decide_eq_decide.mpr
    push_cast
    constructor
    · rintro ⟨rfl, rfl⟩
      simp only [Dm, Ev]
      omega
    · intro h
      simp only [Dm, Ev] at h
      omega
  | succ t ih =>
    rw [cell_succ, ih]
    funext x y
    exact stepF t x y

/-- A sum over the rows `i < 2t+1` of a function of `|i - t|`. -/
theorem symsum (t : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range (2 * t + 1), f ((t - i) + (i - t)) =
      f 0 + 2 * ∑ k ∈ Finset.range t, f (k + 1) := by
  rw [show 2 * t + 1 = (t + 1) + t by ring, Finset.sum_range_add, Finset.sum_range_succ]
  have h1 : ∑ x ∈ Finset.range t, f ((t - x) + (x - t)) = ∑ k ∈ Finset.range t, f (k + 1) := by
    rw [← Finset.sum_range_reflect (fun k => f (k + 1)) t]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have := Finset.mem_range.mp hx
    congr 1
    omega
  have h2 : ∑ x ∈ Finset.range t, f ((t - (t + 1 + x)) + (t + 1 + x - t)) =
      ∑ k ∈ Finset.range t, f (k + 1) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    omega
  rw [h1, h2, show (t - t) + (t - t) = 0 by omega]
  ring

theorem cntAll (lo hi N : ℕ) :
    ∑ j ∈ Finset.range N, (if lo ≤ j ∧ j ≤ hi then 1 else 0) = max (min N (hi + 1)) lo - lo := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

/-- The number of `j < N` with `lo ≤ j ≤ hi` and `j % 2 = p`. -/
def cntc (lo hi p N : ℕ) : ℕ := (max (min N (hi + 1)) lo + 1 - p) / 2 - (lo + 1 - p) / 2

theorem cnt (lo hi p N : ℕ) (hp : p < 2) :
    ∑ j ∈ Finset.range N, (if lo ≤ j ∧ j ≤ hi ∧ j % 2 = p then 1 else 0) = cntc lo hi p N := by
  induction N with
  | zero => simp only [cntc, Finset.range_zero, Finset.sum_empty]; omega
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [cntc]
    split_ifs <;> omega

theorem rowDm (t i : ℕ) (hi : i < 2 * t + 1) :
    ∑ j ∈ Finset.range (2 * t + 1), (if Dm t ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0) =
      2 * t + 1 - 2 * ((t - i) + (i - t)) := by
  rw [show 2 * t + 1 - 2 * ((t - i) + (i - t)) =
      max (min (2 * t + 1) (2 * t - ((t - i) + (i - t)) + 1)) ((t - i) + (i - t)) - ((t - i) + (i - t)) by
    omega, ← cntAll]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)

theorem cval (lo t p : ℕ) (h1 : lo + 2 ≤ t) (hp : p = (lo + t) % 2) :
    cntc (lo + 2) (2 * t - 2 - lo) p (2 * t + 1) = t - 1 - lo - t % 2 := by
  have hmx : max (min (2 * t + 1) (2 * t - 2 - lo + 1)) (lo + 2) = 2 * t - 2 - lo + 1 := by omega
  simp only [cntc, hmx]
  subst hp
  omega

theorem rowEv (t i : ℕ) (hi : i < 2 * t + 1) :
    ∑ j ∈ Finset.range (2 * t + 1), (if Ev t ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0) =
      t - 1 - ((t - i) + (i - t)) - t % 2 := by
  by_cases hb : (t - i) + (i - t) + 2 ≤ t
  · rw [← cval ((t - i) + (i - t)) t (i % 2) hb (by omega), ← cnt _ _ _ _ (by omega)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
  · rw [show t - 1 - ((t - i) + (i - t)) - t % 2 = 0 by omega]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [if_neg]
    omega

theorem odd_sum (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem countDm (t : ℕ) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if Dm t ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0) = 2 * t ^ 2 + 2 * t + 1 := by
  rw [Finset.sum_congr rfl (fun i hi => rowDm t i (Finset.mem_range.mp hi))]
  rw [symsum t (fun k => 2 * t + 1 - 2 * k)]
  have h : ∑ k ∈ Finset.range t, (2 * t + 1 - 2 * (k + 1)) = t ^ 2 := by
    rw [← odd_sum t, ← Finset.sum_range_reflect (fun k => 2 * k + 1) t]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have := Finset.mem_range.mp hk
    omega
  rw [h]
  simp only [mul_zero, Nat.sub_zero]
  ring

theorem tri_sum (u n : ℕ) (hu : u ≤ n) :
    2 * ∑ k ∈ Finset.range n, (u - 1 - k) = u * (u - 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hu
  rw [Finset.sum_range_add]
  have hz : ∑ x ∈ Finset.range d, (u - 1 - (u + x)) = 0 := Finset.sum_eq_zero (fun x _ => by omega)
  rw [hz, add_zero]
  have hr := Finset.sum_range_reflect (fun k : ℕ => k) u
  try simp only at hr
  rw [hr, mul_comm, Finset.sum_range_id_mul_two]

theorem countEv (t : ℕ) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if Ev t ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0) = (t - 1 - t % 2) ^ 2 := by
  rw [Finset.sum_congr rfl (fun i hi => rowEv t i (Finset.mem_range.mp hi))]
  rw [symsum t (fun k => t - 1 - k - t % 2)]
  have e : ∑ k ∈ Finset.range t, (t - 1 - (k + 1) - t % 2) =
      ∑ k ∈ Finset.range t, ((t - 1 - t % 2) - 1 - k) :=
    Finset.sum_congr rfl (fun k _ => by omega)
  rw [e, tri_sum _ _ (by omega)]
  simp only [Nat.sub_zero]
  rcases Nat.eq_zero_or_pos (t - 1 - t % 2) with h | h
  · simp [h]
  · obtain ⟨v, hv⟩ : ∃ v, t - 1 - t % 2 = v + 1 := ⟨t - 1 - t % 2 - 1, by omega⟩
    rw [hv, Nat.add_sub_cancel]
    ring

theorem ind_diff (P Q : Prop) [Decidable P] [Decidable Q] (h : Q → P) :
    ((if decide (P ∧ ¬Q) = true then 1 else 0 : ℕ) : ℤ) =
      ((if P then 1 else 0 : ℕ) : ℤ) - ((if Q then 1 else 0 : ℕ) : ℤ) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
  exact hP (h hQ)

theorem cnt190 (t : ℕ) :
    (onCount 190 t : ℤ) = 2 * (t : ℤ) ^ 2 + 2 * t + 1 - ((t - 1 - t % 2 : ℕ) : ℤ) ^ 2 := by
  have hs : (onCount 190 t : ℤ) =
      ((∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
        (if Dm t ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0) : ℕ) : ℤ) -
      ((∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
        (if Ev t ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0) : ℕ) : ℤ) := by
    simp only [onCount, cellF, F, Nat.cast_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact ind_diff _ _ (fun h => by omega)
  rw [hs, countDm, countEv]
  push_cast
  ring

theorem cE (m : ℕ) (hm : 1 ≤ m) :
    (onCount 190 (2 * m) : ℚ) = 2 * (2 * (m : ℚ)) ^ 2 + 2 * (2 * (m : ℚ)) + 1 - (2 * (m : ℚ) - 1) ^ 2 := by
  have h := cnt190 (2 * m)
  rw [show 2 * m - 1 - 2 * m % 2 = 2 * m - 1 by omega] at h
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast [Nat.cast_sub (show 1 ≤ 2 * m by omega)] at hq
  rw [hq]

theorem cO (m : ℕ) (hm : 1 ≤ m) :
    (onCount 190 (2 * m + 1) : ℚ) =
      2 * (2 * (m : ℚ) + 1) ^ 2 + 2 * (2 * (m : ℚ) + 1) + 1 - (2 * (m : ℚ) - 1) ^ 2 := by
  have h := cnt190 (2 * m + 1)
  rw [show 2 * m + 1 - 1 - (2 * m + 1) % 2 = 2 * m - 1 by omega] at h
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast [Nat.cast_sub (show 1 ≤ 2 * m by omega)] at hq
  rw [hq]

theorem cV0 : (onCount 190 0 : ℚ) = 1 := by
  have h := cnt190 0
  norm_num at h
  exact_mod_cast h

theorem cV1 : (onCount 190 1 : ℚ) = 5 := by
  have h := cnt190 1
  norm_num at h
  exact_mod_cast h

theorem cV2 : (onCount 190 2 : ℚ) = 12 := by
  rw [show (2 : ℕ) = 2 * 1 by norm_num, cE 1 (by norm_num)]
  try norm_num

theorem cV3 : (onCount 190 3 : ℚ) = 24 := by
  rw [show (3 : ℕ) = 2 * 1 + 1 by norm_num, cO 1 (by norm_num)]
  try norm_num

theorem cV4 : (onCount 190 4 : ℚ) = 32 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, cE 2 (by norm_num)]
  try norm_num

theorem cV5 : (onCount 190 5 : ℚ) = 52 := by
  rw [show (5 : ℕ) = 2 * 2 + 1 by norm_num, cO 2 (by norm_num)]
  try norm_num

theorem cV6 : (onCount 190 6 : ℚ) = 60 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, cE 3 (by norm_num)]
  try norm_num

theorem cV7 : (onCount 190 7 : ℚ) = 88 := by
  rw [show (7 : ℕ) = 2 * 3 + 1 by norm_num, cO 3 (by norm_num)]
  try norm_num

theorem cV8 : (onCount 190 8 : ℚ) = 96 := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num, cE 4 (by norm_num)]
  try norm_num

theorem cV9 : (onCount 190 9 : ℚ) = 132 := by
  rw [show (9 : ℕ) = 2 * 4 + 1 by norm_num, cO 4 (by norm_num)]
  try norm_num

theorem cV10 : (onCount 190 10 : ℚ) = 140 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num, cE 5 (by norm_num)]
  try norm_num

theorem cV11 : (onCount 190 11 : ℚ) = 184 := by
  rw [show (11 : ℕ) = 2 * 5 + 1 by norm_num, cO 5 (by norm_num)]
  try norm_num

theorem cV12 : (onCount 190 12 : ℚ) = 192 := by
  rw [show (12 : ℕ) = 2 * 6 by norm_num, cE 6 (by norm_num)]
  try norm_num

theorem cV13 : (onCount 190 13 : ℚ) = 244 := by
  rw [show (13 : ℕ) = 2 * 6 + 1 by norm_num, cO 6 (by norm_num)]
  try norm_num

theorem cV14 : (onCount 190 14 : ℚ) = 252 := by
  rw [show (14 : ℕ) = 2 * 7 by norm_num, cE 7 (by norm_num)]
  try norm_num

theorem cV15 : (onCount 190 15 : ℚ) = 312 := by
  rw [show (15 : ℕ) = 2 * 7 + 1 by norm_num, cO 7 (by norm_num)]
  try norm_num

theorem cV16 : (onCount 190 16 : ℚ) = 320 := by
  rw [show (16 : ℕ) = 2 * 8 by norm_num, cE 8 (by norm_num)]
  try norm_num

theorem cV17 : (onCount 190 17 : ℚ) = 388 := by
  rw [show (17 : ℕ) = 2 * 8 + 1 by norm_num, cO 8 (by norm_num)]
  try norm_num

theorem cV18 : (onCount 190 18 : ℚ) = 396 := by
  rw [show (18 : ℕ) = 2 * 9 by norm_num, cE 9 (by norm_num)]
  try norm_num

theorem cV19 : (onCount 190 19 : ℚ) = 472 := by
  rw [show (19 : ℕ) = 2 * 9 + 1 by norm_num, cO 9 (by norm_num)]
  try norm_num

def G (n : ℕ) : ℚ := (((3 : ℚ) / 2) * (n : ℚ) ^ 0 + ((7 : ℚ) / 6) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 2 + ((1 : ℚ) / 3) * (n : ℚ) ^ 3) + (-1 : ℚ) ^ n * (((1 : ℚ) / 2) * (n : ℚ) ^ 0 + ((-1 : ℚ) / 2) * (n : ℚ) ^ 1)

theorem a_succ (n : ℕ) : (a (n + 1) : ℚ) = a n + (onCount 190 (n + 1) : ℚ) := by
  simp only [a]
  rw [Finset.sum_range_succ]
  push_cast
  ring

theorem aV0 : (a 0 : ℚ) = 1 := by
  simp only [a, Finset.sum_range_one]
  exact cV0

theorem aV1 : (a 1 : ℚ) = 6 := by
  rw [a_succ, aV0, cV1]
  norm_num

theorem aV2 : (a 2 : ℚ) = 18 := by
  rw [a_succ, aV1, cV2]
  norm_num

theorem aV3 : (a 3 : ℚ) = 42 := by
  rw [a_succ, aV2, cV3]
  norm_num

theorem aV4 : (a 4 : ℚ) = 74 := by
  rw [a_succ, aV3, cV4]
  norm_num

theorem aV5 : (a 5 : ℚ) = 126 := by
  rw [a_succ, aV4, cV5]
  norm_num

theorem aV6 : (a 6 : ℚ) = 186 := by
  rw [a_succ, aV5, cV6]
  norm_num

theorem aV7 : (a 7 : ℚ) = 274 := by
  rw [a_succ, aV6, cV7]
  norm_num

theorem aV8 : (a 8 : ℚ) = 370 := by
  rw [a_succ, aV7, cV8]
  norm_num

theorem aV9 : (a 9 : ℚ) = 502 := by
  rw [a_succ, aV8, cV9]
  norm_num

theorem aV10 : (a 10 : ℚ) = 642 := by
  rw [a_succ, aV9, cV10]
  norm_num

theorem aV11 : (a 11 : ℚ) = 826 := by
  rw [a_succ, aV10, cV11]
  norm_num

theorem aV12 : (a 12 : ℚ) = 1018 := by
  rw [a_succ, aV11, cV12]
  norm_num

theorem aV13 : (a 13 : ℚ) = 1262 := by
  rw [a_succ, aV12, cV13]
  norm_num

theorem aV14 : (a 14 : ℚ) = 1514 := by
  rw [a_succ, aV13, cV14]
  norm_num

theorem aV15 : (a 15 : ℚ) = 1826 := by
  rw [a_succ, aV14, cV15]
  norm_num

theorem aV16 : (a 16 : ℚ) = 2146 := by
  rw [a_succ, aV15, cV16]
  norm_num

theorem aV17 : (a 17 : ℚ) = 2534 := by
  rw [a_succ, aV16, cV17]
  norm_num

theorem aG (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = G n := by
  induction n, hn using Nat.le_induction with
  | base => rw [aV2]; norm_num [G]
  | succ n hn ih =>
    rw [a_succ, ih]
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have h := cO m (by omega)
      have h1 : (-1 : ℚ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
      have h2 : (-1 : ℚ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
      rw [h]
      simp only [G, h1, h2]
      push_cast
      ring
    · have h := cE (m + 1) (by omega)
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring] at h
      have h1 : (-1 : ℚ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
      have h2 : (-1 : ℚ) ^ (2 * m + 1 + 1) = 1 := by rw [pow_succ, pow_succ, pow_mul]; norm_num
      rw [h]
      simp only [G, h1, h2]
      push_cast
      ring

end OMA.CA_a270683

open OMA.CA_a270683 OMA.S_oeis_a270683 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a270683.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn0
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      push_cast
      ring
  · intro n hn0 hp
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      rw [Even.neg_one_pow hp]
      push_cast
      ring
  · intro n hp
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      rw [Odd.neg_one_pow hp]
      push_cast
      ring
  · intro n hn0
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
      rw [show k + 8 - 1 = k + 7 by omega]
      rw [show k + 8 - 2 = k + 6 by omega]
      rw [show k + 8 - 3 = k + 5 by omega]
      rw [show k + 8 - 4 = k + 4 by omega]
      rw [show k + 8 - 5 = k + 3 by omega]
      rw [show k + 8 - 6 = k + 2 by omega]
      rw [aG (k + 8) (by omega), aG (k + 7) (by omega), aG (k + 6) (by omega), aG (k + 5) (by omega), aG (k + 4) (by omega), aG (k + 3) (by omega), aG (k + 2) (by omega)]
      simp only [G]
      push_cast
      ring
  · have hL : mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X) ^ 2 : PowerSeries ℚ) = mk (fun n => (a n : ℚ)) - C 2 * (X ^ 1 * mk (fun n => (a n : ℚ))) - X ^ 2 * mk (fun n => (a n : ℚ)) + C 4 * (X ^ 3 * mk (fun n => (a n : ℚ))) - X ^ 4 * mk (fun n => (a n : ℚ)) - C 2 * (X ^ 5 * mk (fun n => (a n : ℚ))) + X ^ 6 * mk (fun n => (a n : ℚ)) := by
      try simp only [map_ofNat]
      ring
    have hR : (1 + 4 * X + 5 * X ^ 2 + 4 * X ^ 3 - 5 * X ^ 4 - X ^ 6 : PowerSeries ℚ) = 1 + C 4 * X ^ 1 + C 5 * X ^ 2 + C 4 * X ^ 3 - C 5 * X ^ 4 - X ^ 6 := by
      try simp only [map_ofNat]
      ring
    rw [hL, hR]
    ext k
    simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_one, coeff_C]
    rcases Nat.lt_or_ge k 16 with h | h
    · interval_cases k <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 16 := ⟨k - 16, by omega⟩
      rw [if_pos (show 1 ≤ j + 16 by omega)]
      rw [if_pos (show 2 ≤ j + 16 by omega)]
      rw [if_pos (show 3 ≤ j + 16 by omega)]
      rw [if_pos (show 4 ≤ j + 16 by omega)]
      rw [if_pos (show 5 ≤ j + 16 by omega)]
      rw [if_pos (show 6 ≤ j + 16 by omega)]
      rw [if_neg (show j + 16 ≠ 0 by omega)]
      rw [if_neg (show j + 16 ≠ 1 by omega)]
      rw [if_neg (show j + 16 ≠ 2 by omega)]
      rw [if_neg (show j + 16 ≠ 3 by omega)]
      rw [if_neg (show j + 16 ≠ 4 by omega)]
      rw [if_neg (show j + 16 ≠ 6 by omega)]
      rw [show j + 16 - 1 = j + 15 by omega]
      rw [show j + 16 - 2 = j + 14 by omega]
      rw [show j + 16 - 3 = j + 13 by omega]
      rw [show j + 16 - 4 = j + 12 by omega]
      rw [show j + 16 - 5 = j + 11 by omega]
      rw [show j + 16 - 6 = j + 10 by omega]
      rw [aG (j + 16) (by omega), aG (j + 15) (by omega), aG (j + 14) (by omega), aG (j + 13) (by omega), aG (j + 12) (by omega), aG (j + 11) (by omega), aG (j + 10) (by omega)]
      simp only [G]
      push_cast
      ring
