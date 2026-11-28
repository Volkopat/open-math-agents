import OMAStatements.S_oeis_a269878
import Mathlib
/-!
Proof of the conjectures of the statement oeis-a269878 (OEIS A269878), Rule 43.

Method: stage t of the automaton is described exactly by an explicit region of the plane
(defined by linear inequalities and a parity condition); one step of the rule maps the description
at t to the one at t + 1 (a case split on the five cells of the neighbourhood, closed by omega).
The ON cells of the square are then counted row by row in closed form, and every conjecture
reduces to a polynomial identity in n and (-1)^n.
-/

namespace OMA.CA_a269878

open OMA.S_oeis_a269878 PowerSeries

def nxt (code : ℕ) (g : ℤ → ℤ → Bool) : ℤ → ℤ → Bool := fun i j =>
  code.testBit ((g i j).toNat + 2 * ((g (i + 1) j).toNat + (g (i - 1) j).toNat +
    (g i (j + 1)).toNat + (g i (j - 1)).toNat))

theorem cell_succ (code t : ℕ) : cell code (t + 1) = nxt code (cell code t) := by
  funext i j
  rfl

/-- The centred square of half-width `(t+1)/2`, restricted to one colour of the checkerboard. -/
abbrev Q (t : ℕ) (x y : ℤ) : Prop :=
  -(((t + 1) / 2 : ℕ) : ℤ) ≤ x ∧ x ≤ (((t + 1) / 2 : ℕ) : ℤ) ∧
  -(((t + 1) / 2 : ℕ) : ℤ) ≤ y ∧ y ≤ (((t + 1) / 2 : ℕ) : ℤ) ∧ (x + y + t) % 2 = 0

/-- Stage `t` of Rule 43: the square checkerboard `Q t` at even times, its complement at odd times. -/
def F (t : ℕ) (x y : ℤ) : Bool := decide ((t % 2 = 0 ∧ Q t x y) ∨ (t % 2 = 1 ∧ ¬ Q t x y))


theorem F_even (t : ℕ) (ht : t % 2 = 0) (x y : ℤ) : F t x y = decide (Q t x y) := by
  simp only [F]
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · omega
  · intro h
    exact Or.inl ⟨ht, h⟩

theorem F_odd (t : ℕ) (ht : t % 2 = 1) (x y : ℤ) : F t x y = decide (¬ Q t x y) := by
  simp only [F]
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · omega
    · exact h
  · intro h
    exact Or.inr ⟨ht, h⟩

set_option maxHeartbeats 4000000 in
theorem stepF (t : ℕ) (x y : ℤ) : nxt 43 (F t) x y = F (t + 1) x y := by
  simp only [nxt]
  cases h0 : F t x y <;> cases h1 : F t (x + 1) y <;> cases h2 : F t (x - 1) y <;>
    cases h3 : F t x (y + 1) <;> cases h4 : F t x (y - 1) <;>
    simp only [F, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true,
      Bool.toNat_false, Nat.testBit_eq_decide_div_mod_eq] at h0 h1 h2 h3 h4 ⊢ <;>
    norm_num <;> push_cast at * <;> omega

theorem cellF (t : ℕ) : cell 43 t = F t := by
  induction t with
  | zero =>
    funext x y
    show decide (x = 0 ∧ y = 0) = F 0 x y
    rw [F_even 0 rfl]
    apply decide_eq_decide.mpr
    simp only [Q]
    norm_num
    constructor
    · rintro ⟨rfl, rfl⟩
      norm_num
    · intro h
      omega
  | succ t ih =>
    rw [cell_succ, ih]
    funext x y
    exact stepF t x y


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

theorem outer (lo hi N : ℕ) (g : ℕ → ℕ) :
    ∑ i ∈ Finset.range N, (if lo ≤ i ∧ i ≤ hi then g (i % 2) else 0) =
      g 0 * cntc lo hi 0 N + g 1 * cntc lo hi 1 N := by
  have e : ∀ i : ℕ, (if lo ≤ i ∧ i ≤ hi then g (i % 2) else 0) =
      g 0 * (if lo ≤ i ∧ i ≤ hi ∧ i % 2 = 0 then 1 else 0) +
      g 1 * (if lo ≤ i ∧ i ≤ hi ∧ i % 2 = 1 then 1 else 0) := by
    intro i
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · by_cases hb : lo ≤ i ∧ i ≤ hi
      · rw [if_pos hb, if_pos ⟨hb.1, hb.2, h⟩, if_neg (by omega), h]
        ring
      · rw [if_neg hb, if_neg (by omega), if_neg (by omega)]
        ring
    · by_cases hb : lo ≤ i ∧ i ≤ hi
      · rw [if_pos hb, if_neg (by omega), if_pos ⟨hb.1, hb.2, h⟩, h]
        ring
      · rw [if_neg hb, if_neg (by omega), if_neg (by omega)]
        ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [cnt lo hi 0 N (by norm_num), cnt lo hi 1 N (by norm_num)]

/-- Rows of the square checkerboard `Q t` in index coordinates. -/
theorem rowQ (t i : ℕ) (q : ℕ) (hq : q = (i % 2 + t) % 2) :
    ∑ j ∈ Finset.range (2 * t + 1),
      (if Q t ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0) =
      if t - (t + 1) / 2 ≤ i ∧ i ≤ t + (t + 1) / 2 then
        cntc (t - (t + 1) / 2) (t + (t + 1) / 2) q (2 * t + 1) else 0 := by
  split_ifs with hb
  · rw [← cnt _ _ q _ (by omega)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
  · refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [if_neg]
    omega

theorem countQ (t : ℕ) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if Q t ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0) =
      cntc (t - (t + 1) / 2) (t + (t + 1) / 2) (t % 2) (2 * t + 1) *
        cntc (t - (t + 1) / 2) (t + (t + 1) / 2) 0 (2 * t + 1) +
      cntc (t - (t + 1) / 2) (t + (t + 1) / 2) ((1 + t) % 2) (2 * t + 1) *
        cntc (t - (t + 1) / 2) (t + (t + 1) / 2) 1 (2 * t + 1) := by
  rw [Finset.sum_congr rfl (fun i _ => rowQ t i ((i % 2 + t) % 2) rfl)]
  rw [outer _ _ _ (fun p => cntc (t - (t + 1) / 2) (t + (t + 1) / 2) ((p + t) % 2) (2 * t + 1))]
  simp only [zero_add]

theorem cE (m : ℕ) (hm : 0 ≤ m) : (onCount 43 (2 * m) : ℚ) = 2 * (m : ℚ) ^ 2 + 2 * m + 1 := by
  have h : onCount 43 (2 * m) = 2 * m ^ 2 + 2 * m + 1 := by
    simp only [onCount, cellF, F_even (2 * m) (by omega), decide_eq_true_eq]
    rw [countQ]
    have h1 : (2 * m + 1) / 2 = m := by omega
    simp only [h1, show (2 * m) % 2 = 0 by omega, show (1 + 2 * m) % 2 = 1 by omega, cntc]
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · have a1 : (max (min (2 * (2 * (2 * k)) + 1) (2 * (2 * k) + 2 * k + 1)) (2 * (2 * k) - 2 * k) + 1 - 0) / 2 -
          (2 * (2 * k) - 2 * k + 1 - 0) / 2 = 2 * k + 1 := by omega
      have a2 : (max (min (2 * (2 * (2 * k)) + 1) (2 * (2 * k) + 2 * k + 1)) (2 * (2 * k) - 2 * k) + 1 - 1) / 2 -
          (2 * (2 * k) - 2 * k + 1 - 1) / 2 = 2 * k := by omega
      rw [a1, a2]
      ring
    · have a1 : (max (min (2 * (2 * (2 * k + 1)) + 1) (2 * (2 * k + 1) + (2 * k + 1) + 1)) (2 * (2 * k + 1) - (2 * k + 1)) + 1 - 0) / 2 -
          (2 * (2 * k + 1) - (2 * k + 1) + 1 - 0) / 2 = 2 * k + 1 := by omega
      have a2 : (max (min (2 * (2 * (2 * k + 1)) + 1) (2 * (2 * k + 1) + (2 * k + 1) + 1)) (2 * (2 * k + 1) - (2 * k + 1)) + 1 - 1) / 2 -
          (2 * (2 * k + 1) - (2 * k + 1) + 1 - 1) / 2 = 2 * k + 2 := by omega
      rw [a1, a2]
      ring
  rw [h]
  push_cast
  ring

theorem ind_not (P : Prop) [Decidable P] :
    ((if decide (¬P) = true then 1 else 0 : ℕ) : ℤ) = 1 - (if P then 1 else 0) := by
  by_cases h : P <;> simp [h]

theorem cO (m : ℕ) (hm : 0 ≤ m) :
    (onCount 43 (2 * m + 1) : ℚ) = (2 * (2 * (m : ℚ) + 1) + 1) ^ 2 - (2 * (m : ℚ) ^ 2 + 6 * m + 4) := by
  have hQ : ∑ i ∈ Finset.range (2 * (2 * m + 1) + 1), ∑ j ∈ Finset.range (2 * (2 * m + 1) + 1),
      (if Q (2 * m + 1) ((i : ℤ) - (2 * m + 1 : ℕ)) ((j : ℤ) - (2 * m + 1 : ℕ)) then 1 else 0) =
      2 * m ^ 2 + 6 * m + 4 := by
    rw [countQ]
    have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    simp only [h1, show (2 * m + 1) % 2 = 1 by omega, show (1 + (2 * m + 1)) % 2 = 0 by omega]
    have key : (cntc (2 * m + 1 - (m + 1)) (2 * m + 1 + (m + 1)) 0 (2 * (2 * m + 1) + 1) = m + 2 ∧
        cntc (2 * m + 1 - (m + 1)) (2 * m + 1 + (m + 1)) 1 (2 * (2 * m + 1) + 1) = m + 1) ∨
        (cntc (2 * m + 1 - (m + 1)) (2 * m + 1 + (m + 1)) 0 (2 * (2 * m + 1) + 1) = m + 1 ∧
        cntc (2 * m + 1 - (m + 1)) (2 * m + 1 + (m + 1)) 1 (2 * (2 * m + 1) + 1) = m + 2) := by
      simp only [cntc]
      omega
    rcases key with ⟨k0, k1⟩ | ⟨k0, k1⟩ <;> rw [k0, k1] <;> ring
  have hs : (onCount 43 (2 * m + 1) : ℤ) = ∑ i ∈ Finset.range (2 * (2 * m + 1) + 1),
      ∑ j ∈ Finset.range (2 * (2 * m + 1) + 1),
      ((1 : ℤ) - (if Q (2 * m + 1) ((i : ℤ) - (2 * m + 1 : ℕ)) ((j : ℤ) - (2 * m + 1 : ℕ)) then 1 else 0)) := by
    simp only [onCount, cellF, F_odd (2 * m + 1) (by omega), Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact ind_not _
  have hQ' : ∑ i ∈ Finset.range (2 * (2 * m + 1) + 1), ∑ j ∈ Finset.range (2 * (2 * m + 1) + 1),
      (if Q (2 * m + 1) ((i : ℤ) - (2 * m + 1 : ℕ)) ((j : ℤ) - (2 * m + 1 : ℕ)) then (1 : ℤ) else 0) =
      2 * (m : ℤ) ^ 2 + 6 * m + 4 := by
    have := congrArg (fun z : ℕ => (z : ℤ)) hQ
    push_cast at this
    exact this
  have hz : (onCount 43 (2 * m + 1) : ℤ) = (2 * (2 * (m : ℤ) + 1) + 1) ^ 2 - (2 * (m : ℤ) ^ 2 + 6 * m + 4) := by
    rw [hs]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    rw [hQ']
    push_cast
    ring
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hz
  push_cast at hq
  exact hq

theorem cV0 : (onCount 43 0 : ℚ) = 1 := by
  rw [show (0 : ℕ) = 2 * 0 by norm_num, cE 0 (by norm_num)]
  try norm_num

theorem cV1 : (onCount 43 1 : ℚ) = 5 := by
  rw [show (1 : ℕ) = 2 * 0 + 1 by norm_num, cO 0 (by norm_num)]
  try norm_num

theorem cV2 : (onCount 43 2 : ℚ) = 5 := by
  rw [show (2 : ℕ) = 2 * 1 by norm_num, cE 1 (by norm_num)]
  try norm_num

theorem cV3 : (onCount 43 3 : ℚ) = 37 := by
  rw [show (3 : ℕ) = 2 * 1 + 1 by norm_num, cO 1 (by norm_num)]
  try norm_num

theorem cV4 : (onCount 43 4 : ℚ) = 13 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, cE 2 (by norm_num)]
  try norm_num

theorem cV5 : (onCount 43 5 : ℚ) = 97 := by
  rw [show (5 : ℕ) = 2 * 2 + 1 by norm_num, cO 2 (by norm_num)]
  try norm_num

theorem cV6 : (onCount 43 6 : ℚ) = 25 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, cE 3 (by norm_num)]
  try norm_num

theorem cV7 : (onCount 43 7 : ℚ) = 185 := by
  rw [show (7 : ℕ) = 2 * 3 + 1 by norm_num, cO 3 (by norm_num)]
  try norm_num

theorem cV8 : (onCount 43 8 : ℚ) = 41 := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num, cE 4 (by norm_num)]
  try norm_num

theorem cV9 : (onCount 43 9 : ℚ) = 301 := by
  rw [show (9 : ℕ) = 2 * 4 + 1 by norm_num, cO 4 (by norm_num)]
  try norm_num

theorem cV10 : (onCount 43 10 : ℚ) = 61 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num, cE 5 (by norm_num)]
  try norm_num

theorem cV11 : (onCount 43 11 : ℚ) = 445 := by
  rw [show (11 : ℕ) = 2 * 5 + 1 by norm_num, cO 5 (by norm_num)]
  try norm_num

theorem cV12 : (onCount 43 12 : ℚ) = 85 := by
  rw [show (12 : ℕ) = 2 * 6 by norm_num, cE 6 (by norm_num)]
  try norm_num

theorem cV13 : (onCount 43 13 : ℚ) = 617 := by
  rw [show (13 : ℕ) = 2 * 6 + 1 by norm_num, cO 6 (by norm_num)]
  try norm_num

theorem cV14 : (onCount 43 14 : ℚ) = 113 := by
  rw [show (14 : ℕ) = 2 * 7 by norm_num, cE 7 (by norm_num)]
  try norm_num

theorem cV15 : (onCount 43 15 : ℚ) = 817 := by
  rw [show (15 : ℕ) = 2 * 7 + 1 by norm_num, cO 7 (by norm_num)]
  try norm_num

theorem cV16 : (onCount 43 16 : ℚ) = 145 := by
  rw [show (16 : ℕ) = 2 * 8 by norm_num, cE 8 (by norm_num)]
  try norm_num

theorem cV17 : (onCount 43 17 : ℚ) = 1045 := by
  rw [show (17 : ℕ) = 2 * 8 + 1 by norm_num, cO 8 (by norm_num)]
  try norm_num

def G (n : ℕ) : ℚ := (((3 : ℚ) / 4) * (n : ℚ) ^ 0 + ((4 : ℚ) / 3) * (n : ℚ) ^ 1 + ((7 : ℚ) / 4) * (n : ℚ) ^ 2 + ((2 : ℚ) / 3) * (n : ℚ) ^ 3) + (-1 : ℚ) ^ n * (((1 : ℚ) / 4) * (n : ℚ) ^ 0 + (-1 : ℚ) * (n : ℚ) ^ 1 + ((-3 : ℚ) / 4) * (n : ℚ) ^ 2)

theorem a_succ (n : ℕ) : (a (n + 1) : ℚ) = a n + (onCount 43 (n + 1) : ℚ) := by
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

theorem aV2 : (a 2 : ℚ) = 11 := by
  rw [a_succ, aV1, cV2]
  norm_num

theorem aV3 : (a 3 : ℚ) = 48 := by
  rw [a_succ, aV2, cV3]
  norm_num

theorem aV4 : (a 4 : ℚ) = 61 := by
  rw [a_succ, aV3, cV4]
  norm_num

theorem aV5 : (a 5 : ℚ) = 158 := by
  rw [a_succ, aV4, cV5]
  norm_num

theorem aV6 : (a 6 : ℚ) = 183 := by
  rw [a_succ, aV5, cV6]
  norm_num

theorem aV7 : (a 7 : ℚ) = 368 := by
  rw [a_succ, aV6, cV7]
  norm_num

theorem aV8 : (a 8 : ℚ) = 409 := by
  rw [a_succ, aV7, cV8]
  norm_num

theorem aV9 : (a 9 : ℚ) = 710 := by
  rw [a_succ, aV8, cV9]
  norm_num

theorem aV10 : (a 10 : ℚ) = 771 := by
  rw [a_succ, aV9, cV10]
  norm_num

theorem aV11 : (a 11 : ℚ) = 1216 := by
  rw [a_succ, aV10, cV11]
  norm_num

theorem aV12 : (a 12 : ℚ) = 1301 := by
  rw [a_succ, aV11, cV12]
  norm_num

theorem aV13 : (a 13 : ℚ) = 1918 := by
  rw [a_succ, aV12, cV13]
  norm_num

theorem aV14 : (a 14 : ℚ) = 2031 := by
  rw [a_succ, aV13, cV14]
  norm_num

theorem aV15 : (a 15 : ℚ) = 2848 := by
  rw [a_succ, aV14, cV15]
  norm_num

theorem aG (n : ℕ) (hn : 0 ≤ n) : (a n : ℚ) = G n := by
  induction n, hn using Nat.le_induction with
  | base => rw [aV0]; norm_num [G]
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

end OMA.CA_a269878

open OMA.CA_a269878 OMA.S_oeis_a269878 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a269878.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rcases Nat.lt_or_ge n 0 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      push_cast
      ring
  · intro n hp
    rcases Nat.lt_or_ge n 0 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      rw [Even.neg_one_pow hp]
      push_cast
      ring
  · intro n hp
    rcases Nat.lt_or_ge n 0 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      rw [Odd.neg_one_pow hp]
      push_cast
      ring
  · intro n hn0
    rcases Nat.lt_or_ge n 7 with h | h
    · interval_cases n <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
      rw [show k + 7 - 1 = k + 6 by omega]
      rw [show k + 7 - 2 = k + 5 by omega]
      rw [show k + 7 - 3 = k + 4 by omega]
      rw [show k + 7 - 4 = k + 3 by omega]
      rw [show k + 7 - 5 = k + 2 by omega]
      rw [show k + 7 - 6 = k + 1 by omega]
      rw [show k + 7 - 7 = k + 0 by omega]
      rw [aG (k + 7) (by omega), aG (k + 6) (by omega), aG (k + 5) (by omega), aG (k + 4) (by omega), aG (k + 3) (by omega), aG (k + 2) (by omega), aG (k + 1) (by omega), aG (k + 0) (by omega)]
      simp only [G]
      push_cast
      ring
  · have hL : mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X) ^ 3 : PowerSeries ℚ) = mk (fun n => (a n : ℚ)) - X ^ 1 * mk (fun n => (a n : ℚ)) - C 3 * (X ^ 2 * mk (fun n => (a n : ℚ))) + C 3 * (X ^ 3 * mk (fun n => (a n : ℚ))) + C 3 * (X ^ 4 * mk (fun n => (a n : ℚ))) - C 3 * (X ^ 5 * mk (fun n => (a n : ℚ))) - X ^ 6 * mk (fun n => (a n : ℚ)) + X ^ 7 * mk (fun n => (a n : ℚ)) := by
      try simp only [map_ofNat]
      ring
    have hR : (1 + 5 * X + 2 * X ^ 2 + 22 * X ^ 3 + X ^ 4 + X ^ 5 : PowerSeries ℚ) = 1 + C 5 * X ^ 1 + C 2 * X ^ 2 + C 22 * X ^ 3 + X ^ 4 + X ^ 5 := by
      try simp only [map_ofNat]
      ring
    rw [hL, hR]
    ext k
    simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_one, coeff_C]
    rcases Nat.lt_or_ge k 14 with h | h
    · interval_cases k <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 14 := ⟨k - 14, by omega⟩
      rw [if_pos (show 1 ≤ j + 14 by omega)]
      rw [if_pos (show 2 ≤ j + 14 by omega)]
      rw [if_pos (show 3 ≤ j + 14 by omega)]
      rw [if_pos (show 4 ≤ j + 14 by omega)]
      rw [if_pos (show 5 ≤ j + 14 by omega)]
      rw [if_pos (show 6 ≤ j + 14 by omega)]
      rw [if_pos (show 7 ≤ j + 14 by omega)]
      rw [if_neg (show j + 14 ≠ 0 by omega)]
      rw [if_neg (show j + 14 ≠ 1 by omega)]
      rw [if_neg (show j + 14 ≠ 2 by omega)]
      rw [if_neg (show j + 14 ≠ 3 by omega)]
      rw [if_neg (show j + 14 ≠ 4 by omega)]
      rw [if_neg (show j + 14 ≠ 5 by omega)]
      rw [show j + 14 - 1 = j + 13 by omega]
      rw [show j + 14 - 2 = j + 12 by omega]
      rw [show j + 14 - 3 = j + 11 by omega]
      rw [show j + 14 - 4 = j + 10 by omega]
      rw [show j + 14 - 5 = j + 9 by omega]
      rw [show j + 14 - 6 = j + 8 by omega]
      rw [show j + 14 - 7 = j + 7 by omega]
      rw [aG (j + 14) (by omega), aG (j + 13) (by omega), aG (j + 12) (by omega), aG (j + 11) (by omega), aG (j + 10) (by omega), aG (j + 9) (by omega), aG (j + 8) (by omega), aG (j + 7) (by omega)]
      simp only [G]
      push_cast
      ring
