import OMAStatements.S_oeis_a269911
import Mathlib
/-!
Proof of the conjectures of the statement oeis-a269911 (OEIS A269911), Rule 3.

Method: from stage 2 on, the automaton is a uniform background (blinking or not) with a fixed
finite list of exceptional cells, alternating between two phases. Each phase step is checked by
a finite kernel computation on a box around the exceptions (everything farther away sees only
background), the count of ON cells follows from the length of the exception list, and every
conjecture then reduces to a polynomial identity in n and (-1)^n (or 2^n and 4^n).
The exception-list technique follows the merged proof of oeis-a273848 in this repository.
-/

namespace OMA.CA_a269911

open OMA.S_oeis_a269911 PowerSeries

abbrev P := ℤ × ℤ

/-- A pattern: background `b` everywhere except on the finite list `L`, where the value is `!b`. -/
def pic (b : Bool) (L : List P) : ℤ → ℤ → Bool := fun i j => if (i, j) ∈ L then !b else b

/-- One synchronous step of the automaton with Wolfram code `code`. -/
def nxt (code : ℕ) (g : ℤ → ℤ → Bool) : ℤ → ℤ → Bool := fun i j =>
  code.testBit ((g i j).toNat + 2 * ((g (i + 1) j).toNat + (g (i - 1) j).toNat +
    (g i (j + 1)).toNat + (g i (j - 1)).toNat))

theorem cell_succ (code t : ℕ) : cell code (t + 1) = nxt code (cell code t) := by
  funext i j
  rfl

theorem cell_zero (code : ℕ) : cell code 0 = pic false [(0, 0)] := by
  funext i j
  by_cases h : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · have h' : (i, j) ∉ [((0 : ℤ), (0 : ℤ))] := by
      simp only [List.mem_singleton, Prod.mk.injEq]
      exact h
    simp only [cell, pic, if_neg h']
    exact decide_eq_false h

/-- Every point of the list lies in the square `[-R, R]²`. -/
def inR (R : ℕ) (L : List P) : Prop :=
  ∀ p ∈ L, -(R : ℤ) ≤ p.1 ∧ p.1 ≤ R ∧ -(R : ℤ) ≤ p.2 ∧ p.2 ≤ R

instance (R : ℕ) (L : List P) : Decidable (inR R L) := by
  unfold inR
  infer_instance

theorem pic_far {R : ℕ} {L : List P} (hL : inR R L) (b : Bool) (u v : ℤ)
    (h : ¬(-(R : ℤ) ≤ u ∧ u ≤ R ∧ -(R : ℤ) ≤ v ∧ v ≤ R)) : pic b L u v = b := by
  have hm : (u, v) ∉ L := fun hm => h (hL _ hm)
  simp only [pic, if_neg hm]

/-- The coordinates `-(R+1), ..., R+1`. -/
def box (R : ℕ) : List ℤ := List.map (fun k : ℕ => (k : ℤ) - ((R : ℤ) + 1)) (List.range (2 * R + 3))

theorem mem_box (R : ℕ) (x : ℤ) (h1 : -((R : ℤ) + 1) ≤ x) (h2 : x ≤ R + 1) : x ∈ box R := by
  have e : (((x + R + 1).toNat : ℕ) : ℤ) = x + R + 1 := Int.toNat_of_nonneg (by omega)
  refine List.mem_map.mpr ⟨(x + R + 1).toNat, List.mem_range.mpr ?_, ?_⟩
  · have : (((x + R + 1).toNat : ℕ) : ℤ) < ((2 * R + 3 : ℕ) : ℤ) := by push_cast; omega
    exact_mod_cast this
  · omega

theorem step {code R : ℕ} {b b' : Bool} {L L' : List P} (hL : inR R L) (hL' : inR R L')
    (hbg : code.testBit (b.toNat + 2 * (b.toNat + b.toNat + b.toNat + b.toNat)) = b')
    (hbox : ∀ x ∈ box R, ∀ y ∈ box R, nxt code (pic b L) x y = pic b' L' x y) :
    nxt code (pic b L) = pic b' L' := by
  funext x y
  by_cases h : (-((R : ℤ) + 1) ≤ x ∧ x ≤ R + 1) ∧ (-((R : ℤ) + 1) ≤ y ∧ y ≤ R + 1)
  · exact hbox x (mem_box R x h.1.1 h.1.2) y (mem_box R y h.2.1 h.2.2)
  · rw [pic_far hL' b' x y (by omega)]
    simp only [nxt]
    rw [pic_far hL b x y (by omega), pic_far hL b (x + 1) y (by omega),
      pic_far hL b (x - 1) y (by omega), pic_far hL b x (y + 1) (by omega),
      pic_far hL b x (y - 1) (by omega)]
    exact hbg

theorem sum_single (t : ℕ) (p : P) (h : -(t : ℤ) ≤ p.1 ∧ p.1 ≤ t ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ t) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if ((i : ℤ) - t, (j : ℤ) - t) = p then (1 : ℤ) else 0) = 1 := by
  obtain ⟨p1, p2⟩ := p
  simp only at h
  rw [Finset.sum_eq_single (p1 + t).toNat, Finset.sum_eq_single (p2 + t).toNat]
  · rw [if_pos]
    simp only [Prod.mk.injEq]
    constructor <;> omega
  · intro j _ hj
    rw [if_neg]
    simp only [Prod.mk.injEq, not_and]
    intro _ h2
    omega
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    simp only [Prod.mk.injEq, not_and]
    intro h1
    omega
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn

theorem sum_mem (t : ℕ) (L : List P) (hn : L.Nodup) (hb : inR t L) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if ((i : ℤ) - t, (j : ℤ) - t) ∈ L then (1 : ℤ) else 0) = L.length := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp : p ∉ L := (List.nodup_cons.mp hn).1
    have e : ∀ i j : ℕ, (if ((i : ℤ) - t, (j : ℤ) - t) ∈ p :: L then (1 : ℤ) else 0) =
        (if ((i : ℤ) - t, (j : ℤ) - t) = p then 1 else 0) +
        (if ((i : ℤ) - t, (j : ℤ) - t) ∈ L then 1 else 0) := by
      intro i j
      by_cases h1 : ((i : ℤ) - t, (j : ℤ) - t) = p
      · rw [h1]
        simp [hp]
      · simp [h1]
    simp only [e, Finset.sum_add_distrib]
    rw [sum_single t p (hb p List.mem_cons_self),
      ih (List.nodup_cons.mp hn).2 (fun q hq => hb q (List.mem_cons_of_mem _ hq))]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

theorem count_false (code t : ℕ) (L : List P) (hn : L.Nodup) (hb : inR t L)
    (h : cell code t = pic false L) : (onCount code t : ℤ) = L.length := by
  rw [← sum_mem t L hn hb]
  simp only [onCount, h, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases hm : ((i : ℤ) - t, (j : ℤ) - t) ∈ L <;> simp [pic, hm]

theorem count_true (code t : ℕ) (L : List P) (hn : L.Nodup) (hb : inR t L)
    (h : cell code t = pic true L) :
    (onCount code t : ℤ) = (2 * (t : ℤ) + 1) ^ 2 - L.length := by
  have hs : (onCount code t : ℤ) = ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      ((1 : ℤ) - (if ((i : ℤ) - t, (j : ℤ) - t) ∈ L then (1 : ℤ) else 0)) := by
    simp only [onCount, h, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hm : ((i : ℤ) - t, (j : ℤ) - t) ∈ L <;> simp [pic, hm]
  rw [hs]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  rw [sum_mem t L hn hb]
  push_cast
  ring

theorem inR_mono {R S : ℕ} {L : List P} (h : inR R L) (hRS : R ≤ S) : inR S L := by
  intro p hp
  have := h p hp
  omega
def L0 : List P := [(0, 0)]
def L1 : List P := [(-1, 0), (0, -1), (0, 1), (1, 0)]
def L2 : List P := [(0, 0)]
def L3 : List P := [(-1, 0), (0, -1), (0, 1), (1, 0)]

theorem lay0 : cell 3 0 = pic false L0 := cell_zero 3

theorem lay1 : cell 3 1 = pic true L1 := by
  rw [cell_succ, lay0]
  exact step (R := 1) (by decide) (by decide) (by decide) (by decide)

theorem lay2 : cell 3 2 = pic false L2 := by
  rw [cell_succ, lay1]
  exact step (R := 1) (by decide) (by decide) (by decide) (by decide)

theorem lay3 : cell 3 3 = pic true L3 := by
  rw [cell_succ, lay2]
  exact step (R := 1) (by decide) (by decide) (by decide) (by decide)

theorem back : nxt 3 (pic true L3) = pic false L2 :=
  step (R := 1) (by decide) (by decide) (by decide) (by decide)

theorem fwd : nxt 3 (pic false L2) = pic true L3 :=
  step (R := 1) (by decide) (by decide) (by decide) (by decide)

theorem per (k : ℕ) : cell 3 (2 + 2 * k) = pic false L2 ∧
    cell 3 (2 + 2 * k + 1) = pic true L3 := by
  induction k with
  | zero => exact ⟨lay2, lay3⟩
  | succ k ih =>
    have h0 : cell 3 (2 + 2 * (k + 1)) = pic false L2 := by
      rw [show 2 + 2 * (k + 1) = (2 + 2 * k + 1) + 1 by ring, cell_succ, ih.2]
      exact back
    refine ⟨h0, ?_⟩
    rw [cell_succ, h0]
    exact fwd

theorem cE (m : ℕ) (hm : 1 ≤ m) :
    (onCount 3 (2 * m) : ℚ) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 1 + k := ⟨m - 1, by omega⟩
  have h := (per k).1
  rw [show 2 + 2 * k = 2 * (1 + k) by ring] at h
  have := count_false 3 _ L2 (by decide) (inR_mono (R := 1) (by decide) (by omega)) h
  have h2 : ((onCount 3 (2 * (1 + k)) : ℤ) : ℚ) = 1 := by
    rw [this]
    simp [L2]
    try ring
  exact_mod_cast h2

theorem cO (m : ℕ) (hm : 1 ≤ m) :
    (onCount 3 (2 * m + 1) : ℚ) = (2 * (2 * (m : ℚ) + 1) + 1) ^ 2 - 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 1 + k := ⟨m - 1, by omega⟩
  have h := (per k).2
  rw [show 2 + 2 * k + 1 = 2 * (1 + k) + 1 by ring] at h
  have := count_true 3 _ L3 (by decide) (inR_mono (R := 1) (by decide) (by omega)) h
  have h2 : ((onCount 3 (2 * (1 + k) + 1) : ℤ) : ℚ) = (2 * (2 * ((1 + k : ℕ) : ℚ) + 1) + 1) ^ 2 - 4 := by
    rw [this]
    simp [L3]
    try ring
  exact_mod_cast h2

theorem cV0 : (onCount 3 0 : ℚ) = 1 := by
  have := count_false 3 0 L0 (by decide) (by decide) lay0
  have h2 : ((onCount 3 0 : ℤ) : ℚ) = 1 := by
    rw [this]
    norm_num [L0]
  exact_mod_cast h2

theorem cV1 : (onCount 3 1 : ℚ) = 5 := by
  have := count_true 3 1 L1 (by decide) (by decide) lay1
  have h2 : ((onCount 3 1 : ℤ) : ℚ) = 5 := by
    rw [this]
    norm_num [L1]
  exact_mod_cast h2

theorem cV2 : (onCount 3 2 : ℚ) = 1 := by
  have := count_false 3 2 L2 (by decide) (by decide) lay2
  have h2 : ((onCount 3 2 : ℤ) : ℚ) = 1 := by
    rw [this]
    norm_num [L2]
  exact_mod_cast h2

theorem cV3 : (onCount 3 3 : ℚ) = 45 := by
  have := count_true 3 3 L3 (by decide) (by decide) lay3
  have h2 : ((onCount 3 3 : ℤ) : ℚ) = 45 := by
    rw [this]
    norm_num [L3]
  exact_mod_cast h2

def G (n : ℕ) : ℚ := 4 * (4 : ℚ) ^ n - 4 * (2 : ℚ) ^ n + (-3 : ℚ)

theorem four_pow (j : ℕ) : (4 : ℚ) ^ j = ((2 : ℚ) ^ j) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

theorem aG (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = G n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hp : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hq : 2 ^ 1 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : 2 ^ (j + 1) - 1 = 2 * (2 ^ j - 1) + 1 := by rw [pow_succ]; omega
  have h := cO (2 ^ j - 1) (by norm_num at hq; omega)
  simp only [a, G]
  rw [e]
  push_cast
  rw [h, Nat.cast_sub hp]
  push_cast
  simp only [four_pow]
  ring

theorem aV0 : (a 0 : ℚ) = 1 := by
  simp only [a]
  norm_num
  exact_mod_cast cV0

theorem aV1 : (a 1 : ℚ) = 5 := by
  simp only [a]
  norm_num
  exact_mod_cast cV1

theorem aV2 : (a 2 : ℚ) = 45 := by
  rw [aG 2 (by norm_num)]
  norm_num [G]

theorem aV3 : (a 3 : ℚ) = 221 := by
  rw [aG 3 (by norm_num)]
  norm_num [G]

theorem aV4 : (a 4 : ℚ) = 957 := by
  rw [aG 4 (by norm_num)]
  norm_num [G]

theorem aV5 : (a 5 : ℚ) = 3965 := by
  rw [aG 5 (by norm_num)]
  norm_num [G]

theorem aV6 : (a 6 : ℚ) = 16125 := by
  rw [aG 6 (by norm_num)]
  norm_num [G]

theorem aV7 : (a 7 : ℚ) = 65021 := by
  rw [aG 7 (by norm_num)]
  norm_num [G]

theorem aV8 : (a 8 : ℚ) = 261117 := by
  rw [aG 8 (by norm_num)]
  norm_num [G]

theorem aV9 : (a 9 : ℚ) = 1046525 := by
  rw [aG 9 (by norm_num)]
  norm_num [G]

theorem aV10 : (a 10 : ℚ) = 4190205 := by
  rw [aG 10 (by norm_num)]
  norm_num [G]

theorem aV11 : (a 11 : ℚ) = 16769021 := by
  rw [aG 11 (by norm_num)]
  norm_num [G]

end OMA.CA_a269911

open OMA.CA_a269911 OMA.S_oeis_a269911 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a269911.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn0
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      simp only [four_pow]; push_cast
      ring
  · intro n hn0
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      rw [show k + 5 - 1 = k + 4 by omega]
      rw [show k + 5 - 2 = k + 3 by omega]
      rw [show k + 5 - 3 = k + 2 by omega]
      rw [aG (k + 5) (by omega), aG (k + 4) (by omega), aG (k + 3) (by omega), aG (k + 2) (by omega)]
      simp only [G]
      push_cast
      ring
  · have hL : mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X) : PowerSeries ℚ) = mk (fun n => (a n : ℚ)) - C 7 * (X ^ 1 * mk (fun n => (a n : ℚ))) + C 14 * (X ^ 2 * mk (fun n => (a n : ℚ))) - C 8 * (X ^ 3 * mk (fun n => (a n : ℚ))) := by
      try simp only [map_ofNat]
      ring
    have hR : (1 - 2 * X + 24 * X ^ 2 - 32 * X ^ 3 : PowerSeries ℚ) = 1 - C 2 * X ^ 1 + C 24 * X ^ 2 - C 32 * X ^ 3 := by
      try simp only [map_ofNat]
      ring
    rw [hL, hR]
    ext k
    simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_one, coeff_C]
    rcases Nat.lt_or_ge k 10 with h | h
    · interval_cases k <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 10 := ⟨k - 10, by omega⟩
      rw [if_pos (show 1 ≤ j + 10 by omega)]
      rw [if_pos (show 2 ≤ j + 10 by omega)]
      rw [if_pos (show 3 ≤ j + 10 by omega)]
      rw [if_neg (show j + 10 ≠ 0 by omega)]
      rw [if_neg (show j + 10 ≠ 1 by omega)]
      rw [if_neg (show j + 10 ≠ 2 by omega)]
      rw [if_neg (show j + 10 ≠ 3 by omega)]
      rw [show j + 10 - 1 = j + 9 by omega]
      rw [show j + 10 - 2 = j + 8 by omega]
      rw [show j + 10 - 3 = j + 7 by omega]
      rw [aG (j + 10) (by omega), aG (j + 9) (by omega), aG (j + 8) (by omega), aG (j + 7) (by omega)]
      simp only [G]
      push_cast
      ring
