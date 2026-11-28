import OMAStatements.S_oeis_a279144
import Mathlib

-- Credit: @qu1r0ra

open OMA.S_oeis_a279144

private def rule137 (c e w n s : Bool) : Bool :=
  if c then decide ((e.toNat + w.toNat + n.toNat + s.toNat) % 2 = 1)
  else !(e || w || n || s)

private lemma rule137_eq (c e w n s : Bool) :
    (137 : ℕ).testBit (c.toNat + 2 * (e.toNat + w.toNat + n.toNat + s.toNat)) =
      rule137 c e w n s := by
  cases c <;> cases e <;> cases w <;> cases n <;> cases s <;> decide

private lemma cell_succ (t : ℕ) (i j : ℤ) :
    cell 137 (t + 1) i j =
      rule137 (cell 137 t i j) (cell 137 t (i + 1) j) (cell 137 t (i - 1) j)
        (cell 137 t i (j + 1)) (cell 137 t i (j - 1)) := by
  exact rule137_eq _ _ _ _ _

private lemma negLeft (i : ℤ) : -i + 1 = -(i - 1) := by omega
private lemma negRight (i : ℤ) : -i - 1 = -(i + 1) := by omega

private lemma cell_neg_i (t : ℕ) (i j : ℤ) : cell 137 t (-i) j = cell 137 t i j := by
  induction t generalizing i j with
  | zero => simp [cell]
  | succ t ih =>
    simp only [cell]
    rw [negLeft i, negRight i, ih i j, ih (i - 1) j, ih (i + 1) j,
        ih i (j + 1), ih i (j - 1)]
    congr 1
    omega

private lemma cell_neg_j (t : ℕ) (i j : ℤ) : cell 137 t i (-j) = cell 137 t i j := by
  induction t generalizing i j with
  | zero => simp [cell]
  | succ t ih =>
    simp only [cell]
    rw [negLeft j, negRight j, ih i j, ih (i + 1) j, ih (i - 1) j,
        ih i (j - 1), ih i (j + 1)]
    congr 1
    omega

private lemma cell_swap (t : ℕ) (i j : ℤ) : cell 137 t j i = cell 137 t i j := by
  induction t generalizing i j with
  | zero => simp [cell, and_comm]
  | succ t ih =>
    simp only [cell]
    rw [ih i j, ih i (j + 1), ih i (j - 1), ih (i + 1) j, ih (i - 1) j]
    congr 1
    omega

private lemma cell_natAbs (t : ℕ) (i j : ℤ) :
    cell 137 t i j = cell 137 t (i.natAbs : ℤ) (j.natAbs : ℤ) := by
  rcases Int.natAbs_eq i with hi | hi <;> rcases Int.natAbs_eq j with hj | hj
  · conv_lhs => rw [hi, hj]
  · conv_lhs => rw [hi, hj]
    exact cell_neg_j t _ _
  · conv_lhs => rw [hi, hj]
    exact cell_neg_i t _ _
  · conv_lhs => rw [hi, hj]
    rw [cell_neg_i, cell_neg_j]

private lemma cell_canonical (t : ℕ) (i j : ℤ) :
    cell 137 t i j =
      cell 137 t ((max i.natAbs j.natAbs : ℕ) : ℤ) ((min i.natAbs j.natAbs : ℕ) : ℤ) := by
  rw [cell_natAbs]
  rcases le_total i.natAbs j.natAbs with h | h
  · rw [max_eq_right h, min_eq_left h, cell_swap]
  · rw [max_eq_left h, min_eq_right h]

private lemma cell_outside (t : ℕ) (i j : ℤ) (h : t < i.natAbs + j.natAbs) :
    cell 137 t i j = decide (t % 2 = 1) := by
  induction t generalizing i j with
  | zero =>
    simp only [cell]
    have hne : ¬(i = 0 ∧ j = 0) := by omega
    simp [hne]
  | succ t ih =>
    rw [cell_succ, ih i j (by omega), ih (i + 1) j (by omega),
        ih (i - 1) j (by omega), ih i (j + 1) (by omega), ih i (j - 1) (by omega)]
    have hmod : t % 2 = 0 ∨ t % 2 = 1 := by omega
    rcases hmod with hm | hm
    · have hm1 : (t + 1) % 2 = 1 := by omega
      simp [hm, hm1, rule137]
    · have hm1 : (t + 1) % 2 ≠ 1 := by omega
      simp [hm, hm1, rule137]

private def bit137 (m k : ℕ) : Bool := (m / 2 ^ k) % 2 == 1

private def gridRow : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 2, 0 => 5
  | 3, 1 => 2
  | 4, 0 => 21
  | 5, 1 => 10 | 5, 2 => 12
  | 6, 0 => 85 | 6, 1 => 8 | 6, 2 => 16
  | 7, 1 => 34 | 7, 2 => 4 | 7, 3 => 8
  | 8, 0 => 349 | 8, 1 => 8 | 8, 2 => 16
  | 9, 0 => 20 | 9, 1 => 170 | 9, 2 => 196 | 9, 3 => 104 | 9, 4 => 48
  | 10, 0 => 1345 | 10, 1 => 128 | 10, 2 => 272
  | 11, 0 => 28 | 11, 1 => 558 | 11, 2 => 68 | 11, 3 => 232 | 11, 4 => 240 | 11, 5 => 96
  | 12, 0 => 5589 | 12, 1 => 128 | 12, 2 => 336 | 12, 4 => 256
  | 13, 0 => 320 | 13, 1 => 2730 | 13, 2 => 3076 | 13, 3 => 1704 | 13, 4 => 112 | 13, 5 => 224 | 13, 6 => 192
  | 14, 0 => 21525 | 14, 1 => 2048 | 14, 2 => 4432 | 14, 3 => 544 | 14, 4 => 1280 | 14, 6 => 256
  | 15, 0 => 448 | 15, 1 => 8874 | 15, 2 => 1028 | 15, 3 => 2184 | 15, 4 => 80 | 15, 5 => 736 | 15, 6 => 64 | 15, 7 => 128
  | 16, 0 => 89429 | 16, 1 => 2176 | 16, 2 => 4432 | 16, 3 => 544 | 16, 4 => 1344 | 16, 5 => 128 | 16, 6 => 256
  | 17, 0 => 5120 | 17, 1 => 43562 | 17, 2 => 50180 | 17, 3 => 26760 | 17, 4 => 12304 | 17, 5 => 6688 | 17, 6 => 3136 | 17, 7 => 1664 | 17, 8 => 768
  | 18, 0 => 344533 | 18, 1 => 32896 | 18, 2 => 69968 | 18, 3 => 544 | 18, 4 => 1344 | 18, 5 => 128 | 18, 6 => 256
  | 19, 0 => 7488 | 19, 1 => 143018 | 19, 2 => 17412 | 19, 3 => 59528 | 19, 4 => 61456 | 19, 5 => 31264 | 19, 6 => 15424 | 19, 7 => 7808 | 19, 8 => 3840 | 19, 9 => 1536
  | 20, 0 => 1430549 | 20, 1 => 33280 | 20, 2 => 87376 | 20, 3 => 544 | 20, 4 => 66880 | 20, 5 => 128 | 20, 6 => 256
  | _, _ => 0

private def gridVal (t i j : ℕ) : Bool :=
  if t < i + j then decide (t % 2 = 1) else bit137 (gridRow t (min i j)) (max i j)

private lemma gridVal_symm (t i j : ℕ) : gridVal t j i = gridVal t i j := by
  simp only [gridVal, Nat.add_comm j i, min_comm j i, max_comm j i]

private def stepGridVal (t i j : ℕ) : Bool :=
  rule137
    (gridVal t i j)
    (gridVal t (i + 1) j)
    (gridVal t (if i = 0 then 1 else i - 1) j)
    (gridVal t i (j + 1))
    (gridVal t i (if j = 0 then 1 else j - 1))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private lemma gridVal_step_ok :
    ∀ t : Fin 20, ∀ i : Fin 21, ∀ j : Fin 21,
      i.val + j.val ≤ t.val + 1 → j.val ≤ i.val →
      stepGridVal t.val i.val j.val = gridVal (t.val + 1) i.val j.val := by
  decide

private lemma natAbs_sub_one (k : ℕ) :
    ((k : ℤ) - 1).natAbs = if k = 0 then 1 else k - 1 := by
  cases k with
  | zero => rfl
  | succ k => simp

private lemma cell_eq_gridVal (t : ℕ) (ht : t ≤ 20) (i j : ℤ) :
    cell 137 t i j = gridVal t i.natAbs j.natAbs := by
  induction t generalizing i j with
  | zero =>
    rw [cell_natAbs]
    set x := i.natAbs
    set y := j.natAbs
    by_cases h : 0 < x + y
    · rw [cell_outside 0 (x : ℤ) (y : ℤ) (by simpa using h)]
      simp [gridVal, h]
    · have hx : x = 0 := by omega
      have hy : y = 0 := by omega
      rw [hx, hy]
      decide
  | succ t ih =>
    rw [cell_natAbs]
    set x := i.natAbs
    set y := j.natAbs
    by_cases hout : t + 1 < x + y
    · rw [cell_outside (t + 1) (x : ℤ) (y : ℤ) (by simpa using hout)]
      simp [gridVal, hout]
    · have hle : x + y ≤ t + 1 := by omega
      suffices step : ∀ u v : ℕ, u + v ≤ t + 1 → v ≤ u →
          cell 137 (t + 1) (u : ℤ) (v : ℤ) = gridVal (t + 1) u v by
        rcases le_total y x with hyx | hxy
        · exact step x y hle hyx
        · rw [← cell_swap, ← gridVal_symm]
          exact step y x (by omega) hxy
      intro u v huv hvu
      rw [cell_succ, ih (by omega), ih (by omega), ih (by omega), ih (by omega), ih (by omega)]
      have hu1 : ((u : ℤ) + 1).natAbs = u + 1 := by omega
      have hv1 : ((v : ℤ) + 1).natAbs = v + 1 := by omega
      simp only [Int.natAbs_natCast, hu1, hv1, natAbs_sub_one]
      exact gridVal_step_ok ⟨t, by omega⟩ ⟨u, by omega⟩ ⟨v, by omega⟩ huv hvu


private def aGrid (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if gridVal n k 0 then (2 : ℤ) ^ (n - k) else 0

private lemma a_eq_aGrid (n : ℕ) (hn : n ≤ 20) : a n = aGrid n := by
  unfold a aGrid
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cell_eq_gridVal n hn (k : ℤ) 0]
  simp

private def c137 (n : ℕ) : ℤ :=
  match n % 6 with
  | 0 => 342
  | 1 => 5
  | 2 => 335
  | 3 => 7
  | 4 => 340
  | _ => 0

private def initial137 : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | 2 => 5
  | 3 => 0
  | 4 => 21
  | 5 => 0
  | 6 => 85
  | 7 => 0
  | 8 => 373
  | 9 => 160
  | 10 => 1045
  | 11 => 896
  | 12 => 5493
  | 13 => 160
  | 14 => 21525
  | 15 => 896
  | _ => 0

private lemma c137_rec (n : ℕ) (hn : 4 ≤ n) :
    c137 n = -c137 (n - 1) + c137 (n - 3) + c137 (n - 4) := by
  have hnmod : n % 6 < 6 := Nat.mod_lt _ (by decide)
  generalize h : n % 6 = r at hnmod
  have h₁ : (n - 1) % 6 = (r + 5) % 6 := by omega
  have h₃ : (n - 3) % 6 = (r + 3) % 6 := by omega
  have h₄ : (n - 4) % 6 = (r + 2) % 6 := by omega
  unfold c137
  rw [h, h₁, h₃, h₄]
  interval_cases r <;> decide

private lemma recur137 (b : ℕ → ℤ)
    (hshift : ∀ n, 12 ≤ n → b n - b (n - 8) = (2 : ℤ) ^ (n - 8) * c137 n)
    (n : ℕ) (hn : 16 ≤ n) :
    (b n : ℚ) = -2 * b (n - 1) + 8 * b (n - 3) + 16 * b (n - 4) +
      b (n - 8) + 2 * b (n - 9) - 8 * b (n - 11) - 16 * b (n - 12) := by
  have h₀ := hshift n (by omega)
  have h₁ := hshift (n - 1) (by omega)
  have h₃ := hshift (n - 3) (by omega)
  have h₄ := hshift (n - 4) (by omega)
  rw [show n - 1 - 8 = n - 9 by omega] at h₁
  rw [show n - 3 - 8 = n - 11 by omega] at h₃
  rw [show n - 4 - 8 = n - 12 by omega] at h₄
  have h : b n - b (n - 8) =
      -2 * (b (n - 1) - b (n - 9)) + 8 * (b (n - 3) - b (n - 11)) +
        16 * (b (n - 4) - b (n - 12)) := by
    rw [h₀, h₁, h₃, h₄, c137_rec n (by omega),
      show n - 8 = (n - 12) + 4 by omega, show n - 9 = (n - 12) + 3 by omega,
      show n - 11 = (n - 12) + 1 by omega]
    simp only [pow_add]
    ring
  have h' : b n = -2 * b (n - 1) + 8 * b (n - 3) + 16 * b (n - 4) +
      b (n - 8) + 2 * b (n - 9) - 8 * b (n - 11) - 16 * b (n - 12) := by linarith
  exact_mod_cast h'

open PowerSeries in
private lemma gf137 (b : ℕ → ℤ)
    (hinit : ∀ n, n < 16 → b n = initial137 n)
    (hrec : ∀ n : ℕ, 16 ≤ n → (b n : ℚ) =
      -2 * b (n - 1) + 8 * b (n - 3) + 16 * b (n - 4) + b (n - 8) +
      2 * b (n - 9) - 8 * b (n - 11) - 16 * b (n - 12)) :
    mk (fun n => (b n : ℚ)) *
      (16 * X ^ 12 + 8 * X ^ 11 - 2 * X ^ 9 - X ^ 8 - 16 * X ^ 4 - 8 * X ^ 3 + 2 * X + 1 :
        PowerSeries ℚ) =
    -14336 * X ^ 15 - 2048 * X ^ 14 + 224 * X ^ 13 + 32 * X ^ 12 + 224 * X ^ 9 + 36 * X ^ 8 +
      2 * X ^ 7 + 5 * X ^ 6 + 2 * X ^ 5 + 5 * X ^ 4 + 2 * X ^ 3 + 5 * X ^ 2 + 2 * X + 1 := by
  set F : PowerSeries ℚ := mk (fun n => (b n : ℚ)) with hF
  have lhs : F *
      (16 * X ^ 12 + 8 * X ^ 11 - 2 * X ^ 9 - X ^ 8 - 16 * X ^ 4 - 8 * X ^ 3 + 2 * X + 1 :
        PowerSeries ℚ) =
      F + (16 : ℤ) • (F * X ^ 12) + (8 : ℤ) • (F * X ^ 11) + (-2 : ℤ) • (F * X ^ 9) +
        (-1 : ℤ) • (F * X ^ 8) + (-16 : ℤ) • (F * X ^ 4) + (-8 : ℤ) • (F * X ^ 3) +
        (2 : ℤ) • (F * X ^ 1) := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  have rhs :
      (-14336 * X ^ 15 - 2048 * X ^ 14 + 224 * X ^ 13 + 32 * X ^ 12 + 224 * X ^ 9 + 36 * X ^ 8 +
        2 * X ^ 7 + 5 * X ^ 6 + 2 * X ^ 5 + 5 * X ^ 4 + 2 * X ^ 3 + 5 * X ^ 2 + 2 * X + 1 :
        PowerSeries ℚ) =
      (-14336 : ℤ) • X ^ 15 + (-2048 : ℤ) • X ^ 14 + (224 : ℤ) • X ^ 13 + (32 : ℤ) • X ^ 12 +
        (224 : ℤ) • X ^ 9 + (36 : ℤ) • X ^ 8 + (2 : ℤ) • X ^ 7 + (5 : ℤ) • X ^ 6 +
        (2 : ℤ) • X ^ 5 + (5 : ℤ) • X ^ 4 + (2 : ℤ) • X ^ 3 + (5 : ℤ) • X ^ 2 +
        (2 : ℤ) • X ^ 1 + (1 : ℤ) • X ^ 0 := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [lhs, rhs]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow]
  simp only [zsmul_eq_mul]
  by_cases hn : 16 ≤ n
  · have hr := hrec n hn
    simp only [show 12 ≤ n by omega, show 11 ≤ n by omega, show 9 ≤ n by omega,
      show 8 ≤ n by omega, show 4 ≤ n by omega, show 3 ≤ n by omega, show 1 ≤ n by omega,
      show n ≠ 15 by omega, show n ≠ 14 by omega, show n ≠ 13 by omega,
      show n ≠ 12 by omega, show n ≠ 9 by omega, show n ≠ 8 by omega, show n ≠ 7 by omega,
      show n ≠ 6 by omega, show n ≠ 5 by omega, show n ≠ 4 by omega, show n ≠ 3 by omega,
      show n ≠ 2 by omega, show n ≠ 1 by omega, show n ≠ 0 by omega, ite_true, ite_false]
    push_cast
    linarith
  · rw [hinit n (by omega), hinit (n - 12) (by omega), hinit (n - 11) (by omega),
      hinit (n - 9) (by omega), hinit (n - 8) (by omega), hinit (n - 4) (by omega),
      hinit (n - 3) (by omega), hinit (n - 1) (by omega)]
    interval_cases n <;> norm_num [initial137]


private lemma a_eq_initial137 (n : ℕ) (hn : n < 16) : a n = initial137 n := by
  rw [a_eq_aGrid n (by omega)]
  have h : ∀ j : Fin 16, aGrid j.val = initial137 j.val := by decide
  exact h ⟨n, hn⟩

private lemma axis_shift (h₁ : ∀ t x : ℕ, 4 ≤ t → 0 < x → x ≤ t → cell 137 (t + 8) ((x + 8 : ℕ) : ℤ) 0 =
      cell 137 t (x : ℤ) 0) (h₂ : ∀ t : ℕ, 4 ≤ t →
      (∑ x ∈ Finset.range 9, if cell 137 (t + 8) (x : ℤ) 0 then (2 : ℤ) ^ (8 - x) else 0) -
        (if cell 137 t 0 0 then 1 else 0) = c137 (t + 8)) (t : ℕ) (ht : 4 ≤ t) :
    a (t + 8) - a t = (2 : ℤ) ^ t * c137 (t + 8) := by
  unfold a
  rw [show t + 8 + 1 = 9 + t by omega, Finset.sum_range_add,
    Finset.sum_range_succ' (fun k => if cell 137 t (k : ℤ) 0 then (2 : ℤ) ^ (t - k) else 0)]
  have htail :
      (∑ x ∈ Finset.range t, if cell 137 (t + 8) ((9 + x : ℕ) : ℤ) 0
        then (2 : ℤ) ^ (t + 8 - (9 + x)) else 0) =
      ∑ x ∈ Finset.range t, if cell 137 t ((x + 1 : ℕ) : ℤ) 0
        then (2 : ℤ) ^ (t - (x + 1)) else 0 := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.mp hx
    rw [show 9 + x = x + 1 + 8 by omega, h₁ t (x + 1) ht (by omega) (by omega),
      show t + 8 - (x + 1 + 8) = t - (x + 1) by omega]
  have hfront :
      (∑ x ∈ Finset.range 9, if cell 137 (t + 8) (x : ℤ) 0
        then (2 : ℤ) ^ (t + 8 - x) else 0) =
      (2 : ℤ) ^ t *
        ∑ x ∈ Finset.range 9, if cell 137 (t + 8) (x : ℤ) 0 then (2 : ℤ) ^ (8 - x) else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.mp hx
    rw [show t + 8 - x = t + (8 - x) by omega, pow_add]
    split <;> simp_all
  have hzero :
      (if cell 137 t (0 : ℤ) 0 then (2 : ℤ) ^ (t - 0) else 0) =
      (2 : ℤ) ^ t * (if cell 137 t (0 : ℤ) 0 then 1 else 0) := by
    split <;> simp_all
  rw [htail, hfront]
  simp only [Nat.cast_zero]
  rw [hzero]
  linear_combination (2 : ℤ) ^ t * (h₂ t ht)

private lemma diff8 (h₁ : ∀ t x : ℕ, 4 ≤ t → 0 < x → x ≤ t → cell 137 (t + 8) ((x + 8 : ℕ) : ℤ) 0 =
      cell 137 t (x : ℤ) 0) (h₂ : ∀ t : ℕ, 4 ≤ t →
      (∑ x ∈ Finset.range 9, if cell 137 (t + 8) (x : ℤ) 0 then (2 : ℤ) ^ (8 - x) else 0) -
        (if cell 137 t 0 0 then 1 else 0) = c137 (t + 8)) (n : ℕ) (hn : 12 ≤ n) :
    a n - a (n - 8) = (2 : ℤ) ^ (n - 8) * c137 n := by
  have h := axis_shift h₁ h₂ (n - 8) (by omega)
  simpa only [show n - 8 + 8 = n by omega] using h

namespace OMA.R_oeis_a279144_R1

/-- The positive positions on the axis are preserved when the frontier advances eight cells. -/
def H1 : Prop :=
  ∀ t x : ℕ, 4 ≤ t → 0 < x → x ≤ t → cell 137 (t + 8) ((x + 8 : ℕ) : ℤ) 0 =
    cell 137 t (x : ℤ) 0

/-- The nine cells nearest the origin supply the change in the axis value. -/
def H2 : Prop :=
  ∀ t : ℕ, 4 ≤ t →
    (∑ x ∈ Finset.range 9, if cell 137 (t + 8) (x : ℤ) 0 then (2 : ℤ) ^ (8 - x) else 0) -
      (if cell 137 t 0 0 then 1 else 0) = c137 (t + 8)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a279144.main := by
  intro h₁ h₂
  exact ⟨recur137 a (diff8 h₁ h₂), gf137 a a_eq_initial137 (recur137 a (diff8 h₁ h₂))⟩

end OMA.R_oeis_a279144_R1
