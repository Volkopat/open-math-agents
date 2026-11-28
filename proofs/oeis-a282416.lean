import OMAStatements.S_oeis_a282416

namespace Adapt282416

open PowerSeries


def state (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t+1, x, y =>
    let s := state r t
    r.testBit ((s x y).toNat + 2 * ((s (x-1) y).toNat + (s (x+1) y).toNat +
      (s x (y-1)).toNat + (s x (y+1)).toNat))


def digits (r n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n+1), ((state r n (i : ℤ) 0).toNat : ℤ) * 10 ^ (n-i)

def a (n : ℕ) : ℤ := digits 469 n


open Adapt282416 PowerSeries

namespace Rule469

def update (c l r u d : Bool) : Bool :=
  (469 : ℕ).testBit (c.toNat+2*(l.toNat+r.toNat+u.toNat+d.toNat))

lemma step (t : ℕ) (x y : ℤ) : state 469 (t+1) x y =
    update (state 469 t x y) (state 469 t (x-1) y) (state 469 t (x+1) y)
      (state 469 t x (y-1)) (state 469 t x (y+1)) := rfl

lemma from_off (l r u d : Bool) : update false l r u d = true := by
  cases l <;> cases r <;> cases u <;> cases d <;> decide

lemma paired (l u : Bool) : update true l l u u = false := by
  cases l <;> cases u <;> decide

lemma reflections (n : ℕ) (x y : ℤ) :
    state 469 n (-x) y = state 469 n x y ∧ state 469 n x (-y) = state 469 n x y := by
  induction n generalizing x y with
  | zero => simp [state]
  | succ n ih =>
    simp only [step, update, show -x-1=-(x+1) by omega, show -x+1=-(x-1) by omega,
      show -y-1=-(y+1) by omega, show -y+1=-(y-1) by omega,
      (ih _ _).1, (ih _ _).2]
    constructor <;> congr 2 <;> omega

def bounded (k : ℕ) : Prop := ∀ x y : ℤ, (k : ℤ) < |x|+|y| → state 469 (2*k) x y = false

def fullAxis (k : ℕ) : Prop := ∀ x : ℕ, x ≤ k → state 469 (2*k) (x : ℤ) 0 = true

lemma outside_odd {k : ℕ} (B : bounded k) (x y : ℤ) (h : (k : ℤ) < |x|+|y|) :
    state 469 (2*k+1) x y = true := by
  rw [step, B x y h, from_off]

lemma off_axis {k : ℕ} (B : bounded k) (A : fullAxis k) (x : ℕ) (hx : x ≤ k) :
    state 469 (2*k+1) (x : ℤ) 0 = false := by
  rw [step, A x hx]
  simp only [zero_sub, zero_add, (reflections (2*k) (x : ℤ) 1).2]
  by_cases z : x=0
  · subst x
    simp only [Nat.cast_zero, zero_sub, zero_add, (reflections (2*k) 1 0).1, paired]
  have L : state 469 (2*k) ((x : ℤ)-1) 0 = true := by
    rw [show (x : ℤ)-1=((x-1 : ℕ) : ℤ) by omega]
    exact A _ (by omega)
  rw [L]
  by_cases e : x=k
  · subst x
    rw [B ((k : ℤ)+1) 0 (by simp [abs_of_nonneg (by omega : (0 : ℤ) ≤ (k : ℤ)+1)]),
        B k 1 (by simp)]
    decide
  · have R : state 469 (2*k) ((x : ℤ)+1) 0 = true := A (x+1) (by omega)
    rw [R, paired]

lemma invariant (k : ℕ) : bounded k ∧ fullAxis k := by
  induction k with
  | zero =>
    constructor
    · intro x y h
      simp only [Nat.mul_zero, state, decide_eq_false_iff_not]
      rintro ⟨rfl,rfl⟩
      simp at h
    · intro x h
      obtain rfl : x=0 := by omega
      decide
  | succ k ih =>
    obtain ⟨B,A⟩ := ih
    have O := outside_odd B
    have offs := off_axis B A
    have dist (x : ℤ) : |x| ≤ |x-1|+1 ∧ |x| ≤ |x+1|+1 := by
      simp only [abs, max_def]; split_ifs <;> omega
    constructor
    · intro x y h
      rw [show 2*(k+1)=2*k+1+1 by omega, step]
      have dx := dist x
      have dy := dist y
      rw [O x y (by omega), O (x-1) y (by omega), O (x+1) y (by omega),
        O x (y-1) (by omega), O x (y+1) (by omega)]
      decide
    · intro x hx
      rw [show 2*(k+1)=2*k+1+1 by omega, step]
      by_cases h : x ≤ k
      · rw [offs x h, from_off]
      · obtain rfl : x=k+1 := by omega
        rw [show ((k+1 : ℕ) : ℤ)-1=(k : ℤ) by omega, offs k (by omega)]
        have h1 := le_abs_self ((k : ℤ)+1)
        have h2 := le_abs_self ((k : ℤ)+1+1)
        rw [O (k+1 : ℕ) 0 (by simp; omega), O (((k+1 : ℕ) : ℤ)+1) 0 (by simp; omega),
          O (k+1 : ℕ) (0-1) (by simp; omega), O (k+1 : ℕ) (0+1) (by simp; omega)]
        decide

lemma axis_even (k : ℕ) (x : ℤ) : state 469 (2*k) x 0 = decide (|x| ≤ k) := by
  have hv : state 469 (2*k) (x.natAbs : ℤ) 0 = state 469 (2*k) x 0 := by
    cases x with
    | ofNat a => rfl
    | negSucc a => exact ((reflections (2*k) (a+1 : ℕ) 0).1).symm
  have hxabs : (x.natAbs : ℤ) = |x| := Int.natCast_natAbs x
  rw [← hv]
  by_cases h : x.natAbs ≤ k
  · rw [(invariant k).2 _ h]; simp; omega
  · rw [(invariant k).1 _ _ (by simp; omega)]; simp; omega

lemma axis_odd (k : ℕ) (x : ℤ) : state 469 (2*k+1) x 0 = decide ((k : ℤ) < |x|) := by
  have hv : state 469 (2*k+1) (x.natAbs : ℤ) 0 = state 469 (2*k+1) x 0 := by
    cases x with
    | ofNat a => rfl
    | negSucc a => exact ((reflections (2*k+1) (a+1 : ℕ) 0).1).symm
  have hxabs : (x.natAbs : ℤ) = |x| := Int.natCast_natAbs x
  rw [← hv]
  by_cases h : x.natAbs ≤ k
  · rw [off_axis (invariant k).1 (invariant k).2 _ h]; simp; omega
  · rw [outside_odd (invariant k).1 _ _ (by simp; omega)]; simp; omega


lemma digitBlock (b : ℤ) (n l h : ℕ) (hl : l ≤ h) (hh : h ≤ n+1) (s : ℕ → Bool)
    (hs : ∀ i ≤ n, s i = decide (l ≤ n-i ∧ n-i < h)) :
    (∑ i ∈ Finset.range (n+1), ((s i).toNat : ℤ) * b^(n-i)) * (b-1) = b^h-b^l := by
  have hr : (∑ i ∈ Finset.range (n+1), ((s i).toNat : ℤ) * b^(n-i)) =
      ∑ i ∈ Finset.Ico l h, b^i := by
    rw [← Finset.sum_range_reflect (fun i => ((s i).toNat : ℤ)*b^(n-i)) (n+1)]
    have filt : (Finset.range (n+1)).filter (fun i => l ≤ i ∧ i < h) = Finset.Ico l h := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [← filt, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    simp only [Nat.add_sub_cancel, hs (n-i) (by omega), show n-(n-i) = i by omega]
    by_cases p : l ≤ i ∧ i < h <;> simp [p]
  rw [hr, Finset.sum_Ico_eq_sub _ hl, sub_mul, geom_sum_mul, geom_sum_mul]
  ring

lemma wordEven (k : ℕ) : a (2*k) * (10-1) =
    (10 : ℤ)^(2*k+1) - 10^(k) := by
  apply digitBlock 10 (2*k) (k) (2*k+1) (by omega) (by omega)
    (fun i => state 469 (2*k) (i : ℤ) 0)
  intro i hi
  rw [axis_even]
  congr 1
  apply propext
  simp only [abs_le, lt_abs, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  omega

lemma wordOdd (k : ℕ) : a (2*k+1) * (10-1) =
    (10 : ℤ)^(k+1) - 10^(0) := by
  apply digitBlock 10 (2*k+1) (0) (k+1) (by omega) (by omega)
    (fun i => state 469 (2*k+1) (i : ℤ) 0)
  intro i hi
  rw [axis_odd]
  congr 1
  apply propext
  simp only [abs_le, lt_abs, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  omega

lemma recurrence (n : ℕ) (hn : 5 < n) :
    a n = 111*a (n-2) - 1110*a (n-4) + 1000*a (n-6) := by
  obtain ⟨k, hk | hk⟩ : ∃ k : ℕ, n=2*(k+3) ∨ n=2*(k+3)+1 := by
    exact ⟨n/2-3, by omega⟩
  · subst n
    have h0 := wordEven k
    have h1 := wordEven (k+1)
    have h2 := wordEven (k+2)
    have h3 := wordEven (k+3)
    have target : a (2*(k+3)) = 111*a (2*(k+2)) - 1110*a (2*(k+1)) + 1000*a (2*(k+0)) := by
      simp only [Nat.mul_add, pow_add, pow_mul] at h0 h1 h2 h3
      norm_num at h0 h1 h2 h3
      simp only [Nat.mul_add, Nat.reduceMul, Nat.add_zero] at *
      linarith only [h0, h1, h2, h3]
    convert target using 2 <;> congr 2 <;> omega
  · subst n
    have h0 := wordOdd k
    have h1 := wordOdd (k+1)
    have h2 := wordOdd (k+2)
    have h3 := wordOdd (k+3)
    have target : a (2*(k+3)+1) = 111*a (2*(k+2)+1) - 1110*a (2*(k+1)+1) + 1000*a (2*(k+0)+1) := by
      simp only [Nat.mul_add, pow_add, pow_mul] at h0 h1 h2 h3
      norm_num at h0 h1 h2 h3
      simp only [Nat.mul_add, Nat.reduceMul, Nat.add_zero] at *
      linarith only [h0, h1, h2, h3]
    convert target using 2 <;> congr 2 <;> omega

end Rule469

open Rule469


lemma previous : (∀ n : ℕ, 5 < n → a n = 111 * a (n - 2) - 1110 * a (n - 4) + 1000 * a (n - 6)) ∧
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) =
      1 + X - X ^ 2 - 100 * X ^ 3) := by
  refine ⟨recurrence, ?_⟩
  have hd : mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) =
      (1 : ℤ) • (mk a * X ^ 0)
      + (-111 : ℤ) • (mk a * X ^ 2)
      + (1110 : ℤ) • (mk a * X ^ 4)
      + (-1000 : ℤ) • (mk a * X ^ 6) := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  have hp : (1 + X - X ^ 2 - 100 * X ^ 3 : PowerSeries ℤ) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (-1 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (-100 : ℤ) • (X ^ 3 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [hd, hp]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
  by_cases hn : n < 6
  · have ha0 : a 0 = 1 := by decide
    have ha1 : a 1 = 1 := by decide
    have ha2 : a 2 = 110 := by decide
    have ha3 : a 3 = 11 := by decide
    have ha4 : a 4 = 11100 := by decide
    have ha5 : a 5 = 111 := by decide
    interval_cases n <;> norm_num [zsmul_eq_mul, ha0, ha1, ha2, ha3, ha4, ha5]
  · have hr := recurrence n (by omega)
    simp only [if_pos (show 0 ≤ n by omega), Nat.sub_zero, zsmul_eq_mul,
      if_pos (show 2 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_pos (show 6 ≤ n by omega),
      if_neg (show n ≠ 0 by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega)]
    norm_num
    linarith only [hr]

lemma cell_bridge (n : ℕ) (x y : ℤ) : OMA.S_oeis_a282416.cell 469 n x y = state 469 n x y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    simp only [OMA.S_oeis_a282416.cell, state, ih]
    congr 1
    omega

lemma value_bridge (n : ℕ) : OMA.S_oeis_a282416.a n = (a n : ℤ) := by
  unfold OMA.S_oeis_a282416.a a digits
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [cell_bridge]
  split <;> rename_i h
  · simp [h]
  · simp [Bool.eq_false_iff.mpr h]


lemma map_series (f : ℕ → ℤ) :
    PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk f) =
      PowerSeries.mk (fun n => (f n : ℚ)) := by
  ext n
  simp
end Adapt282416

open Adapt282416 (value_bridge map_series previous)

theorem OMA.solution : type_of% @OMA.S_oeis_a282416.main := by
  simp only [value_bridge]
  obtain ⟨hrec, hgf⟩ := previous
  refine ⟨?_ , ?_ ⟩
  · intro n hn
    exact_mod_cast hrec n hn
  · have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) hgf
    simpa only [map_mul, map_one, map_add, map_sub, map_pow, map_neg, map_ofNat, PowerSeries.map_X, map_series, Int.cast_natCast] using h
