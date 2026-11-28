import OMAStatements.S_oeis_a278754

namespace Adapt278754

open PowerSeries


def state (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t+1, x, y =>
    let s := state r t
    r.testBit ((s x y).toNat + 2 * ((s (x-1) y).toNat + (s (x+1) y).toNat +
      (s x (y-1)).toNat + (s x (y+1)).toNat))


def digits (r n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n+1), ((state r n (i : ℤ) 0).toNat : ℤ) * 10 ^ (n-i)

def a (n : ℕ) : ℤ := digits 65 n


open Adapt278754 PowerSeries

namespace Rule65

def ev (k x y : ℤ) : Bool := decide
  ((|x| ≤ k ∧ |y| ≤ 0) ∨ (|x| ≤ 0 ∧ |y| ≤ k) ∨ (3 ≤ k ∧ |x| ≤ 1 ∧ |y| ≤ 1))

def od (k x y : ℤ) : Bool := decide
  (¬ ((|x| ≤ k+1 ∧ |y| ≤ 0) ∨ (|y| ≤ k+1 ∧ |x| ≤ 0) ∨
    (|x| ≤ k ∧ |y| ≤ 1) ∨ (|y| ≤ k ∧ |x| ≤ 1)))

def step65 (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  (65 : ℕ).testBit ((s x y).toNat + 2 * ((s (x-1) y).toNat + (s (x+1) y).toNat +
    (s x (y-1)).toNat + (s x (y+1)).toNat))

def foldCoord (k z : ℤ) : ℤ :=
  if k ≤ 6 then max (-9) (min 9 z)
  else if 4 ≤ z then min 9 (max 4 (z-k+6))
  else if z ≤ -4 then max (-9) (min (-4) (z+k-6))
  else z

lemma bounds (k z : ℤ) : -9 ≤ foldCoord k z ∧ foldCoord k z ≤ 9 := by
  simp only [foldCoord, min_def, max_def]
  split_ifs <;> omega

lemma small (k z d b : ℤ) (hd : -1 ≤ d ∧ d ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    |z+d| ≤ b ↔ |foldCoord k z+d| ≤ b := by
  simp only [foldCoord, abs_le, min_def, max_def]
  split_ifs <;> omega

lemma large (k z d b : ℤ) (hd : -1 ≤ d ∧ d ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    |z+d| ≤ k+b ↔ |foldCoord k z+d| ≤ min k 6+b := by
  simp only [foldCoord, abs_le, min_def, max_def]
  split_ifs <;> omega

lemma ev_move (k x y d e b : ℤ) (hd : -1 ≤ d ∧ d ≤ 1) (he : -1 ≤ e ∧ e ≤ 1)
    (hb : 0 ≤ b ∧ b ≤ 1) :
    ev (k+b) (x+d) (y+e) = ev (min k 6+b) (foldCoord k x+d) (foldCoord k y+e) := by
  have hk : 3 ≤ k+b ↔ 3 ≤ min k 6+b := by omega
  simp only [ev, small k x d 0 hd (by decide), small k y e 0 he (by decide),
    small k x d 1 hd (by decide), small k y e 1 he (by decide),
    large k x d b hd hb, large k y e b he hb, hk]

lemma od_move (k x y d e : ℤ) (hd : -1 ≤ d ∧ d ≤ 1) (he : -1 ≤ e ∧ e ≤ 1) :
    od k (x+d) (y+e) = od (min k 6) (foldCoord k x+d) (foldCoord k y+e) := by
  have lx := large k x d 0 hd (by decide)
  have ly := large k y e 0 he (by decide)
  simp only [add_zero] at lx ly
  simp only [od, small k x d 0 hd (by decide), small k y e 0 he (by decide),
    small k x d 1 hd (by decide), small k y e 1 he (by decide),
    large k x d 1 hd (by decide), large k y e 1 he (by decide), lx, ly]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma finite_steps : ∀ k : Fin 7, ∀ i j : Fin 19,
    step65 (ev k) ((i : ℤ)-9) ((j : ℤ)-9) = od k ((i : ℤ)-9) ((j : ℤ)-9) ∧
    step65 (od k) ((i : ℤ)-9) ((j : ℤ)-9) = ev (k+1) ((i : ℤ)-9) ((j : ℤ)-9) := by
  decide +kernel

lemma steps (k : ℕ) (x y : ℤ) :
    step65 (ev k) x y = od k x y ∧ step65 (od k) x y = ev (k+1) x y := by
  let z := min (k : ℤ) 6
  have hx := bounds k x
  have hy := bounds k y
  have hz : 0 ≤ z ∧ z ≤ 6 := by dsimp [z]; omega
  have h := finite_steps ⟨z.toNat, by omega⟩
    ⟨(foldCoord k x+9).toNat, by omega⟩ ⟨(foldCoord k y+9).toNat, by omega⟩
  change step65 (ev (z.toNat : ℤ)) (((foldCoord k x+9).toNat : ℤ)-9)
    (((foldCoord k y+9).toNat : ℤ)-9) = _ ∧ _ at h
  have xx : ((foldCoord k x+9).toNat : ℤ)-9 = foldCoord k x := by omega
  have yy : ((foldCoord k y+9).toNat : ℤ)-9 = foldCoord k y := by omega
  have zz : (z.toNat : ℤ) = z := by omega
  simp only [xx, yy, zz, z, step65] at h
  have E := fun (d e : ℤ) (hd : -1 ≤ d ∧ d ≤ 1) (he : -1 ≤ e ∧ e ≤ 1) =>
    ev_move k x y d e 0 hd he (by decide)
  have O := od_move k x y
  have E0 := E (0) (0) (by decide) (by decide)
  have O1 := O (0) (0) (by decide) (by decide)
  have E2 := E (-1) (0) (by decide) (by decide)
  have O3 := O (-1) (0) (by decide) (by decide)
  have E4 := E (1) (0) (by decide) (by decide)
  have O5 := O (1) (0) (by decide) (by decide)
  have E6 := E (0) (-1) (by decide) (by decide)
  have O7 := O (0) (-1) (by decide) (by decide)
  have E8 := E (0) (1) (by decide) (by decide)
  have O9 := O (0) (1) (by decide) (by decide)
  have E1next := ev_move k x y 0 0 1 (by decide) (by decide) (by decide)
  simp only [add_zero] at E0 O1 E2 O3 E4 O5 E6 O7 E8 O9 E1next
  simp only [step65, sub_eq_add_neg, E0, O1, E2, O3, E4, O5, E6, O7, E8, O9, E1next]
  simpa only [sub_eq_add_neg] using h


lemma states (k : ℕ) : state 65 (2*k) = ev k ∧ state 65 (2*k+1) = od k := by
  have next (t : ℕ) : state 65 (t+1) = step65 (state 65 t) := rfl
  suffices h : state 65 (2*k) = ev k by
    refine ⟨h, ?_⟩
    rw [next, h]
    funext x y
    exact (steps k x y).1
  induction k with
  | zero =>
    funext x y
    change decide (x = 0 ∧ y = 0) = ev 0 x y
    unfold ev
    congr 1
    apply propext
    simp only [abs_le]
    omega
  | succ k ih =>
    have ho : state 65 (2*k+1) = od k := by
      rw [next, ih]
      funext x y
      exact (steps k x y).1
    rw [show 2*(k+1) = (2*k+1)+1 by omega, next, ho]
    funext x y
    exact (steps k x y).2

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
    (fun i => state 65 (2*k) (i : ℤ) 0)
  intro i hi
  rw [(states k).1]
  simp only [ev]
  congr 1
  apply propext
  simp only [abs_le, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  omega

lemma wordOdd (k : ℕ) : a (2*k+1) * (10-1) =
    (10 : ℤ)^(k) - 10^(0) := by
  apply digitBlock 10 (2*k+1) (0) (k) (by omega) (by omega)
    (fun i => state 65 (2*k+1) (i : ℤ) 0)
  intro i hi
  rw [(states k).2]
  simp only [od]
  congr 1
  apply propext
  simp only [abs_le, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
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

end Rule65

open Rule65


lemma previous : (∀ n : ℕ, 5 < n → a n = 111 * a (n - 2) - 1110 * a (n - 4) + 1000 * a (n - 6)) ∧
    (PowerSeries.mk a * (1000 * X ^ 6 - 1110 * X ^ 4 + 111 * X ^ 2 - 1) =
      100 * X ^ 5 - X ^ 3 + X ^ 2 - 1) := by
  refine ⟨recurrence, ?_⟩
  have hd : mk a * (1000 * X ^ 6 - 1110 * X ^ 4 + 111 * X ^ 2 - 1) =
      (-1 : ℤ) • (mk a * X ^ 0)
      + (111 : ℤ) • (mk a * X ^ 2)
      + (-1110 : ℤ) • (mk a * X ^ 4)
      + (1000 : ℤ) • (mk a * X ^ 6) := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  have hp : (100 * X ^ 5 - X ^ 3 + X ^ 2 - 1 : PowerSeries ℤ) =
      (-1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (-1 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (100 : ℤ) • (X ^ 5 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [hd, hp]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
  by_cases hn : n < 6
  · have ha0 : a 0 = 1 := by decide
    have ha1 : a 1 = 0 := by decide
    have ha2 : a 2 = 110 := by decide
    have ha3 : a 3 = 1 := by decide
    have ha4 : a 4 = 11100 := by decide
    have ha5 : a 5 = 11 := by decide
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

lemma cell_bridge (n : ℕ) (x y : ℤ) : OMA.S_oeis_a278754.cell 65 n x y = state 65 n x y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    simp only [OMA.S_oeis_a278754.cell, state, ih]
    congr 1
    omega

lemma value_bridge (n : ℕ) : OMA.S_oeis_a278754.a n = (a n : ℤ) := by
  unfold OMA.S_oeis_a278754.a a digits
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
end Adapt278754

open Adapt278754 (value_bridge map_series previous)

theorem OMA.solution : type_of% @OMA.S_oeis_a278754.main := by
  simp only [value_bridge]
  obtain ⟨hrec, hgf⟩ := previous
  refine ⟨?_ , ?_ ⟩
  · intro n hn
    exact_mod_cast hrec n hn
  · have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) hgf
    simpa only [map_mul, map_one, map_add, map_sub, map_pow, map_neg, map_ofNat, PowerSeries.map_X, map_series, Int.cast_natCast] using h
