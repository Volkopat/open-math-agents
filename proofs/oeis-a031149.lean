import OMAStatements.S_oeis_a031149

open PowerSeries
open OMA.S_oeis_a031149

namespace OMA.A031149Proof

private def step (p : ℤ × ℤ) : ℤ × ℤ :=
  (19 * p.1 + 60 * p.2, 6 * p.1 + 19 * p.2)

private def back (p : ℤ × ℤ) : ℤ × ℤ :=
  (19 * p.1 - 60 * p.2, 19 * p.2 - 6 * p.1)

private def norm (p : ℤ × ℤ) : ℤ := p.1 ^ 2 - 10 * p.2 ^ 2

/-- Positive solutions whose inverse Pell step has a negative second coordinate. -/
private def seed (i : Fin 7) : ℤ × ℤ :=
  ![(1, 0), (2, 0), (3, 0), (4, 1), (7, 2), (13, 4), (16, 5)] i

private def orbit : ℕ → Fin 7 → ℤ × ℤ
  | 0, i => seed i
  | k + 1, i => step (orbit k i)

private theorem step_back (p : ℤ × ℤ) : step (back p) = p := by
  rcases p with ⟨x, y⟩
  apply Prod.ext <;> simp [step, back] <;> ring

private theorem norm_step (p : ℤ × ℤ) : norm (step p) = norm p := by
  simp [norm, step]
  ring

private theorem norm_back (p : ℤ × ℤ) : norm (back p) = norm p := by
  have h := norm_step (back p)
  rw [step_back] at h
  exact h.symm

private theorem orbit_bounds (k : ℕ) (i : Fin 7) :
    0 < (orbit k i).1 ∧ 0 ≤ (orbit k i).2 ∧
      0 ≤ norm (orbit k i) ∧ norm (orbit k i) < 10 := by
  induction k with
  | zero => fin_cases i <;> decide
  | succ k ih =>
    rcases ih with ⟨hx, hy, hl, hu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · change 0 < 19 * (orbit k i).1 + 60 * (orbit k i).2
      omega
    · change 0 ≤ 6 * (orbit k i).1 + 19 * (orbit k i).2
      omega
    · simpa only [orbit, norm_step] using hl
    · simpa only [orbit, norm_step] using hu

private theorem step_lt (p q : ℤ × ℤ) (hx : p.1 < q.1) (hy : p.2 ≤ q.2) :
    (step p).1 < (step q).1 ∧ (step p).2 ≤ (step q).2 := by
  dsimp [step]
  omega

private theorem orbit_adjacent (k : ℕ) (i : Fin 6) :
    (orbit k ⟨i, by omega⟩).1 < (orbit k ⟨i + 1, by omega⟩).1 ∧
      (orbit k ⟨i, by omega⟩).2 ≤ (orbit k ⟨i + 1, by omega⟩).2 := by
  induction k with
  | zero => fin_cases i <;> decide
  | succ k ih => exact step_lt _ _ ih.1 ih.2

private theorem orbit_next (k : ℕ) :
    (orbit k 6).1 < (orbit (k + 1) 0).1 ∧ (orbit k 6).2 ≤ (orbit (k + 1) 0).2 := by
  induction k with
  | zero => decide
  | succ k ih => exact step_lt _ _ ih.1 ih.2

private theorem finite_seeds :
    ∀ (x : Fin 54) (y : Fin 18),
      0 < x.val → 0 ≤ norm (x.val, y.val) → norm (x.val, y.val) < 10 →
      (back (x.val, y.val)).2 < 0 → ∃ i : Fin 7, ((x.val : ℤ), (y.val : ℤ)) = seed i := by
  decide +kernel

private theorem orbit_complete (x y : ℤ) (hx : 0 < x) (hy : 0 ≤ y)
    (hl : 0 ≤ norm (x, y)) (hu : norm (x, y) < 10) :
    ∃ k i, (x, y) = orbit k i := by
  suffices key : ∀ (n : ℕ) (x y : ℤ), x.toNat = n → 0 < x → 0 ≤ y →
      0 ≤ norm (x, y) → norm (x, y) < 10 → ∃ k i, (x, y) = orbit k i from
    key x.toNat x y rfl hx hy hl hu
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hn hx hy hl hu
    have hxl : 10 * y ^ 2 ≤ x ^ 2 := by simpa [norm, sub_nonneg] using hl
    have hxu : x ^ 2 - 10 * y ^ 2 ≤ 9 := by
      change x ^ 2 - 10 * y ^ 2 < 10 at hu
      omega
    by_cases hy' : 0 ≤ (back (x, y)).2
    · have hx' : 0 < (back (x, y)).1 := by
        change 0 < 19 * x - 60 * y
        by_contra! h
        have hp := mul_nonneg (show 0 ≤ 60 * y - 19 * x by omega)
          (show 0 ≤ 60 * y + 19 * x by omega)
        have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
        nlinarith
      have hlt : (back (x, y)).1 < x := by
        change 19 * x - 60 * y < x
        change 0 ≤ 19 * y - 6 * x at hy'
        omega
      obtain ⟨k, i, hi⟩ := ih (back (x, y)).1.toNat (by omega)
        _ _ rfl hx' hy' (by rwa [norm_back]) (by rwa [norm_back])
      exact ⟨k + 1, i, by rw [orbit, ← hi, step_back]⟩
    · have hyb : y < 18 := by
        change ¬ 0 ≤ 19 * y - 6 * x at hy'
        have hp := mul_pos (show 0 < 6 * x - 19 * y by omega)
          (show 0 < 6 * x + 19 * y by omega)
        by_contra! h
        have hsq := mul_nonneg (show 0 ≤ y - 18 by omega) (show 0 ≤ y + 18 by omega)
        nlinarith
      have hxb : x < 54 := by
        have hle : y ≤ 17 := by omega
        have hp := mul_nonneg (show 0 ≤ 17 - y by omega) (show 0 ≤ 17 + y by omega)
        by_contra! h
        have hsq := mul_nonneg (show 0 ≤ x - 54 by omega) (show 0 ≤ x + 54 by omega)
        nlinarith
      let i : Fin 54 := ⟨x.toNat, by omega⟩
      let j : Fin 18 := ⟨y.toNat, by omega⟩
      have hi : (i.val : ℤ) = x := Int.toNat_of_nonneg (by omega)
      have hj : (j.val : ℤ) = y := Int.toNat_of_nonneg hy
      obtain ⟨s, hs⟩ := finite_seeds i j (by omega)
        (by rw [hi, hj]; exact hl) (by rw [hi, hj]; exact hu)
        (by rw [hi, hj]; omega)
      rw [hi, hj] at hs
      exact ⟨0, s, hs⟩

/-- Start at zero, then list the seven interleaved orbits in blocks. -/
private def enumerated : ℕ → ℕ
  | 0 => 0
  | m + 1 => (orbit (m / 7) ⟨m % 7, by omega⟩).1.toNat

private theorem enumerated_mono : StrictMono enumerated := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => decide
  | succ m =>
    change (orbit (m / 7) ⟨m % 7, by omega⟩).1.toNat <
      (orbit ((m + 1) / 7) ⟨(m + 1) % 7, by omega⟩).1.toNat
    by_cases h : m % 7 < 6
    · have hq : (m + 1) / 7 = m / 7 := by omega
      have hr : (⟨(m + 1) % 7, by omega⟩ : Fin 7) =
          ⟨(⟨m % 7, h⟩ : Fin 6).val + 1, by omega⟩ := by
        apply Fin.ext
        dsimp
        omega
      rw [hq, hr]
      have hh := (orbit_adjacent (m / 7) ⟨m % 7, h⟩).1
      have hright := (orbit_bounds (m / 7) ⟨(⟨m % 7, h⟩ : Fin 6).val + 1, by omega⟩).1
      exact (Int.toNat_lt_toNat hright).2 hh
    · have hq : (m + 1) / 7 = m / 7 + 1 := by omega
      have hr : (⟨(m + 1) % 7, by omega⟩ : Fin 7) = 0 := by
        apply Fin.ext
        change (m + 1) % 7 = 0
        omega
      have hs : (⟨m % 7, by omega⟩ : Fin 7) = 6 := by
        apply Fin.ext
        change m % 7 = 6
        omega
      rw [hq, hr, hs]
      exact (Int.toNat_lt_toNat (orbit_bounds (m / 7 + 1) 0).1).2 (orbit_next (m / 7)).1

private theorem square_iff (x : ℕ) :
    IsSquare (x ^ 2 / 10) ↔ ∃ y : ℕ, 0 ≤ norm (x, y) ∧ norm (x, y) < 10 := by
  constructor
  · rintro ⟨y, hy⟩
    have hm := Nat.mod_add_div (x ^ 2) 10
    have hb := Nat.mod_lt (x ^ 2) (by decide : 0 < 10)
    rw [hy, ← pow_two] at hm
    have hz : ((x ^ 2 : ℕ) : ℤ) = (x ^ 2 % 10 : ℕ) + 10 * (y : ℤ) ^ 2 := by
      exact_mod_cast hm.symm
    refine ⟨y, ?_, ?_⟩ <;> simp only [norm, Nat.cast_pow] at * <;> omega
  · rintro ⟨y, hl, hu⟩
    have hl' : 10 * (y ^ 2 : ℕ) ≤ x ^ 2 := by
      have hz : 10 * (y : ℤ) ^ 2 ≤ (x : ℤ) ^ 2 := by simpa [norm, sub_nonneg] using hl
      exact_mod_cast hz
    have hu' : x ^ 2 < 10 * y ^ 2 + 10 := by
      have hz : (x : ℤ) ^ 2 < 10 * (y : ℤ) ^ 2 + 10 := by
        simpa [norm, sub_lt_iff_lt_add, add_comm] using hu
      exact_mod_cast hz
    exact ⟨y, by rw [← pow_two]; omega⟩

private theorem enumerated_range :
    Set.range enumerated = {x : ℕ | IsSquare (x ^ 2 / 10)} := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    change IsSquare (enumerated n ^ 2 / 10)
    cases n with
    | zero => exact ⟨0, rfl⟩
    | succ m =>
      let p := orbit (m / 7) ⟨m % 7, by omega⟩
      have hb := orbit_bounds (m / 7) ⟨m % 7, by omega⟩
      change 0 < p.1 ∧ 0 ≤ p.2 ∧ 0 ≤ norm p ∧ norm p < 10 at hb
      apply (square_iff _).2
      change ∃ y : ℕ, 0 ≤ norm (p.1.toNat, y) ∧ norm (p.1.toNat, y) < 10
      refine ⟨p.2.toNat, ?_⟩
      rw [Int.toNat_of_nonneg (le_of_lt hb.1), Int.toNat_of_nonneg hb.2.1, Prod.mk.eta]
      exact hb.2.2
  · intro hx
    change IsSquare (x ^ 2 / 10) at hx
    by_cases hz : x = 0
    · exact ⟨0, by simpa [enumerated] using hz.symm⟩
    · obtain ⟨y, yl, yu⟩ := (square_iff x).1 hx
      obtain ⟨k, i, hi⟩ := orbit_complete (x : ℤ) (y : ℤ) (by omega) (by omega) yl yu
      refine ⟨7 * k + i.val + 1, ?_⟩
      have hq : (7 * k + i.val) / 7 = k := by omega
      have hr : (⟨(7 * k + i.val) % 7, by omega⟩ : Fin 7) = i := by
        apply Fin.ext
        change (7 * k + i.val) % 7 = i.val
        omega
      rw [enumerated, hq, hr, ← hi]
      simp

private def terms : ℕ → ℤ
  | 0 => 0
  | n + 1 => enumerated n

private theorem a_eq (n : ℕ) : (a n : ℤ) = terms n := by
  have hinf : {x : ℕ | IsSquare (x ^ 2 / 10)}.Infinite := by
    rw [← enumerated_range]
    exact Set.infinite_range_of_injective enumerated_mono.injective
  have heq : Nat.nth (fun x : ℕ => IsSquare (x ^ 2 / 10)) = enumerated := by
    apply ((Nat.nth_strictMono hinf).range_inj enumerated_mono).mp
    rw [enumerated_range, Nat.range_nth_of_infinite hinf]
  cases n with
  | zero => simp [a, terms]
  | succ n => simp [a, terms, heq]

private theorem terms_orbit (m : ℕ) :
    terms (m + 2) = (orbit (m / 7) ⟨m % 7, by omega⟩).1 := by
  change ((orbit (m / 7) ⟨m % 7, by omega⟩).1.toNat : ℤ) = _
  exact Int.toNat_of_nonneg (le_of_lt (orbit_bounds (m / 7) _).1)

private theorem recurrence (n : ℕ) (hn : 15 < n) :
    terms n = 38 * terms (n - 7) - terms (n - 14) := by
  let m := n - 16
  have hn0 : n - 14 = m + 2 := by dsimp [m]; omega
  have hn1 : n - 7 = (m + 7) + 2 := by dsimp [m]; omega
  have hn2 : n = (m + 14) + 2 := by dsimp [m]; omega
  rw [hn0, hn1, hn2, terms_orbit, terms_orbit, terms_orbit]
  have hd1 : (m + 7) / 7 = m / 7 + 1 := by omega
  have hd2 : (m + 14) / 7 = (m / 7 + 1) + 1 := by omega
  have hr (d : ℕ) (hd : d = 7 ∨ d = 14) :
      (⟨(m + d) % 7, by omega⟩ : Fin 7) = ⟨m % 7, by omega⟩ := by
    apply Fin.ext
    change (m + d) % 7 = m % 7
    rcases hd with rfl | rfl <;> omega
  rw [hd1, hd2, hr 7 (Or.inl rfl), hr 14 (Or.inr rfl)]
  simp only [orbit, step]
  ring

private theorem genfun :
    (1 - 38 * X ^ 7 + X ^ 14) * (PowerSeries.mk terms) =
      (X ^ 2 * (1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 + 13 * X ^ 5 + 16 * X ^ 6
        - 19 * X ^ 7 - 38 * X ^ 8 - 57 * X ^ 9 - 16 * X ^ 10 - 13 * X ^ 11 - 7 * X ^ 12
        - 4 * X ^ 13) : PowerSeries ℤ) := by
  let F : PowerSeries ℤ := PowerSeries.mk terms
  change (1 - 38 * X ^ 7 + X ^ 14) * F = _
  have lhs : (1 - 38 * X ^ 7 + X ^ 14) * F = F - C 38 * (X ^ 7 * F) + X ^ 14 * F := by
    simp only [map_ofNat]
    ring
  have rhs : (X ^ 2 * (1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 + 13 * X ^ 5 + 16 * X ^ 6
        - 19 * X ^ 7 - 38 * X ^ 8 - 57 * X ^ 9 - 16 * X ^ 10 - 13 * X ^ 11 - 7 * X ^ 12
        - 4 * X ^ 13) : PowerSeries ℤ) =
      X ^ 2 + C 2 * X ^ 3 + C 3 * X ^ 4 + C 4 * X ^ 5 + C 7 * X ^ 6 + C 13 * X ^ 7 +
        C 16 * X ^ 8 - C 19 * X ^ 9 - C 38 * X ^ 10 - C 57 * X ^ 11 - C 16 * X ^ 12 -
        C 13 * X ^ 13 - C 7 * X ^ 14 - C 4 * X ^ 15 := by
    simp only [map_ofNat]
    ring
  rw [lhs, rhs]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, F, coeff_mk]
  by_cases hn : 15 < n
  · simp only [if_pos (show 7 ≤ n by omega), if_pos (show 14 ≤ n by omega),
      if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 6 by omega), if_neg (show n ≠ 7 by omega),
      if_neg (show n ≠ 8 by omega), if_neg (show n ≠ 9 by omega), if_neg (show n ≠ 10 by omega),
      if_neg (show n ≠ 11 by omega), if_neg (show n ≠ 12 by omega), if_neg (show n ≠ 13 by omega),
      if_neg (show n ≠ 14 by omega), if_neg (show n ≠ 15 by omega), mul_zero, sub_zero, add_zero]
    linarith [recurrence n hn]
  · interval_cases n <;> norm_num <;> decide

theorem result : type_of% @OMA.S_oeis_a031149.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · simp only [a_eq]
    exact recurrence n hn
  · simpa only [a_eq] using genfun

end OMA.A031149Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a031149.main := OMA.A031149Proof.result
