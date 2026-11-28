import OMAStatements.S_oeis_a203719

open PowerSeries
open OMA.S_oeis_a203719

namespace OMA.A203719Proof

private def step (p : ℤ × ℤ) : ℤ × ℤ :=
  (9 * p.1 + 20 * p.2, 4 * p.1 + 9 * p.2)

private def back (p : ℤ × ℤ) : ℤ × ℤ :=
  (9 * p.1 - 20 * p.2, 9 * p.2 - 4 * p.1)

private def norm (p : ℤ × ℤ) : ℤ := p.1 ^ 2 - 5 * p.2 ^ 2

/-- Positive solutions whose inverse Pell step has a negative second coordinate. -/
private def seed (i : Fin 4) : ℤ × ℤ :=
  ![(1, 0), (2, 0), (3, 1), (7, 3)] i

private def orbit : ℕ → Fin 4 → ℤ × ℤ
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

private theorem orbit_bounds (k : ℕ) (i : Fin 4) :
    0 < (orbit k i).1 ∧ 0 ≤ (orbit k i).2 ∧
      0 ≤ norm (orbit k i) ∧ norm (orbit k i) < 5 := by
  induction k with
  | zero => fin_cases i <;> decide
  | succ k ih =>
    rcases ih with ⟨hx, hy, hl, hu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · change 0 < 9 * (orbit k i).1 + 20 * (orbit k i).2
      omega
    · change 0 ≤ 4 * (orbit k i).1 + 9 * (orbit k i).2
      omega
    · simpa only [orbit, norm_step] using hl
    · simpa only [orbit, norm_step] using hu

private theorem step_lt (p q : ℤ × ℤ) (hx : p.1 < q.1) (hy : p.2 ≤ q.2) :
    (step p).1 < (step q).1 ∧ (step p).2 ≤ (step q).2 := by
  dsimp [step]
  omega

private theorem orbit_adjacent (k : ℕ) (i : Fin 3) :
    (orbit k ⟨i, by omega⟩).1 < (orbit k ⟨i + 1, by omega⟩).1 ∧
      (orbit k ⟨i, by omega⟩).2 ≤ (orbit k ⟨i + 1, by omega⟩).2 := by
  induction k with
  | zero => fin_cases i <;> decide
  | succ k ih => exact step_lt _ _ ih.1 ih.2

private theorem orbit_next (k : ℕ) :
    (orbit k 3).1 < (orbit (k + 1) 0).1 ∧ (orbit k 3).2 ≤ (orbit (k + 1) 0).2 := by
  induction k with
  | zero => decide
  | succ k ih => exact step_lt _ _ ih.1 ih.2

private theorem finite_seeds :
    ∀ (x : Fin 16) (y : Fin 8),
      0 < x.val → 0 ≤ norm (x.val, y.val) → norm (x.val, y.val) < 5 →
      (back (x.val, y.val)).2 < 0 → ∃ i : Fin 4, ((x.val : ℤ), (y.val : ℤ)) = seed i := by
  decide +kernel

private theorem orbit_complete (x y : ℤ) (hx : 0 < x) (hy : 0 ≤ y)
    (hl : 0 ≤ norm (x, y)) (hu : norm (x, y) < 5) :
    ∃ k i, (x, y) = orbit k i := by
  suffices key : ∀ (n : ℕ) (x y : ℤ), x.toNat = n → 0 < x → 0 ≤ y →
      0 ≤ norm (x, y) → norm (x, y) < 5 → ∃ k i, (x, y) = orbit k i from
    key x.toNat x y rfl hx hy hl hu
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hn hx hy hl hu
    have hxl : 5 * y ^ 2 ≤ x ^ 2 := by simpa [norm, sub_nonneg] using hl
    have hxu : x ^ 2 - 5 * y ^ 2 ≤ 4 := by
      change x ^ 2 - 5 * y ^ 2 < 5 at hu
      omega
    by_cases hy' : 0 ≤ (back (x, y)).2
    · have hx' : 0 < (back (x, y)).1 := by
        change 0 < 9 * x - 20 * y
        by_contra! h
        have hp := mul_nonneg (show 0 ≤ 20 * y - 9 * x by omega)
          (show 0 ≤ 20 * y + 9 * x by omega)
        have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
        nlinarith
      have hlt : (back (x, y)).1 < x := by
        change 9 * x - 20 * y < x
        change 0 ≤ 9 * y - 4 * x at hy'
        omega
      obtain ⟨k, i, hi⟩ := ih (back (x, y)).1.toNat (by omega)
        _ _ rfl hx' hy' (by rwa [norm_back]) (by rwa [norm_back])
      exact ⟨k + 1, i, by rw [orbit, ← hi, step_back]⟩
    · have hyb : y < 8 := by
        change ¬ 0 ≤ 9 * y - 4 * x at hy'
        have hp := mul_pos (show 0 < 4 * x - 9 * y by omega)
          (show 0 < 4 * x + 9 * y by omega)
        by_contra! h
        have hsq := mul_nonneg (show 0 ≤ y - 8 by omega) (show 0 ≤ y + 8 by omega)
        nlinarith
      have hxb : x < 16 := by
        have hle : y ≤ 7 := by omega
        have hp := mul_nonneg (show 0 ≤ 7 - y by omega) (show 0 ≤ 7 + y by omega)
        by_contra! h
        have hsq := mul_nonneg (show 0 ≤ x - 16 by omega) (show 0 ≤ x + 16 by omega)
        nlinarith
      let i : Fin 16 := ⟨x.toNat, by omega⟩
      let j : Fin 8 := ⟨y.toNat, by omega⟩
      have hi : (i.val : ℤ) = x := Int.toNat_of_nonneg (by omega)
      have hj : (j.val : ℤ) = y := Int.toNat_of_nonneg hy
      obtain ⟨s, hs⟩ := finite_seeds i j (by omega)
        (by rw [hi, hj]; exact hl) (by rw [hi, hj]; exact hu)
        (by rw [hi, hj]; omega)
      rw [hi, hj] at hs
      exact ⟨0, s, hs⟩

/-- Start at zero, then list the four interleaved orbits in blocks. -/
private def enumerated : ℕ → ℕ
  | 0 => 0
  | m + 1 => (orbit (m / 4) ⟨m % 4, by omega⟩).1.toNat

private theorem enumerated_mono : StrictMono enumerated := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => decide
  | succ m =>
    change (orbit (m / 4) ⟨m % 4, by omega⟩).1.toNat <
      (orbit ((m + 1) / 4) ⟨(m + 1) % 4, by omega⟩).1.toNat
    by_cases h : m % 4 < 3
    · have hq : (m + 1) / 4 = m / 4 := by omega
      have hr : (⟨(m + 1) % 4, by omega⟩ : Fin 4) =
          ⟨(⟨m % 4, h⟩ : Fin 3).val + 1, by omega⟩ := by
        apply Fin.ext
        dsimp
        omega
      rw [hq, hr]
      have hh := (orbit_adjacent (m / 4) ⟨m % 4, h⟩).1
      have hright := (orbit_bounds (m / 4) ⟨(⟨m % 4, h⟩ : Fin 3).val + 1, by omega⟩).1
      exact (Int.toNat_lt_toNat hright).2 hh
    · have hq : (m + 1) / 4 = m / 4 + 1 := by omega
      have hr : (⟨(m + 1) % 4, by omega⟩ : Fin 4) = 0 := by
        apply Fin.ext
        change (m + 1) % 4 = 0
        omega
      have hs : (⟨m % 4, by omega⟩ : Fin 4) = 3 := by
        apply Fin.ext
        change m % 4 = 3
        omega
      rw [hq, hr, hs]
      exact (Int.toNat_lt_toNat (orbit_bounds (m / 4 + 1) 0).1).2 (orbit_next (m / 4)).1

private theorem square_iff (x : ℕ) :
    IsSquare (x ^ 2 / 5) ↔ ∃ y : ℕ, 0 ≤ norm (x, y) ∧ norm (x, y) < 5 := by
  constructor
  · rintro ⟨y, hy⟩
    have hm := Nat.mod_add_div (x ^ 2) 5
    have hb := Nat.mod_lt (x ^ 2) (by decide : 0 < 5)
    rw [hy, ← pow_two] at hm
    have hz : ((x ^ 2 : ℕ) : ℤ) = (x ^ 2 % 5 : ℕ) + 5 * (y : ℤ) ^ 2 := by
      exact_mod_cast hm.symm
    refine ⟨y, ?_, ?_⟩ <;> simp only [norm, Nat.cast_pow] at * <;> omega
  · rintro ⟨y, hl, hu⟩
    have hl' : 5 * (y ^ 2 : ℕ) ≤ x ^ 2 := by
      have hz : 5 * (y : ℤ) ^ 2 ≤ (x : ℤ) ^ 2 := by simpa [norm, sub_nonneg] using hl
      exact_mod_cast hz
    have hu' : x ^ 2 < 5 * y ^ 2 + 5 := by
      have hz : (x : ℤ) ^ 2 < 5 * (y : ℤ) ^ 2 + 5 := by
        simpa [norm, sub_lt_iff_lt_add, add_comm] using hu
      exact_mod_cast hz
    exact ⟨y, by rw [← pow_two]; omega⟩

private theorem enumerated_range :
    Set.range enumerated = {x : ℕ | IsSquare (x ^ 2 / 5)} := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    change IsSquare (enumerated n ^ 2 / 5)
    cases n with
    | zero => exact ⟨0, rfl⟩
    | succ m =>
      let p := orbit (m / 4) ⟨m % 4, by omega⟩
      have hb := orbit_bounds (m / 4) ⟨m % 4, by omega⟩
      change 0 < p.1 ∧ 0 ≤ p.2 ∧ 0 ≤ norm p ∧ norm p < 5 at hb
      apply (square_iff _).2
      change ∃ y : ℕ, 0 ≤ norm (p.1.toNat, y) ∧ norm (p.1.toNat, y) < 5
      refine ⟨p.2.toNat, ?_⟩
      rw [Int.toNat_of_nonneg (le_of_lt hb.1), Int.toNat_of_nonneg hb.2.1, Prod.mk.eta]
      exact hb.2.2
  · intro hx
    change IsSquare (x ^ 2 / 5) at hx
    by_cases hz : x = 0
    · exact ⟨0, by simpa [enumerated] using hz.symm⟩
    · obtain ⟨y, yl, yu⟩ := (square_iff x).1 hx
      obtain ⟨k, i, hi⟩ := orbit_complete (x : ℤ) (y : ℤ) (by omega) (by omega) yl yu
      refine ⟨4 * k + i.val + 1, ?_⟩
      have hq : (4 * k + i.val) / 4 = k := by omega
      have hr : (⟨(4 * k + i.val) % 4, by omega⟩ : Fin 4) = i := by
        apply Fin.ext
        change (4 * k + i.val) % 4 = i.val
        omega
      rw [enumerated, hq, hr, ← hi]
      simp

private theorem nth_eq : Nat.nth good = enumerated := by
  have hr : Set.range enumerated = Set.ofPred good := by
    rw [enumerated_range]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_ofPred_eq, good]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by simpa [pow_two] using hy.symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by simpa [pow_two] using hy.symm⟩
  have hinf : (Set.ofPred good).Infinite := by
    rw [← hr]
    exact Set.infinite_range_of_injective enumerated_mono.injective
  apply ((Nat.nth_strictMono hinf).range_inj enumerated_mono).mp
  rw [Nat.range_nth_of_infinite hinf, hr]

private theorem term_orbit (m : ℕ) :
    (term (m + 2) : ℤ) = (orbit (m / 4) ⟨m % 4, by omega⟩).2 ^ 2 := by
  let p := orbit (m / 4) ⟨m % 4, by omega⟩
  have hb := orbit_bounds (m / 4) ⟨m % 4, by omega⟩
  change 0 < p.1 ∧ 0 ≤ p.2 ∧ 0 ≤ norm p ∧ norm p < 5 at hb
  have h1 : (p.1.toNat : ℤ) = p.1 := Int.toNat_of_nonneg (le_of_lt hb.1)
  have h2 : (p.2.toNat : ℤ) = p.2 := Int.toNat_of_nonneg hb.2.1
  have hl : 5 * p.2.toNat ^ 2 ≤ p.1.toNat ^ 2 := by
    have hs : (5 : ℤ) * (p.2.toNat : ℤ) ^ 2 ≤ (p.1.toNat : ℤ) ^ 2 := by
      rw [h1, h2]
      simpa [norm, sub_nonneg] using hb.2.2.1
    exact_mod_cast hs
  have hu : p.1.toNat ^ 2 < 5 * p.2.toNat ^ 2 + 5 := by
    have hs : (p.1.toNat : ℤ) ^ 2 < 5 * (p.2.toNat : ℤ) ^ 2 + 5 := by
      rw [h1, h2]
      simpa [norm, sub_lt_iff_lt_add, add_comm] using hb.2.2.2
    exact_mod_cast hs
  have hd : p.1.toNat ^ 2 / 5 = p.2.toNat ^ 2 := by omega
  unfold term
  rw [show m + 2 - 1 = m + 1 by omega, nth_eq]
  change ((p.1.toNat * p.1.toNat / 5 : ℕ) : ℤ) = p.2 ^ 2
  rw [← pow_two, hd, Nat.cast_pow, h2]

private theorem recurrence (n : ℕ) (hn : 13 < n) :
    (term n : ℤ) = 323 * (term (n - 4) : ℤ) - 323 * (term (n - 8) : ℤ) +
      (term (n - 12) : ℤ) := by
  let m := n - 14
  have hn0 : n - 12 = m + 2 := by dsimp [m]; omega
  have hn1 : n - 8 = (m + 4) + 2 := by dsimp [m]; omega
  have hn2 : n - 4 = (m + 8) + 2 := by dsimp [m]; omega
  have hn3 : n = (m + 12) + 2 := by dsimp [m]; omega
  rw [hn0, hn1, hn2, hn3, term_orbit, term_orbit, term_orbit, term_orbit]
  have hd1 : (m + 4) / 4 = m / 4 + 1 := by omega
  have hd2 : (m + 8) / 4 = (m / 4 + 1) + 1 := by omega
  have hd3 : (m + 12) / 4 = ((m / 4 + 1) + 1) + 1 := by omega
  have hr (d : ℕ) (hd : d = 4 ∨ d = 8 ∨ d = 12) :
      (⟨(m + d) % 4, by omega⟩ : Fin 4) = ⟨m % 4, by omega⟩ := by
    apply Fin.ext
    change (m + d) % 4 = m % 4
    rcases hd with rfl | rfl | rfl <;> omega
  rw [hd1, hd2, hd3, hr 4 (Or.inl rfl), hr 8 (Or.inr (Or.inl rfl)), hr 12 (Or.inr (Or.inr rfl))]
  simp only [orbit, step]
  ring

theorem result : type_of% @OMA.S_oeis_a203719.main := recurrence

end OMA.A203719Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a203719.main := OMA.A203719Proof.result
