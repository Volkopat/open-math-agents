import OMAStatements.S_oeis_a270131

-- Problem: oeis-a270131
-- The automaton is shown equal to an explicit eventually 2-periodic pattern (finite kernel check),
-- from which the cell counts and the stated formulas follow.

namespace OMA.CA

def cellG (code : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0 => fun i j => decide (i = 0 ∧ j = 0)
  | t + 1 => fun i j => code.testBit ((cellG code t i j).toNat + 2 * ((cellG code t (i + 1) j).toNat +
      (cellG code t (i - 1) j).toNat + (cellG code t i (j + 1)).toNat + (cellG code t i (j - 1)).toNat))

def nxtG (K T0 p : ℕ) : ℕ := if p + 1 < K then p + 1 else T0

def phG (K T0 : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => nxtG K T0 (phG K T0 t)

def patG (R : ℕ) (tbl : List (List (List Bool))) (bgl : List Bool) (p : ℕ) (i j : ℤ) : Bool :=
  if -(R : ℤ) ≤ i ∧ i ≤ R ∧ -(R : ℤ) ≤ j ∧ j ≤ R then
    (((tbl.getD p []).getD (i + R).toNat []).getD (j + R).toNat false)
  else bgl.getD p false

theorem patG_out (R : ℕ) (tbl : List (List (List Bool))) (bgl : List Bool) (p : ℕ) (i j : ℤ)
    (h : ¬ (-(R : ℤ) ≤ i ∧ i ≤ R ∧ -(R : ℤ) ≤ j ∧ j ≤ R)) :
    patG R tbl bgl p i j = bgl.getD p false := if_neg h

theorem ph_lt (K T0 : ℕ) (hT : T0 < K) : ∀ t : ℕ, phG K T0 t < K := by
  intro t
  induction t with
  | zero => exact Nat.lt_of_le_of_lt (Nat.zero_le _) hT
  | succ t ih =>
    show nxtG K T0 (phG K T0 t) < K
    unfold nxtG
    split_ifs with h
    · exact h
    · exact hT

theorem ph_eq (T0 : ℕ) : ∀ t : ℕ,
    phG (T0 + 2) T0 t = if t < T0 then t else T0 + (t - T0) % 2 := by
  intro t
  induction t with
  | zero =>
    show (0 : ℕ) = _
    split_ifs with h
    · rfl
    · have : T0 = 0 := by omega
      subst this
      rfl
  | succ t ih =>
    show nxtG (T0 + 2) T0 (phG (T0 + 2) T0 t) = _
    rw [ih]
    unfold nxtG
    split_ifs <;> omega

theorem cell_pat (code R K T0 : ℕ) (tbl : List (List (List Bool))) (bgl : List Bool)
    (hT : T0 < K)
    (h0 : ∀ i ∈ Finset.Icc (-(R : ℤ)) R, ∀ j ∈ Finset.Icc (-(R : ℤ)) R,
      patG R tbl bgl 0 i j = decide (i = 0 ∧ j = 0))
    (hb0 : bgl.getD 0 false = false)
    (hstep : ∀ p ∈ Finset.range K, ∀ i ∈ Finset.Icc (-((R : ℤ) + 1)) (R + 1),
      ∀ j ∈ Finset.Icc (-((R : ℤ) + 1)) (R + 1),
      patG R tbl bgl (nxtG K T0 p) i j = code.testBit ((patG R tbl bgl p i j).toNat +
        2 * ((patG R tbl bgl p (i + 1) j).toNat + (patG R tbl bgl p (i - 1) j).toNat +
          (patG R tbl bgl p i (j + 1)).toNat + (patG R tbl bgl p i (j - 1)).toNat)))
    (hbg : ∀ p ∈ Finset.range K, bgl.getD (nxtG K T0 p) false =
      code.testBit ((bgl.getD p false).toNat + 2 * ((bgl.getD p false).toNat +
        (bgl.getD p false).toNat + (bgl.getD p false).toNat + (bgl.getD p false).toNat))) :
    ∀ (t : ℕ) (i j : ℤ), cellG code t i j = patG R tbl bgl (phG K T0 t) i j := by
  intro t
  induction t with
  | zero =>
    intro i j
    show decide (i = 0 ∧ j = 0) = patG R tbl bgl 0 i j
    by_cases hb : -(R : ℤ) ≤ i ∧ i ≤ R ∧ -(R : ℤ) ≤ j ∧ j ≤ R
    · exact (h0 i (Finset.mem_Icc.mpr ⟨hb.1, hb.2.1⟩) j (Finset.mem_Icc.mpr ⟨hb.2.2.1, hb.2.2.2⟩)).symm
    · rw [patG_out R tbl bgl 0 i j hb, hb0]
      have : ¬ (i = 0 ∧ j = 0) := by
        rintro ⟨rfl, rfl⟩
        exact hb ⟨by omega, by omega, by omega, by omega⟩
      simp [this]
  | succ t ih =>
    intro i j
    show code.testBit ((cellG code t i j).toNat + 2 * ((cellG code t (i + 1) j).toNat +
      (cellG code t (i - 1) j).toNat + (cellG code t i (j + 1)).toNat +
      (cellG code t i (j - 1)).toNat)) = patG R tbl bgl (nxtG K T0 (phG K T0 t)) i j
    rw [ih, ih, ih, ih, ih]
    have hp : phG K T0 t ∈ Finset.range K := Finset.mem_range.mpr (ph_lt K T0 hT t)
    by_cases hb : -((R : ℤ) + 1) ≤ i ∧ i ≤ R + 1 ∧ -((R : ℤ) + 1) ≤ j ∧ j ≤ R + 1
    · exact (hstep _ hp i (Finset.mem_Icc.mpr ⟨hb.1, hb.2.1⟩) j
        (Finset.mem_Icc.mpr ⟨hb.2.2.1, hb.2.2.2⟩)).symm
    · rw [patG_out R tbl bgl _ i j (by omega), patG_out R tbl bgl _ (i + 1) j (by omega),
        patG_out R tbl bgl _ (i - 1) j (by omega), patG_out R tbl bgl _ i (j + 1) (by omega),
        patG_out R tbl bgl _ i (j - 1) (by omega), patG_out R tbl bgl _ i j (by omega)]
      exact (hbg _ hp).symm

theorem sum_shift (f : ℤ → ℤ) (t : ℕ) :
    ∑ i ∈ Finset.range (2 * t + 1), f ((i : ℤ) - t) = ∑ x ∈ Finset.Icc (-(t : ℤ)) t, f x := by
  have himg : Finset.Icc (-(t : ℤ)) t =
      (Finset.range (2 * t + 1)).image (fun i : ℕ => (i : ℤ) - t) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hx
      exact ⟨(x + t).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [himg, Finset.sum_image]
  intro a _ b _ hab
  simp only at hab
  omega

theorem sum_box (h : ℤ → ℤ → ℤ) (R t : ℕ) (hR : R ≤ t)
    (hz : ∀ i j, ¬ (-(R : ℤ) ≤ i ∧ i ≤ R ∧ -(R : ℤ) ≤ j ∧ j ≤ R) → h i j = 0) :
    ∑ i ∈ Finset.Icc (-(t : ℤ)) t, ∑ j ∈ Finset.Icc (-(t : ℤ)) t, h i j
      = ∑ i ∈ Finset.Icc (-(R : ℤ)) R, ∑ j ∈ Finset.Icc (-(R : ℤ)) R, h i j := by
  have hsub : Finset.Icc (-(R : ℤ)) R ⊆ Finset.Icc (-(t : ℤ)) t :=
    Finset.Icc_subset_Icc (by omega) (by omega)
  symm
  rw [Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun i hi => ?_
    refine Finset.sum_subset hsub ?_
    intro j _ hj
    rw [Finset.mem_Icc] at hj
    exact hz i j (fun hb => hj ⟨hb.2.2.1, hb.2.2.2⟩)
  · intro i _ hi
    rw [Finset.mem_Icc] at hi
    refine Finset.sum_eq_zero fun j _ => ?_
    exact hz i j (fun hb => hi ⟨hb.1, hb.2.1⟩)

noncomputable def cntG (R : ℕ) (tbl : List (List (List Bool))) (bgl : List Bool) (p : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc (-(R : ℤ)) R, ∑ j ∈ Finset.Icc (-(R : ℤ)) R,
    ((if patG R tbl bgl p i j then (1 : ℤ) else 0) - (if bgl.getD p false then 1 else 0))

theorem count_pat (R : ℕ) (tbl : List (List (List Bool))) (bgl : List Bool) (p t : ℕ)
    (hR : R ≤ t) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if patG R tbl bgl p ((i : ℤ) - t) ((j : ℤ) - t) then (1 : ℤ) else 0)
      = cntG R tbl bgl p + (if bgl.getD p false then 1 else 0) * (2 * (t : ℤ) + 1) ^ 2 := by
  have e1 : ∀ i : ℕ, ∑ j ∈ Finset.range (2 * t + 1),
      (if patG R tbl bgl p ((i : ℤ) - t) ((j : ℤ) - t) then (1 : ℤ) else 0)
      = ∑ y ∈ Finset.Icc (-(t : ℤ)) t, (if patG R tbl bgl p ((i : ℤ) - t) y then (1 : ℤ) else 0) :=
    fun i => sum_shift (fun y => if patG R tbl bgl p ((i : ℤ) - t) y then (1 : ℤ) else 0) t
  simp only [e1]
  rw [sum_shift (fun x => ∑ y ∈ Finset.Icc (-(t : ℤ)) t,
    (if patG R tbl bgl p x y then (1 : ℤ) else 0)) t]
  have e2 : ∀ x y : ℤ, (if patG R tbl bgl p x y then (1 : ℤ) else 0)
      = ((if patG R tbl bgl p x y then (1 : ℤ) else 0) - (if bgl.getD p false then 1 else 0))
        + (if bgl.getD p false then 1 else 0) := fun x y => by ring
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => e2 x y))]
  simp only [Finset.sum_add_distrib]
  rw [sum_box (fun x y => (if patG R tbl bgl p x y then (1 : ℤ) else 0)
    - (if bgl.getD p false then 1 else 0)) R t hR]
  · unfold cntG
    simp only [Finset.sum_const, Int.card_Icc, smul_eq_mul, nsmul_eq_mul]
    have : (((t : ℤ) + 1 - -(t : ℤ)).toNat : ℤ) = 2 * (t : ℤ) + 1 := by omega
    rw [this]
    ring
  · intro i j hb
    rw [patG_out R tbl bgl p i j hb]
    ring

end OMA.CA

namespace OMA.P270131
open OMA.CA OMA.S_oeis_a270131

def tbl : List (List (List Bool)) :=
  [[[false, false, false, false, false], [false, false, false, false, false], [false, false, true, false, false], [false, false, false, false, false], [false, false, false, false, false]],
   [[true, true, true, true, true], [true, true, false, true, true], [true, false, false, false, true], [true, true, false, true, true], [true, true, true, true, true]],
   [[false, false, false, false, false], [false, false, true, false, false], [false, true, true, true, false], [false, false, true, false, false], [false, false, false, false, false]],
   [[true, true, false, true, true], [true, true, true, true, true], [false, true, false, true, false], [true, true, true, true, true], [true, true, false, true, true]],
   [[false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false], [false, false, false, false, false]],
   [[true, true, true, true, true], [true, true, true, true, true], [true, true, true, true, true], [true, true, true, true, true], [true, true, true, true, true]]]

def bgl : List Bool := [false, true, false, true, false, true]

theorem cellG_eq : ∀ (t : ℕ) (i j : ℤ), cell 89 t i j = cellG 89 t i j := by
  intro t
  induction t with
  | zero => intro i j; rfl
  | succ t ih => intro i j; simp only [cell, cellG, ih]

theorem cell_eq (t : ℕ) (i j : ℤ) : cell 89 t i j = patG 2 tbl bgl (phG (4 + 2) 4 t) i j := by
  rw [cellG_eq]
  exact cell_pat 89 2 (4 + 2) 4 tbl bgl (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) t i j

theorem oc (t : ℕ) (ht : 2 ≤ t) : (onCount 89 t : ℤ) = cntG 2 tbl bgl (phG (4 + 2) 4 t)
    + (if bgl.getD (phG (4 + 2) 4 t) false then 1 else 0) * (2 * (t : ℤ) + 1) ^ 2 := by
  rw [← count_pat 2 tbl bgl (phG (4 + 2) 4 t) t ht]
  unfold onCount
  push_cast
  simp only [cell_eq]

theorem ph0 (t : ℕ) (h : 4 ≤ t) (hp : t % 2 = 0) : phG (4 + 2) 4 t = 4 := by
  rw [ph_eq]
  split_ifs <;> omega

theorem cnt0 : cntG 2 tbl bgl 4 = 0 := by decide +kernel

theorem ocq0 (t : ℕ) (h : 4 ≤ t) (hp : t % 2 = 0) :
    ((onCount 89 t : ℕ) : ℚ) = 0 + 0 * (2 * (t : ℚ) + 1) ^ 2 := by
  have e := oc t (by omega)
  rw [ph0 t (by omega) hp, cnt0, show bgl.getD 4 false = false from by decide] at e
  have e' : ((onCount 89 t : ℕ) : ℤ) = 0 + 0 * (2 * (t : ℤ) + 1) ^ 2 := by
    rw [e]
    simp
  exact_mod_cast e'

theorem ph1 (t : ℕ) (h : 4 ≤ t) (hp : t % 2 = 1) : phG (4 + 2) 4 t = 5 := by
  rw [ph_eq]
  split_ifs <;> omega

theorem cnt1 : cntG 2 tbl bgl 5 = 0 := by decide +kernel

theorem ocq1 (t : ℕ) (h : 4 ≤ t) (hp : t % 2 = 1) :
    ((onCount 89 t : ℕ) : ℚ) = 0 + 1 * (2 * (t : ℚ) + 1) ^ 2 := by
  have e := oc t (by omega)
  rw [ph1 t (by omega) hp, cnt1, show bgl.getD 5 false = true from by decide] at e
  have e' : ((onCount 89 t : ℕ) : ℤ) = 0 + 1 * (2 * (t : ℤ) + 1) ^ 2 := by
    rw [e]
    simp
  exact_mod_cast e'

theorem A0 : a 0 = 1 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A1 : a 1 = 5 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A2 : a 2 = 10 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A3 : a 3 = 54 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A4 : a 4 = 54 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A5 : a 5 = 175 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A6 : a 6 = 175 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A7 : a 7 = 400 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A8 : a 8 = 400 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A9 : a 9 = 761 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A10 : a 10 = 761 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A11 : a 11 = 1290 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem Mall (n : ℕ) (h : 4 ≤ n) : ((a n : ℤ) : ℚ) = if n % 2 = 0 then (-4 / 1 : ℚ) * ((n : ℕ) : ℚ) ^ 0 + (-1 / 6 : ℚ) * ((n : ℕ) : ℚ) ^ 1 + (1 / 1 : ℚ) * ((n : ℕ) : ℚ) ^ 2 + (2 / 3 : ℚ) * ((n : ℕ) : ℚ) ^ 3 else (-5 / 2 : ℚ) * ((n : ℕ) : ℚ) ^ 0 + (23 / 6 : ℚ) * ((n : ℕ) : ℚ) ^ 1 + (3 / 1 : ℚ) * ((n : ℕ) : ℚ) ^ 2 + (2 / 3 : ℚ) * ((n : ℕ) : ℚ) ^ 3 := by
  induction n, h using Nat.le_induction with
  | base =>
    rw [A4]
    norm_num
  | succ n hn ih =>
    have hs : a (n + 1) = a n + (onCount 89 (n + 1) : ℤ) := by
      unfold a
      rw [Finset.sum_range_succ]
    rw [hs]
    push_cast
    rw [ih]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [if_pos h, if_neg (by omega : ¬ (n + 1) % 2 = 0), ocq1 (n + 1) (by omega) (by omega)]
      push_cast
      ring
    · rw [if_neg (by omega : ¬ n % 2 = 0), if_pos (by omega : (n + 1) % 2 = 0), ocq0 (n + 1) (by omega) (by omega)]
      push_cast
      ring

theorem M0 (n : ℕ) (h : 4 ≤ n) (hp : n % 2 = 0) : ((a n : ℤ) : ℚ) = (-4 / 1 : ℚ) * ((n : ℕ) : ℚ) ^ 0 + (-1 / 6 : ℚ) * ((n : ℕ) : ℚ) ^ 1 + (1 / 1 : ℚ) * ((n : ℕ) : ℚ) ^ 2 + (2 / 3 : ℚ) * ((n : ℕ) : ℚ) ^ 3 := by
  rw [Mall n h, if_pos hp]

theorem M1 (n : ℕ) (h : 4 ≤ n) (hp : n % 2 = 1) : ((a n : ℤ) : ℚ) = (-5 / 2 : ℚ) * ((n : ℕ) : ℚ) ^ 0 + (23 / 6 : ℚ) * ((n : ℕ) : ℚ) ^ 1 + (3 / 1 : ℚ) * ((n : ℕ) : ℚ) ^ 2 + (2 / 3 : ℚ) * ((n : ℕ) : ℚ) ^ 3 := by
  rw [Mall n h, if_neg (by omega)]

theorem Aq0 : ((a 0 : ℤ) : ℚ) = 1 := by
  rw [A0]
  norm_num

theorem Aq1 : ((a 1 : ℤ) : ℚ) = 5 := by
  rw [A1]
  norm_num

theorem Aq2 : ((a 2 : ℤ) : ℚ) = 10 := by
  rw [A2]
  norm_num

theorem Aq3 : ((a 3 : ℤ) : ℚ) = 54 := by
  rw [A3]
  norm_num

theorem Aq4 : ((a 4 : ℤ) : ℚ) = 54 := by
  rw [A4]
  norm_num

theorem Aq5 : ((a 5 : ℤ) : ℚ) = 175 := by
  rw [A5]
  norm_num

theorem Aq6 : ((a 6 : ℤ) : ℚ) = 175 := by
  rw [A6]
  norm_num

theorem Aq7 : ((a 7 : ℤ) : ℚ) = 400 := by
  rw [A7]
  norm_num

theorem Aq8 : ((a 8 : ℤ) : ℚ) = 400 := by
  rw [A8]
  norm_num

theorem Aq9 : ((a 9 : ℤ) : ℚ) = 761 := by
  rw [A9]
  norm_num

theorem Aq10 : ((a 10 : ℤ) : ℚ) = 761 := by
  rw [A10]
  norm_num

theorem Aq11 : ((a 11 : ℤ) : ℚ) = 1290 := by
  rw [A11]
  norm_num

theorem rec3 (m : ℕ) : (1 : ℚ) * (OMA.S_oeis_a270131.a (m + 11) : ℚ) + (-1 : ℚ) * (OMA.S_oeis_a270131.a (m + 10) : ℚ) + (-3 : ℚ) * (OMA.S_oeis_a270131.a (m + 9) : ℚ) + (3 : ℚ) * (OMA.S_oeis_a270131.a (m + 8) : ℚ) + (3 : ℚ) * (OMA.S_oeis_a270131.a (m + 7) : ℚ) + (-3 : ℚ) * (OMA.S_oeis_a270131.a (m + 6) : ℚ) + (-1 : ℚ) * (OMA.S_oeis_a270131.a (m + 5) : ℚ) + (1 : ℚ) * (OMA.S_oeis_a270131.a (m + 4) : ℚ) = 0 := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · rw [M1 (2 * k + 11) (by omega) (by omega), M0 (2 * k + 10) (by omega) (by omega), M1 (2 * k + 9) (by omega) (by omega), M0 (2 * k + 8) (by omega) (by omega), M1 (2 * k + 7) (by omega) (by omega), M0 (2 * k + 6) (by omega) (by omega), M1 (2 * k + 5) (by omega) (by omega), M0 (2 * k + 4) (by omega) (by omega)]
    push_cast
    ring
  · rw [M0 (2 * k + 1 + 11) (by omega) (by omega), M1 (2 * k + 1 + 10) (by omega) (by omega), M0 (2 * k + 1 + 9) (by omega) (by omega), M1 (2 * k + 1 + 8) (by omega) (by omega), M0 (2 * k + 1 + 7) (by omega) (by omega), M1 (2 * k + 1 + 6) (by omega) (by omega), M0 (2 * k + 1 + 5) (by omega) (by omega), M1 (2 * k + 1 + 4) (by omega) (by omega)]
    push_cast
    ring

theorem rec4 (m : ℕ) : (1 : ℚ) * (OMA.S_oeis_a270131.a (m + 11) : ℚ) + (-1 : ℚ) * (OMA.S_oeis_a270131.a (m + 10) : ℚ) + (-3 : ℚ) * (OMA.S_oeis_a270131.a (m + 9) : ℚ) + (3 : ℚ) * (OMA.S_oeis_a270131.a (m + 8) : ℚ) + (3 : ℚ) * (OMA.S_oeis_a270131.a (m + 7) : ℚ) + (-3 : ℚ) * (OMA.S_oeis_a270131.a (m + 6) : ℚ) + (-1 : ℚ) * (OMA.S_oeis_a270131.a (m + 5) : ℚ) + (1 : ℚ) * (OMA.S_oeis_a270131.a (m + 4) : ℚ) = 0 := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · rw [M1 (2 * k + 11) (by omega) (by omega), M0 (2 * k + 10) (by omega) (by omega), M1 (2 * k + 9) (by omega) (by omega), M0 (2 * k + 8) (by omega) (by omega), M1 (2 * k + 7) (by omega) (by omega), M0 (2 * k + 6) (by omega) (by omega), M1 (2 * k + 5) (by omega) (by omega), M0 (2 * k + 4) (by omega) (by omega)]
    push_cast
    ring
  · rw [M0 (2 * k + 1 + 11) (by omega) (by omega), M1 (2 * k + 1 + 10) (by omega) (by omega), M0 (2 * k + 1 + 9) (by omega) (by omega), M1 (2 * k + 1 + 8) (by omega) (by omega), M0 (2 * k + 1 + 7) (by omega) (by omega), M1 (2 * k + 1 + 6) (by omega) (by omega), M0 (2 * k + 1 + 5) (by omega) (by omega), M1 (2 * k + 1 + 4) (by omega) (by omega)]
    push_cast
    ring

end OMA.P270131

theorem OMA.solution : type_of% @OMA.S_oeis_a270131.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> norm_num [OMA.P270131.Aq0, OMA.P270131.Aq1, OMA.P270131.Aq2, OMA.P270131.Aq3]
    · rcases Nat.even_or_odd n with he | ho
      · rw [OMA.P270131.M0 n h (Nat.even_iff.mp he)]
        rw [Even.neg_one_pow he]
        ring
      · rw [OMA.P270131.M1 n h (Nat.odd_iff.mp ho)]
        rw [Odd.neg_one_pow ho]
        ring
  · intro n hn hpar
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> first | (exfalso; revert hpar; decide) | norm_num [OMA.P270131.Aq0, OMA.P270131.Aq1, OMA.P270131.Aq2, OMA.P270131.Aq3]
    · rw [OMA.P270131.M0 n h (Nat.even_iff.mp hpar)]
      ring
  · intro n hn hpar
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> first | (exfalso; revert hpar; decide) | norm_num [OMA.P270131.Aq0, OMA.P270131.Aq1, OMA.P270131.Aq2, OMA.P270131.Aq3]
    · rw [OMA.P270131.M1 n h (Nat.odd_iff.mp hpar)]
      ring
  · intro n hn
    rcases Nat.lt_or_ge n 11 with h | h
    · interval_cases n <;> norm_num [OMA.P270131.Aq0, OMA.P270131.Aq1, OMA.P270131.Aq2, OMA.P270131.Aq3, OMA.P270131.Aq4, OMA.P270131.Aq5, OMA.P270131.Aq6, OMA.P270131.Aq7, OMA.P270131.Aq8, OMA.P270131.Aq9, OMA.P270131.Aq10]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
      have hr := OMA.P270131.rec3 m
      simp only [show m + 11 - 1 = m + 10 from rfl, show m + 11 - 2 = m + 9 from rfl, show m + 11 - 3 = m + 8 from rfl, show m + 11 - 4 = m + 7 from rfl, show m + 11 - 5 = m + 6 from rfl, show m + 11 - 6 = m + 5 from rfl, show m + 11 - 7 = m + 4 from rfl]
      linarith
  · have hD : (((1 - PowerSeries.X) ^ 4 * (1 + PowerSeries.X) ^ 3) : PowerSeries ℚ)
        = PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (-3 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (-3 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 7 := by
      simp only [map_ofNat, map_neg, map_one, map_zero]; ring
    have hNum : ((1 + 4 * PowerSeries.X + 2 * PowerSeries.X ^ 2 + 32 * PowerSeries.X ^ 3 - 12 * PowerSeries.X ^ 4 + PowerSeries.X ^ 5 + 14 * PowerSeries.X ^ 6 - 10 * PowerSeries.X ^ 7 - 5 * PowerSeries.X ^ 8 + 5 * PowerSeries.X ^ 9) : PowerSeries ℚ)
        = PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (32 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (-12 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (14 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (-10 : ℚ) * PowerSeries.X ^ 7 + PowerSeries.C (-5 : ℚ) * PowerSeries.X ^ 8 + PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 9 := by
      simp only [map_ofNat, map_neg, map_one, map_zero]; ring
    have key : ∀ F : PowerSeries ℚ, F * (PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (-3 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (-3 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 7)
        = PowerSeries.C (1 : ℚ) * (F * PowerSeries.X ^ 0) + PowerSeries.C (-1 : ℚ) * (F * PowerSeries.X ^ 1) + PowerSeries.C (-3 : ℚ) * (F * PowerSeries.X ^ 2) + PowerSeries.C (3 : ℚ) * (F * PowerSeries.X ^ 3) + PowerSeries.C (3 : ℚ) * (F * PowerSeries.X ^ 4) + PowerSeries.C (-3 : ℚ) * (F * PowerSeries.X ^ 5) + PowerSeries.C (-1 : ℚ) * (F * PowerSeries.X ^ 6) + PowerSeries.C (1 : ℚ) * (F * PowerSeries.X ^ 7) := by
      intro F; ring
    rw [hD, hNum, key]
    ext n
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow,
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
    · norm_num [OMA.P270131.Aq0]
    · norm_num [OMA.P270131.Aq0, OMA.P270131.Aq1]
    · norm_num [OMA.P270131.Aq0, OMA.P270131.Aq1, OMA.P270131.Aq2]
    · norm_num [OMA.P270131.Aq0, OMA.P270131.Aq1, OMA.P270131.Aq2, OMA.P270131.Aq3]
    · norm_num [OMA.P270131.Aq0, OMA.P270131.Aq1, OMA.P270131.Aq2, OMA.P270131.Aq3, OMA.P270131.Aq4]
    · norm_num [OMA.P270131.Aq0, OMA.P270131.Aq1, OMA.P270131.Aq2, OMA.P270131.Aq3, OMA.P270131.Aq4, OMA.P270131.Aq5]
    · norm_num [OMA.P270131.Aq0, OMA.P270131.Aq1, OMA.P270131.Aq2, OMA.P270131.Aq3, OMA.P270131.Aq4, OMA.P270131.Aq5, OMA.P270131.Aq6]
    · norm_num [OMA.P270131.Aq0, OMA.P270131.Aq1, OMA.P270131.Aq2, OMA.P270131.Aq3, OMA.P270131.Aq4, OMA.P270131.Aq5, OMA.P270131.Aq6, OMA.P270131.Aq7]
    · norm_num [OMA.P270131.Aq0, OMA.P270131.Aq1, OMA.P270131.Aq2, OMA.P270131.Aq3, OMA.P270131.Aq4, OMA.P270131.Aq5, OMA.P270131.Aq6, OMA.P270131.Aq7, OMA.P270131.Aq8]
    · norm_num [OMA.P270131.Aq0, OMA.P270131.Aq1, OMA.P270131.Aq2, OMA.P270131.Aq3, OMA.P270131.Aq4, OMA.P270131.Aq5, OMA.P270131.Aq6, OMA.P270131.Aq7, OMA.P270131.Aq8, OMA.P270131.Aq9]
    · norm_num [OMA.P270131.Aq0, OMA.P270131.Aq1, OMA.P270131.Aq2, OMA.P270131.Aq3, OMA.P270131.Aq4, OMA.P270131.Aq5, OMA.P270131.Aq6, OMA.P270131.Aq7, OMA.P270131.Aq8, OMA.P270131.Aq9, OMA.P270131.Aq10]
    · rw [show m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = m + 11 from rfl]
      have hr := OMA.P270131.rec4 m
      simp only [show 0 ≤ m + 11 from by omega,
        show m + 11 - 0 = m + 11 from rfl,
        show ¬ (m + 11 = 0) from by omega,
        show 1 ≤ m + 11 from by omega,
        show m + 11 - 1 = m + 10 from rfl,
        show ¬ (m + 10 = 0) from by omega,
        show 2 ≤ m + 11 from by omega,
        show m + 11 - 2 = m + 9 from rfl,
        show ¬ (m + 9 = 0) from by omega,
        show 3 ≤ m + 11 from by omega,
        show m + 11 - 3 = m + 8 from rfl,
        show ¬ (m + 8 = 0) from by omega,
        show 4 ≤ m + 11 from by omega,
        show m + 11 - 4 = m + 7 from rfl,
        show ¬ (m + 7 = 0) from by omega,
        show 5 ≤ m + 11 from by omega,
        show m + 11 - 5 = m + 6 from rfl,
        show ¬ (m + 6 = 0) from by omega,
        show 6 ≤ m + 11 from by omega,
        show m + 11 - 6 = m + 5 from rfl,
        show ¬ (m + 5 = 0) from by omega,
        show 7 ≤ m + 11 from by omega,
        show m + 11 - 7 = m + 4 from rfl,
        show ¬ (m + 4 = 0) from by omega,
        show 8 ≤ m + 11 from by omega,
        show m + 11 - 8 = m + 3 from rfl,
        show ¬ (m + 3 = 0) from by omega,
        show 9 ≤ m + 11 from by omega,
        show m + 11 - 9 = m + 2 from rfl,
        show ¬ (m + 2 = 0) from by omega,
        if_true, if_false]
      linear_combination hr
