import FormalConjectures.OEIS.«86766»

/-! Shorter disproof of `OeisA86766.conjecture2` via 104040. -/

theorem OMA.disproof : ¬ (type_of% @OeisA86766.conjecture2) := by
  intro h
  refine h 104040 (by decide) (fun m => by
    rcases le_or_gt m 5 with hm | hm
    · have := Nat.pow_le_pow_right (by decide : 1 ≤ 10) hm; omega
    · have := Nat.pow_le_pow_right (by decide : 1 ≤ 10) hm; omega) ?_
  have hd : (Nat.digits 10 104040).length = 6 := by decide
  simp only [OeisA86766.a, show (104040 : ℕ) ≠ 0 by decide, if_false, hd]
  refine Nat.sInf_eq_zero.mpr (Or.inr (Set.eq_empty_iff_forall_notMem.mpr fun r ⟨hr, hp⟩ => ?_))
  have hgeom (k : ℕ) : 999999 * (∑ i ∈ Finset.range k, (1000000 : ℕ) ^ i) + 1 = 1000000 ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega
  let t := (1000 : ℕ) ^ r
  let s := ∑ i ∈ Finset.range r, (1000000 : ℕ) ^ i
  let c := (104040 * s) * 10 + 1
  have ht : 1000 ≤ t := Nat.pow_le_pow_right (by decide : 0 < 1000) hr
  have hg : 999999 * s + 1 = t * t := by dsimp [s, t]; rw [← mul_pow]; exact hgeom r
  have hfac : (1020 * t - 201) * (1020 * t + 201) = 999999 * c := by
    dsimp [c]; zify [show 201 ≤ 1020 * t by omega] at hg ⊢; nlinarith only [hg]
  change c.Prime at hp
  rcases hp.dvd_mul.mp (hfac.symm ▸ dvd_mul_left c 999999) with hd | hd <;>
    (have := Nat.le_of_dvd (by omega) hd; zify [show 201 ≤ 1020 * t by omega] at hfac this; nlinarith)
