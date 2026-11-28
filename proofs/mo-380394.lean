import OMAStatements.S_mo_380394

open OMA.S_mo_380394

/-- The first 31 values of the recurrence, reduced modulo `2 ^ 11`. -/
private def residues : List (ZMod 2048) :=
  [1, 1, 2, 9, 170, 634, 152, 393, 1162, 834, 1528, 1530, 1656, 1080, 608,
    1545, 650, 1442, 1528, 1730, 1240, 1176, 864, 122, 1656, 152, 1888, 696,
    864, 1888, 1024]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem residues_recurrence : ∀ n : Fin 30,
    residues[n.val + 1]! =
      ∑ i : Fin (n.val + 1), residues[i.val]! ^ 2 * residues[n.val - i.val]! ^ 2 := by
  decide

private theorem cast_w (n : ℕ) (hn : n ≤ 30) :
    (w n : ZMod 2048) = residues[n]! := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [w, residues]
    | succ n =>
      rw [w, Nat.cast_sum, ← Nat.succ_eq_add_one]
      rw [residues_recurrence (⟨n, by omega⟩ : Fin 30)]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := i.isLt
      simp only [Nat.cast_mul, Nat.cast_pow]
      rw [ih i.val (by omega) (by omega), ih (n - i.val) (by omega) (by omega)]

private theorem valuation_at_counterexample : padicValNat 2 (w 30) = 10 := by
  have hw : (w 30 : ZMod 2048) = 1024 := (cast_w 30 (by decide)).trans (by decide)
  have hmod := congrArg ZMod.val hw
  rw [ZMod.val_natCast] at hmod
  change w 30 % 2048 = 1024 at hmod
  have hdiv : 2 ^ 10 ∣ w 30 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hndiv : ¬ 2 ^ 11 ∣ w 30 := by
    intro hd
    have hzero := Nat.mod_eq_zero_of_dvd hd
    omega
  have hn : w 30 ≠ 0 := by
    intro hz
    exact hndiv (hz ▸ dvd_zero _)
  have hlo := (padicValNat_dvd_iff_le_of_ne_one (by decide : 2 ≠ 1) hn).mp hdiv
  have hhi := mt (padicValNat_dvd_iff_le_of_ne_one (by decide : 2 ≠ 1) hn).mpr hndiv
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_380394.main) := by
  intro h
  have hcat : catalan 30 % 2 = 0 := by
    rw [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose_eq_descFactorial_div_factorial]
    decide
  have hdigit : (Nat.digits 2 (30 + 1)).sum = 5 := by decide
  have h30 := h 30
  rw [valuation_at_counterexample, hcat, hdigit] at h30
  norm_num at h30
