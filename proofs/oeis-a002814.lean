import OMAStatements.S_oeis_a002814
import Mathlib

open OMA.S_oeis_a002814 Function

private def v (n : ℕ) := a (n+1) - 2

/-- A divisor of the shifted term is exactly a modulus for which the starting
point returns after n iterations. Return times are multiples of the minimal period. -/
private theorem return_time (d n : ℕ) :
    (d : ℤ) ∣ v n ↔
      IsPeriodicPt (fun x : ZMod d => x^3 + 3*x^2 - 3) n 2 := by
  let F (x : ZMod d) := x^3 + 3*x^2 - 3
  have orbit (i : ℕ) : (a (i+1) : ZMod d) = F^[i] 2 := by
    induction i with
    | zero => simp [a]
    | succ i ih =>
      rw [iterate_succ_apply', ← ih]
      change (↑((a (i+1)^3 + 3*a (i+1)^2 - 3) : ℤ) : ZMod d) = _
      push_cast
      rfl
  change (d : ℤ) ∣ (a (n+1) - 2) ↔ F^[n] 2 = 2
  rw [← orbit, eq_comm, ← Int.cast_ofNat (R := ZMod d),
    ZMod.intCast_eq_intCast_iff_dvd_sub]

private theorem common_dvd (d n m : ℕ) :
    (d : ℤ) ∣ v n ∧ (d : ℤ) ∣ v m ↔ (d : ℤ) ∣ v (n.gcd m) := by
  simp [return_time, isPeriodicPt_iff_minimalPeriod_dvd, Nat.dvd_gcd_iff]

private theorem nonneg (n : ℕ) : 0 ≤ v n := by
  apply sub_nonneg.mpr
  induction n with
  | zero => decide
  | succ n ih =>
    change 2 ≤ a (n+1)^3 + 3*a (n+1)^2 - 3
    have h : (0 : ℤ) ≤ 2 := by decide
    nlinarith only [pow_le_pow_left₀ h ih 2, pow_le_pow_left₀ h ih 3]

theorem OMA.solution : type_of% @OMA.S_oeis_a002814.main := by
  intro n m _ _
  change (Int.gcd (v n) (v m) : ℤ) = v (n.gcd m)
  let c := v (n.gcd m)
  have hc : (c.natAbs : ℤ) = c := Int.natAbs_of_nonneg (nonneg (n.gcd m))
  have h := (common_dvd c.natAbs n m).mpr (by rw [hc])
  exact Int.dvd_antisymm (Int.natCast_nonneg _) (nonneg _)
    ((common_dvd _ n m).mp ⟨Int.gcd_dvd_left .., Int.gcd_dvd_right ..⟩)
    (by simpa only [hc] using Int.dvd_coe_gcd h.1 h.2)
