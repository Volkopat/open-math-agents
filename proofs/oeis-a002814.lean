import OMAStatements.S_oeis_a002814
import Mathlib

namespace PolynomialReturnTimes

open OMA.S_oeis_a002814

private def u (n : ℕ) : ℤ := a (n + 1)
private def v (n : ℕ) : ℤ := u n - 2

private theorem step (n : ℕ) : u (n + 1) = u n ^ 3 + 3 * u n ^ 2 - 3 := rfl

private theorem nonneg (n : ℕ) : 0 ≤ v n := by
  suffices h : 2 ≤ u n by unfold v; omega
  induction n with
  | zero => decide
  | succ n ih =>
    rw [step]
    have h₂ := pow_le_pow_left₀ (by decide : (0 : ℤ) ≤ 2) ih 2
    have h₃ := pow_le_pow_left₀ (by decide : (0 : ℤ) ≤ 2) ih 3
    norm_num at h₂ h₃
    linarith

private theorem same_after_shift (d : ℤ) (m : ℕ) (hm : d ∣ v m) (n : ℕ) :
    u n ≡ u (m + n) [ZMOD d] := by
  induction n with
  | zero =>
    rw [Nat.add_zero]
    exact Int.modEq_iff_dvd.mpr hm
  | succ n ih =>
    change u (n + 1) ≡ u ((m + n) + 1) [ZMOD d]
    rw [step n, step (m + n)]
    exact ((ih.pow 3).add ((Int.ModEq.refl (3 : ℤ)).mul (ih.pow 2))).sub
      (Int.ModEq.refl 3)

private theorem periodic (d : ℤ) (m : ℕ) (hm : d ∣ v m) (n : ℕ) :
    d ∣ v (m + n) ↔ d ∣ v n := by
  change (d ∣ u (m + n) - 2) ↔ d ∣ u n - 2
  rw [← Int.modEq_iff_dvd, ← Int.modEq_iff_dvd]
  have h := same_after_shift d m hm n
  exact ⟨fun h' => h'.trans h.symm, fun h' => h'.trans h⟩

private theorem reduce (d : ℤ) (m : ℕ) (hm : d ∣ v m) (q r : ℕ) :
    d ∣ v (m * q + r) ↔ d ∣ v r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, show m * q + m + r = m + (m * q + r) by omega,
      periodic d m hm, ih]

private theorem common_dvd (d : ℤ) (m n : ℕ) :
    d ∣ v m ∧ d ∣ v n ↔ d ∣ v (Nat.gcd m n) := by
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
    by_cases hm : m = 0
    · subst m
      have hv : v 0 = 0 := by decide
      simp [hv]
    rw [Nat.gcd_rec]
    rw [← ih (n % m) (Nat.mod_lt n (Nat.pos_of_ne_zero hm)) m]
    have hmod (h : d ∣ v m) : d ∣ v n ↔ d ∣ v (n % m) := by
      have hn : m * (n / m) + n % m = n := by
        simpa only [Nat.add_comm] using Nat.mod_add_div n m
      simpa only [hn] using reduce d m h (n / m) (n % m)
    exact ⟨fun ⟨h, h'⟩ => ⟨(hmod h).mp h', h⟩,
      fun ⟨h', h⟩ => ⟨h, (hmod h).mpr h'⟩⟩

private theorem gcd_eq (m n : ℕ) : (Int.gcd (v m) (v n) : ℤ) = v (Nat.gcd m n) := by
  let g := Int.gcd (v m) (v n)
  let c := v (Nat.gcd m n)
  have hc : 0 ≤ c := nonneg _
  have hcabs : (c.natAbs : ℤ) = c := Int.natAbs_of_nonneg hc
  have hg : (g : ℤ) ∣ c := (common_dvd (g : ℤ) m n).mp
    ⟨Int.gcd_dvd_left _ _, Int.gcd_dvd_right _ _⟩
  have hret : c ∣ v m ∧ c ∣ v n := (common_dvd c m n).mpr (dvd_refl _)
  rw [← hcabs] at hg hret
  have hgn : g ∣ c.natAbs := Int.natCast_dvd_natCast.mp hg
  have hcn : c.natAbs ∣ g := Int.dvd_gcd hret.1 hret.2
  exact (congrArg (fun x : ℕ => (x : ℤ)) (Nat.dvd_antisymm hgn hcn)).trans hcabs

end PolynomialReturnTimes

theorem OMA.solution : type_of% @OMA.S_oeis_a002814.main := by
  intro n m _ _
  exact PolynomialReturnTimes.gcd_eq n m