import OMAStatements.S_oeis_a363309
import Mathlib.Tactic.Ring

/-!
# Proof of OEIS A363309

For every integer `n ≥ 1`, we construct formal power series `F, A, B ∈ ℤ⟦X⟧`
satisfying
- `F = 1 + X * F ^ n`,
- `A = F.subst (X * F ^ (2 * n - 1))`,
- `B = A.subst (X * B ^ (n - 1))`,

by strong recursion on coefficients, using the divisibility criterion
`X ^ (k + 1) ∣ P - Q` to show that degree-`k` coefficients of powers and
substitutions depend only on lower-order coefficients.

Given any triple `(F, A, B)` satisfying these equations, substituting
`u = X * F ^ (2 * n - 1)` into `F = 1 + X * F ^ n` yields
`A = 1 + X * F ^ (2 * n - 1) * A ^ n`, and then substituting
`v = X * B ^ (n - 1)` yields `B = 1 + X * R ^ (2 * n - 1)` with
`R = B * F.subst (X * B ^ (n - 1))` and `R.constantCoeff = 1`.
-/

namespace OMA.Proof_oeis_a363309

open PowerSeries

private lemma constantCoeff_subst_of_zero {f g : PowerSeries ℤ}
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.constantCoeff (f.subst g) = PowerSeries.constantCoeff f := by
  have hsub : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  rw [← coeff_zero_eq_constantCoeff, coeff_subst' hsub, finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [coeff_zero_eq_constantCoeff, map_pow, hg, zero_pow hd, smul_zero]

private lemma coeff_pow_eq_of_dvd {P Q : PowerSeries ℤ} {k m : ℕ}
    (h : X ^ (k + 1) ∣ P - Q) :
    coeff k (P ^ m) = coeff k (Q ^ m) := by
  have hd : X ^ (k + 1) ∣ P ^ m - Q ^ m := h.trans (sub_dvd_pow_sub_pow P Q m)
  have h0 : coeff k (P ^ m - Q ^ m) = 0 := X_pow_dvd_iff.mp hd k (Nat.lt_succ_self k)
  rw [map_sub, sub_eq_zero] at h0
  exact h0

private noncomputable def fSeq (n : ℕ) : ℕ → ℤ
  | 0 => 1
  | k + 1 =>
    coeff k ((PowerSeries.mk fun i => if _ : i < k + 1 then fSeq n i else 0) ^ n)

private lemma exists_F (n : ℕ) : ∃ F : PowerSeries ℤ, F = 1 + X * F ^ n := by
  refine ⟨PowerSeries.mk (fSeq n), ?_⟩
  ext k
  cases k with
  | zero =>
    simp [fSeq]
  | succ k =>
    let F : PowerSeries ℤ := PowerSeries.mk (fSeq n)
    let P : PowerSeries ℤ := PowerSeries.mk fun i => if _ : i < k + 1 then fSeq n i else 0
    have hFP : X ^ (k + 1) ∣ F - P := by
      rw [X_pow_dvd_iff]
      intro i hi
      simp [F, P, Nat.lt_succ_iff.mp hi]
    have hpow : coeff k (F ^ n) = coeff k (P ^ n) := coeff_pow_eq_of_dvd hFP
    rw [coeff_mk, map_add, coeff_one, if_neg (Nat.succ_ne_zero k), zero_add, coeff_succ_X_mul, fSeq]
    exact hpow.symm

private noncomputable def bSeq (n : ℕ) (A : PowerSeries ℤ) : ℕ → ℤ
  | 0 => 1
  | k + 1 =>
    coeff (k + 1)
      (A.subst (X * (PowerSeries.mk fun i => if _ : i < k + 1 then bSeq n A i else 0) ^ (n - 1)))

private lemma exists_B (n : ℕ) (A : PowerSeries ℤ) (hA0 : PowerSeries.constantCoeff A = 1) :
    ∃ B : PowerSeries ℤ, B = A.subst (X * B ^ (n - 1)) := by
  refine ⟨PowerSeries.mk (bSeq n A), ?_⟩
  ext k
  cases k with
  | zero =>
    have h0 : PowerSeries.constantCoeff (X * PowerSeries.mk (bSeq n A) ^ (n - 1)) = 0 := by simp
    rw [coeff_mk, coeff_zero_eq_constantCoeff, constantCoeff_subst_of_zero h0, hA0, bSeq]
  | succ k =>
    let B : PowerSeries ℤ := PowerSeries.mk (bSeq n A)
    let Q : PowerSeries ℤ := PowerSeries.mk fun i => if _ : i < k + 1 then bSeq n A i else 0
    let gB : PowerSeries ℤ := X * B ^ (n - 1)
    let gQ : PowerSeries ℤ := X * Q ^ (n - 1)
    have hBQ : X ^ (k + 1) ∣ B - Q := by
      rw [X_pow_dvd_iff]
      intro i hi
      simp [B, Q, Nat.lt_succ_iff.mp hi]
    have hg : X ^ (k + 2) ∣ gB - gQ := by
      have hpow : X ^ (k + 1) ∣ B ^ (n - 1) - Q ^ (n - 1) :=
        hBQ.trans (sub_dvd_pow_sub_pow B Q (n - 1))
      have hmul : X * X ^ (k + 1) ∣ X * (B ^ (n - 1) - Q ^ (n - 1)) :=
        mul_dvd_mul_left X hpow
      have hX : (X : PowerSeries ℤ) ^ (k + 2) = X * X ^ (k + 1) := by rw [pow_succ']
      rw [hX]
      simpa [gB, gQ, mul_sub] using hmul
    have hgB : HasSubst gB := HasSubst.of_constantCoeff_zero' (by simp [gB])
    have hgQ : HasSubst gQ := HasSubst.of_constantCoeff_zero' (by simp [gQ])
    have hsubst : coeff (k + 1) (A.subst gB) = coeff (k + 1) (A.subst gQ) := by
      rw [coeff_subst' hgB, coeff_subst' hgQ]
      refine finsum_congr fun d => ?_
      rw [coeff_pow_eq_of_dvd hg]
    rw [coeff_mk, bSeq]
    exact hsubst.symm

private lemma exists_defines (n : ℕ) :
    ∃ F A B, OMA.S_oeis_a363309.Defines n F A B := by
  obtain ⟨F, hF⟩ := exists_F n
  let A : PowerSeries ℤ := F.subst (X * F ^ (2 * n - 1))
  have hF0 : PowerSeries.constantCoeff F = 1 := by
    have h := congr_arg PowerSeries.constantCoeff hF
    simpa using h
  have hA0 : PowerSeries.constantCoeff A = 1 := by
    dsimp [A]
    rw [constantCoeff_subst_of_zero (by simp), hF0]
  obtain ⟨B, hB⟩ := exists_B n A hA0
  exact ⟨F, A, B, hF, rfl, hB⟩

private lemma exists_root (n : ℕ) (hn : 1 ≤ n) (F A B : PowerSeries ℤ)
    (hdef : OMA.S_oeis_a363309.Defines n F A B) :
    ∃ R : PowerSeries ℤ, PowerSeries.constantCoeff R = 1 ∧ B = 1 + X * R ^ (2 * n - 1) := by
  rcases hdef with ⟨hF, hA, hB⟩
  have hF0 : PowerSeries.constantCoeff F = 1 := by
    have h := congr_arg PowerSeries.constantCoeff hF
    simpa using h
  have hA0 : PowerSeries.constantCoeff A = 1 := by
    rw [hA, constantCoeff_subst_of_zero (by simp), hF0]
  have hB0 : PowerSeries.constantCoeff B = 1 := by
    rw [hB, constantCoeff_subst_of_zero (by simp), hA0]
  let u : PowerSeries ℤ := X * F ^ (2 * n - 1)
  have hu : HasSubst u := HasSubst.of_constantCoeff_zero' (by simp [u])
  have hA_eq : A = 1 + X * F ^ (2 * n - 1) * A ^ n := by
    have h1 : A = substAlgHom hu (1 + X * F ^ n) := by
      rw [coe_substAlgHom hu, ← hF, ← hA]
    rw [map_add, map_one, map_mul, map_pow, substAlgHom_X, coe_substAlgHom hu] at h1
    simpa [u, hA] using h1
  let v : PowerSeries ℤ := X * B ^ (n - 1)
  have hv : HasSubst v := HasSubst.of_constantCoeff_zero' (by simp [v])
  refine ⟨B * F.subst v, ?_, ?_⟩
  · rw [map_mul, hB0, constantCoeff_subst_of_zero (by simp [v]), hF0, mul_one]
  · have h1 : B = substAlgHom hv (1 + X * F ^ (2 * n - 1) * A ^ n) := by
      rw [coe_substAlgHom hv, ← hA_eq, ← hB]
    rw [map_add, map_one, map_mul, map_mul, map_pow, map_pow, substAlgHom_X,
      coe_substAlgHom hv] at h1
    have hAv : A.subst v = B := hB.symm
    rw [hAv] at h1
    have hexp : n - 1 + n = 2 * n - 1 := by omega
    calc
      B = 1 + v * F.subst v ^ (2 * n - 1) * B ^ n := h1
      _ = 1 + X * (B * F.subst v) ^ (2 * n - 1) := by
        rw [mul_pow, ← hexp, pow_add]
        dsimp [v]
        ring

end OMA.Proof_oeis_a363309

theorem OMA.solution : type_of% @OMA.S_oeis_a363309.main := fun n hn =>
  ⟨OMA.Proof_oeis_a363309.exists_defines n, OMA.Proof_oeis_a363309.exists_root n hn⟩
