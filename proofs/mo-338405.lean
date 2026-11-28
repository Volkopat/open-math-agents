import OMAStatements.S_mo_338405
import Mathlib

open Matrix Finset

namespace OMA.MatrixOffsets

open OMA.S_mo_338405

private theorem digits (L n k : ℕ) (hL : 0 < L) (hk : k < L ^ n) :
    ∃ a : Fin n → Fin L, (∑ j : Fin n, (a j).val * L ^ j.val) = k := by
  induction n generalizing k with
  | zero =>
      have h : k = 0 := by simpa using hk
      exact ⟨fun j => j.elim0, by simp [h]⟩
  | succ n ih =>
      have hq : k / L < L ^ n := Nat.div_lt_of_lt_mul (by simpa only [pow_succ'] using hk)
      obtain ⟨a, ha⟩ := ih _ hq
      refine ⟨Fin.cons ⟨k % L, Nat.mod_lt _ hL⟩ a, ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
        pow_succ, ← mul_assoc]
      rw [← Finset.sum_mul, ha, Nat.mul_comm (k / L) L, Nat.mod_add_div]

private theorem singular_translate (p d L : ℕ) [Fact p.Prime] (hd : 0 < d)
    (hL : 0 < L) (hp : p ≤ L ^ d) (M : Mat d (ZMod p)) :
    ∃ e : Mat d (Fin L), (M + offset e).det = 0 := by
  let v : Fin d → ZMod p := fun j => (L : ZMod p) ^ j.val
  let r : Fin d → ZMod p := fun i => -(M.mulVec v i)
  have hr (i : Fin d) : (r i).val < L ^ d := (ZMod.val_lt (r i)).trans_le hp
  choose a ha using fun i : Fin d => digits L d (r i).val hL (hr i)
  let e : Mat d (Fin L) := Matrix.of a
  refine ⟨e, ?_⟩
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h (⟨0, hd⟩ : Fin d)
    exact one_ne_zero (by simpa only [v, Fin.val_mk, pow_zero, Pi.zero_apply] using h0)
  have hrow (i : Fin d) : (offset e).mulVec v i = r i := by
    have eq := congrArg (fun k : ℕ => (k : ZMod p)) (ha i)
    push_cast at eq
    rw [ZMod.natCast_zmod_val] at eq
    simpa only [Matrix.mulVec, dotProduct, e, v, offset, Matrix.of_apply] using eq
  have hmv : (M + offset e).mulVec v = 0 := by
    rw [Matrix.add_mulVec]
    funext i
    change M.mulVec v i + (offset e).mulVec v i = 0
    rw [hrow]
    exact add_neg_cancel _
  by_contra h
  have hi : Function.Injective (M + offset e).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h))
  exact hv (hi (hmv.trans (Matrix.mulVec_zero _).symm))

private theorem det_bound {d L : ℕ} (Q : Mat d ℤ) (h : ∀ i j, |Q i j| ≤ (L : ℤ)) :
    |Q.det| ≤ (d.factorial * L ^ d : ℕ) := by
  rw [Matrix.det_apply']
  calc
    |∑ σ : Equiv.Perm (Fin d), (Equiv.Perm.sign σ : ℤ) * ∏ i, Q (σ i) i| ≤
        ∑ σ : Equiv.Perm (Fin d), |(Equiv.Perm.sign σ : ℤ) * ∏ i, Q (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin d), (L : ℤ) ^ d := by
      apply Finset.sum_le_sum
      intro σ hσ
      have hs : |(Equiv.Perm.sign σ : ℤ)| = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsgn | hsgn <;> simp [hsgn]
      rw [abs_mul, hs, one_mul, Finset.abs_prod]
      have hprod : ∏ i : Fin d, |Q (σ i) i| ≤ ∏ _i : Fin d, (L : ℤ) :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => h (σ i) i)
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod
    _ = (d.factorial * L ^ d : ℕ) := by
      simp [Fintype.card_perm, Nat.cast_mul, Nat.cast_pow, mul_comm]

private def center (L : ℕ) : ℕ := L / 2

private def doubled {d L : ℕ} (e : Mat d (Fin L)) : Mat d ℤ :=
  Matrix.of fun i j => 2 * ((e i j).val - (center L : ℤ)) +
    if i = j then 1 else 0

private theorem doubled_entry {d L : ℕ} (e : Mat d (Fin L)) (i j : Fin d) :
    |doubled e i j| ≤ (L : ℤ) := by
  have h := (e i j).isLt
  have hm := Nat.mod_add_div L 2
  apply abs_le.mpr
  change -(L : ℤ) ≤ 2 * ((e i j).val - (center L : ℤ)) + (if i = j then 1 else 0) ∧
    2 * ((e i j).val - (center L : ℤ)) + (if i = j then 1 else 0) ≤ (L : ℤ)
  unfold center
  split <;> omega

private theorem doubled_odd {d L : ℕ} (e : Mat d (Fin L)) :
    ((doubled e).det : ZMod 2) = 1 := by
  have hmap : (doubled e).map (fun z : ℤ => (z : ZMod 2)) = 1 := by
    ext i j
    have htwo : (2 : ZMod 2) = 0 := by decide
    by_cases h : i = j <;>
      simp [doubled, Matrix.one_apply, h, htwo]
  rw [Int.cast_det, hmap, Matrix.det_one]

private theorem translate_large (p d L : ℕ) [Fact p.Prime] (hd : 0 < d) (hL : 2 ≤ L)
    (hp : d.factorial * L ^ d < p) :
    ∃ M : Mat d (ZMod p), ∀ e : Mat d (Fin L), (M + offset e).det ≠ 0 := by
  have hLpow : L ≤ L ^ d := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < L) (by omega : 1 ≤ d)
  have hLt : L ^ d ≤ d.factorial * L ^ d := by
    have hfac : 1 ≤ d.factorial := Nat.factorial_pos d
    simpa only [one_mul] using Nat.mul_le_mul_right (L ^ d) hfac
  have hp2 : 2 < p := (hL.trans (hLpow.trans hLt)).trans_lt hp
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact (not_lt_of_ge (Nat.le_of_dvd (by decide) hdvd)) hp2
  let M : Mat d (ZMod p) := Matrix.of fun i j =>
    (if i = j then (2 : ZMod p)⁻¹ else 0) - (center L : ZMod p)
  refine ⟨M, ?_⟩
  intro e he
  have eq : (doubled e).map (fun z : ℤ => (z : ZMod p)) = (2 : ZMod p) • (M + offset e) := by
    ext i j
    have hinv := mul_inv_cancel₀ htwo
    by_cases hij : i = j <;>
      simp [doubled, M, offset, hij, mul_add, mul_sub, hinv] <;> ring
  have heq : ((doubled e).det : ZMod p) = 0 := by
    rw [Int.cast_det, eq, Matrix.det_smul, he, mul_zero]
  have hnz : (doubled e).det ≠ 0 := by
    intro h
    have h' := doubled_odd e
    rw [h, Int.cast_zero] at h'
    exact zero_ne_one h'
  have hdvd' : (p : ℤ) ∣ (doubled e).det :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp heq
  have hdvd : p ∣ (doubled e).det.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdvd'
  have hpos : 0 < (doubled e).det.natAbs := Int.natAbs_pos.mpr hnz
  have hbounds : (doubled e).det.natAbs ≤ d.factorial * L ^ d := by
    have h' := det_bound (doubled e) (doubled_entry e)
    exact_mod_cast (Int.natCast_natAbs ((doubled e).det)).trans_le h'
  exact (not_lt_of_ge (Nat.le_of_dvd hpos hdvd)) (hbounds.trans_lt hp)

private theorem translate_one (p d : ℕ) [Fact p.Prime] :
    ∃ M : Mat d (ZMod p), ∀ e : Mat d (Fin 1), (M + offset e).det ≠ 0 := by
  refine ⟨1, fun e => ?_⟩
  have he : (offset e : Mat d (ZMod p)) = 0 := by
    ext i j
    simp [offset]
  rw [he, add_zero, Matrix.det_one]
  exact one_ne_zero

end OMA.MatrixOffsets

theorem OMA.solution : type_of% @OMA.S_mo_338405.main := by
  intro p d L _ hd hL
  refine ⟨fun hp M => OMA.MatrixOffsets.singular_translate p d L hd hL hp M, ?_⟩
  rintro (rfl | hp)
  · exact OMA.MatrixOffsets.translate_one p d
  · by_cases hl : L = 1
    · subst L
      exact OMA.MatrixOffsets.translate_one p d
    · exact OMA.MatrixOffsets.translate_large p d L hd (by omega) hp