import OMAStatements.S_mo_282468
import Mathlib

namespace OMA.S_mo_282468
open Polynomial

theorem det_ne_zero {K : Type} [Field K] {n : ℕ} (A : (Sq n K)[X]) (hA : A.Monic) :
    (asMatrix A).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  let N : Sq n K[X] := Matrix.of fun _ j => v j
  have hN : N * asMatrix A = 0 := by
    refine Matrix.ext fun i j => ?_
    have := congrFun hvM j
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, N] using this
  have h2 : matPolyEquiv N * A = 0 := by
    have := congrArg matPolyEquiv hN
    simpa [asMatrix, map_mul] using this
  have h3 : matPolyEquiv N = 0 := (hA.mul_left_eq_zero_iff).mp h2
  have h4 : N = 0 := by simpa using h3
  apply hv
  funext j
  have := congrFun (congrFun h4 0) j
  simpa [N] using this

theorem reduce_add {K : Type} [Field K] {n : ℕ} (A p q : (Sq n K)[X]) :
    reduce A (p + q) = reduce A p + reduce A q := by
  unfold reduce asMatrix
  rw [map_add, map_add]
  rfl

theorem reduce_mul {K : Type} [Field K] {n : ℕ} (A p q : (Sq n K)[X]) :
    reduce A (p * q) = reduce A p * reduce A q := by
  unfold reduce asMatrix
  rw [map_mul, map_mul]
  rfl

theorem forward {K : Type} [Field K] {n : ℕ} (A B p : (Sq n K)[X])
    (h : feasible A B p) : ∃ U V, p = U * A + V * B := by
  obtain ⟨U, V, hUV⟩ := h
  have hs : ∀ W : Sq n (Residue A), ∃ W' : Sq n K[X],
      (AdjoinRoot.mk (asMatrix A).det).mapMatrix W' = W := by
    intro W
    choose f hf using fun i j => AdjoinRoot.mk_surjective (g := (asMatrix A).det) (W i j)
    exact ⟨Matrix.of f, by ext i j; simp [hf]⟩
  obtain ⟨U', rfl⟩ := hs U
  obtain ⟨V', rfl⟩ := hs V
  have hE : (AdjoinRoot.mk (asMatrix A).det).mapMatrix
      (asMatrix p - U' * asMatrix A - V' * asMatrix B) = 0 := by
    rw [map_sub, map_sub, map_mul, map_mul]
    unfold reduce at hUV
    rw [hUV]; abel
  have hdiv : ∀ i j, (asMatrix A).det ∣
      (asMatrix p - U' * asMatrix A - V' * asMatrix B) i j := by
    intro i j
    have := congrFun (congrFun hE i) j
    rw [← AdjoinRoot.mk_eq_zero]
    simpa using this
  choose W hW using hdiv
  have hEq : asMatrix p - U' * asMatrix A - V' * asMatrix B
      = (Matrix.of W * (asMatrix A).adjugate) * asMatrix A := by
    rw [mul_assoc, Matrix.adjugate_mul]
    ext i j
    rw [hW i j]; simp [mul_comm]
  refine ⟨matPolyEquiv (U' + Matrix.of W * (asMatrix A).adjugate), matPolyEquiv V', ?_⟩
  have hp : asMatrix p = (U' + Matrix.of W * (asMatrix A).adjugate) * asMatrix A
      + V' * asMatrix B := by
    rw [add_mul, ← hEq]; abel
  have := congrArg matPolyEquiv hp
  simpa [asMatrix, map_add, map_mul] using this

theorem feas_iff {K : Type} [Field K] {n : ℕ} (A B p : (Sq n K)[X]) :
    feasible A B p ↔ ∃ U V, p = U * A + V * B := by
  constructor
  · exact forward A B p
  · rintro ⟨U, V, rfl⟩
    exact ⟨reduce A U, reduce A V, by rw [reduce_add, reduce_mul, reduce_mul]⟩

theorem cand_eq {K : Type} [Field K] {n : ℕ} (p : (Sq n K)[X]) (hp : p.Monic) :
    candidate p.natDegree (fun i => p.coeff i) = p := by
  unfold candidate
  conv_rhs => rw [hp.as_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => monomial i (p.coeff i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [C_mul_X_pow_eq_monomial]

end OMA.S_mo_282468

open OMA.S_mo_282468 Polynomial in
theorem OMA.solution : type_of% @OMA.S_mo_282468.main := by
  classical
  intro K _ _ n A B hA hB
  refine ⟨?_, feas_iff A B, ?_⟩
  · have hD := det_ne_zero A hA
    have pb := AdjoinRoot.powerBasis hD
    have : Module.Finite K (Residue A) := pb.finite
    exact Module.finite_of_finite K
  · have hne : ∃ m, ∃ p : (Sq n K)[X], p.Monic ∧ (∃ U V, p = U * A + V * B) ∧
        p.natDegree = m := ⟨_, A, hA, ⟨1, 0, by simp⟩, rfl⟩
    obtain ⟨p, hp, hmem, hdeg⟩ := Nat.find_spec hne
    have hmin : ∀ q : (Sq n K)[X], q.Monic → (∃ U V, q = U * A + V * B) →
        Nat.find hne ≤ q.natDegree := fun q hq hq' => Nat.find_min' hne ⟨q, hq, hq', rfl⟩
    have hc := cand_eq p hp
    rw [hdeg] at hc
    refine ⟨Nat.find hne, ?_, fun i => p.coeff i, ?_, ?_, ?_, hmin⟩
    · exact le_min (hmin A hA ⟨1, 0, by simp⟩) (hmin B hB ⟨0, 1, by simp⟩)
    · rw [hc]; exact (feas_iff A B p).mpr hmem
    · rw [hc]; exact hp
    · rw [hc]; exact hdeg
