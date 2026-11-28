import OMAStatements.S_oeis_a210456

namespace FibPeriod

open Finset Function

variable {R : Type*} [CommRing R]

def forward (n : ℕ) (v : Fin n → R) (i : Fin n) : R :=
  if h : i.val + 1 < n then v ⟨i.val + 1, h⟩ else ∑ j, v j

def backward (d : ℕ) (v : Fin (d + 1) → R) : Fin (d + 1) → R :=
  Fin.cons (v (Fin.last d) - ∑ j : Fin d, v j.castSucc) (fun j => v j.castSucc)

@[simp]
theorem forward_last (d : ℕ) (v : Fin (d + 1) → R) :
    forward (d + 1) v (Fin.last d) = ∑ j, v j := by simp [forward]

@[simp]
theorem forward_castSucc (d : ℕ) (v : Fin (d + 1) → R) (i : Fin d) :
    forward (d + 1) v i.castSucc = v i.succ := by
  simp [forward, show i.val + 1 < d + 1 by omega]
  rfl

theorem forward_backward (d : ℕ) :
    LeftInverse (forward (R := R) (d + 1)) (backward d) := by
  intro v
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [backward, Fin.sum_univ_succ]
  · intro j
    simp [backward]

theorem backward_forward (d : ℕ) :
    LeftInverse (backward (R := R) d) (forward (d + 1)) := by
  intro v
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [backward, Fin.sum_univ_succ]
  · intro j
    simp [backward]

theorem advance (n : ℕ) (v : Fin n → R) (m i : ℕ) (hi : i < n) :
    ((forward n)^[m] v) ⟨i, hi⟩ =
    ((forward n)^[m + i] v) ⟨0, by omega⟩ := by
  induction i generalizing m with
  | zero => simp
  | succ i ih =>
      rw [show m + (i + 1) = (m + 1) + i by omega, ← ih (m + 1) (by omega)]
      rw [iterate_succ_apply']
      simp [forward, hi]

open Matrix

def F (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
  Matrix.of fun i j => Fin.lastCases 1 (fun k => if j = k.succ then 1 else 0) i

def B (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
  Matrix.of fun i j =>
    Fin.cases (if j = Fin.last d then 1 else -1)
      (fun k => if j = k.castSucc then 1 else 0) i

@[simp]
theorem F_vec (d : ℕ) (v : Fin (d + 1) → R) : F d *ᵥ v = forward (d + 1) v := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [F, Matrix.mulVec, dotProduct]
  · intro j
    simp [F, Matrix.mulVec, dotProduct, ite_mul]

@[simp]
theorem B_vec (d : ℕ) (v : Fin (d + 1) → R) : B d *ᵥ v = backward d v := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
    simp [B, backward, Finset.sum_neg_distrib]
    ring
  · intro j
    simp [B, backward, Matrix.mulVec, dotProduct, ite_mul]

theorem F_mul_B (d : ℕ) : F d * B d = (1 : Matrix (Fin (d + 1)) _ R) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← Matrix.mulVec_mulVec]
  simpa using forward_backward (R := R) d v

theorem B_mul_F (d : ℕ) : B d * F d = (1 : Matrix (Fin (d + 1)) _ R) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← Matrix.mulVec_mulVec]
  simpa using backward_forward (R := R) d v

theorem pow_vec {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (r : ℕ) (v : Fin n → R) :
    M ^ r *ᵥ v = (fun w => M *ᵥ w)^[r] v := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ', ← Matrix.mulVec_mulVec, iterate_succ_apply', ih]

theorem backward_pow_return (d r : ℕ) (v : Fin (d + 1) → R) :
    (backward d)^[r] v = v ↔ (forward (d + 1))^[r] v = v := by
  have lr : LeftInverse ((forward (R := R) (d + 1))^[r]) ((backward d)^[r]) :=
    (forward_backward d).iterate r
  have rl : LeftInverse ((backward (R := R) d)^[r]) ((forward (d + 1))^[r]) :=
    (backward_forward d).iterate r
  exact ⟨fun h => by simpa only [h] using lr v, fun h => by simpa only [h] using rl v⟩

theorem B_vec_seed (d : ℕ) :
    B d *ᵥ (Pi.single (Fin.last d) 1 : Fin (d + 1) → R) = Pi.single 0 1 := by
  rw [B_vec]
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [backward]
  · intro j
    simp [backward]

theorem B_vec_basis (d : ℕ) (j : Fin d) :
    B d *ᵥ (Pi.single j.castSucc 1 : Fin (d + 1) → R) =
      Pi.single j.succ 1 - Pi.single 0 1 := by
  rw [B_vec]
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [backward, Pi.single_apply, Fin.castSucc_ne_last]
  · intro k
    simp [backward, Pi.single_apply]

theorem power_fix_basis (d r : ℕ)
    (h : (B d : Matrix _ _ R) ^ r *ᵥ Pi.single (Fin.last d) 1 = Pi.single (Fin.last d) 1) :
    (B d : Matrix _ _ R) ^ r = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [Matrix.one_mulVec]
  have hc (v : Fin (d + 1) → R) : B d ^ r *ᵥ (B d *ᵥ v) =
      B d *ᵥ (B d ^ r *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (Commute.refl (B d)).pow_left r |>.eq]
  have h0 := hc (Pi.single (Fin.last d) 1)
  rw [h, B_vec_seed] at h0
  obtain ⟨i, hi⟩ := j
  change B d ^ r *ᵥ Pi.single ⟨i, hi⟩ (1 : R) = Pi.single ⟨i, hi⟩ 1
  induction i with
  | zero => exact h0
  | succ i ih =>
      let k : Fin d := ⟨i, by omega⟩
      have hb := hc (Pi.single k.castSucc 1)
      have hk : (B d : Matrix _ _ R) ^ r *ᵥ Pi.single k.castSucc 1 =
          Pi.single k.castSucc 1 := ih (by omega)
      rw [hk] at hb
      rw [B_vec_basis, Matrix.mulVec_sub, h0] at hb
      exact sub_left_inj.mp hb

theorem backward_last (d i : ℕ) (hi : i < d + 1) (v : Fin (d + 1) → R) :
    (backward d)^[i] v ⟨i, hi⟩ = v 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [iterate_succ_apply']
      exact ih (by omega)

theorem sum_backward (d : ℕ) (v : Fin (d + 1) → R) :
    (∑ i, backward d v i) = v (Fin.last d) := by
  simpa only [forward_last] using congrFun (forward_backward d v) (Fin.last d)

theorem backward_head (d : ℕ) (v : Fin (d + 1) → R) :
    (backward d)^[d+2] v 0 = (2 : R) * backward d v 0 - v 0 := by
  have h₀ : ((backward d)^[d] v) (Fin.last d) = v 0 := backward_last d d (by omega) _
  have h₁ : ((backward d)^[d+1] v) (Fin.last d) = backward d v 0 := by
    rw [iterate_succ_apply]
    exact backward_last d d (by omega) _
  rw [iterate_succ_apply' (n := d+1)]
  change ((backward d)^[d+1] v) (Fin.last d) -
    (∑ j : Fin d, ((backward d)^[d+1] v) j.castSucc) = _
  have hsum : (∑ j, ((backward d)^[d+1] v) j) = v 0 := by
    rw [iterate_succ_apply', sum_backward, h₀]
  rw [Fin.sum_univ_castSucc, h₁] at hsum
  rw [h₁]
  linear_combination -hsum

theorem B_relation (d : ℕ) : (B d : Matrix _ _ R) ^ (d+2) = 2 * B d - 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  funext i
  have hcoord (u : Fin (d+1) → R) :
      u i = (((F d) ^ i.val) *ᵥ u) 0 := by
    rw [pow_vec]
    simp_rw [F_vec]
    simpa using advance (d+1) u 0 i.val i.isLt
  have hcomm : Commute (F d : Matrix _ _ R) (B d) :=
    show F d * B d = B d * F d by rw [F_mul_B, B_mul_F]
  have hm (q : ℕ) (u : Fin (d+1) → R) :
      F d ^ i.val *ᵥ (B d ^ q *ᵥ u) = B d ^ q *ᵥ (F d ^ i.val *ᵥ u) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ((hcomm.pow_left i.val).pow_right q).eq]
  have hm1 (u : Fin (d+1) → R) :
      F d ^ i.val *ᵥ (B d *ᵥ u) = B d *ᵥ (F d ^ i.val *ᵥ u) := by simpa using hm 1 u
  rw [hcoord (B d ^ (d+2) *ᵥ v), hcoord ((2 * B d - 1) *ᵥ v), hm,
    Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    show (2 : Matrix (Fin (d+1)) (Fin (d+1)) R) *ᵥ (B d *ᵥ v) =
      (2 : R) • (B d *ᵥ v) from Matrix.natCast_mulVec 2 _, Matrix.one_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_smul, hm1]
  have h := backward_head d (F d ^ i.val *ᵥ v)
  rw [pow_vec]
  simp only [B_vec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at *
  exact h

theorem backward_support (d r : ℕ) (hr : 0 < r) (i : Fin (d+1)) (hi : r ≤ i.val) :
    (backward (R := R) d)^[r] (Pi.single (Fin.last d) 1) i = 0 := by
  induction r generalizing i with
  | zero => omega
  | succ r ih =>
      rw [iterate_succ_apply']
      by_cases h : r = 0
      · subst r
        simp only [iterate_zero, id_eq, ← B_vec, B_vec_seed]
        have hn : i ≠ 0 := fun h => by subst i; simp at hi
        simp [hn]
      · cases i using Fin.cases with
        | zero => simp at hi
        | succ j =>
            change (backward d)^[r] (Pi.single (Fin.last d) (1 : R)) j.castSucc = 0
            apply ih (by omega)
            simpa using (show r ≤ j.val by simpa using hi)

end FibPeriod
namespace DigitalPeriod

open Finset Function Matrix
open FibPeriod
open OMA.S_oeis_a210456

theorem cast_root (m : ℕ) : (digitalRoot m : ZMod 9) = (m : ZMod 9) := by
  by_cases h : m = 0
  · simp [digitalRoot, h]
  · rw [digitalRoot, if_neg h, Nat.cast_add, ZMod.natCast_mod, ← Nat.cast_add,
      Nat.sub_add_cancel (by omega : 1 ≤ m)]

theorem cast_inj {a b : ℕ} (ha : 1 ≤ a ∧ a ≤ 9) (hb : 1 ≤ b ∧ b ≤ 9)
    (h : (a : ZMod 9) = b) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  omega

def digitCast {n : ℕ} (v : Fin n → ℕ) (i : Fin n) : ZMod 9 := v i

theorem step_cast (n : ℕ) (v : Fin n → ℕ) :
    digitCast (vstep n v) = forward n (digitCast v) := by
  funext i
  by_cases h : i.val+1 < n
  · simp [digitCast, vstep, forward, h]
  · simp [digitCast, vstep, forward, h, cast_root, Nat.cast_sum]

theorem cast_state (d m : ℕ) :
    digitCast (vstate (d+1) m) = (forward (d+1))^[m] (digitCast (vinit (d+1))) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [vstate, iterate_succ_apply', step_cast, iterate_succ_apply']
    exact congrArg (forward (d+1)) ih

theorem cast_seed (d : ℕ) : digitCast (vinit (d+1)) = Pi.single (Fin.last d) 1 := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [digitCast, vinit]
  · intro j
    simp [digitCast, vinit, show j.val + 1 < d + 1 by omega]

theorem advance (n : ℕ) (v : Fin n → ℕ) (m i : ℕ) (hi : i < n) :
    ((vstep n)^[m] v) ⟨i, hi⟩ = ((vstep n)^[m+i] v) ⟨0, by omega⟩ := by
  induction i generalizing m with
  | zero => simp
  | succ i ih =>
    rw [show m+(i+1)=(m+1)+i by omega, ← ih (m+1) (by omega)]
    rw [iterate_succ_apply']
    simp [vstep, hi]

theorem last_bounds (d m : ℕ) :
    1 ≤ vstate (d+1) m (Fin.last d) ∧ vstate (d+1) m (Fin.last d) ≤ 9 := by
  induction m with
  | zero => simp [vstate, vinit]
  | succ m ih =>
    have h : 1 ≤ ∑ i, vstate (d+1) m i :=
      ih.1.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (Fin.last d)))
    have hh : vstate (d+1) (m+1) (Fin.last d) =
        digitalRoot (∑ i, vstate (d+1) m i) := by
      simp [vstate, iterate_succ_apply' (n := m), vstep]
    rw [hh]
    simp only [digitalRoot, if_neg (show (∑ i, vstate (d+1) m i) ≠ 0 by omega)]
    constructor
    · omega
    · have := Nat.mod_lt ((∑ i, vstate (d+1) m i)-1) (by decide : 0 < 9)
      omega

theorem head_bounds (d m : ℕ) (hm : d ≤ m) : 1 ≤ seqN (d+1) m ∧ seqN (d+1) m ≤ 9 := by
  have h := advance (d+1) (vinit (d+1)) (m-d) d (Nat.lt_succ_self d)
  rw [Nat.sub_add_cancel hm] at h
  change vstate (d+1) (m-d) (Fin.last d) = vstate (d+1) m ⟨0, by omega⟩ at h
  rw [seqN, dif_pos (Nat.succ_pos d), ← h]
  exact last_bounds d (m-d)

/-- After the initial zeros, casting to ZMod 9 detects equality of digital roots. -/
theorem period_iff_return (d r : ℕ) :
    IsEventualPeriod (d+1) r ↔
      (forward (d+1))^[r] (digitCast (vinit (d+1))) = digitCast (vinit (d+1)) := by
  let v := digitCast (vinit (d+1))
  have hseq (m : ℕ) : (seqN (d+1) m : ZMod 9) = ((forward (d+1))^[m] v) 0 := by
    rw [seqN, dif_pos (Nat.succ_pos d)]
    exact congrFun (cast_state d m) 0
  constructor
  · rintro ⟨m, hm⟩
    apply (backward_forward (R := ZMod 9) d).injective.iterate m
    rw [← iterate_add_apply]
    funext i
    obtain ⟨i, hi⟩ := i
    change ((forward (d+1))^[m+r] v) ⟨i, hi⟩ = ((forward (d+1))^[m] v) ⟨i, hi⟩
    have hh := congrArg (fun n : ℕ => (n : ZMod 9)) (hm (m+i) (by omega))
    rw [hseq, hseq] at hh
    rw [FibPeriod.advance (d+1) v (m+r) i hi, FibPeriod.advance (d+1) v m i hi,
      show m+r+i=m+i+r by omega]
    exact hh
  · intro h
    refine ⟨d, fun m hm => ?_⟩
    apply cast_inj (head_bounds d (m+r) (by omega)) (head_bounds d m hm)
    rw [hseq, hseq, iterate_add_apply, h]

theorem period_eq_order (d : ℕ) :
    a210456 (d+1) = orderOf (B d : Matrix _ _ (ZMod 9)) := by
  have hh (r : ℕ) : IsEventualPeriod (d+1) r ↔ (B d : Matrix _ _ (ZMod 9))^r = 1 := by
    rw [period_iff_return, cast_seed, ← backward_pow_return]
    rw [show (backward d : (Fin (d+1) → ZMod 9) → _) = fun v => B d *ᵥ v from
      funext (B_vec d) |>.symm, ← pow_vec]
    exact ⟨power_fix_basis d r, fun h => by rw [h, Matrix.one_mulVec]⟩
  rw [a210456, orderOf, minimalPeriod_eq_sInf_n_pos_IsPeriodicPt]
  apply congrArg sInf
  ext r
  exact and_congr_right' ((hh r).trans (isPeriodicPt_mul_iff_pow_eq_one _).symm)

theorem period_zero : a210456 0 = 1 := by
  have h (r : ℕ) : IsEventualPeriod 0 r := ⟨0, by simp [seqN]⟩
  have hs : periodSet 0 = Set.Ici 1 := by
    ext r
    simp [h, Nat.succ_le_iff]
  rw [a210456, hs, csInf_Ici]

end DigitalPeriod
namespace DigitalPeriod

open Polynomial Finset Matrix Function
open FibPeriod

section Companion

variable {R : Type*} [CommRing R]

abbrev BMat (d : ℕ) := Matrix (Fin (d+1)) (Fin (d+1)) R

noncomputable def inversePolynomial (R : Type*) [CommRing R] (d : ℕ) : R[X] :=
  (∑ i ∈ range (d+1), X^(i+1)) - 1

theorem inversePolynomial_relation (d : ℕ) :
    (X-1) * inversePolynomial R d = X^(d+2) - 2*X + 1 := by
  have h (j : ℕ) : (X-1 : R[X]) * (∑ i ∈ range j, X^(i+1)) = X^(j+1) - X := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [sum_range_succ, mul_add, ih, pow_succ X (j+1)]
      ring
  rw [inversePolynomial, mul_sub, h]
  ring

theorem inversePolynomial_form (d : ℕ) :
    inversePolynomial R d = X^(d+1) + ((∑ i ∈ range d, X^(i+1)) - 1) := by
  rw [inversePolynomial, sum_range_succ]
  ring

theorem inversePolynomial_tail_degree (d : ℕ) :
    ((∑ i ∈ range d, (X : R[X])^(i+1)) - 1).natDegree ≤ d := by
  calc
    _ ≤ max d 0 := natDegree_sub_le_of_le
      (natDegree_sum_le_of_forall_le _ _ fun i hi =>
        (natDegree_X_pow_le (i+1)).trans (mem_range.mp hi)) (by rw [natDegree_one])
    _ = d := max_eq_left (Nat.zero_le d)

theorem inversePolynomial_monic [Nontrivial R] (d : ℕ) : (inversePolynomial R d).Monic := by
  rw [inversePolynomial_form]
  have hd := inversePolynomial_tail_degree (R := R) d
  exact monic_X_pow_add (lt_of_le_of_lt degree_le_natDegree
    (by exact_mod_cast Nat.lt_succ_of_le hd))

theorem inversePolynomial_natDegree [Nontrivial R] (d : ℕ) :
    (inversePolynomial R d).natDegree = d+1 := by
  rw [inversePolynomial_form, natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
  rw [natDegree_X_pow]
  exact Nat.lt_succ_of_le (inversePolynomial_tail_degree (R := R) d)

theorem B_seed_sum (d j : ℕ) (hj : 0 < j) (hjd : j ≤ d+1) :
    (∑ i ∈ range j, ((B d : BMat (R := R) d)^(i+1)) *ᵥ Pi.single (Fin.last d) 1) =
      Pi.single (⟨j-1, by omega⟩ : Fin (d+1)) 1 := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [sum_range_succ']
    by_cases h : j = 0
    · subst j
      rw [sum_range_zero, zero_add, pow_one]
      exact B_vec_seed (R := R) d
    · have hterm (i : ℕ) : ((B d : BMat (R := R) d)^(i+1+1)) *ᵥ Pi.single (Fin.last d) 1 =
          B d *ᵥ (B d^(i+1) *ᵥ Pi.single (Fin.last d) 1) := by
        rw [pow_succ', ← Matrix.mulVec_mulVec]
      simp_rw [hterm]
      rw [← Matrix.mulVec_sum, ih (by omega) (by omega), pow_one, B_vec_seed]
      let k : Fin d := ⟨j-1, by omega⟩
      change B d *ᵥ Pi.single k.castSucc (1 : R) + Pi.single 0 1 = Pi.single ⟨j, by omega⟩ 1
      rw [B_vec_basis, sub_add_cancel]
      congr 1
      apply Fin.ext
      simp [k]
      omega

theorem commute_zero_of_seed (d : ℕ) (A : BMat (R := R) d) (hc : Commute A (B d))
    (hz : A *ᵥ Pi.single (Fin.last d) 1 = 0) : A = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [Matrix.zero_mulVec]
  have hcomm (v : Fin (d+1) → R) : A *ᵥ (B d *ᵥ v) = B d *ᵥ (A *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc.eq]
  have h0 := hcomm (Pi.single (Fin.last d) 1)
  rw [hz, B_vec_seed, Matrix.mulVec_zero] at h0
  obtain ⟨i, hi⟩ := j
  change A *ᵥ Pi.single ⟨i, hi⟩ 1 = 0
  induction i with
  | zero => exact h0
  | succ i ih =>
    let k : Fin d := ⟨i, by omega⟩
    have hb := hcomm (Pi.single k.castSucc 1)
    have hk : A *ᵥ Pi.single k.castSucc 1 = 0 := ih (by omega)
    rw [hk, Matrix.mulVec_zero, B_vec_basis, Matrix.mulVec_sub, h0, sub_zero] at hb
    exact hb

theorem aeval_inversePolynomial (d : ℕ) : aeval (B d : BMat (R := R) d)
    (inversePolynomial R d) = 0 := by
  have hc : Commute (aeval (B d : BMat (R := R) d) (inversePolynomial R d)) (B d) := by
    simpa only [aeval_X] using (Commute.all (inversePolynomial R d) X).map (aeval (B d : BMat (R := R) d))
  refine commute_zero_of_seed d _ hc ?_
  simp only [inversePolynomial, map_sub, map_sum, map_pow, aeval_X, map_one,
    Matrix.sub_mulVec, Matrix.sum_mulVec, Matrix.one_mulVec]
  rw [B_seed_sum d (d+1) (by omega) (by omega)]
  exact sub_self _

theorem backward_top (d r : ℕ) (hr : 0 < r) (hle : r ≤ d+1) :
    (backward (R := R) d)^[r] (Pi.single (Fin.last d) 1) ⟨r-1, by omega⟩ = 1 := by
  induction r with
  | zero => omega
  | succ r ih =>
    rw [iterate_succ_apply']
    by_cases h : r = 0
    · subst r
      simp only [iterate_zero, id_eq, ← B_vec, B_vec_seed]
      simp
    · let k : Fin d := ⟨r-1, by omega⟩
      have hh : (⟨r+1-1, by omega⟩ : Fin (d+1)) = k.succ := by
        apply Fin.ext
        simp [k]
        omega
      rw [hh]
      exact ih (by omega) (by omega)

theorem aeval_seed [Nontrivial R] (d : ℕ) (f : R[X]) :
    aeval (B d : BMat (R := R) d) f *ᵥ Pi.single (Fin.last d) 1 =
      ∑ j ∈ range (f.natDegree+1), f.coeff j •
        ((backward d)^[j] (Pi.single (Fin.last d) 1)) := by
  conv_lhs => rw [f.as_sum_range_C_mul_X_pow]
  simp only [map_sum, map_mul, aeval_C, map_pow, aeval_X, Matrix.sum_mulVec]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.mulVec_mulVec, Matrix.algebraMap_eq_diagonal]
  change diagonal (fun _ => f.coeff j) *ᵥ _ = _
  rw [Matrix.diagonal_const_mulVec, pow_vec]
  simp_rw [B_vec]

theorem small_annihilator [Nontrivial R] (d : ℕ) (f : R[X]) (hd : f.natDegree < d+1)
    (hz : aeval (B d : BMat (R := R) d) f = 0) : f = 0 := by
  by_contra hn
  have hc : f.coeff f.natDegree ≠ 0 := (leadingCoeff_ne_zero.mpr hn)
  have hv := aeval_seed d f
  rw [hz, Matrix.zero_mulVec] at hv
  by_cases h : f.natDegree = 0
  · apply hc
    have he := congrFun hv (Fin.last d)
    simpa [h] using he.symm
  · let t := f.natDegree
    let i : Fin (d+1) := ⟨t-1, by dsimp [t]; omega⟩
    have ht : 0 < t := by dsimp [t]; omega
    have he := congrFun hv i
    change (0 : R) = (∑ j ∈ range (t+1), f.coeff j •
      ((backward d)^[j] (Pi.single (Fin.last d) 1))) i at he
    rw [sum_range_succ, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
    have hbelow : (∑ j ∈ range t, (f.coeff j •
        ((backward (R := R) d)^[j] (Pi.single (Fin.last d) 1))) i) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Pi.smul_apply, smul_eq_mul]
      have hjt := mem_range.mp hj
      by_cases hzj : j = 0
      · subst j
        have hi : i ≠ Fin.last d := by
          intro he
          have := congrArg Fin.val he
          simp [i, t] at this
          omega
        simp [hi]
      · rw [backward_support d j (by omega) i (by dsimp [i]; omega), mul_zero]
    have htop : (backward (R := R) d)^[t] (Pi.single (Fin.last d) 1) i = 1 :=
      backward_top d t ht (by dsimp [t]; omega)
    rw [hbelow, zero_add, htop, mul_one] at he
    exact hc he.symm

/-- The seed is cyclic, so the inverse shift has the stated monic annihilator of least degree. -/
theorem inversePolynomial_dvd_iff [Nontrivial R] (d : ℕ) (p : R[X]) :
    inversePolynomial R d ∣ p ↔ aeval (B d : BMat (R := R) d) p = 0 := by
  let f := inversePolynomial R d
  have hf : f.Monic := inversePolynomial_monic d
  constructor
  · rintro ⟨g, rfl⟩
    rw [map_mul, aeval_inversePolynomial d, zero_mul]
  · intro h
    have hd := Polynomial.modByMonic_add_div p f
    have he := congrArg (aeval (B d : BMat (R := R) d)) hd
    simp only [map_add, map_mul, show aeval (B d : BMat (R := R) d) f = 0
      from aeval_inversePolynomial d, zero_mul, add_zero, h] at he
    have hdg : (p %ₘ f).natDegree < d+1 := by
      by_cases hz : p %ₘ f = 0
      · simp [hz]
      · have hdg := degree_modByMonic_lt p hf
        rw [degree_eq_natDegree hz, degree_eq_natDegree hf.ne_zero, inversePolynomial_natDegree] at hdg
        exact_mod_cast hdg
    exact (modByMonic_eq_zero_iff_dvd hf).mp (small_annihilator d _ hdg he)

end Companion
end DigitalPeriod
namespace FibPeriod
open Matrix

abbrev IMat (d : ℕ) := Matrix (Fin (d+1)) (Fin (d+1)) ℤ

def red {d : ℕ} (k : ℕ) : IMat d →+* Matrix (Fin (d+1)) (Fin (d+1)) (ZMod k) :=
  (Int.castRingHom (ZMod k)).mapMatrix

@[simp]
theorem red_B (d k : ℕ) : red k (B d : IMat d) = B d := by
  ext i j
  cases i using Fin.cases <;> simp [red, B]

theorem scalar_apply_entry {d : ℕ} (k : ℕ) (A : IMat d) (i j : Fin (d+1)) :
    (((k : IMat d) * A) i j) = (k : ℤ) * A i j := by
  simp [Matrix.mul_apply, Matrix.natCast_apply, ite_mul]

theorem red_eq_zero {d : ℕ} (k : ℕ) (M : IMat d) :
    red k M = 0 ↔ (k : IMat d) ∣ M := by
  constructor
  · intro h
    have he (i j : Fin (d+1)) : (k : ℤ) ∣ M i j := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      have hh := congrArg (fun (A : Matrix (Fin (d+1)) _ (ZMod k)) => A i j) h
      exact hh
    choose q hq using he
    refine ⟨Matrix.of q, ?_⟩
    ext i j
    rw [scalar_apply_entry]
    exact hq i j
  · rintro ⟨Q, rfl⟩
    rw [map_mul, map_natCast]
    have hzero : (k : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod k)) = 0 := by
      rw [← Matrix.diagonal_natCast]
      simp
    rw [hzero, zero_mul]

theorem B_order_pos (d k : ℕ) (hk : 0 < k) :
    0 < orderOf (B d : Matrix _ _ (ZMod k)) := by
  let : NeZero k := ⟨hk.ne'⟩
  have hu : IsUnit (B d : Matrix _ _ (ZMod k)) :=
    ⟨⟨B d, F d, B_mul_F d, F_mul_B d⟩, rfl⟩
  exact hu.isOfFinOrder.orderOf_pos

theorem B_zero_one (k : ℕ) : (B 0 : Matrix _ _ (ZMod k)) = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [B]

theorem scalar_cancel {d k : ℕ} (hk : 0 < k) {A C : IMat d}
    (h : (k : IMat d) * A = (k : IMat d) * C) : A = C := by
  ext i j
  have ht := congrArg (fun (X : IMat d) => X i j) h
  simp only [scalar_apply_entry] at ht
  exact mul_left_cancel₀ (by exact_mod_cast hk.ne') ht

end FibPeriod
namespace DigitalPeriod

open Matrix Polynomial
open FibPeriod

def modThree : ZMod 9 →+* ZMod 3 := ZMod.castHom (by decide : 3 ∣ 9) (ZMod 3)

def matrixThree {d : ℕ} : BMat (R := ZMod 9) d →+* BMat (R := ZMod 3) d :=
  modThree.mapMatrix

theorem modThree_aeval {d : ℕ} (p : (ZMod 9)[X]) (A : BMat (R := ZMod 9) d) :
    matrixThree (aeval A p) = aeval (matrixThree A) (p.map modThree) := by
  apply map_aeval_eq_aeval_map
  ext c i j
  by_cases h : i = j <;>
    simp [RingHom.comp_apply, Matrix.algebraMap_matrix_apply, matrixThree, h]

theorem modThree_red {d : ℕ} (A : IMat d) : matrixThree (red 9 A) = red 3 A := by
  ext i j
  exact map_intCast modThree (A i j)

theorem red_surj (d k : ℕ) : Function.Surjective (red (d := d) k) := by
  intro A
  have h (i j : Fin (d+1)) : ∃ z : ℤ, (z : ZMod k) = A i j := ZMod.intCast_surjective _
  choose u hu using h
  exact ⟨Matrix.of u, Matrix.ext hu⟩

theorem matrixThree_surj (d : ℕ) : Function.Surjective (matrixThree (d := d)) := by
  intro A
  obtain ⟨M, rfl⟩ := red_surj d 3 A
  exact ⟨red 9 M, modThree_red M⟩

theorem matrixThree_kernel {d : ℕ} (A : BMat (R := ZMod 9) d) (h : matrixThree A = 0) :
    ∃ C : BMat (R := ZMod 9) d, A = 3 * C := by
  obtain ⟨M, rfl⟩ := red_surj d 9 A
  rw [modThree_red] at h
  obtain ⟨Q, hQ⟩ := (red_eq_zero 3 M).mp h
  refine ⟨red 9 Q, ?_⟩
  rw [hQ, map_mul, map_natCast]
  rfl

theorem cube_aeval {d : ℕ} (p : (ZMod 3)[X]) (A : BMat (R := ZMod 3) d) :
    aeval (A^3) p = (aeval A p)^3 := by
  have hf : frobenius (ZMod 3) 3 = RingHom.id _ := RingHom.ext (ZMod.pow_card)
  have he := map_frobenius_expand (R := ZMod 3) 3 p
  rw [hf, Polynomial.map_id] at he
  rw [← Polynomial.expand_aeval, he, map_pow]

theorem right_inverse_lift {d : ℕ} (A : BMat (R := ZMod 9) d)
    (h : ∃ C, matrixThree A * C = 1) : ∃ C, A * C = 1 := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨D, rfl⟩ := matrixThree_surj d C
  have hs : matrixThree (A*D-1) = 0 := by rw [map_sub, map_mul, map_one, hC, sub_self]
  obtain ⟨E, hE⟩ := matrixThree_kernel _ hs
  refine ⟨D*(1-3*E), ?_⟩
  have h9 : (9 : BMat (R := ZMod 9) d) = 0 := CharP.cast_eq_zero _ 9
  rw [← mul_assoc, show A*D = 1+3*E by rw [← hE]; abel]
  calc
    _ = 1 - 9 * E^2 := by noncomm_ring
    _ = 1 := by rw [h9, zero_mul, sub_zero]

theorem B_three_ne_one (d : ℕ) (hd : 0 < d) :
    (B d : BMat (R := ZMod 3) d) ≠ 1 := by
  intro h
  have hseed := B_vec_seed (R := ZMod 3) d
  rw [h, Matrix.one_mulVec] at hseed
  have h0 := congrFun hseed 0
  have hi : (0 : Fin (d+1)) ≠ Fin.last d := by
    intro e
    have := congrArg Fin.val e
    exact hd.ne' (by simpa using this.symm)
  simp [hi] at h0

theorem id_plus_sq_zero_pow {R : Type*} [Ring R] (A : R) (h : A^2 = 0) (r : ℕ) :
    (1+A)^r = 1 + (r : R)*A := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    calc
      _ = 1 + ((r : R) + 1)*A + (r : R)*A^2 := by noncomm_ring
      _ = _ := by rw [h, mul_zero, add_zero]

/-- An order prime to three would make the polynomial factorization modulo nine separable after reduction.
The cubed inverse shift would satisfy the same relation, forcing the original shift to be identity modulo three. -/
theorem three_dvd_order_nine (d : ℕ) (hd : 0 < d) :
    3 ∣ orderOf (B d : BMat (R := ZMod 9) d) := by
  let : Fact (1 < 9) := ⟨by decide⟩
  let M : BMat (R := ZMod 9) d := B d
  let N : BMat (R := ZMod 3) d := B d
  let r := orderOf M
  have hp : M^r = 1 := pow_orderOf_eq_one M
  have hred : matrixThree M = N := by
    change matrixThree (B d) = B d
    rw [← red_B d 9, modThree_red, red_B]
  by_contra hr
  let f := inversePolynomial (ZMod 9) d
  have hfa : f ∣ X^r-1 := by
    apply (inversePolynomial_dvd_iff d _).mpr
    simp only [map_sub, map_pow, aeval_X, map_one]
    exact sub_eq_zero.mpr hp
  obtain ⟨g, hg⟩ := hfa
  let f₃ := f.map modThree
  let g₃ := g.map modThree
  have hfg : (X^r-1 : (ZMod 3)[X]) = f₃*g₃ := by
    simpa [f₃, g₃] using congrArg (Polynomial.map modThree) hg
  have hsep : (f₃*g₃).Separable := by
    rw [← hfg, ← C_1]
    exact Polynomial.separable_X_pow_sub_C' 3 r 1 hr one_ne_zero
  obtain ⟨u, v, huv⟩ := hsep.isCoprime
  have hz : aeval N f₃ = 0 := by
    rw [← hred, ← modThree_aeval]
    change matrixThree (aeval (B d) (inversePolynomial (ZMod 9) d)) = 0
    rw [aeval_inversePolynomial, map_zero]
  have hright : ∃ C, aeval (M^3) g * C = 1 := by
    apply right_inverse_lift
    rw [modThree_aeval, map_pow, hred, cube_aeval]
    have hv := congrArg (aeval N) huv
    simp only [map_add, map_mul, map_one, hz, mul_zero, zero_add] at hv
    have hcomm : Commute (aeval N v) (aeval N g₃) :=
      (Commute.all v g₃).map (aeval N)
    have hv' : aeval N g₃ * aeval N v = 1 := hcomm.eq.symm.trans hv
    exact ⟨(aeval N v)^3, by rw [← hcomm.symm.mul_pow, hv', one_pow]⟩
  obtain ⟨C, hC⟩ := hright
  have hp3 : (M^3)^r = 1 := by rw [pow_right_comm, hp, one_pow]
  have hmul : aeval (M^3) f * aeval (M^3) g = 0 := by
    rw [← map_mul, ← hg, map_sub, map_pow, aeval_X, map_one, hp3, sub_self]
  have hf3 : aeval (M^3) f = 0 := by
    rw [← mul_one (aeval (M^3) f), ← hC, ← mul_assoc, hmul, zero_mul]
  have hrel := congrArg (aeval (M^3)) (inversePolynomial_relation (R := ZMod 9) d)
  change aeval (M^3) ((X-1)*f) = _ at hrel
  simp only [map_mul, hf3, mul_zero, map_add, map_sub, map_pow, aeval_X, map_ofNat, map_one] at hrel
  have hM : M^(d+2) = 2*M-1 := B_relation d
  rw [pow_right_comm M 3 (d+2), hM] at hrel
  have he : 6 * M * (M-1)^2 = 0 := by
    rw [eq_comm] at hrel
    calc
      _ = (2*M-1)^3-2*M^3+1 := by noncomm_ring
      _ = 0 := hrel
  have hsq9 : (3 : BMat (R := ZMod 9) d) * (M-1)^2 = 0 := by
    have hmul := congrArg (fun A => (5 : BMat (R := ZMod 9) d) * (F d * A)) he
    have hcomm : Commute (6 : BMat (R := ZMod 9) d) (F d) := Nat.cast_commute 6 _
    have h6 : F d * (6*M*(M-1)^2) = 6*(M-1)^2 := by
      calc
        _ = (F d * 6) * M * (M-1)^2 := by simp only [mul_assoc]
        _ = _ := by rw [← hcomm.eq, mul_assoc (6 : BMat (R := ZMod 9) d),
          show F d * M = 1 from F_mul_B d, mul_one]
    have hc : (5 : BMat (R := ZMod 9) d) * 6 = 3 := by
      simpa only [map_mul, map_ofNat] using
        congrArg (algebraMap (ZMod 9) (BMat (R := ZMod 9) d))
          (by decide : (5 : ZMod 9) * 6 = 3)
    simpa only [h6, ← mul_assoc, hc, mul_zero] using hmul
  have hsq3 : (N-1)^2 = 0 := by
    have hy := red_eq_zero 9 ((3 : IMat d)*(B d-1)^2)
    have hD : red 9 ((3 : IMat d)*(B d-1)^2) = 0 := by
      simpa only [map_mul, map_pow, map_sub, map_ofNat, map_one, red_B] using hsq9
    obtain ⟨U, hU⟩ := hy.mp hD
    have hcan : (B d-1)^2 = (3 : IMat d)*U := by
      apply scalar_cancel (k := 3) (by decide)
      change (3 : IMat d)*(B d-1)^2 = 3*(3*U)
      have heq : (3 : IMat d)*3 = (9 : ℕ) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          congrArg (fun z : ℕ => (z : IMat d)) (by decide : (3 : ℕ)*3=9)
      rw [← mul_assoc, heq]
      exact hU
    have hm3 := congrArg (red 3) hcan
    simp only [map_pow, map_sub, map_one, red_B, map_mul, map_ofNat] at hm3
    rw [show (3 : BMat (R := ZMod 3) d) = 0 from CharP.cast_eq_zero _ 3, zero_mul] at hm3
    exact hm3
  have hn : N^r=1 := by
    have hm := congrArg (matrixThree (d := d)) hp
    simpa only [map_pow, hred, map_one] using hm
  have hlin := id_plus_sq_zero_pow (N-1) hsq3 r
  rw [show 1+(N-1)=N by abel, hn] at hlin
  have hz : (r : BMat (R := ZMod 3) d)*(N-1)=0 := by
    exact add_left_cancel (by simpa only [add_zero] using hlin.symm)
  have hruz : (r : ZMod 3) ≠ 0 := fun hh => hr ((ZMod.natCast_eq_zero_iff r 3).mp hh)
  have hunit : IsUnit (r : BMat (R := ZMod 3) d) := by
    have hh := (isUnit_iff_ne_zero.mpr hruz).map (algebraMap (ZMod 3) (BMat (R := ZMod 3) d))
    simpa only [map_natCast] using hh
  have hzero : N-1=0 := hunit.mul_left_cancel (hz.trans (mul_zero _).symm)
  exact B_three_ne_one d hd (sub_eq_zero.mp hzero)

end DigitalPeriod
namespace DigitalPeriod

open Polynomial Matrix
open FibPeriod

theorem neg_add_one_pow {R : Type*} [Ring R] [CharP R 3] (x : R) (k : ℕ) :
    (-x-1)^(3^k : ℕ) = -x^(3^k : ℕ)-1 := by
  have odd : Odd (3^k : ℕ) := (by decide : Odd (3:ℕ)).pow
  rw [sub_eq_add_neg, add_pow_char_pow_of_commute 3 k
    ((Commute.one_right (-x)).neg_right), odd.neg_pow, odd.neg_pow, one_pow, sub_eq_add_neg]

theorem B_relation_three (d : ℕ) :
    (B d : BMat (R := ZMod 3) d)^(d+2) = -B d-1 := by
  rw [B_relation]
  have ht : (3 : BMat (R := ZMod 3) d) = 0 := CharP.cast_eq_zero _ 3
  let A : BMat (R := ZMod 3) d := B d
  change 2*A-1 = -A-1
  calc
    2*A-1 = -A-1+3*A := by noncomm_ring
    _ = _ := by rw [ht, zero_mul, add_zero]

theorem B_three_period_square (d k : ℕ) (hd : d+2 = 3^k) :
    (B d : BMat (R := ZMod 3) d)^((3^k)^2-1) = 1 := by
  let A : BMat (R := ZMod 3) d := B d
  have hs : A^(3^k : ℕ) = -A-1 := hd ▸ B_relation_three d
  have hs2 : A^((3^k)^2 : ℕ) = A := by
    rw [pow_two (3^k : ℕ), pow_mul, hs, neg_add_one_pow, hs]
    abel
  have hE : (3^k : ℕ)^2-1+1=(3^k : ℕ)^2 := Nat.sub_add_cancel (Nat.succ_le_of_lt (by positivity))
  rw [← hE, pow_succ] at hs2
  have hcon := congrArg (fun M => M * (F d : BMat (R := ZMod 3) d)) hs2
  simp only [mul_assoc, show A * F d = 1 from B_mul_F d, mul_one] at hcon
  exact hcon

theorem B_three_period_cube (d k : ℕ) (hd : d+2 = 3^k+1) :
    (B d : BMat (R := ZMod 3) d)^((3^k)^2+3^k+1) = 1 := by
  let A : BMat (R := ZMod 3) d := B d
  have hs : A^(3^k+1 : ℕ) = -A-1 := hd ▸ B_relation_three d
  have h2 : A^((3^k)^2+3^k : ℕ) = -A^(3^k : ℕ)-1 := by
    rw [show (3^k : ℕ)^2+3^k=(3^k+1)*3^k by ring, pow_mul, hs, neg_add_one_pow]
  change A^(_ : ℕ) = _
  rw [pow_succ, h2, sub_mul, one_mul, neg_mul, ← pow_succ, hs]
  abel

theorem root_of_shift_power {K : Type*} [Field K] [Algebra (ZMod 3) K] [CharP K 3]
    (d r : ℕ) (hr : (B d : BMat (R := ZMod 3) d)^r=1)
    {x : K} (hx : x^(d+2)+x+1=0) : x^r=1 := by
  let f := inversePolynomial (ZMod 3) d
  have hd : f ∣ X^r-1 := by
    apply (inversePolynomial_dvd_iff d _).mpr
    simp [hr]
  by_cases h1 : x = 1
  · simp [h1]
  have hrel := congrArg (aeval x) (inversePolynomial_relation (R := ZMod 3) d)
  have hfx : aeval x f=0 := by
    have hthree : (3 : K)=0 := CharP.cast_eq_zero K 3
    simp only [map_mul, map_sub, map_one, map_add, map_pow, map_ofNat, aeval_X] at hrel
    have he : x^(d+2)-2*x+1=0 := by
      linear_combination hx - x * hthree
    rw [he] at hrel
    exact (mul_eq_zero.mp hrel).resolve_left (sub_ne_zero.mpr h1)
  have hout := aeval_eq_zero_of_dvd_aeval_eq_zero hd hfx
  simpa only [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] using hout

theorem galois_power (k t : ℕ) (hk : 0 < k) (ht : 0 < t)
    (x : GaloisField 3 (k*t)) : x^((3^k)^t : ℕ)=x := by
  let : Fintype (GaloisField 3 (k*t)) := Fintype.ofFinite _
  rw [← pow_mul, ← GaloisField.card 3 (k*t) (Nat.mul_pos hk ht).ne',
    Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem galois_generator (k t : ℕ) (hk : 0 < k) (ht : 0 < t) :
    ∃ a : GaloisField 3 (k*t), a ≠ 0 ∧ orderOf a = (3^k)^t-1 := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (GaloisField 3 (k*t))ˣ)
  refine ⟨(u : GaloisField 3 (k*t)), Units.ne_zero u, ?_⟩
  rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units,
    GaloisField.card 3 (k*t) (Nat.mul_pos hk ht).ne', pow_mul]

theorem frobenius_not_fixed {K : Type*} [Field K] (a : K) (ha : a ≠ 0)
    (q : ℕ) (hq : 1 < q) (ho : q-1 < orderOf a) : a^q ≠ a := by
  intro h
  have hf : a^(q-1)=1 := by
    apply mul_right_cancel₀ ha
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q), h, one_mul]
  exact (not_le_of_gt ho) (Nat.le_of_dvd (by omega) (orderOf_dvd_iff_pow_eq_one.mpr hf))

/-- A generator of the quadratic field is a quotient of two roots by an explicit linear equation. -/
theorem quadratic_root_pair (k : ℕ) (hk : 0 < k)
    (a : GaloisField 3 (k*2)) (ha : a^(3^k : ℕ) ≠ a) :
    ∃ y : GaloisField 3 (k*2), y^(3^k : ℕ)+y+1=0 ∧
      (a*y)^(3^k : ℕ)+a*y+1=0 := by
  let q : ℕ := 3^k
  let y := (a^q-1)/(a-a^q)
  have hA : (a^q)^q = a := by
    rw [← pow_mul, ← pow_two]
    exact galois_power k 2 hk (by decide) a
  have h1 : a-a^q ≠ 0 := sub_ne_zero.mpr ha.symm
  have h2 : a^q-a ≠ 0 := sub_ne_zero.mpr ha
  have hy : y^q = (a-1)/(a^q-a) := by
    dsimp only [y, q]
    rw [div_pow, sub_pow_char_pow (p := 3) _ _ k, sub_pow_char_pow (p := 3) _ _ k, one_pow, hA]
  refine ⟨y, ?_, ?_⟩
  · change y^q+y+1=0
    rw [hy]
    dsimp only [y]
    field_simp [h1, h2]
    ring
  · change (a*y)^q+a*y+1=0
    rw [mul_pow, hy]
    dsimp only [y]
    field_simp [h1, h2]
    ring

theorem root_of_trace_zero {K : Type*} [Field K] (q : ℕ) (hq : 0 < q)
    {u : K} (hu : u ≠ 0) (ht : u + u^q + u^(q^2)=0) :
    (u^(q-1))^(q+1)+u^(q-1)+1=0 := by
  apply (mul_eq_zero.mp ?_).resolve_right hu
  rw [add_mul, add_mul, one_mul, ← pow_mul, ← pow_succ, ← pow_succ]
  rw [Nat.sub_add_cancel hq, show (q-1)*(q+1)+1=q^2 by
    have h := Nat.sub_add_cancel hq
    nlinarith]
  linear_combination ht

/-- Taking a difference of Frobenius iterates gives a nonzero vector whose trace and whose scaled trace vanish. -/
theorem cubic_trace_pair (k : ℕ) (hk : 0 < k)
    (a : GaloisField 3 (k*3)) (ha : a^(3^k : ℕ) ≠ a) :
    ∃ u : GaloisField 3 (k*3), u ≠ 0 ∧
      u + u^(3^k : ℕ) + u^((3^k)^2 : ℕ) = 0 ∧
      a*u + (a*u)^(3^k : ℕ) + (a*u)^((3^k)^2 : ℕ) = 0 := by
  let q : ℕ := 3^k
  have hq : 0 < q := by dsimp [q]; positivity
  have h3 : a^(q^3) = a := galois_power k 3 hk (by decide) a
  have ha3 : (a^(q^2))^q = a := by rw [← pow_mul, ← pow_succ, h3]
  have ha4 : (a^q)^q = a^(q^2) := by rw [← pow_mul, pow_two]
  let u := a^q-a^(q^2)
  have hu : u ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hh := congrArg (fun x => x^q) h
    simp only [ha3, ha4] at hh
    exact ha (h.trans hh)
  have hu₁ : u^q = a^(q^2)-a := by
    change (a^q-a^(q^2))^(3^k : ℕ) = _
    rw [sub_pow_char_pow (p := 3) _ _ k, ha3, ha4]
  have hu₂ : u^(q^2) = a-a^q := by
    rw [pow_two q, pow_mul, hu₁]
    change (a^(q^2)-a)^(3^k : ℕ) = _
    rw [sub_pow_char_pow (p := 3) _ _ k, ha3]
  refine ⟨u, hu, ?_, ?_⟩
  · change u+u^q+u^(q^2)=0
    rw [hu₁, hu₂]
    dsimp only [u]
    ring
  · change a*u+(a*u)^q+(a*u)^(q^2)=0
    rw [mul_pow, mul_pow, hu₁, hu₂]
    dsimp only [u]
    ring

end DigitalPeriod
namespace DigitalPeriod

open Matrix
open FibPeriod

theorem prime_square_order (d k : ℕ) (hk : 0 < k) (hd : d+2=3^k) :
    orderOf (B d : BMat (R := ZMod 3) d)= (3^k)^2-1 := by
  let q : ℕ := 3^k
  let A : BMat (R := ZMod 3) d := B d
  let r := orderOf A
  have hq : 1 < q := Nat.one_lt_pow hk.ne' (by decide)
  have hupper : r ∣ q^2-1 := orderOf_dvd_iff_pow_eq_one.mpr (B_three_period_square d k hd)
  obtain ⟨a, ha, horder⟩ := galois_generator k 2 hk (by decide)
  have hnot : a^q ≠ a := by
    apply frobenius_not_fixed a ha q hq
    change orderOf a = q^2-1 at horder
    rw [horder]
    have hm := Nat.mul_le_mul_left q (show 2 ≤ q by omega)
    have hlt : q < q^2 := by nlinarith
    omega
  obtain ⟨y, hy, hay⟩ := quadratic_root_pair k hk a hnot
  have hY : y^r=1 := root_of_shift_power d r (pow_orderOf_eq_one A) (by rwa [hd])
  have hAY : (a*y)^r=1 := root_of_shift_power d r (pow_orderOf_eq_one A) (by rwa [hd])
  rw [mul_pow, hY, mul_one] at hAY
  have hlower := orderOf_dvd_iff_pow_eq_one.mpr hAY
  rw [horder] at hlower
  exact Nat.dvd_antisymm hupper hlower

theorem cube_sub_one_factor (q : ℕ) :
    q^3-1 = (q-1)*(q^2+q+1) := by
  rw [Nat.sub_mul, one_mul, show q*(q^2+q+1)=q^3+(q^2+q) by ring]
  omega

theorem prime_cube_order (d k : ℕ) (hk : 0 < k) (hd : d+2=3^k+1) :
    orderOf (B d : BMat (R := ZMod 3) d)= (3^k)^2+3^k+1 := by
  let q : ℕ := 3^k
  let A : BMat (R := ZMod 3) d := B d
  let r := orderOf A
  have hq : 1 < q := Nat.one_lt_pow hk.ne' (by decide)
  have hupper : r ∣ q^2+q+1 := orderOf_dvd_iff_pow_eq_one.mpr (B_three_period_cube d k hd)
  obtain ⟨a, ha, horder⟩ := galois_generator k 3 hk (by decide)
  change orderOf a = q^3-1 at horder
  have hnot : a^q ≠ a := by
    apply frobenius_not_fixed a ha q hq
    rw [horder, cube_sub_one_factor q]
    simpa only [mul_one] using
      Nat.mul_lt_mul_of_pos_left (show 1 < q^2+q+1 by omega) (show 0 < q-1 by omega)
  obtain ⟨u, hu, hut, haut⟩ := cubic_trace_pair k hk a hnot
  have hU : (u^(q-1))^r=1 := root_of_shift_power d r (pow_orderOf_eq_one A) (by
    rw [hd]
    exact root_of_trace_zero q (by omega) hu hut)
  have hAU : ((a*u)^(q-1))^r=1 := root_of_shift_power d r (pow_orderOf_eq_one A) (by
    rw [hd]
    exact root_of_trace_zero q (by omega) (mul_ne_zero ha hu) haut)
  rw [mul_pow, mul_pow, hU, mul_one] at hAU
  have hlower := orderOf_dvd_iff_pow_eq_one.mpr hAU
  have horder' : orderOf (a^(q-1))=q^2+q+1 := by
    rw [orderOf_pow_of_dvd (by omega), horder, cube_sub_one_factor q,
      Nat.mul_comm (q-1), Nat.mul_div_cancel _ (by omega)]
    rw [horder, cube_sub_one_factor q]
    exact dvd_mul_right _ _
  rw [horder'] at hlower
  exact Nat.dvd_antisymm hupper hlower

theorem B_nine_order_triple (d r : ℕ) (hd : 0 < d) (hr : 0 < r)
    (hord : orderOf (B d : BMat (R := ZMod 3) d)=r) (h3 : ¬3∣r) :
    orderOf (B d : BMat (R := ZMod 9) d)=3*r := by
  let N : BMat (R := ZMod 3) d := B d
  let M : BMat (R := ZMod 9) d := B d
  have hred : matrixThree M = N := by
    change matrixThree (B d) = B d
    rw [← red_B d 9, modThree_red, red_B]
  have hN : N^r=1 := by rw [← hord]; exact pow_orderOf_eq_one N
  have hredzero : matrixThree (M^r-1)=0 := by
    rw [map_sub, map_pow, map_one, hred, hN, sub_self]
  obtain ⟨E, hE⟩ := matrixThree_kernel _ hredzero
  have hMe : M^r = 1+3*E := by rw [← hE]; abel
  have h9 : (9 : BMat (R := ZMod 9) d)=0 := CharP.cast_eq_zero _ 9
  have hMp : M^(r*3)=1 := by
    rw [pow_mul, hMe]
    calc
      _ = 1+9*(E+3*E^2+3*E^3) := by noncomm_ring
      _ = 1 := by rw [h9, zero_mul, add_zero]
  let s := orderOf M
  have hl : r∣s := by
    rw [← hord]
    apply orderOf_dvd_iff_pow_eq_one.mpr
    have hx := congrArg (matrixThree (d := d)) (pow_orderOf_eq_one M)
    simpa only [map_pow, map_one, hred] using hx
  have hu : s∣r*3 := orderOf_dvd_iff_pow_eq_one.mpr hMp
  have hs : 3∣s := three_dvd_order_nine d hd
  obtain ⟨w, hw⟩ := hl
  rw [hw] at hu
  have hw' := Nat.dvd_of_mul_dvd_mul_left hr hu
  rcases (by decide : Nat.Prime 3).eq_one_or_self_of_dvd w hw' with h | h
  · rw [hw, h, mul_one] at hs
    exact False.elim (h3 hs)
  · change s = 3*r
    rw [hw, h, Nat.mul_comm]

theorem q_dvd_three (k : ℕ) (hk : 0 < k) : 3 ∣ 3^k :=
  dvd_pow_self 3 hk.ne'

theorem square_order_not_three (k : ℕ) (hk : 0 < k) : ¬ 3 ∣ (3^k)^2-1 := by
  intro h
  have ht : 3 ∣ (3^k)^2 := dvd_pow (q_dvd_three k hk) (by decide)
  have hs := Nat.dvd_sub ht h
  have hq : 0 < (3^k : ℕ)^2 := by positivity
  have h1 : (3^k : ℕ)^2 - ((3^k)^2-1)=1 := by omega
  rw [h1] at hs
  exact (by decide : ¬3∣(1:ℕ)) hs

theorem cube_order_not_three (k : ℕ) (hk : 0 < k) : ¬ 3 ∣ (3^k)^2+3^k+1 := by
  intro h
  have hh := Nat.dvd_add (dvd_pow (q_dvd_three k hk) (by decide : 2 ≠ 0)) (q_dvd_three k hk)
  have ht := Nat.dvd_sub h hh
  rw [Nat.add_sub_cancel_left] at ht
  exact (by decide : ¬3∣ (1:ℕ)) ht

end DigitalPeriod

theorem OMA.solution : type_of% @OMA.S_oeis_a210456.main := by
  open DigitalPeriod in
  constructor
  · intro n hn
    cases n with
    | zero =>
      rw [period_zero] at hn
      omega
    | succ d =>
      rw [period_eq_order]
      have hd : 0 < d := by
        by_contra! h
        have e : d=0 := by omega
        subst d
        rw [period_eq_order, FibPeriod.B_zero_one, orderOf_one] at hn
        omega
      exact three_dvd_order_nine d hd
  · intro k hk
    have hk' : 0 < k := by omega
    have hq : 3 ≤ (3^k : ℕ) := by
      simpa using (Nat.pow_le_pow_right (by decide : 0 < (3:ℕ)) hk)
    let q : ℕ := 3^k
    change 3 ≤ q at hq
    have h2 : q^2 = 3^(2*k) := by
      dsimp only [q]
      rw [← pow_mul, Nat.mul_comm]
    have h3 : 3*q^2 = 3^(2*k+1) := by rw [h2, pow_succ']
    have h4 : 3*q = 3^(k+1) := (pow_succ' (3:ℕ) k).symm
    constructor
    · let d := q-2
      rw [show 3^k-1=d+1 by dsimp [d, q] at *; omega, period_eq_order]
      have h := B_nine_order_triple d (by dsimp [d]; omega)
        (r := q^2-1) (by have := Nat.pow_le_pow_left hq 2; omega)
        (prime_square_order d k hk' (by dsimp [d, q] at *; omega))
        (square_order_not_three k hk')
      rw [h, Nat.mul_sub_left_distrib, h3, mul_one]
    · let d := q-1
      rw [show 3^k=d+1 by dsimp [d, q] at *; omega, period_eq_order]
      have h := B_nine_order_triple d (by dsimp [d]; omega)
        (r := q^2+q+1) (by positivity)
        (prime_cube_order d k hk' (by dsimp [d, q] at *; omega))
        (cube_order_not_three k hk')
      rw [h, Nat.mul_add, Nat.mul_add, h3, h4, mul_one]
