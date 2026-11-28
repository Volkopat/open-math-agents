import OMAStatements.S_oeis_a351889

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

theorem eventual_iff_return (d k r : ℕ) :
    OMA.S_oeis_a351889.IsEventualPeriod (d + 1) k r ↔
    (forward (d + 1))^[r] (OMA.S_oeis_a351889.vinit (d + 1) k) =
      OMA.S_oeis_a351889.vinit (d + 1) k := by
  let v := OMA.S_oeis_a351889.vinit (d + 1) k
  have hseq (m : ℕ) : OMA.S_oeis_a351889.seqN (d + 1) k m =
      ((forward (d + 1))^[m] v) 0 := by
    simp only [OMA.S_oeis_a351889.seqN, dif_pos (Nat.succ_pos d)]
    rfl
  constructor
  · rintro ⟨m, hm⟩
    apply (backward_forward (R := ZMod k) d).injective.iterate m
    rw [← iterate_add_apply]
    funext i
    obtain ⟨i, hi⟩ := i
    change ((forward (d + 1))^[m + r] v) ⟨i, hi⟩ =
      ((forward (d + 1))^[m] v) ⟨i, hi⟩
    have hh := hm (m + i) (by omega)
    rw [hseq, hseq] at hh
    rw [advance (d + 1) v (m + r) i hi, advance (d + 1) v m i hi,
      show m + r + i = m + i + r by omega]
    exact hh
  · intro h
    refine ⟨0, fun m _ => ?_⟩
    rw [hseq, hseq, iterate_add_apply, h]


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

theorem seed_eq (d k : ℕ) :
    OMA.S_oeis_a351889.vinit (d + 1) k = Pi.single (Fin.last d) 1 := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [OMA.S_oeis_a351889.vinit]
  · intro j
    simp [OMA.S_oeis_a351889.vinit, show j.val + 1 < d + 1 by omega]

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

theorem eventual_iff_power (d k r : ℕ) :
    OMA.S_oeis_a351889.IsEventualPeriod (d + 1) k r ↔
    (B d : Matrix _ _ (ZMod k)) ^ r = 1 := by
  rw [eventual_iff_return, seed_eq, ← backward_pow_return]
  rw [show (backward d : (Fin (d + 1) → ZMod k) → _) = fun v => B d *ᵥ v from
    funext (B_vec d) |>.symm, ← pow_vec]
  exact ⟨power_fix_basis d r, fun h => by rw [h, Matrix.one_mulVec]⟩

theorem period_eq_order (d k : ℕ) :
    OMA.S_oeis_a351889.a351889 (d + 1) k =
      orderOf (B d : Matrix _ _ (ZMod k)) := by
  rw [OMA.S_oeis_a351889.a351889, orderOf, minimalPeriod_eq_sInf_n_pos_IsPeriodicPt]
  apply congrArg sInf
  ext r
  exact and_congr_right' ((eventual_iff_power d k r).trans
    (isPeriodicPt_mul_iff_pow_eq_one _).symm)

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

theorem B_two_order (d : ℕ) (hd : 0 < d) :
    orderOf (B d : Matrix _ _ (ZMod 2)) = d+2 := by
  let M : Matrix (Fin (d+1)) _ (ZMod 2) := B d
  have h : M ^ (d+2) = 1 := by
    change (B d : Matrix _ _ (ZMod 2)) ^ (d+2) = 1
    rw [B_relation]
    have hh : (2 : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod 2)) = 0 :=
      CharP.cast_eq_zero _ 2
    rw [hh, zero_mul, zero_sub, neg_eq_iff_add_eq_zero, one_add_one_eq_two, hh]
  have ho : 0 < orderOf M :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨d+2, by omega, h⟩).orderOf_pos
  obtain ⟨q, hq⟩ := orderOf_dvd_iff_pow_eq_one.mpr h
  change orderOf M = d+2
  by_contra hne
  have hq' : 2 ≤ q := by
    by_contra! hq'
    interval_cases q <;> simp_all
  have hsmall : orderOf M ≤ d := by
    have hle := Nat.mul_le_mul_left (orderOf M) hq'
    omega
  have hb := congrArg (fun (A : Matrix (Fin (d+1)) _ (ZMod 2)) =>
    (A *ᵥ Pi.single (Fin.last d) 1) (Fin.last d)) (pow_orderOf_eq_one M)
  simp only [Matrix.one_mulVec, Pi.single_eq_same] at hb
  change ((B d : Matrix _ _ (ZMod 2)) ^ orderOf M *ᵥ _) _ = _ at hb
  rw [pow_vec] at hb
  simp_rw [B_vec] at hb
  rw [backward_support d (orderOf M) ho (Fin.last d) (by simpa using hsmall)] at hb
  exact zero_ne_one hb

theorem B_two_ne_one (d : ℕ) (hd : 0 < d) :
    (B d : Matrix _ _ (ZMod 2)) ≠ 1 := by
  intro h
  have hh := B_two_order d hd
  rw [h, orderOf_one] at hh
  omega

end FibPeriod

namespace FibPeriod

open Finset

theorem sharp_remainder {R : Type*} [Ring R] (p a : ℕ) (hp : p.Prime) (ha : 0 < a)
    (hpa : 3 ≤ p ∨ 2 ≤ a) (B : R) :
    ((p : R) ^ (a + 2)) ∣
      (1 + (p : R) ^ a * B) ^ p - (1 + (p : R) ^ (a + 1) * B) := by
  let D := (p : R) ^ a * B
  let f : ℕ → R := fun i => D ^ i * (p.choose i : R)
  have hexp : (1 + D) ^ p = ∑ i ∈ range p.pred, f (i+2) + (f 1 + f 0) := by
    rw [add_comm (1 : R) D, (Commute.one_right D).add_pow]
    simp only [one_pow, mul_one]
    change (∑ i ∈ range (p+1), f i) = _
    rw [sum_range_succ']
    have tail : (∑ i ∈ range p, f (i+1)) =
        (∑ i ∈ range p.pred, f (i+2)) + f 1 := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hp.pos, sum_range_succ']
    rw [tail]
    rw [add_assoc]
  have hf0 : f 0 = 1 := by simp [f]
  have hf1 : f 1 = (p : R) ^ (a + 1) * B := by
    change D ^ 1 * (p.choose 1 : R) = _
    rw [pow_one, Nat.choose_one_right]
    change ((p : R) ^ a * B) * (p : R) = _
    rw [mul_assoc, ← (Nat.cast_commute p B).eq, ← mul_assoc, ← pow_succ]
  change _ ∣ (1 + D) ^ p - _
  rw [hexp, hf0, hf1, add_comm ((p : R) ^ (a+1) * B) 1, add_sub_cancel_right]
  refine dvd_sum fun i hi => ?_
  have hi' : i + 2 ≤ p := by
    have hpred := Nat.succ_pred_eq_of_pos hp.pos
    have := mem_range.mp hi
    omega
  have hpow (k : ℕ) : D ^ k = (p : R) ^ (a * k) * B ^ k := by
    change (((p : R)^a) * B)^k = _
    rw [((Nat.cast_commute p B).pow_left a).mul_pow, ← pow_mul]
  by_cases he : i + 2 = p
  · have hbound : a + 2 ≤ a * p := by
      rcases hpa with h | h
      · exact (show a+2 ≤ a*3 by omega).trans (Nat.mul_le_mul_left a h)
      · exact (show a+2 ≤ a*2 by omega).trans (Nat.mul_le_mul_left a hp.two_le)
    rw [he, show f p = D ^ p by simp [f], hpow]
    exact (pow_dvd_pow _ hbound).trans (dvd_mul_right _ _)
  · have hbound : a + 2 ≤ a * (i + 2) + 1 := by
      have h := Nat.mul_le_mul_left a (show 2 ≤ i+2 by omega)
      omega
    obtain ⟨q, hq⟩ := hp.dvd_choose_self (show i+2 ≠ 0 by omega) (show i+2 < p by omega)
    change _ ∣ D ^ (i + 2) * (p.choose (i + 2) : R)
    rw [hpow, hq, Nat.cast_mul, ← mul_assoc, mul_assoc ((p:R) ^ (a * (i+2))),
      ← (Nat.cast_commute p (B ^ (i+2))).eq, ← mul_assoc, ← pow_succ, mul_assoc]
    exact (pow_dvd_pow _ hbound).trans (dvd_mul_right _ _)

end FibPeriod
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

theorem scalar_cancel {d k : ℕ} (hk : 0 < k) {A C : IMat d}
    (h : (k : IMat d) * A = (k : IMat d) * C) : A = C := by
  ext i j
  have ht := congrArg (fun (X : IMat d) => X i j) h
  simp only [scalar_apply_entry] at ht
  exact mul_left_cancel₀ (by exact_mod_cast hk.ne') ht

theorem red_pow_eq_one {d : ℕ} (M : IMat d) (p a r : ℕ) :
    (red (p^a) M)^r = 1 ↔ ((p : IMat d)^a) ∣ M^r - 1 := by
  rw [← Nat.cast_pow, ← red_eq_zero, map_sub, map_one, map_pow, sub_eq_zero]

def ExactAt {d : ℕ} (A : IMat d) (p a : ℕ) : Prop :=
  (p : IMat d)^a ∣ A - 1 ∧ ¬ (p : IMat d)^(a+1) ∣ A - 1

theorem exact_of_coeff {d p a : ℕ} (hp : 0 < p) {A C : IMat d}
    (h : A = 1 + (p : IMat d)^a * C) (hc : ¬(p : IMat d) ∣ C) : ExactAt A p a := by
  have ha : A - 1 = (p : IMat d)^a * C := by rw [h]; abel
  rw [ExactAt, ha]
  refine ⟨dvd_mul_right _ _, ?_⟩
  rintro ⟨D, hD⟩
  rw [pow_succ, mul_assoc] at hD
  have hh : C = (p : IMat d) * D := by
    rw [← Nat.cast_pow] at hD
    exact scalar_cancel (pow_pos hp _) hD
  exact hc ⟨D, hh⟩

theorem exact_pow {d p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hpa : 3 ≤ p ∨ 2 ≤ a) {A : IMat d} (hA : ExactAt A p a) :
    ExactAt (A^p) p (a+1) := by
  obtain ⟨C, hC⟩ := hA.1
  have hv : A = 1 + (p : IMat d)^a * C := by rw [← hC]; abel
  have hc : ¬(p : IMat d) ∣ C := by
    rintro ⟨D, hD⟩
    apply hA.2
    refine ⟨D, ?_⟩
    rw [hC, hD, pow_succ, mul_assoc]
  obtain ⟨D, hD⟩ := sharp_remainder p a hp ha hpa C
  have hm : A^p = 1 + (p : IMat d)^(a+1) * (C + (p : IMat d) * D) := by
    rw [← hv, sub_eq_iff_eq_add] at hD
    rw [hD, mul_add, ← mul_assoc ((p : IMat d)^(a+1)), ← pow_succ]
    abel
  apply exact_of_coeff hp.pos hm
  intro hc'
  apply hc
  simpa using hc'.sub (dvd_mul_right (p : IMat d) D)

noncomputable def mord {d : ℕ} (M : IMat d) (p a : ℕ) : ℕ := orderOf (red (p^a) M)

theorem order_div {d p a : ℕ} (M : IMat d) : mord M p a ∣ mord M p (a+1) := by
  apply orderOf_dvd_iff_pow_eq_one.mpr
  rw [red_pow_eq_one]
  have h := (red_pow_eq_one M p (a+1) (mord M p (a+1))).mp (pow_orderOf_eq_one _)
  exact (pow_dvd_pow _ (by omega)).trans h

theorem order_increase {d p a r : ℕ} (M : IMat d) (hp : p.Prime) (hr : 0 < r)
    (he : mord M p a = r) (hex : ExactAt (M^r) p a) (hn : ExactAt ((M^r)^p) p (a+1)) :
    mord M p (a+1) = r * p := by
  have hd := order_div (p := p) (a := a) M
  rw [he] at hd
  have hu : mord M p (a+1) ∣ r * p := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    rw [red_pow_eq_one, pow_mul]
    exact hn.1
  obtain ⟨q, hq⟩ := hd
  rw [hq] at hu
  have hq' : q ∣ p := Nat.dvd_of_mul_dvd_mul_left hr hu
  rcases hp.eq_one_or_self_of_dvd q hq' with h | h
  · exfalso
    apply hex.2
    have hh : (red (p^(a+1)) M)^r = 1 := by
      have hpw := pow_orderOf_eq_one (red (p^(a+1)) M)
      have eq : mord M p (a+1) = r := by simpa [h] using hq
      rwa [show orderOf (red (p^(a+1)) M) = r from eq] at hpw
    exact (red_pow_eq_one M p (a+1) r).mp hh
  · simpa [h] using hq

theorem order_lift {d p a r : ℕ} (M : IMat d) (hp : p.Prime) (ha : 0 < a)
    (hpa : 3 ≤ p ∨ 2 ≤ a) (hr : 0 < r) (he : mord M p a = r)
    (hex : ExactAt (M^r) p a) (k : ℕ) :
    mord M p (a+k) = r * p^k ∧ ExactAt (M^(r*p^k)) p (a+k) := by
  induction k with
  | zero => simpa using And.intro he hex
  | succ k ih =>
      have hx := exact_pow hp (a := a+k) (by omega)
        (hpa.imp_right (fun h => by omega)) ih.2
      have he' := order_increase M hp (mul_pos hr (pow_pos hp.pos _)) ih.1 ih.2 hx
      rw [pow_succ, ← mul_assoc, show a+(k+1) = a+k+1 by omega]
      exact ⟨he', by rwa [pow_mul]⟩

theorem B_order_pos (d k : ℕ) (hk : 0 < k) :
    0 < orderOf (B d : Matrix _ _ (ZMod k)) := by
  let : NeZero k := ⟨hk.ne'⟩
  have hu : IsUnit (B d : Matrix _ _ (ZMod k)) :=
    ⟨⟨B d, F d, B_mul_F d, F_mul_B d⟩, rfl⟩
  exact hu.isOfFinOrder.orderOf_pos

theorem B_order_formula (d m : ℕ) (hd : 0 < d) (hm : 1 ≤ m) :
    orderOf (B d : Matrix _ _ (ZMod (2^m))) = (d+2) * 2^(m-1) := by
  let M : IMat d := B d
  let r := d+2
  have hp : Nat.Prime 2 := by decide
  have hb : mord M 2 1 = r := by
    unfold mord M r
    rw [pow_one, red_B, B_two_order d hd]
  have hnot : ¬(2 : IMat d) ∣ M - 1 := by
    change ¬ ((2 : ℕ) : IMat d) ∣ M-1
    rw [← red_eq_zero 2 (M-1), map_sub, map_one, sub_eq_zero]
    dsimp only [M]
    rw [red_B]
    exact B_two_ne_one d hd
  have hrel : M^r = 1 + 2 * (M-1) := by
    rw [show M^r = 2*M-1 from B_relation d]
    noncomm_ring
  have h1 : ExactAt (M^r) 2 1 := exact_of_coeff (by decide) (by simpa using hrel) hnot
  have hsq : (M^r)^2 = 1 + (2 : IMat d)^2 * (M*(M-1)) := by
    rw [hrel]
    noncomm_ring
  have hnot' : ¬(2 : IMat d) ∣ M*(M-1) := by
    change ¬ ((2 : ℕ) : IMat d) ∣ M*(M-1)
    rw [← red_eq_zero 2 (M*(M-1)), map_mul, map_sub, map_one]
    dsimp only [M]
    rw [red_B]
    intro h
    have ht := congrArg (fun A => (F d : Matrix _ _ (ZMod 2)) * A) h
    rw [mul_zero, ← mul_assoc, F_mul_B, one_mul, sub_eq_zero] at ht
    exact B_two_ne_one d hd ht
  have h2 : ExactAt ((M^r)^2) 2 2 := exact_of_coeff (by decide) (by simpa using hsq) hnot'
  have ht : mord M 2 2 = r*2 := order_increase M hp (by omega) hb h1 h2
  by_cases he : m = 1
  · subst m
    simpa [mord, M, r] using hb
  · have h2m : 2 ≤ m := by omega
    have hu := (order_lift M hp (a := 2) (by decide) (Or.inr (by decide))
      (show 0 < r*2 by omega) ht (by rwa [pow_mul]) (m-2)).1
    rw [show 2+(m-2) = m by omega] at hu
    have eq : r*2*2^(m-2) = r*2^(m-1) := by
      rw [mul_assoc, ← pow_succ', show m-2+1=m-1 by omega]
    simpa only [eq, mord, M, red_B, r] using hu

theorem B_zero_one (k : ℕ) : (B 0 : Matrix _ _ (ZMod k)) = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [B]

theorem conditional_formula (d p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (h : orderOf (B d : Matrix _ _ (ZMod p)) ≠ orderOf (B d : Matrix _ _ (ZMod (p^2)))) :
    orderOf (B d : Matrix _ _ (ZMod (p^k))) =
      p^(k-1) * orderOf (B d : Matrix _ _ (ZMod p)) := by
  by_cases ht : p = 2
  · subst p
    have hd : 0 < d := by
      by_contra! hn
      have hd : d = 0 := by omega
      subst d
      simp only [B_zero_one, orderOf_one, ne_self_iff_false] at h
    rw [B_order_formula d k hd hk]
    simp [B_two_order d hd, Nat.mul_comm]
  · let M : IMat d := B d
    let r := orderOf (B d : Matrix _ _ (ZMod p))
    have he : mord M p 1 = r := by
      unfold mord M r
      rw [pow_one, red_B]
    have hn : mord M p 2 ≠ r := by simpa [mord, M, r, ne_comm] using h
    have hex : ExactAt (M^r) p 1 := by
      constructor
      · apply (red_pow_eq_one M p 1 r).mp
        rw [← he]
        exact pow_orderOf_eq_one _
      · intro hdvd
        have hdiv : mord M p 2 ∣ r := by
          apply orderOf_dvd_iff_pow_eq_one.mpr
          exact (red_pow_eq_one M p 2 r).mpr hdvd
        have hdiv' := order_div (p := p) (a := 1) M
        rw [he] at hdiv'
        exact hn (Nat.dvd_antisymm hdiv hdiv')
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    have hl := (order_lift M hp (a := 1) (by decide) (Or.inl h3)
      (B_order_pos d p hp.pos) he hex (k-1)).1
    rw [show 1+(k-1) = k by omega] at hl
    simpa only [mord, M, red_B, Nat.mul_comm, r] using hl

end FibPeriod

theorem OMA.solution : type_of% @OMA.S_oeis_a351889.main := by
  constructor
  · intro n m hn hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    rw [FibPeriod.period_eq_order]
    exact FibPeriod.B_order_formula d m (by omega) hm
  · intro n p k hn hp hk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    simp only [FibPeriod.period_eq_order]
    exact FibPeriod.conditional_formula d p k hp hk

