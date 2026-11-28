import OMAReductions.R_Erdos975_erdos_975_R1
import Mathlib

/-! A linear mean bound for the number of polynomial roots modulo q.
For each root choose a short annihilating polynomial; the determinant of its
companion iterates controls both how many moduli and how many residues fit it. -/

namespace OMA.Companion975

open Polynomial Finset

def vEval {R : Type*} [CommRing R] {d : ℕ} (r : R) (b : Fin d → ℤ) : R :=
  ∑ i, (b i : R) * r ^ i.val

/-- Columns of multiplication by the integral element aX on the original power coordinates. -/
def column (f : ℤ[X]) (i j : Fin f.natDegree) : ℤ :=
  if i.val + 1 < f.natDegree then (if j.val = i.val + 1 then f.leadingCoeff else 0)
  else - f.coeff j.val

def T (f : ℤ[X]) (b : Fin f.natDegree → ℤ) (j : Fin f.natDegree) : ℤ :=
  ∑ i, b i * column f i j

def matrix (f : ℤ[X]) (b : Fin f.natDegree → ℤ) :
    Matrix (Fin f.natDegree) (Fin f.natDegree) ℤ :=
  fun i j => (T f)^[j.val] b i

private lemma eval_column {R : Type*} [CommRing R] (f : ℤ[X]) (r : R)
    (hr : f.eval₂ (Int.castRingHom R) r = 0) (i : Fin f.natDegree) :
    vEval r (column f i) = (f.leadingCoeff : R) * r ^ (i.val + 1) := by
  classical
  by_cases hi : i.val + 1 < f.natDegree
  · let t : Fin f.natDegree := ⟨i.val + 1, hi⟩
    have ee (j : Fin f.natDegree) : (j.val = i.val + 1) ↔ j = t :=
      ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp [vEval, column, hi, ee, t, ite_mul]
  · have he : i.val + 1 = f.natDegree := by omega
    rw [eval₂_eq_sum_range, sum_range_succ, ← Fin.sum_univ_eq_sum_range] at hr
    simp only [Int.coe_castRingHom, coeff_natDegree] at hr
    simp only [vEval, column, if_neg hi, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
    rw [he]
    linear_combination -hr

lemma eval_T {R : Type*} [CommRing R] (f : ℤ[X]) (r : R)
    (hr : f.eval₂ (Int.castRingHom R) r = 0) (b : Fin f.natDegree → ℤ) :
    vEval r (T f b) = ((f.leadingCoeff : R) * r) * vEval r b := by
  classical
  simp only [vEval, T, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  change (b i : R) * vEval r (column f i) = _
  rw [eval_column f r hr, pow_succ]
  ring

lemma eval_iterate {R : Type*} [CommRing R] (f : ℤ[X]) (r : R)
    (hr : f.eval₂ (Int.castRingHom R) r = 0) (b : Fin f.natDegree → ℤ) (j : ℕ) :
    vEval r ((T f)^[j] b) = ((f.leadingCoeff : R) * r) ^ j * vEval r b := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', eval_T f r hr, ih, pow_succ']; ring

private lemma eval_coeffs_zero {R : Type*} [Field R] [Algebra ℚ R] {d : ℕ} (r : R)
    (basis : LinearIndependent ℚ (fun i : Fin d => r ^ i.val)) (b : Fin d → ℤ)
    (zero : vEval r b = 0) : b = 0 := by
  apply _root_.funext
  intro i
  have hz := (Fintype.linearIndependent_iff.mp basis) (fun j => (b j : ℚ))
  have zero' : ∑ j : Fin d, (b j : ℚ) • r ^ j.val = 0 := by
    simpa [Algebra.smul_def, vEval] using zero
  exact_mod_cast hz zero' i

private lemma eval_lincomb {R : Type*} [CommRing R] {d : ℕ} (r : R)
    (M : Matrix (Fin d) (Fin d) ℤ) (g : Fin d → ℤ) :
    vEval r (∑ i, g i • M.col i) = ∑ i, (g i : R) * vEval r (M.col i) := by
  classical
  simp only [vEval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum,
    Int.cast_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

lemma det_ne_zero (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0)
    (b : Fin f.natDegree → ℤ) (hb : b ≠ 0) : (matrix f b).det ≠ 0 := by
  classical
  let F := f.map (Int.castRingHom ℚ)
  have irr : Irreducible F :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hf.isPrimitive hd)).mp hf
  let : Fact (Irreducible F) := ⟨irr⟩
  let r := AdjoinRoot.root F
  have hr : f.eval₂ (Int.castRingHom (AdjoinRoot F)) r = 0 := by
    have heq : (AdjoinRoot.of F).comp (Int.castRingHom ℚ) =
        Int.castRingHom (AdjoinRoot F) := Subsingleton.elim _ _
    simpa only [F, Polynomial.eval₂_map, heq] using AdjoinRoot.eval₂_root F
  have e : F.natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (Int.cast_injective) _
  have hlin : LinearIndependent ℚ (fun i : Fin F.natDegree => r ^ i.val) := by
    let pb := AdjoinRoot.powerBasis irr.ne_zero
    have heq : (fun i : Fin F.natDegree => r ^ i.val) = pb.basis :=
      _root_.funext fun i => (pb.basis_eq_pow i).symm
    rw [heq]
    exact pb.basis.linearIndependent
  have basis : LinearIndependent ℚ (fun i : Fin f.natDegree => r ^ i.val) := by
    exact hlin.comp (Fin.cast e.symm) (Fin.cast_injective _)
  have vne : vEval r b ≠ 0 := fun z => hb (eval_coeffs_zero r basis b z)
  rw [← Matrix.nonsingular_iff_det_ne_zero, ← Matrix.linearIndependent_col_iff,
    Fintype.linearIndependent_iff]
  intro g hg i
  have hzero := congrArg (vEval r) hg
  rw [eval_lincomb] at hzero
  have hcol (j : Fin f.natDegree) :
      vEval r ((matrix f b).col j) = ((f.leadingCoeff : AdjoinRoot F) * r) ^ j.val * vEval r b :=
    eval_iterate f r hr b j.val
  simp only [hcol, ← mul_assoc, ← Finset.sum_mul] at hzero
  have heval0 : vEval r (0 : Fin f.natDegree → ℤ) = 0 := by simp [vEval]
  rw [heval0] at hzero
  have hz := (mul_eq_zero.mp hzero).resolve_right vne
  let coeff (j : Fin f.natDegree) := g j * f.leadingCoeff ^ j.val
  have rel : vEval r coeff = 0 := by
    simpa [vEval, coeff, mul_pow, mul_assoc] using hz
  have hc := congrFun (eval_coeffs_zero r basis coeff rel) i
  exact (mul_eq_zero.mp hc).resolve_right (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hf.ne_zero))

/-- One common bound on the column sums of multiplication by aX. -/
private def stepSize (f : ℤ[X]) : ℕ :=
  1 + ∑ j, ∑ i, (column f i j).natAbs

private lemma step_bound (f : ℤ[X]) (t : ℕ) (b : Fin f.natDegree → ℤ)
    (hb : ∀ i, (b i).natAbs ≤ t) (j : Fin f.natDegree) : (T f b j).natAbs ≤ stepSize f * t := by
  have hcol := Finset.single_le_sum (f := fun j : Fin f.natDegree => ∑ i, (column f i j).natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  calc
    (T f b j).natAbs ≤ ∑ i, (b i * column f i j).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ i, (column f i j).natAbs * t := Finset.sum_le_sum fun i _ => by
      rw [Int.natAbs_mul, mul_comm]; exact Nat.mul_le_mul_left _ (hb i)
    _ ≤ stepSize f * t := by
      rw [← Finset.sum_mul]
      exact Nat.mul_le_mul_right _ (le_trans hcol (by unfold stepSize; omega))

private lemma iterate_bound (f : ℤ[X]) (t : ℕ) (b : Fin f.natDegree → ℤ)
    (hb : ∀ i, (b i).natAbs ≤ t) (j : ℕ) (i : Fin f.natDegree) :
    ((T f)^[j] b i).natAbs ≤ stepSize f ^ j * t := by
  induction j generalizing i with
  | zero => simpa using hb i
  | succ j ih =>
    rw [Function.iterate_succ_apply', pow_succ', mul_assoc]
    exact step_bound f _ _ ih i

lemma determinant_bound (f : ℤ[X]) :
    ∃ K : ℕ, ∀ (t : ℕ) (b : Fin f.natDegree → ℤ), (∀ i, (b i).natAbs ≤ t) →
      (matrix f b).det.natAbs ≤ K * t ^ f.natDegree := by
  classical
  let d := f.natDegree
  let A := stepSize f ^ d
  refine ⟨Fintype.card (Equiv.Perm (Fin d)) * A ^ d, ?_⟩
  intro t b hb
  have entry (i j : Fin d) : ((matrix f b) i j).natAbs ≤ A * t := by
    apply (iterate_bound f t b hb j.val i).trans
    have hpos : 0 < stepSize f := by unfold stepSize; omega
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hpos j.isLt.le)
  rw [Matrix.det_apply]
  apply (Int.natAbs_sum_le _ _).trans
  calc
    _ ≤ ∑ _σ : Equiv.Perm (Fin d), (A * t) ^ d := Finset.sum_le_sum fun σ _ => by
      rw [Units.smul_def, smul_eq_mul, Int.natAbs_mul, Int.units_natAbs, one_mul]
      change Int.natAbsHom (∏ i, (matrix f b) (σ i) i) ≤ _
      rw [map_prod]
      exact (Finset.prod_le_prod' (fun i _ => entry (σ i) i)).trans_eq (by simp)
    _ = _ := by simp [d, mul_pow, mul_assoc]

lemma columns_divisible (f : ℤ[X]) (q r : ℕ) (b : Fin f.natDegree → ℤ)
    (hroot : (q : ℤ) ∣ f.eval (r : ℤ))
    (hzero : ∑ i, (b i : ZMod q) * (r : ZMod q) ^ i.val = 0) (j : Fin f.natDegree) :
    (q : ℤ) ∣ ∑ i, (r : ℤ) ^ i.val * matrix f b i j := by
  have hr : f.eval₂ (Int.castRingHom (ZMod q)) (r : ZMod q) = 0 := by
    have h := Polynomial.eval₂_at_apply (p := f) (Int.castRingHom (ZMod q)) (r : ℤ)
    simpa only [Int.coe_castRingHom, Int.cast_natCast] using
      h.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hroot)
  have ev := eval_iterate f (r : ZMod q) hr b j.val
  change vEval (r : ZMod q) b = 0 at hzero
  rw [hzero, mul_zero] at ev
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  simpa [vEval, matrix, mul_comm] using ev

end OMA.Companion975

/- Determinant indices for the moment rows (1, r, ..., r^(d-1)). -/

namespace OMA.Index975

open Finset Matrix
open scoped BigOperators

private theorem row_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) {i j : ι} (hij : i ≠ j)
    (u v : ι → ℤ) (hu : u i = 1) (hv : v i = 1) (q : ℤ)
    (du : ∀ k, q ∣ ∑ h, u h * A h k) (dv : ∀ k, q ∣ ∑ h, v h * A h k) :
    q ∣ A.det ∧ q^2 ∣ (v j-u j)*A.det := by
  classical
  have diff (k : ι) : q ∣ ∑ h, (v h - u h) * A h k := by
    simpa only [sub_mul, Finset.sum_sub_distrib] using dvd_sub (dv k) (du k)
  choose U hU using du
  choose V hV using diff
  let B := A.updateRow i (q • U)
  have rowU : ∑ h, u h • A h = q • U := by
    ext k
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hU k
  have detB : B.det = A.det := by
    dsimp [B]
    rw [← rowU, Matrix.det_updateRow_sum, hu, one_smul]
  have d1 : q ∣ A.det := by
    rw [← detB]
    exact ⟨_, Matrix.det_updateRow_smul A i q U⟩
  have rowV : ∑ h, (v h-u h) • B h = q • V := by
    ext k
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [← hV k]
    apply Finset.sum_congr rfl
    intro h _
    by_cases e : h = i
    · simp [e, hu, hv]
    · simp [B, e]
  have detV := Matrix.det_updateRow_sum B j (fun h => v h-u h)
  rw [rowV, smul_eq_mul, detB] at detV
  refine ⟨d1, ?_⟩
  rw [← detV, Matrix.det_updateRow_smul]
  dsimp [B]
  rw [Matrix.updateRow_comm _ hij, Matrix.det_updateRow_smul]
  exact ⟨((A.updateRow j V).updateRow i U).det, by ring⟩

/-- A root forces q to divide the determinant. Comparing two evaluation rows gives a
second factor of q in (s-r) det A. -/
theorem index {d q r s : ℕ} (hd : 2 ≤ d) (hq : 0 < q) (A : Matrix (Fin d) (Fin d) ℤ)
    (hr : ∀ j, (q : ℤ) ∣ ∑ i : Fin d, (r : ℤ)^i.val * A i j)
    (hs : ∀ j, (q : ℤ) ∣ ∑ i : Fin d, (s : ℤ)^i.val * A i j) :
    (q : ℤ) ∣ A.det ∧ (q : ℤ) ∣ (A.det / q) * ((s:ℤ)-r) := by
  let i : Fin d := ⟨0,by omega⟩
  let j : Fin d := ⟨1,by omega⟩
  have h := row_pair A (i:=i) (j:=j) (by intro h; have e : (0:ℕ)=1 := congrArg Fin.val h; omega)
    (fun k => (r:ℤ)^k.val) (fun k => (s:ℤ)^k.val) (by simp [i]) (by simp [i]) q hr hs
  simp only [j, pow_one] at h
  refine ⟨h.1, ?_⟩
  obtain ⟨k,hk⟩ := h.2
  refine ⟨k, ?_⟩
  have he := Int.ediv_mul_cancel h.1
  have hn : (q:ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  apply mul_right_cancel₀ hn
  calc A.det / q * ((s:ℤ) - r) * q = ((s:ℤ)-r) * (A.det / q * q) := by ring
       _ = _ := by rw [he, hk]; ring

/-- When a nonzero integer times the difference of any two residues is divisible
by q, there are at most its absolute value many such residues in [0,q). -/
theorem residue_count {a : ℤ} (ha : a ≠ 0) {q : ℕ} (hq : 0<q) (S : Finset ℕ)
    (bounded : ∀ r∈S, r<q) (law : ∀ r∈S, ∀ s∈S, (q:ℤ) ∣ a*((s:ℤ)-r)) :
    S.card ≤ a.natAbs := by
  let h := a.natAbs
  have hp : 0<h := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr ha)
  change S.card ≤ h
  rw [← Finset.card_range h]
  apply Finset.card_le_card_of_injOn (fun r => h*r/q)
  · intro r hr
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hq).mpr
    exact Nat.mul_lt_mul_of_pos_left (bounded r hr) hp
  · intro r hr s hs he
    have e := law r hr s hs
    have emod : h*r ≡ h*s [MOD q] := by
      apply Int.natCast_modEq_iff.mp
      rw [Int.modEq_iff_dvd]
      push_cast
      rw [← mul_sub]
      change (q:ℤ) ∣ (a.natAbs:ℤ)*((s:ℤ)-r)
      rw [Int.natCast_natAbs]
      rcases le_total 0 a with hn|hn
      · rwa [abs_of_nonneg hn]
      · rwa [abs_of_nonpos hn, neg_mul, dvd_neg]
    have hrem : h*r%q=h*s%q := emod
    change h*r/q=h*s/q at he
    apply Nat.eq_of_mul_eq_mul_left hp
    calc h*r = h*r%q+q*(h*r/q) := (Nat.mod_add_div _ _).symm
         _ = h*s := by rw [hrem, he, Nat.mod_add_div]

/-- If the nonzero determinant has absolute value at most K q, then at most K
residues r in [0,q) annihilate every column of A. The quotient of h r by q
separates these residues, since its remainder is fixed and h = |det A / q|. -/
theorem fiber {d q K : ℕ} (hd : 2 ≤ d) (hq : 0 < q) (A : Matrix (Fin d) (Fin d) ℤ)
    (hD : A.det ≠ 0) (small : A.det.natAbs ≤ K*q) :
    ((Finset.range q).filter (fun r : ℕ => ∀ j, (q : ℤ) ∣
      ∑ i : Fin d, (r : ℤ)^i.val * A i j)).card ≤ K := by
  classical
  let S := (Finset.range q).filter (fun r : ℕ => ∀ j, (q : ℤ) ∣
    ∑ i : Fin d, (r : ℤ)^i.val * A i j)
  change S.card ≤ K
  by_cases hn : S.Nonempty
  · obtain ⟨r₀, hr₀⟩ := hn
    obtain ⟨_,hr₀'⟩ := Finset.mem_filter.mp hr₀
    have hdiv := (index hd hq A hr₀' hr₀').1
    let h := (A.det / (q:ℤ)).natAbs
    have hprod : h*q=A.det.natAbs := by
      simpa [h,Int.natAbs_mul] using congrArg Int.natAbs (Int.ediv_mul_cancel hdiv)
    have hp : 0<h := by
      have : A.det.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD
      by_contra! hz
      have : h=0 := by omega
      simp_all
    have hle : h≤K := by
      exact Nat.le_of_mul_le_mul_right (hprod.le.trans small) hq
    refine (residue_count (a:=A.det/(q:ℤ)) ?_ hq S ?_ ?_).trans hle
    · exact Int.natAbs_ne_zero.mp hp.ne'
    · exact fun _ hr => Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    · exact fun _ hr _ hs =>
        (index hd hq A (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hs).2).2
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

end OMA.Index975

/- Uniform root counts for every nonzero polynomial of degree at most one. -/

namespace OMA.Linear975

open Finset Polynomial

theorem roots {f : ℤ[X]} (hd : f.natDegree = 1) {q : ℕ} (hq : 0<q) :
    Nat.count (fun r : ℕ => (q:ℤ) ∣ f.eval (r:ℤ)) q ≤ f.leadingCoeff.natAbs := by
  have hne : f ≠ 0 := fun h => by simp [h] at hd
  have hcoeff : f.coeff 1 = f.leadingCoeff := by
    rw [← hd,Polynomial.coeff_natDegree]
  have heval (r : ℤ) : f.eval r = f.leadingCoeff * r + f.coeff 0 := by
    calc f.eval r = (C (f.coeff 1) * X + C (f.coeff 0)).eval r :=
            congrArg (fun p : ℤ[X] => p.eval r) (eq_X_add_C_of_natDegree_le_one hd.le)
         _ = _ := by simp [hcoeff]
  rw [Nat.count_eq_card_filter_range]
  apply OMA.Index975.residue_count (Polynomial.leadingCoeff_ne_zero.mpr hne) hq
  · exact fun _ hr => Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  · intro r hr s hs
    have h := dvd_sub (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp hr).2
    simpa only [heval, add_sub_add_right_eq_sub, mul_sub] using h

private theorem sum_bound (f : ℤ[X]) (K : ℕ)
    (bound : ∀ q : ℕ, 0 < q → Nat.count (fun r : ℕ => (q:ℤ) ∣ f.eval (r:ℤ)) q ≤ K) :
    ∃ C ≥ (0:ℝ), ∀ N : ℕ, (∑ q ∈ Icc 1 N,
      (Nat.count (fun n : ℕ => (q:ℤ) ∣ f.eval (n:ℤ)) q : ℝ)) ≤ C*N := by
  refine ⟨K, by positivity, fun N => ?_⟩
  calc (∑ q ∈ Icc 1 N, (Nat.count (fun n : ℕ => (q:ℤ) ∣ f.eval (n:ℤ)) q : ℝ))
        ≤ ∑ _q ∈ Icc 1 N, (K:ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          exact_mod_cast bound q (Finset.mem_Icc.mp hq).1
       _ = (K:ℝ)*N := by simp [mul_comm]

theorem linear (f : ℤ[X]) (hd : f.natDegree = 1) :
    ∃ C ≥ (0:ℝ), ∀ N : ℕ, (∑ q ∈ Icc 1 N,
      (Nat.count (fun n : ℕ => (q:ℤ) ∣ f.eval (n:ℤ)) q : ℝ)) ≤ C*N :=
  sum_bound f f.leadingCoeff.natAbs (fun _ hq => roots hd hq)

theorem constant (f : ℤ[X]) (hne : f ≠ 0) (hd : f.natDegree = 0) :
    ∃ C ≥ (0:ℝ), ∀ N : ℕ, (∑ q ∈ Icc 1 N,
      (Nat.count (fun n : ℕ => (q:ℤ) ∣ f.eval (n:ℤ)) q : ℝ)) ≤ C*N := by
  have h : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hd
  have hn : f.coeff 0 ≠ 0 := fun e => hne (by simpa [e] using h)
  apply sum_bound f (f.coeff 0).natAbs
  intro q hq
  by_cases hdiv : (q:ℤ) ∣ f.coeff 0
  · have hnat : q ∣ (f.coeff 0).natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hdiv
    exact (Nat.count_le _).trans (Nat.le_of_dvd (Int.natAbs_pos.mpr hn) hnat)
  · have hnot (n : ℕ) : ¬(q:ℤ) ∣ f.eval (n:ℤ) := by
      have he : f.eval (n:ℤ) = f.coeff 0 := by
        simpa using congrArg (fun p : ℤ[X] => p.eval (n:ℤ)) h
      rwa [he]
    simp [Nat.count_eq_card_filter_range,hnot]

end OMA.Linear975

/- Short evaluation vectors and the size of their integer boxes. -/

namespace OMA.Box975
open Finset
open scoped BigOperators

/-- The largest integer side length whose d-th power fits in q. -/
def radius (d q : ℕ) := Nat.findGreatest (fun n => n^d ≤ q) q

theorem radius_pow {d q : ℕ} (hd : 0 < d) : (radius d q)^d ≤ q :=
  Nat.findGreatest_spec (P := fun n => n^d ≤ q) (Nat.zero_le q) (by simp [hd.ne'])

theorem radius_pos {d q : ℕ} (hq : 0 < q) : 1 ≤ radius d q :=
  Nat.le_findGreatest (P := fun n => n^d ≤ q) hq (by simpa using (show 1 ≤ q from hq))

theorem radius_mono {d q N : ℕ} (hd : 0 < d) (h : q ≤ N) : radius d q ≤ radius d N :=
  Nat.le_findGreatest (P := fun n => n^d ≤ N)
    ((Nat.findGreatest_le (P := fun n => n^d ≤ q) q).trans h) ((radius_pow hd).trans h)

theorem lt_succ_radius_pow {d q : ℕ} (hd : 0 < d) : q < (radius d q+1)^d := by
  by_contra! he
  have hle : radius d q+1 ≤ q := (le_self_pow₀ (by omega : 1 ≤ radius d q+1) hd.ne').trans he
  have h := Nat.le_findGreatest (P := fun n => n^d ≤ q) hle he
  change radius d q + 1 ≤ radius d q at h
  omega

/-- Two vectors in the positive box have the same value modulo q. Subtract them
to obtain a nonzero vector in the centered box. -/
theorem short_vector {d q : ℕ} (hd : 0 < d) (hq : 0 < q) (r : ℕ) :
    ∃ b : Fin d → ℤ, b ≠ 0 ∧ (∀ i, (b i).natAbs ≤ radius d q) ∧
      (∑ i, (b i : ZMod q) * (r : ZMod q)^i.val) = 0 := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  let t := radius d q
  let E (u : Fin d → Fin (t+1)) := ∑ i, ((u i).val : ZMod q) * (r : ZMod q)^i.val
  have hcard : Fintype.card (ZMod q) < Fintype.card (Fin d → Fin (t+1)) := by
    simpa [Fintype.card_pi_const, ZMod.card, t] using lt_succ_radius_pow (q:=q) hd
  obtain ⟨u,v,huv,he⟩ := Fintype.exists_ne_map_eq_of_card_lt E hcard
  let b (i : Fin d) : ℤ := ((u i).val : ℤ) - (v i).val
  refine ⟨b, ?_, ?_, ?_⟩
  · intro hb
    apply huv
    funext i
    apply Fin.ext
    have h := congrFun hb i
    change ((u i).val : ℤ) - (v i).val = 0 at h
    omega
  · intro i
    have hu := (u i).isLt
    have hv := (v i).isLt
    change (((u i).val : ℤ) - (v i).val).natAbs ≤ t
    omega
  · change (∑ i, ((((u i).val : ℤ) - (v i).val : ℤ) : ZMod q) * _) = 0
    simpa only [Int.cast_sub, Int.cast_natCast, sub_mul, Finset.sum_sub_distrib,
      sub_eq_zero] using he

def box (d t : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ => Icc (-(t:ℤ)) (t:ℤ))

theorem mem_box {d t : ℕ} {b : Fin d → ℤ} (hb : ∀ i, (b i).natAbs ≤ t) : b ∈ box d t := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have := hb i
  apply mem_Icc.mpr
  omega

theorem card_box {d N : ℕ} (hd : 0 < d) (hN : 0 < N) :
    (box d (radius d N)).card ≤ 3^d * N := by
  let t := radius d N
  have ht : 1 ≤ t := radius_pos hN
  have hc : (Icc (-(t:ℤ)) (t:ℤ)).card = 2*t+1 := by rw [Int.card_Icc]; omega
  calc
    (box d t).card = (2*t+1)^d := by simp [box, hc]
    _ ≤ (3*t)^d := Nat.pow_le_pow_left (by omega) _
    _ ≤ 3^d*N := by rw [mul_pow]; exact Nat.mul_le_mul_left _ (radius_pow hd)

/-- Quotients D/q label all divisors lying in the short terminal interval. -/
theorem card_large_divisors {D N K : ℕ} (hD : 0 < D) :
    ((Icc 1 N).filter (fun q => q ∣ D ∧ D ≤ K*q)).card ≤ K := by
  classical
  let S := (Icc 1 N).filter (fun q => q ∣ D ∧ D ≤ K*q)
  have spec {q} (h : q ∈ S) : 0 < q ∧ q ∣ D ∧ D ≤ K*q := by
    obtain ⟨hq, hd, hk⟩ := mem_filter.mp h
    exact ⟨(mem_Icc.mp hq).1,hd,hk⟩
  have hcard : S.card ≤ (Icc 1 K).card := by
    apply card_le_card_of_injOn (fun q => D/q)
    · intro q hq
      obtain ⟨hp,hd,hk⟩ := spec hq
      have he := Nat.div_mul_cancel hd
      apply mem_Icc.mpr
      constructor
      · exact Nat.div_pos (Nat.le_of_dvd hD hd) hp
      · exact Nat.le_of_mul_le_mul_right (he.le.trans hk) hp
    · intro q hq s hs heq
      obtain ⟨hp,dq,_⟩ := spec hq
      obtain ⟨_,ds,_⟩ := spec hs
      have eq₁ := Nat.div_mul_cancel dq
      have eq₂ := Nat.div_mul_cancel ds
      change D / q = D / s at heq
      rw [← heq] at eq₂
      have hn : 0 < D/q := Nat.div_pos (Nat.le_of_dvd hD dq) hp
      exact Nat.eq_of_mul_eq_mul_left hn (eq₁.trans eq₂.symm)
  simpa [S] using hcard

/-- Count roots by their short vector. The determinant restricts both the
number of possible moduli for a vector and the number of roots per modulus. -/
theorem incidence {d N K : ℕ} (hd : 0 < d) (hN : 0 < N)
    (roots : ℕ → Finset ℕ) (detAbs : (Fin d → ℤ) → ℕ)
    (rows : (Fin d → ℤ) → ℕ → Finset ℕ)
    (nonsing : ∀ b, b ≠ 0 → 0 < detAbs b)
    (fiber : ∀ b q, 0 < q → b ≠ 0 → detAbs b ≤ K*q → (rows b q).card ≤ K)
    (cover : ∀ q ∈ Icc 1 N, ∀ r ∈ roots q, ∃ b ∈ box d (radius d N),
      b ≠ 0 ∧ q ∣ detAbs b ∧ detAbs b ≤ K*q ∧ r ∈ rows b q) :
    (∑ q ∈ Icc 1 N, (roots q).card) ≤ (3^d*K^2)*N := by
  classical
  let B := box d (radius d N)
  let Q := Icc 1 N
  let slice (b : Fin d → ℤ) (q : ℕ) := if b ≠ 0 ∧ q ∣ detAbs b ∧ detAbs b ≤ K*q then
    rows b q else ∅
  have bound (b : Fin d → ℤ) : (∑ q ∈ Q, (slice b q).card) ≤ K^2 := by
    by_cases hb : b = 0
    · simp [slice,hb]
    let S := Q.filter (fun q => q ∣ detAbs b ∧ detAbs b ≤ K*q)
    have hs : S.card ≤ K := card_large_divisors (nonsing b hb)
    calc
      (∑ q ∈ Q, (slice b q).card) ≤ ∑ q ∈ Q, (if q ∣ detAbs b ∧ detAbs b ≤ K*q then K else 0) := by
        apply sum_le_sum
        intro q hq
        by_cases h : q ∣ detAbs b ∧ detAbs b ≤ K*q
        · simpa [slice,hb,h] using fiber b q (mem_Icc.mp hq).1 hb h.2
        · simp [slice,hb,h]
      _ = S.card*K := by rw [← sum_filter]; simp [S]
      _ ≤ K^2 := by rw [sq]; exact Nat.mul_le_mul_right _ hs
  calc
    (∑ q ∈ Q, (roots q).card) ≤ ∑ q ∈ Q, ∑ b ∈ B, (slice b q).card := by
      apply sum_le_sum
      intro q hq
      apply le_trans (b := (B.biUnion (fun b => slice b q)).card) _ (card_biUnion_le ..)
      apply card_le_card
      intro r hr
      obtain ⟨b,hb,hn,hdiv,hsize,hr'⟩ := cover q hq r hr
      exact mem_biUnion.mpr ⟨b,hb,by simpa [slice,hn,hdiv,hsize] using hr'⟩
    _ = ∑ b ∈ B, ∑ q ∈ Q, (slice b q).card := sum_comm
    _ ≤ ∑ _ ∈ B, K^2 := sum_le_sum (fun b _ => bound b)
    _ = B.card*K^2 := by simp
    _ ≤ (3^d*K^2)*N := by
      have h := Nat.mul_le_mul_right (K^2) (card_box hd hN)
      calc B.card*K^2 ≤ 3^d*N*K^2 := h
           _ = _ := by ring

end OMA.Box975

namespace OMA.Mean975
open Polynomial Finset Box975 Companion975

/-- The determinant argument treats degree at least two. The linear case
follows directly from the congruence for a linear polynomial. -/
theorem mean (f : ℤ[X]) (hd : f.natDegree ≠ 0) (hf : Irreducible f) :
    ∃ C ≥ (0 : ℝ), ∀ N : ℕ,
      (∑ q ∈ Icc 1 N, (Nat.count (fun r : ℕ => (q:ℤ) ∣ f.eval (r:ℤ)) q : ℝ)) ≤ C*N := by
  classical
  by_cases hone : f.natDegree = 1
  · exact Linear975.linear f hone
  have hd₂ : 2 ≤ f.natDegree := by omega
  obtain ⟨K,hK⟩ := determinant_bound f
  refine ⟨(3^f.natDegree*K^2 : ℕ), by positivity, ?_⟩
  intro N
  by_cases hN : N = 0
  · simp [hN]
  let roots (q : ℕ) := (range q).filter (fun r : ℕ => (q:ℤ) ∣ f.eval (r:ℤ))
  let D (b : Fin f.natDegree → ℤ) := (matrix f b).det.natAbs
  let rows (b : Fin f.natDegree → ℤ) (q : ℕ) :=
    (range q).filter (fun r : ℕ => ∀ j, (q:ℤ) ∣ ∑ i : Fin f.natDegree, (r:ℤ)^i.val * matrix f b i j)
  have hpos : 0 < f.natDegree := Nat.pos_of_ne_zero hd
  have hn : ∀ b, b ≠ 0 → 0 < D b := fun b hb =>
    Int.natAbs_pos.mpr (det_ne_zero f hf hd b hb)
  have fib : ∀ b q, 0 < q → b ≠ 0 → D b ≤ K*q → (rows b q).card ≤ K := by
    intro b q hq hb hsize
    exact Index975.fiber hd₂ hq (matrix f b) (det_ne_zero f hf hd b hb) hsize
  have hcount := Box975.incidence (K:=K) hpos (Nat.pos_of_ne_zero hN) roots D rows hn fib
  have cover : ∀ q ∈ Icc 1 N, ∀ r ∈ roots q, ∃ b ∈ box f.natDegree (radius f.natDegree N),
      b ≠ 0 ∧ q ∣ D b ∧ D b ≤ K*q ∧ r ∈ rows b q := by
    intro q hq r hr
    obtain ⟨hqpos,hqN⟩ := mem_Icc.mp hq
    obtain ⟨hrlt,hroot⟩ := mem_filter.mp hr
    obtain ⟨b,hb,hshort,hzero⟩ := short_vector hpos hqpos r
    have hc := columns_divisible f q r b hroot hzero
    have hdiv := (Index975.index hd₂ hqpos (matrix f b) hc hc).1
    have hdiv' : q ∣ D b := by simpa [D] using Int.natAbs_dvd_natAbs.mpr hdiv
    have hbnd : D b ≤ K*q := (hK _ b hshort).trans (Nat.mul_le_mul_left K (radius_pow hpos))
    exact ⟨b, mem_box (fun i => (hshort i).trans (radius_mono hpos hqN)), hb, hdiv', hbnd,
      mem_filter.mpr ⟨hrlt,hc⟩⟩
  have h := hcount cover
  simp only [roots, ← Nat.count_eq_card_filter_range] at h
  exact_mod_cast h

end OMA.Mean975

theorem OMA.solution : OMA.R_Erdos975_erdos_975_R1.H1 := OMA.Mean975.mean
