import OMAStatements.S_mo_483753
import Mathlib

/-!
# Proof of Kurkov's generalized Stirling identity

Source: https://mathoverflow.net/questions/483753 (Mikhail Kurkov).
The two triangles are OEIS A358612 and A373183.

We work in the integral falling-factorial basis. For E_j=(X)_j, the
identities X E_j=E_{j+1}+j E_j and X E_j(X-1)=E_{j+1} give the two
operators needed to recover the coefficients. For an even binary row,
multiply the shifted-polynomial recurrence by X-1 before comparing
coefficients. This both recovers the integer quotient in the question
and proves that its denominator divides its numerator exactly.
-/

namespace OMA.S_mo_483753
open Polynomial Finset
noncomputable section

def fallingSeq : Polynomial.Sequence ℤ :=
  ⟨descPochhammer ℤ,fun k => (degree_eq_natDegree (monic_descPochhammer ℤ k).ne_zero).trans
    (by rw [descPochhammer_natDegree])⟩

def fallingBasis : Module.Basis ℕ ℤ ℤ[X] := fallingSeq.basis
  (fun k => by change IsUnit (descPochhammer ℤ k).leadingCoeff; rw [(monic_descPochhammer ℤ k).leadingCoeff];exact isUnit_one)

@[simp] theorem basis_apply (k : ℕ) : fallingBasis k=descPochhammer ℤ k :=
  fallingSeq.basis_eq_self _ _

def nc (P : ℤ[X]) (k : ℕ) : ℤ := fallingBasis.repr P k

@[simp] theorem nc_falling (j k : ℕ) : nc (descPochhammer ℤ j) k = if j=k then 1 else 0 := by
  rw [nc,←basis_apply,Module.Basis.repr_self_apply]

@[simp] theorem nc_zero (k : ℕ) : nc 0 k=0 := by simp [nc]
@[simp] theorem nc_add (p q : ℤ[X]) (k : ℕ) : nc (p+q) k=nc p k+nc q k := by simp [nc]
@[simp] theorem nc_sub (p q : ℤ[X]) (k : ℕ) : nc (p-q) k=nc p k-nc q k := by simp [nc]
@[simp] theorem nc_smul (z : ℤ) (p : ℤ[X]) (k : ℕ) : nc (z • p) k=z*nc p k := by
  unfold nc
  rw [map_smul,Finsupp.smul_apply,smul_eq_mul]
@[simp] theorem nc_Cmul (z : ℤ) (p : ℤ[X]) (k : ℕ) : nc (C z*p) k=z*nc p k := by
  rw [←smul_eq_C_mul,nc_smul]

def prev (v : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | k+1 => v k

lemma rising_action (P : ℤ[X]) (k : ℕ) :
    nc (X*P) k = (k:ℤ)*nc P k + prev (nc P) k ∧
    nc (X*P.comp (X-1)) k = prev (nc P) k := by
  have hp := fallingBasis.mem_span P
  induction hp using Submodule.span_induction with
  | mem Q h =>
    obtain ⟨j,rfl⟩ := h
    have hmul : X*descPochhammer ℤ j =
        descPochhammer ℤ (j+1) + C (j:ℤ) * descPochhammer ℤ j := by
      rw [descPochhammer_succ_right, map_natCast]
      ring
    rw [basis_apply,hmul,←descPochhammer_succ_left]
    cases k with
    | zero =>
      simp only [nc_add,nc_Cmul,nc_falling,prev,Nat.succ_ne_zero,if_false,Nat.cast_zero,zero_mul,add_zero,zero_add]
      split_ifs <;> simp_all
    | succ k =>
      simp only [prev,nc_falling,nc_add,nc_Cmul]
      split_ifs <;> simp_all
  | zero => cases k <;> simp [prev]
  | add x y hx hy ih ih' =>
    cases k <;> simp_all [prev,mul_add,add_comp]; ring
  | smul z x hx ih =>
    have e₁ : X*(z • x)=z • (X*x) := by simp only [smul_eq_C_mul];ring
    have e₂ : X*(z • x).comp (X-1)=z • (X*x.comp (X-1)) := by
      simp only [smul_eq_C_mul,mul_comp,C_comp];ring
    rw [e₁,e₂,nc_smul,nc_smul,nc_smul,ih.1,ih.2]
    cases k with
    | zero => simp [prev]
    | succ k =>
      change z*((k+1:ℕ)*nc x (k+1)+nc x k) = (k+1:ℕ)*(z*nc x (k+1))+nc (z • x) k ∧
        z*nc x k=nc (z • x) k
      rw [nc_smul]; exact ⟨by ring,rfl⟩

lemma nc_low (P : ℤ[X]) : nc P 0=P.eval 0 ∧ nc P 1=P.eval 1-P.eval 0 := by
  have hp := fallingBasis.mem_span P
  induction hp using Submodule.span_induction with
  | mem Q h =>
    obtain ⟨j,rfl⟩ := h
    rw [basis_apply]; cases j with
    | zero =>
      rw [nc_falling,nc_falling];norm_num
    | succ j =>
      simp only [nc_falling,descPochhammer_eval_zero]
      cases j with
      | zero => simp
      | succ j => simp [descPochhammer_succ_left]
  | zero => simp
  | add x y hx hy ih ih' => simp_all [eval_add];ring
  | smul z x hx ih =>
    constructor
    · rw [nc_smul,ih.1,smul_eq_C_mul,eval_mul,eval_C]
    · rw [nc_smul,ih.2,smul_eq_C_mul,eval_mul,eval_mul,eval_C,eval_C];ring

theorem newton_expand (P : ℤ[X]) (d : ℕ) (h : P.natDegree ≤ d) :
    (∑ i ∈ range (d+1), C (nc P i)*descPochhammer ℤ i) = P := by
  have hspan : P ∈ Submodule.span ℤ (fallingBasis '' Set.Iic d) := by
    change P ∈ Submodule.span ℤ ((fun i => fallingBasis i) '' Set.Iic d)
    simp only [basis_apply]
    change P ∈ Submodule.span ℤ (fallingSeq '' Set.Iic d)
    rw [fallingSeq.span_degreeLE (fun i _ => by
      change IsUnit (descPochhammer ℤ i).leadingCoeff
      rw [(monic_descPochhammer ℤ i).leadingCoeff]
      exact isUnit_one),mem_degreeLE]
    exact (degree_le_natDegree.trans (by exact_mod_cast h))
  have hsup := fallingBasis.repr_support_subset_of_mem_span _ hspan
  calc
    _ = ∑ i ∈ (fallingBasis.repr P).support, C (nc P i)*descPochhammer ℤ i := by
      symm
      apply sum_subset_zero_on_sdiff
      · intro i hi; exact mem_range.mpr (Nat.lt_succ_of_le (hsup hi))
      · intro i hi
        have hv : nc P i=0 := Finsupp.notMem_support_iff.mp (mem_sdiff.mp hi).2
        simp [hv]
      · intros; rfl
    _ = P := by
      simpa [Finsupp.linearCombination_apply,Finsupp.sum,nc,smul_eq_C_mul] using fallingBasis.linearCombination_repr P
end
end OMA.S_mo_483753

namespace OMA.S_mo_483753
open Polynomial
noncomputable section

def signedRow (n : ℕ) : ℤ[X] := C ((-1:ℤ)^(weight n+1))*X*(row n).comp (-X)

lemma weight_bit (b : Bool) (n : ℕ) (h : n=0 → b=true) :
    weight (n.bit b) = weight n + (if b then 1 else 0) := by
  unfold weight
  rw [Nat.bits_append_bit _ _ h]
  cases b <;> simp

lemma row_bit (b : Bool) (n : ℕ) (h : n=0 → b=true) :
    row (n.bit b) = if b then X*row n else X*((row n).comp (X+1)-row n) := by
  unfold row
  rw [Nat.binaryRec_eq _ _ (Or.inr h)]

lemma entries_bit (b : Bool) (n : ℕ) (h : n=0 → b=true) :
    entries (n.bit b) = if b then fun (k : ℕ) => (k:ℤ)*entries n k + entries n (k-1) else evenRow (entries n) := by
  unfold entries
  rw [Nat.binaryRec_eq _ _ (Or.inr h)]

lemma signed_odd (n : ℕ) : signedRow (n.bit true)=X*signedRow n := by
  simp only [signedRow,row_bit _ _ (fun _ => rfl),weight_bit _ _ (fun _ => rfl),
    ↓reduceIte,mul_comp,X_comp,pow_succ,map_mul,map_neg,map_one]
  ring

lemma signed_even (n : ℕ) (h : n ≠ 0) :
    (X-1)*signedRow (n.bit false) =
    (X-1)*(X*signedRow n) - X*(X*(signedRow n).comp (X-1)) := by
  have hc : (X + 1 : ℤ[X]).comp (-X) = (-X).comp (X-1) := by
    simp [add_comp,neg_comp];ring
  simp only [signedRow,row_bit _ _ (fun h' => (h h').elim),
    weight_bit _ _ (fun h' => (h h').elim),Bool.false_eq_true,↓reduceIte,
    add_zero,mul_comp,X_comp,sub_comp,comp_assoc,C_comp,hc]
  ring

lemma row_zero_neg (n : ℕ) : (row n).eval 0=0 ∧ (row n).eval (-1)=(-1:ℤ)^(weight n+1) := by
  induction n using Nat.binaryRec' with
  | zero => simp [row,weight]
  | bit b n h ih =>
    rw [row_bit _ _ h,weight_bit _ _ h]
    cases b <;> simp [eval_mul,eval_sub,eval_comp,eval_add,ih.1,ih.2,pow_succ]

lemma signed_low (n : ℕ) : (signedRow n).eval 0=0 ∧ (signedRow n).eval 1=1 := by
  simp only [signedRow,eval_mul,eval_C,eval_X,eval_comp,eval_neg,
    mul_zero,zero_mul,mul_one,(row_zero_neg n).2]
  rw [←mul_pow];simp

lemma degree_even (p : ℤ[X]) : (X*(p.comp (X+1)-p)).natDegree ≤ p.natDegree := by
  have he : p.comp (X+1)=taylor 1 p := by simp [taylor_apply]
  rw [he]
  by_cases hz : taylor 1 p-p=0
  · simp [hz]
  have hp : p ≠ 0 := by rintro rfl; simp at hz
  have hlt := degree_sub_lt_right (degree_taylor p 1) hp (leadingCoeff_taylor (r:=1) (f:=p))
  have h' := natDegree_lt_natDegree hz hlt
  exact natDegree_mul_le.trans (by rw [natDegree_X];omega)

lemma signed_degree (n : ℕ) : (signedRow n).natDegree ≤ weight n+2 := by
  have aux (m : ℕ) : (row m).natDegree ≤ weight m+1 := by
    induction m using Nat.binaryRec' with
    | zero => simp [row,weight]
    | bit b m h ih =>
      rw [row_bit _ _ h,weight_bit _ _ h]
      cases b
      · simpa using (degree_even (row m)).trans ih
      · simp only [↓reduceIte]
        exact natDegree_mul_le.trans (by rw [natDegree_X];omega)
  unfold signedRow
  have hd := aux n
  calc
    _ ≤ (C ((-1:ℤ)^(weight n+1))*X).natDegree+((row n).comp (-X)).natDegree := natDegree_mul_le
    _ ≤ _ := by
      rw [natDegree_comp]
      have h := natDegree_mul_le (p:=C ((-1:ℤ)^(weight n+1))) (q:=X)
      simp at h ⊢
      omega

end
end OMA.S_mo_483753

namespace OMA.S_mo_483753
open Polynomial
noncomputable section

lemma nc_sub_one (P : ℤ[X]) (k : ℕ) :
    nc ((X-1)*P) (k+1)=(k:ℤ)*nc P (k+1) + nc P k := by
  rw [sub_mul,one_mul,nc_sub,(rising_action P _).1]
  simp only [prev,Nat.cast_succ]
  ring

lemma even_coeff_exact (n k : ℕ) (h : n ≠ 0) :
    nc (signedRow (n.bit false)) (k+1)+nc (signedRow n) (k+1) =
      ((k+2:ℤ)*nc (signedRow n) (k+2) + nc (signedRow n) (k+1) -
        nc (signedRow (n.bit false)) (k+2))*(k+1:ℤ) := by
  let p := signedRow n
  let q := signedRow (n.bit false)
  have hpoly : (X-1)*q = (X-1)*(X*p) - X*(X*p.comp (X-1)) := signed_even n h
  have he := congrArg (fun P => nc P (k+2)) hpoly
  change nc ((X-1)*q) (k+2)=nc ((X-1)*(X*p)-X*(X*p.comp (X-1))) (k+2) at he
  rw [nc_sub_one,nc_sub,nc_sub_one,(rising_action p (k+2)).1,(rising_action p (k+1)).1,
    (rising_action (X*p.comp (X-1)) (k+2)).1] at he
  simp only [prev,(rising_action p _).2,Nat.cast_succ] at he
  change nc q (k+1)+nc p (k+1) = ((k+2:ℤ)*nc p (k+2)+nc p (k+1)-nc q (k+2))*(k+1:ℤ)
  linarith only [he]

lemma even_coeff (n k : ℕ) (h : n ≠ 0) :
    nc (signedRow (n.bit false)) (k+2) =
      (k+2:ℤ)*nc (signedRow n) (k+2) + nc (signedRow n) (k+1) -
      (nc (signedRow (n.bit false)) (k+1)+nc (signedRow n) (k+1))/(k+1:ℤ) := by
  rw [Int.ediv_eq_of_eq_mul_left (by omega : (k+1:ℤ) ≠ 0) (even_coeff_exact n k h)]
  ring

lemma nc_entries (n : ℕ) : ∀ k, nc (signedRow n) k=entries n k := by
  induction n using Nat.binaryRec' with
  | zero =>
    have h : signedRow 0 = descPochhammer ℤ 2 + descPochhammer ℤ 1 := by
      simp [signedRow,weight,row,descPochhammer_succ_right];ring
    intro k
    rw [h,nc_add,nc_falling,nc_falling]
    simp only [entries,Nat.binaryRec_zero]
    split_ifs <;> omega
  | bit b n h ih =>
    cases b
    · intro k
      induction k with
      | zero =>
        rw [(nc_low _).1,(signed_low _).1,entries_bit _ _ h];rfl
      | succ k ihk =>
        cases k with
        | zero =>
          rw [(nc_low _).2,(signed_low _).1,(signed_low _).2,entries_bit _ _ h];rfl
        | succ k =>
          simp only [entries_bit false n h,Bool.false_eq_true,↓reduceIte] at ihk ⊢
          rw [evenRow,←ihk,←ih _,←ih _]
          exact even_coeff n k (fun hn => by simpa using h hn)
    · intro k
      rw [signed_odd,entries_bit _ _ h,(rising_action _ _).1]
      cases k with
      | zero => simp [prev,←ih,(nc_low _).1,(signed_low _).1]
      | succ k => simp [prev,ih]

/-- The divisions in the displayed recurrence for the integer array A358612 are exact. -/
theorem even_entries_divisible (n k : ℕ) (h : n ≠ 0) :
    (k+1:ℤ) ∣ entries (n.bit false) (k+1)+entries n (k+1) := by
  simp only [←nc_entries]
  exact ⟨_,(even_coeff_exact n k h).trans (mul_comm _ _)⟩

theorem extended_stirling_formula (n : ℕ) :
    (∑ k ∈ Finset.range (weight n+3), C (entries n k)*descPochhammer ℤ k)=signedRow n := by
  simpa only [nc_entries] using newton_expand (signedRow n) (weight n+2) (signed_degree n)

end
end OMA.S_mo_483753

theorem OMA.solution : type_of% @OMA.S_mo_483753.main := OMA.S_mo_483753.extended_stirling_formula

