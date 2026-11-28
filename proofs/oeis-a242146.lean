import OMAStatements.S_oeis_a242146
import Mathlib

namespace OMA.Windows242146

open OMA.S_oeis_a242146 Finset PowerSeries

private abbrev Word (n d : ℕ) := Fin d → Fin (n+1)

private def mass {n d : ℕ} (x : Word n d) : ℤ := ∑ i, ((x i).val : ℤ)
private abbrev Cut (n d : ℕ) (t : ℤ) := {x : Word n d // mass x ≤ t}
private noncomputable instance (n d : ℕ) (t : ℤ) : Fintype (Cut n d t) := Fintype.ofFinite _
private noncomputable def v (n d : ℕ) (t : ℤ) : ℚ := Fintype.card (Cut n d t)

private theorem mass_cons {n d : ℕ} (x : Word n (d+1)) :
    mass x = ((x 0).val : ℤ) + mass (fun i : Fin d => x i.succ) :=
  Fin.sum_univ_succ _

private def split (n d : ℕ) (t : ℤ) :
    Cut n (d+1) t ≃ (Σ j : Fin (n+1), Cut n d (t-j.val)) where
  toFun x := ⟨x.val 0,⟨fun i => x.val i.succ,by
    have h := x.property
    rw [mass_cons] at h
    omega⟩⟩
  invFun z := ⟨Fin.cons z.1 z.2.val,by
    rw [mass_cons]
    change (z.1.val : ℤ) + mass z.2.val ≤ t
    have h := z.2.property
    omega⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv z := by rcases z with ⟨j,x⟩; rfl

private theorem step (n d : ℕ) (t : ℤ) :
    v n (d+1) t = ∑ j ∈ range (n+1), v n d (t-j) := by
  unfold v
  rw [Fintype.card_congr (split n d t),Fintype.card_sigma,Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range]

private def T (d : ℕ) (t : ℤ) : ℚ :=
  if t < 0 then 0 else (t.toNat+d).choose d

private theorem base (n : ℕ) (t : ℤ) : v n 0 t = T 0 t := by
  by_cases h : t < 0
  · have : IsEmpty (Cut n 0 t) := ⟨fun x => by
      have hx := x.property
      simp [mass] at hx
      omega⟩
    simp [v,T,h]
  · have : Unique (Cut n 0 t) :=
      { default := ⟨Fin.elim0,by simpa [mass] using (le_of_not_gt h)⟩
        uniq := fun x => Subtype.ext (funext fun i => i.elim0) }
    simp [v,T,h]

private theorem pascal (d : ℕ) (t : ℤ) : T d t = T (d+1) t - T (d+1) (t-1) := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · simp [T,h,show t-1 < 0 by omega]
  · simp [T]
  · have ht : t.toNat = (t-1).toNat+1 := by omega
    have he : t.toNat + (d+1) = ((t-1).toNat+(d+1))+1 := by omega
    have he' : t.toNat+d = (t-1).toNat+(d+1) := by omega
    simp only [T,if_neg (show ¬t<0 by omega),if_neg (show ¬t-1<0 by omega)]
    rw [he, Nat.choose_succ_succ, he']
    push_cast
    ring

private theorem telescope (d k : ℕ) (t : ℤ) :
    ∑ j ∈ range k, T d (t-j) = T (d+1) t - T (d+1) (t-k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,ih,pascal d (t-k)]
    push_cast
    rw [show t-((k:ℤ)+1)=t-k-1 by ring]
    ring

private def F (d n k : ℕ) (t : ℤ) : ℚ := T d (t-(k:ℤ)*(n+1))

private theorem sumF (d n k : ℕ) (t : ℤ) :
    ∑ j ∈ range (n+1), F d n k (t-j) = F (d+1) n k t - F (d+1) n (k+1) t := by
  unfold F
  simp_rw [show ∀ j : ℕ, t-j-(k:ℤ)*(n+1) = t-(k:ℤ)*(n+1)-j by intro j; ring]
  rw [telescope]
  push_cast
  rw [show t-(k:ℤ)*(n+1)-(n+1)=t-(k+1)*(n+1) by ring]

private theorem count0 (n : ℕ) (t : ℤ) : v n 0 t = F 0 n 0 t := by simpa [F] using base n t

private theorem count1 (n : ℕ) (t : ℤ) : v n 1 t = F 1 n 0 t - F 1 n 1 t := by
  rw [step n 0]
  simp_rw [count0]
  simp only [sumF]

private theorem count2 (n : ℕ) (t : ℤ) : v n 2 t = F 2 n 0 t - 2 * F 2 n 1 t + F 2 n 2 t := by
  rw [step n 1]
  simp_rw [count1]
  simp only [sum_sub_distrib,sumF]
  ring

private theorem count3 (n : ℕ) (t : ℤ) : v n 3 t = F 3 n 0 t - 3 * F 3 n 1 t + 3 * F 3 n 2 t - F 3 n 3 t := by
  rw [step n 2]
  simp_rw [count2]
  simp only [sum_sub_distrib,sum_add_distrib,← mul_sum,sumF]
  ring

private theorem count4 (n : ℕ) (t : ℤ) : v n 4 t = F 4 n 0 t - 4 * F 4 n 1 t + 6 * F 4 n 2 t - 4 * F 4 n 3 t + F 4 n 4 t := by
  rw [step n 3]
  simp_rw [count3]
  simp only [sum_sub_distrib,sum_add_distrib,← mul_sum,sumF]
  ring

private theorem count5 (n : ℕ) (t : ℤ) : v n 5 t = F 5 n 0 t - 5 * F 5 n 1 t + 10 * F 5 n 2 t - 10 * F 5 n 3 t + 5 * F 5 n 4 t - F 5 n 5 t := by
  rw [step n 4]
  simp_rw [count4]
  simp only [sum_sub_distrib,sum_add_distrib,← mul_sum,sumF]
  ring

private def middle {n : ℕ} (x : Word n 7) : Word n 5 := fun i => x i.castSucc.succ

private theorem valid {n : ℕ} (x : Word n 7) :
    good x = true ↔ mass (middle x) ≤ 3*(n:ℤ) - max (x 0).val (x 6).val := by
  simp only [good,decide_eq_true_eq]
  have elem {i : ℕ} (hi : i < 2) : i = 0 ∨ i = 1 := by omega
  constructor
  · intro h
    have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    simp [OMA.S_oeis_a242146.get,sum_range_succ] at h0 h1
    simp [mass,middle,Fin.sum_univ_succ]
    omega
  · intro h i hi
    simp [mass,middle,Fin.sum_univ_succ] at h
    rcases elem hi with rfl | rfl <;> simp [OMA.S_oeis_a242146.get,sum_range_succ] <;> omega

private def ends (n : ℕ) :
    {x : Word n 7 // good x = true} ≃
      (Σ p : Fin (n+1) × Fin (n+1), Cut n 5 (3*(n:ℤ) - max p.1.val p.2.val)) where
  toFun x := ⟨(x.val 0,x.val 6),⟨middle x.val,(valid _).mp x.property⟩⟩
  invFun z :=
    let y := z.2.val
    ⟨![z.1.1,y 0,y 1,y 2,y 3,y 4,z.1.2],(valid _).mpr (by
      have h := z.2.property
      simpa [middle,mass,Fin.sum_univ_succ,y] using h)⟩
  left_inv x := by apply Subtype.ext; funext i; fin_cases i <;> rfl
  right_inv z := by
    rcases z with ⟨⟨l,r⟩,⟨y,hy⟩⟩
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl

private theorem maxSum (f : ℕ → ℚ) (b : ℕ) :
    ∑ i ∈ range b, ∑ j ∈ range b, f (max i j) = ∑ m ∈ range b, (2*m+1:ℚ)*f m := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [sum_range_succ,sum_range_succ (fun m => (2*(m:ℚ)+1)*f m)]
    simp_rw [sum_range_succ]
    rw [sum_add_distrib,ih]
    have col : ∑ i ∈ range b, f (max i b) = b*f b := by
      rw [sum_congr rfl (fun i hi => congrArg f (max_eq_right (mem_range.mp hi).le))]
      simp
    have row : ∑ j ∈ range b, f (max b j) = b*f b := by
      rw [sum_congr rfl (fun j hj => congrArg f (max_eq_left (mem_range.mp hj).le))]
      simp
    rw [col,row,max_self]
    ring

private theorem array_count (n : ℕ) :
    (a n : ℚ) = ∑ m ∈ range (n+1), (2*(m:ℚ)+1)*v n 5 (3*(n:ℤ)-m) := by
  classical
  have h := Fintype.card_congr (ends n)
  rw [Fintype.card_subtype,Fintype.card_sigma] at h
  unfold a
  push_cast
  rw [h,Nat.cast_sum,Fintype.sum_prod_type]
  change (∑ i : Fin (n+1), ∑ j : Fin (n+1), v n 5 (3*(n:ℤ) - max i.val j.val)) = _
  simpa only [← Fin.sum_univ_eq_sum_range,Nat.cast_max] using
    (maxSum (fun m : ℕ => v n 5 (3*(n:ℤ)-m)) (n+1))

private def B (x : ℚ) : ℚ := (x+1)*(x+2)*(x+3)*(x+4)*(x+5)/120

private theorem binValue (t : ℤ) (h : -2 ≤ t) : T 5 t = B t := by
  rcases lt_or_ge t 0 with ht | ht
  · interval_cases t <;> norm_num [T,B]
  · lift t to ℕ using ht
    simp only [T,if_neg (by omega : ¬ (t:ℤ) < 0),Int.toNat_natCast,Int.cast_natCast,B]
    have e := Nat.descFactorial_eq_factorial_mul_choose (t+5) 5
    have eqn : (t+1)*(t+2)*(t+3)*(t+4)*(t+5) = 120*(t+5).choose 5 := by
      simpa [Nat.descFactorial_succ,Nat.factorial,mul_assoc] using e
    have eqr := congrArg (fun z : ℕ => (z:ℚ)) eqn
    push_cast at eqr
    linarith

private def sectionCount (n m : ℚ) : ℚ :=
  B (3*n-m) - 5*B (2*n-m-1) + 10*B (n-m-2)

private theorem sectionValue (n m : ℕ) (hm : m ≤ n) :
    v n 5 (3*(n:ℤ)-m) = sectionCount n m := by
  rw [count5]
  unfold F sectionCount
  have z (u : ℤ) (h : u < 0) : T 5 u = 0 := by simp [T,h]
  rw [binValue _ (by omega), binValue _ (by omega),binValue _ (by omega),
    z _ (by omega),z _ (by omega),z _ (by omega)]
  push_cast
  ring_nf

private def H (n m : ℚ) : ℚ :=
  (m*(m*(m*(m*(m*(m*(-72*m + 210*n + 420) + n*(168*n - 168) + 42) + n*(n*(-630*n - 2205) - 3255) - 2730) + n*(n*(n*(-1540*n - 5320) - 7070) - 2870) + 42) + n*(n*(n*(n*(3906*n + 20685) + 44310) + 48300) + 27279) + 7350) + n*(n*(n*(385*n + 1330) + 1757) + 728) - 12))/5040

private def P (n : ℚ) : ℚ :=
  (n*(n*(n*(n*(n*(n*(1021*n + 7840) + 25753) + 47215) + 52444) + 35665) + 14022) + 2520)/2520

private theorem partialSum (n b : ℕ) :
    ∑ m ∈ range b, (2*(m:ℚ)+1)*sectionCount n m = H n b := by
  induction b with
  | zero => simp [H]
  | succ b ih =>
    rw [sum_range_succ,ih]
    unfold sectionCount B H
    push_cast
    ring

private theorem value (n : ℕ) : (a n : ℚ) = P n := by
  rw [array_count]
  calc
    _ = ∑ m ∈ range (n+1), (2*(m:ℚ)+1)*sectionCount n m := by
      apply sum_congr rfl
      intro m hm
      rw [sectionValue n m (by have h := mem_range.mp hm; omega)]
    _ = H n (n+1:ℕ) := partialSum n (n+1)
    _ = _ := by unfold H P; push_cast; ring

private theorem recurrence (n : ℕ) (hn : 9 ≤ n) :
    (a n : ℚ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+9 := ⟨n-9,by omega⟩
  simp only [show m+9-1 = m+8 by omega,show m+9-2 = m+7 by omega,show m+9-3 = m+6 by omega,show m+9-4 = m+5 by omega,show m+9-5 = m+4 by omega,show m+9-6 = m+3 by omega,show m+9-7 = m+2 by omega,show m+9-8 = m+1 by omega,value,P]
  push_cast
  ring

private theorem generating :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 8 : PowerSeries ℚ) = X * (74 + 521 * X + 1030 * X ^ 2 + 348 * X ^ 3 + 90 * X ^ 4 - 28 * X ^ 5 + 8 * X ^ 6 - X ^ 7) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*(1-X)^8 = S - (8:ℕ) • (S*X^1) + (28:ℕ) • (S*X^2) - (56:ℕ) • (S*X^3) + (70:ℕ) • (S*X^4) - (56:ℕ) • (S*X^5) + (28:ℕ) • (S*X^6) - (8:ℕ) • (S*X^7) + (S*X^8) := by simp only [nsmul_eq_mul]; ring
  have rhs : (X * (74 + 521 * X + 1030 * X ^ 2 + 348 * X ^ 3 + 90 * X ^ 4 - 28 * X ^ 5 + 8 * X ^ 6 - X ^ 7) : PowerSeries ℚ) = (74:ℕ) • X^1 + (521:ℕ) • X^2 + (1030:ℕ) • X^3 + (348:ℕ) • X^4 + (90:ℕ) • X^5 - (28:ℕ) • X^6 + (8:ℕ) • X^7 - X^8 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 9 ≤ n
  · have recn := recurrence n h
    simp only [nsmul_eq_mul,if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),
      if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega),
      if_pos (show 8 ≤ n by omega),
      if_neg (show ¬ n < 1 by omega),
      if_neg (show ¬ n-1 < 1 by omega),
      if_neg (show ¬ n-2 < 1 by omega),
      if_neg (show ¬ n-3 < 1 by omega),
      if_neg (show ¬ n-4 < 1 by omega),
      if_neg (show ¬ n-5 < 1 by omega),
      if_neg (show ¬ n-6 < 1 by omega),
      if_neg (show ¬ n-7 < 1 by omega),
      if_neg (show ¬ n-8 < 1 by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 6 by omega),
      if_neg (show n ≠ 7 by omega),
      if_neg (show n ≠ 8 by omega)]
    norm_num
    linarith
  · interval_cases n <;> norm_num [value,P]

theorem result : type_of% @OMA.S_oeis_a242146.main := ⟨generating,recurrence⟩

end OMA.Windows242146

theorem OMA.solution : type_of% @OMA.S_oeis_a242146.main := OMA.Windows242146.result
