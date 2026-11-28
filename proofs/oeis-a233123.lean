import OMAStatements.S_oeis_a233123
import Mathlib.Tactic

open OMA.S_oeis_a233123 PowerSeries

namespace SixColors

private def oldRow (r : Row) : Bool :=
  compatible r.1 r.2 && r.1 != 2 && r.2 != 2 && r.1 != 3 && r.2 != 3

private lemma compatible_next (seen : Bool) (r s : Row) (hs : s ∈ nextRows seen r) :
    compatible s.1 s.2=true := by
  have h := (List.mem_filter.mp hs).2
  simp only [legal,Bool.and_eq_true_iff] at h
  tauto

set_option maxRecDepth 8192 in
private lemma degree : ∀ r : Row, compatible r.1 r.2=true → (nextRows true r).length=12 := by
  decide +kernel

-- As long as only the first two color pairs have appeared, four successors
-- still use those pairs and four introduce the third pair in its allowed order.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
private lemma restrictedDegrees : ∀ r : Row, oldRow r=true →
    ((nextRows false r).filter usesTwo).length=4 ∧
    ((nextRows false r).filter (fun s => !(usesTwo s))).length=4 ∧
    ∀ s ∈ nextRows false r, usesTwo s=false → oldRow s=true := by
  decide +kernel

private lemma sumGroups {α : Type} (xs : List α) (f : α → ℕ) (p : α → Bool) (u v : ℕ)
    (h : ∀ x ∈ xs, f x = if p x then u else v) :
    (xs.map f).sum=(xs.filter p).length*u + (xs.filter (fun x => !(p x))).length*v := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hhead := h x (by simp)
    have htail := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    cases e : p x <;> simp [e,hhead,htail,Nat.succ_mul] <;> omega

private lemma free (k : ℕ) (r : Row) (hr : compatible r.1 r.2=true) :
    count k r true=12^k := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    rw [count]
    simp only [Bool.true_or]
    have h := sumGroups (nextRows true r) (fun s => count k s true) (fun _ => true) (12^k) 0
      (fun s hs => ih s (compatible_next true r s hs))
    simpa [degree r hr,pow_succ,Nat.mul_comm] using h

private def limited : ℕ → ℕ
  | 0 => 1
  | n+1 => 4*12^n+4*limited n

private lemma limitedCount (k : ℕ) (r : Row) (hr : oldRow r=true) :
    count k r false=limited k := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    obtain ⟨newRows,oldRows,keep⟩ := restrictedDegrees r hr
    rw [count]
    simp only [Bool.false_or]
    have h := sumGroups (nextRows false r) (fun s => count k s (usesTwo s)) usesTwo
      (12^k) (limited k) (by
        intro s hs
        cases e : usesTwo s with
        | false => simpa using ih s (keep s hs e)
        | true => simpa using free k s (compatible_next false r s hs))
    simpa only [limited,newRows,oldRows] using h

private lemma half (n : ℕ) : 2*a (n+1)=12^n+4^n := by
  change 2*count n (0,1) false=_
  rw [limitedCount n (0,1) (by decide)]
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [limited,pow_succ]
    omega

private lemma formula (n : ℕ) : 6*a (n+1)=4^n*(3^(n+1)+3) := by
  calc
    _=3*(2*a (n+1)) := by ring
    _=_ := by rw [half,show (12:ℕ)=4*3 by decide,mul_pow,pow_succ]; ring

private lemma rec (n : ℕ) : a (n+3)+48*a (n+1)=16*a (n+2) := by
  have h₀ := half n
  have h₁ := half (n+1)
  have h₂ := half (n+2)
  simp only [pow_succ] at h₁ h₂
  change 2*a (n+2)=12^n*12+4^n*4 at h₁
  change 2*a (n+3)=12^n*12*12+4^n*4*4 at h₂
  omega

private lemma seriesOfRec (f : ℕ → ℚ) (z : f 0=0) (o : f 1=1) (t : f 2=8)
    (R : ∀ n, f (n+3)+48*f (n+1)=16*f (n+2)) :
    (1-4*X)*(1-12*X)*(PowerSeries.mk f)=X*(1-8*X) := by
  let F := PowerSeries.mk f
  have h : F-C (16:ℚ)*(F*X)+C (48:ℚ)*((F*X)*X)=X-C (8:ℚ)*X^2 := by
    ext k
    by_cases hk : k ≤ 2
    · interval_cases k <;> norm_num [F,coeff_C_mul,coeff_succ_mul_X,coeff_X,coeff_X_pow,
        coeff_zero_eq_constantCoeff,z,o,t]
    · obtain ⟨j,rfl⟩ : ∃ j, k=j+3 := ⟨k-3,by omega⟩
      simp [F,coeff_C_mul,coeff_succ_mul_X,coeff_X,coeff_X_pow]
      linarith [R j]
  change (1-4*X)*(1-12*X)*F=_
  simp only [map_ofNat] at h
  linear_combination h

private lemma series : (1-4*X)*(1-12*X)*(PowerSeries.mk (fun n => (a n : ℚ))) =
    X*(1-8*X) := by
  apply seriesOfRec
  · rfl
  · exact_mod_cast (show a 1=1 by decide)
  · exact_mod_cast (show a 2=8 by decide)
  · intro j; exact_mod_cast rec j

end SixColors

theorem OMA.solution : type_of% @OMA.S_oeis_a233123.main :=
  ⟨SixColors.rec,SixColors.series,SixColors.formula⟩
