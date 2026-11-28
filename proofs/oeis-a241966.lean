import OMAStatements.S_oeis_a241966
import Mathlib

namespace OMA.Windows241966

open OMA.S_oeis_a241966 Finset PowerSeries

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

private abbrev Exact (n s : ℕ) := {x : Word n 2 // mass x = s}
private noncomputable instance (n s : ℕ) : Fintype (Exact n s) := Fintype.ofFinite _
private noncomputable def E (n s : ℕ) : ℚ := Fintype.card (Exact n s)

private def byMass (n s : ℕ) : Cut n 2 s ≃ Cut n 2 ((s:ℤ)-1) ⊕ Exact n s where
  toFun x := if h : mass x.val = s then Sum.inr ⟨x.val,h⟩ else
    Sum.inl ⟨x.val,by have := x.property; omega⟩
  invFun
    | .inl x => ⟨x.val,by have := x.property; omega⟩
    | .inr x => ⟨x.val,x.property.le⟩
  left_inv x := by by_cases h : mass x.val = s <;> simp [h]
  right_inv z := by
    rcases z with x | x
    · have h : mass x.val ≠ s := by have := x.property; omega
      simp [h]
    · simp [x.property]

private theorem exactCount (n s : ℕ) :
    E n s = T 1 s - 2*T 1 ((s:ℤ)-(n+1)) + T 1 ((s:ℤ)-2*(n+1)) := by
  have h := Fintype.card_congr (byMass n s)
  rw [Fintype.card_sum] at h
  have hh : v n 2 s = v n 2 ((s:ℤ)-1) + E n s := by
    unfold v E
    exact_mod_cast h
  rw [count2,count2] at hh
  unfold F at hh
  simp only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,zero_mul,sub_zero,one_mul] at hh
  simp_rw [show ∀ k : ℤ, (s:ℤ)-1-k = s-k-1 by intro k; ring] at hh
  simp only [pascal 1]
  linarith

private def tri (x : ℚ) := x+1

private theorem triValue (t : ℤ) (h : -1 ≤ t) : T 1 t = tri t := by
  rcases lt_or_ge t 0 with ht | ht
  · interval_cases t; norm_num [T,tri]
  · lift t to ℕ using ht
    simp [T,if_neg (by omega : ¬ (t:ℤ) < 0),tri]

private theorem exactSmall (n s : ℕ) (h : s ≤ n) : E n s = tri s := by
  rw [exactCount,triValue _ (by omega)]
  have z (u : ℤ) (hu : u < 0) : T 1 u = 0 := by simp [T,hu]
  rw [z _ (by omega),z _ (by omega)]
  push_cast
  ring

private theorem exactLarge (n s : ℕ) (h : n ≤ s) (hs : s ≤ 2*n) :
    E n s = tri s - 2*tri ((s:ℚ)-n-1) := by
  rw [exactCount,triValue _ (by omega),triValue _ (by omega)]
  have z (u : ℤ) (hu : u < 0) : T 1 u = 0 := by simp [T,hu]
  rw [z _ (by omega)]
  push_cast
  ring_nf

private def center {n : ℕ} (x : Word n 6) : ℕ := (x 2).val + (x 3).val

private theorem valid {n : ℕ} (x : Word n 6) :
    good x = true ↔
    center x + (x 0).val + (x 1).val ≤ 2*n ∧
    center x + (x 1).val + (x 4).val ≤ 2*n ∧
    center x + (x 4).val + (x 5).val ≤ 2*n := by
  simp only [good,decide_eq_true_eq]
  unfold center
  constructor
  · intro h
    have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    have h2 := h 2 (by decide)
    simp [OMA.S_oeis_a241966.get,sum_range_succ] at h0 h1 h2
    omega
  · intro h i hi
    interval_cases i <;> simp [OMA.S_oeis_a241966.get,sum_range_succ] <;> omega

private abbrev Valid (n : ℕ) := {x : Word n 6 // good x = true}

private def idx {n : ℕ} (x : Valid n) : Fin (2*n+1) :=
  ⟨center x.val,by have h := ((valid _).mp x.property).1; omega⟩

private def lim (n r u : ℕ) := min n (r-u) + 1
private abbrev Choices (n r : ℕ) := Σ u : Fin (min n r + 1),
  Σ v : Fin (lim n r u), Fin (lim n r u) × Fin (lim n r v)

private def fiber (n : ℕ) (s : Fin (2*n+1)) :
    {x : Valid n // idx x = s} ≃ Exact n s.val × Choices n (2*n-s.val) where
  toFun z :=
    let x := z.val.val
    have es : center x = s.val := congrArg Fin.val z.property
    have hs := (valid x).mp z.val.property
    have h0 := (x 0).isLt
    have h1 := (x 1).isLt
    have h5 := (x 4).isLt
    have h6 := (x 5).isLt
    (⟨![x 2,x 3],by
        simp [mass,Fin.sum_univ_succ]
        dsimp [center] at es
        omega⟩,
     ⟨⟨(x 1).val,by omega⟩,⟨(x 4).val,by dsimp [lim]; omega⟩,
      ⟨(x 0).val,by dsimp [lim]; omega⟩,⟨(x 5).val,by dsimp [lim]; omega⟩⟩)
  invFun z := by
    let y := z.1.val
    let u := z.2.1
    let v := z.2.2.1
    let a := z.2.2.2.1
    let b := z.2.2.2.2
    have hu := u.isLt
    have hv := v.isLt
    have ha := a.isLt
    have hb := b.isLt
    dsimp [lim] at hv ha hb
    have hs := s.isLt
    let x : Word n 6 := ![⟨a.val,by omega⟩,⟨u.val,by omega⟩,y 0,y 1,⟨v.val,by omega⟩,⟨b.val,by omega⟩]
    have ex : center x = s.val := by
      have hy := z.1.property
      change mass y = _ at hy
      simp [mass,Fin.sum_univ_succ] at hy
      simp [center,x]
      omega
    exact ⟨⟨x,(valid x).mpr (by rw [ex]; simp [x]; omega)⟩,Fin.ext ex⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv z := by
    rcases z with ⟨⟨y,hy⟩,⟨u,v,a,b⟩⟩
    apply Prod.ext
    · apply Subtype.ext
      funext i
      fin_cases i <;> rfl
    · rfl

private def outer (n r : ℕ) : ℚ := ∑ u ∈ range (min n r+1),
  ∑ v ∈ range (lim n r u), (lim n r u : ℚ)*(lim n r v)

private theorem outerCount (n r : ℕ) : (Fintype.card (Choices n r) : ℚ) = outer n r := by
  simp only [Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,Nat.cast_sum,Nat.cast_mul]
  unfold outer
  simp only [← Fin.sum_univ_eq_sum_range]

private theorem arrayCount (n : ℕ) :
    (a n : ℚ) = ∑ s ∈ range (2*n+1), E n s * outer n (2*n-s) := by
  classical
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv (@idx n))
  rw [Fintype.card_sigma,Fintype.card_subtype] at h
  unfold a
  push_cast
  rw [← h,Nat.cast_sum,← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_congr
  intro s
  rw [Fintype.card_congr (fiber n s),Fintype.card_prod,Nat.cast_mul,outerCount]
  rfl


private theorem sumDiff (f : ℕ → ℚ) (P : ℚ → ℚ) (b : ℕ)
    (h : ∀ j < b, f j = P (j+1) - P j) :
    ∑ j ∈ range b, f j = P b - P 0 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [sum_range_succ,ih (fun j hj => h j (by omega)),h b (by omega)]
    push_cast
    ring

private theorem sumTwo (f : ℕ → ℚ) (P Q : ℚ → ℚ) (a b : ℕ) (hab : a ≤ b)
    (hp : ∀ j < a, f j = P (j+1) - P j)
    (hq : ∀ j, a ≤ j → j < b → f j = Q (j+1) - Q j) :
    ∑ j ∈ range b, f j = P a - P 0 + (Q b - Q a) := by
  obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [sum_range_add,sumDiff f P a hp]
  congr 1
  have h := sumDiff (fun j => f (a+j)) (fun z => Q (a+z)) c (by
    intro j hj
    rw [hq (a+j) (by omega) (by omega)]
    push_cast
    rw [add_assoc])
  simpa using h

private def A (r t : ℚ) := t*(r+1)-t*(t-1)/2
private def W (n r t : ℚ) := t*((r-n+1)*(n+1)+A r t-A r (r-n+1))
private def row (n r u : ℕ) : ℚ :=
  (lim n r u : ℚ)*∑ j ∈ range (lim n r u), (lim n r j : ℚ)

private theorem rows (n r : ℕ) : outer n r = ∑ u ∈ range (min n r+1), row n r u := by
  simp only [outer,row,mul_sum]

private theorem lowRow (n r u : ℕ) (hr : r ≤ n) (hu : u ≤ r) :
    row n r u = ((r:ℚ)-u+1)*A r ((r:ℚ)-u+1) := by
  have length (j : ℕ) (hj : j ≤ r) : lim n r j = r-j+1 := by unfold lim; omega
  unfold row
  rw [length u hu,sumDiff _ (A r)]
  · push_cast [Nat.cast_sub hu]
    simp [A]
  · intro j hj
    have hjr : j ≤ r := by omega
    rw [length j hjr]
    push_cast [Nat.cast_sub hjr]
    unfold A
    ring

private theorem highRow (n r u : ℕ) (hn : n ≤ r) (hr : r ≤ 2*n) (hu : u ≤ n) :
    row n r u = W n r (lim n r u) := by
  let k := r-n+1
  have hk : k ≤ lim n r u := by dsimp [k,lim]; omega
  have hkq : (k:ℚ) = (r:ℚ)-n+1 := by dsimp [k]; push_cast [Nat.cast_sub hn]; rfl
  unfold row
  rw [sumTwo _ (fun t => t*(n+1:ℚ)) (A r) k _ hk]
  · rw [hkq]; unfold W; ring
  · intro j hj
    have h : lim n r j = n+1 := by dsimp [lim,k] at *; omega
    rw [h]; push_cast; ring
  · intro j hkj hj
    have hjr : j ≤ r := by dsimp [lim] at hj; omega
    have h : lim n r j = r-j+1 := by dsimp [lim,k] at *; omega
    rw [h]
    push_cast [Nat.cast_sub hjr]
    unfold A
    ring

private def U (r t : ℚ) : ℚ :=
  (t*(r*(r*(12*r + 54) + 82) + t*(r*(-6*r - 18) + t*(-4*r + 3*t - 6) - 15) + 42))/24

private def V (n r t : ℚ) : ℚ :=
  (t*(n*(18 - 18*n) + r*(n*(48 - 12*n) + r*(24*n + 24) + 64) + t*(n*(6*n - 6) + r*(-12*n - 12) + t*(-4*r + 3*t - 6) - 15) + 42))/24

private def outerLo (r : ℚ) : ℚ :=
  (r*(r*(r*(5*r + 30) + 67) + 66) + 24)/24

private def outerHi (n r : ℚ) : ℚ :=
  (n*(n*(n*(24*n - 24) - 36) + 36) + r*(n*(n*(12 - 80*n) + 116) + r*(n*(84*n + 60) + r*(-24*n + r - 18) - 13) + 30) + 24)/24

private theorem lowCount (n r : ℕ) (hr : r ≤ n) : outer n r = outerLo r := by
  rw [rows,min_eq_right hr,sumDiff _ (U r)]
  · unfold U outerLo; push_cast; ring
  · intro j hj
    rw [lowRow n r j hr (by omega)]
    unfold U A
    ring

private theorem highCount (n r : ℕ) (hn : n ≤ r) (hr : r ≤ 2*n) :
    outer n r = outerHi n r := by
  let k := r-n+1
  have hk : k ≤ n+1 := by dsimp [k]; omega
  have hkq : (k:ℚ) = (r:ℚ)-n+1 := by dsimp [k]; push_cast [Nat.cast_sub hn]; rfl
  rw [rows,min_eq_left hn,sumTwo _ (fun t => t*W n r (n+1)) (V n r) k _ hk]
  · rw [hkq]
    unfold W A V outerHi
    push_cast
    ring
  · intro j hj
    have hjn : j ≤ n := by omega
    have len : lim n r j = n+1 := by dsimp [lim,k] at *; omega
    rw [highRow n r j hn hr hjn,len]
    push_cast
    ring
  · intro j hkj hj
    have hjn : j ≤ n := by omega
    have hjr : j ≤ r := by omega
    have len : lim n r j = r-j+1 := by dsimp [lim,k] at *; omega
    rw [highRow n r j hn hr hjn,len]
    push_cast [Nat.cast_sub hjr]
    unfold W A V
    ring

private def H0 (n t : ℚ) : ℚ :=
  (t*(n*(n*(n*(360*n + 1440) + 2340) + 1824) + t*(n*(n*(n*(360*n + 1440) + 2430) + 1920) + t*(n*(-180*n - 480) + t*(n*(-270*n - 480) + t*(96*n + 5*t + 99) - 235) - 315) + 590) + 576))/720

private def H1 (n t : ℚ) : ℚ :=
  (t*(n*(n*(n*(n*(960*n + 4560) + 8416) + 7524) + 3248) + t*(n*(n*(n*(-1200*n - 4560) - 6312) - 3762) + t*(n*(n*(800*n + 2280) + 2104) + t*(n*(-300*n - 570) + t*(60*n - 5*t + 57) - 263) + 627) - 812) + 540))/144

private def P (n : ℚ) : ℚ :=
  (n*(n*(n*(n*(n*(36*n + 254) + 745) + 1180) + 1079) + 546) + 120)/120

private theorem value (n : ℕ) : (a n : ℚ) = P n := by
  rw [arrayCount,sumTwo _ (H0 n) (H1 n) (n+1) _ (by omega)]
  · unfold H0 H1 P; push_cast; ring
  · intro j hj
    have hjn : j ≤ n := by omega
    have hj2 : j ≤ 2*n := by omega
    rw [exactSmall n j hjn,highCount n _ (by omega) (by omega)]
    push_cast [Nat.cast_sub hj2]
    unfold H0 tri outerHi
    ring
  · intro j hj h2
    have hnj : n ≤ j := by omega
    have hj2 : j ≤ 2*n := by omega
    rw [exactLarge n j hnj hj2,lowCount n _ (by omega)]
    push_cast [Nat.cast_sub hj2]
    unfold H1 tri outerLo
    ring
private theorem recurrence (n : ℕ) (hn : 8 ≤ n) :
    (a n : ℚ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+8 := ⟨n-8,by omega⟩
  simp only [show m+8-1 = m+7 by omega,show m+8-2 = m+6 by omega,show m+8-3 = m+5 by omega,show m+8-4 = m+4 by omega,show m+8-5 = m+3 by omega,show m+8-6 = m+2 by omega,show m+8-7 = m+1 by omega,value,P]
  push_cast
  ring

private theorem generating :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 7 : PowerSeries ℚ) = X * (33 + 80 * X + 113 * X ^ 2 - 25 * X ^ 3 + 21 * X ^ 4 - 7 * X ^ 5 + X ^ 6) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*(1-X)^7 = S - (7:ℕ) • (S*X^1) + (21:ℕ) • (S*X^2) - (35:ℕ) • (S*X^3) + (35:ℕ) • (S*X^4) - (21:ℕ) • (S*X^5) + (7:ℕ) • (S*X^6) - (S*X^7) := by simp only [nsmul_eq_mul]; ring
  have rhs : (X * (33 + 80 * X + 113 * X ^ 2 - 25 * X ^ 3 + 21 * X ^ 4 - 7 * X ^ 5 + X ^ 6) : PowerSeries ℚ) = (33:ℕ) • X^1 + (80:ℕ) • X^2 + (113:ℕ) • X^3 - (25:ℕ) • X^4 + (21:ℕ) • X^5 - (7:ℕ) • X^6 + X^7 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 8 ≤ n
  · have recn := recurrence n h
    simp only [nsmul_eq_mul,if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),
      if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega),
      if_neg (show ¬ n < 1 by omega),
      if_neg (show ¬ n-1 < 1 by omega),
      if_neg (show ¬ n-2 < 1 by omega),
      if_neg (show ¬ n-3 < 1 by omega),
      if_neg (show ¬ n-4 < 1 by omega),
      if_neg (show ¬ n-5 < 1 by omega),
      if_neg (show ¬ n-6 < 1 by omega),
      if_neg (show ¬ n-7 < 1 by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 6 by omega),
      if_neg (show n ≠ 7 by omega)]
    norm_num
    linarith
  · interval_cases n <;> norm_num [value,P]

theorem result : type_of% @OMA.S_oeis_a241966.main := ⟨generating,recurrence⟩

end OMA.Windows241966

theorem OMA.solution : type_of% @OMA.S_oeis_a241966.main := OMA.Windows241966.result
