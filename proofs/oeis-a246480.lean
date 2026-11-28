import OMAStatements.S_oeis_a246480
import Mathlib

namespace OMA.Pairs246480
open OMA.S_oeis_a246480 Finset PowerSeries

private abbrev Safe (I : Type) (n : ℕ) :=
  {x : I → Fin (n+1) // ∀ i j, i ≠ j → (x i).val + (x j).val ≠ n}

private noncomputable instance (I : Type) [Fintype I] (n : ℕ) : Fintype (Safe I n) :=
  Fintype.ofFinite _

private noncomputable def V (m n : ℕ) : ℕ := Fintype.card (Safe (Fin m) n)

private def reindex {I J : Type} (e : I ≃ J) (n : ℕ) : Safe I n ≃ Safe J n where
  toFun x := ⟨fun j => x.val (e.symm j),fun i j hij => x.property _ _ (e.symm.injective.ne hij)⟩
  invFun x := ⟨fun i => x.val (e i),fun i j hij => x.property _ _ (e.injective.ne hij)⟩
  left_inv x := by apply Subtype.ext; funext i; simp
  right_inv x := by apply Subtype.ext; funext j; simp

private abbrev Side {m : ℕ} (s : Finset (Fin m)) := Fin (if s = univ then 1 else 2)
private def sideVal {m : ℕ} {s : Finset (Fin m)} (n : ℕ) (o : Side s) := if o.val=0 then 0 else n+2

private def fill {m n : ℕ} (s : Finset (Fin m)) (o : Side s) (y : Safe s n) (i : Fin m) : Fin (n+3) :=
  if hi : i ∈ s then ⟨(y.val ⟨i,hi⟩).val+1,by have := (y.val ⟨i,hi⟩).isLt; omega⟩
  else ⟨sideVal n o,by unfold sideVal; split <;> omega⟩

private theorem interior {m n : ℕ} (s : Finset (Fin m)) (o : Side s) (y : Safe s n) (i : Fin m) :
    i ∈ s ↔ 0 < (fill s o y i).val ∧ (fill s o y i).val < n+2 := by
  by_cases hi : i ∈ s
  · simp [fill,hi]; have := (y.val ⟨i,hi⟩).isLt; omega
  · have e : (fill s o y i).val = sideVal n o := by simp only [fill,dif_neg hi]
    rw [e]
    simp only [hi,false_iff,not_and]
    unfold sideVal
    split <;> omega

private def populate {m n : ℕ} (z : Σ s : Finset (Fin m), Side s × Safe s n) : Safe (Fin m) (n+2) :=
  let s := z.1
  let o := z.2.1
  let y := z.2.2
  ⟨fill s o y,by
    intro i j hij
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
    · have h := y.property ⟨i,hi⟩ ⟨j,hj⟩ (fun e => hij (congrArg Subtype.val e))
      simp only [fill,dif_pos hi,dif_pos hj]; omega
    · have h := (y.val ⟨i,hi⟩).isLt
      simp only [fill,dif_pos hi,dif_neg hj,sideVal]; split <;> omega
    · have h := (y.val ⟨j,hj⟩).isLt
      simp only [fill,dif_neg hi,dif_pos hj,sideVal]; split <;> omega
    · simp only [fill,dif_neg hi,dif_neg hj,sideVal]; split <;> omega⟩

private theorem populate_bij (m n : ℕ) : Function.Bijective (@populate m n) := by
  constructor
  · rintro ⟨s,o,y⟩ ⟨t,p,z⟩ eqn
    have h (i : Fin m) : fill s o y i = fill t p z i := congrFun (congrArg Subtype.val eqn) i
    have st : s=t := by
      ext i
      rw [interior s o y i,interior t p z i,h]
    subst t
    have yz : y=z := by
      apply Subtype.ext
      funext i
      have hh := congrArg Fin.val (h i.val)
      simpa [fill,i.property,Fin.ext_iff] using hh
    subst z
    have op : o=p := by
      apply Fin.ext
      by_cases full : s=univ
      · have a := o.isLt; have b := p.isLt
        simp [full] at a b; omega
      · obtain ⟨i,hi⟩ : ∃ i, i ∉ s := by
          by_contra! hs
          exact full (eq_univ_of_forall hs)
        have a := o.isLt; have b := p.isLt
        simp only [if_neg full] at a b
        have hh := congrArg Fin.val (h i)
        simp only [fill,dif_neg hi,sideVal] at hh
        split at hh <;> split at hh <;> omega
    subst p
    rfl
  · intro x
    let s := univ.filter fun i => 0 < (x.val i).val ∧ (x.val i).val < n+2
    have ins (i : Fin m) : i ∈ s ↔ 0 < (x.val i).val ∧ (x.val i).val < n+2 := by simp [s]
    let y : Safe s n := ⟨fun i => ⟨(x.val i.val).val-1,by have := (ins _).mp i.property; omega⟩,by
      intro i j hij
      have vi := (ins _).mp i.property
      have vj := (ins _).mp j.property
      have h := x.property i.val j.val (fun e => hij (Subtype.ext e))
      dsimp; omega⟩
    let o : Side s := ⟨if s=univ ∨ ∃ i, (x.val i).val=0 then 0 else 1,by split <;> split <;> simp_all⟩
    refine ⟨⟨s,o,y⟩,Subtype.ext (funext (fun i => Fin.ext ?_))⟩
    change (fill s o y i).val = (x.val i).val
    by_cases hi : i ∈ s
    · have h := (ins i).mp hi
      simp only [fill,dif_pos hi,y]; omega
    · have h : (x.val i).val=0 ∨ (x.val i).val=n+2 := by
        have a := (ins i).not.mp hi
        have b := (x.val i).isLt
        omega
      have hn : s ≠ univ := by intro e; exact hi (e ▸ mem_univ _)
      simp only [fill,dif_neg hi,sideVal,o,hn,false_or]
      by_cases hz : ∃ j, (x.val j).val=0
      · obtain ⟨j,hj⟩ := hz
        rw [if_pos (show ∃ j, (x.val j).val=0 from ⟨j,hj⟩),if_pos rfl]
        rcases h with e | e
        · exact e.symm
        · have ji : j ≠ i := by rintro rfl; omega
          have hh := x.property j i ji
          omega
      · rw [if_neg hz,if_neg (by decide : ¬ (1:ℕ)=0)]
        rcases h with e | e
        · exact False.elim (hz ⟨i,e⟩)
        · exact e.symm

private theorem step (m n : ℕ) : V m (n+2) =
    ∑ j ∈ range (m+1), m.choose j * ((if j=m then 1 else 2) * V j n) := by
  classical
  unfold V
  rw [← Fintype.card_congr (Equiv.ofBijective _ (populate_bij m n)),Fintype.card_sigma]
  have term (s : Finset (Fin m)) : Fintype.card (Side s × Safe s n) =
      (if s.card=m then 1 else 2) * Fintype.card (Safe (Fin s.card) n) := by
    have e : s = univ ↔ s.card=m := by simp [← s.card_eq_iff_eq_univ]
    rw [Fintype.card_prod,Fintype.card_fin,if_congr e rfl rfl]
    have eqcard : Fintype.card s = s.card := Fintype.card_coe _
    exact congrArg _ (Fintype.card_congr (reindex ((Fintype.equivFin s).trans (finCongr eqcard)) n))
  simp_rw [term]
  rw [← powerset_univ,sum_powerset]
  simp only [card_univ,Fintype.card_fin]
  apply sum_congr rfl
  intro j _
  simpa only [card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using sum_powersetCard j (univ : Finset (Fin m)) (fun k => (if k=m then 1 else 2) * Fintype.card (Safe (Fin k) n))

private def raw (m n : ℕ) : ℕ := (univ.filter (fun x : Fin m → Fin (n+1) =>
  ∀ i j, i ≠ j → (x i).val + (x j).val ≠ n)).card

private theorem raw_eq (m n : ℕ) : V m n = raw m n :=
  Fintype.card_subtype _

private theorem good_iff {n : ℕ} (x : Fin 4 → Fin (n+1)) :
    good x = true ↔ ∀ i j, i ≠ j → (x i).val + (x j).val ≠ n := by
  simp only [good,decide_eq_true_eq,Nat.lt_one_iff,forall_eq,zero_add]
  constructor
  · intro h i j hij
    rcases lt_or_gt_of_ne hij with he | he
    · simpa [OMA.S_oeis_a246480.get,i.isLt,j.isLt] using h i.val i.isLt j.val j.isLt he
    · simpa [OMA.S_oeis_a246480.get,i.isLt,j.isLt,Nat.add_comm] using h j.val j.isLt i.val i.isLt he
  · intro h i hi j hj hij
    simpa [OMA.S_oeis_a246480.get,hi,hj] using h ⟨i,hi⟩ ⟨j,hj⟩ (by exact Fin.ne_of_lt hij)

private theorem arrayCount (n : ℕ) : (a n : ℚ) = V 4 n := by
  rw [raw_eq]
  unfold a raw
  simp only [Int.cast_natCast]
  congr 2
  apply filter_congr
  intro x _
  exact good_iff x

private theorem step0 (n : ℕ) : V 0 (n+2) = V 0 n := by
  rw [step]
  norm_num [sum_range_succ,Nat.choose]

private def E0 (_t : ℚ) : ℚ := 1
private theorem valE0 (t : ℕ) : (V 0 (2*t) : ℚ) = E0 t := by
  induction t with
  | zero =>
    have h : raw 0 0 = 1 := by decide +kernel
    norm_num [raw_eq,h,E0]
  | succ t ih =>
    rw [show 2*(t+1) = (2*t)+2 by omega,step0]
    rw [ih]
    unfold E0
    ring

private def O0 (_t : ℚ) : ℚ := 1
private theorem valO0 (t : ℕ) : (V 0 (2*t+1) : ℚ) = O0 t := by
  induction t with
  | zero =>
    have h : raw 0 1 = 1 := by decide +kernel
    norm_num [raw_eq,h,O0]
  | succ t ih =>
    rw [show 2*(t+1)+1 = (2*t+1)+2 by omega,step0]
    rw [ih]
    unfold O0
    ring

private theorem step1 (n : ℕ) : V 1 (n+2) = 2*V 0 n + V 1 n := by
  rw [step]
  norm_num [sum_range_succ,Nat.choose]

private def E1 (t : ℚ) : ℚ := 2*t + 1
private theorem valE1 (t : ℕ) : (V 1 (2*t) : ℚ) = E1 t := by
  induction t with
  | zero =>
    have h : raw 1 0 = 1 := by decide +kernel
    norm_num [raw_eq,h,E1]
  | succ t ih =>
    rw [show 2*(t+1) = (2*t)+2 by omega,step1]
    push_cast
    rw [valE0,ih]
    unfold E0 E1
    ring

private def O1 (t : ℚ) : ℚ := 2*t + 2
private theorem valO1 (t : ℕ) : (V 1 (2*t+1) : ℚ) = O1 t := by
  induction t with
  | zero =>
    have h : raw 1 1 = 2 := by decide +kernel
    norm_num [raw_eq,h,O1]
  | succ t ih =>
    rw [show 2*(t+1)+1 = (2*t+1)+2 by omega,step1]
    push_cast
    rw [valO0,ih]
    unfold O0 O1
    ring

private theorem step2 (n : ℕ) : V 2 (n+2) = 2*V 0 n + 4*V 1 n + V 2 n := by
  rw [step]
  norm_num [sum_range_succ,Nat.choose]
  ring

private def E2 (t : ℚ) : ℚ := t*(4*t + 2)
private theorem valE2 (t : ℕ) : (V 2 (2*t) : ℚ) = E2 t := by
  induction t with
  | zero =>
    have h : raw 2 0 = 0 := by decide +kernel
    norm_num [raw_eq,h,E2]
  | succ t ih =>
    rw [show 2*(t+1) = (2*t)+2 by omega,step2]
    push_cast
    rw [valE0,valE1,ih]
    unfold E0 E1 E2
    ring

private def O2 (t : ℚ) : ℚ := t*(4*t + 6) + 2
private theorem valO2 (t : ℕ) : (V 2 (2*t+1) : ℚ) = O2 t := by
  induction t with
  | zero =>
    have h : raw 2 1 = 2 := by decide +kernel
    norm_num [raw_eq,h,O2]
  | succ t ih =>
    rw [show 2*(t+1)+1 = (2*t+1)+2 by omega,step2]
    push_cast
    rw [valO0,valO1,ih]
    unfold O0 O1 O2
    ring

private theorem step3 (n : ℕ) : V 3 (n+2) = 2*V 0 n + 6*V 1 n + 6*V 2 n + V 3 n := by
  rw [step]
  norm_num [sum_range_succ,Nat.choose]
  ring

private def E3 (t : ℚ) : ℚ := 8*t^3
private theorem valE3 (t : ℕ) : (V 3 (2*t) : ℚ) = E3 t := by
  induction t with
  | zero =>
    have h : raw 3 0 = 0 := by decide +kernel
    norm_num [raw_eq,h,E3]
  | succ t ih =>
    rw [show 2*(t+1) = (2*t)+2 by omega,step3]
    push_cast
    rw [valE0,valE1,valE2,ih]
    unfold E0 E1 E2 E3
    ring

private def O3 (t : ℚ) : ℚ := t*(t*(8*t + 12) + 6) + 2
private theorem valO3 (t : ℕ) : (V 3 (2*t+1) : ℚ) = O3 t := by
  induction t with
  | zero =>
    have h : raw 3 1 = 2 := by decide +kernel
    norm_num [raw_eq,h,O3]
  | succ t ih =>
    rw [show 2*(t+1)+1 = (2*t+1)+2 by omega,step3]
    push_cast
    rw [valO0,valO1,valO2,ih]
    unfold O0 O1 O2 O3
    ring

private theorem step4 (n : ℕ) : V 4 (n+2) = 2*V 0 n + 8*V 1 n + 12*V 2 n + 8*V 3 n + V 4 n := by
  rw [step]
  norm_num [sum_range_succ,Nat.choose]
  ring

private def E4 (t : ℚ) : ℚ := t*(t*(t*(16*t - 16) + 12) - 2)
private theorem valE4 (t : ℕ) : (V 4 (2*t) : ℚ) = E4 t := by
  induction t with
  | zero =>
    have h : raw 4 0 = 0 := by decide +kernel
    norm_num [raw_eq,h,E4]
  | succ t ih =>
    rw [show 2*(t+1) = (2*t)+2 by omega,step4]
    push_cast
    rw [valE0,valE1,valE2,valE3,ih]
    unfold E0 E1 E2 E3 E4
    ring

private def O4 (t : ℚ) : ℚ := t*(t*(t*(16*t + 16) + 12) + 14) + 2
private theorem valO4 (t : ℕ) : (V 4 (2*t+1) : ℚ) = O4 t := by
  induction t with
  | zero =>
    have h : raw 4 1 = 2 := by decide +kernel
    norm_num [raw_eq,h,O4]
  | succ t ih =>
    rw [show 2*(t+1)+1 = (2*t+1)+2 by omega,step4]
    push_cast
    rw [valO0,valO1,valO2,valO3,ih]
    unfold O0 O1 O2 O3 O4
    ring

private def P0 (x : ℚ) : ℚ := x*(x*(x*(x - 2) + 3) - 1)

private def P1 (x : ℚ) : ℚ := x*(x*(x*(x - 2) + 3) + 3) - 3

private theorem value (n : ℕ) : (a n : ℚ) = if n%2=0 then P0 n else P1 n := by
  rw [arrayCount]
  by_cases he : n%2=0
  · obtain ⟨t,rfl⟩ : ∃ t, n=2*t := ⟨n/2,by omega⟩
    rw [if_pos he,valE4]
    unfold E4 P0
    push_cast
    ring
  · obtain ⟨t,rfl⟩ : ∃ t, n=2*t+1 := ⟨n/2,by omega⟩
    rw [if_neg he,valO4]
    unfold O4 P1
    push_cast
    ring

private theorem generating :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) ^ 2 : PowerSeries ℚ) = 2 * X * (1 + 2 * X + 16 * X ^ 2 + 6 * X ^ 3 + 23 * X ^ 4) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*((1-X)^5*(1+X)^2) = S - (3:ℕ) • (S*X^1) + (S*X^2) + (5:ℕ) • (S*X^3) - (5:ℕ) • (S*X^4) - (S*X^5) + (3:ℕ) • (S*X^6) - (S*X^7) := by simp only [nsmul_eq_mul]; ring
  have rhs : (2 * X * (1 + 2 * X + 16 * X ^ 2 + 6 * X ^ 3 + 23 * X ^ 4) : PowerSeries ℚ) = (2:ℕ) • X^1 + (4:ℕ) • X^2 + (32:ℕ) • X^3 + (12:ℕ) • X^4 + (46:ℕ) • X^5 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases hn : 8 ≤ n
  · simp only [nsmul_eq_mul,if_pos (show 1 ≤ n by omega),
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
      value]
    by_cases parity : n%2=0
    · simp only [if_pos (show n%2=0 by omega),
        if_neg (show ¬ (n-1)%2=0 by omega),
        if_pos (show (n-2)%2=0 by omega),
        if_neg (show ¬ (n-3)%2=0 by omega),
        if_pos (show (n-4)%2=0 by omega),
        if_neg (show ¬ (n-5)%2=0 by omega),
        if_pos (show (n-6)%2=0 by omega),
        if_neg (show ¬ (n-7)%2=0 by omega),P0,P1]
      push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_sub (by omega : 5 ≤ n), Nat.cast_sub (by omega : 6 ≤ n), Nat.cast_sub (by omega : 7 ≤ n)]
      ring
    · simp only [if_neg (show ¬ n%2=0 by omega),
        if_pos (show (n-1)%2=0 by omega),
        if_neg (show ¬ (n-2)%2=0 by omega),
        if_pos (show (n-3)%2=0 by omega),
        if_neg (show ¬ (n-4)%2=0 by omega),
        if_pos (show (n-5)%2=0 by omega),
        if_neg (show ¬ (n-6)%2=0 by omega),
        if_pos (show (n-7)%2=0 by omega),P0,P1]
      push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_sub (by omega : 5 ≤ n), Nat.cast_sub (by omega : 6 ≤ n), Nat.cast_sub (by omega : 7 ≤ n)]
      ring
  · interval_cases n <;> norm_num [value,P0,P1]

theorem result : type_of% @OMA.S_oeis_a246480.main := by
  refine ⟨generating,?_,?_⟩
  · intro n _ hp
    obtain ⟨k,hk⟩ := hp
    rw [value,if_pos (show n%2=0 by omega),P0]
    ring
  · intro n _ hp
    obtain ⟨k,hk⟩ := hp
    rw [value,if_neg (show ¬ n%2=0 by omega),P1]
    ring

end OMA.Pairs246480

theorem OMA.solution : type_of% @OMA.S_oeis_a246480.main := OMA.Pairs246480.result
