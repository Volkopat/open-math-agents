import OMAStatements.S_mo_355011

-- uses note #105444
-- Complete companion proof by @connoranderson, published in statement PR #22988.
-- Source commit ced2ffbdf7aaa56b2da9bcc38e90b11a674eed1b, 2026-11-28.
-- Rechecked and assembled for the registered statement, with no novelty claim.

/-!
Proof of Johann Cigler’s characteristic-polynomial conjecture,
https://mathoverflow.net/questions/355011 .

The two reflected residues a and h−1−a form one path when distinct. Its two
halves are the stride-h chains, joined at their initial vertices. A fixed
residue instead contributes a path with a single loop. The determinant is
the product of the continuants of these components. Counting the residue
classes in the final partial row yields the four formulas.

Credit: @connoranderson
-/

namespace OMA.S_mo_355011
open Polynomial Matrix

private noncomputable def tr (n : ℕ) (c : ℤ[X]) : Matrix (Fin n) (Fin n) ℤ[X] :=
  fun i j => if i.val=j.val then (if i.val=0 then c else X)
    else if i.val+1=j.val ∨ j.val+1=i.val then -1 else 0

private lemma tr_tail (n : ℕ) (c : ℤ[X]) :
    (tr (n+1) c).submatrix Fin.succ Fin.succ = tr n X := by
  ext i j
  simp [tr, Fin.val_succ, Matrix.submatrix_apply]

private lemma tr_step (n : ℕ) (c : ℤ[X]) :
    (tr (n+2) c).det = c*(tr (n+1) X).det-(tr n X).det := by
  have hrow (j : Fin n) : tr (n+2) c 0 j.succ.succ = 0 := by
    simp [tr,Fin.val_succ]
  let M := (tr (n+2) c).submatrix Fin.succ (1 : Fin (n+2)).succAbove
  have hcol (i : Fin n) : M i.succ 0 = 0 := by
    simp [M,tr,Fin.val_succ]
  have hM0 : M 0 0 = -1 := by simp [M,tr]
  have hMtail : M.submatrix Fin.succ Fin.succ = tr n X := by
    ext i j
    simp only [M,Matrix.submatrix_apply,Fin.one_succAbove_succ,Fin.val_succ,tr]
    simp
  have hM : M.det = -(tr n X).det := by
    rw [Matrix.det_succ_column_zero,Fin.sum_univ_succ]
    simp [hcol,hM0,hMtail]
  rw [Matrix.det_succ_row_zero,Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_mul,Fin.succAbove_zero,tr_tail,Fin.succ_zero_eq_one,
    Fin.val_one, pow_one,hrow,mul_zero,zero_mul,Finset.sum_const_zero,add_zero]
  change tr (n+2) c 0 0 * (tr (n+1) X).det +
      (-1)*tr (n+2) c 0 1 * M.det = _
  have h₀ : tr (n+2) c 0 0 = c := by simp [tr]
  have h₁ : tr (n+2) c 0 1 = -1 := by simp [tr]
  rw [hM,h₀,h₁]
  ring

private lemma tr_path (n : ℕ) : (tr n X).det = pathPoly n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [pathPoly]
  | one => simp [pathPoly,tr]
  | more n h₀ h₁ => rw [tr_step,h₀,h₁,pathPoly]

private lemma tr_loop (n : ℕ) : (tr n (X-1)).det = loopPoly n := by
  cases n with
  | zero => simp [loopPoly]
  | succ n =>
    cases n with
    | zero => simp [loopPoly,pathPoly,tr]
    | succ n => rw [tr_step,tr_path,tr_path,loopPoly,pathPoly]; ring

end OMA.S_mo_355011

namespace OMA.S_mo_355011
open Polynomial Matrix

private def lengthAt (h : ℕ) (L : ℕ → ℕ) (a : ℕ) :=
  if 2*a+1=h then L a else L a+L (h-1-a)

private def position (h : ℕ) (L : ℕ → ℕ) (a t : ℕ) : ℕ × ℕ :=
  if 2*a+1=h then (a,t)
  else if t<L a then (a,L a-1-t) else (h-1-a,t-L a)

private def adjacent (h : ℕ) (x y : ℕ × ℕ) : Prop :=
  (x.1=y.1 ∧ (x.2+1=y.2 ∨ y.2+1=x.2)) ∨ (x.2=0 ∧ y.2=0 ∧ x.1+y.1+1=h)

private lemma column_unique {h r s x y : ℕ} (hr : r<h) (hs : s<h) :
    h*x+r=h*y+s ↔ r=s ∧ x=y := by
  constructor
  · intro he
    have hm := congrArg (fun z => z%h) he
    simp only [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt hs] at hm
    refine ⟨hm,?_⟩
    rw [hm] at he
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0<h) (Nat.add_right_cancel he)
  · rintro ⟨rfl,rfl⟩; rfl

private lemma encoded_adjacent {h : ℕ} (x y : ℕ × ℕ) (hx : x.1<h) (hy : y.1<h) :
    (h*x.2+x.1+h=h*y.2+y.1 ∨ h*y.2+y.1+h=h*x.2+x.1 ∨
      h*x.2+x.1+(h*y.2+y.1)+1=h) ↔ adjacent h x y := by
  have hplus (r z : ℕ) : h*z+r+h=h*(z+1)+r := by ring
  rw [hplus,hplus,column_unique hx hy,column_unique hy hx]
  have href : h*x.2+x.1+(h*y.2+y.1)+1=h ↔ x.2=0 ∧ y.2=0 ∧ x.1+y.1+1=h := by
    constructor
    · intro hd
      have hx0 : x.2=0 := by
        by_contra hneg
        have := Nat.mul_le_mul_left h (show 1≤x.2 by omega)
        simp only [Nat.mul_one] at this
        omega
      have hy0 : y.2=0 := by
        by_contra hk
        have := Nat.mul_le_mul_left h (show 1≤y.2 by omega)
        simp only [Nat.mul_one] at this
        omega
      exact ⟨hx0,hy0,by simpa [hx0,hy0] using hd⟩
    · rintro ⟨ha,hb,hc⟩
      simpa [ha,hb] using hc
  rw [href]
  unfold adjacent
  grind

private lemma position_correct {h a t : ℕ} {L : ℕ → ℕ} (hb : 2*a+1≤h)
    (ht : t<lengthAt h L a) :
    (position h L a t).1 < h ∧ (position h L a t).2 < L (position h L a t).1 := by
  unfold position lengthAt at *
  split_ifs at * <;> simp_all <;> omega

private lemma position_same {h a t u : ℕ} {L : ℕ → ℕ} (hb : 2*a+1≤h)
    (_ht : t<lengthAt h L a) (_hu : u<lengthAt h L a) :
    position h L a t=position h L a u ↔ t=u := by
  unfold position lengthAt at *
  split_ifs at * <;> simp_all <;> omega

private lemma position_edge {h a t u : ℕ} {L : ℕ → ℕ} (hb : 2*a+1≤h)
    (_ht : t<lengthAt h L a) (_hu : u<lengthAt h L a) :
    adjacent h (position h L a t) (position h L a u) ↔
      t+1=u ∨ u+1=t ∨ (2*a+1=h ∧ t=0 ∧ u=0) := by
  unfold position lengthAt adjacent at *
  split_ifs at * <;> simp_all <;> omega

private lemma position_residue (h : ℕ) (L : ℕ → ℕ) (a t : ℕ) :
    (position h L a t).1=a ∨ (position h L a t).1=h-1-a := by
  unfold position
  split_ifs <;> simp

private lemma position_blocks {h a b t u : ℕ} {L : ℕ → ℕ}
    (ha : 2*a+1≤h) (hb : 2*b+1≤h) (hx :
      (position h L a t).1 = (position h L b u).1 ∨
      (position h L a t).1 + (position h L b u).1 + 1 = h) : a=b := by
  have := position_residue h L a t
  have := position_residue h L b u
  omega

private lemma position_surj {h r t : ℕ} (L : ℕ → ℕ) (hr : r<h) (ht : t<L r) :
    ∃ a u : ℕ, 2*a+1≤h ∧ u<lengthAt h L a ∧ position h L a u=(r,t) := by
  by_cases he : 2*r+1=h
  · exact ⟨r,t,he.le,by simpa [lengthAt,he] using ht,by simp [position,he]⟩
  by_cases hl : 2*r+1<h
  · refine ⟨r,L r-1-t,hl.le,?_,?_⟩
    · simp [lengthAt,he]; omega
    · simp [position,he,show L r-1-t<L r by omega]; omega
  · let a := h-1-r
    have hal : 2*a+1<h := by dsimp [a]; omega
    have hae : h-1-a=r := by dsimp [a]; omega
    refine ⟨a,L a+t,hal.le,?_,?_⟩ <;> simp [lengthAt,position,hal.ne,hae,ht]

end OMA.S_mo_355011

namespace OMA.S_mo_355011
open Matrix Polynomial

private abbrev Vtx (h : ℕ) (L : ℕ → ℕ) :=
  (a : Fin ((h+1)/2)) × Fin (lengthAt h L a.val)

private def point {h : ℕ} {L : ℕ → ℕ} (v : Vtx h L) := position h L v.1.val v.2.val

private lemma admissible {h : ℕ} (a : Fin ((h+1)/2)) : 2*a.val+1 ≤ h := by omega

private def encode {N h : ℕ} {L : ℕ → ℕ}
    (hL : ∀ r t : ℕ, r<h → (h*t+r<N ↔ t<L r)) (v : Vtx h L) : Fin N :=
  ⟨h*(point v).2 + (point v).1, by
    have hw := position_correct (admissible v.1) v.2.isLt
    exact (hL _ _ hw.1).mpr hw.2⟩

private lemma encode_bijective {N h : ℕ} {L : ℕ → ℕ} (hh : 0<h)
    (hL : ∀ r t : ℕ, r<h → (h*t+r<N ↔ t<L r)) : Function.Bijective (encode hL) := by
  constructor
  · rintro ⟨a,t⟩ ⟨b,u⟩ he
    have h₁ := position_correct (admissible a) t.isLt
    have h₂ := position_correct (admissible b) u.isLt
    obtain ⟨hcol,hrow⟩ := (column_unique h₁.1 h₂.1).mp (congrArg Fin.val he)
    have hab : a=b := Fin.ext (position_blocks (admissible a) (admissible b) (Or.inl hcol))
    subst b
    have htu : t=u := Fin.ext ((position_same (admissible a) t.isLt u.isLt).mp (Prod.ext hcol hrow))
    subst u
    rfl
  · intro x
    have hr := Nat.mod_lt x.val hh
    have hcode := Nat.div_add_mod x.val h
    have ht := (hL _ _ hr).mp (by rw [hcode]; exact x.isLt : h*(x.val/h)+x.val%h<N)
    obtain ⟨a,u,ha,hu,he⟩ := position_surj L hr ht
    let v : Vtx h L := ⟨⟨a,by omega⟩,⟨u,hu⟩⟩
    refine ⟨v,Fin.ext ?_⟩
    change h*(position h L a u).2+(position h L a u).1=x.val
    simpa only [he] using hcode

private lemma det_sigma {b : ℕ} (L : Fin b → ℕ) (A : Matrix ((i : Fin b) × Fin (L i))
    ((i : Fin b) × Fin (L i)) ℤ[X]) (B : ∀ i, Matrix (Fin (L i)) (Fin (L i)) ℤ[X])
    (hoff : ∀ i j : (i : Fin b) × Fin (L i), i.1 ≠ j.1 → A i j=0)
    (hdiag : ∀ i x y, A ⟨i,x⟩ ⟨i,y⟩=B i x y) : A.det = ∏ i, (B i).det := by
  classical
  have ht : A.BlockTriangular Sigma.fst := fun _ _ h => hoff _ _ (ne_of_gt h)
  rw [ht.det_fintype]
  apply Finset.prod_congr rfl
  intro i _
  let e : Fin (L i) ≃ {v : (a : Fin b) × Fin (L a) // v.1=i} := {
    toFun x := ⟨⟨i,x⟩,rfl⟩
    invFun v := (v.property ▸ v.val.2)
    left_inv _ := rfl
    right_inv := by rintro ⟨⟨a,t⟩,rfl⟩; rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  apply Matrix.ext
  intro j k
  exact hdiag i j k

private lemma stride_charpoly {N h : ℕ} (L : ℕ → ℕ) (hh : 0<h)
    (hL : ∀ r t : ℕ, r<h → (h*t+r<N ↔ t<L r)) :
    (strideMatrix N h).charpoly =
      ∏ a : Fin ((h+1)/2), if 2*a.val+1=h then loopPoly (lengthAt h L a.val)
        else pathPoly (lengthAt h L a.val) := by
  classical
  let e := Equiv.ofBijective (encode hL) (encode_bijective hh hL)
  let A := (strideMatrix N h).charmatrix.submatrix e e
  let B (a : Fin ((h+1)/2)) := tr (lengthAt h L a.val) (if 2*a.val+1=h then X-1 else X)
  have entry (i j : Vtx h L) : strideMatrix N h (e i) (e j) =
      if adjacent h (point i) (point j) then 1 else 0 := by
    have hi := (position_correct (admissible i.1) i.2.isLt).1
    have hj := (position_correct (admissible j.1) j.2.isLt).1
    have ev (v : Vtx h L) : (e v).val=h*(point v).2+(point v).1 := rfl
    simp only [strideMatrix, ev,encoded_adjacent (point i) (point j) hi hj]
  have hdet : A.det=∏ i, (B i).det := by
    apply det_sigma
    · intro i j hij
      have hne : e i ≠ e j := fun he => hij (congrArg Sigma.fst (e.injective he))
      have hn : ¬ adjacent h (point i) (point j) := by
        intro h
        exact hij (Fin.ext (position_blocks (admissible _) (admissible _)
          (h.imp And.left (fun hh => hh.2.2))))
      change (strideMatrix N h).charmatrix (e i) (e j)=0
      rw [Matrix.charmatrix_apply_ne _ _ _ hne,entry,if_neg hn]
      simp
    · intro a x y
      have he := position_edge (admissible a) x.isLt y.isLt
      change (strideMatrix N h).charmatrix (e ⟨a,x⟩) (e ⟨a,y⟩)=_
      rw [Matrix.charmatrix_apply, Matrix.diagonal_apply,entry]
      change (if e ⟨a,x⟩ = e ⟨a,y⟩ then X else 0) -
        C (if adjacent h (position h L a.val x.val) (position h L a.val y.val) then 1 else 0) = _
      rw [he]
      have hinj : e ⟨a,x⟩=e ⟨a,y⟩ ↔ x.val=y.val := by simp [Fin.ext_iff]
      simp only [hinj]
      dsimp only [B,tr]
      split_ifs <;> simp_all
  change (strideMatrix N h).charmatrix.det=_
  rw [← Matrix.det_submatrix_equiv_self e,hdet]
  apply Finset.prod_congr rfl
  intro a _
  by_cases ha : 2*a.val+1=h
  · simp [B,ha,tr_loop]
  · simp [B,ha,tr_path]

end OMA.S_mo_355011

namespace OMA.S_mo_355011
open Polynomial Finset

private lemma cutoff_prod (m j : ℕ) (hj : j ≤ m) (A B : ℤ[X]) :
    (∏ i ∈ range m, if i<j then B else A) = A^(m-j)*B^j := by
  let f := fun i : ℕ => if i<j then B else A
  change ∏ i ∈ range m, f i = _
  have h₁ : ∏ i ∈ range j, f i = B^j := by
    exact (Finset.prod_congr rfl (fun i hi => if_pos (mem_range.mp hi))).trans (by simp)
  have h₂ : ∏ i ∈ range (m-j), f (j+i) = A^(m-j) := by simp [f]
  have hd := Finset.prod_range_add f j (m-j)
  rw [show j+(m-j)=m by omega,h₁,h₂] at hd
  rw [hd,mul_comm]

private lemma component_product {N m b k j S : ℕ} (L : ℕ → ℕ) (hb : b≤1)
    (hh : 0<2*m+b) (hj : j ≤ m)
    (hL : ∀ r t : ℕ, r<2*m+b → ((2*m+b)*t+r<N ↔ t<L r))
    (hs : ∀ a < m, lengthAt (2*m+b) L a = if a<j then S else 2*k)
    (hf : b=1 → lengthAt (2*m+b) L m=k) :
    (strideMatrix N (2*m+b)).charpoly =
      (if b=1 then loopPoly k else 1)*pathPoly (2*k)^(m-j)*pathPoly S^j := by
  let f := fun a : ℕ => if 2*a+1=2*m+b then loopPoly (lengthAt (2*m+b) L a)
    else pathPoly (lengthAt (2*m+b) L a)
  have hd := stride_charpoly L hh hL
  change _ = ∏ a : Fin ((2*m+b+1)/2), f a.val at hd
  rw [Fin.prod_univ_eq_prod_range] at hd
  have hc : ∏ i ∈ range m, f i = pathPoly (2*k)^(m-j)*pathPoly S^j := by
    rw [← cutoff_prod m j hj]
    apply Finset.prod_congr rfl
    intro i hi
    have him := mem_range.mp hi
    have hne : 2*i+1≠2*m+b := by omega
    simp only [f,if_neg hne,hs i him]
    split <;> rfl
  cases b with
  | zero =>
    rw [show (2*m+0+1)/2=m by omega, hc] at hd
    simpa using hd
  | succ b =>
    have hbo : b=0 := by omega
    subst b
    have hmid : f m = loopPoly k := by simp [f,hf rfl]
    rw [show (2*m+1+1)/2=m+1 by omega,Finset.prod_range_succ,hc,hmid] at hd
    simpa [mul_comm,mul_left_comm,mul_assoc] using hd

private lemma plus_col {h t r k j : ℕ} (hr : r<h) (hj : j≤h) :
    h*t+r<h*k+j ↔ t<k+(if r<j then 1 else 0) := by
  rcases lt_trichotomy t k with htk|rfl|hkt
  · have hd := Nat.mul_le_mul_left h (show t+1≤k by omega)
    rw [Nat.mul_add,Nat.mul_one] at hd
    split <;> omega
  · split <;> omega
  · have hd := Nat.mul_le_mul_left h (show k+1≤t by omega)
    rw [Nat.mul_add,Nat.mul_one] at hd
    split <;> omega

private lemma minus_col {h t r k j : ℕ} (hr : r<h) (hj : j≤h) :
    h*t+r<h*k-j ↔ t<k-(if h-j≤r then 1 else 0) := by
  cases k with
  | zero => simp
  | succ k =>
    rw [Nat.mul_succ,show h*k+h-j=h*k+(h-j) by omega,plus_col hr (Nat.sub_le h j)]
    split_ifs <;> omega

private lemma plus_formula {m b k j : ℕ} (hb : b≤1) (hh : 0<2*m+b) (hj : j ≤ m) :
    (strideMatrix ((2*m+b)*k+j) (2*m+b)).charpoly =
      (if b=1 then loopPoly k else 1)*pathPoly (2*k)^(m-j)*pathPoly (2*k+1)^j := by
  apply component_product (fun r => k+(if r<j then 1 else 0)) hb hh hj
  · intro r t hr
    exact plus_col hr (by omega)
  · intro a ha
    simp only [lengthAt]
    split_ifs <;> omega
  · intro h
    subst b
    simp [lengthAt,show ¬m<j by omega]

private lemma minus_formula {m b k j : ℕ} (hb : b≤1) (hh : 0<2*m+b) (hj : j ≤ m) :
    (strideMatrix ((2*m+b)*k-j) (2*m+b)).charpoly =
      (if b=1 then loopPoly k else 1)*pathPoly (2*k)^(m-j)*pathPoly (2*k-1)^j := by
  apply component_product (fun r => k-(if 2*m+b-j≤r then 1 else 0)) hb hh hj
  · intro r t hr
    exact minus_col hr (by omega)
  · intro a ha
    simp only [lengthAt]
    split_ifs <;> omega
  · intro h
    subst b
    simp [lengthAt,show ¬2*m+1-j≤ m by omega]

end OMA.S_mo_355011

theorem OMA.solution : type_of% @OMA.S_mo_355011.main := by
  intro m k j hj
  have empty (N h : ℕ) (hN : N=0) : (OMA.S_mo_355011.strideMatrix N h).charpoly=1 := by
    subst N
    exact Matrix.det_isEmpty
  have hplus := @OMA.S_mo_355011.plus_formula m 1 k j (by decide) (by omega) hj
  have hminus := @OMA.S_mo_355011.minus_formula m 1 k j (by decide) (by omega) hj
  refine ⟨?_,fun _ => ?_,by simpa using hplus,fun _ => by simpa using hminus⟩
  · by_cases hm : m=0
    · subst m
      obtain rfl : j=0 := by omega
      rw [empty _ _ (by simp)]
      simp
    · simpa using @OMA.S_mo_355011.plus_formula m 0 k j (by decide) (by omega) hj
  · by_cases hm : m=0
    · subst m
      obtain rfl : j=0 := by omega
      rw [empty _ _ (by simp)]
      simp
    · simpa using @OMA.S_mo_355011.minus_formula m 0 k j (by decide) (by omega) hj
