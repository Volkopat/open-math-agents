import OMAStatements.S_oeis_a385590
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

namespace OMA.S_oeis_a385590

open Finset

lemma fib_identity (t : ℕ) :
    (Nat.fib t : ℤ)*Nat.fib (t+2) - (Nat.fib (t+1):ℤ)^2 = ((t%2:ℕ):ℤ) - (((t+1)%2:ℕ):ℤ) := by
  induction t with
  | zero => decide
  | succ t ih =>
    have he : (t+1+1)%2 = t%2 := by omega
    rw [he,Nat.fib_add_two (n:=t+1)]
    simp only [Nat.cast_add]
    have hf : (Nat.fib (t+2):ℤ) = Nat.fib t + Nat.fib (t+1) := by exact_mod_cast Nat.fib_add_two (n:=t)
    simp only [hf] at ih ⊢
    linarith only [ih]

lemma start_step (t : ℕ) : start (t+1) = start t + Nat.fib (t+1)*Nat.fib (t+2) := by
  have hz : (Nat.fib (t+2):ℤ)^2 + (((t+1)%2:ℕ):ℤ) = (Nat.fib (t+1):ℤ)^2 + ((t%2:ℕ):ℤ) + (Nat.fib (t+1):ℤ)*Nat.fib (t+2) := by
    have h := fib_identity t
    have hf : (Nat.fib (t+2):ℤ) = Nat.fib t + Nat.fib (t+1) := by exact_mod_cast (Nat.fib_add_two (n:=t))
    simp only [hf] at h ⊢
    linarith only [h]
  unfold start
  exact_mod_cast hz

lemma canonical (a b u v : ℕ) (hb : 0<b) :
    ∃ r j, r<b ∧ a*u+b*v = a*r+b*j := by
  refine ⟨u%b,v+a*(u/b),Nat.mod_lt _ hb,?_⟩
  have h := congrArg (a*·) (Nat.mod_add_div u b)
  nlinarith only [h]

lemma canonical_unique {a b r s j k : ℕ} (hc : a.Coprime b) (hr : r<b) (hs : s<b)
    (h : a*r+b*j = a*s+b*k) : r=s ∧ j=k := by
  have he := congrArg (fun x => x%b) h
  have hm : a*r ≡ a*s [MOD b] := by simpa [Nat.ModEq,Nat.add_mod] using he
  have h' := Nat.ModEq.cancel_left_of_coprime hc.symm hm
  have hrs : r=s := by simpa [Nat.ModEq,Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt hs] using h'
  subst s
  exact ⟨rfl,Nat.eq_of_mul_eq_mul_left (by omega : 0<b) (Nat.add_left_cancel h)⟩

def Tail (t v : ℕ) : Prop := ∃ u w, v = start t + Nat.fib t*u + Nat.fib (t+1)*w

lemma tail_next (t v : ℕ) : Tail (t+1) v ↔
    ∃ r j, r < Nat.fib (t+1) ∧ v = entry t r (width t r+j) := by
  have hb : 0 < Nat.fib (t+1) := Nat.fib_pos.mpr (by omega)
  constructor
  · rintro ⟨u,w,he⟩
    obtain ⟨r,j,hr,hj⟩ := canonical (Nat.fib (t+2)) (Nat.fib (t+1)) w u hb
    refine ⟨r,j,hr,?_⟩
    unfold entry width
    rw [he,start_step]
    change start t + Nat.fib (t+1)*Nat.fib (t+2)+Nat.fib (t+1)*u+Nat.fib (t+2)*w = _
    rw [Nat.fib_add_two (n:=t)] at hj ⊢
    nlinarith only [hj]
  · rintro ⟨r,j,_,he⟩
    refine ⟨j,r,?_⟩
    rw [he,start_step]
    unfold entry width
    change _ = start t + Nat.fib (t+1)*Nat.fib (t+2)+Nat.fib (t+1)*j+Nat.fib (t+2)*r
    rw [Nat.fib_add_two (n:=t)]
    ring

lemma tail_down {t v : ℕ} (h : Tail (t+1) v) : Tail t v := by
  obtain ⟨r,j,_,he⟩ := (tail_next t v).mp h
  exact ⟨r,width t r+j,he⟩

lemma tail_anti {i j v : ℕ} (h : i≤j) (hj : Tail j v) : Tail i v := by
  induction h with
  | refl => exact hj
  | step _ ih => exact ih (tail_down hj)

lemma cell_tail (x : Cell) : Tail x.block (value x) :=
  ⟨x.row,x.column,rfl⟩

lemma cell_not_next (x : Cell) : ¬ Tail (x.block+1) (value x) := by
  rintro h
  obtain ⟨r,j,hr,he⟩ := (tail_next _ _).mp h
  unfold value entry at he
  have he' := (Nat.add_left_cancel (n := start x.block)
    (by simpa [Nat.add_assoc] using he))
  obtain ⟨hh,hj⟩ := canonical_unique (Nat.fib_coprime_fib_succ x.block) x.row.isLt hr he'
  have hx := x.column.isLt
  rw [← hh] at hj
  omega

lemma choose_cell {t v : ℕ} (h : Tail t v) (hn : ¬Tail (t+1) v) :
    ∃ x : Cell, value x = v := by
  obtain ⟨u,w,he⟩ := h
  obtain ⟨r,j,hr,hj⟩ := canonical (Nat.fib t) (Nat.fib (t+1)) u w (Nat.fib_pos.mpr (by omega))
  have hentry : v = entry t r j := by unfold entry; rw [he]; omega
  have hbound : j < width t r := by
    by_contra! hg
    exact hn ((tail_next t v).mpr ⟨r,j-width t r,hr,by simpa [Nat.add_sub_of_le hg] using hentry⟩)
  exact ⟨⟨t,⟨r,hr⟩,⟨j,hbound⟩⟩,hentry.symm⟩

lemma covers (v : ℕ) (hv : 0<v) : ∃ x : Cell, value x=v := by
  have h0 : Tail 0 v := ⟨0,v-1,by simp [start]; omega⟩
  have hend : ¬Tail (v+5) v := by
    rintro ⟨u,w,he⟩
    have b := Nat.le_fib_self (n:=v+5+1) (by omega)
    have b' : Nat.fib (v+5+1) ≤ (Nat.fib (v+5+1))^2 := Nat.le_self_pow (by decide) _
    unfold start at he
    omega
  suffices ∀ t, ¬Tail t v → ∃ x : Cell, value x=v from this _ hend
  intro t
  induction t with
  | zero => intro h; exact (h h0).elim
  | succ t ih =>
    intro h
    by_cases ha : Tail t v
    · exact choose_cell ha h
    · exact ih ha

lemma value_injective : Function.Injective value := by
  intro x y he
  have hxy : x.block = y.block := by
    apply le_antisymm
    · by_contra! h
      exact cell_not_next y (tail_anti h (he ▸ cell_tail x))
    · by_contra! h
      exact cell_not_next x (tail_anti h (he.symm ▸ cell_tail y))
  obtain ⟨t,r,j⟩ := x
  obtain ⟨u,s,k⟩ := y
  change t=u at hxy
  subst u
  unfold value entry at he
  simp only at he
  rw [Nat.add_assoc, Nat.add_assoc] at he
  obtain ⟨hrs,hjk⟩ := canonical_unique (Nat.fib_coprime_fib_succ t) r.isLt s.isLt (Nat.add_left_cancel he)
  have h1 : r=s := Fin.ext hrs
  subst s
  have h2 : j=k := Fin.ext hjk
  subst k
  rfl

lemma weighted_alt (m : ℕ) (hm : 0<m) :
    (∑ j ∈ range (m+2), (-1:ℤ)^j * ((m+1).choose j : ℤ) * (j:ℤ)) = 0 := by
  rw [sum_range_succ']
  simp only [Nat.cast_zero,mul_zero,add_zero]
  calc
    _ = ∑ j ∈ range (m+1), -((m+1:ℕ):ℤ) * ((-1:ℤ)^j * (m.choose j:ℤ)) := by
      apply sum_congr rfl
      intro j _
      have h := congrArg (Nat.cast (R:=ℤ)) (Nat.add_one_mul_choose_eq m j)
      push_cast at h ⊢
      rw [pow_succ]
      linear_combination -((-1:ℤ)^j) * h.symm
    _ = 0 := by rw [← mul_sum,Int.alternating_sum_range_choose_of_ne (by omega : m ≠ 0),mul_zero]

lemma affine_alt (m : ℕ) (hm : 0<m) (A B : ℤ) :
    (∑ j ∈ range (m+2), (-1:ℤ)^(j+1) * ((m+1).choose j:ℤ) * (A+B*j))=0 := by
  calc
    _ = ∑ j ∈ range (m+2), ((-A)*((-1:ℤ)^j*((m+1).choose j:ℤ)) +
        (-B)*((-1:ℤ)^j*((m+1).choose j:ℤ)*(j:ℤ))) := by
      apply sum_congr rfl
      intro j _
      rw [pow_succ]
      ring
    _ = 0 := by
      rw [sum_add_distrib,← mul_sum,← mul_sum,weighted_alt m hm,
        Int.alternating_sum_range_choose_of_ne (by omega : m+1 ≠ 0)]
      ring

lemma row_identity (t r : ℕ) (hr : r < Nat.fib (t+1)) : rowSum t r =
    if width t r < 3 then (-1:ℤ)^(width t r) else 0 := by
  match t with
  | 0 =>
    have h : r=0 := by simpa using hr
    subst r
    decide
  | 1 =>
    have h : r=0 := by simpa using hr
    subst r
    decide
  | t+2 =>
    have h3 : 3 ≤ width (t+2) r := by
      have hf := Nat.fib_mono (by omega : 4 ≤ t+2+2)
      change 3 ≤ Nat.fib (t+2+2) at hf
      unfold width
      omega
    rw [if_neg (by omega)]
    let m := width (t+2) r - 2
    have hm : 0<m := by dsimp [m]; omega
    have hw : width (t+2) r=m+2 := by dsimp [m]; omega
    unfold rowSum
    rw [hw]
    rw [show m+2-1=m+1 by omega]
    convert affine_alt m hm ((start (t+2):ℤ)+(Nat.fib (t+2):ℤ)*r) (Nat.fib (t+2+1):ℤ) using 1
    apply sum_congr rfl
    intro j _
    unfold entry
    push_cast
    ring

theorem solution : ((∀ x : Cell, 0 < value x) ∧
    (∀ v : ℕ, 0 < v → ∃! x : Cell, value x = v)) ∧
    ∀ t r : ℕ, r < Nat.fib (t+1) → rowSum t r =
      if width t r < 3 then (-1 : ℤ)^(width t r) else 0 := by
  refine ⟨⟨?_,?_⟩,row_identity⟩
  · intro x
    have h : 0 < Nat.fib (x.block+1) := Nat.fib_pos.mpr (by omega)
    unfold value entry start
    positivity
  · intro v hv
    obtain ⟨x,hx⟩ := covers v hv
    exact ⟨x,hx,fun y hy => value_injective (hy.trans hx.symm)⟩

/-- Ordinary positive row and column numbers of the source triangle. -/
structure RowColumn where
  row : ℕ
  col : ℕ
  hcol : 0<col
  hbound : col≤row

lemma rowColumn_ext_val {x y : RowColumn} (hr : x.row=y.row) (hc : x.col=y.col) : x=y := by
  cases x
  cases y
  congr

lemma row_block_exists (n : ℕ) : ∃ t : ℕ, n < Nat.fib (t+3) :=
  ⟨n+5,lt_of_lt_of_le (by omega) (Nat.le_fib_self (n:=n+5+3) (by omega))⟩

noncomputable def blockOf (n : ℕ) := Nat.find (row_block_exists n)

lemma block_interval {n : ℕ} (hn : 0<n) :
    Nat.fib (blockOf n+2) ≤ n ∧ n < Nat.fib (blockOf n+3) := by
  refine ⟨?_,Nat.find_spec (row_block_exists n)⟩
  by_cases h : blockOf n=0
  · simpa [h] using (show 1≤n by omega)
  · have hm : blockOf n-1 < blockOf n := by omega
    have h' := Nat.find_min (row_block_exists n) (m:=blockOf n-1) hm
    have he : blockOf n-1+3=blockOf n+2 := by omega
    simpa [he] using h'

lemma block_recover (t r : ℕ) (hr : r < Nat.fib (t+1)) : blockOf (width t r)=t := by
  have hw : 0<width t r := by
    have h : 0<Nat.fib (t+2) := Nat.fib_pos.mpr (by omega)
    unfold width;omega
  obtain ⟨hl,hu⟩ := block_interval hw
  have hb : width t r < Nat.fib (t+3) := by
    unfold width
    have hF : Nat.fib (t+3) = Nat.fib (t+1)+Nat.fib (t+2) := Nat.fib_add_two
    omega
  apply le_antisymm
  · exact Nat.find_min' (row_block_exists _) hb
  · by_contra! hh
    have hf := Nat.fib_mono (show blockOf (width t r)+3 ≤ t+2 by omega)
    have hw' : Nat.fib (t+2) ≤ width t r := Nat.le_add_right _ _
    omega

def ordinaryCell (x : Cell) : RowColumn :=
  ⟨width x.block x.row,x.column.val+1,Nat.succ_pos _,x.column.isLt⟩

noncomputable def blockCell (z : RowColumn) : Cell := by
  let t := blockOf z.row
  have hn : 0<z.row := lt_of_lt_of_le z.hcol z.hbound
  have h1 := (block_interval hn).1
  have h2 := (block_interval hn).2
  let r := z.row - Nat.fib (t+2)
  have hlow : Nat.fib (t+2) ≤ z.row := h1
  have hup : z.row < Nat.fib (t+1)+Nat.fib (t+2) := by
    simpa only [t,Nat.fib_add_two (n:=blockOf z.row+1)] using h2
  have hrow : r<Nat.fib (t+1) := by dsimp [r];omega
  have hw : width t r=z.row := by unfold width; dsimp [r];omega
  exact ⟨t,⟨r,hrow⟩,⟨z.col-1,by rw [hw];have := z.hcol;have := z.hbound;omega⟩⟩

lemma cell_ext_val {x y : Cell} (ht : x.block=y.block) (hr : x.row.val=y.row.val)
    (hj : x.column.val=y.column.val) : x=y := by
  obtain ⟨t,r,j⟩ := x
  obtain ⟨u,s,k⟩ := y
  change t=u at ht
  subst u
  have he : r=s := Fin.ext hr
  subst s
  have he : j=k := Fin.ext hj
  subst k
  rfl

noncomputable def ordinaryEquiv : Cell ≃ RowColumn where
  toFun := ordinaryCell
  invFun := blockCell
  left_inv := by
    rintro ⟨t,⟨r,hr⟩,⟨j,hj⟩⟩
    have ht := block_recover t r hr
    apply cell_ext_val
    · exact ht
    · change width t r - Nat.fib (blockOf (width t r)+2) = r
      rw [ht]
      simp [width]
    · rfl
  right_inv := by
    rintro ⟨n,j,hj,hjn⟩
    have h := (block_interval (lt_of_lt_of_le hj hjn)).1
    apply rowColumn_ext_val <;> (dsimp [ordinaryCell,blockCell,width] <;> omega)

noncomputable def originalEntry (z : RowColumn) : ℕ :=
  let t := blockOf z.row
  (Nat.fib (t+1))^2 + (1-(t+1)%2) +
    (z.row-Nat.fib (t+2))*Nat.fib t + (z.col-1)*Nat.fib (t+1)

lemma originalEntry_eq (z : RowColumn) : originalEntry z = value (blockCell z) := by
  let t := blockOf z.row
  have he : 1-(t+1)%2=t%2 := by omega
  dsimp [originalEntry,value,blockCell,entry,start]
  simp only [t] at he
  rw [he]
  ring

theorem original_triangle_permutation (v : ℕ) (hv : 0<v) :
    ∃! z : RowColumn, originalEntry z=v := by
  obtain ⟨x,hx,hu⟩ := solution.1.2 v hv
  refine ⟨ordinaryEquiv x,?_,?_⟩
  · change originalEntry (ordinaryEquiv x) = v
    rw [originalEntry_eq]
    change value (ordinaryEquiv.symm (ordinaryEquiv x)) = v
    simpa using hx
  · intro y hy
    change originalEntry y=v at hy
    rw [originalEntry_eq] at hy
    exact (ordinaryEquiv.symm_apply_eq.mp (hu _ hy))

end OMA.S_oeis_a385590

theorem OMA.solution : type_of% @OMA.S_oeis_a385590.main :=
  OMA.S_oeis_a385590.solution
