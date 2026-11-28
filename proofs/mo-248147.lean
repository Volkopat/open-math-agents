import OMAStatements.S_mo_248147

namespace OMA.S_mo_248147
open Finset
noncomputable section

private def block {k : ℕ} (a : Mask k) (j : Fin k) (b : Bool) : Count k :=
  AddMonoidAlgebra.single (if b then column a j else 0) 1

private theorem bits {k : ℕ} (a b : Mask k) :
    (∑ j, if b j then column a j else 0) = atom a b := by
  classical
  ext i l
  simp only [Finset.sum_apply]
  have h (j : Fin k) : (if b j then column a j else 0) i l =
      if j=l then (a i && b l).toNat else 0 := by
    by_cases e : j=l
    · subst j
      cases b l <;> simp [column]
    · cases b j <;> simp [column,e,Ne.symm e]
  simp [h,atom]

private theorem oneCoord {k : ℕ} (a : Mask k) :
    factor a = ∑ b : Mask k, AddMonoidAlgebra.single (atom a b) 1 := by
  classical
  have hs (j : Fin k) : 1 + AddMonoidAlgebra.single (column a j) 1 =
      ∑ b : Bool, block a j b := by
    simp [block,AddMonoidAlgebra.one_def,add_comm]
  simp only [factor,hs,Fintype.prod_sum,block,AddMonoidAlgebra.prod_single,Finset.prod_const_one,bits]

private theorem fixed {d k : ℕ} (a : Fin d → Mask k) :
    (∏ t, factor (a t)) =
      ∑ b : Fin d → Mask k, AddMonoidAlgebra.single (overlaps a b) 1 := by
  classical
  simp only [oneCoord,Fintype.prod_sum,AddMonoidAlgebra.prod_single,Finset.prod_const_one,overlaps]

private theorem joint (d k : ℕ) :
    ((∑ a : Mask k, factor a)^d) =
      ∑ z : Fin d → Mask k × Mask k, AddMonoidAlgebra.single
        (overlaps (fun t => (z t).1) (fun t => (z t).2)) 1 := by
  classical
  have h : (∑ a : Mask k, factor a) =
      ∑ z : Mask k × Mask k, (AddMonoidAlgebra.single (atom z.1 z.2) 1 : Count k) := by
    simp [Fintype.sum_prod_type,oneCoord]
  rw [h,Fintype.sum_pow]
  simp only [AddMonoidAlgebra.prod_single,Finset.prod_const_one,overlaps]

private theorem tally {k : ℕ} {T : Type*} [Fintype T] (v : T → Overlaps k)
    (f : ℕ → ℝ) (s : ℝ) : countAt (fun t => score f (v t)) s =
      push f (∑ t, AddMonoidAlgebra.single (v t) 1) s := by
  classical
  let L : Count k →+ AddMonoidAlgebra ℕ ℝ :=
    { toFun := AddMonoidAlgebra.mapDomain (score f)
      map_zero' := AddMonoidAlgebra.mapDomain_zero _
      map_add' := AddMonoidAlgebra.mapDomain_add _ }
  change _ = (L (∑ t, AddMonoidAlgebra.single (v t) 1)).coeff s
  rw [map_sum]
  simp [L,countAt,AddMonoidAlgebra.coeff_sum,Finsupp.single_apply,Finset.sum_boole]

end
end OMA.S_mo_248147

open OMA.S_mo_248147 in
theorem OMA.solution : type_of% @OMA.S_mo_248147.main := by
  intro d k f s
  constructor
  · intro a
    rw [fixed]
    exact tally _ _ _
  · rw [joint]
    exact tally _ _ _
