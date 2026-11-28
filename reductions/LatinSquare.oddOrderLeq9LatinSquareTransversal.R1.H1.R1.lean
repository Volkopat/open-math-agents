import OMAReductions.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1
import Mathlib

/-! McKay, McLeod and Wanless, *The number of transversals in a Latin
square* (2006), Table 2. At order nine an arbitrary pair of rows
determines a derangement on nine columns. Relabelling columns and symbols
puts this derangement into one of eight cycle forms. Normalizing the first
column again preserves the marked row and transports transversals back.
The order-seven case has its own finite enumeration. -/
namespace OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1
open LatinSquare

/-- The order-seven transversal theorem. -/
def H1 : Prop := ∀ L : LatinSquare 7, ∃ σ, IsTransversal L σ

/-- At order nine, check reduced squares with one specified canonical row. -/
def H2 : Prop := ∀ (L : LatinSquare 9), (∀ j, L.mat 0 j=j) → (∀ i, L.mat i 0=i) →
  ∀ a : Fin 9, a≠0 → (∃ i : Fin 8, ∀ j, L.mat a j =
    (![![1, 2, 3, 4, 5, 6, 7, 8, 0],
    ![1, 2, 3, 4, 5, 6, 0, 8, 7],
    ![1, 2, 3, 4, 5, 0, 7, 8, 6],
    ![1, 2, 3, 4, 0, 6, 7, 8, 5],
    ![1, 2, 3, 4, 0, 6, 5, 8, 7],
    ![1, 2, 3, 0, 5, 6, 4, 8, 7],
    ![1, 2, 0, 4, 5, 3, 7, 8, 6],
    ![1, 2, 0, 4, 3, 6, 5, 8, 7]] : Fin 8 → Fin 9 → Fin 9) i j) → ∃ σ, IsTransversal L σ

theorem fourSlots (m : Multiset ℕ) (total : m.sum = 9) (large : ∀ x∈m, 2≤x)
    (kinds : Fin 8 → Multiset ℕ)
    (check : ∀ a b c d : Fin 10, a.val≠1 → b.val≠1 → c.val≠1 → d.val≠1 →
      a.val+b.val+c.val+d.val=9 →
      ∃ i, (([a.val,b.val,c.val,d.val].filter (· != 0) : List ℕ) : Multiset ℕ) = kinds i) :
    ∃ i, m = kinds i := by
  have weight (q : Multiset ℕ) (h : ∀ x∈q, 2≤x) : 2*q.card≤q.sum := by
    induction q using Multiset.induction_on with
    | empty => simp
    | cons x xs ih =>
      have a := h x (by simp)
      have b := ih (fun y hy => h y (by simp [hy]))
      simp only [Multiset.card_cons,Multiset.sum_cons]
      omega
  have len : m.card≤4 := by have := weight m large; omega
  let q := m.toList ++ List.replicate (4-m.card) 0
  have len4 : q.length=4 := by simp [q]; omega
  have sum4 : q.sum=9 := by simpa [q] using total
  have non (x) (hx : x∈q) : x≠1 := by
    rcases List.mem_append.mp hx with h | h
    · have e := large x (by simpa using h)
      omega
    · have := (List.mem_replicate.mp h).2
      omega
  have keep : q.filter (· != 0) = m.toList := by
    have h : m.toList.filter (· != 0) = m.toList := by
      apply List.filter_eq_self.mpr
      intro x hx
      have e := large x (by simpa using hx)
      simpa using (by omega : x ≠ 0)
    simp [q,List.filter_append,h]
  have fields (xs : List ℕ) (hlen : xs.length=4) : ∃ a b c d, xs=[a,b,c,d] := by
    match xs with
    | [a,b,c,d] => exact ⟨a,b,c,d,rfl⟩
    | [] | [_] | [_,_] | [_,_,_] | _::_::_::_::_::_ => simp_all
  obtain ⟨a,b,c,d,shape⟩ := fields q len4
  rw [shape] at sum4 non keep
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at sum4
  have h := check ⟨a,by omega⟩ ⟨b,by omega⟩ ⟨c,by omega⟩ ⟨d,by omega⟩
    (non a (by simp)) (non b (by simp)) (non c (by simp)) (non d (by simp))
    (by change a+b+c+d=9; omega)
  obtain ⟨i,h⟩ := h
  exact ⟨i,by simpa only [keep,Multiset.coe_toList] using h⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem orderNine (nine : H2) (L : LatinSquare 9) (first : ∀ j, L.mat 0 j=j) :
    ∃ σ, IsTransversal L σ := by
  let rows : Fin 8 → Fin 9 → Fin 9 := ![![1, 2, 3, 4, 5, 6, 7, 8, 0],
    ![1, 2, 3, 4, 5, 6, 0, 8, 7],
    ![1, 2, 3, 4, 5, 0, 7, 8, 6],
    ![1, 2, 3, 4, 0, 6, 7, 8, 5],
    ![1, 2, 3, 4, 0, 6, 5, 8, 7],
    ![1, 2, 3, 0, 5, 6, 4, 8, 7],
    ![1, 2, 0, 4, 5, 3, 7, 8, 6],
    ![1, 2, 0, 4, 3, 6, 5, 8, 7]]
  let inv : Fin 8 → Fin 9 → Fin 9 := ![![8, 0, 1, 2, 3, 4, 5, 6, 7],
    ![6, 0, 1, 2, 3, 4, 5, 8, 7],
    ![5, 0, 1, 2, 3, 4, 8, 6, 7],
    ![4, 0, 1, 2, 3, 8, 5, 6, 7],
    ![4, 0, 1, 2, 3, 6, 5, 8, 7],
    ![3, 0, 1, 2, 6, 4, 5, 8, 7],
    ![2, 0, 1, 5, 3, 4, 8, 6, 7],
    ![2, 0, 1, 4, 3, 6, 5, 8, 7]]
  let kinds : Fin 8 → Multiset ℕ := ![({9} : Multiset ℕ), ({7, 2} : Multiset ℕ), ({6, 3} : Multiset ℕ), ({5, 4} : Multiset ℕ), ({5, 2, 2} : Multiset ℕ), ({4, 3, 2} : Multiset ℕ), ({3, 3, 3} : Multiset ℕ), ({3, 2, 2, 2} : Multiset ℕ)]
  let left : ∀ i j, inv i (rows i j)=j := by decide
  let right : ∀ i j, rows i (inv i j)=j := by decide
  let perms (i : Fin 8) : Equiv.Perm (Fin 9) := ⟨rows i, inv i, left i, right i⟩
  have ct : ∀ i, (perms i).cycleType = kinds i := by decide +kernel
  have partCheck : ∀ a b c d : Fin 10, a.val≠1 → b.val≠1 → c.val≠1 → d.val≠1 →
      a.val+b.val+c.val+d.val=9 →
      ∃ i, (([a.val,b.val,c.val,d.val].filter (· != 0) : List ℕ) : Multiset ℕ) = kinds i := by decide +kernel
  let f : Equiv.Perm (Fin 9) := Equiv.ofBijective (L.mat 1)
    ⟨L.row_injective 1,Finite.surjective_of_injective (L.row_injective 1)⟩
  have fixed (j : Fin 9) : f j ≠ j := by
    intro h
    have eq : L.mat 1 j = L.mat 0 j := h.trans (first j).symm
    exact (by decide : (1 : Fin 9) ≠ 0) (L.col_injective j eq)
  have supp : f.support = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    exact Equiv.Perm.mem_support.mpr (fixed j)
  have total : f.cycleType.sum = 9 := by rw [f.sum_cycleType,supp]; simp
  obtain ⟨k,typeEq⟩ := fourSlots f.cycleType total (fun _ h =>
    Equiv.Perm.two_le_of_mem_cycleType h) kinds partCheck
  have conj : IsConj f (perms k) := Equiv.Perm.isConj_iff_cycleType_eq.mpr (typeEq.trans (ct k).symm)
  obtain ⟨e,he⟩ := isConj_iff.mp conj
  let old0 := e.symm 0
  let row : Fin 9 ≃ Fin 9 := Equiv.ofBijective (fun i => e (L.mat i old0))
    ⟨e.injective.comp (L.col_injective old0),
      Finite.surjective_of_injective (e.injective.comp (L.col_injective old0))⟩
  let M : LatinSquare 9 := {
    mat := fun i j => e (L.mat (row.symm i) (e.symm j))
    row_injective := fun i => e.injective.comp ((L.row_injective (row.symm i)).comp e.symm.injective)
    col_injective := fun j => e.injective.comp ((L.col_injective (e.symm j)).comp row.symm.injective) }
  have r0 : row 0=0 := by
    change e (L.mat 0 (e.symm 0))=0
    rw [first,e.apply_symm_apply]
  have top (j : Fin 9) : M.mat 0 j=j := by
    change e (L.mat (row.symm 0) (e.symm j))=j
    rw [show row.symm 0=0 from row.symm_apply_eq.mpr r0.symm,first,e.apply_symm_apply]
  have side (i : Fin 9) : M.mat i 0=i := row.apply_symm_apply i
  have nonzero : row 1 ≠ 0 := fun h => (by decide : (1 : Fin 9) ≠ 0)
    (row.injective (h.trans r0.symm))
  have marked (j : Fin 9) : M.mat (row 1) j = rows k j := by
    change e (L.mat (row.symm (row 1)) (e.symm j)) = rows k j
    rw [row.symm_apply_apply]
    exact DFunLike.congr_fun he j
  obtain ⟨g,cols,syms⟩ := nine M top side (row 1) nonzero ⟨k,marked⟩
  refine ⟨fun i => e.symm (g (row i)),e.symm.injective.comp (cols.comp row.injective),?_⟩
  intro i j eq
  have h : M.mat (row i) (g (row i)) = M.mat (row j) (g (row j)) := by
    change e (L.mat (row.symm (row i)) _) = e (L.mat (row.symm (row j)) _)
    rw [row.symm_apply_apply,row.symm_apply_apply]
    exact congrArg e eq
  exact row.injective (syms h)

theorem main : H1 → H2 → OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1.H1 := by
  intro seven nine n inst hn L first _
  have cases : n=7 ∨ n=9 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hn
  rcases cases with rfl | rfl
  · exact seven L
  · exact orderNine nine L first

end OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1
