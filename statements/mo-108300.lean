import Mathlib

/-! Source: https://mathoverflow.net/questions/108300 -/

open CategoryTheory

namespace OMA.S_mo_108300

/-- An inverse system of integer-graded rings with degree-preserving transition maps. -/
structure RalphGradedSystem (I : Type) [Preorder I] where
  obj : I → RingCat
  grade : (i : I) → ℤ → AddSubgroup (obj i)
  graded : ∀ i, GradedRing (grade i)
  map : ∀ ⦃i j : I⦄, i ≤ j → obj j →+* obj i
  map_refl : ∀ i, map (le_refl i) = RingHom.id (obj i)
  map_trans : ∀ ⦃i j k : I⦄ (h : i ≤ j) (g : j ≤ k),
    map (h.trans g) = (map h).comp (map g)
  map_grade : ∀ ⦃i j : I⦄ (h : i ≤ j) (d : ℤ) (x : obj j),
    x ∈ grade j d → map h x ∈ grade i d

/-- Compatible sections realize the inverse limit in rings. -/
def ralphLimit {I : Type} [Preorder I] (S : RalphGradedSystem I) :
    Subring (∀ i, S.obj i) where
  carrier := {x | ∀ (i j : I) (h : i ≤ j), S.map h (x j) = x i}
  zero_mem' := by intro i j h; exact map_zero _
  one_mem' := by intro i j h; exact map_one _
  add_mem' := by
    intro x y hx hy i j h
    change S.map h (x j + y j) = x i + y i
    rw [map_add, hx i j h, hy i j h]
  neg_mem' := by
    intro x hx i j h
    change S.map h (-x j) = -x i
    rw [map_neg, hx i j h]
  mul_mem' := by
    intro x y hx hy i j h
    change S.map h (x j * y j) = x i * y i
    rw [map_mul, hx i j h, hy i j h]

/-- The degree-d inverse limit is the additive subgroup of compatible homogeneous sections. -/
def ralphGradeLimit {I : Type} [Preorder I] (S : RalphGradedSystem I) (d : ℤ) :
    AddSubgroup (ralphLimit S) where
  carrier := {x | ∀ i, x.val i ∈ S.grade i d}
  zero_mem' := by intro i; exact (S.grade i d).zero_mem
  add_mem' := by intro x y hx hy i; exact (S.grade i d).add_mem (hx i) (hy i)
  neg_mem' := by intro x hx i; exact (S.grade i d).neg_mem (hx i)

/-- The multiplication induced on degreewise inverse limits. -/
def ralphGradeMul {I : Type} [Preorder I] (S : RalphGradedSystem I) {d e : ℤ}
    (x : ralphGradeLimit S d) (y : ralphGradeLimit S e) :
    ralphGradeLimit S (d + e) :=
  ⟨x.val * y.val, fun i => by
    letI := S.graded i
    exact SetLike.mul_mem_graded (x.property i) (y.property i)⟩

/-- Do the groups in each degree and their induced multiplications determine the ring limit? -/
theorem main :
    ∀ (I J : Type) [Preorder I] [Preorder J] [Nonempty I] [Nonempty J],
      Directed (· ≤ ·) (id : I → I) → Directed (· ≤ ·) (id : J → J) →
      ∀ (S : RalphGradedSystem I) (T : RalphGradedSystem J),
        (∃ E : ∀ d : ℤ, ralphGradeLimit S d ≃+ ralphGradeLimit T d,
          ∀ (d e : ℤ) (x : ralphGradeLimit S d) (y : ralphGradeLimit S e),
            E (d + e) (ralphGradeMul S x y) = ralphGradeMul T (E d x) (E e y)) →
        Nonempty ((ralphLimit S) ≃+* (ralphLimit T)) := by
  sorry

end OMA.S_mo_108300
