import OMAStatements.S_mo_487192

/-!
The existing complex square-zero counterexample. The Jacobson radical API
replaces the semisimple-module complement argument, and nilpotence gives the unit.
-/

namespace OMA.MO487192

-- A central square-zero element vanishes in a semisimple ring.
theorem central_square_zero {R : Type} [Ring R] [IsSemisimpleRing R]
    (x : R) (central : ∀ y : R, y * x = x * y) (hx : x * x = 0) : x = 0 := by
  have hj : x ∈ Ideal.jacobson (⊥ : Ideal R) := by
    apply Ideal.mem_jacobson_iff.mpr
    intro y
    refine ⟨1 - y * x, ?_⟩
    have hh : y * x * (y * x) = 0 := by
      rw [mul_assoc y x, ← mul_assoc x y, ← central y, mul_assoc y x, hx, mul_zero, mul_zero]
    change (1 - y * x) * y * x + (1 - y * x) - 1 = 0
    calc
      _ = -(y * x * (y * x)) := by noncomm_ring
      _ = 0 := by rw [hh, neg_zero]
  simpa only [Ideal.jacobson_bot, IsSemisimpleRing.jacobson_eq_bot, Submodule.mem_bot] using hj

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

def nilpotent : Mat := !![1, Complex.I; Complex.I, -1]

theorem nilpotent_transpose : nilpotent.transpose = nilpotent := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem nilpotent_sq : nilpotent * nilpotent = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nilpotent, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem nilpotent_ne_zero : nilpotent ≠ 0 := by
  intro h
  have he := congrArg (fun m : Mat => m 0 0) h
  norm_num [nilpotent] at he

end OMA.MO487192

open OMA.MO487192 OMA.S_mo_487192

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_487192.main) := by
  intro h
  let A : Mat := 1 + nilpotent
  have hA : IsUnit A := IsNilpotent.isUnit_one_add ⟨2, by simpa [pow_two] using nilpotent_sq⟩
  have hAt : A.transpose = A := by simp [A, nilpotent_transpose]
  let S := jointCentralizer ℂ A
  have hS : nilpotent ∈ S := by
    change nilpotent ∈ Subalgebra.centralizer ℂ ({A, A.transpose} : Set Mat)
    rw [Subalgebra.mem_centralizer_iff]
    intro B hB
    have hBA : B = A := by simpa [hAt] using hB
    subst B
    simp [A, add_mul, mul_add]
  let x : S := ⟨nilpotent, hS⟩
  have hxSq : x * x = 0 := Subtype.ext nilpotent_sq
  have hxCenter (y : S) : y * x = x * y := by
    apply Subtype.ext
    change (y : Mat) * nilpotent = nilpotent * (y : Mat)
    have hy : (y : Mat) ∈ Subalgebra.centralizer ℂ ({A, A.transpose} : Set Mat) := y.property
    have hyA := (Subalgebra.mem_centralizer_iff ℂ).mp hy A (by simp)
    dsimp only [A] at hyA
    rw [add_mul, mul_add, one_mul, mul_one] at hyA
    exact (add_left_cancel hyA).symm
  let : IsSemisimpleRing S := h.2.2 ℂ 2 (by decide) A hA
  have hxZero := central_square_zero x hxCenter hxSq
  exact nilpotent_ne_zero (congrArg Subtype.val hxZero)
