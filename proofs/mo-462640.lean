import OMAStatements.S_mo_462640
import Mathlib

open scoped TensorProduct

theorem OMA.solution : type_of% @OMA.S_mo_462640.main := by
  intro A B X rA rB rX f g hf hg
  let fs : A × B →+* X := f.comp (RingHom.fst A B)
  let gs : A × B →+* X := g.comp (RingHom.snd A B)
  let S := fs.eqLocus gs
  let C := ↥S
  let l : C →+* A := (RingHom.fst A B).comp S.subtype
  let r : C →+* B := (RingHom.snd A B).comp S.subtype
  have agree (c : C) : f (l c) = g (r c) := c.property
  let _ : Algebra C A := l.toAlgebra
  let _ : Algebra C B := r.toAlgebra
  let _ : Module C X := Module.compHom X (f.comp l)
  let L : A →ₗ[C] B →ₗ[C] X := LinearMap.mk₂ C (fun a b => f a * g b)
    (by intro a a' b; simp [add_mul])
    (by
      intro c a b
      change f (l c * a) * g b = f (l c) * (f a * g b)
      simp [mul_assoc])
    (by intro a b b'; simp [mul_add])
    (by
      intro c a b
      change f a * g (r c * b) = f (l c) * (f a * g b)
      rw [map_mul, ← agree c, ← mul_assoc, ← mul_assoc, ← map_mul, mul_comm a, map_mul])
  let p : A ⊗[C] B →ₗ[C] X := TensorProduct.lift L
  let i : A →+* A ⊗[C] B := Algebra.TensorProduct.includeLeftRingHom
  let j : B →+* A ⊗[C] B := Algebra.TensorProduct.includeRight.toRingHom
  have hp (a : A) (b : B) : p (a ⊗ₜ[C] b) = f a * g b := by
    rw [show p = TensorProduct.lift L from rfl, TensorProduct.lift.tmul]
    rfl
  have hi (a : A) : p (i a) = f a := by
    change p (a ⊗ₜ[C] (1 : B)) = f a
    simp [hp]
  have hj (b : B) : p (j b) = g b := by
    change p ((1 : A) ⊗ₜ[C] b) = g b
    simp [hp]
  refine ⟨A ⊗[C] B, inferInstance, i, j, ?_, ?_, fun a b => ⟨?_, ?_⟩⟩
  · intro a a' h
    apply hf
    simpa only [hi] using congrArg p h
  · intro b b' h
    apply hg
    simpa only [hj] using congrArg p h
  · intro h
    simpa only [hi, hj] using congrArg p h
  · intro h
    let c : C := ⟨(a, b), h⟩
    have ha : c • (1 : A) = a := by change a * 1 = a; simp
    have hb : c • (1 : B) = b := by change b * 1 = b; simp
    change a ⊗ₜ[C] (1 : B) = (1 : A) ⊗ₜ[C] b
    rw [← ha, ← hb]
    exact TensorProduct.smul_tmul c (1 : A) (1 : B)