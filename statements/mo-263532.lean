import Mathlib

/-!
# Bounds for the sesquilinear forms of closed operators and their adjoints

Source: Piero D'Ancona, https://mathoverflow.net/questions/263532 (CC BY-SA 3.0).
Credit: @connoranderson.

We take the common domains of each pair as the natural dense subspaces in
the question. A diagonal weight n+1 acts on the first coordinate of each
two-dimensional block and sends it into either the first or the second
coordinate. These closed operators have mutually orthogonal outputs, yet
their adjoints violate every quadratic bound even on finitely supported
vectors. All operators and adjoints below are Mathlib linear partial maps.
-/

namespace OMA.S_mo_263532
open LinearPMap
abbrev I := ℕ × Fin 2
noncomputable abbrev H := lp (fun _ : I => ℂ) 2
abbrev Op := H →ₗ.[ℂ] H
def coord (d : Fin 2) (x : H) (i : I) : ℂ :=
  if i.2=d then ((i.1:ℂ)+1)*x (i.1,0) else 0
def graphAt (d : Fin 2) : Submodule ℂ (H × H) where
  carrier := {p | ∀ i,p.2 i=coord d p.1 i}
  zero_mem' := by intro i; simp [coord]
  add_mem' := by intro p q hp hq i; change p.2 i+q.2 i=coord d (p.1+q.1) i
                 rw [hp i,hq i]; by_cases hi : i.2=d <;> simp [coord,hi,mul_add]
  smul_mem' := by intro c p hp i; change c*p.2 i=coord d (c • p.1) i
                  rw [hp i]; by_cases hi : i.2=d <;> simp [coord,hi,mul_left_comm]
noncomputable def op (d : Fin 2) : Op := (graphAt d).toLinearPMap
def finiteSupport : Set H := {x | (Function.support (fun i => x i)).Finite}

theorem main :
    (∀ d, (op d).IsClosed ∧ Dense ((op d).domain : Set H)) ∧
    Dense (↑((op 0).domain ⊓ (op 1).domain) : Set H) ∧
    Dense (↑((op 0).adjoint.domain ⊓ (op 1).adjoint.domain) : Set H) ∧
    (∀ (x : (op 0).domain) (y : (op 1).domain), inner ℂ (op 0 x) (op 1 y)=0) ∧
    ∀ c : ℝ, ∃ y ∈ finiteSupport, ∃ (h0 : y∈(op 0).adjoint.domain) (h1 : y∈(op 1).adjoint.domain),
      c*‖y‖^2 < ‖inner ℂ ((op 0).adjoint ⟨y,h0⟩) ((op 1).adjoint ⟨y,h1⟩)‖ := by
  sorry
end OMA.S_mo_263532
