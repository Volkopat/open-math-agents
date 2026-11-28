import Mathlib

/-!
# Blatter–Specker theorem for ternary relations

Open Problem Garden: https://www.openproblemgarden.org/op/blatter_specker_theorem_for_ternary_relations
For a class `C` of finite structures let `f_C(n)` be the number of structures in `C` on the
labelled set `{0, …, n-1}`. Blatter and Specker proved that for every class definable in
monadic second-order logic (MSO) with unary and binary relation symbols, `f_C(n) mod m` is
ultimately periodic for every `m`. Question: does this hold for ternary relations? (Fischer
showed that it fails for a quaternary relation.) `main` states the affirmative answer for
one ternary relation symbol.

Conventions. `MSO` formulas over one ternary symbol `R` use first-order variables and
monadic (set) variables, both indexed by `ℕ`, atoms `x = y`, `R x y z`, `x ∈ X`, and
connectives `¬`, `∧`, `∃x`, `∃X`. A sentence is a formula evaluated under arbitrary
assignments; `f φ n` counts the relations `R ⊆ (Fin n)³` such that `(Fin n, R) ⊨ φ`
for the assignments sending all variables to `0` and all set variables to `∅` (for a
sentence the assignment is irrelevant; for `n = 0` there are no individuals and
first-order variables cannot be assigned, so the count starts at `n = 1`).
Ultimately periodic: there are `N` and `T > 0` with `f (n + T) ≡ f n (mod m)` for `n ≥ N`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_opg_blatter_specker_theorem_for_ternary_relations

/-- MSO formulas over one ternary relation symbol. -/
inductive MSO : Type
  | eq : ℕ → ℕ → MSO
  | rel : ℕ → ℕ → ℕ → MSO
  | mem : ℕ → ℕ → MSO
  | neg : MSO → MSO
  | conj : MSO → MSO → MSO
  | exFO : ℕ → MSO → MSO
  | exSO : ℕ → MSO → MSO

/-- Satisfaction in the structure `(Fin n, R)` under assignments `v` (individuals) and `V`
(sets). -/
def Sat {n : ℕ} (R : Fin n → Fin n → Fin n → Prop) :
    MSO → (ℕ → Fin n) → (ℕ → Set (Fin n)) → Prop
  | .eq x y, v, _ => v x = v y
  | .rel x y z, v, _ => R (v x) (v y) (v z)
  | .mem x X, v, V => v x ∈ V X
  | .neg φ, v, V => ¬ Sat R φ v V
  | .conj φ ψ, v, V => Sat R φ v V ∧ Sat R ψ v V
  | .exFO x φ, v, V => ∃ a : Fin n, Sat R φ (Function.update v x a) V
  | .exSO X φ, v, V => ∃ A : Set (Fin n), Sat R φ v (Function.update V X A)

/-- `φ` has no free variables: its truth value does not depend on the assignments. -/
def IsSentence (φ : MSO) : Prop :=
  ∀ (n : ℕ) (R : Fin n → Fin n → Fin n → Prop) (v w : ℕ → Fin n) (V W : ℕ → Set (Fin n)),
    (Sat R φ v V ↔ Sat R φ w W)

/-- The number of ternary relations on `Fin (n+1)` satisfying `φ`. -/
noncomputable def f (φ : MSO) (n : ℕ) : ℕ :=
  Set.ncard {R : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Prop |
    Sat R φ (fun _ => 0) (fun _ => ∅)}

theorem main :
    ∀ φ : MSO, IsSentence φ → ∀ m : ℕ, 1 ≤ m →
      ∃ N T : ℕ, 0 < T ∧ ∀ n ≥ N, f φ (n + T) ≡ f φ n [MOD m] := by
  sorry

end OMA.S_opg_blatter_specker_theorem_for_ternary_relations
