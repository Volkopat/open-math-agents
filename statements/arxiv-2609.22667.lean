import Mathlib

namespace OMA.S_arxiv_2609_22667

/-- The six-element carrier of the common commutative multiplicative semigroup `M`
of `SR₆` and `TR₆` (Wang–Wu–Wang, Section 2). -/
inductive Elem6 where
  | zero | c | p | q | a | b
  deriving DecidableEq

instance : Fintype Elem6 where
  elems := {.zero, .c, .p, .q, .a, .b}
  complete := fun x => by cases x <;> decide

/-- The common commutative multiplication on `M`: the only nonzero products are
`p*b = b*p = a*b = b*a = a*q = q*a = c` (graph `p -- b -- a -- q`). -/
def mulM : Elem6 → Elem6 → Elem6
  | .p, .b => .c
  | .b, .p => .c
  | .a, .b => .c
  | .b, .a => .c
  | .a, .q => .c
  | .q, .a => .c
  | _, _ => .zero

/-- A binary operation `+` on `Elem6` is a compatible ai-semiring addition on `M`
iff `(Elem6, +)` is a commutative idempotent semigroup distributing over `mulM`. -/
def IsCompatAdd (add : Elem6 → Elem6 → Elem6) : Prop :=
  (∀ x y z, add (add x y) z = add x (add y z)) ∧
  (∀ x y, add x y = add y x) ∧
  (∀ x, add x x = x) ∧
  (∀ x y z, mulM x (add y z) = add (mulM x y) (mulM x z)) ∧
  (∀ x y z, mulM (add x y) z = add (mulM x z) (mulM y z))

/-- Elements below `c` in `R_{ij}` (`i, j ∈ {0, 1, 2}`): the first `i` elements of
`a < p` and the first `j` elements of `b < q`, plus `c` itself. -/
def belowC (i j : Fin 3) : Elem6 → Bool
  | .c => true
  | .a => decide (1 ≤ i.val)
  | .p => decide (2 ≤ i.val)
  | .b => decide (1 ≤ j.val)
  | .q => decide (2 ≤ j.val)
  | .zero => false

/-- The nine canonical compatible additions `R_{ij}` (`0 ≤ i, j ≤ 2`) on `M`. -/
def addR (i j : Fin 3) (x y : Elem6) : Elem6 :=
  if x = y then x
  else if x = .zero ∨ y = .zero then .zero
  else if (x = .a ∧ y = .p) ∨ (x = .p ∧ y = .a) then .p
  else if (x = .b ∧ y = .q) ∨ (x = .q ∧ y = .b) then .q
  else if belowC i j x && belowC i j y then .c
  else .zero

/-- Semiring isomorphism between two compatible additions on `M`. -/
def AddIso (add₁ add₂ : Elem6 → Elem6 → Elem6) : Prop :=
  ∃ e : Elem6 ≃ Elem6,
    (∀ x y, e (mulM x y) = mulM (e x) (e y)) ∧
    (∀ x y, e (add₁ x y) = add₂ (e x) (e y))

/-- Terms in the constant-free semiring signature `(+, ·)`. -/
inductive SemiringTerm where
  | var : ℕ → SemiringTerm
  | add : SemiringTerm → SemiringTerm → SemiringTerm
  | mul : SemiringTerm → SemiringTerm → SemiringTerm
  deriving DecidableEq

/-- Evaluation of a semiring term in `R_{ij}`. -/
def SemiringTerm.eval (i j : Fin 3) (v : ℕ → Elem6) : SemiringTerm → Elem6
  | .var n => v n
  | .add s t => addR i j (s.eval i j v) (t.eval i j v)
  | .mul s t => mulM (s.eval i j v) (t.eval i j v)

/-- Substitution of terms for variables. -/
def SemiringTerm.subst (σ : ℕ → SemiringTerm) : SemiringTerm → SemiringTerm
  | .var n => σ n
  | .add s t => .add (s.subst σ) (t.subst σ)
  | .mul s t => .mul (s.subst σ) (t.subst σ)

/-- Satisfaction of an identity `s ≈ t` in `R_{ij}`. -/
def SatisfiesId (i j : Fin 3) (s t : SemiringTerm) : Prop :=
  ∀ v : ℕ → Elem6, s.eval i j v = t.eval i j v

/-- Equational derivability relative to the variety of commutative ai-semirings. -/
inductive EqDerives (Ax : Set (SemiringTerm × SemiringTerm)) : SemiringTerm → SemiringTerm → Prop where
  | ax {s t : SemiringTerm} : (s, t) ∈ Ax → EqDerives Ax s t
  | add_assoc (a b c : SemiringTerm) : EqDerives Ax (.add (.add a b) c) (.add a (.add b c))
  | add_comm (a b : SemiringTerm) : EqDerives Ax (.add a b) (.add b a)
  | add_idem (a : SemiringTerm) : EqDerives Ax (.add a a) a
  | mul_assoc (a b c : SemiringTerm) : EqDerives Ax (.mul (.mul a b) c) (.mul a (.mul b c))
  | mul_comm (a b : SemiringTerm) : EqDerives Ax (.mul a b) (.mul b a)
  | left_distrib (a b c : SemiringTerm) : EqDerives Ax (.mul a (.add b c)) (.add (.mul a b) (.mul a c))
  | right_distrib (a b c : SemiringTerm) : EqDerives Ax (.mul (.add a b) c) (.add (.mul a c) (.mul b c))
  | refl (a : SemiringTerm) : EqDerives Ax a a
  | symm {a b : SemiringTerm} : EqDerives Ax a b → EqDerives Ax b a
  | trans {a b c : SemiringTerm} : EqDerives Ax a b → EqDerives Ax b c → EqDerives Ax a c
  | add_cong {a₁ a₂ b₁ b₂ : SemiringTerm} :
      EqDerives Ax a₁ a₂ → EqDerives Ax b₁ b₂ → EqDerives Ax (.add a₁ b₁) (.add a₂ b₂)
  | mul_cong {a₁ a₂ b₁ b₂ : SemiringTerm} :
      EqDerives Ax a₁ a₂ → EqDerives Ax b₁ b₂ → EqDerives Ax (.mul a₁ b₁) (.mul a₂ b₂)
  | subst {a b : SemiringTerm} (σ : ℕ → SemiringTerm) :
      EqDerives Ax a b → EqDerives Ax (a.subst σ) (b.subst σ)

/-- `Ax` is an equational basis for `R_{ij}` (relative to commutative ai-semirings). -/
def IsEquationalBasis (i j : Fin 3) (Ax : Set (SemiringTerm × SemiringTerm)) : Prop :=
  (∀ p ∈ Ax, SatisfiesId i j p.1 p.2) ∧
  (∀ s t : SemiringTerm, SatisfiesId i j s t → EqDerives Ax s t)

/-- `R_{ij}` is finitely based iff it admits a finite equational basis. -/
def IsFinitelyBased (i j : Fin 3) : Prop :=
  ∃ Ax : Finset (SemiringTerm × SemiringTerm), IsEquationalBasis i j (Ax : Set (SemiringTerm × SemiringTerm))

/-- Absorption identity `u ⪯ v`, i.e. `u + v ≈ v`. -/
def absId (u v : SemiringTerm) : SemiringTerm × SemiringTerm := (.add u v, v)

/-- Path term `x_0 x_1 + x_1 x_2 + ... + x_{k-1} x_k` for `k ≥ 1`. -/
def pathTerm : ℕ → SemiringTerm
  | 0 => .mul (.var 0) (.var 1)
  | n + 1 => .add (pathTerm n) (.mul (.var (n + 1)) (.var (n + 2)))

/-- Odd-cycle term `x_0 x_1 + x_1 x_2 + ... + x_{2n-1} x_{2n} + x_{2n} x_0` for `n ≥ 1`. -/
def oddCycleTerm (n : ℕ) : SemiringTerm :=
  .add (pathTerm (2 * n - 1)) (.mul (.var (2 * n)) (.var 0))

/-- Common base identities `Σ₀`: `x ⪯ y²`, `x² ≈ yzt`, and odd-cycle identities `σ_n` (`n ≥ 1`). -/
def Sigma0 : Set (SemiringTerm × SemiringTerm) :=
  { absId (.var 0) (.mul (.var 1) (.var 1)),
    (.mul (.var 0) (.var 0), .mul (.mul (.var 1) (.var 2)) (.var 3)) } ∪
  { p | ∃ n : ℕ, 1 ≤ n ∧ p = absId (.var (2 * n + 1)) (oddCycleTerm n) }

/-- Identity `ξ : x² ≈ x + y + xy`. -/
def idXi : SemiringTerm × SemiringTerm :=
  (.mul (.var 0) (.var 0), .add (.add (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))

/-- Identity `α : x_0 x_3 ⪯ x_0 + x_0 x_1 + x_1 x_2 + x_2 x_3`. -/
def idAlpha : SemiringTerm × SemiringTerm :=
  absId (.mul (.var 0) (.var 3)) (.add (.var 0) (pathTerm 2))

/-- Identity `β : x_0 x_2 ⪯ x_0 + x_0 x_1 + x_3 + x_3 x_2`. -/
def idBeta : SemiringTerm × SemiringTerm :=
  absId (.mul (.var 0) (.var 2))
    (.add (.add (.var 0) (.mul (.var 0) (.var 1))) (.add (.var 3) (.mul (.var 3) (.var 2))))

/-- Identity `η : x_2 ⪯ x_0 + x_0 x_1 + x_1 x_2`. -/
def idEta : SemiringTerm × SemiringTerm :=
  absId (.var 2) (.add (.var 0) (pathTerm 1))

/-- Identity `θ_n : x_0 x_{2n+1} ⪯ x_0 + x_{2n+1} + ∑_{j=0}^{2n} x_j x_{j+1}` (`n ≥ 1`). -/
def idTheta (n : ℕ) : SemiringTerm × SemiringTerm :=
  absId (.mul (.var 0) (.var (2 * n + 1)))
    (.add (.add (.var 0) (.var (2 * n + 1))) (pathTerm (2 * n)))

/-- Explicit infinite bases for `R_{01}, R_{02}, R_{11}, R_{12}` (Theorem 4.1). -/
def basis01 : Set (SemiringTerm × SemiringTerm) := Sigma0 ∪ {idXi, idAlpha, idBeta}
def basis02 : Set (SemiringTerm × SemiringTerm) := Sigma0 ∪ {idXi, idEta}
def basis11 : Set (SemiringTerm × SemiringTerm) := Sigma0 ∪ {idAlpha}
def basis12 : Set (SemiringTerm × SemiringTerm) := Sigma0 ∪ { p | ∃ n : ℕ, 1 ≤ n ∧ p = idTheta n }

/-- Main theorem (Wang–Wu–Wang, Theorems 2.1, 4.1, and 4.2):
1. Classification of compatible additions on `M`: there are exactly 9 labelled compatible additions
   `addR i j` (`i, j ∈ Fin 3`) and 6 isomorphism types (`R_{ij} ≅ R_{i'j'} ↔ {i, j} = {i', j'}`).
2. Complete explicit infinite equational bases for all four new semirings `R_{01}, R_{02}, R_{11}, R_{12}`.
3. None of `R_{01}, R_{02}, R_{11}, R_{12}` is finitely based. -/
theorem main :
    (∀ add : Elem6 → Elem6 → Elem6, IsCompatAdd add ↔ ∃ i j : Fin 3, add = addR i j) ∧
    (Function.Injective fun p : Fin 3 × Fin 3 => addR p.1 p.2) ∧
    (∀ i j i' j' : Fin 3, AddIso (addR i j) (addR i' j') ↔ (i = i' ∧ j = j') ∨ (i = j' ∧ j = i')) ∧
    IsEquationalBasis 0 1 basis01 ∧
    IsEquationalBasis 0 2 basis02 ∧
    IsEquationalBasis 1 1 basis11 ∧
    IsEquationalBasis 1 2 basis12 ∧
    ¬ IsFinitelyBased 0 1 ∧
    ¬ IsFinitelyBased 0 2 ∧
    ¬ IsFinitelyBased 1 1 ∧
    ¬ IsFinitelyBased 1 2 := by
  sorry

end OMA.S_arxiv_2609_22667
