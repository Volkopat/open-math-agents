import Mathlib

namespace OMA.S_arxiv_2312_14661

open FirstOrder

/-- First-order signature corresponding to a hybrid propositional signature `(P, N)`:
binary accessibility relation `R`, unary predicates for propositional variables `P`,
and constants for nominals `N`. -/
def hybridLang (P N : Type) : FirstOrder.Language.{0, 0} where
  Functions
    | 0 => N
    | _ + 1 => PEmpty
  Relations
    | 1 => P
    | 2 => Unit
    | _ => PEmpty

/-- Binary accessibility relation `R` of a Kripke structure over `hybridLang P N`. -/
def accRel {P N M : Type} [(hybridLang P N).Structure M] (x y : M) : Prop :=
  FirstOrder.Language.Structure.RelMap (L := hybridLang P N) (n := 2) () ![x, y]

/-- Valuation of a propositional atom `p ∈ P` at world `x`. -/
def propVal {P N M : Type} [(hybridLang P N).Structure M] (p : P) (x : M) : Prop :=
  FirstOrder.Language.Structure.RelMap (L := hybridLang P N) (n := 1) p ![x]

/-- Denotation of a nominal `s ∈ N` in a Kripke structure. -/
def nomVal {P N M : Type} [(hybridLang P N).Structure M] (s : N) : M :=
  FirstOrder.Language.Structure.funMap (L := hybridLang P N) (n := 0) s Fin.elim0

/-- Subset of hybrid logic features `ℱ ⊆ {Nom, ↓, @, ∃}`. -/
structure HybridFeatures where
  hasNom : Bool
  hasBind : Bool
  hasJump : Bool
  hasExists : Bool
  deriving DecidableEq

/-- Hybrid logic formulas over signature `(P, N)` with `k` world variables in scope
(closed hybrid sentences have `k = 0`). -/
inductive HybridFormula (P N : Type) : ℕ → Type
  | bot {k : ℕ} : HybridFormula P N k
  | prop {k : ℕ} : P → HybridFormula P N k
  | nom {k : ℕ} : N → HybridFormula P N k
  | wvar {k : ℕ} : Fin k → HybridFormula P N k
  | neg {k : ℕ} : HybridFormula P N k → HybridFormula P N k
  | or {k : ℕ} : HybridFormula P N k → HybridFormula P N k → HybridFormula P N k
  | diam {k : ℕ} : HybridFormula P N k → HybridFormula P N k
  | bind {k : ℕ} : Fin k → HybridFormula P N k → HybridFormula P N k
  | bindExt {k : ℕ} : HybridFormula P N (k + 1) → HybridFormula P N k
  | jumpVar {k : ℕ} : Fin k → HybridFormula P N k → HybridFormula P N k
  | jumpNom {k : ℕ} : N → HybridFormula P N k → HybridFormula P N k
  | existsVar {k : ℕ} : Fin k → HybridFormula P N k → HybridFormula P N k
  | existsExt {k : ℕ} : HybridFormula P N (k + 1) → HybridFormula P N k

/-- Whether a hybrid formula belongs to the fragment determined by feature set `F`. -/
def UsesFeatures {P N : Type} (F : HybridFeatures) : ∀ {k : ℕ}, HybridFormula P N k → Prop
  | _, .bot => True
  | _, .prop _ => True
  | _, .nom _ => F.hasNom = true
  | _, .wvar _ => True
  | _, .neg φ => UsesFeatures F φ
  | _, .or φ ψ => UsesFeatures F φ ∧ UsesFeatures F ψ
  | _, .diam φ => UsesFeatures F φ
  | _, .bind _ φ => F.hasBind = true ∧ UsesFeatures F φ
  | _, .bindExt φ => F.hasBind = true ∧ UsesFeatures F φ
  | _, .jumpVar _ φ => F.hasJump = true ∧ UsesFeatures F φ
  | _, .jumpNom _ φ => F.hasJump = true ∧ F.hasNom = true ∧ UsesFeatures F φ
  | _, .existsVar _ φ => F.hasExists = true ∧ UsesFeatures F φ
  | _, .existsExt φ => F.hasExists = true ∧ UsesFeatures F φ

/-- Kripke semantics `M, ms, m ⊩ φ` for hybrid formulas with `k` world variables `ms : Fin k → M`
evaluated at current world `m : M`. -/
def HybridSat {P N M : Type} [(hybridLang P N).Structure M] :
    ∀ {k : ℕ}, (Fin k → M) → M → HybridFormula P N k → Prop
  | _, _, _, .bot => False
  | _, _, m, .prop p => propVal (P := P) (N := N) p m
  | _, _, m, .nom s => m = nomVal (P := P) (N := N) s
  | _, ms, m, .wvar j => m = ms j
  | _, ms, m, .neg φ => ¬ HybridSat ms m φ
  | _, ms, m, .or φ ψ => HybridSat ms m φ ∨ HybridSat ms m ψ
  | _, ms, m, .diam φ => ∃ m' : M, accRel (P := P) (N := N) m m' ∧ HybridSat ms m' φ
  | _, ms, m, .bind j φ => HybridSat (Function.update ms j m) m φ
  | _, ms, m, .bindExt φ => HybridSat (Fin.snoc ms m) m φ
  | _, ms, _, .jumpVar j φ => HybridSat ms (ms j) φ
  | _, ms, _, .jumpNom s φ => HybridSat ms (nomVal (P := P) (N := N) s) φ
  | _, ms, m, .existsVar j φ => ∃ n : M, HybridSat (Function.update ms j n) m φ
  | _, ms, m, .existsExt φ => ∃ n : M, HybridSat (Fin.snoc ms n) m φ

/-- Modular `F`-`ω`-bisimulation between Kripke structures `M` and `N'` (Definitions 3 and 4
of arXiv:2312.14661): a family of relations `B k` on `(M^k × M) × (N'^k × N')` satisfying
the base clauses `(prop)`, `(wvar)`, `(forth)`, `(back)` together with the clauses activated
by each feature in `F`. -/
structure IsFOmegaBisim {P N M M' : Type} [(hybridLang P N).Structure M]
    [(hybridLang P N).Structure M'] (F : HybridFeatures)
    (B : ∀ k : ℕ, (Fin k → M) → M → (Fin k → M') → M' → Prop) : Prop where
  prop : ∀ {k} {ms m ms' m'}, B k ms m ms' m' →
    ∀ p : P, propVal (P := P) (N := N) p m ↔ propVal (P := P) (N := N) p m'
  wvar : ∀ {k} {ms m ms' m'}, B k ms m ms' m' → ∀ j : Fin k, ms j = m ↔ ms' j = m'
  forth : ∀ {k} {ms m ms' m'}, B k ms m ms' m' →
    ∀ n : M, accRel (P := P) (N := N) m n → ∃ n' : M', accRel (P := P) (N := N) m' n' ∧ B k ms n ms' n'
  back : ∀ {k} {ms m ms' m'}, B k ms m ms' m' →
    ∀ n' : M', accRel (P := P) (N := N) m' n' → ∃ n : M, accRel (P := P) (N := N) m n ∧ B k ms n ms' n'
  nom : F.hasNom = true → ∀ {k} {ms m ms' m'}, B k ms m ms' m' →
    ∀ s : N, m = nomVal (P := P) (N := N) s ↔ m' = nomVal (P := P) (N := N) s
  ext : (F.hasBind = true ∨ F.hasExists = true) → ∀ {k} {ms m ms' m'}, B k ms m ms' m' →
    B (k + 1) (Fin.snoc ms m) m (Fin.snoc ms' m') m'
  bind : F.hasBind = true → ∀ {k} {ms m ms' m'}, B k ms m ms' m' →
    ∀ j : Fin k, B k (Function.update ms j m) m (Function.update ms' j m') m'
  atv : F.hasJump = true → ∀ {k} {ms m ms' m'}, B k ms m ms' m' →
    ∀ j : Fin k, B k ms (ms j) ms' (ms' j)
  atn : F.hasJump = true → F.hasNom = true → ∀ {k} {ms m ms' m'}, B k ms m ms' m' →
    ∀ s : N, B k ms (nomVal (P := P) (N := N) s) ms' (nomVal (P := P) (N := N) s)
  ex_forth : F.hasExists = true → ∀ {k} {ms m ms' m'}, B k ms m ms' m' →
    ∀ (j : Fin k) (a : M), ∃ a' : M', B k (Function.update ms j a) m (Function.update ms' j a') m'
  ex_back : F.hasExists = true → ∀ {k} {ms m ms' m'}, B k ms m ms' m' →
    ∀ (j : Fin k) (a' : M'), ∃ a : M, B k (Function.update ms j a) m (Function.update ms' j a') m'

/-- Pointed Kripke models `(M, m)` and `(M', m')` are `F`-`ω`-bisimilar. -/
def FOmegaBisimilar {P N M M' : Type} [(hybridLang P N).Structure M]
    [(hybridLang P N).Structure M'] (F : HybridFeatures) (m : M) (m' : M') : Prop :=
  ∃ B : ∀ k : ℕ, (Fin k → M) → M → (Fin k → M') → M' → Prop,
    IsFOmegaBisim (P := P) (N := N) F B ∧ B 0 Fin.elim0 m Fin.elim0 m'

/-- Invariance of a one-variable first-order formula `φ(x)` over `hybridLang P N` under
`F`-`ω`-bisimulations between pointed Kripke models. -/
def IsFOmegaBisimInvariant {P N : Type} (F : HybridFeatures)
    (φ : (hybridLang P N).Formula (Fin 1)) : Prop :=
  ∀ (M M' : Type) [(hybridLang P N).Structure M] [(hybridLang P N).Structure M']
    (m : M) (m' : M'),
    FOmegaBisimilar (P := P) (N := N) F m m' → (φ.Realize ![m] ↔ φ.Realize ![m'])

/-- Generic modular bisimulation characterization theorem for all standard fragments of hybrid
logic (Theorem 2 of arXiv:2312.14661, settling the open `{↓, Nom}` case of Hodkinson–Tahiri):
over any finite signature `(P, N)` and any feature set `F ⊆ {Nom, ↓, @, ∃}`, a first-order
formula `φ(x)` is equivalent to a closed hybrid `F`-sentence if and only if it is invariant
under `F`-`ω`-bisimulations. -/
theorem main :
    ∀ (P N : Type) [Fintype P] [Fintype N] (F : HybridFeatures)
      (φ : (hybridLang P N).Formula (Fin 1)),
      (∃ ψ : HybridFormula P N 0, UsesFeatures F ψ ∧
        ∀ (M : Type) [(hybridLang P N).Structure M] (m : M),
          φ.Realize ![m] ↔ HybridSat Fin.elim0 m ψ) ↔
      IsFOmegaBisimInvariant F φ := by sorry

end OMA.S_arxiv_2312_14661
