import OMAReductions.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_realExp_of_realSchanuelConjecture_R1
import Mathlib.Computability.Primrec.List

/-!
# Effective first-order completeness and recursively enumerable proof search

We prove `OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_realExp_of_realSchanuelConjecture_R1.H3`:
for any recursive theory `T` in `Language.orderedExpField` and any `b : Bool`, the set of Gödel
numbers of sentences `φ` such that `T ⊨ᵇ (if b then φ else φ.not)` is recursively enumerable.

## Structure of the proof
1. **Concrete syntax and bridge (`OTerm`, `OForm`)**: locally nameless ASTs with de Bruijn levels
   matching Mathlib's `FirstOrder.Language.BoundedFormula`, together with realization and
   exact round-trip translations with `Language.orderedExpField.BoundedFormula Empty k`.
2. **Cut-free two-sided sequent calculus (`SeqProv`)**: 14 rules covering propositional logic,
   quantifiers (with fresh free variable), equality equivalence, and congruence for the 5
   non-constant symbols of `orderedExpField`. Soundness is a direct induction; completeness is
   proved via a countable Schütte–Hintikka saturation chain and a quotient term model. Combined
   with Mathlib's compactness theorem, `T ⊨ᵇ φ` iff there is a finite list `Γ ⊆ T` with
   `SeqProv Γ [φ]`.
3. **Strict-subterm `ℕ`-encoding and bottom-up proof traces**: `encT`/`encF` use `Nat.pair tag body + 1`
   so every subterm/subformula has strictly smaller code. A bottom-up sequent trace validator and a
   forward stack-machine translator to Mathlib's `BoundedFormula.listEncode` are proved primitive
   recursive via `Primrec.nat_strong_rec` and `Primrec.nat_rec'`.
4. **Effective proof search**: `Partrec.rfind` over witnesses `(φ_code, Γ_codes, trace)` using the
   computable decider of `T` yields `REPred`.
-/

-- Step TarskiExponentialFunctionProblem.isDecidable_completeTheory_realExp_of_realSchanuelConjecture.R1.H3
-- Credit: @ovolee37

namespace OMA.TarskiH3

open FirstOrder FirstOrder.Language Encodable

abbrev L : Language := Language.orderedExpField

abbrev fAdd : L.Functions 2 := Sum.inl Ring.addFunc
abbrev fMul : L.Functions 2 := Sum.inl Ring.mulFunc
abbrev fNeg : L.Functions 1 := Sum.inl Ring.negFunc
abbrev fZero : L.Functions 0 := Sum.inl Ring.zeroFunc
abbrev fOne : L.Functions 0 := Sum.inl Ring.oneFunc
abbrev fExp : L.Functions 1 := Sum.inr (Sum.inl expFunc.exp)
abbrev rLe : L.Relations 2 := Sum.inr (Sum.inr leSymb)

/- ## Section 1: Concrete AST, semantics, substitution, and Mathlib bridge -/

inductive OTerm : Type
  | fvar (v : ℕ) : OTerm
  | bvar (k : ℕ) : OTerm
  | zero : OTerm
  | one : OTerm
  | neg (t : OTerm) : OTerm
  | exp (t : OTerm) : OTerm
  | add (t₁ t₂ : OTerm) : OTerm
  | mul (t₁ t₂ : OTerm) : OTerm
  deriving DecidableEq

inductive OForm : Type
  | bot : OForm
  | eq (t₁ t₂ : OTerm) : OForm
  | le (t₁ t₂ : OTerm) : OForm
  | imp (φ ψ : OForm) : OForm
  | all (k : ℕ) (φ : OForm) : OForm
  deriving DecidableEq

def OTerm.noBVar : OTerm → Bool
  | .fvar _ => true
  | .bvar _ => false
  | .zero => true
  | .one => true
  | .neg t => t.noBVar
  | .exp t => t.noBVar
  | .add t₁ t₂ => t₁.noBVar && t₂.noBVar
  | .mul t₁ t₂ => t₁.noBVar && t₂.noBVar

def OTerm.hasFVar (v : ℕ) : OTerm → Bool
  | .fvar w => decide (w = v)
  | .bvar _ => false
  | .zero => false
  | .one => false
  | .neg t => t.hasFVar v
  | .exp t => t.hasFVar v
  | .add t₁ t₂ => t₁.hasFVar v || t₂.hasFVar v
  | .mul t₁ t₂ => t₁.hasFVar v || t₂.hasFVar v

def OTerm.maxFVar : OTerm → ℕ
  | .fvar w => w + 1
  | .bvar _ => 0
  | .zero => 0
  | .one => 0
  | .neg t => t.maxFVar
  | .exp t => t.maxFVar
  | .add t₁ t₂ => max t₁.maxFVar t₂.maxFVar
  | .mul t₁ t₂ => max t₁.maxFVar t₂.maxFVar

lemma OTerm.hasFVar_eq_false_of_le (t : OTerm) {v : ℕ} (hv : t.maxFVar ≤ v) :
    t.hasFVar v = false := by
  induction t with
  | fvar w =>
    simp only [maxFVar] at hv
    simp [hasFVar, Nat.ne_of_lt (by omega : w < v)]
  | bvar _ | zero | one => rfl
  | neg t ih | exp t ih => exact ih hv
  | add t₁ t₂ ih₁ ih₂ | mul t₁ t₂ ih₁ ih₂ =>
    simp only [maxFVar, max_le_iff] at hv
    simp [hasFVar, ih₁ hv.1, ih₂ hv.2]

def OTerm.substB : OTerm → ℕ → OTerm → OTerm
  | .fvar v, _, _ => .fvar v
  | .bvar j, k, u => if j = k then u else .bvar j
  | .zero, _, _ => .zero
  | .one, _, _ => .one
  | .neg t, k, u => .neg (t.substB k u)
  | .exp t, k, u => .exp (t.substB k u)
  | .add t₁ t₂, k, u => .add (t₁.substB k u) (t₂.substB k u)
  | .mul t₁ t₂, k, u => .mul (t₁.substB k u) (t₂.substB k u)

def OTerm.bvarsSub (bound : List ℕ) : OTerm → Prop
  | .fvar _ => True
  | .bvar j => j ∈ bound
  | .zero => True
  | .one => True
  | .neg t => t.bvarsSub bound
  | .exp t => t.bvarsSub bound
  | .add t₁ t₂ => t₁.bvarsSub bound ∧ t₂.bvarsSub bound
  | .mul t₁ t₂ => t₁.bvarsSub bound ∧ t₂.bvarsSub bound

lemma OTerm.bvarsSub_nil_iff (t : OTerm) : t.bvarsSub [] ↔ t.noBVar = true := by
  induction t with
  | fvar _ | zero | one => simp [bvarsSub, noBVar]
  | bvar _ => simp [bvarsSub, noBVar]
  | neg t ih | exp t ih => simpa [bvarsSub, noBVar] using ih
  | add t₁ t₂ ih₁ ih₂ | mul t₁ t₂ ih₁ ih₂ =>
    simp [bvarsSub, noBVar, ih₁, ih₂]

lemma OTerm.bvarsSub_substB {t u : OTerm} {k : ℕ} {bound : List ℕ}
    (ht : t.bvarsSub (k :: bound)) (hu : u.noBVar = true) :
    (t.substB k u).bvarsSub bound := by
  have huB : ∀ b, u.bvarsSub b := by
    intro b
    clear ht
    induction u with
    | fvar _ | zero | one => trivial
    | bvar _ => simp [noBVar] at hu
    | neg t ih | exp t ih => exact ih hu
    | add t₁ t₂ ih₁ ih₂ | mul t₁ t₂ ih₁ ih₂ =>
      simp only [noBVar, Bool.and_eq_true] at hu
      exact ⟨ih₁ hu.1, ih₂ hu.2⟩
  induction t with
  | fvar _ | zero | one => trivial
  | bvar j =>
    simp only [bvarsSub, List.mem_cons] at ht
    simp only [substB]
    split_ifs with h
    · exact huB bound
    · exact ht.resolve_left h
  | neg t ih | exp t ih => exact ih ht
  | add t₁ t₂ ih₁ ih₂ | mul t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ ht.1, ih₂ ht.2⟩

def OTerm.isBounded (k : ℕ) : OTerm → Bool
  | .fvar _ => false
  | .bvar i => decide (i < k)
  | .zero => true
  | .one => true
  | .neg t => t.isBounded k
  | .exp t => t.isBounded k
  | .add t₁ t₂ => t₁.isBounded k && t₂.isBounded k
  | .mul t₁ t₂ => t₁.isBounded k && t₂.isBounded k

lemma OTerm.bvarsSub_range_of_isBounded {t : OTerm} {k : ℕ} (h : t.isBounded k = true) :
    t.bvarsSub (List.range k) := by
  induction t with
  | fvar _ => simp [isBounded] at h
  | bvar i => simp [isBounded, bvarsSub] at h ⊢; exact h
  | zero | one => trivial
  | neg t ih | exp t ih => exact ih h
  | add t₁ t₂ ih₁ ih₂ | mul t₁ t₂ ih₁ ih₂ =>
    simp only [isBounded, Bool.and_eq_true] at h
    exact ⟨ih₁ h.1, ih₂ h.2⟩

def OForm.size : OForm → ℕ
  | .bot => 1
  | .eq _ _ => 1
  | .le _ _ => 1
  | .imp φ ψ => 1 + φ.size + ψ.size
  | .all _ φ => 1 + φ.size

def OForm.hasFVar (v : ℕ) : OForm → Bool
  | .bot => false
  | .eq t₁ t₂ => t₁.hasFVar v || t₂.hasFVar v
  | .le t₁ t₂ => t₁.hasFVar v || t₂.hasFVar v
  | .imp φ ψ => φ.hasFVar v || ψ.hasFVar v
  | .all _ φ => φ.hasFVar v

def OForm.maxFVar : OForm → ℕ
  | .bot => 0
  | .eq t₁ t₂ => max t₁.maxFVar t₂.maxFVar
  | .le t₁ t₂ => max t₁.maxFVar t₂.maxFVar
  | .imp φ ψ => max φ.maxFVar ψ.maxFVar
  | .all _ φ => φ.maxFVar

lemma OForm.hasFVar_eq_false_of_le (φ : OForm) {v : ℕ} (hv : φ.maxFVar ≤ v) :
    φ.hasFVar v = false := by
  induction φ with
  | bot => rfl
  | eq t₁ t₂ | le t₁ t₂ =>
    simp only [maxFVar, max_le_iff] at hv
    simp [hasFVar, t₁.hasFVar_eq_false_of_le hv.1, t₂.hasFVar_eq_false_of_le hv.2]
  | imp φ ψ ih₁ ih₂ =>
    simp only [maxFVar, max_le_iff] at hv
    simp [hasFVar, ih₁ hv.1, ih₂ hv.2]
  | all _ φ ih => exact ih hv

def OForm.substB : OForm → ℕ → OTerm → OForm
  | .bot, _, _ => .bot
  | .eq t₁ t₂, k, u => .eq (t₁.substB k u) (t₂.substB k u)
  | .le t₁ t₂, k, u => .le (t₁.substB k u) (t₂.substB k u)
  | .imp φ ψ, k, u => .imp (φ.substB k u) (ψ.substB k u)
  | .all m φ, k, u => if m = k then .all m φ else .all m (φ.substB k u)

lemma OForm.size_substB (φ : OForm) (k : ℕ) (u : OTerm) : (φ.substB k u).size = φ.size := by
  induction φ with
  | bot | eq _ _ | le _ _ => rfl
  | imp φ ψ ih₁ ih₂ => simp [substB, size, ih₁, ih₂]
  | all m φ ih =>
    simp only [substB]
    split_ifs <;> simp [size, ih]

def OForm.closedAt (bound : List ℕ) : OForm → Prop
  | .bot => True
  | .eq t₁ t₂ => t₁.bvarsSub bound ∧ t₂.bvarsSub bound
  | .le t₁ t₂ => t₁.bvarsSub bound ∧ t₂.bvarsSub bound
  | .imp φ ψ => φ.closedAt bound ∧ ψ.closedAt bound
  | .all m φ => φ.closedAt (m :: bound)

lemma OForm.closedAt_mono {φ : OForm} {b₁ b₂ : List ℕ}
    (h : ∀ x, x ∈ b₁ → x ∈ b₂) (hc : φ.closedAt b₁) : φ.closedAt b₂ := by
  have hT : ∀ {t : OTerm} {a b : List ℕ}, (∀ x, x ∈ a → x ∈ b) → t.bvarsSub a → t.bvarsSub b := by
    intro t a b hab ht
    induction t with
    | fvar _ | zero | one => trivial
    | bvar j => exact hab j ht
    | neg t ih | exp t ih => exact ih ht
    | add t₁ t₂ ih₁ ih₂ | mul t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ ht.1, ih₂ ht.2⟩
  induction φ generalizing b₁ b₂ with
  | bot => trivial
  | eq t₁ t₂ | le t₁ t₂ => exact ⟨hT h hc.1, hT h hc.2⟩
  | imp φ ψ ih₁ ih₂ => exact ⟨ih₁ h hc.1, ih₂ h hc.2⟩
  | all m φ ih =>
    apply ih _ hc
    intro x hx
    simp only [List.mem_cons] at hx ⊢
    exact hx.imp id (h x)

lemma OForm.closedAt_substB {φ : OForm} {k : ℕ} {u : OTerm} {bound : List ℕ}
    (hφ : φ.closedAt (k :: bound)) (hu : u.noBVar = true) :
    (φ.substB k u).closedAt bound := by
  induction φ generalizing bound with
  | bot => trivial
  | eq t₁ t₂ | le t₁ t₂ =>
    exact ⟨OTerm.bvarsSub_substB hφ.1 hu, OTerm.bvarsSub_substB hφ.2 hu⟩
  | imp φ ψ ih₁ ih₂ => exact ⟨ih₁ hφ.1, ih₂ hφ.2⟩
  | all m φ ih =>
    simp only [substB]
    split_ifs with hmk
    · change φ.closedAt (m :: bound)
      refine closedAt_mono (fun x hx => ?_) hφ
      simp only [List.mem_cons] at hx ⊢
      rcases hx with h1 | h2 | hx
      · exact Or.inl h1
      · exact Or.inl (h2.trans hmk.symm)
      · exact Or.inr hx
    · refine ih (closedAt_mono (fun x hx => ?_) hφ)
      simp only [List.mem_cons] at hx ⊢
      tauto

def OForm.isBounded (k : ℕ) : OForm → Bool
  | .bot => true
  | .eq t₁ t₂ => t₁.isBounded k && t₂.isBounded k
  | .le t₁ t₂ => t₁.isBounded k && t₂.isBounded k
  | .imp φ ψ => φ.isBounded k && ψ.isBounded k
  | .all m φ => decide (m = k) && φ.isBounded (k + 1)

lemma OForm.closedAt_range_of_isBounded {φ : OForm} {k : ℕ} (h : φ.isBounded k = true) :
    φ.closedAt (List.range k) := by
  induction φ generalizing k with
  | bot => trivial
  | eq t₁ t₂ | le t₁ t₂ =>
    simp only [isBounded, Bool.and_eq_true] at h
    exact ⟨OTerm.bvarsSub_range_of_isBounded h.1, OTerm.bvarsSub_range_of_isBounded h.2⟩
  | imp φ ψ ih₁ ih₂ =>
    simp only [isBounded, Bool.and_eq_true] at h
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | all m φ ih =>
    simp only [isBounded, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨rfl, hφ⟩
    change φ.closedAt (m :: List.range m)
    refine closedAt_mono (fun x hx => ?_) (ih hφ)
    simp only [List.mem_range, List.mem_cons] at hx ⊢
    omega

/- ### Semantics of `OTerm` and `OForm` -/

def OTerm.eval (M : Type*) [L.Structure M] (ρ σ : ℕ → M) : OTerm → M
  | .fvar v => ρ v
  | .bvar k => σ k
  | .zero => Structure.funMap (L := L) fZero Fin.elim0
  | .one => Structure.funMap (L := L) fOne Fin.elim0
  | .neg t => Structure.funMap (L := L) fNeg ![t.eval M ρ σ]
  | .exp t => Structure.funMap (L := L) fExp ![t.eval M ρ σ]
  | .add t₁ t₂ => Structure.funMap (L := L) fAdd ![t₁.eval M ρ σ, t₂.eval M ρ σ]
  | .mul t₁ t₂ => Structure.funMap (L := L) fMul ![t₁.eval M ρ σ, t₂.eval M ρ σ]

def OForm.Realize (M : Type*) [L.Structure M] (ρ σ : ℕ → M) : OForm → Prop
  | .bot => False
  | .eq t₁ t₂ => t₁.eval M ρ σ = t₂.eval M ρ σ
  | .le t₁ t₂ => Structure.RelMap (L := L) rLe ![t₁.eval M ρ σ, t₂.eval M ρ σ]
  | .imp φ ψ => φ.Realize M ρ σ → ψ.Realize M ρ σ
  | .all k φ => ∀ x : M, φ.Realize M ρ (Function.update σ k x)

lemma OTerm.eval_noBVar {M : Type*} [L.Structure M] (ρ σ₁ σ₂ : ℕ → M) {t : OTerm}
    (ht : t.noBVar = true) : t.eval M ρ σ₁ = t.eval M ρ σ₂ := by
  induction t with
  | fvar _ | zero | one => rfl
  | bvar _ => simp [noBVar] at ht
  | neg t ih | exp t ih => simp [eval, ih ht]
  | add t₁ t₂ ih₁ ih₂ | mul t₁ t₂ ih₁ ih₂ =>
    simp only [noBVar, Bool.and_eq_true] at ht
    simp [eval, ih₁ ht.1, ih₂ ht.2]

lemma OTerm.eval_substB {M : Type*} [L.Structure M] (ρ σ : ℕ → M) {t u : OTerm} {k : ℕ}
    (hu : u.noBVar = true) :
    (t.substB k u).eval M ρ σ = t.eval M ρ (Function.update σ k (u.eval M ρ σ)) := by
  induction t with
  | fvar _ | zero | one => rfl
  | bvar j =>
    simp only [substB]
    by_cases hjk : j = k
    · subst hjk; simp [eval]
    · simp [hjk, eval, Function.update_of_ne hjk]
  | neg t ih | exp t ih => simp [substB, eval, ih]
  | add t₁ t₂ ih₁ ih₂ | mul t₁ t₂ ih₁ ih₂ => simp [substB, eval, ih₁, ih₂]

lemma OForm.realize_substB {M : Type*} [L.Structure M] (ρ σ : ℕ → M) {φ : OForm} {u : OTerm}
    {k : ℕ} (hu : u.noBVar = true) :
    (φ.substB k u).Realize M ρ σ ↔ φ.Realize M ρ (Function.update σ k (u.eval M ρ σ)) := by
  induction φ generalizing σ with
  | bot => rfl
  | eq t₁ t₂ => simp [substB, Realize, OTerm.eval_substB _ _ hu]
  | le t₁ t₂ => simp [substB, Realize, OTerm.eval_substB _ _ hu]
  | imp φ ψ ih₁ ih₂ => simp [substB, Realize, ih₁, ih₂]
  | all m φ ih =>
    simp only [substB]
    split_ifs with hmk
    · subst hmk
      simp only [Realize, Function.update_idem]
    · simp only [Realize]
      constructor
      · intro h x
        have hx := (ih (Function.update σ m x)).mp (h x)
        rw [OTerm.eval_noBVar ρ (Function.update σ m x) σ hu,
          Function.update_comm hmk] at hx
        exact hx
      · intro h x
        apply (ih (Function.update σ m x)).mpr
        rw [OTerm.eval_noBVar ρ (Function.update σ m x) σ hu,
          Function.update_comm hmk]
        exact h x

lemma OTerm.eval_update_fvar {M : Type*} [L.Structure M] (ρ σ : ℕ → M) {t : OTerm} {v : ℕ}
    {x : M} (hv : t.hasFVar v = false) :
    t.eval M (Function.update ρ v x) σ = t.eval M ρ σ := by
  induction t with
  | fvar w =>
    simp only [hasFVar, decide_eq_false_iff_not] at hv
    simp [eval, Function.update_of_ne hv]
  | bvar _ | zero | one => rfl
  | neg t ih | exp t ih => simp [eval, ih hv]
  | add t₁ t₂ ih₁ ih₂ | mul t₁ t₂ ih₁ ih₂ =>
    simp only [hasFVar, Bool.or_eq_false_iff] at hv
    simp [eval, ih₁ hv.1, ih₂ hv.2]

lemma OForm.realize_update_fvar {M : Type*} [L.Structure M] (ρ σ : ℕ → M) {φ : OForm} {v : ℕ}
    {x : M} (hv : φ.hasFVar v = false) :
    φ.Realize M (Function.update ρ v x) σ ↔ φ.Realize M ρ σ := by
  induction φ generalizing σ with
  | bot => rfl
  | eq t₁ t₂ | le t₁ t₂ =>
    simp only [hasFVar, Bool.or_eq_false_iff] at hv
    simp [Realize, OTerm.eval_update_fvar _ _ hv.1, OTerm.eval_update_fvar _ _ hv.2]
  | imp φ ψ ih₁ ih₂ =>
    simp only [hasFVar, Bool.or_eq_false_iff] at hv
    simp [Realize, ih₁ _ hv.1, ih₂ _ hv.2]
  | all m φ ih =>
    simp only [Realize]
    exact forall_congr' fun y => ih (Function.update σ m y) hv

/- ### Exact bridge with `Language.orderedExpField` -/

def fromTerm {k : ℕ} : L.Term (Empty ⊕ Fin k) → OTerm
  | .var (Sum.inl e) => Empty.elim e
  | .var (Sum.inr i) => .bvar i.val
  | .func f ts =>
    match f with
    | Sum.inl ringFunc.add => .add (fromTerm (ts 0)) (fromTerm (ts 1))
    | Sum.inl ringFunc.mul => .mul (fromTerm (ts 0)) (fromTerm (ts 1))
    | Sum.inl ringFunc.neg => .neg (fromTerm (ts 0))
    | Sum.inl ringFunc.zero => .zero
    | Sum.inl ringFunc.one => .one
    | Sum.inr (Sum.inl expFunc.exp) => .exp (fromTerm (ts 0))
    | Sum.inr (Sum.inr r) => Empty.elim r

def fromBF : ∀ {k : ℕ}, L.BoundedFormula Empty k → OForm
  | _, .falsum => .bot
  | _, .equal t₁ t₂ => .eq (fromTerm t₁) (fromTerm t₂)
  | _, .rel r ts =>
    match r with
    | Sum.inl r => Empty.elim r
    | Sum.inr (Sum.inl r) => Empty.elim r
    | Sum.inr (Sum.inr r) =>
      match r with
      | orderRel.le => .le (fromTerm (ts 0)) (fromTerm (ts 1))
  | _, .imp φ ψ => .imp (fromBF φ) (fromBF ψ)
  | k, .all φ => .all k (fromBF φ)

lemma fromTerm_isBounded {k : ℕ} (t : L.Term (Empty ⊕ Fin k)) :
    (fromTerm t).isBounded k = true := by
  induction t with
  | var v =>
    rcases v with e | i
    · exact Empty.elim e
    · simp [fromTerm, OTerm.isBounded, i.isLt]
  | func f ts ih =>
    rcases f with f | (f | f)
    · cases f <;> simp [fromTerm, OTerm.isBounded, ih]
    · cases f; simp [fromTerm, OTerm.isBounded, ih]
    · exact Empty.elim f

lemma fromBF_isBounded {k : ℕ} (φ : L.BoundedFormula Empty k) :
    (fromBF φ).isBounded k = true := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp [fromBF, OForm.isBounded, fromTerm_isBounded]
  | rel r ts =>
    rcases r with r | (r | r)
    · exact Empty.elim r
    · exact Empty.elim r
    · cases r; simp [fromBF, OForm.isBounded, fromTerm_isBounded]
  | imp φ ψ ih₁ ih₂ => simp [fromBF, OForm.isBounded, ih₁, ih₂]
  | all φ ih => simp [fromBF, OForm.isBounded, ih]

def toTerm {k : ℕ} : (t : OTerm) → t.isBounded k = true → L.Term (Empty ⊕ Fin k)
  | .fvar _, h => by simp [OTerm.isBounded] at h
  | .bvar i, h => .var (Sum.inr ⟨i, by simpa [OTerm.isBounded] using h⟩)
  | .zero, _ => .func fZero Fin.elim0
  | .one, _ => .func fOne Fin.elim0
  | .neg t, h => .func fNeg ![toTerm t h]
  | .exp t, h => .func fExp ![toTerm t h]
  | .add t₁ t₂, h =>
    .func fAdd ![toTerm t₁ (Bool.and_eq_true _ _ |>.mp h).1,
                 toTerm t₂ (Bool.and_eq_true _ _ |>.mp h).2]
  | .mul t₁ t₂, h =>
    .func fMul ![toTerm t₁ (Bool.and_eq_true _ _ |>.mp h).1,
                 toTerm t₂ (Bool.and_eq_true _ _ |>.mp h).2]

def toBF : ∀ {k : ℕ} (φ : OForm), φ.isBounded k = true → L.BoundedFormula Empty k
  | _, .bot, _ => .falsum
  | _, .eq t₁ t₂, h =>
    .equal (toTerm t₁ (Bool.and_eq_true _ _ |>.mp h).1)
           (toTerm t₂ (Bool.and_eq_true _ _ |>.mp h).2)
  | _, .le t₁ t₂, h =>
    .rel rLe ![toTerm t₁ (Bool.and_eq_true _ _ |>.mp h).1,
               toTerm t₂ (Bool.and_eq_true _ _ |>.mp h).2]
  | _, .imp φ ψ, h =>
    .imp (toBF φ (Bool.and_eq_true _ _ |>.mp h).1)
         (toBF ψ (Bool.and_eq_true _ _ |>.mp h).2)
  | _, .all _ φ, h =>
    .all (toBF φ (Bool.and_eq_true _ _ |>.mp h).2)

lemma fromTerm_toTerm {k : ℕ} (t : OTerm) (h : t.isBounded k = true) :
    fromTerm (toTerm t h) = t := by
  induction t with
  | fvar _ => simp [OTerm.isBounded] at h
  | bvar _ | zero | one => rfl
  | neg t ih => simp only [toTerm, fromTerm, fNeg, Ring.negFunc]; exact congrArg OTerm.neg (ih h)
  | exp t ih => simp only [toTerm, fromTerm, fExp]; exact congrArg OTerm.exp (ih h)
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [toTerm, fromTerm, fAdd, Ring.addFunc]
    exact congrArg₂ OTerm.add (ih₁ _) (ih₂ _)
  | mul t₁ t₂ ih₁ ih₂ =>
    simp only [toTerm, fromTerm, fMul, Ring.mulFunc]
    exact congrArg₂ OTerm.mul (ih₁ _) (ih₂ _)

lemma fromBF_toBF {k : ℕ} (φ : OForm) (h : φ.isBounded k = true) :
    fromBF (toBF φ h) = φ := by
  induction φ generalizing k with
  | bot => rfl
  | eq t₁ t₂ => simp [toBF, fromBF, fromTerm_toTerm]
  | le t₁ t₂ => simp [toBF, fromBF, rLe, leSymb, fromTerm_toTerm]
  | imp φ ψ ih₁ ih₂ => simp [toBF, fromBF, ih₁, ih₂]
  | all m φ ih =>
    have hm : m = k := by
      simp only [OForm.isBounded, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1
    subst hm
    simp [toBF, fromBF, ih]

lemma toTerm_fromTerm {k : ℕ} (t : L.Term (Empty ⊕ Fin k)) :
    toTerm (fromTerm t) (fromTerm_isBounded t) = t := by
  induction t with
  | var v =>
    rcases v with e | i
    · exact Empty.elim e
    · rfl
  | func f ts ih =>
    rcases f with f | (f | f)
    · cases f
      · simp only [fromTerm, toTerm]; congr 1; funext i; fin_cases i <;> simp [ih]
      · simp only [fromTerm, toTerm]; congr 1; funext i; fin_cases i <;> simp [ih]
      · simp only [fromTerm, toTerm]; congr 1; funext i; fin_cases i; simp [ih]
      · simp only [fromTerm, toTerm]; congr 1; funext i; exact Fin.elim0 i
      · simp only [fromTerm, toTerm]; congr 1; funext i; exact Fin.elim0 i
    · cases f
      simp only [fromTerm, toTerm]; congr 1; funext i; fin_cases i; simp [ih]
    · exact Empty.elim f

lemma toBF_fromBF {k : ℕ} (φ : L.BoundedFormula Empty k) :
    toBF (fromBF φ) (fromBF_isBounded φ) = φ := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp [fromBF, toBF, toTerm_fromTerm]
  | rel r ts =>
    rcases r with r | (r | r)
    · exact Empty.elim r
    · exact Empty.elim r
    · cases r
      simp only [fromBF, toBF]
      congr 1; funext i; fin_cases i <;> simp [toTerm_fromTerm]
  | imp φ ψ ih₁ ih₂ => simp [fromBF, toBF, ih₁, ih₂]
  | all φ ih => simp [fromBF, toBF, ih]

lemma fromTerm_eval {M : Type*} [L.Structure M] (ρ σ : ℕ → M) {k : ℕ}
    (xs : Fin k → M) (hσ : ∀ i : Fin k, σ i.val = xs i) (t : L.Term (Empty ⊕ Fin k)) :
    (fromTerm t).eval M ρ σ = t.realize (Sum.elim Empty.elim xs) := by
  induction t with
  | var v =>
    rcases v with e | i
    · exact Empty.elim e
    · simp [fromTerm, OTerm.eval, hσ i]
  | func f ts ih =>
    rcases f with f | (f | f)
    · cases f
      · simp only [fromTerm, OTerm.eval, Term.realize_func]
        congr 1; funext i; fin_cases i <;> simp [ih]
      · simp only [fromTerm, OTerm.eval, Term.realize_func]
        congr 1; funext i; fin_cases i <;> simp [ih]
      · simp only [fromTerm, OTerm.eval, Term.realize_func]
        congr 1; funext i; fin_cases i; simp [ih]
      · simp only [fromTerm, OTerm.eval, Term.realize_func]
        congr 1; funext i; exact Fin.elim0 i
      · simp only [fromTerm, OTerm.eval, Term.realize_func]
        congr 1; funext i; exact Fin.elim0 i
    · cases f
      simp only [fromTerm, OTerm.eval, Term.realize_func]
      congr 1; funext i; fin_cases i; simp [ih]
    · exact Empty.elim f

lemma fromBF_realize {M : Type*} [L.Structure M] (ρ σ : ℕ → M) {k : ℕ}
    (xs : Fin k → M) (hσ : ∀ i : Fin k, σ i.val = xs i) (φ : L.BoundedFormula Empty k) :
    (fromBF φ).Realize M ρ σ ↔ φ.Realize Empty.elim xs := by
  induction φ generalizing σ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp [fromBF, OForm.Realize, BoundedFormula.Realize, fromTerm_eval ρ σ xs hσ]
  | rel r ts =>
    rcases r with r | (r | r)
    · exact Empty.elim r
    · exact Empty.elim r
    · cases r
      simp only [fromBF, OForm.Realize, BoundedFormula.realize_rel]
      have heq : ![(fromTerm (ts 0)).eval M ρ σ, (fromTerm (ts 1)).eval M ρ σ] =
          fun i => (ts i).realize (Sum.elim Empty.elim xs) := by
        funext i; fin_cases i <;> simp [fromTerm_eval ρ σ xs hσ]
      rw [heq]
      rfl
  | imp φ ψ ih₁ ih₂ =>
    simp [fromBF, OForm.Realize, BoundedFormula.realize_imp, ih₁ σ xs hσ, ih₂ σ xs hσ]
  | @all k φ ih =>
    simp only [fromBF, OForm.Realize, BoundedFormula.realize_all]
    refine forall_congr' fun x => ih (Function.update σ k x) (Fin.snoc xs x) fun i => ?_
    by_cases hi : i.val < k
    · have hne : i.val ≠ k := Nat.ne_of_lt hi
      have hcast : i = (⟨i.val, hi⟩ : Fin k).castSucc := rfl
      rw [Function.update_of_ne hne, hcast, Fin.snoc_castSucc]
      exact hσ ⟨i.val, hi⟩
    · have heq : i.val = k := by omega
      have hlast : i = Fin.last k := Fin.ext heq
      subst hlast
      simp

lemma fromSent_realize {M : Type*} [L.Structure M] (ρ σ : ℕ → M) (φ : L.Sentence) :
    (fromBF φ).Realize M ρ σ ↔ M ⊨ φ := by
  have h1 : (default : Empty → M) = Empty.elim := funext fun e => Empty.elim e
  have h2 : (default : Fin 0 → M) = Fin.elim0 := funext fun i => Fin.elim0 i
  exact (fromBF_realize ρ σ Fin.elim0 (fun i => Fin.elim0 i) φ).trans (by
    change BoundedFormula.Realize φ Empty.elim Fin.elim0 ↔ BoundedFormula.Realize φ default default
    rw [h1, h2])

lemma toSent_realize {M : Type*} [L.Structure M] (ρ σ : ℕ → M) (φ : OForm)
    (h : φ.isBounded 0 = true) :
    M ⊨ (toBF φ h : L.Sentence) ↔ φ.Realize M ρ σ := by
  have := fromSent_realize (M := M) ρ σ (toBF φ h)
  rw [fromBF_toBF φ h] at this
  exact this.symm

/- ## Section 2: Cut-free two-sided sequent calculus, soundness, and completeness -/

inductive SeqProv : List OForm → List OForm → Prop
  | ax {Γ Δ φ} : φ ∈ Γ → φ ∈ Δ → SeqProv Γ Δ
  | botL {Γ Δ} : OForm.bot ∈ Γ → SeqProv Γ Δ
  | impL {Γ Δ φ ψ} : OForm.imp φ ψ ∈ Γ →
      SeqProv Γ (φ :: Δ) → SeqProv (ψ :: Γ) Δ → SeqProv Γ Δ
  | impR {Γ Δ φ ψ} : OForm.imp φ ψ ∈ Δ →
      SeqProv (φ :: Γ) (ψ :: Δ) → SeqProv Γ Δ
  | allL {Γ Δ k φ t} : OForm.all k φ ∈ Γ → t.noBVar = true →
      SeqProv (φ.substB k t :: Γ) Δ → SeqProv Γ Δ
  | allR {Γ Δ k φ v} : OForm.all k φ ∈ Δ →
      (∀ ψ ∈ Γ, ψ.hasFVar v = false) → (∀ ψ ∈ Δ, ψ.hasFVar v = false) →
      SeqProv Γ (φ.substB k (.fvar v) :: Δ) → SeqProv Γ Δ
  | eqRefl {Γ Δ t} : t.noBVar = true →
      SeqProv (.eq t t :: Γ) Δ → SeqProv Γ Δ
  | eqSymm {Γ Δ t₁ t₂} : OForm.eq t₁ t₂ ∈ Γ →
      SeqProv (.eq t₂ t₁ :: Γ) Δ → SeqProv Γ Δ
  | eqTrans {Γ Δ t₁ t₂ t₃} : OForm.eq t₁ t₂ ∈ Γ → OForm.eq t₂ t₃ ∈ Γ →
      SeqProv (.eq t₁ t₃ :: Γ) Δ → SeqProv Γ Δ
  | congNeg {Γ Δ t₁ t₂} : OForm.eq t₁ t₂ ∈ Γ →
      SeqProv (.eq (.neg t₁) (.neg t₂) :: Γ) Δ → SeqProv Γ Δ
  | congExp {Γ Δ t₁ t₂} : OForm.eq t₁ t₂ ∈ Γ →
      SeqProv (.eq (.exp t₁) (.exp t₂) :: Γ) Δ → SeqProv Γ Δ
  | congAdd {Γ Δ t₁ s₁ t₂ s₂} : OForm.eq t₁ s₁ ∈ Γ → OForm.eq t₂ s₂ ∈ Γ →
      SeqProv (.eq (.add t₁ t₂) (.add s₁ s₂) :: Γ) Δ → SeqProv Γ Δ
  | congMul {Γ Δ t₁ s₁ t₂ s₂} : OForm.eq t₁ s₁ ∈ Γ → OForm.eq t₂ s₂ ∈ Γ →
      SeqProv (.eq (.mul t₁ t₂) (.mul s₁ s₂) :: Γ) Δ → SeqProv Γ Δ
  | congLe {Γ Δ t₁ s₁ t₂ s₂} : OForm.eq t₁ s₁ ∈ Γ → OForm.eq t₂ s₂ ∈ Γ →
      OForm.le t₁ t₂ ∈ Γ → SeqProv (.le s₁ s₂ :: Γ) Δ → SeqProv Γ Δ

lemma SeqProv.sound {Γ Δ : List OForm} (h : SeqProv Γ Δ)
    (M : Type*) [L.Structure M] (ρ σ : ℕ → M)
    (hΓ : ∀ φ ∈ Γ, φ.Realize M ρ σ) : ∃ ψ ∈ Δ, ψ.Realize M ρ σ := by
  induction h generalizing ρ with
  | ax h1 h2 => exact ⟨_, h2, hΓ _ h1⟩
  | botL h1 => exact False.elim (hΓ _ h1)
  | impL h1 _ _ ih1 ih2 =>
    obtain ⟨χ, hχ, hχR⟩ := ih1 ρ hΓ
    rcases List.mem_cons.mp hχ with rfl | hχ'
    · exact ih2 ρ (fun ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ'
        · exact hΓ _ h1 hχR
        · exact hΓ _ hψ')
    · exact ⟨χ, hχ', hχR⟩
  | @impR Γ Δ φ ψ h1 _ ih =>
    by_cases hφ : φ.Realize M ρ σ
    · obtain ⟨χ, hχ, hχR⟩ := ih ρ (fun ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ'
        · exact hφ
        · exact hΓ _ hψ')
      rcases List.mem_cons.mp hχ with rfl | hχ'
      · exact ⟨_, h1, fun _ => hχR⟩
      · exact ⟨χ, hχ', hχR⟩
    · exact ⟨_, h1, fun h => False.elim (hφ h)⟩
  | allL h1 ht _ ih =>
    apply ih ρ
    intro ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ'
    · exact (OForm.realize_substB ρ σ ht).mpr (hΓ _ h1 _)
    · exact hΓ _ hψ'
  | @allR Γ Δ k φ v h1 hfvΓ hfvΔ _ ih =>
    by_contra hno
    push Not at hno
    have hall : ¬ ∀ x : M, φ.Realize M ρ (Function.update σ k x) := hno _ h1
    push Not at hall
    obtain ⟨x, hx⟩ := hall
    obtain ⟨χ, hχ, hχR⟩ := ih (Function.update ρ v x) (fun ψ hψ =>
      (OForm.realize_update_fvar ρ σ (hfvΓ ψ hψ)).mpr (hΓ ψ hψ))
    rcases List.mem_cons.mp hχ with rfl | hχ'
    · have hsub := (OForm.realize_substB (Function.update ρ v x) σ rfl).mp hχR
      simp only [OTerm.eval, Function.update_self] at hsub
      have hφfv : φ.hasFVar v = false := hfvΔ (.all k φ) h1
      exact hx ((OForm.realize_update_fvar ρ (Function.update σ k x) hφfv).mp hsub)
    · exact hno χ hχ' ((OForm.realize_update_fvar ρ σ (hfvΔ χ hχ')).mp hχR)
  | eqRefl _ _ ih =>
    exact ih ρ (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · exact rfl
      · exact hΓ _ hψ')
  | eqSymm h1 _ ih =>
    exact ih ρ (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · exact (hΓ _ h1).symm
      · exact hΓ _ hψ')
  | eqTrans h1 h2 _ ih =>
    exact ih ρ (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · exact (hΓ _ h1).trans (hΓ _ h2)
      · exact hΓ _ hψ')
  | congNeg h1 _ ih =>
    exact ih ρ (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · change Structure.funMap (L := L) fNeg ![_] = Structure.funMap (L := L) fNeg ![_]
        rw [show _ = _ from hΓ _ h1]
      · exact hΓ _ hψ')
  | congExp h1 _ ih =>
    exact ih ρ (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · change Structure.funMap (L := L) fExp ![_] = Structure.funMap (L := L) fExp ![_]
        rw [show _ = _ from hΓ _ h1]
      · exact hΓ _ hψ')
  | congAdd h1 h2 _ ih =>
    exact ih ρ (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · change Structure.funMap (L := L) fAdd ![_, _] = Structure.funMap (L := L) fAdd ![_, _]
        rw [show _ = _ from hΓ _ h1, show _ = _ from hΓ _ h2]
      · exact hΓ _ hψ')
  | congMul h1 h2 _ ih =>
    exact ih ρ (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · change Structure.funMap (L := L) fMul ![_, _] = Structure.funMap (L := L) fMul ![_, _]
        rw [show _ = _ from hΓ _ h1, show _ = _ from hΓ _ h2]
      · exact hΓ _ hψ')
  | congLe h1 h2 h3 _ ih =>
    exact ih ρ (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · change Structure.RelMap (L := L) rLe ![_, _]
        rw [← show _ = _ from hΓ _ h1, ← show _ = _ from hΓ _ h2]
        exact hΓ _ h3
      · exact hΓ _ hψ')

/- ### Strict-subterm `ℕ` codes for `OTerm` and `OForm` (used both for enumeration and Primrec) -/

def encT : OTerm → ℕ
  | .fvar v => Nat.pair 0 v + 1
  | .bvar k => Nat.pair 1 k + 1
  | .zero => Nat.pair 2 0 + 1
  | .one => Nat.pair 3 0 + 1
  | .neg t => Nat.pair 4 (encT t) + 1
  | .exp t => Nat.pair 5 (encT t) + 1
  | .add t₁ t₂ => Nat.pair 6 (Nat.pair (encT t₁) (encT t₂)) + 1
  | .mul t₁ t₂ => Nat.pair 7 (Nat.pair (encT t₁) (encT t₂)) + 1

def encF : OForm → ℕ
  | .bot => Nat.pair 0 0 + 1
  | .eq t₁ t₂ => Nat.pair 1 (Nat.pair (encT t₁) (encT t₂)) + 1
  | .le t₁ t₂ => Nat.pair 2 (Nat.pair (encT t₁) (encT t₂)) + 1
  | .imp φ ψ => Nat.pair 3 (Nat.pair (encF φ) (encF ψ)) + 1
  | .all k φ => Nat.pair 4 (Nat.pair k (encF φ)) + 1

lemma encT_pos (t : OTerm) : 0 < encT t := by
  cases t <;> exact Nat.succ_pos _

lemma encF_pos (φ : OForm) : 0 < encF φ := by
  cases φ <;> exact Nat.succ_pos _

lemma pair_add_ge (a b : ℕ) : a + b ≤ Nat.pair a b := by
  unfold Nat.pair
  split_ifs with h
  · nlinarith
  · nlinarith

lemma encF_ge_size (φ : OForm) : φ.size ≤ encF φ := by
  induction φ with
  | bot => simp [OForm.size, encF]
  | eq _ _ => simp [OForm.size, encF]
  | le _ _ => simp [OForm.size, encF]
  | imp φ ψ ih₁ ih₂ =>
    simp only [OForm.size, encF]
    have h1 := pair_add_ge 3 (Nat.pair (encF φ) (encF ψ))
    have h2 := pair_add_ge (encF φ) (encF ψ)
    omega
  | all k φ ih =>
    simp only [OForm.size, encF]
    have h1 := pair_add_ge 4 (Nat.pair k (encF φ))
    have h2 := pair_add_ge k (encF φ)
    omega

def decT (n : ℕ) : Option OTerm :=
  if h : n = 0 then none
  else
    let p := (n - 1).unpair
    have hp2 : p.2 < n := by
      have : p.2 ≤ n - 1 := Nat.unpair_right_le (n - 1)
      omega
    match p.1 with
    | 0 => some (.fvar p.2)
    | 1 => some (.bvar p.2)
    | 2 => if p.2 = 0 then some .zero else none
    | 3 => if p.2 = 0 then some .one else none
    | 4 => (decT p.2).map .neg
    | 5 => (decT p.2).map .exp
    | 6 =>
      have ha : p.2.unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le p.2) hp2
      have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
      match decT p.2.unpair.1, decT p.2.unpair.2 with
      | some t₁, some t₂ => some (.add t₁ t₂)
      | _, _ => none
    | 7 =>
      have ha : p.2.unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le p.2) hp2
      have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
      match decT p.2.unpair.1, decT p.2.unpair.2 with
      | some t₁, some t₂ => some (.mul t₁ t₂)
      | _, _ => none
    | _ => none
termination_by n

lemma decT_encT (t : OTerm) : decT (encT t) = some t := by
  induction t with
  | fvar v => rw [encT, decT]; simp
  | bvar k => rw [encT, decT]; simp
  | zero => rw [encT, decT]; simp
  | one => rw [encT, decT]; simp
  | neg t ih => rw [encT, decT]; simp [ih]
  | exp t ih => rw [encT, decT]; simp [ih]
  | add t₁ t₂ ih₁ ih₂ => rw [encT, decT]; simp [ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => rw [encT, decT]; simp [ih₁, ih₂]

lemma encT_injective : Function.Injective encT := fun a b h => by
  have := congrArg decT h
  rw [decT_encT, decT_encT] at this
  exact Option.some.inj this

lemma encT_decT {n : ℕ} {t : OTerm} (h : decT n = some t) : encT t = n := by
  induction n using Nat.strong_induction_on generalizing t with
  | h n ih =>
    rw [decT] at h
    by_cases hn : n = 0
    · simp [hn] at h
    · simp only [dif_neg hn] at h
      set p := (n - 1).unpair with hp
      have hp2 : p.2 < n := lt_of_le_of_lt (Nat.unpair_right_le (n - 1)) (by omega)
      have hpair : Nat.pair p.1 p.2 + 1 = n := by
        rw [hp, Nat.pair_unpair]; omega
      rcases h1 : p.1 with _ | _ | _ | _ | _ | _ | _ | _ | k
      · simp [h1] at h; subst h; simpa [encT, h1] using hpair
      · simp [h1] at h; subst h; simpa [encT, h1] using hpair
      · simp [h1] at h; rcases h with ⟨h0, rfl⟩; simpa [encT, h1, h0] using hpair
      · simp [h1] at h; rcases h with ⟨h0, rfl⟩; simpa [encT, h1, h0] using hpair
      · simp [h1] at h; rcases h with ⟨u, hu, rfl⟩
        rw [encT, ih p.2 hp2 hu]; simpa [h1] using hpair
      · simp [h1] at h; rcases h with ⟨u, hu, rfl⟩
        rw [encT, ih p.2 hp2 hu]; simpa [h1] using hpair
      · simp only [h1] at h
        have ha : p.2.unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le p.2) hp2
        have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
        cases hA : decT p.2.unpair.1 with
        | none => simp [hA] at h
        | some t₁ =>
          cases hB : decT p.2.unpair.2 with
          | none => simp [hA, hB] at h
          | some t₂ =>
            simp [hA, hB] at h; subst h
            rw [encT, ih _ ha hA, ih _ hb hB, Nat.pair_unpair]
            simpa [h1] using hpair
      · simp only [h1] at h
        have ha : p.2.unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le p.2) hp2
        have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
        cases hA : decT p.2.unpair.1 with
        | none => simp [hA] at h
        | some t₁ =>
          cases hB : decT p.2.unpair.2 with
          | none => simp [hA, hB] at h
          | some t₂ =>
            simp [hA, hB] at h; subst h
            rw [encT, ih _ ha hA, ih _ hb hB, Nat.pair_unpair]
            simpa [h1] using hpair
      · simp [h1] at h

def decF (n : ℕ) : Option OForm :=
  if h : n = 0 then none
  else
    let p := (n - 1).unpair
    have hp2 : p.2 < n := by
      have : p.2 ≤ n - 1 := Nat.unpair_right_le (n - 1)
      omega
    match p.1 with
    | 0 => if p.2 = 0 then some .bot else none
    | 1 =>
      match decT p.2.unpair.1, decT p.2.unpair.2 with
      | some t₁, some t₂ => some (.eq t₁ t₂)
      | _, _ => none
    | 2 =>
      match decT p.2.unpair.1, decT p.2.unpair.2 with
      | some t₁, some t₂ => some (.le t₁ t₂)
      | _, _ => none
    | 3 =>
      have ha : p.2.unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le p.2) hp2
      have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
      match decF p.2.unpair.1, decF p.2.unpair.2 with
      | some φ, some ψ => some (.imp φ ψ)
      | _, _ => none
    | 4 =>
      have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
      (decF p.2.unpair.2).map (.all p.2.unpair.1)
    | _ => none
termination_by n

lemma decF_encF (φ : OForm) : decF (encF φ) = some φ := by
  induction φ with
  | bot => rw [encF, decF]; simp
  | eq t₁ t₂ => rw [encF, decF]; simp [decT_encT]
  | le t₁ t₂ => rw [encF, decF]; simp [decT_encT]
  | imp φ ψ ih₁ ih₂ => rw [encF, decF]; simp [ih₁, ih₂]
  | all k φ ih => rw [encF, decF]; simp [ih]

lemma encF_injective : Function.Injective encF := fun a b h => by
  have := congrArg decF h
  rw [decF_encF, decF_encF] at this
  exact Option.some.inj this

lemma encF_decF {n : ℕ} {φ : OForm} (h : decF n = some φ) : encF φ = n := by
  induction n using Nat.strong_induction_on generalizing φ with
  | h n ih =>
    rw [decF] at h
    by_cases hn : n = 0
    · simp [hn] at h
    · simp only [dif_neg hn] at h
      set p := (n - 1).unpair with hp
      have hp2 : p.2 < n := lt_of_le_of_lt (Nat.unpair_right_le (n - 1)) (by omega)
      have hpair : Nat.pair p.1 p.2 + 1 = n := by
        rw [hp, Nat.pair_unpair]; omega
      rcases h1 : p.1 with _ | _ | _ | _ | _ | k
      · simp [h1] at h; rcases h with ⟨h0, rfl⟩; simpa [encF, h1, h0] using hpair
      · simp only [h1] at h
        cases hA : decT p.2.unpair.1 with
        | none => simp [hA] at h
        | some t₁ =>
          cases hB : decT p.2.unpair.2 with
          | none => simp [hA, hB] at h
          | some t₂ =>
            simp [hA, hB] at h; subst h
            rw [encF, encT_decT hA, encT_decT hB, Nat.pair_unpair]
            simpa [h1] using hpair
      · simp only [h1] at h
        cases hA : decT p.2.unpair.1 with
        | none => simp [hA] at h
        | some t₁ =>
          cases hB : decT p.2.unpair.2 with
          | none => simp [hA, hB] at h
          | some t₂ =>
            simp [hA, hB] at h; subst h
            rw [encF, encT_decT hA, encT_decT hB, Nat.pair_unpair]
            simpa [h1] using hpair
      · simp only [h1] at h
        have ha : p.2.unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le p.2) hp2
        have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
        cases hA : decF p.2.unpair.1 with
        | none => simp [hA] at h
        | some φ₁ =>
          cases hB : decF p.2.unpair.2 with
          | none => simp [hA, hB] at h
          | some φ₂ =>
            simp [hA, hB] at h; subst h
            rw [encF, ih _ ha hA, ih _ hb hB, Nat.pair_unpair]
            simpa [h1] using hpair
      · simp only [h1] at h
        have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
        simp at h; rcases h with ⟨ψ, hψ, rfl⟩
        rw [encF, ih _ hb hψ, Nat.pair_unpair]
        simpa [h1] using hpair
      · simp [h1] at h

/- ### Schütte–Hintikka completeness for `SeqProv` -/

inductive HStep : Type
  | noop : HStep
  | impL (φ ψ : OForm) : HStep
  | impR (φ ψ : OForm) : HStep
  | allL (k : ℕ) (φ : OForm) (t : OTerm) : HStep
  | allR (k : ℕ) (φ : OForm) : HStep
  | eqRefl (t : OTerm) : HStep
  | eqSymm (t₁ t₂ : OTerm) : HStep
  | eqTrans (t₁ t₂ t₃ : OTerm) : HStep
  | congNeg (t₁ t₂ : OTerm) : HStep
  | congExp (t₁ t₂ : OTerm) : HStep
  | congAdd (t₁ s₁ t₂ s₂ : OTerm) : HStep
  | congMul (t₁ s₁ t₂ s₂ : OTerm) : HStep
  | congLe (t₁ s₁ t₂ s₂ : OTerm) : HStep

def enumStep (n : ℕ) : HStep :=
  let p := n.unpair
  let tag := p.1
  let b := p.2
  match tag with
  | 0 => match decF b.unpair.1, decF b.unpair.2 with
         | some φ, some ψ => .impL φ ψ | _, _ => .noop
  | 1 => match decF b.unpair.1, decF b.unpair.2 with
         | some φ, some ψ => .impR φ ψ | _, _ => .noop
  | 2 => match decF b.unpair.2.unpair.1, decT b.unpair.2.unpair.2 with
         | some φ, some t => .allL b.unpair.1 φ t | _, _ => .noop
  | 3 => match decF b.unpair.2 with
         | some φ => .allR b.unpair.1 φ | _ => .noop
  | 4 => match decT b with
         | some t => .eqRefl t | _ => .noop
  | 5 => match decT b.unpair.1, decT b.unpair.2 with
         | some t₁, some t₂ => .eqSymm t₁ t₂ | _, _ => .noop
  | 6 => match decT b.unpair.1, decT b.unpair.2.unpair.1, decT b.unpair.2.unpair.2 with
         | some t₁, some t₂, some t₃ => .eqTrans t₁ t₂ t₃ | _, _, _ => .noop
  | 7 => match decT b.unpair.1, decT b.unpair.2 with
         | some t₁, some t₂ => .congNeg t₁ t₂ | _, _ => .noop
  | 8 => match decT b.unpair.1, decT b.unpair.2 with
         | some t₁, some t₂ => .congExp t₁ t₂ | _, _ => .noop
  | 9 => match decT b.unpair.1.unpair.1, decT b.unpair.1.unpair.2,
               decT b.unpair.2.unpair.1, decT b.unpair.2.unpair.2 with
         | some t₁, some s₁, some t₂, some s₂ => .congAdd t₁ s₁ t₂ s₂ | _, _, _, _ => .noop
  | 10 => match decT b.unpair.1.unpair.1, decT b.unpair.1.unpair.2,
                decT b.unpair.2.unpair.1, decT b.unpair.2.unpair.2 with
          | some t₁, some s₁, some t₂, some s₂ => .congMul t₁ s₁ t₂ s₂ | _, _, _, _ => .noop
  | 11 => match decT b.unpair.1.unpair.1, decT b.unpair.1.unpair.2,
                decT b.unpair.2.unpair.1, decT b.unpair.2.unpair.2 with
          | some t₁, some s₁, some t₂, some s₂ => .congLe t₁ s₁ t₂ s₂ | _, _, _, _ => .noop
  | _ => .noop

lemma enumStep_surj (s : HStep) : ∃ m : ℕ, enumStep m = s := by
  cases s with
  | noop => exact ⟨Nat.pair 12 0, by simp [enumStep]⟩
  | impL φ ψ => exact ⟨Nat.pair 0 (Nat.pair (encF φ) (encF ψ)), by simp [enumStep, decF_encF]⟩
  | impR φ ψ => exact ⟨Nat.pair 1 (Nat.pair (encF φ) (encF ψ)), by simp [enumStep, decF_encF]⟩
  | allL k φ t =>
    exact ⟨Nat.pair 2 (Nat.pair k (Nat.pair (encF φ) (encT t))),
      by simp [enumStep, decF_encF, decT_encT]⟩
  | allR k φ => exact ⟨Nat.pair 3 (Nat.pair k (encF φ)), by simp [enumStep, decF_encF]⟩
  | eqRefl t => exact ⟨Nat.pair 4 (encT t), by simp [enumStep, decT_encT]⟩
  | eqSymm t₁ t₂ =>
    exact ⟨Nat.pair 5 (Nat.pair (encT t₁) (encT t₂)), by simp [enumStep, decT_encT]⟩
  | eqTrans t₁ t₂ t₃ =>
    exact ⟨Nat.pair 6 (Nat.pair (encT t₁) (Nat.pair (encT t₂) (encT t₃))),
      by simp [enumStep, decT_encT]⟩
  | congNeg t₁ t₂ =>
    exact ⟨Nat.pair 7 (Nat.pair (encT t₁) (encT t₂)), by simp [enumStep, decT_encT]⟩
  | congExp t₁ t₂ =>
    exact ⟨Nat.pair 8 (Nat.pair (encT t₁) (encT t₂)), by simp [enumStep, decT_encT]⟩
  | congAdd t₁ s₁ t₂ s₂ =>
    exact ⟨Nat.pair 9 (Nat.pair (Nat.pair (encT t₁) (encT s₁)) (Nat.pair (encT t₂) (encT s₂))),
      by simp [enumStep, decT_encT]⟩
  | congMul t₁ s₁ t₂ s₂ =>
    exact ⟨Nat.pair 10 (Nat.pair (Nat.pair (encT t₁) (encT s₁)) (Nat.pair (encT t₂) (encT s₂))),
      by simp [enumStep, decT_encT]⟩
  | congLe t₁ s₁ t₂ s₂ =>
    exact ⟨Nat.pair 11 (Nat.pair (Nat.pair (encT t₁) (encT s₁)) (Nat.pair (encT t₂) (encT s₂))),
      by simp [enumStep, decT_encT]⟩

lemma exists_step_ge (s : HStep) (N : ℕ) : ∃ n ≥ N, enumStep n.unpair.1 = s := by
  obtain ⟨m, hm⟩ := enumStep_surj s
  refine ⟨Nat.pair m N, Nat.right_le_pair m N, ?_⟩
  simp [hm]

def freshVar (Γ Δ : List OForm) : ℕ :=
  (Γ ++ Δ).foldl (fun acc φ => max acc φ.maxFVar) 0

lemma freshVar_spec (Γ Δ : List OForm) :
    (∀ φ ∈ Γ, φ.hasFVar (freshVar Γ Δ) = false) ∧
    (∀ φ ∈ Δ, φ.hasFVar (freshVar Γ Δ) = false) := by
  have hfold : ∀ (l : List OForm) (init : ℕ),
      init ≤ l.foldl (fun acc φ => max acc φ.maxFVar) init ∧
      ∀ φ ∈ l, φ.maxFVar ≤ l.foldl (fun acc φ => max acc φ.maxFVar) init := by
    intro l
    induction l with
    | nil => intro init; exact ⟨le_rfl, fun _ h => by simp at h⟩
    | cons a l ih =>
      intro init
      obtain ⟨h1, h2⟩ := ih (max init a.maxFVar)
      refine ⟨le_trans (le_max_left _ _) h1, fun φ hφ => ?_⟩
      rcases List.mem_cons.mp hφ with rfl | hφ'
      · exact le_trans (le_max_right _ _) h1
      · exact h2 φ hφ'
  have hall := (hfold (Γ ++ Δ) 0).2
  constructor
  · intro φ hφ
    exact φ.hasFVar_eq_false_of_le (hall φ (List.mem_append_left Δ hφ))
  · intro φ hφ
    exact φ.hasFVar_eq_false_of_le (hall φ (List.mem_append_right Γ hφ))

open scoped Classical in
noncomputable def satStep (s : HStep) (st : List OForm × List OForm) :
    List OForm × List OForm :=
  let Γ := st.1
  let Δ := st.2
  match s with
  | .noop => (Γ, Δ)
  | .impL φ ψ =>
    if OForm.imp φ ψ ∈ Γ then
      if ¬ SeqProv Γ (φ :: Δ) then (Γ, φ :: Δ) else (ψ :: Γ, Δ)
    else (Γ, Δ)
  | .impR φ ψ =>
    if OForm.imp φ ψ ∈ Δ then (φ :: Γ, ψ :: Δ) else (Γ, Δ)
  | .allL k φ t =>
    if OForm.all k φ ∈ Γ ∧ t.noBVar = true then (φ.substB k t :: Γ, Δ) else (Γ, Δ)
  | .allR k φ =>
    if OForm.all k φ ∈ Δ then (Γ, φ.substB k (.fvar (freshVar Γ Δ)) :: Δ) else (Γ, Δ)
  | .eqRefl t =>
    if t.noBVar = true then (.eq t t :: Γ, Δ) else (Γ, Δ)
  | .eqSymm t₁ t₂ =>
    if OForm.eq t₁ t₂ ∈ Γ then (.eq t₂ t₁ :: Γ, Δ) else (Γ, Δ)
  | .eqTrans t₁ t₂ t₃ =>
    if OForm.eq t₁ t₂ ∈ Γ ∧ OForm.eq t₂ t₃ ∈ Γ then (.eq t₁ t₃ :: Γ, Δ) else (Γ, Δ)
  | .congNeg t₁ t₂ =>
    if OForm.eq t₁ t₂ ∈ Γ then (.eq (.neg t₁) (.neg t₂) :: Γ, Δ) else (Γ, Δ)
  | .congExp t₁ t₂ =>
    if OForm.eq t₁ t₂ ∈ Γ then (.eq (.exp t₁) (.exp t₂) :: Γ, Δ) else (Γ, Δ)
  | .congAdd t₁ s₁ t₂ s₂ =>
    if OForm.eq t₁ s₁ ∈ Γ ∧ OForm.eq t₂ s₂ ∈ Γ then
      (.eq (.add t₁ t₂) (.add s₁ s₂) :: Γ, Δ)
    else (Γ, Δ)
  | .congMul t₁ s₁ t₂ s₂ =>
    if OForm.eq t₁ s₁ ∈ Γ ∧ OForm.eq t₂ s₂ ∈ Γ then
      (.eq (.mul t₁ t₂) (.mul s₁ s₂) :: Γ, Δ)
    else (Γ, Δ)
  | .congLe t₁ s₁ t₂ s₂ =>
    if OForm.eq t₁ s₁ ∈ Γ ∧ OForm.eq t₂ s₂ ∈ Γ ∧ OForm.le t₁ t₂ ∈ Γ then
      (.le s₁ s₂ :: Γ, Δ)
    else (Γ, Δ)

open scoped Classical in
lemma satStep_preserves (s : HStep) (st : List OForm × List OForm)
    (hnp : ¬ SeqProv st.1 st.2) :
    ¬ SeqProv (satStep s st).1 (satStep s st).2 := by
  rcases st with ⟨Γ, Δ⟩
  cases s with
  | noop => exact hnp
  | impL φ ψ =>
    simp only [satStep]
    by_cases h1 : OForm.imp φ ψ ∈ Γ
    · by_cases h2 : ¬ SeqProv Γ (φ :: Δ)
      · simp [h1, h2]
      · simp only [h1, h2, ↓reduceIte]
        push Not at h2
        intro h3
        exact hnp (SeqProv.impL h1 h2 h3)
    · simp [h1, hnp]
  | impR φ ψ =>
    simp only [satStep]
    split_ifs with h1
    · intro h2; exact hnp (SeqProv.impR h1 h2)
    · exact hnp
  | allL k φ t =>
    simp only [satStep]
    split_ifs with h1
    · intro h2; exact hnp (SeqProv.allL h1.1 h1.2 h2)
    · exact hnp
  | allR k φ =>
    simp only [satStep]
    split_ifs with h1
    · intro h2
      obtain ⟨hf1, hf2⟩ := freshVar_spec Γ Δ
      exact hnp (SeqProv.allR h1 hf1 hf2 h2)
    · exact hnp
  | eqRefl t =>
    simp only [satStep]
    split_ifs with h1
    · intro h2; exact hnp (SeqProv.eqRefl h1 h2)
    · exact hnp
  | eqSymm t₁ t₂ =>
    simp only [satStep]
    split_ifs with h1
    · intro h2; exact hnp (SeqProv.eqSymm h1 h2)
    · exact hnp
  | eqTrans t₁ t₂ t₃ =>
    simp only [satStep]
    split_ifs with h1
    · intro h2; exact hnp (SeqProv.eqTrans h1.1 h1.2 h2)
    · exact hnp
  | congNeg t₁ t₂ =>
    simp only [satStep]
    split_ifs with h1
    · intro h2; exact hnp (SeqProv.congNeg h1 h2)
    · exact hnp
  | congExp t₁ t₂ =>
    simp only [satStep]
    split_ifs with h1
    · intro h2; exact hnp (SeqProv.congExp h1 h2)
    · exact hnp
  | congAdd t₁ s₁ t₂ s₂ =>
    simp only [satStep]
    split_ifs with h1
    · intro h2; exact hnp (SeqProv.congAdd h1.1 h1.2 h2)
    · exact hnp
  | congMul t₁ s₁ t₂ s₂ =>
    simp only [satStep]
    split_ifs with h1
    · intro h2; exact hnp (SeqProv.congMul h1.1 h1.2 h2)
    · exact hnp
  | congLe t₁ s₁ t₂ s₂ =>
    simp only [satStep]
    split_ifs with h1
    · intro h2; exact hnp (SeqProv.congLe h1.1 h1.2.1 h1.2.2 h2)
    · exact hnp

open scoped Classical in
lemma satStep_mono (s : HStep) (st : List OForm × List OForm) :
    (∀ φ ∈ st.1, φ ∈ (satStep s st).1) ∧ (∀ φ ∈ st.2, φ ∈ (satStep s st).2) := by
  rcases st with ⟨Γ, Δ⟩
  cases s <;> simp only [satStep] <;> repeat split_ifs
  all_goals exact ⟨fun _ h => by simp [h], fun _ h => by simp [h]⟩

open scoped Classical in
lemma satStep_closed (s : HStep) (st : List OForm × List OForm)
    (hc1 : ∀ φ ∈ st.1, φ.closedAt []) (hc2 : ∀ φ ∈ st.2, φ.closedAt []) :
    (∀ φ ∈ (satStep s st).1, φ.closedAt []) ∧ (∀ φ ∈ (satStep s st).2, φ.closedAt []) := by
  rcases st with ⟨Γ, Δ⟩
  dsimp only at hc1 hc2 ⊢
  cases s with
  | noop => exact ⟨hc1, hc2⟩
  | impL φ ψ =>
    simp only [satStep]
    by_cases h1 : OForm.imp φ ψ ∈ Γ
    · by_cases h2 : ¬ SeqProv Γ (φ :: Δ)
      · simp only [h1, h2, ↓reduceIte]
        refine ⟨hc1, fun χ hχ => ?_⟩
        rcases List.mem_cons.mp hχ with rfl | hχ'
        · exact (hc1 _ h1).1
        · exact hc2 _ hχ'
      · simp only [h1, h2, ↓reduceIte]
        refine ⟨fun χ hχ => ?_, hc2⟩
        rcases List.mem_cons.mp hχ with rfl | hχ'
        · exact (hc1 _ h1).2
        · exact hc1 _ hχ'
    · simp only [h1, ↓reduceIte]; exact ⟨hc1, hc2⟩
  | impR φ ψ =>
    simp only [satStep]
    split_ifs with h1
    · refine ⟨fun χ hχ => ?_, fun χ hχ => ?_⟩
      · rcases List.mem_cons.mp hχ with rfl | hχ'
        · exact (hc2 _ h1).1
        · exact hc1 _ hχ'
      · rcases List.mem_cons.mp hχ with rfl | hχ'
        · exact (hc2 _ h1).2
        · exact hc2 _ hχ'
    · exact ⟨hc1, hc2⟩
  | allL k φ t =>
    simp only [satStep]
    split_ifs with h1
    · refine ⟨fun χ hχ => ?_, hc2⟩
      rcases List.mem_cons.mp hχ with rfl | hχ'
      · exact OForm.closedAt_substB (hc1 _ h1.1) h1.2
      · exact hc1 _ hχ'
    · exact ⟨hc1, hc2⟩
  | allR k φ =>
    simp only [satStep]
    split_ifs with h1
    · refine ⟨hc1, fun χ hχ => ?_⟩
      rcases List.mem_cons.mp hχ with rfl | hχ'
      · exact OForm.closedAt_substB (hc2 _ h1) rfl
      · exact hc2 _ hχ'
    · exact ⟨hc1, hc2⟩
  | eqRefl t =>
    simp only [satStep]
    split_ifs with h1
    · refine ⟨fun χ hχ => ?_, hc2⟩
      rcases List.mem_cons.mp hχ with rfl | hχ'
      · have ht := (OTerm.bvarsSub_nil_iff t).mpr h1
        exact ⟨ht, ht⟩
      · exact hc1 _ hχ'
    · exact ⟨hc1, hc2⟩
  | eqSymm t₁ t₂ =>
    simp only [satStep]
    split_ifs with h1
    · refine ⟨fun χ hχ => ?_, hc2⟩
      rcases List.mem_cons.mp hχ with rfl | hχ'
      · exact ⟨(hc1 _ h1).2, (hc1 _ h1).1⟩
      · exact hc1 _ hχ'
    · exact ⟨hc1, hc2⟩
  | eqTrans t₁ t₂ t₃ =>
    simp only [satStep]
    split_ifs with h1
    · refine ⟨fun χ hχ => ?_, hc2⟩
      rcases List.mem_cons.mp hχ with rfl | hχ'
      · exact ⟨(hc1 _ h1.1).1, (hc1 _ h1.2).2⟩
      · exact hc1 _ hχ'
    · exact ⟨hc1, hc2⟩
  | congNeg t₁ t₂ =>
    simp only [satStep]
    split_ifs with h1
    · refine ⟨fun χ hχ => ?_, hc2⟩
      rcases List.mem_cons.mp hχ with rfl | hχ'
      · exact ⟨(hc1 _ h1).1, (hc1 _ h1).2⟩
      · exact hc1 _ hχ'
    · exact ⟨hc1, hc2⟩
  | congExp t₁ t₂ =>
    simp only [satStep]
    split_ifs with h1
    · refine ⟨fun χ hχ => ?_, hc2⟩
      rcases List.mem_cons.mp hχ with rfl | hχ'
      · exact ⟨(hc1 _ h1).1, (hc1 _ h1).2⟩
      · exact hc1 _ hχ'
    · exact ⟨hc1, hc2⟩
  | congAdd t₁ s₁ t₂ s₂ =>
    simp only [satStep]
    split_ifs with h1
    · refine ⟨fun χ hχ => ?_, hc2⟩
      rcases List.mem_cons.mp hχ with rfl | hχ'
      · exact ⟨⟨(hc1 _ h1.1).1, (hc1 _ h1.2).1⟩, ⟨(hc1 _ h1.1).2, (hc1 _ h1.2).2⟩⟩
      · exact hc1 _ hχ'
    · exact ⟨hc1, hc2⟩
  | congMul t₁ s₁ t₂ s₂ =>
    simp only [satStep]
    split_ifs with h1
    · refine ⟨fun χ hχ => ?_, hc2⟩
      rcases List.mem_cons.mp hχ with rfl | hχ'
      · exact ⟨⟨(hc1 _ h1.1).1, (hc1 _ h1.2).1⟩, ⟨(hc1 _ h1.1).2, (hc1 _ h1.2).2⟩⟩
      · exact hc1 _ hχ'
    · exact ⟨hc1, hc2⟩
  | congLe t₁ s₁ t₂ s₂ =>
    simp only [satStep]
    split_ifs with h1
    · refine ⟨fun χ hχ => ?_, hc2⟩
      rcases List.mem_cons.mp hχ with rfl | hχ'
      · exact ⟨(hc1 _ h1.1).2, (hc1 _ h1.2.1).2⟩
      · exact hc1 _ hχ'
    · exact ⟨hc1, hc2⟩

noncomputable def satChain (Γ₀ Δ₀ : List OForm) : ℕ → List OForm × List OForm
  | 0 => (Γ₀, Δ₀)
  | n + 1 => satStep (enumStep n.unpair.1) (satChain Γ₀ Δ₀ n)

lemma satChain_mono (Γ₀ Δ₀ : List OForm) {i j : ℕ} (hij : i ≤ j) :
    (∀ φ ∈ (satChain Γ₀ Δ₀ i).1, φ ∈ (satChain Γ₀ Δ₀ j).1) ∧
    (∀ φ ∈ (satChain Γ₀ Δ₀ i).2, φ ∈ (satChain Γ₀ Δ₀ j).2) := by
  induction hij with
  | refl => exact ⟨fun _ h => h, fun _ h => h⟩
  | @step m _ ih =>
    obtain ⟨h1, h2⟩ := satStep_mono (enumStep m.unpair.1) (satChain Γ₀ Δ₀ m)
    exact ⟨fun φ h => h1 φ (ih.1 φ h), fun φ h => h2 φ (ih.2 φ h)⟩

lemma satChain_not_prov {Γ₀ Δ₀ : List OForm} (hnp : ¬ SeqProv Γ₀ Δ₀) (n : ℕ) :
    ¬ SeqProv (satChain Γ₀ Δ₀ n).1 (satChain Γ₀ Δ₀ n).2 := by
  induction n with
  | zero => exact hnp
  | succ n ih => exact satStep_preserves _ _ ih

lemma satChain_closed {Γ₀ Δ₀ : List OForm}
    (hc1 : ∀ φ ∈ Γ₀, φ.closedAt []) (hc2 : ∀ φ ∈ Δ₀, φ.closedAt []) (n : ℕ) :
    (∀ φ ∈ (satChain Γ₀ Δ₀ n).1, φ.closedAt []) ∧
    (∀ φ ∈ (satChain Γ₀ Δ₀ n).2, φ.closedAt []) := by
  induction n with
  | zero => exact ⟨hc1, hc2⟩
  | succ n ih => exact satStep_closed _ _ ih.1 ih.2

abbrev ClosedTerm := {t : OTerm // t.noBVar = true}

open scoped Classical in
theorem SeqProv.complete {Γ₀ Δ₀ : List OForm}
    (hc1 : ∀ φ ∈ Γ₀, φ.closedAt []) (hc2 : ∀ φ ∈ Δ₀, φ.closedAt [])
    (hnp : ¬ SeqProv Γ₀ Δ₀) :
    ∃ (M : Type) (_ : Nonempty M) (_ : L.Structure M) (ρ σ : ℕ → M),
      (∀ φ ∈ Γ₀, φ.Realize M ρ σ) ∧ (∀ ψ ∈ Δ₀, ¬ ψ.Realize M ρ σ) := by
  let Γinf : Set OForm := {φ | ∃ n, φ ∈ (satChain Γ₀ Δ₀ n).1}
  let Δinf : Set OForm := {φ | ∃ n, φ ∈ (satChain Γ₀ Δ₀ n).2}
  have hdisj : ∀ φ, φ ∈ Γinf → φ ∈ Δinf → False := by
    rintro φ ⟨i, hi⟩ ⟨j, hj⟩
    exact satChain_not_prov hnp (max i j)
      (SeqProv.ax ((satChain_mono Γ₀ Δ₀ (le_max_left i j)).1 φ hi)
                  ((satChain_mono Γ₀ Δ₀ (le_max_right i j)).2 φ hj))
  have hbot : OForm.bot ∉ Γinf := by
    rintro ⟨i, hi⟩
    exact satChain_not_prov hnp i (SeqProv.botL hi)
  have hrefl : ∀ t : ClosedTerm, OForm.eq t.1 t.1 ∈ Γinf := by
    intro t
    obtain ⟨n, -, hn⟩ := exists_step_ge (.eqRefl t.1) 0
    refine ⟨n + 1, ?_⟩
    simp [satChain, hn, satStep, t.2]
  have hsymm : ∀ t₁ t₂ : OTerm, OForm.eq t₁ t₂ ∈ Γinf → OForm.eq t₂ t₁ ∈ Γinf := by
    rintro t₁ t₂ ⟨i, hi⟩
    obtain ⟨n, hni, hn⟩ := exists_step_ge (.eqSymm t₁ t₂) i
    refine ⟨n + 1, ?_⟩
    have hm := (satChain_mono Γ₀ Δ₀ hni).1 _ hi
    simp [satChain, hn, satStep, hm]
  have htrans : ∀ t₁ t₂ t₃ : OTerm, OForm.eq t₁ t₂ ∈ Γinf → OForm.eq t₂ t₃ ∈ Γinf →
      OForm.eq t₁ t₃ ∈ Γinf := by
    rintro t₁ t₂ t₃ ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨n, hni, hn⟩ := exists_step_ge (.eqTrans t₁ t₂ t₃) (max i j)
    refine ⟨n + 1, ?_⟩
    have hm1 := (satChain_mono Γ₀ Δ₀ (le_trans (le_max_left i j) hni)).1 _ hi
    have hm2 := (satChain_mono Γ₀ Δ₀ (le_trans (le_max_right i j) hni)).1 _ hj
    simp [satChain, hn, satStep, hm1, hm2]
  have hcongNeg : ∀ t₁ t₂ : OTerm, OForm.eq t₁ t₂ ∈ Γinf →
      OForm.eq (.neg t₁) (.neg t₂) ∈ Γinf := by
    rintro t₁ t₂ ⟨i, hi⟩
    obtain ⟨n, hni, hn⟩ := exists_step_ge (.congNeg t₁ t₂) i
    refine ⟨n + 1, ?_⟩
    have hm := (satChain_mono Γ₀ Δ₀ hni).1 _ hi
    simp [satChain, hn, satStep, hm]
  have hcongExp : ∀ t₁ t₂ : OTerm, OForm.eq t₁ t₂ ∈ Γinf →
      OForm.eq (.exp t₁) (.exp t₂) ∈ Γinf := by
    rintro t₁ t₂ ⟨i, hi⟩
    obtain ⟨n, hni, hn⟩ := exists_step_ge (.congExp t₁ t₂) i
    refine ⟨n + 1, ?_⟩
    have hm := (satChain_mono Γ₀ Δ₀ hni).1 _ hi
    simp [satChain, hn, satStep, hm]
  have hcongAdd : ∀ t₁ s₁ t₂ s₂ : OTerm, OForm.eq t₁ s₁ ∈ Γinf → OForm.eq t₂ s₂ ∈ Γinf →
      OForm.eq (.add t₁ t₂) (.add s₁ s₂) ∈ Γinf := by
    rintro t₁ s₁ t₂ s₂ ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨n, hni, hn⟩ := exists_step_ge (.congAdd t₁ s₁ t₂ s₂) (max i j)
    refine ⟨n + 1, ?_⟩
    have hm1 := (satChain_mono Γ₀ Δ₀ (le_trans (le_max_left i j) hni)).1 _ hi
    have hm2 := (satChain_mono Γ₀ Δ₀ (le_trans (le_max_right i j) hni)).1 _ hj
    simp [satChain, hn, satStep, hm1, hm2]
  have hcongMul : ∀ t₁ s₁ t₂ s₂ : OTerm, OForm.eq t₁ s₁ ∈ Γinf → OForm.eq t₂ s₂ ∈ Γinf →
      OForm.eq (.mul t₁ t₂) (.mul s₁ s₂) ∈ Γinf := by
    rintro t₁ s₁ t₂ s₂ ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨n, hni, hn⟩ := exists_step_ge (.congMul t₁ s₁ t₂ s₂) (max i j)
    refine ⟨n + 1, ?_⟩
    have hm1 := (satChain_mono Γ₀ Δ₀ (le_trans (le_max_left i j) hni)).1 _ hi
    have hm2 := (satChain_mono Γ₀ Δ₀ (le_trans (le_max_right i j) hni)).1 _ hj
    simp [satChain, hn, satStep, hm1, hm2]
  have hcongLe : ∀ t₁ s₁ t₂ s₂ : OTerm, OForm.eq t₁ s₁ ∈ Γinf → OForm.eq t₂ s₂ ∈ Γinf →
      OForm.le t₁ t₂ ∈ Γinf → OForm.le s₁ s₂ ∈ Γinf := by
    rintro t₁ s₁ t₂ s₂ ⟨i, hi⟩ ⟨j, hj⟩ ⟨l, hl⟩
    obtain ⟨n, hni, hn⟩ := exists_step_ge (.congLe t₁ s₁ t₂ s₂) (max (max i j) l)
    refine ⟨n + 1, ?_⟩
    have hm1 := (satChain_mono Γ₀ Δ₀ (le_trans (le_trans (le_max_left i j) (le_max_left _ l)) hni)).1 _ hi
    have hm2 := (satChain_mono Γ₀ Δ₀ (le_trans (le_trans (le_max_right i j) (le_max_left _ l)) hni)).1 _ hj
    have hm3 := (satChain_mono Γ₀ Δ₀ (le_trans (le_max_right _ l) hni)).1 _ hl
    simp [satChain, hn, satStep, hm1, hm2, hm3]
  let setoid : Setoid ClosedTerm :=
    { r := fun a b => OForm.eq a.1 b.1 ∈ Γinf
      iseqv :=
        { refl := hrefl
          symm := fun h => hsymm _ _ h
          trans := fun h1 h2 => htrans _ _ _ h1 h2 } }
  letI : Setoid ClosedTerm := setoid
  let M : Type := Quotient setoid
  letI : Nonempty M := ⟨⟦⟨.zero, rfl⟩⟧⟩
  letI strM : L.Structure M :=
    { funMap := fun {n} f v =>
        match n, f with
        | _, Sum.inl ringFunc.zero => ⟦⟨.zero, rfl⟩⟧
        | _, Sum.inl ringFunc.one => ⟦⟨.one, rfl⟩⟧
        | _, Sum.inl ringFunc.neg =>
          Quotient.lift (fun t : ClosedTerm => (⟦⟨.neg t.1, t.2⟩⟧ : M))
            (fun a b hab => Quotient.sound (hcongNeg a.1 b.1 hab)) (v 0)
        | _, Sum.inr (Sum.inl expFunc.exp) =>
          Quotient.lift (fun t : ClosedTerm => (⟦⟨.exp t.1, t.2⟩⟧ : M))
            (fun a b hab => Quotient.sound (hcongExp a.1 b.1 hab)) (v 0)
        | _, Sum.inl ringFunc.add =>
          Quotient.lift₂ (fun a b : ClosedTerm =>
            (⟦⟨.add a.1 b.1, Bool.and_eq_true _ _ |>.mpr ⟨a.2, b.2⟩⟩⟧ : M))
            (fun a₁ b₁ a₂ b₂ ha hb => Quotient.sound (hcongAdd a₁.1 a₂.1 b₁.1 b₂.1 ha hb))
            (v 0) (v 1)
        | _, Sum.inl ringFunc.mul =>
          Quotient.lift₂ (fun a b : ClosedTerm =>
            (⟦⟨.mul a.1 b.1, Bool.and_eq_true _ _ |>.mpr ⟨a.2, b.2⟩⟩⟧ : M))
            (fun a₁ b₁ a₂ b₂ ha hb => Quotient.sound (hcongMul a₁.1 a₂.1 b₁.1 b₂.1 ha hb))
            (v 0) (v 1)
        | _, Sum.inr (Sum.inr r) => Empty.elim r
      RelMap := fun {n} r v =>
        match n, r with
        | _, Sum.inl r => Empty.elim r
        | _, Sum.inr (Sum.inl r) => Empty.elim r
        | _, Sum.inr (Sum.inr r) =>
          match r with
          | orderRel.le =>
            Quotient.lift₂ (fun a b : ClosedTerm => OForm.le a.1 b.1 ∈ Γinf)
              (fun a₁ b₁ a₂ b₂ ha hb => propext
                ⟨fun h => hcongLe a₁.1 a₂.1 b₁.1 b₂.1 ha hb h,
                 fun h => hcongLe a₂.1 a₁.1 b₂.1 b₁.1 (hsymm _ _ ha) (hsymm _ _ hb) h⟩)
              (v 0) (v 1) }
  let ρ : ℕ → M := fun v => ⟦⟨.fvar v, rfl⟩⟧
  let σ : ℕ → M := fun _ => ⟦⟨.zero, rfl⟩⟧
  have heval : ∀ (t : ClosedTerm), t.1.eval M ρ σ = ⟦t⟧ := by
    rintro ⟨t, ht⟩
    induction t with
    | fvar v => rfl
    | bvar _ => simp [OTerm.noBVar] at ht
    | zero => rfl
    | one => rfl
    | neg t ih =>
      change Structure.funMap (L := L) fNeg ![t.eval M ρ σ] = ⟦⟨.neg t, ht⟩⟧
      rw [ih ht]; rfl
    | exp t ih =>
      change Structure.funMap (L := L) fExp ![t.eval M ρ σ] = ⟦⟨.exp t, ht⟩⟧
      rw [ih ht]; rfl
    | add t₁ t₂ ih₁ ih₂ =>
      simp only [OTerm.noBVar, Bool.and_eq_true] at ht
      change Structure.funMap (L := L) fAdd ![t₁.eval M ρ σ, t₂.eval M ρ σ] = _
      rw [ih₁ ht.1, ih₂ ht.2]; rfl
    | mul t₁ t₂ ih₁ ih₂ =>
      simp only [OTerm.noBVar, Bool.and_eq_true] at ht
      change Structure.funMap (L := L) fMul ![t₁.eval M ρ σ, t₂.eval M ρ σ] = _
      rw [ih₁ ht.1, ih₂ ht.2]; rfl
  have himpL : ∀ φ ψ, OForm.imp φ ψ ∈ Γinf → φ ∈ Δinf ∨ ψ ∈ Γinf := by
    rintro φ ψ ⟨i, hi⟩
    obtain ⟨n, hni, hn⟩ := exists_step_ge (.impL φ ψ) i
    have hm := (satChain_mono Γ₀ Δ₀ hni).1 _ hi
    by_cases hbr : ¬ SeqProv (satChain Γ₀ Δ₀ n).1 (φ :: (satChain Γ₀ Δ₀ n).2)
    · left; refine ⟨n + 1, ?_⟩
      change φ ∈ (satStep (enumStep n.unpair.1) (satChain Γ₀ Δ₀ n)).2
      rw [hn]; simp [satStep, hm, hbr]
    · right; refine ⟨n + 1, ?_⟩
      change ψ ∈ (satStep (enumStep n.unpair.1) (satChain Γ₀ Δ₀ n)).1
      rw [hn]; simp [satStep, hm, hbr]
  have himpR : ∀ φ ψ, OForm.imp φ ψ ∈ Δinf → φ ∈ Γinf ∧ ψ ∈ Δinf := by
    rintro φ ψ ⟨i, hi⟩
    obtain ⟨n, hni, hn⟩ := exists_step_ge (.impR φ ψ) i
    have hm := (satChain_mono Γ₀ Δ₀ hni).2 _ hi
    exact ⟨⟨n + 1, by simp [satChain, hn, satStep, hm]⟩,
           ⟨n + 1, by simp [satChain, hn, satStep, hm]⟩⟩
  have hallL : ∀ k φ (t : ClosedTerm), OForm.all k φ ∈ Γinf → φ.substB k t.1 ∈ Γinf := by
    rintro k φ t ⟨i, hi⟩
    obtain ⟨n, hni, hn⟩ := exists_step_ge (.allL k φ t.1) i
    have hm := (satChain_mono Γ₀ Δ₀ hni).1 _ hi
    exact ⟨n + 1, by simp [satChain, hn, satStep, hm, t.2]⟩
  have hallR : ∀ k φ, OForm.all k φ ∈ Δinf → ∃ v : ℕ, φ.substB k (.fvar v) ∈ Δinf := by
    rintro k φ ⟨i, hi⟩
    obtain ⟨n, hni, hn⟩ := exists_step_ge (.allR k φ) i
    have hm := (satChain_mono Γ₀ Δ₀ hni).2 _ hi
    exact ⟨freshVar (satChain Γ₀ Δ₀ n).1 (satChain Γ₀ Δ₀ n).2,
      ⟨n + 1, by simp [satChain, hn, satStep, hm]⟩⟩
  have htruth : ∀ (sz : ℕ) (φ : OForm), φ.size = sz → φ.closedAt [] →
      (φ ∈ Γinf → φ.Realize M ρ σ) ∧ (φ ∈ Δinf → ¬ φ.Realize M ρ σ) := by
    intro sz
    induction sz using Nat.strong_induction_on with
    | h sz ih =>
      intro φ hsz hcl
      cases φ with
      | bot =>
        exact ⟨fun h => False.elim (hbot h), fun _ h => h⟩
      | eq t₁ t₂ =>
        have ht₁ : t₁.noBVar = true := (OTerm.bvarsSub_nil_iff t₁).mp hcl.1
        have ht₂ : t₂.noBVar = true := (OTerm.bvarsSub_nil_iff t₂).mp hcl.2
        constructor
        · intro h
          simp only [OForm.Realize, heval ⟨t₁, ht₁⟩, heval ⟨t₂, ht₂⟩]
          exact Quotient.sound h
        · intro h heq
          simp only [OForm.Realize, heval ⟨t₁, ht₁⟩, heval ⟨t₂, ht₂⟩] at heq
          exact hdisj _ (Quotient.exact heq) h
      | le t₁ t₂ =>
        have ht₁ : t₁.noBVar = true := (OTerm.bvarsSub_nil_iff t₁).mp hcl.1
        have ht₂ : t₂.noBVar = true := (OTerm.bvarsSub_nil_iff t₂).mp hcl.2
        constructor
        · intro h
          change Structure.RelMap (L := L) rLe ![t₁.eval M ρ σ, t₂.eval M ρ σ]
          rw [heval ⟨t₁, ht₁⟩, heval ⟨t₂, ht₂⟩]
          exact h
        · intro h hle
          change Structure.RelMap (L := L) rLe ![t₁.eval M ρ σ, t₂.eval M ρ σ] at hle
          rw [heval ⟨t₁, ht₁⟩, heval ⟨t₂, ht₂⟩] at hle
          exact hdisj _ hle h
      | imp φ₁ φ₂ =>
        have h1 := ih φ₁.size (by simp [OForm.size] at hsz; omega) φ₁ rfl hcl.1
        have h2 := ih φ₂.size (by simp [OForm.size] at hsz; omega) φ₂ rfl hcl.2
        constructor
        · intro h hφ₁
          rcases himpL φ₁ φ₂ h with hL | hR
          · exact False.elim (h1.2 hL hφ₁)
          · exact h2.1 hR
        · intro h himp
          obtain ⟨hL, hR⟩ := himpR φ₁ φ₂ h
          exact h2.2 hR (himp (h1.1 hL))
      | all k φ₁ =>
        constructor
        · intro h x
          refine Quotient.inductionOn x fun t => ?_
          have hsub := hallL k φ₁ t h
          have hsz' : (φ₁.substB k t.1).size < sz := by
            rw [OForm.size_substB]; simp [OForm.size] at hsz; omega
          have hcl' : (φ₁.substB k t.1).closedAt [] := OForm.closedAt_substB hcl t.2
          have hR := (ih _ hsz' _ rfl hcl').1 hsub
          have hR' := (OForm.realize_substB ρ σ t.2).mp hR
          rwa [heval t] at hR'
        · intro h hall
          obtain ⟨v, hv⟩ := hallR k φ₁ h
          have hsz' : (φ₁.substB k (.fvar v)).size < sz := by
            rw [OForm.size_substB]; simp [OForm.size] at hsz; omega
          have hcl' : (φ₁.substB k (.fvar v)).closedAt [] := OForm.closedAt_substB hcl rfl
          have hR := (ih _ hsz' _ rfl hcl').2 hv
          apply hR
          exact (OForm.realize_substB ρ σ rfl).mpr (hall ⟦⟨.fvar v, rfl⟩⟧)
  refine ⟨M, inferInstance, strM, ρ, σ, ?_, ?_⟩
  · intro φ hφ
    exact (htruth φ.size φ rfl (hc1 φ hφ)).1 ⟨0, hφ⟩
  · intro ψ hψ
    exact (htruth ψ.size ψ rfl (hc2 ψ hψ)).2 ⟨0, hψ⟩

lemma models_iff_exists_seqProv (T : L.Theory) (φ : L.Sentence) :
    T ⊨ᵇ φ ↔ ∃ Γ : List L.Sentence, (∀ ψ ∈ Γ, ψ ∈ T) ∧ SeqProv (Γ.map fromBF) [fromBF φ] := by
  classical
  constructor
  · intro hmod
    rw [Theory.models_iff_not_satisfiable, Theory.isSatisfiable_iff_isFinitelySatisfiable] at hmod
    unfold Theory.IsFinitelySatisfiable at hmod
    push Not at hmod
    obtain ⟨T0, hT0sub, hunsat⟩ := hmod
    set Γ : List L.Sentence := (T0.erase φ.not).toList
    have hΓT : ∀ ψ ∈ Γ, ψ ∈ T := by
      intro ψ hψ
      have h1 := Finset.mem_erase.mp (Finset.mem_toList.mp hψ)
      have h2 := hT0sub h1.2
      rcases h2 with hT | hneg
      · exact hT
      · exact False.elim (h1.1 (Set.mem_singleton_iff.mp hneg))
    refine ⟨Γ, hΓT, ?_⟩
    by_contra hnp
    have hc1 : ∀ χ ∈ Γ.map fromBF, χ.closedAt [] := by
      intro χ hχ
      obtain ⟨ψ, -, rfl⟩ := List.mem_map.mp hχ
      exact OForm.closedAt_range_of_isBounded (fromBF_isBounded ψ)
    have hc2 : ∀ χ ∈ [fromBF φ], χ.closedAt [] := by
      intro χ hχ
      rcases List.mem_singleton.mp hχ with rfl
      exact OForm.closedAt_range_of_isBounded (fromBF_isBounded φ)
    obtain ⟨M, _, _, ρ, σ, hMΓ, hMφ⟩ := SeqProv.complete hc1 hc2 hnp
    have hMT0 : M ⊨ (T0 : L.Theory) := by
      refine ⟨fun ψ hψ => ?_⟩
      by_cases heq : ψ = φ.not
      · subst heq
        rw [Sentence.realize_not]
        intro hφM
        exact hMφ (fromBF φ) (List.mem_singleton_self _) ((fromSent_realize ρ σ φ).mpr hφM)
      · have hψΓ : ψ ∈ Γ := Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨heq, hψ⟩)
        exact (fromSent_realize ρ σ ψ).mp (hMΓ (fromBF ψ) (List.mem_map_of_mem hψΓ))
    exact hunsat (Theory.Model.isSatisfiable M)
  · rintro ⟨Γ, hΓT, hprov⟩
    rw [Theory.models_sentence_iff]
    intro M
    let ρ : ℕ → M := fun _ => Classical.arbitrary M
    let σ : ℕ → M := fun _ => Classical.arbitrary M
    have hMΓ : ∀ χ ∈ Γ.map fromBF, χ.Realize M ρ σ := by
      intro χ hχ
      obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hχ
      exact (fromSent_realize ρ σ ψ).mpr (Theory.realize_sentence_of_mem T (hΓT ψ hψ))
    obtain ⟨χ, hχ, hχR⟩ := hprov.sound M ρ σ hMΓ
    rcases List.mem_singleton.mp hχ with rfl
    exact (fromSent_realize ρ σ φ).mp hχR

/- ## Section 3: Forward encoding to Mathlib `BoundedFormula.listEncode` and flat traces -/

def tListEnc : OTerm → List ℕ
  | .fvar _ => []
  | .bvar i => [2 * (2 * i + 1)]
  | .zero => [13]
  | .one => [17]
  | .neg t => 9 :: tListEnc t
  | .exp t => 3 :: tListEnc t
  | .add t₁ t₂ => 1 :: (tListEnc t₁ ++ tListEnc t₂)
  | .mul t₁ t₂ => 5 :: (tListEnc t₁ ++ tListEnc t₂)

def fListEnc (k : ℕ) : OForm → List ℕ
  | .bot => [4 * k + 11]
  | .eq t₁ t₂ =>
    [2 * Nat.pair k (encode (tListEnc t₁)), 2 * Nat.pair k (encode (tListEnc t₂))]
  | .le t₁ t₂ =>
    [13, 4 * k + 3, 2 * Nat.pair k (encode (tListEnc t₁)), 2 * Nat.pair k (encode (tListEnc t₂))]
  | .imp φ ψ => 3 :: (fListEnc k φ ++ fListEnc k ψ)
  | .all _ φ => 7 :: fListEnc (k + 1) φ

lemma encode_list_map {β : Type*} [Encodable β] (l : List β) :
    encode l = encode (l.map encode) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [Encodable.encode_list_cons, ih]

lemma term_listEncode_eq {k : ℕ} (t : L.Term (Empty ⊕ Fin k)) :
    t.listEncode.map encode = tListEnc (fromTerm t) := by
  induction t with
  | var v =>
    rcases v with e | i
    · exact Empty.elim e
    · simp only [Term.listEncode, fromTerm, tListEnc, List.map_cons, List.map_nil,
        encode_inl, encode_inr]
      rfl
  | func f ts ih =>
    rcases f with f | (f | f)
    · cases f
      · simp only [Term.listEncode, fromTerm, tListEnc, List.map_cons, List.finRange_succ,
          List.finRange_zero, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.map_append, Fin.succ_zero_eq_one]
        exact congrArg₂ List.cons rfl (congrArg₂ List.append (ih 0) (ih 1))
      · simp only [Term.listEncode, fromTerm, tListEnc, List.map_cons, List.finRange_succ,
          List.finRange_zero, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.map_append, Fin.succ_zero_eq_one]
        exact congrArg₂ List.cons rfl (congrArg₂ List.append (ih 0) (ih 1))
      · simp only [Term.listEncode, fromTerm, tListEnc, List.map_cons, List.finRange_succ,
          List.finRange_zero, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact congrArg₂ List.cons rfl (ih 0)
      · simp only [Term.listEncode, fromTerm, tListEnc, List.map_cons, List.finRange_zero,
          List.flatMap_nil, List.map_nil]
        rfl
      · simp only [Term.listEncode, fromTerm, tListEnc, List.map_cons, List.finRange_zero,
          List.flatMap_nil, List.map_nil]
        rfl
    · cases f
      simp only [Term.listEncode, fromTerm, tListEnc, List.map_cons, List.finRange_succ,
        List.finRange_zero, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact congrArg₂ List.cons rfl (ih 0)
    · exact Empty.elim f

lemma term_encode_eq {k : ℕ} (t : L.Term (Empty ⊕ Fin k)) :
    encode t = encode (tListEnc (fromTerm t)) := by
  change encode t.listEncode = _
  rw [encode_list_map, term_listEncode_eq]

lemma bf_listEncode_eq {k : ℕ} (φ : L.BoundedFormula Empty k) :
    φ.listEncode.map encode = fListEnc k (fromBF φ) := by
  induction φ with
  | @falsum k =>
    simp only [BoundedFormula.listEncode, fromBF, fListEnc, List.map_cons, List.map_nil]
    congr 1
    simp only [encode_inr, encode_nat]
    omega
  | @equal k t₁ t₂ =>
    simp only [BoundedFormula.listEncode, fromBF, fListEnc, List.map_cons, List.map_nil]
    simp only [encode_inl, encode_sigma_val, encode_nat, term_encode_eq]
  | @rel k l r ts =>
    rcases r with r | (r | r)
    · exact Empty.elim r
    · exact Empty.elim r
    · cases r
      simp only [BoundedFormula.listEncode, fromBF, fListEnc, List.cons_append, List.nil_append,
        List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil, Fin.succ_zero_eq_one]
      refine congrArg₂ List.cons rfl (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl)))
      · simp only [encode_inr, encode_nat]; omega
      · simp only [encode_inl, encode_sigma_val, encode_nat, term_encode_eq]
      · simp only [encode_inl, encode_sigma_val, encode_nat, term_encode_eq]
  | imp φ ψ ih₁ ih₂ =>
    simp only [BoundedFormula.listEncode, fromBF, fListEnc, List.cons_append, List.map_cons,
      List.map_append, ih₁, ih₂]
    rfl
  | all φ ih =>
    simp only [BoundedFormula.listEncode, fromBF, fListEnc, List.map_cons, ih]
    rfl

lemma sentence_encode_eq (φ : L.Sentence) :
    encode φ = encode (fListEnc 0 (fromBF φ)) := by
  change encode φ.listEncode = _
  rw [encode_list_map, bf_listEncode_eq]

lemma toSent_encode_eq (φ : OForm) (h : φ.isBounded 0 = true) :
    encode (toBF φ h : L.Sentence) = encode (fListEnc 0 φ) := by
  rw [sentence_encode_eq, fromBF_toBF φ h]

/- ### Code-level mirror operations on `ℕ` -/

def isValidTStep (l : List Bool) (n : ℕ) : Bool :=
  if n == 0 then false
  else
    let p := (n - 1).unpair
    match p.1 with
    | 0 => true
    | 1 => true
    | 2 => p.2 == 0
    | 3 => p.2 == 0
    | 4 => l.getD p.2 false
    | 5 => l.getD p.2 false
    | 6 => l.getD p.2.unpair.1 false && l.getD p.2.unpair.2 false
    | 7 => l.getD p.2.unpair.1 false && l.getD p.2.unpair.2 false
    | _ => false

def isValidTCode (n : ℕ) : Bool := (decT n).isSome

lemma isValidTCode_rec (n : ℕ) :
    isValidTStep ((List.range n).map isValidTCode) n = isValidTCode n := by
  have hget : ∀ m < n, ((List.range n).map isValidTCode).getD m false = isValidTCode m := fun m hm => by
    simp [List.getD, List.getElem?_map, List.getElem?_range hm]
  unfold isValidTStep; conv_rhs => unfold isValidTCode
  by_cases hn : n = 0
  · subst hn; rw [decT]; simp
  · simp only [beq_iff_eq, hn, ↓reduceIte]
    rw [decT, dif_neg hn]
    dsimp only
    set p := (n - 1).unpair with hp
    have hp2 : p.2 < n := lt_of_le_of_lt (Nat.unpair_right_le (n - 1)) (by omega)
    have ha : p.2.unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le p.2) hp2
    have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
    rcases h1 : p.1 with _ | _ | _ | _ | _ | _ | _ | _ | k <;> (try dsimp only)
    · rfl
    · rfl
    · cases p.2 <;> rfl
    · cases p.2 <;> rfl
    · rw [hget p.2 hp2]; simp [isValidTCode]
    · rw [hget p.2 hp2]; simp [isValidTCode]
    · rw [hget _ ha, hget _ hb]; unfold isValidTCode
      have aux : ∀ x y : Option OTerm,
          (x.isSome && y.isSome) = (match x, y with | some t₁, some t₂ => some (OTerm.add t₁ t₂) | _, _ => none).isSome := by
        rintro (_ | _) (_ | _) <;> rfl
      exact aux _ _
    · rw [hget _ ha, hget _ hb]; unfold isValidTCode
      have aux : ∀ x y : Option OTerm,
          (x.isSome && y.isSome) = (match x, y with | some t₁, some t₂ => some (OTerm.mul t₁ t₂) | _, _ => none).isSome := by
        rintro (_ | _) (_ | _) <;> rfl
      exact aux _ _
    · rfl

def noBVarTStep (l : List Bool) (n : ℕ) : Bool :=
  if n == 0 then false
  else
    let p := (n - 1).unpair
    match p.1 with
    | 0 => true
    | 1 => false
    | 2 => p.2 == 0
    | 3 => p.2 == 0
    | 4 => l.getD p.2 false
    | 5 => l.getD p.2 false
    | 6 => l.getD p.2.unpair.1 false && l.getD p.2.unpair.2 false
    | 7 => l.getD p.2.unpair.1 false && l.getD p.2.unpair.2 false
    | _ => false

def noBVarTCode (n : ℕ) : Bool :=
  match decT n with
  | some t => t.noBVar
  | none => false

lemma noBVarTCode_rec (n : ℕ) :
    noBVarTStep ((List.range n).map noBVarTCode) n = noBVarTCode n := by
  have hget : ∀ m < n, ((List.range n).map noBVarTCode).getD m false = noBVarTCode m := fun m hm => by
    simp [List.getD, List.getElem?_map, List.getElem?_range hm]
  unfold noBVarTStep; conv_rhs => unfold noBVarTCode
  by_cases hn : n = 0
  · subst hn; rw [decT]; simp
  · simp only [beq_iff_eq, hn, ↓reduceIte]
    rw [decT, dif_neg hn]
    dsimp only
    set p := (n - 1).unpair with hp
    have hp2 : p.2 < n := lt_of_le_of_lt (Nat.unpair_right_le (n - 1)) (by omega)
    have ha : p.2.unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le p.2) hp2
    have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
    rcases h1 : p.1 with _ | _ | _ | _ | _ | _ | _ | _ | k <;> (try dsimp only)
    · rfl
    · rfl
    · cases p.2 <;> rfl
    · cases p.2 <;> rfl
    · rw [hget p.2 hp2]; unfold noBVarTCode
      have aux : ∀ x : Option OTerm,
          (match x with | some t => t.noBVar | none => false) =
          (match x.map OTerm.neg with | some t => t.noBVar | none => false) := by rintro (_ | _) <;> rfl
      exact aux _
    · rw [hget p.2 hp2]; unfold noBVarTCode
      have aux : ∀ x : Option OTerm,
          (match x with | some t => t.noBVar | none => false) =
          (match x.map OTerm.exp with | some t => t.noBVar | none => false) := by rintro (_ | _) <;> rfl
      exact aux _
    · rw [hget _ ha, hget _ hb]; unfold noBVarTCode
      have aux : ∀ x y : Option OTerm,
          ((match x with | some t => t.noBVar | none => false) &&
           (match y with | some t => t.noBVar | none => false)) =
          (match (match x, y with | some t₁, some t₂ => some (OTerm.add t₁ t₂) | _, _ => none) with
           | some t => t.noBVar | none => false) := by rintro (_ | _) (_ | _) <;> simp [OTerm.noBVar]
      exact aux _ _
    · rw [hget _ ha, hget _ hb]; unfold noBVarTCode
      have aux : ∀ x y : Option OTerm,
          ((match x with | some t => t.noBVar | none => false) &&
           (match y with | some t => t.noBVar | none => false)) =
          (match (match x, y with | some t₁, some t₂ => some (OTerm.mul t₁ t₂) | _, _ => none) with
           | some t => t.noBVar | none => false) := by rintro (_ | _) (_ | _) <;> simp [OTerm.noBVar]
      exact aux _ _
    · rfl

def isBoundedTStep (k : ℕ) (l : List Bool) (n : ℕ) : Bool :=
  if n == 0 then false
  else
    let p := (n - 1).unpair
    match p.1 with
    | 0 => false
    | 1 => decide (p.2 < k)
    | 2 => p.2 == 0
    | 3 => p.2 == 0
    | 4 => l.getD p.2 false
    | 5 => l.getD p.2 false
    | 6 => l.getD p.2.unpair.1 false && l.getD p.2.unpair.2 false
    | 7 => l.getD p.2.unpair.1 false && l.getD p.2.unpair.2 false
    | _ => false

def isBoundedTCode (k n : ℕ) : Bool :=
  match decT n with
  | some t => t.isBounded k
  | none => false

lemma isBoundedTCode_rec (k n : ℕ) :
    isBoundedTStep k ((List.range n).map (isBoundedTCode k)) n = isBoundedTCode k n := by
  have hget : ∀ m < n, ((List.range n).map (isBoundedTCode k)).getD m false = isBoundedTCode k m := fun m hm => by
    simp [List.getD, List.getElem?_map, List.getElem?_range hm]
  unfold isBoundedTStep; conv_rhs => unfold isBoundedTCode
  by_cases hn : n = 0
  · subst hn; rw [decT]; simp
  · simp only [beq_iff_eq, hn, ↓reduceIte]
    rw [decT, dif_neg hn]
    dsimp only
    set p := (n - 1).unpair with hp
    have hp2 : p.2 < n := lt_of_le_of_lt (Nat.unpair_right_le (n - 1)) (by omega)
    have ha : p.2.unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le p.2) hp2
    have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
    rcases h1 : p.1 with _ | _ | _ | _ | _ | _ | _ | _ | r <;> (try dsimp only)
    · rfl
    · rfl
    · cases p.2 <;> rfl
    · cases p.2 <;> rfl
    · rw [hget p.2 hp2]; unfold isBoundedTCode
      have aux : ∀ x : Option OTerm,
          (match x with | some t => t.isBounded k | none => false) =
          (match x.map OTerm.neg with | some t => t.isBounded k | none => false) := by rintro (_ | _) <;> rfl
      exact aux _
    · rw [hget p.2 hp2]; unfold isBoundedTCode
      have aux : ∀ x : Option OTerm,
          (match x with | some t => t.isBounded k | none => false) =
          (match x.map OTerm.exp with | some t => t.isBounded k | none => false) := by rintro (_ | _) <;> rfl
      exact aux _
    · rw [hget _ ha, hget _ hb]; unfold isBoundedTCode
      have aux : ∀ x y : Option OTerm,
          ((match x with | some t => t.isBounded k | none => false) &&
           (match y with | some t => t.isBounded k | none => false)) =
          (match (match x, y with | some t₁, some t₂ => some (OTerm.add t₁ t₂) | _, _ => none) with
           | some t => t.isBounded k | none => false) := by rintro (_ | _) (_ | _) <;> simp [OTerm.isBounded]
      exact aux _ _
    · rw [hget _ ha, hget _ hb]; unfold isBoundedTCode
      have aux : ∀ x y : Option OTerm,
          ((match x with | some t => t.isBounded k | none => false) &&
           (match y with | some t => t.isBounded k | none => false)) =
          (match (match x, y with | some t₁, some t₂ => some (OTerm.mul t₁ t₂) | _, _ => none) with
           | some t => t.isBounded k | none => false) := by rintro (_ | _) (_ | _) <;> simp [OTerm.isBounded]
      exact aux _ _
    · rfl

def hasFVarTStep (v : ℕ) (l : List Bool) (n : ℕ) : Bool :=
  if n == 0 then false
  else
    let p := (n - 1).unpair
    match p.1 with
    | 0 => p.2 == v
    | 1 => false
    | 2 => false
    | 3 => false
    | 4 => l.getD p.2 false
    | 5 => l.getD p.2 false
    | 6 => if isValidTCode p.2.unpair.1 && isValidTCode p.2.unpair.2 then
             l.getD p.2.unpair.1 false || l.getD p.2.unpair.2 false else false
    | 7 => if isValidTCode p.2.unpair.1 && isValidTCode p.2.unpair.2 then
             l.getD p.2.unpair.1 false || l.getD p.2.unpair.2 false else false
    | _ => false

def hasFVarTCode (v n : ℕ) : Bool :=
  match decT n with
  | some t => t.hasFVar v
  | none => false

lemma hasFVarTCode_rec (v n : ℕ) :
    hasFVarTStep v ((List.range n).map (hasFVarTCode v)) n = hasFVarTCode v n := by
  have hget : ∀ m < n, ((List.range n).map (hasFVarTCode v)).getD m false = hasFVarTCode v m := fun m hm => by
    simp [List.getD, List.getElem?_map, List.getElem?_range hm]
  unfold hasFVarTStep; conv_rhs => unfold hasFVarTCode
  by_cases hn : n = 0
  · subst hn; rw [decT]; simp
  · simp only [beq_iff_eq, hn, ↓reduceIte]
    rw [decT, dif_neg hn]
    dsimp only
    set p := (n - 1).unpair with hp
    have hp2 : p.2 < n := lt_of_le_of_lt (Nat.unpair_right_le (n - 1)) (by omega)
    have ha : p.2.unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le p.2) hp2
    have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
    rcases h1 : p.1 with _ | _ | _ | _ | _ | _ | _ | _ | r <;> (try dsimp only)
    · by_cases h : p.2 = v <;> simp [OTerm.hasFVar, h]
    · rfl
    · cases p.2 <;> rfl
    · cases p.2 <;> rfl
    · rw [hget p.2 hp2]; unfold hasFVarTCode
      have aux : ∀ x : Option OTerm,
          (match x with | some t => t.hasFVar v | none => false) =
          (match x.map OTerm.neg with | some t => t.hasFVar v | none => false) := by rintro (_ | _) <;> rfl
      exact aux _
    · rw [hget p.2 hp2]; unfold hasFVarTCode
      have aux : ∀ x : Option OTerm,
          (match x with | some t => t.hasFVar v | none => false) =
          (match x.map OTerm.exp with | some t => t.hasFVar v | none => false) := by rintro (_ | _) <;> rfl
      exact aux _
    · rw [hget _ ha, hget _ hb]; unfold hasFVarTCode isValidTCode
      have aux : ∀ x y : Option OTerm,
          (if x.isSome && y.isSome then
            (match x with | some t => t.hasFVar v | none => false) ||
            (match y with | some t => t.hasFVar v | none => false) else false) =
          (match (match x, y with | some t₁, some t₂ => some (OTerm.add t₁ t₂) | _, _ => none) with
           | some t => t.hasFVar v | none => false) := by rintro (_ | _) (_ | _) <;> rfl
      exact aux _ _
    · rw [hget _ ha, hget _ hb]; unfold hasFVarTCode isValidTCode
      have aux : ∀ x y : Option OTerm,
          (if x.isSome && y.isSome then
            (match x with | some t => t.hasFVar v | none => false) ||
            (match y with | some t => t.hasFVar v | none => false) else false) =
          (match (match x, y with | some t₁, some t₂ => some (OTerm.mul t₁ t₂) | _, _ => none) with
           | some t => t.hasFVar v | none => false) := by rintro (_ | _) (_ | _) <;> rfl
      exact aux _ _
    · rfl

def substBTStep (ku : ℕ × ℕ) (l : List ℕ) (n : ℕ) : ℕ :=
  if n == 0 then 0
  else
    let p := (n - 1).unpair
    match p.1 with
    | 0 => n
    | 1 => if p.2 == ku.1 then ku.2 else n
    | 2 => if p.2 == 0 then n else 0
    | 3 => if p.2 == 0 then n else 0
    | 4 => let a := l.getD p.2 0; if a == 0 then 0 else Nat.pair 4 a + 1
    | 5 => let a := l.getD p.2 0; if a == 0 then 0 else Nat.pair 5 a + 1
    | 6 =>
      let a := l.getD p.2.unpair.1 0
      let b := l.getD p.2.unpair.2 0
      if a == 0 || b == 0 then 0 else Nat.pair 6 (Nat.pair a b) + 1
    | 7 =>
      let a := l.getD p.2.unpair.1 0
      let b := l.getD p.2.unpair.2 0
      if a == 0 || b == 0 then 0 else Nat.pair 7 (Nat.pair a b) + 1
    | _ => 0

def substBTCode (ku : ℕ × ℕ) (n : ℕ) : ℕ :=
  match decT n, decT ku.2 with
  | some t, some u => encT (t.substB ku.1 u)
  | _, _ => 0

lemma substBTCode_rec (ku : ℕ × ℕ) (hku : isValidTCode ku.2 = true) (n : ℕ) :
    substBTStep ku ((List.range n).map (substBTCode ku)) n = substBTCode ku n := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hku
  have hget : ∀ m < n, ((List.range n).map (substBTCode ku)).getD m 0 = substBTCode ku m := fun m hm => by
    simp [List.getD, List.getElem?_map, List.getElem?_range hm]
  unfold substBTStep; conv_rhs => unfold substBTCode
  by_cases hn : n = 0
  · subst hn; rw [decT]; simp
  · rw [if_neg (by simp [hn])]
    set p := (n - 1).unpair with hp
    rw [decT, dif_neg hn]
    simp only [← hp]
    have hp2 : p.2 < n := lt_of_le_of_lt (Nat.unpair_right_le (n - 1)) (by omega)
    have ha : p.2.unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le p.2) hp2
    have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
    have hpair : Nat.pair p.1 p.2 + 1 = n := by rw [hp, Nat.pair_unpair]; omega
    rcases h1 : p.1 with _ | _ | _ | _ | _ | _ | _ | _ | r <;> (try dsimp only)
    · rw [hu]; simp only [OTerm.substB, encT]; simpa [h1] using hpair.symm
    · rw [hu]; simp only [OTerm.substB]
      by_cases hk : p.2 = ku.1
      · simp [hk, encT_decT hu]
      · simp only [beq_iff_eq, hk, ↓reduceIte, encT]; simpa [h1] using hpair.symm
    · by_cases h0 : p.2 = 0
      · simp only [beq_iff_eq, h0, ↓reduceIte, hu, OTerm.substB, encT]; simpa [h1, h0] using hpair.symm
      · simp [h0]
    · by_cases h0 : p.2 = 0
      · simp only [beq_iff_eq, h0, ↓reduceIte, hu, OTerm.substB, encT]; simpa [h1, h0] using hpair.symm
      · simp [h0]
    · rw [hget p.2 hp2]; unfold substBTCode; rw [hu]
      cases decT p.2 <;> simp [(encT_pos _).ne', OTerm.substB, encT]
    · rw [hget p.2 hp2]; unfold substBTCode; rw [hu]
      cases decT p.2 <;> simp [(encT_pos _).ne', OTerm.substB, encT]
    · rw [hget _ ha, hget _ hb]; unfold substBTCode; rw [hu]
      cases decT p.2.unpair.1 <;> cases decT p.2.unpair.2 <;> simp [(encT_pos _).ne', OTerm.substB, encT]
    · rw [hget _ ha, hget _ hb]; unfold substBTCode; rw [hu]
      cases decT p.2.unpair.1 <;> cases decT p.2.unpair.2 <;> simp [(encT_pos _).ne', OTerm.substB, encT]
    · rfl

def substBTCode' (ku : ℕ × ℕ) (n : ℕ) : ℕ :=
  if isValidTCode ku.2 then substBTCode ku n else 0

def tListEncStep (l : List (List ℕ)) (n : ℕ) : List ℕ :=
  if n == 0 then []
  else
    let p := (n - 1).unpair
    match p.1 with
    | 0 => []
    | 1 => [2 * (2 * p.2 + 1)]
    | 2 => if p.2 == 0 then [13] else []
    | 3 => if p.2 == 0 then [17] else []
    | 4 => if isValidTCode p.2 then 9 :: l.getD p.2 [] else []
    | 5 => if isValidTCode p.2 then 3 :: l.getD p.2 [] else []
    | 6 => if isValidTCode p.2.unpair.1 && isValidTCode p.2.unpair.2 then
             1 :: (l.getD p.2.unpair.1 [] ++ l.getD p.2.unpair.2 []) else []
    | 7 => if isValidTCode p.2.unpair.1 && isValidTCode p.2.unpair.2 then
             5 :: (l.getD p.2.unpair.1 [] ++ l.getD p.2.unpair.2 []) else []
    | _ => []

def tListEncCode (n : ℕ) : List ℕ :=
  match decT n with
  | some t => tListEnc t
  | none => []

lemma tListEncCode_encT (t : OTerm) : tListEncCode (encT t) = tListEnc t := by
  simp [tListEncCode, decT_encT]

lemma tListEncCode_rec (n : ℕ) :
    tListEncStep ((List.range n).map tListEncCode) n = tListEncCode n := by
  have hget : ∀ m < n, ((List.range n).map tListEncCode).getD m [] = tListEncCode m := fun m hm => by
    simp [List.getD, List.getElem?_map, List.getElem?_range hm]
  unfold tListEncStep; conv_rhs => unfold tListEncCode
  by_cases hn : n = 0
  · subst hn; rw [decT]; simp
  · simp only [beq_iff_eq, hn, ↓reduceIte]
    rw [decT, dif_neg hn]
    dsimp only
    set p := (n - 1).unpair with hp
    have hp2 : p.2 < n := lt_of_le_of_lt (Nat.unpair_right_le (n - 1)) (by omega)
    have ha : p.2.unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le p.2) hp2
    have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
    rcases h1 : p.1 with _ | _ | _ | _ | _ | _ | _ | _ | k <;> (try dsimp only)
    · rfl
    · rfl
    · cases p.2 <;> rfl
    · cases p.2 <;> rfl
    · rw [hget p.2 hp2]; unfold tListEncCode isValidTCode
      have aux : ∀ x : Option OTerm,
          (if x.isSome then 9 :: match x with | some t => tListEnc t | none => [] else []) =
          (match x.map OTerm.neg with | some t => tListEnc t | none => []) := by rintro (_ | _) <;> rfl
      exact aux _
    · rw [hget p.2 hp2]; unfold tListEncCode isValidTCode
      have aux : ∀ x : Option OTerm,
          (if x.isSome then 3 :: match x with | some t => tListEnc t | none => [] else []) =
          (match x.map OTerm.exp with | some t => tListEnc t | none => []) := by rintro (_ | _) <;> rfl
      exact aux _
    · rw [hget _ ha, hget _ hb]; unfold tListEncCode isValidTCode
      have aux : ∀ x y : Option OTerm,
          (if x.isSome && y.isSome then
            1 :: ((match x with | some t => tListEnc t | none => []) ++
                  (match y with | some t => tListEnc t | none => [])) else []) =
          (match (match x, y with | some t₁, some t₂ => some (OTerm.add t₁ t₂) | _, _ => none) with
           | some t => tListEnc t | none => []) := by rintro (_ | _) (_ | _) <;> rfl
      exact aux _ _
    · rw [hget _ ha, hget _ hb]; unfold tListEncCode isValidTCode
      have aux : ∀ x y : Option OTerm,
          (if x.isSome && y.isSome then
            5 :: ((match x with | some t => tListEnc t | none => []) ++
                  (match y with | some t => tListEnc t | none => [])) else []) =
          (match (match x, y with | some t₁, some t₂ => some (OTerm.mul t₁ t₂) | _, _ => none) with
           | some t => tListEnc t | none => []) := by rintro (_ | _) (_ | _) <;> rfl
      exact aux _ _
    · rfl

def isValidFStep (l : List Bool) (n : ℕ) : Bool :=
  if n == 0 then false
  else
    let p := (n - 1).unpair
    match p.1 with
    | 0 => p.2 == 0
    | 1 => isValidTCode p.2.unpair.1 && isValidTCode p.2.unpair.2
    | 2 => isValidTCode p.2.unpair.1 && isValidTCode p.2.unpair.2
    | 3 => l.getD p.2.unpair.1 false && l.getD p.2.unpair.2 false
    | 4 => l.getD p.2.unpair.2 false
    | _ => false

def isValidFCode (n : ℕ) : Bool := (decF n).isSome

lemma isValidFCode_rec (n : ℕ) :
    isValidFStep ((List.range n).map isValidFCode) n = isValidFCode n := by
  have hget : ∀ m < n, ((List.range n).map isValidFCode).getD m false = isValidFCode m := fun m hm => by
    simp [List.getD, List.getElem?_map, List.getElem?_range hm]
  unfold isValidFStep; conv_rhs => unfold isValidFCode
  by_cases hn : n = 0
  · subst hn; rw [decF]; simp
  · simp only [beq_iff_eq, hn, ↓reduceIte]
    rw [decF, dif_neg hn]
    dsimp only
    set p := (n - 1).unpair with hp
    have hp2 : p.2 < n := lt_of_le_of_lt (Nat.unpair_right_le (n - 1)) (by omega)
    have ha : p.2.unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le p.2) hp2
    have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
    rcases h1 : p.1 with _ | _ | _ | _ | _ | r <;> (try dsimp only)
    · cases p.2 <;> rfl
    · unfold isValidTCode
      have aux : ∀ x y : Option OTerm,
          (x.isSome && y.isSome) = (match x, y with | some t₁, some t₂ => some (OForm.eq t₁ t₂) | _, _ => none).isSome := by
        rintro (_ | _) (_ | _) <;> rfl
      exact aux _ _
    · unfold isValidTCode
      have aux : ∀ x y : Option OTerm,
          (x.isSome && y.isSome) = (match x, y with | some t₁, some t₂ => some (OForm.le t₁ t₂) | _, _ => none).isSome := by
        rintro (_ | _) (_ | _) <;> rfl
      exact aux _ _
    · rw [hget _ ha, hget _ hb]; unfold isValidFCode
      have aux : ∀ x y : Option OForm,
          (x.isSome && y.isSome) = (match x, y with | some φ, some ψ => some (OForm.imp φ ψ) | _, _ => none).isSome := by
        rintro (_ | _) (_ | _) <;> rfl
      exact aux _ _
    · rw [hget _ hb]; simp [isValidFCode]
    · rfl

def hasFVarFStep (v : ℕ) (l : List Bool) (n : ℕ) : Bool :=
  if n == 0 then false
  else
    let p := (n - 1).unpair
    match p.1 with
    | 0 => false
    | 1 => if isValidTCode p.2.unpair.1 && isValidTCode p.2.unpair.2 then
             hasFVarTCode v p.2.unpair.1 || hasFVarTCode v p.2.unpair.2 else false
    | 2 => if isValidTCode p.2.unpair.1 && isValidTCode p.2.unpair.2 then
             hasFVarTCode v p.2.unpair.1 || hasFVarTCode v p.2.unpair.2 else false
    | 3 => if isValidFCode p.2.unpair.1 && isValidFCode p.2.unpair.2 then
             l.getD p.2.unpair.1 false || l.getD p.2.unpair.2 false else false
    | 4 => l.getD p.2.unpair.2 false
    | _ => false

def hasFVarFCode (v n : ℕ) : Bool :=
  match decF n with
  | some φ => φ.hasFVar v
  | none => false

lemma hasFVarFCode_rec (v n : ℕ) :
    hasFVarFStep v ((List.range n).map (hasFVarFCode v)) n = hasFVarFCode v n := by
  have hget : ∀ m < n, ((List.range n).map (hasFVarFCode v)).getD m false = hasFVarFCode v m := fun m hm => by
    simp [List.getD, List.getElem?_map, List.getElem?_range hm]
  unfold hasFVarFStep; conv_rhs => unfold hasFVarFCode
  by_cases hn : n = 0
  · subst hn; rw [decF]; simp
  · simp only [beq_iff_eq, hn, ↓reduceIte]
    rw [decF, dif_neg hn]
    dsimp only
    set p := (n - 1).unpair with hp
    have hp2 : p.2 < n := lt_of_le_of_lt (Nat.unpair_right_le (n - 1)) (by omega)
    have ha : p.2.unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le p.2) hp2
    have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
    rcases h1 : p.1 with _ | _ | _ | _ | _ | r <;> (try dsimp only)
    · cases p.2 <;> rfl
    · unfold hasFVarTCode isValidTCode
      have aux : ∀ x y : Option OTerm,
          (if x.isSome && y.isSome then
            (match x with | some t => t.hasFVar v | none => false) ||
            (match y with | some t => t.hasFVar v | none => false) else false) =
          (match (match x, y with | some t₁, some t₂ => some (OForm.eq t₁ t₂) | _, _ => none) with
           | some φ => φ.hasFVar v | none => false) := by rintro (_ | _) (_ | _) <;> rfl
      exact aux _ _
    · unfold hasFVarTCode isValidTCode
      have aux : ∀ x y : Option OTerm,
          (if x.isSome && y.isSome then
            (match x with | some t => t.hasFVar v | none => false) ||
            (match y with | some t => t.hasFVar v | none => false) else false) =
          (match (match x, y with | some t₁, some t₂ => some (OForm.le t₁ t₂) | _, _ => none) with
           | some φ => φ.hasFVar v | none => false) := by rintro (_ | _) (_ | _) <;> rfl
      exact aux _ _
    · rw [hget _ ha, hget _ hb]; unfold hasFVarFCode isValidFCode
      have aux : ∀ x y : Option OForm,
          (if x.isSome && y.isSome then
            (match x with | some φ => φ.hasFVar v | none => false) ||
            (match y with | some φ => φ.hasFVar v | none => false) else false) =
          (match (match x, y with | some φ, some ψ => some (OForm.imp φ ψ) | _, _ => none) with
           | some χ => χ.hasFVar v | none => false) := by rintro (_ | _) (_ | _) <;> rfl
      exact aux _ _
    · rw [hget _ hb]; unfold hasFVarFCode
      have aux : ∀ x : Option OForm,
          (match x with | some φ => φ.hasFVar v | none => false) =
          (match x.map (OForm.all p.2.unpair.1) with | some φ => φ.hasFVar v | none => false) := by
        rintro (_ | _) <;> rfl
      exact aux _
    · rfl

def substBFStep (ku : ℕ × ℕ) (l : List ℕ) (n : ℕ) : ℕ :=
  if n == 0 then 0
  else
    let p := (n - 1).unpair
    match p.1 with
    | 0 => if p.2 == 0 && isValidTCode ku.2 then n else 0
    | 1 =>
      let a := substBTCode' ku p.2.unpair.1
      let b := substBTCode' ku p.2.unpair.2
      if a == 0 || b == 0 then 0 else Nat.pair 1 (Nat.pair a b) + 1
    | 2 =>
      let a := substBTCode' ku p.2.unpair.1
      let b := substBTCode' ku p.2.unpair.2
      if a == 0 || b == 0 then 0 else Nat.pair 2 (Nat.pair a b) + 1
    | 3 =>
      let a := l.getD p.2.unpair.1 0
      let b := l.getD p.2.unpair.2 0
      if a == 0 || b == 0 then 0 else Nat.pair 3 (Nat.pair a b) + 1
    | 4 =>
      let m := p.2.unpair.1
      let body := p.2.unpair.2
      if m == ku.1 then
        if isValidFCode body && isValidTCode ku.2 then n else 0
      else
        let b := l.getD body 0
        if b == 0 then 0 else Nat.pair 4 (Nat.pair m b) + 1
    | _ => 0

def substBFCode (ku : ℕ × ℕ) (n : ℕ) : ℕ :=
  match decF n, decT ku.2 with
  | some φ, some u => encF (φ.substB ku.1 u)
  | _, _ => 0

lemma substBFCode_rec (ku : ℕ × ℕ) (n : ℕ) :
    substBFStep ku ((List.range n).map (substBFCode ku)) n = substBFCode ku n := by
  have hget : ∀ m < n, ((List.range n).map (substBFCode ku)).getD m 0 = substBFCode ku m := fun m hm => by
    simp [List.getD, List.getElem?_map, List.getElem?_range hm]
  by_cases hku : isValidTCode ku.2 = true
  · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hku
    unfold substBFStep; conv_rhs => unfold substBFCode
    by_cases hn : n = 0
    · subst hn; rw [decF]; simp
    · rw [if_neg (by simp [hn])]
      set p := (n - 1).unpair with hp
      rw [decF, dif_neg hn]
      simp only [← hp]
      have hp2 : p.2 < n := lt_of_le_of_lt (Nat.unpair_right_le (n - 1)) (by omega)
      have ha : p.2.unpair.1 < n := lt_of_le_of_lt (Nat.unpair_left_le p.2) hp2
      have hb : p.2.unpair.2 < n := lt_of_le_of_lt (Nat.unpair_right_le p.2) hp2
      have hpair : Nat.pair p.1 p.2 + 1 = n := by rw [hp, Nat.pair_unpair]; omega
      rcases h1 : p.1 with _ | _ | _ | _ | _ | r <;> (try dsimp only)
      · by_cases h0 : p.2 = 0
        · simp only [beq_iff_eq, h0, hku, Bool.and_self, ↓reduceIte, hu, OForm.substB, encF]
          simpa [h1, h0] using hpair.symm
        · simp [h0]
      · simp only [substBTCode', hku, ↓reduceIte]; unfold substBTCode; rw [hu]
        cases decT p.2.unpair.1 <;> cases decT p.2.unpair.2 <;> simp [(encT_pos _).ne', OForm.substB, encF]
      · simp only [substBTCode', hku, ↓reduceIte]; unfold substBTCode; rw [hu]
        cases decT p.2.unpair.1 <;> cases decT p.2.unpair.2 <;> simp [(encT_pos _).ne', OForm.substB, encF]
      · rw [hget _ ha, hget _ hb]; unfold substBFCode; rw [hu]
        cases decF p.2.unpair.1 <;> cases decF p.2.unpair.2 <;> simp [(encF_pos _).ne', OForm.substB, encF]
      · rw [hget _ hb]; unfold substBFCode isValidFCode; rw [hu, hku]
        by_cases hmk : p.2.unpair.1 = ku.1
        · simp only [beq_iff_eq, hmk, ↓reduceIte, Bool.and_true]
          cases hB : decF p.2.unpair.2 with
          | none => rfl
          | some φ =>
            simp only [Option.isSome_some, ↓reduceIte, Option.map_some, OForm.substB, encF]
            rw [encF_decF hB, ← hmk, Nat.pair_unpair]
            simpa [h1] using hpair.symm
        · simp only [beq_iff_eq, hmk, ↓reduceIte]
          cases decF p.2.unpair.2 <;> simp [hmk, (encF_pos _).ne', OForm.substB, encF]
      · rfl
  · have hu : decT ku.2 = none := by
      cases h : decT ku.2 with
      | none => rfl
      | some u => exact False.elim (hku (by simp [isValidTCode, h]))
    have hsub0 : ∀ m, substBFCode ku m = 0 := fun m => by simp [substBFCode, hu]
    have hget0 : ∀ m, ((List.range n).map (substBFCode ku)).getD m 0 = 0 := fun m => by
      by_cases hm : m < n
      · simp [List.getD, List.getElem?_map, List.getElem?_range hm, hsub0]
      · have hge : ((List.range n).map (substBFCode ku)).length ≤ m := by simp; omega
        simp [List.getD, List.getElem?_eq_none hge]
    rw [hsub0 n]
    unfold substBFStep
    by_cases hn : n = 0
    · simp [hn]
    · simp only [beq_iff_eq, hn, ↓reduceIte]
      set p := (n - 1).unpair
      rcases p.1 with _ | _ | _ | _ | _ | r <;> (try dsimp only)
      · simp [hku]
      · simp [substBTCode', hku]
      · simp [substBTCode', hku]
      · rw [hget0, hget0]; rfl
      · by_cases hmk : p.2.unpair.1 = ku.1
        · simp [hmk, hku]
        · simp only [beq_iff_eq, hmk, ↓reduceIte]; rw [hget0]; rfl
      · rfl

/- ### Stack-machine forward encoder to Mathlib `BoundedFormula.listEncode` -/

def encStep (st : (Bool × List (ℕ × ℕ)) × List ℕ) : (Bool × List (ℕ × ℕ)) × List ℕ :=
  let ok := st.1.1
  let stack := st.1.2
  let revOut := st.2
  if !ok then st
  else
    match stack with
    | [] => st
    | (tag, val) :: rest =>
      if tag == 0 then ((true, rest), val :: revOut)
      else if tag == 1 then
        let k := val.unpair.1
        let c := val.unpair.2
        if c == 0 then ((false, []), revOut)
        else
          let p := (c - 1).unpair
          match p.1 with
          | 0 =>
            if p.2 == 0 then ((true, (0, 4 * k + 11) :: rest), revOut)
            else ((false, []), revOut)
          | 1 =>
            let a := p.2.unpair.1
            let b := p.2.unpair.2
            if isBoundedTCode k a && isBoundedTCode k b then
              ((true, (0, 2 * Nat.pair k (encode (tListEncCode a))) ::
                      (0, 2 * Nat.pair k (encode (tListEncCode b))) :: rest), revOut)
            else ((false, []), revOut)
          | 2 =>
            let a := p.2.unpair.1
            let b := p.2.unpair.2
            if isBoundedTCode k a && isBoundedTCode k b then
              ((true, (0, 13) :: (0, 4 * k + 3) ::
                      (0, 2 * Nat.pair k (encode (tListEncCode a))) ::
                      (0, 2 * Nat.pair k (encode (tListEncCode b))) :: rest), revOut)
            else ((false, []), revOut)
          | 3 =>
            let a := p.2.unpair.1
            let b := p.2.unpair.2
            ((true, (0, 3) :: (1, Nat.pair k a) :: (1, Nat.pair k b) :: rest), revOut)
          | 4 =>
            let m := p.2.unpair.1
            let body := p.2.unpair.2
            if m == k then ((true, (0, 7) :: (1, Nat.pair (k + 1) body) :: rest), revOut)
            else ((false, []), revOut)
          | _ => ((false, []), revOut)
      else ((false, []), revOut)

def encodeIfBounded (c : ℕ) : Option ℕ :=
  let res := encStep^[5 * c + 5] ((true, [(1, Nat.pair 0 c)]), [])
  if res.1.1 && res.1.2.isEmpty then some (encode res.2.reverse) else none

def stepsNeeded : OForm → ℕ
  | .bot => 2
  | .eq _ _ => 3
  | .le _ _ => 5
  | .imp φ ψ => 2 + stepsNeeded φ + stepsNeeded ψ
  | .all _ φ => 2 + stepsNeeded φ

lemma stepsNeeded_le (φ : OForm) : stepsNeeded φ ≤ 5 * φ.size := by
  induction φ with
  | bot => simp [stepsNeeded, OForm.size]
  | eq _ _ => simp [stepsNeeded, OForm.size]
  | le _ _ => simp [stepsNeeded, OForm.size]
  | imp φ ψ ih₁ ih₂ => simp [stepsNeeded, OForm.size]; omega
  | all _ φ ih => simp [stepsNeeded, OForm.size]; omega

lemma encStep_nil (revOut : List ℕ) (n : ℕ) :
    encStep^[n] ((true, []), revOut) = ((true, []), revOut) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

lemma encStep_forward (φ : OForm) (k : ℕ) (h : φ.isBounded k = true)
    (rest : List (ℕ × ℕ)) (revOut : List ℕ) :
    encStep^[stepsNeeded φ] ((true, (1, Nat.pair k (encF φ)) :: rest), revOut) =
      ((true, rest), (fListEnc k φ).reverse ++ revOut) := by
  induction φ generalizing k rest revOut with
  | bot =>
    simp [stepsNeeded, Function.iterate_succ_apply, encStep, encF, fListEnc]
  | eq t₁ t₂ =>
    simp only [OForm.isBounded, Bool.and_eq_true] at h
    have h1 : isBoundedTCode k (encT t₁) = true := by simp [isBoundedTCode, decT_encT, h.1]
    have h2 : isBoundedTCode k (encT t₂) = true := by simp [isBoundedTCode, decT_encT, h.2]
    simp [stepsNeeded, Function.iterate_succ_apply, encStep, encF, h1, h2,
      tListEncCode_encT, fListEnc]
  | le t₁ t₂ =>
    simp only [OForm.isBounded, Bool.and_eq_true] at h
    have h1 : isBoundedTCode k (encT t₁) = true := by simp [isBoundedTCode, decT_encT, h.1]
    have h2 : isBoundedTCode k (encT t₂) = true := by simp [isBoundedTCode, decT_encT, h.2]
    simp [stepsNeeded, Function.iterate_succ_apply, encStep, encF, h1, h2,
      tListEncCode_encT, fListEnc]
  | imp φ ψ ih₁ ih₂ =>
    simp only [OForm.isBounded, Bool.and_eq_true] at h
    have hstep : stepsNeeded (.imp φ ψ) = stepsNeeded ψ + (stepsNeeded φ + 2) := by
      simp [stepsNeeded]; omega
    rw [hstep, Function.iterate_add_apply, Function.iterate_add_apply]
    have h2 : encStep^[2] ((true, (1, Nat.pair k (encF (.imp φ ψ))) :: rest), revOut) =
        ((true, (1, Nat.pair k (encF φ)) :: (1, Nat.pair k (encF ψ)) :: rest), 3 :: revOut) := by
      simp [Function.iterate_succ_apply, encStep, encF]
    rw [h2, ih₁ k h.1 _ _, ih₂ k h.2 _ _]
    simp [fListEnc, List.reverse_append, List.append_assoc]
  | all m φ ih =>
    simp only [OForm.isBounded, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨rfl, hφ⟩
    have hstep : stepsNeeded (.all m φ) = stepsNeeded φ + 2 := by
      simp [stepsNeeded]; omega
    rw [hstep, Function.iterate_add_apply]
    have h2 : encStep^[2] ((true, (1, Nat.pair m (encF (.all m φ))) :: rest), revOut) =
        ((true, (1, Nat.pair (m + 1) (encF φ)) :: rest), 7 :: revOut) := by
      simp [Function.iterate_succ_apply, encStep, encF]
    rw [h2, ih (m + 1) hφ _ _]
    simp [fListEnc, List.append_assoc]

lemma encodeIfBounded_encF (φ : OForm) (h : φ.isBounded 0 = true) :
    encodeIfBounded (encF φ) = some (encode (fListEnc 0 φ)) := by
  unfold encodeIfBounded
  have hle : stepsNeeded φ ≤ 5 * encF φ + 5 := by
    have := stepsNeeded_le φ
    have := encF_ge_size φ
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, Nat.add_comm, Function.iterate_add_apply, encStep_forward φ 0 h [] [],
    List.append_nil, encStep_nil]
  simp

def stackDenotes : List (ℕ × ℕ) → Option (List ℕ)
  | [] => some []
  | (tag, val) :: rest =>
    if tag = 0 then (stackDenotes rest).map (val :: ·)
    else if tag = 1 then
      match decF val.unpair.2, stackDenotes rest with
      | some φ, some r => if φ.isBounded val.unpair.1 then some (fListEnc val.unpair.1 φ ++ r) else none
      | _, _ => none
    else none

lemma encStep_back {stack stack' : List (ℕ × ℕ)} {revOut revOut' outFinal : List ℕ}
    (hstep : encStep ((true, stack), revOut) = ((true, stack'), revOut'))
    (r' : List ℕ) (hd' : stackDenotes stack' = some r')
    (hout : outFinal = r'.reverse ++ revOut') :
    ∃ r : List ℕ, stackDenotes stack = some r ∧ outFinal = r.reverse ++ revOut := by
  cases stack with
  | nil =>
    simp [encStep] at hstep
    rcases hstep with ⟨rfl, rfl⟩
    exact ⟨r', hd', hout⟩
  | cons item rest =>
    rcases item with ⟨tag, val⟩
    unfold encStep at hstep
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hstep
    by_cases ht0 : tag = 0
    · subst ht0
      simp only [beq_self_eq_true, ↓reduceIte, Prod.mk.injEq, true_and] at hstep
      rcases hstep with ⟨rfl, rfl⟩
      refine ⟨val :: r', ?_, ?_⟩
      · simp [stackDenotes, hd']
      · simp [hout, List.append_assoc]
    · by_cases ht1 : tag = 1
      · subst ht1
        simp only [show (1 == 0) = false by rfl, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true] at hstep
        set k := val.unpair.1 with hk_def
        set c := val.unpair.2 with hc_def
        by_cases hc : c = 0
        · simp [hc] at hstep
        · simp only [beq_iff_eq, hc, ↓reduceIte] at hstep
          set p := (c - 1).unpair with hp
          have hdec : decF c =
              match p.1 with
              | 0 => if p.2 = 0 then some .bot else none
              | 1 => match decT p.2.unpair.1, decT p.2.unpair.2 with
                     | some t₁, some t₂ => some (.eq t₁ t₂) | _, _ => none
              | 2 => match decT p.2.unpair.1, decT p.2.unpair.2 with
                     | some t₁, some t₂ => some (.le t₁ t₂) | _, _ => none
              | 3 => match decF p.2.unpair.1, decF p.2.unpair.2 with
                     | some φ, some ψ => some (.imp φ ψ) | _, _ => none
              | 4 => (decF p.2.unpair.2).map (.all p.2.unpair.1)
              | _ => none := by rw [decF, dif_neg hc]
          rcases h1 : p.1 with _ | _ | _ | _ | _ | z
          · simp only [h1] at hstep hdec
            by_cases hp0 : p.2 = 0
            · simp only [hp0, beq_self_eq_true, ↓reduceIte, Prod.mk.injEq, true_and] at hstep hdec
              rcases hstep with ⟨rfl, rfl⟩
              simp only [stackDenotes, ↓reduceIte, Option.map_eq_some_iff] at hd'
              obtain ⟨r0, hr0, rfl⟩ := hd'
              refine ⟨(4 * k + 11) :: r0, ?_, hout⟩
              simp [stackDenotes, show (1 : ℕ) ≠ 0 by decide, ← hk_def, ← hc_def, hdec, OForm.isBounded, fListEnc, hr0]
            · simp [hp0] at hstep
          · simp only [h1] at hstep hdec
            set a := p.2.unpair.1
            set b := p.2.unpair.2
            by_cases hab : isBoundedTCode k a = true ∧ isBoundedTCode k b = true
            · simp only [hab.1, hab.2, Bool.and_self, ↓reduceIte, Prod.mk.injEq, true_and] at hstep
              rcases hstep with ⟨rfl, rfl⟩
              have ha := hab.1; have hb := hab.2
              unfold isBoundedTCode at ha hb
              cases hta : decT a with
              | none => simp [hta] at ha
              | some t₁ =>
                cases htb : decT b with
                | none => simp [htb] at hb
                | some t₂ =>
                  simp only [hta] at ha; simp only [htb] at hb
                  simp only [hta, htb] at hdec
                  simp only [stackDenotes, ↓reduceIte, Option.map_eq_some_iff] at hd'
                  obtain ⟨r1, hr1, rfl⟩ := hd'
                  obtain ⟨r0, hr0, rfl⟩ := hr1
                  have htae : encT t₁ = a := encT_decT hta
                  have htbe : encT t₂ = b := encT_decT htb
                  refine ⟨fListEnc k (.eq t₁ t₂) ++ r0, ?_, ?_⟩
                  · simp [stackDenotes, show (1 : ℕ) ≠ 0 by decide, ← hk_def, ← hc_def, hdec, OForm.isBounded, ha, hb, hr0]
                  · simp [hout, fListEnc, ← htae, ← htbe, tListEncCode_encT]
            · have hfalse : (isBoundedTCode k a && isBoundedTCode k b) = false := by
                cases hA : isBoundedTCode k a <;> cases hB : isBoundedTCode k b <;> simp_all
              simp [hfalse] at hstep
          · simp only [h1] at hstep hdec
            set a := p.2.unpair.1
            set b := p.2.unpair.2
            by_cases hab : isBoundedTCode k a = true ∧ isBoundedTCode k b = true
            · simp only [hab.1, hab.2, Bool.and_self, ↓reduceIte, Prod.mk.injEq, true_and] at hstep
              rcases hstep with ⟨rfl, rfl⟩
              have ha := hab.1; have hb := hab.2
              unfold isBoundedTCode at ha hb
              cases hta : decT a with
              | none => simp [hta] at ha
              | some t₁ =>
                cases htb : decT b with
                | none => simp [htb] at hb
                | some t₂ =>
                  simp only [hta] at ha; simp only [htb] at hb
                  simp only [hta, htb] at hdec
                  simp only [stackDenotes, ↓reduceIte, Option.map_eq_some_iff] at hd'
                  obtain ⟨r3, hr3, rfl⟩ := hd'
                  obtain ⟨r2, hr2, rfl⟩ := hr3
                  obtain ⟨r1, hr1, rfl⟩ := hr2
                  obtain ⟨r0, hr0, rfl⟩ := hr1
                  have htae : encT t₁ = a := encT_decT hta
                  have htbe : encT t₂ = b := encT_decT htb
                  refine ⟨fListEnc k (.le t₁ t₂) ++ r0, ?_, ?_⟩
                  · simp [stackDenotes, show (1 : ℕ) ≠ 0 by decide, ← hk_def, ← hc_def, hdec, OForm.isBounded, ha, hb, hr0]
                  · simp [hout, fListEnc, ← htae, ← htbe, tListEncCode_encT]
            · have hfalse : (isBoundedTCode k a && isBoundedTCode k b) = false := by
                cases hA : isBoundedTCode k a <;> cases hB : isBoundedTCode k b <;> simp_all
              simp [hfalse] at hstep
          · simp only [h1, Prod.mk.injEq, true_and] at hstep hdec
            rcases hstep with ⟨rfl, rfl⟩
            set a := p.2.unpair.1
            set b := p.2.unpair.2
            simp only [stackDenotes, ↓reduceIte, Option.map_eq_some_iff] at hd'
            obtain ⟨r1, hr1, rfl⟩ := hd'
            simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, Nat.unpair_pair] at hr1
            cases hfa : decF a with
            | none => simp [hfa] at hr1
            | some φ =>
              simp only [hfa] at hr1
              cases hfb : decF b with
              | none => simp [hfb] at hr1
              | some ψ =>
                simp only [hfb] at hr1
                cases hr0 : stackDenotes rest with
                | none => simp [hr0] at hr1
                | some r0 =>
                  simp only [hr0] at hr1
                  by_cases hψ : ψ.isBounded k = true
                  · simp only [hψ, ↓reduceIte] at hr1
                    by_cases hφ : φ.isBounded k = true
                    · simp only [hφ, ↓reduceIte, Option.some.injEq] at hr1
                      subst hr1
                      refine ⟨fListEnc k (.imp φ ψ) ++ r0, ?_, ?_⟩
                      · simp [stackDenotes, show (1 : ℕ) ≠ 0 by decide, ← hk_def, ← hc_def, hdec, hfa, hfb, OForm.isBounded, hφ, hψ, hr0]
                      · simp [hout, fListEnc, List.append_assoc]
                    · simp [hφ] at hr1
                  · simp [hψ] at hr1
          · simp only [h1] at hstep hdec
            set m := p.2.unpair.1
            set body := p.2.unpair.2
            by_cases hmk : m = k
            · simp only [hmk, beq_self_eq_true, ↓reduceIte, Prod.mk.injEq, true_and] at hstep
              rcases hstep with ⟨rfl, rfl⟩
              simp only [stackDenotes, ↓reduceIte, Option.map_eq_some_iff] at hd'
              obtain ⟨r1, hr1, rfl⟩ := hd'
              simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, Nat.unpair_pair] at hr1
              cases hfb : decF body with
              | none => simp [hfb] at hr1
              | some φ =>
                simp only [hfb] at hr1
                cases hr0 : stackDenotes rest with
                | none => simp [hr0] at hr1
                | some r0 =>
                  simp only [hr0] at hr1
                  by_cases hφ : φ.isBounded (k + 1) = true
                  · simp only [hφ, ↓reduceIte, Option.some.injEq] at hr1
                    subst hr1
                    refine ⟨fListEnc k (.all m φ) ++ r0, ?_, ?_⟩
                    · simp [stackDenotes, show (1 : ℕ) ≠ 0 by decide, ← hk_def, ← hc_def, hdec, hfb, OForm.isBounded, hmk, hφ, hr0]
                    · simp [hout, fListEnc]
                  · simp [hφ] at hr1
            · simp [hmk] at hstep
          · simp [h1] at hstep
      · simp [ht0, ht1] at hstep

lemma encStep_iter_back : ∀ (N : ℕ) (stack : List (ℕ × ℕ)) (revOut outFinal : List ℕ),
    encStep^[N] ((true, stack), revOut) = ((true, []), outFinal) →
    ∃ r : List ℕ, stackDenotes stack = some r ∧ outFinal = r.reverse ++ revOut
  | 0, stack, revOut, outFinal, h => by
    simp only [Function.iterate_zero, id_eq, Prod.mk.injEq, true_and] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨[], rfl, rfl⟩
  | N + 1, stack, revOut, outFinal, h => by
    rw [Function.iterate_succ_apply] at h
    cases h1 : encStep ((true, stack), revOut) with
    | mk p revOut' =>
      rcases p with ⟨ok', stack'⟩
      rw [h1] at h
      cases ok' with
      | false =>
        have hfalse : ∀ m, encStep^[m] ((false, stack'), revOut') = ((false, stack'), revOut') := by
          intro m
          induction m with
          | zero => rfl
          | succ m ih => rw [Function.iterate_succ_apply', ih]; rfl
        rw [hfalse] at h
        simp at h
      | true =>
        obtain ⟨r', hd', hout⟩ := encStep_iter_back N stack' revOut' outFinal h
        exact encStep_back h1 r' hd' hout

lemma encodeIfBounded_eq_some_iff (c n : ℕ) :
    encodeIfBounded c = some n ↔
      ∃ φ : OForm, encF φ = c ∧ φ.isBounded 0 = true ∧ encode (fListEnc 0 φ) = n := by
  constructor
  · intro h
    unfold encodeIfBounded at h
    set res := encStep^[5 * c + 5] ((true, [(1, Nat.pair 0 c)]), []) with hres
    cases hok : res.1.1 with
    | false => simp [hok] at h
    | true =>
      cases hst : res.1.2 with
      | cons _ _ => simp [hok, hst] at h
      | nil =>
        simp only [hok, hst, List.isEmpty_nil, Bool.and_self, ↓reduceIte, Option.some.injEq] at h
        have hres' : encStep^[5 * c + 5] ((true, [(1, Nat.pair 0 c)]), []) = ((true, []), res.2) := by
          rw [← hres]; exact Prod.ext (Prod.ext hok hst) rfl
        obtain ⟨r, hr, hout⟩ := encStep_iter_back _ _ _ _ hres'
        simp only [stackDenotes, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, Nat.unpair_pair] at hr
        cases hdec : decF c with
        | none => simp [hdec] at hr
        | some φ =>
          simp only [hdec] at hr
          by_cases hbd : φ.isBounded 0 = true
          · simp only [hbd, ↓reduceIte, Option.some.injEq, List.append_nil] at hr
            subst hr
            refine ⟨φ, encF_decF hdec, hbd, ?_⟩
            rw [← h, hout, List.append_nil, List.reverse_reverse]
          · simp [hbd] at hr
  · rintro ⟨φ, rfl, hbd, rfl⟩
    exact encodeIfBounded_encF φ hbd

/- ### Bottom-up flat derivation traces on `ℕ`-codes -/

def mkBotCode : ℕ := Nat.pair 0 0 + 1
def mkEqCode (a b : ℕ) : ℕ := Nat.pair 1 (Nat.pair a b) + 1
def mkLeCode (a b : ℕ) : ℕ := Nat.pair 2 (Nat.pair a b) + 1
def mkImpCode (a b : ℕ) : ℕ := Nat.pair 3 (Nat.pair a b) + 1
def mkNegCode (a : ℕ) : ℕ := Nat.pair 4 a + 1
def mkExpCode (a : ℕ) : ℕ := Nat.pair 5 a + 1
def mkAddCode (a b : ℕ) : ℕ := Nat.pair 6 (Nat.pair a b) + 1
def mkMulCode (a b : ℕ) : ℕ := Nat.pair 7 (Nat.pair a b) + 1

def listContains {α : Type*} [BEq α] (l : List α) (x : α) : Bool :=
  l.any (fun y => y == x)

lemma listContains_iff {α : Type*} [BEq α] [LawfulBEq α] (l : List α) (x : α) :
    listContains l x = true ↔ x ∈ l := by
  unfold listContains
  simp only [List.any_eq_true, beq_iff_eq]
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun h => ⟨x, h, rfl⟩⟩

def validStep (prev : List (List ℕ × List ℕ)) (step : (List ℕ × List ℕ) × ℕ) : Bool :=
  let Γ := step.1.1
  let Δ := step.1.2
  let t := step.2
  let pt := (t - 1).unpair
  (Γ.all isValidFCode) && (Δ.all isValidFCode) && (isValidTCode t) &&
  (
    -- 1. ax
    Γ.any (fun c => listContains Δ c) ||
    -- 2. botL
    listContains Γ mkBotCode ||
    -- 3. impL
    Γ.any (fun c =>
      let p := (c - 1).unpair
      (p.1 == 3) &&
      listContains prev (Γ, p.2.unpair.1 :: Δ) &&
      listContains prev (p.2.unpair.2 :: Γ, Δ)) ||
    -- 4. impR
    Δ.any (fun c =>
      let p := (c - 1).unpair
      (p.1 == 3) &&
      listContains prev (p.2.unpair.1 :: Γ, p.2.unpair.2 :: Δ)) ||
    -- 5. allL
    (noBVarTCode t &&
      Γ.any (fun c =>
        let p := (c - 1).unpair
        (p.1 == 4) &&
        listContains prev (substBFCode (p.2.unpair.1, t) p.2.unpair.2 :: Γ, Δ))) ||
    -- 6. allR
    ((pt.1 == 0) &&
      !(Γ.any (fun c => hasFVarFCode pt.2 c)) &&
      !(Δ.any (fun c => hasFVarFCode pt.2 c)) &&
      Δ.any (fun c =>
        let p := (c - 1).unpair
        (p.1 == 4) &&
        listContains prev (Γ, substBFCode (p.2.unpair.1, t) p.2.unpair.2 :: Δ))) ||
    -- 7. eqRefl
    (noBVarTCode t && listContains prev (mkEqCode t t :: Γ, Δ)) ||
    -- 8. eqSymm
    Γ.any (fun c =>
      let p := (c - 1).unpair
      (p.1 == 1) && listContains prev (mkEqCode p.2.unpair.2 p.2.unpair.1 :: Γ, Δ)) ||
    -- 9. eqTrans
    Γ.any (fun c₁ =>
      let p₁ := (c₁ - 1).unpair
      (p₁.1 == 1) &&
      Γ.any (fun c₂ =>
        let p₂ := (c₂ - 1).unpair
        (p₂.1 == 1) && (p₁.2.unpair.2 == p₂.2.unpair.1) &&
        listContains prev (mkEqCode p₁.2.unpair.1 p₂.2.unpair.2 :: Γ, Δ))) ||
    -- 10. congNeg
    Γ.any (fun c =>
      let p := (c - 1).unpair
      (p.1 == 1) &&
      listContains prev (mkEqCode (mkNegCode p.2.unpair.1) (mkNegCode p.2.unpair.2) :: Γ, Δ)) ||
    -- 11. congExp
    Γ.any (fun c =>
      let p := (c - 1).unpair
      (p.1 == 1) &&
      listContains prev (mkEqCode (mkExpCode p.2.unpair.1) (mkExpCode p.2.unpair.2) :: Γ, Δ)) ||
    -- 12. congAdd
    Γ.any (fun c₁ =>
      let p₁ := (c₁ - 1).unpair
      (p₁.1 == 1) &&
      Γ.any (fun c₂ =>
        let p₂ := (c₂ - 1).unpair
        (p₂.1 == 1) &&
        listContains prev
          (mkEqCode (mkAddCode p₁.2.unpair.1 p₂.2.unpair.1)
                    (mkAddCode p₁.2.unpair.2 p₂.2.unpair.2) :: Γ, Δ))) ||
    -- 13. congMul
    Γ.any (fun c₁ =>
      let p₁ := (c₁ - 1).unpair
      (p₁.1 == 1) &&
      Γ.any (fun c₂ =>
        let p₂ := (c₂ - 1).unpair
        (p₂.1 == 1) &&
        listContains prev
          (mkEqCode (mkMulCode p₁.2.unpair.1 p₂.2.unpair.1)
                    (mkMulCode p₁.2.unpair.2 p₂.2.unpair.2) :: Γ, Δ))) ||
    -- 14. congLe
    Γ.any (fun c₁ =>
      let p₁ := (c₁ - 1).unpair
      (p₁.1 == 1) &&
      Γ.any (fun c₂ =>
        let p₂ := (c₂ - 1).unpair
        (p₂.1 == 1) &&
        listContains Γ (mkLeCode p₁.2.unpair.1 p₂.2.unpair.1) &&
        listContains prev (mkLeCode p₁.2.unpair.2 p₂.2.unpair.2 :: Γ, Δ)))
  )

def validTraceAux (prev : List (List ℕ × List ℕ)) :
    List ((List ℕ × List ℕ) × ℕ) → Bool
  | [] => true
  | st :: rest => validStep prev st && validTraceAux (st.1 :: prev) rest

def validTrace (tr : List ((List ℕ × List ℕ) × ℕ)) : Bool :=
  validTraceAux [] tr

lemma validStep_mono {prev prev' : List (List ℕ × List ℕ)}
    (hsub : ∀ x ∈ prev, x ∈ prev') (st : (List ℕ × List ℕ) × ℕ)
    (hv : validStep prev st = true) : validStep prev' st = true := by
  have hlc : ∀ x, listContains prev x = true → listContains prev' x = true := by
    intro x hx
    rw [listContains_iff] at hx ⊢
    exact hsub x hx
  unfold validStep at hv ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, listContains_iff] at hv ⊢
  refine ⟨hv.1, ?_⟩
  rcases hv.2 with
    (((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
  · left; left; left; left; left; left; left; left; left; left; left; left; left; exact h
  · left; left; left; left; left; left; left; left; left; left; left; left; right; exact h
  · left; left; left; left; left; left; left; left; left; left; left; right
    rcases h with ⟨c, hc, ⟨hp, h1⟩, h2⟩
    exact ⟨c, hc, ⟨hp, hsub _ h1⟩, hsub _ h2⟩
  · left; left; left; left; left; left; left; left; left; left; right
    rcases h with ⟨c, hc, hp, h1⟩
    exact ⟨c, hc, hp, hsub _ h1⟩
  · left; left; left; left; left; left; left; left; left; right
    rcases h with ⟨ht, c, hc, hp, h1⟩
    exact ⟨ht, c, hc, hp, hsub _ h1⟩
  · left; left; left; left; left; left; left; left; right
    rcases h with ⟨h1, c, hc, hp, h2⟩
    exact ⟨h1, c, hc, hp, hsub _ h2⟩
  · left; left; left; left; left; left; left; right
    exact ⟨h.1, hsub _ h.2⟩
  · left; left; left; left; left; left; right
    rcases h with ⟨c, hc, hp, h1⟩
    exact ⟨c, hc, hp, hsub _ h1⟩
  · left; left; left; left; left; right
    rcases h with ⟨c₁, hc₁, hp₁, c₂, hc₂, ⟨hp₂, heq⟩, h1⟩
    exact ⟨c₁, hc₁, hp₁, c₂, hc₂, ⟨hp₂, heq⟩, hsub _ h1⟩
  · left; left; left; left; right
    rcases h with ⟨c, hc, hp, h1⟩
    exact ⟨c, hc, hp, hsub _ h1⟩
  · left; left; left; right
    rcases h with ⟨c, hc, hp, h1⟩
    exact ⟨c, hc, hp, hsub _ h1⟩
  · left; left; right
    rcases h with ⟨c₁, hc₁, hp₁, c₂, hc₂, hp₂, h1⟩
    exact ⟨c₁, hc₁, hp₁, c₂, hc₂, hp₂, hsub _ h1⟩
  · left; right
    rcases h with ⟨c₁, hc₁, hp₁, c₂, hc₂, hp₂, h1⟩
    exact ⟨c₁, hc₁, hp₁, c₂, hc₂, hp₂, hsub _ h1⟩
  · right
    rcases h with ⟨c₁, hc₁, hp₁, c₂, hc₂, ⟨hp₂, hle⟩, h1⟩
    exact ⟨c₁, hc₁, hp₁, c₂, hc₂, ⟨hp₂, hle⟩, hsub _ h1⟩

lemma validTraceAux_mono {prev prev' : List (List ℕ × List ℕ)}
    (hsub : ∀ x ∈ prev, x ∈ prev') (tr : List ((List ℕ × List ℕ) × ℕ))
    (hv : validTraceAux prev tr = true) : validTraceAux prev' tr = true := by
  induction tr generalizing prev prev' with
  | nil => rfl
  | cons st rest ih =>
    simp only [validTraceAux, Bool.and_eq_true] at hv ⊢
    refine ⟨validStep_mono hsub st hv.1, ih (fun x hx => ?_) hv.2⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (hsub x hx')

lemma validTraceAux_append (prev : List (List ℕ × List ℕ))
    (tr₁ tr₂ : List ((List ℕ × List ℕ) × ℕ))
    (h1 : validTraceAux prev tr₁ = true) (h2 : validTraceAux prev tr₂ = true) :
    validTraceAux prev (tr₁ ++ tr₂) = true := by
  induction tr₁ generalizing prev with
  | nil => exact h2
  | cons st rest ih =>
    simp only [List.cons_append, validTraceAux, Bool.and_eq_true] at h1 ⊢
    exact ⟨h1.1, ih _ h1.2 (validTraceAux_mono (fun x hx => List.mem_cons_of_mem _ hx) tr₂ h2)⟩

lemma validTraceAux_concat_step (tr : List ((List ℕ × List ℕ) × ℕ))
    (st : (List ℕ × List ℕ) × ℕ)
    (htr : validTrace tr = true)
    (hst : validStep (tr.map Prod.fst) st = true) :
    validTrace (tr ++ [st]) = true := by
  suffices ∀ prev, validTraceAux prev tr = true →
      validStep (tr.map Prod.fst ++ prev) st = true →
      validTraceAux prev (tr ++ [st]) = true by
    exact this [] htr (by simpa using hst)
  clear htr hst
  induction tr with
  | nil =>
    intro prev _ h
    simpa [validTraceAux] using h
  | cons a rest ih =>
    intro prev h1 h2
    simp only [List.cons_append, validTraceAux, Bool.and_eq_true] at h1 ⊢
    refine ⟨h1.1, ih (a.1 :: prev) h1.2 ?_⟩
    exact validStep_mono (fun x hx => by
      simp only [List.map_cons, List.mem_append, List.mem_cons] at hx ⊢
      tauto) st h2

lemma seqProv_to_trace {Γ Δ : List OForm} (h : SeqProv Γ Δ) :
    ∃ tr : List ((List ℕ × List ℕ) × ℕ),
      validTrace tr = true ∧ (Γ.map encF, Δ.map encF) ∈ tr.map Prod.fst := by
  have hallF : ∀ l : List OForm, (l.map encF).all isValidFCode = true := by
    intro l
    simp [isValidFCode, decF_encF]
  have hvalT : ∀ t : OTerm, isValidTCode (encT t) = true := fun t => by
    simp [isValidTCode, decT_encT]
  induction h with
  | @ax Γ Δ φ h1 h2 =>
    refine ⟨[((Γ.map encF, Δ.map encF), encT .zero)], ?_, by simp⟩
    simp only [validTrace, validTraceAux, Bool.and_true]
    unfold validStep
    simp only [hallF, hvalT, Bool.and_self, Bool.true_and, Bool.or_eq_true, List.any_eq_true,
      listContains_iff]
    left; left; left; left; left; left; left; left; left; left; left; left; left
    exact ⟨encF φ, List.mem_map_of_mem h1, List.mem_map_of_mem h2⟩
  | @botL Γ Δ h1 =>
    refine ⟨[((Γ.map encF, Δ.map encF), encT .zero)], ?_, by simp⟩
    simp only [validTrace, validTraceAux, Bool.and_true]
    unfold validStep
    simp only [hallF, hvalT, Bool.and_self, Bool.true_and, Bool.or_eq_true, listContains_iff]
    left; left; left; left; left; left; left; left; left; left; left; left; right
    exact List.mem_map_of_mem h1
  | @impL Γ Δ φ ψ h1 _ _ ih1 ih2 =>
    obtain ⟨tr1, hv1, hm1⟩ := ih1
    obtain ⟨tr2, hv2, hm2⟩ := ih2
    let st := ((Γ.map encF, Δ.map encF), encT .zero)
    refine ⟨(tr1 ++ tr2) ++ [st], ?_, by simp [st]⟩
    apply validTraceAux_concat_step _ _ (validTraceAux_append [] tr1 tr2 hv1 hv2)
    unfold validStep
    simp only [st, hallF, hvalT, Bool.and_self, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true,
      List.any_eq_true, listContains_iff, List.map_append, List.mem_append]
    left; left; left; left; left; left; left; left; left; left; left; right
    refine ⟨encF (.imp φ ψ), List.mem_map_of_mem h1, ?_⟩
    simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair, beq_self_eq_true, true_and]
    exact ⟨Or.inl (by simpa using hm1), Or.inr (by simpa using hm2)⟩
  | @impR Γ Δ φ ψ h1 _ ih =>
    obtain ⟨tr, hv, hm⟩ := ih
    let st := ((Γ.map encF, Δ.map encF), encT .zero)
    refine ⟨tr ++ [st], validTraceAux_concat_step tr st hv ?_, by simp [st]⟩
    unfold validStep
    simp only [st, hallF, hvalT, Bool.and_self, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true,
      List.any_eq_true, listContains_iff]
    left; left; left; left; left; left; left; left; left; left; right
    refine ⟨encF (.imp φ ψ), List.mem_map_of_mem h1, ?_⟩
    simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair, beq_self_eq_true, true_and]
    simpa using hm
  | @allL Γ Δ k φ t h1 ht _ ih =>
    obtain ⟨tr, hv, hm⟩ := ih
    let st := ((Γ.map encF, Δ.map encF), encT t)
    refine ⟨tr ++ [st], validTraceAux_concat_step tr st hv ?_, by simp [st]⟩
    unfold validStep
    simp only [st, hallF, hvalT, Bool.and_self, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true,
      List.any_eq_true, listContains_iff]
    left; left; left; left; left; left; left; left; left; right
    refine ⟨by simp [noBVarTCode, decT_encT, ht], encF (.all k φ), List.mem_map_of_mem h1, ?_⟩
    simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair, beq_self_eq_true, Bool.true_and]
    simpa [substBFCode, decF_encF, decT_encT] using hm
  | @allR Γ Δ k φ v h1 hfvΓ hfvΔ _ ih =>
    obtain ⟨tr, hv, hm⟩ := ih
    let st := ((Γ.map encF, Δ.map encF), encT (.fvar v))
    refine ⟨tr ++ [st], validTraceAux_concat_step tr st hv ?_, by simp [st]⟩
    unfold validStep
    simp only [st, hallF, hvalT, Bool.and_self, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true,
      List.any_eq_true, listContains_iff]
    left; left; left; left; left; left; left; left; right
    have hΓf : (Γ.map encF).any (fun c => hasFVarFCode v c) = false := by
      rw [Bool.eq_false_iff]; intro h; simp only [List.any_eq_true, List.mem_map] at h
      obtain ⟨_, ⟨ψ, hψ, rfl⟩, h2⟩ := h
      simp [hasFVarFCode, decF_encF, hfvΓ ψ hψ] at h2
    have hΔf : (Δ.map encF).any (fun c => hasFVarFCode v c) = false := by
      rw [Bool.eq_false_iff]; intro h; simp only [List.any_eq_true, List.mem_map] at h
      obtain ⟨_, ⟨ψ, hψ, rfl⟩, h2⟩ := h
      simp [hasFVarFCode, decF_encF, hfvΔ ψ hψ] at h2
    refine ⟨⟨⟨by simp [encT], by simp [encT, hΓf]⟩, by simp [encT, hΔf]⟩,
      encF (.all k φ), List.mem_map_of_mem h1, ?_⟩
    simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair, beq_self_eq_true, Bool.true_and]
    simpa [substBFCode, decF_encF, decT_encT] using hm
  | @eqRefl Γ Δ t ht _ ih =>
    obtain ⟨tr, hv, hm⟩ := ih
    let st := ((Γ.map encF, Δ.map encF), encT t)
    refine ⟨tr ++ [st], validTraceAux_concat_step tr st hv ?_, by simp [st]⟩
    unfold validStep
    simp only [st, hallF, hvalT, Bool.and_self, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true,
      listContains_iff]
    left; left; left; left; left; left; left; right
    exact ⟨by simp [noBVarTCode, decT_encT, ht], by simpa [mkEqCode, encF] using hm⟩
  | @eqSymm Γ Δ t₁ t₂ h1 _ ih =>
    obtain ⟨tr, hv, hm⟩ := ih
    let st := ((Γ.map encF, Δ.map encF), encT .zero)
    refine ⟨tr ++ [st], validTraceAux_concat_step tr st hv ?_, by simp [st]⟩
    unfold validStep
    simp only [st, hallF, hvalT, Bool.and_self, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true,
      List.any_eq_true, listContains_iff]
    left; left; left; left; left; left; right
    refine ⟨encF (.eq t₁ t₂), List.mem_map_of_mem h1, ?_⟩
    simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair, beq_self_eq_true, true_and]
    simpa [mkEqCode, encF] using hm
  | @eqTrans Γ Δ t₁ t₂ t₃ h1 h2 _ ih =>
    obtain ⟨tr, hv, hm⟩ := ih
    let st := ((Γ.map encF, Δ.map encF), encT .zero)
    refine ⟨tr ++ [st], validTraceAux_concat_step tr st hv ?_, by simp [st]⟩
    unfold validStep
    simp only [st, hallF, hvalT, Bool.and_self, Bool.true_and, Bool.or_eq_true, List.any_eq_true,
      Bool.and_eq_true, listContains_iff]
    left; left; left; left; left; right
    refine ⟨encF (.eq t₁ t₂), List.mem_map_of_mem h1, by simp [encF],
      encF (.eq t₂ t₃), List.mem_map_of_mem h2, ?_⟩
    simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair, beq_self_eq_true, Bool.and_self,
      true_and]
    simpa [mkEqCode, encF] using hm
  | @congNeg Γ Δ t₁ t₂ h1 _ ih =>
    obtain ⟨tr, hv, hm⟩ := ih
    let st := ((Γ.map encF, Δ.map encF), encT .zero)
    refine ⟨tr ++ [st], validTraceAux_concat_step tr st hv ?_, by simp [st]⟩
    unfold validStep
    simp only [st, hallF, hvalT, Bool.and_self, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true,
      List.any_eq_true, listContains_iff]
    left; left; left; left; right
    refine ⟨encF (.eq t₁ t₂), List.mem_map_of_mem h1, ?_⟩
    simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair, beq_self_eq_true, true_and]
    simpa [mkEqCode, mkNegCode, encF, encT] using hm
  | @congExp Γ Δ t₁ t₂ h1 _ ih =>
    obtain ⟨tr, hv, hm⟩ := ih
    let st := ((Γ.map encF, Δ.map encF), encT .zero)
    refine ⟨tr ++ [st], validTraceAux_concat_step tr st hv ?_, by simp [st]⟩
    unfold validStep
    simp only [st, hallF, hvalT, Bool.and_self, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true,
      List.any_eq_true, listContains_iff]
    left; left; left; right
    refine ⟨encF (.eq t₁ t₂), List.mem_map_of_mem h1, ?_⟩
    simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair, beq_self_eq_true, true_and]
    simpa [mkEqCode, mkExpCode, encF, encT] using hm
  | @congAdd Γ Δ t₁ s₁ t₂ s₂ h1 h2 _ ih =>
    obtain ⟨tr, hv, hm⟩ := ih
    let st := ((Γ.map encF, Δ.map encF), encT .zero)
    refine ⟨tr ++ [st], validTraceAux_concat_step tr st hv ?_, by simp [st]⟩
    unfold validStep
    simp only [st, hallF, hvalT, Bool.and_self, Bool.true_and, Bool.or_eq_true, List.any_eq_true,
      Bool.and_eq_true, listContains_iff]
    left; left; right
    refine ⟨encF (.eq t₁ s₁), List.mem_map_of_mem h1, by simp [encF],
      encF (.eq t₂ s₂), List.mem_map_of_mem h2, by simp [encF], ?_⟩
    simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair]
    simpa [mkEqCode, mkAddCode, encF, encT] using hm
  | @congMul Γ Δ t₁ s₁ t₂ s₂ h1 h2 _ ih =>
    obtain ⟨tr, hv, hm⟩ := ih
    let st := ((Γ.map encF, Δ.map encF), encT .zero)
    refine ⟨tr ++ [st], validTraceAux_concat_step tr st hv ?_, by simp [st]⟩
    unfold validStep
    simp only [st, hallF, hvalT, Bool.and_self, Bool.true_and, Bool.or_eq_true, List.any_eq_true,
      Bool.and_eq_true, listContains_iff]
    left; right
    refine ⟨encF (.eq t₁ s₁), List.mem_map_of_mem h1, by simp [encF],
      encF (.eq t₂ s₂), List.mem_map_of_mem h2, by simp [encF], ?_⟩
    simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair]
    simpa [mkEqCode, mkMulCode, encF, encT] using hm
  | @congLe Γ Δ t₁ s₁ t₂ s₂ h1 h2 h3 _ ih =>
    obtain ⟨tr, hv, hm⟩ := ih
    let st := ((Γ.map encF, Δ.map encF), encT .zero)
    refine ⟨tr ++ [st], validTraceAux_concat_step tr st hv ?_, by simp [st]⟩
    unfold validStep
    simp only [st, hallF, hvalT, Bool.and_self, Bool.true_and, Bool.or_eq_true, List.any_eq_true,
      Bool.and_eq_true, listContains_iff]
    right
    refine ⟨encF (.eq t₁ s₁), List.mem_map_of_mem h1, by simp [encF],
      encF (.eq t₂ s₂), List.mem_map_of_mem h2,
      ⟨by simp [encF], by
        simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair]
        exact List.mem_map_of_mem h3⟩, ?_⟩
    simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair]
    simpa [mkLeCode, encF] using hm

lemma list_of_all_validF {cs : List ℕ} (h : cs.all isValidFCode = true) :
    ∃ l : List OForm, l.map encF = cs := by
  induction cs with
  | nil => exact ⟨[], rfl⟩
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.mp h.1
    obtain ⟨l, hl⟩ := ih h.2
    exact ⟨φ :: l, by simp [encF_decF hφ, hl]⟩

lemma validStep_sound {prev : List (List ℕ × List ℕ)}
    (hprev : ∀ p ∈ prev, ∀ Γ Δ : List OForm, p = (Γ.map encF, Δ.map encF) → SeqProv Γ Δ)
    {st : (List ℕ × List ℕ) × ℕ} (hv : validStep prev st = true) :
    ∀ Γ Δ : List OForm, st.1 = (Γ.map encF, Δ.map encF) → SeqProv Γ Δ := by
  intro Γ Δ heq
  rcases st with ⟨⟨Γc, Δc⟩, tc⟩
  simp only at heq
  rcases heq with ⟨rfl, rfl⟩
  unfold validStep at hv
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, listContains_iff] at hv
  obtain ⟨⟨⟨-, -⟩, htc⟩, hdisj⟩ := hv
  obtain ⟨t, htdec⟩ := Option.isSome_iff_exists.mp htc
  have htenc : encT t = tc := encT_decT htdec
  subst htenc
  have hmemF : ∀ {l : List OForm} {c : ℕ}, c ∈ l.map encF → ∃ φ ∈ l, encF φ = c := by
    intro l c hc
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hc
    exact ⟨φ, hφ, rfl⟩
  rcases hdisj with
    (((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
  · obtain ⟨c, hc1, hc2⟩ := h
    obtain ⟨φ, hφ1, rfl⟩ := hmemF hc1
    obtain ⟨ψ, hψ2, heq⟩ := hmemF hc2
    cases encF_injective heq
    exact SeqProv.ax hφ1 hψ2
  · obtain ⟨φ, hφ, heq⟩ := hmemF h
    have : φ = .bot := encF_injective heq
    subst this
    exact SeqProv.botL hφ
  · obtain ⟨c, hc, ⟨htag, h1⟩, h2⟩ := h
    obtain ⟨χ, hχ, rfl⟩ := hmemF hc
    cases χ with
    | imp φ ψ =>
      simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair] at h1 h2
      exact SeqProv.impL hχ
        (hprev _ h1 Γ (φ :: Δ) (by simp))
        (hprev _ h2 (ψ :: Γ) Δ (by simp))
    | bot | eq _ _ | le _ _ | all _ _ => simp [encF] at htag
  · obtain ⟨c, hc, htag, h1⟩ := h
    obtain ⟨χ, hχ, rfl⟩ := hmemF hc
    cases χ with
    | imp φ ψ =>
      simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair] at h1
      exact SeqProv.impR hχ (hprev _ h1 (φ :: Γ) (ψ :: Δ) (by simp))
    | bot | eq _ _ | le _ _ | all _ _ => simp [encF] at htag
  · obtain ⟨htnb, c, hc, htag, h1⟩ := h
    have ht' : t.noBVar = true := by simpa [noBVarTCode, decT_encT] using htnb
    obtain ⟨χ, hχ, rfl⟩ := hmemF hc
    cases χ with
    | all k φ =>
      simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair, substBFCode, decF_encF, decT_encT] at h1
      exact SeqProv.allL hχ ht' (hprev _ h1 (φ.substB k t :: Γ) Δ (by simp))
    | bot | eq _ _ | le _ _ | imp _ _ => simp [encF] at htag
  · obtain ⟨⟨⟨ht0, hfv1⟩, hfv2⟩, c, hc, htag, h1⟩ := h
    cases t with
    | fvar v =>
      simp only [encT, Nat.add_sub_cancel, Nat.unpair_pair] at hfv1 hfv2
      have hΓfv : ∀ ψ ∈ Γ, ψ.hasFVar v = false := by
        intro ψ hψ
        by_contra hne
        have htrue : ψ.hasFVar v = true := by cases h' : ψ.hasFVar v <;> simp_all
        have hany : (Γ.map encF).any (fun c => hasFVarFCode v c) = true := by
          rw [List.any_eq_true]
          exact ⟨encF ψ, List.mem_map_of_mem hψ, by simp [hasFVarFCode, decF_encF, htrue]⟩
        simp [hany] at hfv1
      have hΔfv : ∀ ψ ∈ Δ, ψ.hasFVar v = false := by
        intro ψ hψ
        by_contra hne
        have htrue : ψ.hasFVar v = true := by cases h' : ψ.hasFVar v <;> simp_all
        have hany : (Δ.map encF).any (fun c => hasFVarFCode v c) = true := by
          rw [List.any_eq_true]
          exact ⟨encF ψ, List.mem_map_of_mem hψ, by simp [hasFVarFCode, decF_encF, htrue]⟩
        simp [hany] at hfv2
      obtain ⟨χ, hχ, rfl⟩ := hmemF hc
      cases χ with
      | all k φ =>
        simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair, substBFCode, decF_encF,
          decT_encT] at h1
        exact SeqProv.allR hχ hΓfv hΔfv (hprev _ h1 Γ (φ.substB k (.fvar v) :: Δ) (by simp))
      | bot | eq _ _ | le _ _ | imp _ _ => simp [encF] at htag
    | bvar _ | zero | one | neg _ | exp _ | add _ _ | mul _ _ => simp [encT] at ht0
  · obtain ⟨htnb, h1⟩ := h
    have ht' : t.noBVar = true := by simpa [noBVarTCode, decT_encT] using htnb
    exact SeqProv.eqRefl ht' (hprev _ h1 (.eq t t :: Γ) Δ (by simp [mkEqCode, encF]))
  · obtain ⟨c, hc, htag, h1⟩ := h
    obtain ⟨χ, hχ, rfl⟩ := hmemF hc
    cases χ with
    | eq t₁ t₂ =>
      simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair] at h1
      exact SeqProv.eqSymm hχ (hprev _ h1 (.eq t₂ t₁ :: Γ) Δ (by simp [mkEqCode, encF]))
    | bot | le _ _ | imp _ _ | all _ _ => simp [encF] at htag
  · obtain ⟨c₁, hc₁, htag₁, c₂, hc₂, ⟨htag₂, hmid⟩, h1⟩ := h
    obtain ⟨χ₁, hχ₁, rfl⟩ := hmemF hc₁
    obtain ⟨χ₂, hχ₂, rfl⟩ := hmemF hc₂
    cases χ₁ with
    | eq t₁ t₂ =>
      cases χ₂ with
      | eq t₂' t₃ =>
        simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair, beq_iff_eq] at hmid h1
        have heqt : t₂ = t₂' := encT_injective hmid
        subst heqt
        exact SeqProv.eqTrans hχ₁ hχ₂ (hprev _ h1 (.eq t₁ t₃ :: Γ) Δ (by simp [mkEqCode, encF]))
      | bot | le _ _ | imp _ _ | all _ _ => simp [encF] at htag₂
    | bot | le _ _ | imp _ _ | all _ _ => simp [encF] at htag₁
  · obtain ⟨c, hc, htag, h1⟩ := h
    obtain ⟨χ, hχ, rfl⟩ := hmemF hc
    cases χ with
    | eq t₁ t₂ =>
      simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair] at h1
      exact SeqProv.congNeg hχ
        (hprev _ h1 (.eq (.neg t₁) (.neg t₂) :: Γ) Δ (by simp [mkEqCode, mkNegCode, encF, encT]))
    | bot | le _ _ | imp _ _ | all _ _ => simp [encF] at htag
  · obtain ⟨c, hc, htag, h1⟩ := h
    obtain ⟨χ, hχ, rfl⟩ := hmemF hc
    cases χ with
    | eq t₁ t₂ =>
      simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair] at h1
      exact SeqProv.congExp hχ
        (hprev _ h1 (.eq (.exp t₁) (.exp t₂) :: Γ) Δ (by simp [mkEqCode, mkExpCode, encF, encT]))
    | bot | le _ _ | imp _ _ | all _ _ => simp [encF] at htag
  · obtain ⟨c₁, hc₁, htag₁, c₂, hc₂, htag₂, h1⟩ := h
    obtain ⟨χ₁, hχ₁, rfl⟩ := hmemF hc₁
    obtain ⟨χ₂, hχ₂, rfl⟩ := hmemF hc₂
    cases χ₁ with
    | eq t₁ s₁ =>
      cases χ₂ with
      | eq t₂ s₂ =>
        simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair] at h1
        exact SeqProv.congAdd hχ₁ hχ₂
          (hprev _ h1 (.eq (.add t₁ t₂) (.add s₁ s₂) :: Γ) Δ
            (by simp [mkEqCode, mkAddCode, encF, encT]))
      | bot | le _ _ | imp _ _ | all _ _ => simp [encF] at htag₂
    | bot | le _ _ | imp _ _ | all _ _ => simp [encF] at htag₁
  · obtain ⟨c₁, hc₁, htag₁, c₂, hc₂, htag₂, h1⟩ := h
    obtain ⟨χ₁, hχ₁, rfl⟩ := hmemF hc₁
    obtain ⟨χ₂, hχ₂, rfl⟩ := hmemF hc₂
    cases χ₁ with
    | eq t₁ s₁ =>
      cases χ₂ with
      | eq t₂ s₂ =>
        simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair] at h1
        exact SeqProv.congMul hχ₁ hχ₂
          (hprev _ h1 (.eq (.mul t₁ t₂) (.mul s₁ s₂) :: Γ) Δ
            (by simp [mkEqCode, mkMulCode, encF, encT]))
      | bot | le _ _ | imp _ _ | all _ _ => simp [encF] at htag₂
    | bot | le _ _ | imp _ _ | all _ _ => simp [encF] at htag₁
  · obtain ⟨c₁, hc₁, htag₁, c₂, hc₂, ⟨htag₂, hle⟩, h1⟩ := h
    obtain ⟨χ₁, hχ₁, rfl⟩ := hmemF hc₁
    obtain ⟨χ₂, hχ₂, rfl⟩ := hmemF hc₂
    cases χ₁ with
    | eq t₁ s₁ =>
      cases χ₂ with
      | eq t₂ s₂ =>
        simp only [encF, Nat.add_sub_cancel, Nat.unpair_pair] at hle h1
        obtain ⟨χ₃, hχ₃, heq3⟩ := hmemF hle
        have hχ3eq : χ₃ = .le t₁ t₂ := encF_injective heq3
        subst hχ3eq
        exact SeqProv.congLe hχ₁ hχ₂ hχ₃
          (hprev _ h1 (.le s₁ s₂ :: Γ) Δ (by simp [mkLeCode, encF]))
      | bot | le _ _ | imp _ _ | all _ _ => simp [encF] at htag₂
    | bot | le _ _ | imp _ _ | all _ _ => simp [encF] at htag₁

lemma validTrace_sound {tr : List ((List ℕ × List ℕ) × ℕ)} (htr : validTrace tr = true) :
    ∀ p ∈ tr.map Prod.fst, ∀ Γ Δ : List OForm, p = (Γ.map encF, Δ.map encF) → SeqProv Γ Δ := by
  suffices ∀ prev,
      (∀ p ∈ prev, ∀ Γ Δ : List OForm, p = (Γ.map encF, Δ.map encF) → SeqProv Γ Δ) →
      validTraceAux prev tr = true →
      ∀ p ∈ tr.map Prod.fst, ∀ Γ Δ : List OForm, p = (Γ.map encF, Δ.map encF) → SeqProv Γ Δ by
    exact this [] (fun _ h => by simp at h) htr
  clear htr
  induction tr with
  | nil => intro _ _ _ _ h; simp at h
  | cons st rest ih =>
    intro prev hprev hv p hp Γ Δ heq
    simp only [validTraceAux, Bool.and_eq_true] at hv
    simp only [List.map_cons, List.mem_cons] at hp
    rcases hp with rfl | hp'
    · exact validStep_sound hprev hv.1 Γ Δ heq
    · refine ih (st.1 :: prev) (fun q hq => ?_) hv.2 p hp' Γ Δ heq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact validStep_sound hprev hv.1
      · exact hprev q hq'

/- ## Section 4: `Primrec` proofs for code-level operations and trace validation -/

section PrimrecHelpers

lemma primrec_ite_bool {α β : Type*} [Primcodable α] [Primcodable β]
    {c : α → Bool} {f g : α → β} (hc : Primrec c) (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => if c a = true then f a else g a :=
  (Primrec.cond hc hf hg).of_eq fun a => by cases h : c a <;> simp [h]

lemma primrec_bool_not : Primrec Bool.not := Primrec.dom_bool Bool.not
lemma primrec_bool_and : Primrec₂ Bool.and := Primrec.dom_bool₂ Bool.and
lemma primrec_bool_or : Primrec₂ Bool.or := Primrec.dom_bool₂ Bool.or

lemma primrec_beq_nat : Primrec₂ (fun a b : ℕ => a == b) := Primrec.beq

lemma primrec_list_any {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).any (p a) := by
  have hstep : Primrec₂ fun a (x : Bool × β) => x.1 || p a x.2 := by
    refine (Primrec.cond (Primrec.fst.comp Primrec.snd) (Primrec.const true)
      (hp.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).of_eq ?_
    rintro ⟨a, ⟨b1, b2⟩⟩; cases b1 <;> rfl
  refine (Primrec.list_foldl hf (Primrec.const false) hstep).of_eq fun a => ?_
  have key : ∀ (l : List β) (init : Bool),
      l.foldl (fun acc b => acc || p a b) init = (init || l.any (p a)) := by
    intro l; induction l with
    | nil => intro init; simp
    | cons b t ih => intro init; simp only [List.foldl_cons, List.any_cons, ih, Bool.or_assoc]
  simpa using key (f a) false

lemma primrec_list_all {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).all (p a) := by
  have hstep : Primrec₂ fun a (x : Bool × β) => x.1 && p a x.2 := by
    refine (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (hp.comp Primrec.fst (Primrec.snd.comp Primrec.snd)) (Primrec.const false)).of_eq ?_
    rintro ⟨a, ⟨b1, b2⟩⟩; cases b1 <;> rfl
  refine (Primrec.list_foldl hf (Primrec.const true) hstep).of_eq fun a => ?_
  have key : ∀ (l : List β) (init : Bool),
      l.foldl (fun acc b => acc && p a b) init = (init && l.all (p a)) := by
    intro l; induction l with
    | nil => intro init; simp
    | cons b t ih => intro init; simp only [List.foldl_cons, List.all_cons, ih, Bool.and_assoc]
  simpa using key (f a) true

lemma primrec_listContains {α β : Type*} [Primcodable α] [Primcodable β] [BEq β] [LawfulBEq β]
    {f : α → List β} {x : α → β} (hf : Primrec f) (hx : Primrec x) :
    Primrec fun a => listContains (f a) (x a) := by
  letI : DecidableEq β := fun a b => decidable_of_iff ((a == b) = true) beq_iff_eq
  refine (primrec_list_any hf
    ((@Primrec.beq β _ this).comp Primrec.snd (hx.comp Primrec.fst)).to₂).of_eq fun a => ?_
  unfold listContains
  congr 1
  funext b
  rw [Bool.eq_iff_iff]
  simp [beq_iff_eq]

lemma primrec_iterate {α β : Type*} [Primcodable α] [Primcodable β]
    {n : α → ℕ} {x : α → β} {f : α → β → β}
    (hn : Primrec n) (hx : Primrec x) (hf : Primrec₂ f) :
    Primrec fun a => (f a)^[n a] (x a) := by
  have h1 : Primrec fun a => (n a).rec (motive := fun _ => β) (x a) (fun _ ih => f a ih) :=
    Primrec.nat_rec' hn hx (hf.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to₂
  refine h1.of_eq fun a => ?_
  generalize n a = k
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ← ih]

lemma primrec_strong_rec {α σ : Type*} [Primcodable α] [Primcodable σ]
    (f : α → ℕ → σ) (g : α → List σ → ℕ → σ)
    (hg : Primrec fun p : (α × List σ) × ℕ => g p.1.1 p.1.2 p.2)
    (H : ∀ a n, g a ((List.range n).map (f a)) n = f a n) :
    Primrec₂ f := by
  refine Primrec.nat_strong_rec f (g := fun a l => some (g a l l.length)) ?_ ?_
  · exact (Primrec.option_some.comp (hg.comp (Primrec.id.pair (Primrec.list_length.comp Primrec.snd)))).to₂
  · intro a n
    simp [H a n]

lemma primrec_strong_rec₁ {σ : Type*} [Primcodable σ]
    (f : ℕ → σ) (g : List σ → ℕ → σ)
    (hg : Primrec₂ g)
    (H : ∀ n, g ((List.range n).map f) n = f n) :
    Primrec f := by
  have h2 : Primrec₂ (fun (_ : Unit) (n : ℕ) => f n) :=
    primrec_strong_rec (fun _ n => f n) (fun _ l n => g l n)
      (hg.comp (Primrec.snd.comp Primrec.fst) Primrec.snd) (fun _ n => H n)
  exact h2.comp (Primrec.const ()) Primrec.id

lemma primrec_unpair_fst : Primrec (fun n : ℕ => n.unpair.1) :=
  Primrec.fst.comp Primrec.unpair

lemma primrec_unpair_snd : Primrec (fun n : ℕ => n.unpair.2) :=
  Primrec.snd.comp Primrec.unpair

lemma primrec_sub1 : Primrec (fun n : ℕ => n - 1) :=
  Primrec.nat_sub.comp Primrec.id (Primrec.const 1)

lemma primrec_pair_succ : Primrec₂ (fun a b : ℕ => Nat.pair a b + 1) :=
  (Primrec.succ.comp Primrec₂.natPair).to₂

lemma primrec_nat_cases9 {α β : Type*} [Primcodable α] [Primcodable β]
    {tag : α → ℕ} {f0 f1 f2 f3 f4 f5 f6 f7 fd : α → β}
    (ht : Primrec tag) (h0 : Primrec f0) (h1 : Primrec f1) (h2 : Primrec f2)
    (h3 : Primrec f3) (h4 : Primrec f4) (h5 : Primrec f5) (h6 : Primrec f6)
    (h7 : Primrec f7) (hd : Primrec fd) :
    Primrec fun a =>
      match tag a with
      | 0 => f0 a | 1 => f1 a | 2 => f2 a | 3 => f3 a
      | 4 => f4 a | 5 => f5 a | 6 => f6 a | 7 => f7 a | _ => fd a := by
  have h :=
    primrec_ite_bool (Primrec.beq.comp ht (Primrec.const 0)) h0 <|
    primrec_ite_bool (Primrec.beq.comp ht (Primrec.const 1)) h1 <|
    primrec_ite_bool (Primrec.beq.comp ht (Primrec.const 2)) h2 <|
    primrec_ite_bool (Primrec.beq.comp ht (Primrec.const 3)) h3 <|
    primrec_ite_bool (Primrec.beq.comp ht (Primrec.const 4)) h4 <|
    primrec_ite_bool (Primrec.beq.comp ht (Primrec.const 5)) h5 <|
    primrec_ite_bool (Primrec.beq.comp ht (Primrec.const 6)) h6 <|
    primrec_ite_bool (Primrec.beq.comp ht (Primrec.const 7)) h7 hd
  refine h.of_eq fun a => ?_
  rcases tag a with _ | _ | _ | _ | _ | _ | _ | _ | k <;> rfl

lemma primrec_nat_cases6 {α β : Type*} [Primcodable α] [Primcodable β]
    {tag : α → ℕ} {f0 f1 f2 f3 f4 fd : α → β}
    (ht : Primrec tag) (h0 : Primrec f0) (h1 : Primrec f1) (h2 : Primrec f2)
    (h3 : Primrec f3) (h4 : Primrec f4) (hd : Primrec fd) :
    Primrec fun a =>
      match tag a with
      | 0 => f0 a | 1 => f1 a | 2 => f2 a | 3 => f3 a
      | 4 => f4 a | _ => fd a := by
  have h :=
    primrec_ite_bool (Primrec.beq.comp ht (Primrec.const 0)) h0 <|
    primrec_ite_bool (Primrec.beq.comp ht (Primrec.const 1)) h1 <|
    primrec_ite_bool (Primrec.beq.comp ht (Primrec.const 2)) h2 <|
    primrec_ite_bool (Primrec.beq.comp ht (Primrec.const 3)) h3 <|
    primrec_ite_bool (Primrec.beq.comp ht (Primrec.const 4)) h4 hd
  refine h.of_eq fun a => ?_
  rcases tag a with _ | _ | _ | _ | _ | k <;> rfl

lemma primrec_isValidTCode : Primrec isValidTCode := by
  refine primrec_strong_rec₁ isValidTCode isValidTStep ?_ isValidTCode_rec
  have hn : Primrec fun p : List Bool × ℕ => p.2 := Primrec.snd
  have hl : Primrec fun p : List Bool × ℕ => p.1 := Primrec.fst
  have hp1 : Primrec fun p : List Bool × ℕ => (p.2 - 1).unpair.1 :=
    primrec_unpair_fst.comp (primrec_sub1.comp hn)
  have hp2 : Primrec fun p : List Bool × ℕ => (p.2 - 1).unpair.2 :=
    primrec_unpair_snd.comp (primrec_sub1.comp hn)
  have ha : Primrec fun p : List Bool × ℕ => (p.2 - 1).unpair.2.unpair.1 :=
    primrec_unpair_fst.comp hp2
  have hb : Primrec fun p : List Bool × ℕ => (p.2 - 1).unpair.2.unpair.2 :=
    primrec_unpair_snd.comp hp2
  have hget2 := (Primrec.list_getD false).comp hl hp2
  have hgeta := (Primrec.list_getD false).comp hl ha
  have hgetb := (Primrec.list_getD false).comp hl hb
  have hpair := primrec_bool_and.comp hgeta hgetb
  exact (primrec_ite_bool (Primrec.beq.comp hn (Primrec.const 0)) (Primrec.const false)
    (primrec_nat_cases9 hp1 (Primrec.const true) (Primrec.const true)
      (Primrec.beq.comp hp2 (Primrec.const 0)) (Primrec.beq.comp hp2 (Primrec.const 0))
      hget2 hget2 hpair hpair (Primrec.const false))).to₂

lemma primrec_noBVarTCode : Primrec noBVarTCode := by
  refine primrec_strong_rec₁ noBVarTCode noBVarTStep ?_ noBVarTCode_rec
  have hn : Primrec fun p : List Bool × ℕ => p.2 := Primrec.snd
  have hl : Primrec fun p : List Bool × ℕ => p.1 := Primrec.fst
  have hp1 : Primrec fun p : List Bool × ℕ => (p.2 - 1).unpair.1 :=
    primrec_unpair_fst.comp (primrec_sub1.comp hn)
  have hp2 : Primrec fun p : List Bool × ℕ => (p.2 - 1).unpair.2 :=
    primrec_unpair_snd.comp (primrec_sub1.comp hn)
  have ha := primrec_unpair_fst.comp hp2
  have hb := primrec_unpair_snd.comp hp2
  have hget2 := (Primrec.list_getD false).comp hl hp2
  have hpair := primrec_bool_and.comp ((Primrec.list_getD false).comp hl ha)
    ((Primrec.list_getD false).comp hl hb)
  exact (primrec_ite_bool (Primrec.beq.comp hn (Primrec.const 0)) (Primrec.const false)
    (primrec_nat_cases9 hp1 (Primrec.const true) (Primrec.const false)
      (Primrec.beq.comp hp2 (Primrec.const 0)) (Primrec.beq.comp hp2 (Primrec.const 0))
      hget2 hget2 hpair hpair (Primrec.const false))).to₂

lemma primrec_isBoundedTCode : Primrec₂ isBoundedTCode := by
  refine primrec_strong_rec isBoundedTCode isBoundedTStep ?_ isBoundedTCode_rec
  have hk : Primrec fun p : (ℕ × List Bool) × ℕ => p.1.1 := Primrec.fst.comp Primrec.fst
  have hl : Primrec fun p : (ℕ × List Bool) × ℕ => p.1.2 := Primrec.snd.comp Primrec.fst
  have hn : Primrec fun p : (ℕ × List Bool) × ℕ => p.2 := Primrec.snd
  have hp1 := primrec_unpair_fst.comp (primrec_sub1.comp hn)
  have hp2 := primrec_unpair_snd.comp (primrec_sub1.comp hn)
  have ha := primrec_unpair_fst.comp hp2
  have hb := primrec_unpair_snd.comp hp2
  have hget2 := (Primrec.list_getD false).comp hl hp2
  have hpair := primrec_bool_and.comp ((Primrec.list_getD false).comp hl ha)
    ((Primrec.list_getD false).comp hl hb)
  have hlt : Primrec fun p : (ℕ × List Bool) × ℕ => decide ((p.2 - 1).unpair.2 < p.1.1) :=
    (PrimrecRel.decide Primrec.nat_lt).comp hp2 hk
  exact primrec_ite_bool (Primrec.beq.comp hn (Primrec.const 0)) (Primrec.const false)
    (primrec_nat_cases9 hp1 (Primrec.const false) hlt
      (Primrec.beq.comp hp2 (Primrec.const 0)) (Primrec.beq.comp hp2 (Primrec.const 0))
      hget2 hget2 hpair hpair (Primrec.const false))

lemma primrec_hasFVarTCode : Primrec₂ hasFVarTCode := by
  refine primrec_strong_rec hasFVarTCode hasFVarTStep ?_ hasFVarTCode_rec
  have hv : Primrec fun p : (ℕ × List Bool) × ℕ => p.1.1 := Primrec.fst.comp Primrec.fst
  have hl : Primrec fun p : (ℕ × List Bool) × ℕ => p.1.2 := Primrec.snd.comp Primrec.fst
  have hn : Primrec fun p : (ℕ × List Bool) × ℕ => p.2 := Primrec.snd
  have hp1 := primrec_unpair_fst.comp (primrec_sub1.comp hn)
  have hp2 := primrec_unpair_snd.comp (primrec_sub1.comp hn)
  have ha := primrec_unpair_fst.comp hp2
  have hb := primrec_unpair_snd.comp hp2
  have hget2 := (Primrec.list_getD false).comp hl hp2
  have hpair := primrec_ite_bool
    (primrec_bool_and.comp (primrec_isValidTCode.comp ha) (primrec_isValidTCode.comp hb))
    (primrec_bool_or.comp ((Primrec.list_getD false).comp hl ha)
      ((Primrec.list_getD false).comp hl hb))
    (Primrec.const false)
  exact primrec_ite_bool (Primrec.beq.comp hn (Primrec.const 0)) (Primrec.const false)
    (primrec_nat_cases9 hp1 (Primrec.beq.comp hp2 hv) (Primrec.const false)
      (Primrec.const false) (Primrec.const false)
      hget2 hget2 hpair hpair (Primrec.const false))

lemma primrec_substBTCode' : Primrec₂ substBTCode' := by
  have hinner : Primrec₂ fun (ku : ℕ × ℕ) (n : ℕ) =>
      if isValidTCode ku.2 then substBTCode ku n else 0 := by
    let g (ku : ℕ × ℕ) (l : List ℕ) (n : ℕ) : ℕ :=
      if isValidTCode ku.2 then substBTStep ku l n else 0
    refine primrec_strong_rec (fun ku n => if isValidTCode ku.2 then substBTCode ku n else 0) g ?_ ?_
    · have hku : Primrec fun p : ((ℕ × ℕ) × List ℕ) × ℕ => p.1.1 := Primrec.fst.comp Primrec.fst
      have hk := Primrec.fst.comp hku
      have hu := Primrec.snd.comp hku
      have hl : Primrec fun p : ((ℕ × ℕ) × List ℕ) × ℕ => p.1.2 := Primrec.snd.comp Primrec.fst
      have hn : Primrec fun p : ((ℕ × ℕ) × List ℕ) × ℕ => p.2 := Primrec.snd
      have hp1 := primrec_unpair_fst.comp (primrec_sub1.comp hn)
      have hp2 := primrec_unpair_snd.comp (primrec_sub1.comp hn)
      have ha := primrec_unpair_fst.comp hp2
      have hb := primrec_unpair_snd.comp hp2
      have hga := (Primrec.list_getD 0).comp hl ha
      have hgb := (Primrec.list_getD 0).comp hl hb
      have hg2 := (Primrec.list_getD 0).comp hl hp2
      have hstep : Primrec fun p : ((ℕ × ℕ) × List ℕ) × ℕ => substBTStep p.1.1 p.1.2 p.2 :=
        primrec_ite_bool (Primrec.beq.comp hn (Primrec.const 0)) (Primrec.const 0)
          (primrec_nat_cases9 hp1 hn
            (primrec_ite_bool (Primrec.beq.comp hp2 hk) hu hn)
            (primrec_ite_bool (Primrec.beq.comp hp2 (Primrec.const 0)) hn (Primrec.const 0))
            (primrec_ite_bool (Primrec.beq.comp hp2 (Primrec.const 0)) hn (Primrec.const 0))
            (primrec_ite_bool (Primrec.beq.comp hg2 (Primrec.const 0)) (Primrec.const 0)
              (primrec_pair_succ.comp (Primrec.const 4) hg2))
            (primrec_ite_bool (Primrec.beq.comp hg2 (Primrec.const 0)) (Primrec.const 0)
              (primrec_pair_succ.comp (Primrec.const 5) hg2))
            (primrec_ite_bool
              (primrec_bool_or.comp (Primrec.beq.comp hga (Primrec.const 0))
                (Primrec.beq.comp hgb (Primrec.const 0)))
              (Primrec.const 0)
              (primrec_pair_succ.comp (Primrec.const 6) (Primrec₂.natPair.comp hga hgb)))
            (primrec_ite_bool
              (primrec_bool_or.comp (Primrec.beq.comp hga (Primrec.const 0))
                (Primrec.beq.comp hgb (Primrec.const 0)))
              (Primrec.const 0)
              (primrec_pair_succ.comp (Primrec.const 7) (Primrec₂.natPair.comp hga hgb)))
            (Primrec.const 0))
      exact primrec_ite_bool (primrec_isValidTCode.comp hu) hstep (Primrec.const 0)
    · intro ku n
      dsimp only [g]
      by_cases hku : isValidTCode ku.2 = true
      · simp only [hku, ↓reduceIte]
        exact substBTCode_rec ku hku n
      · simp [hku]
  exact hinner

lemma primrec_tListEncCode : Primrec tListEncCode := by
  refine primrec_strong_rec₁ tListEncCode tListEncStep ?_ tListEncCode_rec
  have hl : Primrec fun p : List (List ℕ) × ℕ => p.1 := Primrec.fst
  have hn : Primrec fun p : List (List ℕ) × ℕ => p.2 := Primrec.snd
  have hp1 := primrec_unpair_fst.comp (primrec_sub1.comp hn)
  have hp2 := primrec_unpair_snd.comp (primrec_sub1.comp hn)
  have ha := primrec_unpair_fst.comp hp2
  have hb := primrec_unpair_snd.comp hp2
  have hg2 := (Primrec.list_getD ([] : List ℕ)).comp hl hp2
  have hga := (Primrec.list_getD ([] : List ℕ)).comp hl ha
  have hgb := (Primrec.list_getD ([] : List ℕ)).comp hl hb
  have happ := Primrec.list_append.comp hga hgb
  have hbvar : Primrec fun p : List (List ℕ) × ℕ => [2 * (2 * (p.2 - 1).unpair.2 + 1)] :=
    Primrec.list_cons.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) hp2)))
      (Primrec.const [])
  exact (primrec_ite_bool (Primrec.beq.comp hn (Primrec.const 0)) (Primrec.const [])
    (primrec_nat_cases9 hp1 (Primrec.const []) hbvar
      (primrec_ite_bool (Primrec.beq.comp hp2 (Primrec.const 0)) (Primrec.const [13]) (Primrec.const []))
      (primrec_ite_bool (Primrec.beq.comp hp2 (Primrec.const 0)) (Primrec.const [17]) (Primrec.const []))
      (primrec_ite_bool (primrec_isValidTCode.comp hp2) (Primrec.list_cons.comp (Primrec.const 9) hg2) (Primrec.const []))
      (primrec_ite_bool (primrec_isValidTCode.comp hp2) (Primrec.list_cons.comp (Primrec.const 3) hg2) (Primrec.const []))
      (primrec_ite_bool (primrec_bool_and.comp (primrec_isValidTCode.comp ha) (primrec_isValidTCode.comp hb))
        (Primrec.list_cons.comp (Primrec.const 1) happ) (Primrec.const []))
      (primrec_ite_bool (primrec_bool_and.comp (primrec_isValidTCode.comp ha) (primrec_isValidTCode.comp hb))
        (Primrec.list_cons.comp (Primrec.const 5) happ) (Primrec.const []))
      (Primrec.const []))).to₂

lemma primrec_isValidFCode : Primrec isValidFCode := by
  refine primrec_strong_rec₁ isValidFCode isValidFStep ?_ isValidFCode_rec
  have hl : Primrec fun p : List Bool × ℕ => p.1 := Primrec.fst
  have hn : Primrec fun p : List Bool × ℕ => p.2 := Primrec.snd
  have hp1 := primrec_unpair_fst.comp (primrec_sub1.comp hn)
  have hp2 := primrec_unpair_snd.comp (primrec_sub1.comp hn)
  have ha := primrec_unpair_fst.comp hp2
  have hb := primrec_unpair_snd.comp hp2
  have hvt := primrec_bool_and.comp (primrec_isValidTCode.comp ha) (primrec_isValidTCode.comp hb)
  have hvf := primrec_bool_and.comp ((Primrec.list_getD false).comp hl ha)
    ((Primrec.list_getD false).comp hl hb)
  have hvb := (Primrec.list_getD false).comp hl hb
  exact (primrec_ite_bool (Primrec.beq.comp hn (Primrec.const 0)) (Primrec.const false)
    (primrec_nat_cases6 hp1 (Primrec.beq.comp hp2 (Primrec.const 0)) hvt hvt hvf hvb
      (Primrec.const false))).to₂

lemma primrec_hasFVarFCode : Primrec₂ hasFVarFCode := by
  refine primrec_strong_rec hasFVarFCode hasFVarFStep ?_ hasFVarFCode_rec
  have hv : Primrec fun p : (ℕ × List Bool) × ℕ => p.1.1 := Primrec.fst.comp Primrec.fst
  have hl : Primrec fun p : (ℕ × List Bool) × ℕ => p.1.2 := Primrec.snd.comp Primrec.fst
  have hn : Primrec fun p : (ℕ × List Bool) × ℕ => p.2 := Primrec.snd
  have hp1 := primrec_unpair_fst.comp (primrec_sub1.comp hn)
  have hp2 := primrec_unpair_snd.comp (primrec_sub1.comp hn)
  have ha := primrec_unpair_fst.comp hp2
  have hb := primrec_unpair_snd.comp hp2
  have hft := primrec_ite_bool
    (primrec_bool_and.comp (primrec_isValidTCode.comp ha) (primrec_isValidTCode.comp hb))
    (primrec_bool_or.comp (primrec_hasFVarTCode.comp hv ha)
      (primrec_hasFVarTCode.comp hv hb))
    (Primrec.const false)
  have hff := primrec_ite_bool
    (primrec_bool_and.comp (primrec_isValidFCode.comp ha) (primrec_isValidFCode.comp hb))
    (primrec_bool_or.comp ((Primrec.list_getD false).comp hl ha)
      ((Primrec.list_getD false).comp hl hb))
    (Primrec.const false)
  have hfb := (Primrec.list_getD false).comp hl hb
  exact primrec_ite_bool (Primrec.beq.comp hn (Primrec.const 0)) (Primrec.const false)
    (primrec_nat_cases6 hp1 (Primrec.const false) hft hft hff hfb (Primrec.const false))

lemma primrec_substBFCode : Primrec₂ substBFCode := by
  refine primrec_strong_rec substBFCode substBFStep ?_ substBFCode_rec
  have hku : Primrec fun p : ((ℕ × ℕ) × List ℕ) × ℕ => p.1.1 := Primrec.fst.comp Primrec.fst
  have hk := Primrec.fst.comp hku
  have hu := Primrec.snd.comp hku
  have hl : Primrec fun p : ((ℕ × ℕ) × List ℕ) × ℕ => p.1.2 := Primrec.snd.comp Primrec.fst
  have hn : Primrec fun p : ((ℕ × ℕ) × List ℕ) × ℕ => p.2 := Primrec.snd
  have hp1 := primrec_unpair_fst.comp (primrec_sub1.comp hn)
  have hp2 := primrec_unpair_snd.comp (primrec_sub1.comp hn)
  have ha := primrec_unpair_fst.comp hp2
  have hb := primrec_unpair_snd.comp hp2
  have hta := primrec_substBTCode'.comp hku ha
  have htb := primrec_substBTCode'.comp hku hb
  have hga := (Primrec.list_getD 0).comp hl ha
  have hgb := (Primrec.list_getD 0).comp hl hb
  have h0 := primrec_ite_bool
    (primrec_bool_and.comp (Primrec.beq.comp hp2 (Primrec.const 0)) (primrec_isValidTCode.comp hu))
    hn (Primrec.const 0)
  have h1 := primrec_ite_bool
    (primrec_bool_or.comp (Primrec.beq.comp hta (Primrec.const 0)) (Primrec.beq.comp htb (Primrec.const 0)))
    (Primrec.const 0) (primrec_pair_succ.comp (Primrec.const 1) (Primrec₂.natPair.comp hta htb))
  have h2 := primrec_ite_bool
    (primrec_bool_or.comp (Primrec.beq.comp hta (Primrec.const 0)) (Primrec.beq.comp htb (Primrec.const 0)))
    (Primrec.const 0) (primrec_pair_succ.comp (Primrec.const 2) (Primrec₂.natPair.comp hta htb))
  have h3 := primrec_ite_bool
    (primrec_bool_or.comp (Primrec.beq.comp hga (Primrec.const 0)) (Primrec.beq.comp hgb (Primrec.const 0)))
    (Primrec.const 0) (primrec_pair_succ.comp (Primrec.const 3) (Primrec₂.natPair.comp hga hgb))
  have h4 := primrec_ite_bool (Primrec.beq.comp ha hk)
    (primrec_ite_bool
      (primrec_bool_and.comp (primrec_isValidFCode.comp hb) (primrec_isValidTCode.comp hu))
      hn (Primrec.const 0))
    (primrec_ite_bool (Primrec.beq.comp hgb (Primrec.const 0)) (Primrec.const 0)
      (primrec_pair_succ.comp (Primrec.const 4) (Primrec₂.natPair.comp ha hgb)))
  exact primrec_ite_bool (Primrec.beq.comp hn (Primrec.const 0)) (Primrec.const 0)
    (primrec_nat_cases6 hp1 h0 h1 h2 h3 h4 (Primrec.const 0))

lemma primrec_encStep : Primrec encStep := by
  let S := (Bool × List (ℕ × ℕ)) × List ℕ
  have hok : Primrec fun st : S => st.1.1 := Primrec.fst.comp Primrec.fst
  have hstk : Primrec fun st : S => st.1.2 := Primrec.snd.comp Primrec.fst
  have hout : Primrec fun st : S => st.2 := Primrec.snd
  have hcons : Primrec fun p : S × ((ℕ × ℕ) × List (ℕ × ℕ)) =>
      let st := p.1
      let revOut := st.2
      let tag := p.2.1.1
      let val := p.2.1.2
      let rest := p.2.2
      if tag == 0 then ((true, rest), val :: revOut)
      else if tag == 1 then
        let k := val.unpair.1
        let c := val.unpair.2
        if c == 0 then ((false, []), revOut)
        else
          let q := (c - 1).unpair
          match q.1 with
          | 0 =>
            if q.2 == 0 then ((true, (0, 4 * k + 11) :: rest), revOut)
            else ((false, []), revOut)
          | 1 =>
            let a := q.2.unpair.1
            let b := q.2.unpair.2
            if isBoundedTCode k a && isBoundedTCode k b then
              ((true, (0, 2 * Nat.pair k (encode (tListEncCode a))) ::
                      (0, 2 * Nat.pair k (encode (tListEncCode b))) :: rest), revOut)
            else ((false, []), revOut)
          | 2 =>
            let a := q.2.unpair.1
            let b := q.2.unpair.2
            if isBoundedTCode k a && isBoundedTCode k b then
              ((true, (0, 13) :: (0, 4 * k + 3) ::
                      (0, 2 * Nat.pair k (encode (tListEncCode a))) ::
                      (0, 2 * Nat.pair k (encode (tListEncCode b))) :: rest), revOut)
            else ((false, []), revOut)
          | 3 =>
            let a := q.2.unpair.1
            let b := q.2.unpair.2
            ((true, (0, 3) :: (1, Nat.pair k a) :: (1, Nat.pair k b) :: rest), revOut)
          | 4 =>
            let m := q.2.unpair.1
            let body := q.2.unpair.2
            if m == k then ((true, (0, 7) :: (1, Nat.pair (k + 1) body) :: rest), revOut)
            else ((false, []), revOut)
          | _ => ((false, []), revOut)
      else ((false, []), revOut) := by
    let P := S × ((ℕ × ℕ) × List (ℕ × ℕ))
    have hrev : Primrec fun p : P => p.1.2 := Primrec.snd.comp Primrec.fst
    have htag : Primrec fun p : P => p.2.1.1 := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
    have hval : Primrec fun p : P => p.2.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    have hrest : Primrec fun p : P => p.2.2 := Primrec.snd.comp Primrec.snd
    have hfail : Primrec fun p : P => ((false, ([] : List (ℕ × ℕ))), p.1.2) :=
      (Primrec.const (false, ([] : List (ℕ × ℕ)))).pair hrev
    have hk := primrec_unpair_fst.comp hval
    have hc := primrec_unpair_snd.comp hval
    have hq1 := primrec_unpair_fst.comp (primrec_sub1.comp hc)
    have hq2 := primrec_unpair_snd.comp (primrec_sub1.comp hc)
    have ha := primrec_unpair_fst.comp hq2
    have hb := primrec_unpair_snd.comp hq2
    have htokA : Primrec fun p : P =>
        2 * Nat.pair p.2.1.2.unpair.1 (encode (tListEncCode (p.2.1.2.unpair.2 - 1).unpair.2.unpair.1)) :=
      Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec₂.natPair.comp hk (Primrec.encode.comp (primrec_tListEncCode.comp ha)))
    have htokB : Primrec fun p : P =>
        2 * Nat.pair p.2.1.2.unpair.1 (encode (tListEncCode (p.2.1.2.unpair.2 - 1).unpair.2.unpair.2)) :=
      Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec₂.natPair.comp hk (Primrec.encode.comp (primrec_tListEncCode.comp hb)))
    have hbdAB := primrec_bool_and.comp (primrec_isBoundedTCode.comp hk ha)
      (primrec_isBoundedTCode.comp hk hb)
    have hitem0 : ∀ {f : P → ℕ}, Primrec f → Primrec fun p : P => ((0 : ℕ), f p) :=
      fun hf => (Primrec.const 0).pair hf
    have hitem1 : ∀ {f : P → ℕ}, Primrec f → Primrec fun p : P => ((1 : ℕ), f p) :=
      fun hf => (Primrec.const 1).pair hf
    have hmk : ∀ {f : P → List (ℕ × ℕ)}, Primrec f → Primrec fun p : P => ((true, f p), p.1.2) :=
      fun hf => ((Primrec.const true).pair hf).pair hrev
    have hc0 := primrec_ite_bool (Primrec.beq.comp hq2 (Primrec.const 0))
      (hmk (Primrec.list_cons.comp
        (hitem0 (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) hk) (Primrec.const 11)))
        hrest))
      hfail
    have hc1 := primrec_ite_bool hbdAB
      (hmk (Primrec.list_cons.comp (hitem0 htokA) (Primrec.list_cons.comp (hitem0 htokB) hrest)))
      hfail
    have hc2 := primrec_ite_bool hbdAB
      (hmk (Primrec.list_cons.comp (Primrec.const (0, 13))
        (Primrec.list_cons.comp
          (hitem0 (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) hk) (Primrec.const 3)))
          (Primrec.list_cons.comp (hitem0 htokA) (Primrec.list_cons.comp (hitem0 htokB) hrest)))))
      hfail
    have hc3 := hmk (Primrec.list_cons.comp (Primrec.const (0, 3))
      (Primrec.list_cons.comp (hitem1 (Primrec₂.natPair.comp hk ha))
        (Primrec.list_cons.comp (hitem1 (Primrec₂.natPair.comp hk hb)) hrest)))
    have hc4 := primrec_ite_bool (Primrec.beq.comp ha hk)
      (hmk (Primrec.list_cons.comp (Primrec.const (0, 7))
        (Primrec.list_cons.comp (hitem1 (Primrec₂.natPair.comp (Primrec.succ.comp hk) hb)) hrest)))
      hfail
    have htag1 := primrec_ite_bool (Primrec.beq.comp hc (Primrec.const 0)) hfail
      (primrec_nat_cases6 hq1 hc0 hc1 hc2 hc3 hc4 hfail)
    exact primrec_ite_bool (Primrec.beq.comp htag (Primrec.const 0))
      (((Primrec.const true).pair hrest).pair (Primrec.list_cons.comp hval hrev))
      (primrec_ite_bool (Primrec.beq.comp htag (Primrec.const 1)) htag1 hfail)
  have hmatch := Primrec.list_casesOn hstk Primrec.id hcons.to₂
  exact (primrec_ite_bool (primrec_bool_not.comp hok) Primrec.id hmatch).of_eq fun st => by
    unfold encStep
    cases st.1.1 <;> cases st.1.2 <;> rfl

lemma primrec_encodeIfBounded : Primrec encodeIfBounded := by
  have hsteps : Primrec fun c : ℕ => 5 * c + 5 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 5) Primrec.id) (Primrec.const 5)
  have hinit : Primrec fun c : ℕ => ((true, [(1, Nat.pair 0 c)]), ([] : List ℕ)) :=
    ((Primrec.const true).pair
      (Primrec.list_cons.comp ((Primrec.const 1).pair (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id))
        (Primrec.const []))).pair (Primrec.const [])
  have hres : Primrec fun c : ℕ => encStep^[5 * c + 5] ((true, [(1, Nat.pair 0 c)]), []) :=
    primrec_iterate hsteps hinit (primrec_encStep.comp Primrec.snd).to₂
  have hemp : Primrec fun c : ℕ =>
      (encStep^[5 * c + 5] ((true, [(1, Nat.pair 0 c)]), [])).1.2.isEmpty :=
    (Primrec.beq.comp (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp hres)))
      (Primrec.const 0)).of_eq fun c => by
      cases (encStep^[5 * c + 5] ((true, [(1, Nat.pair 0 c)]), [])).1.2 <;> rfl
  exact primrec_ite_bool
    (primrec_bool_and.comp (Primrec.fst.comp (Primrec.fst.comp hres)) hemp)
    (Primrec.option_some.comp (Primrec.encode.comp (Primrec.list_reverse.comp (Primrec.snd.comp hres))))
    (Primrec.const none)

lemma primrec_mkEqCode : Primrec₂ mkEqCode :=
  (primrec_pair_succ.comp (Primrec.const 1) Primrec₂.natPair).to₂

lemma primrec_mkLeCode : Primrec₂ mkLeCode :=
  (primrec_pair_succ.comp (Primrec.const 2) Primrec₂.natPair).to₂

lemma primrec_mkImpCode : Primrec₂ mkImpCode :=
  (primrec_pair_succ.comp (Primrec.const 3) Primrec₂.natPair).to₂

lemma primrec_mkNegCode : Primrec mkNegCode :=
  primrec_pair_succ.comp (Primrec.const 4) Primrec.id

lemma primrec_mkExpCode : Primrec mkExpCode :=
  primrec_pair_succ.comp (Primrec.const 5) Primrec.id

lemma primrec_mkAddCode : Primrec₂ mkAddCode :=
  (primrec_pair_succ.comp (Primrec.const 6) Primrec₂.natPair).to₂

lemma primrec_mkMulCode : Primrec₂ mkMulCode :=
  (primrec_pair_succ.comp (Primrec.const 7) Primrec₂.natPair).to₂

lemma primrec_validStep : Primrec₂ validStep := by
  let A := List (List ℕ × List ℕ) × ((List ℕ × List ℕ) × ℕ)
  have hprev : Primrec fun a : A => a.1 := Primrec.fst
  have hΓ : Primrec fun a : A => a.2.1.1 := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hΔ : Primrec fun a : A => a.2.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have ht : Primrec fun a : A => a.2.2 := Primrec.snd.comp Primrec.snd
  have hwf : Primrec fun a : A =>
      (a.2.1.1.all isValidFCode) && (a.2.1.2.all isValidFCode) && isValidTCode a.2.2 :=
    primrec_bool_and.comp
      (primrec_bool_and.comp
        (primrec_list_all hΓ (primrec_isValidFCode.comp Primrec.snd).to₂)
        (primrec_list_all hΔ (primrec_isValidFCode.comp Primrec.snd).to₂))
      (primrec_isValidTCode.comp ht)
  have hr1 : Primrec fun a : A => a.2.1.1.any (fun c => listContains a.2.1.2 c) :=
    primrec_list_any hΓ (primrec_listContains (hΔ.comp Primrec.fst) Primrec.snd).to₂
  have hr2 : Primrec fun a : A => listContains a.2.1.1 mkBotCode :=
    primrec_listContains hΓ (Primrec.const mkBotCode)
  have hr3 : Primrec fun a : A =>
      a.2.1.1.any (fun c =>
        let p := (c - 1).unpair
        (p.1 == 3) &&
        listContains a.1 (a.2.1.1, p.2.unpair.1 :: a.2.1.2) &&
        listContains a.1 (p.2.unpair.2 :: a.2.1.1, a.2.1.2)) := by
    have hc : Primrec fun x : A × ℕ => x.2 := Primrec.snd
    have hp1 := primrec_unpair_fst.comp (primrec_sub1.comp hc)
    have hp2 := primrec_unpair_snd.comp (primrec_sub1.comp hc)
    have ha := primrec_unpair_fst.comp hp2
    have hb := primrec_unpair_snd.comp hp2
    exact primrec_list_any hΓ
      (primrec_bool_and.comp
        (primrec_bool_and.comp (Primrec.beq.comp hp1 (Primrec.const 3))
          (primrec_listContains (hprev.comp Primrec.fst)
            ((hΓ.comp Primrec.fst).pair (Primrec.list_cons.comp ha (hΔ.comp Primrec.fst)))))
        (primrec_listContains (hprev.comp Primrec.fst)
          ((Primrec.list_cons.comp hb (hΓ.comp Primrec.fst)).pair (hΔ.comp Primrec.fst)))).to₂
  have hr4 : Primrec fun a : A =>
      a.2.1.2.any (fun c =>
        let p := (c - 1).unpair
        (p.1 == 3) &&
        listContains a.1 (p.2.unpair.1 :: a.2.1.1, p.2.unpair.2 :: a.2.1.2)) := by
    have hc : Primrec fun x : A × ℕ => x.2 := Primrec.snd
    have hp1 := primrec_unpair_fst.comp (primrec_sub1.comp hc)
    have hp2 := primrec_unpair_snd.comp (primrec_sub1.comp hc)
    have ha := primrec_unpair_fst.comp hp2
    have hb := primrec_unpair_snd.comp hp2
    exact primrec_list_any hΔ
      (primrec_bool_and.comp (Primrec.beq.comp hp1 (Primrec.const 3))
        (primrec_listContains (hprev.comp Primrec.fst)
          ((Primrec.list_cons.comp ha (hΓ.comp Primrec.fst)).pair
            (Primrec.list_cons.comp hb (hΔ.comp Primrec.fst))))).to₂
  have hr5 : Primrec fun a : A =>
      noBVarTCode a.2.2 &&
      a.2.1.1.any (fun c =>
        let p := (c - 1).unpair
        (p.1 == 4) &&
        listContains a.1 (substBFCode (p.2.unpair.1, a.2.2) p.2.unpair.2 :: a.2.1.1, a.2.1.2)) := by
    have hc : Primrec fun x : A × ℕ => x.2 := Primrec.snd
    have hp1 := primrec_unpair_fst.comp (primrec_sub1.comp hc)
    have hp2 := primrec_unpair_snd.comp (primrec_sub1.comp hc)
    have hk := primrec_unpair_fst.comp hp2
    have hbody := primrec_unpair_snd.comp hp2
    have hsub := primrec_substBFCode.comp (hk.pair (ht.comp Primrec.fst)) hbody
    exact primrec_bool_and.comp (primrec_noBVarTCode.comp ht)
      (primrec_list_any hΓ
        (primrec_bool_and.comp (Primrec.beq.comp hp1 (Primrec.const 4))
          (primrec_listContains (hprev.comp Primrec.fst)
            ((Primrec.list_cons.comp hsub (hΓ.comp Primrec.fst)).pair (hΔ.comp Primrec.fst)))).to₂)
  have hr6 : Primrec fun a : A =>
      let pt := (a.2.2 - 1).unpair
      (pt.1 == 0) &&
      !(a.2.1.1.any (fun c => hasFVarFCode pt.2 c)) &&
      !(a.2.1.2.any (fun c => hasFVarFCode pt.2 c)) &&
      a.2.1.2.any (fun c =>
        let p := (c - 1).unpair
        (p.1 == 4) &&
        listContains a.1 (a.2.1.1, substBFCode (p.2.unpair.1, a.2.2) p.2.unpair.2 :: a.2.1.2)) := by
    have hpt1 := primrec_unpair_fst.comp (primrec_sub1.comp ht)
    have hpt2 := primrec_unpair_snd.comp (primrec_sub1.comp ht)
    have hfvΓ := primrec_bool_not.comp
      (primrec_list_any hΓ (primrec_hasFVarFCode.comp (hpt2.comp Primrec.fst) Primrec.snd).to₂)
    have hfvΔ := primrec_bool_not.comp
      (primrec_list_any hΔ (primrec_hasFVarFCode.comp (hpt2.comp Primrec.fst) Primrec.snd).to₂)
    have hc : Primrec fun x : A × ℕ => x.2 := Primrec.snd
    have hp1 := primrec_unpair_fst.comp (primrec_sub1.comp hc)
    have hp2 := primrec_unpair_snd.comp (primrec_sub1.comp hc)
    have hk := primrec_unpair_fst.comp hp2
    have hbody := primrec_unpair_snd.comp hp2
    have hsub := primrec_substBFCode.comp (hk.pair (ht.comp Primrec.fst)) hbody
    have hallΔ := primrec_list_any hΔ
      (primrec_bool_and.comp (Primrec.beq.comp hp1 (Primrec.const 4))
        (primrec_listContains (hprev.comp Primrec.fst)
          ((hΓ.comp Primrec.fst).pair (Primrec.list_cons.comp hsub (hΔ.comp Primrec.fst))))).to₂
    exact primrec_bool_and.comp
      (primrec_bool_and.comp (primrec_bool_and.comp (Primrec.beq.comp hpt1 (Primrec.const 0)) hfvΓ) hfvΔ)
      hallΔ
  have hr7 : Primrec fun a : A =>
      noBVarTCode a.2.2 && listContains a.1 (mkEqCode a.2.2 a.2.2 :: a.2.1.1, a.2.1.2) :=
    primrec_bool_and.comp (primrec_noBVarTCode.comp ht)
      (primrec_listContains hprev ((Primrec.list_cons.comp (primrec_mkEqCode.comp ht ht) hΓ).pair hΔ))
  have hr8 : Primrec fun a : A =>
      a.2.1.1.any (fun c =>
        let p := (c - 1).unpair
        (p.1 == 1) && listContains a.1 (mkEqCode p.2.unpair.2 p.2.unpair.1 :: a.2.1.1, a.2.1.2)) := by
    have hc : Primrec fun x : A × ℕ => x.2 := Primrec.snd
    have hp1 := primrec_unpair_fst.comp (primrec_sub1.comp hc)
    have hp2 := primrec_unpair_snd.comp (primrec_sub1.comp hc)
    have ha := primrec_unpair_fst.comp hp2
    have hb := primrec_unpair_snd.comp hp2
    exact primrec_list_any hΓ
      (primrec_bool_and.comp (Primrec.beq.comp hp1 (Primrec.const 1))
        (primrec_listContains (hprev.comp Primrec.fst)
          ((Primrec.list_cons.comp (primrec_mkEqCode.comp hb ha) (hΓ.comp Primrec.fst)).pair
            (hΔ.comp Primrec.fst)))).to₂
  have hr9 : Primrec fun a : A =>
      a.2.1.1.any (fun c₁ =>
        let p₁ := (c₁ - 1).unpair
        (p₁.1 == 1) &&
        a.2.1.1.any (fun c₂ =>
          let p₂ := (c₂ - 1).unpair
          (p₂.1 == 1) && (p₁.2.unpair.2 == p₂.2.unpair.1) &&
          listContains a.1 (mkEqCode p₁.2.unpair.1 p₂.2.unpair.2 :: a.2.1.1, a.2.1.2))) := by
    have hc₁ : Primrec fun x : A × ℕ => x.2 := Primrec.snd
    have hp₁1 := primrec_unpair_fst.comp (primrec_sub1.comp hc₁)
    have hp₁2 := primrec_unpair_snd.comp (primrec_sub1.comp hc₁)
    have hinner : Primrec fun x : A × ℕ =>
        x.1.2.1.1.any (fun c₂ =>
          let p₂ := (c₂ - 1).unpair
          (p₂.1 == 1) && ((x.2 - 1).unpair.2.unpair.2 == p₂.2.unpair.1) &&
          listContains x.1.1 (mkEqCode (x.2 - 1).unpair.2.unpair.1 p₂.2.unpair.2 :: x.1.2.1.1, x.1.2.1.2)) := by
      have hc₂ : Primrec fun y : (A × ℕ) × ℕ => y.2 := Primrec.snd
      have hp₂1 := primrec_unpair_fst.comp (primrec_sub1.comp hc₂)
      have hp₂2 := primrec_unpair_snd.comp (primrec_sub1.comp hc₂)
      have ha₁ : Primrec fun y : (A × ℕ) × ℕ => (y.1.2 - 1).unpair.2.unpair.1 :=
        (primrec_unpair_fst.comp hp₁2).comp Primrec.fst
      have hb₁ : Primrec fun y : (A × ℕ) × ℕ => (y.1.2 - 1).unpair.2.unpair.2 :=
        (primrec_unpair_snd.comp hp₁2).comp Primrec.fst
      have ha₂ := primrec_unpair_fst.comp hp₂2
      have hb₂ := primrec_unpair_snd.comp hp₂2
      have hA : Primrec fun y : (A × ℕ) × ℕ => y.1.1 := Primrec.fst.comp Primrec.fst
      exact primrec_list_any (hΓ.comp Primrec.fst)
        (primrec_bool_and.comp
          (primrec_bool_and.comp (Primrec.beq.comp hp₂1 (Primrec.const 1)) (Primrec.beq.comp hb₁ ha₂))
          (primrec_listContains (hprev.comp hA)
            ((Primrec.list_cons.comp (primrec_mkEqCode.comp ha₁ hb₂) (hΓ.comp hA)).pair (hΔ.comp hA)))).to₂
    exact primrec_list_any hΓ
      (primrec_bool_and.comp (Primrec.beq.comp hp₁1 (Primrec.const 1)) hinner).to₂
  have hr10 : Primrec fun a : A =>
      a.2.1.1.any (fun c =>
        let p := (c - 1).unpair
        (p.1 == 1) &&
        listContains a.1 (mkEqCode (mkNegCode p.2.unpair.1) (mkNegCode p.2.unpair.2) :: a.2.1.1, a.2.1.2)) := by
    have hc : Primrec fun x : A × ℕ => x.2 := Primrec.snd
    have hp1 := primrec_unpair_fst.comp (primrec_sub1.comp hc)
    have hp2 := primrec_unpair_snd.comp (primrec_sub1.comp hc)
    have ha := primrec_mkNegCode.comp (primrec_unpair_fst.comp hp2)
    have hb := primrec_mkNegCode.comp (primrec_unpair_snd.comp hp2)
    exact primrec_list_any hΓ
      (primrec_bool_and.comp (Primrec.beq.comp hp1 (Primrec.const 1))
        (primrec_listContains (hprev.comp Primrec.fst)
          ((Primrec.list_cons.comp (primrec_mkEqCode.comp ha hb) (hΓ.comp Primrec.fst)).pair
            (hΔ.comp Primrec.fst)))).to₂
  have hr11 : Primrec fun a : A =>
      a.2.1.1.any (fun c =>
        let p := (c - 1).unpair
        (p.1 == 1) &&
        listContains a.1 (mkEqCode (mkExpCode p.2.unpair.1) (mkExpCode p.2.unpair.2) :: a.2.1.1, a.2.1.2)) := by
    have hc : Primrec fun x : A × ℕ => x.2 := Primrec.snd
    have hp1 := primrec_unpair_fst.comp (primrec_sub1.comp hc)
    have hp2 := primrec_unpair_snd.comp (primrec_sub1.comp hc)
    have ha := primrec_mkExpCode.comp (primrec_unpair_fst.comp hp2)
    have hb := primrec_mkExpCode.comp (primrec_unpair_snd.comp hp2)
    exact primrec_list_any hΓ
      (primrec_bool_and.comp (Primrec.beq.comp hp1 (Primrec.const 1))
        (primrec_listContains (hprev.comp Primrec.fst)
          ((Primrec.list_cons.comp (primrec_mkEqCode.comp ha hb) (hΓ.comp Primrec.fst)).pair
            (hΔ.comp Primrec.fst)))).to₂
  have hr12 : Primrec fun a : A =>
      a.2.1.1.any (fun c₁ =>
        let p₁ := (c₁ - 1).unpair
        (p₁.1 == 1) &&
        a.2.1.1.any (fun c₂ =>
          let p₂ := (c₂ - 1).unpair
          (p₂.1 == 1) &&
          listContains a.1
            (mkEqCode (mkAddCode p₁.2.unpair.1 p₂.2.unpair.1)
                      (mkAddCode p₁.2.unpair.2 p₂.2.unpair.2) :: a.2.1.1, a.2.1.2))) := by
    have hc₁ : Primrec fun x : A × ℕ => x.2 := Primrec.snd
    have hp₁1 := primrec_unpair_fst.comp (primrec_sub1.comp hc₁)
    have hp₁2 := primrec_unpair_snd.comp (primrec_sub1.comp hc₁)
    have hinner : Primrec fun x : A × ℕ =>
        x.1.2.1.1.any (fun c₂ =>
          let p₂ := (c₂ - 1).unpair
          (p₂.1 == 1) &&
          listContains x.1.1
            (mkEqCode (mkAddCode (x.2 - 1).unpair.2.unpair.1 p₂.2.unpair.1)
                      (mkAddCode (x.2 - 1).unpair.2.unpair.2 p₂.2.unpair.2) :: x.1.2.1.1, x.1.2.1.2)) := by
      have hc₂ : Primrec fun y : (A × ℕ) × ℕ => y.2 := Primrec.snd
      have hp₂1 := primrec_unpair_fst.comp (primrec_sub1.comp hc₂)
      have hp₂2 := primrec_unpair_snd.comp (primrec_sub1.comp hc₂)
      have ha₁ : Primrec fun y : (A × ℕ) × ℕ => (y.1.2 - 1).unpair.2.unpair.1 :=
        (primrec_unpair_fst.comp hp₁2).comp Primrec.fst
      have hb₁ : Primrec fun y : (A × ℕ) × ℕ => (y.1.2 - 1).unpair.2.unpair.2 :=
        (primrec_unpair_snd.comp hp₁2).comp Primrec.fst
      have ha₂ := primrec_unpair_fst.comp hp₂2
      have hb₂ := primrec_unpair_snd.comp hp₂2
      have hA : Primrec fun y : (A × ℕ) × ℕ => y.1.1 := Primrec.fst.comp Primrec.fst
      exact primrec_list_any (hΓ.comp Primrec.fst)
        (primrec_bool_and.comp (Primrec.beq.comp hp₂1 (Primrec.const 1))
          (primrec_listContains (hprev.comp hA)
            ((Primrec.list_cons.comp
              (primrec_mkEqCode.comp (primrec_mkAddCode.comp ha₁ ha₂) (primrec_mkAddCode.comp hb₁ hb₂))
              (hΓ.comp hA)).pair (hΔ.comp hA)))).to₂
    exact primrec_list_any hΓ
      (primrec_bool_and.comp (Primrec.beq.comp hp₁1 (Primrec.const 1)) hinner).to₂
  have hr13 : Primrec fun a : A =>
      a.2.1.1.any (fun c₁ =>
        let p₁ := (c₁ - 1).unpair
        (p₁.1 == 1) &&
        a.2.1.1.any (fun c₂ =>
          let p₂ := (c₂ - 1).unpair
          (p₂.1 == 1) &&
          listContains a.1
            (mkEqCode (mkMulCode p₁.2.unpair.1 p₂.2.unpair.1)
                      (mkMulCode p₁.2.unpair.2 p₂.2.unpair.2) :: a.2.1.1, a.2.1.2))) := by
    have hc₁ : Primrec fun x : A × ℕ => x.2 := Primrec.snd
    have hp₁1 := primrec_unpair_fst.comp (primrec_sub1.comp hc₁)
    have hp₁2 := primrec_unpair_snd.comp (primrec_sub1.comp hc₁)
    have hinner : Primrec fun x : A × ℕ =>
        x.1.2.1.1.any (fun c₂ =>
          let p₂ := (c₂ - 1).unpair
          (p₂.1 == 1) &&
          listContains x.1.1
            (mkEqCode (mkMulCode (x.2 - 1).unpair.2.unpair.1 p₂.2.unpair.1)
                      (mkMulCode (x.2 - 1).unpair.2.unpair.2 p₂.2.unpair.2) :: x.1.2.1.1, x.1.2.1.2)) := by
      have hc₂ : Primrec fun y : (A × ℕ) × ℕ => y.2 := Primrec.snd
      have hp₂1 := primrec_unpair_fst.comp (primrec_sub1.comp hc₂)
      have hp₂2 := primrec_unpair_snd.comp (primrec_sub1.comp hc₂)
      have ha₁ : Primrec fun y : (A × ℕ) × ℕ => (y.1.2 - 1).unpair.2.unpair.1 :=
        (primrec_unpair_fst.comp hp₁2).comp Primrec.fst
      have hb₁ : Primrec fun y : (A × ℕ) × ℕ => (y.1.2 - 1).unpair.2.unpair.2 :=
        (primrec_unpair_snd.comp hp₁2).comp Primrec.fst
      have ha₂ := primrec_unpair_fst.comp hp₂2
      have hb₂ := primrec_unpair_snd.comp hp₂2
      have hA : Primrec fun y : (A × ℕ) × ℕ => y.1.1 := Primrec.fst.comp Primrec.fst
      exact primrec_list_any (hΓ.comp Primrec.fst)
        (primrec_bool_and.comp (Primrec.beq.comp hp₂1 (Primrec.const 1))
          (primrec_listContains (hprev.comp hA)
            ((Primrec.list_cons.comp
              (primrec_mkEqCode.comp (primrec_mkMulCode.comp ha₁ ha₂) (primrec_mkMulCode.comp hb₁ hb₂))
              (hΓ.comp hA)).pair (hΔ.comp hA)))).to₂
    exact primrec_list_any hΓ
      (primrec_bool_and.comp (Primrec.beq.comp hp₁1 (Primrec.const 1)) hinner).to₂
  have hr14 : Primrec fun a : A =>
      a.2.1.1.any (fun c₁ =>
        let p₁ := (c₁ - 1).unpair
        (p₁.1 == 1) &&
        a.2.1.1.any (fun c₂ =>
          let p₂ := (c₂ - 1).unpair
          (p₂.1 == 1) &&
          listContains a.2.1.1 (mkLeCode p₁.2.unpair.1 p₂.2.unpair.1) &&
          listContains a.1 (mkLeCode p₁.2.unpair.2 p₂.2.unpair.2 :: a.2.1.1, a.2.1.2))) := by
    have hc₁ : Primrec fun x : A × ℕ => x.2 := Primrec.snd
    have hp₁1 := primrec_unpair_fst.comp (primrec_sub1.comp hc₁)
    have hp₁2 := primrec_unpair_snd.comp (primrec_sub1.comp hc₁)
    have hinner : Primrec fun x : A × ℕ =>
        x.1.2.1.1.any (fun c₂ =>
          let p₂ := (c₂ - 1).unpair
          (p₂.1 == 1) &&
          listContains x.1.2.1.1 (mkLeCode (x.2 - 1).unpair.2.unpair.1 p₂.2.unpair.1) &&
          listContains x.1.1 (mkLeCode (x.2 - 1).unpair.2.unpair.2 p₂.2.unpair.2 :: x.1.2.1.1, x.1.2.1.2)) := by
      have hc₂ : Primrec fun y : (A × ℕ) × ℕ => y.2 := Primrec.snd
      have hp₂1 := primrec_unpair_fst.comp (primrec_sub1.comp hc₂)
      have hp₂2 := primrec_unpair_snd.comp (primrec_sub1.comp hc₂)
      have ha₁ : Primrec fun y : (A × ℕ) × ℕ => (y.1.2 - 1).unpair.2.unpair.1 :=
        (primrec_unpair_fst.comp hp₁2).comp Primrec.fst
      have hb₁ : Primrec fun y : (A × ℕ) × ℕ => (y.1.2 - 1).unpair.2.unpair.2 :=
        (primrec_unpair_snd.comp hp₁2).comp Primrec.fst
      have ha₂ := primrec_unpair_fst.comp hp₂2
      have hb₂ := primrec_unpair_snd.comp hp₂2
      have hA : Primrec fun y : (A × ℕ) × ℕ => y.1.1 := Primrec.fst.comp Primrec.fst
      exact primrec_list_any (hΓ.comp Primrec.fst)
        (primrec_bool_and.comp
          (primrec_bool_and.comp (Primrec.beq.comp hp₂1 (Primrec.const 1))
            (primrec_listContains (hΓ.comp hA) (primrec_mkLeCode.comp ha₁ ha₂)))
          (primrec_listContains (hprev.comp hA)
            ((Primrec.list_cons.comp (primrec_mkLeCode.comp hb₁ hb₂) (hΓ.comp hA)).pair (hΔ.comp hA)))).to₂
    exact primrec_list_any hΓ
      (primrec_bool_and.comp (Primrec.beq.comp hp₁1 (Primrec.const 1)) hinner).to₂
  have hor :=
    primrec_bool_or.comp (primrec_bool_or.comp (primrec_bool_or.comp
    (primrec_bool_or.comp (primrec_bool_or.comp (primrec_bool_or.comp
    (primrec_bool_or.comp (primrec_bool_or.comp (primrec_bool_or.comp
    (primrec_bool_or.comp (primrec_bool_or.comp (primrec_bool_or.comp
    (primrec_bool_or.comp hr1 hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10) hr11) hr12) hr13) hr14
  exact (primrec_bool_and.comp hwf hor).to₂

lemma primrec_validTrace : Primrec validTrace := by
  let S := Bool × List (List ℕ × List ℕ)
  let stepFn : S → ((List ℕ × List ℕ) × ℕ) → S :=
    fun acc st => (acc.1 && validStep acc.2 st, st.1 :: acc.2)
  have hstep : Primrec₂ stepFn :=
    ((primrec_bool_and.comp (Primrec.fst.comp Primrec.fst)
        (primrec_validStep.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).pair
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))).to₂
  have hfold : Primrec fun tr : List ((List ℕ × List ℕ) × ℕ) =>
      (tr.foldl stepFn (true, [])).1 :=
    Primrec.fst.comp (Primrec.list_foldl Primrec.id (Primrec.const (true, ([] : List (List ℕ × List ℕ))))
      (hstep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)
  refine hfold.of_eq fun tr => ?_
  have key : ∀ (l : List ((List ℕ × List ℕ) × ℕ)) (b : Bool) (prev : List (List ℕ × List ℕ)),
      (l.foldl stepFn (b, prev)).1 = (b && validTraceAux prev l) := by
    intro l
    induction l with
    | nil => intro b prev; simp [validTraceAux]
    | cons st rest ih =>
      intro b prev
      simp only [List.foldl_cons, stepFn, ih, validTraceAux, Bool.and_assoc]
  simpa [validTrace] using key tr true []

end PrimrecHelpers

/- ## Section 5: Effective proof search and main theorem -/

lemma computable_list_all_nat {p : ℕ → Bool} (hp : Computable p) :
    Computable (fun l : List ℕ => l.all p) := by
  let g : List ℕ → ℕ → Bool := fun l i => decide (l.length ≤ i) || !(p (l.getD i 0))
  have hg : Computable₂ g := by
    have hle : Primrec₂ (fun (l : List ℕ) (i : ℕ) => decide (l.length ≤ i)) :=
      ((PrimrecRel.decide Primrec.nat_le).comp
        (Primrec.list_length.comp Primrec.fst) Primrec.snd).to₂
    have hget : Primrec₂ (fun (l : List ℕ) (i : ℕ) => l.getD i 0) :=
      ((Primrec.list_getD 0).comp Primrec.fst Primrec.snd).to₂
    exact (primrec_bool_or.to_comp.comp hle.to_comp
      (primrec_bool_not.to_comp.comp (hp.comp hget.to_comp))).to₂
  have hr : Partrec (fun l : List ℕ => Nat.rfind (fun i => Part.some (g l i))) :=
    Partrec.rfind hg.partrec
  have hle_p : Primrec₂ (fun (l : List ℕ) (i : ℕ) => decide (l.length ≤ i)) :=
    ((PrimrecRel.decide Primrec.nat_le).comp
      (Primrec.list_length.comp Primrec.fst) Primrec.snd).to₂
  have hmap : Partrec (fun l : List ℕ =>
      (Nat.rfind (fun i => Part.some (g l i))).bind (fun i => Part.some (decide (l.length ≤ i)))) :=
    Partrec.bind hr hle_p.to_comp.partrec.to₂
  refine hmap.of_eq fun l => ?_
  have hdom : (Nat.rfind (fun i => Part.some (g l i))).Dom := by
    rw [Nat.rfind_dom (p := (fun i => Part.some (g l i) : ℕ →. Bool))]
    refine ⟨l.length, ?_, fun _ => Part.some_dom _⟩
    simp [g]
  obtain ⟨k, hk⟩ := Part.dom_iff_mem.mp hdom
  rw [Part.eq_some_iff.mpr hk, Part.bind_some]
  congr 1
  have hk_spec : g l k = true := by simpa using Nat.rfind_spec hk
  have hk_min : ∀ j < k, g l j = false := fun j hj => by
    have := Nat.rfind_min hk hj
    simpa using this
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, List.all_eq_true]
  constructor
  · intro hle x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    have hjk : j < k := lt_of_lt_of_le hj hle
    have hgj := hk_min j hjk
    simp only [g, Bool.or_eq_false_iff, Bool.not_eq_false'] at hgj
    rw [List.getD_eq_getElem _ _ hj] at hgj; exact hgj.2
  · intro hall
    by_contra hlt
    push_neg at hlt
    have hgk : g l k = false := by
      simp only [g, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le, Bool.not_eq_false']
      refine ⟨hlt, ?_⟩
      rw [List.getD_eq_getElem _ _ hlt]
      exact hall _ (List.getElem_mem hlt)
    rw [hgk] at hk_spec
    exact Bool.false_ne_true hk_spec

def checkWitnessStatic (b : Bool) (n m : ℕ) : Bool :=
  let φc := m.unpair.1
  let Γcode := m.unpair.2.unpair.1
  let trCode := m.unpair.2.unpair.2
  let target := if b then φc else mkImpCode φc mkBotCode
  match decode (α := List ℕ) Γcode, decode (α := List ((List ℕ × List ℕ) × ℕ)) trCode with
  | some Γc, some tr =>
    (encodeIfBounded φc == some n) && validTrace tr && listContains (tr.map Prod.fst) (Γc, [target])
  | _, _ => false

def checkWitnessOracle (f : ℕ → Bool) (m : ℕ) : Bool :=
  match decode (α := List ℕ) m.unpair.2.unpair.1 with
  | none => false
  | some Γc => Γc.all (fun c => match encodeIfBounded c with | none => false | some code => f code)

def checkWitness (f : ℕ → Bool) (b : Bool) (n m : ℕ) : Bool :=
  checkWitnessStatic b n m && checkWitnessOracle f m

lemma primrec_encEq : Primrec₂ (fun (n φc : ℕ) => encodeIfBounded φc == some n) := by
  letI : DecidableEq (Option ℕ) := inferInstance
  have h : Primrec (fun p : ℕ × ℕ => encodeIfBounded p.2 == some p.1) := by
    refine ((@Primrec.beq (Option ℕ) _ this).comp
      (primrec_encodeIfBounded.comp Primrec.snd) (Primrec.option_some.comp Primrec.fst)).of_eq fun p => ?_
    rw [Bool.eq_iff_iff]
    simp [beq_iff_eq]
  exact h.to₂

lemma primrec_traceMem :
    Primrec (fun p : (List ((List ℕ × List ℕ) × ℕ) × List ℕ) × ℕ =>
      listContains (p.1.1.map Prod.fst) (p.1.2, [p.2])) := by
  have hmap : Primrec fun tr : List ((List ℕ × List ℕ) × ℕ) => tr.map Prod.fst :=
    Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd).to₂
  exact primrec_listContains (hmap.comp (Primrec.fst.comp Primrec.fst))
    ((Primrec.snd.comp Primrec.fst).pair (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))

lemma primrec_checkWitnessStatic (b : Bool) : Primrec₂ (checkWitnessStatic b) := by
  have hφ : Primrec fun p : ℕ × ℕ => p.2.unpair.1 :=
    primrec_unpair_fst.comp Primrec.snd
  have hΓc : Primrec fun p : ℕ × ℕ => decode (α := List ℕ) p.2.unpair.2.unpair.1 :=
    Primrec.decode.comp (primrec_unpair_fst.comp (primrec_unpair_snd.comp Primrec.snd))
  have htrc : Primrec fun p : ℕ × ℕ => decode (α := List ((List ℕ × List ℕ) × ℕ)) p.2.unpair.2.unpair.2 :=
    Primrec.decode.comp (primrec_unpair_snd.comp (primrec_unpair_snd.comp Primrec.snd))
  have htarg : Primrec fun p : ℕ × ℕ => if b then p.2.unpair.1 else mkImpCode p.2.unpair.1 mkBotCode := by
    cases b
    · simpa using primrec_mkImpCode.comp hφ (Primrec.const mkBotCode)
    · simpa using hφ
  have hinner : Primrec₂ (fun (q : (ℕ × ℕ) × List ℕ) (tr : List ((List ℕ × List ℕ) × ℕ)) =>
      (encodeIfBounded q.1.2.unpair.1 == some q.1.1) &&
      validTrace tr &&
      listContains (tr.map Prod.fst) (q.2, [if b then q.1.2.unpair.1 else mkImpCode q.1.2.unpair.1 mkBotCode])) := by
    have hq1 : Primrec fun x : ((ℕ × ℕ) × List ℕ) × List ((List ℕ × List ℕ) × ℕ) => x.1.1 :=
      Primrec.fst.comp Primrec.fst
    have hΓ : Primrec fun x : ((ℕ × ℕ) × List ℕ) × List ((List ℕ × List ℕ) × ℕ) => x.1.2 :=
      Primrec.snd.comp Primrec.fst
    have htr : Primrec fun x : ((ℕ × ℕ) × List ℕ) × List ((List ℕ × List ℕ) × ℕ) => x.2 :=
      Primrec.snd
    have h1 := primrec_encEq.comp (Primrec.fst.comp hq1) (hφ.comp hq1)
    have h2 := primrec_validTrace.comp htr
    have h3 := primrec_traceMem.comp ((htr.pair hΓ).pair (htarg.comp hq1))
    exact (primrec_bool_and.comp (primrec_bool_and.comp h1 h2) h3).to₂
  have hmid := (Primrec.option_casesOn (htrc.comp Primrec.fst) (Primrec.const false) hinner).to₂
  have hout := Primrec.option_casesOn hΓc (Primrec.const false) hmid
  refine hout.to₂.of_eq fun n m => ?_
  unfold checkWitnessStatic
  dsimp only
  cases decode (α := List ℕ) m.unpair.2.unpair.1 <;>
    cases decode (α := List ((List ℕ × List ℕ) × ℕ)) m.unpair.2.unpair.2 <;> rfl

lemma computable_checkWitnessOracle {f : ℕ → Bool} (hf : Computable f) :
    Computable (checkWitnessOracle f) := by
  have hax : Computable fun c : ℕ =>
      match encodeIfBounded c with
      | none => false
      | some code => f code := by
    have h1 := Computable.option_casesOn (primrec_encodeIfBounded.to_comp)
      (Computable.const false) (hf.comp Computable.snd).to₂
    refine h1.of_eq fun c => ?_
    cases encodeIfBounded c <;> rfl
  have hall : Computable fun l : List ℕ =>
      l.all (fun c => match encodeIfBounded c with | none => false | some code => f code) :=
    computable_list_all_nat hax
  have hdec : Computable fun m : ℕ => decode (α := List ℕ) m.unpair.2.unpair.1 :=
    (Primrec.decode.comp (primrec_unpair_fst.comp (primrec_unpair_snd.comp Primrec.id))).to_comp
  have hcomp := Computable.option_casesOn hdec (Computable.const false) (hall.comp Computable.snd).to₂
  refine hcomp.of_eq fun m => ?_
  unfold checkWitnessOracle
  cases decode (α := List ℕ) m.unpair.2.unpair.1 <;> rfl

lemma computable_checkWitness {f : ℕ → Bool} (hf : Computable f) (b : Bool) :
    Computable₂ (checkWitness f b) :=
  (primrec_bool_and.to_comp.comp
    (primrec_checkWitnessStatic b).to_comp
    ((computable_checkWitnessOracle hf).comp Computable.snd)).to₂

lemma exists_checkWitness_iff {T : L.Theory} {f : ℕ → Bool}
    (hfT : ∀ φ : L.Sentence, f (encode φ) = true ↔ φ ∈ T) (b : Bool) (n : ℕ) :
    (∃ m : ℕ, checkWitness f b n m = true) ↔
      ∃ φ : L.Sentence, encode φ = n ∧ T ⊨ᵇ (if b then φ else φ.not) := by
  constructor
  · rintro ⟨m, hm⟩
    unfold checkWitness checkWitnessStatic checkWitnessOracle at hm
    simp only [Bool.and_eq_true] at hm
    rcases hm with ⟨hstat, hor⟩
    cases hΓd : decode (α := List ℕ) m.unpair.2.unpair.1 with
    | none => rw [hΓd] at hor; simp at hor
    | some Γc =>
      cases htrd : decode (α := List ((List ℕ × List ℕ) × ℕ)) m.unpair.2.unpair.2 with
      | none => rw [hΓd, htrd] at hstat; simp at hstat
      | some tr =>
        rw [hΓd, htrd] at hstat
        rw [hΓd] at hor
        simp only [Bool.and_eq_true, beq_iff_eq, listContains_iff] at hstat
        obtain ⟨⟨hφenc, htr⟩, hmem⟩ := hstat
        set φc := m.unpair.1
        obtain ⟨φo, hφc_eq, hφbd, hφcode⟩ := (encodeIfBounded_eq_some_iff φc n).mp hφenc
        let φ : L.Sentence := toBF φo hφbd
        have hφeq : encode φ = n := (toSent_encode_eq φo hφbd).trans hφcode
        have hΓex : ∃ Γ : List L.Sentence, (∀ ψ ∈ Γ, ψ ∈ T) ∧ Γ.map (fun ψ => encF (fromBF ψ)) = Γc := by
          clear hΓd htrd hmem htr hφenc hφc_eq hφcode hφbd φo φ hφeq φc
          induction Γc with
          | nil => exact ⟨[], fun _ h => by simp at h, rfl⟩
          | cons c rest ih =>
            simp only [List.all_cons, Bool.and_eq_true] at hor
            obtain ⟨Γ', hΓ'T, hΓ'eq⟩ := ih hor.2
            cases he : encodeIfBounded c with
            | none => simp [he] at hor
            | some code =>
              simp only [he] at hor
              obtain ⟨ψo, rfl, hψbd, hψcode⟩ := (encodeIfBounded_eq_some_iff c code).mp he
              let ψ : L.Sentence := toBF ψo hψbd
              have hψT : ψ ∈ T := by
                rw [← hfT ψ, toSent_encode_eq ψo hψbd, hψcode]
                exact hor.1
              refine ⟨ψ :: Γ', fun χ hχ => ?_, ?_⟩
              · rcases List.mem_cons.mp hχ with rfl | hχ'
                · exact hψT
                · exact hΓ'T χ hχ'
              · simp [ψ, fromBF_toBF, hΓ'eq]
        obtain ⟨Γ, hΓT, rfl⟩ := hΓex
        refine ⟨φ, hφeq, ?_⟩
        rw [models_iff_exists_seqProv]
        refine ⟨Γ, hΓT, ?_⟩
        have htarget :
            (if b then φc else mkImpCode φc mkBotCode) =
              encF (fromBF (if b then φ else φ.not)) := by
          rw [← hφc_eq]
          cases b
          · simp [φ, Formula.not, BoundedFormula.not, fromBF, fromBF_toBF, mkImpCode, mkBotCode, encF]
          · simp [φ, fromBF_toBF]
        rw [htarget] at hmem
        exact validTrace_sound htr _ hmem (Γ.map fromBF) [fromBF (if b then φ else φ.not)]
          (by simp [List.map_map])
  · rintro ⟨φ, rfl, hmod⟩
    rw [models_iff_exists_seqProv] at hmod
    obtain ⟨Γ, hΓT, hprov⟩ := hmod
    obtain ⟨tr, htr, hmem⟩ := seqProv_to_trace hprov
    let m : ℕ := Nat.pair (encF (fromBF φ)) (Nat.pair (encode ((Γ.map fromBF).map encF)) (encode tr))
    refine ⟨m, ?_⟩
    unfold checkWitness checkWitnessStatic checkWitnessOracle
    simp only [m, Nat.unpair_pair, encodek, Bool.and_eq_true, beq_iff_eq, listContains_iff]
    refine ⟨⟨⟨?_, htr⟩, ?_⟩, ?_⟩
    · rw [encodeIfBounded_encF (fromBF φ) (fromBF_isBounded φ), ← sentence_encode_eq φ]
    · have htarget :
          (if b then encF (fromBF φ) else mkImpCode (encF (fromBF φ)) mkBotCode) =
            encF (fromBF (if b then φ else φ.not)) := by
        cases b
        · simp [Formula.not, BoundedFormula.not, fromBF, mkImpCode, mkBotCode, encF]
        · rfl
      rw [htarget]
      simpa using hmem
    · rw [List.all_eq_true]
      intro c hc
      obtain ⟨ψo, hψo, rfl⟩ := List.mem_map.mp hc
      obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hψo
      rw [encodeIfBounded_encF (fromBF ψ) (fromBF_isBounded ψ), ← sentence_encode_eq ψ]
      exact (hfT ψ).mpr (hΓT ψ hψ)

end OMA.TarskiH3

open FirstOrder OMA.TarskiH3 in
theorem OMA.solution :
    OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_realExp_of_realSchanuelConjecture_R1.H3 := by
  intro T hT b
  obtain ⟨f, hf, hfT⟩ := hT
  have hcheck : Computable₂ (checkWitness f b) := computable_checkWitness hf b
  have hrfind : Partrec (fun n : ℕ => Nat.rfind (fun m => Part.some (checkWitness f b n m))) :=
    Partrec.rfind hcheck.partrec
  refine hrfind.dom_re.of_eq fun n => ?_
  rw [Nat.rfind_dom (p := (fun m => Part.some (checkWitness f b n m) : ℕ →. Bool))]
  simp only [Part.some_dom, forall_const, Part.mem_some_iff]
  refine (Iff.intro ?_ ?_).trans (exists_checkWitness_iff hfT b n)
  · rintro ⟨m, hm, -⟩; exact ⟨m, hm.symm⟩
  · rintro ⟨m, hm⟩; exact ⟨m, hm.symm, fun _ => trivial⟩
