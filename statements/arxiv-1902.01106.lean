import Mathlib

namespace OMA.S_arxiv_1902_01106

/-- Formulas of modal logic S4 (Full G3s language). -/
inductive S4Form where
  | bot : S4Form
  | atom : ℕ → S4Form
  | neg : S4Form → S4Form
  | conj : S4Form → S4Form → S4Form
  | disj : S4Form → S4Form → S4Form
  | imp : S4Form → S4Form → S4Form
  | box : S4Form → S4Form
  | dia : S4Form → S4Form
  deriving DecidableEq

/-- Annotated S4 formulas where every `□` carries a family label `i : ι`. -/
inductive AnnS4Form (ι : Type) where
  | bot : AnnS4Form ι
  | atom : ℕ → AnnS4Form ι
  | neg : AnnS4Form ι → AnnS4Form ι
  | conj : AnnS4Form ι → AnnS4Form ι → AnnS4Form ι
  | disj : AnnS4Form ι → AnnS4Form ι → AnnS4Form ι
  | imp : AnnS4Form ι → AnnS4Form ι → AnnS4Form ι
  | box : ι → AnnS4Form ι → AnnS4Form ι
  | dia : AnnS4Form ι → AnnS4Form ι

/-- Erase family annotations from an annotated S4 formula. -/
def AnnS4Form.erase {ι : Type} : AnnS4Form ι → S4Form
  | .bot => .bot
  | .atom p => .atom p
  | .neg A => .neg A.erase
  | .conj A B => .conj A.erase B.erase
  | .disj A B => .disj A.erase B.erase
  | .imp A B => .imp A.erase B.erase
  | .box _ A => .box A.erase
  | .dia A => .dia A.erase

/-- Whether a family label `h : ι` occurs on a `□` inside an annotated S4 formula. -/
def AnnS4Form.hasBoxLabel {ι : Type} (h : ι) : AnnS4Form ι → Prop
  | .bot => False
  | .atom _ => False
  | .neg A => A.hasBoxLabel h
  | .conj A B => A.hasBoxLabel h ∨ B.hasBoxLabel h
  | .disj A B => A.hasBoxLabel h ∨ B.hasBoxLabel h
  | .imp A B => A.hasBoxLabel h ∨ B.hasBoxLabel h
  | .box i A => i = h ∨ A.hasBoxLabel h
  | .dia A => A.hasBoxLabel h

/-- Full Gentzen sequent calculus G3s for S4 (Troelstra–Schwichtenberg / Gass–Studer, Fig. 1). -/
inductive G3s : Multiset S4Form → Multiset S4Form → Type where
  | ax (p : ℕ) (Γ Δ : Multiset S4Form) :
      G3s (.atom p ::ₘ Γ) (.atom p ::ₘ Δ)
  | botL (Γ Δ : Multiset S4Form) :
      G3s (.bot ::ₘ Γ) Δ
  | negL {A : S4Form} {Γ Δ : Multiset S4Form} :
      G3s Γ (A ::ₘ Δ) → G3s (.neg A ::ₘ Γ) Δ
  | negR {A : S4Form} {Γ Δ : Multiset S4Form} :
      G3s (A ::ₘ Γ) Δ → G3s Γ (.neg A ::ₘ Δ)
  | conjL {A B : S4Form} {Γ Δ : Multiset S4Form} :
      G3s (A ::ₘ B ::ₘ Γ) Δ → G3s (.conj A B ::ₘ Γ) Δ
  | conjR {A B : S4Form} {Γ Δ : Multiset S4Form} :
      G3s Γ (A ::ₘ Δ) → G3s Γ (B ::ₘ Δ) → G3s Γ (.conj A B ::ₘ Δ)
  | disjL {A B : S4Form} {Γ Δ : Multiset S4Form} :
      G3s (A ::ₘ Γ) Δ → G3s (B ::ₘ Γ) Δ → G3s (.disj A B ::ₘ Γ) Δ
  | disjR {A B : S4Form} {Γ Δ : Multiset S4Form} :
      G3s Γ (A ::ₘ B ::ₘ Δ) → G3s Γ (.disj A B ::ₘ Δ)
  | impL {A B : S4Form} {Γ Δ : Multiset S4Form} :
      G3s Γ (A ::ₘ Δ) → G3s (B ::ₘ Γ) Δ → G3s (.imp A B ::ₘ Γ) Δ
  | impR {A B : S4Form} {Γ Δ : Multiset S4Form} :
      G3s (A ::ₘ Γ) (B ::ₘ Δ) → G3s Γ (.imp A B ::ₘ Δ)
  | boxL {A : S4Form} {Γ Δ : Multiset S4Form} :
      G3s (A ::ₘ .box A ::ₘ Γ) Δ → G3s (.box A ::ₘ Γ) Δ
  | boxR {A : S4Form} {Γ Γ' Δ Δ' : Multiset S4Form} :
      G3s (Γ.map .box) (A ::ₘ Δ.map .dia) →
      G3s (Γ' + Γ.map .box) (.box A ::ₘ (Δ.map .dia + Δ'))
  | diaL {A : S4Form} {Γ Γ' Δ Δ' : Multiset S4Form} :
      G3s (A ::ₘ Γ.map .box) (Δ.map .dia) →
      G3s (.dia A ::ₘ (Γ' + Γ.map .box)) (Δ.map .dia + Δ')
  | diaR {A : S4Form} {Γ Δ : Multiset S4Form} :
      G3s Γ (A ::ₘ .dia A ::ₘ Δ) → G3s Γ (.dia A ::ₘ Δ)

/-- Annotated G3s derivations tracking `□`-family correspondence throughout the proof tree. -/
inductive AnnG3s {ι : Type} : Multiset (AnnS4Form ι) → Multiset (AnnS4Form ι) → Type where
  | ax (p : ℕ) (Γ Δ : Multiset (AnnS4Form ι)) :
      AnnG3s (.atom p ::ₘ Γ) (.atom p ::ₘ Δ)
  | botL (Γ Δ : Multiset (AnnS4Form ι)) :
      AnnG3s (.bot ::ₘ Γ) Δ
  | negL {A : AnnS4Form ι} {Γ Δ : Multiset (AnnS4Form ι)} :
      AnnG3s Γ (A ::ₘ Δ) → AnnG3s (.neg A ::ₘ Γ) Δ
  | negR {A : AnnS4Form ι} {Γ Δ : Multiset (AnnS4Form ι)} :
      AnnG3s (A ::ₘ Γ) Δ → AnnG3s Γ (.neg A ::ₘ Δ)
  | conjL {A B : AnnS4Form ι} {Γ Δ : Multiset (AnnS4Form ι)} :
      AnnG3s (A ::ₘ B ::ₘ Γ) Δ → AnnG3s (.conj A B ::ₘ Γ) Δ
  | conjR {A B : AnnS4Form ι} {Γ Δ : Multiset (AnnS4Form ι)} :
      AnnG3s Γ (A ::ₘ Δ) → AnnG3s Γ (B ::ₘ Δ) → AnnG3s Γ (.conj A B ::ₘ Δ)
  | disjL {A B : AnnS4Form ι} {Γ Δ : Multiset (AnnS4Form ι)} :
      AnnG3s (A ::ₘ Γ) Δ → AnnG3s (B ::ₘ Γ) Δ → AnnG3s (.disj A B ::ₘ Γ) Δ
  | disjR {A B : AnnS4Form ι} {Γ Δ : Multiset (AnnS4Form ι)} :
      AnnG3s Γ (A ::ₘ B ::ₘ Δ) → AnnG3s Γ (.disj A B ::ₘ Δ)
  | impL {A B : AnnS4Form ι} {Γ Δ : Multiset (AnnS4Form ι)} :
      AnnG3s Γ (A ::ₘ Δ) → AnnG3s (B ::ₘ Γ) Δ → AnnG3s (.imp A B ::ₘ Γ) Δ
  | impR {A B : AnnS4Form ι} {Γ Δ : Multiset (AnnS4Form ι)} :
      AnnG3s (A ::ₘ Γ) (B ::ₘ Δ) → AnnG3s Γ (.imp A B ::ₘ Δ)
  | boxL {i : ι} {A : AnnS4Form ι} {Γ Δ : Multiset (AnnS4Form ι)} :
      AnnG3s (A ::ₘ .box i A ::ₘ Γ) Δ → AnnG3s (.box i A ::ₘ Γ) Δ
  | boxR {i : ι} {A : AnnS4Form ι} {Γ : Multiset (ι × AnnS4Form ι)}
      {Γ' Δ Δ' : Multiset (AnnS4Form ι)} :
      AnnG3s (Γ.map fun p => .box p.1 p.2) (A ::ₘ Δ.map .dia) →
      AnnG3s (Γ' + Γ.map fun p => .box p.1 p.2) (.box i A ::ₘ (Δ.map .dia + Δ'))
  | diaL {A : AnnS4Form ι} {Γ : Multiset (ι × AnnS4Form ι)}
      {Γ' Δ Δ' : Multiset (AnnS4Form ι)} :
      AnnG3s (A ::ₘ Γ.map fun p => .box p.1 p.2) (Δ.map .dia) →
      AnnG3s (.dia A ::ₘ (Γ' + Γ.map fun p => .box p.1 p.2)) (Δ.map .dia + Δ')
  | diaR {A : AnnS4Form ι} {Γ Δ : Multiset (AnnS4Form ι)} :
      AnnG3s Γ (A ::ₘ .dia A ::ₘ Δ) → AnnG3s Γ (.dia A ::ₘ Δ)

/-- Left prehistoric relation `h ≺_L i` in an annotated G3s proof (Yu 2010 / Gass–Studer Def. 11):
there is a `(⊃ □)` rule introducing `□_i A` whose premise contains an occurrence of `□_h` on the left. -/
def LeftPrehist {ι : Type} : {Γ Δ : Multiset (AnnS4Form ι)} → AnnG3s Γ Δ → ι → ι → Prop
  | _, _, .ax _ _ _, _, _ => False
  | _, _, .botL _ _, _, _ => False
  | _, _, .negL d, h, i => LeftPrehist d h i
  | _, _, .negR d, h, i => LeftPrehist d h i
  | _, _, .conjL d, h, i => LeftPrehist d h i
  | _, _, .conjR d₁ d₂, h, i => LeftPrehist d₁ h i ∨ LeftPrehist d₂ h i
  | _, _, .disjL d₁ d₂, h, i => LeftPrehist d₁ h i ∨ LeftPrehist d₂ h i
  | _, _, .disjR d, h, i => LeftPrehist d h i
  | _, _, .impL d₁ d₂, h, i => LeftPrehist d₁ h i ∨ LeftPrehist d₂ h i
  | _, _, .impR d, h, i => LeftPrehist d h i
  | _, _, .boxL d, h, i => LeftPrehist d h i
  | _, _, @AnnG3s.boxR _ j _ Γ _ _ _ d, h, i =>
      (j = i ∧ ∃ F ∈ Γ.map (fun p => AnnS4Form.box p.1 p.2), F.hasBoxLabel h) ∨ LeftPrehist d h i
  | _, _, .diaL d, h, i => LeftPrehist d h i
  | _, _, .diaR d, h, i => LeftPrehist d h i

/-- Right prehistoric relation `h ≺_R i` in an annotated G3s proof. -/
def RightPrehist {ι : Type} : {Γ Δ : Multiset (AnnS4Form ι)} → AnnG3s Γ Δ → ι → ι → Prop
  | _, _, .ax _ _ _, _, _ => False
  | _, _, .botL _ _, _, _ => False
  | _, _, .negL d, h, i => RightPrehist d h i
  | _, _, .negR d, h, i => RightPrehist d h i
  | _, _, .conjL d, h, i => RightPrehist d h i
  | _, _, .conjR d₁ d₂, h, i => RightPrehist d₁ h i ∨ RightPrehist d₂ h i
  | _, _, .disjL d₁ d₂, h, i => RightPrehist d₁ h i ∨ RightPrehist d₂ h i
  | _, _, .disjR d, h, i => RightPrehist d h i
  | _, _, .impL d₁ d₂, h, i => RightPrehist d₁ h i ∨ RightPrehist d₂ h i
  | _, _, .impR d, h, i => RightPrehist d h i
  | _, _, .boxL d, h, i => RightPrehist d h i
  | _, _, @AnnG3s.boxR _ j A _ _ Δ _ d, h, i =>
      (j = i ∧ ∃ F ∈ A ::ₘ Δ.map AnnS4Form.dia, F.hasBoxLabel h) ∨ RightPrehist d h i
  | _, _, .diaL d, h, i => RightPrehist d h i
  | _, _, .diaR d, h, i => RightPrehist d h i

/-- Prehistoric relation `≺ := ≺_L ∪ ≺_R`. -/
def Prehist {ι : Type} {Γ Δ : Multiset (AnnS4Form ι)} (T : AnnG3s Γ Δ) (h i : ι) : Prop :=
  LeftPrehist T h i ∨ RightPrehist T h i

/-- A proof `T` has a left prehistoric cycle if `≺_L⁺` has a cycle `i ≺_L⁺ i`. -/
def HasLeftPrehistCycle {ι : Type} {Γ Δ : Multiset (AnnS4Form ι)} (T : AnnG3s Γ Δ) : Prop :=
  ∃ i : ι, Relation.TransGen (LeftPrehist T) i i

/-- A proof `T` has a prehistoric cycle if `≺⁺` has a cycle `i ≺⁺ i`. -/
def HasPrehistCycle {ι : Type} {Γ Δ : Multiset (AnnS4Form ι)} (T : AnnG3s Γ Δ) : Prop :=
  ∃ i : ι, Relation.TransGen (Prehist T) i i

/-- Justification terms of the Logic of Proofs LP. -/
inductive LPTerm where
  | const : ℕ → LPTerm
  | var : ℕ → LPTerm
  | app : LPTerm → LPTerm → LPTerm
  | sum : LPTerm → LPTerm → LPTerm
  | bang : LPTerm → LPTerm
  deriving DecidableEq

/-- Formulas of the Logic of Proofs LP. -/
inductive LPForm where
  | bot : LPForm
  | atom : ℕ → LPForm
  | neg : LPForm → LPForm
  | conj : LPForm → LPForm → LPForm
  | disj : LPForm → LPForm → LPForm
  | imp : LPForm → LPForm → LPForm
  | just : LPTerm → LPForm → LPForm
  deriving DecidableEq

/-- Forgetful projection `B°` from LP formulas to S4 formulas. -/
def LPForm.forget : LPForm → S4Form
  | .bot => .bot
  | .atom p => .atom p
  | .neg A => .neg A.forget
  | .conj A B => .conj A.forget B.forget
  | .disj A B => .disj A.forget B.forget
  | .imp A B => .imp A.forget B.forget
  | .just _ A => .box A.forget

/-- Boolean evaluation of an LP formula treating atomic and `t:F` formulas as propositional atoms. -/
def LPForm.propEval (valAtom : ℕ → Bool) (valJust : LPTerm → LPForm → Bool) : LPForm → Bool
  | .bot => false
  | .atom p => valAtom p
  | .neg A => !(A.propEval valAtom valJust)
  | .conj A B => A.propEval valAtom valJust && B.propEval valAtom valJust
  | .disj A B => A.propEval valAtom valJust || B.propEval valAtom valJust
  | .imp A B => !(A.propEval valAtom valJust) || B.propEval valAtom valJust
  | .just t A => valJust t A

/-- Classical propositional tautology schema (A0 of LP). -/
def IsPropTaut (A : LPForm) : Prop :=
  ∀ (valAtom : ℕ → Bool) (valJust : LPTerm → LPForm → Bool), A.propEval valAtom valJust = true

/-- Axiom schemes A0–A4 of LP. -/
inductive IsLPAxiom : LPForm → Prop where
  | a0 {A : LPForm} : IsPropTaut A → IsLPAxiom A
  | a1 (t : LPTerm) (F : LPForm) : IsLPAxiom (.imp (.just t F) F)
  | a2 (s t : LPTerm) (F G : LPForm) :
      IsLPAxiom (.imp (.just s (.imp F G)) (.imp (.just t F) (.just (.app s t) G)))
  | a3 (t : LPTerm) (F : LPForm) :
      IsLPAxiom (.imp (.just t F) (.just (.bang t) (.just t F)))
  | a4l (s t : LPTerm) (F : LPForm) :
      IsLPAxiom (.imp (.just s F) (.just (.sum s t) F))
  | a4r (s t : LPTerm) (F : LPForm) :
      IsLPAxiom (.imp (.just t F) (.just (.sum s t) F))

/-- Whether justification constant `c` occurs in term `t`. -/
def LPTerm.hasConst (c : ℕ) : LPTerm → Prop
  | .const c' => c' = c
  | .var _ => False
  | .app s t => s.hasConst c ∨ t.hasConst c
  | .sum s t => s.hasConst c ∨ t.hasConst c
  | .bang t => t.hasConst c

/-- Whether justification constant `c` occurs in LP formula `F`. -/
def LPForm.hasConst (c : ℕ) : LPForm → Prop
  | .bot => False
  | .atom _ => False
  | .neg A => A.hasConst c
  | .conj A B => A.hasConst c ∨ B.hasConst c
  | .disj A B => A.hasConst c ∨ B.hasConst c
  | .imp A B => A.hasConst c ∨ B.hasConst c
  | .just t A => t.hasConst c ∨ A.hasConst c

/-- A constant specification `CS` is self-referential if there is a finite cycle
`c₀ : A₀(c₁), ..., c_{n-1} : A_{n-1}(c₀)` in `CS`. -/
def IsSelfRefCS (CS : Set (ℕ × LPForm)) : Prop :=
  ∃ c : ℕ, Relation.TransGen (fun c₁ c₂ => ∃ F : LPForm, (c₁, F) ∈ CS ∧ F.hasConst c₂) c c

/-- Hilbert-style provability in `LP(CS)`. -/
inductive LPProv (CS : Set (ℕ × LPForm)) : LPForm → Prop where
  | ax {A : LPForm} : IsLPAxiom A → LPProv CS A
  | mp {F G : LPForm} : LPProv CS (.imp F G) → LPProv CS F → LPProv CS G
  | nec {c : ℕ} {A : LPForm} : (c, A) ∈ CS → IsLPAxiom A → LPProv CS (.just (.const c) A)

/-- Main theorem (Gass–Studer, *Self-referentiality in Justification Logic*, Section 4.3):
prehistoric cycles in G3s are NOT a sufficient condition for needing a self-referential
constant specification. There exists an S4 theorem `A` and an LP realization `B` of `A`
provable in `LP(CS)` for a non-self-referential constant specification `CS` (in fact `CS = ∅`,
i.e. `LP₀`), such that every annotated G3s proof of `A` contains a left prehistoric cycle. -/
theorem main :
    ∃ (A : S4Form) (B : LPForm) (CS : Set (ℕ × LPForm)),
      Nonempty (G3s 0 {A}) ∧
      B.forget = A ∧
      ¬ IsSelfRefCS CS ∧
      LPProv CS B ∧
      ∀ {ι : Type} (A_ann : AnnS4Form ι),
        A_ann.erase = A →
        ∀ (T : AnnG3s 0 {A_ann}), HasLeftPrehistCycle T ∧ HasPrehistCycle T := by
  sorry

end OMA.S_arxiv_1902_01106
