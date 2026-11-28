import OMAReductions.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_real_orderedField_R1
import Mathlib.Computability.RE

/-!
# Proof of `TarskiExponentialFunctionProblem.isDecidable_completeTheory_real_orderedField.R1.H2`

Every complete recursive theory in the language of ordered rings
`L = Language.ring.sum Language.order` is decidable.

Architecture:
1. Non-dependent de Bruijn-level AST (`OTerm`, `OForm`) with canonical `Nat.pair` encoding,
   semantic equivalence to Mathlib's `FirstOrder.Language.Sentence`, and exact Gödel-number
   agreement with `Encodable.encode`.
2. Cut-free 13-rule two-sided sequent calculus `Deriv Γ Δ`, proved sound and complete via a
   fair Hintikka saturation tree and quotient term model, combined with Mathlib's compactness
   theorem (`Theory.models_iff_finset_models`).
3. `Primcodable` instances on `OTerm` and `OForm`, a primitive recursive linearized sequent
   proof verifier `checkDeriv`, a primitive recursive sentence decoder from Mathlib's Gödel
   numbering, and unbounded search (`Computable.find`) deciding `T ⊨ᵇ φ` vs `T ⊨ᵇ φ.not`.

Credit: @Rickxscz
-/

namespace OMA.P_TarskiR1H2

open FirstOrder FirstOrder.Language

abbrev LO : Language := Language.ring.sum Language.order

/- ### 1. Non-dependent syntax (`OTerm`, `OForm`) and canonical encoding -/

inductive OTerm : Type
  | fvar (c : ℕ)
  | bvar (k : ℕ)
  | zero
  | one
  | neg (t : OTerm)
  | add (t₁ t₂ : OTerm)
  | mul (t₁ t₂ : OTerm)
  deriving DecidableEq

inductive OForm : Type
  | bot
  | eq (t₁ t₂ : OTerm)
  | le (t₁ t₂ : OTerm)
  | imp (φ ψ : OForm)
  | all (φ : OForm)
  deriving DecidableEq

def encOTerm : OTerm → ℕ
  | .fvar c => Nat.pair 0 c + 1
  | .bvar k => Nat.pair 1 k + 1
  | .zero => Nat.pair 2 0 + 1
  | .one => Nat.pair 3 0 + 1
  | .neg t => Nat.pair 4 (encOTerm t) + 1
  | .add t₁ t₂ => Nat.pair 5 (Nat.pair (encOTerm t₁) (encOTerm t₂)) + 1
  | .mul t₁ t₂ => Nat.pair 6 (Nat.pair (encOTerm t₁) (encOTerm t₂)) + 1

def decOTerm : ℕ → Option OTerm
  | 0 => none
  | n + 1 =>
    match (Nat.unpair n).1 with
    | 0 => some (.fvar (Nat.unpair n).2)
    | 1 => some (.bvar (Nat.unpair n).2)
    | 2 => if (Nat.unpair n).2 = 0 then some .zero else none
    | 3 => if (Nat.unpair n).2 = 0 then some .one else none
    | 4 => (decOTerm (Nat.unpair n).2).map .neg
    | 5 =>
      (decOTerm (Nat.unpair (Nat.unpair n).2).1).bind fun t₁ =>
        (decOTerm (Nat.unpair (Nat.unpair n).2).2).map fun t₂ => .add t₁ t₂
    | 6 =>
      (decOTerm (Nat.unpair (Nat.unpair n).2).1).bind fun t₁ =>
        (decOTerm (Nat.unpair (Nat.unpair n).2).2).map fun t₂ => .mul t₁ t₂
    | _ => none
termination_by n => n
decreasing_by
  all_goals
    first
    | exact Nat.lt_succ_of_le (Nat.unpair_right_le _)
    | exact Nat.lt_succ_of_le ((Nat.unpair_left_le _).trans (Nat.unpair_right_le _))
    | exact Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _))

lemma decOTerm_encOTerm (t : OTerm) : decOTerm (encOTerm t) = some t := by
  induction t with
  | fvar c => simp [encOTerm, decOTerm, Nat.unpair_pair]
  | bvar k => simp [encOTerm, decOTerm, Nat.unpair_pair]
  | zero => simp [encOTerm, decOTerm, Nat.unpair_pair]
  | one => simp [encOTerm, decOTerm, Nat.unpair_pair]
  | neg t ih => simp [encOTerm, decOTerm, Nat.unpair_pair, ih]
  | add t₁ t₂ ih₁ ih₂ => simp [encOTerm, decOTerm, Nat.unpair_pair, ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => simp [encOTerm, decOTerm, Nat.unpair_pair, ih₁, ih₂]

lemma encOTerm_of_decOTerm : ∀ {n : ℕ} {t : OTerm}, decOTerm n = some t → encOTerm t = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t h
    cases n with
    | zero => simp [decOTerm] at h
    | succ m =>
      simp only [decOTerm] at h
      have hle : (Nat.unpair m).2 ≤ m := Nat.unpair_right_le m
      generalize hp : Nat.unpair m = p at h hle
      have hpm : Nat.pair p.1 p.2 = m := by rw [← hp, Nat.pair_unpair]
      rcases p with ⟨tag, val⟩
      dsimp only at h hle hpm
      rcases tag with _ | _ | _ | _ | _ | _ | _ | tag
      · simp only [Option.some.injEq] at h
        subst h; simp [encOTerm, hpm]
      · simp only [Option.some.injEq] at h
        subst h; simp [encOTerm, hpm]
      · split_ifs at h with hv
        · subst hv; simp only [Option.some.injEq] at h; subst h
          simpa [encOTerm] using congrArg Nat.succ hpm
      · split_ifs at h with hv
        · subst hv; simp only [Option.some.injEq] at h; subst h
          simpa [encOTerm] using congrArg Nat.succ hpm
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨t', ht', rfl⟩ := h
        have e := ih val (Nat.lt_succ_of_le hle) ht'
        simp [encOTerm, e, hpm]
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := h
        have e₁ := ih (Nat.unpair val).1
          (Nat.lt_succ_of_le ((Nat.unpair_left_le val).trans hle)) ht₁
        have e₂ := ih (Nat.unpair val).2
          (Nat.lt_succ_of_le ((Nat.unpair_right_le val).trans hle)) ht₂
        simp [encOTerm, e₁, e₂, Nat.pair_unpair, hpm]
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := h
        have e₁ := ih (Nat.unpair val).1
          (Nat.lt_succ_of_le ((Nat.unpair_left_le val).trans hle)) ht₁
        have e₂ := ih (Nat.unpair val).2
          (Nat.lt_succ_of_le ((Nat.unpair_right_le val).trans hle)) ht₂
        simp [encOTerm, e₁, e₂, Nat.pair_unpair, hpm]
      · cases h

def encOForm : OForm → ℕ
  | .bot => Nat.pair 0 0 + 1
  | .eq t₁ t₂ => Nat.pair 1 (Nat.pair (encOTerm t₁) (encOTerm t₂)) + 1
  | .le t₁ t₂ => Nat.pair 2 (Nat.pair (encOTerm t₁) (encOTerm t₂)) + 1
  | .imp φ ψ => Nat.pair 3 (Nat.pair (encOForm φ) (encOForm ψ)) + 1
  | .all φ => Nat.pair 4 (encOForm φ) + 1

def decOForm : ℕ → Option OForm
  | 0 => none
  | n + 1 =>
    match (Nat.unpair n).1 with
    | 0 => if (Nat.unpair n).2 = 0 then some .bot else none
    | 1 =>
      (decOTerm (Nat.unpair (Nat.unpair n).2).1).bind fun t₁ =>
        (decOTerm (Nat.unpair (Nat.unpair n).2).2).map fun t₂ => .eq t₁ t₂
    | 2 =>
      (decOTerm (Nat.unpair (Nat.unpair n).2).1).bind fun t₁ =>
        (decOTerm (Nat.unpair (Nat.unpair n).2).2).map fun t₂ => .le t₁ t₂
    | 3 =>
      (decOForm (Nat.unpair (Nat.unpair n).2).1).bind fun φ =>
        (decOForm (Nat.unpair (Nat.unpair n).2).2).map fun ψ => .imp φ ψ
    | 4 => (decOForm (Nat.unpair n).2).map .all
    | _ => none
termination_by n => n
decreasing_by
  all_goals
    first
    | exact Nat.lt_succ_of_le (Nat.unpair_right_le _)
    | exact Nat.lt_succ_of_le ((Nat.unpair_left_le _).trans (Nat.unpair_right_le _))
    | exact Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _))

lemma decOForm_encOForm (φ : OForm) : decOForm (encOForm φ) = some φ := by
  induction φ with
  | bot => simp [encOForm, decOForm, Nat.unpair_pair]
  | eq t₁ t₂ => simp [encOForm, decOForm, Nat.unpair_pair, decOTerm_encOTerm]
  | le t₁ t₂ => simp [encOForm, decOForm, Nat.unpair_pair, decOTerm_encOTerm]
  | imp φ ψ ih₁ ih₂ => simp [encOForm, decOForm, Nat.unpair_pair, ih₁, ih₂]
  | all φ ih => simp [encOForm, decOForm, Nat.unpair_pair, ih]

lemma encOForm_of_decOForm : ∀ {n : ℕ} {φ : OForm}, decOForm n = some φ → encOForm φ = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro φ h
    cases n with
    | zero => simp [decOForm] at h
    | succ m =>
      simp only [decOForm] at h
      have hle : (Nat.unpair m).2 ≤ m := Nat.unpair_right_le m
      generalize hp : Nat.unpair m = p at h hle
      have hpm : Nat.pair p.1 p.2 = m := by rw [← hp, Nat.pair_unpair]
      rcases p with ⟨tag, val⟩
      dsimp only at h hle hpm
      rcases tag with _ | _ | _ | _ | _ | tag
      · split_ifs at h with hv
        · subst hv; simp only [Option.some.injEq] at h; subst h
          simpa [encOForm] using congrArg Nat.succ hpm
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := h
        simp [encOForm, encOTerm_of_decOTerm ht₁, encOTerm_of_decOTerm ht₂, Nat.pair_unpair, hpm]
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := h
        simp [encOForm, encOTerm_of_decOTerm ht₁, encOTerm_of_decOTerm ht₂, Nat.pair_unpair, hpm]
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := h
        have e₁ := ih (Nat.unpair val).1
          (Nat.lt_succ_of_le ((Nat.unpair_left_le val).trans hle)) h₁
        have e₂ := ih (Nat.unpair val).2
          (Nat.lt_succ_of_le ((Nat.unpair_right_le val).trans hle)) h₂
        simp [encOForm, e₁, e₂, Nat.pair_unpair, hpm]
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨φ', h', rfl⟩ := h
        have e := ih val (Nat.lt_succ_of_le hle) h'
        simp [encOForm, e, hpm]
      · cases h

/- ### 2. Operations on `OTerm` and `OForm` -/

def noBVar : OTerm → Bool
  | .fvar _ => true
  | .bvar _ => false
  | .zero => true
  | .one => true
  | .neg t => noBVar t
  | .add t₁ t₂ => noBVar t₁ && noBVar t₂
  | .mul t₁ t₂ => noBVar t₁ && noBVar t₂

def isFormTerm (d : ℕ) : OTerm → Bool
  | .fvar _ => true
  | .bvar k => decide (k < d)
  | .zero => true
  | .one => true
  | .neg t => isFormTerm d t
  | .add t₁ t₂ => isFormTerm d t₁ && isFormTerm d t₂
  | .mul t₁ t₂ => isFormTerm d t₁ && isFormTerm d t₂

def isForm : ℕ → OForm → Bool
  | _, .bot => true
  | d, .eq t₁ t₂ => isFormTerm d t₁ && isFormTerm d t₂
  | d, .le t₁ t₂ => isFormTerm d t₁ && isFormTerm d t₂
  | d, .imp φ ψ => isForm d φ && isForm d ψ
  | d, .all φ => isForm (d + 1) φ

def isSentTerm (d : ℕ) : OTerm → Bool
  | .fvar _ => false
  | .bvar k => decide (k < d)
  | .zero => true
  | .one => true
  | .neg t => isSentTerm d t
  | .add t₁ t₂ => isSentTerm d t₁ && isSentTerm d t₂
  | .mul t₁ t₂ => isSentTerm d t₁ && isSentTerm d t₂

def isSentForm : ℕ → OForm → Bool
  | _, .bot => true
  | d, .eq t₁ t₂ => isSentTerm d t₁ && isSentTerm d t₂
  | d, .le t₁ t₂ => isSentTerm d t₁ && isSentTerm d t₂
  | d, .imp φ ψ => isSentForm d φ && isSentForm d ψ
  | d, .all φ => isSentForm (d + 1) φ

def freshInTerm (c : ℕ) : OTerm → Bool
  | .fvar x => decide (x ≠ c)
  | .bvar _ => true
  | .zero => true
  | .one => true
  | .neg t => freshInTerm c t
  | .add t₁ t₂ => freshInTerm c t₁ && freshInTerm c t₂
  | .mul t₁ t₂ => freshInTerm c t₁ && freshInTerm c t₂

def freshInForm (c : ℕ) : OForm → Bool
  | .bot => true
  | .eq t₁ t₂ => freshInTerm c t₁ && freshInTerm c t₂
  | .le t₁ t₂ => freshInTerm c t₁ && freshInTerm c t₂
  | .imp φ ψ => freshInForm c φ && freshInForm c ψ
  | .all φ => freshInForm c φ

def maxVarTerm : OTerm → ℕ
  | .fvar c => c + 1
  | .bvar _ => 0
  | .zero => 0
  | .one => 0
  | .neg t => maxVarTerm t
  | .add t₁ t₂ => max (maxVarTerm t₁) (maxVarTerm t₂)
  | .mul t₁ t₂ => max (maxVarTerm t₁) (maxVarTerm t₂)

def maxVarForm : OForm → ℕ
  | .bot => 0
  | .eq t₁ t₂ => max (maxVarTerm t₁) (maxVarTerm t₂)
  | .le t₁ t₂ => max (maxVarTerm t₁) (maxVarTerm t₂)
  | .imp φ ψ => max (maxVarForm φ) (maxVarForm ψ)
  | .all φ => maxVarForm φ

def maxVarList (l : List OForm) : ℕ :=
  l.foldr (fun φ acc => max (maxVarForm φ) acc) 0

def substTerm0 (t : OTerm) : OTerm → OTerm
  | .fvar c => .fvar c
  | .bvar 0 => t
  | .bvar (k + 1) => .bvar k
  | .zero => .zero
  | .one => .one
  | .neg s => .neg (substTerm0 t s)
  | .add s₁ s₂ => .add (substTerm0 t s₁) (substTerm0 t s₂)
  | .mul s₁ s₂ => .mul (substTerm0 t s₁) (substTerm0 t s₂)

def substForm0 (t : OTerm) : OForm → OForm
  | .bot => .bot
  | .eq s₁ s₂ => .eq (substTerm0 t s₁) (substTerm0 t s₂)
  | .le s₁ s₂ => .le (substTerm0 t s₁) (substTerm0 t s₂)
  | .imp φ ψ => .imp (substForm0 t φ) (substForm0 t ψ)
  | .all φ => .all (substForm0 t φ)

def formSize : OForm → ℕ
  | .bot => 0
  | .eq _ _ => 0
  | .le _ _ => 0
  | .imp φ ψ => formSize φ + formSize ψ + 1
  | .all φ => formSize φ + 1

lemma formSize_substForm0 (t : OTerm) (φ : OForm) :
    formSize (substForm0 t φ) = formSize φ := by
  induction φ with
  | bot => rfl
  | eq _ _ => rfl
  | le _ _ => rfl
  | imp _ _ ih₁ ih₂ => simp [substForm0, formSize, ih₁, ih₂]
  | all _ ih => simp [substForm0, formSize, ih]

lemma isFormTerm_of_noBVar {t : OTerm} (ht : noBVar t = true) (d : ℕ) :
    isFormTerm d t = true := by
  induction t with
  | fvar _ => rfl
  | bvar _ => simp [noBVar] at ht
  | zero => rfl
  | one => rfl
  | neg _ ih => exact ih ht
  | add _ _ ih₁ ih₂ =>
    simp only [noBVar, Bool.and_eq_true] at ht
    simp [isFormTerm, ih₁ ht.1, ih₂ ht.2]
  | mul _ _ ih₁ ih₂ =>
    simp only [noBVar, Bool.and_eq_true] at ht
    simp [isFormTerm, ih₁ ht.1, ih₂ ht.2]

lemma noBVar_of_isFormTerm_zero {t : OTerm} (ht : isFormTerm 0 t = true) :
    noBVar t = true := by
  induction t with
  | fvar _ => rfl
  | bvar _ => simp [isFormTerm] at ht
  | zero => rfl
  | one => rfl
  | neg _ ih => exact ih ht
  | add _ _ ih₁ ih₂ =>
    simp only [isFormTerm, Bool.and_eq_true] at ht
    simp [noBVar, ih₁ ht.1, ih₂ ht.2]
  | mul _ _ ih₁ ih₂ =>
    simp only [isFormTerm, Bool.and_eq_true] at ht
    simp [noBVar, ih₁ ht.1, ih₂ ht.2]

lemma isFormTerm_of_isSentTerm {d : ℕ} {t : OTerm} (ht : isSentTerm d t = true) :
    isFormTerm d t = true := by
  induction t with
  | fvar _ => simp [isSentTerm] at ht
  | bvar _ => exact ht
  | zero => rfl
  | one => rfl
  | neg _ ih => exact ih ht
  | add _ _ ih₁ ih₂ =>
    simp only [isSentTerm, Bool.and_eq_true] at ht
    simp [isFormTerm, ih₁ ht.1, ih₂ ht.2]
  | mul _ _ ih₁ ih₂ =>
    simp only [isSentTerm, Bool.and_eq_true] at ht
    simp [isFormTerm, ih₁ ht.1, ih₂ ht.2]

lemma isForm_of_isSentForm {d : ℕ} {φ : OForm} (hφ : isSentForm d φ = true) :
    isForm d φ = true := by
  induction φ generalizing d with
  | bot => rfl
  | eq _ _ =>
    simp only [isSentForm, Bool.and_eq_true] at hφ
    simp [isForm, isFormTerm_of_isSentTerm hφ.1, isFormTerm_of_isSentTerm hφ.2]
  | le _ _ =>
    simp only [isSentForm, Bool.and_eq_true] at hφ
    simp [isForm, isFormTerm_of_isSentTerm hφ.1, isFormTerm_of_isSentTerm hφ.2]
  | imp _ _ ih₁ ih₂ =>
    simp only [isSentForm, Bool.and_eq_true] at hφ
    simp [isForm, ih₁ hφ.1, ih₂ hφ.2]
  | all _ ih => exact ih hφ

lemma isFormTerm_substTerm0 {t s : OTerm} {d : ℕ}
    (ht : noBVar t = true) (hs : isFormTerm (d + 1) s = true) :
    isFormTerm d (substTerm0 t s) = true := by
  induction s with
  | fvar _ => rfl
  | bvar k =>
    cases k with
    | zero => exact isFormTerm_of_noBVar ht d
    | succ k =>
      simp only [substTerm0, isFormTerm, decide_eq_true_eq] at hs ⊢
      omega
  | zero => rfl
  | one => rfl
  | neg _ ih => exact ih hs
  | add _ _ ih₁ ih₂ =>
    simp only [isFormTerm, Bool.and_eq_true] at hs
    simp [substTerm0, isFormTerm, ih₁ hs.1, ih₂ hs.2]
  | mul _ _ ih₁ ih₂ =>
    simp only [isFormTerm, Bool.and_eq_true] at hs
    simp [substTerm0, isFormTerm, ih₁ hs.1, ih₂ hs.2]

lemma isForm_substForm0 {t : OTerm} {φ : OForm} {d : ℕ}
    (ht : noBVar t = true) (hφ : isForm (d + 1) φ = true) :
    isForm d (substForm0 t φ) = true := by
  induction φ generalizing d with
  | bot => rfl
  | eq _ _ =>
    simp only [isForm, Bool.and_eq_true] at hφ
    simp [substForm0, isForm, isFormTerm_substTerm0 ht hφ.1, isFormTerm_substTerm0 ht hφ.2]
  | le _ _ =>
    simp only [isForm, Bool.and_eq_true] at hφ
    simp [substForm0, isForm, isFormTerm_substTerm0 ht hφ.1, isFormTerm_substTerm0 ht hφ.2]
  | imp _ _ ih₁ ih₂ =>
    simp only [isForm, Bool.and_eq_true] at hφ
    simp [substForm0, isForm, ih₁ hφ.1, ih₂ hφ.2]
  | all _ ih => exact ih hφ

lemma freshInTerm_of_ge_maxVarTerm {c : ℕ} {t : OTerm} (h : maxVarTerm t ≤ c) :
    freshInTerm c t = true := by
  induction t with
  | fvar x => simp only [maxVarTerm] at h; simp [freshInTerm]; omega
  | bvar _ => rfl
  | zero => rfl
  | one => rfl
  | neg _ ih => exact ih h
  | add _ _ ih₁ ih₂ =>
    simp only [maxVarTerm, max_le_iff] at h
    simp [freshInTerm, ih₁ h.1, ih₂ h.2]
  | mul _ _ ih₁ ih₂ =>
    simp only [maxVarTerm, max_le_iff] at h
    simp [freshInTerm, ih₁ h.1, ih₂ h.2]

lemma freshInForm_of_ge_maxVarForm {c : ℕ} {φ : OForm} (h : maxVarForm φ ≤ c) :
    freshInForm c φ = true := by
  induction φ with
  | bot => rfl
  | eq _ _ =>
    simp only [maxVarForm, max_le_iff] at h
    simp [freshInForm, freshInTerm_of_ge_maxVarTerm h.1, freshInTerm_of_ge_maxVarTerm h.2]
  | le _ _ =>
    simp only [maxVarForm, max_le_iff] at h
    simp [freshInForm, freshInTerm_of_ge_maxVarTerm h.1, freshInTerm_of_ge_maxVarTerm h.2]
  | imp _ _ ih₁ ih₂ =>
    simp only [maxVarForm, max_le_iff] at h
    simp [freshInForm, ih₁ h.1, ih₂ h.2]
  | all _ ih => exact ih h

lemma maxVarForm_le_maxVarList {φ : OForm} {l : List OForm} (h : φ ∈ l) :
    maxVarForm φ ≤ maxVarList l := by
  induction l with
  | nil => cases h
  | cons ψ l ih =>
    simp only [maxVarList, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | hmem
    · exact le_max_left _ _
    · exact (ih hmem).trans (le_max_right _ _)

/- ### 3. Semantics and equivalence with Mathlib's `FirstOrder.Language` -/

def evalTerm {M : Type*} [LO.Structure M] (v ρ : ℕ → M) : OTerm → M
  | .fvar c => v c
  | .bvar k => ρ k
  | .zero => Structure.funMap (L := LO) (Sum.inl ringFunc.zero) ![]
  | .one => Structure.funMap (L := LO) (Sum.inl ringFunc.one) ![]
  | .neg t => Structure.funMap (L := LO) (Sum.inl ringFunc.neg) ![evalTerm v ρ t]
  | .add t₁ t₂ =>
      Structure.funMap (L := LO) (Sum.inl ringFunc.add) ![evalTerm v ρ t₁, evalTerm v ρ t₂]
  | .mul t₁ t₂ =>
      Structure.funMap (L := LO) (Sum.inl ringFunc.mul) ![evalTerm v ρ t₁, evalTerm v ρ t₂]

def evalForm {M : Type*} [LO.Structure M] (v : ℕ → M) : ℕ → (ℕ → M) → OForm → Prop
  | _, _, .bot => False
  | _, ρ, .eq t₁ t₂ => evalTerm v ρ t₁ = evalTerm v ρ t₂
  | _, ρ, .le t₁ t₂ =>
      Structure.RelMap (L := LO) (Sum.inr orderRel.le) ![evalTerm v ρ t₁, evalTerm v ρ t₂]
  | d, ρ, .imp φ ψ => evalForm v d ρ φ → evalForm v d ρ ψ
  | d, ρ, .all φ => ∀ a : M, evalForm v (d + 1) (Function.update ρ d a) φ

def cons0 {M : Type*} (a : M) (ρ : ℕ → M) : ℕ → M
  | 0 => a
  | k + 1 => ρ k

lemma update_cons0 {M : Type*} (a b : M) (ρ : ℕ → M) (d : ℕ) :
    Function.update (cons0 a ρ) (d + 1) b = cons0 a (Function.update ρ d b) := by
  ext k
  cases k with
  | zero => simp [cons0, Function.update]
  | succ k => simp [cons0, Function.update]

lemma evalTerm_eq_of_agree {M : Type*} [LO.Structure M] {v v' ρ ρ' : ℕ → M} {d : ℕ} {t : OTerm}
    (ht : isFormTerm d t = true)
    (hv : ∀ c, freshInTerm c t = false → v c = v' c)
    (hρ : ∀ k < d, ρ k = ρ' k) :
    evalTerm v ρ t = evalTerm v' ρ' t := by
  induction t with
  | fvar c => exact hv c (by simp [freshInTerm])
  | bvar k =>
    simp only [isFormTerm, decide_eq_true_eq] at ht
    exact hρ k ht
  | zero => rfl
  | one => rfl
  | neg _ ih =>
    simp only [evalTerm]
    rw [ih ht hv]
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [isFormTerm, Bool.and_eq_true] at ht
    simp only [evalTerm]
    rw [ih₁ ht.1 (fun c hc => hv c (by simp [freshInTerm, hc])),
        ih₂ ht.2 (fun c hc => hv c (by simp [freshInTerm, hc]))]
  | mul t₁ t₂ ih₁ ih₂ =>
    simp only [isFormTerm, Bool.and_eq_true] at ht
    simp only [evalTerm]
    rw [ih₁ ht.1 (fun c hc => hv c (by simp [freshInTerm, hc])),
        ih₂ ht.2 (fun c hc => hv c (by simp [freshInTerm, hc]))]

lemma evalForm_iff_of_agree {M : Type*} [LO.Structure M] {v v' ρ ρ' : ℕ → M} {d : ℕ} {φ : OForm}
    (hφ : isForm d φ = true)
    (hv : ∀ c, freshInForm c φ = false → v c = v' c)
    (hρ : ∀ k < d, ρ k = ρ' k) :
    evalForm v d ρ φ ↔ evalForm v' d ρ' φ := by
  induction φ generalizing d ρ ρ' with
  | bot => rfl
  | eq t₁ t₂ =>
    simp only [isForm, Bool.and_eq_true] at hφ
    simp only [evalForm]
    rw [evalTerm_eq_of_agree hφ.1 (fun c hc => hv c (by simp [freshInForm, hc])) hρ,
        evalTerm_eq_of_agree hφ.2 (fun c hc => hv c (by simp [freshInForm, hc])) hρ]
  | le t₁ t₂ =>
    simp only [isForm, Bool.and_eq_true] at hφ
    simp only [evalForm]
    rw [evalTerm_eq_of_agree hφ.1 (fun c hc => hv c (by simp [freshInForm, hc])) hρ,
        evalTerm_eq_of_agree hφ.2 (fun c hc => hv c (by simp [freshInForm, hc])) hρ]
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [isForm, Bool.and_eq_true] at hφ
    simp only [evalForm]
    rw [ih₁ hφ.1 (fun c hc => hv c (by simp [freshInForm, hc])) hρ,
        ih₂ hφ.2 (fun c hc => hv c (by simp [freshInForm, hc])) hρ]
  | all φ ih =>
    simp only [evalForm]
    refine forall_congr' fun a => ih hφ hv fun k hk => ?_
    by_cases hkd : k = d
    · subst hkd; simp
    · simp [Function.update, hkd, hρ k (by omega)]

lemma evalForm_update_fresh {M : Type*} [LO.Structure M] {v ρ : ℕ → M} {d c : ℕ} {a : M}
    {φ : OForm} (hφ : isForm d φ = true) (hf : freshInForm c φ = true) :
    evalForm (Function.update v c a) d ρ φ ↔ evalForm v d ρ φ := by
  refine evalForm_iff_of_agree hφ (fun x hx => ?_) (fun _ _ => rfl)
  have hxc : x ≠ c := by
    intro h; subst h; rw [hf] at hx; cases hx
  simp [Function.update, hxc]

lemma evalTerm_substTerm0 {M : Type*} [LO.Structure M] {v ρ : ℕ → M} {t s : OTerm}
    (_ht : noBVar t = true) :
    evalTerm v ρ (substTerm0 t s) = evalTerm v (cons0 (evalTerm v ρ t) ρ) s := by
  induction s with
  | fvar _ => rfl
  | bvar k => cases k <;> rfl
  | zero => rfl
  | one => rfl
  | neg _ ih => simp [substTerm0, evalTerm, ih]
  | add _ _ ih₁ ih₂ => simp [substTerm0, evalTerm, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp [substTerm0, evalTerm, ih₁, ih₂]

lemma evalForm_substForm0 {M : Type*} [LO.Structure M] {v : ℕ → M} {t : OTerm}
    (ht : noBVar t = true) :
    ∀ {d : ℕ} {ρ : ℕ → M} {φ : OForm},
      evalForm v d ρ (substForm0 t φ) ↔ evalForm v (d + 1) (cons0 (evalTerm v ρ t) ρ) φ := by
  intro d ρ φ
  induction φ generalizing d ρ with
  | bot => rfl
  | eq s₁ s₂ => simp [substForm0, evalForm, evalTerm_substTerm0 ht]
  | le s₁ s₂ => simp [substForm0, evalForm, evalTerm_substTerm0 ht]
  | imp φ₁ φ₂ ih₁ ih₂ => simp [substForm0, evalForm, ih₁, ih₂]
  | all φ ih =>
    simp only [substForm0, evalForm]
    refine forall_congr' fun a => ?_
    have heq : evalTerm v (Function.update ρ d a) t = evalTerm v ρ t :=
      evalTerm_eq_of_agree (isFormTerm_of_noBVar ht 0) (fun _ _ => rfl) (fun _ hk => by omega)
    rw [ih, heq, update_cons0]

lemma evalForm_substForm0_zero {M : Type*} [LO.Structure M] {v ρ : ℕ → M} {t : OTerm} {φ : OForm}
    (ht : noBVar t = true) (hφ : isForm 1 φ = true) :
    evalForm v 0 ρ (substForm0 t φ) ↔
      evalForm v 1 (Function.update ρ 0 (evalTerm v ρ t)) φ := by
  rw [evalForm_substForm0 ht]
  refine evalForm_iff_of_agree hφ (fun _ _ => rfl) fun k hk => ?_
  have hk0 : k = 0 := by omega
  subst hk0
  simp [cons0]

/- ### 4. Translation between `LO.Sentence` and `OForm` -/

def ofMathlibTerm {d : ℕ} : LO.Term (Empty ⊕ Fin d) → OTerm
  | .var (.inl e) => Empty.elim e
  | .var (.inr i) => .bvar i.val
  | .func (.inl .zero) _ => .zero
  | .func (.inl .one) _ => .one
  | .func (.inl .neg) ts => .neg (ofMathlibTerm (ts 0))
  | .func (.inl .add) ts => .add (ofMathlibTerm (ts 0)) (ofMathlibTerm (ts 1))
  | .func (.inl .mul) ts => .mul (ofMathlibTerm (ts 0)) (ofMathlibTerm (ts 1))
  | .func (.inr f) _ => Empty.elim f

def ofMathlibForm {d : ℕ} : LO.BoundedFormula Empty d → OForm
  | .falsum => .bot
  | .equal t₁ t₂ => .eq (ofMathlibTerm t₁) (ofMathlibTerm t₂)
  | .rel (.inl r) _ => Empty.elim r
  | .rel (.inr .le) ts => .le (ofMathlibTerm (ts 0)) (ofMathlibTerm (ts 1))
  | .imp φ ψ => .imp (ofMathlibForm φ) (ofMathlibForm ψ)
  | .all φ => .all (ofMathlibForm φ)

lemma isSentTerm_ofMathlibTerm {d : ℕ} (t : LO.Term (Empty ⊕ Fin d)) :
    isSentTerm d (ofMathlibTerm t) = true := by
  induction t with
  | var x =>
    rcases x with e | i
    · exact Empty.elim e
    · simp [ofMathlibTerm, isSentTerm, i.isLt]
  | func f ts ih =>
    rcases f with f | f
    · cases f <;> simp [ofMathlibTerm, isSentTerm, ih]
    · exact Empty.elim f

lemma isSentForm_ofMathlibForm {d : ℕ} (φ : LO.BoundedFormula Empty d) :
    isSentForm d (ofMathlibForm φ) = true := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp [ofMathlibForm, isSentForm, isSentTerm_ofMathlibTerm]
  | rel R ts =>
    rcases R with R | R
    · exact Empty.elim R
    · cases R; simp [ofMathlibForm, isSentForm, isSentTerm_ofMathlibTerm]
  | imp _ _ ih₁ ih₂ => simp [ofMathlibForm, isSentForm, ih₁, ih₂]
  | all _ ih => exact ih

lemma evalTerm_ofMathlibTerm {M : Type*} [LO.Structure M] {d : ℕ}
    (t : LO.Term (Empty ⊕ Fin d)) (v ρ : ℕ → M) (xs : Fin d → M)
    (hxs : ∀ i : Fin d, ρ i.val = xs i) :
    evalTerm v ρ (ofMathlibTerm t) = t.realize (Sum.elim Empty.elim xs) := by
  induction t with
  | var x =>
    rcases x with e | i
    · exact Empty.elim e
    · simp [ofMathlibTerm, evalTerm, hxs i]
  | func f ts ih =>
    rcases f with f | f
    · cases f
      · simp only [ofMathlibTerm, evalTerm]
        congr 1; ext i; fin_cases i <;> simp [ih]
      · simp only [ofMathlibTerm, evalTerm]
        congr 1; ext i; fin_cases i <;> simp [ih]
      · simp only [ofMathlibTerm, evalTerm]
        congr 1; ext i; fin_cases i; simp [ih]
      · simp only [ofMathlibTerm, evalTerm]
        congr 1; ext i; exact Fin.elim0 i
      · simp only [ofMathlibTerm, evalTerm]
        congr 1; ext i; exact Fin.elim0 i
    · exact Empty.elim f

lemma evalForm_ofMathlibForm {M : Type*} [LO.Structure M] {d : ℕ}
    (φ : LO.BoundedFormula Empty d) (v ρ : ℕ → M) (xs : Fin d → M)
    (hxs : ∀ i : Fin d, ρ i.val = xs i) :
    evalForm v d ρ (ofMathlibForm φ) ↔ φ.Realize Empty.elim xs := by
  induction φ generalizing ρ with
  | falsum => simp [ofMathlibForm, evalForm, BoundedFormula.Realize]
  | equal t₁ t₂ =>
    simp [ofMathlibForm, evalForm, BoundedFormula.Realize, evalTerm_ofMathlibTerm _ v ρ xs hxs]
  | rel R ts =>
    rcases R with R | R
    · exact Empty.elim R
    · cases R
      simp only [ofMathlibForm, evalForm, BoundedFormula.Realize]
      have hvec : (![evalTerm v ρ (ofMathlibTerm (ts 0)), evalTerm v ρ (ofMathlibTerm (ts 1))] :
          Fin 2 → M) = fun i => (ts i).realize (Sum.elim Empty.elim xs) := by
        ext i; fin_cases i <;> simp [evalTerm_ofMathlibTerm _ v ρ xs hxs]
      rw [hvec]
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp [ofMathlibForm, evalForm, ih₁ ρ xs hxs, ih₂ ρ xs hxs]
  | all φ ih =>
    simp only [ofMathlibForm, evalForm, BoundedFormula.realize_all]
    refine forall_congr' fun a => ih (Function.update ρ _ a) (Fin.snoc xs a) fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Function.update]
    · simp [Function.update, Nat.ne_of_lt j.isLt, hxs j]

lemma evalForm_ofMathlibSentence {M : Type*} [LO.Structure M]
    (φ : LO.Sentence) (v ρ : ℕ → M) :
    evalForm v 0 ρ (ofMathlibForm φ) ↔ M ⊨ φ := by
  have he : (Empty.elim : Empty → M) = default := funext fun x => Empty.elim x
  simpa [Sentence.Realize, Formula.Realize, he] using
    evalForm_ofMathlibForm φ v ρ default (fun i => Fin.elim0 i)

def toMathlibTerm (d : ℕ) : (t : OTerm) → isSentTerm d t = true → LO.Term (Empty ⊕ Fin d)
  | .fvar _, h => by simp [isSentTerm] at h
  | .bvar k, h => .var (.inr ⟨k, by simpa [isSentTerm] using h⟩)
  | .zero, _ => .func (.inl .zero) Fin.elim0
  | .one, _ => .func (.inl .one) Fin.elim0
  | .neg t, h => .func (.inl .neg) ![toMathlibTerm d t h]
  | .add t₁ t₂, h =>
      .func (.inl .add)
        ![toMathlibTerm d t₁ (Bool.and_eq_true_iff.mp h).1,
          toMathlibTerm d t₂ (Bool.and_eq_true_iff.mp h).2]
  | .mul t₁ t₂, h =>
      .func (.inl .mul)
        ![toMathlibTerm d t₁ (Bool.and_eq_true_iff.mp h).1,
          toMathlibTerm d t₂ (Bool.and_eq_true_iff.mp h).2]

def toMathlibForm : (d : ℕ) → (φ : OForm) → isSentForm d φ = true → LO.BoundedFormula Empty d
  | _, .bot, _ => .falsum
  | d, .eq t₁ t₂, h =>
      .equal (toMathlibTerm d t₁ (Bool.and_eq_true_iff.mp h).1)
             (toMathlibTerm d t₂ (Bool.and_eq_true_iff.mp h).2)
  | d, .le t₁ t₂, h =>
      .rel (.inr .le)
        ![toMathlibTerm d t₁ (Bool.and_eq_true_iff.mp h).1,
          toMathlibTerm d t₂ (Bool.and_eq_true_iff.mp h).2]
  | d, .imp φ ψ, h =>
      .imp (toMathlibForm d φ (Bool.and_eq_true_iff.mp h).1)
           (toMathlibForm d ψ (Bool.and_eq_true_iff.mp h).2)
  | d, .all φ, h => .all (toMathlibForm (d + 1) φ h)

lemma ofMathlibTerm_toMathlibTerm {d : ℕ} (t : OTerm) (h : isSentTerm d t = true) :
    ofMathlibTerm (toMathlibTerm d t h) = t := by
  induction t with
  | fvar _ => simp [isSentTerm] at h
  | bvar _ => rfl
  | zero => rfl
  | one => rfl
  | neg _ ih => simp [toMathlibTerm, ofMathlibTerm, ih h]
  | add _ _ ih₁ ih₂ =>
    simp [toMathlibTerm, ofMathlibTerm,
      ih₁ (Bool.and_eq_true_iff.mp h).1, ih₂ (Bool.and_eq_true_iff.mp h).2]
  | mul _ _ ih₁ ih₂ =>
    simp [toMathlibTerm, ofMathlibTerm,
      ih₁ (Bool.and_eq_true_iff.mp h).1, ih₂ (Bool.and_eq_true_iff.mp h).2]

lemma ofMathlibForm_toMathlibForm : ∀ {d : ℕ} (φ : OForm) (h : isSentForm d φ = true),
    ofMathlibForm (toMathlibForm d φ h) = φ := by
  intro d φ
  induction φ generalizing d with
  | bot => intro _; rfl
  | eq _ _ =>
    intro h
    simp [toMathlibForm, ofMathlibForm, ofMathlibTerm_toMathlibTerm]
  | le _ _ =>
    intro h
    simp [toMathlibForm, ofMathlibForm, ofMathlibTerm_toMathlibTerm]
  | imp _ _ ih₁ ih₂ =>
    intro h
    simp [toMathlibForm, ofMathlibForm,
      ih₁ (Bool.and_eq_true_iff.mp h).1, ih₂ (Bool.and_eq_true_iff.mp h).2]
  | all _ ih =>
    intro h
    simp [toMathlibForm, ofMathlibForm, ih h]

lemma ofMathlibTerm_injective {d : ℕ} :
    Function.Injective (ofMathlibTerm (d := d)) := by
  intro t₁ t₂ h
  induction t₁ generalizing t₂ with
  | var x =>
    rcases x with e | i
    · exact Empty.elim e
    · cases t₂ with
      | var y =>
        rcases y with e' | j
        · exact Empty.elim e'
        · simp only [ofMathlibTerm, OTerm.bvar.injEq] at h
          exact congrArg (Term.var ∘ Sum.inr) (Fin.ext h)
      | func g _ =>
        rcases g with g | g
        · cases g <;> simp [ofMathlibTerm] at h
        · exact Empty.elim g
  | func f ts ih =>
    cases t₂ with
    | var y =>
      rcases f with f | f
      · rcases y with e' | j
        · exact Empty.elim e'
        · cases f <;> simp [ofMathlibTerm] at h
      · exact Empty.elim f
    | func g us =>
      rcases f with f | f
      · rcases g with g | g
        · cases f <;> cases g <;> simp only [ofMathlibTerm, OTerm.add.injEq, OTerm.mul.injEq,
            OTerm.neg.injEq, reduceCtorEq] at h
          · congr 1; ext i; fin_cases i
            · exact ih 0 h.1
            · exact ih 1 h.2
          · congr 1; ext i; fin_cases i
            · exact ih 0 h.1
            · exact ih 1 h.2
          · congr 1; ext i; fin_cases i; exact ih 0 h
          · congr 1; ext i; exact Fin.elim0 i
          · congr 1; ext i; exact Fin.elim0 i
        · exact Empty.elim g
      · exact Empty.elim f

lemma ofMathlibForm_injective : ∀ {d : ℕ},
    Function.Injective (ofMathlibForm (d := d)) := by
  intro d φ₁ φ₂ h
  induction φ₁ with
  | falsum =>
    cases φ₂ with
    | falsum => rfl
    | equal _ _ => simp [ofMathlibForm] at h
    | rel R _ => rcases R with R | R; exact Empty.elim R; cases R; simp [ofMathlibForm] at h
    | imp _ _ => simp [ofMathlibForm] at h
    | all _ => simp [ofMathlibForm] at h
  | equal t₁ t₂ =>
    cases φ₂ with
    | falsum => simp [ofMathlibForm] at h
    | equal s₁ s₂ =>
      simp only [ofMathlibForm, OForm.eq.injEq] at h
      rw [ofMathlibTerm_injective h.1, ofMathlibTerm_injective h.2]
    | rel R _ => rcases R with R | R; exact Empty.elim R; cases R; simp [ofMathlibForm] at h
    | imp _ _ => simp [ofMathlibForm] at h
    | all _ => simp [ofMathlibForm] at h
  | rel R ts =>
    rcases R with R | R
    · exact Empty.elim R
    · cases R
      cases φ₂ with
      | falsum => simp [ofMathlibForm] at h
      | equal _ _ => simp [ofMathlibForm] at h
      | rel R' us =>
        rcases R' with R' | R'
        · exact Empty.elim R'
        · cases R'
          simp only [ofMathlibForm, OForm.le.injEq] at h
          congr 1; ext i; fin_cases i
          · exact ofMathlibTerm_injective h.1
          · exact ofMathlibTerm_injective h.2
      | imp _ _ => simp [ofMathlibForm] at h
      | all _ => simp [ofMathlibForm] at h
  | imp φ₁ ψ₁ ih₁ ih₂ =>
    cases φ₂ with
    | falsum => simp [ofMathlibForm] at h
    | equal _ _ => simp [ofMathlibForm] at h
    | rel R _ => rcases R with R | R; exact Empty.elim R; cases R; simp [ofMathlibForm] at h
    | imp φ₂ ψ₂ =>
      simp only [ofMathlibForm, OForm.imp.injEq] at h
      rw [ih₁ h.1, ih₂ h.2]
    | all _ => simp [ofMathlibForm] at h
  | all φ₁ ih =>
    cases φ₂ with
    | falsum => simp [ofMathlibForm] at h
    | equal _ _ => simp [ofMathlibForm] at h
    | rel R _ => rcases R with R | R; exact Empty.elim R; cases R; simp [ofMathlibForm] at h
    | imp _ _ => simp [ofMathlibForm] at h
    | all φ₂ =>
      simp only [ofMathlibForm, OForm.all.injEq] at h
      rw [ih h]

/- ### 5. Cut-free two-sided sequent calculus (`Deriv`) -/

inductive Deriv : List OForm → List OForm → Prop
  | ax_id {Γ Δ φ} : φ ∈ Γ → φ ∈ Δ → Deriv Γ Δ
  | ax_bot {Γ Δ} : OForm.bot ∈ Γ → Deriv Γ Δ
  | imp_L {Γ Δ φ ψ} : OForm.imp φ ψ ∈ Γ → Deriv Γ (φ :: Δ) → Deriv (ψ :: Γ) Δ → Deriv Γ Δ
  | imp_R {Γ Δ φ ψ} : OForm.imp φ ψ ∈ Δ → Deriv (φ :: Γ) (ψ :: Δ) → Deriv Γ Δ
  | all_L {Γ Δ φ t} : OForm.all φ ∈ Γ → noBVar t = true → Deriv (substForm0 t φ :: Γ) Δ → Deriv Γ Δ
  | all_R {Γ Δ φ c} : OForm.all φ ∈ Δ →
      (∀ ψ ∈ Γ, freshInForm c ψ = true) →
      (∀ ψ ∈ Δ, freshInForm c ψ = true) →
      Deriv Γ (substForm0 (.fvar c) φ :: Δ) → Deriv Γ Δ
  | eq_refl {Γ Δ t} : noBVar t = true → Deriv (OForm.eq t t :: Γ) Δ → Deriv Γ Δ
  | eq_symm {Γ Δ t₁ t₂} : OForm.eq t₁ t₂ ∈ Γ → Deriv (OForm.eq t₂ t₁ :: Γ) Δ → Deriv Γ Δ
  | eq_trans {Γ Δ t₁ t₂ t₃} : OForm.eq t₁ t₂ ∈ Γ → OForm.eq t₂ t₃ ∈ Γ →
      Deriv (OForm.eq t₁ t₃ :: Γ) Δ → Deriv Γ Δ
  | eq_neg {Γ Δ s t} : OForm.eq s t ∈ Γ → Deriv (OForm.eq (.neg s) (.neg t) :: Γ) Δ → Deriv Γ Δ
  | eq_add {Γ Δ s₁ t₁ s₂ t₂} : OForm.eq s₁ t₁ ∈ Γ → OForm.eq s₂ t₂ ∈ Γ →
      Deriv (OForm.eq (.add s₁ s₂) (.add t₁ t₂) :: Γ) Δ → Deriv Γ Δ
  | eq_mul {Γ Δ s₁ t₁ s₂ t₂} : OForm.eq s₁ t₁ ∈ Γ → OForm.eq s₂ t₂ ∈ Γ →
      Deriv (OForm.eq (.mul s₁ s₂) (.mul t₁ t₂) :: Γ) Δ → Deriv Γ Δ
  | eq_le {Γ Δ s₁ t₁ s₂ t₂} : OForm.eq s₁ t₁ ∈ Γ → OForm.eq s₂ t₂ ∈ Γ →
      OForm.le s₁ s₂ ∈ Γ → Deriv (OForm.le t₁ t₂ :: Γ) Δ → Deriv Γ Δ

/- ### 6. Soundness of `Deriv` -/

theorem deriv_sound {Γ Δ : List OForm} (hd : Deriv Γ Δ) :
    ∀ {M : Type*} [LO.Structure M] (v ρ : ℕ → M),
      (∀ φ ∈ Γ, isForm 0 φ = true) →
      (∀ ψ ∈ Δ, isForm 0 ψ = true) →
      (∀ φ ∈ Γ, evalForm v 0 ρ φ) →
      ∃ ψ ∈ Δ, evalForm v 0 ρ ψ := by
  induction hd with
  | ax_id hΓ hΔ =>
    intro M _ v ρ _ _ hv
    exact ⟨_, hΔ, hv _ hΓ⟩
  | ax_bot hΓ =>
    intro M _ v ρ _ _ hv
    exact False.elim (hv _ hΓ)
  | @imp_L Γ Δ φ ψ hmem _ _ ih₁ ih₂ =>
    intro M _ v ρ hΓf hΔf hv
    have hfp := hΓf _ hmem
    simp only [isForm, Bool.and_eq_true] at hfp
    have himp : evalForm v 0 ρ φ → evalForm v 0 ρ ψ := hv _ hmem
    by_cases hφ : evalForm v 0 ρ φ
    · refine ih₂ v ρ (List.forall_mem_cons.mpr ⟨hfp.2, hΓf⟩) hΔf
        (List.forall_mem_cons.mpr ⟨himp hφ, hv⟩)
    · obtain ⟨θ, hθ, hθv⟩ := ih₁ v ρ hΓf (List.forall_mem_cons.mpr ⟨hfp.1, hΔf⟩) hv
      rcases List.mem_cons.mp hθ with rfl | hθΔ
      · exact False.elim (hφ hθv)
      · exact ⟨θ, hθΔ, hθv⟩
  | @imp_R Γ Δ φ ψ hmem _ ih =>
    intro M _ v ρ hΓf hΔf hv
    have hfp := hΔf _ hmem
    simp only [isForm, Bool.and_eq_true] at hfp
    by_cases hφ : evalForm v 0 ρ φ
    · obtain ⟨θ, hθ, hθv⟩ := ih v ρ (List.forall_mem_cons.mpr ⟨hfp.1, hΓf⟩)
        (List.forall_mem_cons.mpr ⟨hfp.2, hΔf⟩) (List.forall_mem_cons.mpr ⟨hφ, hv⟩)
      rcases List.mem_cons.mp hθ with rfl | hθΔ
      · exact ⟨OForm.imp φ θ, hmem, fun _ => hθv⟩
      · exact ⟨θ, hθΔ, hθv⟩
    · exact ⟨OForm.imp φ ψ, hmem, fun h => False.elim (hφ h)⟩
  | @all_L Γ Δ φ t hmem ht _ ih =>
    intro M _ v ρ hΓf hΔf hv
    have hφ1 : isForm 1 φ = true := hΓf _ hmem
    have hinst : evalForm v 0 ρ (substForm0 t φ) :=
      (evalForm_substForm0_zero ht hφ1).2 (hv _ hmem (evalTerm v ρ t))
    exact ih v ρ (List.forall_mem_cons.mpr ⟨isForm_substForm0 ht hφ1, hΓf⟩) hΔf
      (List.forall_mem_cons.mpr ⟨hinst, hv⟩)
  | @all_R Γ Δ φ c hmem hfΓ hfΔ _ ih =>
    intro M _ v ρ hΓf hΔf hv
    have hφ1 : isForm 1 φ = true := hΔf _ hmem
    by_cases hall : ∀ a : M, evalForm v 1 (Function.update ρ 0 a) φ
    · exact ⟨OForm.all φ, hmem, hall⟩
    · push Not at hall
      obtain ⟨a, ha⟩ := hall
      let v' := Function.update v c a
      have hv' : ∀ θ ∈ Γ, evalForm v' 0 ρ θ := fun θ hθ =>
        (evalForm_update_fresh (hΓf θ hθ) (hfΓ θ hθ)).2 (hv θ hθ)
      obtain ⟨θ, hθ, hθv'⟩ := ih v' ρ hΓf
        (List.forall_mem_cons.mpr ⟨isForm_substForm0 (by rfl) hφ1, hΔf⟩) hv'
      rcases List.mem_cons.mp hθ with rfl | hθΔ
      · exfalso
        have h1 : evalForm v' 1 (Function.update ρ 0 a) φ := by
          have := (evalForm_substForm0_zero (t := .fvar c) (by rfl) hφ1).1 hθv'
          simpa [v', evalTerm] using this
        have h2 : evalForm v 1 (Function.update ρ 0 a) φ :=
          (evalForm_update_fresh hφ1 (hfΔ (OForm.all φ) hmem)).1 h1
        exact ha h2
      · exact ⟨θ, hθΔ, (evalForm_update_fresh (hΔf θ hθΔ) (hfΔ θ hθΔ)).1 hθv'⟩
  | @eq_refl Γ Δ t ht _ ih =>
    intro M _ v ρ hΓf hΔf hv
    have hft : isFormTerm 0 t = true := isFormTerm_of_noBVar ht 0
    exact ih v ρ (List.forall_mem_cons.mpr ⟨by simp [isForm, hft], hΓf⟩) hΔf
      (List.forall_mem_cons.mpr ⟨rfl, hv⟩)
  | @eq_symm Γ Δ t₁ t₂ hmem _ ih =>
    intro M _ v ρ hΓf hΔf hv
    have hf := hΓf _ hmem
    simp only [isForm, Bool.and_eq_true] at hf
    exact ih v ρ (List.forall_mem_cons.mpr ⟨by simp [isForm, hf.1, hf.2], hΓf⟩) hΔf
      (List.forall_mem_cons.mpr ⟨(hv _ hmem).symm, hv⟩)
  | @eq_trans Γ Δ t₁ t₂ t₃ h₁ h₂ _ ih =>
    intro M _ v ρ hΓf hΔf hv
    have hf₁ := hΓf _ h₁; have hf₂ := hΓf _ h₂
    simp only [isForm, Bool.and_eq_true] at hf₁ hf₂
    exact ih v ρ (List.forall_mem_cons.mpr ⟨by simp [isForm, hf₁.1, hf₂.2], hΓf⟩) hΔf
      (List.forall_mem_cons.mpr ⟨(hv _ h₁).trans (hv _ h₂), hv⟩)
  | @eq_neg Γ Δ s t hmem _ ih =>
    intro M _ v ρ hΓf hΔf hv
    have hf := hΓf _ hmem
    simp only [isForm, Bool.and_eq_true] at hf
    refine ih v ρ (List.forall_mem_cons.mpr ⟨by simp [isForm, isFormTerm, hf.1, hf.2], hΓf⟩) hΔf
      (List.forall_mem_cons.mpr ⟨?_, hv⟩)
    simp [evalForm, evalTerm, show evalTerm v ρ s = evalTerm v ρ t from hv _ hmem]
  | @eq_add Γ Δ s₁ t₁ s₂ t₂ h₁ h₂ _ ih =>
    intro M _ v ρ hΓf hΔf hv
    have hf₁ := hΓf _ h₁; have hf₂ := hΓf _ h₂
    simp only [isForm, Bool.and_eq_true] at hf₁ hf₂
    refine ih v ρ
      (List.forall_mem_cons.mpr ⟨by simp [isForm, isFormTerm, hf₁.1, hf₁.2, hf₂.1, hf₂.2], hΓf⟩)
      hΔf (List.forall_mem_cons.mpr ⟨?_, hv⟩)
    simp [evalForm, evalTerm, show evalTerm v ρ s₁ = evalTerm v ρ t₁ from hv _ h₁,
      show evalTerm v ρ s₂ = evalTerm v ρ t₂ from hv _ h₂]
  | @eq_mul Γ Δ s₁ t₁ s₂ t₂ h₁ h₂ _ ih =>
    intro M _ v ρ hΓf hΔf hv
    have hf₁ := hΓf _ h₁; have hf₂ := hΓf _ h₂
    simp only [isForm, Bool.and_eq_true] at hf₁ hf₂
    refine ih v ρ
      (List.forall_mem_cons.mpr ⟨by simp [isForm, isFormTerm, hf₁.1, hf₁.2, hf₂.1, hf₂.2], hΓf⟩)
      hΔf (List.forall_mem_cons.mpr ⟨?_, hv⟩)
    simp [evalForm, evalTerm, show evalTerm v ρ s₁ = evalTerm v ρ t₁ from hv _ h₁,
      show evalTerm v ρ s₂ = evalTerm v ρ t₂ from hv _ h₂]
  | @eq_le Γ Δ s₁ t₁ s₂ t₂ h₁ h₂ hle _ ih =>
    intro M _ v ρ hΓf hΔf hv
    have hf₁ := hΓf _ h₁; have hf₂ := hΓf _ h₂
    simp only [isForm, Bool.and_eq_true] at hf₁ hf₂
    refine ih v ρ
      (List.forall_mem_cons.mpr ⟨by simp [isForm, hf₁.2, hf₂.2], hΓf⟩)
      hΔf (List.forall_mem_cons.mpr ⟨?_, hv⟩)
    have hrel : Structure.RelMap (L := LO) (Sum.inr orderRel.le) ![evalTerm v ρ s₁, evalTerm v ρ s₂] :=
      hv _ hle
    simpa [evalForm, show evalTerm v ρ s₁ = evalTerm v ρ t₁ from hv _ h₁,
      show evalTerm v ρ s₂ = evalTerm v ρ t₂ from hv _ h₂] using hrel

/- ### 7. Completeness of `Deriv` via fair Hintikka tree + quotient term model -/

noncomputable def satStep (n : ℕ) (Γ Δ : List OForm) : List OForm × List OForm :=
  let code := (Nat.unpair n).1
  let tag := code % 11
  let arg := code / 11
  match tag with
  | 0 =>
    match decOForm arg with
    | some (.imp φ ψ) =>
      if .imp φ ψ ∈ Γ then
        if Classical.propDecidable (Deriv Γ (φ :: Δ)) |>.decide then (ψ :: Γ, Δ)
        else (Γ, φ :: Δ)
      else (Γ, Δ)
    | _ => (Γ, Δ)
  | 1 =>
    match decOForm arg with
    | some (.imp φ ψ) => if .imp φ ψ ∈ Δ then (φ :: Γ, ψ :: Δ) else (Γ, Δ)
    | _ => (Γ, Δ)
  | 2 =>
    let p := Nat.unpair arg
    match decOForm p.1, decOTerm p.2 with
    | some (.all φ), some t =>
      if .all φ ∈ Γ ∧ noBVar t = true then (substForm0 t φ :: Γ, Δ) else (Γ, Δ)
    | _, _ => (Γ, Δ)
  | 3 =>
    match decOForm arg with
    | some (.all φ) =>
      if .all φ ∈ Δ then
        let c := max (maxVarList Γ) (maxVarList Δ)
        (Γ, substForm0 (.fvar c) φ :: Δ)
      else (Γ, Δ)
    | _ => (Γ, Δ)
  | 4 =>
    match decOTerm arg with
    | some t => if noBVar t = true then (.eq t t :: Γ, Δ) else (Γ, Δ)
    | _ => (Γ, Δ)
  | 5 =>
    match decOForm arg with
    | some (.eq t₁ t₂) => if .eq t₁ t₂ ∈ Γ then (.eq t₂ t₁ :: Γ, Δ) else (Γ, Δ)
    | _ => (Γ, Δ)
  | 6 =>
    let p := Nat.unpair arg
    match decOForm p.1, decOForm p.2 with
    | some (.eq t₁ t₂), some (.eq t₂' t₃) =>
      if t₂ = t₂' ∧ .eq t₁ t₂ ∈ Γ ∧ .eq t₂' t₃ ∈ Γ then (.eq t₁ t₃ :: Γ, Δ) else (Γ, Δ)
    | _, _ => (Γ, Δ)
  | 7 =>
    match decOForm arg with
    | some (.eq s t) => if .eq s t ∈ Γ then (.eq (.neg s) (.neg t) :: Γ, Δ) else (Γ, Δ)
    | _ => (Γ, Δ)
  | 8 =>
    let p := Nat.unpair arg
    match decOForm p.1, decOForm p.2 with
    | some (.eq s₁ t₁), some (.eq s₂ t₂) =>
      if .eq s₁ t₁ ∈ Γ ∧ .eq s₂ t₂ ∈ Γ then (.eq (.add s₁ s₂) (.add t₁ t₂) :: Γ, Δ) else (Γ, Δ)
    | _, _ => (Γ, Δ)
  | 9 =>
    let p := Nat.unpair arg
    match decOForm p.1, decOForm p.2 with
    | some (.eq s₁ t₁), some (.eq s₂ t₂) =>
      if .eq s₁ t₁ ∈ Γ ∧ .eq s₂ t₂ ∈ Γ then (.eq (.mul s₁ s₂) (.mul t₁ t₂) :: Γ, Δ) else (Γ, Δ)
    | _, _ => (Γ, Δ)
  | _ =>
    let p := Nat.unpair arg
    let q := Nat.unpair p.2
    match decOForm p.1, decOForm q.1, decOForm q.2 with
    | some (.eq s₁ t₁), some (.eq s₂ t₂), some (.le s₁' s₂') =>
      if s₁ = s₁' ∧ s₂ = s₂' ∧ .eq s₁ t₁ ∈ Γ ∧ .eq s₂ t₂ ∈ Γ ∧ .le s₁' s₂' ∈ Γ then
        (.le t₁ t₂ :: Γ, Δ)
      else (Γ, Δ)
    | _, _, _ => (Γ, Δ)

noncomputable def satSeq (Γ₀ : List OForm) : ℕ → List OForm × List OForm
  | 0 => (Γ₀, [])
  | n + 1 => satStep n (satSeq Γ₀ n).1 (satSeq Γ₀ n).2

lemma satStep_sub (n : ℕ) (Γ Δ : List OForm) :
    (∀ φ ∈ Γ, φ ∈ (satStep n Γ Δ).1) ∧ (∀ ψ ∈ Δ, ψ ∈ (satStep n Γ Δ).2) := by
  unfold satStep
  dsimp only
  split <;>
    repeat (first | split | exact ⟨fun _ h => h, fun _ h => h⟩ |
      exact ⟨fun _ h => List.mem_cons_of_mem _ h, fun _ h => h⟩ |
      exact ⟨fun _ h => h, fun _ h => List.mem_cons_of_mem _ h⟩ |
      exact ⟨fun _ h => List.mem_cons_of_mem _ h, fun _ h => List.mem_cons_of_mem _ h⟩)

lemma satSeq_mono (Γ₀ : List OForm) {m n : ℕ} (h : m ≤ n) :
    (∀ φ ∈ (satSeq Γ₀ m).1, φ ∈ (satSeq Γ₀ n).1) ∧
    (∀ ψ ∈ (satSeq Γ₀ m).2, ψ ∈ (satSeq Γ₀ n).2) := by
  induction h with
  | refl => exact ⟨fun _ h => h, fun _ h => h⟩
  | @step k _ ih =>
    have hs := satStep_sub k (satSeq Γ₀ k).1 (satSeq Γ₀ k).2
    exact ⟨fun φ hφ => hs.1 φ (ih.1 φ hφ), fun ψ hψ => hs.2 ψ (ih.2 ψ hψ)⟩

lemma satStep_unprovable (n : ℕ) {Γ Δ : List OForm} (hnd : ¬ Deriv Γ Δ) :
    ¬ Deriv (satStep n Γ Δ).1 (satStep n Γ Δ).2 := by
  classical
  unfold satStep
  dsimp only
  split
  · split
    · split_ifs with hmem hd
      · intro h2
        rw [decide_eq_true_eq] at hd
        exact hnd (Deriv.imp_L hmem hd h2)
      · intro h1
        simp [h1] at hd
      · exact hnd
    · exact hnd
  · split
    · split_ifs with hmem
      · exact fun h => hnd (Deriv.imp_R hmem h)
      · exact hnd
    · exact hnd
  · split
    · split_ifs with hcond
      · exact fun h => hnd (Deriv.all_L hcond.1 hcond.2 h)
      · exact hnd
    · exact hnd
  · split
    · split_ifs with hmem
      · refine fun h => hnd (Deriv.all_R hmem ?_ ?_ h)
        · intro ψ hψ
          exact freshInForm_of_ge_maxVarForm ((maxVarForm_le_maxVarList hψ).trans (le_max_left _ _))
        · intro ψ hψ
          exact freshInForm_of_ge_maxVarForm ((maxVarForm_le_maxVarList hψ).trans (le_max_right _ _))
      · exact hnd
    · exact hnd
  · split
    · split_ifs with ht
      · exact fun h => hnd (Deriv.eq_refl ht h)
      · exact hnd
    · exact hnd
  · split
    · split_ifs with hmem
      · exact fun h => hnd (Deriv.eq_symm hmem h)
      · exact hnd
    · exact hnd
  · split
    · split_ifs with hcond
      · rcases hcond with ⟨rfl, h1, h2⟩
        exact fun h => hnd (Deriv.eq_trans h1 h2 h)
      · exact hnd
    · exact hnd
  · split
    · split_ifs with hmem
      · exact fun h => hnd (Deriv.eq_neg hmem h)
      · exact hnd
    · exact hnd
  · split
    · split_ifs with hcond
      · exact fun h => hnd (Deriv.eq_add hcond.1 hcond.2 h)
      · exact hnd
    · exact hnd
  · split
    · split_ifs with hcond
      · exact fun h => hnd (Deriv.eq_mul hcond.1 hcond.2 h)
      · exact hnd
    · exact hnd
  · split
    · split_ifs with hcond
      · rcases hcond with ⟨rfl, rfl, h1, h2, h3⟩
        exact fun h => hnd (Deriv.eq_le h1 h2 h3 h)
      · exact hnd
    · exact hnd

lemma satSeq_unprovable {Γ₀ : List OForm} (hnd : ¬ Deriv Γ₀ []) (n : ℕ) :
    ¬ Deriv (satSeq Γ₀ n).1 (satSeq Γ₀ n).2 := by
  induction n with
  | zero => exact hnd
  | succ n ih => exact satStep_unprovable n ih

lemma satStep_isForm (n : ℕ) {Γ Δ : List OForm}
    (hΓ : ∀ φ ∈ Γ, isForm 0 φ = true) (hΔ : ∀ ψ ∈ Δ, isForm 0 ψ = true) :
    (∀ φ ∈ (satStep n Γ Δ).1, isForm 0 φ = true) ∧
    (∀ ψ ∈ (satStep n Γ Δ).2, isForm 0 ψ = true) := by
  unfold satStep
  dsimp only
  split
  · split
    · split_ifs with hmem _
      · have hf := hΓ _ hmem; simp only [isForm, Bool.and_eq_true] at hf
        exact ⟨List.forall_mem_cons.mpr ⟨hf.2, hΓ⟩, hΔ⟩
      · have hf := hΓ _ hmem; simp only [isForm, Bool.and_eq_true] at hf
        exact ⟨hΓ, List.forall_mem_cons.mpr ⟨hf.1, hΔ⟩⟩
      · exact ⟨hΓ, hΔ⟩
    · exact ⟨hΓ, hΔ⟩
  · split
    · split_ifs with hmem
      · have hf := hΔ _ hmem; simp only [isForm, Bool.and_eq_true] at hf
        exact ⟨List.forall_mem_cons.mpr ⟨hf.1, hΓ⟩, List.forall_mem_cons.mpr ⟨hf.2, hΔ⟩⟩
      · exact ⟨hΓ, hΔ⟩
    · exact ⟨hΓ, hΔ⟩
  · split
    · split_ifs with hcond
      · have hf : isForm 1 _ = true := hΓ _ hcond.1
        exact ⟨List.forall_mem_cons.mpr ⟨isForm_substForm0 hcond.2 hf, hΓ⟩, hΔ⟩
      · exact ⟨hΓ, hΔ⟩
    · exact ⟨hΓ, hΔ⟩
  · split
    · split_ifs with hmem
      · have hf : isForm 1 _ = true := hΔ _ hmem
        exact ⟨hΓ, List.forall_mem_cons.mpr ⟨isForm_substForm0 (by rfl) hf, hΔ⟩⟩
      · exact ⟨hΓ, hΔ⟩
    · exact ⟨hΓ, hΔ⟩
  · split
    · split_ifs with ht
      · have hft := isFormTerm_of_noBVar ht 0
        exact ⟨List.forall_mem_cons.mpr ⟨by simp [isForm, hft], hΓ⟩, hΔ⟩
      · exact ⟨hΓ, hΔ⟩
    · exact ⟨hΓ, hΔ⟩
  · split
    · split_ifs with hmem
      · have hf := hΓ _ hmem; simp only [isForm, Bool.and_eq_true] at hf
        exact ⟨List.forall_mem_cons.mpr ⟨by simp [isForm, hf.1, hf.2], hΓ⟩, hΔ⟩
      · exact ⟨hΓ, hΔ⟩
    · exact ⟨hΓ, hΔ⟩
  · split
    · split_ifs with hcond
      · have hf1 := hΓ _ hcond.2.1; have hf2 := hΓ _ hcond.2.2
        simp only [isForm, Bool.and_eq_true] at hf1 hf2
        exact ⟨List.forall_mem_cons.mpr ⟨by simp [isForm, hf1.1, hf2.2], hΓ⟩, hΔ⟩
      · exact ⟨hΓ, hΔ⟩
    · exact ⟨hΓ, hΔ⟩
  · split
    · split_ifs with hmem
      · have hf := hΓ _ hmem; simp only [isForm, Bool.and_eq_true] at hf
        exact ⟨List.forall_mem_cons.mpr ⟨by simp [isForm, isFormTerm, hf.1, hf.2], hΓ⟩, hΔ⟩
      · exact ⟨hΓ, hΔ⟩
    · exact ⟨hΓ, hΔ⟩
  · split
    · split_ifs with hcond
      · have hf1 := hΓ _ hcond.1; have hf2 := hΓ _ hcond.2
        simp only [isForm, Bool.and_eq_true] at hf1 hf2
        exact ⟨List.forall_mem_cons.mpr ⟨by simp [isForm, isFormTerm, hf1.1, hf1.2, hf2.1, hf2.2], hΓ⟩, hΔ⟩
      · exact ⟨hΓ, hΔ⟩
    · exact ⟨hΓ, hΔ⟩
  · split
    · split_ifs with hcond
      · have hf1 := hΓ _ hcond.1; have hf2 := hΓ _ hcond.2
        simp only [isForm, Bool.and_eq_true] at hf1 hf2
        exact ⟨List.forall_mem_cons.mpr ⟨by simp [isForm, isFormTerm, hf1.1, hf1.2, hf2.1, hf2.2], hΓ⟩, hΔ⟩
      · exact ⟨hΓ, hΔ⟩
    · exact ⟨hΓ, hΔ⟩
  · split
    · split_ifs with hcond
      · have hf1 := hΓ _ hcond.2.2.1; have hf2 := hΓ _ hcond.2.2.2.1
        simp only [isForm, Bool.and_eq_true] at hf1 hf2
        exact ⟨List.forall_mem_cons.mpr ⟨by simp [isForm, hf1.2, hf2.2], hΓ⟩, hΔ⟩
      · exact ⟨hΓ, hΔ⟩
    · exact ⟨hΓ, hΔ⟩

lemma satSeq_isForm {Γ₀ : List OForm} (hΓ₀ : ∀ φ ∈ Γ₀, isForm 0 φ = true) (n : ℕ) :
    (∀ φ ∈ (satSeq Γ₀ n).1, isForm 0 φ = true) ∧
    (∀ ψ ∈ (satSeq Γ₀ n).2, isForm 0 ψ = true) := by
  induction n with
  | zero => exact ⟨hΓ₀, fun _ h => by cases h⟩
  | succ n ih => exact satStep_isForm n ih.1 ih.2

theorem deriv_complete {Γ₀ : List OForm}
    (hΓ₀ : ∀ φ ∈ Γ₀, isForm 0 φ = true) (hnd : ¬ Deriv Γ₀ []) :
    ∃ (M : Type) (_ : Nonempty M) (_ : LO.Structure M) (v ρ : ℕ → M),
      ∀ φ ∈ Γ₀, evalForm v 0 ρ φ := by
  let inL (φ : OForm) : Prop := ∃ n, φ ∈ (satSeq Γ₀ n).1
  let inR (φ : OForm) : Prop := ∃ n, φ ∈ (satSeq Γ₀ n).2
  have hdisj : ∀ φ, inL φ → inR φ → False := by
    rintro φ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩
    have hm₁ := (satSeq_mono Γ₀ (le_max_left n₁ n₂)).1 φ h₁
    have hm₂ := (satSeq_mono Γ₀ (le_max_right n₁ n₂)).2 φ h₂
    exact satSeq_unprovable hnd (max n₁ n₂) (Deriv.ax_id hm₁ hm₂)
  have hnobot : ¬ inL .bot := by
    rintro ⟨n, hn⟩
    exact satSeq_unprovable hnd n (Deriv.ax_bot hn)
  have himpL : ∀ φ ψ, inL (.imp φ ψ) → inR φ ∨ inL ψ := by
    rintro φ ψ ⟨m, hm⟩
    let code := 11 * encOForm (.imp φ ψ) + 0
    let n := Nat.pair code m
    have hmn : m ≤ n := Nat.right_le_pair code m
    have hmem : .imp φ ψ ∈ (satSeq Γ₀ n).1 := (satSeq_mono Γ₀ hmn).1 _ hm
    have hstep : satSeq Γ₀ (n + 1) = satStep n (satSeq Γ₀ n).1 (satSeq Γ₀ n).2 := rfl
    have hcode : (Nat.unpair n).1 = code := by simp [n]
    have htag : code % 11 = 0 := by omega
    have harg : code / 11 = encOForm (.imp φ ψ) := by omega
    simp only [satStep, hcode, htag, harg, decOForm_encOForm, hmem, ↓reduceIte] at hstep
    split_ifs at hstep
    · exact Or.inr ⟨n + 1, by rw [hstep]; simp⟩
    · exact Or.inl ⟨n + 1, by rw [hstep]; simp⟩
  have himpR : ∀ φ ψ, inR (.imp φ ψ) → inL φ ∧ inR ψ := by
    rintro φ ψ ⟨m, hm⟩
    let code := 11 * encOForm (.imp φ ψ) + 1
    let n := Nat.pair code m
    have hmn : m ≤ n := Nat.right_le_pair code m
    have hmem : .imp φ ψ ∈ (satSeq Γ₀ n).2 := (satSeq_mono Γ₀ hmn).2 _ hm
    have hstep : satSeq Γ₀ (n + 1) = satStep n (satSeq Γ₀ n).1 (satSeq Γ₀ n).2 := rfl
    have hcode : (Nat.unpair n).1 = code := by simp [n]
    have htag : code % 11 = 1 := by omega
    have harg : code / 11 = encOForm (.imp φ ψ) := by omega
    simp only [satStep, hcode, htag, harg, decOForm_encOForm, hmem, ↓reduceIte] at hstep
    exact ⟨⟨n + 1, by rw [hstep]; simp⟩, ⟨n + 1, by rw [hstep]; simp⟩⟩
  have hallL : ∀ φ t, inL (.all φ) → noBVar t = true → inL (substForm0 t φ) := by
    rintro φ t ⟨m, hm⟩ ht
    let code := 11 * Nat.pair (encOForm (.all φ)) (encOTerm t) + 2
    let n := Nat.pair code m
    have hmn : m ≤ n := Nat.right_le_pair code m
    have hmem : .all φ ∈ (satSeq Γ₀ n).1 := (satSeq_mono Γ₀ hmn).1 _ hm
    have hstep : satSeq Γ₀ (n + 1) = satStep n (satSeq Γ₀ n).1 (satSeq Γ₀ n).2 := rfl
    have hcode : (Nat.unpair n).1 = code := by simp [n]
    have htag : code % 11 = 2 := by omega
    have harg : code / 11 = Nat.pair (encOForm (.all φ)) (encOTerm t) := by omega
    simp only [satStep, hcode, htag, harg, Nat.unpair_pair, decOForm_encOForm, decOTerm_encOTerm,
      hmem, ht, and_self, ↓reduceIte] at hstep
    exact ⟨n + 1, by rw [hstep]; simp⟩
  have hallR : ∀ φ, inR (.all φ) → ∃ c : ℕ, inR (substForm0 (.fvar c) φ) := by
    rintro φ ⟨m, hm⟩
    let code := 11 * encOForm (.all φ) + 3
    let n := Nat.pair code m
    have hmn : m ≤ n := Nat.right_le_pair code m
    have hmem : .all φ ∈ (satSeq Γ₀ n).2 := (satSeq_mono Γ₀ hmn).2 _ hm
    have hstep : satSeq Γ₀ (n + 1) = satStep n (satSeq Γ₀ n).1 (satSeq Γ₀ n).2 := rfl
    have hcode : (Nat.unpair n).1 = code := by simp [n]
    have htag : code % 11 = 3 := by omega
    have harg : code / 11 = encOForm (.all φ) := by omega
    simp only [satStep, hcode, htag, harg, decOForm_encOForm, hmem, ↓reduceIte] at hstep
    exact ⟨max (maxVarList (satSeq Γ₀ n).1) (maxVarList (satSeq Γ₀ n).2),
      ⟨n + 1, by rw [hstep]; simp⟩⟩
  have heqRefl : ∀ t, noBVar t = true → inL (.eq t t) := by
    intro t ht
    let code := 11 * encOTerm t + 4
    let n := Nat.pair code 0
    have hstep : satSeq Γ₀ (n + 1) = satStep n (satSeq Γ₀ n).1 (satSeq Γ₀ n).2 := rfl
    have hcode : (Nat.unpair n).1 = code := by simp [n]
    have htag : code % 11 = 4 := by omega
    have harg : code / 11 = encOTerm t := by omega
    simp only [satStep, hcode, htag, harg, decOTerm_encOTerm, ht, ↓reduceIte] at hstep
    exact ⟨n + 1, by rw [hstep]; simp⟩
  have heqSymm : ∀ t₁ t₂, inL (.eq t₁ t₂) → inL (.eq t₂ t₁) := by
    rintro t₁ t₂ ⟨m, hm⟩
    let code := 11 * encOForm (.eq t₁ t₂) + 5
    let n := Nat.pair code m
    have hmem : .eq t₁ t₂ ∈ (satSeq Γ₀ n).1 := (satSeq_mono Γ₀ (Nat.right_le_pair code m)).1 _ hm
    have hstep : satSeq Γ₀ (n + 1) = satStep n (satSeq Γ₀ n).1 (satSeq Γ₀ n).2 := rfl
    have hcode : (Nat.unpair n).1 = code := by simp [n]
    have htag : code % 11 = 5 := by omega
    have harg : code / 11 = encOForm (.eq t₁ t₂) := by omega
    simp only [satStep, hcode, htag, harg, decOForm_encOForm, hmem, ↓reduceIte] at hstep
    exact ⟨n + 1, by rw [hstep]; simp⟩
  have heqTrans : ∀ t₁ t₂ t₃, inL (.eq t₁ t₂) → inL (.eq t₂ t₃) → inL (.eq t₁ t₃) := by
    rintro t₁ t₂ t₃ ⟨m₁, h₁⟩ ⟨m₂, h₂⟩
    let m := max m₁ m₂
    let code := 11 * Nat.pair (encOForm (.eq t₁ t₂)) (encOForm (.eq t₂ t₃)) + 6
    let n := Nat.pair code m
    have hm₁ : .eq t₁ t₂ ∈ (satSeq Γ₀ n).1 :=
      (satSeq_mono Γ₀ ((le_max_left m₁ m₂).trans (Nat.right_le_pair code m))).1 _ h₁
    have hm₂ : .eq t₂ t₃ ∈ (satSeq Γ₀ n).1 :=
      (satSeq_mono Γ₀ ((le_max_right m₁ m₂).trans (Nat.right_le_pair code m))).1 _ h₂
    have hstep : satSeq Γ₀ (n + 1) = satStep n (satSeq Γ₀ n).1 (satSeq Γ₀ n).2 := rfl
    have hcode : (Nat.unpair n).1 = code := by simp [n]
    have htag : code % 11 = 6 := by omega
    have harg : code / 11 = Nat.pair (encOForm (.eq t₁ t₂)) (encOForm (.eq t₂ t₃)) := by omega
    simp only [satStep, hcode, htag, harg, Nat.unpair_pair, decOForm_encOForm,
      hm₁, hm₂, and_self, ↓reduceIte] at hstep
    exact ⟨n + 1, by rw [hstep]; simp⟩
  have heqNeg : ∀ s t, inL (.eq s t) → inL (.eq (.neg s) (.neg t)) := by
    rintro s t ⟨m, hm⟩
    let code := 11 * encOForm (.eq s t) + 7
    let n := Nat.pair code m
    have hmem : .eq s t ∈ (satSeq Γ₀ n).1 := (satSeq_mono Γ₀ (Nat.right_le_pair code m)).1 _ hm
    have hstep : satSeq Γ₀ (n + 1) = satStep n (satSeq Γ₀ n).1 (satSeq Γ₀ n).2 := rfl
    have hcode : (Nat.unpair n).1 = code := by simp [n]
    have htag : code % 11 = 7 := by omega
    have harg : code / 11 = encOForm (.eq s t) := by omega
    simp only [satStep, hcode, htag, harg, decOForm_encOForm, hmem, ↓reduceIte] at hstep
    exact ⟨n + 1, by rw [hstep]; simp⟩
  have heqAdd : ∀ s₁ t₁ s₂ t₂, inL (.eq s₁ t₁) → inL (.eq s₂ t₂) →
      inL (.eq (.add s₁ s₂) (.add t₁ t₂)) := by
    rintro s₁ t₁ s₂ t₂ ⟨m₁, h₁⟩ ⟨m₂, h₂⟩
    let m := max m₁ m₂
    let code := 11 * Nat.pair (encOForm (.eq s₁ t₁)) (encOForm (.eq s₂ t₂)) + 8
    let n := Nat.pair code m
    have hm₁ : .eq s₁ t₁ ∈ (satSeq Γ₀ n).1 :=
      (satSeq_mono Γ₀ ((le_max_left m₁ m₂).trans (Nat.right_le_pair code m))).1 _ h₁
    have hm₂ : .eq s₂ t₂ ∈ (satSeq Γ₀ n).1 :=
      (satSeq_mono Γ₀ ((le_max_right m₁ m₂).trans (Nat.right_le_pair code m))).1 _ h₂
    have hstep : satSeq Γ₀ (n + 1) = satStep n (satSeq Γ₀ n).1 (satSeq Γ₀ n).2 := rfl
    have hcode : (Nat.unpair n).1 = code := by simp [n]
    have htag : code % 11 = 8 := by omega
    have harg : code / 11 = Nat.pair (encOForm (.eq s₁ t₁)) (encOForm (.eq s₂ t₂)) := by omega
    simp only [satStep, hcode, htag, harg, Nat.unpair_pair, decOForm_encOForm,
      hm₁, hm₂, and_self, ↓reduceIte] at hstep
    exact ⟨n + 1, by rw [hstep]; simp⟩
  have heqMul : ∀ s₁ t₁ s₂ t₂, inL (.eq s₁ t₁) → inL (.eq s₂ t₂) →
      inL (.eq (.mul s₁ s₂) (.mul t₁ t₂)) := by
    rintro s₁ t₁ s₂ t₂ ⟨m₁, h₁⟩ ⟨m₂, h₂⟩
    let m := max m₁ m₂
    let code := 11 * Nat.pair (encOForm (.eq s₁ t₁)) (encOForm (.eq s₂ t₂)) + 9
    let n := Nat.pair code m
    have hm₁ : .eq s₁ t₁ ∈ (satSeq Γ₀ n).1 :=
      (satSeq_mono Γ₀ ((le_max_left m₁ m₂).trans (Nat.right_le_pair code m))).1 _ h₁
    have hm₂ : .eq s₂ t₂ ∈ (satSeq Γ₀ n).1 :=
      (satSeq_mono Γ₀ ((le_max_right m₁ m₂).trans (Nat.right_le_pair code m))).1 _ h₂
    have hstep : satSeq Γ₀ (n + 1) = satStep n (satSeq Γ₀ n).1 (satSeq Γ₀ n).2 := rfl
    have hcode : (Nat.unpair n).1 = code := by simp [n]
    have htag : code % 11 = 9 := by omega
    have harg : code / 11 = Nat.pair (encOForm (.eq s₁ t₁)) (encOForm (.eq s₂ t₂)) := by omega
    simp only [satStep, hcode, htag, harg, Nat.unpair_pair, decOForm_encOForm,
      hm₁, hm₂, and_self, ↓reduceIte] at hstep
    exact ⟨n + 1, by rw [hstep]; simp⟩
  have heqLe : ∀ s₁ t₁ s₂ t₂, inL (.eq s₁ t₁) → inL (.eq s₂ t₂) → inL (.le s₁ s₂) →
      inL (.le t₁ t₂) := by
    rintro s₁ t₁ s₂ t₂ ⟨m₁, h₁⟩ ⟨m₂, h₂⟩ ⟨m₃, h₃⟩
    let m := max (max m₁ m₂) m₃
    let code := 11 * Nat.pair (encOForm (.eq s₁ t₁))
      (Nat.pair (encOForm (.eq s₂ t₂)) (encOForm (.le s₁ s₂))) + 10
    let n := Nat.pair code m
    have hm₁ : .eq s₁ t₁ ∈ (satSeq Γ₀ n).1 :=
      (satSeq_mono Γ₀ (((le_max_left m₁ m₂).trans (le_max_left _ m₃)).trans
        (Nat.right_le_pair code m))).1 _ h₁
    have hm₂ : .eq s₂ t₂ ∈ (satSeq Γ₀ n).1 :=
      (satSeq_mono Γ₀ (((le_max_right m₁ m₂).trans (le_max_left _ m₃)).trans
        (Nat.right_le_pair code m))).1 _ h₂
    have hm₃ : .le s₁ s₂ ∈ (satSeq Γ₀ n).1 :=
      (satSeq_mono Γ₀ ((le_max_right _ m₃).trans (Nat.right_le_pair code m))).1 _ h₃
    have hstep : satSeq Γ₀ (n + 1) = satStep n (satSeq Γ₀ n).1 (satSeq Γ₀ n).2 := rfl
    have hcode : (Nat.unpair n).1 = code := by simp [n]
    have htag : code % 11 = 10 := by omega
    have harg : code / 11 = Nat.pair (encOForm (.eq s₁ t₁))
      (Nat.pair (encOForm (.eq s₂ t₂)) (encOForm (.le s₁ s₂))) := by omega
    simp only [satStep, hcode, htag, harg, Nat.unpair_pair, decOForm_encOForm,
      hm₁, hm₂, hm₃, and_self, ↓reduceIte] at hstep
    exact ⟨n + 1, by rw [hstep]; simp⟩
  -- Quotient term model on closed-in-bound-vars terms `{t : OTerm // noBVar t = true}`
  let GTerm := {t : OTerm // noBVar t = true}
  let S : Setoid GTerm :=
    { r := fun x y => inL (.eq x.1 y.1)
      iseqv := ⟨fun x => heqRefl x.1 x.2, fun h => heqSymm _ _ h, fun h₁ h₂ => heqTrans _ _ _ h₁ h₂⟩ }
  let M : Type := Quotient S
  let mkM (t : OTerm) (ht : noBVar t = true) : M := Quotient.mk S ⟨t, ht⟩
  have hM_ne : Nonempty M := ⟨mkM .zero rfl⟩
  let negM : M → M := Quotient.lift (fun x => mkM (.neg x.1) x.2) fun _ _ h =>
    Quotient.sound (heqNeg _ _ h)
  let addM : M → M → M := Quotient.lift₂ (fun x y => mkM (.add x.1 y.1) (by simp [noBVar, x.2, y.2]))
    fun _ _ _ _ h₁ h₂ => Quotient.sound (heqAdd _ _ _ _ h₁ h₂)
  let mulM : M → M → M := Quotient.lift₂ (fun x y => mkM (.mul x.1 y.1) (by simp [noBVar, x.2, y.2]))
    fun _ _ _ _ h₁ h₂ => Quotient.sound (heqMul _ _ _ _ h₁ h₂)
  let leM : M → M → Prop := Quotient.lift₂ (fun x y => inL (.le x.1 y.1))
    fun _ _ _ _ h₁ h₂ => propext ⟨fun h => heqLe _ _ _ _ h₁ h₂ h,
      fun h => heqLe _ _ _ _ (heqSymm _ _ h₁) (heqSymm _ _ h₂) h⟩
  let strM : LO.Structure M :=
    { funMap := fun f xs =>
        match f with
        | .inl .zero => mkM .zero rfl
        | .inl .one => mkM .one rfl
        | .inl .neg => negM (xs 0)
        | .inl .add => addM (xs 0) (xs 1)
        | .inl .mul => mulM (xs 0) (xs 1)
        | .inr e => Empty.elim e
      RelMap := fun R xs =>
        match R with
        | .inl e => Empty.elim e
        | .inr .le => leM (xs 0) (xs 1) }
  let v : ℕ → M := fun c => mkM (.fvar c) rfl
  let ρ : ℕ → M := fun _ => mkM .zero rfl
  have hevalTerm : ∀ (t : OTerm) (ht : noBVar t = true), evalTerm v ρ t = mkM t ht := by
    intro t
    induction t with
    | fvar c => intro _; rfl
    | bvar _ => intro h; simp [noBVar] at h
    | zero => intro _; rfl
    | one => intro _; rfl
    | neg t ih =>
      intro ht
      simp only [evalTerm, ih ht]
      rfl
    | add t₁ t₂ ih₁ ih₂ =>
      intro ht
      simp only [noBVar, Bool.and_eq_true] at ht
      simp only [evalTerm, ih₁ ht.1, ih₂ ht.2]
      rfl
    | mul t₁ t₂ ih₁ ih₂ =>
      intro ht
      simp only [noBVar, Bool.and_eq_true] at ht
      simp only [evalTerm, ih₁ ht.1, ih₂ ht.2]
      rfl
  have htruth : ∀ (k : ℕ) (φ : OForm), formSize φ ≤ k →
      (inL φ → evalForm v 0 ρ φ) ∧ (inR φ → ¬ evalForm v 0 ρ φ) := by
    intro k
    induction k with
    | zero =>
      intro φ hk
      cases φ with
      | bot => exact ⟨fun h => False.elim (hnobot h), fun _ h => h⟩
      | eq t₁ t₂ =>
        constructor
        · intro h
          rcases h with ⟨n, hn⟩
          have hf := (satSeq_isForm hΓ₀ n).1 _ hn
          simp only [isForm, Bool.and_eq_true] at hf
          have ht₁ := noBVar_of_isFormTerm_zero hf.1
          have ht₂ := noBVar_of_isFormTerm_zero hf.2
          simp only [evalForm, hevalTerm t₁ ht₁, hevalTerm t₂ ht₂]
          exact Quotient.sound ⟨n, hn⟩
        · intro h hev
          rcases h with ⟨n, hn⟩
          have hf := (satSeq_isForm hΓ₀ n).2 _ hn
          simp only [isForm, Bool.and_eq_true] at hf
          have ht₁ := noBVar_of_isFormTerm_zero hf.1
          have ht₂ := noBVar_of_isFormTerm_zero hf.2
          simp only [evalForm, hevalTerm t₁ ht₁, hevalTerm t₂ ht₂] at hev
          exact hdisj _ (Quotient.exact hev) ⟨n, hn⟩
      | le t₁ t₂ =>
        constructor
        · intro h
          rcases h with ⟨n, hn⟩
          have hf := (satSeq_isForm hΓ₀ n).1 _ hn
          simp only [isForm, Bool.and_eq_true] at hf
          have ht₁ := noBVar_of_isFormTerm_zero hf.1
          have ht₂ := noBVar_of_isFormTerm_zero hf.2
          simp only [evalForm, hevalTerm t₁ ht₁, hevalTerm t₂ ht₂]
          exact ⟨n, hn⟩
        · intro h hev
          rcases h with ⟨n, hn⟩
          have hf := (satSeq_isForm hΓ₀ n).2 _ hn
          simp only [isForm, Bool.and_eq_true] at hf
          have ht₁ := noBVar_of_isFormTerm_zero hf.1
          have ht₂ := noBVar_of_isFormTerm_zero hf.2
          simp only [evalForm, hevalTerm t₁ ht₁, hevalTerm t₂ ht₂] at hev
          exact hdisj _ hev ⟨n, hn⟩
      | imp _ _ => simp [formSize] at hk
      | all _ => simp [formSize] at hk
    | succ k ih =>
      intro φ hk
      cases φ with
      | bot => exact ⟨fun h => False.elim (hnobot h), fun _ h => h⟩
      | eq t₁ t₂ => exact ih (.eq t₁ t₂) (by simp [formSize])
      | le t₁ t₂ => exact ih (.le t₁ t₂) (by simp [formSize])
      | imp φ₁ φ₂ =>
        simp only [formSize] at hk
        have ih₁ := ih φ₁ (by omega)
        have ih₂ := ih φ₂ (by omega)
        constructor
        · intro h h1
          rcases himpL φ₁ φ₂ h with hR | hL
          · exact False.elim (ih₁.2 hR h1)
          · exact ih₂.1 hL
        · intro h himp
          obtain ⟨hL, hR⟩ := himpR φ₁ φ₂ h
          exact ih₂.2 hR (himp (ih₁.1 hL))
      | all φ =>
        simp only [formSize] at hk
        constructor
        · intro h a
          rcases h with ⟨n, hn⟩
          have hφ1 : isForm 1 φ = true := (satSeq_isForm hΓ₀ n).1 _ hn
          refine Quotient.inductionOn a fun ⟨t, ht⟩ => ?_
          have hinst : inL (substForm0 t φ) := hallL φ t ⟨n, hn⟩ ht
          have hev : evalForm v 0 ρ (substForm0 t φ) :=
            (ih (substForm0 t φ) (by rw [formSize_substForm0]; omega)).1 hinst
          have := (evalForm_substForm0_zero ht hφ1).1 hev
          simpa [hevalTerm t ht] using this
        · intro h hall
          rcases h with ⟨n, hn⟩
          have hφ1 : isForm 1 φ = true := (satSeq_isForm hΓ₀ n).2 _ hn
          obtain ⟨c, hc⟩ := hallR φ ⟨n, hn⟩
          have hnev : ¬ evalForm v 0 ρ (substForm0 (.fvar c) φ) :=
            (ih (substForm0 (.fvar c) φ) (by rw [formSize_substForm0]; omega)).2 hc
          apply hnev
          rw [evalForm_substForm0_zero (by rfl) hφ1]
          exact hall (evalTerm v ρ (.fvar c))
  refine ⟨M, hM_ne, strM, v, ρ, fun φ hφ => (htruth (formSize φ) φ le_rfl).1 ⟨0, hφ⟩⟩

/- ### 8. Semantic consequence ↔ syntactic refutation (via Compactness) -/

theorem models_iff_exists_deriv (T : LO.Theory) (φ : LO.Sentence) :
    T ⊨ᵇ φ ↔
      ∃ (T₀ : List OForm),
        (∀ θ ∈ T₀, isSentForm 0 θ = true ∧ ∃ s ∈ T, ofMathlibForm s = θ) ∧
        Deriv (OForm.imp (ofMathlibForm φ) .bot :: T₀) [] := by
  constructor
  · intro hmod
    rw [Theory.models_iff_finset_models] at hmod
    obtain ⟨S, hST, hSmod⟩ := hmod
    let T₀ : List OForm := S.toList.map ofMathlibForm
    refine ⟨T₀, fun θ hθ => ?_, ?_⟩
    · simp only [T₀, List.mem_map, Finset.mem_toList] at hθ
      obtain ⟨s, hsS, rfl⟩ := hθ
      exact ⟨isSentForm_ofMathlibForm s, s, hST hsS, rfl⟩
    · by_contra hnd
      have hΓ₀ : ∀ ψ ∈ OForm.imp (ofMathlibForm φ) .bot :: T₀, isForm 0 ψ = true := by
        intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hmem
        · simp [isForm, isForm_of_isSentForm (isSentForm_ofMathlibForm φ)]
        · simp only [T₀, List.mem_map] at hmem
          obtain ⟨s, _, rfl⟩ := hmem
          exact isForm_of_isSentForm (isSentForm_ofMathlibForm s)
      obtain ⟨M, hMne, hMstr, v, ρ, hsat⟩ := deriv_complete hΓ₀ hnd
      let _ : Nonempty M := hMne
      let _ : LO.Structure M := hMstr
      have hMS : M ⊨ (S : LO.Theory) := by
        rw [Theory.model_iff]
        intro s hs
        have hmem : ofMathlibForm s ∈ OForm.imp (ofMathlibForm φ) .bot :: T₀ :=
          List.mem_cons_of_mem _ (List.mem_map_of_mem (Finset.mem_toList.2 hs))
        exact (evalForm_ofMathlibSentence s v ρ).1 (hsat _ hmem)
      have hMφ : M ⊨ φ := hSmod.realize_sentence M
      have hnotφ : evalForm v 0 ρ (OForm.imp (ofMathlibForm φ) .bot) :=
        hsat _ (List.mem_cons_self ..)
      exact hnotφ ((evalForm_ofMathlibSentence φ v ρ).2 hMφ)
  · rintro ⟨T₀, hT₀, hderiv⟩
    rw [Theory.models_sentence_iff]
    intro M
    have hΓ₀ : ∀ ψ ∈ OForm.imp (ofMathlibForm φ) .bot :: T₀, isForm 0 ψ = true := by
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hmem
      · simp [isForm, isForm_of_isSentForm (isSentForm_ofMathlibForm φ)]
      · exact isForm_of_isSentForm (hT₀ ψ hmem).1
    let a₀ : M := Classical.arbitrary M
    by_contra hnot
    have hv : ∀ ψ ∈ OForm.imp (ofMathlibForm φ) .bot :: T₀,
        evalForm (fun _ => a₀) 0 (fun _ => a₀) ψ := by
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hmem
      · intro h
        exact hnot ((evalForm_ofMathlibSentence φ (fun _ => a₀) (fun _ => a₀)).1 h)
      · obtain ⟨_, s, hsT, rfl⟩ := hT₀ ψ hmem
        exact (evalForm_ofMathlibSentence s (fun _ => a₀) (fun _ => a₀)).2
          (Theory.realize_sentence_of_mem T hsT)
    obtain ⟨_, hmem, _⟩ := deriv_sound hderiv (fun _ => a₀) (fun _ => a₀) hΓ₀ (fun _ h => by cases h) hv
    cases hmem

/- ### 9. `Primcodable` instances and `Primrec` for syntax operations -/

instance : Encodable OTerm := ⟨encOTerm, decOTerm, decOTerm_encOTerm⟩
instance : Encodable OForm := ⟨encOForm, decOForm, decOForm_encOForm⟩

lemma getD_map_range (f : ℕ → ℕ) {n k : ℕ} (hk : k < n) :
    ((List.range n).map f).getD k 0 = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

def gTermStep (L : List ℕ) : ℕ :=
  if L.length = 0 then 0
  else
    let m := L.length - 1
    let tag := (Nat.unpair m).1
    let val := (Nat.unpair m).2
    if tag = 0 then m + 2
    else if tag = 1 then m + 2
    else if tag = 2 then if val = 0 then m + 2 else 0
    else if tag = 3 then if val = 0 then m + 2 else 0
    else if tag = 4 then if L.getD val 0 = 0 then 0 else m + 2
    else if tag = 5 then
      if L.getD (Nat.unpair val).1 0 ≠ 0 ∧ L.getD (Nat.unpair val).2 0 ≠ 0 then m + 2 else 0
    else if tag = 6 then
      if L.getD (Nat.unpair val).1 0 ≠ 0 ∧ L.getD (Nat.unpair val).2 0 ≠ 0 then m + 2 else 0
    else 0

lemma primrec_gTermStep : Primrec gTermStep := by
  have hm : Primrec (fun L : List ℕ => L.length - 1) := Primrec.pred.comp Primrec.list_length
  have htag : Primrec (fun L : List ℕ => (Nat.unpair (L.length - 1)).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hm)
  have hval : Primrec (fun L : List ℕ => (Nat.unpair (L.length - 1)).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hm)
  have hm2 : Primrec (fun L : List ℕ => (L.length - 1) + 2) :=
    Primrec.succ.comp (Primrec.succ.comp hm)
  have hg0 : Primrec (fun L : List ℕ => L.getD (Nat.unpair (L.length - 1)).2 0) :=
    (Primrec.list_getD 0).comp .id hval
  have hgL : Primrec (fun L : List ℕ => L.getD (Nat.unpair (Nat.unpair (L.length - 1)).2).1 0) :=
    (Primrec.list_getD 0).comp .id (Primrec.fst.comp (Primrec.unpair.comp hval))
  have hgR : Primrec (fun L : List ℕ => L.getD (Nat.unpair (Nat.unpair (L.length - 1)).2).2 0) :=
    (Primrec.list_getD 0).comp .id (Primrec.snd.comp (Primrec.unpair.comp hval))
  have hboth : PrimrecPred (fun L : List ℕ =>
      L.getD (Nat.unpair (Nat.unpair (L.length - 1)).2).1 0 ≠ 0 ∧
      L.getD (Nat.unpair (Nat.unpair (L.length - 1)).2).2 0 ≠ 0) :=
    PrimrecPred.and (Primrec.eq.comp hgL (.const 0)).not (Primrec.eq.comp hgR (.const 0)).not
  unfold gTermStep
  exact Primrec.ite (Primrec.eq.comp Primrec.list_length (.const 0)) (.const 0)
    (Primrec.ite (Primrec.eq.comp htag (.const 0)) hm2
    (Primrec.ite (Primrec.eq.comp htag (.const 1)) hm2
    (Primrec.ite (Primrec.eq.comp htag (.const 2))
      (Primrec.ite (Primrec.eq.comp hval (.const 0)) hm2 (.const 0))
    (Primrec.ite (Primrec.eq.comp htag (.const 3))
      (Primrec.ite (Primrec.eq.comp hval (.const 0)) hm2 (.const 0))
    (Primrec.ite (Primrec.eq.comp htag (.const 4))
      (Primrec.ite (Primrec.eq.comp hg0 (.const 0)) (.const 0) hm2)
    (Primrec.ite (Primrec.eq.comp htag (.const 5))
      (Primrec.ite hboth hm2 (.const 0))
    (Primrec.ite (Primrec.eq.comp htag (.const 6))
      (Primrec.ite hboth hm2 (.const 0))
      (.const 0))))))))

lemma encode_decOTerm_eq_ite (n : ℕ) :
    Encodable.encode (decOTerm n) = if (decOTerm n).isSome then n + 1 else 0 := by
  cases h : decOTerm n with
  | none => rfl
  | some t =>
    simp [Encodable.encode_some, show Encodable.encode t = n from encOTerm_of_decOTerm h]

instance : Primcodable OTerm := by
  refine ⟨Primrec.nat_iff.1 ?_⟩
  have hrec : Primrec₂ (fun (_ : Unit) (n : ℕ) => Encodable.encode (decOTerm n)) := by
    refine Primrec.nat_strong_rec (fun (_ : Unit) n => Encodable.encode (decOTerm n))
      (g := fun _ L => some (gTermStep L))
      (Primrec.option_some.comp (primrec_gTermStep.comp .snd)) ?_
    intro _ n
    congr 1
    cases n with
    | zero => simp [gTermStep, decOTerm]
    | succ m =>
      have hlen : ((List.range (m + 1)).map (fun k => Encodable.encode (decOTerm k))).length = m + 1 := by
        simp
      have hval_lt : (Nat.unpair m).2 < m + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le m)
      have hvalL_lt : (Nat.unpair (Nat.unpair m).2).1 < m + 1 :=
        Nat.lt_succ_of_le ((Nat.unpair_left_le _).trans (Nat.unpair_right_le m))
      have hvalR_lt : (Nat.unpair (Nat.unpair m).2).2 < m + 1 :=
        Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le m))
      rw [encode_decOTerm_eq_ite]
      unfold gTermStep
      simp only [hlen, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel, decOTerm]
      rw [getD_map_range _ hval_lt, getD_map_range _ hvalL_lt, getD_map_range _ hvalR_lt]
      rcases (Nat.unpair m).1 with _ | _ | _ | _ | _ | _ | _ | tag
      · simp
      · simp
      · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
        by_cases hv : (Nat.unpair m).2 = 0 <;> simp [hv]
      · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
        by_cases hv : (Nat.unpair m).2 = 0 <;> simp [hv]
      · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
        cases h : decOTerm (Nat.unpair m).2 <;> simp [Encodable.encode_none, Encodable.encode_some]
      · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
        cases h₁ : decOTerm (Nat.unpair (Nat.unpair m).2).1 <;>
        cases h₂ : decOTerm (Nat.unpair (Nat.unpair m).2).2 <;>
        simp [Encodable.encode_none, Encodable.encode_some]
      · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
        cases h₁ : decOTerm (Nat.unpair (Nat.unpair m).2).1 <;>
        cases h₂ : decOTerm (Nat.unpair (Nat.unpair m).2).2 <;>
        simp [Encodable.encode_none, Encodable.encode_some]
      · simp only [show tag + 7 ≠ 0 by omega, show tag + 7 ≠ 1 by omega,
          show tag + 7 ≠ 2 by omega, show tag + 7 ≠ 3 by omega,
          show tag + 7 ≠ 4 by omega, show tag + 7 ≠ 5 by omega,
          show tag + 7 ≠ 6 by omega, ↓reduceIte]
        simp
  exact hrec.comp (.const ()) .id

def gFormStep (L : List ℕ) : ℕ :=
  if L.length = 0 then 0
  else
    let m := L.length - 1
    let tag := (Nat.unpair m).1
    let val := (Nat.unpair m).2
    if tag = 0 then if val = 0 then m + 2 else 0
    else if tag = 1 then
      if Encodable.encode (decOTerm (Nat.unpair val).1) ≠ 0 ∧
         Encodable.encode (decOTerm (Nat.unpair val).2) ≠ 0 then m + 2 else 0
    else if tag = 2 then
      if Encodable.encode (decOTerm (Nat.unpair val).1) ≠ 0 ∧
         Encodable.encode (decOTerm (Nat.unpair val).2) ≠ 0 then m + 2 else 0
    else if tag = 3 then
      if L.getD (Nat.unpair val).1 0 ≠ 0 ∧ L.getD (Nat.unpair val).2 0 ≠ 0 then m + 2 else 0
    else if tag = 4 then
      if L.getD val 0 = 0 then 0 else m + 2
    else 0

lemma primrec_gFormStep : Primrec gFormStep := by
  have hm : Primrec (fun L : List ℕ => L.length - 1) := Primrec.pred.comp Primrec.list_length
  have htag : Primrec (fun L : List ℕ => (Nat.unpair (L.length - 1)).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hm)
  have hval : Primrec (fun L : List ℕ => (Nat.unpair (L.length - 1)).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hm)
  have hm2 : Primrec (fun L : List ℕ => (L.length - 1) + 2) :=
    Primrec.succ.comp (Primrec.succ.comp hm)
  have hvalL : Primrec (fun L : List ℕ => (Nat.unpair (Nat.unpair (L.length - 1)).2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hval)
  have hvalR : Primrec (fun L : List ℕ => (Nat.unpair (Nat.unpair (L.length - 1)).2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hval)
  have hdecT : Primrec (fun n : ℕ => Encodable.encode (decOTerm n)) := Primrec.encdec (α := OTerm)
  have htermBoth : PrimrecPred (fun L : List ℕ =>
      Encodable.encode (decOTerm (Nat.unpair (Nat.unpair (L.length - 1)).2).1) ≠ 0 ∧
      Encodable.encode (decOTerm (Nat.unpair (Nat.unpair (L.length - 1)).2).2) ≠ 0) :=
    PrimrecPred.and (Primrec.eq.comp (hdecT.comp hvalL) (.const 0)).not
      (Primrec.eq.comp (hdecT.comp hvalR) (.const 0)).not
  have hg0 : Primrec (fun L : List ℕ => L.getD (Nat.unpair (L.length - 1)).2 0) :=
    (Primrec.list_getD 0).comp .id hval
  have hgL : Primrec (fun L : List ℕ => L.getD (Nat.unpair (Nat.unpair (L.length - 1)).2).1 0) :=
    (Primrec.list_getD 0).comp .id hvalL
  have hgR : Primrec (fun L : List ℕ => L.getD (Nat.unpair (Nat.unpair (L.length - 1)).2).2 0) :=
    (Primrec.list_getD 0).comp .id hvalR
  have hformBoth : PrimrecPred (fun L : List ℕ =>
      L.getD (Nat.unpair (Nat.unpair (L.length - 1)).2).1 0 ≠ 0 ∧
      L.getD (Nat.unpair (Nat.unpair (L.length - 1)).2).2 0 ≠ 0) :=
    PrimrecPred.and (Primrec.eq.comp hgL (.const 0)).not (Primrec.eq.comp hgR (.const 0)).not
  unfold gFormStep
  exact Primrec.ite (Primrec.eq.comp Primrec.list_length (.const 0)) (.const 0)
    (Primrec.ite (Primrec.eq.comp htag (.const 0))
      (Primrec.ite (Primrec.eq.comp hval (.const 0)) hm2 (.const 0))
    (Primrec.ite (Primrec.eq.comp htag (.const 1))
      (Primrec.ite htermBoth hm2 (.const 0))
    (Primrec.ite (Primrec.eq.comp htag (.const 2))
      (Primrec.ite htermBoth hm2 (.const 0))
    (Primrec.ite (Primrec.eq.comp htag (.const 3))
      (Primrec.ite hformBoth hm2 (.const 0))
    (Primrec.ite (Primrec.eq.comp htag (.const 4))
      (Primrec.ite (Primrec.eq.comp hg0 (.const 0)) (.const 0) hm2)
      (.const 0))))))

lemma encode_decOForm_eq_ite (n : ℕ) :
    Encodable.encode (decOForm n) = if (decOForm n).isSome then n + 1 else 0 := by
  cases h : decOForm n with
  | none => rfl
  | some φ =>
    simp [Encodable.encode_some, show Encodable.encode φ = n from encOForm_of_decOForm h]

instance : Primcodable OForm := by
  refine ⟨Primrec.nat_iff.1 ?_⟩
  have hrec : Primrec₂ (fun (_ : Unit) (n : ℕ) => Encodable.encode (decOForm n)) := by
    refine Primrec.nat_strong_rec (fun (_ : Unit) n => Encodable.encode (decOForm n))
      (g := fun _ L => some (gFormStep L))
      (Primrec.option_some.comp (primrec_gFormStep.comp .snd)) ?_
    intro _ n
    congr 1
    cases n with
    | zero => simp [gFormStep, decOForm]
    | succ m =>
      have hlen : ((List.range (m + 1)).map (fun k => Encodable.encode (decOForm k))).length = m + 1 := by
        simp
      have hval_lt : (Nat.unpair m).2 < m + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le m)
      have hvalL_lt : (Nat.unpair (Nat.unpair m).2).1 < m + 1 :=
        Nat.lt_succ_of_le ((Nat.unpair_left_le _).trans (Nat.unpair_right_le m))
      have hvalR_lt : (Nat.unpair (Nat.unpair m).2).2 < m + 1 :=
        Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le m))
      rw [encode_decOForm_eq_ite]
      unfold gFormStep
      simp only [hlen, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel, decOForm]
      rw [getD_map_range _ hval_lt, getD_map_range _ hvalL_lt, getD_map_range _ hvalR_lt]
      rcases (Nat.unpair m).1 with _ | _ | _ | _ | _ | tag
      · simp only [↓reduceIte]
        by_cases hv : (Nat.unpair m).2 = 0 <;> simp [hv]
      · simp only [Nat.zero_add, Nat.reduceEqDiff, ↓reduceIte]
        cases h₁ : decOTerm (Nat.unpair (Nat.unpair m).2).1 <;>
        cases h₂ : decOTerm (Nat.unpair (Nat.unpair m).2).2 <;>
        simp [Encodable.encode_none, Encodable.encode_some]
      · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
        cases h₁ : decOTerm (Nat.unpair (Nat.unpair m).2).1 <;>
        cases h₂ : decOTerm (Nat.unpair (Nat.unpair m).2).2 <;>
        simp [Encodable.encode_none, Encodable.encode_some]
      · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
        cases h₁ : decOForm (Nat.unpair (Nat.unpair m).2).1 <;>
        cases h₂ : decOForm (Nat.unpair (Nat.unpair m).2).2 <;>
        simp [Encodable.encode_none, Encodable.encode_some]
      · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
        cases h : decOForm (Nat.unpair m).2 <;> simp [Encodable.encode_none, Encodable.encode_some]
      · simp only [show tag + 5 ≠ 0 by omega, show tag + 5 ≠ 1 by omega,
          show tag + 5 ≠ 2 by omega, show tag + 5 ≠ 3 by omega,
          show tag + 5 ≠ 4 by omega, ↓reduceIte]
        simp
  exact hrec.comp (.const ()) .id

lemma primrec_oterm_fvar : Primrec OTerm.fvar :=
  Primrec.encode_iff.1 (Primrec.succ.comp (Primrec₂.natPair.comp (.const 0) .id))

lemma primrec_oterm_bvar : Primrec OTerm.bvar :=
  Primrec.encode_iff.1 (Primrec.succ.comp (Primrec₂.natPair.comp (.const 1) .id))

lemma primrec_oterm_neg : Primrec OTerm.neg :=
  Primrec.encode_iff.1 (Primrec.succ.comp (Primrec₂.natPair.comp (.const 4) Primrec.encode))

lemma primrec_oterm_add : Primrec₂ OTerm.add :=
  Primrec₂.encode_iff.1 (Primrec.succ.comp
    (Primrec₂.natPair.comp (.const 5)
      (Primrec₂.natPair.comp (Primrec.encode.comp .fst) (Primrec.encode.comp .snd))))

lemma primrec_oterm_mul : Primrec₂ OTerm.mul :=
  Primrec₂.encode_iff.1 (Primrec.succ.comp
    (Primrec₂.natPair.comp (.const 6)
      (Primrec₂.natPair.comp (Primrec.encode.comp .fst) (Primrec.encode.comp .snd))))

lemma primrec_oform_eq : Primrec₂ OForm.eq :=
  Primrec₂.encode_iff.1 (Primrec.succ.comp
    (Primrec₂.natPair.comp (.const 1)
      (Primrec₂.natPair.comp (Primrec.encode.comp .fst) (Primrec.encode.comp .snd))))

lemma primrec_oform_le : Primrec₂ OForm.le :=
  Primrec₂.encode_iff.1 (Primrec.succ.comp
    (Primrec₂.natPair.comp (.const 2)
      (Primrec₂.natPair.comp (Primrec.encode.comp .fst) (Primrec.encode.comp .snd))))

lemma primrec_oform_imp : Primrec₂ OForm.imp :=
  Primrec₂.encode_iff.1 (Primrec.succ.comp
    (Primrec₂.natPair.comp (.const 3)
      (Primrec₂.natPair.comp (Primrec.encode.comp .fst) (Primrec.encode.comp .snd))))

lemma primrec_oform_all : Primrec OForm.all :=
  Primrec.encode_iff.1 (Primrec.succ.comp (Primrec₂.natPair.comp (.const 4) Primrec.encode))

lemma primrec_oterm_casesOn {α σ : Type*} [Primcodable α] [Primcodable σ]
    {f_fvar f_bvar : α → ℕ → σ} {f_zero f_one : α → σ}
    {f_neg : α → OTerm → σ} {f_add f_mul : α → OTerm × OTerm → σ}
    (hfv : Primrec₂ f_fvar) (hbv : Primrec₂ f_bvar)
    (hz : Primrec f_zero) (ho : Primrec f_one)
    (hn : Primrec₂ f_neg) (ha : Primrec₂ f_add) (hm : Primrec₂ f_mul) :
    Primrec₂ (fun (a : α) (t : OTerm) => match t with
      | .fvar c => f_fvar a c
      | .bvar k => f_bvar a k
      | .zero => f_zero a
      | .one => f_one a
      | .neg t' => f_neg a t'
      | .add t₁ t₂ => f_add a (t₁, t₂)
      | .mul t₁ t₂ => f_mul a (t₁, t₂)) := by
  refine Primrec₂.option_some_iff.1 ?_
  have hm' : Primrec (fun p : α × OTerm => Encodable.encode p.2 - 1) :=
    Primrec.pred.comp (Primrec.encode.comp .snd)
  have htag : Primrec (fun p : α × OTerm => (Nat.unpair (Encodable.encode p.2 - 1)).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hm')
  have hval : Primrec (fun p : α × OTerm => (Nat.unpair (Encodable.encode p.2 - 1)).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hm')
  have hvalL : Primrec (fun p : α × OTerm => (Nat.unpair (Nat.unpair (Encodable.encode p.2 - 1)).2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hval)
  have hvalR : Primrec (fun p : α × OTerm => (Nat.unpair (Nat.unpair (Encodable.encode p.2 - 1)).2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hval)
  have hbody : Primrec (fun p : α × OTerm =>
      let m := Encodable.encode p.2 - 1
      let tag := (Nat.unpair m).1
      let val := (Nat.unpair m).2
      if tag = 0 then some (f_fvar p.1 val)
      else if tag = 1 then some (f_bvar p.1 val)
      else if tag = 2 then some (f_zero p.1)
      else if tag = 3 then some (f_one p.1)
      else if tag = 4 then (Encodable.decode (α := OTerm) val).map (f_neg p.1)
      else if tag = 5 then
        (Encodable.decode (α := OTerm) (Nat.unpair val).1).bind fun t₁ =>
          (Encodable.decode (α := OTerm) (Nat.unpair val).2).map fun t₂ => f_add p.1 (t₁, t₂)
      else if tag = 6 then
        (Encodable.decode (α := OTerm) (Nat.unpair val).1).bind fun t₁ =>
          (Encodable.decode (α := OTerm) (Nat.unpair val).2).map fun t₂ => f_mul p.1 (t₁, t₂)
      else none) := by
    refine Primrec.ite (Primrec.eq.comp htag (.const 0)) (Primrec.option_some.comp (hfv.comp .fst hval))
      (Primrec.ite (Primrec.eq.comp htag (.const 1)) (Primrec.option_some.comp (hbv.comp .fst hval))
      (Primrec.ite (Primrec.eq.comp htag (.const 2)) (Primrec.option_some.comp (hz.comp .fst))
      (Primrec.ite (Primrec.eq.comp htag (.const 3)) (Primrec.option_some.comp (ho.comp .fst))
      (Primrec.ite (Primrec.eq.comp htag (.const 4))
        (Primrec.option_map (Primrec.decode.comp hval) (hn.comp (Primrec.fst.comp .fst) .snd).to₂)
      (Primrec.ite (Primrec.eq.comp htag (.const 5))
        (Primrec.option_bind (Primrec.decode.comp hvalL)
          (Primrec.option_map (Primrec.decode.comp (hvalR.comp .fst))
            (ha.comp (Primrec.fst.comp (Primrec.fst.comp .fst))
              (Primrec.pair (Primrec.snd.comp .fst) .snd)).to₂).to₂)
      (Primrec.ite (Primrec.eq.comp htag (.const 6))
        (Primrec.option_bind (Primrec.decode.comp hvalL)
          (Primrec.option_map (Primrec.decode.comp (hvalR.comp .fst))
            (hm.comp (Primrec.fst.comp (Primrec.fst.comp .fst))
              (Primrec.pair (Primrec.snd.comp .fst) .snd)).to₂).to₂)
        (.const none)))))))
  refine Primrec₂.mk (hbody.of_eq ?_)
  rintro ⟨a, t⟩
  cases t <;> simp [Encodable.encode, Encodable.decode, encOTerm, Nat.unpair_pair, decOTerm_encOTerm]

lemma primrec_oform_casesOn {α σ : Type*} [Primcodable α] [Primcodable σ]
    {f_bot : α → σ} {f_eq f_le : α → OTerm × OTerm → σ}
    {f_imp : α → OForm × OForm → σ} {f_all : α → OForm → σ}
    (hb : Primrec f_bot) (heq : Primrec₂ f_eq) (hle : Primrec₂ f_le)
    (himp : Primrec₂ f_imp) (hall : Primrec₂ f_all) :
    Primrec₂ (fun (a : α) (φ : OForm) => match φ with
      | .bot => f_bot a
      | .eq t₁ t₂ => f_eq a (t₁, t₂)
      | .le t₁ t₂ => f_le a (t₁, t₂)
      | .imp φ₁ φ₂ => f_imp a (φ₁, φ₂)
      | .all φ' => f_all a φ') := by
  refine Primrec₂.option_some_iff.1 ?_
  have hm' : Primrec (fun p : α × OForm => Encodable.encode p.2 - 1) :=
    Primrec.pred.comp (Primrec.encode.comp .snd)
  have htag : Primrec (fun p : α × OForm => (Nat.unpair (Encodable.encode p.2 - 1)).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hm')
  have hval : Primrec (fun p : α × OForm => (Nat.unpair (Encodable.encode p.2 - 1)).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hm')
  have hvalL : Primrec (fun p : α × OForm => (Nat.unpair (Nat.unpair (Encodable.encode p.2 - 1)).2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hval)
  have hvalR : Primrec (fun p : α × OForm => (Nat.unpair (Nat.unpair (Encodable.encode p.2 - 1)).2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hval)
  have hbody : Primrec (fun p : α × OForm =>
      let m := Encodable.encode p.2 - 1
      let tag := (Nat.unpair m).1
      let val := (Nat.unpair m).2
      if tag = 0 then some (f_bot p.1)
      else if tag = 1 then
        (Encodable.decode (α := OTerm) (Nat.unpair val).1).bind fun t₁ =>
          (Encodable.decode (α := OTerm) (Nat.unpair val).2).map fun t₂ => f_eq p.1 (t₁, t₂)
      else if tag = 2 then
        (Encodable.decode (α := OTerm) (Nat.unpair val).1).bind fun t₁ =>
          (Encodable.decode (α := OTerm) (Nat.unpair val).2).map fun t₂ => f_le p.1 (t₁, t₂)
      else if tag = 3 then
        (Encodable.decode (α := OForm) (Nat.unpair val).1).bind fun φ₁ =>
          (Encodable.decode (α := OForm) (Nat.unpair val).2).map fun φ₂ => f_imp p.1 (φ₁, φ₂)
      else if tag = 4 then (Encodable.decode (α := OForm) val).map (f_all p.1)
      else none) := by
    refine Primrec.ite (Primrec.eq.comp htag (.const 0)) (Primrec.option_some.comp (hb.comp .fst))
      (Primrec.ite (Primrec.eq.comp htag (.const 1))
        (Primrec.option_bind (Primrec.decode.comp hvalL)
          (Primrec.option_map (Primrec.decode.comp (hvalR.comp .fst))
            (heq.comp (Primrec.fst.comp (Primrec.fst.comp .fst))
              (Primrec.pair (Primrec.snd.comp .fst) .snd)).to₂).to₂)
      (Primrec.ite (Primrec.eq.comp htag (.const 2))
        (Primrec.option_bind (Primrec.decode.comp hvalL)
          (Primrec.option_map (Primrec.decode.comp (hvalR.comp .fst))
            (hle.comp (Primrec.fst.comp (Primrec.fst.comp .fst))
              (Primrec.pair (Primrec.snd.comp .fst) .snd)).to₂).to₂)
      (Primrec.ite (Primrec.eq.comp htag (.const 3))
        (Primrec.option_bind (Primrec.decode.comp hvalL)
          (Primrec.option_map (Primrec.decode.comp (hvalR.comp .fst))
            (himp.comp (Primrec.fst.comp (Primrec.fst.comp .fst))
              (Primrec.pair (Primrec.snd.comp .fst) .snd)).to₂).to₂)
      (Primrec.ite (Primrec.eq.comp htag (.const 4))
        (Primrec.option_map (Primrec.decode.comp hval) (hall.comp (Primrec.fst.comp .fst) .snd).to₂)
        (.const none)))))
  refine Primrec₂.mk (hbody.of_eq ?_)
  rintro ⟨a, φ⟩
  cases φ <;> simp [Encodable.encode, Encodable.decode, encOForm, Nat.unpair_pair,
    decOTerm_encOTerm, decOForm_encOForm]

lemma primrec_oterm_rec {α σ : Type*} [Primcodable α] [Primcodable σ]
    (f : α → OTerm → σ)
    {f_fvar f_bvar : α → ℕ → σ} {f_zero f_one : α → σ}
    {f_neg : α → σ → σ} {f_add f_mul : α → σ × σ → σ}
    (hfv : Primrec₂ f_fvar) (hbv : Primrec₂ f_bvar)
    (hz : Primrec f_zero) (ho : Primrec f_one)
    (hn : Primrec₂ f_neg) (ha : Primrec₂ f_add) (hm : Primrec₂ f_mul)
    (h_fvar : ∀ a c, f a (.fvar c) = f_fvar a c)
    (h_bvar : ∀ a k, f a (.bvar k) = f_bvar a k)
    (h_zero : ∀ a, f a .zero = f_zero a)
    (h_one : ∀ a, f a .one = f_one a)
    (h_neg : ∀ a t, f a (.neg t) = f_neg a (f a t))
    (h_add : ∀ a t₁ t₂, f a (.add t₁ t₂) = f_add a (f a t₁, f a t₂))
    (h_mul : ∀ a t₁ t₂, f a (.mul t₁ t₂) = f_mul a (f a t₁, f a t₂)) :
    Primrec₂ f := by
  let children : α × OTerm → List (α × OTerm) := fun p =>
    match p.2 with
    | .fvar _ => []
    | .bvar _ => []
    | .zero => []
    | .one => []
    | .neg t => [(p.1, t)]
    | .add t₁ t₂ => [(p.1, t₁), (p.1, t₂)]
    | .mul t₁ t₂ => [(p.1, t₁), (p.1, t₂)]
  have hchildren : Primrec children :=
    primrec_oterm_casesOn (Primrec₂.const []) (Primrec₂.const []) (.const []) (.const [])
      (Primrec.list_cons.comp (Primrec.pair .fst .snd) (.const ([] : List (α × OTerm)))).to₂
      (Primrec.list_cons.comp (Primrec.pair .fst (Primrec.fst.comp .snd))
        (Primrec.list_cons.comp (Primrec.pair .fst (Primrec.snd.comp .snd))
          (.const ([] : List (α × OTerm))))).to₂
      (Primrec.list_cons.comp (Primrec.pair .fst (Primrec.fst.comp .snd))
        (Primrec.list_cons.comp (Primrec.pair .fst (Primrec.snd.comp .snd))
          (.const ([] : List (α × OTerm))))).to₂
  let step : α × OTerm → List σ → Option σ := fun p rs =>
    match p.2 with
    | .fvar c => some (f_fvar p.1 c)
    | .bvar k => some (f_bvar p.1 k)
    | .zero => some (f_zero p.1)
    | .one => some (f_one p.1)
    | .neg _ => (rs[0]?).map (f_neg p.1)
    | .add _ _ => (rs[0]?).bind fun r₁ => (rs[1]?).map fun r₂ => f_add p.1 (r₁, r₂)
    | .mul _ _ => (rs[0]?).bind fun r₁ => (rs[1]?).map fun r₂ => f_mul p.1 (r₁, r₂)
  have hstep : Primrec₂ step := by
    have haux : Primrec₂ (fun (q : α × List σ) (t : OTerm) => step (q.1, t) q.2) :=
      primrec_oterm_casesOn
        (Primrec.option_some.comp (hfv.comp (Primrec.fst.comp .fst) .snd)).to₂
        (Primrec.option_some.comp (hbv.comp (Primrec.fst.comp .fst) .snd)).to₂
        (Primrec.option_some.comp (hz.comp .fst))
        (Primrec.option_some.comp (ho.comp .fst))
        (Primrec.option_map (Primrec.list_getElem?.comp (Primrec.snd.comp .fst) (.const 0))
          (hn.comp (Primrec.fst.comp (Primrec.fst.comp .fst)) .snd).to₂).to₂
        (Primrec.option_bind (Primrec.list_getElem?.comp (Primrec.snd.comp .fst) (.const 0))
          (Primrec.option_map
            (Primrec.list_getElem?.comp (Primrec.snd.comp (Primrec.fst.comp .fst)) (.const 1))
            (ha.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp .fst)))
              (Primrec.pair (Primrec.snd.comp .fst) .snd)).to₂).to₂).to₂
        (Primrec.option_bind (Primrec.list_getElem?.comp (Primrec.snd.comp .fst) (.const 0))
          (Primrec.option_map
            (Primrec.list_getElem?.comp (Primrec.snd.comp (Primrec.fst.comp .fst)) (.const 1))
            (hm.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp .fst)))
              (Primrec.pair (Primrec.snd.comp .fst) .snd)).to₂).to₂).to₂
    exact haux.comp (Primrec.pair (Primrec.fst.comp .fst) .snd) (Primrec.snd.comp .fst)
  refine Primrec.nat_omega_rec' (fun p : α × OTerm => f p.1 p.2)
    (m := fun p => Encodable.encode p.2) (l := children) (g := step)
    (Primrec.encode.comp .snd) hchildren hstep ?_ ?_
  · rintro ⟨a, t⟩ ⟨a', t'⟩ hmem
    cases t <;> simp only [children, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    · rcases hmem with ⟨_, rfl⟩
      exact Nat.lt_succ_of_le (Nat.right_le_pair _ _)
    · rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Nat.lt_succ_of_le ((Nat.left_le_pair _ _).trans (Nat.right_le_pair _ _))
      · exact Nat.lt_succ_of_le ((Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _))
    · rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Nat.lt_succ_of_le ((Nat.left_le_pair _ _).trans (Nat.right_le_pair _ _))
      · exact Nat.lt_succ_of_le ((Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _))
  · rintro ⟨a, t⟩
    cases t <;> simp [children, step, h_fvar, h_bvar, h_zero, h_one, h_neg, h_add, h_mul]

lemma primrec_oform_rec {α σ : Type*} [Primcodable α] [Primcodable σ]
    (f : α → OForm → σ) (allArg : α → α)
    {f_bot : α → σ} {f_eq f_le : α → OTerm × OTerm → σ}
    {f_imp : α → σ × σ → σ} {f_all : α → σ → σ}
    (hallArg : Primrec allArg)
    (hb : Primrec f_bot) (heq : Primrec₂ f_eq) (hle : Primrec₂ f_le)
    (himp : Primrec₂ f_imp) (hall : Primrec₂ f_all)
    (h_bot : ∀ a, f a .bot = f_bot a)
    (h_eq : ∀ a t₁ t₂, f a (.eq t₁ t₂) = f_eq a (t₁, t₂))
    (h_le : ∀ a t₁ t₂, f a (.le t₁ t₂) = f_le a (t₁, t₂))
    (h_imp : ∀ a φ₁ φ₂, f a (.imp φ₁ φ₂) = f_imp a (f a φ₁, f a φ₂))
    (h_all : ∀ a φ, f a (.all φ) = f_all a (f (allArg a) φ)) :
    Primrec₂ f := by
  let children : α × OForm → List (α × OForm) := fun p =>
    match p.2 with
    | .bot => []
    | .eq _ _ => []
    | .le _ _ => []
    | .imp φ₁ φ₂ => [(p.1, φ₁), (p.1, φ₂)]
    | .all φ => [(allArg p.1, φ)]
  have hchildren : Primrec children :=
    primrec_oform_casesOn (.const []) (Primrec₂.const []) (Primrec₂.const [])
      (Primrec.list_cons.comp (Primrec.pair .fst (Primrec.fst.comp .snd))
        (Primrec.list_cons.comp (Primrec.pair .fst (Primrec.snd.comp .snd))
          (.const ([] : List (α × OForm))))).to₂
      (Primrec.list_cons.comp (Primrec.pair (hallArg.comp .fst) .snd)
        (.const ([] : List (α × OForm)))).to₂
  let step : α × OForm → List σ → Option σ := fun p rs =>
    match p.2 with
    | .bot => some (f_bot p.1)
    | .eq t₁ t₂ => some (f_eq p.1 (t₁, t₂))
    | .le t₁ t₂ => some (f_le p.1 (t₁, t₂))
    | .imp _ _ => (rs[0]?).bind fun r₁ => (rs[1]?).map fun r₂ => f_imp p.1 (r₁, r₂)
    | .all _ => (rs[0]?).map (f_all p.1)
  have hstep : Primrec₂ step := by
    have haux : Primrec₂ (fun (q : α × List σ) (φ : OForm) => step (q.1, φ) q.2) :=
      primrec_oform_casesOn
        (Primrec.option_some.comp (hb.comp .fst))
        (Primrec.option_some.comp (heq.comp (Primrec.fst.comp .fst) .snd)).to₂
        (Primrec.option_some.comp (hle.comp (Primrec.fst.comp .fst) .snd)).to₂
        (Primrec.option_bind (Primrec.list_getElem?.comp (Primrec.snd.comp .fst) (.const 0))
          (Primrec.option_map
            (Primrec.list_getElem?.comp (Primrec.snd.comp (Primrec.fst.comp .fst)) (.const 1))
            (himp.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp .fst)))
              (Primrec.pair (Primrec.snd.comp .fst) .snd)).to₂).to₂).to₂
        (Primrec.option_map (Primrec.list_getElem?.comp (Primrec.snd.comp .fst) (.const 0))
          (hall.comp (Primrec.fst.comp (Primrec.fst.comp .fst)) .snd).to₂).to₂
    exact haux.comp (Primrec.pair (Primrec.fst.comp .fst) .snd) (Primrec.snd.comp .fst)
  refine Primrec.nat_omega_rec' (fun p : α × OForm => f p.1 p.2)
    (m := fun p => Encodable.encode p.2) (l := children) (g := step)
    (Primrec.encode.comp .snd) hchildren hstep ?_ ?_
  · rintro ⟨a, φ⟩ ⟨a', φ'⟩ hmem
    cases φ <;> simp only [children, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    · rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Nat.lt_succ_of_le ((Nat.left_le_pair _ _).trans (Nat.right_le_pair _ _))
      · exact Nat.lt_succ_of_le ((Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _))
    · rcases hmem with ⟨_, rfl⟩
      exact Nat.lt_succ_of_le (Nat.right_le_pair _ _)
  · rintro ⟨a, φ⟩
    cases φ <;> simp [children, step, h_bot, h_eq, h_le, h_imp, h_all]

lemma primrec_noBVar : Primrec noBVar := by
  have h : Primrec₂ (fun (_ : Unit) t => noBVar t) :=
    primrec_oterm_rec (fun (_ : Unit) t => noBVar t)
      (f_fvar := fun _ _ => true) (f_bvar := fun _ _ => false)
      (f_zero := fun _ => true) (f_one := fun _ => true)
      (f_neg := fun _ b => b) (f_add := fun _ p => p.1 && p.2) (f_mul := fun _ p => p.1 && p.2)
      (Primrec₂.const true) (Primrec₂.const false) (.const true) (.const true)
      Primrec₂.right (Primrec.and.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
      (Primrec.and.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  exact h.comp (.const ()) .id

lemma primrec_isSentTerm : Primrec₂ isSentTerm :=
  primrec_oterm_rec isSentTerm
    (f_fvar := fun _ _ => false) (f_bvar := fun d k => decide (k < d))
    (f_zero := fun _ => true) (f_one := fun _ => true)
    (f_neg := fun _ b => b) (f_add := fun _ p => p.1 && p.2) (f_mul := fun _ p => p.1 && p.2)
    (Primrec₂.const false) (Primrec.nat_lt.comp .snd .fst).decide.to₂ (.const true) (.const true)
    Primrec₂.right (Primrec.and.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
    (Primrec.and.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

lemma primrec_isSentForm : Primrec₂ isSentForm :=
  primrec_oform_rec isSentForm Nat.succ
    (f_bot := fun _ => true)
    (f_eq := fun d p => isSentTerm d p.1 && isSentTerm d p.2)
    (f_le := fun d p => isSentTerm d p.1 && isSentTerm d p.2)
    (f_imp := fun _ p => p.1 && p.2) (f_all := fun _ b => b)
    Primrec.succ (.const true)
    (Primrec.and.comp (primrec_isSentTerm.comp .fst (Primrec.fst.comp .snd))
      (primrec_isSentTerm.comp .fst (Primrec.snd.comp .snd))).to₂
    (Primrec.and.comp (primrec_isSentTerm.comp .fst (Primrec.fst.comp .snd))
      (primrec_isSentTerm.comp .fst (Primrec.snd.comp .snd))).to₂
    (Primrec.and.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
    Primrec₂.right
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)

lemma primrec_freshInTerm : Primrec₂ freshInTerm :=
  primrec_oterm_rec freshInTerm
    (f_fvar := fun c x => decide (x ≠ c)) (f_bvar := fun _ _ => true)
    (f_zero := fun _ => true) (f_one := fun _ => true)
    (f_neg := fun _ b => b) (f_add := fun _ p => p.1 && p.2) (f_mul := fun _ p => p.1 && p.2)
    (Primrec.eq.comp .snd .fst).not.decide.to₂ (Primrec₂.const true) (.const true) (.const true)
    Primrec₂.right (Primrec.and.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
    (Primrec.and.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

lemma primrec_freshInForm : Primrec₂ freshInForm :=
  primrec_oform_rec freshInForm id
    (f_bot := fun _ => true)
    (f_eq := fun c p => freshInTerm c p.1 && freshInTerm c p.2)
    (f_le := fun c p => freshInTerm c p.1 && freshInTerm c p.2)
    (f_imp := fun _ p => p.1 && p.2) (f_all := fun _ b => b)
    Primrec.id (.const true)
    (Primrec.and.comp (primrec_freshInTerm.comp .fst (Primrec.fst.comp .snd))
      (primrec_freshInTerm.comp .fst (Primrec.snd.comp .snd))).to₂
    (Primrec.and.comp (primrec_freshInTerm.comp .fst (Primrec.fst.comp .snd))
      (primrec_freshInTerm.comp .fst (Primrec.snd.comp .snd))).to₂
    (Primrec.and.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
    Primrec₂.right
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)

lemma primrec_substTerm0 : Primrec₂ substTerm0 :=
  primrec_oterm_rec substTerm0
    (f_fvar := fun _ c => .fvar c)
    (f_bvar := fun t k => Nat.casesOn k t .bvar)
    (f_zero := fun _ => .zero) (f_one := fun _ => .one)
    (f_neg := fun _ s => .neg s)
    (f_add := fun _ p => .add p.1 p.2)
    (f_mul := fun _ p => .mul p.1 p.2)
    (primrec_oterm_fvar.comp .snd).to₂
    (Primrec.nat_casesOn .snd .fst (primrec_oterm_bvar.comp .snd).to₂).to₂
    (.const OTerm.zero) (.const OTerm.one)
    (primrec_oterm_neg.comp .snd).to₂
    (primrec_oterm_add.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
    (primrec_oterm_mul.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
    (fun _ _ => rfl) (fun _ k => by cases k <;> rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

lemma primrec_substForm0 : Primrec₂ substForm0 :=
  primrec_oform_rec substForm0 id
    (f_bot := fun _ => .bot)
    (f_eq := fun t p => .eq (substTerm0 t p.1) (substTerm0 t p.2))
    (f_le := fun t p => .le (substTerm0 t p.1) (substTerm0 t p.2))
    (f_imp := fun _ p => .imp p.1 p.2)
    (f_all := fun _ ψ => .all ψ)
    Primrec.id (.const OForm.bot)
    (primrec_oform_eq.comp (primrec_substTerm0.comp .fst (Primrec.fst.comp .snd))
      (primrec_substTerm0.comp .fst (Primrec.snd.comp .snd))).to₂
    (primrec_oform_le.comp (primrec_substTerm0.comp .fst (Primrec.fst.comp .snd))
      (primrec_substTerm0.comp .fst (Primrec.snd.comp .snd))).to₂
    (primrec_oform_imp.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
    (primrec_oform_all.comp .snd).to₂
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)

/- ### 10. Exact Gödel-number agreement with Mathlib and `Primrec` sentence decoder -/

def mathlibTermTokens : OTerm → List ℕ
  | .fvar _ => []
  | .bvar k => [4 * k + 2]
  | .zero => [13]
  | .one => [17]
  | .neg t => 9 :: mathlibTermTokens t
  | .add t₁ t₂ => 1 :: (mathlibTermTokens t₁ ++ mathlibTermTokens t₂)
  | .mul t₁ t₂ => 5 :: (mathlibTermTokens t₁ ++ mathlibTermTokens t₂)

def mathlibCodeTerm (t : OTerm) : ℕ := Encodable.encode (mathlibTermTokens t)

def mathlibFormTokens (d : ℕ) : OForm → List ℕ
  | .bot => [4 * d + 11]
  | .eq t₁ t₂ =>
      [2 * Nat.pair d (mathlibCodeTerm t₁), 2 * Nat.pair d (mathlibCodeTerm t₂)]
  | .le t₁ t₂ =>
      [5, 4 * d + 3, 2 * Nat.pair d (mathlibCodeTerm t₁), 2 * Nat.pair d (mathlibCodeTerm t₂)]
  | .imp φ₁ φ₂ => 3 :: (mathlibFormTokens d φ₁ ++ mathlibFormTokens d φ₂)
  | .all φ => 7 :: mathlibFormTokens (d + 1) φ

def mathlibCodeSent (φ : OForm) : ℕ := Encodable.encode (mathlibFormTokens 0 φ)

lemma primrec_mathlibTermTokens : Primrec mathlibTermTokens := by
  have h : Primrec₂ (fun (_ : Unit) t => mathlibTermTokens t) :=
    primrec_oterm_rec (fun (_ : Unit) t => mathlibTermTokens t)
      (f_fvar := fun _ _ => [])
      (f_bvar := fun _ k => [4 * k + 2])
      (f_zero := fun _ => [13]) (f_one := fun _ => [17])
      (f_neg := fun _ l => 9 :: l)
      (f_add := fun _ p => 1 :: (p.1 ++ p.2))
      (f_mul := fun _ p => 5 :: (p.1 ++ p.2))
      (Primrec₂.const [])
      (Primrec.list_cons.comp
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 4) .snd) (.const 2)) (.const [])).to₂
      (.const [13]) (.const [17])
      (Primrec.list_cons.comp (.const 9) .snd).to₂
      (Primrec.list_cons.comp (.const 1)
        (Primrec.list_append.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd))).to₂
      (Primrec.list_cons.comp (.const 5)
        (Primrec.list_append.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd))).to₂
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  exact h.comp (.const ()) .id

lemma primrec_mathlibCodeTerm : Primrec mathlibCodeTerm :=
  Primrec.encode.comp primrec_mathlibTermTokens

lemma primrec_mathlibFormTokens : Primrec₂ mathlibFormTokens := by
  have htokTerm : Primrec₂ (fun (d : ℕ) (t : OTerm) => 2 * Nat.pair d (mathlibCodeTerm t)) :=
    (Primrec.nat_mul.comp (.const 2)
      (Primrec₂.natPair.comp .fst (primrec_mathlibCodeTerm.comp .snd))).to₂
  exact primrec_oform_rec mathlibFormTokens Nat.succ
    (f_bot := fun d => [4 * d + 11])
    (f_eq := fun d p => [2 * Nat.pair d (mathlibCodeTerm p.1), 2 * Nat.pair d (mathlibCodeTerm p.2)])
    (f_le := fun d p => [5, 4 * d + 3, 2 * Nat.pair d (mathlibCodeTerm p.1),
      2 * Nat.pair d (mathlibCodeTerm p.2)])
    (f_imp := fun _ p => 3 :: (p.1 ++ p.2))
    (f_all := fun _ l => 7 :: l)
    Primrec.succ
    (Primrec.list_cons.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 4) .id) (.const 11)) (.const []))
    (Primrec.list_cons.comp (htokTerm.comp .fst (Primrec.fst.comp .snd))
      (Primrec.list_cons.comp (htokTerm.comp .fst (Primrec.snd.comp .snd)) (.const []))).to₂
    (Primrec.list_cons.comp (.const 5)
      (Primrec.list_cons.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 4) .fst) (.const 3))
        (Primrec.list_cons.comp (htokTerm.comp .fst (Primrec.fst.comp .snd))
          (Primrec.list_cons.comp (htokTerm.comp .fst (Primrec.snd.comp .snd)) (.const []))))).to₂
    (Primrec.list_cons.comp (.const 3)
      (Primrec.list_append.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd))).to₂
    (Primrec.list_cons.comp (.const 7) .snd).to₂
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)

lemma primrec_mathlibCodeSent : Primrec mathlibCodeSent :=
  Primrec.encode.comp (primrec_mathlibFormTokens.comp (.const 0) .id)

lemma encode_list_eq_encode_map {α : Type*} [Encodable α] (l : List α) :
    Encodable.encode l = Encodable.encode (l.map Encodable.encode) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [Encodable.encode_list_cons, ih]

lemma listEncode_map_encode_term {d : ℕ} (t : LO.Term (Empty ⊕ Fin d)) :
    (t.listEncode).map Encodable.encode = mathlibTermTokens (ofMathlibTerm t) := by
  induction t with
  | var x =>
    rcases x with e | i
    · exact Empty.elim e
    · simp only [Term.listEncode, List.map_cons, List.map_nil, ofMathlibTerm, mathlibTermTokens,
        List.cons.injEq, and_true]
      change 2 * (2 * i.val + 1) = 4 * i.val + 2
      omega
  | func f ts ih =>
    rcases f with f | f
    · cases f
      · change 1 :: ((List.finRange 2).flatMap fun i => (ts i).listEncode).map Encodable.encode = _
        simp [List.finRange, ih, ofMathlibTerm, mathlibTermTokens]
      · change 5 :: ((List.finRange 2).flatMap fun i => (ts i).listEncode).map Encodable.encode = _
        simp [List.finRange, ih, ofMathlibTerm, mathlibTermTokens]
      · change 9 :: ((List.finRange 1).flatMap fun i => (ts i).listEncode).map Encodable.encode = _
        simp [List.finRange, ih, ofMathlibTerm, mathlibTermTokens]
      · change 13 :: ((List.finRange 0).flatMap fun i => (ts i).listEncode).map Encodable.encode = _
        simp [List.finRange, ofMathlibTerm, mathlibTermTokens]
      · change 17 :: ((List.finRange 0).flatMap fun i => (ts i).listEncode).map Encodable.encode = _
        simp [List.finRange, ofMathlibTerm, mathlibTermTokens]
    · exact Empty.elim f

lemma mathlibCodeTerm_ofMathlibTerm {d : ℕ} (t : LO.Term (Empty ⊕ Fin d)) :
    mathlibCodeTerm (ofMathlibTerm t) = Encodable.encode t := by
  unfold mathlibCodeTerm
  rw [← listEncode_map_encode_term t, ← encode_list_eq_encode_map]
  rfl

lemma listEncode_map_encode_form : ∀ {d : ℕ} (φ : LO.BoundedFormula Empty d),
    (φ.listEncode).map Encodable.encode = mathlibFormTokens d (ofMathlibForm φ) := by
  intro d φ
  induction φ with
  | @falsum d =>
    simp only [BoundedFormula.listEncode, List.map_cons, List.map_nil, ofMathlibForm,
      mathlibFormTokens, List.cons.injEq, and_true]
    change 2 * (2 * (d + 2) + 1) + 1 = 4 * d + 11
    omega
  | @equal d t₁ t₂ =>
    simp only [BoundedFormula.listEncode, List.map_cons, List.map_nil, ofMathlibForm,
      mathlibFormTokens, List.cons.injEq, and_true]
    exact ⟨by simp [mathlibCodeTerm_ofMathlibTerm],
           by simp [mathlibCodeTerm_ofMathlibTerm]⟩
  | @rel d l R ts =>
    rcases R with R | R
    · exact Empty.elim R
    · cases R
      have hfr : List.finRange 2 = [0, 1] := rfl
      simp only [BoundedFormula.listEncode, hfr, List.map_cons,
        List.map_nil, List.cons_append, List.nil_append, ofMathlibForm,
        mathlibFormTokens, List.cons.injEq, and_true]
      refine ⟨rfl, ?_, ?_, ?_⟩
      · change 2 * (2 * d + 1) + 1 = 4 * d + 3; omega
      · simp [mathlibCodeTerm_ofMathlibTerm]
      · simp [mathlibCodeTerm_ofMathlibTerm]
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [BoundedFormula.listEncode, List.cons_append, List.map_cons, List.map_append,
      ofMathlibForm, mathlibFormTokens, ih₁, ih₂]
    rfl
  | all φ ih =>
    simp only [BoundedFormula.listEncode, List.map_cons, ofMathlibForm, mathlibFormTokens, ih]
    rfl

lemma mathlibCodeSent_ofMathlibForm (φ : LO.Sentence) :
    mathlibCodeSent (ofMathlibForm φ) = Encodable.encode φ := by
  unfold mathlibCodeSent
  rw [← listEncode_map_encode_form φ, ← encode_list_eq_encode_map]
  rfl

def decodeTermStep (tok : ℕ) (st : List OTerm) : List OTerm :=
  if tok = 13 then .zero :: st
  else if tok = 17 then .one :: st
  else if tok = 9 then
    match st with
    | t :: rest => .neg t :: rest
    | [] => []
  else if tok = 1 then
    match st with
    | t₁ :: t₂ :: rest => .add t₁ t₂ :: rest
    | _ => []
  else if tok = 5 then
    match st with
    | t₁ :: t₂ :: rest => .mul t₁ t₂ :: rest
    | _ => []
  else if tok % 4 = 2 then .bvar (tok / 4) :: st
  else []

def decodeTermList (l : List ℕ) : List OTerm :=
  l.foldr decodeTermStep []

def decodeMathlibTerm (n : ℕ) : Option OTerm :=
  (decodeTermList (Denumerable.ofNat (List ℕ) n)).head?

lemma primrec_decodeTermStep : Primrec₂ decodeTermStep := by
  have hneg : Primrec (fun st : List OTerm => match st with | t :: r => OTerm.neg t :: r | [] => []) :=
    (Primrec.list_casesOn .id (.const [])
      (Primrec.list_cons.comp (primrec_oterm_neg.comp (Primrec.fst.comp .snd))
        (Primrec.snd.comp .snd)).to₂).of_eq fun st => by cases st <;> rfl
  have hadd : Primrec (fun st : List OTerm =>
      match st with | t₁ :: t₂ :: r => OTerm.add t₁ t₂ :: r | _ => []) :=
    (Primrec.list_casesOn .id (.const [])
      (Primrec.list_casesOn (Primrec.snd.comp .snd) (.const [])
        (Primrec.list_cons.comp
          (primrec_oterm_add.comp (Primrec.fst.comp (Primrec.snd.comp .fst)) (Primrec.fst.comp .snd))
          (Primrec.snd.comp .snd)).to₂).to₂).of_eq fun st => by
      rcases st with _ | ⟨t₁, _ | ⟨t₂, r⟩⟩ <;> rfl
  have hmul : Primrec (fun st : List OTerm =>
      match st with | t₁ :: t₂ :: r => OTerm.mul t₁ t₂ :: r | _ => []) :=
    (Primrec.list_casesOn .id (.const [])
      (Primrec.list_casesOn (Primrec.snd.comp .snd) (.const [])
        (Primrec.list_cons.comp
          (primrec_oterm_mul.comp (Primrec.fst.comp (Primrec.snd.comp .fst)) (Primrec.fst.comp .snd))
          (Primrec.snd.comp .snd)).to₂).to₂).of_eq fun st => by
      rcases st with _ | ⟨t₁, _ | ⟨t₂, r⟩⟩ <;> rfl
  unfold decodeTermStep
  exact Primrec.ite (Primrec.eq.comp .fst (.const 13)) (Primrec.list_cons.comp (.const OTerm.zero) .snd)
    (Primrec.ite (Primrec.eq.comp .fst (.const 17)) (Primrec.list_cons.comp (.const OTerm.one) .snd)
    (Primrec.ite (Primrec.eq.comp .fst (.const 9)) (hneg.comp .snd)
    (Primrec.ite (Primrec.eq.comp .fst (.const 1)) (hadd.comp .snd)
    (Primrec.ite (Primrec.eq.comp .fst (.const 5)) (hmul.comp .snd)
    (Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp .fst (.const 4)) (.const 2))
      (Primrec.list_cons.comp
        (primrec_oterm_bvar.comp (Primrec.nat_div.comp .fst (.const 4))) .snd)
      (.const []))))))

lemma primrec_decodeTermList : Primrec decodeTermList :=
  Primrec.list_foldr .id (.const []) (primrec_decodeTermStep.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂

lemma primrec_decodeMathlibTerm : Primrec decodeMathlibTerm :=
  Primrec.list_head?.comp (primrec_decodeTermList.comp (Primrec.ofNat (List ℕ)))

lemma decodeTermList_mathlibTermTokens {d : ℕ} (t : LO.Term (Empty ⊕ Fin d)) (rest : List ℕ) :
    decodeTermList (mathlibTermTokens (ofMathlibTerm t) ++ rest) =
      ofMathlibTerm t :: decodeTermList rest := by
  induction t generalizing rest with
  | var x =>
    rcases x with e | i
    · exact Empty.elim e
    · simp only [ofMathlibTerm, mathlibTermTokens, List.singleton_append, decodeTermList,
        List.foldr_cons, decodeTermStep]
      have h1 : 4 * i.val + 2 ≠ 13 := by omega
      have h2 : 4 * i.val + 2 ≠ 17 := by omega
      have h3 : 4 * i.val + 2 ≠ 9 := by omega
      have h4 : 4 * i.val + 2 ≠ 1 := by omega
      have h5 : 4 * i.val + 2 ≠ 5 := by omega
      have h6 : (4 * i.val + 2) % 4 = 2 := by omega
      have h7 : (4 * i.val + 2) / 4 = i.val := by omega
      simp [h1, h2, h3, h4, h5, h6, h7]
  | func f ts ih =>
    rcases f with f | f
    · cases f
      · simp only [ofMathlibTerm, mathlibTermTokens, List.cons_append, List.append_assoc]
        change decodeTermStep 1 (decodeTermList (mathlibTermTokens (ofMathlibTerm (ts 0)) ++
          (mathlibTermTokens (ofMathlibTerm (ts 1)) ++ rest))) = _
        rw [ih 0, ih 1]
        simp [decodeTermStep]
      · simp only [ofMathlibTerm, mathlibTermTokens, List.cons_append, List.append_assoc]
        change decodeTermStep 5 (decodeTermList (mathlibTermTokens (ofMathlibTerm (ts 0)) ++
          (mathlibTermTokens (ofMathlibTerm (ts 1)) ++ rest))) = _
        rw [ih 0, ih 1]
        simp [decodeTermStep]
      · simp only [ofMathlibTerm, mathlibTermTokens, List.cons_append]
        change decodeTermStep 9 (decodeTermList (mathlibTermTokens (ofMathlibTerm (ts 0)) ++ rest)) = _
        rw [ih 0]
        simp [decodeTermStep]
      · simp [ofMathlibTerm, mathlibTermTokens, decodeTermList, decodeTermStep]
      · simp [ofMathlibTerm, mathlibTermTokens, decodeTermList, decodeTermStep]
    · exact Empty.elim f

lemma decodeMathlibTerm_encode {d : ℕ} (t : LO.Term (Empty ⊕ Fin d)) :
    decodeMathlibTerm (Encodable.encode t) = some (ofMathlibTerm t) := by
  unfold decodeMathlibTerm
  rw [← mathlibCodeTerm_ofMathlibTerm t, mathlibCodeTerm, Denumerable.ofNat_encode]
  have h := decodeTermList_mathlibTermTokens t []
  simp only [List.append_nil] at h
  simp [h]

def decodeFormList : List ℕ → List OForm
  | [] => []
  | tok :: l =>
      if tok = 3 then
        match decodeFormList l with
        | φ₁ :: φ₂ :: rest => OForm.imp φ₁ φ₂ :: rest
        | _ => []
      else if tok = 7 then
        match decodeFormList l with
        | φ :: rest => OForm.all φ :: rest
        | _ => []
      else if tok = 5 then
        match l with
        | _ :: tok₁ :: tok₂ :: rest =>
            match decodeMathlibTerm (Nat.unpair (tok₁ / 2)).2,
                  decodeMathlibTerm (Nat.unpair (tok₂ / 2)).2 with
            | some t₁, some t₂ => OForm.le t₁ t₂ :: decodeFormList rest
            | _, _ => []
        | _ => []
      else if tok % 2 = 0 then
        match l with
        | tok₂ :: rest =>
            match decodeMathlibTerm (Nat.unpair (tok / 2)).2,
                  decodeMathlibTerm (Nat.unpair (tok₂ / 2)).2 with
            | some t₁, some t₂ => OForm.eq t₁ t₂ :: decodeFormList rest
            | _, _ => []
        | [] => []
      else
        OForm.bot :: decodeFormList l
termination_by l => l.length

def decodeMathlibSent (n : ℕ) : Option OForm :=
  (decodeFormList (Denumerable.ofNat (List ℕ) n)).head?

lemma primrec_decodeFormList : Primrec decodeFormList := by
  let child : List ℕ → List (List ℕ) := fun xs =>
    match xs with
    | [] => []
    | tok :: l =>
      if tok = 3 ∨ tok = 7 then [l]
      else if tok = 5 then
        if 3 ≤ l.length then [l.tail.tail.tail] else []
      else if tok % 2 = 0 then
        if 1 ≤ l.length then [l.tail] else []
      else [l]
  have hchild : Primrec child := by
    have hdrop3 : Primrec (fun l : List ℕ => if 3 ≤ l.length then [l.tail.tail.tail] else []) :=
      Primrec.ite (Primrec.nat_le.comp (.const 3) Primrec.list_length)
        (Primrec.list_cons.comp
          (Primrec.list_tail.comp (Primrec.list_tail.comp (Primrec.list_tail.comp .id)))
          (.const ([] : List (List ℕ))))
        (.const ([] : List (List ℕ)))
    have hdrop1 : Primrec (fun l : List ℕ => if 1 ≤ l.length then [l.tail] else []) :=
      Primrec.ite (Primrec.nat_le.comp (.const 1) Primrec.list_length)
        (Primrec.list_cons.comp Primrec.list_tail (.const ([] : List (List ℕ))))
        (.const ([] : List (List ℕ)))
    exact (Primrec.list_casesOn .id (.const [])
      (Primrec.ite
        (PrimrecPred.or (Primrec.eq.comp (Primrec.fst.comp .snd) (.const 3))
          (Primrec.eq.comp (Primrec.fst.comp .snd) (.const 7)))
        (Primrec.list_cons.comp (Primrec.snd.comp .snd) (.const ([] : List (List ℕ))))
        (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp .snd) (.const 5))
          (hdrop3.comp (Primrec.snd.comp .snd))
          (Primrec.ite
            (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.fst.comp .snd) (.const 2)) (.const 0))
            (hdrop1.comp (Primrec.snd.comp .snd))
            (Primrec.list_cons.comp (Primrec.snd.comp .snd) (.const ([] : List (List ℕ))))))).to₂).of_eq
      fun xs => by cases xs <;> rfl
  let tokToTerm : ℕ → Option OTerm := fun tok => decodeMathlibTerm (Nat.unpair (tok / 2)).2
  have htokToTerm : Primrec tokToTerm :=
    primrec_decodeMathlibTerm.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.nat_div.comp .id (.const 2))))
  let step : List ℕ → List (List OForm) → Option (List OForm) := fun xs rs =>
    let r := rs.getD 0 []
    some (match xs with
      | [] => []
      | tok :: l =>
        if tok = 3 then
          match r with | φ₁ :: φ₂ :: rest => OForm.imp φ₁ φ₂ :: rest | _ => []
        else if tok = 7 then
          match r with | φ :: rest => OForm.all φ :: rest | _ => []
        else if tok = 5 then
          match l with
          | _ :: tok₁ :: tok₂ :: _ =>
            match tokToTerm tok₁, tokToTerm tok₂ with
            | some t₁, some t₂ => OForm.le t₁ t₂ :: r
            | _, _ => []
          | _ => []
        else if tok % 2 = 0 then
          match l with
          | tok₂ :: _ =>
            match tokToTerm tok, tokToTerm tok₂ with
            | some t₁, some t₂ => OForm.eq t₁ t₂ :: r
            | _, _ => []
          | [] => []
        else OForm.bot :: r)
  have hstep : Primrec₂ step := by
    refine Primrec₂.option_some_iff.2 ?_
    have hr : Primrec (fun p : List ℕ × List (List OForm) => p.2.getD 0 []) :=
      (Primrec.list_getD []).comp .snd (.const 0)
    have himpR : Primrec (fun r : List OForm =>
        match r with | φ₁ :: φ₂ :: rest => OForm.imp φ₁ φ₂ :: rest | _ => []) :=
      (Primrec.list_casesOn .id (.const [])
        (Primrec.list_casesOn (Primrec.snd.comp .snd) (.const [])
          (Primrec.list_cons.comp
            (primrec_oform_imp.comp (Primrec.fst.comp (Primrec.snd.comp .fst)) (Primrec.fst.comp .snd))
            (Primrec.snd.comp .snd)).to₂).to₂).of_eq fun r => by
        rcases r with _ | ⟨φ₁, _ | ⟨φ₂, rest⟩⟩ <;> rfl
    have hallR : Primrec (fun r : List OForm =>
        match r with | φ :: rest => OForm.all φ :: rest | _ => []) :=
      (Primrec.list_casesOn .id (.const [])
        (Primrec.list_cons.comp (primrec_oform_all.comp (Primrec.fst.comp .snd))
          (Primrec.snd.comp .snd)).to₂).of_eq fun r => by cases r <;> rfl
    have hmkLe : Primrec (fun q : ℕ × ℕ × List OForm =>
        match tokToTerm q.1, tokToTerm q.2.1 with
        | some t₁, some t₂ => OForm.le t₁ t₂ :: q.2.2
        | _, _ => []) :=
      (Primrec.option_casesOn (htokToTerm.comp .fst) (.const [])
        (Primrec.option_casesOn (htokToTerm.comp (Primrec.fst.comp (Primrec.snd.comp .fst)))
          (.const [])
          (Primrec.list_cons.comp
            (primrec_oform_le.comp (Primrec.snd.comp .fst) .snd)
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp .fst)))).to₂).to₂).of_eq fun q => by
        dsimp only; cases tokToTerm q.1 <;> cases tokToTerm q.2.1 <;> rfl
    have hmkEq : Primrec (fun q : ℕ × ℕ × List OForm =>
        match tokToTerm q.1, tokToTerm q.2.1 with
        | some t₁, some t₂ => OForm.eq t₁ t₂ :: q.2.2
        | _, _ => []) :=
      (Primrec.option_casesOn (htokToTerm.comp .fst) (.const [])
        (Primrec.option_casesOn (htokToTerm.comp (Primrec.fst.comp (Primrec.snd.comp .fst)))
          (.const [])
          (Primrec.list_cons.comp
            (primrec_oform_eq.comp (Primrec.snd.comp .fst) .snd)
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp .fst)))).to₂).to₂).of_eq fun q => by
        dsimp only; cases tokToTerm q.1 <;> cases tokToTerm q.2.1 <;> rfl
    have hleBranch : Primrec₂ (fun (r : List OForm) (l : List ℕ) =>
        match l with
        | _ :: tok₁ :: tok₂ :: _ =>
          match tokToTerm tok₁, tokToTerm tok₂ with
          | some t₁, some t₂ => OForm.le t₁ t₂ :: r
          | _, _ => []
        | _ => []) :=
      Primrec₂.mk ((Primrec.list_casesOn .snd (.const [])
        (Primrec.list_casesOn (Primrec.snd.comp .snd) (.const [])
          (Primrec.list_casesOn (Primrec.snd.comp .snd) (.const [])
            (hmkLe.comp (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp .fst))
              (Primrec.pair (Primrec.fst.comp .snd)
                (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp .fst)))))).to₂).to₂).to₂).of_eq
        fun ⟨r, l⟩ => by rcases l with _ | ⟨_, _ | ⟨tok₁, _ | ⟨tok₂, _⟩⟩⟩ <;> rfl)
    have heqBranch : Primrec₂ (fun (q : ℕ × List OForm) (l : List ℕ) =>
        match l with
        | tok₂ :: _ =>
          match tokToTerm q.1, tokToTerm tok₂ with
          | some t₁, some t₂ => OForm.eq t₁ t₂ :: q.2
          | _, _ => []
        | [] => []) :=
      Primrec₂.mk ((Primrec.list_casesOn .snd (.const [])
        (hmkEq.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp .fst))
          (Primrec.pair (Primrec.fst.comp .snd) (Primrec.snd.comp (Primrec.fst.comp .fst))))).to₂).of_eq
        fun ⟨q, l⟩ => by cases l <;> rfl)
    exact Primrec₂.mk ((Primrec.list_casesOn .fst (.const [])
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp .snd) (.const 3))
        (himpR.comp (hr.comp .fst))
        (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp .snd) (.const 7))
          (hallR.comp (hr.comp .fst))
          (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp .snd) (.const 5))
            (hleBranch.comp (hr.comp .fst) (Primrec.snd.comp .snd))
            (Primrec.ite
              (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.fst.comp .snd) (.const 2)) (.const 0))
              (heqBranch.comp (Primrec.pair (Primrec.fst.comp .snd) (hr.comp .fst))
                (Primrec.snd.comp .snd))
              (Primrec.list_cons.comp (.const OForm.bot) (hr.comp .fst)))))).to₂).of_eq
      fun ⟨xs, rs⟩ => by cases xs <;> rfl)
  refine Primrec.nat_omega_rec' decodeFormList
    (m := List.length) (l := child) (g := step)
    Primrec.list_length hchild hstep ?_ ?_
  · intro xs ys hmem
    cases xs with
    | nil => simp [child] at hmem
    | cons tok l =>
      dsimp only [child] at hmem
      split_ifs at hmem with h37 h5 hlen3 heven hlen1
      · simp only [List.mem_singleton] at hmem; subst hmem; simp
      · simp only [List.mem_singleton] at hmem; subst hmem; simp; omega
      · simp at hmem
      · simp only [List.mem_singleton] at hmem; subst hmem; simp
      · simp at hmem
      · simp only [List.mem_singleton] at hmem; subst hmem; simp
  · intro xs
    cases xs with
    | nil => simp [child, step, decodeFormList]
    | cons tok l =>
      conv_rhs => rw [decodeFormList.eq_def]
      by_cases h3 : tok = 3
      · subst h3; simp [child, step]
      · by_cases h7 : tok = 7
        · subst h7; simp [child, step]
        · by_cases h5 : tok = 5
          · subst h5
            cases l with
            | nil => simp [child, step]
            | cons a l1 => cases l1 with
              | nil => simp [child, step]
              | cons tok₁ l2 => cases l2 with
                | nil => simp [child, step]
                | cons tok₂ l3 => simp [child, step, tokToTerm]
          · by_cases heven : tok % 2 = 0
            · cases l with
              | nil => simp [child, step, h3, h7, h5, heven]
              | cons tok₂ rest => simp [child, step, h3, h7, h5, heven, tokToTerm]
            · simp [child, step, h3, h7, h5, heven]

lemma primrec_decodeMathlibSent : Primrec decodeMathlibSent :=
  Primrec.list_head?.comp (primrec_decodeFormList.comp (Primrec.ofNat (List ℕ)))

lemma decodeFormList_mathlibFormTokens : ∀ {d : ℕ} (φ : LO.BoundedFormula Empty d) (rest : List ℕ),
    decodeFormList (mathlibFormTokens d (ofMathlibForm φ) ++ rest) =
      ofMathlibForm φ :: decodeFormList rest := by
  intro d φ
  induction φ with
  | @falsum d =>
    intro rest
    simp only [ofMathlibForm, mathlibFormTokens, List.singleton_append]
    rw [decodeFormList.eq_def]
    have h3 : 4 * d + 11 ≠ 3 := by omega
    have h7 : 4 * d + 11 ≠ 7 := by omega
    have h5 : 4 * d + 11 ≠ 5 := by omega
    have h2 : (4 * d + 11) % 2 ≠ 0 := by omega
    simp [h3, h7, h5, h2]
  | @equal d t₁ t₂ =>
    intro rest
    simp only [ofMathlibForm, mathlibFormTokens, List.cons_append, List.nil_append,
      mathlibCodeTerm_ofMathlibTerm]
    rw [decodeFormList.eq_def]
    have h3 : 2 * Nat.pair d (Encodable.encode t₁) ≠ 3 := by omega
    have h7 : 2 * Nat.pair d (Encodable.encode t₁) ≠ 7 := by omega
    have h5 : 2 * Nat.pair d (Encodable.encode t₁) ≠ 5 := by omega
    have h2 : (2 * Nat.pair d (Encodable.encode t₁)) % 2 = 0 := by omega
    simp [h3, h7, h5, h2, Nat.unpair_pair, decodeMathlibTerm_encode]
  | @rel d l R ts =>
    intro rest
    rcases R with R | R
    · exact Empty.elim R
    · cases R
      simp only [ofMathlibForm, mathlibFormTokens, List.cons_append, List.nil_append]
      rw [decodeFormList.eq_def]
      simp [Nat.unpair_pair, mathlibCodeTerm_ofMathlibTerm, decodeMathlibTerm_encode]
  | imp φ₁ φ₂ ih₁ ih₂ =>
    intro rest
    simp only [ofMathlibForm, mathlibFormTokens, List.cons_append, List.append_assoc]
    rw [decodeFormList.eq_def]
    simp [ih₁, ih₂]
  | all φ ih =>
    intro rest
    simp only [ofMathlibForm, mathlibFormTokens, List.cons_append]
    rw [decodeFormList.eq_def]
    simp [ih]

lemma decodeMathlibSent_encode (φ : LO.Sentence) :
    decodeMathlibSent (Encodable.encode φ) = some (ofMathlibForm φ) := by
  unfold decodeMathlibSent
  rw [← mathlibCodeSent_ofMathlibForm φ, mathlibCodeSent, Denumerable.ofNat_encode]
  have h := decodeFormList_mathlibFormTokens φ []
  simp only [List.append_nil] at h
  simp [h]

/- ### 11. Linearized sequent-proof verifier (`checkDeriv`) -/

abbrev PStep := (List OForm × List OForm) × (ℕ × ℕ × ℕ) × (List OForm × List OTerm)

def listMem {α : Type*} [DecidableEq α] (x : α) (l : List α) : Bool :=
  l.foldr (fun y b => decide (x = y) || b) false

lemma listMem_eq_true {α : Type*} [DecidableEq α] (x : α) (l : List α) :
    listMem x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [listMem]
  | cons a l ih =>
    simp only [listMem, List.foldr_cons, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    exact or_congr_right ih

lemma primrec_listMem {α : Type*} [Primcodable α] [DecidableEq α] :
    Primrec₂ (listMem (α := α)) :=
  (Primrec.list_foldr .snd (.const false)
    (Primrec.or.comp
      (Primrec.eq.comp (Primrec.fst.comp .fst) (Primrec.fst.comp .snd)).decide
      (Primrec.snd.comp .snd)).to₂).to₂

lemma primrec_list_all {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).all (p a)) := by
  have h : Primrec (fun a => (f a).foldr (fun x b => p a x && b) true) :=
    Primrec.list_foldr hf (.const true)
      (Primrec.and.comp (hp.comp .fst (Primrec.fst.comp .snd)) (Primrec.snd.comp .snd)).to₂
  refine h.of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons x l ih => simp [List.all_cons, ih]

def hasPrem (steps : List PStep) (k i : ℕ) (Γ' Δ' : List OForm) : Bool :=
  decide (i < k) &&
    match steps[i]? with
    | some ((Γ₀, Δ₀), _, _) => decide (Γ₀ = Γ') && decide (Δ₀ = Δ')
    | none => false

lemma hasPrem_eq_true (steps : List PStep) (k i : ℕ) (Γ' Δ' : List OForm) :
    hasPrem steps k i Γ' Δ' = true ↔
      i < k ∧ ∃ rest, steps[i]? = some ((Γ', Δ'), rest) := by
  unfold hasPrem
  cases h : steps[i]? with
  | none => simp
  | some s =>
    rcases s with ⟨⟨Γ₀, Δ₀⟩, rest⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨hlt, rfl, rfl⟩; exact ⟨hlt, rest, ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨hlt, _, ⟨rfl, rfl⟩, _⟩; exact ⟨hlt, rfl, rfl⟩

lemma primrec_hasPrem :
    Primrec (fun q : (List PStep × ℕ × ℕ) × (List OForm × List OForm) =>
      hasPrem q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2) := by
  have hopt : Primrec (fun q : (List PStep × ℕ × ℕ) × (List OForm × List OForm) =>
      Option.casesOn (motive := fun _ => Bool) (q.1.1[q.1.2.2]?) false fun s =>
        decide (s.1.1 = q.2.1) && decide (s.1.2 = q.2.2)) :=
    Primrec.option_casesOn
      (Primrec.list_getElem?.comp (Primrec.fst.comp .fst) (Primrec.snd.comp (Primrec.snd.comp .fst)))
      (.const false)
      (Primrec.and.comp
        (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp .snd))
          (Primrec.fst.comp (Primrec.snd.comp .fst))).decide
        (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp .snd))
          (Primrec.snd.comp (Primrec.snd.comp .fst))).decide).to₂
  refine (Primrec.and.comp
    (Primrec.nat_lt.comp (Primrec.snd.comp (Primrec.snd.comp .fst))
      (Primrec.fst.comp (Primrec.snd.comp .fst))).decide
    hopt).of_eq fun ⟨⟨steps, k, i⟩, ⟨Γ', Δ'⟩⟩ => ?_
  unfold hasPrem
  cases steps[i]? with
  | none => rfl
  | some s => rcases s with ⟨⟨_, _⟩, _, _⟩; rfl

def checkStepBody (steps : List PStep) (k : ℕ) (s : PStep) : Bool :=
  let Γ := s.1.1
  let Δ := s.1.2
  let tag := s.2.1.1
  let i₁ := s.2.1.2.1
  let i₂ := s.2.1.2.2
  let fs := s.2.2.1
  let ts := s.2.2.2
  let f0 := fs.getD 0 OForm.bot
  let f1 := fs.getD 1 OForm.bot
  let t0 := ts.getD 0 OTerm.zero
  let t1 := ts.getD 1 OTerm.zero
  let t2 := ts.getD 2 OTerm.zero
  let t3 := ts.getD 3 OTerm.zero
  if tag = 0 then listMem f0 Γ && listMem f0 Δ
  else if tag = 1 then listMem OForm.bot Γ
  else if tag = 2 then
    listMem (OForm.imp f0 f1) Γ && hasPrem steps k i₁ Γ (f0 :: Δ) && hasPrem steps k i₂ (f1 :: Γ) Δ
  else if tag = 3 then
    listMem (OForm.imp f0 f1) Δ && hasPrem steps k i₁ (f0 :: Γ) (f1 :: Δ)
  else if tag = 4 then
    listMem (OForm.all f0) Γ && noBVar t0 && hasPrem steps k i₁ (substForm0 t0 f0 :: Γ) Δ
  else if tag = 5 then
    listMem (OForm.all f0) Δ && Γ.all (freshInForm i₂) && Δ.all (freshInForm i₂) &&
      hasPrem steps k i₁ Γ (substForm0 (OTerm.fvar i₂) f0 :: Δ)
  else if tag = 6 then
    noBVar t0 && hasPrem steps k i₁ (OForm.eq t0 t0 :: Γ) Δ
  else if tag = 7 then
    listMem (OForm.eq t0 t1) Γ && hasPrem steps k i₁ (OForm.eq t1 t0 :: Γ) Δ
  else if tag = 8 then
    listMem (OForm.eq t0 t1) Γ && listMem (OForm.eq t1 t2) Γ &&
      hasPrem steps k i₁ (OForm.eq t0 t2 :: Γ) Δ
  else if tag = 9 then
    listMem (OForm.eq t0 t1) Γ &&
      hasPrem steps k i₁ (OForm.eq (OTerm.neg t0) (OTerm.neg t1) :: Γ) Δ
  else if tag = 10 then
    listMem (OForm.eq t0 t1) Γ && listMem (OForm.eq t2 t3) Γ &&
      hasPrem steps k i₁ (OForm.eq (OTerm.add t0 t2) (OTerm.add t1 t3) :: Γ) Δ
  else if tag = 11 then
    listMem (OForm.eq t0 t1) Γ && listMem (OForm.eq t2 t3) Γ &&
      hasPrem steps k i₁ (OForm.eq (OTerm.mul t0 t2) (OTerm.mul t1 t3) :: Γ) Δ
  else if tag = 12 then
    listMem (OForm.eq t0 t1) Γ && listMem (OForm.eq t2 t3) Γ && listMem (OForm.le t0 t2) Γ &&
      hasPrem steps k i₁ (OForm.le t1 t3 :: Γ) Δ
  else false

def checkStep (steps : List PStep) (k : ℕ) : Bool :=
  match steps[k]? with
  | some s => checkStepBody steps k s
  | none => false

def checkDeriv (Γ Δ : List OForm) (steps : List PStep) : Bool :=
  decide (0 < steps.length) &&
    (match steps[steps.length - 1]? with
     | some ((Γ₀, Δ₀), _, _) => decide (Γ₀ = Γ) && decide (Δ₀ = Δ)
     | none => false) &&
    (List.range steps.length).all (checkStep steps)

lemma primrec_checkStepBody :
    Primrec (fun q : List PStep × ℕ × PStep => checkStepBody q.1 q.2.1 q.2.2) := by
  let Q := List PStep × ℕ × PStep
  have hsteps : Primrec (fun q : Q => q.1) := .fst
  have hk : Primrec (fun q : Q => q.2.1) := Primrec.fst.comp .snd
  have hs : Primrec (fun q : Q => q.2.2) := Primrec.snd.comp .snd
  have hΓ : Primrec (fun q : Q => q.2.2.1.1) := Primrec.fst.comp (Primrec.fst.comp hs)
  have hΔ : Primrec (fun q : Q => q.2.2.1.2) := Primrec.snd.comp (Primrec.fst.comp hs)
  have htag : Primrec (fun q : Q => q.2.2.2.1.1) := Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp hs))
  have hi1 : Primrec (fun q : Q => q.2.2.2.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp hs)))
  have hi2 : Primrec (fun q : Q => q.2.2.2.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp hs)))
  have hfs : Primrec (fun q : Q => q.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hs))
  have hts : Primrec (fun q : Q => q.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hs))
  have hf0 : Primrec (fun q : Q => q.2.2.2.2.1.getD 0 OForm.bot) :=
    (Primrec.list_getD OForm.bot).comp hfs (.const 0)
  have hf1 : Primrec (fun q : Q => q.2.2.2.2.1.getD 1 OForm.bot) :=
    (Primrec.list_getD OForm.bot).comp hfs (.const 1)
  have ht0 : Primrec (fun q : Q => q.2.2.2.2.2.getD 0 OTerm.zero) :=
    (Primrec.list_getD OTerm.zero).comp hts (.const 0)
  have ht1 : Primrec (fun q : Q => q.2.2.2.2.2.getD 1 OTerm.zero) :=
    (Primrec.list_getD OTerm.zero).comp hts (.const 1)
  have ht2 : Primrec (fun q : Q => q.2.2.2.2.2.getD 2 OTerm.zero) :=
    (Primrec.list_getD OTerm.zero).comp hts (.const 2)
  have ht3 : Primrec (fun q : Q => q.2.2.2.2.2.getD 3 OTerm.zero) :=
    (Primrec.list_getD OTerm.zero).comp hts (.const 3)
  have mkP1 : ∀ {L R : Q → List OForm}, Primrec L → Primrec R →
      Primrec (fun q : Q => hasPrem q.1 q.2.1 q.2.2.2.1.2.1 (L q) (R q)) :=
    fun hL hR => primrec_hasPrem.comp (Primrec.pair (Primrec.pair hsteps (Primrec.pair hk hi1)) (Primrec.pair hL hR))
  have mkP2 : ∀ {L R : Q → List OForm}, Primrec L → Primrec R →
      Primrec (fun q : Q => hasPrem q.1 q.2.1 q.2.2.2.1.2.2 (L q) (R q)) :=
    fun hL hR => primrec_hasPrem.comp (Primrec.pair (Primrec.pair hsteps (Primrec.pair hk hi2)) (Primrec.pair hL hR))
  have hr0 := Primrec.and.comp (primrec_listMem.comp hf0 hΓ) (primrec_listMem.comp hf0 hΔ)
  have hr1 := primrec_listMem.comp (.const OForm.bot) hΓ
  have hr2 := Primrec.and.comp
    (Primrec.and.comp (primrec_listMem.comp (primrec_oform_imp.comp hf0 hf1) hΓ)
      (mkP1 hΓ (Primrec.list_cons.comp hf0 hΔ)))
    (mkP2 (Primrec.list_cons.comp hf1 hΓ) hΔ)
  have hr3 := Primrec.and.comp
    (primrec_listMem.comp (primrec_oform_imp.comp hf0 hf1) hΔ)
    (mkP1 (Primrec.list_cons.comp hf0 hΓ) (Primrec.list_cons.comp hf1 hΔ))
  have hr4 := Primrec.and.comp
    (Primrec.and.comp (primrec_listMem.comp (primrec_oform_all.comp hf0) hΓ)
      (primrec_noBVar.comp ht0))
    (mkP1 (Primrec.list_cons.comp (primrec_substForm0.comp ht0 hf0) hΓ) hΔ)
  have hr5 := Primrec.and.comp
    (Primrec.and.comp
      (Primrec.and.comp (primrec_listMem.comp (primrec_oform_all.comp hf0) hΔ)
        (primrec_list_all hΓ (primrec_freshInForm.comp (hi2.comp .fst) .snd).to₂))
      (primrec_list_all hΔ (primrec_freshInForm.comp (hi2.comp .fst) .snd).to₂))
    (mkP1 hΓ (Primrec.list_cons.comp (primrec_substForm0.comp (primrec_oterm_fvar.comp hi2) hf0) hΔ))
  have hr6 := Primrec.and.comp (primrec_noBVar.comp ht0)
    (mkP1 (Primrec.list_cons.comp (primrec_oform_eq.comp ht0 ht0) hΓ) hΔ)
  have hr7 := Primrec.and.comp (primrec_listMem.comp (primrec_oform_eq.comp ht0 ht1) hΓ)
    (mkP1 (Primrec.list_cons.comp (primrec_oform_eq.comp ht1 ht0) hΓ) hΔ)
  have hr8 := Primrec.and.comp
    (Primrec.and.comp (primrec_listMem.comp (primrec_oform_eq.comp ht0 ht1) hΓ)
      (primrec_listMem.comp (primrec_oform_eq.comp ht1 ht2) hΓ))
    (mkP1 (Primrec.list_cons.comp (primrec_oform_eq.comp ht0 ht2) hΓ) hΔ)
  have hr9 := Primrec.and.comp (primrec_listMem.comp (primrec_oform_eq.comp ht0 ht1) hΓ)
    (mkP1 (Primrec.list_cons.comp
      (primrec_oform_eq.comp (primrec_oterm_neg.comp ht0) (primrec_oterm_neg.comp ht1)) hΓ) hΔ)
  have hr10 := Primrec.and.comp
    (Primrec.and.comp (primrec_listMem.comp (primrec_oform_eq.comp ht0 ht1) hΓ)
      (primrec_listMem.comp (primrec_oform_eq.comp ht2 ht3) hΓ))
    (mkP1 (Primrec.list_cons.comp
      (primrec_oform_eq.comp (primrec_oterm_add.comp ht0 ht2) (primrec_oterm_add.comp ht1 ht3)) hΓ) hΔ)
  have hr11 := Primrec.and.comp
    (Primrec.and.comp (primrec_listMem.comp (primrec_oform_eq.comp ht0 ht1) hΓ)
      (primrec_listMem.comp (primrec_oform_eq.comp ht2 ht3) hΓ))
    (mkP1 (Primrec.list_cons.comp
      (primrec_oform_eq.comp (primrec_oterm_mul.comp ht0 ht2) (primrec_oterm_mul.comp ht1 ht3)) hΓ) hΔ)
  have hr12 := Primrec.and.comp
    (Primrec.and.comp
      (Primrec.and.comp (primrec_listMem.comp (primrec_oform_eq.comp ht0 ht1) hΓ)
        (primrec_listMem.comp (primrec_oform_eq.comp ht2 ht3) hΓ))
      (primrec_listMem.comp (primrec_oform_le.comp ht0 ht2) hΓ))
    (mkP1 (Primrec.list_cons.comp (primrec_oform_le.comp ht1 ht3) hΓ) hΔ)
  unfold checkStepBody
  exact Primrec.ite (Primrec.eq.comp htag (.const 0)) hr0
    (Primrec.ite (Primrec.eq.comp htag (.const 1)) hr1
    (Primrec.ite (Primrec.eq.comp htag (.const 2)) hr2
    (Primrec.ite (Primrec.eq.comp htag (.const 3)) hr3
    (Primrec.ite (Primrec.eq.comp htag (.const 4)) hr4
    (Primrec.ite (Primrec.eq.comp htag (.const 5)) hr5
    (Primrec.ite (Primrec.eq.comp htag (.const 6)) hr6
    (Primrec.ite (Primrec.eq.comp htag (.const 7)) hr7
    (Primrec.ite (Primrec.eq.comp htag (.const 8)) hr8
    (Primrec.ite (Primrec.eq.comp htag (.const 9)) hr9
    (Primrec.ite (Primrec.eq.comp htag (.const 10)) hr10
    (Primrec.ite (Primrec.eq.comp htag (.const 11)) hr11
    (Primrec.ite (Primrec.eq.comp htag (.const 12)) hr12
      (.const false)))))))))))))

lemma primrec_checkStep : Primrec₂ checkStep := by
  refine Primrec₂.mk ((Primrec.option_casesOn
    (Primrec.list_getElem?.comp .fst .snd) (.const false)
    (primrec_checkStepBody.comp (Primrec.pair (Primrec.fst.comp .fst)
      (Primrec.pair (Primrec.snd.comp .fst) .snd))).to₂).of_eq fun ⟨steps, k⟩ => ?_)
  unfold checkStep
  cases steps[k]? <;> rfl

lemma primrec_checkDeriv :
    Primrec (fun q : List OForm × List OForm × List PStep => checkDeriv q.1 q.2.1 q.2.2) := by
  have hsteps : Primrec (fun q : List OForm × List OForm × List PStep => q.2.2) :=
    Primrec.snd.comp .snd
  have hlast : Primrec (fun q : List OForm × List OForm × List PStep =>
      Option.casesOn (motive := fun _ => Bool) (q.2.2[q.2.2.length - 1]?) false fun s =>
        decide (s.1.1 = q.1) && decide (s.1.2 = q.2.1)) :=
    Primrec.option_casesOn
      (Primrec.list_getElem?.comp hsteps (Primrec.pred.comp (Primrec.list_length.comp hsteps)))
      (.const false)
      (Primrec.and.comp
        (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp .snd)) (Primrec.fst.comp .fst)).decide
        (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp .snd))
          (Primrec.fst.comp (Primrec.snd.comp .fst))).decide).to₂
  have hall := primrec_list_all (Primrec.list_range.comp (Primrec.list_length.comp hsteps))
    (primrec_checkStep.comp (hsteps.comp .fst) .snd).to₂
  refine (Primrec.and.comp
    (Primrec.and.comp
      (Primrec.nat_lt.comp (.const 0) (Primrec.list_length.comp hsteps)).decide hlast)
    hall).of_eq fun ⟨Γ, Δ, steps⟩ => ?_
  unfold checkDeriv
  cases steps[steps.length - 1]? with
  | none => rfl
  | some s => rcases s with ⟨⟨_, _⟩, _, _⟩; rfl

lemma deriv_of_checkAll {steps : List PStep}
    (hall : (List.range steps.length).all (checkStep steps) = true) :
    ∀ {k : ℕ}, k < steps.length → ∀ {s : PStep},
      steps[k]? = some s → Deriv s.1.1 s.1.2 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk s hs
    have hck : checkStep steps k = true := by
      rw [List.all_eq_true] at hall
      exact hall k (List.mem_range.2 hk)
    unfold checkStep at hck
    rw [hs] at hck
    dsimp only at hck
    unfold checkStepBody at hck
    dsimp only at hck
    rcases htag : s.2.1.1 with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | tag <;>
      rw [htag] at hck
    · simp only [↓reduceIte, Bool.and_eq_true, listMem_eq_true] at hck
      exact Deriv.ax_id hck.1 hck.2
    · simp only [Nat.zero_add, Nat.reduceEqDiff, ↓reduceIte, listMem_eq_true] at hck
      exact Deriv.ax_bot hck
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte,
        Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true] at hck
      rcases hck with ⟨⟨hmem, hi1, r1, hr1⟩, hi2, r2, hr2⟩
      exact Deriv.imp_L hmem (ih _ hi1 (hi1.trans hk) hr1) (ih _ hi2 (hi2.trans hk) hr2)
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte,
        Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true] at hck
      rcases hck with ⟨hmem, hi1, r1, hr1⟩
      exact Deriv.imp_R hmem (ih _ hi1 (hi1.trans hk) hr1)
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte,
        Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true] at hck
      rcases hck with ⟨⟨hmem, hnb⟩, hi1, r1, hr1⟩
      exact Deriv.all_L hmem hnb (ih _ hi1 (hi1.trans hk) hr1)
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte,
        Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true, List.all_eq_true] at hck
      rcases hck with ⟨⟨⟨hmem, hfrΓ⟩, hfrΔ⟩, hi1, r1, hr1⟩
      exact Deriv.all_R hmem hfrΓ hfrΔ (ih _ hi1 (hi1.trans hk) hr1)
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte,
        Bool.and_eq_true, hasPrem_eq_true] at hck
      rcases hck with ⟨hnb, hi1, r1, hr1⟩
      exact Deriv.eq_refl hnb (ih _ hi1 (hi1.trans hk) hr1)
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte,
        Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true] at hck
      rcases hck with ⟨hmem, hi1, r1, hr1⟩
      exact Deriv.eq_symm hmem (ih _ hi1 (hi1.trans hk) hr1)
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte,
        Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true] at hck
      rcases hck with ⟨⟨hm1, hm2⟩, hi1, r1, hr1⟩
      exact Deriv.eq_trans hm1 hm2 (ih _ hi1 (hi1.trans hk) hr1)
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte,
        Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true] at hck
      rcases hck with ⟨hmem, hi1, r1, hr1⟩
      exact Deriv.eq_neg hmem (ih _ hi1 (hi1.trans hk) hr1)
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte,
        Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true] at hck
      rcases hck with ⟨⟨hm1, hm2⟩, hi1, r1, hr1⟩
      exact Deriv.eq_add hm1 hm2 (ih _ hi1 (hi1.trans hk) hr1)
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte,
        Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true] at hck
      rcases hck with ⟨⟨hm1, hm2⟩, hi1, r1, hr1⟩
      exact Deriv.eq_mul hm1 hm2 (ih _ hi1 (hi1.trans hk) hr1)
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte,
        Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true] at hck
      rcases hck with ⟨⟨⟨hm1, hm2⟩, hm3⟩, hi1, r1, hr1⟩
      exact Deriv.eq_le hm1 hm2 hm3 (ih _ hi1 (hi1.trans hk) hr1)
    · simp only [show tag + 13 ≠ 0 by omega, show tag + 13 ≠ 1 by omega,
        show tag + 13 ≠ 2 by omega, show tag + 13 ≠ 3 by omega,
        show tag + 13 ≠ 4 by omega, show tag + 13 ≠ 5 by omega,
        show tag + 13 ≠ 6 by omega, show tag + 13 ≠ 7 by omega,
        show tag + 13 ≠ 8 by omega, show tag + 13 ≠ 9 by omega,
        show tag + 13 ≠ 10 by omega, show tag + 13 ≠ 11 by omega,
        show tag + 13 ≠ 12 by omega, ↓reduceIte] at hck
      cases hck

theorem deriv_of_checkDeriv {Γ Δ : List OForm} {steps : List PStep}
    (h : checkDeriv Γ Δ steps = true) : Deriv Γ Δ := by
  unfold checkDeriv at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨hlen, hlast⟩, hall⟩
  cases hs : steps[steps.length - 1]? with
  | none => simp [hs] at hlast
  | some s =>
    rcases s with ⟨⟨Γ₀, Δ₀⟩, rest⟩
    rw [hs] at hlast
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hlast
    rcases hlast with ⟨rfl, rfl⟩
    exact deriv_of_checkAll hall (by omega) hs

def shiftStep (d : ℕ) (s : PStep) : PStep :=
  (s.1, (s.2.1.1, s.2.1.2.1 + d, if s.2.1.1 = 2 then s.2.1.2.2 + d else s.2.1.2.2), s.2.2)

lemma hasPrem_congr {steps₁ steps₂ : List PStep} {k i : ℕ} {Γ' Δ' : List OForm}
    (h : ∀ j < k, steps₁[j]? = steps₂[j]?) :
    hasPrem steps₁ k i Γ' Δ' = hasPrem steps₂ k i Γ' Δ' := by
  unfold hasPrem
  by_cases hik : i < k
  · simp [hik, h i hik]
  · simp [hik]

lemma checkStepBody_congr {steps₁ steps₂ : List PStep} {k : ℕ} {s : PStep}
    (h : ∀ j < k, steps₁[j]? = steps₂[j]?) :
    checkStepBody steps₁ k s = checkStepBody steps₂ k s := by
  unfold checkStepBody
  simp only [hasPrem_congr h]

lemma hasPrem_shift {steps₁ steps₂ : List PStep} {k i : ℕ} {Γ' Δ' : List OForm} :
    hasPrem (steps₁ ++ steps₂.map (shiftStep steps₁.length))
      (steps₁.length + k) (i + steps₁.length) Γ' Δ' =
    hasPrem steps₂ k i Γ' Δ' := by
  unfold hasPrem
  have hlt : decide (i + steps₁.length < steps₁.length + k) = decide (i < k) := by
    by_cases h : i < k <;> simp [h] <;> omega
  rw [hlt]
  have hget : (steps₁ ++ steps₂.map (shiftStep steps₁.length))[i + steps₁.length]? =
      (steps₂[i]?).map (shiftStep steps₁.length) := by
    rw [List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel, List.getElem?_map]
  rw [hget]
  cases steps₂[i]? with
  | none => rfl
  | some s => rcases s with ⟨⟨_, _⟩, _, _⟩; rfl

lemma checkStepBody_shift {steps₁ steps₂ : List PStep} {k : ℕ} {s : PStep} :
    checkStepBody (steps₁ ++ steps₂.map (shiftStep steps₁.length))
      (steps₁.length + k) (shiftStep steps₁.length s) =
    checkStepBody steps₂ k s := by
  change checkStepBody (steps₁ ++ steps₂.map (shiftStep steps₁.length)) (steps₁.length + k)
      (s.1, (s.2.1.1, s.2.1.2.1 + steps₁.length,
        if s.2.1.1 = 2 then s.2.1.2.2 + steps₁.length else s.2.1.2.2), s.2.2) =
    checkStepBody steps₂ k s
  unfold checkStepBody
  dsimp only
  by_cases h2 : s.2.1.1 = 2
  · simp only [h2, Nat.reduceEqDiff, ↓reduceIte, hasPrem_shift]
  · simp only [h2, ↓reduceIte, hasPrem_shift]

lemma checkAll_snoc {steps : List PStep} {s : PStep}
    (hall : (List.range steps.length).all (checkStep steps) = true)
    (hlast : checkStepBody (steps ++ [s]) steps.length s = true) :
    (List.range (steps ++ [s]).length).all (checkStep (steps ++ [s])) = true := by
  rw [List.all_eq_true] at hall ⊢
  intro k hk
  simp only [List.mem_range, List.length_append, List.length_singleton] at hk
  by_cases hlt : k < steps.length
  · have hck := hall k (List.mem_range.2 hlt)
    unfold checkStep at hck ⊢
    rw [List.getElem?_append_left hlt]
    cases hs : steps[k]? with
    | none => simp [hs] at hck
    | some s' =>
      rw [hs] at hck
      dsimp only at hck ⊢
      rw [← checkStepBody_congr (steps₁ := steps) (steps₂ := steps ++ [s])]
      · exact hck
      · intro j hj; exact (List.getElem?_append_left (hj.trans hlt)).symm
  · have hkeq : k = steps.length := by omega
    subst hkeq
    unfold checkStep
    simp [hlast]

lemma checkAll_append_shift {steps₁ steps₂ : List PStep}
    (h₁ : (List.range steps₁.length).all (checkStep steps₁) = true)
    (h₂ : (List.range steps₂.length).all (checkStep steps₂) = true) :
    (List.range (steps₁ ++ steps₂.map (shiftStep steps₁.length)).length).all
      (checkStep (steps₁ ++ steps₂.map (shiftStep steps₁.length))) = true := by
  rw [List.all_eq_true] at h₁ h₂ ⊢
  intro k hk
  simp only [List.mem_range, List.length_append, List.length_map] at hk
  by_cases hlt : k < steps₁.length
  · have hck := h₁ k (List.mem_range.2 hlt)
    unfold checkStep at hck ⊢
    rw [List.getElem?_append_left hlt]
    cases hs : steps₁[k]? with
    | none => simp [hs] at hck
    | some s' =>
      rw [hs] at hck
      dsimp only at hck ⊢
      rw [← checkStepBody_congr (steps₁ := steps₁)]
      · exact hck
      · intro j hj; exact (List.getElem?_append_left (hj.trans hlt)).symm
  · have hge : steps₁.length ≤ k := Nat.le_of_not_lt hlt
    let j := k - steps₁.length
    have hjlt : j < steps₂.length := by omega
    have hk_eq : k = steps₁.length + j := by omega
    have hcj := h₂ j (List.mem_range.2 hjlt)
    unfold checkStep at hcj ⊢
    rw [hk_eq, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.getElem?_map]
    cases hs : steps₂[j]? with
    | none => simp [hs] at hcj
    | some s' =>
      rw [hs] at hcj
      dsimp only at hcj ⊢
      simp only [Option.map_some]
      rw [checkStepBody_shift]
      exact hcj

lemma checkDeriv_append_step {Γ Δ : List OForm} {steps : List PStep} {s : PStep}
    (hseq : s.1 = (Γ, Δ))
    (hall : (List.range steps.length).all (checkStep steps) = true)
    (hbody : checkStepBody (steps ++ [s]) steps.length s = true) :
    checkDeriv Γ Δ (steps ++ [s]) = true := by
  unfold checkDeriv
  have hlen : (steps ++ [s]).length = steps.length + 1 := by simp
  have hlast : (steps ++ [s])[(steps ++ [s]).length - 1]? = some s := by
    simp [hlen]
  rcases s with ⟨⟨Γ₀, Δ₀⟩, rest⟩
  simp only [Prod.mk.injEq] at hseq
  rcases hseq with ⟨rfl, rfl⟩
  rw [hlast, checkAll_snoc hall hbody]
  simp [hlen]

lemma checkDeriv_unpack {Γ Δ : List OForm} {steps : List PStep}
    (h : checkDeriv Γ Δ steps = true) :
    0 < steps.length ∧
    (∃ rest, steps[steps.length - 1]? = some ((Γ, Δ), rest)) ∧
    (List.range steps.length).all (checkStep steps) = true := by
  unfold checkDeriv at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨hlen, hlast⟩, hall⟩
  cases hs : steps[steps.length - 1]? with
  | none => simp [hs] at hlast
  | some s =>
    rcases s with ⟨⟨Γ₀, Δ₀⟩, rest⟩
    rw [hs] at hlast
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hlast
    rcases hlast with ⟨rfl, rfl⟩
    exact ⟨hlen, ⟨rest, rfl⟩, hall⟩

theorem exists_checkDeriv_of_deriv {Γ Δ : List OForm} (hd : Deriv Γ Δ) :
    ∃ steps : List PStep, checkDeriv Γ Δ steps = true := by
  induction hd with
  | @ax_id Γ Δ φ hΓ hΔ =>
    refine ⟨[((Γ, Δ), (0, 0, 0), ([φ], []))], ?_⟩
    exact checkDeriv_append_step (steps := []) rfl rfl
      (by simp [checkStepBody, listMem_eq_true, hΓ, hΔ])
  | @ax_bot Γ Δ hΓ =>
    refine ⟨[((Γ, Δ), (1, 0, 0), ([], []))], ?_⟩
    exact checkDeriv_append_step (steps := []) rfl rfl
      (by simp [checkStepBody, listMem_eq_true, hΓ])
  | @imp_L Γ Δ φ ψ hmem _ _ ih₁ ih₂ =>
    obtain ⟨s₁, hs₁⟩ := ih₁
    obtain ⟨s₂, hs₂⟩ := ih₂
    obtain ⟨hl₁, ⟨r₁, hr₁⟩, ha₁⟩ := checkDeriv_unpack hs₁
    obtain ⟨hl₂, ⟨r₂, hr₂⟩, ha₂⟩ := checkDeriv_unpack hs₂
    let pref := s₁ ++ s₂.map (shiftStep s₁.length)
    let step : PStep := ((Γ, Δ), (2, s₁.length - 1, s₁.length + (s₂.length - 1)), ([φ, ψ], []))
    refine ⟨pref ++ [step], checkDeriv_append_step rfl (checkAll_append_shift ha₁ ha₂) ?_⟩
    have hlt1 : s₁.length - 1 < pref.length := by simp [pref]; omega
    have hlt2 : s₁.length + (s₂.length - 1) < pref.length := by simp [pref]; omega
    have hg1 : (pref ++ [step])[s₁.length - 1]? = some ((Γ, φ :: Δ), r₁) := by
      rw [List.getElem?_append_left hlt1, List.getElem?_append_left (by omega), hr₁]
    have hg2 : (pref ++ [step])[s₁.length + (s₂.length - 1)]? =
        some ((ψ :: Γ, Δ), (shiftStep s₁.length ((ψ :: Γ, Δ), r₂)).2) := by
      rw [List.getElem?_append_left hlt2, List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, List.getElem?_map, hr₂]
      rfl
    simp only [checkStepBody, step, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceEqDiff, ↓reduceIte, Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true]
    exact ⟨⟨hmem, hlt1, r₁, hg1⟩, hlt2, _, hg2⟩
  | @imp_R Γ Δ φ ψ hmem _ ih =>
    obtain ⟨s₁, hs₁⟩ := ih
    obtain ⟨hl₁, ⟨r₁, hr₁⟩, ha₁⟩ := checkDeriv_unpack hs₁
    let step : PStep := ((Γ, Δ), (3, s₁.length - 1, 0), ([φ, ψ], []))
    refine ⟨s₁ ++ [step], checkDeriv_append_step rfl ha₁ ?_⟩
    have hlt : s₁.length - 1 < s₁.length := by omega
    have hg : (s₁ ++ [step])[s₁.length - 1]? = some ((φ :: Γ, ψ :: Δ), r₁) := by
      rw [List.getElem?_append_left hlt, hr₁]
    simp only [checkStepBody, step, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceEqDiff, ↓reduceIte, Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true]
    exact ⟨hmem, hlt, r₁, hg⟩
  | @all_L Γ Δ φ t hmem hnb _ ih =>
    obtain ⟨s₁, hs₁⟩ := ih
    obtain ⟨hl₁, ⟨r₁, hr₁⟩, ha₁⟩ := checkDeriv_unpack hs₁
    let step : PStep := ((Γ, Δ), (4, s₁.length - 1, 0), ([φ], [t]))
    refine ⟨s₁ ++ [step], checkDeriv_append_step rfl ha₁ ?_⟩
    have hlt : s₁.length - 1 < s₁.length := by omega
    have hg : (s₁ ++ [step])[s₁.length - 1]? = some ((substForm0 t φ :: Γ, Δ), r₁) := by
      rw [List.getElem?_append_left hlt, hr₁]
    simp only [checkStepBody, step, List.getD_cons_zero,
      Nat.reduceEqDiff, ↓reduceIte, Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true]
    exact ⟨⟨hmem, hnb⟩, hlt, r₁, hg⟩
  | @all_R Γ Δ φ c hmem hfrΓ hfrΔ _ ih =>
    obtain ⟨s₁, hs₁⟩ := ih
    obtain ⟨hl₁, ⟨r₁, hr₁⟩, ha₁⟩ := checkDeriv_unpack hs₁
    let step : PStep := ((Γ, Δ), (5, s₁.length - 1, c), ([φ], []))
    refine ⟨s₁ ++ [step], checkDeriv_append_step rfl ha₁ ?_⟩
    have hlt : s₁.length - 1 < s₁.length := by omega
    have hg : (s₁ ++ [step])[s₁.length - 1]? = some ((Γ, substForm0 (OTerm.fvar c) φ :: Δ), r₁) := by
      rw [List.getElem?_append_left hlt, hr₁]
    simp only [checkStepBody, step, List.getD_cons_zero,
      Nat.reduceEqDiff, ↓reduceIte, Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true,
      List.all_eq_true]
    exact ⟨⟨⟨hmem, hfrΓ⟩, hfrΔ⟩, hlt, r₁, hg⟩
  | @eq_refl Γ Δ t hnb _ ih =>
    obtain ⟨s₁, hs₁⟩ := ih
    obtain ⟨hl₁, ⟨r₁, hr₁⟩, ha₁⟩ := checkDeriv_unpack hs₁
    let step : PStep := ((Γ, Δ), (6, s₁.length - 1, 0), ([], [t]))
    refine ⟨s₁ ++ [step], checkDeriv_append_step rfl ha₁ ?_⟩
    have hlt : s₁.length - 1 < s₁.length := by omega
    have hg : (s₁ ++ [step])[s₁.length - 1]? = some ((OForm.eq t t :: Γ, Δ), r₁) := by
      rw [List.getElem?_append_left hlt, hr₁]
    simp only [checkStepBody, step, List.getD_cons_zero,
      Nat.reduceEqDiff, ↓reduceIte, Bool.and_eq_true, hasPrem_eq_true]
    exact ⟨hnb, hlt, r₁, hg⟩
  | @eq_symm Γ Δ t₁ t₂ hmem _ ih =>
    obtain ⟨s₁, hs₁⟩ := ih
    obtain ⟨hl₁, ⟨r₁, hr₁⟩, ha₁⟩ := checkDeriv_unpack hs₁
    let step : PStep := ((Γ, Δ), (7, s₁.length - 1, 0), ([], [t₁, t₂]))
    refine ⟨s₁ ++ [step], checkDeriv_append_step rfl ha₁ ?_⟩
    have hlt : s₁.length - 1 < s₁.length := by omega
    have hg : (s₁ ++ [step])[s₁.length - 1]? = some ((OForm.eq t₂ t₁ :: Γ, Δ), r₁) := by
      rw [List.getElem?_append_left hlt, hr₁]
    simp only [checkStepBody, step, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceEqDiff, ↓reduceIte, Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true]
    exact ⟨hmem, hlt, r₁, hg⟩
  | @eq_trans Γ Δ t₁ t₂ t₃ hm1 hm2 _ ih =>
    obtain ⟨s₁, hs₁⟩ := ih
    obtain ⟨hl₁, ⟨r₁, hr₁⟩, ha₁⟩ := checkDeriv_unpack hs₁
    let step : PStep := ((Γ, Δ), (8, s₁.length - 1, 0), ([], [t₁, t₂, t₃]))
    refine ⟨s₁ ++ [step], checkDeriv_append_step rfl ha₁ ?_⟩
    have hlt : s₁.length - 1 < s₁.length := by omega
    have hg : (s₁ ++ [step])[s₁.length - 1]? = some ((OForm.eq t₁ t₃ :: Γ, Δ), r₁) := by
      rw [List.getElem?_append_left hlt, hr₁]
    simp only [checkStepBody, step, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceEqDiff, ↓reduceIte, Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true]
    exact ⟨⟨hm1, hm2⟩, hlt, r₁, hg⟩
  | @eq_neg Γ Δ s t hmem _ ih =>
    obtain ⟨s₁, hs₁⟩ := ih
    obtain ⟨hl₁, ⟨r₁, hr₁⟩, ha₁⟩ := checkDeriv_unpack hs₁
    let step : PStep := ((Γ, Δ), (9, s₁.length - 1, 0), ([], [s, t]))
    refine ⟨s₁ ++ [step], checkDeriv_append_step rfl ha₁ ?_⟩
    have hlt : s₁.length - 1 < s₁.length := by omega
    have hg : (s₁ ++ [step])[s₁.length - 1]? = some ((OForm.eq (.neg s) (.neg t) :: Γ, Δ), r₁) := by
      rw [List.getElem?_append_left hlt, hr₁]
    simp only [checkStepBody, step, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceEqDiff, ↓reduceIte, Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true]
    exact ⟨hmem, hlt, r₁, hg⟩
  | @eq_add Γ Δ s₁ t₁ s₂ t₂ hm1 hm2 _ ih =>
    obtain ⟨st, hst⟩ := ih
    obtain ⟨hl, ⟨r, hr⟩, ha⟩ := checkDeriv_unpack hst
    let step : PStep := ((Γ, Δ), (10, st.length - 1, 0), ([], [s₁, t₁, s₂, t₂]))
    refine ⟨st ++ [step], checkDeriv_append_step rfl ha ?_⟩
    have hlt : st.length - 1 < st.length := by omega
    have hg : (st ++ [step])[st.length - 1]? =
        some ((OForm.eq (.add s₁ s₂) (.add t₁ t₂) :: Γ, Δ), r) := by
      rw [List.getElem?_append_left hlt, hr]
    simp only [checkStepBody, step, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceEqDiff, ↓reduceIte, Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true]
    exact ⟨⟨hm1, hm2⟩, hlt, r, hg⟩
  | @eq_mul Γ Δ s₁ t₁ s₂ t₂ hm1 hm2 _ ih =>
    obtain ⟨st, hst⟩ := ih
    obtain ⟨hl, ⟨r, hr⟩, ha⟩ := checkDeriv_unpack hst
    let step : PStep := ((Γ, Δ), (11, st.length - 1, 0), ([], [s₁, t₁, s₂, t₂]))
    refine ⟨st ++ [step], checkDeriv_append_step rfl ha ?_⟩
    have hlt : st.length - 1 < st.length := by omega
    have hg : (st ++ [step])[st.length - 1]? =
        some ((OForm.eq (.mul s₁ s₂) (.mul t₁ t₂) :: Γ, Δ), r) := by
      rw [List.getElem?_append_left hlt, hr]
    simp only [checkStepBody, step, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceEqDiff, ↓reduceIte, Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true]
    exact ⟨⟨hm1, hm2⟩, hlt, r, hg⟩
  | @eq_le Γ Δ s₁ t₁ s₂ t₂ hm1 hm2 hm3 _ ih =>
    obtain ⟨st, hst⟩ := ih
    obtain ⟨hl, ⟨r, hr⟩, ha⟩ := checkDeriv_unpack hst
    let step : PStep := ((Γ, Δ), (12, st.length - 1, 0), ([], [s₁, t₁, s₂, t₂]))
    refine ⟨st ++ [step], checkDeriv_append_step rfl ha ?_⟩
    have hlt : st.length - 1 < st.length := by omega
    have hg : (st ++ [step])[st.length - 1]? = some ((OForm.le t₁ t₂ :: Γ, Δ), r) := by
      rw [List.getElem?_append_left hlt, hr]
    simp only [checkStepBody, step, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceEqDiff, ↓reduceIte, Bool.and_eq_true, listMem_eq_true, hasPrem_eq_true]
    exact ⟨⟨⟨hm1, hm2⟩, hm3⟩, hlt, r, hg⟩

/- ### 12. Computability of witness search and main theorem -/

lemma computable_list_all {α : Type*} [Primcodable α] {p : α → Bool} (hp : Computable p) :
    Computable (fun l : List α => l.all p) := by
  have h : Computable (fun l : List α =>
      Nat.rec (motive := fun _ => Bool) true (fun i acc => acc && (l[i]?.map p).getD true) l.length) :=
    Computable.nat_rec Computable.list_length (Computable.const true)
      (Primrec.and.to_comp.comp
        (Computable.snd.comp Computable.snd)
        (Computable.option_getD
          (Computable.option_map
            (Computable.list_getElem?.comp Computable.fst (Computable.fst.comp Computable.snd))
            (hp.comp Computable.snd).to₂)
          (Computable.const true))).to₂
  refine h.of_eq fun l => ?_
  have haux : ∀ n ≤ l.length,
      Nat.rec (motive := fun _ => Bool) true (fun i acc => acc && (l[i]?.map p).getD true) n =
        (l.take n).all p := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [ih (Nat.le_of_succ_le hn), List.take_succ_eq_append_getElem hn,
        List.all_append, List.all_cons, List.all_nil, Bool.and_true,
        List.getElem?_eq_getElem hn, Option.map_some, Option.getD_some]
  simpa using haux l.length le_rfl

def checkWitness (fT : ℕ → Bool) (n w : ℕ) : Bool :=
  match decodeMathlibSent n with
  | none => true
  | some ψ =>
    if isSentForm 0 ψ && decide (mathlibCodeSent ψ = n) then
      match Encodable.decode (α := List OForm × List PStep × Bool) w with
      | none => false
      | some (T₀, steps, side) =>
        T₀.all (fun θ => isSentForm 0 θ && fT (mathlibCodeSent θ)) &&
        if side then
          checkDeriv (OForm.imp ψ OForm.bot :: T₀) [] steps
        else
          checkDeriv (OForm.imp (OForm.imp ψ OForm.bot) OForm.bot :: T₀) [] steps
    else true

lemma computable_checkWitness {fT : ℕ → Bool} (hfT : Computable fT) :
    Computable (fun p : ℕ × ℕ => checkWitness fT p.1 p.2) := by
  have hmemθ : Computable (fun θ : OForm => isSentForm 0 θ && fT (mathlibCodeSent θ)) :=
    Primrec.and.to_comp.comp
      ((primrec_isSentForm.comp (.const 0) .id).to_comp)
      (hfT.comp primrec_mathlibCodeSent.to_comp)
  have hallT : Computable (fun T₀ : List OForm =>
      T₀.all (fun θ => isSentForm 0 θ && fT (mathlibCodeSent θ))) :=
    computable_list_all hmemθ
  have hinner : Computable₂ (fun (ψ : OForm) (w : ℕ) =>
      Option.casesOn (motive := fun _ => Bool)
        (Encodable.decode (α := List OForm × List PStep × Bool) w) false
        fun x =>
          x.1.all (fun θ => isSentForm 0 θ && fT (mathlibCodeSent θ)) &&
          cond x.2.2
            (checkDeriv (OForm.imp ψ OForm.bot :: x.1) [] x.2.1)
            (checkDeriv (OForm.imp (OForm.imp ψ OForm.bot) OForm.bot :: x.1) [] x.2.1)) :=
    (Computable.option_casesOn (Computable.decode.comp Computable.snd) (Computable.const false)
      (Primrec.and.to_comp.comp
        (hallT.comp (Computable.fst.comp Computable.snd))
        (Computable.cond (Computable.snd.comp (Computable.snd.comp Computable.snd))
          (primrec_checkDeriv.to_comp.comp
            (Computable.pair
              (Computable.list_cons.comp
                (primrec_oform_imp.to_comp.comp (Computable.fst.comp Computable.fst)
                  (Computable.const OForm.bot))
                (Computable.fst.comp Computable.snd))
              (Computable.pair (Computable.const [])
                (Computable.fst.comp (Computable.snd.comp Computable.snd)))))
          (primrec_checkDeriv.to_comp.comp
            (Computable.pair
              (Computable.list_cons.comp
                (primrec_oform_imp.to_comp.comp
                  (primrec_oform_imp.to_comp.comp (Computable.fst.comp Computable.fst)
                    (Computable.const OForm.bot))
                  (Computable.const OForm.bot))
                (Computable.fst.comp Computable.snd))
              (Computable.pair (Computable.const [])
                (Computable.fst.comp (Computable.snd.comp Computable.snd))))))).to₂).to₂
  have houter : Computable (fun p : ℕ × ℕ =>
      Option.casesOn (motive := fun _ => Bool) (decodeMathlibSent p.1) true fun ψ =>
        cond (isSentForm 0 ψ && decide (mathlibCodeSent ψ = p.1))
          (Option.casesOn (motive := fun _ => Bool)
            (Encodable.decode (α := List OForm × List PStep × Bool) p.2) false
            fun x =>
              x.1.all (fun θ => isSentForm 0 θ && fT (mathlibCodeSent θ)) &&
              cond x.2.2
                (checkDeriv (OForm.imp ψ OForm.bot :: x.1) [] x.2.1)
                (checkDeriv (OForm.imp (OForm.imp ψ OForm.bot) OForm.bot :: x.1) [] x.2.1))
          true) :=
    Computable.option_casesOn (primrec_decodeMathlibSent.to_comp.comp Computable.fst)
      (Computable.const true)
      (Computable.cond
        (Primrec.and.to_comp.comp
          ((primrec_isSentForm.comp (.const 0) .snd).to_comp)
          ((Primrec.eq.comp (primrec_mathlibCodeSent.comp .snd)
            (Primrec.fst.comp .fst)).decide.to_comp))
        (hinner.comp Computable.snd (Computable.snd.comp Computable.fst))
        (Computable.const true)).to₂
  refine houter.of_eq fun ⟨n, w⟩ => ?_
  unfold checkWitness
  dsimp only
  cases decodeMathlibSent n with
  | none => rfl
  | some ψ =>
    dsimp only
    cases hcond : isSentForm 0 ψ && decide (mathlibCodeSent ψ = n) with
    | false => rfl
    | true =>
      cases Encodable.decode (α := List OForm × List PStep × Bool) w with
      | none => rfl
      | some x => rcases x with ⟨T₀, steps, side⟩; dsimp only; cases side <;> rfl

theorem complete_recursive_isDecidable
    (T : LO.Theory) (hRec : T.IsRecursive) (hComp : T.IsComplete) :
    T.IsDecidable := by
  obtain ⟨fT, hfT, hmemT⟩ := hRec
  have hEx : ∀ n : ℕ, ∃ w : ℕ, checkWitness fT n w = true := by
    intro n
    cases hdec : decodeMathlibSent n with
    | none => exact ⟨0, by simp [checkWitness, hdec]⟩
    | some ψ =>
      by_cases hvalid : isSentForm 0 ψ = true ∧ mathlibCodeSent ψ = n
      · let φ : LO.Sentence := toMathlibForm 0 ψ hvalid.1
        have hφ : ofMathlibForm φ = ψ := ofMathlibForm_toMathlibForm ψ hvalid.1
        rcases hComp.2 φ with hmod | hmod
        · rw [models_iff_exists_deriv] at hmod
          obtain ⟨T₀, hT₀, hderiv⟩ := hmod
          rw [hφ] at hderiv
          obtain ⟨steps, hsteps⟩ := exists_checkDeriv_of_deriv hderiv
          refine ⟨Encodable.encode (T₀, steps, true), ?_⟩
          simp only [checkWitness, hdec, hvalid.1, hvalid.2, decide_true, Bool.and_self,
            ↓reduceIte, Encodable.encodek, hsteps, Bool.and_true, List.all_eq_true,
            Bool.and_eq_true]
          intro θ hθ
          obtain ⟨hsθ, s, hsT, rfl⟩ := hT₀ θ hθ
          exact ⟨hsθ, by rw [mathlibCodeSent_ofMathlibForm]; exact (hmemT s).2 hsT⟩
        · rw [models_iff_exists_deriv] at hmod
          obtain ⟨T₀, hT₀, hderiv⟩ := hmod
          have hnot : ofMathlibForm φ.not = OForm.imp ψ OForm.bot := by
            simp [ofMathlibForm, hφ]
          rw [hnot] at hderiv
          obtain ⟨steps, hsteps⟩ := exists_checkDeriv_of_deriv hderiv
          refine ⟨Encodable.encode (T₀, steps, false), ?_⟩
          simp only [checkWitness, hdec, hvalid.1, hvalid.2, decide_true, Bool.and_self,
            ↓reduceIte, Encodable.encodek, Bool.false_eq_true, hsteps, Bool.and_true,
            List.all_eq_true, Bool.and_eq_true]
          intro θ hθ
          obtain ⟨hsθ, s, hsT, rfl⟩ := hT₀ θ hθ
          exact ⟨hsθ, by rw [mathlibCodeSent_ofMathlibForm]; exact (hmemT s).2 hsT⟩
      · refine ⟨0, ?_⟩
        have hfalse : (isSentForm 0 ψ && decide (mathlibCodeSent ψ = n)) = false := by
          cases h1 : isSentForm 0 ψ
          · rfl
          · simp only [Bool.true_and, decide_eq_false_iff_not]
            intro h2; exact hvalid ⟨h1, h2⟩
        simp [checkWitness, hdec, hfalse]
  have hPred : ComputablePred (fun p : ℕ × ℕ => checkWitness fT p.1 p.2 = true) := by
    refine Computable.computablePred ?_
    exact (computable_checkWitness hfT).of_eq fun p => by cases checkWitness fT p.1 p.2 <;> rfl
  have hFind : Computable (fun n : ℕ => Nat.find (hEx n)) := Computable.find hPred hEx
  let f : ℕ → Bool := fun n =>
    Option.casesOn (Encodable.decode (α := List OForm × List PStep × Bool) (Nat.find (hEx n)))
      false fun x => x.2.2
  have hf : Computable f :=
    Computable.option_casesOn (Computable.decode.comp hFind) (Computable.const false)
      (Computable.snd.comp (Computable.snd.comp Computable.snd)).to₂
  refine ⟨f, hf, fun φ => ?_⟩
  have hspec : checkWitness fT (Encodable.encode φ) (Nat.find (hEx (Encodable.encode φ))) = true :=
    Nat.find_spec (hEx (Encodable.encode φ))
  have hdec : decodeMathlibSent (Encodable.encode φ) = some (ofMathlibForm φ) :=
    decodeMathlibSent_encode φ
  have hsent : isSentForm 0 (ofMathlibForm φ) = true := isSentForm_ofMathlibForm φ
  have hcode : mathlibCodeSent (ofMathlibForm φ) = Encodable.encode φ :=
    mathlibCodeSent_ofMathlibForm φ
  have hfeq : f (Encodable.encode φ) =
      Option.casesOn (Encodable.decode (α := List OForm × List PStep × Bool)
        (Nat.find (hEx (Encodable.encode φ)))) false fun x => x.2.2 := rfl
  generalize hw_val : Nat.find (hEx (Encodable.encode φ)) = w at hspec hfeq
  unfold checkWitness at hspec
  rw [hdec] at hspec
  dsimp only at hspec
  rw [hsent, hcode] at hspec
  simp only [decide_true, Bool.and_self, ↓reduceIte] at hspec
  cases hw : Encodable.decode (α := List OForm × List PStep × Bool) w with
  | none => rw [hw] at hspec; cases hspec
  | some x =>
    rcases x with ⟨T₀, steps, side⟩
    rw [hw] at hspec hfeq
    dsimp only at hspec hfeq
    simp only [Bool.and_eq_true, List.all_eq_true] at hspec
    rcases hspec with ⟨hT₀, hcheck⟩
    have hT₀_mem : ∀ θ ∈ T₀, isSentForm 0 θ = true ∧ ∃ s ∈ T, ofMathlibForm s = θ := by
      intro θ hθ
      obtain ⟨hsθ, hfθ⟩ := hT₀ θ hθ
      let s : LO.Sentence := toMathlibForm 0 θ hsθ
      have hs_eq : ofMathlibForm s = θ := ofMathlibForm_toMathlibForm θ hsθ
      have hs_in : s ∈ T := by
        rw [← hmemT s, ← mathlibCodeSent_ofMathlibForm s, hs_eq]
        exact hfθ
      exact ⟨hsθ, s, hs_in, hs_eq⟩
    rw [hfeq]
    cases side with
    | true =>
      simp only [↓reduceIte] at hcheck
      have hmod : T ⊨ᵇ φ := (models_iff_exists_deriv T φ).2
        ⟨T₀, hT₀_mem, deriv_of_checkDeriv hcheck⟩
      simp [hmod]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hcheck
      have hnot_eq : OForm.imp (OForm.imp (ofMathlibForm φ) OForm.bot) OForm.bot =
          OForm.imp (ofMathlibForm φ.not) OForm.bot := by
        simp [ofMathlibForm]
      rw [hnot_eq] at hcheck
      have hmod_not : T ⊨ᵇ φ.not := (models_iff_exists_deriv T φ.not).2
        ⟨T₀, hT₀_mem, deriv_of_checkDeriv hcheck⟩
      have hnot_mod : ¬ T ⊨ᵇ φ := by
        intro hmod
        obtain ⟨M⟩ := hComp.1
        have h1 : M ⊨ φ := hmod.realize_sentence M
        have h2 : M ⊨ φ.not := hmod_not.realize_sentence M
        exact h2 h1
      simp [hnot_mod]

end OMA.P_TarskiR1H2

theorem OMA.solution :
    OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_real_orderedField_R1.H2 :=
  OMA.P_TarskiR1H2.complete_recursive_isDecidable
