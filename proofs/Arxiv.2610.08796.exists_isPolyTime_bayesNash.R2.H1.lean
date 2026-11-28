import OMAReductions.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Proof of Step R2.H1 of `Arxiv.2610.08796.exists_isPolyTime_bayesNash`

We prove closure of `ComplexityTheory.IsPolyTime` under pairing `x ↦ h (x, f x)` by constructing
an explicit combined finite multi-stack Turing machine (`FinTM2`) that:
1. duplicates the input `bitEncode x` onto `Mf`'s input stack while retaining a copy,
2. simulates `Mf` to produce `bitEncode (f x)`,
3. transfers `delimit (bitEncode x) ++ bitEncode (f x) = bitEncode (x, f x)` onto `Mh`'s input
   stack (leaving all other stacks empty), and
4. simulates `Mh` to produce `bitEncode (h (x, f x))`.

A uniform bound on stack growth per step bounds `(bitEncode (f x)).length` polynomially in
`(bitEncode x).length`, yielding an explicit polynomial time bound for the combined machine.
-/

namespace OMAR2H1

open Computability Turing ComplexityTheory BitstringEncoding StateTransition
open Turing.TM2 Turing.TM2.Stmt Polynomial

section StackGrowth

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Maximum number of push operations executed in a single TM2 statement. -/
def stmtMaxPush : TM2.Stmt Γ Λ σ → ℕ
  | push _ _ q => stmtMaxPush q + 1
  | peek _ _ q => stmtMaxPush q
  | pop _ _ q => stmtMaxPush q
  | load _ q => stmtMaxPush q
  | branch _ q₁ q₂ => max (stmtMaxPush q₁) (stmtMaxPush q₂)
  | goto _ => 0
  | halt => 0

lemma stepAux_stk_length_le (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + stmtMaxPush q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux, stmtMaxPush]
    have h := ih v (Function.update S k' (f v :: S k'))
    by_cases hk : k = k'
    · subst hk
      simp only [Function.update_self, List.length_cons] at h
      omega
    · simp only [Function.update_of_ne hk] at h
      omega
  | peek k' f q ih =>
    simpa [TM2.stepAux, stmtMaxPush] using ih (f v (S k').head?) S
  | pop k' f q ih =>
    simp only [TM2.stepAux, stmtMaxPush]
    have h := ih (f v (S k').head?) (Function.update S k' (S k').tail)
    by_cases hk : k = k'
    · subst hk
      simp only [Function.update_self, List.length_tail] at h
      omega
    · simp only [Function.update_of_ne hk] at h
      exact h
  | load f q ih =>
    simpa [TM2.stepAux, stmtMaxPush] using ih (f v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, stmtMaxPush]
    cases f v
    · simp only [cond_false]
      have h := ih₂ v S
      omega
    · simp only [cond_true]
      have h := ih₁ v S
      omega
  | goto f =>
    simp [TM2.stepAux, stmtMaxPush]
  | halt =>
    simp [TM2.stepAux, stmtMaxPush]

/-- Maximum number of pushes per step of a finite TM2 machine. -/
def tmMaxPush (tm : FinTM2) : ℕ :=
  letI := tm.ΛFin
  Finset.univ.sup (fun l => stmtMaxPush (tm.m l))

lemma step_stk_length_le (tm : FinTM2) (c c' : tm.Cfg) (hc : tm.step c = some c') (k : tm.K) :
    (c'.stk k).length ≤ (c.stk k).length + tmMaxPush tm := by
  cases c with
  | mk l v S =>
    cases l with
    | none => simp [FinTM2.step, TM2.step] at hc
    | some lbl =>
      simp only [FinTM2.step, TM2.step] at hc
      injection hc with hc
      subst hc
      have h1 := stepAux_stk_length_le (tm.m lbl) v S k
      have h2 : stmtMaxPush (tm.m lbl) ≤ tmMaxPush tm := by
        let _ := tm.ΛFin
        exact Finset.le_sup (f := fun l => stmtMaxPush (tm.m l)) (Finset.mem_univ lbl)
      dsimp only
      omega

lemma iterate_step_stk_length_le (tm : FinTM2) :
    ∀ (n : ℕ) (c c' : tm.Cfg),
      (flip bind tm.step)^[n] (some c) = some c' →
      ∀ k : tm.K, (c'.stk k).length ≤ (c.stk k).length + n * tmMaxPush tm
  | 0, c, c', h, k => by
    simp only [Function.iterate_zero_apply, Option.some.injEq] at h
    subst h
    simp
  | n + 1, c, c', h, k => by
    rw [Function.iterate_succ_apply'] at h
    cases hm : (flip bind tm.step)^[n] (some c) with
    | none =>
      rw [hm] at h
      change none = some c' at h
      cases h
    | some cm =>
      rw [hm] at h
      have hstep : tm.step cm = some c' := h
      have h1 := iterate_step_stk_length_le tm n c cm hm k
      have h2 := step_stk_length_le tm cm c' hstep k
      calc (c'.stk k).length
          ≤ (cm.stk k).length + tmMaxPush tm := h2
        _ ≤ (c.stk k).length + n * tmMaxPush tm + tmMaxPush tm := by omega
        _ = (c.stk k).length + (n + 1) * tmMaxPush tm := by ring

lemma initList_stk_length_le (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((initList tm l).stk k).length ≤ l.length := by
  unfold initList
  dsimp only
  split_ifs with h
  · subst h; exact le_rfl
  · simp

lemma outputsInTime_len_le (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : List (tm.Γ tm.k₁)) (m : ℕ)
    (h : TM2OutputsInTime tm l (some l') m) :
    l'.length ≤ l.length + m * tmMaxPush tm := by
  have h1 := iterate_step_stk_length_le tm h.steps (initList tm l) (haltList tm l')
    h.evals_in_steps tm.k₁
  have h2 : ((haltList tm l').stk tm.k₁).length = l'.length := by
    simp [haltList]
  have h3 := initList_stk_length_le tm l tm.k₁
  have h4 : h.steps * tmMaxPush tm ≤ m * tmMaxPush tm := Nat.mul_le_mul_right _ h.steps_le_m
  omega

end StackGrowth

section CombinedMachine

variable {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
variable {f : α → β} {h : α × β → γ}
variable (Mf : TM2ComputableInPolyTime (bitEncode : α → List Bool) (bitEncode : β → List Bool) f)
variable (Mh : TM2ComputableInPolyTime (bitEncode : α × β → List Bool) (bitEncode : γ → List Bool) h)

/-- Combined stack index type: Mf's stacks, Mh's stacks, and 3 auxiliary Bool stacks
    (0 = input, 1 = tmpA, 2 = tmpB). -/
abbrev CombK := Mf.tm.K ⊕ Mh.tm.K ⊕ Fin 3

/-- Combined stack alphabet family. -/
abbrev CombΓ : CombK Mf Mh → Type
  | Sum.inl k => Mf.tm.Γ k
  | Sum.inr (Sum.inl k) => Mh.tm.Γ k
  | Sum.inr (Sum.inr _) => Bool

/-- Combined label type: 6 glue loop labels, Mf's labels, Mh's labels. -/
abbrev CombΛ := Fin 6 ⊕ Mf.tm.Λ ⊕ Mh.tm.Λ

/-- Combined internal state type: scratch Option Bool, Mf's state, Mh's state. -/
abbrev Combσ := Option Bool ⊕ Mf.tm.σ ⊕ Mh.tm.σ

/-- Explicit transparent DecidableEq instance for CombK. -/
def combDecEq : DecidableEq (CombK Mf Mh) :=
  @instDecidableEqSum _ _ Mf.tm.kDecidableEq
    (@instDecidableEqSum _ _ Mh.tm.kDecidableEq (inferInstance : DecidableEq (Fin 3)))

def getF (s : Combσ Mf Mh) : Mf.tm.σ :=
  match s with
  | Sum.inr (Sum.inl v) => v
  | _ => Mf.tm.initialState

def getH (s : Combσ Mf Mh) : Mh.tm.σ :=
  match s with
  | Sum.inr (Sum.inr v) => v
  | _ => Mh.tm.initialState

def isSomeBool (s : Combσ Mf Mh) : Bool :=
  match s with
  | Sum.inl (some _) => true
  | _ => false

def getBool (s : Combσ Mf Mh) : Bool :=
  match s with
  | Sum.inl (some b) => b
  | _ => false

/-- Lift a statement of Mf to the combined machine, transitioning to label 2 (revF) on halt. -/
def liftStmtF : TM2.Stmt Mf.tm.Γ Mf.tm.Λ Mf.tm.σ →
    TM2.Stmt (CombΓ Mf Mh) (CombΛ Mf Mh) (Combσ Mf Mh)
  | push k g q => push (Sum.inl k) (fun s => g (getF Mf Mh s)) (liftStmtF q)
  | peek k g q => peek (Sum.inl k) (fun s o => Sum.inr (Sum.inl (g (getF Mf Mh s) o))) (liftStmtF q)
  | pop k g q => pop (Sum.inl k) (fun s o => Sum.inr (Sum.inl (g (getF Mf Mh s) o))) (liftStmtF q)
  | load g q => load (fun s => Sum.inr (Sum.inl (g (getF Mf Mh s)))) (liftStmtF q)
  | branch g q₁ q₂ => branch (fun s => g (getF Mf Mh s)) (liftStmtF q₁) (liftStmtF q₂)
  | goto g => goto (fun s => Sum.inr (Sum.inl (g (getF Mf Mh s))))
  | halt => load (fun _ => Sum.inl none) (goto (fun _ => Sum.inl 2))

/-- Lift a statement of Mh to the combined machine, resetting var to initialState on halt. -/
def liftStmtH : TM2.Stmt Mh.tm.Γ Mh.tm.Λ Mh.tm.σ →
    TM2.Stmt (CombΓ Mf Mh) (CombΛ Mf Mh) (Combσ Mf Mh)
  | push k g q => push (Sum.inr (Sum.inl k)) (fun s => g (getH Mf Mh s)) (liftStmtH q)
  | peek k g q =>
      peek (Sum.inr (Sum.inl k)) (fun s o => Sum.inr (Sum.inr (g (getH Mf Mh s) o))) (liftStmtH q)
  | pop k g q =>
      pop (Sum.inr (Sum.inl k)) (fun s o => Sum.inr (Sum.inr (g (getH Mf Mh s) o))) (liftStmtH q)
  | load g q => load (fun s => Sum.inr (Sum.inr (g (getH Mf Mh s)))) (liftStmtH q)
  | branch g q₁ q₂ => branch (fun s => g (getH Mf Mh s)) (liftStmtH q₁) (liftStmtH q₂)
  | goto g => goto (fun s => Sum.inr (Sum.inr (g (getH Mf Mh s))))
  | halt => load (fun _ => Sum.inl none) halt

/-- Program of the combined machine. -/
def combProg : CombΛ Mf Mh → TM2.Stmt (CombΓ Mf Mh) (CombΛ Mf Mh) (Combσ Mf Mh)
  | Sum.inl 0 =>
      pop (Sum.inr (Sum.inr 0)) (fun _ o => Sum.inl o)
        (branch (isSomeBool Mf Mh)
          (push (Sum.inr (Sum.inr 1)) (getBool Mf Mh) (goto (fun _ => Sum.inl 0)))
          (goto (fun _ => Sum.inl 1)))
  | Sum.inl 1 =>
      pop (Sum.inr (Sum.inr 1)) (fun _ o => Sum.inl o)
        (branch (isSomeBool Mf Mh)
          (push (Sum.inr (Sum.inr 0)) (getBool Mf Mh)
            (push (Sum.inl Mf.tm.k₀) (fun s => Mf.inputAlphabet.invFun (getBool Mf Mh s))
              (goto (fun _ => Sum.inl 1))))
          (load (fun _ => Sum.inr (Sum.inl Mf.tm.initialState))
            (goto (fun _ => Sum.inr (Sum.inl Mf.tm.main)))))
  | Sum.inl 2 =>
      pop (Sum.inl Mf.tm.k₁) (fun _ o => Sum.inl (o.map Mf.outputAlphabet))
        (branch (isSomeBool Mf Mh)
          (push (Sum.inr (Sum.inr 2)) (getBool Mf Mh) (goto (fun _ => Sum.inl 2)))
          (goto (fun _ => Sum.inl 3)))
  | Sum.inl 3 =>
      pop (Sum.inr (Sum.inr 2)) (fun _ o => Sum.inl o)
        (branch (isSomeBool Mf Mh)
          (push (Sum.inr (Sum.inl Mh.tm.k₀)) (fun s => Mh.inputAlphabet.invFun (getBool Mf Mh s))
            (goto (fun _ => Sum.inl 3)))
          (push (Sum.inr (Sum.inl Mh.tm.k₀)) (fun _ => Mh.inputAlphabet.invFun false)
            (goto (fun _ => Sum.inl 4))))
  | Sum.inl 4 =>
      pop (Sum.inr (Sum.inr 0)) (fun _ o => Sum.inl o)
        (branch (isSomeBool Mf Mh)
          (push (Sum.inr (Sum.inr 1)) (getBool Mf Mh) (goto (fun _ => Sum.inl 4)))
          (goto (fun _ => Sum.inl 5)))
  | Sum.inl 5 =>
      pop (Sum.inr (Sum.inr 1)) (fun _ o => Sum.inl o)
        (branch (isSomeBool Mf Mh)
          (push (Sum.inr (Sum.inl Mh.tm.k₀)) (fun s => Mh.inputAlphabet.invFun (getBool Mf Mh s))
            (push (Sum.inr (Sum.inl Mh.tm.k₀)) (fun _ => Mh.inputAlphabet.invFun true)
              (goto (fun _ => Sum.inl 5))))
          (load (fun _ => Sum.inr (Sum.inr Mh.tm.initialState))
            (goto (fun _ => Sum.inr (Sum.inr Mh.tm.main)))))
  | Sum.inr (Sum.inl l) => liftStmtF Mf Mh (Mf.tm.m l)
  | Sum.inr (Sum.inr l) => liftStmtH Mf Mh (Mh.tm.m l)

/-- The combined FinTM2 machine for x |-> h (x, f x). -/
def combTM : FinTM2 where
  K := CombK Mf Mh
  kDecidableEq := combDecEq Mf Mh
  kFin := by
    letI := Mf.tm.kFin
    letI := Mh.tm.kFin
    infer_instance
  k₀ := Sum.inr (Sum.inr 0)
  k₁ := Sum.inr (Sum.inl Mh.tm.k₁)
  Γ := CombΓ Mf Mh
  Λ := CombΛ Mf Mh
  main := Sum.inl 0
  ΛFin := by
    letI := Mf.tm.ΛFin
    letI := Mh.tm.ΛFin
    infer_instance
  σ := Combσ Mf Mh
  initialState := Sum.inl none
  σFin := by
    letI := Mf.tm.σFin
    letI := Mh.tm.σFin
    infer_instance
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := combProg Mf Mh

/-- Assemble a combined stack function from Mf's stacks, Mh's stacks, and the 3 auxiliary stacks. -/
def mkStk (sf : ∀ k, List (Mf.tm.Γ k)) (sh : ∀ k, List (Mh.tm.Γ k))
    (s0 s1 s2 : List Bool) : ∀ k, List (CombΓ Mf Mh k)
  | Sum.inl k => sf k
  | Sum.inr (Sum.inl k) => sh k
  | Sum.inr (Sum.inr 0) => s0
  | Sum.inr (Sum.inr 1) => s1
  | Sum.inr (Sum.inr 2) => s2

def emptyF : ∀ k, List (Mf.tm.Γ k) := fun _ => []
def emptyH : ∀ k, List (Mh.tm.Γ k) := fun _ => []

lemma mkStk_update_inl {inst : DecidableEq (CombK Mf Mh)}
    (sf : ∀ k, List (Mf.tm.Γ k)) (sh : ∀ k, List (Mh.tm.Γ k))
    (s0 s1 s2 : List Bool) (k : Mf.tm.K) (val : List (Mf.tm.Γ k)) :
    @Function.update (CombK Mf Mh) (fun k => List (CombΓ Mf Mh k)) inst
      (mkStk Mf Mh sf sh s0 s1 s2) (Sum.inl k) val =
    mkStk Mf Mh (@Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf k val)
      sh s0 s1 s2 := by
  funext x
  cases x with
  | inl k' =>
    dsimp only [Function.update, mkStk]
    by_cases hk : k' = k
    · subst hk
      rw [dif_pos rfl, dif_pos rfl]
    · have hne : (Sum.inl k' : CombK Mf Mh) ≠ Sum.inl k := fun h => hk (Sum.inl.inj h)
      rw [dif_neg hne, dif_neg hk]
  | inr x =>
    cases x with
    | inl _ =>
      dsimp only [Function.update, mkStk]
      rw [dif_neg (by simp)]
    | inr i =>
      fin_cases i <;> (dsimp only [Function.update, mkStk]; rw [dif_neg (by simp)])

lemma mkStk_update_inr_inl {inst : DecidableEq (CombK Mf Mh)}
    (sf : ∀ k, List (Mf.tm.Γ k)) (sh : ∀ k, List (Mh.tm.Γ k))
    (s0 s1 s2 : List Bool) (k : Mh.tm.K) (val : List (Mh.tm.Γ k)) :
    @Function.update (CombK Mf Mh) (fun k => List (CombΓ Mf Mh k)) inst
      (mkStk Mf Mh sf sh s0 s1 s2) (Sum.inr (Sum.inl k)) val =
    mkStk Mf Mh sf
      (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh k val)
      s0 s1 s2 := by
  funext x
  cases x with
  | inl _ =>
    dsimp only [Function.update, mkStk]
    rw [dif_neg (by simp)]
  | inr x =>
    cases x with
    | inl k' =>
      dsimp only [Function.update, mkStk]
      by_cases hk : k' = k
      · subst hk
        rw [dif_pos rfl, dif_pos rfl]
      · have hne : (Sum.inr (Sum.inl k') : CombK Mf Mh) ≠ Sum.inr (Sum.inl k) :=
          fun h => hk (Sum.inl.inj (Sum.inr.inj h))
        rw [dif_neg hne, dif_neg hk]
    | inr i =>
      fin_cases i <;> (dsimp only [Function.update, mkStk]; rw [dif_neg (by simp)])

lemma mkStk_update_0 {inst : DecidableEq (CombK Mf Mh)}
    (sf : ∀ k, List (Mf.tm.Γ k)) (sh : ∀ k, List (Mh.tm.Γ k))
    (s0 s1 s2 val : List Bool) :
    @Function.update (CombK Mf Mh) (fun k => List (CombΓ Mf Mh k)) inst
      (mkStk Mf Mh sf sh s0 s1 s2) (Sum.inr (Sum.inr 0)) val =
    mkStk Mf Mh sf sh val s1 s2 := by
  funext x
  cases x with
  | inl _ =>
    dsimp only [Function.update, mkStk]; rw [dif_neg (by simp)]
  | inr x =>
    cases x with
    | inl _ =>
      dsimp only [Function.update, mkStk]; rw [dif_neg (by simp)]
    | inr i =>
      fin_cases i
      · dsimp only [Function.update, mkStk]
        have heq : (Sum.inr (Sum.inr ⟨0, by omega⟩) : CombK Mf Mh) = Sum.inr (Sum.inr 0) := rfl
        rw [dif_pos heq]
      · dsimp only [Function.update, mkStk]
        rw [dif_neg (by intro h; injection h with h; injection h with h; exact absurd h (by decide))]
      · dsimp only [Function.update, mkStk]
        rw [dif_neg (by intro h; injection h with h; injection h with h; exact absurd h (by decide))]

lemma mkStk_update_1 {inst : DecidableEq (CombK Mf Mh)}
    (sf : ∀ k, List (Mf.tm.Γ k)) (sh : ∀ k, List (Mh.tm.Γ k))
    (s0 s1 s2 val : List Bool) :
    @Function.update (CombK Mf Mh) (fun k => List (CombΓ Mf Mh k)) inst
      (mkStk Mf Mh sf sh s0 s1 s2) (Sum.inr (Sum.inr 1)) val =
    mkStk Mf Mh sf sh s0 val s2 := by
  funext x
  cases x with
  | inl _ =>
    dsimp only [Function.update, mkStk]; rw [dif_neg (by simp)]
  | inr x =>
    cases x with
    | inl _ =>
      dsimp only [Function.update, mkStk]; rw [dif_neg (by simp)]
    | inr i =>
      fin_cases i
      · dsimp only [Function.update, mkStk]
        rw [dif_neg (by intro h; injection h with h; injection h with h; exact absurd h (by decide))]
      · dsimp only [Function.update, mkStk]
        have heq : (Sum.inr (Sum.inr ⟨1, by omega⟩) : CombK Mf Mh) = Sum.inr (Sum.inr 1) := rfl
        rw [dif_pos heq]
      · dsimp only [Function.update, mkStk]
        rw [dif_neg (by intro h; injection h with h; injection h with h; exact absurd h (by decide))]

lemma mkStk_update_2 {inst : DecidableEq (CombK Mf Mh)}
    (sf : ∀ k, List (Mf.tm.Γ k)) (sh : ∀ k, List (Mh.tm.Γ k))
    (s0 s1 s2 val : List Bool) :
    @Function.update (CombK Mf Mh) (fun k => List (CombΓ Mf Mh k)) inst
      (mkStk Mf Mh sf sh s0 s1 s2) (Sum.inr (Sum.inr 2)) val =
    mkStk Mf Mh sf sh s0 s1 val := by
  funext x
  cases x with
  | inl _ =>
    dsimp only [Function.update, mkStk]; rw [dif_neg (by simp)]
  | inr x =>
    cases x with
    | inl _ =>
      dsimp only [Function.update, mkStk]; rw [dif_neg (by simp)]
    | inr i =>
      fin_cases i
      · dsimp only [Function.update, mkStk]
        rw [dif_neg (by intro h; injection h with h; injection h with h; exact absurd h (by decide))]
      · dsimp only [Function.update, mkStk]
        rw [dif_neg (by intro h; injection h with h; injection h with h; exact absurd h (by decide))]
      · dsimp only [Function.update, mkStk]
        have heq : (Sum.inr (Sum.inr ⟨2, by omega⟩) : CombK Mf Mh) = Sum.inr (Sum.inr 2) := rfl
        rw [dif_pos heq]

/-- Single step helper for EvalsToInTime on a FinTM2. -/
def evals_step {tm : FinTM2} {a b : tm.Cfg} (hstep : tm.step a = some b) :
    EvalsToInTime tm.step a (some b) 1 where
  steps := 1
  evals_in_steps := hstep
  steps_le_m := le_rfl

/-- Lift EvalsToInTime bound by monotonicity on a FinTM2. -/
def evals_le {tm : FinTM2} {a : tm.Cfg} {b : Option tm.Cfg} {m₁ m₂ : ℕ}
    (he : EvalsToInTime tm.step a b m₁) (hle : m₁ ≤ m₂) : EvalsToInTime tm.step a b m₂ where
  steps := he.steps
  evals_in_steps := he.evals_in_steps
  steps_le_m := le_trans he.steps_le_m hle

/-- Helper: stepAux of liftStmtF mirrors stepAux of Mf.tm. -/
lemma stepAux_liftStmtF (q : TM2.Stmt Mf.tm.Γ Mf.tm.Λ Mf.tm.σ)
    (v : Mf.tm.σ) (sf : ∀ k, List (Mf.tm.Γ k))
    (sh : ∀ k, List (Mh.tm.Γ k)) (s0 s1 s2 : List Bool) :
    @TM2.stepAux (CombK Mf Mh) (CombΓ Mf Mh) (CombΛ Mf Mh) (Combσ Mf Mh)
      (combDecEq Mf Mh) (liftStmtF Mf Mh q) (Sum.inr (Sum.inl v))
      (mkStk Mf Mh sf sh s0 s1 s2) =
    let res := @TM2.stepAux Mf.tm.K Mf.tm.Γ Mf.tm.Λ Mf.tm.σ Mf.tm.kDecidableEq q v sf
    match res.l with
    | some l' => ⟨some (Sum.inr (Sum.inl l')), Sum.inr (Sum.inl res.var),
        mkStk Mf Mh res.stk sh s0 s1 s2⟩
    | none => ⟨some (Sum.inl 2), Sum.inl none, mkStk Mf Mh res.stk sh s0 s1 s2⟩ := by
  induction q generalizing v sf with
  | push k g q ih =>
    dsimp only [liftStmtF, TM2.stepAux, getF, mkStk]
    rw [mkStk_update_inl]
    exact ih v _
  | peek k g q ih =>
    dsimp only [liftStmtF, TM2.stepAux, getF, mkStk]
    exact ih _ sf
  | pop k g q ih =>
    dsimp only [liftStmtF, TM2.stepAux, getF, mkStk]
    rw [mkStk_update_inl]
    exact ih _ _
  | load g q ih =>
    dsimp only [liftStmtF, TM2.stepAux, getF]
    exact ih _ sf
  | branch g q₁ q₂ ih₁ ih₂ =>
    dsimp only [liftStmtF, TM2.stepAux, getF]
    cases g v
    · simpa only [cond_false] using ih₂ v sf
    · simpa only [cond_true] using ih₁ v sf
  | goto g =>
    rfl
  | halt =>
    rfl

/-- Helper: stepAux of liftStmtH mirrors stepAux of Mh.tm. -/
lemma stepAux_liftStmtH (q : TM2.Stmt Mh.tm.Γ Mh.tm.Λ Mh.tm.σ)
    (v : Mh.tm.σ) (sf : ∀ k, List (Mf.tm.Γ k))
    (sh : ∀ k, List (Mh.tm.Γ k)) (s0 s1 s2 : List Bool) :
    @TM2.stepAux (CombK Mf Mh) (CombΓ Mf Mh) (CombΛ Mf Mh) (Combσ Mf Mh)
      (combDecEq Mf Mh) (liftStmtH Mf Mh q) (Sum.inr (Sum.inr v))
      (mkStk Mf Mh sf sh s0 s1 s2) =
    let res := @TM2.stepAux Mh.tm.K Mh.tm.Γ Mh.tm.Λ Mh.tm.σ Mh.tm.kDecidableEq q v sh
    match res.l with
    | some l' => ⟨some (Sum.inr (Sum.inr l')), Sum.inr (Sum.inr res.var),
        mkStk Mf Mh sf res.stk s0 s1 s2⟩
    | none => ⟨none, Sum.inl none, mkStk Mf Mh sf res.stk s0 s1 s2⟩ := by
  induction q generalizing v sh with
  | push k g q ih =>
    dsimp only [liftStmtH, TM2.stepAux, getH, mkStk]
    rw [mkStk_update_inr_inl]
    exact ih v _
  | peek k g q ih =>
    dsimp only [liftStmtH, TM2.stepAux, getH, mkStk]
    exact ih _ sh
  | pop k g q ih =>
    dsimp only [liftStmtH, TM2.stepAux, getH, mkStk]
    rw [mkStk_update_inr_inl]
    exact ih _ _
  | load g q ih =>
    dsimp only [liftStmtH, TM2.stepAux, getH]
    exact ih _ sh
  | branch g q₁ q₂ ih₁ ih₂ =>
    dsimp only [liftStmtH, TM2.stepAux, getH]
    cases g v
    · simpa only [cond_false] using ih₂ v sh
    · simpa only [cond_true] using ih₁ v sh
  | goto g =>
    rfl
  | halt =>
    rfl

/-- Simulation of Mf.tm inside combTM for n steps until reaching a halting configuration. -/
lemma simF (sh : ∀ k, List (Mh.tm.Γ k)) (s0 s1 s2 : List Bool) :
    ∀ (n : ℕ) (c : Mf.tm.Cfg) (out : Mf.tm.Cfg),
      (flip bind Mf.tm.step)^[n] (some c) = some out →
      ∀ l0 : Mf.tm.Λ, c.l = some l0 →
      (flip bind (combTM Mf Mh).step)^[n]
        (some ⟨some (Sum.inr (Sum.inl l0)), Sum.inr (Sum.inl c.var),
          mkStk Mf Mh c.stk sh s0 s1 s2⟩) =
      match out.l with
      | some l' => some ⟨some (Sum.inr (Sum.inl l')), Sum.inr (Sum.inl out.var),
          mkStk Mf Mh out.stk sh s0 s1 s2⟩
      | none => some ⟨some (Sum.inl 2), Sum.inl none,
          mkStk Mf Mh out.stk sh s0 s1 s2⟩
  | 0, c, out, hev, l0, hl0 => by
    simp only [Function.iterate_zero_apply, Option.some.injEq] at hev
    subst hev
    simp [hl0]
  | n + 1, c, out, hev, l0, hl0 => by
    rw [Function.iterate_succ_apply] at hev ⊢
    cases c with
    | mk cl cv cs =>
      simp only at hl0
      subst hl0
      let next : Mf.tm.Cfg :=
        @TM2.stepAux Mf.tm.K Mf.tm.Γ Mf.tm.Λ Mf.tm.σ Mf.tm.kDecidableEq (Mf.tm.m l0) cv cs
      have hev' : (flip bind Mf.tm.step)^[n] (some next) = some out := hev
      change (flip bind (combTM Mf Mh).step)^[n]
        (some (@TM2.stepAux (CombK Mf Mh) (CombΓ Mf Mh) (CombΛ Mf Mh) (Combσ Mf Mh)
          (combDecEq Mf Mh) (liftStmtF Mf Mh (Mf.tm.m l0)) (Sum.inr (Sum.inl cv))
          (mkStk Mf Mh cs sh s0 s1 s2))) = _
      rw [stepAux_liftStmtF]
      change (flip bind (combTM Mf Mh).step)^[n]
        (some (match next.l with
          | some l' => ⟨some (Sum.inr (Sum.inl l')), Sum.inr (Sum.inl next.var),
              mkStk Mf Mh next.stk sh s0 s1 s2⟩
          | none => ⟨some (Sum.inl 2), Sum.inl none,
              mkStk Mf Mh next.stk sh s0 s1 s2⟩)) = _
      cases hnl : next.l with
      | none =>
        cases n with
        | zero =>
          have hne : next = out := Option.some.inj hev'
          rw [← hne, Function.iterate_zero_apply, hnl]
        | succ m =>
          rw [Function.iterate_succ_apply] at hev'
          have hstep_none : ∀ cfg : Mf.tm.Cfg, cfg.l = none → Mf.tm.step cfg = none := by
            rintro ⟨l, v, s⟩ hl
            simp only at hl
            subst hl
            rfl
          have hnone : Mf.tm.step next = none := hstep_none next hnl
          have hev'' : (flip bind Mf.tm.step)^[m] (Mf.tm.step next) = some out := hev'
          rw [hnone] at hev''
          have hnone_iter : ∀ k, (flip bind Mf.tm.step)^[k] none = none := by
            intro k
            induction k with
            | zero => rfl
            | succ k ih => rw [Function.iterate_succ_apply]; exact ih
          rw [hnone_iter] at hev''
          cases hev''
      | some l1 =>
        exact simF sh s0 s1 s2 n next out hev' l1 hnl

/-- Simulation of Mh.tm inside combTM for n steps until reaching a halting configuration. -/
lemma simH (sf : ∀ k, List (Mf.tm.Γ k)) (s0 s1 s2 : List Bool) :
    ∀ (n : ℕ) (c : Mh.tm.Cfg) (out : Mh.tm.Cfg),
      (flip bind Mh.tm.step)^[n] (some c) = some out →
      ∀ l0 : Mh.tm.Λ, c.l = some l0 →
      (flip bind (combTM Mf Mh).step)^[n]
        (some ⟨some (Sum.inr (Sum.inr l0)), Sum.inr (Sum.inr c.var),
          mkStk Mf Mh sf c.stk s0 s1 s2⟩) =
      match out.l with
      | some l' => some ⟨some (Sum.inr (Sum.inr l')), Sum.inr (Sum.inr out.var),
          mkStk Mf Mh sf out.stk s0 s1 s2⟩
      | none => some ⟨none, Sum.inl none,
          mkStk Mf Mh sf out.stk s0 s1 s2⟩
  | 0, c, out, hev, l0, hl0 => by
    simp only [Function.iterate_zero_apply, Option.some.injEq] at hev
    subst hev
    simp [hl0]
  | n + 1, c, out, hev, l0, hl0 => by
    rw [Function.iterate_succ_apply] at hev ⊢
    cases c with
    | mk cl cv cs =>
      simp only at hl0
      subst hl0
      let next : Mh.tm.Cfg :=
        @TM2.stepAux Mh.tm.K Mh.tm.Γ Mh.tm.Λ Mh.tm.σ Mh.tm.kDecidableEq (Mh.tm.m l0) cv cs
      have hev' : (flip bind Mh.tm.step)^[n] (some next) = some out := hev
      change (flip bind (combTM Mf Mh).step)^[n]
        (some (@TM2.stepAux (CombK Mf Mh) (CombΓ Mf Mh) (CombΛ Mf Mh) (Combσ Mf Mh)
          (combDecEq Mf Mh) (liftStmtH Mf Mh (Mh.tm.m l0)) (Sum.inr (Sum.inr cv))
          (mkStk Mf Mh sf cs s0 s1 s2))) = _
      rw [stepAux_liftStmtH]
      change (flip bind (combTM Mf Mh).step)^[n]
        (some (match next.l with
          | some l' => ⟨some (Sum.inr (Sum.inr l')), Sum.inr (Sum.inr next.var),
              mkStk Mf Mh sf next.stk s0 s1 s2⟩
          | none => ⟨none, Sum.inl none,
              mkStk Mf Mh sf next.stk s0 s1 s2⟩)) = _
      cases hnl : next.l with
      | none =>
        cases n with
        | zero =>
          have hne : next = out := Option.some.inj hev'
          rw [← hne, Function.iterate_zero_apply, hnl]
        | succ m =>
          rw [Function.iterate_succ_apply] at hev'
          have hstep_none : ∀ cfg : Mh.tm.Cfg, cfg.l = none → Mh.tm.step cfg = none := by
            rintro ⟨l, v, s⟩ hl
            simp only at hl
            subst hl
            rfl
          have hnone : Mh.tm.step next = none := hstep_none next hnl
          have hev'' : (flip bind Mh.tm.step)^[m] (Mh.tm.step next) = some out := hev'
          rw [hnone] at hev''
          have hnone_iter : ∀ k, (flip bind Mh.tm.step)^[k] none = none := by
            intro k
            induction k with
            | zero => rfl
            | succ k ih => rw [Function.iterate_succ_apply]; exact ih
          rw [hnone_iter] at hev''
          cases hev''
      | some l1 =>
        exact simH sf s0 s1 s2 n next out hev' l1 hnl

-- Phase 0 (copyIn): pop s0 into s1
def phase0 (sf : ∀ k, List (Mf.tm.Γ k)) (sh : ∀ k, List (Mh.tm.Γ k)) (s2 : List Bool)
    (v : Combσ Mf Mh) :
    ∀ (s0 s1 : List Bool),
      EvalsToInTime (combTM Mf Mh).step
        ⟨some (Sum.inl 0), v, mkStk Mf Mh sf sh s0 s1 s2⟩
        (some ⟨some (Sum.inl 1), Sum.inl none, mkStk Mf Mh sf sh [] (s0.reverse ++ s1) s2⟩)
        (s0.length + 1)
  | [], s1 => by
    have hst : (combTM Mf Mh).step ⟨some (Sum.inl 0), v, mkStk Mf Mh sf sh [] s1 s2⟩ =
        some ⟨some (Sum.inl 1), Sum.inl none, mkStk Mf Mh sf sh [] s1 s2⟩ := by
      dsimp only [FinTM2.step, TM2.step, combTM, combProg, TM2.stepAux, mkStk, isSomeBool,
        List.head?, List.tail, cond_false]
      rw [mkStk_update_0]
      rfl
    simpa only [List.reverse_nil, List.nil_append, List.length_nil, Nat.zero_add] using
      evals_step hst
  | b :: bs, s1 => by
    have hst : (combTM Mf Mh).step ⟨some (Sum.inl 0), v, mkStk Mf Mh sf sh (b :: bs) s1 s2⟩ =
        some ⟨some (Sum.inl 0), Sum.inl (some b), mkStk Mf Mh sf sh bs (b :: s1) s2⟩ := by
      dsimp only [FinTM2.step, TM2.step, combTM, combProg, TM2.stepAux, mkStk, isSomeBool, getBool,
        List.head?, List.tail, cond_true]
      rw [mkStk_update_0]
      dsimp only [mkStk]
      rw [mkStk_update_1]
      rfl
    have hrest := phase0 sf sh s2 (Sum.inl (some b)) bs (b :: s1)
    have htr := EvalsToInTime.trans (combTM Mf Mh).step 1 (bs.length + 1) _ _ _
      (evals_step hst) hrest
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
      Nat.add_comm] using htr

-- Phase 1 (dupIn): pop s1, push to s0 and to Mf.k₀, then start Mf
def phase1 (sf : ∀ k, List (Mf.tm.Γ k)) (sh : ∀ k, List (Mh.tm.Γ k)) (s2 : List Bool)
    (v : Combσ Mf Mh) :
    ∀ (s1 s0 : List Bool),
      EvalsToInTime (combTM Mf Mh).step
        ⟨some (Sum.inl 1), v, mkStk Mf Mh sf sh s0 s1 s2⟩
        (some ⟨some (Sum.inr (Sum.inl Mf.tm.main)), Sum.inr (Sum.inl Mf.tm.initialState),
          mkStk Mf Mh
            (@Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf Mf.tm.k₀
              (s1.reverse.map Mf.inputAlphabet.invFun ++ sf Mf.tm.k₀))
            sh (s1.reverse ++ s0) [] s2⟩)
        (s1.length + 1)
  | [], s0 => by
    have hst : (combTM Mf Mh).step ⟨some (Sum.inl 1), v, mkStk Mf Mh sf sh s0 [] s2⟩ =
        some ⟨some (Sum.inr (Sum.inl Mf.tm.main)), Sum.inr (Sum.inl Mf.tm.initialState),
          mkStk Mf Mh sf sh s0 [] s2⟩ := by
      dsimp only [FinTM2.step, TM2.step, combTM, combProg, TM2.stepAux, mkStk, isSomeBool,
        List.head?, List.tail, cond_false]
      rw [mkStk_update_1]
      rfl
    have hupd : @Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf Mf.tm.k₀
        (sf Mf.tm.k₀) = sf := by
      funext k
      dsimp only [Function.update]
      by_cases hk : k = Mf.tm.k₀
      · subst hk; rw [dif_pos rfl]
      · rw [dif_neg hk]
    simpa only [List.reverse_nil, List.map_nil, List.nil_append, List.length_nil, Nat.zero_add,
      hupd] using evals_step hst
  | b :: bs, s0 => by
    let sf' := @Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf Mf.tm.k₀
      (Mf.inputAlphabet.invFun b :: sf Mf.tm.k₀)
    have hst : (combTM Mf Mh).step ⟨some (Sum.inl 1), v, mkStk Mf Mh sf sh s0 (b :: bs) s2⟩ =
        some ⟨some (Sum.inl 1), Sum.inl (some b), mkStk Mf Mh sf' sh (b :: s0) bs s2⟩ := by
      dsimp only [FinTM2.step, TM2.step, combTM, combProg, TM2.stepAux, mkStk, isSomeBool, getBool,
        List.head?, List.tail, cond_true]
      rw [mkStk_update_1]
      dsimp only [mkStk]
      rw [mkStk_update_0]
      dsimp only [mkStk]
      rw [mkStk_update_inl]
      rfl
    have hrest := phase1 sf' sh s2 (Sum.inl (some b)) bs (b :: s0)
    have hupd2 :
        @Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf' Mf.tm.k₀
          (bs.reverse.map Mf.inputAlphabet.invFun ++ sf' Mf.tm.k₀) =
        @Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf Mf.tm.k₀
          ((b :: bs).reverse.map Mf.inputAlphabet.invFun ++ sf Mf.tm.k₀) := by
      funext k
      dsimp only [sf', Function.update]
      by_cases hk : k = Mf.tm.k₀
      · subst hk
        rw [dif_pos rfl, dif_pos rfl, dif_pos rfl]
        simp [List.reverse_cons, List.map_append, List.append_assoc]
      · rw [dif_neg hk, dif_neg hk, dif_neg hk]
    have htr := EvalsToInTime.trans (combTM Mf Mh).step 1 (bs.length + 1) _ _ _
      (evals_step hst) hrest
    simpa only [hupd2, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, Nat.add_comm] using htr

-- Phase 2 (revF): pop Mf.k₁ into s2
def phase2 (sf : ∀ k, List (Mf.tm.Γ k)) (sh : ∀ k, List (Mh.tm.Γ k)) (s0 s1 : List Bool)
    (v : Combσ Mf Mh) :
    ∀ (l : List (Mf.tm.Γ Mf.tm.k₁)) (s2 : List Bool),
      EvalsToInTime (combTM Mf Mh).step
        ⟨some (Sum.inl 2), v,
          mkStk Mf Mh
            (@Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf Mf.tm.k₁ l)
            sh s0 s1 s2⟩
        (some ⟨some (Sum.inl 3), Sum.inl none,
          mkStk Mf Mh
            (@Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf Mf.tm.k₁ [])
            sh s0 s1 ((l.map Mf.outputAlphabet).reverse ++ s2)⟩)
        (l.length + 1)
  | [], s2 => by
    have hst : (combTM Mf Mh).step
        ⟨some (Sum.inl 2), v,
          mkStk Mf Mh
            (@Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf Mf.tm.k₁ [])
            sh s0 s1 s2⟩ =
        some ⟨some (Sum.inl 3), Sum.inl none,
          mkStk Mf Mh
            (@Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf Mf.tm.k₁ [])
            sh s0 s1 s2⟩ := by
      dsimp only [FinTM2.step, TM2.step, combTM, combProg, TM2.stepAux, mkStk]
      have hself : (@Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq
          sf Mf.tm.k₁ []) Mf.tm.k₁ = [] := by
        dsimp only [Function.update]; rw [dif_pos rfl]
      rw [hself]
      dsimp only [List.head?, List.tail, Option.map_none, isSomeBool, cond_false]
      rw [mkStk_update_inl]
      have hidem : @Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq
          (@Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf Mf.tm.k₁ [])
          Mf.tm.k₁ [] =
          @Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf Mf.tm.k₁ [] := by
        funext k; dsimp only [Function.update]
        by_cases hk : k = Mf.tm.k₁
        · subst hk; simp only [dif_pos]
        · simp only [dif_neg hk]
      rw [hidem]
      rfl
    simpa only [List.map_nil, List.reverse_nil, List.nil_append, List.length_nil, Nat.zero_add] using
      evals_step hst
  | c :: cs, s2 => by
    have hst : (combTM Mf Mh).step
        ⟨some (Sum.inl 2), v,
          mkStk Mf Mh
            (@Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf Mf.tm.k₁
              (c :: cs))
            sh s0 s1 s2⟩ =
        some ⟨some (Sum.inl 2), Sum.inl (some (Mf.outputAlphabet c)),
          mkStk Mf Mh
            (@Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf Mf.tm.k₁ cs)
            sh s0 s1 (Mf.outputAlphabet c :: s2)⟩ := by
      dsimp only [FinTM2.step, TM2.step, combTM, combProg, TM2.stepAux, mkStk]
      have hself : (@Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq
          sf Mf.tm.k₁ (c :: cs)) Mf.tm.k₁ = c :: cs := by
        dsimp only [Function.update]; rw [dif_pos rfl]
      rw [hself]
      dsimp only [List.head?, List.tail, Option.map_some, isSomeBool, getBool, cond_true]
      rw [mkStk_update_inl]
      dsimp only [mkStk]
      rw [mkStk_update_2]
      have hidem : @Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq
          (@Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf Mf.tm.k₁
            (c :: cs))
          Mf.tm.k₁ cs =
          @Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq sf Mf.tm.k₁ cs := by
        funext k; dsimp only [Function.update]
        by_cases hk : k = Mf.tm.k₁
        · subst hk; simp only [dif_pos]
        · simp only [dif_neg hk]
      rw [hidem]
      rfl
    have hrest := phase2 sf sh s0 s1 (Sum.inl (some (Mf.outputAlphabet c))) cs
      (Mf.outputAlphabet c :: s2)
    have htr := EvalsToInTime.trans (combTM Mf Mh).step 1 (cs.length + 1) _ _ _
      (evals_step hst) hrest
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, Nat.add_comm] using htr

-- Phase 3 (pushF): pop s2, push encoded to Mh.k₀; at end push false terminator & goto 4
def phase3 (sf : ∀ k, List (Mf.tm.Γ k)) (sh : ∀ k, List (Mh.tm.Γ k)) (s0 s1 : List Bool)
    (v : Combσ Mf Mh) :
    ∀ (s2 : List Bool) (acc : List (Mh.tm.Γ Mh.tm.k₀)),
      EvalsToInTime (combTM Mf Mh).step
        ⟨some (Sum.inl 3), v,
          mkStk Mf Mh sf
            (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀ acc)
            s0 s1 s2⟩
        (some ⟨some (Sum.inl 4), Sum.inl none,
          mkStk Mf Mh sf
            (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀
              (Mh.inputAlphabet.invFun false :: (s2.reverse.map Mh.inputAlphabet.invFun ++ acc)))
            s0 s1 []⟩)
        (s2.length + 1)
  | [], acc => by
    have hst : (combTM Mf Mh).step
        ⟨some (Sum.inl 3), v,
          mkStk Mf Mh sf
            (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀ acc)
            s0 s1 []⟩ =
        some ⟨some (Sum.inl 4), Sum.inl none,
          mkStk Mf Mh sf
            (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀
              (Mh.inputAlphabet.invFun false :: acc))
            s0 s1 []⟩ := by
      dsimp only [FinTM2.step, TM2.step, combTM, combProg, TM2.stepAux, mkStk, List.head?, List.tail,
        isSomeBool, cond_false]
      rw [mkStk_update_2]
      dsimp only [mkStk]
      rw [mkStk_update_inr_inl]
      have hself : (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq
          sh Mh.tm.k₀ acc) Mh.tm.k₀ = acc := by
        dsimp only [Function.update]; rw [dif_pos rfl]
      have hidem : @Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq
          (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀ acc)
          Mh.tm.k₀ (Mh.inputAlphabet.invFun false :: acc) =
          @Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀
            (Mh.inputAlphabet.invFun false :: acc) := by
        funext k; dsimp only [Function.update]
        by_cases hk : k = Mh.tm.k₀
        · subst hk; simp only [dif_pos]
        · simp only [dif_neg hk]
      rw [hself, hidem]
      rfl
    simpa only [List.reverse_nil, List.map_nil, List.nil_append, List.length_nil, Nat.zero_add] using
      evals_step hst
  | b :: bs, acc => by
    have hst : (combTM Mf Mh).step
        ⟨some (Sum.inl 3), v,
          mkStk Mf Mh sf
            (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀ acc)
            s0 s1 (b :: bs)⟩ =
        some ⟨some (Sum.inl 3), Sum.inl (some b),
          mkStk Mf Mh sf
            (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀
              (Mh.inputAlphabet.invFun b :: acc))
            s0 s1 bs⟩ := by
      dsimp only [FinTM2.step, TM2.step, combTM, combProg, TM2.stepAux, mkStk, List.head?, List.tail,
        isSomeBool, getBool, cond_true]
      rw [mkStk_update_2]
      dsimp only [mkStk]
      rw [mkStk_update_inr_inl]
      have hself : (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq
          sh Mh.tm.k₀ acc) Mh.tm.k₀ = acc := by
        dsimp only [Function.update]; rw [dif_pos rfl]
      have hidem : @Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq
          (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀ acc)
          Mh.tm.k₀ (Mh.inputAlphabet.invFun b :: acc) =
          @Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀
            (Mh.inputAlphabet.invFun b :: acc) := by
        funext k; dsimp only [Function.update]
        by_cases hk : k = Mh.tm.k₀
        · subst hk; simp only [dif_pos]
        · simp only [dif_neg hk]
      rw [hself, hidem]
      rfl
    have hrest := phase3 sf sh s0 s1 (Sum.inl (some b)) bs (Mh.inputAlphabet.invFun b :: acc)
    have htr := EvalsToInTime.trans (combTM Mf Mh).step 1 (bs.length + 1) _ _ _
      (evals_step hst) hrest
    simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.singleton_append, List.length_cons, Nat.add_comm] using htr

-- Phase 4 (revA): pop s0 into s1
def phase4 (sf : ∀ k, List (Mf.tm.Γ k)) (sh : ∀ k, List (Mh.tm.Γ k)) (s2 : List Bool)
    (v : Combσ Mf Mh) :
    ∀ (s0 s1 : List Bool),
      EvalsToInTime (combTM Mf Mh).step
        ⟨some (Sum.inl 4), v, mkStk Mf Mh sf sh s0 s1 s2⟩
        (some ⟨some (Sum.inl 5), Sum.inl none, mkStk Mf Mh sf sh [] (s0.reverse ++ s1) s2⟩)
        (s0.length + 1)
  | [], s1 => by
    have hst : (combTM Mf Mh).step ⟨some (Sum.inl 4), v, mkStk Mf Mh sf sh [] s1 s2⟩ =
        some ⟨some (Sum.inl 5), Sum.inl none, mkStk Mf Mh sf sh [] s1 s2⟩ := by
      dsimp only [FinTM2.step, TM2.step, combTM, combProg, TM2.stepAux, mkStk, isSomeBool,
        List.head?, List.tail, cond_false]
      rw [mkStk_update_0]
      rfl
    simpa only [List.reverse_nil, List.nil_append, List.length_nil, Nat.zero_add] using
      evals_step hst
  | b :: bs, s1 => by
    have hst : (combTM Mf Mh).step ⟨some (Sum.inl 4), v, mkStk Mf Mh sf sh (b :: bs) s1 s2⟩ =
        some ⟨some (Sum.inl 4), Sum.inl (some b), mkStk Mf Mh sf sh bs (b :: s1) s2⟩ := by
      dsimp only [FinTM2.step, TM2.step, combTM, combProg, TM2.stepAux, mkStk, isSomeBool, getBool,
        List.head?, List.tail, cond_true]
      rw [mkStk_update_0]
      dsimp only [mkStk]
      rw [mkStk_update_1]
      rfl
    have hrest := phase4 sf sh s2 (Sum.inl (some b)) bs (b :: s1)
    have htr := EvalsToInTime.trans (combTM Mf Mh).step 1 (bs.length + 1) _ _ _
      (evals_step hst) hrest
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
      Nat.add_comm] using htr

/-- Prepending `true :: b` for each element of `s1` in reverse produces `delimit` prefix. -/
def delimitPrefix : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: delimitPrefix bs

lemma delimit_eq_delimitPrefix_append (l : List Bool) :
    delimit l = delimitPrefix l ++ [false] := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [delimit, delimitPrefix, ih]

lemma delimitPrefix_append (l₁ l₂ : List Bool) :
    delimitPrefix (l₁ ++ l₂) = delimitPrefix l₁ ++ delimitPrefix l₂ := by
  induction l₁ with
  | nil => rfl
  | cons b bs ih => simp [delimitPrefix, ih]

-- Phase 5 (pushDelimitA): pop s1, push b then true onto Mh.k₀; when done, start Mh
def phase5 (sf : ∀ k, List (Mf.tm.Γ k)) (sh : ∀ k, List (Mh.tm.Γ k)) (s0 s2 : List Bool)
    (v : Combσ Mf Mh) :
    ∀ (s1 : List Bool) (acc : List (Mh.tm.Γ Mh.tm.k₀)),
      EvalsToInTime (combTM Mf Mh).step
        ⟨some (Sum.inl 5), v,
          mkStk Mf Mh sf
            (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀ acc)
            s0 s1 s2⟩
        (some ⟨some (Sum.inr (Sum.inr Mh.tm.main)), Sum.inr (Sum.inr Mh.tm.initialState),
          mkStk Mf Mh sf
            (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀
              ((delimitPrefix s1.reverse).map Mh.inputAlphabet.invFun ++ acc))
            s0 [] s2⟩)
        (s1.length + 1)
  | [], acc => by
    have hst : (combTM Mf Mh).step
        ⟨some (Sum.inl 5), v,
          mkStk Mf Mh sf
            (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀ acc)
            s0 [] s2⟩ =
        some ⟨some (Sum.inr (Sum.inr Mh.tm.main)), Sum.inr (Sum.inr Mh.tm.initialState),
          mkStk Mf Mh sf
            (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀ acc)
            s0 [] s2⟩ := by
      dsimp only [FinTM2.step, TM2.step, combTM, combProg, TM2.stepAux, mkStk, isSomeBool,
        List.head?, List.tail, cond_false]
      rw [mkStk_update_1]
      rfl
    simpa only [List.reverse_nil, delimitPrefix, List.map_nil, List.nil_append, List.length_nil,
      Nat.zero_add] using evals_step hst
  | b :: bs, acc => by
    have hst : (combTM Mf Mh).step
        ⟨some (Sum.inl 5), v,
          mkStk Mf Mh sf
            (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀ acc)
            s0 (b :: bs) s2⟩ =
        some ⟨some (Sum.inl 5), Sum.inl (some b),
          mkStk Mf Mh sf
            (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀
              (Mh.inputAlphabet.invFun true :: Mh.inputAlphabet.invFun b :: acc))
            s0 bs s2⟩ := by
      dsimp only [FinTM2.step, TM2.step, combTM, combProg, TM2.stepAux, mkStk, List.head?, List.tail,
        isSomeBool, getBool, cond_true]
      rw [mkStk_update_1]
      dsimp only [mkStk]
      rw [mkStk_update_inr_inl]
      have hself1 : (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq
          sh Mh.tm.k₀ acc) Mh.tm.k₀ = acc := by
        dsimp only [Function.update]; rw [dif_pos rfl]
      have hidem1 : @Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq
          (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀ acc)
          Mh.tm.k₀ (Mh.inputAlphabet.invFun b :: acc) =
          @Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀
            (Mh.inputAlphabet.invFun b :: acc) := by
        funext k; dsimp only [Function.update]
        by_cases hk : k = Mh.tm.k₀
        · subst hk; simp only [dif_pos]
        · simp only [dif_neg hk]
      rw [hself1, hidem1]
      dsimp only [mkStk]
      rw [mkStk_update_inr_inl]
      have hself2 : (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq
          sh Mh.tm.k₀ (Mh.inputAlphabet.invFun b :: acc)) Mh.tm.k₀ =
          Mh.inputAlphabet.invFun b :: acc := by
        dsimp only [Function.update]; rw [dif_pos rfl]
      have hidem2 : @Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq
          (@Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀
            (Mh.inputAlphabet.invFun b :: acc))
          Mh.tm.k₀ (Mh.inputAlphabet.invFun true :: Mh.inputAlphabet.invFun b :: acc) =
          @Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq sh Mh.tm.k₀
            (Mh.inputAlphabet.invFun true :: Mh.inputAlphabet.invFun b :: acc) := by
        funext k; dsimp only [Function.update]
        by_cases hk : k = Mh.tm.k₀
        · subst hk; simp only [dif_pos]
        · simp only [dif_neg hk]
      rw [hself2, hidem2]
      rfl
    have hrest := phase5 sf sh s0 s2 (Sum.inl (some b)) bs
      (Mh.inputAlphabet.invFun true :: Mh.inputAlphabet.invFun b :: acc)
    have htr := EvalsToInTime.trans (combTM Mf Mh).step 1 (bs.length + 1) _ _ _
      (evals_step hst) hrest
    simpa only [List.reverse_cons, delimitPrefix_append, delimitPrefix, List.map_append,
      List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append,
      List.length_cons, Nat.add_comm] using htr

/-- Polynomial evaluation on ℕ is monotone. -/
lemma poly_eval_mono (p : Polynomial ℕ) {a b : ℕ} (hab : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ ih₁ ih₂ =>
    simp only [Polynomial.eval_add]
    exact add_le_add ih₁ ih₂
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab n)

/-- Equivalence between the combined machine's input alphabet and Bool. -/
def combInputEquiv : (combTM Mf Mh).Γ (combTM Mf Mh).k₀ ≃ Bool :=
  Equiv.refl Bool

lemma initList_comb (l : List Bool) :
    initList (combTM Mf Mh) (l.map (combInputEquiv Mf Mh).invFun) =
    ⟨some (Sum.inl 0), Sum.inl none, mkStk Mf Mh (emptyF Mf) (emptyH Mh) l [] []⟩ := by
  have hmap : l.map (combInputEquiv Mf Mh).invFun =
      (l : List ((combTM Mf Mh).Γ (combTM Mf Mh).k₀)) := List.map_id l
  rw [hmap]
  dsimp only [initList, combTM]
  congr 1
  funext k
  cases k with
  | inl _ =>
    dsimp only [mkStk, emptyF]; rw [dif_neg (by simp)]
  | inr x =>
    cases x with
    | inl _ =>
      dsimp only [mkStk, emptyH]; rw [dif_neg (by simp)]
    | inr i =>
      fin_cases i
      · dsimp only [mkStk]
        have heq : (Sum.inr (Sum.inr ⟨0, by omega⟩) : CombK Mf Mh) = Sum.inr (Sum.inr 0) := rfl
        rw [dif_pos heq]; rfl
      · dsimp only [mkStk]
        rw [dif_neg (by intro h; injection h with h; injection h with h; exact absurd h (by decide))]
      · dsimp only [mkStk]
        rw [dif_neg (by intro h; injection h with h; injection h with h; exact absurd h (by decide))]

lemma haltList_comb (out : List (Mh.tm.Γ Mh.tm.k₁)) :
    haltList (combTM Mf Mh) out =
    ⟨none, Sum.inl none, mkStk Mf Mh (emptyF Mf) (haltList Mh.tm out).stk [] [] []⟩ := by
  dsimp only [haltList, combTM]
  congr 1
  funext k
  cases k with
  | inl _ =>
    dsimp only [mkStk, emptyF]; rw [dif_neg (by simp)]
  | inr x =>
    cases x with
    | inl k' =>
      dsimp only [mkStk]
      by_cases hk : k' = Mh.tm.k₁
      · subst hk; rw [dif_pos rfl, dif_pos rfl]
      · have hne : (Sum.inr (Sum.inl k') : CombK Mf Mh) ≠ Sum.inr (Sum.inl Mh.tm.k₁) :=
          fun h => hk (Sum.inl.inj (Sum.inr.inj h))
        rw [dif_neg hne, dif_neg hk]
    | inr i =>
      fin_cases i <;> (dsimp only [mkStk]; rw [dif_neg (by simp)])

lemma update_emptyF_eq_initStk (l : List (Mf.tm.Γ Mf.tm.k₀)) :
    @Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq (emptyF Mf) Mf.tm.k₀ l =
    (initList Mf.tm l).stk := by
  funext k
  unfold Function.update initList
  dsimp only
  split_ifs with h1
  · subst h1; rfl
  · rfl

lemma update_emptyH_eq_initStk (l : List (Mh.tm.Γ Mh.tm.k₀)) :
    @Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq (emptyH Mh) Mh.tm.k₀ l =
    (initList Mh.tm l).stk := by
  funext k
  unfold Function.update initList
  dsimp only
  split_ifs with h1
  · subst h1; rfl
  · rfl

lemma update_emptyF_eq_haltStk (l : List (Mf.tm.Γ Mf.tm.k₁)) :
    @Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq (emptyF Mf) Mf.tm.k₁ l =
    (haltList Mf.tm l).stk := by
  funext k
  unfold Function.update haltList
  dsimp only
  split_ifs with h1
  · subst h1; rfl
  · rfl

/-- The polynomial time bound of the combined machine. -/
noncomputable def combTime : Polynomial ℕ :=
  let Cf := tmMaxPush Mf.tm
  let argPoly := C 1 + C 3 * X + C Cf * Mf.time
  C 6 + C 6 * X + C (2 * Cf + 1) * Mf.time + Mh.time.comp argPoly

/-- Main construction: `TM2ComputableInPolyTime` for `fun x => h (x, f x)`. -/
noncomputable def combComputable :
    TM2ComputableInPolyTime (bitEncode : α → List Bool) (bitEncode : γ → List Bool)
      (fun x => h (x, f x)) where
  tm := combTM Mf Mh
  inputAlphabet := combInputEquiv Mf Mh
  outputAlphabet := Mh.outputAlphabet
  time := combTime Mf Mh
  outputsFun x := by
    let la := bitEncode x
    let lb := bitEncode (f x)
    let lc := bitEncode (h (x, f x))
    let Cf := tmMaxPush Mf.tm
    have hf := Mf.outputsFun x
    have hh := Mh.outputsFun (x, f x)
    have hlb_len : lb.length ≤ la.length + Mf.time.eval la.length * Cf := by
      have hlen := outputsInTime_len_le Mf.tm (la.map Mf.inputAlphabet.invFun)
        (lb.map Mf.outputAlphabet.invFun) (Mf.time.eval la.length) hf
      simpa using hlen
    -- Phase 0: copyIn
    have p0 : EvalsToInTime (combTM Mf Mh).step
        (initList (combTM Mf Mh) (la.map (combInputEquiv Mf Mh).invFun))
        (some ⟨some (Sum.inl 1), Sum.inl none,
          mkStk Mf Mh (emptyF Mf) (emptyH Mh) [] la.reverse []⟩)
        (la.length + 1) := by
      have h0 := phase0 Mf Mh (emptyF Mf) (emptyH Mh) [] (Sum.inl none) la []
      rw [initList_comb]
      simpa only [List.append_nil] using h0
    -- Phase 1: dupIn
    have p1 : EvalsToInTime (combTM Mf Mh).step
        ⟨some (Sum.inl 1), Sum.inl none, mkStk Mf Mh (emptyF Mf) (emptyH Mh) [] la.reverse []⟩
        (some ⟨some (Sum.inr (Sum.inl Mf.tm.main)), Sum.inr (Sum.inl Mf.tm.initialState),
          mkStk Mf Mh (initList Mf.tm (la.map Mf.inputAlphabet.invFun)).stk (emptyH Mh) la [] []⟩)
        (la.length + 1) := by
      have h1 := phase1 Mf Mh (emptyF Mf) (emptyH Mh) [] (Sum.inl none) la.reverse []
      simpa only [List.reverse_reverse, List.length_reverse, List.append_nil, emptyF,
        update_emptyF_eq_initStk] using h1
    have p01 := EvalsToInTime.trans (combTM Mf Mh).step _ _ _ _ _ p0 p1
    -- Phase F: simulate Mf
    have hsimF_eq := simF Mf Mh (emptyH Mh) la [] [] hf.steps
      (initList Mf.tm (la.map Mf.inputAlphabet.invFun))
      (haltList Mf.tm (lb.map Mf.outputAlphabet.invFun))
      hf.evals_in_steps Mf.tm.main rfl
    have pF : EvalsToInTime (combTM Mf Mh).step
        ⟨some (Sum.inr (Sum.inl Mf.tm.main)), Sum.inr (Sum.inl Mf.tm.initialState),
          mkStk Mf Mh (initList Mf.tm (la.map Mf.inputAlphabet.invFun)).stk (emptyH Mh) la [] []⟩
        (some ⟨some (Sum.inl 2), Sum.inl none,
          mkStk Mf Mh (haltList Mf.tm (lb.map Mf.outputAlphabet.invFun)).stk (emptyH Mh) la [] []⟩)
        (Mf.time.eval la.length) :=
      ⟨⟨hf.steps, by simpa only [initList, haltList] using hsimF_eq⟩, hf.steps_le_m⟩
    have p01F := EvalsToInTime.trans (combTM Mf Mh).step _ _ _ _ _ p01 pF
    -- Phase 2: revF
    have p2 : EvalsToInTime (combTM Mf Mh).step
        ⟨some (Sum.inl 2), Sum.inl none,
          mkStk Mf Mh (haltList Mf.tm (lb.map Mf.outputAlphabet.invFun)).stk (emptyH Mh) la [] []⟩
        (some ⟨some (Sum.inl 3), Sum.inl none,
          mkStk Mf Mh (emptyF Mf) (emptyH Mh) la [] lb.reverse⟩)
        (lb.length + 1) := by
      have h2 := phase2 Mf Mh (emptyF Mf) (emptyH Mh) la [] (Sum.inl none)
        (lb.map Mf.outputAlphabet.invFun) []
      have hmap_lb : (lb.map Mf.outputAlphabet.invFun).map Mf.outputAlphabet = lb := by
        simp [List.map_map]
      have hempty : @Function.update Mf.tm.K (fun k => List (Mf.tm.Γ k)) Mf.tm.kDecidableEq
          (emptyF Mf) Mf.tm.k₁ [] = emptyF Mf := by
        funext k; unfold Function.update; split_ifs with hk
        · subst hk; rfl
        · rfl
      simpa only [update_emptyF_eq_haltStk, hempty, hmap_lb, List.append_nil, List.length_map] using h2
    have p01F2 := EvalsToInTime.trans (combTM Mf Mh).step _ _ _ _ _ p01F p2
    -- Phase 3: pushF
    let sh3 := @Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq
      (emptyH Mh) Mh.tm.k₀ (Mh.inputAlphabet.invFun false :: lb.map Mh.inputAlphabet.invFun)
    have p3 : EvalsToInTime (combTM Mf Mh).step
        ⟨some (Sum.inl 3), Sum.inl none, mkStk Mf Mh (emptyF Mf) (emptyH Mh) la [] lb.reverse⟩
        (some ⟨some (Sum.inl 4), Sum.inl none, mkStk Mf Mh (emptyF Mf) sh3 la [] []⟩)
        (lb.length + 1) := by
      have h3 := phase3 Mf Mh (emptyF Mf) (emptyH Mh) la [] (Sum.inl none) lb.reverse []
      have hemptyH : @Function.update Mh.tm.K (fun k => List (Mh.tm.Γ k)) Mh.tm.kDecidableEq
          (emptyH Mh) Mh.tm.k₀ [] = emptyH Mh := by
        funext k; unfold Function.update; split_ifs with hk
        · subst hk; rfl
        · rfl
      simpa only [sh3, hemptyH, List.reverse_reverse, List.length_reverse, List.append_nil] using h3
    have p01F23 := EvalsToInTime.trans (combTM Mf Mh).step _ _ _ _ _ p01F2 p3
    -- Phase 4: revA
    have p4 : EvalsToInTime (combTM Mf Mh).step
        ⟨some (Sum.inl 4), Sum.inl none, mkStk Mf Mh (emptyF Mf) sh3 la [] []⟩
        (some ⟨some (Sum.inl 5), Sum.inl none, mkStk Mf Mh (emptyF Mf) sh3 [] la.reverse []⟩)
        (la.length + 1) := by
      have h4 := phase4 Mf Mh (emptyF Mf) sh3 [] (Sum.inl none) la []
      simpa only [List.append_nil] using h4
    have p01F234 := EvalsToInTime.trans (combTM Mf Mh).step _ _ _ _ _ p01F23 p4
    -- Phase 5: pushDelimitA
    have hpair_enc : bitEncode (x, f x) = delimit la ++ lb := rfl
    have hmh_in : (delimitPrefix la).map Mh.inputAlphabet.invFun ++
        (Mh.inputAlphabet.invFun false :: lb.map Mh.inputAlphabet.invFun) =
        (bitEncode (x, f x)).map Mh.inputAlphabet.invFun := by
      rw [hpair_enc, delimit_eq_delimitPrefix_append]
      simp [List.map_append, List.append_assoc]
    have p5 : EvalsToInTime (combTM Mf Mh).step
        ⟨some (Sum.inl 5), Sum.inl none, mkStk Mf Mh (emptyF Mf) sh3 [] la.reverse []⟩
        (some ⟨some (Sum.inr (Sum.inr Mh.tm.main)), Sum.inr (Sum.inr Mh.tm.initialState),
          mkStk Mf Mh (emptyF Mf)
            (initList Mh.tm ((bitEncode (x, f x)).map Mh.inputAlphabet.invFun)).stk [] [] []⟩)
        (la.length + 1) := by
      have h5 := phase5 Mf Mh (emptyF Mf) (emptyH Mh) [] [] (Sum.inl none) la.reverse
        (Mh.inputAlphabet.invFun false :: lb.map Mh.inputAlphabet.invFun)
      simpa only [sh3, List.reverse_reverse, List.length_reverse, hmh_in,
        update_emptyH_eq_initStk] using h5
    have p01F2345 := EvalsToInTime.trans (combTM Mf Mh).step _ _ _ _ _ p01F234 p5
    -- Phase H: simulate Mh
    have hsimH_eq := simH Mf Mh (emptyF Mf) [] [] [] hh.steps
      (initList Mh.tm ((bitEncode (x, f x)).map Mh.inputAlphabet.invFun))
      (haltList Mh.tm (lc.map Mh.outputAlphabet.invFun))
      hh.evals_in_steps Mh.tm.main rfl
    have pH : EvalsToInTime (combTM Mf Mh).step
        ⟨some (Sum.inr (Sum.inr Mh.tm.main)), Sum.inr (Sum.inr Mh.tm.initialState),
          mkStk Mf Mh (emptyF Mf)
            (initList Mh.tm ((bitEncode (x, f x)).map Mh.inputAlphabet.invFun)).stk [] [] []⟩
        (some (haltList (combTM Mf Mh) (lc.map Mh.outputAlphabet.invFun)))
        (Mh.time.eval (bitEncode (x, f x)).length) :=
      ⟨⟨hh.steps, Eq.trans hsimH_eq
        (congrArg some (haltList_comb Mf Mh (lc.map Mh.outputAlphabet.invFun)).symm)⟩, hh.steps_le_m⟩
    have pAll := EvalsToInTime.trans (combTM Mf Mh).step _ _ _ _ _ p01F2345 pH
    -- Bound total time by combTime.eval la.length
    have hpair_len : (bitEncode (x, f x)).length ≤ 1 + 3 * la.length + Cf * Mf.time.eval la.length := by
      rw [hpair_enc, List.length_append, length_delimit]
      have : Mf.time.eval la.length * Cf = Cf * Mf.time.eval la.length := Nat.mul_comm _ _
      omega
    have hmh_bound : Mh.time.eval (bitEncode (x, f x)).length ≤
        (Mh.time.comp (C 1 + C 3 * X + C Cf * Mf.time)).eval la.length := by
      rw [Polynomial.eval_comp]
      have heval : (C 1 + C 3 * X + C Cf * Mf.time).eval la.length =
          1 + 3 * la.length + Cf * Mf.time.eval la.length := by
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      rw [heval]
      exact poly_eval_mono Mh.time hpair_len
    have htime_bound :
        Mh.time.eval (bitEncode (x, f x)).length +
          ((la.length + 1) + ((la.length + 1) + ((lb.length + 1) +
            ((lb.length + 1) + (Mf.time.eval la.length + ((la.length + 1) + (la.length + 1))))))) ≤
        (combTime Mf Mh).eval la.length := by
      have hct : (combTime Mf Mh).eval la.length =
          6 + 6 * la.length + (2 * Cf + 1) * Mf.time.eval la.length +
            (Mh.time.comp (C 1 + C 3 * X + C Cf * Mf.time)).eval la.length := by
        simp [combTime, Cf, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      rw [hct]
      have hcomm : Mf.time.eval la.length * Cf = Cf * Mf.time.eval la.length := Nat.mul_comm _ _
      have h2lb : 2 * lb.length ≤ 2 * la.length + 2 * Cf * Mf.time.eval la.length := by
        have := Nat.mul_le_mul_left 2 hlb_len
        linarith
      linarith
    exact evals_le pAll htime_bound

end CombinedMachine

end OMAR2H1

theorem OMA.solution : OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2.H1 := by
  intro Λ F ⟨Mf⟩ ⟨Mh⟩
  exact ⟨OMAR2H1.combComputable Mf Mh⟩
