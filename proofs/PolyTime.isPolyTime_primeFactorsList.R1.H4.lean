import OMAReductions.R_PolyTime_isPolyTime_primeFactorsList_R1
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Size
import Mathlib.Data.Num.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Computability.Encoding

/-!
# Polynomial-time quotient iteration

Credit: @neiam00

The caller emits each word as a self-delimiting block. A verified binary long-division subroutine computes the next quotient, and the input bit length bounds the number of calls. The clock includes the size of every returned word.
-/

/- Run a TM2 statement on selected stacks of a larger machine, leaving the other stacks
unchanged. Halting may transfer control to a specified continuation label. -/

namespace FactorMachineLift

open Turing.TM2

variable {K J Λ Λ' σ σ' : Type} {Γ : K → Type} {Γ' : J → Type}

/-- The stack/symbol embedding and register operations for a machine inside a caller. -/
structure Lift (Γ : K → Type) (Γ' : J → Type) (Λ Λ' σ σ' : Type) where
  stack : K ↪ J
  symbol : ∀ k, Γ k ≃ Γ' (stack k)
  label : Λ → Λ'
  exitLabel : Option Λ'
  read : σ' → σ
  write : σ' → σ → σ'
  read_write : ∀ w v, read (write w v) = v
  write_write : ∀ w v u, write (write w v) u = write w u

namespace Lift

variable (e : Lift Γ Γ' Λ Λ' σ σ')

def mapLabel : Option Λ → Option Λ'
  | none => e.exitLabel
  | some l => some (e.label l)

/-- Translate operations on the callee's stacks, registers and control labels. -/
def stmt : Stmt Γ Λ σ → Stmt Γ' Λ' σ'
  | .push k f q => .push (e.stack k) (fun w => e.symbol k (f (e.read w))) (stmt q)
  | .peek k f q => .peek (e.stack k)
      (fun w a => e.write w (f (e.read w) (a.map (e.symbol k).symm))) (stmt q)
  | .pop k f q => .pop (e.stack k)
      (fun w a => e.write w (f (e.read w) (a.map (e.symbol k).symm))) (stmt q)
  | .load f q => .load (fun w => e.write w (f (e.read w))) (stmt q)
  | .branch f qt qf => .branch (fun w => f (e.read w)) (stmt qt) (stmt qf)
  | .goto f => .goto (fun w => e.label (f (e.read w)))
  | .halt => match e.exitLabel with
    | none => .halt
    | some l => .goto (fun _ => l)

/-- The selected stacks encode the callee's stacks and every other stack retains its
contents from the start of the call. -/
structure StacksMatch (frozen : ∀ j, List (Γ' j))
    (s : ∀ k, List (Γ k)) (t : ∀ j, List (Γ' j)) : Prop where
  inside : ∀ k, t (e.stack k) = (s k).map (e.symbol k)
  outside : ∀ j, (∀ k, e.stack k ≠ j) → t j = frozen j

structure Matches (base : σ') (frozen : ∀ j, List (Γ' j))
    (c : Cfg Γ Λ σ) (C : Cfg Γ' Λ' σ') : Prop where
  label_eq : C.l = e.mapLabel c.l
  state_eq : C.var = e.write base c.var
  stack_eq : e.StacksMatch frozen c.stk C.stk

variable [DecidableEq K] [DecidableEq J]

theorem StacksMatch.update {frozen s t} (h : e.StacksMatch frozen s t)
    (k : K) (xs : List (Γ k)) :
    e.StacksMatch frozen (Function.update s k xs)
      (Function.update t (e.stack k) (xs.map (e.symbol k))) := by
  constructor
  · intro i
    by_cases hi : i = k
    · subst i
      simp
    · have hkey : e.stack i ≠ e.stack k := fun a => hi (e.stack.injective a)
      simpa [Function.update_of_ne hi, Function.update_of_ne hkey] using h.inside i
  · intro j hj
    have hkey : j ≠ e.stack k := (hj k).symm
    simpa [Function.update_of_ne hkey] using h.outside j hj

private theorem decode_head {α β : Type} (h : α ≃ β) (xs : List α) :
    ((xs.map h).head?).map h.symm = xs.head? := by
  cases xs <;> simp

/-- A source statement and its translation take exactly one step, including every nested
stack primitive before the next goto or halt. -/
theorem stepAux_stmt (q : Stmt Γ Λ σ) (base : σ') (frozen : ∀ j, List (Γ' j))
    (v : σ) (s : ∀ k, List (Γ k)) (t : ∀ j, List (Γ' j))
    (h : e.StacksMatch frozen s t) :
    e.Matches base frozen (stepAux q v s) (stepAux (e.stmt q) (e.write base v) t) := by
  induction q generalizing v s t with
  | push k f q ih =>
    simp only [stmt, stepAux, e.read_write, h.inside k]
    exact ih _ _ _ (h.update e k (f v :: s k))
  | peek k f q ih =>
    simp only [stmt, stepAux, e.read_write, e.write_write, h.inside k, decode_head]
    exact ih _ _ _ h
  | pop k f q ih =>
    simp only [stmt, stepAux, e.read_write, e.write_write, h.inside k, decode_head]
    simpa using ih _ _ _ (h.update e k (s k).tail)
  | load f q ih =>
    simp only [stmt, stepAux, e.read_write, e.write_write]
    exact ih _ _ _ h
  | branch f qt qf iht ihf =>
    simp only [stmt, stepAux, e.read_write]
    cases f v
    · exact ihf _ _ _ h
    · exact iht _ _ _ h
  | goto f =>
    exact ⟨by simp [stmt, stepAux, mapLabel, e.read_write], rfl, h⟩
  | halt =>
    cases hx : e.exitLabel with
    | none => exact ⟨by simp [stmt, stepAux, mapLabel, hx], by simp [stmt, stepAux, hx],
                       by simpa [stmt, stepAux, hx] using h⟩
    | some l => exact ⟨by simp [stmt, stepAux, mapLabel, hx], by simp [stmt, stepAux, hx],
                         by simpa [stmt, stepAux, hx] using h⟩

omit [DecidableEq K] [DecidableEq J] in
/-- The callee configuration, caller register base and untouched stacks determine the host. -/
theorem Matches.unique {base frozen c C D}
    (hc : e.Matches base frozen c C) (hd : e.Matches base frozen c D) : C = D := by
  have hl := hc.label_eq.trans hd.label_eq.symm
  have hv := hc.state_eq.trans hd.state_eq.symm
  have hs : C.stk = D.stk := by
    funext j
    by_cases hj : ∃ k, e.stack k = j
    · obtain ⟨k, rfl⟩ := hj
      exact (hc.stack_eq.inside k).trans (hd.stack_eq.inside k).symm
    · have hout : ∀ k, e.stack k ≠ j := fun k hk => hj ⟨k, hk⟩
      exact (hc.stack_eq.outside j hout).trans (hd.stack_eq.outside j hout).symm
  cases C
  cases D
  congr

variable {p : Λ → Stmt Γ Λ σ} {P : Λ' → Stmt Γ' Λ' σ'}

/-- A live transition produces an agreeing host configuration. The rest of the host
program, including the continuation's code, is unrestricted. -/
theorem step_matches (hprog : ∀ l, P (e.label l) = e.stmt (p l))
    {base frozen c d C} (hc : e.Matches base frozen c C) (hs : step p c = some d) :
    ∃ D, step P C = some D ∧ e.Matches base frozen d D := by
  cases c with
  | mk l v s =>
    cases l with
    | none => simp [step] at hs
    | some l =>
      cases C with
      | mk L V S =>
        have hL : L = some (e.label l) := hc.label_eq
        have hV : V = e.write base v := hc.state_eq
        subst L
        subst V
        have hd : stepAux (p l) v s = d := Option.some.inj hs
        subst d
        exact ⟨_, by simp [step, hprog], e.stepAux_stmt _ _ _ _ _ _ hc.stack_eq⟩

/-- Transfer an exact number of live transitions. An embedded halt may be a live
continuation label, so the statement ends on the same step as the callee. -/
theorem iterate_matches (hprog : ∀ l, P (e.label l) = e.stmt (p l))
    (n : ℕ) {base frozen c d C} (hc : e.Matches base frozen c C)
    (hs : (flip bind (step p))^[n] (some c) = some d) :
    ∃ D, (flip bind (step P))^[n] (some C) = some D ∧ e.Matches base frozen d D := by
  induction n generalizing c C with
  | zero =>
    have hd : c = d := Option.some.inj hs
    subst d
    exact ⟨C, rfl, hc⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hs ⊢
    change (flip bind (step p))^[n] (step p c) = some d at hs
    cases hnext : step p c with
    | none =>
      rw [hnext, Function.iterate_fixed (f := flip bind (step p)) (x := none) rfl n] at hs
      cases hs
    | some cnext =>
      obtain ⟨Cnext, hCnext, hmatch⟩ := e.step_matches hprog hc hnext
      obtain ⟨D, hsteps, hD⟩ := ih hmatch (hnext ▸ hs)
      exact ⟨D, by change (flip bind (step P))^[n] (step P C) = some D; rwa [hCnext], hD⟩

/-- Lift a time-bounded execution to named host configurations. Its step count is unchanged. -/
def evalsToInTime (hprog : ∀ l, P (e.label l) = e.stmt (p l))
    {base frozen c d C D budget} (hc : e.Matches base frozen c C)
    (hd : e.Matches base frozen d D)
    (run : StateTransition.EvalsToInTime (step p) c (some d) budget) :
    StateTransition.EvalsToInTime (step P) C (some D) budget where
  steps := run.steps
  steps_le_m := run.steps_le_m
  evals_in_steps := by
    obtain ⟨actual, ha, hactual⟩ := e.iterate_matches hprog run.steps hc run.evals_in_steps
    simpa only [hactual.unique e hd] using ha

end Lift

end FactorMachineLift

/- Compilation of finite-stack programs making calls to a Boolean-valued TM2 machine. -/

namespace FactorOracleMachine

open Turing FactorMachineLift StateTransition

structure OracleProgram where
  K : Type
  [kDec : DecidableEq K]
  [kFin : Fintype K]
  Λ : Type
  [lDec : DecidableEq Λ]
  [lFin : Fintype Λ]
  σ : Type
  [sFin : Fintype σ]
  k₀ : K
  k₁ : K
  arg : K
  main : Λ
  call : Λ
  resume : Λ
  initialState : σ
  m : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ

instance (C : OracleProgram) : DecidableEq C.K := C.kDec
instance (C : OracleProgram) : Fintype C.K := C.kFin
instance (C : OracleProgram) : DecidableEq C.Λ := C.lDec
instance (C : OracleProgram) : Fintype C.Λ := C.lFin
instance (C : OracleProgram) : Fintype C.σ := C.sFin

namespace OracleProgram

variable (C : OracleProgram)

abbrev Cfg := TM2.Cfg (fun _ : C.K => Bool) C.Λ C.σ

def tm : FinTM2 where
  K := C.K
  Γ _ := Bool
  Λ := C.Λ
  σ := C.σ
  k₀ := C.k₀
  k₁ := C.k₁
  main := C.main
  initialState := C.initialState
  m := C.m

/-- An atomic call can be used only with a validly encoded argument. -/
inductive Run {A : Type} (encode : A → List Bool) (query : A → Bool) (cost : ℕ → ℕ) :
    C.Cfg → C.Cfg → ℕ → Prop
  | refl (c) : Run encode query cost c c 0
  | normal {c d} (hc : c.l ≠ some C.call) (hs : TM2.step C.m c = some d) : Run encode query cost c d 1
  | oracle (x : A) (v : C.σ) (s : C.K → List Bool) (h : s C.arg = encode x) :
      Run encode query cost ⟨some C.call, v, s⟩
        ⟨some C.resume, v, Function.update s C.arg [query x]⟩
        (cost (encode x).length + 2 * (encode x).length + 4)
  | trans {a b c t u} : Run encode query cost a b t → Run encode query cost b c u →
      Run encode query cost a c (t + u)
  | mono {a b t u} : Run encode query cost a b t → t ≤ u → Run encode query cost a b u

inductive Phase | reverse | transfer | finish deriving DecidableEq
instance : Fintype Phase := ⟨{.reverse, .transfer, .finish}, by intro p; cases p <;> simp⟩

variable (Q : FinTM2) (ei : Q.Γ Q.k₀ ≃ Bool) (eo : Q.Γ Q.k₁ ≃ Bool)

abbrev Index := C.K ⊕ (Q.K ⊕ Unit)
abbrev Label := C.Λ ⊕ (Q.Λ ⊕ Phase)
abbrev Register := C.σ × Q.σ × Option Bool
abbrev Alphabet : C.Index Q → Type := Sum.elim (fun _ => Bool) (Sum.elim Q.Γ (fun _ => Bool))
abbrev HostCfg := TM2.Cfg (C.Alphabet Q) (C.Label Q) (C.Register Q)

def caller : Lift (fun _ : C.K => Bool) (C.Alphabet Q) C.Λ (C.Label Q) C.σ (C.Register Q) where
  stack := ⟨Sum.inl, Sum.inl_injective⟩
  symbol _ := Equiv.refl _
  label := Sum.inl
  exitLabel := none
  read := Prod.fst
  write w v := (v, w.2)
  read_write _ _ := rfl
  write_write _ _ _ := rfl

def callee : Lift Q.Γ (C.Alphabet Q) Q.Λ (C.Label Q) Q.σ (C.Register Q) where
  stack := ⟨fun k => .inr (.inl k), fun _ _ h => Sum.inl.inj (Sum.inr.inj h)⟩
  symbol _ := Equiv.refl _
  label l := .inr (.inl l)
  exitLabel := some (.inr (.inr .finish))
  read v := v.2.1
  write w v := (w.1, v, w.2.2)
  read_write _ _ := rfl
  write_write _ _ _ := rfl

def program : C.Label Q → TM2.Stmt (C.Alphabet Q) (C.Label Q) (C.Register Q)
  | .inl l => if l = C.call then .goto (fun _ => .inr (.inr .reverse)) else (C.caller Q).stmt (C.m l)
  | .inr (.inl l) => (C.callee Q).stmt (Q.m l)
  | .inr (.inr .reverse) =>
      .pop (.inl C.arg) (fun w o => (w.1, w.2.1, o))
        (.branch (fun w => w.2.2.isSome)
          (.push (.inr (.inr ())) (fun w => w.2.2.getD false) (.goto fun _ => .inr (.inr .reverse)))
          (.goto fun _ => .inr (.inr .transfer)))
  | .inr (.inr .transfer) =>
      .pop (.inr (.inr ())) (fun w o => (w.1, w.2.1, o))
        (.branch (fun w => w.2.2.isSome)
          (.push (.inr (.inl Q.k₀)) (fun w => ei.symm (w.2.2.getD false)) (.goto fun _ => .inr (.inr .transfer)))
          (.goto fun _ => .inr (.inl Q.main)))
  | .inr (.inr .finish) =>
      .pop (.inr (.inl Q.k₁)) (fun w o => (w.1, w.2.1, o.map eo))
        (.push (.inl C.arg) (fun w => w.2.2.getD false)
          (.load (fun w => (w.1, w.2.1, none)) (.goto fun _ => .inl C.resume)))

def compiled : FinTM2 :=
  letI := Q.kFin
  letI := Q.ΛFin
  letI := Q.σFin
  { K := C.Index Q
    Γ := C.Alphabet Q
    Λ := C.Label Q
    σ := C.Register Q
    k₀ := .inl C.k₀
    k₁ := .inl C.k₁
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    main := .inl C.main
    initialState := (C.initialState, Q.initialState, none)
    m := C.program Q ei eo }

def tapes (s : C.K → List Bool) (t : ∀ k, List (Q.Γ k)) (b : List Bool) :
    ∀ j, List (C.Alphabet Q j)
  | .inl k => s k
  | .inr (.inl k) => t k
  | .inr (.inr _) => b

def embed (c : C.Cfg) : C.HostCfg Q :=
  ⟨c.l.map Sum.inl, (c.var, Q.initialState, none), C.tapes Q c.stk (fun _ => []) []⟩

private abbrev Stores := ∀ k, List (Q.Γ k)

@[simp] private theorem tapes_c (s t b k) : C.tapes Q s t b (.inl k) = s k := rfl
@[simp] private theorem tapes_q (s t b k) : C.tapes Q s t b (.inr (.inl k)) = t k := rfl
@[simp] private theorem tapes_b (s t b) : C.tapes Q s t b (.inr (.inr ())) = b := rfl

@[simp] private theorem update_c (s t b k) (xs : List Bool) :
    Function.update (C.tapes Q s t b) (.inl k) xs = C.tapes Q (Function.update s k xs) t b := by
  funext j
  rcases j with i | i | u
  · by_cases h : i = k
    · subst i; simp [Function.update, tapes]
    · simp [Function.update, tapes, h]
  · simp [Function.update, tapes]
  · cases u; simp [Function.update, tapes]

@[simp] private theorem update_q (s t b k) (xs : List (Q.Γ k)) :
    Function.update (C.tapes Q s t b) (.inr (.inl k)) xs = C.tapes Q s (Function.update t k xs) b := by
  funext j
  rcases j with i | i | u
  · simp [Function.update, tapes]
  · by_cases h : i = k
    · subst i; simp [Function.update, tapes]
    · simp [Function.update, tapes, h]
  · cases u; simp [Function.update, tapes]

@[simp] private theorem update_b (s t b) (xs : List Bool) :
    Function.update (C.tapes Q s t b) (.inr (.inr ())) xs = C.tapes Q s t xs := by
  funext j
  rcases j with i | i | u
  · simp [Function.update, tapes]
  · simp [Function.update, tapes]
  · cases u; simp [Function.update, tapes]

private def oneStack {K : Type} [DecidableEq K] (Γ : K → Type) (k : K) (xs : List (Γ k)) :
    ∀ j, List (Γ j) := Function.update (fun j => ([] : List (Γ j))) k xs

private def stage (l : C.Label Q) (v : C.σ) (o : Option Bool) (s : C.K → List Bool)
    (t : Stores Q) (b : List Bool) : C.HostCfg Q :=
  ⟨some l, (v, Q.initialState, o), C.tapes Q s t b⟩

private def Exact (a b : C.HostCfg Q) (t : ℕ) : Prop :=
  (flip bind (TM2.step (C.program Q ei eo)))^[t] (some a) = some b

private theorem next {a b d t} (ab : TM2.step (C.program Q ei eo) a = some b)
    (bd : C.Exact Q ei eo b d t) : C.Exact Q ei eo a d (t+1) := by
  unfold Exact at *
  rw [Function.iterate_succ_apply]
  change (flip bind (TM2.step (C.program Q ei eo)))^[t] (TM2.step (C.program Q ei eo) a) = some d
  rwa [ab]

private theorem one {a b} (ab : TM2.step (C.program Q ei eo) a = some b) : C.Exact Q ei eo a b 1 := ab

private theorem join {a b d t u} (ab : C.Exact Q ei eo a b t) (bd : C.Exact Q ei eo b d u) :
    C.Exact Q ei eo a d (u+t) := by
  unfold Exact at *
  rw [Function.iterate_add_apply, ab, bd]

private theorem reverse_run (v : C.σ) (s : C.K → List Bool) (xs bs : List Bool) (o : Option Bool) :
    C.Exact Q ei eo
      (C.stage Q (.inr (.inr .reverse)) v o (Function.update s C.arg xs) (fun _ => []) bs)
      (C.stage Q (.inr (.inr .transfer)) v none (Function.update s C.arg []) (fun _ => []) (xs.reverse ++ bs))
      (xs.length+1) := by
  induction xs generalizing bs o with
  | nil => apply C.one; simp [stage, program, TM2.stepAux]
  | cons a xs ih =>
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using
      (C.next Q ei eo (a := C.stage Q (.inr (.inr .reverse)) v o (Function.update s C.arg (a::xs)) (fun _ => []) bs)
        (by simp [stage, program, TM2.stepAux]) (ih (a::bs) (some a)))

private theorem transfer_run (v : C.σ) (s : C.K → List Bool) (bs : List Bool)
    (xs : List (Q.Γ Q.k₀)) (o : Option Bool) :
    C.Exact Q ei eo
      (C.stage Q (.inr (.inr .transfer)) v o s (oneStack Q.Γ Q.k₀ xs) bs)
      (C.stage Q (.inr (.inl Q.main)) v none s (oneStack Q.Γ Q.k₀ (bs.reverse.map ei.symm ++ xs)) [])
      (bs.length+1) := by
  induction bs generalizing xs o with
  | nil => apply C.one; simp [stage, program, TM2.stepAux]
  | cons a bs ih =>
    simpa only [List.length_cons, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append] using
      (C.next Q ei eo (a := C.stage Q (.inr (.inr .transfer)) v o s (oneStack Q.Γ Q.k₀ xs) (a::bs))
        (by simp [stage, program, TM2.stepAux, oneStack]) (ih (ei.symm a::xs) (some a)))

private theorem caller_match (c : C.Cfg) : (C.caller Q).Matches
    (C.initialState, Q.initialState, none) (fun _ => []) c (C.embed Q c) := by
  refine ⟨?_, rfl, ⟨?_, ?_⟩⟩
  · change c.l.map Sum.inl = (C.caller Q).mapLabel c.l
    cases c.l <;> rfl
  · intro k
    change c.stk k = (c.stk k).map id
    simp
  · rintro (k | k | u) h
    · exact False.elim (h k rfl)
    · rfl
    · cases u; rfl

private theorem ordinary_run {c d : C.Cfg} (hc : c.l ≠ some C.call) (hs : TM2.step C.m c = some d) :
    C.Exact Q ei eo (C.embed Q c) (C.embed Q d) 1 := by
  rcases c with ⟨_ | l, v, s⟩
  · contradiction
  · have hl : l ≠ C.call := fun h => hc (congrArg some h)
    have hd : TM2.stepAux (C.m l) v s = d := Option.some.inj hs
    subst d
    have hmatch := (C.caller Q).stepAux_stmt (C.m l) (C.initialState, Q.initialState, none)
      (fun _ => []) v s (C.tapes Q s (fun _ => []) []) (C.caller_match Q ⟨some l, v, s⟩).stack_eq
    apply C.one
    change some (TM2.stepAux (C.program Q ei eo (.inl l)) _ _) = _
    rw [show C.program Q ei eo (.inl l) = (C.caller Q).stmt (C.m l) by simp [program, hl]]
    exact congrArg some (hmatch.unique _ (C.caller_match Q _))

private def embedQuery (v : C.σ) (s : C.K → List Bool) (d : Q.Cfg) : C.HostCfg Q :=
  ⟨(C.callee Q).mapLabel d.l, (v, d.var, none), C.tapes Q s d.stk []⟩

private theorem callee_match (v : C.σ) (s : C.K → List Bool) (d : Q.Cfg) :
    (C.callee Q).Matches (v, Q.initialState, none) (C.tapes Q s (fun _ => []) []) d (C.embedQuery Q v s d) := by
  refine ⟨rfl, rfl, ⟨?_, ?_⟩⟩
  · intro k
    change d.stk k = (d.stk k).map id
    simp
  · rintro (k | k | u) h
    · rfl
    · exact False.elim (h k rfl)
    · cases u; rfl

private theorem init_tapes (T : FinTM2) (xs : List (T.Γ T.k₀)) :
    (initList T xs).stk = oneStack T.Γ T.k₀ xs := by
  funext j
  by_cases h : j = T.k₀
  · subst j; simp [initList, oneStack, Function.update]
  · simp [initList, oneStack, Function.update, h]

private theorem halt_tapes (T : FinTM2) (xs : List (T.Γ T.k₁)) :
    (haltList T xs).stk = oneStack T.Γ T.k₁ xs := by
  funext j
  by_cases h : j = T.k₁
  · subst j; simp [haltList, oneStack, Function.update]
  · simp [haltList, oneStack, Function.update, h]

private theorem nil_stack {K : Type} [DecidableEq K] (Γ : K → Type) (k : K) :
    oneStack Γ k [] = (fun _ => []) := by
  funext j
  by_cases h : j = k
  · subst j; simp [oneStack]
  · simp [oneStack, h]

private theorem start_call (v : C.σ) (s : C.K → List Bool) (w : List Bool) (harg : s C.arg = w) :
    C.Exact Q ei eo (C.embed Q ⟨some C.call, v, s⟩)
      (C.embedQuery Q v (Function.update s C.arg []) (initList Q (w.map ei.symm))) (2 * w.length + 3) := by
  have hrev := C.reverse_run Q ei eo v s w [] none
  have htrans := C.transfer_run Q ei eo v (Function.update s C.arg []) w.reverse [] none
  have hstart : Function.update s C.arg w = s := by rw [← harg]; exact Function.update_eq_self _ _
  rw [hstart, List.append_nil] at hrev
  rw [List.reverse_reverse, List.append_nil, nil_stack, List.length_reverse] at htrans
  have henter := C.one Q ei eo (a := C.embed Q ⟨some C.call, v, s⟩)
    (b := C.stage Q (.inr (.inr .reverse)) v none s (fun _ => []) []) (by simp [embed, stage, program, TM2.stepAux])
  have hs := C.join Q ei eo (C.join Q ei eo henter hrev) htrans
  convert hs using 1
  · unfold embedQuery stage
    rw [init_tapes]
    rfl
  · omega

private theorem finish_call (v : C.σ) (s : C.K → List Bool) (r : Bool) :
    C.Exact Q ei eo
      (C.embedQuery Q v (Function.update s C.arg []) (haltList Q [eo.symm r]))
      (C.embed Q ⟨some C.resume, v, Function.update s C.arg [r]⟩) 1 := by
  apply C.one
  unfold embedQuery embed
  rw [halt_tapes]
  change some (TM2.stepAux (C.program Q ei eo (.inr (.inr .finish)))
    (v, Q.initialState, none)
    (C.tapes Q (Function.update s C.arg []) (oneStack Q.Γ Q.k₁ [eo.symm r]) [])) = _
  simp [program, TM2.stepAux, oneStack]

private theorem call_run (v : C.σ) (s : C.K → List Bool) (w : List Bool) (r : Bool) (t : ℕ)
    (harg : s C.arg = w) (oracleRun : TM2OutputsInTime Q (w.map ei.symm) (some [eo.symm r]) t) :
    ∃ k ≤ t + 2*w.length + 4, C.Exact Q ei eo (C.embed Q ⟨some C.call, v, s⟩)
      (C.embed Q ⟨some C.resume, v, Function.update s C.arg [r]⟩) k := by
  let cleared := Function.update s C.arg []
  let middle := (C.callee Q).evalsToInTime (p := Q.m) (P := C.program Q ei eo) (fun _ => rfl)
    (C.callee_match Q v cleared (initList Q (w.map ei.symm)))
    (C.callee_match Q v cleared (haltList Q [eo.symm r])) oracleRun
  have hmiddle : C.Exact Q ei eo (C.embedQuery Q v cleared (initList Q (w.map ei.symm)))
      (C.embedQuery Q v cleared (haltList Q [eo.symm r])) middle.steps := middle.evals_in_steps
  have h := C.join Q ei eo (C.join Q ei eo (C.start_call Q ei eo v s w harg) hmiddle) (C.finish_call Q ei eo v s r)
  exact ⟨_, by have := middle.steps_le_m; omega, h⟩

private theorem simulate {A : Type} {encode : A → List Bool} {query : A → Bool} {cost : ℕ → ℕ}
    (oracleRun : ∀ x, TM2OutputsInTime Q ((encode x).map ei.symm) (some [eo.symm (query x)]) (cost (encode x).length))
    {a b : C.Cfg} {t : ℕ} (run : C.Run encode query cost a b t) :
    ∃ k ≤ t, C.Exact Q ei eo (C.embed Q a) (C.embed Q b) k := by
  induction run with
  | refl a => exact ⟨0, Nat.le_refl _, rfl⟩
  | normal hc hs => exact ⟨1, Nat.le_refl _, C.ordinary_run Q ei eo hc hs⟩
  | oracle x v s h => exact C.call_run Q ei eo v s _ _ _ h (oracleRun x)
  | trans _ _ ih ih' =>
    obtain ⟨k, hk, h⟩ := ih
    obtain ⟨j, hj, h'⟩ := ih'
    exact ⟨j+k, by omega, C.join Q ei eo h h'⟩
  | mono _ hle ih =>
    obtain ⟨k, hk, h⟩ := ih
    exact ⟨k, hk.trans hle, h⟩

private theorem singleCaller (k : C.K) (xs : List Bool) :
    C.tapes Q (oneStack (fun _ : C.K => Bool) k xs) (fun _ => []) [] =
      oneStack (C.Alphabet Q) (.inl k) xs := by
  have empty : C.tapes Q (fun _ => []) (fun _ => []) [] = (fun _ => []) := by
    funext j
    rcases j with i | i | u <;> rfl
  unfold oneStack
  rw [← update_c, empty]

private theorem embed_init (xs : List Bool) : C.embed Q (initList C.tm xs) =
    initList (C.compiled Q ei eo) xs := by
  apply congrArg (fun s => (⟨some (.inl C.main), (C.initialState, Q.initialState, none), s⟩ : C.HostCfg Q))
  change C.tapes Q (initList C.tm xs).stk (fun _ => []) [] = (initList (C.compiled Q ei eo) xs).stk
  exact (congrArg (fun s => C.tapes Q s (fun _ => []) []) (init_tapes C.tm xs)).trans
    ((C.singleCaller Q C.k₀ xs).trans (init_tapes (C.compiled Q ei eo) xs).symm)

private theorem embed_halt (xs : List Bool) : C.embed Q (haltList C.tm xs) =
    haltList (C.compiled Q ei eo) xs := by
  apply congrArg (fun s => (⟨none, (C.initialState, Q.initialState, none), s⟩ : C.HostCfg Q))
  change C.tapes Q (haltList C.tm xs).stk (fun _ => []) [] = (haltList (C.compiled Q ei eo) xs).stk
  exact (congrArg (fun s => C.tapes Q s (fun _ => []) []) (halt_tapes C.tm xs)).trans
    ((C.singleCaller Q C.k₁ xs).trans (halt_tapes (C.compiled Q ei eo) xs).symm)

/-- Any valid time-budgeted oracle program executes on a standard finite TM2 machine.
The caller's workspace survives every call and all callee workspace is cleared before resuming. -/
theorem compile_run {A : Type} {encode : A → List Bool} {query : A → Bool} {cost : ℕ → ℕ}
    (oracleRun : ∀ x, TM2OutputsInTime Q ((encode x).map ei.symm) (some [eo.symm (query x)]) (cost (encode x).length))
    {input output : List Bool} {t : ℕ}
    (run : C.Run encode query cost (initList C.tm input) (haltList C.tm output) t) :
    Nonempty (TM2OutputsInTime (C.compiled Q ei eo) input (some output) t) := by
  obtain ⟨k, hk, h⟩ := C.simulate Q ei eo oracleRun run
  unfold Exact at h
  rw [embed_init C Q ei eo, embed_halt C Q ei eo] at h
  exact ⟨⟨⟨k, h⟩, hk⟩⟩

end OracleProgram
end FactorOracleMachine

/- Output and stack growth bounds for the finite multitape machine used by `IsPolyTime`. -/

namespace FactorMachineBound

open Turing ComplexityTheory BitstringEncoding

private def pushes {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q | .pop _ _ q | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ | .halt => 0

private theorem stepAux_bound {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (j : K) :
    ((TM2.stepAux q v S).stk j).length ≤ (S j).length + pushes q := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [TM2.stepAux, pushes]
    have h := ih v (Function.update S k (f v :: S k))
    by_cases heq : j = k
    · subst j
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    · simp [Function.update_of_ne heq] at h
      omega
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    simp only [TM2.stepAux, pushes]
    have h := ih (f v (S k).head?) (Function.update S k (S k).tail)
    by_cases heq : j = k
    · subst j
      simpa only [Function.update_self] using h.trans
        (Nat.add_le_add_right (by simp) (pushes q))
    · simpa [Function.update_of_ne heq] using h
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
    cases he : f v <;> simp only [TM2.stepAux, he, cond_true, cond_false, pushes]
    · exact (ihr v S).trans (Nat.add_le_add_left (le_max_right _ _) _)
    · exact (ihq v S).trans (Nat.add_le_add_left (le_max_left _ _) _)
  | goto f => simp [TM2.stepAux, pushes]
  | halt => simp [TM2.stepAux, pushes]

private def growth (M : FinTM2) : ℕ :=
  letI := M.ΛFin
  Finset.univ.sup fun l => pushes (M.m l)

private theorem step_bound (M : FinTM2) (x y : M.Cfg) (j : M.K) (h : M.step x = some y) :
    (y.stk j).length ≤ (x.stk j).length + growth M := by
  let _ := M.ΛFin
  rcases x with ⟨_ | l, v, S⟩
  · contradiction
  · change some (TM2.stepAux (M.m l) v S) = some y at h
    cases h
    exact (stepAux_bound (M.m l) v S j).trans
      (Nat.add_le_add_left (Finset.le_sup (f := fun l => pushes (M.m l)) (Finset.mem_univ l)) _)

private def stackLength (M : FinTM2) (j : M.K) : Option M.Cfg → ℕ
  | none => 0
  | some c => (c.stk j).length

private theorem iterate_bound (M : FinTM2) (j : M.K) (x : Option M.Cfg) (t : ℕ) :
    stackLength M j ((flip bind M.step)^[t] x) ≤ stackLength M j x + t * growth M := by
  induction t generalizing x with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply, Nat.succ_mul]
    have hs : stackLength M j ((flip bind M.step) x) ≤ stackLength M j x + growth M := by
      cases x with
      | none => exact Nat.zero_le _
      | some c =>
        change stackLength M j (M.step c) ≤ _
        cases he : M.step c with
        | none => exact Nat.zero_le _
        | some c' => exact step_bound M c c' j he
    have h := ih ((flip bind M.step) x)
    omega

/-- A machine can grow any designated output by only a constant number of cells per step. -/
theorem output_length_le (M : FinTM2) : ∃ c : ℕ,
    ∀ (input : List (M.Γ M.k₀)) (output : List (M.Γ M.k₁)) (t : ℕ),
      TM2OutputsInTime M input (some output) t → output.length ≤ input.length + t * c := by
  refine ⟨growth M, ?_⟩
  intro input output t h
  have hbound := iterate_bound M M.k₁ (some (initList M input)) h.steps
  rw [h.evals_in_steps] at hbound
  have hin (k : M.K) : ((initList M input).stk k).length ≤ input.length := by
    by_cases he : k = M.k₀
    · subst k
      simp [initList]
    · simp [initList, he]
  change ((haltList M output).stk M.k₁).length ≤ _ at hbound
  simpa [haltList] using hbound.trans (Nat.add_le_add (hin M.k₁) (Nat.mul_le_mul_right _ h.steps_le_m))

/-- A polynomial-time computation has polynomially bounded encoded outputs. -/
theorem polytime_output_bound {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {f : α → β} (hf : IsPolyTime f) : ∃ p : Polynomial ℕ,
    ∀ a, (bitEncode (f a)).length ≤ p.eval (bitEncode a).length := by
  obtain ⟨D⟩ := hf
  obtain ⟨c, hc⟩ := output_length_le D.tm
  refine ⟨Polynomial.X + D.time * Polynomial.C c, ?_⟩
  intro a
  have h := hc _ _ _ (D.outputsFun a)
  simpa [bitEncode] using h

end FactorMachineBound

/- Clocked finite-stack callers with word-valued subroutines on canonical bitstring encodings.
A call moves the input and result through a temporary stack to preserve their bit order. -/

namespace FactorWordOracle

open FactorOracleMachine Turing FactorMachineLift StateTransition

variable (C : OracleProgram)

/-- An atomic call can be used only with a validly encoded argument. -/
inductive Run {A B : Type} (encode : A → List Bool) (encodeOut : B → List Bool) (query : A → B) (cost : ℕ → ℕ) :
    C.Cfg → C.Cfg → ℕ → Prop
  | refl (c) : Run encode encodeOut query cost c c 0
  | normal {c d} (hc : c.l ≠ some C.call) (hs : TM2.step C.m c = some d) : Run encode encodeOut query cost c d 1
  | oracle (x : A) (v : C.σ) (s : C.K → List Bool) (h : s C.arg = encode x) :
      Run encode encodeOut query cost ⟨some C.call, v, s⟩
        ⟨some C.resume, v, Function.update s C.arg (encodeOut (query x))⟩
        (cost (encode x).length)
  | trans {a b c t u} : Run encode encodeOut query cost a b t → Run encode encodeOut query cost b c u →
      Run encode encodeOut query cost a c (t + u)
  | mono {a b t u} : Run encode encodeOut query cost a b t → t ≤ u → Run encode encodeOut query cost a b u

inductive Phase | reverse | transfer | collect | deliver deriving DecidableEq
instance : Fintype Phase := ⟨{.reverse, .transfer, .collect, .deliver}, by intro p; cases p <;> simp⟩

variable (Q : FinTM2) (ei : Q.Γ Q.k₀ ≃ Bool) (eo : Q.Γ Q.k₁ ≃ Bool)

abbrev Label := C.Λ ⊕ (Q.Λ ⊕ Phase)
abbrev HostCfg := TM2.Cfg (C.Alphabet Q) (Label C Q) (C.Register Q)

def caller : Lift (fun _ : C.K => Bool) (C.Alphabet Q) C.Λ (Label C Q) C.σ (C.Register Q) where
  stack := ⟨Sum.inl, Sum.inl_injective⟩
  symbol _ := Equiv.refl _
  label := Sum.inl
  exitLabel := none
  read := Prod.fst
  write w v := (v, w.2)
  read_write _ _ := rfl
  write_write _ _ _ := rfl

def callee : Lift Q.Γ (C.Alphabet Q) Q.Λ (Label C Q) Q.σ (C.Register Q) where
  stack := ⟨fun k => .inr (.inl k), fun _ _ h => Sum.inl.inj (Sum.inr.inj h)⟩
  symbol _ := Equiv.refl _
  label l := .inr (.inl l)
  exitLabel := some (.inr (.inr .collect))
  read v := v.2.1
  write w v := (w.1, v, w.2.2)
  read_write _ _ := rfl
  write_write _ _ _ := rfl

def program : Label C Q → TM2.Stmt (C.Alphabet Q) (Label C Q) (C.Register Q)
  | .inl l => if l = C.call then .goto (fun _ => .inr (.inr .reverse)) else (caller C Q).stmt (C.m l)
  | .inr (.inl l) => (callee C Q).stmt (Q.m l)
  | .inr (.inr .reverse) =>
      .pop (.inl C.arg) (fun w o => (w.1, w.2.1, o))
        (.branch (fun w => w.2.2.isSome)
          (.push (.inr (.inr ())) (fun w => w.2.2.getD false) (.goto fun _ => .inr (.inr .reverse)))
          (.goto fun _ => .inr (.inr .transfer)))
  | .inr (.inr .transfer) =>
      .pop (.inr (.inr ())) (fun w o => (w.1, w.2.1, o))
        (.branch (fun w => w.2.2.isSome)
          (.push (.inr (.inl Q.k₀)) (fun w => ei.symm (w.2.2.getD false)) (.goto fun _ => .inr (.inr .transfer)))
          (.goto fun _ => .inr (.inl Q.main)))
  | .inr (.inr .collect) =>
      .pop (.inr (.inl Q.k₁)) (fun w o => (w.1, w.2.1, o.map eo))
        (.branch (fun w => w.2.2.isSome)
          (.push (.inr (.inr ())) (fun w => w.2.2.getD false) (.goto fun _ => .inr (.inr .collect)))
          (.goto fun _ => .inr (.inr .deliver)))
  | .inr (.inr .deliver) =>
      .pop (.inr (.inr ())) (fun w o => (w.1, w.2.1, o))
        (.branch (fun w => w.2.2.isSome)
          (.push (.inl C.arg) (fun w => w.2.2.getD false) (.goto fun _ => .inr (.inr .deliver)))
          (.goto fun _ => .inl C.resume))

def compiled : FinTM2 :=
  letI := Q.kFin
  letI := Q.ΛFin
  letI := Q.σFin
  { K := C.Index Q
    Γ := C.Alphabet Q
    Λ := Label C Q
    σ := C.Register Q
    k₀ := .inl C.k₀
    k₁ := .inl C.k₁
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    main := .inl C.main
    initialState := (C.initialState, Q.initialState, none)
    m := program C Q ei eo }

def embed (c : C.Cfg) : HostCfg C Q :=
  ⟨c.l.map Sum.inl, (c.var, Q.initialState, none), C.tapes Q c.stk (fun _ => []) []⟩

private abbrev Stores := ∀ k, List (Q.Γ k)

private def oneStack {K : Type} [DecidableEq K] (Γ : K → Type) (k : K) (xs : List (Γ k)) :
    ∀ j, List (Γ j) := Function.update (fun j => ([] : List (Γ j))) k xs

private def stage (l : Label C Q) (v : C.σ) (o : Option Bool) (s : C.K → List Bool)
    (t : Stores Q) (b : List Bool) : HostCfg C Q :=
  ⟨some l, (v, Q.initialState, o), C.tapes Q s t b⟩

private def Exact (a b : HostCfg C Q) (t : ℕ) : Prop :=
  (flip bind (TM2.step (program C Q ei eo)))^[t] (some a) = some b

private theorem next {a b d t} (ab : TM2.step (program C Q ei eo) a = some b)
    (bd : Exact C Q ei eo b d t) : Exact C Q ei eo a d (t+1) := by
  unfold Exact at *
  rw [Function.iterate_succ_apply]
  change (flip bind (TM2.step (program C Q ei eo)))^[t] (TM2.step (program C Q ei eo) a) = some d
  rwa [ab]

private theorem one {a b} (ab : TM2.step (program C Q ei eo) a = some b) : Exact C Q ei eo a b 1 := ab

private theorem join {a b d t u} (ab : Exact C Q ei eo a b t) (bd : Exact C Q ei eo b d u) :
    Exact C Q ei eo a d (u+t) := by
  unfold Exact at *
  rw [Function.iterate_add_apply, ab, bd]

private theorem reverse_run (v : C.σ) (s : C.K → List Bool) (xs bs : List Bool) (o : Option Bool) :
    Exact C Q ei eo
      (stage C Q (.inr (.inr .reverse)) v o (Function.update s C.arg xs) (fun _ => []) bs)
      (stage C Q (.inr (.inr .transfer)) v none (Function.update s C.arg []) (fun _ => []) (xs.reverse ++ bs))
      (xs.length+1) := by
  induction xs generalizing bs o with
  | nil => apply one C; simp [stage, program, TM2.stepAux]
  | cons a xs ih =>
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using
      (next C Q ei eo (a := stage C Q (.inr (.inr .reverse)) v o (Function.update s C.arg (a::xs)) (fun _ => []) bs)
        (by simp [stage, program, TM2.stepAux]) (ih (a::bs) (some a)))

private theorem transfer_run (v : C.σ) (s : C.K → List Bool) (bs : List Bool)
    (xs : List (Q.Γ Q.k₀)) (o : Option Bool) :
    Exact C Q ei eo
      (stage C Q (.inr (.inr .transfer)) v o s (oneStack Q.Γ Q.k₀ xs) bs)
      (stage C Q (.inr (.inl Q.main)) v none s (oneStack Q.Γ Q.k₀ (bs.reverse.map ei.symm ++ xs)) [])
      (bs.length+1) := by
  induction bs generalizing xs o with
  | nil => apply one C; simp [stage, program, TM2.stepAux]
  | cons a bs ih =>
    simpa only [List.length_cons, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append] using
      (next C Q ei eo (a := stage C Q (.inr (.inr .transfer)) v o s (oneStack Q.Γ Q.k₀ xs) (a::bs))
        (by simp [stage, program, TM2.stepAux, oneStack]) (ih (ei.symm a::xs) (some a)))

private theorem caller_match (c : C.Cfg) : (caller C Q).Matches
    (C.initialState, Q.initialState, none) (fun _ => []) c (embed C Q c) := by
  refine ⟨?_, rfl, ⟨?_, ?_⟩⟩
  · change c.l.map Sum.inl = (caller C Q).mapLabel c.l
    cases c.l <;> rfl
  · intro k
    change c.stk k = (c.stk k).map id
    simp
  · rintro (k | k | u) h
    · exact False.elim (h k rfl)
    · rfl
    · cases u; rfl

private theorem ordinary_run {c d : C.Cfg} (hc : c.l ≠ some C.call) (hs : TM2.step C.m c = some d) :
    Exact C Q ei eo (embed C Q c) (embed C Q d) 1 := by
  rcases c with ⟨_ | l, v, s⟩
  · contradiction
  · have hl : l ≠ C.call := fun h => hc (congrArg some h)
    have hd : TM2.stepAux (C.m l) v s = d := Option.some.inj hs
    subst d
    have hmatch := (caller C Q).stepAux_stmt (C.m l) (C.initialState, Q.initialState, none)
      (fun _ => []) v s (C.tapes Q s (fun _ => []) []) (caller_match C Q ⟨some l, v, s⟩).stack_eq
    apply one C
    change some (TM2.stepAux (program C Q ei eo (.inl l)) _ _) = _
    rw [show program C Q ei eo (.inl l) = (caller C Q).stmt (C.m l) by simp [program, hl]]
    exact congrArg some (hmatch.unique _ (caller_match C Q _))

private def embedQuery (v : C.σ) (s : C.K → List Bool) (d : Q.Cfg) : HostCfg C Q :=
  ⟨(callee C Q).mapLabel d.l, (v, d.var, none), C.tapes Q s d.stk []⟩

private theorem callee_match (v : C.σ) (s : C.K → List Bool) (d : Q.Cfg) :
    (callee C Q).Matches (v, Q.initialState, none) (C.tapes Q s (fun _ => []) []) d (embedQuery C Q v s d) := by
  refine ⟨rfl, rfl, ⟨?_, ?_⟩⟩
  · intro k
    change d.stk k = (d.stk k).map id
    simp
  · rintro (k | k | u) h
    · rfl
    · exact False.elim (h k rfl)
    · cases u; rfl

private theorem init_tapes (T : FinTM2) (xs : List (T.Γ T.k₀)) :
    (initList T xs).stk = oneStack T.Γ T.k₀ xs := by
  funext j
  by_cases h : j = T.k₀
  · subst j; simp [initList, oneStack, Function.update]
  · simp [initList, oneStack, Function.update, h]

private theorem halt_tapes (T : FinTM2) (xs : List (T.Γ T.k₁)) :
    (haltList T xs).stk = oneStack T.Γ T.k₁ xs := by
  funext j
  by_cases h : j = T.k₁
  · subst j; simp [haltList, oneStack, Function.update]
  · simp [haltList, oneStack, Function.update, h]

private theorem nil_stack {K : Type} [DecidableEq K] (Γ : K → Type) (k : K) :
    oneStack Γ k [] = (fun _ => []) := by
  funext j
  by_cases h : j = k
  · subst j; simp [oneStack]
  · simp [oneStack, h]

private theorem start_call (v : C.σ) (s : C.K → List Bool) (w : List Bool) (harg : s C.arg = w) :
    Exact C Q ei eo (embed C Q ⟨some C.call, v, s⟩)
      (embedQuery C Q v (Function.update s C.arg []) (initList Q (w.map ei.symm))) (2 * w.length + 3) := by
  have hrev := reverse_run C Q ei eo v s w [] none
  have htrans := transfer_run C Q ei eo v (Function.update s C.arg []) w.reverse [] none
  have hstart : Function.update s C.arg w = s := by rw [← harg]; exact Function.update_eq_self _ _
  rw [hstart, List.append_nil] at hrev
  rw [List.reverse_reverse, List.append_nil, nil_stack, List.length_reverse] at htrans
  have henter := one C Q ei eo (a := embed C Q ⟨some C.call, v, s⟩)
    (b := stage C Q (.inr (.inr .reverse)) v none s (fun _ => []) []) (by simp [embed, stage, program, TM2.stepAux])
  have hs := join C Q ei eo (join C Q ei eo henter hrev) htrans
  convert hs using 1
  · unfold embedQuery stage
    rw [init_tapes]
    rfl
  · omega

private theorem collect_run (v : C.σ) (s : C.K → List Bool) (xs bs : List Bool) (o : Option Bool) :
    Exact C Q ei eo
      (stage C Q (.inr (.inr .collect)) v o s (oneStack Q.Γ Q.k₁ (xs.map eo.symm)) bs)
      (stage C Q (.inr (.inr .deliver)) v none s (oneStack Q.Γ Q.k₁ []) (xs.reverse ++ bs))
      (xs.length + 1) := by
  induction xs generalizing bs o with
  | nil => apply one C; simp [stage, program, TM2.stepAux, oneStack]
  | cons a xs ih =>
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using
      (next C Q ei eo (a := stage C Q (.inr (.inr .collect)) v o s (oneStack Q.Γ Q.k₁ ((a::xs).map eo.symm)) bs)
        (by simp [stage, program, TM2.stepAux, oneStack]) (ih (a::bs) (some a)))

private theorem deliver_run (v : C.σ) (s : C.K → List Bool) (bs xs : List Bool) (o : Option Bool) :
    Exact C Q ei eo
      (stage C Q (.inr (.inr .deliver)) v o (Function.update s C.arg xs) (fun _ => []) bs)
      (embed C Q ⟨some C.resume, v, Function.update s C.arg (bs.reverse ++ xs)⟩)
      (bs.length + 1) := by
  induction bs generalizing xs o with
  | nil => apply one C; simp [stage, program, TM2.stepAux, embed]
  | cons a bs ih =>
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using
      (next C Q ei eo (a := stage C Q (.inr (.inr .deliver)) v o (Function.update s C.arg xs) (fun _ => []) (a::bs))
        (by simp [stage, program, TM2.stepAux]) (ih (a::xs) (some a)))

private theorem finish_call (v : C.σ) (s : C.K → List Bool) (r : List Bool) :
    Exact C Q ei eo
      (embedQuery C Q v (Function.update s C.arg []) (haltList Q (r.map eo.symm)))
      (embed C Q ⟨some C.resume, v, Function.update s C.arg r⟩) (2*r.length + 2) := by
  have hcollect := collect_run C Q ei eo v (Function.update s C.arg []) r [] none
  have hdeliver := deliver_run C Q ei eo v s r.reverse [] none
  rw [List.append_nil, nil_stack] at hcollect
  rw [List.reverse_reverse, List.append_nil, List.length_reverse] at hdeliver
  have h := join C Q ei eo hcollect hdeliver
  convert h using 1
  · unfold embedQuery stage
    rw [halt_tapes]
    rfl
  · omega

private theorem call_run (v : C.σ) (s : C.K → List Bool) (w : List Bool) (r : List Bool) (t : ℕ)
    (harg : s C.arg = w) (oracleRun : TM2OutputsInTime Q (w.map ei.symm) (some (r.map eo.symm)) t) :
    ∃ k ≤ t + 2*w.length + 2*r.length + 5, Exact C Q ei eo (embed C Q ⟨some C.call, v, s⟩)
      (embed C Q ⟨some C.resume, v, Function.update s C.arg r⟩) k := by
  let cleared := Function.update s C.arg []
  let middle := (callee C Q).evalsToInTime (p := Q.m) (P := program C Q ei eo) (fun _ => rfl)
    (callee_match C Q v cleared (initList Q (w.map ei.symm)))
    (callee_match C Q v cleared (haltList Q (r.map eo.symm))) oracleRun
  have hmiddle : Exact C Q ei eo (embedQuery C Q v cleared (initList Q (w.map ei.symm)))
      (embedQuery C Q v cleared (haltList Q (r.map eo.symm))) middle.steps := middle.evals_in_steps
  have h := join C Q ei eo (join C Q ei eo (start_call C Q ei eo v s w harg) hmiddle) (finish_call C Q ei eo v s r)
  exact ⟨_, by have := middle.steps_le_m; omega, h⟩

private theorem simulate {A B : Type} {encode : A → List Bool} {encodeOut : B → List Bool} {query : A → B} {cost time : ℕ → ℕ}
    (oracleRun : ∀ x, TM2OutputsInTime Q ((encode x).map ei.symm) (some ((encodeOut (query x)).map eo.symm)) (time (encode x).length))
    (hcost : ∀ x, time (encode x).length + 2 * (encode x).length + 2 * (encodeOut (query x)).length + 5 ≤ cost (encode x).length)
    {a b : C.Cfg} {t : ℕ} (run : Run C encode encodeOut query cost a b t) :
    ∃ k ≤ t, Exact C Q ei eo (embed C Q a) (embed C Q b) k := by
  induction run with
  | refl a => exact ⟨0, Nat.le_refl _, rfl⟩
  | normal hc hs => exact ⟨1, Nat.le_refl _, ordinary_run C Q ei eo hc hs⟩
  | oracle x v s h =>
    obtain ⟨k, hk, steps⟩ := call_run C Q ei eo v s _ _ _ h (oracleRun x)
    exact ⟨k, hk.trans (hcost x), steps⟩
  | trans _ _ ih ih' =>
    obtain ⟨k, hk, h⟩ := ih
    obtain ⟨j, hj, h'⟩ := ih'
    exact ⟨j+k, by omega, join C Q ei eo h h'⟩
  | mono _ hle ih =>
    obtain ⟨k, hk, h⟩ := ih
    exact ⟨k, hk.trans hle, h⟩

private theorem singleCaller (k : C.K) (xs : List Bool) :
    C.tapes Q (oneStack (fun _ : C.K => Bool) k xs) (fun _ => []) [] =
      oneStack (C.Alphabet Q) (.inl k) xs := by
  have empty : C.tapes Q (fun _ => []) (fun _ => []) [] = (fun _ => []) := by
    funext j
    rcases j with i | i | u <;> rfl
  unfold oneStack
  have hu := show Function.update (C.tapes Q (fun _ => []) (fun _ => []) []) (.inl k) xs =
      C.tapes Q (Function.update (fun _ => []) k xs) (fun _ => []) [] by simp
  simpa only [empty] using hu.symm

private theorem embed_init (xs : List Bool) : embed C Q (initList C.tm xs) =
    initList (compiled C Q ei eo) xs := by
  apply congrArg (fun s => (⟨some (.inl C.main), (C.initialState, Q.initialState, none), s⟩ : HostCfg C Q))
  change C.tapes Q (initList C.tm xs).stk (fun _ => []) [] = (initList (compiled C Q ei eo) xs).stk
  exact (congrArg (fun s => C.tapes Q s (fun _ => []) []) (init_tapes C.tm xs)).trans
    ((singleCaller C Q C.k₀ xs).trans (init_tapes (compiled C Q ei eo) xs).symm)

private theorem embed_halt (xs : List Bool) : embed C Q (haltList C.tm xs) =
    haltList (compiled C Q ei eo) xs := by
  apply congrArg (fun s => (⟨none, (C.initialState, Q.initialState, none), s⟩ : HostCfg C Q))
  change C.tapes Q (haltList C.tm xs).stk (fun _ => []) [] = (haltList (compiled C Q ei eo) xs).stk
  exact (congrArg (fun s => C.tapes Q s (fun _ => []) []) (halt_tapes C.tm xs)).trans
    ((singleCaller C Q C.k₁ xs).trans (halt_tapes (compiled C Q ei eo) xs).symm)

/-- Any valid time-budgeted oracle program executes on a standard finite TM2 machine.
The caller's workspace survives every call and all callee workspace is cleared before resuming. -/
theorem compile_run {A B : Type} {encode : A → List Bool} {encodeOut : B → List Bool} {query : A → B} {cost time : ℕ → ℕ}
    (oracleRun : ∀ x, TM2OutputsInTime Q ((encode x).map ei.symm) (some ((encodeOut (query x)).map eo.symm)) (time (encode x).length))
    (hcost : ∀ x, time (encode x).length + 2 * (encode x).length + 2 * (encodeOut (query x)).length + 5 ≤ cost (encode x).length)
    {input output : List Bool} {t : ℕ}
    (run : Run C encode encodeOut query cost (initList C.tm input) (haltList C.tm output) t) :
    Nonempty (TM2OutputsInTime (compiled C Q ei eo) input (some output) t) := by
  obtain ⟨k, hk, h⟩ := simulate C Q ei eo oracleRun hcost run
  unfold Exact at h
  rw [embed_init C Q ei eo, embed_halt C Q ei eo] at h
  exact ⟨⟨⟨k, h⟩, hk⟩⟩

open ComplexityTheory BitstringEncoding

/-- A polynomial-time word-valued oracle can be substituted into any caller that runs
in polynomial time for every polynomial charge on the bit length of each query.
The charge used by the compiler also pays for copying the full result. -/
theorem polytime_from_runs {A B X Y : Type} [BitstringEncoding A] [BitstringEncoding B]
    [BitstringEncoding X] [BitstringEncoding Y] (C : OracleProgram) (q : A → B) (f : X → Y)
    (hq : IsPolyTime q)
    (runs : ∀ charge : Polynomial ℕ, ∃ total : Polynomial ℕ, ∀ x,
      Run C bitEncode bitEncode q charge.eval (initList C.tm (bitEncode x))
        (haltList C.tm (bitEncode (f x))) (total.eval (bitEncode x).length)) : IsPolyTime f := by
  obtain ⟨outputBound, hsize⟩ := FactorMachineBound.polytime_output_bound hq
  obtain ⟨Q⟩ := hq
  let charge : Polynomial ℕ := Q.time + 2 * Polynomial.X + 2 * outputBound + 5
  have budget (x : A) : Q.time.eval (bitEncode x).length + 2 * (bitEncode x).length +
      2 * (bitEncode (q x)).length + 5 ≤ charge.eval (bitEncode x).length := by
    have h := hsize x
    simp [charge]
    omega
  obtain ⟨total, run⟩ := runs charge
  refine ⟨{ tm := compiled C Q.tm Q.inputAlphabet Q.outputAlphabet
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := total
            outputsFun := fun x => ?_ }⟩
  let out := Classical.choice (compile_run C Q.tm Q.inputAlphabet Q.outputAlphabet
    (encode := bitEncode) (encodeOut := bitEncode) (query := q) (time := Q.time.eval)
    Q.outputsFun budget (run x))
  change TM2OutputsInTime (compiled C Q.tm Q.inputAlphabet Q.outputAlphabet) ((bitEncode x).map id)
    (some ((bitEncode (f x)).map id)) (total.eval (bitEncode x).length)
  erw [List.map_id, List.map_id]
  exact out

end FactorWordOracle

/-
# Finite control for emitting factors

The input is saved on the numerator stack. Each remaining fuel marker permits
one divisor call and one division. Before dividing, the controller appends the
self-delimited divisor to a reversed output accumulator. At the end it reverses
the accumulator onto the output stack and clears all working stacks.
-/

namespace FactorEmitController

open Turing.TM2 BitstringEncoding

inductive Stack
  | io | num | den | fuel | acc | tmp
  deriving DecidableEq

inductive Label
  | start | setNum | dropFuel | round | check | cloneNum | restoreNum | ask
  | resume | restoreDen | divCall | drainNum | drainFuel | emit
  deriving DecidableEq

instance : Fintype Stack := Fintype.ofList [.io, .num, .den, .fuel, .acc, .tmp]
  (by intro k; cases k <;> decide)

instance : Fintype Label := Fintype.ofList
  [.start, .setNum, .dropFuel, .round, .check, .cloneNum, .restoreNum, .ask,
   .resume, .restoreDen, .divCall, .drainNum, .drainFuel, .emit]
  (by intro k; cases k <;> decide)

abbrev Code := Stmt (fun _ : Stack => Bool) Label (Option Bool)
abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)

private def jump (l : Label) : Code := .load (fun _ => none) (.goto (fun _ => l))
private def stop : Code := .load (fun _ => none) .halt
private def putBit (k : Stack) (b : Bool) (q : Code) : Code := .push k (fun _ => b) q
private def putRead (k : Stack) (q : Code) : Code := .push k (fun s => s.getD false) q
private def take (k : Stack) (item empty : Code) : Code :=
  .pop k (fun _ b => b) (.branch Option.isSome item empty)
private def look (k : Stack) (item empty : Code) : Code :=
  .peek k (fun _ b => b) (.branch Option.isSome item empty)

/-- The two call labels are filled by the enclosing machine. -/
def program : Label → Code
  | .start => take .io (putRead .tmp (putBit .fuel true (jump .start))) (jump .setNum)
  | .setNum => take .tmp (putRead .num (jump .setNum)) (jump .dropFuel)
  | .dropFuel => .pop .fuel (fun _ _ => none) (jump .round)
  | .round => take .fuel (jump .check) (jump .drainNum)
  | .check => take .num
      (putRead .tmp (look .num (jump .cloneNum) (.pop .tmp (fun _ _ => none) (jump .drainFuel))))
      (jump .drainFuel)
  | .cloneNum => take .num (putRead .tmp (jump .cloneNum)) (jump .restoreNum)
  | .restoreNum => take .tmp (putRead .io (putRead .num (jump .restoreNum))) (jump .ask)
  | .ask => .halt
  | .resume => take .io (putRead .tmp (putBit .acc true (putRead .acc (jump .resume))))
      (putBit .acc false (jump .restoreDen))
  | .restoreDen => take .tmp (putRead .den (jump .restoreDen)) (jump .divCall)
  | .divCall => .halt
  | .drainNum => take .num (jump .drainNum) (jump .drainFuel)
  | .drainFuel => take .fuel (jump .drainFuel) (jump .emit)
  | .emit => take .acc (putRead .io (jump .emit)) stop

def words (io num den fuel acc tmp : List Bool) : Stack → List Bool
  | .io => io
  | .num => num
  | .den => den
  | .fuel => fuel
  | .acc => acc
  | .tmp => tmp

def cfg (l : Option Label) (io num den fuel acc tmp : List Bool) : Config :=
  ⟨l, none, words io num den fuel acc tmp⟩

abbrev atL (l : Label) := cfg (some l)

/-- Each path consists exclusively of controller transitions between calls. -/
inductive Work : Config → Config → ℕ → Prop
  | refl (c) : Work c c 0
  | one {c d} : c.l ≠ some .ask → c.l ≠ some .divCall → step program c = some d → Work c d 1
  | trans {a b c t u} : Work a b t → Work b c u → Work a c (t + u)

private theorem workStep {l io n d f a t z}
    (hn₁ : l ≠ Label.ask) (hn₂ : l ≠ Label.divCall)
    (hl : (stepAux (program l) none (words io n d f a t)).l = z.l)
    (hv : (stepAux (program l) none (words io n d f a t)).var = z.var)
    (hio : (stepAux (program l) none (words io n d f a t)).stk .io = z.stk .io)
    (hn : (stepAux (program l) none (words io n d f a t)).stk .num = z.stk .num)
    (hd : (stepAux (program l) none (words io n d f a t)).stk .den = z.stk .den)
    (hf : (stepAux (program l) none (words io n d f a t)).stk .fuel = z.stk .fuel)
    (ha : (stepAux (program l) none (words io n d f a t)).stk .acc = z.stk .acc)
    (ht : (stepAux (program l) none (words io n d f a t)).stk .tmp = z.stk .tmp) :
    Work (atL l io n d f a t) z 1 := by
  apply Work.one (fun h => hn₁ (Option.some.inj h)) (fun h => hn₂ (Option.some.inj h))
  apply congrArg some
  change stepAux _ _ _ = z
  have hs : (stepAux (program l) none (words io n d f a t)).stk = z.stk := by
    funext k
    cases k <;> assumption
  cases eqn : stepAux (program l) none (words io n d f a t) with
  | mk L V S =>
    rw [eqn] at hl hv hs
    cases z
    congr

private theorem consume (stage : List Bool → List Bool → Config) (finish : List Bool → Config)
    (next : ∀ b xs acc, Work (stage (b :: xs) acc) (stage xs (b :: acc)) 1)
    (done_ : ∀ acc, Work (stage [] acc) (finish acc) 1)
    (xs acc : List Bool) : Work (stage xs acc) (finish (xs.reverse ++ acc)) (xs.length + 1) := by
  induction xs generalizing acc with
  | nil => simpa using done_ acc
  | cons b xs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm 1 (xs.length + 1)] using
      (next b xs acc).trans (ih (b :: acc))

/-- Store the original input and leave one fuel bit per input bit after the first. -/
theorem startup (x : List Bool) :
    Work (atL .start x [] [] [] [] [])
      (atL .round [] x [] (List.replicate (x.length - 1) true) [] []) (2 * x.length + 3) := by
  have scan := consume (fun xs seen => atL .start xs [] [] (List.replicate seen.length true) [] seen)
    (fun seen => atL .setNum [] [] [] (List.replicate seen.length true) [] seen)
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) x []
  have restore := consume
    (fun xs acc => atL .setNum [] acc [] (List.replicate x.length true) [] xs)
    (fun acc => atL .dropFuel [] acc [] (List.replicate x.length true) [] [])
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) x.reverse []
  have drop : Work (atL .dropFuel [] x [] (List.replicate x.length true) [] [])
      (atL .round [] x [] (List.replicate (x.length - 1) true) [] []) 1 := by
    cases x <;> apply workStep <;> first | rfl | decide
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at scan restore
  convert (scan.trans restore).trans drop using 1
  · rfl
  · omega

/-- Clone a numerator of at least two bits to the input stack for the divisor call. -/
theorem prepareRound (x fuel acc : List Bool) (v : Bool) (hx : 2 ≤ x.length) :
    Work (atL .round [] x [] (v :: fuel) acc [])
      (atL .ask x x [] fuel acc []) (2 * x.length + 3) := by
  rcases x with _ | ⟨b, xs⟩
  · simp at hx
  rcases xs with _ | ⟨c, rest⟩
  · simp at hx
  have enter : Work (atL .round [] (b :: c :: rest) [] (v :: fuel) acc [])
      (atL .check [] (b :: c :: rest) [] fuel acc []) 1 := by
    apply workStep <;> first | rfl | decide
  have check : Work (atL .check [] (b :: c :: rest) [] fuel acc [])
      (atL .cloneNum [] (c :: rest) [] fuel acc [b]) 1 := by
    apply workStep <;> first | rfl | decide
  have clone := consume (fun xs seen => atL .cloneNum [] xs [] fuel acc seen)
    (fun seen => atL .restoreNum [] [] [] fuel acc seen)
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) (c :: rest) [b]
  have restore := consume (fun xs seen => atL .restoreNum seen seen [] fuel acc xs)
    (fun seen => atL .ask seen seen [] fuel acc [])
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) (b :: c :: rest).reverse []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at restore
  rw [← List.reverse_cons] at clone
  convert ((enter.trans check).trans clone).trans restore using 1
  simp
  omega

private def payloadRev (word : List Bool) : List Bool := word.flatMap fun b => [b, true]

private theorem reverse_delimit (word : List Bool) :
    (delimit word).reverse = false :: payloadRev word.reverse := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    simp [delimit, List.reverse_cons, ih, payloadRev, List.append_assoc]

/-- Emit the self-delimited divisor, restore it on the denominator stack, and call division. -/
theorem resumeRound (d x fuel acc : List Bool) :
    Work (atL .resume d x [] fuel acc [])
      (atL .divCall [] x d fuel ((delimit d).reverse ++ acc) []) (2 * d.length + 2) := by
  have scan := consume
    (fun xs seen => atL .resume xs x [] fuel (payloadRev seen ++ acc) seen)
    (fun seen => atL .restoreDen [] x [] fuel (false :: (payloadRev seen ++ acc)) seen)
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) d []
  have restore := consume
    (fun xs seen => atL .restoreDen [] x seen fuel ((delimit d).reverse ++ acc) xs)
    (fun seen => atL .divCall [] x seen fuel ((delimit d).reverse ++ acc) [])
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) d.reverse []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at scan restore
  rw [reverse_delimit] at restore ⊢
  convert scan.trans restore using 1
  · rfl
  · omega

private theorem teardown (fuel acc : List Bool) :
    Work (atL .drainFuel [] [] [] fuel acc []) (cfg none acc.reverse [] [] [] [] [])
      (fuel.length + acc.length + 2) := by
  have drain := consume (fun xs _ => atL .drainFuel [] [] [] xs acc [])
    (fun _ => atL .emit [] [] [] [] acc [])
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) fuel []
  have emit := consume (fun xs seen => atL .emit seen [] [] [] xs [])
    (fun seen => cfg none seen [] [] [] [] [])
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) acc []
  simp only [List.append_nil] at emit
  convert drain.trans emit using 1
  omega

/-- When fuel is exhausted, erase the numerator and return the accumulated output. -/
theorem finish_empty (x acc : List Bool) :
    Work (atL .round [] x [] [] acc []) (cfg none acc.reverse [] [] [] [] [])
      (x.length + acc.length + 4) := by
  have enter : Work (atL .round [] x [] [] acc []) (atL .drainNum [] x [] [] acc []) 1 := by
    apply workStep <;> first | rfl | decide
  have drain := consume (fun xs _ => atL .drainNum [] xs [] [] acc [])
    (fun _ => atL .drainFuel [] [] [] [] acc [])
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) x []
  convert (enter.trans drain).trans (teardown [] acc) using 1
  simp
  omega

/-- A numerator with fewer than two bits ends the loop, even with fuel left. -/
theorem finish_small (x fuel acc : List Bool) (v : Bool) (hx : x.length < 2) :
    Work (atL .round [] x [] (v :: fuel) acc []) (cfg none acc.reverse [] [] [] [] [])
      (fuel.length + acc.length + 4) := by
  have enter : Work (atL .round [] x [] (v :: fuel) acc []) (atL .check [] x [] fuel acc []) 1 := by
    apply workStep <;> first | rfl | decide
  have check : Work (atL .check [] x [] fuel acc []) (atL .drainFuel [] [] [] fuel acc []) 1 := by
    rcases x with _ | ⟨b, xs⟩
    · apply workStep <;> first | rfl | decide
    rcases xs with _ | ⟨c, rest⟩
    · apply workStep <;> first | rfl | decide
    · simp only [List.length_cons] at hx
      omega
  convert (enter.trans check).trans (teardown fuel acc) using 1
  omega

end FactorEmitController

/-
# Length of the encoded prime factor list

The integer-factorization conjecture encodes each prime in binary, writing two
bits per payload bit and one delimiter per factor. The total length is at most
five times the floor of the binary logarithm of the input. Powers of two attain
the bound.
-/

namespace FactorEncoding

open BitstringEncoding

private theorem length_encodePosNum (p : PosNum) :
    (Computability.encodePosNum p).length = p.natSize := by
  induction p <;> simp_all [Computability.encodePosNum, PosNum.natSize]

/-- The canonical encoding uses the usual number of binary digits. -/
theorem length_bitEncode_nat (n : ℕ) : (bitEncode n).length = n.size := by
  have hnum (m : Num) : (Computability.encodeNum m).length = m.natSize := by
    cases m with
    | zero => rfl
    | pos p => exact length_encodePosNum p
  calc
    (bitEncode n).length = (n : Num).natSize := hnum (n : Num)
    _ = n.size := by rw [Num.natSize_to_nat, Num.to_of_nat]

private theorem length_bitEncode_pos {n : ℕ} (hn : n ≠ 0) :
    (bitEncode n).length = n.log2 + 1 := by
  rw [length_bitEncode_nat]
  have hlo : n.log2 < n.size := Nat.lt_size.mpr (Nat.log2_self_le hn)
  have hhi : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
  omega

private theorem length_bitEncode_cons (p : ℕ) (ps : List ℕ) :
    (bitEncode (p :: ps)).length = 2 * (bitEncode p).length + 1 + (bitEncode ps).length := by
  change (delimit (bitEncode p) ++ bitEncode ps).length = _
  rw [List.length_append, length_delimit]

private theorem length_bitEncode_le_log2_prod (ps : List ℕ) (h : ∀ p ∈ ps, 2 ≤ p) :
    (bitEncode ps).length ≤ 5 * ps.prod.log2 := by
  induction ps with
  | nil => decide
  | cons p ps ih =>
    have hp : 2 ≤ p := h p (by simp)
    have ht : ∀ q ∈ ps, 2 ≤ q := fun q hq => h q (by simp [hq])
    have hp0 : p ≠ 0 := by omega
    have ht0 : ps.prod ≠ 0 := by
      apply List.prod_ne_zero
      intro hz
      have := ht 0 hz
      omega
    have hbit : 1 ≤ p.log2 := (Nat.le_log2 hp0).mpr (by simpa using hp)
    have hlog : p.log2 + ps.prod.log2 ≤ (p * ps.prod).log2 := by
      apply (Nat.le_log2 (Nat.mul_ne_zero hp0 ht0)).mpr
      rw [pow_add]
      exact Nat.mul_le_mul (Nat.log2_self_le hp0) (Nat.log2_self_le ht0)
    have htail := ih ht
    rw [length_bitEncode_cons, length_bitEncode_pos hp0, List.prod_cons]
    omega

/-- A sharp upper bound on the length of the actual output in the conjecture. -/
theorem primeFactorsList_length_bound (n : ℕ) :
    (bitEncode n.primeFactorsList).length ≤ 5 * n.log2 := by
  by_cases hn : n = 0
  · subst n
    rw [Nat.primeFactorsList_zero]
    exact Nat.zero_le _
  · have h := length_bitEncode_le_log2_prod n.primeFactorsList
        (fun _ hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
    simpa only [Nat.prod_primeFactorsList hn] using h

/-- Each occurrence of the prime two contributes exactly five bits. -/
theorem primeFactorsList_length_two_pow (k : ℕ) :
    (bitEncode (2 ^ k).primeFactorsList).length = 5 * k := by
  rw [Nat.prime_two.primeFactorsList_pow]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, length_bitEncode_cons, ih]
    have htwo : (bitEncode (2 : ℕ)).length = 2 := by decide
    omega

end FactorEncoding

/-
# Cost of the comparator calls in the factor search

The recursion in the third hypothesis of the integer-factorization reduction
reads one threshold bit at a time. We record the pairs it passes to the
comparator. On an input of length `L`, the total of its comparator clocks is at
most `L * P.eval (3 * L + 1)`, for every clock polynomial `P` over the naturals.
This accounts for the oracle calls. A machine implementing the surrounding
control flow additionally needs to construct its queries and maintain its state.
-/

namespace FactorSearchClock

open BitstringEncoding

/-- The value and ordered oracle calls of a search in the interval
`[low, low + 2^k)`. -/
def run (query : ℕ × ℕ → Bool) (n : ℕ) : (k low : ℕ) → ℕ × List (ℕ × ℕ)
  | 0, low => (low, [])
  | k + 1, low =>
    let pivot := low + 2 ^ k - 1
    let next := if query (n, pivot) then low else low + 2 ^ k
    let rest := run query n k next
    (rest.1, (n, pivot) :: rest.2)

/-- Apply the guard and initial interval from the submitted reduction. -/
def search (query : ℕ × ℕ → Bool) (n : ℕ) : ℕ × List (ℕ × ℕ) :=
  if n < 2 then (2 - n, []) else run query n (n.log2 + 1) 0

private theorem run_value (query : ℕ × ℕ → Bool) (n k low : ℕ) :
    (run query n k low).1 =
      (Nat.rec (motive := fun _ => ℕ → ℕ) id
        (fun i search low =>
          if query (n, low + 2 ^ i - 1) then search low else search (low + 2 ^ i)) k) low := by
  induction k generalizing low with
  | zero => rfl
  | succ k ih =>
    simp only [run]
    split <;> apply ih

/-- Forgetting the trace gives the exact function in the third hypothesis. -/
theorem search_value (query : ℕ × ℕ → Bool) (n : ℕ) :
    (search query n).1 =
      if n < 2 then 2 - n else
        (Nat.rec (motive := fun _ => ℕ → ℕ) id
          (fun i search low =>
            if query (n, low + 2 ^ i - 1) then search low else search (low + 2 ^ i))
          (n.log2 + 1)) 0 := by
  by_cases hn : n < 2 <;> simp [search, hn, run_value]

private theorem run_queries (query : ℕ × ℕ → Bool) (n L k low : ℕ)
    (hi : low + 2 ^ k ≤ 2 ^ L) :
    (run query n k low).2.length = k ∧
    ∀ x ∈ (run query n k low).2, x.1 = n ∧ x.2 < 2 ^ L := by
  induction k generalizing low with
  | zero => simp [run]
  | succ k ih =>
    let next := if query (n, low + 2 ^ k - 1) then low else low + 2 ^ k
    rw [Nat.pow_succ] at hi
    have hp : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have hnext : next + 2 ^ k ≤ 2 ^ L := by
      dsimp [next]
      split <;> omega
    obtain ⟨hc, hb⟩ := ih next hnext
    change ((n, low + 2 ^ k - 1) :: (run query n k next).2).length = k + 1 ∧ _
    constructor
    · simpa only [List.length_cons] using congrArg Nat.succ hc
    · intro x hx
      change x ∈ (n, low + 2 ^ k - 1) :: (run query n k next).2 at hx
      rcases List.mem_cons.mp hx with h | h
      · subst x
        exact ⟨rfl, by dsimp; omega⟩
      · exact hb x h

/-- The canonical binary pair format delimits its first component and appends
the bare encoding of its second component. -/
theorem pair_length (n b : ℕ) :
    (bitEncode (n, b)).length = 2 * n.size + 1 + b.size := by
  change (delimit (bitEncode n) ++ bitEncode b).length = _
  simp only [List.length_append, length_delimit, FactorEncoding.length_bitEncode_nat]

private theorem bit_length_eq_log2_succ {n : ℕ} (hn : n ≠ 0) : n.size = n.log2 + 1 := by
  have hlo := Nat.lt_size.mpr (Nat.log2_self_le hn)
  have hhi : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
  omega

/-- The number of calls and the size of every queried pivot and encoded pair.
Inputs zero and one issue no calls. -/
theorem search_queries (query : ℕ × ℕ → Bool) (n : ℕ) :
    (search query n).2.length = (if n < 2 then 0 else (bitEncode n).length) ∧
      ∀ x ∈ (search query n).2,
        (bitEncode x.2).length ≤ (bitEncode n).length ∧
        (bitEncode x).length ≤ 3 * (bitEncode n).length + 1 := by
  by_cases hn : n < 2
  · simp [search, hn]
  · have hL := bit_length_eq_log2_succ (by omega : n ≠ 0)
    obtain ⟨hl, hq⟩ := run_queries query n (n.log2 + 1) (n.log2 + 1) 0 (by simp)
    simp only [search, if_neg hn, FactorEncoding.length_bitEncode_nat]
    refine ⟨hl.trans hL.symm, ?_⟩
    rintro ⟨n', b⟩ hx
    obtain ⟨heq, hb⟩ := hq _ hx
    change n' = n at heq
    subst n'
    have hbits : b.size ≤ n.size := hL ▸ Nat.size_le.mpr hb
    simpa only [pair_length, FactorEncoding.length_bitEncode_nat] using
      And.intro hbits (by omega : 2 * n.size + 1 + b.size ≤ 3 * n.size + 1)

private theorem eval_monotone (P : Polynomial ℕ) : Monotone P.eval := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    intro a b h
    simpa only [Polynomial.eval_add] using Nat.add_le_add (hp h) (hq h)
  | monomial k c =>
    intro a b h
    simpa only [Polynomial.eval_monomial] using
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left h k)

private theorem sum_map_le (f : α → ℕ) (xs : List α) (C : ℕ)
    (h : ∀ x ∈ xs, f x ≤ C) : (xs.map f).sum ≤ xs.length * C := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simpa only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, Nat.add_comm C]
      using Nat.add_le_add hx ht

/-- The aggregate time budget for the actual comparator calls, with the same
bit encoding as the comparator's polynomial-time Turing machine. -/
theorem search_clock (query : ℕ × ℕ → Bool) (P : Polynomial ℕ) (n : ℕ) :
    (((search query n).2.map (fun x => P.eval (bitEncode x).length)).sum) ≤
      (bitEncode n).length * P.eval (3 * (bitEncode n).length + 1) := by
  obtain ⟨hl, hq⟩ := search_queries query n
  apply (sum_map_le _ _ _ (fun x hx => eval_monotone P (hq x hx).2)).trans
  apply Nat.mul_le_mul_right
  rw [hl]
  split <;> omega

/-- As a polynomial in the input length, the bound is `X * P(3X+1)`. -/
theorem search_clock_polynomial (query : ℕ × ℕ → Bool) (P : Polynomial ℕ) (n : ℕ) :
    (((search query n).2.map (fun x => P.eval (bitEncode x).length)).sum) ≤
      (Polynomial.X * P.comp (3 * Polynomial.X + 1)).eval (bitEncode n).length := by
  simpa using search_clock query P n

/-- Each transition count comes from the comparator machine's certified evaluation
on the actual pair sent to it. The clock bound therefore applies to the sum of
these transition counts. -/
theorem comparator_steps {query : ℕ × ℕ → Bool}
    (machine : Turing.TM2ComputableInPolyTime bitEncode bitEncode query) (n : ℕ) :
    (((search query n).2.map (fun x => (machine.outputsFun x).steps)).sum) ≤
      (Polynomial.X * machine.time.comp (3 * Polynomial.X + 1)).eval (bitEncode n).length := by
  apply le_trans _ (search_clock_polynomial query machine.time n)
  exact List.sum_le_sum fun x _ => (machine.outputsFun x).steps_le_m

end FactorSearchClock

/-
# Building factor-search queries from bits

All words use the little-endian natural-number encoding in the factorization
conjecture. The search retains the already chosen high bits as a canonical
word. The remaining input bits serve as a counter, one bit per comparison.
-/

namespace FactorSearchBits

open Computability BitstringEncoding

/-- Extend the high prefix by a less significant digit, retaining the empty word
for zero. -/
def digit : Bool → List Bool → List Bool
  | false, [] => []
  | b, high => b :: high

/-- Each remaining bit supplies a low one in the last candidate of the lower
half. The zero immediately above these ones is significant when `high` is nonempty. -/
def pivot (remaining high : List Bool) : List Bool :=
  remaining.map (fun _ => true) ++ digit false high

/-- A raw query on the comparator's input stack. -/
def queryWord (input remaining high : List Bool) : List Bool :=
  delimit input ++ pivot remaining high

/-- Read one comparator answer per remaining bit, processing positions from
most to least significant. -/
def run (compare : List Bool → Bool) (input : List Bool) :
    List Bool → List Bool → List Bool
  | [], high => high
  | _ :: remaining, high =>
    let answer := compare (queryWord input remaining high)
    run compare input remaining (digit (!answer) high)

/-- Handle zero and one according to the search specification. For a canonical
input of length at least two, all bits contribute one comparison. -/
def search (compare : List Bool → Bool) (input : List Bool) : List Bool :=
  match input with
  | [] => [false, true]
  | [_] => [true]
  | _ :: _ :: _ => run compare input input []

/-- Extending a canonical prefix implements the binary place-value recurrence. -/
theorem digit_encode (b : Bool) (h : ℕ) :
    digit b (encodeNat h) = encodeNat (2 * h + b.toNat) := by
  have hb : 2 * h + b.toNat = Nat.bit b h := by cases b <;> simp [Nat.bit]
  change digit b (encodeNum (h : Num)) = encodeNum ((2 * h + b.toNat : ℕ) : Num)
  rw [hb, ← Num.ofNat'_eq (Nat.bit b h), Num.ofNat'_bit, Num.ofNat'_eq h]
  cases b <;> cases (h : Num) with
    | zero => rfl
    | pos p => cases p <;> rfl

private theorem leading_ones (remaining : List Bool) (x : ℕ) :
    remaining.map (fun _ => true) ++ encodeNat x =
      encodeNat ((x + 1) * 2 ^ remaining.length - 1) := by
  induction remaining with
  | nil => simp
  | cons bit rest ih =>
    change true :: (rest.map (fun _ => true) ++ encodeNat x) = _
    rw [ih]
    rw [← show digit true (encodeNat ((x + 1) * 2 ^ rest.length - 1)) =
        true :: encodeNat ((x + 1) * 2 ^ rest.length - 1) from rfl, digit_encode]
    congr 1
    have hp : 0 < (x + 1) * 2 ^ rest.length := Nat.mul_pos (by omega) (Nat.pow_pos (by decide))
    simp only [Bool.toNat_true, List.length_cons, Nat.pow_succ, ← Nat.mul_assoc]
    omega

/-- For `k` bits after the queried position, the interval starts at
`h * 2^(k+1)`, and the query asks about its lower half's upper endpoint. -/
theorem pivot_encode (remaining : List Bool) (h : ℕ) :
    pivot remaining (encodeNat h) =
      encodeNat (h * 2 ^ (remaining.length + 1) + 2 ^ remaining.length - 1) := by
  rw [pivot, digit_encode, leading_ones]
  simp only [Bool.toNat_false, Nat.add_zero, Nat.pow_succ]
  congr 2
  ring

/-- The concrete query word uses the exact paired-input encoding of H3. -/
theorem queryWord_encode (n : ℕ) (remaining : List Bool) (h : ℕ) :
    queryWord (encodeNat n) remaining (encodeNat h) =
      bitEncode (n, h * 2 ^ (remaining.length + 1) + 2 ^ remaining.length - 1) := by
  change delimit (encodeNat n) ++ pivot remaining (encodeNat h) = _
  rw [pivot_encode]
  rfl

/-- Invariant of the word search. With `k` unprocessed bits, the numeric
search interval starts at `h * 2^k`. -/
theorem run_encode (compare : List Bool → Bool) (query : ℕ × ℕ → Bool)
    (hq : ∀ x, compare (bitEncode x) = query x) (n : ℕ) (remaining : List Bool) (h : ℕ) :
    run compare (encodeNat n) remaining (encodeNat h) =
      encodeNat (FactorSearchClock.run query n remaining.length (h * 2 ^ remaining.length)).1 := by
  induction remaining generalizing h with
  | nil => simp [run, FactorSearchClock.run]
  | cons bit rest ih =>
    simp only [run, queryWord_encode, hq, List.length_cons, FactorSearchClock.run]
    cases ha : query (n, h * 2 ^ (rest.length + 1) + 2 ^ rest.length - 1) <;>
      simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false, if_true,
        digit_encode, Bool.toNat_true, Bool.toNat_false, Nat.add_zero, ih]
    · congr 3
      rw [Nat.pow_succ]
      ring
    · congr 3
      rw [Nat.pow_succ]
      ring

/-- The output of the word-level algorithm is the canonical encoding of exactly
the guarded arithmetic recursion used in H3. -/
theorem search_encode (compare : List Bool → Bool) (query : ℕ × ℕ → Bool)
    (hq : ∀ x, compare (bitEncode x) = query x) (n : ℕ) :
    search compare (encodeNat n) = encodeNat
      (if n < 2 then 2 - n else
        (Nat.rec (motive := fun _ => ℕ → ℕ) id
          (fun i search low =>
            if query (n, low + 2 ^ i - 1) then search low else search (low + 2 ^ i))
          (n.log2 + 1)) 0) := by
  rw [← FactorSearchClock.search_value]
  by_cases hn : n < 2
  · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;>
      simp only [FactorSearchClock.search, if_pos hn] <;> rfl
  · have hlen : (encodeNat n).length = n.log2 + 1 := by
      change (bitEncode n).length = _
      rw [FactorEncoding.length_bitEncode_nat]
      have hlo := Nat.lt_size.mpr (Nat.log2_self_le (by omega : n ≠ 0))
      have hhi : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
      omega
    have hlength : 2 ≤ (encodeNat n).length := by
      have := (Nat.le_log2 (by omega : n ≠ 0)).mpr (by omega : 2 ^ 1 ≤ n)
      omega
    have hstart : search compare (encodeNat n) = run compare (encodeNat n) (encodeNat n) [] := by
      cases hword : encodeNat n with
      | nil => simp [hword] at hlength
      | cons b rest =>
        cases rest <;> simp_all [search]
    rw [hstart, ← show encodeNat 0 = [] from rfl, run_encode compare query hq, hlen]
    simp [FactorSearchClock.search, hn]

end FactorSearchBits

/-
# Binary long division on canonical words

Read the numerator from the most significant bit. Each step appends the input
bit to the remainder and tests a subtraction of the denominator. The final
borrow determines the next quotient bit. All words passed to the next step use
the same little-endian encoding as the factorization target.
-/

namespace FactorDivisionBits

open Computability FactorSearchBits

/-- Arithmetic value of a little-endian word, including padded words. -/
def value : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * value bs + b.toNat

def diffBit (a b carry : Bool) : Bool := xor (xor a b) carry

def borrowBit (a b carry : Bool) : Bool := (!a && (b || carry)) || (b && carry)

/-- Scan the candidate from its low end. An exhausted denominator supplies zero
bits. A remaining nonempty suffix of a canonical denominator is nonzero. -/
def trial : List Bool → List Bool → Bool → Bool × List Bool
  | [], v, carry => (carry || !v.isEmpty, [])
  | a :: as, v, carry =>
    let b := v.head?.getD false
    let higher := trial as v.tail (borrowBit a b carry)
    (higher.1, diffBit a b carry :: higher.2)

/-- Drop high zeroes from a least-significant-bit-first word. -/
def trim (w : List Bool) : List Bool := (w.reverse.dropWhile (!·)).reverse

/-- The state holds the quotient prefix and the current remainder, in that order. -/
def divisionStep (den : List Bool) (qr : List Bool × List Bool) (b : Bool) :
    List Bool × List Bool :=
  let x := digit b qr.2
  let t := trial x den false
  (digit (!t.1) qr.1, if t.1 then x else trim t.2)

/-- The zero divisor returns the empty encoding of zero, matching natural division. -/
def divide (num den : List Bool) : List Bool :=
  if den.isEmpty then [] else (num.reverse.foldl (divisionStep den) ([], [])).1

private theorem toNat_le_one (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

theorem digit_length (b : Bool) (w : List Bool) :
    (digit b w).length ≤ w.length + 1 := by
  cases b <;> cases w <;> simp [digit]

theorem trial_length (u v : List Bool) (c : Bool) :
    (trial u v c).2.length = u.length := by
  induction u generalizing v c with
  | nil => rfl
  | cons a as ih => simp [trial, ih]

theorem trim_length (w : List Bool) : (trim w).length ≤ w.length := by
  simpa [trim] using (List.dropWhile_sublist (l := w.reverse) (!·)).length_le

private theorem digit_value (b : Bool) (w : List Bool) :
    value (digit b w) = 2 * value w + b.toNat := by
  cases b <;> cases w <;> rfl

private theorem bit_arith (b : Bool) (n : ℕ) : Nat.bit b n = 2 * n + b.toNat := by
  cases b <;> simp [Nat.bit]

theorem value_encodeNat (n : ℕ) : value (encodeNat n) = n := by
  induction n using Nat.binaryRec with
  | zero => rfl
  | bit b n ih => rw [bit_arith, ← digit_encode, digit_value, ih]

private def Canonical : List Bool → Prop
  | [] => True
  | b :: bs => (b = true ∨ 0 < value bs) ∧ Canonical bs

private theorem value_pos {b : Bool} {w : List Bool} (hw : Canonical (b :: w)) :
    0 < value (b :: w) := by
  rcases hw.1 with rfl | h <;> simp [value]
  omega

private theorem canonical_digit (b : Bool) (w : List Bool) (hw : Canonical w) :
    Canonical (digit b w) := by
  cases w with
  | nil => cases b <;> simp [digit, Canonical]
  | cons a as =>
    have hp := value_pos hw
    cases b <;> exact ⟨Or.inr hp, hw⟩

private theorem canonical_encode (n : ℕ) : Canonical (encodeNat n) := by
  induction n using Nat.binaryRec with
  | zero => trivial
  | bit b n ih => rw [bit_arith, ← digit_encode]; exact canonical_digit _ _ ih

private theorem trim_cons (b : Bool) (w : List Bool) : trim (b :: w) = digit b (trim w) := by
  simp only [trim, List.reverse_cons, List.dropWhile_append]
  cases h : (w.reverse.dropWhile (!·)) with
  | nil => cases b <;> rfl
  | cons a rest =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append]
    cases b <;> simp [digit]

theorem trim_encode (w : List Bool) : trim w = encodeNat (value w) := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [trim_cons, ih, digit_encode, value]

private theorem sub_digit_identity (a b c : Bool) :
    a.toNat + 2 * (borrowBit a b c).toNat = b.toNat + c.toNat + (diffBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

private theorem trial_spec (u v : List Bool) (c : Bool) (hv : Canonical v) :
    ((trial u v c).1 = true ↔ value u < value v + c.toNat) ∧
    ((trial u v c).1 = false → value (trial u v c).2 + value v + c.toNat = value u) := by
  induction u generalizing v c with
  | nil =>
    cases v with
    | nil => cases c <;> decide
    | cons b bs =>
      have hp := value_pos hv
      cases c <;> simp [trial, value] at *
      omega
  | cons a as ih =>
    let b := v.head?.getD false
    have htail : Canonical v.tail := by cases v with
      | nil => trivial
      | cons d ds => exact hv.2
    have hval : value v = 2 * value v.tail + b.toNat := by cases v <;> rfl
    obtain ⟨hborrow, hdiff⟩ := ih v.tail (borrowBit a b c) htail
    have hbit := sub_digit_identity a b c
    have hsmall := toNat_le_one (diffBit a b c)
    change ((trial as v.tail (borrowBit a b c)).1 = true ↔ 2 * value as + a.toNat < value v + c.toNat) ∧
      ((trial as v.tail (borrowBit a b c)).1 = false →
        2 * value (trial as v.tail (borrowBit a b c)).2 + (diffBit a b c).toNat +
          value v + c.toNat = 2 * value as + a.toNat)
    rw [hborrow, hval]
    constructor
    · omega
    · intro hc
      have := hdiff hc
      omega

/-- A single bit scan compares with the denominator and, on success, produces
the canonical nonnegative difference after trimming. -/
theorem trial_encode (u d : ℕ) :
    ((trial (encodeNat u) (encodeNat d) false).1 = true ↔ u < d) ∧
    (d ≤ u → trim (trial (encodeNat u) (encodeNat d) false).2 = encodeNat (u - d)) := by
  obtain ⟨hb, hs⟩ := trial_spec (encodeNat u) (encodeNat d) false (canonical_encode d)
  simp only [value_encodeNat, Bool.toNat_false, Nat.add_zero] at hb hs
  refine ⟨hb, fun h => ?_⟩
  have hf : (trial (encodeNat u) (encodeNat d) false).1 = false := by
    cases h' : (trial (encodeNat u) (encodeNat d) false).1 with
    | false => rfl
    | true => exact False.elim ((Nat.not_lt.mpr h) (hb.mp h'))
  rw [trim_encode]
  congr 1
  have := hs hf
  omega

/-- One input digit extends the value of the processed prefix from `a` to
`2*a+b`, preserving the exact quotient and remainder. -/
theorem divisionStep_encode (d a : ℕ) (hd : 0 < d) (b : Bool) :
    divisionStep (encodeNat d) (encodeNat (a / d), encodeNat (a % d)) b =
      (encodeNat ((2 * a + b.toNat) / d), encodeNat ((2 * a + b.toNat) % d)) := by
  let x := 2 * (a % d) + b.toNat
  have hx : x < 2 * d := by
    have := Nat.mod_lt a hd
    have := toNat_le_one b
    dsimp [x]
    omega
  have hsplit : 2 * a + b.toNat = x + d * (2 * (a / d)) := by
    have h := Nat.mod_add_div a d
    dsimp [x]
    calc
      2 * a + b.toNat = 2 * (a % d + d * (a / d)) + b.toNat := by rw [h]
      _ = _ := by ring
  have hq : (2 * a + b.toNat) / d = x / d + 2 * (a / d) := by
    rw [hsplit, Nat.add_mul_div_left _ _ hd]
  have hr : (2 * a + b.toNat) % d = x % d := by rw [hsplit, Nat.add_mul_mod_self_left]
  obtain ⟨hborrow, hdiff⟩ := trial_encode x d
  change (digit (!(trial (digit b (encodeNat (a % d))) (encodeNat d) false).1) (encodeNat (a / d)),
    if (trial (digit b (encodeNat (a % d))) (encodeNat d) false).1
      then digit b (encodeNat (a % d))
      else trim (trial (digit b (encodeNat (a % d))) (encodeNat d) false).2) = _
  rw [digit_encode b (a % d), hq, hr]
  change (digit (!(trial (encodeNat x) (encodeNat d) false).1) (encodeNat (a / d)),
    if (trial (encodeNat x) (encodeNat d) false).1 then encodeNat x
    else trim (trial (encodeNat x) (encodeNat d) false).2) = _
  by_cases h : x < d
  · simp [hborrow.mpr h, digit_encode, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
  · have hb : (trial (encodeNat x) (encodeNat d) false).1 = false :=
      Bool.eq_false_iff.mpr (fun e => h (hborrow.mp e))
    have hd' : d ≤ x := by omega
    have hsmall : x - d < d := by omega
    have hdiv : x / d = 1 := by rw [Nat.div_eq_sub_div hd hd', Nat.div_eq_of_lt hsmall]
    have hmod : x % d = x - d := by rw [Nat.mod_eq_sub_mod hd', Nat.mod_eq_of_lt hsmall]
    simp [hb, hdiff hd', hdiv, hmod, digit_encode, Nat.add_comm]

/-- The state after reading any prefix, stored here least significant bit first. -/
theorem fold_encode (w : List Bool) (d : ℕ) (hd : 0 < d) :
    w.reverse.foldl (divisionStep (encodeNat d)) ([], []) =
      (encodeNat (value w / d), encodeNat (value w % d)) := by
  induction w with
  | nil => simp [value]; rfl
  | cons b w ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    exact divisionStep_encode _ _ hd _

/-- Machine-level output specification including natural division by zero. -/
theorem divide_encode (n d : ℕ) :
    divide (encodeNat n) (encodeNat d) = encodeNat (n / d) := by
  by_cases hd : d = 0
  · subst d
    simp [divide]
    rfl
  · have hne : encodeNat d ≠ [] := by
      intro h
      have hv := value_encodeNat d
      rw [h] at hv
      exact hd hv.symm
    simp [divide, hne, fold_encode _ _ (by omega : 0 < d), value_encodeNat]

private theorem length_encode (n : ℕ) : (encodeNat n).length = n.size :=
  FactorEncoding.length_bitEncode_nat n

private theorem value_lt_pow (w : List Bool) : value w < 2 ^ w.length := by
  induction w with
  | nil => decide
  | cons b w ih =>
    have hb := toNat_le_one b
    simp only [value, List.length_cons, Nat.pow_succ]
    omega

/-- The quotient and remainder each grow by at most one bit in a single
iteration. This bound does not require a canonical incoming state. -/
theorem divisionStep_lengths (den : List Bool) (qr : List Bool × List Bool) (b : Bool) :
    (divisionStep den qr b).1.length ≤ qr.1.length + 1 ∧
    (divisionStep den qr b).2.length ≤ qr.2.length + 1 := by
  constructor
  · exact digit_length _ _
  · dsimp only [divisionStep]
    split
    · exact digit_length _ _
    · exact (trim_length _).trans ((trial_length _ _ _).le.trans (digit_length _ _))

/-- After `w.length` input digits the quotient has at most that many bits.
The remainder is also bounded by the denominator width. -/
theorem prefix_lengths (w : List Bool) (d : ℕ) (hd : 0 < d) :
    let qr := w.reverse.foldl (divisionStep (encodeNat d)) ([], [])
    qr.1.length ≤ w.length ∧ qr.2.length ≤ min w.length (encodeNat d).length := by
  dsimp only
  rw [fold_encode w d hd]
  simp only [length_encode, le_min_iff]
  have hv : (value w).size ≤ w.length := Nat.size_le.mpr (value_lt_pow w)
  exact ⟨(Nat.size_le_size (Nat.div_le_self _ _)).trans hv,
    (Nat.size_le_size (Nat.mod_le _ _)).trans hv, Nat.size_le_size (Nat.mod_lt _ hd).le⟩

/-- The candidate remainder and its raw trial-difference buffer have the
same length. Both use at most one bit beyond the smaller of the divisor width
and the number of digits processed before this step. -/
theorem trial_working_lengths (w : List Bool) (d : ℕ) (hd : 0 < d) (b : Bool) :
    let rem := (w.reverse.foldl (divisionStep (encodeNat d)) ([], [])).2
    let x := digit b rem
    x.length ≤ min w.length (encodeNat d).length + 1 ∧
    (trial x (encodeNat d) false).2.length = x.length := by
  dsimp only
  exact ⟨(digit_length _ _).trans (Nat.succ_le_succ (prefix_lengths w d hd).2),
    trial_length _ _ _⟩

end FactorDivisionBits

/- Interface for the two-input binary quotient routine inside factor extraction. -/

namespace FactorQuotientSpec

open Turing Computability

/-- Both arguments are little-endian natural number encodings. The quotient
replaces the numerator. The denominator and all private working stacks are
empty when the subroutine finishes. -/
structure Routine where
  K : Type
  [kDec : DecidableEq K]
  [kFin : Fintype K]
  Λ : Type
  [lDec : DecidableEq Λ]
  [lFin : Fintype Λ]
  σ : Type
  [sFin : Fintype σ]
  numerator : K
  denominator : K
  separate : numerator ≠ denominator
  entry : Λ
  initial : σ
  code : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ

instance (D : Routine) : DecidableEq D.K := D.kDec
instance (D : Routine) : Fintype D.K := D.kFin
instance (D : Routine) : DecidableEq D.Λ := D.lDec
instance (D : Routine) : Fintype D.Λ := D.lFin
instance (D : Routine) : Fintype D.σ := D.sFin

namespace Routine

variable (D : Routine)

abbrev Cfg := TM2.Cfg (fun _ : D.K => Bool) D.Λ D.σ

/-- Denominator and numerator words in the otherwise empty division block. -/
def inputs (x y : List Bool) (k : D.K) : List Bool :=
  if k = D.numerator then x else if k = D.denominator then y else []

def beginCfg (x y : ℕ) : D.Cfg :=
  ⟨some D.entry, D.initial, D.inputs (encodeNat x) (encodeNat y)⟩

def endCfg (x y : ℕ) : D.Cfg :=
  ⟨none, D.initial, D.inputs (encodeNat (x / y)) []⟩

def CorrectIn (P : Polynomial ℕ) : Prop :=
  ∀ x y : ℕ, Nonempty (StateTransition.EvalsToInTime (TM2.step D.code)
    (D.beginCfg x y) (some (D.endCfg x y))
    (P.eval ((encodeNat x).length + (encodeNat y).length)))

end Routine
end FactorQuotientSpec

/- Restoring binary long division on finite Bool stacks. The input is reversed
once. Each round tries one subtraction, restores the divisor, and outputs one bit. -/

namespace FactorDivisionController

open Turing.TM2

inductive Stack
  | num | den | bits | rem | savedDen | savedRem | diff
  deriving DecidableEq

inductive Label
  | start | zero | reverseIn | readBit | subtract (borrow : Bool)
  | reject | restoreRem | clearDiff | accept | trim | writeRem | clearSaved
  | restoreDen | clearDen | clearRem
  deriving DecidableEq

instance : Fintype Stack := Fintype.ofList
  [.num, .den, .bits, .rem, .savedDen, .savedRem, .diff] (by intro k; cases k <;> decide)

instance : Fintype Label := Fintype.ofList
  [.start, .zero, .reverseIn, .readBit, .subtract false, .subtract true,
   .reject, .restoreRem, .clearDiff, .accept, .trim, .writeRem, .clearSaved,
   .restoreDen, .clearDen, .clearRem]
  (by intro l; cases l <;> first | decide | (rename_i borrow; cases borrow <;> decide))

abbrev Reg := Option Bool × Option Bool
abbrev Code := Stmt (fun _ : Stack => Bool) Label Reg
abbrev Config := Cfg (fun _ : Stack => Bool) Label Reg

private def go (l : Label) : Code := .load (fun _ => (none, none)) (.goto (fun _ => l))
private def stop : Code := .load (fun _ => (none, none)) .halt
private def put (k : Stack) (b : Bool) (q : Code) : Code := .push k (fun _ => b) q
private def bit₁ (r : Reg) : Bool := r.1.getD false
private def bit₂ (r : Reg) : Bool := r.2.getD false
private def pop (k : Stack) (item empty : Code) : Code :=
  .pop k (fun _ v => (v, none)) (.branch (fun r => r.1.isSome) item empty)
private def peek (k : Stack) (item empty : Code) : Code :=
  .peek k (fun _ v => (v, none)) (.branch (fun r => r.1.isSome) item empty)
private def skip (k : Stack) (q : Code) : Code := .pop k (fun r _ => r) q
private def transfer (from_ to_ : Stack) (again next : Label) : Code :=
  pop from_ (.push to_ bit₁ (go again)) (go next)

private def subtractBit (borrow : Bool) : Code :=
  let calculate := .push Stack.diff (fun r => FactorDivisionBits.diffBit (bit₁ r) (bit₂ r) borrow)
    (.branch (fun r => FactorDivisionBits.borrowBit (bit₁ r) (bit₂ r) borrow)
      (go (.subtract true)) (go (.subtract false)))
  .push .savedRem bit₁ (.pop .den (fun r v => (r.1, v))
    (.branch (fun r => r.2.isSome) (.push .savedDen bit₂ calculate) calculate))

def program : Label → Code
  | .start => peek .den (go .reverseIn) (go .zero)
  | .zero => pop .num (go .zero) stop
  | .reverseIn => transfer .num .bits .reverseIn .readBit
  | .readBit => pop .bits
      (.branch bit₁ (put .rem true (go (.subtract false)))
        (peek .rem (put .rem false (go (.subtract false))) (go (.subtract false))))
      (go .clearDen)
  | .subtract borrow => pop .rem (subtractBit borrow)
      (if borrow then go .reject else peek .den (go .reject) (go .accept))
  | .reject => peek .num (put .num false (go .restoreRem)) (go .restoreRem)
  | .restoreRem => transfer .savedRem .rem .restoreRem .clearDiff
  | .clearDiff => pop .diff (go .clearDiff) (go .restoreDen)
  | .accept => put .num true (go .trim)
  | .trim => peek .diff (.branch bit₁ (go .writeRem) (skip .diff (go .trim))) (go .writeRem)
  | .writeRem => transfer .diff .rem .writeRem .clearSaved
  | .clearSaved => pop .savedRem (go .clearSaved) (go .restoreDen)
  | .restoreDen => transfer .savedDen .den .restoreDen .readBit
  | .clearDen => pop .den (go .clearDen) (go .clearRem)
  | .clearRem => pop .rem (go .clearRem) stop

def division : FactorQuotientSpec.Routine where
  K := Stack
  Λ := Label
  σ := Reg
  numerator := .num
  denominator := .den
  separate := by decide
  entry := .start
  initial := (none, none)
  code := program

def words (num den bits rem savedDen savedRem diff : List Bool) : Stack → List Bool
  | .num => num
  | .den => den
  | .bits => bits
  | .rem => rem
  | .savedDen => savedDen
  | .savedRem => savedRem
  | .diff => diff

def cfg (l : Option Label) (num den bits rem sd sr df : List Bool) : Config :=
  ⟨l, (none, none), words num den bits rem sd sr df⟩
abbrev atL (l : Label) := cfg (some l)

inductive Work : Config → Config → ℕ → Prop
  | refl (c) : Work c c 0
  | one {c d} : step program c = some d → Work c d 1
  | trans {a b c t u} : Work a b t → Work b c u → Work a c (t + u)
  | mono {a b t u} : Work a b t → t ≤ u → Work a b u

private theorem workStep {l n d bs r sd sr df dest}
    (hl : (stepAux (program l) (none,none) (words n d bs r sd sr df)).l = dest.l)
    (hv : (stepAux (program l) (none,none) (words n d bs r sd sr df)).var = dest.var)
    (hs : ∀ k, (stepAux (program l) (none,none) (words n d bs r sd sr df)).stk k = dest.stk k) :
    Work (atL l n d bs r sd sr df) dest 1 := by
  apply Work.one
  apply congrArg some
  change stepAux _ _ _ = dest
  have hstk := funext hs
  cases ha : stepAux (program l) (none,none) (words n d bs r sd sr df) with
  | mk L V S =>
    rw [ha] at hl hv hstk
    cases dest
    congr

private theorem consume (stage : List Bool → List Bool → Config) (finish : List Bool → Config)
    (next : ∀ b xs acc, Work (stage (b :: xs) acc) (stage xs (b :: acc)) 1)
    (done_ : ∀ acc, Work (stage [] acc) (finish acc) 1)
    (xs acc : List Bool) : Work (stage xs acc) (finish (xs.reverse ++ acc)) (xs.length + 1) := by
  induction xs generalizing acc with
  | nil => simpa using done_ acc
  | cons b xs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm 1 (xs.length + 1)] using
      (next b xs acc).trans (ih (b :: acc))

private theorem clear (stage : List Bool → Config) (finish : Config)
    (next : ∀ b xs, Work (stage (b :: xs)) (stage xs) 1)
    (done_ : Work (stage []) finish 1)
    (xs : List Bool) : Work (stage xs) finish (xs.length + 1) := by
  have h := consume (fun xs _ => stage xs) (fun _ => finish)
    (fun b xs _ => next b xs) (fun _ => done_) xs []
  exact h

theorem initNonzero (x : List Bool) (d : Bool) (ds : List Bool) :
    Work (atL .start x (d :: ds) [] [] [] [] [])
      (atL .readBit [] (d :: ds) x.reverse [] [] [] []) (x.length + 2) := by
  have a : Work (atL .start x (d :: ds) [] [] [] [] [])
      (atL .reverseIn x (d :: ds) [] [] [] [] []) 1 := by
    apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  have b := consume (fun xs acc => atL .reverseIn xs (d :: ds) acc [] [] [] [])
    (fun acc => atL .readBit [] (d :: ds) acc [] [] [] [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) x []
  simpa [Nat.add_comm 1 (x.length + 1)] using a.trans b

theorem initZero (x : List Bool) :
    Work (atL .start x [] [] [] [] [] []) (cfg none [] [] [] [] [] [] []) (x.length + 2) := by
  have a : Work (atL .start x [] [] [] [] [] []) (atL .zero x [] [] [] [] [] []) 1 := by
    apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  have b := clear (fun xs => atL .zero xs [] [] [] [] [] []) (cfg none [] [] [] [] [] [] [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) x
  simpa [Nat.add_comm 1 (x.length + 1)] using a.trans b

theorem finishPath (q d r : List Bool) :
    Work (atL .readBit q d [] r [] [] []) (cfg none q [] [] [] [] [] [])
      (d.length + r.length + 3) := by
  have a : Work (atL .readBit q d [] r [] [] []) (atL .clearDen q d [] r [] [] []) 1 := by
    apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  have b := clear (fun xs => atL .clearDen q xs [] r [] [] [])
    (atL .clearRem q [] [] r [] [] [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) d
  have c := clear (fun xs => atL .clearRem q [] [] xs [] [] [])
    (cfg none q [] [] [] [] [] [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) r
  convert (a.trans b).trans c using 1
  omega

private theorem subtractRun (q bs u : List Bool) (d : List Bool) (borrow : Bool) (sd sr df : List Bool) :
    Work (atL (.subtract borrow) q d bs u sd sr df)
      (atL (cond (FactorDivisionBits.trial u d borrow).1 .reject .accept)
        q (d.drop u.length) bs [] ((d.take u.length).reverse ++ sd)
        (u.reverse ++ sr) ((FactorDivisionBits.trial u d borrow).2.reverse ++ df)) (u.length + 1) := by
  induction u generalizing d borrow sd sr df with
  | nil =>
    cases d <;> cases borrow <;> apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  | cons a u ih =>
    cases d with
    | nil =>
      let c := FactorDivisionBits.borrowBit a false borrow
      let z := FactorDivisionBits.diffBit a false borrow
      have h : Work (atL (.subtract borrow) q [] bs (a :: u) sd sr df)
          (atL (.subtract c) q [] bs u sd (a :: sr) (z :: df)) 1 := by
        cases a <;> cases borrow <;> apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
      simpa [FactorDivisionBits.trial, c, z, List.reverse_cons, List.append_assoc,
        Nat.add_comm 1 (u.length + 1)] using h.trans (ih [] c sd (a :: sr) (z :: df))
    | cons y ys =>
      let c := FactorDivisionBits.borrowBit a y borrow
      let z := FactorDivisionBits.diffBit a y borrow
      have h : Work (atL (.subtract borrow) q (y :: ys) bs (a :: u) sd sr df)
          (atL (.subtract c) q ys bs u (y :: sd) (a :: sr) (z :: df)) 1 := by
        cases a <;> cases y <;> cases borrow <;> apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
      simpa [FactorDivisionBits.trial, c, z, List.reverse_cons, List.append_assoc,
        Nat.add_comm 1 (u.length + 1)] using h.trans (ih ys c (y :: sd) (a :: sr) (z :: df))

private theorem trimPath (q d bs sd sr df : List Bool) :
    Work (atL .trim q d bs [] sd sr df)
      (atL .writeRem q d bs [] sd sr (df.dropWhile (!·))) (df.length + 1) := by
  induction df with
  | nil => apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  | cons b df ih =>
    cases b with
    | false =>
      have h : Work (atL .trim q d bs [] sd sr (false :: df))
          (atL .trim q d bs [] sd sr df) 1 := by
        apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
      simpa [List.dropWhile, Nat.add_comm 1 (df.length + 1)] using h.trans ih
    | true =>
      have h : Work (atL .trim q d bs [] sd sr (true :: df))
          (atL .writeRem q d bs [] sd sr (true :: df)) 1 := by
        apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
      exact h.mono (by simp)

private theorem restoreDenPath (q d bs r sd : List Bool) :
    Work (atL .restoreDen q d bs r sd [] [])
      (atL .readBit q (sd.reverse ++ d) bs r [] [] []) (sd.length + 1) := by
  exact consume (fun xs acc => atL .restoreDen q acc bs r xs [] [])
    (fun acc => atL .readBit q acc bs r [] [] [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) sd d

private theorem rejectPath (q d bs sd sr df : List Bool) :
    Work (atL .reject q d bs [] sd sr df)
      (atL .readBit (FactorSearchBits.digit false q) (sd.reverse ++ d) bs sr.reverse [] [] [])
      (sr.length + df.length + sd.length + 4) := by
  let out := FactorSearchBits.digit false q
  have a : Work (atL .reject q d bs [] sd sr df) (atL .restoreRem out d bs [] sd sr df) 1 := by
    cases q <;> apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  have b := consume (fun xs acc => atL .restoreRem out d bs acc sd xs df)
    (fun acc => atL .clearDiff out d bs acc sd [] df)
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) sr []
  have c := clear (fun xs => atL .clearDiff out d bs sr.reverse sd [] xs)
    (atL .restoreDen out d bs sr.reverse sd [] [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) df
  simp only [List.append_nil] at b
  convert ((a.trans b).trans c).trans (restoreDenPath out d bs sr.reverse sd) using 1
  omega

private theorem acceptPath (q d bs sd sr df : List Bool) :
    Work (atL .accept q d bs [] sd sr df)
      (atL .readBit (true :: q) (sd.reverse ++ d) bs (df.dropWhile (!·)).reverse [] [] [])
      (2 * df.length + sr.length + sd.length + 5) := by
  let out := true :: q
  let trimmed := df.dropWhile (!·)
  have a : Work (atL .accept q d bs [] sd sr df) (atL .trim out d bs [] sd sr df) 1 := by
    apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  have b := trimPath out d bs sd sr df
  have c := consume (fun xs acc => atL .writeRem out d bs acc sd sr xs)
    (fun acc => atL .clearSaved out d bs acc sd sr [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) trimmed []
  simp only [List.append_nil] at c
  have e := clear (fun xs => atL .clearSaved out d bs trimmed.reverse sd xs [])
    (atL .restoreDen out d bs trimmed.reverse sd [] [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) sr
  apply ((((a.trans b).trans c).trans e).trans (restoreDenPath out d bs trimmed.reverse sd)).mono
  have hlen : trimmed.length ≤ df.length := (List.dropWhile_sublist (l := df) (!·)).length_le
  omega

/-- Process one numerator bit. Trial subtraction and restoration inspect no more
denominator bits than there are bits of the shifted remainder. -/
theorem roundStep (q d bs r : List Bool) (b : Bool) :
    Work (atL .readBit q d (b :: bs) r [] [] [])
      (atL .readBit (FactorDivisionBits.divisionStep d (q, r) b).1 d bs
        (FactorDivisionBits.divisionStep d (q, r) b).2 [] [] [])
      (6 * (r.length + 1) + 10) := by
  let u := FactorSearchBits.digit b r
  let lhs := FactorDivisionBits.trial u d false
  have a : Work (atL .readBit q d (b :: bs) r [] [] [])
      (atL (.subtract false) q d bs u [] [] []) 1 := by
    cases b <;> cases r <;> apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  have sub := subtractRun q bs u d false [] [] []
  simp only [List.append_nil] at sub
  change Work _ (atL (cond lhs.1 .reject .accept) q (d.drop u.length) bs []
    (d.take u.length).reverse u.reverse lhs.2.reverse) _ at sub
  have hu : u.length ≤ r.length + 1 := FactorDivisionBits.digit_length b r
  have hraw : lhs.2.length = u.length := FactorDivisionBits.trial_length u d false
  have htake : (d.take u.length).length ≤ u.length := List.length_take_le ..
  change Work _ (atL .readBit (FactorSearchBits.digit (!lhs.1) q) d bs
    (if lhs.1 then u else FactorDivisionBits.trim lhs.2) [] [] []) _
  cases hb : lhs.1 with
  | false =>
    rw [hb] at sub
    have h := acceptPath q (d.drop u.length) bs (d.take u.length).reverse u.reverse lhs.2.reverse
    simp only [List.reverse_reverse, List.take_append_drop, List.length_reverse] at h
    exact ((a.trans sub).trans h).mono (by omega)
  | true =>
    rw [hb] at sub
    have h := rejectPath q (d.drop u.length) bs (d.take u.length).reverse u.reverse lhs.2.reverse
    simp only [List.reverse_reverse, List.take_append_drop, List.length_reverse] at h
    exact ((a.trans sub).trans h).mono (by omega)

end FactorDivisionController

/- A quadratic clock for finite-stack binary long division, in the sum of both input lengths. -/

namespace FactorDivisionTime

open FactorDivisionBits FactorDivisionController FactorQuotientSpec Computability Turing

theorem work_to_evals {a b : Config} {t : ℕ} (h : Work a b t) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step program) a (some b) t) := by
  induction h with
  | refl c => exact ⟨StateTransition.EvalsToInTime.refl _ _⟩
  | one hs => exact ⟨⟨⟨1, hs⟩, Nat.le_refl _⟩⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨u⟩ := ih₁
    obtain ⟨v⟩ := ih₂
    exact ⟨⟨u.toEvalsTo.trans _ _ _ _ v.toEvalsTo, by
      dsimp [StateTransition.EvalsTo.trans]
      have := u.steps_le_m
      have := v.steps_le_m
      omega⟩⟩
  | mono _ hle ih =>
    obtain ⟨u⟩ := ih
    exact ⟨⟨u.toEvalsTo, u.steps_le_m.trans hle⟩⟩

noncomputable def divisionClock : Polynomial ℕ := 6 * Polynomial.X ^ 2 + 19 * Polynomial.X + 5

private theorem run_rounds (d bs : List Bool) (qr : List Bool × List Bool) (L : ℕ)
    (hsize : qr.2.length + bs.length ≤ L) :
    Work (atL .readBit qr.1 d bs qr.2 [] [] [])
      (atL .readBit (bs.foldl (divisionStep d) qr).1 d [] (bs.foldl (divisionStep d) qr).2 [] [] [])
      (bs.length * (6*(L+1)+10)) ∧ (bs.foldl (divisionStep d) qr).2.length ≤ L := by
  induction bs generalizing qr with
  | nil => exact ⟨by simpa using Work.refl (atL .readBit qr.1 d [] qr.2 [] [] []), by simpa using hsize⟩
  | cons b bs ih =>
    have hnew := (divisionStep_lengths d qr b).2
    simp only [List.length_cons] at hsize
    obtain ⟨hrest, hend⟩ := ih (divisionStep d qr b) (by omega)
    refine ⟨((roundStep qr.1 d bs qr.2 b).trans hrest).mono ?_, hend⟩
    simp only [List.length_cons, Nat.succ_mul]
    omega

private theorem clock_arith (L D R : ℕ) (hR : R ≤ L) :
    L + 2 + L * (6 * (L + 1) + 10) + (D + R + 3) ≤ divisionClock.eval (L+D) := by
  have hL : L ≤ L+D := by omega
  have hD : D ≤ L+D := by omega
  calc
    _ ≤ (L+D) + 2 + (L+D) * (6 * ((L+D) + 1) + 10) + (2 * (L+D) + 3) := by
      apply Nat.add_le_add
      · apply Nat.add_le_add (by omega)
        exact Nat.mul_le_mul hL (by omega)
      · omega
    _ = _ := by simp [divisionClock]; ring

private theorem divide_words (x den : List Bool) : Work
    (atL .start x den [] [] [] [] []) (cfg none (divide x den) [] [] [] [] [] [])
    (divisionClock.eval (x.length+den.length)) := by
  cases den with
  | nil =>
    apply (initZero x).mono
    simp [divisionClock]
    omega
  | cons d ds =>
    let den := d :: ds
    obtain ⟨hr, hlen⟩ := run_rounds den x.reverse ([], []) x.length (by simp)
    rw [List.length_reverse] at hr
    let finalState := x.reverse.foldl (divisionStep den) ([], [])
    have h := ((initNonzero x d ds).trans hr).trans (finishPath finalState.1 den finalState.2)
    exact h.mono (clock_arith x.length den.length finalState.2.length hlen)

private theorem start_cfg (x y : ℕ) : division.beginCfg x y = atL .start (encodeNat x) (encodeNat y) [] [] [] [] [] := by
  apply congrArg (fun s => (⟨some Label.start, (none,none), s⟩ : Config))
  funext k
  cases k <;> rfl

private theorem stop_cfg (x y : ℕ) : division.endCfg x y = cfg none (encodeNat (x/y)) [] [] [] [] [] [] := by
  apply congrArg (fun s => (⟨none, (none,none), s⟩ : Config))
  funext k
  cases k <;> rfl

/-- On natural number inputs the finite machine returns the encoded quotient, including at a zero divisor. -/
theorem division_correct : division.CorrectIn divisionClock := by
  intro x y
  have h := divide_words (encodeNat x) (encodeNat y)
  rw [divide_encode] at h
  rw [start_cfg, stop_cfg]
  exact work_to_evals h

/-- Polynomial-time witness for embedding the quotient subroutine. -/
theorem exists_clock : ∃ P : Polynomial ℕ, division.CorrectIn P := ⟨divisionClock, division_correct⟩

end FactorDivisionTime

/-
# A finite-stack machine for repeated factor extraction

The caller saves its factor list and clock on private stacks. The division
subroutine uses the existing numerator and denominator stacks in place. Each
factor found by the supplied function is appended as a self-delimiting block.
-/

namespace FactorEmitMachine

open Turing Computability BitstringEncoding FactorMachineLift FactorOracleMachine FactorEmitController
open FactorQuotientSpec

variable (D : Routine)

abbrev PrivateIndex := {k : D.K // k ≠ D.numerator ∧ k ≠ D.denominator}
abbrev Idx := Stack ⊕ PrivateIndex D
abbrev PC := Label ⊕ D.Λ
abbrev Reg := Option Bool × D.σ

private def divIndex (k : D.K) : Idx D :=
  if hn : k = D.numerator then .inl .num else
  if hd : k = D.denominator then .inl .den else .inr ⟨k, hn, hd⟩

private def divEmbedding : D.K ↪ Idx D where
  toFun := divIndex D
  inj' := by
    intro a b hab
    by_cases ha : a = D.numerator <;> by_cases hb : b = D.numerator <;>
      by_cases hda : a = D.denominator <;> by_cases hdb : b = D.denominator <;>
      simp_all [divIndex]

private def outerLift : Lift (fun _ : Stack => Bool) (fun _ : Idx D => Bool)
    Label (PC D) (Option Bool) (Reg D) where
  stack := ⟨Sum.inl, Sum.inl_injective⟩
  symbol _ := Equiv.refl _
  label := Sum.inl
  exitLabel := none
  read := Prod.fst
  write w v := (v, w.2)
  read_write _ _ := rfl
  write_write _ _ _ := rfl

private def divLift : Lift (fun _ : D.K => Bool) (fun _ : Idx D => Bool)
    D.Λ (PC D) D.σ (Reg D) where
  stack := divEmbedding D
  symbol _ := Equiv.refl _
  label := Sum.inr
  exitLabel := some (.inl .round)
  read := Prod.snd
  write w v := (w.1, v)
  read_write _ _ := rfl
  write_write _ _ _ := rfl

private def hostCode : PC D → TM2.Stmt (fun _ : Idx D => Bool) (PC D) (Reg D)
  | .inl l => if l = .divCall then .goto (fun _ => .inr D.entry)
              else (outerLift D).stmt (program l)
  | .inr l => (divLift D).stmt (D.code l)

def driver : OracleProgram where
  K := Idx D
  Λ := PC D
  σ := Reg D
  k₀ := .inl .io
  k₁ := .inl .io
  arg := .inl .io
  main := .inl .start
  call := .inl .ask
  resume := .inl .resume
  initialState := (none, D.initial)
  m := hostCode D

private def outerTapes (s : Stack → List Bool) : Idx D → List Bool :=
  Sum.elim s (fun _ => [])

def embedOuter (c : Config) : (driver D).Cfg :=
  ⟨c.l.map Sum.inl, (c.var, D.initial), outerTapes D c.stk⟩

private theorem outerMatch (c : Config) :
    (outerLift D).Matches (none, D.initial) (fun _ => []) c (embedOuter D c) := by
  refine ⟨?_, rfl, ⟨?_, ?_⟩⟩
  · change c.l.map Sum.inl = (outerLift D).mapLabel c.l
    cases c.l <;> rfl
  · intro k
    exact (List.map_id _).symm
  · rintro (k | k) h
    · exact False.elim (h k rfl)
    · rfl

abbrev Runs (d : ℕ → ℕ) (charge : Polynomial ℕ) :=
  FactorWordOracle.Run (driver D) (bitEncode (α := ℕ)) (bitEncode (α := ℕ)) d charge.eval

theorem work_runs {a b t} (hw : Work a b t) (d : ℕ → ℕ) (charge : Polynomial ℕ) :
    Runs D d charge (embedOuter D a) (embedOuter D b) t := by
  induction hw with
  | refl c => exact FactorWordOracle.Run.refl (C := driver D) _
  | trans _ _ ha hb => exact ha.trans hb
  | @one c z hna hnd hs =>
    rcases c with ⟨lo,v,s⟩
    cases lo with
    | none => cases hs
    | some l =>
      have hd : l ≠ .divCall := fun h => hnd (congrArg some h)
      have ha : l ≠ .ask := fun h => hna (congrArg some h)
      have he : TM2.stepAux (program l) v s = z := Option.some.inj hs
      subst z
      apply FactorWordOracle.Run.normal
      · exact fun h => ha (Sum.inl.inj (Option.some.inj h))
      · change some (TM2.stepAux (hostCode D (.inl l)) (v, D.initial) (outerTapes D s)) = _
        rw [hostCode, if_neg hd]
        apply congrArg some
        have m := (outerLift D).stepAux_stmt (program l) (none, D.initial) (fun _ => [])
          v s (outerTapes D s) (outerMatch D ⟨some l,v,s⟩).stack_eq
        exact m.unique _ (outerMatch D _)

private def mounted (dstate : D.Cfg) (fuel acc : List Bool) : (driver D).Cfg :=
  ⟨(divLift D).mapLabel dstate.l, (none, dstate.var),
    fun j => match j with
    | .inl .num => dstate.stk D.numerator
    | .inl .den => dstate.stk D.denominator
    | .inl .fuel => fuel
    | .inl .acc => acc
    | .inl _ => []
    | .inr k => dstate.stk k.1⟩

private theorem divMatch (c : D.Cfg) (fu ac : List Bool) :
    (divLift D).Matches (none, D.initial) (outerTapes D (words [] [] [] fu ac []))
      c (mounted D c fu ac) := by
  refine ⟨rfl, rfl, ⟨?_, ?_⟩⟩
  · intro k
    change (mounted D c fu ac).stk (divIndex D k) = (c.stk k).map id
    by_cases hn : k = D.numerator
    · subst k
      simp [mounted, divIndex]
    · by_cases hd : k = D.denominator
      · subst k
        simp [mounted, divIndex, hn]
      · simp [mounted, divIndex, hn, hd]
  · rintro (j | j) h
    · cases j <;> try rfl
      · exfalso; apply h D.numerator; change divIndex D _ = _; simp [divIndex]
      · exfalso; apply h D.denominator; change divIndex D _ = _; simp [divIndex, D.separate.symm]
    · exfalso
      apply h j.1
      change divIndex D _ = _
      simp [divIndex, j.2.1, j.2.2]

private theorem div_steps (d : ℕ → ℕ) (charge : Polynomial ℕ) (fu ac : List Bool)
    {a b : D.Cfg} (k : ℕ)
    (he : (flip bind (TM2.step D.code))^[k] (some a) = some b) :
    Runs D d charge (mounted D a fu ac) (mounted D b fu ac) k := by
  induction k generalizing a with
  | zero =>
    have hab : a = b := Option.some.inj he
    subst b
    exact .refl _
  | succ k ih =>
    rw [Function.iterate_succ_apply] at he
    change (flip bind (TM2.step D.code))^[k] (TM2.step D.code a) = some b at he
    cases hstep : TM2.step D.code a with
    | none =>
      rw [hstep, Function.iterate_fixed (f := flip bind (TM2.step D.code)) (x := none) rfl k] at he
      cases he
    | some next =>
      obtain ⟨actual, hactual, hm⟩ := (divLift D).step_matches (P := hostCode D) (fun _ => rfl)
        (divMatch D a fu ac) hstep
      have hnormal : (mounted D a fu ac).l ≠ some (driver D).call := by
        change (divLift D).mapLabel a.l ≠ some (Sum.inl Label.ask)
        cases a.l <;> simp [divLift, Lift.mapLabel]
      rw [hm.unique _ (divMatch D next fu ac)] at hactual
      have one : Runs D d charge _ _ 1 := FactorWordOracle.Run.normal hnormal hactual
      have later := ih (hstep ▸ he)
      simpa only [Nat.add_comm 1 k] using one.trans later

private theorem doDivision {P : Polynomial ℕ} (hD : D.CorrectIn P) (d : ℕ → ℕ)
    (charge : Polynomial ℕ) (x y : ℕ) (fu ac : List Bool) :
    Runs D d charge (embedOuter D (atL .divCall [] (encodeNat x) (encodeNat y) fu ac []))
      (embedOuter D (atL .round [] (encodeNat (x/y)) [] fu ac []))
      (1 + P.eval ((encodeNat x).length + (encodeNat y).length)) := by
  have entry : Runs D d charge (embedOuter D (atL .divCall [] (encodeNat x) (encodeNat y) fu ac []))
      (mounted D (D.beginCfg x y) fu ac) 1 := by
    apply FactorWordOracle.Run.normal (by intro h; cases h)
    apply congrArg some
    change TM2.stepAux (.goto (fun _ => Sum.inr D.entry)) _ _ = _
    unfold mounted
    simp only [TM2.stepAux]
    congr 1
    funext j
    rcases j with j | j
    · cases j <;> simp [Routine.beginCfg, Routine.inputs, outerTapes,
        cfg, atL, words, D.separate.symm]
    · simp [Routine.beginCfg, Routine.inputs, outerTapes, cfg, atL,
        j.2.1, j.2.2]
  have hend : mounted D (D.endCfg x y) fu ac =
      embedOuter D (atL .round [] (encodeNat (x/y)) [] fu ac []) := by
    unfold mounted embedOuter
    congr 1
    funext j
    rcases j with j | j
    · cases j <;> simp [Routine.endCfg, Routine.inputs, outerTapes, atL, cfg, words, D.separate.symm]
    · simp [Routine.endCfg, Routine.inputs, outerTapes, j.2.1, j.2.2]
  obtain ⟨hr⟩ := hD x y
  have hd := div_steps D d charge fu ac hr.steps hr.evals_in_steps
  rw [hend] at hd
  exact entry.trans (hd.mono hr.steps_le_m)

private theorem doOracle (d : ℕ → ℕ) (charge : Polynomial ℕ) (x : ℕ)
    (fu ac : List Bool) :
    Runs D d charge (embedOuter D (atL .ask (encodeNat x) (encodeNat x) [] fu ac []))
      (embedOuter D (atL .resume (encodeNat (d x)) (encodeNat x) [] fu ac []))
      (charge.eval (encodeNat x).length) := by
  let tapes := outerTapes D (words (encodeNat x) (encodeNat x) [] fu ac [])
  have hup : Function.update tapes ((driver D).arg) (encodeNat (d x)) =
      outerTapes D (words (encodeNat (d x)) (encodeNat x) [] fu ac []) := by
    funext k
    rcases k with k | k
    · cases k <;> rfl
    · rfl
  have h := @FactorWordOracle.Run.oracle (driver D) ℕ ℕ bitEncode bitEncode d charge.eval x
    (none, D.initial) tapes rfl
  erw [hup] at h
  exact h

private theorem initial (w : List Bool) : initList (driver D).tm w =
    embedOuter D (atL .start w [] [] [] [] []) := by
  unfold initList embedOuter
  congr 1
  funext j
  rcases j with j | j
  · cases j <;> rfl
  · rfl

private theorem finalCfg (w : List Bool) : haltList (driver D).tm w =
    embedOuter D (cfg none w [] [] [] [] []) := by
  unfold haltList embedOuter
  congr 1
  funext j
  rcases j with j | j
  · cases j <;> rfl
  · rfl

private theorem eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial k c => simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h k)

private def factorList (d : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, x => if x < 2 then [] else d x :: factorList d k (x / d x)

private def roundClock (charge divTime size : Polynomial ℕ) (L : ℕ) :=
  charge.eval L + divTime.eval (L + size.eval L) + 2*L + 4*size.eval L + 8

private theorem emitRounds (divTime : Polynomial ℕ) (hdiv : D.CorrectIn divTime)
    (d : ℕ → ℕ) (charge size : Polynomial ℕ)
    (hsize : ∀ x, (encodeNat (d x)).length ≤ size.eval (encodeNat x).length)
    (L : ℕ) (fu ac : List Bool) (x : ℕ) (hx : (encodeNat x).length ≤ L) (hf : fu.length ≤ L) :
    Runs D d charge (embedOuter D (atL .round [] (encodeNat x) [] fu ac []))
      (embedOuter D (cfg none (ac.reverse ++ bitEncode (factorList d fu.length x)) [] [] [] [] []))
      (fu.length * roundClock charge divTime size L + ac.length + L + 4) := by
  induction fu generalizing x ac with
  | nil =>
    have path := work_runs D (finish_empty (encodeNat x) ac) d charge
    change Runs D d charge _ (embedOuter D (cfg none (ac.reverse ++ []) [] [] [] [] [])) _
    rw [List.append_nil]
    exact path.mono (by simp; omega)
  | cons v fu ih =>
    by_cases hsmall : x < 2
    · have hbits : (encodeNat x).length < 2 := by
        rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> decide
      have path := work_runs D (finish_small (encodeNat x) fu ac v hbits) d charge
      simp only [List.length_cons, factorList, if_pos hsmall]
      change Runs D d charge _ (embedOuter D (cfg none (ac.reverse ++ []) [] [] [] [] [])) _
      rw [List.append_nil]
      apply path.mono
      simp only [List.length_cons] at hf
      omega
    · let input := encodeNat x
      let dw := encodeNat (d x)
      have hbits : 2 ≤ input.length := by
        change 2 ≤ (bitEncode x).length
        rw [FactorEncoding.length_bitEncode_nat]
        exact Nat.lt_size.mpr (by omega : 2 ^ 1 ≤ x)
      have hdlen : dw.length ≤ size.eval L := (hsize x).trans (eval_mono size hx)
      have hquot : (encodeNat (x / d x)).length ≤ L := by
        change (bitEncode (x / d x)).length ≤ L
        change (bitEncode x).length ≤ L at hx
        rw [FactorEncoding.length_bitEncode_nat] at hx ⊢
        exact (Nat.size_le_size (Nat.div_le_self _ _)).trans hx
      let acc := (delimit dw).reverse ++ ac
      have next := ih acc (x / d x) hquot (by simpa using (Nat.le_succ _).trans hf)
      have prepare := work_runs D (prepareRound input fu ac v hbits) d charge
      have query := doOracle D d charge x fu ac
      have receive := work_runs D (resumeRound dw input fu ac) d charge
      have divide := doDivision D hdiv d charge x (d x) fu acc
      have path := (((prepare.trans query).trans receive).trans divide).trans next
      have he : acc.reverse ++ bitEncode (factorList d fu.length (x / d x)) =
          ac.reverse ++ bitEncode (factorList d (v :: fu).length x) := by
        change acc.reverse ++ bitEncode (factorList d fu.length (x / d x)) =
          ac.reverse ++ bitEncode (if x < 2 then [] else d x :: factorList d fu.length (x / d x))
        rw [if_neg hsmall]
        change _ = ac.reverse ++ (delimit dw ++ bitEncode (factorList d fu.length (x / d x)))
        simp [acc, List.append_assoc]
      rw [he] at path
      apply path.mono
      change input.length ≤ L at hx
      have hcost : charge.eval input.length ≤ charge.eval L := eval_mono charge hx
      have hdcost : divTime.eval (input.length + dw.length) ≤ divTime.eval (L + size.eval L) :=
        eval_mono divTime (Nat.add_le_add hx hdlen)
      have hac : acc.length = 2*dw.length + 1 + ac.length := by simp [acc, length_delimit]
      simp only [List.length_cons, Nat.succ_mul]
      dsimp only [roundClock, input, dw] at *
      omega

private noncomputable def totalClock (charge divTime size : Polynomial ℕ) : Polynomial ℕ :=
  let X := (Polynomial.X : Polynomial ℕ)
  X * (charge + divTime.comp (X + size) + 2*X + 4*size + 8) + 3*X + 7

private theorem clock_eval (charge divTime size : Polynomial ℕ) (L : ℕ) :
    (totalClock charge divTime size).eval L =
      L * roundClock charge divTime size L + 3*L + 7 := by
  simp [totalClock, roundClock]

private theorem fuel_size (x : ℕ) : (encodeNat x).length - 1 = x.log2 := by
  by_cases h : x = 0
  · subst x; rfl
  · change (bitEncode x).length - 1 = _
    rw [FactorEncoding.length_bitEncode_nat]
    have hlo := Nat.lt_size.mpr (Nat.log2_self_le h)
    have hhi := Nat.size_le.mpr (Nat.lt_log2_self (n := x))
    omega

private theorem factorList_rec (d : ℕ → ℕ) (k : ℕ) :
    factorList d k = Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => [])
      (fun _ loop x => if x < 2 then [] else d x :: loop (x / d x)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext x
    simp only [factorList, ih]

theorem emission_polytime (d : ℕ → ℕ) (hd : ComplexityTheory.IsPolyTime d) :
    ComplexityTheory.IsPolyTime (fun n : ℕ =>
      (Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => [])
        (fun _ loop x => if x < 2 then [] else d x :: loop (x / d x)) n.log2) n) := by
  let D := FactorDivisionController.division
  let divTime := FactorDivisionTime.divisionClock
  obtain ⟨size, hsize⟩ := FactorMachineBound.polytime_output_bound hd
  apply FactorWordOracle.polytime_from_runs (driver D) d _ hd
  intro charge
  refine ⟨totalClock charge divTime size, ?_⟩
  intro n
  let w := encodeNat n
  let fu := List.replicate (w.length - 1) true
  have hh : fu.length ≤ w.length := by simp [fu]
  have hinit := work_runs D (startup w) d charge
  have hloop := emitRounds D divTime FactorDivisionTime.division_correct d charge size hsize
    w.length fu [] n le_rfl hh
  have path := hinit.trans hloop
  have hlen : fu.length = n.log2 := by simp [fu,w,fuel_size]
  rw [hlen] at path
  simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero] at path
  rw [factorList_rec] at path
  change Runs D d charge (initList (driver D).tm w) (haltList (driver D).tm _) _
  rw [initial, finalCfg]
  apply path.mono
  rw [clock_eval]
  change _ ≤ w.length * roundClock charge divTime size w.length + 3 * w.length + 7
  have hm := Nat.mul_le_mul_right (roundClock charge divTime size w.length) (hlen ▸ hh)
  omega

end FactorEmitMachine

theorem OMA.solution : OMA.R_PolyTime_isPolyTime_primeFactorsList_R1.H4 := by
  exact FactorEmitMachine.emission_polytime
