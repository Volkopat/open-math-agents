import OMAReductions.R_oeis_a203914_R1_H1_R1
import Mathlib

/-!
# A203914 R1.H1.R1.H3: P ⊆ NP
Credit: @my-other-github-account

A polynomial-time decider is a verifier that ignores the witness: the empty witness suffices, and a
finite-state transducer strips the self-delimited input from `delimit x ++ w`. The machine
composition library is adapted from OpenAI math commit 3344da59991e (Apache-2.0),
`OAI/Computability/MaxCut/{Model, Machines/Runtime, Machines/MachineCopy, Machines/MachineSequential}`.
-/

-- Model
section

namespace OAI

namespace MaxCutGames.BinaryFormula

structure Literal where
  name : Nat
  positive : Bool
  deriving DecidableEq

def Literal.eval (literal : Literal) (assignment : Nat → Bool) : Bool :=
  if literal.positive then assignment literal.name else !(assignment literal.name)

abbrev Clause := Vector Literal 3

def Clause.eval (clause : Clause) (assignment : Nat → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

/-- An ordinary conjunction of three-slot clauses with sparse variable names.
Repeated names and repeated literals are permitted in every clause. -/
structure Formula where
  clauses : List Clause

def Formula.Satisfiable (F : Formula) : Prop :=
  ∃ assignment : Nat → Bool, ∀ clause ∈ F.clauses, clause.eval assignment = true

end MaxCutGames.BinaryFormula

namespace MaxCutGames.BinaryEncoding

open BinaryFormula

def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bits => Nat.bit b (bitsValue bits)

/-- Prefix-free framing on the two-symbol input alphabet. -/
def frame : List Bool → List Bool
  | [] => [false]
  | b :: bits => true :: b :: frame bits

def parseFrame : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest => do
      let (bits, trailing) ← parseFrame rest
      return (b :: bits, trailing)
  | _ => none

def nameBits (name : Nat) : List Bool := frame name.bits

/-- Equality with the canonical digits rejects alternate padded encodings. -/
def parseName (input : List Bool) : Option (Nat × List Bool) := do
  let (digits, rest) ← parseFrame input
  let name := bitsValue digits
  if digits = name.bits then some (name, rest) else none

def parseLiteral : List Bool → Option (Literal × List Bool)
  | sign :: input => do
      let (name, rest) ← parseName input
      return (⟨name, sign⟩, rest)
  | [] => none

def parseClause (input : List Bool) : Option (Clause × List Bool) := do
  let (a, input) ← parseLiteral input
  let (b, input) ← parseLiteral input
  let (c, rest) ← parseLiteral input
  return (#v[a, b, c], rest)

/-- Fuel bounds the number of clause iterations, not the size of any name. -/
def parseClauses : Nat → List Bool → Option (List Clause × List Bool)
  | 0, _ => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: input => do
      let (clause, input) ← parseClause input
      let (clauses, rest) ← parseClauses fuel input
      return (clause :: clauses, rest)
  | _ + 1, [] => none

def decodeFormula (input : List Bool) : Option Formula := do
  let (clauses, rest) ← parseClauses (input.length + 1) input
  if rest = [] then some ⟨clauses⟩ else none

end MaxCutGames.BinaryEncoding

namespace OptimalMaxCut

open scoped BigOperators

/-- The exact Goemans–Williamson ratio, as an infimum over -1 ≤ ρ < 1. -/
noncomputable def alphaGW : ℝ :=
  sInf ((fun ρ : ℝ => 2 * Real.arccos ρ / (Real.pi * (1 - ρ))) ''
    Set.Ico (-1 : ℝ) 1)

/-- The ordinary binary 3SAT language, including rejection of malformed words. -/
def binary3SAT (input : List Bool) : Prop :=
  ∃ formula, MaxCutGames.BinaryEncoding.decodeFormula input = some formula ∧
    formula.Satisfiable

/-- A finite simple unweighted graph with its full Boolean adjacency table. -/
structure Graph where
  vertices : ℕ
  adj : Fin vertices → Fin vertices → Bool
  symmetric : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

/-- Each unordered distinct edge crossing the cut is counted exactly once. -/
def Graph.cutSize (G : Graph) (cut : Fin G.vertices → Bool) : ℕ :=
  ∑ u : Fin G.vertices, ∑ v : Fin G.vertices,
    if u < v ∧ G.adj u v = true ∧ cut u ≠ cut v then 1 else 0

/-- The maximum over all Boolean cuts of the finite vertex set. -/
def Graph.maxCut (G : Graph) : ℕ :=
  (Finset.univ.image G.cutSize).sup id

/-- The positive integer scale Q is part of the output. It need not equal the
number of graph edges. -/
structure ScaledGraph where
  graph : Graph
  scale : ℕ
  scale_pos : 0 < scale

/-- Canonical delimited binary vertex count and scale, followed by the full
adjacency table in lexicographic order. -/
def ScaledGraph.bits (G : ScaledGraph) : List Bool :=
  MaxCutGames.BinaryEncoding.nameBits G.graph.vertices ++
  MaxCutGames.BinaryEncoding.nameBits G.scale ++
  (List.finRange G.graph.vertices).flatMap (fun u =>
    (List.finRange G.graph.vertices).map (fun v => G.graph.adj u v))

/-- The rational gap bounds and the finite machine are fixed before the input.
The bounds compare the maximum cut divided by the positive output scale. -/
structure GapReduction (α : ℝ) where
  yesBound : ℚ
  noBound : ℚ
  yes_pos : 0 < yesBound
  no_nonneg : 0 ≤ noBound
  gap : (noBound : ℝ) < α * (yesBound : ℝ)
  construct : List Bool → ScaledGraph
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    ScaledGraph.bits construct
  finiteAlphabet : ∀ k, Finite (computation.tm.Γ k)
  completeness : ∀ input, binary3SAT input →
    (yesBound : ℝ) ≤ ((construct input).graph.maxCut : ℝ) / (construct input).scale
  soundness : ∀ input, ¬ binary3SAT input →
    ((construct input).graph.maxCut : ℝ) / (construct input).scale ≤ (noBound : ℝ)

def MainStatement : Prop :=
  ∀ α : ℝ, alphaGW < α → α ≤ 1 → Nonempty (GapReduction α)

end OptimalMaxCut

end OAI

end

-- Runtime
section


namespace OAI

/-!
Stack-length bounds derived from actual machine transitions. A finite program
has a maximum number of pushes in any one statement. Iterating its transitions
therefore bounds output length by input length plus that constant times elapsed
steps. This proves a consequence of a runtime certificate, not its converse.
-/

namespace MaxCutGames.Foundations.Complexity.Runtime

def statementPushBound {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Turing.TM2.Stmt Γ Λ σ → Nat
  | .push _ _ next => statementPushBound next + 1
  | .peek _ _ next => statementPushBound next
  | .pop _ _ next => statementPushBound next
  | .load _ next => statementPushBound next
  | .branch _ yes no => max (statementPushBound yes) (statementPushBound no)
  | .goto _ => 0
  | .halt => 0

def maxLabelPushes {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) : List Λ → Nat
  | [] => 0
  | label :: rest => max (statementPushBound (program label)) (maxLabelPushes program rest)

theorem maxLabelPushes_ge {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (labels : List Λ) (label : Λ)
    (member : label ∈ labels) :
    statementPushBound (program label) ≤ maxLabelPushes program labels := by
  induction labels with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

/-- The finite maximum is a proof-bound constant, not an operation of the
machine being analyzed. -/
noncomputable def programPushBound (tm : Turing.FinTM2) : Nat :=
  maxLabelPushes tm.m tm.ΛFin.elems.toList

theorem statement_le_programPushBound (tm : Turing.FinTM2) (label : tm.Λ) :
    statementPushBound (tm.m label) ≤ programPushBound tm := by
  apply maxLabelPushes_ge
  simpa using tm.ΛFin.complete label

theorem stepAuxStackLength {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
    (stmt : Turing.TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) (k : K) :
    ((Turing.TM2.stepAux stmt state tapes).stk k).length ≤
      (tapes k).length + statementPushBound stmt := by
  induction stmt generalizing state tapes with
  | push j f next ih =>
      have changed : ((Function.update tapes j (f state :: tapes j)) k).length ≤
          (tapes k).length + 1 := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih state (Function.update tapes j (f state :: tapes j))
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | peek j f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using
        ih (f state (tapes j).head?) tapes
  | pop j f next ih =>
      have changed : ((Function.update tapes j (tapes j).tail) k).length ≤
          (tapes k).length := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih (f state (tapes j).head?) (Function.update tapes j (tapes j).tail)
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | load f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using ih (f state) tapes
  | branch condition yes no ihYes ihNo =>
      cases decision : condition state with
      | false =>
          have h := ihNo state tapes
          have hm := Nat.le_max_right (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_false]
          omega
      | true =>
          have h := ihYes state tapes
          have hm := Nat.le_max_left (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_true]
          omega
  | goto f => simp [Turing.TM2.stepAux, statementPushBound]
  | halt => simp [Turing.TM2.stepAux, statementPushBound]

private theorem iterateSizeBound_inline_Runtime {α : Type} (f : α → α) (size : α → Nat) (C : Nat)
    (oneStep : ∀ x, size (f x) ≤ size x + C) (n : Nat) (x : α) :
    size ((f^[n]) x) ≤ size x + n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := oneStep ((f^[n]) x)
      have bound : size (f ((f^[n]) x)) ≤ size x + (n + 1) * C := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [Function.iterate_succ_apply'] using bound

/-- Resource growth along the actual iterated transition witness. -/
theorem executionSizeBound {σ : Type} (step : σ → Option σ) (size : σ → Nat) (C : Nat)
    (oneStep : ∀ a b, step a = some b → size b ≤ size a + C)
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime step start (some finish) budget) :
    size finish ≤ size start + budget * C := by
  let liftedSize : Option σ → Nat := fun state => (state.map size).getD 0
  have liftedStep : ∀ state : Option σ,
      liftedSize (state.bind step) ≤ liftedSize state + C := by
    intro state
    cases state with
    | none => simp [liftedSize]
    | some a =>
        cases transition : step a with
        | none => simp [liftedSize, transition]
        | some b => simpa [liftedSize, transition] using oneStep a b transition
  have bound := iterateSizeBound_inline_Runtime (fun state : Option σ => state.bind step)
    liftedSize C liftedStep execution.steps (some start)
  change liftedSize ((flip bind step)^[execution.steps] (some start)) ≤ _ at bound
  rw [execution.evals_in_steps] at bound
  simp only [liftedSize, Option.map_some, Option.getD_some] at bound
  exact Nat.le_trans bound (Nat.add_le_add_left
    (Nat.mul_le_mul_right C execution.steps_le_m) _)

theorem stepStackLength (tm : Turing.FinTM2) (k : tm.K) (a b : tm.Cfg)
    (transition : tm.step a = some b) :
    (b.stk k).length ≤ (a.stk k).length + programPushBound tm := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => simp [Turing.FinTM2.step, Turing.TM2.step] at transition
      | some label =>
          have result := Option.some.inj transition
          rw [← result]
          exact Nat.le_trans (stepAuxStackLength _ _ _ _)
            (Nat.add_le_add_left (statement_le_programPushBound tm label) _)

theorem initialStackLength (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((Turing.initList tm input).stk k).length ≤ input.length := by
  simp only [Turing.initList]
  split
  next same => subst k; exact Nat.le_refl _
  next _ => simp

@[simp] theorem haltedOutputLength (tm : Turing.FinTM2) (output : List (tm.Γ tm.k₁)) :
    ((Turing.haltList tm output).stk tm.k₁).length = output.length := by
  simp [Turing.haltList]

theorem outputLength_le (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (budget : Nat)
    (execution : Turing.TM2OutputsInTime tm input (some output) budget) :
    output.length ≤ input.length + budget * programPushBound tm := by
  have bound := executionSizeBound tm.step (fun cfg => (cfg.stk tm.k₁).length)
    (programPushBound tm) (stepStackLength tm tm.k₁) execution
  calc
    output.length = ((Turing.haltList tm output).stk tm.k₁).length := (haltedOutputLength tm output).symm
    _ ≤ ((Turing.initList tm input).stk tm.k₁).length + budget * programPushBound tm := bound
    _ ≤ input.length + budget * programPushBound tm :=
      Nat.add_le_add_right (initialStackLength tm input tm.k₁) _

/-- Polynomial-time computation implies a polynomial bound on serialized
output length. This direction is used for intermediate data in composition. -/
theorem encodedOutputLength {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (certificate : Turing.TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤
      (Polynomial.X + Polynomial.C (programPushBound certificate.tm) * certificate.time).eval
        (ea a).length := by
  have bound := outputLength_le certificate.tm _ _ _ (certificate.outputsFun a)
  simpa only [List.length_map, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Nat.mul_comm] using bound

end MaxCutGames.Foundations.Complexity.Runtime

/-! Exact embedding of a finite-stack program into disjoint stacks and labels.
An original halt can either halt or enter an explicit continuation label.
The simulation preserves all extra stacks and the second state component. -/

namespace MaxCutGames.Foundations.Complexity.MachineEmbedding

open Turing.TM2

variable {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}

abbrev Alphabet (Γ : K → Type) (Δ : E → Type) : K ⊕ E → Type
  | .inl k => Γ k
  | .inr e => Δ e

def tapes (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e)) :
    ∀ j, List (Alphabet Γ Δ j)
  | .inl k => source k
  | .inr e => extra e

@[simp] theorem tapes_inl (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (k : K) : tapes source extra (.inl k) = source k := rfl

@[simp] theorem tapes_inr (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (e : E) : tapes source extra (.inr e) = extra e := rfl

def label (haltTarget : Option (Λ ⊕ Λextra)) : Option Λ → Option (Λ ⊕ Λextra)
  | none => haltTarget
  | some l => some (.inl l)

def configuration (haltTarget : Option (Λ ⊕ Λextra)) (extraState : τ)
    (extraTapes : ∀ e, List (Δ e)) (c : Cfg Γ Λ σ) :
    Cfg (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ) where
  l := label haltTarget c.l
  var := (c.var, extraState)
  stk := tapes c.stk extraTapes

def statement (haltTarget : Option (Λ ⊕ Λextra)) :
    Stmt Γ Λ σ → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)
  | .push k f next => .push (.inl k) (fun st => f st.1) (statement haltTarget next)
  | .peek k f next => .peek (.inl k) (fun st v => (f st.1 v, st.2))
      (statement haltTarget next)
  | .pop k f next => .pop (.inl k) (fun st v => (f st.1 v, st.2))
      (statement haltTarget next)
  | .load f next => .load (fun st => (f st.1, st.2)) (statement haltTarget next)
  | .branch f yes no => .branch (fun st => f st.1)
      (statement haltTarget yes) (statement haltTarget no)
  | .goto f => .goto (fun st => .inl (f st.1))
  | .halt => match haltTarget with
      | none => .halt
      | some l => .goto (fun _ => l)

variable [DecidableEq K] [DecidableEq E]

theorem tapes_update (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (k : K) (value : List (Γ k)) :
    tapes (Function.update source k value) extra =
      Function.update (tapes source extra) (.inl k) value := by
  funext j
  cases j with
  | inl j =>
    by_cases h : j = k
    · subst j
      simp [Function.update]
    · simp [Function.update, h]
  | inr e => simp [Function.update]

/-- One finite statement executes identically on the original stacks and state.
The entire statement is simulated in exactly one TM2 transition. -/
theorem stepAux_simulation (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (q : Stmt Γ Λ σ) (state : σ) (source : ∀ k, List (Γ k)) :
    stepAux (statement haltTarget q) (state, extraState) (tapes source extraTapes) =
      configuration haltTarget extraState extraTapes (stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    simp only [statement, stepAux, tapes_inl]
    rw [← tapes_update]
    exact ih state (Function.update source k (f state :: source k))
  | peek k f next ih =>
    simpa only [statement, stepAux, tapes_inl] using
      ih (f state (source k).head?) source
  | pop k f next ih =>
    simp only [statement, stepAux, tapes_inl]
    rw [← tapes_update]
    exact ih (f state (source k).head?) (Function.update source k (source k).tail)
  | load f next ih =>
    simpa only [statement, stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => cases haltTarget <;> rfl

theorem stepAux_preserves_extra_state (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (q : Stmt Γ Λ σ) (state : σ) (source : ∀ k, List (Γ k)) :
    (stepAux (statement haltTarget q) (state, extraState)
      (tapes source extraTapes)).var.2 = extraState := by
  rw [stepAux_simulation]
  rfl

theorem stepAux_preserves_extra_tape (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (q : Stmt Γ Λ σ) (state : σ) (source : ∀ k, List (Γ k)) (e : E) :
    (stepAux (statement haltTarget q) (state, extraState)
      (tapes source extraTapes)).stk (.inr e) = extraTapes e := by
  rw [stepAux_simulation]
  rfl

def program (haltTarget : Option (Λ ⊕ Λextra)) (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)) :
    Λ ⊕ Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)
  | .inl l => statement haltTarget (source l)
  | .inr l => extra l

theorem step_running (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ))
    (l : Λ) (state : σ) (sourceTapes : ∀ k, List (Γ k)) :
    step (program haltTarget source extra)
      (configuration haltTarget extraState extraTapes ⟨some l, state, sourceTapes⟩) =
      some (configuration haltTarget extraState extraTapes
        (stepAux (source l) state sourceTapes)) := by
  change some (stepAux (statement haltTarget (source l)) (state, extraState)
    (tapes sourceTapes extraTapes)) = _
  rw [stepAux_simulation]

theorem step_simulation (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ))
    (a b : Cfg Γ Λ σ) (h : step source a = some b) :
    step (program haltTarget source extra)
      (configuration haltTarget extraState extraTapes a) =
      some (configuration haltTarget extraState extraTapes b) := by
  cases a with
  | mk l state sourceTapes =>
    cases l with
    | none => simp [step] at h
    | some l =>
      have hb : stepAux (source l) state sourceTapes = b := Option.some.inj h
      rw [← hb]
      exact step_running haltTarget extraState extraTapes source extra l state sourceTapes

end MaxCutGames.Foundations.Complexity.MachineEmbedding

/-!
Execution transport and polynomial budget arithmetic for genuine TM2 sequential
composition. These lemmas preserve actual transition witnesses. The four-phase
lemma requires all phases to be executions of the same combined program; it is
not a replacement for constructing that program and proving its tape handoffs.
-/

namespace MaxCutGames.Foundations.Complexity.MachineComposition

def advance {σ : Type} (step : σ → Option σ) (state : Option σ) : Option σ :=
  state.bind step

@[simp] theorem advance_none {σ : Type} (step : σ → Option σ) :
    advance step none = none := rfl

@[simp] theorem advance_some {σ : Type} (step : σ → Option σ) (state : σ) :
    advance step (some state) = step state := rfl

@[simp] theorem advance_iterate_none {σ : Type} (step : σ → Option σ) (n : Nat) :
    (advance step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, advance_none]

theorem liftSuccessfulTrace {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    (n : Nat) (start finish : σ)
    (trace : (advance source)^[n] (some start) = some finish) :
    (advance target)^[n] (some (embed start)) = some (embed finish) := by
  induction n generalizing start with
  | zero =>
      have same := Option.some.inj trace
      cases same
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at trace ⊢
      change (advance source)^[n] (source start) = some finish at trace
      change (advance target)^[n] (target (embed start)) = some (embed finish)
      cases firstStep : source start with
      | none =>
          rw [firstStep, advance_iterate_none] at trace
          contradiction
      | some intermediate =>
          rw [firstStep] at trace
          rw [simulation start intermediate firstStep]
          exact ih intermediate trace

def liftExecutionInTime {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    StateTransition.EvalsToInTime target (embed start) (some (embed finish)) budget where
  steps := execution.steps
  evals_in_steps := by
    have sourceTrace := execution.evals_in_steps
    change (advance source)^[execution.steps] (some start) = some finish at sourceTrace
    change (advance target)^[execution.steps] (some (embed start)) = some (embed finish)
    exact liftSuccessfulTrace source target embed simulation execution.steps start finish sourceTrace
  steps_le_m := execution.steps_le_m

@[simp] theorem liftExecutionInTime_steps {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    (liftExecutionInTime source target embed simulation execution).steps = execution.steps := rfl

/-- The checked disjoint-stack embedding transports a complete successful run
with no additional transitions, including its final jump to a bridge label. -/
def embeddedExecution {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}
    [DecidableEq K] [DecidableEq E]
    (haltTarget : Option (Λ ⊕ Λextra)) (extraState : τ)
    (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Turing.TM2.Stmt Γ Λ σ)
    (extra : Λextra → Turing.TM2.Stmt (MachineEmbedding.Alphabet Γ Δ)
      (Λ ⊕ Λextra) (σ × τ))
    {start finish : Turing.TM2.Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (Turing.TM2.step source)
      start (some finish) budget) :
    StateTransition.EvalsToInTime (Turing.TM2.step (MachineEmbedding.program haltTarget source extra))
      (MachineEmbedding.configuration haltTarget extraState extraTapes start)
      (some (MachineEmbedding.configuration haltTarget extraState extraTapes finish)) budget :=
  liftExecutionInTime (Turing.TM2.step source)
    (Turing.TM2.step (MachineEmbedding.program haltTarget source extra))
    (MachineEmbedding.configuration haltTarget extraState extraTapes)
    (MachineEmbedding.step_simulation haltTarget extraState extraTapes source extra) execution

theorem natPolynomial_eval_mono (p : Polynomial Nat) {a b : Nat} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial degree coefficient =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left h degree)

/-- Two reversal transfers each consume `intermediateLength + 1` transitions. -/
noncomputable def compositionPolynomial (first second intermediate : Polynomial Nat) : Polynomial Nat :=
  first + Polynomial.C 2 * (intermediate + 1) + second.comp intermediate

theorem compositionBudget_le (first second intermediate : Polynomial Nat)
    (inputLength intermediateLength : Nat)
    (intermediateBound : intermediateLength ≤ intermediate.eval inputLength) :
    first.eval inputLength + 2 * (intermediateLength + 1) + second.eval intermediateLength ≤
      (compositionPolynomial first second intermediate).eval inputLength := by
  have secondBound := natPolynomial_eval_mono second intermediateBound
  have transferBound := Nat.mul_le_mul_left 2 (Nat.add_le_add_right intermediateBound 1)
  simp only [compositionPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_comp]
  omega

def fourPhaseExecution {σ : Type} (step : σ → Option σ)
    (start afterFirst afterTransfer₁ afterTransfer₂ : σ) (finish : Option σ)
    (first second intermediate : Polynomial Nat) (inputLength intermediateLength : Nat)
    (intermediateBound : intermediateLength ≤ intermediate.eval inputLength)
    (runFirst : StateTransition.EvalsToInTime step start (some afterFirst) (first.eval inputLength))
    (transfer₁ : StateTransition.EvalsToInTime step afterFirst (some afterTransfer₁)
      (intermediateLength + 1))
    (transfer₂ : StateTransition.EvalsToInTime step afterTransfer₁ (some afterTransfer₂)
      (intermediateLength + 1))
    (runSecond : StateTransition.EvalsToInTime step afterTransfer₂ finish
      (second.eval intermediateLength)) :
    StateTransition.EvalsToInTime step start finish
      ((compositionPolynomial first second intermediate).eval inputLength) := by
  let firstTwo := StateTransition.EvalsToInTime.trans step _ _ start afterFirst
    (some afterTransfer₁) runFirst transfer₁
  let firstThree := StateTransition.EvalsToInTime.trans step _ _ start afterTransfer₁
    (some afterTransfer₂) firstTwo transfer₂
  let allFour := StateTransition.EvalsToInTime.trans step _ _ start afterTransfer₂
    finish firstThree runSecond
  refine {
    toEvalsTo := allFour.toEvalsTo
    steps_le_m := Nat.le_trans allFour.steps_le_m ?_
  }
  have bounded := compositionBudget_le first second intermediate inputLength intermediateLength
    intermediateBound
  omega

end MaxCutGames.Foundations.Complexity.MachineComposition

/-!
# Certified reversal and relabeling between finite alphabets

The actual TM2 machine transfers a list over a finite alphabet `α` to a second
stack over `β`, reverses its order, and applies a fixed map `f : α → β` to each
symbol. The trace has exactly `input.length + 1` transitions. An explicit
fallback symbol makes the push expression total, including the unused branch
where the internal register is empty.

This primitive supports machine composition when intermediate stack alphabets
differ. It does not yet implement the Unique Games reduction.
-/

namespace MaxCutGames.Reduction.MachineTransfer

open Turing

abbrev alphabet (α β : Type) : Bool → Type
  | false => α
  | true => β

variable {α β : Type} [Fintype α] [Fintype β]

def loop (f : α → β) (fallback : β) :
    TM2.Stmt (alphabet α β) Unit (Option β) :=
  .pop false (fun _ head => head.map f)
    (.branch Option.isSome
      (.push true (fun state => state.getD fallback) (.goto fun _ => ()))
      .halt)

def machine (f : α → β) (fallback : β) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := alphabet α β
  Λ := Unit
  main := ()
  σ := Option β
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype α)
  m _ := loop f fallback

def tapeStacks (input : List α) (output : List β) :
    (side : Bool) → List (alphabet α β side)
  | false => input
  | true => output

def running (f : α → β) (fallback : β) (input : List α) (output : List β)
    (state : Option β) : (machine f fallback).Cfg :=
  ⟨some (), state, tapeStacks input output⟩

def halted (f : α → β) (fallback : β) (output : List β) : (machine f fallback).Cfg :=
  ⟨none, none, tapeStacks (α := α) [] output⟩

omit [Fintype α] [Fintype β] in
private theorem update_input_inline_MachineTransfer (input replacement : List α) (output : List β) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> rfl

omit [Fintype α] [Fintype β] in
private theorem update_output_inline_MachineTransfer (input : List α) (output replacement : List β) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> rfl

theorem step_empty (f : α → β) (fallback : β) (output : List β) (state : Option β) :
    (machine f fallback).step (running f fallback [] output state) =
      some (halted f fallback output) := by
  change some (TM2.stepAux (loop f fallback) state (tapeStacks (α := α) [] output)) = _
  simp [loop, TM2.stepAux, tapeStacks, halted, Function.update]
  rw [update_input_inline_MachineTransfer]
  rfl

theorem step_cons (f : α → β) (fallback : β) (head : α) (input : List α)
    (output : List β) (state : Option β) :
    (machine f fallback).step (running f fallback (head :: input) output state) =
      some (running f fallback input (f head :: output) (some (f head))) := by
  change some (TM2.stepAux (loop f fallback) state (tapeStacks (head :: input) output)) = _
  simp [loop, TM2.stepAux, tapeStacks, running, Function.update]
  rw [update_input_inline_MachineTransfer, update_output_inline_MachineTransfer]
  rfl

def next (f : α → β) (fallback : β) (configuration : Option (machine f fallback).Cfg) :
    Option (machine f fallback).Cfg := configuration.bind (machine f fallback).step

/-- Exact actual-machine trace, for any accumulator and internal register. -/
theorem transfer_steps (f : α → β) (fallback : β) (input : List α) (output : List β)
    (state : Option β) :
    (next f fallback)^[input.length + 1] (some (running f fallback input output state)) =
      some (halted f fallback (input.reverse.map f ++ output)) := by
  induction input generalizing output state with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, List.reverse_nil, List.map_nil, List.nil_append]
      using step_empty f fallback output state
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (next f fallback)^[input.length + 1]
      ((machine f fallback).step (running f fallback (head :: input) output state)) = _
    rw [step_cons, ih]
    simp only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append]

theorem initList_eq (f : α → β) (fallback : β) (input : List α) :
    initList (machine f fallback) input = running f fallback input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (f : α → β) (fallback : β) (output : List β) :
    haltList (machine f fallback) output = halted f fallback output := by
  unfold haltList halted
  congr 1
  funext side
  cases side <;> rfl

theorem transfer_init_steps (f : α → β) (fallback : β) (input : List α) :
    (next f fallback)^[input.length + 1] (some (initList (machine f fallback) input)) =
      some (haltList (machine f fallback) (input.reverse.map f)) := by
  erw [initList_eq, haltList_eq]
  simpa only [List.append_nil] using! transfer_steps f fallback input [] none

def outputsInTime (f : α → β) (fallback : β) (input : List α) :
    TM2OutputsInTime (machine f fallback) input (some (input.reverse.map f))
      (input.length + 1) where
  steps := input.length + 1
  evals_in_steps := transfer_init_steps f fallback input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (f : α → β) (fallback : β) (input : List α) :
    (outputsInTime f fallback input).steps = input.length + 1 := rfl

/-- A genuine finite-machine certificate with identity encodings and bound `X+1`. -/
noncomputable def computableInPolyTime (f : α → β) (fallback : β) :
    TM2ComputableInPolyTime (id : List α → List α) (id : List β → List β)
      (fun input => input.reverse.map f) where
  tm := machine f fallback
  inputAlphabet := Equiv.refl α
  outputAlphabet := Equiv.refl β
  time := Polynomial.X + 1
  outputsFun input := by
    change TM2OutputsInTime (machine f fallback) (input.map id)
      (some ((input.reverse.map f).map id))
      ((Polynomial.X + 1 : Polynomial Nat).eval input.length)
    have hi := @List.map_id ((machine f fallback).Γ (machine f fallback).k₀) input
    have ho := @List.map_id ((machine f fallback).Γ (machine f fallback).k₁) (input.reverse.map f)
    erw [hi, ho]
    simpa only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      using outputsInTime f fallback input

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

def exitAt (dst : K) (exit : Option Λ) : TM2.Stmt Γ Λ (σ × Option (Γ dst)) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def loopAt (src dst : K) (f : Γ src → Γ dst) (fallback : Γ dst)
    (loopLabel : Λ) (exit : Option Λ) : TM2.Stmt Γ Λ (σ × Option (Γ dst)) :=
  .pop src (fun state head => (state.1, head.map f))
    (.branch (fun state => state.2.isSome)
      (.push dst (fun state => state.2.getD fallback) (.goto fun _ => loopLabel))
      (exitAt dst exit))

def tapesAt (src dst : K) (base : (k : K) → List (Γ k))
    (input : List (Γ src)) (output : List (Γ dst)) : (k : K) → List (Γ k) :=
  Function.update (Function.update base src input) dst output

@[simp] theorem tapesAt_src (src dst : K) (distinct : src ≠ dst)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst)) :
    tapesAt src dst base input output src = input := by
  simp [tapesAt, distinct]

@[simp] theorem tapesAt_dst (src dst : K)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst)) :
    tapesAt src dst base input output dst = output := by
  simp [tapesAt]

theorem tapesAt_other (src dst k : K) (notSrc : k ≠ src) (notDst : k ≠ dst)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst)) :
    tapesAt src dst base input output k = base k := by
  simp [tapesAt, notSrc, notDst]

@[simp] theorem tapesAt_self (src dst : K) (base : (k : K) → List (Γ k)) :
    tapesAt src dst base (base src) (base dst) = base := by
  simp [tapesAt]

private theorem update_tapesAt_src_inline_MachineTransfer (src dst : K) (distinct : src ≠ dst)
    (base : (k : K) → List (Γ k)) (input replacement : List (Γ src))
    (output : List (Γ dst)) :
    Function.update (tapesAt src dst base input output) src replacement =
      tapesAt src dst base replacement output := by
  funext k
  by_cases hs : k = src
  · subst k
    simp [tapesAt, distinct]
  · by_cases hd : k = dst
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

private theorem update_tapesAt_dst_inline_MachineTransfer (src dst : K)
    (base : (k : K) → List (Γ k)) (input : List (Γ src))
    (output replacement : List (Γ dst)) :
    Function.update (tapesAt src dst base input output) dst replacement =
      tapesAt src dst base input replacement := by
  funext k
  by_cases hd : k = dst
  · subst k
    simp [tapesAt]
  · simp [tapesAt, hd]

def nextAt (dst : K) (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (configuration : Option (TM2.Cfg Γ Λ (σ × Option (Γ dst)))) :
    Option (TM2.Cfg Γ Λ (σ × Option (Γ dst))) :=
  configuration.bind (TM2.step program)

theorem stepAt_empty (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (output : List (Γ dst))
    (ambient : σ) (register : Option (Γ dst)) :
    TM2.step program ⟨some loopLabel, (ambient, register), tapesAt src dst base [] output⟩ =
      some ⟨exit, (ambient, none), tapesAt src dst base [] output⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (tapesAt src dst base [] output)) = _
  rw [atLoop]
  cases exit <;>
    simp [loopAt, exitAt, TM2.stepAux, tapesAt_src, distinct, update_tapesAt_src_inline_MachineTransfer]

theorem stepAt_cons (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (head : Γ src) (input : List (Γ src))
    (output : List (Γ dst)) (ambient : σ) (register : Option (Γ dst)) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), tapesAt src dst base (head :: input) output⟩ =
      some ⟨some loopLabel, (ambient, some (f head)),
        tapesAt src dst base input (f head :: output)⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (tapesAt src dst base (head :: input) output)) = _
  rw [atLoop]
  simp [loopAt, TM2.stepAux, tapesAt_src, tapesAt_dst, distinct,
    update_tapesAt_src_inline_MachineTransfer, update_tapesAt_dst_inline_MachineTransfer]

/-- Placement-aware exact transfer, preserving all ambient state and other tapes.
The optional exit label is reached in the same final empty-pop transition. -/
theorem transferAt_steps (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst))
    (ambient : σ) (register : Option (Γ dst)) :
    (nextAt dst program)^[input.length + 1]
      (some ⟨some loopLabel, (ambient, register), tapesAt src dst base input output⟩) =
      some ⟨exit, (ambient, none), tapesAt src dst base [] (input.reverse.map f ++ output)⟩ := by
  induction input generalizing output register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, nextAt,
      Option.bind_some, List.reverse_nil, List.map_nil, List.nil_append]
      using stepAt_empty src dst distinct f fallback loopLabel exit program atLoop base output
        ambient register
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (nextAt dst program)^[input.length + 1]
      (TM2.step program
        ⟨some loopLabel, (ambient, register), tapesAt src dst base (head :: input) output⟩) = _
    rw [stepAt_cons src dst distinct f fallback loopLabel exit program atLoop, ih]
    simp only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append]

/-- The same trace starting with an arbitrary actual ambient tape family. -/
theorem transferAt_fromTapes (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (ambient : σ) (register : Option (Γ dst)) :
    (nextAt dst program)^[(base src).length + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        tapesAt src dst base [] ((base src).reverse.map f ++ base dst)⟩ := by
  simpa only [tapesAt_self] using
    transferAt_steps src dst distinct f fallback loopLabel exit program atLoop base
      (base src) (base dst) ambient register

/-- A timed execution witness suitable for composing this bridge with other
phases of the same actual transition system. -/
def transferAtInTime (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (ambient : σ) (register : Option (Γ dst)) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        tapesAt src dst base [] ((base src).reverse.map f ++ base dst)⟩)
      ((base src).length + 1) where
  steps := (base src).length + 1
  evals_in_steps := transferAt_fromTapes src dst distinct f fallback loopLabel exit
    program atLoop base ambient register
  steps_le_m := Nat.le_refl _

end MaxCutGames.Reduction.MachineTransfer

end OAI

end

-- MachineCopy
section


namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineCopy

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

abbrev Alphabet (β : Type) (_ : K) := β

/-- Drain one tape into two reverse-order accumulators. -/
def forkLoop (source left right : K) (fallback : β) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push left (fun state => state.2.getD fallback)
        (.push right (fun state => state.2.getD fallback) (.goto fun _ => loopLabel)))
      (Reduction.MachineTransfer.exitAt right exit))

def forkTapes (source left right : K) (base : K → List β)
    (input leftOutput rightOutput : List β) : K → List β :=
  Function.update (Function.update (Function.update base source input) left leftOutput)
    right rightOutput

@[simp] theorem forkTapes_source (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right)
    (base : K → List β) (input leftOutput rightOutput : List β) :
    forkTapes source left right base input leftOutput rightOutput source = input := by
  simp [forkTapes, sourceLeft, sourceRight]

@[simp] theorem forkTapes_left (source left right : K) (leftRight : left ≠ right)
    (base : K → List β) (input leftOutput rightOutput : List β) :
    forkTapes source left right base input leftOutput rightOutput left = leftOutput := by
  simp [forkTapes, leftRight]

@[simp] theorem forkTapes_right (source left right : K)
    (base : K → List β) (input leftOutput rightOutput : List β) :
    forkTapes source left right base input leftOutput rightOutput right = rightOutput := by
  simp [forkTapes]

@[simp] theorem forkTapes_self (source left right : K) (base : K → List β) :
    forkTapes source left right base (base source) (base left) (base right) = base := by
  simp [forkTapes]

private theorem update_fork_source_inline_MachineCopy (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (base : K → List β) (input leftOutput rightOutput replacement : List β) :
    Function.update (forkTapes source left right base input leftOutput rightOutput)
      source replacement = forkTapes source left right base replacement leftOutput rightOutput := by
  funext k
  by_cases hs : k = source
  · subst k; simp [forkTapes, sourceLeft, sourceRight]
  · by_cases hl : k = left
    · subst k; simp [forkTapes, Ne.symm sourceLeft, leftRight]
    · by_cases hr : k = right
      · subst k; simp [forkTapes, Ne.symm sourceRight]
      · simp [forkTapes, hs, hl, hr]

private theorem update_fork_left_inline_MachineCopy (source left right : K) (leftRight : left ≠ right)
    (base : K → List β) (input leftOutput rightOutput replacement : List β) :
    Function.update (forkTapes source left right base input leftOutput rightOutput)
      left replacement = forkTapes source left right base input replacement rightOutput := by
  funext k
  by_cases hl : k = left
  · subst k; simp [forkTapes, leftRight]
  · by_cases hr : k = right
    · subst k; simp [forkTapes, Ne.symm leftRight]
    · simp [forkTapes, hl, hr]

private theorem update_fork_right_inline_MachineCopy (source left right : K)
    (base : K → List β) (input leftOutput rightOutput replacement : List β) :
    Function.update (forkTapes source left right base input leftOutput rightOutput)
      right replacement = forkTapes source left right base input leftOutput replacement := by
  simp [forkTapes]

theorem forkStep_empty (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (leftOutput rightOutput : List β) (ambient : σ) (register : Option β) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), forkTapes source left right base [] leftOutput rightOutput⟩ =
        some ⟨exit, (ambient, none), forkTapes source left right base [] leftOutput rightOutput⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (forkTapes source left right base [] leftOutput rightOutput)) = _
  rw [atLoop]
  cases exit <;>
    simp [forkLoop, Reduction.MachineTransfer.exitAt, TM2.stepAux, sourceLeft, sourceRight,
      leftRight, update_fork_source_inline_MachineCopy]

theorem forkStep_cons (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (head : β) (input leftOutput rightOutput : List β)
    (ambient : σ) (register : Option β) :
    TM2.step program
      ⟨some loopLabel, (ambient, register),
        forkTapes source left right base (head :: input) leftOutput rightOutput⟩ =
      some ⟨some loopLabel, (ambient, some head),
        forkTapes source left right base input (head :: leftOutput) (head :: rightOutput)⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (forkTapes source left right base (head :: input) leftOutput rightOutput)) = _
  rw [atLoop]
  simp [forkLoop, TM2.stepAux, sourceLeft, sourceRight, leftRight,
    update_fork_source_inline_MachineCopy, update_fork_left_inline_MachineCopy, update_fork_right_inline_MachineCopy]

/-- Each symbol and the final empty test take one actual transition. -/
theorem forkTrace (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (input leftOutput rightOutput : List β)
    (ambient : σ) (register : Option β) :
    (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (some ⟨some loopLabel, (ambient, register),
        forkTapes source left right base input leftOutput rightOutput⟩) =
      some ⟨exit, (ambient, none), forkTapes source left right base []
        (input.reverse ++ leftOutput) (input.reverse ++ rightOutput)⟩ := by
  induction input generalizing leftOutput rightOutput register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, List.reverse_nil, List.nil_append] using
        forkStep_empty source left right sourceLeft sourceRight leftRight fallback loopLabel exit
          program atLoop base leftOutput rightOutput ambient register
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        forkTapes source left right base (head :: input) leftOutput rightOutput⟩) = _
    rw [forkStep_cons source left right sourceLeft sourceRight leftRight fallback loopLabel exit
      program atLoop base head input leftOutput rightOutput ambient register, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

def forkInTime (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (ambient : σ) (register : Option β) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), forkTapes source left right base []
        ((base source).reverse ++ base left) ((base source).reverse ++ base right)⟩)
      ((base source).length + 1) where
  steps := (base source).length + 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[(base source).length + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) = _
    simpa only [forkTapes_self] using
      forkTrace source left right sourceLeft sourceRight leftRight fallback loopLabel exit
        program atLoop base (base source) (base left) (base right) ambient register
  steps_le_m := Nat.le_refl _

def drainedTapes (source scratch : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt source scratch base [] (base source).reverse

theorem restoredTapes (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (base : K → List β)
    (scratchEmpty : base scratch = []) :
    forkTapes scratch source destination (drainedTapes source scratch base) []
      (base source) (base source ++ base destination) =
        Function.update base destination (base source ++ base destination) := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [forkTapes, sourceDestination]
  · by_cases hd : k = destination
    · subst k; simp [forkTapes]
    · by_cases ht : k = scratch
      · subst k
        simp [forkTapes, Ne.symm sourceScratch, Ne.symm destinationScratch, scratchEmpty]
      · simp [forkTapes, drainedTapes, Reduction.MachineTransfer.tapesAt, hs, hd, ht]

theorem copyTrace (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (fallback : β) (firstLabel secondLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id fallback firstLabel (some secondLabel))
    (atSecond : program secondLabel = forkLoop scratch source destination fallback secondLabel exit)
    (base : K → List β) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option β) :
    (MachineComposition.advance (TM2.step program))^[2 * ((base source).length + 1)]
      (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base destination (base source ++ base destination)⟩ := by
  have first := Reduction.MachineTransfer.transferAt_fromTapes source scratch sourceScratch
    id fallback firstLabel (some secondLabel) program atFirst base ambient register
  change (MachineComposition.advance (TM2.step program))^[(base source).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) = _ at first
  simp only [List.map_id, scratchEmpty, List.append_nil] at first
  have second := forkTrace scratch source destination (Ne.symm sourceScratch)
    (Ne.symm destinationScratch) sourceDestination fallback secondLabel exit program atSecond
    (drainedTapes source scratch base)
    (drainedTapes source scratch base scratch) (drainedTapes source scratch base source)
    (drainedTapes source scratch base destination) ambient none
  simp only [forkTapes_self] at second
  have scratchWord : drainedTapes source scratch base scratch = (base source).reverse := by
    simp [drainedTapes]
  have sourceWord : drainedTapes source scratch base source = [] := by
    simp [drainedTapes, sourceScratch]
  have destinationWord : drainedTapes source scratch base destination = base destination := by
    simp [drainedTapes, Reduction.MachineTransfer.tapesAt, Ne.symm sourceDestination,
      destinationScratch]
  rw [scratchWord, sourceWord, destinationWord] at second
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at second
  rw [restoredTapes source destination scratch sourceDestination sourceScratch destinationScratch
    base scratchEmpty] at second
  rw [show 2 * ((base source).length + 1) =
    ((base source).length + 1) + ((base source).length + 1) by omega,
    Function.iterate_add_apply, first]
  exact second

/-- A timed witness whose stored step count is the exact two-loop trace length. -/
def copyInTime (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (fallback : β) (firstLabel secondLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id fallback firstLabel (some secondLabel))
    (atSecond : program secondLabel = forkLoop scratch source destination fallback secondLabel exit)
    (base : K → List β) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option β) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        Function.update base destination (base source ++ base destination)⟩)
      (2 * ((base source).length + 1)) where
  steps := 2 * ((base source).length + 1)
  evals_in_steps := copyTrace source destination scratch sourceDestination sourceScratch
    destinationScratch fallback firstLabel secondLabel exit program atFirst atSecond base
    scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

end MaxCutGames.Foundations.Complexity.MachineCopy

/-!
# A certified machine for fixed symbol substitution

For a fixed table `emit : Bool → List Bool`, this actual finite TM2 machine
produces `(input.flatMap emit).reverse` in exactly `2 * input.length + 1`
transitions. It has one input-pop transition and one literal-emission transition
per input symbol, followed by the final empty pop. Literal emission is a fixed
finite statement; its maximum number of pushes depends only on `emit`.

This is a machine primitive, not a runtime theorem for the Unique Games reduction.
-/

namespace MaxCutGames.Reduction.MachineSubstitution

open Turing

open MaxCutGames.Foundations.Complexity

section PushWord

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

/-- Push a fixed word in its listed order, then execute the continuation. -/
def pushWord (dst : K) : List (Γ dst) → TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ σ
  | [], continuation => continuation
  | symbol :: word, continuation =>
      .push dst (fun _ => symbol) (pushWord dst word continuation)

/-- Literal pushes preserve the state and every other tape. -/
theorem stepAux_pushWord (dst : K) (word : List (Γ dst))
    (continuation : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (pushWord dst word continuation) state tapes =
      TM2.stepAux continuation state
        (Function.update tapes dst (word.reverse ++ tapes dst)) := by
  induction word generalizing tapes with
  | nil => simp [pushWord]
  | cons symbol word ih =>
    simp only [pushWord, TM2.stepAux]
    rw [ih]
    simp only [Function.update_self, Function.update_idem, List.reverse_cons,
      List.append_assoc, List.singleton_append]

omit [DecidableEq K] in
theorem statementPushBound_pushWord (dst : K) (word : List (Γ dst))
    (continuation : TM2.Stmt Γ Λ σ) :
    Runtime.statementPushBound (pushWord dst word continuation) =
      word.length + Runtime.statementPushBound continuation := by
  induction word with
  | nil => simp [pushWord]
  | cons symbol word ih =>
    simp only [pushWord, Runtime.statementPushBound, ih, List.length_cons]
    omega

end PushWord

def loop : TM2.Stmt (fun _ : Bool => Bool) (Option Bool) (Option Bool) :=
  .pop false (fun _ head => head)
    (.branch Option.isSome
      (.goto fun state => some (state.getD false))
      .halt)

def program (emit : Bool → List Bool) :
    Option Bool → TM2.Stmt (fun _ : Bool => Bool) (Option Bool) (Option Bool)
  | none => loop
  | some symbol => pushWord true (emit symbol) (.goto fun _ => none)

def machine (emit : Bool → List Bool) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Option Bool
  main := none
  σ := Option Bool
  initialState := none
  m := program emit

/-- The fixed maximum word length bounds pushes in each emitted statement. -/
def maxEmission (emit : Bool → List Bool) : Nat :=
  max (emit false).length (emit true).length

theorem statementPushBound_le (emit : Bool → List Bool) (label : Option Bool) :
    Runtime.statementPushBound (program emit label) ≤ maxEmission emit := by
  cases label with
  | none => simp [program, loop, Runtime.statementPushBound]
  | some symbol =>
    simp only [program, statementPushBound_pushWord, Runtime.statementPushBound, Nat.add_zero]
    cases symbol
    · exact Nat.le_max_left _ _
    · exact Nat.le_max_right _ _

theorem programPushBound_le (emit : Bool → List Bool) :
    Runtime.programPushBound (machine emit) ≤ maxEmission emit := by
  have allLabels (labels : List (Option Bool)) :
      Runtime.maxLabelPushes (program emit) labels ≤ maxEmission emit := by
    induction labels with
    | nil => exact Nat.zero_le _
    | cons label rest ih =>
      exact max_le (statementPushBound_le emit label) ih
  exact allLabels (machine emit).ΛFin.elems.toList

def tapeStacks (input output : List Bool) : Bool → List Bool :=
  fun side => if side then output else input

def running (emit : Bool → List Bool) (input output : List Bool) (state : Option Bool) :
    (machine emit).Cfg :=
  ⟨some none, state, tapeStacks input output⟩

def emitting (emit : Bool → List Bool) (symbol : Bool)
    (input output : List Bool) (state : Option Bool) : (machine emit).Cfg :=
  ⟨some (some symbol), state, tapeStacks input output⟩

def halted (emit : Bool → List Bool) (output : List Bool) : (machine emit).Cfg :=
  ⟨none, none, tapeStacks [] output⟩

private theorem update_input_inline_MachineSubstitution (input output replacement : List Bool) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> simp [tapeStacks]

private theorem update_output_inline_MachineSubstitution (input output replacement : List Bool) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> simp [tapeStacks]

theorem step_empty (emit : Bool → List Bool) (output : List Bool) (state : Option Bool) :
    (machine emit).step (running emit [] output state) = some (halted emit output) := by
  change some (TM2.stepAux loop state (tapeStacks [] output)) = some (halted emit output)
  simp [loop, TM2.stepAux, tapeStacks, halted]
  rw [update_input_inline_MachineSubstitution]
  rfl

theorem step_cons (emit : Bool → List Bool) (symbol : Bool)
    (input output : List Bool) (state : Option Bool) :
    (machine emit).step (running emit (symbol :: input) output state) =
      some (emitting emit symbol input output (some symbol)) := by
  change some (TM2.stepAux loop state (tapeStacks (symbol :: input) output)) = _
  simp [loop, TM2.stepAux, tapeStacks, emitting]
  rw [update_input_inline_MachineSubstitution]
  rfl

/-- Emission does not depend on the register; the symbol is held in the control label. -/
theorem step_emit (emit : Bool → List Bool) (symbol : Bool)
    (input output : List Bool) (state : Option Bool) :
    (machine emit).step (emitting emit symbol input output state) =
      some (running emit input ((emit symbol).reverse ++ output) state) := by
  change some (TM2.stepAux (pushWord true (emit symbol) (.goto fun _ => none))
    state (tapeStacks input output)) = _
  rw [stepAux_pushWord]
  simp only [TM2.stepAux]
  change some (⟨some none, state,
    Function.update (tapeStacks input output) true ((emit symbol).reverse ++ output)⟩ :
    (machine emit).Cfg) = _
  erw [update_output_inline_MachineSubstitution]
  rfl

def next (emit : Bool → List Bool) (configuration : Option (machine emit).Cfg) :
    Option (machine emit).Cfg :=
  configuration.bind (machine emit).step

theorem two_steps_cons (emit : Bool → List Bool) (symbol : Bool)
    (input output : List Bool) (state : Option Bool) :
    (next emit)^[2] (some (running emit (symbol :: input) output state)) =
      some (running emit input ((emit symbol).reverse ++ output) (some symbol)) := by
  change (machine emit).step (running emit (symbol :: input) output state) >>=
    (machine emit).step = _
  rw [step_cons]
  exact step_emit emit symbol input output (some symbol)

/-- Exact execution, including an arbitrary initial accumulator and register. -/
theorem substitution_steps (emit : Bool → List Bool)
    (input output : List Bool) (state : Option Bool) :
    (next emit)^[2 * input.length + 1] (some (running emit input output state)) =
      some (halted emit ((input.flatMap emit).reverse ++ output)) := by
  induction input generalizing output state with
  | nil =>
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, List.flatMap_nil, List.reverse_nil, List.nil_append]
      using step_empty emit output state
  | cons symbol input ih =>
    rw [List.length_cons]
    rw [show 2 * (input.length + 1) + 1 = (2 * input.length + 1) + 2 by omega]
    rw [Function.iterate_add_apply, two_steps_cons, ih]
    simp only [List.flatMap_cons, List.reverse_append, List.append_assoc]

theorem initList_eq (emit : Bool → List Bool) (input : List Bool) :
    initList (machine emit) input = running emit input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (emit : Bool → List Bool) (output : List Bool) :
    haltList (machine emit) output = halted emit output := by
  unfold haltList halted
  congr 1

theorem substitution_init_steps (emit : Bool → List Bool) (input : List Bool) :
    (next emit)^[2 * input.length + 1] (some (initList (machine emit) input)) =
      some (haltList (machine emit) (input.flatMap emit).reverse) := by
  rw [initList_eq, haltList_eq]
  simpa only [List.append_nil] using substitution_steps emit input [] none

def outputsInTime (emit : Bool → List Bool) (input : List Bool) :
    TM2OutputsInTime (machine emit) input (some (input.flatMap emit).reverse)
      (2 * input.length + 1) where
  steps := 2 * input.length + 1
  evals_in_steps := substitution_init_steps emit input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (emit : Bool → List Bool) (input : List Bool) :
    (outputsInTime emit input).steps = 2 * input.length + 1 := rfl

/-- A finite-machine polynomial-time certificate for reversed fixed substitution. -/
noncomputable def computableInPolyTime (emit : Bool → List Bool) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id
      (fun input => (input.flatMap emit).reverse) where
  tm := machine emit
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 1
  outputsFun input := by
    change TM2OutputsInTime (machine emit) (input.map id)
      (some ((input.flatMap emit).reverse.map id))
      ((2 * Polynomial.X + 1 : Polynomial Nat).eval input.length)
    have hi := @List.map_id ((machine emit).Γ (machine emit).k₀) input
    have ho := @List.map_id ((machine emit).Γ (machine emit).k₁) (input.flatMap emit).reverse
    rw [hi, ho]
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat, Polynomial.eval_one] using outputsInTime emit input

end MaxCutGames.Reduction.MachineSubstitution

namespace MaxCutGames.Reduction.MachineReverse

open Turing

def loop : TM2.Stmt (fun _ : Bool => Bool) Unit (Option Bool) :=
  .pop false (fun _ head => head)
    (.branch Option.isSome
      (.push true (fun state => state.getD false) (.goto fun _ => ()))
      .halt)

def machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m _ := loop

def tapeStacks (input output : List Bool) : Bool → List Bool :=
  fun side => if side then output else input

def running (input output : List Bool) (state : Option Bool) : machine.Cfg :=
  ⟨some (), state, tapeStacks input output⟩

def halted (output : List Bool) : machine.Cfg :=
  ⟨none, none, tapeStacks [] output⟩

private theorem update_input_inline_MachineReverse (input output replacement : List Bool) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> simp [tapeStacks]

private theorem update_output_inline_MachineReverse (input output replacement : List Bool) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> simp [tapeStacks]

/-- Popping an empty input resets the internal state to `none` before halting. -/
theorem step_empty (output : List Bool) (state : Option Bool) :
    machine.step (running [] output state) = some (halted output) := by
  change some (TM2.stepAux loop state (tapeStacks [] output)) = some (halted output)
  simp [loop, TM2.stepAux, tapeStacks, halted, Function.update]
  rw [update_input_inline_MachineReverse]
  rfl

/-- One transition moves the head symbol from the input onto the output. -/
theorem step_cons (head : Bool) (input output : List Bool) (state : Option Bool) :
    machine.step (running (head :: input) output state) =
      some (running input (head :: output) (some head)) := by
  change some (TM2.stepAux loop state (tapeStacks (head :: input) output)) = _
  simp [loop, TM2.stepAux, tapeStacks, running, Function.update]
  rw [update_input_inline_MachineReverse, update_output_inline_MachineReverse]
  rfl

def next (configuration : Option machine.Cfg) : Option machine.Cfg :=
  configuration.bind machine.step

/-- An exact transition trace, with arbitrary initial accumulator and state. -/
theorem reverse_steps (input output : List Bool) (state : Option Bool) :
    next^[input.length + 1] (some (running input output state)) =
      some (halted (input.reverse ++ output)) := by
  induction input generalizing output state with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, List.reverse_nil, List.nil_append] using step_empty output state
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change next^[input.length + 1]
      (machine.step (running (head :: input) output state)) = _
    rw [step_cons, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem initList_eq (input : List Bool) :
    initList machine input = running input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (output : List Bool) : haltList machine output = halted output := by
  unfold haltList halted
  congr 1

/-- The exact trace starts and ends at the standard encoded TM2 configurations. -/
theorem reverse_init_steps (input : List Bool) :
    next^[input.length + 1] (some (initList machine input)) =
      some (haltList machine input.reverse) := by
  rw [initList_eq, haltList_eq]
  simpa only [List.append_nil] using reverse_steps input [] none

def outputsInTime (input : List Bool) :
    TM2OutputsInTime machine input (some input.reverse) (input.length + 1) where
  steps := input.length + 1
  evals_in_steps := reverse_init_steps input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (input : List Bool) :
    (outputsInTime input).steps = input.length + 1 := rfl

/-- Actual finite-machine polynomial-time computability, with identity encodings. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id List.reverse where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun input := by
    change TM2OutputsInTime machine (input.map id) (some (input.reverse.map id))
      ((Polynomial.X + 1 : Polynomial Nat).eval input.length)
    have hi := @List.map_id (machine.Γ machine.k₀) input
    have ho := @List.map_id (machine.Γ machine.k₁) input.reverse
    rw [hi, ho]
    simpa only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      using outputsInTime input

end MaxCutGames.Reduction.MachineReverse

/-! Static renaming of labels and finite internal states. This does not execute
a data-copying phase and preserves every actual transition exactly. -/

namespace MaxCutGames.Foundations.Complexity.MachineControl

open Turing.TM2

variable {K Λ Λ' σ σ' : Type} {Γ : K → Type}

def configuration (labels : Λ → Λ') (states : σ ≃ σ') (c : Cfg Γ Λ σ) :
    Cfg Γ Λ' σ' where
  l := c.l.map labels
  var := states c.var
  stk := c.stk

def statement (labels : Λ → Λ') (states : σ ≃ σ') : Stmt Γ Λ σ → Stmt Γ Λ' σ'
  | .push k f next => .push k (fun st => f (states.symm st)) (statement labels states next)
  | .peek k f next => .peek k (fun st v => states (f (states.symm st) v))
      (statement labels states next)
  | .pop k f next => .pop k (fun st v => states (f (states.symm st) v))
      (statement labels states next)
  | .load f next => .load (fun st => states (f (states.symm st)))
      (statement labels states next)
  | .branch f yes no => .branch (fun st => f (states.symm st))
      (statement labels states yes) (statement labels states no)
  | .goto f => .goto (fun st => labels (f (states.symm st)))
  | .halt => .halt

variable [DecidableEq K]

theorem stepAux_simulation (labels : Λ → Λ') (states : σ ≃ σ')
    (q : Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    stepAux (statement labels states q) (states state) tapes =
      configuration labels states (stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false =>
      simpa only [statement, stepAux, Equiv.symm_apply_apply, h, Bool.cond_false] using
        ihNo state tapes
    | true =>
      simpa only [statement, stepAux, Equiv.symm_apply_apply, h, Bool.cond_true] using
        ihYes state tapes
  | goto f => simp [statement, stepAux, configuration]
  | halt => rfl

def program (labels : Λ ≃ Λ') (states : σ ≃ σ') (source : Λ → Stmt Γ Λ σ) :
    Λ' → Stmt Γ Λ' σ' := fun l => statement labels states (source (labels.symm l))

/-- The renamed program is conjugate to the original transition function,
including the halted configuration. -/
theorem step_simulation (labels : Λ ≃ Λ') (states : σ ≃ σ')
    (source : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) :
    step (program labels states source) (configuration labels states c) =
      (step source c).map (configuration labels states) := by
  cases c with
  | mk l state tapes =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (statement labels states (source (labels.symm (labels l))))
        (states state) tapes) = _
      rw [Equiv.symm_apply_apply, stepAux_simulation]
      rfl

end MaxCutGames.Foundations.Complexity.MachineControl

/-! Static exchange of the first two groups of stacks. Symbol types and stack
contents are retained exactly; no machine transition is spent on this layout
change. This aligns the two component machines in sequential composition. -/

namespace MaxCutGames.Foundations.Complexity.MachineStackSwap

open Turing.TM2

variable {A B C Λ σ : Type}
  {ΓA : A → Type} {ΓB : B → Type} {ΓC : C → Type}

abbrev Alphabet (ΓA : A → Type) (ΓB : B → Type) (ΓC : C → Type) :=
  MachineEmbedding.Alphabet ΓA (MachineEmbedding.Alphabet ΓB ΓC)

def tapes (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) :
    ∀ j, List (Alphabet ΓB ΓA ΓC j)
  | .inl b => source (.inr (.inl b))
  | .inr (.inl a) => source (.inl a)
  | .inr (.inr c) => source (.inr (.inr c))

@[simp] theorem tapes_first (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (a : A) :
    tapes source (.inr (.inl a)) = source (.inl a) := rfl
@[simp] theorem tapes_second (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (b : B) :
    tapes source (.inl b) = source (.inr (.inl b)) := rfl
@[simp] theorem tapes_third (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (c : C) :
    tapes source (.inr (.inr c)) = source (.inr (.inr c)) := rfl

theorem tapes_involutive (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) :
    tapes (tapes source) = source := by
  funext k
  rcases k with a | b | c <;> rfl

def configuration (c : Cfg (Alphabet ΓA ΓB ΓC) Λ σ) :
    Cfg (Alphabet ΓB ΓA ΓC) Λ σ where
  l := c.l
  var := c.var
  stk := tapes c.stk

def statement : Stmt (Alphabet ΓA ΓB ΓC) Λ σ → Stmt (Alphabet ΓB ΓA ΓC) Λ σ
  | .push (.inl a) f next => .push (.inr (.inl a)) f (statement next)
  | .push (.inr (.inl b)) f next => .push (.inl b) f (statement next)
  | .push (.inr (.inr c)) f next => .push (.inr (.inr c)) f (statement next)
  | .peek (.inl a) f next => .peek (.inr (.inl a)) f (statement next)
  | .peek (.inr (.inl b)) f next => .peek (.inl b) f (statement next)
  | .peek (.inr (.inr c)) f next => .peek (.inr (.inr c)) f (statement next)
  | .pop (.inl a) f next => .pop (.inr (.inl a)) f (statement next)
  | .pop (.inr (.inl b)) f next => .pop (.inl b) f (statement next)
  | .pop (.inr (.inr c)) f next => .pop (.inr (.inr c)) f (statement next)
  | .load f next => .load f (statement next)
  | .branch f yes no => .branch f (statement yes) (statement no)
  | .goto f => .goto f
  | .halt => .halt

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem tapes_update_first (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (a : A) (value : List (ΓA a)) :
    tapes (Function.update source (.inl a) value) =
      Function.update (tapes source) (.inr (.inl a)) value := by
  funext j
  rcases j with b | a' | c
  · simp [Function.update]
  · by_cases h : a' = a
    · subst a'; simp [Function.update]
    · simp [Function.update, h]
  · simp [Function.update]

theorem tapes_update_second (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (b : B) (value : List (ΓB b)) :
    tapes (Function.update source (.inr (.inl b)) value) =
      Function.update (tapes source) (.inl b) value := by
  funext j
  rcases j with b' | a | c
  · by_cases h : b' = b
    · subst b'; simp [Function.update]
    · simp [Function.update, h]
  · simp [Function.update]
  · simp [Function.update]

theorem tapes_update_third (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (c : C) (value : List (ΓC c)) :
    tapes (Function.update source (.inr (.inr c)) value) =
      Function.update (tapes source) (.inr (.inr c)) value := by
  funext j
  rcases j with b | a | c'
  · simp [Function.update]
  · simp [Function.update]
  · by_cases h : c' = c
    · subst c'; simp [Function.update]
    · simp [Function.update, h]

theorem stepAux_simulation (q : Stmt (Alphabet ΓA ΓB ΓC) Λ σ)
    (state : σ) (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) :
    stepAux (statement q) state (tapes source) =
      configuration (stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    rcases k with a | b | c
    · simp only [statement, stepAux, tapes_first]
      rw [← tapes_update_first]
      exact ih state (Function.update source (.inl a) (f state :: source (.inl a)))
    · simp only [statement, stepAux, tapes_second]
      rw [← tapes_update_second]
      exact ih state (Function.update source (.inr (.inl b))
        (f state :: source (.inr (.inl b))))
    · simp only [statement, stepAux, tapes_third]
      rw [← tapes_update_third]
      exact ih state (Function.update source (.inr (.inr c))
        (f state :: source (.inr (.inr c))))
  | peek k f next ih =>
    rcases k with a | b | c
    · simpa only [statement, stepAux, tapes_first] using
        ih (f state (source (.inl a)).head?) source
    · simpa only [statement, stepAux, tapes_second] using
        ih (f state (source (.inr (.inl b))).head?) source
    · simpa only [statement, stepAux, tapes_third] using
        ih (f state (source (.inr (.inr c))).head?) source
  | pop k f next ih =>
    rcases k with a | b | c
    · simp only [statement, stepAux, tapes_first]
      rw [← tapes_update_first]
      exact ih (f state (source (.inl a)).head?)
        (Function.update source (.inl a) (source (.inl a)).tail)
    · simp only [statement, stepAux, tapes_second]
      rw [← tapes_update_second]
      exact ih (f state (source (.inr (.inl b))).head?)
        (Function.update source (.inr (.inl b)) (source (.inr (.inl b))).tail)
    · simp only [statement, stepAux, tapes_third]
      rw [← tapes_update_third]
      exact ih (f state (source (.inr (.inr c))).head?)
        (Function.update source (.inr (.inr c)) (source (.inr (.inr c))).tail)
  | load f next ih => simpa only [statement, stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => rfl

def program (source : Λ → Stmt (Alphabet ΓA ΓB ΓC) Λ σ) :
    Λ → Stmt (Alphabet ΓB ΓA ΓC) Λ σ := fun l => statement (source l)

theorem step_simulation (source : Λ → Stmt (Alphabet ΓA ΓB ΓC) Λ σ)
    (c : Cfg (Alphabet ΓA ΓB ΓC) Λ σ) :
    step (program source) (configuration c) = (step source c).map configuration := by
  cases c with
  | mk l state sourceTapes =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (statement (source l)) state (tapes sourceTapes)) = _
      rw [stepAux_simulation]
      rfl

end MaxCutGames.Foundations.Complexity.MachineStackSwap

end OAI

end

-- MachineSequential
section


namespace OAI

/-!
A concrete sequential composition of two finite TM2 programs. The first output
is transferred to a temporary stack and then to the second input. Both loops
execute actual transitions and reset their shared register on exit. Static
renaming changes neither a stack word nor the number of executed transitions.
-/

namespace MaxCutGames.Foundations.Complexity.MachineSequential

open Turing

abbrev Tape (first second : FinTM2) := first.K ⊕ (second.K ⊕ Unit)
abbrev Symbols (first second : FinTM2) : Tape first second → Type :=
  MachineEmbedding.Alphabet first.Γ
    (MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
abbrev Label (first second : FinTM2) := first.Λ ⊕ (Bool ⊕ second.Λ)
abbrev Register (second : FinTM2) := Option (second.Γ second.k₀)
abbrev State (first second : FinTM2) := (first.σ × second.σ) × Register second

def firstStates (first second : FinTM2) :
    first.σ × (second.σ × Register second) ≃ State first second where
  toFun st := ((st.1, st.2.1), st.2.2)
  invFun st := (st.1.1, (st.1.2, st.2))
  left_inv _ := rfl
  right_inv _ := rfl

def secondStates (first second : FinTM2) :
    second.σ × (first.σ × Register second) ≃ State first second where
  toFun st := ((st.2.1, st.1), st.2.2)
  invFun st := (st.1.2, (st.1.1, st.2))
  left_inv _ := rfl
  right_inv _ := rfl

def secondLabels (first second : FinTM2) :
    second.Λ ⊕ (Bool ⊕ first.Λ) → Label first second
  | .inl label => .inr (.inr label)
  | .inr (.inl bit) => .inr (.inl bit)
  | .inr (.inr label) => .inl label

def bridgeLabel (first second : FinTM2) (bit : Bool) : Label first second :=
  .inr (.inl bit)

def firstStatement (first second : FinTM2) (q : first.Stmt) :
    TM2.Stmt (Symbols first second) (Label first second) (State first second) :=
  MachineControl.statement id (firstStates first second)
    (MachineEmbedding.statement (some (bridgeLabel first second false)) q)

def secondStatement (first second : FinTM2) (q : second.Stmt) :
    TM2.Stmt (Symbols first second) (Label first second) (State first second) :=
  MachineControl.statement (secondLabels first second) (secondStates first second)
    (MachineStackSwap.statement
      (MachineEmbedding.statement
        (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
        (Λextra := Bool ⊕ first.Λ) none q))

def program (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) :
    Label first second → TM2.Stmt (Symbols first second) (Label first second)
      (State first second)
  | .inl label => firstStatement first second (first.m label)
  | .inr (.inr label) => secondStatement first second (second.m label)
  | .inr (.inl false) =>
      Reduction.MachineTransfer.loopAt (Γ := Symbols first second)
        (.inl first.k₁) (.inr (.inr ())) relabel fallback
        (bridgeLabel first second false) (some (bridgeLabel first second true))
  | .inr (.inl true) =>
      Reduction.MachineTransfer.loopAt (Γ := Symbols first second)
        (.inr (.inr ())) (.inr (.inl second.k₀)) id fallback
        (bridgeLabel first second true) (some (.inr (.inr second.main)))

def machine (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) : FinTM2 where
  K := Tape first second
  kFin := by
    letI := first.kFin
    letI := second.kFin
    exact inferInstanceAs (Fintype (first.K ⊕ (second.K ⊕ Unit)))
  k₀ := .inl first.k₀
  k₁ := .inr (.inl second.k₁)
  Γ := Symbols first second
  Λ := Label first second
  ΛFin := by
    letI := first.ΛFin
    letI := second.ΛFin
    exact inferInstanceAs (Fintype (first.Λ ⊕ (Bool ⊕ second.Λ)))
  main := .inl first.main
  σ := State first second
  σFin := by
    letI := first.σFin
    letI := second.σFin
    letI := second.Γk₀Fin
    exact inferInstanceAs (Fintype ((first.σ × second.σ) × Option (second.Γ second.k₀)))
  initialState := ((first.initialState, second.initialState), none)
  Γk₀Fin := first.Γk₀Fin
  m := program first second relabel fallback

def firstConfiguration (first second : FinTM2) (c : first.Cfg) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  MachineControl.configuration id (firstStates first second)
    (MachineEmbedding.configuration (some (bridgeLabel first second false))
      (second.initialState, (none : Register second)) (fun _ => []) c)

def secondConfiguration (first second : FinTM2) (c : second.Cfg) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  MachineControl.configuration (secondLabels first second) (secondStates first second)
    (MachineStackSwap.configuration
      (MachineEmbedding.configuration
        (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
        (Λextra := Bool ⊕ first.Λ) none
        (first.initialState, (none : Register second)) (fun _ => []) c))

theorem firstStep (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (a b : first.Cfg)
    (transition : first.step a = some b) :
    (machine first second relabel fallback).step (firstConfiguration first second a) =
      some (firstConfiguration first second b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => cases transition
    | some label =>
      have hb := Option.some.inj transition
      subst b
      change some (TM2.stepAux
        (MachineControl.statement id (firstStates first second)
          (MachineEmbedding.statement (some (bridgeLabel first second false)) (first.m label)))
        ((firstStates first second) (state, (second.initialState, none)))
        (MachineEmbedding.tapes tapes (fun _ => []))) = _
      have controlled := MachineControl.stepAux_simulation id (firstStates first second)
        (MachineEmbedding.statement
          (Δ := MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
          (some (bridgeLabel first second false)) (first.m label))
        (state, (second.initialState, none)) (MachineEmbedding.tapes tapes (fun _ => []))
      have embedded := MachineEmbedding.stepAux_simulation
        (Δ := MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
        (some (bridgeLabel first second false)) (second.initialState, (none : Register second))
        (fun _ => []) (first.m label) state tapes
      exact congrArg some (controlled.trans
        (congrArg (MachineControl.configuration id (firstStates first second)) embedded))

theorem secondStep (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (a b : second.Cfg)
    (transition : second.step a = some b) :
    (machine first second relabel fallback).step (secondConfiguration first second a) =
      some (secondConfiguration first second b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => cases transition
    | some label =>
      have hb := Option.some.inj transition
      subst b
      change some (TM2.stepAux
        (MachineControl.statement (secondLabels first second) (secondStates first second)
          (MachineStackSwap.statement
            (MachineEmbedding.statement
              (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
              (Λextra := Bool ⊕ first.Λ) none (second.m label))))
        ((secondStates first second) (state, (first.initialState, none)))
        (MachineStackSwap.tapes (MachineEmbedding.tapes tapes (fun _ => [])))) = _
      rw [MachineControl.stepAux_simulation, MachineStackSwap.stepAux_simulation,
        MachineEmbedding.stepAux_simulation]
      rfl

theorem firstConfiguration_init (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (input : List (first.Γ first.k₀)) :
    firstConfiguration first second (initList first input) =
      initList (machine first second relabel fallback) input := by
  unfold firstConfiguration MachineControl.configuration MachineEmbedding.configuration initList
  congr 1
  funext k
  rcases k with k | k | k
  · by_cases h : k = first.k₀
    · subst k
      simp [machine, MachineEmbedding.tapes]; rfl
    · simp [machine, MachineEmbedding.tapes, h]
  · simp [machine, MachineEmbedding.tapes]
  · simp [machine, MachineEmbedding.tapes]

theorem secondConfiguration_halt (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (output : List (second.Γ second.k₁)) :
    secondConfiguration first second (haltList second output) =
      haltList (machine first second relabel fallback) output := by
  unfold secondConfiguration MachineControl.configuration MachineStackSwap.configuration
    MachineEmbedding.configuration haltList
  congr 1
  funext k
  rcases k with k | k | k
  · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]
  · by_cases h : k = second.k₁
    · subst k
      simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]; rfl
    · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes, h]
  · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]

def temporaryTapes (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    ∀ k, List (Symbols first second k)
  | .inl _ => []
  | .inr (.inl _) => []
  | .inr (.inr _) => word

def temporaryConfiguration (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  ⟨some (bridgeLabel first second true),
    ((first.initialState, second.initialState), none), temporaryTapes first second word⟩

theorem firstTransfer_tapes (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (word : List (first.Γ first.k₁)) :
    Reduction.MachineTransfer.tapesAt (.inl first.k₁) (.inr (.inr ()))
      (firstConfiguration first second (haltList first word)).stk [] (word.reverse.map relabel) =
        temporaryTapes first second (word.reverse.map relabel) := by
  funext k
  rcases k with k | k | k
  · by_cases h : k = first.k₁
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, firstConfiguration,
        MachineControl.configuration, MachineEmbedding.configuration, MachineEmbedding.tapes,
        haltList, h]
  · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, firstConfiguration,
      MachineControl.configuration, MachineEmbedding.configuration, MachineEmbedding.tapes]
  · cases k
    simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]

theorem secondTransfer_tapes (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols first second)
      (.inr (.inr ())) (.inr (.inl second.k₀))
      (temporaryTapes first second word) [] word.reverse =
        (secondConfiguration first second (initList second word.reverse)).stk := by
  funext k
  rcases k with k | k | k
  · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, secondConfiguration,
      MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
      MachineEmbedding.configuration, MachineEmbedding.tapes]
  · by_cases h : k = second.k₀
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, secondConfiguration,
        MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
        MachineEmbedding.configuration, MachineEmbedding.tapes, initList]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, secondConfiguration,
        MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
        MachineEmbedding.configuration, MachineEmbedding.tapes, initList, h]
  · cases k
    simp [Reduction.MachineTransfer.tapesAt, secondConfiguration,
      MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
      MachineEmbedding.configuration, MachineEmbedding.tapes]

def firstTransfer (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (word : List (first.Γ first.k₁)) :
    StateTransition.EvalsToInTime (machine first second relabel fallback).step
      (firstConfiguration first second (haltList first word))
      (some (temporaryConfiguration first second (word.reverse.map relabel)))
      (word.length + 1) := by
  let run := Reduction.MachineTransfer.transferAtInTime
    (.inl first.k₁ : Tape first second) (.inr (.inr ())) (by intro h; cases h)
    relabel fallback (bridgeLabel first second false)
    (some (bridgeLabel first second true)) (program first second relabel fallback) rfl
    (firstConfiguration first second (haltList first word)).stk
    (first.initialState, second.initialState) none
  have inputTape : (firstConfiguration first second (haltList first word)).stk (.inl first.k₁) =
      word := by simp [firstConfiguration, MachineControl.configuration,
        MachineEmbedding.configuration, MachineEmbedding.tapes, haltList]
  have outputTape :
      (firstConfiguration first second (haltList first word)).stk (.inr (.inr ())) = [] := rfl
  rw [inputTape, outputTape, List.append_nil, firstTransfer_tapes] at run
  exact run

def secondTransfer (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (word : List (second.Γ second.k₀)) :
    StateTransition.EvalsToInTime (machine first second relabel fallback).step
      (temporaryConfiguration first second word)
      (some (secondConfiguration first second (initList second word.reverse)))
      (word.length + 1) := by
  let run := Reduction.MachineTransfer.transferAtInTime
    (.inr (.inr ()) : Tape first second) (.inr (.inl second.k₀)) (by intro h; cases h)
    id fallback (bridgeLabel first second true) (some (.inr (.inr second.main)))
    (program first second relabel fallback) rfl (temporaryTapes first second word)
    (first.initialState, second.initialState) none
  simp only [temporaryTapes, List.map_id, List.append_nil] at run
  rw [secondTransfer_tapes] at run
  exact run

/-- An execution of each component yields an actual execution of the combined
machine. The two transfer loops add exactly twice the intermediate length plus two. -/
def execute (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀)
    (input : List (first.Γ first.k₀)) (middle : List (first.Γ first.k₁))
    (output : List (second.Γ second.k₁)) (firstBudget secondBudget : Nat)
    (runFirst : TM2OutputsInTime first input (some middle) firstBudget)
    (runSecond : TM2OutputsInTime second (middle.map relabel) (some output) secondBudget) :
    TM2OutputsInTime (machine first second relabel fallback) input (some output)
      (firstBudget + 2 * (middle.length + 1) + secondBudget) := by
  let start := MachineComposition.liftExecutionInTime first.step
    (machine first second relabel fallback).step (firstConfiguration first second)
    (firstStep first second relabel fallback) runFirst
  let bridge₁ := firstTransfer first second relabel fallback middle
  have bridge₂ := secondTransfer first second relabel fallback (middle.reverse.map relabel)
  have reversal : (middle.reverse.map relabel).reverse = middle.map relabel := by
    simp only [List.map_reverse, List.reverse_reverse]
  rw [reversal] at bridge₂
  simp only [List.length_map, List.length_reverse] at bridge₂
  let finish := MachineComposition.liftExecutionInTime second.step
    (machine first second relabel fallback).step (secondConfiguration first second)
    (secondStep first second relabel fallback) runSecond
  let phase₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ start bridge₁
  let phase₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ phase₁₂ bridge₂
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ phase₁₂₃ finish
  rw [firstConfiguration_init, secondConfiguration_halt] at full
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by have h := full.steps_le_m; omega
  }

/-- General sequential composition with an explicit symbol of the intermediate
alphabet to totalize the bridge's unused empty-register expression. Its time
polynomial uses the transition-derived output-length bound of the first machine. -/
noncomputable def compose {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) (fallback : βΓ) :
    TM2ComputableInPolyTime ea ec (fun a => g (f a)) := by
  let relabel : first.tm.Γ first.tm.k₁ → second.tm.Γ second.tm.k₀ :=
    fun symbol => second.inputAlphabet.symm (first.outputAlphabet symbol)
  let defaultSymbol := second.inputAlphabet.symm fallback
  let intermediate : Polynomial Nat := Polynomial.X +
    Polynomial.C (Runtime.programPushBound first.tm) * first.time
  refine {
    tm := machine first.tm second.tm relabel defaultSymbol
    inputAlphabet := first.inputAlphabet
    outputAlphabet := second.outputAlphabet
    time := MachineComposition.compositionPolynomial first.time second.time intermediate
    outputsFun := ?_
  }
  intro a
  let input := (ea a).map first.inputAlphabet.invFun
  let middle := (eb (f a)).map first.outputAlphabet.invFun
  let output := (ec (g (f a))).map second.outputAlphabet.invFun
  have handoff : middle.map relabel = (eb (f a)).map second.inputAlphabet.invFun := by
    dsimp only [middle, relabel]
    simp only [List.map_map]
    apply List.map_congr_left
    intro symbol _
    exact congrArg second.inputAlphabet.symm (first.outputAlphabet.apply_symm_apply symbol)
  have runSecond : TM2OutputsInTime second.tm (middle.map relabel) (some output)
      (second.time.eval (eb (f a)).length) := by
    rw [handoff]
    exact second.outputsFun (f a)
  have full := execute first.tm second.tm relabel defaultSymbol input middle output
    (first.time.eval (ea a).length) (second.time.eval (eb (f a)).length)
    (first.outputsFun a) runSecond
  have intermediateBound : (eb (f a)).length ≤ intermediate.eval (ea a).length :=
    Runtime.encodedOutputLength first a
  have totalBound := MachineComposition.compositionBudget_le first.time second.time
    intermediate (ea a).length (eb (f a)).length intermediateBound
  have middleLength : middle.length = (eb (f a)).length := by simp only [middle, List.length_map]
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by
      apply Nat.le_trans full.steps_le_m
      simpa only [middleLength] using totalBound
  }

noncomputable def composeBits {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) :
    TM2ComputableInPolyTime ea ec (fun a => g (f a)) :=
  compose first second false

end MaxCutGames.Foundations.Complexity.MachineSequential

namespace MaxCutGames.Reduction.MachineTransducer

open Turing
open MaxCutGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord statementPushBound_pushWord)

def tapeStacks (input output : List Bool) : Bool → List Bool :=
  fun side => if side then output else input

private theorem update_input_inline_MachineTransducer (input output replacement : List Bool) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> simp [tapeStacks]

private theorem update_output_inline_MachineTransducer (input output replacement : List Bool) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> simp [tapeStacks]

variable {Q : Type} [Fintype Q]

/-- The semantic output, with the control state updated after each input bit. -/
def output (transition : Q → Bool → Q) (emit : Q → Bool → List Bool) :
    Q → List Bool → List Bool
  | _, [] => []
  | state, symbol :: input =>
      emit state symbol ++ output transition emit (transition state symbol) input

def loop (initial : Q) :
    TM2.Stmt (fun _ : Bool => Bool) (Option (Q × Bool)) (Q × Option Bool) :=
  .pop false (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun state => some (state.1, state.2.getD false))
      (.load (fun _ => (initial, none)) .halt))

def program (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool) :
    Option (Q × Bool) →
      TM2.Stmt (fun _ : Bool => Bool) (Option (Q × Bool)) (Q × Option Bool)
  | none => loop initial
  | some (state, symbol) =>
      .load (fun register => (transition state symbol, register.2))
        (pushWord true (emit state symbol) (.goto fun _ => none))

def machine (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool) :
    FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Option (Q × Bool)
  main := none
  σ := Q × Option Bool
  initialState := (initial, none)
  m := program initial transition emit

/-- A finite maximum depending only on the fixed emission table. -/
noncomputable def maxEmission (emit : Q → Bool → List Bool) : Nat :=
  Finset.univ.sup (fun pair : Q × Bool => (emit pair.1 pair.2).length)

theorem emission_le (emit : Q → Bool → List Bool) (state : Q) (symbol : Bool) :
    (emit state symbol).length ≤ maxEmission emit := by
  exact Finset.le_sup (f := fun pair : Q × Bool => (emit pair.1 pair.2).length)
    (Finset.mem_univ (state, symbol))

theorem statementPushBound_le (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (label : Option (Q × Bool)) :
    Runtime.statementPushBound (program initial transition emit label) ≤ maxEmission emit := by
  cases label with
  | none => simp [program, loop, Runtime.statementPushBound]
  | some pair =>
    simpa only [program, Runtime.statementPushBound, statementPushBound_pushWord,
      Nat.add_zero] using emission_le emit pair.1 pair.2

theorem programPushBound_le (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) :
    Runtime.programPushBound (machine initial transition emit) ≤ maxEmission emit := by
  have allLabels (labels : List (Option (Q × Bool))) :
      Runtime.maxLabelPushes (program initial transition emit) labels ≤ maxEmission emit := by
    induction labels with
    | nil => exact Nat.zero_le _
    | cons label rest ih =>
      exact max_le (statementPushBound_le initial transition emit label) ih
  exact allLabels (machine initial transition emit).ΛFin.elems.toList

def running (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (state : Q) (input accumulator : List Bool) (register : Option Bool) :
    (machine initial transition emit).Cfg :=
  ⟨some none, (state, register), tapeStacks input accumulator⟩

def emitting (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (oldState : Q) (symbol : Bool) (input accumulator : List Bool)
    (state : Q × Option Bool) : (machine initial transition emit).Cfg :=
  ⟨some (some (oldState, symbol)), state, tapeStacks input accumulator⟩

def halted (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (accumulator : List Bool) : (machine initial transition emit).Cfg :=
  ⟨none, (initial, none), tapeStacks [] accumulator⟩

/-- The final empty pop also restores the initial finite control state. -/
theorem step_empty (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (accumulator : List Bool)
    (register : Option Bool) :
    (machine initial transition emit).step
        (running initial transition emit state [] accumulator register) =
      some (halted initial transition emit accumulator) := by
  change some (TM2.stepAux (loop initial) (state, register) (tapeStacks [] accumulator)) = _
  simp [loop, TM2.stepAux, tapeStacks, halted]
  erw [update_input_inline_MachineTransducer]
  rfl

theorem step_cons (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (symbol : Bool)
    (input accumulator : List Bool) (register : Option Bool) :
    (machine initial transition emit).step
        (running initial transition emit state (symbol :: input) accumulator register) =
      some (emitting initial transition emit state symbol input accumulator (state, some symbol)) := by
  change some (TM2.stepAux (loop initial) (state, register)
    (tapeStacks (symbol :: input) accumulator)) = _
  simp [loop, TM2.stepAux, tapeStacks, emitting]
  rw [update_input_inline_MachineTransducer]
  rfl

/-- Emission reads the old state from its label and installs its successor state. -/
theorem step_emit (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (oldState : Q) (symbol : Bool)
    (input accumulator : List Bool) (state : Q × Option Bool) :
    (machine initial transition emit).step
        (emitting initial transition emit oldState symbol input accumulator state) =
      some (running initial transition emit (transition oldState symbol) input
        ((emit oldState symbol).reverse ++ accumulator) state.2) := by
  change some (TM2.stepAux (pushWord true (emit oldState symbol) (.goto fun _ => none))
    (transition oldState symbol, state.2) (tapeStacks input accumulator)) = _
  rw [stepAux_pushWord]
  simp only [TM2.stepAux]
  change some (⟨some none, (transition oldState symbol, state.2),
    Function.update (tapeStacks input accumulator) true
      ((emit oldState symbol).reverse ++ accumulator)⟩ :
    (machine initial transition emit).Cfg) = _
  erw [update_output_inline_MachineTransducer]
  rfl

def next (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (configuration : Option (machine initial transition emit).Cfg) :
    Option (machine initial transition emit).Cfg :=
  configuration.bind (machine initial transition emit).step

theorem two_steps_cons (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (symbol : Bool)
    (input accumulator : List Bool) (register : Option Bool) :
    (next initial transition emit)^[2]
        (some (running initial transition emit state (symbol :: input) accumulator register)) =
      some (running initial transition emit (transition state symbol) input
        ((emit state symbol).reverse ++ accumulator) (some symbol)) := by
  change (machine initial transition emit).step
    (running initial transition emit state (symbol :: input) accumulator register) >>=
      (machine initial transition emit).step = _
  rw [step_cons]
  exact step_emit initial transition emit state symbol input accumulator (state, some symbol)

/-- Exact execution from any finite control state, accumulator, and symbol register. -/
theorem transduce_steps (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (input accumulator : List Bool)
    (register : Option Bool) :
    (next initial transition emit)^[2 * input.length + 1]
        (some (running initial transition emit state input accumulator register)) =
      some (halted initial transition emit ((output transition emit state input).reverse ++ accumulator)) := by
  induction input generalizing state accumulator register with
  | nil =>
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, output, List.reverse_nil, List.nil_append]
      using step_empty initial transition emit state accumulator register
  | cons symbol input ih =>
    rw [List.length_cons]
    rw [show 2 * (input.length + 1) + 1 = (2 * input.length + 1) + 2 by omega]
    rw [Function.iterate_add_apply, two_steps_cons, ih]
    simp only [output, List.reverse_append, List.append_assoc]

theorem initList_eq (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    initList (machine initial transition emit) input =
      running initial transition emit initial input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (accumulator : List Bool) :
    haltList (machine initial transition emit) accumulator =
      halted initial transition emit accumulator := by
  unfold haltList halted
  congr 1

theorem transduce_init_steps (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    (next initial transition emit)^[2 * input.length + 1]
        (some (initList (machine initial transition emit) input)) =
      some (haltList (machine initial transition emit) (output transition emit initial input).reverse) := by
  rw [initList_eq, haltList_eq]
  simpa only [List.append_nil] using transduce_steps initial transition emit initial input [] none

def outputsInTime (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    TM2OutputsInTime (machine initial transition emit) input
      (some (output transition emit initial input).reverse) (2 * input.length + 1) where
  steps := 2 * input.length + 1
  evals_in_steps := transduce_init_steps initial transition emit input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    (outputsInTime initial transition emit input).steps = 2 * input.length + 1 := rfl

/-- Reversed transducer output in polynomial `2 * X + 1` time. -/
noncomputable def reversedComputableInPolyTime (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id
      (fun input => (output transition emit initial input).reverse) where
  tm := machine initial transition emit
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 1
  outputsFun input := by
    change TM2OutputsInTime (machine initial transition emit) (input.map id)
      (some ((output transition emit initial input).reverse.map id))
      ((2 * Polynomial.X + 1 : Polynomial Nat).eval input.length)
    have hi := @List.map_id ((machine initial transition emit).Γ
      (machine initial transition emit).k₀) input
    have ho := @List.map_id ((machine initial transition emit).Γ
      (machine initial transition emit).k₁) (output transition emit initial input).reverse
    rw [hi, ho]
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat, Polynomial.eval_one] using outputsInTime initial transition emit input

/-- Forward transducer output, using the checked actual reversal composition. -/
noncomputable def computableInPolyTime (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id
      (output transition emit initial) := by
  simpa only [List.reverse_reverse] using
    MachineSequential.composeBits (reversedComputableInPolyTime initial transition emit)
      MachineReverse.computableInPolyTime

end MaxCutGames.Reduction.MachineTransducer

namespace MaxCutGames.Foundations.Complexity.MachineTransducerCopy

open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ Q : Type} [DecidableEq K]

abbrev Alphabet (K : Type) (_ : K) := Bool
abbrev State (σ Q : Type) := (σ × Q) × Option Bool

def scanLoop (source scratch : K) (initial : Q)
    (emitterLabel : Q → Bool → Λ) (restoreLabel : Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ Q) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push scratch (fun state => state.2.getD false)
        (.goto fun state => emitterLabel state.1.2 (state.2.getD false)))
      (.load (fun state => ((state.1.1, initial), none)) (.goto fun _ => restoreLabel)))

def emitter (destination : K) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (scanLabel : Λ) (control : Q) (symbol : Bool) :
    TM2.Stmt (Alphabet K) Λ (State σ Q) :=
  .load (fun state => ((state.1.1, transition control symbol), state.2))
    (pushWord destination (emit control symbol) (.goto fun _ => scanLabel))

abbrev tapes (source scratch destination : K) (base : K → List Bool)
    (input scratchWord outputWord : List Bool) : K → List Bool :=
  MachineCopy.forkTapes source scratch destination base input scratchWord outputWord

private theorem update_source_inline_MachineTransducerCopy (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination) (base : K → List Bool)
    (input scratchWord outputWord replacement : List Bool) :
    Function.update (tapes source scratch destination base input scratchWord outputWord)
      source replacement = tapes source scratch destination base replacement scratchWord outputWord := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, sourceScratch, sourceDestination]
  · by_cases ht : k = scratch
    · subst k; simp [tapes, MachineCopy.forkTapes, Ne.symm sourceScratch, scratchDestination]
    · by_cases hd : k = destination
      · subst k; simp [tapes, MachineCopy.forkTapes, Ne.symm sourceDestination]
      · simp [tapes, MachineCopy.forkTapes, hs, ht, hd]

private theorem update_scratch_inline_MachineTransducerCopy (source scratch destination : K)
    (scratchDestination : scratch ≠ destination) (base : K → List Bool)
    (input scratchWord outputWord replacement : List Bool) :
    Function.update (tapes source scratch destination base input scratchWord outputWord)
      scratch replacement = tapes source scratch destination base input replacement outputWord := by
  funext k
  by_cases ht : k = scratch
  · subst k; simp [tapes, MachineCopy.forkTapes, scratchDestination]
  · by_cases hd : k = destination
    · subst k; simp [tapes, MachineCopy.forkTapes, Ne.symm scratchDestination]
    · simp [tapes, MachineCopy.forkTapes, ht, hd]

private theorem update_output_inline_MachineTransducerCopy (source scratch destination : K) (base : K → List Bool)
    (input scratchWord outputWord replacement : List Bool) :
    Function.update (tapes source scratch destination base input scratchWord outputWord)
      destination replacement = tapes source scratch destination base input scratchWord replacement := by
  simp [tapes, MachineCopy.forkTapes]

theorem scanStep_empty (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (base : K → List Bool) (scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, control), register),
      tapes source scratch destination base [] scratchWord outputWord⟩ =
      some ⟨some restoreLabel, ((ambient, initial), none),
        tapes source scratch destination base [] scratchWord outputWord⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, control), register)
    (tapes source scratch destination base [] scratchWord outputWord)) = _
  rw [atScan]
  simp [scanLoop, TM2.stepAux, sourceScratch, sourceDestination, scratchDestination,
    update_source_inline_MachineTransducerCopy]

theorem scanStep_cons (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (base : K → List Bool) (symbol : Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, control), register),
      tapes source scratch destination base (symbol :: input) scratchWord outputWord⟩ =
      some ⟨some (emitterLabel control symbol), ((ambient, control), some symbol),
        tapes source scratch destination base input (symbol :: scratchWord) outputWord⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, control), register)
    (tapes source scratch destination base (symbol :: input) scratchWord outputWord)) = _
  rw [atScan]
  simp [scanLoop, TM2.stepAux, sourceScratch, sourceDestination, scratchDestination,
    update_source_inline_MachineTransducerCopy, update_scratch_inline_MachineTransducerCopy]

theorem emitterStep (source scratch destination : K)
    (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (base : K → List Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (symbol : Bool) :
    TM2.step program ⟨some (emitterLabel control symbol), ((ambient, control), some symbol),
      tapes source scratch destination base input scratchWord outputWord⟩ =
      some ⟨some scanLabel, ((ambient, transition control symbol), some symbol),
        tapes source scratch destination base input scratchWord
          ((emit control symbol).reverse ++ outputWord)⟩ := by
  change some (TM2.stepAux (program (emitterLabel control symbol)) ((ambient, control), some symbol)
    (tapes source scratch destination base input scratchWord outputWord)) = _
  rw [atEmitter]
  simp only [emitter, TM2.stepAux]
  rw [stepAux_pushWord]
  simp only [TM2.stepAux, MachineCopy.forkTapes_right]
  rw [update_output_inline_MachineTransducerCopy]

theorem twoSteps_cons (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (base : K → List Bool) (symbol : Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2]
      (some ⟨some scanLabel, ((ambient, control), register),
        tapes source scratch destination base (symbol :: input) scratchWord outputWord⟩) =
      some ⟨some scanLabel, ((ambient, transition control symbol), some symbol),
        tapes source scratch destination base input (symbol :: scratchWord)
          ((emit control symbol).reverse ++ outputWord)⟩ := by
  change (TM2.step program ⟨some scanLabel, ((ambient, control), register),
    tapes source scratch destination base (symbol :: input) scratchWord outputWord⟩).bind
      (TM2.step program) = _
  rw [scanStep_cons source scratch destination sourceScratch sourceDestination scratchDestination
    initial scanLabel restoreLabel emitterLabel program atScan base symbol input scratchWord
    outputWord ambient control register]
  exact emitterStep source scratch destination transition emit scanLabel emitterLabel program
    atEmitter base input (symbol :: scratchWord) outputWord ambient control symbol

theorem scanTrace (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (base : K → List Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * input.length + 1]
      (some ⟨some scanLabel, ((ambient, control), register),
        tapes source scratch destination base input scratchWord outputWord⟩) =
      some ⟨some restoreLabel, ((ambient, initial), none),
        tapes source scratch destination base [] (input.reverse ++ scratchWord)
          ((Reduction.MachineTransducer.output transition emit control input).reverse ++ outputWord)⟩ := by
  induction input generalizing control scratchWord outputWord register with
  | nil =>
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, Reduction.MachineTransducer.output, List.reverse_nil,
      List.nil_append] using
      scanStep_empty source scratch destination sourceScratch sourceDestination scratchDestination
        initial scanLabel restoreLabel emitterLabel program atScan base scratchWord outputWord
        ambient control register
  | cons symbol input ih =>
    rw [List.length_cons, show 2 * (input.length + 1) + 1 = (2 * input.length + 1) + 2 by omega,
      Function.iterate_add_apply]
    rw [twoSteps_cons source scratch destination sourceScratch sourceDestination scratchDestination
      initial transition emit scanLabel restoreLabel emitterLabel program atScan atEmitter base
      symbol input scratchWord outputWord ambient control register, ih]
    simp only [Reduction.MachineTransducer.output, List.reverse_append, List.reverse_cons,
      List.append_assoc, List.singleton_append]

theorem restoreTapes (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (base : K → List Bool) (scratchEmpty : base scratch = []) (outputWord : List Bool) :
    Reduction.MachineTransfer.tapesAt scratch source
      (tapes source scratch destination base [] (base source).reverse outputWord)
      [] (base source) = Function.update base destination outputWord := by
  funext k
  by_cases hs : k = source
  · subst k; simp [Reduction.MachineTransfer.tapesAt, sourceDestination]
  · by_cases ht : k = scratch
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, Ne.symm sourceScratch, scratchDestination, scratchEmpty]
    · by_cases hd : k = destination
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, tapes, MachineCopy.forkTapes,
          Ne.symm sourceDestination, Ne.symm scratchDestination]
      · simp [Reduction.MachineTransfer.tapesAt, tapes, MachineCopy.forkTapes, hs, ht, hd]

theorem transduceCopyTrace (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (atRestore : program restoreLabel =
      Reduction.MachineTransfer.loopAt scratch source id false restoreLabel exit)
    (base : K → List Bool) (scratchEmpty : base scratch = [])
    (ambient : σ) (control : Q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[3 * (base source).length + 2]
      (some ⟨some scanLabel, ((ambient, control), register), base⟩) =
      some ⟨exit, ((ambient, initial), none),
        Function.update base destination
          ((Reduction.MachineTransducer.output transition emit control (base source)).reverse ++
            base destination)⟩ := by
  have scan := scanTrace source scratch destination sourceScratch sourceDestination scratchDestination
    initial transition emit scanLabel restoreLabel emitterLabel program atScan atEmitter base
    (base source) (base scratch) (base destination) ambient control register
  have tapesSelf : tapes source scratch destination base (base source) (base scratch)
      (base destination) = base := MachineCopy.forkTapes_self source scratch destination base
  rw [tapesSelf] at scan
  simp only [scratchEmpty, List.append_nil] at scan
  let outputWord :=
    (Reduction.MachineTransducer.output transition emit control (base source)).reverse ++ base destination
  let scanned := tapes source scratch destination base [] (base source).reverse outputWord
  have restore := Reduction.MachineTransfer.transferAt_fromTapes scratch source (Ne.symm sourceScratch)
    id false restoreLabel exit program atRestore scanned (ambient, initial) none
  change (MachineComposition.advance (TM2.step program))^[(scanned scratch).length + 1]
    (some ⟨some restoreLabel, ((ambient, initial), none), scanned⟩) = _ at restore
  have scratchWord : scanned scratch = (base source).reverse := by
    simp [scanned, scratchDestination]
  have sourceWord : scanned source = [] := by
    simp [scanned, sourceScratch, sourceDestination]
  rw [scratchWord, sourceWord] at restore
  simp only [List.map_id, List.reverse_reverse, List.append_nil, List.length_reverse] at restore
  rw [restoreTapes source scratch destination sourceScratch sourceDestination scratchDestination
    base scratchEmpty outputWord] at restore
  rw [show 3 * (base source).length + 2 =
    ((base source).length + 1) + (2 * (base source).length + 1) by omega,
    Function.iterate_add_apply, scan]
  exact restore

def transduceCopyInTime (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (atRestore : program restoreLabel =
      Reduction.MachineTransfer.loopAt scratch source id false restoreLabel exit)
    (base : K → List Bool) (scratchEmpty : base scratch = [])
    (ambient : σ) (control : Q) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some scanLabel, ((ambient, control), register), base⟩
      (some ⟨exit, ((ambient, initial), none), Function.update base destination
        ((Reduction.MachineTransducer.output transition emit control (base source)).reverse ++
          base destination)⟩)
      (3 * (base source).length + 2) where
  steps := 3 * (base source).length + 2
  evals_in_steps := transduceCopyTrace source scratch destination sourceScratch sourceDestination
    scratchDestination initial transition emit scanLabel restoreLabel emitterLabel exit program
    atScan atEmitter atRestore base scratchEmpty ambient control register
  steps_le_m := Nat.le_refl _

omit [DecidableEq K] in
theorem scanLoop_pushBound (source scratch : K) (initial : Q)
    (emitterLabel : Q → Bool → Λ) (restoreLabel : Λ) :
    Runtime.statementPushBound (scanLoop (σ := σ) source scratch initial emitterLabel restoreLabel) = 1 := by
  simp [scanLoop, Runtime.statementPushBound]

omit [DecidableEq K] in
theorem emitter_pushBound (destination : K) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (scanLabel : Λ) (control : Q) (symbol : Bool) :
    Runtime.statementPushBound (emitter (σ := σ) destination transition emit scanLabel control symbol) =
      (emit control symbol).length := by
  simp [emitter, Runtime.statementPushBound, Reduction.MachineSubstitution.statementPushBound_pushWord]

end MaxCutGames.Foundations.Complexity.MachineTransducerCopy

end OAI

end

-- PsubsetNP
section


namespace A203914Bridge
open OAI.MaxCutGames.Reduction.MachineTransducer OAI.MaxCutGames.Foundations.Complexity OMA.S_oeis_a203914
-- none means discard the remainder; some false expects a tag, some true a payload.
def delta : Option Bool → Bool → Option Bool
  | none, _ => none
  | some true, _ => some false
  | some false, true => some true
  | some false, false => none

def emit : Option Bool → Bool → List Bool
  | some true, b => [b]
  | _, _ => []

theorem skipAll (w : List Bool) : output delta emit none w = [] := by
  induction w <;> simp_all [output, delta, emit]

theorem recover (x w : List Bool) : output delta emit (some false) (delimit x ++ w) = x := by
  induction x with
  | nil => simp [delimit, output, delta, emit, skipAll]
  | cons a x ih => simpa [delimit, output, delta, emit] using congrArg (List.cons a) ih

theorem P_subset_NP : P ⊆ NP := by
  rintro L ⟨decider⟩
  let trans := computableInPolyTime (some false) delta emit
  let both := MachineSequential.composeBits trans decider
  refine ⟨0, fun xw => L xw.1, ⟨{ both.toTM2ComputableAux with
    time := both.time
    outputsFun := fun xw => ?_ }⟩, ?_⟩
  · simpa only [id_eq, pairBits, recover] using both.outputsFun (pairBits xw)
  · intro x; constructor
    · intro h; exact ⟨[], by simp, h⟩
    · rintro ⟨_, _, h⟩; exact h
end A203914Bridge

end

theorem OMA.solution : OMA.R_oeis_a203914_R1_H1_R1.H3 := A203914Bridge.P_subset_NP
