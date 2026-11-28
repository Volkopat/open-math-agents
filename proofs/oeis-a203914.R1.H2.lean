import OMAReductions.R_oeis_a203914_R1
/- A203914 H2, @my-other-github-account. Machine combinators adapted from OpenAI openai/math (Apache-2.0), commit 3344da59991ed94f9ba711217b29c1d760badfa6. -/

-- Search.lean
section

namespace A203914.Search
open OMA.S_oeis_a203914

/-- Extend a prefix by testing only its false child. -/
def recover (ask : List Bool → Bool) : Nat → List Bool → List Bool
  | 0, p => p
  | d+1, p => recover ask d (p ++ [!(ask (p ++ [false]))])

theorem recover_spec (good : List Bool → Prop) (ask : List Bool → Bool) (n : Nat)
    (correct : ∀ p, ask p = true ↔ ∃ s, (p ++ s).length = n ∧ good (p ++ s))
    (d : Nat) (p : List Bool) (len : p.length + d = n)
    (feasible : ∃ s, (p ++ s).length = n ∧ good (p ++ s)) :
    good (recover ask d p) := by
  induction d generalizing p with
  | zero =>
    obtain ⟨s,hs,hg⟩ := feasible
    simp at len
    have : s = [] := List.length_eq_zero_iff.mp (by simp at hs; omega)
    simpa [this,recover] using hg
  | succ d ih =>
    rw [recover]
    apply ih
    · simp; omega
    cases h : ask (p ++ [false]) with
    | true => simpa using (correct _).mp h
    | false =>
      simp only [Bool.not_false]
      obtain ⟨s, hs, hg⟩ := feasible
      cases s with
      | nil => simp at hs; omega
      | cons b s =>
        cases b with
        | true => exact ⟨s, by simpa using hs, by simpa using hg⟩
        | false =>
          have hh := (correct (p ++ [false])).mpr ⟨s, by simpa using hs, by simpa using hg⟩
          simp [h] at hh

def threshold (ask : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k+1 => if ask (k+1) then k+1 else threshold ask k

theorem threshold_spec (ask : Nat → Bool) (opt : Nat)
    (h : ∀ k, ask k = true ↔ k ≤ opt) (k : Nat) : threshold ask k = min k opt := by
  induction k with
  | zero => simp [threshold]
  | succ k ih =>
    simp only [threshold, h, ih]
    split <;> omega

def Good {n} (G : SimpleGraph (Fin n)) (k : Nat) (w : List Bool) : Prop :=
  ∃ c, w = List.ofFn c ∧ k ≤ cutSize G c

def search (ask : Nat → List Bool → Bool) (n : Nat) : List Bool :=
  let k := threshold (fun i => ask i []) (n*n)
  recover (ask k) n []

theorem search_optimal {n} (G : SimpleGraph (Fin n)) (ask : Nat → List Bool → Bool)
    (spec : ∀ k p, ask k p = true ↔ ∃ s, (p ++ s).length = n ∧ Good G k (p ++ s)) :
    ∃ c, search ask n = List.ofFn c ∧ maxCut G ≤ cutSize G c := by
  classical
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin n → Bool)))
    Finset.univ_nonempty (cutSize G)
  change maxCut G = cutSize G c at hc
  have bound : maxCut G ≤ n*n := by
    rw [hc]; unfold cutSize
    simpa using (Finset.card_filter_le (s := (Finset.univ : Finset (Fin n × Fin n))) _)
  have emptySpec : ∀ k, ask k [] = true ↔ k ≤ maxCut G := by
    intro k; rw [spec]; constructor
    · rintro ⟨s,-,c',-,hk⟩
      exact hk.trans (Finset.le_sup (f := cutSize G) (Finset.mem_univ c'))
    · intro hk
      exact ⟨List.ofFn c, by simp, c, rfl, hc ▸ hk⟩
  unfold search
  rw [threshold_spec _ _ emptySpec, Nat.min_eq_right bound]
  exact recover_spec (Good G (maxCut G)) _ n (spec _) n [] (by simp)
    ((spec _ []).mp ((emptySpec _).mpr le_rfl))


def query (g : List Bool) (k : Nat) (p : List Bool) :=
  delimit g ++ delimit (List.replicate k true) ++ p

def driver (L : DecisionProblem) (g : List Bool) :=
  search (fun k p => L (query g k p)) g.length.sqrt

theorem graphBits_length {n} (G : SimpleGraph (Fin n)) : (graphBits G).length = n*n := by
  classical
  simp [graphBits, List.length_flatMap]

theorem optimal_of_decider (L : DecisionProblem)
    (spec : ∀ n (G : SimpleGraph (Fin n)) k p,
      L (query (graphBits G) k p) = true ↔ ∃ s, (p ++ s).length = n ∧ Good G k (p ++ s))
    (n) (G : SimpleGraph (Fin n)) :
    ∃ c, driver L (graphBits G) = List.ofFn c ∧ maxCut G ≤ cutSize G c := by
  simpa [driver, graphBits_length] using search_optimal G _ (spec n G)

theorem H2_of_machines (L : DecisionProblem) (hNP : L ∈ NP)
    (spec : ∀ n (G : SimpleGraph (Fin n)) k p,
      L (query (graphBits G) k p) = true ↔ ∃ s, (p ++ s).length = n ∧ Good G k (p ++ s))
    (realize : L ∈ P → Nonempty (Turing.TM2ComputableInPolyTime id id (driver L)))
    (h : P = NP) : ApproximatesMaxCut 1 := by
  refine ⟨driver L, realize (h ▸ hNP), ?_⟩
  intro n G
  obtain ⟨c,hc,ho⟩ := optimal_of_decider L spec n G
  exact ⟨c,hc,by simpa using (Nat.cast_le.mpr ho : (maxCut G : ℝ) ≤ _)⟩


theorem delimit_length (p : List Bool) : (delimit p).length = 2*p.length+1 := by
  induction p with
  | nil => rfl
  | cons b p ih => simp [delimit, ih]; omega

theorem query_length (g : List Bool) (k : Nat) (p : List Bool) :
    (query g k p).length = 2*g.length + 2*k + p.length + 2 := by
  simp [query, delimit_length]; omega

/-- Actual queries made by recovery, including the tested bit. -/
def prefixCalls (ask : List Bool → Bool) : Nat → List Bool → List (List Bool)
  | 0, _ => []
  | d+1, p => (p ++ [false]) :: prefixCalls ask d (p ++ [!(ask (p ++ [false]))])

theorem prefixCalls_bound (ask : List Bool → Bool) (d : Nat) (p : List Bool) :
    (prefixCalls ask d p).length = d ∧ ∀ q ∈ prefixCalls ask d p, q.length ≤ p.length+d := by
  induction d generalizing p with
  | zero => simp [prefixCalls]
  | succ d ih =>
    obtain ⟨h₁,h₂⟩ := ih (p ++ [!(ask (p ++ [false]))])
    constructor
    · simp [prefixCalls, h₁]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | h
      · simp
      · have := h₂ q h; simp at this; omega

/-- Actual thresholds tested before a feasible value is found. -/
def thresholdCalls (ask : Nat → Bool) : Nat → List Nat
  | 0 => []
  | k+1 => (k+1) :: (if ask (k+1) then [] else thresholdCalls ask k)

theorem thresholdCalls_bound (ask : Nat → Bool) (k : Nat) :
    (thresholdCalls ask k).length ≤ k ∧ ∀ i ∈ thresholdCalls ask k, i ≤ k := by
  induction k with
  | zero => simp [thresholdCalls]
  | succ k ih =>
    cases h : ask (k+1) <;> (simp [thresholdCalls,h] <;> grind)

theorem threshold_le (ask : Nat → Bool) (k : Nat) : threshold ask k ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [threshold]; split <;> omega

def calls (L : DecisionProblem) (g : List Bool) : List (List Bool) :=
  let n := g.length.sqrt
  let test k := L (query g k [])
  let k := threshold test (n*n)
  (thresholdCalls test (n*n)).map (fun i => query g i []) ++
    (prefixCalls (fun p => L (query g k p)) n []).map (query g k)

theorem calls_bound (L : DecisionProblem) (g : List Bool) :
    (calls L g).length ≤ 2*g.length ∧ ∀ q ∈ calls L g, q.length ≤ 5*g.length+2 := by
  let n := g.length.sqrt
  let test k := L (query g k [])
  let k := threshold test (n*n)
  have hn : n*n ≤ g.length := Nat.sqrt_le _
  have hn' : n ≤ g.length := by nlinarith [Nat.le_mul_self n]
  have hk : k ≤ n*n := threshold_le _ _
  obtain ⟨h₁,h₂⟩ := thresholdCalls_bound test (n*n)
  obtain ⟨h₃,h₄⟩ := prefixCalls_bound (fun p => L (query g k p)) n []
  constructor
  · simp only [calls,List.length_append,List.length_map] at *
    change (thresholdCalls test (n*n)).length + (prefixCalls (fun p => L (query g k p)) n []).length ≤ _
    omega
  · intro q hq
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
      have := h₂ i hi
      simp [query_length]; omega
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h
      have := h₄ p hp
      simp only [List.length_nil,zero_add] at this
      change (query g k p).length ≤ _
      rw [query_length]; omega

end A203914.Search

end

-- Oracle.lean
section
/- Adapted from OpenAI OAI, commit 3344da59991ed94f9ba711217b29c1d760badfa6. -/
namespace OAI.IndependentSetsGames.Foundations.Complexity
def encodeWord (n : Nat) := List.replicate n true ++ [false]
@[simp] theorem encodeWord_length (n : Nat) : (encodeWord n).length=n+1 := by simp [encodeWord]
end OAI.IndependentSetsGames.Foundations.Complexity

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineEmbedding

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

end IndependentSetsGames.Foundations.Complexity.MachineEmbedding

end OAI

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineComposition

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

end IndependentSetsGames.Foundations.Complexity.MachineComposition

end OAI

namespace OAI

namespace IndependentSetsGames.Reduction.MachineTransfer
open Turing
variable {α β : Type} [Fintype α] [Fintype β]

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

private theorem update_tapesAt_src (src dst : K) (distinct : src ≠ dst)
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

private theorem update_tapesAt_dst (src dst : K)
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
    simp [loopAt, exitAt, TM2.stepAux, tapesAt_src, distinct, update_tapesAt_src]

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
    update_tapesAt_src, update_tapesAt_dst]

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

end IndependentSetsGames.Reduction.MachineTransfer

end OAI

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRepeat
open Turing

inductive ExtraTape | counter | temporary | output
  deriving DecidableEq

instance : Fintype ExtraTape where
  elems := {.counter, .temporary, .output}
  complete tape := by cases tape <;> simp

inductive Phase | parse | guard | bodyToTemp | tempToBody | finalToTemp | tempToOutput
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.parse, .guard, .bodyToTemp, .tempToBody, .finalToTemp, .tempToOutput}
  complete phase := by cases phase <;> simp

abbrev Tape (M : FinTM2) := M.K ⊕ ExtraTape
abbrev Symbols (M : FinTM2) := MachineEmbedding.Alphabet M.Γ (fun _ : ExtraTape => M.Γ M.k₀)
abbrev Label (M : FinTM2) := M.Λ ⊕ Phase
abbrev State (M : FinTM2) := M.σ × Option (M.Γ M.k₀)

def extraTapes (M : FinTM2) (counter temporary output : List (M.Γ M.k₀)) :
    ExtraTape → List (M.Γ M.k₀)
  | .counter => counter
  | .temporary => temporary
  | .output => output

def auxProgram (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool) :
    Phase → TM2.Stmt (Symbols M) (Label M) (State M)
  | .parse => .pop (.inl M.k₀) (fun s v => (s.1,v))
      (.branch (fun s => input (s.2.getD (input.symm false)))
        (.push (.inr .counter) (fun _ => input.symm true)
          (.load (fun s => (s.1,none)) (.goto (fun _ => .inr .parse))))
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inr .guard))))
  | .guard => .pop (.inr .counter) (fun s v => (s.1,v))
      (.branch (fun s => s.2.isSome)
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inl M.main)))
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inr .finalToTemp))))
  | .bodyToTemp => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inl M.k₁) (.inr .temporary)
      (fun b => input.symm (output b)) (input.symm false)
      (.inr .bodyToTemp) (some (.inr .tempToBody))
  | .tempToBody => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inr .temporary) (.inl M.k₀)
      id (input.symm false) (.inr .tempToBody) (some (.inr .guard))
  | .finalToTemp => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inl M.k₀) (.inr .temporary)
      id (input.symm false) (.inr .finalToTemp) (some (.inr .tempToOutput))
  | .tempToOutput => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inr .temporary) (.inr .output)
      id (input.symm false) (.inr .tempToOutput) none

def program (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool) :
    Label M → TM2.Stmt (Symbols M) (Label M) (State M) :=
  MachineEmbedding.program (some (.inr .bodyToTemp)) M.m (auxProgram M input output)

def machine (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool) : FinTM2 where
  K := Tape M
  kFin := by letI := M.kFin; exact inferInstanceAs (Fintype (Tape M))
  k₀ := .inl M.k₀
  k₁ := .inr .output
  Γ := Symbols M
  Λ := Label M
  ΛFin := by letI := M.ΛFin; exact inferInstanceAs (Fintype (Label M))
  main := .inr .parse
  σ := State M
  σFin := by
    letI := M.σFin
    letI := M.Γk₀Fin
    exact inferInstanceAs (Fintype (State M))
  initialState := (M.initialState,none)
  Γk₀Fin := M.Γk₀Fin
  m := program M input output

def inputTapes (M : FinTM2) (word counter : List (M.Γ M.k₀)) : ∀k, List (Symbols M k) :=
  MachineEmbedding.tapes (initList M word).stk (extraTapes M counter [] [])

@[simp] theorem inputTapes_input (M : FinTM2) (word counter : List (M.Γ M.k₀)) :
    inputTapes M word counter (.inl M.k₀) = word := by
  simp [inputTapes, initList]

@[simp] theorem inputTapes_counter (M : FinTM2) (word counter : List (M.Γ M.k₀)) :
    inputTapes M word counter (.inr .counter) = counter := rfl

def inputConfig (M : FinTM2) (phase : Phase) (word counter : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr phase),(M.initialState,none),inputTapes M word counter⟩

def embedded (M : FinTM2) (counter : List (M.Γ M.k₀)) (c : M.Cfg) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  MachineEmbedding.configuration (some (.inr .bodyToTemp)) (none : Option (M.Γ M.k₀))
    (extraTapes M counter [] []) c

def temporaryTapes (M : FinTM2) (word counter : List (M.Γ M.k₀)) : ∀k, List (Symbols M k) :=
  MachineEmbedding.tapes (fun _ => []) (extraTapes M counter word [])

def temporaryConfig (M : FinTM2) (phase : Phase) (word counter : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr phase),(M.initialState,none),temporaryTapes M word counter⟩

private theorem inputTapes_update_input (M : FinTM2)
    (word counter replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word counter) (.inl M.k₀) replacement =
      inputTapes M replacement counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes, initList]
    · simp [inputTapes, initList, h]
  | inr k => simp [inputTapes]

private theorem inputTapes_update_counter (M : FinTM2)
    (word counter replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word counter) (.inr .counter) replacement =
      inputTapes M word replacement := by
  funext k
  cases k with
  | inl k => simp [inputTapes]
  | inr k => cases k <;> simp [inputTapes, extraTapes]

def oneStep {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := le_refl _

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

theorem parseStep_true (word counter : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M .parse (input.symm true :: word) counter) =
    some (inputConfig M .parse word (input.symm true :: counter)) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState,none) (inputTapes M (input.symm true :: word) counter)) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_input, inputTapes_update_counter,
    inputConfig]

theorem parseStep_false (word counter : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M .parse (input.symm false :: word) counter) =
    some (inputConfig M .guard word counter) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState,none) (inputTapes M (input.symm false :: word) counter)) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_input, inputTapes_update_counter,
    inputConfig]

theorem parseTrace (count : Nat) (word counter : List (M.Γ M.k₀)) :
    (MachineComposition.advance (machine M input output).step)^[count+1]
      (some (inputConfig M .parse ((encodeWord count).map input.symm ++ word) counter)) =
    some (inputConfig M .guard word (List.replicate count (input.symm true) ++ counter)) := by
  induction count generalizing counter with
  | zero =>
    simp only [encodeWord, List.replicate_zero, List.nil_append, List.map_singleton,
      List.singleton_append, Nat.zero_add, Function.iterate_one]
    exact parseStep_false M input output word counter
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (machine M input output).step)^[count+1]
      ((machine M input output).step
        (inputConfig M .parse ((encodeWord (count+1)).map input.symm ++ word) counter)) = _
    simp only [encodeWord, List.replicate_succ, List.cons_append, List.map_cons,
      List.map_append, List.map_replicate, List.map_nil, List.append_assoc, List.nil_append]
    rw [parseStep_true]
    have h := ih (input.symm true :: counter)
    have hc : List.replicate count (input.symm true) ++ input.symm true :: counter =
        input.symm true :: (List.replicate count (input.symm true) ++ counter) := by
      rw [← List.singleton_append, ← List.append_assoc,
        ← List.replicate_succ', List.replicate_succ, List.cons_append]
    rw [hc] at h
    simp only [encodeWord, List.map_append, List.map_replicate, List.map_singleton,
      List.singleton_append, List.append_assoc] at h
    exact h

theorem guardStep_some (word counter : List (M.Γ M.k₀)) (symbol : M.Γ M.k₀) :
    (machine M input output).step (inputConfig M .guard word (symbol :: counter)) =
      some (embedded M counter (initList M word)) := by
  change some (TM2.stepAux (auxProgram M input output .guard)
    (M.initialState,none) (inputTapes M word (symbol :: counter))) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_counter,
    embedded, MachineEmbedding.configuration]
  exact ⟨rfl,rfl,rfl⟩

theorem guardStep_none (word : List (M.Γ M.k₀)) :
    (machine M input output).step (inputConfig M .guard word []) =
      some (inputConfig M .finalToTemp word []) := by
  change some (TM2.stepAux (auxProgram M input output .guard)
    (M.initialState,none) (inputTapes M word [])) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_counter, inputConfig]

def bodyExecution (counter : List (M.Γ M.k₀))
    (word : List (M.Γ M.k₀)) (result : List (M.Γ M.k₁)) (budget : Nat)
    (run : TM2OutputsInTime M word (some result) budget) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M counter (initList M word))
      (some (embedded M counter (haltList M result))) budget :=
  MachineComposition.embeddedExecution (some (.inr .bodyToTemp : Label M))
    (none : Option (M.Γ M.k₀)) (extraTapes M counter [] []) M.m
    (auxProgram M input output) run

private theorem bodyToTemp_tapes (result : List (M.Γ M.k₁)) (counter : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (.inl M.k₁) (.inr .temporary)
      (embedded M counter (haltList M result)).stk []
      (result.reverse.map (fun b => input.symm (output b))) =
    temporaryTapes M (result.reverse.map (fun b => input.symm (output b))) counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₁
    · subst k; simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, embedded,
        MachineEmbedding.configuration, haltList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, embedded,
      MachineEmbedding.configuration, extraTapes]

private theorem tempToBody_tapes (word counter : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .temporary) (.inl M.k₀)
      (temporaryTapes M word counter) [] word.reverse = inputTapes M word.reverse counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [Reduction.MachineTransfer.tapesAt, inputTapes, initList]
    · simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, initList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, extraTapes]

private theorem finalToTemp_tapes (word : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inl M.k₀) (.inr .temporary)
      (inputTapes M word []) [] word.reverse = temporaryTapes M word.reverse [] := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, initList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, extraTapes]

private theorem tempToOutput_tapes (word : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .temporary) (.inr .output)
      (temporaryTapes M word []) [] word.reverse =
        (haltList (machine M input output) word.reverse).stk := by
  funext k
  cases k with
  | inl k => simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, haltList, machine]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, haltList,
      machine, extraTapes]
    rfl

def bodyToTemp (result : List (M.Γ M.k₁)) (counter : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M counter (haltList M result))
      (some (temporaryConfig M .tempToBody
        (result.reverse.map (fun b => input.symm (output b))) counter)) (result.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inl M.k₁) (.inr .temporary) (by intro h; cases h)
    (fun b => input.symm (output b)) (input.symm false)
    (.inr .bodyToTemp) (some (.inr .tempToBody)) (program M input output) rfl
    (embedded M counter (haltList M result)).stk M.initialState none
  have hs : (embedded M counter (haltList M result)).stk (.inl M.k₁) = result := by
    simp [embedded, MachineEmbedding.configuration, haltList]
  have hd : (embedded M counter (haltList M result)).stk (.inr .temporary) = [] := rfl
  rw [hs,hd,List.append_nil,bodyToTemp_tapes] at run
  exact run

def tempToBody (word counter : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (temporaryConfig M .tempToBody word counter)
      (some (inputConfig M .guard word.reverse counter)) (word.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inr .temporary) (.inl M.k₀) (by intro h; cases h)
    id (input.symm false) (.inr .tempToBody) (some (.inr .guard))
    (program M input output) rfl (temporaryTapes M word counter) M.initialState none
  simp only [temporaryTapes, MachineEmbedding.tapes, extraTapes,
    List.map_id, List.append_nil] at run
  rw [show Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .temporary) (.inl M.k₀)
      (MachineEmbedding.tapes (fun _ => []) (extraTapes M counter word [])) [] word.reverse =
        inputTapes M word.reverse counter from tempToBody_tapes M word counter] at run
  exact run

def finalToTemp (word : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .finalToTemp word [])
      (some (temporaryConfig M .tempToOutput word.reverse [])) (word.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inl M.k₀) (.inr .temporary) (by intro h; cases h)
    id (input.symm false) (.inr .finalToTemp) (some (.inr .tempToOutput))
    (program M input output) rfl (inputTapes M word []) M.initialState none
  have hd : inputTapes M word [] (.inr .temporary) = [] := rfl
  rw [inputTapes_input,hd,List.map_id,List.append_nil,finalToTemp_tapes] at run
  exact run

def tempToOutput (word : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (temporaryConfig M .tempToOutput word [])
      (some (haltList (machine M input output) word.reverse)) (word.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inr .temporary) (.inr .output) (by intro h; cases h)
    id (input.symm false) (.inr .tempToOutput) none
    (program M input output) rfl (temporaryTapes M word []) M.initialState none
  have hs : temporaryTapes M word [] (.inr .temporary) = word := rfl
  have hd : temporaryTapes M word [] (.inr .output) = [] := rfl
  rw [hs,hd,List.map_id,List.append_nil,tempToOutput_tapes] at run
  exact run

def bodyReturn (result : List (M.Γ M.k₁)) (counter : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M counter (haltList M result))
      (some (inputConfig M .guard (result.map (fun b => input.symm (output b))) counter))
      (2*(result.length+1)) := by
  have first := bodyToTemp M input output result counter
  have second := tempToBody M input output (result.reverse.map (fun b => input.symm (output b))) counter
  simp only [List.map_reverse,List.reverse_reverse,List.length_reverse,List.length_map] at first second
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  exact { toEvalsTo := full.toEvalsTo, steps_le_m := by have h := full.steps_le_m; omega }

def finish (word : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .guard word []) (some (haltList (machine M input output) word))
      (2*word.length+3) := by
  have guard := oneStep _ _ _ (guardStep_none M input output word)
  have first := finalToTemp M input output word
  have second := tempToOutput M input output word.reverse
  simp only [List.reverse_reverse,List.length_reverse] at second
  have gfirst := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard first
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ gfirst second
  exact { toEvalsTo := full.toEvalsTo, steps_le_m := by have h := full.steps_le_m; omega }

def loopBudget : Nat → (Nat → List Bool) → (Nat → Nat) → Nat
  | 0, words, _ => 2*(words 0).length+3
  | count+1, words, budgets => budgets 0 + 2*(words 1).length+3 +
      loopBudget count (fun i => words (i+1)) (fun i => budgets (i+1))

def loopExecution (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (runs : ∀ i, i < count → TM2OutputsInTime M ((words i).map input.symm)
      (some ((words (i+1)).map output.symm)) (budgets i)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .guard ((words 0).map input.symm)
        (List.replicate count (input.symm true)))
      (some (haltList (machine M input output) ((words count).map input.symm)))
      (loopBudget count words budgets) := by
  induction count generalizing words budgets with
  | zero =>
    simp only [loopBudget, List.replicate_zero]
    have finished := finish M input output ((words 0).map input.symm)
    simp only [List.length_map] at finished
    exact finished
  | succ count ih =>
    rw [List.replicate_succ]
    have guard := oneStep _ _ _ (guardStep_some M input output ((words 0).map input.symm)
      (List.replicate count (input.symm true)) (input.symm true))
    have body := bodyExecution M input output (List.replicate count (input.symm true))
      ((words 0).map input.symm) ((words 1).map output.symm) (budgets 0)
      (runs 0 (Nat.zero_lt_succ count))
    have returned := bodyReturn M input output ((words 1).map output.symm)
      (List.replicate count (input.symm true))
    have handoff : ((words 1).map output.symm).map (fun b => input.symm (output b)) =
        (words 1).map input.symm := by
      simp only [List.map_map,Function.comp_def,Equiv.apply_symm_apply]
    rw [handoff,List.length_map] at returned
    have tail := ih (fun i => words (i+1)) (fun i => budgets (i+1))
      (fun i hi => runs (i+1) (Nat.succ_lt_succ hi))
    have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard body
    have second := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first returned
    have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ second tail
    exact {
      toEvalsTo := full.toEvalsTo
      steps_le_m := by
        have h := full.steps_le_m
        simp only [loopBudget]
        omega
    }

private theorem inputConfig_init (word : List (M.Γ M.k₀)) :
    inputConfig M .parse word [] = initList (machine M input output) word := by
  unfold inputConfig initList
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes,initList,machine]; rfl
    · simp [inputTapes,initList,machine,h]
  | inr k => cases k <;> simp [inputTapes,initList,machine,extraTapes]

def executeSequence (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (runs : ∀ i, i < count → TM2OutputsInTime M ((words i).map input.symm)
      (some ((words (i+1)).map output.symm)) (budgets i)) :
    TM2OutputsInTime (machine M input output)
      ((encodeWord count ++ words 0).map input.symm)
      (some ((words count).map input.symm))
      (count+1 + loopBudget count words budgets) := by
  let parsed : StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .parse ((encodeWord count).map input.symm ++ (words 0).map input.symm) [])
      (some (inputConfig M .guard ((words 0).map input.symm)
        (List.replicate count (input.symm true)))) (count+1) := {
    steps := count+1
    evals_in_steps := by
      change (MachineComposition.advance (machine M input output).step)^[count+1]
        (some (inputConfig M .parse ((encodeWord count).map input.symm ++ (words 0).map input.symm) [])) = _
      have parsedTrace := parseTrace M input output count
        ((words 0).map input.symm) []
      simp only [List.append_nil] at parsedTrace
      exact parsedTrace
    steps_le_m := le_refl _
  }
  have body := loopExecution M input output count words budgets runs
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ parsed body
  rw [inputConfig_init M input output] at full
  simp only [TM2OutputsInTime, Option.map_some]
  erw [List.map_append]
  rw [Nat.add_comm (loopBudget count words budgets)] at full
  exact full

omit M input output in

theorem loopBudget_eq_sum (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat) :
    loopBudget count words budgets =
      (∑ i ∈ Finset.range count, (budgets i + 2*(words (i+1)).length+3)) +
      2*(words count).length+3 := by
  induction count generalizing words budgets with
  | zero => simp [loopBudget]
  | succ count ih =>
    rw [loopBudget, ih, Finset.sum_range_succ']
    simp only [Nat.zero_add]
    omega

def executeSequenceSum (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (runs : ∀ i, i < count → TM2OutputsInTime M ((words i).map input.symm)
      (some ((words (i+1)).map output.symm)) (budgets i)) :
    TM2OutputsInTime (machine M input output)
      ((encodeWord count ++ words 0).map input.symm)
      (some ((words count).map input.symm))
      (count+1 + ((∑ i ∈ Finset.range count, (budgets i+2*(words (i+1)).length+3)) +
        2*(words count).length+3)) := by
  rw [← loopBudget_eq_sum]
  exact executeSequence M input output count words budgets runs

omit M input output in

theorem loopBudget_le (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (bodyBound lengthBound : Nat)
    (hb : ∀i, i<count → budgets i ≤ bodyBound)
    (hl : ∀i, i≤count → (words i).length ≤ lengthBound) :
    loopBudget count words budgets ≤ count*(bodyBound+2*lengthBound+3)+2*lengthBound+3 := by
  rw [loopBudget_eq_sum]
  have hs : (∑ i ∈ Finset.range count, (budgets i+2*(words (i+1)).length+3)) ≤
      count*(bodyBound+2*lengthBound+3) := by
    calc
      _ ≤ ∑ i ∈ Finset.range count, (bodyBound+2*lengthBound+3) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hbi := hb i hi'
        have hli := hl (i+1) hi'
        omega
      _ = _ := by simp
  have hlast := hl count (le_refl _)
  omega

end IndependentSetsGames.Foundations.Complexity.MachineRepeat

end OAI

namespace OAI

namespace LargeIndependentSets.BoundedIteration
open Turing
open IndependentSetsGames.Foundations.Complexity

variable {α β : Type}

def counted (count : α → ℕ) (enc : β → List Bool) (start : α → β) (a : α) : List Bool :=
  encodeWord (count a) ++ enc (start a)

lemma count_le (count : α → ℕ) (enc : β → List Bool) (start : α → β) (a : α) :
    count a ≤ (counted count enc start a).length := by
  simp [counted,encodeWord]

noncomputable def runtime (body length : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X*(body.comp length + 2*length + 4) + 2*length + 4

lemma runtime_eval (body length : Polynomial ℕ) (n : ℕ) :
    (runtime body length).eval n = n*(body.eval (length.eval n)+2*length.eval n+4)+2*length.eval n+4 := by
  simp [runtime]

noncomputable def certificate (enc : β → List Bool) (step : β → β) (start : α → β)
    (count : α → ℕ) (body : TM2ComputableInPolyTime enc enc step) (length : Polynomial ℕ)
    (growth : ∀ a i, i≤count a → (enc (step^[i] (start a))).length ≤
      length.eval (counted count enc start a).length) :
    TM2ComputableInPolyTime (counted count enc start) enc
      (fun a => step^[count a] (start a)) where
  tm := MachineRepeat.machine body.tm body.inputAlphabet body.outputAlphabet
  inputAlphabet := body.inputAlphabet
  outputAlphabet := body.inputAlphabet
  time := runtime body.time length
  outputsFun a := by
    let words : ℕ → List Bool := fun i => enc (step^[i] (start a))
    let budgets : ℕ → ℕ := fun i => body.time.eval (words i).length
    have runs (i : ℕ) (_hi : i<count a) :
        TM2OutputsInTime body.tm ((words i).map body.inputAlphabet.symm)
          (some ((words (i+1)).map body.outputAlphabet.symm)) (budgets i) := by
      simpa only [words,budgets,Function.iterate_succ_apply',Equiv.symm,Equiv.coe_fn_mk] using
        body.outputsFun (step^[i] (start a))
    let run := MachineRepeat.executeSequence body.tm body.inputAlphabet body.outputAlphabet
      (count a) words budgets runs
    have start_eq : encodeWord (count a) ++ words 0 = counted count enc start a := rfl
    rw [start_eq] at run
    refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
    let N := (counted count enc start a).length
    let L := length.eval N
    let B := body.time.eval L
    have hl (i : ℕ) (hi : i≤count a) : (words i).length≤L := growth a i hi
    have hb (i : ℕ) (hi : i<count a) : budgets i≤B :=
      MachineComposition.natPolynomial_eval_mono body.time (hl i hi.le)
    have hloop := MachineRepeat.loopBudget_le (count a) words budgets B L hb hl
    have hc : count a≤N := count_le count enc start a
    rw [runtime_eval]
    calc
      run.steps ≤ count a+1+MachineRepeat.loopBudget (count a) words budgets := run.steps_le_m
      _ ≤ count a+1+(count a*(B+2*L+3)+2*L+3) := Nat.add_le_add_left hloop _
      _ = count a*(B+2*L+4)+2*L+4 := by ring
      _ ≤ N*(B+2*L+4)+2*L+4 := by gcongr

end LargeIndependentSets.BoundedIteration

end OAI

namespace OAI

namespace BinPackingGap.MachineKeepDecision

section

open Turing IndependentSetsGames.Foundations
open Complexity

def frame : List Bool → List Bool
  | [] => [false]
  | bit :: rest => true :: bit :: frame rest

@[simp] theorem frame_length (word : List Bool) :
    (frame word).length = 2 * word.length + 1 := by
  induction word with
  | nil => rfl
  | cons bit rest ih => simp only [frame, List.length_cons, ih]; omega

def inputBits (p : List Bool × List Bool) : List Bool := frame p.1 ++ p.2

def outputBits (p : List Bool × Bool) : List Bool := p.2 :: p.1

def keep (decide : List Bool → Bool) (p : List Bool × List Bool) : List Bool × Bool :=
  (p.1, decide p.2)

@[simp] theorem inputBits_length (p : List Bool × List Bool) :
    (inputBits p).length = 2 * p.1.length + 1 + p.2.length := by
  simp [inputBits]

inductive ExtraTape
  | saved | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.saved, .output]

protected theorem ExtraTape.enumList_getElem?_ctorIdx_eq (x : ExtraTape) :
    ExtraTape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Phase
  | parse | transfer | finish
  deriving DecidableEq

protected abbrev Phase.enumList : List Phase := [.parse, .transfer, .finish]

protected theorem Phase.enumList_getElem?_ctorIdx_eq (x : Phase) :
    Phase.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Phase.enumList_nodup : Phase.enumList.Nodup := by decide

instance : Fintype Phase where
  elems := ⟨Phase.enumList, Phase.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape (M : FinTM2) := M.K ⊕ ExtraTape
abbrev Symbols (M : FinTM2) :=
  MachineEmbedding.Alphabet M.Γ (fun _ : ExtraTape => M.Γ M.k₀)
abbrev Label (M : FinTM2) := M.Λ ⊕ Phase
abbrev State (M : FinTM2) := M.σ × Option (M.Γ M.k₀)

def extraTapes (M : FinTM2) (saved output : List (M.Γ M.k₀)) :
    ExtraTape → List (M.Γ M.k₀)
  | .saved => saved
  | .output => output

def auxProgram (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool)
    (output : M.Γ M.k₁ ≃ Bool) : Phase → TM2.Stmt (Symbols M) (Label M) (State M)
  | .parse => .pop (.inl M.k₀) (fun s bit => (s.1, bit))
      (.branch (fun s => input (s.2.getD (input.symm false)))
        (.pop (.inl M.k₀) (fun s bit => (s.1, bit))
          (.push (.inr .saved) (fun s => s.2.getD (input.symm false))
            (.load (fun s => (s.1, none)) (.goto (fun _ => .inr .parse)))))
        (.load (fun s => (s.1, none)) (.goto (fun _ => .inl M.main))))
  | .transfer => IndependentSetsGames.Reduction.MachineTransfer.loopAt
      (K := Tape M) (Λ := Label M) (σ := M.σ) (Γ := Symbols M) (.inr .saved) (.inr .output)
      id (input.symm false) (.inr .transfer) (some (.inr .finish))
  | .finish => .pop (.inl M.k₁)
      (fun s bit => (s.1, bit.map (fun b => input.symm (output b))))
      (.push (.inr .output) (fun s => s.2.getD (input.symm false))
        (.load (fun _ => (M.initialState, none)) .halt))

def program (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool)
    (output : M.Γ M.k₁ ≃ Bool) : Label M → TM2.Stmt (Symbols M) (Label M) (State M) :=
  MachineEmbedding.program (some (.inr .transfer)) M.m (auxProgram M input output)

def machine (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool)
    (output : M.Γ M.k₁ ≃ Bool) : FinTM2 where
  K := Tape M
  kFin := by letI := M.kFin; exact inferInstanceAs (Fintype (Tape M))
  k₀ := .inl M.k₀
  k₁ := .inr .output
  Γ := Symbols M
  Λ := Label M
  ΛFin := by letI := M.ΛFin; exact inferInstanceAs (Fintype (Label M))
  main := .inr .parse
  σ := State M
  σFin := by
    letI := M.σFin
    letI := M.Γk₀Fin
    exact inferInstanceAs (Fintype (State M))
  initialState := (M.initialState, none)
  Γk₀Fin := M.Γk₀Fin
  m := program M input output

def inputTapes (M : FinTM2) (word saved : List (M.Γ M.k₀)) :
    (k : Tape M) → List (Symbols M k) :=
  MachineEmbedding.tapes (initList M word).stk (extraTapes M saved [])

@[simp] theorem inputTapes_input (M : FinTM2) (word saved : List (M.Γ M.k₀)) :
    inputTapes M word saved (.inl M.k₀) = word := by
  simp [inputTapes, initList]

@[simp] theorem inputTapes_saved (M : FinTM2) (word saved : List (M.Γ M.k₀)) :
    inputTapes M word saved (.inr .saved) = saved := rfl

def inputConfig (M : FinTM2) (word saved : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr .parse), (M.initialState, none), inputTapes M word saved⟩

def embedded (M : FinTM2) (saved : List (M.Γ M.k₀)) (c : M.Cfg) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  MachineEmbedding.configuration (some (.inr .transfer))
    (none : Option (M.Γ M.k₀)) (extraTapes M saved []) c

def returnTapes (M : FinTM2) (answer : M.Γ M.k₁) (word : List (M.Γ M.k₀)) :
    (k : Tape M) → List (Symbols M k) :=
  MachineEmbedding.tapes (haltList M [answer]).stk (extraTapes M [] word)

def returnConfig (M : FinTM2) (answer : M.Γ M.k₁) (word : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr .finish), (M.initialState, none), returnTapes M answer word⟩

private theorem inputTapes_update_input (M : FinTM2)
    (word saved replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word saved) (.inl M.k₀) replacement =
      inputTapes M replacement saved := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes, initList]
    · simp [inputTapes, initList, h]
  | inr k => simp [inputTapes]

private theorem inputTapes_update_saved (M : FinTM2)
    (word saved replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word saved) (.inr .saved) replacement =
      inputTapes M word replacement := by
  funext k
  cases k with
  | inl k => simp [inputTapes]
  | inr k => cases k <;> simp [inputTapes, extraTapes]

private def oneStep {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := le_refl _

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

theorem parseStep_digit (bit : Bool) (word saved : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M (input.symm true :: input.symm bit :: word) saved) =
    some (inputConfig M word (input.symm bit :: saved)) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState, none)
    (inputTapes M (input.symm true :: input.symm bit :: word) saved)) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_input, inputTapes_update_saved,
    inputConfig]

theorem parseStep_end (word saved : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M (input.symm false :: word) saved) =
    some (embedded M saved (initList M word)) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState, none) (inputTapes M (input.symm false :: word) saved)) = _
  simp only [auxProgram, TM2.stepAux, inputTapes_input, List.head?_cons,
    Option.getD_some, Equiv.apply_symm_apply, Bool.cond_false, List.tail_cons,
    inputTapes_update_input]
  rfl

theorem parseTrace (state : List Bool) (query saved : List (M.Γ M.k₀)) :
    (MachineComposition.advance (machine M input output).step)^[state.length + 1]
      (some (inputConfig M ((frame state).map input.symm ++ query) saved)) =
    some (embedded M (state.reverse.map input.symm ++ saved) (initList M query)) := by
  induction state generalizing saved with
  | nil =>
    simpa only [frame, List.map_singleton, List.singleton_append, List.length_nil,
      Nat.zero_add, List.reverse_nil, List.map_nil, List.nil_append,
      Function.iterate_one, MachineComposition.advance_some] using!
      parseStep_end M input output query saved
  | cons bit state ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (machine M input output).step)^[state.length + 1]
      ((machine M input output).step
        (inputConfig M ((frame (bit :: state)).map input.symm ++ query) saved)) = _
    simp only [frame, List.map_cons, List.cons_append]
    rw [parseStep_digit]
    simpa only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append] using! ih (input.symm bit :: saved)

private theorem inputConfig_init (word : List (M.Γ M.k₀)) :
    inputConfig M word [] = initList (machine M input output) word := by
  unfold inputConfig initList
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes, initList, machine]; rfl
    · simp [inputTapes, initList, machine, h]
  | inr k => cases k <;> simp [inputTapes, initList, machine, extraTapes]

def decisionExecution (saved query : List (M.Γ M.k₀))
    (answer : M.Γ M.k₁) (budget : Nat)
    (run : TM2OutputsInTime M query (some [answer]) budget) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M saved (initList M query))
      (some (embedded M saved (haltList M [answer]))) budget :=
  MachineComposition.embeddedExecution (some (.inr .transfer : Label M))
    (none : Option (M.Γ M.k₀)) (extraTapes M saved []) M.m
    (auxProgram M input output) run

private theorem returnTransfer_tapes (saved : List (M.Γ M.k₀)) (answer : M.Γ M.k₁) :
    IndependentSetsGames.Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .saved) (.inr .output)
      (embedded M saved (haltList M [answer])).stk [] saved.reverse =
    returnTapes M answer saved.reverse := by
  funext k
  cases k with
  | inl k => simp [IndependentSetsGames.Reduction.MachineTransfer.tapesAt, embedded,
      MachineEmbedding.configuration, returnTapes]
  | inr k => cases k <;> simp [IndependentSetsGames.Reduction.MachineTransfer.tapesAt, embedded,
      MachineEmbedding.configuration, returnTapes, extraTapes]

def returnTransfer (saved : List (M.Γ M.k₀)) (answer : M.Γ M.k₁) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M saved (haltList M [answer]))
      (some (returnConfig M answer saved.reverse)) (saved.length + 1) := by
  have run := IndependentSetsGames.Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inr .saved) (.inr .output) (by intro h; cases h)
    id (input.symm false) (.inr .transfer) (some (.inr .finish))
    (program M input output) rfl
    (embedded M saved (haltList M [answer])).stk M.initialState none
  have hs : (embedded M saved (haltList M [answer])).stk (.inr .saved) = saved := rfl
  have hd : (embedded M saved (haltList M [answer])).stk (.inr .output) = [] := rfl
  rw [hs, hd, List.map_id, List.append_nil, returnTransfer_tapes] at run
  exact run

private theorem finish_tapes (answer : M.Γ M.k₁) (word : List (M.Γ M.k₀)) :
    Function.update
      (Function.update (returnTapes M answer word) (.inl M.k₁) [])
      (.inr .output) (input.symm (output answer) :: word) =
    (haltList (machine M input output) (input.symm (output answer) :: word)).stk := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₁
    · subst k; simp [returnTapes, haltList, machine]
    · simp [returnTapes, haltList, machine, h]
  | inr k =>
    cases k <;> simp [returnTapes, haltList, machine, extraTapes]
    rfl

theorem finishStep (answer : M.Γ M.k₁) (word : List (M.Γ M.k₀)) :
    (machine M input output).step (returnConfig M answer word) =
    some (haltList (machine M input output) (input.symm (output answer) :: word)) := by
  have ha : returnTapes M answer word (.inl M.k₁) = [answer] := by
    simp [returnTapes, haltList]
  have hw : returnTapes M answer word (.inr .output) = word := rfl
  change some (TM2.stepAux (auxProgram M input output .finish)
    (M.initialState, none) (returnTapes M answer word)) = _
  simp only [auxProgram, TM2.stepAux, ha, List.head?_cons, List.tail_cons,
    Option.map_some, Option.getD_some]
  have hw' : (Function.update (returnTapes M answer word) (.inl M.k₁) [])
      (.inr .output) = word := by simp [hw]
  rw [hw', finish_tapes]
  rfl

def outputsInTime (state query : List Bool) (answer : Bool) (budget : Nat)
    (run : TM2OutputsInTime M (query.map input.symm)
      (some [output.symm answer]) budget) :
    TM2OutputsInTime (machine M input output)
      ((frame state ++ query).map input.symm)
      (some ((answer :: state).map input.symm))
      (budget + 2 * state.length + 3) := by
  let parsed : StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M ((frame state).map input.symm ++ query.map input.symm) [])
      (some (embedded M (state.reverse.map input.symm)
        (initList M (query.map input.symm)))) (state.length + 1) := {
    steps := state.length + 1
    evals_in_steps := by
      change (MachineComposition.advance (machine M input output).step)^[state.length + 1] _ = _
      simpa only [List.append_nil] using!
        parseTrace M input output state (query.map input.symm) []
    steps_le_m := le_refl _ }
  have decision := decisionExecution M input output (state.reverse.map input.symm)
    (query.map input.symm) (output.symm answer) budget run
  have transfer := returnTransfer M input output (state.reverse.map input.symm)
    (output.symm answer)
  have restored : (state.reverse.map input.symm).reverse = state.map input.symm := by
    rw [List.map_reverse, List.reverse_reverse]
  rw [restored, List.length_map, List.length_reverse] at transfer
  have finish := oneStep _ _ _ (finishStep M input output
    (output.symm answer) (state.map input.symm))
  simp only [Equiv.apply_symm_apply] at finish
  have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ parsed decision
  have second := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first transfer
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ second finish
  rw [inputConfig_init] at full
  simp only [← List.map_append] at full
  refine { toEvalsTo := full.toEvalsTo, steps_le_m := ?_ }
  have h := full.steps_le_m
  omega

noncomputable def computation (decide : List Bool → Bool)
    (certificate : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) decide) :
    TM2ComputableInPolyTime inputBits outputBits (keep decide) where
  tm := machine certificate.tm certificate.inputAlphabet certificate.outputAlphabet
  inputAlphabet := certificate.inputAlphabet
  outputAlphabet := certificate.inputAlphabet
  time := certificate.time + Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun pair := by
    have run := outputsInTime certificate.tm certificate.inputAlphabet
      certificate.outputAlphabet pair.1 pair.2 (decide pair.2)
      (certificate.time.eval pair.2.length) (certificate.outputsFun pair.2)
    have hq : pair.2.length ≤ (inputBits pair).length := by
      rw [inputBits_length]; omega
    have hs : pair.1.length ≤ (inputBits pair).length := by
      rw [inputBits_length]; omega
    have ht := MachineComposition.natPolynomial_eval_mono certificate.time hq
    refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
    have hr := run.steps_le_m
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
    omega

end

open Turing IndependentSetsGames.Foundations.Complexity

def typedInputBits {α : Type} (encode : α → List Bool) (p : α × List Bool) : List Bool :=
  inputBits (encode p.1, p.2)

def typedOutputBits {α : Type} (encode : α → List Bool) (p : α × Bool) : List Bool :=
  p.2 :: encode p.1

def typedKeep {α : Type} (decide : List Bool → Bool) (p : α × List Bool) : α × Bool :=
  (p.1, decide p.2)

noncomputable def computationWithSavedCodec {α : Type} (encode : α → List Bool)
    (decide : List Bool → Bool)
    (certificate : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) decide) :
    TM2ComputableInPolyTime (typedInputBits encode) (typedOutputBits encode)
      (typedKeep decide) where
  tm := (computation decide certificate).tm
  inputAlphabet := (computation decide certificate).inputAlphabet
  outputAlphabet := (computation decide certificate).outputAlphabet
  time := (computation decide certificate).time
  outputsFun p := (computation decide certificate).outputsFun (encode p.1, p.2)

end BinPackingGap.MachineKeepDecision

end OAI

end

-- Driver.lean
section
namespace A203914.Search.Wire
open OMA.S_oeis_a203914 Turing
open OAI.IndependentSetsGames.Foundations.Complexity


abbrev W := List Bool
abbrev T := W × Nat × Nat
abbrev R := W × Nat × W
def U (k : Nat) := List.replicate k true
def S (s : T) := delimit s.1 ++ delimit (U s.2.1) ++ U s.2.2
def V (r : R) := query r.1 r.2.1 r.2.2
def tq (s : T) := query s.1 s.2.2 []
def rq (r : R) := query r.1 r.2.1 (r.2.2 ++ [false])
def tnext (L : DecisionProblem) (s : T) : T := (s.1,s.2.1,if L (tq s) then s.2.2 else s.2.2-1)
def rnext (L : DecisionProblem) (r : R) : R := (r.1,r.2.1,r.2.2 ++ [!(L (rq r))])
def start (g : W) : T := (g,g.length.sqrt,g.length.sqrt*g.length.sqrt)
def enter (s : T) : R := (s.1,s.2.2,[])
def tc (g : W) := (start g).2.2
def rc (s : T) := s.2.1
abbrev CT := OAI.LargeIndependentSets.BoundedIteration.counted tc S start
abbrev CR := OAI.LargeIndependentSets.BoundedIteration.counted rc V enter
def tout (L : DecisionProblem) (g : W) := (tnext L)^[tc g] (start g)
def rout (L : DecisionProblem) (s : T) := (rnext L)^[rc s] (enter s)
lemma tdet (L : DecisionProblem) (g : W) (n i k : Nat) :
    ∃ j ≤ k, (tnext L)^[i] (g,n,k)=(g,n,j) := by
  induction i generalizing k with
  | zero => exact ⟨k,le_rfl,rfl⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply]; unfold tnext
    split <;> (obtain ⟨j,h,e⟩ := ih _; exact ⟨j,by dsimp at h; omega,e⟩)
lemma rdet (L : DecisionProblem) (g : W) (k i : Nat) (p : W) :
    (rnext L)^[i] (g,k,p) = (g,k,recover (fun p => L (query g k p)) i p) := by
  induction i generalizing p with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply]; exact ih _
lemma recover_len (f : W → Bool) (i : Nat) (p : W) : (recover f i p).length=p.length+i := by
  induction i generalizing p with
  | zero => simp [recover]
  | succ i ih => simp [recover,ih]; omega
lemma tresult (L : DecisionProblem) (g : W) (n k : Nat) :
    (tnext L)^[k] (g,n,k)=(g,n,threshold (fun j => L (query g j [])) k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases h : L (query g (k+1) []) with
    | false => rw [Function.iterate_succ_apply]; simpa [tnext,tq,h,threshold] using ih
    | true =>
      have f : tnext L (g,n,k+1)=(g,n,k+1) := by simp [tnext,tq,h]
      simpa [threshold,h] using Function.iterate_fixed f (k+1)
theorem exact_driver (L : DecisionProblem) (g : W) : (rout L (tout L g)).2.2 = driver L g := by
  simp [tout,tc,start,tresult,rout,rc,enter,rdet,driver,search]
@[simp] theorem lenS (g : W) (n k : Nat) : (S (g,n,k)).length=2*g.length+2*n+k+2 := by simp [S,delimit_length,U]; omega
@[simp] theorem lenV (g p : W) (k : Nat) : (V (g,k,p)).length=2*g.length+2*k+p.length+2 := query_length ..
noncomputable def tloop (L : DecisionProblem) (m : TM2ComputableInPolyTime S S (tnext L)) :
    TM2ComputableInPolyTime CT S (tout L) := by
  apply OAI.LargeIndependentSets.BoundedIteration.certificate _ _ _ _ m Polynomial.X
  intro g i hi
  obtain ⟨j,h,e⟩ := tdet L g g.length.sqrt i (tc g)
  change (S ((tnext L)^[i] (g,g.length.sqrt,tc g))).length ≤ _
  rw [e]; simp [OAI.LargeIndependentSets.BoundedIteration.counted,Polynomial.eval_X,start,tc] at *; omega
noncomputable def rloop (L : DecisionProblem) (m : TM2ComputableInPolyTime V V (rnext L)) :
    TM2ComputableInPolyTime CR V (rout L) := by
  apply OAI.LargeIndependentSets.BoundedIteration.certificate _ _ _ _ m Polynomial.X
  rintro ⟨g,n,k⟩ i hi
  simp [OAI.LargeIndependentSets.BoundedIteration.counted,rc,enter,rdet,recover_len] at *; omega
end A203914.Search.Wire

end

-- WordAlgebra.lean
section
/- Word-machine algebra adapted from OpenAI OAI KMedianRecovery, commit 3344da59991ed94f9ba711217b29c1d760badfa6. -/
namespace OAI.MetricKMedianRecovery
def pairBits (p : List Bool × List Bool) : List Bool :=
  p.1.flatMap (fun b => [true, b]) ++ [false] ++ p.2


end OAI.MetricKMedianRecovery

/- Machines/Program -/
namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

structure Program where
  K : Type
  [kDecidableEq : DecidableEq K]
  [kFinite : Fintype K]
  input : K
  output : K
  Label : Type
  [labelFinite : Fintype Label]
  main : Label
  State : Type
  [stateFinite : Fintype State]
  initial : State
  code : Label → TM2.Stmt (fun _ : K => Bool) Label State

instance (p : Program) : DecidableEq p.K := p.kDecidableEq
instance (p : Program) : Fintype p.K := p.kFinite
instance (p : Program) : Fintype p.Label := p.labelFinite
instance (p : Program) : Fintype p.State := p.stateFinite

abbrev Program.machine (p : Program) : FinTM2 where
  K := p.K
  k₀ := p.input
  k₁ := p.output
  Γ _ := Bool
  Λ := p.Label
  main := p.main
  σ := p.State
  initialState := p.initial
  m := p.code

abbrev Stacks (K : Type) := K → List Bool

noncomputable def embedStacks {K L : Type} (e : K ↪ L) (s : Stacks K) : Stacks L := by
  classical
  exact fun l => if h : ∃ k, e k = l then s h.choose else []

lemma embedStacks_apply {K L : Type} (e : K ↪ L) (s : Stacks K) (k : K) :
    embedStacks e s (e k) = s k := by
  classical
  simp only [embedStacks,dif_pos (show ∃ j, e j = e k from ⟨k,rfl⟩)]
  congr 1
  exact e.injective (Classical.choose_spec (show ∃ j, e j = e k from ⟨k,rfl⟩))

lemma embedStacks_not_image {K L : Type} (e : K ↪ L) (s : Stacks K) (l : L)
    (h : ¬∃ k, e k = l) : embedStacks e s l = [] := by
  classical
  simp only [embedStacks,dif_neg h]

lemma embedStacks_update {K L : Type} [DecidableEq K] [DecidableEq L]
    (e : K ↪ L) (s : Stacks K) (k : K) (v : List Bool) :
    embedStacks e (Function.update s k v) = Function.update (embedStacks e s) (e k) v := by
  classical
  funext l
  by_cases h : ∃ j, e j = l
  · obtain ⟨j,rfl⟩ := h
    simp only [embedStacks_apply,Function.update_apply,e.injective.eq_iff]
  · rw [embedStacks_not_image e _ l h,Function.update_of_ne (by intro he; exact h ⟨k,he.symm⟩),
      embedStacks_not_image e s l h]

section Rename
variable {K L A B S T : Type} [DecidableEq K] [DecidableEq L]

def renameStmt (ek : K ↪ L) (el : A → B) (es : S → T) (rs : T → S)
    (ret : Option B) : TM2.Stmt (fun _ : K => Bool) A S → TM2.Stmt (fun _ : L => Bool) B T
  | .push k f q => .push (ek k) (fun t => f (rs t)) (renameStmt ek el es rs ret q)
  | .peek k f q => .peek (ek k) (fun t b => es (f (rs t) b)) (renameStmt ek el es rs ret q)
  | .pop k f q => .pop (ek k) (fun t b => es (f (rs t) b)) (renameStmt ek el es rs ret q)
  | .load f q => .load (fun t => es (f (rs t))) (renameStmt ek el es rs ret q)
  | .branch f q r => .branch (fun t => f (rs t))
      (renameStmt ek el es rs ret q) (renameStmt ek el es rs ret r)
  | .goto f => .goto (fun t => el (f (rs t)))
  | .halt => match ret with | none => .halt | some b => .goto (fun _ => b)

noncomputable def renameCfg (ek : K ↪ L) (el : A → B) (es : S → T)
    (ret : Option B) (c : TM2.Cfg (fun _ : K => Bool) A S) : TM2.Cfg (fun _ : L => Bool) B T :=
  ⟨c.l.elim ret (fun a => some (el a)), es c.var, embedStacks ek c.stk⟩

lemma stepAux_rename (ek : K ↪ L) (el : A → B) (es : S → T) (rs : T → S)
    (h : ∀ s, rs (es s) = s) (ret : Option B)
    (q : TM2.Stmt (fun _ : K => Bool) A S) (s : S) (stk : Stacks K) :
    TM2.stepAux (renameStmt ek el es rs ret q) (es s) (embedStacks ek stk) =
      renameCfg ek el es ret (TM2.stepAux q s stk) := by
  induction q generalizing s stk with
  | push k f q ih =>
    simp only [renameStmt,TM2.stepAux,h,embedStacks_apply,←embedStacks_update]
    exact ih _ _
  | peek k f q ih =>
    simp only [renameStmt,TM2.stepAux,h,embedStacks_apply]
    exact ih _ _
  | pop k f q ih =>
    simp only [renameStmt,TM2.stepAux,h,embedStacks_apply,←embedStacks_update]
    exact ih _ _
  | load f q ih =>
    simp only [renameStmt,TM2.stepAux,h]
    exact ih _ _
  | branch f q r ihq ihr =>
    simp only [renameStmt,TM2.stepAux,h]
    cases f s <;> simp only [Bool.cond_false,Bool.cond_true]
    · exact ihr _ _
    · exact ihq _ _
  | goto f => simp only [renameStmt,TM2.stepAux,h,renameCfg,Option.elim_some]
  | halt => cases ret <;> rfl

end Rename

lemma iterate_transfer {S T : Type} (f : S → Option S) (g : T → Option T) (e : S → T)
    (h : ∀ s s', f s = some s' → g (e s) = some (e s')) (n : ℕ) (s s' : S)
    (he : (fun x : Option S => x.bind f)^[n] (some s) = some s') :
    (fun x : Option T => x.bind g)^[n] (some (e s)) = some (e s') := by
  induction n generalizing s with
  | zero => simpa only [Function.iterate_zero_apply,Option.some.injEq] using congrArg e (Option.some.inj he)
  | succ n ih =>
    rw [Function.iterate_succ_apply] at he ⊢
    change (fun x : Option S => x.bind f)^[n] (f s) = some s' at he
    change (fun x : Option T => x.bind g)^[n] (g (e s)) = some (e s')
    cases hf : f s with
    | none =>
      rw [hf] at he
      have hn : (fun x : Option S => x.bind f)^[n] none = none :=
        Function.iterate_fixed rfl n
      rw [hn] at he
      contradiction
    | some t =>
      rw [h s t hf]
      exact ih t (by simpa only [hf] using he)

end MetricKMedianRecovery.BitMachine

end OAI

/- Recovery/Stack -/
namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

lemma embedStacks_empty {K L : Type} (e : K ↪ L) :
    embedStacks e (fun _ => []) = fun _ => [] := by
  classical
  funext l
  simp only [embedStacks]
  split <;> rfl

lemma embedStacks_pure {K L : Type} [DecidableEq K] [DecidableEq L]
    (e : K ↪ L) (k : K) (bits : List Bool) :
    embedStacks e (Function.update (fun _ => []) k bits) =
      Function.update (fun _ => []) (e k) bits := by
  rw [embedStacks_update,embedStacks_empty]

lemma initList_bool (p : Program) (bits : List Bool) :
    initList p.machine bits = ⟨some p.main,p.initial,Function.update (fun _ => []) p.input bits⟩ := by
  unfold initList
  congr 1
  funext k
  simp only [Program.machine,Function.update_apply]
  split <;> rfl

lemma haltList_bool (p : Program) (bits : List Bool) :
    haltList p.machine bits = ⟨none,p.initial,Function.update (fun _ => []) p.output bits⟩ := by
  unfold haltList
  congr 1
  funext k
  simp only [Program.machine,Function.update_apply]
  split <;> rfl

namespace Composition
variable (p q : Program)

abbrev Stack := p.K ⊕ {k : q.K // k ≠ q.input}

def leftStack : p.K ↪ Stack p q := ⟨Sum.inl,Sum.inl_injective⟩

def rightStack : q.K ↪ Stack p q where
  toFun k := if h : k = q.input then Sum.inl p.output else Sum.inr ⟨k,h⟩
  inj' := by
    intro k j h
    by_cases hk : k = q.input <;> by_cases hj : j = q.input
    · exact hk.trans hj.symm
    · simp only [dif_pos hk,dif_neg hj] at h
      contradiction
    · simp only [dif_neg hk,dif_pos hj] at h
      contradiction
    · simp only [dif_neg hk,dif_neg hj,Sum.inr.injEq,Subtype.mk.injEq] at h
      exact h

@[simp] lemma rightStack_input : rightStack p q q.input = Sum.inl p.output := by
  simp [rightStack]

noncomputable abbrev program : Program where
  K := Stack p q
  input := Sum.inl p.input
  output := rightStack p q q.output
  Label := p.Label ⊕ q.Label
  main := Sum.inl p.main
  State := p.State × q.State
  initial := (p.initial,q.initial)
  code := fun l => match l with
    | .inl l => renameStmt (leftStack p q) Sum.inl (fun s => (s,q.initial)) Prod.fst
        (some (Sum.inr q.main)) (p.code l)
    | .inr l => renameStmt (rightStack p q) Sum.inr (fun s => (p.initial,s)) Prod.snd
        none (q.code l)

noncomputable def leftCfg : p.machine.Cfg → (program p q).machine.Cfg :=
  renameCfg (leftStack p q) Sum.inl (fun s => (s,q.initial)) (some (Sum.inr q.main))

noncomputable def rightCfg : q.machine.Cfg → (program p q).machine.Cfg :=
  renameCfg (rightStack p q) Sum.inr (fun s => (p.initial,s)) none

lemma left_step (s t : p.machine.Cfg) (h : p.machine.step s = some t) :
    (program p q).machine.step (leftCfg p q s) = some (leftCfg p q t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt (leftStack p q) Sum.inl
      (fun s => (s,q.initial)) Prod.fst (some (Sum.inr q.main)) (p.code l))
        (v,q.initial) (embedStacks (leftStack p q) stk)) = _
    rw [stepAux_rename _ _ _ _ (fun _ => rfl)]
    rfl

lemma right_step (s t : q.machine.Cfg) (h : q.machine.step s = some t) :
    (program p q).machine.step (rightCfg p q s) = some (rightCfg p q t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt (rightStack p q) Sum.inr
      (fun s => (p.initial,s)) Prod.snd none (q.code l))
        (p.initial,v) (embedStacks (rightStack p q) stk)) = _
    rw [stepAux_rename _ _ _ _ (fun _ => rfl)]
    rfl

lemma left_initial (bits : List Bool) :
    leftCfg p q (initList p.machine bits) = initList (program p q).machine bits := by
  rw [initList_bool,initList_bool]
  change (⟨some (Sum.inl p.main),(p.initial,q.initial),
      embedStacks (leftStack p q) (Function.update (fun _ => []) p.input bits)⟩ : (program p q).machine.Cfg) = _
  rw [embedStacks_pure]
  rfl

lemma handoff (bits : List Bool) :
    leftCfg p q (haltList p.machine bits) = rightCfg p q (initList q.machine bits) := by
  rw [haltList_bool,initList_bool]
  change (⟨some (Sum.inr q.main),(p.initial,q.initial),
    embedStacks (leftStack p q) (Function.update (fun _ => []) p.output bits)⟩ : (program p q).machine.Cfg) =
    ⟨some (Sum.inr q.main),(p.initial,q.initial),
    embedStacks (rightStack p q) (Function.update (fun _ => []) q.input bits)⟩
  rw [embedStacks_pure,embedStacks_pure,rightStack_input]
  rfl

lemma right_final (bits : List Bool) :
    rightCfg p q (haltList q.machine bits) = haltList (program p q).machine bits := by
  rw [haltList_bool,haltList_bool]
  change (⟨none,(p.initial,q.initial),
      embedStacks (rightStack p q) (Function.update (fun _ => []) q.output bits)⟩ : (program p q).machine.Cfg) = _
  rw [embedStacks_pure]

noncomputable def outputs {x y z : List Bool} {m n : ℕ}
    (hp : TM2OutputsInTime p.machine x (some y) m)
    (hq : TM2OutputsInTime q.machine y (some z) n) :
    TM2OutputsInTime (program p q).machine x (some z) (n+m) := by
  have h1 := iterate_transfer p.machine.step (program p q).machine.step (leftCfg p q)
    (left_step p q) hp.steps (initList p.machine x) (haltList p.machine y) hp.evals_in_steps
  have h2 := iterate_transfer q.machine.step (program p q).machine.step (rightCfg p q)
    (right_step p q) hq.steps (initList q.machine y) (haltList q.machine z) hq.evals_in_steps
  rw [left_initial,handoff] at h1
  rw [right_final] at h2
  refine ⟨⟨hq.steps+hp.steps,?_⟩,Nat.add_le_add hq.steps_le_m hp.steps_le_m⟩
  change (fun x : Option (program p q).machine.Cfg => x.bind (program p q).machine.step)^[hq.steps+hp.steps]
    (some (initList (program p q).machine x)) = some (haltList (program p q).machine z)
  rw [Function.iterate_add_apply,h1,h2]

end Composition
end MetricKMedianRecovery.BitMachine

end OAI

/- Recovery/StackLength -/
namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

section Length
variable {K A S : Type} [DecidableEq K] [Fintype K]

def stackLength (stk : Stacks K) : ℕ := ∑ k, (stk k).length

def pushBound : TM2.Stmt (fun _ : K => Bool) A S → ℕ
  | .push _ _ q => pushBound q + 1
  | .peek _ _ q => pushBound q
  | .pop _ _ q => pushBound q
  | .load _ q => pushBound q
  | .branch _ q r => max (pushBound q) (pushBound r)
  | .goto _ => 0
  | .halt => 0

lemma stackLength_pure (k : K) (bits : List Bool) :
    stackLength (Function.update (fun _ => []) k bits) = bits.length := by
  simp [stackLength,Function.update_apply,apply_ite]

lemma stackLength_update_le (stk : Stacks K) (k : K) (bits : List Bool) (d : ℕ)
    (h : bits.length ≤ (stk k).length+d) :
    stackLength (Function.update stk k bits) ≤ stackLength stk + d := by
  have he : (fun j => (Function.update stk k bits j).length) =
      Function.update (fun j => (stk j).length) k bits.length := by
    funext j
    simp only [Function.update_apply]
    split <;> rfl
  unfold stackLength
  rw [he,Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hs := Finset.sum_eq_add_sum_sdiff_singleton_of_mem (s := Finset.univ)
    (f := fun j => (stk j).length) (Finset.mem_univ k)
  omega

lemma stepAux_length (stmt : TM2.Stmt (fun _ : K => Bool) A S) (s : S) (stk : Stacks K) :
    stackLength (TM2.stepAux stmt s stk).stk ≤ stackLength stk + pushBound stmt := by
  induction stmt generalizing s stk with
  | push k f q ih =>
    apply (ih s (Function.update stk k (f s :: stk k))).trans
    have hl := stackLength_update_le stk k (f s :: stk k) 1 (by simp)
    change _ ≤ _ + (pushBound q+1)
    omega
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    apply (ih _ (Function.update stk k (stk k).tail)).trans
    have hl := stackLength_update_le stk k (stk k).tail 0 (by simp)
    change _ ≤ _ + pushBound q
    omega
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
    simp only [TM2.stepAux,pushBound]
    cases hf : f s <;> simp only [Bool.cond_false,Bool.cond_true]
    · exact (ihr _ _).trans (Nat.add_le_add_left (le_max_right _ _) _)
    · exact (ihq _ _).trans (Nat.add_le_add_left (le_max_left _ _) _)
  | goto f => simp only [TM2.stepAux,pushBound,Nat.add_zero,le_refl]
  | halt => simp only [TM2.stepAux,pushBound,Nat.add_zero,le_refl]

end Length

noncomputable def Program.maxPush (p : Program) : ℕ := Finset.univ.sup (fun l => pushBound (p.code l))

lemma Program.step_length (p : Program) (s t : p.machine.Cfg) (h : p.machine.step s = some t) :
    stackLength t.stk ≤ stackLength s.stk + p.maxPush := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    have hb : pushBound (p.code l) ≤ p.maxPush :=
      Finset.le_sup (f := fun l => pushBound (p.code l)) (Finset.mem_univ l)
    exact (stepAux_length (p.code l) v stk).trans (Nat.add_le_add_left hb _)

lemma iterate_length {S : Type} (f : S → Option S) (len : S → ℕ) (c : ℕ)
    (h : ∀ s t, f s = some t → len t ≤ len s+c) (n : ℕ) (s t : S)
    (he : (fun x : Option S => x.bind f)^[n] (some s) = some t) :
    len t ≤ len s+n*c := by
  induction n generalizing s with
  | zero =>
    have ht : s = t := Option.some.inj he
    subst t
    omega
  | succ n ih =>
    rw [Function.iterate_succ_apply] at he
    change (fun x : Option S => x.bind f)^[n] (f s) = some t at he
    cases hf : f s with
    | none =>
      rw [hf,Function.iterate_fixed rfl n] at he
      contradiction
    | some u =>
      have hi := ih u (by simpa only [hf] using he)
      have hs := h s u hf
      simp only [Nat.succ_mul]
      omega

lemma Program.output_length (p : Program) {x y : List Bool} {m : ℕ}
    (h : TM2OutputsInTime p.machine x (some y) m) :
    y.length ≤ x.length+m*p.maxPush := by
  have hl := iterate_length p.machine.step (fun s => stackLength s.stk) p.maxPush
    p.step_length h.steps (initList p.machine x) (haltList p.machine y) h.evals_in_steps
  simp only [initList_bool,haltList_bool,stackLength_pure] at hl
  exact hl.trans (Nat.add_le_add_left (Nat.mul_le_mul_right p.maxPush h.steps_le_m) _)

structure PolyComputes (f : List Bool → List Bool) where
  program : Program
  time : Polynomial ℕ
  outputs : ∀ x, TM2OutputsInTime program.machine x (some (f x)) (time.eval x.length)

noncomputable def PolyComputes.toTM2 {f : List Bool → List Bool} (h : PolyComputes f) :
    Turing.TM2ComputableInPolyTime id id f where
  tm := h.program.machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := h.time
  outputsFun x := by simpa using h.outputs x

lemma polynomial_monotone (P : Polynomial ℕ) : Monotone (fun n => P.eval n) := by
  intro n m h
  simp only [Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i))

noncomputable def PolyComputes.comp {f g : List Bool → List Bool}
    (hf : PolyComputes f) (hg : PolyComputes g) : PolyComputes (g ∘ f) where
  program := Composition.program hf.program hg.program
  time := hg.time.comp (Polynomial.X + hf.time * Polynomial.C hf.program.maxPush) + hf.time
  outputs x := by
    have hlen := hf.program.output_length (hf.outputs x)
    have hh := Composition.outputs hf.program hg.program (hf.outputs x) (hg.outputs (f x))
    refine ⟨hh.toEvalsTo,?_⟩
    apply hh.steps_le_m.trans
    simp only [Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X]
    exact Nat.add_le_add_right (polynomial_monotone hg.time hlen) _

end MetricKMedianRecovery.BitMachine

end OAI

/- Recovery/StepThen -/
namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

lemma unit_update {α : Type} (f : Unit → α) (a : α) :
    Function.update f () a = fun _ => a := by
  funext u
  cases u
  simp only [Function.update_self]

noncomputable def step_then {S : Type} {f : S → Option S} {s t : S} {z : Option S} {n : ℕ}
    (h : f s = some t) (ht : EvalsToInTime f t z n) : EvalsToInTime f s z (n+1) := by
  refine ⟨⟨ht.steps+1,?_⟩,Nat.add_le_add_right ht.steps_le_m 1⟩
  rw [Function.iterate_succ_apply]
  change (fun x : Option S => x.bind f)^[ht.steps] (f s) = z
  rw [h]
  exact ht.evals_in_steps

noncomputable def time_mono {S : Type} {f : S → Option S} {s : S} {z : Option S} {m n : ℕ}
    (h : EvalsToInTime f s z m) (hm : m ≤ n) : EvalsToInTime f s z n :=
  ⟨h.toEvalsTo,h.steps_le_m.trans hm⟩

noncomputable def one_step {S : Type} {f : S → Option S} {s t : S}
    (h : f s = some t) : EvalsToInTime f s (some t) 1 :=
  ⟨⟨1,h⟩,le_rfl⟩

def discardPrefix : List Bool → List Bool
  | true :: _ :: bits => discardPrefix bits
  | true :: [] => []
  | false :: bits => bits
  | [] => []

lemma discardPrefix_pair (x y : List Bool) :
    discardPrefix (x.flatMap (fun b => [true,b]) ++ [false] ++ y) = y := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa only [List.flatMap_cons,List.cons_append,List.nil_append,discardPrefix] using ih

abbrev tailProgram : Program where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Option Bool
  initial := none
  code _ := .pop () (fun _ b => b)
    (.branch (fun s => decide (s = some true))
      (.pop () (fun _ _ => none) (.goto (fun _ => ())))
      (.load (fun _ => none) .halt))

def tailCfg (xs : List Bool) : tailProgram.machine.Cfg := ⟨some (),none,fun _ => xs⟩
def tailEnd (xs : List Bool) : tailProgram.machine.Cfg := ⟨none,none,fun _ => xs⟩

lemma tail_initial (xs : List Bool) : initList tailProgram.machine xs = tailCfg xs := by
  exact (initList_bool tailProgram xs).trans
    (congrArg (fun stk : Unit → List Bool => (⟨some (),none,stk⟩ : tailProgram.machine.Cfg))
      (unit_update (fun _ => []) xs))

lemma tail_final (xs : List Bool) : haltList tailProgram.machine xs = tailEnd xs := by
  exact (haltList_bool tailProgram xs).trans
    (congrArg (fun stk : Unit → List Bool => (⟨none,none,stk⟩ : tailProgram.machine.Cfg))
      (unit_update (fun _ => []) xs))

lemma tail_step_nil : tailProgram.machine.step (tailCfg []) = some (tailEnd []) := by
  simp [FinTM2.step,tailCfg,tailEnd,tailProgram,TM2.step,TM2.stepAux]
  rfl

lemma tail_step_false (xs : List Bool) :
    tailProgram.machine.step (tailCfg (false::xs)) = some (tailEnd xs) := by
  simp [FinTM2.step,tailCfg,tailEnd,tailProgram,TM2.step,TM2.stepAux,unit_update]
  rfl

lemma tail_step_true (xs : List Bool) :
    tailProgram.machine.step (tailCfg (true::xs)) = some (tailCfg xs.tail) := by
  simp [FinTM2.step,tailCfg,tailProgram,TM2.step,TM2.stepAux,unit_update]
  rfl

noncomputable def tail_outputs (xs : List Bool) :
    EvalsToInTime tailProgram.machine.step (tailCfg xs) (some (tailEnd (discardPrefix xs)))
      (xs.length+1) := by
  induction xs using List.twoStepInduction with
  | nil => exact one_step tail_step_nil
  | singleton b =>
    cases b with
    | false => exact time_mono (one_step (tail_step_false [])) (by decide)
    | true => exact step_then (tail_step_true []) (one_step tail_step_nil)
  | cons_cons b c xs ih _ihc =>
    cases b with
    | false => exact time_mono (one_step (tail_step_false (c::xs))) (by simp)
    | true =>
      have hh := step_then (tail_step_true (c::xs)) ih
      exact time_mono hh (by simp)

noncomputable def discardPrefix_computes : PolyComputes discardPrefix where
  program := tailProgram
  time := Polynomial.X+1
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,tail_initial,tail_final,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using tail_outputs xs

def twoStacks (xs ys : List Bool) : Stacks Bool := fun k => cond k ys xs

@[simp] lemma twoStacks_false (xs ys : List Bool) : twoStacks xs ys false = xs := rfl
@[simp] lemma twoStacks_true (xs ys : List Bool) : twoStacks xs ys true = ys := rfl

lemma twoStacks_update_false (xs ys zs : List Bool) :
    Function.update (twoStacks xs ys) false zs = twoStacks zs ys := by
  funext b
  cases b <;> rfl

lemma twoStacks_update_true (xs ys zs : List Bool) :
    Function.update (twoStacks xs ys) true zs = twoStacks xs zs := by
  funext b
  cases b <;> rfl

lemma twoStacks_pure_false (xs : List Bool) :
    Function.update (fun _ : Bool => []) false xs = twoStacks xs [] := by
  funext b
  cases b <;> rfl

lemma twoStacks_pure_true (xs : List Bool) :
    Function.update (fun _ : Bool => []) true xs = twoStacks [] xs := by
  funext b
  cases b <;> rfl

abbrev reverseProgram : Program where
  K := Bool
  input := false
  output := true
  Label := Unit
  main := ()
  State := Option Bool
  initial := none
  code _ := .pop false (fun _ b => b)
    (.branch Option.isSome
      (.push true (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => ()))))
      (.load (fun _ => none) .halt))

def reverseCfg (xs ys : List Bool) : reverseProgram.machine.Cfg :=
  ⟨some (),none,twoStacks xs ys⟩
def reverseEnd (ys : List Bool) : reverseProgram.machine.Cfg :=
  ⟨none,none,twoStacks [] ys⟩

lemma reverse_initial (xs : List Bool) : initList reverseProgram.machine xs = reverseCfg xs [] := by
  exact (initList_bool reverseProgram xs).trans
    (congrArg (fun stk : Stacks Bool => (⟨some (),none,stk⟩ : reverseProgram.machine.Cfg))
      (twoStacks_pure_false xs))

lemma reverse_final (xs : List Bool) : haltList reverseProgram.machine xs = reverseEnd xs := by
  exact (haltList_bool reverseProgram xs).trans
    (congrArg (fun stk : Stacks Bool => (⟨none,none,stk⟩ : reverseProgram.machine.Cfg))
      (twoStacks_pure_true xs))

lemma reverse_step_nil (ys : List Bool) :
    reverseProgram.machine.step (reverseCfg [] ys) = some (reverseEnd ys) := by
  simp [FinTM2.step,reverseCfg,reverseEnd,reverseProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

lemma reverse_step_cons (b : Bool) (xs ys : List Bool) :
    reverseProgram.machine.step (reverseCfg (b::xs) ys) = some (reverseCfg xs (b::ys)) := by
  simp [FinTM2.step,reverseCfg,reverseProgram,TM2.step,TM2.stepAux,
    twoStacks_update_false,twoStacks_update_true]
  rfl

noncomputable def reverse_outputs (xs ys : List Bool) :
    EvalsToInTime reverseProgram.machine.step (reverseCfg xs ys) (some (reverseEnd (xs.reverse++ys)))
      (xs.length+1) := by
  induction xs generalizing ys with
  | nil => exact one_step (reverse_step_nil ys)
  | cons b xs ih =>
    have hh := step_then (reverse_step_cons b xs ys) (ih (b::ys))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hh

noncomputable def reverse_computes : PolyComputes List.reverse where
  program := reverseProgram
  time := Polynomial.X+1
  outputs xs := by
    simpa only [List.append_nil,TM2OutputsInTime,Option.map_some,reverse_initial,reverse_final,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using reverse_outputs xs []

end MetricKMedianRecovery.BitMachine

end OAI

/- Sampling/ExtractPrefix -/
namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

def extractPrefix : List Bool → List Bool
  | true :: b :: bits => b :: extractPrefix bits
  | _ => []

lemma extractPrefix_pair (x y : List Bool) :
    extractPrefix (x.flatMap (fun b => [true,b]) ++ [false] ++ y) = x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    simpa only [List.flatMap_cons,List.cons_append,List.nil_append,extractPrefix] using congrArg (List.cons b) ih

abbrev headProgram : Program where
  K := Bool
  input := false
  output := true
  Label := Bool
  main := false
  State := Option Bool
  initial := none
  code l := if l then
    .pop false (fun _ b => b)
      (.branch Option.isSome
        (.load (fun _ => none) (.goto (fun _ => true)))
        (.load (fun _ => none) .halt))
    else
    .pop false (fun _ b => b)
      (.branch (fun s => decide (s = some true))
        (.pop false (fun _ b => b)
          (.branch Option.isSome
            (.push true (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => false))))
            (.load (fun _ => none) .halt)))
        (.load (fun _ => none) (.goto (fun _ => true))))

def headCfg (l : Bool) (xs ys : List Bool) : headProgram.machine.Cfg :=
  ⟨some l,none,twoStacks xs ys⟩
def headEnd (ys : List Bool) : headProgram.machine.Cfg :=
  ⟨none,none,twoStacks [] ys⟩

lemma head_initial (xs : List Bool) : initList headProgram.machine xs = headCfg false xs [] := by
  exact (initList_bool headProgram xs).trans
    (congrArg (fun stk : Stacks Bool => (⟨some false,none,stk⟩ : headProgram.machine.Cfg))
      (twoStacks_pure_false xs))

lemma head_final (xs : List Bool) : haltList headProgram.machine xs = headEnd xs := by
  exact (haltList_bool headProgram xs).trans
    (congrArg (fun stk : Stacks Bool => (⟨none,none,stk⟩ : headProgram.machine.Cfg))
      (twoStacks_pure_true xs))

lemma head_clear_nil (ys : List Bool) :
    headProgram.machine.step (headCfg true [] ys) = some (headEnd ys) := by
  simp [FinTM2.step,headCfg,headEnd,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

lemma head_clear_cons (b : Bool) (xs ys : List Bool) :
    headProgram.machine.step (headCfg true (b::xs) ys) = some (headCfg true xs ys) := by
  simp [FinTM2.step,headCfg,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

noncomputable def head_clear_outputs (xs ys : List Bool) :
    EvalsToInTime headProgram.machine.step (headCfg true xs ys) (some (headEnd ys)) (xs.length+1) := by
  induction xs with
  | nil => exact one_step (head_clear_nil ys)
  | cons b xs ih => exact step_then (head_clear_cons b xs ys) ih

lemma head_step_nil (ys : List Bool) :
    headProgram.machine.step (headCfg false [] ys) = some (headCfg true [] ys) := by
  simp [FinTM2.step,headCfg,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

lemma head_step_one (ys : List Bool) :
    headProgram.machine.step (headCfg false [true] ys) = some (headEnd ys) := by
  simp [FinTM2.step,headCfg,headEnd,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

lemma head_step_false (xs ys : List Bool) :
    headProgram.machine.step (headCfg false (false::xs) ys) = some (headCfg true xs ys) := by
  simp [FinTM2.step,headCfg,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

lemma head_step_true (b : Bool) (xs ys : List Bool) :
    headProgram.machine.step (headCfg false (true::b::xs) ys) = some (headCfg false xs (b::ys)) := by
  simp [FinTM2.step,headCfg,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false,twoStacks_update_true]
  rfl

noncomputable def head_outputs (xs ys : List Bool) :
    EvalsToInTime headProgram.machine.step (headCfg false xs ys)
      (some (headEnd ((extractPrefix xs).reverse++ys))) (xs.length+2) := by
  induction xs using List.twoStepInduction generalizing ys with
  | nil => exact step_then (head_step_nil ys) (one_step (head_clear_nil ys))
  | singleton b =>
    cases b with
    | false => exact time_mono (step_then (head_step_false [] ys) (head_clear_outputs [] ys)) (by decide)
    | true => exact time_mono (one_step (head_step_one ys)) (by decide)
  | cons_cons b c xs ih _ =>
    cases b with
    | false =>
      exact time_mono (step_then (head_step_false (c::xs) ys) (head_clear_outputs (c::xs) ys)) (by simp)
    | true =>
      have hh := step_then (head_step_true c xs ys) (ih (c::ys))
      simp only [extractPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def extractReverse_computes : PolyComputes (fun xs => (extractPrefix xs).reverse) where
  program := headProgram
  time := Polynomial.X+2
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,head_initial,head_final,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat,List.append_nil] using head_outputs xs []

noncomputable def extractPrefix_computes : PolyComputes extractPrefix := by
  have hh := extractReverse_computes.comp reverse_computes
  simpa only [Function.comp_def,List.reverse_reverse] using hh

end MetricKMedianRecovery.BitMachine

end OAI

/- Recovery/FrameStacks -/
namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

def frameStacks {K L : Type} (s : Stacks K) (t : Stacks L) : Stacks (K⊕L) := Sum.elim s t

@[simp] lemma frameStacks_inl {K L : Type} (s : Stacks K) (t : Stacks L) (k : K) :
    frameStacks s t (.inl k)=s k := rfl

@[simp] lemma frameStacks_inr {K L : Type} (s : Stacks K) (t : Stacks L) (k : L) :
    frameStacks s t (.inr k)=t k := rfl

lemma frameStacks_update {K L : Type} [DecidableEq K] [DecidableEq L]
    (s : Stacks K) (t : Stacks L) (k : K) (xs : List Bool) :
    frameStacks (Function.update s k xs) t = Function.update (frameStacks s t) (.inl k) xs := by
  funext i
  cases i <;> simp [frameStacks,Function.update_apply]

lemma stepAux_frame {K L A B S T : Type} [DecidableEq K] [DecidableEq L]
    (el : A → B) (es : S → T) (rs : T → S) (h : ∀ s,rs (es s)=s)
    (ret : Option B) (q : TM2.Stmt (fun _ : K => Bool) A S)
    (s : S) (stk : Stacks K) (extra : Stacks L) :
    TM2.stepAux (renameStmt (Function.Embedding.inl) el es rs ret q) (es s)
      (frameStacks stk extra) =
    ⟨(TM2.stepAux q s stk).l.elim ret (fun a => some (el a)),
      es (TM2.stepAux q s stk).var,frameStacks (TM2.stepAux q s stk).stk extra⟩ := by
  induction q generalizing s stk with
  | push k f q ih =>
    simpa only [renameStmt,TM2.stepAux,h,Function.Embedding.inl_apply,frameStacks_inl,
      ←frameStacks_update] using ih s (Function.update stk k (f s::stk k))
  | peek k f q ih =>
    simpa only [renameStmt,TM2.stepAux,h,Function.Embedding.inl_apply,frameStacks_inl] using
      ih (f s (stk k).head?) stk
  | pop k f q ih =>
    simpa only [renameStmt,TM2.stepAux,h,Function.Embedding.inl_apply,frameStacks_inl,
      ←frameStacks_update] using ih (f s (stk k).head?) (Function.update stk k (stk k).tail)
  | load f q ih => simpa only [renameStmt,TM2.stepAux,h] using ih (f s) stk
  | branch f q r ihq ihr =>
    simp only [renameStmt,TM2.stepAux,h]
    cases f s <;> simp only [Bool.cond_false,Bool.cond_true]
    · exact ihr _ _
    · exact ihq _ _
  | goto f => simp only [renameStmt,TM2.stepAux,h,Option.elim_some]
  | halt => cases ret <;> rfl

lemma extractPrefix_length (bits : List Bool) : (extractPrefix bits).length≤bits.length := by
  induction bits using List.twoStepInduction with
  | nil => simp [extractPrefix]
  | singleton b => cases b <;> simp [extractPrefix]
  | cons_cons b c bits ih _ =>
    cases b <;> simp only [extractPrefix,List.length_cons,List.length_nil] <;> omega

namespace MapLeft
variable (p : Program)

abbrev Stack := p.K ⊕ Fin 2
abbrev Label := p.Label ⊕ Fin 4
abbrev State := p.State × Option Bool

def mapStacks (s : Stacks p.K) (a b : List Bool) : Stacks (Stack p) := frameStacks s ![a,b]
@[simp] lemma stacks_left (s : Stacks p.K) (a b : List Bool) (k : p.K) :
    mapStacks p s a b (.inl k)=s k := rfl
@[simp] lemma stacks_zero (s : Stacks p.K) (a b : List Bool) :
    mapStacks p s a b (.inr 0)=a := rfl
@[simp] lemma stacks_one (s : Stacks p.K) (a b : List Bool) :
    mapStacks p s a b (.inr 1)=b := rfl
lemma updLeft (s : Stacks p.K) (a b t : List Bool) (k : p.K) :
    Function.update (mapStacks p s a b) (.inl k) t=mapStacks p (Function.update s k t) a b :=
  (frameStacks_update _ _ _ _).symm
lemma upd0 (s : Stacks p.K) (a b t : List Bool) :
    Function.update (mapStacks p s a b) (.inr 0) t=mapStacks p s t b := by
  funext i
  cases i with
  | inl k => simp [mapStacks]
  | inr k => fin_cases k <;> simp [mapStacks]
lemma upd1 (s : Stacks p.K) (a b t : List Bool) :
    Function.update (mapStacks p s a b) (.inr 1) t=mapStacks p s a t := by
  funext i
  cases i with
  | inl k => simp [mapStacks]
  | inr k => fin_cases k <;> simp [mapStacks]

abbrev program : Program where
  K := Stack p
  input := .inr 1
  output := .inr 1
  Label := Label p
  main := .inr 0
  State := State p
  initial := (p.initial,none)
  code l := match l with
    | .inl i => renameStmt Function.Embedding.inl Sum.inl (fun s => (s,none)) Prod.fst
        (some (.inr 2)) (p.code i)
    | .inr i => if i=0 then
        .pop (.inr 1) (fun s b => (s.1,b))
          (.branch (fun s => decide (s.2=some true))
            (.pop (.inr 1) (fun s b => (s.1,b))
              (.branch (fun s => s.2.isSome)
                (.push (.inr 0) (fun s => s.2.getD false)
                  (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 0))))
                (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 1)))))
            (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 1))))
      else if i=1 then
        .pop (.inr 0) (fun s b => (s.1,b))
          (.branch (fun s => s.2.isSome)
            (.push (.inl p.input) (fun s => s.2.getD false)
              (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 1))))
            (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inl p.main))))
      else if i=2 then
        .pop (.inl p.output) (fun s b => (s.1,b))
          (.branch (fun s => s.2.isSome)
            (.push (.inr 0) (fun s => s.2.getD false)
              (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 2))))
            (.push (.inr 1) (fun _ => false)
              (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 3)))))
      else
        .pop (.inr 0) (fun s b => (s.1,b))
          (.branch (fun s => s.2.isSome)
            (.push (.inr 1) (fun s => s.2.getD false)
              (.push (.inr 1) (fun _ => true)
                (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 3)))))
            (.load (fun _ => (p.initial,none)) .halt))

def pure (k : p.K) (xs : List Bool) : Stacks p.K := Function.update (fun _ => []) k xs
lemma pure_at (k : p.K) (xs : List Bool) : pure p k xs k=xs := by simp [pure]
lemma pure_update (k : p.K) (xs ys : List Bool) :
    Function.update (pure p k xs) k ys=pure p k ys := Function.update_idem ..
lemma pure_nil (k : p.K) : pure p k []=fun _ => [] := by simp [pure]

def cfg (l : Label p) (s : Stacks p.K) (a b : List Bool) : (program p).machine.Cfg :=
  ⟨some l,(p.initial,none),mapStacks p s a b⟩
def done (ys : List Bool) : (program p).machine.Cfg :=
  ⟨none,(p.initial,none),mapStacks p (fun _ => []) [] ys⟩

def runCfg (ys : List Bool) (c : p.machine.Cfg) : (program p).machine.Cfg :=
  ⟨c.l.elim (some (.inr 2)) (fun l => some (.inl l)),(c.var,none),mapStacks p c.stk [] ys⟩

lemma run_step (ys : List Bool) (s t : p.machine.Cfg) (h : p.machine.step s=some t) :
    (program p).machine.step (runCfg p ys s)=some (runCfg p ys t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt Function.Embedding.inl Sum.inl (fun s => (s,none))
      Prod.fst (some (.inr 2)) (p.code l)) (v,none) (frameStacks stk ![[],ys]))=_
    rw [stepAux_frame _ _ _ (fun _ => rfl)]
    rfl

lemma parse_nil (a : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (fun _=>[]) a [])=
      some (cfg p (.inr 1) (fun _=>[]) a []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1]; rfl
lemma parse_false (xs a : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (fun _=>[]) a (false::xs))=
      some (cfg p (.inr 1) (fun _=>[]) a xs) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1]; rfl
lemma parse_one (a : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (fun _=>[]) a [true])=
      some (cfg p (.inr 1) (fun _=>[]) a []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1]; rfl
lemma parse_true (b : Bool) (xs a : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (fun _=>[]) a (true::b::xs))=
      some (cfg p (.inr 0) (fun _=>[]) (b::a) xs) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,upd1]; rfl
lemma restore_nil (xs ys : List Bool) :
    (program p).machine.step (cfg p (.inr 1) (pure p p.input xs) [] ys)=
      some (cfg p (.inl p.main) (pure p p.input xs) [] ys) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma restore_cons (b : Bool) (a xs ys : List Bool) :
    (program p).machine.step (cfg p (.inr 1) (pure p p.input xs) (b::a) ys)=
      some (cfg p (.inr 1) (pure p p.input (b::xs)) a ys) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,updLeft,pure_at,pure_update]; rfl
lemma reverse_nil (a ys : List Bool) :
    (program p).machine.step (cfg p (.inr 2) (pure p p.output []) a ys)=
      some (cfg p (.inr 3) (fun _=>[]) a (false::ys)) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,updLeft,upd1,pure_nil]; rfl
lemma reverse_cons (b : Bool) (xs a ys : List Bool) :
    (program p).machine.step (cfg p (.inr 2) (pure p p.output (b::xs)) a ys)=
      some (cfg p (.inr 2) (pure p p.output xs) (b::a) ys) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,updLeft,upd0,pure_at,pure_update]; rfl
lemma encode_nil (ys : List Bool) :
    (program p).machine.step (cfg p (.inr 3) (fun _=>[]) [] ys)=some (done p ys) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,done,upd0]; rfl
lemma encode_cons (b : Bool) (xs ys : List Bool) :
    (program p).machine.step (cfg p (.inr 3) (fun _=>[]) (b::xs) ys)=
      some (cfg p (.inr 3) (fun _=>[]) xs (true::b::ys)) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,upd1]; rfl

end MapLeft
end MetricKMedianRecovery.BitMachine

end OAI

/- Recovery/EvalTrans -/
namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
noncomputable def eval_trans {S : Type} {f : S → Option S} {s t : S} {z : Option S} {m n : ℕ}
    (h1 : EvalsToInTime f s (some t) m) (h2 : EvalsToInTime f t z n) : EvalsToInTime f s z (n+m) := by
  refine ⟨⟨h2.steps+h1.steps,?_⟩,Nat.add_le_add h2.steps_le_m h1.steps_le_m⟩
  change (fun s : Option S => s.bind f)^[h2.steps+h1.steps] (some s) = z
  have e1 : (fun s : Option S => s.bind f)^[h1.steps] (some s) = some t := h1.evals_in_steps
  have e2 : (fun s : Option S => s.bind f)^[h2.steps] (some t) = z := h2.evals_in_steps
  rw [Function.iterate_add_apply,e1,e2]

namespace MapLeft
variable (p : Program)

noncomputable def parse_phase (bits a : List Bool) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 0) (fun _=>[]) a bits)
      (some (cfg p (.inr 1) (fun _=>[]) ((extractPrefix bits).reverse++a) (discardPrefix bits)))
      (bits.length+1) := by
  induction bits using List.twoStepInduction generalizing a with
  | nil => exact one_step (parse_nil p a)
  | singleton b =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_false p [] a)) (by decide : 1≤2)
    | true => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_one p a)) (by decide : 1≤2)
  | cons_cons b c bits ih _ =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append] using
        time_mono (one_step (parse_false p (c::bits) a)) (by simp : 1≤(false::c::bits).length+1)
    | true =>
      have hh := step_then (parse_true p c bits a) (ih (c::a))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def restore_phase (a xs ys : List Bool) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 1) (pure p p.input xs) a ys)
      (some (cfg p (.inl p.main) (pure p p.input (a.reverse++xs)) [] ys)) (a.length+1) := by
  induction a generalizing xs with
  | nil => exact one_step (restore_nil p xs ys)
  | cons b a ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (restore_cons p b a xs ys) (ih (b::xs))

noncomputable def reverse_phase (xs a ys : List Bool) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 2) (pure p p.output xs) a ys)
      (some (cfg p (.inr 3) (fun _=>[]) (xs.reverse++a) (false::ys))) (xs.length+1) := by
  induction xs generalizing a with
  | nil => exact one_step (reverse_nil p a ys)
  | cons b xs ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (reverse_cons p b xs a ys) (ih (b::a))

noncomputable def encode_phase (xs ys : List Bool) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 3) (fun _=>[]) xs ys)
      (some (done p (xs.reverse.flatMap (fun b => [true,b])++ys))) (xs.length+1) := by
  induction xs generalizing ys with
  | nil => exact one_step (encode_nil p ys)
  | cons b xs ih =>
    simpa only [List.length_cons,List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      step_then (encode_cons p b xs ys) (ih (true::b::ys))

lemma initial (xs : List Bool) : initList (program p).machine xs=cfg p (.inr 0) (fun _=>[]) [] xs := by
  rw [initList_bool]
  congr 1
  have he : (fun _ : Stack p => ([] : List Bool))=mapStacks p (fun _=>[]) [] [] := by
    funext i
    cases i with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  rw [he,upd1]
lemma final (xs : List Bool) : haltList (program p).machine xs=done p xs := by
  rw [haltList_bool]
  congr 1
  have he : (fun _ : Stack p => ([] : List Bool))=mapStacks p (fun _=>[]) [] [] := by
    funext i
    cases i with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  rw [he,upd1]
lemma run_initial (xs ys : List Bool) :
    runCfg p ys (initList p.machine xs)=cfg p (.inl p.main) (pure p p.input xs) [] ys := by
  rw [initList_bool]
  rfl
lemma run_final (xs ys : List Bool) :
    runCfg p ys (haltList p.machine xs)=cfg p (.inr 2) (pure p p.output xs) [] ys := by
  rw [haltList_bool]
  rfl

noncomputable def outputs (bits out : List Bool) (n : ℕ)
    (h : TM2OutputsInTime p.machine (extractPrefix bits) (some out) n) :
    TM2OutputsInTime (program p).machine bits (some (pairBits (out,discardPrefix bits)))
      (n+2*bits.length+2*out.length+4) := by
  let xs := extractPrefix bits
  let ys := discardPrefix bits
  have hparse := parse_phase p bits []
  simp only [List.append_nil] at hparse
  have hrestore := restore_phase p xs.reverse [] ys
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hrestore
  rw [pure_nil] at hrestore
  have hrun : EvalsToInTime (program p).machine.step
      (runCfg p ys (initList p.machine xs)) (some (runCfg p ys (haltList p.machine out))) n := by
    refine ⟨⟨h.steps,?_⟩,h.steps_le_m⟩
    exact iterate_transfer _ _ (runCfg p ys) (run_step p ys) h.steps _ _ h.evals_in_steps
  rw [run_initial,run_final] at hrun
  have hreverse := reverse_phase p out [] ys
  simp only [List.append_nil] at hreverse
  have hencode := encode_phase p out.reverse (false::ys)
  simp only [List.reverse_reverse,List.length_reverse] at hencode
  have hh := eval_trans hparse (eval_trans hrestore (eval_trans hrun (eval_trans hreverse hencode)))
  simp only [TM2OutputsInTime,Option.map_some,initial,final,pairBits,List.append_assoc,List.cons_append,List.nil_append]
  apply time_mono hh
  have hl : xs.length≤bits.length := extractPrefix_length bits
  omega

end MapLeft

noncomputable def PolyComputes.mapLeft {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun bits => pairBits (f (extractPrefix bits),discardPrefix bits)) where
  program := MapLeft.program hf.program
  time := hf.time+2*Polynomial.X+2*(Polynomial.X+hf.time*Polynomial.C hf.program.maxPush)+4
  outputs bits := by
    have hh := MapLeft.outputs hf.program bits (f (extractPrefix bits))
      (hf.time.eval (extractPrefix bits).length) (hf.outputs (extractPrefix bits))
    have hx := extractPrefix_length bits
    have ho := hf.program.output_length (hf.outputs (extractPrefix bits))
    have ht := polynomial_monotone hf.time hx
    apply time_mono hh
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_C]
    nlinarith

end MetricKMedianRecovery.BitMachine

end OAI

/- Recovery/Store -/
namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace ProductBits

def store (a b c : List Bool) : Stacks (Fin 3) := ![a,b,c]
@[simp] lemma store0 (a b c : List Bool) : store a b c 0=a := rfl
@[simp] lemma store1 (a b c : List Bool) : store a b c 1=b := rfl
@[simp] lemma store2 (a b c : List Bool) : store a b c 2=c := rfl
lemma upd0 (a b c t : List Bool) : Function.update (store a b c) 0 t=store t b c := by
  funext i; fin_cases i <;> simp [store]
lemma upd1 (a b c t : List Bool) : Function.update (store a b c) 1 t=store a t c := by
  funext i; fin_cases i <;> simp [store]
lemma upd2 (a b c t : List Bool) : Function.update (store a b c) 2 t=store a b t := by
  funext i; fin_cases i <;> simp [store]

abbrev program (duplicate : Bool) : Program where
  K := Fin 3
  input := 0
  output := 0
  Label := Fin 4
  main := 0
  State := Option Bool
  initial := none
  code l := if l=0 then
    if duplicate then
      .pop 0 (fun _ b => b)
        (.branch Option.isSome
          (.push 1 (fun s => s.getD false)
            (.push 2 (fun s => s.getD false)
              (.load (fun _=>none) (.goto (fun _=>0)))))
          (.load (fun _=>none) (.goto (fun _=>2))))
    else
      .pop 0 (fun _ b => b)
        (.branch (fun s => decide (s=some true))
          (.pop 0 (fun _ b => b)
            (.branch Option.isSome
              (.push 1 (fun s => s.getD false) (.load (fun _=>none) (.goto (fun _=>0))))
              (.load (fun _=>none) (.goto (fun _=>1)))))
          (.load (fun _=>none) (.goto (fun _=>1))))
    else if l=1 then
      .pop 0 (fun _ b => b)
        (.branch Option.isSome
          (.push 2 (fun s => s.getD false) (.load (fun _=>none) (.goto (fun _=>1))))
          (.load (fun _=>none) (.goto (fun _=>2))))
    else if l=2 then
      .pop 1 (fun _ b => b)
        (.branch Option.isSome
          (.push 0 (fun s => s.getD false) (.load (fun _=>none) (.goto (fun _=>2))))
          (.push 0 (fun _=>false) (.load (fun _=>none) (.goto (fun _=>3)))))
    else
      .pop 2 (fun _ b => b)
        (.branch Option.isSome
          (.push 0 (fun s=>s.getD false)
            (.push 0 (fun _=>true) (.load (fun _=>none) (.goto (fun _=>3)))))
          (.load (fun _=>none) .halt))

def cfg (mode : Bool) (l : Fin 4) (a b c : List Bool) : (program mode).machine.Cfg :=
  ⟨some l,none,store a b c⟩
def done (mode : Bool) (out : List Bool) : (program mode).machine.Cfg :=
  ⟨none,none,store out [] []⟩
lemma copy_nil (b c : List Bool) :
    (program true).machine.step (cfg true 0 [] b c)=some (cfg true 2 [] b c) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma copy_cons (x : Bool) (a b c : List Bool) :
    (program true).machine.step (cfg true 0 (x::a) b c)=some (cfg true 0 a (x::b) (x::c)) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,upd1,upd2]; rfl
lemma parse_nil (b : List Bool) :
    (program false).machine.step (cfg false 0 [] b [])=some (cfg false 1 [] b []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma parse_false (a b : List Bool) :
    (program false).machine.step (cfg false 0 (false::a) b [])=some (cfg false 1 a b []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma parse_one (b : List Bool) :
    (program false).machine.step (cfg false 0 [true] b [])=some (cfg false 1 [] b []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma parse_true (x : Bool) (a b : List Bool) :
    (program false).machine.step (cfg false 0 (true::x::a) b [])=some (cfg false 0 a (x::b) []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,upd1]; rfl
lemma reverse_nil (mode : Bool) (b c : List Bool) :
    (program mode).machine.step (cfg mode 1 [] b c)=some (cfg mode 2 [] b c) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma reverse_cons (mode x : Bool) (a b c : List Bool) :
    (program mode).machine.step (cfg mode 1 (x::a) b c)=some (cfg mode 1 a b (x::c)) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,upd2]; rfl
lemma restore_nil (mode : Bool) (a c : List Bool) :
    (program mode).machine.step (cfg mode 2 a [] c)=some (cfg mode 3 (false::a) [] c) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1,upd0]; rfl
lemma restore_cons (mode x : Bool) (a b c : List Bool) :
    (program mode).machine.step (cfg mode 2 a (x::b) c)=some (cfg mode 2 (x::a) b c) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1,upd0]; rfl
lemma encode_nil (mode : Bool) (a : List Bool) :
    (program mode).machine.step (cfg mode 3 a [] [])=some (done mode a) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,done,upd2]; rfl
lemma encode_cons (mode x : Bool) (a c : List Bool) :
    (program mode).machine.step (cfg mode 3 a [] (x::c))=some (cfg mode 3 (true::x::a) [] c) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd2,upd0]; rfl

noncomputable def copy_phase (a b c : List Bool) :
    EvalsToInTime (program true).machine.step (cfg true 0 a b c)
      (some (cfg true 2 [] (a.reverse++b) (a.reverse++c))) (a.length+1) := by
  induction a generalizing b c with
  | nil => exact one_step (copy_nil b c)
  | cons x a ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (copy_cons x a b c) (ih (x::b) (x::c))

noncomputable def parse_phase (a b : List Bool) :
    EvalsToInTime (program false).machine.step (cfg false 0 a b [])
      (some (cfg false 1 (discardPrefix a) ((extractPrefix a).reverse++b) [])) (a.length+1) := by
  induction a using List.twoStepInduction generalizing b with
  | nil => exact one_step (parse_nil b)
  | singleton x =>
    cases x with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_false [] b)) (by decide : 1≤2)
    | true => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_one b)) (by decide : 1≤2)
  | cons_cons x y a ih _ =>
    cases x with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append] using
        time_mono (one_step (parse_false (y::a) b)) (by simp : 1≤(false::y::a).length+1)
    | true =>
      have hh := step_then (parse_true y a b) (ih (y::b))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def reverse_phase (mode : Bool) (a b c : List Bool) :
    EvalsToInTime (program mode).machine.step (cfg mode 1 a b c)
      (some (cfg mode 2 [] b (a.reverse++c))) (a.length+1) := by
  induction a generalizing c with
  | nil => exact one_step (reverse_nil mode b c)
  | cons x a ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (reverse_cons mode x a b c) (ih (x::c))

noncomputable def restore_phase (mode : Bool) (a b c : List Bool) :
    EvalsToInTime (program mode).machine.step (cfg mode 2 a b c)
      (some (cfg mode 3 (false::(b.reverse++a)) [] c)) (b.length+1) := by
  induction b generalizing a with
  | nil => exact one_step (restore_nil mode a c)
  | cons x b ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (restore_cons mode x a b c) (ih (x::a))

noncomputable def encode_phase (mode : Bool) (a c : List Bool) :
    EvalsToInTime (program mode).machine.step (cfg mode 3 a [] c)
      (some (done mode (c.reverse.flatMap (fun b=>[true,b])++a))) (c.length+1) := by
  induction c generalizing a with
  | nil => exact one_step (encode_nil mode a)
  | cons x c ih =>
    simpa only [List.length_cons,List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      step_then (encode_cons mode x a c) (ih (true::x::a))

lemma initial (mode : Bool) (xs : List Bool) : initList (program mode).machine xs=cfg mode 0 xs [] [] := by
  rw [initList_bool]
  congr 1
  funext i; fin_cases i <;> simp [program,store]
lemma final (mode : Bool) (xs : List Bool) : haltList (program mode).machine xs=done mode xs := by
  rw [haltList_bool]
  congr 1
  funext i; fin_cases i <;> simp [program,store]

noncomputable def duplicate_computes : PolyComputes (fun xs => pairBits (xs,xs)) where
  program := program true
  time := 3*Polynomial.X+3
  outputs xs := by
    have h1 := copy_phase xs [] []
    have h2 := restore_phase true [] xs.reverse xs.reverse
    have h3 := encode_phase true (false::xs) xs.reverse
    simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h2 h3
    have hh := eval_trans h1 (eval_trans h2 h3)
    simp only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,pairBits,List.append_assoc,List.cons_append,List.nil_append]
    exact time_mono hh (by omega)

lemma projections_length (xs : List Bool) :
    (extractPrefix xs).length≤xs.length ∧ (discardPrefix xs).length≤xs.length := by
  induction xs using List.twoStepInduction with
  | nil => simp [extractPrefix,discardPrefix]
  | singleton b => cases b <;> simp [extractPrefix,discardPrefix]
  | cons_cons b c xs ih _ => cases b <;> simp only [extractPrefix,discardPrefix,List.length_cons,List.length_nil] <;> omega

noncomputable def swap_computes : PolyComputes (fun xs => pairBits (discardPrefix xs,extractPrefix xs)) where
  program := program false
  time := 4*Polynomial.X+4
  outputs xs := by
    let a := extractPrefix xs
    let b := discardPrefix xs
    have h1 := parse_phase xs []
    have h2 := reverse_phase false b a.reverse []
    have h3 := restore_phase false [] a.reverse b.reverse
    have h4 := encode_phase false (false::a) b.reverse
    simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h2 h3 h4
    have hh := eval_trans h1 (eval_trans h2 (eval_trans h3 h4))
    simp only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,pairBits,List.append_assoc,List.cons_append,List.nil_append]
    apply time_mono hh
    have hp := projections_length xs
    change a.length≤xs.length ∧ b.length≤xs.length at hp
    omega

end ProductBits

noncomputable def PolyComputes.pair {f g : List Bool → List Bool}
    (hf : PolyComputes f) (hg : PolyComputes g) : PolyComputes (fun xs=>pairBits (f xs,g xs)) := by
  have h := (((ProductBits.duplicate_computes.comp hf.mapLeft).comp ProductBits.swap_computes).comp
    hg.mapLeft).comp ProductBits.swap_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] using h

end MetricKMedianRecovery.BitMachine

end OAI

/- Encoding/PushWord -/
namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

def pushWord {K L S : Type} (k : K) : List Bool → TM2.Stmt (fun _ : K=>Bool) L S → TM2.Stmt (fun _ : K=>Bool) L S
  | [],c => c
  | b::bs,c => pushWord k bs (.push k (fun _=>b) c)

lemma pushWord_step {K L S : Type} [DecidableEq K] (k : K) (bs : List Bool)
    (c : TM2.Stmt (fun _ : K=>Bool) L S) (v : S) (s : Stacks K) :
    TM2.stepAux (pushWord k bs c) v s=TM2.stepAux c v (Function.update s k (bs++s k)) := by
  induction bs generalizing c with
  | nil => simp only [pushWord,List.nil_append,Function.update_eq_self]
  | cons b bs ih =>
    rw [pushWord,ih]
    simp only [TM2.stepAux,Function.update_self,Function.update_idem,List.cons_append]

namespace FiniteFold
variable {Q : Type} [Fintype Q] (q₀ : Q) (next : Q → Bool → Q) (out : Q → List Bool)

abbrev program : Program where
  K := Unit
  input := ()
  output := ()
  Label := Option Q
  main := none
  State := Q × Option Bool
  initial := (q₀,none)
  code l := match l with
    | none => .pop () (fun q b=>(q.1,b))
      (.branch (fun q=>q.2.isSome)
        (.load (fun q=>(next q.1 (q.2.getD false),none)) (.goto (fun _=>none)))
        (.goto (fun q=>some q.1)))
    | some q => pushWord () (out q) (.load (fun _=>(q₀,none)) .halt)

def cfg (q : Q) (xs : List Bool) : (program q₀ next out).machine.Cfg :=
  ⟨some none,(q,none),fun _=>xs⟩
def finish (q : Q) : (program q₀ next out).machine.Cfg :=
  ⟨some (some q),(q,none),fun _=>[]⟩
def done (xs : List Bool) : (program q₀ next out).machine.Cfg :=
  ⟨none,(q₀,none),fun _=>xs⟩

lemma nil_step (q : Q) : (program q₀ next out).machine.step (cfg q₀ next out q [])=
    some (finish q₀ next out q) := by
  simp [FinTM2.step,program,cfg,finish,TM2.step,TM2.stepAux]
  rfl
lemma cons_step (q : Q) (b : Bool) (xs : List Bool) :
    (program q₀ next out).machine.step (cfg q₀ next out q (b::xs))=
      some (cfg q₀ next out (next q b) xs) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,unit_update]
  rfl
lemma finish_step (q : Q) : (program q₀ next out).machine.step (finish q₀ next out q)=
    some (done q₀ next out (out q)) := by
  simp [FinTM2.step,program,finish,done,TM2.step,pushWord_step,TM2.stepAux,unit_update]
  rfl

noncomputable def outputs (q : Q) (xs : List Bool) :
    EvalsToInTime (program q₀ next out).machine.step (cfg q₀ next out q xs)
      (some (done q₀ next out (out (xs.foldl next q)))) (xs.length+2) := by
  induction xs generalizing q with
  | nil => exact step_then (nil_step q₀ next out q) (one_step (finish_step q₀ next out q))
  | cons b xs ih =>
    simpa only [List.foldl_cons,List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
      step_then (cons_step q₀ next out q b xs) (ih (next q b))

lemma initial (xs : List Bool) : initList (program q₀ next out).machine xs=cfg q₀ next out q₀ xs := by
  rw [initList_bool]
  congr 1
lemma final (xs : List Bool) : haltList (program q₀ next out).machine xs=done q₀ next out xs := by
  rw [haltList_bool]
  congr 1

noncomputable def computes : PolyComputes (fun xs=>out (xs.foldl next q₀)) where
  program := program q₀ next out
  time := Polynomial.X+2
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_ofNat] using outputs q₀ next out q₀ xs

end FiniteFold

lemma fold_orElse (xs : List Bool) (q : Option Bool) :
    xs.foldl (fun q b=>q.orElse (fun _=>some b)) q=q.orElse (fun _=>xs.head?) := by
  induction xs generalizing q with
  | nil => simp
  | cons b xs ih =>
    rw [List.foldl_cons,ih]
    cases q <;> simp

noncomputable def head_computes : PolyComputes (fun xs=>[xs.head?.getD false]) := by
  have hh := FiniteFold.computes (none : Option Bool) (fun q b=>q.orElse (fun _=>some b)) (fun q=>[q.getD false])
  simpa only [fold_orElse,Option.orElse_none] using hh

lemma fold_empty (xs : List Bool) (q : Bool) :
    xs.foldl (fun _ _=>false) q=if xs=[] then q else false := by
  induction xs generalizing q with
  | nil => simp
  | cons b xs ih => simp [ih]

noncomputable def isEmpty_computes : PolyComputes (fun xs=>[decide (xs=[])]) := by
  have hh := FiniteFold.computes true (fun _ _=>false) (fun q=>[q])
  simpa [fold_empty] using hh

end MetricKMedianRecovery.BitMachine

end OAI

/- Recovery/Store2 -/
namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace WordOperations

def store (xs ys : List Bool) : Stacks (Fin 2) := ![xs,ys]
@[simp] lemma store0 (xs ys : List Bool) : store xs ys 0=xs := rfl
@[simp] lemma store1 (xs ys : List Bool) : store xs ys 1=ys := rfl
lemma upd0 (xs ys zs : List Bool) : Function.update (store xs ys) 0 zs=store zs ys := by
  funext i; fin_cases i <;> simp [store]
lemma upd1 (xs ys zs : List Bool) : Function.update (store xs ys) 1 zs=store xs zs := by
  funext i; fin_cases i <;> simp [store]

abbrev appendProgram : Program where
  K := Fin 2
  input := 0
  output := 0
  Label := Bool
  main := false
  State := Option Bool
  initial := none
  code l := if l then
    .pop 1 (fun _ b=>b)
      (.branch Option.isSome
        (.push 0 (fun s=>s.getD false) (.load (fun _=>none) (.goto (fun _=>true))))
        (.load (fun _=>none) .halt))
    else
      .pop 0 (fun _ b=>b)
        (.branch (fun s=>decide (s=some true))
          (.pop 0 (fun _ b=>b)
            (.branch Option.isSome
              (.push 1 (fun s=>s.getD false) (.load (fun _=>none) (.goto (fun _=>false))))
              (.load (fun _=>none) (.goto (fun _=>true)))))
          (.load (fun _=>none) (.goto (fun _=>true))))

def cfg (l : Bool) (xs ys : List Bool) : appendProgram.machine.Cfg := ⟨some l,none,store xs ys⟩
def done (xs : List Bool) : appendProgram.machine.Cfg := ⟨none,none,store xs []⟩

lemma parse_nil (ys : List Bool) : appendProgram.machine.step (cfg false [] ys)=some (cfg true [] ys) := by
  simp [FinTM2.step,appendProgram,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_one (ys : List Bool) : appendProgram.machine.step (cfg false [true] ys)=some (cfg true [] ys) := by
  simp [FinTM2.step,appendProgram,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_false (xs ys : List Bool) : appendProgram.machine.step (cfg false (false::xs) ys)=some (cfg true xs ys) := by
  simp [FinTM2.step,appendProgram,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_true (b : Bool) (xs ys : List Bool) :
    appendProgram.machine.step (cfg false (true::b::xs) ys)=some (cfg false xs (b::ys)) := by
  simp [FinTM2.step,appendProgram,cfg,TM2.step,TM2.stepAux,upd0,upd1]; rfl
lemma restore_nil (xs : List Bool) : appendProgram.machine.step (cfg true xs [])=some (done xs) := by
  simp [FinTM2.step,appendProgram,cfg,done,TM2.step,TM2.stepAux,upd1]; rfl
lemma restore_cons (b : Bool) (xs ys : List Bool) :
    appendProgram.machine.step (cfg true xs (b::ys))=some (cfg true (b::xs) ys) := by
  simp [FinTM2.step,appendProgram,cfg,TM2.step,TM2.stepAux,upd0,upd1]; rfl

noncomputable def parse_phase (xs ys : List Bool) :
    EvalsToInTime appendProgram.machine.step (cfg false xs ys)
      (some (cfg true (discardPrefix xs) ((extractPrefix xs).reverse++ys))) (xs.length+1) := by
  induction xs using List.twoStepInduction generalizing ys with
  | nil => exact one_step (parse_nil ys)
  | singleton b =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_singleton] using
        time_mono (one_step (parse_false [] ys)) (by decide : 1≤2)
    | true => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_singleton] using
        time_mono (one_step (parse_one ys)) (by decide : 1≤2)
  | cons_cons b c xs ih _ =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append] using
        time_mono (one_step (parse_false (c::xs) ys)) (by simp : 1≤(false::c::xs).length+1)
    | true =>
      have hh := step_then (parse_true c xs ys) (ih (c::ys))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def restore_phase (xs ys : List Bool) :
    EvalsToInTime appendProgram.machine.step (cfg true xs ys)
      (some (done (ys.reverse++xs))) (ys.length+1) := by
  induction ys generalizing xs with
  | nil => exact one_step (restore_nil xs)
  | cons b ys ih =>
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using step_then (restore_cons b xs ys) (ih (b::xs))

lemma initial (xs : List Bool) : initList appendProgram.machine xs=cfg false xs [] := by
  rw [initList_bool]
  congr 1
  funext i; fin_cases i <;> simp [appendProgram,store]
lemma final (xs : List Bool) : haltList appendProgram.machine xs=done xs := by
  rw [haltList_bool]
  congr 1
  funext i; fin_cases i <;> simp [appendProgram,store]

noncomputable def append_computes : PolyComputes (fun xs=>extractPrefix xs++discardPrefix xs) where
  program := appendProgram
  time := 2*Polynomial.X+2
  outputs xs := by
    have h1 := parse_phase xs []
    have h2 := restore_phase (discardPrefix xs) (extractPrefix xs).reverse
    simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h2
    have hh := eval_trans h1 h2
    simp only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    have hl := extractPrefix_length xs
    exact time_mono hh (by omega)

abbrev prefixProgram (b : Bool) : Program where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Unit
  initial := ()
  code _ := .push () (fun _=>b) .halt

noncomputable def prefix_computes (b : Bool) : PolyComputes (List.cons b) where
  program := prefixProgram b
  time := 1
  outputs xs := by
    simp only [TM2OutputsInTime,Option.map_some,Polynomial.eval_one]
    apply one_step
    simp [initList_bool,haltList_bool,FinTM2.step,prefixProgram,TM2.step,TM2.stepAux,unit_update]
    rfl

abbrev tailProgram : Program where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Unit
  initial := ()
  code _ := .pop () (fun _ _=>()) .halt

noncomputable def tail_computes : PolyComputes (List.tail : List Bool → List Bool) where
  program := tailProgram
  time := 1
  outputs xs := by
    simp only [TM2OutputsInTime,Option.map_some,Polynomial.eval_one]
    apply one_step
    cases xs <;> simp [initList_bool,haltList_bool,FinTM2.step,tailProgram,TM2.step,TM2.stepAux,unit_update]
    all_goals rfl

end WordOperations

noncomputable def PolyComputes.append {f g : List Bool → List Bool}
    (hf : PolyComputes f) (hg : PolyComputes g) : PolyComputes (fun xs=>f xs++g xs) := by
  have hh := (hf.pair hg).comp WordOperations.append_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

noncomputable def const_computes (ys : List Bool) : PolyComputes (fun _=>ys) := by
  have hh := FiniteFold.computes () (fun _ _=>()) (fun _=>ys)
  exact hh

end MetricKMedianRecovery.BitMachine

end OAI

/- Recovery/Computes -/
namespace OAI

namespace MetricKMedianRecovery.BitMachine

open Turing Turing.TM2 StateTransition
namespace WordSelection
open WordOperations

def choose (xs : List Bool) : List Bool :=
  if xs.head?=some true then extractPrefix xs.tail else discardPrefix xs.tail

abbrev program : Program where
  K := Fin 2
  input := 0
  output := 0
  Label := Fin 5
  main := 0
  State := Option Bool
  initial := none
  code l := if l=0 then
    .pop 0 (fun _ b=>b)
      (.branch (fun s=>decide (s=some true))
        (.load (fun _=>none) (.goto (fun _=>1)))
        (.load (fun _=>none) (.goto (fun _=>2))))
    else if l=1 then
      .pop 0 (fun _ b=>b)
        (.branch (fun s=>decide (s=some true))
          (.pop 0 (fun _ b=>b)
            (.branch Option.isSome
              (.push 1 (fun s=>s.getD false) (.load (fun _=>none) (.goto (fun _=>1))))
              (.load (fun _=>none) (.goto (fun _=>3)))))
          (.load (fun _=>none) (.goto (fun _=>3))))
    else if l=2 then
      .pop 0 (fun _ b=>b)
        (.branch (fun s=>decide (s=some true))
          (.pop 0 (fun _ b=>b)
            (.branch Option.isSome
              (.load (fun _=>none) (.goto (fun _=>2)))
              (.load (fun _=>none) .halt)))
          (.load (fun _=>none) .halt))
    else if l=3 then
      .pop 0 (fun _ b=>b)
        (.branch Option.isSome
          (.load (fun _=>none) (.goto (fun _=>3)))
          (.load (fun _=>none) (.goto (fun _=>4))))
    else
      .pop 1 (fun _ b=>b)
        (.branch Option.isSome
          (.push 0 (fun s=>s.getD false) (.load (fun _=>none) (.goto (fun _=>4))))
          (.load (fun _=>none) .halt))

def cfg (l : Fin 5) (xs ys : List Bool) : program.machine.Cfg := ⟨some l,none,store xs ys⟩
def done (xs : List Bool) : program.machine.Cfg := ⟨none,none,store xs []⟩

lemma start_true (xs : List Bool) : program.machine.step (cfg 0 (true::xs) [])=some (cfg 1 xs []) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma start_false (xs : List Bool) : program.machine.step (cfg 0 (false::xs) [])=some (cfg 2 xs []) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma start_nil : program.machine.step (cfg 0 [] [])=some (cfg 2 [] []) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_nil (ys : List Bool) : program.machine.step (cfg 1 [] ys)=some (cfg 3 [] ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_one (ys : List Bool) : program.machine.step (cfg 1 [true] ys)=some (cfg 3 [] ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_false (xs ys : List Bool) : program.machine.step (cfg 1 (false::xs) ys)=some (cfg 3 xs ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_true (b : Bool) (xs ys : List Bool) :
    program.machine.step (cfg 1 (true::b::xs) ys)=some (cfg 1 xs (b::ys)) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0,upd1]; rfl
lemma discard_nil : program.machine.step (cfg 2 [] [])=some (done []) := by
  simp [FinTM2.step,program,cfg,done,TM2.step,TM2.stepAux,upd0]; rfl
lemma discard_one : program.machine.step (cfg 2 [true] [])=some (done []) := by
  simp [FinTM2.step,program,cfg,done,TM2.step,TM2.stepAux,upd0]; rfl
lemma discard_false (xs : List Bool) : program.machine.step (cfg 2 (false::xs) [])=some (done xs) := by
  simp [FinTM2.step,program,cfg,done,TM2.step,TM2.stepAux,upd0]; rfl
lemma discard_true (b : Bool) (xs : List Bool) :
    program.machine.step (cfg 2 (true::b::xs) [])=some (cfg 2 xs []) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma clear_nil (ys : List Bool) : program.machine.step (cfg 3 [] ys)=some (cfg 4 [] ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma clear_cons (b : Bool) (xs ys : List Bool) : program.machine.step (cfg 3 (b::xs) ys)=some (cfg 3 xs ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma restore_nil (xs : List Bool) : program.machine.step (cfg 4 xs [])=some (done xs) := by
  simp [FinTM2.step,program,cfg,done,TM2.step,TM2.stepAux,upd1]; rfl
lemma restore_cons (b : Bool) (xs ys : List Bool) : program.machine.step (cfg 4 xs (b::ys))=some (cfg 4 (b::xs) ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0,upd1]; rfl

noncomputable def parse_phase (xs ys : List Bool) :
    EvalsToInTime program.machine.step (cfg 1 xs ys)
      (some (cfg 3 (discardPrefix xs) ((extractPrefix xs).reverse++ys))) (xs.length+1) := by
  induction xs using List.twoStepInduction generalizing ys with
  | nil => exact one_step (parse_nil ys)
  | singleton b =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_singleton] using
        time_mono (one_step (parse_false [] ys)) (by decide : 1≤2)
    | true => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_singleton] using
        time_mono (one_step (parse_one ys)) (by decide : 1≤2)
  | cons_cons b c xs ih _ =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append] using
        time_mono (one_step (parse_false (c::xs) ys)) (by simp : 1≤(false::c::xs).length+1)
    | true =>
      have hh := step_then (parse_true c xs ys) (ih (c::ys))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def restore_phase (xs ys : List Bool) :
    EvalsToInTime program.machine.step (cfg 4 xs ys)
      (some (done (ys.reverse++xs))) (ys.length+1) := by
  induction ys generalizing xs with
  | nil => exact one_step (restore_nil xs)
  | cons b ys ih =>
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using step_then (restore_cons b xs ys) (ih (b::xs))

noncomputable def discard_phase (xs : List Bool) :
    EvalsToInTime program.machine.step (cfg 2 xs []) (some (done (discardPrefix xs))) (xs.length+1) := by
  induction xs using List.twoStepInduction with
  | nil => exact one_step discard_nil
  | singleton b =>
    cases b with
    | false => simpa only [discardPrefix,List.length_singleton] using
        time_mono (one_step (discard_false [])) (by decide : 1≤2)
    | true => simpa only [discardPrefix,List.length_singleton] using
        time_mono (one_step discard_one) (by decide : 1≤2)
  | cons_cons b c xs ih _ =>
    cases b with
    | false => simpa only [discardPrefix] using
        time_mono (one_step (discard_false (c::xs))) (by simp : 1≤(false::c::xs).length+1)
    | true =>
      have hh := step_then (discard_true c xs) ih
      simp only [discardPrefix]
      exact time_mono hh (by simp)

noncomputable def clear_phase (xs ys : List Bool) :
    EvalsToInTime program.machine.step (cfg 3 xs ys) (some (cfg 4 [] ys)) (xs.length+1) := by
  induction xs with
  | nil => exact one_step (clear_nil ys)
  | cons b xs ih => simpa only [List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
        (step_then (clear_cons b xs ys) ih)

noncomputable def true_phase (xs : List Bool) :
    EvalsToInTime program.machine.step (cfg 1 xs []) (some (done (extractPrefix xs))) (3*xs.length+3) := by
  have h1 := parse_phase xs []
  have h2 := clear_phase (discardPrefix xs) (extractPrefix xs).reverse
  have h3 := restore_phase [] (extractPrefix xs).reverse
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h3
  have hh := eval_trans h1 (eval_trans h2 h3)
  have hl := ProductBits.projections_length xs
  exact time_mono hh (by omega)

noncomputable def outputs (xs : List Bool) :
    EvalsToInTime program.machine.step (cfg 0 xs []) (some (done (choose xs))) (4*xs.length+4) := by
  cases xs with
  | nil =>
    have hh := step_then start_nil (one_step discard_nil)
    exact time_mono hh (by decide : 2≤4)
  | cons b xs =>
    cases b with
    | false =>
      have hh := step_then (start_false xs) (discard_phase xs)
      simpa only [choose,List.head?_cons,List.tail_cons,Option.some.injEq,Bool.false_eq_true,ite_false] using
        time_mono hh (by simp only [List.length_cons]; omega)
    | true =>
      have hh := step_then (start_true xs) (true_phase xs)
      simpa only [choose,List.head?_cons,List.tail_cons,ite_true] using
        time_mono hh (by simp only [List.length_cons]; omega)

lemma initial (xs : List Bool) : initList program.machine xs=cfg 0 xs [] := by
  rw [initList_bool]
  congr 1
  funext i; fin_cases i <;> simp [program,store]
lemma final (xs : List Bool) : haltList program.machine xs=done xs := by
  rw [haltList_bool]
  congr 1
  funext i; fin_cases i <;> simp [program,store]

noncomputable def choose_computes : PolyComputes choose where
  program := program
  time := 4*Polynomial.X+4
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using outputs xs

end WordSelection

noncomputable def PolyComputes.cond {p : List Bool → Bool} {f g : List Bool → List Bool}
    (hp : PolyComputes (fun xs=>[p xs])) (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun xs=>if p xs then f xs else g xs) := by
  have hh := (hp.append (hf.pair hg)).comp WordSelection.choose_computes
  simpa only [Function.comp_def,List.singleton_append,WordSelection.choose,List.head?_cons,
    List.tail_cons,Option.some.injEq,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

noncomputable def id_computes : PolyComputes id := by
  have he : (List.reverse ∘ List.reverse : List Bool → List Bool) = id := by
    funext x
    exact List.reverse_reverse x
  rw [← he]
  exact reverse_computes.comp reverse_computes

end MetricKMedianRecovery.BitMachine

end OAI

end

-- Assembly.lean
section
namespace A203914.Search.Wire
open OMA.S_oeis_a203914 Turing OAI.BinPackingGap.MachineKeepDecision
abbrev Machine {α β : Type} (a : α → W) (b : β → W) (f : α → β) := TM2ComputableInPolyTime a b f
abbrev Compose := ∀ {α β γ : Type} {a : α → W} {b : β → W} {c : γ → W} {f : α → β} {g : β → γ},
    Machine a b f → Machine b c g → (q : Polynomial Nat) →
    (∀ x, (b (f x)).length ≤ q.eval (a x).length) → Machine a c (g ∘ f)
def tt (s : T) : T × W := (s,tq s)
def rr (s : R) : R × W := (s,rq s)
def ut (s : T × Bool) : T := (s.1.1,s.1.2.1,if s.2 then s.1.2.2 else s.1.2.2-1)
def ur (s : R × Bool) : R := (s.1.1,s.1.2.1,s.1.2.2 ++ [!s.2])
structure Wiring where
  init : Machine id CT id
  tprep : Machine S (typedInputBits S) tt
  tup : Machine (typedOutputBits S) S ut
  hand : Machine S CR id
  rprep : Machine V (typedInputBits V) rr
  rup : Machine (typedOutputBits V) V ur
  finish : Machine V id (fun r => r.2.2)
private theorem frame_len (w : W) : (frame w).length=2*w.length+1 := frame_length w
noncomputable def runOracle {α : Type} (enc : α → W) (q : α → W) (L : DecisionProblem)
    (d : Machine id (fun b => [b]) L) : Machine (fun s => typedInputBits enc (s,q s))
      (typedOutputBits enc) (fun s => (s,L (q s))) where
  tm := (computationWithSavedCodec enc L d).tm
  inputAlphabet := (computationWithSavedCodec enc L d).inputAlphabet
  outputAlphabet := (computationWithSavedCodec enc L d).outputAlphabet
  time := (computationWithSavedCodec enc L d).time
  outputsFun s := (computationWithSavedCodec enc L d).outputsFun (s,q s)
noncomputable def cells (compose : Compose) (w : Wiring) (L : DecisionProblem)
    (d : Machine id (fun b => [b]) L) : Machine S S (tnext L) × Machine V V (rnext L) := by
  let tm := compose w.tprep (computationWithSavedCodec S L d) (4*Polynomial.X+4) (by
    rintro ⟨g,n,k⟩; simp [typedInputBits,inputBits,tt,tq,query_length]; omega)
  let rm := compose w.rprep (computationWithSavedCodec V L d) (4*Polynomial.X+4) (by
    rintro ⟨g,k,p⟩; simp [typedInputBits,inputBits,rr,rq,query_length]; omega)
  refine ⟨compose tm w.tup (Polynomial.X+1) ?_,compose rm w.rup (Polynomial.X+1) ?_⟩ <;>
    intro x <;> simp [typedOutputBits,typedKeep,tt,rr]
noncomputable def assembled (compose : Compose) (w : Wiring) (L : DecisionProblem)
    (d : Machine id (fun b => [b]) L) : Machine id id (driver L) := by
  let m := cells compose w L d
  let t := compose w.init (tloop L m.1) (8*Polynomial.X+8) (by
    intro g
    have h := Nat.sqrt_le g.length
    have h' := Nat.le_mul_self g.length.sqrt
    simp [CT,OAI.LargeIndependentSets.BoundedIteration.counted,start,tc]; omega)
  let h := compose t w.hand (8*Polynomial.X+8) (by
    intro g
    have h := Nat.sqrt_le g.length
    have h' := Nat.le_mul_self g.length.sqrt
    obtain ⟨j,hj,e⟩ := tdet L g g.length.sqrt (tc g) (tc g)
    change (S ((tnext L)^[tc g] (g,g.length.sqrt,tc g))).length ≤ _
    rw [e,lenS]; simp [tc,start] at *; omega)
  let r := compose h (rloop L m.2) (8*Polynomial.X+8) (by
    intro g
    have hs := Nat.sqrt_le g.length
    have h' := Nat.le_mul_self g.length.sqrt
    obtain ⟨j,hj,e⟩ := tdet L g g.length.sqrt (tc g) (tc g)
    change (CR ((tnext L)^[tc g] (g,g.length.sqrt,tc g))).length ≤ _
    rw [e]; simp [CR,OAI.LargeIndependentSets.BoundedIteration.counted,rc,enter,tc,start] at *; omega)
  let z := compose r w.finish (8*Polynomial.X+8) (by
    intro g
    have hs := Nat.sqrt_le g.length
    have h' := Nat.le_mul_self g.length.sqrt
    obtain ⟨j,hj,e⟩ := tdet L g g.length.sqrt (tc g) (tc g)
    change (V (rout L ((tnext L)^[tc g] (g,g.length.sqrt,tc g)))).length ≤ _
    rw [e]; simp [rout,rc,enter,rdet,recover_len,tc,start] at *; omega)
  convert z using 1
  funext g
  exact (exact_driver L g).symm
end A203914.Search.Wire

end

-- Pure.lean
section

namespace A203914.Search.Wire.Pure
open OMA.S_oeis_a203914 OAI.MetricKMedianRecovery OAI.MetricKMedianRecovery.BitMachine
open OAI.BinPackingGap.MachineKeepDecision

private abbrev pack (x y : W) := delimit x ++ y
private lemma dp (x y : W) : OAI.MetricKMedianRecovery.pairBits (x,y) = pack x y := by
  unfold OAI.MetricKMedianRecovery.pairBits pack
  have h : delimit x = x.flatMap (fun b => [true,b]) ++ [false] := by
    induction x with
    | nil => rfl
    | cons b x ih => simp [delimit,ih]
  rw [h]
private lemma frame_eq (x : W) : frame x = delimit x := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [frame,delimit,ih]

private structure Cert {α : Type} (e f : α → W) where
  fn : W → W
  m : PolyComputes fn
  spec : ∀ x, fn (e x) = f x
private noncomputable def src {α} (e : α → W) : Cert e e := ⟨id,id_computes,fun _ => rfl⟩
private noncomputable def con {α} (e : α → W) (w : W) : Cert e (fun _ => w) :=
  ⟨_,const_computes w,fun _ => rfl⟩
private noncomputable def pair {α} {e f g : α → W} (a : Cert e f) (b : Cert e g) :
    Cert e (fun x => pack (f x) (g x)) :=
  ⟨_,a.m.pair b.m,fun x => by simp only [dp,a.spec,b.spec]⟩
private noncomputable def app {α} {e f g : α → W} (a : Cert e f) (b : Cert e g) :
    Cert e (fun x => f x ++ g x) := ⟨_,a.m.append b.m,fun x => by rw [a.spec,b.spec]⟩
private noncomputable def left {α} {e f g : α → W} (a : Cert e (fun x => pack (f x) (g x))) : Cert e f :=
  ⟨_,a.m.comp extractPrefix_computes,fun x => by simp only [Function.comp_apply,a.spec,←dp,OAI.MetricKMedianRecovery.pairBits,extractPrefix_pair]⟩
private noncomputable def right {α} {e f g : α → W} (a : Cert e (fun x => pack (f x) (g x))) : Cert e g :=
  ⟨_,a.m.comp discardPrefix_computes,fun x => by simp only [Function.comp_apply,a.spec,←dp,OAI.MetricKMedianRecovery.pairBits,discardPrefix_pair]⟩
private noncomputable def tail {α} {e f : α → W} (a : Cert e f) : Cert e (fun x => (f x).tail) :=
  ⟨_,a.m.comp WordOperations.tail_computes,fun x => by simp only [Function.comp_apply,a.spec]⟩
private noncomputable def choose {α} {e f g : α → W} (a : Cert e f) (b : Cert e g) :
    Cert e (fun x => if (e x).head?.getD false then f x else g x) :=
  ⟨_,head_computes.cond a.m b.m,fun x => by simp only [a.spec,b.spec]⟩
private noncomputable def cert {α β} {e : α → W} {o : β → W} {f : α → β}
    {g : α → W} (c : Cert e g) (h : ∀ x, g x = o (f x)) : Machine e o f where
  tm := c.m.toTM2.tm
  inputAlphabet := c.m.toTM2.inputAlphabet
  outputAlphabet := c.m.toTM2.outputAlphabet
  time := c.m.toTM2.time
  outputsFun x := by rw [←h,←c.spec]; exact c.m.toTM2.outputsFun (e x)

private abbrev fields (g u p : W) := pack g (pack u p)
private theorem s_fields (s : T) : S s = fields s.1 (U s.2.1) (U s.2.2) := List.append_assoc ..
private theorem v_fields (s : R) : V s = fields s.1 (U s.2.1) s.2.2 := List.append_assoc ..
private noncomputable def sread : Cert S (fun s => fields s.1 (U s.2.1) (U s.2.2)) :=
  ⟨_,id_computes,s_fields⟩
private noncomputable def vread : Cert V (fun r => fields r.1 (U r.2.1) r.2.2) :=
  ⟨_,id_computes,v_fields⟩
private noncomputable def sans : Cert (typedOutputBits S) (fun x => fields x.1.1 (U x.1.2.1) (U x.1.2.2)) :=
  ⟨_,WordOperations.tail_computes,fun x => s_fields x.1⟩

noncomputable def tprep : Machine S (typedInputBits S) tt := by
  apply cert (pair (src S) (pair (left sread) (pair (right (right sread)) (con S []))))
  intro s; simp [typedInputBits,inputBits,tt,tq,query,frame_eq,pack,U]

private lemma tailU (k : Nat) : (U k).tail = U (k-1) := by cases k <;> rfl
noncomputable def tup : Machine (typedOutputBits S) S ut := by
  let k := right (right sans)
  apply cert (pair (left sans) (pair (left (right sans)) (choose k (tail k))))
  rintro ⟨⟨g,n,k'⟩,b⟩; cases b <;> simp [ut,S,pack,typedOutputBits,tailU]

noncomputable def hand : Machine S CR id := by
  apply cert (app (app (left (right sread)) (con S [false])) (pair (left sread) (pair (right (right sread)) (con S []))))
  intro s; simp [CR,OAI.LargeIndependentSets.BoundedIteration.counted,OAI.IndependentSetsGames.Foundations.Complexity.encodeWord,enter,V,rc,query,pack,U]

noncomputable def rprep : Machine V (typedInputBits V) rr := by
  apply cert (pair (src V) (app (src V) (con V [false])))
  intro r; simp [typedInputBits,inputBits,rr,rq,V,query,frame_eq,pack]

noncomputable def rup : Machine (typedOutputBits V) V ur := by
  let e := typedOutputBits V
  apply cert (app (tail (src e)) (choose (con e [false]) (con e [true])))
  rintro ⟨⟨g,k,p⟩,b⟩; cases b <;> simp [ur,V,query,typedOutputBits,e]

noncomputable def finish : Machine V id (fun r => r.2.2) := cert (right (right vread)) (fun _ => rfl)

end A203914.Search.Wire.Pure

end

-- Verify.lean
section
namespace A203914.Search.Wire
noncomputable def checkedFields (init : Machine id CT id) : Wiring := ⟨init, Pure.tprep, Pure.tup, Pure.hand, Pure.rprep, Pure.rup, Pure.finish⟩
end A203914.Search.Wire

end

-- Sequential.lean
section
/- Adapted from OpenAI OAI 3344da59991ed94f9ba711217b29c1d760badfa6. -/
namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineControl

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

end IndependentSetsGames.Foundations.Complexity.MachineControl
namespace IndependentSetsGames.Foundations.Complexity.MachineStackSwap

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

end IndependentSetsGames.Foundations.Complexity.MachineStackSwap



namespace IndependentSetsGames.Foundations.Complexity.MachineSequential

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

/-- With no intermediate symbols, both transfers are empty jumps. -/
inductive Bridge (α : Type)
  | symbol (x : α)
  | empty (h : α → False)

def program (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : Bridge (second.Γ second.k₀)) :
    Label first second → TM2.Stmt (Symbols first second) (Label first second)
      (State first second)
  | .inl label => firstStatement first second (first.m label)
  | .inr (.inr label) => secondStatement first second (second.m label)
  | .inr (.inl false) => match fallback with
    | .empty _ => .goto fun _ => bridgeLabel first second true
    | .symbol fallback =>
      Reduction.MachineTransfer.loopAt (Γ := Symbols first second)
        (.inl first.k₁) (.inr (.inr ())) relabel fallback
        (bridgeLabel first second false) (some (bridgeLabel first second true))
  | .inr (.inl true) => match fallback with
    | .empty _ => .goto fun _ => .inr (.inr second.main)
    | .symbol fallback =>
      Reduction.MachineTransfer.loopAt (Γ := Symbols first second)
        (.inr (.inr ())) (.inr (.inl second.k₀)) id fallback
        (bridgeLabel first second true) (some (.inr (.inr second.main)))

def machine (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : Bridge (second.Γ second.k₀)) : FinTM2 where
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
    (fallback : Bridge (second.Γ second.k₀)) (a b : first.Cfg)
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
    (fallback : Bridge (second.Γ second.k₀)) (a b : second.Cfg)
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
    (fallback : Bridge (second.Γ second.k₀)) (input : List (first.Γ first.k₀)) :
    firstConfiguration first second (initList first input) =
      initList (machine first second relabel fallback) input := by
  unfold firstConfiguration MachineControl.configuration MachineEmbedding.configuration initList
  congr 1
  funext k
  rcases k with k | k | k
  · by_cases h : k = first.k₀
    · subst k
      simp [machine, MachineEmbedding.tapes]
      rfl
    · simp [machine, MachineEmbedding.tapes, h]
  · simp [machine, MachineEmbedding.tapes]
  · simp [machine, MachineEmbedding.tapes]

theorem secondConfiguration_halt (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : Bridge (second.Γ second.k₀)) (output : List (second.Γ second.k₁)) :
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
      simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]
      rfl
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
    (fallback : Bridge (second.Γ second.k₀)) (word : List (first.Γ first.k₁)) :
    StateTransition.EvalsToInTime (machine first second relabel fallback).step
      (firstConfiguration first second (haltList first word))
      (some (temporaryConfiguration first second (word.reverse.map relabel)))
      (word.length + 1) := by
  cases fallback with
  | empty h =>
    cases word with
    | cons x xs => exact (h (relabel x)).elim
    | nil =>
      refine { steps := 1, steps_le_m := le_rfl, evals_in_steps := ?_ }
      apply congrArg some
      change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
      congr 1
      funext k
      rcases k with k | k | k <;> simp [temporaryTapes, MachineEmbedding.configuration, MachineEmbedding.tapes, haltList]
      rintro rfl
      rfl
  | symbol fallback =>
      let run := Reduction.MachineTransfer.transferAtInTime
        (.inl first.k₁ : Tape first second) (.inr (.inr ())) (by intro h; cases h)
        relabel fallback (bridgeLabel first second false)
        (some (bridgeLabel first second true)) (program first second relabel (.symbol fallback)) rfl
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
    (fallback : Bridge (second.Γ second.k₀)) (word : List (second.Γ second.k₀)) :
    StateTransition.EvalsToInTime (machine first second relabel fallback).step
      (temporaryConfiguration first second word)
      (some (secondConfiguration first second (initList second word.reverse)))
      (word.length + 1) := by
  cases fallback with
  | empty h =>
    cases word with
    | cons x xs => exact (h x).elim
    | nil =>
      refine { steps := 1, steps_le_m := le_rfl, evals_in_steps := ?_ }
      apply congrArg some
      change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
      congr 1
      funext k
      rcases k with k | k | k <;> simp [temporaryTapes, MachineStackSwap.configuration, MachineStackSwap.tapes, MachineEmbedding.configuration, MachineEmbedding.tapes, initList]
      rintro rfl
      rfl
  | symbol fallback =>
      let run := Reduction.MachineTransfer.transferAtInTime
        (.inr (.inr ()) : Tape first second) (.inr (.inl second.k₀)) (by intro h; cases h)
        id fallback (bridgeLabel first second true) (some (.inr (.inr second.main)))
        (program first second relabel (.symbol fallback)) rfl (temporaryTapes first second word)
        (first.initialState, second.initialState) none
      simp only [temporaryTapes, List.map_id, List.append_nil] at run
      rw [secondTransfer_tapes] at run
      exact run

def execute (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : Bridge (second.Γ second.k₀))
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

noncomputable def compose {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) (intermediate : Polynomial Nat)
    (bound : ∀ a, (eb (f a)).length ≤ intermediate.eval (ea a).length) :
    TM2ComputableInPolyTime ea ec (fun a => g (f a)) := by
  let relabel : first.tm.Γ first.tm.k₁ → second.tm.Γ second.tm.k₀ :=
    fun symbol => second.inputAlphabet.symm (first.outputAlphabet symbol)
  classical
  let defaultSymbol : Bridge (second.tm.Γ second.tm.k₀) :=
    if h : Nonempty (second.tm.Γ second.tm.k₀) then .symbol (Classical.choice h)
    else .empty (fun x => h ⟨x⟩)
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
    bound a
  have totalBound := MachineComposition.compositionBudget_le first.time second.time
    intermediate (ea a).length (eb (f a)).length intermediateBound
  have middleLength : middle.length = (eb (f a)).length := by simp only [middle, List.length_map]
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by
      apply Nat.le_trans full.steps_le_m
      simpa only [middleLength] using totalBound
  }

end IndependentSetsGames.Foundations.Complexity.MachineSequential

end OAI

end

-- WireCompose.lean
section

namespace A203914.Search.Wire
noncomputable def checkedCompose : Compose := by
  intro α β γ a b c f g first second q bound
  exact OAI.IndependentSetsGames.Foundations.Complexity.MachineSequential.compose (f := f) (g := g) first second q bound
end A203914.Search.Wire

end

-- RawInit.lean
section

namespace A203914.RawInit
open OMA.S_oeis_a203914 Turing StateTransition
abbrev W := List Bool
abbrev U (n : Nat) := List.replicate n true
inductive K | inp | rev | rem | tmp | root | pre | out deriving DecidableEq
instance : Fintype K := ⟨{.inp, .rev, .rem, .tmp, .root, .pre, .out}, by intro x; cases x <;> simp⟩
inductive L | start | scan | fill | clearR | clearT | emitN | emitG | emitK deriving DecidableEq
instance : Fintype L := ⟨{.start, .scan, .fill, .clearR, .clearT, .emitN, .emitG, .emitK}, by intro x; cases x <;> simp⟩
abbrev St := TM2.Stmt (fun _ : K => Bool) L (Option Bool)
def jump (l : L) : St := .load (fun _ => none) (.goto (fun _ => l))
def save (k : K) (b : Bool) (s : St) : St := .push k (fun _ => b) s
def takeS (k : K) (yes no : St) : St := .pop k (fun _ b => b) (.branch Option.isSome yes no)
def code : L → St
 | .start => save .rem true (jump .scan)
 | .scan => takeS .rem (takeS .inp (.push .rev (fun b => b.getD false) (save .tmp true (jump .scan))) (jump .clearR)) (save .root true (jump .fill))
 | .fill => takeS .tmp (save .rem true (save .pre true (save .out true (jump .fill)))) (save .rem true (save .rem true (jump .scan)))
 | .clearR => takeS .rem (jump .clearR) (jump .clearT)
 | .clearT => takeS .tmp (jump .clearT) (save .out false (jump .emitN))
 | .emitN => takeS .root (save .out true (save .out true (jump .emitN))) (save .out false (jump .emitG))
 | .emitG => takeS .rev (.push .out (fun b => b.getD false) (save .out true (jump .emitG))) (save .out false (jump .emitK))
 | .emitK => takeS .pre (save .out true (jump .emitK)) (.load (fun _ => none) .halt)
abbrev M : FinTM2 where
 K := K
 k₀ := .inp
 k₁ := .out
 Γ _ := Bool
 Λ := L
 main := .start
 σ := Option Bool
 initialState := none
 m := code

def cfg (l : Option L) (x v : W) (r t n p : Nat) (o : W) : M.Cfg :=
 ⟨l, none, fun k => match k with
  | .inp => x | .rev => v | .rem => U r | .tmp => U t | .root => U n | .pre => U p | .out => o⟩

private theorem eqcfg {l : Option L} {v : Option Bool} {s t : K → W} (h : ∀ k, s k = t k) :
 (⟨l,v,s⟩ : M.Cfg) = ⟨l,v,t⟩ := by rw [funext h]
section
variable {x v o : W} {r t n p : Nat} {b : Bool}
private theorem s_start : M.step (cfg (some .start) x v r t n p o) = some (cfg (some .scan) x v (r+1) t n p o) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
private theorem s_read : M.step (cfg (some .scan) (b::x) v (r+1) t n p o) = some (cfg (some .scan) x (b::v) r (t+1) n p o) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
private theorem s_endInput : M.step (cfg (some .scan) [] v (r+1) t n p o) = some (cfg (some .clearR) [] v r t n p o) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
private theorem s_block : M.step (cfg (some .scan) x v 0 t n p o) = some (cfg (some .fill) x v 0 t (n+1) p o) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
private theorem s_move : M.step (cfg (some .fill) x v r (t+1) n p o) = some (cfg (some .fill) x v (r+1) t n (p+1) (true::o)) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
private theorem s_filled : M.step (cfg (some .fill) x v r 0 n p o) = some (cfg (some .scan) x v (r+2) 0 n p o) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
private theorem s_cr : M.step (cfg (some .clearR) x v (r+1) t n p o) = some (cfg (some .clearR) x v r t n p o) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
private theorem s_cr0 : M.step (cfg (some .clearR) x v 0 t n p o) = some (cfg (some .clearT) x v 0 t n p o) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
private theorem s_ct : M.step (cfg (some .clearT) x v r (t+1) n p o) = some (cfg (some .clearT) x v r t n p o) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
private theorem s_ct0 : M.step (cfg (some .clearT) x v r 0 n p o) = some (cfg (some .emitN) x v r 0 n p (false::o)) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
private theorem s_en : M.step (cfg (some .emitN) x v r t (n+1) p o) = some (cfg (some .emitN) x v r t n p (true::true::o)) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
private theorem s_en0 : M.step (cfg (some .emitN) x v r t 0 p o) = some (cfg (some .emitG) x v r t 0 p (false::o)) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
private theorem s_eg : M.step (cfg (some .emitG) x (b::v) r t n p o) = some (cfg (some .emitG) x v r t n p (true::b::o)) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
private theorem s_eg0 : M.step (cfg (some .emitG) x [] r t n p o) = some (cfg (some .emitK) x [] r t n p (false::o)) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
private theorem s_ek : M.step (cfg (some .emitK) x v r t n (p+1) o) = some (cfg (some .emitK) x v r t n p (true::o)) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
private theorem s_ek0 : M.step (cfg (some .emitK) x v r t n 0 o) = some (cfg none x v r t n 0 o) := by (apply congrArg some; apply eqcfg; intro k; cases k <;> rfl)
end

private def Reach (a b : M.Cfg) (d : Nat) : Prop := Nonempty (EvalsToInTime M.step a (some b) d)
private theorem reflR {a : M.Cfg} : Reach a a 0 := ⟨EvalsToInTime.refl _ _⟩
private theorem chain {a b c : M.Cfg} {i j d : Nat} (h : Reach a b i) (h' : Reach b c j) (le : j+i ≤ d) : Reach a c d := by
 obtain ⟨u⟩ := h; obtain ⟨v⟩ := h'
 let w := EvalsToInTime.trans _ _ _ _ _ _ u v
 exact ⟨⟨w.toEvalsTo,w.steps_le_m.trans le⟩⟩
private theorem one {a b : M.Cfg} (h : M.step a = some b) : Reach a b 1 := ⟨⟨⟨1,h⟩,le_rfl⟩⟩
private theorem oneMore {a b c : M.Cfg} {j d : Nat} (h : M.step a = some b) (h' : Reach b c j) (le : j+1 ≤ d) : Reach a c d := chain (one h) h' le
private def finalC (o : W) := cfg none [] [] 0 0 0 0 o
private theorem emitK (p : Nat) (o : W) : Reach (cfg (some .emitK) [] [] 0 0 0 p o) (finalC (U p ++ o)) (p+1) := by
 induction p generalizing o with
 | zero => exact one s_ek0
 | succ p ih =>
   have h := oneMore s_ek (ih (true::o)) (le_refl _)
   simpa [List.replicate_succ' (a := true), List.append_assoc] using h
private def frame (w o : W) : W := (delimit w).dropLast ++ o
private theorem fr_nil (o : W) : frame [] o = o := rfl
private theorem fr_cons (b : Bool) (w o : W) : frame (b::w) o = true :: b :: frame w o := by
 cases w <;> rfl
private theorem fr_app (v w o : W) : frame (v++w) o = frame v (frame w o) := by
 induction v with
 | nil => rfl
 | cons b v ih => simp only [List.cons_append,fr_cons,ih]
private theorem fr_del (v o : W) : frame v (false::o) = delimit v ++ o := by
 induction v with
 | nil => rfl
 | cons b v ih => rw [fr_cons,ih]; rfl
private theorem emitG (v : W) (p : Nat) (o : W) :
 Reach (cfg (some .emitG) [] v 0 0 0 p o) (finalC (U p ++ false :: frame v.reverse o)) (v.length+p+2) := by
 induction v generalizing o with
 | nil => exact oneMore s_eg0 (emitK p _) (by simp)
 | cons b v ih =>
   rw [List.reverse_cons,fr_app,fr_cons,fr_nil]
   exact oneMore s_eg (ih _) (by simp)
private theorem emitN (v : W) (n p : Nat) (o : W) :
 Reach (cfg (some .emitN) [] v 0 0 n p o) (finalC (U p ++ false :: frame v.reverse (false :: frame (U n) o))) (v.length+n+p+3) := by
 induction n generalizing o with
 | zero => exact oneMore s_en0 (emitG v p _) (by omega)
 | succ n ih =>
   rw [show U (n+1) = U n ++ [true] from List.replicate_succ',fr_app,fr_cons,fr_nil]
   exact oneMore s_en (ih _) (by omega)
private def result (g : W) (n p : Nat) := U p ++ false :: (delimit g ++ delimit (U n) ++ U p)
private theorem clearT (v : W) (t n p : Nat) :
 Reach (cfg (some .clearT) [] v 0 t n p (U p)) (finalC (result v.reverse n p)) (v.length+n+p+t+4) := by
 induction t with
 | zero =>
   apply oneMore s_ct0 _ (show (v.length+n+p+3)+1 ≤ _ by omega)
   simpa [fr_del,result,List.append_assoc] using emitN v n p (false::U p)
 | succ t ih => exact oneMore s_ct ih (by omega)
private theorem clearR (v : W) (r t n p : Nat) :
 Reach (cfg (some .clearR) [] v r t n p (U p)) (finalC (result v.reverse n p)) (v.length+n+p+t+r+5) := by
 induction r with
 | zero => exact oneMore s_cr0 (clearT v t n p) (by omega)
 | succ r ih => exact oneMore s_cr ih (by omega)
private theorem fill (x v : W) (r t n p : Nat) :
 Reach (cfg (some .fill) x v r t n p (U p)) (cfg (some .scan) x v (r+t+2) 0 n (p+t) (U (p+t))) (t+1) := by
 induction t generalizing r p with
 | zero => exact one s_filled
 | succ t ih =>
   have h := oneMore s_move (ih (r+1) (p+1)) (le_refl _)
   simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

/-- Count complete odd blocks of sizes 1,3,5,... . `t` symbols of the current
block have been read and `r` remain. Only complete blocks enter both copies of k. -/
private def budget (x v : W) (r t n p : Nat) := 20*x.length + v.length + 2*r + 15*t + n+p+10
private def output (g : W) := result g g.length.sqrt (g.length.sqrt*g.length.sqrt)
private theorem scanAux (fuel : Nat) (g x v : W) (r t n p : Nat) (hb : 2*x.length + (if r=0 then 1 else 0) ≤ fuel) (hg : v.reverse ++ x = g)
 (hlen : v.length = p+t) (hp : p = n*n) (hblock : r+t = 2*n+1) :
 Reach (cfg (some .scan) x v r t n p (U p)) (finalC (output g)) (budget x v r t n p) := by
 induction fuel generalizing x v r t n p with
 | zero =>
   cases r <;> cases x <;> simp at hb <;> try omega
   rename_i r
   simp only [List.append_nil] at hg
   have hlen' : g.length = p+t := by rw [←hg,List.length_reverse,hlen]
   have hn : n = g.length.sqrt := by rw [hlen',hp]; exact (Nat.sqrt_add_eq n (by omega)).symm
   have hout : output g = result v.reverse n p := by simp only [output,←hn,←hp,hg]
   rw [hout]
   exact oneMore s_endInput (clearR v r t n p) (by unfold budget; simp <;> omega)
 | succ fuel ih =>
  cases r with
  | zero =>
    have hnew : p+t = (n+1)*(n+1) := by rw [hp,Nat.add_mul,Nat.mul_add]; simp; omega
    have h := ih x v (0+t+2) 0 (n+1) (p+t) (by simp at hb ⊢ <;> omega) hg (by omega) hnew (by omega)
    exact oneMore s_block (chain (fill x v 0 t (n+1) p) h (le_refl _)) (by unfold budget; omega)
  | succ r =>
    cases x with
    | nil =>
      simp only [List.append_nil] at hg
      have hlen' : g.length = p+t := by rw [←hg,List.length_reverse,hlen]
      have hn : n = g.length.sqrt := by rw [hlen',hp]; exact (Nat.sqrt_add_eq n (by omega)).symm
      have hout : output g = result v.reverse n p := by simp only [output,←hn,←hp,hg]
      rw [hout]
      exact oneMore s_endInput (clearR v r t n p) (by unfold budget; simp <;> omega)
    | cons b x =>
      apply oneMore s_read (ih x (b::v) r (t+1) n p (by simp at hb; split <;> omega) (by simpa using hg) (by simp; omega) hp (by omega))
      unfold budget; simp; omega
private theorem initEq (g : W) : initList M g = cfg (some .start) g [] 0 0 0 0 [] := by
 apply eqcfg; intro k; cases k <;> rfl
private theorem haltEq (o : W) : haltList M o = finalC o := by
 apply eqcfg; intro k; cases k <;> rfl

/-- Linear-time raw initializer. No validity assumption on the graph word. -/
theorem initializer : Nonempty (TM2ComputableInPolyTime id (fun g : List Bool =>
 let n := g.length.sqrt
 let k := n*n
 (List.replicate k true ++ [false]) ++ (delimit g ++ delimit (List.replicate n true) ++ List.replicate k true)) id) := by
 classical
 refine ⟨{tm := M, inputAlphabet := Equiv.refl Bool, outputAlphabet := Equiv.refl Bool,
          time := 20*Polynomial.X+13, outputsFun := ?_}⟩
 intro g
 have hh := oneMore s_start (scanAux (2*g.length) g g [] 1 0 0 0 (by simp) (by simp) rfl rfl rfl) (le_refl _)
 have h := Classical.choice hh
 change TM2OutputsInTime M (List.map (id : Bool → Bool) g) (some (List.map (id : Bool → Bool) _)) _
 simp only [List.map_id]
 unfold TM2OutputsInTime
 rw [initEq,Option.map_some,haltEq]
 simpa [budget,output,result,List.append_assoc,Nat.add_assoc] using h

end A203914.RawInit

end

-- Realize.lean
section

namespace A203914.Search
open OMA.S_oeis_a203914

/-- Compile a polynomial-time decision machine into the search driver on raw words. -/
theorem realize (L : DecisionProblem) (hL : L ∈ P) :
    Nonempty (Turing.TM2ComputableInPolyTime id id (driver L)) := by
  obtain ⟨d⟩ := hL
  obtain ⟨i⟩ := A203914.RawInit.initializer
  exact ⟨Wire.assembled Wire.checkedCompose (Wire.checkedFields i) L d⟩

end A203914.Search

end

-- Verifier.lean
section

namespace A203914.Verify
open OMA.S_oeis_a203914 A203914.Search

def block : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest => (block rest).map fun (u,v) => (b :: u,v)
  | _ => none

@[simp] theorem block_delimit (u v : List Bool) : block (delimit u ++ v) = some (u,v) := by
  induction u <;> simp [delimit, block, *]

def parse (x : List Bool) : Option (List Bool × Nat × List Bool) := do
  let (g,r) ← block x
  let (t,p) ← block r
  if t.all id then some (g,t.length,p) else none

@[simp] theorem parse_query (g k p) : parse (query g k p) = some (g,k,p) := by
  simp [parse, query, List.append_assoc, List.all_eq_true]

private theorem lookup_row {α : Type} (us : List α) (f : α → List Bool) (n i j : Nat)
    (h : ∀ u, (f u).length = n) (hi : i < us.length) (hj : j < n) :
    (us.flatMap f)[i*n+j]? = (f us[i])[j]? := by
  induction us generalizing i with
  | nil => simp at hi
  | cons u us ih =>
    cases i with
    | zero => simp [List.getElem?_append, h, hj]
    | succ i =>
      have hi' : i < us.length := by simpa using hi
      have hn : ¬ i*n+n+j < n := by omega
      simpa [List.getElem?_append, Nat.succ_mul, h, hn, show i*n+n+j-n=i*n+j by omega] using ih i hi'

open Classical in
theorem graph_entry {n} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    (graphBits G)[i.val*n+j.val]? = some (decide (G.Adj i j)) := by
  classical
  unfold graphBits
  rw [lookup_row _ _ n i.val j.val (by simp) (by simp) j.isLt]
  simp

def score (g w : List Bool) (n : Nat) : Nat :=
  (Finset.univ.filter fun t : Fin n × Fin n =>
    t.1 < t.2 ∧ g[t.1.val*n+t.2.val]? = some true ∧ w[t.1.val]? ≠ w[t.2.val]?).card

theorem score_graph {n} (G : SimpleGraph (Fin n)) (c : Fin n → Bool) :
    score (graphBits G) (List.ofFn c) n = cutSize G c := by
  classical
  unfold score cutSize
  congr 1
  ext t
  simp [graph_entry]

/-- The witness is the missing suffix; its length certifies the square root without
    requiring the verifier machine to compute a square root. -/
def R (z : List Bool × List Bool) : Bool :=
  match parse z.1 with
  | none => false
  | some (g,k,p) =>
    let w := p ++ z.2
    decide (w.length * w.length = g.length ∧ k ≤ score g w w.length)

theorem R_query {n} (G : SimpleGraph (Fin n)) (k : Nat) (p s : List Bool) :
    R (query (graphBits G) k p,s) = true ↔
      (p++s).length = n ∧ Good G k (p++s) := by
  rw [R, parse_query]
  simp only [decide_eq_true_eq, graphBits_length]
  constructor
  · rintro ⟨he, hk⟩
    have hl : (p++s).length = n := by nlinarith
    let c : Fin n → Bool := fun i => (p++s)[i.val]'(hl ▸ i.isLt)
    have hw : p++s = List.ofFn c := by apply List.ext_getElem <;> simp [hl,c]
    exact ⟨hl,c,hw,by rwa [hl, hw, score_graph] at hk⟩
  · rintro ⟨hl,c,hw,hk⟩
    rw [hl, hw, score_graph]
    exact ⟨rfl,hk⟩

def words : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => [] :: ((words n).map (false :: ·) ++ (words n).map (true :: ·))

@[simp] theorem mem_words (n : Nat) (w : List Bool) : w ∈ words n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons b w => cases b <;> simp [words, ih]

def L (x : List Bool) : Bool := (words x.length).any fun w => R (x,w)

theorem bounded (x) : L x = true ↔ ∃ w : List Bool, w.length ≤ x.length ∧ R (x,w) = true := by
  simp [L]

theorem delim_len (l : List Bool) : (delimit l).length = 2*l.length+1 := by
  induction l <;> simp [delimit, *, Nat.mul_add]

theorem spec (n) (G : SimpleGraph (Fin n)) (k : Nat) (p : List Bool) :
    L (query (graphBits G) k p) = true ↔ ∃ s, (p++s).length = n ∧ Good G k (p++s) := by
  rw [bounded]
  constructor
  · rintro ⟨s,_,hs⟩; exact ⟨s,(R_query ..).mp hs⟩
  · rintro ⟨s,hl,hg⟩
    refine ⟨s,?_,(R_query ..).mpr ⟨hl,hg⟩⟩
    simp only [List.length_append] at hl
    simp [query, delim_len, graphBits_length]
    nlinarith [Nat.le_mul_self n]

theorem mem_NP_of_machine
    (h : Nonempty (Turing.TM2ComputableInPolyTime pairBits (fun b : Bool => [b]) R)) : L ∈ NP :=
  ⟨Polynomial.X, R, h, fun x => by simpa using bounded x⟩

/-- Single-stream specification for a machine implementation. -/
def raw (bits : List Bool) : Bool :=
  match block bits with
  | none => false
  | some z => R z

@[simp] theorem raw_pair (z) : raw (pairBits z) = R z := by
  cases z; simp [raw, pairBits]

theorem mem_NP_of_raw_machine
    (h : Nonempty (Turing.TM2ComputableInPolyTime id (fun b : Bool => [b]) raw)) : L ∈ NP := by
  obtain ⟨m⟩ := h
  apply mem_NP_of_machine
  exact ⟨{ toTM2ComputableAux := m.toTM2ComputableAux, time := m.time,
           outputsFun := fun z => by simpa using m.outputsFun (pairBits z) }⟩


end A203914.Verify

end

-- Integrated.lean
section

namespace A203914.Integrated
open OMA.S_oeis_a203914
/-- A machine for the explicit suffix verifier suffices; search is already compiled. -/
theorem exactCut_of_verifier
    (v : Nonempty (Turing.TM2ComputableInPolyTime id (fun b : Bool => [b]) Verify.raw)) :
    P = NP → ApproximatesMaxCut 1 :=
  Search.H2_of_machines Verify.L (Verify.mem_NP_of_raw_machine v) Verify.spec
    (Search.realize Verify.L)
end A203914.Integrated

end

-- RawDispatch.lean
section

namespace A203914.Verify.Stream
open OMA.S_oeis_a203914 A203914.Search
open OAI.MetricKMedianRecovery.BitMachine
abbrev Bits := List Bool

def packet (bits : Bits) : Bits :=
  match block bits with
  | none => [false]
  | some (x,s) => match parse x with
    | none => [false]
    | some (g,k,p) => true :: (delimit g ++ (delimit (List.replicate k true) ++ (p ++ s)))

def dispatch (f : Bits → Bits) (x : Bits) : Bits :=
  if x.head?.getD false then f x.tail else [false]

noncomputable def dispatchMachine {f : Bits → Bits} (m : PolyComputes f) : PolyComputes (dispatch f) :=
  head_computes.cond (WordOperations.tail_computes.comp m) (const_computes [false])

theorem dispatch_packet {f : Bits → Bits}
    (hf : ∀ (g : Bits) (k : Nat) (w : Bits),
      f (delimit g ++ (delimit (List.replicate k true) ++ w)) =
        [decide (w.length * w.length = g.length ∧ k ≤ score g w w.length)])
    (bits : Bits) : dispatch f (packet bits) = [raw bits] := by
  cases hb : block bits with
  | none => simp [packet,raw,hb,dispatch]
  | some z =>
    obtain ⟨x,s⟩ := z
    cases hp : parse x with
    | none => simp [packet,raw,hb,R,hp,dispatch]
    | some v =>
      obtain ⟨g,k,p⟩ := v
      simpa [packet,raw,hb,R,hp,dispatch] using hf g k (p ++ s)

noncomputable def realizeSingleton {f : Bits → Bool} {g : Bits → Bits}
    (m : PolyComputes g) (h : ∀ x, g x = [f x]) :
    Turing.TM2ComputableInPolyTime id (fun b : Bool => [b]) f where
  toTM2ComputableAux := m.toTM2.toTM2ComputableAux
  time := m.toTM2.time
  outputsFun x := by simpa only [id_eq,h] using m.toTM2.outputsFun x

end A203914.Verify.Stream

end

-- RawParse.lean
section

namespace A203914.Verify.Stream
open OMA.S_oeis_a203914 OAI.MetricKMedianRecovery.BitMachine

def parsed (bits : List Bool) : List Bool :=
  match block bits with
  | none => [false]
  | some (x,s) => match parse x with
    | none => [false]
    | some (g,k,p) => true :: (delimit g ++ (delimit (List.replicate k true) ++ (p ++ s)))

-- DFA: none is the absorbing success state; some true expects a payload bit.
private def next : Option Bool → Bool → Option Bool
  | none, _ => none
  | some true, _ => some false
  | some false, true => some true
  | some false, false => none
private def valid (xs : List Bool) := (xs.foldl next (some false)).isNone
private theorem absorbed (xs : List Bool) : xs.foldl next none = none := by
  induction xs <;> simp [next, *]
private theorem block_spec (xs : List Bool) : block xs =
    if valid xs then some (extractPrefix xs, discardPrefix xs) else none := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton b => cases b <;> rfl
  | cons_cons b c xs ih _ =>
    cases b with
    | false => simp [valid, List.foldl_cons, next, absorbed, block, extractPrefix, discardPrefix]
    | true =>
      change (block xs).map _ = if valid xs then some (c :: extractPrefix xs, discardPrefix xs) else none
      rw [ih]; cases valid xs <;> rfl
private theorem all_rep (xs : List Bool) (h : xs.all id = true) : List.replicate xs.length true = xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp_all [List.replicate_succ]
private theorem pair_eq (u v : List Bool) : OAI.MetricKMedianRecovery.pairBits (u,v) = delimit u ++ v := by
  induction u with
  | nil => rfl
  | cons b u ih => simpa only [OAI.MetricKMedianRecovery.pairBits, List.flatMap_cons, List.cons_append, List.nil_append, delimit, List.cons.injEq, true_and] using ih

private noncomputable def validM : PolyComputes (fun xs => [valid xs]) :=
  FiniteFold.computes (some false) next (fun q => [q.isNone])
private theorem all_fold (xs : List Bool) (b : Bool) : xs.foldl (· && ·) b = (b && xs.all id) := by
  induction xs generalizing b <;> simp [*, Bool.and_assoc]
private noncomputable def allM : PolyComputes (fun xs => [xs.all id]) := by
  simpa only [all_fold, Bool.true_and] using FiniteFold.computes true (· && ·) (fun q => [q])

noncomputable def parseMachine : PolyComputes parsed := by
  let x := extractPrefix_computes
  let s := discardPrefix_computes
  let g := x.comp extractPrefix_computes
  let r := x.comp discardPrefix_computes
  let t := r.comp extractPrefix_computes
  let p := r.comp discardPrefix_computes
  let yes := (g.pair (t.pair (p.append s))).comp (WordOperations.prefix_computes true)
  let no := const_computes [false]
  let m := validM.cond ((x.comp validM).cond ((r.comp validM).cond ((t.comp allM).cond yes no) no) no) no
  refine Eq.mp (congrArg PolyComputes ?_) m
  funext bits
  simp only [Function.comp_apply, Function.comp_def, pair_eq, parsed, parse, block_spec]
  split_ifs <;> simp_all [all_rep]

end A203914.Verify.Stream

end

-- CountScan.lean
section
namespace A203914.Verify.Stream.CountScan
open OAI.MetricKMedianRecovery.BitMachine
abbrev W := List Bool
abbrev P (x y : W) := OAI.MetricKMedianRecovery.pairBits (x,y)
abbrev L := extractPrefix
abbrev Rr := discardPrefix
@[simp] lemma Lp (x y : W) : L (P x y) = x := extractPrefix_pair ..
@[simp] lemma Rp (x y : W) : Rr (P x y) = y := discardPrefix_pair ..
@[simp] lemma plen (x y : W) : (P x y).length = 2*x.length + 1 + y.length := by
  induction x with
  | nil => simp [P,OAI.MetricKMedianRecovery.pairBits]; omega
  | cons b x ih => change (_ :: _ :: P x y).length = _; simp [ih]; omega
lemma splitlen : ∀ x : W, 2*(L x).length + (Rr x).length ≤ x.length
  | [] => by decide
  | false :: xs => by simp [L,Rr,extractPrefix,discardPrefix]
  | [true] => by decide
  | true :: b :: xs => by have h := splitlen xs; simp [L,Rr,extractPrefix,discardPrefix] at *; omega

def pack (g m k : W) := P g (P m k)
abbrev graph := L
abbrev mask' (x : W) := L (Rr x)
abbrev budget (x : W) := Rr (Rr x)
def nextK (x : W) := if (graph x).head?.getD false then
  if (mask' x).head?.getD false then (budget x).tail else budget x else budget x
def advance (x : W) := if decide (graph x = []) then x else
  if decide (mask' x = []) then x else pack (graph x).tail (mask' x).tail (nextK x)
def finish (x : W) : W := if decide (graph x = []) then
  if decide (mask' x = []) then [decide (budget x = [])] else [false] else [false]
noncomputable def mg : PolyComputes graph := extractPrefix_computes
noncomputable def mm : PolyComputes mask' := discardPrefix_computes.comp mg
noncomputable def mkb : PolyComputes budget := discardPrefix_computes.comp discardPrefix_computes
noncomputable def mnext : PolyComputes nextK :=
  (mg.comp head_computes).cond ((mm.comp head_computes).cond (mkb.comp WordOperations.tail_computes) mkb) mkb
noncomputable def mstep : PolyComputes advance :=
  (mg.comp isEmpty_computes).cond id_computes ((mm.comp isEmpty_computes).cond id_computes
    ((mg.comp WordOperations.tail_computes).pair ((mm.comp WordOperations.tail_computes).pair mnext)))
noncomputable def mend : PolyComputes finish :=
  (mg.comp isEmpty_computes).cond ((mm.comp isEmpty_computes).cond (mkb.comp isEmpty_computes) (const_computes [false])) (const_computes [false])
lemma step_bound (x : W) : (advance x).length ≤ x.length+2 := by
  have h := splitlen x
  have h' := splitlen (Rr x)
  simp only [advance]; split <;> try omega
  split <;> try omega
  unfold pack nextK; simp only [plen,List.length_tail]; split <;> (try split) <;> (try simp only [List.length_tail]) <;> dsimp only [graph,mask',budget] at * <;> omega
lemma iter_bound (x : W) (i : Nat) : (advance^[i] x).length ≤ x.length+2*i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply']; have := step_bound (advance^[i] x); omega

def hits (g m : W) := ((g.zip m).filter (fun p => p.1 && p.2)).length
lemma scan (g m k : W) : finish (advance^[g.length] (pack g m k)) =
    [decide (m.length = g.length ∧ k.length ≤ hits g m)] := by
  induction g generalizing m k with
  | nil => cases m <;> simp [finish,graph,mask',budget,pack,hits]
  | cons a g ih =>
    cases m with
    | nil =>
      have h : advance (pack (a::g) [] k) = pack (a::g) [] k := by simp [advance,graph,mask',budget,pack]
      rw [Function.iterate_fixed h]; simp [finish,graph,mask',budget,pack]
    | cons b m =>
      rw [List.length_cons,Function.iterate_succ_apply]
      cases a <;> cases b <;>
        simp [advance,nextK,graph,mask',budget,pack] <;> change finish (advance^[g.length] (pack g m _)) = _ <;>
        rw [ih] <;> simp [hits,List.zip,List.zipWith,List.length_tail] <;> (by_cases e : m.length = g.length <;> simp [e])
end A203914.Verify.Stream.CountScan

end

-- CountCore.lean
section
namespace A203914.Verify.Stream.CountScan
open OAI.MetricKMedianRecovery.BitMachine
open OMA.S_oeis_a203914 A203914.Search

def prepare (mask : W → W) (x : W) := P (L x) (pack (L x) (mask (budget x)) (mask' x))
noncomputable def prepareMachine {mask} (hm : PolyComputes mask) : PolyComputes (prepare mask) :=
  mg.pair (mg.pair ((mkb.comp hm).pair mm))
lemma it_bound (x : W) (i : Nat) (h : i ≤ (L x).length) :
  (advance^[i] (Rr x)).length ≤ (3 * Polynomial.X : Polynomial Nat).eval x.length := by
  have h' := splitlen x
  have hh := iter_bound (Rr x) i
  simp; omega
lemma packet_pair (x y : W) : delimit x ++ y = P x y := by
  induction x with
  | nil => rfl
  | cons b x ih => exact congrArg (fun l => true :: b :: l) ih
lemma prepared (f : W → W) (g : W) (k : Nat) (w : W) :
    prepare f (delimit g ++ (delimit (List.replicate k true) ++ w)) =
      P g (pack g (f w) (List.replicate k true)) := by
  simp [prepare,budget,mask',packet_pair]
end A203914.Verify.Stream.CountScan

end

-- CountIter.lean
section
/- Counted bounded iteration for Bool word programs.
   Adapted from OpenAI OAI LargeIndependentSets.BoundedIteration and
   MetricKMedianRecovery.BitMachine (commit 3344da59991ed94f9ba711217b29c1d760badfa6). -/
namespace A203914.Verify.Stream
open Turing Turing.TM2 StateTransition
open OAI.MetricKMedianRecovery.BitMachine

/-- Iterate `f` on the payload `discardPrefix x`, as many times as the length of the
delimited prefix `extractPrefix x`. -/
def iterWord (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  f^[(extractPrefix x).length] (discardPrefix x)

namespace Iter
variable (p : Program)

open MapLeft (mapStacks pure pure_at pure_update pure_nil updLeft upd0 upd1 stacks_left stacks_zero
  stacks_one)

/-- Stacks: body stacks, `.inr 0` = unary counter, `.inr 1` = transfer stack.
Labels: body labels, `.inr 0` parse, `.inr 1` test counter, `.inr 2` drain output,
`.inr 3` refill input. -/
abbrev program : Program where
  K := MapLeft.Stack p
  input := .inl p.input
  output := .inl p.input
  Label := MapLeft.Label p
  main := .inr 0
  State := MapLeft.State p
  initial := (p.initial,none)
  code l := match l with
    | .inl i => renameStmt Function.Embedding.inl Sum.inl (fun s => (s,none)) Prod.fst
        (some (.inr 2)) (p.code i)
    | .inr i => if i=0 then
        .pop (.inl p.input) (fun s b => (s.1,b))
          (.branch (fun s => decide (s.2=some true))
            (.pop (.inl p.input) (fun s b => (s.1,b))
              (.branch (fun s => s.2.isSome)
                (.push (.inr 0) (fun _ => true)
                  (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 0))))
                (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 1)))))
            (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 1))))
      else if i=1 then
        .pop (.inr 0) (fun s b => (s.1,b))
          (.branch (fun s => s.2.isSome)
            (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inl p.main)))
            (.load (fun _ => (p.initial,none)) .halt))
      else if i=2 then
        .pop (.inl p.output) (fun s b => (s.1,b))
          (.branch (fun s => s.2.isSome)
            (.push (.inr 1) (fun s => s.2.getD false)
              (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 2))))
            (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 3))))
      else
        .pop (.inr 1) (fun s b => (s.1,b))
          (.branch (fun s => s.2.isSome)
            (.push (.inl p.input) (fun s => s.2.getD false)
              (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 3))))
            (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 1))))

def cfg (l : MapLeft.Label p) (s : Stacks p.K) (a b : List Bool) : (program p).machine.Cfg :=
  ⟨some l,(p.initial,none),mapStacks p s a b⟩
def done (ys : List Bool) : (program p).machine.Cfg :=
  ⟨none,(p.initial,none),mapStacks p (pure p p.input ys) [] []⟩

def runCfg (c0 : List Bool) (c : p.machine.Cfg) : (program p).machine.Cfg :=
  ⟨c.l.elim (some (.inr 2)) (fun l => some (.inl l)),(c.var,none),mapStacks p c.stk c0 []⟩

lemma run_step (c0 : List Bool) (s t : p.machine.Cfg) (h : p.machine.step s=some t) :
    (program p).machine.step (runCfg p c0 s)=some (runCfg p c0 t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt Function.Embedding.inl Sum.inl (fun s => (s,none))
      Prod.fst (some (.inr 2)) (p.code l)) (v,none) (frameStacks stk ![c0,[]]))=_
    rw [stepAux_frame _ _ _ (fun _ => rfl)]
    rfl

lemma parse_nil (c : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (pure p p.input []) c [])=
      some (cfg p (.inr 1) (pure p p.input []) c []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,updLeft,pure_at,pure_update]; rfl
lemma parse_false (xs c : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (pure p p.input (false::xs)) c [])=
      some (cfg p (.inr 1) (pure p p.input xs) c []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,updLeft,pure_at,pure_update]; rfl
lemma parse_one (c : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (pure p p.input [true]) c [])=
      some (cfg p (.inr 1) (pure p p.input []) c []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,updLeft,pure_at,pure_update]; rfl
lemma parse_true (b : Bool) (xs c : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (pure p p.input (true::b::xs)) c [])=
      some (cfg p (.inr 0) (pure p p.input xs) (true::c) []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,updLeft,upd0,pure_at,pure_update]; rfl
lemma test_nil (w : List Bool) :
    (program p).machine.step (cfg p (.inr 1) (pure p p.input w) [] [])=some (done p w) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,done,upd0]; rfl
lemma test_cons (w c : List Bool) :
    (program p).machine.step (cfg p (.inr 1) (pure p p.input w) (true::c) [])=
      some (cfg p (.inl p.main) (pure p p.input w) c []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma drain_nil (c t : List Bool) :
    (program p).machine.step (cfg p (.inr 2) (pure p p.output []) c t)=
      some (cfg p (.inr 3) (pure p p.output []) c t) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,updLeft,pure_at,pure_update]; rfl
lemma drain_cons (b : Bool) (xs c t : List Bool) :
    (program p).machine.step (cfg p (.inr 2) (pure p p.output (b::xs)) c t)=
      some (cfg p (.inr 2) (pure p p.output xs) c (b::t)) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,updLeft,upd1,pure_at,pure_update]; rfl
lemma refill_nil (xs c : List Bool) :
    (program p).machine.step (cfg p (.inr 3) (pure p p.input xs) c [])=
      some (cfg p (.inr 1) (pure p p.input xs) c []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1]; rfl
lemma refill_cons (b : Bool) (xs c t : List Bool) :
    (program p).machine.step (cfg p (.inr 3) (pure p p.input xs) c (b::t))=
      some (cfg p (.inr 3) (pure p p.input (b::xs)) c t) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,updLeft,upd1,pure_at,pure_update]; rfl

noncomputable def parse_phase (bits c : List Bool) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 0) (pure p p.input bits) c [])
      (some (cfg p (.inr 1) (pure p p.input (discardPrefix bits))
        (List.replicate (extractPrefix bits).length true++c) [])) (bits.length+1) := by
  induction bits using List.twoStepInduction generalizing c with
  | nil => exact one_step (parse_nil p c)
  | singleton b =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.length_nil,List.replicate_zero,
        List.nil_append,List.length_cons] using time_mono (one_step (parse_false p [] c)) (by decide : 1≤2)
    | true => simpa only [extractPrefix,discardPrefix,List.length_nil,List.replicate_zero,
        List.nil_append,List.length_cons] using time_mono (one_step (parse_one p c)) (by decide : 1≤2)
  | cons_cons b d bits ih _ =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.length_nil,List.replicate_zero,
        List.nil_append] using
        time_mono (one_step (parse_false p (d::bits) c)) (by simp : 1≤(false::d::bits).length+1)
    | true =>
      have hh := step_then (parse_true p d bits c) (ih (true::c))
      simp only [extractPrefix,discardPrefix,List.length_cons,List.replicate_succ',
        List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def drain_phase (xs c t : List Bool) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 2) (pure p p.output xs) c t)
      (some (cfg p (.inr 3) (pure p p.output []) c (xs.reverse++t))) (xs.length+1) := by
  induction xs generalizing t with
  | nil => exact one_step (drain_nil p c t)
  | cons b xs ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (drain_cons p b xs c t) (ih (b::t))

noncomputable def refill_phase (t xs c : List Bool) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 3) (pure p p.input xs) c t)
      (some (cfg p (.inr 1) (pure p p.input (t.reverse++xs)) c [])) (t.length+1) := by
  induction t generalizing xs with
  | nil => exact one_step (refill_nil p xs c)
  | cons b t ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (refill_cons p b xs c t) (ih (b::xs))

lemma pure_switch : pure p p.output [] = pure p p.input [] := by
  rw [pure_nil,pure_nil]

lemma run_initial (w c : List Bool) :
    runCfg p c (initList p.machine w)=cfg p (.inl p.main) (pure p p.input w) c [] := by
  rw [initList_bool]
  rfl
lemma run_final (w c : List Bool) :
    runCfg p c (haltList p.machine w)=cfg p (.inr 2) (pure p p.output w) c [] := by
  rw [haltList_bool]
  rfl

/-- One round: decrement counter, run the body, move its output back to the input stack. -/
noncomputable def round (w c out : List Bool) (n : ℕ)
    (h : TM2OutputsInTime p.machine w (some out) n) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 1) (pure p p.input w) (true::c) [])
      (some (cfg p (.inr 1) (pure p p.input out) c [])) (out.length+1+(out.length+1)+n+1) := by
  have hrun : EvalsToInTime (program p).machine.step
      (runCfg p c (initList p.machine w)) (some (runCfg p c (haltList p.machine out))) n := by
    refine ⟨⟨h.steps,?_⟩,h.steps_le_m⟩
    exact iterate_transfer _ _ (runCfg p c) (run_step p c) h.steps _ _ h.evals_in_steps
  rw [run_initial,run_final] at hrun
  have hdrain := drain_phase p out c []
  rw [List.append_nil,pure_switch p] at hdrain
  have hrefill := refill_phase p out.reverse [] c
  rw [List.reverse_reverse,List.append_nil,List.length_reverse] at hrefill
  exact eval_trans (one_step (test_cons p w c)) (eval_trans hrun (eval_trans hdrain hrefill))

noncomputable def loop {f : List Bool → List Bool} (mf : PolyComputes f) (hp : mf.program = p)
    (L : ℕ) (k : ℕ) (w : List Bool) (hl : ∀ i, i ≤ k → (f^[i] w).length ≤ L) :
    EvalsToInTime (program p).machine.step
      (cfg p (.inr 1) (pure p p.input w) (List.replicate k true) [])
      (some (done p (f^[k] w))) (k*(mf.time.eval L+2*L+3)+1) := by
  subst hp
  induction k generalizing w with
  | zero => exact time_mono (one_step (test_nil _ w)) (by simp)
  | succ k ih =>
    have hw : w.length ≤ L := hl 0 (Nat.zero_le _)
    have hf : (f w).length ≤ L := hl 1 (by omega)
    have hr := round mf.program w (List.replicate k true) (f w) _ (mf.outputs w)
    have hrest := ih (f w) (fun i hi => by
      have := hl (i+1) (by omega)
      rwa [Function.iterate_succ_apply] at this)
    rw [← Function.iterate_succ_apply] at hrest
    refine time_mono (eval_trans hr hrest) ?_
    have ht := polynomial_monotone mf.time hw
    simp only at ht
    have hk : (k+1)*(mf.time.eval L+2*L+3) = k*(mf.time.eval L+2*L+3)+(mf.time.eval L+2*L+3) := by ring
    rw [hk]
    omega

lemma initial (x : List Bool) : initList (program p).machine x=cfg p (.inr 0) (pure p p.input x) [] [] := by
  rw [initList_bool]
  congr 1
  funext i
  cases i with
  | inl k => simp [mapStacks,MapLeft.pure,Function.update_apply]
  | inr k => fin_cases k <;> rfl
lemma final (x : List Bool) : haltList (program p).machine x=done p x := by
  rw [haltList_bool]
  congr 1
  funext i
  cases i with
  | inl k => simp [mapStacks,MapLeft.pure,Function.update_apply]
  | inr k => fin_cases k <;> rfl

end Iter

/-- Counted bounded iteration of a polynomial-time Bool word program. -/
noncomputable def iterMachine {f : List Bool → List Bool} (mf : PolyComputes f) (B : Polynomial ℕ)
    (hb : ∀ x i, i ≤ (extractPrefix x).length → (f^[i] (discardPrefix x)).length ≤ B.eval x.length) :
    PolyComputes (iterWord f) where
  program := Iter.program mf.program
  time := Polynomial.X*(mf.time.comp B+2*B+3)+Polynomial.X+2
  outputs x := by
    have hparse := Iter.parse_phase mf.program x []
    rw [List.append_nil] at hparse
    have hloop := Iter.loop mf.program mf rfl (B.eval x.length) (extractPrefix x).length
      (discardPrefix x) (hb x)
    have hh := eval_trans hparse hloop
    have hk := extractPrefix_length x
    simp only [TM2OutputsInTime,Option.map_some,Iter.initial,Iter.final,iterWord]
    refine time_mono hh ?_
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_X,
      Polynomial.eval_ofNat]
    have hm := Nat.mul_le_mul_right (mf.time.eval (B.eval x.length)+2*B.eval x.length+3) hk
    omega

end A203914.Verify.Stream

end

-- MaskBridge.lean
section
namespace A203914.Verify.Stream.CountScan
private theorem len_sum {α} (p : α → Bool) (l : List α) :
  (l.filter p).length = (l.map (fun a => if p a then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [List.filter_cons,h,ih,Nat.add_comm]

theorem scoreBridge (g w m : W) (hg : w.length*w.length = g.length)
    (hm : m.length = w.length*w.length)
    (he : ∀ i j : Fin w.length, m[i.val*w.length+j.val]? =
      some (decide (i < j ∧ w[i.val]? ≠ w[j.val]?))) : hits g m = score g w w.length := by
  let z := g.zip m
  have hl : z.length = w.length*w.length := by simp [z,hm,← hg]
  let f (i : Fin (w.length*w.length)) := z[i.val]'(hl.symm ▸ i.isLt)
  have hz : z = List.ofFn f := by apply List.ext_getElem <;> simp [f,hl]
  unfold hits
  change (z.filter _).length = _
  rw [len_sum,hz,List.map_ofFn,List.sum_ofFn,score,Finset.card_filter]
  symm
  apply Fintype.sum_equiv finProdFinEquiv
  rintro ⟨i,j⟩
  have hi := (finProdFinEquiv (i,j)).isLt
  have ei : (finProdFinEquiv (i,j)).val = i.val*w.length+j.val := by change _ + _ * _ = _; ring
  rw [ei] at hi
  have gg : i.val*w.length+j.val < g.length := by omega
  have mm : i.val*w.length+j.val < m.length := by omega
  have h := he i j
  rw [List.getElem?_eq_getElem mm,Option.some.injEq] at h
  simp only [Function.comp_apply,f,z,List.getElem_zip,ei,List.getElem?_eq_getElem gg,h]
  cases g[i.val*w.length+j.val] <;> simp [and_assoc]
end A203914.Verify.Stream.CountScan

end

-- CountMask.lean
section
namespace A203914.Verify.Stream
open OAI.MetricKMedianRecovery.BitMachine CountScan
namespace CutMask
-- Negate a suffix by scanning right to left and prepending each flipped bit.
def flipStep (x : W) := P (CountScan.L x).tail (if (CountScan.L x).head?.getD false then false :: Rr x else true :: Rr x)
noncomputable def flipStepM : PolyComputes flipStep :=
  (mg.comp WordOperations.tail_computes).pair ((mg.comp head_computes).cond
    (discardPrefix_computes.comp (WordOperations.prefix_computes false))
    (discardPrefix_computes.comp (WordOperations.prefix_computes true)))
lemma flipBound (x : W) (i : ℕ) : (flipStep^[i] x).length ≤ x.length+2*i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']; have := splitlen (flipStep^[i] x)
    simp only [flipStep,plen,List.length_tail]; split <;> simp only [List.length_cons] <;> omega
lemma flipRun (x acc : W) : Rr (flipStep^[x.length] (P x acc)) = x.reverse.map Bool.not ++ acc := by
  induction x generalizing acc with
  | nil => simp
  | cons b x ih => cases b <;> simp [Function.iterate_succ_apply,flipStep,ih,List.reverse_cons,List.append_assoc]
noncomputable def notM : PolyComputes (List.map Bool.not) := by
  let m := iterMachine flipStepM (3*Polynomial.X) (by
    intro x i hi; have := flipBound (Rr x) i; have := splitlen x; simp; dsimp only [CountScan.L,Rr] at *; omega)
  have h := (reverse_computes.pair (reverse_computes.pair (const_computes []))).comp (m.comp discardPrefix_computes)
  convert h using 1
  funext w
  change w.map Bool.not = Rr (flipStep^[(CountScan.L (P w.reverse (P w.reverse []))).length] (Rr (P w.reverse (P w.reverse []))))
  rw [Lp,Rp,flipRun]; simp

abbrev zpad (x : W) := false :: graph x
abbrev rest (x : W) := (mask' x).tail
def color (b : Bool) (t : W) := if b then t.map Bool.not else t
@[simp] lemma color_len (b : Bool) (t : W) : (color b t).length = t.length := by cases b <;> simp [color]
def rowStep (x : W) := pack (zpad x) (rest x)
  (budget x ++ (zpad x ++ color ((mask' x).head?.getD false) (rest x)))
noncomputable def rowM : PolyComputes rowStep := by
  let z := mg.comp (WordOperations.prefix_computes false)
  let t := mm.comp WordOperations.tail_computes
  exact z.pair (t.pair (mkb.append (z.append ((mm.comp head_computes).cond (t.comp notM) t))))
abbrev width (x : W) := (graph x).length + (mask' x).length
lemma widthStep (x : W) : width (rowStep x) ≤ width x + 1 := by
  simp [rowStep,width,graph,mask',pack]; omega
lemma sizeStep (x : W) : (rowStep x).length ≤ x.length + width x + 5 := by
  have := splitlen x; have := splitlen (Rr x)
  simp [rowStep,pack,width,graph,mask',budget]; omega
lemma widthIter (x : W) (i : ℕ) : width (rowStep^[i] x) ≤ width x+i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply']; have := widthStep (rowStep^[i] x); omega
lemma sizeIter (x : W) (i : ℕ) : (rowStep^[i] x).length ≤ x.length+i*(width x+i+5) := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply']; have := sizeStep (rowStep^[i] x); have := widthIter x i; nlinarith
noncomputable def loopM : PolyComputes (iterWord rowStep) := iterMachine rowM
  (Polynomial.X + Polynomial.X*(2*Polynomial.X+5)) (by
    intro x i hi
    have h := sizeIter (Rr x) i
    have a := splitlen x; have b := splitlen (Rr x); have c := splitlen (Rr (Rr x))
    change i ≤ (CountScan.L x).length at hi
    have wi : width (Rr x) ≤ x.length := by dsimp only [width,graph,mask']; omega
    have ii : i ≤ x.length := by omega
    have hh := Nat.mul_le_mul ii (show width (Rr x)+i+5 ≤ 2*x.length+5 by omega)
    change (rowStep^[i] (Rr x)).length ≤ _; simp; omega)

def rows (k : ℕ) : W → W
  | [] => []
  | b :: t => (List.replicate (k+1) false ++ color b t) ++ rows (k+1) t
lemma rowRun (k : ℕ) (t acc : W) : budget (rowStep^[t.length] (pack (List.replicate k false) t acc)) = acc ++ rows k t := by
  induction t generalizing k acc with
  | nil => simp [pack,budget,rows]
  | cons b t ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    simp only [rowStep,zpad,graph,mask',budget,rest,pack,Lp,Rp,List.tail_cons,List.head?_cons,Option.getD_some]
    change budget (rowStep^[t.length] (pack (List.replicate (k+1) false) t _)) = _
    rw [ih]; simp [rows,List.replicate_succ,List.append_assoc]
end CutMask
open CutMask
def mask (w : W) := rows 0 w
noncomputable def maskMachine : PolyComputes mask := by
  have h := (id_computes.pair ((const_computes []).pair (id_computes.pair (const_computes [])))).comp (loopM.comp mkb)
  convert h using 1
  funext w
  change rows 0 w = budget (rowStep^[(CountScan.L (P w (pack [] w []))).length] (Rr (P w (pack [] w []))))
  rw [Lp,Rp]; simpa using (rowRun 0 w []).symm

private theorem rowsLen (k : ℕ) (t : W) : (rows k t).length = t.length*(k+t.length) := by
  induction t generalizing k with
  | nil => simp [rows]
  | cons b t ih => simp [rows,ih]; ring

theorem mask_len (w : W) : (mask w).length = w.length*w.length := by simp [mask,rowsLen]

private theorem rowsEntry (w t : W) (k : ℕ) (ht : w.drop k = t) (hn : k+t.length = w.length)
    (i j : ℕ) (hi : i < t.length) (hj : j < w.length) :
    (rows k t)[i*w.length+j]? = some (decide (k+i < j ∧ w[k+i]? ≠ w[j]?)) := by
  induction t generalizing k i with
  | nil => simp at hi
  | cons b t ih =>
    have len : (List.replicate (k+1) false ++ color b t).length = w.length := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hn
    have hd : w.drop (k+1) = t := by
      rw [← List.drop_drop (i := 1) (j := k),ht]; rfl
    rw [rows]
    cases i with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,Nat.add_zero]
      rw [List.getElem?_append_left (len ▸ hj)]
      by_cases h : k < j
      · rw [List.getElem?_append_right (by simp; omega),List.length_replicate]
        have hb : w[k]? = some b := by rw [← List.head?_drop,ht]; rfl
        have hj' : t[j-(k+1)]? = w[j]? := by rw [← hd,List.getElem?_drop]; congr 1; omega
        cases b <;> simp [color,List.getElem?_map,hj',hb,h,List.getElem?_eq_getElem hj]
      · rw [List.getElem?_append_left (by simp; omega),List.getElem?_replicate]; simp [h,show j < k+1 by omega]
    | succ i =>
      rw [Nat.succ_mul,List.getElem?_append_right (by rw [len]; omega),len]
      have hh := ih (k+1) hd (by simp at hn; omega) i (by simp at hi; omega)
      simpa only [show i*w.length+w.length+j-w.length = i*w.length+j by omega,
        show k+(i+1) = (k+1)+i by omega] using hh

theorem mask_entry (w : W) (i j : Fin w.length) : (mask w)[i.val*w.length+j.val]? =
    some (decide (i < j ∧ w[i.val]? ≠ w[j.val]?)) := by
  simpa [mask] using rowsEntry w w 0 (by simp) (by simp) i j i.isLt j.isLt

theorem hits_score (g w : W) (hg : w.length*w.length = g.length) :
    ((g.zip (mask w)).filter (fun p => p.1 && p.2)).length = score g w w.length :=
  CountScan.scoreBridge g w (mask w) hg (mask_len w) (mask_entry w)
end A203914.Verify.Stream

end

-- RawCount.lean
section
namespace A203914.Verify.Stream
open CountScan
open OAI.MetricKMedianRecovery.BitMachine
open OMA.S_oeis_a203914 A203914.Search

def countOut (x : List Bool) : List Bool := finish (iterWord advance (prepare mask x))
noncomputable def countMachine : PolyComputes countOut :=
  ((prepareMachine maskMachine).comp (iterMachine mstep (3*Polynomial.X) it_bound)).comp mend

theorem count_spec (g : List Bool) (k : Nat) (w : List Bool) :
    countOut (delimit g ++ (delimit (List.replicate k true) ++ w)) =
      [decide (w.length * w.length = g.length ∧ k ≤ score g w w.length)] := by
  rw [countOut, prepared]; simp only [iterWord,Lp,Rp,scan,mask_len,List.length_replicate]
  by_cases h : w.length * w.length = g.length
  · simp [h,hits,hits_score]
  · simp [h]
end A203914.Verify.Stream

end

-- RawExact.lean
section

namespace A203914.Verify.Stream

theorem raw_machine : Nonempty (Turing.TM2ComputableInPolyTime id (fun b : Bool => [b]) raw) := by
  refine ⟨realizeSingleton (parseMachine.comp (dispatchMachine countMachine)) ?_⟩
  exact dispatch_packet count_spec

end A203914.Verify.Stream

end

-- ExactCut.lean
section
namespace A203914.Integrated
open OMA.S_oeis_a203914
theorem exactCut : P = NP → ApproximatesMaxCut 1 :=
  exactCut_of_verifier Verify.Stream.raw_machine
end A203914.Integrated

end

theorem OMA.solution : OMA.R_oeis_a203914_R1.H2 := A203914.Integrated.exactCut
