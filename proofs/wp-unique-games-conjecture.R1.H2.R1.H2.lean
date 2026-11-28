import OMAReductions.R_wp_unique_games_conjecture_R1_H2_R1
import Mathlib

/- Proof of the square-matrix 3-coloring to canonical binary 3SAT reduction.
Includes code adapted from OpenAI/math commit 3344da59991ed94f9ba711217b29c1d760badfa6
(The Unique Games Theorem / bin-packing Cook-Levin development), used under the Apache License 2.0. -/
-- Compact
section
namespace Compact
open Turing
variable {K : Type} [DecidableEq K]
abbrev Store (K : Type) := K → List Bool
inductive Cmd (K : Type) where
 | push (k : K) (b : Bool)
 | pop (k : K)
 | seq (p q : Cmd K)
 | test (k : K) (f : Option Bool → Bool) (p q : Cmd K)
 | loop (k : K) (f : Option Bool → Bool) (p : Cmd K)
namespace Cmd
inductive Run : Cmd K → Store K → Store K → Nat → Type where
 | push : Run (.push k b) s (Function.update s k (b :: s k)) 1
 | pop : Run (.pop k) s (Function.update s k (s k).tail) 1
 | seq : Run p s t n → Run q t u m → Run (.seq p q) s u (m+n)
 | yes : f (s k).head? = true → Run p s t n → Run (.test k f p q) s t (n+1)
 | no : f (s k).head? = false → Run q s t n → Run (.test k f p q) s t (n+1)
 | stop : f (s k).head? = false → Run (.loop k f p) s s 1
 | more : f (s k).head? = true → Run p s t n → Run (.loop k f p) t u m → Run (.loop k f p) s u (m+n+1)

def Lab : Cmd K → Type
 | .push .. | .pop .. => Unit
 | .seq p q => Lab p ⊕ Lab q
 | .test _ _ p q => Option (Lab p ⊕ Lab q)
 | .loop _ _ p => Option (Lab p)
noncomputable instance fintypeLab (p : Cmd K) : Fintype p.Lab := by
 induction p <;> dsimp [Lab] <;> infer_instance

def entry : (p : Cmd K) → p.Lab
 | .push .. | .pop .. => ()
 | .seq p _ => .inl p.entry
 | .test .. | .loop .. => none
abbrev St (L : Type) := TM2.Stmt (fun _ : K => Bool) L Bool
private def jump {L : Type} : Option L → St (K := K) L
 | none => .halt
 | some l => .goto (fun _ => l)
private def condAt {L : Type} (k : K) (f : Option Bool → Bool) (yes no : Option L) : St (K := K) L :=
 .peek k (fun _ b => f b) (.branch id (.load (fun _ => false) (jump yes)) (.load (fun _ => false) (jump no)))

def code {L : Type} : (p : Cmd K) → (p.Lab → L) → Option L → p.Lab → St (K := K) L
 | .push k b, _, out, _ => .push k (fun _ => b) (jump out)
 | .pop k, _, out, _ => .pop k (fun s _ => s) (jump out)
 | .seq p q, e, out, .inl i => code p (e ∘ Sum.inl) (some (e (.inr q.entry))) i
 | .seq _ q, e, out, .inr i => code q (e ∘ Sum.inr) out i
 | .test k f p q, e, _, none => condAt k f (some (e (some (.inl p.entry)))) (some (e (some (.inr q.entry))))
 | .test _ _ p _, e, out, some (.inl i) => code p (fun i => e (some (.inl i))) out i
 | .test _ _ _ q, e, out, some (.inr i) => code q (fun i => e (some (.inr i))) out i
 | .loop k f p, e, out, none => condAt k f (some (e (some p.entry))) out
 | .loop _ _ p, e, _, some i => code p (fun i => e (some i)) (some (e none)) i

private theorem jump_step {L : Type} (o : Option L) (s : Store K) : TM2.stepAux (jump o) false s = ⟨o,false,s⟩ := by cases o <;> rfl
private theorem cond_step {L : Type} (a b : Option L) (s : Store K) (k : K) (f : Option Bool → Bool) :
 TM2.stepAux (condAt k f a b) false s = ⟨if f (s k).head? then a else b,false,s⟩ := by
 cases h : f (s k).head? <;> simp [condAt,TM2.stepAux,h,jump_step]
private def once {L : Type} (M : L → St (K := K) L) {a b : TM2.Cfg (fun _ : K => Bool) L Bool} (h : TM2.step M a = some b) : StateTransition.EvalsToInTime (TM2.step M) a (some b) 1 := ⟨⟨1,h⟩,le_rfl⟩

private abbrev Cfg (K L : Type) := TM2.Cfg (fun _ : K => Bool) L Bool
private def cf {L : Type} (l : Option L) (s : Store K) : Cfg K L := ⟨l,false,s⟩
noncomputable def Run.sound {p : Cmd K} {s t : Store K} {n : Nat} (r : Run p s t n) {L : Type} (M : L → St (K := K) L) (e : p.Lab → L) (o : Option L) (h : ∀ i, M (e i) = p.code e o i) : StateTransition.EvalsToInTime (TM2.step M) (cf (some (e p.entry)) s) (some (cf o t)) n := by
 induction r generalizing o with
 | push | pop => apply once; simp only [cf,TM2.step,h,code,TM2.stepAux,jump_step]
 | seq _ _ ih jh => exact StateTransition.EvalsToInTime.trans _ _ _ _ _ _ (ih (e ∘ Sum.inl) _ (fun i => h (.inl i))) (jh (e ∘ Sum.inr) o (fun i => h (.inr i)))
 | yes hit _ ih =>
   apply StateTransition.EvalsToInTime.trans _ 1 _ _ _ _ _ (ih (fun i => e (some (.inl i))) o (fun i => h (some (.inl i))))
   apply once; simp only [cf,TM2.step,entry,Option.some.injEq]; rw [h none]; simp [code,cond_step,hit]
 | no hit _ ih =>
   apply StateTransition.EvalsToInTime.trans _ 1 _ _ _ _ _ (ih (fun i => e (some (.inr i))) o (fun i => h (some (.inr i))))
   apply once; simp only [cf,TM2.step,entry,Option.some.injEq]; rw [h none]; simp [code,cond_step,hit]
 | stop hit => apply once; simp only [cf,TM2.step,entry,Option.some.injEq]; rw [h none]; simp [code,cond_step,hit]
 | more hit _ _ ih jh =>
   have body := ih (fun i => e (some i)) (some (e none)) (fun i => h (some i))
   have rest := jh e o h
   apply StateTransition.EvalsToInTime.trans _ 1 _ _ _ _ _ (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ body rest)
   apply once; simp only [cf,TM2.step,entry,Option.some.injEq]; rw [h none]; simp [code,cond_step,hit]

noncomputable def machine [Fintype K] (p : Cmd K) (i o : K) : FinTM2 where
 K := K
 k₀ := i
 k₁ := o
 Γ := fun _ => Bool
 Λ := p.Lab
 main := p.entry
 σ := Bool
 initialState := false
 m := p.code id none

def singleStack (k : K) (xs : List Bool) : Store K := fun j => if j = k then xs else []
noncomputable def realizes [Fintype K] (p : Cmd K) (i o : K) {A B : Type} (ea : A → List Bool) (eb : B → List Bool) (f : A → B) (time : Polynomial Nat)
 (runs : ∀ a, Σ n, Run p (singleStack i (ea a)) (singleStack o (eb (f a))) n ×' (n ≤ time.eval (ea a).length)) : TM2ComputableInPolyTime ea eb f where
 tm := machine p i o
 inputAlphabet := Equiv.refl _
 outputAlphabet := Equiv.refl _
 time := time
 outputsFun a := by
   obtain ⟨n,r,hn⟩ := runs a
   have ex := r.sound (p.code id none) id none (fun _ => rfl)
   have start : initList (machine p i o) (ea a) = cf (some p.entry) (singleStack i (ea a)) := by
     rfl
   have done : haltList (machine p i o) (eb (f a)) = cf (none : Option p.Lab) (singleStack o (eb (f a))) := by
     rfl
   change StateTransition.EvalsToInTime _ (initList (machine p i o) ((ea a).map id)) (some (haltList (machine p i o) ((eb (f a)).map id))) _
   erw [show ((ea a).map (id : Bool → Bool)) = ea a from List.map_id _, show ((eb (f a)).map (id : Bool → Bool)) = eb (f a) from List.map_id _,start,done]
   exact ⟨ex.toEvalsTo,ex.steps_le_m.trans hn⟩
end Cmd
end Compact
end

-- Countdown
section
namespace Compact.Reg
open Compact.Cmd
variable {J S : Type} [DecidableEq J]
-- Loop counter is snapshotted before entry; the body preserves this counter.
-- 'repr n s' includes all live outer counters and the caller's frame.
noncomputable def countdown (k : J) (body : Cmd J) (step : S → S) (work : S → Nat)
 (repr : Nat → S → Store J) (C : Nat) (hC : 2 ≤ C)
 (count : ∀ n s, repr n s k = List.replicate n true)
 (frame : ∀ n s, Function.update (repr (n+1) s) k (List.replicate n true) = repr n s)
 (iter : ∀ n s, Σ m, Run body (repr n s) (repr n (step s)) m ×' (work s*C+m+2 ≤ work (step s)*C))
 (n : Nat) (s : S) : Σ m, Run (.loop k Option.isSome (.seq (.pop k) body)) (repr n s) (repr 0 (step^[n] s)) m ×' (work s*C+m ≤ work (step^[n] s)*C+1) := by
 induction n generalizing s with
 | zero => exact ⟨1,Run.stop (by simp [count]),by simp⟩
 | succ n ih =>
   have pop : Run (.pop k) (repr (n+1) s) (repr n s) 1 := by
     have h := Run.pop (k := k) (s := repr (n+1) s)
     simpa [count,List.replicate_succ,frame] using h
   obtain ⟨a,ra,ha⟩ := iter n s
   obtain ⟨b,rb,hb⟩ := ih (step s)
   refine ⟨_,Run.more (by simp [count,List.replicate_succ]) (Run.seq pop ra) rb,?_⟩
   rw [Function.iterate_succ_apply]; omega
end Compact.Reg
end

-- Registers
section
namespace Compact.Reg
inductive P (K : Type) where
 | zero (r : K) | inc (r : K) | dec (r : K) | len (r : K) | read (dst idx : K) | emit (r : K)
 | seq (a b : P K) | branch (r : K) (yes no : P K) | repeatN (r : K) (body : P K)
structure S (K : Type) where
 reg : K → Nat
 words : List Nat
 work : Nat
namespace S
def init : S K := ⟨fun _ => 0, [], 0⟩
def tick (s : S K) (n : Nat) : S K := {s with work := s.work+n}
def put [DecidableEq K] (s : S K) (r : K) (v cost : Nat) : S K := ⟨Function.update s.reg r v,s.words,s.work+cost⟩
end S
variable {K : Type} [DecidableEq K]
def P.exec (x : List Bool) : P K → S K → S K
 | .zero r,s => s.put r 0 (1+s.reg r)
 | .inc r,s => s.put r (s.reg r+1) 1
 | .dec r,s => s.put r (s.reg r-1) 1
 | .len r,s => s.put r x.length (1+s.reg r+x.length)
 | .read d i,s => s.put d (if x[s.reg i]?.getD false then 1 else 0) (1+s.reg d+s.reg i+x.length)
 | .emit r,s => ⟨s.reg,s.words++[s.reg r],s.work+(1+s.reg r)⟩
 | .seq a b,s => b.exec x (a.exec x s)
 | .branch r a b,s => if s.reg r ≠ 0 then a.exec x (s.tick 1) else b.exec x (s.tick 1)
 | .repeatN r b,s => (fun t => (b.exec x t).tick 1)^[s.reg r] (s.tick (1+s.reg r))
end Compact.Reg
end

-- RegCompiler
section
namespace Compact.Reg
open Cmd
variable {K J : Type} [DecidableEq K] [DecidableEq J]
-- The counter bank holds snapshots of outer loops. A program at level d
-- may use slots < d, provided those slots are initially empty.
abbrev Bank (N : Nat) := Fin N → Nat
structure Layout (K J : Type) [DecidableEq K] [DecidableEq J] (N : Nat) where
 C : Nat
 scale : 2 ≤ C
 reg : K → J
 slot : Fin N → J
 repr : List Bool → Bank N → S K → Store J
 headR : ∀ x f s k, repr x f s (reg k) = List.replicate (s.reg k) true
 headL : ∀ x f s i, repr x f s (slot i) = List.replicate (f i) true
 updateL : ∀ x f s i n, Function.update (repr x f s) (slot i) (List.replicate n true) = repr x (Function.update f i n) s
 tick : ∀ x f s n, repr x f (s.tick n) = repr x f s
 snapshot : Fin N → K → Cmd J
 snapRun : ∀ x f s i k, f i = 0 → Σ n, Run (snapshot i k) (repr x f s) (repr x (Function.update f i (s.reg k)) s) n ×' (n+1 ≤ (1+s.reg k)*C)
structure Sim {N : Nat} (L : Layout K J N) (d : Nat) (p : P K) where
 code : Cmd J
 sound : ∀ x f s, (∀ i : Fin N, i.val < d → f i = 0) → Σ n, Run code (L.repr x f s) (L.repr x f (p.exec x s)) n ×' (s.work*L.C+n ≤ (p.exec x s).work*L.C)
namespace Sim
variable {N d : Nat} {L : Layout K J N} {a b : P K}
def seq (A : Sim L d a) (B : Sim L d b) : Sim L d (.seq a b) where
 code := .seq A.code B.code
 sound x f s h := by
   obtain ⟨n,r,u⟩ := A.sound x f s h
   obtain ⟨m,t,v⟩ := B.sound x f _ h
   exact ⟨_,Run.seq r t,by change _ ≤ (b.exec x (a.exec x s)).work*L.C; omega⟩
def branch (k : K) (A : Sim L d a) (B : Sim L d b) : Sim L d (.branch k a b) where
 code := .test (L.reg k) Option.isSome A.code B.code
 sound x f s h := by
   have C := L.scale
   by_cases hk : s.reg k = 0
   · obtain ⟨m,t,v⟩ := B.sound x f (s.tick 1) h
     rw [L.tick] at t
     simp only [P.exec,hk,ne_eq,not_true_eq_false,if_false]
     exact ⟨_,Run.no (by simp [L.headR,hk]) t,by change (s.work+1)*L.C+m ≤ _ at v; rw [Nat.add_mul,one_mul] at v; omega⟩
   · obtain ⟨m,t,v⟩ := A.sound x f (s.tick 1) h
     rw [L.tick] at t
     simp only [P.exec,hk,ne_eq,not_false_eq_true,if_true]
     exact ⟨_,Run.yes (by obtain ⟨z,hz⟩ := Nat.exists_eq_succ_of_ne_zero hk; simp [L.headR,hz,List.replicate_succ]) t,by change (s.work+1)*L.C+m ≤ _ at v; rw [Nat.add_mul,one_mul] at v; omega⟩
noncomputable def repeatN (k : K) (hd : d < N) (B : Sim L d b) : Sim L (d+1) (.repeatN k b) where
 code := .seq (L.snapshot ⟨d,hd⟩ k) (.loop (L.slot ⟨d,hd⟩) Option.isSome (.seq (.pop (L.slot ⟨d,hd⟩)) B.code))
 sound x f s h := by
   let i : Fin N := ⟨d,hd⟩
   let R := fun n t => L.repr x (Function.update f i n) t
   let step := fun t => (b.exec x t).tick 1
   have hi : f i = 0 := h i (by simp [i])
   have upd0 : Function.update f i 0 = f := by rw [← hi,Function.update_eq_self]
   have iter n t : Σ m, Run B.code (R n t) (R n (step t)) m ×' (t.work*L.C+m+2 ≤ (step t).work*L.C) := by
     obtain ⟨m,r,v⟩ := B.sound x (Function.update f i n) t (by intro j hj; rw [Function.update_of_ne (show j ≠ i by intro e; subst j; exact (Nat.lt_irrefl d) hj)]; exact h j (by omega))
     have C := L.scale
     exact ⟨m,by simpa [R,step,L.tick] using r,by simp only [step,S.tick,Nat.add_mul,one_mul]; omega⟩
   let s' := s.tick (1+s.reg k)
   obtain ⟨m,r,hm⟩ := countdown (L.slot i) B.code step S.work R L.C L.scale (by simp [R,L.headL]) (by simp [R,L.updateL,Function.update_idem]) iter (s.reg k) s'
   obtain ⟨n,t,hn⟩ := L.snapRun x f s i k hi
   simp only [R,s',L.tick,upd0] at r
   refine ⟨_,Run.seq t r,?_⟩
   change _ ≤ (step^[s.reg k] s').work*L.C
   simp only [s',S.tick,Nat.add_mul] at hm hn ⊢
   omega
end Sim
structure Base {N : Nat} (L : Layout K J N) where
 zero : ∀ d k, Sim L d (.zero k)
 inc : ∀ d k, Sim L d (.inc k)
 dec : ∀ d k, Sim L d (.dec k)
 len : ∀ d k, Sim L d (.len k)
 read : ∀ d k i, Sim L d (.read k i)
 emit : ∀ d k, Sim L d (.emit k)
def P.depth : P K → Nat
 | .seq a b | .branch _ a b => max a.depth b.depth
 | .repeatN _ b => b.depth + 1
 | _ => 0
noncomputable def compile {N : Nat} {L : Layout K J N} (B : Base L) (p : P K) : ∀ d, p.depth ≤ d → d ≤ N → Sim L d p := by
 induction p with
 | zero k => exact fun d _ _ => B.zero d k
 | inc k => exact fun d _ _ => B.inc d k
 | dec k => exact fun d _ _ => B.dec d k
 | len k => exact fun d _ _ => B.len d k
 | read k i => exact fun d _ _ => B.read d k i
 | emit k => exact fun d _ _ => B.emit d k
 | seq a b A B => exact fun d h H => (A d ((le_max_left ..).trans h) H).seq (B d ((le_max_right ..).trans h) H)
 | branch k a b A B => exact fun d h H => Sim.branch k (A d ((le_max_left ..).trans h) H) (B d ((le_max_right ..).trans h) H)
 | repeatN k b B =>
   rintro (_|d) h H <;> simp only [P.depth] at h
   · omega
   · exact Sim.repeatN k (by omega) (B d (by omega) (by omega))
end Compact.Reg
end

-- OAI.Computability.BinPacking.Model
section
/- Adapted from OpenAI/openai math, 3344da59991ed94f9ba711217b29c1d760badfa6. See LICENSE.openai. -/

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity

def encodeWord (n : Nat) : List Bool := List.replicate n true ++ [false]

end BinPackingGames.Foundations.Complexity

namespace BinPackingGames.Foundations.Complexity.MachineFiniteAlphabet

open Turing

def FiniteAlphabet (M : FinTM2) : Prop := ∀ k, Finite (M.Γ k)

end BinPackingGames.Foundations.Complexity.MachineFiniteAlphabet

namespace BinPackingGames.Foundations.Complexity.CookLevin

def pairBits (input : List Bool × List Bool) : List Bool :=
  encodeWord input.1.length ++ input.1 ++ input.2

structure NPVerifier where
  witnessBound : Polynomial Nat
  verify : (List Bool × List Bool) → Bool
  computation : Turing.TM2ComputableInPolyTime pairBits (fun bit => [bit]) verify
  finiteAlphabet : (k : computation.tm.K) → Fintype (computation.tm.Γ k)

def NPVerifier.Accepts (verifier : NPVerifier) (input : List Bool) : Prop :=
  ∃ witness : List Bool,
    witness.length ≤ verifier.witnessBound.eval input.length ∧
    verifier.verify (input, witness) = true

def InNP (language : List Bool → Prop) : Prop :=
  ∃ verifier : NPVerifier, ∀ input, language input ↔ verifier.Accepts input

end BinPackingGames.Foundations.Complexity.CookLevin

end
end OAI
end

-- OAI.Computability.BinPacking.Reductions.Target
section
/- Adapted from OpenAI/openai math, 3344da59991ed94f9ba711217b29c1d760badfa6. See LICENSE.openai. -/

namespace OAI

namespace BinPackingGames.Foundations.Target

structure Literal («variables» : Nat) where
  variableIndex : Fin «variables»
  positive : Bool
  deriving DecidableEq

def Literal.eval {n : Nat} (literal : Literal n) (assignment : Fin n → Bool) : Bool :=
  if literal.positive then assignment literal.variableIndex else !(assignment literal.variableIndex)

abbrev Clause («variables» : Nat) := Vector (Literal «variables») 3

def Clause.eval {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  «variables» : Nat
  clauses : List (Clause «variables»)

def Formula.Satisfiable (formula : Formula) : Prop :=
  ∃ assignment : Fin formula.variables → Bool,
    ∀ clause ∈ formula.clauses, clause.eval assignment = true

end BinPackingGames.Foundations.Target
end OAI
end

-- OAI.Computability.BinPacking.Computation.Machine
section
/- Adapted from OpenAI/openai math, 3344da59991ed94f9ba711217b29c1d760badfa6. See LICENSE.openai. -/

namespace OAI

namespace BinPackingGames.Foundations.Complexity

section

def encodeWords : List Nat → List Bool
  | [] => []
  | n :: ns => encodeWord n ++ encodeWords ns

open Target

def literalWords {n : Nat} (literal : Literal n) : List Nat :=
  [literal.variableIndex.val, if literal.positive then 1 else 0]

def clauseWords {n : Nat} (clause : Clause n) : List Nat :=
  literalWords clause[0] ++ literalWords clause[1] ++ literalWords clause[2]

def formulaWords (formula : Formula) : List Nat :=
  [formula.variables, formula.clauses.length] ++ formula.clauses.flatMap clauseWords

def formulaBits (formula : Formula) : List Bool := encodeWords (formulaWords formula)

end
end BinPackingGames.Foundations.Complexity
end OAI
end

-- Emit
section
namespace Compact.Emit
open Cmd OAI.BinPackingGames.Foundations.Complexity
variable {K : Type} [DecidableEq K]
-- Move one bit selected by the source head, and advance the source stack.
def moveOne (i o : K) : Cmd K := .seq (.test i (· == some true) (.push o true) (.push o false)) (.pop i)
def reverseOnto (i o : K) : Cmd K := .loop i Option.isSome (moveOne i o)
private abbrev upd (s : Store K) (k : K) (xs : List Bool) := Function.update s k xs
noncomputable def moveRun {i o : K} (h : i ≠ o) (b : Bool) (xs : List Bool) (s : Store K) (hin : s i = b :: xs) :
 Run (moveOne i o) s (upd (upd s o (b :: s o)) i xs) 3 := by
 have a : Run (.test i (· == some true) (.push o true) (.push o false)) s (upd s o (b :: s o)) 2 := by
   cases b
   · exact Run.no (by simp [hin]) Run.push
   · exact Run.yes (by simp [hin]) Run.push
 have z := Run.seq a (Run.pop (k := i))
 simpa [moveOne,upd,Function.update_of_ne h,hin] using z

noncomputable def reverseRun {i o : K} (h : i ≠ o) (s : Store K) (xs ys : List Bool) :
 Run (reverseOnto i o) (upd (upd s o ys) i xs) (upd (upd s o (xs.reverse ++ ys)) i []) (4*xs.length+1) := by
 induction xs generalizing ys with
 | nil => exact Run.stop (by simp [upd])
 | cons b xs ih =>
   let t := upd (upd s o ys) i (b :: xs)
   have m := moveRun h b xs t (by simp [t,upd])
   have E : upd (upd t o (b :: t o)) i xs = upd (upd s o (b :: ys)) i xs := by
     funext j; by_cases a : j = i <;> by_cases c : j = o <;> simp_all [upd,t,Function.update]
   rw [E] at m
   have r := Run.more (k := i) (f := Option.isSome) (by simp [t,upd]) m (ih (b::ys))
   simpa [reverseOnto,t,List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using r

-- Emit a unary word without consuming the counter that supplied its length.
def spread (i o w : K) : Cmd K := .loop i Option.isSome (.seq (.pop i) (.seq (.push o true) (.push w true)))
private def at3 (s : Store K) (i o w : K) (xs ys zs : List Bool) := upd (upd (upd s i xs) o ys) w zs
noncomputable def spreadRun {i o w : K} (hi : i ≠ o) (hw : i ≠ w) (ho : o ≠ w) (s : Store K) (xs ys zs : List Bool) :
 Run (spread i o w) (at3 s i o w xs ys zs) (at3 s i o w [] (List.replicate xs.length true ++ ys) (List.replicate xs.length true ++ zs)) (4*xs.length+1) := by
 induction xs generalizing ys zs with
 | nil => exact Run.stop (by simp [at3,upd,hi,hw])
 | cons b xs ih =>
   let t := at3 s i o w (b::xs) ys zs
   have m := Run.seq (Run.pop (s := t) (k := i)) (Run.seq (Run.push (k := o) (b := true)) (Run.push (k := w) (b := true)))
   have e : ∀ {n} {u : Store K}, Run (.seq (.pop i) (.seq (.push o true) (.push w true))) t u n → u = at3 s i o w xs (true::ys) (true::zs) := by
     intro n u r; cases r with | seq a d => cases a; cases d with | seq b c => cases b; cases c; funext j; by_cases H : j = i <;> by_cases J : j = o <;> by_cases T : j = w <;> simp_all [upd,at3,t,Function.update]
   have m' : Run (.seq (.pop i) (.seq (.push o true) (.push w true))) t (at3 s i o w xs (true::ys) (true::zs)) 3 := e m ▸ m
   have r := Run.more (k := i) (f := Option.isSome) (by simp [t,at3,upd,hi,hw]) m' (ih (true::ys) (true::zs))
   simpa [spread,t,Nat.mul_add,Nat.add_assoc,List.replicate_succ',List.append_assoc] using r

def word (i o w : K) : Cmd K := .seq (.push o false) (.seq (spread i o w) (reverseOnto w i))
noncomputable def wordRun {i o w : K} (hi : i ≠ o) (hw : i ≠ w) (ho : o ≠ w) (s : Store K) (n : Nat) (ys : List Bool) :
 Run (word i o w) (at3 s i o w (List.replicate n true) ys []) (at3 s i o w (List.replicate n true) (encodeWord n ++ ys) []) (8*n+3) := by
   let xs := List.replicate n true
   have swap (j : K) (a b c : List Bool) : at3 s i o w a b c j = (upd (upd (upd s o b) i a) w c) j := by
     by_cases I : j = i <;> by_cases O : j = o <;> by_cases W : j = w <;> simp_all [at3,upd,Function.update]
   have hpush : upd (at3 s i o w xs ys []) o (false :: at3 s i o w xs ys [] o) = at3 s i o w xs (false::ys) [] := by
     funext j; by_cases I : j = i <;> by_cases O : j = o <;> by_cases W : j = w <;> simp_all [at3,upd,Function.update]
   have a := Run.push (s := at3 s i o w xs ys []) (k := o) (b := false)
   change Run _ _ (upd _ _ _) _ at a; rw [hpush] at a
   have b := spreadRun hi hw ho s xs (false::ys) []
   let out := encodeWord n ++ ys
   have c := reverseRun hw.symm (upd s o out) xs []
   have ec (a c : List Bool) : upd (upd (upd s o out) i a) w c = at3 s i o w a out c := (funext (fun j => swap j a out c)).symm
   simp only [ec,List.reverse_replicate,List.append_nil,xs,List.length_replicate] at c
   simp only [xs,List.length_replicate,List.append_nil] at b
   have outEq : out = List.replicate n true ++ false :: ys := by simp [out,encodeWord,List.append_assoc]
   rw [outEq] at c
   have d := Run.seq a (Run.seq b c)
   convert d using 1 <;> simp [out,word,xs,encodeWord,List.append_assoc] <;> omega
end Compact.Emit
end

-- Cleanup
section
open Compact.Cmd
namespace Compact.Cleanup
variable {K : Type} [DecidableEq K]
theorem growth {s t : Store K} {p : Cmd K} {n : Nat} (r : Run p s t n) (i : K) : (t i).length ≤ (s i).length+n := by
 induction r with
 | push => simp [Function.update]; split <;> simp_all
 | pop => simp [Function.update]; split <;> simp_all <;> omega
 | seq _ _ a b => omega
 | stop _ => omega
 | yes _ _ h | no _ _ h => omega
 | more _ _ _ h g => omega

def clear (k : K) : Cmd K := .loop k Option.isSome (.pop k)
noncomputable def clearRun (k : K) (s : Store K) (xs : List Bool) : Run (clear k) (Function.update s k xs) (Function.update s k []) (2*xs.length+1) := by
 induction xs with
 | nil => exact Run.stop (by simp)
 | cons b xs ih =>
   have p := Run.pop (k := k) (s := Function.update s k (b::xs))
   simp only [Function.update_self,List.tail_cons,Function.update_idem] at p
   have r := Run.more (k := k) (f := Option.isSome) (by simp) p ih
   convert r using 1 <;> first | omega | rfl | (simp; omega)

def wipe (idle : K) : List K → Cmd K
 | [] => clear idle
 | i :: is => .seq (clear i) (wipe idle is)
noncomputable def wipeRun (idle : K) (ks : List K) (s : Store K) (B : Nat) (bound : ∀ i, (s i).length ≤ B) :
 Σ n, Run (wipe idle ks) s (fun i => if i ∈ idle::ks then [] else s i) n ×' (n ≤ (ks.length+1)*(2*B+1)) := by
 induction ks generalizing s with
 | nil =>
   have r := clearRun idle s (s idle)
   rw [Function.update_eq_self] at r
   exact ⟨2*(s idle).length+1,by change Run (clear idle) _ _ _; convert r using 1; funext j; by_cases h : j = idle <;> simp [Function.update,h],by simpa using Nat.add_le_add_right (Nat.mul_le_mul_left 2 (bound idle)) 1⟩
 | cons k ks ih =>
   have r := clearRun k s (s k); rw [Function.update_eq_self] at r
   obtain ⟨n,t,h⟩ := ih (Function.update s k []) (fun i => by by_cases H : i = k <;> simp_all [Function.update])
   refine ⟨n+(2*(s k).length+1),?_,?_⟩
   · change Run (.seq _ _) _ _ _; convert Run.seq r t using 1
     funext j; by_cases A : j = idle <;> by_cases B : j = k <;> by_cases C : j ∈ ks <;> simp_all [Function.update]
   · change _ ≤ ((ks.length+1)+1)*(2*B+1); rw [Nat.succ_mul (ks.length+1) (2*B+1)]; exact Nat.add_le_add h (by have := bound k; omega)
noncomputable def others [Fintype K] (a : K) : List K := (Finset.univ.erase a).toList
@[simp] theorem mem_others [Fintype K] {i a : K} : i ∈ others a ↔ i ≠ a := by simp [others]
noncomputable def finish [Fintype K] (p : Cmd K) (a o : K) : Cmd K := .seq p (.seq (wipe o (others a)) (Emit.reverseOnto a o))
noncomputable def finishRun [Fintype K] {p : Cmd K} {i a o : K} (ha : a ≠ o) {x y : List Bool} {s : Store K} {n : Nat}
 (r : Run p (singleStack i x) s n) (out : s a = y.reverse) :
 Σ m, Run (finish p a o) (singleStack i x) (singleStack o y) m ×' (m ≤ n+((others a).length+1)*(2*(x.length+n)+1)+(4*(x.length+n)+1)) := by
 have bound j : (s j).length ≤ x.length+n := (growth r j).trans (by by_cases h : j = i <;> simp [singleStack,h])
 obtain ⟨b,w,hb⟩ := wipeRun o (others a) s _ bound
 let nils : Store K := fun _ => []
 have rev := Emit.reverseRun ha nils y.reverse []
 have start : (fun j => if j ∈ o :: others a then [] else s j) = Function.update (Function.update nils o []) a y.reverse := by
   funext j; by_cases H : j = a <;> by_cases G : j = o <;> simp_all [Function.update,nils]
 have done : Function.update (Function.update nils o y) a [] = singleStack o y := by
   funext j; by_cases H : j = a <;> by_cases G : j = o <;> simp_all [singleStack,Function.update,nils]
 rw [start] at w
 simp only [List.reverse_reverse,List.append_nil,done,List.length_reverse] at rev
 have hlen := bound a; rw [out,List.length_reverse] at hlen
 exact ⟨_,Run.seq r (Run.seq w rev),by omega⟩
end Compact.Cleanup
end

-- Prim
section
namespace Compact.Prim
open Cmd OAI.BinPackingGames.Foundations.Complexity
variable {J : Type} [DecidableEq J]
private abbrev U (s : Store J) (k : J) (v : List Bool) := Function.update s k v
def clear (d : J) : Cmd J := .loop d Option.isSome (.pop d)
noncomputable def clearRun (d : J) (s : Store J) : Run (clear d) s (U s d []) (2*(s d).length+1) := by
 suffices H : ∀ xs : List Bool, Run (clear d) (U s d xs) (U s d []) (2*xs.length+1) by simpa using H (s d)
 intro xs; induction xs with
 | nil => exact Run.stop (by simp [U])
 | cons b xs ih =>
   have p := Run.pop (s := U s d (b::xs)) (k := d)
   simp [U] at p
   have r := Run.more (k:=d) (f:=Option.isSome) (by simp) p ih
   convert r using 1 <;> rfl

def splitBit (f : Bool → Bool) (w i d : J) : Cmd J := .test w (· == some true)
 (.seq (.push i true) (.seq (.push d (f true)) (.pop w)))
 (.seq (.push i false) (.seq (.push d (f false)) (.pop w)))
def splitBack (f : Bool → Bool) (w i d : J) : Cmd J := .loop w Option.isSome (splitBit f w i d)
private abbrev A (s : Store J) (w i d : J) (xs ys zs : List Bool) := U (U (U s d zs) i ys) w xs
private noncomputable def splitRun (f : Bool → Bool) {w i d : J} (wi : w ≠ i) (wd : w ≠ d) (id' : i ≠ d) (s : Store J) (xs ys zs : List Bool) :
 Run (splitBack f w i d) (A s w i d xs ys zs) (A s w i d [] (xs.reverse ++ ys) (xs.reverse.map f ++ zs)) (5*xs.length+1) := by
 induction xs generalizing ys zs with
 | nil => exact Run.stop (by simp [A,U])
 | cons b xs ih =>
   let t := A s w i d (b::xs) ys zs
   have p := Run.seq (Run.push (s:=t) (k:=i) (b:=b)) (Run.seq (Run.push (k:=d) (b:=f b)) (Run.pop (k:=w)))
   have E : Function.update (Function.update (Function.update t i (b::t i)) d (f b :: (Function.update t i (b::t i)) d)) w (((Function.update (Function.update t i (b::t i)) d (f b :: (Function.update t i (b::t i)) d)) w).tail) = A s w i d xs (b::ys) (f b::zs) := by
     dsimp [t,A,U]; (funext j; simp only [U, Function.update]; split_ifs <;> (subst_vars <;> simp_all))
   rw [E] at p
   have q : Run (splitBit f w i d) t (A s w i d xs (b::ys) (f b::zs)) 4 := by
     cases b
     · exact Run.no (by simp [t,A,U]) p
     · exact Run.yes (by simp [t,A,U]) p
   have r := Run.more (k:=w) (f:=Option.isSome) (by simp [t,A,U]) q (ih (b::ys) (f b::zs))
   convert r using 1 <;> first | rfl | simp [List.reverse_cons,List.append_assoc]

def clone (f : Bool → Bool) (d i w : J) : Cmd J := .seq (clear d) (.seq (Emit.reverseOnto i w) (splitBack f w i d))
noncomputable def cloneRun (f : Bool → Bool) {d i w : J} (di : d ≠ i) (dw : d ≠ w) (iw : i ≠ w) (s : Store J) (empty : s w = []) :
 Run (clone f d i w) s (U s d ((s i).map f)) (2*(s d).length+9*(s i).length+3) := by
 have a := clearRun d s
 have b := Emit.reverseRun iw (U s d []) (s i) []
 have c := splitRun f iw.symm dw.symm di.symm s (s i).reverse [] []
 simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at b c
 convert Run.seq a (Run.seq (p:=Emit.reverseOnto i w) (q:=splitBack f w i d) (s:=U s d []) (t:=A s w i d (s i).reverse [] []) (by convert b using 1 <;> (funext j; simp only [U, Function.update]; split_ifs <;> (subst_vars <;> simp_all))) c) using 1
 · rfl
 · (funext j; simp only [U, Function.update]; split_ifs <;> (subst_vars <;> simp_all))
 · omega

def len (d i w : J) := clone (fun _ => true) d i w
abbrev copyLen (d src w : J) := len d src w
noncomputable def lenRun {d i w : J} (di : d ≠ i) (dw : d ≠ w) (iw : i ≠ w) (s : Store J) (empty : s w = []) :
 Run (len d i w) s (U s d (List.replicate (s i).length true)) (2*(s d).length+9*(s i).length+3) := by
 simpa [len,List.map_const'] using cloneRun (fun _ => true) di dw iw s empty

def emit (r out w : J) : Cmd J := .seq (Emit.reverseOnto r w) (.seq (splitBack (fun _ => true) w r out) (.push out false))
noncomputable def emitRun {r out w : J} (ro : r ≠ out) (rw' : r ≠ w) (ow : out ≠ w) (s : Store J) (empty : s w = []) :
 Run (emit r out w) s (U s out ((encodeWord (s r).length).reverse ++ s out)) (9*(s r).length+3) := by
 have a := Emit.reverseRun rw' s (s r) []
 have b := splitRun (fun _ => true) rw'.symm ow.symm ro s (s r).reverse [] (s out)
 simp only [List.reverse_reverse,List.append_nil,List.length_reverse,List.map_const'] at a b
 let t := A s w r out [] (s r) (List.replicate (s r).length true ++ s out)
 have p := Run.push (s:=t) (k:=out) (b:=false)
 have a' : Run (Emit.reverseOnto r w) s (A s w r out (s r).reverse [] (s out)) (4*(s r).length+1) := by convert a using 1 <;> (funext j; simp only [U, Function.update]; split_ifs <;> (subst_vars <;> simp_all))
 convert Run.seq a' (Run.seq b p) using 1
 · rfl
 · simp only [encodeWord,List.reverse_append,List.reverse_replicate,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append]; dsimp [t,A]; (funext j; simp only [U, Function.update]; split_ifs <;> (subst_vars <;> simp_all))
 · omega

private def skipN (n x : J) : Cmd J := .loop n Option.isSome (.seq (.pop n) (.pop x))
private noncomputable def skipRun {n x : J} (nx : n ≠ x) (s : Store J) (ns xs : List Bool) :
 Run (skipN n x) (U (U s x xs) n ns) (U (U s x (xs.drop ns.length)) n []) (3*ns.length+1) := by
 induction ns generalizing xs with
 | nil => simpa [skipN] using (Run.stop (p:=Cmd.seq (.pop n) (.pop x)) (k:=n) (f:=Option.isSome) (s:=U (U s x xs) n []) (by simp [U]))
 | cons b ns ih =>
   let t := U (U s x xs) n (b::ns)
   have a := Run.seq (Run.pop (s:=t) (k:=n)) (Run.pop (k:=x))
   have a' : Run (.seq (.pop n) (.pop x)) t (U (U s x xs.tail) n ns) 2 := by convert a using 1; dsimp [t]; (funext j; simp only [U, Function.update]; split_ifs <;> (subst_vars <;> simp_all))
   have r := Run.more (k:=n) (f:=Option.isSome) (by simp [t,U]) a' (ih xs.tail)
   convert r using 1
   · rfl
   · cases xs <;> simp [List.drop_succ_cons]
   · simp; omega

def read (d idx input : J) (w : Fin 3 → J) : Cmd J :=
 .seq (len (w 0) idx (w 2)) (.seq (clone id (w 1) input (w 2)) (.seq (skipN (w 0) (w 1)) (.seq (clear d) (.seq (.test (w 1) (· == some true) (.push d true) (.pop d)) (clear (w 1))))))

private noncomputable def bitRun (x d : J) (s : Store J) (e : s d = []) :
 Run (.test x (· == some true) (.push d true) (.pop d)) s (U s d (List.replicate (if (s x).head?.getD false then 1 else 0) true)) 2 := by
 cases h : (s x).head? with
 | none => exact Run.no (by simp [h]) (by simpa [h,e,U] using (Run.pop (k:=d) (s:=s)))
 | some b => cases b with
   | false => exact Run.no (by simp [h]) (by simpa [h,e,U] using (Run.pop (k:=d) (s:=s)))
   | true => exact Run.yes (by simp [h]) (by simpa [h,e,U] using (Run.push (k:=d) (b:=true) (s:=s)))

noncomputable def readRun {d idx input : J} {w : Fin 3 → J} (inj : Function.Injective w)
 (hd : ∀ j, w j ≠ d) (hi : ∀ j, w j ≠ idx) (hx : ∀ j, w j ≠ input) (s : Store J) (empty : ∀ j, s (w j) = []) :
 Run (read d idx input w) s (U s d (List.replicate (if (s input)[(s idx).length]?.getD false then 1 else 0) true))
 (12*(s idx).length+9*(s input).length+2*(s d).length+2*((s input).length-(s idx).length)+11) := by
 have hn : w 0 ≠ w 1 := fun h => (by decide : (0:Fin 3) ≠ 1) (inj h)
 have hn2 : w 0 ≠ w 2 := fun h => (by decide : (0:Fin 3) ≠ 2) (inj h)
 have hx2 : w 1 ≠ w 2 := fun h => (by decide : (1:Fin 3) ≠ 2) (inj h)
 let ns := List.replicate (s idx).length true
 let xs := s input
 let ys := xs.drop ns.length
 let result := List.replicate (if ys.head?.getD false then 1 else 0) true
 let t := U s (w 0) ns
 let u := U s (w 1) ys
 let v := U u d []
 have a := lenRun (hi 0) hn2 (hi 2).symm s (empty 2)
 have b := cloneRun id (hx 1) hx2 (hx 2).symm t (by simp [t,U,hn2.symm,empty])
 simp only [List.map_id] at b
 have c := skipRun hn s ns xs
 have c' : Run (skipN (w 0) (w 1)) (U t (w 1) (t input)) u (3*ns.length+1) := by
   convert c using 1
   · dsimp [xs,t]; have := hx 0; (funext j; simp only [U, Function.update]; split_ifs <;> (subst_vars <;> simp_all))
   · dsimp [ys,u]; have := empty 0; (funext j; simp only [U, Function.update]; split_ifs <;> (subst_vars <;> simp_all))
 have f := clearRun d u
 have g := bitRun (w 1) d v (by simp [v,U])
 have gv : v (w 1) = ys := by simp [v,u,U,hd 1]
 rw [gv] at g
 have z := clearRun (w 1) (U v d result)
 have allr := Run.seq a (Run.seq b (Run.seq c' (Run.seq f (Run.seq g z))))
 have res : result = List.replicate (if (s input)[(s idx).length]?.getD false then 1 else 0) true := by simp [result,ys,xs,ns]
 have finalE : U (U v d result) (w 1) [] = U s d result := by dsimp only [v,u]; have := hd 1; have := empty 1; (funext j; simp only [U, Function.update]; split_ifs <;> (subst_vars <;> simp_all))
 change Run _ _ (U (U v d result) (w 1) []) _ at allr
 rw [finalE,res] at allr
 convert allr using 1
 · rfl
 · simp [t,u,v,U,hn.symm,(hd 1).symm,hd 1,(hx 0).symm,empty,ys,xs,ns]; omega

noncomputable def copyLenRun {d src w : J} (ds : d ≠ src) (dw : d ≠ w) (sw : src ≠ w) (s : Store J) (empty : s w = []) :
 Run (copyLen d src w) s (U s d (List.replicate (s src).length true)) (2*(s d).length+9*(s src).length+3) := lenRun ds dw sw s empty

theorem readCost_le (d i x : Nat) : 12*i+9*x+2*d+2*(x-i)+11 ≤ 12*(1+d+i+x) := by omega

end Compact.Prim
end

-- Physical
section
namespace Compact.Reg.Phys
open Cmd OAI.BinPackingGames.Foundations.Complexity
variable {K : Type} [DecidableEq K] {N : Nat}
abbrev J (K : Type) (N : Nat) := K ⊕ Fin N ⊕ (Fin 3 ⊕ Fin 3)
abbrev reg (k : K) : J K N := .inl k
abbrev slot (i : Fin N) : J K N := .inr (.inl i)
abbrev io (i : Fin 3) : J K N := .inr (.inr (.inl i))
abbrev tmp (i : Fin 3) : J K N := .inr (.inr (.inr i))
def repr (x : List Bool) (f : Bank N) (s : S K) : Store (J K N)
 | .inl k => List.replicate (s.reg k) true
 | .inr (.inl i) => List.replicate (f i) true
 | .inr (.inr (.inl i)) => if i = 0 then x else if i = 1 then (encodeWords s.words).reverse else []
 | .inr (.inr (.inr _)) => []
@[simp] theorem setSlot (x f s) (i : Fin N) (n : Nat) : Function.update (repr (K:=K) x f s) (slot i) (List.replicate n true) = repr x (Function.update f i n) s := by
 funext j; rcases j with k|(l|(u|v)); swap; by_cases h : l=i <;> simp [Function.update,repr,h]; all_goals rfl
@[simp] theorem setReg (x) (f : Bank N) (s : S K) (k : K) (n c : Nat) : Function.update (repr x f s) (reg k) (List.replicate n true) = repr x f (s.put k n c) := by
 funext j; rcases j with k'|(l|z)
 · by_cases h : k'=k <;> simp [repr,S.put,Function.update,h]
 · rfl
 · cases z <;> rfl
theorem wordsAppend (ws : List Nat) (n : Nat) : encodeWords (ws++[n]) = encodeWords ws ++ encodeWord n := by
 induction ws <;> simp_all [encodeWords,List.append_assoc]
@[simp] theorem setOut (x f) (s : S K) (n c : Nat) : Function.update (repr (N:=N) x f s) (io 1) ((encodeWord n).reverse ++ (encodeWords s.words).reverse) = repr x f ⟨s.reg,s.words++[n],c⟩ := by
 funext j; rcases j with k|(l|(u|v))
 · rfl
 · rfl
 · fin_cases u <;> simp [Function.update,repr,wordsAppend,List.reverse_append]
 · rfl
noncomputable def layout (K : Type) [DecidableEq K] (N : Nat) : Layout K (J K N) N where
 C := 20
 scale := by decide
 reg := reg
 slot := slot
 repr := repr
 headR := by intros; rfl
 headL := by intros; rfl
 updateL := setSlot
 tick := by intros; rfl
 snapshot i k := Prim.len (slot i) (reg k) (tmp 0)
 snapRun x f s i k hi := by
   have r := Prim.lenRun (d:=slot i) (i:=reg k) (w:=tmp 0) (by simp) (by simp) (by simp) (repr x f s) rfl
   change Run _ _ (Function.update _ _ _) _ at r
   simp only [show (repr x f s (reg k)).length = s.reg k by simp [repr],show (repr x f s (slot i)).length = 0 by simp [repr,hi],setSlot] at r
   exact ⟨_,r,by omega⟩
end Compact.Reg.Phys
end

-- Base
section
namespace Compact.Reg.Phys
open Cmd OAI.BinPackingGames.Foundations.Complexity
variable {K : Type} [DecidableEq K] {N : Nat}
private theorem rlen (x) (f : Bank N) (s : S K) (k : K) : (repr x f s (reg k)).length = s.reg k := List.length_replicate
private theorem ri (x) (f : Bank N) (s : S K) : repr x f s (io 0) = x := rfl
private theorem ro (x) (f : Bank N) (s : S K) : repr x f s (io 1) = (encodeWords s.words).reverse := rfl
noncomputable def base (K : Type) [DecidableEq K] (N : Nat) : Base (layout K N) where
 zero d k := ⟨Prim.clear (reg k),fun x f s _ => by
   have r := Prim.clearRun (reg k) (repr x f s)
   have e := setReg x f s k (0) (1+s.reg k)
   change Run _ _ (Function.update _ _ _) _ at r
   simp only [rlen,ri] at r
   simp only [List.replicate_zero] at e
   rw [e] at r
   exact ⟨_,r,by change s.work*20+_ ≤ (s.work+_)*20; omega⟩⟩
 inc d k := ⟨.push (reg k) true,fun x f s _ => by
   have r := Run.push (s:=repr x f s) (k:=reg k) (b:=true)
   have e := setReg x f s k (s.reg k+1) (1)
   change Run _ _ (Function.update _ _ _) _ at r
   simp only [List.replicate_succ] at e
   change Run _ _ (Function.update _ _ (true :: List.replicate (s.reg k) true)) _ at r
   rw [e] at r
   exact ⟨_,r,by change s.work*20+_ ≤ (s.work+_)*20; omega⟩⟩
 dec d k := ⟨.pop (reg k),fun x f s _ => by
   have r := Run.pop (s:=repr x f s) (k:=reg k)
   have e := setReg x f s k (s.reg k-1) (1)
   change Run _ _ (Function.update _ _ _) _ at r
   have drop : (repr x f s (reg k)).tail = List.replicate (s.reg k-1) true := by simp [repr,List.tail_replicate]
   rw [drop] at r
   rw [e] at r
   exact ⟨_,r,by change s.work*20+_ ≤ (s.work+_)*20; omega⟩⟩
 len d k := ⟨Prim.len (reg k) (io 0) (tmp 0),fun x f s _ => by
   have r := Prim.lenRun (d:=reg k) (i:=io 0) (w:=tmp 0) (by simp) (by simp) (by simp) (repr x f s) rfl
   have e := setReg x f s k (x.length) (1+s.reg k+x.length)
   change Run _ _ (Function.update _ _ _) _ at r
   simp only [rlen,ri] at r
   rw [e] at r
   exact ⟨_,r,by change s.work*20+_ ≤ (s.work+_)*20; omega⟩⟩
 read d k j := ⟨Prim.read (reg k) (reg j) (io 0) tmp,fun x f s _ => by
   have r := Prim.readRun (d:=reg k) (idx:=reg j) (input:=io 0) (w:=tmp) (by intro a b h; simpa using h) (by simp) (by simp) (by simp) (repr x f s) (fun _ => rfl)
   have e := setReg x f s k (if x[s.reg j]?.getD false then 1 else 0) (1+s.reg k+s.reg j+x.length)
   change Run _ _ (Function.update _ _ _) _ at r
   simp only [rlen,ri] at r
   rw [e] at r
   exact ⟨_,r,by change s.work*20+_ ≤ (s.work+_)*20; omega⟩⟩
 emit d k := ⟨Prim.emit (reg k) (io 1) (tmp 0), fun x f s _ => by
   have r := Prim.emitRun (r:=reg k) (out:=io 1) (w:=tmp 0) (by simp) (by simp) (by simp) (repr x f s) rfl
   change Run _ _ (Function.update _ _ _) _ at r
   simp only [rlen,ro] at r
   rw [setOut x f s (s.reg k) (s.work+(1+s.reg k))] at r
   exact ⟨_,r,by change s.work*20+_ ≤ (s.work+_)*20; omega⟩⟩
end Compact.Reg.Phys
end

-- Realize
section
namespace Compact.Reg
open Cmd Phys Polynomial Turing OAI.BinPackingGames.Foundations.Complexity
variable {K : Type} [DecidableEq K] [Fintype K]
noncomputable def realize (p : P K) (F : List Bool → A) (enc : A → List Bool) (T : Polynomial Nat)
 (words : ∀ x, encodeWords (p.exec x S.init).words = enc (F x))
 (cost : ∀ x, (p.exec x S.init).work ≤ T.eval x.length) : TM2ComputableInPolyTime id enc F := by
 let N := p.depth
 let B := compile (Phys.base K N) p N le_rfl le_rfl
 let i : J K N := io 0
 let a : J K N := io 1
 let o : J K N := io 2
 let q := Cleanup.finish B.code a o
 let z : Polynomial Nat := 20*T
 let v : Polynomial Nat := X+z
 let u : Polynomial Nat := z+C ((Cleanup.others a).length+1)*(2*v+1)+(4*v+1)
 apply Cmd.realizes q i o id enc F u
 intro x
 obtain ⟨n,r,hn⟩ := B.sound x (fun _ => 0) S.init (by simp)
 have start : Phys.repr x (fun _ : Fin N => 0) (S.init : S K) = singleStack i x := by
   funext j; rcases j with k|(l|(u|v))
   · rfl
   · rfl
   · fin_cases u <;> rfl
   · rfl
 change Run _ (Phys.repr x (fun _ : Fin N => 0) S.init) (Phys.repr x (fun _ : Fin N => 0) (p.exec x S.init)) _ at r
 rw [start] at r
 have out : Phys.repr x (fun _ : Fin N => 0) (p.exec x S.init) a = (enc (F x)).reverse := by change (encodeWords _).reverse = _; rw [words]
 obtain ⟨m,r',hm⟩ := Cleanup.finishRun (o:=o) (by simp [a,o] : a ≠ o) r out
 refine ⟨m,r',hm.trans ?_⟩
 have nle : n ≤ z.eval x.length := by
   change 0*20+n ≤ (p.exec x S.init).work*20 at hn
   simp [z]; have := cost x; omega
 simp only [u,eval_add,eval_mul,eval_C,eval_ofNat,eval_one,v,eval_X,id_eq]
 gcongr
end Compact.Reg
end

-- FiniteRegs
section
/- A fixed register term mentions only finitely many locations. -/
namespace Compact.Reg
namespace P
def top : P Nat → Nat
 | .zero r | .inc r | .dec r | .len r | .emit r => r
 | .read d i => max d i | .seq a b => max a.top b.top
 | .branch r a b => max r (max a.top b.top) | .repeatN r b => max r b.top

def trim (n : Nat) (p : P Nat) (h : p.top < n) : P (Fin n) := match p with
 | .zero r => .zero ⟨r,h⟩ | .inc r => .inc ⟨r,h⟩ | .dec r => .dec ⟨r,h⟩ | .len r => .len ⟨r,h⟩ | .emit r => .emit ⟨r,h⟩
 | .read d i => .read ⟨d,lt_of_le_of_lt (le_max_left ..) h⟩ ⟨i,lt_of_le_of_lt (le_max_right ..) h⟩
 | .seq a b => .seq (trim n a (lt_of_le_of_lt (le_max_left ..) h)) (trim n b (lt_of_le_of_lt (le_max_right ..) h))
 | .branch r a b => .branch ⟨r,lt_of_le_of_lt (le_max_left ..) h⟩ (trim n a (lt_of_le_of_lt ((le_max_left ..).trans (le_max_right ..)) h)) (trim n b (lt_of_le_of_lt ((le_max_right ..).trans (le_max_right ..)) h))
 | .repeatN r b => .repeatN ⟨r,lt_of_le_of_lt (le_max_left ..) h⟩ (trim n b (lt_of_le_of_lt (le_max_right ..) h))

def restrict (n : Nat) (s : S Nat) : S (Fin n) := ⟨fun j => s.reg j.val,s.words,s.work⟩
private theorem restrict_put {n} (s : S Nat) (r : Fin n) (v c) : (restrict n s).put r v c = restrict n (s.put r.val v c) := by
 unfold S.put restrict; congr 1; funext j; by_cases e : j = r
 · subst j; simp
 · simp [Function.update_of_ne e,Function.update_of_ne (show j.val ≠ r.val from fun h => e (Fin.ext h))]
private theorem restrict_tick (n s c) : (restrict n s).tick c = restrict n (s.tick c) := rfl

theorem trim_exec (p : P Nat) (x n h) (s : S Nat) : (trim n p h).exec x (restrict n s) = restrict n (p.exec x s) := by
 induction p generalizing s with
 | zero | inc | dec | len | read => apply restrict_put
 | emit => rfl
 | seq a b ia ib => simp only [trim,P.exec,ia,ib]
 | branch r a b ia ib => simp only [trim,P.exec,restrict_tick]; change (if s.reg r ≠ 0 then _ else _) = _; split <;> rename_i hh <;> simp_all
 | repeatN r b ib =>
   have aux (k : Nat) (t : S Nat) (hb : b.top < n) : (fun z => ((trim n b hb).exec x z).tick 1)^[k] (restrict n t) = restrict n ((fun z => (b.exec x z).tick 1)^[k] t) := by
     induction k with | zero => rfl | succ k ih => rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih,ib,restrict_tick]
   simp only [trim,P.exec,restrict_tick]; apply aux
abbrev finite (p : P Nat) : P (Fin (p.top+1)) := trim _ p (Nat.lt_succ_self _)
theorem finite_exec (p : P Nat) (x) : p.finite.exec x S.init = restrict _ (p.exec x S.init) := trim_exec p x (p.top+1) (Nat.lt_succ_self _) S.init
end P
end Compact.Reg
end

-- WS
section
/- Word streams compiled to the Compact.Reg register machine.
Register macros adapted from the t_7d9f7135 release (OpenAI/openai math,
3344da59991ed94f9ba711217b29c1d760badfa6; see LICENSE.openai). -/
namespace Compact.WS
open Compact.Reg

theorem iterInc (x : List Bool) (r : Nat) (s : S Nat) (n : Nat) : (fun t => ((P.inc r).exec x t).tick 1)^[n] s = ⟨Function.update s.reg r (s.reg r+n),s.words,s.work+2*n⟩ := by
 induction n with
 | zero => simp [Function.update_eq_self]
 | succ n ih => rw [Function.iterate_succ_apply',ih]; simp [P.exec,S.tick,S.put,Function.update_idem,Nat.mul_succ,Nat.add_assoc]

def acc (d r : Nat) : P Nat := .repeatN r (.inc d)
theorem acc_exec (d r : Nat) (x) (s : S Nat) : (acc d r).exec x s = ⟨Function.update s.reg d (s.reg d+s.reg r),s.words,s.work+1+3*s.reg r⟩ := by
 unfold acc; rw [P.exec,iterInc]; simp only [S.tick]; congr 1; omega

def copy (d r : Nat) : P Nat := .seq (.zero d) (acc d r)
theorem copy_exec (x) (s : S Nat) {d r} (h : r ≠ d) : (copy d r).exec x s = ⟨Function.update s.reg d (s.reg r),s.words,s.work+2+s.reg d+3*s.reg r⟩ := by
 simp [copy,P.exec,S.put,acc_exec,Function.update_of_ne h,Function.update_idem]; omega

def minus (d r : Nat) : P Nat := .repeatN r (.dec d)
theorem minus_exec (x) (s : S Nat) (d r : Nat) : (minus d r).exec x s = ⟨Function.update s.reg d (s.reg d - s.reg r),s.words,s.work+1+3*s.reg r⟩ := by
 have aux (t : S Nat) (n : Nat) : (fun u => ((P.dec d).exec x u).tick 1)^[n] t = ⟨Function.update t.reg d (t.reg d-n),t.words,t.work+2*n⟩ := by
   induction n with
   | zero => simp [Function.update_eq_self]
   | succ n ih => rw [Function.iterate_succ_apply',ih]; simp [P.exec,S.tick,S.put,Function.update_idem,Nat.sub_sub,Nat.mul_succ,Nat.add_assoc]
 unfold minus; rw [P.exec,aux]; simp only [S.tick]; congr 1; omega

def madd (d a b : Nat) : P Nat := .repeatN a (acc d b)
theorem madd_exec (x) (s : S Nat) (d a b : Nat) (hb : b ≠ d) : (madd d a b).exec x s = ⟨Function.update s.reg d (s.reg d+s.reg a*s.reg b),s.words,s.work+1+s.reg a+s.reg a*(2+3*s.reg b)⟩ := by
 have aux (t : S Nat) (n : Nat) : (fun u => ((acc d b).exec x u).tick 1)^[n] t = ⟨Function.update t.reg d (t.reg d+n*t.reg b),t.words,t.work+n*(2+3*t.reg b)⟩ := by
   induction n with
   | zero => simp [Function.update_eq_self]
   | succ n ih => rw [Function.iterate_succ_apply',ih,acc_exec]; simp [Function.update_of_ne hb,S.tick,Function.update_idem,Nat.succ_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]; omega
 unfold madd; rw [P.exec,aux]; simp [S.tick,Nat.add_assoc]

def bump (d : Nat) : Nat → P Nat
 | 0 => .zero d | n+1 => .seq (bump d n) (.inc d)
theorem bump_exec (x) (s : S Nat) (d n) : (bump d n).exec x s = ⟨Function.update s.reg d n,s.words,s.work+1+s.reg d+n⟩ := by
 induction n with
 | zero => simp [bump,P.exec,S.put,Nat.add_assoc]
 | succ n ih => simp [bump,P.exec,S.put,ih,Function.update_idem,Nat.add_assoc]

/-- A bounded loop, stated as an invariant over the actual iterates. -/
theorem loop (x : List Bool) (r : Nat) (b : P Nat) (s : S Nat) (I : Nat → S Nat → Prop)
 (h0 : I 0 (s.tick (1+s.reg r))) (hs : ∀ k z, k < s.reg r → I k z → I (k+1) ((b.exec x z).tick 1)) :
 I (s.reg r) ((P.repeatN r b).exec x s) := by
 have h : ∀ k ≤ s.reg r, I k ((fun t => (b.exec x t).tick 1)^[k] (s.tick (1+s.reg r))) := by
   intro k hk
   induction k with
   | zero => exact h0
   | succ k ih => rw [Function.iterate_succ_apply']; exact hs k _ (by omega) (ih (by omega))
 exact h _ le_rfl

inductive Op | add | sub | mul
def Op.eval : Op → Nat → Nat → Nat | .add => Nat.add | .sub => Nat.sub | .mul => Nat.mul
def Op.combine (op : Op) (d : Nat) : P Nat := match op with
 | .add => .seq (copy d (d+1)) (acc d (d+2))
 | .sub => .seq (copy d (d+1)) (minus d (d+2))
 | .mul => .seq (.zero d) (madd d (d+1) (d+2))
theorem combine_spec (op : Op) (d x) (s : S Nat) : let t := (op.combine d).exec x s
 t.reg = Function.update s.reg d (op.eval (s.reg (d+1)) (s.reg (d+2))) ∧ t.words = s.words := by
 cases op <;> simp [Op.combine,Op.eval,P.exec,copy_exec,acc_exec,minus_exec,madd_exec,Function.update_of_ne (show d+2 ≠ d by omega),Function.update_idem,S.put]

/-- Bounded arithmetic over the input bits; `sum n b` binds a new loop index. -/
inductive E : Type → Type 1 where
 | var (a : α) : E α
 | const (n : Nat) : E α
 | len : E α
 | read (i : E α) : E α
 | bin (op : Op) (a b : E α) : E α
 | cond (c y n : E α) : E α
 | sum (n : E α) (b : E (Option α)) : E α

namespace E
def val (x : List Bool) : (α → Nat) → E α → Nat
 | v, .var a => v a
 | _, .const n => n
 | _, .len => x.length
 | v, .read i => if x[val x v i]?.getD false then 1 else 0
 | v, .bin op a b => op.eval (val x v a) (val x v b)
 | v, .cond c a b => if val x v c ≠ 0 then val x v a else val x v b
 | v, .sum n b => ∑ j ∈ Finset.range (val x v n), val x (fun o => o.elim j v) b

def code : (α → Nat) → Nat → E α → P Nat
 | ref, d, .var a => copy d (ref a)
 | _, d, .const n => bump d n
 | _, d, .len => .len d
 | ref, d, .read i => .seq (code ref d i) (.read d d)
 | ref, d, .bin op a b => .seq (code ref (d+1) a) (.seq (code ref (d+2) b) (op.combine d))
 | ref, d, .cond c y n => .seq (code ref d c) (.branch d (code ref d y) (code ref d n))
 | ref, d, .sum n b => .seq (code ref (d+1) n) (.seq (.zero d) (.seq (.zero (d+2))
     (.repeatN (d+1) (.seq (code (fun o => o.elim (d+2) ref) (d+3) b) (.seq (acc d (d+3)) (.inc (d+2)))))))

def At (x : List Bool) (ref : α → Nat) (d : Nat) (e : E α) (s t : S Nat) :=
 t.reg d = e.val x (s.reg ∘ ref) ∧ (∀ j < d, t.reg j = s.reg j) ∧ t.words = s.words

theorem envEq {ref : α → Nat} {s t : S Nat} {d : Nat} (hr : ∀ a, ref a < d) (hf : ∀ j < d, t.reg j = s.reg j) : t.reg ∘ ref = s.reg ∘ ref := funext fun a => hf _ (hr a)

theorem code_spec (e : E α) (x : List Bool) (ref : α → Nat) (d) (hr : ∀ a, ref a < d) (s : S Nat) : At x ref d e s ((code ref d e).exec x s) := by
 induction e generalizing d s with
 | var a => simp [At,code,copy_exec x s (Nat.ne_of_lt (hr a)),val,Function.comp_def]; intro j h; exact Function.update_of_ne (by omega) ..
 | const n => simp [At,code,bump_exec,val]; intro j h; exact Function.update_of_ne (by omega) ..
 | len => simp [At,code,P.exec,S.put,val]; intro j h; exact Function.update_of_ne (by omega) ..
 | read i ih =>
   obtain ⟨he,hf,hw⟩ := ih ref d hr s; simp [At,code,P.exec,S.put,val,he,hw]; intro j h; rw [Function.update_of_ne (by omega : j ≠ d),hf _ h]
 | bin op a b ia ib =>
   let t := (code ref (d+1) a).exec x s
   let u := (code ref (d+2) b).exec x t
   have ha := ia ref (d+1) (fun j => by have := hr j; omega) s
   have hb := ib ref (d+2) (fun j => by have := hr j; omega) t
   obtain ⟨h,w⟩ := combine_spec op d x u
   change At x ref d _ s ((op.combine d).exec x u)
   refine ⟨?_,?_,?_⟩
   · rw [h,Function.update_self,hb.2.1 (d+1) (by omega),ha.1,hb.1,envEq (d:=d+1) (fun j => by have := hr j; omega) ha.2.1]; rfl
   · intro j hj; rw [h,Function.update_of_ne (by omega : j ≠ d),hb.2.1 _ (by omega),ha.2.1 _ (by omega)]
   · rw [w,hb.2.2,ha.2.2]
 | cond c y n ic iy ineg =>
   let t := (code ref d c).exec x s
   obtain ⟨he,hf,hw⟩ : At x ref d c s t := ic ref d hr s
   have hy := iy ref d hr (t.tick 1); have hn := ineg ref d hr (t.tick 1)
   change At x ref d _ s (if t.reg d ≠ 0 then _ else _)
   split <;> rename_i h
   · simpa [At,val,← he,h,S.tick,envEq hr hf] using (show _ from And.intro hy.1 (And.intro (fun j hj => (hy.2.1 j hj).trans (hf j hj)) (hy.2.2.trans hw)))
   · simpa [At,val,← he,h,S.tick,envEq hr hf] using (show _ from And.intro hn.1 (And.intro (fun j hj => (hn.2.1 j hj).trans (hf j hj)) (hn.2.2.trans hw)))
 | sum n b ihn ihb =>
   let t := (code ref (d+1) n).exec x s
   have hn : At x ref (d+1) n s t := ihn ref (d+1) (fun j => by have := hr j; omega) s
   let u := ((P.zero (d+2)).exec x ((P.zero d).exec x t))
   let ρ := fun o : Option _ => o.elim (d+2) ref
   have hρ (o) : ρ o < d+3 := by cases o <;> simp [ρ] <;> first | omega | (have := hr ‹_›; omega)
   let f := fun j => b.val x (fun o => o.elim j (s.reg ∘ ref))
   let I := fun k (z : S Nat) => z.reg d = ∑ j ∈ Finset.range k, f j ∧ z.reg (d+2) = k ∧ (∀ j < d, z.reg j = s.reg j) ∧ z.words = s.words
   have hu (j) (hj : j < d) : u.reg j = s.reg j := by
     simp [u,P.exec,S.put,Function.update_of_ne (by omega : j ≠ d+2),Function.update_of_ne (by omega : j ≠ d),hn.2.1 j (by omega)]
   have cnt : u.reg (d+1) = n.val x (s.reg ∘ ref) := by simp [u,P.exec,S.put,hn.1]
   have main := loop x (d+1) (.seq (code ρ (d+3) b) (.seq (acc d (d+3)) (.inc (d+2)))) u I (by
       refine ⟨by simp [u,P.exec,S.put,S.tick],by simp [u,P.exec,S.put,S.tick],fun j hj => by simpa [S.tick] using hu j hj,by simp [u,P.exec,S.put,S.tick,hn.2.2]⟩)
     (by
       intro k z _ ⟨hz0,hz2,hzf,hzw⟩
       let v := (code ρ (d+3) b).exec x z
       have hb := ihb ρ (d+3) hρ z
       unfold At at hb
       have env : z.reg ∘ ρ = fun o => o.elim k (s.reg ∘ ref) := by
         funext o; cases o with
         | none => exact hz2
         | some a => exact hzf _ (hr a)
       rw [env] at hb
       simp only [P.exec,acc_exec,S.put,S.tick]
       refine ⟨?_,?_,?_,?_⟩
       · simp [Function.update_of_ne (by omega : d ≠ d+2),hb.2.1 d (by omega),hz0,hb.1,Finset.sum_range_succ,f,v]
       · simp [hb.2.1 (d+2) (by omega),hz2,Function.update_of_ne (by omega : d+2 ≠ d)]
       · intro j hj; simp [Function.update_of_ne (by omega : j ≠ d+2),Function.update_of_ne (by omega : j ≠ d),hb.2.1 j (by omega),hzf j hj]
       · simp [hb.2.2,hzw])
   rw [cnt] at main
   exact ⟨main.1,main.2.2.1,main.2.2.2⟩
end E

/-- Streams of words: ranges bind a new index, guards test nonzero values. -/
inductive W : Type → Type 1 where
 | nil : W α
 | word (e : E α) : W α
 | cat (a b : W α) : W α
 | range (n : E α) (b : W (Option α)) : W α
 | guard (c : E α) (y n : W α) : W α

namespace W
def eval (x : List Bool) : (α → Nat) → W α → List Nat
 | _, .nil => []
 | v, .word e => [e.val x v]
 | v, .cat a b => eval x v a ++ eval x v b
 | v, .range n b => (List.range (n.val x v)).flatMap fun j => eval x (fun o => o.elim j v) b
 | v, .guard c y n => if c.val x v ≠ 0 then eval x v y else eval x v n

def code : (α → Nat) → Nat → W α → P Nat
 | _, d, .nil => .zero d
 | ref, d, .word e => .seq (e.code ref d) (.emit d)
 | ref, d, .cat a b => .seq (code ref d a) (code ref d b)
 | ref, d, .range n b => .seq (n.code ref d) (.seq (.zero (d+1)) (.repeatN d (.seq (code (fun o => o.elim (d+1) ref) (d+2) b) (.inc (d+1)))))
 | ref, d, .guard c y n => .seq (c.code ref d) (.branch d (code ref d y) (code ref d n))

def At (x : List Bool) (ref : α → Nat) (d : Nat) (w : W α) (s t : S Nat) :=
 t.words = s.words ++ w.eval x (s.reg ∘ ref) ∧ ∀ j < d, t.reg j = s.reg j

theorem code_spec (w : W α) (x : List Bool) (ref : α → Nat) (d) (hr : ∀ a, ref a < d) (s : S Nat) : At x ref d w s ((code ref d w).exec x s) := by
 induction w generalizing d s with
 | nil => simp [At,code,eval,P.exec,S.put]; intro j h; exact Function.update_of_ne (by omega) ..
 | word e =>
   have h := E.code_spec e x ref d hr s
   simp [At,code,eval,P.exec,h.2.2,h.1]; exact h.2.1
 | cat a b ia ib =>
   have ha := ia ref d hr s; have hb := ib ref d hr ((code ref d a).exec x s)
   unfold At at ha hb
   rw [E.envEq hr ha.2] at hb
   exact ⟨by simp [code,P.exec,eval,hb.1,ha.1],fun j hj => (hb.2 j hj).trans (ha.2 j hj)⟩
 | guard c y n iy ineg =>
   let t := (c.code ref d).exec x s
   obtain ⟨he,hf,hw⟩ := E.code_spec c x ref d hr s
   have hy := iy ref d hr (t.tick 1); have hn := ineg ref d hr (t.tick 1)
   change At x ref d _ s (if t.reg d ≠ 0 then _ else _)
   have ev : (t.tick 1).reg ∘ ref = s.reg ∘ ref := E.envEq hr hf
   unfold At at hy hn
   rw [ev] at hy hn
   split <;> rename_i h <;> rw [he] at h
   · exact ⟨by rw [hy.1]; simp [eval,h,S.tick]; exact hw,fun j hj => (hy.2 j hj).trans (hf j hj)⟩
   · exact ⟨by rw [hn.1]; simp [eval,h,S.tick]; exact hw,fun j hj => (hn.2 j hj).trans (hf j hj)⟩
 | range n b ib =>
   let t := (n.code ref d).exec x s
   have hn : E.At x ref d n s t := E.code_spec n x ref d hr s
   let u := (P.zero (d+1)).exec x t
   let ρ := fun o : Option _ => o.elim (d+1) ref
   have hρ (o) : ρ o < d+2 := by cases o <;> simp [ρ] <;> first | omega | (have := hr ‹_›; omega)
   let f := fun j => b.eval x (fun o => o.elim j (s.reg ∘ ref))
   let I := fun k (z : S Nat) => z.words = s.words ++ (List.range k).flatMap f ∧ z.reg (d+1) = k ∧ ∀ j < d, z.reg j = s.reg j
   have hu (j) (hj : j < d) : u.reg j = s.reg j := by simp [u,P.exec,S.put,Function.update_of_ne (by omega : j ≠ d+1),hn.2.1 j hj]
   have cnt : u.reg d = n.val x (s.reg ∘ ref) := by simp [u,P.exec,S.put,hn.1]
   have main := loop x d (.seq (code ρ (d+2) b) (.inc (d+1))) u I
     ⟨by simp [u,P.exec,S.put,S.tick,hn.2.2],by simp [u,P.exec,S.put,S.tick],fun j hj => by simpa [S.tick] using hu j hj⟩
     (by
       intro k z _ ⟨hzw,hz1,hzf⟩
       have hb := ib ρ (d+2) hρ z
       unfold At at hb
       have env : z.reg ∘ ρ = fun o => o.elim k (s.reg ∘ ref) := by
         funext o; cases o with
         | none => exact hz1
         | some a => exact hzf _ (hr a)
       rw [env] at hb
       simp only [P.exec,S.put,S.tick]
       refine ⟨?_,?_,?_⟩
       · simp [hb.1,hzw,List.range_succ,f]
       · simp [hb.2 (d+1) (by omega),hz1]
       · intro j hj; simp [Function.update_of_ne (by omega : j ≠ d+1),hb.2 j (by omega),hzf j hj])
   rw [cnt] at main
   exact ⟨main.1,main.2.2⟩
end W
end Compact.WS
end

-- WSBound
section
/- Polynomial work bounds for word-stream programs. -/
namespace Compact.WS
open Compact.Reg Polynomial
abbrev Poly := Polynomial Nat
theorem mono (p : Poly) {i j : Nat} (h : i ≤ j) : p.eval i ≤ p.eval j := by
 induction p using Polynomial.induction_on' with
 | add _ _ ha hb => simpa using Nat.add_le_add ha hb
 | monomial n c => simp only [Polynomial.eval_monomial]; gcongr

/-- Two tiers: environment values stay below `a`, scratch below `m`. Values
written are bounded by `p a`; work grows by at most `p (a+m)`. -/
def ELim (e : E α) (p : Poly) : Prop := ∀ x ref d (s : S Nat) a m, (∀ j, ref j < d) → x.length ≤ a →
 (∀ j, s.reg (ref j) ≤ a) → (∀ j, s.reg j ≤ m) →
 e.val x (s.reg ∘ ref) ≤ p.eval a ∧ (∀ j, ((e.code ref d).exec x s).reg j ≤ max m (p.eval a)) ∧
 ((e.code ref d).exec x s).work ≤ s.work + p.eval (a+m)

def WLim (w : W α) (p : Poly) : Prop := ∀ x ref d (s : S Nat) a m, (∀ j, ref j < d) → x.length ≤ a →
 (∀ j, s.reg (ref j) ≤ a) → (∀ j, s.reg j ≤ m) →
 (∀ j, ((w.code ref d).exec x s).reg j ≤ max m (p.eval a)) ∧ ((w.code ref d).exec x s).work ≤ s.work + p.eval (a+m)

theorem combine_work (op : Op) (d x) (u : S Nat) : ((op.combine d).exec x u).work ≤ u.work + 3 + u.reg d + 3*u.reg (d+1) + 3*u.reg (d+2) + 3*(u.reg (d+1)*u.reg (d+2)) := by
 cases op <;> simp [Op.combine,P.exec,copy_exec,acc_exec,minus_exec,madd_exec,S.put,Function.update_of_ne (show d+1 ≠ d by omega),Function.update_of_ne (show d+2 ≠ d by omega)] <;> nlinarith

theorem upd_le {f : Nat → Nat} {M v : Nat} (h : ∀ j, f j ≤ M) (hv : v ≤ M) (d j : Nat) : Function.update f d v j ≤ M := by
 by_cases e : j = d
 · subst e; simpa using hv
 · rw [Function.update_of_ne e]; exact h j

theorem op_le (op : Op) {u v U V : Nat} (hu : u ≤ U) (hv : v ≤ V) : op.eval u v ≤ U + V + U*V := by
 have := Nat.mul_le_mul hu hv
 cases op <;> simp only [Op.eval,Nat.add_eq,Nat.sub_eq,Nat.mul_eq] <;> omega

theorem sum_step (x) (v : S Nat) (d : Nat) :
  (((P.seq (acc d (d+3)) (.inc (d+2))).exec x v).tick 1).reg d = v.reg d + v.reg (d+3) ∧
  (((P.seq (acc d (d+3)) (.inc (d+2))).exec x v).tick 1).reg (d+2) = v.reg (d+2) + 1 ∧
  (∀ j, j ≠ d → j ≠ d+2 → (((P.seq (acc d (d+3)) (.inc (d+2))).exec x v).tick 1).reg j = v.reg j) ∧
  (((P.seq (acc d (d+3)) (.inc (d+2))).exec x v).tick 1).work = v.work + 3 + 3*v.reg (d+3) := by
 simp only [P.exec, acc_exec, S.put, S.tick]
 refine ⟨?_,?_,fun j h1 h2 => ?_,?_⟩
 · rw [Function.update_of_ne (by omega : d ≠ d+2), Function.update_self]
 · rw [Function.update_self, Function.update_of_ne (by omega : d+2 ≠ d)]
 · rw [Function.update_of_ne h2, Function.update_of_ne h1]
 · omega

theorem zero2 (x) (t : S Nat) (d : Nat) :
  (∀ j, ((P.zero (d+2)).exec x ((P.zero d).exec x t)).reg j = if j = d ∨ j = d+2 then 0 else t.reg j) ∧
  ((P.zero (d+2)).exec x ((P.zero d).exec x t)).work = t.work + 2 + t.reg d + t.reg (d+2) := by
 simp only [P.exec, S.put]
 refine ⟨fun j => ?_,?_⟩
 · simp only [Function.update_apply]; split_ifs <;> first | rfl | omega
 · rw [Function.update_of_ne (by omega : d+2 ≠ d)]; omega

noncomputable def sumK (pn pb : Poly) : Poly := pn + pn*pb.comp (X+pn) + pb.comp (X+pn)
noncomputable def sumP (pn pb : Poly) : Poly := 3+2*X+4*pn+sumK pn pb+pn*(pb.comp (X+pn+sumK pn pb)+3*pb.comp (X+pn)+3)
noncomputable def rangeK (pn pb : Poly) : Poly := pn + pb.comp (X+pn)
noncomputable def rangeP (pn pb : Poly) : Poly := 3+2*X+4*pn+rangeK pn pb+pn*(pb.comp (X+pn+rangeK pn pb)+2)

theorem E.bound (e : E α) : ∃ p, ELim e p := by
 induction e with
 | var c =>
   refine ⟨3+3*X,fun x ref d s a m hr hl hv hm => ?_⟩
   simp only [E.code,copy_exec x s (Nat.ne_of_lt (hr c)),E.val,Function.comp_apply]
   have := hv c; have := hm d; have := hm (ref c)
   simp only [eval_add,eval_mul,eval_X,eval_ofNat]
   exact ⟨by omega,upd_le (fun j => (hm j).trans (le_max_left _ _)) (by omega) _,by omega⟩
 | const n =>
   refine ⟨C (n+1)+X,fun x ref d s a m hr hl hv hm => ?_⟩
   simp only [E.code,bump_exec,E.val,eval_add,eval_C,eval_X]
   have := hm d
   exact ⟨by omega,upd_le (fun j => (hm j).trans (le_max_left _ _)) (by omega) _,by omega⟩
 | len =>
   refine ⟨1+X,fun x ref d s a m hr hl hv hm => ?_⟩
   simp only [E.code,P.exec,S.put,E.val,eval_add,eval_one,eval_X]
   have := hm d
   exact ⟨by omega,upd_le (fun j => (hm j).trans (le_max_left _ _)) (by omega) _,by omega⟩
 | read i ih =>
   obtain ⟨p,hp⟩ := ih
   refine ⟨1+X+3*p,fun x ref d s a m hr hl hv hm => ?_⟩
   obtain ⟨v,r,w⟩ := hp x ref d s a m hr hl hv hm
   have sp := E.code_spec i x ref d hr s
   have mp := mono p (show a ≤ a+m by omega)
   simp only [E.code,P.exec,S.put,E.val,eval_add,eval_one,eval_X,eval_mul,eval_ofNat] at *
   refine ⟨by split <;> omega,upd_le (fun j => (r j).trans (by omega)) (by split <;> omega) _,?_⟩
   rw [sp.1]; omega
 | bin op l r il ir =>
   obtain ⟨pl,hl'⟩ := il; obtain ⟨pr,hr'⟩ := ir
   refine ⟨3+X+4*pl+4*pr+3*(pl*pr)+pr.comp (X+pl)+pl,fun x ref d s a m hr hl hv hm => ?_⟩
   have hd1 j : ref j < d+1 := by have := hr j; omega
   have hd2 j : ref j < d+2 := by have := hr j; omega
   obtain ⟨vl,rl,wl⟩ := hl' x ref (d+1) s a m hd1 hl hv hm
   have sl := E.code_spec l x ref (d+1) hd1 s
   unfold E.At at sl
   have hvt j : ((l.code ref (d+1)).exec x s).reg (ref j) ≤ a := by rw [sl.2.1 _ (hd1 j)]; exact hv j
   obtain ⟨vr,rr,wr⟩ := hr' x ref (d+2) _ a (max m (pl.eval a)) hd2 hl hvt rl
   have sr := E.code_spec r x ref (d+2) hd2 ((l.code ref (d+1)).exec x s)
   unfold E.At at sr
   rw [E.envEq hd1 sl.2.1] at vr sr
   have cw := combine_work op d x ((r.code ref (d+2)).exec x ((l.code ref (d+1)).exec x s))
   have cs := combine_spec op d x ((r.code ref (d+2)).exec x ((l.code ref (d+1)).exec x s))
   have u1 := (sr.2.1 (d+1) (by omega)).trans sl.1
   have vb := op_le op vl vr
   have e : (E.code ref d (E.bin op l r)).exec x s = (op.combine d).exec x ((r.code ref (d+2)).exec x ((l.code ref (d+1)).exec x s)) := rfl
   have ev : (E.bin op l r).val x (s.reg ∘ ref) = op.eval (l.val x (s.reg ∘ ref)) (r.val x (s.reg ∘ ref)) := rfl
   rw [e, cs.1, ev]
   generalize (r.code ref (d+2)).exec x ((l.code ref (d+1)).exec x s) = u at *
   generalize (l.code ref (d+1)).exec x s = t at *
   rw [u1, sr.1] at cw ⊢
   have mpl := mono pl (show a ≤ a+m by omega); have mpr := mono pr (show a ≤ a+m by omega)
   have mc := mono pr (show a + max m (pl.eval a) ≤ (a+m) + pl.eval (a+m) by omega)
   have prod := Nat.mul_le_mul (vl.trans mpl) (vr.trans mpr)
   have ud := rr d
   simp only [eval_add,eval_mul,eval_X,eval_ofNat,eval_comp]
   refine ⟨by omega,upd_le (fun j => (rr j).trans (by omega)) (by omega) _,by omega⟩
 | cond c y n ic iy ineg =>
   obtain ⟨pc,hc⟩ := ic; obtain ⟨py,hy⟩ := iy; obtain ⟨pn,hn⟩ := ineg
   refine ⟨1+pc+py+pn+(py+pn).comp (X+pc),fun x ref d s a m hr hl hv hm => ?_⟩
   obtain ⟨vc,rc,wc⟩ := hc x ref d s a m hr hl hv hm
   have sc := E.code_spec c x ref d hr s
   unfold E.At at sc
   have env : (((c.code ref d).exec x s).tick 1).reg ∘ ref = s.reg ∘ ref := E.envEq hr sc.2.1
   have hvt j : (((c.code ref d).exec x s).tick 1).reg (ref j) ≤ a := by simp only [S.tick]; rw [sc.2.1 _ (hr j)]; exact hv j
   have mpc := mono pc (show a ≤ a+m by omega)
   have key (b : E _) (pb : Poly) (hb : ELim b pb) (lb : ∀ z, pb.eval z ≤ py.eval z + pn.eval z) :
       b.val x (s.reg ∘ ref) ≤ (1+pc+py+pn+(py+pn).comp (X+pc)).eval a ∧
       (∀ j, ((b.code ref d).exec x (((c.code ref d).exec x s).tick 1)).reg j ≤ max m ((1+pc+py+pn+(py+pn).comp (X+pc)).eval a)) ∧
       ((b.code ref d).exec x (((c.code ref d).exec x s).tick 1)).work ≤ s.work + (1+pc+py+pn+(py+pn).comp (X+pc)).eval (a+m) := by
     obtain ⟨vb,rb,wb⟩ := hb x ref d _ a (max m (pc.eval a)) hr hl hvt (by simpa [S.tick] using rc)
     rw [env] at vb
     have m1 := mono py (show a + max m (pc.eval a) ≤ (a+m) + pc.eval (a+m) by omega)
     have m2 := mono pn (show a + max m (pc.eval a) ≤ (a+m) + pc.eval (a+m) by omega)
     have l1 := lb a; have l2 := lb (a + max m (pc.eval a))
     have tw : (((c.code ref d).exec x s).tick 1).work = ((c.code ref d).exec x s).work + 1 := rfl
     simp only [eval_add,eval_one,eval_comp,eval_X]
     exact ⟨by omega, fun j => (rb j).trans (by omega), by omega⟩
   have e : (E.code ref d (E.cond c y n)).exec x s = if ((c.code ref d).exec x s).reg d ≠ 0 then (y.code ref d).exec x (((c.code ref d).exec x s).tick 1) else (n.code ref d).exec x (((c.code ref d).exec x s).tick 1) := rfl
   have ev : (E.cond c y n).val x (s.reg ∘ ref) = if c.val x (s.reg ∘ ref) ≠ 0 then y.val x (s.reg ∘ ref) else n.val x (s.reg ∘ ref) := rfl
   rw [e, ev, ← sc.1]
   split
   · exact key y py hy (fun z => by omega)
   · exact key n pn hn (fun z => by omega)
 | sum n b ihn ihb =>
   obtain ⟨pn,hn⟩ := ihn; obtain ⟨pb,hb⟩ := ihb
   refine ⟨sumP pn pb,fun x ref d s a m hr hl hv hm => ?_⟩
   have hd1 j : ref j < d+1 := by have := hr j; omega
   obtain ⟨vn,rn,wn⟩ := hn x ref (d+1) s a m hd1 hl hv hm
   have sn := E.code_spec n x ref (d+1) hd1 s
   unfold E.At at sn
   have At := E.code_spec (E.sum n b) x ref d hr s
   unfold E.At at At
   have e : (E.code ref d (E.sum n b)).exec x s = (P.repeatN (d+1) (.seq (E.code (fun o => o.elim (d+2) ref) (d+3) b) (.seq (acc d (d+3)) (.inc (d+2))))).exec x ((P.zero (d+2)).exec x ((P.zero d).exec x ((n.code ref (d+1)).exec x s))) := rfl
   rw [e] at At ⊢
   rw [← At.1]
   obtain ⟨ureg,uwork⟩ := zero2 x ((n.code ref (d+1)).exec x s) d
   generalize (P.zero (d+2)).exec x ((P.zero d).exec x ((n.code ref (d+1)).exec x s)) = u at *
   generalize (n.code ref (d+1)).exec x s = t at *
   obtain ⟨N,hN⟩ : ∃ N, N = n.val x (s.reg ∘ ref) := ⟨_,rfl⟩
   rw [← hN] at vn sn
   obtain ⟨B,hB⟩ : ∃ B, B = pb.eval (a + pn.eval a) := ⟨_,rfl⟩
   obtain ⟨M,hM⟩ : ∃ M, M = max m (pn.eval a + pn.eval a * B + B) := ⟨_,rfl⟩
   obtain ⟨c,hc⟩ : ∃ c, c = pb.eval (a + pn.eval a + M) + 3*B + 3 := ⟨_,rfl⟩
   have cnt : u.reg (d+1) = N := by rw [ureg]; simp; exact sn.1
   have hu j (hj : j < d) : u.reg j = s.reg j := by rw [ureg, if_neg (by omega)]; exact sn.2.1 j (by omega)
   have pB : pn.eval a * B ≤ pn.eval a * B := le_rfl
   have ur j : u.reg j ≤ M := by
     rw [ureg]; split_ifs
     · omega
     · have := rn j; omega
   have hρ (o : Option _) : (fun o => o.elim (d+2) ref) o < d+3 := by cases o <;> simp <;> first | omega | (have := hr ‹_›; omega)
   have main := loop x (d+1) (.seq (E.code (fun o => o.elim (d+2) ref) (d+3) b) (.seq (acc d (d+3)) (.inc (d+2)))) u
     (fun k z => z.reg d ≤ k*B ∧ z.reg (d+2) = k ∧ (∀ j < d, z.reg j = s.reg j) ∧ (∀ j, z.reg j ≤ M) ∧ z.work ≤ u.work + (1+N) + k*c)
     ⟨by simp [S.tick,ureg],by simp [S.tick,ureg],fun j hj => by simpa [S.tick] using hu j hj,fun j => by simpa [S.tick] using ur j,by simp [S.tick,cnt]⟩
     (by
       intro k z hk ⟨hz0,hz2,hzf,hzr,hzw⟩
       rw [cnt] at hk
       have env (o : Option _) : z.reg ((fun o => o.elim (d+2) ref) o) ≤ a + pn.eval a := by
         cases o with
         | none => simp only [Option.elim]; omega
         | some j => simp only [Option.elim]; rw [hzf _ (hr j)]; have := hv j; omega
       obtain ⟨vb,rb,wb⟩ := hb x _ (d+3) z (a + pn.eval a) M hρ (by omega) env hzr
       have sb := E.code_spec b x _ (d+3) hρ z
       unfold E.At at sb
       obtain ⟨q1,q2,q3,q4⟩ := sum_step x ((E.code (fun o => o.elim (d+2) ref) (d+3) b).exec x z) d
       beta_reduce
       have hz' : (P.exec x (.seq (E.code (fun o => o.elim (d+2) ref) (d+3) b) (.seq (acc d (d+3)) (.inc (d+2)))) z).tick 1 = ((P.seq (acc d (d+3)) (.inc (d+2))).exec x ((E.code (fun o => o.elim (d+2) ref) (d+3) b).exec x z)).tick 1 := rfl
       rw [hz']
       generalize ((P.seq (acc d (d+3)) (.inc (d+2))).exec x ((E.code (fun o => o.elim (d+2) ref) (d+3) b).exec x z)).tick 1 = z' at *
       generalize (E.code (fun o => o.elim (d+2) ref) (d+3) b).exec x z = v at *
       have v3 : v.reg (d+3) ≤ B := by rw [sb.1, hB]; exact vb
       have v0 : v.reg d = z.reg d := sb.2.1 d (by omega)
       have v2 : v.reg (d+2) = z.reg (d+2) := sb.2.1 (d+2) (by omega)
       have kB : (k+1)*B ≤ pn.eval a * B := Nat.mul_le_mul_right _ (by omega)
       have kB' : (k+1)*B = k*B + B := Nat.succ_mul k B
       have kc : (k+1)*c = k*c + c := Nat.succ_mul k c
       have mb := mono pb (show a + pn.eval a + M ≤ a + pn.eval a + M from le_rfl)
       refine ⟨by omega,by omega,fun j hj => ?_,fun j => ?_,?_⟩
       · rw [q3 j (by omega) (by omega), sb.2.1 j (by omega)]; exact hzf j hj
       · by_cases h0 : j = d
         · subst h0; omega
         · by_cases h2 : j = d+2
           · subst h2; omega
           · rw [q3 j h0 h2]; have := rb j; omega
       · rw [q4]; have := Nat.mul_le_mul_left 3 v3; rw [kc, hc]; rw [hc] at hzw; omega)
   obtain ⟨m0,_,_,mr,mw⟩ := main
   rw [cnt] at m0 mw
   have mn := mono pn (show a ≤ a+m by omega)
   have mA := mono pb (show a + pn.eval a ≤ (a+m) + pn.eval (a+m) by omega)
   have mK : pn.eval a + pn.eval a * B + B ≤ (sumK pn pb).eval (a+m) := by
     have := Nat.mul_le_mul mn mA
     simp only [sumK,eval_add,eval_mul,eval_comp,eval_X]; rw [hB]; omega
   have mG := mono pb (show a + pn.eval a + M ≤ (a+m) + pn.eval (a+m) + (sumK pn pb).eval (a+m) by omega)
   have cN := Nat.mul_le_mul (vn.trans mn) (show c ≤ pb.eval ((a+m) + pn.eval (a+m) + (sumK pn pb).eval (a+m)) + 3*pb.eval ((a+m) + pn.eval (a+m)) + 3 by omega)
   have NB := Nat.mul_le_mul_right B vn
   have t0 := rn d; have t2 := rn (d+2)
   have kA : (sumK pn pb).eval a = pn.eval a + pn.eval a * B + B := by simp [sumK, hB]
   have mS := mono (sumK pn pb) (show a ≤ a+m by omega)
   simp only [sumP,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat] at cN ⊢
   refine ⟨by omega,fun j => (mr j).trans (by omega),by omega⟩


theorem W.bound (w : W α) : ∃ p, WLim w p := by
 induction w with
 | nil =>
   refine ⟨1+X,fun x ref d s a m hr hl hv hm => ?_⟩
   simp only [W.code,P.exec,S.put,eval_add,eval_one,eval_X]; have := hm d
   exact ⟨upd_le (fun j => (hm j).trans (le_max_left _ _)) (by omega) _,by omega⟩
 | word e =>
   obtain ⟨p,hp⟩ := E.bound e
   refine ⟨1+2*p,fun x ref d s a m hr hl hv hm => ?_⟩
   obtain ⟨v,r,w⟩ := hp x ref d s a m hr hl hv hm
   have sp := E.code_spec e x ref d hr s
   unfold E.At at sp
   have mp := mono p (show a ≤ a+m by omega)
   have e1 : (W.code ref d (W.word e)).exec x s = ⟨((e.code ref d).exec x s).reg,((e.code ref d).exec x s).words++[((e.code ref d).exec x s).reg d],((e.code ref d).exec x s).work+(1+((e.code ref d).exec x s).reg d)⟩ := rfl
   rw [e1]; simp only [eval_add,eval_one,eval_mul,eval_ofNat]
   rw [sp.1]
   exact ⟨fun j => (r j).trans (by omega),by omega⟩
 | cat a b ia ib =>
   obtain ⟨pa,ha⟩ := ia; obtain ⟨pb,hb⟩ := ib
   refine ⟨pa+pb+pb.comp (X+pa),fun x ref d s a' m hr hl hv hm => ?_⟩
   obtain ⟨r1,w1⟩ := ha x ref d s a' m hr hl hv hm
   have s1 := W.code_spec a x ref d hr s
   unfold W.At at s1
   have env j : ((W.code ref d a).exec x s).reg (ref j) ≤ a' := by rw [s1.2 _ (hr j)]; exact hv j
   obtain ⟨r2,w2⟩ := hb x ref d _ a' _ hr hl env r1
   have mpa := mono pa (show a' ≤ a'+m by omega)
   have mc := mono pb (show a' + max m (pa.eval a') ≤ (a'+m) + pa.eval (a'+m) by omega)
   have e1 : (W.code ref d (W.cat a b)).exec x s = (W.code ref d b).exec x ((W.code ref d a).exec x s) := rfl
   rw [e1]; simp only [eval_add,eval_comp,eval_X]
   exact ⟨fun j => (r2 j).trans (by omega),by omega⟩
 | guard c y n iy ineg =>
   obtain ⟨pc,hc⟩ := E.bound c; obtain ⟨py,hy⟩ := iy; obtain ⟨pn,hn⟩ := ineg
   refine ⟨1+pc+py+pn+(py+pn).comp (X+pc),fun x ref d s a m hr hl hv hm => ?_⟩
   obtain ⟨vc,rc,wc⟩ := hc x ref d s a m hr hl hv hm
   have sc := E.code_spec c x ref d hr s
   unfold E.At at sc
   have hvt j : (((c.code ref d).exec x s).tick 1).reg (ref j) ≤ a := by simp only [S.tick]; rw [sc.2.1 _ (hr j)]; exact hv j
   have mpc := mono pc (show a ≤ a+m by omega)
   have key (b : W _) (pb : Poly) (hb : WLim b pb) (lb : ∀ z, pb.eval z ≤ py.eval z + pn.eval z) :
       (∀ j, ((b.code ref d).exec x (((c.code ref d).exec x s).tick 1)).reg j ≤ max m ((1+pc+py+pn+(py+pn).comp (X+pc)).eval a)) ∧
       ((b.code ref d).exec x (((c.code ref d).exec x s).tick 1)).work ≤ s.work + (1+pc+py+pn+(py+pn).comp (X+pc)).eval (a+m) := by
     obtain ⟨rb,wb⟩ := hb x ref d _ a (max m (pc.eval a)) hr hl hvt (by simpa [S.tick] using rc)
     have m1 := mono py (show a + max m (pc.eval a) ≤ (a+m) + pc.eval (a+m) by omega)
     have m2 := mono pn (show a + max m (pc.eval a) ≤ (a+m) + pc.eval (a+m) by omega)
     have l1 := lb a; have l2 := lb (a + max m (pc.eval a))
     have tw : (((c.code ref d).exec x s).tick 1).work = ((c.code ref d).exec x s).work + 1 := rfl
     simp only [eval_add,eval_one,eval_comp,eval_X]
     exact ⟨fun j => (rb j).trans (by omega), by omega⟩
   have e : (W.code ref d (W.guard c y n)).exec x s = if ((c.code ref d).exec x s).reg d ≠ 0 then (y.code ref d).exec x (((c.code ref d).exec x s).tick 1) else (n.code ref d).exec x (((c.code ref d).exec x s).tick 1) := rfl
   rw [e]
   split
   · exact key y py hy (fun z => by omega)
   · exact key n pn hn (fun z => by omega)
 | range n b ib =>
   obtain ⟨pn,hn⟩ := E.bound n; obtain ⟨pb,hb⟩ := ib
   refine ⟨rangeP pn pb,fun x ref d s a m hr hl hv hm => ?_⟩
   obtain ⟨vn,rn,wn⟩ := hn x ref d s a m hr hl hv hm
   have sn := E.code_spec n x ref d hr s
   unfold E.At at sn
   have e : (W.code ref d (W.range n b)).exec x s = (P.repeatN d (.seq (W.code (fun o => o.elim (d+1) ref) (d+2) b) (.inc (d+1)))).exec x ((P.zero (d+1)).exec x ((n.code ref d).exec x s)) := rfl
   rw [e]
   have ureg j : ((P.zero (d+1)).exec x ((n.code ref d).exec x s)).reg j = if j = d+1 then 0 else ((n.code ref d).exec x s).reg j := by
     simp only [P.exec,S.put,Function.update_apply]
   have uwork : ((P.zero (d+1)).exec x ((n.code ref d).exec x s)).work = ((n.code ref d).exec x s).work + 1 + ((n.code ref d).exec x s).reg (d+1) := by
     simp only [P.exec,S.put]; omega
   generalize (P.zero (d+1)).exec x ((n.code ref d).exec x s) = u at *
   generalize (n.code ref d).exec x s = t at *
   obtain ⟨N,hN⟩ : ∃ N, N = n.val x (s.reg ∘ ref) := ⟨_,rfl⟩
   rw [← hN] at vn sn
   obtain ⟨B,hB⟩ : ∃ B, B = pb.eval (a + pn.eval a) := ⟨_,rfl⟩
   obtain ⟨M,hM⟩ : ∃ M, M = max m (pn.eval a + B) := ⟨_,rfl⟩
   obtain ⟨c,hc⟩ : ∃ c, c = pb.eval (a + pn.eval a + M) + 2 := ⟨_,rfl⟩
   have cnt : u.reg d = N := by rw [ureg, if_neg (by omega)]; exact sn.1
   have hu j (hj : j < d) : u.reg j = s.reg j := by rw [ureg, if_neg (by omega)]; exact sn.2.1 j hj
   have ur j : u.reg j ≤ M := by
     rw [ureg]; split_ifs
     · omega
     · have := rn j; omega
   have hρ (o : Option _) : (fun o => o.elim (d+1) ref) o < d+2 := by cases o <;> simp <;> first | omega | (have := hr ‹_›; omega)
   have main := loop x d (.seq (W.code (fun o => o.elim (d+1) ref) (d+2) b) (.inc (d+1))) u
     (fun k z => z.reg (d+1) = k ∧ (∀ j < d, z.reg j = s.reg j) ∧ (∀ j, z.reg j ≤ M) ∧ z.work ≤ u.work + (1+N) + k*c)
     ⟨by simp [S.tick,ureg],fun j hj => by simpa [S.tick] using hu j hj,fun j => by simpa [S.tick] using ur j,by simp [S.tick,cnt]⟩
     (by
       intro k z hk ⟨hz1,hzf,hzr,hzw⟩
       rw [cnt] at hk
       have env (o : Option _) : z.reg ((fun o => o.elim (d+1) ref) o) ≤ a + pn.eval a := by
         cases o with
         | none => simp only [Option.elim]; omega
         | some j => simp only [Option.elim]; rw [hzf _ (hr j)]; have := hv j; omega
       obtain ⟨rb,wb⟩ := hb x _ (d+2) z (a + pn.eval a) M hρ (by omega) env hzr
       have sb := W.code_spec b x _ (d+2) hρ z
       unfold W.At at sb
       beta_reduce
       have hz' : (P.exec x (.seq (W.code (fun o => o.elim (d+1) ref) (d+2) b) (.inc (d+1))) z).tick 1 = ⟨Function.update ((W.code (fun o => o.elim (d+1) ref) (d+2) b).exec x z).reg (d+1) (((W.code (fun o => o.elim (d+1) ref) (d+2) b).exec x z).reg (d+1)+1),((W.code (fun o => o.elim (d+1) ref) (d+2) b).exec x z).words,((W.code (fun o => o.elim (d+1) ref) (d+2) b).exec x z).work+1+1⟩ := rfl
       rw [hz']
       generalize (W.code (fun o => o.elim (d+1) ref) (d+2) b).exec x z = v at *
       have v1 : v.reg (d+1) = z.reg (d+1) := sb.2 (d+1) (by omega)
       have kc : (k+1)*c = k*c + c := Nat.succ_mul k c
       refine ⟨by simp [v1,hz1],fun j hj => ?_,fun j => ?_,?_⟩
       · simp only [Function.update_apply]; rw [if_neg (by omega), sb.2 j (by omega)]; exact hzf j hj
       · simp only [Function.update_apply]; split_ifs
         · omega
         · have := rb j; omega
       · simp only; rw [kc, hc]; rw [hc] at hzw; omega)
   obtain ⟨_,_,mr,mw⟩ := main
   rw [cnt] at mw
   have mn := mono pn (show a ≤ a+m by omega)
   have mA := mono pb (show a + pn.eval a ≤ (a+m) + pn.eval (a+m) by omega)
   have kA : (rangeK pn pb).eval a = pn.eval a + B := by simp [rangeK, hB]
   have mS := mono (rangeK pn pb) (show a ≤ a+m by omega)
   have mG := mono pb (show a + pn.eval a + M ≤ (a+m) + pn.eval (a+m) + (rangeK pn pb).eval (a+m) by omega)
   have cN := Nat.mul_le_mul (vn.trans mn) (show c ≤ pb.eval ((a+m) + pn.eval (a+m) + (rangeK pn pb).eval (a+m)) + 2 by omega)
   have t1 := rn (d+1)
   simp only [rangeP,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat] at cN ⊢
   exact ⟨fun j => (mr j).trans (by omega),by omega⟩
end Compact.WS
end

-- OAI.Computability.UniqueGames.Model
section

namespace OAI

namespace UniqueGamesTheorem.Foundations.Target

/-- Finite forward and inverse tables make totality and invertibility explicit.
An eventual external encoding only needs to serialize the forward table. -/
structure PermutationTable (alphabet : Nat) where
  images : Vector (Fin alphabet) alphabet
  inverseImages : Vector (Fin alphabet) alphabet
  leftInverse : ∀ label : Fin alphabet, inverseImages[images[label]] = label
  rightInverse : ∀ label : Fin alphabet, images[inverseImages[label]] = label

structure Constraint (vertices alphabet : Nat) where
  source : Fin vertices
  target : Fin vertices
  permutation : PermutationTable alphabet

def Constraint.satisfied {n q : Nat} (constraint : Constraint n q)
    (labeling : Fin n → Fin q) : Bool :=
  decide (constraint.permutation.images[labeling constraint.source] = labeling constraint.target)

/-- Constraint occurrences are list entries, so repeated parallel edges retain
their multiplicity. No weights are hidden in this representation. -/
structure Instance (alphabet : Nat) where
  vertices : Nat
  constraints : List (Constraint vertices alphabet)
  nonempty : constraints ≠ []

def countSatisfied {n q : Nat} (labeling : Fin n → Fin q) :
    List (Constraint n q) → Nat
  | [] => 0
  | constraint :: rest =>
      (if constraint.satisfied labeling then 1 else 0) + countSatisfied labeling rest

end UniqueGamesTheorem.Foundations.Target

namespace UniqueGamesTheorem.BinaryFormula

open UniqueGamesTheorem.Foundations

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

end UniqueGamesTheorem.BinaryFormula

namespace UniqueGamesTheorem.BinaryEncoding

open BinaryFormula

def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bits => Nat.bit b (bitsValue bits)

def parseFrame : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest => do
      let (bits, trailing) ← parseFrame rest
      return (b :: bits, trailing)
  | _ => none

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

end UniqueGamesTheorem.BinaryEncoding

namespace UniqueGamesTheorem.BinaryLanguage

open UniqueGamesTheorem.Foundations

def language (input : List Bool) : Prop :=
  ∃ formula, BinaryEncoding.decodeFormula input = some formula ∧ formula.Satisfiable

end UniqueGamesTheorem.BinaryLanguage

namespace UniqueGamesTheorem.Integration.BinaryLinear

abbrev F2 := ZMod 2

abbrev Vector (n : Nat) := Fin n → F2

end UniqueGamesTheorem.Integration.BinaryLinear

namespace UniqueGamesTheorem.Integration.TranslationTarget

open UniqueGamesTheorem.Foundations
open Target

def IsTranslationInstance {q s : Nat} (coordinates : Fin q ≃ BinaryLinear.Vector s)
    (g : Instance q) : Prop :=
  ∀ constraint ∈ g.constraints, ∃ shift : BinaryLinear.Vector s,
    ∀ label : Fin q,
      coordinates (constraint.permutation.images[label]) = coordinates label + shift

end UniqueGamesTheorem.Integration.TranslationTarget

namespace UniqueGamesTheorem.Foundations.Complexity

def encodeWord (n : Nat) : List Bool := List.replicate n true ++ [false]

def encodeWords : List Nat → List Bool
  | [] => []
  | n :: ns => encodeWord n ++ encodeWords ns

end UniqueGamesTheorem.Foundations.Complexity

namespace UniqueGamesTheorem.Foundations.Complexity

open Target

def tableWords {q : Nat} (table : PermutationTable q) : List Nat :=
  table.images.toList.map Fin.val

def constraintWords {n q : Nat} (constraint : Constraint n q) : List Nat :=
  [constraint.source.val, constraint.target.val] ++ tableWords constraint.permutation

def gameWords {q : Nat} (game : Instance q) : List Nat :=
  [game.vertices, q, game.constraints.length] ++ game.constraints.flatMap constraintWords

def gameBits {q : Nat} (game : Instance q) : List Bool := encodeWords (gameWords game)

end UniqueGamesTheorem.Foundations.Complexity

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

open Turing

/-- Every physical tape has a finite alphabet. Together with `M.kFin`, this
also makes the disjoint union of all physical tape alphabets finite. -/
def FiniteAlphabet (M : FinTM2) : Prop := ∀ k, Finite (M.Γ k)

end UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

namespace UniqueGamesTheorem.Explicit.MachineOutputContract

open UniqueGamesTheorem.Foundations
open Target
open scoped BigOperators

/-- A canonical orientation from the false side to the true side. Injectivity
is on occurrence indices, so two distinct list entries cannot be parallel even
when their constraint tables are different. -/
structure SimpleBipartite {q : Nat} (game : Instance q) where
  side : Fin game.vertices → Bool
  sourceSide : ∀ i : Fin game.constraints.length,
    side game.constraints[i].source = false
  targetSide : ∀ i : Fin game.constraints.length,
    side game.constraints[i].target = true
  endpoints_injective : Function.Injective (fun i : Fin game.constraints.length =>
    (game.constraints[i].source, game.constraints[i].target))

/-- Every parameter, coordinate identification, program, and polynomial is
fixed before the input quantifier. The identity input encoding measures runtime
in the original raw bit length, including sparse binary variable names. -/
structure BinaryGapReduction (ε δ : ℝ) where
  alphabet : Nat
  alphabetAtLeastTwo : 2 ≤ alphabet
  dimension : Nat
  dimensionPositive : 1 ≤ dimension
  coordinates : Fin alphabet ≃ Integration.BinaryLinear.Vector dimension
  construct : List Bool → Instance alphabet
  simpleBipartite : ∀ input, SimpleBipartite (construct input)
  translations : ∀ input,
    Integration.TranslationTarget.IsTranslationInstance coordinates (construct input)
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    Complexity.gameBits construct
  finiteAlphabet : Complexity.MachineFiniteAlphabet.FiniteAlphabet computation.tm
  completeness : ∀ input, BinaryLanguage.language input →
    ∃ labeling, 1 - ε ≤
      (countSatisfied labeling (construct input).constraints : ℝ) /
        (construct input).constraints.length
  soundness : ∀ input, ¬BinaryLanguage.language input →
    ∀ labeling, (countSatisfied labeling (construct input).constraints : ℝ) /
      (construct input).constraints.length ≤ δ

end UniqueGamesTheorem.Explicit.MachineOutputContract

end OAI
end

-- Bridge
section
/- Bridge: a word-stream program over the input bits yields a polynomial-time
FinTM2 certificate for any function whose output is a word list. -/
namespace Compact.WS
open Compact.Reg Cmd Phys Polynomial Turing
abbrev bpWords := OAI.BinPackingGames.Foundations.Complexity.encodeWords
abbrev ugWords := OAI.UniqueGamesTheorem.Foundations.Complexity.encodeWords

theorem bp_ug (ws : List Nat) : bpWords ws = ugWords ws := by
 induction ws with
 | nil => rfl
 | cons n ns ih =>
   simp only [bpWords, ugWords, OAI.BinPackingGames.Foundations.Complexity.encodeWords,
     OAI.UniqueGamesTheorem.Foundations.Complexity.encodeWords] at *
   rw [ih]; rfl

/-- `Compact.Reg.realize` with an arbitrary input encoding (same proof). -/
noncomputable def realizeG {K : Type} [DecidableEq K] [Fintype K] (p : P K) {A B : Type}
 (ea : A → List Bool) (F : A → B) (enc : B → List Bool) (T : Polynomial Nat)
 (words : ∀ a, bpWords (p.exec (ea a) S.init).words = enc (F a))
 (cost : ∀ a, (p.exec (ea a) S.init).work ≤ T.eval (ea a).length) : TM2ComputableInPolyTime ea enc F := by
 let N := p.depth
 let B := compile (Phys.base K N) p N le_rfl le_rfl
 let i : J K N := io 0
 let a : J K N := io 1
 let o : J K N := io 2
 let q := Cleanup.finish B.code a o
 let z : Polynomial Nat := 20*T
 let v : Polynomial Nat := X+z
 let u : Polynomial Nat := z+C ((Cleanup.others a).length+1)*(2*v+1)+(4*v+1)
 apply Cmd.realizes q i o ea enc F u
 intro y
 set x := ea y with hx
 obtain ⟨n,r,hn⟩ := B.sound x (fun _ => 0) S.init (by simp)
 have start : Phys.repr x (fun _ : Fin N => 0) (S.init : S K) = singleStack i x := by
   funext j; rcases j with k|(l|(u|v))
   · rfl
   · rfl
   · fin_cases u <;> rfl
   · rfl
 change Run _ (Phys.repr x (fun _ : Fin N => 0) S.init) (Phys.repr x (fun _ : Fin N => 0) (p.exec x S.init)) _ at r
 rw [start] at r
 have out : Phys.repr x (fun _ : Fin N => 0) (p.exec x S.init) a = (enc (F y)).reverse := by change (bpWords _).reverse = _; rw [words]
 obtain ⟨m,r',hm⟩ := Cleanup.finishRun (o:=o) (by simp [a,o] : a ≠ o) r out
 refine ⟨m,r',hm.trans ?_⟩
 have nle : n ≤ z.eval x.length := by
   change 0*20+n ≤ (p.exec x S.init).work*20 at hn
   have hc := cost y; rw [← hx] at hc; simp [z]; omega
 simp only [u,eval_add,eval_mul,eval_C,eval_ofNat,eval_one,v,eval_X]
 gcongr

/-- Main bridge: a closed word stream whose emitted words encode `eb (f a)`. -/
noncomputable def ofW (w : W Empty) {A B : Type} (ea : A → List Bool) (eb : B → List Bool) (f : A → B)
 (h : ∀ a, ugWords (w.eval (ea a) Empty.elim) = eb (f a)) : TM2ComputableInPolyTime ea eb f :=
 let p := W.code Empty.elim 0 w
 realizeG p.finite ea f eb (W.bound w).choose
  (fun a => by
    rw [P.finite_exec]
    have hs := W.code_spec w (ea a) Empty.elim 0 (fun j => nomatch j) S.init
    change bpWords ((p.exec (ea a) S.init).words) = _
    have e : ((S.init : S Nat).reg ∘ (Empty.elim : Empty → Nat)) = Empty.elim := funext (fun j => nomatch j)
    rw [hs.1, bp_ug, e, ← h a]; rfl)
  (fun a => by
    rw [P.finite_exec]
    have hb := (W.bound w).choose_spec (ea a) Empty.elim 0 S.init (ea a).length 0 (fun j => nomatch j) le_rfl (fun j => nomatch j) (fun j => by simp [S.init])
    change (p.exec (ea a) S.init).work ≤ _
    simpa [S.init] using hb.2)
theorem ofW_finite (w : W Empty) {A B : Type} (ea : A → List Bool) (eb : B → List Bool) (f : A → B) (h) :
  ∀ k, Finite ((ofW w ea eb f h).tm.Γ k) := fun _ => inferInstanceAs (Finite Bool)
end Compact.WS
end

-- Words
section
/- Random access to the k-th unary word of the input, and finite tables. -/
namespace Compact.WS
open Compact.Reg Turing

namespace E
def rename {α β : Type} (f : α → β) : E α → E β
 | .var a => .var (f a) | .const n => .const n | .len => .len | .read i => .read (rename f i)
 | .bin op a b => .bin op (rename f a) (rename f b) | .cond c y n => .cond (rename f c) (rename f y) (rename f n)
 | .sum n b => .sum (rename f n) (rename (Option.map f) b)

theorem val_rename {α β : Type} (f : α → β) (e : E α) (x) (v : β → Nat) : (e.rename f).val x v = e.val x (v ∘ f) := by
 induction e generalizing β with
 | var a => rfl
 | const n => rfl
 | len => rfl
 | read i ih => simp only [rename,val,ih]
 | bin op a b ia ib => simp only [rename,val,ia,ib]
 | cond c y n ic iy ineg => simp only [rename,val,ic,iy,ineg]
 | sum n b ihn ihb =>
   simp only [rename,val,ihn,ihb]
   apply Finset.sum_congr rfl; intro j _; congr 1; funext o; cases o <;> rfl

def notE (e : E α) : E α := .bin .sub (.const 1) e
def eqE (a b : E α) : E α := .cond (.bin .add (.bin .sub a b) (.bin .sub b a)) (.const 0) (.const 1)
@[simp] theorem val_eqE (a b : E α) (x v) : (eqE a b).val x v = if a.val x v = b.val x v then 1 else 0 := by
 show (if (a.val x v - b.val x v) + (b.val x v - a.val x v) ≠ 0 then 0 else 1) = _
 split_ifs <;> omega
/-- Number of `false` bits strictly before position `j`. -/
def zerosE (j : E α) : E α := .sum j (notE (.read (.var none)))
/-- The `k`-th zero-delimited unary word of the input. -/
def wordE (k : E α) : E α := .sum .len (.bin .mul (.read (.var none)) (eqE (zerosE (.var none)) (k.rename some)))
end E

def bitv (x : List Bool) (j : Nat) : Nat := if x[j]?.getD false then 1 else 0
def zb (x : List Bool) (j : Nat) : Nat := ∑ i ∈ Finset.range j, (1 - bitv x i)
def cntW (x : List Bool) (k : Nat) : Nat := ∑ j ∈ Finset.range x.length, bitv x j * (if zb x j = k then 1 else 0)

theorem val_wordE (k : E α) (x v) : (E.wordE k).val x v = cntW x (k.val x v) := by
 simp only [E.wordE,E.zerosE,E.notE,E.val,E.val_eqE,E.val_rename,Op.eval,cntW,zb,bitv]
 rfl

theorem zb_cons (b : Bool) (x : List Bool) (j : Nat) : zb (b :: x) (j+1) = zb x j + (if b then 0 else 1) := by
 simp only [zb, Finset.sum_range_succ']
 congr 1; cases b <;> rfl

theorem cntW_true (x : List Bool) (k : Nat) : cntW (true :: x) k = (if k = 0 then 1 else 0) + cntW x k := by
 unfold cntW
 rw [List.length_cons, Finset.sum_range_succ']
 have h0 : zb (true :: x) 0 = 0 := rfl
 have b0 : bitv (true :: x) 0 = 1 := rfl
 rw [h0, b0, Nat.add_comm]
 congr 1
 · by_cases hk : k = 0
   · subst hk; simp
   · rw [if_neg (Ne.symm hk), if_neg hk]
 · apply Finset.sum_congr rfl; intro j _
   rw [zb_cons]; rfl

theorem cntW_false (x : List Bool) (k : Nat) : cntW (false :: x) k = if k = 0 then 0 else cntW x (k-1) := by
 simp only [cntW, List.length_cons, Finset.sum_range_succ']
 have : bitv (false :: x) 0 = 0 := rfl
 rw [this, Nat.zero_mul, Nat.add_zero]
 simp only [zb_cons, Bool.false_eq_true, if_false]
 split_ifs with hk
 · apply Finset.sum_eq_zero; intro j _; rw [if_neg (by omega)]; simp
 · apply Finset.sum_congr rfl; intro j _
   have : bitv (false :: x) (j+1) = bitv x j := rfl
   rw [this]; congr 1; congr 1; apply propext; omega

theorem cntW_rep (n : Nat) (x : List Bool) (k : Nat) : cntW (List.replicate n true ++ x) k = (if k = 0 then n else 0) + cntW x k := by
 induction n with
 | zero => simp
 | succ n ih => rw [List.replicate_succ, List.cons_append, cntW_true, ih]; split_ifs <;> omega

theorem cntW_words (ws : List Nat) (k : Nat) : cntW (ugWords ws) k = ws.getD k 0 := by
 induction ws generalizing k with
 | nil => simp [ugWords, OAI.UniqueGamesTheorem.Foundations.Complexity.encodeWords, cntW]
 | cons n ns ih =>
   simp only [ugWords, OAI.UniqueGamesTheorem.Foundations.Complexity.encodeWords, OAI.UniqueGamesTheorem.Foundations.Complexity.encodeWord, List.append_assoc, List.singleton_append] at ih ⊢
   rw [cntW_rep, cntW_false]
   cases k with
   | zero => simp
   | succ k => simp [ih]

/-- Finite lookup table indexed by an expression. -/
def tabAux (i : E α) : Nat → List Nat → E α
 | _, [] => .const 0
 | off, a :: r => .cond (E.eqE i (.const off)) (.const a) (tabAux i (off+1) r)
def tab (l : List Nat) (i : E α) : E α := tabAux i 0 l

theorem val_tabAux (i : E α) (x v) (l : List Nat) (off : Nat) (h : off ≤ i.val x v) :
  (tabAux i off l).val x v = l.getD (i.val x v - off) 0 := by
 induction l generalizing off with
 | nil => simp [tabAux, E.val]
 | cons a r ih =>
   simp only [tabAux, E.val, E.val_eqE]
   by_cases e : i.val x v = off
   · simp [e]
   · rw [if_neg (by simp [e]), ih (off+1) (by omega)]
     obtain ⟨d, hd⟩ : ∃ d, i.val x v - off = d + 1 := ⟨i.val x v - off - 1, by omega⟩
     rw [hd, show i.val x v - (off+1) = d by omega]; simp

theorem val_tab (l : List Nat) (i : E α) (x v) : (tab l i).val x v = l.getD (i.val x v) 0 := by
 unfold tab; simpa using val_tabAux i x v l 0 (Nat.zero_le _)

end Compact.WS
end

-- MatrixShape
section
/- Matrix shape pass. Compiler: Compact.WS, adapted from OpenAI 3344da59. -/
namespace MatrixShape
open Compact.WS Turing
private def nextIx : E (Option α) := .bin .add (.var none) (.const 1)
def dim : E α := .sum .len (.cond (.bin .sub (.bin .mul nextIx nextIx) .len) (.const 0) (.const 1))
theorem dim_ok (x : List Bool) (env : α → Nat) : dim.val x env = x.length.sqrt := by
 change (∑ j ∈ Finset.range x.length, if (j+1)*(j+1)-x.length ≠ 0 then 0 else 1) = _
 have h (j : Nat) : (if (j+1)*(j+1)-x.length ≠ 0 then 0 else 1 : Nat) = if j < x.length.sqrt then 1 else 0 := by
   have := Nat.le_sqrt (m := j+1) (n := x.length)
   split_ifs <;> omega
 simp_rw [h]; rw [← Finset.sum_filter]
 have hf : (Finset.range x.length).filter (fun j => j < x.length.sqrt) = Finset.range x.length.sqrt := by
   ext i; simp only [Finset.mem_filter,Finset.mem_range]; exact and_iff_right_of_imp (fun hi => lt_of_lt_of_le hi (Nat.sqrt_le_self _))
 simp [hf]
def valid : E α := E.eqE .len (.bin .mul dim dim)
def shape (x : List Bool) : List Nat := [x.length.sqrt, if x.length = x.length.sqrt*x.length.sqrt then 1 else 0]
def prog : W Empty := .cat (.word dim) (.word valid)
theorem output (x : List Bool) : prog.eval x Empty.elim = shape x := by simp [shape,prog,W.eval,valid,E.val,dim_ok,Op.eval]
noncomputable def machine : TM2ComputableInPolyTime id ugWords shape := ofW prog id ugWords shape (fun x => congrArg ugWords (output x))
theorem finite (k) : Finite (machine.tm.Γ k) := inferInstanceAs (Finite Bool)
end MatrixShape
end

-- MatrixSerialize
section
/- Binary formula and decoder adapted from OpenAI math 3344da59. -/
namespace UGBridge.SAT
open OAI.UniqueGamesTheorem.BinaryFormula OAI.UniqueGamesTheorem.BinaryEncoding
open OAI.UniqueGamesTheorem.BinaryLanguage

def frame : List Bool → List Bool
  | [] => [false]
  | b::bs => true :: b :: frame bs

theorem unframe (xs rest) : parseFrame (frame xs ++ rest) = some (xs,rest) := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [frame, parseFrame, ih]

theorem digits (n : Nat) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih => simp [Nat.bits_append_bit _ _ h, bitsValue, ih]

def lit (l : Literal) := l.positive :: frame l.name.bits

theorem unlit (l : Literal) (rest) : parseLiteral (lit l ++ rest) = some (l, rest) := by
  cases l; simp [lit, parseLiteral, parseName, unframe, digits]

def clause (v : Clause) := lit v[0] ++ lit v[1] ++ lit v[2]

theorem unclause (v : Clause) (rest) : parseClause (clause v ++ rest) = some (v,rest) := by
  have h : #v[v[0],v[1],v[2]] = v := by ext i hi; interval_cases i <;> rfl
  simp [clause, parseClause, List.append_assoc, unlit, h]

def body : List Clause → List Bool
  | [] => [false]
  | v::cs => true :: (clause v ++ body cs)

theorem unbody (cs) (n : Nat) (h : cs.length < n) : parseClauses n (body cs) = some (cs,[]) := by
  induction cs generalizing n with
  | nil => cases n <;> simp_all [body,parseClauses]
  | cons v cs ih =>
    cases n with
    | zero => omega
    | succ n => simp [body, parseClauses, unclause, ih n (by simpa using h)]

theorem length_body (cs : List Clause) : cs.length ≤ (body cs).length := by
  induction cs with
  | nil => simp
  | cons v cs ih => simp [body]; omega

theorem decoded (f : Formula) : decodeFormula (body f.clauses) = some f := by
  cases f with
  | mk cs => simp [decodeFormula, unbody cs _ (Nat.lt_succ_of_le (length_body cs))]

theorem language_body (f : Formula) : language (body f.clauses) ↔ f.Satisfiable := by
  simp [language, decoded]
end UGBridge.SAT
namespace MatrixSAT
open OAI.UniqueGamesTheorem.BinaryFormula

def pos (i t : Nat) : Literal := ⟨3*i+t,true⟩
def neg (i t : Nat) : Literal := ⟨3*i+t,false⟩
def vertex (i : Nat) : Clause := #v[pos i 0,pos i 1,pos i 2]
def edge (i j t : Nat) : Clause := #v[neg i t,neg j t,neg j t]
def sat (y : List Bool) (n : Nat) : Formula := ⟨((List.range n).map vertex) ++
  (List.range n).flatMap fun i => (List.range n).flatMap fun j =>
    if y.getD (i*n+j) false then (List.range 3).map (edge i j) else []⟩

theorem spec (y : List Bool) (n : Nat) : (sat y n).Satisfiable ↔
    ∃ c : Fin n → Fin 3, ∀ i j, y.getD (i.val*n+j.val) false = true → c i ≠ c j := by
  classical
  constructor
  · rintro ⟨a,ha⟩
    have hv (i : Fin n) : ∃ t : Fin 3, a (3*i.val+t.val) = true := by
      have h := ha (vertex i.val) (List.mem_append_left _ (List.mem_map.mpr ⟨i.val,List.mem_range.mpr i.isLt,rfl⟩))
      simp [vertex,pos,Clause.eval,Literal.eval] at h
      rcases h with (h|h)|h
      · exact ⟨0,by simpa using h⟩
      · exact ⟨1,h⟩
      · exact ⟨2,h⟩
    refine ⟨fun i => (hv i).choose, ?_⟩
    intro i j hij eq
    let t := (hv i).choose
    have he := ha (edge i.val j.val t.val) (by
      apply List.mem_append_right
      apply List.mem_flatMap.mpr; refine ⟨i.val,List.mem_range.mpr i.isLt,?_⟩
      apply List.mem_flatMap.mpr; refine ⟨j.val,List.mem_range.mpr j.isLt,?_⟩
      rw [if_pos hij]; exact List.mem_map.mpr ⟨t.val,List.mem_range.mpr t.isLt,rfl⟩)
    have hi : a (3*i.val+t.val) = true := (hv i).choose_spec
    have hj : a (3*j.val+t.val) = true := by simpa only [t,eq] using (hv j).choose_spec
    simp [edge,neg,Clause.eval,Literal.eval,hi,hj] at he
  · rintro ⟨c,hc⟩
    let a (x : Nat) := if h : x/3 < n then decide ((c ⟨x/3,h⟩).val = x%3) else false
    have ev (i : Fin n) (t : Fin 3) : a (3*i.val+t.val) = decide (c i = t) := by
      have h : (3*i.val+t.val)/3 = i.val := by omega
      have h' : (3*i.val+t.val)%3 = t.val := by omega
      simp [a,h,h',i.isLt,Fin.ext_iff]
    refine ⟨a,?_⟩
    intro cl hm
    rcases List.mem_append.mp hm with hm|hm
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
      let v : Fin n := ⟨i,List.mem_range.mp hi⟩
      have hh := ev v (c v)
      generalize h : c v = t at hh
      fin_cases t <;> simp_all [vertex,Clause.eval,pos,Literal.eval,v]
    · obtain ⟨i,hi,hm⟩ := List.mem_flatMap.mp hm
      obtain ⟨j,hj,hm⟩ := List.mem_flatMap.mp hm
      split at hm
      case isFalse => contradiction
      rename_i h
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hm
      let u : Fin n := ⟨i,List.mem_range.mp hi⟩
      let v : Fin n := ⟨j,List.mem_range.mp hj⟩
      let z : Fin 3 := ⟨t,List.mem_range.mp ht⟩
      have hn := hc u v h
      have hu := ev u z
      have hv := ev v z
      change a (3*i+t) = _ at hu
      change a (3*j+t) = _ at hv
      by_cases e : c u = z <;> simp_all [edge,Clause.eval,neg,Literal.eval]
      exact Ne.symm hn

def impossible : Formula := ⟨[#v[pos 0 0,pos 0 0,pos 0 0], #v[neg 0 0,neg 0 0,neg 0 0]]⟩
theorem impossible_no : ¬ impossible.Satisfiable := by
  rintro ⟨a,h⟩
  have h1 := h _ (List.Mem.head _)
  have h2 := h _ (List.Mem.tail _ (List.Mem.head _))
  simp_all [pos,neg,Literal.eval,Clause.eval]

def fromBits (y : List Bool) : Formula :=
  if y.length = y.length.sqrt*y.length.sqrt then sat y y.length.sqrt else impossible

theorem exact_graph (y : List Bool) : (fromBits y).Satisfiable ↔
    ∃ (n : Nat) (c : Fin n → Fin 3), y.length = n*n ∧
      ∀ i j, y.getD (i.val*n+j.val) false = true → c i ≠ c j := by
  unfold fromBits
  split <;> rename_i h
  · rw [spec]; constructor
    · rintro ⟨c,hc⟩; exact ⟨_,c,h,hc⟩
    · rintro ⟨n,c,hn,hc⟩
      have e : y.length.sqrt = n := by rw [hn]; simp
      rw [e]; exact ⟨c,hc⟩
  · constructor
    · exact fun hx => (impossible_no hx).elim
    · rintro ⟨n,c,hn,hc⟩
      exact (h (by rw [hn]; simp)).elim
end MatrixSAT
end

-- Framed2
section
/- Framed identifiers for the OpenAI 3344da59 binary SAT decoder. -/
namespace MatrixFramed
open Compact.WS UGBridge.SAT OAI.UniqueGamesTheorem.BinaryFormula OAI.UniqueGamesTheorem.BinaryEncoding
abbrev rep (n : Nat) := List.replicate n true
def name (n : Nat) := bitsValue (rep n)
theorem step (n : Nat) : name (n+1) = 2*name n+1 := by simp [name,rep,List.replicate_succ,bitsValue,Nat.bit]
theorem inj : Function.Injective name := (strictMono_nat_of_lt_succ (fun n => by rw [step]; omega)).injective
theorem canonical (n : Nat) : (name n).bits = rep n := by
 induction n with
 | zero => rfl
 | succ n ih =>
   change (Nat.bit true (name n)).bits = _
   rw [Nat.bits_append_bit _ _ (by simp), ih]; rfl

theorem framed (n : Nat) : UGBridge.SAT.frame (rep n) = rep (2*n) ++ [false] := by
 induction n with
 | zero => rfl
 | succ n ih => rw [show 2*(n+1) = (2*n+1)+1 by omega]; unfold rep at *; rw [List.replicate_succ,UGBridge.SAT.frame,ih]; rfl

def words (prefixLen : Nat) (positive : Bool) (n : Nat) := if positive then [prefixLen+1+2*n] else [prefixLen,2*n]
def prog (k : Nat) (p : Bool) (n : E α) : W α := if p then .word (.bin .add (.const (k+1)) (.bin .mul (.const 2) n)) else .cat (.word (.const k)) (.word (.bin .mul (.const 2) n))
theorem emit (k p) (n : E α) (x v) : (prog k p n).eval x v = words k p (n.val x v) := by cases p <;> rfl
theorem wire (k p n) : ugWords (words k p n) = rep k ++ p :: UGBridge.SAT.frame (rep n) := by
 rw [framed]; cases p <;> simp [words,ugWords,OAI.UniqueGamesTheorem.Foundations.Complexity.encodeWords,OAI.UniqueGamesTheorem.Foundations.Complexity.encodeWord,rep,List.replicate_add,List.append_assoc]
theorem parsed (p n rest) : OAI.UniqueGamesTheorem.BinaryEncoding.parseLiteral (ugWords (words 0 p n) ++ rest) = some (⟨name n,p⟩,rest) := by
 rw [wire]; simp [rep,OAI.UniqueGamesTheorem.BinaryEncoding.parseLiteral,OAI.UniqueGamesTheorem.BinaryEncoding.parseName,unframe, show (bitsValue (rep n)).bits = rep n from canonical n, name]
end MatrixFramed
end

-- MatrixWord2
section
namespace MatrixFramed
open Compact.WS MatrixSAT OAI.UniqueGamesTheorem.BinaryFormula UGBridge.SAT Turing
def rn (l : Literal) : Literal := ⟨name l.name,l.positive⟩
def rc (c : Clause) : Clause := c.map rn
def rf (f : Formula) : Formula := ⟨f.clauses.map rc⟩
theorem sat_iff (f : Formula) : (rf f).Satisfiable ↔ f.Satisfiable := by
 classical
 have ev (c : Clause) (a b : Nat → Bool) (h : ∀ n, a (name n) = b n) : (rc c).eval a = c.eval b := by simp [rc,rn,Clause.eval,Literal.eval,h]
 constructor
 · rintro ⟨a,ha⟩; exact ⟨a ∘ name, fun c hc => (ev c a _ (fun _ => rfl)).symm.trans (ha _ (List.mem_map.mpr ⟨c,hc,rfl⟩))⟩
 · rintro ⟨b,hb⟩; let a := b ∘ Function.invFun name
   refine ⟨a,?_⟩; intro c hc; obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
   exact (ev d a b (fun n => congrArg b (Function.leftInverse_invFun inj n))).trans (hb d hd)
def cw (v : Clause) := words 1 (v[0]).positive (v[0]).name ++ words 0 (v[1]).positive (v[1]).name ++ words 0 (v[2]).positive (v[2]).name
theorem catWords (a b : List Nat) : ugWords (a++b) = ugWords a ++ ugWords b := by
 induction a with
 | nil => rfl
 | cons x xs ih => change _ ++ ugWords (xs ++ b) = (_ ++ ugWords xs) ++ _; rw [ih,List.append_assoc]
theorem cw_ok (c : Clause) : ugWords (cw c) = true :: clause (rc c) := by simp [cw,catWords,wire,clause,lit,rc,rn,canonical,rep]
def fw (f : Formula) := f.clauses.flatMap cw ++ [0]
theorem fw_ok (f : Formula) : ugWords (fw f) = body (rf f).clauses := by
 obtain ⟨cs⟩ := f; change ugWords (cs.flatMap cw ++ [0]) = body (cs.map rc)
 induction cs with
 | nil => rfl
 | cons c cs ih => simp [List.append_assoc,catWords,cw_ok,body,← ih]

def triple (p : Bool) (a b c : E α) : W α := .cat (prog 1 p a) (.cat (prog 0 p b) (prog 0 p c))
def ix (i t : E α) : E α := .bin .add (.bin .mul (.const 3) i) t
def vert (i : E α) := triple true (ix i (.const 0)) (ix i (.const 1)) (ix i (.const 2))
def ed (i j t : E α) := triple false (ix i t) (ix j t) (ix j t)
def good : W Empty := .cat (.range MatrixShape.dim (vert (.var none))) (.range MatrixShape.dim (.range MatrixShape.dim (.guard (.read (.bin .add (.bin .mul (.var (some none)) MatrixShape.dim) (.var none))) (.range (.const 3) (ed (.var (some (some none))) (.var (some none)) (.var none))) .nil)))
def fixed : List Nat → W α | [] => .nil | n::ns => .cat (.word (.const n)) (fixed ns)
theorem fixed_ok (ns : List Nat) (x : List Bool) (v : α → Nat) : (fixed ns).eval x v = ns := by induction ns <;> simp_all [fixed,W.eval,E.val]
def allP : W Empty := .cat (.guard MatrixShape.valid good (fixed (impossible.clauses.flatMap cw))) (.word (.const 0))
theorem good_ok (x : List Bool) : good.eval x Empty.elim = (sat x x.length.sqrt).clauses.flatMap cw := by
 simp [good,W.eval,MatrixShape.dim_ok,E.val,sat,List.flatMap_append,List.flatMap_map,List.flatMap_assoc,Function.comp_def]
 simp [vert,ed,triple,W.eval,emit,ix,E.val,Op.eval,vertex,edge,cw,neg,pos, List.getD_eq_getElem?_getD]
 congr 1; funext i; congr 1; funext j; split_ifs <;> simp [List.flatMap_map] <;> rfl

theorem all_ok (x : List Bool) : allP.eval x Empty.elim = fw (fromBits x) := by
 have flag : MatrixShape.valid.val x Empty.elim = if x.length = x.length.sqrt*x.length.sqrt then 1 else 0 := by simp [MatrixShape.valid,E.val,MatrixShape.dim_ok,Op.eval]
 change (if MatrixShape.valid.val x Empty.elim ≠ 0 then _ else _) ++ [0] = _ ++ [0]
 rw [flag]; unfold fromBits; split <;> rename_i h
 · rw [if_pos one_ne_zero, good_ok]
 · rw [if_neg (by simp), fixed_ok]
def output (x : List Bool) := body (rf (fromBits x)).clauses
noncomputable def machine : TM2ComputableInPolyTime id id output := ofW allP id id output (fun x => by rw [id_eq,all_ok,fw_ok];rfl)
theorem finite (k) : Finite (machine.tm.Γ k) := inferInstanceAs (Finite Bool)
theorem language_ok (x : List Bool) : OAI.UniqueGamesTheorem.BinaryLanguage.language (output x) ↔ ∃ (n : Nat) (c : Fin n → Fin 3), x.length = n*n ∧ ∀ i j, x.getD (i.val*n+j.val) false = true → c i ≠ c j := (language_body (rf (fromBits x))).trans ((sat_iff _).trans (exact_graph x))
end MatrixFramed
end

-- LeafMat
section
namespace LeafProofs
open OAI.UniqueGamesTheorem.BinaryFormula OAI.UniqueGamesTheorem.BinaryEncoding OAI.UniqueGamesTheorem.BinaryLanguage

def enc (cs : List (Fin 3 → ℕ × Bool)) : List Bool :=
  (cs.flatMap fun c => true :: (List.finRange 3).flatMap fun t =>
    (c t).2 :: ((c t).1.bits.flatMap fun b => [true, b]) ++ [false]) ++ [false]
def Sat (cs : List (Fin 3 → ℕ × Bool)) : Prop := ∃ a : ℕ → Bool, ∀ c ∈ cs, ∃ t, a (c t).1 = (c t).2
def SAT3 (x : List Bool) : Prop := ∃ cs, x = enc cs ∧ Sat cs

def toC (v : Clause) : Fin 3 → ℕ × Bool := fun t => (v[t].name, v[t].positive)
def ofC (c : Fin 3 → ℕ × Bool) : Clause := #v[⟨(c 0).1,(c 0).2⟩,⟨(c 1).1,(c 1).2⟩,⟨(c 2).1,(c 2).2⟩]
theorem ofC_toC (v : Clause) : ofC (toC v) = v := by ext i hi; interval_cases i <;> rfl

theorem frame_eq (bs : List Bool) : UGBridge.SAT.frame bs = (bs.flatMap fun b => [true, b]) ++ [false] := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [UGBridge.SAT.frame, ih]

theorem body_eq (cs : List Clause) : UGBridge.SAT.body cs = enc (cs.map toC) := by
  induction cs with
  | nil => rfl
  | cons v cs ih =>
    rw [UGBridge.SAT.body, ih]
    simp [enc, UGBridge.SAT.clause, UGBridge.SAT.lit, frame_eq, toC, List.finRange_succ, Fin.succ]

theorem lit_eval (l : Literal) (a : ℕ → Bool) : l.eval a = true ↔ a l.name = l.positive := by
  cases l with | mk n p => cases p <;> simp [Literal.eval]

theorem sat_iff (cs : List Clause) : Sat (cs.map toC) ↔ (Formula.mk cs).Satisfiable := by
  unfold Sat Formula.Satisfiable
  refine exists_congr fun a => ?_
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun v _ => ?_
  simp only [Clause.eval, Bool.or_eq_true, lit_eval, toC, Fin.exists_fin_succ]
  simp [or_assoc, Fin.succ, Fin.exists_fin_two]


theorem unframe' : ∀ (xs bs rest : List Bool), parseFrame xs = some (bs, rest) → xs = UGBridge.SAT.frame bs ++ rest
  | false :: r, bs, rest, h => by simp [parseFrame] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | true :: b :: r, bs, rest, h => by
    simp only [parseFrame] at h
    rcases hp : parseFrame r with _ | ⟨bs', rest'⟩ <;> simp [hp] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [UGBridge.SAT.frame, unframe' r bs' rest' hp]
  | [], _, _, h => by simp [parseFrame] at h
  | [true], _, _, h => by simp [parseFrame] at h

theorem unlit' (xs : List Bool) (l : Literal) (rest : List Bool) (h : parseLiteral xs = some (l, rest)) :
    xs = UGBridge.SAT.lit l ++ rest := by
  match xs, h with
  | s :: inp, h =>
    rcases hp : parseFrame inp with _ | ⟨ds, r⟩
    · simp [parseLiteral, parseName, hp] at h
    · have key : parseName inp = if ds = (bitsValue ds).bits then some (bitsValue ds, r) else none := by
        simp [parseName, hp]
      split at key
      · rename_i hd
        have h' : some ((⟨bitsValue ds, s⟩ : Literal), r) = some (l, rest) := by
          simpa [parseLiteral, key] using h
        simp only [Option.some.injEq, Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        rw [unframe' _ _ _ hp]
        show s :: (UGBridge.SAT.frame ds ++ r) = (s :: UGBridge.SAT.frame (bitsValue ds).bits) ++ r
        rw [← hd]; rfl
      · simp [parseLiteral, key] at h

theorem unclause' (xs : List Bool) (v : Clause) (rest : List Bool) (h : parseClause xs = some (v, rest)) :
    xs = UGBridge.SAT.clause v ++ rest := by
  simp only [parseClause] at h
  rcases h1 : parseLiteral xs with _ | ⟨a, r1⟩ <;> simp [h1] at h
  rcases h2 : parseLiteral r1 with _ | ⟨b, r2⟩ <;> simp [h2] at h
  rcases h3 : parseLiteral r2 with _ | ⟨c, r3⟩ <;> simp [h3] at h
  obtain ⟨hv, rfl⟩ := h
  have hv' : v = #v[a, b, c] := (Vector.toArray_inj.mp hv).symm
  subst hv'
  rw [unlit' _ _ _ h1, unlit' _ _ _ h2, unlit' _ _ _ h3]
  simp [UGBridge.SAT.clause, List.append_assoc]

theorem unclauses : ∀ (n : ℕ) (xs : List Bool) (cs : List Clause) (rest : List Bool),
    parseClauses n xs = some (cs, rest) → xs = UGBridge.SAT.body cs ++ rest
  | 0, _, _, _, h => by simp [parseClauses] at h
  | n+1, false :: r, cs, rest, h => by simp [parseClauses] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | n+1, [], _, _, h => by simp [parseClauses] at h
  | n+1, true :: r, cs, rest, h => by
    simp only [parseClauses] at h
    rcases h1 : parseClause r with _ | ⟨v, r1⟩ <;> simp [h1] at h
    rcases h2 : parseClauses n r1 with _ | ⟨cs', r2⟩ <;> simp [h2] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [unclause' _ _ _ h1, unclauses n _ _ _ h2]
    simp [UGBridge.SAT.body, List.append_assoc]

/-- Canonical encodings are exactly the accepted inputs of the OpenAI decoder. -/
theorem lang_iff (x : List Bool) : language x ↔ SAT3 x := by
  constructor
  · rintro ⟨⟨cs⟩, hf, hs⟩
    refine ⟨cs.map toC, ?_, (sat_iff cs).2 hs⟩
    rw [← body_eq]
    unfold decodeFormula at hf
    rcases hp : parseClauses (x.length + 1) x with _ | ⟨cs', rest⟩
    · rw [hp] at hf; simp at hf
    · rw [hp] at hf
      by_cases hr : rest = []
      · subst hr; simp at hf; subst hf
        simpa using unclauses _ _ _ _ hp
      · simp [hr] at hf
  · rintro ⟨cs, rfl, hs⟩
    have h : enc cs = UGBridge.SAT.body (cs.map ofC) := by
      rw [body_eq, List.map_map]; congr 1
      symm; apply List.map_id''; intro c; funext t; fin_cases t <;> rfl
    rw [h, UGBridge.SAT.language_body]
    rw [← sat_iff, List.map_map]
    have : (toC ∘ ofC) = id := by funext c t; fin_cases t <;> rfl
    rwa [this, List.map_id]

theorem H2_proof : OMA.R_wp_unique_games_conjecture_R1_H2_R1.H2 := by
  refine ⟨MatrixFramed.output, ⟨MatrixFramed.machine, MatrixFramed.finite⟩, fun y => ?_⟩
  exact (lang_iff _).symm.trans (MatrixFramed.language_ok y)

end LeafProofs
theorem OMA.solution : OMA.R_wp_unique_games_conjecture_R1_H2_R1.H2 := LeafProofs.H2_proof
end
