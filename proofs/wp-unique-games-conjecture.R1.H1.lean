import OMAReductions.R_wp_unique_games_conjecture_R1
import Mathlib

/- Proof of wp-unique-games-conjecture.R1.H1 (NP-hardness of 3-Coloring on n*n adjacency matrices).
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

-- OAI.Computability.BinPacking.CookLevin.VerifierCircuit
section
/- Adapted from OpenAI/openai math, 3344da59991ed94f9ba711217b29c1d760badfa6. See LICENSE.openai. -/
namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin

structure PolynomialThreeSATReduction (language : List Bool → Prop) where
  reduce : List Bool → Target.Formula
  computation : Turing.TM2ComputableInPolyTime id formulaBits reduce
  correct : ∀ input, language input ↔ (reduce input).Satisfiable

noncomputable def NPVerifier.horizon (verifier : NPVerifier) (inputLength : Nat) : Nat :=
  verifier.computation.time.eval
    (2 * inputLength + verifier.witnessBound.eval inputLength + 1)

end BinPackingGames.Foundations.Complexity.CookLevin
end
end OAI
end

-- CNF
section
/- Independent tableau construction for the OpenAI verifier API. See LICENSE.openai. -/
namespace Window
open OAI.BinPackingGames.Foundations Target
inductive Q (α : Type) where
 | ret (x : α)
 | ask (i : Nat) (yes no : Q α)
 deriving DecidableEq
namespace Q
def run (a : Nat → Bool) : Q α → α
 | .ret x => x
 | .ask i y n => if a i then run a y else run a n
def seq (q : Q α) (f : α → Q β) : Q β := match q with
 | .ret x => f x
 | .ask i y n => .ask i (seq y f) (seq n f)
@[simp] theorem run_seq (q : Q α) (f : α → Q β) (a) : (q.seq f).run a = (f (q.run a)).run a := by
 induction q <;> simp_all [seq,run] <;> split <;> rfl
end Q
abbrev Key := Sum Nat (Q Bool)
local instance : BEq Key := ⟨fun x y => decide (x = y)⟩
local instance : LawfulBEq Key where
  eq_of_beq := by simp [BEq.beq]
  rfl := by simp [BEq.beq]
abbrev Lit := Key × Bool
abbrev Triple := Lit × Lit × Lit
def pos (q : Q Bool) : Lit := (.inr q,true)
def neg (q : Q Bool) : Lit := (.inr q,false)
def gates : Q Bool → List Triple
 | .ret true => []
 | .ret false => let l := neg (.ret false); [(l,l,l)]
 | q@(.ask i y n) => [(neg q,(.inl i,false),pos y),(neg q,(.inl i,true),pos n)] ++ gates y ++ gates n
def litOK (a : Key → Bool) (l : Lit) := a l.1 = l.2
def ok (a : Key → Bool) (t : Triple) := litOK a t.1 ∨ litOK a t.2.1 ∨ litOK a t.2.2
def extA (a : Nat → Bool) : Key → Bool := Sum.elim a (Q.run a)
theorem gate_ok (a) (q : Q Bool) : ∀ t ∈ gates q, ok (extA a) t := by
 induction q with
 | ret x => cases x <;> simp [gates,ok,litOK,neg,extA,Q.run]
 | ask i y n hy hn =>
   simp only [gates,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_const]
   intro t ht; rcases ht with ((rfl|rfl)|h)|h
   · cases e : a i <;> simp [ok,litOK,neg,pos,extA,Q.run,e]
   · cases e : a i <;> simp [ok,litOK,neg,pos,extA,Q.run,e]
   · exact hy _ h
   · exact hn _ h
theorem gate_sound (a : Key → Bool) (q : Q Bool) (h : ∀ t ∈ gates q, ok a t) (active : a (.inr q) = true) : q.run (a ∘ Sum.inl) = true := by
 induction q with
 | ret x => cases x <;> simp_all [gates,ok,litOK,neg,Q.run]
 | ask i y n hy hn =>
   simp only [gates,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
   cases e : a (.inl i) <;> simp only [Q.run,Function.comp_apply,e,Bool.false_eq_true,if_false,if_true]
   · apply hn (fun _ ht => h _ (Or.inr ht)); simpa [ok,litOK,neg,pos,active,e] using h _ (Or.inl (Or.inl (Or.inr rfl)))
   · apply hy (fun _ ht => h _ (Or.inl (Or.inr ht))); simpa [ok,litOK,neg,pos,active,e] using h _ (Or.inl (Or.inl (Or.inl rfl)))
def raw (qs : List (Q Bool)) : List Triple := qs.flatMap fun q => (pos q,pos q,pos q) :: gates q
def keys (ts : List Triple) := ts.flatMap fun t => [t.1.1,t.2.1.1,t.2.2.1]
def encode (ts : List Triple) : Formula :=
 let ks := keys ts
 let lit := fun l : Lit => (⟨⟨ks.idxOf l.1, Nat.lt_succ_of_le (List.idxOf_le_length ..)⟩,l.2⟩ : Literal (ks.length+1))
 ⟨_,ts.map fun t => #v[lit t.1,lit t.2.1,lit t.2.2]⟩
theorem enc_correct (ts : List Triple) : (encode ts).Satisfiable ↔ ∃ a, ∀ t ∈ ts, ok a t := by
 classical
 let ks := keys ts
 let idx := fun k : Key => (⟨ks.idxOf k,Nat.lt_succ_of_le (List.idxOf_le_length ..)⟩ : Fin (ks.length+1))
 have ev (a : Fin (ks.length+1) → Bool) : (∀ c ∈ (encode ts).clauses, c.eval a = true) ↔ ∀ t ∈ ts, ok (a ∘ idx) t := by
   unfold encode; dsimp only; rw [List.forall_mem_map]
   apply forall_congr'; intro t; apply forall_congr'; intro _
   rcases t with ⟨⟨i,b⟩,⟨j,c⟩,⟨k,d⟩⟩; cases b <;> cases c <;> cases d <;> simp [Clause.eval,Literal.eval,ok,litOK,idx,ks,or_assoc]
 constructor
 · rintro ⟨a,h⟩; exact ⟨_,(ev a).mp h⟩
 · rintro ⟨a,h⟩; let b := fun i : Fin (ks.length+1) => (ks[i.val]?).elim false a
   refine ⟨b,(ev b).mpr ?_⟩
   have eqv (k : Key) (hk : k ∈ ks) : (b ∘ idx) k = a k := by simp [b,idx,List.getElem?_idxOf hk]
   intro t ht; have mem (k : Key) (hh : k ∈ [t.1.1,t.2.1.1,t.2.2.1]) : k ∈ ks := List.mem_flatMap.mpr ⟨t,ht,hh⟩
   simpa only [ok,litOK,eqv _ (mem t.1.1 (by simp)),eqv _ (mem t.2.1.1 (by simp)),eqv _ (mem t.2.2.1 (by simp))] using h t ht
def compile (qs : List (Q Bool)) := encode (raw qs)
theorem compile_correct (qs : List (Q Bool)) : (compile qs).Satisfiable ↔ ∃ a, ∀ q ∈ qs, q.run a = true := by
 rw [compile,enc_correct]; constructor
 · rintro ⟨a,h⟩; refine ⟨a ∘ Sum.inl,fun q hq => gate_sound _ _ (fun t ht => h _ (List.mem_flatMap.mpr ⟨q,hq,List.mem_cons_of_mem _ ht⟩)) ?_⟩
   simpa [ok,litOK,pos] using h _ (List.mem_flatMap.mpr ⟨q,hq,List.mem_cons_self ..⟩)
 · rintro ⟨a,h⟩; refine ⟨extA a,fun t ht => ?_⟩; obtain ⟨q,hq,hm⟩ := List.mem_flatMap.mp ht
   rcases List.mem_cons.mp hm with rfl|hh
   · simp [ok,litOK,pos,extA,h q hq]
   · exact gate_ok a q t hh
end Window
end

-- Local
section
namespace Compact.Local
open Turing TM2
variable {K : Type} [DecidableEq K] {G : K → Type} {L S : Type}
abbrev Stacks (G : K → Type) := (k : K) → List (G k)
def join (a b : Stacks G) : Stacks G := fun k => a k ++ b k
def extend (c : Cfg G L S) (b : Stacks G) : Cfg G L S := {c with stk := join c.stk b}
def depth : Stmt G L S → Nat
 | .push _ _ q | .load _ q => depth q
 | .pop _ _ q | .peek _ _ q => depth q + 1
 | .branch _ p q => max (depth p) (depth q)
 | .goto _ | .halt => 0
private theorem upd (a b : Stacks G) (k : K) (xs : List (G k)) :
 Function.update (join a b) k (xs ++ b k) = join (Function.update a k xs) b := by
 funext j; by_cases h : j = k
 · subst j; simp [join]
 · simp [join,h]
private theorem hd {A} (a b : List A) (h : b = [] ∨ 0 < a.length) : (a++b).head? = a.head? := by rcases h with h|h; simp [h]; cases a <;> simp_all
private theorem tl {A} (a b : List A) (h : b = [] ∨ 0 < a.length) : (a++b).tail = a.tail ++ b := by rcases h with h|h; simp [h]; cases a <;> simp_all
theorem locality (q : Stmt G L S) (v : S) (a b : Stacks G) (h : ∀ k, b k = [] ∨ depth q ≤ (a k).length) :
 stepAux q v (join a b) = extend (stepAux q v a) b := by
 induction q generalizing v a with
 | goto | halt => rfl
 | load _ q ih => exact ih _ _ h
 | branch f p q ih jh =>
   cases e : f v <;> simp only [stepAux,e,cond_false,cond_true] <;> first | apply ih | apply jh
   all_goals intro k; specialize h k; simp [depth] at h; tauto
 | push k f q ih =>
   simp only [stepAux]; rw [show f v :: join a b k = (f v :: a k) ++ b k from rfl,upd]; apply ih
   intro j; by_cases e : j = k
   · subst j; simpa [depth] using (h k).imp_right (fun t => Nat.le_trans t (Nat.le_succ _))
   · simpa [e,depth] using h j
 | peek k f q ih =>
   have H := (h k).imp_right (fun t => Nat.zero_lt_of_lt (Nat.lt_of_succ_le t))
   simp only [stepAux, show (join a b k).head? = (a k).head? from hd _ _ H]; apply ih
   intro j; exact (h j).imp_right (fun t => Nat.le_of_succ_le t)
 | pop k f q ih =>
   have H := (h k).imp_right (fun t => Nat.zero_lt_of_lt (Nat.lt_of_succ_le t))
   simp only [stepAux, show (join a b k).head? = (a k).head? from hd _ _ H, show (join a b k).tail = (a k).tail ++ b k from tl _ _ H,upd]; apply ih
   intro j; by_cases e : j = k
   · subst j; simp; apply (h k).imp_right; simp [depth]; omega
   · simpa [e] using (h j).imp_right (fun t => Nat.le_of_succ_le t)
theorem truncate_step (q : Stmt G L S) (v : S) (s : Stacks G) (D : Nat) (hD : depth q ≤ D) :
 stepAux q v s = extend (stepAux q v (fun k => (s k).take D)) (fun k => (s k).drop D) := by
 have e := locality q v (fun k => (s k).take D) (fun k => (s k).drop D) (by
   intro k; by_cases h : (s k).length ≤ D
   · exact Or.inl (List.drop_eq_nil_of_le h)
   · right; simp; omega)
 have hj : join (fun k => (s k).take D) (fun k => (s k).drop D) = s := by
   funext k; exact List.take_append_drop _ _
 rw [hj] at e; exact e
end Compact.Local
end

-- Symbolic
section
/- Symbolic execution of one bounded local transition. -/
namespace Window
open Turing TM2
abbrev Tape (M : FinTM2) := (k : M.K) → Nat → Q (Option (M.Γ k))
structure View (M : FinTM2) where
 l : Option M.Λ
 v : M.σ
 s : Tape M
variable {M : FinTM2}
def sstep (q : Stmt M.Γ M.Λ M.σ) (v : M.σ) (s : Tape M) : Q (View M) := match q with
 | .push k f p => sstep p v (Function.update s k (fun | 0 => .ret (some (f v)) | i+1 => s k i))
 | .peek k f p => (s k 0).seq fun x => sstep p (f v x) s
 | .pop k f p => (s k 0).seq fun x => sstep p (f v x) (Function.update s k (fun i => s k (i+1)))
 | .load f p => sstep p (f v) s
 | .branch f p r => if f v then sstep p v s else sstep r v s
 | .goto f => .ret ⟨some (f v),v,s⟩
 | .halt => .ret ⟨none,v,s⟩
def agrees (a : Nat → Bool) (s : Tape M) (c : Compact.Local.Stacks M.Γ) (n : Nat) := ∀ k i, i < n → (s k i).run a = (c k)[i]?
def matchV (a) (r : View M) (c : M.Cfg) (n) := r.l = c.l ∧ r.v = c.var ∧ agrees a r.s c.stk n
theorem shrink {a s c n m} (h : @agrees M a s c n) (le : m ≤ n) : agrees a s c m := fun k i hi => h k i (lt_of_lt_of_le hi le)
private theorem z {α} (l : List α) : l[0]? = l.head? := by cases l <;> rfl
open Compact.Local in
theorem step_correct (a) (q : Stmt M.Γ M.Λ M.σ) (v s c n) (h : agrees a s c (n + depth q)) : matchV a ((sstep q v s).run a) (stepAux q v c) n := by
 induction q generalizing s c v with
 | goto | halt => exact ⟨rfl,rfl,h⟩
 | load f p ih => exact ih _ _ _ h
 | branch f p r ih jh =>
   cases e : f v <;> simp [sstep,stepAux,e] <;> first | apply ih | apply jh
   all_goals apply shrink h; simp [depth]
 | push k f p ih =>
   apply ih; intro j i hi; by_cases hj : j = k
   · subst j; cases i with
     | zero => simp [Q.run]
     | succ i => simpa using h k i (by simpa [depth] using (Nat.lt_trans (Nat.lt_succ_self _) hi))
   · simpa [hj] using h j i hi
 | peek k f p ih =>
   have hh := h k 0 (by simp [depth]); simp [sstep,hh,z,stepAux] at *; apply ih; apply shrink h; simp [depth]
 | pop k f p ih =>
   have hh := h k 0 (by simp [depth]); simp only [z] at hh
   simp only [sstep,Q.run_seq,hh,stepAux]; apply ih; intro j i hi; by_cases hj : j = k
   · subst j; simpa [List.getElem?_tail] using h k (i+1) (by simp [depth]; omega)
   · simpa [hj] using h j i (by simp [depth]; omega)
def tick (M : FinTM2) (c : M.Cfg) : M.Cfg := match c.l with
 | none => c
 | some l => stepAux (M.m l) c.var c.stk
def next (r : View M) : Q (View M) := match r.l with
 | none => .ret r
 | some l => sstep (M.m l) r.v r.s
noncomputable def loss (M : FinTM2) := @Finset.univ M.Λ M.ΛFin |>.sup fun l => Compact.Local.depth (M.m l)
theorem next_correct (a) (r : View M) (c n) (h : matchV a r c (n+loss M)) : matchV a ((next r).run a) (tick M c) n := by
 letI := M.ΛFin
 obtain ⟨hl,hv,hs⟩ := h; cases e : c.l with
 | none => simp only [next,hl,e,Q.run,tick]; exact ⟨hl,hv,shrink hs (by omega)⟩
 | some l => simp only [next,hl,e,tick,hv]; apply step_correct; apply shrink hs; apply Nat.add_le_add_left; exact Finset.le_sup (f := fun l => Compact.Local.depth (M.m l)) (Finset.mem_univ l)
end Window
end

-- Rows
section
namespace Window
open Turing TM2
noncomputable section
abbrev Slot := Nat × Nat × Nat × Nat
def addr (s : Slot) (i : Nat) := Encodable.encode (s,i)
def writer (f : Slot → Nat) (n : Nat) := (((Encodable.decode n : Option (Slot × Nat))).map fun p => decide (f p.1 = p.2)).getD false
@[simp] theorem writer_addr (f s i) : writer f (addr s i) = decide (f s = i) := by simp only [writer,addr,Encodable.encodek,Option.map_some,Option.getD_some]
def pick (s : Slot) (code : α → Nat) (d : α) : List α → Q α
 | [] => .ret d
 | x::xs => .ask (addr s (code x)) (.ret x) (pick s code d xs)
theorem pick_hit (f : Slot → Nat) (s) (code : α → Nat) (inj : Function.Injective code) (d x) (xs : List α) (hx : x ∈ xs) (hf : f s = code x) : (pick s code d xs).run (writer f) = x := by
 induction xs with
 | nil => simp at hx
 | cons y ys ih =>
   by_cases e : x = y
   · subst y; simp [pick,Q.run,hf]
   · simp [pick,Q.run,hf,inj.eq_iff,e,ih (List.mem_cons.mp hx |>.resolve_left e)]
def num [Fintype α] (x : α) : Nat := (Fintype.equivFin α x).val
def all (α) [Fintype α] := List.ofFn (Fintype.equivFin α).symm
@[simp] theorem mem_all [Fintype α] (x : α) : x ∈ all α := by exact List.mem_ofFn.mpr ⟨_,(Fintype.equivFin α).symm_apply_apply x⟩
def readVal [Fintype α] (s : Slot) (d : α) := pick s num d (all α)
theorem read_hit [Fintype α] (f : Slot → Nat) (s) (d x : α) (h : f s = num x) : (readVal s d).run (writer f) = x := pick_hit f s _ ((Fin.val_injective).comp (Fintype.equivFin α).injective) _ _ _ (mem_all x) h
variable (M : FinTM2) [A : ∀ k, Fintype (M.Γ k)]
local instance kFinI1 (M : Turing.FinTM2) : Fintype M.K := M.kFin
local instance ΛFinI1 (M : Turing.FinTM2) : Fintype M.Λ := M.ΛFin
local instance σFinI1 (M : Turing.FinTM2) : Fintype M.σ := M.σFin
def row (t : Nat) : Q (View M) := (readVal (2,t,0,0) (none : Option M.Λ)).seq fun l => (readVal (3,t,0,0) M.initialState).seq fun v => .ret ⟨l,v,fun k i => readVal (4,t,num k,i) none⟩
def store (cs : Nat → M.Cfg) (w : List Bool) : Slot → Nat
 | (0,_,_,_) => w.length
 | (1,_,_,i) => if w[i]?.getD false then 1 else 0
 | (2,t,_,_) => num (cs t).l
 | (3,t,_,_) => num (cs t).var
 | (4,t,k,i) => if h : k < Fintype.card M.K then let j := (Fintype.equivFin M.K).symm ⟨k,h⟩; num ((cs t).stk j)[i]? else 0
 | _ => 0
theorem row_hit (cs w t n) : matchV (writer (store M cs w)) ((row M t).run (writer (store M cs w))) (cs t) n := by
 let f := store M cs w
 have hl := read_hit f (2,t,0,0) none (cs t).l rfl
 have hv := read_hit f (3,t,0,0) M.initialState (cs t).var rfl
 simp only [row,Q.run_seq,Q.run]; refine ⟨hl,hv,?_⟩; intro k i _
 apply read_hit; simp [store,num]; exact congrArg (fun j : M.K => num ((cs t).stk j)[i]?) ((Fintype.equivFin M.K).symm_apply_apply k)
def same [DecidableEq α] (x y : Q α) : Q Bool := x.seq fun u => y.seq fun v => .ret (decide (u=v))
@[simp] theorem same_run [DecidableEq α] (x y : Q α) (a) : (same x y).run a = true ↔ x.run a = y.run a := by simp [same,Q.run]
def field (x : Q (View M)) (f : View M → α) := x.seq fun c => .ret (f c)
def cell (x : Q (View M)) (k i) := x.seq fun c => c.s k i
def equalRows (x y : Q (View M)) (b : Nat) : List (Q Bool) := by classical exact
 [same (field M x View.l) (field M y View.l),same (field M x View.v) (field M y View.v)] ++ (all M.K).flatMap fun k => (List.range b).map fun i => same (cell M x k i) (cell M y k i)
theorem equal_spec (x y : Q (View M)) (a b) : (∀ q ∈ equalRows M x y b, q.run a = true) ↔
 (x.run a).l = (y.run a).l ∧ (x.run a).v = (y.run a).v ∧ ∀ k i, i < b → ((x.run a).s k i).run a = ((y.run a).s k i).run a := by
 classical
 unfold equalRows
 rw [List.forall_mem_append]; simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true,List.forall_mem_flatMap,List.forall_mem_map,mem_all,true_implies,List.mem_range,same_run,field,cell,Q.run_seq,Q.run,and_assoc]
theorem equal_transfer (x y : Q (View M)) (a b c) (hx : matchV a (x.run a) c b) : (∀ q ∈ equalRows M x y b, q.run a = true) ↔ matchV a (y.run a) c b := by
 rw [equal_spec]; unfold matchV agrees at *; obtain ⟨hl,hv,hs⟩ := hx; constructor <;> rintro ⟨ll,vv,ss⟩ <;> refine ⟨by grind,by grind,fun k i hi => ?_⟩ <;> specialize hs k i hi <;> specialize ss k i hi <;> grind
end
end Window
end

-- Input
section
namespace Window
open Turing OAI.BinPackingGames.Foundations Complexity CookLevin
noncomputable section
variable (V : NPVerifier) (x : List Bool)
abbrev tm := V.computation.tm
abbrev bound := V.witnessBound.eval x.length
def sizeQ : Q (Fin (bound V x + 1)) := pick (0,0,0,0) Fin.val 0 (List.finRange _)
def bits (n : Nat) : List (Q Bool) := (List.range n).map fun i => .ask (addr (1,0,0,i) 1) (.ret true) (.ret false)
def witness (a) := (bits ((sizeQ V x).run a).val).map (Q.run a)
theorem witness_le (a) : (witness V x a).length ≤ bound V x := by simp [witness,bits]; exact Nat.le_of_lt_succ ((sizeQ V x).run a).isLt
local instance : ∀ k, Fintype ((tm V).Γ k) := V.finiteAlphabet
theorem witness_hit (cs w) (h : w.length ≤ bound V x) : witness V x (writer (store (tm V) cs w)) = w := by
 let n : Fin (bound V x+1) := ⟨w.length,by omega⟩
 have hh : (sizeQ V x).run (writer (store (tm V) cs w)) = n := pick_hit _ _ _ Fin.val_injective _ n _ (by simp) rfl
 apply List.ext_getElem <;> simp [witness,hh,bits,n,Q.run,store,List.getElem?_eq_getElem] <;> intros <;> simp_all [List.getElem?_eq_getElem]
def inputQ (w : List (Q Bool)) := ((encodeWord x.length ++ x).map Q.ret) ++ w
def optQ : Option (Q α) → Q (Option α)
 | none => .ret none
 | some q => q.seq fun z => .ret (some z)
theorem getQ (l : List (Q α)) (i : Nat) (a) : (optQ l[i]?).run a = (l.map (Q.run a))[i]? := by simp [List.getElem?_map]; cases l[i]? <;> simp [optQ,Q.run]
def initView (w : List (Q Bool)) : View (tm V) where
 l := some (tm V).main
 v := (tm V).initialState
 s k i := if e : k = (tm V).k₀ then e.symm ▸ ((optQ (inputQ x w)[i]?).seq fun b => .ret (b.map V.computation.inputAlphabet.invFun)) else .ret none
def start := (sizeQ V x).seq fun n => Q.ret (initView V x (bits n.val))
def initial (w) := initList (tm V) ((pairBits (x,w)).map V.computation.inputAlphabet.invFun)
theorem start_match (a n) : matchV a ((start V x).run a) (initial V x (witness V x a)) n := by
 simp only [start,Q.run_seq,Q.run]; refine ⟨rfl,rfl,?_⟩; intro k i _; by_cases e : k = (tm V).k₀
 · subst k; simp [initView,initial,initList,getQ,Q.run,inputQ,witness,pairBits,List.map_append,List.map_map,Function.comp_def,List.append_assoc]; rw [← List.getElem?_map]; simp [List.map_append,List.map_map,Function.comp_def]
 · simp [initView,initial,initList,e,Q.run]
def hist (w) (t : Nat) := (tick (tm V))^[t] (initial V x w)
private theorem none_iter (M : FinTM2) (n : Nat) : (flip Bind.bind M.step)^[n] (none : Option M.Cfg) = none := by
 induction n with
 | zero => rfl
 | succ n ih => exact ih
private theorem tick_iter (M : FinTM2) (n : Nat) (c d : M.Cfg) (h : (flip Bind.bind M.step)^[n] (some c) = some d) : (tick M)^[n] c = d := by
 induction n generalizing c with
 | zero => simpa using h
 | succ n ih =>
   rw [Function.iterate_succ_apply] at h ⊢; rcases c with ⟨l,v,s⟩; cases l with
   | none => change (flip Bind.bind M.step)^[n] none = some d at h; rw [none_iter] at h; contradiction
   | some l => exact ih _ h
abbrev horizon := V.horizon x.length
def finish (b : Bool) := haltList (tm V) [V.computation.outputAlphabet.invFun b]
private theorem monoP (p : Polynomial Nat) {i j : Nat} (h : i ≤ j) : p.eval i ≤ p.eval j := by
 induction p using Polynomial.induction_on' with
 | add _ _ ha hb => simpa using Nat.add_le_add ha hb
 | monomial n c => simp only [Polynomial.eval_monomial]; gcongr
theorem hist_last (w) (hw : w.length ≤ bound V x) : hist V x w (horizon V x) = finish V (V.verify (x,w)) := by
 let o := V.computation.outputsFun (x,w)
 have e := tick_iter _ o.steps _ _ o.evals_in_steps
 have hn : o.steps ≤ horizon V x := o.steps_le_m.trans (monoP _ (by change (pairBits (x,w)).length ≤ 2*x.length+bound V x+1; simp [pairBits,encodeWord]; omega))
 obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hn
 unfold hist; rw [hj,Nat.add_comm,Function.iterate_add_apply]; change (tick (tm V))^[j] ((tick (tm V))^[o.steps] _) = _
 rw [show (tick (tm V))^[o.steps] (initial V x w) = finish V (V.verify (x,w)) from e]
 exact Function.iterate_fixed (f := tick (tm V)) (by rfl) j
end
end Window
end

-- Tableau
section
/- Direct bounded-window reduction for the OpenAI NPVerifier API. See LICENSE.openai. -/
namespace Window
open Turing OAI.BinPackingGames.Foundations Complexity CookLevin
noncomputable section
variable (V : NPVerifier) (x : List Bool)
local instance : ∀ k, Fintype ((tm V).Γ k) := V.finiteAlphabet
def width (t : Nat) := (horizon V x - t) * loss (tm V) + 1
def trans (t : Nat) := equalRows (tm V) ((row (tm V) t).seq next) (row (tm V) (t+1)) (width V x (t+1))
def out := by classical exact same (cell (tm V) (row (tm V) (horizon V x)) (tm V).k₁ 0) (.ret (some (V.computation.outputAlphabet.invFun true)))
def tests := equalRows (tm V) (start V x) (row (tm V) 0) (width V x 0) ++ ((List.range (horizon V x)).flatMap (trans V x) ++ [out V x])
def formula := compile (tests V x)
def Good (a : Nat → Bool) (t : Nat) := matchV a ((row (tm V) t).run a) (hist V x (witness V x a) t) (width V x t)
private theorem trans_good (a t) (ht : t < horizon V x) (g : Good V x a t) : (∀ q ∈ trans V x t, q.run a = true) ↔ Good V x a (t+1) := by
 apply equal_transfer; rw [Q.run_seq]; unfold hist; rw [Function.iterate_succ_apply']; apply next_correct
 have eqw : width V x (t+1) + loss (tm V) = width V x t := by
   unfold width; rw [show horizon V x-t = (horizon V x-(t+1))+1 by omega,Nat.add_mul]; omega
 rwa [eqw]
private theorem out_good (a) (g : Good V x a (horizon V x)) : (out V x).run a = true ↔ V.verify (x,witness V x a) = true := by
 have hh := g.2.2 (tm V).k₁ 0 (by simp [width]); rw [hist_last _ _ _ (witness_le ..)] at hh
 simp only [finish,haltList,dif_pos rfl,List.getElem?_cons_zero] at hh
 simpa [out,cell,Q.run,hh] using (show _ ↔ _ from (Iff.rfl : V.verify (x,witness V x a) = true ↔ _))
theorem correct (V : NPVerifier) (x : List Bool) : V.Accepts x ↔ (formula V x).Satisfiable := by
 rw [formula,compile_correct]; constructor
 · rintro ⟨w,hw,hv⟩
   let cs := hist V x w
   let a := writer (store (tm V) cs w)
   have he : witness V x a = w := witness_hit V x cs w hw
   have g (t) : Good V x a t := by unfold Good; rw [he]; exact row_hit _ cs w t _
   refine ⟨a,?_⟩; unfold tests; rw [List.forall_mem_append,List.forall_mem_append,List.forall_mem_flatMap]; refine ⟨(equal_transfer _ _ _ _ _ _ (start_match ..)).mpr (g 0),?_,?_⟩
   · intro t ht; exact (trans_good V x a t (List.mem_range.mp ht) (g t)).mpr (g _)
   · simpa using (out_good V x a (g _)).mpr (he ▸ hv)
 · rintro ⟨a,h⟩; unfold tests at h; rw [List.forall_mem_append,List.forall_mem_append,List.forall_mem_flatMap] at h
   have g (t) (ht : t ≤ horizon V x) : Good V x a t := by
     induction t with
     | zero => exact (equal_transfer _ _ _ _ _ _ (start_match ..)).mp h.1
     | succ t ih => exact (trans_good _ _ _ _ (by omega) (ih (by omega))).mp (h.2.1 _ (List.mem_range.mpr (by omega)))
   exact ⟨_,witness_le ..,(out_good _ _ _ (g _ le_rfl)).mp (h.2.2 _ (by simp))⟩
end
end Window
end

-- Numbered
section
/- Independent streaming tableau numbering for the OpenAI verifier API. See LICENSE.openai. -/
namespace Window.Stream
open OAI.BinPackingGames.Foundations Target Complexity
abbrev L := Nat × Bool
abbrev T := L × L × L
def holds (a : Nat → Bool) (t : T) := a t.1.1 = t.1.2 ∨ a t.2.1.1 = t.2.1.2 ∨ a t.2.2.1 = t.2.2.2
def nodes : Q Bool → List (Q Bool)
 | q@(.ret _) => [q]
 | q@(.ask _ y n) => q :: nodes y ++ nodes n
def gate (i : Nat) (b : Bool) : L := (2*i+1,b)
def inp (i : Nat) (b : Bool) : L := (2*i,b)
def unit (l : L) : T := (l,l,l)
def body (i : Nat) : Q Bool → List T
 | .ret true => []
 | .ret false => [unit (gate i false)]
 | .ask j y n => [(gate i false,inp j false,gate (i+1) true), (gate i false,inp j true,gate (i+1+(nodes y).length) true)] ++ body (i+1) y ++ body (i+1+(nodes y).length) n
def forest (i : Nat) : List (Q Bool) → List T
 | [] => []
 | q :: qs => unit (gate i true) :: body i q ++ forest (i+(nodes q).length) qs
def on (a : Nat → Bool) (i : Nat) (ns : List (Q Bool)) := ∀ j q, ns[j]? = some q → a (2*(i+j)+1) = q.run (fun k => a (2*k))
private theorem splitOn {a i xs ys} (h : on a i (xs++ys)) : on a i xs ∧ on a (i+xs.length) ys := by
 constructor
 · intro j q hj; apply h; rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj).1]
   exact hj
 · intro j q hj; rw [Nat.add_assoc]; apply h; simp [List.getElem?_append_right,hj]
private theorem consOn {a i q ns} (h : on a i (q::ns)) : a (2*i+1) = q.run (fun k => a (2*k)) ∧ on a (i+1) ns := by
 refine ⟨by simpa using h 0 q rfl, ?_⟩; intro j p hp; simpa [Nat.add_assoc,Nat.add_comm 1 j] using h (j+1) p hp
private theorem rootOn {a i q} (h : on a i (nodes q)) : a (2*i+1) = q.run (fun k => a (2*k)) := by cases q <;> exact (consOn h).1
theorem completeBody (a i q) (h : on a i (nodes q)) : ∀ t ∈ body i q, holds a t := by
 induction q generalizing i with
 | ret b => cases b <;> simp_all [body,unit,gate,holds,rootOn h,Q.run]
 | ask j y n hy hn =>
   obtain ⟨hr,hs⟩ := consOn h; obtain ⟨sy,sn⟩ := splitOn hs
   simp only [body,List.forall_mem_append,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
   refine ⟨⟨⟨?_,?_⟩,hy _ sy⟩, hn _ sn⟩ <;> cases e : a (2*j) <;> simp [holds,gate,inp,hr,Q.run,e,rootOn sy,rootOn sn]

theorem soundBody (a i q) (h : ∀ t ∈ body i q, holds a t) (act : a (2*i+1) = true) : q.run (fun k => a (2*k)) = true := by
 induction q generalizing i with
 | ret b => cases b <;> simp_all [body,holds,unit,gate,Q.run]
 | ask j y n hy hn =>
   simp only [body,List.forall_mem_append,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true] at h
   cases e : a (2*j) <;> simp [Q.run,e]
   · apply hn _ h.2; simpa [holds,gate,inp,act,e] using h.1.1.2
   · apply hy _ h.1.2; simpa [holds,gate,inp,act,e] using h.1.1.1

theorem forest_iff (qs : List (Q Bool)) : (∃ a, ∀ t ∈ forest 0 qs, holds a t) ↔ ∃ b, ∀ q ∈ qs, q.run b = true := by
 constructor
 · rintro ⟨a,h⟩; refine ⟨fun j => a (2*j),?_⟩; generalize ei : 0 = i at h; clear ei
   induction qs generalizing i with
   | nil => simp
   | cons q qs ih =>
     simp only [forest,List.forall_mem_cons,List.forall_mem_append] at h
     exact List.forall_mem_cons.mpr ⟨soundBody _ _ _ h.1.2 (by simpa [holds,unit,gate] using h.1.1),ih _ h.2⟩
 · rintro ⟨b,h⟩
   let ns := qs.flatMap nodes
   let a := fun i : Nat => if i%2=0 then b (i/2) else (ns[i/2]?).elim false (Q.run b)
   have he (j) : a (2*j) = b j := by simp [a]
   have hn : on a 0 ns := by intro j q hj; simp [a,show (2*j+1)/2=j by omega,hj,he]
   refine ⟨a,?_⟩; change on a 0 (qs.flatMap nodes) at hn
   generalize ei : 0 = i at hn ⊢; clear ei; clear_value a; clear ns; induction qs generalizing i with
   | nil => simp [forest]
   | cons q qs ih =>
     obtain ⟨hy,hs⟩ := splitOn hn
     simp only [forest,List.forall_mem_cons,List.forall_mem_append]; refine ⟨⟨?_,completeBody _ _ _ hy⟩,ih (fun p hp => h p (.tail _ hp)) _ hs⟩
     simp [holds,unit,gate,rootOn hy,he,h q (.head _)]

def span (t : T) := t.1.1 + t.2.1.1 + t.2.2.1
abbrev limit (ts : List T) := (ts.map span).sum+1
def mkLit (v : Nat) (l : L) : Literal (v+1) := ⟨⟨min l.1 v,by omega⟩,l.2⟩
def pack (ts : List T) : Formula := ⟨limit ts, ts.map fun t => #v[mkLit _ t.1,mkLit _ t.2.1,mkLit _ t.2.2]⟩
private theorem leSum (t : T) (ts : List T) (h : t ∈ ts) : span t ≤ (ts.map span).sum := by induction ts with | nil => simp at h | cons s ss ih => rcases List.mem_cons.mp h with rfl|hh <;> simp <;> first | omega | exact (ih hh).trans (Nat.le_add_left ..)
private theorem bounds (t : T) (ts : List T) (h : t ∈ ts) : t.1.1 ≤ (ts.map span).sum ∧ t.2.1.1 ≤ (ts.map span).sum ∧ t.2.2.1 ≤ (ts.map span).sum := by have := leSum _ _ h; change t.1.1+t.2.1.1+t.2.2.1 ≤ _ at this; omega
private theorem evalPack (ts : List T) (a : Nat → Bool) : (∀ c ∈ (pack ts).clauses, c.eval (fun i => a i.val) = true) ↔ ∀ t ∈ ts, holds a t := by
 unfold pack; dsimp only; rw [List.forall_mem_map]; apply forall_congr'; intro t; apply forall_congr'; intro ht
 obtain ⟨hu,hv,hw⟩ := bounds _ _ ht
 rcases t with ⟨⟨u,p⟩,⟨v,q⟩,⟨w,r⟩⟩; cases p <;> cases q <;> cases r <;> simp_all [Clause.eval,Literal.eval,mkLit,holds,or_assoc,min_eq_left]
theorem pack_iff (ts : List T) : (pack ts).Satisfiable ↔ ∃ a, ∀ t ∈ ts, holds a t := by
 constructor
 · rintro ⟨a,h⟩; let b := fun j : Nat => a ⟨min j ((ts.map span).sum),by change _ < (ts.map span).sum+1; omega⟩; refine ⟨b,(evalPack _ _).mp ?_⟩
   have he (i : Fin (limit ts)) : b i.val = a i := by unfold b; apply congrArg a; apply Fin.ext; exact min_eq_left (Nat.le_of_lt_succ i.isLt)
   have e : (fun i : Fin (limit ts) => b i.val) = a := funext he
   exact e.symm ▸ h
 · rintro ⟨a,h⟩; exact ⟨_,(evalPack _ _).mpr h⟩
def words (t : T) := [t.1.1,if t.1.2 then 1 else 0,t.2.1.1,if t.2.1.2 then 1 else 0,t.2.2.1,if t.2.2.2 then 1 else 0]
theorem pack_words (ts : List T) : formulaWords (pack ts) = [limit ts,ts.length] ++ ts.flatMap words := by
 simp only [formulaWords,pack,List.length_map,List.flatMap_map]; congr 1
 apply List.flatMap_congr; intro t ht; obtain ⟨ha,hb,hc⟩ := bounds _ _ ht
 simp [Function.comp_def,clauseWords,literalWords,mkLit,words,min_eq_left ha,min_eq_left hb,min_eq_left hc]
noncomputable def formula' (V x) := pack (forest 0 (tests V x))
theorem equiv_formula (V x) : (formula' V x).Satisfiable ↔ (Window.formula V x).Satisfiable := by rw [formula',pack_iff,forest_iff,Window.formula,compile_correct]
end Window.Stream
end

-- ClauseReg
section
/- Register back end for numbered tableau clauses. See LICENSE.openai. -/
namespace Window.Stream
open Compact.Reg
variable {K : Type} [DecidableEq K]
private theorem iterInc (x : List Bool) (r : K) (s : S K) (n : Nat) : (fun t => ((P.inc r).exec x t).tick 1)^[n] s = ⟨Function.update s.reg r (s.reg r+n),s.words,s.work+2*n⟩ := by
 induction n with
 | zero => simp [Function.update_eq_self]
 | succ n ih => rw [Function.iterate_succ_apply',ih]; simp [P.exec,S.tick,S.put,Function.update_idem,Nat.mul_succ,Nat.add_assoc]

def accumulate (dst src : K) : P K := .repeatN src (.inc dst)
theorem accumulate_exec (dst src : K) (x) (s : S K) : (accumulate dst src).exec x s = ⟨Function.update s.reg dst (s.reg dst+s.reg src),s.words,s.work+1+3*s.reg src⟩ := by
 unfold accumulate; rw [P.exec,iterInc]; simp only [S.tick]; congr 1; omega

inductive Pass | header | data
structure Ports (K : Type) where
 sum : K
 count : K
 z : K
 one : K

def regClause (p : Ports K) (phase : Pass) (u v w : K × Bool) : P K :=
 let bit := fun (b : Bool) => if b then p.one else p.z
 let lit := fun l : K × Bool => P.seq (.emit l.1) (.emit (bit l.2))
 match phase with
 | .header => .seq (accumulate p.sum u.1) (.seq (accumulate p.sum v.1) (.seq (accumulate p.sum w.1) (.inc p.count)))
 | .data => .seq (lit u) (.seq (lit v) (lit w))
def evalReg (s : S K) (u : K × Bool) : L := (s.reg u.1,u.2)
theorem regClause_data (x) (s : S K) (p : Ports K) (hz : s.reg p.z = 0) (ho : s.reg p.one = 1) (u v w : K × Bool) :
 let t := (evalReg s u,evalReg s v,evalReg s w)
 let s' := (regClause p .data u v w).exec x s
 s'.reg = s.reg ∧ s'.words = s.words ++ words t ∧ s'.work ≤ s.work + span t + 9 := by
 rcases u with ⟨u,b⟩; rcases v with ⟨v,c⟩; rcases w with ⟨w,d⟩; cases b <;> cases c <;> cases d <;> simp [regClause,P.exec,words,evalReg,span,hz,ho,List.append_assoc] <;> omega

theorem regClause_header (x) (s : S K) (p : Ports K) (u v w : K × Bool)
 (hc : p.count ≠ p.sum) (hv : v.1 ≠ p.sum) (hw : w.1 ≠ p.sum) :
 let t := (evalReg s u,evalReg s v,evalReg s w)
 let s' := (regClause p .header u v w).exec x s
 s'.reg = Function.update (Function.update s.reg p.sum (s.reg p.sum + span t)) p.count (s.reg p.count+1) ∧ s'.words = s.words ∧ s'.work = s.work+4+3*span t := by
 simp [regClause,P.exec,accumulate_exec,Function.update_of_ne hv,Function.update_of_ne hw,Function.update_of_ne hc,Function.update_idem,span,evalReg,S.put,Nat.add_assoc,Nat.mul_add]; omega
end Window.Stream
end

-- IndexReg
section
/- Arithmetic macros for numbered tableau indices. See LICENSE.openai. -/
namespace Window.Stream
open Compact.Reg
variable {K : Type} [DecidableEq K]
def copyReg (d r : K) : P K := .seq (.zero d) (accumulate d r)
theorem copy_exec (x) (s : S K) {d r} (h : r ≠ d) : (copyReg d r).exec x s = ⟨Function.update s.reg d (s.reg r),s.words,s.work+2+s.reg d+3*s.reg r⟩ := by
 simp [copyReg,P.exec,S.put,accumulate_exec,Function.update_of_ne h,Function.update_idem]; omega

def minusReg (d r : K) : P K := .repeatN r (.dec d)
theorem minus_exec (x) (s : S K) (d r : K) : (minusReg d r).exec x s = ⟨Function.update s.reg d (s.reg d - s.reg r),s.words,s.work+1+3*s.reg r⟩ := by
 have aux (t : S K) (n : Nat) : (fun u => ((P.dec d).exec x u).tick 1)^[n] t = ⟨Function.update t.reg d (t.reg d-n),t.words,t.work+2*n⟩ := by
   induction n with
   | zero => simp [Function.update_eq_self]
   | succ n ih => rw [Function.iterate_succ_apply',ih]; simp [P.exec,S.tick,S.put,Function.update_idem,Nat.sub_sub,Nat.mul_succ,Nat.add_assoc]
 unfold minusReg; rw [P.exec,aux]; simp only [S.tick]; congr 1; omega

def maddReg (d a b : K) : P K := .repeatN a (accumulate d b)
theorem madd_exec (x) (s : S K) (d a b : K) (hb : b ≠ d) : (maddReg d a b).exec x s = ⟨Function.update s.reg d (s.reg d+s.reg a*s.reg b),s.words,s.work+1+s.reg a+s.reg a*(2+3*s.reg b)⟩ := by
 have aux (t : S K) (n : Nat) : (fun u => ((accumulate d b).exec x u).tick 1)^[n] t = ⟨Function.update t.reg d (t.reg d+n*t.reg b),t.words,t.work+n*(2+3*t.reg b)⟩ := by
   induction n with
   | zero => simp [Function.update_eq_self]
   | succ n ih => rw [Function.iterate_succ_apply',ih,accumulate_exec]; simp [Function.update_of_ne hb,S.tick,Function.update_idem,Nat.succ_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]; omega
 unfold maddReg; rw [P.exec,aux]; simp [S.tick,Nat.add_assoc]

inductive E (α : Type) where
 | var (a : α) | const (n : Nat) | len | read (i : E α)
 | add (a b : E α) | sub (a b : E α) | mul (a b : E α) | cond (c y n : E α)
namespace E
def val (x : List Bool) (v : α → Nat) : E α → Nat
 | .var a => v a | .const n => n | .len => x.length | .read i => if x[val x v i]?.getD false then 1 else 0
 | .add a b => val x v a + val x v b | .sub a b => val x v a - val x v b | .mul a b => val x v a * val x v b | .cond c a b => if val x v c ≠ 0 then val x v a else val x v b
def pair (a b : E α) := cond (sub b a) (add (mul b b) a) (add (add (mul a a) a) b)
@[simp] theorem val_pair (x v) (a b : E α) : (pair a b).val x v = Nat.pair (a.val x v) (b.val x v) := by simp [pair,val,Nat.pair,Nat.sub_eq_zero_iff_le,not_le]

def addrE (kind t k i tag : E α) : E α := pair (pair kind (pair t (pair k i))) tag
@[simp] theorem val_addrE (x v) (kind t k i tag : E α) : (addrE kind t k i tag).val x v = addr (kind.val x v,t.val x v,k.val x v,i.val x v) (tag.val x v) := by simp [addrE]; rfl
end E
end Window.Stream
end

-- TransitionTree
section
/- Fixed arithmetic decision trees for the numbered tableau. See LICENSE.openai. -/
namespace Window.Stream
inductive Tree (α β : Type) where
 | ret (b : β)
 | ask (e : E α) (yes no : Tree α β)
 | cond (e : E α) (yes no : Tree α β)
namespace Tree
def eval (x : List Bool) (v : α → Nat) : Tree α β → Q β
 | .ret b => .ret b
 | .ask e y n => .ask (e.val x v) (eval x v y) (eval x v n)
 | .cond e y n => if e.val x v ≠ 0 then eval x v y else eval x v n
def bind (q : Tree α β) (f : β → Tree α γ) : Tree α γ := match q with
 | .ret b => f b
 | .ask e y n => .ask e (bind y f) (bind n f)
 | .cond e y n => .cond e (bind y f) (bind n f)
@[simp] theorem eval_bind (x v) (q : Tree α β) (f : β → Tree α γ) :
 eval x v (bind q f) = (eval x v q).seq (fun b => eval x v (f b)) := by
 induction q <;> simp_all [bind,eval,Q.seq] <;> split <;> rfl
end Tree
end Window.Stream
end

-- Plans
section
/- Fixed, bounded iteration over arithmetic tableau tests. See LICENSE.openai. -/
namespace Window.Stream
inductive Plan : Type → Type 1 where
 | empty : Plan α
 | tree (q : Tree α Bool) : Plan α
 | cat (a b : Plan α) : Plan α
 | range (n : E α) (body : Plan (Option α)) : Plan α
 | guard (c : E α) (y n : Plan α) : Plan α
namespace Plan
def eval (x : List Bool) (v : α → Nat) : Plan α → List (Q Bool)
 | .empty => [] | .tree q => [q.eval x v] | .cat a b => eval x v a ++ eval x v b
 | .range n b => (List.range (n.val x v)).flatMap fun j => eval x (fun o => o.elim j v) b
 | .guard c y n => if c.val x v ≠ 0 then eval x v y else eval x v n
end Plan
end Window.Stream
end

-- Lower
section
/- Lower fixed tableau templates to bounded streams of triples. See LICENSE.openai. -/
namespace Window.Stream
namespace E
def rename (f : α → β) : E α → E β
 | .var a => .var (f a) | .const n => .const n | .len => .len | .read i => .read (rename f i)
 | .add a b => .add (rename f a) (rename f b) | .sub a b => .sub (rename f a) (rename f b) | .mul a b => .mul (rename f a) (rename f b) | .cond c y n => .cond (rename f c) (rename f y) (rename f n)
@[simp] theorem val_rename (x) (v : β → Nat) (f : α → β) (e : E α) : (e.rename f).val x v = e.val x (v ∘ f) := by induction e <;> simp_all [rename,val,Function.comp_def]
end E
abbrev EL (α : Type) := E α × Bool
abbrev ET (α : Type) := EL α × EL α × EL α
def EL.eval (x : List Bool) (v : α → Nat) (l : EL α) : L := (l.1.val x v,l.2)
def ET.eval (x : List Bool) (v : α → Nat) (t : ET α) : T := (EL.eval x v t.1,EL.eval x v t.2.1,EL.eval x v t.2.2)
inductive Script : Type → Type 1 where
 | empty : Script α
 | clause (t : ET (Option α)) : Script α
 | advance (n : E α) : Script α
 | cat (a b : Script α) : Script α
 | range (n : E α) (b : Script (Option α)) : Script α
 | guard (c : E α) (y n : Script α) : Script α
structure Fragment where
 size : Nat
 triples : Nat → List T
namespace Fragment
def nil : Fragment := ⟨0,fun _ => []⟩
def join (a b : Fragment) : Fragment := ⟨a.size+b.size, fun i => a.triples i ++ b.triples (i+a.size)⟩
end Fragment
namespace Script
def frag (x : List Bool) (v : α → Nat) : Script α → Fragment
 | .empty => .nil | .clause t => ⟨0,fun i => [ET.eval x (fun o => o.elim i v) t]⟩ | .advance n => ⟨n.val x v,fun _ => []⟩
 | .cat a b => (frag x v a).join (frag x v b)
 | .range n b => ((List.range (n.val x v)).map fun j => frag x (fun o => o.elim j v) b).foldr Fragment.join .nil
 | .guard c y n => if c.val x v ≠ 0 then frag x v y else frag x v n
end Script
namespace Tree
def sizeE : Tree α β → E α
 | .ret _ => .const 1 | .ask _ y n => .add (.const 1) (.add (sizeE y) (sizeE n)) | .cond c y n => .cond c (sizeE y) (sizeE n)
theorem sizeE_val (q : Tree α Bool) (x v) : q.sizeE.val x v = (nodes (q.eval x v)).length := by
 induction q <;> simp_all [sizeE,E.val,eval,nodes,Nat.add_comm,Nat.add_assoc] <;> split <;> rfl
private def g (i : E α) (b : Bool) : EL α := (.add (.mul (.const 2) i) (.const 1),b)
private def inE (i : E α) (b : Bool) : EL α := (.mul (.const 2) i,b)
def lower (base : E (Option α)) : Tree α Bool → Script α
 | .ret true => .empty | .ret false => .clause (g base false,g base false,g base false)
 | .cond c y n => .guard c (lower base y) (lower base n)
 | .ask c y n =>
   let l := E.add base (.const 1); let r := E.add l (y.sizeE.rename some); let j := c.rename some
   .cat (.clause (g base false,inE j false,g l true)) (.cat (.clause (g base false,inE j true,g r true)) (.cat (lower l y) (lower r n)))
private theorem lower_sz (q : Tree α Bool) (x v base) : ((lower base q).frag x v).size = 0 := by
 induction q generalizing base with
 | ret b => cases b <;> rfl
 | ask e y n iy ino => simp [lower,Script.frag,Fragment.join,iy,ino]
 | cond e y n iy ino => simp [lower,Script.frag]; split <;> simp_all
theorem lower_spec (q : Tree α Bool) (x v base i) : ((lower base q).frag x v).triples i = body (base.val x (fun o => o.elim i v)) (q.eval x v) := by
 induction q generalizing base i with
 | ret b => cases b <;> rfl
 | ask e y n iy ino => simp [lower,Script.frag,Fragment.join,lower_sz,iy,ino,ET.eval,EL.eval,g,inE,E.val,Tree.eval,body,gate,inp,sizeE_val,List.append_assoc,Function.comp_def]
 | cond e y n iy ino => simp [lower,Script.frag,eval]; split <;> simp_all

def emitTree (q : Tree α Bool) : Script α := let root := g (.var none : E (Option α)) true; .cat (.clause (root,root,root)) (.cat (lower (.var none) q) (.advance q.sizeE))
end Tree
def forestFrag (qs : List (Q Bool)) : Fragment := ⟨(qs.flatMap nodes).length, fun i => forest i qs⟩
theorem forest_append (as bs : List (Q Bool)) (i : Nat) : forest i (as++bs) = forest i as ++ forest (i+(as.flatMap nodes).length) bs := by
 induction as generalizing i <;> simp_all [forest,List.append_assoc,Nat.add_assoc]
theorem forest_join (as bs : List (Q Bool)) : (forestFrag as).join (forestFrag bs) = forestFrag (as++bs) := by
 unfold forestFrag Fragment.join; congr 1 <;> simp [forest_append]
theorem forest_fold (as : List (List (Q Bool))) : (as.map forestFrag).foldr Fragment.join .nil = forestFrag as.flatten := by induction as <;> simp_all [forest_join]; rfl
namespace Plan
def lower : Plan α → Script α
 | .empty => .empty | .tree q => q.emitTree | .cat a b => .cat (lower a) (lower b)
 | .range n b => .range n (lower b) | .guard c y n => .guard c (lower y) (lower n)
theorem lower_spec (p : Plan α) (x v) : (p.lower.frag x v) = forestFrag (p.eval x v) := by
 induction p with
 | empty => rfl
 | tree q => unfold lower Tree.emitTree; simp [Script.frag,Fragment.join,Tree.lower_sz,Tree.sizeE_val,Plan.eval,forestFrag,Tree.lower_spec,E.val,forest,unit,gate,ET.eval,EL.eval,Tree.g]
 | cat a b ia ib => simp [lower,Script.frag,ia,ib,forest_join,eval]
 | range n b ih => simp only [lower,Script.frag,eval,List.flatMap_def]; rw [← forest_fold]; simp [List.map_map,Function.comp_def,ih]
 | guard c y n iy ino => simp only [lower,Script.frag,eval]; split <;> simp_all
end Plan
end Window.Stream
end

-- ExprCode
section
/- Fixed register code for arithmetic expressions on tableau indices. See LICENSE.openai. -/
namespace Window.Stream
open Compact.Reg
namespace E

def bump (d : Nat) : Nat → P Nat
 | 0 => .zero d | n+1 => .seq (bump d n) (.inc d)
theorem bump_exec (x) (s : S Nat) (d n) : (bump d n).exec x s = ⟨Function.update s.reg d n,s.words,s.work+1+s.reg d+n⟩ := by
 induction n with
 | zero => simp [bump,P.exec,S.put,Nat.add_assoc]
 | succ n ih => simp [bump,P.exec,S.put,ih,Function.update_idem,Nat.add_assoc]

inductive Op | add | sub | mul
def Op.eval : Op → Nat → Nat → Nat | .add => Nat.add | .sub => Nat.sub | .mul => Nat.mul
def Op.combine (op : Op) (d : Nat) : P Nat := match op with
 | .add => .seq (copyReg d (d+1)) (accumulate d (d+2))
 | .sub => .seq (copyReg d (d+1)) (minusReg d (d+2))
 | .mul => .seq (.zero d) (maddReg d (d+1) (d+2))
theorem combine_spec (op : Op) (d x) (s : S Nat) : let t := (op.combine d).exec x s
 t.reg = Function.update s.reg d (op.eval (s.reg (d+1)) (s.reg (d+2))) ∧ t.words = s.words := by
 cases op <;> simp [Op.combine,Op.eval,P.exec,copy_exec,accumulate_exec,minus_exec,madd_exec,Function.update_of_ne (show d+2 ≠ d by omega),Function.update_idem,S.put]

def code (ref : α → Nat) (d : Nat) : E α → P Nat
 | .var a => copyReg d (ref a) | .const n => bump d n | .len => .len d
 | .read i => .seq (code ref d i) (.read d d)
 | .add a b => .seq (code ref (d+1) a) (.seq (code ref (d+2) b) (Op.add.combine d))
 | .sub a b => .seq (code ref (d+1) a) (.seq (code ref (d+2) b) (Op.sub.combine d))
 | .mul a b => .seq (code ref (d+1) a) (.seq (code ref (d+2) b) (Op.mul.combine d))
 | .cond c y n => .seq (code ref d c) (.branch d (code ref d y) (code ref d n))

def At (x : List Bool) (ref : α → Nat) (d : Nat) (e : E α) (s t : S Nat) := t.reg d = e.val x (s.reg ∘ ref) ∧ (∀ j < d, t.reg j = s.reg j) ∧ t.words = s.words
private theorem envEq {ref : α → Nat} {s t : S Nat} {d : Nat} (hr : ∀ a, ref a < d) (hf : ∀ j < d, t.reg j = s.reg j) : t.reg ∘ ref = s.reg ∘ ref := funext fun a => hf _ (hr a)
private theorem two {x : List Bool} {ref : α → Nat} {d} {a b : E α} {s t u : S Nat} (op : Op)
 (hr : ∀ j, ref j < d) (ha : At x ref (d+1) a s t) (hb : At x ref (d+2) b t u) :
 let v := (op.combine d).exec x u
 v.reg d = op.eval (a.val x (s.reg ∘ ref)) (b.val x (s.reg ∘ ref)) ∧ (∀ j < d, v.reg j = s.reg j) ∧ v.words = s.words := by
 obtain ⟨h,w⟩ := combine_spec op d x u
 simp only [h,w,Function.update_self,hb.2.2,ha.2.2,and_true,hb.2.1 (d+1) (by omega),ha.1,hb.1,envEq (d:=d+1) (fun a => Nat.lt_succ_of_lt (hr a)) ha.2.1,true_and]
 intro j hj; rw [Function.update_of_ne (by omega : j ≠ d),hb.2.1 _ (by omega),ha.2.1 _ (by omega)]

theorem code_spec (e : E α) (x : List Bool) (ref : α → Nat) (d) (hr : ∀ a, ref a < d) (s : S Nat) : At x ref d e s ((code ref d e).exec x s) := by
 induction e generalizing d s with
 | var a => simp [At,code,copy_exec x s (Nat.ne_of_lt (hr a)),val,Function.comp_def]; intro j h; exact Function.update_of_ne (by omega) ..
 | const n => simp [At,code,bump_exec,val]; intro j h; exact Function.update_of_ne (by omega) ..
 | len => simp [At,code,P.exec,S.put,val]; intro j h; exact Function.update_of_ne (by omega) ..
 | read i ih =>
   obtain ⟨he,hf,hw⟩ := ih d hr s; simp [At,code,P.exec,S.put,val,he,hw]; intro j h; rw [Function.update_of_ne (by omega : j ≠ d),hf _ h]
 | add a b ia ib | sub a b ia ib | mul a b ia ib =>
   first | apply two Op.add hr | apply two Op.sub hr | apply two Op.mul hr
   all_goals first | apply ia | apply ib
   all_goals intro j; specialize hr j; omega
 | cond c y n ic iy ineg =>
   let t := (code ref d c).exec x s
   obtain ⟨he,hf,hw⟩ : At x ref d c s t := ic d hr s
   have hy := iy d hr (t.tick 1); have hn := ineg d hr (t.tick 1)
   change At x ref d _ s (if t.reg d ≠ 0 then _ else _)
   split <;> rename_i h
   · simpa [At,val,← he,h,S.tick,envEq hr hf] using (show _ from And.intro hy.1 (And.intro (fun j hj => (hy.2.1 j hj).trans (hf j hj)) (hy.2.2.trans hw)))
   · simpa [At,val,← he,h,S.tick,envEq hr hf] using (show _ from And.intro hn.1 (And.intro (fun j hj => (hn.2.1 j hj).trans (hf j hj)) (hn.2.2.trans hw)))
end E
end Window.Stream
end

-- ScriptCode
section
/- Structured bounded streams compiled to fixed register programs. See LICENSE.openai. -/
namespace Window.Stream
open Compact.Reg
namespace Script
abbrev ports : Ports Nat := ⟨1,2,3,4⟩
def skip : P Nat := .repeatN 3 (.inc 3)
def code (phase : Pass) (ref : α → Nat) (d : Nat) : Script α → P Nat
 | .empty => skip
 | .advance n => .seq (n.code ref d) (accumulate 0 d)
 | .clause t =>
   let ρ := fun (o : Option α) => o.elim 0 ref
   .seq (t.1.1.code ρ d) (.seq (t.2.1.1.code ρ (d+1)) (.seq (t.2.2.1.code ρ (d+2)) (regClause ports phase (d,t.1.2) (d+1,t.2.1.2) (d+2,t.2.2.2))))
 | .cat a b => .seq (code phase ref d a) (code phase ref d b)
 | .guard c y n => .seq (c.code ref d) (.branch d (code phase ref d y) (code phase ref d n))
 | .range n b => .seq (n.code ref d) (.seq (.zero (d+1)) (.repeatN d (.seq (code phase (fun o => o.elim (d+1) ref) (d+2) b) (.inc (d+1)))))
structure Obs where
 cursor : Nat
 sum : Nat
 count : Nat
 words : List Nat
 deriving DecidableEq
def obs (s : S Nat) : Obs := ⟨s.reg 0,s.reg 1,s.reg 2,s.words⟩
def Obs.act (phase : Pass) (f : Fragment) (o : Obs) : Obs :=
 let ts := f.triples o.cursor
 match phase with
 | .header => ⟨o.cursor+f.size,o.sum+(ts.map span).sum,o.count+ts.length,o.words⟩
 | .data => ⟨o.cursor+f.size,o.sum,o.count,o.words++ts.flatMap Window.Stream.words⟩
@[simp] theorem act_nil (phase o) : Obs.act phase .nil o = o := by cases phase <;> cases o <;> simp [Obs.act,Fragment.nil]
theorem act_join (phase a b o) : Obs.act phase (a.join b) o = Obs.act phase b (Obs.act phase a o) := by cases phase <;> simp [Obs.act,Fragment.join,Nat.add_assoc,List.append_assoc]
def Spec (phase : Pass) (d : Nat) (f : Fragment) (s t : S Nat) := obs t = Obs.act phase f (obs s) ∧ ∀ j, 3 ≤ j → j < d → t.reg j = s.reg j
private theorem ex_obs {x ref d} {e : E α} {s t} (h : E.At x ref d e s t) (hd : 5 ≤ d) : obs t = obs s := by simp [obs,h.2.1 0 (by omega),h.2.1 1 (by omega),h.2.1 2 (by omega),h.2.2]
private theorem ex_env {x ref d} {e : E α} {s t} (h : E.At x ref d e s t) {ρ : β → Nat} (hr : ∀ a, ρ a < d) : t.reg ∘ ρ = s.reg ∘ ρ := funext fun a => h.2.1 _ (hr a)
private theorem skip_spec (x d phase) (s : S Nat) (hz : s.reg 3 = 0) : Spec phase d .nil s (skip.exec x s) := by simp [Spec,skip,P.exec,hz,obs,S.tick]
private theorem advance_spec (x ref d phase) (n : E α) (s : S Nat) (hd : 5 ≤ d) (hr : ∀ a, ref a < d) : Spec phase d ((advance n).frag x (s.reg ∘ ref)) s ((code phase ref d (.advance n)).exec x s) := by
 let t := (n.code ref d).exec x s; have h : E.At x ref d n s t := E.code_spec _ _ _ _ hr _
 change Spec _ _ _ s ((accumulate 0 d).exec x t)
 rw [accumulate_exec]; cases phase <;> simp [Spec,obs,Obs.act,frag,h.1,h.2.1 0 (by omega),h.2.1 1 (by omega),h.2.1 2 (by omega),h.2.2] <;> intros j hj hj' <;> rw [Function.update_of_ne (by omega : j ≠ 0),h.2.1 j hj']
private theorem clause_spec (x ref d phase) (q : ET (Option α)) (s : S Nat) (hd : 5 ≤ d) (hr : ∀ a, ref a < d) (hz : s.reg 3 = 0) (ho : s.reg 4 = 1) : Spec phase d ((clause q).frag x (s.reg ∘ ref)) s ((code phase ref d (.clause q)).exec x s) := by
 let ρ := fun o : Option α => o.elim 0 ref
 have hρ (o) : ρ o < d := by cases o <;> simp [ρ,hr] <;> omega
 let a := (q.1.1.code ρ d).exec x s
 let b := (q.2.1.1.code ρ (d+1)).exec x a
 let c := (q.2.2.1.code ρ (d+2)).exec x b
 have ha : E.At x ρ d q.1.1 s a := E.code_spec _ _ _ _ hρ _
 have hb : E.At x ρ (d+1) q.2.1.1 a b := E.code_spec _ _ _ _ (fun j => by specialize hρ j; omega) _
 have hc : E.At x ρ (d+2) q.2.2.1 b c := E.code_spec _ _ _ _ (fun j => by specialize hρ j; omega) _
 have frame (j) (hj : j < d) : c.reg j = s.reg j := (hc.2.1 j (by omega)).trans ((hb.2.1 j (by omega)).trans (ha.2.1 j hj))
 have ew : c.words = s.words := hc.2.2.trans (hb.2.2.trans ha.2.2)
 let u := (d,q.1.2); let v := (d+1,q.2.1.2); let w := (d+2,q.2.2.2)
 have ee : (evalReg c u,evalReg c v,evalReg c w) = ET.eval x (fun o => o.elim (s.reg 0) (s.reg ∘ ref)) q := by
   have hev : s.reg ∘ ρ = (fun o => o.elim (s.reg 0) (s.reg ∘ ref)) := funext fun o => by cases o <;> rfl
   simp [ET.eval,EL.eval,evalReg,u,v,w,hc.2.1 d (by omega),hc.2.1 (d+1) (by omega),hb.2.1 d (by omega),ha.1,hb.1,hc.1,ex_env hb (fun j => Nat.lt_succ_of_lt (hρ j)),ex_env ha hρ,hev]
 change Spec _ _ _ s ((regClause ports phase u v w).exec x c)
 cases phase with
 | header =>
   obtain ⟨h,e,_⟩ := regClause_header x c ports u v w (by decide) (by dsimp [ports,v]; omega) (by dsimp [ports,w]; omega)
   simp [Spec,obs,Obs.act,frag,h,e,ew,ee,ports,frame 0 (by omega),frame 1 (by omega),frame 2 (by omega)]; intro j hj hj'; rw [Function.update_of_ne (by omega : j ≠ 2),Function.update_of_ne (by omega : j ≠ 1),frame j hj']
 | data =>
   obtain ⟨h,e,_⟩ := regClause_data x c ports ((frame 3 (by omega)).trans hz) ((frame 4 (by omega)).trans ho) u v w
   simp [Spec,obs,Obs.act,frag,h,e,ew,ee,frame 0 (by omega),frame 1 (by omega),frame 2 (by omega)]; exact fun j _ => frame j

private theorem fold_act (fs : List Fragment) (phase o) : Obs.act phase (fs.foldr Fragment.join .nil) o = fs.foldl (fun a f => Obs.act phase f a) o := by induction fs generalizing o <;> simp_all [act_join]
private abbrev Valid (s : S Nat) := s.reg 3 = 0 ∧ s.reg 4 = 1
private theorem carry {phase d f s t} (h : Spec phase d f s t) (hd : 5 ≤ d) (valid : Valid s) : Valid t := ⟨(h.2 3 (by decide) (by omega)).trans valid.1,(h.2 4 (by decide) (by omega)).trans valid.2⟩
private theorem carryEnv {phase d f s t} (h : Spec phase d f s t) {ref : α → Nat} (lo : ∀ a, 3 ≤ ref a) (hi : ∀ a, ref a < d) : t.reg ∘ ref = s.reg ∘ ref := funext fun a => h.2 _ (lo a) (hi a)
private abbrev Correct (p : Script α) (phase : Pass) (x : List Bool) := ∀ (ref : α → Nat) (d : Nat) (s : S Nat), 5 ≤ d → (∀ a, 3 ≤ ref a) → (∀ a, ref a < d) → Valid s → Spec phase d (p.frag x (s.reg ∘ ref)) s ((p.code phase ref d).exec x s)
private theorem range_spec (b : Script (Option α)) (n : E α) (phase x) (ih : Correct b phase x) : Correct (.range n b) phase x := by
 intro ref d s hd lo hi valid
 let t := (n.code ref d).exec x s
 have he : E.At x ref d n s t := E.code_spec _ _ _ _ hi _
 let u := t.put (d+1) 0 (1+t.reg (d+1)); let start := u.tick (1+u.reg d)
 let ρ := fun o : Option α => o.elim (d+1) ref
 have hlo (o) : 3 ≤ ρ o := by cases o <;> simp [ρ,lo] <;> omega
 have hhi (o) : ρ o < d+2 := by cases o <;> simp [ρ] <;> first | omega | exact Nat.lt_trans (hi _) (by omega)
 let step := fun z : S Nat => (((P.seq (b.code phase ρ (d+2)) (.inc (d+1))).exec x z).tick 1)
 let fs := fun j => b.frag x (fun o => o.elim j (s.reg ∘ ref))
 have initFrame (j) (hj : j<d) : start.reg j = s.reg j := by simp [start,u,S.put,S.tick,Function.update_of_ne (by omega : j ≠ d+1),he.2.1 _ hj]
 have inv (k) : let z := step^[k] start
     obs z = ((List.range k).map fs).foldl (fun o f => Obs.act phase f o) (obs s) ∧ z.reg (d+1) = k ∧ ∀ j, 3 ≤ j → j < d → z.reg j = s.reg j := by
   induction k with
   | zero => simp [obs,initFrame 0 (by omega),initFrame 1 (by omega),initFrame 2 (by omega)]; exact ⟨by simp [start,u,S.tick,S.put,he.2.2],by simp [start,u,S.tick,S.put],fun j _ => initFrame j⟩
   | succ k ik =>
     let z := step^[k] start
     obtain ⟨oz,iz,fz⟩ := ik
     have ve : z.reg ∘ ρ = (fun o => o.elim k (s.reg ∘ ref)) := by funext o; cases o with | none => exact iz | some a => exact fz _ (lo a) (hi a)
     let v := (b.code phase ρ (d+2)).exec x z
     have hv : Spec phase (d+2) (fs k) z v := by rw [show fs k = b.frag x (z.reg ∘ ρ) by rw [ve]]; exact ih _ _ _ (by omega) hlo hhi ⟨(fz 3 (by decide) (by omega)).trans valid.1,(fz 4 (by decide) (by omega)).trans valid.2⟩
     have idx := (hv.2 (d+1) (by omega) (by omega)).trans iz
     rw [Function.iterate_succ_apply']; change obs ((v.put (d+1) (v.reg (d+1)+1) 1).tick 1) = _ ∧ _
     have sameObs : obs ((v.put (d+1) (v.reg (d+1)+1) 1).tick 1) = obs v := by simp [obs,S.put,S.tick,Function.update_of_ne (by omega : 0 ≠ d+1),Function.update_of_ne (by omega : 1 ≠ d+1),Function.update_of_ne (by omega : 2 ≠ d+1)]
     rw [sameObs,hv.1]; simp only [List.range_succ,List.map_append,List.map_cons,List.map_nil,List.foldl_append,List.foldl_cons,List.foldl_nil,← oz]; refine ⟨rfl,?_,?_⟩
     · change (Function.update v.reg (d+1) (v.reg (d+1)+1)) (d+1) = _; simp [idx]
     · intro j hj hj'; change (Function.update v.reg (d+1) _) j = _; rw [Function.update_of_ne (by omega : j ≠ d+1),hv.2 _ hj (by omega),fz _ hj hj']
 have cnt : u.reg d = n.val x (s.reg ∘ ref) := by simp [u,S.put,he.1]
 obtain ⟨a,_,c⟩ := inv (u.reg d)
 change obs (step^[u.reg d] start) = Obs.act phase _ _ ∧ _
 refine ⟨?_,c⟩; change _ = Obs.act phase (((List.range _).map fs).foldr Fragment.join .nil) _; rw [fold_act,← cnt]; exact a

theorem code_spec (p : Script α) (phase x) : Correct p phase x := by
 induction p with
 | empty => intro ref d s _ _ _ h; exact skip_spec _ _ _ _ h.1
 | advance n => intro ref d s hd lo hi _; exact advance_spec _ _ _ _ _ _ hd hi
 | clause q => intro ref d s hd lo hi h; exact clause_spec _ _ _ _ _ _ hd hi h.1 h.2
 | range n b ih => exact range_spec b n phase x ih
 | cat a b ia ib =>
   intro ref d s hd lo hi v; let t := (a.code phase ref d).exec x s
   have h := ia ref d s hd lo hi v; have g := ib ref d t hd lo hi (carry h hd v)
   have ev : t.reg ∘ ref = s.reg ∘ ref := carryEnv h lo hi
   rw [ev] at g; exact ⟨g.1.trans (by rw [frag,act_join,← h.1]),fun j hj hj' => (g.2 _ hj hj').trans (h.2 _ hj hj')⟩
 | guard c y n iy ino =>
   intro ref d s hd lo hi v; let t := (c.code ref d).exec x s; let u := t.tick 1
   have h : E.At x ref d c s t := E.code_spec _ _ _ _ hi _
   have env : u.reg ∘ ref = s.reg ∘ ref := ex_env h hi
   have eqo : obs u = obs s := ex_obs h hd
   have good : Valid u := ⟨(h.2.1 3 (by omega)).trans v.1,(h.2.1 4 (by omega)).trans v.2⟩
   change Spec _ _ (if _ then _ else _) _ (if t.reg d ≠ 0 then _ else _); rw [h.1]; split
   · have g := iy ref d u hd lo hi good; rw [env] at g; exact ⟨g.1.trans (by rw [eqo]),fun j hj hj' => (g.2 _ hj hj').trans (h.2.1 _ hj')⟩
   · have g := ino ref d u hd lo hi good; rw [env] at g; exact ⟨g.1.trans (by rw [eqo]),fun j hj hj' => (g.2 _ hj hj').trans (h.2.1 _ hj')⟩
end Script
end Window.Stream
end

-- PlanProgram
section
/- Two-pass emission: count and sum indices, emit the header, then replay clauses. -/
namespace Window.Stream
open Compact.Reg OAI.BinPackingGames.Foundations.Complexity
namespace Plan
abbrev noRef : Empty → Nat := Empty.elim
def program (p : Plan Empty) : P Nat := .seq (.inc 4) (.seq (p.lower.code .header noRef 5) (.seq (.inc 1) (.seq (.emit 1) (.seq (.emit 2) (.seq (.zero 0) (p.lower.code .data noRef 5))))))
def packed (p : Plan Empty) (x : List Bool) := pack (forest 0 (p.eval x noRef))
theorem program_words (p : Plan Empty) (x) : (p.program.exec x S.init).words = formulaWords (p.packed x) := by
 let a := (P.inc 4 : P Nat).exec x S.init; let b := (p.lower.code .header noRef 5).exec x a
 let c := ((P.seq (.inc 1) (.seq (.emit 1) (.seq (.emit 2) (.zero 0)))) : P Nat).exec x b
 let qs := p.eval x noRef; let ts := forest 0 qs
 have ve (t : S Nat) : t.reg ∘ noRef = noRef := funext fun a => nomatch a
 have ah := Script.code_spec p.lower .header x noRef 5 a (by decide) (fun a => nomatch a) (fun a => nomatch a) (by exact ⟨rfl,rfl⟩)
 obtain ⟨ah,af⟩ := ah; rw [ve,lower_spec] at ah
 have bobs : Script.obs b = ⟨(qs.flatMap nodes).length,(ts.map span).sum,ts.length,[]⟩ := by simpa [b,a,Script.Obs.act,forestFrag,Script.obs,P.exec,S.put,S.init,ts,qs] using ah
 have h1 : b.reg 1 = (ts.map span).sum := congrArg Script.Obs.sum bobs
 have h2 : b.reg 2 = ts.length := congrArg Script.Obs.count bobs
 have hw : b.words = [] := congrArg Script.Obs.words bobs
 have hz : b.reg 3 = 0 := af 3 (by decide) (by decide)
 have ho : b.reg 4 = 1 := af 4 (by decide) (by decide)
 have dh := Script.code_spec p.lower .data x noRef 5 c (by decide) (fun a => nomatch a) (fun a => nomatch a) (by exact ⟨by simpa [c,P.exec,S.put] using hz,by simpa [c,P.exec,S.put] using ho⟩)
 obtain ⟨dh,_⟩ := dh; rw [ve,lower_spec] at dh
 have wh := congrArg Script.Obs.words dh
 change ((p.lower.code .data noRef 5).exec x c).words = _
 rw [packed,pack_words]; simpa [Script.Obs.act,forestFrag,Script.obs,c,P.exec,S.put,h1,h2,hw,ts,qs] using wh
end Plan
end Window.Stream
end

-- Budget
section
/- Polynomial envelopes for bounded iteration; tiers separate indices, cursor, and scratch. -/
namespace Window.Stream.Resources
open Compact.Reg
abbrev Poly := Polynomial Nat
abbrev ev (p : Poly) (n : Nat) := p.eval n
theorem mono (p : Poly) {i j : Nat} (h : i ≤ j) : p.eval i ≤ p.eval j := by
 induction p using Polynomial.induction_on' with
 | add _ _ ha hb => simpa using Nat.add_le_add ha hb
 | monomial n c => simp only [Polynomial.eval_monomial]; gcongr
structure Inp (x : List Bool) (ref : α → Nat) (s : S Nat) (a b m : Nat) : Prop where
 len : x.length ≤ a
 env : ∀ j, s.reg (ref j) ≤ a
 cursor : s.reg 0 ≤ b
 regs : ∀ j, s.reg j ≤ m
 ab : a ≤ b
 bm : b ≤ m
structure Out (p : Poly) (a b m : Nat) (s t : S Nat) : Prop where
 cursor : t.reg 0 ≤ b+p.eval a
 regs : ∀ j, t.reg j ≤ m+p.eval b
 work : t.work ≤ s.work+p.eval m

noncomputable def mix (p q : Poly) : Poly := p + q.comp (Polynomial.X+p)
theorem chain {p q a b m : _} {s t u : S Nat} (ab : a ≤ b) (bm : b ≤ m) (h : Out p a b m s t) (g : Out q a (b+p.eval a) (m+p.eval b) t u) : Out (mix p q) a b m s u := by
 constructor
 · have := g.cursor; simp [mix]; have := mono q (Nat.le_add_right a (p.eval a)); omega
 · intro j; have hj := g.regs j; have hz := mono q (Nat.add_le_add_left (mono p ab) b); simp [mix]; omega
 · have hw := g.work; have hz := mono q (Nat.add_le_add_left (mono p bm) m); have := h.work; simp [mix]; omega
abbrev Valid (s : S Nat) := s.reg 3 = 0 ∧ s.reg 4 = 1
abbrev Scope (ref : α → Nat) (d : Nat) := 5 ≤ d ∧ ∀ j, 3 ≤ ref j ∧ ref j < d
abbrev Limit (s : Script α) (p : Poly) := ∀ phase x ref d z a b m, Scope ref d → Valid z → Inp x ref z a b m → Out p a b m z ((s.code phase ref d).exec x z)
theorem scopeFrame (s : Script α) (phase x ref d z) (hd : Scope ref d) (h : Valid z) : let t := (s.code phase ref d).exec x z; Valid t ∧ ∀ j, t.reg (ref j) = z.reg (ref j) := by
 have g := (Script.code_spec s phase x ref d z hd.1 (fun j => (hd.2 j).1) (fun j => (hd.2 j).2) h).2
 exact ⟨⟨(g 3 (by decide) (by have := hd.1; omega)).trans h.1,(g 4 (by decide) (by have := hd.1; omega)).trans h.2⟩,fun j => g _ (hd.2 j).1 (hd.2 j).2⟩
theorem cat {s t : Script α} {p q} (hp : Limit s p) (hq : Limit t q) : Limit (.cat s t) (mix p q) := by
 intro phase x ref d z a b m hd v h
 have g := hp phase x ref d z a b m hd v h
 obtain ⟨vv,fr⟩ := scopeFrame s phase x ref d z hd v
 apply chain h.ab h.bm g (hq phase x ref d _ _ _ _ hd vv ?_)
 exact ⟨h.len,fun j => (fr j).le.trans (h.env j),g.cursor,g.regs,by have := h.ab; omega,Nat.add_le_add h.bm (mono p h.ab)⟩
end Window.Stream.Resources
end

-- ExprLimit
section
/- Interface for expression resource accounting. -/
namespace Window.Stream.Resources
open Compact.Reg
abbrev ELimit (e : E α) (p : Poly) := ∀ x ref d (s : S Nat) a m, (∀ j, ref j < d) → x.length ≤ a → (∀ j, s.reg (ref j) ≤ a) → a ≤ m → (∀ j, s.reg j ≤ m) → let t := (e.code ref d).exec x s; t.reg d ≤ p.eval a ∧ (∀ j, t.reg j ≤ m+p.eval a) ∧ t.work ≤ s.work+p.eval m
end Window.Stream.Resources
end

-- RangeLimit
section
/- Accounting for snapshot iteration in nested tableau streams. -/
namespace Window.Stream.Resources
open Compact.Reg Polynomial
noncomputable section
private def arg (p : Poly) := X+p+1
private def cur (p q : Poly) := arg p + p * q.comp (arg p)
private def mem (p q : Poly) := X + cur p q + p + p * (q.comp (X + cur p q)+1)
private def tim (p q : Poly) := 4 + 2*X + 4*p + p * (q.comp (mem p q)+2)
private def total (p q : Poly) := cur p q + mem p q + tim p q
private theorem loop_bound (p q : Poly) (a b m n : Nat) (s : S Nat) (z : Nat → S Nat) (ab : a ≤ b) (bm : b ≤ m) (hn : n ≤ p.eval a)
 (ic : (z 0).reg 0 ≤ b) (ir : ∀ j, (z 0).reg j ≤ m+p.eval a) (iw : (z 0).work ≤ s.work+4+2*m+4*p.eval m)
 (step : ∀ k < n, ∀ B M, (arg p).eval a ≤ B → B ≤ M → (z k).reg 0 ≤ B → (∀ j, (z k).reg j ≤ M) →
 (z (k+1)).reg 0 ≤ B+q.eval ((arg p).eval a) ∧ (∀ j,(z (k+1)).reg j ≤ M+q.eval B+1) ∧ (z (k+1)).work ≤ (z k).work+q.eval M+2) : Out (total p q) a b m s (z n) := by
 let A := (arg p).eval a
 let B := fun k => b+A+k*q.eval A
 let M := fun k => m+(cur p q).eval b+p.eval a+k*(q.eval (b+(cur p q).eval b)+1)
 have cb k (hk : k ≤ n) : B k ≤ b+(cur p q).eval b := by
   have hA := mono (arg p) ab; have hq := mono q hA; have hk' := hk.trans (hn.trans (mono p ab)); dsimp [B,A]; simp only [cur,eval_add,eval_mul,eval_comp]; have := Nat.mul_le_mul hk' hq; omega
 have ub k (hk : k ≤ n) : M k ≤ (mem p q).eval m := by
   have hh : b+(cur p q).eval b ≤ m+(cur p q).eval m := Nat.add_le_add bm (mono _ bm)
   have hp := mono p (ab.trans bm); have hk' := hk.trans (hn.trans hp); dsimp [M]; simp only [mem,eval_add,eval_X,eval_mul,eval_comp,eval_one]; gcongr <;> first | apply mono; assumption | assumption
 have inv k (hk : k ≤ n) : (z k).reg 0 ≤ B k ∧ (∀ j,(z k).reg j ≤ M k) ∧ (z k).work ≤ s.work+4+2*m+4*p.eval m+k*(q.eval ((mem p q).eval m)+2) := by
   induction k with
   | zero => simp [B,M]; exact ⟨by omega,fun j => by have := ir j; omega,iw⟩
   | succ k ih =>
     obtain ⟨hc,hr,hw⟩ := ih (by omega)
     have hb := cb k (by omega); have hm := ub k (by omega)
     have hbm : B k ≤ M k := by dsimp [M]; omega
     obtain ⟨oc,orr,ow⟩ := step k (by omega) (B k) (M k) (by dsimp [B,A]; omega) hbm hc hr
     have hq := mono q hb; have hq' := mono q hm
     constructor
     · simpa [B,Nat.succ_mul,Nat.add_assoc] using oc
     · constructor
       · intro j; have := orr j; dsimp [M] at *; rw [Nat.succ_mul]; omega
       · simp only [Nat.succ_mul]; omega
 obtain ⟨oc,orr,ow⟩ := inv n le_rfl
 constructor
 · have hmul := Nat.mul_le_mul_right (q.eval A) hn; dsimp [B] at oc; simp only [total,cur,eval_add,eval_mul,eval_comp]; dsimp [A] at *; omega
 · intro j; have hj := (orr j).trans (ub n le_rfl); -- use b-tier growth, not the coarser m-tier bound
   have ha := mono p ab; have hn' := hn.trans ha
   have mul := Nat.mul_le_mul_right (q.eval (b+(cur p q).eval b)+1) hn'
   have hv := orr j; dsimp [M] at hv; simp only [total,mem,eval_add,eval_X,eval_mul,eval_comp,eval_one]; omega
 · have hn' := hn.trans (mono p (ab.trans bm)); have mul := Nat.mul_le_mul_right (q.eval ((mem p q).eval m)+2) hn'
   simp only [total,tim,eval_add,eval_mul,eval_ofNat,eval_X,eval_comp]; omega

theorem range {e : E α} {bdy : Script (Option α)} {p q : Poly} (he : ELimit e p) (hh : Limit bdy q) : ∃ r, Limit (.range e bdy) r := by
 refine ⟨total p q,?_⟩; intro phase x ref d s a b m hd valid h
 let t := (e.code ref d).exec x s; let u := t.put (d+1) 0 (1+t.reg (d+1)); let start := u.tick (1+u.reg d)
 let n := u.reg d; let ρ := fun o : Option α => o.elim (d+1) ref
 let step := fun z : S Nat => (((P.seq (bdy.code phase ρ (d+2)) (.inc (d+1))).exec x z).tick 1)
 let z := fun k : Nat => step^[k] start
 have D := hd.1; have H (j) := (hd.2 j).2
 have rs : Scope ρ (d+2) := ⟨by omega,fun o => by cases o with | none => dsimp [ρ]; omega | some j => exact ⟨(hd.2 j).1,by dsimp [ρ]; specialize H j; omega⟩⟩
 have hm := h.ab.trans h.bm
 obtain ⟨en,er,ew⟩ := he x ref d s a m H h.len h.env hm h.regs
 have hn : n ≤ p.eval a := by simpa [n,u,t,S.put] using en
 have ef := (E.code_spec e x ref d H s).2.1
 have initF (j) (hj : j < d) : start.reg j = s.reg j := by simp [start,u,S.tick,S.put,Function.update_of_ne (by omega : j ≠ d+1),t,ef _ hj]
 have frame (k) : (z k).reg (d+1) = k ∧ Valid (z k) ∧ ∀ j, (z k).reg (ref j) = s.reg (ref j) := by
   induction k with
   | zero => exact ⟨by simp [z,start,u,S.tick,S.put],⟨(initF 3 (by omega)).trans valid.1,(initF 4 (by omega)).trans valid.2⟩,fun j => initF _ (H j)⟩
   | succ k ih =>
     obtain ⟨vv,fr⟩ := scopeFrame bdy phase x ρ (d+2) (z k) rs ih.2.1
     have idx := (fr none).trans ih.1
     change _ = _ ∧ _; simp only [z,Function.iterate_succ_apply']; change (Function.update _ (d+1) (_+1)) (d+1) = _ ∧ _
     refine ⟨by simpa [ρ] using idx,⟨?_,?_⟩,fun j => ?_⟩
     · exact (Function.update_of_ne (by omega : 3 ≠ d+1) ..).trans vv.1
     · exact (Function.update_of_ne (by omega : 4 ≠ d+1) ..).trans vv.2
     · exact (Function.update_of_ne (by specialize H j; omega : ref j ≠ d+1) ..).trans ((fr (some j)).trans (ih.2.2 j))
 change Out _ _ _ _ _ (z n)
 apply loop_bound p q a b m n s z h.ab h.bm hn ((initF 0 (by omega)).le.trans h.cursor)
 · intro j; by_cases eq : j = d+1
   · subst j; simp [z,start,u,S.tick,S.put]
   · simpa [z,start,u,S.tick,S.put,Function.update_of_ne eq,t] using er j
 · have ed := er (d+1); have en' := mono p hm
   change t.work + (1+t.reg (d+1)) + (1+n) ≤ _; change t.work ≤ _ at ew; change t.reg (d+1) ≤ _ at ed; omega
 · intro k hk B M hB hM hc hr
   have fa := frame k
   have input : Inp x ρ (z k) ((arg p).eval a) B M := by
     refine ⟨?_,?_,hc,hr,hB,hM⟩
     · simp [arg]; have := h.len; omega
     · intro o; cases o with
       | none => simp [ρ,fa.1,arg]; omega
       | some j => simp [ρ,fa.2.2,arg]; have := h.env j; omega
   let v := (bdy.code phase ρ (d+2)).exec x (z k)
   obtain ⟨oc,orr,ow⟩ := hh phase x ρ (d+2) (z k) _ B M rs fa.2.1 input
   have e0 : z (k+1) = (v.put (d+1) (v.reg (d+1)+1) 1).tick 1 := by simp [z,v,step,Function.iterate_succ_apply',P.exec]
   rw [e0]; refine ⟨by simpa [S.tick,S.put,v] using oc,?_,by dsimp [S.tick,S.put]; dsimp [v]; omega⟩
   intro j; by_cases eq : j = d+1
   · subst j; simpa [S.tick,S.put,v] using Nat.add_le_add_right (orr (d+1)) 1
   · dsimp [S.tick,S.put]; rw [Function.update_of_ne eq]; exact (orr j).trans (by omega)
end
end Window.Stream.Resources
end

-- AtomLimit
section
/- Atomic resource bounds for the two-pass tableau emitter. -/
namespace Window.Stream.Resources
open Compact.Reg Polynomial
noncomputable section
abbrev AllE := ∀ {α : Type} (e : E α), ∃ p, ELimit e p
private theorem weakenE {e : E α} {p q : Poly} (hp : ELimit e p) (g : ∀ n, p.eval n ≤ q.eval n) : ELimit e q := by
 intro x ref d s a m hd hl hv ham hr; obtain ⟨o,r,w⟩ := hp x ref d s a m hd hl hv ham hr; exact ⟨o.trans (g a),fun j => (r j).trans (Nat.add_le_add_left (g a) _),w.trans (Nat.add_le_add_left (g m) _)⟩
theorem empty : Limit (.empty : Script α) 1 := by
 intro phase x ref d z a b m hd v h; have hz := v.1; constructor <;> simp [Script.code,Script.skip,P.exec,hz,S.tick] <;> first | exact Nat.le_succ_of_le h.cursor | intro j; exact Nat.le_succ_of_le (h.regs j)
theorem advance (e : E α) {p} (g : ELimit e p) : Limit (.advance e) (1+4*p) := by
 intro phase x ref d s a b m hd v h; let t := (e.code ref d).exec x s
 have H (j) := (hd.2 j).2
 obtain ⟨o,r,w⟩ := g x ref d s a m H h.len h.env (h.ab.trans h.bm) h.regs
 have D := hd.1; have F : t.reg 0 = s.reg 0 := (E.code_spec e x ref d H s).2.1 _ (by omega)
 have pab := mono p h.ab; have pbm := mono p h.bm; have oc := h.cursor; have bm := h.bm
 change Out _ _ _ _ s ((accumulate 0 d).exec x t); rw [accumulate_exec]; change t.reg d ≤ _ at o; change t.work ≤ _ at w
 constructor
 · simp [F]; omega
 · intro j; by_cases hj : j=0
   · subst j; simp [F]; omega
   · simp [Function.update_of_ne hj]; have := r j; change t.reg j ≤ _ at this; omega
 · simp; omega

theorem guard {e : E α} {y n : Script α} {p q r : Poly} (ep : ELimit e p) (yq : Limit y q) (nr : Limit n r) : Limit (.guard e y n) (1+p+(q+r).comp (X+p)) := by
 intro phase x ref d s a b m hd v h; let t := (e.code ref d).exec x s; let u := t.tick 1
 have D := hd.1; have H j := (hd.2 j).2
 have F := (E.code_spec e x ref d H s).2.1
 obtain ⟨_,rs,ws⟩ := ep x ref d s a m H h.len h.env (h.ab.trans h.bm) h.regs
 have vn : Valid u := ⟨(F 3 (by omega)).trans v.1,(F 4 (by omega)).trans v.2⟩
 have h' : Inp x ref u a b (m+p.eval a) := ⟨h.len,fun j => (F _ (H j)).le.trans (h.env j),(F 0 (by omega)).le.trans h.cursor,rs,h.ab,h.bm.trans (Nat.le_add_right ..)⟩
 change Out _ _ _ _ s (if t.reg d ≠ 0 then _ else _)
 have pab := mono p h.ab; have pam := mono p (h.ab.trans h.bm)
 have lift (pp : Poly) (w : S Nat) (le : ∀ i, pp.eval i ≤ (q+r).eval i) (z : Out pp a b (m+p.eval a) u w) : Out (1+p+(q+r).comp (X+p)) a b m s w := by
   constructor
   · have hh := (le a).trans (mono (q+r) (Nat.le_add_right a (p.eval a))); have hc := z.cursor; simp at hh ⊢; omega
   · intro j; have hh := (le b).trans (mono (q+r) (Nat.le_add_right b (p.eval b))); have hr := z.regs j; simp at hh ⊢; omega
   · have hh := (le _).trans (mono (q+r) (Nat.add_le_add_left pam m)); have hw := z.work; change t.work ≤ _ at ws; change _ ≤ t.work+1+_ at hw; simp at hh ⊢; omega
 split
 · exact lift q _ (by simp) (yq phase x ref d u a b _ hd vn h')
 · exact lift r _ (by simp) (nr phase x ref d u a b _ hd vn h')

theorem clause (allE : AllE) (t : ET (Option α)) : ∃ f, Limit (.clause t) f := by
 obtain ⟨p1,h1⟩ := allE t.1.1; obtain ⟨p2,h2⟩ := allE t.2.1.1; obtain ⟨p3,h3⟩ := allE t.2.2.1
 let p := p1+p2+p3
 replace h1 := weakenE (q:=p) h1 (by intro n; simp [p] <;> omega)
 replace h2 := weakenE (q:=p) h2 (by intro n; simp [p] <;> omega)
 replace h3 := weakenE (q:=p) h3 (by intro n; simp [p] <;> omega)
 let f : Poly := 10+10*p+3*p.comp (X+2*p)
 refine ⟨f,?_⟩; intro phase x ref d s a b m hd valid h
 let ρ := fun o : Option α => o.elim 0 ref
 have D := hd.1; have H (o) : ρ o < d := by cases o with | none => dsimp [ρ]; omega | some j => exact (hd.2 j).2
 have V (o) : s.reg (ρ o) ≤ b := by cases o with | none => exact h.cursor | some j => exact (h.env j).trans h.ab
 let s1 := (t.1.1.code ρ d).exec x s; let s2 := (t.2.1.1.code ρ (d+1)).exec x s1; let s3 := (t.2.2.1.code ρ (d+2)).exec x s2
 have H2 (o) := Nat.lt_succ_of_lt (H o); have H3 (o) := Nat.lt_succ_of_lt (H2 o)
 have F1 := (E.code_spec t.1.1 x ρ d H s).2.1; have F2 := (E.code_spec t.2.1.1 x ρ (d+1) H2 s1).2.1; have F3 := (E.code_spec t.2.2.1 x ρ (d+2) H3 s2).2.1
 have len := h.len.trans h.ab; have bm := h.bm
 obtain ⟨o1,r1,w1⟩ := h1 x ρ d s b m H len V bm h.regs
 obtain ⟨o2,r2,w2⟩ := h2 x ρ (d+1) s1 b (m+p.eval b) H2 len (fun j => (F1 _ (H j)).le.trans (V j)) (by omega) r1
 obtain ⟨o3,r3,w3⟩ := h3 x ρ (d+2) s2 b (m+p.eval b+p.eval b) H3 len (fun j => (F2 _ (H2 j)).le.trans ((F1 _ (H j)).le.trans (V j))) (by omega) r2
 have idx : s3.reg d ≤ p.eval b := (F3 _ (by omega)).le.trans ((F2 _ (by omega)).le.trans o1)
 have idx' : s3.reg (d+1) ≤ p.eval b := (F3 _ (by omega)).le.trans o2
 have idx'' : s3.reg (d+2) ≤ p.eval b := o3
 have fr (j) (hj : j<d) : s3.reg j = s.reg j := (F3 j (by omega)).trans ((F2 j (by omega)).trans (F1 j hj))
 have pbm := mono p bm
 have W : s3.work ≤ s.work+3*p.eval (m+2*p.eval m) := by
   change s1.work ≤ _ at w1; change s2.work ≤ _ at w2; change s3.work ≤ _ at w3
   have A := mono p (Nat.le_add_right m (2*p.eval m)); have B := mono p (show m+p.eval b ≤ m+2*p.eval m by omega); have C := mono p (show m+p.eval b+p.eval b ≤ m+2*p.eval m by omega); omega
 let u := (d,t.1.2); let v := (d+1,t.2.1.2); let w := (d+2,t.2.2.2)
 have sum : span (evalReg s3 u,evalReg s3 v,evalReg s3 w) ≤ 3*p.eval b := by dsimp [u,v,w,evalReg,span]; omega
 change Out _ _ _ _ s ((regClause Script.ports phase u v w).exec x s3)
 cases phase with
 | header =>
   obtain ⟨re,_,we⟩ := regClause_header x s3 Script.ports u v w (by decide) (by dsimp [v,Script.ports]; omega) (by dsimp [w,Script.ports]; omega)
   constructor
   · simp [re,Script.ports,fr 0 (by omega)]; exact h.cursor.trans (by omega)
   · intro j; rw [re]; by_cases c : j=2
     · subst j; simp [Script.ports,fr 2 (by omega),f]; have := h.regs 2; omega
     · by_cases e : j=1
       · subst j; simp [Script.ports,fr 1 (by omega),f]; have := h.regs 1; omega
       · simp [Script.ports,Function.update_of_ne c,Function.update_of_ne e,f]; have := r3 j; change s3.reg j ≤ _ at this; omega
   · rw [we]; simp [f]; omega
 | data =>
   obtain ⟨re,_,we⟩ := regClause_data x s3 Script.ports ((fr 3 (by omega)).trans valid.1) ((fr 4 (by omega)).trans valid.2) u v w
   constructor
   · simp [re,fr 0 (by omega)]; exact h.cursor.trans (by omega)
   · intro j; rw [re]; have := r3 j; change s3.reg j ≤ _ at this; simp [f]; omega
   · simp [f]; omega

theorem script_limit (h : AllE) (s : Script α) : ∃ p, Limit s p := by
 induction s with
 | empty => exact ⟨_,empty⟩
 | advance e => obtain ⟨p,he⟩ := h e; exact ⟨_,advance e he⟩
 | clause t => exact clause h t
 | cat a b ia ib => obtain ⟨p,hp⟩ := ia; obtain ⟨q,hq⟩ := ib; exact ⟨_,cat hp hq⟩
 | guard e y n iy ino => obtain ⟨p,hp⟩ := h e; obtain ⟨q,hq⟩ := iy; obtain ⟨r,hr⟩ := ino; exact ⟨_,guard hp hq hr⟩
 | range e b ih => obtain ⟨p,hp⟩ := h e; obtain ⟨q,hq⟩ := ih; exact range hp hq
end
end Window.Stream.Resources
end

-- ProgramWork
section
/- Polynomial work bound for the complete two-pass register program. -/
namespace Window.Stream.Resources
open Compact.Reg Polynomial
noncomputable section
theorem program_work (hE : AllE) (plan : Plan Empty) : ∃ P : Poly, ∀ x, (plan.program.exec x S.init).work ≤ P.eval x.length := by
 obtain ⟨p,hp⟩ := script_limit hE plan.lower
 let B : Poly := X+2+p.comp (X+1)
 refine ⟨10+5*B+p.comp B,?_⟩; intro x
 let a := (P.inc 4 : P Nat).exec x S.init; let b := (plan.lower.code .header Plan.noRef 5).exec x a
 let c := ((P.seq (.inc 1) (.seq (.emit 1) (.seq (.emit 2) (.zero 0)))) : P Nat).exec x b
 have hd : Scope Plan.noRef 5 := ⟨by decide,fun j => nomatch j⟩
 have va : Valid a := ⟨rfl,rfl⟩
 have inp : Inp x Plan.noRef a x.length x.length (x.length+1) := ⟨le_rfl,(fun j => nomatch j),Nat.zero_le _,fun j => by by_cases e : j=4 <;> simp [a,P.exec,S.put,S.init,Function.update,e],le_rfl,by omega⟩
 have obt := hp .header x Plan.noRef 5 a _ _ _ hd va inp
 have vb : Valid b := (scopeFrame plan.lower .header x Plan.noRef 5 a hd va).1
 have vc : Valid c := ⟨by simpa [c,P.exec,S.put] using vb.1,by simpa [c,P.exec,S.put] using vb.2⟩
 have hmono : p.eval x.length ≤ p.eval (x.length+1) := mono p (by omega)
 have regs (j) : b.reg j ≤ x.length+1+p.eval x.length := obt.regs j
 have wk : b.work ≤ 1+p.eval (x.length+1) := obt.work
 have cr (j) : c.reg j ≤ B.eval x.length := by
   have := regs j; have := regs 1; by_cases u : j=0 <;> by_cases v : j=1 <;> simp [c,P.exec,S.put,Function.update,u,v,B] <;> omega
 have cinp : Inp x Plan.noRef c x.length x.length (B.eval x.length) := ⟨le_rfl,(fun j => nomatch j),by simp [c,P.exec,S.put],cr,le_rfl,by simp [B]; omega⟩
 have out := hp .data x Plan.noRef 5 c _ _ _ hd vc cinp
 have cw : c.work ≤ 10+5*B.eval x.length := by
   have := regs 0; have := regs 1; have := regs 2; simp [c,P.exec,S.put,B]; omega
 change ((plan.lower.code .data Plan.noRef 5).exec x c).work ≤ _
 simpa using (out.work.trans (Nat.add_le_add_right cw _))
end
end Window.Stream.Resources
end

-- PrefixInit
section
namespace Window.Stream.Prefix
open Turing OAI.BinPackingGames.Foundations Complexity CookLevin
noncomputable section
local instance kFinI2 (M : Turing.FinTM2) : Fintype M.K := M.kFin
local instance ΛFinI2 (M : Turing.FinTM2) : Fintype M.Λ := M.ΛFin
local instance σFinI2 (M : Turing.FinTM2) : Fintype M.σ := M.σFin
variable (V : NPVerifier)
local instance : ∀ k, Fintype ((tm V).Γ k) := V.finiteAlphabet

def paddr (tag : Nat) (i : E α) : E α := E.addrE (.const tag) (.const 0) (.const 0) i (.const 1)
def flag (tag : Nat) (a : Nat → Bool) (i : Nat) := a (addr (tag,0,0,i) 1)
def monoT (j : E α) : Tree α Bool := .ask (paddr 5 (.add j (.const 1))) (.ask (paddr 5 j) (.ret true) (.ret false)) (.ret true)
def Mono (W : Nat) (a : Nat → Bool) := ∀ j, j+1 < W → flag 5 a (j+1) = true → flag 5 a j = true
def Repr (W : Nat) (a : Nat → Bool) (w : List Bool) := ∀ i, w[i]? = if i < W ∧ flag 5 a i = true then some (flag 1 a i) else none
private theorem decode {a W} (h : Mono W a) : ∃ w : List Bool, w.length ≤ W ∧ Repr W a w := by
 let bad (i : Nat) := W ≤ i ∨ flag 5 a i = false
 have ex : ∃ i, bad i := ⟨W,Or.inl le_rfl⟩
 let n := Nat.find ex
 have hn : n ≤ W := Nat.find_min' ex (Or.inl le_rfl : bad W)
 have hi (i) : i < n ↔ i < W ∧ flag 5 a i = true := by
   constructor
   · intro hl; have := Nat.find_min ex hl; simp [bad] at this; exact this
   · rintro ⟨hw,hp⟩; by_contra! hh
     have back : ∀ d, n+d < W → flag 5 a (n+d) = true → flag 5 a n = true := by
       intro d; induction d with
       | zero => simp
       | succ d ih => intro hd hp; exact ih (by omega) (h _ hd hp)
     have hf := Nat.find_spec ex; change W ≤ n ∨ flag 5 a n = false at hf
     obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hh
     specialize back d hw hp; grind
 refine ⟨(List.range n).map (flag 1 a),by simpa,?_⟩
 intro i; by_cases hl : i < n
 · simp [List.getElem?_map,List.getElem?_eq_getElem,hl,(hi i).mp hl]
 · simp [List.getElem?_map,List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hl : (List.range n).length ≤ i),mt (hi i).mpr hl]

def witT (W j : E α) : Tree α (Option Bool) := .cond (.sub W j) (.ask (paddr 5 j) (.ask (paddr 1 j) (.ret (some true)) (.ret (some false))) (.ret none)) (.ret none)
def inputT (W i : E α) : Tree α (Option Bool) :=
 let s := E.add (.len) (.const 1); let b := E.add s (.len)
 .cond (.sub (.len) i) (.ret (some true)) (.cond (.sub s i) (.ret (some false)) (.cond (.sub b i) (.cond (.read (.sub i s)) (.ret (some true)) (.ret (some false))) (witT W (.sub i b))))
private theorem witSpec (x) (v : α → Nat) (W j a w) (h : Repr (E.val x v W) a w) : ((Tree.eval x v (witT W j)).run a) = w[E.val x v j]? := by
 rw [h _]; by_cases hj : E.val x v j < E.val x v W <;> cases h5 : flag 5 a (E.val x v j) <;> cases h1 : flag 1 a (E.val x v j) <;> simp_all [witT,paddr,Tree.eval,E.val,flag,Q.run,Nat.sub_eq_zero_iff_le, show (E.val x v W - E.val x v j ≠ 0) ↔ E.val x v j < E.val x v W by omega]
private theorem inputSpec (x) (v : α → Nat) (W i a w) (h : Repr (E.val x v W) a w) : ((Tree.eval x v (inputT W i)).run a) = (pairBits (x,w))[E.val x v i]? := by
 let k := E.val x v i
 have sub (m n : Nat) : m-n ≠ 0 ↔ n < m := by omega
 have hb : pairBits (x,w) = ((List.replicate x.length true ++ [false]) ++ x) ++ w := by simp [pairBits,encodeWord,List.append_assoc]
 simp only [inputT,Tree.eval,E.val,sub,hb,List.getElem?_append,List.length_append,List.length_replicate,List.length_cons,List.length_nil,Nat.zero_add,show E.val x v i = k from rfl]
 split_ifs <;> first | rfl | (simp_all [Q.run,List.getElem?_replicate,List.getElem?_eq_getElem] <;> done) | skip
 all_goals try omega
 all_goals first | exact witSpec _ _ _ _ _ _ h | skip
 all_goals
   have hl : k-(x.length+1) < x.length := by omega
   simp_all [Q.run,List.getElem?_eq_getElem]
private def pickT (j : β → E α) (d : β) : List β → Tree α β
 | [] => .ret d
 | b::bs => .ask (j b) (.ret b) (pickT j d bs)
def readT [Fintype β] (kind : Nat) (t : E α) (k : Nat) (i : E α) (d : β) :=
 pickT (fun b => E.addrE (.const kind) t (.const k) i (.const (num b))) d (all β)
@[simp] theorem eval_readT [Fintype β] (x) (v : α → Nat) (kind t k i) (d : β) :
 Tree.eval x v (readT kind t k i d) = readVal (kind,E.val x v t,k,E.val x v i) d := by
 unfold readT readVal; induction all β with
 | nil => rfl
 | cons b bs ih => simp only [pickT,Tree.eval,E.val_addrE,E.val,pick,ih]

def liftE : E α → E (Option α)
 | .var j => .var (some j) | .const n => .const n | .len => .len | .read i => .read (liftE i)
 | .add a b => .add (liftE a) (liftE b) | .sub a b => .sub (liftE a) (liftE b) | .mul a b => .mul (liftE a) (liftE b) | .cond c a b => .cond (liftE c) (liftE a) (liftE b)
@[simp] theorem liftSpec (x) (v : α → Nat) (j) (e : E α) : E.val x (fun o => o.elim j v) (liftE e) = E.val x v e := by induction e <;> simp_all [liftE,E.val]
def eqT [DecidableEq β] (p q : Tree α β) := p.bind fun b => q.bind fun c => .ret (decide (b=c))
@[simp] theorem eqSpec [DecidableEq β] (x v a) (p q : Tree α β) : ((eqT p q).eval x v).run a = true ↔ (p.eval x v).run a = (q.eval x v).run a := by simp [eqT,Tree.eval,Q.run]
def cellT (k : (tm V).K) (W i : E α) : Tree α Bool := by
 classical
 let inp : Tree α (Option ((tm V).Γ k)) := if e : k = (tm V).k₀ then e.symm ▸ ((inputT W i).bind fun z => .ret (z.map V.computation.inputAlphabet.invFun)) else .ret none
 exact eqT (readT 4 (.const 0) (num k) i none) inp
def perK (b W : E α) (k : (tm V).K) : Plan α := .range b (.tree (cellT V k (liftE W) (.var none)))
def initPlan (b W : E α) : Plan α := by
 classical exact .cat (.range (.sub W (.const 1)) (.tree (monoT (.var none)))) (.cat (.tree (eqT (readT 2 (.const 0) 0 (.const 0) (none : Option (tm V).Λ)) (.ret (some (tm V).main)))) (.cat (.tree (eqT (readT 3 (.const 0) 0 (.const 0) (tm V).initialState) (.ret (tm V).initialState))) (((all (tm V).K).map (perK V b W)).foldr Plan.cat .empty)))
private theorem allPlans (x) (v : α → Nat) (a) (ps : List (Plan α)) : (∀ q ∈ Plan.eval x v (ps.foldr Plan.cat .empty), q.run a = true) ↔ ∀ p ∈ ps, ∀ q ∈ p.eval x v, q.run a = true := by
 induction ps with | nil => simp [Plan.eval] | cons p ps ih => simp only [List.foldr_cons,Plan.eval,List.forall_mem_append,ih,List.forall_mem_cons]
private theorem monoSpec (x) (v : α → Nat) (a) (j : E α) : ((monoT j).eval x v).run a = true ↔ (flag 5 a (j.val x v+1) = true → flag 5 a (j.val x v) = true) := by cases h : flag 5 a (j.val x v+1) <;> simp_all [flag,monoT,paddr,Tree.eval,E.val,Q.run]
private theorem cellSpec (x) (v : α → Nat) (a W i k w) (h : Repr (E.val x v W) a w) : ((cellT V k W i).eval x v).run a = true ↔ (((row (tm V) 0).run a).s k (E.val x v i)).run a = ((initial V x w).stk k)[E.val x v i]? := by
 classical
 by_cases e : k = (tm V).k₀
 · subst k; simp [cellT,Tree.eval,E.val,Q.run,row,initial,initList,inputSpec x v W i a w h,List.getElem?_map]
 · simp [cellT,e,Tree.eval,E.val,Q.run,row,initial,initList]

def Pass (x) (v : α → Nat) (a) (p : Plan α) := ∀ q ∈ p.eval x v, q.run a = true
private theorem monoPart (x) (v : α → Nat) (a) (W : E α) : Pass x v a (.range (.sub W (.const 1)) (.tree (monoT (.var none)))) ↔ Mono (W.val x v) a := by
 simp only [Pass,Plan.eval,List.forall_mem_flatMap,List.mem_range,List.forall_mem_singleton,monoSpec,E.val,Option.elim_none,Mono]; apply forall_congr'; intro j; have h : j < W.val x v - 1 ↔ j+1 < W.val x v := by omega
 rw [h]
private theorem initGiven (x) (v : α → Nat) (a b W w) (h : Repr (E.val x v W) a w) : Pass x v a (initPlan V b W) ↔ Mono (E.val x v W) a ∧ matchV a ((row (tm V) 0).run a) (initial V x w) (b.val x v) := by
 classical
 unfold initPlan Pass
 rw [Plan.eval,List.forall_mem_append]
 apply and_congr (monoPart x v a W)
 simp only [Plan.eval,List.forall_mem_append,List.forall_mem_singleton,eqSpec,Tree.eval,eval_readT,E.val,Q.run,allPlans,List.forall_mem_map,mem_all,true_implies,perK,List.forall_mem_flatMap,List.mem_range,matchV,agrees,row,Q.run_seq,initial,initList]
 apply and_congr_right; intro _; apply and_congr_right; intro _
 apply forall_congr'; intro k; apply forall_congr'; intro i; apply forall_congr'; intro _
 simpa [row,Q.run,initial,initList,E.val] using cellSpec V x (fun o : Option α => o.elim i v) a (liftE W) (.var none) k w (by simpa using h)

theorem init_sound (x) (v : α → Nat) (a b W) (h : Pass x v a (initPlan V b W)) : ∃ w : List Bool, w.length ≤ W.val x v ∧ matchV a ((row (tm V) 0).run a) (initial V x w) (b.val x v) := by
 have hm : Mono (W.val x v) a := (monoPart x v a W).mp ((List.forall_mem_append.mp h).1)
 obtain ⟨w,hw,hr⟩ := decode hm
 exact ⟨w,hw,((initGiven V x v a b W w hr).mp h).2⟩

def pstore (cs : Nat → (tm V).Cfg) (w : List Bool) (s : Slot) := if s.1 = 5 then (if s.2.2.2 < w.length then 1 else 0) else store (tm V) cs w s
private theorem pRow (cs w t n) : matchV (writer (pstore V cs w)) ((row (tm V) t).run (writer (pstore V cs w))) (cs t) n := by
 let f := pstore V cs w
 have hl := read_hit f (2,t,0,0) none (cs t).l rfl
 have hv := read_hit f (3,t,0,0) (tm V).initialState (cs t).var rfl
 simp only [row,Q.run_seq,Q.run]; refine ⟨hl,hv,?_⟩; intro k i _
 apply read_hit; simp [pstore,store,num]; exact congrArg (fun j : (tm V).K => num ((cs t).stk j)[i]?) ((Fintype.equivFin (tm V).K).symm_apply_apply k)
theorem init_complete (x) (v : α → Nat) (b W) (w : List Bool) (hw : w.length ≤ E.val x v W) (cs : Nat → (tm V).Cfg) (hc : cs 0 = initial V x w) : ∃ a, Pass x v a (initPlan V b W) ∧ ∀ t n, matchV a ((row (tm V) t).run a) (cs t) n := by
 let a := writer (pstore V cs w)
 have hp (j) : flag 5 a j = true ↔ j < w.length := by simp [flag,a,pstore]
 have hr : Repr (W.val x v) a w := by
   intro i; simp only [hp]; by_cases hi : i < w.length
   · simp [hi,lt_of_lt_of_le hi hw,flag,a,pstore,store,List.getElem?_eq_getElem]
   · simp [hi,List.getElem?_eq_none (Nat.le_of_not_gt hi)]
 refine ⟨a,(initGiven V x v a b W w hr).mpr ⟨fun j _ hj => (hp j).mpr (by have := (hp _).mp hj; omega), hc ▸ pRow V cs w 0 _⟩,pRow V cs w⟩

private def GoodW (x w a t) := matchV a ((row (tm V) t).run a) (hist V x w t) (width V x t)
private theorem trans_good (x w a t) (ht : t < horizon V x) (g : GoodW V x w a t) : (∀ q ∈ trans V x t, q.run a = true) ↔ GoodW V x w a (t+1) := by
 apply equal_transfer; rw [Q.run_seq]; unfold hist; rw [Function.iterate_succ_apply']; apply next_correct
 have eqw : width V x (t+1) + loss (tm V) = width V x t := by
   unfold width; rw [show horizon V x-t = (horizon V x-(t+1))+1 by omega,Nat.add_mul]; omega
 rwa [eqw]
private theorem out_good (x w) (hw : w.length ≤ bound V x) (a) (g : GoodW V x w a (horizon V x)) : (out V x).run a = true ↔ V.verify (x,w) = true := by
 have hh := g.2.2 (tm V).k₁ 0 (by simp [width]); rw [hist_last _ _ _ hw] at hh
 simp only [finish,haltList,dif_pos rfl,List.getElem?_cons_zero] at hh
 simpa [out,cell,Q.run,hh] using (show _ ↔ _ from (Iff.rfl : V.verify (x,w) = true ↔ _))

/-- Drop-in replacement for the initial block of `Window.tests`. -/
theorem prefix_correct (x) (v : α → Nat) (b W : E α) (hb : b.val x v = width V x 0) (hW : W.val x v = bound V x) :
 V.Accepts x ↔ ∃ a, ∀ q ∈ Plan.eval x v (initPlan V b W) ++ ((List.range (horizon V x)).flatMap (trans V x) ++ [out V x]), q.run a = true := by
 constructor
 · rintro ⟨w,hw,hv⟩
   obtain ⟨a,hi,hr⟩ := init_complete V x v b W w (hW.symm ▸ hw) (hist V x w) rfl
   refine ⟨a,List.forall_mem_append.mpr ⟨hi,List.forall_mem_append.mpr ⟨List.forall_mem_flatMap.mpr ?_,?_⟩⟩⟩
   · intro t ht; exact (trans_good V x w a t (List.mem_range.mp ht) (hr t _)).mpr (hr _ _)
   · simpa using (out_good V x w hw a (hr _ _)).mpr hv
 · rintro ⟨a,h⟩; rw [List.forall_mem_append,List.forall_mem_append,List.forall_mem_flatMap] at h
   obtain ⟨w,hw,hi⟩ := init_sound V x v a b W h.1
   rw [hb] at hi; rw [hW] at hw
   have g (t) (ht : t ≤ horizon V x) : GoodW V x w a t := by
     induction t with
     | zero => exact hi
     | succ t ih => exact (trans_good V x w a t (by omega) (ih (by omega))).mp (h.2.1 _ (List.mem_range.mpr (by omega)))
   exact ⟨w,hw,(out_good V x w hw a (g _ le_rfl)).mp (h.2.2 _ (by simp))⟩
theorem prefix_sat (x) (v : α → Nat) (b W : E α) (hb : b.val x v = width V x 0) (hW : W.val x v = bound V x) :
 V.Accepts x ↔ (compile (Plan.eval x v (initPlan V b W) ++ ((List.range (horizon V x)).flatMap (trans V x) ++ [out V x]))).Satisfiable := by rw [compile_correct]; exact prefix_correct V x v b W hb hW
end
end Window.Stream.Prefix
end

-- TransitionTemplates
section
/- Reification of bounded tableau transitions. See LICENSE.openai. -/
namespace Window.Stream
open Turing TM2
noncomputable section
local instance kFinI3 (M : Turing.FinTM2) : Fintype M.K := M.kFin
local instance ΛFinI3 (M : Turing.FinTM2) : Fintype M.Λ := M.ΛFin
local instance σFinI3 (M : Turing.FinTM2) : Fintype M.σ := M.σFin
/-- Same query skeleton and related leaves (which may contain tapes). -/
inductive Sync (R : β → γ → Prop) : Q β → Q γ → Prop where
 | ret {a b} : R a b → Sync R (.ret a) (.ret b)
 | ask {j y n y' n'} : Sync R y y' → Sync R n n' → Sync R (.ask j y n) (.ask j y' n')
namespace Sync
theorem bind {R : β → γ → Prop} {S : δ → ε → Prop} {p q} (h : Sync R p q)
 (f : β → Q δ) (g : γ → Q ε) (hh : ∀ a b, R a b → Sync S (f a) (g b)) : Sync S (p.seq f) (q.seq g) := by
 induction h with | ret h => exact hh _ _ h | ask _ _ hy hn => exact .ask hy hn
theorem reflQ (q : Q β) : Sync Eq q q := by induction q with | ret _ => exact .ret rfl | ask _ _ _ ih jh => exact .ask ih jh
theorem eqQ {p q : Q β} (h : Sync Eq p q) : p=q := by induction h <;> congr
end Sync
private def pickT (j : β → E α) (d : β) : List β → Tree α β
 | [] => .ret d
 | b::bs => .ask (j b) (.ret b) (pickT j d bs)
def readT [Fintype β] (kind : Nat) (t : E α) (k : Nat) (i : E α) (d : β) :=
 pickT (fun b => E.addrE (.const kind) t (.const k) i (.const (num b))) d (all β)
@[simp] theorem eval_readT [Fintype β] (x) (v : α → Nat) (kind t k i) (d : β) :
 Tree.eval x v (readT kind t k i d) = readVal (kind,E.val x v t,k,E.val x v i) d := by
 unfold readT readVal; induction all β with
 | nil => rfl
 | cons b bs ih => simp only [pickT,Tree.eval,E.val_addrE,E.val,pick,ih]
abbrev TTape (α) (M : FinTM2) := (k : M.K) → E α → Tree α (Option (M.Γ k))
structure TView (α) (M : FinTM2) where
 l : Option M.Λ
 v : M.σ
 s : TTape α M
variable {M : FinTM2}
def TapeSpec (x) (v : α → Nat) (s : TTape α M) (p : Tape M) := ∀ k i, Tree.eval x v (s k i) = p k (E.val x v i)
def ViewSpec (x) (v : α → Nat) (a : TView α M) (b : View M) := a.l=b.l ∧ a.v=b.v ∧ TapeSpec x v a.s b.s
private def pushT (s : TTape α M) (k : M.K) (a : M.Γ k) : TTape α M :=
 Function.update s k (fun i => .cond i (s k (.sub i (.const 1))) (.ret (some a)))
private def popT (s : TTape α M) (k : M.K) : TTape α M := Function.update s k (fun i => s k (.add i (.const 1)))
private theorem pushSpec {x v} {s : TTape α M} {p} (h : TapeSpec x v s p) (k a) : TapeSpec x v (pushT s k a) (Function.update p k (fun | 0 => .ret (some a) | i+1 => p k i)) := by
 intro j i; by_cases e : j=k
 · subst j; simp only [pushT,Function.update_self,Tree.eval,h k _,E.val]; cases E.val x v i <;> simp
 · simpa [pushT,e] using h j i
private theorem popSpec {x v} {s : TTape α M} {p} (h : TapeSpec x v s p) (k) : TapeSpec x v (popT s k) (Function.update p k (fun i => p k (i+1))) := by
 intro j i; by_cases e : j=k
 · subst j; simpa only [popT,Function.update_self,E.val] using h k (.add i (.const 1))
 · simpa [popT,e] using h j i

def stepT (q : Stmt M.Γ M.Λ M.σ) (w : M.σ) (s : TTape α M) : Tree α (TView α M) := match q with
 | .push k f p => stepT p w (pushT s k (f w))
 | .peek k f p => (s k (.const 0)).bind fun z => stepT p (f w z) s
 | .pop k f p => (s k (.const 0)).bind fun z => stepT p (f w z) (popT s k)
 | .load f p => stepT p (f w) s
 | .branch f p r => if f w then stepT p w s else stepT r w s
 | .goto f => .ret ⟨some (f w),w,s⟩
 | .halt => .ret ⟨none,w,s⟩
private theorem stepSpec (x) (v : α → Nat) (q : Stmt M.Γ M.Λ M.σ) (w s p) (h : TapeSpec x v s p) :
 Sync (ViewSpec x v) (Tree.eval x v (stepT q w s)) (sstep q w p) := by
 induction q generalizing s p w with
 | push k f q ih => exact ih _ _ _ (pushSpec h _ _)
 | peek k f q ih => simp only [stepT,sstep,Tree.eval_bind,h k _,E.val]; apply (Sync.reflQ _).bind; rintro _ b rfl; exact ih _ _ _ h
 | pop k f q ih => simp only [stepT,sstep,Tree.eval_bind,h k _,E.val]; apply (Sync.reflQ _).bind; rintro _ b rfl; exact ih _ _ _ (popSpec h _)
 | load f q ih => exact ih _ _ _ h
 | branch f q r ih jh => cases e : f w <;> simp [stepT,sstep,e,ih _ _ _ h,jh _ _ _ h]
 | goto | halt => exact .ret ⟨rfl,rfl,h⟩

def nextT (a : TView α M) : Tree α (TView α M) := match a.l with
 | none => .ret a
 | some l => stepT (M.m l) a.v a.s
private theorem nextSpec (x) (v : α → Nat) (a : TView α M) (b) (h : ViewSpec x v a b) :
 Sync (ViewSpec x v) (Tree.eval x v (nextT a)) (next b) := by
 obtain ⟨hl,hv,hs⟩ := h
 cases e : b.l with
 | none => simp only [nextT,next,hl,e,Tree.eval]; exact .ret ⟨hl,hv,hs⟩
 | some l => simp only [nextT,next,hl,e,hv]; exact stepSpec _ _ _ _ _ _ hs
variable (M) [∀ k, Fintype (M.Γ k)]
def rowT (t : E α) : Tree α (TView α M) :=
 (readT 2 t 0 (.const 0) (none : Option M.Λ)).bind fun l =>
 (readT 3 t 0 (.const 0) M.initialState).bind fun w =>
 .ret ⟨l,w,fun k i => readT 4 t (num k) i none⟩
private theorem rowSpec (x) (v : α → Nat) (t) : Sync (ViewSpec x v) (Tree.eval x v (rowT M t)) (row M (E.val x v t)) := by
 simp only [rowT,row,Tree.eval_bind,eval_readT,E.val]
 apply (Sync.reflQ _).bind; rintro _ l rfl
 apply (Sync.reflQ _).bind; rintro _ w rfl
 apply Sync.ret; exact ⟨rfl,rfl,fun k i => eval_readT ..⟩
def succT (t : E α) := (rowT M t).bind nextT
private theorem succSpec (x) (v : α → Nat) (t) : Sync (ViewSpec x v) (Tree.eval x v (succT M t)) ((row M (E.val x v t)).seq next) := by
 rw [succT,Tree.eval_bind]; exact (rowSpec ..).bind _ _ (nextSpec x v)
def sameT [DecidableEq β] (a b : Tree α β) : Tree α Bool := a.bind fun u => b.bind fun w => .ret (decide (u=w))
@[simp] theorem eval_sameT [DecidableEq β] (x) (v : α → Nat) (a b : Tree α β) : Tree.eval x v (sameT a b) = same (Tree.eval x v a) (Tree.eval x v b) := by simp only [sameT,same,Tree.eval_bind,Tree.eval]
private def projectLabel (q : Tree α (TView α M)) : Tree α (Option M.Λ) := q.bind fun a => .ret a.l
omit [∀ k, Fintype (M.Γ k)] in
private theorem eval_projectLabel (x) (v : α → Nat) (q : Tree α (TView α M)) (r) (h : Sync (ViewSpec x v) (Tree.eval x v q) r) :
 Tree.eval x v (projectLabel M q) = field M r View.l := by
 rw [projectLabel,Tree.eval_bind]; apply Sync.eqQ; apply h.bind; intro a b hab
 exact .ret hab.1
def transLabel (t : E α) := by classical exact sameT (projectLabel M (succT M t)) (projectLabel M (rowT M (.add t (.const 1))))
@[simp] theorem eval_transLabel (x) (v : α → Nat) (t) : Tree.eval x v (transLabel M t) = (by classical exact same (field M ((row M (E.val x v t)).seq next) View.l) (field M (row M (E.val x v t+1)) View.l)) := by
 classical
 simp only [transLabel,eval_sameT,eval_projectLabel _ _ _ _ _ (succSpec ..),eval_projectLabel _ _ _ _ _ (rowSpec ..),E.val]
private def projectState (q : Tree α (TView α M)) : Tree α (M.σ) := q.bind fun a => .ret a.v
omit [∀ k, Fintype (M.Γ k)] in
private theorem eval_projectState (x) (v : α → Nat) (q : Tree α (TView α M)) (r) (h : Sync (ViewSpec x v) (Tree.eval x v q) r) :
 Tree.eval x v (projectState M q) = field M r View.v := by
 rw [projectState,Tree.eval_bind]; apply Sync.eqQ; apply h.bind; intro a b hab
 exact .ret hab.2.1
def transState (t : E α) := by classical exact sameT (projectState M (succT M t)) (projectState M (rowT M (.add t (.const 1))))
@[simp] theorem eval_transState (x) (v : α → Nat) (t) : Tree.eval x v (transState M t) = (by classical exact same (field M ((row M (E.val x v t)).seq next) View.v) (field M (row M (E.val x v t+1)) View.v)) := by
 classical
 simp only [transState,eval_sameT,eval_projectState _ _ _ _ _ (succSpec ..),eval_projectState _ _ _ _ _ (rowSpec ..),E.val]
private def projectCell (q : Tree α (TView α M)) (k : M.K) (i : E α) : Tree α (Option (M.Γ k)) := q.bind fun a => a.s k i
omit [∀ k, Fintype (M.Γ k)] in
private theorem eval_projectCell (x) (v : α → Nat) (q : Tree α (TView α M)) (r) (h : Sync (ViewSpec x v) (Tree.eval x v q) r) (k : M.K) (i : E α) :
 Tree.eval x v (projectCell M q k i) = cell M r k (E.val x v i) := by
 rw [projectCell,Tree.eval_bind]; apply Sync.eqQ; apply h.bind; intro a b hab
 rw [hab.2.2 k i]; exact Sync.reflQ _
def transCell (t : E α) (k : M.K) (i : E α) := by classical exact sameT (projectCell M (succT M t) k i) (projectCell M (rowT M (.add t (.const 1))) k i)
@[simp] theorem eval_transCell (x) (v : α → Nat) (t) (k : M.K) (i : E α) : Tree.eval x v (transCell M t k i) = (by classical exact same (cell M ((row M (E.val x v t)).seq next) k (E.val x v i)) (cell M (row M (E.val x v t+1)) k (E.val x v i))) := by
 classical
 simp only [transCell,eval_sameT,eval_projectCell _ _ _ _ _ (succSpec ..),eval_projectCell _ _ _ _ _ (rowSpec ..),E.val]

/-- Specialization preserves both the order and the syntax of all tests of a transition. -/
theorem transitionBlock (x) (v : α → Nat) (t : E α) (pos : Nat → E α) (b : Nat)
 (hp : ∀ j < b, (pos j).val x v = j) :
 [Tree.eval x v (transLabel M t),Tree.eval x v (transState M t)] ++
 ((all M.K).flatMap fun k => (List.range b).map fun i => Tree.eval x v (transCell M t k (pos i))) =
 equalRows M ((row M (t.val x v)).seq next) (row M (t.val x v+1)) b := by
 classical
 simp only [eval_transLabel,eval_transState,eval_transCell,equalRows]; congr 1
 apply List.flatMap_congr; intro k _; apply List.map_congr_left; intro j hj
 rw [hp j (List.mem_range.mp hj)]
end
end Window.Stream
end

-- VerifierPlan
section
/- Closed verification plan assembled from the prefix (math09) and transition (math08) templates. -/
namespace Window.Stream
open Turing OAI.BinPackingGames.Foundations Complexity CookLevin
noncomputable section
local instance kFinI4 (M : Turing.FinTM2) : Fintype M.K := M.kFin
local instance ΛFinI4 (M : Turing.FinTM2) : Fintype M.Λ := M.ΛFin
local instance σFinI4 (M : Turing.FinTM2) : Fintype M.σ := M.σFin
private def powE (e : E α) : Nat → E α | 0 => .const 1 | n+1 => .mul (powE e n) e
private theorem vp (e : E α) (n x v) : (powE e n).val x v = (e.val x v)^n := by induction n <;> simp_all [powE,E.val,pow_succ]
private theorem reifiable (p : Polynomial Nat) (e : E α) : ∃ q : E α, ∀ x v, q.val x v = p.eval (e.val x v) := by
 induction p using Polynomial.induction_on' with
 | add p q hp hq => obtain ⟨a,ha⟩ := hp; obtain ⟨b,hb⟩ := hq; exact ⟨.add a b,by simp [E.val,ha,hb]⟩
 | monomial n c => exact ⟨.mul (.const c) (powE e n),by simp [E.val,vp]⟩
private def polE (p : Polynomial Nat) (e : E α) := (reifiable p e).choose
private theorem peval (p : Polynomial Nat) (e : E α) (x v) : (polE p e).val x v = p.eval (e.val x v) := (reifiable p e).choose_spec ..
variable (V : NPVerifier)
local instance : ∀ k, Fintype ((tm V).Γ k) := V.finiteAlphabet
private def witE : E α := polE V.witnessBound .len
private def horE : E α := polE V.computation.time (.add (.add (.mul (.const 2) .len) (witE V)) (.const 1))
private def widE (t : E α) := E.add (.mul (.sub (horE V) t) (.const (loss (tm V)))) (.const 1)
private theorem hv (x) (v : α → Nat) : (horE V).val x v = horizon V x := by simp [horE,witE,peval,E.val,horizon,CookLevin.NPVerifier.horizon]
private theorem wv (t : E α) (x v) : (widE V t).val x v = width V x (t.val x v) := by simp [widE,E.val,hv,width]
private def block (t : E α) : Plan α := .cat (.tree (transLabel (tm V) t)) (.cat (.tree (transState (tm V) t)) (((all (tm V).K).map fun k => Plan.range (widE V (.add t (.const 1))) (.tree (transCell (tm V) (t.rename some) k (.var none)))).foldr Plan.cat .empty))
private theorem fold_eval (ps : List (Plan α)) (x v) : (ps.foldr Plan.cat .empty).eval x v = ps.flatMap (Plan.eval x v) := by induction ps <;> simp_all [Plan.eval]
private theorem mapSingle (l : List γ) (f : γ → β) : (l.map fun j => [f j]).flatten = l.map f := by induction l <;> simp_all
private theorem block_eval (t : E α) (x v) : (block V t).eval x v = trans V x (t.val x v) := by
 classical
 simp [block,Plan.eval,fold_eval,List.flatMap_map,Function.comp_def,wv,E.val,trans,equalRows,List.flatMap_def,List.map_map,mapSingle]
private def lastT : Tree α Bool := by classical exact sameT (Prefix.readT 4 (horE V) (num (tm V).k₁) (.const 0) none) (.ret (some (V.computation.outputAlphabet.invFun true)))
private theorem last_run (x) (v : α → Nat) (a) : ((lastT V).eval x v).run a = (out V x).run a := by classical simp [lastT,Tree.eval,hv,E.val,out,cell,row,same,Q.run]
def verifierPlan : Plan Empty := .cat (Prefix.initPlan V (widE V (.const 0)) (witE V)) (.cat (.range (horE V) (block V (.var none))) (.tree (lastT V)))
theorem verifierPlan_correct (x) : V.Accepts x ↔ ((verifierPlan V).packed x).Satisfiable := by
 rw [Plan.packed,pack_iff,forest_iff,Prefix.prefix_correct V x Plan.noRef (widE V (.const 0)) (witE V) (by simp [wv,E.val]) (by simp [witE,peval,E.val,bound])]
 simp only [verifierPlan,Plan.eval,hv,block_eval,E.val,Option.elim_none,List.forall_mem_append,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true,last_run]
end
end Window.Stream
end

-- WindowProducer
section
/- Private finite-register tableau producer. Based on the OpenAI API, see LICENSE.openai. -/
namespace Window.Stream
open Compact.Reg OAI.BinPackingGames.Foundations Complexity CookLevin
noncomputable section
def newFormula (V : NPVerifier) := (verifierPlan V).packed
def emitProgram (V : NPVerifier) := (verifierPlan V).program.finite
theorem emit_words (V : NPVerifier) (x) : ((emitProgram V).exec x S.init).words = formulaWords (newFormula V x) := by rw [emitProgram,P.finite_exec]; exact Plan.program_words _ _
theorem newFormula_equiv (V : NPVerifier) (x) : (newFormula V x).Satisfiable ↔ (Window.formula V x).Satisfiable := (verifierPlan_correct _ _).symm.trans (Window.correct ..)
theorem emit_work_of (h : Resources.AllE) (V : NPVerifier) : ∃ P : Polynomial Nat, ∀ x, ((emitProgram V).exec x S.init).work ≤ P.eval x.length := by
 obtain ⟨p,hp⟩ := Resources.program_work h (verifierPlan V); exact ⟨p,fun x => by rw [emitProgram,P.finite_exec]; exact hp x⟩
end
end Window.Stream
end

-- AllExprBudget
section
namespace Window.Stream.Resources
open Compact.Reg Polynomial
noncomputable section
private def B : Poly := 10+10*X+4*X*X
private theorem combineW (op : E.Op) (d x) (s : S Nat) (m : Nat) (h : ∀ j, s.reg j ≤ m) :
 ((op.combine d).exec x s).work ≤ s.work+B.eval m := by
 have h0 := h d; have h1 := h (d+1); have h2 := h (d+2)
 have hm := Nat.mul_le_mul h1 (Nat.add_le_add_left (Nat.mul_le_mul_left 3 h2) 2)
 cases op <;> simp [E.Op.combine,P.exec,copy_exec,accumulate_exec,minus_exec,madd_exec,S.put, B] <;> nlinarith
private theorem combineO (op : E.Op) {i j n : Nat} (hi : i ≤ n) (hj : j ≤ n) : op.eval i j ≤ B.eval n := by
 have hh := Nat.mul_le_mul hi hj
 cases op <;> simp [E.Op.eval,B] <;> first | omega | nlinarith
private theorem binBound (op : E.Op) (l r e : E α)
 (eqc : ∀ (ref : α → Nat) d, e.code ref d = .seq (l.code ref (d+1)) (.seq (r.code ref (d+2)) (op.combine d)))
 {p q : Poly} (hp : ELimit l p) (hq : ELimit r q) : ∃ f, ELimit e f := by
 let k := X+p+q
 refine ⟨p+q+q.comp (X+p)+B.comp k,?_⟩
 intro x ref d s a m hd hl hv ham hr
 let t := (l.code ref (d+1)).exec x s
 let u := (r.code ref (d+2)).exec x t
 have hd1 j := Nat.lt_succ_of_lt (hd j)
 have hd2 j := Nat.lt_succ_of_lt (hd1 j)
 obtain ⟨ot,rt,wt⟩ := hp x ref (d+1) s a m hd1 hl hv ham hr
 change t.reg _ ≤ _ at ot; change ∀ j, t.reg j ≤ _ at rt; change t.work ≤ _ at wt
 have ft := (E.code_spec l x ref (d+1) hd1 s).2.1
 have vt (j) : t.reg (ref j) ≤ a := (ft _ (hd1 j)).le.trans (hv j)
 obtain ⟨ou,ru,wu⟩ := hq x ref (d+2) t a _ hd2 hl vt (by omega) rt
 change u.reg _ ≤ _ at ou; change ∀ j, u.reg j ≤ _ at ru; change u.work ≤ _ at wu
 have fu := (E.code_spec r x ref (d+2) hd2 t).2.1
 have hleft : u.reg (d+1) ≤ p.eval a := (fu _ (by omega)).le.trans ot
 have co := combineO op (n:=k.eval a) (hleft.trans (by simp [k]; omega)) (ou.trans (by simp [k]))
 have pam := mono p ham; have qam := mono q ham
 have cw := combineW op d x u (k.eval m) (fun j => (ru j).trans (by simp [k]; omega))
 have wq := mono q (Nat.add_le_add_left pam m)
 rw [eqc]; change ((op.combine d).exec x u).reg d ≤ _ ∧ (∀ j, ((op.combine d).exec x u).reg j ≤ _) ∧ _
 rw [(E.combine_spec op d x u).1,Function.update_self]
 refine ⟨?_,?_,?_⟩
 · simp; omega
 · intro j; by_cases h : j=d
   · subst j; simp; omega
   · rw [Function.update_of_ne h]; have := ru j; simp; omega
 · change ((op.combine d).exec x u).work ≤ _; simp; omega

theorem all_expr : AllE := by
 intro α e
 induction e with
 | var j =>
   refine ⟨2+4*X,?_⟩; intro x ref d s a m hd hl hv ham hr
   have h := hv j; have g := hr d
   simp [E.code,copy_exec x s (Nat.ne_of_lt (hd j))]; refine ⟨by omega,?_,by omega⟩
   intro i; by_cases H : i=d <;> simp [H,Function.update_of_ne] <;> have := hr i <;> omega
 | const n =>
   refine ⟨1+C n+X,?_⟩; intro x ref d s a m hd hl hv ham hr
   have g := hr d
   simp [E.code,E.bump_exec]; refine ⟨by omega,?_,by omega⟩; intro i; by_cases H : i=d <;> simp [H,Function.update_of_ne] <;> have := hr i <;> omega
 | len =>
   refine ⟨1+2*X,?_⟩; intro x ref d s a m hd hl hv ham hr
   have g := hr d
   simp [E.code,P.exec,S.put]; refine ⟨by omega,?_,by omega⟩
   intro i; by_cases H : i=d <;> simp [H,Function.update_of_ne] <;> have := hr i <;> omega
 | add l r il ir | sub l r il ir | mul l r il ir =>
   obtain ⟨p,hp⟩ := il; obtain ⟨q,hq⟩ := ir
   first | exact binBound .add l r _ (fun _ _ => rfl) hp hq | exact binBound .sub l r _ (fun _ _ => rfl) hp hq | exact binBound .mul l r _ (fun _ _ => rfl) hp hq
 | read i ih =>
   obtain ⟨p,hp⟩ := ih; refine ⟨1+X+3*p,?_⟩
   intro x ref d s a m hd hl hv ham hr
   let t := (i.code ref d).exec x s
   obtain ⟨o,r,w⟩ := hp x ref d s a m hd hl hv ham hr
   change t.reg d ≤ _ at o; change ∀ j, t.reg j ≤ _ at r; change t.work ≤ _ at w
   have pam := mono p ham
   change (t.put d _ _).reg d ≤ _ ∧ (∀ j, (t.put d _ _).reg j ≤ _) ∧ (t.put d _ _).work ≤ _
   simp [S.put]; constructor
   · split <;> omega
   · constructor
     · intro j; by_cases H : j=d
       · subst j; simp; split <;> omega
       · rw [Function.update_of_ne H]; have := r j; omega
     · change t.work + (1+t.reg d+t.reg d+x.length) ≤ _; omega
 | cond c y n ic iy inn =>
   obtain ⟨p,hp⟩ := ic; obtain ⟨q,hq⟩ := iy; obtain ⟨r,hr⟩ := inn
   let k := q+r
   refine ⟨1+p+k+k.comp (X+p),?_⟩
   intro x ref d s a m hd hl hv ham hs
   let t := (c.code ref d).exec x s
   obtain ⟨_,rs,ws⟩ := hp x ref d s a m hd hl hv ham hs
   change ∀ j, t.reg j ≤ _ at rs; change t.work ≤ _ at ws
   have vf (j) : t.reg (ref j) ≤ a := ((E.code_spec c x ref d hd s).2.1 _ (hd j)).le.trans (hv j)
   have pam := mono p ham
   have branch (b : E α) {f : Poly} (hb : ELimit b f) (le : ∀ z, f.eval z ≤ k.eval z) :
      let u := (b.code ref d).exec x (t.tick 1)
      u.reg d ≤ (1+p+k+k.comp (X+p)).eval a ∧ (∀ j, u.reg j ≤ m+(1+p+k+k.comp (X+p)).eval a) ∧ u.work ≤ s.work+(1+p+k+k.comp (X+p)).eval m := by
     obtain ⟨o,R,w⟩ := hb x ref d (t.tick 1) a (m+p.eval a) hd hl vf (by omega) rs
     have la := le a; have lm := (le _).trans (mono k (Nat.add_le_add_left pam m))
     change ((b.code ref d).exec x (t.tick 1)).work ≤ t.work+1+_ at w
     dsimp only; simp; refine ⟨by omega,fun j => ?_,by omega⟩; have := R j; omega
   simp only [E.code,P.exec]; split
   · exact branch y hq (by simp [k])
   · exact branch n hr (by simp [k])
end
end Window.Stream.Resources
end

-- WindowEmitter
section
/- Private finite-register tableau producer. Based on the OpenAI API, see LICENSE.openai. -/
namespace Window.Stream
open Compact.Reg OAI.BinPackingGames.Foundations Complexity CookLevin
noncomputable section
theorem emit_work (V : NPVerifier) : ∃ P : Polynomial Nat, ∀ x, ((emitProgram V).exec x S.init).work ≤ P.eval x.length := emit_work_of Resources.all_expr V
end
end Window.Stream
end

-- OAI.Computability.BinPacking.CookLevin.Completeness
section
/- Private redesign of the OpenAI reduction; see LICENSE.openai. -/
namespace OAI.BinPackingGames.Foundations.Complexity.CookLevin.Completeness
open Window.Stream
noncomputable def verifierReduction (V : NPVerifier) : PolynomialThreeSATReduction V.Accepts where
 reduce := newFormula V
 computation := Compact.Reg.realize (emitProgram V) (newFormula V) formulaBits (emit_work V).choose (fun x => congrArg encodeWords (emit_words V x)) (emit_work V).choose_spec
 correct := verifierPlan_correct V

theorem verifierReduction_finiteAlphabet (V : NPVerifier) : MachineFiniteAlphabet.FiniteAlphabet (verifierReduction V).computation.tm := by
 intro k; change Finite Bool; infer_instance

theorem threeSATReduction (language : List Bool → Prop) (membership : InNP language) :
    ∃ source : PolynomialThreeSATReduction language,
      MachineFiniteAlphabet.FiniteAlphabet source.computation.tm := by
 obtain ⟨V,h⟩ := membership
 exact ⟨⟨_, (verifierReduction V).computation, fun x => (h x).trans ((verifierReduction V).correct x)⟩, verifierReduction_finiteAlphabet V⟩
end OAI.BinPackingGames.Foundations.Complexity.CookLevin.Completeness
end

/- wp-unique-games-conjecture.R1.H1: every NP language reduces in polynomial time, with finite
stack alphabets, to 3-Coloring of n*n adjacency-matrix bit strings.

Route: the finite-stack Cook–Levin reduction `threeSATReduction` (private redesign of the OpenAI
reduction in OpenAI/math commit 3344da59991ed94f9ba711217b29c1d760badfa6, see LICENSE.openai),
then the textbook 3SAT → 3-Coloring gadget (palette triangle, variable pairs, two OR-triangles per
clause), emitted by a word-stream program as a padded adjacency matrix whose odd rows/columns are
isolated vertices. -/

namespace Col3
open OAI.BinPackingGames.Foundations

def ind (p q a b : Nat) : Nat := (if p = a then 1 else 0) * (if q = b then 1 else 0)
theorem ind_ne {p q a b : Nat} (h : ind p q a b ≠ 0) : p = a ∧ q = b := by
  unfold ind at h; by_cases h1 : p = a <;> by_cases h2 : q = b <;> simp_all
theorem ind_self (a b : Nat) : ind a b a b = 1 := by simp [ind]

section
variable (w : Nat → Nat)
def lv (j t : Nat) : Nat := 3 + 2 * w (2 + 2*t + 6*j) + (1 - w (3 + 2*t + 6*j))
def bs (j : Nat) : Nat := 3 + 2 * w 0 + 6 * j
def size : Nat := 3 + 2 * w 0 + 6 * w 1
def varCnt (p q i : Nat) : Nat := ind p q (3+2*i) (3+2*i+1) + ind p q (3+2*i) 2 + ind p q (3+2*i+1) 2
def clCnt (p q j : Nat) : Nat :=
  ind p q (lv w j 0) (bs w j) +
  ind p q (lv w j 1) (bs w j+1) +
  ind p q (bs w j) (bs w j+1) +
  ind p q (bs w j+1) (bs w j+2) +
  ind p q (bs w j) (bs w j+2) +
  ind p q (bs w j+2) (bs w j+3) +
  ind p q (lv w j 2) (bs w j+4) +
  ind p q (bs w j+3) (bs w j+4) +
  ind p q (bs w j+4) (bs w j+5) +
  ind p q (bs w j+3) (bs w j+5) +
  ind p q (bs w j+5) (1) +
  ind p q (bs w j+5) (2)
def cnt (p q : Nat) : Nat := ind p q 0 1 + ind p q 1 2 + ind p q 0 2 +
  (∑ i ∈ Finset.range (w 0), varCnt p q i) + ∑ j ∈ Finset.range (w 1), clCnt w p q j
def Col (c : Nat → Fin 3) : Prop := ∀ p q, p < size w → q < size w → cnt w p q ≠ 0 → c p ≠ c q

structure Enc (F : Target.Formula) : Prop where
  v : w 0 = F.variables
  c : w 1 = F.clauses.length
  idx : ∀ j (hj : j < F.clauses.length) t (ht : t < 3),
    w (2 + 2*t + 6*j) = ((F.clauses[j])[t]'ht).variableIndex.val
  sgn : ∀ j (hj : j < F.clauses.length) t (ht : t < 3),
    w (3 + 2*t + 6*j) = if ((F.clauses[j])[t]'ht).positive then 1 else 0
end

theorem other : ∀ x T F B : Fin 3, T ≠ F → F ≠ B → T ≠ B → x ≠ T → x ≠ B → x = F := by decide
theorem gateF : ∀ u v o F : Fin 3, F ≠ u → F ≠ v → u ≠ v → v ≠ o → u ≠ o → o = F := by decide

theorem cnt_var {w : Nat → Nat} {p q i : Nat} (hi : i < w 0) (h : varCnt p q i ≠ 0) : cnt w p q ≠ 0 := by
  have := Finset.single_le_sum (f := varCnt p q) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hi)
  unfold cnt; omega
theorem cnt_cl {w : Nat → Nat} {p q j : Nat} (hj : j < w 1) (h : clCnt w p q j ≠ 0) : cnt w p q ≠ 0 := by
  have := Finset.single_le_sum (f := clCnt w p q) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hj)
  unfold cnt; omega

theorem sound (w : Nat → Nat) (F : Target.Formula) (hw : Enc w F) (c : Nat → Fin 3) (hc : Col w c) :
    F.Satisfiable := by
  obtain ⟨V, cs⟩ := F
  have hv := hw.v; have hcl := hw.c
  simp only at hv hcl
  have sz : size w = 3 + 2*V + 6*cs.length := by simp [size, hv, hcl]
  have E (p q) (hp : p < 3 + 2*V + 6*cs.length) (hq : q < 3 + 2*V + 6*cs.length) (h : cnt w p q ≠ 0) :
      c p ≠ c q := hc p q (sz ▸ hp) (sz ▸ hq) h
  have e01 : c 0 ≠ c 1 := E 0 1 (by omega) (by omega) (by unfold cnt; rw [ind_self]; omega)
  have e12 : c 1 ≠ c 2 := E 1 2 (by omega) (by omega) (by unfold cnt; rw [ind_self]; omega)
  have e02 : c 0 ≠ c 2 := E 0 2 (by omega) (by omega) (by unfold cnt; rw [ind_self]; omega)
  have vB (i) (hi : i < V) : c (3+2*i) ≠ c 2 :=
    E _ _ (by omega) (by omega) (cnt_var (hv ▸ hi) (by unfold varCnt; rw [ind_self]; omega))
  have vB' (i) (hi : i < V) : c (3+2*i+1) ≠ c 2 :=
    E _ _ (by omega) (by omega) (cnt_var (hv ▸ hi) (by unfold varCnt; rw [ind_self]; omega))
  have vN (i) (hi : i < V) : c (3+2*i) ≠ c (3+2*i+1) :=
    E _ _ (by omega) (by omega) (cnt_var (hv ▸ hi) (by unfold varCnt; rw [ind_self]; omega))
  refine ⟨fun i => decide (c (3+2*i.val) = c 0), fun cl hmem => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
  have hjw : j < w 1 := hcl ▸ hj
  have lvlt (t) (ht : t < 3) : lv w j t < 3 + 2*V + 6*cs.length := by
    have hi := hw.idx j hj t ht; simp only at hi
    have := ((cs[j])[t]'ht).variableIndex.isLt
    unfold lv; rw [hi]; omega
  have blt (k) (hk : k < 6) : bs w j + k < 3 + 2*V + 6*cs.length := by
    have : j + 1 ≤ cs.length := hj
    unfold bs; rw [hv]; omega
  have b0 : bs w j < 3 + 2*V + 6*cs.length := by simpa using blt 0 (by omega)
  have lit (t) (ht : t < 3)
      (hf : ((cs[j])[t]'ht).eval (fun i => decide (c (3+2*i.val) = c 0)) = false) : c (lv w j t) = c 1 := by
    have hi := hw.idx j hj t ht; have hs := hw.sgn j hj t ht
    simp only at hi hs
    have hlt := ((cs[j])[t]'ht).variableIndex.isLt
    unfold lv; rw [hi, hs]
    simp only [Target.Literal.eval] at hf
    revert hf hlt
    generalize ((cs[j])[t]'ht).positive = P
    generalize ((cs[j])[t]'ht).variableIndex.val = i
    intro hlt hf
    have hv1 := vB i hlt; have hv2 := vB' i hlt; have hn := vN i hlt
    cases P <;> simp at hf ⊢
    · exact other _ _ _ _ e01 e12 e02 (fun h => hn (hf.trans h.symm)) hv2
    · exact other _ _ _ _ e01 e12 e02 hf hv1
  by_contra hfalse
  simp only [Target.Clause.eval, Bool.or_eq_true, not_or, Bool.not_eq_true] at hfalse
  obtain ⟨⟨h0, h1⟩, h2⟩ := hfalse
  have l0 : c (lv w j 0) = c 1 := lit 0 (by omega) h0
  have l1 : c (lv w j 1) = c 1 := lit 1 (by omega) h1
  have l2 : c (lv w j 2) = c 1 := lit 2 (by omega) h2
  have ed (p q) (hp : p < 3 + 2*V + 6*cs.length) (hq : q < 3 + 2*V + 6*cs.length) (h : clCnt w p q j ≠ 0) :
      c p ≠ c q := E p q hp hq (cnt_cl hjw h)
  have g1 := gateF (c (bs w j)) (c (bs w j+1)) (c (bs w j+2)) (c 1)
    (by rw [← l0]; exact ed _ _ (lvlt 0 (by omega)) b0 (by unfold clCnt; rw [ind_self]; omega))
    (by rw [← l1]; exact ed _ _ (lvlt 1 (by omega)) (blt 1 (by omega)) (by unfold clCnt; rw [ind_self]; omega))
    (ed _ _ b0 (blt 1 (by omega)) (by unfold clCnt; rw [ind_self]; omega))
    (ed _ _ (blt 1 (by omega)) (blt 2 (by omega)) (by unfold clCnt; rw [ind_self]; omega))
    (ed _ _ b0 (blt 2 (by omega)) (by unfold clCnt; rw [ind_self]; omega))
  have g2 := gateF (c (bs w j+3)) (c (bs w j+4)) (c (bs w j+5)) (c 1)
    (by rw [← g1]; exact ed _ _ (blt 2 (by omega)) (blt 3 (by omega)) (by unfold clCnt; rw [ind_self]; omega))
    (by rw [← l2]; exact ed _ _ (lvlt 2 (by omega)) (blt 4 (by omega)) (by unfold clCnt; rw [ind_self]; omega))
    (ed _ _ (blt 3 (by omega)) (blt 4 (by omega)) (by unfold clCnt; rw [ind_self]; omega))
    (ed _ _ (blt 4 (by omega)) (blt 5 (by omega)) (by unfold clCnt; rw [ind_self]; omega))
    (ed _ _ (blt 3 (by omega)) (blt 5 (by omega)) (by unfold clCnt; rw [ind_self]; omega))
  exact ed _ _ (blt 5 (by omega)) (by omega) (by unfold clCnt; rw [ind_self]; omega) g2

def lc (b : Bool) : Fin 3 := if b then 0 else 1
def gate : Bool → Bool → Fin 3 × Fin 3 × Fin 3
  | false, false => (0, 2, 1) | true, false => (1, 2, 0) | false, true => (2, 1, 0) | true, true => (1, 2, 0)
theorem gadget_ok (x y z : Bool) (h : ((x || y) || z) = true) :
    lc x ≠ (gate x y).1 ∧ lc y ≠ (gate x y).2.1 ∧ (gate x y).1 ≠ (gate x y).2.1 ∧
    (gate x y).2.1 ≠ (gate x y).2.2 ∧ (gate x y).1 ≠ (gate x y).2.2 ∧ (gate x y).2.2 ≠ (gate (x||y) z).1 ∧
    lc z ≠ (gate (x||y) z).2.1 ∧ (gate (x||y) z).1 ≠ (gate (x||y) z).2.1 ∧
    (gate (x||y) z).2.1 ≠ (gate (x||y) z).2.2 ∧ (gate (x||y) z).1 ≠ (gate (x||y) z).2.2 ∧
    (gate (x||y) z).2.2 ≠ 1 ∧ (gate (x||y) z).2.2 ≠ 2 := by
  revert h; cases x <;> cases y <;> cases z <;> decide

section
variable (w : Nat → Nat) (a : Nat → Bool)
def lt (j t : Nat) : Bool := if w (3 + 2*t + 6*j) = 1 then a (w (2 + 2*t + 6*j)) else !a (w (2 + 2*t + 6*j))
def gv (j k : Nat) : Fin 3 :=
  if k = 0 then (gate (lt w a j 0) (lt w a j 1)).1 else if k = 1 then (gate (lt w a j 0) (lt w a j 1)).2.1
  else if k = 2 then (gate (lt w a j 0) (lt w a j 1)).2.2
  else if k = 3 then (gate (lt w a j 0 || lt w a j 1) (lt w a j 2)).1
  else if k = 4 then (gate (lt w a j 0 || lt w a j 1) (lt w a j 2)).2.1
  else (gate (lt w a j 0 || lt w a j 1) (lt w a j 2)).2.2
def col (p : Nat) : Fin 3 :=
  if h : p < 3 then ⟨p, h⟩ else if p < 3 + 2 * w 0 then
    (if (p-3) % 2 = 0 then lc (a ((p-3)/2)) else lc (!a ((p-3)/2)))
  else gv w a ((p - (3 + 2*w 0))/6) ((p - (3 + 2*w 0)) % 6)
theorem col_pos (i) (hi : i < w 0) : col w a (3+2*i) = lc (a i) := by
  unfold col; rw [dif_neg (by omega), if_pos (by omega), if_pos (by omega), show (3+2*i-3)/2 = i by omega]
theorem col_neg (i) (hi : i < w 0) : col w a (3+2*i+1) = lc (!a i) := by
  unfold col; rw [dif_neg (by omega), if_pos (by omega), if_neg (by omega), show (3+2*i+1-3)/2 = i by omega]
theorem col_cl {j} (hj : j < w 1) (k) (hk : k < 6) : col w a (bs w j + k) = gv w a j k := by
  unfold col bs; rw [dif_neg (by omega), if_neg (by omega), show (3+2*w 0+6*j+k-(3+2*w 0))/6 = j by omega,
    show (3+2*w 0+6*j+k-(3+2*w 0)) % 6 = k by omega]
theorem col_lv (x s : Nat) (hx : x < w 0) (hs : s = 0 ∨ s = 1) :
    col w a (3 + 2*x + (1 - s)) = lc (if s = 1 then a x else !a x) := by
  rcases hs with rfl | rfl
  · simpa using col_neg w a x hx
  · simpa using col_pos w a x hx
end

theorem complete (w : Nat → Nat) (F : Target.Formula) (hw : Enc w F) (hs : F.Satisfiable) : ∃ c, Col w c := by
  obtain ⟨V, cs⟩ := F
  obtain ⟨A, hA⟩ := hs
  have hv := hw.v; have hcl := hw.c
  simp only at hv hcl
  let a : Nat → Bool := fun n => if h : n < V then A ⟨n, h⟩ else false
  have hlt (j) (hj : j < cs.length) (t) (ht : t < 3) : lt w a j t = ((cs[j])[t]'ht).eval A := by
    have hi := hw.idx j hj t ht; have hs := hw.sgn j hj t ht; simp only at hi hs
    unfold lt; rw [hi, hs]; unfold Target.Literal.eval
    have := ((cs[j])[t]'ht).variableIndex.isLt
    cases ((cs[j])[t]'ht).positive <;> simp [a, this]
  have hsat (j) (hj : j < cs.length) : ((lt w a j 0 || lt w a j 1) || lt w a j 2) = true := by
    rw [hlt j hj 0 (by omega), hlt j hj 1 (by omega), hlt j hj 2 (by omega)]; exact hA _ (List.getElem_mem hj)
  refine ⟨col w a, fun p q hp hq h => ?_⟩
  have col0 : col w a 0 = 0 := rfl
  have col1 : col w a 1 = 1 := rfl
  have col2 : col w a 2 = 2 := rfl
  unfold cnt at h
  have h5 : ind p q 0 1 ≠ 0 ∨ ind p q 1 2 ≠ 0 ∨ ind p q 0 2 ≠ 0 ∨
      (∑ i ∈ Finset.range (w 0), varCnt p q i) ≠ 0 ∨ (∑ j ∈ Finset.range (w 1), clCnt w p q j) ≠ 0 := by omega
  rcases h5 with h | h | h | h | h
  · obtain ⟨rfl, rfl⟩ := ind_ne h; rw [col0, col1]; decide
  · obtain ⟨rfl, rfl⟩ := ind_ne h; rw [col1, col2]; decide
  · obtain ⟨rfl, rfl⟩ := ind_ne h; rw [col0, col2]; decide
  · obtain ⟨i, hi, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    rw [Finset.mem_range] at hi
    unfold varCnt at h
    have h3 : ind p q (3+2*i) (3+2*i+1) ≠ 0 ∨ ind p q (3+2*i) 2 ≠ 0 ∨ ind p q (3+2*i+1) 2 ≠ 0 := by omega
    rcases h3 with h | h | h <;> obtain ⟨rfl, rfl⟩ := ind_ne h
    · rw [col_pos w a i hi, col_neg w a i hi]; cases a i <;> decide
    · rw [col_pos w a i hi, col2]; cases a i <;> decide
    · rw [col_neg w a i hi, col2]; cases a i <;> decide
  · obtain ⟨j, hjw, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    rw [Finset.mem_range] at hjw
    have hj : j < cs.length := hcl ▸ hjw
    have G := gadget_ok _ _ _ (hsat j hj)
    have col_lit (t) (ht : t < 3) : col w a (lv w j t) = lc (lt w a j t) := by
      have hi := hw.idx j hj t ht; have hs := hw.sgn j hj t ht; simp only at hi hs
      have hx : w (2 + 2*t + 6*j) < w 0 := by rw [hi, hv]; exact ((cs[j])[t]'ht).variableIndex.isLt
      unfold lv lt
      exact col_lv w a _ _ hx (by rw [hs]; split <;> simp)
    have col_b0 : col w a (bs w j) = gv w a j 0 := by simpa using col_cl w a hjw 0 (by omega)
    unfold clCnt at h
    have h12 : ind p q (lv w j 0) (bs w j) ≠ 0 ∨ ind p q (lv w j 1) (bs w j+1) ≠ 0 ∨ ind p q (bs w j) (bs w j+1) ≠ 0 ∨ ind p q (bs w j+1) (bs w j+2) ≠ 0 ∨ ind p q (bs w j) (bs w j+2) ≠ 0 ∨ ind p q (bs w j+2) (bs w j+3) ≠ 0 ∨ ind p q (lv w j 2) (bs w j+4) ≠ 0 ∨ ind p q (bs w j+3) (bs w j+4) ≠ 0 ∨ ind p q (bs w j+4) (bs w j+5) ≠ 0 ∨ ind p q (bs w j+3) (bs w j+5) ≠ 0 ∨ ind p q (bs w j+5) (1) ≠ 0 ∨ ind p q (bs w j+5) (2) ≠ 0 := by omega
    rcases h12 with h|h|h|h|h|h|h|h|h|h|h|h
    · obtain ⟨rfl, rfl⟩ := ind_ne h; rw [col_lit 0 (by omega), col_b0]; exact G.1
    · obtain ⟨rfl, rfl⟩ := ind_ne h; rw [col_lit 1 (by omega), col_cl w a hjw 1 (by omega)]; exact G.2.1
    · obtain ⟨rfl, rfl⟩ := ind_ne h; rw [col_b0, col_cl w a hjw 1 (by omega)]; exact G.2.2.1
    · obtain ⟨rfl, rfl⟩ := ind_ne h; rw [col_cl w a hjw 1 (by omega), col_cl w a hjw 2 (by omega)]; exact G.2.2.2.1
    · obtain ⟨rfl, rfl⟩ := ind_ne h; rw [col_b0, col_cl w a hjw 2 (by omega)]; exact G.2.2.2.2.1
    · obtain ⟨rfl, rfl⟩ := ind_ne h; rw [col_cl w a hjw 2 (by omega), col_cl w a hjw 3 (by omega)]; exact G.2.2.2.2.2.1
    · obtain ⟨rfl, rfl⟩ := ind_ne h; rw [col_lit 2 (by omega), col_cl w a hjw 4 (by omega)]; exact G.2.2.2.2.2.2.1
    · obtain ⟨rfl, rfl⟩ := ind_ne h; rw [col_cl w a hjw 3 (by omega), col_cl w a hjw 4 (by omega)]; exact G.2.2.2.2.2.2.2.1
    · obtain ⟨rfl, rfl⟩ := ind_ne h; rw [col_cl w a hjw 4 (by omega), col_cl w a hjw 5 (by omega)]; exact G.2.2.2.2.2.2.2.2.1
    · obtain ⟨rfl, rfl⟩ := ind_ne h; rw [col_cl w a hjw 3 (by omega), col_cl w a hjw 5 (by omega)]; exact G.2.2.2.2.2.2.2.2.2.1
    · obtain ⟨rfl, rfl⟩ := ind_ne h; rw [col_cl w a hjw 5 (by omega), col1]; exact G.2.2.2.2.2.2.2.2.2.2.1
    · obtain ⟨rfl, rfl⟩ := ind_ne h; rw [col_cl w a hjw 5 (by omega), col2]; exact G.2.2.2.2.2.2.2.2.2.2.2

/-! ### The padded adjacency matrix -/

theorem len_flat {α : Type} (L : Nat → List α) (k : Nat) (hL : ∀ p, (L p).length = k) :
    ∀ n, ((List.range n).flatMap L).length = n * k
  | 0 => by simp
  | n+1 => by rw [List.range_succ, List.flatMap_append, List.length_append, len_flat L k hL n]; simp [hL, Nat.succ_mul]

theorem getD_flat {α : Type} (L : Nat → List α) (k : Nat) (hL : ∀ p, (L p).length = k) (d : α) :
    ∀ n p r, p < n → r < k → ((List.range n).flatMap L).getD (p*k + r) d = (L p).getD r d
  | 0, _, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | n+1, p, r, hp, hr => by
    rw [List.range_succ, List.flatMap_append]
    have hl := len_flat L k hL n
    by_cases h : p < n
    · have : (p+1)*k ≤ n*k := Nat.mul_le_mul_right _ h
      rw [Nat.succ_mul] at this
      rw [List.getD_append _ _ _ _ (by omega), getD_flat L k hL d n p r h hr]
    · have hpn : p = n := by omega
      subst hpn
      rw [List.getD_append_right _ _ _ _ (by omega), hl, show p*k + r - p*k = r by omega]
      simp

section
variable (w : Nat → Nat)
def pair (p q : Nat) : List Bool := if cnt w p q ≠ 0 then [true, false] else [false, false]
def row (p : Nat) : List Bool :=
  (List.range (size w)).flatMap (pair w p) ++ (List.range (2 * size w)).flatMap (fun _ => [false])
def bits : List Bool := (List.range (size w)).flatMap (row w)

theorem pair_len (p q) : (pair w p q).length = 2 := by unfold pair; split <;> rfl
theorem row_len (p) : (row w p).length = 2 * (2 * size w) := by
  unfold row; rw [List.length_append, len_flat _ 2 (pair_len w p), len_flat (fun _ => [false]) 1 (fun _ => rfl)]; ring
theorem bits_len : (bits w).length = (2 * size w) * (2 * size w) := by
  unfold bits; rw [len_flat _ _ (row_len w)]; ring

theorem entry (i j) (hi : i < 2 * size w) (hj : j < 2 * size w) :
    (bits w).getD (i * (2 * size w) + j) false = true ↔ (i % 2 = 0 ∧ j % 2 = 0 ∧ cnt w (i/2) (j/2) ≠ 0) := by
  have e : i * (2 * size w) + j = (i/2) * (2 * (2 * size w)) + ((i%2) * (2 * size w) + j) := by
    conv_lhs => rw [← Nat.div_add_mod i 2]
    ring
  have hr : (i%2) * (2 * size w) + j < 2 * (2 * size w) := by
    have : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have : (i%2) * (2 * size w) ≤ 1 * (2 * size w) := Nat.mul_le_mul_right _ (by omega)
    omega
  unfold bits
  rw [e, getD_flat _ _ (row_len w) _ _ _ _ (by omega) hr]
  unfold row
  have hl := len_flat (pair w (i/2)) 2 (pair_len w _) (size w)
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h, Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by omega)]
    have ej : j = (j/2) * 2 + j % 2 := by omega
    have := getD_flat (pair w (i/2)) 2 (pair_len w _) false (size w) (j/2) (j%2) (by omega) (Nat.mod_lt _ (by norm_num))
    rw [← ej] at this
    rw [this]; clear this ej
    unfold pair
    rcases Nat.mod_two_eq_zero_or_one j with h' | h' <;> simp only [h'] <;> split <;> simp_all
  · rw [h, Nat.one_mul, List.getD_append_right _ _ _ _ (by omega), hl, show 2 * size w + j - size w * 2 = j by omega]
    have := getD_flat (fun _ : Nat => [false]) 1 (fun _ => rfl) false (2 * size w) j 0 (by omega) (by omega)
    simp only [Nat.mul_one, Nat.add_zero] at this
    rw [this]; simp [h]

theorem colorable_iff : (∃ (n : ℕ) (c : Fin n → Fin 3), (bits w).length = n * n ∧
    ∀ i j : Fin n, (bits w).getD (i.val * n + j.val) false = true → c i ≠ c j) ↔ ∃ c, Col w c := by
  constructor
  · rintro ⟨n, c, hl, hc⟩
    rw [bits_len] at hl
    have hn : n = 2 * size w := (Nat.mul_self_inj.mp hl).symm
    subst hn
    refine ⟨fun p => if h : 2*p < 2 * size w then c ⟨2*p, h⟩ else 0, fun p q hp hq hpq => ?_⟩
    dsimp only
    rw [dif_pos (by omega), dif_pos (by omega)]
    apply hc
    rw [entry w _ _ (by simp; omega) (by simp; omega)]
    simp only
    refine ⟨by omega, by omega, ?_⟩
    rwa [show 2*p/2 = p by omega, show 2*q/2 = q by omega]
  · rintro ⟨c, hc⟩
    refine ⟨2 * size w, fun i => c (i.val/2), bits_len w, fun i j h => ?_⟩
    rw [entry w _ _ i.2 j.2] at h
    exact hc _ _ (by have := i.2; omega) (by have := j.2; omega) h.2.2
end

/-! ### The word-stream program -/
open Compact.WS

section
variable {α : Type}
def cE (n : Nat) : E α := .const n
def wE (k : E α) : E α := E.wordE k
def ad (a b : E α) : E α := .bin .add a b
def mu (a b : E α) : E α := .bin .mul a b
def su (a b : E α) : E α := .bin .sub a b
def indE (p q a b : E α) : E α := mu (E.eqE p a) (E.eqE q b)
def lvE (j : E α) (t : Nat) : E α :=
  ad (ad (cE 3) (mu (cE 2) (wE (ad (cE (2+2*t)) (mu (cE 6) j))))) (su (cE 1) (wE (ad (cE (3+2*t)) (mu (cE 6) j))))
def bsE (j : E α) : E α := ad (ad (cE 3) (mu (cE 2) (wE (cE 0)))) (mu (cE 6) j)
def sizeE : E α := ad (ad (cE 3) (mu (cE 2) (wE (cE 0)))) (mu (cE 6) (wE (cE 1)))
def varE (p q i : E α) : E α :=
  ad (ad (indE p q (ad (cE 3) (mu (cE 2) i)) (ad (ad (cE 3) (mu (cE 2) i)) (cE 1)))
    (indE p q (ad (cE 3) (mu (cE 2) i)) (cE 2))) (indE p q (ad (ad (cE 3) (mu (cE 2) i)) (cE 1)) (cE 2))
def clE (p q j : E α) : E α :=
  ad (ad (ad (ad (ad (ad (ad (ad (ad (ad (ad (indE p q (lvE j 0) (bsE j)) (indE p q (lvE j 1) (ad (bsE j) (cE 1)))) (indE p q (bsE j) (ad (bsE j) (cE 1)))) (indE p q (ad (bsE j) (cE 1)) (ad (bsE j) (cE 2)))) (indE p q (bsE j) (ad (bsE j) (cE 2)))) (indE p q (ad (bsE j) (cE 2)) (ad (bsE j) (cE 3)))) (indE p q (lvE j 2) (ad (bsE j) (cE 4)))) (indE p q (ad (bsE j) (cE 3)) (ad (bsE j) (cE 4)))) (indE p q (ad (bsE j) (cE 4)) (ad (bsE j) (cE 5)))) (indE p q (ad (bsE j) (cE 3)) (ad (bsE j) (cE 5)))) (indE p q (ad (bsE j) (cE 5)) (cE 1))) (indE p q (ad (bsE j) (cE 5)) (cE 2))
def cntE (p q : E α) : E α :=
  ad (ad (ad (ad (indE p q (cE 0) (cE 1)) (indE p q (cE 1) (cE 2))) (indE p q (cE 0) (cE 2)))
    (.sum (wE (cE 0)) (varE (p.rename some) (q.rename some) (.var none))))
    (.sum (wE (cE 1)) (clE (p.rename some) (q.rename some) (.var none)))

theorem val_size (x : List Bool) (v : α → Nat) : (sizeE : E α).val x v = size (cntW x) := by
  simp only [sizeE, ad, mu, cE, wE, E.val, val_wordE]; rfl

theorem val_cnt (p q : E α) (x : List Bool) (v : α → Nat) :
    (cntE p q).val x v = cnt (cntW x) (p.val x v) (q.val x v) := by
  simp only [cntE, clE, varE, indE, lvE, bsE, ad, mu, su, cE, wE, E.val, val_wordE, E.val_rename, E.val_eqE]
  rfl
end

def rowW : W (Option Empty) :=
  .cat (.range sizeE (.guard (cntE (.var (some none)) (.var none)) (.word (cE 1)) (.cat (.word (cE 0)) (.word (cE 0)))))
    (.range (mu (cE 2) sizeE) (.word (cE 0)))
def prog : W Empty := .range sizeE rowW

theorem ug_append (a b : List Nat) : ugWords (a ++ b) = ugWords a ++ ugWords b := by
  induction a with
  | nil => rfl
  | cons x xs ih => change _ ++ ugWords (xs ++ b) = (_ ++ ugWords xs) ++ _; rw [ih, List.append_assoc]
theorem ug_flat {β : Type} (l : List β) (f : β → List Nat) : ugWords (l.flatMap f) = l.flatMap (fun b => ugWords (f b)) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [List.flatMap_cons, ug_append, ih]

theorem prog_ok (x : List Bool) : ugWords (prog.eval x Empty.elim) = bits (cntW x) := by
  simp only [prog, rowW, W.eval, val_size, val_cnt, E.val, mu, cE, Op.eval, ug_flat, ug_append]
  unfold bits row pair
  congr 1; funext p; congr 1
  congr 1; funext q
  by_cases hc : cnt (cntW x) p q = 0 <;>
    simp only [Option.elim, hc, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false] <;> rfl

/-! ### Assembly -/
open OAI.BinPackingGames.Foundations.Complexity

noncomputable def g (F : Target.Formula) : List Bool := ugWords (prog.eval (formulaBits F) Empty.elim)
noncomputable def machine : Turing.TM2ComputableInPolyTime formulaBits id g :=
  ofW prog formulaBits id g (fun _ => rfl)
theorem finite (k) : Finite (machine.tm.Γ k) := inferInstanceAs (Finite Bool)

theorem flat6 {n : Nat} : ∀ (cs : List (Target.Clause n)) (j o : Nat) (hj : j < cs.length), o < 6 →
    (cs.flatMap clauseWords).getD (6*j+o) 0 = (clauseWords cs[j]).getD o 0
  | [], _, _, h, _ => by simp at h
  | c :: cs, 0, o, _, ho => by
    have hl : (clauseWords c).length = 6 := by simp [clauseWords, literalWords]
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
    rfl
  | c :: cs, j+1, o, h, ho => by
    have hl : (clauseWords c).length = 6 := by simp [clauseWords, literalWords]
    simp only [List.flatMap_cons]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl,
      show 6*(j+1)+o-6 = 6*j+o by omega, ← List.getD_eq_getElem?_getD,
      flat6 cs j o (by simp at h; omega) ho]
    rfl

theorem enc (F : Target.Formula) : Enc (cntW (formulaBits F)) F := by
  have hw (k) : cntW (formulaBits F) k = (formulaWords F).getD k 0 := by
    show cntW (bpWords _) k = _
    rw [bp_ug, cntW_words]
  obtain ⟨V, cs⟩ := F
  have six (j o) (hj : j < cs.length) (ho : o < 6) :
      cntW (formulaBits ⟨V, cs⟩) (o + 2 + 6*j) = (clauseWords cs[j]).getD o 0 := by
    rw [hw, show o + 2 + 6*j = 6*j+o+2 by omega]
    simp only [formulaWords, List.cons_append, List.getD_cons_succ]
    exact flat6 cs j o hj ho
  refine ⟨by rw [hw]; rfl, by rw [hw]; simp [formulaWords], fun j hj t ht => ?_, fun j hj t ht => ?_⟩
  · rw [show 2 + 2*t + 6*j = 2*t + 2 + 6*j by omega, six j _ hj (by omega)]
    interval_cases t <;> simp [clauseWords, literalWords]
  · rw [show 3 + 2*t + 6*j = (2*t+1) + 2 + 6*j by omega, six j _ hj (by omega)]
    interval_cases t <;> simp [clauseWords, literalWords]

theorem g_iff (F : Target.Formula) : (∃ (n : ℕ) (c : Fin n → Fin 3), (g F).length = n * n ∧
    ∀ i j : Fin n, (g F).getD (i.val * n + j.val) false = true → c i ≠ c j) ↔ F.Satisfiable := by
  rw [g, prog_ok]
  exact (colorable_iff _).trans ⟨fun ⟨c, h⟩ => sound _ F (enc F) c h, fun h => complete _ F (enc F) h⟩

theorem toOAI {L : List Bool → Prop} (h : OMA.S_wp_unique_games_conjecture.InNP L) : CookLevin.InNP L := by
  obtain ⟨p, V, ⟨c, hc⟩, hL⟩ := h
  exact ⟨⟨p, V, c, fun k => @Fintype.ofFinite _ (hc k)⟩, hL⟩
end Col3

open OMA.S_wp_unique_games_conjecture OMA.R_wp_unique_games_conjecture_R1 in
theorem OMA.solution : OMA.R_wp_unique_games_conjecture_R1.H1 := by
  intro L hL
  obtain ⟨R, hfin⟩ :=
    OAI.BinPackingGames.Foundations.Complexity.CookLevin.Completeness.threeSATReduction L (Col3.toOAI hL)
  refine ⟨Col3.g ∘ R.reduce, polyTime_comp ⟨R.computation, hfin⟩ ⟨Col3.machine, Col3.finite⟩, fun x => ?_⟩
  exact (R.correct x).trans (Col3.g_iff (R.reduce x)).symm

