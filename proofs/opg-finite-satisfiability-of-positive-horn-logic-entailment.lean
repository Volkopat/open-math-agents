import OMAStatements.S_opg_finite_satisfiability_of_positive_horn_logic_entailment
import Mathlib

/- Finite entailment of positive Horn logic, following Bova and Mogavero,
LICS 2017, DOI 10.1109/LICS.2017.8005073. -/

namespace HornLift

variable {F V : Type} (ar : F → ℕ)
abbrev Slot := (f : F) × Fin (ar f)
abbrev Ops (A : Type) := (f : F) → (Fin (ar f) → A) → A

/-- A flat equation has the form value(out) = f(value(arg 0), ...). -/
structure Row where
  out : V
  sym : F
  arg : Fin (ar sym) → V

def Sol {A : Type} (op : Ops ar A) (rows : Set (Row (V := V) ar)) (x : V → A) :=
  ∀ r ∈ rows, x r.out = op r.sym (x ∘ r.arg)

/-- One finite expansion of A remembers the immediate arguments of each operation. -/
def liftOp {A : Type} [DecidableEq F] (d : A) (op : Ops ar A) :
    Ops ar (A × (Slot ar → A)) := fun f xs =>
  (op f (fun i => (xs i).1), fun s => if h : s.1 = f then (xs (h ▸ s.2)).1 else d)

variable {ar}

theorem project [DecidableEq F] {A : Type} (d : A) (op : Ops ar A)
    {rows : Set (Row (V := V) ar)} {x}
    (hx : Sol ar (liftOp ar d op) rows x) :
    Sol ar op rows (fun v => (x v).1) := by
  intro r hr
  exact congrArg Prod.fst (hx r hr)

theorem decompose [DecidableEq F] {A : Type} (d : A) (op : Ops ar A)
    {rows : Set (Row (V := V) ar)} {x}
    (hx : Sol ar (liftOp ar d op) rows x)
    {r s : Row (V := V) ar} (hr : r ∈ rows) (hs : s ∈ rows)
    (hf : r.sym = s.sym) (hout : x r.out = x s.out)
    (i : Fin (ar r.sym)) :
    (x (r.arg i)).1 = (x (s.arg (hf ▸ i))).1 := by
  cases r with | mk u f a =>
    cases s with | mk v g b =>
      change f = g at hf
      subst g
      have e := (hx _ hr).symm.trans (hout.trans (hx _ hs))
      simpa [liftOp, Function.comp_def] using
        congrArg (fun y : A × (Slot ar → A) => y.2 ⟨f,i⟩) e

/-- A single flipped coordinate makes a directed dependency cycle inconsistent. -/
theorem noTwistedCycle {n : ℕ} (b : Fin (n+1) → Bool)
    (h : ∀ i : Fin n, b i.castSucc = b i.succ)
    (last : b (Fin.last n) = !(b 0)) : False := by
  have all_eq (i : Fin (n+1)) : b i = b 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (h i).symm.trans ih
  have e := (all_eq (Fin.last n)).symm.trans last
  cases hv : b 0 <;> simp [hv] at e

structure FA {F : Type} (ar : F → ℕ) where
  A : Type
  fin : Finite A
  ne : Nonempty A
  op : Ops ar A

variable {I Q : Type}
/-- A repeated vertex in a descending chain yields a cycle. A finite bit-vector algebra
with one negated coordinate rules out that cycle, so the rows can be evaluated recursively. -/
theorem graphEval [Finite Q] {out : I → Q} {sym : I → F}
    {arg : (i : I) → Fin (ar (sym i)) → Q}
    (det : ∀ i j, out i = out j →
      (⟨sym i, arg i⟩ : (f : F) × (Fin (ar f) → Q)) = ⟨sym j, arg j⟩)
    (solve : ∀ B : FA ar, ∃ x : Q → B.A, ∀ i, x (out i) = B.op (sym i) (x ∘ arg i))
    {M : Type} (d : M) (op : Ops ar M) :
    ∃ x : Q → M, ∀ i, x (out i) = op (sym i) (x ∘ arg i) := by
  classical
  let dep (a b : Q) := ∃ i j, out i = b ∧ arg i j = a
  have wf : WellFounded dep := by
    apply wellFounded_iff_isEmpty_descending_chain.mpr
    constructor
    rintro ⟨p, hp⟩
    choose r slot hr hs using hp
    obtain ⟨u, v, he, huv⟩ : ∃ u v, p u = p v ∧ u ≠ v := by
      simpa [Function.Injective] using not_injective_infinite_finite p
    obtain ⟨m,k, loop⟩ : ∃ m k, p (m+k+1) = p m := by
      rcases lt_or_gt_of_ne huv with h|h
      · exact ⟨u,v-u-1,by rwa [show u+(v-u-1)+1 = v by omega, eq_comm]⟩
      · exact ⟨v,u-v-1,by rwa [show v+(u-v-1)+1 = u by omega]⟩
    let T := Fin (k+1)
    let idx (t : T) := m + t.val
    let next (t : T) : T := if h : t.val < k then ⟨t.val+1,by omega⟩ else 0
    let twist (f : F) (ys : Fin (ar f) → T → Bool) (t : T) :=
      if h : sym (r (idx t)) = f then
        let b := ys (h ▸ slot (idx t)) (next t)
        if t.val < k then b else !b
      else false
    obtain ⟨x,hx⟩ := solve ⟨T → Bool, inferInstance, inferInstance, twist⟩
    have eqn (t : T) := congrFun (hx (r (idx t))) t
    have step (t : T) : x (p (idx t)) t =
        if t.val < k then x (p (idx t+1)) (next t) else !(x (p (idx t+1)) (next t)) := by
      simpa [twist, Function.comp_def, hr, hs] using eqn t
    apply noTwistedCycle (fun t => x (p (idx t)) t)
    · intro t
      simpa [idx, next, t.isLt, Nat.add_assoc, Fin.succ] using step t.castSucc
    · simpa [idx, next, loop] using step (Fin.last k)
  let body (q : Q) (rec : (a : Q) → dep a q → M) : M :=
    if h : ∃ i, out i = q then
      op (sym h.choose) (fun j => rec _ ⟨_,j,h.choose_spec,rfl⟩) else d
  refine ⟨wf.fix body, fun i => ?_⟩
  rw [wf.fix_eq]
  dsimp only [body]
  rw [dif_pos (show ∃ j, out j = out i from ⟨i,rfl⟩)]
  exact congrArg (fun z : (f : F) × (Fin (ar f) → Q) =>
    op z.1 (wf.fix body ∘ z.2)) (det _ i ((show ∃ j, out j = out i from ⟨i,rfl⟩).choose_spec))

abbrev Eqs (V : Type) := Set (V × V)
def Respects {A : Type} (x : V → A) (e : Eqs V) := ∀ a b, (a,b) ∈ e → x a = x b

/-- Maximize the identifications of nodes compatible with solvability in every finite
algebra. On the quotient each defined output has a unique operation and argument tuple. -/
theorem finiteTest [Finite V] [Finite F] {rows : Set (Row (V := V) ar)} {eqs : Eqs V}
    (h : ∀ B : FA ar, ∃ x, Sol ar B.op rows x ∧ Respects x eqs)
    {M : Type} (d : M) (op : Ops ar M) :
    ∃ x, Sol ar op rows x ∧ Respects x eqs := by
  classical
  let ok : Set (Eqs V) := {e | ∀ B : FA ar, ∃ x, Sol ar B.op rows x ∧ Respects x eqs ∧ Respects x e}
  obtain ⟨e,he,hm⟩ := ok.toFinite.exists_maximal (show ok.Nonempty from
    ⟨eqs,fun B => by obtain ⟨x,hx,ex⟩ := h B; exact ⟨x,hx,ex,ex⟩⟩)
  have extend (a b : V) (hab : ∀ B : FA ar, ∃ x, Sol ar B.op rows x ∧ Respects x eqs ∧
      Respects x e ∧ x a = x b) : (a,b) ∈ e := by
    apply hm (y := insert (a,b) e) _ (Set.subset_insert ..) (Set.mem_insert ..)
    intro B
    obtain ⟨x,hx,ex,ee,hp⟩ := hab B
    refine ⟨x,hx,ex,fun u v huv => ?_⟩
    rcases huv with huv|huv
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj huv
      exact hp
    · exact ee u v huv
  have forced (a b : V) (hf : ∀ (B : FA ar) (x : V → B.A), Sol ar B.op rows x →
      Respects x eqs → Respects x e → x a = x b) : (a,b) ∈ e := by
    apply extend
    intro B
    obtain ⟨x,hx,ex,ee⟩ := he B
    exact ⟨x,hx,ex,ee,hf B x hx ex ee⟩
  let S : Setoid V :=
    { r := fun a b => (a,b) ∈ e
      iseqv := ⟨fun a => forced a a (by intros; rfl),
        fun {a b} hab => forced b a (fun _ _ _ _ ee => (ee a b hab).symm),
        fun {a b c} hab hbc => forced a c (fun _ _ _ _ ee => (ee a b hab).trans (ee b c hbc))⟩ }
  let q := Quotient.mk S
  have det (r s : rows) (hout : q r.1.out = q s.1.out) :
      (⟨r.1.sym, q ∘ r.1.arg⟩ : (f : F) × (Fin (ar f) → Quotient S)) =
        ⟨s.1.sym, q ∘ s.1.arg⟩ := by
    have ho : (r.1.out,s.1.out) ∈ e := Quotient.exact hout
    obtain ⟨x,hx,_,ee⟩ := he (⟨Option F,inferInstance,inferInstance,fun f _ => some f⟩ : FA ar)
    have hf : r.1.sym = s.1.sym := Option.some.inj
      ((hx _ r.2).symm.trans ((ee _ _ ho).trans (hx _ s.2)))
    rcases r with ⟨⟨u,f,ra⟩,hr⟩
    rcases s with ⟨⟨v,g,sa⟩,ht⟩
    change f = g at hf
    subst g
    apply congrArg (Sigma.mk f)
    funext i
    apply Quotient.sound
    apply extend
    intro B
    have := B.fin
    let b := Classical.choice B.ne
    let C : FA ar := ⟨B.A × (Slot ar → B.A), inferInstance, ⟨b,fun _ => b⟩, liftOp ar b B.op⟩
    obtain ⟨y,hy,ey,er⟩ := he C
    refine ⟨fun v => (y v).1,project b B.op hy,fun _ _ hp => congrArg Prod.fst (ey _ _ hp),
      fun _ _ hp => congrArg Prod.fst (er _ _ hp),?_⟩
    exact decompose b B.op hy hr ht rfl (er _ _ ho) i
  obtain ⟨v,hv⟩ := graphEval det (fun B => by
    obtain ⟨x,hx,_,ee⟩ := he B
    exact ⟨Quotient.lift x (fun _ _ => ee _ _),fun r => hx r.1 r.2⟩) d op
  exact ⟨v ∘ q,fun r hr => hv ⟨r,hr⟩,fun a b hab => congrArg v
    (Quotient.sound (s := S) (forced a b (fun _ _ _ ex _ => ex a b hab)))⟩

/-- Take a product of separating finite algebras, one for each diagram on V. Every
assignment of V in the product then has a matching assignment in the given algebra. -/
theorem localTransfer (V : Type) [Finite V] [Finite F] {M : Type} (d : M) (op : Ops ar M) :
    ∃ B : FA ar, ∀ x : V → B.A, ∃ y : V → M,
      (∀ a b, x a = x b → y a = y b) ∧
      ∀ (v : V) f (a : Fin (ar f) → V), x v = B.op f (x ∘ a) → y v = op f (y ∘ a) := by
  classical
  let D := Set (Row (V := V) ar) × Eqs V
  have : Finite (Row (V := V) ar) := Finite.of_injective
    (fun (r : Row (V := V) ar) => (r.out, (⟨r.sym,r.arg⟩ : (f : F) × (Fin (ar f) → V))))
    (by rintro ⟨u,f,a⟩ ⟨v,g,b⟩ h; simpa using h)
  have separate (z : D) : ∃ B : FA ar, (∃ x, Sol ar B.op z.1 x ∧ Respects x z.2) →
      ∃ y, Sol ar op z.1 y ∧ Respects y z.2 := by
    by_contra! h
    have allB (B : FA ar) := (h B).1
    obtain ⟨v,hv,ev⟩ := finiteTest allB d op
    exact (h ⟨Unit,inferInstance,inferInstance,fun _ _ => ()⟩).2 v hv ev
  choose C hC using separate
  have (z : D) := (C z).fin
  have (z : D) := (C z).ne
  let B : FA ar := ⟨(z : D) → (C z).A, inferInstance, inferInstance,fun f xs z =>
    (C z).op f (fun i => xs i z)⟩
  refine ⟨B,fun x => ?_⟩
  let z : D := ({r | x r.out = B.op r.sym (x ∘ r.arg)}, {p | x p.1 = x p.2})
  obtain ⟨y,hy,ey⟩ := hC z ⟨fun v => x v z,fun r hr => congrFun hr z,
    fun a b h => congrFun h z⟩
  exact ⟨y,ey,fun v f a => hy ⟨v,f,a⟩⟩

open OMA.S_opg_finite_satisfiability_of_positive_horn_logic_entailment
variable {R : Type} {a : R → ℕ} {U W : Type}

inductive Atom (a : R → ℕ) (V : Type) where
  | eq (u v : V)
  | rel (r : R) (args : Fin (a r) → V)

def Atom.map (f : V → W) : Atom a V → Atom a W
  | .eq u v => .eq (f u) (f v)
  | .rel r t => .rel r (f ∘ t)

def Atom.holds (M : Str a) (p : V → M.carrier) : Atom a V → Prop
  | .eq u v => p u = p v
  | .rel r t => M.interp r (p ∘ t)

theorem Atom.holds_map (M : Str a) (p : W → M.carrier) (f : V → W) (t : Atom a V) :
    (t.map f).holds M p ↔ t.holds M (p ∘ f) := by cases t <;> rfl

/-- A prenex game extends the variable type by one fresh position for each binder. -/
inductive Game (a : R → ℕ) : Type → Type 1 where
  | leaf {V : Type} (ts : List (Atom a V)) : Game a V
  | bind {V : Type} (u : Bool) (g : Game a (Option V)) : Game a V

def ext (p : V → U) (v : U) : Option V → U := Option.elim' v p

def Game.sat (M : Str a) : {V : Type} → Game a V → (V → M.carrier) → Prop
  | _,.leaf ts,p => ∀ t ∈ ts, t.holds M p
  | _,.bind true g,p => ∀ v, g.sat M (ext p v)
  | _,.bind false g,p => ∃ v, g.sat M (ext p v)

def Game.map : {V W : Type} → (V → W) → Game a V → Game a W
  | _,_,f,.leaf ts => .leaf (ts.map (Atom.map f))
  | _,_,f,.bind u g => .bind u (g.map (Option.map f))

theorem ext_map (p : W → U) (f : V → W) (v : U) :
    ext p v ∘ Option.map f = ext (p ∘ f) v := by funext w; cases w <;> rfl

theorem Game.sat_map (M : Str a) (g : Game a V) (f : V → W) (p : W → M.carrier) :
    (g.map f).sat M p ↔ g.sat M (p ∘ f) := by
  induction g generalizing W with
  | leaf ts => simp [Game.map, Game.sat, Atom.holds_map]
  | bind u g ih => cases u <;> simp [Game.map, Game.sat, ih, ext_map]

def Game.prepend : {V : Type} → List (Atom a V) → Game a V → Game a V
  | _,xs,.leaf ys => .leaf (xs ++ ys)
  | _,xs,.bind u g => .bind u (g.prepend (xs.map (Atom.map some)))

theorem Game.sat_prepend (M : Str a) (g : Game a V) (xs : List (Atom a V)) (p : V → M.carrier) :
    (g.prepend xs).sat M p ↔ (∀ t ∈ xs, t.holds M p) ∧ g.sat M p := by
  have := M.nonempty
  induction g with
  | leaf ys => exact List.forall_mem_append
  | bind u g ih =>
    cases u <;> simp [Game.prepend, Game.sat, ih, Atom.holds_map,
      show ∀ v, ext p v ∘ some = p from fun _ => rfl, forall_and, exists_and_left]

def Game.join : {V : Type} → Game a V → Game a V → Game a V
  | _,.leaf xs,h => h.prepend xs
  | _,.bind u g,h => .bind u (g.join (h.map some))

theorem Game.sat_join (M : Str a) (g h : Game a V) (p : V → M.carrier) :
    (g.join h).sat M p ↔ g.sat M p ∧ h.sat M p := by
  have := M.nonempty
  induction g with
  | leaf xs => exact Game.sat_prepend ..
  | bind u g ih => cases u <;> simp [Game.join, Game.sat, ih, Game.sat_map,
      show ∀ v, ext p v ∘ some = p from fun _ => rfl, forall_and, exists_and_right]

def compile : {V : Type} → PH a → (ℕ → V) → Game a V
  | _,.eq x y,s => .leaf [.eq (s x) (s y)]
  | _,.rel r xs,s => .leaf [.rel r (s ∘ xs)]
  | _,.and g h,s => (compile g s).join (compile h s)
  | _,.ex x g,s => .bind false (compile g (Function.update (some ∘ s) x none))
  | _,.all x g,s => .bind true (compile g (Function.update (some ∘ s) x none))

theorem ext_update (p : V → U) (s : ℕ → V) (x : ℕ) (v : U) :
    ext p v ∘ Function.update (some ∘ s) x none = Function.update (p ∘ s) x v := by
  funext i
  by_cases hi : i = x <;> simp [hi,Function.comp_def,ext,Function.update]

theorem sat_compile (g : PH a) (M : Str a) (s : ℕ → V) (p : V → M.carrier) :
    (compile g s).sat M p ↔ g.sat M (p ∘ s) := by
  induction g generalizing V with
  | eq | rel => simp [compile, Game.sat, PH.sat, Atom.holds, Function.comp_def]
  | and g h ih jh => simp [compile,Game.sat_join,PH.sat,ih,jh]
  | ex x g ih => simp [compile,Game.sat,PH.sat,ih,ext_update]
  | all x g ih => simp [compile,Game.sat,PH.sat,ih,ext_update]

theorem sat_congr (g : PH a) (M : Str a) (s p : ℕ → M.carrier)
    (h : ∀ i ∈ g.free, s i = p i) : g.sat M s ↔ g.sat M p := by
  induction g generalizing s p with
  | eq x y => simp [PH.sat,h x (by simp [PH.free]),h y (by simp [PH.free])]
  | rel r xs => have e : s ∘ xs = p ∘ xs := funext fun i => h _ ⟨i,rfl⟩
                simp [PH.sat,e]
  | and g k ih jh =>
    exact and_congr (ih _ _ (fun i hi => h i (Or.inl hi))) (jh _ _ (fun i hi => h i (Or.inr hi)))
  | ex x g ih | all x g ih =>
    first | apply exists_congr | apply forall_congr'
    intro v
    apply ih
    intro i hi
    by_cases e : i = x
    · simp [e]
    · simpa [Function.update_of_ne e] using h i ⟨hi,e⟩

inductive Flat {F : Type} (ar : F → ℕ) (n : ℕ) where
  | var (i : Fin n)
  | app (f : F) (args : Fin (ar f) → Fin n)

instance {n} [Finite F] : Finite (Flat ar n) := Finite.of_surjective
    (fun z : Fin n ⊕ ((f : F) × (Fin (ar f) → Fin n)) =>
      match z with | .inl i => Flat.var i | .inr ⟨f,args⟩ => Flat.app f args)
    (by rintro (i|⟨f⟩); exact ⟨.inl i,rfl⟩; exact ⟨.inr ⟨_,_⟩,rfl⟩)

def Flat.eval {n} {A : Type} (op : Ops ar A) (p : Fin n → A) : Flat ar n → A
  | .var i => p i
  | .app f t => op f (p ∘ t)

def Flat.wk {n} : Flat ar n → Flat ar (n+1)
  | .var i => .var i.castSucc
  | .app f t => .app f (Fin.castSucc ∘ t)

theorem Flat.eval_wk {n} {A : Type} (op : Ops ar A) (p : Fin (n+1) → A) (t : Flat ar n) :
    t.wk.eval op p = t.eval op (p ∘ Fin.castSucc) := by cases t <;> rfl

def arExt (ar : F → ℕ) (n : ℕ) : Option F → ℕ := Option.elim' n ar

def Flat.incl {n} (t : Flat ar n) : Flat (arExt ar n) n :=
  match t with
  | .var i => .var i
  | .app f a => .app (some f) a

theorem Flat.eval_incl {n} {A : Type} (o : Ops (arExt ar n) A) (p : Fin n → A) (t : Flat ar n) :
    t.incl.eval o p = t.eval (fun f => o (some f)) p := by cases t <;> rfl

def Signed (neg : Bool) (P : Prop) := if neg then ¬ P else P

def Mat {n} (ts : List (Atom a (Flat ar n))) (N : Str a) (o : Ops ar N.carrier) (neg : Bool) :=
  ∀ p : Fin n → N.carrier, Signed neg (∀ t ∈ ts, t.holds N (Flat.eval o p))

structure Cert (M : Str a) (neg : Bool) where
  F : Type
  fin : Finite F
  ar : F → ℕ
  n : ℕ
  op : Ops ar M.carrier
  ts : List (Atom a (Flat ar n))
  valid : Mat ts M op neg
  faithful : ∀ u v, Atom.eq u v ∈ ts → (∀ p, u.eval op p = v.eval op p) → u = v

def Faith {n} {A : Type} (op : Ops ar A) (t : V → Flat ar n) :=
  ∀ v w, (∀ p, (t v).eval op p = (t w).eval op p) → t v = t w

theorem Game.quant (M : Str a) (neg u : Bool) (g : Game a (Option V)) (s : V → M.carrier) :
    Signed neg ((Game.bind u g).sat M s) ↔
      (if u != neg then ∀ x, Signed neg (g.sat M (ext s x)) else ∃ x, Signed neg (g.sat M (ext s x))) := by
  cases u <;> cases neg <;> simp [Signed, Game.sat]

/-- Record a strategy by terms in its unrestricted inputs. A controlled move that
always equals an earlier move reuses its term. Otherwise it introduces a new operation.
An unrestricted move adds an independent input, preserving faithfulness of the terms. -/
theorem extractGame {M : Str a} [Nontrivial M.carrier] (neg : Bool) (g : Game a V)
    {F : Type} [Finite F] {ar : F → ℕ} (op : Ops ar M.carrier) {n : ℕ} (t : V → Flat ar n)
    (faith : Faith op t)
    (win : ∀ p, Signed neg (g.sat M (Flat.eval op p ∘ t))) :
    ∃ (C : Cert M neg) (red : (A : Type) → Ops C.ar A → Ops ar A),
      ∀ (N : Str a) (o : Ops C.ar N.carrier), Mat C.ts N o neg →
        ∀ p, Signed neg (g.sat N (Flat.eval (red _ o) p ∘ t)) := by
  classical
  induction g generalizing F n with
  | leaf xs =>
    have leafEquiv (N : Str a) (o : Ops ar N.carrier) (p : Fin n → N.carrier) :
        (∀ z ∈ xs.map (Atom.map t), Atom.holds N (Flat.eval o p) z) ↔
        (Game.leaf xs).sat N (Flat.eval o p ∘ t) := by
      simp [Game.sat, Atom.holds_map]
    refine ⟨⟨F,inferInstance,ar,n,op,xs.map (Atom.map t),fun p => ?_,?_⟩,fun _ o => o,?_⟩
    · rw [leafEquiv]; exact win p
    · intro u v huv h
      obtain ⟨z,_,hz⟩ := List.mem_map.mp huv
      cases z with
      | eq i j =>
        obtain ⟨rfl,rfl⟩ := Atom.eq.inj hz
        exact faith i j h
      | rel r args => contradiction
    · intro N o hv p
      rw [← leafEquiv]
      exact hv p
  | @bind V u g ih =>
    have hwin (p) := (Game.quant M neg u g _).mp (win p)
    by_cases free : (u != neg) = true
    · let t' : Option V → Flat ar (n+1) := ext (Flat.wk ∘ t) (.var (Fin.last n))
      have ev {A : Type} (o : Ops ar A) (p : Fin (n+1) → A) :
          Flat.eval o p ∘ t' = ext (Flat.eval o (p ∘ Fin.castSucc) ∘ t) (p (Fin.last n)) := by
        funext v; cases v with
        | none => rfl
        | some v => exact Flat.eval_wk .. 
      have cross (v : V) : ¬∀ p, p (Fin.last n) = (t v).eval op (p ∘ Fin.castSucc) := by
        intro h
        let p₀ : Fin n → M.carrier := fun _ => Classical.choice M.nonempty
        obtain ⟨b,hb⟩ := exists_ne ((t v).eval op p₀)
        apply hb
        simpa [Function.comp_def] using h (Fin.snoc p₀ b)
      have ft : Faith op t' := by
        intro v w hh
        have eqv (p) := congrFun (ev op p) v
        have eqw (p) := congrFun (ev op p) w
        have pair (p) := (eqv p).symm.trans ((hh p).trans (eqw p))
        cases v with
        | none => cases w with
                  | none => rfl
                  | some w => exact (cross w pair).elim
        | some v => cases w with
                    | none => exact (cross v (fun p => (pair p).symm)).elim
                    | some w =>
                      apply congrArg Flat.wk
                      apply faith
                      intro p
                      simpa [ext, Function.comp_def] using pair (Fin.snoc p (Classical.choice M.nonempty))
      obtain ⟨C,red,hC⟩ := ih op t' ft (fun p => by
        rw [ev]; exact (if_pos free ▸ hwin (p ∘ Fin.castSucc)) (p (Fin.last n)))
      refine ⟨C,red,fun N o hv p => (Game.quant ..).mpr ?_⟩
      rw [if_pos free]
      intro b
      have hh := hC N o hv (Fin.snoc p b)
      rw [ev] at hh
      simpa [Function.comp_def] using hh
    · have hw (p) : ∃ x, Signed neg (g.sat M (ext (Flat.eval op p ∘ t) x)) := by simpa only [if_neg free] using hwin p
      choose w hw using hw
      let o' : Ops (arExt ar n) M.carrier
        | none => w
        | some f => op f
      let old := Flat.incl ∘ t
      let wterm : Flat (arExt ar n) n :=
        if h : ∃ v, ∀ p, (t v).eval op p = w p then old h.choose else .app none id
      have ew (p) : wterm.eval o' p = w p := by
        dsimp only [wterm]; split
        next h => exact (Flat.eval_incl o' p _).trans (h.choose_spec p)
        next => rfl
      let t' := ext old wterm
      have ev {A : Type} (o : Ops (arExt ar n) A) (p : Fin n → A) :
          Flat.eval o p ∘ t' = ext (Flat.eval (fun f => o (some f)) p ∘ t) (wterm.eval o p) := by
        funext v; cases v with
        | none => rfl
        | some v => exact Flat.eval_incl .. 
      have copy (v : V) (hh : ∀ p, (t v).eval op p = w p) : old v = wterm := by
        have h : ∃ v, ∀ p, (t v).eval op p = w p := ⟨v,hh⟩
        simp only [wterm,dif_pos h]
        exact congrArg Flat.incl (faith _ _ (fun p => (hh p).trans (h.choose_spec p).symm))
      have ft : Faith o' t' := by
        intro v k hh
        cases v with
        | none => cases k with
                  | none => rfl
                  | some k =>
                    exact (copy k (fun p => (Flat.eval_incl o' p _).symm.trans ((hh p).symm.trans (ew p)))).symm
        | some v => cases k with
                    | none => exact copy v (fun p => (Flat.eval_incl o' p _).symm.trans ((hh p).trans (ew p)))
                    | some k => exact congrArg Flat.incl (faith v k (fun p =>
                        (Flat.eval_incl o' p _).symm.trans ((hh p).trans (Flat.eval_incl o' p _))))
      obtain ⟨C,red,hC⟩ := ih o' t' ft (fun p => by rw [ev,ew]; exact hw p)
      refine ⟨C,fun A o f => red A o (some f),fun N o hv p => (Game.quant ..).mpr ?_⟩
      rw [if_neg free]
      refine ⟨wterm.eval (red _ o) p,?_⟩
      exact (ev (red _ o) p) ▸ hC N o hv p

theorem certificate (M : Str a) [Nontrivial M.carrier] (neg : Bool) (g : PH a) (hg : g.free = ∅)
    (s : ℕ → M.carrier) (hs : Signed neg (g.sat M s)) :
    ∃ C : Cert M neg, ∀ (N : Str a) (o : Ops C.ar N.carrier), Mat C.ts N o neg →
      ∀ v : N.carrier, Signed neg (g.sat N (fun _ => v)) := by
  let t : Unit → Flat (fun _ : Empty => 0) 1 := fun _ => .var 0
  let o : Ops (fun _ : Empty => 0) M.carrier := fun e => e.elim
  let game := compile g (fun _ => ())
  have hv (p : Fin 1 → M.carrier) : Signed neg (game.sat M (Flat.eval o p ∘ t)) := by
    rw [show game.sat M (Flat.eval o p ∘ t) ↔ g.sat M s from
      (sat_compile ..).trans (sat_congr g _ _ _ (by simp [hg]))]
    exact hs
  obtain ⟨C,red,hC⟩ := extractGame neg game o t (fun _ _ _ => rfl) hv
  refine ⟨C,fun N alg h v => ?_⟩
  have hh := hC N alg h (fun _ => v)
  simpa only [game, sat_compile, t, Function.comp_def, Flat.eval] using hh

theorem liftTerms {A M : Type} {n : ℕ} (o : Ops ar A) (op : Ops ar M)
    (x : V → A) (y : V → M)
    (eqs : ∀ a b, x a = x b → y a = y b)
    (rows : ∀ v f (b : Fin (ar f) → V), x v = o f (x ∘ b) → y v = op f (y ∘ b))
    (input : Fin n → V) (node : Flat ar n → V)
    (ev : ∀ t, x (node t) = t.eval o (x ∘ input)) (t : Flat ar n) :
    y (node t) = t.eval op (y ∘ input) := by
  cases t with
  | var i => exact eqs _ _ (ev _)
  | app f b => exact rows _ f (input ∘ b) (ev _)

def generated {M : Str a} (C : Cert M false) {A : Type} (o : Ops C.ar A)
    (r : R) (v : Fin (a r) → A) :=
  ∃ (p : Fin C.n → A) (args : Fin (a r) → Flat C.ar C.n),
    Atom.rel r args ∈ C.ts ∧ Flat.eval o p ∘ args = v

def matched {M : Str a} (P : Cert M false) (D : Cert M true) {A : Type}
    (op : Ops P.ar A) (od : Ops D.ar A) (p : Fin P.n → A) (d : Fin D.n → A) :
    Atom a (Flat D.ar D.n) → Prop
  | .eq u v => u.eval od d = v.eval od d
  | .rel r args => ∃ bs, Atom.rel r bs ∈ P.ts ∧ Flat.eval op p ∘ bs = Flat.eval od d ∘ args

/-- Generate each finite relation from the positive matrix. A play satisfying the
negative matrix would match each relational occurrence to a positive tuple. Transferring
all those plays together would satisfy the same negative matrix in the original model. -/
theorem joint {M : Str a} (P : Cert M false) (D : Cert M true) :
    ∃ (N : Str a) (_ : Finite N.carrier) (op : Ops P.ar N.carrier) (od : Ops D.ar N.carrier),
      Mat P.ts N op false ∧ Mat D.ts N od true := by
  classical
  have := P.fin
  have := D.fin
  let sig := Sum.elim P.ar D.ar
  let alg : Ops sig M.carrier := fun f => Sum.rec (motive := fun f =>
    (Fin (sig f) → M.carrier) → M.carrier) P.op D.op f
  let I := Fin D.ts.length
  let V := (I × (Fin P.n ⊕ Flat P.ar P.n)) ⊕ (Fin D.n ⊕ Flat D.ar D.n)
  obtain ⟨B,hB⟩ := localTransfer V (Classical.choice M.nonempty) alg
  let op : Ops P.ar B.A := fun f => B.op (.inl f)
  let od : Ops D.ar B.A := fun f => B.op (.inr f)
  let N : Str a := ⟨B.A,B.ne,generated P op⟩
  refine ⟨N,B.fin,op,od,?_,?_⟩
  · intro p t ht
    cases t with
    | eq u v =>
      have e := P.faithful u v ht (fun p => P.valid p (.eq u v) ht)
      rw [e]
      rfl
    | rel r args => exact ⟨p,args,ht,rfl⟩
  · intro d h
    have allMatches (i : I) : ∃ p, matched P D op od p d D.ts[i] := by
      have ht := h D.ts[i] (List.getElem_mem ..)
      cases he : D.ts[i] with
      | eq u v =>
        rw [he] at ht
        exact ⟨fun _ => Classical.choice B.ne,ht⟩
      | rel r args =>
        rw [he] at ht
        obtain ⟨p,bs,hb,ev⟩ := ht
        exact ⟨p,bs,hb,ev⟩
    choose p hp using allMatches
    let x : V → B.A
      | .inl (i,.inl k) => p i k
      | .inl (i,.inr t) => t.eval op (p i)
      | .inr (.inl k) => d k
      | .inr (.inr t) => t.eval od d
    obtain ⟨y,ey,ry⟩ := hB x
    let pi (i : I) (k : Fin P.n) : V := .inl (i,.inl k)
    let pt (i : I) (t : Flat P.ar P.n) : V := .inl (i,.inr t)
    let di (k : Fin D.n) : V := .inr (.inl k)
    let dt (t : Flat D.ar D.n) : V := .inr (.inr t)
    have ep (i : I) := liftTerms op P.op x y ey (fun v f => ry v (.inl f)) (pi i) (pt i) (fun _ => rfl)
    have ed := liftTerms od D.op x y ey (fun v f => ry v (.inr f)) di dt (fun _ => rfl)
    apply D.valid (y ∘ di)
    intro t ht
    obtain ⟨i,hi⟩ := List.mem_iff_getElem.mp ht
    let j : I := ⟨i,hi.choose⟩
    have he : D.ts[j] = t := hi.choose_spec
    have hm := hp j
    rw [he] at hm
    cases t with
    | eq u v => exact (ed u).symm.trans ((ey (dt u) (dt v) hm).trans (ed v))
    | rel r args =>
      obtain ⟨bs,hb,eb⟩ := hm
      have pos := P.valid (y ∘ pi j) (.rel r bs) hb
      change M.interp r (Flat.eval P.op (y ∘ pi j) ∘ bs) at pos
      change M.interp r (Flat.eval D.op (y ∘ di) ∘ args)
      have e : Flat.eval D.op (y ∘ di) ∘ args = Flat.eval P.op (y ∘ pi j) ∘ bs := by
        funext k
        exact (ed _).symm.trans ((ey (dt _) (pt j _) (congrFun eb k).symm).trans (ep j _))
      rwa [e]

theorem finish (φ ψ : PH a) (hφ : φ.free = ∅) (hψ : ψ.free = ∅)
    (M : Str a) (s : ℕ → M.carrier) (hp : φ.sat M s) (hd : ¬ ψ.sat M s) :
    ∃ (N : Str a) (_ : Finite N.carrier) (p : ℕ → N.carrier), φ.sat N p ∧ ¬ ψ.sat N p := by
  classical
  cases subsingleton_or_nontrivial M.carrier with
  | inl hs => exact ⟨M,inferInstance,s,hp,hd⟩
  | inr hn =>
    obtain ⟨P,hP⟩ := certificate M false φ hφ s hp
    obtain ⟨D,hD⟩ := certificate M true ψ hψ s hd
    obtain ⟨N,fin,op,od,vp,vd⟩ := joint P D
    let b := Classical.choice N.nonempty
    exact ⟨N,fin,fun _ => b,hP N op vp b,hD N od vd b⟩

end HornLift

theorem OMA.solution : type_of% @OMA.S_opg_finite_satisfiability_of_positive_horn_logic_entailment.main := by
  rintro R _ ar φ ψ hφ hψ ⟨M,s,hp,hd⟩
  exact HornLift.finish φ ψ hφ hψ M s hp hd
