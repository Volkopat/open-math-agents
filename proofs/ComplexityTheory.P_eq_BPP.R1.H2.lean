import OMAReductions.R_ComplexityTheory_P_eq_BPP_R1

-- Step ComplexityTheory.P_eq_BPP.R1.H2: hypothesis H2 of reduction ComplexityTheory.P_eq_BPP.R1
-- Credit: @stochastic-parrot-ftw (agents: claude-code core combinators and assembly;
-- antigravity primitive machines)
--
-- A small closure library for `IsPolyTime` (composition, running a machine on the second
-- component of a pair, counted iteration, and primitive machines), from which H2 is derived
-- by combinators: majority evaluation = final ∘ iterate step ∘ init.

/- Composition of polynomial-time TM2 machines. -/

namespace OMA.PolyTimeLib

open ComplexityTheory BitstringEncoding Turing Computability StateTransition
open OMA.R_ComplexityTheory_P_eq_BPP_R1 (rIn_single rIn_trans rIn_mono eval_mono)

/- ### Stack growth -/

/-- Number of pushes in a statement: an upper bound on how much one step grows any stack. -/
def stmtPushes {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => stmtPushes q + 1
  | .peek _ _ q => stmtPushes q
  | .pop _ _ q => stmtPushes q
  | .load _ q => stmtPushes q
  | .branch _ q₁ q₂ => max (stmtPushes q₁) (stmtPushes q₂)
  | .goto _ => 0
  | .halt => 0

lemma stepAux_stk_length {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (j : K) :
    ((TM2.stepAux q v S).stk j).length ≤ (S j).length + stmtPushes q := by
  induction q generalizing v S with
  | push k f q ih =>
    refine (ih _ _).trans ?_
    simp only [stmtPushes]
    by_cases h : j = k
    · subst h; simp; omega
    · rw [Function.update_of_ne h]; omega
  | peek k f q ih => exact (ih _ _).trans (by simp [stmtPushes])
  | pop k f q ih =>
    refine (ih _ _).trans ?_
    simp only [stmtPushes]
    by_cases h : j = k
    · subst h; simp
    · rw [Function.update_of_ne h]
  | load a q ih => exact (ih _ _).trans (by simp [stmtPushes])
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, stmtPushes]
    cases f v
    · exact (ih₂ _ _).trans (by omega)
    · exact (ih₁ _ _).trans (by omega)
  | goto f => simp [TM2.stepAux]
  | halt => simp [TM2.stepAux]

/-- The largest number of pushes of any statement of the machine. -/
def maxPushes (tm : FinTM2) : ℕ :=
  letI := tm.ΛFin
  Finset.univ.sup fun l => stmtPushes (tm.m l)

lemma step_stk_length (tm : FinTM2) {c d : tm.Cfg} (h : tm.step c = some d) (j : tm.K) :
    (d.stk j).length ≤ (c.stk j).length + maxPushes tm := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [FinTM2.step, TM2.step] at h
  · simp only [FinTM2.step, TM2.step] at h
    cases Option.some.inj h
    refine (stepAux_stk_length _ _ _ _).trans ?_
    letI := tm.ΛFin
    have : stmtPushes (tm.m l) ≤ maxPushes tm :=
      Finset.le_sup (f := fun l => stmtPushes (tm.m l)) (Finset.mem_univ l)
    exact Nat.add_le_add_left this _

lemma iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

lemma iterate_stk_length (tm : FinTM2) (n : ℕ) :
    ∀ (c d : tm.Cfg), (flip bind tm.step)^[n] (some c) = some d →
      ∀ j, (d.stk j).length ≤ (c.stk j).length + maxPushes tm * n := by
  induction n with
  | zero =>
    intro c d h j
    simp only [Function.iterate_zero, id, Option.some.injEq] at h
    subst h; simp
  | succ n ih =>
    intro c d h j
    rw [Function.iterate_succ_apply] at h
    change (flip bind tm.step)^[n] (tm.step c) = some d at h
    cases hc : tm.step c with
    | none => rw [hc, iterate_none] at h; exact absurd h (by simp)
    | some c' =>
      rw [hc] at h
      have h1 := ih c' d h j
      have h2 := step_stk_length tm hc j
      rw [Nat.mul_succ]; omega

lemma initList_stk_length (tm : FinTM2) (s : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((initList tm s).stk k).length ≤ s.length := by
  simp only [initList]
  split
  · rename_i h
    subst h
    rfl
  · simp

lemma haltList_stk_k₁ (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    (haltList tm s).stk tm.k₁ = s := by
  simp [haltList]

/-- The output of a run is at most the input plus `maxPushes` per step. -/
lemma output_length_le (tm : FinTM2) {s : List (tm.Γ tm.k₀)} {out : List (tm.Γ tm.k₁)} {T : ℕ}
    (h : TM2OutputsInTime tm s (some out) T) : out.length ≤ s.length + maxPushes tm * T := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  have := iterate_stk_length tm n _ _ hn tm.k₁
  rw [haltList_stk_k₁] at this
  have h2 := initList_stk_length tm s tm.k₁
  have h3 : maxPushes tm * n ≤ maxPushes tm * T := Nat.mul_le_mul_left _ hle
  omega


/- ### The composed machine -/

section Comp

variable (M1 M2 : FinTM2)

/-- Stacks of the composed machine: those of `M1`, those of `M2`, and one Bool buffer. -/
abbrev compK := M1.K ⊕ (M2.K ⊕ Unit)

/-- Alphabets of the composed machine. -/
abbrev compΓ (k : compK M1 M2) : Type :=
  Sum.casesOn (motive := fun _ => Type) k M1.Γ
    (fun k => Sum.casesOn (motive := fun _ => Type) k M2.Γ (fun _ => Bool))

/-- Labels: those of `M1`, those of `M2`, and two copy phases. -/
abbrev compΛ := M1.Λ ⊕ (M2.Λ ⊕ Bool)

/-- States: both machines' states and one buffered bit. -/
abbrev compσ := M1.σ × M2.σ × Option Bool

/-- `M1`'s statements, with `halt` replaced by a jump to the copy phase. -/
def lift1 : TM2.Stmt M1.Γ M1.Λ M1.σ → TM2.Stmt (compΓ M1 M2) (compΛ M1 M2) (compσ M1 M2)
  | .push k f q => .push (Sum.inl k) (fun v => f v.1) (lift1 q)
  | .peek k f q => .peek (Sum.inl k) (fun v o => (f v.1 o, v.2)) (lift1 q)
  | .pop k f q => .pop (Sum.inl k) (fun v o => (f v.1 o, v.2)) (lift1 q)
  | .load a q => .load (fun v => (a v.1, v.2)) (lift1 q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (lift1 q₁) (lift1 q₂)
  | .goto f => .goto (fun v => Sum.inl (f v.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr false))

/-- `M2`'s statements. -/
def lift2 : TM2.Stmt M2.Γ M2.Λ M2.σ → TM2.Stmt (compΓ M1 M2) (compΛ M1 M2) (compσ M1 M2)
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun v => f v.2.1) (lift2 q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (lift2 q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (lift2 q)
  | .load a q => .load (fun v => (v.1, a v.2.1, v.2.2)) (lift2 q)
  | .branch f q₁ q₂ => .branch (fun v => f v.2.1) (lift2 q₁) (lift2 q₂)
  | .goto f => .goto (fun v => Sum.inr (Sum.inl (f v.2.1)))
  | .halt => .halt

variable (e1 : M1.Γ M1.k₁ → Bool) (e2 : Bool → M2.Γ M2.k₀)

/-- The program of the composed machine. Phase `false` moves `M1`'s output onto the buffer
(reversing it), phase `true` moves the buffer onto `M2`'s input (reversing it back). -/
def compProg : compΛ M1 M2 → TM2.Stmt (compΓ M1 M2) (compΛ M1 M2) (compσ M1 M2)
  | .inl l => lift1 M1 M2 (M1.m l)
  | .inr (.inl l) => lift2 M1 M2 (M2.m l)
  | .inr (.inr false) =>
    .pop (Sum.inl M1.k₁) (fun v o => (v.1, v.2.1, o.map e1)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inr (Sum.inr ())) (fun v => v.2.2.getD false) <|
          .goto fun _ => Sum.inr (Sum.inr false))
        (.goto fun _ => Sum.inr (Sum.inr true))
  | .inr (.inr true) =>
    .pop (Sum.inr (Sum.inr ())) (fun v o => (v.1, v.2.1, o)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inr (Sum.inl M2.k₀)) (fun v => e2 (v.2.2.getD false)) <|
          .goto fun _ => Sum.inr (Sum.inr true))
        (.goto fun _ => Sum.inr (Sum.inl M2.main))

/-- The composed machine. -/
def compTM : FinTM2 :=
  letI := M1.kFin; letI := M2.kFin; letI := M1.ΛFin; letI := M2.ΛFin
  letI := M1.σFin; letI := M2.σFin
  { K := compK M1 M2
    k₀ := Sum.inl M1.k₀
    k₁ := Sum.inr (Sum.inl M2.k₁)
    Γ := compΓ M1 M2
    Λ := compΛ M1 M2
    main := Sum.inl M1.main
    σ := compσ M1 M2
    initialState := (M1.initialState, M2.initialState, none)
    Γk₀Fin := M1.Γk₀Fin
    m := compProg M1 M2 e1 e2 }

/-- Stacks of the composed machine from stacks of the parts and the buffer. -/
def mkStk (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (a : List Bool) :
    ∀ k : compK M1 M2, List (compΓ M1 M2 k)
  | .inl k => S1 k
  | .inr (.inl k) => S2 k
  | .inr (.inr _) => a

end Comp


section CompLemmas

variable (M1 M2 : FinTM2) (e1 : M1.Γ M1.k₁ → Bool) (e2 : Bool → M2.Γ M2.k₀)

lemma mkStk_update_inl (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (a : List Bool)
    (k : M1.K) (v : List (M1.Γ k)) :
    Function.update (mkStk M1 M2 S1 S2 a) (Sum.inl k) v =
      mkStk M1 M2 (Function.update S1 k v) S2 a := by
  funext k'
  rcases k' with k' | k' | u
  · by_cases h : k' = k
    · subst h; simp [mkStk]
    · rw [Function.update_of_ne (by simpa using h)]
      simp [mkStk, Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

lemma mkStk_update_inr (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (a : List Bool)
    (k : M2.K) (v : List (M2.Γ k)) :
    Function.update (mkStk M1 M2 S1 S2 a) (Sum.inr (Sum.inl k)) v =
      mkStk M1 M2 S1 (Function.update S2 k v) a := by
  funext k'
  rcases k' with k' | k' | u
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : k' = k
    · subst h; simp [mkStk]
    · rw [Function.update_of_ne (by simpa using h)]
      simp [mkStk, Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl

lemma mkStk_update_buf (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (a a' : List Bool) :
    Function.update (mkStk M1 M2 S1 S2 a) (Sum.inr (Sum.inr ())) a' = mkStk M1 M2 S1 S2 a' := by
  funext k'
  rcases k' with k' | k' | u
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · cases u; simp [mkStk]

/-- Configurations of `M1` inside the composed machine; a halted `M1` sits at the copy phase. -/
def liftCfg1 (c : TM2.Cfg M1.Γ M1.Λ M1.σ) : TM2.Cfg (compΓ M1 M2) (compΛ M1 M2) (compσ M1 M2) :=
  ⟨c.l.elim (some (Sum.inr (Sum.inr false))) (fun l => some (Sum.inl l)),
    (c.var, M2.initialState, none), mkStk M1 M2 c.stk (fun _ => []) []⟩

/-- Configurations of `M2` inside the composed machine. -/
def liftCfg2 (c : TM2.Cfg M2.Γ M2.Λ M2.σ) : TM2.Cfg (compΓ M1 M2) (compΛ M1 M2) (compσ M1 M2) :=
  ⟨c.l.map (fun l => Sum.inr (Sum.inl l)), (M1.initialState, c.var, none),
    mkStk M1 M2 (fun _ => []) c.stk []⟩

lemma stepAux_lift1 (q : TM2.Stmt M1.Γ M1.Λ M1.σ) (v : M1.σ) (S : ∀ k, List (M1.Γ k)) :
    TM2.stepAux (lift1 M1 M2 q) (v, M2.initialState, none) (mkStk M1 M2 S (fun _ => []) []) =
      liftCfg1 M1 M2 (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [lift1, TM2.stepAux]
    rw [show mkStk M1 M2 S (fun _ => []) [] (Sum.inl k) = S k from rfl, mkStk_update_inl]
    exact ih _ _
  | peek k f q ih =>
    simp only [lift1, TM2.stepAux]
    exact ih _ _
  | pop k f q ih =>
    simp only [lift1, TM2.stepAux]
    rw [show mkStk M1 M2 S (fun _ => []) [] (Sum.inl k) = S k from rfl, mkStk_update_inl]
    exact ih _ _
  | load a q ih =>
    simp only [lift1, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [lift1, TM2.stepAux, ih₁, ih₂]
    cases f v <;> rfl
  | goto f => rfl
  | halt => rfl

lemma stepAux_lift2 (q : TM2.Stmt M2.Γ M2.Λ M2.σ) (v : M2.σ) (S : ∀ k, List (M2.Γ k)) :
    TM2.stepAux (lift2 M1 M2 q) (M1.initialState, v, none) (mkStk M1 M2 (fun _ => []) S []) =
      liftCfg2 M1 M2 (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [lift2, TM2.stepAux]
    rw [show mkStk M1 M2 (fun _ => []) S [] (Sum.inr (Sum.inl k)) = S k from rfl,
      mkStk_update_inr]
    exact ih _ _
  | peek k f q ih =>
    simp only [lift2, TM2.stepAux]
    exact ih _ _
  | pop k f q ih =>
    simp only [lift2, TM2.stepAux]
    rw [show mkStk M1 M2 (fun _ => []) S [] (Sum.inr (Sum.inl k)) = S k from rfl,
      mkStk_update_inr]
    exact ih _ _
  | load a q ih =>
    simp only [lift2, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [lift2, TM2.stepAux, ih₁, ih₂]
    cases f v <;> rfl
  | goto f => rfl
  | halt => rfl

lemma step_lift1 (l : M1.Λ) (v : M1.σ) (S : ∀ k, List (M1.Γ k)) :
    (compTM M1 M2 e1 e2).step (liftCfg1 M1 M2 ⟨some l, v, S⟩) =
      some (liftCfg1 M1 M2 (TM2.stepAux (M1.m l) v S)) := by
  show some (TM2.stepAux (lift1 M1 M2 (M1.m l)) (v, M2.initialState, none)
    (mkStk M1 M2 S (fun _ => []) [])) = _
  rw [stepAux_lift1]

lemma step_lift2 (c : TM2.Cfg M2.Γ M2.Λ M2.σ) :
    (compTM M1 M2 e1 e2).step (liftCfg2 M1 M2 c) = (M2.step c).map (liftCfg2 M1 M2) := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · show some (TM2.stepAux (lift2 M1 M2 (M2.m l)) (M1.initialState, v, none)
      (mkStk M1 M2 (fun _ => []) S [])) = _
    rw [stepAux_lift2]
    rfl

lemma run_lift1 (n : ℕ) : ∀ (c d : TM2.Cfg M1.Γ M1.Λ M1.σ),
    (flip bind M1.step)^[n] (some c) = some d →
      (flip bind (compTM M1 M2 e1 e2).step)^[n] (some (liftCfg1 M1 M2 c)) =
        some (liftCfg1 M1 M2 d) := by
  induction n with
  | zero =>
    intro c d h
    cases Option.some.inj h
    rfl
  | succ n ih =>
    intro c d h
    rw [Function.iterate_succ_apply] at h ⊢
    change (flip bind M1.step)^[n] (M1.step c) = some d at h
    rcases c with ⟨_ | l, v, S⟩
    · change (flip bind M1.step)^[n] none = some d at h
      rw [iterate_none] at h; exact absurd h (by simp)
    · change (flip bind M1.step)^[n] (some (TM2.stepAux (M1.m l) v S)) = some d at h
      change (flip bind (compTM M1 M2 e1 e2).step)^[n]
        ((compTM M1 M2 e1 e2).step (liftCfg1 M1 M2 ⟨some l, v, S⟩)) = _
      rw [step_lift1]
      exact ih _ _ h

lemma run_lift2 (n : ℕ) (o : Option (TM2.Cfg M2.Γ M2.Λ M2.σ)) :
    (flip bind (compTM M1 M2 e1 e2).step)^[n] (o.map (liftCfg2 M1 M2)) =
      ((flip bind M2.step)^[n] o).map (liftCfg2 M1 M2) := by
  have hs : Function.Semiconj (Option.map (liftCfg2 M1 M2)) (flip bind M2.step)
      (flip bind (compTM M1 M2 e1 e2).step) := by
    intro o
    rcases o with _ | c
    · rfl
    · show (M2.step c).map (liftCfg2 M1 M2) = (compTM M1 M2 e1 e2).step (liftCfg2 M1 M2 c)
      rw [step_lift2]
  exact ((hs.iterate_right n) o).symm

end CompLemmas


section CompCopy

variable (M1 M2 : FinTM2) (e1 : M1.Γ M1.k₁ → Bool) (e2 : Bool → M2.Γ M2.k₀)

/-- A configuration in one of the two copy phases. -/
def copyCfg (b : Bool) (o : Option Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k))
    (a : List Bool) : TM2.Cfg (compΓ M1 M2) (compΛ M1 M2) (compσ M1 M2) :=
  ⟨some (Sum.inr (Sum.inr b)), (M1.initialState, M2.initialState, o), mkStk M1 M2 S1 S2 a⟩

lemma step_copy0_cons (o : Option Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k))
    (a : List Bool) (x : M1.Γ M1.k₁) (t : List (M1.Γ M1.k₁)) (h : S1 M1.k₁ = x :: t) :
    (compTM M1 M2 e1 e2).step (copyCfg M1 M2 false o S1 S2 a) =
      some (copyCfg M1 M2 false (some (e1 x)) (Function.update S1 M1.k₁ t) S2 (e1 x :: a)) := by
  show some (TM2.stepAux (compProg M1 M2 e1 e2 (Sum.inr (Sum.inr false)))
    (M1.initialState, M2.initialState, o) (mkStk M1 M2 S1 S2 a)) = _
  simp only [compProg, TM2.stepAux]
  rw [show mkStk M1 M2 S1 S2 a (Sum.inl M1.k₁) = S1 M1.k₁ from rfl, h, mkStk_update_inl]
  simp only [List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some, cond_true,
    Option.getD_some]
  rw [show mkStk M1 M2 (Function.update S1 M1.k₁ t) S2 a (Sum.inr (Sum.inr ())) = a from rfl,
    mkStk_update_buf]
  rfl

lemma step_copy0_nil (o : Option Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k))
    (a : List Bool) (h : S1 M1.k₁ = []) :
    (compTM M1 M2 e1 e2).step (copyCfg M1 M2 false o S1 S2 a) =
      some (copyCfg M1 M2 true none S1 S2 a) := by
  show some (TM2.stepAux (compProg M1 M2 e1 e2 (Sum.inr (Sum.inr false)))
    (M1.initialState, M2.initialState, o) (mkStk M1 M2 S1 S2 a)) = _
  simp only [compProg, TM2.stepAux]
  rw [show mkStk M1 M2 S1 S2 a (Sum.inl M1.k₁) = S1 M1.k₁ from rfl, h, mkStk_update_inl]
  simp only [List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, cond_false]
  rw [← h, Function.update_eq_self]
  rfl

lemma step_copy1_cons (o : Option Bool) (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k))
    (b : Bool) (a : List Bool) :
    (compTM M1 M2 e1 e2).step (copyCfg M1 M2 true o S1 S2 (b :: a)) =
      some (copyCfg M1 M2 true (some b) S1 (Function.update S2 M2.k₀ (e2 b :: S2 M2.k₀)) a) := by
  show some (TM2.stepAux (compProg M1 M2 e1 e2 (Sum.inr (Sum.inr true)))
    (M1.initialState, M2.initialState, o) (mkStk M1 M2 S1 S2 (b :: a))) = _
  simp only [compProg, TM2.stepAux]
  rw [show mkStk M1 M2 S1 S2 (b :: a) (Sum.inr (Sum.inr ())) = b :: a from rfl, mkStk_update_buf]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
  rw [show mkStk M1 M2 S1 S2 a (Sum.inr (Sum.inl M2.k₀)) = S2 M2.k₀ from rfl, mkStk_update_inr]
  rfl

lemma step_copy1_nil (o : Option Bool) (S2 : ∀ k, List (M2.Γ k)) :
    (compTM M1 M2 e1 e2).step (copyCfg M1 M2 true o (fun _ => []) S2 []) =
      some (liftCfg2 M1 M2 ⟨some M2.main, M2.initialState, S2⟩) := by
  show some (TM2.stepAux (compProg M1 M2 e1 e2 (Sum.inr (Sum.inr true)))
    (M1.initialState, M2.initialState, o) (mkStk M1 M2 (fun _ => []) S2 [])) = _
  simp only [compProg, TM2.stepAux]
  rw [show mkStk M1 M2 (fun _ => []) S2 [] (Sum.inr (Sum.inr ())) = [] from rfl, mkStk_update_buf]
  rfl

lemma copy0_run (S2 : ∀ k, List (M2.Γ k)) (out : List (M1.Γ M1.k₁)) :
    ∀ (o : Option Bool) (S1 : ∀ k, List (M1.Γ k)) (a : List Bool), S1 M1.k₁ = out →
      ∃ n ≤ out.length + 1, (flip bind (compTM M1 M2 e1 e2).step)^[n]
        (some (copyCfg M1 M2 false o S1 S2 a)) =
        some (copyCfg M1 M2 true none (Function.update S1 M1.k₁ []) S2
          ((out.map e1).reverse ++ a)) := by
  induction out with
  | nil =>
    intro o S1 a h
    have h' : Function.update S1 M1.k₁ [] = S1 := by rw [← h, Function.update_eq_self]
    rw [h']
    exact rIn_single (step_copy0_nil M1 M2 e1 e2 o S1 S2 a h)
  | cons x t ih =>
    intro o S1 a h
    have h1 := rIn_single (step_copy0_cons M1 M2 e1 e2 o S1 S2 a x t h)
    have h2 := ih (some (e1 x)) (Function.update S1 M1.k₁ t) (e1 x :: a) (by simp)
    obtain ⟨n, hn, he⟩ := rIn_trans h1 h2
    refine ⟨n, by simp only [List.length_cons]; omega, he.trans ?_⟩
    congr 2
    · exact Function.update_idem _ _ _
    · simp

lemma copy1_run (a : List Bool) :
    ∀ (o : Option Bool) (S2 : ∀ k, List (M2.Γ k)),
      ∃ n ≤ a.length + 1, (flip bind (compTM M1 M2 e1 e2).step)^[n]
        (some (copyCfg M1 M2 true o (fun _ => []) S2 a)) =
        some (liftCfg2 M1 M2 ⟨some M2.main, M2.initialState,
          Function.update S2 M2.k₀ ((a.map e2).reverse ++ S2 M2.k₀)⟩) := by
  induction a with
  | nil =>
    intro o S2
    simp only [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
    exact rIn_single (step_copy1_nil M1 M2 e1 e2 o S2)
  | cons b a ih =>
    intro o S2
    have h1 := rIn_single (step_copy1_cons M1 M2 e1 e2 o (fun _ => []) S2 b a)
    have h2 := ih (some b) (Function.update S2 M2.k₀ (e2 b :: S2 M2.k₀))
    obtain ⟨n, hn, he⟩ := rIn_trans h1 h2
    refine ⟨n, by simp only [List.length_cons]; omega, he.trans ?_⟩
    congr 3
    rw [Function.update_idem, Function.update_self]
    simp

lemma initList_comp (s : List (M1.Γ M1.k₀)) :
    initList (compTM M1 M2 e1 e2) s = liftCfg1 M1 M2 (initList M1 s) := by
  simp only [initList, liftCfg1]
  congr 1
  funext k
  rcases k with k | k | u
  · by_cases h : k = M1.k₀
    · subst h; simp [mkStk, compTM]; rfl
    · simp [mkStk, compTM, h]
  · simp [mkStk, compTM]
  · simp [mkStk, compTM]

lemma initList_eq_update (s : List (M2.Γ M2.k₀)) :
    (⟨some M2.main, M2.initialState, Function.update (fun _ => []) M2.k₀ s⟩ :
      TM2.Cfg M2.Γ M2.Λ M2.σ) = initList M2 s := by
  simp only [initList]
  congr 1
  funext k
  by_cases h : k = M2.k₀
  · subst h; simp
  · rw [Function.update_of_ne h, dif_neg h]

lemma haltList_update_k₁ (out : List (M1.Γ M1.k₁)) :
    Function.update (haltList M1 out).stk M1.k₁ [] = fun _ => [] := by
  funext k
  by_cases h : k = M1.k₁
  · subst h; simp
  · rw [Function.update_of_ne h]; simp [haltList, h]

lemma haltList_comp (out : List (M2.Γ M2.k₁)) :
    liftCfg2 M1 M2 (haltList M2 out) = haltList (compTM M1 M2 e1 e2) out := by
  simp only [liftCfg2, haltList]
  congr 1
  funext k
  rcases k with k | k | u
  · simp [mkStk, compTM]
  · by_cases h : k = M2.k₁
    · subst h; simp [mkStk, compTM]; rfl
    · simp [mkStk, compTM, h]
  · simp [mkStk, compTM]

end CompCopy


/-- Composition of polynomial-time machines whose intermediate alphabet is `Bool`. -/
theorem tm2_comp {α β γ αΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List Bool}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ} (h1 : TM2ComputableInPolyTime ea eb f)
    (h2 : TM2ComputableInPolyTime eb ec g) : Nonempty (TM2ComputableInPolyTime ea ec (g ∘ f)) := by
  classical
  let M1 := h1.tm
  let M2 := h2.tm
  let e1 : M1.Γ M1.k₁ → Bool := h1.outputAlphabet
  let e2 : Bool → M2.Γ M2.k₀ := h2.inputAlphabet.symm
  let c := maxPushes M1
  let N := compTM M1 M2 e1 e2
  let P : Polynomial ℕ := Polynomial.X + Polynomial.C c * h1.time
  let T : Polynomial ℕ := h1.time + 2 * P + 3 + h2.time.comp P
  refine ⟨⟨⟨N, h1.inputAlphabet, h2.outputAlphabet⟩, T, fun a => ?_⟩⟩
  set L := (ea a).length with hL
  set s1 : List (M1.Γ M1.k₀) := List.map h1.inputAlphabet.invFun (ea a) with hs1
  set out : List (M1.Γ M1.k₁) := List.map h1.outputAlphabet.invFun (eb (f a)) with hout
  set s2 : List (M2.Γ M2.k₀) := List.map h2.inputAlphabet.invFun (eb (f a)) with hs2
  set out2 : List (M2.Γ M2.k₁) := List.map h2.outputAlphabet.invFun (ec (g (f a))) with hout2
  have hr1 : TM2OutputsInTime M1 s1 (some out) (h1.time.eval L) := h1.outputsFun a
  have hlen := output_length_le M1 hr1
  obtain ⟨⟨n1, hn1⟩, hle1⟩ := hr1
  have hr2 : TM2OutputsInTime M2 s2 (some out2) (h2.time.eval (eb (f a)).length) :=
    h2.outputsFun (f a)
  obtain ⟨⟨n2, hn2⟩, hle2⟩ := hr2
  have A : ∃ n ≤ n1, (flip bind N.step)^[n] (some (initList N s1)) =
      some (copyCfg M1 M2 false none (haltList M1 out).stk (fun _ => []) []) := by
    refine ⟨n1, le_rfl, ?_⟩
    rw [initList_comp]
    exact run_lift1 M1 M2 e1 e2 n1 _ _ hn1
  have B := copy0_run M1 M2 e1 e2 (fun _ => []) out none (haltList M1 out).stk []
    (haltList_stk_k₁ M1 out)
  rw [haltList_update_k₁] at B
  have C := copy1_run M1 M2 e1 e2 ((out.map e1).reverse ++ []) none (fun _ => [])
  have hmid : ((((out.map e1).reverse ++ []).map e2).reverse ++ ([] : List (M2.Γ M2.k₀))) = s2 := by
    simp only [List.append_nil, List.map_reverse, List.reverse_reverse, List.map_map, hout, hs2]
    congr 1
    funext b
    simp [e1, e2]
  rw [hmid, initList_eq_update] at C
  have D : ∃ n ≤ n2, (flip bind N.step)^[n] (some (liftCfg2 M1 M2 (initList M2 s2))) =
      some (haltList N out2) := by
    refine ⟨n2, le_rfl, ?_⟩
    have := run_lift2 M1 M2 e1 e2 n2 (some (initList M2 s2))
    exact this.trans ((congrArg (Option.map (liftCfg2 M1 M2)) hn2).trans
      (congrArg some (haltList_comp M1 M2 e1 e2 out2)))
  have hall := rIn_trans (rIn_trans (rIn_trans A B) C) D
  have hs1L : s1.length = L := by simp [hs1, hL]
  have houtL : out.length = (eb (f a)).length := by simp [hout]
  have hlen' : out.length ≤ L + c * h1.time.eval L := by
    have := hlen; rw [hs1L] at this; exact this
  have hPL : P.eval L = L + c * h1.time.eval L := by
    simp [P]
  have h2b : h2.time.eval (eb (f a)).length ≤ h2.time.eval (L + c * h1.time.eval L) := by
    apply eval_mono; rw [← houtL]; exact hlen'
  have hTL : T.eval L = h1.time.eval L + 2 * (L + c * h1.time.eval L) + 3 +
      h2.time.eval (L + c * h1.time.eval L) := by
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_comp, hPL]
  have hb : n1 + (out.length + 1) + (((out.map e1).reverse ++ []).length + 1) + n2 ≤ T.eval L := by
    rw [hTL]
    simp only [List.length_append, List.length_reverse, List.length_map, List.length_nil,
      Nat.add_zero]
    have hle1' : n1 ≤ h1.time.eval L := hle1
    have hle2' : n2 ≤ h2.time.eval (eb (f a)).length := hle2
    omega
  exact Classical.choice (by
    obtain ⟨n, hle, he⟩ := rIn_mono hall hb
    exact ⟨⟨⟨n, he⟩, hle⟩⟩)

theorem isPolyTime_comp {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] {f : α → β} {g : β → γ} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (g ∘ f) := by
  obtain ⟨M1⟩ := hf
  obtain ⟨M2⟩ := hg
  exact tm2_comp M1 M2


/- ### Running a machine on the second component -/

section PMR

variable (M : FinTM2)

/-- Stacks: input, stash, buffer (all Bool), then `M`'s. -/
abbrev pmrΓ (k : Fin 3 ⊕ M.K) : Type := Sum.casesOn (motive := fun _ => Type) k (fun _ => Bool) M.Γ

abbrev pmrΛ := M.Λ ⊕ Fin 5

abbrev pmrσ := M.σ × Option Bool

/-- `M`'s statements, with `halt` replaced by a jump to phase 3. -/
def liftP : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (pmrΓ M) (pmrΛ M) (pmrσ M)
  | .push k f q => .push (Sum.inr k) (fun v => f v.1) (liftP q)
  | .peek k f q => .peek (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftP q)
  | .pop k f q => .pop (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftP q)
  | .load a q => .load (fun v => (a v.1, v.2)) (liftP q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (liftP q₁) (liftP q₂)
  | .goto f => .goto (fun v => Sum.inl (f v.1))
  | .halt => .goto (fun _ => Sum.inr 3)

variable (ei : Bool → M.Γ M.k₀) (eo : Bool → M.Γ M.k₁)

def pmr0 : TM2.Stmt (pmrΓ M) (pmrΛ M) (pmrσ M) :=
  .pop (Sum.inl 0) (fun v o => (v.1, o)) <|
    .branch (fun v => v.2 == some true)
      (.pop (Sum.inl 0) (fun v o => (v.1, o)) <|
        .push (Sum.inl 1) (fun v => v.2.getD false) <| .goto fun _ => Sum.inr 0)
      (.goto fun _ => Sum.inr 1)

def pmr1 : TM2.Stmt (pmrΓ M) (pmrΛ M) (pmrσ M) :=
  .pop (Sum.inl 0) (fun v o => (v.1, o)) <|
    .branch (fun v => v.2.isSome)
      (.push (Sum.inl 2) (fun v => v.2.getD false) <| .goto fun _ => Sum.inr 1)
      (.goto fun _ => Sum.inr 2)

def pmr2 : TM2.Stmt (pmrΓ M) (pmrΛ M) (pmrσ M) :=
  .pop (Sum.inl 2) (fun v o => (v.1, o)) <|
    .branch (fun v => v.2.isSome)
      (.push (Sum.inr M.k₀) (fun v => ei (v.2.getD false)) <| .goto fun _ => Sum.inr 2)
      (.goto fun _ => Sum.inl M.main)

def pmr3 : TM2.Stmt (pmrΓ M) (pmrΛ M) (pmrσ M) :=
  .push (Sum.inr M.k₁) (fun _ => eo false) <| .goto fun _ => Sum.inr 4

def pmr4 : TM2.Stmt (pmrΓ M) (pmrΛ M) (pmrσ M) :=
  .pop (Sum.inl 1) (fun v o => (v.1, o)) <|
    .branch (fun v => v.2.isSome)
      (.push (Sum.inr M.k₁) (fun v => eo (v.2.getD false)) <|
        .push (Sum.inr M.k₁) (fun _ => eo true) <| .goto fun _ => Sum.inr 4)
      .halt

/-- Phases: 0 parse the first block into the stash, 1 move the rest to the buffer, 2 buffer to
`M`'s input, 3 push the block terminator, 4 stash onto the output. -/
def pmrProg : pmrΛ M → TM2.Stmt (pmrΓ M) (pmrΛ M) (pmrσ M)
  | .inl l => liftP M (M.m l)
  | .inr p =>
    if p = 0 then pmr0 M else if p = 1 then pmr1 M else if p = 2 then pmr2 M ei
    else if p = 3 then pmr3 M eo else pmr4 M eo

def pmrTM : FinTM2 :=
  letI := M.kFin; letI := M.ΛFin; letI := M.σFin
  { K := Fin 3 ⊕ M.K
    k₀ := Sum.inl 0
    k₁ := Sum.inr M.k₁
    Γ := pmrΓ M
    Λ := pmrΛ M
    main := Sum.inr 0
    σ := pmrσ M
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := pmrProg M ei eo }

def pmrStk (i st b : List Bool) (S : ∀ k, List (M.Γ k)) : ∀ k : Fin 3 ⊕ M.K, List (pmrΓ M k)
  | .inl j => if j = 0 then i else if j = 1 then st else b
  | .inr k => S k

lemma pmrStk_update_inr (i st b : List Bool) (S : ∀ k, List (M.Γ k)) (k : M.K)
    (v : List (M.Γ k)) :
    Function.update (pmrStk M i st b S) (Sum.inr k) v = pmrStk M i st b (Function.update S k v) := by
  funext k'
  rcases k' with j | k'
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : k' = k
    · subst h; simp [pmrStk]
    · rw [Function.update_of_ne (by simpa using h)]
      simp [pmrStk, Function.update_of_ne h]

lemma pmrStk_update_0 (i st b i' : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (pmrStk M i st b S) (Sum.inl 0) i' = pmrStk M i' st b S := by
  funext k'
  rcases k' with j | k'
  · fin_cases j <;> simp [pmrStk, Function.update]
  · rw [Function.update_of_ne (by simp)]; rfl

lemma pmrStk_update_1 (i st b st' : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (pmrStk M i st b S) (Sum.inl 1) st' = pmrStk M i st' b S := by
  funext k'
  rcases k' with j | k'
  · fin_cases j <;> simp [pmrStk, Function.update]
  · rw [Function.update_of_ne (by simp)]; rfl

lemma pmrStk_update_2 (i st b b' : List Bool) (S : ∀ k, List (M.Γ k)) :
    Function.update (pmrStk M i st b S) (Sum.inl 2) b' = pmrStk M i st b' S := by
  funext k'
  rcases k' with j | k'
  · fin_cases j <;> simp [pmrStk, Function.update]
  · rw [Function.update_of_ne (by simp)]; rfl

end PMR


section PMRLemmas

variable (M : FinTM2) (ei : Bool → M.Γ M.k₀) (eo : Bool → M.Γ M.k₁)

def cfgP (p : Fin 5) (o : Option Bool) (i st b : List Bool) (S : ∀ k, List (M.Γ k)) :
    TM2.Cfg (pmrΓ M) (pmrΛ M) (pmrσ M) :=
  ⟨some (Sum.inr p), (M.initialState, o), pmrStk M i st b S⟩

def liftCfgP (st : List Bool) (c : TM2.Cfg M.Γ M.Λ M.σ) : TM2.Cfg (pmrΓ M) (pmrΛ M) (pmrσ M) :=
  ⟨c.l.elim (some (Sum.inr 3)) (fun l => some (Sum.inl l)), (c.var, none), pmrStk M [] st [] c.stk⟩

lemma stepAux_liftP (st : List Bool) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ)
    (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (liftP M q) (v, none) (pmrStk M [] st [] S) = liftCfgP M st (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [liftP, TM2.stepAux]
    rw [show pmrStk M [] st [] S (Sum.inr k) = S k from rfl, pmrStk_update_inr]
    exact ih _ _
  | peek k f q ih => simp only [liftP, TM2.stepAux]; exact ih _ _
  | pop k f q ih =>
    simp only [liftP, TM2.stepAux]
    rw [show pmrStk M [] st [] S (Sum.inr k) = S k from rfl, pmrStk_update_inr]
    exact ih _ _
  | load a q ih => simp only [liftP, TM2.stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [liftP, TM2.stepAux, ih₁, ih₂]
    cases f v <;> rfl
  | goto f => rfl
  | halt => rfl

lemma step_liftP (st : List Bool) (l : M.Λ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    (pmrTM M ei eo).step (liftCfgP M st ⟨some l, v, S⟩) =
      some (liftCfgP M st (TM2.stepAux (M.m l) v S)) := by
  show some (TM2.stepAux (liftP M (M.m l)) (v, none) (pmrStk M [] st [] S)) = _
  rw [stepAux_liftP]


lemma run_liftP (st : List Bool) (n : ℕ) : ∀ (c d : TM2.Cfg M.Γ M.Λ M.σ),
    (flip bind M.step)^[n] (some c) = some d →
      (flip bind (pmrTM M ei eo).step)^[n] (some (liftCfgP M st c)) = some (liftCfgP M st d) := by
  induction n with
  | zero => intro c d h; cases Option.some.inj h; rfl
  | succ n ih =>
    intro c d h
    rw [Function.iterate_succ_apply] at h ⊢
    change (flip bind M.step)^[n] (M.step c) = some d at h
    rcases c with ⟨_ | l, v, S⟩
    · change (flip bind M.step)^[n] none = some d at h
      rw [iterate_none] at h; exact absurd h (by simp)
    · change (flip bind M.step)^[n] (some (TM2.stepAux (M.m l) v S)) = some d at h
      change (flip bind (pmrTM M ei eo).step)^[n]
        ((pmrTM M ei eo).step (liftCfgP M st ⟨some l, v, S⟩)) = _
      rw [step_liftP]
      exact ih _ _ h

lemma step0_true (o : Option Bool) (x : Bool) (rest st b : List Bool) (S : ∀ k, List (M.Γ k)) :
    (pmrTM M ei eo).step (cfgP M 0 o (true :: x :: rest) st b S) =
      some (cfgP M 0 (some x) rest (x :: st) b S) := by
  change some (TM2.stepAux (pmr0 M) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [pmr0, TM2.stepAux, pmrStk, pmrStk_update_0, pmrStk_update_1, pmrStk_update_2,
    pmrStk_update_inr, cfgP, liftCfgP, Function.update_idem]

lemma step0_false (o : Option Bool) (rest st b : List Bool) (S : ∀ k, List (M.Γ k)) :
    (pmrTM M ei eo).step (cfgP M 0 o (false :: rest) st b S) =
      some (cfgP M 1 (some false) rest st b S) := by
  change some (TM2.stepAux (pmr0 M) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [pmr0, TM2.stepAux, pmrStk, pmrStk_update_0, pmrStk_update_1, pmrStk_update_2,
    pmrStk_update_inr, cfgP, liftCfgP, Function.update_idem]

lemma step1_cons (o : Option Bool) (x : Bool) (rest st b : List Bool) (S : ∀ k, List (M.Γ k)) :
    (pmrTM M ei eo).step (cfgP M 1 o (x :: rest) st b S) =
      some (cfgP M 1 (some x) rest st (x :: b) S) := by
  change some (TM2.stepAux (pmr1 M) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [pmr1, TM2.stepAux, pmrStk, pmrStk_update_0, pmrStk_update_1, pmrStk_update_2,
    pmrStk_update_inr, cfgP, liftCfgP, Function.update_idem]

lemma step1_nil (o : Option Bool) (st b : List Bool) (S : ∀ k, List (M.Γ k)) :
    (pmrTM M ei eo).step (cfgP M 1 o [] st b S) = some (cfgP M 2 none [] st b S) := by
  change some (TM2.stepAux (pmr1 M) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [pmr1, TM2.stepAux, pmrStk, pmrStk_update_0, pmrStk_update_1, pmrStk_update_2,
    pmrStk_update_inr, cfgP, liftCfgP, Function.update_idem]

lemma step2_cons (o : Option Bool) (x : Bool) (st b : List Bool) (S : ∀ k, List (M.Γ k)) :
    (pmrTM M ei eo).step (cfgP M 2 o [] st (x :: b) S) =
      some (cfgP M 2 (some x) [] st b (Function.update S M.k₀ (ei x :: S M.k₀))) := by
  change some (TM2.stepAux (pmr2 M ei) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [pmr2, TM2.stepAux, pmrStk, pmrStk_update_0, pmrStk_update_1, pmrStk_update_2,
    pmrStk_update_inr, cfgP, liftCfgP, Function.update_idem]

lemma step2_nil (o : Option Bool) (st : List Bool) (S : ∀ k, List (M.Γ k)) :
    (pmrTM M ei eo).step (cfgP M 2 o [] st [] S) =
      some (liftCfgP M st ⟨some M.main, M.initialState, S⟩) := by
  change some (TM2.stepAux (pmr2 M ei) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [pmr2, TM2.stepAux, pmrStk, pmrStk_update_0, pmrStk_update_1, pmrStk_update_2,
    pmrStk_update_inr, cfgP, liftCfgP, Function.update_idem]

lemma step3 (o : Option Bool) (st : List Bool) (S : ∀ k, List (M.Γ k)) :
    (pmrTM M ei eo).step (cfgP M 3 o [] st [] S) =
      some (cfgP M 4 o [] st [] (Function.update S M.k₁ (eo false :: S M.k₁))) := by
  change some (TM2.stepAux (pmr3 M eo) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp only [pmr3, TM2.stepAux]
  rw [show pmrStk M [] st [] S (Sum.inr M.k₁) = S M.k₁ from rfl, pmrStk_update_inr]
  rfl

lemma step4_cons (o : Option Bool) (x : Bool) (st : List Bool) (S : ∀ k, List (M.Γ k)) :
    (pmrTM M ei eo).step (cfgP M 4 o [] (x :: st) [] S) =
      some (cfgP M 4 (some x) [] st [] (Function.update S M.k₁ (eo true :: eo x :: S M.k₁))) := by
  change some (TM2.stepAux (pmr4 M eo) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [pmr4, TM2.stepAux, pmrStk, pmrStk_update_0, pmrStk_update_1, pmrStk_update_2,
    pmrStk_update_inr, cfgP, liftCfgP, Function.update_idem]

lemma step4_nil (o : Option Bool) (S : ∀ k, List (M.Γ k)) :
    (pmrTM M ei eo).step (cfgP M 4 o [] [] [] S) =
      some ⟨none, (M.initialState, none), pmrStk M [] [] [] S⟩ := by
  change some (TM2.stepAux (pmr4 M eo) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [pmr4, TM2.stepAux, pmrStk, pmrStk_update_0, pmrStk_update_1, pmrStk_update_2,
    pmrStk_update_inr, cfgP, liftCfgP, Function.update_idem]
  rfl

end PMRLemmas


section PMRRuns

variable (M : FinTM2) (ei : Bool → M.Γ M.k₀) (eo : Bool → M.Γ M.k₁)

lemma parse_runP (b : List Bool) (S : ∀ k, List (M.Γ k)) (rest : List Bool) (A : List Bool) :
    ∀ (st : List Bool) (o : Option Bool),
      ∃ n ≤ A.length + 1, (flip bind (pmrTM M ei eo).step)^[n]
        (some (cfgP M 0 o (delimit A ++ rest) st b S)) =
        some (cfgP M 1 (some false) rest (A.reverse ++ st) b S) := by
  induction A with
  | nil => intro st o; exact rIn_single (step0_false M ei eo o rest st b S)
  | cons x A ih =>
    intro st o
    obtain ⟨n, hn, he⟩ := rIn_trans
      (rIn_single (step0_true M ei eo o x (delimit A ++ rest) st b S)) (ih (x :: st) (some x))
    refine ⟨n, by simp only [List.length_cons]; omega, he.trans ?_⟩
    simp

lemma move_runP (st : List Bool) (S : ∀ k, List (M.Γ k)) (B : List Bool) :
    ∀ (b : List Bool) (o : Option Bool),
      ∃ n ≤ B.length + 1, (flip bind (pmrTM M ei eo).step)^[n]
        (some (cfgP M 1 o B st b S)) = some (cfgP M 2 none [] st (B.reverse ++ b) S) := by
  induction B with
  | nil => intro b o; exact rIn_single (step1_nil M ei eo o st b S)
  | cons x B ih =>
    intro b o
    obtain ⟨n, hn, he⟩ := rIn_trans (rIn_single (step1_cons M ei eo o x B st b S)) (ih (x :: b) (some x))
    refine ⟨n, by simp only [List.length_cons]; omega, he.trans ?_⟩
    simp

lemma buf_runP (st : List Bool) (b : List Bool) :
    ∀ (S : ∀ k, List (M.Γ k)) (o : Option Bool),
      ∃ n ≤ b.length + 1, (flip bind (pmrTM M ei eo).step)^[n]
        (some (cfgP M 2 o [] st b S)) =
        some (liftCfgP M st ⟨some M.main, M.initialState,
          Function.update S M.k₀ ((b.map ei).reverse ++ S M.k₀)⟩) := by
  induction b with
  | nil =>
    intro S o
    simp only [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
    exact rIn_single (step2_nil M ei eo o st S)
  | cons x b ih =>
    intro S o
    obtain ⟨n, hn, he⟩ := rIn_trans (rIn_single (step2_cons M ei eo o x st b S))
      (ih (Function.update S M.k₀ (ei x :: S M.k₀)) (some x))
    refine ⟨n, by simp only [List.length_cons]; omega, he.trans ?_⟩
    congr 3
    rw [Function.update_idem, Function.update_self]
    simp

lemma out_runP (l : List Bool) :
    ∀ (S : ∀ k, List (M.Γ k)) (o : Option Bool),
      ∃ n ≤ l.length + 1, (flip bind (pmrTM M ei eo).step)^[n]
        (some (cfgP M 4 o [] l [] S)) =
        some ⟨none, (M.initialState, none), pmrStk M [] [] [] (Function.update S M.k₁
          ((l.reverse.flatMap fun x => [eo true, eo x]) ++ S M.k₁))⟩ := by
  induction l with
  | nil =>
    intro S o
    simp only [List.reverse_nil, List.flatMap_nil, List.nil_append, Function.update_eq_self]
    exact rIn_single (step4_nil M ei eo o S)
  | cons x l ih =>
    intro S o
    obtain ⟨n, hn, he⟩ := rIn_trans (rIn_single (step4_cons M ei eo o x l S))
      (ih (Function.update S M.k₁ (eo true :: eo x :: S M.k₁)) (some x))
    refine ⟨n, by simp only [List.length_cons]; omega, he.trans ?_⟩
    congr 3
    rw [Function.update_idem, Function.update_self]
    simp

lemma initList_pmr (l : List Bool) :
    initList (pmrTM M ei eo) l = cfgP M 0 none l [] [] (fun _ => []) := by
  simp only [initList, cfgP]
  congr 1
  funext k
  rcases k with j | k
  · fin_cases j <;> simp [pmrStk, pmrTM] <;> rfl
  · simp [pmrStk, pmrTM]

lemma haltList_pmr (S : ∀ k, List (M.Γ k)) (hS : ∀ k, k ≠ M.k₁ → S k = []) (Z : List (M.Γ M.k₁)) :
    (⟨none, (M.initialState, none), pmrStk M [] [] [] (Function.update S M.k₁ Z)⟩ :
      TM2.Cfg (pmrΓ M) (pmrΛ M) (pmrσ M)) = haltList (pmrTM M ei eo) Z := by
  simp only [haltList]
  congr 1
  funext k
  rcases k with j | k
  · fin_cases j <;> simp [pmrStk, pmrTM]
  · by_cases h : k = M.k₁
    · subst h; simp [pmrStk, pmrTM]; rfl
    · simp [pmrStk, pmrTM, h, hS k h]

end PMRRuns

lemma delimit_eq_flatMap (A : List Bool) :
    delimit A = (A.flatMap fun x => [true, x]) ++ [false] := by
  induction A with
  | nil => rfl
  | cons x A ih => simp [delimit, ih]

theorem isPolyTime_prodMap_right {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] {g : β → γ} (hg : IsPolyTime g) :
    IsPolyTime (fun p : α × β => (p.1, g p.2)) := by
  classical
  obtain ⟨H⟩ := hg
  let M := H.tm
  let ei : Bool → M.Γ M.k₀ := H.inputAlphabet.symm
  let eo : Bool → M.Γ M.k₁ := H.outputAlphabet.symm
  let N := pmrTM M ei eo
  let T : Polynomial ℕ := 3 * Polynomial.X + 5 + H.time
  refine ⟨⟨⟨N, Equiv.refl Bool, H.outputAlphabet⟩, T, fun p => ?_⟩⟩
  set A := bitEncode p.1 with hA
  set B := bitEncode p.2 with hB
  have henc : (BitstringEncoding.toEncoding (α := α × β)).encode p = delimit A ++ B := rfl
  have hin : List.map ((Equiv.refl Bool : N.Γ N.k₀ ≃ Bool).invFun)
      ((BitstringEncoding.toEncoding (α := α × β)).encode p) = delimit A ++ B := by
    rw [henc]; exact List.map_id _
  set sB : List (M.Γ M.k₀) := List.map H.inputAlphabet.invFun B with hsB
  set outM : List (M.Γ M.k₁) :=
    List.map H.outputAlphabet.invFun ((BitstringEncoding.toEncoding (α := γ)).encode (g p.2))
    with houtM
  have hr : TM2OutputsInTime M sB (some outM) (H.time.eval B.length) := H.outputsFun p.2
  have h1 := parse_runP M ei eo [] (fun _ => []) B A [] none
  have h2 := move_runP M ei eo (A.reverse ++ []) (fun _ => []) B [] (some false)
  have h3 := buf_runP M ei eo (A.reverse ++ []) (B.reverse ++ []) (fun _ => []) none
  have hmid : Function.update (fun _ => []) M.k₀
      (((B.reverse ++ []).map ei).reverse ++ ([] : List (M.Γ M.k₀))) =
        Function.update (fun _ => []) M.k₀ sB := by
    congr 1
    simp [hsB, ei, List.map_reverse]
  rw [hmid, initList_eq_update] at h3
  have h4 : ∃ n ≤ H.time.eval B.length,
      (flip bind N.step)^[n] (some (liftCfgP M (A.reverse ++ []) (initList M sB))) =
      some (cfgP M 3 none [] (A.reverse ++ []) [] (haltList M outM).stk) := by
    obtain ⟨⟨nM, hnM⟩, hleM⟩ := hr
    exact ⟨nM, hleM, run_liftP M ei eo _ nM _ _ hnM⟩
  have h5 := rIn_single (step3 M ei eo none (A.reverse ++ []) (haltList M outM).stk)
  rw [haltList_stk_k₁] at h5
  have hS : ∀ k, k ≠ M.k₁ → (haltList M outM).stk k = [] := by
    intro k hk; simp [haltList, hk]
  have h6 : ∃ n ≤ (A.reverse ++ []).length + 1, (flip bind N.step)^[n]
      (some (cfgP M 4 none [] (A.reverse ++ []) []
        (Function.update (haltList M outM).stk M.k₁ (eo false :: outM)))) =
      some (haltList N (show List (M.Γ M.k₁) from
        ((A.reverse ++ []).reverse.flatMap fun x => [eo true, eo x]) ++ eo false :: outM)) := by
    obtain ⟨n6, hn6, he6⟩ := out_runP M ei eo (A.reverse ++ [])
      (Function.update (haltList M outM).stk M.k₁ (eo false :: outM)) none
    rw [Function.update_idem, Function.update_self] at he6
    exact ⟨n6, hn6, he6.trans (congrArg some (haltList_pmr M ei eo _ hS _))⟩
  have hall := rIn_trans (rIn_trans (rIn_trans (rIn_trans (rIn_trans h1 h2) h3) h4) h5) h6
  rw [← initList_pmr] at hall
  have hout : (((A.reverse ++ []).reverse.flatMap fun x => [eo true, eo x]) ++ eo false :: outM) =
      List.map H.outputAlphabet.invFun
        ((BitstringEncoding.toEncoding (α := α × γ)).encode (p.1, g p.2)) := by
    show _ = List.map H.outputAlphabet.invFun (delimit A ++ _)
    rw [delimit_eq_flatMap]
    simp [houtM, eo, List.map_flatMap]
    rfl
  rw [hout] at hall
  have hn : ((BitstringEncoding.toEncoding (α := α × β)).encode p).length =
      2 * A.length + 1 + B.length := by
    rw [henc]; simp [length_delimit]
  have hb : A.length + 1 + (B.length + 1) + ((B.reverse ++ []).length + 1) +
      H.time.eval B.length + 1 + ((A.reverse ++ []).length + 1) ≤
      T.eval ((BitstringEncoding.toEncoding (α := α × β)).encode p).length := by
    rw [hn]
    have hTm := eval_mono H.time (show B.length ≤ 2 * A.length + 1 + B.length by omega)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat, List.length_append, List.length_reverse, List.length_nil]
    omega
  have key : ∀ l : List Bool, l = delimit A ++ B →
      TM2OutputsInTime N l (some (List.map H.outputAlphabet.invFun
        ((BitstringEncoding.toEncoding (α := α × γ)).encode (p.1, g p.2))))
        (T.eval ((BitstringEncoding.toEncoding (α := α × β)).encode p).length) := by
    rintro l rfl
    exact Classical.choice (by
      obtain ⟨n, hle, he⟩ := rIn_mono hall hb
      exact ⟨⟨⟨n, he⟩, hle⟩⟩)
  exact key _ hin


/- ### Counted iteration -/

section IT

variable (M : FinTM2) (ei : Bool → M.Γ M.k₀) (eo : M.Γ M.k₁ → Bool)

/-- 0: parse the value into the stash (reversed). -/
def it0 : TM2.Stmt (pmrΓ M) (pmrΛ M) (pmrσ M) := pmr0 M

/-- 1: consume one unary tick (three bits), or finish. -/
def it1 : TM2.Stmt (pmrΓ M) (pmrΛ M) (pmrσ M) :=
  .pop (Sum.inl 0) (fun v o => (v.1, o)) <|
    .branch (fun v => v.2.isSome)
      (.pop (Sum.inl 0) (fun v o => (v.1, o)) <| .pop (Sum.inl 0) (fun v o => (v.1, o)) <|
        .goto fun _ => Sum.inr 2)
      (.goto fun _ => Sum.inr 4)

/-- 2: load the stash into `M`'s input, then run `M`. -/
def it2 : TM2.Stmt (pmrΓ M) (pmrΛ M) (pmrσ M) :=
  .pop (Sum.inl 1) (fun v o => (v.1, o)) <|
    .branch (fun v => v.2.isSome)
      (.push (Sum.inr M.k₀) (fun v => ei (v.2.getD false)) <| .goto fun _ => Sum.inr 2)
      (.goto fun _ => Sum.inl M.main)

/-- 3: unload `M`'s output into the stash (reversed), then the next tick. -/
def it3 : TM2.Stmt (pmrΓ M) (pmrΛ M) (pmrσ M) :=
  .pop (Sum.inr M.k₁) (fun v o => (v.1, o.map eo)) <|
    .branch (fun v => v.2.isSome)
      (.push (Sum.inl 1) (fun v => v.2.getD false) <| .goto fun _ => Sum.inr 3)
      (.goto fun _ => Sum.inr 1)

/-- 4: move the stash to the output stack. -/
def it4 : TM2.Stmt (pmrΓ M) (pmrΛ M) (pmrσ M) :=
  .pop (Sum.inl 1) (fun v o => (v.1, o)) <|
    .branch (fun v => v.2.isSome)
      (.push (Sum.inl 2) (fun v => v.2.getD false) <| .goto fun _ => Sum.inr 4)
      .halt

def itProg : pmrΛ M → TM2.Stmt (pmrΓ M) (pmrΛ M) (pmrσ M)
  | .inl l => liftP M (M.m l)
  | .inr p =>
    if p = 0 then it0 M else if p = 1 then it1 M else if p = 2 then it2 M ei
    else if p = 3 then it3 M eo else it4 M

def itTM : FinTM2 :=
  letI := M.kFin; letI := M.ΛFin; letI := M.σFin
  { K := Fin 3 ⊕ M.K
    k₀ := Sum.inl 0
    k₁ := Sum.inl 2
    Γ := pmrΓ M
    Λ := pmrΛ M
    main := Sum.inr 0
    σ := pmrσ M
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := itProg M ei eo }

def cfgI (p : Fin 5) (o : Option Bool) (i st out : List Bool) (S : ∀ k, List (M.Γ k)) :
    TM2.Cfg (pmrΓ M) (pmrΛ M) (pmrσ M) :=
  ⟨some (Sum.inr p), (M.initialState, o), pmrStk M i st out S⟩

def liftCfgI (i : List Bool) (c : TM2.Cfg M.Γ M.Λ M.σ) : TM2.Cfg (pmrΓ M) (pmrΛ M) (pmrσ M) :=
  ⟨c.l.elim (some (Sum.inr 3)) (fun l => some (Sum.inl l)), (c.var, none), pmrStk M i [] [] c.stk⟩

lemma stepAux_liftI (i : List Bool) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (liftP M q) (v, none) (pmrStk M i [] [] S) = liftCfgI M i (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [liftP, TM2.stepAux]
    rw [show pmrStk M i [] [] S (Sum.inr k) = S k from rfl, pmrStk_update_inr]
    exact ih _ _
  | peek k f q ih => simp only [liftP, TM2.stepAux]; exact ih _ _
  | pop k f q ih =>
    simp only [liftP, TM2.stepAux]
    rw [show pmrStk M i [] [] S (Sum.inr k) = S k from rfl, pmrStk_update_inr]
    exact ih _ _
  | load a q ih => simp only [liftP, TM2.stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [liftP, TM2.stepAux, ih₁, ih₂]
    cases f v <;> rfl
  | goto f => rfl
  | halt => rfl

lemma step_liftI (i : List Bool) (l : M.Λ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    (itTM M ei eo).step (liftCfgI M i ⟨some l, v, S⟩) =
      some (liftCfgI M i (TM2.stepAux (M.m l) v S)) := by
  show some (TM2.stepAux (liftP M (M.m l)) (v, none) (pmrStk M i [] [] S)) = _
  rw [stepAux_liftI]

lemma run_liftI (i : List Bool) (n : ℕ) : ∀ (c d : TM2.Cfg M.Γ M.Λ M.σ),
    (flip bind M.step)^[n] (some c) = some d →
      (flip bind (itTM M ei eo).step)^[n] (some (liftCfgI M i c)) = some (liftCfgI M i d) := by
  induction n with
  | zero => intro c d h; cases Option.some.inj h; rfl
  | succ n ih =>
    intro c d h
    rw [Function.iterate_succ_apply] at h ⊢
    change (flip bind M.step)^[n] (M.step c) = some d at h
    rcases c with ⟨_ | l, v, S⟩
    · change (flip bind M.step)^[n] none = some d at h
      rw [iterate_none] at h; exact absurd h (by simp)
    · change (flip bind M.step)^[n] (some (TM2.stepAux (M.m l) v S)) = some d at h
      change (flip bind (itTM M ei eo).step)^[n]
        ((itTM M ei eo).step (liftCfgI M i ⟨some l, v, S⟩)) = _
      rw [step_liftI]
      exact ih _ _ h

lemma it0_true (o : Option Bool) (x : Bool) (rest st out : List Bool) (S : ∀ k, List (M.Γ k)) :
    (itTM M ei eo).step (cfgI M 0 o (true :: x :: rest) st out S) =
      some (cfgI M 0 (some x) rest (x :: st) out S) := by
  change some (TM2.stepAux (pmr0 M) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [pmr0, TM2.stepAux, pmrStk, pmrStk_update_0, pmrStk_update_1, cfgI]

lemma it0_false (o : Option Bool) (rest st out : List Bool) (S : ∀ k, List (M.Γ k)) :
    (itTM M ei eo).step (cfgI M 0 o (false :: rest) st out S) =
      some (cfgI M 1 (some false) rest st out S) := by
  change some (TM2.stepAux (pmr0 M) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [pmr0, TM2.stepAux, pmrStk, pmrStk_update_0, cfgI]

lemma it1_tick (o : Option Bool) (b : Bool) (rest st : List Bool) (S : ∀ k, List (M.Γ k)) :
    (itTM M ei eo).step (cfgI M 1 o (true :: b :: false :: rest) st [] S) =
      some (cfgI M 2 (some false) rest st [] S) := by
  change some (TM2.stepAux (it1 M) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [it1, TM2.stepAux, pmrStk, pmrStk_update_0, cfgI]

lemma it1_nil (o : Option Bool) (st : List Bool) (S : ∀ k, List (M.Γ k)) :
    (itTM M ei eo).step (cfgI M 1 o [] st [] S) = some (cfgI M 4 none [] st [] S) := by
  change some (TM2.stepAux (it1 M) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [it1, TM2.stepAux, pmrStk, pmrStk_update_0, cfgI]

lemma it2_cons (o : Option Bool) (x : Bool) (i st : List Bool) (S : ∀ k, List (M.Γ k)) :
    (itTM M ei eo).step (cfgI M 2 o i (x :: st) [] S) =
      some (cfgI M 2 (some x) i st [] (Function.update S M.k₀ (ei x :: S M.k₀))) := by
  change some (TM2.stepAux (it2 M ei) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [it2, TM2.stepAux, pmrStk, pmrStk_update_1, pmrStk_update_inr, cfgI]

lemma it2_nil (o : Option Bool) (i : List Bool) (S : ∀ k, List (M.Γ k)) :
    (itTM M ei eo).step (cfgI M 2 o i [] [] S) =
      some (liftCfgI M i ⟨some M.main, M.initialState, S⟩) := by
  change some (TM2.stepAux (it2 M ei) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [it2, TM2.stepAux, pmrStk, pmrStk_update_1, liftCfgI]

lemma it3_cons (o : Option Bool) (i st : List Bool) (S : ∀ k, List (M.Γ k))
    (x : M.Γ M.k₁) (t : List (M.Γ M.k₁)) (h : S M.k₁ = x :: t) :
    (itTM M ei eo).step (cfgI M 3 o i st [] S) =
      some (cfgI M 3 (some (eo x)) i (eo x :: st) [] (Function.update S M.k₁ t)) := by
  change some (TM2.stepAux (it3 M eo) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp only [it3, TM2.stepAux]
  rw [show pmrStk M i st [] S (Sum.inr M.k₁) = S M.k₁ from rfl, h, pmrStk_update_inr]
  simp [pmrStk, pmrStk_update_1, cfgI]

lemma it3_nil (o : Option Bool) (i st : List Bool) (S : ∀ k, List (M.Γ k)) (h : S M.k₁ = []) :
    (itTM M ei eo).step (cfgI M 3 o i st [] S) = some (cfgI M 1 none i st [] S) := by
  change some (TM2.stepAux (it3 M eo) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp only [it3, TM2.stepAux]
  rw [show pmrStk M i st [] S (Sum.inr M.k₁) = S M.k₁ from rfl, h, pmrStk_update_inr]
  simp only [List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, cond_false]
  rw [← h, Function.update_eq_self]
  rfl

lemma it4_cons (o : Option Bool) (x : Bool) (st out : List Bool) (S : ∀ k, List (M.Γ k)) :
    (itTM M ei eo).step (cfgI M 4 o [] (x :: st) out S) =
      some (cfgI M 4 (some x) [] st (x :: out) S) := by
  change some (TM2.stepAux (it4 M) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [it4, TM2.stepAux, pmrStk, pmrStk_update_1, pmrStk_update_2, cfgI]

lemma it4_nil (o : Option Bool) (out : List Bool) (S : ∀ k, List (M.Γ k)) :
    (itTM M ei eo).step (cfgI M 4 o [] [] out S) =
      some ⟨none, (M.initialState, none), pmrStk M [] [] out S⟩ := by
  change some (TM2.stepAux (it4 M) (M.initialState, o) (pmrStk M _ _ _ _)) = _
  simp [it4, TM2.stepAux, pmrStk, pmrStk_update_1]
  rfl

end IT


section ITRuns

variable (M : FinTM2) (ei : Bool → M.Γ M.k₀) (eo : M.Γ M.k₁ → Bool)

lemma parse_runI (S : ∀ k, List (M.Γ k)) (rest : List Bool) (A : List Bool) :
    ∀ (st : List Bool) (o : Option Bool),
      ∃ n ≤ A.length + 1, (flip bind (itTM M ei eo).step)^[n]
        (some (cfgI M 0 o (delimit A ++ rest) st [] S)) =
        some (cfgI M 1 (some false) rest (A.reverse ++ st) [] S) := by
  induction A with
  | nil => intro st o; exact rIn_single (it0_false M ei eo o rest st [] S)
  | cons x A ih =>
    intro st o
    obtain ⟨n, hn, he⟩ := rIn_trans
      (rIn_single (it0_true M ei eo o x (delimit A ++ rest) st [] S)) (ih (x :: st) (some x))
    refine ⟨n, by simp only [List.length_cons]; omega, he.trans ?_⟩
    simp

lemma load_runI (i : List Bool) (st : List Bool) :
    ∀ (S : ∀ k, List (M.Γ k)) (o : Option Bool),
      ∃ n ≤ st.length + 1, (flip bind (itTM M ei eo).step)^[n]
        (some (cfgI M 2 o i st [] S)) =
        some (liftCfgI M i ⟨some M.main, M.initialState,
          Function.update S M.k₀ ((st.map ei).reverse ++ S M.k₀)⟩) := by
  induction st with
  | nil =>
    intro S o
    simp only [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
    exact rIn_single (it2_nil M ei eo o i S)
  | cons x st ih =>
    intro S o
    obtain ⟨n, hn, he⟩ := rIn_trans (rIn_single (it2_cons M ei eo o x i st S))
      (ih (Function.update S M.k₀ (ei x :: S M.k₀)) (some x))
    refine ⟨n, by simp only [List.length_cons]; omega, he.trans ?_⟩
    congr 3
    rw [Function.update_idem, Function.update_self]
    simp

lemma unload_runI (i : List Bool) (out : List (M.Γ M.k₁)) :
    ∀ (o : Option Bool) (S : ∀ k, List (M.Γ k)) (st : List Bool), S M.k₁ = out →
      ∃ n ≤ out.length + 1, (flip bind (itTM M ei eo).step)^[n]
        (some (cfgI M 3 o i st [] S)) =
        some (cfgI M 1 none i ((out.map eo).reverse ++ st) [] (Function.update S M.k₁ [])) := by
  induction out with
  | nil =>
    intro o S st h
    have h' : Function.update S M.k₁ [] = S := by rw [← h, Function.update_eq_self]
    rw [h']
    exact rIn_single (it3_nil M ei eo o i st S h)
  | cons x t ih =>
    intro o S st h
    obtain ⟨n, hn, he⟩ := rIn_trans (rIn_single (it3_cons M ei eo o i st S x t h))
      (ih (some (eo x)) (Function.update S M.k₁ t) (eo x :: st) (by simp))
    refine ⟨n, by simp only [List.length_cons]; omega, he.trans ?_⟩
    congr 2
    · simp
    · exact Function.update_idem _ _ _

lemma finish_runI (S : ∀ k, List (M.Γ k)) (st : List Bool) :
    ∀ (o : Option Bool) (out : List Bool),
      ∃ n ≤ st.length + 1, (flip bind (itTM M ei eo).step)^[n]
        (some (cfgI M 4 o [] st out S)) =
        some ⟨none, (M.initialState, none), pmrStk M [] [] (st.reverse ++ out) S⟩ := by
  induction st with
  | nil => intro o out; exact rIn_single (it4_nil M ei eo o out S)
  | cons x st ih =>
    intro o out
    obtain ⟨n, hn, he⟩ := rIn_trans (rIn_single (it4_cons M ei eo o x st out S))
      (ih (some x) (x :: out))
    refine ⟨n, by simp only [List.length_cons]; omega, he.trans ?_⟩
    congr 3
    simp

lemma initList_it (l : List Bool) :
    initList (itTM M ei eo) l = cfgI M 0 none l [] [] (fun _ => []) := by
  simp only [initList, cfgI]
  congr 1
  funext k
  rcases k with j | k
  · fin_cases j <;> simp [pmrStk, itTM] <;> rfl
  · simp [pmrStk, itTM]

lemma haltList_it (out : List Bool) :
    (⟨none, (M.initialState, none), pmrStk M [] [] out (fun _ => [])⟩ :
      TM2.Cfg (pmrΓ M) (pmrΛ M) (pmrσ M)) = haltList (itTM M ei eo) out := by
  simp only [haltList]
  congr 1
  funext k
  rcases k with j | k
  · fin_cases j <;> simp [pmrStk, itTM] <;> rfl
  · simp [pmrStk, itTM]

end ITRuns

/-- The encoding of a unary counter. -/
lemma bitEncode_list_bool_cons (b : Bool) (u : List Bool) :
    bitEncode (b :: u) = true :: b :: false :: bitEncode u := rfl

theorem isPolyTime_iterate {α : Type} [BitstringEncoding α] (s : α → α) (hs : IsPolyTime s)
    (c : ℕ) (hc : ∀ a, (bitEncode (s a)).length ≤ (bitEncode a).length + c) :
    IsPolyTime (fun p : α × List Bool => s^[p.2.length] p.1) := by
  classical
  obtain ⟨H⟩ := hs
  let M := H.tm
  let ei : Bool → M.Γ M.k₀ := H.inputAlphabet.symm
  let eo : M.Γ M.k₁ → Bool := H.outputAlphabet
  let N := itTM M ei eo
  have hrunM : ∀ a : α, TM2OutputsInTime M (List.map H.inputAlphabet.invFun (bitEncode a))
      (some (List.map H.outputAlphabet.invFun (bitEncode (s a))))
      (H.time.eval (bitEncode a).length) := fun a => H.outputsFun a
  -- the main loop
  have loop : ∀ (u : List Bool) (a : α) (Lb : ℕ) (o : Option Bool),
      (bitEncode a).length + c * u.length ≤ Lb →
      ∃ n ≤ u.length * (2 * Lb + 3 + H.time.eval Lb) + (Lb + 2),
        (flip bind N.step)^[n] (some (cfgI M 1 o (bitEncode u) (bitEncode a).reverse [] fun _ => [])) =
        some (haltList N (bitEncode (s^[u.length] a))) := by
    intro u
    induction u with
    | nil =>
      intro a Lb o hL
      have h1 := rIn_single (it1_nil M ei eo o (bitEncode a).reverse (fun _ => []))
      have h2 := finish_runI M ei eo (fun _ => []) (bitEncode a).reverse none []
      obtain ⟨n, hn, he⟩ := rIn_trans h1 h2
      refine ⟨n, ?_, he.trans ?_⟩
      · simp only [List.length_nil, Nat.mul_zero, Nat.zero_mul, Nat.zero_add,
          List.length_reverse] at hn hL ⊢
        omega
      · refine Eq.trans ?_ (congrArg some (haltList_it M ei eo (bitEncode a)))
        congr 3
        simp
    | cons b u ih =>
      intro a Lb o hL
      have hcu : c * (b :: u).length = c * u.length + c := by simp [Nat.mul_succ]
      have hsa : (bitEncode (s a)).length + c * u.length ≤ Lb := by
        have := hc a; omega
      have h1 := rIn_single (it1_tick M ei eo o b (bitEncode u) (bitEncode a).reverse
        (fun _ => []))
      have h2 := load_runI M ei eo (bitEncode u) (bitEncode a).reverse (fun _ => []) (some false)
      have hmid : Function.update (fun _ => []) M.k₀
          (((bitEncode a).reverse.map ei).reverse ++ ([] : List (M.Γ M.k₀))) =
            Function.update (fun _ => []) M.k₀ (List.map H.inputAlphabet.invFun (bitEncode a)) := by
        congr 1; simp [ei, List.map_reverse]
      rw [hmid, initList_eq_update] at h2
      have h3 : ∃ n ≤ H.time.eval (bitEncode a).length,
          (flip bind N.step)^[n] (some (liftCfgI M (bitEncode u)
            (initList M (List.map H.inputAlphabet.invFun (bitEncode a))))) =
          some (cfgI M 3 none (bitEncode u) [] []
            (haltList M (List.map H.outputAlphabet.invFun (bitEncode (s a)))).stk) := by
        obtain ⟨⟨nM, hnM⟩, hleM⟩ := hrunM a
        exact ⟨nM, hleM, run_liftI M ei eo _ nM _ _ hnM⟩
      have h4 := unload_runI M ei eo (bitEncode u)
        (List.map H.outputAlphabet.invFun (bitEncode (s a))) none _ [] (haltList_stk_k₁ _ _)
      rw [haltList_update_k₁] at h4
      have hout : ((List.map H.outputAlphabet.invFun (bitEncode (s a))).map eo).reverse ++ [] =
          (bitEncode (s a)).reverse := by
        simp [eo, List.map_map]
      rw [hout] at h4
      have h5 := ih (s a) Lb none hsa
      rw [← Function.iterate_succ_apply] at h5
      have hall := rIn_trans (rIn_trans (rIn_trans (rIn_trans h1 h2) h3) h4) h5
      refine rIn_mono hall ?_
      have hTa : H.time.eval (bitEncode a).length ≤ H.time.eval Lb := eval_mono _ (by omega)
      have hsa' : (bitEncode (s a)).length ≤ Lb := by omega
      have ha' : (bitEncode a).length ≤ Lb := by omega
      have e1 : (bitEncode a).reverse.length = (bitEncode a).length := List.length_reverse
      have e2 : (List.map H.outputAlphabet.invFun (bitEncode (s a))).length =
          (bitEncode (s a)).length := List.length_map _
      have e4 : (u.length + 1) * (2 * Lb + 3 + H.time.eval Lb) =
          u.length * (2 * Lb + 3 + H.time.eval Lb) + (2 * Lb + 3 + H.time.eval Lb) := Nat.succ_mul _ _
      rw [List.length_cons, e4]
      omega
  refine ⟨⟨⟨N, Equiv.refl Bool, Equiv.refl Bool⟩, ?_, fun p => ?_⟩⟩
  · exact Polynomial.X + 1 + Polynomial.X * (2 * (Polynomial.C (1 + c) * Polynomial.X) + 3 +
      H.time.comp (Polynomial.C (1 + c) * Polynomial.X)) +
      Polynomial.C (1 + c) * Polynomial.X + 2
  · set A := bitEncode p.1 with hA
    set U := bitEncode p.2 with hU
    have henc : (BitstringEncoding.toEncoding (α := α × List Bool)).encode p = delimit A ++ U := rfl
    have hin : List.map ((Equiv.refl Bool : N.Γ N.k₀ ≃ Bool).invFun)
        ((BitstringEncoding.toEncoding (α := α × List Bool)).encode p) = delimit A ++ U := by
      rw [henc]; exact List.map_id _
    have hUlen : p.2.length ≤ U.length := by
      rw [hU]
      clear hU hin henc
      induction p.2 with
      | nil => simp
      | cons b u ih => rw [bitEncode_list_bool_cons]; simp only [List.length_cons]; omega
    set n := ((BitstringEncoding.toEncoding (α := α × List Bool)).encode p).length with hn
    have hn' : n = 2 * A.length + 1 + U.length := by rw [hn, henc]; simp [length_delimit]
    set Lb := (1 + c) * n with hLb
    have hL : A.length + c * p.2.length ≤ Lb := by
      rw [hLb, Nat.add_mul, Nat.one_mul]
      have : c * p.2.length ≤ c * n := Nat.mul_le_mul_left _ (by omega)
      omega
    have h1 := parse_runI M ei eo (fun _ => []) U A [] none
    have h2 := loop p.2 p.1 Lb (some false) hL
    simp only [List.append_nil] at h1
    have hall := rIn_trans h1 h2
    rw [← initList_it] at hall
    have hb : A.length + 1 + (p.2.length * (2 * Lb + 3 + H.time.eval Lb) + (Lb + 2)) ≤
        (Polynomial.X + 1 + Polynomial.X * (2 * (Polynomial.C (1 + c) * Polynomial.X) + 3 +
          H.time.comp (Polynomial.C (1 + c) * Polynomial.X)) +
          Polynomial.C (1 + c) * Polynomial.X + 2).eval n := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_comp]
      rw [← hLb]
      have hk : p.2.length * (2 * Lb + 3 + H.time.eval Lb) ≤ n * (2 * Lb + 3 + H.time.eval Lb) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have key : ∀ l : List Bool, l = delimit A ++ U →
        TM2OutputsInTime N l (some (List.map (Equiv.refl Bool).invFun
          ((BitstringEncoding.toEncoding (α := α)).encode (s^[p.2.length] p.1))))
          ((Polynomial.X + 1 + Polynomial.X * (2 * (Polynomial.C (1 + c) * Polynomial.X) + 3 +
            H.time.comp (Polynomial.C (1 + c) * Polynomial.X)) +
            Polynomial.C (1 + c) * Polynomial.X + 2).eval n) := by
      rintro l rfl
      exact Classical.choice (by
        obtain ⟨m, hle, he⟩ := rIn_mono hall hb
        refine ⟨⟨⟨m, he.trans ?_⟩, hle⟩⟩
        rw [Option.map_some]
        congr 2
        exact (List.map_id _).symm)
    exact key _ hin

end OMA.PolyTimeLib

/- Proof of `isPolyTime_const` for the polynomial-time closure library. -/

namespace OMA.PolyTimeLib

open ComplexityTheory BitstringEncoding

variable {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]

open Turing OMA.R_ComplexityTheory_P_eq_BPP_R1 in
theorem isPolyTime_const (b : β) : IsPolyTime (fun _ : α => b) := by
  let pushRev : List Bool →
      TM2.Stmt (fun _ : Unit => Bool) Unit (Option Bool) →
      TM2.Stmt (fun _ : Unit => Bool) Unit (Option Bool) :=
    fun l q => l.foldr (fun x acc => .push () (fun _ => x) acc) q
  let target : List Bool := bitEncode b
  let prog : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit (Option Bool) := fun _ =>
    .pop () (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.load (fun _ => none) <| .goto fun _ => ())
        (pushRev target.reverse (.load (fun _ => none) .halt))
  let N : FinTM2 :=
    { K := Unit
      k₀ := ()
      k₁ := ()
      Γ := fun _ => Bool
      Λ := Unit
      main := ()
      σ := Option Bool
      initialState := none
      m := prog }
  let cfg (l : Option Unit) (s : List Bool) : N.Cfg := ⟨l, none, fun _ => s⟩
  have stepAux_pushRev (l : List Bool)
      (q : TM2.Stmt (fun _ : Unit => Bool) Unit (Option Bool))
      (v : Option Bool) (st : List Bool) :
      TM2.stepAux (pushRev l q) v (fun _ => st) =
        TM2.stepAux q v (fun _ => l.reverse ++ st) := by
    induction l generalizing st with
    | nil => rfl
    | cons x xs ih =>
      show TM2.stepAux (.push () (fun _ => x) (pushRev xs q)) v (fun _ => st) = _
      simp only [TM2.stepAux]
      have hupd : Function.update (fun _ : Unit => st) () (x :: st) = (fun _ : Unit => x :: st) := by
        funext k; cases k; rfl
      rw [hupd, ih (x :: st)]
      simp [List.reverse_cons, List.append_assoc]
  have step_cons (c : Bool) (rest : List Bool) :
      N.step (cfg (some ()) (c :: rest)) = some (cfg (some ()) rest) := by
    show some (TM2.stepAux (prog ()) none (fun _ => c :: rest)) = _
    dsimp only [prog]
    simp only [TM2.stepAux, List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true]
    rfl
  have step_nil :
      N.step (cfg (some ()) []) = some (cfg none target) := by
    show some (TM2.stepAux (prog ()) none (fun _ => [])) = _
    dsimp only [prog]
    simp only [TM2.stepAux, List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
    have hupd : Function.update (fun _ : Unit => ([] : List Bool)) () [] = (fun _ : Unit => []) := by
      funext k; cases k; rfl
    rw [hupd, stepAux_pushRev]
    simp only [TM2.stepAux, List.reverse_reverse, List.append_nil, cfg]
    rfl
  have run_all (s : List Bool) :
      ∃ n ≤ s.length + 1, (flip bind N.step)^[n] (some (cfg (some ()) s)) =
        some (cfg none target) := by
    induction s with
    | nil => exact rIn_single step_nil
    | cons c s ih =>
      have h := rIn_trans (rIn_single (step_cons c s)) ih
      simpa [Nat.add_comm] using h
  have init_eq (l : List Bool) : initList N l = cfg (some ()) l := by
    simp only [initList, cfg, N]
    rfl
  have halt_eq (l : List Bool) : haltList N l = cfg none l := by
    simp only [haltList, cfg, N]
    rfl
  refine ⟨{ tm := N
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := Polynomial.X + 1
            outputsFun := fun a => ?_ }⟩
  set s := bitEncode a
  have hin : List.map (Equiv.refl Bool).invFun ((toEncoding (α := α)).encode a) = s := by
    change List.map id s = s; simp
  have hout : List.map (Equiv.refl Bool).invFun ((toEncoding (α := β)).encode b) = target := by
    change List.map id target = target; simp
  have hb : s.length + 1 ≤
      (Polynomial.X + 1 : Polynomial ℕ).eval ((toEncoding (α := α)).encode a).length := by
    change s.length + 1 ≤ (Polynomial.X + 1 : Polynomial ℕ).eval s.length
    simp
  rw [hin, hout]
  exact Classical.choice (by
    obtain ⟨n, hle, he⟩ := rIn_mono (run_all s) hb
    rw [← init_eq, ← halt_eq] at he
    exact ⟨⟨⟨n, he⟩, hle⟩⟩)

end OMA.PolyTimeLib

/- Proof of `isPolyTime_snd` for the polynomial-time closure library. -/

namespace OMA.PolyTimeLib

open ComplexityTheory BitstringEncoding

variable {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]

open Turing OMA.R_ComplexityTheory_P_eq_BPP_R1 in
theorem isPolyTime_snd : IsPolyTime (Prod.snd : α × β → β) := by
  let prog : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit (Option Bool) := fun _ =>
    .pop () (fun _ o => o) <|
      .branch (fun v => v == some true)
        (.pop () (fun _ _ => none) <| .goto fun _ => ())
        (.load (fun _ => none) .halt)
  let N : FinTM2 :=
    { K := Unit
      k₀ := ()
      k₁ := ()
      Γ := fun _ => Bool
      Λ := Unit
      main := ()
      σ := Option Bool
      initialState := none
      m := prog }
  let cfg (l : Option Unit) (s : List Bool) : N.Cfg := ⟨l, none, fun _ => s⟩
  have step_true (c : Bool) (rest : List Bool) :
      N.step (cfg (some ()) (true :: c :: rest)) = some (cfg (some ()) rest) := by
    show some (TM2.stepAux (prog ()) none (fun _ => true :: c :: rest)) = _
    dsimp only [prog]
    simp only [TM2.stepAux, List.head?_cons, List.tail_cons, Function.update_apply, beq_self_eq_true,
      Bool.cond_true]
    rfl
  have step_false (rest : List Bool) :
      N.step (cfg (some ()) (false :: rest)) = some (cfg none rest) := by
    show some (TM2.stepAux (prog ()) none (fun _ => false :: rest)) = _
    dsimp only [prog]
    simp only [TM2.stepAux, List.head?_cons, List.tail_cons, Function.update_apply]
    rfl
  have run_delimit (s t : List Bool) :
      ∃ n ≤ s.length + 1, (flip bind N.step)^[n] (some (cfg (some ()) (delimit s ++ t))) =
        some (cfg none t) := by
    induction s with
    | nil => exact rIn_single (step_false t)
    | cons c s ih =>
      have h1 := rIn_single (step_true c (delimit s ++ t))
      have h := rIn_trans h1 ih
      simpa [delimit, Nat.add_comm] using h
  have init_eq (l : List Bool) : initList N l = cfg (some ()) l := by
    simp only [initList, cfg, N]
    rfl
  have halt_eq (l : List Bool) : haltList N l = cfg none l := by
    simp only [haltList, cfg, N]
    rfl
  refine ⟨{ tm := N
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := Polynomial.X
            outputsFun := fun p => ?_ }⟩
  set s := bitEncode p.1
  set t := bitEncode p.2
  have hin : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := α × β)).encode p) = delimit s ++ t := by
    change List.map id (delimit s ++ t) = _
    simp
  have hout : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := β)).encode p.2) = t := by
    change List.map id t = t
    simp
  have hlen : ((toEncoding (α := α × β)).encode p).length = 2 * s.length + 1 + t.length := by
    change (delimit s ++ t).length = _
    simp [length_delimit]
  have hb : s.length + 1 ≤
      (Polynomial.X : Polynomial ℕ).eval ((toEncoding (α := α × β)).encode p).length := by
    rw [hlen, Polynomial.eval_X]
    omega
  rw [hin, hout]
  exact Classical.choice (by
    obtain ⟨n, hle, he⟩ := rIn_mono (run_delimit s t) hb
    rw [← init_eq, ← halt_eq] at he
    exact ⟨⟨⟨n, he⟩, hle⟩⟩)

end OMA.PolyTimeLib

/- Proof of `isPolyTime_dup` for the polynomial-time closure library. -/

namespace OMA.PolyTimeLib

open ComplexityTheory BitstringEncoding

variable {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]

open Turing OMA.R_ComplexityTheory_P_eq_BPP_R1 in
theorem isPolyTime_dup : IsPolyTime (fun a : α => (a, a)) := by
  let prog : Fin 3 → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool) := fun q =>
    if q = 0 then
      .pop 0 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push 1 (fun v => v.getD false) <|
            .push 2 (fun v => v.getD false) <|
            .load (fun _ => none) <| .goto fun _ => 0)
          (.load (fun _ => none) <| .goto fun _ => 1)
    else if q = 1 then
      .pop 1 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push 0 (fun v => v.getD false) <|
            .load (fun _ => none) <| .goto fun _ => 1)
          (.push 0 (fun _ => false) <|
            .load (fun _ => none) <| .goto fun _ => 2)
    else
      .pop 2 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push 0 (fun v => v.getD false) <|
            .push 0 (fun _ => true) <|
            .load (fun _ => none) <| .goto fun _ => 2)
          (.load (fun _ => none) .halt)
  let N : FinTM2 :=
    { K := Fin 3
      k₀ := 0
      k₁ := 0
      Γ := fun _ => Bool
      Λ := Fin 3
      main := 0
      σ := Option Bool
      initialState := none
      m := prog }
  let mk (s0 s1 s2 : List Bool) : Fin 3 → List Bool :=
    fun k => if k = 0 then s0 else if k = 1 then s1 else s2
  have upd0 (s0 s1 s2 s0' : List Bool) :
      Function.update (mk s0 s1 s2) 0 s0' = mk s0' s1 s2 := by
    funext k; fin_cases k <;> rfl
  have upd1 (s0 s1 s2 s1' : List Bool) :
      Function.update (mk s0 s1 s2) 1 s1' = mk s0 s1' s2 := by
    funext k; fin_cases k <;> rfl
  have upd2 (s0 s1 s2 s2' : List Bool) :
      Function.update (mk s0 s1 s2) 2 s2' = mk s0 s1 s2' := by
    funext k; fin_cases k <;> rfl
  let cfg (l : Option (Fin 3)) (s0 s1 s2 : List Bool) : N.Cfg := ⟨l, none, mk s0 s1 s2⟩
  have step0_cons (c : Bool) (rest s1 s2 : List Bool) :
      N.step (cfg (some 0) (c :: rest) s1 s2) =
        some (cfg (some 0) rest (c :: s1) (c :: s2)) := by
    show some (TM2.stepAux (prog 0) none (mk (c :: rest) s1 s2)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, upd2, cfg]; rfl
  have step0_nil (s1 s2 : List Bool) :
      N.step (cfg (some 0) [] s1 s2) = some (cfg (some 1) [] s1 s2) := by
    show some (TM2.stepAux (prog 0) none (mk [] s1 s2)) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step1_cons (s0 : List Bool) (c : Bool) (s1 s2 : List Bool) :
      N.step (cfg (some 1) s0 (c :: s1) s2) = some (cfg (some 1) (c :: s0) s1 s2) := by
    show some (TM2.stepAux (prog 1) none (mk s0 (c :: s1) s2)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step1_nil (s0 s2 : List Bool) :
      N.step (cfg (some 1) s0 [] s2) = some (cfg (some 2) (false :: s0) [] s2) := by
    show some (TM2.stepAux (prog 1) none (mk s0 [] s2)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step2_cons (s0 s1 : List Bool) (c : Bool) (s2 : List Bool) :
      N.step (cfg (some 2) s0 s1 (c :: s2)) =
        some (cfg (some 2) (true :: c :: s0) s1 s2) := by
    show some (TM2.stepAux (prog 2) none (mk s0 s1 (c :: s2))) = _
    simp [prog, TM2.stepAux, mk, upd0, upd2, cfg]; rfl
  have step2_nil (s0 s1 : List Bool) :
      N.step (cfg (some 2) s0 s1 []) = some (cfg none s0 s1 []) := by
    show some (TM2.stepAux (prog 2) none (mk s0 s1 [])) = _
    simp [prog, TM2.stepAux, mk, upd2, cfg]; rfl
  have run0 (a s1 s2 : List Bool) :
      ∃ n ≤ a.length + 1, (flip bind N.step)^[n] (some (cfg (some 0) a s1 s2)) =
        some (cfg (some 1) [] (a.reverse ++ s1) (a.reverse ++ s2)) := by
    induction a generalizing s1 s2 with
    | nil => exact rIn_single (step0_nil s1 s2)
    | cons c a ih =>
      have h := rIn_trans (rIn_single (step0_cons c a s1 s2)) (ih (c :: s1) (c :: s2))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h
  have run1 (s0 r s2 : List Bool) :
      ∃ n ≤ r.length + 1, (flip bind N.step)^[n] (some (cfg (some 1) s0 r s2)) =
        some (cfg (some 2) (false :: (r.reverse ++ s0)) [] s2) := by
    induction r generalizing s0 with
    | nil => exact rIn_single (step1_nil s0 s2)
    | cons c r ih =>
      have h := rIn_trans (rIn_single (step1_cons s0 c r s2)) (ih (c :: s0))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h
  have run2 (u a r : List Bool) :
      ∃ n ≤ r.length + 1, (flip bind N.step)^[n]
        (some (cfg (some 2) (delimit u ++ a) [] r)) =
        some (cfg none (delimit (r.reverse ++ u) ++ a) [] []) := by
    induction r generalizing u with
    | nil => exact rIn_single (step2_nil (delimit u ++ a) [])
    | cons c r ih =>
      have h := rIn_trans (rIn_single (step2_cons (delimit u ++ a) [] c r)) (ih (c :: u))
      simpa [delimit, List.reverse_cons, List.append_assoc, Nat.add_comm] using h
  have init_eq (l : List Bool) : initList N l = cfg (some 0) l [] [] := by
    simp only [initList, cfg, N]
    congr 1; funext k; fin_cases k <;> rfl
  have halt_eq (l : List Bool) : haltList N l = cfg none l [] [] := by
    simp only [haltList, cfg, N]
    congr 1; funext k; fin_cases k <;> rfl
  refine ⟨{ tm := N
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := 3 * Polynomial.X + 3
            outputsFun := fun x => ?_ }⟩
  set a := bitEncode x
  have hin : List.map (Equiv.refl Bool).invFun ((toEncoding (α := α)).encode x) = a := by
    change List.map id a = a; simp
  have hout : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := α × α)).encode (x, x)) = delimit a ++ a := by
    change List.map id (delimit a ++ a) = _; simp
  have hrun : ∃ n ≤ (a.length + 1) + (a.length + 1) + (a.length + 1),
      (flip bind N.step)^[n] (some (cfg (some 0) a [] [])) =
        some (cfg none (delimit a ++ a) [] []) := by
    have h0 := run0 a [] []
    have h1 := run1 [] a.reverse a.reverse
    have h2 := run2 [] a a.reverse
    simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h0 h1 h2
    exact rIn_trans (rIn_trans h0 h1) h2
  have hb : (a.length + 1) + (a.length + 1) + (a.length + 1) ≤
      (3 * Polynomial.X + 3 : Polynomial ℕ).eval ((toEncoding (α := α)).encode x).length := by
    change _ ≤ (3 * Polynomial.X + 3 : Polynomial ℕ).eval a.length
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    omega
  rw [hin, hout]
  exact Classical.choice (by
    obtain ⟨n, hle, he⟩ := rIn_mono hrun hb
    rw [← init_eq, ← halt_eq] at he
    exact ⟨⟨⟨n, he⟩, hle⟩⟩)

end OMA.PolyTimeLib

/- Proof of `isPolyTime_swap` for the polynomial-time closure library. -/

namespace OMA.PolyTimeLib

open ComplexityTheory BitstringEncoding

variable {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]

open Turing OMA.R_ComplexityTheory_P_eq_BPP_R1 in
theorem isPolyTime_swap : IsPolyTime (Prod.swap : α × β → β × α) := by
  let prog : Fin 4 → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) := fun q =>
    if q = 0 then
      .pop 0 (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.pop 0 (fun _ o => o) <|
            .push 1 (fun v => v.getD false) <|
            .load (fun _ => none) <| .goto fun _ => 0)
          (.load (fun _ => none) <| .goto fun _ => 1)
    else if q = 1 then
      .pop 0 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push 2 (fun v => v.getD false) <|
            .load (fun _ => none) <| .goto fun _ => 1)
          (.load (fun _ => none) <| .goto fun _ => 2)
    else if q = 2 then
      .pop 1 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push 0 (fun v => v.getD false) <|
            .load (fun _ => none) <| .goto fun _ => 2)
          (.push 0 (fun _ => false) <|
            .load (fun _ => none) <| .goto fun _ => 3)
    else
      .pop 2 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push 0 (fun v => v.getD false) <|
            .push 0 (fun _ => true) <|
            .load (fun _ => none) <| .goto fun _ => 3)
          (.load (fun _ => none) .halt)
  let N : FinTM2 :=
    { K := Fin 3
      k₀ := 0
      k₁ := 0
      Γ := fun _ => Bool
      Λ := Fin 4
      main := 0
      σ := Option Bool
      initialState := none
      m := prog }
  let mk (s0 s1 s2 : List Bool) : Fin 3 → List Bool :=
    fun k => if k = 0 then s0 else if k = 1 then s1 else s2
  have upd0 (s0 s1 s2 s0' : List Bool) :
      Function.update (mk s0 s1 s2) 0 s0' = mk s0' s1 s2 := by
    funext k; fin_cases k <;> rfl
  have upd1 (s0 s1 s2 s1' : List Bool) :
      Function.update (mk s0 s1 s2) 1 s1' = mk s0 s1' s2 := by
    funext k; fin_cases k <;> rfl
  have upd2 (s0 s1 s2 s2' : List Bool) :
      Function.update (mk s0 s1 s2) 2 s2' = mk s0 s1 s2' := by
    funext k; fin_cases k <;> rfl
  let cfg (l : Option (Fin 4)) (s0 s1 s2 : List Bool) : N.Cfg := ⟨l, none, mk s0 s1 s2⟩
  have step0_true (c : Bool) (rest s1 s2 : List Bool) :
      N.step (cfg (some 0) (true :: c :: rest) s1 s2) = some (cfg (some 0) rest (c :: s1) s2) := by
    show some (TM2.stepAux (prog 0) none (mk (true :: c :: rest) s1 s2)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step0_false (rest s1 s2 : List Bool) :
      N.step (cfg (some 0) (false :: rest) s1 s2) = some (cfg (some 1) rest s1 s2) := by
    show some (TM2.stepAux (prog 0) none (mk (false :: rest) s1 s2)) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step1_cons (c : Bool) (rest s1 s2 : List Bool) :
      N.step (cfg (some 1) (c :: rest) s1 s2) = some (cfg (some 1) rest s1 (c :: s2)) := by
    show some (TM2.stepAux (prog 1) none (mk (c :: rest) s1 s2)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd2, cfg]; rfl
  have step1_nil (s1 s2 : List Bool) :
      N.step (cfg (some 1) [] s1 s2) = some (cfg (some 2) [] s1 s2) := by
    show some (TM2.stepAux (prog 1) none (mk [] s1 s2)) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step2_cons (s0 : List Bool) (c : Bool) (s1 s2 : List Bool) :
      N.step (cfg (some 2) s0 (c :: s1) s2) = some (cfg (some 2) (c :: s0) s1 s2) := by
    show some (TM2.stepAux (prog 2) none (mk s0 (c :: s1) s2)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step2_nil (s0 s2 : List Bool) :
      N.step (cfg (some 2) s0 [] s2) = some (cfg (some 3) (false :: s0) [] s2) := by
    show some (TM2.stepAux (prog 2) none (mk s0 [] s2)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step3_cons (s0 s1 : List Bool) (c : Bool) (s2 : List Bool) :
      N.step (cfg (some 3) s0 s1 (c :: s2)) =
        some (cfg (some 3) (true :: c :: s0) s1 s2) := by
    show some (TM2.stepAux (prog 3) none (mk s0 s1 (c :: s2))) = _
    simp [prog, TM2.stepAux, mk, upd0, upd2, cfg]; rfl
  have step3_nil (s0 s1 : List Bool) :
      N.step (cfg (some 3) s0 s1 []) = some (cfg none s0 s1 []) := by
    show some (TM2.stepAux (prog 3) none (mk s0 s1 [])) = _
    simp [prog, TM2.stepAux, mk, upd2, cfg]; rfl
  have run0 (a rest s1 s2 : List Bool) :
      ∃ n ≤ a.length + 1, (flip bind N.step)^[n]
        (some (cfg (some 0) (delimit a ++ rest) s1 s2)) =
        some (cfg (some 1) rest (a.reverse ++ s1) s2) := by
    induction a generalizing s1 with
    | nil => exact rIn_single (step0_false rest s1 s2)
    | cons c a ih =>
      have h := rIn_trans (rIn_single (step0_true c (delimit a ++ rest) s1 s2)) (ih (c :: s1))
      simpa [delimit, List.reverse_cons, List.append_assoc, Nat.add_comm] using h
  have run1 (b s1 s2 : List Bool) :
      ∃ n ≤ b.length + 1, (flip bind N.step)^[n] (some (cfg (some 1) b s1 s2)) =
        some (cfg (some 2) [] s1 (b.reverse ++ s2)) := by
    induction b generalizing s2 with
    | nil => exact rIn_single (step1_nil s1 s2)
    | cons c b ih =>
      have h := rIn_trans (rIn_single (step1_cons c b s1 s2)) (ih (c :: s2))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h
  have run2 (s0 r s2 : List Bool) :
      ∃ n ≤ r.length + 1, (flip bind N.step)^[n] (some (cfg (some 2) s0 r s2)) =
        some (cfg (some 3) (false :: (r.reverse ++ s0)) [] s2) := by
    induction r generalizing s0 with
    | nil => exact rIn_single (step2_nil s0 s2)
    | cons c r ih =>
      have h := rIn_trans (rIn_single (step2_cons s0 c r s2)) (ih (c :: s0))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h
  have run3 (u a r : List Bool) :
      ∃ n ≤ r.length + 1, (flip bind N.step)^[n]
        (some (cfg (some 3) (delimit u ++ a) [] r)) =
        some (cfg none (delimit (r.reverse ++ u) ++ a) [] []) := by
    induction r generalizing u with
    | nil => exact rIn_single (step3_nil (delimit u ++ a) [])
    | cons c r ih =>
      have h1 := rIn_single (step3_cons (delimit u ++ a) [] c r)
      have h2 := ih (c :: u)
      have h := rIn_trans h1 h2
      simpa [delimit, List.reverse_cons, List.append_assoc, Nat.add_comm] using h
  have init_eq (l : List Bool) : initList N l = cfg (some 0) l [] [] := by
    simp only [initList, cfg, N]
    congr 1; funext k; fin_cases k <;> rfl
  have halt_eq (l : List Bool) : haltList N l = cfg none l [] [] := by
    simp only [haltList, cfg, N]
    congr 1; funext k; fin_cases k <;> rfl
  refine ⟨{ tm := N
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := 2 * Polynomial.X + 4
            outputsFun := fun p => ?_ }⟩
  set a := bitEncode p.1
  set b := bitEncode p.2
  have hin : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := α × β)).encode p) = delimit a ++ b := by
    change List.map id (delimit a ++ b) = _; simp
  have hout : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := β × α)).encode p.swap) = delimit b ++ a := by
    change List.map id (delimit b ++ a) = _; simp
  have hrun : ∃ n ≤ (a.length + 1) + (b.length + 1) + (a.length + 1) + (b.length + 1),
      (flip bind N.step)^[n] (some (cfg (some 0) (delimit a ++ b) [] [])) =
        some (cfg none (delimit b ++ a) [] []) := by
    have h0 := run0 a b [] []
    have h1 := run1 b a.reverse []
    have h2 := run2 [] a.reverse b.reverse
    have h3 := run3 [] a b.reverse
    simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h0 h1 h2 h3
    exact rIn_trans (rIn_trans (rIn_trans h0 h1) h2) h3
  have hlen : ((toEncoding (α := α × β)).encode p).length = 2 * a.length + 1 + b.length := by
    change (delimit a ++ b).length = _; simp [length_delimit]
  have hb : (a.length + 1) + (b.length + 1) + (a.length + 1) + (b.length + 1) ≤
      (2 * Polynomial.X + 4 : Polynomial ℕ).eval ((toEncoding (α := α × β)).encode p).length := by
    rw [hlen]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    omega
  rw [hin, hout]
  exact Classical.choice (by
    obtain ⟨n, hle, he⟩ := rIn_mono hrun hb
    rw [← init_eq, ← halt_eq] at he
    exact ⟨⟨⟨n, he⟩, hle⟩⟩)

end OMA.PolyTimeLib

/- Proof of `isPolyTime_select` for the polynomial-time closure library. -/

namespace OMA.PolyTimeLib

open ComplexityTheory BitstringEncoding

variable {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]

open Turing OMA.R_ComplexityTheory_P_eq_BPP_R1 in
theorem isPolyTime_select :
    IsPolyTime (fun p : Bool × (β × β) => if p.1 then p.2.1 else p.2.2) := by
  let prog : Fin 5 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 5) (Option Bool) := fun q =>
    if q = 0 then
      .pop 0 (fun _ _ => none) <|
        .pop 0 (fun _ o => o) <|
        .pop 0 (fun v _ => v) <|
        .branch (fun v => v == some true)
          (.load (fun _ => none) <| .goto fun _ => 1)
          (.load (fun _ => none) <| .goto fun _ => 4)
    else if q = 1 then
      .pop 0 (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.pop 0 (fun _ o => o) <|
            .push 1 (fun v => v.getD false) <|
            .load (fun _ => none) <| .goto fun _ => 1)
          (.load (fun _ => none) <| .goto fun _ => 2)
    else if q = 2 then
      .pop 0 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.load (fun _ => none) <| .goto fun _ => 2)
          (.load (fun _ => none) <| .goto fun _ => 3)
    else if q = 3 then
      .pop 1 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push 0 (fun v => v.getD false) <|
            .load (fun _ => none) <| .goto fun _ => 3)
          (.load (fun _ => none) .halt)
    else
      .pop 0 (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.pop 0 (fun _ _ => none) <| .goto fun _ => 4)
          (.load (fun _ => none) .halt)
  let N : FinTM2 :=
    { K := Fin 2
      k₀ := 0
      k₁ := 0
      Γ := fun _ => Bool
      Λ := Fin 5
      main := 0
      σ := Option Bool
      initialState := none
      m := prog }
  let mk (s0 s1 : List Bool) : Fin 2 → List Bool := fun k => if k = 0 then s0 else s1
  have upd0 (s0 s1 s0' : List Bool) :
      Function.update (mk s0 s1) 0 s0' = mk s0' s1 := by
    funext k; fin_cases k <;> rfl
  have upd1 (s0 s1 s1' : List Bool) :
      Function.update (mk s0 s1) 1 s1' = mk s0 s1' := by
    funext k; fin_cases k <;> rfl
  let cfg (l : Option (Fin 5)) (s0 s1 : List Bool) : N.Cfg := ⟨l, none, mk s0 s1⟩
  have step0_true (rest : List Bool) :
      N.step (cfg (some 0) (true :: true :: false :: rest) []) =
        some (cfg (some 1) rest []) := by
    show some (TM2.stepAux (prog 0) none (mk (true :: true :: false :: rest) [])) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step0_false (rest : List Bool) :
      N.step (cfg (some 0) (true :: false :: false :: rest) []) =
        some (cfg (some 4) rest []) := by
    show some (TM2.stepAux (prog 0) none (mk (true :: false :: false :: rest) [])) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step1_true (c : Bool) (rest s1 : List Bool) :
      N.step (cfg (some 1) (true :: c :: rest) s1) = some (cfg (some 1) rest (c :: s1)) := by
    show some (TM2.stepAux (prog 1) none (mk (true :: c :: rest) s1)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step1_false (rest s1 : List Bool) :
      N.step (cfg (some 1) (false :: rest) s1) = some (cfg (some 2) rest s1) := by
    show some (TM2.stepAux (prog 1) none (mk (false :: rest) s1)) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step2_cons (c : Bool) (rest s1 : List Bool) :
      N.step (cfg (some 2) (c :: rest) s1) = some (cfg (some 2) rest s1) := by
    show some (TM2.stepAux (prog 2) none (mk (c :: rest) s1)) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step2_nil (s1 : List Bool) :
      N.step (cfg (some 2) [] s1) = some (cfg (some 3) [] s1) := by
    show some (TM2.stepAux (prog 2) none (mk [] s1)) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step3_cons (s0 : List Bool) (c : Bool) (s1 : List Bool) :
      N.step (cfg (some 3) s0 (c :: s1)) = some (cfg (some 3) (c :: s0) s1) := by
    show some (TM2.stepAux (prog 3) none (mk s0 (c :: s1))) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step3_nil (s0 : List Bool) :
      N.step (cfg (some 3) s0 []) = some (cfg none s0 []) := by
    show some (TM2.stepAux (prog 3) none (mk s0 [])) = _
    simp [prog, TM2.stepAux, mk, upd1, cfg]; rfl
  have step4_true (c : Bool) (rest : List Bool) :
      N.step (cfg (some 4) (true :: c :: rest) []) = some (cfg (some 4) rest []) := by
    show some (TM2.stepAux (prog 4) none (mk (true :: c :: rest) [])) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step4_false (rest : List Bool) :
      N.step (cfg (some 4) (false :: rest) []) = some (cfg none rest []) := by
    show some (TM2.stepAux (prog 4) none (mk (false :: rest) [])) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have run1 (s rest s1 : List Bool) :
      ∃ n ≤ s.length + 1, (flip bind N.step)^[n]
        (some (cfg (some 1) (delimit s ++ rest) s1)) =
        some (cfg (some 2) rest (s.reverse ++ s1)) := by
    induction s generalizing s1 with
    | nil => exact rIn_single (step1_false rest s1)
    | cons c s ih =>
      have h := rIn_trans (rIn_single (step1_true c (delimit s ++ rest) s1)) (ih (c :: s1))
      simpa [delimit, List.reverse_cons, List.append_assoc, Nat.add_comm] using h
  have run2 (t s1 : List Bool) :
      ∃ n ≤ t.length + 1, (flip bind N.step)^[n] (some (cfg (some 2) t s1)) =
        some (cfg (some 3) [] s1) := by
    induction t with
    | nil => exact rIn_single (step2_nil s1)
    | cons c t ih =>
      have h := rIn_trans (rIn_single (step2_cons c t s1)) ih
      simpa [Nat.add_comm] using h
  have run3 (s0 r : List Bool) :
      ∃ n ≤ r.length + 1, (flip bind N.step)^[n] (some (cfg (some 3) s0 r)) =
        some (cfg none (r.reverse ++ s0) []) := by
    induction r generalizing s0 with
    | nil => exact rIn_single (step3_nil s0)
    | cons c r ih =>
      have h := rIn_trans (rIn_single (step3_cons s0 c r)) (ih (c :: s0))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h
  have run4 (s t : List Bool) :
      ∃ n ≤ s.length + 1, (flip bind N.step)^[n]
        (some (cfg (some 4) (delimit s ++ t) [])) =
        some (cfg none t []) := by
    induction s with
    | nil => exact rIn_single (step4_false t)
    | cons c s ih =>
      have h := rIn_trans (rIn_single (step4_true c (delimit s ++ t))) ih
      simpa [delimit, Nat.add_comm] using h
  have init_eq (l : List Bool) : initList N l = cfg (some 0) l [] := by
    simp only [initList, cfg, N]; rfl
  have halt_eq (l : List Bool) : haltList N l = cfg none l [] := by
    simp only [haltList, cfg, N]; rfl
  refine ⟨{ tm := N
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := Polynomial.X
            outputsFun := fun p => ?_ }⟩
  rcases p with ⟨b, x, y⟩
  set s := bitEncode x
  set t := bitEncode y
  have hin : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := Bool × (β × β))).encode (b, (x, y))) =
      true :: b :: false :: (delimit s ++ t) := by
    change List.map id (true :: b :: false :: (delimit s ++ t)) = _
    simp
  have hlen : ((toEncoding (α := Bool × (β × β))).encode (b, (x, y))).length =
      2 * s.length + t.length + 4 := by
    change (true :: b :: false :: (delimit s ++ t)).length = _
    simp [length_delimit]; omega
  cases b with
  | true =>
    have hout : List.map (Equiv.refl Bool).invFun
        ((toEncoding (α := β)).encode (if true then x else y)) = s := by
      change List.map id s = s; simp
    have hrun : ∃ n ≤ 1 + (s.length + 1) + (t.length + 1) + (s.length + 1),
        (flip bind N.step)^[n]
          (some (cfg (some 0) (true :: true :: false :: (delimit s ++ t)) [])) =
          some (cfg none s []) := by
      have h0 := rIn_single (step0_true (delimit s ++ t))
      have h1 := run1 s t []
      have h2 := run2 t s.reverse
      have h3 := run3 [] s.reverse
      simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h1 h2 h3
      exact rIn_trans (rIn_trans (rIn_trans h0 h1) h2) h3
    have hb : 1 + (s.length + 1) + (t.length + 1) + (s.length + 1) ≤
        (Polynomial.X : Polynomial ℕ).eval
          ((toEncoding (α := Bool × (β × β))).encode (true, (x, y))).length := by
      rw [hlen, Polynomial.eval_X]; omega
    rw [hin, hout]
    exact Classical.choice (by
      obtain ⟨n, hle, he⟩ := rIn_mono hrun hb
      rw [← init_eq, ← halt_eq] at he
      exact ⟨⟨⟨n, he⟩, hle⟩⟩)
  | false =>
    have hout : List.map (Equiv.refl Bool).invFun
        ((toEncoding (α := β)).encode (if false then x else y)) = t := by
      change List.map id t = t; simp
    have hrun : ∃ n ≤ 1 + (s.length + 1),
        (flip bind N.step)^[n]
          (some (cfg (some 0) (true :: false :: false :: (delimit s ++ t)) [])) =
          some (cfg none t []) :=
      rIn_trans (rIn_single (step0_false (delimit s ++ t))) (run4 s t)
    have hb : 1 + (s.length + 1) ≤
        (Polynomial.X : Polynomial ℕ).eval
          ((toEncoding (α := Bool × (β × β))).encode (false, (x, y))).length := by
      rw [hlen, Polynomial.eval_X]; omega
    rw [hin, hout]
    exact Classical.choice (by
      obtain ⟨n, hle, he⟩ := rIn_mono hrun hb
      rw [← init_eq, ← halt_eq] at he
      exact ⟨⟨⟨n, he⟩, hle⟩⟩)

end OMA.PolyTimeLib

/- Proof of `isPolyTime_natSucc` for the polynomial-time closure library. -/

namespace OMA.PolyTimeLib

open ComplexityTheory BitstringEncoding

variable {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]

private def isPolyTime_natSucc_incBits : List Bool → List Bool
  | [] => [true]
  | false :: rest => true :: rest
  | true :: rest => false :: isPolyTime_natSucc_incBits rest

open Turing OMA.R_ComplexityTheory_P_eq_BPP_R1 in
theorem isPolyTime_natSucc : IsPolyTime Nat.succ := by
  have incBits_encodePosNum (p : PosNum) :
      isPolyTime_natSucc_incBits (Computability.encodePosNum p) =
        Computability.encodePosNum (PosNum.succ p) := by
    induction p with
    | one => rfl
    | bit0 p _ => rfl
    | bit1 p ih =>
      simp only [Computability.encodePosNum, PosNum.succ, isPolyTime_natSucc_incBits, ih]
  have incBits_encodeNat (n : ℕ) :
      isPolyTime_natSucc_incBits (Computability.encodeNat n) =
        Computability.encodeNat (Nat.succ n) := by
    unfold Computability.encodeNat
    have hsucc : ((Nat.succ n : ℕ) : Num) = Num.succ (n : Num) := by
      apply Num.to_nat_inj.1
      simp [Num.cast_succ]
    rw [hsucc]
    cases h : (n : Num) with
    | zero => rfl
    | pos p =>
      simp only [Computability.encodeNum, Num.succ, Num.succ']
      exact incBits_encodePosNum p
  let prog : Fin 2 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool) := fun q =>
    if q = 0 then
      .pop 0 (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.push 1 (fun _ => false) <| .load (fun _ => none) <| .goto fun _ => 0)
          (.push 0 (fun _ => true) <| .load (fun _ => none) <| .goto fun _ => 1)
    else
      .pop 1 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push 0 (fun v => v.getD false) <| .load (fun _ => none) <| .goto fun _ => 1)
          (.load (fun _ => none) .halt)
  let N : FinTM2 :=
    { K := Fin 2
      k₀ := 0
      k₁ := 0
      Γ := fun _ => Bool
      Λ := Fin 2
      main := 0
      σ := Option Bool
      initialState := none
      m := prog }
  let mk (s0 s1 : List Bool) : Fin 2 → List Bool := fun k => if k = 0 then s0 else s1
  have upd0 (s0 s1 s0' : List Bool) :
      Function.update (mk s0 s1) 0 s0' = mk s0' s1 := by
    funext k; fin_cases k <;> rfl
  have upd1 (s0 s1 s1' : List Bool) :
      Function.update (mk s0 s1) 1 s1' = mk s0 s1' := by
    funext k; fin_cases k <;> rfl
  let cfg (l : Option (Fin 2)) (s0 s1 : List Bool) : N.Cfg := ⟨l, none, mk s0 s1⟩
  have step0_true (rest s1 : List Bool) :
      N.step (cfg (some 0) (true :: rest) s1) = some (cfg (some 0) rest (false :: s1)) := by
    show some (TM2.stepAux (prog 0) none (mk (true :: rest) s1)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step0_false (rest s1 : List Bool) :
      N.step (cfg (some 0) (false :: rest) s1) = some (cfg (some 1) (true :: rest) s1) := by
    show some (TM2.stepAux (prog 0) none (mk (false :: rest) s1)) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step0_nil (s1 : List Bool) :
      N.step (cfg (some 0) [] s1) = some (cfg (some 1) [true] s1) := by
    show some (TM2.stepAux (prog 0) none (mk [] s1)) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step1_cons (s0 : List Bool) (c : Bool) (s1 : List Bool) :
      N.step (cfg (some 1) s0 (c :: s1)) = some (cfg (some 1) (c :: s0) s1) := by
    show some (TM2.stepAux (prog 1) none (mk s0 (c :: s1))) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step1_nil (s0 : List Bool) :
      N.step (cfg (some 1) s0 []) = some (cfg none s0 []) := by
    show some (TM2.stepAux (prog 1) none (mk s0 [])) = _
    simp [prog, TM2.stepAux, mk, upd1, cfg]; rfl
  have run1 (s0 r : List Bool) :
      ∃ n ≤ r.length + 1, (flip bind N.step)^[n] (some (cfg (some 1) s0 r)) =
        some (cfg none (r.reverse ++ s0) []) := by
    induction r generalizing s0 with
    | nil => exact rIn_single (step1_nil s0)
    | cons c r ih =>
      have h := rIn_trans (rIn_single (step1_cons s0 c r)) (ih (c :: s0))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h
  have run0 (s s1 : List Bool) :
      ∃ n ≤ 2 * s.length + s1.length + 2, (flip bind N.step)^[n] (some (cfg (some 0) s s1)) =
        some (cfg none (s1.reverse ++ isPolyTime_natSucc_incBits s) []) := by
    induction s generalizing s1 with
    | nil =>
      have h := rIn_trans (rIn_single (step0_nil s1)) (run1 [true] s1)
      exact rIn_mono h (by simp; omega)
    | cons c rest ih =>
      cases c with
      | false =>
        have h := rIn_trans (rIn_single (step0_false rest s1)) (run1 (true :: rest) s1)
        exact rIn_mono h (by simp; omega)
      | true =>
        have h := rIn_trans (rIn_single (step0_true rest s1)) (ih (false :: s1))
        have h' : (false :: s1).reverse ++ isPolyTime_natSucc_incBits rest =
            s1.reverse ++ isPolyTime_natSucc_incBits (true :: rest) := by
          simp [isPolyTime_natSucc_incBits, List.reverse_cons, List.append_assoc]
        rw [h'] at h
        exact rIn_mono h (by simp; omega)
  have init_eq (l : List Bool) : initList N l = cfg (some 0) l [] := by
    simp only [initList, cfg, N]; rfl
  have halt_eq (l : List Bool) : haltList N l = cfg none l [] := by
    simp only [haltList, cfg, N]; rfl
  refine ⟨{ tm := N
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := 2 * Polynomial.X + 2
            outputsFun := fun n => ?_ }⟩
  set s := Computability.encodeNat n
  have hin : List.map (Equiv.refl Bool).invFun ((toEncoding (α := ℕ)).encode n) = s := by
    change List.map id s = s; simp
  have hout : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := ℕ)).encode (Nat.succ n)) = isPolyTime_natSucc_incBits s := by
    change List.map id (Computability.encodeNat (Nat.succ n)) = _
    rw [List.map_id, incBits_encodeNat]
  have hrun := run0 s []
  simp only [List.length_nil, List.reverse_nil, List.nil_append, add_zero] at hrun
  have hb : 2 * s.length + 2 ≤
      (2 * Polynomial.X + 2 : Polynomial ℕ).eval ((toEncoding (α := ℕ)).encode n).length := by
    change 2 * s.length + 2 ≤ (2 * Polynomial.X + 2 : Polynomial ℕ).eval s.length
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    omega
  rw [hin, hout]
  exact Classical.choice (by
    obtain ⟨m, hle, he⟩ := rIn_mono hrun hb
    rw [← init_eq, ← halt_eq] at he
    exact ⟨⟨⟨m, he⟩, hle⟩⟩)

end OMA.PolyTimeLib

/- Proof of `isPolyTime_natDouble` for the polynomial-time closure library. -/

namespace OMA.PolyTimeLib

open ComplexityTheory BitstringEncoding

variable {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]

private def isPolyTime_natDouble_bits : List Bool → List Bool
  | [] => []
  | c :: rest => false :: c :: rest

open Turing OMA.R_ComplexityTheory_P_eq_BPP_R1 in
theorem isPolyTime_natDouble : IsPolyTime (fun n : ℕ => 2 * n) := by
  let prog : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit (Option Bool) := fun _ =>
    .peek () (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push () (fun _ => false) <| .load (fun _ => none) .halt)
        (.load (fun _ => none) .halt)
  let N : FinTM2 :=
    { K := Unit
      k₀ := ()
      k₁ := ()
      Γ := fun _ => Bool
      Λ := Unit
      main := ()
      σ := Option Bool
      initialState := none
      m := prog }
  let cfg (l : Option Unit) (s : List Bool) : N.Cfg := ⟨l, none, fun _ => s⟩
  have step_nil : N.step (cfg (some ()) []) = some (cfg none []) := by
    show some (TM2.stepAux (prog ()) none (fun _ => [])) = _
    simp [prog, TM2.stepAux, cfg]; rfl
  have step_cons (c : Bool) (rest : List Bool) :
      N.step (cfg (some ()) (c :: rest)) = some (cfg none (false :: c :: rest)) := by
    show some (TM2.stepAux (prog ()) none (fun _ => c :: rest)) = _
    simp [prog, TM2.stepAux, cfg]; rfl
  have init_eq (l : List Bool) : initList N l = cfg (some ()) l := by
    simp only [initList, cfg, N]; rfl
  have halt_eq (l : List Bool) : haltList N l = cfg none l := by
    simp only [haltList, cfg, N]; rfl
  have encodeNat_double (n : ℕ) :
      Computability.encodeNat (2 * n) =
        isPolyTime_natDouble_bits (Computability.encodeNat n) := by
    unfold Computability.encodeNat
    cases h : (n : Num) with
    | zero =>
      have hn : n = 0 := by
        have := congrArg ((↑) : Num → ℕ) h
        simpa using this
      subst hn
      rfl
    | pos p =>
      have hn : (n : ℕ) = (p : ℕ) := by
        have := congrArg ((↑) : Num → ℕ) h
        simpa using this
      have h2 : ((2 * n : ℕ) : Num) = Num.pos (PosNum.bit0 p) := by
        apply Num.to_nat_inj.1
        simp only [Num.to_of_nat, Num.cast_pos, PosNum.cast_bit0, hn]
        omega
      rw [h2]
      simp only [Computability.encodeNum]
      cases hp : Computability.encodePosNum p with
      | nil => exact absurd hp (Computability.encodePosNum_nonempty p)
      | cons c rest =>
        simp only [Computability.encodePosNum, hp, isPolyTime_natDouble_bits]
  have run_bits (s : List Bool) :
      ∃ m ≤ 1, (flip bind N.step)^[m] (some (cfg (some ()) s)) =
        some (cfg none (isPolyTime_natDouble_bits s)) := by
    cases s with
    | nil => exact rIn_single step_nil
    | cons c rest => exact rIn_single (step_cons c rest)
  refine ⟨{ tm := N
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := 1
            outputsFun := fun n => ?_ }⟩
  set s := Computability.encodeNat n
  have hin : List.map (Equiv.refl Bool).invFun ((toEncoding (α := ℕ)).encode n) = s := by
    change List.map id s = s; simp
  have hout : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := ℕ)).encode (2 * n)) = isPolyTime_natDouble_bits s := by
    change List.map id (Computability.encodeNat (2 * n)) = _
    rw [List.map_id, encodeNat_double n]
  have hb : 1 ≤ (1 : Polynomial ℕ).eval ((toEncoding (α := ℕ)).encode n).length := by
    simp
  rw [hin, hout]
  exact Classical.choice (by
    obtain ⟨m, hle, he⟩ := rIn_mono (run_bits s) hb
    rw [← init_eq, ← halt_eq] at he
    exact ⟨⟨⟨m, he⟩, hle⟩⟩)

end OMA.PolyTimeLib

/- Proof of `isPolyTime_unaryLen` for the polynomial-time closure library. -/

namespace OMA.PolyTimeLib

open ComplexityTheory BitstringEncoding

variable {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]

private def isPolyTime_unaryLen_uEnc : ℕ → List Bool
  | 0 => []
  | k + 1 => true :: false :: false :: isPolyTime_unaryLen_uEnc k

open Turing OMA.R_ComplexityTheory_P_eq_BPP_R1 in
theorem isPolyTime_unaryLen :
    IsPolyTime (fun x : List Bool => List.replicate x.length false) := by
  have uEnc_succ_append (k : ℕ) (s : List Bool) :
      isPolyTime_unaryLen_uEnc k ++ true :: false :: false :: s =
        isPolyTime_unaryLen_uEnc (k + 1) ++ s := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [isPolyTime_unaryLen_uEnc, List.cons_append, ih]
  have bitEncode_rep (k : ℕ) :
      bitEncode (List.replicate k false) = isPolyTime_unaryLen_uEnc k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change true :: false :: false :: bitEncode (List.replicate k false) = _
      rw [ih]; rfl
  have bitEncode_len (x : List Bool) : (bitEncode x).length = 3 * x.length := by
    induction x with
    | nil => rfl
    | cons b xs ih =>
      change (true :: b :: false :: bitEncode xs).length = _
      simp only [List.length_cons, ih]; omega
  let prog : Fin 2 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool) := fun q =>
    if q = 0 then
      .pop 0 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.pop 0 (fun _ _ => none) <|
            .pop 0 (fun _ _ => none) <|
            .push 1 (fun _ => false) <|
            .load (fun _ => none) <| .goto fun _ => 0)
          (.load (fun _ => none) <| .goto fun _ => 1)
    else
      .pop 1 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push 0 (fun _ => false) <|
            .push 0 (fun _ => false) <|
            .push 0 (fun _ => true) <|
            .load (fun _ => none) <| .goto fun _ => 1)
          (.load (fun _ => none) .halt)
  let N : FinTM2 :=
    { K := Fin 2
      k₀ := 0
      k₁ := 0
      Γ := fun _ => Bool
      Λ := Fin 2
      main := 0
      σ := Option Bool
      initialState := none
      m := prog }
  let mk (s0 s1 : List Bool) : Fin 2 → List Bool := fun k => if k = 0 then s0 else s1
  have upd0 (s0 s1 s0' : List Bool) :
      Function.update (mk s0 s1) 0 s0' = mk s0' s1 := by
    funext k; fin_cases k <;> rfl
  have upd1 (s0 s1 s1' : List Bool) :
      Function.update (mk s0 s1) 1 s1' = mk s0 s1' := by
    funext k; fin_cases k <;> rfl
  let cfg (l : Option (Fin 2)) (s0 s1 : List Bool) : N.Cfg := ⟨l, none, mk s0 s1⟩
  have step0_cons (a b c : Bool) (rest s1 : List Bool) :
      N.step (cfg (some 0) (a :: b :: c :: rest) s1) = some (cfg (some 0) rest (false :: s1)) := by
    show some (TM2.stepAux (prog 0) none (mk (a :: b :: c :: rest) s1)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step0_nil (s1 : List Bool) :
      N.step (cfg (some 0) [] s1) = some (cfg (some 1) [] s1) := by
    show some (TM2.stepAux (prog 0) none (mk [] s1)) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step1_cons (s0 : List Bool) (c : Bool) (s1 : List Bool) :
      N.step (cfg (some 1) s0 (c :: s1)) =
        some (cfg (some 1) (true :: false :: false :: s0) s1) := by
    show some (TM2.stepAux (prog 1) none (mk s0 (c :: s1))) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step1_nil (s0 : List Bool) :
      N.step (cfg (some 1) s0 []) = some (cfg none s0 []) := by
    show some (TM2.stepAux (prog 1) none (mk s0 [])) = _
    simp [prog, TM2.stepAux, mk, upd1, cfg]; rfl
  have run0 (x : List Bool) (k : ℕ) :
      ∃ n ≤ x.length + 1, (flip bind N.step)^[n]
        (some (cfg (some 0) (bitEncode x) (List.replicate k false))) =
        some (cfg (some 1) [] (List.replicate (x.length + k) false)) := by
    induction x generalizing k with
    | nil =>
      change ∃ n ≤ 0 + 1, (flip bind N.step)^[n] (some (cfg (some 0) [] _)) = _
      simpa using rIn_single (step0_nil (List.replicate k false))
    | cons b xs ih =>
      have h1 : N.step (cfg (some 0) (bitEncode (b :: xs)) (List.replicate k false)) =
          some (cfg (some 0) (bitEncode xs) (List.replicate (k + 1) false)) :=
        step0_cons true b false (bitEncode xs) (List.replicate k false)
      have h := rIn_trans (rIn_single h1) (ih (k + 1))
      have hlen : xs.length + (k + 1) = (b :: xs).length + k := by simp; omega
      rw [hlen] at h
      exact rIn_mono h (by simp; omega)
  have run1 (s0 : List Bool) (k : ℕ) :
      ∃ n ≤ k + 1, (flip bind N.step)^[n]
        (some (cfg (some 1) s0 (List.replicate k false))) =
        some (cfg none (isPolyTime_unaryLen_uEnc k ++ s0) []) := by
    induction k generalizing s0 with
    | zero => exact rIn_single (step1_nil s0)
    | succ k ih =>
      have h := rIn_trans (rIn_single (step1_cons s0 false (List.replicate k false)))
        (ih (true :: false :: false :: s0))
      rw [uEnc_succ_append] at h
      exact rIn_mono h (by omega)
  have init_eq (l : List Bool) : initList N l = cfg (some 0) l [] := by
    simp only [initList, cfg, N]; rfl
  have halt_eq (l : List Bool) : haltList N l = cfg none l [] := by
    simp only [haltList, cfg, N]; rfl
  refine ⟨{ tm := N
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := Polynomial.X + 2
            outputsFun := fun x => ?_ }⟩
  have hin : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := List Bool)).encode x) = bitEncode x := by
    change List.map id (bitEncode x) = _; simp
  have hout : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := List Bool)).encode (List.replicate x.length false)) =
      isPolyTime_unaryLen_uEnc x.length := by
    change List.map id (bitEncode (List.replicate x.length false)) = _
    rw [List.map_id, bitEncode_rep]
  have hrun : ∃ n ≤ (x.length + 1) + (x.length + 1),
      (flip bind N.step)^[n] (some (cfg (some 0) (bitEncode x) [])) =
        some (cfg none (isPolyTime_unaryLen_uEnc x.length) []) := by
    have h0 := run0 x 0
    have h1 := run1 [] x.length
    simp only [List.replicate_zero, add_zero, List.append_nil] at h0 h1
    exact rIn_trans h0 h1
  have hb : (x.length + 1) + (x.length + 1) ≤
      (Polynomial.X + 2 : Polynomial ℕ).eval ((toEncoding (α := List Bool)).encode x).length := by
    change _ ≤ (Polynomial.X + 2 : Polynomial ℕ).eval (bitEncode x).length
    rw [bitEncode_len]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  rw [hin, hout]
  exact Classical.choice (by
    obtain ⟨n, hle, he⟩ := rIn_mono hrun hb
    rw [← init_eq, ← halt_eq] at he
    exact ⟨⟨⟨n, he⟩, hle⟩⟩)

end OMA.PolyTimeLib

/- Proof of `isPolyTime_unaryAdd` for the polynomial-time closure library. -/

namespace OMA.PolyTimeLib

open ComplexityTheory BitstringEncoding

variable {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]

private def isPolyTime_unaryAdd_uEnc : ℕ → List Bool
  | 0 => []
  | k + 1 => true :: false :: false :: isPolyTime_unaryAdd_uEnc k

open Turing OMA.R_ComplexityTheory_P_eq_BPP_R1 in
theorem isPolyTime_unaryAdd :
    IsPolyTime (fun p : List Bool × List Bool =>
      List.replicate (p.1.length + p.2.length) false) := by
  have uEnc_succ_append (k : ℕ) (s : List Bool) :
      isPolyTime_unaryAdd_uEnc k ++ true :: false :: false :: s =
        isPolyTime_unaryAdd_uEnc (k + 1) ++ s := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [isPolyTime_unaryAdd_uEnc, List.cons_append, ih]
  have bitEncode_rep (k : ℕ) :
      bitEncode (List.replicate k false) = isPolyTime_unaryAdd_uEnc k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change true :: false :: false :: bitEncode (List.replicate k false) = _
      rw [ih]; rfl
  have bitEncode_len (x : List Bool) : (bitEncode x).length = 3 * x.length := by
    induction x with
    | nil => rfl
    | cons b xs ih =>
      change (true :: b :: false :: bitEncode xs).length = _
      simp only [List.length_cons, ih]; omega
  let prog : Fin 3 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 3) (Option Bool) := fun q =>
    if q = 0 then
      .pop 0 (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.pop 0 (fun _ _ => none) <|
            .pop 0 (fun _ _ => none) <|
            .pop 0 (fun _ _ => none) <|
            .pop 0 (fun _ _ => none) <|
            .pop 0 (fun _ _ => none) <|
            .push 1 (fun _ => false) <|
            .load (fun _ => none) <| .goto fun _ => 0)
          (.load (fun _ => none) <| .goto fun _ => 1)
    else if q = 1 then
      .pop 0 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.pop 0 (fun _ _ => none) <|
            .pop 0 (fun _ _ => none) <|
            .push 1 (fun _ => false) <|
            .load (fun _ => none) <| .goto fun _ => 1)
          (.load (fun _ => none) <| .goto fun _ => 2)
    else
      .pop 1 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push 0 (fun _ => false) <|
            .push 0 (fun _ => false) <|
            .push 0 (fun _ => true) <|
            .load (fun _ => none) <| .goto fun _ => 2)
          (.load (fun _ => none) .halt)
  let N : FinTM2 :=
    { K := Fin 2
      k₀ := 0
      k₁ := 0
      Γ := fun _ => Bool
      Λ := Fin 3
      main := 0
      σ := Option Bool
      initialState := none
      m := prog }
  let mk (s0 s1 : List Bool) : Fin 2 → List Bool := fun k => if k = 0 then s0 else s1
  have upd0 (s0 s1 s0' : List Bool) :
      Function.update (mk s0 s1) 0 s0' = mk s0' s1 := by
    funext k; fin_cases k <;> rfl
  have upd1 (s0 s1 s1' : List Bool) :
      Function.update (mk s0 s1) 1 s1' = mk s0 s1' := by
    funext k; fin_cases k <;> rfl
  let cfg (l : Option (Fin 3)) (s0 s1 : List Bool) : N.Cfg := ⟨l, none, mk s0 s1⟩
  have step0_true (b1 b2 b3 b4 b5 : Bool) (rest s1 : List Bool) :
      N.step (cfg (some 0) (true :: b1 :: b2 :: b3 :: b4 :: b5 :: rest) s1) =
        some (cfg (some 0) rest (false :: s1)) := by
    show some (TM2.stepAux (prog 0) none
      (mk (true :: b1 :: b2 :: b3 :: b4 :: b5 :: rest) s1)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step0_false (rest s1 : List Bool) :
      N.step (cfg (some 0) (false :: rest) s1) = some (cfg (some 1) rest s1) := by
    show some (TM2.stepAux (prog 0) none (mk (false :: rest) s1)) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step1_cons (a b c : Bool) (rest s1 : List Bool) :
      N.step (cfg (some 1) (a :: b :: c :: rest) s1) = some (cfg (some 1) rest (false :: s1)) := by
    show some (TM2.stepAux (prog 1) none (mk (a :: b :: c :: rest) s1)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step1_nil (s1 : List Bool) :
      N.step (cfg (some 1) [] s1) = some (cfg (some 2) [] s1) := by
    show some (TM2.stepAux (prog 1) none (mk [] s1)) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step2_cons (s0 : List Bool) (c : Bool) (s1 : List Bool) :
      N.step (cfg (some 2) s0 (c :: s1)) =
        some (cfg (some 2) (true :: false :: false :: s0) s1) := by
    show some (TM2.stepAux (prog 2) none (mk s0 (c :: s1))) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step2_nil (s0 : List Bool) :
      N.step (cfg (some 2) s0 []) = some (cfg none s0 []) := by
    show some (TM2.stepAux (prog 2) none (mk s0 [])) = _
    simp [prog, TM2.stepAux, mk, upd1, cfg]; rfl
  have run0 (x rest : List Bool) (k : ℕ) :
      ∃ n ≤ x.length + 1, (flip bind N.step)^[n]
        (some (cfg (some 0) (delimit (bitEncode x) ++ rest) (List.replicate k false))) =
        some (cfg (some 1) rest (List.replicate (x.length + k) false)) := by
    induction x generalizing k with
    | nil =>
      change ∃ n ≤ 0 + 1, (flip bind N.step)^[n] (some (cfg (some 0) (false :: rest) _)) = _
      simpa using rIn_single (step0_false rest (List.replicate k false))
    | cons b xs ih =>
      have h1 : N.step (cfg (some 0) (delimit (bitEncode (b :: xs)) ++ rest)
            (List.replicate k false)) =
          some (cfg (some 0) (delimit (bitEncode xs) ++ rest) (List.replicate (k + 1) false)) :=
        step0_true true true b true false (delimit (bitEncode xs) ++ rest) (List.replicate k false)
      have h := rIn_trans (rIn_single h1) (ih (k + 1))
      have hlen : xs.length + (k + 1) = (b :: xs).length + k := by simp; omega
      rw [hlen] at h
      exact rIn_mono h (by simp; omega)
  have run1 (y : List Bool) (k : ℕ) :
      ∃ n ≤ y.length + 1, (flip bind N.step)^[n]
        (some (cfg (some 1) (bitEncode y) (List.replicate k false))) =
        some (cfg (some 2) [] (List.replicate (y.length + k) false)) := by
    induction y generalizing k with
    | nil =>
      change ∃ n ≤ 0 + 1, (flip bind N.step)^[n] (some (cfg (some 1) [] _)) = _
      simpa using rIn_single (step1_nil (List.replicate k false))
    | cons b ys ih =>
      have h1 : N.step (cfg (some 1) (bitEncode (b :: ys)) (List.replicate k false)) =
          some (cfg (some 1) (bitEncode ys) (List.replicate (k + 1) false)) :=
        step1_cons true b false (bitEncode ys) (List.replicate k false)
      have h := rIn_trans (rIn_single h1) (ih (k + 1))
      have hlen : ys.length + (k + 1) = (b :: ys).length + k := by simp; omega
      rw [hlen] at h
      exact rIn_mono h (by simp; omega)
  have run2 (s0 : List Bool) (k : ℕ) :
      ∃ n ≤ k + 1, (flip bind N.step)^[n]
        (some (cfg (some 2) s0 (List.replicate k false))) =
        some (cfg none (isPolyTime_unaryAdd_uEnc k ++ s0) []) := by
    induction k generalizing s0 with
    | zero => exact rIn_single (step2_nil s0)
    | succ k ih =>
      have h := rIn_trans (rIn_single (step2_cons s0 false (List.replicate k false)))
        (ih (true :: false :: false :: s0))
      rw [uEnc_succ_append] at h
      exact rIn_mono h (by omega)
  have init_eq (l : List Bool) : initList N l = cfg (some 0) l [] := by
    simp only [initList, cfg, N]; rfl
  have halt_eq (l : List Bool) : haltList N l = cfg none l [] := by
    simp only [haltList, cfg, N]; rfl
  refine ⟨{ tm := N
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := Polynomial.X + 3
            outputsFun := fun p => ?_ }⟩
  rcases p with ⟨x, y⟩
  have hin : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := List Bool × List Bool)).encode (x, y)) =
      delimit (bitEncode x) ++ bitEncode y := by
    change List.map id (delimit (bitEncode x) ++ bitEncode y) = _; simp
  have hout : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := List Bool)).encode (List.replicate (x.length + y.length) false)) =
      isPolyTime_unaryAdd_uEnc (x.length + y.length) := by
    change List.map id (bitEncode (List.replicate (x.length + y.length) false)) = _
    rw [List.map_id, bitEncode_rep]
  have hrun : ∃ n ≤ (x.length + 1) + (y.length + 1) + (x.length + y.length + 1),
      (flip bind N.step)^[n]
        (some (cfg (some 0) (delimit (bitEncode x) ++ bitEncode y) [])) =
        some (cfg none (isPolyTime_unaryAdd_uEnc (x.length + y.length)) []) := by
    have h0 := run0 x (bitEncode y) 0
    have h1 := run1 y x.length
    have h2 := run2 [] (x.length + y.length)
    simp only [List.replicate_zero, add_zero, List.append_nil] at h0 h1 h2
    rw [Nat.add_comm y.length x.length] at h1
    exact rIn_trans (rIn_trans h0 h1) h2
  have hlen : ((toEncoding (α := List Bool × List Bool)).encode (x, y)).length =
      6 * x.length + 3 * y.length + 1 := by
    change (delimit (bitEncode x) ++ bitEncode y).length = _
    simp only [List.length_append, length_delimit, bitEncode_len]
    omega
  have hb : (x.length + 1) + (y.length + 1) + (x.length + y.length + 1) ≤
      (Polynomial.X + 3 : Polynomial ℕ).eval
        ((toEncoding (α := List Bool × List Bool)).encode (x, y)).length := by
    rw [hlen]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  rw [hin, hout]
  exact Classical.choice (by
    obtain ⟨n, hle, he⟩ := rIn_mono hrun hb
    rw [← init_eq, ← halt_eq] at he
    exact ⟨⟨⟨n, he⟩, hle⟩⟩)

end OMA.PolyTimeLib

/- Proof of `isPolyTime_unaryMul` for the polynomial-time closure library. -/

namespace OMA.PolyTimeLib

open ComplexityTheory BitstringEncoding

variable {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]

private def isPolyTime_unaryMul_uEnc : ℕ → List Bool
  | 0 => []
  | k + 1 => true :: false :: false :: isPolyTime_unaryMul_uEnc k

open Turing OMA.R_ComplexityTheory_P_eq_BPP_R1 in
theorem isPolyTime_unaryMul :
    IsPolyTime (fun p : List Bool × List Bool =>
      List.replicate (p.1.length * p.2.length) false) := by
  have uEnc_succ_append (k : ℕ) (s : List Bool) :
      isPolyTime_unaryMul_uEnc k ++ true :: false :: false :: s =
        isPolyTime_unaryMul_uEnc (k + 1) ++ s := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [isPolyTime_unaryMul_uEnc, List.cons_append, ih]
  have uEnc_add (a b : ℕ) :
      isPolyTime_unaryMul_uEnc a ++ isPolyTime_unaryMul_uEnc b =
        isPolyTime_unaryMul_uEnc (a + b) := by
    induction a with
    | zero => simp [isPolyTime_unaryMul_uEnc]
    | succ a ih =>
      simp only [isPolyTime_unaryMul_uEnc, List.cons_append, ih, Nat.succ_add]
  have bitEncode_rep (k : ℕ) :
      bitEncode (List.replicate k false) = isPolyTime_unaryMul_uEnc k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change true :: false :: false :: bitEncode (List.replicate k false) = _
      rw [ih]; rfl
  have bitEncode_len (x : List Bool) : (bitEncode x).length = 3 * x.length := by
    induction x with
    | nil => rfl
    | cons b xs ih =>
      change (true :: b :: false :: bitEncode xs).length = _
      simp only [List.length_cons, ih]; omega
  let prog : Fin 6 → TM2.Stmt (fun _ : Fin 4 => Bool) (Fin 6) (Option Bool) := fun q =>
    if q = 0 then
      .pop 0 (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.pop 0 (fun _ _ => none) <|
            .pop 0 (fun _ _ => none) <|
            .pop 0 (fun _ _ => none) <|
            .pop 0 (fun _ _ => none) <|
            .pop 0 (fun _ _ => none) <|
            .push 1 (fun _ => false) <|
            .load (fun _ => none) <| .goto fun _ => 0)
          (.load (fun _ => none) <| .goto fun _ => 1)
    else if q = 1 then
      .pop 0 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.pop 0 (fun _ _ => none) <|
            .pop 0 (fun _ _ => none) <|
            .push 2 (fun _ => false) <|
            .load (fun _ => none) <| .goto fun _ => 1)
          (.load (fun _ => none) <| .goto fun _ => 2)
    else if q = 2 then
      .pop 1 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.load (fun _ => none) <| .goto fun _ => 3)
          (.load (fun _ => none) <| .goto fun _ => 5)
    else if q = 3 then
      .pop 2 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push 3 (fun _ => false) <|
            .push 0 (fun _ => false) <|
            .push 0 (fun _ => false) <|
            .push 0 (fun _ => true) <|
            .load (fun _ => none) <| .goto fun _ => 3)
          (.load (fun _ => none) <| .goto fun _ => 4)
    else if q = 4 then
      .pop 3 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push 2 (fun _ => false) <|
            .load (fun _ => none) <| .goto fun _ => 4)
          (.load (fun _ => none) <| .goto fun _ => 2)
    else
      .pop 2 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.load (fun _ => none) <| .goto fun _ => 5)
          (.load (fun _ => none) .halt)
  let N : FinTM2 :=
    { K := Fin 4
      k₀ := 0
      k₁ := 0
      Γ := fun _ => Bool
      Λ := Fin 6
      main := 0
      σ := Option Bool
      initialState := none
      m := prog }
  let mk (s0 s1 s2 s3 : List Bool) : Fin 4 → List Bool :=
    fun k => if k = 0 then s0 else if k = 1 then s1 else if k = 2 then s2 else s3
  have upd0 (s0 s1 s2 s3 s0' : List Bool) :
      Function.update (mk s0 s1 s2 s3) 0 s0' = mk s0' s1 s2 s3 := by
    funext k; fin_cases k <;> rfl
  have upd1 (s0 s1 s2 s3 s1' : List Bool) :
      Function.update (mk s0 s1 s2 s3) 1 s1' = mk s0 s1' s2 s3 := by
    funext k; fin_cases k <;> rfl
  have upd2 (s0 s1 s2 s3 s2' : List Bool) :
      Function.update (mk s0 s1 s2 s3) 2 s2' = mk s0 s1 s2' s3 := by
    funext k; fin_cases k <;> rfl
  have upd3 (s0 s1 s2 s3 s3' : List Bool) :
      Function.update (mk s0 s1 s2 s3) 3 s3' = mk s0 s1 s2 s3' := by
    funext k; fin_cases k <;> rfl
  let cfg (l : Option (Fin 6)) (s0 s1 s2 s3 : List Bool) : N.Cfg := ⟨l, none, mk s0 s1 s2 s3⟩
  have step0_true (b1 b2 b3 b4 b5 : Bool) (rest s1 s2 s3 : List Bool) :
      N.step (cfg (some 0) (true :: b1 :: b2 :: b3 :: b4 :: b5 :: rest) s1 s2 s3) =
        some (cfg (some 0) rest (false :: s1) s2 s3) := by
    show some (TM2.stepAux (prog 0) none
      (mk (true :: b1 :: b2 :: b3 :: b4 :: b5 :: rest) s1 s2 s3)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step0_false (rest s1 s2 s3 : List Bool) :
      N.step (cfg (some 0) (false :: rest) s1 s2 s3) = some (cfg (some 1) rest s1 s2 s3) := by
    show some (TM2.stepAux (prog 0) none (mk (false :: rest) s1 s2 s3)) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step1_cons (a b c : Bool) (rest s1 s2 s3 : List Bool) :
      N.step (cfg (some 1) (a :: b :: c :: rest) s1 s2 s3) =
        some (cfg (some 1) rest s1 (false :: s2) s3) := by
    show some (TM2.stepAux (prog 1) none (mk (a :: b :: c :: rest) s1 s2 s3)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd2, cfg]; rfl
  have step1_nil (s1 s2 s3 : List Bool) :
      N.step (cfg (some 1) [] s1 s2 s3) = some (cfg (some 2) [] s1 s2 s3) := by
    show some (TM2.stepAux (prog 1) none (mk [] s1 s2 s3)) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step2_cons (s0 : List Bool) (c : Bool) (s1 s2 s3 : List Bool) :
      N.step (cfg (some 2) s0 (c :: s1) s2 s3) = some (cfg (some 3) s0 s1 s2 s3) := by
    show some (TM2.stepAux (prog 2) none (mk s0 (c :: s1) s2 s3)) = _
    simp [prog, TM2.stepAux, mk, upd1, cfg]; rfl
  have step2_nil (s0 s2 s3 : List Bool) :
      N.step (cfg (some 2) s0 [] s2 s3) = some (cfg (some 5) s0 [] s2 s3) := by
    show some (TM2.stepAux (prog 2) none (mk s0 [] s2 s3)) = _
    simp [prog, TM2.stepAux, mk, upd1, cfg]; rfl
  have step3_cons (s0 s1 : List Bool) (c : Bool) (s2 s3 : List Bool) :
      N.step (cfg (some 3) s0 s1 (c :: s2) s3) =
        some (cfg (some 3) (true :: false :: false :: s0) s1 s2 (false :: s3)) := by
    show some (TM2.stepAux (prog 3) none (mk s0 s1 (c :: s2) s3)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd2, upd3, cfg]; rfl
  have step3_nil (s0 s1 s3 : List Bool) :
      N.step (cfg (some 3) s0 s1 [] s3) = some (cfg (some 4) s0 s1 [] s3) := by
    show some (TM2.stepAux (prog 3) none (mk s0 s1 [] s3)) = _
    simp [prog, TM2.stepAux, mk, upd2, cfg]; rfl
  have step4_cons (s0 s1 s2 : List Bool) (c : Bool) (s3 : List Bool) :
      N.step (cfg (some 4) s0 s1 s2 (c :: s3)) =
        some (cfg (some 4) s0 s1 (false :: s2) s3) := by
    show some (TM2.stepAux (prog 4) none (mk s0 s1 s2 (c :: s3))) = _
    simp [prog, TM2.stepAux, mk, upd2, upd3, cfg]; rfl
  have step4_nil (s0 s1 s2 : List Bool) :
      N.step (cfg (some 4) s0 s1 s2 []) = some (cfg (some 2) s0 s1 s2 []) := by
    show some (TM2.stepAux (prog 4) none (mk s0 s1 s2 [])) = _
    simp [prog, TM2.stepAux, mk, upd3, cfg]; rfl
  have step5_cons (s0 : List Bool) (c : Bool) (s2 : List Bool) :
      N.step (cfg (some 5) s0 [] (c :: s2) []) = some (cfg (some 5) s0 [] s2 []) := by
    show some (TM2.stepAux (prog 5) none (mk s0 [] (c :: s2) [])) = _
    simp [prog, TM2.stepAux, mk, upd2, cfg]; rfl
  have step5_nil (s0 : List Bool) :
      N.step (cfg (some 5) s0 [] [] []) = some (cfg none s0 [] [] []) := by
    show some (TM2.stepAux (prog 5) none (mk s0 [] [] [])) = _
    simp [prog, TM2.stepAux, mk, cfg]
    congr 2; funext k; fin_cases k <;> rfl
  have run0 (x rest : List Bool) (k : ℕ) :
      ∃ n ≤ x.length + 1, (flip bind N.step)^[n]
        (some (cfg (some 0) (delimit (bitEncode x) ++ rest) (List.replicate k false) [] [])) =
        some (cfg (some 1) rest (List.replicate (x.length + k) false) [] []) := by
    induction x generalizing k with
    | nil =>
      change ∃ n ≤ 0 + 1, (flip bind N.step)^[n] (some (cfg (some 0) (false :: rest) _ [] [])) = _
      simpa using rIn_single (step0_false rest (List.replicate k false) [] [])
    | cons b xs ih =>
      have h1 : N.step (cfg (some 0) (delimit (bitEncode (b :: xs)) ++ rest)
            (List.replicate k false) [] []) =
          some (cfg (some 0) (delimit (bitEncode xs) ++ rest)
            (List.replicate (k + 1) false) [] []) :=
        step0_true true true b true false (delimit (bitEncode xs) ++ rest)
          (List.replicate k false) [] []
      have h := rIn_trans (rIn_single h1) (ih (k + 1))
      have hlen : xs.length + (k + 1) = (b :: xs).length + k := by simp; omega
      rw [hlen] at h
      exact rIn_mono h (by simp; omega)
  have run1 (y : List Bool) (m k : ℕ) :
      ∃ n ≤ y.length + 1, (flip bind N.step)^[n]
        (some (cfg (some 1) (bitEncode y) (List.replicate m false) (List.replicate k false) [])) =
        some (cfg (some 2) [] (List.replicate m false) (List.replicate (y.length + k) false) []) := by
    induction y generalizing k with
    | nil =>
      change ∃ n ≤ 0 + 1, (flip bind N.step)^[n] (some (cfg (some 1) [] _ _ [])) = _
      simpa using rIn_single (step1_nil (List.replicate m false) (List.replicate k false) [])
    | cons b ys ih =>
      have h1 : N.step (cfg (some 1) (bitEncode (b :: ys))
            (List.replicate m false) (List.replicate k false) []) =
          some (cfg (some 1) (bitEncode ys)
            (List.replicate m false) (List.replicate (k + 1) false) []) :=
        step1_cons true b false (bitEncode ys) (List.replicate m false) (List.replicate k false) []
      have h := rIn_trans (rIn_single h1) (ih (k + 1))
      have hlen : ys.length + (k + 1) = (b :: ys).length + k := by simp; omega
      rw [hlen] at h
      exact rIn_mono h (by simp; omega)
  have run5 (s0 : List Bool) (r : ℕ) :
      ∃ n ≤ r + 1, (flip bind N.step)^[n]
        (some (cfg (some 5) s0 [] (List.replicate r false) [])) =
        some (cfg none s0 [] [] []) := by
    induction r with
    | zero => exact rIn_single (step5_nil s0)
    | succ r ih =>
      have h := rIn_trans (rIn_single (step5_cons s0 false (List.replicate r false))) ih
      exact rIn_mono h (by omega)
  have run3 (s0 s1 : List Bool) (r t : ℕ) :
      ∃ n ≤ r + 1, (flip bind N.step)^[n]
        (some (cfg (some 3) s0 s1 (List.replicate r false) (List.replicate t false))) =
        some (cfg (some 4) (isPolyTime_unaryMul_uEnc r ++ s0) s1 []
          (List.replicate (r + t) false)) := by
    induction r generalizing s0 t with
    | zero =>
      simp only [List.replicate_zero, isPolyTime_unaryMul_uEnc, List.nil_append, zero_add]
      exact rIn_single (step3_nil s0 s1 (List.replicate t false))
    | succ r ih =>
      have h1 : N.step (cfg (some 3) s0 s1 (List.replicate (r + 1) false)
            (List.replicate t false)) =
          some (cfg (some 3) (true :: false :: false :: s0) s1 (List.replicate r false)
            (List.replicate (t + 1) false)) :=
        step3_cons s0 s1 false (List.replicate r false) (List.replicate t false)
      have h := rIn_trans (rIn_single h1) (ih (true :: false :: false :: s0) (t + 1))
      rw [uEnc_succ_append] at h
      have hlen : r + (t + 1) = r + 1 + t := by omega
      rw [hlen] at h
      exact rIn_mono h (by omega)
  have run4 (s0 s1 : List Bool) (r t : ℕ) :
      ∃ n ≤ t + 1, (flip bind N.step)^[n]
        (some (cfg (some 4) s0 s1 (List.replicate r false) (List.replicate t false))) =
        some (cfg (some 2) s0 s1 (List.replicate (t + r) false) []) := by
    induction t generalizing r with
    | zero =>
      simp only [List.replicate_zero, zero_add]
      exact rIn_single (step4_nil s0 s1 (List.replicate r false))
    | succ t ih =>
      have h1 : N.step (cfg (some 4) s0 s1 (List.replicate r false)
            (List.replicate (t + 1) false)) =
          some (cfg (some 4) s0 s1 (List.replicate (r + 1) false)
            (List.replicate t false)) :=
        step4_cons s0 s1 (List.replicate r false) false (List.replicate t false)
      have h := rIn_trans (rIn_single h1) (ih (r + 1))
      have hlen : t + (r + 1) = t + 1 + r := by omega
      rw [hlen] at h
      exact rIn_mono h (by omega)
  have run2 (s0 : List Bool) (m r : ℕ) :
      ∃ n ≤ m * (2 * r + 3) + (r + 2), (flip bind N.step)^[n]
        (some (cfg (some 2) s0 (List.replicate m false) (List.replicate r false) [])) =
        some (cfg none (isPolyTime_unaryMul_uEnc (m * r) ++ s0) [] [] []) := by
    induction m generalizing s0 with
    | zero =>
      simp only [List.replicate_zero, zero_mul, isPolyTime_unaryMul_uEnc, List.nil_append, zero_add]
      have h := rIn_trans (rIn_single (step2_nil s0 (List.replicate r false) [])) (run5 s0 r)
      exact rIn_mono h (by omega)
    | succ m ih =>
      have h1 := rIn_single (step2_cons s0 false (List.replicate m false)
        (List.replicate r false) [])
      have h3 := run3 s0 (List.replicate m false) r 0
      have h4 := run4 (isPolyTime_unaryMul_uEnc r ++ s0) (List.replicate m false) 0 r
      have hrest := ih (isPolyTime_unaryMul_uEnc r ++ s0)
      simp only [List.replicate_zero, add_zero] at h3 h4
      have h := rIn_trans (rIn_trans (rIn_trans h1 h3) h4) hrest
      have hcat : isPolyTime_unaryMul_uEnc (m * r) ++ (isPolyTime_unaryMul_uEnc r ++ s0) =
          isPolyTime_unaryMul_uEnc ((m + 1) * r) ++ s0 := by
        rw [← List.append_assoc, uEnc_add, Nat.add_mul, one_mul]
      rw [hcat] at h
      exact rIn_mono h (by
        have : (m + 1) * (2 * r + 3) = m * (2 * r + 3) + (2 * r + 3) := by ring
        omega)
  have init_eq (l : List Bool) : initList N l = cfg (some 0) l [] [] [] := by
    simp only [initList, cfg, N]
    congr 1; funext k; fin_cases k <;> rfl
  have halt_eq (l : List Bool) : haltList N l = cfg none l [] [] [] := by
    simp only [haltList, cfg, N]
    congr 1; funext k; fin_cases k <;> rfl
  refine ⟨{ tm := N
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := 2 * Polynomial.X ^ 2 + 6 * Polynomial.X + 4
            outputsFun := fun p => ?_ }⟩
  rcases p with ⟨x, y⟩
  have hin : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := List Bool × List Bool)).encode (x, y)) =
      delimit (bitEncode x) ++ bitEncode y := by
    change List.map id (delimit (bitEncode x) ++ bitEncode y) = _; simp
  have hout : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := List Bool)).encode (List.replicate (x.length * y.length) false)) =
      isPolyTime_unaryMul_uEnc (x.length * y.length) := by
    change List.map id (bitEncode (List.replicate (x.length * y.length) false)) = _
    rw [List.map_id, bitEncode_rep]
  have hrun : ∃ n ≤ (x.length + 1) + (y.length + 1) +
        (x.length * (2 * y.length + 3) + (y.length + 2)),
      (flip bind N.step)^[n]
        (some (cfg (some 0) (delimit (bitEncode x) ++ bitEncode y) [] [] [])) =
        some (cfg none (isPolyTime_unaryMul_uEnc (x.length * y.length)) [] [] []) := by
    have h0 := run0 x (bitEncode y) 0
    have h1 := run1 y x.length 0
    have h2 := run2 [] x.length y.length
    simp only [List.replicate_zero, add_zero, List.append_nil] at h0 h1 h2
    exact rIn_trans (rIn_trans h0 h1) h2
  have hlen : ((toEncoding (α := List Bool × List Bool)).encode (x, y)).length =
      6 * x.length + 3 * y.length + 1 := by
    change (delimit (bitEncode x) ++ bitEncode y).length = _
    simp only [List.length_append, length_delimit, bitEncode_len]
    omega
  have hb : (x.length + 1) + (y.length + 1) +
        (x.length * (2 * y.length + 3) + (y.length + 2)) ≤
      (2 * Polynomial.X ^ 2 + 6 * Polynomial.X + 4 : Polynomial ℕ).eval
        ((toEncoding (α := List Bool × List Bool)).encode (x, y)).length := by
    rw [hlen]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_X]
    nlinarith
  rw [hin, hout]
  exact Classical.choice (by
    obtain ⟨n, hle, he⟩ := rIn_mono hrun hb
    rw [← init_eq, ← halt_eq] at he
    exact ⟨⟨⟨n, he⟩, hle⟩⟩)

end OMA.PolyTimeLib

/- Proof of `isPolyTime_natLt` for the polynomial-time closure library. -/

namespace OMA.PolyTimeLib

open ComplexityTheory BitstringEncoding

variable {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]

private def isPolyTime_natLt_cmpBits (acc : Bool) : List Bool → List Bool → Bool
  | [], [] => acc
  | [], _ :: _ => true
  | _ :: _, [] => false
  | ba :: sa, bb :: sb =>
      isPolyTime_natLt_cmpBits (if ba == bb then acc else bb) sa sb

open Turing OMA.R_ComplexityTheory_P_eq_BPP_R1 in
theorem isPolyTime_natLt : IsPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  have hone : ((PosNum.one : PosNum) : ℕ) = 1 := rfl
  have pos_pos : ∀ p : PosNum, 0 < (p : ℕ) := by
    intro p
    induction p with
    | one => decide
    | bit0 p ih => simp only [PosNum.cast_bit0]; omega
    | bit1 p ih => simp only [PosNum.cast_bit1]; omega
  have cmp_pos (p q : PosNum) (acc : Bool) :
      isPolyTime_natLt_cmpBits acc (Computability.encodePosNum p) (Computability.encodePosNum q) =
        if (p : ℕ) < (q : ℕ) then true else if (p : ℕ) = (q : ℕ) then acc else false := by
    induction p generalizing q acc with
    | one =>
      cases q with
      | one => simp [Computability.encodePosNum, isPolyTime_natLt_cmpBits]
      | bit0 q' =>
        have hq := pos_pos q'
        simp only [Computability.encodePosNum, isPolyTime_natLt_cmpBits]
        cases h : Computability.encodePosNum q' with
        | nil => exact absurd h (Computability.encodePosNum_nonempty q')
        | cons c cs =>
          simp only [isPolyTime_natLt_cmpBits, hone, PosNum.cast_bit0]
          split_ifs <;> first | rfl | omega
      | bit1 q' =>
        have hq := pos_pos q'
        simp only [Computability.encodePosNum, isPolyTime_natLt_cmpBits]
        cases h : Computability.encodePosNum q' with
        | nil => exact absurd h (Computability.encodePosNum_nonempty q')
        | cons c cs =>
          simp only [isPolyTime_natLt_cmpBits, hone, PosNum.cast_bit1]
          split_ifs <;> first | rfl | omega
    | bit0 p' ih =>
      cases q with
      | one =>
        have hp := pos_pos p'
        simp only [Computability.encodePosNum, isPolyTime_natLt_cmpBits]
        cases h : Computability.encodePosNum p' with
        | nil => exact absurd h (Computability.encodePosNum_nonempty p')
        | cons c cs =>
          simp only [isPolyTime_natLt_cmpBits, hone, PosNum.cast_bit0]
          split_ifs <;> first | rfl | omega
      | bit0 q' =>
        have hstep : isPolyTime_natLt_cmpBits acc
            (Computability.encodePosNum (PosNum.bit0 p'))
            (Computability.encodePosNum (PosNum.bit0 q')) =
            isPolyTime_natLt_cmpBits acc (Computability.encodePosNum p')
              (Computability.encodePosNum q') := rfl
        rw [hstep, ih q' acc]
        simp only [PosNum.cast_bit0]
        rcases lt_trichotomy (p' : ℕ) (q' : ℕ) with h | h | h
        · simp [h, show (p' : ℕ) + p' < q' + q' by omega]
        · simp [h]
        · simp [show ¬(p' : ℕ) < q' by omega, show (p' : ℕ) ≠ q' by omega,
            show ¬((p' : ℕ) + p' < q' + q') by omega,
            show (p' : ℕ) + p' ≠ q' + q' by omega]
      | bit1 q' =>
        have hstep : isPolyTime_natLt_cmpBits acc
            (Computability.encodePosNum (PosNum.bit0 p'))
            (Computability.encodePosNum (PosNum.bit1 q')) =
            isPolyTime_natLt_cmpBits true (Computability.encodePosNum p')
              (Computability.encodePosNum q') := rfl
        rw [hstep, ih q' true]
        simp only [PosNum.cast_bit0, PosNum.cast_bit1]
        rcases lt_trichotomy (p' : ℕ) (q' : ℕ) with h | h | h
        · simp [h, show (p' : ℕ) + p' < q' + q' + 1 by omega]
        · simp [h]
        · simp [show ¬(p' : ℕ) < q' by omega, show (p' : ℕ) ≠ q' by omega,
            show ¬((p' : ℕ) + p' < q' + q' + 1) by omega,
            show (p' : ℕ) + p' ≠ q' + q' + 1 by omega]
    | bit1 p' ih =>
      cases q with
      | one =>
        have hp := pos_pos p'
        simp only [Computability.encodePosNum, isPolyTime_natLt_cmpBits]
        cases h : Computability.encodePosNum p' with
        | nil => exact absurd h (Computability.encodePosNum_nonempty p')
        | cons c cs =>
          simp only [isPolyTime_natLt_cmpBits, hone, PosNum.cast_bit1]
          split_ifs <;> first | rfl | omega
      | bit0 q' =>
        have hstep : isPolyTime_natLt_cmpBits acc
            (Computability.encodePosNum (PosNum.bit1 p'))
            (Computability.encodePosNum (PosNum.bit0 q')) =
            isPolyTime_natLt_cmpBits false (Computability.encodePosNum p')
              (Computability.encodePosNum q') := rfl
        rw [hstep, ih q' false]
        simp only [PosNum.cast_bit1, PosNum.cast_bit0]
        rcases lt_trichotomy (p' : ℕ) (q' : ℕ) with h | h | h
        · simp [h, show (p' : ℕ) + p' + 1 < q' + q' by omega]
        · simp [h, show ¬((q' : ℕ) + q' + 1 < q' + q') by omega]
        · simp [show ¬(p' : ℕ) < q' by omega, show (p' : ℕ) ≠ q' by omega,
            show ¬((p' : ℕ) + p' + 1 < q' + q') by omega,
            show (p' : ℕ) + p' + 1 ≠ q' + q' by omega]
      | bit1 q' =>
        have hstep : isPolyTime_natLt_cmpBits acc
            (Computability.encodePosNum (PosNum.bit1 p'))
            (Computability.encodePosNum (PosNum.bit1 q')) =
            isPolyTime_natLt_cmpBits acc (Computability.encodePosNum p')
              (Computability.encodePosNum q') := rfl
        rw [hstep, ih q' acc]
        simp only [PosNum.cast_bit1]
        rcases lt_trichotomy (p' : ℕ) (q' : ℕ) with h | h | h
        · simp [h, show (p' : ℕ) + p' + 1 < q' + q' + 1 by omega]
        · simp [h]
        · simp [show ¬(p' : ℕ) < q' by omega, show (p' : ℕ) ≠ q' by omega,
            show ¬((p' : ℕ) + p' + 1 < q' + q' + 1) by omega,
            show (p' : ℕ) + p' ≠ q' + q' by omega]
  have cmp_nat (m n : ℕ) :
      isPolyTime_natLt_cmpBits false (Computability.encodeNat m) (Computability.encodeNat n) =
        decide (m < n) := by
    unfold Computability.encodeNat
    cases hm : (m : Num) with
    | zero =>
      have hm0 : m = 0 := by have := congrArg ((↑) : Num → ℕ) hm; simpa using this
      cases hn : (n : Num) with
      | zero =>
        have hn0 : n = 0 := by have := congrArg ((↑) : Num → ℕ) hn; simpa using this
        subst hm0; subst hn0; rfl
      | pos q =>
        have hnq : n = (q : ℕ) := by have := congrArg ((↑) : Num → ℕ) hn; simpa using this
        have hq := pos_pos q
        simp only [Computability.encodeNum]
        cases h : Computability.encodePosNum q with
        | nil => exact absurd h (Computability.encodePosNum_nonempty q)
        | cons c cs =>
          simp only [isPolyTime_natLt_cmpBits, hm0, hnq]
          exact (decide_eq_true hq).symm
    | pos p =>
      have hmp : m = (p : ℕ) := by have := congrArg ((↑) : Num → ℕ) hm; simpa using this
      have hp := pos_pos p
      cases hn : (n : Num) with
      | zero =>
        have hn0 : n = 0 := by have := congrArg ((↑) : Num → ℕ) hn; simpa using this
        simp only [Computability.encodeNum]
        cases h : Computability.encodePosNum p with
        | nil => exact absurd h (Computability.encodePosNum_nonempty p)
        | cons c cs =>
          simp only [isPolyTime_natLt_cmpBits, hmp, hn0]
          exact (decide_eq_false (by omega)).symm
      | pos q =>
        have hnq : n = (q : ℕ) := by have := congrArg ((↑) : Num → ℕ) hn; simpa using this
        simp only [Computability.encodeNum, cmp_pos p q false, hmp, hnq]
        by_cases hlt : (p : ℕ) < (q : ℕ)
        · simp [hlt]
        · simp [hlt]
  let cmpStmt (acc : Bool) :
      TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 6) (Option Bool × Option Bool) :=
    .pop 2 (fun _ o => (o, none)) <|
      .pop 0 (fun v o => (v.1, o)) <|
      .branch (fun v => v.1.isSome)
        (.branch (fun v => v.2.isSome)
          (.branch (fun v => if v.1 == v.2 then acc else v.2.getD false)
            (.load (fun _ => (none, none)) <| .goto fun _ => 3)
            (.load (fun _ => (none, none)) <| .goto fun _ => 2))
          (.load (fun _ => (none, none)) <| .goto fun _ => 4))
        (.branch (fun v => v.2.isSome)
          (.load (fun _ => (none, none)) <| .goto fun _ => 5)
          (.push 0 (fun _ => acc) <| .load (fun _ => (none, none)) .halt))
  let prog : Fin 6 →
      TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 6) (Option Bool × Option Bool) := fun q =>
    if q = 0 then
      .pop 0 (fun _ o => (o, none)) <|
        .branch (fun v => v.1 == some true)
          (.pop 0 (fun _ o => (o, none)) <|
            .push 1 (fun v => v.1.getD false) <|
            .load (fun _ => (none, none)) <| .goto fun _ => 0)
          (.load (fun _ => (none, none)) <| .goto fun _ => 1)
    else if q = 1 then
      .pop 1 (fun _ o => (o, none)) <|
        .branch (fun v => v.1.isSome)
          (.push 2 (fun v => v.1.getD false) <|
            .load (fun _ => (none, none)) <| .goto fun _ => 1)
          (.load (fun _ => (none, none)) <| .goto fun _ => 2)
    else if q = 2 then
      cmpStmt false
    else if q = 3 then
      cmpStmt true
    else if q = 4 then
      .pop 2 (fun _ o => (o, none)) <|
        .branch (fun v => v.1.isSome)
          (.load (fun _ => (none, none)) <| .goto fun _ => 4)
          (.push 0 (fun _ => false) <| .load (fun _ => (none, none)) .halt)
    else
      .pop 0 (fun _ o => (o, none)) <|
        .branch (fun v => v.1.isSome)
          (.load (fun _ => (none, none)) <| .goto fun _ => 5)
          (.push 0 (fun _ => true) <| .load (fun _ => (none, none)) .halt)
  let N : FinTM2 :=
    { K := Fin 3
      k₀ := 0
      k₁ := 0
      Γ := fun _ => Bool
      Λ := Fin 6
      main := 0
      σ := Option Bool × Option Bool
      initialState := (none, none)
      m := prog }
  let mk (s0 s1 s2 : List Bool) : Fin 3 → List Bool :=
    fun k => if k = 0 then s0 else if k = 1 then s1 else s2
  have upd0 (s0 s1 s2 s0' : List Bool) :
      Function.update (mk s0 s1 s2) 0 s0' = mk s0' s1 s2 := by
    funext k; fin_cases k <;> rfl
  have upd1 (s0 s1 s2 s1' : List Bool) :
      Function.update (mk s0 s1 s2) 1 s1' = mk s0 s1' s2 := by
    funext k; fin_cases k <;> rfl
  have upd2 (s0 s1 s2 s2' : List Bool) :
      Function.update (mk s0 s1 s2) 2 s2' = mk s0 s1 s2' := by
    funext k; fin_cases k <;> rfl
  let cfg (l : Option (Fin 6)) (s0 s1 s2 : List Bool) : N.Cfg := ⟨l, (none, none), mk s0 s1 s2⟩
  let accLab (acc : Bool) : Fin 6 := if acc then 3 else 2
  have step0_true (c : Bool) (rest s1 s2 : List Bool) :
      N.step (cfg (some 0) (true :: c :: rest) s1 s2) = some (cfg (some 0) rest (c :: s1) s2) := by
    show some (TM2.stepAux (prog 0) (none, none) (mk (true :: c :: rest) s1 s2)) = _
    simp [prog, TM2.stepAux, mk, upd0, upd1, cfg]; rfl
  have step0_false (rest s1 s2 : List Bool) :
      N.step (cfg (some 0) (false :: rest) s1 s2) = some (cfg (some 1) rest s1 s2) := by
    show some (TM2.stepAux (prog 0) (none, none) (mk (false :: rest) s1 s2)) = _
    simp [prog, TM2.stepAux, mk, upd0, cfg]; rfl
  have step1_cons (s0 : List Bool) (c : Bool) (s1 s2 : List Bool) :
      N.step (cfg (some 1) s0 (c :: s1) s2) = some (cfg (some 1) s0 s1 (c :: s2)) := by
    show some (TM2.stepAux (prog 1) (none, none) (mk s0 (c :: s1) s2)) = _
    simp [prog, TM2.stepAux, mk, upd1, upd2, cfg]; rfl
  have step1_nil (s0 s2 : List Bool) :
      N.step (cfg (some 1) s0 [] s2) = some (cfg (some 2) s0 [] s2) := by
    show some (TM2.stepAux (prog 1) (none, none) (mk s0 [] s2)) = _
    simp [prog, TM2.stepAux, mk, upd1, cfg]; rfl
  have step4_cons (c : Bool) (sa : List Bool) :
      N.step (cfg (some 4) [] [] (c :: sa)) = some (cfg (some 4) [] [] sa) := by
    show some (TM2.stepAux (prog 4) (none, none) (mk [] [] (c :: sa))) = _
    simp [prog, TM2.stepAux, mk, upd2, cfg]; rfl
  have step4_nil :
      N.step (cfg (some 4) [] [] []) = some (cfg none [false] [] []) := by
    show some (TM2.stepAux (prog 4) (none, none) (mk [] [] [])) = _
    simp [prog, TM2.stepAux, mk, cfg]
    congr 2; funext k; fin_cases k <;> rfl
  have step5_cons (c : Bool) (sb : List Bool) :
      N.step (cfg (some 5) (c :: sb) [] []) = some (cfg (some 5) sb [] []) := by
    show some (TM2.stepAux (prog 5) (none, none) (mk (c :: sb) [] [])) = _
    simp [prog, TM2.stepAux, mk, cfg]
    congr 2; funext k; fin_cases k <;> rfl
  have step5_nil :
      N.step (cfg (some 5) [] [] []) = some (cfg none [true] [] []) := by
    show some (TM2.stepAux (prog 5) (none, none) (mk [] [] [])) = _
    simp [prog, TM2.stepAux, mk, cfg]
    congr 2; funext k; fin_cases k <;> rfl
  have step_cmp_nil_nil (acc : Bool) :
      N.step (cfg (some (accLab acc)) [] [] []) = some (cfg none [acc] [] []) := by
    cases acc
    · show some (TM2.stepAux (prog 2) (none, none) (mk [] [] [])) = _
      simp [prog, cmpStmt, TM2.stepAux, mk, cfg]
      congr 2; funext k; fin_cases k <;> rfl
    · show some (TM2.stepAux (prog 3) (none, none) (mk [] [] [])) = _
      simp [prog, cmpStmt, TM2.stepAux, mk, cfg]
      congr 2; funext k; fin_cases k <;> rfl
  have step_cmp_nil_cons (acc bb : Bool) (sb : List Bool) :
      N.step (cfg (some (accLab acc)) (bb :: sb) [] []) = some (cfg (some 5) sb [] []) := by
    cases acc
    · show some (TM2.stepAux (prog 2) (none, none) (mk (bb :: sb) [] [])) = _
      simp [prog, cmpStmt, TM2.stepAux, mk, cfg]
      congr 2; funext k; fin_cases k <;> rfl
    · show some (TM2.stepAux (prog 3) (none, none) (mk (bb :: sb) [] [])) = _
      simp [prog, cmpStmt, TM2.stepAux, mk, cfg]
      congr 2; funext k; fin_cases k <;> rfl
  have step_cmp_cons_nil (acc ba : Bool) (sa : List Bool) :
      N.step (cfg (some (accLab acc)) [] [] (ba :: sa)) = some (cfg (some 4) [] [] sa) := by
    cases acc
    · show some (TM2.stepAux (prog 2) (none, none) (mk [] [] (ba :: sa))) = _
      simp [prog, cmpStmt, TM2.stepAux, mk, cfg]
      congr 2; funext k; fin_cases k <;> rfl
    · show some (TM2.stepAux (prog 3) (none, none) (mk [] [] (ba :: sa))) = _
      simp [prog, cmpStmt, TM2.stepAux, mk, cfg]
      congr 2; funext k; fin_cases k <;> rfl
  have step_cmp_cons_cons (acc ba bb : Bool) (sa sb : List Bool) :
      N.step (cfg (some (accLab acc)) (bb :: sb) [] (ba :: sa)) =
        some (cfg (some (accLab (if ba == bb then acc else bb))) sb [] sa) := by
    cases acc <;> cases ba <;> cases bb <;> (
      dsimp only [accLab, cfg]
      simp [N, FinTM2.step, TM2.step, prog, cmpStmt, TM2.stepAux, mk]
      congr 2; funext k; fin_cases k <;> rfl)
  have run0 (a rest s1 s2 : List Bool) :
      ∃ n ≤ a.length + 1, (flip bind N.step)^[n]
        (some (cfg (some 0) (delimit a ++ rest) s1 s2)) =
        some (cfg (some 1) rest (a.reverse ++ s1) s2) := by
    induction a generalizing s1 with
    | nil => exact rIn_single (step0_false rest s1 s2)
    | cons c a ih =>
      have h := rIn_trans (rIn_single (step0_true c (delimit a ++ rest) s1 s2)) (ih (c :: s1))
      simpa [delimit, List.reverse_cons, List.append_assoc, Nat.add_comm] using h
  have run1 (s0 r s2 : List Bool) :
      ∃ n ≤ r.length + 1, (flip bind N.step)^[n] (some (cfg (some 1) s0 r s2)) =
        some (cfg (some 2) s0 [] (r.reverse ++ s2)) := by
    induction r generalizing s2 with
    | nil => exact rIn_single (step1_nil s0 s2)
    | cons c r ih =>
      have h := rIn_trans (rIn_single (step1_cons s0 c r s2)) (ih (c :: s2))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h
  have run4 (sa : List Bool) :
      ∃ n ≤ sa.length + 1, (flip bind N.step)^[n] (some (cfg (some 4) [] [] sa)) =
        some (cfg none [false] [] []) := by
    induction sa with
    | nil => exact rIn_single step4_nil
    | cons c sa ih =>
      have h := rIn_trans (rIn_single (step4_cons c sa)) ih
      simpa [Nat.add_comm] using h
  have run5 (sb : List Bool) :
      ∃ n ≤ sb.length + 1, (flip bind N.step)^[n] (some (cfg (some 5) sb [] [])) =
        some (cfg none [true] [] []) := by
    induction sb with
    | nil => exact rIn_single step5_nil
    | cons c sb ih =>
      have h := rIn_trans (rIn_single (step5_cons c sb)) ih
      simpa [Nat.add_comm] using h
  have run_cmp (sa sb : List Bool) (acc : Bool) :
      ∃ n ≤ sa.length + sb.length + 2,
        (flip bind N.step)^[n] (some (cfg (some (accLab acc)) sb [] sa)) =
          some (cfg none [isPolyTime_natLt_cmpBits acc sa sb] [] []) := by
    induction sa generalizing sb acc with
    | nil =>
      cases sb with
      | nil => exact rIn_mono (rIn_single (step_cmp_nil_nil acc)) (by omega)
      | cons bb sb =>
        have h := rIn_trans (rIn_single (step_cmp_nil_cons acc bb sb)) (run5 sb)
        exact rIn_mono h (by simp; omega)
    | cons ba sa ih =>
      cases sb with
      | nil =>
        have h := rIn_trans (rIn_single (step_cmp_cons_nil acc ba sa)) (run4 sa)
        exact rIn_mono h (by simp; omega)
      | cons bb sb =>
        have h := rIn_trans (rIn_single (step_cmp_cons_cons acc ba bb sa sb))
          (ih sb (if ba == bb then acc else bb))
        exact rIn_mono h (by simp; omega)
  have init_eq (l : List Bool) : initList N l = cfg (some 0) l [] [] := by
    simp only [initList, cfg, N]
    congr 1; funext k; fin_cases k <;> rfl
  have halt_eq (l : List Bool) : haltList N l = cfg none l [] [] := by
    simp only [haltList, cfg, N]
    congr 1; funext k; fin_cases k <;> rfl
  refine ⟨{ tm := N
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := 2 * Polynomial.X + 4
            outputsFun := fun p => ?_ }⟩
  rcases p with ⟨m, n⟩
  set a := Computability.encodeNat m
  set b := Computability.encodeNat n
  have hin : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := ℕ × ℕ)).encode (m, n)) = delimit a ++ b := by
    change List.map id (delimit a ++ b) = _; simp
  have hout : List.map (Equiv.refl Bool).invFun
      ((toEncoding (α := Bool)).encode (decide (m < n))) =
      [isPolyTime_natLt_cmpBits false a b] := by
    change List.map id [decide (m < n)] = _
    rw [List.map_id, cmp_nat m n]
  have hrun : ∃ k ≤ (a.length + 1) + (a.length + 1) + (a.length + b.length + 2),
      (flip bind N.step)^[k] (some (cfg (some 0) (delimit a ++ b) [] [])) =
        some (cfg none [isPolyTime_natLt_cmpBits false a b] [] []) := by
    have h0 := run0 a b [] []
    have h1 := run1 b a.reverse []
    have h2 := run_cmp a b false
    simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h0 h1 h2
    exact rIn_trans (rIn_trans h0 h1) h2
  have hlen : ((toEncoding (α := ℕ × ℕ)).encode (m, n)).length = 2 * a.length + 1 + b.length := by
    change (delimit a ++ b).length = _; simp [length_delimit]
  have hb : (a.length + 1) + (a.length + 1) + (a.length + b.length + 2) ≤
      (2 * Polynomial.X + 4 : Polynomial ℕ).eval ((toEncoding (α := ℕ × ℕ)).encode (m, n)).length := by
    rw [hlen]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    omega
  rw [hin, hout]
  exact Classical.choice (by
    obtain ⟨k, hle, he⟩ := rIn_mono hrun hb
    rw [← init_eq, ← halt_eq] at he
    exact ⟨⟨⟨k, he⟩, hle⟩⟩)

end OMA.PolyTimeLib

namespace OMA.PolyTimeLib

open ComplexityTheory BitstringEncoding

variable {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]

theorem isPolyTime_fst : IsPolyTime (Prod.fst : α × β → α) :=
  OMA.R_ComplexityTheory_P_eq_BPP_R1.comp_fst (γ := β) id isPolyTime_id

theorem isPolyTime_comp' {f : α → β} {g : β → γ} (hg : IsPolyTime g) (hf : IsPolyTime f) :
    IsPolyTime (fun x => g (f x)) := isPolyTime_comp hf hg

theorem isPolyTime_prodMap_left {f : α → γ} (hf : IsPolyTime f) :
    IsPolyTime (fun p : α × β => (f p.1, p.2)) := by
  have h := isPolyTime_comp' (isPolyTime_swap (α := β) (β := γ))
    (isPolyTime_comp' (isPolyTime_prodMap_right (α := β) hf) (isPolyTime_swap (α := α) (β := β)))
  exact h

theorem isPolyTime_pair {f : α → β} {g : α → γ} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => (f x, g x)) := by
  have h := isPolyTime_comp' (isPolyTime_prodMap_left (β := γ) hf)
    (isPolyTime_comp' (isPolyTime_prodMap_right (α := α) hg) (isPolyTime_dup (α := α)))
  exact h

theorem isPolyTime_ite {c : α → Bool} {f g : α → β} (hc : IsPolyTime c) (hf : IsPolyTime f)
    (hg : IsPolyTime g) : IsPolyTime (fun x => if c x then f x else g x) :=
  isPolyTime_comp' (isPolyTime_select (β := β)) (isPolyTime_pair hc (isPolyTime_pair hf hg))

theorem isPolyTime_unaryPoly (q : Polynomial ℕ) :
    IsPolyTime (fun x : List Bool => List.replicate (q.eval x.length) false) := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    simp only [Polynomial.eval_add]
    simpa using isPolyTime_comp' isPolyTime_unaryAdd (isPolyTime_pair hp hr)
  | monomial k a =>
    simp only [Polynomial.eval_monomial]
    induction k with
    | zero => simpa using isPolyTime_const (α := List Bool) (List.replicate a false)
    | succ k ih =>
      have h := isPolyTime_comp' isPolyTime_unaryMul (isPolyTime_pair ih isPolyTime_unaryLen)
      simpa [pow_succ, mul_assoc] using h

/- ## Assembly of H2 -/

lemma length_encodePosNum_succ (p : PosNum) :
    (Computability.encodePosNum (PosNum.succ p)).length ≤
      (Computability.encodePosNum p).length + 1 := by
  induction p with
  | one => simp [PosNum.succ, Computability.encodePosNum]
  | bit0 p _ => simp [PosNum.succ, Computability.encodePosNum]
  | bit1 p ih => simp [PosNum.succ, Computability.encodePosNum]; omega

lemma length_encodeNat_succ (n : ℕ) :
    (Computability.encodeNat (n + 1)).length ≤ (Computability.encodeNat n).length + 1 := by
  unfold Computability.encodeNat
  have : ((n + 1 : ℕ) : Num) = Num.succ (n : Num) := by
    apply Num.to_nat_inj.1; simp [Num.cast_succ]
  rw [this]
  cases h : (n : Num) with
  | zero => simp [Num.succ, Num.succ', Computability.encodeNum, Computability.encodePosNum]
  | pos p =>
    simpa [Num.succ, Num.succ', Computability.encodeNum] using length_encodePosNum_succ p

theorem h2 : OMA.R_ComplexityTheory_P_eq_BPP_R1.H2 := by
  intro q R G hR hG
  let F : List Bool × ℕ → Bool := fun p => R (p.1, G (List.replicate p.1.length false, p.2))
  have hF : IsPolyTime F :=
    isPolyTime_comp' hR (isPolyTime_pair isPolyTime_fst
      (isPolyTime_comp' hG (isPolyTime_prodMap_left isPolyTime_unaryLen)))
  let step : List Bool × (ℕ × ℕ) → List Bool × (ℕ × ℕ) := fun s =>
    (s.1, (s.2.1 + 1, if F (s.1, s.2.1) then s.2.2 + 1 else s.2.2))
  have hstep : IsPolyTime step := by
    refine isPolyTime_pair isPolyTime_fst (isPolyTime_pair ?_ ?_)
    · exact isPolyTime_comp' isPolyTime_natSucc
        (isPolyTime_comp' isPolyTime_fst isPolyTime_snd)
    · exact isPolyTime_ite
        (isPolyTime_comp' hF (isPolyTime_pair isPolyTime_fst
          (isPolyTime_comp' isPolyTime_fst isPolyTime_snd)))
        (isPolyTime_comp' isPolyTime_natSucc (isPolyTime_comp' isPolyTime_snd isPolyTime_snd))
        (isPolyTime_comp' isPolyTime_snd isPolyTime_snd)
  have hsize : ∀ s, (bitEncode (step s)).length ≤ (bitEncode s).length + 4 := by
    rintro ⟨x, i, c⟩
    have h1 := length_encodeNat_succ i
    have h2 := length_encodeNat_succ c
    change (delimit (bitEncode x) ++ (delimit (Computability.encodeNat (i + 1)) ++
        Computability.encodeNat (if F (x, i) then c + 1 else c))).length ≤
      (delimit (bitEncode x) ++ (delimit (Computability.encodeNat i) ++
        Computability.encodeNat c)).length + 4
    split <;> simp only [List.length_append, length_delimit] <;> omega
  have hiter := isPolyTime_iterate step hstep 4 hsize
  have hrun : ∀ (x : List Bool) (k : ℕ), step^[k] (x, (0, 0)) =
      (x, (k, ((Finset.range k).filter fun i => F (x, i) = true).card)) := by
    intro x k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Finset.range_add_one, Finset.filter_insert]
      simp only [step]
      split
      · rw [Finset.card_insert_of_notMem (by simp)]
      · rfl
  have hinit : IsPolyTime (fun x : List Bool =>
      ((x, ((0 : ℕ), (0 : ℕ))), List.replicate (q.eval x.length) false)) :=
    isPolyTime_pair (isPolyTime_pair isPolyTime_id (isPolyTime_const _)) (isPolyTime_unaryPoly q)
  have hfinal : IsPolyTime (fun s : List Bool × (ℕ × ℕ) => decide (s.2.1 < 2 * s.2.2)) :=
    isPolyTime_comp' isPolyTime_natLt (isPolyTime_pair
      (isPolyTime_comp' isPolyTime_fst isPolyTime_snd)
      (isPolyTime_comp' isPolyTime_natDouble (isPolyTime_comp' isPolyTime_snd isPolyTime_snd)))
  have hall := isPolyTime_comp' hfinal (isPolyTime_comp' hiter hinit)
  convert hall using 1
  funext x
  simp only [List.length_replicate, hrun, F]

end OMA.PolyTimeLib

theorem OMA.solution : OMA.R_ComplexityTheory_P_eq_BPP_R1.H2 := OMA.PolyTimeLib.h2
