import OMAReductions.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1
-- Step Erdos78.erdos_78.variants.strongly_explicit.R1.H1.R1.H2: hypothesis H2 of reduction
-- Erdos78.erdos_78.variants.strongly_explicit.R1.H1.R1
-- Credit: @adammcarter
-- H2: the adjacency rule of the Paley graph over F_13[x]/(x^m - 2), on 0/1 polynomials, is
-- computable in polynomial time. Proof in five parts:
--   1. composition of poly-time maps (hand-built machine);
--   2. shared list-level definitions (coefficient lists, Horner product, norm);
--   3. a machine that turns (n, u, v) into the interleaved first m bits of u and v;
--   4. a machine that computes the norm down to F_13 by repeated Horner products and answers
--      whether it is a square;
--   5. algebra: x^m - 2 is irreducible, the quotient is a field with 13^m elements, and the
--      Euler criterion turns the square test into the norm computation of part 4.

section PartComp

open ComplexityTheory
open Turing Computability

namespace Erdos78Comp

/-! Reachability of a configuration within a step budget, as a Prop. -/

def RIn {σ : Type} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Prop :=
  ∃ n ≤ m, (flip bind f)^[n] (some a) = b

lemma RIn.single {σ : Type} {f : σ → Option σ} {a b : σ} (h : f a = some b) :
    RIn f a (some b) 1 :=
  ⟨1, le_rfl, h⟩

lemma RIn.trans {σ : Type} {f : σ → Option σ} {a b : σ} {c : Option σ} {m₁ m₂ : ℕ}
    (h₁ : RIn f a (some b) m₁) (h₂ : RIn f b c m₂) : RIn f a c (m₁ + m₂) := by
  obtain ⟨n₁, hn₁, e₁⟩ := h₁
  obtain ⟨n₂, hn₂, e₂⟩ := h₂
  refine ⟨n₂ + n₁, by omega, ?_⟩
  rw [Function.iterate_add_apply, e₁, e₂]

lemma RIn.mono {σ : Type} {f : σ → Option σ} {a : σ} {b : Option σ} {m m' : ℕ}
    (h : RIn f a b m) (hm : m ≤ m') : RIn f a b m' := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨n, hn.trans hm, e⟩

lemma eval_mono (q : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : q.eval a ≤ q.eval b := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; exact Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

lemma iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-! Growth of stacks: one step pushes at most a bounded number of symbols. -/

def pushCount {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushCount q + 1
  | .peek _ _ q => pushCount q
  | .pop _ _ q => pushCount q
  | .load _ q => pushCount q
  | .branch _ q₁ q₂ => pushCount q₁ + pushCount q₂
  | .goto _ => 0
  | .halt => 0

lemma stepAux_len {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushCount q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux, pushCount]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      simp only [Function.update_self, List.length_cons]
      omega
    · rw [Function.update_of_ne h]
      omega
  | peek k' f q ih =>
    simp only [TM2.stepAux, pushCount]
    exact ih _ _
  | pop k' f q ih =>
    simp only [TM2.stepAux, pushCount]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      simp only [Function.update_self, List.length_tail]
      omega
    · rw [Function.update_of_ne h]
  | load a q ih =>
    simp only [TM2.stepAux, pushCount]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, pushCount]
    cases f v
    · exact (ih₂ v S).trans (by omega)
    · exact (ih₁ v S).trans (by omega)
  | goto f => simp [TM2.stepAux, pushCount]
  | halt => simp [TM2.stepAux, pushCount]

lemma exists_pushBound (M : FinTM2) : ∃ B : ℕ, ∀ l, pushCount (M.m l) ≤ B := by
  let _ : Fintype M.Λ := M.ΛFin
  exact ⟨Finset.univ.sup (fun l => pushCount (M.m l)),
    fun l => Finset.le_sup (f := fun l => pushCount (M.m l)) (Finset.mem_univ l)⟩

lemma step_len (M : FinTM2) {B : ℕ} (hB : ∀ l, pushCount (M.m l) ≤ B)
    {c c' : TM2.Cfg M.Γ M.Λ M.σ} (h : M.step c = some c') (k : M.K) :
    (c'.stk k).length ≤ (c.stk k).length + B := by
  rcases c with ⟨_ | l, v, S⟩
  · exact absurd h (by simp [FinTM2.step, TM2.step])
  · have h' : some (TM2.stepAux (M.m l) v S) = some c' := h
    injection h' with h'
    subst h'
    exact (stepAux_len (M.m l) v S k).trans (Nat.add_le_add_left (hB l) _)

lemma iterate_len (M : FinTM2) {B : ℕ} (hB : ∀ l, pushCount (M.m l) ≤ B) (n : ℕ)
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : (flip bind M.step)^[n] (some c) = some c') (k : M.K) :
    (c'.stk k).length ≤ (c.stk k).length + n * B := by
  induction n generalizing c with
  | zero =>
    have h' : some c = some c' := h
    injection h' with h'
    subst h'
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    change (flip bind M.step)^[n] (M.step c) = some c' at h
    cases hs : M.step c with
    | none =>
      rw [hs, iterate_none] at h
      exact absurd h (by simp)
    | some c₁ =>
      rw [hs] at h
      have h1 := ih c₁ h
      have h2 := step_len M hB hs k
      rw [Nat.succ_mul]
      omega

lemma initList_stk_len (M : FinTM2) (s : List (M.Γ M.k₀)) (k : M.K) :
    ((initList M s).stk k).length ≤ s.length := by
  by_cases h : k = M.k₀
  · subst h
    simp [initList]
  · simp [initList, h]

lemma haltList_stk_self (M : FinTM2) (s : List (M.Γ M.k₁)) :
    (haltList M s).stk M.k₁ = s := by
  simp [haltList]

lemma haltList_stk_update (M : FinTM2) (s : List (M.Γ M.k₁)) :
    Function.update (haltList M s).stk M.k₁ [] = fun _ => [] := by
  funext k
  by_cases h : k = M.k₁
  · subst h
    simp
  · simp [haltList, h]

lemma out_len (M : FinTM2) {B : ℕ} (hB : ∀ l, pushCount (M.m l) ≤ B)
    {s : List (M.Γ M.k₀)} {out : List (M.Γ M.k₁)} {T : ℕ}
    (h : TM2OutputsInTime M s (some out) T) : out.length ≤ s.length + T * B := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  have h1 := iterate_len M hB n (initList M s) (haltList M out) hn M.k₁
  rw [haltList_stk_self] at h1
  have h2 := initList_stk_len M s M.k₁
  have h3 : n * B ≤ T * B := Nat.mul_le_mul_right B hle
  omega

/-! The composed machine. Stacks: the stacks of M, the stacks of N and one helper stack. -/

variable (M N : FinTM2) (eo : M.Γ M.k₁ ≃ Bool) (ei : N.Γ N.k₀ ≃ Bool)

abbrev KK : Type := M.K ⊕ (N.K ⊕ Unit)

abbrev LL : Type := M.Λ ⊕ (N.Λ ⊕ Bool)

abbrev VV : Type := M.σ × N.σ × Option Bool

abbrev GG : KK M N → Type := fun k =>
  Sum.casesOn (motive := fun _ => Type) k M.Γ
    (fun k' => Sum.casesOn (motive := fun _ => Type) k' N.Γ (fun _ => Bool))

def liftM : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (GG M N) (LL M N) (VV M N)
  | .push k f q => .push (Sum.inl k) (fun v => f v.1) (liftM q)
  | .peek k f q => .peek (Sum.inl k) (fun v o => (f v.1 o, v.2)) (liftM q)
  | .pop k f q => .pop (Sum.inl k) (fun v o => (f v.1 o, v.2)) (liftM q)
  | .load a q => .load (fun v => (a v.1, v.2)) (liftM q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (liftM q₁) (liftM q₂)
  | .goto f => .goto (fun v => Sum.inl (f v.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr false))

def liftN : TM2.Stmt N.Γ N.Λ N.σ → TM2.Stmt (GG M N) (LL M N) (VV M N)
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun v => f v.2.1) (liftN q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftN q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftN q)
  | .load a q => .load (fun v => (v.1, a v.2.1, v.2.2)) (liftN q)
  | .branch f q₁ q₂ => .branch (fun v => f v.2.1) (liftN q₁) (liftN q₂)
  | .goto f => .goto (fun v => Sum.inr (Sum.inl (f v.2.1)))
  | .halt => .halt

def prog : LL M N → TM2.Stmt (GG M N) (LL M N) (VV M N)
  | Sum.inl l => liftM M N (M.m l)
  | Sum.inr (Sum.inl l) => liftN M N (N.m l)
  | Sum.inr (Sum.inr false) =>
    .pop (Sum.inl M.k₁) (fun v (o : Option (M.Γ M.k₁)) => (v.1, v.2.1, o.map eo)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inr (Sum.inr ())) (fun v => v.2.2.getD false) <|
          .goto fun _ => Sum.inr (Sum.inr false))
        (.goto fun _ => Sum.inr (Sum.inr true))
  | Sum.inr (Sum.inr true) =>
    .pop (Sum.inr (Sum.inr ())) (fun v (o : Option Bool) => (v.1, v.2.1, o)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inr (Sum.inl N.k₀)) (fun v => ei.symm (v.2.2.getD false)) <|
          .goto fun _ => Sum.inr (Sum.inr true))
        (.goto fun _ => Sum.inr (Sum.inl N.main))

def Cmp : FinTM2 :=
  letI := M.kFin
  letI := N.kFin
  letI := M.ΛFin
  letI := N.ΛFin
  letI := M.σFin
  letI := N.σFin
  { K := KK M N
    k₀ := Sum.inl M.k₀
    k₁ := Sum.inr (Sum.inl N.k₁)
    Γ := GG M N
    Λ := LL M N
    main := Sum.inl M.main
    σ := VV M N
    initialState := (M.initialState, N.initialState, none)
    Γk₀Fin := M.Γk₀Fin
    m := prog M N eo ei }

def mk (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool) :
    ∀ k : KK M N, List (GG M N k)
  | Sum.inl k => SM k
  | Sum.inr (Sum.inl k) => SN k
  | Sum.inr (Sum.inr _) => a

variable {M N} {eo} {ei}

lemma upd_M (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool) (k : M.K)
    (v : List (GG M N (Sum.inl k))) :
    Function.update (mk M N SM SN a) (Sum.inl k) v = mk M N (Function.update SM k v) SN a := by
  funext k'
  rcases k' with k' | k' | k'
  · by_cases h : k' = k
    · subst h
      simp [Function.update, mk]
    · simp [Function.update, mk, h]
  · simp [Function.update, mk]
  · simp [Function.update, mk]

lemma upd_N (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool) (k : N.K)
    (v : List (GG M N (Sum.inr (Sum.inl k)))) :
    Function.update (mk M N SM SN a) (Sum.inr (Sum.inl k)) v =
      mk M N SM (Function.update SN k v) a := by
  funext k'
  rcases k' with k' | k' | k'
  · simp [Function.update, mk]
  · by_cases h : k' = k
    · subst h
      simp [Function.update, mk]
    · simp [Function.update, mk, h]
  · simp [Function.update, mk]

lemma upd_A (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool)
    (v : List (GG M N (Sum.inr (Sum.inr ())))) :
    Function.update (mk M N SM SN a) (Sum.inr (Sum.inr ())) v = mk M N SM SN v := by
  funext k'
  rcases k' with k' | k' | k'
  · simp [Function.update, mk]
  · simp [Function.update, mk]
  · simp [Function.update, mk]

lemma mk_nil : mk M N (fun _ => []) (fun _ => []) [] = fun _ => [] := by
  funext k
  rcases k with k | k | k <;> rfl

def liftCfgM (c : TM2.Cfg M.Γ M.Λ M.σ) : (Cmp M N eo ei).Cfg :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr false)) Sum.inl), (c.var, N.initialState, none),
    mk M N c.stk (fun _ => []) []⟩

def liftCfgN (c : TM2.Cfg N.Γ N.Λ N.σ) : (Cmp M N eo ei).Cfg :=
  ⟨c.l.map (fun l => Sum.inr (Sum.inl l)), (M.initialState, c.var, none),
    mk M N (fun _ => []) c.stk []⟩

def cfg (b : Bool) (o : Option Bool) (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k))
    (a : List Bool) : (Cmp M N eo ei).Cfg :=
  ⟨some (Sum.inr (Sum.inr b)), (M.initialState, N.initialState, o), mk M N SM SN a⟩

/-! Simulation of the first machine. -/

lemma stepAux_liftM (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (liftM M N q) (v, N.initialState, none) (mk M N S (fun _ => []) []) =
      liftCfgM (eo := eo) (ei := ei) (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [liftM, TM2.stepAux]
    rw [upd_M]
    exact ih _ _
  | peek k f q ih =>
    simp only [liftM, TM2.stepAux]
    exact ih _ _
  | pop k f q ih =>
    simp only [liftM, TM2.stepAux]
    rw [upd_M]
    exact ih _ _
  | load a q ih =>
    simp only [liftM, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [liftM, TM2.stepAux, ih₁, ih₂]
    cases f v <;> rfl
  | goto f => rfl
  | halt => rfl

lemma step_liftM {c c' : TM2.Cfg M.Γ M.Λ M.σ} (h : M.step c = some c') :
    (Cmp M N eo ei).step (liftCfgM c) = some (liftCfgM c') := by
  rcases c with ⟨_ | l, v, S⟩
  · exact absurd h (by simp [FinTM2.step, TM2.step])
  · have h' : some (TM2.stepAux (M.m l) v S) = some c' := h
    injection h' with h'
    subst h'
    show some (TM2.stepAux (liftM M N (M.m l)) (v, N.initialState, none)
      (mk M N S (fun _ => []) [])) = _
    exact congrArg some (stepAux_liftM (eo := eo) (ei := ei) (M.m l) v S)

lemma iterate_liftM (n : ℕ) (c c' : TM2.Cfg M.Γ M.Λ M.σ)
    (h : (flip bind M.step)^[n] (some c) = some c') :
    (flip bind (Cmp M N eo ei).step)^[n] (some (liftCfgM c)) = some (liftCfgM c') := by
  induction n generalizing c with
  | zero =>
    have h' : some c = some c' := h
    injection h' with h'
    subst h'
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    change (flip bind M.step)^[n] (M.step c) = some c' at h
    change (flip bind (Cmp M N eo ei).step)^[n] ((Cmp M N eo ei).step (liftCfgM c)) = _
    cases hs : M.step c with
    | none =>
      rw [hs, iterate_none] at h
      exact absurd h (by simp)
    | some c₁ =>
      rw [hs] at h
      rw [step_liftM hs]
      exact ih c₁ h

/-! Simulation of the second machine. -/

lemma stepAux_liftN (q : TM2.Stmt N.Γ N.Λ N.σ) (v : N.σ) (S : ∀ k, List (N.Γ k)) :
    TM2.stepAux (liftN M N q) (M.initialState, v, none) (mk M N (fun _ => []) S []) =
      liftCfgN (eo := eo) (ei := ei) (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [liftN, TM2.stepAux]
    rw [upd_N]
    exact ih _ _
  | peek k f q ih =>
    simp only [liftN, TM2.stepAux]
    exact ih _ _
  | pop k f q ih =>
    simp only [liftN, TM2.stepAux]
    rw [upd_N]
    exact ih _ _
  | load a q ih =>
    simp only [liftN, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [liftN, TM2.stepAux, ih₁, ih₂]
    cases f v <;> rfl
  | goto f => rfl
  | halt => rfl

lemma step_liftN (c : TM2.Cfg N.Γ N.Λ N.σ) :
    (Cmp M N eo ei).step (liftCfgN c) = (N.step c).map liftCfgN := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · show some (TM2.stepAux (liftN M N (N.m l)) (M.initialState, v, none)
      (mk M N (fun _ => []) S [])) = _
    rw [stepAux_liftN]
    rfl

lemma iterate_liftN (n : ℕ) (o : Option (TM2.Cfg N.Γ N.Λ N.σ)) :
    (flip bind (Cmp M N eo ei).step)^[n] (o.map liftCfgN) =
      ((flip bind N.step)^[n] o).map liftCfgN := by
  have hs : Function.Semiconj (Option.map (liftCfgN (M := M) (N := N) (eo := eo) (ei := ei)))
      (flip bind N.step) (flip bind (Cmp M N eo ei).step) := by
    intro o
    rcases o with _ | c
    · rfl
    · show (N.step c).map liftCfgN = (Cmp M N eo ei).step (liftCfgN c)
      rw [step_liftN]
  exact ((hs.iterate_right n) o).symm

/-! One step of each transfer phase. -/

lemma step_mv1_cons (o : Option Bool) (c : M.Γ M.k₁) (s : List (M.Γ M.k₁))
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool)
    (h : SM M.k₁ = c :: s) :
    (Cmp M N eo ei).step (cfg false o SM SN a) =
      some (cfg false (some (eo c)) (Function.update SM M.k₁ s) SN (eo c :: a)) := by
  show some (TM2.stepAux (prog M N eo ei (Sum.inr (Sum.inr false)))
    (M.initialState, N.initialState, o) (mk M N SM SN a)) = _
  simp [prog, TM2.stepAux, mk, upd_M, upd_A, cfg, h]
  rfl

lemma step_mv1_nil (o : Option Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool)
    (h : SM M.k₁ = []) :
    (Cmp M N eo ei).step (cfg false o SM SN a) =
      some (cfg true none (Function.update SM M.k₁ []) SN a) := by
  show some (TM2.stepAux (prog M N eo ei (Sum.inr (Sum.inr false)))
    (M.initialState, N.initialState, o) (mk M N SM SN a)) = _
  simp [prog, TM2.stepAux, mk, upd_M, upd_A, cfg, h]
  rfl

lemma step_mv2_cons (o : Option Bool) (c : Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool) :
    (Cmp M N eo ei).step (cfg true o SM SN (c :: a)) =
      some (cfg true (some c) SM (Function.update SN N.k₀ (ei.symm c :: SN N.k₀)) a) := by
  show some (TM2.stepAux (prog M N eo ei (Sum.inr (Sum.inr true)))
    (M.initialState, N.initialState, o) (mk M N SM SN (c :: a))) = _
  simp [prog, TM2.stepAux, mk, upd_N, upd_A, cfg]
  rfl

lemma step_mv2_nil (o : Option Bool) (SN : ∀ k, List (N.Γ k)) :
    (Cmp M N eo ei).step (cfg true o (fun _ => []) SN []) =
      some (liftCfgN ⟨some N.main, N.initialState, SN⟩) := by
  show some (TM2.stepAux (prog M N eo ei (Sum.inr (Sum.inr true)))
    (M.initialState, N.initialState, o) (mk M N (fun _ => []) SN [])) = _
  simp [prog, TM2.stepAux, mk, upd_N, upd_A, liftCfgN]
  rfl

/-! The two transfer phases. -/

lemma mv1_run (s : List (M.Γ M.k₁)) (o : Option Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool) (h : SM M.k₁ = s) :
    RIn (Cmp M N eo ei).step (cfg false o SM SN a)
      (some (cfg true none (Function.update SM M.k₁ []) SN ((s.map eo).reverse ++ a)))
      (s.length + 1) := by
  induction s generalizing o SM a with
  | nil => exact RIn.single (step_mv1_nil o SM SN a h)
  | cons c s ih =>
    have h1 := RIn.single (step_mv1_cons (eo := eo) (ei := ei) o c s SM SN a h)
    have h2 := ih (some (eo c)) (Function.update SM M.k₁ s) (eo c :: a)
      (Function.update_self _ _ _)
    have := RIn.trans h1 h2
    simp only [Function.update_idem] at this
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

lemma mv2_run (a : List Bool) (o : Option Bool) (SN : ∀ k, List (N.Γ k)) :
    RIn (Cmp M N eo ei).step (cfg true o (fun _ => []) SN a)
      (some (liftCfgN ⟨some N.main, N.initialState,
        Function.update SN N.k₀ ((a.map ei.symm).reverse ++ SN N.k₀)⟩))
      (a.length + 1) := by
  induction a generalizing o SN with
  | nil =>
    simp only [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
    exact RIn.single (step_mv2_nil o SN)
  | cons c a ih =>
    have := RIn.trans (RIn.single (step_mv2_cons (eo := eo) (ei := ei) o c (fun _ => []) SN a))
      (ih (some c) _)
    simp only [Function.update_self, Function.update_idem] at this
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

/-! Initial and final configurations. -/

lemma initList_stk (M : FinTM2) (s : List (M.Γ M.k₀)) :
    (initList M s).stk = Function.update (fun _ => []) M.k₀ s := by
  funext k
  by_cases h : k = M.k₀
  · subst h
    simp [initList]
  · simp [initList, h]

lemma initList_Cmp (s : List (M.Γ M.k₀)) :
    initList (Cmp M N eo ei) s = liftCfgM (initList M s) := by
  simp only [initList, liftCfgM]
  congr 1
  funext k
  rcases k with k | k | k
  · by_cases h : k = M.k₀
    · subst h
      simp [mk]
      split
      · rfl
      · rename_i hne
        exact absurd rfl hne
    · simp [mk, h]
      split
      · rename_i heq
        exact absurd (Sum.inl_injective (heq : (Sum.inl k : KK M N) = Sum.inl M.k₀)) h
      · rfl
  · rfl
  · rfl

lemma initList_N (s : List (N.Γ N.k₀)) :
    liftCfgN (eo := eo) (ei := ei)
      ⟨some N.main, N.initialState, Function.update (fun _ => []) N.k₀ s⟩ =
      liftCfgN (eo := eo) (ei := ei) (initList N s) := by
  have : (initList N s) = ⟨some N.main, N.initialState, (initList N s).stk⟩ := rfl
  rw [this, initList_stk]

lemma haltList_Cmp (s : List (N.Γ N.k₁)) :
    liftCfgN (eo := eo) (ei := ei) (haltList N s) = haltList (Cmp M N eo ei) s := by
  simp only [liftCfgN, haltList]
  congr 1
  funext k
  rcases k with k | k | k
  · rfl
  · by_cases h : k = N.k₁
    · subst h
      simp [mk]
      split
      · rfl
      · rename_i hne
        exact absurd rfl hne
    · simp [mk, h]
      split
      · rename_i heq
        exact absurd (Sum.inl_injective (Sum.inr_injective
          (heq : (Sum.inr (Sum.inl k) : KK M N) = Sum.inr (Sum.inl N.k₁)))) h
      · rfl
  · rfl

lemma run_M {s : List (M.Γ M.k₀)} {out : List (M.Γ M.k₁)} {T : ℕ}
    (h : TM2OutputsInTime M s (some out) T) :
    RIn (Cmp M N eo ei).step (initList (Cmp M N eo ei) s)
      (some (cfg false none (haltList M out).stk (fun _ => []) [])) T := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  refine ⟨n, hle, ?_⟩
  rw [initList_Cmp]
  exact iterate_liftM n (initList M s) (haltList M out) hn

lemma run_N {s : List (N.Γ N.k₀)} {out : List (N.Γ N.k₁)} {T : ℕ}
    (h : TM2OutputsInTime N s (some out) T) :
    RIn (Cmp M N eo ei).step (liftCfgN (initList N s))
      (some (haltList (Cmp M N eo ei) out)) T := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  refine ⟨n, hle, ?_⟩
  have := iterate_liftN (M := M) (N := N) (eo := eo) (ei := ei) n (some (initList N s))
  change (flip bind (Cmp M N eo ei).step)^[n] (Option.map liftCfgN (some (initList N s))) = _
  rw [this]
  refine (congrArg (Option.map liftCfgN) hn).trans ?_
  show some (liftCfgN (haltList N out)) = _
  rw [haltList_Cmp]

lemma transfer_run (out : List (M.Γ M.k₁)) :
    RIn (Cmp M N eo ei).step (cfg false none (haltList M out).stk (fun _ => []) [])
      (some (liftCfgN (initList N (List.map ei.symm (List.map eo out)))))
      ((out.length + 1) + (out.length + 1)) := by
  have h2 := mv1_run (eo := eo) (ei := ei) out none (haltList M out).stk (fun _ => []) []
    (haltList_stk_self M out)
  rw [haltList_stk_update] at h2
  have h3 := mv2_run (M := M) (eo := eo) (ei := ei) ((out.map eo).reverse ++ []) none
    (fun _ => [])
  have hcfg : (List.map ei.symm ((out.map eo).reverse ++ [])).reverse ++ [] =
      List.map ei.symm (List.map eo out) := by
    simp [List.map_reverse]
  rw [hcfg, initList_N] at h3
  have hlen : ((out.map eo).reverse ++ []).length = out.length := by simp
  rw [hlen] at h3
  exact h2.trans h3

/-- Composition of two machines: the composed machine computes the composite within the
sum of the time budgets. -/
lemma comp_run {s : List (M.Γ M.k₀)} {mid : List Bool} {out : List (N.Γ N.k₁)} {T₁ T₂ : ℕ}
    (h₁ : TM2OutputsInTime M s (some (List.map eo.symm mid)) T₁)
    (h₂ : TM2OutputsInTime N (List.map ei.symm mid) (some out) T₂) :
    RIn (Cmp M N eo ei).step (initList (Cmp M N eo ei) s)
      (some (haltList (Cmp M N eo ei) out))
      (T₁ + ((mid.length + 1) + (mid.length + 1)) + T₂) := by
  have a1 := run_M (N := N) (eo := eo) (ei := ei) h₁
  have a2 := transfer_run (M := M) (N := N) (eo := eo) (ei := ei) (List.map eo.symm mid)
  have a3 := run_N (M := M) (eo := eo) (ei := ei) h₂
  have hmid : List.map eo (List.map eo.symm mid) = mid := by simp
  have hlen : (List.map eo.symm mid).length = mid.length := by simp
  rw [hmid, hlen] at a2
  exact (a1.trans a2).trans a3

end Erdos78Comp

open Erdos78Comp in
/-- Polynomial-time computable functions are closed under composition. -/
theorem Erdos78Comp.comp_polyTime {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] (f : α → β) (g : β → γ) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (g ∘ f) := by
  obtain ⟨M⟩ := hf
  obtain ⟨N⟩ := hg
  obtain ⟨B, hB⟩ := exists_pushBound M.tm
  refine ⟨{ tm := Cmp M.tm N.tm M.outputAlphabet N.inputAlphabet
            inputAlphabet := M.inputAlphabet
            outputAlphabet := N.outputAlphabet
            time := M.time + Polynomial.C 2 * (Polynomial.X + M.time * Polynomial.C B + 1) +
              N.time.comp (Polynomial.X + M.time * Polynomial.C B)
            outputsFun := fun a => ?_ }⟩
  have hM := M.outputsFun a
  have hN := N.outputsFun (f a)
  set x := (BitstringEncoding.toEncoding (α := α)).encode a with hx
  set y := (BitstringEncoding.toEncoding (α := β)).encode (f a) with hy
  have hlen : y.length ≤ x.length + M.time.eval x.length * B := by
    have := out_len M.tm hB hM
    simpa using this
  have hrun := comp_run (M := M.tm) (N := N.tm) (eo := M.outputAlphabet)
    (ei := N.inputAlphabet) (mid := y) hM hN
  have hb : M.time.eval x.length + ((y.length + 1) + (y.length + 1)) + N.time.eval y.length ≤
      (M.time + Polynomial.C 2 * (Polynomial.X + M.time * Polynomial.C B + 1) +
        N.time.comp (Polynomial.X + M.time * Polynomial.C B)).eval x.length := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_comp]
    have := eval_mono N.time hlen
    generalize M.time.eval x.length * B = W at *
    omega
  exact Classical.choice (by
    obtain ⟨n, hle, he⟩ := hrun.mono hb
    exact ⟨⟨⟨n, he⟩, hle⟩⟩)

/-- The composition fact used in the reduction of Erdos problem 78 (strongly explicit variant). -/
theorem erdos78_comp_polyTime (f : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (g : ℕ × ℕ × ℕ → Bool)
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (g ∘ f) :=
  Erdos78Comp.comp_polyTime f g hf hg

end PartComp

section PartSpec

open ComplexityTheory

-- Shared definitions for the poly-time half of the Paley split of Erdos 78 (strongly explicit).
-- Field elements of F_13[x]/(x^m - 2) are lists of m coefficients, constant term first.

namespace Erdos78Paley

abbrev F : Type := ZMod 13

def bF (b : Bool) : F := if b then 1 else 0

/-- Decode a bit list, two bits per coefficient: (a, b) is the coefficient bF a - bF b. -/
def dec : List Bool → List F
  | a :: b :: rest => (bF a - bF b) :: dec rest
  | _ => []

/-- Multiply by x modulo x^m - 2: the top coefficient wraps around with a factor 2. -/
def mulX (a : List F) : List F :=
  match a.getLast? with
  | none => []
  | some t => (2 * t) :: a.dropLast

/-- One Horner step: acc * x + c * b. -/
def hstep (b acc : List F) (c : F) : List F :=
  List.zipWith (fun r s => r + c * s) (mulX acc) b

/-- Product a * b modulo x^m - 2 (m is the length of b). -/
def mul (a b : List F) : List F :=
  a.foldr (fun c acc => hstep b acc c) (List.replicate b.length 0)

def one : ℕ → List F
  | 0 => []
  | m + 1 => 1 :: List.replicate m 0

/-- y maps to y^13 * w. -/
def frob (w y : List F) : List F := (fun z => mul z y)^[13] w

/-- w ^ (1 + 13 + ... + 13^(m-1)), the norm of w down to F_13. -/
def normL (w : List F) : List F := (frob w)^[w.length] (one w.length)

def isSq (c : F) : Bool := decide (c = 0 ∨ c ^ 6 = 1)

def evalFn (l : List Bool) : Bool := isSq ((normL (dec l)).headD 0)

/-- Intermediate data: a raw bit string. -/
structure Mid where
  bits : List Bool

instance : BitstringEncoding Mid where
  encode x := x.bits
  decode l := some ⟨l⟩
  decode_encode _ := rfl

/-- First half: from (n, u, v) to the interleaved first m bits of u and v, m = 3 ^ clog 3 (size n). -/
def setupFn (p : ℕ × ℕ × ℕ) : Mid :=
  ⟨(List.range (3 ^ Nat.clog 3 (Nat.size p.1))).flatMap
    (fun i => [p.2.1.testBit i, p.2.2.testBit i])⟩

/-- Second half: quadratic character of the encoded field element. -/
def evalMid (x : Mid) : Bool := evalFn x.bits

end Erdos78Paley

end PartSpec

section PartSetup

open ComplexityTheory
open Turing Computability

-- Poly-time fact for the Paley split of Erdos 78: the map from (n, u, v) to the interleaved
-- first m bits of u and v, with m = 3 ^ clog 3 (size n), is computable in polynomial time.
-- The machine is built by hand. Six stacks over Bool:
--   inp (input and output), mk1 and mk2 (unary marks), u1 and u2 (the bits of u), acc (output).
-- Phase one computes m in unary on mk1 by repeated tripling while eating the n block.
-- Phase two moves the bits of u to u2. Phase three weaves the bits of u and v on acc.
-- Phase four clears the leftovers and pours acc back to inp.

namespace Erdos78Paley

namespace Setup

-- Reachability of a configuration within a step budget, as a Prop.

def RIn {σ : Type} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Prop :=
  ∃ n ≤ m, (flip bind f)^[n] (some a) = b

lemma RIn.single {σ : Type} {f : σ → Option σ} {a b : σ} (h : f a = some b) :
    RIn f a (some b) 1 :=
  ⟨1, le_rfl, h⟩

lemma RIn.trans {σ : Type} {f : σ → Option σ} {a b : σ} {c : Option σ} {m₁ m₂ : ℕ}
    (h₁ : RIn f a (some b) m₁) (h₂ : RIn f b c m₂) : RIn f a c (m₁ + m₂) := by
  obtain ⟨n₁, hn₁, e₁⟩ := h₁
  obtain ⟨n₂, hn₂, e₂⟩ := h₂
  refine ⟨n₂ + n₁, by omega, ?_⟩
  rw [Function.iterate_add_apply, e₁, e₂]

lemma RIn.mono {σ : Type} {f : σ → Option σ} {a : σ} {b : Option σ} {m m' : ℕ}
    (h : RIn f a b m) (hm : m ≤ m') : RIn f a b m' := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨n, hn.trans hm, e⟩

-- The binary encoding of a natural number is its list of bits.

lemma encodePosNum_eq_bits (p : PosNum) : encodePosNum p = Nat.bits (p : ℕ) := by
  induction p with
  | one => simp [encodePosNum]
  | bit1 p ih =>
    rw [encodePosNum, ih, PosNum.cast_bit1, ← two_mul, Nat.bit1_bits]
  | bit0 p ih =>
    rw [encodePosNum, ih, PosNum.cast_bit0, ← two_mul,
      Nat.bit0_bits _ (PosNum.to_nat_pos p).ne']

lemma encodeNum_eq_bits (q : Num) : encodeNum q = Nat.bits (q : ℕ) := by
  cases q with
  | zero => simp [encodeNum]
  | pos p => simpa [encodeNum] using encodePosNum_eq_bits p

lemma encodeNat_eq_bits (n : ℕ) : encodeNat n = Nat.bits n := by
  rw [encodeNat, encodeNum_eq_bits, Num.to_of_nat]

-- Pure facts: the woven list, bits, and the arithmetic of the time bound.

/-- The first c bits of a and of b, interleaved, missing bits read as false. -/
def weave : ℕ → List Bool → List Bool → List Bool
  | 0, _, _ => []
  | c + 1, a, b => a.head?.getD false :: b.head?.getD false :: weave c a.tail b.tail

lemma weave_length (c : ℕ) (a b : List Bool) : (weave c a b).length = 2 * c := by
  induction c generalizing a b with
  | zero => rfl
  | succ c ih => simp [weave, ih]; omega

lemma weave_eq (c : ℕ) (a b : List Bool) :
    weave c a b = (List.range c).flatMap (fun i => [a.getD i false, b.getD i false]) := by
  induction c generalizing a b with
  | zero => simp [weave]
  | succ c ih =>
    rw [weave, ih, List.range_succ_eq_map]
    cases a <;> cases b <;> simp [List.flatMap_map]

lemma testBit_eq_getD (n i : ℕ) : n.testBit i = (Nat.bits n).getD i false := by
  rw [Nat.testBit_eq_inth, List.getI_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

lemma clog_le_self (s : ℕ) : Nat.clog 3 s ≤ s :=
  Nat.clog_le_of_le_pow (Nat.lt_pow_self (by norm_num)).le

lemma pow_clog_le (s : ℕ) : 3 ^ Nat.clog 3 s ≤ 3 * s + 1 := by
  rcases Nat.lt_or_ge 1 s with h | h
  · have h1 := Nat.pow_pred_clog_lt_self (b := 3) (by norm_num) h
    have hpos : 0 < Nat.clog 3 s := Nat.clog_pos (by norm_num) h
    obtain ⟨k, hk⟩ : ∃ k, Nat.clog 3 s = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hk] at h1 ⊢
    simp only [Nat.pred_succ] at h1
    rw [pow_succ]
    omega
  · rw [Nat.clog_of_right_le_one h]
    simp

lemma budget_le (s su sv L : ℕ) (hL : 2 * s + 2 * su + sv + 2 ≤ L) :
    Nat.clog 3 s * (5 * 3 ^ Nat.clog 3 s) + 3 * 3 ^ Nat.clog 3 s + 3 * su + sv + 8 ≤
      15 * L * L + 14 * L + 11 := by
  have hK := clog_le_self s
  have hm := pow_clog_le s
  generalize 3 ^ Nat.clog 3 s = m at *
  generalize Nat.clog 3 s = K at *
  have h1 : K * (5 * m) ≤ s * (5 * (3 * s + 1)) := Nat.mul_le_mul hK (by omega)
  have h2 : s * s ≤ L * L := Nat.mul_le_mul (by omega) (by omega)
  nlinarith [h1, h2]

-- The machine.

inductive Stk
  | inp
  | mk1
  | mk2
  | u1
  | u2
  | acc
  deriving DecidableEq

instance : Fintype Stk :=
  ⟨{Stk.inp, Stk.mk1, Stk.mk2, Stk.u1, Stk.u2, Stk.acc}, by intro x; cases x <;> simp⟩

inductive Lab
  | init
  | chk
  | tri
  | pour
  | movU
  | revU
  | emit
  | clrU
  | clrI
  | out
  deriving DecidableEq

instance : Fintype Lab :=
  ⟨{Lab.init, Lab.chk, Lab.tri, Lab.pour, Lab.movU, Lab.revU, Lab.emit, Lab.clrU, Lab.clrI,
    Lab.out}, by intro x; cases x <;> simp⟩

def prog : Lab → TM2.Stmt (fun _ : Stk => Bool) Lab (Option Bool)
  | .init =>
    .push .mk1 (fun _ => true) <|
      .peek .inp (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.pop .inp (fun _ o => o) <| .pop .inp (fun _ o => o) <|
            .load (fun _ => none) <| .goto fun _ => .chk)
          (.load (fun _ => none) <| .goto fun _ => .chk)
  | .chk =>
    .peek .inp (fun _ o => o) <|
      .branch (fun v => v == some true)
        (.load (fun _ => none) <| .goto fun _ => .tri)
        (.pop .inp (fun _ o => o) <| .load (fun _ => none) <| .goto fun _ => .movU)
  | .tri =>
    .pop .mk1 (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push .mk2 (fun _ => true) <| .push .mk2 (fun _ => true) <|
          .push .mk2 (fun _ => true) <|
            .peek .inp (fun _ o => o) <|
              .branch (fun v => v == some true)
                (.pop .inp (fun _ o => o) <| .pop .inp (fun _ o => o) <|
                  .peek .inp (fun _ o => o) <|
                    .branch (fun v => v == some true)
                      (.pop .inp (fun _ o => o) <| .pop .inp (fun _ o => o) <|
                        .load (fun _ => none) <| .goto fun _ => .tri)
                      (.load (fun _ => none) <| .goto fun _ => .tri))
                (.load (fun _ => none) <| .goto fun _ => .tri))
        (.load (fun _ => none) <| .goto fun _ => .pour)
  | .pour =>
    .pop .mk2 (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push .mk1 (fun _ => true) <| .load (fun _ => none) <| .goto fun _ => .pour)
        (.load (fun _ => none) <| .goto fun _ => .chk)
  | .movU =>
    .pop .inp (fun _ o => o) <|
      .branch (fun v => v == some true)
        (.pop .inp (fun _ o => o) <| .push .u1 (fun v => v.getD false) <|
          .load (fun _ => none) <| .goto fun _ => .movU)
        (.load (fun _ => none) <| .goto fun _ => .revU)
  | .revU =>
    .pop .u1 (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push .u2 (fun v => v.getD false) <| .load (fun _ => none) <| .goto fun _ => .revU)
        (.load (fun _ => none) <| .goto fun _ => .emit)
  | .emit =>
    .pop .mk1 (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.pop .u2 (fun _ o => o) <| .push .acc (fun v => v.getD false) <|
          .pop .inp (fun _ o => o) <| .push .acc (fun v => v.getD false) <|
            .load (fun _ => none) <| .goto fun _ => .emit)
        (.load (fun _ => none) <| .goto fun _ => .clrU)
  | .clrU =>
    .pop .u2 (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.load (fun _ => none) <| .goto fun _ => .clrU)
        (.load (fun _ => none) <| .goto fun _ => .clrI)
  | .clrI =>
    .pop .inp (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.load (fun _ => none) <| .goto fun _ => .clrI)
        (.load (fun _ => none) <| .goto fun _ => .out)
  | .out =>
    .pop .acc (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push .inp (fun v => v.getD false) <| .load (fun _ => none) <| .goto fun _ => .out)
        (.load (fun _ => none) <| .halt)

def N : FinTM2 :=
  { K := Stk
    k₀ := Stk.inp
    k₁ := Stk.inp
    Γ := fun _ => Bool
    Λ := Lab
    main := Lab.init
    σ := Option Bool
    initialState := none
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := prog }

def stk (i m1 m2 a1 a2 t : List Bool) : ∀ k : Stk, List ((fun _ : Stk => Bool) k)
  | .inp => i
  | .mk1 => m1
  | .mk2 => m2
  | .u1 => a1
  | .u2 => a2
  | .acc => t

lemma upd_inp (i m1 m2 a1 a2 t x : List Bool) :
    Function.update (stk i m1 m2 a1 a2 t) Stk.inp x = stk x m1 m2 a1 a2 t := by
  funext k
  cases k <;> simp [Function.update, stk]

lemma upd_mk1 (i m1 m2 a1 a2 t x : List Bool) :
    Function.update (stk i m1 m2 a1 a2 t) Stk.mk1 x = stk i x m2 a1 a2 t := by
  funext k
  cases k <;> simp [Function.update, stk]

lemma upd_mk2 (i m1 m2 a1 a2 t x : List Bool) :
    Function.update (stk i m1 m2 a1 a2 t) Stk.mk2 x = stk i m1 x a1 a2 t := by
  funext k
  cases k <;> simp [Function.update, stk]

lemma upd_u1 (i m1 m2 a1 a2 t x : List Bool) :
    Function.update (stk i m1 m2 a1 a2 t) Stk.u1 x = stk i m1 m2 x a2 t := by
  funext k
  cases k <;> simp [Function.update, stk]

lemma upd_u2 (i m1 m2 a1 a2 t x : List Bool) :
    Function.update (stk i m1 m2 a1 a2 t) Stk.u2 x = stk i m1 m2 a1 x t := by
  funext k
  cases k <;> simp [Function.update, stk]

lemma upd_acc (i m1 m2 a1 a2 t x : List Bool) :
    Function.update (stk i m1 m2 a1 a2 t) Stk.acc x = stk i m1 m2 a1 a2 x := by
  funext k
  cases k <;> simp [Function.update, stk]

def cfg (l : Option Lab) (i m1 m2 a1 a2 t : List Bool) : N.Cfg :=
  ⟨l, none, stk i m1 m2 a1 a2 t⟩

-- One step of each label, case by case.

lemma step_init (l rest : List Bool) :
    N.step (cfg (some .init) (BitstringEncoding.delimit l ++ rest) [] [] [] [] []) =
      some (cfg (some .chk) (BitstringEncoding.delimit (l.drop 1) ++ rest) [true] [] [] [] []) := by
  show some (TM2.stepAux (prog .init) none
    (stk (BitstringEncoding.delimit l ++ rest) [] [] [] [] [])) = _
  rcases l with _ | ⟨c, l⟩ <;>
    simp [prog, TM2.stepAux, stk, upd_inp, upd_mk1, cfg, BitstringEncoding.delimit] <;> rfl

lemma step_chk_nil (rest m1 : List Bool) :
    N.step (cfg (some .chk) (false :: rest) m1 [] [] [] []) =
      some (cfg (some .movU) rest m1 [] [] [] []) := by
  show some (TM2.stepAux (prog .chk) none (stk (false :: rest) m1 [] [] [] [])) = _
  simp [prog, TM2.stepAux, stk, upd_inp, cfg]
  rfl

lemma step_chk_cons (rest m1 : List Bool) :
    N.step (cfg (some .chk) (true :: rest) m1 [] [] [] []) =
      some (cfg (some .tri) (true :: rest) m1 [] [] [] []) := by
  show some (TM2.stepAux (prog .chk) none (stk (true :: rest) m1 [] [] [] [])) = _
  simp [prog, TM2.stepAux, stk, upd_inp, cfg]
  rfl

lemma step_tri_cons (l rest : List Bool) (c : Bool) (m1 m2 : List Bool) :
    N.step (cfg (some .tri) (BitstringEncoding.delimit l ++ rest) (c :: m1) m2 [] [] []) =
      some (cfg (some .tri) (BitstringEncoding.delimit (l.drop 2) ++ rest) m1
        (true :: true :: true :: m2) [] [] []) := by
  show some (TM2.stepAux (prog .tri) none
    (stk (BitstringEncoding.delimit l ++ rest) (c :: m1) m2 [] [] [])) = _
  rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩ <;>
    simp [prog, TM2.stepAux, stk, upd_inp, upd_mk1, upd_mk2, cfg, BitstringEncoding.delimit] <;>
    rfl

lemma step_tri_nil (i m2 : List Bool) :
    N.step (cfg (some .tri) i [] m2 [] [] []) = some (cfg (some .pour) i [] m2 [] [] []) := by
  show some (TM2.stepAux (prog .tri) none (stk i [] m2 [] [] [])) = _
  simp [prog, TM2.stepAux, stk, upd_mk1, cfg]
  rfl

lemma step_pour_cons (i m1 m2 : List Bool) (c : Bool) :
    N.step (cfg (some .pour) i m1 (c :: m2) [] [] []) =
      some (cfg (some .pour) i (true :: m1) m2 [] [] []) := by
  show some (TM2.stepAux (prog .pour) none (stk i m1 (c :: m2) [] [] [])) = _
  simp [prog, TM2.stepAux, stk, upd_mk1, upd_mk2, cfg]
  rfl

lemma step_pour_nil (i m1 : List Bool) :
    N.step (cfg (some .pour) i m1 [] [] [] []) = some (cfg (some .chk) i m1 [] [] [] []) := by
  show some (TM2.stepAux (prog .pour) none (stk i m1 [] [] [] [])) = _
  simp [prog, TM2.stepAux, stk, upd_mk2, cfg]
  rfl

lemma step_movU_true (c : Bool) (rest m1 a1 : List Bool) :
    N.step (cfg (some .movU) (true :: c :: rest) m1 [] a1 [] []) =
      some (cfg (some .movU) rest m1 [] (c :: a1) [] []) := by
  show some (TM2.stepAux (prog .movU) none (stk (true :: c :: rest) m1 [] a1 [] [])) = _
  simp [prog, TM2.stepAux, stk, upd_inp, upd_u1, cfg]
  rfl

lemma step_movU_false (rest m1 a1 : List Bool) :
    N.step (cfg (some .movU) (false :: rest) m1 [] a1 [] []) =
      some (cfg (some .revU) rest m1 [] a1 [] []) := by
  show some (TM2.stepAux (prog .movU) none (stk (false :: rest) m1 [] a1 [] [])) = _
  simp [prog, TM2.stepAux, stk, upd_inp, upd_u1, cfg]
  rfl

lemma step_revU_cons (c : Bool) (i m1 a1 a2 : List Bool) :
    N.step (cfg (some .revU) i m1 [] (c :: a1) a2 []) =
      some (cfg (some .revU) i m1 [] a1 (c :: a2) []) := by
  show some (TM2.stepAux (prog .revU) none (stk i m1 [] (c :: a1) a2 [])) = _
  simp [prog, TM2.stepAux, stk, upd_u1, upd_u2, cfg]
  rfl

lemma step_revU_nil (i m1 a2 : List Bool) :
    N.step (cfg (some .revU) i m1 [] [] a2 []) = some (cfg (some .emit) i m1 [] [] a2 []) := by
  show some (TM2.stepAux (prog .revU) none (stk i m1 [] [] a2 [])) = _
  simp [prog, TM2.stepAux, stk, upd_u1, upd_u2, cfg]
  rfl

lemma step_emit_cons (c : Bool) (i m1 a2 t : List Bool) :
    N.step (cfg (some .emit) i (c :: m1) [] [] a2 t) =
      some (cfg (some .emit) i.tail m1 [] [] a2.tail
        (i.head?.getD false :: a2.head?.getD false :: t)) := by
  show some (TM2.stepAux (prog .emit) none (stk i (c :: m1) [] [] a2 t)) = _
  simp [prog, TM2.stepAux, stk, upd_inp, upd_mk1, upd_u2, upd_acc, cfg]
  rfl

lemma step_emit_nil (i a2 t : List Bool) :
    N.step (cfg (some .emit) i [] [] [] a2 t) = some (cfg (some .clrU) i [] [] [] a2 t) := by
  show some (TM2.stepAux (prog .emit) none (stk i [] [] [] a2 t)) = _
  simp [prog, TM2.stepAux, stk, upd_inp, upd_mk1, upd_u2, upd_acc, cfg]
  rfl

lemma step_clrU_cons (c : Bool) (i a2 t : List Bool) :
    N.step (cfg (some .clrU) i [] [] [] (c :: a2) t) =
      some (cfg (some .clrU) i [] [] [] a2 t) := by
  show some (TM2.stepAux (prog .clrU) none (stk i [] [] [] (c :: a2) t)) = _
  simp [prog, TM2.stepAux, stk, upd_u2, cfg]
  rfl

lemma step_clrU_nil (i t : List Bool) :
    N.step (cfg (some .clrU) i [] [] [] [] t) = some (cfg (some .clrI) i [] [] [] [] t) := by
  show some (TM2.stepAux (prog .clrU) none (stk i [] [] [] [] t)) = _
  simp [prog, TM2.stepAux, stk, upd_u2, cfg]
  rfl

lemma step_clrI_cons (c : Bool) (i t : List Bool) :
    N.step (cfg (some .clrI) (c :: i) [] [] [] [] t) =
      some (cfg (some .clrI) i [] [] [] [] t) := by
  show some (TM2.stepAux (prog .clrI) none (stk (c :: i) [] [] [] [] t)) = _
  simp [prog, TM2.stepAux, stk, upd_inp, cfg]
  rfl

lemma step_clrI_nil (t : List Bool) :
    N.step (cfg (some .clrI) [] [] [] [] [] t) = some (cfg (some .out) [] [] [] [] [] t) := by
  show some (TM2.stepAux (prog .clrI) none (stk [] [] [] [] [] t)) = _
  simp [prog, TM2.stepAux, stk, upd_inp, cfg]
  rfl

lemma step_out_cons (c : Bool) (i t : List Bool) :
    N.step (cfg (some .out) i [] [] [] [] (c :: t)) =
      some (cfg (some .out) (c :: i) [] [] [] [] t) := by
  show some (TM2.stepAux (prog .out) none (stk i [] [] [] [] (c :: t))) = _
  simp [prog, TM2.stepAux, stk, upd_inp, upd_acc, cfg]
  rfl

lemma step_out_nil (i : List Bool) :
    N.step (cfg (some .out) i [] [] [] [] []) = some (cfg none i [] [] [] [] []) := by
  show some (TM2.stepAux (prog .out) none (stk i [] [] [] [] [])) = _
  simp [prog, TM2.stepAux, stk, upd_inp, upd_acc, cfg]
  rfl

-- The loops.

lemma tri_run (rest : List Bool) (c : ℕ) : ∀ (l : List Bool) (d : ℕ),
    RIn N.step
      (cfg (some .tri) (BitstringEncoding.delimit l ++ rest) (List.replicate c true)
        (List.replicate d true) [] [] [])
      (some (cfg (some .pour) (BitstringEncoding.delimit (l.drop (2 * c)) ++ rest) []
        (List.replicate (d + 3 * c) true) [] [] []))
      (c + 1) := by
  induction c with
  | zero =>
    intro l d
    exact RIn.single (step_tri_nil _ _)
  | succ c ih =>
    intro l d
    have h1 : RIn N.step
        (cfg (some .tri) (BitstringEncoding.delimit l ++ rest) (List.replicate (c + 1) true)
          (List.replicate d true) [] [] [])
        (some (cfg (some .tri) (BitstringEncoding.delimit (l.drop 2) ++ rest)
          (List.replicate c true) (List.replicate (d + 3) true) [] [] [])) 1 :=
      RIn.single (step_tri_cons l rest true (List.replicate c true) (List.replicate d true))
    have h2 := ih (l.drop 2) (d + 3)
    have e2 : (l.drop 2).drop (2 * c) = l.drop (2 * (c + 1)) := by
      rw [List.drop_drop]
      congr 1
      omega
    have e3 : d + 3 + 3 * c = d + 3 * (c + 1) := by omega
    rw [e2, e3] at h2
    exact (h1.trans h2).mono (by omega)

lemma pour_run (i : List Bool) (d : ℕ) : ∀ c : ℕ,
    RIn N.step
      (cfg (some .pour) i (List.replicate c true) (List.replicate d true) [] [] [])
      (some (cfg (some .chk) i (List.replicate (c + d) true) [] [] [] []))
      (d + 1) := by
  induction d with
  | zero =>
    intro c
    exact RIn.single (step_pour_nil _ _)
  | succ d ih =>
    intro c
    have h1 : RIn N.step
        (cfg (some .pour) i (List.replicate c true) (List.replicate (d + 1) true) [] [] [])
        (some (cfg (some .pour) i (List.replicate (c + 1) true) (List.replicate d true)
          [] [] [])) 1 :=
      RIn.single (step_pour_cons i (List.replicate c true) (List.replicate d true) true)
    have h2 := ih (c + 1)
    have e : c + 1 + d = c + (d + 1) := by omega
    rw [e] at h2
    exact (h1.trans h2).mono (by omega)

lemma stage_run (s rest : List Bool) : ∀ k i : ℕ, i + k = Nat.clog 3 s.length →
    RIn N.step
      (cfg (some .chk) (BitstringEncoding.delimit (s.drop (3 ^ i)) ++ rest)
        (List.replicate (3 ^ i) true) [] [] [] [])
      (some (cfg (some .movU) rest (List.replicate (3 ^ Nat.clog 3 s.length) true) [] [] [] []))
      (k * (5 * 3 ^ Nat.clog 3 s.length) + 1) := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have hi' : i = Nat.clog 3 s.length := by omega
    subst hi'
    have hle : s.length ≤ 3 ^ Nat.clog 3 s.length := Nat.le_pow_clog (by norm_num) _
    rw [List.drop_eq_nil_of_le hle]
    exact (RIn.single (step_chk_nil rest _)).mono (by omega)
  | succ k ih =>
    intro i hi
    have hlt : 3 ^ i < s.length := (Nat.lt_clog_iff_pow_lt (by norm_num)).mp (by omega)
    have hpow : 3 ^ (i + 1) ≤ 3 ^ Nat.clog 3 s.length :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < 3 ^ i := Nat.pow_pos (by norm_num)
    rw [pow_succ] at hpow
    obtain ⟨c, l', hd⟩ : ∃ c l', s.drop (3 ^ i) = c :: l' := by
      cases hd : s.drop (3 ^ i) with
      | nil =>
        have := List.drop_eq_nil_iff.mp hd
        omega
      | cons c l' => exact ⟨c, l', rfl⟩
    have h1 : RIn N.step
        (cfg (some .chk) (BitstringEncoding.delimit (s.drop (3 ^ i)) ++ rest)
          (List.replicate (3 ^ i) true) [] [] [] [])
        (some (cfg (some .tri) (BitstringEncoding.delimit (s.drop (3 ^ i)) ++ rest)
          (List.replicate (3 ^ i) true) (List.replicate 0 true) [] [] [])) 1 := by
      rw [hd]
      exact RIn.single (step_chk_cons _ _)
    have h2 := tri_run rest (3 ^ i) (s.drop (3 ^ i)) 0
    have h3 := pour_run (BitstringEncoding.delimit ((s.drop (3 ^ i)).drop (2 * 3 ^ i)) ++ rest)
      (0 + 3 * 3 ^ i) 0
    have h4 := ih (i + 1) (by omega)
    have e1 : (s.drop (3 ^ i)).drop (2 * 3 ^ i) = s.drop (3 ^ (i + 1)) := by
      rw [List.drop_drop, pow_succ]
      congr 1
      omega
    have e2 : 0 + (0 + 3 * 3 ^ i) = 3 ^ (i + 1) := by
      rw [pow_succ]
      omega
    rw [e1] at h2 h3
    rw [e2] at h3
    refine (((h1.trans h2).trans h3).trans h4).mono ?_
    rw [show (k + 1) * (5 * 3 ^ Nat.clog 3 s.length) =
      k * (5 * 3 ^ Nat.clog 3 s.length) + 5 * 3 ^ Nat.clog 3 s.length from Nat.succ_mul _ _]
    generalize k * (5 * 3 ^ Nat.clog 3 s.length) = z
    omega

lemma movU_run (m1 rest : List Bool) : ∀ s a1 : List Bool,
    RIn N.step
      (cfg (some .movU) (BitstringEncoding.delimit s ++ rest) m1 [] a1 [] [])
      (some (cfg (some .revU) rest m1 [] (s.reverse ++ a1) [] []))
      (s.length + 1) := by
  intro s
  induction s with
  | nil =>
    intro a1
    exact RIn.single (step_movU_false rest m1 a1)
  | cons c s ih =>
    intro a1
    have h1 : RIn N.step
        (cfg (some .movU) (BitstringEncoding.delimit (c :: s) ++ rest) m1 [] a1 [] [])
        (some (cfg (some .movU) (BitstringEncoding.delimit s ++ rest) m1 [] (c :: a1) [] []))
        1 :=
      RIn.single (step_movU_true c _ m1 a1)
    have h2 := ih (c :: a1)
    have e : s.reverse ++ c :: a1 = (c :: s).reverse ++ a1 := by simp
    rw [e] at h2
    exact (h1.trans h2).mono (by simp; omega)

lemma revU_run (i m1 : List Bool) : ∀ a1 a2 : List Bool,
    RIn N.step
      (cfg (some .revU) i m1 [] a1 a2 [])
      (some (cfg (some .emit) i m1 [] [] (a1.reverse ++ a2) []))
      (a1.length + 1) := by
  intro a1
  induction a1 with
  | nil =>
    intro a2
    exact RIn.single (step_revU_nil i m1 a2)
  | cons c a1 ih =>
    intro a2
    have h1 := RIn.single (step_revU_cons c i m1 a1 a2)
    have h2 := ih (c :: a2)
    have e : a1.reverse ++ c :: a2 = (c :: a1).reverse ++ a2 := by simp
    rw [e] at h2
    exact (h1.trans h2).mono (by simp; omega)

lemma emit_run (c : ℕ) : ∀ i a2 t : List Bool,
    ∃ i' a2' : List Bool, i'.length ≤ i.length ∧ a2'.length ≤ a2.length ∧
      RIn N.step
        (cfg (some .emit) i (List.replicate c true) [] [] a2 t)
        (some (cfg (some .clrU) i' [] [] [] a2' ((weave c a2 i).reverse ++ t)))
        (c + 1) := by
  induction c with
  | zero =>
    intro i a2 t
    exact ⟨i, a2, le_rfl, le_rfl, RIn.single (step_emit_nil i a2 t)⟩
  | succ c ih =>
    intro i a2 t
    obtain ⟨i', a2', hi, ha, h2⟩ :=
      ih i.tail a2.tail (i.head?.getD false :: a2.head?.getD false :: t)
    have h1 : RIn N.step
        (cfg (some .emit) i (List.replicate (c + 1) true) [] [] a2 t)
        (some (cfg (some .emit) i.tail (List.replicate c true) [] [] a2.tail
          (i.head?.getD false :: a2.head?.getD false :: t))) 1 :=
      RIn.single (step_emit_cons true i (List.replicate c true) a2 t)
    have e : (weave c a2.tail i.tail).reverse ++
        (i.head?.getD false :: a2.head?.getD false :: t) =
        (weave (c + 1) a2 i).reverse ++ t := by
      simp [weave]
    rw [e] at h2
    refine ⟨i', a2', ?_, ?_, (h1.trans h2).mono (by omega)⟩
    · exact hi.trans (by simp)
    · exact ha.trans (by simp)

lemma clrU_run (i t : List Bool) : ∀ a2 : List Bool,
    RIn N.step
      (cfg (some .clrU) i [] [] [] a2 t)
      (some (cfg (some .clrI) i [] [] [] [] t))
      (a2.length + 1) := by
  intro a2
  induction a2 with
  | nil => exact RIn.single (step_clrU_nil i t)
  | cons c a2 ih =>
    exact ((RIn.single (step_clrU_cons c i a2 t)).trans ih).mono (by simp; omega)

lemma clrI_run (t : List Bool) : ∀ i : List Bool,
    RIn N.step
      (cfg (some .clrI) i [] [] [] [] t)
      (some (cfg (some .out) [] [] [] [] [] t))
      (i.length + 1) := by
  intro i
  induction i with
  | nil => exact RIn.single (step_clrI_nil t)
  | cons c i ih =>
    exact ((RIn.single (step_clrI_cons c i t)).trans ih).mono (by simp; omega)

lemma out_run : ∀ t i : List Bool,
    RIn N.step
      (cfg (some .out) i [] [] [] [] t)
      (some (cfg none (t.reverse ++ i) [] [] [] [] []))
      (t.length + 1) := by
  intro t
  induction t with
  | nil =>
    intro i
    exact RIn.single (step_out_nil i)
  | cons c t ih =>
    intro i
    have h1 := RIn.single (step_out_cons c i t)
    have h2 := ih (c :: i)
    have e : t.reverse ++ c :: i = (c :: t).reverse ++ i := by simp
    rw [e] at h2
    exact (h1.trans h2).mono (by simp; omega)

-- Initial and final configurations.

lemma initList_N (l : List Bool) : initList N l = cfg (some .init) l [] [] [] [] [] := by
  simp only [initList, cfg]
  congr 1
  funext k
  cases k <;> rfl

lemma haltList_N (l : List Bool) : haltList N l = cfg none l [] [] [] [] [] := by
  simp only [haltList, cfg]
  congr 1
  funext k
  cases k <;> rfl

/-- The whole run. -/
lemma full_run (s bu bv : List Bool) :
    RIn N.step
      (initList N (BitstringEncoding.delimit s ++ (BitstringEncoding.delimit bu ++ bv)))
      (some (haltList N (weave (3 ^ Nat.clog 3 s.length) bu bv)))
      (Nat.clog 3 s.length * (5 * 3 ^ Nat.clog 3 s.length) + 3 * 3 ^ Nat.clog 3 s.length +
        3 * bu.length + bv.length + 8) := by
  rw [initList_N, haltList_N]
  have h0 := RIn.single (step_init s (BitstringEncoding.delimit bu ++ bv))
  have h1 := stage_run s (BitstringEncoding.delimit bu ++ bv) (Nat.clog 3 s.length) 0
    (by omega)
  have h2 := movU_run (List.replicate (3 ^ Nat.clog 3 s.length) true) bv bu []
  have h3 := revU_run bv (List.replicate (3 ^ Nat.clog 3 s.length) true) (bu.reverse ++ []) []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h3
  obtain ⟨i', a2', hi, ha, h4⟩ := emit_run (3 ^ Nat.clog 3 s.length) bv bu []
  have h5 := clrU_run i' ((weave (3 ^ Nat.clog 3 s.length) bu bv).reverse ++ []) a2'
  have h6 := clrI_run ((weave (3 ^ Nat.clog 3 s.length) bu bv).reverse ++ []) i'
  have h7 := out_run ((weave (3 ^ Nat.clog 3 s.length) bu bv).reverse ++ []) []
  simp only [List.append_nil, List.reverse_reverse] at h2 h4 h5 h6 h7
  have hw := weave_length (3 ^ Nat.clog 3 s.length) bu bv
  rw [List.length_reverse, hw] at h7
  have h01 : RIn N.step
      (cfg (some .init) (BitstringEncoding.delimit s ++ (BitstringEncoding.delimit bu ++ bv))
        [] [] [] [] [])
      (some (cfg (some .movU) (BitstringEncoding.delimit bu ++ bv)
        (List.replicate (3 ^ Nat.clog 3 s.length) true) [] [] [] []))
      (1 + (Nat.clog 3 s.length * (5 * 3 ^ Nat.clog 3 s.length) + 1)) := h0.trans h1
  refine ((((((h01.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).mono ?_
  generalize Nat.clog 3 s.length * (5 * 3 ^ Nat.clog 3 s.length) = z
  omega

/-- The value of the time bound. -/
lemma time_eval (L : ℕ) :
    (15 * Polynomial.X * Polynomial.X + 14 * Polynomial.X + 11 : Polynomial ℕ).eval L =
      15 * L * L + 14 * L + 11 := by
  simp

end Setup

open Setup in
/-- The setup map is computable in polynomial time. -/
theorem setupFn_polyTime : ComplexityTheory.IsPolyTime setupFn := by
  refine ⟨{ tm := N
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := 15 * Polynomial.X * Polynomial.X + 14 * Polynomial.X + 11
            outputsFun := fun x => ?_ }⟩
  obtain ⟨n, u, v⟩ := x
  have henc : (BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode (n, u, v) =
      BitstringEncoding.delimit (Nat.bits n) ++
        (BitstringEncoding.delimit (Nat.bits u) ++ Nat.bits v) := by
    have : (BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode (n, u, v) =
        BitstringEncoding.delimit (encodeNat n) ++
          (BitstringEncoding.delimit (encodeNat u) ++ encodeNat v) := rfl
    rw [this, encodeNat_eq_bits, encodeNat_eq_bits, encodeNat_eq_bits]
  have hout : (BitstringEncoding.toEncoding (α := Mid)).encode (setupFn (n, u, v)) =
      weave (3 ^ Nat.clog 3 (Nat.bits n).length) (Nat.bits u) (Nat.bits v) := by
    have : (BitstringEncoding.toEncoding (α := Mid)).encode (setupFn (n, u, v)) =
        (List.range (3 ^ Nat.clog 3 (Nat.size n))).flatMap
          (fun i => [u.testBit i, v.testBit i]) := rfl
    rw [this, weave_eq, Nat.size_eq_bits_len]
    congr 1
    funext i
    rw [testBit_eq_getD, testBit_eq_getD]
  have hin : List.map ((Equiv.refl Bool : N.Γ N.k₀ ≃ Bool).invFun)
      ((BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode (n, u, v)) =
      BitstringEncoding.delimit (Nat.bits n) ++
        (BitstringEncoding.delimit (Nat.bits u) ++ Nat.bits v) := by
    rw [henc]; exact List.map_id _
  have hout' : List.map ((Equiv.refl Bool : N.Γ N.k₁ ≃ Bool).invFun)
      ((BitstringEncoding.toEncoding (α := Mid)).encode (setupFn (n, u, v))) =
      weave (3 ^ Nat.clog 3 (Nat.bits n).length) (Nat.bits u) (Nat.bits v) := by
    rw [hout]; exact List.map_id _
  have hn : ((BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode (n, u, v)).length =
      2 * (Nat.bits n).length + 1 + (2 * (Nat.bits u).length + 1 + (Nat.bits v).length) := by
    rw [henc]; simp [BitstringEncoding.length_delimit]
  have hb : Nat.clog 3 (Nat.bits n).length * (5 * 3 ^ Nat.clog 3 (Nat.bits n).length) +
      3 * 3 ^ Nat.clog 3 (Nat.bits n).length + 3 * (Nat.bits u).length + (Nat.bits v).length + 8 ≤
      (15 * Polynomial.X * Polynomial.X + 14 * Polynomial.X + 11 : Polynomial ℕ).eval
        ((BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode (n, u, v)).length := by
    rw [time_eval]
    exact budget_le _ _ _ _ (by rw [hn]; omega)
  have key : ∀ l l' : List Bool,
      l = BitstringEncoding.delimit (Nat.bits n) ++
        (BitstringEncoding.delimit (Nat.bits u) ++ Nat.bits v) →
      l' = weave (3 ^ Nat.clog 3 (Nat.bits n).length) (Nat.bits u) (Nat.bits v) →
      TM2OutputsInTime N l (some l')
        ((15 * Polynomial.X * Polynomial.X + 14 * Polynomial.X + 11 : Polynomial ℕ).eval
          ((BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode (n, u, v)).length) := by
    rintro l l' rfl rfl
    exact Classical.choice (by
      obtain ⟨k, hle, he⟩ := (full_run (Nat.bits n) (Nat.bits u) (Nat.bits v)).mono hb
      exact ⟨⟨⟨k, he⟩, hle⟩⟩)
  exact key _ _ hin hout'

end Erdos78Paley

end PartSetup

section PartEval

open ComplexityTheory
open Turing Computability

-- Poly-time fact for the Paley split of Erdos 78: the quadratic character of the norm of a
-- field element of F_13[x]/(x^m - 2), read from a bit list, is computable in polynomial time.
-- Mathlib has no composition lemmas for poly-time machines, so the machine is built by hand.
-- Stacks: the main stack (input bits, then the one-bit answer) and nine internal stacks over
-- ZMod 13. A polynomial is stored with its highest coefficient on top (the reversed list).
--   W: the element w.  Y: the running power.  Z, R: operands of the Horner product.
--   T, Y2, R2: temporaries.  C: one mark per coefficient.  K: thirteen marks per round.
-- Round (once per mark on C): Z := W, then thirteen times Z := Z * Y, then Y := Z.
-- Product: R starts empty (read as zero); for each coefficient c of Z, highest first,
-- one pass replaces R by R * x + c * Y modulo x^m - 2.

namespace Erdos78Paley

namespace Eval

def RIn {σ : Type} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Prop :=
  ∃ n ≤ m, (flip bind f)^[n] (some a) = b

lemma RIn.single {σ : Type} {f : σ → Option σ} {a b : σ} (h : f a = some b) :
    RIn f a (some b) 1 :=
  ⟨1, le_rfl, h⟩

lemma RIn.trans {σ : Type} {f : σ → Option σ} {a b : σ} {c : Option σ} {m₁ m₂ : ℕ}
    (h₁ : RIn f a (some b) m₁) (h₂ : RIn f b c m₂) : RIn f a c (m₁ + m₂) := by
  obtain ⟨n₁, hn₁, e₁⟩ := h₁
  obtain ⟨n₂, hn₂, e₂⟩ := h₂
  refine ⟨n₂ + n₁, by omega, ?_⟩
  rw [Function.iterate_add_apply, e₁, e₂]

lemma RIn.mono {σ : Type} {f : σ → Option σ} {a : σ} {b : Option σ} {m m' : ℕ}
    (h : RIn f a b m) (hm : m ≤ m') : RIn f a b m' := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨n, hn.trans hm, e⟩

-- Internal stacks.
inductive J
  | sW | sY | sZ | sR | sT | sY2 | sR2 | sC | sK
  deriving DecidableEq

instance : Fintype J :=
  Fintype.ofList [.sW, .sY, .sZ, .sR, .sT, .sY2, .sR2, .sC, .sK] (by intro x; cases x <;> simp)

-- Pour operations: move one stack onto another (or discard it).
inductive PId
  | pWT | pRT | pTZ | pY2Y | pR2R | cY | pZT | pTY | pYT | cT | cW
  deriving DecidableEq

instance : Fintype PId :=
  Fintype.ofList [.pWT, .pRT, .pTZ, .pY2Y, .pR2R, .cY, .pZT, .pTY, .pYT, .cT, .cW]
    (by intro x; cases x <;> simp)

inductive Lbl
  | init0 | init | outer | copy | mulHead | passLoop | repCheck | fin1 | fin2
  | pour (p : PId)
  deriving DecidableEq, Fintype

structure St where
  tmp : Option F
  c : F
  carry : F
  r : F
  deriving DecidableEq, Fintype

def v0 : St := ⟨none, 0, 0, 0⟩

abbrev Gam : Option J → Type
  | none => Bool
  | some _ => F

def psrc : PId → J
  | .pWT => .sW | .pRT => .sR | .pTZ => .sT | .pY2Y => .sY2 | .pR2R => .sR2 | .cY => .sY
  | .pZT => .sZ | .pTY => .sT | .pYT => .sY | .cT => .sT | .cW => .sW

def pdst : PId → Option J
  | .pWT => some .sT | .pRT => some .sT | .pTZ => some .sZ | .pY2Y => some .sY
  | .pR2R => some .sR | .cY => none
  | .pZT => some .sT | .pTY => some .sY | .pYT => some .sT | .cT => none | .cW => none

def pnext : PId → Lbl
  | .pWT => .copy | .pRT => .pour .pTZ | .pTZ => .repCheck | .pY2Y => .pour .pR2R
  | .pR2R => .mulHead | .cY => .pour .pZT
  | .pZT => .pour .pTY | .pTY => .outer | .pYT => .fin1 | .cT => .pour .cW | .cW => .fin2

def pushTo : Option J → TM2.Stmt Gam Lbl St → TM2.Stmt Gam Lbl St
  | none, q => q
  | some d, q => .push (some d) (fun v => v.tmp.getD 0) q

def initStmt (y : F) : TM2.Stmt Gam Lbl St :=
  .pop none (fun v (o : Option Bool) => { v with tmp := o.map bF }) <|
    .branch (fun v => v.tmp.isSome)
      (.pop none (fun v (o : Option Bool) =>
          { v with tmp := o.map (fun b => v.tmp.getD 0 - bF b) }) <|
        .branch (fun v => v.tmp.isSome)
          (.push (some .sW) (fun v => v.tmp.getD 0) <|
            .push (some .sC) (fun _ => (0 : F)) <|
              .push (some .sY) (fun _ => y) <| .goto fun _ => .init)
          (.goto fun _ => .outer))
      (.goto fun _ => .outer)

def push13 (q : TM2.Stmt Gam Lbl St) : TM2.Stmt Gam Lbl St :=
  let p : TM2.Stmt Gam Lbl St → TM2.Stmt Gam Lbl St := .push (some .sK) (fun _ => (0 : F))
  p <| p <| p <| p <| p <| p <| p <| p <| p <| p <| p <| p <| p <| q

def prog : Lbl → TM2.Stmt Gam Lbl St
  | .init0 => initStmt 1
  | .init => initStmt 0
  | .outer =>
    .pop (some .sC) (fun v (o : Option F) => { v with tmp := o }) <|
      .branch (fun v => v.tmp.isSome)
        (.goto fun _ => .pour .pWT)
        (.goto fun _ => .pour .pYT)
  | .copy =>
    .pop (some .sT) (fun v (o : Option F) => { v with tmp := o }) <|
      .branch (fun v => v.tmp.isSome)
        (.push (some .sW) (fun v => v.tmp.getD 0) <|
          .push (some .sZ) (fun v => v.tmp.getD 0) <| .goto fun _ => .copy)
        (push13 <| .goto fun _ => .repCheck)
  | .repCheck =>
    .pop (some .sK) (fun v (o : Option F) => { v with tmp := o }) <|
      .branch (fun v => v.tmp.isSome)
        (.goto fun _ => .mulHead)
        (.goto fun _ => .pour .cY)
  | .mulHead =>
    .pop (some .sZ) (fun v (o : Option F) => { v with tmp := o }) <|
      .branch (fun v => v.tmp.isSome)
        (.pop (some .sR) (fun v (o : Option F) =>
            { v with c := v.tmp.getD 0, carry := 2 * o.getD 0 }) <|
          .goto fun _ => .passLoop)
        (.goto fun _ => .pour .pRT)
  | .passLoop =>
    .pop (some .sY) (fun v (o : Option F) => { v with tmp := o }) <|
      .branch (fun v => v.tmp.isSome)
        (.pop (some .sR) (fun v (o : Option F) => { v with r := o.getD v.carry }) <|
          .push (some .sY2) (fun v => v.tmp.getD 0) <|
            .push (some .sR2) (fun v => v.r + v.c * v.tmp.getD 0) <| .goto fun _ => .passLoop)
        (.goto fun _ => .pour .pY2Y)
  | .fin1 =>
    .pop (some .sT) (fun v (o : Option F) => { v with c := o.getD 0 }) <|
      .push none (fun v => isSq v.c) <| .goto fun _ => .pour .cT
  | .fin2 => .halt
  | .pour p =>
    .pop (some (psrc p)) (fun v (o : Option F) => { v with tmp := o }) <|
      .branch (fun v => v.tmp.isSome)
        (pushTo (pdst p) (.goto fun _ => .pour p))
        (.load (fun _ => v0) <| .goto fun _ => pnext p)

def M : FinTM2 :=
  { K := Option J
    k₀ := none
    k₁ := none
    Γ := Gam
    Λ := Lbl
    main := .init0
    σ := St
    initialState := v0
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := prog }

def mk (i : List Bool) (S : J → List F) : ∀ k : Option J, List (Gam k)
  | none => i
  | some j => S j

def st (w y z r t y2 r2 c k : List F) : J → List F
  | .sW => w | .sY => y | .sZ => z | .sR => r | .sT => t | .sY2 => y2 | .sR2 => r2
  | .sC => c | .sK => k


-- Stack-level versions of the spec functions (stack lists are reversed coefficient lists).

def passF (c carry : F) : List F → List F → List F
  | [], _ => []
  | s :: y, r => (r.headD carry + c * s) :: passF c carry y r.tail

def hS (c : F) (y r : List F) : List F := passF c (2 * r.headD 0) y r.tail

def mulS (z y : List F) : List F := z.foldl (fun r c => hS c y r) []

def frobS (w y : List F) : List F := (fun z => mulS z y)^[13] w

lemma passF_length (c carry : F) (y r : List F) : (passF c carry y r).length = y.length := by
  induction y generalizing r with
  | nil => rfl
  | cons s y ih => simp [passF, ih]

lemma passF_eq (c carry : F) (y r : List F) :
    passF c carry y r = List.zipWith (fun r s => r + c * s)
      (r ++ List.replicate (y.length - r.length) carry) y := by
  induction y generalizing r with
  | nil => simp [passF]
  | cons s y ih =>
    cases r with
    | nil => simp [passF, ih, List.replicate_succ]
    | cons a r => simp [passF, ih]

lemma mulX_concat (init : List F) (t : F) : mulX (init ++ [t]) = (2 * t) :: init := by
  simp [mulX]

lemma mulX_length (a : List F) : (mulX a).length = a.length := by
  rcases List.eq_nil_or_concat' a with rfl | ⟨i, t, rfl⟩
  · simp [mulX]
  · simp [mulX]

lemma mulX_replicate (n : ℕ) : mulX (List.replicate n (0 : F)) = List.replicate n 0 := by
  cases n with
  | zero => simp [mulX]
  | succ n =>
    have h : List.replicate (n + 1) (0 : F) = List.replicate n 0 ++ [0] := by
      rw [← List.replicate_succ']
    rw [h, mulX_concat, ← h]
    simp [List.replicate_succ]

lemma hstep_length (b acc : List F) (c : F) (h : acc.length = b.length) :
    (hstep b acc c).length = b.length := by
  simp [hstep, mulX_length, h]

lemma mul_length (a b : List F) : (mul a b).length = b.length := by
  induction a with
  | nil => simp [mul]
  | cons c a ih => exact hstep_length b (mul a b) c ih

lemma hS_rev (c : F) (b acc : List F) (h : acc.length = b.length) :
    hS c b.reverse acc.reverse = (hstep b acc c).reverse := by
  rcases List.eq_nil_or_concat' acc with rfl | ⟨init, t, rfl⟩
  · have hb : b = [] := by
      rw [← List.length_eq_zero_iff]; simpa using h.symm
    subst hb
    simp [hS, passF, hstep, mulX]
  · have hl : init.length + 1 = b.length := by simpa using h
    rw [hstep, mulX_concat, List.reverse_zipWith (by simpa using hl)]
    simp only [hS, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.headD_cons, List.tail_cons, passF_eq, List.length_reverse]
    have : b.length - init.length = 1 := by omega
    rw [this]
    rfl

lemma hS_nil (c : F) (b : List F) :
    hS c b.reverse [] = (hstep b (List.replicate b.length 0) c).reverse := by
  rw [hstep, mulX_replicate, List.reverse_zipWith (by simp)]
  simp [hS, passF_eq]

lemma mulS_rev (a b : List F) (h : a.length = b.length) :
    mulS a.reverse b.reverse = (mul a b).reverse := by
  have key : ∀ a : List F, a ≠ [] →
      a.foldr (fun c r => hS c b.reverse r) [] = (mul a b).reverse := by
    intro a
    induction a with
    | nil => intro h; exact absurd rfl h
    | cons c a ih =>
      intro _
      by_cases ha : a = []
      · subst ha
        simp [mul, hS_nil]
      · rw [List.foldr_cons, ih ha]
        exact hS_rev c b (mul a b) (mul_length a b)
  unfold mulS
  rw [List.foldl_reverse]
  by_cases ha : a = []
  · subst ha
    have hb : b = [] := by
      rw [← List.length_eq_zero_iff]; simpa using h.symm
    subst hb
    simp [mul]
  · exact key a ha

lemma iter_mulS_rev (y : List F) (k : ℕ) : ∀ z : List F, z.length = y.length →
    (fun z => mulS z y.reverse)^[k] z.reverse = ((fun z => mul z y)^[k] z).reverse := by
  induction k with
  | zero => intro z _; rfl
  | succ k ih =>
    intro z hz
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, mulS_rev z y hz]
    exact ih _ (mul_length z y)

lemma frobS_rev (w y : List F) (h : w.length = y.length) :
    frobS w.reverse y.reverse = (frob w y).reverse :=
  iter_mulS_rev y 13 w h

lemma frob_length (w y : List F) : (frob w y).length = y.length := by
  show ((fun z => mul z y)^[12 + 1] w).length = y.length
  rw [Function.iterate_succ_apply']
  exact mul_length _ _

lemma iter_frobS_rev (w : List F) (k : ℕ) : ∀ y : List F, w.length = y.length →
    (frobS w.reverse)^[k] y.reverse = ((frob w)^[k] y).reverse := by
  induction k with
  | zero => intro y _; rfl
  | succ k ih =>
    intro y hy
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, frobS_rev w y hy]
    exact ih _ (by rw [frob_length]; exact hy)

lemma hS_length (c : F) (y r : List F) : (hS c y r).length = y.length :=
  passF_length _ _ _ _

lemma foldl_hS_length_le (z y : List F) : ∀ r : List F, r.length ≤ y.length →
    (z.foldl (fun r c => hS c y r) r).length ≤ y.length := by
  induction z with
  | nil => intro r h; exact h
  | cons c z ih =>
    intro r _
    exact ih _ (by rw [hS_length])

lemma mulS_length_le (z y : List F) : (mulS z y).length ≤ y.length :=
  foldl_hS_length_le z y [] (by simp)

lemma iter_mulS_length_le (y : List F) (B : ℕ) (hy : y.length ≤ B) (k : ℕ) :
    ∀ z : List F, z.length ≤ B → ((fun z => mulS z y)^[k] z).length ≤ B := by
  induction k with
  | zero => intro z hz; exact hz
  | succ k ih =>
    intro z _
    rw [Function.iterate_succ_apply]
    exact ih _ ((mulS_length_le z y).trans hy)

lemma frobS_length_le (w y : List F) : (frobS w y).length ≤ y.length := by
  show ((fun z => mulS z y)^[12 + 1] w).length ≤ y.length
  rw [Function.iterate_succ_apply']
  exact mulS_length_le _ _

lemma iter_frobS_length_le (w : List F) (B : ℕ) (k : ℕ) :
    ∀ y : List F, y.length ≤ B → ((frobS w)^[k] y).length ≤ B := by
  induction k with
  | zero => intro y hy; exact hy
  | succ k ih =>
    intro y hy
    rw [Function.iterate_succ_apply]
    exact ih _ ((frobS_length_le w y).trans hy)

lemma dec_length_aux (l : List Bool) :
    2 * (dec l).length ≤ l.length ∧ ∀ a, 2 * (dec (a :: l)).length ≤ l.length + 1 := by
  induction l with
  | nil => simp [dec]
  | cons b l ih =>
    refine ⟨ih.2 b, fun a => ?_⟩
    have := ih.1
    simp only [dec, List.length_cons]
    omega

lemma dec_length_le (l : List Bool) : (dec l).length ≤ l.length := by
  have := (dec_length_aux l).1
  omega

lemma one_reverse (n : ℕ) : (one (n + 1)).reverse = List.replicate n 0 ++ [1] := by
  simp [one]

-- Presenting the stacks as a function of lists.

@[simp] lemma upd_none (i : List Bool) (S : J → List F) (i' : List Bool) :
    Function.update (mk i S) none i' = mk i' S := by
  funext k
  cases k <;> simp [Function.update, mk]

@[simp] lemma upd_some (i : List Bool) (S : J → List F) (j : J) (l : List F) :
    Function.update (mk i S) (some j) l = mk i (Function.update S j l) := by
  funext k
  rcases k with _ | k
  · simp [Function.update, mk]
  · by_cases h : k = j
    · subst h
      simp [Function.update, mk]
    · simp [Function.update, mk, h]

@[simp] lemma st_upd_W (w y z r t y2 r2 c k l : List F) :
    Function.update (st w y z r t y2 r2 c k) J.sW l = st l y z r t y2 r2 c k := by
  funext j
  cases j <;> simp [Function.update, st]

@[simp] lemma st_upd_Y (w y z r t y2 r2 c k l : List F) :
    Function.update (st w y z r t y2 r2 c k) J.sY l = st w l z r t y2 r2 c k := by
  funext j
  cases j <;> simp [Function.update, st]

@[simp] lemma st_upd_Z (w y z r t y2 r2 c k l : List F) :
    Function.update (st w y z r t y2 r2 c k) J.sZ l = st w y l r t y2 r2 c k := by
  funext j
  cases j <;> simp [Function.update, st]

@[simp] lemma st_upd_R (w y z r t y2 r2 c k l : List F) :
    Function.update (st w y z r t y2 r2 c k) J.sR l = st w y z l t y2 r2 c k := by
  funext j
  cases j <;> simp [Function.update, st]

@[simp] lemma st_upd_T (w y z r t y2 r2 c k l : List F) :
    Function.update (st w y z r t y2 r2 c k) J.sT l = st w y z r l y2 r2 c k := by
  funext j
  cases j <;> simp [Function.update, st]

@[simp] lemma st_upd_Y2 (w y z r t y2 r2 c k l : List F) :
    Function.update (st w y z r t y2 r2 c k) J.sY2 l = st w y z r t l r2 c k := by
  funext j
  cases j <;> simp [Function.update, st]

@[simp] lemma st_upd_R2 (w y z r t y2 r2 c k l : List F) :
    Function.update (st w y z r t y2 r2 c k) J.sR2 l = st w y z r t y2 l c k := by
  funext j
  cases j <;> simp [Function.update, st]

@[simp] lemma st_upd_C (w y z r t y2 r2 c k l : List F) :
    Function.update (st w y z r t y2 r2 c k) J.sC l = st w y z r t y2 r2 l k := by
  funext j
  cases j <;> simp [Function.update, st]

@[simp] lemma st_upd_K (w y z r t y2 r2 c k l : List F) :
    Function.update (st w y z r t y2 r2 c k) J.sK l = st w y z r t y2 r2 c l := by
  funext j
  cases j <;> simp [Function.update, st]

def cfg (l : Option Lbl) (v : St) (i : List Bool) (S : J → List F) : M.Cfg :=
  ⟨l, v, mk i S⟩

-- Single steps.

lemma stepAux_init_pair (yv : F) (v : St) (a b : Bool) (rest : List Bool)
    (w y z r t y2 r2 c k : List F) :
    TM2.stepAux (initStmt yv) v (mk (a :: b :: rest) (st w y z r t y2 r2 c k)) =
      cfg (some .init) { v with tmp := some (bF a - bF b) } rest
        (st ((bF a - bF b) :: w) (yv :: y) z r t y2 r2 (0 :: c) k) := by
  simp [initStmt, TM2.stepAux, mk, cfg, st]
  rfl

lemma stepAux_init_one (yv : F) (v : St) (a : Bool) (S : J → List F) :
    TM2.stepAux (initStmt yv) v (mk [a] S) = cfg (some .outer) { v with tmp := none } [] S := by
  simp [initStmt, TM2.stepAux, mk, cfg, st]
  rfl

lemma stepAux_init_nil (yv : F) (v : St) (S : J → List F) :
    TM2.stepAux (initStmt yv) v (mk [] S) = cfg (some .outer) { v with tmp := none } [] S := by
  simp [initStmt, TM2.stepAux, mk, cfg, st]
  rfl

lemma step_outer_cons (v : St) (i : List Bool) (x : F) (w y z r t y2 r2 c k : List F) :
    M.step (cfg (some .outer) v i (st w y z r t y2 r2 (x :: c) k)) =
      some (cfg (some (.pour .pWT)) { v with tmp := some x } i (st w y z r t y2 r2 c k)) := by
  show some (TM2.stepAux (prog .outer) v (mk i (st w y z r t y2 r2 (x :: c) k))) = _
  simp [prog, TM2.stepAux, mk, cfg, st]
  rfl

lemma step_outer_nil (v : St) (i : List Bool) (w y z r t y2 r2 k : List F) :
    M.step (cfg (some .outer) v i (st w y z r t y2 r2 [] k)) =
      some (cfg (some (.pour .pYT)) { v with tmp := none } i (st w y z r t y2 r2 [] k)) := by
  show some (TM2.stepAux (prog .outer) v (mk i (st w y z r t y2 r2 [] k))) = _
  simp [prog, TM2.stepAux, mk, cfg, st]
  rfl

lemma step_copy_cons (v : St) (i : List Bool) (x : F) (w y z r t y2 r2 c k : List F) :
    M.step (cfg (some .copy) v i (st w y z r (x :: t) y2 r2 c k)) =
      some (cfg (some .copy) { v with tmp := some x } i (st (x :: w) y (x :: z) r t y2 r2 c k)) := by
  show some (TM2.stepAux (prog .copy) v (mk i (st w y z r (x :: t) y2 r2 c k))) = _
  simp [prog, TM2.stepAux, mk, cfg, st]
  rfl

lemma step_copy_nil (v : St) (i : List Bool) (w y z r y2 r2 c k : List F) :
    M.step (cfg (some .copy) v i (st w y z r [] y2 r2 c k)) =
      some (cfg (some .repCheck) { v with tmp := none } i
        (st w y z r [] y2 r2 c (List.replicate 13 0 ++ k))) := by
  show some (TM2.stepAux (prog .copy) v (mk i (st w y z r [] y2 r2 c k))) = _
  simp [prog, push13, TM2.stepAux, mk, cfg, st, List.replicate]
  rfl

lemma step_rep_cons (v : St) (i : List Bool) (x : F) (w y z r t y2 r2 c k : List F) :
    M.step (cfg (some .repCheck) v i (st w y z r t y2 r2 c (x :: k))) =
      some (cfg (some .mulHead) { v with tmp := some x } i (st w y z r t y2 r2 c k)) := by
  show some (TM2.stepAux (prog .repCheck) v (mk i (st w y z r t y2 r2 c (x :: k)))) = _
  simp [prog, TM2.stepAux, mk, cfg, st]
  rfl

lemma step_rep_nil (v : St) (i : List Bool) (w y z r t y2 r2 c : List F) :
    M.step (cfg (some .repCheck) v i (st w y z r t y2 r2 c [])) =
      some (cfg (some (.pour .cY)) { v with tmp := none } i (st w y z r t y2 r2 c [])) := by
  show some (TM2.stepAux (prog .repCheck) v (mk i (st w y z r t y2 r2 c []))) = _
  simp [prog, TM2.stepAux, mk, cfg, st]
  rfl

lemma step_mulHead_cons (v : St) (i : List Bool) (x : F) (w y z r t y2 r2 c k : List F) :
    M.step (cfg (some .mulHead) v i (st w y (x :: z) r t y2 r2 c k)) =
      some (cfg (some .passLoop) { v with tmp := some x, c := x, carry := 2 * r.headD 0 } i
        (st w y z r.tail t y2 r2 c k)) := by
  show some (TM2.stepAux (prog .mulHead) v (mk i (st w y (x :: z) r t y2 r2 c k))) = _
  cases r <;> simp [prog, TM2.stepAux, mk, cfg, st] <;> rfl

lemma step_mulHead_nil (v : St) (i : List Bool) (w y r t y2 r2 c k : List F) :
    M.step (cfg (some .mulHead) v i (st w y [] r t y2 r2 c k)) =
      some (cfg (some (.pour .pRT)) { v with tmp := none } i (st w y [] r t y2 r2 c k)) := by
  show some (TM2.stepAux (prog .mulHead) v (mk i (st w y [] r t y2 r2 c k))) = _
  simp [prog, TM2.stepAux, mk, cfg, st]
  rfl

lemma step_pass_cons (v : St) (i : List Bool) (s : F) (w y z r t y2 r2 c k : List F) :
    M.step (cfg (some .passLoop) v i (st w (s :: y) z r t y2 r2 c k)) =
      some (cfg (some .passLoop) { v with tmp := some s, r := r.headD v.carry } i
        (st w y z r.tail t (s :: y2) ((r.headD v.carry + v.c * s) :: r2) c k)) := by
  show some (TM2.stepAux (prog .passLoop) v (mk i (st w (s :: y) z r t y2 r2 c k))) = _
  cases r <;> simp [prog, TM2.stepAux, mk, cfg, st] <;> rfl

lemma step_pass_nil (v : St) (i : List Bool) (w z r t y2 r2 c k : List F) :
    M.step (cfg (some .passLoop) v i (st w [] z r t y2 r2 c k)) =
      some (cfg (some (.pour .pY2Y)) { v with tmp := none } i (st w [] z r t y2 r2 c k)) := by
  show some (TM2.stepAux (prog .passLoop) v (mk i (st w [] z r t y2 r2 c k))) = _
  simp [prog, TM2.stepAux, mk, cfg, st]
  rfl

lemma step_fin1 (v : St) (i : List Bool) (w y z r t y2 r2 c k : List F) :
    M.step (cfg (some .fin1) v i (st w y z r t y2 r2 c k)) =
      some (cfg (some (.pour .cT)) { v with c := t.headD 0 } (isSq (t.headD 0) :: i)
        (st w y z r t.tail y2 r2 c k)) := by
  show some (TM2.stepAux (prog .fin1) v (mk i (st w y z r t y2 r2 c k))) = _
  cases t <;> simp [prog, TM2.stepAux, mk, cfg, st] <;> rfl

lemma step_fin2 (v : St) (i : List Bool) (S : J → List F) :
    M.step (cfg (some .fin2) v i S) = some (cfg none v i S) := by
  show some (TM2.stepAux (prog .fin2) v (mk i S)) = _
  simp [prog, TM2.stepAux, cfg]
  rfl

lemma step_pour_cons (p : PId) (d : J) (hd : pdst p = some d) (v : St) (i : List Bool)
    (S : J → List F) (x : F) (l : List F) (hS : S (psrc p) = x :: l) :
    M.step (cfg (some (.pour p)) v i S) =
      some (cfg (some (.pour p)) { v with tmp := some x } i
        (Function.update (Function.update S (psrc p) l) d
          (x :: Function.update S (psrc p) l d))) := by
  show some (TM2.stepAux (prog (.pour p)) v (mk i S)) = _
  simp [prog, pushTo, hd, TM2.stepAux, mk, cfg, hS]
  rfl

lemma step_clear_cons (p : PId) (hd : pdst p = none) (v : St) (i : List Bool)
    (S : J → List F) (x : F) (l : List F) (hS : S (psrc p) = x :: l) :
    M.step (cfg (some (.pour p)) v i S) =
      some (cfg (some (.pour p)) { v with tmp := some x } i
        (Function.update S (psrc p) l)) := by
  show some (TM2.stepAux (prog (.pour p)) v (mk i S)) = _
  simp [prog, pushTo, hd, TM2.stepAux, mk, cfg, hS]
  rfl

lemma step_pour_nil (p : PId) (v : St) (i : List Bool)
    (S : J → List F) (hS : S (psrc p) = []) :
    M.step (cfg (some (.pour p)) v i S) = some (cfg (some (pnext p)) v0 i S) := by
  show some (TM2.stepAux (prog (.pour p)) v (mk i S)) = _
  have h : Function.update S (psrc p) [] = S := by
    rw [← hS]; exact Function.update_eq_self _ _
  simp [prog, TM2.stepAux, mk, cfg, hS, h]
  rfl

-- Generic pours.

lemma pour_run (p : PId) (d : J) (hd : pdst p = some d) (hne : psrc p ≠ d) (i : List Bool) :
    ∀ (l : List F) (S : J → List F) (v : St), S (psrc p) = l →
      RIn M.step (cfg (some (.pour p)) v i S)
        (some (cfg (some (pnext p)) v0 i
          (Function.update (Function.update S (psrc p) []) d (l.reverse ++ S d))))
        (l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro S v hS
    have h := RIn.single (step_pour_nil p v i S hS)
    have e : Function.update (Function.update S (psrc p) []) d ([].reverse ++ S d) = S := by
      funext j
      by_cases hj : j = d
      · simp [Function.update_apply, hj]
      · by_cases hj2 : j = psrc p
        · subst hj2
          simp [Function.update_apply, hne, hS]
        · simp [Function.update_apply, hj, hj2]
    rw [e]
    exact h
  | cons x l ih =>
    intro S v hS
    have h1 := RIn.single (step_pour_cons p d hd v i S x l hS)
    have h2 := ih (Function.update (Function.update S (psrc p) l) d
      (x :: Function.update S (psrc p) l d)) { v with tmp := some x }
      (by simp [Function.update_apply, hne])
    have h := RIn.trans h1 h2
    have e : Function.update (Function.update (Function.update (Function.update S (psrc p) l) d
        (x :: Function.update S (psrc p) l d)) (psrc p) []) d
        (l.reverse ++ Function.update (Function.update S (psrc p) l) d
          (x :: Function.update S (psrc p) l d) d) =
        Function.update (Function.update S (psrc p) []) d ((x :: l).reverse ++ S d) := by
      funext j
      by_cases hj : j = d
      · simp [Function.update_apply, hj, hne.symm]
      · by_cases hj2 : j = psrc p
        · subst hj2
          simp [Function.update_apply, hne]
        · simp [Function.update_apply, hj, hj2]
    rw [e] at h
    exact h.mono (by simp only [List.length_cons]; omega)

lemma clear_run (p : PId) (hd : pdst p = none) (i : List Bool) :
    ∀ (l : List F) (S : J → List F) (v : St), S (psrc p) = l →
      RIn M.step (cfg (some (.pour p)) v i S)
        (some (cfg (some (pnext p)) v0 i (Function.update S (psrc p) [])))
        (l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro S v hS
    have h := RIn.single (step_pour_nil p v i S hS)
    have e : Function.update S (psrc p) [] = S := by
      rw [← hS]; exact Function.update_eq_self _ _
    rw [e]
    exact h
  | cons x l ih =>
    intro S v hS
    have h1 := RIn.single (step_clear_cons p hd v i S x l hS)
    have h2 := ih (Function.update S (psrc p) l) { v with tmp := some x } (by simp)
    have h := RIn.trans h1 h2
    rw [Function.update_idem] at h
    exact h.mono (by simp only [List.length_cons]; omega)

-- The copy loop: T is poured back on W and also on Z, then 13 marks are pushed on K.

lemma copy_run (i : List Bool) (y r y2 r2 c k : List F) :
    ∀ (t w z : List F) (v : St),
      RIn M.step (cfg (some .copy) v i (st w y z r t y2 r2 c k))
        (some (cfg (some .repCheck) { v with tmp := none } i
          (st (t.reverse ++ w) y (t.reverse ++ z) r [] y2 r2 c (List.replicate 13 0 ++ k))))
        (t.length + 1) := by
  intro t
  induction t with
  | nil =>
    intro w z v
    exact RIn.single (step_copy_nil v i w y z r y2 r2 c k)
  | cons x t ih =>
    intro w z v
    have h := RIn.trans (RIn.single (step_copy_cons v i x w y z r t y2 r2 c k))
      (ih (x :: w) (x :: z) { v with tmp := some x })
    have e1 : (x :: t).reverse ++ w = t.reverse ++ x :: w := by simp
    have e2 : (x :: t).reverse ++ z = t.reverse ++ x :: z := by simp
    rw [e1, e2]
    exact h.mono (by simp only [List.length_cons]; omega)

-- One pass: R becomes R * x + c * Y.

lemma passLoop_run (i : List Bool) (w z t c k : List F) :
    ∀ (y r y2 r2 : List F) (v : St), ∃ v' : St,
      RIn M.step (cfg (some .passLoop) v i (st w y z r t y2 r2 c k))
        (some (cfg (some (.pour .pY2Y)) v' i
          (st w [] z (r.drop y.length) t (y.reverse ++ y2)
            ((passF v.c v.carry y r).reverse ++ r2) c k)))
        (y.length + 1) := by
  intro y
  induction y with
  | nil =>
    intro r y2 r2 v
    exact ⟨_, RIn.single (step_pass_nil v i w z r t y2 r2 c k)⟩
  | cons s y ih =>
    intro r y2 r2 v
    obtain ⟨v', h2⟩ := ih r.tail (s :: y2) ((r.headD v.carry + v.c * s) :: r2)
      { v with tmp := some s, r := r.headD v.carry }
    refine ⟨v', ?_⟩
    have h := RIn.trans (RIn.single (step_pass_cons v i s w y z r t y2 r2 c k)) h2
    have e0 : r.tail.drop y.length = r.drop (s :: y).length := by
      cases r <;> simp
    have e1 : (s :: y).reverse ++ y2 = y.reverse ++ s :: y2 := by simp
    have e2 : (passF v.c v.carry (s :: y) r).reverse ++ r2 =
        (passF v.c v.carry y r.tail).reverse ++ (r.headD v.carry + v.c * s) :: r2 := by
      simp [passF]
    rw [← e0, e1, e2]
    exact h.mono (by simp only [List.length_cons]; omega)

lemma pass_run (v : St) (i : List Bool) (x : F) (w y z r t c k : List F)
    (hr : r.length ≤ y.length) :
    RIn M.step (cfg (some .mulHead) v i (st w y (x :: z) r t [] [] c k))
      (some (cfg (some .mulHead) v0 i (st w y z (hS x y r) t [] [] c k)))
      (3 * y.length + 4) := by
  have h1 := RIn.single (step_mulHead_cons v i x w y z r t [] [] c k)
  obtain ⟨v', h2⟩ := passLoop_run i w z t c k y r.tail [] []
    { v with tmp := some x, c := x, carry := 2 * r.headD 0 }
  have e0 : r.tail.drop y.length = [] := by
    apply List.drop_eq_nil_of_le
    rw [List.length_tail]
    omega
  rw [e0] at h2
  simp only [List.append_nil] at h2
  have h3 := pour_run .pY2Y .sY rfl (by decide) i _ _ v' (rfl :
    (st w [] z [] t (y.reverse ++ []) ((hS x y r).reverse ++ []) c k) (psrc .pY2Y) =
      y.reverse ++ [])
  have h4 := pour_run .pR2R .sR rfl (by decide) i _ _ v0 (rfl :
    (st w y z [] t [] ((hS x y r).reverse ++ []) c k) (psrc .pR2R) = (hS x y r).reverse ++ [])
  simp only [psrc, pnext, st, st_upd_Y, st_upd_Y2, st_upd_R, st_upd_R2, List.append_nil,
    List.reverse_reverse, List.length_reverse, hS_length] at h3 h4
  have h := RIn.trans (RIn.trans (RIn.trans h1 h2) h3) h4
  exact h.mono (by omega)

-- The multiplication loop.

lemma mulloop_run (i : List Bool) (w y t c k : List F) :
    ∀ (z r : List F) (v : St), r.length ≤ y.length → ∃ v' : St,
      RIn M.step (cfg (some .mulHead) v i (st w y z r t [] [] c k))
        (some (cfg (some (.pour .pRT)) v' i
          (st w y [] (z.foldl (fun r x => hS x y r) r) t [] [] c k)))
        (z.length * (3 * y.length + 4) + 1) := by
  intro z
  induction z with
  | nil =>
    intro r v _
    exact ⟨_, (RIn.single (step_mulHead_nil v i w y r t [] [] c k)).mono (by simp)⟩
  | cons x z ih =>
    intro r v hr
    obtain ⟨v', h2⟩ := ih (hS x y r) v0 (by rw [hS_length])
    refine ⟨v', ?_⟩
    have h := RIn.trans (pass_run v i x w y z r t c k hr) h2
    exact h.mono (le_of_eq (by simp only [List.length_cons]; ring))

def mulT (B : ℕ) : ℕ := B * (3 * B + 4) + 2 * B + 3

lemma mulT_le {a b B : ℕ} (ha : a ≤ B) (hb : b ≤ B) : a * (3 * b + 4) + 2 * b + 3 ≤ mulT B := by
  unfold mulT
  have := Nat.mul_le_mul ha (show 3 * b + 4 ≤ 3 * B + 4 by omega)
  omega

lemma mult_run (v : St) (i : List Bool) (w y z c k : List F) :
    RIn M.step (cfg (some .mulHead) v i (st w y z [] [] [] [] c k))
      (some (cfg (some .repCheck) v0 i (st w y (mulS z y) [] [] [] [] c k)))
      (z.length * (3 * y.length + 4) + 2 * y.length + 3) := by
  obtain ⟨v', h1⟩ := mulloop_run i w y [] c k z [] v (by simp)
  have h2 := pour_run .pRT .sT rfl (by decide) i _ _ v' (rfl :
    (st w y [] (mulS z y) [] [] [] c k) (psrc .pRT) = mulS z y)
  have h3 := pour_run .pTZ .sZ rfl (by decide) i _ _ v0 (rfl :
    (st w y [] [] ((mulS z y).reverse ++ []) [] [] c k) (psrc .pTZ) = (mulS z y).reverse ++ [])
  simp only [psrc, pnext, st, st_upd_R, st_upd_T, st_upd_Z, List.append_nil,
    List.reverse_reverse, List.length_reverse] at h2 h3
  have h := RIn.trans (RIn.trans h1 h2) h3
  have hl := mulS_length_le z y
  exact h.mono (by omega)

-- Thirteen multiplications, counted by the marks on K.

lemma frobloop_run (i : List Bool) (w y c : List F) (B : ℕ) (hy : y.length ≤ B) :
    ∀ (ks z : List F) (v : St), z.length ≤ B → ∃ v' : St,
      RIn M.step (cfg (some .repCheck) v i (st w y z [] [] [] [] c ks))
        (some (cfg (some (.pour .cY)) v' i
          (st w y ((fun z => mulS z y)^[ks.length] z) [] [] [] [] c [])))
        (ks.length * (mulT B + 1) + 1) := by
  intro ks
  induction ks with
  | nil =>
    intro z v _
    exact ⟨_, (RIn.single (step_rep_nil v i w y z [] [] [] [] c)).mono (by simp)⟩
  | cons x ks ih =>
    intro z v hz
    obtain ⟨v', h3⟩ := ih (mulS z y) v0 ((mulS_length_le z y).trans hy)
    refine ⟨v', ?_⟩
    have h1 := RIn.single (step_rep_cons v i x w y z [] [] [] [] c ks)
    have h2 := (mult_run { v with tmp := some x } i w y z c ks).mono (mulT_le hz hy)
    have h := RIn.trans (RIn.trans h1 h2) h3
    rw [List.length_cons, Function.iterate_succ_apply]
    exact h.mono (le_of_eq (by ring))

def frobT (B : ℕ) : ℕ := 13 * (mulT B + 1) + 5 * B + 7

-- One round of the outer loop: Y becomes Y ^ 13 * W.

lemma round_run (v : St) (i : List Bool) (x : F) (w y cs : List F) (B : ℕ)
    (hw : w.length ≤ B) (hy : y.length ≤ B) :
    RIn M.step (cfg (some .outer) v i (st w y [] [] [] [] [] (x :: cs) []))
      (some (cfg (some .outer) v0 i (st w (frobS w y) [] [] [] [] [] cs [])))
      (frobT B) := by
  have h1 := RIn.single (step_outer_cons v i x w y [] [] [] [] [] cs [])
  have h2 := pour_run .pWT .sT rfl (by decide) i _ _ { v with tmp := some x } (rfl :
    (st w y [] [] [] [] [] cs []) (psrc .pWT) = w)
  have h3 := copy_run i y [] [] [] cs [] (w.reverse ++ []) [] [] v0
  obtain ⟨v', h4⟩ := frobloop_run i w y cs B hy (List.replicate 13 0) w
    { v0 with tmp := none } hw
  have h5 := clear_run .cY rfl i _ _ v' (rfl :
    (st w y (frobS w y) [] [] [] [] cs []) (psrc .cY) = y)
  have h6 := pour_run .pZT .sT rfl (by decide) i _ _ v0 (rfl :
    (st w [] (frobS w y) [] [] [] [] cs []) (psrc .pZT) = frobS w y)
  have h7 := pour_run .pTY .sY rfl (by decide) i _ _ v0 (rfl :
    (st w [] [] [] ((frobS w y).reverse ++ []) [] [] cs []) (psrc .pTY) =
      (frobS w y).reverse ++ [])
  simp only [psrc, pnext, st, st_upd_W, st_upd_T, st_upd_Z, st_upd_Y, List.append_nil,
    List.reverse_reverse, List.length_reverse, List.length_replicate] at h2 h3 h4 h5 h6 h7
  have h := RIn.trans (RIn.trans (RIn.trans (RIn.trans (RIn.trans (RIn.trans h1 h2) h3) h4) h5)
    h6) h7
  have hl := frobS_length_le w y
  exact h.mono (by unfold frobT; omega)

lemma outerloop_run (i : List Bool) (w : List F) (B : ℕ) (hw : w.length ≤ B) :
    ∀ (cs y : List F) (v : St), y.length ≤ B → ∃ v' : St,
      RIn M.step (cfg (some .outer) v i (st w y [] [] [] [] [] cs []))
        (some (cfg (some (.pour .pYT)) v' i
          (st w ((frobS w)^[cs.length] y) [] [] [] [] [] [] [])))
        (cs.length * frobT B + 1) := by
  intro cs
  induction cs with
  | nil =>
    intro y v _
    exact ⟨_, (RIn.single (step_outer_nil v i w y [] [] [] [] [] [])).mono (by simp)⟩
  | cons x cs ih =>
    intro y v hy
    obtain ⟨v', h2⟩ := ih (frobS w y) v0 ((frobS_length_le w y).trans hy)
    refine ⟨v', ?_⟩
    have h := RIn.trans (round_run v i x w y cs B hw hy) h2
    rw [List.length_cons, Function.iterate_succ_apply]
    exact h.mono (le_of_eq (by ring))

-- The end: read the constant coefficient, clear everything, write the answer.

lemma end_run (v : St) (i : List Bool) (w y : List F) :
    RIn M.step (cfg (some (.pour .pYT)) v i (st w y [] [] [] [] [] [] []))
      (some (cfg none v0 (isSq (y.reverse.headD 0) :: i) (st [] [] [] [] [] [] [] [] [])))
      (2 * y.length + w.length + 5) := by
  have h1 := pour_run .pYT .sT rfl (by decide) i _ _ v (rfl :
    (st w y [] [] [] [] [] [] []) (psrc .pYT) = y)
  have h2 := RIn.single (step_fin1 v0 i w [] [] [] (y.reverse ++ []) [] [] [] [])
  have h3 := clear_run .cT rfl (isSq ((y.reverse ++ []).headD 0) :: i) _ _
    { v0 with c := (y.reverse ++ []).headD 0 } (rfl :
    (st w [] [] [] (y.reverse ++ []).tail [] [] [] []) (psrc .cT) = (y.reverse ++ []).tail)
  have h4 := clear_run .cW rfl (isSq ((y.reverse ++ []).headD 0) :: i) _ _ v0 (rfl :
    (st w [] [] [] [] [] [] [] []) (psrc .cW) = w)
  have h5 := RIn.single (step_fin2 v0 (isSq ((y.reverse ++ []).headD 0) :: i)
    (st [] [] [] [] [] [] [] [] []))
  simp only [psrc, pnext, st, st_upd_W, st_upd_T, st_upd_Y, List.append_nil,
    List.length_tail, List.length_reverse] at h1 h2 h3 h4 h5
  have h := RIn.trans (RIn.trans (RIn.trans (RIn.trans h1 h2) h3) h4) h5
  exact h.mono (by omega)

-- Reading the input: two bits per coefficient.

lemma rep_cons (n : ℕ) (a : F) (l : List F) :
    List.replicate n a ++ a :: l = List.replicate (n + 1) a ++ l := by
  rw [List.replicate_succ']
  simp

lemma step_init_pair (v : St) (a b : Bool) (rest : List Bool) (w y z r t y2 r2 c k : List F) :
    M.step (cfg (some .init) v (a :: b :: rest) (st w y z r t y2 r2 c k)) =
      some (cfg (some .init) { v with tmp := some (bF a - bF b) } rest
        (st ((bF a - bF b) :: w) (0 :: y) z r t y2 r2 (0 :: c) k)) := by
  show some (TM2.stepAux (initStmt 0) v (mk (a :: b :: rest) (st w y z r t y2 r2 c k))) = _
  rw [stepAux_init_pair]
  rfl

lemma step_init_one (v : St) (a : Bool) (S : J → List F) :
    M.step (cfg (some .init) v [a] S) = some (cfg (some .outer) { v with tmp := none } [] S) := by
  show some (TM2.stepAux (initStmt 0) v (mk [a] S)) = _
  rw [stepAux_init_one]
  rfl

lemma step_init_nil (v : St) (S : J → List F) :
    M.step (cfg (some .init) v [] S) = some (cfg (some .outer) { v with tmp := none } [] S) := by
  show some (TM2.stepAux (initStmt 0) v (mk [] S)) = _
  rw [stepAux_init_nil]
  rfl

lemma step_init0_pair (v : St) (a b : Bool) (rest : List Bool) (w y z r t y2 r2 c k : List F) :
    M.step (cfg (some .init0) v (a :: b :: rest) (st w y z r t y2 r2 c k)) =
      some (cfg (some .init) { v with tmp := some (bF a - bF b) } rest
        (st ((bF a - bF b) :: w) (1 :: y) z r t y2 r2 (0 :: c) k)) := by
  show some (TM2.stepAux (initStmt 1) v (mk (a :: b :: rest) (st w y z r t y2 r2 c k))) = _
  rw [stepAux_init_pair]
  rfl

lemma step_init0_one (v : St) (a : Bool) (S : J → List F) :
    M.step (cfg (some .init0) v [a] S) = some (cfg (some .outer) { v with tmp := none } [] S) := by
  show some (TM2.stepAux (initStmt 1) v (mk [a] S)) = _
  rw [stepAux_init_one]
  rfl

lemma step_init0_nil (v : St) (S : J → List F) :
    M.step (cfg (some .init0) v [] S) = some (cfg (some .outer) { v with tmp := none } [] S) := by
  show some (TM2.stepAux (initStmt 1) v (mk [] S)) = _
  rw [stepAux_init_nil]
  rfl

lemma dec_pair (a b : Bool) (rest : List Bool) : dec (a :: b :: rest) = (bF a - bF b) :: dec rest :=
  rfl

lemma init_loop (bits : List Bool) :
    (∀ (w y c : List F) (v : St), ∃ v' : St,
      RIn M.step (cfg (some .init) v bits (st w y [] [] [] [] [] c []))
        (some (cfg (some .outer) v' []
          (st ((dec bits).reverse ++ w) (List.replicate (dec bits).length 0 ++ y) [] [] [] [] []
            (List.replicate (dec bits).length 0 ++ c) [])))
        ((dec bits).length + 1)) ∧
    (∀ (a : Bool) (w y c : List F) (v : St), ∃ v' : St,
      RIn M.step (cfg (some .init) v (a :: bits) (st w y [] [] [] [] [] c []))
        (some (cfg (some .outer) v' []
          (st ((dec (a :: bits)).reverse ++ w) (List.replicate (dec (a :: bits)).length 0 ++ y)
            [] [] [] [] [] (List.replicate (dec (a :: bits)).length 0 ++ c) [])))
        ((dec (a :: bits)).length + 1)) := by
  induction bits with
  | nil =>
    constructor
    · intro w y c v
      exact ⟨_, RIn.single (step_init_nil v (st w y [] [] [] [] [] c []))⟩
    · intro a w y c v
      exact ⟨_, RIn.single (step_init_one v a (st w y [] [] [] [] [] c []))⟩
  | cons b bits ih =>
    constructor
    · exact ih.2 b
    · intro a w y c v
      obtain ⟨v', h2⟩ := ih.1 ((bF a - bF b) :: w) (0 :: y) (0 :: c)
        { v with tmp := some (bF a - bF b) }
      refine ⟨v', ?_⟩
      have h := RIn.trans (RIn.single (step_init_pair v a b bits w y [] [] [] [] [] c [])) h2
      rw [dec_pair, List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
        ← rep_cons, ← rep_cons]
      exact h.mono (by omega)

lemma init_run (bits : List Bool) : ∃ v' : St,
    RIn M.step (cfg (some .init0) v0 bits (st [] [] [] [] [] [] [] [] []))
      (some (cfg (some .outer) v' []
        (st (dec bits).reverse (one (dec bits).length).reverse [] [] [] [] []
          (List.replicate (dec bits).length 0) [])))
      ((dec bits).length + 1) := by
  rcases bits with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact ⟨_, RIn.single (step_init0_nil v0 (st [] [] [] [] [] [] [] [] []))⟩
  · exact ⟨_, RIn.single (step_init0_one v0 a (st [] [] [] [] [] [] [] [] []))⟩
  · obtain ⟨v', h2⟩ := (init_loop rest).1 [bF a - bF b] [1] [0]
      { v0 with tmp := some (bF a - bF b) }
    refine ⟨v', ?_⟩
    have h := RIn.trans (RIn.single (step_init0_pair v0 a b rest [] [] [] [] [] [] [] [] [])) h2
    rw [dec_pair, List.length_cons, List.reverse_cons, one_reverse, List.replicate_succ']
    exact h.mono (by omega)

-- Initial and final configurations.

lemma initList_M (l : List Bool) :
    initList M l = cfg (some .init0) v0 l (st [] [] [] [] [] [] [] [] []) := by
  simp only [initList, cfg]
  congr 1
  funext k
  rcases k with _ | j
  · rfl
  · cases j <;> rfl

lemma haltList_M (l : List Bool) :
    haltList M l = cfg none v0 l (st [] [] [] [] [] [] [] [] []) := by
  simp only [haltList, cfg]
  congr 1
  funext k
  rcases k with _ | j
  · rfl
  · cases j <;> rfl

lemma one_length (n : ℕ) : (one n).length = n := by
  cases n <;> simp [one]

def totalT (m : ℕ) : ℕ := m * frobT m + 4 * m + 7

lemma mulT_mono {a b : ℕ} (h : a ≤ b) : mulT a ≤ mulT b := mulT_le h h

lemma frobT_mono {a b : ℕ} (h : a ≤ b) : frobT a ≤ frobT b := by
  unfold frobT
  have := mulT_mono h
  omega

lemma totalT_mono {a b : ℕ} (h : a ≤ b) : totalT a ≤ totalT b := by
  unfold totalT
  have := Nat.mul_le_mul h (frobT_mono h)
  omega

lemma full_run_cfg (bits : List Bool) :
    RIn M.step (cfg (some .init0) v0 bits (st [] [] [] [] [] [] [] [] []))
      (some (cfg none v0 [evalFn bits] (st [] [] [] [] [] [] [] [] [])))
      (totalT (dec bits).length) := by
  obtain ⟨v1, h1⟩ := init_run bits
  obtain ⟨v2, h2⟩ := outerloop_run [] (dec bits).reverse (dec bits).length (by simp)
    (List.replicate (dec bits).length 0) (one (dec bits).length).reverse v1
    (by simp [one_length])
  have e : (frobS (dec bits).reverse)^[(List.replicate (dec bits).length (0 : F)).length]
      (one (dec bits).length).reverse = (normL (dec bits)).reverse := by
    rw [List.length_replicate, iter_frobS_rev _ _ _ (by rw [one_length])]
    rfl
  have hl := iter_frobS_length_le (dec bits).reverse (dec bits).length
    (List.replicate (dec bits).length (0 : F)).length (one (dec bits).length).reverse
    (by simp [one_length])
  rw [e] at h2 hl
  have h3 := end_run v2 [] (dec bits).reverse (normL (dec bits)).reverse
  simp only [List.reverse_reverse, List.length_reverse, List.length_replicate] at h2 h3 hl
  have h := RIn.trans (RIn.trans h1 h2) h3
  exact h.mono (by unfold totalT; omega)

/-- The whole run on a bit list. -/
lemma full_run (bits : List Bool) :
    RIn M.step (initList M bits) (some (haltList M [evalFn bits]))
      (totalT (dec bits).length) := by
  have h := full_run_cfg bits
  have e1 : initList M bits = cfg (some .init0) v0 bits (st [] [] [] [] [] [] [] [] []) := initList_M bits
  have e2 : haltList M [evalFn bits] = cfg none v0 [evalFn bits] (st [] [] [] [] [] [] [] [] []) :=
    haltList_M _
  rw [← e1, ← e2] at h
  exact h

lemma poly_eval (n : ℕ) :
    (Polynomial.X * (Polynomial.C 13 * (Polynomial.X * (Polynomial.C 3 * Polynomial.X + Polynomial.C 4) + Polynomial.C 2 * Polynomial.X + Polynomial.C 3 + Polynomial.C 1) + Polynomial.C 5 * Polynomial.X + Polynomial.C 7) + Polynomial.C 4 * Polynomial.X + Polynomial.C 7 : Polynomial ℕ).eval n = totalT n := by
  simp [totalT, frobT, mulT]

end Eval

open Eval in
/-- The quadratic character of the encoded field element is computable in polynomial time. -/
theorem evalMid_polyTime : ComplexityTheory.IsPolyTime evalMid := by
  refine ⟨{ tm := M
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := (Polynomial.X * (Polynomial.C 13 * (Polynomial.X * (Polynomial.C 3 * Polynomial.X + Polynomial.C 4) + Polynomial.C 2 * Polynomial.X + Polynomial.C 3 + Polynomial.C 1) + Polynomial.C 5 * Polynomial.X + Polynomial.C 7) + Polynomial.C 4 * Polynomial.X + Polynomial.C 7 : Polynomial ℕ)
            outputsFun := fun x => ?_ }⟩
  have hin : List.map ((Equiv.refl Bool : M.Γ M.k₀ ≃ Bool).invFun)
      ((BitstringEncoding.toEncoding (α := Mid)).encode x) = x.bits := List.map_id _
  have hout : List.map ((Equiv.refl Bool : M.Γ M.k₁ ≃ Bool).invFun)
      ((BitstringEncoding.toEncoding (α := Bool)).encode (evalMid x)) = [evalFn x.bits] :=
    List.map_id _
  have hb : totalT (dec x.bits).length ≤ (Polynomial.X * (Polynomial.C 13 * (Polynomial.X * (Polynomial.C 3 * Polynomial.X + Polynomial.C 4) + Polynomial.C 2 * Polynomial.X + Polynomial.C 3 + Polynomial.C 1) + Polynomial.C 5 * Polynomial.X + Polynomial.C 7) + Polynomial.C 4 * Polynomial.X + Polynomial.C 7 : Polynomial ℕ).eval
      ((BitstringEncoding.toEncoding (α := Mid)).encode x).length := by
    rw [poly_eval]
    exact totalT_mono (dec_length_le x.bits)
  have key : ∀ l l' : List Bool, l = x.bits → l' = [evalFn x.bits] →
      TM2OutputsInTime M l (some l') ((Polynomial.X * (Polynomial.C 13 * (Polynomial.X * (Polynomial.C 3 * Polynomial.X + Polynomial.C 4) + Polynomial.C 2 * Polynomial.X + Polynomial.C 3 + Polynomial.C 1) + Polynomial.C 5 * Polynomial.X + Polynomial.C 7) + Polynomial.C 4 * Polynomial.X + Polynomial.C 7 : Polynomial ℕ).eval
        ((BitstringEncoding.toEncoding (α := Mid)).encode x).length) := by
    rintro l l' rfl rfl
    exact Classical.choice (by
      obtain ⟨n, hle, he⟩ := (full_run x.bits).mono hb
      exact ⟨⟨⟨n, he⟩, hle⟩⟩)
  exact key _ _ hin hout

end Erdos78Paley

end PartEval

section PartBridge

/-!
Algebraic bridge for the Paley split of Erdos 78: the abstract quadratic residue test in
F_13[x]/(x^m - 2), m a power of 3, agrees with the concrete list algorithm of the spec file.
Block 1 (ListAlgebra): the list operations compute products modulo x^m - 2, in any ring with x^m = 2.
Block 2 (FieldCore): Euler criterion via the norm down to F_13, in any field with 13^m elements.
Block 3 (Glue): the two blocks instantiated at AdjoinRoot (X^m - 2).
-/

open Polynomial

namespace Erdos78Paley

/-- Value at the point x of the polynomial whose coefficient list (constant term first) is l. -/
def ev {K : Type} [CommRing K] [Algebra F K] (x : K) : List F → K
  | [] => 0
  | c :: l => algebraMap F K c + x * ev x l

section ListAlgebra

variable {K : Type} [CommRing K] [Algebra F K] (x : K)

theorem ev_append (l r : List F) : ev x (l ++ r) = ev x l + x ^ l.length * ev x r := by
  induction l with
  | nil => simp [ev]
  | cons c l ih =>
    simp only [List.cons_append, ev, ih, List.length_cons, pow_succ]
    ring

theorem mulX_concat (l : List F) (t : F) : mulX (l ++ [t]) = (2 * t) :: l := by
  simp [mulX]

theorem length_mulX (a : List F) : (mulX a).length = a.length := by
  rcases List.eq_nil_or_concat a with rfl | ⟨l, t, rfl⟩
  · rfl
  · rw [List.concat_eq_append, mulX_concat]
    simp

theorem ev_mulX (m : ℕ) (hx : x ^ m = 2) (a : List F) (ha : a.length = m) :
    ev x (mulX a) = x * ev x a := by
  rcases List.eq_nil_or_concat a with rfl | ⟨l, t, rfl⟩
  · simp [mulX, ev]
  · rw [List.concat_eq_append] at ha ⊢
    rw [mulX_concat, ev_append]
    simp only [List.length_append, List.length_singleton] at ha
    have h2 : x ^ (l.length + 1) = 2 := by rw [ha]; exact hx
    simp only [ev, map_mul, map_ofNat]
    linear_combination (-(algebraMap F K t)) * h2

theorem ev_zipWith (c : F) (l1 l2 : List F) (h : l1.length = l2.length) :
    ev x (List.zipWith (fun r s => r + c * s) l1 l2) =
      ev x l1 + algebraMap F K c * ev x l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp [ev]
    | cons b l2 => simp at h
  | cons a l1 ih =>
    cases l2 with
    | nil => simp at h
    | cons b l2 =>
      simp only [List.zipWith_cons_cons, ev, map_add, map_mul]
      rw [ih l2 (by simpa using h)]
      ring

theorem length_hstep (b acc : List F) (c : F) (h : acc.length = b.length) :
    (hstep b acc c).length = b.length := by
  simp [hstep, length_mulX, h]

theorem ev_hstep (m : ℕ) (hx : x ^ m = 2) (b acc : List F) (c : F) (hb : b.length = m)
    (hacc : acc.length = m) :
    ev x (hstep b acc c) = x * ev x acc + algebraMap F K c * ev x b := by
  unfold hstep
  rw [ev_zipWith x c _ _ (by rw [length_mulX, hacc, hb]), ev_mulX x m hx acc hacc]

theorem length_mul (a b : List F) : (mul a b).length = b.length := by
  induction a with
  | nil => simp [mul]
  | cons c a ih =>
    show (hstep b (mul a b) c).length = b.length
    exact length_hstep b _ c ih

theorem ev_replicate_zero (n : ℕ) : ev x (List.replicate n (0 : F)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ev, ih]

theorem ev_mul (m : ℕ) (hx : x ^ m = 2) (a b : List F) (hb : b.length = m) :
    ev x (mul a b) = ev x a * ev x b := by
  induction a with
  | nil => simp [mul, ev, ev_replicate_zero]
  | cons c a ih =>
    show ev x (hstep b (mul a b) c) = _
    rw [ev_hstep x m hx b _ c hb (by rw [length_mul, hb]), ih]
    simp only [ev]
    ring

theorem length_iter_mul (y w : List F) (k : ℕ) (hk : 0 < k) :
    ((fun z => mul z y)^[k] w).length = y.length := by
  cases k with
  | zero => omega
  | succ k =>
    rw [Function.iterate_succ_apply']
    exact length_mul _ _

theorem ev_iter_mul (m : ℕ) (hx : x ^ m = 2) (y w : List F) (hy : y.length = m) (k : ℕ) :
    ev x ((fun z => mul z y)^[k] w) = ev x w * ev x y ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ev_mul x m hx _ _ hy, ih, pow_succ, mul_assoc]

theorem length_frob (w y : List F) : (frob w y).length = y.length :=
  length_iter_mul y w 13 (by norm_num)

theorem ev_frob (m : ℕ) (hx : x ^ m = 2) (w y : List F) (hy : y.length = m) :
    ev x (frob w y) = ev x w * ev x y ^ 13 :=
  ev_iter_mul x m hx y w hy 13

theorem length_one (m : ℕ) : (one m).length = m := by
  cases m <;> simp [one]

theorem ev_one (m : ℕ) (hm : 0 < m) : ev x (one m) = 1 := by
  cases m with
  | zero => omega
  | succ m => simp [one, ev, ev_replicate_zero]

theorem iter_frob (m : ℕ) (hx : x ^ m = 2) (hm : 0 < m) (w : List F) (k : ℕ) :
    ((frob w)^[k] (one m)).length = m ∧
      ∃ e : ℕ, 12 * e + 1 = 13 ^ k ∧ ev x ((frob w)^[k] (one m)) = ev x w ^ e := by
  induction k with
  | zero => exact ⟨length_one m, 0, by norm_num, by simp [ev_one x m hm]⟩
  | succ k ih =>
    obtain ⟨hl, e, he, hev⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨by rw [length_frob, hl], 1 + 13 * e, by rw [pow_succ]; omega, ?_⟩
    rw [ev_frob x m hx _ _ hl, hev, pow_add, pow_one, mul_comm 13 e, pow_mul]

theorem normL_spec (m : ℕ) (hx : x ^ m = 2) (hm : 0 < m) (w : List F) (hw : w.length = m) :
    (normL w).length = m ∧ ∃ e : ℕ, 12 * e + 1 = 13 ^ m ∧ ev x (normL w) = ev x w ^ e := by
  unfold normL
  rw [hw]
  exact iter_frob x m hx hm w m

end ListAlgebra

section FieldCore

theorem field_core {K : Type} [Field K] [Algebra F K] [Fintype K] (m e : ℕ) (hm : 0 < m)
    (hcard : Fintype.card K = 13 ^ m) (he : 12 * e + 1 = 13 ^ m) (w : K) :
    ∃ c : F, w ^ e = algebraMap F K c ∧ (IsSquare w ↔ c = 0 ∨ c ^ 6 = 1) := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hinj : Function.Injective (algebraMap F K) := (algebraMap F K).injective
  have : CharP K 13 := charP_of_injective_algebraMap hinj 13
  have h13 : 13 ^ 1 ≤ 13 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have he1 : 1 ≤ e := by omega
  have hfix : (w ^ e) ^ 13 = w ^ e := by
    by_cases hw : w = 0
    · subst hw
      simp [zero_pow (by omega : e ≠ 0)]
    · have h1 := FiniteField.pow_card_sub_one_eq_one w hw
      have h2 : Fintype.card K - 1 = 12 * e := by omega
      rw [h2] at h1
      rw [← pow_mul, show e * 13 = 12 * e + e by ring, pow_add, h1, one_mul]
  have hmem : w ^ e ∈ (⊥ : Subfield K) := (Subfield.mem_bot_iff_pow_eq_self K 13).2 hfix
  rw [← ZMod.fieldRange_castHom_eq_bot 13] at hmem
  obtain ⟨c, hc⟩ := RingHom.mem_fieldRange.1 hmem
  have hc' : w ^ e = algebraMap F K c := by
    rw [← hc]
    exact congrArg (fun g : F →+* K => g c) (RingHom.ext_zmod _ _)
  refine ⟨c, hc', ?_⟩
  by_cases hw : w = 0
  · subst hw
    rw [zero_pow (by omega : e ≠ 0)] at hc'
    have hc0 : c = 0 := hinj (by rw [← hc', map_zero])
    simp [hc0]
  · have hchar : ringChar K ≠ 2 := by
      intro h
      have := FiniteField.even_card_iff_char_two.1 h
      omega
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc'
      exact hw (pow_eq_zero_iff (by omega : e ≠ 0) |>.1 hc')
    rw [FiniteField.isSquare_iff hchar hw, show Fintype.card K / 2 = e * 6 by omega, pow_mul, hc',
      ← map_pow]
    constructor
    · intro h
      exact Or.inr (hinj (by rw [h, map_one]))
    · rintro (h | h)
      · exact absurd h hc0
      · rw [h, map_one]

end FieldCore

section Glue

theorem no_cube : ∀ b : ZMod 13, b ^ 3 ≠ 2 := by decide

theorem irr (j : ℕ) : Irreducible (X ^ 3 ^ j - C 2 : (ZMod 13)[X]) := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact X_pow_sub_C_irreducible_of_prime_pow Nat.prime_three (by norm_num) j no_cube

theorem card_K (m : ℕ) (hm : 0 < m) :
    Nat.card (AdjoinRoot (X ^ m - C 2 : (ZMod 13)[X])) = 13 ^ m := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hmon : (X ^ m - C 2 : (ZMod 13)[X]).Monic := monic_X_pow_sub_C 2 hm.ne'
  have := hmon.finite_adjoinRoot
  rw [Module.natCard_eq_pow_finrank (K := ZMod 13), Nat.card_zmod]
  congr 1
  exact (finrank_quotient_span_eq_natDegree (f := (X ^ m - C 2 : (ZMod 13)[X]))).trans
    natDegree_X_pow_sub_C

theorem dec_flatMap (g h : ℕ → Bool) (l : List ℕ) :
    dec (l.flatMap (fun i => [g i, h i])) = l.map (fun i => bF (g i) - bF (h i)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, dec, ih]

theorem ev_range (g : ℕ → F) (m : ℕ) :
    ev (X : (ZMod 13)[X]) ((List.range m).map g) = ∑ i ∈ Finset.range m, C (g i) * X ^ i := by
  induction m with
  | zero => simp [ev]
  | succ m ih =>
    rw [List.range_succ, List.map_append, ev_append, ih, Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, ev, List.length_map, List.length_range, mul_zero,
      add_zero, Polynomial.algebraMap_eq]
    rw [mul_comm]

theorem ev_dec_setup (m u v : ℕ) :
    ev (X : (ZMod 13)[X])
        (dec ((List.range m).flatMap (fun i => [u.testBit i, v.testBit i]))) =
      (∑ i ∈ Finset.range m, if u.testBit i then X ^ i else 0) -
        (∑ i ∈ Finset.range m, if v.testBit i then X ^ i else 0) := by
  rw [dec_flatMap, ev_range, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases u.testBit i <;> cases v.testBit i <;> simp [bF]

theorem length_dec_setup (m u v : ℕ) :
    (dec ((List.range m).flatMap (fun i => [u.testBit i, v.testBit i]))).length = m := by
  rw [dec_flatMap]
  simp

theorem coeff_ev (l : List F) (n : ℕ) : (ev (X : (ZMod 13)[X]) l).coeff n = l.getD n 0 := by
  induction l generalizing n with
  | nil => simp [ev]
  | cons c l ih =>
    cases n with
    | zero => simp [ev]
    | succ n => simp [ev, ih, coeff_X_mul, coeff_C_succ]

theorem degree_ev_lt (l : List F) (m : ℕ) (hl : l.length = m) :
    (ev (X : (ZMod 13)[X]) l).degree < m := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [coeff_ev]
  exact List.getD_eq_default _ _ (by omega)

theorem mk_ev (f : (ZMod 13)[X]) (l : List F) :
    AdjoinRoot.mk f (ev X l) = ev (AdjoinRoot.mk f X) l := by
  induction l with
  | nil => simp [ev]
  | cons c l ih => simp [ev, ih, AdjoinRoot.algebraMap_eq]

theorem mk_inj (m : ℕ) (hm : 0 < m) (a b : (ZMod 13)[X]) (ha : a.degree < m) (hb : b.degree < m)
    (h : AdjoinRoot.mk (X ^ m - C 2 : (ZMod 13)[X]) a = AdjoinRoot.mk (X ^ m - C 2) b) :
    a = b := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hd : (X ^ m - C 2 : (ZMod 13)[X]) ∣ a - b := AdjoinRoot.mk_eq_mk.1 h
  have hdeg : (a - b).degree < (X ^ m - C 2 : (ZMod 13)[X]).degree := by
    rw [Polynomial.degree_X_pow_sub_C hm]
    exact (Polynomial.degree_sub_le a b).trans_lt (max_lt ha hb)
  exact sub_eq_zero.1 (Polynomial.eq_zero_of_dvd_of_degree_lt hd hdeg)

theorem bridge_core (j u v : ℕ) :
    @decide (IsSquare (AdjoinRoot.mk (X ^ 3 ^ j - C 2 : (ZMod 13)[X])
      ((∑ i ∈ Finset.range (3 ^ j), if u.testBit i then X ^ i else 0) -
       (∑ i ∈ Finset.range (3 ^ j), if v.testBit i then X ^ i else 0))))
      (Classical.propDecidable _) =
      evalFn ((List.range (3 ^ j)).flatMap (fun i => [u.testBit i, v.testBit i])) := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have : Fact (Irreducible (X ^ 3 ^ j - C 2 : (ZMod 13)[X])) := ⟨irr j⟩
  have hm : 0 < 3 ^ j := by positivity
  generalize hmdef : 3 ^ j = m at *
  have hx : (AdjoinRoot.mk (X ^ m - C 2 : (ZMod 13)[X]) X) ^ m = 2 := by
    have h0 := AdjoinRoot.mk_self (f := (X ^ m - C 2 : (ZMod 13)[X]))
    rw [map_sub, map_pow, sub_eq_zero] at h0
    rw [h0, AdjoinRoot.mk_C]
    exact map_ofNat (AdjoinRoot.of _) 2
  have hwl := length_dec_setup m u v
  rw [← ev_dec_setup m u v, mk_ev]
  unfold evalFn isSq
  generalize dec ((List.range m).flatMap (fun i => [u.testBit i, v.testBit i])) = wl at *
  obtain ⟨hlen, e, he, hev⟩ := normL_spec _ m hx hm wl hwl
  have : Finite (AdjoinRoot (X ^ m - C 2 : (ZMod 13)[X])) :=
    Nat.finite_of_card_ne_zero (by rw [card_K m hm]; positivity)
  let := Fintype.ofFinite (AdjoinRoot (X ^ m - C 2 : (ZMod 13)[X]))
  have hcard : Fintype.card (AdjoinRoot (X ^ m - C 2 : (ZMod 13)[X])) = 13 ^ m := by
    rw [← Nat.card_eq_fintype_card, card_K m hm]
  obtain ⟨c, hc, hsq⟩ := field_core m e hm hcard he
    (ev (AdjoinRoot.mk (X ^ m - C 2 : (ZMod 13)[X]) X) wl)
  have hN : ev (X : (ZMod 13)[X]) (normL wl) = C c := by
    apply mk_inj m hm _ _ (degree_ev_lt _ m hlen)
      (lt_of_le_of_lt degree_C_le (by exact_mod_cast hm))
    rw [mk_ev, hev, hc, AdjoinRoot.algebraMap_eq]
    rfl
  have hhead : (normL wl).headD 0 = c := by
    have h0 := coeff_ev (normL wl) 0
    rw [hN, coeff_C_zero] at h0
    rw [h0]
    cases normL wl <;> rfl
  rw [hhead]
  exact decide_eq_decide.2 hsq

end Glue

theorem bridge (p : ℕ × ℕ × ℕ) :
    @decide (IsSquare (AdjoinRoot.mk (X ^ 3 ^ Nat.clog 3 (Nat.size p.1) - C 2 : (ZMod 13)[X])
      ((∑ i ∈ Finset.range (3 ^ Nat.clog 3 (Nat.size p.1)), if p.2.1.testBit i then X ^ i else 0) -
       (∑ i ∈ Finset.range (3 ^ Nat.clog 3 (Nat.size p.1)), if p.2.2.testBit i then X ^ i else 0))))
      (Classical.propDecidable _) = Erdos78Paley.evalMid (Erdos78Paley.setupFn p) :=
  bridge_core (Nat.clog 3 (Nat.size p.1)) p.2.1 p.2.2

end Erdos78Paley

end PartBridge

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1.H2 := by
  have e : OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1.H2 = ComplexityTheory.IsPolyTime
      (fun p : ℕ × ℕ × ℕ => Erdos78Paley.evalMid (Erdos78Paley.setupFn p)) := by
    unfold OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1.H2
    exact congrArg _ (funext Erdos78Paley.bridge)
  rw [e]
  exact Erdos78Comp.comp_polyTime Erdos78Paley.setupFn Erdos78Paley.evalMid
    Erdos78Paley.setupFn_polyTime Erdos78Paley.evalMid_polyTime
