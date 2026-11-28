import OMAReductions.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R2

-- Proof of step H3 of the range avoidance split (single file).

-- ===== part: H3 =====
section
/-! Polynomial-time computable functions (FinTM2 model) are closed under pairing, composition
and precomposition with the first projection; the machines are built by hand. -/

open ComplexityTheory
open Turing Computability

namespace Erdos78Pair

/- Reachability of a configuration within a step budget, as a Prop. -/

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

/- Growth of stacks: one step pushes at most a bounded number of symbols. -/

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

lemma initList_stk (M : FinTM2) (s : List (M.Γ M.k₀)) :
    (initList M s).stk = Function.update (fun _ => []) M.k₀ s := by
  funext k
  by_cases h : k = M.k₀
  · subst h
    simp [initList]
  · simp [initList, h]

lemma haltList_stk (M : FinTM2) (s : List (M.Γ M.k₁)) :
    (haltList M s).stk = Function.update (fun _ => []) M.k₁ s := by
  funext k
  by_cases h : k = M.k₁
  · subst h
    simp [haltList]
  · simp [haltList, h]

lemma initList_eq (M : FinTM2) (s : List (M.Γ M.k₀)) :
    (⟨some M.main, M.initialState, Function.update (fun _ => []) M.k₀ s⟩ :
      TM2.Cfg M.Γ M.Λ M.σ) = initList M s := by
  have : initList M s = ⟨some M.main, M.initialState, (initList M s).stk⟩ := rfl
  rw [this, initList_stk]

lemma foldl_delimit {Γ : Type} (e : Bool → Γ) (s t : List Bool) :
    s.reverse.foldl (fun acc b => e true :: e b :: acc) (e false :: t.map e) =
      (BitstringEncoding.delimit s ++ t).map e := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [List.foldl_append, BitstringEncoding.delimit, ih]

/- The pairing machine. Stacks: inl false is the input stack, inl true a scratch stack,
then the stacks of M and the stacks of N. The output stack is the output stack of N. -/

namespace Pr

inductive Ph
  | a
  | b
  | c
  | d
  deriving DecidableEq

instance : Fintype Ph :=
  ⟨{Ph.a, Ph.b, Ph.c, Ph.d}, by intro x; cases x <;> simp⟩

variable (M N : FinTM2) (eMi : M.Γ M.k₀ ≃ Bool) (eMo : M.Γ M.k₁ ≃ Bool)
  (eNi : N.Γ N.k₀ ≃ Bool) (eNo : N.Γ N.k₁ ≃ Bool)

abbrev PK : Type := Bool ⊕ (M.K ⊕ N.K)

abbrev PL : Type := M.Λ ⊕ (N.Λ ⊕ Ph)

abbrev PV : Type := M.σ × N.σ × Option Bool

abbrev PG : PK M N → Type := fun k =>
  Sum.casesOn (motive := fun _ => Type) k (fun _ => Bool)
    (fun k' => Sum.casesOn (motive := fun _ => Type) k' M.Γ N.Γ)

def pliftM : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (PG M N) (PL M N) (PV M N)
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun v => f v.1) (pliftM q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun v o => (f v.1 o, v.2)) (pliftM q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun v o => (f v.1 o, v.2)) (pliftM q)
  | .load a q => .load (fun v => (a v.1, v.2)) (pliftM q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (pliftM q₁) (pliftM q₂)
  | .goto f => .goto (fun v => Sum.inl (f v.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inl N.main))

def pliftN : TM2.Stmt N.Γ N.Λ N.σ → TM2.Stmt (PG M N) (PL M N) (PV M N)
  | .push k f q => .push (Sum.inr (Sum.inr k)) (fun v => f v.2.1) (pliftN q)
  | .peek k f q => .peek (Sum.inr (Sum.inr k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (pliftN q)
  | .pop k f q => .pop (Sum.inr (Sum.inr k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (pliftN q)
  | .load a q => .load (fun v => (v.1, a v.2.1, v.2.2)) (pliftN q)
  | .branch f q₁ q₂ => .branch (fun v => f v.2.1) (pliftN q₁) (pliftN q₂)
  | .goto f => .goto (fun v => Sum.inr (Sum.inl (f v.2.1)))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr Ph.c))

def pprog : PL M N → TM2.Stmt (PG M N) (PL M N) (PV M N)
  | Sum.inl l => pliftM M N (M.m l)
  | Sum.inr (Sum.inl l) => pliftN M N (N.m l)
  | Sum.inr (Sum.inr Ph.a) =>
    .pop (Sum.inl false) (fun v (o : Option Bool) => (v.1, v.2.1, o)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inl true) (fun v => v.2.2.getD false) <|
          .goto fun _ => Sum.inr (Sum.inr Ph.a))
        (.goto fun _ => Sum.inr (Sum.inr Ph.b))
  | Sum.inr (Sum.inr Ph.b) =>
    .pop (Sum.inl true) (fun v (o : Option Bool) => (v.1, v.2.1, o)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inr (Sum.inl M.k₀)) (fun v => eMi.symm (v.2.2.getD false)) <|
          .push (Sum.inr (Sum.inr N.k₀)) (fun v => eNi.symm (v.2.2.getD false)) <|
          .goto fun _ => Sum.inr (Sum.inr Ph.b))
        (.goto fun _ => Sum.inl M.main)
  | Sum.inr (Sum.inr Ph.c) =>
    .pop (Sum.inr (Sum.inl M.k₁)) (fun v (o : Option (M.Γ M.k₁)) => (v.1, v.2.1, o.map eMo)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inl true) (fun v => v.2.2.getD false) <|
          .goto fun _ => Sum.inr (Sum.inr Ph.c))
        (.push (Sum.inr (Sum.inr N.k₁)) (fun _ => eNo.symm false) <|
          .goto fun _ => Sum.inr (Sum.inr Ph.d))
  | Sum.inr (Sum.inr Ph.d) =>
    .pop (Sum.inl true) (fun v (o : Option Bool) => (v.1, v.2.1, o)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inr (Sum.inr N.k₁)) (fun v => eNo.symm (v.2.2.getD false)) <|
          .push (Sum.inr (Sum.inr N.k₁)) (fun _ => eNo.symm true) <|
          .goto fun _ => Sum.inr (Sum.inr Ph.d))
        .halt

def PM : FinTM2 :=
  letI := M.kFin
  letI := N.kFin
  letI := M.ΛFin
  letI := N.ΛFin
  letI := M.σFin
  letI := N.σFin
  { K := PK M N
    k₀ := Sum.inl false
    k₁ := Sum.inr (Sum.inr N.k₁)
    Γ := PG M N
    Λ := PL M N
    main := Sum.inr (Sum.inr Ph.a)
    σ := PV M N
    initialState := (M.initialState, N.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := pprog M N eMi eMo eNi eNo }

def pmk (i z : List Bool) (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) :
    ∀ k : PK M N, List (PG M N k)
  | Sum.inl false => i
  | Sum.inl true => z
  | Sum.inr (Sum.inl k) => SM k
  | Sum.inr (Sum.inr k) => SN k

def pliftCfgM (SN : ∀ k, List (N.Γ k)) (c : TM2.Cfg M.Γ M.Λ M.σ) :
    TM2.Cfg (PG M N) (PL M N) (PV M N) :=
  ⟨some (c.l.elim (Sum.inr (Sum.inl N.main)) Sum.inl), (c.var, N.initialState, none),
    pmk M N [] [] c.stk SN⟩

def pliftCfgN (SM : ∀ k, List (M.Γ k)) (c : TM2.Cfg N.Γ N.Λ N.σ) :
    TM2.Cfg (PG M N) (PL M N) (PV M N) :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr Ph.c)) (fun l => Sum.inr (Sum.inl l))),
    (M.initialState, c.var, none), pmk M N [] [] SM c.stk⟩

def pcfg (p : Ph) (o : Option Bool) (i z : List Bool) (SM : ∀ k, List (M.Γ k))
    (SN : ∀ k, List (N.Γ k)) : TM2.Cfg (PG M N) (PL M N) (PV M N) :=
  ⟨some (Sum.inr (Sum.inr p)), (M.initialState, N.initialState, o), pmk M N i z SM SN⟩

def pfin (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) :
    TM2.Cfg (PG M N) (PL M N) (PV M N) :=
  ⟨none, (M.initialState, N.initialState, none), pmk M N [] [] SM SN⟩

variable {M N} {eMi eMo eNi eNo}

lemma pupd_I (i z : List Bool) (i' : List (PG M N (Sum.inl false)))
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) :
    Function.update (pmk M N i z SM SN) (Sum.inl false) i' = pmk M N i' z SM SN := by
  funext k
  rcases k with (_ | _) | k | k <;> simp [Function.update, pmk]

lemma pupd_Z (i z : List Bool) (z' : List (PG M N (Sum.inl true)))
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) :
    Function.update (pmk M N i z SM SN) (Sum.inl true) z' = pmk M N i z' SM SN := by
  funext k
  rcases k with (_ | _) | k | k <;> simp [Function.update, pmk]

lemma pupd_M (i z : List Bool) (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (k : M.K)
    (v : List (PG M N (Sum.inr (Sum.inl k)))) :
    Function.update (pmk M N i z SM SN) (Sum.inr (Sum.inl k)) v =
      pmk M N i z (Function.update SM k v) SN := by
  funext k'
  rcases k' with (_ | _) | k' | k'
  · simp [Function.update, pmk]
  · simp [Function.update, pmk]
  · by_cases h : k' = k
    · subst h
      simp [Function.update, pmk]
    · simp [Function.update, pmk, h]
  · simp [Function.update, pmk]

lemma pupd_N (i z : List Bool) (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (k : N.K)
    (v : List (PG M N (Sum.inr (Sum.inr k)))) :
    Function.update (pmk M N i z SM SN) (Sum.inr (Sum.inr k)) v =
      pmk M N i z SM (Function.update SN k v) := by
  funext k'
  rcases k' with (_ | _) | k' | k'
  · simp [Function.update, pmk]
  · simp [Function.update, pmk]
  · simp [Function.update, pmk]
  · by_cases h : k' = k
    · subst h
      simp [Function.update, pmk]
    · simp [Function.update, pmk, h]

/- Simulation of the two machines inside the pairing machine. -/

lemma pstepAux_liftM (SN : ∀ k, List (N.Γ k)) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ)
    (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (pliftM M N q) (v, N.initialState, none) (pmk M N [] [] S SN) =
      pliftCfgM M N SN (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [pliftM, TM2.stepAux]
    rw [pupd_M]
    exact ih _ _
  | peek k f q ih =>
    simp only [pliftM, TM2.stepAux]
    exact ih _ _
  | pop k f q ih =>
    simp only [pliftM, TM2.stepAux]
    rw [pupd_M]
    exact ih _ _
  | load a q ih =>
    simp only [pliftM, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [pliftM, TM2.stepAux, ih₁, ih₂]
    cases f v <;> rfl
  | goto f => rfl
  | halt => rfl

lemma pstep_liftM (SN : ∀ k, List (N.Γ k)) {c c' : TM2.Cfg M.Γ M.Λ M.σ}
    (h : M.step c = some c') :
    (PM M N eMi eMo eNi eNo).step (pliftCfgM M N SN c) = some (pliftCfgM M N SN c') := by
  rcases c with ⟨_ | l, v, S⟩
  · exact absurd h (by simp [FinTM2.step, TM2.step])
  · have h' : some (TM2.stepAux (M.m l) v S) = some c' := h
    injection h' with h'
    subst h'
    show some (TM2.stepAux (pliftM M N (M.m l)) (v, N.initialState, none)
      (pmk M N [] [] S SN)) = _
    exact congrArg some (pstepAux_liftM SN (M.m l) v S)

lemma piterate_liftM (SN : ∀ k, List (N.Γ k)) (n : ℕ) (c c' : TM2.Cfg M.Γ M.Λ M.σ)
    (h : (flip bind M.step)^[n] (some c) = some c') :
    (flip bind (PM M N eMi eMo eNi eNo).step)^[n] (some (pliftCfgM M N SN c)) =
      some (pliftCfgM M N SN c') := by
  induction n generalizing c with
  | zero =>
    have h' : some c = some c' := h
    injection h' with h'
    subst h'
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    change (flip bind M.step)^[n] (M.step c) = some c' at h
    change (flip bind (PM M N eMi eMo eNi eNo).step)^[n]
      ((PM M N eMi eMo eNi eNo).step (pliftCfgM M N SN c)) = _
    cases hs : M.step c with
    | none =>
      rw [hs, iterate_none] at h
      exact absurd h (by simp)
    | some c₁ =>
      rw [hs] at h
      rw [pstep_liftM SN hs]
      exact ih c₁ h

lemma pstepAux_liftN (SM : ∀ k, List (M.Γ k)) (q : TM2.Stmt N.Γ N.Λ N.σ) (v : N.σ)
    (S : ∀ k, List (N.Γ k)) :
    TM2.stepAux (pliftN M N q) (M.initialState, v, none) (pmk M N [] [] SM S) =
      pliftCfgN M N SM (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [pliftN, TM2.stepAux]
    rw [pupd_N]
    exact ih _ _
  | peek k f q ih =>
    simp only [pliftN, TM2.stepAux]
    exact ih _ _
  | pop k f q ih =>
    simp only [pliftN, TM2.stepAux]
    rw [pupd_N]
    exact ih _ _
  | load a q ih =>
    simp only [pliftN, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [pliftN, TM2.stepAux, ih₁, ih₂]
    cases f v <;> rfl
  | goto f => rfl
  | halt => rfl

lemma pstep_liftN (SM : ∀ k, List (M.Γ k)) {c c' : TM2.Cfg N.Γ N.Λ N.σ}
    (h : N.step c = some c') :
    (PM M N eMi eMo eNi eNo).step (pliftCfgN M N SM c) = some (pliftCfgN M N SM c') := by
  rcases c with ⟨_ | l, v, S⟩
  · exact absurd h (by simp [FinTM2.step, TM2.step])
  · have h' : some (TM2.stepAux (N.m l) v S) = some c' := h
    injection h' with h'
    subst h'
    show some (TM2.stepAux (pliftN M N (N.m l)) (M.initialState, v, none)
      (pmk M N [] [] SM S)) = _
    exact congrArg some (pstepAux_liftN SM (N.m l) v S)

lemma piterate_liftN (SM : ∀ k, List (M.Γ k)) (n : ℕ) (c c' : TM2.Cfg N.Γ N.Λ N.σ)
    (h : (flip bind N.step)^[n] (some c) = some c') :
    (flip bind (PM M N eMi eMo eNi eNo).step)^[n] (some (pliftCfgN M N SM c)) =
      some (pliftCfgN M N SM c') := by
  induction n generalizing c with
  | zero =>
    have h' : some c = some c' := h
    injection h' with h'
    subst h'
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    change (flip bind N.step)^[n] (N.step c) = some c' at h
    change (flip bind (PM M N eMi eMo eNi eNo).step)^[n]
      ((PM M N eMi eMo eNi eNo).step (pliftCfgN M N SM c)) = _
    cases hs : N.step c with
    | none =>
      rw [hs, iterate_none] at h
      exact absurd h (by simp)
    | some c₁ =>
      rw [hs] at h
      rw [pstep_liftN SM hs]
      exact ih c₁ h

lemma prun_M (SN : ∀ k, List (N.Γ k)) {s : List (M.Γ M.k₀)} {out : List (M.Γ M.k₁)} {T : ℕ}
    (h : TM2OutputsInTime M s (some out) T) :
    RIn (PM M N eMi eMo eNi eNo).step (pliftCfgM M N SN (initList M s))
      (some (pliftCfgM M N SN (haltList M out))) T := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  exact ⟨n, hle, piterate_liftM SN n (initList M s) (haltList M out) hn⟩

lemma prun_N (SM : ∀ k, List (M.Γ k)) {s : List (N.Γ N.k₀)} {out : List (N.Γ N.k₁)} {T : ℕ}
    (h : TM2OutputsInTime N s (some out) T) :
    RIn (PM M N eMi eMo eNi eNo).step (pliftCfgN M N SM (initList N s))
      (some (pliftCfgN M N SM (haltList N out))) T := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  exact ⟨n, hle, piterate_liftN SM n (initList N s) (haltList N out) hn⟩

/- One step of each phase. -/

lemma pstep_a_cons (o : Option Bool) (c : Bool) (i z : List Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) :
    (PM M N eMi eMo eNi eNo).step (pcfg M N Ph.a o (c :: i) z SM SN) =
      some (pcfg M N Ph.a (some c) i (c :: z) SM SN) := by
  show some (TM2.stepAux (pprog M N eMi eMo eNi eNo (Sum.inr (Sum.inr Ph.a)))
    (M.initialState, N.initialState, o) (pmk M N (c :: i) z SM SN)) = _
  simp [pprog, TM2.stepAux, pmk, pupd_I, pupd_Z, pcfg]

lemma pstep_a_nil (o : Option Bool) (z : List Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) :
    (PM M N eMi eMo eNi eNo).step (pcfg M N Ph.a o [] z SM SN) =
      some (pcfg M N Ph.b none [] z SM SN) := by
  show some (TM2.stepAux (pprog M N eMi eMo eNi eNo (Sum.inr (Sum.inr Ph.a)))
    (M.initialState, N.initialState, o) (pmk M N [] z SM SN)) = _
  simp [pprog, TM2.stepAux, pmk, pupd_I, pupd_Z, pcfg]

lemma pstep_b_cons (o : Option Bool) (c : Bool) (z : List Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) :
    (PM M N eMi eMo eNi eNo).step (pcfg M N Ph.b o [] (c :: z) SM SN) =
      some (pcfg M N Ph.b (some c) [] z (Function.update SM M.k₀ (eMi.symm c :: SM M.k₀))
        (Function.update SN N.k₀ (eNi.symm c :: SN N.k₀))) := by
  show some (TM2.stepAux (pprog M N eMi eMo eNi eNo (Sum.inr (Sum.inr Ph.b)))
    (M.initialState, N.initialState, o) (pmk M N [] (c :: z) SM SN)) = _
  simp [pprog, TM2.stepAux, pmk, pupd_Z, pupd_M, pupd_N, pcfg]

lemma pstep_b_nil (o : Option Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) :
    (PM M N eMi eMo eNi eNo).step (pcfg M N Ph.b o [] [] SM SN) =
      some (pliftCfgM M N SN ⟨some M.main, M.initialState, SM⟩) := by
  show some (TM2.stepAux (pprog M N eMi eMo eNi eNo (Sum.inr (Sum.inr Ph.b)))
    (M.initialState, N.initialState, o) (pmk M N [] [] SM SN)) = _
  simp [pprog, TM2.stepAux, pmk, pupd_Z, pupd_M, pupd_N, pliftCfgM]

lemma pstep_c_cons (o : Option Bool) (c : M.Γ M.k₁) (s : List (M.Γ M.k₁)) (z : List Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (h : SM M.k₁ = c :: s) :
    (PM M N eMi eMo eNi eNo).step (pcfg M N Ph.c o [] z SM SN) =
      some (pcfg M N Ph.c (some (eMo c)) [] (eMo c :: z) (Function.update SM M.k₁ s) SN) := by
  show some (TM2.stepAux (pprog M N eMi eMo eNi eNo (Sum.inr (Sum.inr Ph.c)))
    (M.initialState, N.initialState, o) (pmk M N [] z SM SN)) = _
  simp [pprog, TM2.stepAux, pmk, pupd_Z, pupd_M, pupd_N, pcfg, h]

lemma pstep_c_nil (o : Option Bool) (z : List Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (h : SM M.k₁ = []) :
    (PM M N eMi eMo eNi eNo).step (pcfg M N Ph.c o [] z SM SN) =
      some (pcfg M N Ph.d none [] z (Function.update SM M.k₁ [])
        (Function.update SN N.k₁ (eNo.symm false :: SN N.k₁))) := by
  show some (TM2.stepAux (pprog M N eMi eMo eNi eNo (Sum.inr (Sum.inr Ph.c)))
    (M.initialState, N.initialState, o) (pmk M N [] z SM SN)) = _
  simp [pprog, TM2.stepAux, pmk, pupd_Z, pupd_M, pupd_N, pcfg, h]

lemma pstep_d_cons (o : Option Bool) (c : Bool) (z : List Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) :
    (PM M N eMi eMo eNi eNo).step (pcfg M N Ph.d o [] (c :: z) SM SN) =
      some (pcfg M N Ph.d (some c) [] z SM
        (Function.update SN N.k₁ (eNo.symm true :: eNo.symm c :: SN N.k₁))) := by
  show some (TM2.stepAux (pprog M N eMi eMo eNi eNo (Sum.inr (Sum.inr Ph.d)))
    (M.initialState, N.initialState, o) (pmk M N [] (c :: z) SM SN)) = _
  simp [pprog, TM2.stepAux, pmk, pupd_Z, pupd_N, pcfg]

lemma pstep_d_nil (o : Option Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) :
    (PM M N eMi eMo eNi eNo).step (pcfg M N Ph.d o [] [] SM SN) =
      some (pfin M N SM SN) := by
  show some (TM2.stepAux (pprog M N eMi eMo eNi eNo (Sum.inr (Sum.inr Ph.d)))
    (M.initialState, N.initialState, o) (pmk M N [] [] SM SN)) = _
  simp [pprog, TM2.stepAux, pmk, pupd_Z, pupd_N, pfin]

/- The four phases. -/

lemma prun_a (i : List Bool) (o : Option Bool) (z : List Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) :
    RIn (PM M N eMi eMo eNi eNo).step (pcfg M N Ph.a o i z SM SN)
      (some (pcfg M N Ph.b none [] (i.reverse ++ z) SM SN)) (i.length + 1) := by
  induction i generalizing o z with
  | nil => exact RIn.single (pstep_a_nil o z SM SN)
  | cons c i ih =>
    have h1 : RIn (PM M N eMi eMo eNi eNo).step _ _ 1 :=
      RIn.single (pstep_a_cons o c i z SM SN)
    have := RIn.trans h1 (ih (some c) (c :: z))
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

lemma prun_b (z : List Bool) (o : Option Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) :
    RIn (PM M N eMi eMo eNi eNo).step (pcfg M N Ph.b o [] z SM SN)
      (some (pliftCfgM M N
        (Function.update SN N.k₀ ((z.map eNi.symm).reverse ++ SN N.k₀))
        ⟨some M.main, M.initialState,
          Function.update SM M.k₀ ((z.map eMi.symm).reverse ++ SM M.k₀)⟩))
      (z.length + 1) := by
  induction z generalizing o SM SN with
  | nil =>
    simp only [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
    exact RIn.single (pstep_b_nil o SM SN)
  | cons c z ih =>
    have h1 : RIn (PM M N eMi eMo eNi eNo).step _ _ 1 :=
      RIn.single (pstep_b_cons o c z SM SN)
    have := RIn.trans h1 (ih (some c) _ _)
    simp only [Function.update_self, Function.update_idem] at this
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

lemma prun_c (s : List (M.Γ M.k₁)) (o : Option Bool) (z : List Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (h : SM M.k₁ = s) :
    RIn (PM M N eMi eMo eNi eNo).step (pcfg M N Ph.c o [] z SM SN)
      (some (pcfg M N Ph.d none [] ((s.map eMo).reverse ++ z) (Function.update SM M.k₁ [])
        (Function.update SN N.k₁ (eNo.symm false :: SN N.k₁)))) (s.length + 1) := by
  induction s generalizing o z SM with
  | nil => exact RIn.single (pstep_c_nil o z SM SN h)
  | cons c s ih =>
    have h1 : RIn (PM M N eMi eMo eNi eNo).step _ _ 1 :=
      RIn.single (pstep_c_cons o c s z SM SN h)
    have h2 := ih (some (eMo c)) (eMo c :: z) (Function.update SM M.k₁ s)
      (Function.update_self _ _ _)
    have := RIn.trans h1 h2
    simp only [Function.update_idem] at this
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

lemma prun_d (z : List Bool) (o : Option Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) :
    RIn (PM M N eMi eMo eNi eNo).step (pcfg M N Ph.d o [] z SM SN)
      (some (pfin M N SM (Function.update SN N.k₁
        (z.foldl (fun acc b => eNo.symm true :: eNo.symm b :: acc) (SN N.k₁)))))
      (z.length + 1) := by
  induction z generalizing o SN with
  | nil =>
    simp only [List.foldl_nil, Function.update_eq_self]
    exact RIn.single (pstep_d_nil o SM SN)
  | cons c z ih =>
    have h1 : RIn (PM M N eMi eMo eNi eNo).step _ _ 1 :=
      RIn.single (pstep_d_cons o c z SM SN)
    have := RIn.trans h1 (ih (some c) _)
    simp only [Function.update_self, Function.update_idem] at this
    simpa [Nat.add_comm] using this

/- Initial and final configurations. -/

lemma pinitList (x : List Bool) :
    initList (PM M N eMi eMo eNi eNo) x =
      pcfg M N Ph.a none x [] (fun _ => []) (fun _ => []) := by
  simp only [initList, pcfg]
  congr 1
  funext k
  rcases k with (_ | _) | k | k <;> rfl

lemma phaltList (w : List (N.Γ N.k₁)) :
    pfin M N (fun _ => []) (Function.update (fun _ => []) N.k₁ w) =
      haltList (PM M N eMi eMo eNi eNo) w := by
  simp only [pfin, haltList]
  congr 1
  funext k
  rcases k with (_ | _) | k | k
  · rfl
  · rfl
  · rfl
  · by_cases h : k = N.k₁
    · subst h
      simp [pmk]
      split
      · rfl
      · rename_i hne
        exact absurd rfl hne
    · simp [pmk, h]
      split
      · rename_i heq
        exact absurd (Sum.inr_injective (Sum.inr_injective
          (heq : (Sum.inr (Sum.inr k) : PK M N) = Sum.inr (Sum.inr N.k₁)))) h
      · rfl

/-- The pairing machine: on input x it runs M and N on x and outputs the delimited output of M
followed by the output of N. -/
lemma pair_run {x s t : List Bool} {T₁ T₂ : ℕ}
    (h₁ : TM2OutputsInTime M (List.map eMi.symm x) (some (List.map eMo.symm s)) T₁)
    (h₂ : TM2OutputsInTime N (List.map eNi.symm x) (some (List.map eNo.symm t)) T₂) :
    RIn (PM M N eMi eMo eNi eNo).step (initList (PM M N eMi eMo eNi eNo) x)
      (some (haltList (PM M N eMi eMo eNi eNo)
        (List.map eNo.symm (BitstringEncoding.delimit s ++ t))))
      ((x.length + 1) + (x.length + 1) + T₁ + T₂ + (s.length + 1) + (s.length + 1)) := by
  rw [pinitList]
  have a1 := prun_a (eMi := eMi) (eMo := eMo) (eNi := eNi) (eNo := eNo) x none []
    (fun _ => []) (fun _ => [])
  have a2 : RIn (PM M N eMi eMo eNi eNo).step
      (pcfg M N Ph.b none [] (x.reverse ++ []) (fun _ => []) (fun _ => []))
      (some (pliftCfgM M N (initList N (List.map eNi.symm x)).stk
        (initList M (List.map eMi.symm x)))) (x.length + 1) := by
    have := prun_b (eMi := eMi) (eMo := eMo) (eNi := eNi) (eNo := eNo) (x.reverse ++ []) none
      (fun _ => []) (fun _ => [])
    have e1 : (List.map eMi.symm (x.reverse ++ [])).reverse ++ [] = List.map eMi.symm x := by
      simp [List.map_reverse]
    have e2 : (List.map eNi.symm (x.reverse ++ [])).reverse ++ [] = List.map eNi.symm x := by
      simp [List.map_reverse]
    have e3 : (x.reverse ++ []).length = x.length := by simp
    rw [e1, e2, e3, initList_eq, ← initList_stk] at this
    exact this
  have a3 := prun_M (eMi := eMi) (eMo := eMo) (eNi := eNi) (eNo := eNo)
    (initList N (List.map eNi.symm x)).stk h₁
  have a4 : RIn (PM M N eMi eMo eNi eNo).step
      (pliftCfgM M N (initList N (List.map eNi.symm x)).stk (haltList M (List.map eMo.symm s)))
      (some (pcfg M N Ph.c none [] [] (haltList M (List.map eMo.symm s)).stk
        (haltList N (List.map eNo.symm t)).stk)) T₂ :=
    prun_N (eMi := eMi) (eMo := eMo) (eNi := eNi) (eNo := eNo)
      (haltList M (List.map eMo.symm s)).stk h₂
  have a5 : RIn (PM M N eMi eMo eNi eNo).step
      (pcfg M N Ph.c none [] [] (haltList M (List.map eMo.symm s)).stk
        (haltList N (List.map eNo.symm t)).stk)
      (some (pcfg M N Ph.d none [] s.reverse (fun _ => [])
        (Function.update (fun _ => []) N.k₁ (eNo.symm false :: List.map eNo.symm t))))
      (s.length + 1) := by
    have := prun_c (eMi := eMi) (eMo := eMo) (eNi := eNi) (eNo := eNo) (List.map eMo.symm s)
      none [] (haltList M (List.map eMo.symm s)).stk (haltList N (List.map eNo.symm t)).stk
      (haltList_stk_self M _)
    have e1 : (List.map eMo (List.map eMo.symm s)).reverse ++ [] = s.reverse := by simp
    have e2 : (List.map eMo.symm s).length = s.length := by simp
    rw [e1, e2, haltList_stk_update, haltList_stk_self, haltList_stk N, Function.update_idem]
      at this
    rw [haltList_stk N]
    exact this
  have a6 : RIn (PM M N eMi eMo eNi eNo).step
      (pcfg M N Ph.d none [] s.reverse (fun _ => [])
        (Function.update (fun _ => []) N.k₁ (eNo.symm false :: List.map eNo.symm t)))
      (some (haltList (PM M N eMi eMo eNi eNo)
        (List.map eNo.symm (BitstringEncoding.delimit s ++ t)))) (s.length + 1) := by
    have := prun_d (eMi := eMi) (eMo := eMo) (eNi := eNi) (eNo := eNo) s.reverse none
      (fun _ => [])
      (Function.update (fun _ => []) N.k₁ (eNo.symm false :: List.map eNo.symm t))
    have e1 : s.reverse.length = s.length := by simp
    rw [Function.update_self, Function.update_idem, foldl_delimit, e1, phaltList] at this
    exact this
  exact ((((a1.trans a2).trans a3).trans a4).trans a5).trans a6

end Pr

open Pr in
/-- Polynomial-time computable functions are closed under pairing. -/
theorem pair_polyTime {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] (f : α → β) (g : α → γ) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a : α => (f a, g a)) := by
  obtain ⟨M⟩ := hf
  obtain ⟨N⟩ := hg
  obtain ⟨B, hB⟩ := exists_pushBound M.tm
  refine ⟨{ tm := PM M.tm N.tm M.inputAlphabet M.outputAlphabet N.inputAlphabet N.outputAlphabet
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := N.outputAlphabet
            time := Polynomial.C 2 * (Polynomial.X + 1) + M.time + N.time +
              Polynomial.C 2 * (Polynomial.X + M.time * Polynomial.C B + 1)
            outputsFun := fun a => ?_ }⟩
  have hM := M.outputsFun a
  have hN := N.outputsFun a
  set x := (BitstringEncoding.toEncoding (α := α)).encode a with hx
  set s := (BitstringEncoding.toEncoding (α := β)).encode (f a) with hs
  set t := (BitstringEncoding.toEncoding (α := γ)).encode (g a) with ht
  have henc : (BitstringEncoding.toEncoding (α := β × γ)).encode (f a, g a) =
      BitstringEncoding.delimit s ++ t := rfl
  have hlen : s.length ≤ x.length + M.time.eval x.length * B := by
    have := out_len M.tm hB hM
    simpa using this
  have hrun := pair_run (M := M.tm) (N := N.tm) (eMi := M.inputAlphabet)
    (eMo := M.outputAlphabet) (eNi := N.inputAlphabet) (eNo := N.outputAlphabet)
    (x := x) (s := s) (t := t) hM hN
  have hb : (x.length + 1) + (x.length + 1) + M.time.eval x.length + N.time.eval x.length +
      (s.length + 1) + (s.length + 1) ≤
      (Polynomial.C 2 * (Polynomial.X + 1) + M.time + N.time +
        Polynomial.C 2 * (Polynomial.X + M.time * Polynomial.C B + 1)).eval x.length := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_one]
    generalize M.time.eval x.length * B = W at *
    omega
  have hin : List.map ((Equiv.refl Bool :
      (PM M.tm N.tm M.inputAlphabet M.outputAlphabet N.inputAlphabet N.outputAlphabet).Γ
        (PM M.tm N.tm M.inputAlphabet M.outputAlphabet N.inputAlphabet N.outputAlphabet).k₀ ≃
      Bool).invFun) x = x := List.map_id _
  have key : ∀ l : List Bool, l = x →
      TM2OutputsInTime
        (PM M.tm N.tm M.inputAlphabet M.outputAlphabet N.inputAlphabet N.outputAlphabet) l
        (some (List.map N.outputAlphabet.invFun
          ((BitstringEncoding.toEncoding (α := β × γ)).encode (f a, g a))))
        ((Polynomial.C 2 * (Polynomial.X + 1) + M.time + N.time +
          Polynomial.C 2 * (Polynomial.X + M.time * Polynomial.C B + 1)).eval x.length) := by
    rintro l rfl
    rw [henc]
    exact Classical.choice (by
      obtain ⟨n, hle, he⟩ := hrun.mono hb
      exact ⟨⟨⟨n, he⟩, hle⟩⟩)
  exact key _ hin

/- The composition machine. -/

namespace Cm

/- The composed machine. Stacks: the stacks of M, the stacks of N and one helper stack. -/

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

/- Simulation of the first machine. -/

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

/- Simulation of the second machine. -/

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

/- One step of each transfer phase. -/

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

/- The two transfer phases. -/

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

/- Initial and final configurations. -/

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

end Cm

open Cm in
/-- Polynomial-time computable functions are closed under composition. -/
theorem comp_polyTime {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
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


/- The first-projection machine: parse the first block of a pair, erase the rest, run M. -/

namespace Fs

/- The new machine. Stacks: `inl false` is the new input stack, `inl true` an auxiliary
stack, `inr k` the stack `k` of the simulated decider. -/

inductive Ph
  | parse
  | erase
  | move
  deriving DecidableEq

instance : Fintype Ph :=
  ⟨{Ph.parse, Ph.erase, Ph.move}, by intro x; cases x <;> simp⟩

variable (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool)

abbrev G : Bool ⊕ M.K → Type := fun k => Sum.casesOn (motive := fun _ => Type) k (fun _ => Bool) M.Γ

def liftStmt : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool)
  | .push k f q => .push (Sum.inr k) (fun v => f v.1) (liftStmt q)
  | .peek k f q => .peek (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftStmt q)
  | .pop k f q => .pop (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftStmt q)
  | .load a q => .load (fun v => (a v.1, v.2)) (liftStmt q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (liftStmt q₁) (liftStmt q₂)
  | .goto f => .goto (fun v => Sum.inl (f v.1))
  | .halt => .halt

def prog : M.Λ ⊕ Ph → TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool)
  | Sum.inl l => liftStmt M (M.m l)
  | Sum.inr .parse =>
    .pop (Sum.inl false) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2 == some true)
        (.pop (Sum.inl false) (fun v o => (v.1, o)) <|
          .push (Sum.inl true) (fun v => v.2.getD false) <| .goto fun _ => Sum.inr .parse)
        (.goto fun _ => Sum.inr .erase)
  | Sum.inr .erase =>
    .pop (Sum.inl false) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome) (.goto fun _ => Sum.inr .erase)
        (.goto fun _ => Sum.inr .move)
  | Sum.inr .move =>
    .pop (Sum.inl true) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inr M.k₀) (fun v => e.symm (v.2.getD false)) <|
          .goto fun _ => Sum.inr .move)
        (.goto fun _ => Sum.inl M.main)

def N : FinTM2 :=
  letI := M.kFin
  letI := M.ΛFin
  letI := M.σFin
  { K := Bool ⊕ M.K
    k₀ := Sum.inl false
    k₁ := Sum.inr M.k₁
    Γ := G M
    Λ := M.Λ ⊕ Ph
    main := Sum.inr .parse
    σ := M.σ × Option Bool
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := prog M e }

def mk (i a : List Bool) (S : ∀ k, List (M.Γ k)) : ∀ k : Bool ⊕ M.K, List (G M k)
  | Sum.inl false => i
  | Sum.inl true => a
  | Sum.inr k => S k

variable {M} {e}

lemma upd_inp (i a : List Bool) (i' : List (G M (Sum.inl false))) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk M i a S) (Sum.inl false) i' = mk M i' a S := by
  funext k
  rcases k with (_ | _) | k <;> simp [Function.update, mk]

lemma upd_aux (i a : List Bool) (a' : List (G M (Sum.inl true))) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk M i a S) (Sum.inl true) a' = mk M i a' S := by
  funext k
  rcases k with (_ | _) | k <;> simp [Function.update, mk]

lemma upd_inr (i a : List Bool) (S : ∀ k, List (M.Γ k)) (k : M.K) (v : List (G M (Sum.inr k))) :
    Function.update (mk M i a S) (Sum.inr k) v = mk M i a (Function.update S k v) := by
  funext k'
  rcases k' with (_ | _) | k'
  · simp [Function.update, mk]
  · simp [Function.update, mk]
  · by_cases h : k' = k
    · subst h
      simp [Function.update, mk]
    · simp [Function.update, mk, h]

def liftCfg (c : TM2.Cfg M.Γ M.Λ M.σ) : (N M e).Cfg :=
  ⟨c.l.map Sum.inl, (c.var, none), mk M [] [] c.stk⟩

def cfg (l : Ph) (o : Option Bool) (i a : List Bool) (S : ∀ k, List (M.Γ k)) : (N M e).Cfg :=
  ⟨some (Sum.inr l), (M.initialState, o), mk M i a S⟩

lemma stepAux_lift (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (liftStmt M q) (v, none) (mk M [] [] S) = liftCfg (e := e) (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [liftStmt, TM2.stepAux]
    rw [upd_inr]
    exact ih _ _
  | peek k f q ih =>
    simp only [liftStmt, TM2.stepAux]
    exact ih _ _
  | pop k f q ih =>
    simp only [liftStmt, TM2.stepAux]
    rw [upd_inr]
    exact ih _ _
  | load a q ih =>
    simp only [liftStmt, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [liftStmt, TM2.stepAux, ih₁, ih₂]
    cases f v <;> rfl
  | goto f => rfl
  | halt => rfl

lemma step_lift (c : TM2.Cfg M.Γ M.Λ M.σ) :
    (N M e).step (liftCfg c) = (M.step c).map liftCfg := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · show some (TM2.stepAux (liftStmt M (M.m l)) (v, none) (mk M [] [] S)) = _
    rw [stepAux_lift]
    rfl

lemma iterate_lift (n : ℕ) (o : Option (TM2.Cfg M.Γ M.Λ M.σ)) :
    (flip bind (N M e).step)^[n] (o.map liftCfg) = ((flip bind M.step)^[n] o).map liftCfg := by
  have hs : Function.Semiconj (Option.map (liftCfg (M := M) (e := e))) (flip bind M.step)
      (flip bind (N M e).step) := by
    intro o
    rcases o with _ | c
    · rfl
    · show (M.step c).map liftCfg = (N M e).step (liftCfg c)
      rw [step_lift]
  exact ((hs.iterate_right n) o).symm

/- One step of each phase. -/

lemma step_parse_false (o : Option Bool) (rest a : List Bool) (S : ∀ k, List (M.Γ k)) :
    (N M e).step (cfg .parse o (false :: rest) a S) = some (cfg .erase (some false) rest a S) := by
  show some (TM2.stepAux (prog M e (Sum.inr .parse)) (M.initialState, o)
    (mk M (false :: rest) a S)) = _
  simp [prog, TM2.stepAux, mk, upd_inp, upd_aux, upd_inr, cfg, liftCfg]
  rfl

lemma step_parse_true (o : Option Bool) (c : Bool) (rest a : List Bool)
    (S : ∀ k, List (M.Γ k)) :
    (N M e).step (cfg .parse o (true :: c :: rest) a S) =
      some (cfg .parse (some c) rest (c :: a) S) := by
  show some (TM2.stepAux (prog M e (Sum.inr .parse)) (M.initialState, o)
    (mk M (true :: c :: rest) a S)) = _
  simp [prog, TM2.stepAux, mk, upd_inp, upd_aux, upd_inr, cfg, liftCfg]
  rfl

lemma step_erase_cons (o : Option Bool) (b : Bool) (t a : List Bool) (S : ∀ k, List (M.Γ k)) :
    (N M e).step (cfg .erase o (b :: t) a S) = some (cfg .erase (some b) t a S) := by
  show some (TM2.stepAux (prog M e (Sum.inr .erase)) (M.initialState, o)
    (mk M (b :: t) a S)) = _
  simp [prog, TM2.stepAux, mk, upd_inp, upd_aux, upd_inr, cfg, liftCfg]
  rfl

lemma step_erase_nil (o : Option Bool) (a : List Bool) (S : ∀ k, List (M.Γ k)) :
    (N M e).step (cfg .erase o [] a S) = some (cfg .move none [] a S) := by
  show some (TM2.stepAux (prog M e (Sum.inr .erase)) (M.initialState, o) (mk M [] a S)) = _
  simp [prog, TM2.stepAux, mk, upd_inp, upd_aux, upd_inr, cfg, liftCfg]
  rfl

lemma step_move_cons (o : Option Bool) (c : Bool) (a : List Bool) (S : ∀ k, List (M.Γ k)) :
    (N M e).step (cfg .move o [] (c :: a) S) =
      some (cfg .move (some c) [] a
        (Function.update S M.k₀ (e.symm c :: S M.k₀))) := by
  show some (TM2.stepAux (prog M e (Sum.inr .move)) (M.initialState, o) (mk M [] (c :: a) S)) = _
  simp [prog, TM2.stepAux, mk, upd_inp, upd_aux, upd_inr, cfg, liftCfg]
  rfl

lemma step_move_nil (o : Option Bool) (S : ∀ k, List (M.Γ k)) :
    (N M e).step (cfg .move o [] [] S) = some (liftCfg ⟨some M.main, M.initialState, S⟩) := by
  show some (TM2.stepAux (prog M e (Sum.inr .move)) (M.initialState, o) (mk M [] [] S)) = _
  simp [prog, TM2.stepAux, mk, upd_inp, upd_aux, upd_inr, cfg, liftCfg]
  rfl

/- The three phases. -/

lemma parse_run (s : List Bool) (rest : List Bool) (a : List Bool) (o : Option Bool)
    (S : ∀ k, List (M.Γ k)) :
    RIn (N M e).step (cfg .parse o (BitstringEncoding.delimit s ++ rest) a S)
      (some (cfg .erase (some false) rest (s.reverse ++ a) S)) (s.length + 1) := by
  induction s generalizing a o with
  | nil => exact RIn.single (step_parse_false o rest a S)
  | cons c s ih =>
    have h1 := RIn.single (step_parse_true (M := M) (e := e) o c (BitstringEncoding.delimit s ++ rest) a S)
    have h2 := ih (c :: a) (some c)
    have := RIn.trans h1 h2
    simpa [BitstringEncoding.delimit, List.reverse_cons, List.append_assoc, Nat.add_comm] using this

lemma erase_run (t a : List Bool) (o : Option Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e).step (cfg .erase o t a S) (some (cfg .move none [] a S)) (t.length + 1) := by
  induction t generalizing o with
  | nil => exact RIn.single (step_erase_nil o a S)
  | cons b t ih =>
    have := RIn.trans (RIn.single (step_erase_cons (M := M) (e := e) o b t a S)) (ih (some b))
    simpa [Nat.add_comm] using this

lemma move_run (a : List Bool) (o : Option Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e).step (cfg .move o [] a S)
      (some (liftCfg ⟨some M.main, M.initialState,
        Function.update S M.k₀ ((a.map e.symm).reverse ++ S M.k₀)⟩))
      (a.length + 1) := by
  induction a generalizing o S with
  | nil =>
    simp only [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
    exact RIn.single (step_move_nil o S)
  | cons c a ih =>
    have := RIn.trans (RIn.single (step_move_cons (M := M) (e := e) o c a S)) (ih (some c) _)
    simp only [Function.update_self, Function.update_idem] at this
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

/- Initial and final configurations. -/

lemma initList_N (l : List Bool) :
    initList (N M e) l = cfg .parse none l [] (fun _ => []) := by
  simp only [initList, cfg]
  congr 1
  funext k
  rcases k with (_ | _) | k
  · rfl
  · rfl
  · rfl

lemma initList_M (s : List (M.Γ M.k₀)) :
    liftCfg (e := e) ⟨some M.main, M.initialState, Function.update (fun _ => []) M.k₀ s⟩ =
      liftCfg (e := e) (initList M s) := by
  simp only [initList]
  congr 3
  funext k
  by_cases h : k = M.k₀
  · subst h
    simp
  · rw [Function.update_of_ne h, dif_neg h]

lemma haltList_lift (s : List (M.Γ M.k₁)) : liftCfg (e := e) (haltList M s) = haltList (N M e) s := by
  simp only [liftCfg, haltList]
  congr 1
  funext k
  rcases k with (_ | _) | k
  · rfl
  · rfl
  · by_cases h : k = M.k₁
    · subst h
      simp only [mk]
      split
      · split
        · rfl
        · rename_i hne
          exact absurd rfl hne
      · rename_i hne
        exact absurd trivial hne
    · simp only [mk, dif_neg h]
      split
      · rename_i heq
        exact absurd (Sum.inr_injective (heq : (Sum.inr k : Bool ⊕ M.K) = Sum.inr M.k₁)) h
      · rfl

variable (M e) in
lemma run_M {s : List (M.Γ M.k₀)} {out : List (M.Γ M.k₁)} {T : ℕ}
    (h : TM2OutputsInTime M s (some out) T) :
    RIn (N M e).step (liftCfg (e := e) (initList M s)) (some (haltList (N M e) out)) T := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  refine ⟨n, hle, ?_⟩
  have := iterate_lift (M := M) (e := e) n (some (initList M s))
  change (flip bind (N M e).step)^[n] (Option.map liftCfg (some (initList M s))) = _
  rw [this]
  refine (congrArg (Option.map liftCfg) hn).trans ?_
  show some (liftCfg (haltList M out)) = _
  rw [haltList_lift]

end Fs

open Fs in
/-- If f is computable in polynomial time, then so is the map sending a pair p to f p.1. -/
theorem comp_fst {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] (f : α → β) (hf : IsPolyTime f) :
    IsPolyTime (fun p : α × γ => f p.1) := by
  obtain ⟨M⟩ := hf
  refine ⟨{ tm := N M.tm M.inputAlphabet
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := M.outputAlphabet
            time := Polynomial.X + 2 + M.time
            outputsFun := fun p => ?_ }⟩
  set s := BitstringEncoding.bitEncode p.1 with hs
  set t := BitstringEncoding.bitEncode p.2 with ht
  have henc : (BitstringEncoding.toEncoding (α := α × γ)).encode p =
      BitstringEncoding.delimit s ++ t := rfl
  have hin : List.map ((Equiv.refl Bool : (N M.tm M.inputAlphabet).Γ (N M.tm M.inputAlphabet).k₀ ≃
      Bool).invFun) ((BitstringEncoding.toEncoding (α := α × γ)).encode p) =
      BitstringEncoding.delimit s ++ t := by
    rw [henc]; exact List.map_id _
  have hrun : RIn (N M.tm M.inputAlphabet).step (initList (N M.tm M.inputAlphabet) (BitstringEncoding.delimit s ++ t))
      (some (haltList (N M.tm M.inputAlphabet) (List.map M.outputAlphabet.invFun
        ((BitstringEncoding.toEncoding (α := β)).encode (f p.1)))))
      ((s.length + 1) + (t.length + 1) + (s.length + 1) + M.time.eval s.length) := by
    rw [initList_N]
    have h1 := parse_run (M := M.tm) (e := M.inputAlphabet) s t [] none (fun _ => [])
    have h2 := erase_run (M := M.tm) (e := M.inputAlphabet) t (s.reverse ++ []) (some false) (fun _ => [])
    have h3 := move_run (M := M.tm) (e := M.inputAlphabet) (s.reverse ++ []) none (fun _ => [])
    have h4 := run_M M.tm M.inputAlphabet (M.outputsFun p.1)
    have hcfg : (List.map M.inputAlphabet.symm (s.reverse ++ [])).reverse ++ [] =
        List.map M.inputAlphabet.invFun s := by
      simp [List.map_reverse]
    rw [hcfg, initList_M] at h3
    have hlen : (s.reverse ++ []).length = s.length := by simp
    rw [hlen] at h3
    exact ((h1.trans h2).trans h3).trans h4
  have hn : ((BitstringEncoding.toEncoding (α := α × γ)).encode p).length =
      2 * s.length + 1 + t.length := by
    rw [henc]; simp [BitstringEncoding.length_delimit]
  have hb : (s.length + 1) + (t.length + 1) + (s.length + 1) + M.time.eval s.length ≤
      (Polynomial.X + 2 + M.time).eval
        ((BitstringEncoding.toEncoding (α := α × γ)).encode p).length := by
    rw [hn]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    have := eval_mono M.time (show s.length ≤ 2 * s.length + 1 + t.length by omega)
    omega
  have key : ∀ l : List Bool, l = BitstringEncoding.delimit s ++ t →
      TM2OutputsInTime (N M.tm M.inputAlphabet) l
        (some (List.map M.outputAlphabet.invFun
          ((BitstringEncoding.toEncoding (α := β)).encode (f p.1))))
        ((Polynomial.X + 2 + M.time).eval
          ((BitstringEncoding.toEncoding (α := α × γ)).encode p).length) := by
    rintro l rfl
    exact Classical.choice (by
      obtain ⟨n, hle, he⟩ := hrun.mono hb
      exact ⟨⟨⟨n, he⟩, hle⟩⟩)
  exact key _ hin


end Erdos78Pair

/-- Feeding the output of a poly-time map, next to the original input, into another poly-time
map stays poly-time. -/
theorem erdos78_avoid_H3 : ∀ (g : ℕ → ℕ) (dec : ℕ × ℕ × ℕ × ℕ → Bool), IsPolyTime g → IsPolyTime dec →
    IsPolyTime (fun x : ℕ × ℕ × ℕ => dec (g x.1, x)) := by
  intro g dec hg hdec
  exact Erdos78Pair.comp_polyTime (fun x : ℕ × ℕ × ℕ => (g x.1, id x)) dec
    (Erdos78Pair.pair_polyTime (fun x : ℕ × ℕ × ℕ => g x.1) id
      (Erdos78Pair.comp_fst (γ := ℕ × ℕ) g hg) isPolyTime_id) hdec
end

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R2.H3 :=
  erdos78_avoid_H3
