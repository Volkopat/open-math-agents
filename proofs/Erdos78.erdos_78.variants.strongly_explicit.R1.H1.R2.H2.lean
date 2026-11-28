import OMAReductions.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R2

-- Proof of step H2 of the range avoidance split (single file).
-- Parts: hand-built machines for the closure facts, binary arithmetic, the decoder and the
-- compression map as polynomial-time programs, and the Ramsey compression lemma.

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

-- ===== part: While =====
section
open ComplexityTheory
open Turing Computability

namespace Erdos78While

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

-- The encoding of a pair (flag, state).

lemma enc_pair {α : Type} [BitstringEncoding α] (p : Bool × α) :
    (BitstringEncoding.toEncoding (α := Bool × α)).encode p =
      true :: p.1 :: false :: BitstringEncoding.bitEncode p.2 := rfl

-- The looping machine. Stacks: the stacks of M and one helper stack.
-- Labels: the labels of M, then: none = read the header of the output of M,
-- some false = move the output stack of M to the helper stack,
-- some true = move the helper stack to the input stack of M.

variable (M : FinTM2) (eo : M.Γ M.k₁ ≃ Bool) (ei : M.Γ M.k₀ ≃ Bool)

abbrev KK : Type := M.K ⊕ Unit

abbrev LL : Type := M.Λ ⊕ Option Bool

abbrev VV : Type := M.σ × Option Bool

abbrev GG : KK M → Type := fun k =>
  Sum.casesOn (motive := fun _ => Type) k M.Γ (fun _ => Bool)

def liftM : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (GG M) (LL M) (VV M)
  | .push k f q => .push (Sum.inl k) (fun v => f v.1) (liftM q)
  | .peek k f q => .peek (Sum.inl k) (fun v o => (f v.1 o, v.2)) (liftM q)
  | .pop k f q => .pop (Sum.inl k) (fun v o => (f v.1 o, v.2)) (liftM q)
  | .load a q => .load (fun v => (a v.1, v.2)) (liftM q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (liftM q₁) (liftM q₂)
  | .goto f => .goto (fun v => Sum.inl (f v.1))
  | .halt => .goto (fun _ => Sum.inr none)

def prog : LL M → TM2.Stmt (GG M) (LL M) (VV M)
  | Sum.inl l => liftM M (M.m l)
  | Sum.inr none =>
    .pop (Sum.inl M.k₁) (fun v (_ : Option (M.Γ M.k₁)) => v) <|
    .pop (Sum.inl M.k₁) (fun v (o : Option (M.Γ M.k₁)) => (v.1, o.map eo)) <|
    .pop (Sum.inl M.k₁) (fun v (_ : Option (M.Γ M.k₁)) => v) <|
      .branch (fun v => v.2 == some true)
        (.load (fun v => (v.1, none)) .halt)
        (.goto fun _ => Sum.inr (some false))
  | Sum.inr (some false) =>
    .pop (Sum.inl M.k₁) (fun v (o : Option (M.Γ M.k₁)) => (v.1, o.map eo)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inr ()) (fun v => v.2.getD false) <|
          .goto fun _ => Sum.inr (some false))
        (.goto fun _ => Sum.inr (some true))
  | Sum.inr (some true) =>
    .pop (Sum.inr ()) (fun v (o : Option Bool) => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inl M.k₀) (fun v => ei.symm (v.2.getD false)) <|
          .goto fun _ => Sum.inr (some true))
        (.goto fun _ => Sum.inl M.main)

def Wh : FinTM2 :=
  letI := M.kFin
  letI := M.ΛFin
  letI := M.σFin
  { K := KK M
    k₀ := Sum.inl M.k₀
    k₁ := Sum.inl M.k₁
    Γ := GG M
    Λ := LL M
    main := Sum.inl M.main
    σ := VV M
    initialState := (M.initialState, none)
    Γk₀Fin := M.Γk₀Fin
    m := prog M eo ei }

def mk (SM : ∀ k, List (M.Γ k)) (a : List Bool) : ∀ k : KK M, List (GG M k)
  | Sum.inl k => SM k
  | Sum.inr _ => a

variable {M} {eo} {ei}

lemma upd_M (SM : ∀ k, List (M.Γ k)) (a : List Bool) (k : M.K)
    (v : List (GG M (Sum.inl k))) :
    Function.update (mk M SM a) (Sum.inl k) v = mk M (Function.update SM k v) a := by
  funext k'
  rcases k' with k' | k'
  · by_cases h : k' = k
    · subst h
      simp [Function.update, mk]
    · simp [Function.update, mk, h]
  · simp [Function.update, mk]

lemma upd_A (SM : ∀ k, List (M.Γ k)) (a : List Bool)
    (v : List (GG M (Sum.inr ()))) :
    Function.update (mk M SM a) (Sum.inr ()) v = mk M SM v := by
  funext k'
  rcases k' with k' | k'
  · simp [Function.update, mk]
  · simp [Function.update, mk]

-- Lifted configuration of M (helper stack empty, flag register empty).
def liftCfgM (c : TM2.Cfg M.Γ M.Λ M.σ) : (Wh M eo ei).Cfg :=
  ⟨some (c.l.elim (Sum.inr none) Sum.inl), (c.var, none), mk M c.stk []⟩

-- Configuration of the two transfer phases.
def cfg (b : Bool) (o : Option Bool) (SM : ∀ k, List (M.Γ k)) (a : List Bool) :
    (Wh M eo ei).Cfg :=
  ⟨some (Sum.inr (some b)), (M.initialState, o), mk M SM a⟩

-- Configuration just after M halted.
def post (SM : ∀ k, List (M.Γ k)) : (Wh M eo ei).Cfg :=
  ⟨some (Sum.inr none), (M.initialState, none), mk M SM []⟩

-- Halted configuration of the looping machine.
def fin (SM : ∀ k, List (M.Γ k)) : (Wh M eo ei).Cfg :=
  ⟨none, (M.initialState, none), mk M SM []⟩

-- Simulation of M.

lemma stepAux_liftM (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (liftM M q) (v, none) (mk M S []) =
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
    (Wh M eo ei).step (liftCfgM c) = some (liftCfgM c') := by
  rcases c with ⟨_ | l, v, S⟩
  · exact absurd h (by simp [FinTM2.step, TM2.step])
  · have h' : some (TM2.stepAux (M.m l) v S) = some c' := h
    injection h' with h'
    subst h'
    show some (TM2.stepAux (liftM M (M.m l)) (v, none) (mk M S [])) = _
    exact congrArg some (stepAux_liftM (eo := eo) (ei := ei) (M.m l) v S)

lemma iterate_liftM (n : ℕ) (c c' : TM2.Cfg M.Γ M.Λ M.σ)
    (h : (flip bind M.step)^[n] (some c) = some c') :
    (flip bind (Wh M eo ei).step)^[n] (some (liftCfgM c)) = some (liftCfgM c') := by
  induction n generalizing c with
  | zero =>
    have h' : some c = some c' := h
    injection h' with h'
    subst h'
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    change (flip bind M.step)^[n] (M.step c) = some c' at h
    change (flip bind (Wh M eo ei).step)^[n] ((Wh M eo ei).step (liftCfgM c)) = _
    cases hs : M.step c with
    | none =>
      rw [hs, iterate_none] at h
      exact absurd h (by simp)
    | some c₁ =>
      rw [hs] at h
      rw [step_liftM hs]
      exact ih c₁ h

-- The header-reading step.

lemma step_post_true (c1 c2 c3 : M.Γ M.k₁) (s : List (M.Γ M.k₁))
    (SM : ∀ k, List (M.Γ k)) (h : SM M.k₁ = c1 :: c2 :: c3 :: s) (hc : eo c2 = true) :
    (Wh M eo ei).step (post SM) = some (fin (Function.update SM M.k₁ s)) := by
  show some (TM2.stepAux (prog M eo ei (Sum.inr none)) (M.initialState, none)
    (mk M SM [])) = _
  simp [prog, TM2.stepAux, mk, upd_M, fin, h, hc]
  rfl

lemma step_post_false (c1 c2 c3 : M.Γ M.k₁) (s : List (M.Γ M.k₁))
    (SM : ∀ k, List (M.Γ k)) (h : SM M.k₁ = c1 :: c2 :: c3 :: s) (hc : eo c2 = false) :
    (Wh M eo ei).step (post SM) =
      some (cfg false (some false) (Function.update SM M.k₁ s) []) := by
  show some (TM2.stepAux (prog M eo ei (Sum.inr none)) (M.initialState, none)
    (mk M SM [])) = _
  simp [prog, TM2.stepAux, mk, upd_M, cfg, h, hc]
  rfl

-- One step of each transfer phase.

lemma step_mv1_cons (o : Option Bool) (c : M.Γ M.k₁) (s : List (M.Γ M.k₁))
    (SM : ∀ k, List (M.Γ k)) (a : List Bool) (h : SM M.k₁ = c :: s) :
    (Wh M eo ei).step (cfg false o SM a) =
      some (cfg false (some (eo c)) (Function.update SM M.k₁ s) (eo c :: a)) := by
  show some (TM2.stepAux (prog M eo ei (Sum.inr (some false)))
    (M.initialState, o) (mk M SM a)) = _
  simp [prog, TM2.stepAux, mk, upd_M, upd_A, cfg, h]
  rfl

lemma step_mv1_nil (o : Option Bool) (SM : ∀ k, List (M.Γ k)) (a : List Bool)
    (h : SM M.k₁ = []) :
    (Wh M eo ei).step (cfg false o SM a) =
      some (cfg true none (Function.update SM M.k₁ []) a) := by
  show some (TM2.stepAux (prog M eo ei (Sum.inr (some false)))
    (M.initialState, o) (mk M SM a)) = _
  simp [prog, TM2.stepAux, mk, upd_M, upd_A, cfg, h]
  rfl

lemma step_mv2_cons (o : Option Bool) (c : Bool) (SM : ∀ k, List (M.Γ k)) (a : List Bool) :
    (Wh M eo ei).step (cfg true o SM (c :: a)) =
      some (cfg true (some c) (Function.update SM M.k₀ (ei.symm c :: SM M.k₀)) a) := by
  show some (TM2.stepAux (prog M eo ei (Sum.inr (some true)))
    (M.initialState, o) (mk M SM (c :: a))) = _
  simp [prog, TM2.stepAux, mk, upd_M, upd_A, cfg]
  rfl

lemma step_mv2_nil (o : Option Bool) (SM : ∀ k, List (M.Γ k)) :
    (Wh M eo ei).step (cfg true o SM []) =
      some (liftCfgM ⟨some M.main, M.initialState, SM⟩) := by
  show some (TM2.stepAux (prog M eo ei (Sum.inr (some true)))
    (M.initialState, o) (mk M SM [])) = _
  simp [prog, TM2.stepAux, mk, upd_M, upd_A, liftCfgM]
  rfl

-- The two transfer phases.

lemma mv1_run (s : List (M.Γ M.k₁)) (o : Option Bool)
    (SM : ∀ k, List (M.Γ k)) (a : List Bool) (h : SM M.k₁ = s) :
    RIn (Wh M eo ei).step (cfg false o SM a)
      (some (cfg true none (Function.update SM M.k₁ []) ((s.map eo).reverse ++ a)))
      (s.length + 1) := by
  induction s generalizing o SM a with
  | nil => exact RIn.single (step_mv1_nil o SM a h)
  | cons c s ih =>
    have h1 := RIn.single (step_mv1_cons (eo := eo) (ei := ei) o c s SM a h)
    have h2 := ih (some (eo c)) (Function.update SM M.k₁ s) (eo c :: a)
      (Function.update_self _ _ _)
    have := RIn.trans h1 h2
    simp only [Function.update_idem] at this
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

lemma mv2_run (a : List Bool) (o : Option Bool) (SM : ∀ k, List (M.Γ k)) :
    RIn (Wh M eo ei).step (cfg true o SM a)
      (some (liftCfgM ⟨some M.main, M.initialState,
        Function.update SM M.k₀ ((a.map ei.symm).reverse ++ SM M.k₀)⟩))
      (a.length + 1) := by
  induction a generalizing o SM with
  | nil =>
    simp only [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
    exact RIn.single (step_mv2_nil o SM)
  | cons c a ih =>
    have := RIn.trans (RIn.single (step_mv2_cons (eo := eo) (ei := ei) o c SM a))
      (ih (some c) _)
    simp only [Function.update_self, Function.update_idem] at this
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

-- Initial and final configurations.

lemma initList_stk (M : FinTM2) (s : List (M.Γ M.k₀)) :
    (initList M s).stk = Function.update (fun _ => []) M.k₀ s := by
  funext k
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

lemma haltList_stk_upd (M : FinTM2) (s t : List (M.Γ M.k₁)) :
    Function.update (haltList M s).stk M.k₁ t = (haltList M t).stk := by
  funext k
  by_cases h : k = M.k₁
  · subst h
    simp [haltList]
  · simp [haltList, h]

lemma initList_Wh (s : List (M.Γ M.k₀)) :
    initList (Wh M eo ei) s = liftCfgM (initList M s) := by
  simp only [initList, liftCfgM]
  congr 1
  funext k
  rcases k with k | k
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
        exact absurd (Sum.inl_injective (heq : (Sum.inl k : KK M) = Sum.inl M.k₀)) h
      · rfl
  · rfl

lemma fin_haltList (s : List (M.Γ M.k₁)) :
    fin (eo := eo) (ei := ei) (haltList M s).stk = haltList (Wh M eo ei) s := by
  simp only [fin, haltList]
  congr 1
  funext k
  rcases k with k | k
  · by_cases h : k = M.k₁
    · subst h
      simp [mk]
      split
      · rfl
      · rename_i hne
        exact absurd rfl hne
    · simp [mk, h]
      split
      · rename_i heq
        exact absurd (Sum.inl_injective (heq : (Sum.inl k : KK M) = Sum.inl M.k₁)) h
      · rfl
  · rfl

-- One round of the loop.

lemma run_M {s : List (M.Γ M.k₀)} {out : List (M.Γ M.k₁)} {T : ℕ}
    (h : TM2OutputsInTime M s (some out) T) :
    RIn (Wh M eo ei).step (liftCfgM (initList M s))
      (some (post (haltList M out).stk)) T := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  exact ⟨n, hle, iterate_liftM n (initList M s) (haltList M out) hn⟩

lemma round_true {s : List (M.Γ M.k₀)} {r : List Bool} {T : ℕ}
    (h : TM2OutputsInTime M s (some (List.map eo.symm (true :: true :: false :: r))) T) :
    RIn (Wh M eo ei).step (liftCfgM (initList M s))
      (some (haltList (Wh M eo ei) (List.map eo.symm r))) (T + 1) := by
  have a1 := run_M (eo := eo) (ei := ei) h
  have hs : (haltList M (List.map eo.symm (true :: true :: false :: r))).stk M.k₁ =
      eo.symm true :: eo.symm true :: eo.symm false :: List.map eo.symm r := by
    rw [haltList_stk_self]
    rfl
  have a2 := RIn.single (step_post_true (eo := eo) (ei := ei) _ _ _ _ _ hs (by simp))
  rw [haltList_stk_upd, fin_haltList] at a2
  exact a1.trans a2

lemma round_false {s : List (M.Γ M.k₀)} {r : List Bool} {T : ℕ}
    (h : TM2OutputsInTime M s (some (List.map eo.symm (true :: false :: false :: r))) T) :
    RIn (Wh M eo ei).step (liftCfgM (initList M s))
      (some (liftCfgM (initList M (List.map ei.symm r))))
      (T + 1 + ((r.length + 1) + (r.length + 1))) := by
  have a1 := run_M (eo := eo) (ei := ei) h
  have hs : (haltList M (List.map eo.symm (true :: false :: false :: r))).stk M.k₁ =
      eo.symm true :: eo.symm false :: eo.symm false :: List.map eo.symm r := by
    rw [haltList_stk_self]
    rfl
  have a2 := RIn.single (step_post_false (eo := eo) (ei := ei) _ _ _ _ _ hs (by simp))
  rw [haltList_stk_upd] at a2
  have a3 := mv1_run (eo := eo) (ei := ei) (List.map eo.symm r) (some false)
    (haltList M (List.map eo.symm r)).stk [] (haltList_stk_self M _)
  rw [haltList_stk_update] at a3
  have a4 := mv2_run (eo := eo) (ei := ei) ((List.map eo (List.map eo.symm r)).reverse ++ [])
    none (fun _ => [])
  have hcfg : (List.map ei.symm ((List.map eo (List.map eo.symm r)).reverse ++ [])).reverse ++ [] =
      List.map ei.symm r := by
    simp [List.map_reverse]
  have hinit : (⟨some M.main, M.initialState,
      Function.update (fun _ => []) M.k₀ (List.map ei.symm r)⟩ : TM2.Cfg M.Γ M.Λ M.σ) =
      initList M (List.map ei.symm r) := by
    have : initList M (List.map ei.symm r) =
        ⟨some M.main, M.initialState, (initList M (List.map ei.symm r)).stk⟩ := rfl
    rw [this, initList_stk]
  rw [hcfg, hinit] at a4
  have hlen1 : (List.map eo.symm r).length = r.length := by simp
  have hlen2 : ((List.map eo (List.map eo.symm r)).reverse ++ []).length = r.length := by simp
  rw [hlen1] at a3
  rw [hlen2] at a4
  exact (a1.trans a2).trans (a3.trans a4)

-- The whole loop, by induction on the number of rounds.

lemma loop_run {α : Type} [BitstringEncoding α] (F : α → Bool × α)
    (Mc : TM2ComputableInPolyTime (BitstringEncoding.toEncoding (α := α)).encode
      (BitstringEncoding.toEncoding (α := Bool × α)).encode F) (L : ℕ) (n : ℕ) :
    ∀ a : α,
      (∀ i ≤ n, (BitstringEncoding.bitEncode ((fun a => (F a).2)^[i] a)).length ≤ L) →
      (∀ i < n, (F ((fun a => (F a).2)^[i] a)).1 = false) →
      (F ((fun a => (F a).2)^[n] a)).1 = true →
      RIn (Wh Mc.tm Mc.outputAlphabet Mc.inputAlphabet).step
        (liftCfgM (initList Mc.tm
          (List.map Mc.inputAlphabet.symm (BitstringEncoding.bitEncode a))))
        (some (haltList (Wh Mc.tm Mc.outputAlphabet Mc.inputAlphabet)
          (List.map Mc.outputAlphabet.symm
            (BitstringEncoding.bitEncode (F ((fun a => (F a).2)^[n] a)).2))))
        ((n + 1) * (Mc.time.eval L + 2 * L + 3)) := by
  induction n with
  | zero =>
    intro a hL _ htrue
    have h0 : (F a).1 = true := htrue
    have hlen : (BitstringEncoding.bitEncode a).length ≤ L := hL 0 le_rfl
    have hM : TM2OutputsInTime Mc.tm
        (List.map Mc.inputAlphabet.symm (BitstringEncoding.bitEncode a))
        (some (List.map Mc.outputAlphabet.symm
          (true :: true :: false :: BitstringEncoding.bitEncode (F a).2)))
        (Mc.time.eval (BitstringEncoding.bitEncode a).length) := by
      have := Mc.outputsFun a
      rw [enc_pair, h0] at this
      exact this
    have hr := round_true (ei := Mc.inputAlphabet) hM
    have ht := eval_mono Mc.time hlen
    exact hr.mono (by omega)
  | succ n ih =>
    intro a hL hfalse htrue
    have h0 : (F a).1 = false := hfalse 0 (by omega)
    have hlen : (BitstringEncoding.bitEncode a).length ≤ L := hL 0 (by omega)
    have hlen' : (BitstringEncoding.bitEncode (F a).2).length ≤ L := hL 1 (by omega)
    have hM : TM2OutputsInTime Mc.tm
        (List.map Mc.inputAlphabet.symm (BitstringEncoding.bitEncode a))
        (some (List.map Mc.outputAlphabet.symm
          (true :: false :: false :: BitstringEncoding.bitEncode (F a).2)))
        (Mc.time.eval (BitstringEncoding.bitEncode a).length) := by
      have := Mc.outputsFun a
      rw [enc_pair, h0] at this
      exact this
    have hr := round_false (ei := Mc.inputAlphabet) hM
    have hi := ih (F a).2 (fun i hi => hL (i + 1) (by omega))
      (fun i hi => hfalse (i + 1) (by omega)) htrue
    have ht := eval_mono Mc.time hlen
    have hmul : (n + 1 + 1) * (Mc.time.eval L + 2 * L + 3) =
        (n + 1) * (Mc.time.eval L + 2 * L + 3) + (Mc.time.eval L + 2 * L + 3) := by ring
    refine (hr.trans hi).mono ?_
    rw [hmul]
    generalize (n + 1) * (Mc.time.eval L + 2 * L + 3) = Y
    omega

end Erdos78While

open Erdos78While

-- Polynomial-time computable functions are closed under polynomially bounded
-- WHILE-iteration.
theorem Erdos78While.while_polyTime {α : Type} [BitstringEncoding α] (F : α → Bool × α)
    (hF : IsPolyTime F) (pT pB : Polynomial ℕ) (G : α → α)
    (hG : ∀ x : α, ∃ n : ℕ, n ≤ pT.eval (BitstringEncoding.bitEncode x).length ∧
      (∀ i ≤ n, (BitstringEncoding.bitEncode ((fun a => (F a).2)^[i] x)).length ≤
        pB.eval (BitstringEncoding.bitEncode x).length) ∧
      (∀ i < n, (F ((fun a => (F a).2)^[i] x)).1 = false) ∧
      (F ((fun a => (F a).2)^[n] x)).1 = true ∧
      G x = (F ((fun a => (F a).2)^[n] x)).2) :
    IsPolyTime G := by
  obtain ⟨Mc⟩ := hF
  refine ⟨{ tm := Wh Mc.tm Mc.outputAlphabet Mc.inputAlphabet
            inputAlphabet := Mc.inputAlphabet
            outputAlphabet := Mc.outputAlphabet
            time := (pT + 1) * (Mc.time.comp pB + Polynomial.C 2 * pB + Polynomial.C 3)
            outputsFun := fun x => ?_ }⟩
  exact Classical.choice (by
    obtain ⟨n, hn, hB, hfl, htr, hGx⟩ := hG x
    have hrun := loop_run F Mc (pB.eval (BitstringEncoding.bitEncode x).length) n x hB hfl htr
    rw [← initList_Wh, ← hGx] at hrun
    have hb : (n + 1) * (Mc.time.eval (pB.eval (BitstringEncoding.bitEncode x).length) +
        2 * pB.eval (BitstringEncoding.bitEncode x).length + 3) ≤
        ((pT + 1) * (Mc.time.comp pB + Polynomial.C 2 * pB + Polynomial.C 3)).eval
          (BitstringEncoding.bitEncode x).length := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_one, Polynomial.eval_comp]
      exact Nat.mul_le_mul_right _ (by omega)
    obtain ⟨m, hle, he⟩ := hrun.mono hb
    exact ⟨⟨⟨m, he⟩, hle⟩⟩)
end

-- ===== part: Prim1 =====
section
open ComplexityTheory
open Turing Computability

-- Toolkit facts on polynomial-time computability in the FinTM2 model:
-- second projection, constant functions and selection by a Boolean flag.
-- Mathlib has no closure lemmas for poly-time machines, so each machine is built by hand.
-- All machines have two stacks of bits: stack false is the main stack (input and output),
-- stack true is a scratch stack. The finite state is the last popped symbol.

namespace Erdos78Prim1

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

-- A two-stack machine over bits with label type L.

def mach (L : Type) [Fintype L] (main : L)
    (prog : L → TM2.Stmt (fun _ : Bool => Bool) L (Option Bool)) : FinTM2 :=
  { K := Bool
    k₀ := false
    k₁ := false
    Γ := fun _ => Bool
    Λ := L
    main := main
    σ := Option Bool
    initialState := none
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := prog }

def mk (i a : List Bool) : ∀ k : Bool, List ((fun _ : Bool => Bool) k)
  | false => i
  | true => a

lemma upd_main (i a : List Bool) (i' : List Bool) :
    Function.update (mk i a) false i' = mk i' a := by
  funext k
  cases k <;> simp [Function.update, mk]

lemma upd_aux (i a : List Bool) (a' : List Bool) :
    Function.update (mk i a) true a' = mk i a' := by
  funext k
  cases k <;> simp [Function.update, mk]

def cfg {L : Type} (l : Option L) (o : Option Bool) (i a : List Bool) :
    TM2.Cfg (fun _ : Bool => Bool) L (Option Bool) :=
  ⟨l, o, mk i a⟩

/-- The step function of a program, with the configuration type spelled out. -/
def stp {L : Type} (prog : L → TM2.Stmt (fun _ : Bool => Bool) L (Option Bool)) :
    TM2.Cfg (fun _ : Bool => Bool) L (Option Bool) →
      Option (TM2.Cfg (fun _ : Bool => Bool) L (Option Bool)) :=
  TM2.step prog

section generic

variable {L : Type} [Fintype L] (main : L)
  (prog : L → TM2.Stmt (fun _ : Bool => Bool) L (Option Bool))

lemma initList_mach (l : List Bool) :
    initList (mach L main prog) l = cfg (some main) none l [] := by
  simp only [initList, cfg]
  congr 1
  funext k
  cases k <;> rfl

lemma haltList_mach (l : List Bool) :
    haltList (mach L main prog) l = cfg none none l [] := by
  simp only [haltList, cfg]
  congr 1
  funext k
  cases k <;> rfl

/-- A machine mapping encodings to encodings within a polynomial step budget gives IsPolyTime. -/
lemma polyTime_of_run {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (f : α → β)
    (p : Polynomial ℕ)
    (h : ∀ x : α, RIn (stp prog)
      (cfg (some main) none (BitstringEncoding.bitEncode x) [])
      (some (cfg none none (BitstringEncoding.bitEncode (f x)) []))
      (p.eval (BitstringEncoding.bitEncode x).length)) :
    IsPolyTime f := by
  refine ⟨{ tm := mach L main prog
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := p
            outputsFun := fun x => ?_ }⟩
  have key : ∀ l l' : List Bool, l = BitstringEncoding.bitEncode x →
      l' = BitstringEncoding.bitEncode (f x) →
      TM2OutputsInTime (mach L main prog) l (some l')
        (p.eval (BitstringEncoding.bitEncode x).length) := by
    rintro l l' rfl rfl
    exact Classical.choice (by
      have h' : RIn (mach L main prog).step
          (initList (mach L main prog) (BitstringEncoding.bitEncode x))
          (some (haltList (mach L main prog) (BitstringEncoding.bitEncode (f x))))
          (p.eval (BitstringEncoding.bitEncode x).length) := by
        rw [initList_mach, haltList_mach]
        exact h x
      obtain ⟨n, hle, he⟩ := h'
      exact ⟨⟨⟨n, he⟩, hle⟩⟩)
  exact key _ _ (List.map_id _) (List.map_id _)

end generic

lemma eval_X_add_one (n : ℕ) : (Polynomial.X + 1 : Polynomial ℕ).eval n = n + 1 := by
  simp

-- Second projection: pop the first self-delimiting block, keep the rest.

def progSnd : Unit → TM2.Stmt (fun _ : Bool => Bool) Unit (Option Bool)
  | _ =>
    .pop false (fun _ o => o) <|
      .branch (fun v => v == some true)
        (.pop false (fun _ o => o) <| .goto fun _ => ())
        (.load (fun _ => none) <| .halt)

lemma step_snd_true (o : Option Bool) (c : Bool) (rest a : List Bool) :
    (stp progSnd) (cfg (some ()) o (true :: c :: rest) a) =
      some (cfg (some ()) (some c) rest a) := by
  show some (TM2.stepAux (progSnd ()) o (mk (true :: c :: rest) a)) = _
  simp [progSnd, TM2.stepAux, mk, upd_main, cfg]

lemma step_snd_false (o : Option Bool) (rest a : List Bool) :
    (stp progSnd) (cfg (some ()) o (false :: rest) a) =
      some (cfg none none rest a) := by
  show some (TM2.stepAux (progSnd ()) o (mk (false :: rest) a)) = _
  simp [progSnd, TM2.stepAux, mk, upd_main, cfg]

lemma snd_run (s rest a : List Bool) (o : Option Bool) :
    RIn (stp progSnd) (cfg (some ()) o (BitstringEncoding.delimit s ++ rest) a)
      (some (cfg none none rest a)) (s.length + 1) := by
  induction s generalizing o with
  | nil =>
    have := RIn.single (step_snd_false o rest a)
    simpa [BitstringEncoding.delimit] using this
  | cons c s ih =>
    have h1 := RIn.single (step_snd_true o c (BitstringEncoding.delimit s ++ rest) a)
    have h2 := ih (some c)
    have := RIn.trans h1 h2
    simpa [BitstringEncoding.delimit, Nat.add_comm] using this

/-- The second projection of a pair is computable in polynomial time. -/
theorem snd_polyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    IsPolyTime (Prod.snd : α × β → β) := by
  refine polyTime_of_run () progSnd _ (Polynomial.X + 1) fun x => ?_
  have henc : BitstringEncoding.bitEncode x =
      BitstringEncoding.delimit (BitstringEncoding.bitEncode x.1) ++
        BitstringEncoding.bitEncode x.2 := rfl
  rw [henc, eval_X_add_one]
  refine (snd_run _ _ [] none).mono ?_
  simp only [List.length_append, BitstringEncoding.length_delimit]
  omega

-- Selection: the input is a flag and two blocks, the output is one of the blocks.
-- Labels: none reads the header; some (false, false) skips the first block and halts;
-- some (false, true) moves the payload of the first block to the scratch stack;
-- some (true, false) erases the rest of the input; some (true, true) pours the scratch
-- stack back on the main stack.

def progSel : Option (Bool × Bool) → TM2.Stmt (fun _ : Bool => Bool) (Option (Bool × Bool))
    (Option Bool)
  | none =>
    .pop false (fun _ o => o) <|
      .pop false (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.pop false (fun v _ => v) <| .goto fun _ => some (false, true))
          (.pop false (fun v _ => v) <| .goto fun _ => some (false, false))
  | some (false, false) =>
    .pop false (fun _ o => o) <|
      .branch (fun v => v == some true)
        (.pop false (fun _ o => o) <| .goto fun _ => some (false, false))
        (.load (fun _ => none) <| .halt)
  | some (false, true) =>
    .pop false (fun _ o => o) <|
      .branch (fun v => v == some true)
        (.pop false (fun _ o => o) <|
          .push true (fun v => v.getD false) <| .goto fun _ => some (false, true))
        (.goto fun _ => some (true, false))
  | some (true, false) =>
    .pop false (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.goto fun _ => some (true, false))
        (.goto fun _ => some (true, true))
  | some (true, true) =>
    .pop true (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push false (fun v => v.getD false) <| .goto fun _ => some (true, true))
        (.load (fun _ => none) <| .halt)

lemma step_sel_hdr_true (o : Option Bool) (rest a : List Bool) :
    (stp progSel) (cfg (some none) o (true :: true :: false :: rest) a) =
      some (cfg (some (some (false, true))) (some true) rest a) := by
  show some (TM2.stepAux (progSel none) o (mk (true :: true :: false :: rest) a)) = _
  simp [progSel, TM2.stepAux, mk, upd_main, cfg]

lemma step_sel_hdr_false (o : Option Bool) (rest a : List Bool) :
    (stp progSel) (cfg (some none) o (true :: false :: false :: rest) a) =
      some (cfg (some (some (false, false))) (some false) rest a) := by
  show some (TM2.stepAux (progSel none) o (mk (true :: false :: false :: rest) a)) = _
  simp [progSel, TM2.stepAux, mk, upd_main, cfg]

lemma step_sel_skip_true (o : Option Bool) (c : Bool) (rest a : List Bool) :
    (stp progSel) (cfg (some (some (false, false))) o (true :: c :: rest) a) =
      some (cfg (some (some (false, false))) (some c) rest a) := by
  show some (TM2.stepAux (progSel (some (false, false))) o (mk (true :: c :: rest) a)) = _
  simp [progSel, TM2.stepAux, mk, upd_main, cfg]

lemma step_sel_skip_false (o : Option Bool) (rest a : List Bool) :
    (stp progSel) (cfg (some (some (false, false))) o (false :: rest) a) =
      some (cfg none none rest a) := by
  show some (TM2.stepAux (progSel (some (false, false))) o (mk (false :: rest) a)) = _
  simp [progSel, TM2.stepAux, mk, upd_main, cfg]

lemma step_sel_parse_true (o : Option Bool) (c : Bool) (rest a : List Bool) :
    (stp progSel) (cfg (some (some (false, true))) o (true :: c :: rest) a) =
      some (cfg (some (some (false, true))) (some c) rest (c :: a)) := by
  show some (TM2.stepAux (progSel (some (false, true))) o (mk (true :: c :: rest) a)) = _
  simp [progSel, TM2.stepAux, mk, upd_main, upd_aux, cfg]

lemma step_sel_parse_false (o : Option Bool) (rest a : List Bool) :
    (stp progSel) (cfg (some (some (false, true))) o (false :: rest) a) =
      some (cfg (some (some (true, false))) (some false) rest a) := by
  show some (TM2.stepAux (progSel (some (false, true))) o (mk (false :: rest) a)) = _
  simp [progSel, TM2.stepAux, mk, upd_main, upd_aux, cfg]

lemma step_sel_erase_cons (o : Option Bool) (c : Bool) (i a : List Bool) :
    (stp progSel) (cfg (some (some (true, false))) o (c :: i) a) =
      some (cfg (some (some (true, false))) (some c) i a) := by
  show some (TM2.stepAux (progSel (some (true, false))) o (mk (c :: i) a)) = _
  simp [progSel, TM2.stepAux, mk, upd_main, cfg]

lemma step_sel_erase_nil (o : Option Bool) (a : List Bool) :
    (stp progSel) (cfg (some (some (true, false))) o [] a) =
      some (cfg (some (some (true, true))) none [] a) := by
  show some (TM2.stepAux (progSel (some (true, false))) o (mk [] a)) = _
  simp [progSel, TM2.stepAux, mk, upd_main, cfg]

lemma step_sel_pour_cons (o : Option Bool) (c : Bool) (i a : List Bool) :
    (stp progSel) (cfg (some (some (true, true))) o i (c :: a)) =
      some (cfg (some (some (true, true))) (some c) (c :: i) a) := by
  show some (TM2.stepAux (progSel (some (true, true))) o (mk i (c :: a))) = _
  simp [progSel, TM2.stepAux, mk, upd_main, upd_aux, cfg]

lemma step_sel_pour_nil (o : Option Bool) (i : List Bool) :
    (stp progSel) (cfg (some (some (true, true))) o i []) =
      some (cfg none none i []) := by
  show some (TM2.stepAux (progSel (some (true, true))) o (mk i [])) = _
  simp [progSel, TM2.stepAux, mk, upd_main, upd_aux, cfg]

lemma sel_skip_run (s rest a : List Bool) (o : Option Bool) :
    RIn (stp progSel)
      (cfg (some (some (false, false))) o (BitstringEncoding.delimit s ++ rest) a)
      (some (cfg none none rest a)) (s.length + 1) := by
  induction s generalizing o with
  | nil =>
    have := RIn.single (step_sel_skip_false o rest a)
    simpa [BitstringEncoding.delimit] using this
  | cons c s ih =>
    have h1 := RIn.single (step_sel_skip_true o c (BitstringEncoding.delimit s ++ rest) a)
    have h2 := ih (some c)
    have := RIn.trans h1 h2
    simpa [BitstringEncoding.delimit, Nat.add_comm] using this

lemma sel_parse_run (s rest a : List Bool) (o : Option Bool) :
    RIn (stp progSel)
      (cfg (some (some (false, true))) o (BitstringEncoding.delimit s ++ rest) a)
      (some (cfg (some (some (true, false))) (some false) rest (s.reverse ++ a)))
      (s.length + 1) := by
  induction s generalizing a o with
  | nil =>
    have := RIn.single (step_sel_parse_false o rest a)
    simpa [BitstringEncoding.delimit] using this
  | cons c s ih =>
    have h1 := RIn.single (step_sel_parse_true o c (BitstringEncoding.delimit s ++ rest) a)
    have h2 := ih (c :: a) (some c)
    have := RIn.trans h1 h2
    simpa [BitstringEncoding.delimit, List.reverse_cons, List.append_assoc, Nat.add_comm]
      using this

lemma sel_erase_run (i a : List Bool) (o : Option Bool) :
    RIn (stp progSel) (cfg (some (some (true, false))) o i a)
      (some (cfg (some (some (true, true))) none [] a)) (i.length + 1) := by
  induction i generalizing o with
  | nil => exact RIn.single (step_sel_erase_nil o a)
  | cons c i ih =>
    have := RIn.trans (RIn.single (step_sel_erase_cons o c i a)) (ih (some c))
    simpa [Nat.add_comm] using this

lemma sel_pour_run (i a : List Bool) (o : Option Bool) :
    RIn (stp progSel) (cfg (some (some (true, true))) o i a)
      (some (cfg none none (a.reverse ++ i) [])) (a.length + 1) := by
  induction a generalizing o i with
  | nil => exact RIn.single (step_sel_pour_nil o i)
  | cons c a ih =>
    have := RIn.trans (RIn.single (step_sel_pour_cons o c i a)) (ih (c :: i) (some c))
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

lemma sel_run_true (s t : List Bool) :
    RIn (stp progSel)
      (cfg (some none) none (true :: true :: false :: (BitstringEncoding.delimit s ++ t)) [])
      (some (cfg none none s [])) (2 * s.length + t.length + 4) := by
  have h1 := RIn.single (step_sel_hdr_true none (BitstringEncoding.delimit s ++ t) [])
  have h2 := sel_parse_run s t [] (some true)
  have h3 := sel_erase_run t (s.reverse ++ []) (some false)
  have h4 := sel_pour_run [] (s.reverse ++ []) none
  have h := ((h1.trans h2).trans h3).trans h4
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h
  exact h.mono (by omega)

lemma sel_run_false (s t : List Bool) :
    RIn (stp progSel)
      (cfg (some none) none (true :: false :: false :: (BitstringEncoding.delimit s ++ t)) [])
      (some (cfg none none t [])) (s.length + 2) := by
  have h1 := RIn.single (step_sel_hdr_false none (BitstringEncoding.delimit s ++ t) [])
  have h2 := sel_skip_run s t [] (some false)
  exact (h1.trans h2).mono (by omega)

/-- Selecting one of two values by a Boolean flag is computable in polynomial time. -/
theorem sel_polyTime {β : Type} [BitstringEncoding β] :
    IsPolyTime (fun p : Bool × β × β => if p.1 then p.2.1 else p.2.2) := by
  refine polyTime_of_run none progSel _ (Polynomial.X + 1) fun x => ?_
  obtain ⟨flag, y, z⟩ := x
  have henc : BitstringEncoding.bitEncode (flag, y, z) =
      true :: flag :: false :: (BitstringEncoding.delimit (BitstringEncoding.bitEncode y) ++
        BitstringEncoding.bitEncode z) := rfl
  rw [henc, eval_X_add_one]
  cases flag
  · refine (sel_run_false _ _).mono ?_
    simp only [List.length_cons, List.length_append, BitstringEncoding.length_delimit]
    omega
  · refine (sel_run_true _ _).mono ?_
    simp only [List.length_cons, List.length_append, BitstringEncoding.length_delimit]
    omega

-- Constant functions: erase the input, then push the fixed output in one step.

def pushAll {L : Type} : List Bool → TM2.Stmt (fun _ : Bool => Bool) L (Option Bool) →
    TM2.Stmt (fun _ : Bool => Bool) L (Option Bool)
  | [], q => q
  | b :: l, q => .push false (fun _ => b) (pushAll l q)

lemma stepAux_pushAll {L : Type} (w : List Bool)
    (q : TM2.Stmt (fun _ : Bool => Bool) L (Option Bool)) (v : Option Bool) (i a : List Bool) :
    TM2.stepAux (pushAll w q) v (mk i a) = TM2.stepAux q v (mk (w.reverse ++ i) a) := by
  induction w generalizing i with
  | nil => rfl
  | cons b w ih =>
    have h : TM2.stepAux (pushAll (b :: w) q) v (mk i a) =
        TM2.stepAux (pushAll w q) v (mk (b :: i) a) := by
      simp [pushAll, TM2.stepAux, mk, upd_main]
    rw [h, ih]
    simp [List.reverse_cons, List.append_assoc]

def progConst (w : List Bool) : Unit → TM2.Stmt (fun _ : Bool => Bool) Unit (Option Bool)
  | _ =>
    .pop false (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.goto fun _ => ())
        (pushAll w (.load (fun _ => none) <| .halt))

lemma step_const_cons (w : List Bool) (o : Option Bool) (c : Bool) (i a : List Bool) :
    (stp (progConst w)) (cfg (some ()) o (c :: i) a) =
      some (cfg (some ()) (some c) i a) := by
  show some (TM2.stepAux (progConst w ()) o (mk (c :: i) a)) = _
  simp [progConst, TM2.stepAux, mk, upd_main, cfg]

lemma step_const_nil (w : List Bool) (o : Option Bool) (a : List Bool) :
    (stp (progConst w)) (cfg (some ()) o [] a) =
      some (cfg none none w.reverse a) := by
  show some (TM2.stepAux (progConst w ()) o (mk [] a)) = _
  have h : TM2.stepAux (progConst w ()) o (mk [] a) =
      TM2.stepAux (pushAll w (.load (fun _ => none) <| .halt)) none (mk [] a) := by
    simp [progConst, TM2.stepAux, mk, upd_main]
  rw [h, stepAux_pushAll]
  simp [TM2.stepAux, cfg]

lemma const_run (w i a : List Bool) (o : Option Bool) :
    RIn (stp (progConst w)) (cfg (some ()) o i a)
      (some (cfg none none w.reverse a)) (i.length + 1) := by
  induction i generalizing o with
  | nil => exact RIn.single (step_const_nil w o a)
  | cons c i ih =>
    have := RIn.trans (RIn.single (step_const_cons w o c i a)) (ih (some c))
    simpa [Nat.add_comm] using this

/-- Constant functions are computable in polynomial time. -/
theorem const_polyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (c : β) :
    IsPolyTime (fun _ : α => c) := by
  refine polyTime_of_run () (progConst (BitstringEncoding.bitEncode c).reverse) _
    (Polynomial.X + 1) fun x => ?_
  rw [eval_X_add_one]
  have h := const_run (BitstringEncoding.bitEncode c).reverse (BitstringEncoding.bitEncode x)
    [] none
  rw [List.reverse_reverse] at h
  exact h

end Erdos78Prim1
end

-- ===== part: Prim2 =====
section
open ComplexityTheory
open Turing Computability

-- Toolkit: five basic bit operations on natural numbers are computable in polynomial time
-- (doubling, doubling plus one, halving, parity test, zero test).
-- Mathlib has no such lemmas, so one small generic machine is built by hand and used five times.
-- Two stacks: the main stack (input and output) and a scratch stack.
-- The machine pops the first input symbol and emits a short fixed list that depends on it.
-- In keep mode the rest of the input stays where it is and the run takes one step.
-- In drop mode the rest of the input is erased, and the emitted list (first written on the
-- scratch stack) is poured back on the main stack.

namespace Erdos78Prim2

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

lemma bits_eq_nil_iff (n : ℕ) : Nat.bits n = [] ↔ n = 0 := by
  constructor
  · intro h
    have h1 := Nat.size_eq_bits_len n
    rw [h] at h1
    exact Nat.size_eq_zero.mp h1.symm
  · rintro rfl
    simp

-- The machine. Stack false is the main stack, stack true the scratch stack.
-- Label none is the start, label some false the erase loop, label some true the pour loop.

abbrev St : Type := TM2.Stmt (fun _ : Bool => Bool) (Option Bool) (Option Bool)

/-- Push a fixed list on stack k, first element first. -/
def emit (k : Bool) : List Bool → St → St
  | [], q => q
  | b :: l, q => .push k (fun _ => b) (emit k l q)

/-- Run the statement selected by the current value of the register. -/
def onHead (body : Option Bool → St) : St :=
  .branch (fun v => v == none) (body none)
    (.branch (fun v => v == some true) (body (some true)) (body (some false)))

def prog (hd : Option Bool → List Bool) (keep : Bool) : Option Bool → St
  | none =>
    .pop false (fun _ o => o) <| onHead fun v =>
      cond keep (emit false (hd v).reverse (.load (fun _ => none) .halt))
        (emit true (hd v) (.goto fun _ => some false))
  | some false =>
    .pop false (fun _ o => o) <|
      .branch (fun v => v.isSome) (.goto fun _ => some false)
        (.load (fun _ => none) <| .goto fun _ => some true)
  | some true =>
    .pop true (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push false (fun v => v.getD false) <| .goto fun _ => some true)
        (.load (fun _ => none) <| .halt)

def N (hd : Option Bool → List Bool) (keep : Bool) : FinTM2 :=
  { K := Bool
    k₀ := false
    k₁ := false
    Γ := fun _ => Bool
    Λ := Option Bool
    main := none
    σ := Option Bool
    initialState := none
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := prog hd keep }

def mk (i a : List Bool) : ∀ k : Bool, List ((fun _ : Bool => Bool) k)
  | false => i
  | true => a

lemma upd_main (i a : List Bool) (i' : List Bool) :
    Function.update (mk i a) false i' = mk i' a := by
  funext k
  cases k <;> simp [Function.update, mk]

lemma upd_aux (i a : List Bool) (a' : List Bool) :
    Function.update (mk i a) true a' = mk i a' := by
  funext k
  cases k <;> simp [Function.update, mk]

def cfg {hd : Option Bool → List Bool} {keep : Bool} (l : Option (Option Bool))
    (o : Option Bool) (i a : List Bool) : (N hd keep).Cfg :=
  ⟨l, o, mk i a⟩

lemma stepAux_emit_main (l : List Bool) (q : St) (v : Option Bool) (i a : List Bool) :
    TM2.stepAux (emit false l q) v (mk i a) = TM2.stepAux q v (mk (l.reverse ++ i) a) := by
  induction l generalizing i with
  | nil => rfl
  | cons b l ih =>
    simp only [emit, TM2.stepAux]
    rw [upd_main, ih]
    simp [mk]

lemma stepAux_emit_aux (l : List Bool) (q : St) (v : Option Bool) (i a : List Bool) :
    TM2.stepAux (emit true l q) v (mk i a) = TM2.stepAux q v (mk i (l.reverse ++ a)) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    simp only [emit, TM2.stepAux]
    rw [upd_aux, ih]
    simp [mk]

lemma stepAux_onHead (body : Option Bool → St) (v : Option Bool)
    (S : ∀ k : Bool, List ((fun _ : Bool => Bool) k)) :
    TM2.stepAux (onHead body) v S = TM2.stepAux (body v) v S := by
  rcases v with _ | _ | _ <;> simp [onHead, TM2.stepAux]

variable (hd : Option Bool → List Bool) (keep : Bool)

-- One step from each label.

lemma step_start_keep (o : Option Bool) (l a : List Bool) :
    (N hd true).step (cfg (some none) o l a) =
      some (cfg none none (hd l.head? ++ l.tail) a) := by
  show some (TM2.stepAux (prog hd true none) o (mk l a)) = _
  simp only [prog, TM2.stepAux, stepAux_onHead, cond_true]
  rw [upd_main, stepAux_emit_main]
  simp [TM2.stepAux, cfg, mk]
  rfl

lemma step_start_drop (o : Option Bool) (l a : List Bool) :
    (N hd false).step (cfg (some none) o l a) =
      some (cfg (some (some false)) l.head? l.tail ((hd l.head?).reverse ++ a)) := by
  show some (TM2.stepAux (prog hd false none) o (mk l a)) = _
  simp only [prog, TM2.stepAux, stepAux_onHead, cond_false]
  rw [upd_main, stepAux_emit_aux]
  simp [TM2.stepAux, cfg, mk]
  rfl

lemma step_erase_cons (o : Option Bool) (c : Bool) (i a : List Bool) :
    (N hd keep).step (cfg (some (some false)) o (c :: i) a) =
      some (cfg (some (some false)) (some c) i a) := by
  show some (TM2.stepAux (prog hd keep (some false)) o (mk (c :: i) a)) = _
  simp [prog, TM2.stepAux, mk, upd_main, cfg]
  rfl

lemma step_erase_nil (o : Option Bool) (a : List Bool) :
    (N hd keep).step (cfg (some (some false)) o [] a) =
      some (cfg (some (some true)) none [] a) := by
  show some (TM2.stepAux (prog hd keep (some false)) o (mk [] a)) = _
  simp [prog, TM2.stepAux, mk, upd_main, cfg]
  rfl

lemma step_pour_cons (o : Option Bool) (c : Bool) (i a : List Bool) :
    (N hd keep).step (cfg (some (some true)) o i (c :: a)) =
      some (cfg (some (some true)) (some c) (c :: i) a) := by
  show some (TM2.stepAux (prog hd keep (some true)) o (mk i (c :: a))) = _
  simp [prog, TM2.stepAux, mk, upd_main, upd_aux, cfg]
  rfl

lemma step_pour_nil (o : Option Bool) (i : List Bool) :
    (N hd keep).step (cfg (some (some true)) o i []) = some (cfg none none i []) := by
  show some (TM2.stepAux (prog hd keep (some true)) o (mk i [])) = _
  simp [prog, TM2.stepAux, mk, upd_main, upd_aux, cfg]
  rfl

-- The two loops.

lemma erase_run (i a : List Bool) (o : Option Bool) :
    RIn (N hd keep).step (cfg (some (some false)) o i a)
      (some (cfg (some (some true)) none [] a)) (i.length + 1) := by
  induction i generalizing o with
  | nil => exact RIn.single (step_erase_nil hd keep o a)
  | cons c i ih =>
    have := RIn.trans (RIn.single (step_erase_cons hd keep o c i a)) (ih (some c))
    simpa [Nat.add_comm] using this

lemma pour_run (i a : List Bool) (o : Option Bool) :
    RIn (N hd keep).step (cfg (some (some true)) o i a)
      (some (cfg none none (a.reverse ++ i) [])) (a.length + 1) := by
  induction a generalizing o i with
  | nil => exact RIn.single (step_pour_nil hd keep o i)
  | cons c a ih =>
    have := RIn.trans (RIn.single (step_pour_cons hd keep o c i a)) (ih (c :: i) (some c))
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

-- Initial and final configurations.

lemma initList_N (l : List Bool) :
    initList (N hd keep) l = cfg (some none) none l [] := by
  simp only [initList, cfg]
  congr 1
  funext k
  cases k <;> rfl

lemma haltList_N (l : List Bool) : haltList (N hd keep) l = cfg none none l [] := by
  simp only [haltList, cfg]
  congr 1
  funext k
  cases k <;> rfl

/-- The list function computed by the machine. -/
def phi (hd : Option Bool → List Bool) (keep : Bool) (l : List Bool) : List Bool :=
  hd l.head? ++ cond keep l.tail []

/-- The whole run of the machine, with a linear step budget. -/
lemma full_run (l : List Bool) :
    RIn (N hd keep).step (initList (N hd keep) l)
      (some (haltList (N hd keep) (phi hd keep l)))
      (l.length + (hd l.head?).length + 3) := by
  rw [initList_N, haltList_N]
  cases keep with
  | true =>
    exact (RIn.single (step_start_keep hd none l [])).mono (by omega)
  | false =>
    have h1 := RIn.single (step_start_drop hd none l [])
    have h2 := erase_run hd false l.tail ((hd l.head?).reverse ++ []) l.head?
    have h3 := pour_run hd false [] ((hd l.head?).reverse ++ []) none
    have h := (h1.trans h2).trans h3
    simp only [List.append_nil, List.reverse_reverse] at h
    have h' : RIn (N hd false).step (cfg (some none) none l [])
        (some (cfg none none (phi hd false l) []))
        (1 + (l.tail.length + 1) + ((hd l.head?).reverse.length + 1)) := by
      simpa [phi] using h
    refine h'.mono ?_
    simp only [List.length_reverse, List.length_tail]
    omega

/-- A constant bounding the length of the emitted list. -/
def hdBound (hd : Option Bool → List Bool) : ℕ :=
  (hd none).length + (hd (some true)).length + (hd (some false)).length

lemma hd_le (o : Option Bool) : (hd o).length ≤ hdBound hd := by
  rcases o with _ | _ | _ <;> simp only [hdBound] <;> omega

/-- Any function that acts on encodings as phi does is computable in polynomial time. -/
theorem polyTime_of_phi {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (f : α → β)
    (hd : Option Bool → List Bool) (keep : Bool)
    (h : ∀ a, (BitstringEncoding.toEncoding (α := β)).encode (f a) =
      phi hd keep ((BitstringEncoding.toEncoding (α := α)).encode a)) :
    IsPolyTime f := by
  refine ⟨{ tm := N hd keep
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := Polynomial.X + Polynomial.C (hdBound hd + 3)
            outputsFun := fun x => ?_ }⟩
  have hin : List.map ((Equiv.refl Bool : (N hd keep).Γ (N hd keep).k₀ ≃ Bool).invFun)
      ((BitstringEncoding.toEncoding (α := α)).encode x) =
      (BitstringEncoding.toEncoding (α := α)).encode x := List.map_id _
  have hout : List.map ((Equiv.refl Bool : (N hd keep).Γ (N hd keep).k₁ ≃ Bool).invFun)
      ((BitstringEncoding.toEncoding (α := β)).encode (f x)) =
      phi hd keep ((BitstringEncoding.toEncoding (α := α)).encode x) := by
    rw [h]; exact List.map_id _
  have hb : ((BitstringEncoding.toEncoding (α := α)).encode x).length +
      (hd ((BitstringEncoding.toEncoding (α := α)).encode x).head?).length + 3 ≤
      (Polynomial.X + Polynomial.C (hdBound hd + 3) : Polynomial ℕ).eval
        ((BitstringEncoding.toEncoding (α := α)).encode x).length := by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    have := hd_le hd ((BitstringEncoding.toEncoding (α := α)).encode x).head?
    omega
  have key : ∀ l l' : List Bool, l = (BitstringEncoding.toEncoding (α := α)).encode x →
      l' = phi hd keep ((BitstringEncoding.toEncoding (α := α)).encode x) →
      TM2OutputsInTime (N hd keep) l (some l')
        ((Polynomial.X + Polynomial.C (hdBound hd + 3) : Polynomial ℕ).eval
          ((BitstringEncoding.toEncoding (α := α)).encode x).length) := by
    rintro l l' rfl rfl
    exact Classical.choice (by
      obtain ⟨n, hle, he⟩ := (full_run hd keep _).mono hb
      exact ⟨⟨⟨n, he⟩, hle⟩⟩)
  exact key _ _ hin hout

-- The five bit operations.

/-- Doubling is computable in polynomial time. -/
theorem double_polyTime : IsPolyTime (fun n : ℕ => 2 * n) := by
  refine polyTime_of_phi _ (fun o => o.elim [] (fun b => [false, b])) true (fun n => ?_)
  show encodeNat (2 * n) = phi _ true (encodeNat n)
  rw [encodeNat_eq_bits, encodeNat_eq_bits]
  by_cases hn : n = 0
  · subst hn
    simp [phi]
  · rw [Nat.bit0_bits n hn]
    cases h : Nat.bits n with
    | nil => exact absurd ((bits_eq_nil_iff n).mp h) hn
    | cons b t => simp [phi]

/-- Doubling plus one is computable in polynomial time. -/
theorem doubleSucc_polyTime : IsPolyTime (fun n : ℕ => 2 * n + 1) := by
  refine polyTime_of_phi _ (fun o => o.elim [true] (fun b => [true, b])) true (fun n => ?_)
  show encodeNat (2 * n + 1) = phi _ true (encodeNat n)
  rw [encodeNat_eq_bits, encodeNat_eq_bits, Nat.bit1_bits]
  cases Nat.bits n <;> simp [phi]

/-- Halving (rounded down) is computable in polynomial time. -/
theorem half_polyTime : IsPolyTime (fun n : ℕ => n / 2) := by
  refine polyTime_of_phi _ (fun _ => []) true (fun n => ?_)
  show encodeNat (n / 2) = phi _ true (encodeNat n)
  rw [encodeNat_eq_bits, encodeNat_eq_bits, ← Nat.div2_val, Nat.div2_bits_eq_tail]
  simp [phi]

/-- The parity test is computable in polynomial time. -/
theorem odd_polyTime : IsPolyTime (fun n : ℕ => decide (n % 2 = 1)) := by
  refine polyTime_of_phi _ (fun o => [o.getD false]) false (fun n => ?_)
  show [decide (n % 2 = 1)] = phi _ false (encodeNat n)
  rw [encodeNat_eq_bits]
  have h1 : decide (n % 2 = 1) = n.bodd := by
    rw [Nat.mod_two_of_bodd]
    cases n.bodd <;> simp
  have h2 : (Nat.bits n).head?.getD false = n.bodd := by
    rw [Nat.bodd_eq_bits_head]
    cases Nat.bits n <;> rfl
  simp [phi, h1, h2]

/-- The zero test is computable in polynomial time. -/
theorem isZero_polyTime : IsPolyTime (fun n : ℕ => decide (n = 0)) := by
  refine polyTime_of_phi _ (fun o => [o.isNone]) false (fun n => ?_)
  show [decide (n = 0)] = phi _ false (encodeNat n)
  rw [encodeNat_eq_bits]
  by_cases hn : n = 0
  · subst hn
    simp [phi]
  · cases h : Nat.bits n with
    | nil => exact absurd ((bits_eq_nil_iff n).mp h) hn
    | cons b t => simp [phi, hn]

end Erdos78Prim2
end

-- ===== part: Toolkit =====
section
open ComplexityTheory

/-! Uniform names for the polynomial-time toolkit (all proved by hand-built machines). -/
namespace PT

variable {α β γ δ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
  [BitstringEncoding δ]

theorem id' : IsPolyTime (fun a : α => a) := isPolyTime_id

theorem comp {g : β → γ} {f : α → β} (hg : IsPolyTime g) (hf : IsPolyTime f) :
    IsPolyTime (fun a => g (f a)) :=
  Erdos78Pair.comp_polyTime f g hf hg

theorem pair {f : α → β} {g : α → γ} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => (f a, g a)) :=
  Erdos78Pair.pair_polyTime f g hf hg

theorem fst : IsPolyTime (Prod.fst : α × β → α) :=
  Erdos78Pair.comp_fst (fun a : α => a) isPolyTime_id

theorem snd : IsPolyTime (Prod.snd : α × β → β) := Erdos78Prim1.snd_polyTime

theorem const (c : β) : IsPolyTime (fun _ : α => c) := Erdos78Prim1.const_polyTime c

theorem ite {c : α → Bool} {f g : α → β} (hc : IsPolyTime c) (hf : IsPolyTime f)
    (hg : IsPolyTime g) : IsPolyTime (fun a => if c a then f a else g a) :=
  comp (g := fun p : Bool × β × β => if p.1 then p.2.1 else p.2.2) Erdos78Prim1.sel_polyTime
    (pair hc (pair hf hg))

theorem double : IsPolyTime (fun n : ℕ => 2 * n) := Erdos78Prim2.double_polyTime
theorem doubleSucc : IsPolyTime (fun n : ℕ => 2 * n + 1) := Erdos78Prim2.doubleSucc_polyTime
theorem half : IsPolyTime (fun n : ℕ => n / 2) := Erdos78Prim2.half_polyTime
theorem odd : IsPolyTime (fun n : ℕ => decide (n % 2 = 1)) := Erdos78Prim2.odd_polyTime
theorem isZero : IsPolyTime (fun n : ℕ => decide (n = 0)) := Erdos78Prim2.isZero_polyTime

/-- Raw while-iteration closure. -/
theorem whileRaw (F : α → Bool × α) (hF : IsPolyTime F) (pT pB : Polynomial ℕ) (G : α → α)
    (hG : ∀ x : α, ∃ n : ℕ, n ≤ pT.eval (BitstringEncoding.bitEncode x).length ∧
      (∀ i ≤ n, (BitstringEncoding.bitEncode ((fun a => (F a).2)^[i] x)).length ≤
        pB.eval (BitstringEncoding.bitEncode x).length) ∧
      (∀ i < n, (F ((fun a => (F a).2)^[i] x)).1 = false) ∧
      (F ((fun a => (F a).2)^[n] x)).1 = true ∧
      G x = (F ((fun a => (F a).2)^[n] x)).2) :
    IsPolyTime G :=
  Erdos78While.while_polyTime F hF pT pB G hG

/-- While-loop closure in cond/step form: repeat step while cond holds. -/
theorem loop (cond : α → Bool) (step : α → α) (hc : IsPolyTime cond) (hs : IsPolyTime step)
    (pT pB : Polynomial ℕ) (G : α → α)
    (hG : ∀ x : α, ∃ n : ℕ, n ≤ pT.eval (BitstringEncoding.bitEncode x).length ∧
      (∀ i ≤ n, (BitstringEncoding.bitEncode (step^[i] x)).length ≤
        pB.eval (BitstringEncoding.bitEncode x).length) ∧
      (∀ i < n, cond (step^[i] x) = true) ∧ cond (step^[n] x) = false ∧ G x = step^[n] x) :
    IsPolyTime G := by
  have hF : IsPolyTime (fun a : α => (!cond a, if cond a then step a else a)) :=
    pair (comp (g := fun b : Bool => !b)
      (ite (c := fun b : Bool => b) (f := fun _ => false) (g := fun _ => true) id' (const false)
        (const true) |> fun h => by simpa using h) hc) (ite hc hs id')
  refine whileRaw (fun a : α => (!cond a, if cond a then step a else a)) hF pT pB G ?_
  intro x
  obtain ⟨n, hn, hsz, hct, hcf, hGx⟩ := hG x
  have hit : ∀ i ≤ n, (fun a : α => if cond a then step a else a)^[i] x = step^[i] x := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
      simp [hct i (by omega)]
  refine ⟨n, hn, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hit i hi
    simp only at this ⊢
    rw [this]
    exact hsz i hi
  · intro i hi
    have := hit i hi.le
    simp only at this ⊢
    rw [this]
    simp [hct i hi]
  · have := hit n le_rfl
    simp only at this ⊢
    rw [this]
    simp [hcf]
  · have := hit n le_rfl
    simp only at this ⊢
    rw [this]
    simp [hcf, hGx]

/-- The binary arithmetic facts used by the programs (proved in Erdos78_avoid_Arith). -/
structure ArithFacts : Prop where
  add : IsPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
  sub : IsPolyTime (fun p : ℕ × ℕ => p.1 - p.2)
  mul : IsPolyTime (fun p : ℕ × ℕ => p.1 * p.2)
  div : IsPolyTime (fun p : ℕ × ℕ => p.1 / p.2)
  mod : IsPolyTime (fun p : ℕ × ℕ => p.1 % p.2)
  lt : IsPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))
  eq : IsPolyTime (fun p : ℕ × ℕ => decide (p.1 = p.2))
  log2 : IsPolyTime (fun n : ℕ => Nat.log2 n)
  testBit : IsPolyTime (fun p : ℕ × ℕ => p.1.testBit p.2)
  shiftRight : IsPolyTime (fun p : ℕ × ℕ => p.1 / 2 ^ p.2)
  lowBits : IsPolyTime (fun p : ℕ × ℕ => p.1 % 2 ^ p.2)

end PT
end

-- ===== part: Arith1 =====
section
open ComplexityTheory

-- Binary arithmetic on natural numbers is polynomial-time computable.
-- Everything is functional programming on top of the toolkit: four while-loops
-- (pour, bit-serial, bit count, shift) plus invariants and size bounds.
namespace Erdos78Arith1

open BitstringEncoding

-- Fuel-driven while loops

/-- Repeat step while cond holds, at most the given number of times. -/
def whileFuel {α : Type} (cond : α → Bool) (step : α → α) : ℕ → α → α
  | 0, x => x
  | k + 1, x => if cond x then whileFuel cond step k (step x) else x

/-- The while loop, with the measure as fuel. -/
def W {α : Type} (cond : α → Bool) (step : α → α) (μ : α → ℕ) (x : α) : α := whileFuel cond step (μ x) x

section loops

variable {α : Type} {cond : α → Bool} {step : α → α} {μ : α → ℕ}

theorem whileFuel_succ_eq (hμ : ∀ a, cond a = true → μ (step a) < μ a) :
    ∀ k x, μ x ≤ k → whileFuel cond step (k + 1) x = whileFuel cond step k x := by
  intro k
  induction k with
  | zero =>
    intro x hx
    have hc : ¬ cond x = true := by
      intro h
      have := hμ x h
      omega
    simp [whileFuel, hc]
  | succ k ih =>
    intro x hx
    by_cases hc : cond x = true
    · have := hμ x hc
      show (if cond x then whileFuel cond step (k + 1) (step x) else x)
        = (if cond x then whileFuel cond step k (step x) else x)
      rw [ih (step x) (by omega)]
    · simp [whileFuel, hc]

theorem whileFuel_eq (hμ : ∀ a, cond a = true → μ (step a) < μ a) :
    ∀ k x, μ x ≤ k → whileFuel cond step k x = whileFuel cond step (μ x) x := by
  intro k x hx
  induction k, hx using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [whileFuel_succ_eq hμ k x hk, ih]

theorem W_unfold (hμ : ∀ a, cond a = true → μ (step a) < μ a) (x : α) :
    W cond step μ x = if cond x then W cond step μ (step x) else x := by
  unfold W
  by_cases hc : cond x = true
  · have h1 := hμ x hc
    obtain ⟨m, hm⟩ : ∃ m, μ x = m + 1 := ⟨μ x - 1, by omega⟩
    rw [hm]
    show (if cond x then whileFuel cond step m (step x) else x) = _
    rw [if_pos hc, if_pos hc, whileFuel_eq hμ m (step x) (by omega)]
  · rw [if_neg hc]
    cases μ x with
    | zero => rfl
    | succ m =>
      show (if cond x then whileFuel cond step m (step x) else x) = x
      rw [if_neg hc]

theorem W_induction (hμ : ∀ a, cond a = true → μ (step a) < μ a) {motive : α → Prop}
    (h : ∀ x, (cond x = true → motive (step x)) → motive x) (x : α) : motive x := by
  induction hn : μ x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    exact h x (fun hc => ih (μ (step x)) (by have := hμ x hc; omega) (step x) rfl)

theorem W_iter (hμ : ∀ a, cond a = true → μ (step a) < μ a) (x : α) :
    ∃ n, n ≤ μ x ∧ (∀ i < n, cond (step^[i] x) = true) ∧ cond (step^[n] x) = false ∧
      W cond step μ x = step^[n] x := by
  refine W_induction (μ := μ) hμ (motive := fun x => ∃ n, n ≤ μ x ∧
    (∀ i < n, cond (step^[i] x) = true) ∧ cond (step^[n] x) = false ∧
      W cond step μ x = step^[n] x) ?_ x
  intro x ih
  by_cases hc : cond x = true
  · obtain ⟨n, hn, h1, h2, h3⟩ := ih hc
    refine ⟨n + 1, by have := hμ x hc; omega, ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero => exact hc
      | succ i =>
        rw [Function.iterate_succ_apply]
        exact h1 i (by omega)
    · rw [Function.iterate_succ_apply]
      exact h2
    · rw [W_unfold hμ, if_pos hc, Function.iterate_succ_apply]
      exact h3
  · refine ⟨0, Nat.zero_le _, by intro i hi; omega, by simpa using hc, ?_⟩
    rw [W_unfold hμ, if_neg hc]
    rfl

end loops

variable {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]

-- Encoding lengths

/-- Encoding length. -/
def len (a : α) : ℕ := (bitEncode a).length

theorem len_nat (n : ℕ) : len n = Nat.size n := by
  show (Computability.encodeNat n).length = _
  rw [Erdos78Prim2.encodeNat_eq_bits, Nat.size_eq_bits_len]

theorem len_bool (b : Bool) : len b = 1 := rfl

theorem len_pair (a : α) (b : β) : len (a, b) = 2 * len a + 1 + len b := by
  show (delimit (bitEncode a) ++ bitEncode b).length = _
  simp [len, length_delimit]

theorem size_half {n : ℕ} (h : n ≠ 0) : Nat.size (n / 2) + 1 = Nat.size n := by
  have h1 := Nat.size_bit (b := n.bodd) (n := n.div2) (by rw [Nat.bit_bodd_div2]; exact h)
  rw [Nat.bit_bodd_div2, Nat.div2_val] at h1
  omega

theorem size_half_le (n : ℕ) : Nat.size (n / 2) ≤ Nat.size n :=
  Nat.size_le_size (Nat.div_le_self n 2)

theorem size_le_succ {m n : ℕ} (h : m ≤ 2 * n + 1) : Nat.size m ≤ Nat.size n + 1 := by
  rw [Nat.size_le, pow_succ]
  have := Nat.lt_size_self n
  omega

-- Generic helpers

theorem of_eq {f g : α → β} (hf : IsPolyTime f) (h : ∀ a, f a = g a) : IsPolyTime g := by
  have e : f = g := funext h
  rw [← e]
  exact hf

theorem bool3 (g : Bool → Bool → Bool → Bool) {x y z : α → Bool} (hx : IsPolyTime x)
    (hy : IsPolyTime y) (hz : IsPolyTime z) : IsPolyTime (fun a => g (x a) (y a) (z a)) := by
  refine of_eq (PT.ite hx
    (PT.ite hy
      (PT.ite hz (PT.const (g true true true)) (PT.const (g true true false)))
      (PT.ite hz (PT.const (g true false true)) (PT.const (g true false false))))
    (PT.ite hy
      (PT.ite hz (PT.const (g false true true)) (PT.const (g false true false)))
      (PT.ite hz (PT.const (g false false true)) (PT.const (g false false false))))) ?_
  intro a
  cases x a <;> cases y a <;> cases z a <;> simp

theorem bool2 (g : Bool → Bool → Bool) {x y : α → Bool} (hx : IsPolyTime x)
    (hy : IsPolyTime y) : IsPolyTime (fun a => g (x a) (y a)) :=
  bool3 (fun a b _ => g a b) hx hy (PT.const true)

theorem bool1 (g : Bool → Bool) {x : α → Bool} (hx : IsPolyTime x) :
    IsPolyTime (fun a => g (x a)) :=
  bool3 (fun a _ _ => g a) hx (PT.const true) (PT.const true)

-- The loop closure

/-- The loop closure in the form used below: a measure bounded by the encoding length that
  drops each round, and a state that grows by at most a constant each round. -/
theorem loopW (cond : α → Bool) (step : α → α) (hc : IsPolyTime cond) (hs : IsPolyTime step)
    (μ : α → ℕ) (c : ℕ) (hμ : ∀ a, cond a = true → μ (step a) < μ a)
    (hT : ∀ x, μ x ≤ len x) (hlen : ∀ a, cond a = true → len (step a) ≤ len a + c) :
    IsPolyTime (W cond step μ) := by
  refine PT.loop cond step hc hs Polynomial.X (Polynomial.C (c + 1) * Polynomial.X) _ ?_
  intro x
  obtain ⟨n, hn, h1, h2, h3⟩ := W_iter hμ x
  have hnx : n ≤ len x := hn.trans (hT x)
  refine ⟨n, by simpa [len] using hnx, ?_, h1, h2, h3⟩
  have key : ∀ i ≤ n, len (step^[i] x) ≤ len x + c * i := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      rw [Function.iterate_succ_apply']
      have h5 := hlen _ (h1 i (by omega))
      have h6 := ih (by omega)
      rw [Nat.mul_succ]
      omega
  intro i hi
  have h7 := key i hi
  have h4 : c * i ≤ c * len x := Nat.mul_le_mul_left _ (hi.trans hnx)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  show len (step^[i] x) ≤ (c + 1) * len x
  rw [Nat.succ_mul]
  omega

-- Pushing a bit on a number, and pouring a sentinel stack into an accumulator

/-- Append a bit at the low end. -/
def push (b : Bool) (s : ℕ) : ℕ := if b then 2 * s + 1 else 2 * s

theorem push_pt {b : α → Bool} {s : α → ℕ} (hb : IsPolyTime b) (hs : IsPolyTime s) :
    IsPolyTime (fun a => push (b a) (s a)) :=
  PT.ite hb (PT.comp (g := fun n : ℕ => 2 * n + 1) PT.doubleSucc hs)
    (PT.comp (g := fun n : ℕ => 2 * n) PT.double hs)

theorem push_eq (b : Bool) (s : ℕ) : push b s = 2 * s + b.toNat := by
  cases b <;> simp [push]

theorem push_div (b : Bool) (s : ℕ) : push b s / 2 = s := by
  cases b <;> simp [push]
  omega

theorem push_odd (b : Bool) (s : ℕ) : decide (push b s % 2 = 1) = b := by
  cases b <;> simp [push]

theorem push_ne_zero (b : Bool) {s : ℕ} (h : s ≠ 0) : push b s ≠ 0 := by
  rw [push_eq]
  omega

theorem size_push_le (b : Bool) (s : ℕ) : Nat.size (push b s) ≤ Nat.size s + 1 := by
  apply size_le_succ
  rw [push_eq]
  cases b <;> simp

/-- Pour loop guard: the stack still has a bit above the sentinel. -/
def pcond (x : ℕ × ℕ) : Bool := !decide (x.2 / 2 = 0)

/-- Pour loop body: move the low bit of the stack to the low end of the accumulator. -/
def pstep (x : ℕ × ℕ) : ℕ × ℕ := (push (decide (x.2 % 2 = 1)) x.1, x.2 / 2)

/-- Pour loop measure. -/
def pmu (x : ℕ × ℕ) : ℕ := Nat.size x.2

theorem pour_dec : ∀ a, pcond a = true → pmu (pstep a) < pmu a := by
  rintro ⟨r, s⟩ h
  have hs : s ≠ 0 := by
    rintro rfl
    simp [pcond] at h
  have := size_half hs
  show Nat.size (s / 2) < Nat.size s
  omega

/-- The pour loop. -/
def pourW : ℕ × ℕ → ℕ × ℕ := W pcond pstep pmu

theorem pour_pt : IsPolyTime pourW := by
  refine loopW pcond pstep ?_ ?_ pmu 2 pour_dec ?_ ?_
  · exact bool1 (fun b => !b) (PT.comp PT.isZero (PT.comp PT.half PT.snd))
  · exact PT.pair (push_pt (PT.comp PT.odd PT.snd) PT.fst) (PT.comp PT.half PT.snd)
  · rintro ⟨r, s⟩
    rw [len_pair, len_nat, len_nat]
    show Nat.size s ≤ _
    omega
  · rintro ⟨r, s⟩ _
    show len (push (decide (s % 2 = 1)) r, s / 2) ≤ len (r, s) + 2
    rw [len_pair, len_pair, len_nat, len_nat, len_nat, len_nat]
    have h1 := size_push_le (decide (s % 2 = 1)) r
    have h2 := size_half_le s
    omega

/-- Pour the stack s (sentinel on top) into the accumulator r. -/
def P (r s : ℕ) : ℕ := (pourW (r, s)).1

theorem P_pt {r s : α → ℕ} (hr : IsPolyTime r) (hs : IsPolyTime s) :
    IsPolyTime (fun a => P (r a) (s a)) :=
  PT.comp PT.fst (PT.comp pour_pt (PT.pair hr hs))

theorem P_one (r : ℕ) : P r 1 = r := by
  unfold P pourW
  rw [W_unfold pour_dec]
  simp [pcond]

theorem P_push (r : ℕ) (b : Bool) {s : ℕ} (h : s ≠ 0) : P r (push b s) = P (push b r) s := by
  unfold P pourW
  rw [W_unfold pour_dec]
  have hc : pcond (r, push b s) = true := by simp [pcond, push_div, h]
  rw [if_pos hc]
  simp [pstep, push_div, push_odd]

-- The bit-serial loop

/-- Guard: one of the two numbers still has bits. -/
def scond (x : (ℕ × ℕ) × (Bool × ℕ)) : Bool := !(decide (x.1.1 = 0) && decide (x.1.2 = 0))

/-- Body: consume the low bits of both numbers, update the carry, push the output bit. -/
def sstep (out next : Bool → Bool → Bool → Bool) (x : (ℕ × ℕ) × (Bool × ℕ)) :
    (ℕ × ℕ) × (Bool × ℕ) :=
  ((x.1.1 / 2, x.1.2 / 2),
    (next (decide (x.1.1 % 2 = 1)) (decide (x.1.2 % 2 = 1)) x.2.1,
      push (out (decide (x.1.1 % 2 = 1)) (decide (x.1.2 % 2 = 1)) x.2.1) x.2.2))

/-- Measure: total number of bits left. -/
def smu (x : (ℕ × ℕ) × (Bool × ℕ)) : ℕ := Nat.size x.1.1 + Nat.size x.1.2

theorem ser_dec (out next : Bool → Bool → Bool → Bool) :
    ∀ a, scond a = true → smu (sstep out next a) < smu a := by
  rintro ⟨⟨a, b⟩, c, s⟩ h
  show Nat.size (a / 2) + Nat.size (b / 2) < Nat.size a + Nat.size b
  have h1 := size_half_le a
  have h2 := size_half_le b
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      rintro rfl
      simp [scond, ha] at h
    have := size_half hb
    omega
  · have := size_half ha
    omega

/-- The bit-serial loop. -/
def serW (out next : Bool → Bool → Bool → Bool) : (ℕ × ℕ) × (Bool × ℕ) → (ℕ × ℕ) × (Bool × ℕ) :=
  W scond (sstep out next) smu

theorem ser_pt (out next : Bool → Bool → Bool → Bool) : IsPolyTime (serW out next) := by
  have ha : IsPolyTime (fun x : (ℕ × ℕ) × (Bool × ℕ) => x.1.1) := PT.comp PT.fst PT.fst
  have hb : IsPolyTime (fun x : (ℕ × ℕ) × (Bool × ℕ) => x.1.2) := PT.comp PT.snd PT.fst
  have hc : IsPolyTime (fun x : (ℕ × ℕ) × (Bool × ℕ) => x.2.1) := PT.comp PT.fst PT.snd
  have hs : IsPolyTime (fun x : (ℕ × ℕ) × (Bool × ℕ) => x.2.2) := PT.comp PT.snd PT.snd
  refine loopW scond (sstep out next) ?_ ?_ smu 1 (ser_dec out next) ?_ ?_
  · exact bool2 (fun p q => !(p && q)) (PT.comp PT.isZero ha) (PT.comp PT.isZero hb)
  · exact PT.pair (PT.pair (PT.comp PT.half ha) (PT.comp PT.half hb))
      (PT.pair (bool3 next (PT.comp PT.odd ha) (PT.comp PT.odd hb) hc)
        (push_pt (bool3 out (PT.comp PT.odd ha) (PT.comp PT.odd hb) hc) hs))
  · rintro ⟨⟨a, b⟩, c, s⟩
    rw [len_pair, len_pair, len_nat, len_nat]
    show Nat.size a + Nat.size b ≤ _
    omega
  · rintro ⟨⟨a, b⟩, c, s⟩ _
    show len ((a / 2, b / 2), (next (decide (a % 2 = 1)) (decide (b % 2 = 1)) c,
      push (out (decide (a % 2 = 1)) (decide (b % 2 = 1)) c) s)) ≤ len ((a, b), (c, s)) + 1
    simp only [len_pair, len_nat, len_bool]
    have h1 := size_push_le (out (decide (a % 2 = 1)) (decide (b % 2 = 1)) c) s
    have h2 := size_half_le a
    have h3 := size_half_le b
    omega

-- Addition

/-- Sum bit. -/
def bxor3 (a b c : Bool) : Bool := Bool.xor (Bool.xor a b) c

/-- Carry out of a full adder. -/
def bmaj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- Borrow out of a full subtractor. -/
def bbor (a b c : Bool) : Bool := (!a && (b || c)) || (b && c)

theorem add_spec : ∀ x : (ℕ × ℕ) × (Bool × ℕ), x.2.2 ≠ 0 →
    (serW bxor3 bmaj x).2.2 ≠ 0 ∧
      P 0 (push (serW bxor3 bmaj x).2.1 (serW bxor3 bmaj x).2.2)
        = P (x.1.1 + x.1.2 + x.2.1.toNat) x.2.2 := by
  intro x
  refine W_induction (ser_dec bxor3 bmaj) (motive := fun x => x.2.2 ≠ 0 →
    (serW bxor3 bmaj x).2.2 ≠ 0 ∧
      P 0 (push (serW bxor3 bmaj x).2.1 (serW bxor3 bmaj x).2.2)
        = P (x.1.1 + x.1.2 + x.2.1.toNat) x.2.2) ?_ x
  rintro ⟨⟨a, b⟩, c, s⟩ ih hs
  have hs' : s ≠ 0 := hs
  unfold serW at ih ⊢
  rw [W_unfold (ser_dec bxor3 bmaj)]
  by_cases hc : scond ((a, b), (c, s)) = true
  · rw [if_pos hc]
    obtain ⟨h1, h2⟩ := ih hc (push_ne_zero _ hs')
    refine ⟨h1, h2.trans ?_⟩
    show P (a / 2 + b / 2 + (bmaj (decide (a % 2 = 1)) (decide (b % 2 = 1)) c).toNat)
      (push (bxor3 (decide (a % 2 = 1)) (decide (b % 2 = 1)) c) s) = P (a + b + c.toNat) s
    rw [P_push _ _ hs']
    congr 1
    rw [push_eq]
    have ea := Nat.div_add_mod a 2
    have eb := Nat.div_add_mod b 2
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
      cases c <;> simp [ha, hb, bxor3, bmaj] <;> omega
  · rw [if_neg hc]
    have hab : a = 0 ∧ b = 0 := by simpa [scond] using hc
    obtain ⟨rfl, rfl⟩ := hab
    refine ⟨hs', ?_⟩
    show P 0 (push c s) = P (0 + 0 + c.toNat) s
    rw [P_push _ _ hs', push_eq]

theorem add_polyTime : IsPolyTime (fun p : ℕ × ℕ => p.1 + p.2) := by
  have h1 : IsPolyTime (fun p : ℕ × ℕ => serW bxor3 bmaj (p, (false, 1))) :=
    PT.comp (ser_pt bxor3 bmaj) (PT.pair PT.id' (PT.const (false, 1)))
  have h2 : IsPolyTime (fun p : ℕ × ℕ => P 0 (push (serW bxor3 bmaj (p, (false, 1))).2.1
      (serW bxor3 bmaj (p, (false, 1))).2.2)) :=
    P_pt (PT.const 0) (push_pt (PT.comp PT.fst (PT.comp PT.snd h1))
      (PT.comp PT.snd (PT.comp PT.snd h1)))
  refine of_eq h2 ?_
  intro p
  have := (add_spec (p, (false, 1)) (by simp)).2
  rw [this, P_one]
  simp

theorem succ_pt : IsPolyTime (fun n : ℕ => n + 1) :=
  PT.comp (g := fun p : ℕ × ℕ => p.1 + p.2) add_polyTime (PT.pair PT.id' (PT.const 1))

-- Comparison and truncated subtraction

theorem lt_spec : ∀ x : (ℕ × ℕ) × (Bool × ℕ),
    (serW bxor3 bbor x).2.1 = decide (x.1.1 < x.1.2 + x.2.1.toNat) := by
  intro x
  refine W_induction (ser_dec bxor3 bbor) (motive := fun x =>
    (serW bxor3 bbor x).2.1 = decide (x.1.1 < x.1.2 + x.2.1.toNat)) ?_ x
  rintro ⟨⟨a, b⟩, c, s⟩ ih
  unfold serW at ih ⊢
  rw [W_unfold (ser_dec bxor3 bbor)]
  by_cases hc : scond ((a, b), (c, s)) = true
  · rw [if_pos hc, ih hc]
    show decide (a / 2 < b / 2 + (bbor (decide (a % 2 = 1)) (decide (b % 2 = 1)) c).toNat)
      = decide (a < b + c.toNat)
    have ea := Nat.div_add_mod a 2
    have eb := Nat.div_add_mod b 2
    rw [decide_eq_decide]
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
      cases c <;> simp [ha, hb, bbor] <;> omega
  · rw [if_neg hc]
    have hab : a = 0 ∧ b = 0 := by simpa [scond] using hc
    obtain ⟨rfl, rfl⟩ := hab
    show c = decide (0 < 0 + c.toNat)
    cases c <;> simp

theorem sub_spec : ∀ x : (ℕ × ℕ) × (Bool × ℕ), x.2.2 ≠ 0 → x.1.2 + x.2.1.toNat ≤ x.1.1 →
    (serW bxor3 bbor x).2.2 ≠ 0 ∧
      P 0 (serW bxor3 bbor x).2.2 = P (x.1.1 - x.1.2 - x.2.1.toNat) x.2.2 := by
  intro x
  refine W_induction (ser_dec bxor3 bbor) (motive := fun x => x.2.2 ≠ 0 →
    x.1.2 + x.2.1.toNat ≤ x.1.1 → (serW bxor3 bbor x).2.2 ≠ 0 ∧
      P 0 (serW bxor3 bbor x).2.2 = P (x.1.1 - x.1.2 - x.2.1.toNat) x.2.2) ?_ x
  rintro ⟨⟨a, b⟩, c, s⟩ ih hs hle
  have hs' : s ≠ 0 := hs
  have hle' : b + c.toNat ≤ a := hle
  unfold serW at ih ⊢
  rw [W_unfold (ser_dec bxor3 bbor)]
  have ea := Nat.div_add_mod a 2
  have eb := Nat.div_add_mod b 2
  by_cases hc : scond ((a, b), (c, s)) = true
  · rw [if_pos hc]
    have hle2 : b / 2 + (bbor (decide (a % 2 = 1)) (decide (b % 2 = 1)) c).toNat ≤ a / 2 := by
      revert hle'
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
        cases c <;> simp [ha, hb, bbor] <;> omega
    obtain ⟨h1, h2⟩ := ih hc (push_ne_zero _ hs') hle2
    refine ⟨h1, h2.trans ?_⟩
    show P (a / 2 - b / 2 - (bbor (decide (a % 2 = 1)) (decide (b % 2 = 1)) c).toNat)
      (push (bxor3 (decide (a % 2 = 1)) (decide (b % 2 = 1)) c) s) = P (a - b - c.toNat) s
    rw [P_push _ _ hs']
    congr 1
    rw [push_eq]
    revert hle' hle2
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
      cases c <;> simp [ha, hb, bxor3, bbor] <;> omega
  · rw [if_neg hc]
    have hab : a = 0 ∧ b = 0 := by simpa [scond] using hc
    obtain ⟨rfl, rfl⟩ := hab
    refine ⟨hs', ?_⟩
    have hc0 : c = false := by
      revert hle'
      cases c <;> simp
    subst hc0
    rfl

theorem lt_polyTime : IsPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  have h1 : IsPolyTime (fun p : ℕ × ℕ => serW bxor3 bbor (p, (false, 1))) :=
    PT.comp (ser_pt bxor3 bbor) (PT.pair PT.id' (PT.const (false, 1)))
  have h2 : IsPolyTime (fun p : ℕ × ℕ => (serW bxor3 bbor (p, (false, 1))).2.1) :=
    PT.comp PT.fst (PT.comp PT.snd h1)
  refine of_eq h2 ?_
  intro p
  rw [lt_spec]
  simp

theorem sub_polyTime : IsPolyTime (fun p : ℕ × ℕ => p.1 - p.2) := by
  have h1 : IsPolyTime (fun p : ℕ × ℕ => serW bxor3 bbor (p, (false, 1))) :=
    PT.comp (ser_pt bxor3 bbor) (PT.pair PT.id' (PT.const (false, 1)))
  have h2 : IsPolyTime (fun p : ℕ × ℕ => P 0 (serW bxor3 bbor (p, (false, 1))).2.2) :=
    P_pt (PT.const 0) (PT.comp PT.snd (PT.comp PT.snd h1))
  have h3 : IsPolyTime (fun p : ℕ × ℕ => if decide (p.1 < p.2) then 0
      else P 0 (serW bxor3 bbor (p, (false, 1))).2.2) :=
    PT.ite lt_polyTime (PT.const 0) h2
  refine of_eq h3 ?_
  intro p
  by_cases h : p.1 < p.2
  · simp [h]
    omega
  · have := (sub_spec (p, (false, 1)) (by simp) (by simp; omega)).2
    simp only [h, decide_false, Bool.false_eq_true, if_false]
    rw [this, P_one]
    simp

theorem eq_polyTime : IsPolyTime (fun p : ℕ × ℕ => decide (p.1 = p.2)) := by
  have hswap : IsPolyTime (fun p : ℕ × ℕ => decide (p.2 < p.1)) :=
    PT.comp (g := fun p : ℕ × ℕ => decide (p.1 < p.2)) lt_polyTime (PT.pair PT.snd PT.fst)
  refine of_eq (bool2 (fun x y => !x && !y) lt_polyTime hswap) ?_
  intro p
  rcases lt_trichotomy p.1 p.2 with h | h | h
  · have h2 : ¬ p.2 < p.1 := by omega
    have h3 : p.1 ≠ p.2 := by omega
    simp [h, h3]
  · simp [h]
  · have h2 : ¬ p.1 < p.2 := by omega
    have h3 : p.1 ≠ p.2 := by omega
    simp [h, h3]

theorem pred_pt : IsPolyTime (fun n : ℕ => n - 1) :=
  PT.comp (g := fun p : ℕ × ℕ => p.1 - p.2) sub_polyTime (PT.pair PT.id' (PT.const 1))

-- Bit length and binary logarithm

/-- Guard of the counting loop. -/
def zcond (x : ℕ × ℕ) : Bool := !decide (x.1 = 0)

/-- Body of the counting loop: halve and count. -/
def zstep (x : ℕ × ℕ) : ℕ × ℕ := (x.1 / 2, x.2 + 1)

/-- Measure of the counting loop. -/
def zmu (x : ℕ × ℕ) : ℕ := Nat.size x.1

theorem z_dec : ∀ a, zcond a = true → zmu (zstep a) < zmu a := by
  rintro ⟨n, k⟩ h
  have hn : n ≠ 0 := by simpa [zcond] using h
  have := size_half hn
  show Nat.size (n / 2) < Nat.size n
  omega

theorem z_pt : IsPolyTime (W zcond zstep zmu) := by
  refine loopW zcond zstep ?_ ?_ zmu 1 z_dec ?_ ?_
  · exact bool1 (fun b => !b) (PT.comp PT.isZero PT.fst)
  · exact PT.pair (PT.comp PT.half PT.fst) (PT.comp (g := fun n : ℕ => n + 1) succ_pt PT.snd)
  · rintro ⟨n, k⟩
    rw [len_pair, len_nat, len_nat]
    show Nat.size n ≤ _
    omega
  · rintro ⟨n, k⟩ _
    show len (n / 2, k + 1) ≤ len (n, k) + 1
    simp only [len_pair, len_nat]
    have h1 := size_half_le n
    have h2 : Nat.size (k + 1) ≤ Nat.size k + 1 := size_le_succ (by omega)
    omega

theorem z_spec : ∀ x : ℕ × ℕ, (W zcond zstep zmu x).2 = x.2 + Nat.size x.1 := by
  intro x
  refine W_induction z_dec (motive := fun x =>
    (W zcond zstep zmu x).2 = x.2 + Nat.size x.1) ?_ x
  rintro ⟨n, k⟩ ih
  rw [W_unfold z_dec]
  by_cases hc : zcond (n, k) = true
  · rw [if_pos hc, ih hc]
    have hn : n ≠ 0 := by simpa [zcond] using hc
    have := size_half hn
    show k + 1 + Nat.size (n / 2) = k + Nat.size n
    omega
  · rw [if_neg hc]
    have hn : n = 0 := by simpa [zcond] using hc
    subst hn
    simp

theorem size_pt : IsPolyTime (fun n : ℕ => Nat.size n) := by
  have h : IsPolyTime (fun n : ℕ => (W zcond zstep zmu (n, 0)).2) :=
    PT.comp PT.snd (PT.comp z_pt (PT.pair PT.id' (PT.const 0)))
  refine of_eq h ?_
  intro n
  rw [z_spec]
  simp

theorem log2_eq (n : ℕ) : Nat.log2 n = Nat.size n - 1 := by
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [Nat.log2_eq_log_two]
    have h1 : Nat.size n ≤ Nat.log 2 n + 1 := by
      rw [Nat.size_le]
      exact Nat.lt_pow_succ_log_self (by norm_num) n
    have h2 : Nat.log 2 n < Nat.size n := by
      rw [Nat.lt_size]
      exact Nat.pow_log_le_self 2 hn
    omega

theorem log2_polyTime : IsPolyTime (fun n : ℕ => Nat.log2 n) := by
  refine of_eq (PT.comp (g := fun n : ℕ => n - 1) pred_pt size_pt) ?_
  intro n
  rw [log2_eq]

-- Shifts, bit tests and low bits

/-- Guard of the shift loop: bits left and shift count left. -/
def hcond (x : (ℕ × ℕ) × ℕ) : Bool := !(decide (x.1.1 = 0) || decide (x.1.2 = 0))

/-- Body of the shift loop: drop the low bit, count down, remember the bit. -/
def hstep (x : (ℕ × ℕ) × ℕ) : (ℕ × ℕ) × ℕ :=
  ((x.1.1 / 2, x.1.2 - 1), push (decide (x.1.1 % 2 = 1)) x.2)

/-- Measure of the shift loop. -/
def hmu (x : (ℕ × ℕ) × ℕ) : ℕ := Nat.size x.1.1

theorem h_dec : ∀ a, hcond a = true → hmu (hstep a) < hmu a := by
  rintro ⟨⟨n, i⟩, s⟩ h
  have hn : n ≠ 0 := by
    rintro rfl
    simp [hcond] at h
  have := size_half hn
  show Nat.size (n / 2) < Nat.size n
  omega

theorem h_pt : IsPolyTime (W hcond hstep hmu) := by
  have hn : IsPolyTime (fun x : (ℕ × ℕ) × ℕ => x.1.1) := PT.comp PT.fst PT.fst
  have hi : IsPolyTime (fun x : (ℕ × ℕ) × ℕ => x.1.2) := PT.comp PT.snd PT.fst
  refine loopW hcond hstep ?_ ?_ hmu 1 h_dec ?_ ?_
  · exact bool2 (fun p q => !(p || q)) (PT.comp PT.isZero hn) (PT.comp PT.isZero hi)
  · exact PT.pair (PT.pair (PT.comp PT.half hn) (PT.comp (g := fun n : ℕ => n - 1) pred_pt hi))
      (push_pt (PT.comp PT.odd hn) PT.snd)
  · rintro ⟨⟨n, i⟩, s⟩
    rw [len_pair, len_pair, len_nat]
    show Nat.size n ≤ _
    omega
  · rintro ⟨⟨n, i⟩, s⟩ _
    show len ((n / 2, i - 1), push (decide (n % 2 = 1)) s) ≤ len ((n, i), s) + 1
    simp only [len_pair, len_nat]
    have h1 := size_half_le n
    have h2 : Nat.size (i - 1) ≤ Nat.size i := Nat.size_le_size (Nat.sub_le i 1)
    have h3 := size_push_le (decide (n % 2 = 1)) s
    omega

theorem h_spec : ∀ x : (ℕ × ℕ) × ℕ, (W hcond hstep hmu x).1.1 = x.1.1 / 2 ^ x.1.2 ∧
    (x.2 ≠ 0 → (W hcond hstep hmu x).2 ≠ 0 ∧
      P 0 (W hcond hstep hmu x).2 = P (x.1.1 % 2 ^ x.1.2) x.2) := by
  intro x
  refine W_induction h_dec (motive := fun x =>
    (W hcond hstep hmu x).1.1 = x.1.1 / 2 ^ x.1.2 ∧
    (x.2 ≠ 0 → (W hcond hstep hmu x).2 ≠ 0 ∧
      P 0 (W hcond hstep hmu x).2 = P (x.1.1 % 2 ^ x.1.2) x.2)) ?_ x
  rintro ⟨⟨n, i⟩, s⟩ ih
  rw [W_unfold h_dec]
  by_cases hc : hcond ((n, i), s) = true
  · rw [if_pos hc]
    obtain ⟨h1, h2⟩ := ih hc
    have hni : n ≠ 0 ∧ i ≠ 0 := by simpa [hcond] using hc
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have e1 : n / 2 / 2 ^ j = n / 2 ^ (j + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ']
    have e2 : push (decide (n % 2 = 1)) (n / 2 % 2 ^ j) = n % 2 ^ (j + 1) := by
      rw [push_eq, pow_succ', Nat.mod_mul]
      have hbit : (decide (n % 2 = 1)).toNat = n % 2 := by
        rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [hn]
      omega
    refine ⟨h1.trans e1, ?_⟩
    intro hs
    have hs' : s ≠ 0 := hs
    obtain ⟨h3, h4⟩ := h2 (push_ne_zero _ hs')
    refine ⟨h3, h4.trans ?_⟩
    show P (n / 2 % 2 ^ j) (push (decide (n % 2 = 1)) s) = P (n % 2 ^ (j + 1)) s
    rw [P_push _ _ hs', e2]
  · rw [if_neg hc]
    have hni : n = 0 ∨ i = 0 := by
      by_contra hcon
      rw [not_or] at hcon
      exact hc (by simp [hcond, hcon.1, hcon.2])
    rcases hni with rfl | rfl
    · simp
    · simp [Nat.mod_one]

theorem shiftRight_polyTime : IsPolyTime (fun p : ℕ × ℕ => p.1 / 2 ^ p.2) := by
  have h : IsPolyTime (fun p : ℕ × ℕ => (W hcond hstep hmu (p, 1)).1.1) :=
    PT.comp PT.fst (PT.comp PT.fst (PT.comp h_pt (PT.pair PT.id' (PT.const 1))))
  refine of_eq h ?_
  intro p
  exact (h_spec (p, 1)).1

theorem testBit_polyTime : IsPolyTime (fun p : ℕ × ℕ => p.1.testBit p.2) := by
  refine of_eq (PT.comp (g := fun n : ℕ => decide (n % 2 = 1)) PT.odd shiftRight_polyTime) ?_
  intro p
  rw [Nat.testBit_eq_decide_div_mod_eq]

theorem lowBits_polyTime : IsPolyTime (fun p : ℕ × ℕ => p.1 % 2 ^ p.2) := by
  have h : IsPolyTime (fun p : ℕ × ℕ => P 0 (W hcond hstep hmu (p, 1)).2) :=
    P_pt (PT.const 0) (PT.comp PT.snd (PT.comp h_pt (PT.pair PT.id' (PT.const 1))))
  refine of_eq h ?_
  intro p
  have := ((h_spec (p, 1)).2 (by simp)).2
  rw [this, P_one]

end Erdos78Arith1
end

-- ===== part: Arith2 =====
section
open ComplexityTheory

/-! Multiplication, division and remainder of binary naturals are polynomial-time computable,
  given addition, subtraction and comparison. Pure functional programming over the toolkit. -/
namespace Erdos78Arith2

/- Size bookkeeping. -/

theorem len_nat (n : ℕ) : (BitstringEncoding.bitEncode n).length = Nat.size n := by
  show (Computability.encodeNat n).length = _
  rw [Erdos78Prim2.encodeNat_eq_bits, Nat.size_eq_bits_len]

theorem len_pair {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (a : α) (b : β) :
    (BitstringEncoding.bitEncode (a, b)).length =
      2 * (BitstringEncoding.bitEncode a).length + 1 + (BitstringEncoding.bitEncode b).length := by
  show (BitstringEncoding.delimit (BitstringEncoding.bitEncode a) ++
    BitstringEncoding.bitEncode b).length = _
  simp [BitstringEncoding.length_delimit]

theorem size_mul_pow (a i : ℕ) : Nat.size (a * 2 ^ i) ≤ Nat.size a + i := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity)

theorem size_div_pow (b i : ℕ) : Nat.size (b / 2 ^ i) ≤ Nat.size b :=
  Nat.size_le_size (Nat.div_le_self _ _)

/- A loop driven by a counter that is halved every round: it runs exactly as many rounds as the
  counter has bits. -/
theorem counterLoop {α : Type} [BitstringEncoding α] (step : α → α) (cnt : α → ℕ)
    (hs : IsPolyTime step) (hc : IsPolyTime cnt) (hcnt : ∀ x, cnt (step x) = cnt x / 2)
    (pB : Polynomial ℕ)
    (hT : ∀ x, Nat.size (cnt x) ≤ (BitstringEncoding.bitEncode x).length)
    (hB : ∀ x i, i ≤ Nat.size (cnt x) →
      (BitstringEncoding.bitEncode (step^[i] x)).length ≤
        pB.eval (BitstringEncoding.bitEncode x).length) :
    IsPolyTime (fun x => step^[Nat.size (cnt x)] x) := by
  have hiter : ∀ x i, cnt (step^[i] x) = cnt x / 2 ^ i := by
    intro x i
    induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply', hcnt, ih, Nat.div_div_eq_div_mul, pow_succ]
  have hcond : IsPolyTime (fun x : α => if decide (cnt x = 0) then false else true) :=
    PT.ite (PT.comp PT.isZero hc) (PT.const false) (PT.const true)
  refine PT.loop _ step hcond hs Polynomial.X pB _ ?_
  intro x
  refine ⟨Nat.size (cnt x), ?_, hB x, ?_, ?_, rfl⟩
  · simpa using hT x
  · intro i hi
    have h2 : 2 ^ i ≤ cnt x := Nat.lt_size.1 hi
    have h3 : cnt x / 2 ^ i ≠ 0 := (Nat.div_pos h2 (by positivity)).ne'
    simp [hiter, h3]
  · have h3 : cnt x / 2 ^ Nat.size (cnt x) = 0 := Nat.div_eq_of_lt (Nat.lt_size_self _)
    simp [hiter, h3]

/- Multiplication by shift-and-add. State (a, b, acc). -/

def mulStep (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (2 * s.1, s.2.1 / 2, if decide (s.2.1 % 2 = 1) then s.2.2 + s.1 else s.2.2)

theorem mulStep_polyTime (hadd : IsPolyTime (fun p : ℕ × ℕ => p.1 + p.2)) :
    IsPolyTime mulStep :=
  PT.pair (PT.comp PT.double PT.fst)
    (PT.pair (PT.comp PT.half (PT.comp PT.fst PT.snd))
      (PT.ite (PT.comp PT.odd (PT.comp PT.fst PT.snd))
        (PT.comp hadd (PT.pair (PT.comp PT.snd PT.snd) PT.fst)) (PT.comp PT.snd PT.snd)))

theorem mulStep_iter (a b acc i : ℕ) :
    mulStep^[i] (a, b, acc) = (a * 2 ^ i, b / 2 ^ i, acc + a * (b % 2 ^ i)) := by
  induction i with
  | zero => simp [Nat.mod_one]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    have h1 : 2 * (a * 2 ^ i) = a * 2 ^ (i + 1) := by ring
    have h2 : b / 2 ^ i / 2 = b / 2 ^ (i + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
    have h3 : b % 2 ^ (i + 1) = b % 2 ^ i + 2 ^ i * (b / 2 ^ i % 2) := Nat.mod_pow_succ
    have h4 : b / 2 ^ i % 2 = 0 ∨ b / 2 ^ i % 2 = 1 := by omega
    simp only [mulStep, h1, h2, h3]
    rcases h4 with h | h
    · simp [h]
    · simp [h]; ring

theorem mulLoop_polyTime (hadd : IsPolyTime (fun p : ℕ × ℕ => p.1 + p.2)) :
    IsPolyTime (fun s : ℕ × ℕ × ℕ => mulStep^[Nat.size s.2.1] s) := by
  refine counterLoop mulStep (fun s => s.2.1) (mulStep_polyTime hadd) (PT.comp PT.fst PT.snd)
    (fun _ => rfl) (Polynomial.C 5 * Polynomial.X + Polynomial.C 5) ?_ ?_
  · rintro ⟨a, b, acc⟩
    simp only [len_pair, len_nat]
    omega
  · rintro ⟨a, b, acc⟩ i hi
    rw [mulStep_iter]
    simp only [len_pair, len_nat, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    have h1 := size_mul_pow a i
    have h2 := size_div_pow b i
    have h3 : Nat.size (acc + a * (b % 2 ^ i)) ≤ Nat.size acc + Nat.size a + i + 1 := by
      rw [Nat.size_le]
      have e1 : acc < 2 ^ Nat.size acc := Nat.lt_size_self acc
      have e2 : a * (b % 2 ^ i) < 2 ^ Nat.size a * 2 ^ i :=
        Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.mod_lt _ (by positivity))
      have e3 : 2 ^ Nat.size acc ≤ 2 ^ (Nat.size acc + Nat.size a + i) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have e4 : 2 ^ Nat.size a * 2 ^ i ≤ 2 ^ (Nat.size acc + Nat.size a + i) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have e5 : 2 ^ (Nat.size acc + Nat.size a + i + 1) =
          2 * 2 ^ (Nat.size acc + Nat.size a + i) := by ring
      omega
    simp only at hi
    omega

theorem mulLoop_val (a b : ℕ) :
    mulStep^[Nat.size b] (a, b, 0) = (a * 2 ^ Nat.size b, 0, a * b) := by
  rw [mulStep_iter, Nat.div_eq_of_lt (Nat.lt_size_self b), Nat.mod_eq_of_lt (Nat.lt_size_self b),
    zero_add]

theorem mul_polyTime (hadd : IsPolyTime (fun p : ℕ × ℕ => p.1 + p.2)) :
    IsPolyTime (fun p : ℕ × ℕ => p.1 * p.2) := by
  have h := PT.comp (PT.comp PT.snd PT.snd)
    (PT.comp (mulLoop_polyTime hadd) (PT.pair PT.fst (PT.pair PT.snd (PT.const 0))))
  have e : (fun p : ℕ × ℕ => p.1 * p.2) =
      (fun p : ℕ × ℕ => (mulStep^[Nat.size p.2] (p.1, p.2, 0)).2.2) := by
    funext p
    rw [mulLoop_val]
  rw [e]
  exact h

/-- Shifting up: the second argument times two to the bit length of the first. -/
theorem shiftUp_polyTime (hadd : IsPolyTime (fun p : ℕ × ℕ => p.1 + p.2)) :
    IsPolyTime (fun p : ℕ × ℕ => p.2 * 2 ^ Nat.size p.1) := by
  have h := PT.comp PT.fst
    (PT.comp (mulLoop_polyTime hadd) (PT.pair PT.snd (PT.pair PT.fst (PT.const 0))))
  have e : (fun p : ℕ × ℕ => p.2 * 2 ^ Nat.size p.1) =
      (fun p : ℕ × ℕ => (mulStep^[Nat.size p.1] (p.2, p.1, 0)).1) := by
    funext p
    rw [mulLoop_val]
  rw [e]
  exact h

/- Division with remainder by shift-and-subtract. State (r, d, q, c): remainder so far, the
  shifted divisor, quotient so far, and a counter. -/

def divStep (s : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (if decide (s.1 < s.2.1) then s.1 else s.1 - s.2.1, s.2.1 / 2,
    if decide (s.1 < s.2.1) then 2 * s.2.2.1 else 2 * s.2.2.1 + 1, s.2.2.2 / 2)

theorem divStep_polyTime (hsub : IsPolyTime (fun p : ℕ × ℕ => p.1 - p.2))
    (hlt : IsPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))) : IsPolyTime divStep :=
  have hc : IsPolyTime (fun s : ℕ × ℕ × ℕ × ℕ => decide (s.1 < s.2.1)) :=
    PT.comp hlt (PT.pair PT.fst (PT.comp PT.fst PT.snd))
  have hq : IsPolyTime (fun s : ℕ × ℕ × ℕ × ℕ => s.2.2.1) :=
    PT.comp PT.fst (PT.comp PT.snd PT.snd)
  PT.pair (PT.ite hc PT.fst (PT.comp hsub (PT.pair PT.fst (PT.comp PT.fst PT.snd))))
    (PT.pair (PT.comp PT.half (PT.comp PT.fst PT.snd))
      (PT.pair (PT.ite hc (PT.comp (g := fun n : ℕ => 2 * n) PT.double hq)
        (PT.comp (g := fun n : ℕ => 2 * n + 1) PT.doubleSucc hq))
        (PT.comp PT.half (PT.comp PT.snd (PT.comp PT.snd PT.snd)))))

theorem divStep_bound (r d q c i : ℕ) :
    (divStep^[i] (r, d, q, c)).1 ≤ r ∧ (divStep^[i] (r, d, q, c)).2.1 ≤ d ∧
      (divStep^[i] (r, d, q, c)).2.2.1 + 1 ≤ (q + 1) * 2 ^ i ∧
      (divStep^[i] (r, d, q, c)).2.2.2 ≤ c := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    generalize divStep^[i] (r, d, q, c) = s at ih
    obtain ⟨r', d', q', c'⟩ := s
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only at h1 h2 h3 h4
    have e : (q + 1) * 2 ^ (i + 1) = 2 * ((q + 1) * 2 ^ i) := by ring
    simp only [divStep, e]
    refine ⟨?_, ?_, ?_, ?_⟩
    · split <;> omega
    · omega
    · split <;> omega
    · omega

theorem divLoop_polyTime (hsub : IsPolyTime (fun p : ℕ × ℕ => p.1 - p.2))
    (hlt : IsPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))) :
    IsPolyTime (fun s : ℕ × ℕ × ℕ × ℕ => divStep^[Nat.size s.2.2.2] s) := by
  refine counterLoop divStep (fun s => s.2.2.2) (divStep_polyTime hsub hlt)
    (PT.comp PT.snd (PT.comp PT.snd PT.snd))
    (fun _ => rfl) (Polynomial.C 5 * Polynomial.X + Polynomial.C 5) ?_ ?_
  · rintro ⟨r, d, q, c⟩
    simp only [len_pair, len_nat]
    omega
  · rintro ⟨r, d, q, c⟩ i hi
    obtain ⟨h1, h2, h3, h4⟩ := divStep_bound r d q c i
    generalize divStep^[i] (r, d, q, c) = s at h1 h2 h3 h4
    obtain ⟨r', d', q', c'⟩ := s
    simp only at h1 h2 h3 h4 hi
    simp only [len_pair, len_nat, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    have g1 := Nat.size_le_size h1
    have g2 := Nat.size_le_size h2
    have g4 := Nat.size_le_size h4
    have g3 : Nat.size q' ≤ Nat.size q + i := by
      rw [Nat.size_le, pow_add]
      have e1 : q + 1 ≤ 2 ^ Nat.size q := Nat.lt_size_self q
      have e2 : (q + 1) * 2 ^ i ≤ 2 ^ Nat.size q * 2 ^ i := Nat.mul_le_mul_right _ e1
      omega
    omega

/-- Correctness of the division loop: started with the divisor shifted up by j places and a
  remainder below twice that, j + 1 rounds leave a remainder below the divisor and preserve
  quotient times divisor plus remainder. -/
theorem divStep_run (b : ℕ) : ∀ j r q c : ℕ, r < b * 2 ^ (j + 1) →
    (divStep^[j + 1] (r, b * 2 ^ j, q, c)).1 < b ∧
      q * (b * 2 ^ (j + 1)) + r =
        (divStep^[j + 1] (r, b * 2 ^ j, q, c)).2.2.1 * b + (divStep^[j + 1] (r, b * 2 ^ j, q, c)).1 := by
  intro j
  induction j with
  | zero =>
    intro r q c hr
    simp only [zero_add, pow_one, pow_zero, mul_one, Function.iterate_one] at hr ⊢
    by_cases h : r < b
    · have e : divStep (r, b, q, c) = (r, b / 2, 2 * q, c / 2) := by simp [divStep, h]
      rw [e]
      exact ⟨h, by ring⟩
    · have e : divStep (r, b, q, c) = (r - b, b / 2, 2 * q + 1, c / 2) := by simp [divStep, h]
      rw [e]
      have e3 : (2 * q + 1) * b = q * (b * 2) + b := by ring
      simp only [e3]
      constructor <;> omega
  | succ j ih =>
    intro r q c hr
    rw [Function.iterate_succ_apply]
    have hd : b * 2 ^ (j + 1) / 2 = b * 2 ^ j := by
      rw [pow_succ, ← mul_assoc]
      exact Nat.mul_div_cancel _ (by norm_num)
    have e2 : b * 2 ^ (j + 1 + 1) = 2 * (b * 2 ^ (j + 1)) := by ring
    by_cases h : r < b * 2 ^ (j + 1)
    · have e : divStep (r, b * 2 ^ (j + 1), q, c) = (r, b * 2 ^ j, 2 * q, c / 2) := by
        simp [divStep, h, hd]
      rw [e]
      obtain ⟨h1, h2⟩ := ih r (2 * q) (c / 2) h
      refine ⟨h1, ?_⟩
      rw [← h2]
      ring
    · have e : divStep (r, b * 2 ^ (j + 1), q, c) =
          (r - b * 2 ^ (j + 1), b * 2 ^ j, 2 * q + 1, c / 2) := by
        simp [divStep, h, hd]
      rw [e]
      obtain ⟨h1, h2⟩ := ih (r - b * 2 ^ (j + 1)) (2 * q + 1) (c / 2) (by omega)
      refine ⟨h1, ?_⟩
      rw [← h2]
      have e3 : (2 * q + 1) * (b * 2 ^ (j + 1)) = q * (2 * (b * 2 ^ (j + 1))) + b * 2 ^ (j + 1) := by
        ring
      rw [e2, e3]
      omega

/-- The start state of the division loop. -/
def divInit (p : ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (p.1, p.2 * 2 ^ Nat.size p.1, 0, 1 * 2 ^ Nat.size p.1)

theorem divInit_polyTime (hadd : IsPolyTime (fun p : ℕ × ℕ => p.1 + p.2)) : IsPolyTime divInit :=
  PT.pair PT.fst (PT.pair (shiftUp_polyTime hadd)
    (PT.pair (PT.const 0) (PT.comp (g := fun p : ℕ × ℕ => p.2 * 2 ^ Nat.size p.1)
      (shiftUp_polyTime hadd) (PT.pair PT.fst (PT.const 1)))))

theorem divLoop_val (a b : ℕ) (hb : 0 < b) :
    (divStep^[Nat.size (divInit (a, b)).2.2.2] (divInit (a, b))).2.2.1 = a / b ∧
      (divStep^[Nat.size (divInit (a, b)).2.2.2] (divInit (a, b))).1 = a % b := by
  have hsz : Nat.size (divInit (a, b)).2.2.2 = Nat.size a + 1 := by
    simp only [divInit, one_mul]
    exact Nat.size_pow
  rw [hsz]
  have hr : a < b * 2 ^ (Nat.size a + 1) := by
    have e1 : a < 2 ^ Nat.size a := Nat.lt_size_self a
    have e2 : 2 ^ Nat.size a ≤ b * 2 ^ Nat.size a := Nat.le_mul_of_pos_left _ hb
    have e3 : b * 2 ^ (Nat.size a + 1) = 2 * (b * 2 ^ Nat.size a) := by ring
    omega
  obtain ⟨h1, h2⟩ := divStep_run b (Nat.size a) a 0 (1 * 2 ^ Nat.size a) hr
  simp only [divInit]
  generalize divStep^[Nat.size a + 1] (a, b * 2 ^ Nat.size a, 0, 1 * 2 ^ Nat.size a) = s
    at h1 h2 ⊢
  rw [zero_mul, zero_add] at h2
  have hc := Nat.mul_comm b s.2.2.1
  have key := (Nat.div_mod_unique hb).2 ⟨(by omega : s.1 + b * s.2.2.1 = a), h1⟩
  exact ⟨key.1.symm, key.2.symm⟩

theorem divMod_polyTime (hadd : IsPolyTime (fun p : ℕ × ℕ => p.1 + p.2))
    (hsub : IsPolyTime (fun p : ℕ × ℕ => p.1 - p.2))
    (hlt : IsPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))) :
    IsPolyTime (fun p : ℕ × ℕ => p.1 / p.2) ∧ IsPolyTime (fun p : ℕ × ℕ => p.1 % p.2) := by
  have hrun : IsPolyTime (fun p : ℕ × ℕ => divStep^[Nat.size (divInit p).2.2.2] (divInit p)) :=
    PT.comp (divLoop_polyTime hsub hlt) (divInit_polyTime hadd)
  have hz : IsPolyTime (fun p : ℕ × ℕ => decide (p.2 = 0)) := PT.comp PT.isZero PT.snd
  have hq := PT.ite hz (PT.const 0) (PT.comp (PT.comp PT.fst (PT.comp PT.snd PT.snd)) hrun)
  have hr := PT.ite hz PT.fst (PT.comp PT.fst hrun)
  have eq : (fun p : ℕ × ℕ => p.1 / p.2) = (fun p : ℕ × ℕ => if decide (p.2 = 0) then 0 else
      (divStep^[Nat.size (divInit p).2.2.2] (divInit p)).2.2.1) := by
    funext p
    obtain ⟨a, b⟩ := p
    by_cases hb : b = 0
    · simp [hb]
    · simp only [hb, decide_false, Bool.false_eq_true, if_false]
      exact (divLoop_val a b (Nat.pos_of_ne_zero hb)).1.symm
  have er : (fun p : ℕ × ℕ => p.1 % p.2) = (fun p : ℕ × ℕ => if decide (p.2 = 0) then p.1 else
      (divStep^[Nat.size (divInit p).2.2.2] (divInit p)).1) := by
    funext p
    obtain ⟨a, b⟩ := p
    by_cases hb : b = 0
    · simp [hb]
    · simp only [hb, decide_false, Bool.false_eq_true, if_false]
      exact (divLoop_val a b (Nat.pos_of_ne_zero hb)).2.symm
  rw [eq, er]
  exact ⟨hq, hr⟩

end Erdos78Arith2
end

-- ===== part: Defs =====
section
namespace Erdos78Avoid
open Filter ComplexityTheory Erdos78

/-- side length A of the seed table: moduli 1..A are used. -/
def side (k : ℕ) : ℕ := 48 * k ^ 2 + 2
/-- seed length in bits. -/
def L (k : ℕ) : ℕ := side k ^ 3
/-- number of pairs in a set of 12k vertices. -/
def t (k : ℕ) : ℕ := (12 * k).choose 2
/-- position in the seed of the table entry (q, a, b). -/
def idx (k q a b : ℕ) : ℕ := (q - 1) * side k ^ 2 + a * side k + b
/-- the bit that seed s assigns to the pair (u, v): parity of the table entries
(q, u mod q, v mod q) over all moduli q = 1..A. -/
def ebit (k s u v : ℕ) : Bool :=
  decide (Odd ((Finset.Icc 1 (side k)).filter
    (fun q => s.testBit (idx k q (u % q) (v % q)) = true)).card)
/-- the decoder: (seed, N, u, v) to the adjacency bit, where N = 2^k. -/
def dec0 : ℕ × ℕ × ℕ × ℕ → Bool := fun x =>
  decide (x.2.2.1 < x.2.2.2) && ebit (Nat.log2 x.2.1) x.1 x.2.2.1 x.2.2.2
/-- q isolates the pair (u, v) inside S. -/
def isol (S : Finset ℕ) (u v q : ℕ) : Prop :=
  ∀ u' ∈ S, ∀ v' ∈ S, u' < v' → u' % q = u % q → v' % q = v % q → u' = u ∧ v' = v
open Classical in
/-- least isolating modulus in 1..A (1 if none). -/
noncomputable def modOf (k : ℕ) (S : Finset ℕ) (u v : ℕ) : ℕ :=
  if h : ∃ q, 1 ≤ q ∧ q ≤ side k ∧ isol S u v q then Nat.find h else 1
/-- private seed position of the pair (u, v). -/
noncomputable def priv (k : ℕ) (S : Finset ℕ) (u v : ℕ) : ℕ :=
  idx k (modOf k S u v) (u % modOf k S u v) (v % modOf k S u v)
/-- ordered pairs of S. -/
def pairs (S : Finset ℕ) : Finset (ℕ × ℕ) := (S ×ˢ S).filter (fun e => e.1 < e.2)
/-- all private positions. -/
noncomputable def privSet (k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (pairs S).image (fun e => priv k S e.1 e.2)
open Classical in
/-- seed bit i with all private bits cleared; the other bits are read off R in order. -/
noncomputable def sbit0 (k : ℕ) (S : Finset ℕ) (R i : ℕ) : Bool :=
  if i ∈ privSet k S then false
  else R.testBit ((Finset.range i).filter (fun j => j ∉ privSet k S)).card
noncomputable def seed0 (k : ℕ) (S : Finset ℕ) (R : ℕ) : ℕ :=
  Nat.ofBits (fun i : Fin (L k) => sbit0 k S R i)
open Classical in
/-- final seed bit i: private bits are set so that every pair of S gets the bit b. -/
noncomputable def sbit (k : ℕ) (S : Finset ℕ) (b : Bool) (R i : ℕ) : Bool :=
  if i ∈ privSet k S then
    decide (∃ e ∈ pairs S, priv k S e.1 e.2 = i ∧ xor b (ebit k (seed0 k S R) e.1 e.2) = true)
  else R.testBit ((Finset.range i).filter (fun j => j ∉ privSet k S)).card
/-- the compression map: (N, x) with N = 2^k; x = R + 2^(L-t) * (b + 2 * code), where code lists
the vertices of S in base 2^k. -/
noncomputable def cmp0 : ℕ × ℕ → ℕ := fun y =>
  Nat.ofBits (fun i : Fin (L (Nat.log2 y.1)) =>
    sbit (Nat.log2 y.1)
      (Nat.digits (2 ^ Nat.log2 y.1)
        (y.2 / 2 ^ (L (Nat.log2 y.1) - t (Nat.log2 y.1)) / 2)).toFinset
      ((y.2 / 2 ^ (L (Nat.log2 y.1) - t (Nat.log2 y.1))).testBit 0)
      (y.2 % 2 ^ (L (Nat.log2 y.1) - t (Nat.log2 y.1))) i)

end Erdos78Avoid
end

-- ===== part: Dec =====
section
/-! The decoder dec0 is polynomial-time computable: a parity loop over the moduli q = 1..A. -/

open ComplexityTheory BitstringEncoding

namespace Erdos78Dec

/-- loop state: the untouched input (s, N, u, v), the current modulus q, the parity so far. -/
abbrev St : Type := (ℕ × ℕ × ℕ × ℕ) × ℕ × Bool

/-- side length, recomputed from the input N. -/
def sideOf (a : St) : ℕ := Erdos78Avoid.side (Nat.log2 a.1.2.1)

/-- table position read in the current round. -/
def idxOf (a : St) : ℕ :=
  Erdos78Avoid.idx (Nat.log2 a.1.2.1) a.2.1 (a.1.2.2.1 % a.2.1) (a.1.2.2.2 % a.2.1)

/-- table bit read in the current round. -/
def bitOf (a : St) : Bool := a.1.1.testBit (idxOf a)

/-- the loop continues while q is at most the side length. -/
def cond (a : St) : Bool := decide (a.2.1 < sideOf a + 1)

/-- one round: flip the parity if the table bit is set, and move to the next modulus. -/
def step (a : St) : St :=
  (a.1, a.2.1 + 1, if bitOf a then (if a.2.2 then false else true) else a.2.2)

/-- the result of the loop. -/
def G (a : St) : St := step^[sideOf a + 1 - a.2.1] a

/- Closure helpers -/

section helpers

variable {α : Type} [BitstringEncoding α]

lemma add2 (hA : PT.ArithFacts) {f g : α → ℕ} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => f a + g a) := by
  have h := PT.comp hA.add (PT.pair hf hg)
  exact h

lemma sub2 (hA : PT.ArithFacts) {f g : α → ℕ} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => f a - g a) := by
  have h := PT.comp hA.sub (PT.pair hf hg)
  exact h

lemma mul2 (hA : PT.ArithFacts) {f g : α → ℕ} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => f a * g a) := by
  have h := PT.comp hA.mul (PT.pair hf hg)
  exact h

lemma mod2 (hA : PT.ArithFacts) {f g : α → ℕ} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => f a % g a) := by
  have h := PT.comp hA.mod (PT.pair hf hg)
  exact h

lemma lt2 (hA : PT.ArithFacts) {f g : α → ℕ} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => decide (f a < g a)) := by
  have h := PT.comp hA.lt (PT.pair hf hg)
  exact h

lemma testBit2 (hA : PT.ArithFacts) {f g : α → ℕ} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => (f a).testBit (g a)) := by
  have h := PT.comp hA.testBit (PT.pair hf hg)
  exact h

lemma log2' (hA : PT.ArithFacts) {f : α → ℕ} (hf : IsPolyTime f) :
    IsPolyTime (fun a => Nat.log2 (f a)) := by
  have h := PT.comp hA.log2 hf
  exact h

end helpers

/- The pieces of the loop are polynomial-time -/

lemma st_x : IsPolyTime (fun a : St => a.1) := PT.fst
lemma st_q : IsPolyTime (fun a : St => a.2.1) := PT.comp PT.fst PT.snd
lemma st_acc : IsPolyTime (fun a : St => a.2.2) := PT.comp PT.snd PT.snd
lemma st_s : IsPolyTime (fun a : St => a.1.1) := PT.comp PT.fst PT.fst
lemma st_N : IsPolyTime (fun a : St => a.1.2.1) := PT.comp PT.fst (PT.comp PT.snd PT.fst)
lemma st_u : IsPolyTime (fun a : St => a.1.2.2.1) :=
  PT.comp PT.fst (PT.comp PT.snd (PT.comp PT.snd PT.fst))
lemma st_v : IsPolyTime (fun a : St => a.1.2.2.2) :=
  PT.comp PT.snd (PT.comp PT.snd (PT.comp PT.snd PT.fst))

lemma sideOf_eq (a : St) :
    sideOf a = 48 * (Nat.log2 a.1.2.1 * Nat.log2 a.1.2.1) + 2 := by
  simp [sideOf, Erdos78Avoid.side, pow_two]

lemma sideOf_polyTime (hA : PT.ArithFacts) : IsPolyTime sideOf := by
  have h : IsPolyTime (fun a : St => 48 * (Nat.log2 a.1.2.1 * Nat.log2 a.1.2.1) + 2) :=
    add2 hA (mul2 hA (PT.const 48) (mul2 hA (log2' hA st_N) (log2' hA st_N))) (PT.const 2)
  have e : sideOf = fun a : St => 48 * (Nat.log2 a.1.2.1 * Nat.log2 a.1.2.1) + 2 :=
    funext sideOf_eq
  rw [e]
  exact h

lemma idxOf_eq (a : St) :
    idxOf a = (a.2.1 - 1) * (sideOf a * sideOf a) + (a.1.2.2.1 % a.2.1) * sideOf a
      + a.1.2.2.2 % a.2.1 := by
  simp [idxOf, Erdos78Avoid.idx, sideOf, pow_two]

lemma idxOf_polyTime (hA : PT.ArithFacts) : IsPolyTime idxOf := by
  have hs := sideOf_polyTime hA
  have h : IsPolyTime (fun a : St =>
      (a.2.1 - 1) * (sideOf a * sideOf a) + (a.1.2.2.1 % a.2.1) * sideOf a
        + a.1.2.2.2 % a.2.1) :=
    add2 hA
      (add2 hA (mul2 hA (sub2 hA st_q (PT.const 1)) (mul2 hA hs hs))
        (mul2 hA (mod2 hA st_u st_q) hs))
      (mod2 hA st_v st_q)
  have e : idxOf = fun a : St =>
      (a.2.1 - 1) * (sideOf a * sideOf a) + (a.1.2.2.1 % a.2.1) * sideOf a
        + a.1.2.2.2 % a.2.1 := funext idxOf_eq
  rw [e]
  exact h

lemma bitOf_polyTime (hA : PT.ArithFacts) : IsPolyTime bitOf := by
  have h : IsPolyTime (fun a : St => a.1.1.testBit (idxOf a)) :=
    testBit2 hA st_s (idxOf_polyTime hA)
  exact h

lemma cond_polyTime (hA : PT.ArithFacts) : IsPolyTime cond := by
  have h : IsPolyTime (fun a : St => decide (a.2.1 < sideOf a + 1)) :=
    lt2 hA st_q (add2 hA (sideOf_polyTime hA) (PT.const 1))
  exact h

lemma step_polyTime (hA : PT.ArithFacts) : IsPolyTime step := by
  have hflip : IsPolyTime (fun a : St => if a.2.2 then false else true) :=
    PT.ite st_acc (PT.const false) (PT.const true)
  have hacc : IsPolyTime
      (fun a : St => if bitOf a then (if a.2.2 then false else true) else a.2.2) :=
    PT.ite (bitOf_polyTime hA) hflip st_acc
  have hq : IsPolyTime (fun a : St => a.2.1 + 1) := add2 hA st_q (PT.const 1)
  have h : IsPolyTime (fun a : St =>
      (a.1, a.2.1 + 1, if bitOf a then (if a.2.2 then false else true) else a.2.2)) :=
    PT.pair st_x (PT.pair hq hacc)
  exact h

/- Encoding sizes -/

lemma len_nat (n : ℕ) : (bitEncode n).length = Nat.size n := by
  show (Computability.encodeNat n).length = Nat.size n
  rw [Erdos78Prim2.encodeNat_eq_bits, Nat.size_eq_bits_len]

lemma len_bool (b : Bool) : (bitEncode b).length = 1 := rfl

lemma len_pair {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (p : α × β) :
    (bitEncode p).length = 2 * (bitEncode p.1).length + 1 + (bitEncode p.2).length := by
  show (delimit (bitEncode p.1) ++ bitEncode p.2).length = _
  rw [List.length_append, length_delimit]

lemma len_St (a : St) :
    (bitEncode a).length = 2 * (bitEncode a.1).length + 2 * Nat.size a.2.1 + 3 := by
  rw [len_pair a, len_pair a.2, len_nat, len_bool]
  omega

lemma sizeN_le (a : St) : Nat.size a.1.2.1 ≤ (bitEncode a.1).length := by
  rw [len_pair a.1, len_pair a.1.2, len_nat a.1.2.1]
  omega

lemma log2_le_size (n : ℕ) : Nat.log2 n ≤ Nat.size n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · exact ((Nat.log2_lt (by omega)).2 (Nat.lt_size_self n)).le

lemma size_le_self (n : ℕ) : Nat.size n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self

lemma log2_le_len (a : St) : Nat.log2 a.1.2.1 ≤ (bitEncode a).length := by
  have h1 := log2_le_size a.1.2.1
  have h2 := sizeN_le a
  have h3 := len_St a
  omega

lemma sideOf_le (a : St) :
    sideOf a ≤ 48 * ((bitEncode a).length * (bitEncode a).length) + 2 := by
  rw [sideOf_eq]
  have h := log2_le_len a
  have h2 := Nat.mul_le_mul h h
  omega

/- The loop -/

lemma iter_fst (a : St) (i : ℕ) : (step^[i] a).1 = a.1 ∧ (step^[i] a).2.1 = a.2.1 + i := by
  induction i with
  | zero => exact ⟨rfl, rfl⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨ih.1, ?_⟩
    show (step^[i] a).2.1 + 1 = a.2.1 + (i + 1)
    rw [ih.2]
    omega

lemma sideOf_iter (a : St) (i : ℕ) : sideOf (step^[i] a) = sideOf a := by
  unfold sideOf
  rw [(iter_fst a i).1]

lemma cond_iter (a : St) (i : ℕ) :
    cond (step^[i] a) = decide (a.2.1 + i < sideOf a + 1) := by
  unfold cond
  rw [sideOf_iter, (iter_fst a i).2]

lemma G_polyTime (hA : PT.ArithFacts) : IsPolyTime G := by
  refine PT.loop cond step (cond_polyTime hA) (step_polyTime hA)
    (Polynomial.C 48 * Polynomial.X ^ 2 + Polynomial.C 3)
    (Polynomial.X + Polynomial.C 96 * Polynomial.X ^ 2 + Polynomial.C 6) G ?_
  intro a
  have hside := sideOf_le a
  refine ⟨sideOf a + 1 - a.2.1, ?_, ?_, ?_, ?_, rfl⟩
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, pow_two]
    omega
  · intro i hi
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, pow_two]
    have h1 := len_St (step^[i] a)
    rw [(iter_fst a i).1, (iter_fst a i).2] at h1
    have h2 := len_St a
    rw [h1]
    by_cases hq : a.2.1 ≤ sideOf a + 1
    · have h3 : Nat.size (a.2.1 + i) ≤ sideOf a + 1 :=
        (Nat.size_le_size (by omega)).trans (size_le_self _)
      omega
    · have hi0 : i = 0 := by omega
      subst hi0
      simp only [Nat.add_zero]
      omega
  · intro i hi
    rw [cond_iter]
    exact decide_eq_true (by omega)
  · rw [cond_iter]
    exact decide_eq_false (by omega)

/- Correctness of the loop -/

lemma parity_succ (P : ℕ → Bool) (j : ℕ) :
    decide (Odd ((Finset.Icc 1 (j + 1)).filter (fun q => P q = true)).card) =
      (if P (j + 1) then
        (if decide (Odd ((Finset.Icc 1 j).filter (fun q => P q = true)).card) then false
          else true)
       else decide (Odd ((Finset.Icc 1 j).filter (fun q => P q = true)).card)) := by
  have hI : Finset.Icc 1 (j + 1) = insert (j + 1) (Finset.Icc 1 j) := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hn : j + 1 ∉ (Finset.Icc 1 j).filter (fun q => P q = true) := by
    simp
  rw [hI, Finset.filter_insert]
  by_cases hp : P (j + 1) = true
  · rw [if_pos hp, Finset.card_insert_of_notMem hn, if_pos hp]
    by_cases ho : Odd ((Finset.Icc 1 j).filter (fun q => P q = true)).card
    · simp [ho, Nat.odd_add_one]
    · simp [ho, Nat.odd_add_one]
  · rw [if_neg hp, if_neg hp]

lemma iter_parity (x : ℕ × ℕ × ℕ × ℕ) (j : ℕ) :
    step^[j] ((x, 1, false) : St) =
      (x, j + 1, decide (Odd ((Finset.Icc 1 j).filter
        (fun q => x.1.testBit
          (Erdos78Avoid.idx (Nat.log2 x.2.1) q (x.2.2.1 % q) (x.2.2.2 % q)) = true)).card)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [parity_succ (fun q => x.1.testBit
      (Erdos78Avoid.idx (Nat.log2 x.2.1) q (x.2.2.1 % q) (x.2.2.2 % q))) j]
    rfl

lemma G_init (x : ℕ × ℕ × ℕ × ℕ) :
    (G ((x, 1, false) : St)).2.2 = Erdos78Avoid.ebit (Nat.log2 x.2.1) x.1 x.2.2.1 x.2.2.2 := by
  unfold G
  rw [iter_parity]
  show _ = Erdos78Avoid.ebit (Nat.log2 x.2.1) x.1 x.2.2.1 x.2.2.2
  unfold Erdos78Avoid.ebit
  simp [sideOf]

/-- The decoder is polynomial-time computable (given the binary arithmetic facts). -/
theorem dec0_polyTime (hA : PT.ArithFacts) : IsPolyTime Erdos78Avoid.dec0 := by
  have hinit : IsPolyTime (fun x : ℕ × ℕ × ℕ × ℕ => ((x, 1, false) : St)) :=
    PT.pair PT.id' (PT.const (1, false))
  have hGi : IsPolyTime (fun x : ℕ × ℕ × ℕ × ℕ => G ((x, 1, false) : St)) :=
    PT.comp (G_polyTime hA) hinit
  have hres : IsPolyTime (fun x : ℕ × ℕ × ℕ × ℕ => (G ((x, 1, false) : St)).2.2) :=
    PT.comp (g := fun a : St => a.2.2) st_acc hGi
  have hu : IsPolyTime (fun x : ℕ × ℕ × ℕ × ℕ => x.2.2.1) :=
    PT.comp PT.fst (PT.comp PT.snd PT.snd)
  have hv : IsPolyTime (fun x : ℕ × ℕ × ℕ × ℕ => x.2.2.2) :=
    PT.comp PT.snd (PT.comp PT.snd PT.snd)
  have hlt : IsPolyTime (fun x : ℕ × ℕ × ℕ × ℕ => decide (x.2.2.1 < x.2.2.2)) :=
    lt2 hA hu hv
  have h := PT.ite hlt hres (PT.const false)
  have e : Erdos78Avoid.dec0 = fun x : ℕ × ℕ × ℕ × ℕ =>
      if decide (x.2.2.1 < x.2.2.2) = true then (G ((x, 1, false) : St)).2.2 else false := by
    funext x
    rw [G_init]
    unfold Erdos78Avoid.dec0
    by_cases hc : x.2.2.1 < x.2.2.2 <;> simp [hc]
  rw [e]
  exact h

end Erdos78Dec
end

-- ===== part: Arith =====
section
/-! Binary arithmetic is polynomial time (all fields of PT.ArithFacts), and the decoder with it. -/
open ComplexityTheory

namespace Erdos78Arith

theorem arithFacts : PT.ArithFacts where
  add := Erdos78Arith1.add_polyTime
  sub := Erdos78Arith1.sub_polyTime
  mul := Erdos78Arith2.mul_polyTime Erdos78Arith1.add_polyTime
  div := (Erdos78Arith2.divMod_polyTime Erdos78Arith1.add_polyTime Erdos78Arith1.sub_polyTime
    Erdos78Arith1.lt_polyTime).1
  mod := (Erdos78Arith2.divMod_polyTime Erdos78Arith1.add_polyTime Erdos78Arith1.sub_polyTime
    Erdos78Arith1.lt_polyTime).2
  lt := Erdos78Arith1.lt_polyTime
  eq := Erdos78Arith1.eq_polyTime
  log2 := Erdos78Arith1.log2_polyTime
  testBit := Erdos78Arith1.testBit_polyTime
  shiftRight := Erdos78Arith1.shiftRight_polyTime
  lowBits := Erdos78Arith1.lowBits_polyTime

/-- The decoder of the seeded graph family is polynomial time, with no hypotheses. -/
theorem dec0_polyTime : IsPolyTime Erdos78Avoid.dec0 := Erdos78Dec.dec0_polyTime arithFacts

end Erdos78Arith
end

-- ===== part: CmpA =====
section
-- Loop combinators (bounded for-loops over natural numbers) and their polynomial-time closure
-- lemmas, built on the toolkit.

open ComplexityTheory

namespace Erdos78Cmp

variable {α β γ δ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
  [BitstringEncoding δ]

/-- encoding length. -/
def sz (a : α) : ℕ := (BitstringEncoding.bitEncode a).length

lemma sz_pair (a : α) (b : β) : sz (a, b) = 2 * sz a + 1 + sz b := by
  show (BitstringEncoding.delimit (BitstringEncoding.bitEncode a) ++
    BitstringEncoding.bitEncode b).length = _
  simp [sz, BitstringEncoding.length_delimit]

lemma sz_nat (n : ℕ) : sz n = Nat.size n := by
  show (Computability.encodeNat n).length = _
  rw [Erdos78Prim2.encodeNat_eq_bits, Nat.size_eq_bits_len]

lemma sz_bool (b : Bool) : sz b = 1 := rfl

lemma sz_fst_le (c : α × β) : sz c.1 ≤ sz c := by
  obtain ⟨a, b⟩ := c
  rw [sz_pair]; show sz a ≤ _; omega

lemma sz_snd_le (c : α × β) : sz c.2 ≤ sz c := by
  obtain ⟨a, b⟩ := c
  rw [sz_pair]; show sz b ≤ _; omega

lemma size_le_self (n : ℕ) : Nat.size n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self

lemma size_succ_le (n : ℕ) : Nat.size (n + 1) ≤ Nat.size n + 1 := by
  rw [Nat.size_le, pow_succ]
  have := Nat.lt_size_self n
  omega

lemma size_double_le (n : ℕ) : Nat.size (2 * n) ≤ Nat.size n + 1 := by
  rw [Nat.size_le, pow_succ]
  have := Nat.lt_size_self n
  omega

lemma size_double_succ_le (n : ℕ) : Nat.size (2 * n + 1) ≤ Nat.size n + 1 := by
  rw [Nat.size_le, pow_succ]
  have := Nat.lt_size_self n
  omega

lemma log2_le_size (n : ℕ) : Nat.log2 n ≤ Nat.size n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact le_of_lt ((Nat.log2_lt (by omega)).2 (Nat.lt_size_self n))

/-- polynomially bounded value. -/
def PBdd (f : α → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ c, f c ≤ p.eval (sz c)

lemma PBdd.const (m : ℕ) : PBdd (fun _ : α => m) := ⟨Polynomial.C m, fun c => by simp⟩

lemma PBdd.sz_le {f : α → ℕ} (h : ∀ c, f c ≤ sz c) : PBdd f :=
  ⟨Polynomial.X, fun c => by simpa using h c⟩

lemma PBdd.mono {f g : α → ℕ} (hg : PBdd g) (h : ∀ c, f c ≤ g c) : PBdd f := by
  obtain ⟨p, hp⟩ := hg
  exact ⟨p, fun c => le_trans (h c) (hp c)⟩

lemma PBdd.add {f g : α → ℕ} (hf : PBdd f) (hg : PBdd g) : PBdd (fun c => f c + g c) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun c => by rw [Polynomial.eval_add]; exact Nat.add_le_add (hp c) (hq c)⟩

lemma PBdd.mul {f g : α → ℕ} (hf : PBdd f) (hg : PBdd g) : PBdd (fun c => f c * g c) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun c => by rw [Polynomial.eval_mul]; exact Nat.mul_le_mul (hp c) (hq c)⟩

lemma PBdd.comp {f : α → ℕ} (hf : PBdd f) (g : β → α) (hg : ∀ c, sz (g c) ≤ sz c) :
    PBdd (fun c => f (g c)) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, fun c => le_trans (hp (g c)) (Erdos78While.eval_mono p (hg c))⟩

/-- bounded for-loop: fold of f over the indices 0, .., n-1. -/
def forN {β : Type} (f : ℕ → β → β) (a : β) : ℕ → β
  | 0 => a
  | n + 1 => f n (forN f a n)

-- derived toolkit: binary operations

section ops
variable {f g : α → ℕ} {b c : α → Bool}

theorem fst' {f : α → β × γ} (hf : IsPolyTime f) : IsPolyTime (fun a => (f a).1) :=
  PT.comp PT.fst hf
theorem snd' {f : α → β × γ} (hf : IsPolyTime f) : IsPolyTime (fun a => (f a).2) :=
  PT.comp PT.snd hf

theorem add2 (hA : PT.ArithFacts) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => f a + g a) := PT.comp hA.add (PT.pair hf hg)
theorem sub2 (hA : PT.ArithFacts) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => f a - g a) := PT.comp hA.sub (PT.pair hf hg)
theorem mul2 (hA : PT.ArithFacts) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => f a * g a) := PT.comp hA.mul (PT.pair hf hg)
theorem div2 (hA : PT.ArithFacts) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => f a / g a) := PT.comp hA.div (PT.pair hf hg)
theorem mod2 (hA : PT.ArithFacts) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => f a % g a) := PT.comp hA.mod (PT.pair hf hg)
theorem lt2 (hA : PT.ArithFacts) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => decide (f a < g a)) := PT.comp hA.lt (PT.pair hf hg)
theorem eq2 (hA : PT.ArithFacts) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => decide (f a = g a)) := PT.comp hA.eq (PT.pair hf hg)
theorem tb2 (hA : PT.ArithFacts) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => (f a).testBit (g a)) :=
  PT.comp (g := fun p : ℕ × ℕ => p.1.testBit p.2) hA.testBit (PT.pair hf hg)
theorem shr2 (hA : PT.ArithFacts) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => f a / 2 ^ g a) := PT.comp hA.shiftRight (PT.pair hf hg)
theorem low2 (hA : PT.ArithFacts) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun a => f a % 2 ^ g a) := PT.comp hA.lowBits (PT.pair hf hg)
theorem log2' (hA : PT.ArithFacts) (hf : IsPolyTime f) :
    IsPolyTime (fun a => Nat.log2 (f a)) := PT.comp hA.log2 hf
theorem half' (hf : IsPolyTime f) : IsPolyTime (fun a => f a / 2) := PT.comp PT.half hf

theorem or2 (hb : IsPolyTime b) (hc : IsPolyTime c) : IsPolyTime (fun a => b a || c a) := by
  have h := PT.ite hb (PT.const true) hc
  have e : (fun a => if b a then true else c a) = fun a => b a || c a := by
    funext a; cases b a <;> simp
  rw [← e]; exact h
theorem and2 (hb : IsPolyTime b) (hc : IsPolyTime c) : IsPolyTime (fun a => b a && c a) := by
  have h := PT.ite hb hc (PT.const false)
  have e : (fun a => if b a then c a else false) = fun a => b a && c a := by
    funext a; cases b a <;> simp
  rw [← e]; exact h
theorem not1 (hb : IsPolyTime b) : IsPolyTime (fun a => !b a) := by
  have h := PT.ite hb (PT.const false) (PT.const true)
  have e : (fun a => if b a then false else true) = fun a => !b a := by
    funext a; cases b a <;> simp
  rw [← e]; exact h
theorem xor2 (hb : IsPolyTime b) (hc : IsPolyTime c) : IsPolyTime (fun a => xor (b a) (c a)) := by
  have h := PT.ite hb (not1 hc) hc
  have e : (fun a => if b a then !c a else c a) = fun a => xor (b a) (c a) := by
    funext a; cases b a <;> simp
  rw [← e]; exact h

end ops

-- the for-loop closure lemma

theorem forLoop_pt (hA : PT.ArithFacts) (n : γ → ℕ) (init : γ → β) (body : γ × ℕ × β → β)
    (hn : IsPolyTime n) (hi : IsPolyTime init) (hb : IsPolyTime body) (hN : PBdd n)
    (hS : ∃ pS : Polynomial ℕ, ∀ c i a, i < n c → sz (body (c, i, a)) ≤ sz a + pS.eval (sz c)) :
    IsPolyTime (fun c => forN (fun i a => body (c, i, a)) (init c) (n c)) := by
  obtain ⟨pN, hpN⟩ := hN
  obtain ⟨pS, hpS⟩ := hS
  let step : γ × ℕ × β → γ × ℕ × β := fun x => (x.1, x.2.1 + 1, body x)
  let cond : γ × ℕ × β → Bool := fun x => decide (x.2.1 < n x.1)
  have hstep : IsPolyTime step :=
    PT.pair PT.fst (PT.pair (add2 hA (fst' PT.snd) (PT.const 1)) hb)
  have hcond : IsPolyTime cond := lt2 hA (fst' PT.snd) (PT.comp hn PT.fst)
  let G : γ × ℕ × β → γ × ℕ × β := fun x => step^[n x.1 - x.2.1] x
  have hiter : ∀ (c : γ) (i : ℕ) (a : β) (j : ℕ), step^[j] (c, i, a) =
      (c, i + j, forN (fun l acc => body (c, i + l, acc)) a j) := by
    intro c i a j
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih]; rfl
  have hsize : ∀ (c : γ) (i : ℕ) (a : β) (j : ℕ), i + j ≤ n c →
      sz (forN (fun l acc => body (c, i + l, acc)) a j) ≤ sz a + j * pS.eval (sz c) := by
    intro c i a j
    induction j with
    | zero => intro _; simp [forN]
    | succ j ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := hpS c (i + j) (forN (fun l acc => body (c, i + l, acc)) a j) (by omega)
      rw [Nat.succ_mul]
      show sz (body (c, i + j, forN (fun l acc => body (c, i + l, acc)) a j)) ≤ _
      omega
  have hG : IsPolyTime G := by
    refine PT.loop cond step hcond hstep pN
      (Polynomial.C 3 * Polynomial.X + Polynomial.C 2 + Polynomial.C 2 * pN + pN * pS) G ?_
    rintro ⟨c, i, a⟩
    have hsx : sz (c, i, a) = 2 * sz c + 1 + (2 * Nat.size i + 1 + sz a) := by
      rw [sz_pair, sz_pair, sz_nat]
    have hc1 : pN.eval (sz c) ≤ pN.eval (sz (c, i, a)) :=
      Erdos78While.eval_mono pN (by omega)
    have hc2 : pS.eval (sz c) ≤ pS.eval (sz (c, i, a)) :=
      Erdos78While.eval_mono pS (by omega)
    refine ⟨n c - i, ?_, ?_, ?_, ?_, rfl⟩
    · show n c - i ≤ pN.eval (sz (c, i, a))
      have := hpN c
      omega
    · intro j hj
      rw [hiter]
      show sz (c, i + j, forN (fun l acc => body (c, i + l, acc)) a j) ≤
        Polynomial.eval (sz (c, i, a)) _
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      rw [sz_pair, sz_pair, sz_nat]
      have h2 : Nat.size (i + j) ≤ Nat.size i + pN.eval (sz (c, i, a)) := by
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · subst h0; simp
        · exact le_trans (le_trans (size_le_self _)
            (le_trans (by omega) (le_trans (hpN c) hc1))) (Nat.le_add_left _ _)
      have h1 : sz (forN (fun l acc => body (c, i + l, acc)) a j) ≤
          sz a + pN.eval (sz (c, i, a)) * pS.eval (sz (c, i, a)) := by
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · subst h0
          show sz a ≤ _
          omega
        · exact le_trans (hsize c i a j (by omega)) (Nat.add_le_add_left
            (Nat.mul_le_mul (le_trans (by omega) (le_trans (hpN c) hc1)) hc2) _)
      generalize pN.eval (sz (c, i, a)) * pS.eval (sz (c, i, a)) = M at h1 ⊢
      generalize sz (forN (fun l acc => body (c, i + l, acc)) a j) = F at h1 ⊢
      omega
    · intro j hj
      rw [hiter]
      show decide (i + j < n c) = true
      simp only [decide_eq_true_eq]
      omega
    · rw [hiter]
      show decide (i + (n c - i) < n c) = false
      simp only [decide_eq_false_iff_not]
      omega
  have hfin : IsPolyTime (fun c => (G (c, 0, init c)).2.2) :=
    snd' (snd' (PT.comp hG (PT.pair PT.id' (PT.pair (PT.const 0) hi))))
  have e : (fun c => (G (c, 0, init c)).2.2) =
      fun c => forN (fun i a => body (c, i, a)) (init c) (n c) := by
    funext c
    show (step^[n c - 0] (c, 0, init c)).2.2 = _
    rw [hiter]
    simp
  rw [← e]; exact hfin

-- combinators and their specifications

/-- Boolean OR over indices below n. -/
def anyN (n : ℕ) (p : ℕ → Bool) : Bool := forN (fun i acc => acc || p i) false n

lemma anyN_iff (n : ℕ) (p : ℕ → Bool) : anyN n p = true ↔ ∃ i < n, p i = true := by
  induction n with
  | zero => simp [anyN, forN]
  | succ n ih =>
    have h : anyN (n + 1) p = (anyN n p || p n) := rfl
    rw [h, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨i, hi, hpi⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
      · exact Or.inl ⟨i, h', hpi⟩
      · rw [h'] at hpi; exact Or.inr hpi

/-- parity of the number of indices below n satisfying p. -/
def parN (n : ℕ) (p : ℕ → Bool) : Bool := forN (fun i acc => xor acc (p i)) false n

lemma parN_eq (n : ℕ) (p : ℕ → Bool) :
    parN n p = decide (Odd ((Finset.range n).filter (fun i => p i = true)).card) := by
  induction n with
  | zero => simp [parN, forN]
  | succ n ih =>
    have h : parN (n + 1) p = xor (parN n p) (p n) := rfl
    rw [h, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases hp : p n = true
    · rw [if_pos hp, Finset.card_insert_of_notMem (by simp), hp, Bool.xor_true]
      generalize ((Finset.range n).filter (fun i => p i = true)).card = m
      by_cases ho : Odd m
      · have h1 : ¬ Odd (m + 1) := by rw [Nat.odd_add_one]; exact not_not.2 ho
        simp [ho, h1]
      · have h1 : Odd (m + 1) := Nat.odd_add_one.2 ho
        simp [ho, h1]
    · rw [if_neg hp]
      simp [hp]

/-- number of indices below n satisfying p. -/
def countN (n : ℕ) (p : ℕ → Bool) : ℕ := forN (fun i acc => if p i then acc + 1 else acc) 0 n

lemma countN_eq (n : ℕ) (p : ℕ → Bool) :
    countN n p = ((Finset.range n).filter (fun i => p i = true)).card := by
  induction n with
  | zero => simp [countN, forN]
  | succ n ih =>
    have h : countN (n + 1) p = if p n then countN n p + 1 else countN n p := rfl
    rw [h, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases hp : p n = true
    · rw [if_pos hp, if_pos hp, Finset.card_insert_of_notMem (by simp)]
    · rw [if_neg hp, if_neg hp]

/-- least q in 1..n with p q (default d): scan downwards from n. -/
def firstDown (n : ℕ) (p : ℕ → Bool) (d : ℕ) : ℕ :=
  forN (fun j acc => if p (n - j) then n - j else acc) d n

lemma firstDown_aux (n : ℕ) (p : ℕ → Bool) (d : ℕ) (m : ℕ) (hm : m ≤ n) :
    ((∀ q, n - m < q → q ≤ n → p q = false) ∧
      forN (fun j acc => if p (n - j) then n - j else acc) d m = d) ∨
    (n - m < forN (fun j acc => if p (n - j) then n - j else acc) d m ∧
      forN (fun j acc => if p (n - j) then n - j else acc) d m ≤ n ∧
      p (forN (fun j acc => if p (n - j) then n - j else acc) d m) = true ∧
      ∀ q, n - m < q → q < forN (fun j acc => if p (n - j) then n - j else acc) d m →
        p q = false) := by
  induction m with
  | zero =>
    left
    exact ⟨fun q h1 h2 => by omega, rfl⟩
  | succ m ih =>
    have ih' := ih (by omega)
    have hstep : forN (fun j acc => if p (n - j) then n - j else acc) d (m + 1) =
        if p (n - m) then n - m
        else forN (fun j acc => if p (n - j) then n - j else acc) d m := rfl
    rw [hstep]
    generalize forN (fun j acc => if p (n - j) then n - j else acc) d m = r at ih'
    by_cases hp : p (n - m) = true
    · rw [if_pos hp]
      right
      exact ⟨by omega, by omega, hp, fun q h1 h2 => by omega⟩
    · rw [if_neg hp]
      have hp' : p (n - m) = false := by simpa using hp
      rcases ih' with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
      · left
        refine ⟨fun q hq1 hq2 => ?_, h2⟩
        by_cases hq : q = n - m
        · rw [hq]; exact hp'
        · exact h1 q (by omega) hq2
      · right
        refine ⟨by omega, h2, h3, fun q hq1 hq2 => ?_⟩
        by_cases hq : q = n - m
        · rw [hq]; exact hp'
        · exact h4 q (by omega) hq2

lemma firstDown_spec (n : ℕ) (p : ℕ → Bool) (d : ℕ) :
    ((∀ q, 1 ≤ q → q ≤ n → p q = false) ∧ firstDown n p d = d) ∨
    (1 ≤ firstDown n p d ∧ firstDown n p d ≤ n ∧ p (firstDown n p d) = true ∧
      ∀ q, 1 ≤ q → q < firstDown n p d → p q = false) := by
  rcases firstDown_aux n p d n le_rfl with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · left
    exact ⟨fun q hq1 hq2 => h1 q (by omega) hq2, h2⟩
  · right
    exact ⟨by unfold firstDown; omega, h2, h3, fun q hq1 hq2 => h4 q (by omega) hq2⟩

/-- the n-bit number with bits f 0, .., f (n-1). -/
def ofBitsN (n : ℕ) (f : ℕ → Bool) : ℕ := Nat.ofBits (fun i : Fin n => f i)

lemma ofBitsN_congr (n : ℕ) (f g : ℕ → Bool) (h : ∀ i < n, f i = g i) :
    ofBitsN n f = ofBitsN n g := by
  unfold ofBitsN
  congr 1
  funext i
  exact h i i.2

/-- top-down assembly: after m rounds the accumulator holds bits f (n-m), .., f (n-1). -/
def tdN (n : ℕ) (f : ℕ → Bool) (m : ℕ) : ℕ :=
  forN (fun j acc => if f (n - 1 - j) then 2 * acc + 1 else 2 * acc) 0 m

lemma tdN_spec (n : ℕ) (f : ℕ → Bool) (m : ℕ) (hm : m ≤ n) :
    tdN n f m < 2 ^ m ∧ ∀ i < m, (tdN n f m).testBit i = f (n - m + i) := by
  induction m with
  | zero => exact ⟨by simp [tdN, forN], fun i hi => by omega⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hstep : tdN n f (m + 1) =
        if f (n - 1 - m) then 2 * tdN n f m + 1 else 2 * tdN n f m := rfl
    rw [hstep]
    generalize tdN n f m = X at ih1 ih2
    have e0 : n - (m + 1) + 0 = n - 1 - m := by omega
    by_cases hf : f (n - 1 - m) = true
    · rw [if_pos hf]
      refine ⟨by rw [pow_succ]; omega, fun i hi => ?_⟩
      rcases i with _ | i
      · rw [e0, hf, Nat.testBit_zero]
        simp
      · rw [Nat.testBit_succ, show (2 * X + 1) / 2 = X by omega, ih2 i (by omega)]
        congr 1; omega
    · rw [if_neg hf]
      have hf' : f (n - 1 - m) = false := by simpa using hf
      refine ⟨by rw [pow_succ]; omega, fun i hi => ?_⟩
      rcases i with _ | i
      · rw [e0, hf', Nat.testBit_zero]
        simp
      · rw [Nat.testBit_succ, show (2 * X) / 2 = X by omega, ih2 i (by omega)]
        congr 1; omega

lemma ofBitsN_eq (n : ℕ) (f : ℕ → Bool) : ofBitsN n f = tdN n f n := by
  obtain ⟨h1, h2⟩ := tdN_spec n f n le_rfl
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · rw [h2 i hi]
    unfold ofBitsN
    rw [Nat.testBit_ofBits_lt _ _ hi]
    show f i = f (n - n + i)
    rw [Nat.sub_self, Nat.zero_add]
  · have hp : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 hp)]
    unfold ofBitsN
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.ofBits_lt_two_pow _) hp)

-- polynomial-time closure of the combinators

theorem anyN_pt (hA : PT.ArithFacts) (n : γ → ℕ) (p : γ × ℕ → Bool) (hn : IsPolyTime n)
    (hN : PBdd n) (hp : IsPolyTime p) : IsPolyTime (fun c => anyN (n c) (fun i => p (c, i))) :=
  forLoop_pt hA n (fun _ => false) (fun x => x.2.2 || p (x.1, x.2.1)) hn (PT.const false)
    (or2 (snd' PT.snd) (PT.comp hp (PT.pair PT.fst (fst' PT.snd)))) hN
    ⟨0, fun c i a _ => by simp [sz_bool]⟩

theorem parN_pt (hA : PT.ArithFacts) (n : γ → ℕ) (p : γ × ℕ → Bool) (hn : IsPolyTime n)
    (hN : PBdd n) (hp : IsPolyTime p) : IsPolyTime (fun c => parN (n c) (fun i => p (c, i))) :=
  forLoop_pt hA n (fun _ => false) (fun x => xor x.2.2 (p (x.1, x.2.1))) hn (PT.const false)
    (xor2 (snd' PT.snd) (PT.comp hp (PT.pair PT.fst (fst' PT.snd)))) hN
    ⟨0, fun c i a _ => by simp [sz_bool]⟩

theorem countN_pt (hA : PT.ArithFacts) (n : γ → ℕ) (p : γ × ℕ → Bool) (hn : IsPolyTime n)
    (hN : PBdd n) (hp : IsPolyTime p) :
    IsPolyTime (fun c => countN (n c) (fun i => p (c, i))) :=
  forLoop_pt hA n (fun _ => 0)
    (fun x => if p (x.1, x.2.1) then x.2.2 + 1 else x.2.2) hn (PT.const 0)
    (PT.ite (PT.comp hp (PT.pair PT.fst (fst' PT.snd)))
      (add2 hA (snd' PT.snd) (PT.const 1)) (snd' PT.snd)) hN
    ⟨Polynomial.C 1, fun c i a _ => by
      simp only [Polynomial.eval_C]
      split_ifs
      · rw [sz_nat, sz_nat]; exact size_succ_le a
      · omega⟩

theorem firstDown_pt (hA : PT.ArithFacts) (n : γ → ℕ) (p : γ × ℕ → Bool) (d : γ → ℕ)
    (hn : IsPolyTime n) (hN : PBdd n) (hp : IsPolyTime p) (hd : IsPolyTime d) :
    IsPolyTime (fun c => firstDown (n c) (fun q => p (c, q)) (d c)) := by
  obtain ⟨pN, hpN⟩ := hN
  exact forLoop_pt hA n d
    (fun x => if p (x.1, n x.1 - x.2.1) then n x.1 - x.2.1 else x.2.2) hn hd
    (PT.ite (PT.comp hp (PT.pair PT.fst (sub2 hA (PT.comp hn PT.fst) (fst' PT.snd))))
      (sub2 hA (PT.comp hn PT.fst) (fst' PT.snd)) (snd' PT.snd)) ⟨pN, hpN⟩
    ⟨pN, fun c i a _ => by
      split_ifs
      · rw [sz_nat]
        exact le_trans (le_trans (size_le_self _) (le_trans (Nat.sub_le _ _) (hpN c)))
          (Nat.le_add_left _ _)
      · exact Nat.le_add_right _ _⟩

theorem ofBitsN_pt (hA : PT.ArithFacts) (n : γ → ℕ) (f : γ × ℕ → Bool) (hn : IsPolyTime n)
    (hN : PBdd n) (hf : IsPolyTime f) :
    IsPolyTime (fun c => ofBitsN (n c) (fun i => f (c, i))) := by
  have h := forLoop_pt hA n (fun _ => 0)
    (fun x => if f (x.1, n x.1 - 1 - x.2.1) then 2 * x.2.2 + 1 else 2 * x.2.2) hn (PT.const 0)
    (PT.ite (PT.comp hf (PT.pair PT.fst
        (sub2 hA (sub2 hA (PT.comp hn PT.fst) (PT.const 1)) (fst' PT.snd))))
      (PT.comp PT.doubleSucc (snd' PT.snd)) (PT.comp PT.double (snd' PT.snd))) hN
    ⟨Polynomial.C 1, fun c i a _ => by
      simp only [Polynomial.eval_C]
      split_ifs
      · rw [sz_nat, sz_nat]; exact size_double_succ_le a
      · rw [sz_nat, sz_nat]; exact size_double_le a⟩
  have e : (fun c => ofBitsN (n c) (fun i => f (c, i))) = fun c =>
      forN (fun i a => (fun x : γ × ℕ × ℕ =>
        if f (x.1, n x.1 - 1 - x.2.1) then 2 * x.2.2 + 1 else 2 * x.2.2) (c, i, a))
        ((fun _ => 0) c) (n c) := by
    funext c
    rw [ofBitsN_eq]
    rfl
  rw [e]; exact h

end Erdos78Cmp
end

-- ===== part: CmpB =====
section
-- The compression map as a composition of bounded loops, and its equality with the
-- specification Erdos78Avoid.cmp0.

open ComplexityTheory Erdos78Avoid

namespace Erdos78Cmp

/-- the parameter k read off the pair P = (N, code). -/
def kk (P : ℕ × ℕ) : ℕ := Nat.log2 P.1
/-- bound on the number of digit positions. -/
def JJ (P : ℕ × ℕ) : ℕ := Nat.log2 P.2 + 1
/-- digit number j of the code in base 2^k. -/
def dg (P : ℕ × ℕ) (j : ℕ) : ℕ := P.2 / 2 ^ (Nat.log2 P.1 * j) % 2 ^ Nat.log2 P.1
/-- is j a valid digit position. -/
def vd (P : ℕ × ℕ) (j : ℕ) : Bool := !decide (P.2 / 2 ^ (Nat.log2 P.1 * j) = 0)
/-- the set of digits. -/
def SS (P : ℕ × ℕ) : Finset ℕ :=
  ((Finset.range (JJ P)).filter (fun j => vd P j = true)).image (dg P)

/-- existence of a pair of digits satisfying r. -/
def exS2 (P : ℕ × ℕ) (r : ℕ → ℕ → Bool) : Bool :=
  anyN (JJ P) (fun j1 => anyN (JJ P) (fun j2 =>
    vd P j1 && (vd P j2 && r (dg P j1) (dg P j2))))

lemma exS2_iff (P : ℕ × ℕ) (r : ℕ → ℕ → Bool) :
    exS2 P r = true ↔ ∃ u ∈ SS P, ∃ v ∈ SS P, r u v = true := by
  simp only [exS2, anyN_iff, SS, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
    Bool.and_eq_true]
  constructor
  · rintro ⟨j1, h1, j2, h2, hv1, hv2, hr⟩
    exact ⟨_, ⟨j1, ⟨h1, hv1⟩, rfl⟩, _, ⟨j2, ⟨h2, hv2⟩, rfl⟩, hr⟩
  · rintro ⟨u, ⟨j1, ⟨h1, hv1⟩, rfl⟩, v, ⟨j2, ⟨h2, hv2⟩, rfl⟩, hr⟩
    exact ⟨j1, h1, j2, h2, hv1, hv2, hr⟩

lemma mem_pairs' {S : Finset ℕ} {e : ℕ × ℕ} : e ∈ pairs S ↔ e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 < e.2 := by
  simp [pairs, and_assoc]

lemma mem_privSet' {k : ℕ} {S : Finset ℕ} {i : ℕ} :
    i ∈ privSet k S ↔ ∃ e ∈ pairs S, priv k S e.1 e.2 = i := by
  unfold privSet
  exact Finset.mem_image

/-- isolation test. -/
def isolB (P : ℕ × ℕ) (u v q : ℕ) : Bool :=
  !exS2 P (fun u' v' => decide (u' < v') && (decide (u' % q = u % q) &&
    (decide (v' % q = v % q) && !(decide (u' = u) && decide (v' = v)))))

lemma isolB_iff (P : ℕ × ℕ) (u v q : ℕ) : isolB P u v q = true ↔ isol (SS P) u v q := by
  unfold isolB isol
  rw [Bool.not_eq_true', ← Bool.not_eq_true, exS2_iff]
  constructor
  · intro h u' hu' v' hv' hlt h1 h2
    by_contra hne
    apply h
    refine ⟨u', hu', v', hv', ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    refine ⟨hlt, h1, h2, ?_⟩
    by_cases hu : u' = u
    · exact Or.inr (fun hv => hne ⟨hu, hv⟩)
    · exact Or.inl hu
  · rintro h ⟨u', hu', v', hv', hr⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not] at hr
    obtain ⟨hlt, h1, h2, h3⟩ := hr
    obtain ⟨e1, e2⟩ := h u' hu' v' hv' hlt h1 h2
    rcases h3 with h3 | h3
    · exact h3 e1
    · exact h3 e2

/-- least isolating modulus. -/
def modB (P : ℕ × ℕ) (u v : ℕ) : ℕ :=
  firstDown (side (kk P)) (fun q => isolB P u v q) 1

lemma modB_eq (P : ℕ × ℕ) (u v : ℕ) : modB P u v = modOf (kk P) (SS P) u v := by
  classical
  unfold modOf
  have hs := firstDown_spec (side (kk P)) (fun q => isolB P u v q) 1
  by_cases h : ∃ q, 1 ≤ q ∧ q ≤ side (kk P) ∧ isol (SS P) u v q
  · rw [dif_pos h]
    symm
    refine (Nat.find_eq_iff h).2 ?_
    rcases hs with ⟨h1, _⟩ | ⟨h1, h2, h3, h4⟩
    · obtain ⟨q, hq1, hq2, hq3⟩ := h
      have hf : isolB P u v q = false := h1 q hq1 hq2
      rw [← isolB_iff] at hq3
      rw [hq3] at hf
      cases hf
    · refine ⟨⟨h1, h2, (isolB_iff P u v _).1 h3⟩, fun q hq hc => ?_⟩
      obtain ⟨c1, c2, c3⟩ := hc
      have hf : isolB P u v q = false := h4 q c1 hq
      rw [← isolB_iff] at c3
      rw [c3] at hf
      cases hf
  · rw [dif_neg h]
    rcases hs with ⟨_, h2⟩ | ⟨h1, h2, h3, h4⟩
    · exact h2
    · exact absurd ⟨_, h1, h2, (isolB_iff P u v _).1 h3⟩ h

/-- private position of a pair. -/
def privB (P : ℕ × ℕ) (u v : ℕ) : ℕ :=
  idx (kk P) (modB P u v) (u % modB P u v) (v % modB P u v)

lemma privB_eq (P : ℕ × ℕ) (u v : ℕ) : privB P u v = priv (kk P) (SS P) u v := by
  unfold privB priv
  rw [modB_eq]

/-- is position i private. -/
def isPrivB (P : ℕ × ℕ) (i : ℕ) : Bool :=
  exS2 P (fun u v => decide (u < v) && decide (privB P u v = i))

lemma isPrivB_iff (P : ℕ × ℕ) (i : ℕ) : isPrivB P i = true ↔ i ∈ privSet (kk P) (SS P) := by
  rw [mem_privSet']
  unfold isPrivB
  rw [exS2_iff]
  constructor
  · rintro ⟨u, hu, v, hv, h⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨(u, v), mem_pairs'.2 ⟨hu, hv, h.1⟩, by rw [← privB_eq]; exact h.2⟩
  · rintro ⟨e, he, h⟩
    obtain ⟨h1, h2, h3⟩ := mem_pairs'.1 he
    refine ⟨e.1, h1, e.2, h2, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h3, by rw [privB_eq]; exact h⟩

/-- number of non-private positions below i. -/
def rankB (P : ℕ × ℕ) (i : ℕ) : ℕ :=
  countN (L (kk P)) (fun j => decide (j < i) && !isPrivB P j)

lemma rankB_eq (P : ℕ × ℕ) (i : ℕ) (hi : i ≤ L (kk P))
    (inst : DecidablePred (fun j => j ∉ privSet (kk P) (SS P))) :
    rankB P i =
      (@Finset.filter _ (fun j => j ∉ privSet (kk P) (SS P)) inst (Finset.range i)).card := by
  unfold rankB
  rw [countN_eq]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true']
  constructor
  · rintro ⟨_, h1, h2⟩
    refine ⟨h1, fun hm => ?_⟩
    rw [← isPrivB_iff, h2] at hm
    cases hm
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, h1, ?_⟩
    rw [← isPrivB_iff] at h2
    simpa using h2

/-- the decoder bit. -/
def ebitB (k s u v : ℕ) : Bool :=
  parN (side k) (fun i => s.testBit (idx k (i + 1) (u % (i + 1)) (v % (i + 1))))

lemma ebitB_eq (k s u v : ℕ) : ebitB k s u v = ebit k s u v := by
  unfold ebitB ebit
  rw [parN_eq]
  congr 2
  apply Finset.card_bij (fun i _ => i + 1)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hi ⊢
    exact ⟨by omega, hi.2⟩
  · intro a _ b _ h
    omega
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    refine ⟨q', ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hq.2⟩

/-- the bit to write at a private position. -/
def gB (P : ℕ × ℕ) (b : Bool) (s i : ℕ) : Bool :=
  exS2 P (fun u v => decide (u < v) &&
    (decide (privB P u v = i) && xor b (ebitB (kk P) s u v)))

lemma gB_iff (P : ℕ × ℕ) (b : Bool) (s i : ℕ) : gB P b s i = true ↔
    ∃ e ∈ pairs (SS P), priv (kk P) (SS P) e.1 e.2 = i ∧
      xor b (ebit (kk P) s e.1 e.2) = true := by
  unfold gB
  rw [exS2_iff]
  constructor
  · rintro ⟨u, hu, v, hv, h⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨(u, v), mem_pairs'.2 ⟨hu, hv, h.1⟩, by rw [← privB_eq]; exact h.2.1, ?_⟩
    rw [← ebitB_eq]; exact h.2.2
  · rintro ⟨e, he, h, hx⟩
    obtain ⟨h1, h2, h3⟩ := mem_pairs'.1 he
    refine ⟨e.1, h1, e.2, h2, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h3, by rw [privB_eq]; exact h, by rw [ebitB_eq]; exact hx⟩

/-- seed bit with the private bits cleared. -/
def sbit0B (P : ℕ × ℕ) (R i : ℕ) : Bool :=
  if isPrivB P i then false else R.testBit (rankB P i)

lemma sbit0B_eq (P : ℕ × ℕ) (R i : ℕ) (hi : i ≤ L (kk P)) :
    sbit0B P R i = sbit0 (kk P) (SS P) R i := by
  unfold sbit0B sbit0
  by_cases h : i ∈ privSet (kk P) (SS P)
  · rw [if_pos h, if_pos ((isPrivB_iff P i).2 h)]
  · rw [if_neg h, if_neg (by rw [isPrivB_iff]; exact h)]
    exact congrArg _ (rankB_eq P i hi _)

/-- the seed with the private bits cleared. -/
def seedB (P : ℕ × ℕ) (R : ℕ) : ℕ := ofBitsN (L (kk P)) (fun i => sbit0B P R i)

lemma seedB_eq (P : ℕ × ℕ) (R : ℕ) : seedB P R = seed0 (kk P) (SS P) R := by
  unfold seedB seed0 ofBitsN
  congr 1
  funext i
  exact sbit0B_eq P R i (le_of_lt i.2)

/-- final seed bit, given the cleared seed s. -/
def sbitB (P : ℕ × ℕ) (b : Bool) (R s i : ℕ) : Bool :=
  if isPrivB P i then gB P b s i else R.testBit (rankB P i)

lemma sbitB_eq (P : ℕ × ℕ) (b : Bool) (R i : ℕ) (hi : i ≤ L (kk P)) :
    sbitB P b R (seedB P R) i = sbit (kk P) (SS P) b R i := by
  unfold sbitB sbit
  by_cases h : i ∈ privSet (kk P) (SS P)
  · rw [if_pos h, if_pos ((isPrivB_iff P i).2 h), Bool.eq_iff_iff, gB_iff, seedB_eq,
      decide_eq_true_iff]
  · rw [if_neg h, if_neg (by rw [isPrivB_iff]; exact h)]
    exact congrArg _ (rankB_eq P i hi _)

/-- the output for the parameter pair P, the bit b and the free bits R. -/
def outB (P : ℕ × ℕ) (b : Bool) (R : ℕ) : ℕ :=
  ofBitsN (L (kk P)) (fun i => sbitB P b R (seedB P R) i)

lemma outB_eq (N c : ℕ) (b : Bool) (R : ℕ) : outB (N, c) b R =
    Nat.ofBits (fun i : Fin (L (Nat.log2 N)) => sbit (Nat.log2 N) (SS (N, c)) b R i) := by
  unfold outB ofBitsN
  show Nat.ofBits (fun i : Fin (L (Nat.log2 N)) => sbitB (N, c) b R (seedB (N, c) R) i) = _
  congr 1
  funext i
  exact sbitB_eq (N, c) b R i (le_of_lt i.2)

-- the digit set

lemma SS_eq_digits (N c : ℕ) (hk : 1 ≤ Nat.log2 N) :
    SS (N, c) = (Nat.digits (2 ^ Nat.log2 N) c).toFinset := by
  have hb : 2 ≤ 2 ^ Nat.log2 N :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (show 0 < 2 by omega) hk)
  have hpos : ∀ j, 0 < (2 ^ Nat.log2 N) ^ j := fun j => pow_pos (by omega) j
  ext d
  simp only [SS, Finset.mem_image, Finset.mem_filter, Finset.mem_range, List.mem_toFinset, JJ,
    vd, dg, Bool.not_eq_true', decide_eq_false_iff_not, pow_mul]
  constructor
  · rintro ⟨j, ⟨hj, hv⟩, rfl⟩
    have hle : (2 ^ Nat.log2 N) ^ j ≤ c := by
      by_contra hlt
      exact hv (Nat.div_eq_of_lt (by omega))
    have hlen : j < (Nat.digits (2 ^ Nat.log2 N) c).length :=
      (Nat.lt_digits_length_iff (by omega) c).2 hle
    rw [← Nat.getD_digits c j hb, List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  · intro hd
    obtain ⟨j, hlen, rfl⟩ := List.mem_iff_getElem.1 hd
    have hle : (2 ^ Nat.log2 N) ^ j ≤ c := (Nat.lt_digits_length_iff (by omega) c).1 hlen
    have hc0 : c ≠ 0 := by have := hpos j; omega
    have hkj : Nat.log2 N * j ≤ Nat.log2 c := by
      rw [Nat.le_log2 hc0, pow_mul]; exact hle
    have hjk : j ≤ Nat.log2 N * j := Nat.le_mul_of_pos_left j hk
    refine ⟨j, ⟨by omega, ?_⟩, ?_⟩
    · have := Nat.div_pos hle (hpos j)
      omega
    · rw [← Nat.getD_digits c j hb, List.getD_eq_getElem _ _ hlen]

lemma pairs_empty_of_subsingleton {S : Finset ℕ} (h : ∀ a ∈ S, ∀ b ∈ S, a = b) :
    pairs S = ∅ := by
  unfold pairs
  rw [Finset.filter_eq_empty_iff]
  intro e he
  rw [Finset.mem_product] at he
  have := h _ he.1 _ he.2
  omega

lemma sbit_of_pairs_empty (k : ℕ) (S S' : Finset ℕ) (b : Bool) (R i : ℕ) (h : pairs S = ∅)
    (h' : pairs S' = ∅) : sbit k S b R i = sbit k S' b R i := by
  simp [sbit, privSet, h, h']

/-- the algorithm. -/
def cmpAlg (y : ℕ × ℕ) : ℕ :=
  outB (y.1, y.2 / 2 ^ (L (Nat.log2 y.1) - t (Nat.log2 y.1)) / 2)
    ((y.2 / 2 ^ (L (Nat.log2 y.1) - t (Nat.log2 y.1))).testBit 0)
    (y.2 % 2 ^ (L (Nat.log2 y.1) - t (Nat.log2 y.1)))

theorem cmpAlg_eq (y : ℕ × ℕ) : cmpAlg y = cmp0 y := by
  unfold cmpAlg cmp0
  rw [outB_eq]
  congr 1
  funext i
  rcases Nat.eq_zero_or_pos (Nat.log2 y.1) with hk | hk
  · apply sbit_of_pairs_empty
    · apply pairs_empty_of_subsingleton
      intro a ha b hb
      simp only [SS, Finset.mem_image, Finset.mem_filter, Finset.mem_range, dg] at ha hb
      obtain ⟨j1, _, rfl⟩ := ha
      obtain ⟨j2, _, rfl⟩ := hb
      simp [hk, Nat.mod_one]
    · apply pairs_empty_of_subsingleton
      intro a ha b hb
      rw [hk] at ha hb
      simp only [pow_zero, Nat.digits_one, List.mem_toFinset, List.mem_replicate] at ha hb
      rw [ha.2, hb.2]
  · rw [SS_eq_digits _ _ hk]

end Erdos78Cmp
end

-- ===== part: Cmp =====
section
-- Polynomial-time computability of the compression map Erdos78Avoid.cmp0.

open ComplexityTheory Erdos78Avoid

namespace Erdos78Cmp

variable {α β γ δ ε : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
  [BitstringEncoding δ] [BitstringEncoding ε]

-- composition helpers with the outer function given explicitly

theorem comp2 (g : β → γ → δ) (hg : IsPolyTime (fun x : β × γ => g x.1 x.2))
    {f1 : α → β} {f2 : α → γ} (h1 : IsPolyTime f1) (h2 : IsPolyTime f2) :
    IsPolyTime (fun a => g (f1 a) (f2 a)) :=
  PT.comp (g := fun x : β × γ => g x.1 x.2) hg (PT.pair h1 h2)

theorem comp3 {ζ : Type} [BitstringEncoding ζ] (g : β → γ → δ → ζ)
    (hg : IsPolyTime (fun x : β × γ × δ => g x.1 x.2.1 x.2.2))
    {f1 : α → β} {f2 : α → γ} {f3 : α → δ} (h1 : IsPolyTime f1) (h2 : IsPolyTime f2)
    (h3 : IsPolyTime f3) : IsPolyTime (fun a => g (f1 a) (f2 a) (f3 a)) :=
  PT.comp (g := fun x : β × γ × δ => g x.1 x.2.1 x.2.2) hg (PT.pair h1 (PT.pair h2 h3))

theorem comp4 {ζ : Type} [BitstringEncoding ζ] (g : β → γ → δ → ε → ζ)
    (hg : IsPolyTime (fun x : β × γ × δ × ε => g x.1 x.2.1 x.2.2.1 x.2.2.2))
    {f1 : α → β} {f2 : α → γ} {f3 : α → δ} {f4 : α → ε} (h1 : IsPolyTime f1)
    (h2 : IsPolyTime f2) (h3 : IsPolyTime f3) (h4 : IsPolyTime f4) :
    IsPolyTime (fun a => g (f1 a) (f2 a) (f3 a) (f4 a)) :=
  PT.comp (g := fun x : β × γ × δ × ε => g x.1 x.2.1 x.2.2.1 x.2.2.2) hg
    (PT.pair h1 (PT.pair h2 (PT.pair h3 h4)))

-- polynomial bounds

lemma kk_le (P : ℕ × ℕ) : kk P ≤ sz P := by
  have h1 : Nat.log2 P.1 ≤ Nat.size P.1 := log2_le_size _
  have h2 := sz_fst_le P
  rw [sz_nat] at h2
  exact le_trans h1 h2

lemma PBdd_side : PBdd (fun P : ℕ × ℕ => side (kk P)) := by
  refine ⟨Polynomial.C 48 * (Polynomial.X * Polynomial.X) + Polynomial.C 2, fun P => ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have h := kk_le P
  have h2 : kk P ^ 2 ≤ sz P * sz P := by rw [sq]; exact Nat.mul_le_mul h h
  unfold side
  generalize kk P ^ 2 = a at h2 ⊢
  generalize sz P * sz P = b at h2 ⊢
  omega

lemma PBdd_L : PBdd (fun P : ℕ × ℕ => L (kk P)) :=
  PBdd.mono (PBdd.mul (PBdd.mul PBdd_side PBdd_side) PBdd_side)
    (fun P => le_of_eq (by unfold L; ring))

lemma PBdd_JJ : PBdd JJ := by
  refine ⟨Polynomial.X + Polynomial.C 1, fun P => ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  have h1 : Nat.log2 P.2 ≤ Nat.size P.2 := log2_le_size _
  have h2 := sz_snd_le P
  rw [sz_nat] at h2
  unfold JJ
  omega

-- arithmetic of the parameters

theorem kk_pt (hA : PT.ArithFacts) {P : α → ℕ × ℕ} (hP : IsPolyTime P) :
    IsPolyTime (fun a => kk (P a)) := by
  show IsPolyTime (fun a => Nat.log2 (P a).1)
  exact log2' hA (fst' hP)

theorem JJ_pt (hA : PT.ArithFacts) {P : α → ℕ × ℕ} (hP : IsPolyTime P) :
    IsPolyTime (fun a => JJ (P a)) := by
  show IsPolyTime (fun a => Nat.log2 (P a).2 + 1)
  exact add2 hA (log2' hA (snd' hP)) (PT.const 1)

theorem side_pt (hA : PT.ArithFacts) {f : α → ℕ} (hf : IsPolyTime f) :
    IsPolyTime (fun a => side (f a)) := by
  have e : (fun a => side (f a)) = fun a => 48 * (f a * f a) + 2 := by
    funext a; unfold side; ring
  rw [e]
  exact add2 hA (mul2 hA (PT.const 48) (mul2 hA hf hf)) (PT.const 2)

theorem L_pt (hA : PT.ArithFacts) {f : α → ℕ} (hf : IsPolyTime f) :
    IsPolyTime (fun a => L (f a)) := by
  have e : (fun a => L (f a)) = fun a => side (f a) * side (f a) * side (f a) := by
    funext a; unfold L; ring
  rw [e]
  exact mul2 hA (mul2 hA (side_pt hA hf) (side_pt hA hf)) (side_pt hA hf)

theorem t_pt (hA : PT.ArithFacts) {f : α → ℕ} (hf : IsPolyTime f) :
    IsPolyTime (fun a => t (f a)) := by
  have e : (fun a => t (f a)) = fun a => 12 * f a * (12 * f a - 1) / 2 := by
    funext a; unfold t; rw [Nat.choose_two_right]
  rw [e]
  exact half' (mul2 hA (mul2 hA (PT.const 12) hf) (sub2 hA (mul2 hA (PT.const 12) hf) (PT.const 1)))

theorem idx_pt (hA : PT.ArithFacts) {k q u v : α → ℕ} (hk : IsPolyTime k) (hq : IsPolyTime q)
    (hu : IsPolyTime u) (hv : IsPolyTime v) :
    IsPolyTime (fun a => idx (k a) (q a) (u a) (v a)) := by
  have e : (fun a => idx (k a) (q a) (u a) (v a)) =
      fun a => (q a - 1) * (side (k a) * side (k a)) + u a * side (k a) + v a := by
    funext a; unfold idx; ring
  rw [e]
  exact add2 hA (add2 hA (mul2 hA (sub2 hA hq (PT.const 1))
    (mul2 hA (side_pt hA hk) (side_pt hA hk))) (mul2 hA hu (side_pt hA hk))) hv

-- digits

theorem dg_base (hA : PT.ArithFacts) : IsPolyTime (fun x : (ℕ × ℕ) × ℕ => dg x.1 x.2) := by
  show IsPolyTime (fun x : (ℕ × ℕ) × ℕ =>
    x.1.2 / 2 ^ (Nat.log2 x.1.1 * x.2) % 2 ^ Nat.log2 x.1.1)
  exact low2 hA (shr2 hA (snd' PT.fst) (mul2 hA (log2' hA (fst' PT.fst)) PT.snd))
    (log2' hA (fst' PT.fst))

theorem dg_pt (hA : PT.ArithFacts) {P : α → ℕ × ℕ} {j : α → ℕ} (hP : IsPolyTime P)
    (hj : IsPolyTime j) : IsPolyTime (fun a => dg (P a) (j a)) :=
  comp2 dg (dg_base hA) hP hj

theorem vd_base (hA : PT.ArithFacts) : IsPolyTime (fun x : (ℕ × ℕ) × ℕ => vd x.1 x.2) := by
  show IsPolyTime (fun x : (ℕ × ℕ) × ℕ =>
    !decide (x.1.2 / 2 ^ (Nat.log2 x.1.1 * x.2) = 0))
  exact not1 (eq2 hA (shr2 hA (snd' PT.fst) (mul2 hA (log2' hA (fst' PT.fst)) PT.snd))
    (PT.const 0))

theorem vd_pt (hA : PT.ArithFacts) {P : α → ℕ × ℕ} {j : α → ℕ} (hP : IsPolyTime P)
    (hj : IsPolyTime j) : IsPolyTime (fun a => vd (P a) (j a)) :=
  comp2 vd (vd_base hA) hP hj

theorem exS2_pt (hA : PT.ArithFacts) (π : γ → ℕ × ℕ) (r : γ × ℕ × ℕ → Bool)
    (hπ : IsPolyTime π) (hπs : ∀ c, sz (π c) ≤ sz c) (hr : IsPolyTime r) :
    IsPolyTime (fun c => exS2 (π c) (fun u v => r (c, u, v))) := by
  have hJ : PBdd (fun c : γ => JJ (π c)) := PBdd_JJ.comp π hπs
  have hJ' : PBdd (fun c : γ × ℕ => JJ (π c.1)) :=
    PBdd_JJ.comp (fun c : γ × ℕ => π c.1) (fun c => le_trans (hπs c.1) (sz_fst_le c))
  let q2 : (γ × ℕ) × ℕ → Bool := fun x =>
    vd (π x.1.1) x.1.2 && (vd (π x.1.1) x.2 && r (x.1.1, dg (π x.1.1) x.1.2, dg (π x.1.1) x.2))
  have hπ1 : IsPolyTime (fun x : (γ × ℕ) × ℕ => π x.1.1) := PT.comp hπ (fst' PT.fst)
  have hq2 : IsPolyTime q2 :=
    and2 (vd_pt hA hπ1 (snd' PT.fst)) (and2 (vd_pt hA hπ1 PT.snd)
      (PT.comp hr (PT.pair (fst' PT.fst)
        (PT.pair (dg_pt hA hπ1 (snd' PT.fst)) (dg_pt hA hπ1 PT.snd)))))
  let q1 : γ × ℕ → Bool := fun c' => anyN (JJ (π c'.1)) (fun j2 => q2 (c', j2))
  have hq1 : IsPolyTime q1 :=
    anyN_pt hA (fun c' : γ × ℕ => JJ (π c'.1)) q2 (JJ_pt hA (PT.comp hπ PT.fst)) hJ' hq2
  exact anyN_pt hA (fun c => JJ (π c)) q1 (JJ_pt hA hπ) hJ hq1

-- isolation test

theorem isolB_base (hA : PT.ArithFacts) :
    IsPolyTime (fun x : (ℕ × ℕ) × ℕ × ℕ × ℕ => isolB x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  have hU' : IsPolyTime (fun y : ((ℕ × ℕ) × ℕ × ℕ × ℕ) × ℕ × ℕ => y.2.1) := fst' PT.snd
  have hV' : IsPolyTime (fun y : ((ℕ × ℕ) × ℕ × ℕ × ℕ) × ℕ × ℕ => y.2.2) := snd' PT.snd
  have hU : IsPolyTime (fun y : ((ℕ × ℕ) × ℕ × ℕ × ℕ) × ℕ × ℕ => y.1.2.1) :=
    fst' (snd' PT.fst)
  have hV : IsPolyTime (fun y : ((ℕ × ℕ) × ℕ × ℕ × ℕ) × ℕ × ℕ => y.1.2.2.1) :=
    fst' (snd' (snd' PT.fst))
  have hQ : IsPolyTime (fun y : ((ℕ × ℕ) × ℕ × ℕ × ℕ) × ℕ × ℕ => y.1.2.2.2) :=
    snd' (snd' (snd' PT.fst))
  unfold isolB
  exact not1 (exS2_pt hA (fun x : (ℕ × ℕ) × ℕ × ℕ × ℕ => x.1)
    (fun y : ((ℕ × ℕ) × ℕ × ℕ × ℕ) × ℕ × ℕ => decide (y.2.1 < y.2.2) &&
      (decide (y.2.1 % y.1.2.2.2 = y.1.2.1 % y.1.2.2.2) &&
      (decide (y.2.2 % y.1.2.2.2 = y.1.2.2.1 % y.1.2.2.2) &&
        !(decide (y.2.1 = y.1.2.1) && decide (y.2.2 = y.1.2.2.1)))))
    PT.fst sz_fst_le
    (and2 (lt2 hA hU' hV') (and2 (eq2 hA (mod2 hA hU' hQ) (mod2 hA hU hQ))
      (and2 (eq2 hA (mod2 hA hV' hQ) (mod2 hA hV hQ))
        (not1 (and2 (eq2 hA hU' hU) (eq2 hA hV' hV)))))))

theorem isolB_pt (hA : PT.ArithFacts) {P : α → ℕ × ℕ} {u v q : α → ℕ} (hP : IsPolyTime P)
    (hu : IsPolyTime u) (hv : IsPolyTime v) (hq : IsPolyTime q) :
    IsPolyTime (fun a => isolB (P a) (u a) (v a) (q a)) :=
  comp4 isolB (isolB_base hA) hP hu hv hq

-- least isolating modulus and private position

theorem modB_base (hA : PT.ArithFacts) :
    IsPolyTime (fun x : (ℕ × ℕ) × ℕ × ℕ => modB x.1 x.2.1 x.2.2) := by
  unfold modB
  exact firstDown_pt hA (fun x : (ℕ × ℕ) × ℕ × ℕ => side (kk x.1))
    (fun y : ((ℕ × ℕ) × ℕ × ℕ) × ℕ => isolB y.1.1 y.1.2.1 y.1.2.2 y.2) (fun _ => 1)
    (side_pt hA (kk_pt hA PT.fst))
    (PBdd_side.comp (fun x : (ℕ × ℕ) × ℕ × ℕ => x.1) sz_fst_le)
    (isolB_pt hA (fst' PT.fst) (fst' (snd' PT.fst)) (snd' (snd' PT.fst)) PT.snd) (PT.const 1)

theorem modB_pt (hA : PT.ArithFacts) {P : α → ℕ × ℕ} {u v : α → ℕ} (hP : IsPolyTime P)
    (hu : IsPolyTime u) (hv : IsPolyTime v) :
    IsPolyTime (fun a => modB (P a) (u a) (v a)) :=
  comp3 modB (modB_base hA) hP hu hv

theorem privB_pt (hA : PT.ArithFacts) {P : α → ℕ × ℕ} {u v : α → ℕ} (hP : IsPolyTime P)
    (hu : IsPolyTime u) (hv : IsPolyTime v) :
    IsPolyTime (fun a => privB (P a) (u a) (v a)) := by
  unfold privB
  exact idx_pt hA (kk_pt hA hP) (modB_pt hA hP hu hv) (mod2 hA hu (modB_pt hA hP hu hv))
    (mod2 hA hv (modB_pt hA hP hu hv))

theorem isPrivB_base (hA : PT.ArithFacts) :
    IsPolyTime (fun x : (ℕ × ℕ) × ℕ => isPrivB x.1 x.2) := by
  unfold isPrivB
  exact exS2_pt hA (fun x : (ℕ × ℕ) × ℕ => x.1)
    (fun y : ((ℕ × ℕ) × ℕ) × ℕ × ℕ =>
      decide (y.2.1 < y.2.2) && decide (privB y.1.1 y.2.1 y.2.2 = y.1.2))
    PT.fst sz_fst_le
    (and2 (lt2 hA (fst' PT.snd) (snd' PT.snd))
      (eq2 hA (privB_pt hA (fst' PT.fst) (fst' PT.snd) (snd' PT.snd)) (snd' PT.fst)))

theorem isPrivB_pt (hA : PT.ArithFacts) {P : α → ℕ × ℕ} {i : α → ℕ} (hP : IsPolyTime P)
    (hi : IsPolyTime i) : IsPolyTime (fun a => isPrivB (P a) (i a)) :=
  comp2 isPrivB (isPrivB_base hA) hP hi

theorem rankB_base (hA : PT.ArithFacts) :
    IsPolyTime (fun x : (ℕ × ℕ) × ℕ => rankB x.1 x.2) := by
  unfold rankB
  exact countN_pt hA (fun x : (ℕ × ℕ) × ℕ => L (kk x.1))
    (fun y : ((ℕ × ℕ) × ℕ) × ℕ => decide (y.2 < y.1.2) && !isPrivB y.1.1 y.2)
    (L_pt hA (kk_pt hA PT.fst)) (PBdd_L.comp (fun x : (ℕ × ℕ) × ℕ => x.1) sz_fst_le)
    (and2 (lt2 hA PT.snd (snd' PT.fst)) (not1 (isPrivB_pt hA (fst' PT.fst) PT.snd)))

theorem rankB_pt (hA : PT.ArithFacts) {P : α → ℕ × ℕ} {i : α → ℕ} (hP : IsPolyTime P)
    (hi : IsPolyTime i) : IsPolyTime (fun a => rankB (P a) (i a)) :=
  comp2 rankB (rankB_base hA) hP hi

-- the decoder bit

theorem ebitB_base (hA : PT.ArithFacts) :
    IsPolyTime (fun x : (ℕ × ℕ) × ℕ × ℕ × ℕ => ebitB (kk x.1) x.2.1 x.2.2.1 x.2.2.2) := by
  have hQ : IsPolyTime (fun y : ((ℕ × ℕ) × ℕ × ℕ × ℕ) × ℕ => y.2 + 1) :=
    add2 hA PT.snd (PT.const 1)
  unfold ebitB
  exact parN_pt hA (fun x : (ℕ × ℕ) × ℕ × ℕ × ℕ => side (kk x.1))
    (fun y : ((ℕ × ℕ) × ℕ × ℕ × ℕ) × ℕ => y.1.2.1.testBit
      (idx (kk y.1.1) (y.2 + 1) (y.1.2.2.1 % (y.2 + 1)) (y.1.2.2.2 % (y.2 + 1))))
    (side_pt hA (kk_pt hA PT.fst))
    (PBdd_side.comp (fun x : (ℕ × ℕ) × ℕ × ℕ × ℕ => x.1) sz_fst_le)
    (tb2 hA (fst' (snd' PT.fst)) (idx_pt hA (kk_pt hA (fst' PT.fst)) hQ
      (mod2 hA (fst' (snd' (snd' PT.fst))) hQ) (mod2 hA (snd' (snd' (snd' PT.fst))) hQ)))

theorem ebitB_pt (hA : PT.ArithFacts) {P : α → ℕ × ℕ} {s u v : α → ℕ} (hP : IsPolyTime P)
    (hs : IsPolyTime s) (hu : IsPolyTime u) (hv : IsPolyTime v) :
    IsPolyTime (fun a => ebitB (kk (P a)) (s a) (u a) (v a)) :=
  comp4 (fun P s u v => ebitB (kk P) s u v) (ebitB_base hA) hP hs hu hv

theorem gB_base (hA : PT.ArithFacts) :
    IsPolyTime (fun x : (ℕ × ℕ) × Bool × ℕ × ℕ => gB x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold gB
  exact exS2_pt hA (fun x : (ℕ × ℕ) × Bool × ℕ × ℕ => x.1)
    (fun y : ((ℕ × ℕ) × Bool × ℕ × ℕ) × ℕ × ℕ => decide (y.2.1 < y.2.2) &&
      (decide (privB y.1.1 y.2.1 y.2.2 = y.1.2.2.2) &&
        xor y.1.2.1 (ebitB (kk y.1.1) y.1.2.2.1 y.2.1 y.2.2)))
    PT.fst sz_fst_le
    (and2 (lt2 hA (fst' PT.snd) (snd' PT.snd))
      (and2 (eq2 hA (privB_pt hA (fst' PT.fst) (fst' PT.snd) (snd' PT.snd))
          (snd' (snd' (snd' PT.fst))))
        (xor2 (fst' (snd' PT.fst))
          (ebitB_pt hA (fst' PT.fst) (fst' (snd' (snd' PT.fst))) (fst' PT.snd)
            (snd' PT.snd)))))

theorem gB_pt (hA : PT.ArithFacts) {P : α → ℕ × ℕ} {b : α → Bool} {s i : α → ℕ}
    (hP : IsPolyTime P) (hb : IsPolyTime b) (hs : IsPolyTime s) (hi : IsPolyTime i) :
    IsPolyTime (fun a => gB (P a) (b a) (s a) (i a)) :=
  comp4 gB (gB_base hA) hP hb hs hi

-- the seed bits and the output

theorem sbit0B_base (hA : PT.ArithFacts) :
    IsPolyTime (fun x : ((ℕ × ℕ) × ℕ) × ℕ => sbit0B x.1.1 x.1.2 x.2) := by
  unfold sbit0B
  exact PT.ite (isPrivB_pt hA (fst' PT.fst) PT.snd) (PT.const false)
    (tb2 hA (snd' PT.fst) (rankB_pt hA (fst' PT.fst) PT.snd))

theorem seedB_base (hA : PT.ArithFacts) :
    IsPolyTime (fun x : (ℕ × ℕ) × ℕ => seedB x.1 x.2) := by
  unfold seedB
  exact ofBitsN_pt hA (fun x : (ℕ × ℕ) × ℕ => L (kk x.1))
    (fun y : ((ℕ × ℕ) × ℕ) × ℕ => sbit0B y.1.1 y.1.2 y.2)
    (L_pt hA (kk_pt hA PT.fst)) (PBdd_L.comp (fun x : (ℕ × ℕ) × ℕ => x.1) sz_fst_le)
    (sbit0B_base hA)

theorem seedB_pt (hA : PT.ArithFacts) {P : α → ℕ × ℕ} {R : α → ℕ} (hP : IsPolyTime P)
    (hR : IsPolyTime R) : IsPolyTime (fun a => seedB (P a) (R a)) :=
  comp2 seedB (seedB_base hA) hP hR

theorem sbitB_base (hA : PT.ArithFacts) :
    IsPolyTime (fun x : ((ℕ × ℕ) × Bool × ℕ × ℕ) × ℕ =>
      sbitB x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2) := by
  unfold sbitB
  exact PT.ite (isPrivB_pt hA (fst' PT.fst) PT.snd)
    (gB_pt hA (fst' PT.fst) (fst' (snd' PT.fst)) (snd' (snd' (snd' PT.fst))) PT.snd)
    (tb2 hA (fst' (snd' (snd' PT.fst))) (rankB_pt hA (fst' PT.fst) PT.snd))

theorem out4_base (hA : PT.ArithFacts) :
    IsPolyTime (fun x : (ℕ × ℕ) × Bool × ℕ × ℕ =>
      ofBitsN (L (kk x.1)) (fun i => sbitB x.1 x.2.1 x.2.2.1 x.2.2.2 i)) :=
  ofBitsN_pt hA (fun x : (ℕ × ℕ) × Bool × ℕ × ℕ => L (kk x.1))
    (fun y : ((ℕ × ℕ) × Bool × ℕ × ℕ) × ℕ => sbitB y.1.1 y.1.2.1 y.1.2.2.1 y.1.2.2.2 y.2)
    (L_pt hA (kk_pt hA PT.fst))
    (PBdd_L.comp (fun x : (ℕ × ℕ) × Bool × ℕ × ℕ => x.1) sz_fst_le) (sbitB_base hA)

theorem outB_pt (hA : PT.ArithFacts) {P : α → ℕ × ℕ} {b : α → Bool} {R : α → ℕ}
    (hP : IsPolyTime P) (hb : IsPolyTime b) (hR : IsPolyTime R) :
    IsPolyTime (fun a => outB (P a) (b a) (R a)) := by
  have h := PT.comp
    (g := fun x : (ℕ × ℕ) × Bool × ℕ × ℕ =>
      ofBitsN (L (kk x.1)) (fun i => sbitB x.1 x.2.1 x.2.2.1 x.2.2.2 i))
    (out4_base hA) (PT.pair hP (PT.pair hb (PT.pair hR (seedB_pt hA hP hR))))
  exact h

theorem cmpAlg_pt (hA : PT.ArithFacts) : IsPolyTime cmpAlg := by
  have hk : IsPolyTime (fun y : ℕ × ℕ => Nat.log2 y.1) := log2' hA PT.fst
  have hD : IsPolyTime (fun y : ℕ × ℕ => L (Nat.log2 y.1) - t (Nat.log2 y.1)) :=
    sub2 hA (L_pt hA hk) (t_pt hA hk)
  have hw : IsPolyTime (fun y : ℕ × ℕ =>
      y.2 / 2 ^ (L (Nat.log2 y.1) - t (Nat.log2 y.1))) := shr2 hA PT.snd hD
  have h1 : IsPolyTime (fun y : ℕ × ℕ =>
      (y.1, y.2 / 2 ^ (L (Nat.log2 y.1) - t (Nat.log2 y.1)) / 2)) := PT.pair PT.fst (half' hw)
  have h2 : IsPolyTime (fun y : ℕ × ℕ =>
      (y.2 / 2 ^ (L (Nat.log2 y.1) - t (Nat.log2 y.1))).testBit 0) := tb2 hA hw (PT.const 0)
  have h3 : IsPolyTime (fun y : ℕ × ℕ =>
      y.2 % 2 ^ (L (Nat.log2 y.1) - t (Nat.log2 y.1))) := low2 hA PT.snd hD
  exact outB_pt hA h1 h2 h3

/-- The compression map is polynomial-time computable. -/
theorem cmp0_polyTime (hA : PT.ArithFacts) : IsPolyTime Erdos78Avoid.cmp0 := by
  have e : Erdos78Avoid.cmp0 = cmpAlg := (funext cmpAlg_eq).symm
  rw [e]
  exact cmpAlg_pt hA

end Erdos78Cmp
end

-- ===== part: NT =====
section
/-!
Elementary number theory: a positive integer smaller than 4^n / (2n+1) cannot be
divisible by every q in 1..2n (otherwise the central binomial coefficient divides it).
-/

namespace Erdos78AvoidNT

theorem exists_not_dvd (n D : ℕ) (hD : 0 < D) (h : D * (2 * n + 1) < 4 ^ n) :
    ∃ q, 1 ≤ q ∧ q ≤ 2 * n ∧ ¬ q ∣ D := by
  by_contra hc
  push Not at hc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at h
    omega
  have h2n : 2 * n ≠ 0 := by omega
  have hdvd : (2 * n).choose n ∣ D := by
    rw [← Nat.factorization_prime_le_iff_dvd (Nat.choose_pos (by omega)).ne' hD.ne']
    intro p hp
    have hq := Nat.pow_log_le_self p h2n
    have hq1 : 1 ≤ p ^ Nat.log p (2 * n) := Nat.one_le_pow _ _ hp.pos
    have hpd := hc _ hq1 hq
    rw [hp.pow_dvd_iff_le_factorization hD.ne'] at hpd
    exact Nat.factorization_choose_le_log.trans hpd
  have hle := Nat.le_of_dvd hD hdvd
  have h4 := Nat.four_pow_le_two_mul_add_one_mul_central_binom n
  have hm := Nat.mul_le_mul_left (2 * n + 1) hle
  rw [Nat.mul_comm] at h
  omega

end Erdos78AvoidNT
end

-- ===== part: H2core =====
section
namespace Erdos78Avoid
open Filter ComplexityTheory Erdos78

/-- rank of position i among the non-private positions. -/
noncomputable def rank (k : ℕ) (S : Finset ℕ) (i : ℕ) : ℕ := by
  classical exact ((Finset.range i).filter (fun j => j ∉ privSet k S)).card

lemma sbit0_eq (k : ℕ) (S : Finset ℕ) (R i : ℕ) :
    sbit0 k S R i = true ↔ i ∉ privSet k S ∧ R.testBit (rank k S i) = true := by
  classical
  unfold sbit0 rank
  split_ifs with h
  · simp [h]
  · simp only [h, not_false_eq_true, true_and]

lemma sbit_priv (k : ℕ) (S : Finset ℕ) (b : Bool) (R i : ℕ) (h : i ∈ privSet k S) :
    sbit k S b R i = true ↔
      ∃ e ∈ pairs S, priv k S e.1 e.2 = i ∧ xor b (ebit k (seed0 k S R) e.1 e.2) = true := by
  unfold sbit
  rw [if_pos h]
  exact decide_eq_true_iff

lemma sbit_nonpriv (k : ℕ) (S : Finset ℕ) (b : Bool) (R i : ℕ) (h : i ∉ privSet k S) :
    sbit k S b R i = R.testBit (rank k S i) := by
  classical
  unfold sbit rank
  rw [if_neg h]

lemma dec0_eq (k s u v : ℕ) :
    dec0 (s, 2 ^ k, u, v) = (decide (u < v) && ebit k s u v) := by
  simp [dec0]

lemma cmp0_eq (k x : ℕ) :
    cmp0 (2 ^ k, x) = Nat.ofBits (fun i : Fin (L k) =>
      sbit k (Nat.digits (2 ^ k) (x / 2 ^ (L k - t k) / 2)).toFinset
        ((x / 2 ^ (L k - t k)).testBit 0) (x % 2 ^ (L k - t k)) i) := by
  have h : Nat.log2 (2 ^ k) = k := Nat.log2_two_pow
  simp only [cmp0]
  rw [h]

/- Arithmetic -/

lemma two_le_side (k : ℕ) : 2 ≤ side k := by
  unfold side
  omega

lemma t_succ (j : ℕ) : t (j + 1) = (6 * j + 6) * (12 * j + 11) := by
  unfold t
  rw [Nat.choose_two_right]
  have h1 : 12 * (j + 1) - 1 = 12 * j + 11 := by omega
  rw [h1]
  have h2 : 12 * (j + 1) * (12 * j + 11) = 2 * ((6 * j + 6) * (12 * j + 11)) := by ring
  rw [h2, Nat.mul_div_cancel_left _ (by norm_num)]

lemma t_bound (k : ℕ) (hk : 1 ≤ k) : side k + 12 * k ^ 2 + 1 ≤ t k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [t_succ]
  unfold side
  nlinarith [Nat.zero_le j, Nat.zero_le (j * j)]

lemma t_le_L (k : ℕ) (hk : 1 ≤ k) : t k ≤ L k := by
  have hA := two_le_side k
  have h4 : side k * 2 ≤ side k * side k := Nat.mul_le_mul_left _ hA
  have h5 : side k * side k * 1 ≤ side k * side k * side k := Nat.mul_le_mul_left _ (by omega)
  have h6 : L k = side k * side k * side k := by unfold L; ring
  have h7 : t k ≤ side k * 2 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [t_succ]
    unfold side
    nlinarith [Nat.zero_le j, Nat.zero_le (j * j)]
  rw [h6]
  linarith

lemma exists_not_dvd
    (hN : ∀ n D : ℕ, 0 < D → D * (2 * n + 1) < 4 ^ n → ∃ q, 1 ≤ q ∧ q ≤ 2 * n ∧ ¬ q ∣ D)
    (k D : ℕ) (hD : 0 < D) (hle : D ≤ 2 ^ (24 * k ^ 2)) :
    ∃ q, 1 ≤ q ∧ q ≤ side k ∧ ¬ q ∣ D := by
  have hlt : D * (2 * (24 * k ^ 2 + 1) + 1) < 4 ^ (24 * k ^ 2 + 1) := by
    have h4 : (4 : ℕ) ^ (24 * k ^ 2 + 1) = 2 ^ (24 * k ^ 2) * (2 * 2 ^ (24 * k ^ 2 + 1)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ', ← pow_add]
      congr 1
      ring
    have h5 : 24 * k ^ 2 + 1 < 2 ^ (24 * k ^ 2 + 1) := Nat.lt_two_pow_self
    rw [h4]
    calc D * (2 * (24 * k ^ 2 + 1) + 1)
        ≤ 2 ^ (24 * k ^ 2) * (2 * (24 * k ^ 2 + 1) + 1) := Nat.mul_le_mul_right _ hle
      _ < 2 ^ (24 * k ^ 2) * (2 * 2 ^ (24 * k ^ 2 + 1)) :=
        (Nat.mul_lt_mul_left (by positivity)).2 (by omega)
  obtain ⟨q, h1, h2, h3⟩ := hN _ D hD hlt
  exact ⟨q, h1, by unfold side; omega, h3⟩

/- Isolation -/

/-- absolute difference of two naturals. -/
def gap (u w : ℕ) : ℕ := (u - w) + (w - u)

lemma gap_pos {u w : ℕ} (h : w ≠ u) : 0 < gap u w := by
  unfold gap
  omega

lemma gap_le {u w n : ℕ} (hu : u < n) (hw : w < n) : gap u w ≤ n := by
  unfold gap
  omega

lemma dvd_gap {u w q : ℕ} (h : w % q = u % q) : q ∣ gap u w := by
  unfold gap
  exact Nat.dvd_add (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h.symm))
    (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h))

lemma prod_gap_pos (S : Finset ℕ) (u : ℕ) : 0 < ∏ w ∈ S.erase u, gap u w :=
  Finset.prod_pos fun _ hw => gap_pos (Finset.ne_of_mem_erase hw)

lemma prod_gap_le (k : ℕ) (S : Finset ℕ) (hS : ∀ w ∈ S, w < 2 ^ k) (u : ℕ) (hu : u < 2 ^ k) :
    ∏ w ∈ S.erase u, gap u w ≤ (2 ^ k) ^ S.card := by
  calc ∏ w ∈ S.erase u, gap u w ≤ (2 ^ k) ^ (S.erase u).card :=
        Finset.prod_le_pow_card _ _ _ fun w hw => gap_le hu (hS w (Finset.mem_of_mem_erase hw))
    _ ≤ (2 ^ k) ^ S.card := Nat.pow_le_pow_right (by positivity) (Finset.card_erase_le)

lemma exists_isol
    (hN : ∀ n D : ℕ, 0 < D → D * (2 * n + 1) < 4 ^ n → ∃ q, 1 ≤ q ∧ q ≤ 2 * n ∧ ¬ q ∣ D)
    (k : ℕ) (S : Finset ℕ) (hS : ∀ w ∈ S, w < 2 ^ k) (hcard : S.card = 12 * k)
    (u v : ℕ) (hu : u < 2 ^ k) (hv : v < 2 ^ k) :
    ∃ q, 1 ≤ q ∧ q ≤ side k ∧ isol S u v q := by
  have hle : (∏ w ∈ S.erase u, gap u w) * (∏ w ∈ S.erase v, gap v w) ≤ 2 ^ (24 * k ^ 2) := by
    calc (∏ w ∈ S.erase u, gap u w) * (∏ w ∈ S.erase v, gap v w)
        ≤ (2 ^ k) ^ S.card * (2 ^ k) ^ S.card :=
          Nat.mul_le_mul (prod_gap_le k S hS u hu) (prod_gap_le k S hS v hv)
      _ = 2 ^ (24 * k ^ 2) := by
          rw [hcard, ← pow_mul, ← pow_add]
          congr 1
          ring
  obtain ⟨q, h1, h2, h3⟩ :=
    exists_not_dvd hN k _ (Nat.mul_pos (prod_gap_pos S u) (prod_gap_pos S v)) hle
  refine ⟨q, h1, h2, ?_⟩
  intro u' hu' v' hv' _ hmu hmv
  constructor
  · by_contra hne
    exact h3 (Dvd.dvd.mul_right ((dvd_gap hmu).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hne, hu'⟩))) _)
  · by_contra hne
    exact h3 (Dvd.dvd.mul_left ((dvd_gap hmv).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hne, hv'⟩))) _)

/-- every pair of elements of S has an isolating modulus in 1..A. -/
def IsolAll (k : ℕ) (S : Finset ℕ) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ∃ q, 1 ≤ q ∧ q ≤ side k ∧ isol S u v q

lemma modOf_spec {k : ℕ} {S : Finset ℕ} {u v : ℕ}
    (h : ∃ q, 1 ≤ q ∧ q ≤ side k ∧ isol S u v q) :
    1 ≤ modOf k S u v ∧ modOf k S u v ≤ side k ∧ isol S u v (modOf k S u v) := by
  classical
  unfold modOf
  rw [dif_pos h]
  exact Nat.find_spec h

/- The index map -/

lemma divmod_unique {A x a x' a' : ℕ} (ha : a < A) (ha' : a' < A)
    (h : x * A + a = x' * A + a') : x = x' ∧ a = a' := by
  have hx : x = x' := by
    rcases lt_trichotomy x x' with hlt | heq | hgt
    · exfalso
      have h1 : (x + 1) * A ≤ x' * A := Nat.mul_le_mul_right _ hlt
      have e : (x + 1) * A = x * A + A := by ring
      omega
    · exact heq
    · exfalso
      have h1 : (x' + 1) * A ≤ x * A := Nat.mul_le_mul_right _ hgt
      have e : (x' + 1) * A = x' * A + A := by ring
      omega
  subst hx
  exact ⟨rfl, by omega⟩

lemma idx_inj {k q a b q' a' b' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (ha : a < side k)
    (ha' : a' < side k) (hb : b < side k) (hb' : b' < side k)
    (h : idx k q a b = idx k q' a' b') : q = q' ∧ a = a' ∧ b = b' := by
  unfold idx at h
  have e : ∀ x y z : ℕ, x * side k ^ 2 + y * side k + z = (x * side k + y) * side k + z := by
    intro x y z
    ring
  rw [e, e] at h
  obtain ⟨h1, h2⟩ := divmod_unique hb hb' h
  obtain ⟨h3, h4⟩ := divmod_unique ha ha' h1
  exact ⟨by omega, h4, h2⟩

lemma idx_lt {k q a b : ℕ} (hq : 1 ≤ q) (hqA : q ≤ side k) (ha : a < side k) (hb : b < side k) :
    idx k q a b < L k := by
  unfold idx L
  generalize side k = A at *
  obtain ⟨q0, rfl⟩ : ∃ q0, q = q0 + 1 := ⟨q - 1, by omega⟩
  have h1 : (a + 1) * A ≤ A * A := Nat.mul_le_mul_right _ ha
  have h2 : (q0 + 1) * (A * A) ≤ A * (A * A) := Nat.mul_le_mul_right _ hqA
  have e1 : q0 + 1 - 1 = q0 := by omega
  rw [e1]
  nlinarith [h1, h2]

/- Privacy -/

lemma mem_pairs {S : Finset ℕ} {e : ℕ × ℕ} : e ∈ pairs S ↔ e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 < e.2 := by
  simp [pairs, and_assoc]

lemma mem_privSet {k : ℕ} {S : Finset ℕ} {i : ℕ} :
    i ∈ privSet k S ↔ ∃ e ∈ pairs S, priv k S e.1 e.2 = i := by
  unfold privSet
  exact Finset.mem_image

lemma idx_eq_priv {k : ℕ} {S : Finset ℕ} (hI : IsolAll k S) {e e' : ℕ × ℕ} (he : e ∈ pairs S)
    (he' : e' ∈ pairs S) {q : ℕ} (hq1 : 1 ≤ q) (hqA : q ≤ side k)
    (h : idx k q (e'.1 % q) (e'.2 % q) = priv k S e.1 e.2) :
    q = modOf k S e.1 e.2 ∧ e' = e := by
  rw [mem_pairs] at he he'
  obtain ⟨m1, mA, miso⟩ := modOf_spec (hI e.1 he.1 e.2 he.2.1)
  unfold priv at h
  have hlt : ∀ x n : ℕ, 1 ≤ n → n ≤ side k → x % n < side k := fun x n h1 h2 =>
    lt_of_lt_of_le (Nat.mod_lt _ h1) h2
  obtain ⟨h1, h2, h3⟩ := idx_inj hq1 m1 (hlt _ _ hq1 hqA) (hlt _ _ m1 mA) (hlt _ _ hq1 hqA)
    (hlt _ _ m1 mA) h
  refine ⟨h1, ?_⟩
  rw [h1] at h2 h3
  obtain ⟨h4, h5⟩ := miso e'.1 he'.1 e'.2 he'.2.1 he'.2.2 h2 h3
  exact Prod.ext h4 h5

lemma priv_inj {k : ℕ} {S : Finset ℕ} (hI : IsolAll k S) {e e' : ℕ × ℕ} (he : e ∈ pairs S)
    (he' : e' ∈ pairs S) (h : priv k S e'.1 e'.2 = priv k S e.1 e.2) : e' = e := by
  have he'' := mem_pairs.1 he'
  obtain ⟨m1, mA, _⟩ := modOf_spec (hI e'.1 he''.1 e'.2 he''.2.1)
  exact (idx_eq_priv hI he he' m1 mA h).2

lemma priv_lt {k : ℕ} {S : Finset ℕ} (hI : IsolAll k S) {e : ℕ × ℕ} (he : e ∈ pairs S) :
    priv k S e.1 e.2 < L k := by
  have he' := mem_pairs.1 he
  obtain ⟨m1, mA, _⟩ := modOf_spec (hI e.1 he'.1 e.2 he'.2.1)
  exact idx_lt m1 mA (lt_of_lt_of_le (Nat.mod_lt _ m1) mA) (lt_of_lt_of_le (Nat.mod_lt _ m1) mA)

lemma privSet_lt {k : ℕ} {S : Finset ℕ} (hI : IsolAll k S) {i : ℕ} (hi : i ∈ privSet k S) :
    i < L k := by
  obtain ⟨e, he, rfl⟩ := mem_privSet.1 hi
  exact priv_lt hI he

lemma privSet_card {k : ℕ} {S : Finset ℕ} (hI : IsolAll k S) :
    (privSet k S).card = (pairs S).card := by
  unfold privSet
  apply Finset.card_image_of_injOn
  intro e he e' he' h
  exact priv_inj hI (Finset.mem_coe.1 he') (Finset.mem_coe.1 he) h

lemma pairs_insert (a : ℕ) (s : Finset ℕ) (hmax : ∀ x ∈ s, x < a) :
    pairs (insert a s) = pairs s ∪ s.image (fun u => (u, a)) := by
  ext e
  rw [Finset.mem_union, mem_pairs, mem_pairs, Finset.mem_image, Finset.mem_insert,
    Finset.mem_insert]
  constructor
  · rintro ⟨h1 | h1, h2 | h2, h3⟩
    · omega
    · have := hmax _ h2
      omega
    · exact Or.inr ⟨e.1, h1, Prod.ext rfl h2.symm⟩
    · exact Or.inl ⟨h1, h2, h3⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨u, hu, rfl⟩)
    · exact ⟨Or.inr h1, Or.inr h2, h3⟩
    · exact ⟨Or.inr hu, Or.inl rfl, hmax u hu⟩

lemma pairs_card (S : Finset ℕ) : (pairs S).card = S.card.choose 2 := by
  refine Finset.induction_on_max S ?_ ?_
  · simp [pairs]
  · intro a s hmax ih
    have ha : a ∉ s := fun h => lt_irrefl _ (hmax a h)
    have hdisj : Disjoint (pairs s) (s.image (fun u => (u, a))) := by
      rw [Finset.disjoint_left]
      intro e he he2
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 he2
      have := hmax _ (mem_pairs.1 he).2.1
      simp at this
    have hch : (s.card + 1).choose 2 = s.card.choose 1 + s.card.choose 2 :=
      Nat.choose_succ_succ' s.card 1
    rw [pairs_insert a s hmax, Finset.card_union_of_disjoint hdisj, ih,
      Finset.card_image_of_injective _ (fun u u' h => (Prod.mk.inj h).1),
      Finset.card_insert_of_notMem ha, hch, Nat.choose_one_right]
    omega

/- Ranks of the non-private positions -/

lemma rank_lt_rank (k : ℕ) (S : Finset ℕ) {i j : ℕ} (hij : i < j) (hi : i ∉ privSet k S) :
    rank k S i < rank k S j := by
  classical
  unfold rank
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset ?_).2 ⟨i, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨by omega, hx.2⟩
  · simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hij, hi⟩
  · simp only [Finset.mem_filter, Finset.mem_range]
    omega

lemma rank_inj (k : ℕ) (S : Finset ℕ) {i j : ℕ} (hi : i ∉ privSet k S) (hj : j ∉ privSet k S)
    (h : rank k S i = rank k S j) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have := rank_lt_rank k S hlt hi
    omega
  · exact heq
  · have := rank_lt_rank k S hgt hj
    omega

lemma rank_L (k : ℕ) (S : Finset ℕ) (hP : ∀ i ∈ privSet k S, i < L k) :
    rank k S (L k) + (privSet k S).card = L k := by
  classical
  unfold rank
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range (L k))
    (fun j => j ∈ privSet k S)
  have h2 : (Finset.range (L k)).filter (fun j => j ∈ privSet k S) = privSet k S := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨hP x h, h⟩⟩
  rw [h2, Finset.card_range] at h
  omega

lemma rank_lt (k : ℕ) (S : Finset ℕ) (hP : ∀ i ∈ privSet k S, i < L k) {i : ℕ} (hi : i < L k)
    (hnp : i ∉ privSet k S) : rank k S i < L k - (privSet k S).card := by
  have h1 := rank_lt_rank k S hi hnp
  have h2 := rank_L k S hP
  omega

/- The compressed residual string R -/

/-- the non-private bits of s, listed in increasing order of position. -/
noncomputable def Rof (k : ℕ) (S : Finset ℕ) (s : ℕ) : ℕ := by
  classical exact Nat.ofBits (fun j : Fin (L k - t k) =>
    decide (∃ i, i < L k ∧ i ∉ privSet k S ∧ rank k S i = j ∧ s.testBit i = true))

lemma Rof_lt (k : ℕ) (S : Finset ℕ) (s : ℕ) : Rof k S s < 2 ^ (L k - t k) := by
  unfold Rof
  exact Nat.ofBits_lt_two_pow _

lemma Rof_testBit (k : ℕ) (S : Finset ℕ) (s : ℕ) (hP : ∀ i ∈ privSet k S, i < L k)
    (hc : (privSet k S).card = t k) {i : ℕ} (hi : i < L k) (hnp : i ∉ privSet k S) :
    (Rof k S s).testBit (rank k S i) = s.testBit i := by
  have hr : rank k S i < L k - t k := hc ▸ rank_lt k S hP hi hnp
  unfold Rof
  rw [Nat.testBit_ofBits_lt _ _ hr, Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨i', _, hnp', hrk, hb⟩
    have : i' = i := rank_inj k S hnp' hnp hrk
    rw [← this]
    exact hb
  · intro hb
    exact ⟨i, hi, hnp, rfl, hb⟩

/- The cleared seed -/

lemma seed0_testBit_lt (k : ℕ) (S : Finset ℕ) (R : ℕ) {j : ℕ} (hj : j < L k) :
    (seed0 k S R).testBit j = sbit0 k S R j := by
  unfold seed0
  exact Nat.testBit_ofBits_lt _ _ hj

lemma seed0_testBit (k : ℕ) (S : Finset ℕ) (s : ℕ) (hP : ∀ i ∈ privSet k S, i < L k)
    (hc : (privSet k S).card = t k) (hs : s < 2 ^ L k) (j : ℕ) :
    (seed0 k S (Rof k S s)).testBit j = true ↔ j ∉ privSet k S ∧ s.testBit j = true := by
  by_cases hj : j < L k
  · rw [seed0_testBit_lt k S _ hj, sbit0_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← Rof_testBit k S s hP hc hj h1]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [Rof_testBit k S s hP hc hj h1]; exact h2⟩
  · have h1 : (seed0 k S (Rof k S s)).testBit j = false := by
      unfold seed0
      exact Nat.testBit_ofBits_ge _ _ (by omega)
    have h2 : s.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [h1, h2]

/- Flipping one private bit flips the pair bit -/

lemma decide_odd_succ (n : ℕ) : decide (Odd (n + 1)) = !decide (Odd n) := by
  by_cases h : Odd n
  · have h' : ¬ Odd (n + 1) := by
      rw [Nat.odd_add_one]
      exact not_not.2 h
    simp [h, h']
  · have h' : Odd (n + 1) := Nat.odd_add_one.2 h
    simp [h, h']

lemma ebit_flip {k : ℕ} {S : Finset ℕ} {s : ℕ} (hI : IsolAll k S)
    (hc : (privSet k S).card = t k) (hs : s < 2 ^ L k) {e : ℕ × ℕ} (he : e ∈ pairs S) :
    ebit k s e.1 e.2 =
      xor (s.testBit (priv k S e.1 e.2)) (ebit k (seed0 k S (Rof k S s)) e.1 e.2) := by
  have hP : ∀ i ∈ privSet k S, i < L k := fun i hi => privSet_lt hI hi
  have he' := mem_pairs.1 he
  obtain ⟨m1, mA, _⟩ := modOf_spec (hI e.1 he'.1 e.2 he'.2.1)
  have hF : (Finset.Icc 1 (side k)).filter
        (fun q => (seed0 k S (Rof k S s)).testBit (idx k q (e.1 % q) (e.2 % q)) = true)
      = ((Finset.Icc 1 (side k)).filter
        (fun q => s.testBit (idx k q (e.1 % q) (e.2 % q)) = true)).erase (modOf k S e.1 e.2) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase,
      seed0_testBit k S s hP hc hs]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨?_, ⟨h1, h2⟩, h4⟩
      intro hq
      apply h3
      rw [hq]
      exact mem_privSet.2 ⟨e, he, rfl⟩
    · rintro ⟨h0, ⟨h1, h2⟩, h4⟩
      refine ⟨⟨h1, h2⟩, ?_, h4⟩
      intro hmem
      obtain ⟨e', he2, hpe⟩ := mem_privSet.1 hmem
      obtain ⟨hq, hee⟩ := idx_eq_priv hI he2 he h1 h2 hpe.symm
      rw [hee] at h0
      exact h0 hq
  unfold ebit
  rw [hF]
  by_cases hb : s.testBit (priv k S e.1 e.2) = true
  · have hm : modOf k S e.1 e.2 ∈ (Finset.Icc 1 (side k)).filter
        (fun q => s.testBit (idx k q (e.1 % q) (e.2 % q)) = true) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨m1, mA⟩, hb⟩
    rw [← Finset.card_erase_add_one hm, hb, decide_odd_succ]
    simp
  · have hm : modOf k S e.1 e.2 ∉ (Finset.Icc 1 (side k)).filter
        (fun q => s.testBit (idx k q (e.1 % q) (e.2 % q)) = true) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact fun h => hb h.2
    rw [Finset.erase_eq_of_notMem hm]
    simp only [Bool.not_eq_true] at hb
    rw [hb]
    simp

/- Reconstruction of the seed -/

lemma bool_key : ∀ b X T : Bool, b = xor T X → (xor b X = true ↔ T = true) := by
  decide

lemma sbit_eq {k : ℕ} {S : Finset ℕ} {s : ℕ} {b : Bool} (hI : IsolAll k S)
    (hc : (privSet k S).card = t k) (hs : s < 2 ^ L k)
    (hb : ∀ e ∈ pairs S, ebit k s e.1 e.2 = b) {i : ℕ} (hi : i < L k) :
    sbit k S b (Rof k S s) i = s.testBit i := by
  have hP : ∀ i ∈ privSet k S, i < L k := fun i hi => privSet_lt hI hi
  by_cases hp : i ∈ privSet k S
  · obtain ⟨e, he, rfl⟩ := mem_privSet.1 hp
    have hflip := ebit_flip hI hc hs he
    rw [hb e he] at hflip
    rw [Bool.eq_iff_iff, sbit_priv _ _ _ _ _ hp]
    constructor
    · rintro ⟨e', he', hpe, hx⟩
      have hee : e' = e := priv_inj hI he he' hpe
      rw [hee] at hx
      exact (bool_key _ _ _ hflip).1 hx
    · intro hT
      exact ⟨e, he, rfl, (bool_key _ _ _ hflip).2 hT⟩
  · rw [sbit_nonpriv _ _ _ _ _ hp]
    exact Rof_testBit k S s hP hc hi hp

/- Encoding the vertex set -/

lemma exists_code (k : ℕ) (hk : 1 ≤ k) (S : Finset ℕ) (hS : ∀ w ∈ S, w < 2 ^ k)
    (hcard : S.card = 12 * k) :
    ∃ c, c < 2 ^ (12 * k ^ 2) ∧ (Nat.digits (2 ^ k) c).toFinset = S := by
  have h2 : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
  obtain ⟨m, hm, hm0⟩ : ∃ m ∈ S, m ≠ 0 := by
    by_contra hcon
    have hsub : S ⊆ {0} := fun x hx => Finset.mem_singleton.2 (by
      by_contra hx0
      exact hcon ⟨x, hx, hx0⟩)
    have h3 := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h3
    omega
  have hl : ∀ x ∈ (S.erase m).toList ++ [m], x < 2 ^ k := by
    intro x hx
    simp only [List.mem_append, Finset.mem_toList, Finset.mem_erase, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact hS x hx.2
    · rw [hx]
      exact hS m hm
  have hlast : ∀ h : (S.erase m).toList ++ [m] ≠ [], ((S.erase m).toList ++ [m]).getLast h ≠ 0 := by
    intro h
    rw [List.getLast_concat]
    exact hm0
  have hlen : ((S.erase m).toList ++ [m]).length = 12 * k := by
    rw [List.length_append, Finset.length_toList, Finset.card_erase_of_mem hm, hcard]
    simp only [List.length_singleton]
    omega
  refine ⟨Nat.ofDigits (2 ^ k) ((S.erase m).toList ++ [m]), ?_, ?_⟩
  · have h3 := Nat.ofDigits_lt_base_pow_length h2 hl
    rw [hlen, ← pow_mul] at h3
    have h4 : k * (12 * k) = 12 * k ^ 2 := by ring
    rw [h4] at h3
    exact h3
  · rw [Nat.digits_ofDigits _ h2 _ hl hlast]
    ext x
    simp only [List.toFinset_append, Finset.toList_toFinset, List.toFinset_cons,
      List.toFinset_nil, Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
      Finset.notMem_empty, or_false]
    constructor
    · rintro (h | h)
      · exact h.2
      · rw [h]
        exact hm
    · intro hx
      by_cases hxm : x = m
      · exact Or.inr hxm
      · exact Or.inl ⟨hxm, hx⟩

/- The pivot: a monochromatic set of size 12k puts the seed in the range of cmp0 -/

theorem pivot
    (hN : ∀ n D : ℕ, 0 < D → D * (2 * n + 1) < 4 ^ n → ∃ q, 1 ≤ q ∧ q ≤ 2 * n ∧ ¬ q ∣ D)
    (k : ℕ) (hk : 1 ≤ k) (s : ℕ) (hs : s < 2 ^ L k) (S : Finset ℕ)
    (hS : ∀ w ∈ S, w < 2 ^ k) (hcard : S.card = 12 * k) (b : Bool)
    (hb : ∀ u ∈ S, ∀ v ∈ S, u < v → ebit k s u v = b) :
    ∃ x, x < 2 ^ (L k - side k) ∧ cmp0 (2 ^ k, x) = s := by
  have hI : IsolAll k S := fun u hu v hv =>
    exists_isol hN k S hS hcard u v (hS u hu) (hS v hv)
  have hc : (privSet k S).card = t k := by
    rw [privSet_card hI, pairs_card, hcard]
    rfl
  have hb' : ∀ e ∈ pairs S, ebit k s e.1 e.2 = b := fun e he =>
    hb _ (mem_pairs.1 he).1 _ (mem_pairs.1 he).2.1 (mem_pairs.1 he).2.2
  obtain ⟨c, hclt, hcS⟩ := exists_code k hk S hS hcard
  have hR := Rof_lt k S s
  have hbn : b.toNat ≤ 1 := Bool.toNat_le b
  refine ⟨Rof k S s + 2 ^ (L k - t k) * (b.toNat + 2 * c), ?_, ?_⟩
  · have h1 : b.toNat + 2 * c + 1 ≤ 2 ^ (12 * k ^ 2 + 1) := by
      rw [pow_succ]
      omega
    have h2 : Rof k S s + 2 ^ (L k - t k) * (b.toNat + 2 * c)
        < 2 ^ (L k - t k) * (b.toNat + 2 * c + 1) := by
      rw [Nat.mul_add_one]
      omega
    have h3 : 2 ^ (L k - t k) * (b.toNat + 2 * c + 1)
        ≤ 2 ^ (L k - t k) * 2 ^ (12 * k ^ 2 + 1) := Nat.mul_le_mul_left _ h1
    have h4 : 2 ^ (L k - t k) * 2 ^ (12 * k ^ 2 + 1) ≤ 2 ^ (L k - side k) := by
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by norm_num)
      have h5 := t_bound k hk
      have h6 := t_le_L k hk
      omega
    exact lt_of_lt_of_le h2 (h3.trans h4)
  · rw [cmp0_eq]
    have e1 : (Rof k S s + 2 ^ (L k - t k) * (b.toNat + 2 * c)) / 2 ^ (L k - t k)
        = b.toNat + 2 * c := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hR, zero_add]
    have e2 : (Rof k S s + 2 ^ (L k - t k) * (b.toNat + 2 * c)) % 2 ^ (L k - t k)
        = Rof k S s := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hR]
    have e3 : (b.toNat + 2 * c).testBit 0 = b := by
      rw [Nat.testBit_zero]
      cases b <;> simp
    have e4 : (b.toNat + 2 * c) / 2 = c := by
      omega
    simp only [e1, e2, e3, e4, hcS]
    have e5 : (fun i : Fin (L k) => sbit k S b (Rof k S s) i)
        = fun i : Fin (L k) => s.testBit i :=
      funext fun i => sbit_eq hI hc hs hb' i.2
    rw [e5, Nat.ofBits_testBit, Nat.mod_eq_of_lt hs]

/- The main statement -/

lemma adj_iff (k s : ℕ) (u v : Fin (2 ^ k)) (huv : (u : ℕ) < v) :
    (SimpleGraph.fromRel fun u v : Fin (2 ^ k) => dec0 (s, 2 ^ k, (u : ℕ), (v : ℕ))).Adj u v ↔
      ebit k s u v = true := by
  have hne : u ≠ v := fun h => by
    rw [h] at huv
    exact lt_irrefl _ huv
  have h2 : ¬ ((v : ℕ) < u) := by omega
  simp only [SimpleGraph.fromRel_adj, dec0_eq]
  simp [hne, huv, h2]

theorem combi (hN : ∀ n D : ℕ, 0 < D → D * (2 * n + 1) < 4 ^ n → ∃ q, 1 ≤ q ∧ q ≤ 2 * n ∧ ¬ q ∣ D)
    (k : ℕ) (hk : 1 ≤ k) (s : ℕ) (hs : s < 2 ^ L k)
    (hav : ∀ x : ℕ, x < 2 ^ (L k - side k) → cmp0 (2 ^ k, x) ≠ s) :
    NoHomogeneousSet
      (SimpleGraph.fromRel fun u v : Fin (2 ^ k) => dec0 (s, 2 ^ k, (u : ℕ), (v : ℕ))) (12 * k) := by
  have key : ∀ (S0 : Finset (Fin (2 ^ k))) (b : Bool), S0.card = 12 * k →
      (∀ u ∈ S0, ∀ v ∈ S0, (u : ℕ) < v → ebit k s u v = b) → False := by
    intro S0 b hcard hb
    obtain ⟨x, hx, hxs⟩ := pivot hN k hk s hs (S0.map Fin.valEmbedding)
      (by
        intro w hw
        obtain ⟨u, _, rfl⟩ := Finset.mem_map.1 hw
        exact u.2)
      (by rw [Finset.card_map, hcard]) b
      (by
        intro u hu v hv huv
        obtain ⟨u0, hu0, rfl⟩ := Finset.mem_map.1 hu
        obtain ⟨v0, hv0, rfl⟩ := Finset.mem_map.1 hv
        exact hb u0 hu0 v0 hv0 huv)
    exact hav x hx hxs
  unfold NoHomogeneousSet
  constructor
  · intro S0 hS0
    rw [SimpleGraph.isNClique_iff] at hS0
    refine key S0 true hS0.2 ?_
    intro u hu v hv huv
    have hne : u ≠ v := fun h => by
      rw [h] at huv
      exact lt_irrefl _ huv
    exact (adj_iff k s u v huv).1 (hS0.1 (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv) hne)
  · intro S0 hS0
    rw [SimpleGraph.isNClique_iff] at hS0
    refine key S0 false hS0.2 ?_
    intro u hu v hv huv
    have hne : u ≠ v := fun h => by
      rw [h] at huv
      exact lt_irrefl _ huv
    have h1 := hS0.1 (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv) hne
    rw [SimpleGraph.compl_adj] at h1
    have h3 := mt (adj_iff k s u v huv).2 h1.2
    simpa using h3

end Erdos78Avoid
end

-- ===== part: H2 =====
section
/-! Hypothesis H2 of the range avoidance split, reduced to two polynomial-time facts. -/
namespace Erdos78Avoid
open Filter ComplexityTheory Erdos78

/-- The combinatorial heart, with no hypotheses left: every seed outside the range of the
compression map gives a graph on 2^k vertices with no clique or independent set of size 12k. -/
theorem combi_full (k : ℕ) (hk : 1 ≤ k) (s : ℕ) (hs : s < 2 ^ L k)
    (hav : ∀ x : ℕ, x < 2 ^ (L k - side k) → cmp0 (2 ^ k, x) ≠ s) :
    NoHomogeneousSet
      (SimpleGraph.fromRel fun u v : Fin (2 ^ k) => dec0 (s, 2 ^ k, (u : ℕ), (v : ℕ))) (12 * k) :=
  combi Erdos78AvoidNT.exists_not_dvd k hk s hs hav

/-- H2 follows once the decoder and the compression map are shown to be polynomial time. -/
theorem H2_of_polyTime (hd : IsPolyTime dec0) (hc : IsPolyTime cmp0) :
    OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R2.H2 := by
  refine ⟨12, by norm_num, Polynomial.C 48 * Polynomial.X ^ 2 + 1, dec0, cmp0, hd, hc, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with k hk s hs hav
  have hside : (Polynomial.C 48 * Polynomial.X ^ 2 + 1 : Polynomial ℕ).eval k + 1 = side k := by
    simp [side]
  rw [hside] at hs hav
  have := combi_full k hk s hs hav
  have hceil : ⌈(12 : ℝ) * (k : ℝ)⌉₊ = 12 * k := by
    have : ((12 : ℝ) * (k : ℝ)) = ((12 * k : ℕ) : ℝ) := by push_cast; ring
    rw [this, Nat.ceil_natCast]
  rw [hceil]
  exact this

end Erdos78Avoid
end

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R2.H2 :=
  Erdos78Avoid.H2_of_polyTime Erdos78Arith.dec0_polyTime
    (Erdos78Cmp.cmp0_polyTime Erdos78Arith.arithFacts)
