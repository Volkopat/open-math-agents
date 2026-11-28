import OMAReductions.R_Erdos78_erdos_78_R1

namespace OMA.Proof_Erdos78_erdos_78_R1_H2

open Turing StateTransition ComplexityTheory Computability

private def stmtPushes {K : Type} {Γ : K → Type} {Λ σ : Type} :
    TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + stmtPushes q
  | .peek _ _ q => stmtPushes q
  | .pop _ _ q => stmtPushes q
  | .load _ q => stmtPushes q
  | .branch _ q1 q2 => max (stmtPushes q1) (stmtPushes q2)
  | .goto _ => 0
  | .halt => 0

private def totalLen {K : Type} [Fintype K] {Γ : K → Type} (S : ∀ k, List (Γ k)) : ℕ :=
  ∑ k : K, (S k).length

private lemma totalLen_update {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type}
    (S : ∀ k, List (Γ k)) (k : K) (l : List (Γ k)) :
    totalLen (Function.update S k l) + (S k).length = totalLen S + l.length := by
  unfold totalLen
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  conv_rhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have hsum : ∑ i ∈ Finset.univ.erase k, (Function.update S k l i).length =
      ∑ i ∈ Finset.univ.erase k, (S i).length := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [Function.update_self, hsum]
  omega

private lemma totalLen_stepAux_le {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type}
    {Λ σ : Type} (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    totalLen (TM2.stepAux q v S).stk ≤ totalLen S + stmtPushes q := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [TM2.stepAux, stmtPushes]
    have hupd := totalLen_update S k (f v :: S k)
    simp only [List.length_cons] at hupd
    have h1 := ih v (Function.update S k (f v :: S k))
    omega
  | peek k f q ih =>
    simp only [TM2.stepAux, stmtPushes]
    exact ih _ S
  | pop k f q ih =>
    simp only [TM2.stepAux, stmtPushes]
    have hupd := totalLen_update S k (S k).tail
    have htail : (S k).tail.length ≤ (S k).length := by cases S k <;> simp
    have h1 := ih (f v (S k).head?) (Function.update S k (S k).tail)
    omega
  | load f q ih =>
    simp only [TM2.stepAux, stmtPushes]
    exact ih _ S
  | branch f q1 q2 ih1 ih2 =>
    simp only [TM2.stepAux, stmtPushes]
    cases f v
    · simp only [cond_false]
      exact (ih2 v S).trans (Nat.add_le_add_left (le_max_right _ _) _)
    · simp only [cond_true]
      exact (ih1 v S).trans (Nat.add_le_add_left (le_max_left _ _) _)
  | goto f =>
    simp only [TM2.stepAux, stmtPushes, add_zero, le_refl]
  | halt =>
    simp only [TM2.stepAux, stmtPushes, add_zero, le_refl]

private def maxPushes (tm : FinTM2) : ℕ :=
  letI := tm.ΛFin
  Finset.univ.sup fun l : tm.Λ => stmtPushes (tm.m l)

private lemma totalLen_iterate_le (tm : FinTM2) (n : ℕ) (c c' : tm.Cfg)
    (h : (flip bind tm.step)^[n] (some c) = some c') :
    @totalLen tm.K tm.kFin tm.Γ c'.stk ≤ @totalLen tm.K tm.kFin tm.Γ c.stk + n * maxPushes tm := by
  letI := tm.kFin
  letI := tm.ΛFin
  induction n generalizing c' with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at h
    subst h
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hmid : (flip bind tm.step)^[n] (some c) with
    | none =>
      rw [hmid] at h
      change none = some c' at h
      cases h
    | some cmid =>
      rw [hmid] at h
      rcases cmid with ⟨l, v, S⟩
      cases l with
      | none =>
        change none = some c' at h
        cases h
      | some lbl =>
        change some (TM2.stepAux (tm.m lbl) v S) = some c' at h
        injection h with h
        subst h
        have h1 : totalLen S ≤ totalLen c.stk + n * maxPushes tm := ih ⟨some lbl, v, S⟩ hmid
        have h2 : totalLen (TM2.stepAux (tm.m lbl) v S).stk ≤
            totalLen S + stmtPushes (tm.m lbl) := totalLen_stepAux_le (tm.m lbl) v S
        have h3 : stmtPushes (tm.m lbl) ≤ maxPushes tm :=
          Finset.le_sup (f := fun l : tm.Λ => stmtPushes (tm.m l)) (Finset.mem_univ lbl)
        calc totalLen (TM2.stepAux (tm.m lbl) v S).stk
            ≤ totalLen S + stmtPushes (tm.m lbl) := h2
          _ ≤ totalLen c.stk + n * maxPushes tm + maxPushes tm := by omega
          _ = totalLen c.stk + (n + 1) * maxPushes tm := by ring

private lemma totalLen_initList (tm : FinTM2) (l : List (tm.Γ tm.k₀)) :
    @totalLen tm.K tm.kFin tm.Γ (initList tm l).stk = l.length := by
  letI := tm.kFin
  unfold totalLen initList
  rw [Finset.sum_eq_single tm.k₀]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h; exact absurd (Finset.mem_univ tm.k₀) h

private lemma totalLen_haltList (tm : FinTM2) (l : List (tm.Γ tm.k₁)) :
    @totalLen tm.K tm.kFin tm.Γ (haltList tm l).stk = l.length := by
  letI := tm.kFin
  unfold totalLen haltList
  rw [Finset.sum_eq_single tm.k₁]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h; exact absurd (Finset.mem_univ tm.k₁) h

private lemma poly_eval_mono (p : Polynomial ℕ) {a b : ℕ} (hab : a ≤ b) :
    p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i)

section CompTM

variable {α β γ αΓ βΓ γΓ : Type} [Fintype βΓ] [Inhabited βΓ]
  {eα : α → List αΓ} {eβ : β → List βΓ} {eγ : γ → List γΓ}
  {f : α → β} {g : β → γ}
  (h1 : TM2ComputableInPolyTime eα eβ f)
  (h2 : TM2ComputableInPolyTime eβ eγ g)

private abbrev CompK (tm1 tm2 : FinTM2) : Type := tm1.K ⊕ tm2.K ⊕ Unit

private def CompΓ (tm1 tm2 : FinTM2) (βΓ : Type) : CompK tm1 tm2 → Type
  | Sum.inl k => tm1.Γ k
  | Sum.inr (Sum.inl k) => tm2.Γ k
  | Sum.inr (Sum.inr ()) => βΓ

private abbrev CompΛ (tm1 tm2 : FinTM2) : Type := tm1.Λ ⊕ tm2.Λ ⊕ Bool

private abbrev Compσ (tm1 tm2 : FinTM2) (βΓ : Type) : Type := tm1.σ × tm2.σ × Option βΓ

private def liftStmt1 (tm1 tm2 : FinTM2) (βΓ : Type) :
    TM2.Stmt tm1.Γ tm1.Λ tm1.σ → TM2.Stmt (CompΓ tm1 tm2 βΓ) (CompΛ tm1 tm2) (Compσ tm1 tm2 βΓ)
  | .push k fn q => .push (Sum.inl k) (fun s => fn s.1) (liftStmt1 tm1 tm2 βΓ q)
  | .peek k fn q => .peek (Sum.inl k) (fun s o => (fn s.1 o, s.2)) (liftStmt1 tm1 tm2 βΓ q)
  | .pop k fn q => .pop (Sum.inl k) (fun s o => (fn s.1 o, s.2)) (liftStmt1 tm1 tm2 βΓ q)
  | .load fn q => .load (fun s => (fn s.1, s.2)) (liftStmt1 tm1 tm2 βΓ q)
  | .branch fn q1 q2 => .branch (fun s => fn s.1) (liftStmt1 tm1 tm2 βΓ q1) (liftStmt1 tm1 tm2 βΓ q2)
  | .goto fn => .goto (fun s => Sum.inl (fn s.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr false))

private def liftStmt2 (tm1 tm2 : FinTM2) (βΓ : Type) :
    TM2.Stmt tm2.Γ tm2.Λ tm2.σ → TM2.Stmt (CompΓ tm1 tm2 βΓ) (CompΛ tm1 tm2) (Compσ tm1 tm2 βΓ)
  | .push k fn q => .push (Sum.inr (Sum.inl k)) (fun s => fn s.2.1) (liftStmt2 tm1 tm2 βΓ q)
  | .peek k fn q => .peek (Sum.inr (Sum.inl k)) (fun s o => (s.1, fn s.2.1 o, s.2.2)) (liftStmt2 tm1 tm2 βΓ q)
  | .pop k fn q => .pop (Sum.inr (Sum.inl k)) (fun s o => (s.1, fn s.2.1 o, s.2.2)) (liftStmt2 tm1 tm2 βΓ q)
  | .load fn q => .load (fun s => (s.1, fn s.2.1, s.2.2)) (liftStmt2 tm1 tm2 βΓ q)
  | .branch fn q1 q2 => .branch (fun s => fn s.2.1) (liftStmt2 tm1 tm2 βΓ q1) (liftStmt2 tm1 tm2 βΓ q2)
  | .goto fn => .goto (fun s => Sum.inr (Sum.inl (fn s.2.1)))
  | .halt => .halt

private def copy1Stmt :
    TM2.Stmt (CompΓ h1.tm h2.tm βΓ) (CompΛ h1.tm h2.tm) (Compσ h1.tm h2.tm βΓ) :=
  .pop (Sum.inl h1.tm.k₁) (fun s o => (s.1, s.2.1, o.map h1.outputAlphabet))
    (.branch (fun s => s.2.2.isSome)
      (.push (Sum.inr (Sum.inr ())) (fun s => s.2.2.getD default)
        (.load (fun s => (s.1, s.2.1, none))
          (.goto (fun _ => Sum.inr (Sum.inr false)))))
      (.goto (fun _ => Sum.inr (Sum.inr true))))

private def copy2Stmt :
    TM2.Stmt (CompΓ h1.tm h2.tm βΓ) (CompΛ h1.tm h2.tm) (Compσ h1.tm h2.tm βΓ) :=
  .pop (Sum.inr (Sum.inr ())) (fun s o => (s.1, s.2.1, o))
    (.branch (fun s => s.2.2.isSome)
      (.push (Sum.inr (Sum.inl h2.tm.k₀)) (fun s => h2.inputAlphabet.symm (s.2.2.getD default))
        (.load (fun s => (s.1, s.2.1, none))
          (.goto (fun _ => Sum.inr (Sum.inr true)))))
      (.goto (fun _ => Sum.inr (Sum.inl h2.tm.main))))

private def compFinTM2 : FinTM2 :=
  { K := CompK h1.tm h2.tm
    kDecidableEq := inferInstance
    kFin := @instFintypeSum _ _ h1.tm.kFin (@instFintypeSum _ _ h2.tm.kFin inferInstance)
    k₀ := Sum.inl h1.tm.k₀
    k₁ := Sum.inr (Sum.inl h2.tm.k₁)
    Γ := CompΓ h1.tm h2.tm βΓ
    Λ := CompΛ h1.tm h2.tm
    main := Sum.inl h1.tm.main
    ΛFin := @instFintypeSum _ _ h1.tm.ΛFin (@instFintypeSum _ _ h2.tm.ΛFin inferInstance)
    σ := Compσ h1.tm h2.tm βΓ
    initialState := (h1.tm.initialState, h2.tm.initialState, none)
    σFin := @instFintypeProd _ _ h1.tm.σFin (@instFintypeProd _ _ h2.tm.σFin inferInstance)
    Γk₀Fin := h1.tm.Γk₀Fin
    m := fun
      | Sum.inl l => liftStmt1 h1.tm h2.tm βΓ (h1.tm.m l)
      | Sum.inr (Sum.inl l) => liftStmt2 h1.tm h2.tm βΓ (h2.tm.m l)
      | Sum.inr (Sum.inr false) => copy1Stmt h1 h2
      | Sum.inr (Sum.inr true) => copy2Stmt h1 h2 }

private def embedStk1 (S : ∀ k, List (h1.tm.Γ k)) :
    ∀ k : CompK h1.tm h2.tm, List (CompΓ h1.tm h2.tm βΓ k)
  | Sum.inl k => S k
  | Sum.inr (Sum.inl _) => []
  | Sum.inr (Sum.inr ()) => []

private def embed1 (c : h1.tm.Cfg) : (compFinTM2 h1 h2).Cfg where
  l := match c.l with
    | some l => some (Sum.inl l)
    | none => some (Sum.inr (Sum.inr false))
  var := (c.var, h2.tm.initialState, none)
  stk := embedStk1 h1 h2 c.stk

private def embedStk2 (S : ∀ k, List (h2.tm.Γ k)) :
    ∀ k : CompK h1.tm h2.tm, List (CompΓ h1.tm h2.tm βΓ k)
  | Sum.inl _ => []
  | Sum.inr (Sum.inl k) => S k
  | Sum.inr (Sum.inr ()) => []

private def embed2 (c : h2.tm.Cfg) : (compFinTM2 h1 h2).Cfg where
  l := c.l.map (Sum.inr ∘ Sum.inl)
  var := (h1.tm.initialState, c.var, none)
  stk := embedStk2 h1 h2 c.stk

private lemma embedStk1_update (S : ∀ k, List (h1.tm.Γ k)) (k : h1.tm.K)
    (l : List (h1.tm.Γ k)) :
    Function.update (embedStk1 h1 h2 S) (Sum.inl k) l =
      embedStk1 h1 h2 (Function.update S k l) := by
  funext x
  rcases x with k' | k' | ⟨⟩
  · by_cases hk : k' = k
    · subst hk; simp [Function.update, embedStk1]; rfl
    · have hne : (Sum.inl k' : CompK h1.tm h2.tm) ≠ Sum.inl k := fun h => hk (Sum.inl.inj h)
      simp [Function.update, embedStk1, hk, hne]; rfl
  · have hne : (Sum.inr (Sum.inl k') : CompK h1.tm h2.tm) ≠ Sum.inl k := by intro h; cases h
    simp [Function.update, embedStk1, hne]
  · have hne : (Sum.inr (Sum.inr ()) : CompK h1.tm h2.tm) ≠ Sum.inl k := by intro h; cases h
    simp [Function.update, embedStk1, hne]

private lemma embedStk2_update (S : ∀ k, List (h2.tm.Γ k)) (k : h2.tm.K)
    (l : List (h2.tm.Γ k)) :
    Function.update (embedStk2 h1 h2 S) (Sum.inr (Sum.inl k)) l =
      embedStk2 h1 h2 (Function.update S k l) := by
  funext x
  rcases x with k' | k' | ⟨⟩
  · have hne : (Sum.inl k' : CompK h1.tm h2.tm) ≠ Sum.inr (Sum.inl k) := by intro h; cases h
    simp [Function.update, embedStk2, hne]
  · by_cases hk : k' = k
    · subst hk; simp [Function.update, embedStk2]; rfl
    · have hne : (Sum.inr (Sum.inl k') : CompK h1.tm h2.tm) ≠ Sum.inr (Sum.inl k) := fun h =>
        hk (Sum.inl.inj (Sum.inr.inj h))
      simp [Function.update, embedStk2, hk, hne]; rfl
  · have hne : (Sum.inr (Sum.inr ()) : CompK h1.tm h2.tm) ≠ Sum.inr (Sum.inl k) := by
      intro h; cases h
    simp [Function.update, embedStk2, hne]

private lemma stepAux_liftStmt1 (q : TM2.Stmt h1.tm.Γ h1.tm.Λ h1.tm.σ)
    (v : h1.tm.σ) (S : ∀ k, List (h1.tm.Γ k)) :
    TM2.stepAux (liftStmt1 h1.tm h2.tm βΓ q) (v, h2.tm.initialState, none) (embedStk1 h1 h2 S) =
      embed1 h1 h2 (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k fn q ih =>
    simp only [liftStmt1, TM2.stepAux]
    rw [← ih v (Function.update S k (fn v :: S k))]
    exact congrArg (TM2.stepAux (liftStmt1 h1.tm h2.tm βΓ q) (v, h2.tm.initialState, none))
      (embedStk1_update h1 h2 S k (fn v :: S k))
  | peek k fn q ih =>
    simp only [liftStmt1, TM2.stepAux]
    exact ih (fn v (S k).head?) S
  | pop k fn q ih =>
    simp only [liftStmt1, TM2.stepAux]
    rw [← ih (fn v (S k).head?) (Function.update S k (S k).tail)]
    exact congrArg (TM2.stepAux (liftStmt1 h1.tm h2.tm βΓ q)
      (fn v (S k).head?, h2.tm.initialState, none))
      (embedStk1_update h1 h2 S k (S k).tail)
  | load fn q ih =>
    simp only [liftStmt1, TM2.stepAux]
    exact ih (fn v) S
  | branch fn q1 q2 ih1 ih2 =>
    simp only [liftStmt1, TM2.stepAux]
    cases fn v
    · simp only [cond_false]; exact ih2 v S
    · simp only [cond_true]; exact ih1 v S
  | goto fn =>
    rfl
  | halt =>
    rfl

private lemma stepAux_liftStmt2 (q : TM2.Stmt h2.tm.Γ h2.tm.Λ h2.tm.σ)
    (v : h2.tm.σ) (S : ∀ k, List (h2.tm.Γ k)) :
    TM2.stepAux (liftStmt2 h1.tm h2.tm βΓ q) (h1.tm.initialState, v, none) (embedStk2 h1 h2 S) =
      embed2 h1 h2 (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k fn q ih =>
    simp only [liftStmt2, TM2.stepAux]
    rw [← ih v (Function.update S k (fn v :: S k))]
    exact congrArg (TM2.stepAux (liftStmt2 h1.tm h2.tm βΓ q) (h1.tm.initialState, v, none))
      (embedStk2_update h1 h2 S k (fn v :: S k))
  | peek k fn q ih =>
    simp only [liftStmt2, TM2.stepAux]
    exact ih (fn v (S k).head?) S
  | pop k fn q ih =>
    simp only [liftStmt2, TM2.stepAux]
    rw [← ih (fn v (S k).head?) (Function.update S k (S k).tail)]
    exact congrArg (TM2.stepAux (liftStmt2 h1.tm h2.tm βΓ q)
      (h1.tm.initialState, fn v (S k).head?, none))
      (embedStk2_update h1 h2 S k (S k).tail)
  | load fn q ih =>
    simp only [liftStmt2, TM2.stepAux]
    exact ih (fn v) S
  | branch fn q1 q2 ih1 ih2 =>
    simp only [liftStmt2, TM2.stepAux]
    cases fn v
    · simp only [cond_false]; exact ih2 v S
    · simp only [cond_true]; exact ih1 v S
  | goto fn =>
    rfl
  | halt =>
    rfl

private lemma sim1_iterate (n : ℕ) (c c' : h1.tm.Cfg)
    (h : (flip bind h1.tm.step)^[n] (some c) = some c') :
    (flip bind (compFinTM2 h1 h2).step)^[n] (some (embed1 h1 h2 c)) = some (embed1 h1 h2 c') := by
  induction n generalizing c' with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at h
    subst h
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h ⊢
    cases hmid : (flip bind h1.tm.step)^[n] (some c) with
    | none =>
      rw [hmid] at h
      change none = some c' at h
      cases h
    | some cmid =>
      rw [hmid] at h
      rw [ih cmid hmid]
      rcases cmid with ⟨l, v, S⟩
      cases l with
      | none =>
        change none = some c' at h
        cases h
      | some lbl =>
        change some (TM2.stepAux (h1.tm.m lbl) v S) = some c' at h
        injection h with h
        subst h
        change some (TM2.stepAux (liftStmt1 h1.tm h2.tm βΓ (h1.tm.m lbl))
          (v, h2.tm.initialState, none) (embedStk1 h1 h2 S)) = _
        exact congrArg some (stepAux_liftStmt1 h1 h2 (h1.tm.m lbl) v S)

private lemma sim2_iterate (n : ℕ) (c c' : h2.tm.Cfg)
    (h : (flip bind h2.tm.step)^[n] (some c) = some c') :
    (flip bind (compFinTM2 h1 h2).step)^[n] (some (embed2 h1 h2 c)) = some (embed2 h1 h2 c') := by
  induction n generalizing c' with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at h
    subst h
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h ⊢
    cases hmid : (flip bind h2.tm.step)^[n] (some c) with
    | none =>
      rw [hmid] at h
      change none = some c' at h
      cases h
    | some cmid =>
      rw [hmid] at h
      rw [ih cmid hmid]
      rcases cmid with ⟨l, v, S⟩
      cases l with
      | none =>
        change none = some c' at h
        cases h
      | some lbl =>
        change some (TM2.stepAux (h2.tm.m lbl) v S) = some c' at h
        injection h with h
        subst h
        change some (TM2.stepAux (liftStmt2 h1.tm h2.tm βΓ (h2.tm.m lbl))
          (h1.tm.initialState, v, none) (embedStk2 h1 h2 S)) = _
        exact congrArg some (stepAux_liftStmt2 h1 h2 (h2.tm.m lbl) v S)

private def copyStk (l1 : List (h1.tm.Γ h1.tm.k₁)) (ltmp : List βΓ)
    (l2 : List (h2.tm.Γ h2.tm.k₀)) :
    ∀ k : CompK h1.tm h2.tm, List (CompΓ h1.tm h2.tm βΓ k)
  | Sum.inl k => if hk : k = h1.tm.k₁ then hk ▸ l1 else []
  | Sum.inr (Sum.inl k) => if hk : k = h2.tm.k₀ then hk ▸ l2 else []
  | Sum.inr (Sum.inr ()) => ltmp

private lemma copy1_run (xs : List (h1.tm.Γ h1.tm.k₁)) (ys : List βΓ) :
    (flip bind (compFinTM2 h1 h2).step)^[xs.length + 1]
      (some ⟨some (Sum.inr (Sum.inr false)), (h1.tm.initialState, h2.tm.initialState, none),
        copyStk h1 h2 xs ys []⟩) =
      some ⟨some (Sum.inr (Sum.inr true)), (h1.tm.initialState, h2.tm.initialState, none),
        copyStk h1 h2 [] ((xs.map h1.outputAlphabet).reverse ++ ys) []⟩ := by
  induction xs generalizing ys with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one]
    dsimp only [flip, Bind.bind, Option.bind]
    simp only [FinTM2.step, TM2.step, compFinTM2, copy1Stmt, TM2.stepAux, copyStk, ↓reduceDIte]
    dsimp only [List.head?, Option.map, Option.isSome, Option.getD, cond, TM2.stepAux]
    simp only [List.map_nil, List.reverse_nil, List.nil_append]
    congr 2
    funext k
    rcases k with k | k | ⟨⟩
    · by_cases hk : k = h1.tm.k₁
      · subst hk; simp [Function.update, copyStk]; rfl
      · have hne : (Sum.inl k : CompK h1.tm h2.tm) ≠ Sum.inl h1.tm.k₁ := fun h => hk (Sum.inl.inj h)
        simp [Function.update, copyStk, hk, hne]
    · have hne : (Sum.inr (Sum.inl k) : CompK h1.tm h2.tm) ≠ Sum.inl h1.tm.k₁ := by
        intro h; cases h
      simp [Function.update, copyStk, hne]
    · have hne : (Sum.inr (Sum.inr ()) : CompK h1.tm h2.tm) ≠ Sum.inl h1.tm.k₁ := by
        intro h; cases h
      simp [Function.update, copyStk, hne]; rfl
  | cons x xs ih =>
    rw [List.length_cons, show xs.length + 1 + 1 = (xs.length + 1) + 1 by omega,
      Function.iterate_succ_apply]
    have hstep : (compFinTM2 h1 h2).step
        ⟨some (Sum.inr (Sum.inr false)), (h1.tm.initialState, h2.tm.initialState, none),
          copyStk h1 h2 (x :: xs) ys []⟩ =
        some ⟨some (Sum.inr (Sum.inr false)), (h1.tm.initialState, h2.tm.initialState, none),
          copyStk h1 h2 xs (h1.outputAlphabet x :: ys) []⟩ := by
      simp only [FinTM2.step, TM2.step, compFinTM2, copy1Stmt, TM2.stepAux, copyStk, ↓reduceDIte]
      dsimp only [List.head?, Option.map, Option.isSome, Option.getD, cond, TM2.stepAux]
      congr 2
      funext k
      rcases k with k | k | ⟨⟩
      · have hne1 : (Sum.inl k : CompK h1.tm h2.tm) ≠ Sum.inr (Sum.inr ()) := by intro h; cases h
        by_cases hk : k = h1.tm.k₁
        · subst hk; simp [Function.update, copyStk, hne1]; rfl
        · have hne2 : (Sum.inl k : CompK h1.tm h2.tm) ≠ Sum.inl h1.tm.k₁ := fun h =>
            hk (Sum.inl.inj h)
          simp [Function.update, copyStk, hne1, hne2, hk]
      · have hne1 : (Sum.inr (Sum.inl k) : CompK h1.tm h2.tm) ≠ Sum.inr (Sum.inr ()) := by
          intro h; cases h
        have hne2 : (Sum.inr (Sum.inl k) : CompK h1.tm h2.tm) ≠ Sum.inl h1.tm.k₁ := by
          intro h; cases h
        simp [Function.update, copyStk, hne1, hne2]
      · have hne2 : (Sum.inr (Sum.inr ()) : CompK h1.tm h2.tm) ≠ Sum.inl h1.tm.k₁ := by
          intro h; cases h
        simp [Function.update, copyStk, hne2]; rfl
    dsimp only [flip, Bind.bind, Option.bind]
    rw [hstep, List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    exact ih (h1.outputAlphabet x :: ys)

private lemma copy2_run (xs : List βΓ) (ys : List (h2.tm.Γ h2.tm.k₀)) :
    (flip bind (compFinTM2 h1 h2).step)^[xs.length + 1]
      (some ⟨some (Sum.inr (Sum.inr true)), (h1.tm.initialState, h2.tm.initialState, none),
        copyStk h1 h2 [] xs ys⟩) =
      some ⟨some (Sum.inr (Sum.inl h2.tm.main)), (h1.tm.initialState, h2.tm.initialState, none),
        copyStk h1 h2 [] [] ((xs.map h2.inputAlphabet.symm).reverse ++ ys)⟩ := by
  induction xs generalizing ys with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one]
    dsimp only [flip, Bind.bind, Option.bind]
    simp only [FinTM2.step, TM2.step, compFinTM2, copy2Stmt, TM2.stepAux, copyStk, ↓reduceDIte]
    dsimp only [List.head?, Option.map, Option.isSome, Option.getD, cond, TM2.stepAux]
    simp only [List.map_nil, List.reverse_nil, List.nil_append]
    congr 2
    funext k
    rcases k with k | k | ⟨⟩
    · have hne : (Sum.inl k : CompK h1.tm h2.tm) ≠ Sum.inr (Sum.inr ()) := by intro h; cases h
      simp [Function.update, copyStk, hne]
    · have hne : (Sum.inr (Sum.inl k) : CompK h1.tm h2.tm) ≠ Sum.inr (Sum.inr ()) := by
        intro h; cases h
      simp [Function.update, copyStk, hne]
    · simp [Function.update, copyStk]; rfl
  | cons x xs ih =>
    rw [List.length_cons, show xs.length + 1 + 1 = (xs.length + 1) + 1 by omega,
      Function.iterate_succ_apply]
    have hstep : (compFinTM2 h1 h2).step
        ⟨some (Sum.inr (Sum.inr true)), (h1.tm.initialState, h2.tm.initialState, none),
          copyStk h1 h2 [] (x :: xs) ys⟩ =
        some ⟨some (Sum.inr (Sum.inr true)), (h1.tm.initialState, h2.tm.initialState, none),
          copyStk h1 h2 [] xs (h2.inputAlphabet.symm x :: ys)⟩ := by
      simp only [FinTM2.step, TM2.step, compFinTM2, copy2Stmt, TM2.stepAux, copyStk, ↓reduceDIte]
      dsimp only [List.head?, Option.map, Option.isSome, Option.getD, cond, TM2.stepAux]
      congr 2
      funext k
      rcases k with k | k | ⟨⟩
      · have hne1 : (Sum.inl k : CompK h1.tm h2.tm) ≠ Sum.inr (Sum.inl h2.tm.k₀) := by
          intro h; cases h
        have hne2 : (Sum.inl k : CompK h1.tm h2.tm) ≠ Sum.inr (Sum.inr ()) := by
          intro h; cases h
        simp [Function.update, copyStk, hne1, hne2]
      · have hne2 : (Sum.inr (Sum.inl k) : CompK h1.tm h2.tm) ≠ Sum.inr (Sum.inr ()) := by
          intro h; cases h
        by_cases hk : k = h2.tm.k₀
        · subst hk; simp [Function.update, copyStk, hne2]; rfl
        · have hne1 : (Sum.inr (Sum.inl k) : CompK h1.tm h2.tm) ≠ Sum.inr (Sum.inl h2.tm.k₀) :=
            fun h => hk (Sum.inl.inj (Sum.inr.inj h))
          simp [Function.update, copyStk, hne1, hne2, hk]
      · have hne1 : (Sum.inr (Sum.inr ()) : CompK h1.tm h2.tm) ≠ Sum.inr (Sum.inl h2.tm.k₀) := by
          intro h; cases h
        simp [Function.update, copyStk, hne1]; rfl
    dsimp only [flip, Bind.bind, Option.bind]
    rw [hstep, List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    exact ih (h2.inputAlphabet.symm x :: ys)

private lemma embed1_initList (l : List (h1.tm.Γ h1.tm.k₀)) :
    embed1 h1 h2 (initList h1.tm l) = initList (compFinTM2 h1 h2) l := by
  simp only [embed1, initList, compFinTM2]
  congr 1
  funext k
  rcases k with k | k | ⟨⟩
  · by_cases hk : k = h1.tm.k₀
    · subst hk; simp [embedStk1]; rfl
    · have hne : (Sum.inl k : CompK h1.tm h2.tm) ≠ Sum.inl h1.tm.k₀ := fun h => hk (Sum.inl.inj h)
      simp [embedStk1, hk, hne]; rfl
  · have hne : (Sum.inr (Sum.inl k) : CompK h1.tm h2.tm) ≠ Sum.inl h1.tm.k₀ := by
      intro h; cases h
    simp [embedStk1, hne]
  · have hne : (Sum.inr (Sum.inr ()) : CompK h1.tm h2.tm) ≠ Sum.inl h1.tm.k₀ := by
      intro h; cases h
    simp [embedStk1, hne]

private lemma embed1_haltList (l : List (h1.tm.Γ h1.tm.k₁)) :
    embed1 h1 h2 (haltList h1.tm l) =
      ⟨some (Sum.inr (Sum.inr false)), (h1.tm.initialState, h2.tm.initialState, none),
        copyStk h1 h2 l [] []⟩ := by
  simp only [embed1, haltList]
  congr 1
  funext k
  rcases k with k | k | ⟨⟩
  · by_cases hk : k = h1.tm.k₁
    · subst hk; simp [embedStk1, copyStk]; rfl
    · simp [embedStk1, copyStk, hk]; rfl
  · by_cases hk : k = h2.tm.k₀
    · subst hk; simp [embedStk1, copyStk]; rfl
    · simp [embedStk1, copyStk, hk]
  · rfl

private lemma copyStk_eq_embed2_init (l : List (h2.tm.Γ h2.tm.k₀)) :
    (⟨some (Sum.inr (Sum.inl h2.tm.main)), (h1.tm.initialState, h2.tm.initialState, none),
        copyStk h1 h2 [] [] l⟩ : (compFinTM2 h1 h2).Cfg) =
      embed2 h1 h2 (initList h2.tm l) := by
  simp only [embed2, initList]
  congr 1
  funext k
  rcases k with k | k | ⟨⟩
  · by_cases hk : k = h1.tm.k₁
    · subst hk; simp [embedStk2, copyStk]; rfl
    · simp [embedStk2, copyStk, hk]
  · by_cases hk : k = h2.tm.k₀
    · subst hk; simp [embedStk2, copyStk]; rfl
    · simp [embedStk2, copyStk, hk]; rfl
  · rfl

private lemma embed2_haltList (l : List (h2.tm.Γ h2.tm.k₁)) :
    embed2 h1 h2 (haltList h2.tm l) = haltList (compFinTM2 h1 h2) l := by
  simp only [embed2, haltList, compFinTM2, Option.map_none]
  congr 1
  funext k
  rcases k with k | k | ⟨⟩
  · have hne : (Sum.inl k : CompK h1.tm h2.tm) ≠ Sum.inr (Sum.inl h2.tm.k₁) := by
      intro h; cases h
    simp [embedStk2, hne]
  · by_cases hk : k = h2.tm.k₁
    · subst hk; simp [embedStk2]; rfl
    · have hne : (Sum.inr (Sum.inl k) : CompK h1.tm h2.tm) ≠ Sum.inr (Sum.inl h2.tm.k₁) :=
        fun h => hk (Sum.inl.inj (Sum.inr.inj h))
      simp [embedStk2, hk, hne]; rfl
  · have hne : (Sum.inr (Sum.inr ()) : CompK h1.tm h2.tm) ≠ Sum.inr (Sum.inl h2.tm.k₁) := by
      intro h; cases h
    simp [embedStk2, hne]

private noncomputable def tm2Comp : TM2ComputableInPolyTime eα eγ (g ∘ f) :=
  let P : Polynomial ℕ := Polynomial.X + Polynomial.C (maxPushes h1.tm) * h1.time
  { tm := compFinTM2 h1 h2
    inputAlphabet := h1.inputAlphabet
    outputAlphabet := h2.outputAlphabet
    time := h1.time + Polynomial.C 2 * (P + 1) + h2.time.comp P
    outputsFun := fun a => by
      have ho1 := h1.outputsFun a
      have ho2 := h2.outputsFun (f a)
      let inp1 := (eα a).map h1.inputAlphabet.invFun
      let out1 := (eβ (f a)).map h1.outputAlphabet.invFun
      let inp2 := (eβ (f a)).map h2.inputAlphabet.invFun
      let out2 := (eγ (g (f a))).map h2.outputAlphabet.invFun
      have hlen_out1 : out1.length ≤ P.eval (eα a).length := by
        have htot := totalLen_iterate_le h1.tm ho1.steps (initList h1.tm inp1) (haltList h1.tm out1)
          ho1.evals_in_steps
        rw [totalLen_initList, totalLen_haltList] at htot
        have hinp : inp1.length = (eα a).length := List.length_map _
        have hsteps : ho1.steps ≤ h1.time.eval (eα a).length := ho1.steps_le_m
        have hPeval : P.eval (eα a).length =
            (eα a).length + maxPushes h1.tm * h1.time.eval (eα a).length := by
          simp [P]
        rw [hPeval]
        calc out1.length ≤ inp1.length + ho1.steps * maxPushes h1.tm := htot
          _ = (eα a).length + maxPushes h1.tm * ho1.steps := by rw [hinp, mul_comm]
          _ ≤ (eα a).length + maxPushes h1.tm * h1.time.eval (eα a).length :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ hsteps) _
      have heval1 : (flip bind (compFinTM2 h1 h2).step)^[ho1.steps]
          (some (initList (compFinTM2 h1 h2) inp1)) =
          some ⟨some (Sum.inr (Sum.inr false)), (h1.tm.initialState, h2.tm.initialState, none),
            copyStk h1 h2 out1 [] []⟩ := by
        rw [← embed1_initList h1 h2 inp1, ← embed1_haltList h1 h2 out1]
        exact sim1_iterate h1 h2 ho1.steps (initList h1.tm inp1) (haltList h1.tm out1)
          ho1.evals_in_steps
      have hrev1 : (out1.map h1.outputAlphabet).reverse ++ [] = (eβ (f a)).reverse := by
        simp only [out1, List.map_map, List.append_nil]
        have : (h1.outputAlphabet ∘ h1.outputAlphabet.invFun) = id := by
          funext x; exact h1.outputAlphabet.apply_symm_apply x
        simp [this]
      have heval2 : (flip bind (compFinTM2 h1 h2).step)^[out1.length + 1]
          (some ⟨some (Sum.inr (Sum.inr false)), (h1.tm.initialState, h2.tm.initialState, none),
            copyStk h1 h2 out1 [] []⟩) =
          some ⟨some (Sum.inr (Sum.inr true)), (h1.tm.initialState, h2.tm.initialState, none),
            copyStk h1 h2 [] (eβ (f a)).reverse []⟩ := by
        rw [← hrev1]
        exact copy1_run h1 h2 out1 []
      have hrev2 : ((eβ (f a)).reverse.map h2.inputAlphabet.symm).reverse ++ [] = inp2 := by
        simp only [List.append_nil, List.map_reverse, List.reverse_reverse]
        rfl
      have heval3 : (flip bind (compFinTM2 h1 h2).step)^[(eβ (f a)).reverse.length + 1]
          (some ⟨some (Sum.inr (Sum.inr true)), (h1.tm.initialState, h2.tm.initialState, none),
            copyStk h1 h2 [] (eβ (f a)).reverse []⟩) =
          some (embed2 h1 h2 (initList h2.tm inp2)) := by
        rw [← copyStk_eq_embed2_init h1 h2 inp2, ← hrev2]
        exact copy2_run h1 h2 (eβ (f a)).reverse []
      have heval4 : (flip bind (compFinTM2 h1 h2).step)^[ho2.steps]
          (some (embed2 h1 h2 (initList h2.tm inp2))) =
          some (haltList (compFinTM2 h1 h2) out2) := by
        rw [← embed2_haltList h1 h2 out2]
        exact sim2_iterate h1 h2 ho2.steps (initList h2.tm inp2) (haltList h2.tm out2)
          ho2.evals_in_steps
      refine ⟨⟨ho2.steps + ((eβ (f a)).reverse.length + 1) + (out1.length + 1) + ho1.steps, ?_⟩, ?_⟩
      · change (flip bind (compFinTM2 h1 h2).step)^[ho2.steps + ((eβ (f a)).reverse.length + 1) +
            (out1.length + 1) + ho1.steps] (some (initList (compFinTM2 h1 h2) inp1)) =
            some (haltList (compFinTM2 h1 h2) out2)
        rw [Function.iterate_add_apply, heval1, Function.iterate_add_apply, heval2,
          Function.iterate_add_apply, heval3, heval4]
      · have hlen_rev : (eβ (f a)).reverse.length = out1.length := by
          simp [out1]
        have hlen_eq : (eβ (f a)).length = out1.length := by
          simp [out1]
        have h2bound : ho2.steps ≤ (h2.time.comp P).eval (eα a).length := by
          rw [Polynomial.eval_comp]
          exact ho2.steps_le_m.trans (poly_eval_mono h2.time (hlen_eq ▸ hlen_out1))
        have htime_eval : (h1.time + Polynomial.C 2 * (P + 1) + h2.time.comp P).eval (eα a).length =
            h1.time.eval (eα a).length + 2 * (P.eval (eα a).length + 1) +
              (h2.time.comp P).eval (eα a).length := by
          simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one]
        dsimp only
        rw [htime_eval, hlen_rev]
        have h1bound : ho1.steps ≤ h1.time.eval (eα a).length := ho1.steps_le_m
        omega }

end CompTM

end OMA.Proof_Erdos78_erdos_78_R1_H2

theorem OMA.solution : OMA.R_Erdos78_erdos_78_R1.H2 := by
  intro f g ⟨hf⟩ ⟨hg⟩
  exact ⟨OMA.Proof_Erdos78_erdos_78_R1_H2.tm2Comp hf hg⟩
