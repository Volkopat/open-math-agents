import OMAStatements.S_wp_unique_games_conjecture

-- Reduction wp-unique-games-conjecture.R1 of Unique games conjecture
-- Credit: @hadijannat
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Reduction of the Unique Games Conjecture to 3-Coloring NP-hardness and 3-Coloring-to-UGC

This reduction proves general sequential composition for `OMA.S_wp_unique_games_conjecture.PolyTime`
(`TM2ComputableInPolyTime` with finite stack alphabets) inside `main`, including a constructive
output-length growth bound, and decomposes the Unique Games Conjecture into two steps:

* `H1` (known step): every language in `InNP` reduces in `PolyTime` to 3-Coloring of
  finite graphs encoded as `n * n` adjacency-matrix bitstrings.
* `H2` (core step): 3-Coloring reduces in `PolyTime` to `(1 - δ, ε)`-Gap Unique Games with
  `k` colors for all sufficiently small `ε, δ > 0`.
-/

namespace OMA.R_wp_unique_games_conjecture_R1

/-- Cook-Levin / Karp NP-hardness of 3-Coloring on `n * n` adjacency-matrix bitstrings. -/
def H1 : Prop :=
  ∀ L : List Bool → Prop, OMA.S_wp_unique_games_conjecture.InNP L →
    ∃ f : List Bool → List Bool,
      OMA.S_wp_unique_games_conjecture.PolyTime id id f ∧
      ∀ x, L x ↔ ∃ (n : ℕ) (c : Fin n → Fin 3),
        (f x).length = n * n ∧
        ∀ i j : Fin n, (f x).getD (i.val * n + j.val) false = true → c i ≠ c j

/-- Polynomial-time gap reduction from 3-Coloring to `(1 - δ, ε)`-Gap Unique Games. -/
def H2 : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < ε₀ →
      ∃ (k : ℕ) (g : List Bool → OMA.S_wp_unique_games_conjecture.Instance k),
        OMA.S_wp_unique_games_conjecture.PolyTime id
          OMA.S_wp_unique_games_conjecture.Instance.bits g ∧
        ∀ y,
          ((∃ (n : ℕ) (c : Fin n → Fin 3),
              y.length = n * n ∧
              ∀ i j : Fin n, y.getD (i.val * n + j.val) false = true → c i ≠ c j) →
            ∃ a, 1 - δ ≤ (g y).fraction a) ∧
          ((¬ ∃ (n : ℕ) (c : Fin n → Fin 3),
              y.length = n * n ∧
              ∀ i j : Fin n, y.getD (i.val * n + j.val) false = true → c i ≠ c j) →
            ∀ a, (g y).fraction a ≤ ε)

open Turing OMA.S_wp_unique_games_conjecture

lemma rIn_single {σ : Type} {f : σ → Option σ} {a b : σ} (h : f a = some b) :
    ∃ n ≤ 1, (flip bind f)^[n] (some a) = some b :=
  ⟨1, le_rfl, h⟩

lemma rIn_trans {σ : Type} {f : σ → Option σ} {a b : σ} {c : Option σ} {m₁ m₂ : ℕ}
    (h₁ : ∃ n ≤ m₁, (flip bind f)^[n] (some a) = some b)
    (h₂ : ∃ n ≤ m₂, (flip bind f)^[n] (some b) = c) :
    ∃ n ≤ m₁ + m₂, (flip bind f)^[n] (some a) = c := by
  obtain ⟨n₁, hn₁, e₁⟩ := h₁
  obtain ⟨n₂, hn₂, e₂⟩ := h₂
  refine ⟨n₂ + n₁, by omega, ?_⟩
  rw [Function.iterate_add_apply, e₁, e₂]

lemma rIn_mono {σ : Type} {f : σ → Option σ} {a : σ} {b : Option σ} {m m' : ℕ}
    (h : ∃ n ≤ m, (flip bind f)^[n] (some a) = b) (hm : m ≤ m') :
    ∃ n ≤ m', (flip bind f)^[n] (some a) = b := by
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
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

/-- Sequential composition of polynomial-time `FinTM2` computations with finite stacks. -/
lemma polyTime_comp {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {g : β → γ}
    (hf : PolyTime ea eb f) (hg : PolyTime eb ec g) :
    PolyTime ea ec (g ∘ f) := by
  obtain ⟨c₁, hfin₁⟩ := hf
  obtain ⟨c₂, hfin₂⟩ := hg
  let M₁ := c₁.tm
  let M₂ := c₂.tm
  let e₁_out : M₁.Γ M₁.k₁ ≃ Bool := c₁.outputAlphabet
  let e₂_in : M₂.Γ M₂.k₀ ≃ Bool := c₂.inputAlphabet
  let pushBound : TM2.Stmt M₁.Γ M₁.Λ M₁.σ → ℕ :=
    @TM2.Stmt.rec M₁.K M₁.Γ M₁.Λ M₁.σ (fun _ => ℕ)
      (fun _ _ _ ih => ih + 1)
      (fun _ _ _ ih => ih)
      (fun _ _ _ ih => ih)
      (fun _ _ ih => ih)
      (fun _ _ _ ih₁ ih₂ => max ih₁ ih₂)
      (fun _ => 0)
      0
  have stepAux_len : ∀ (q : TM2.Stmt M₁.Γ M₁.Λ M₁.σ) (v : M₁.σ)
      (S : ∀ k, List (M₁.Γ k)) (k' : M₁.K),
      ((TM2.stepAux q v S).stk k').length ≤ (S k').length + pushBound q := by
    intro q
    induction q with
    | push k fn q ih =>
      intro v S k'
      simp only [TM2.stepAux]
      have hupd : ((Function.update S k (fn v :: S k)) k').length ≤ (S k').length + 1 := by
        by_cases hk : k' = k
        · subst hk
          simp
        · simp [hk]
      have hrec := ih v (Function.update S k (fn v :: S k)) k'
      change ((TM2.stepAux q v (Function.update S k (fn v :: S k))).stk k').length ≤
        (S k').length + (pushBound q + 1)
      omega
    | peek k fn q ih =>
      intro v S k'
      exact ih (fn v (S k).head?) S k'
    | pop k fn q ih =>
      intro v S k'
      simp only [TM2.stepAux]
      have hupd : ((Function.update S k (S k).tail) k').length ≤ (S k').length := by
        by_cases hk : k' = k
        · subst hk
          simp
        · simp [hk]
      have hrec := ih (fn v (S k).head?) (Function.update S k (S k).tail) k'
      change ((TM2.stepAux q (fn v (S k).head?) (Function.update S k (S k).tail)).stk k').length ≤
        (S k').length + pushBound q
      omega
    | load fn q ih =>
      intro v S k'
      exact ih (fn v) S k'
    | branch fn q₁ q₂ ih₁ ih₂ =>
      intro v S k'
      simp only [TM2.stepAux]
      cases fn v
      · simp only [Bool.cond_false]
        have hrec := ih₂ v S k'
        have hle : pushBound q₂ ≤ max (pushBound q₁) (pushBound q₂) := le_max_right _ _
        change ((TM2.stepAux q₂ v S).stk k').length ≤
          (S k').length + max (pushBound q₁) (pushBound q₂)
        omega
      · simp only [Bool.cond_true]
        have hrec := ih₁ v S k'
        have hle : pushBound q₁ ≤ max (pushBound q₁) (pushBound q₂) := le_max_left _ _
        change ((TM2.stepAux q₁ v S).stk k').length ≤
          (S k').length + max (pushBound q₁) (pushBound q₂)
        omega
    | goto fn =>
      intro v S k'
      simp [TM2.stepAux]
    | halt =>
      intro v S k'
      simp [TM2.stepAux]
  let B : ℕ := letI := M₁.ΛFin; Finset.univ.sup fun l : M₁.Λ => pushBound (M₁.m l)
  have step_len : ∀ (c c' : TM2.Cfg M₁.Γ M₁.Λ M₁.σ),
      M₁.step c = some c' → ∀ k', (c'.stk k').length ≤ (c.stk k').length + B := by
    intro c c' hstep k'
    rcases c with ⟨_ | l, v, S⟩
    · simp [FinTM2.step, TM2.step] at hstep
    · simp only [FinTM2.step, TM2.step] at hstep
      cases hstep
      have h1 := stepAux_len (M₁.m l) v S k'
      have h2 : pushBound (M₁.m l) ≤ B := by
        letI := M₁.ΛFin
        exact Finset.le_sup (f := fun l : M₁.Λ => pushBound (M₁.m l)) (Finset.mem_univ l)
      change ((TM2.stepAux (M₁.m l) v S).stk k').length ≤ (S k').length + B
      omega
  have iter_len : ∀ (t : ℕ) (c c' : TM2.Cfg M₁.Γ M₁.Λ M₁.σ),
      (flip bind M₁.step)^[t] (some c) = some c' →
      ∀ k', (c'.stk k').length ≤ (c.stk k').length + B * t := by
    intro t
    induction t with
    | zero =>
      intro c c' h k'
      simp only [Function.iterate_zero, id_eq] at h
      cases h
      simp
    | succ t ih =>
      intro c c' h k'
      rw [Function.iterate_succ_apply] at h
      rcases hstep : M₁.step c with _ | c₁
      · change (flip bind M₁.step)^[t] (M₁.step c) = some c' at h
        rw [hstep, iterate_none] at h
        cases h
      · change (flip bind M₁.step)^[t] (M₁.step c) = some c' at h
        rw [hstep] at h
        have h1 := step_len c c₁ hstep k'
        have h2 := ih c₁ c' h k'
        have hmul : B * (t + 1) = B * t + B := by ring
        omega
  have out_len : ∀ a : α, (eb (f a)).length ≤ (ea a).length + B * c₁.time.eval (ea a).length := by
    intro a
    obtain ⟨⟨t, ht⟩, hle⟩ := c₁.outputsFun a
    have hkl := iter_len t (initList M₁ (List.map c₁.inputAlphabet.invFun (ea a)))
      (haltList M₁ (List.map c₁.outputAlphabet.invFun (eb (f a)))) ht M₁.k₁
    have hhalt : ((haltList M₁ (List.map c₁.outputAlphabet.invFun (eb (f a)))).stk M₁.k₁).length =
        (eb (f a)).length := by
      simp [haltList]
    have hinit_all : ∀ k : M₁.K,
        ((initList M₁ (List.map c₁.inputAlphabet.invFun (ea a))).stk k).length ≤
          (ea a).length := by
      intro k
      simp only [initList]
      by_cases hk : k = M₁.k₀
      · subst hk
        simp
      · simp [hk]
    have hinit := hinit_all M₁.k₁
    have hmul : B * t ≤ B * c₁.time.eval (ea a).length := Nat.mul_le_mul_left B hle
    omega
  let G : M₁.K ⊕ M₂.K ⊕ Unit → Type := fun k =>
    match k with
    | Sum.inl k => M₁.Γ k
    | Sum.inr (Sum.inl k) => M₂.Γ k
    | Sum.inr (Sum.inr ()) => Bool
  let liftStmt₁ : TM2.Stmt M₁.Γ M₁.Λ M₁.σ →
      TM2.Stmt G (M₁.Λ ⊕ M₂.Λ ⊕ Fin 2) (M₁.σ × M₂.σ × Option Bool) :=
    @TM2.Stmt.rec M₁.K M₁.Γ M₁.Λ M₁.σ
      (fun _ => TM2.Stmt G (M₁.Λ ⊕ M₂.Λ ⊕ Fin 2) (M₁.σ × M₂.σ × Option Bool))
      (fun k fn _ ih => TM2.Stmt.push (Sum.inl k) (fun v => fn v.1) ih)
      (fun k fn _ ih => TM2.Stmt.peek (Sum.inl k) (fun v o => (fn v.1 o, v.2)) ih)
      (fun k fn _ ih => TM2.Stmt.pop (Sum.inl k) (fun v o => (fn v.1 o, v.2)) ih)
      (fun fn _ ih => TM2.Stmt.load (fun v => (fn v.1, v.2)) ih)
      (fun fn _ _ ih₁ ih₂ => TM2.Stmt.branch (fun v => fn v.1) ih₁ ih₂)
      (fun fn => TM2.Stmt.goto (fun v => Sum.inl (fn v.1)))
      (TM2.Stmt.goto (fun _ => Sum.inr (Sum.inr 0)))
  let liftStmt₂ : TM2.Stmt M₂.Γ M₂.Λ M₂.σ →
      TM2.Stmt G (M₁.Λ ⊕ M₂.Λ ⊕ Fin 2) (M₁.σ × M₂.σ × Option Bool) :=
    @TM2.Stmt.rec M₂.K M₂.Γ M₂.Λ M₂.σ
      (fun _ => TM2.Stmt G (M₁.Λ ⊕ M₂.Λ ⊕ Fin 2) (M₁.σ × M₂.σ × Option Bool))
      (fun k fn _ ih => TM2.Stmt.push (Sum.inr (Sum.inl k)) (fun v => fn v.2.1) ih)
      (fun k fn _ ih => TM2.Stmt.peek (Sum.inr (Sum.inl k)) (fun v o => (v.1, fn v.2.1 o, v.2.2)) ih)
      (fun k fn _ ih => TM2.Stmt.pop (Sum.inr (Sum.inl k)) (fun v o => (v.1, fn v.2.1 o, v.2.2)) ih)
      (fun fn _ ih => TM2.Stmt.load (fun v => (v.1, fn v.2.1, v.2.2)) ih)
      (fun fn _ _ ih₁ ih₂ => TM2.Stmt.branch (fun v => fn v.2.1) ih₁ ih₂)
      (fun fn => TM2.Stmt.goto (fun v => Sum.inr (Sum.inl (fn v.2.1))))
      TM2.Stmt.halt
  let prog : M₁.Λ ⊕ M₂.Λ ⊕ Fin 2 →
      TM2.Stmt G (M₁.Λ ⊕ M₂.Λ ⊕ Fin 2) (M₁.σ × M₂.σ × Option Bool) :=
    fun q => match q with
    | Sum.inl l => liftStmt₁ (M₁.m l)
    | Sum.inr (Sum.inl l) => liftStmt₂ (M₂.m l)
    | Sum.inr (Sum.inr p) =>
      if p = 0 then
        .pop (Sum.inl M₁.k₁) (fun v o => (v.1, v.2.1, o.map e₁_out)) <|
          .branch (fun v => v.2.2.isSome)
            (.push (Sum.inr (Sum.inr ())) (fun v => v.2.2.getD false) <|
              .goto fun _ => Sum.inr (Sum.inr 0))
            (.goto fun _ => Sum.inr (Sum.inr 1))
      else
        .pop (Sum.inr (Sum.inr ())) (fun v o => (v.1, v.2.1, o)) <|
          .branch (fun v => v.2.2.isSome)
            (.push (Sum.inr (Sum.inl M₂.k₀)) (fun v => e₂_in.symm (v.2.2.getD false)) <|
              .goto fun _ => Sum.inr (Sum.inr 1))
            (.goto fun _ => Sum.inr (Sum.inl M₂.main))
  let N : FinTM2 :=
    letI := M₁.kFin
    letI := M₂.kFin
    letI := M₁.ΛFin
    letI := M₂.ΛFin
    letI := M₁.σFin
    letI := M₂.σFin
    { K := M₁.K ⊕ M₂.K ⊕ Unit
      k₀ := Sum.inl M₁.k₀
      k₁ := Sum.inr (Sum.inl M₂.k₁)
      Γ := G
      Λ := M₁.Λ ⊕ M₂.Λ ⊕ Fin 2
      main := Sum.inl M₁.main
      σ := M₁.σ × M₂.σ × Option Bool
      initialState := (M₁.initialState, M₂.initialState, none)
      Γk₀Fin := M₁.Γk₀Fin
      m := prog }
  have hfinN : FiniteStacks N := by
    intro k
    rcases k with k | (k | ⟨⟩)
    · exact hfin₁ k
    · exact hfin₂ k
    · exact inferInstance
  let mk (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (aux : List Bool) :
      ∀ k : M₁.K ⊕ M₂.K ⊕ Unit, List (G k) :=
    fun k => match k with
    | Sum.inl k => S₁ k
    | Sum.inr (Sum.inl k) => S₂ k
    | Sum.inr (Sum.inr ()) => aux
  have upd_inl (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (aux : List Bool)
      (k : M₁.K) (v : List (G (Sum.inl k))) :
      Function.update (mk S₁ S₂ aux) (Sum.inl k) v = mk (Function.update S₁ k v) S₂ aux := by
    funext k'
    rcases k' with k' | (k' | ⟨⟩)
    · by_cases h : k' = k
      · subst h
        simp [Function.update, mk]
      · simp [Function.update, mk, h]
    · simp [Function.update, mk]
    · simp [Function.update, mk]
  have upd_mid (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (aux : List Bool)
      (k : M₂.K) (v : List (G (Sum.inr (Sum.inl k)))) :
      Function.update (mk S₁ S₂ aux) (Sum.inr (Sum.inl k)) v =
        mk S₁ (Function.update S₂ k v) aux := by
    funext k'
    rcases k' with k' | (k' | ⟨⟩)
    · simp [Function.update, mk]
    · by_cases h : k' = k
      · subst h
        simp [Function.update, mk]
      · simp [Function.update, mk, h]
    · simp [Function.update, mk]
  have upd_aux (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (aux aux' : List Bool) :
      Function.update (mk S₁ S₂ aux) (Sum.inr (Sum.inr ())) aux' = mk S₁ S₂ aux' := by
    funext k'
    rcases k' with k' | (k' | ⟨⟩) <;> simp [Function.update, mk]
  let liftCfg₁ (c : TM2.Cfg M₁.Γ M₁.Λ M₁.σ) : N.Cfg :=
    ⟨match c.l with | some l => some (Sum.inl l) | none => some (Sum.inr (Sum.inr 0)),
      (c.var, M₂.initialState, none), mk c.stk (fun _ => []) []⟩
  let cfg₀ (o : Option Bool) (S₁ : ∀ k, List (M₁.Γ k)) (aux : List Bool) : N.Cfg :=
    ⟨some (Sum.inr (Sum.inr 0)), (M₁.initialState, M₂.initialState, o), mk S₁ (fun _ => []) aux⟩
  let cfg₁ (o : Option Bool) (S₁ : ∀ k, List (M₁.Γ k)) (aux : List Bool)
      (S₂ : ∀ k, List (M₂.Γ k)) : N.Cfg :=
    ⟨some (Sum.inr (Sum.inr 1)), (M₁.initialState, M₂.initialState, o), mk S₁ S₂ aux⟩
  let liftCfg₂ (c : TM2.Cfg M₂.Γ M₂.Λ M₂.σ) : N.Cfg :=
    ⟨c.l.map (Sum.inr ∘ Sum.inl), (M₁.initialState, c.var, none), mk (fun _ => []) c.stk []⟩
  have stepAux_lift₁ : ∀ (q : TM2.Stmt M₁.Γ M₁.Λ M₁.σ) (v : M₁.σ)
      (S : ∀ k, List (M₁.Γ k)),
      TM2.stepAux (liftStmt₁ q) (v, M₂.initialState, none) (mk S (fun _ => []) []) =
        liftCfg₁ (TM2.stepAux q v S) := by
    intro q v S
    induction q generalizing v S with
    | push k fn q ih =>
      change TM2.stepAux (TM2.Stmt.push (Sum.inl k) (fun v => fn v.1) (liftStmt₁ q))
        (v, M₂.initialState, none) (mk S (fun _ => []) []) = _
      simp only [TM2.stepAux]
      rw [upd_inl]
      exact ih _ _
    | peek k fn q ih =>
      change TM2.stepAux (TM2.Stmt.peek (Sum.inl k) (fun v o => (fn v.1 o, v.2)) (liftStmt₁ q))
        (v, M₂.initialState, none) (mk S (fun _ => []) []) = _
      simp only [TM2.stepAux]
      exact ih _ _
    | pop k fn q ih =>
      change TM2.stepAux (TM2.Stmt.pop (Sum.inl k) (fun v o => (fn v.1 o, v.2)) (liftStmt₁ q))
        (v, M₂.initialState, none) (mk S (fun _ => []) []) = _
      simp only [TM2.stepAux]
      rw [upd_inl]
      exact ih _ _
    | load fn q ih =>
      change TM2.stepAux (TM2.Stmt.load (fun v => (fn v.1, v.2)) (liftStmt₁ q))
        (v, M₂.initialState, none) (mk S (fun _ => []) []) = _
      simp only [TM2.stepAux]
      exact ih _ _
    | branch fn q₁ q₂ ih₁ ih₂ =>
      change TM2.stepAux (TM2.Stmt.branch (fun v => fn v.1) (liftStmt₁ q₁) (liftStmt₁ q₂))
        (v, M₂.initialState, none) (mk S (fun _ => []) []) = _
      simp only [TM2.stepAux, ih₁, ih₂]
      cases fn v <;> rfl
    | goto fn => rfl
    | halt => rfl
  have step_lift₁ : ∀ (l : M₁.Λ) (v : M₁.σ) (S : ∀ k, List (M₁.Γ k)),
      N.step (liftCfg₁ ⟨some l, v, S⟩) = some (liftCfg₁ (TM2.stepAux (M₁.m l) v S)) := by
    intro l v S
    show some (TM2.stepAux (liftStmt₁ (M₁.m l)) (v, M₂.initialState, none)
      (mk S (fun _ => []) [])) = _
    rw [stepAux_lift₁]
    rfl
  have iterate_lift₁ : ∀ (n : ℕ) (c c' : TM2.Cfg M₁.Γ M₁.Λ M₁.σ),
      (flip bind M₁.step)^[n] (some c) = some c' →
      (flip bind N.step)^[n] (some (liftCfg₁ c)) = some (liftCfg₁ c') := by
    intro n
    induction n with
    | zero =>
      intro c c' h
      simp only [Function.iterate_zero, id_eq] at h
      cases h
      rfl
    | succ n ih =>
      intro c c' h
      rw [Function.iterate_succ_apply] at h ⊢
      rcases c with ⟨_ | l, v, S⟩
      · have hnone : M₁.step ⟨none, v, S⟩ = none := rfl
        change (flip bind M₁.step)^[n] (M₁.step ⟨none, v, S⟩) = some c' at h
        rw [hnone, iterate_none] at h
        cases h
      · have hstep : N.step (liftCfg₁ ⟨some l, v, S⟩) =
            some (liftCfg₁ (TM2.stepAux (M₁.m l) v S)) := step_lift₁ l v S
        change (flip bind M₁.step)^[n] (some (TM2.stepAux (M₁.m l) v S)) = some c' at h
        change (flip bind N.step)^[n] (N.step (liftCfg₁ ⟨some l, v, S⟩)) = _
        rw [hstep]
        exact ih _ _ h
  have stepAux_lift₂ : ∀ (q : TM2.Stmt M₂.Γ M₂.Λ M₂.σ) (v : M₂.σ)
      (S : ∀ k, List (M₂.Γ k)),
      TM2.stepAux (liftStmt₂ q) (M₁.initialState, v, none) (mk (fun _ => []) S []) =
        liftCfg₂ (TM2.stepAux q v S) := by
    intro q v S
    induction q generalizing v S with
    | push k fn q ih =>
      change TM2.stepAux (TM2.Stmt.push (Sum.inr (Sum.inl k)) (fun v => fn v.2.1) (liftStmt₂ q))
        (M₁.initialState, v, none) (mk (fun _ => []) S []) = _
      simp only [TM2.stepAux]
      rw [upd_mid]
      exact ih _ _
    | peek k fn q ih =>
      change TM2.stepAux (TM2.Stmt.peek (Sum.inr (Sum.inl k))
        (fun v o => (v.1, fn v.2.1 o, v.2.2)) (liftStmt₂ q))
        (M₁.initialState, v, none) (mk (fun _ => []) S []) = _
      simp only [TM2.stepAux]
      exact ih _ _
    | pop k fn q ih =>
      change TM2.stepAux (TM2.Stmt.pop (Sum.inr (Sum.inl k))
        (fun v o => (v.1, fn v.2.1 o, v.2.2)) (liftStmt₂ q))
        (M₁.initialState, v, none) (mk (fun _ => []) S []) = _
      simp only [TM2.stepAux]
      rw [upd_mid]
      exact ih _ _
    | load fn q ih =>
      change TM2.stepAux (TM2.Stmt.load (fun v => (v.1, fn v.2.1, v.2.2)) (liftStmt₂ q))
        (M₁.initialState, v, none) (mk (fun _ => []) S []) = _
      simp only [TM2.stepAux]
      exact ih _ _
    | branch fn q₁ q₂ ih₁ ih₂ =>
      change TM2.stepAux (TM2.Stmt.branch (fun v => fn v.2.1) (liftStmt₂ q₁) (liftStmt₂ q₂))
        (M₁.initialState, v, none) (mk (fun _ => []) S []) = _
      simp only [TM2.stepAux, ih₁, ih₂]
      cases fn v <;> rfl
    | goto fn => rfl
    | halt => rfl
  have step_lift₂ : ∀ (c : TM2.Cfg M₂.Γ M₂.Λ M₂.σ),
      N.step (liftCfg₂ c) = (M₂.step c).map liftCfg₂ := by
    intro c
    rcases c with ⟨_ | l, v, S⟩
    · rfl
    · show some (TM2.stepAux (liftStmt₂ (M₂.m l)) (M₁.initialState, v, none)
        (mk (fun _ => []) S [])) = _
      rw [stepAux_lift₂]
      rfl
  have iterate_lift₂ : ∀ (n : ℕ) (o : Option (TM2.Cfg M₂.Γ M₂.Λ M₂.σ)),
      (flip bind N.step)^[n] (o.map liftCfg₂) = ((flip bind M₂.step)^[n] o).map liftCfg₂ := by
    intro n o
    have hs : Function.Semiconj (Option.map liftCfg₂) (flip bind M₂.step) (flip bind N.step) := by
      intro o
      rcases o with _ | c
      · rfl
      · show (M₂.step c).map liftCfg₂ = N.step (liftCfg₂ c)
        rw [step_lift₂]
    exact ((hs.iterate_right n) o).symm
  have step_rev_nil : ∀ (o : Option Bool) (S₁ : ∀ k, List (M₁.Γ k)) (aux : List Bool),
      S₁ M₁.k₁ = [] →
      N.step (cfg₀ o S₁ aux) = some (cfg₁ none S₁ aux (fun _ => [])) := by
    intro o S₁ aux hS
    show some (TM2.stepAux (prog (Sum.inr (Sum.inr 0)))
      (M₁.initialState, M₂.initialState, o) (mk S₁ (fun _ => []) aux)) = _
    have hupd : Function.update S₁ M₁.k₁ [] = S₁ := by
      rw [← hS, Function.update_eq_self]
    dsimp only [prog]
    simp [TM2.stepAux, mk, hS, upd_inl, cfg₁]
    rw [hupd]
    rfl
  have step_rev_cons : ∀ (o : Option Bool) (S₁ : ∀ k, List (M₁.Γ k))
      (x : M₁.Γ M₁.k₁) (rest : List (M₁.Γ M₁.k₁)) (aux : List Bool),
      S₁ M₁.k₁ = x :: rest →
      N.step (cfg₀ o S₁ aux) =
        some (cfg₀ (some (e₁_out x)) (Function.update S₁ M₁.k₁ rest) (e₁_out x :: aux)) := by
    intro o S₁ x rest aux hS
    show some (TM2.stepAux (prog (Sum.inr (Sum.inr 0)))
      (M₁.initialState, M₂.initialState, o) (mk S₁ (fun _ => []) aux)) = _
    dsimp only [prog]
    simp [TM2.stepAux, mk, hS, upd_inl, upd_aux, cfg₀]
    rfl
  have step_copy_nil : ∀ (o : Option Bool) (S₂ : ∀ k, List (M₂.Γ k)),
      N.step (cfg₁ o (fun _ => []) [] S₂) =
        some (liftCfg₂ ⟨some M₂.main, M₂.initialState, S₂⟩) := by
    intro o S₂
    show some (TM2.stepAux (prog (Sum.inr (Sum.inr 1)))
      (M₁.initialState, M₂.initialState, o) (mk (fun _ => []) S₂ [])) = _
    dsimp only [prog]
    simp [TM2.stepAux, mk, liftCfg₂]
    rfl
  have step_copy_cons : ∀ (o : Option Bool) (b : Bool) (aux : List Bool)
      (S₂ : ∀ k, List (M₂.Γ k)),
      N.step (cfg₁ o (fun _ => []) (b :: aux) S₂) =
        some (cfg₁ (some b) (fun _ => []) aux
          (Function.update S₂ M₂.k₀ (e₂_in.symm b :: S₂ M₂.k₀))) := by
    intro o b aux S₂
    show some (TM2.stepAux (prog (Sum.inr (Sum.inr 1)))
      (M₁.initialState, M₂.initialState, o) (mk (fun _ => []) S₂ (b :: aux))) = _
    dsimp only [prog]
    simp [TM2.stepAux, mk, upd_aux, upd_mid, cfg₁]
    rfl
  have rev_run : ∀ (l : List (M₁.Γ M₁.k₁)) (S₁ : ∀ k, List (M₁.Γ k))
      (aux : List Bool) (o : Option Bool),
      S₁ M₁.k₁ = l →
      ∃ n ≤ l.length + 1, (flip bind N.step)^[n] (some (cfg₀ o S₁ aux)) =
        some (cfg₁ none (Function.update S₁ M₁.k₁ []) ((l.map e₁_out).reverse ++ aux)
          (fun _ => [])) := by
    intro l
    induction l with
    | nil =>
      intro S₁ aux o hS
      have hupd : Function.update S₁ M₁.k₁ [] = S₁ := by
        rw [← hS, Function.update_eq_self]
      rw [hupd]
      simpa using rIn_single (step_rev_nil o S₁ aux hS)
    | cons x l ih =>
      intro S₁ aux o hS
      have h1 := rIn_single (step_rev_cons o S₁ x l aux hS)
      have h2 := ih (Function.update S₁ M₁.k₁ l) (e₁_out x :: aux) (some (e₁_out x)) (by simp)
      have htrans := rIn_trans h1 h2
      simp only [Function.update_idem] at htrans
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using htrans
  have copy_run : ∀ (aux : List Bool) (o : Option Bool) (S₂ : ∀ k, List (M₂.Γ k)),
      ∃ n ≤ aux.length + 1, (flip bind N.step)^[n] (some (cfg₁ o (fun _ => []) aux S₂)) =
        some (liftCfg₂ ⟨some M₂.main, M₂.initialState,
          Function.update S₂ M₂.k₀ ((aux.map e₂_in.symm).reverse ++ S₂ M₂.k₀)⟩) := by
    intro aux
    induction aux with
    | nil =>
      intro o S₂
      simp only [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
      exact rIn_single (step_copy_nil o S₂)
    | cons b aux ih =>
      intro o S₂
      have h1 := rIn_single (step_copy_cons o b aux S₂)
      have h2 := ih (some b) (Function.update S₂ M₂.k₀ (e₂_in.symm b :: S₂ M₂.k₀))
      have htrans := rIn_trans h1 h2
      simp only [Function.update_idem] at htrans
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using htrans
  have initList_N (l : List (M₁.Γ M₁.k₀)) :
      initList N l = liftCfg₁ (initList M₁ l) := by
    simp only [initList, liftCfg₁, N]
    congr 1
    funext k
    rcases k with k | (k | ⟨⟩)
    · by_cases h : k = M₁.k₀
      · subst h
        simp [mk]
      · simp [mk, h]
    · simp [mk]
    · simp [mk]
  have initList_M₂ (l : List (M₂.Γ M₂.k₀)) :
      liftCfg₂ ⟨some M₂.main, M₂.initialState, Function.update (fun _ => []) M₂.k₀ l⟩ =
        liftCfg₂ (initList M₂ l) := by
    simp only [initList]
    congr 3
    funext k
    by_cases h : k = M₂.k₀
    · subst h
      simp
    · rw [Function.update_of_ne h, dif_neg h]
  have haltList_lift₂ (out₂ : List (M₂.Γ M₂.k₁)) :
      liftCfg₂ (haltList M₂ out₂) = haltList N out₂ := by
    simp only [liftCfg₂, haltList, N]
    congr 1
    funext k
    rcases k with k | (k | ⟨⟩)
    · simp [mk]
    · by_cases h : k = M₂.k₁
      · subst h
        simp [mk]
      · simp [mk, h]
    · simp [mk]
  let p₁ : Polynomial ℕ := Polynomial.X + Polynomial.C B * c₁.time
  let totalPoly : Polynomial ℕ :=
    c₁.time + Polynomial.C 2 * (p₁ + 1) + c₂.time.comp p₁
  refine ⟨{ tm := N
            inputAlphabet := c₁.inputAlphabet
            outputAlphabet := c₂.outputAlphabet
            time := totalPoly
            outputsFun := fun a => ?_ }, hfinN⟩
  set inp₁ : List (M₁.Γ M₁.k₀) := List.map c₁.inputAlphabet.invFun (ea a)
  set out₁ : List (M₁.Γ M₁.k₁) := List.map c₁.outputAlphabet.invFun (eb (f a))
  set inp₂ : List (M₂.Γ M₂.k₀) := List.map c₂.inputAlphabet.invFun (eb (f a))
  set out₂ : List (M₂.Γ M₂.k₁) := List.map c₂.outputAlphabet.invFun (ec (g (f a)))
  have hrun₁ : ∃ n ≤ c₁.time.eval (ea a).length,
      (flip bind N.step)^[n] (some (initList N inp₁)) =
        some (liftCfg₁ (haltList M₁ out₁)) := by
    obtain ⟨⟨t, ht⟩, hle⟩ := c₁.outputsFun a
    refine ⟨t, hle, ?_⟩
    rw [initList_N]
    exact iterate_lift₁ t (initList M₁ inp₁) (haltList M₁ out₁) ht
  have hrev_start : liftCfg₁ (haltList M₁ out₁) = cfg₀ none (haltList M₁ out₁).stk [] := rfl
  have hstk₁ : (haltList M₁ out₁).stk M₁.k₁ = out₁ := by simp [haltList]
  have hclear₁ : Function.update (haltList M₁ out₁).stk M₁.k₁ [] = fun _ => [] := by
    let s₁ : ∀ k, List (M₁.Γ k) := (haltList M₁ out₁).stk
    show Function.update s₁ M₁.k₁ [] = fun _ => []
    funext k
    by_cases h : k = M₁.k₁
    · subst h
      exact Function.update_self M₁.k₁ [] s₁
    · rw [Function.update_of_ne h]
      simp [s₁, haltList, h]
  have hrun_rev : ∃ n ≤ (eb (f a)).length + 1,
      (flip bind N.step)^[n] (some (liftCfg₁ (haltList M₁ out₁))) =
        some (cfg₁ none (fun _ => []) (eb (f a)).reverse (fun _ => [])) := by
    rw [hrev_start]
    have hr := rev_run out₁ (haltList M₁ out₁).stk [] none hstk₁
    rw [hclear₁] at hr
    have hmap : out₁.map e₁_out = eb (f a) := by
      simp [out₁, e₁_out]
    have hlen : out₁.length = (eb (f a)).length := by simp [out₁]
    rw [hlen, hmap, List.append_nil] at hr
    exact hr
  have hrun_copy : ∃ n ≤ (eb (f a)).length + 1,
      (flip bind N.step)^[n] (some (cfg₁ none (fun _ => []) (eb (f a)).reverse (fun _ => []))) =
        some (liftCfg₂ (initList M₂ inp₂)) := by
    have hc := copy_run (eb (f a)).reverse none (fun _ => [])
    have hlen : (eb (f a)).reverse.length = (eb (f a)).length := by simp
    have hinp : ((eb (f a)).reverse.map e₂_in.symm).reverse ++ [] = inp₂ := by
      simp [inp₂, e₂_in, List.map_reverse]
    rw [hlen, hinp, initList_M₂] at hc
    exact hc
  have hrun₂ : ∃ n ≤ c₂.time.eval (eb (f a)).length,
      (flip bind N.step)^[n] (some (liftCfg₂ (initList M₂ inp₂))) =
        some (haltList N out₂) := by
    obtain ⟨⟨t, ht⟩, hle⟩ := c₂.outputsFun (f a)
    refine ⟨t, hle, ?_⟩
    have := iterate_lift₂ t (some (initList M₂ inp₂))
    change (flip bind N.step)^[t] (Option.map liftCfg₂ (some (initList M₂ inp₂))) = _
    rw [this]
    refine (congrArg (Option.map liftCfg₂) ht).trans ?_
    show some (liftCfg₂ (haltList M₂ out₂)) = _
    rw [haltList_lift₂]
  have hrun : ∃ n ≤ c₁.time.eval (ea a).length + ((eb (f a)).length + 1) +
      ((eb (f a)).length + 1) + c₂.time.eval (eb (f a)).length,
      (flip bind N.step)^[n] (some (initList N inp₁)) = some (haltList N out₂) :=
    rIn_trans (rIn_trans (rIn_trans hrun₁ hrun_rev) hrun_copy) hrun₂
  have hb : c₁.time.eval (ea a).length + ((eb (f a)).length + 1) +
      ((eb (f a)).length + 1) + c₂.time.eval (eb (f a)).length ≤
      totalPoly.eval (ea a).length := by
    have hlen := out_len a
    have hev₂ := eval_mono c₂.time hlen
    have hp₁ : p₁.eval (ea a).length = (ea a).length + B * c₁.time.eval (ea a).length := by
      simp [p₁]
    have htot : totalPoly.eval (ea a).length =
        c₁.time.eval (ea a).length + 2 * (p₁.eval (ea a).length + 1) +
          c₂.time.eval (p₁.eval (ea a).length) := by
      simp only [totalPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_one, Polynomial.eval_comp]
    rw [htot, hp₁]
    omega
  exact Classical.choice (by
    obtain ⟨n, hle, he⟩ := rIn_mono hrun hb
    exact ⟨⟨⟨n, he⟩, hle⟩⟩)

theorem main : H1 → H2 → type_of% @OMA.S_wp_unique_games_conjecture.main := by
  intro h1 h2
  obtain ⟨ε₀, hε₀, h2⟩ := h2
  refine ⟨ε₀, hε₀, fun ε δ hε hε' hδ hδ' => ?_⟩
  obtain ⟨k, g, hg_poly, hg_gap⟩ := h2 ε δ hε hε' hδ hδ'
  refine ⟨k, fun L hL => ?_⟩
  obtain ⟨f, hf_poly, hf_iff⟩ := h1 L hL
  refine ⟨g ∘ f, polyTime_comp hf_poly hg_poly, fun x => ?_⟩
  obtain ⟨hyes, hno⟩ := hg_gap (f x)
  constructor
  · intro hx
    exact hyes ((hf_iff x).mp hx)
  · intro hx
    exact hno (fun hcol => hx ((hf_iff x).mpr hcol))

end OMA.R_wp_unique_games_conjecture_R1
