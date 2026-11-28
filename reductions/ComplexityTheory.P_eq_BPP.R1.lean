import FormalConjectures.Millennium.PvsNP
import Mathlib.Tactic

-- Reduction ComplexityTheory.P_eq_BPP.R1 of P = BPP
-- Credit: @hadijannat
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Reduction of P = BPP to PRG derandomization and majority evaluation

`P ⊆ BPP` is proved unconditionally inside this reduction (mirroring the `FinTM2`
projection machine from `ComplexityTheory.P_subset_BPP` by `@ashnewmanjones` / `AItoBit/p-subset-np`).
`BPP ⊆ P` is reduced via pseudorandom derandomization to two hypotheses:

* `H1` (open core): every polynomial-time predicate `R(x, r)` admits a polynomial `q` and a
  polynomial-time generator `G(1^|x|, i)` (`i < q(|x|)`) that `1/6`-fools `R(x, ·)`.
* `H2` (known step): deciding majority acceptance of `R(x, G(1^|x|, i))` over `i < q(|x|)`
  is computable in polynomial time.
-/

namespace OMA.R_ComplexityTheory_P_eq_BPP_R1

/-- Existence of polynomial-time pseudorandom generators fooling polynomial-time predicates. -/
def H1 : Prop :=
  ∀ (p : Polynomial ℕ) (R : (List Bool × List Bool) → Bool),
    ComplexityTheory.IsPolyTime R →
    ∃ (q : Polynomial ℕ) (G : (List Bool × ℕ) → List Bool),
      ComplexityTheory.IsPolyTime G ∧
      ∀ x : List Bool,
        0 < q.eval x.length ∧
        (∀ i < q.eval x.length,
          (G (List.replicate x.length false, i)).length = p.eval x.length) ∧
        |(((Finset.range (q.eval x.length)).filter
            fun i => R (x, G (List.replicate x.length false, i)) = true).card : ℚ) /
            ((q.eval x.length : ℕ) : ℚ) -
         ((Finset.univ.filter
            fun r : Fin (p.eval x.length) → Bool => R (x, List.ofFn r) = true).card : ℚ) /
            (2 : ℚ) ^ (p.eval x.length)| < (1 : ℚ) / 6

/-- Majority evaluation over polynomially many PRG seeds is polynomial-time computable. -/
def H2 : Prop :=
  ∀ (q : Polynomial ℕ) (R : (List Bool × List Bool) → Bool)
    (G : (List Bool × ℕ) → List Bool),
    ComplexityTheory.IsPolyTime R →
    ComplexityTheory.IsPolyTime G →
    ComplexityTheory.IsPolyTime (fun x : List Bool =>
      decide (q.eval x.length <
        2 * ((Finset.range (q.eval x.length)).filter
          fun i => R (x, G (List.replicate x.length false, i)) = true).card))

open Turing Computability ComplexityTheory

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

/-- If `f` is computable in polynomial time, then so is `fun p => f p.1`. -/
lemma comp_fst {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] (f : α → β) (hf : IsPolyTime f) :
    IsPolyTime (fun p : α × γ => f p.1) := by
  obtain ⟨M⟩ := hf
  let tm := M.tm
  let e : tm.Γ tm.k₀ ≃ Bool := M.inputAlphabet
  let G : Bool ⊕ tm.K → Type := fun k => Sum.casesOn (motive := fun _ => Type) k (fun _ => Bool) tm.Γ
  let liftStmt : TM2.Stmt tm.Γ tm.Λ tm.σ → TM2.Stmt G (tm.Λ ⊕ Fin 3) (tm.σ × Option Bool) :=
    @TM2.Stmt.rec tm.K tm.Γ tm.Λ tm.σ
      (fun _ => TM2.Stmt G (tm.Λ ⊕ Fin 3) (tm.σ × Option Bool))
      (fun k f _ ih => TM2.Stmt.push (Sum.inr k) (fun v => f v.1) ih)
      (fun k f _ ih => TM2.Stmt.peek (Sum.inr k) (fun v o => (f v.1 o, v.2)) ih)
      (fun k f _ ih => TM2.Stmt.pop (Sum.inr k) (fun v o => (f v.1 o, v.2)) ih)
      (fun a _ ih => TM2.Stmt.load (fun v => (a v.1, v.2)) ih)
      (fun f _ _ ih₁ ih₂ => TM2.Stmt.branch (fun v => f v.1) ih₁ ih₂)
      (fun f => TM2.Stmt.goto (fun v => Sum.inl (f v.1)))
      TM2.Stmt.halt
  let prog : tm.Λ ⊕ Fin 3 → TM2.Stmt G (tm.Λ ⊕ Fin 3) (tm.σ × Option Bool) :=
    fun q => match q with
    | Sum.inl l => liftStmt (tm.m l)
    | Sum.inr p =>
      if p = 0 then
        .pop (Sum.inl false) (fun v o => (v.1, o)) <|
          .branch (fun v => v.2 == some true)
            (.pop (Sum.inl false) (fun v o => (v.1, o)) <|
              .push (Sum.inl true) (fun v => v.2.getD false) <| .goto fun _ => Sum.inr 0)
            (.goto fun _ => Sum.inr 1)
      else if p = 1 then
        .pop (Sum.inl false) (fun v o => (v.1, o)) <|
          .branch (fun v => v.2.isSome) (.goto fun _ => Sum.inr 1)
            (.goto fun _ => Sum.inr 2)
      else
        .pop (Sum.inl true) (fun v o => (v.1, o)) <|
          .branch (fun v => v.2.isSome)
            (.push (Sum.inr tm.k₀) (fun v => e.symm (v.2.getD false)) <|
              .goto fun _ => Sum.inr 2)
            (.goto fun _ => Sum.inl tm.main)
  let N : FinTM2 :=
    letI := tm.kFin
    letI := tm.ΛFin
    letI := tm.σFin
    { K := Bool ⊕ tm.K
      k₀ := Sum.inl false
      k₁ := Sum.inr tm.k₁
      Γ := G
      Λ := tm.Λ ⊕ Fin 3
      main := Sum.inr 0
      σ := tm.σ × Option Bool
      initialState := (tm.initialState, none)
      Γk₀Fin := inferInstanceAs (Fintype Bool)
      m := prog }
  let mk (i a : List Bool) (S : ∀ k, List (tm.Γ k)) : ∀ k : Bool ⊕ tm.K, List (G k) :=
    fun k => match k with
    | Sum.inl false => i
    | Sum.inl true => a
    | Sum.inr k => S k
  have upd_inp (i a : List Bool) (i' : List (G (Sum.inl false))) (S : ∀ k, List (tm.Γ k)) :
      Function.update (mk i a S) (Sum.inl false) i' = mk i' a S := by
    funext k
    rcases k with (_ | _) | k <;> simp [Function.update, mk]
  have upd_aux (i a : List Bool) (a' : List (G (Sum.inl true))) (S : ∀ k, List (tm.Γ k)) :
      Function.update (mk i a S) (Sum.inl true) a' = mk i a' S := by
    funext k
    rcases k with (_ | _) | k <;> simp [Function.update, mk]
  have upd_inr (i a : List Bool) (S : ∀ k, List (tm.Γ k)) (k : tm.K) (v : List (G (Sum.inr k))) :
      Function.update (mk i a S) (Sum.inr k) v = mk i a (Function.update S k v) := by
    funext k'
    rcases k' with (_ | _) | k'
    · simp [Function.update, mk]
    · simp [Function.update, mk]
    · by_cases h : k' = k
      · subst h
        simp [Function.update, mk]
      · simp [Function.update, mk, h]
  let liftCfg (c : TM2.Cfg tm.Γ tm.Λ tm.σ) : N.Cfg :=
    ⟨c.l.map Sum.inl, (c.var, none), mk [] [] c.stk⟩
  let cfg (l : Fin 3) (o : Option Bool) (i a : List Bool) (S : ∀ k, List (tm.Γ k)) : N.Cfg :=
    ⟨some (Sum.inr l), (tm.initialState, o), mk i a S⟩
  have stepAux_lift (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)) :
      TM2.stepAux (liftStmt q) (v, none) (mk [] [] S) = liftCfg (TM2.stepAux q v S) := by
    induction q generalizing v S with
    | push k f q ih =>
      change TM2.stepAux (TM2.Stmt.push (Sum.inr k) (fun v => f v.1) (liftStmt q)) (v, none) (mk [] [] S) = _
      simp only [TM2.stepAux]
      rw [upd_inr]
      exact ih _ _
    | peek k f q ih =>
      change TM2.stepAux (TM2.Stmt.peek (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftStmt q)) (v, none) (mk [] [] S) = _
      simp only [TM2.stepAux]
      exact ih _ _
    | pop k f q ih =>
      change TM2.stepAux (TM2.Stmt.pop (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftStmt q)) (v, none) (mk [] [] S) = _
      simp only [TM2.stepAux]
      rw [upd_inr]
      exact ih _ _
    | load a q ih =>
      change TM2.stepAux (TM2.Stmt.load (fun v => (a v.1, v.2)) (liftStmt q)) (v, none) (mk [] [] S) = _
      simp only [TM2.stepAux]
      exact ih _ _
    | branch f q₁ q₂ ih₁ ih₂ =>
      change TM2.stepAux (TM2.Stmt.branch (fun v => f v.1) (liftStmt q₁) (liftStmt q₂)) (v, none) (mk [] [] S) = _
      simp only [TM2.stepAux, ih₁, ih₂]
      cases f v <;> rfl
    | goto f => rfl
    | halt => rfl
  have step_lift (c : TM2.Cfg tm.Γ tm.Λ tm.σ) :
      N.step (liftCfg c) = (tm.step c).map liftCfg := by
    rcases c with ⟨_ | l, v, S⟩
    · rfl
    · show some (TM2.stepAux (liftStmt (tm.m l)) (v, none) (mk [] [] S)) = _
      rw [stepAux_lift]
      rfl
  have iterate_lift (n : ℕ) (o : Option (TM2.Cfg tm.Γ tm.Λ tm.σ)) :
      (flip bind N.step)^[n] (o.map liftCfg) = ((flip bind tm.step)^[n] o).map liftCfg := by
    have hs : Function.Semiconj (Option.map liftCfg) (flip bind tm.step) (flip bind N.step) := by
      intro o
      rcases o with _ | c
      · rfl
      · show (tm.step c).map liftCfg = N.step (liftCfg c)
        rw [step_lift]
    exact ((hs.iterate_right n) o).symm
  have step_parse_false (o : Option Bool) (rest a : List Bool) (S : ∀ k, List (tm.Γ k)) :
      N.step (cfg 0 o (false :: rest) a S) = some (cfg 1 (some false) rest a S) := by
    show some (TM2.stepAux (prog (Sum.inr 0)) (tm.initialState, o)
      (mk (false :: rest) a S)) = _
    dsimp only [prog]
    simp [TM2.stepAux, mk, upd_inp, upd_aux, cfg]
    rfl
  have step_parse_true (o : Option Bool) (c : Bool) (rest a : List Bool)
      (S : ∀ k, List (tm.Γ k)) :
      N.step (cfg 0 o (true :: c :: rest) a S) =
        some (cfg 0 (some c) rest (c :: a) S) := by
    show some (TM2.stepAux (prog (Sum.inr 0)) (tm.initialState, o)
      (mk (true :: c :: rest) a S)) = _
    dsimp only [prog]
    simp [TM2.stepAux, mk, upd_inp, upd_aux, cfg]
    rfl
  have step_erase_cons (o : Option Bool) (b : Bool) (t a : List Bool) (S : ∀ k, List (tm.Γ k)) :
      N.step (cfg 1 o (b :: t) a S) = some (cfg 1 (some b) t a S) := by
    show some (TM2.stepAux (prog (Sum.inr 1)) (tm.initialState, o)
      (mk (b :: t) a S)) = _
    dsimp only [prog]
    simp [TM2.stepAux, mk, upd_inp, cfg]
    rfl
  have step_erase_nil (o : Option Bool) (a : List Bool) (S : ∀ k, List (tm.Γ k)) :
      N.step (cfg 1 o [] a S) = some (cfg 2 none [] a S) := by
    show some (TM2.stepAux (prog (Sum.inr 1)) (tm.initialState, o) (mk [] a S)) = _
    dsimp only [prog]
    simp [TM2.stepAux, mk, cfg]
    rfl
  have step_move_cons (o : Option Bool) (c : Bool) (a : List Bool) (S : ∀ k, List (tm.Γ k)) :
      N.step (cfg 2 o [] (c :: a) S) =
        some (cfg 2 (some c) [] a
          (Function.update S tm.k₀ (e.symm c :: S tm.k₀))) := by
    show some (TM2.stepAux (prog (Sum.inr 2)) (tm.initialState, o) (mk [] (c :: a) S)) = _
    dsimp only [prog]
    simp [TM2.stepAux, mk, upd_aux, upd_inr, cfg]
    rfl
  have step_move_nil (o : Option Bool) (S : ∀ k, List (tm.Γ k)) :
      N.step (cfg 2 o [] [] S) = some (liftCfg ⟨some tm.main, tm.initialState, S⟩) := by
    show some (TM2.stepAux (prog (Sum.inr 2)) (tm.initialState, o) (mk [] [] S)) = _
    dsimp only [prog]
    simp [TM2.stepAux, mk]
    rfl
  have parse_run (s : List Bool) (rest : List Bool) (a : List Bool) (o : Option Bool)
      (S : ∀ k, List (tm.Γ k)) :
      ∃ n ≤ s.length + 1, (flip bind N.step)^[n]
        (some (cfg 0 o (BitstringEncoding.delimit s ++ rest) a S)) =
        some (cfg 1 (some false) rest (s.reverse ++ a) S) := by
    induction s generalizing a o with
    | nil => exact rIn_single (step_parse_false o rest a S)
    | cons c s ih =>
      have h1 := rIn_single (step_parse_true o c (BitstringEncoding.delimit s ++ rest) a S)
      have h2 := ih (c :: a) (some c)
      have := rIn_trans h1 h2
      simpa [BitstringEncoding.delimit, List.reverse_cons, List.append_assoc, Nat.add_comm] using this
  have erase_run (t a : List Bool) (o : Option Bool) (S : ∀ k, List (tm.Γ k)) :
      ∃ n ≤ t.length + 1, (flip bind N.step)^[n] (some (cfg 1 o t a S)) =
        some (cfg 2 none [] a S) := by
    induction t generalizing o with
    | nil => exact rIn_single (step_erase_nil o a S)
    | cons b t ih =>
      have := rIn_trans (rIn_single (step_erase_cons o b t a S)) (ih (some b))
      simpa [Nat.add_comm] using this
  have move_run (a : List Bool) (o : Option Bool) (S : ∀ k, List (tm.Γ k)) :
      ∃ n ≤ a.length + 1, (flip bind N.step)^[n] (some (cfg 2 o [] a S)) =
        some (liftCfg ⟨some tm.main, tm.initialState,
          Function.update S tm.k₀ ((a.map e.symm).reverse ++ S tm.k₀)⟩) := by
    induction a generalizing o S with
    | nil =>
      simp only [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
      exact rIn_single (step_move_nil o S)
    | cons c a ih =>
      have := rIn_trans (rIn_single (step_move_cons o c a S)) (ih (some c) _)
      simp only [Function.update_self, Function.update_idem] at this
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this
  have initList_N (l : List Bool) :
      initList N l = cfg 0 none l [] (fun _ => []) := by
    simp only [initList, cfg, N]
    congr 1
    funext k
    rcases k with (_ | _) | k <;> rfl
  have initList_M (s : List (tm.Γ tm.k₀)) :
      liftCfg ⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ =
        liftCfg (initList tm s) := by
    simp only [initList]
    congr 3
    funext k
    by_cases h : k = tm.k₀
    · subst h
      simp
    · rw [Function.update_of_ne h, dif_neg h]
  have haltList_lift (s : List (tm.Γ tm.k₁)) : liftCfg (haltList tm s) = haltList N s := by
    simp only [liftCfg, haltList, N]
    congr 1
    funext k
    rcases k with (_ | _) | k
    · rfl
    · rfl
    · by_cases h : k = tm.k₁
      · subst h
        simp only [mk]
      · simp only [mk, dif_neg h]
        split
        · rename_i heq
          exact absurd (Sum.inr_injective (heq : (Sum.inr k : Bool ⊕ tm.K) = Sum.inr tm.k₁)) h
        · rfl
  have run_M {s : List (tm.Γ tm.k₀)} {out : List (tm.Γ tm.k₁)} {T : ℕ}
      (h : TM2OutputsInTime tm s (some out) T) :
      ∃ n ≤ T, (flip bind N.step)^[n] (some (liftCfg (initList tm s))) =
        some (haltList N out) := by
    obtain ⟨⟨n, hn⟩, hle⟩ := h
    refine ⟨n, hle, ?_⟩
    have := iterate_lift n (some (initList tm s))
    change (flip bind N.step)^[n] (Option.map liftCfg (some (initList tm s))) = _
    rw [this]
    refine (congrArg (Option.map liftCfg) hn).trans ?_
    show some (liftCfg (haltList tm out)) = _
    rw [haltList_lift]
  refine ⟨{ tm := N
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := M.outputAlphabet
            time := Polynomial.X + 2 + M.time
            outputsFun := fun p => ?_ }⟩
  set s := BitstringEncoding.bitEncode p.1
  set t := BitstringEncoding.bitEncode p.2
  have henc : (BitstringEncoding.toEncoding (α := α × γ)).encode p =
      BitstringEncoding.delimit s ++ t := rfl
  have hin : List.map ((Equiv.refl Bool : N.Γ N.k₀ ≃ Bool).invFun)
      ((BitstringEncoding.toEncoding (α := α × γ)).encode p) =
      BitstringEncoding.delimit s ++ t := by
    rw [henc]; exact List.map_id _
  have hrun : ∃ n ≤ (s.length + 1) + (t.length + 1) + (s.length + 1) + M.time.eval s.length,
      (flip bind N.step)^[n] (some (initList N (BitstringEncoding.delimit s ++ t))) =
        some (haltList N (List.map M.outputAlphabet.invFun
          ((BitstringEncoding.toEncoding (α := β)).encode (f p.1)))) := by
    rw [initList_N]
    have h1 := parse_run s t [] none (fun _ => [])
    have h2 := erase_run t (s.reverse ++ []) (some false) (fun _ => [])
    have h3 := move_run (s.reverse ++ []) none (fun _ => [])
    have h4 := run_M (M.outputsFun p.1)
    have hcfg : (List.map e.symm (s.reverse ++ [])).reverse ++ [] =
        List.map e.invFun s := by
      simp [List.map_reverse, e]
    rw [hcfg, initList_M] at h3
    have hlen : (s.reverse ++ []).length = s.length := by simp
    rw [hlen] at h3
    exact rIn_trans (rIn_trans (rIn_trans h1 h2) h3) h4
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
      TM2OutputsInTime N l
        (some (List.map M.outputAlphabet.invFun
          ((BitstringEncoding.toEncoding (α := β)).encode (f p.1))))
        ((Polynomial.X + 2 + M.time).eval
          ((BitstringEncoding.toEncoding (α := α × γ)).encode p).length) := by
    rintro l rfl
    exact Classical.choice (by
      obtain ⟨n, hle, he⟩ := rIn_mono hrun hb
      exact ⟨⟨⟨n, he⟩, hle⟩⟩)
  exact key _ hin

lemma p_subset_bpp : ComplexityTheory.P ⊆ ComplexityTheory.BPP := by
  intro L hL
  refine ⟨0, fun q => L q.1, comp_fst (γ := List Bool) L hL, fun x => ?_⟩
  simp
  norm_num

lemma bpp_subset_p (h1 : H1) (h2 : H2) : ComplexityTheory.BPP ⊆ ComplexityTheory.P := by
  intro L hL
  obtain ⟨p, R, hR, hacc⟩ := hL
  obtain ⟨q, G, hG, hfool⟩ := h1 p R hR
  let L' : DecisionProblem := fun x : List Bool =>
    decide (q.eval x.length <
      2 * ((Finset.range (q.eval x.length)).filter
        fun i => R (x, G (List.replicate x.length false, i)) = true).card)
  have hL' : L' ∈ ComplexityTheory.P := h2 q R G hR hG
  have hEq : L = L' := by
    funext x
    obtain ⟨hm, _, habs⟩ := hfool x
    set m : ℕ := q.eval x.length
    set N : ℕ := 2 ^ p.eval x.length
    set c : ℕ := ((Finset.range m).filter
      fun i => R (x, G (List.replicate x.length false, i)) = true).card
    set t : ℕ := (Finset.univ.filter
      fun r : Fin (p.eval x.length) → Bool => R (x, List.ofFn r) = true).card
    have hm_pos : (0 : ℚ) < m := by exact_mod_cast hm
    have hN_pos : (0 : ℚ) < N := by dsimp [N]; positivity
    have hN_cast : (N : ℚ) = 2 ^ p.eval x.length := by dsimp [N]; push_cast; rfl
    have hc_bound := abs_lt.mp habs
    cases hx : L x
    · have hfx := hacc x
      rw [hx] at hfx
      set f : ℕ := (Finset.univ.filter
        fun r : Fin (p.eval x.length) → Bool => R (x, List.ofFn r) = false).card
      have htf : t + f = N := by
        have hpred : (Finset.univ.filter
            fun r : Fin (p.eval x.length) → Bool => R (x, List.ofFn r) = false) =
            Finset.univ.filter (fun r : Fin (p.eval x.length) → Bool =>
              ¬ (R (x, List.ofFn r) = true)) := by
          ext r
          cases R (x, List.ofFn r) <;> simp
        dsimp only [t, f]
        rw [hpred, Finset.card_filter_add_card_filter_not]
        simp [N]
      have htf_q : (t : ℚ) / 2 ^ p.eval x.length + (f : ℚ) / 2 ^ p.eval x.length = 1 := by
        rw [← hN_cast, ← add_div, ← Nat.cast_add, htf, div_self hN_pos.ne']
      have hf_le : (t : ℚ) / 2 ^ p.eval x.length ≤ 1 / 3 := by linarith
      have hcm_lt : (c : ℚ) / m < 1 / 2 := by linarith [hc_bound.2]
      have h2cm : 2 * (c : ℚ) < m := by
        have h1' : (c : ℚ) < (1 / 2 : ℚ) * m := (div_lt_iff₀ hm_pos).mp hcm_lt
        linarith
      have h2cm_nat : ¬ (m < 2 * c) := by
        have : 2 * c < m := by exact_mod_cast h2cm
        omega
      simp [L', m, c, h2cm_nat]
    · have htx := hacc x
      rw [hx] at htx
      have hcm_gt : (1 : ℚ) / 2 < (c : ℚ) / m := by linarith [hc_bound.1]
      have hm2c : (m : ℚ) < 2 * (c : ℚ) := by
        have h1' : (1 / 2 : ℚ) * m < (c : ℚ) := (lt_div_iff₀ hm_pos).mp hcm_gt
        linarith
      have hm2c_nat : m < 2 * c := by exact_mod_cast hm2c
      simp [L', m, c, hm2c_nat]
  rw [hEq]
  exact hL'

theorem main : H1 → H2 → type_of% @ComplexityTheory.P_eq_BPP := by
  intro h1 h2
  exact Set.Subset.antisymm p_subset_bpp (bpp_subset_p h1 h2)

end OMA.R_ComplexityTheory_P_eq_BPP_R1
