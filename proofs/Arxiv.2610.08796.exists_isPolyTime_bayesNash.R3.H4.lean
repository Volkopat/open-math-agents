import OMAReductions.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R3

-- Step H4 of reduction R3: Quantile Multiplicative-Weight Search Engine
-- Formalizing Section 3 of Shiva Kintali, SecurityGames-short.pdf (Nov 24, 2026).

/-!
# Quantile Multiplicative-Weight Search Engine (`R3.H4`)

Given any target predicate `Good : GameInput → EquilibriumOutput → Prop` and polynomial-time
oracles `lp`, `eta`, `patLP`, `decode`, `grid`, `sweep` satisfying the fixed-witness blocker
contract of Kintali (Section 3), we construct a polynomial-time solver `solve : GameInput →
EquilibriumOutput` satisfying `∀ g, g.Valid → Good g (solve g)`.

## Architecture
1. **Core `FinTM2` combinators & binary arithmetic**: sequential composition, pairing,
   space-bounded unary iteration (`isPolyTime_iter`), 4-stack primitives, binary `ℕ`
   addition/subtraction/multiplication/division.
2. **Generic list primitives & exact LP feasibility checker**: zero-overhead `listCons`,
   1-step `listUncons`, `listAppend`, `listRev`, `listToUnary`, `listLen`, `listReplicate`,
   `listMap`, `zipMapD`, and unreduced-fraction `checkLP`.
3. **Run-length quantile table & MWU loop**: run-length weight segments `(len, wt)`,
   quantile selection `tableQuantiles`, interval doubling `doubleRuns` / `updateTable`,
   and the `R = 4 * (k + m + 1) * (bitEncode G).length` round MWU loop.
4. **Elementary integer termination proof**: discrete quantile avoidance bound
   `J * wtInterval ≤ M`, binomial bound `(J + 1)^J ≤ 3 * J^J`, and pigeonhole over
   the sparse witness `W` (`|W| ≤ k + m`).
-/

open Turing Computability ComplexityTheory StateTransition BitstringEncoding
open Arxiv.«2610.08796»

namespace OMA.Helpers

/- ## Section 1: Generic `FinTM2` Helpers and Combinators -/

section IterUtils

variable {α : Type*}

private theorem iter_none (f : α → Option α) : ∀ n, (flip bind f)^[n] none = none
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply]; exact iter_none f n

private theorem iter_step {f : α → Option α} {c : α} (n : ℕ) :
    (flip bind f)^[n + 1] (some c) = (flip bind f)^[n] (f c) := rfl

private theorem iter_succ_of {f : α → Option α} {c d : α} (h : f c = some d) (n : ℕ) :
    (flip bind f)^[n + 1] (some c) = (flip bind f)^[n] (some d) := by
  rw [iter_step, h]

private theorem iter_trans {f : α → Option α} {x y z : Option α} {a b : ℕ}
    (h1 : (flip bind f)^[a] x = y) (h2 : (flip bind f)^[b] y = z) :
    (flip bind f)^[b + a] x = z := by
  rw [Function.iterate_add_apply, h1, h2]

end IterUtils

section StmtGrowth

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

private def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => pushes q₁ + pushes q₂
  | .goto _ => 0
  | .halt => 0

private theorem len_stepAux [DecidableEq K] (k : K) (q : TM2.Stmt Γ Λ σ) :
    ∀ (v : σ) (S : ∀ k, List (Γ k)),
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q with
  | push k' f q ih =>
    intro v S
    have h1 := ih v (Function.update S k' (f v :: S k'))
    have h2 : (Function.update S k' (f v :: S k') k).length ≤ (S k).length + 1 := by
      by_cases hk : k = k'
      · subst hk; simp
      · rw [Function.update_of_ne hk]; omega
    simp only [TM2.stepAux, pushes]
    omega
  | peek k' f q ih =>
    intro v S; simp only [TM2.stepAux, pushes]; exact ih _ _
  | pop k' f q ih =>
    intro v S
    have h1 := ih (f v (S k').head?) (Function.update S k' (S k').tail)
    have h2 : (Function.update S k' (S k').tail k).length ≤ (S k).length := by
      by_cases hk : k = k'
      · subst hk; simp
      · rw [Function.update_of_ne hk]
    simp only [TM2.stepAux, pushes]
    omega
  | load a q ih =>
    intro v S; simp only [TM2.stepAux, pushes]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S
    have h1 := ih₁ v S
    have h2 := ih₂ v S
    simp only [TM2.stepAux, pushes]
    cases f v
    · simp only [cond_false]; omega
    · simp only [cond_true]; omega
  | goto f => intro v S; simp [TM2.stepAux, pushes]
  | halt => intro v S; simp [TM2.stepAux, pushes]

private theorem len_step [DecidableEq K] (M : Λ → TM2.Stmt Γ Λ σ) (B : ℕ)
    (hB : ∀ l, pushes (M l) ≤ B) (k : K) {c d : TM2.Cfg Γ Λ σ}
    (h : TM2.step M c = some d) :
    (d.stk k).length ≤ (c.stk k).length + B := by
  rcases c with ⟨_ | l, v, S⟩
  · simp at h
  · simp only [TM2.step, Option.some.injEq] at h
    subst h
    have h1 := len_stepAux k (M l) v S
    have h2 := hB l
    simp only at h1 ⊢
    omega

private theorem len_run [DecidableEq K] (M : Λ → TM2.Stmt Γ Λ σ) (B : ℕ)
    (hB : ∀ l, pushes (M l) ≤ B) (k : K) :
    ∀ (n : ℕ) (c d : TM2.Cfg Γ Λ σ),
    (flip bind (TM2.step M))^[n] (some c) = some d →
    (d.stk k).length ≤ (c.stk k).length + B * n
  | 0, c, d, h => by
    simp only [Function.iterate_zero, id, Option.some.injEq] at h
    subst h; simp
  | n + 1, c, d, h => by
    cases hc : TM2.step M c with
    | none =>
      rw [Function.iterate_succ_apply] at h
      change (flip bind (TM2.step M))^[n] (TM2.step M c) = some d at h
      rw [hc, iter_none] at h; cases h
    | some c' =>
      rw [iter_succ_of hc] at h
      have h1 := len_run M B hB k n c' d h
      have h2 := len_step M B hB k hc
      rw [Nat.mul_succ]; omega

end StmtGrowth

private theorem poly_mono (p : Polynomial ℕ) {a b : ℕ} (hab : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval_add, Polynomial.eval_add]; exact Nat.add_le_add hp hq
  | monomial n c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab n)

section InitHaltHelpers

variable (tm : FinTM2)

private theorem halt_k1 (X : List (tm.Γ tm.k₁)) : (haltList tm X).stk tm.k₁ = X := by
  simp [haltList]

private theorem halt_ne (X : List (tm.Γ tm.k₁)) (k : tm.K) (h : k ≠ tm.k₁) :
    (haltList tm X).stk k = [] := by
  simp [haltList, h]

private theorem halt_upd [DecidableEq tm.K] (X : List (tm.Γ tm.k₁)) :
    Function.update (haltList tm X).stk tm.k₁ [] = fun k => ([] : List (tm.Γ k)) := by
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · rw [Function.update_of_ne h]; simp [haltList, h]

private theorem init_k0 (X : List (tm.Γ tm.k₀)) : (initList tm X).stk tm.k₀ = X := by
  simp [initList]

private theorem init_ne (X : List (tm.Γ tm.k₀)) (k : tm.K) (h : k ≠ tm.k₀) :
    (initList tm X).stk k = [] := by
  simp [initList, h]

private theorem init_upd [DecidableEq tm.K] (X : List (tm.Γ tm.k₀)) :
    Function.update (fun k => ([] : List (tm.Γ k))) tm.k₀ X = (initList tm X).stk := by
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp [initList]
  · rw [Function.update_of_ne h]; simp [initList, h]

private theorem init_len (X : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((initList tm X).stk k).length ≤ X.length := by
  by_cases h : k = tm.k₀
  · subst h; simp [initList]
  · simp [initList, h]

end InitHaltHelpers

private theorem delim_map {Γ : Type} (g : Bool → Γ) (O : List Bool) : ∀ I : List Bool,
    I.flatMap (fun b => [g true, g b]) ++ g false :: O.map g =
      (BitstringEncoding.delimit I ++ O).map g
  | [] => rfl
  | b :: I => by
    show g true :: g b :: (I.flatMap (fun b => [g true, g b]) ++ g false :: O.map g) =
      g true :: g b :: (BitstringEncoding.delimit I ++ O).map g
    rw [delim_map g O I]

/- ### Sequential Composition (`isPolyTime_seq`) and Pairing (`isPolyTime_pair`) -/

private inductive Aux2
  | main
  | tmp
  | tmp2
  | save
  deriving DecidableEq

private instance : Fintype Aux2 :=
  ⟨{Aux2.main, Aux2.tmp, Aux2.tmp2, Aux2.save}, by intro x; cases x <;> simp⟩

private inductive Ph2
  | copy
  | feed
  | unload
  | load
  | out_sep
  | out_delim
  deriving DecidableEq

private instance : Fintype Ph2 :=
  ⟨{Ph2.copy, Ph2.feed, Ph2.unload, Ph2.load, Ph2.out_sep, Ph2.out_delim}, by
    intro x; cases x <;> simp⟩

section PairSeqMachine

variable (Mf Mg : FinTM2)

private abbrev KK2 : Type := Aux2 ⊕ (Mf.K ⊕ Mg.K)

private abbrev G2 : KK2 Mf Mg → Type := fun k =>
  Sum.casesOn (motive := fun _ => Type) k (fun _ => Bool)
    (fun k' => Sum.casesOn (motive := fun _ => Type) k' Mf.Γ Mg.Γ)

private abbrev Lab2 : Type := (Mf.Λ ⊕ Mg.Λ) ⊕ Ph2

private abbrev Var2 : Type := Mf.σ × Mg.σ × Option Bool

private def emb2 (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (Sg : ∀ k, List (Mg.Γ k)) :
    ∀ k, List (G2 Mf Mg k)
  | Sum.inl Aux2.main => a
  | Sum.inl Aux2.tmp => b
  | Sum.inl Aux2.tmp2 => c
  | Sum.inl Aux2.save => d
  | Sum.inr (Sum.inl k) => Sf k
  | Sum.inr (Sum.inr k) => Sg k

@[simp] private theorem emb2_main (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sg : ∀ k, List (Mg.Γ k)) : emb2 Mf Mg a b c d Sf Sg (Sum.inl Aux2.main) = a := rfl
@[simp] private theorem emb2_tmp (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sg : ∀ k, List (Mg.Γ k)) : emb2 Mf Mg a b c d Sf Sg (Sum.inl Aux2.tmp) = b := rfl
@[simp] private theorem emb2_tmp2 (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sg : ∀ k, List (Mg.Γ k)) : emb2 Mf Mg a b c d Sf Sg (Sum.inl Aux2.tmp2) = c := rfl
@[simp] private theorem emb2_save (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sg : ∀ k, List (Mg.Γ k)) : emb2 Mf Mg a b c d Sf Sg (Sum.inl Aux2.save) = d := rfl
@[simp] private theorem emb2_f (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sg : ∀ k, List (Mg.Γ k)) (k : Mf.K) :
    emb2 Mf Mg a b c d Sf Sg (Sum.inr (Sum.inl k)) = Sf k := rfl
@[simp] private theorem emb2_g (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sg : ∀ k, List (Mg.Γ k)) (k : Mg.K) :
    emb2 Mf Mg a b c d Sf Sg (Sum.inr (Sum.inr k)) = Sg k := rfl

section Upd2
variable [DecidableEq (KK2 Mf Mg)]

private theorem upd2_main (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (Sg : ∀ k, List (Mg.Γ k))
    (l : List (G2 Mf Mg (Sum.inl Aux2.main))) :
    Function.update (emb2 Mf Mg a b c d Sf Sg) (Sum.inl Aux2.main) l =
      emb2 Mf Mg l b c d Sf Sg := by
  funext k; match k with
  | Sum.inl Aux2.main => simp
  | Sum.inl Aux2.tmp => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux2.tmp2 => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux2.save => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inl k) => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inr k) => rw [Function.update_of_ne (by simp)]; rfl

private theorem upd2_tmp (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (Sg : ∀ k, List (Mg.Γ k))
    (l : List (G2 Mf Mg (Sum.inl Aux2.tmp))) :
    Function.update (emb2 Mf Mg a b c d Sf Sg) (Sum.inl Aux2.tmp) l =
      emb2 Mf Mg a l c d Sf Sg := by
  funext k; match k with
  | Sum.inl Aux2.main => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux2.tmp => simp
  | Sum.inl Aux2.tmp2 => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux2.save => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inl k) => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inr k) => rw [Function.update_of_ne (by simp)]; rfl

private theorem upd2_tmp2 (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (Sg : ∀ k, List (Mg.Γ k))
    (l : List (G2 Mf Mg (Sum.inl Aux2.tmp2))) :
    Function.update (emb2 Mf Mg a b c d Sf Sg) (Sum.inl Aux2.tmp2) l =
      emb2 Mf Mg a b l d Sf Sg := by
  funext k; match k with
  | Sum.inl Aux2.main => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux2.tmp => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux2.tmp2 => simp
  | Sum.inl Aux2.save => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inl k) => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inr k) => rw [Function.update_of_ne (by simp)]; rfl

private theorem upd2_save (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (Sg : ∀ k, List (Mg.Γ k))
    (l : List (G2 Mf Mg (Sum.inl Aux2.save))) :
    Function.update (emb2 Mf Mg a b c d Sf Sg) (Sum.inl Aux2.save) l =
      emb2 Mf Mg a b c l Sf Sg := by
  funext k; match k with
  | Sum.inl Aux2.main => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux2.tmp => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux2.tmp2 => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux2.save => simp
  | Sum.inr (Sum.inl k) => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inr k) => rw [Function.update_of_ne (by simp)]; rfl

private theorem upd2_f [DecidableEq Mf.K] (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sg : ∀ k, List (Mg.Γ k)) (k : Mf.K) (l : List (Mf.Γ k)) :
    Function.update (emb2 Mf Mg a b c d Sf Sg) (Sum.inr (Sum.inl k)) l =
      emb2 Mf Mg a b c d (Function.update Sf k l) Sg := by
  funext j; match j with
  | Sum.inl Aux2.main => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux2.tmp => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux2.tmp2 => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux2.save => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inl j) =>
    by_cases h : j = k
    · subst h; simp
    · rw [Function.update_of_ne (by simpa using h)]
      show Sf j = Function.update Sf k l j
      rw [Function.update_of_ne h]
  | Sum.inr (Sum.inr j) => rw [Function.update_of_ne (by simp)]; rfl

private theorem upd2_g [DecidableEq Mg.K] (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sg : ∀ k, List (Mg.Γ k)) (k : Mg.K) (l : List (Mg.Γ k)) :
    Function.update (emb2 Mf Mg a b c d Sf Sg) (Sum.inr (Sum.inr k)) l =
      emb2 Mf Mg a b c d Sf (Function.update Sg k l) := by
  funext j; match j with
  | Sum.inl Aux2.main => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux2.tmp => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux2.tmp2 => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux2.save => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inl j) => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inr j) =>
    by_cases h : j = k
    · subst h; simp
    · rw [Function.update_of_ne (by simpa using h)]
      show Sg j = Function.update Sg k l j
      rw [Function.update_of_ne h]

end Upd2

private def liftF2 : TM2.Stmt Mf.Γ Mf.Λ Mf.σ → TM2.Stmt (G2 Mf Mg) (Lab2 Mf Mg) (Var2 Mf Mg)
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun v => f v.1) (liftF2 q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun v o => (f v.1 o, v.2)) (liftF2 q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun v o => (f v.1 o, v.2)) (liftF2 q)
  | .load a q => .load (fun v => (a v.1, v.2)) (liftF2 q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (liftF2 q₁) (liftF2 q₂)
  | .goto f => .goto (fun v => Sum.inl (Sum.inl (f v.1)))
  | .halt => .goto (fun _ => Sum.inr Ph2.unload)

private def liftG2 (pair : Bool) :
    TM2.Stmt Mg.Γ Mg.Λ Mg.σ → TM2.Stmt (G2 Mf Mg) (Lab2 Mf Mg) (Var2 Mf Mg)
  | .push k f q => .push (Sum.inr (Sum.inr k)) (fun v => f v.2.1) (liftG2 pair q)
  | .peek k f q => .peek (Sum.inr (Sum.inr k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftG2 pair q)
  | .pop k f q => .pop (Sum.inr (Sum.inr k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftG2 pair q)
  | .load a q => .load (fun v => (v.1, a v.2.1, v.2.2)) (liftG2 pair q)
  | .branch f q₁ q₂ => .branch (fun v => f v.2.1) (liftG2 pair q₁) (liftG2 pair q₂)
  | .goto f => .goto (fun v => Sum.inl (Sum.inr (f v.2.1)))
  | .halt => if pair then .goto (fun _ => Sum.inr Ph2.out_sep) else .halt

private def liftCfgF2 (sg : Mg.σ) (o : Option Bool) (a b c d : List Bool) (Sg : ∀ k, List (Mg.Γ k))
    (cf : TM2.Cfg Mf.Γ Mf.Λ Mf.σ) : TM2.Cfg (G2 Mf Mg) (Lab2 Mf Mg) (Var2 Mf Mg) :=
  ⟨some (cf.l.elim (Sum.inr Ph2.unload) fun l => Sum.inl (Sum.inl l)), (cf.var, sg, o),
    emb2 Mf Mg a b c d cf.stk Sg⟩

private def liftCfgG2 (pair : Bool) (sf : Mf.σ) (o : Option Bool) (a b c d : List Bool)
    (Sf : ∀ k, List (Mf.Γ k)) (cg : TM2.Cfg Mg.Γ Mg.Λ Mg.σ) :
    TM2.Cfg (G2 Mf Mg) (Lab2 Mf Mg) (Var2 Mf Mg) :=
  ⟨if pair then some (cg.l.elim (Sum.inr Ph2.out_sep) fun l => Sum.inl (Sum.inr l))
   else cg.l.map fun l => Sum.inl (Sum.inr l),
    (sf, cg.var, o), emb2 Mf Mg a b c d Sf cg.stk⟩

private theorem stepAux_liftF2 [DecidableEq (KK2 Mf Mg)] [DecidableEq Mf.K] (sg : Mg.σ)
    (o : Option Bool) (a b c d : List Bool) (Sg : ∀ k, List (Mg.Γ k))
    (q : TM2.Stmt Mf.Γ Mf.Λ Mf.σ) :
    ∀ (v : Mf.σ) (S : ∀ k, List (Mf.Γ k)),
    TM2.stepAux (liftF2 Mf Mg q) (v, sg, o) (emb2 Mf Mg a b c d S Sg) =
      liftCfgF2 Mf Mg sg o a b c d Sg (TM2.stepAux q v S) := by
  induction q with
  | push k f q ih =>
    intro v S; simp only [liftF2, TM2.stepAux]
    rw [show emb2 Mf Mg a b c d S Sg (Sum.inr (Sum.inl k)) = S k from rfl, upd2_f]; exact ih _ _
  | peek k f q ih => intro v S; simp only [liftF2, TM2.stepAux]; exact ih _ _
  | pop k f q ih =>
    intro v S; simp only [liftF2, TM2.stepAux]
    rw [show emb2 Mf Mg a b c d S Sg (Sum.inr (Sum.inl k)) = S k from rfl, upd2_f]; exact ih _ _
  | load f q ih => intro v S; simp only [liftF2, TM2.stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S; simp only [liftF2, TM2.stepAux]; cases f v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f => intro v S; rfl
  | halt => intro v S; rfl

private theorem stepAux_liftG2 [DecidableEq (KK2 Mf Mg)] [DecidableEq Mg.K] (pair : Bool)
    (sf : Mf.σ) (o : Option Bool) (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (q : TM2.Stmt Mg.Γ Mg.Λ Mg.σ) :
    ∀ (v : Mg.σ) (S : ∀ k, List (Mg.Γ k)),
    TM2.stepAux (liftG2 Mf Mg pair q) (sf, v, o) (emb2 Mf Mg a b c d Sf S) =
      liftCfgG2 Mf Mg pair sf o a b c d Sf (TM2.stepAux q v S) := by
  induction q with
  | push k f q ih =>
    intro v S; simp only [liftG2, TM2.stepAux]
    rw [show emb2 Mf Mg a b c d Sf S (Sum.inr (Sum.inr k)) = S k from rfl, upd2_g]; exact ih _ _
  | peek k f q ih => intro v S; simp only [liftG2, TM2.stepAux]; exact ih _ _
  | pop k f q ih =>
    intro v S; simp only [liftG2, TM2.stepAux]
    rw [show emb2 Mf Mg a b c d Sf S (Sum.inr (Sum.inr k)) = S k from rfl, upd2_g]; exact ih _ _
  | load f q ih => intro v S; simp only [liftG2, TM2.stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S; simp only [liftG2, TM2.stepAux]; cases f v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f => intro v S; cases pair <;> rfl
  | halt => intro v S; cases pair <;> rfl

variable (ef : Mf.Γ Mf.k₀ ≃ Bool) (of : Mf.Γ Mf.k₁ ≃ Bool)
  (eg : Mg.Γ Mg.k₀ ≃ Bool) (og : Mg.Γ Mg.k₁ ≃ Bool)

/-- Unified program for sequential composition (`pair = false`: `g ∘ f`) and pairing
(`pair = true`: `x ↦ (f x, g x)`). -/
private def prog2 (pair : Bool) : Lab2 Mf Mg → TM2.Stmt (G2 Mf Mg) (Lab2 Mf Mg) (Var2 Mf Mg)
  | Sum.inl (Sum.inl l) => liftF2 Mf Mg (Mf.m l)
  | Sum.inl (Sum.inr l) => liftG2 Mf Mg pair (Mg.m l)
  | Sum.inr Ph2.copy =>
    .pop (Sum.inl Aux2.main) (fun v o => (v.1, v.2.1, o)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inl Aux2.tmp) (fun v => v.2.2.getD false) <|
          .push (Sum.inl Aux2.tmp2) (fun v => v.2.2.getD false) (.goto fun _ => Sum.inr Ph2.copy))
        (.goto fun _ => Sum.inr Ph2.feed)
  | Sum.inr Ph2.feed =>
    .pop (Sum.inl Aux2.tmp) (fun v o => (v.1, v.2.1, o)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inr (Sum.inl Mf.k₀)) (fun v => ef.symm (v.2.2.getD false))
          (.goto fun _ => Sum.inr Ph2.feed))
        (.goto fun _ => Sum.inl (Sum.inl Mf.main))
  | Sum.inr Ph2.unload =>
    .pop (Sum.inr (Sum.inl Mf.k₁)) (fun v o => (v.1, v.2.1, o.map of)) <|
      .branch (fun v => v.2.2.isSome)
        (if pair then
          .push (Sum.inl Aux2.save) (fun v => v.2.2.getD false) (.goto fun _ => Sum.inr Ph2.unload)
        else
          .push (Sum.inl Aux2.tmp) (fun v => v.2.2.getD false) (.goto fun _ => Sum.inr Ph2.unload))
        (.goto fun _ => Sum.inr Ph2.load)
  | Sum.inr Ph2.load =>
    if pair then
      .pop (Sum.inl Aux2.tmp2) (fun v o => (v.1, v.2.1, o)) <|
        .branch (fun v => v.2.2.isSome)
          (.push (Sum.inr (Sum.inr Mg.k₀)) (fun v => eg.symm (v.2.2.getD false))
            (.goto fun _ => Sum.inr Ph2.load))
          (.goto fun _ => Sum.inl (Sum.inr Mg.main))
    else
      .pop (Sum.inl Aux2.tmp) (fun v o => (v.1, v.2.1, o)) <|
        .branch (fun v => v.2.2.isSome)
          (.push (Sum.inr (Sum.inr Mg.k₀)) (fun v => eg.symm (v.2.2.getD false))
            (.goto fun _ => Sum.inr Ph2.load))
          (.goto fun _ => Sum.inl (Sum.inr Mg.main))
  | Sum.inr Ph2.out_sep =>
    .push (Sum.inr (Sum.inr Mg.k₁)) (fun _ => og.symm false)
      (.goto fun _ => Sum.inr Ph2.out_delim)
  | Sum.inr Ph2.out_delim =>
    .pop (Sum.inl Aux2.save) (fun v o => (v.1, v.2.1, o)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inr (Sum.inr Mg.k₁)) (fun v => og.symm (v.2.2.getD false)) <|
          .push (Sum.inr (Sum.inr Mg.k₁)) (fun _ => og.symm true)
            (.goto fun _ => Sum.inr Ph2.out_delim))
        .halt

private def NSeq : FinTM2 :=
  letI := Mf.kFin; letI := Mg.kFin; letI := Mf.ΛFin; letI := Mg.ΛFin
  letI := Mf.σFin; letI := Mg.σFin
  { K := KK2 Mf Mg, k₀ := Sum.inr (Sum.inl Mf.k₀), k₁ := Sum.inr (Sum.inr Mg.k₁),
    Γ := G2 Mf Mg, Λ := Lab2 Mf Mg, main := Sum.inl (Sum.inl Mf.main),
    σ := Var2 Mf Mg, initialState := (Mf.initialState, Mg.initialState, none),
    Γk₀Fin := Mf.Γk₀Fin, m := prog2 Mf Mg ef of eg og false }

private def NPair : FinTM2 :=
  letI := Mf.kFin; letI := Mg.kFin; letI := Mf.ΛFin; letI := Mg.ΛFin
  letI := Mf.σFin; letI := Mg.σFin
  { K := KK2 Mf Mg, k₀ := Sum.inl Aux2.main, k₁ := Sum.inr (Sum.inr Mg.k₁),
    Γ := G2 Mf Mg, Λ := Lab2 Mf Mg, main := Sum.inr Ph2.copy,
    σ := Var2 Mf Mg, initialState := (Mf.initialState, Mg.initialState, none),
    Γk₀Fin := inferInstanceAs (Fintype Bool), m := prog2 Mf Mg ef of eg og true }

section Runs2
variable [DecidableEq (KK2 Mf Mg)]

private theorem copy2_run (pair : Bool) (sf : Mf.σ) (sg : Mg.σ) (Sf : ∀ k, List (Mf.Γ k))
    (Sg : ∀ k, List (Mg.Γ k)) :
    ∀ (l t t2 sv : List Bool) (o : Option Bool),
    (flip bind (TM2.step (prog2 Mf Mg ef of eg og pair)))^[l.length + 1]
      (some ⟨some (Sum.inr Ph2.copy), (sf, sg, o), emb2 Mf Mg l t t2 sv Sf Sg⟩) =
    some ⟨some (Sum.inr Ph2.feed), (sf, sg, none),
      emb2 Mf Mg [] (l.reverse ++ t) (l.reverse ++ t2) sv Sf Sg⟩
  | [], t, t2, sv, o => by
    rw [List.length_nil, iter_step]; simp [prog2, upd2_main]
  | x :: l, t, t2, sv, o => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog2, upd2_main, upd2_tmp, upd2_tmp2]); rw [copy2_run pair sf sg Sf Sg l (x :: t) (x :: t2) sv (some x)]
    simp

private theorem feed2_run [DecidableEq Mf.K] (pair : Bool) (sf : Mf.σ) (sg : Mg.σ)
    (Sg : ∀ k, List (Mg.Γ k)) :
    ∀ (t m t2 sv : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (o : Option Bool),
    (flip bind (TM2.step (prog2 Mf Mg ef of eg og pair)))^[t.length + 1]
      (some ⟨some (Sum.inr Ph2.feed), (sf, sg, o), emb2 Mf Mg m t t2 sv Sf Sg⟩) =
    some ⟨some (Sum.inl (Sum.inl Mf.main)), (sf, sg, none),
      emb2 Mf Mg m [] t2 sv (Function.update Sf Mf.k₀ (t.reverse.map ef.symm ++ Sf Mf.k₀)) Sg⟩
  | [], m, t2, sv, Sf, o => by
    rw [List.length_nil, iter_step]; simp [prog2, upd2_tmp]
  | y :: t, m, t2, sv, Sf, o => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog2, upd2_tmp, upd2_f]); rw [feed2_run pair sf sg Sg t m t2 sv _ (some y)]
    simp [Function.update_idem]

private theorem unload2_run_false [DecidableEq Mf.K] (sf : Mf.σ) (sg : Mg.σ)
    (Sg : ∀ k, List (Mg.Γ k)) :
    ∀ (L : List (Mf.Γ Mf.k₁)) (m t t2 sv : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (o : Option Bool),
    Sf Mf.k₁ = L →
    (flip bind (TM2.step (prog2 Mf Mg ef of eg og false)))^[L.length + 1]
      (some ⟨some (Sum.inr Ph2.unload), (sf, sg, o), emb2 Mf Mg m t t2 sv Sf Sg⟩) =
    some ⟨some (Sum.inr Ph2.load), (sf, sg, none),
      emb2 Mf Mg m (L.reverse.map of ++ t) t2 sv (Function.update Sf Mf.k₁ []) Sg⟩
  | [], m, t, t2, sv, Sf, o, hS => by
    rw [List.length_nil, iter_step]; simp [prog2, hS, upd2_f]
  | y :: L, m, t, t2, sv, Sf, o, hS => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog2, hS, upd2_tmp, upd2_f]); rw [unload2_run_false sf sg Sg L m (of y :: t) t2 sv _ (some (of y)) (by simp)]
    simp [Function.update_idem]

private theorem unload2_run_true [DecidableEq Mf.K] (sf : Mf.σ) (sg : Mg.σ)
    (Sg : ∀ k, List (Mg.Γ k)) :
    ∀ (L : List (Mf.Γ Mf.k₁)) (m t t2 sv : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (o : Option Bool),
    Sf Mf.k₁ = L →
    (flip bind (TM2.step (prog2 Mf Mg ef of eg og true)))^[L.length + 1]
      (some ⟨some (Sum.inr Ph2.unload), (sf, sg, o), emb2 Mf Mg m t t2 sv Sf Sg⟩) =
    some ⟨some (Sum.inr Ph2.load), (sf, sg, none),
      emb2 Mf Mg m t t2 (L.reverse.map of ++ sv) (Function.update Sf Mf.k₁ []) Sg⟩
  | [], m, t, t2, sv, Sf, o, hS => by
    rw [List.length_nil, iter_step]; simp [prog2, hS, upd2_f]
  | y :: L, m, t, t2, sv, Sf, o, hS => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog2, hS, upd2_save, upd2_f]); rw [unload2_run_true sf sg Sg L m t t2 (of y :: sv) _ (some (of y)) (by simp)]
    simp [Function.update_idem]

private theorem load2_run_false [DecidableEq Mg.K] (sf : Mf.σ) (sg : Mg.σ)
    (Sf : ∀ k, List (Mf.Γ k)) :
    ∀ (t m t2 sv : List Bool) (Sg : ∀ k, List (Mg.Γ k)) (o : Option Bool),
    (flip bind (TM2.step (prog2 Mf Mg ef of eg og false)))^[t.length + 1]
      (some ⟨some (Sum.inr Ph2.load), (sf, sg, o), emb2 Mf Mg m t t2 sv Sf Sg⟩) =
    some ⟨some (Sum.inl (Sum.inr Mg.main)), (sf, sg, none),
      emb2 Mf Mg m [] t2 sv Sf (Function.update Sg Mg.k₀ (t.reverse.map eg.symm ++ Sg Mg.k₀))⟩
  | [], m, t2, sv, Sg, o => by
    rw [List.length_nil, iter_step]; simp [prog2, upd2_tmp]
  | y :: t, m, t2, sv, Sg, o => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog2, upd2_tmp, upd2_g]); rw [load2_run_false sf sg Sf t m t2 sv _ (some y)]
    simp [Function.update_idem]

private theorem load2_run_true [DecidableEq Mg.K] (sf : Mf.σ) (sg : Mg.σ)
    (Sf : ∀ k, List (Mf.Γ k)) :
    ∀ (t2 m t sv : List Bool) (Sg : ∀ k, List (Mg.Γ k)) (o : Option Bool),
    (flip bind (TM2.step (prog2 Mf Mg ef of eg og true)))^[t2.length + 1]
      (some ⟨some (Sum.inr Ph2.load), (sf, sg, o), emb2 Mf Mg m t t2 sv Sf Sg⟩) =
    some ⟨some (Sum.inl (Sum.inr Mg.main)), (sf, sg, none),
      emb2 Mf Mg m t [] sv Sf (Function.update Sg Mg.k₀ (t2.reverse.map eg.symm ++ Sg Mg.k₀))⟩
  | [], m, t, sv, Sg, o => by
    rw [List.length_nil, iter_step]; simp [prog2, upd2_tmp2]
  | y :: t2, m, t, sv, Sg, o => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog2, upd2_tmp2, upd2_g]); rw [load2_run_true sf sg Sf t2 m t sv _ (some y)]
    simp [Function.update_idem]

private theorem out_delim2_run [DecidableEq Mg.K] (pair : Bool) (sf : Mf.σ) (sg : Mg.σ)
    (Sf : ∀ k, List (Mf.Γ k)) :
    ∀ (sv m t t2 : List Bool) (Sg : ∀ k, List (Mg.Γ k)) (o : Option Bool),
    (flip bind (TM2.step (prog2 Mf Mg ef of eg og pair)))^[sv.length + 1]
      (some ⟨some (Sum.inr Ph2.out_delim), (sf, sg, o), emb2 Mf Mg m t t2 sv Sf Sg⟩) =
    some ⟨none, (sf, sg, none),
      emb2 Mf Mg m t t2 [] Sf
        (Function.update Sg Mg.k₁
          (sv.reverse.flatMap (fun b => [og.symm true, og.symm b]) ++ Sg Mg.k₁))⟩
  | [], m, t, t2, Sg, o => by
    rw [List.length_nil, iter_step]; simp [prog2, upd2_save]
  | y :: sv, m, t, t2, Sg, o => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog2, upd2_save, upd2_g]); rw [out_delim2_run pair sf sg Sf sv m t t2 _ (some y)]
    simp [Function.update_idem]

private theorem lift_stepF2 [DecidableEq Mf.K] (pair : Bool) (sg : Mg.σ) (o : Option Bool)
    (a b c d : List Bool) (Sg : ∀ k, List (Mg.Γ k)) {cf df : TM2.Cfg Mf.Γ Mf.Λ Mf.σ}
    (h : TM2.step Mf.m cf = some df) :
    TM2.step (prog2 Mf Mg ef of eg og pair) (liftCfgF2 Mf Mg sg o a b c d Sg cf) =
      some (liftCfgF2 Mf Mg sg o a b c d Sg df) := by
  rcases cf with ⟨_ | l, v, S⟩
  · simp at h
  · simp only [TM2.step] at h; cases h
    show some (TM2.stepAux (liftF2 Mf Mg (Mf.m l)) (v, sg, o) (emb2 Mf Mg a b c d S Sg)) = _
    rw [stepAux_liftF2]

private theorem lift_runF2 [DecidableEq Mf.K] (pair : Bool) (sg : Mg.σ) (o : Option Bool)
    (a b c d : List Bool) (Sg : ∀ k, List (Mg.Γ k)) :
    ∀ (n : ℕ) (cf df : TM2.Cfg Mf.Γ Mf.Λ Mf.σ),
    (flip bind (TM2.step Mf.m))^[n] (some cf) = some df →
    (flip bind (TM2.step (prog2 Mf Mg ef of eg og pair)))^[n]
        (some (liftCfgF2 Mf Mg sg o a b c d Sg cf)) =
      some (liftCfgF2 Mf Mg sg o a b c d Sg df)
  | 0, cf, df, h => by simp only [Function.iterate_zero, id, Option.some.injEq] at h ⊢; rw [h]
  | n + 1, cf, df, h => by
    cases hc : TM2.step Mf.m cf with
    | none =>
      rw [Function.iterate_succ_apply] at h
      change (flip bind (TM2.step Mf.m))^[n] (TM2.step Mf.m cf) = some df at h
      rw [hc, iter_none] at h; cases h
    | some cf' =>
      rw [iter_succ_of hc] at h
      rw [iter_succ_of (lift_stepF2 Mf Mg ef of eg og pair sg o a b c d Sg hc)]
      exact lift_runF2 pair sg o a b c d Sg n cf' df h

private theorem lift_stepG2 [DecidableEq Mg.K] (pair : Bool) (sf : Mf.σ) (o : Option Bool)
    (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k)) {cg dg : TM2.Cfg Mg.Γ Mg.Λ Mg.σ}
    (h : TM2.step Mg.m cg = some dg) :
    TM2.step (prog2 Mf Mg ef of eg og pair) (liftCfgG2 Mf Mg pair sf o a b c d Sf cg) =
      some (liftCfgG2 Mf Mg pair sf o a b c d Sf dg) := by
  rcases cg with ⟨_ | l, v, S⟩
  · simp at h
  · simp only [TM2.step] at h; cases h
    have hstep : TM2.step (prog2 Mf Mg ef of eg og pair)
        (liftCfgG2 Mf Mg pair sf o a b c d Sf ⟨some l, v, S⟩) =
        some (TM2.stepAux (liftG2 Mf Mg pair (Mg.m l)) (sf, v, o) (emb2 Mf Mg a b c d Sf S)) := by
      cases pair <;> rfl
    rw [hstep, stepAux_liftG2]

private theorem lift_runG2 [DecidableEq Mg.K] (pair : Bool) (sf : Mf.σ) (o : Option Bool)
    (a b c d : List Bool) (Sf : ∀ k, List (Mf.Γ k)) :
    ∀ (n : ℕ) (cg dg : TM2.Cfg Mg.Γ Mg.Λ Mg.σ),
    (flip bind (TM2.step Mg.m))^[n] (some cg) = some dg →
    (flip bind (TM2.step (prog2 Mf Mg ef of eg og pair)))^[n]
        (some (liftCfgG2 Mf Mg pair sf o a b c d Sf cg)) =
      some (liftCfgG2 Mf Mg pair sf o a b c d Sf dg)
  | 0, cg, dg, h => by simp only [Function.iterate_zero, id, Option.some.injEq] at h ⊢; rw [h]
  | n + 1, cg, dg, h => by
    cases hc : TM2.step Mg.m cg with
    | none =>
      rw [Function.iterate_succ_apply] at h
      change (flip bind (TM2.step Mg.m))^[n] (TM2.step Mg.m cg) = some dg at h
      rw [hc, iter_none] at h; cases h
    | some cg' =>
      rw [iter_succ_of hc] at h
      rw [iter_succ_of (lift_stepG2 Mf Mg ef of eg og pair sf o a b c d Sf hc)]
      exact lift_runG2 pair sf o a b c d Sf n cg' dg h

end Runs2

private theorem init_NSeq2 (X : List (Mf.Γ Mf.k₀)) :
    initList (NSeq Mf Mg ef of eg og) X =
      liftCfgF2 Mf Mg Mg.initialState none [] [] [] [] (fun k => ([] : List (Mg.Γ k)))
        (initList Mf X) := by
  have hstk : (initList (NSeq Mf Mg ef of eg og) X).stk =
      emb2 Mf Mg [] [] [] [] (initList Mf X).stk (fun k => ([] : List (Mg.Γ k))) := by
    funext k; match k with
    | Sum.inl Aux2.main => exact init_ne (NSeq Mf Mg ef of eg og) X _ (by intro h; cases h)
    | Sum.inl Aux2.tmp => exact init_ne (NSeq Mf Mg ef of eg og) X _ (by intro h; cases h)
    | Sum.inl Aux2.tmp2 => exact init_ne (NSeq Mf Mg ef of eg og) X _ (by intro h; cases h)
    | Sum.inl Aux2.save => exact init_ne (NSeq Mf Mg ef of eg og) X _ (by intro h; cases h)
    | Sum.inr (Sum.inl k) =>
      by_cases hk : k = Mf.k₀
      · subst hk; rw [emb2_f, init_k0]; exact init_k0 (NSeq Mf Mg ef of eg og) X
      · rw [emb2_f, init_ne Mf X k hk]
        exact init_ne (NSeq Mf Mg ef of eg og) X _ (fun h => hk (Sum.inl.inj (Sum.inr.inj h)))
    | Sum.inr (Sum.inr k) => exact init_ne (NSeq Mf Mg ef of eg og) X _ (by intro h; cases h)
  show TM2.Cfg.mk _ _ (initList (NSeq Mf Mg ef of eg og) X).stk = _
  rw [hstk]; rfl

private theorem halt_NSeq2 (R : List (Mg.Γ Mg.k₁)) :
    haltList (NSeq Mf Mg ef of eg og) R =
      TM2.Cfg.mk none (Mf.initialState, Mg.initialState, none)
        (emb2 Mf Mg [] [] [] [] (fun k => ([] : List (Mf.Γ k))) (haltList Mg R).stk) := by
  have hstk : (haltList (NSeq Mf Mg ef of eg og) R).stk =
      emb2 Mf Mg [] [] [] [] (fun k => ([] : List (Mf.Γ k))) (haltList Mg R).stk := by
    funext k; match k with
    | Sum.inl Aux2.main => exact halt_ne (NSeq Mf Mg ef of eg og) R _ (by intro h; cases h)
    | Sum.inl Aux2.tmp => exact halt_ne (NSeq Mf Mg ef of eg og) R _ (by intro h; cases h)
    | Sum.inl Aux2.tmp2 => exact halt_ne (NSeq Mf Mg ef of eg og) R _ (by intro h; cases h)
    | Sum.inl Aux2.save => exact halt_ne (NSeq Mf Mg ef of eg og) R _ (by intro h; cases h)
    | Sum.inr (Sum.inl k) => exact halt_ne (NSeq Mf Mg ef of eg og) R _ (by intro h; cases h)
    | Sum.inr (Sum.inr k) =>
      by_cases hk : k = Mg.k₁
      · subst hk; rw [emb2_g, halt_k1]; exact halt_k1 (NSeq Mf Mg ef of eg og) R
      · rw [emb2_g, halt_ne Mg R k hk]
        exact halt_ne (NSeq Mf Mg ef of eg og) R _ (fun h => hk (Sum.inr.inj (Sum.inr.inj h)))
  rw [← hstk]; rfl

private theorem init_NPair2 (I : List Bool) :
    initList (NPair Mf Mg ef of eg og) I =
      TM2.Cfg.mk (some (Sum.inr Ph2.copy)) (Mf.initialState, Mg.initialState, none)
        (emb2 Mf Mg I [] [] [] (fun k => ([] : List (Mf.Γ k))) (fun k => ([] : List (Mg.Γ k)))) := by
  unfold initList; congr 1; funext k
  match k with
  | Sum.inl Aux2.main => rfl
  | Sum.inl Aux2.tmp => rfl
  | Sum.inl Aux2.tmp2 => rfl
  | Sum.inl Aux2.save => rfl
  | Sum.inr (Sum.inl k) => rfl
  | Sum.inr (Sum.inr k) => rfl

private theorem halt_NPair2 (R : List (Mg.Γ Mg.k₁)) :
    haltList (NPair Mf Mg ef of eg og) R =
      TM2.Cfg.mk none (Mf.initialState, Mg.initialState, none)
        (emb2 Mf Mg [] [] [] [] (fun k => ([] : List (Mf.Γ k))) (haltList Mg R).stk) := by
  have hstk : (haltList (NPair Mf Mg ef of eg og) R).stk =
      emb2 Mf Mg [] [] [] [] (fun k => ([] : List (Mf.Γ k))) (haltList Mg R).stk := by
    funext k; match k with
    | Sum.inl Aux2.main => exact halt_ne (NPair Mf Mg ef of eg og) R _ (by intro h; cases h)
    | Sum.inl Aux2.tmp => exact halt_ne (NPair Mf Mg ef of eg og) R _ (by intro h; cases h)
    | Sum.inl Aux2.tmp2 => exact halt_ne (NPair Mf Mg ef of eg og) R _ (by intro h; cases h)
    | Sum.inl Aux2.save => exact halt_ne (NPair Mf Mg ef of eg og) R _ (by intro h; cases h)
    | Sum.inr (Sum.inl k) => exact halt_ne (NPair Mf Mg ef of eg og) R _ (by intro h; cases h)
    | Sum.inr (Sum.inr k) =>
      by_cases hk : k = Mg.k₁
      · subst hk; rw [emb2_g, halt_k1]; exact halt_k1 (NPair Mf Mg ef of eg og) R
      · rw [emb2_g, halt_ne Mg R k hk]
        exact halt_ne (NPair Mf Mg ef of eg og) R _ (fun h => hk (Sum.inr.inj (Sum.inr.inj h)))
  rw [← hstk]; rfl

end PairSeqMachine

/-- Polynomial time is closed under sequential composition `x ↦ g (f x)`. -/
private theorem isPolyTime_seq {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] {f : α → β} {g : β → γ} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => g (f x)) := by
  obtain ⟨Tf⟩ := hf
  obtain ⟨Tg⟩ := hg
  obtain ⟨B, hB⟩ : ∃ B, ∀ l, pushes (Tf.tm.m l) ≤ B := by
    let _ := Tf.tm.ΛFin
    exact ⟨∑ l, pushes (Tf.tm.m l), fun l =>
      Finset.single_le_sum (f := fun l => pushes (Tf.tm.m l)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ l)⟩
  refine ⟨{ tm := NSeq Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet Tg.outputAlphabet
            inputAlphabet := Tf.inputAlphabet
            outputAlphabet := Tg.outputAlphabet
            time := 2 * (Polynomial.X + (B : Polynomial ℕ) * Tf.time + 1) + Tf.time +
              Tg.time.comp (Polynomial.X + (B : Polynomial ℕ) * Tf.time)
            outputsFun := fun x => ?_ }⟩
  obtain ⟨⟨tf, htf⟩, htfle⟩ := Tf.outputsFun x
  obtain ⟨⟨tg, htg⟩, htgle⟩ := Tg.outputsFun (f x)
  have hf' : (flip bind (TM2.step Tf.tm.m))^[tf]
      (some (initList Tf.tm (List.map Tf.inputAlphabet.symm (bitEncode x)))) =
      some (haltList Tf.tm (List.map Tf.outputAlphabet.symm (bitEncode (f x)))) := htf
  have hg' : (flip bind (TM2.step Tg.tm.m))^[tg]
      (some (initList Tg.tm (List.map Tg.inputAlphabet.symm (bitEncode (f x))))) =
      some (haltList Tg.tm (List.map Tg.outputAlphabet.invFun (bitEncode (g (f x))))) := htg
  have htfle' : tf ≤ Tf.time.eval (bitEncode x).length := htfle
  have htgle' : tg ≤ Tg.time.eval (bitEncode (f x)).length := htgle
  clear htfle htgle htf htg
  change TM2OutputsInTime (NSeq Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet
      Tg.outputAlphabet) (List.map Tf.inputAlphabet.invFun (bitEncode x))
    (some (List.map Tg.outputAlphabet.invFun (bitEncode (g (f x)))))
    (Polynomial.eval (bitEncode x).length _)
  generalize bitEncode x = I at hf' htfle' ⊢
  generalize bitEncode (f x) = O at hf' hg' htgle'
  refine ⟨⟨tg + ((O.length + 1) + ((O.length + 1) + tf)), ?_⟩, ?_⟩
  · have h1 := lift_runF2 Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet
      Tg.outputAlphabet false Tg.tm.initialState none [] [] [] [] (fun k => ([] : List (Tg.tm.Γ k)))
      tf _ _ hf'
    have h2 := unload2_run_false Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet
      Tg.outputAlphabet Tf.tm.initialState Tg.tm.initialState (fun k => ([] : List (Tg.tm.Γ k)))
      (O.map Tf.outputAlphabet.symm) [] [] [] [] (haltList Tf.tm (O.map Tf.outputAlphabet.symm)).stk
      none (halt_k1 Tf.tm _)
    rw [halt_upd] at h2
    simp only [List.length_map, List.append_nil, List.map_reverse, List.map_map,
      Equiv.self_comp_symm, List.map_id] at h2
    have h3 := load2_run_false Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet
      Tg.outputAlphabet Tf.tm.initialState Tg.tm.initialState (fun k => ([] : List (Tf.tm.Γ k)))
      O.reverse [] [] [] (fun k => ([] : List (Tg.tm.Γ k))) none
    simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h3
    rw [init_upd] at h3
    have h4 := lift_runG2 Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet
      Tg.outputAlphabet false Tf.tm.initialState none [] [] [] [] (fun k => ([] : List (Tf.tm.Γ k)))
      tg _ _ hg'
    have hrun := iter_trans (iter_trans (iter_trans h1 h2) h3) h4
    exact (congrArg (fun c => (flip bind (TM2.step (prog2 Tf.tm Tg.tm Tf.inputAlphabet
        Tf.outputAlphabet Tg.inputAlphabet Tg.outputAlphabet false)))^[tg + ((O.length + 1) +
        ((O.length + 1) + tf))] (some c))
      (init_NSeq2 Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet
        Tg.outputAlphabet (List.map Tf.inputAlphabet.symm I))).trans
      (hrun.trans (congrArg some (halt_NSeq2 Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet
        Tg.inputAlphabet Tg.outputAlphabet _).symm))
  · have hO : O.length ≤ I.length + B * tf := by
      have h1 := len_run Tf.tm.m B hB Tf.tm.k₁ tf _ _ hf'
      rw [halt_k1, List.length_map] at h1
      have h2 := init_len Tf.tm (I.map Tf.inputAlphabet.symm) Tf.tm.k₁
      rw [List.length_map] at h2; omega
    have hBt : B * tf ≤ B * Tf.time.eval I.length := Nat.mul_le_mul_left B htfle'
    have hmono := poly_mono Tg.time (show O.length ≤ I.length + B * Tf.time.eval I.length by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_natCast, Polynomial.eval_comp, Polynomial.eval_ofNat, Nat.cast_id]
    omega

/-- Polynomial time is closed under pairing `x ↦ (f x, g x)`. -/
private theorem isPolyTime_pair {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] {f : α → β} {g : α → γ} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => (f x, g x)) := by
  obtain ⟨Tf⟩ := hf
  obtain ⟨Tg⟩ := hg
  obtain ⟨B, hB⟩ : ∃ B, ∀ l, pushes (Tf.tm.m l) ≤ B := by
    let _ := Tf.tm.ΛFin
    exact ⟨∑ l, pushes (Tf.tm.m l), fun l =>
      Finset.single_le_sum (f := fun l => pushes (Tf.tm.m l)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ l)⟩
  refine ⟨{ tm := NPair Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet Tg.outputAlphabet
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Tg.outputAlphabet
            time := 3 * (Polynomial.X + 1) + 2 * (Polynomial.X + (B : Polynomial ℕ) * Tf.time + 1) +
              1 + Tf.time + Tg.time
            outputsFun := fun x => ?_ }⟩
  obtain ⟨⟨tf, htf⟩, htfle⟩ := Tf.outputsFun x
  obtain ⟨⟨tg, htg⟩, htgle⟩ := Tg.outputsFun x
  have hf' : (flip bind (TM2.step Tf.tm.m))^[tf]
      (some (initList Tf.tm (List.map Tf.inputAlphabet.symm (bitEncode x)))) =
      some (haltList Tf.tm (List.map Tf.outputAlphabet.symm (bitEncode (f x)))) := htf
  have hg' : (flip bind (TM2.step Tg.tm.m))^[tg]
      (some (initList Tg.tm (List.map Tg.inputAlphabet.symm (bitEncode x)))) =
      some (haltList Tg.tm (List.map Tg.outputAlphabet.symm (bitEncode (g x)))) := htg
  have htfle' : tf ≤ Tf.time.eval (bitEncode x).length := htfle
  have htgle' : tg ≤ Tg.time.eval (bitEncode x).length := htgle
  clear htfle htgle htf htg
  have hpair_enc : bitEncode (f x, g x) = delimit (bitEncode (f x)) ++ bitEncode (g x) := rfl
  change TM2OutputsInTime (NPair Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet
      Tg.outputAlphabet) (List.map (@Equiv.invFun ((NPair Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet Tg.outputAlphabet).Γ (NPair Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet Tg.outputAlphabet).k₀) Bool (Equiv.refl Bool)) (bitEncode x))
    (some (List.map Tg.outputAlphabet.invFun (bitEncode (f x, g x))))
    (Polynomial.eval (bitEncode x).length _)
  rw [hpair_enc]
  generalize bitEncode x = I at hf' hg' htfle' htgle' ⊢
  generalize bitEncode (f x) = O at hf' ⊢
  generalize bitEncode (g x) = R at hg' ⊢
  refine ⟨⟨(O.length + 1) + (1 + (tg + ((I.length + 1) + ((O.length + 1) +
      (tf + ((I.length + 1) + (I.length + 1))))))), ?_⟩, ?_⟩
  · have h1 := copy2_run Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet
      Tg.outputAlphabet true Tf.tm.initialState Tg.tm.initialState (fun k => ([] : List (Tf.tm.Γ k)))
      (fun k => ([] : List (Tg.tm.Γ k))) I [] [] [] none
    simp only [List.append_nil] at h1
    have h2 := feed2_run Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet
      Tg.outputAlphabet true Tf.tm.initialState Tg.tm.initialState (fun k => ([] : List (Tg.tm.Γ k)))
      I.reverse [] I.reverse [] (fun k => ([] : List (Tf.tm.Γ k))) none
    simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h2
    rw [init_upd] at h2
    have h3 := lift_runF2 Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet
      Tg.outputAlphabet true Tg.tm.initialState none [] [] I.reverse []
      (fun k => ([] : List (Tg.tm.Γ k))) tf _ _ hf'
    have h4 := unload2_run_true Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet
      Tg.outputAlphabet Tf.tm.initialState Tg.tm.initialState (fun k => ([] : List (Tg.tm.Γ k)))
      (O.map Tf.outputAlphabet.symm) [] [] I.reverse []
      (haltList Tf.tm (O.map Tf.outputAlphabet.symm)).stk none (halt_k1 Tf.tm _)
    rw [halt_upd] at h4
    simp only [List.length_map, List.append_nil, List.map_reverse, List.map_map,
      Equiv.self_comp_symm, List.map_id] at h4
    have h5 := load2_run_true Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet
      Tg.outputAlphabet Tf.tm.initialState Tg.tm.initialState (fun k => ([] : List (Tf.tm.Γ k)))
      I.reverse [] [] O.reverse (fun k => ([] : List (Tg.tm.Γ k))) none
    simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h5
    rw [init_upd] at h5
    have h6 := lift_runG2 Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet
      Tg.outputAlphabet true Tf.tm.initialState none [] [] [] O.reverse
      (fun k => ([] : List (Tf.tm.Γ k))) tg _ _ hg'
    have h7 : (flip bind (TM2.step (prog2 Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet
        Tg.inputAlphabet Tg.outputAlphabet true)))^[1]
        (some (liftCfgG2 Tf.tm Tg.tm true Tf.tm.initialState none [] [] [] O.reverse
          (fun k => ([] : List (Tf.tm.Γ k))) (haltList Tg.tm (R.map Tg.outputAlphabet.symm)))) =
        some ⟨some (Sum.inr Ph2.out_delim), (Tf.tm.initialState, Tg.tm.initialState, none),
          emb2 Tf.tm Tg.tm [] [] [] O.reverse (fun k => ([] : List (Tf.tm.Γ k)))
            (Function.update (haltList Tg.tm (R.map Tg.outputAlphabet.symm)).stk Tg.tm.k₁
              (Tg.outputAlphabet.symm false :: R.map Tg.outputAlphabet.symm))⟩ := by
      rw [iter_succ_of]
      · rfl
      · simp [liftCfgG2, prog2, haltList, upd2_g]
    have h8 := out_delim2_run Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet
      Tg.outputAlphabet true Tf.tm.initialState Tg.tm.initialState (fun k => ([] : List (Tf.tm.Γ k)))
      O.reverse [] [] []
      (Function.update (haltList Tg.tm (R.map Tg.outputAlphabet.symm)).stk Tg.tm.k₁
        (Tg.outputAlphabet.symm false :: R.map Tg.outputAlphabet.symm)) none
    simp only [List.length_reverse, List.reverse_reverse, Function.update_idem,
      Function.update_self] at h8
    rw [delim_map] at h8
    have hupd_eq : Function.update (haltList Tg.tm (R.map Tg.outputAlphabet.symm)).stk Tg.tm.k₁
        ((delimit O ++ R).map Tg.outputAlphabet.symm) =
        (haltList Tg.tm ((delimit O ++ R).map Tg.outputAlphabet.symm)).stk := by
      funext k
      by_cases hk : k = Tg.tm.k₁
      · subst hk; simp [haltList]
      · rw [Function.update_of_ne hk]; simp [haltList, hk]
    rw [hupd_eq] at h8
    have hrun := iter_trans (iter_trans (iter_trans (iter_trans (iter_trans (iter_trans
      (iter_trans h1 h2) h3) h4) h5) h6) h7) h8
    have hmapI : List.map (@Equiv.invFun ((NPair Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet Tg.outputAlphabet).Γ (NPair Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet Tg.outputAlphabet).k₀) Bool (Equiv.refl Bool)) I = I := List.map_id I
    rw [hmapI]
    exact (congrArg (fun c => (flip bind (TM2.step (prog2 Tf.tm Tg.tm Tf.inputAlphabet
        Tf.outputAlphabet Tg.inputAlphabet Tg.outputAlphabet true)))^[_] (some c))
      (init_NPair2 Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet Tg.inputAlphabet
        Tg.outputAlphabet I)).trans
      (hrun.trans (congrArg some (halt_NPair2 Tf.tm Tg.tm Tf.inputAlphabet Tf.outputAlphabet
        Tg.inputAlphabet Tg.outputAlphabet _).symm))
  · have hO : O.length ≤ I.length + B * tf := by
      have h1 := len_run Tf.tm.m B hB Tf.tm.k₁ tf _ _ hf'
      rw [halt_k1, List.length_map] at h1
      have h2 := init_len Tf.tm (I.map Tf.inputAlphabet.symm) Tf.tm.k₁
      rw [List.length_map] at h2; omega
    have hBt : B * tf ≤ B * Tf.time.eval I.length := Nat.mul_le_mul_left B htfle'
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_natCast, Polynomial.eval_ofNat, Nat.cast_id]
    omega

/- ### Bounded-Space Unary Iteration (`isPolyTime_iter`) -/

private inductive AuxIt
  | main
  | cnt
  | tmp
  deriving DecidableEq

private instance : Fintype AuxIt :=
  ⟨{AuxIt.main, AuxIt.cnt, AuxIt.tmp}, by intro x; cases x <;> simp⟩

private inductive PhIt
  | undelim
  | copyInit
  | loadInit
  | loopChk
  | unloadM
  | reloadM
  | finUnload
  | finOut
  deriving DecidableEq

private instance : Fintype PhIt :=
  ⟨{PhIt.undelim, PhIt.copyInit, PhIt.loadInit, PhIt.loopChk, PhIt.unloadM, PhIt.reloadM,
    PhIt.finUnload, PhIt.finOut}, by intro x; cases x <;> simp⟩

section IterMachine

variable (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)

private abbrev KKIt : Type := AuxIt ⊕ M.K

private abbrev GIt : KKIt M → Type := fun k =>
  Sum.casesOn (motive := fun _ => Type) k (fun _ => Bool) M.Γ

private abbrev LabIt : Type := M.Λ ⊕ PhIt

private abbrev VarIt : Type := M.σ × Option Bool

private def embIt (a b c : List Bool) (S : ∀ k, List (M.Γ k)) : ∀ k, List (GIt M k)
  | Sum.inl AuxIt.main => a
  | Sum.inl AuxIt.cnt => b
  | Sum.inl AuxIt.tmp => c
  | Sum.inr k => S k

@[simp] private theorem embIt_main (a b c : List Bool) (S : ∀ k, List (M.Γ k)) :
    embIt M a b c S (Sum.inl AuxIt.main) = a := rfl
@[simp] private theorem embIt_cnt (a b c : List Bool) (S : ∀ k, List (M.Γ k)) :
    embIt M a b c S (Sum.inl AuxIt.cnt) = b := rfl
@[simp] private theorem embIt_tmp (a b c : List Bool) (S : ∀ k, List (M.Γ k)) :
    embIt M a b c S (Sum.inl AuxIt.tmp) = c := rfl
@[simp] private theorem embIt_m (a b c : List Bool) (S : ∀ k, List (M.Γ k)) (k : M.K) :
    embIt M a b c S (Sum.inr k) = S k := rfl

section UpdIt
variable [DecidableEq (KKIt M)]

private theorem updIt_main (a b c : List Bool) (S : ∀ k, List (M.Γ k)) (l : List Bool) :
    Function.update (embIt M a b c S) (Sum.inl AuxIt.main) l = embIt M l b c S := by
  funext k; match k with
  | Sum.inl AuxIt.main => simp
  | Sum.inl AuxIt.cnt => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl AuxIt.tmp => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr k => rw [Function.update_of_ne (by simp)]; rfl

private theorem updIt_cnt (a b c : List Bool) (S : ∀ k, List (M.Γ k)) (l : List Bool) :
    Function.update (embIt M a b c S) (Sum.inl AuxIt.cnt) l = embIt M a l c S := by
  funext k; match k with
  | Sum.inl AuxIt.main => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl AuxIt.cnt => simp
  | Sum.inl AuxIt.tmp => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr k => rw [Function.update_of_ne (by simp)]; rfl

private theorem updIt_tmp (a b c : List Bool) (S : ∀ k, List (M.Γ k)) (l : List Bool) :
    Function.update (embIt M a b c S) (Sum.inl AuxIt.tmp) l = embIt M a b l S := by
  funext k; match k with
  | Sum.inl AuxIt.main => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl AuxIt.cnt => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl AuxIt.tmp => simp
  | Sum.inr k => rw [Function.update_of_ne (by simp)]; rfl

private theorem updIt_m [DecidableEq M.K] (a b c : List Bool) (S : ∀ k, List (M.Γ k))
    (k : M.K) (l : List (M.Γ k)) :
    Function.update (embIt M a b c S) (Sum.inr k) l = embIt M a b c (Function.update S k l) := by
  funext j; match j with
  | Sum.inl AuxIt.main => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl AuxIt.cnt => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl AuxIt.tmp => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr j =>
    by_cases h : j = k
    · subst h; simp
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k l j
      rw [Function.update_of_ne h]

end UpdIt

private def liftMIt : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (GIt M) (LabIt M) (VarIt M)
  | .push k f q => .push (Sum.inr k) (fun v => f v.1) (liftMIt q)
  | .peek k f q => .peek (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftMIt q)
  | .pop k f q => .pop (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftMIt q)
  | .load a q => .load (fun v => (a v.1, v.2)) (liftMIt q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (liftMIt q₁) (liftMIt q₂)
  | .goto f => .goto (fun v => Sum.inl (f v.1))
  | .halt => .goto (fun _ => Sum.inr PhIt.unloadM)

private def liftCfgIt (o : Option Bool) (a b c : List Bool) (cm : TM2.Cfg M.Γ M.Λ M.σ) :
    TM2.Cfg (GIt M) (LabIt M) (VarIt M) :=
  ⟨some (cm.l.elim (Sum.inr PhIt.unloadM) Sum.inl), (cm.var, o), embIt M a b c cm.stk⟩

private theorem stepAux_liftMIt [DecidableEq (KKIt M)] [DecidableEq M.K] (o : Option Bool)
    (a b c : List Bool) (q : TM2.Stmt M.Γ M.Λ M.σ) :
    ∀ (v : M.σ) (S : ∀ k, List (M.Γ k)),
    TM2.stepAux (liftMIt M q) (v, o) (embIt M a b c S) =
      liftCfgIt M o a b c (TM2.stepAux q v S) := by
  induction q with
  | push k f q ih =>
    intro v S; simp only [liftMIt, TM2.stepAux]
    rw [show embIt M a b c S (Sum.inr k) = S k from rfl, updIt_m]; exact ih _ _
  | peek k f q ih => intro v S; simp only [liftMIt, TM2.stepAux]; exact ih _ _
  | pop k f q ih =>
    intro v S; simp only [liftMIt, TM2.stepAux]
    rw [show embIt M a b c S (Sum.inr k) = S k from rfl, updIt_m]; exact ih _ _
  | load f q ih => intro v S; simp only [liftMIt, TM2.stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S; simp only [liftMIt, TM2.stepAux]; cases f v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f => intro v S; rfl
  | halt => intro v S; rfl

/-- Program for iterating `M` `u.length` times on `(u : List Bool, x : α)`.
Since `bitEncode (u : List Bool)` consists of `u.length` blocks of 3 bits (`[true, b, false]`),
`loopChk` pops 3 bits from `cnt` per iteration. -/
private def progIt : LabIt M → TM2.Stmt (GIt M) (LabIt M) (VarIt M)
  | Sum.inl l => liftMIt M (M.m l)
  | Sum.inr PhIt.undelim =>
    .pop (Sum.inl AuxIt.main) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2 == some true)
        (.pop (Sum.inl AuxIt.main) (fun v o => (v.1, o)) <|
          .push (Sum.inl AuxIt.cnt) (fun v => v.2.getD false)
            (.goto fun _ => Sum.inr PhIt.undelim))
        (.load (fun v => (v.1, none)) (.goto fun _ => Sum.inr PhIt.copyInit))
  | Sum.inr PhIt.copyInit =>
    .pop (Sum.inl AuxIt.main) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inl AuxIt.tmp) (fun v => v.2.getD false)
          (.goto fun _ => Sum.inr PhIt.copyInit))
        (.goto fun _ => Sum.inr PhIt.loadInit)
  | Sum.inr PhIt.loadInit =>
    .pop (Sum.inl AuxIt.tmp) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inr M.k₀) (fun v => ei.symm (v.2.getD false))
          (.goto fun _ => Sum.inr PhIt.loadInit))
        (.goto fun _ => Sum.inr PhIt.loopChk)
  | Sum.inr PhIt.loopChk =>
    .pop (Sum.inl AuxIt.cnt) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.pop (Sum.inl AuxIt.cnt) (fun v _ => (v.1, none)) <|
          .pop (Sum.inl AuxIt.cnt) (fun v _ => (v.1, none))
            (.goto fun _ => Sum.inl M.main))
        (.goto fun _ => Sum.inr PhIt.finUnload)
  | Sum.inr PhIt.unloadM =>
    .pop (Sum.inr M.k₁) (fun v o => (v.1, o.map eo)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inl AuxIt.tmp) (fun v => v.2.getD false)
          (.goto fun _ => Sum.inr PhIt.unloadM))
        (.goto fun _ => Sum.inr PhIt.reloadM)
  | Sum.inr PhIt.reloadM =>
    .pop (Sum.inl AuxIt.tmp) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inr M.k₀) (fun v => ei.symm (v.2.getD false))
          (.goto fun _ => Sum.inr PhIt.reloadM))
        (.goto fun _ => Sum.inr PhIt.loopChk)
  | Sum.inr PhIt.finUnload =>
    .pop (Sum.inr M.k₀) (fun v o => (v.1, o.map ei)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inl AuxIt.tmp) (fun v => v.2.getD false)
          (.goto fun _ => Sum.inr PhIt.finUnload))
        (.goto fun _ => Sum.inr PhIt.finOut)
  | Sum.inr PhIt.finOut =>
    .pop (Sum.inl AuxIt.tmp) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inl AuxIt.main) (fun v => v.2.getD false)
          (.goto fun _ => Sum.inr PhIt.finOut))
        .halt

private def NIter : FinTM2 :=
  letI := M.kFin; letI := M.ΛFin; letI := M.σFin
  { K := KKIt M, k₀ := Sum.inl AuxIt.main, k₁ := Sum.inl AuxIt.main,
    Γ := GIt M, Λ := LabIt M, main := Sum.inr PhIt.undelim,
    σ := VarIt M, initialState := (M.initialState, none),
    Γk₀Fin := inferInstanceAs (Fintype Bool), m := progIt M ei eo }

section RunsIt
variable [DecidableEq (KKIt M)]

private theorem undelimIt_run (s : M.σ) (S : ∀ k, List (M.Γ k)) :
    ∀ (u rest c t : List Bool) (o : Option Bool),
    (flip bind (TM2.step (progIt M ei eo)))^[u.length + 1]
      (some ⟨some (Sum.inr PhIt.undelim), (s, o), embIt M (delimit u ++ rest) c t S⟩) =
    some ⟨some (Sum.inr PhIt.copyInit), (s, none), embIt M rest (u.reverse ++ c) t S⟩
  | [], rest, c, t, o => by
    rw [List.length_nil, iter_step]; simp [delimit, progIt, updIt_main]
  | b :: u, rest, c, t, o => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [delimit, progIt, updIt_main, updIt_cnt]); rw [undelimIt_run s S u rest (b :: c) t (some b)]
    simp

private theorem copyInitIt_run (s : M.σ) (S : ∀ k, List (M.Γ k)) :
    ∀ (l c t : List Bool) (o : Option Bool),
    (flip bind (TM2.step (progIt M ei eo)))^[l.length + 1]
      (some ⟨some (Sum.inr PhIt.copyInit), (s, o), embIt M l c t S⟩) =
    some ⟨some (Sum.inr PhIt.loadInit), (s, none), embIt M [] c (l.reverse ++ t) S⟩
  | [], c, t, o => by
    rw [List.length_nil, iter_step]; simp [progIt, updIt_main]
  | b :: l, c, t, o => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [progIt, updIt_main, updIt_tmp]); rw [copyInitIt_run s S l c (b :: t) (some b)]
    simp

private theorem loadInitIt_run [DecidableEq M.K] (s : M.σ) :
    ∀ (t m c : List Bool) (S : ∀ k, List (M.Γ k)) (o : Option Bool),
    (flip bind (TM2.step (progIt M ei eo)))^[t.length + 1]
      (some ⟨some (Sum.inr PhIt.loadInit), (s, o), embIt M m c t S⟩) =
    some ⟨some (Sum.inr PhIt.loopChk), (s, none),
      embIt M m c [] (Function.update S M.k₀ (t.reverse.map ei.symm ++ S M.k₀))⟩
  | [], m, c, S, o => by
    rw [List.length_nil, iter_step]; simp [progIt, updIt_tmp]
  | b :: t, m, c, S, o => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [progIt, updIt_tmp, updIt_m]); rw [loadInitIt_run s t m c _ (some b)]
    simp [Function.update_idem]

private theorem unloadMIt_run [DecidableEq M.K] (s : M.σ) :
    ∀ (L : List (M.Γ M.k₁)) (m c t : List Bool) (S : ∀ k, List (M.Γ k)) (o : Option Bool),
    S M.k₁ = L →
    (flip bind (TM2.step (progIt M ei eo)))^[L.length + 1]
      (some ⟨some (Sum.inr PhIt.unloadM), (s, o), embIt M m c t S⟩) =
    some ⟨some (Sum.inr PhIt.reloadM), (s, none),
      embIt M m c (L.reverse.map eo ++ t) (Function.update S M.k₁ [])⟩
  | [], m, c, t, S, o, hS => by
    rw [List.length_nil, iter_step]; simp [progIt, hS, updIt_m]
  | y :: L, m, c, t, S, o, hS => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [progIt, hS, updIt_tmp, updIt_m]); rw [unloadMIt_run s L m c (eo y :: t) _ (some (eo y)) (by simp)]
    simp [Function.update_idem]

private theorem reloadMIt_run [DecidableEq M.K] (s : M.σ) :
    ∀ (t m c : List Bool) (S : ∀ k, List (M.Γ k)) (o : Option Bool),
    (flip bind (TM2.step (progIt M ei eo)))^[t.length + 1]
      (some ⟨some (Sum.inr PhIt.reloadM), (s, o), embIt M m c t S⟩) =
    some ⟨some (Sum.inr PhIt.loopChk), (s, none),
      embIt M m c [] (Function.update S M.k₀ (t.reverse.map ei.symm ++ S M.k₀))⟩
  | [], m, c, S, o => by
    rw [List.length_nil, iter_step]; simp [progIt, updIt_tmp]
  | b :: t, m, c, S, o => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [progIt, updIt_tmp, updIt_m]); rw [reloadMIt_run s t m c _ (some b)]
    simp [Function.update_idem]

private theorem finUnloadIt_run [DecidableEq M.K] (s : M.σ) :
    ∀ (L : List (M.Γ M.k₀)) (m c t : List Bool) (S : ∀ k, List (M.Γ k)) (o : Option Bool),
    S M.k₀ = L →
    (flip bind (TM2.step (progIt M ei eo)))^[L.length + 1]
      (some ⟨some (Sum.inr PhIt.finUnload), (s, o), embIt M m c t S⟩) =
    some ⟨some (Sum.inr PhIt.finOut), (s, none),
      embIt M m c (L.reverse.map ei ++ t) (Function.update S M.k₀ [])⟩
  | [], m, c, t, S, o, hS => by
    rw [List.length_nil, iter_step]; simp [progIt, hS, updIt_m]
  | y :: L, m, c, t, S, o, hS => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [progIt, hS, updIt_tmp, updIt_m]); rw [finUnloadIt_run s L m c (ei y :: t) _ (some (ei y)) (by simp)]
    simp [Function.update_idem]

private theorem finOutIt_run (s : M.σ) (S : ∀ k, List (M.Γ k)) :
    ∀ (t m c : List Bool) (o : Option Bool),
    (flip bind (TM2.step (progIt M ei eo)))^[t.length + 1]
      (some ⟨some (Sum.inr PhIt.finOut), (s, o), embIt M m c t S⟩) =
    some ⟨none, (s, none), embIt M (t.reverse ++ m) c [] S⟩
  | [], m, c, o => by
    rw [List.length_nil, iter_step]; simp [progIt, updIt_tmp]
  | b :: t, m, c, o => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [progIt, updIt_tmp, updIt_main]); rw [finOutIt_run s S t (b :: m) c (some b)]
    simp

private theorem lift_stepMIt [DecidableEq M.K] (o : Option Bool) (a b c : List Bool)
    {cm dm : TM2.Cfg M.Γ M.Λ M.σ} (h : TM2.step M.m cm = some dm) :
    TM2.step (progIt M ei eo) (liftCfgIt M o a b c cm) = some (liftCfgIt M o a b c dm) := by
  rcases cm with ⟨_ | l, v, S⟩
  · simp at h
  · simp only [TM2.step] at h; cases h
    show some (TM2.stepAux (liftMIt M (M.m l)) (v, o) (embIt M a b c S)) = _
    rw [stepAux_liftMIt]

private theorem lift_runMIt [DecidableEq M.K] (o : Option Bool) (a b c : List Bool) :
    ∀ (n : ℕ) (cm dm : TM2.Cfg M.Γ M.Λ M.σ),
    (flip bind (TM2.step M.m))^[n] (some cm) = some dm →
    (flip bind (TM2.step (progIt M ei eo)))^[n] (some (liftCfgIt M o a b c cm)) =
      some (liftCfgIt M o a b c dm)
  | 0, cm, dm, h => by simp only [Function.iterate_zero, id, Option.some.injEq] at h ⊢; rw [h]
  | n + 1, cm, dm, h => by
    cases hc : TM2.step M.m cm with
    | none =>
      rw [Function.iterate_succ_apply] at h
      change (flip bind (TM2.step M.m))^[n] (TM2.step M.m cm) = some dm at h
      rw [hc, iter_none] at h; cases h
    | some cm' =>
      rw [iter_succ_of hc] at h
      rw [iter_succ_of (lift_stepMIt M ei eo o a b c hc)]
      exact lift_runMIt o a b c n cm' dm h

end RunsIt

private theorem init_NIter (I : List Bool) :
    initList (NIter M ei eo) I =
      TM2.Cfg.mk (some (Sum.inr PhIt.undelim)) (M.initialState, none)
        (embIt M I [] [] (fun k => ([] : List (M.Γ k)))) := by
  unfold initList; congr 1; funext k
  match k with
  | Sum.inl AuxIt.main => rfl
  | Sum.inl AuxIt.cnt => rfl
  | Sum.inl AuxIt.tmp => rfl
  | Sum.inr k => rfl

private theorem halt_NIter (O : List Bool) :
    haltList (NIter M ei eo) O =
      TM2.Cfg.mk none (M.initialState, none)
        (embIt M O [] [] (fun k => ([] : List (M.Γ k)))) := by
  unfold haltList; congr 1; funext k
  match k with
  | Sum.inl AuxIt.main => rfl
  | Sum.inl AuxIt.cnt => rfl
  | Sum.inl AuxIt.tmp => rfl
  | Sum.inr k => rfl

end IterMachine

private theorem bitEncode_listBool_length (u : List Bool) :
    (bitEncode u).length = 3 * u.length := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    change (delimit [b] ++ bitEncode u).length = 3 * (u.length + 1)
    rw [List.length_append, length_delimit, List.length_singleton, ih]; omega

private theorem bitEncode_listBool_cons (b : Bool) (u : List Bool) :
    bitEncode (b :: u) = true :: b :: false :: bitEncode u := rfl

/-- Bounded-space polynomial-time iteration: if `step : α → α` is `IsPolyTime` and every
intermediate iterate `step^[k] x` (`k ≤ u.length`) has bit-length bounded by `S.eval |(u, x)|`,
then `(u, x) ↦ step^[u.length] x` is `IsPolyTime`. -/
private theorem isPolyTime_iter {α : Type} [BitstringEncoding α]
    (step : α → α) (hstep : IsPolyTime step) (S : Polynomial ℕ)
    (hbound : ∀ (u : List Bool) (x : α) (k : ℕ), k ≤ u.length →
      (bitEncode (step^[k] x)).length ≤ S.eval (bitEncode (u, x)).length) :
    IsPolyTime (fun p : List Bool × α => step^[p.1.length] p.2) := by
  obtain ⟨Tm⟩ := hstep
  refine ⟨{ tm := NIter Tm.tm Tm.inputAlphabet Tm.outputAlphabet
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := 4 * Polynomial.X + 4 +
              Polynomial.X * (Tm.time.comp S + 2 * S + 4) + (2 * S + 4)
            outputsFun := fun ⟨u, x⟩ => ?_ }⟩
  change TM2OutputsInTime (NIter Tm.tm Tm.inputAlphabet Tm.outputAlphabet)
    (List.map (@Equiv.invFun ((NIter Tm.tm Tm.inputAlphabet Tm.outputAlphabet).Γ
      (NIter Tm.tm Tm.inputAlphabet Tm.outputAlphabet).k₀) Bool (Equiv.refl Bool)) (bitEncode (u, x)))
    (some (List.map (@Equiv.invFun ((NIter Tm.tm Tm.inputAlphabet Tm.outputAlphabet).Γ
      (NIter Tm.tm Tm.inputAlphabet Tm.outputAlphabet).k₁) Bool (Equiv.refl Bool))
      (bitEncode (step^[u.length] x)))) _
  have hmi1 : List.map (@Equiv.invFun ((NIter Tm.tm Tm.inputAlphabet Tm.outputAlphabet).Γ
      (NIter Tm.tm Tm.inputAlphabet Tm.outputAlphabet).k₀) Bool (Equiv.refl Bool))
      (bitEncode (u, x)) = bitEncode (u, x) := List.map_id _
  have hmi2 : List.map (@Equiv.invFun ((NIter Tm.tm Tm.inputAlphabet Tm.outputAlphabet).Γ
      (NIter Tm.tm Tm.inputAlphabet Tm.outputAlphabet).k₁) Bool (Equiv.refl Bool))
      (bitEncode (step^[u.length] x)) = bitEncode (step^[u.length] x) := List.map_id _
  rw [hmi1, hmi2]
  let L := (bitEncode (u, x)).length
  have henc : bitEncode (u, x) = delimit (bitEncode u) ++ bitEncode x := rfl
  have hL_eq : L = 2 * (bitEncode u).length + 1 + (bitEncode x).length := by
    change (delimit (bitEncode u) ++ bitEncode x).length = _
    rw [List.length_append, length_delimit]
  have hu_le : u.length ≤ L := by
    have := bitEncode_listBool_length u; omega
  have hbu_le : (bitEncode u).length ≤ L := by omega
  have hbx_le : (bitEncode x).length ≤ L := by omega
  -- Helper: run `k` loop iterations on a suffix of `cnt` of length `3 * k`.
  have hloop : ∀ (k : ℕ) (c : List Bool) (y : α),
      c.length = 3 * k →
      (∀ j ≤ k, (bitEncode (step^[j] y)).length ≤ S.eval L) →
      ∃ t ≤ k * (Tm.time.eval (S.eval L) + 2 * S.eval L + 3),
        (flip bind (TM2.step (progIt Tm.tm Tm.inputAlphabet Tm.outputAlphabet)))^[t]
          (some ⟨some (Sum.inr PhIt.loopChk), (Tm.tm.initialState, none),
            embIt Tm.tm [] c [] (initList Tm.tm ((bitEncode y).map Tm.inputAlphabet.symm)).stk⟩) =
        some ⟨some (Sum.inr PhIt.loopChk), (Tm.tm.initialState, none),
          embIt Tm.tm [] [] []
            (initList Tm.tm ((bitEncode (step^[k] y)).map Tm.inputAlphabet.symm)).stk⟩ := by
    intro k
    induction k with
    | zero =>
      intro c y hc _
      cases c with
      | nil => exact ⟨0, by simp, rfl⟩
      | cons _ _ => simp at hc
    | succ k ih =>
      intro c y hc hbd
      cases c with
      | nil => simp at hc
      | cons b1 c1 =>
      cases c1 with
      | nil => simp at hc; omega
      | cons b2 c2 =>
      cases c2 with
      | nil => simp at hc; omega
      | cons b3 c' =>
      have hc' : c'.length = 3 * k := by simp at hc; omega
      obtain ⟨⟨ts, hts⟩, htsle⟩ := Tm.outputsFun y
      have hs' : (flip bind (TM2.step Tm.tm.m))^[ts]
          (some (initList Tm.tm ((bitEncode y).map Tm.inputAlphabet.symm))) =
          some (haltList Tm.tm ((bitEncode (step y)).map Tm.outputAlphabet.symm)) := hts
      have hts_le_S : ts ≤ Tm.time.eval (S.eval L) :=
        le_trans htsle (poly_mono Tm.time (hbd 0 (Nat.zero_le _)))
      have hnext_le : (bitEncode (step y)).length ≤ S.eval L := by
        simpa using hbd 1 (by omega)
      -- 1 step of loopChk popping 3 bits
      have hchk : (flip bind (TM2.step (progIt Tm.tm Tm.inputAlphabet Tm.outputAlphabet)))^[1]
          (some ⟨some (Sum.inr PhIt.loopChk), (Tm.tm.initialState, none),
            embIt Tm.tm [] (b1 :: b2 :: b3 :: c') []
              (initList Tm.tm ((bitEncode y).map Tm.inputAlphabet.symm)).stk⟩) =
          some (liftCfgIt Tm.tm none [] c' []
            (initList Tm.tm ((bitEncode y).map Tm.inputAlphabet.symm))) := by
        rw [iter_succ_of]
        · rfl
        · simp [progIt, updIt_cnt, liftCfgIt, initList]
      -- ts steps of Tm
      have hrunM := lift_runMIt Tm.tm Tm.inputAlphabet Tm.outputAlphabet none [] c' [] ts _ _ hs'
      -- unloadM + reloadM
      have hunl := unloadMIt_run Tm.tm Tm.inputAlphabet Tm.outputAlphabet Tm.tm.initialState
        ((bitEncode (step y)).map Tm.outputAlphabet.symm) [] c' []
        (haltList Tm.tm ((bitEncode (step y)).map Tm.outputAlphabet.symm)).stk none (halt_k1 Tm.tm _)
      rw [halt_upd] at hunl
      simp only [List.length_map, List.append_nil, List.map_reverse, List.map_map,
        Equiv.self_comp_symm, List.map_id] at hunl
      have hrel := reloadMIt_run Tm.tm Tm.inputAlphabet Tm.outputAlphabet Tm.tm.initialState
        (bitEncode (step y)).reverse [] c' (fun k => ([] : List (Tm.tm.Γ k))) none
      simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hrel
      rw [init_upd] at hrel
      have hone := iter_trans (iter_trans (iter_trans hchk hrunM) hunl) hrel
      -- inductive call on step y
      have hbd' : ∀ j ≤ k, (bitEncode (step^[j] (step y))).length ≤ S.eval L := by
        intro j hj
        have hEq : step^[j] (step y) = step^[j + 1] y := by
          rw [Function.iterate_succ_apply]
        rw [hEq]
        exact hbd (j + 1) (by omega)
      obtain ⟨trest, htrest_le, htrest⟩ := ih c' (step y) hc' hbd'
      have hiter_eq : step^[k] (step y) = step^[k + 1] y := by
        rw [Function.iterate_succ_apply]
      rw [hiter_eq] at htrest
      refine ⟨trest + (((bitEncode (step y)).length + 1) +
        (((bitEncode (step y)).length + 1) + (ts + 1))), ?_, iter_trans hone htrest⟩
      rw [Nat.succ_mul]; omega
  -- Assemble full run: undelim -> copyInit -> loadInit -> loop -> finChk -> finUnload -> finOut
  have h1 := undelimIt_run Tm.tm Tm.inputAlphabet Tm.outputAlphabet Tm.tm.initialState
    (fun k => ([] : List (Tm.tm.Γ k))) (bitEncode u) (bitEncode x) [] [] none
  simp only [List.append_nil] at h1
  have h2 := copyInitIt_run Tm.tm Tm.inputAlphabet Tm.outputAlphabet Tm.tm.initialState
    (fun k => ([] : List (Tm.tm.Γ k))) (bitEncode x) (bitEncode u).reverse [] none
  simp only [List.append_nil] at h2
  have h3 := loadInitIt_run Tm.tm Tm.inputAlphabet Tm.outputAlphabet Tm.tm.initialState
    (bitEncode x).reverse [] (bitEncode u).reverse (fun k => ([] : List (Tm.tm.Γ k))) none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h3
  rw [init_upd] at h3
  have hloop_ex := hloop u.length (bitEncode u).reverse x
    (by rw [List.length_reverse, bitEncode_listBool_length]) (fun j hj => hbound u x j hj)
  let tloop := Classical.choose hloop_ex
  have htloop_le : tloop ≤ u.length * (Tm.time.eval (S.eval L) + 2 * S.eval L + 3) :=
    (Classical.choose_spec hloop_ex).1
  have h4 := (Classical.choose_spec hloop_ex).2
  have h5 : (flip bind (TM2.step (progIt Tm.tm Tm.inputAlphabet Tm.outputAlphabet)))^[1]
      (some ⟨some (Sum.inr PhIt.loopChk), (Tm.tm.initialState, none),
        embIt Tm.tm [] [] []
          (initList Tm.tm ((bitEncode (step^[u.length] x)).map Tm.inputAlphabet.symm)).stk⟩) =
      some ⟨some (Sum.inr PhIt.finUnload), (Tm.tm.initialState, none),
        embIt Tm.tm [] [] []
          (initList Tm.tm ((bitEncode (step^[u.length] x)).map Tm.inputAlphabet.symm)).stk⟩ := by
    rw [iter_succ_of]; · rfl
    · simp [progIt, updIt_cnt]
  have h6 := finUnloadIt_run Tm.tm Tm.inputAlphabet Tm.outputAlphabet Tm.tm.initialState
    ((bitEncode (step^[u.length] x)).map Tm.inputAlphabet.symm) [] [] []
    (initList Tm.tm ((bitEncode (step^[u.length] x)).map Tm.inputAlphabet.symm)).stk
    none (init_k0 Tm.tm _)
  have hinit_clear : Function.update
      (initList Tm.tm ((bitEncode (step^[u.length] x)).map Tm.inputAlphabet.symm)).stk Tm.tm.k₀ [] =
      fun k => ([] : List (Tm.tm.Γ k)) := by
    funext k; by_cases hk : k = Tm.tm.k₀
    · subst hk; simp
    · rw [Function.update_of_ne hk]; simp [initList, hk]
  rw [hinit_clear] at h6
  simp only [List.length_map, List.append_nil, List.map_reverse, List.map_map,
    Equiv.self_comp_symm, List.map_id] at h6
  have h7 := finOutIt_run Tm.tm Tm.inputAlphabet Tm.outputAlphabet Tm.tm.initialState
    (fun k => ([] : List (Tm.tm.Γ k))) (bitEncode (step^[u.length] x)).reverse [] [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h7
  have hfull := iter_trans (iter_trans (iter_trans (iter_trans (iter_trans (iter_trans
    h1 h2) h3) h4) h5) h6) h7
  have hfin_le : (bitEncode (step^[u.length] x)).length ≤ S.eval L := hbound u x u.length le_rfl
  refine ⟨⟨(bitEncode (step^[u.length] x)).length + 1 +
      ((bitEncode (step^[u.length] x)).length + 1 +
        (1 + (tloop + ((bitEncode x).length + 1 +
          ((bitEncode x).length + 1 + ((bitEncode u).length + 1)))))), ?_⟩, ?_⟩
  · rw [henc]
    exact (congrArg (fun c => (flip bind (TM2.step (progIt Tm.tm Tm.inputAlphabet
        Tm.outputAlphabet)))^[(bitEncode (step^[u.length] x)).length + 1 +
      ((bitEncode (step^[u.length] x)).length + 1 +
        (1 + (tloop + ((bitEncode x).length + 1 +
          ((bitEncode x).length + 1 + ((bitEncode u).length + 1))))))] (some c))
      (init_NIter Tm.tm Tm.inputAlphabet Tm.outputAlphabet (delimit (bitEncode u) ++ bitEncode x))).trans
      (hfull.trans (congrArg some (halt_NIter Tm.tm Tm.inputAlphabet Tm.outputAlphabet _).symm))
  · have hmul_le : u.length * (Tm.time.eval (S.eval L) + 2 * S.eval L + 3) ≤
        L * (Tm.time.eval (S.eval L) + 2 * S.eval L + 4) :=
      Nat.mul_le_mul hu_le (by omega)
    change _ ≤ _
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_comp, Polynomial.eval_ofNat]
    change _ ≤ 4 * L + 4 + L * (Tm.time.eval (S.eval L) + 2 * S.eval L + 4) + (2 * S.eval L + 4)
    omega


/- ## Section 2: Shared 4-Stack Boolean `FinTM2` Toolkit and Primitives -/

private inductive Stk4
  | s0
  | s1
  | s2
  | s3
  deriving DecidableEq

private instance : Fintype Stk4 :=
  ⟨{Stk4.s0, Stk4.s1, Stk4.s2, Stk4.s3}, by intro x; cases x <;> simp⟩

private def mk4 (a b c d : List Bool) : Stk4 → List Bool
  | Stk4.s0 => a
  | Stk4.s1 => b
  | Stk4.s2 => c
  | Stk4.s3 => d

@[simp] private theorem mk4_s0 (a b c d : List Bool) : mk4 a b c d Stk4.s0 = a := rfl
@[simp] private theorem mk4_s1 (a b c d : List Bool) : mk4 a b c d Stk4.s1 = b := rfl
@[simp] private theorem mk4_s2 (a b c d : List Bool) : mk4 a b c d Stk4.s2 = c := rfl
@[simp] private theorem mk4_s3 (a b c d : List Bool) : mk4 a b c d Stk4.s3 = d := rfl

@[simp] private theorem upd4_s0 (a b c d l : List Bool) :
    Function.update (mk4 a b c d) Stk4.s0 l = mk4 l b c d := by
  funext k; cases k <;> simp [mk4]

@[simp] private theorem upd4_s1 (a b c d l : List Bool) :
    Function.update (mk4 a b c d) Stk4.s1 l = mk4 a l c d := by
  funext k; cases k <;> simp [mk4]

@[simp] private theorem upd4_s2 (a b c d l : List Bool) :
    Function.update (mk4 a b c d) Stk4.s2 l = mk4 a b l d := by
  funext k; cases k <;> simp [mk4]

@[simp] private theorem upd4_s3 (a b c d l : List Bool) :
    Function.update (mk4 a b c d) Stk4.s3 l = mk4 a b c l := by
  funext k; cases k <;> simp [mk4]

private def mkFinTM2_4 {Λ σ : Type} [Fintype Λ] [Fintype σ]
    (main : Λ) (init : σ) (m : Λ → TM2.Stmt (fun _ : Stk4 => Bool) Λ σ) : FinTM2 where
  K := Stk4
  k₀ := Stk4.s0
  k₁ := Stk4.s0
  Γ _ := Bool
  Λ := Λ
  main := main
  σ := σ
  initialState := init
  m := m

private theorem init_mk4 {Λ σ : Type} [Fintype Λ] [Fintype σ]
    (main : Λ) (init : σ) (m : Λ → TM2.Stmt (fun _ : Stk4 => Bool) Λ σ) (I : List Bool) :
    initList (mkFinTM2_4 main init m) I = ⟨some main, init, mk4 I [] [] []⟩ := by
  unfold initList mkFinTM2_4; congr 1; funext k; cases k <;> rfl

private theorem halt_mk4 {Λ σ : Type} [Fintype Λ] [Fintype σ]
    (main : Λ) (init : σ) (m : Λ → TM2.Stmt (fun _ : Stk4 => Bool) Λ σ) (O : List Bool) :
    haltList (mkFinTM2_4 main init m) O = ⟨none, init, mk4 O [] [] []⟩ := by
  unfold haltList mkFinTM2_4; congr 1; funext k; cases k <;> rfl

private theorem mkBoolPolyTime {α β Λ σ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [Fintype Λ] [Fintype σ] (f : α → β)
    (main : Λ) (init : σ) (m : Λ → TM2.Stmt (fun _ : Stk4 => Bool) Λ σ)
    (time : Polynomial ℕ)
    (hrun : ∀ x : α, ∃ t ≤ time.eval (bitEncode x).length,
      (flip bind (TM2.step m))^[t] (some ⟨some main, init, mk4 (bitEncode x) [] [] []⟩) =
        some ⟨none, init, mk4 (bitEncode (f x)) [] [] []⟩) :
    IsPolyTime f := by
  refine ⟨{ tm := mkFinTM2_4 main init m
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := time
            outputsFun := fun x => ?_ }⟩
  refine ⟨⟨Classical.choose (hrun x), ?_⟩, (Classical.choose_spec (hrun x)).1⟩
  change (flip bind (TM2.step m))^[Classical.choose (hrun x)]
    (some (initList (mkFinTM2_4 main init m)
      (List.map (@Equiv.invFun ((mkFinTM2_4 main init m).Γ (mkFinTM2_4 main init m).k₀)
        Bool (Equiv.refl Bool)) (bitEncode x)))) =
    some (haltList (mkFinTM2_4 main init m)
      (List.map (@Equiv.invFun ((mkFinTM2_4 main init m).Γ (mkFinTM2_4 main init m).k₁)
        Bool (Equiv.refl Bool)) (bitEncode (f x))))
  have hmi1 : List.map (@Equiv.invFun ((mkFinTM2_4 main init m).Γ (mkFinTM2_4 main init m).k₀)
      Bool (Equiv.refl Bool)) (bitEncode x) = bitEncode x := List.map_id _
  have hmi2 : List.map (@Equiv.invFun ((mkFinTM2_4 main init m).Γ (mkFinTM2_4 main init m).k₁)
      Bool (Equiv.refl Bool)) (bitEncode (f x)) = bitEncode (f x) := List.map_id _
  rw [hmi1, hmi2]
  rw [init_mk4, halt_mk4]
  exact (Classical.choose_spec (hrun x)).2

/- ### Reusable `Stk4` Sub-Routines -/

section SubRoutines

private theorem rev_s1_s0_halt {Λ : Type} {m : Λ → TM2.Stmt (fun _ : Stk4 => Bool) Λ (Option Bool)}
    {lRev : Λ}
    (hm : m lRev = (.pop Stk4.s1 (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push Stk4.s0 (fun v => v.getD false) (.goto fun _ => lRev))
        .halt)) :
    ∀ (b a c d : List Bool) (o : Option Bool),
    (flip bind (TM2.step m))^[b.length + 1]
      (some ⟨some lRev, o, mk4 a b c d⟩) =
    some ⟨none, none, mk4 (b.reverse ++ a) [] c d⟩
  | [], a, c, d, o => by
    rw [List.length_nil, iter_step]; simp [hm]
  | x :: b, a, c, d, o => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [hm]); rw [rev_s1_s0_halt hm b (x :: a) c d (some x)]
    simp

private theorem rev_s1_s2_goto {Λ : Type} {m : Λ → TM2.Stmt (fun _ : Stk4 => Bool) Λ (Option Bool)}
    {lRev lNext : Λ}
    (hm : m lRev = (.pop Stk4.s1 (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push Stk4.s2 (fun v => v.getD false) (.goto fun _ => lRev))
        (.goto fun _ => lNext))) :
    ∀ (b a c d : List Bool) (o : Option Bool),
    (flip bind (TM2.step m))^[b.length + 1]
      (some ⟨some lRev, o, mk4 a b c d⟩) =
    some ⟨some lNext, none, mk4 a [] (b.reverse ++ c) d⟩
  | [], a, c, d, o => by
    rw [List.length_nil, iter_step]; simp [hm]
  | x :: b, a, c, d, o => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [hm]); rw [rev_s1_s2_goto hm b a (x :: c) d (some x)]
    simp

private theorem drain_s0_goto {Λ : Type} {m : Λ → TM2.Stmt (fun _ : Stk4 => Bool) Λ (Option Bool)}
    {lDrain lNext : Λ}
    (hm : m lDrain = (.pop Stk4.s0 (fun _ o => o) <|
      .branch (fun v => v.isSome) (.goto fun _ => lDrain) (.goto fun _ => lNext))) :
    ∀ (a b c d : List Bool) (o : Option Bool),
    (flip bind (TM2.step m))^[a.length + 1]
      (some ⟨some lDrain, o, mk4 a b c d⟩) =
    some ⟨some lNext, none, mk4 [] b c d⟩
  | [], b, c, d, o => by
    rw [List.length_nil, iter_step]; simp [hm]
  | _ :: a, b, c, d, o => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [hm])
    exact drain_s0_goto hm a b c d _

private theorem undelim_s0_s1_goto {Λ : Type}
    {m : Λ → TM2.Stmt (fun _ : Stk4 => Bool) Λ (Option Bool)} {lUnd lNext : Λ}
    (hm : m lUnd = (.pop Stk4.s0 (fun _ o => o) <|
      .branch (fun v => v == some true)
        (.pop Stk4.s0 (fun _ o => o) <|
          .push Stk4.s1 (fun v => v.getD false) (.goto fun _ => lUnd))
        (.load (fun _ => none) (.goto fun _ => lNext)))) :
    ∀ (u rest b c d : List Bool) (o : Option Bool),
    (flip bind (TM2.step m))^[u.length + 1]
      (some ⟨some lUnd, o, mk4 (delimit u ++ rest) b c d⟩) =
    some ⟨some lNext, none, mk4 rest (u.reverse ++ b) c d⟩
  | [], rest, b, c, d, o => by
    rw [List.length_nil, iter_step]; simp [delimit, hm]
  | x :: u, rest, b, c, d, o => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [delimit, hm]); rw [undelim_s0_s1_goto hm u rest (x :: b) c d (some x)]
    simp

private theorem skipDelim_s0_goto {Λ : Type}
    {m : Λ → TM2.Stmt (fun _ : Stk4 => Bool) Λ (Option Bool)} {lSkip lNext : Λ}
    (hm : m lSkip = (.pop Stk4.s0 (fun _ o => o) <|
      .branch (fun v => v == some true)
        (.pop Stk4.s0 (fun _ _ => none) (.goto fun _ => lSkip))
        (.load (fun _ => none) (.goto fun _ => lNext)))) :
    ∀ (u rest b c d : List Bool) (o : Option Bool),
    (flip bind (TM2.step m))^[u.length + 1]
      (some ⟨some lSkip, o, mk4 (delimit u ++ rest) b c d⟩) =
    some ⟨some lNext, none, mk4 rest b c d⟩
  | [], rest, b, c, d, o => by
    rw [List.length_nil, iter_step]; simp [delimit, hm]
  | _ :: u, rest, b, c, d, o => by
    rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [delimit, hm])
    exact skipDelim_s0_goto hm u rest b c d none

end SubRoutines

/- ### Basic Combinator Primitives: `fst`, `snd`, `const`, `select`, `ite` -/

private theorem isPolyTime_fst {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    IsPolyTime (Prod.fst : α × β → α) := by
  let prog : Fin 3 → TM2.Stmt (fun _ : Stk4 => Bool) (Fin 3) (Option Bool)
    | ⟨0, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.pop Stk4.s0 (fun _ o => o) <|
            .push Stk4.s1 (fun v => v.getD false) (.goto fun _ => 0))
          (.load (fun _ => none) (.goto fun _ => 1))
    | ⟨1, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v.isSome) (.goto fun _ => 1) (.goto fun _ => 2)
    | ⟨2, _⟩ => .pop Stk4.s1 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push Stk4.s0 (fun v => v.getD false) (.goto fun _ => 2))
          .halt
  refine mkBoolPolyTime Prod.fst 0 none prog (2 * Polynomial.X + 3) (fun ⟨a, b⟩ => ?_)
  have h1 := undelim_s0_s1_goto (m := prog) (lUnd := 0) (lNext := 1) rfl
    (bitEncode a) (bitEncode b) [] [] [] none
  have h2 := drain_s0_goto (m := prog) (lDrain := 1) (lNext := 2) rfl
    (bitEncode b) (bitEncode a).reverse [] [] none
  have h3 := rev_s1_s0_halt (m := prog) (lRev := 2) rfl
    (bitEncode a).reverse [] [] [] none
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at h1 h2 h3
  refine ⟨_, ?_, iter_trans (iter_trans h1 h2) h3⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]; change _ ≤ 2 * (delimit (bitEncode a) ++ bitEncode b).length + 3
  rw [List.length_append, length_delimit]; omega

private theorem isPolyTime_snd {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    IsPolyTime (Prod.snd : α × β → β) := by
  let prog : Fin 2 → TM2.Stmt (fun _ : Stk4 => Bool) (Fin 2) (Option Bool)
    | ⟨0, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.pop Stk4.s0 (fun _ _ => none) (.goto fun _ => 0))
          (.load (fun _ => none) (.goto fun _ => 1))
    | ⟨1, _⟩ => .halt
  refine mkBoolPolyTime Prod.snd 0 none prog (Polynomial.X + 2) (fun ⟨a, b⟩ => ?_)
  have h1 := skipDelim_s0_goto (m := prog) (lSkip := 0) (lNext := 1) rfl
    (bitEncode a) (bitEncode b) [] [] [] none
  have h2 : (flip bind (TM2.step prog))^[1]
      (some ⟨some 1, none, mk4 (bitEncode b) [] [] []⟩) =
      some ⟨none, none, mk4 (bitEncode b) [] [] []⟩ := rfl
  refine ⟨_, ?_, iter_trans h1 h2⟩
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]; change _ ≤ (delimit (bitEncode a) ++ bitEncode b).length + 2
  rw [List.length_append, length_delimit]; omega

private def pushListStmt {Λ σ : Type} (l : List Bool) (next : TM2.Stmt (fun _ : Stk4 => Bool) Λ σ) :
    TM2.Stmt (fun _ : Stk4 => Bool) Λ σ :=
  l.foldr (fun b q => .push Stk4.s0 (fun _ => b) q) next

private theorem stepAux_pushListStmt {Λ σ : Type} (l : List Bool)
    (next : TM2.Stmt (fun _ : Stk4 => Bool) Λ σ) (v : σ) (a b c d : List Bool) :
    TM2.stepAux (pushListStmt l next) v (mk4 a b c d) =
      TM2.stepAux next v (mk4 (l.reverse ++ a) b c d) := by
  induction l generalizing a with
  | nil => simp [pushListStmt]
  | cons x l ih =>
    simp only [pushListStmt, List.foldr_cons, TM2.stepAux, upd4_s0, mk4_s0]
    change TM2.stepAux (pushListStmt l next) v (mk4 (x :: a) b c d) = _
    rw [ih (x :: a)]; simp

private theorem isPolyTime_const {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (c : β) : IsPolyTime (fun _ : α => c) := by
  let prog : Fin 2 → TM2.Stmt (fun _ : Stk4 => Bool) (Fin 2) (Option Bool)
    | ⟨0, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v.isSome) (.goto fun _ => 0) (.goto fun _ => 1)
    | ⟨1, _⟩ => pushListStmt (bitEncode c).reverse .halt
  refine mkBoolPolyTime (fun _ => c) 0 none prog (Polynomial.X + 2) (fun x => ?_)
  have h1 := drain_s0_goto (m := prog) (lDrain := 0) (lNext := 1) rfl
    (bitEncode x) [] [] [] none
  have h2 : (flip bind (TM2.step prog))^[1]
      (some ⟨some 1, none, mk4 [] [] [] []⟩) =
      some ⟨none, none, mk4 (bitEncode c) [] [] []⟩ := by
    rw [iter_succ_of]
    · rfl
    · simp only [TM2.step, prog, stepAux_pushListStmt, List.reverse_reverse, List.append_nil,
        TM2.stepAux]
  refine ⟨_, ?_, iter_trans h1 h2⟩
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]; omega

private theorem isPolyTime_select {α : Type} [BitstringEncoding α] :
    IsPolyTime (fun p : Bool × (α × α) => if p.1 then p.2.1 else p.2.2) := by
  let prog : Fin 5 → TM2.Stmt (fun _ : Stk4 => Bool) (Fin 5) (Option Bool)
    | ⟨0, _⟩ =>
        .pop Stk4.s0 (fun _ _ => none) <|
        .pop Stk4.s0 (fun _ o => o) <|
        .pop Stk4.s0 (fun v _ => v) <|
        .branch (fun v => v == some true)
          (.load (fun _ => none) (.goto fun _ => 1))
          (.load (fun _ => none) (.goto fun _ => 4))
    | ⟨1, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.pop Stk4.s0 (fun _ o => o) <|
            .push Stk4.s1 (fun v => v.getD false) (.goto fun _ => 1))
          (.load (fun _ => none) (.goto fun _ => 2))
    | ⟨2, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v.isSome) (.goto fun _ => 2) (.goto fun _ => 3)
    | ⟨3, _⟩ => .pop Stk4.s1 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push Stk4.s0 (fun v => v.getD false) (.goto fun _ => 3))
          .halt
    | ⟨4, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.pop Stk4.s0 (fun _ _ => none) (.goto fun _ => 4))
          (.load (fun _ => none) .halt)
  refine mkBoolPolyTime (fun p : Bool × (α × α) => if p.1 then p.2.1 else p.2.2)
    0 none prog (2 * Polynomial.X + 5) (fun ⟨b, x, y⟩ => ?_)
  have henc : bitEncode (b, (x, y)) =
      true :: b :: false :: (delimit (bitEncode x) ++ bitEncode y) := rfl
  cases b with
  | true =>
    have h0 : (flip bind (TM2.step prog))^[1]
        (some ⟨some 0, none, mk4 (bitEncode (true, (x, y))) [] [] []⟩) =
        some ⟨some 1, none, mk4 (delimit (bitEncode x) ++ bitEncode y) [] [] []⟩ := by
      rw [henc, iter_step]; simp [prog]
    have h1 := undelim_s0_s1_goto (m := prog) (lUnd := 1) (lNext := 2) rfl
      (bitEncode x) (bitEncode y) [] [] [] none
    have h2 := drain_s0_goto (m := prog) (lDrain := 2) (lNext := 3) rfl
      (bitEncode y) (bitEncode x).reverse [] [] none
    have h3 := rev_s1_s0_halt (m := prog) (lRev := 3) rfl
      (bitEncode x).reverse [] [] [] none
    simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at h1 h2 h3
    refine ⟨_, ?_, iter_trans (iter_trans (iter_trans h0 h1) h2) h3⟩
    rw [henc]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,
      List.length_cons, List.length_append, length_delimit]
    omega
  | false =>
    have h0 : (flip bind (TM2.step prog))^[1]
        (some ⟨some 0, none, mk4 (bitEncode (false, (x, y))) [] [] []⟩) =
        some ⟨some 4, none, mk4 (delimit (bitEncode x) ++ bitEncode y) [] [] []⟩ := by
      rw [henc, iter_step]; simp [prog]
    have hskip : ∀ (u rest : List Bool) (o : Option Bool),
        (flip bind (TM2.step prog))^[u.length + 1]
          (some ⟨some 4, o, mk4 (delimit u ++ rest) [] [] []⟩) =
        some ⟨none, none, mk4 rest [] [] []⟩ := by
      intro u
      induction u with
      | nil =>
        intro rest o
        rw [List.length_nil, iter_step]; simp [delimit, prog]
      | cons z u ih =>
        intro rest o
        rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [delimit, prog])
        exact ih rest none
    refine ⟨_, ?_, iter_trans h0 (hskip (bitEncode x) (bitEncode y) none)⟩
    rw [henc]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,
      List.length_cons, List.length_append, length_delimit]
    omega

private theorem isPolyTime_ite {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {c : α → Bool} {f g : α → β} (hc : IsPolyTime c) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => if c x then f x else g x) :=
  isPolyTime_seq (isPolyTime_pair hc (isPolyTime_pair hf hg)) isPolyTime_select

/- ### Unary List-Length and Unary Addition -/

private theorem isPolyTime_unaryLen {α : Type} [BitstringEncoding α] :
    IsPolyTime (fun x : α => List.replicate (bitEncode x).length false) := by
  let prog : Fin 2 → TM2.Stmt (fun _ : Stk4 => Bool) (Fin 2) (Option Bool)
    | ⟨0, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push Stk4.s1 (fun _ => true) <|
            .push Stk4.s1 (fun _ => false) <|
            .push Stk4.s1 (fun _ => false) (.goto fun _ => 0))
          (.goto fun _ => 1)
    | ⟨1, _⟩ => .pop Stk4.s1 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push Stk4.s0 (fun v => v.getD false) (.goto fun _ => 1))
          .halt
  refine mkBoolPolyTime (fun x : α => List.replicate (bitEncode x).length false)
    0 none prog (4 * Polynomial.X + 2) (fun x => ?_)
  have h1 : ∀ (l acc : List Bool) (o : Option Bool),
      (flip bind (TM2.step prog))^[l.length + 1]
        (some ⟨some 0, o, mk4 l acc [] []⟩) =
      some ⟨some 1, none,
        mk4 [] ((bitEncode (List.replicate l.length false)).reverse ++ acc) [] []⟩ := by
    intro l
    induction l with
    | nil =>
      intro acc o
      rw [List.length_nil, iter_step]; simp [prog]; try rfl
    | cons _ l ih =>
      intro acc o
      rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog]); rw [ih (false :: false :: true :: acc) _]
      have hrep : bitEncode (List.replicate (l.length + 1) false) =
          true :: false :: false :: bitEncode (List.replicate l.length false) := rfl
      rw [hrep]
      simp [List.reverse_cons]
  have hp1 := h1 (bitEncode x) [] none
  simp only [List.append_nil] at hp1
  have hp2 := rev_s1_s0_halt (m := prog) (lRev := 1) rfl
    (bitEncode (List.replicate (bitEncode x).length false)).reverse [] [] [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hp2
  refine ⟨_, ?_, iter_trans hp1 hp2⟩
  rw [bitEncode_listBool_length, List.length_replicate]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

private theorem bitEncode_list_append {α : Type} [BitstringEncoding α] (u v : List α) :
    bitEncode (u ++ v) = bitEncode u ++ bitEncode v := by
  change (((u ++ v).map bitEncode).map delimit).flatten =
    ((u.map bitEncode).map delimit).flatten ++ ((v.map bitEncode).map delimit).flatten
  simp [List.map_append, List.flatten_append]

private theorem isPolyTime_listAppend {α : Type} [BitstringEncoding α] :
    IsPolyTime (fun p : List α × List α => p.1 ++ p.2) := by
  let prog : Fin 2 → TM2.Stmt (fun _ : Stk4 => Bool) (Fin 2) (Option Bool)
    | ⟨0, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.pop Stk4.s0 (fun _ o => o) <|
            .push Stk4.s1 (fun v => v.getD false) (.goto fun _ => 0))
          (.load (fun _ => none) (.goto fun _ => 1))
    | ⟨1, _⟩ => .pop Stk4.s1 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push Stk4.s0 (fun v => v.getD false) (.goto fun _ => 1))
          .halt
  refine mkBoolPolyTime (fun p : List α × List α => p.1 ++ p.2)
    0 none prog (2 * Polynomial.X + 2) (fun ⟨u, v⟩ => ?_)
  have h1 := undelim_s0_s1_goto (m := prog) (lUnd := 0) (lNext := 1) rfl
    (bitEncode u) (bitEncode v) [] [] [] none
  have h2 := rev_s1_s0_halt (m := prog) (lRev := 1) rfl
    (bitEncode u).reverse (bitEncode v) [] [] none
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at h1 h2
  rw [bitEncode_list_append]
  refine ⟨_, ?_, iter_trans h1 h2⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]; change _ ≤ 2 * (delimit (bitEncode u) ++ bitEncode v).length + 2
  rw [List.length_append, length_delimit]; omega

/- ### Binary `ℕ` Encoding Lemmas and Primitives -/

private theorem bitEncode_nat_eq (n : ℕ) : bitEncode n = encodeNat n := rfl

private theorem encodeNat_zero : encodeNat 0 = [] := rfl

private theorem encodeNat_bit1 (n : ℕ) : encodeNat (2 * n + 1) = true :: encodeNat n := by
  have h1 : ∀ p : PosNum, ((PosNum.bit1 p : ℕ) : Num) = Num.pos (PosNum.bit1 p) := fun p => by
    simpa [PosNum.cast_to_num] using Num.of_to_nat (Num.pos p.bit1)
  cases h : (n : Num) with
  | zero =>
    have hn : n = 0 := by
      have := congrArg (fun m : Num => (m : ℕ)) h
      simpa [Num.to_of_nat] using this
    subst hn; rfl
  | pos p =>
    have hn : n = (p : ℕ) := by
      have := congrArg (fun m : Num => (m : ℕ)) h
      simpa [Num.to_of_nat] using this
    have h2 : 2 * n + 1 = (PosNum.bit1 p : ℕ) := by
      rw [hn]; simp; omega
    simp only [encodeNat, h2, h1, h, encodeNum, encodePosNum]

private theorem encodeNat_bit0 {n : ℕ} (hn : n ≠ 0) : encodeNat (2 * n) = false :: encodeNat n := by
  have h1 : ∀ p : PosNum, ((PosNum.bit0 p : ℕ) : Num) = Num.pos (PosNum.bit0 p) := fun p => by
    simpa [PosNum.cast_to_num] using Num.of_to_nat (Num.pos p.bit0)
  cases h : (n : Num) with
  | zero =>
    exfalso; apply hn
    have := congrArg (fun m : Num => (m : ℕ)) h
    simpa [Num.to_of_nat] using this
  | pos p =>
    have hn' : n = (p : ℕ) := by
      have := congrArg (fun m : Num => (m : ℕ)) h
      simpa [Num.to_of_nat] using this
    have h2 : 2 * n = (PosNum.bit0 p : ℕ) := by
      rw [hn']; simp; omega
    simp only [encodeNat, h2, h1, h, encodeNum, encodePosNum]

private theorem encodeNat_pos {n : ℕ} (hn : n ≠ 0) :
    encodeNat n = decide (n % 2 = 1) :: encodeNat (n / 2) := by
  have hdiv := Nat.div_add_mod n 2
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · have hq : n / 2 ≠ 0 := by omega
    have hEq : n = 2 * (n / 2) := by omega
    conv_lhs => rw [hEq]
    rw [encodeNat_bit0 hq, h0]; rfl
  · have hEq : n = 2 * (n / 2) + 1 := by omega
    conv_lhs => rw [hEq]
    rw [encodeNat_bit1, h1]; rfl

private theorem encodeNat_div2 (n : ℕ) : encodeNat (n / 2) = (encodeNat n).tail := by
  by_cases hn : n = 0
  · subst hn; rfl
  · rw [encodeNat_pos hn]; rfl

private theorem encodeNat_eq_nil_iff (n : ℕ) : encodeNat n = [] ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    rw [encodeNat_pos hn] at h; cases h
  · intro h; subst h; rfl

private theorem length_encodeNat (n : ℕ) : (encodeNat n).length = n.size := by
  have hpos : ∀ p : PosNum, (encodePosNum p).length = p.natSize := by
    intro p; induction p <;> simp_all [encodePosNum, PosNum.natSize]
  have hnum : ∀ m : Num, (encodeNum m).length = m.natSize := by
    intro m; cases m with
    | zero => rfl
    | pos p => exact hpos p
  calc (encodeNat n).length = (n : Num).natSize := hnum (n : Num)
    _ = n.size := by rw [Num.natSize_to_nat, Num.to_of_nat]

private theorem lt_two_pow_length_encodeNat (n : ℕ) : n < 2 ^ (encodeNat n).length := by
  rw [length_encodeNat]; exact Nat.lt_size_self n

private theorem length_encodeNat_le {n k : ℕ} (h : n < 2 ^ k) : (encodeNat n).length ≤ k := by
  rw [length_encodeNat]; exact Nat.size_le.mpr h

private theorem isPolyTime_natIsZero : IsPolyTime (fun n : ℕ => decide (n = 0)) := by
  let prog : Fin 2 → TM2.Stmt (fun _ : Stk4 => Bool) (Fin 2) (Option Bool)
    | ⟨0, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.load (fun _ => none) (.goto fun _ => 1))
          (.push Stk4.s0 (fun _ => true) .halt)
    | ⟨1, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.goto fun _ => 1)
          (.push Stk4.s0 (fun _ => false) .halt)
  refine mkBoolPolyTime (fun n : ℕ => decide (n = 0)) 0 none prog
    (Polynomial.X + 2) (fun n => ?_)
  cases hn : bitEncode n with
  | nil =>
    have hz : n = 0 := (encodeNat_eq_nil_iff n).mp hn
    subst hz
    refine ⟨1, by simp, ?_⟩
    rw [iter_step]; simp [prog]; rfl
  | cons b l =>
    have hnz : n ≠ 0 := by intro hz; subst hz; exact List.cons_ne_nil b l hn.symm
    have h0 : (flip bind (TM2.step prog))^[1]
        (some ⟨some 0, none, mk4 (b :: l) [] [] []⟩) =
        some ⟨some 1, none, mk4 l [] [] []⟩ := by
      rw [iter_step]; simp [prog]; try rfl
    have h1 : ∀ (r : List Bool) (o : Option Bool),
        (flip bind (TM2.step prog))^[r.length + 1]
          (some ⟨some 1, o, mk4 r [] [] []⟩) =
        some ⟨none, none, mk4 [false] [] [] []⟩ := by
      intro r; induction r with
      | nil =>
        intro o; rw [List.length_nil, iter_step]; simp [prog]
      | cons _ r ih =>
        intro o; rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog])
        exact ih _
    have hdec : decide (n = 0) = false := decide_eq_false hnz
    rw [hdec]
    refine ⟨(l.length + 1) + 1, ?_, ?_⟩
    · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat,
        List.length_cons]; omega
    · exact iter_trans h0 (h1 l none)

private theorem isPolyTime_natLsb : IsPolyTime (fun n : ℕ => decide (n % 2 = 1)) := by
  let prog : Fin 3 → TM2.Stmt (fun _ : Stk4 => Bool) (Fin 3) (Option Bool)
    | ⟨0, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.load (fun _ => none) (.goto fun _ => 1))
          (.load (fun _ => none) (.goto fun _ => 2))
    | ⟨1, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.goto fun _ => 1)
          (.push Stk4.s0 (fun _ => true) .halt)
    | ⟨2, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.goto fun _ => 2)
          (.push Stk4.s0 (fun _ => false) .halt)
  refine mkBoolPolyTime (fun n : ℕ => decide (n % 2 = 1)) 0 none prog
    (Polynomial.X + 2) (fun n => ?_)
  have hdrain : ∀ (idx : Fin 3) (res : Bool),
      prog idx = (.pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.goto fun _ => idx)
          (.push Stk4.s0 (fun _ => res) .halt)) →
      ∀ (r : List Bool) (o : Option Bool),
      (flip bind (TM2.step prog))^[r.length + 1]
        (some ⟨some idx, o, mk4 r [] [] []⟩) =
      some ⟨none, none, mk4 [res] [] [] []⟩ := by
    intro idx res hidx r
    induction r with
    | nil =>
      intro o; rw [List.length_nil, iter_step]; simp [hidx]
    | cons _ r ih =>
      intro o; rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [hidx])
      exact ih _
  by_cases hn : n = 0
  · subst hn
    have h0 : (flip bind (TM2.step prog))^[1]
        (some ⟨some 0, none, mk4 [] [] [] []⟩) =
        some ⟨some 2, none, mk4 [] [] [] []⟩ := by
      rw [iter_step]; simp [prog]; try rfl
    refine ⟨(0 + 1) + 1, by simp, ?_⟩
    exact iter_trans h0 (hdrain 2 false rfl [] none)
  · have hpos := encodeNat_pos hn
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
    · have hbit : bitEncode n = false :: encodeNat (n / 2) := by
        rw [bitEncode_nat_eq, hpos, h0]; rfl
      have hs0 : (flip bind (TM2.step prog))^[1]
          (some ⟨some 0, none, mk4 (bitEncode n) [] [] []⟩) =
          some ⟨some 2, none, mk4 (encodeNat (n / 2)) [] [] []⟩ := by
        rw [hbit, iter_step]; simp [prog]
      have hdec : decide (n % 2 = 1) = false := by rw [h0]; rfl
      rw [hdec]
      refine ⟨((encodeNat (n / 2)).length + 1) + 1, ?_,
        iter_trans hs0 (hdrain 2 false rfl (encodeNat (n / 2)) none)⟩
      rw [hbit]; simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat,
        List.length_cons]; omega
    · have hbit : bitEncode n = true :: encodeNat (n / 2) := by
        rw [bitEncode_nat_eq, hpos, h1]; rfl
      have hs0 : (flip bind (TM2.step prog))^[1]
          (some ⟨some 0, none, mk4 (bitEncode n) [] [] []⟩) =
          some ⟨some 1, none, mk4 (encodeNat (n / 2)) [] [] []⟩ := by
        rw [hbit, iter_step]; simp [prog]
      have hdec : decide (n % 2 = 1) = true := by rw [h1]; rfl
      rw [hdec]
      refine ⟨((encodeNat (n / 2)).length + 1) + 1, ?_,
        iter_trans hs0 (hdrain 1 true rfl (encodeNat (n / 2)) none)⟩
      rw [hbit]; simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat,
        List.length_cons]; omega

private theorem isPolyTime_natDiv2 : IsPolyTime (fun n : ℕ => n / 2) := by
  let prog : Unit → TM2.Stmt (fun _ : Stk4 => Bool) Unit Unit
    | () => .pop Stk4.s0 (fun _ _ => ()) .halt
  refine mkBoolPolyTime (fun n : ℕ => n / 2) () () prog 1 (fun n => ?_)
  refine ⟨1, by simp, ?_⟩
  rw [iter_step]; simp [prog, bitEncode_nat_eq, encodeNat_div2]

private theorem isPolyTime_natMul2Add :
    IsPolyTime (fun p : ℕ × Bool => 2 * p.1 + if p.2 then 1 else 0) := by
  let prog : Fin 3 → TM2.Stmt (fun _ : Stk4 => Bool) (Fin 3) (Option Bool)
    | ⟨0, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.pop Stk4.s0 (fun _ o => o) <|
            .push Stk4.s1 (fun v => v.getD false) (.goto fun _ => 0))
          (.load (fun _ => none) (.goto fun _ => 1))
    | ⟨1, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .push Stk4.s2 (fun v => v.getD false) (.load (fun _ => none) (.goto fun _ => 2))
    | ⟨2, _⟩ => .pop Stk4.s1 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push Stk4.s0 (fun v => v.getD false) (.goto fun _ => 2))
          (.pop Stk4.s2 (fun _ o => o) <|
            .branch (fun v => v == some true)
              (.push Stk4.s0 (fun _ => true) (.load (fun _ => none) .halt))
              (.peek Stk4.s0 (fun _ o => o) <|
                .branch (fun v => v.isSome)
                  (.push Stk4.s0 (fun _ => false) (.load (fun _ => none) .halt))
                  (.load (fun _ => none) .halt)))
  refine mkBoolPolyTime (fun p : ℕ × Bool => 2 * p.1 + if p.2 then 1 else 0)
    0 none prog (2 * Polynomial.X + 4) (fun ⟨n, b⟩ => ?_)
  have h1 := undelim_s0_s1_goto (m := prog) (lUnd := 0) (lNext := 1) rfl
    (bitEncode n) [b] [] [] [] none
  simp only [List.append_nil] at h1
  have h2 : (flip bind (TM2.step prog))^[1]
      (some ⟨some 1, none, mk4 [b] (bitEncode n).reverse [] []⟩) =
      some ⟨some 2, none, mk4 [] (bitEncode n).reverse [b] []⟩ := by
    rw [iter_step]; simp [prog]; try rfl
  have hrev : ∀ (l a : List Bool) (o : Option Bool),
      ∃ o', (flip bind (TM2.step prog))^[l.length]
        (some ⟨some 2, o, mk4 a l [b] []⟩) =
      some ⟨some 2, o', mk4 (l.reverse ++ a) [] [b] []⟩ := by
    intro l; induction l with
    | nil => intro a o; exact ⟨o, by simp⟩
    | cons x l ih =>
      intro a o
      obtain ⟨o', ho'⟩ := ih (x :: a) (some x)
      refine ⟨o', ?_⟩
      rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog])
      simpa using ho'
  obtain ⟨o', h3⟩ := hrev (bitEncode n).reverse [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h3
  have h4 : (flip bind (TM2.step prog))^[1]
      (some ⟨some 2, o', mk4 (bitEncode n) [] [b] []⟩) =
      some ⟨none, none, mk4 (bitEncode (2 * n + if b then 1 else 0)) [] [] []⟩ := by
    rw [iter_step]
    cases b with
    | true =>
      simp [prog, bitEncode_nat_eq, encodeNat_bit1]
    | false =>
      by_cases hn : n = 0
      · subst hn
        simp [prog, bitEncode_nat_eq, encodeNat_zero]
      · have hne : bitEncode n ≠ [] := by
          intro h; exact hn ((encodeNat_eq_nil_iff n).mp h)
        cases hbn : bitEncode n with
        | nil => exact absurd hbn hne
        | cons d ds =>
          have hbe : bitEncode (2 * n + 0) = false :: d :: ds := by
            change encodeNat (2 * n) = _
            rw [encodeNat_bit0 hn]; exact congrArg (false :: ·) hbn
          simp only [Bool.false_eq_true, ↓reduceIte, hbe]
          simp [prog]
  refine ⟨_, ?_, iter_trans (iter_trans (iter_trans h1 h2) h3) h4⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]; change _ ≤ 2 * (delimit (bitEncode n) ++ [b]).length + 4
  rw [List.length_append, length_delimit, List.length_singleton]; omega

/- ### Binary Addition (`natAdd`) -/

private def addBits (c : Bool) : List Bool → List Bool → List Bool
  | [], [] => if c then [true] else []
  | x :: xs, [] => (xor x c) :: addBits (x && c) xs []
  | [], y :: ys => (xor y c) :: addBits (y && c) [] ys
  | x :: xs, y :: ys =>
      (xor (xor x y) c) :: addBits ((x && y) || (x && c) || (y && c)) xs ys

private theorem addBits_encodeNat : ∀ (n : ℕ) (a b : ℕ) (c : Bool), a + b ≤ n →
    addBits c (encodeNat a) (encodeNat b) = encodeNat (a + b + c.toNat)
  | 0, a, b, c, hab => by
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb
    cases c <;> simp [addBits, encodeNat_zero]; rfl
  | n + 1, a, b, c, hab => by
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · subst ha; subst hb; cases c <;> simp [addBits, encodeNat_zero]; rfl
      · subst ha
        rw [encodeNat_zero, encodeNat_pos hb, addBits]
        have hpos : 0 + b + c.toNat ≠ 0 := by omega
        rw [encodeNat_pos hpos]
        have hih := addBits_encodeNat n 0 (b / 2) (decide (b % 2 = 1) && c) (by omega)
        rw [encodeNat_zero] at hih
        rw [hih]
        congr 1
        · cases c <;> rcases Nat.mod_two_eq_zero_or_one b with h | h <;> simp [h] <;> omega
        · congr 1
          cases c <;> rcases Nat.mod_two_eq_zero_or_one b with h | h <;> simp [h] <;> omega
    · by_cases hb : b = 0
      · subst hb
        rw [encodeNat_zero, encodeNat_pos ha, addBits]
        have hpos : a + 0 + c.toNat ≠ 0 := by omega
        rw [encodeNat_pos hpos]
        have hih := addBits_encodeNat n (a / 2) 0 (decide (a % 2 = 1) && c) (by omega)
        rw [encodeNat_zero] at hih
        rw [hih]
        congr 1
        · cases c <;> rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h] <;> omega
        · congr 1
          cases c <;> rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h] <;> omega
      · rw [encodeNat_pos ha, encodeNat_pos hb, addBits]
        have hpos : a + b + c.toNat ≠ 0 := by omega
        rw [encodeNat_pos hpos]
        have hih := addBits_encodeNat n (a / 2) (b / 2)
          ((decide (a % 2 = 1) && decide (b % 2 = 1)) ||
           (decide (a % 2 = 1) && c) || (decide (b % 2 = 1) && c)) (by omega)
        rw [hih]
        congr 1
        · cases c <;> rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
            rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;> simp [h1, h2] <;> omega
        · congr 1
          cases c <;> rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
            rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;> simp [h1, h2] <;> omega

private theorem length_addBits_le (c : Bool) : ∀ (xs ys : List Bool),
    (addBits c xs ys).length ≤ max xs.length ys.length + 1
  | [], [] => by cases c <;> simp [addBits]
  | x :: xs, [] => by
    simp only [addBits, List.length_cons, List.length_nil]
    have := length_addBits_le (x && c) xs []; simp at this; omega
  | [], y :: ys => by
    simp only [addBits, List.length_cons, List.length_nil]
    have := length_addBits_le (y && c) [] ys; simp at this; omega
  | x :: xs, y :: ys => by
    simp only [addBits, List.length_cons]
    have := length_addBits_le ((x && y) || (x && c) || (y && c)) xs ys; omega

private abbrev AddVar : Type := Bool × Option Bool × Option Bool

private theorem isPolyTime_natAdd : IsPolyTime (fun p : ℕ × ℕ => p.1 + p.2) := by
  let prog : Fin 4 → TM2.Stmt (fun _ : Stk4 => Bool) (Fin 4) AddVar
    | ⟨0, _⟩ => .pop Stk4.s0 (fun v o => (v.1, o, v.2.2)) <|
        .branch (fun v => v.2.1 == some true)
          (.pop Stk4.s0 (fun v o => (v.1, o, v.2.2)) <|
            .push Stk4.s1 (fun v => v.2.1.getD false) (.goto fun _ => 0))
          (.load (fun _ => (false, none, none)) (.goto fun _ => 1))
    | ⟨1, _⟩ => .pop Stk4.s1 (fun v o => (v.1, o, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.push Stk4.s2 (fun v => v.2.1.getD false) (.goto fun _ => 1))
          (.load (fun _ => (false, none, none)) (.goto fun _ => 2))
    | ⟨2, _⟩ => .pop Stk4.s2 (fun v o => (v.1, o, v.2.2)) <|
        .pop Stk4.s0 (fun v o => (v.1, v.2.1, o)) <|
        .branch (fun v => v.2.1.isSome || v.2.2.isSome)
          (.push Stk4.s1
            (fun v => xor (xor (v.2.1.getD false) (v.2.2.getD false)) v.1) <|
            .load (fun v =>
              let ba := v.2.1.getD false
              let bb := v.2.2.getD false
              ((ba && bb) || (ba && v.1) || (bb && v.1), none, none))
            (.goto fun _ => 2))
          (.branch (fun v => v.1)
            (.push Stk4.s1 (fun _ => true)
              (.load (fun _ => (false, none, none)) (.goto fun _ => 3)))
            (.load (fun _ => (false, none, none)) (.goto fun _ => 3)))
    | ⟨3, _⟩ => .pop Stk4.s1 (fun v o => (v.1, o, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.push Stk4.s0 (fun v => v.2.1.getD false) (.goto fun _ => 3))
          (.load (fun _ => (false, none, none)) .halt)
  refine mkBoolPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
    0 (false, none, none) prog (4 * Polynomial.X + 6) (fun ⟨a, b⟩ => ?_)
  have h1 : ∀ (u rest s1 : List Bool) (o : Option Bool),
      (flip bind (TM2.step prog))^[u.length + 1]
        (some ⟨some 0, (false, o, none), mk4 (delimit u ++ rest) s1 [] []⟩) =
      some ⟨some 1, (false, none, none), mk4 rest (u.reverse ++ s1) [] []⟩ := by
    intro u; induction u with
    | nil =>
      intro rest s1 o
      rw [List.length_nil, iter_step]; simp [delimit, prog]
    | cons x u ih =>
      intro rest s1 o
      rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [delimit, prog]); rw [ih rest (x :: s1) (some x)]
      simp
  have h2 : ∀ (s1 s0 s2 : List Bool) (o : Option Bool),
      (flip bind (TM2.step prog))^[s1.length + 1]
        (some ⟨some 1, (false, o, none), mk4 s0 s1 s2 []⟩) =
      some ⟨some 2, (false, none, none), mk4 s0 [] (s1.reverse ++ s2) []⟩ := by
    intro s1; induction s1 with
    | nil =>
      intro s0 s2 o
      rw [List.length_nil, iter_step]; simp [prog]; try rfl
    | cons x s1 ih =>
      intro s0 s2 o
      rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog]); rw [ih s0 (x :: s2) (some x)]
      simp
  have h3 : ∀ (k : ℕ) (xs ys acc : List Bool) (c : Bool), xs.length + ys.length ≤ k →
      ∃ t ≤ max xs.length ys.length + 1,
      (flip bind (TM2.step prog))^[t]
        (some ⟨some 2, (c, none, none), mk4 ys acc xs []⟩) =
      some ⟨some 3, (false, none, none), mk4 [] ((addBits c xs ys).reverse ++ acc) [] []⟩ := by
    intro k; induction k with
    | zero =>
      intro xs ys acc c hxy
      cases xs <;> cases ys <;> try (simp at hxy)
      refine ⟨1, by simp, ?_⟩
      cases c <;>
        (rw [iter_step]; simp [prog]; try simp [addBits])
    | succ k ih =>
      intro xs ys acc c hxy
      cases xs with
      | nil =>
        cases ys with
        | nil =>
          refine ⟨1, by simp, ?_⟩
          cases c <;>
            (rw [iter_step]; simp [prog]; try simp [addBits])
        | cons y ys =>
          have hstep : (flip bind (TM2.step prog))^[1]
              (some ⟨some 2, (c, none, none), mk4 (y :: ys) acc [] []⟩) =
              some ⟨some 2, (y && c, none, none), mk4 ys (xor y c :: acc) [] []⟩ := by
            rw [iter_step]; simp [prog]; try rfl
          obtain ⟨t, htle, ht⟩ := ih [] ys (xor y c :: acc) (y && c) (by simp at hxy ⊢; omega)
          refine ⟨t + 1, by simp at htle ⊢; omega, ?_⟩
          have htr := iter_trans hstep ht
          simpa [addBits] using htr
      | cons x xs =>
        cases ys with
        | nil =>
          have hstep : (flip bind (TM2.step prog))^[1]
              (some ⟨some 2, (c, none, none), mk4 [] acc (x :: xs) []⟩) =
              some ⟨some 2, (x && c, none, none), mk4 [] (xor x c :: acc) xs []⟩ := by
            rw [iter_step]; simp [prog]; try rfl
          obtain ⟨t, htle, ht⟩ := ih xs [] (xor x c :: acc) (x && c) (by simp at hxy ⊢; omega)
          refine ⟨t + 1, by simp at htle ⊢; omega, ?_⟩
          have htr := iter_trans hstep ht
          simpa [addBits] using htr
        | cons y ys =>
          have hstep : (flip bind (TM2.step prog))^[1]
              (some ⟨some 2, (c, none, none), mk4 (y :: ys) acc (x :: xs) []⟩) =
              some ⟨some 2, ((x && y) || (x && c) || (y && c), none, none),
                mk4 ys (xor (xor x y) c :: acc) xs []⟩ := by
            rw [iter_step]; simp [prog]; try rfl
          obtain ⟨t, htle, ht⟩ := ih xs ys (xor (xor x y) c :: acc)
            ((x && y) || (x && c) || (y && c)) (by simp at hxy ⊢; omega)
          refine ⟨t + 1, by simp at htle ⊢; omega, ?_⟩
          have htr := iter_trans hstep ht
          simpa [addBits] using htr
  have h4 : ∀ (s1 s0 : List Bool) (o : Option Bool),
      (flip bind (TM2.step prog))^[s1.length + 1]
        (some ⟨some 3, (false, o, none), mk4 s0 s1 [] []⟩) =
      some ⟨none, (false, none, none), mk4 (s1.reverse ++ s0) [] [] []⟩ := by
    intro s1; induction s1 with
    | nil =>
      intro s0 o
      rw [List.length_nil, iter_step]; simp [prog]; try rfl
    | cons x s1 ih =>
      intro s0 o
      rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog]); rw [ih (x :: s0) (some x)]
      simp
  have hp1 := h1 (bitEncode a) (bitEncode b) [] none
  simp only [List.append_nil] at hp1
  have hp2 := h2 (bitEncode a).reverse (bitEncode b) [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hp2
  obtain ⟨t3, ht3le, hp3⟩ := h3 ((bitEncode a).length + (bitEncode b).length)
    (bitEncode a) (bitEncode b) [] false le_rfl
  simp only [List.append_nil] at hp3
  have hp4 := h4 (addBits false (bitEncode a) (bitEncode b)).reverse [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hp4
  have hsum : addBits false (bitEncode a) (bitEncode b) = bitEncode (a + b) := by
    simpa [bitEncode_nat_eq] using addBits_encodeNat (a + b) a b false le_rfl
  rw [hsum] at hp3 hp4
  have hlen : (bitEncode (a + b)).length ≤ max (bitEncode a).length (bitEncode b).length + 1 := by
    rw [← hsum]; exact length_addBits_le false (bitEncode a) (bitEncode b)
  refine ⟨_, ?_, iter_trans (iter_trans (iter_trans hp1 hp2) hp3) hp4⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]; change _ ≤ 4 * (delimit (bitEncode a) ++ bitEncode b).length + 6
  rw [List.length_append, length_delimit]; omega

/- ### Binary Subtraction and Comparison (`natSubCmp`) -/

private def trimLeadFalse : List Bool → List Bool
  | false :: l => trimLeadFalse l
  | l => l

private def subBits (bw : Bool) : List Bool → List Bool → Bool × List Bool
  | [], [] => (bw, [])
  | x :: xs, [] =>
      let res := subBits (!x && bw) xs []
      (res.1, xor x bw :: res.2)
  | [], y :: ys =>
      let res := subBits (y || bw) [] ys
      (res.1, xor y bw :: res.2)
  | x :: xs, y :: ys =>
      let nbw := (!x && y) || (!x && bw) || (y && bw)
      let res := subBits nbw xs ys
      (res.1, xor (xor x y) bw :: res.2)

private theorem trimLeadFalse_reverse_append_false (l : List Bool) :
    trimLeadFalse (false :: l) = trimLeadFalse l := rfl

private theorem trimLeadFalse_reverse_cons_true (l : List Bool) :
    trimLeadFalse (true :: l) = true :: l := rfl

private theorem trimLeadFalse_append_of_eq (l : List Bool) (b : Bool) :
    trimLeadFalse (l ++ [b]) =
      if trimLeadFalse l = [] then (if b then [true] else []) else trimLeadFalse l ++ [b] := by
  induction l with
  | nil => cases b <;> rfl
  | cons x l ih =>
    cases x with
    | false => exact ih
    | true => simp [trimLeadFalse]

private theorem subBits_encodeNat : ∀ (n : ℕ) (a b : ℕ) (bw : Bool), a + b ≤ n →
    (subBits bw (encodeNat a) (encodeNat b)).1 = decide (a < b + bw.toNat) ∧
    (b + bw.toNat ≤ a →
      (trimLeadFalse (subBits bw (encodeNat a) (encodeNat b)).2.reverse).reverse =
        encodeNat (a - (b + bw.toNat)))
  | 0, a, b, bw, hab => by
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb
    cases bw <;> simp [subBits, encodeNat_zero, trimLeadFalse]
  | n + 1, a, b, bw, hab => by
    have hstep_combine : ∀ (d : Bool) (nbw : Bool) (a' b' : ℕ)
        (hr1 : (subBits nbw (encodeNat a') (encodeNat b')).1 = decide (a' < b' + nbw.toNat))
        (hr2 : b' + nbw.toNat ≤ a' →
          (trimLeadFalse (subBits nbw (encodeNat a') (encodeNat b')).2.reverse).reverse =
            encodeNat (a' - (b' + nbw.toNat)))
        (hcmp : decide (a' < b' + nbw.toNat) = decide (a < b + bw.toNat))
        (hdiv : b + bw.toNat ≤ a → (a - (b + bw.toNat)) / 2 = a' - (b' + nbw.toNat) ∧
          b' + nbw.toNat ≤ a' ∧ decide ((a - (b + bw.toNat)) % 2 = 1) = d),
        (subBits nbw (encodeNat a') (encodeNat b')).1 = decide (a < b + bw.toNat) ∧
        (b + bw.toNat ≤ a →
          (trimLeadFalse (d :: (subBits nbw (encodeNat a') (encodeNat b')).2).reverse).reverse =
            encodeNat (a - (b + bw.toNat))) := by
      intro d nbw a' b' hr1 hr2 hcmp hdiv
      refine ⟨hr1.trans hcmp, fun hle => ?_⟩
      obtain ⟨hq, hle', hd⟩ := hdiv hle
      have hih_eq := hr2 hle'
      rw [List.reverse_cons, trimLeadFalse_append_of_eq]
      by_cases hq0 : a' - (b' + nbw.toNat) = 0
      · have htr : trimLeadFalse (subBits nbw (encodeNat a') (encodeNat b')).2.reverse = [] := by
          have := congrArg List.reverse hih_eq
          rw [List.reverse_reverse, hq0, encodeNat_zero] at this
          simpa using this
        rw [htr, if_pos rfl]
        cases d with
        | false =>
          have hmod : (a - (b + bw.toNat)) % 2 ≠ 1 := by
            intro h; rw [h] at hd; cases hd
          have hdiff0 : a - (b + bw.toNat) = 0 := by omega
          rw [hdiff0]; rfl
        | true =>
          have hmod : (a - (b + bw.toNat)) % 2 = 1 := by
            by_contra h
            have hf : decide ((a - (b + bw.toNat)) % 2 = 1) = false := decide_eq_false h
            rw [hf] at hd; cases hd
          have hdiff1 : a - (b + bw.toNat) = 1 := by omega
          rw [hdiff1]; rfl
      · have hne : trimLeadFalse (subBits nbw (encodeNat a') (encodeNat b')).2.reverse ≠ [] := by
          intro h
          rw [h, List.reverse_nil] at hih_eq
          exact hq0 ((encodeNat_eq_nil_iff _).mp hih_eq.symm)
        rw [if_neg hne, List.reverse_append, List.reverse_singleton, List.singleton_append, hih_eq]
        have hpos : a - (b + bw.toNat) ≠ 0 := by omega
        rw [encodeNat_pos hpos, hq, hd]
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · subst ha; subst hb; cases bw <;> simp [subBits, encodeNat_zero, trimLeadFalse]
      · subst ha
        rw [encodeNat_zero, encodeNat_pos hb, subBits]
        have ⟨hr1, hr2⟩ := subBits_encodeNat n 0 (b / 2) (decide (b % 2 = 1) || bw) (by omega)
        rw [encodeNat_zero] at hr1 hr2
        exact hstep_combine _ _ 0 (b / 2) hr1 hr2
          (by cases bw <;> rcases Nat.mod_two_eq_zero_or_one b with h | h <;> simp [h] <;> omega)
          (fun hle => by omega)
    · by_cases hb : b = 0
      · subst hb
        rw [encodeNat_zero, encodeNat_pos ha, subBits]
        have ⟨hr1, hr2⟩ := subBits_encodeNat n (a / 2) 0 (!decide (a % 2 = 1) && bw) (by omega)
        rw [encodeNat_zero] at hr1 hr2
        exact hstep_combine _ _ (a / 2) 0 hr1 hr2
          (by cases bw <;> rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h] <;> omega)
          (fun hle => by
            cases bw <;> rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h] <;> omega)
      · rw [encodeNat_pos ha, encodeNat_pos hb, subBits]
        let nbw := (!decide (a % 2 = 1) && decide (b % 2 = 1)) ||
          (!decide (a % 2 = 1) && bw) || (decide (b % 2 = 1) && bw)
        have ⟨hr1, hr2⟩ := subBits_encodeNat n (a / 2) (b / 2) nbw (by omega)
        exact hstep_combine _ nbw (a / 2) (b / 2) hr1 hr2
          (by cases bw <;> rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
            rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;> simp [nbw, h1, h2] <;> omega)
          (fun hle => by
            cases bw <;> rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
              rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;>
              simp only [Bool.toNat_true, Bool.toNat_false, Nat.add_zero] at hle ⊢ <;>
              refine ⟨by simp [nbw, h1, h2]; omega, by simp [nbw, h1, h2]; omega, ?_⟩ <;>
              simp [h1, h2] <;> omega)

private theorem length_subBits_le (bw : Bool) : ∀ (xs ys : List Bool),
    (subBits bw xs ys).2.length ≤ max xs.length ys.length
  | [], [] => by simp [subBits]
  | x :: xs, [] => by
    simp only [subBits, List.length_cons, List.length_nil]
    have := length_subBits_le (!x && bw) xs []; simp at this; omega
  | [], y :: ys => by
    simp only [subBits, List.length_cons, List.length_nil]
    have := length_subBits_le (y || bw) [] ys; simp at this; omega
  | x :: xs, y :: ys => by
    simp only [subBits, List.length_cons]
    have := length_subBits_le ((!x && y) || (!x && bw) || (y && bw)) xs ys; omega

private theorem length_trimLeadFalse_le : ∀ l : List Bool, (trimLeadFalse l).length ≤ l.length
  | [] => le_rfl
  | false :: l => by simp [trimLeadFalse]; have := length_trimLeadFalse_le l; omega
  | true :: l => le_rfl

private theorem isPolyTime_natSubCmp :
    IsPolyTime (fun p : ℕ × ℕ => (decide (p.2 ≤ p.1), p.1 - p.2)) := by
  let prog : Fin 6 → TM2.Stmt (fun _ : Stk4 => Bool) (Fin 6) AddVar
    | ⟨0, _⟩ => .pop Stk4.s0 (fun v o => (v.1, o, v.2.2)) <|
        .branch (fun v => v.2.1 == some true)
          (.pop Stk4.s0 (fun v o => (v.1, o, v.2.2)) <|
            .push Stk4.s1 (fun v => v.2.1.getD false) (.goto fun _ => 0))
          (.load (fun _ => (false, none, none)) (.goto fun _ => 1))
    | ⟨1, _⟩ => .pop Stk4.s1 (fun v o => (v.1, o, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.push Stk4.s2 (fun v => v.2.1.getD false) (.goto fun _ => 1))
          (.load (fun _ => (false, none, none)) (.goto fun _ => 2))
    | ⟨2, _⟩ => .pop Stk4.s2 (fun v o => (v.1, o, v.2.2)) <|
        .pop Stk4.s0 (fun v o => (v.1, v.2.1, o)) <|
        .branch (fun v => v.2.1.isSome || v.2.2.isSome)
          (.push Stk4.s1
            (fun v => xor (xor (v.2.1.getD false) (v.2.2.getD false)) v.1) <|
            .load (fun v =>
              let ba := v.2.1.getD false
              let bb := v.2.2.getD false
              ((!ba && bb) || (!ba && v.1) || (bb && v.1), none, none))
            (.goto fun _ => 2))
          (.branch (fun v => v.1)
            (.load (fun _ => (false, none, none)) (.goto fun _ => 3))
            (.load (fun _ => (false, none, none)) (.goto fun _ => 4)))
    | ⟨3, _⟩ => .pop Stk4.s1 (fun v o => (v.1, o, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.goto fun _ => 3)
          (.push Stk4.s0 (fun _ => false) <|
            .push Stk4.s0 (fun _ => false) <|
            .push Stk4.s0 (fun _ => true)
            (.load (fun _ => (false, none, none)) .halt))
    | ⟨4, _⟩ => .peek Stk4.s1 (fun v o => (v.1, o, v.2.2)) <|
        .branch (fun v => v.2.1 == some false)
          (.pop Stk4.s1 (fun _ _ => (false, none, none)) (.goto fun _ => 4))
          (.load (fun _ => (false, none, none)) (.goto fun _ => 5))
    | ⟨5, _⟩ => .pop Stk4.s1 (fun v o => (v.1, o, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.push Stk4.s0 (fun v => v.2.1.getD false) (.goto fun _ => 5))
          (.push Stk4.s0 (fun _ => false) <|
            .push Stk4.s0 (fun _ => true) <|
            .push Stk4.s0 (fun _ => true)
            (.load (fun _ => (false, none, none)) .halt))
  refine mkBoolPolyTime (fun p : ℕ × ℕ => (decide (p.2 ≤ p.1), p.1 - p.2))
    0 (false, none, none) prog (6 * Polynomial.X + 8) (fun ⟨a, b⟩ => ?_)
  have h1 : ∀ (u rest s1 : List Bool) (o : Option Bool),
      (flip bind (TM2.step prog))^[u.length + 1]
        (some ⟨some 0, (false, o, none), mk4 (delimit u ++ rest) s1 [] []⟩) =
      some ⟨some 1, (false, none, none), mk4 rest (u.reverse ++ s1) [] []⟩ := by
    intro u; induction u with
    | nil =>
      intro rest s1 o
      rw [List.length_nil, iter_step]; simp [delimit, prog]
    | cons x u ih =>
      intro rest s1 o
      rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [delimit, prog]); rw [ih rest (x :: s1) (some x)]
      simp
  have h2 : ∀ (s1 s0 s2 : List Bool) (o : Option Bool),
      (flip bind (TM2.step prog))^[s1.length + 1]
        (some ⟨some 1, (false, o, none), mk4 s0 s1 s2 []⟩) =
      some ⟨some 2, (false, none, none), mk4 s0 [] (s1.reverse ++ s2) []⟩ := by
    intro s1; induction s1 with
    | nil =>
      intro s0 s2 o
      rw [List.length_nil, iter_step]; simp [prog]; try rfl
    | cons x s1 ih =>
      intro s0 s2 o
      rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog]); rw [ih s0 (x :: s2) (some x)]
      simp
  have h3 : ∀ (k : ℕ) (xs ys acc : List Bool) (bw : Bool), xs.length + ys.length ≤ k →
      ∃ t ≤ max xs.length ys.length + 1,
      (flip bind (TM2.step prog))^[t]
        (some ⟨some 2, (bw, none, none), mk4 ys acc xs []⟩) =
      some ⟨some (if (subBits bw xs ys).1 then 3 else 4),
        (false, none, none), mk4 [] ((subBits bw xs ys).2.reverse ++ acc) [] []⟩ := by
    intro k; induction k with
    | zero =>
      intro xs ys acc bw hxy
      cases xs <;> cases ys <;> try (simp at hxy)
      refine ⟨1, by simp, ?_⟩
      cases bw <;> (rw [iter_step]; simp [prog]; try simp [subBits])
    | succ k ih =>
      intro xs ys acc bw hxy
      cases xs with
      | nil =>
        cases ys with
        | nil =>
          refine ⟨1, by simp, ?_⟩
          cases bw <;> (rw [iter_step]; simp [prog]; try simp [subBits])
        | cons y ys =>
          have hstep : (flip bind (TM2.step prog))^[1]
              (some ⟨some 2, (bw, none, none), mk4 (y :: ys) acc [] []⟩) =
              some ⟨some 2, (y || bw, none, none), mk4 ys (xor y bw :: acc) [] []⟩ := by
            rw [iter_step]; cases y <;> cases bw <;> simp [prog]
          obtain ⟨t, htle, ht⟩ := ih [] ys (xor y bw :: acc) (y || bw) (by simp at hxy ⊢; omega)
          refine ⟨t + 1, by simp at htle ⊢; omega, ?_⟩
          simpa [subBits] using iter_trans hstep ht
      | cons x xs =>
        cases ys with
        | nil =>
          have hstep : (flip bind (TM2.step prog))^[1]
              (some ⟨some 2, (bw, none, none), mk4 [] acc (x :: xs) []⟩) =
              some ⟨some 2, (!x && bw, none, none), mk4 [] (xor x bw :: acc) xs []⟩ := by
            rw [iter_step]; simp [prog]; try rfl
          obtain ⟨t, htle, ht⟩ := ih xs [] (xor x bw :: acc) (!x && bw) (by simp at hxy ⊢; omega)
          refine ⟨t + 1, by simp at htle ⊢; omega, ?_⟩
          simpa [subBits] using iter_trans hstep ht
        | cons y ys =>
          let nbw := (!x && y) || (!x && bw) || (y && bw)
          have hstep : (flip bind (TM2.step prog))^[1]
              (some ⟨some 2, (bw, none, none), mk4 (y :: ys) acc (x :: xs) []⟩) =
              some ⟨some 2, (nbw, none, none),
                mk4 ys (xor (xor x y) bw :: acc) xs []⟩ := by
            rw [iter_step]; simp [prog]; try rfl
          obtain ⟨t, htle, ht⟩ := ih xs ys (xor (xor x y) bw :: acc) nbw
            (by simp at hxy ⊢; omega)
          refine ⟨t + 1, by simp at htle ⊢; omega, ?_⟩
          simpa [subBits, nbw] using iter_trans hstep ht
  have hdrain3 : ∀ (s1 : List Bool) (o : Option Bool),
      (flip bind (TM2.step prog))^[s1.length + 1]
        (some ⟨some 3, (false, o, none), mk4 [] s1 [] []⟩) =
      some ⟨none, (false, none, none), mk4 [true, false, false] [] [] []⟩ := by
    intro s1; induction s1 with
    | nil =>
      intro o; rw [List.length_nil, iter_step]; simp [prog]
    | cons _ s1 ih =>
      intro o; rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog])
      exact ih _
  have htrim4 : ∀ (s1 : List Bool),
      ∃ t ≤ s1.length + 1,
      (flip bind (TM2.step prog))^[t]
        (some ⟨some 4, (false, none, none), mk4 [] s1 [] []⟩) =
      some ⟨some 5, (false, none, none), mk4 [] (trimLeadFalse s1) [] []⟩ := by
    intro s1; induction s1 with
    | nil =>
      refine ⟨1, le_rfl, ?_⟩
      rw [iter_step]; simp [prog]; try rfl
    | cons b s1 ih =>
      cases b with
      | false =>
        have hs : (flip bind (TM2.step prog))^[1]
            (some ⟨some 4, (false, none, none), mk4 [] (false :: s1) [] []⟩) =
            some ⟨some 4, (false, none, none), mk4 [] s1 [] []⟩ := by
          rw [iter_step]; simp [prog]; try rfl
        obtain ⟨t, htle, ht⟩ := ih
        exact ⟨t + 1, by simp; omega, iter_trans hs ht⟩
      | true =>
        refine ⟨1, by simp, ?_⟩
        rw [iter_step]; simp [prog]; try rfl
  have hrev5 : ∀ (s1 s0 : List Bool) (o : Option Bool),
      (flip bind (TM2.step prog))^[s1.length + 1]
        (some ⟨some 5, (false, o, none), mk4 s0 s1 [] []⟩) =
      some ⟨none, (false, none, none), mk4 (true :: true :: false :: (s1.reverse ++ s0)) [] [] []⟩ := by
    intro s1; induction s1 with
    | nil =>
      intro s0 o; rw [List.length_nil, iter_step]; simp [prog]
    | cons x s1 ih =>
      intro s0 o
      rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog]); rw [ih (x :: s0) (some x)]
      simp
  have hp1 := h1 (bitEncode a) (bitEncode b) [] none
  simp only [List.append_nil] at hp1
  have hp2 := h2 (bitEncode a).reverse (bitEncode b) [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hp2
  obtain ⟨t3, ht3le, hp3⟩ := h3 ((bitEncode a).length + (bitEncode b).length)
    (bitEncode a) (bitEncode b) [] false le_rfl
  simp only [List.append_nil] at hp3
  have ⟨hcmp, hdiff⟩ := subBits_encodeNat (a + b) a b false le_rfl
  simp only [Bool.toNat_false, Nat.add_zero] at hcmp hdiff
  have hsublen := length_subBits_le false (bitEncode a) (bitEncode b)
  by_cases hle : b ≤ a
  · have hbw : (subBits false (bitEncode a) (bitEncode b)).1 = false := by
      change (subBits false (encodeNat a) (encodeNat b)).1 = false
      rw [hcmp]; exact decide_eq_false (by omega)
    rw [hbw, if_neg Bool.false_ne_true] at hp3
    obtain ⟨t4, ht4le, hp4⟩ := htrim4 (subBits false (bitEncode a) (bitEncode b)).2.reverse
    have hp5 := hrev5 (trimLeadFalse (subBits false (bitEncode a) (bitEncode b)).2.reverse) [] none
    simp only [List.append_nil] at hp5
    have hres_enc : bitEncode (decide (b ≤ a), a - b) =
        true :: true :: false ::
          (trimLeadFalse (subBits false (bitEncode a) (bitEncode b)).2.reverse).reverse := by
      rw [decide_eq_true hle]
      change true :: true :: false :: encodeNat (a - b) = _
      rw [← hdiff hle]; rfl
    rw [hres_enc]
    have htlen : (trimLeadFalse (subBits false (bitEncode a) (bitEncode b)).2.reverse).length ≤
        max (bitEncode a).length (bitEncode b).length := by
      have := length_trimLeadFalse_le (subBits false (bitEncode a) (bitEncode b)).2.reverse
      rw [List.length_reverse] at this; omega
    refine ⟨_, ?_, iter_trans (iter_trans (iter_trans (iter_trans hp1 hp2) hp3) hp4) hp5⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]; change _ ≤ 6 * (delimit (bitEncode a) ++ bitEncode b).length + 8
    rw [List.length_reverse] at ht4le; rw [List.length_append, length_delimit]; omega
  · have hbw : (subBits false (bitEncode a) (bitEncode b)).1 = true := by
      change (subBits false (encodeNat a) (encodeNat b)).1 = true
      rw [hcmp]; exact decide_eq_true (by omega)
    rw [hbw, if_pos rfl] at hp3
    have hp4 := hdrain3 (subBits false (bitEncode a) (bitEncode b)).2.reverse none
    have hres_enc : bitEncode (decide (b ≤ a), a - b) = [true, false, false] := by
      rw [decide_eq_false hle, Nat.sub_eq_zero_of_le (by omega)]; rfl
    rw [hres_enc]
    refine ⟨_, ?_, iter_trans (iter_trans (iter_trans hp1 hp2) hp3) hp4⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]; change _ ≤ 6 * (delimit (bitEncode a) ++ bitEncode b).length + 8
    rw [List.length_append, length_delimit, List.length_reverse]; omega

private theorem isPolyTime_natLe : IsPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
  have hswap : IsPolyTime (fun p : ℕ × ℕ => (p.2, p.1)) :=
    isPolyTime_pair isPolyTime_snd isPolyTime_fst
  exact isPolyTime_seq (isPolyTime_seq hswap isPolyTime_natSubCmp) isPolyTime_fst

private theorem isPolyTime_natSub : IsPolyTime (fun p : ℕ × ℕ => p.1 - p.2) :=
  isPolyTime_seq isPolyTime_natSubCmp isPolyTime_snd


private theorem isPolyTime_unaryAdd :
    IsPolyTime (fun p : List Bool × List Bool => p.1 ++ p.2) :=
  isPolyTime_listAppend

private theorem bitEncode_pair_len {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (a : α) (b : β) :
    (bitEncode (a, b)).length = 2 * (bitEncode a).length + 1 + (bitEncode b).length := by
  change (delimit (bitEncode a) ++ bitEncode b).length = _
  rw [List.length_append, length_delimit]

private theorem bitEncode_bool_len (b : Bool) : (bitEncode b).length = 1 := rfl

private theorem lt_two_pow_bitEncode_nat (n : ℕ) : n < 2 ^ (bitEncode n).length :=
  lt_two_pow_length_encodeNat n

private theorem isPolyTime_boolOr : IsPolyTime (fun p : Bool × Bool => p.1 || p.2) := by
  have h : (fun p : Bool × Bool => p.1 || p.2) = fun p => if p.1 then true else p.2 := by
    funext ⟨a, b⟩; cases a <;> rfl
  rw [h]
  exact isPolyTime_ite isPolyTime_fst (isPolyTime_const true) isPolyTime_snd

private theorem isPolyTime_unarySucc : IsPolyTime (fun u : List Bool => false :: u) := by
  simpa [id] using isPolyTime_seq (isPolyTime_pair (isPolyTime_const [false]) isPolyTime_id) isPolyTime_unaryAdd

/- ### Unary Multiplication and Polynomial Unary Evaluation -/

private def unaryMulStep (p : List Bool × List Bool) : List Bool × List Bool :=
  (p.1, p.1 ++ p.2)

private theorem unaryMulStep_iter (k : ℕ) (v acc : List Bool) :
    (unaryMulStep^[k] (v, acc)).1 = v ∧
    (unaryMulStep^[k] (v, acc)).2.length = k * v.length + acc.length := by
  induction k generalizing acc with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    dsimp only [unaryMulStep]
    obtain ⟨h1, h2⟩ := ih (v ++ acc)
    refine ⟨h1, ?_⟩
    rw [h2, List.length_append, Nat.succ_mul]; omega

private theorem unaryMulStep_replicate (k m : ℕ) :
    (unaryMulStep^[k] (List.replicate m false, [])).2 = List.replicate (k * m) false := by
  suffices h : ∀ a, (unaryMulStep^[k] (List.replicate m false, List.replicate a false)).2 =
      List.replicate (k * m + a) false by
    simpa using h 0
  induction k with
  | zero => intro a; simp
  | succ k ih =>
    intro a
    rw [Function.iterate_succ_apply]
    show (unaryMulStep^[k] (List.replicate m false, List.replicate m false ++ List.replicate a false)).2 = _
    rw [← List.replicate_add, ih (m + a)]
    congr 1; rw [Nat.succ_mul]; omega

private theorem isPolyTime_uRepeat :
    IsPolyTime (fun p : List Bool × List Bool => (unaryMulStep^[p.1.length] (p.2, [])).2) := by
  have hstep : IsPolyTime unaryMulStep :=
    isPolyTime_pair isPolyTime_fst isPolyTime_unaryAdd
  have hiter : IsPolyTime (fun q : List Bool × (List Bool × List Bool) =>
      unaryMulStep^[q.1.length] q.2) := by
    refine isPolyTime_iter unaryMulStep hstep (3 * Polynomial.X * Polynomial.X + 4 * Polynomial.X + 4)
      (fun u ⟨v, acc⟩ k hk => ?_)
    obtain ⟨h1, h2⟩ := unaryMulStep_iter k v acc
    rw [bitEncode_pair_len, h1, bitEncode_listBool_length, bitEncode_listBool_length, h2]
    set L := (bitEncode (u, (v, acc))).length
    have hL : L = 2 * (3 * u.length) + 1 + (2 * (3 * v.length) + 1 + 3 * acc.length) := by
      dsimp only [L]
      rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_listBool_length,
        bitEncode_listBool_length, bitEncode_listBool_length]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    have hkv : k * v.length ≤ L * L := Nat.mul_le_mul (by omega) (by omega)
    have h3L : 3 * L * L = 3 * (L * L) := by ring
    omega
  exact isPolyTime_seq
    (isPolyTime_seq (isPolyTime_pair isPolyTime_fst (isPolyTime_pair isPolyTime_snd (isPolyTime_const [])))
      hiter)
    isPolyTime_snd


private def natDouble (n : ℕ) : ℕ := 2 * n

private theorem isPolyTime_natDouble : IsPolyTime natDouble := by
  have h : natDouble = fun n => 2 * n + if false then 1 else 0 := by funext n; rfl
  rw [h]
  simpa [id] using isPolyTime_seq (isPolyTime_pair isPolyTime_id (isPolyTime_const false)) isPolyTime_natMul2Add

private theorem natDouble_iter (k n : ℕ) : natDouble^[k] n = n * 2 ^ k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, natDouble, pow_succ]; ring

private theorem isPolyTime_shiftLeft :
    IsPolyTime (fun p : List Bool × ℕ => p.2 * 2 ^ p.1.length) := by
  have hfn : (fun p : List Bool × ℕ => p.2 * 2 ^ p.1.length) =
      fun p : List Bool × ℕ => natDouble^[p.1.length] p.2 := by
    funext ⟨u, n⟩; exact (natDouble_iter u.length n).symm
  rw [hfn]
  refine isPolyTime_iter natDouble isPolyTime_natDouble (2 * Polynomial.X + 2) (fun u n k hk => ?_)
  rw [natDouble_iter]
  have hlt : n * 2 ^ k < 2 ^ ((bitEncode n).length + k) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right (lt_two_pow_length_encodeNat n) (by positivity)
  have hlen : (bitEncode (n * 2 ^ k)).length ≤ (bitEncode n).length + k :=
    length_encodeNat_le hlt
  have hL : (bitEncode (u, n)).length = 2 * (3 * u.length) + 1 + (bitEncode n).length := by
    rw [bitEncode_pair_len, bitEncode_listBool_length]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

private theorem isPolyTime_pow2 : IsPolyTime (fun u : List Bool => 2 ^ u.length) := by
  have h : (fun u : List Bool => 2 ^ u.length) = fun u => 1 * 2 ^ u.length := by
    funext u; simp
  rw [h]
  simpa [id] using isPolyTime_seq (isPolyTime_pair isPolyTime_id (isPolyTime_const 1)) isPolyTime_shiftLeft

/- ### Binary Multiplication (`natMul`) -/

private def mulStep (s : ℕ × (ℕ × ℕ)) : ℕ × (ℕ × ℕ) :=
  (s.1 / 2, 2 * s.2.1, if decide (s.1 % 2 = 1) then s.2.2 + s.2.1 else s.2.2)

private theorem mulStep_iter (k a b acc : ℕ) :
    (mulStep^[k] (a, (b, acc))).1 = a / 2 ^ k ∧
    (mulStep^[k] (a, (b, acc))).2.1 = b * 2 ^ k ∧
    (mulStep^[k] (a, (b, acc))).2.2 + (a / 2 ^ k) * (b * 2 ^ k) = acc + a * b := by
  induction k generalizing a b acc with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    let acc' := if decide (a % 2 = 1) then acc + b else acc
    have hstep : mulStep (a, (b, acc)) = (a / 2, (2 * b, acc')) := rfl
    rw [hstep]
    obtain ⟨h1, h2, h3⟩ := ih (a / 2) (2 * b) acc'
    have hdiv : a / 2 / 2 ^ k = a / 2 ^ (k + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ']
    have hmul : 2 * b * 2 ^ k = b * 2 ^ (k + 1) := by rw [pow_succ]; ring
    refine ⟨by rw [h1, hdiv], by rw [h2, hmul], ?_⟩
    rw [← hdiv, ← hmul, h3]
    rcases Nat.mod_two_eq_zero_or_one a with hm | hm
    · have ha : a = 2 * (a / 2) := by omega
      have hdec : decide (a % 2 = 1) = false := by rw [hm]; rfl
      simp only [acc', hdec, Bool.false_eq_true, ↓reduceIte]
      conv_rhs => rw [ha]
      ring
    · have ha : a = 2 * (a / 2) + 1 := by omega
      have hdec : decide (a % 2 = 1) = true := by rw [hm]; rfl
      simp only [acc', hdec, ↓reduceIte]
      conv_rhs => rw [ha]
      ring

private theorem isPolyTime_natMul : IsPolyTime (fun p : ℕ × ℕ => p.1 * p.2) := by
  have hstep : IsPolyTime mulStep := by
    have ha : IsPolyTime (fun s : ℕ × (ℕ × ℕ) => s.1 / 2) :=
      isPolyTime_seq isPolyTime_fst isPolyTime_natDiv2
    have hb : IsPolyTime (fun s : ℕ × (ℕ × ℕ) => 2 * s.2.1) :=
      isPolyTime_seq (isPolyTime_seq isPolyTime_snd isPolyTime_fst) isPolyTime_natDouble
    have hc : IsPolyTime (fun s : ℕ × (ℕ × ℕ) => decide (s.1 % 2 = 1)) :=
      isPolyTime_seq isPolyTime_fst isPolyTime_natLsb
    have hadd : IsPolyTime (fun s : ℕ × (ℕ × ℕ) => s.2.2 + s.2.1) :=
      isPolyTime_seq (isPolyTime_pair (isPolyTime_seq isPolyTime_snd isPolyTime_snd)
        (isPolyTime_seq isPolyTime_snd isPolyTime_fst)) isPolyTime_natAdd
    have hacc : IsPolyTime (fun s : ℕ × (ℕ × ℕ) =>
        if decide (s.1 % 2 = 1) then s.2.2 + s.2.1 else s.2.2) :=
      isPolyTime_ite hc hadd (isPolyTime_seq isPolyTime_snd isPolyTime_snd)
    exact isPolyTime_pair ha (isPolyTime_pair hb hacc)
  have hiter : IsPolyTime (fun q : List Bool × (ℕ × (ℕ × ℕ)) => mulStep^[q.1.length] q.2) := by
    refine isPolyTime_iter mulStep hstep (10 * Polynomial.X + 10) (fun u ⟨a, b, acc⟩ k hk => ?_)
    obtain ⟨h1, h2, h3⟩ := mulStep_iter k a b acc
    set st := mulStep^[k] (a, (b, acc))
    have ha_le : (bitEncode st.1).length ≤ (bitEncode a).length := by
      rw [h1]
      exact length_encodeNat_le (lt_of_le_of_lt (Nat.div_le_self a _) (lt_two_pow_length_encodeNat a))
    have hb_le : (bitEncode st.2.1).length ≤ (bitEncode b).length + k := by
      rw [h2]
      exact length_encodeNat_le (by
        rw [pow_add]; exact Nat.mul_lt_mul_of_pos_right (lt_two_pow_length_encodeNat b) (by positivity))
    have hacc_le : (bitEncode st.2.2).length ≤
        (bitEncode acc).length + (bitEncode a).length + (bitEncode b).length + 1 := by
      have hlt_ab : a * b < 2 ^ ((bitEncode a).length + (bitEncode b).length) := by
        rw [pow_add]
        exact Nat.mul_lt_mul'' (lt_two_pow_length_encodeNat a) (lt_two_pow_length_encodeNat b)
      have hlt_acc : acc < 2 ^ (bitEncode acc).length := lt_two_pow_length_encodeNat acc
      have hlt_sum : st.2.2 < 2 ^ ((bitEncode acc).length + (bitEncode a).length + (bitEncode b).length + 1) := by
        have hsum_le : st.2.2 ≤ acc + a * b := by omega
        have hp1 : 2 ^ (bitEncode acc).length ≤
            2 ^ ((bitEncode acc).length + (bitEncode a).length + (bitEncode b).length) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hp2 : 2 ^ ((bitEncode a).length + (bitEncode b).length) ≤
            2 ^ ((bitEncode acc).length + (bitEncode a).length + (bitEncode b).length) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        rw [pow_succ]; omega
      exact length_encodeNat_le hlt_sum
    have hL : (bitEncode (u, (a, (b, acc)))).length =
        2 * (3 * u.length) + 1 + (2 * (bitEncode a).length + 1 +
          (2 * (bitEncode b).length + 1 + (bitEncode acc).length)) := by
      rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len, bitEncode_listBool_length]
    have hst_len : (bitEncode st).length =
        2 * (bitEncode st.1).length + 1 + (2 * (bitEncode st.2.1).length + 1 + (bitEncode st.2.2).length) := by
      rw [bitEncode_pair_len, bitEncode_pair_len]
    change (bitEncode st).length ≤ _
    rw [hst_len]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  have hfn : (fun p : ℕ × ℕ => p.1 * p.2) =
      fun p => (mulStep^[(List.replicate (bitEncode p.1).length false).length] (p.1, (p.2, 0))).2.2 := by
    funext ⟨a, b⟩
    rw [List.length_replicate]
    obtain ⟨_, _, h3⟩ := mulStep_iter (bitEncode a).length a b 0
    rw [Nat.div_eq_of_lt (lt_two_pow_bitEncode_nat a)] at h3
    dsimp only; omega
  rw [hfn]
  have hprep : IsPolyTime (fun p : ℕ × ℕ =>
      (List.replicate (bitEncode p.1).length false, (p.1, (p.2, 0)))) :=
    isPolyTime_pair (isPolyTime_seq isPolyTime_fst isPolyTime_unaryLen)
      (isPolyTime_pair isPolyTime_fst (isPolyTime_pair isPolyTime_snd (isPolyTime_const 0)))
  simpa using isPolyTime_seq (isPolyTime_seq hprep hiter) (isPolyTime_seq isPolyTime_snd isPolyTime_snd)

/- ### Binary Restoring Shift-Subtract Division (`natDivMod`) -/

private def divStep (s : ℕ × (ℕ × ℕ)) : ℕ × (ℕ × ℕ) :=
  if decide (s.2.2 ≤ s.1) then
    (s.1 - s.2.2, (2 * s.2.1 + 1, s.2.2 / 2))
  else
    (s.1, (2 * s.2.1, s.2.2 / 2))

private theorem divStep_bound (k rem quot cur : ℕ) :
    (divStep^[k] (rem, (quot, cur))).1 ≤ rem ∧
    (divStep^[k] (rem, (quot, cur))).2.2 ≤ cur ∧
    (bitEncode (divStep^[k] (rem, (quot, cur))).2.1).length ≤ (bitEncode quot).length + k := by
  induction k generalizing rem quot cur with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    by_cases hle : cur ≤ rem
    · have hst : divStep (rem, (quot, cur)) = (rem - cur, (2 * quot + 1, cur / 2)) := by
        simp [divStep, hle]
      rw [hst]
      obtain ⟨h1, h2, h3⟩ := ih (rem - cur) (2 * quot + 1) (cur / 2)
      have hqlen : (bitEncode (2 * quot + 1)).length ≤ (bitEncode quot).length + 1 := by
        change (encodeNat (2 * quot + 1)).length ≤ (encodeNat quot).length + 1
        rw [encodeNat_bit1, List.length_cons]
      refine ⟨by omega, le_trans h2 (Nat.div_le_self cur 2), by omega⟩
    · have hst : divStep (rem, (quot, cur)) = (rem, (2 * quot, cur / 2)) := by
        simp [divStep, hle]
      rw [hst]
      obtain ⟨h1, h2, h3⟩ := ih rem (2 * quot) (cur / 2)
      have hqlen : (bitEncode (2 * quot)).length ≤ (bitEncode quot).length + 1 := by
        by_cases hq : quot = 0
        · subst hq; simp [bitEncode_nat_eq, encodeNat_zero]
        · change (encodeNat (2 * quot)).length ≤ (encodeNat quot).length + 1
          rw [encodeNat_bit0 hq, List.length_cons]
      refine ⟨h1, le_trans h2 (Nat.div_le_self cur 2), by omega⟩

private theorem divStep_inv (a b n : ℕ) (hb : 0 < b) (ha : a < 2 ^ n) :
    ∀ k ≤ n + 1,
      let st := divStep^[k] (a, (0, b * 2 ^ n))
      a = st.2.1 * (b * 2 ^ (n + 1 - k)) + st.1 ∧
      st.1 < b * 2 ^ (n + 1 - k) ∧
      (k ≤ n → st.2.2 = b * 2 ^ (n - k)) := by
  intro k
  induction k with
  | zero =>
    intro _
    dsimp only
    simp only [Function.iterate_zero, id_eq, Nat.sub_zero, zero_mul, zero_add, true_and]
    have h1 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    have h2 : 2 ^ (n + 1) ≤ b * 2 ^ (n + 1) := Nat.le_mul_of_pos_left _ hb
    exact ⟨by omega, fun _ => trivial⟩
  | succ k ih =>
    intro hk
    obtain ⟨heq, hlt, hcur⟩ := ih (by omega)
    have hkn : k ≤ n := by omega
    have hc : (divStep^[k] (a, (0, b * 2 ^ n))).2.2 = b * 2 ^ (n - k) := hcur hkn
    set st := divStep^[k] (a, (0, b * 2 ^ n))
    have hpow_split : b * 2 ^ (n + 1 - k) = 2 * (b * 2 ^ (n - k)) := by
      have hexp : n + 1 - k = (n - k) + 1 := by omega
      rw [hexp, pow_succ]; ring
    have hnext_exp : n + 1 - (k + 1) = n - k := by omega
    have hdiv2 : (b * 2 ^ (n - k)) / 2 = if k + 1 ≤ n then b * 2 ^ (n - (k + 1)) else b / 2 := by
      split_ifs with hle
      · have hexp : n - k = (n - (k + 1)) + 1 := by omega
        rw [hexp, pow_succ, show b * (2 ^ (n - (k + 1)) * 2) = (b * 2 ^ (n - (k + 1))) * 2 by ring,
          Nat.mul_div_cancel _ (by omega)]
      · have heq0 : n - k = 0 := by omega
        rw [heq0, pow_zero, mul_one]
    rw [Function.iterate_succ_apply']
    change let st' := divStep st; _
    by_cases hcmp : st.2.2 ≤ st.1
    · have hst' : divStep st = (st.1 - st.2.2, (2 * st.2.1 + 1, st.2.2 / 2)) := by
        simp [divStep, hcmp]
      dsimp only
      rw [hc] at hcmp
      rw [hst', hnext_exp, hc]
      refine ⟨?_, ?_, fun hle => by rw [hdiv2, if_pos hle]⟩
      · rw [heq, hpow_split]
        have : st.1 = (st.1 - b * 2 ^ (n - k)) + b * 2 ^ (n - k) := by omega
        linarith
      · rw [hpow_split] at hlt; omega
    · have hst' : divStep st = (st.1, (2 * st.2.1, st.2.2 / 2)) := by
        simp [divStep, hcmp]
      dsimp only
      rw [hc] at hcmp
      rw [hst', hnext_exp, hc]
      refine ⟨?_, by omega, fun hle => by rw [hdiv2, if_pos hle]⟩
      · rw [heq, hpow_split]; ring

private def natDivMod (p : ℕ × ℕ) : ℕ × ℕ :=
  if decide (p.2 = 0) then (0, p.1) else (p.1 / p.2, p.1 % p.2)

private theorem isPolyTime_natDivMod : IsPolyTime natDivMod := by
  have hstep : IsPolyTime divStep := by
    have hcmp : IsPolyTime (fun s : ℕ × (ℕ × ℕ) => decide (s.2.2 ≤ s.1)) :=
      isPolyTime_seq (isPolyTime_pair (isPolyTime_seq isPolyTime_snd isPolyTime_snd) isPolyTime_fst)
        isPolyTime_natLe
    have hrem1 : IsPolyTime (fun s : ℕ × (ℕ × ℕ) => s.1 - s.2.2) :=
      isPolyTime_seq (isPolyTime_pair isPolyTime_fst (isPolyTime_seq isPolyTime_snd isPolyTime_snd))
        isPolyTime_natSub
    have hq1 : IsPolyTime (fun s : ℕ × (ℕ × ℕ) => 2 * s.2.1 + 1) := by
      have h : (fun s : ℕ × (ℕ × ℕ) => 2 * s.2.1 + 1) =
          fun s => 2 * s.2.1 + if true then 1 else 0 := rfl
      rw [h]
      simpa using isPolyTime_seq
        (isPolyTime_pair (isPolyTime_seq isPolyTime_snd isPolyTime_fst) (isPolyTime_const true))
        isPolyTime_natMul2Add
    have hq0 : IsPolyTime (fun s : ℕ × (ℕ × ℕ) => 2 * s.2.1) :=
      isPolyTime_seq (isPolyTime_seq isPolyTime_snd isPolyTime_fst) isPolyTime_natDouble
    have hc2 : IsPolyTime (fun s : ℕ × (ℕ × ℕ) => s.2.2 / 2) :=
      isPolyTime_seq (isPolyTime_seq isPolyTime_snd isPolyTime_snd) isPolyTime_natDiv2
    exact isPolyTime_ite hcmp
      (isPolyTime_pair hrem1 (isPolyTime_pair hq1 hc2))
      (isPolyTime_pair isPolyTime_fst (isPolyTime_pair hq0 hc2))
  have hiter : IsPolyTime (fun q : List Bool × (ℕ × (ℕ × ℕ)) => divStep^[q.1.length] q.2) := by
    refine isPolyTime_iter divStep hstep (6 * Polynomial.X + 8) (fun u ⟨rem, quot, cur⟩ k hk => ?_)
    obtain ⟨h1, h2, h3⟩ := divStep_bound k rem quot cur
    set st := divStep^[k] (rem, (quot, cur))
    have hrem_len : (bitEncode st.1).length ≤ (bitEncode rem).length :=
      length_encodeNat_le (lt_of_le_of_lt h1 (lt_two_pow_length_encodeNat rem))
    have hcur_len : (bitEncode st.2.2).length ≤ (bitEncode cur).length :=
      length_encodeNat_le (lt_of_le_of_lt h2 (lt_two_pow_length_encodeNat cur))
    have hL : (bitEncode (u, (rem, (quot, cur)))).length =
        2 * (3 * u.length) + 1 + (2 * (bitEncode rem).length + 1 +
          (2 * (bitEncode quot).length + 1 + (bitEncode cur).length)) := by
      rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len, bitEncode_listBool_length]
    have hst_len : (bitEncode st).length =
        2 * (bitEncode st.1).length + 1 + (2 * (bitEncode st.2.1).length + 1 + (bitEncode st.2.2).length) := by
      rw [bitEncode_pair_len, bitEncode_pair_len]
    change (bitEncode st).length ≤ _
    rw [hst_len]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  let runDiv : ℕ × ℕ → ℕ × ℕ := fun p =>
    let u := List.replicate (bitEncode p.1).length false
    let st := divStep^[(false :: u).length] (p.1, (0, p.2 * 2 ^ u.length))
    (st.2.1, st.1)
  have hrunDiv : IsPolyTime runDiv := by
    have hu : IsPolyTime (fun p : ℕ × ℕ => List.replicate (bitEncode p.1).length false) :=
      isPolyTime_seq isPolyTime_fst isPolyTime_unaryLen
    have hcnt : IsPolyTime (fun p : ℕ × ℕ => false :: List.replicate (bitEncode p.1).length false) :=
      isPolyTime_seq hu isPolyTime_unarySucc
    have hcur : IsPolyTime (fun p : ℕ × ℕ => p.2 * 2 ^ (List.replicate (bitEncode p.1).length false).length) :=
      isPolyTime_seq (isPolyTime_pair hu isPolyTime_snd) isPolyTime_shiftLeft
    have hinit : IsPolyTime (fun p : ℕ × ℕ =>
        (false :: List.replicate (bitEncode p.1).length false,
          (p.1, (0, p.2 * 2 ^ (List.replicate (bitEncode p.1).length false).length)))) :=
      isPolyTime_pair hcnt (isPolyTime_pair isPolyTime_fst (isPolyTime_pair (isPolyTime_const 0) hcur))
    exact isPolyTime_seq (isPolyTime_seq hinit hiter)
      (isPolyTime_pair (isPolyTime_seq isPolyTime_snd isPolyTime_fst) isPolyTime_fst)
  have heq : natDivMod = fun p => if decide (p.2 = 0) then (0, p.1) else runDiv p := by
    funext ⟨a, b⟩
    by_cases hb : b = 0
    · simp [natDivMod, hb]
    · simp only [natDivMod, hb, decide_false, Bool.false_eq_true, ↓reduceIte]
      dsimp only [runDiv]
      rw [List.length_cons, List.length_replicate]
      obtain ⟨heq_a, hlt_r, _⟩ := divStep_inv a b (bitEncode a).length (Nat.pos_of_ne_zero hb)
        (lt_two_pow_length_encodeNat a) ((bitEncode a).length + 1) le_rfl
      simp only [Nat.sub_self, pow_zero, mul_one] at heq_a hlt_r
      have hdiv_eq : a / b = (divStep^[(bitEncode a).length + 1] (a, (0, b * 2 ^ (bitEncode a).length))).2.1 := by
        conv_lhs => rw [heq_a]
        rw [mul_comm _ b, Nat.mul_add_div (Nat.pos_of_ne_zero hb), Nat.div_eq_of_lt hlt_r, add_zero]
      have hmod_eq : a % b = (divStep^[(bitEncode a).length + 1] (a, (0, b * 2 ^ (bitEncode a).length))).1 := by
        conv_lhs => rw [heq_a]
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hlt_r]
      exact Prod.ext hdiv_eq hmod_eq
  rw [heq]
  exact isPolyTime_ite (isPolyTime_seq isPolyTime_snd isPolyTime_natIsZero)
    (isPolyTime_pair (isPolyTime_const 0) isPolyTime_fst) hrunDiv



/- ## Section 4: Generic List Combinators & Exact LP Feasibility Checker -/

private theorem isPolyTime_output_bound {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {f : α → β} (hf : IsPolyTime f) :
    ∃ P : Polynomial ℕ, ∀ x : α, (bitEncode (f x)).length ≤ P.eval (bitEncode x).length := by
  obtain ⟨Tf⟩ := hf
  obtain ⟨B, hB⟩ : ∃ B, ∀ l, pushes (Tf.tm.m l) ≤ B := by
    let _ := Tf.tm.ΛFin
    exact ⟨∑ l, pushes (Tf.tm.m l), fun l =>
      Finset.single_le_sum (f := fun l => pushes (Tf.tm.m l)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ l)⟩
  refine ⟨Polynomial.X + (B : Polynomial ℕ) * Tf.time, fun x => ?_⟩
  obtain ⟨⟨t, ht⟩, htle⟩ := Tf.outputsFun x
  have h1 : (bitEncode (f x)).length ≤
      ((initList Tf.tm ((bitEncode x).map Tf.inputAlphabet.symm)).stk Tf.tm.k₁).length + B * t := by
    have hrun := len_run Tf.tm.m B hB Tf.tm.k₁ t _ _ ht
    rw [halt_k1, List.length_map] at hrun
    exact hrun
  have h2 : ((initList Tf.tm ((bitEncode x).map Tf.inputAlphabet.symm)).stk Tf.tm.k₁).length ≤
      (bitEncode x).length := by
    have hi := init_len Tf.tm ((bitEncode x).map Tf.inputAlphabet.symm) Tf.tm.k₁
    rwa [List.length_map] at hi
  have htle' : t ≤ Tf.time.eval (bitEncode x).length := htle
  have hBt : B * t ≤ B * Tf.time.eval (bitEncode x).length := Nat.mul_le_mul_left B htle'
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_natCast, Nat.cast_id]
  omega

private theorem isPolyTime_ofSameEncode {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) (hf : ∀ x, bitEncode (f x) = bitEncode x) : IsPolyTime f := by
  let prog : Unit → TM2.Stmt (fun _ : Stk4 => Bool) Unit Unit := fun _ => .halt
  refine mkBoolPolyTime f () () prog 1 (fun x => ⟨1, by simp, ?_⟩)
  rw [iter_step, hf]; rfl

private theorem isPolyTime_boolAnd : IsPolyTime (fun p : Bool × Bool => p.1 && p.2) := by
  have h : (fun p : Bool × Bool => p.1 && p.2) = fun p => if p.1 then p.2 else false := by
    funext ⟨a, b⟩; cases a <;> rfl
  rw [h]
  exact isPolyTime_ite isPolyTime_fst isPolyTime_snd (isPolyTime_const false)

private theorem isPolyTime_boolNot : IsPolyTime (fun b : Bool => !b) := by
  have h : (fun b : Bool => !b) = fun b => if b then false else true := by
    funext b; cases b <;> rfl
  rw [h]
  exact isPolyTime_ite isPolyTime_id (isPolyTime_const false) (isPolyTime_const true)

private theorem isPolyTime_natEq : IsPolyTime (fun p : ℕ × ℕ => decide (p.1 = p.2)) := by
  have h : (fun p : ℕ × ℕ => decide (p.1 = p.2)) =
      fun p => decide (p.1 ≤ p.2) && decide (p.2 ≤ p.1) := by
    funext ⟨a, b⟩; by_cases h1 : a ≤ b <;> by_cases h2 : b ≤ a <;> simp_all <;> omega
  rw [h]
  exact isPolyTime_seq
    (isPolyTime_pair isPolyTime_natLe
      (isPolyTime_seq (isPolyTime_pair isPolyTime_snd isPolyTime_fst) isPolyTime_natLe))
    isPolyTime_boolAnd

private theorem isPolyTime_natLt : IsPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  have h : (fun p : ℕ × ℕ => decide (p.1 < p.2)) = fun p => !decide (p.2 ≤ p.1) := by
    funext ⟨a, b⟩; by_cases h1 : b ≤ a
    · simp [h1]
    · simp [h1]; omega
  rw [h]
  exact isPolyTime_seq
    (isPolyTime_seq (isPolyTime_pair isPolyTime_snd isPolyTime_fst) isPolyTime_natLe)
    isPolyTime_boolNot

private theorem isPolyTime_natMin : IsPolyTime (fun p : ℕ × ℕ => min p.1 p.2) := by
  have h : (fun p : ℕ × ℕ => min p.1 p.2) = fun p => if decide (p.1 ≤ p.2) then p.1 else p.2 := by
    funext ⟨a, b⟩; by_cases h1 : a ≤ b
    · simp [h1]
    · simp [h1]; omega
  rw [h]
  exact isPolyTime_ite isPolyTime_natLe isPolyTime_fst isPolyTime_snd

private theorem isPolyTime_natDiv : IsPolyTime (fun p : ℕ × ℕ => p.1 / p.2) := by
  have h : (fun p : ℕ × ℕ => p.1 / p.2) = fun p => (natDivMod p).1 := by
    funext ⟨a, b⟩; by_cases hb : b = 0 <;> simp [natDivMod, hb]
  rw [h]
  exact isPolyTime_seq isPolyTime_natDivMod isPolyTime_fst

/- ### Ergonomic `IsPolyTime` Combinators -/

private theorem pt_fst {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] {f : α → β × γ} (hf : IsPolyTime f) :
    IsPolyTime (fun x => (f x).1) := isPolyTime_seq hf isPolyTime_fst

private theorem pt_snd {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] {f : α → β × γ} (hf : IsPolyTime f) :
    IsPolyTime (fun x => (f x).2) := isPolyTime_seq hf isPolyTime_snd

private theorem pt_add {α : Type} [BitstringEncoding α] {f g : α → ℕ}
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (fun x => f x + g x) :=
  isPolyTime_seq (isPolyTime_pair hf hg) isPolyTime_natAdd

private theorem pt_sub {α : Type} [BitstringEncoding α] {f g : α → ℕ}
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (fun x => f x - g x) :=
  isPolyTime_seq (isPolyTime_pair hf hg) isPolyTime_natSub

private theorem pt_mul {α : Type} [BitstringEncoding α] {f g : α → ℕ}
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (fun x => f x * g x) :=
  isPolyTime_seq (isPolyTime_pair hf hg) isPolyTime_natMul

private theorem pt_div {α : Type} [BitstringEncoding α] {f g : α → ℕ}
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (fun x => f x / g x) :=
  isPolyTime_seq (isPolyTime_pair hf hg) isPolyTime_natDiv

private theorem pt_min {α : Type} [BitstringEncoding α] {f g : α → ℕ}
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (fun x => min (f x) (g x)) :=
  isPolyTime_seq (isPolyTime_pair hf hg) isPolyTime_natMin

private theorem pt_le {α : Type} [BitstringEncoding α] {f g : α → ℕ}
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (fun x => decide (f x ≤ g x)) :=
  isPolyTime_seq (isPolyTime_pair hf hg) isPolyTime_natLe

private theorem pt_lt {α : Type} [BitstringEncoding α] {f g : α → ℕ}
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (fun x => decide (f x < g x)) :=
  isPolyTime_seq (isPolyTime_pair hf hg) isPolyTime_natLt

private theorem pt_eq {α : Type} [BitstringEncoding α] {f g : α → ℕ}
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (fun x => decide (f x = g x)) :=
  isPolyTime_seq (isPolyTime_pair hf hg) isPolyTime_natEq

private theorem pt_and {α : Type} [BitstringEncoding α] {f g : α → Bool}
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (fun x => f x && g x) :=
  isPolyTime_seq (isPolyTime_pair hf hg) isPolyTime_boolAnd

private theorem pt_or {α : Type} [BitstringEncoding α] {f g : α → Bool}
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (fun x => f x || g x) :=
  isPolyTime_seq (isPolyTime_pair hf hg) isPolyTime_boolOr

private theorem pt_not {α : Type} [BitstringEncoding α] {f : α → Bool}
    (hf : IsPolyTime f) : IsPolyTime (fun x => !f x) :=
  isPolyTime_seq hf isPolyTime_boolNot

/- ### Generic List Encoding & Primitives -/

private theorem bitEncode_list_nil {α : Type} [BitstringEncoding α] :
    bitEncode ([] : List α) = [] := rfl

private theorem bitEncode_list_cons {α : Type} [BitstringEncoding α] (a : α) (l : List α) :
    bitEncode (a :: l) = delimit (bitEncode a) ++ bitEncode l := rfl

private theorem bitEncode_list_cons_len {α : Type} [BitstringEncoding α] (a : α) (l : List α) :
    (bitEncode (a :: l)).length = 2 * (bitEncode a).length + 1 + (bitEncode l).length := by
  rw [bitEncode_list_cons, List.length_append, length_delimit]

private theorem bitEncode_list_append_len {α : Type} [BitstringEncoding α] (u v : List α) :
    (bitEncode (u ++ v)).length = (bitEncode u).length + (bitEncode v).length := by
  rw [bitEncode_list_append, List.length_append]

private theorem bitEncode_list_reverse_len {α : Type} [BitstringEncoding α] (l : List α) :
    (bitEncode l.reverse).length = (bitEncode l).length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.reverse_cons, bitEncode_list_append_len, ih, bitEncode_list_cons_len,
      bitEncode_list_cons_len, bitEncode_list_nil, List.length_nil]
    omega

private theorem list_len_le_bitEncode {α : Type} [BitstringEncoding α] (l : List α) :
    l.length ≤ (bitEncode l).length := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.length_cons, bitEncode_list_cons_len]; omega

private theorem bitEncode_mem_le {α : Type} [BitstringEncoding α] {a : α} {l : List α}
    (h : a ∈ l) : (bitEncode a).length ≤ (bitEncode l).length := by
  induction l with
  | nil => cases h
  | cons x t ih =>
    rw [bitEncode_list_cons_len]
    rcases List.mem_cons.mp h with rfl | ht
    · omega
    · have := ih ht; omega

private theorem isPolyTime_listCons {α : Type} [BitstringEncoding α] :
    IsPolyTime (fun p : α × List α => p.1 :: p.2) :=
  isPolyTime_ofSameEncode _ (fun _ => rfl)

private theorem pt_cons {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {f : α → β} {g : α → List β} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => f x :: g x) :=
  isPolyTime_seq (isPolyTime_pair hf hg) isPolyTime_listCons

private theorem pt_append {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {f g : α → List β} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => f x ++ g x) :=
  isPolyTime_seq (isPolyTime_pair hf hg) isPolyTime_listAppend

private def listUncons {α : Type} (d : α) : List α → Bool × (α × List α)
  | [] => (false, (d, []))
  | a :: t => (true, (a, t))

private theorem isPolyTime_listUncons {α : Type} [BitstringEncoding α] (d : α) :
    IsPolyTime (listUncons d) := by
  let prog : Unit → TM2.Stmt (fun _ : Stk4 => Bool) Unit (Option Bool) := fun _ =>
    .peek Stk4.s0 (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push Stk4.s0 (fun _ => false) <|
          .push Stk4.s0 (fun _ => true) <|
          .push Stk4.s0 (fun _ => true) <|
          .load (fun _ => none) .halt)
        (pushListStmt (bitEncode (false, (d, ([] : List α)))).reverse
          (.load (fun _ => none) .halt))
  refine mkBoolPolyTime (listUncons d) () none prog 1 (fun l => ?_)
  refine ⟨1, by simp, ?_⟩
  cases l with
  | nil =>
    rw [iter_step]
    change some (TM2.stepAux (prog ()) none (mk4 [] [] [] [])) = _
    simp [prog, listUncons, stepAux_pushListStmt]
  | cons a t =>
    have hne : bitEncode (a :: t) ≠ [] := by
      rw [bitEncode_list_cons]
      cases bitEncode a <;> simp [delimit]
    cases henc : bitEncode (a :: t) with
    | nil => exact absurd henc hne
    | cons b bs =>
      have hout : bitEncode (listUncons d (a :: t)) = true :: true :: false :: b :: bs := by
        change true :: true :: false :: (delimit (bitEncode a) ++ bitEncode t) = _
        exact congrArg (fun r => true :: true :: false :: r) henc
      rw [hout, iter_step]
      simp [prog]

private theorem isPolyTime_listTail {α : Type} [BitstringEncoding α] (d : α) :
    IsPolyTime (fun l : List α => l.tail) := by
  have h : (fun l : List α => l.tail) = fun l => (listUncons d l).2.2 := by
    funext l; cases l <;> rfl
  rw [h]
  exact pt_snd (pt_snd (isPolyTime_listUncons d))

/- ### Derived List Combinators: `listRev`, `listToUnary`, `listLen`, `listReplicate`, `listMap`, `zipMapD` -/

private def revStep {α : Type} (d : α) (p : List α × List α) : List α × List α :=
  let u := listUncons d p.1
  if u.1 then (u.2.2, u.2.1 :: p.2) else p

private theorem revStep_len_eq {α : Type} [BitstringEncoding α] (d : α) (k : ℕ) (xs acc : List α) :
    (bitEncode ((revStep d)^[k] (xs, acc)).1).length +
      (bitEncode ((revStep d)^[k] (xs, acc)).2).length =
      (bitEncode xs).length + (bitEncode acc).length := by
  induction k generalizing xs acc with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil => simpa [revStep, listUncons] using ih [] acc
    | cons a t =>
      simp only [revStep, listUncons, ↓reduceIte]
      rw [ih t (a :: acc), bitEncode_list_cons_len, bitEncode_list_cons_len]; omega

private theorem revStep_eq {α : Type} (d : α) : ∀ (k : ℕ) (xs acc : List α),
    xs.length ≤ k → ((revStep d)^[k] (xs, acc)).2 = xs.reverse ++ acc
  | k, [], acc, _ => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply]
      simpa [revStep, listUncons] using ih
  | 0, _ :: _, _, h => by simp at h
  | k + 1, a :: t, acc, h => by
    rw [Function.iterate_succ_apply]
    simp only [revStep, listUncons, ↓reduceIte]
    rw [revStep_eq d k t (a :: acc) (by simp at h; omega), List.reverse_cons, List.append_assoc]
    rfl

private theorem isPolyTime_listRev {α : Type} [BitstringEncoding α] (d : α) :
    IsPolyTime (fun l : List α => l.reverse) := by
  have hstep : IsPolyTime (revStep d) := by
    have hu : IsPolyTime (fun p : List α × List α => listUncons d p.1) :=
      isPolyTime_seq isPolyTime_fst (isPolyTime_listUncons d)
    exact isPolyTime_ite (pt_fst hu)
      (isPolyTime_pair (pt_snd (pt_snd hu)) (pt_cons (pt_fst (pt_snd hu)) isPolyTime_snd))
      isPolyTime_id
  have hiter : IsPolyTime (fun q : List Bool × (List α × List α) => (revStep d)^[q.1.length] q.2) := by
    refine isPolyTime_iter (revStep d) hstep (4 * Polynomial.X + 4) (fun u ⟨xs, acc⟩ k _ => ?_)
    have heq := revStep_len_eq d k xs acc
    rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  have hfn : (fun l : List α => l.reverse) =
      fun l => ((revStep d)^[(List.replicate (bitEncode l).length false).length] (l, [])).2 := by
    funext l
    rw [List.length_replicate, revStep_eq d (bitEncode l).length l [] (list_len_le_bitEncode l),
      List.append_nil]
  rw [hfn]
  have hprep : IsPolyTime (fun l : List α =>
      (List.replicate (bitEncode l).length false, (l, ([] : List α)))) :=
    isPolyTime_pair isPolyTime_unaryLen (isPolyTime_pair isPolyTime_id (isPolyTime_const []))
  exact pt_snd (isPolyTime_seq hprep hiter)

private def toUnaryStep {α : Type} (d : α) (p : List α × List Bool) : List α × List Bool :=
  let u := listUncons d p.1
  if u.1 then (u.2.2, false :: p.2) else p

private theorem toUnaryStep_spec {α : Type} [BitstringEncoding α] (d : α) :
    ∀ (k : ℕ) (xs : List α) (acc : List Bool),
      (bitEncode ((toUnaryStep d)^[k] (xs, acc)).1).length ≤ (bitEncode xs).length ∧
      ((toUnaryStep d)^[k] (xs, acc)).2.length ≤ acc.length + k ∧
      (xs.length ≤ k → ((toUnaryStep d)^[k] (xs, acc)).2 = List.replicate xs.length false ++ acc)
  | 0, xs, acc => by
    refine ⟨le_rfl, by simp, fun h => ?_⟩
    cases xs with
    | nil => simp
    | cons _ _ => simp at h
  | k + 1, xs, acc => by
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil =>
      simp only [toUnaryStep, listUncons, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2, h3⟩ := toUnaryStep_spec d k [] acc
      exact ⟨h1, by omega, fun _ => h3 (Nat.zero_le _)⟩
    | cons a t =>
      simp only [toUnaryStep, listUncons, ↓reduceIte]
      obtain ⟨h1, h2, h3⟩ := toUnaryStep_spec d k t (false :: acc)
      refine ⟨le_trans h1 (by rw [bitEncode_list_cons_len]; omega),
        by simp at h2; omega, fun hk => ?_⟩
      rw [h3 (by simp at hk; omega), List.length_cons, List.replicate_succ']
      simp [List.append_assoc]

private theorem isPolyTime_listToUnary {α : Type} [BitstringEncoding α] (d : α) :
    IsPolyTime (fun l : List α => List.replicate l.length false) := by
  have hstep : IsPolyTime (toUnaryStep d) := by
    have hu : IsPolyTime (fun p : List α × List Bool => listUncons d p.1) :=
      isPolyTime_seq isPolyTime_fst (isPolyTime_listUncons d)
    exact isPolyTime_ite (pt_fst hu)
      (isPolyTime_pair (pt_snd (pt_snd hu)) (isPolyTime_seq isPolyTime_snd isPolyTime_unarySucc))
      isPolyTime_id
  have hiter : IsPolyTime (fun q : List Bool × (List α × List Bool) =>
      (toUnaryStep d)^[q.1.length] q.2) := by
    refine isPolyTime_iter (toUnaryStep d) hstep (4 * Polynomial.X + 4) (fun u ⟨xs, acc⟩ k hk => ?_)
    obtain ⟨h1, h2, _⟩ := toUnaryStep_spec d k xs acc
    rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len,
      bitEncode_listBool_length, bitEncode_listBool_length, bitEncode_listBool_length]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  have hfn : (fun l : List α => List.replicate l.length false) =
      fun l => ((toUnaryStep d)^[(List.replicate (bitEncode l).length false).length] (l, [])).2 := by
    funext l
    rw [List.length_replicate,
      (toUnaryStep_spec d (bitEncode l).length l []).2.2 (list_len_le_bitEncode l),
      List.append_nil]
  rw [hfn]
  have hprep : IsPolyTime (fun l : List α =>
      (List.replicate (bitEncode l).length false, (l, ([] : List Bool)))) :=
    isPolyTime_pair isPolyTime_unaryLen (isPolyTime_pair isPolyTime_id (isPolyTime_const []))
  exact pt_snd (isPolyTime_seq hprep hiter)

private def lenStep {α : Type} (d : α) (p : List α × ℕ) : List α × ℕ :=
  let u := listUncons d p.1
  if u.1 then (u.2.2, p.2 + 1) else p

private theorem lenStep_spec {α : Type} [BitstringEncoding α] (d : α) :
    ∀ (k : ℕ) (xs : List α) (n : ℕ),
      (bitEncode ((lenStep d)^[k] (xs, n)).1).length ≤ (bitEncode xs).length ∧
      ((lenStep d)^[k] (xs, n)).2 ≤ n + k ∧
      (xs.length ≤ k → ((lenStep d)^[k] (xs, n)).2 = xs.length + n)
  | 0, xs, n => by
    refine ⟨le_rfl, by simp, fun h => ?_⟩
    cases xs with
    | nil => simp
    | cons _ _ => simp at h
  | k + 1, xs, n => by
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil =>
      simp only [lenStep, listUncons, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2, h3⟩ := lenStep_spec d k [] n
      exact ⟨h1, by omega, fun _ => h3 (Nat.zero_le _)⟩
    | cons a t =>
      simp only [lenStep, listUncons, ↓reduceIte]
      obtain ⟨h1, h2, h3⟩ := lenStep_spec d k t (n + 1)
      refine ⟨le_trans h1 (by rw [bitEncode_list_cons_len]; omega), by omega, fun hk => ?_⟩
      rw [h3 (by simp at hk; omega), List.length_cons]; omega

private theorem isPolyTime_listLen {α : Type} [BitstringEncoding α] (d : α) :
    IsPolyTime (fun l : List α => l.length) := by
  have hstep : IsPolyTime (lenStep d) := by
    have hu : IsPolyTime (fun p : List α × ℕ => listUncons d p.1) :=
      isPolyTime_seq isPolyTime_fst (isPolyTime_listUncons d)
    exact isPolyTime_ite (pt_fst hu)
      (isPolyTime_pair (pt_snd (pt_snd hu)) (pt_add isPolyTime_snd (isPolyTime_const 1)))
      isPolyTime_id
  have hiter : IsPolyTime (fun q : List Bool × (List α × ℕ) => (lenStep d)^[q.1.length] q.2) := by
    refine isPolyTime_iter (lenStep d) hstep (4 * Polynomial.X + 6) (fun u ⟨xs, n⟩ k hk => ?_)
    obtain ⟨h1, h2, _⟩ := lenStep_spec d k xs n
    have hn_len : (bitEncode ((lenStep d)^[k] (xs, n)).2).length ≤ (bitEncode n).length + k + 1 := by
      have hlt_n : n < 2 ^ (bitEncode n).length := lt_two_pow_bitEncode_nat n
      have hlt_k : k < 2 ^ k := Nat.lt_two_pow_self
      have hlt : ((lenStep d)^[k] (xs, n)).2 < 2 ^ ((bitEncode n).length + k + 1) := by
        have hp1 : 2 ^ (bitEncode n).length ≤ 2 ^ ((bitEncode n).length + k) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hp2 : 2 ^ k ≤ 2 ^ ((bitEncode n).length + k) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        rw [pow_succ]; omega
      exact length_encodeNat_le hlt
    rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len, bitEncode_listBool_length]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  have hfn : (fun l : List α => l.length) =
      fun l => ((lenStep d)^[(List.replicate (bitEncode l).length false).length] (l, 0)).2 := by
    funext l
    rw [List.length_replicate,
      (lenStep_spec d (bitEncode l).length l 0).2.2 (list_len_le_bitEncode l), add_zero]
  rw [hfn]
  have hprep : IsPolyTime (fun l : List α =>
      (List.replicate (bitEncode l).length false, (l, (0 : ℕ)))) :=
    isPolyTime_pair isPolyTime_unaryLen (isPolyTime_pair isPolyTime_id (isPolyTime_const 0))
  exact pt_snd (isPolyTime_seq hprep hiter)

private def repStep {α : Type} (p : α × List α) : α × List α := (p.1, p.1 :: p.2)

private theorem repStep_iter {α : Type} (k : ℕ) (x : α) (acc : List α) :
    repStep^[k] (x, acc) = (x, List.replicate k x ++ acc) := by
  induction k generalizing acc with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    change repStep^[k] (x, x :: acc) = _
    rw [ih (x :: acc), List.replicate_succ']
    simp [List.append_assoc]

private theorem bitEncode_replicate_len {α : Type} [BitstringEncoding α] (k : ℕ) (x : α) :
    (bitEncode (List.replicate k x)).length = k * (2 * (bitEncode x).length + 1) := by
  induction k with
  | zero => simp [bitEncode_list_nil]
  | succ k ih =>
    rw [List.replicate_succ, bitEncode_list_cons_len, ih]; ring

private theorem isPolyTime_listReplicate {α : Type} [BitstringEncoding α] :
    IsPolyTime (fun p : List Bool × α => List.replicate p.1.length p.2) := by
  have hstep : IsPolyTime (repStep (α := α)) :=
    isPolyTime_pair isPolyTime_fst isPolyTime_listCons
  have hiter : IsPolyTime (fun q : List Bool × (α × List α) => repStep^[q.1.length] q.2) := by
    refine isPolyTime_iter repStep hstep (2 * Polynomial.X * Polynomial.X + 4 * Polynomial.X + 4)
      (fun u ⟨x, acc⟩ k hk => ?_)
    rw [repStep_iter, bitEncode_pair_len, bitEncode_list_append_len, bitEncode_replicate_len]
    set L := (bitEncode (u, (x, acc))).length
    have hL : L = 2 * (3 * u.length) + 1 + (2 * (bitEncode x).length + 1 + (bitEncode acc).length) := by
      dsimp only [L]
      rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_listBool_length]
    have hmul : k * (2 * (bitEncode x).length + 1) ≤ L * L :=
      Nat.mul_le_mul (by omega) (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    have h2L : 2 * L * L = 2 * (L * L) := by ring
    omega
  have hfn : (fun p : List Bool × α => List.replicate p.1.length p.2) =
      fun p => (repStep^[p.1.length] (p.2, [])).2 := by
    funext ⟨u, x⟩; rw [repStep_iter, List.append_nil]
  rw [hfn]
  have hprep : IsPolyTime (fun p : List Bool × α => (p.1, (p.2, ([] : List α)))) :=
    isPolyTime_pair isPolyTime_fst (isPolyTime_pair isPolyTime_snd (isPolyTime_const []))
  exact pt_snd (isPolyTime_seq hprep hiter)

private def mapStep {α β γ : Type} (da : α) (f : γ × α → β)
    (st : γ × (List α × List β)) : γ × (List α × List β) :=
  let u := listUncons da st.2.1
  if u.1 then (st.1, (u.2.2, f (st.1, u.2.1) :: st.2.2)) else st

private theorem mapStep_spec {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] (da : α) (f : γ × α → β) (M : ℕ) :
    ∀ (k : ℕ) (c : γ) (xs : List α) (acc : List β),
      (∀ a ∈ xs, (bitEncode (f (c, a))).length ≤ M) →
      ((mapStep da f)^[k] (c, (xs, acc))).1 = c ∧
      (bitEncode ((mapStep da f)^[k] (c, (xs, acc))).2.1).length ≤ (bitEncode xs).length ∧
      (bitEncode ((mapStep da f)^[k] (c, (xs, acc))).2.2).length ≤
        (bitEncode acc).length + k * (2 * M + 1) ∧
      (xs.length ≤ k →
        ((mapStep da f)^[k] (c, (xs, acc))).2.2 = (xs.map (fun a => f (c, a))).reverse ++ acc)
  | 0, c, xs, acc, _ => by
    refine ⟨rfl, le_rfl, by simp, fun h => ?_⟩
    cases xs with
    | nil => simp
    | cons _ _ => simp at h
  | k + 1, c, xs, acc, hM => by
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil =>
      simp only [mapStep, listUncons, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2, h3, h4⟩ := mapStep_spec da f M k c [] acc (by simp)
      refine ⟨h1, h2, ?_, fun _ => h4 (Nat.zero_le _)⟩
      rw [Nat.succ_mul]; omega
    | cons a t =>
      simp only [mapStep, listUncons, ↓reduceIte]
      obtain ⟨h1, h2, h3, h4⟩ := mapStep_spec da f M k c t (f (c, a) :: acc)
        (fun x hx => hM x (List.mem_cons_of_mem a hx))
      have hfa : (bitEncode (f (c, a))).length ≤ M := hM a (List.mem_cons_self ..)
      rw [bitEncode_list_cons_len] at h3
      refine ⟨h1, le_trans h2 (by rw [bitEncode_list_cons_len]; omega), ?_, fun hk => ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [h4 (by simp at hk; omega), List.map_cons, List.reverse_cons, List.append_assoc]; rfl

private theorem isPolyTime_listMap {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] (da : α) (db : β) (f : γ × α → β) (hf : IsPolyTime f) :
    IsPolyTime (fun p : γ × List α => p.2.map (fun a => f (p.1, a))) := by
  obtain ⟨Pf, hPf⟩ := isPolyTime_output_bound hf
  have hstep : IsPolyTime (mapStep da f) := by
    have hu : IsPolyTime (fun st : γ × (List α × List β) => listUncons da st.2.1) :=
      isPolyTime_seq (pt_fst isPolyTime_snd) (isPolyTime_listUncons da)
    have hfa : IsPolyTime (fun st : γ × (List α × List β) => f (st.1, (listUncons da st.2.1).2.1)) :=
      isPolyTime_seq (isPolyTime_pair isPolyTime_fst (pt_fst (pt_snd hu))) hf
    exact isPolyTime_ite (pt_fst hu)
      (isPolyTime_pair isPolyTime_fst
        (isPolyTime_pair (pt_snd (pt_snd hu)) (pt_cons hfa (pt_snd isPolyTime_snd))))
      isPolyTime_id
  have hiter : IsPolyTime (fun q : List Bool × (γ × (List α × List β)) =>
      (mapStep da f)^[q.1.length] q.2) := by
    refine isPolyTime_iter (mapStep da f) hstep
      (4 * Polynomial.X + 4 + Polynomial.X * (2 * Pf + 1))
      (fun u ⟨c, xs, acc⟩ k hk => ?_)
    set L := (bitEncode (u, (c, (xs, acc)))).length
    have hL : L = 2 * (3 * u.length) + 1 + (2 * (bitEncode c).length + 1 +
        (2 * (bitEncode xs).length + 1 + (bitEncode acc).length)) := by
      dsimp only [L]
      rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len, bitEncode_listBool_length]
    have hM : ∀ a ∈ xs, (bitEncode (f (c, a))).length ≤ Pf.eval L := fun a ha => by
      have ha_le := bitEncode_mem_le ha
      have hca : (bitEncode (c, a)).length ≤ L := by rw [bitEncode_pair_len]; omega
      exact le_trans (hPf (c, a)) (poly_mono Pf hca)
    set st := (mapStep da f)^[k] (c, (xs, acc))
    obtain ⟨h1, h2, h3, _⟩ := mapStep_spec da f (Pf.eval L) k c xs acc hM
    have h1' : st.1 = c := h1
    have h2' : (bitEncode st.2.1).length ≤ (bitEncode xs).length := h2
    have h3' : (bitEncode st.2.2).length ≤ (bitEncode acc).length + k * (2 * Pf.eval L + 1) := h3
    have hst_len : (bitEncode st).length =
        2 * (bitEncode st.1).length + 1 + (2 * (bitEncode st.2.1).length + 1 + (bitEncode st.2.2).length) := by
      rw [bitEncode_pair_len st.1 st.2, bitEncode_pair_len st.2.1 st.2.2]
    change (bitEncode st).length ≤ _
    rw [hst_len, h1']
    have hk_le : k * (2 * Pf.eval L + 1) ≤ L * (2 * Pf.eval L + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat, Polynomial.eval_one]
    omega
  have hfn : (fun p : γ × List α => p.2.map (fun a => f (p.1, a))) =
      fun p => (((mapStep da f)^[(List.replicate (bitEncode p.2).length false).length]
        (p.1, (p.2, ([] : List β)))).2.2).reverse := by
    funext ⟨c, xs⟩
    rw [List.length_replicate]
    set M := Pf.eval (2 * (bitEncode c).length + 1 + (bitEncode xs).length)
    have hM : ∀ a ∈ xs, (bitEncode (f (c, a))).length ≤ M := fun a ha => by
      have ha_le := bitEncode_mem_le ha
      exact le_trans (hPf (c, a)) (poly_mono Pf (by rw [bitEncode_pair_len]; omega))
    have h4 := (mapStep_spec da f M (bitEncode xs).length c xs [] hM).2.2.2
      (list_len_le_bitEncode xs)
    rw [h4, List.append_nil, List.reverse_reverse]
  rw [hfn]
  have hprep : IsPolyTime (fun p : γ × List α =>
      (List.replicate (bitEncode p.2).length false, (p.1, (p.2, ([] : List β))))) :=
    isPolyTime_pair (isPolyTime_seq isPolyTime_snd isPolyTime_unaryLen)
      (isPolyTime_pair isPolyTime_fst (isPolyTime_pair isPolyTime_snd (isPolyTime_const [])))
  exact isPolyTime_seq (pt_snd (pt_snd (isPolyTime_seq hprep hiter))) (isPolyTime_listRev db)

private def zipMapD {α β γ : Type} (db : β) (f : α × β → γ) : List α → List β → List γ
  | [], _ => []
  | a :: as, [] => f (a, db) :: zipMapD db f as []
  | a :: as, b :: bs => f (a, b) :: zipMapD db f as bs

private theorem zipMapD_length {α β γ : Type} (db : β) (f : α × β → γ) :
    ∀ (xs : List α) (ys : List β), (zipMapD db f xs ys).length = xs.length
  | [], _ => rfl
  | _ :: as, [] => by simp [zipMapD, zipMapD_length db f as []]
  | _ :: as, _ :: bs => by simp [zipMapD, zipMapD_length db f as bs]

private theorem zipMapD_getElem? {α β γ : Type} (db : β) (f : α × β → γ) :
    ∀ (xs : List α) (ys : List β) (i : ℕ),
      (zipMapD db f xs ys)[i]? = xs[i]?.map (fun a => f (a, ys[i]?.getD db))
  | [], _, _ => by simp [zipMapD]
  | a :: as, [], 0 => by simp [zipMapD]
  | a :: as, [], i + 1 => by simp [zipMapD, zipMapD_getElem? db f as [] i]
  | a :: as, b :: bs, 0 => by simp [zipMapD]
  | a :: as, b :: bs, i + 1 => by simp [zipMapD, zipMapD_getElem? db f as bs i]

private def zipStep {α β γ : Type} (da : α) (db : β) (f : α × β → γ)
    (st : List α × (List β × List γ)) : List α × (List β × List γ) :=
  let ua := listUncons da st.1
  let ub := listUncons db st.2.1
  if ua.1 then (ua.2.2, (ub.2.2, f (ua.2.1, ub.2.1) :: st.2.2)) else st

private theorem zipStep_spec {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] (da : α) (db : β) (f : α × β → γ) (M : ℕ) :
    ∀ (k : ℕ) (xs : List α) (ys : List β) (acc : List γ),
      (∀ a ∈ xs, (∀ b ∈ ys, (bitEncode (f (a, b))).length ≤ M) ∧
        (bitEncode (f (a, db))).length ≤ M) →
      (bitEncode ((zipStep da db f)^[k] (xs, (ys, acc))).1).length ≤ (bitEncode xs).length ∧
      (bitEncode ((zipStep da db f)^[k] (xs, (ys, acc))).2.1).length ≤ (bitEncode ys).length ∧
      (bitEncode ((zipStep da db f)^[k] (xs, (ys, acc))).2.2).length ≤
        (bitEncode acc).length + k * (2 * M + 1) ∧
      (xs.length ≤ k →
        ((zipStep da db f)^[k] (xs, (ys, acc))).2.2 = (zipMapD db f xs ys).reverse ++ acc)
  | 0, xs, ys, acc, _ => by
    refine ⟨le_rfl, le_rfl, by simp, fun h => ?_⟩
    cases xs with
    | nil => simp [zipMapD]
    | cons _ _ => simp at h
  | k + 1, xs, ys, acc, hM => by
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil =>
      simp only [zipStep, listUncons, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2, h3, h4⟩ := zipStep_spec da db f M k [] ys acc (by simp)
      refine ⟨h1, h2, ?_, fun _ => h4 (Nat.zero_le _)⟩
      rw [Nat.succ_mul]; omega
    | cons a as =>
      cases ys with
      | nil =>
        simp only [zipStep, listUncons, ↓reduceIte]
        obtain ⟨h1, h2, h3, h4⟩ := zipStep_spec da db f M k as [] (f (a, db) :: acc)
          (fun x hx => hM x (List.mem_cons_of_mem a hx))
        have hfa : (bitEncode (f (a, db))).length ≤ M := (hM a (List.mem_cons_self ..)).2
        rw [bitEncode_list_cons_len] at h3
        refine ⟨le_trans h1 (by rw [bitEncode_list_cons_len]; omega), h2, ?_, fun hk => ?_⟩
        · rw [Nat.succ_mul]; omega
        · rw [h4 (by simp at hk; omega), zipMapD, List.reverse_cons, List.append_assoc]; rfl
      | cons b bs =>
        simp only [zipStep, listUncons, ↓reduceIte]
        obtain ⟨h1, h2, h3, h4⟩ := zipStep_spec da db f M k as bs (f (a, b) :: acc)
          (fun x hx => ⟨fun y hy => (hM x (List.mem_cons_of_mem a hx)).1 y (List.mem_cons_of_mem b hy),
            (hM x (List.mem_cons_of_mem a hx)).2⟩)
        have hfa : (bitEncode (f (a, b))).length ≤ M :=
          (hM a (List.mem_cons_self ..)).1 b (List.mem_cons_self ..)
        rw [bitEncode_list_cons_len] at h3
        refine ⟨le_trans h1 (by rw [bitEncode_list_cons_len]; omega),
          le_trans h2 (by rw [bitEncode_list_cons_len]; omega), ?_, fun hk => ?_⟩
        · rw [Nat.succ_mul]; omega
        · rw [h4 (by simp at hk; omega), zipMapD, List.reverse_cons, List.append_assoc]; rfl

private theorem isPolyTime_zipMapD {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] (da : α) (db : β) (dc : γ) (f : α × β → γ) (hf : IsPolyTime f) :
    IsPolyTime (fun p : List α × List β => zipMapD db f p.1 p.2) := by
  obtain ⟨Pf, hPf⟩ := isPolyTime_output_bound hf
  have hstep : IsPolyTime (zipStep da db f) := by
    have hua : IsPolyTime (fun st : List α × (List β × List γ) => listUncons da st.1) :=
      isPolyTime_seq isPolyTime_fst (isPolyTime_listUncons da)
    have hub : IsPolyTime (fun st : List α × (List β × List γ) => listUncons db st.2.1) :=
      isPolyTime_seq (pt_fst isPolyTime_snd) (isPolyTime_listUncons db)
    have hfab : IsPolyTime (fun st : List α × (List β × List γ) =>
        f ((listUncons da st.1).2.1, (listUncons db st.2.1).2.1)) :=
      isPolyTime_seq (isPolyTime_pair (pt_fst (pt_snd hua)) (pt_fst (pt_snd hub))) hf
    exact isPolyTime_ite (pt_fst hua)
      (isPolyTime_pair (pt_snd (pt_snd hua))
        (isPolyTime_pair (pt_snd (pt_snd hub)) (pt_cons hfab (pt_snd isPolyTime_snd))))
      isPolyTime_id
  let Cdb : ℕ := (bitEncode db).length
  have hiter : IsPolyTime (fun q : List Bool × (List α × (List β × List γ)) =>
      (zipStep da db f)^[q.1.length] q.2) := by
    refine isPolyTime_iter (zipStep da db f) hstep
      (4 * Polynomial.X + 4 + Polynomial.X * (2 * Pf.comp (Polynomial.X + (Cdb : Polynomial ℕ)) + 1))
      (fun u ⟨xs, ys, acc⟩ k hk => ?_)
    set L := (bitEncode (u, (xs, (ys, acc)))).length
    have hL : L = 2 * (3 * u.length) + 1 + (2 * (bitEncode xs).length + 1 +
        (2 * (bitEncode ys).length + 1 + (bitEncode acc).length)) := by
      dsimp only [L]
      rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len, bitEncode_listBool_length]
    have hM : ∀ a ∈ xs, (∀ b ∈ ys, (bitEncode (f (a, b))).length ≤ Pf.eval (L + Cdb)) ∧
        (bitEncode (f (a, db))).length ≤ Pf.eval (L + Cdb) := fun a ha => by
      have ha_le := bitEncode_mem_le ha
      refine ⟨fun b hb => ?_, ?_⟩
      · have hb_le := bitEncode_mem_le hb
        have hab : (bitEncode (a, b)).length ≤ L + Cdb := by rw [bitEncode_pair_len]; omega
        exact le_trans (hPf (a, b)) (poly_mono Pf hab)
      · have hab : (bitEncode (a, db)).length ≤ L + Cdb := by rw [bitEncode_pair_len]; omega
        exact le_trans (hPf (a, db)) (poly_mono Pf hab)
    set st := (zipStep da db f)^[k] (xs, (ys, acc))
    obtain ⟨h1, h2, h3, _⟩ := zipStep_spec da db f (Pf.eval (L + Cdb)) k xs ys acc hM
    have h1' : (bitEncode st.1).length ≤ (bitEncode xs).length := h1
    have h2' : (bitEncode st.2.1).length ≤ (bitEncode ys).length := h2
    have h3' : (bitEncode st.2.2).length ≤ (bitEncode acc).length + k * (2 * Pf.eval (L + Cdb) + 1) := h3
    have hst_len : (bitEncode st).length =
        2 * (bitEncode st.1).length + 1 + (2 * (bitEncode st.2.1).length + 1 + (bitEncode st.2.2).length) := by
      rw [bitEncode_pair_len st.1 st.2, bitEncode_pair_len st.2.1 st.2.2]
    change (bitEncode st).length ≤ _
    rw [hst_len]
    have hk_le : k * (2 * Pf.eval (L + Cdb) + 1) ≤ L * (2 * Pf.eval (L + Cdb) + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_comp,
      Polynomial.eval_natCast, Nat.cast_id]
    omega
  have hfn : (fun p : List α × List β => zipMapD db f p.1 p.2) =
      fun p => (((zipStep da db f)^[(List.replicate (bitEncode p.1).length false).length]
        (p.1, (p.2, ([] : List γ)))).2.2).reverse := by
    funext ⟨xs, ys⟩
    rw [List.length_replicate]
    set M := Pf.eval ((bitEncode xs).length * 2 + 1 + (bitEncode ys).length + Cdb)
    have hM : ∀ a ∈ xs, (∀ b ∈ ys, (bitEncode (f (a, b))).length ≤ M) ∧
        (bitEncode (f (a, db))).length ≤ M := fun a ha => by
      have ha_le := bitEncode_mem_le ha
      refine ⟨fun b hb => ?_, ?_⟩
      · have hb_le := bitEncode_mem_le hb
        exact le_trans (hPf (a, b)) (poly_mono Pf (by rw [bitEncode_pair_len]; omega))
      · exact le_trans (hPf (a, db)) (poly_mono Pf (by rw [bitEncode_pair_len]; omega))
    have h4 := (zipStep_spec da db f M (bitEncode xs).length xs ys [] hM).2.2.2
      (list_len_le_bitEncode xs)
    rw [h4, List.append_nil, List.reverse_reverse]
  rw [hfn]
  have hprep : IsPolyTime (fun p : List α × List β =>
      (List.replicate (bitEncode p.1).length false, (p.1, (p.2, ([] : List γ))))) :=
    isPolyTime_pair (isPolyTime_seq isPolyTime_fst isPolyTime_unaryLen)
      (isPolyTime_pair isPolyTime_fst (isPolyTime_pair isPolyTime_snd (isPolyTime_const [])))
  exact isPolyTime_seq (pt_snd (pt_snd (isPolyTime_seq hprep hiter))) (isPolyTime_listRev dc)

/- ### Exact Rational Dot Product & LP Feasibility Checker (`checkLP`) -/

private def ratToTriple (q : ℚ) : (ℕ × ℕ) × ℕ :=
  ((q.num.toNat, (-q.num).toNat), q.den)

private theorem isPolyTime_ratToTriple : IsPolyTime ratToTriple :=
  isPolyTime_ofSameEncode ratToTriple (fun _ => rfl)

private def fracVal (f : (ℕ × ℕ) × ℕ) : ℚ :=
  (((f.1.1 : ℤ) - (f.1.2 : ℤ)) : ℚ) / (f.2 : ℚ)

private theorem fracVal_ratToTriple (q : ℚ) : fracVal (ratToTriple q) = q := by
  simp only [fracVal, ratToTriple]
  have hnum : ((q.num.toNat : ℤ) - ((-q.num).toNat : ℤ)) = q.num := by omega
  have hnum_q : (((q.num.toNat : ℤ) - ((-q.num).toNat : ℤ)) : ℚ) = (q.num : ℚ) := by
    exact_mod_cast hnum
  rw [hnum_q]
  exact Rat.num_div_den q

private def rawWeight (q : ℚ) : ℕ :=
  q.num.toNat + (-q.num).toNat + q.den

private theorem rawWeight_pos (q : ℚ) : 1 ≤ rawWeight q := by
  have := q.den_pos; dsimp only [rawWeight]; omega

private theorem rawWeight_lt_pow (q : ℚ) : rawWeight q < 2 ^ (bitEncode q).length := by
  have hlen : (bitEncode q).length =
      4 * (bitEncode q.num.toNat).length + 2 * (bitEncode (-q.num).toNat).length +
        (bitEncode q.den).length + 3 := by
    change (delimit (delimit (encodeNat q.num.toNat) ++ encodeNat (-q.num).toNat) ++
      encodeNat q.den).length = _
    rw [List.length_append, length_delimit, List.length_append, length_delimit]
    change 2 * (2 * (bitEncode q.num.toNat).length + 1 + (bitEncode (-q.num).toNat).length) + 1 +
      (bitEncode q.den).length = _
    omega
  have hp := lt_two_pow_bitEncode_nat q.num.toNat
  have hn := lt_two_pow_bitEncode_nat (-q.num).toNat
  have hd := lt_two_pow_bitEncode_nat q.den
  have hm1 : 2 ^ (bitEncode q.num.toNat).length ≤
      2 ^ (4 * (bitEncode q.num.toNat).length + 2 * (bitEncode (-q.num).toNat).length +
        (bitEncode q.den).length + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hm2 : 2 ^ (bitEncode (-q.num).toNat).length ≤
      2 ^ (4 * (bitEncode q.num.toNat).length + 2 * (bitEncode (-q.num).toNat).length +
        (bitEncode q.den).length + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hm3 : 2 ^ (bitEncode q.den).length ≤
      2 ^ (4 * (bitEncode q.num.toNat).length + 2 * (bitEncode (-q.num).toNat).length +
        (bitEncode q.den).length + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  dsimp only [rawWeight]
  rw [hlen, show 4 * (bitEncode q.num.toNat).length + 2 * (bitEncode (-q.num).toNat).length +
    (bitEncode q.den).length + 3 =
    (4 * (bitEncode q.num.toNat).length + 2 * (bitEncode (-q.num).toNat).length +
      (bitEncode q.den).length + 1) + 2 by omega, pow_add]
  omega

private def prodWt : List ℚ → ℕ
  | [] => 1
  | q :: qs => rawWeight q * prodWt qs

private theorem prodWt_pos : ∀ l : List ℚ, 1 ≤ prodWt l
  | [] => le_rfl
  | q :: qs => Nat.mul_pos (rawWeight_pos q) (prodWt_pos qs)

private theorem prodWt_lt_pow : ∀ l : List ℚ, prodWt l < 2 ^ ((bitEncode l).length + 1)
  | [] => by simp [prodWt, bitEncode_list_nil]
  | q :: qs => by
    rw [prodWt, bitEncode_list_cons_len]
    have hq := rawWeight_lt_pow q
    have hqs := prodWt_lt_pow qs
    have hmul := Nat.mul_lt_mul'' hq hqs
    rw [← pow_add] at hmul
    exact lt_of_lt_of_le hmul (Nat.pow_le_pow_right (by omega) (by omega))

private def fracMulAdd (acc : (ℕ × ℕ) × ℕ) (a b : (ℕ × ℕ) × ℕ) : (ℕ × ℕ) × ℕ :=
  let p := a.1.1 * b.1.1 + a.1.2 * b.1.2
  let n := a.1.1 * b.1.2 + a.1.2 * b.1.1
  let d := a.2 * b.2
  ((acc.1.1 * d + p * acc.2, acc.1.2 * d + n * acc.2), acc.2 * d)

private theorem fracMulAdd_val (acc : (ℕ × ℕ) × ℕ) (a b : ℚ) (hD : 0 < acc.2) :
    0 < (fracMulAdd acc (ratToTriple a) (ratToTriple b)).2 ∧
    fracVal (fracMulAdd acc (ratToTriple a) (ratToTriple b)) = fracVal acc + a * b := by
  have hd : 0 < a.den * b.den := Nat.mul_pos a.den_pos b.den_pos
  have hD' : 0 < acc.2 * (a.den * b.den) := Nat.mul_pos hD hd
  refine ⟨hD', ?_⟩
  conv_rhs => rw [← fracVal_ratToTriple a, ← fracVal_ratToTriple b]
  simp only [fracVal, fracMulAdd, ratToTriple]
  have hDq : (acc.2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hD)
  have haq : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp a.den_pos)
  have hbq : (b.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp b.den_pos)
  push_cast
  field_simp [hDq, haq, hbq]
  ring

private theorem fracMulAdd_bound (acc : (ℕ × ℕ) × ℕ) (a b : ℚ) :
    let r := fracMulAdd acc (ratToTriple a) (ratToTriple b)
    r.1.1 + r.1.2 + r.2 ≤ (acc.1.1 + acc.1.2 + acc.2) * (rawWeight a * rawWeight b) := by
  dsimp only [fracMulAdd, ratToTriple, rawWeight]
  set P := acc.1.1; set N := acc.1.2; set D := acc.2
  set ap := a.num.toNat; set an := (-a.num).toNat; set ad := a.den
  set bp := b.num.toNat; set bn := (-b.num).toNat; set bd := b.den
  set p := ap * bp + an * bn
  set n := ap * bn + an * bp
  set d := ad * bd
  have h1 : p + n + d ≤ (ap + an + ad) * (bp + bn + bd) := by
    dsimp only [p, n, d]; nlinarith
  have h2 : (P * d + p * D) + (N * d + n * D) + D * d ≤ (P + N + D) * (p + n + d) := by
    have hEq : (P + N + D) * (p + n + d) =
        ((P * d + p * D) + (N * d + n * D) + D * d) + (P * p + P * n + N * p + N * n) := by ring
    omega
  exact le_trans h2 (Nat.mul_le_mul_left _ h1)

private theorem isPolyTime_fracMulAdd :
    IsPolyTime (fun x : ((ℕ × ℕ) × ℕ) × (((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) =>
      fracMulAdd x.1 x.2.1 x.2.2) := by
  have hid : IsPolyTime (id : ((ℕ × ℕ) × ℕ) × (((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) → _) := isPolyTime_id
  have accP := pt_fst (pt_fst (pt_fst hid))
  have accN := pt_snd (pt_fst (pt_fst hid))
  have accD := pt_snd (pt_fst hid)
  have aP := pt_fst (pt_fst (pt_fst (pt_snd hid)))
  have aN := pt_snd (pt_fst (pt_fst (pt_snd hid)))
  have aD := pt_snd (pt_fst (pt_snd hid))
  have bP := pt_fst (pt_fst (pt_snd (pt_snd hid)))
  have bN := pt_snd (pt_fst (pt_snd (pt_snd hid)))
  have bD := pt_snd (pt_snd (pt_snd hid))
  have hp := pt_add (pt_mul aP bP) (pt_mul aN bN)
  have hn := pt_add (pt_mul aP bN) (pt_mul aN bP)
  have hd := pt_mul aD bD
  have hP' := pt_add (pt_mul accP hd) (pt_mul hp accD)
  have hN' := pt_add (pt_mul accN hd) (pt_mul hn accD)
  have hD' := pt_mul accD hd
  exact isPolyTime_pair (isPolyTime_pair hP' hN') hD'

private def dotStep (st : List ℚ × (List ℚ × ((ℕ × ℕ) × ℕ))) :
    List ℚ × (List ℚ × ((ℕ × ℕ) × ℕ)) :=
  let ua := listUncons (0 : ℚ) st.1
  let ub := listUncons (0 : ℚ) st.2.1
  if ua.1 && ub.1 then
    (ua.2.2, (ub.2.2, fracMulAdd st.2.2 (ratToTriple ua.2.1) (ratToTriple ub.2.1)))
  else st

private def zipDot : List ℚ → List ℚ → ℚ
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => a * b + zipDot as bs

private theorem zipDot_eq_fin_sum : ∀ (n : ℕ) (xs ys : List ℚ),
    xs.length = n → ys.length = n →
    zipDot xs ys = ∑ j : Fin n, xs[j.val]?.getD 0 * ys[j.val]?.getD 0
  | 0, [], [], _, _ => by simp [zipDot]
  | n + 1, a :: as, b :: bs, hxs, hys => by
    rw [zipDot, Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getElem?_cons_zero, Option.getD_some,
      Fin.val_succ, List.getElem?_cons_succ]
    rw [zipDot_eq_fin_sum n as bs (by simp at hxs; exact hxs) (by simp at hys; exact hys)]
  | 0, _ :: _, _, hxs, _ => by simp at hxs
  | 0, [], _ :: _, _, hys => by simp at hys
  | _ + 1, [], _, hxs, _ => by simp at hxs
  | _ + 1, _ :: _, [], _, hys => by simp at hys

private theorem dotStep_spec : ∀ (k : ℕ) (xs ys : List ℚ) (acc : (ℕ × ℕ) × ℕ),
    let st := dotStep^[k] (xs, (ys, acc))
    (bitEncode st.1).length ≤ (bitEncode xs).length ∧
    (bitEncode st.2.1).length ≤ (bitEncode ys).length ∧
    (st.2.2.1.1 + st.2.2.1.2 + st.2.2.2) * (prodWt st.1 * prodWt st.2.1) ≤
      (acc.1.1 + acc.1.2 + acc.2) * (prodWt xs * prodWt ys) ∧
    (0 < acc.2 → xs.length ≤ k →
      0 < st.2.2.2 ∧ fracVal st.2.2 = fracVal acc + zipDot xs ys)
  | 0, xs, ys, acc => by
    dsimp only
    refine ⟨le_rfl, le_rfl, le_rfl, fun hD hlen => ?_⟩
    cases xs with
    | nil => simp [zipDot, hD]
    | cons _ _ => simp at hlen
  | k + 1, xs, ys, acc => by
    dsimp only
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil =>
      simp only [dotStep, listUncons, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      have h := dotStep_spec k [] ys acc
      exact ⟨h.1, h.2.1, h.2.2.1, fun hD _ => h.2.2.2 hD (Nat.zero_le _)⟩
    | cons a as =>
      cases ys with
      | nil =>
        simp only [dotStep, listUncons, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        have h := dotStep_spec k (a :: as) [] acc
        refine ⟨h.1, h.2.1, h.2.2.1, fun hD _ => ?_⟩
        have hnoop : ∀ m, dotStep^[m] (a :: as, ([], acc)) = (a :: as, ([], acc)) := by
          intro m; induction m with
          | zero => rfl
          | succ m ihm =>
            rw [Function.iterate_succ_apply]
            simpa [dotStep, listUncons] using ihm
        rw [hnoop k]; simp [zipDot, hD]
      | cons b bs =>
        simp only [dotStep, listUncons, Bool.and_self, ↓reduceIte]
        set acc' := fracMulAdd acc (ratToTriple a) (ratToTriple b)
        obtain ⟨h1, h2, h3, h4⟩ := dotStep_spec k as bs acc'
        refine ⟨le_trans h1 (by rw [bitEncode_list_cons_len]; omega),
          le_trans h2 (by rw [bitEncode_list_cons_len]; omega), ?_, fun hD hlen => ?_⟩
        · have hb := fracMulAdd_bound acc a b
          have hprod : prodWt (a :: as) * prodWt (b :: bs) =
              (rawWeight a * rawWeight b) * (prodWt as * prodWt bs) := by
            simp only [prodWt]; ring
          rw [hprod]
          calc _ ≤ (acc'.1.1 + acc'.1.2 + acc'.2) * (prodWt as * prodWt bs) := h3
            _ ≤ ((acc.1.1 + acc.1.2 + acc.2) * (rawWeight a * rawWeight b)) *
                  (prodWt as * prodWt bs) := Nat.mul_le_mul_right _ hb
            _ = (acc.1.1 + acc.1.2 + acc.2) * ((rawWeight a * rawWeight b) *
                  (prodWt as * prodWt bs)) := by ring
        · obtain ⟨hD', hval'⟩ := fracMulAdd_val acc a b hD
          obtain ⟨hDfin, hvalfin⟩ := h4 hD' (by simp at hlen; omega)
          refine ⟨hDfin, ?_⟩
          rw [hvalfin, hval', zipDot]; ring

private def checkRow (p : (List ℚ × ℚ) × List ℚ) : Bool :=
  let acc := (dotStep^[(List.replicate (bitEncode p.1.1).length false).length]
    (p.1.1, (p.2, ((0, 0), 1)))).2.2
  let r := ratToTriple p.1.2
  decide (acc.1.1 * r.2 + r.1.2 * acc.2 ≤ r.1.1 * acc.2 + acc.1.2 * r.2)

private theorem checkRow_iff (row : List ℚ) (rhs : ℚ) (y : List ℚ) :
    checkRow ((row, rhs), y) = true ↔ zipDot row y ≤ rhs := by
  dsimp only [checkRow]
  rw [List.length_replicate]
  obtain ⟨hD, hval⟩ := (dotStep_spec (bitEncode row).length row y ((0, 0), 1)).2.2.2
    (by omega) (list_len_le_bitEncode row)
  have hval0 : fracVal ((0, 0), 1) = 0 := by simp [fracVal]
  rw [hval0, zero_add] at hval
  set acc := (dotStep^[(bitEncode row).length] (row, (y, ((0, 0), 1)))).2.2
  rw [decide_eq_true_eq]
  conv_rhs => rw [← hval, ← fracVal_ratToTriple rhs]
  simp only [fracVal, ratToTriple]
  have hDq : (0 : ℚ) < (acc.2 : ℚ) := Nat.cast_pos.mpr hD
  have hrq : (0 : ℚ) < (rhs.den : ℚ) := Nat.cast_pos.mpr rhs.den_pos
  rw [div_le_div_iff₀ hDq hrq]
  constructor
  · intro h
    have hq : ((acc.1.1 * rhs.den + (-rhs.num).toNat * acc.2 : ℕ) : ℚ) ≤
        ((rhs.num.toNat * acc.2 + acc.1.2 * rhs.den : ℕ) : ℚ) := by exact_mod_cast h
    push_cast at hq ⊢
    linarith
  · intro h
    push_cast at h
    have hq : ((acc.1.1 * rhs.den + (-rhs.num).toNat * acc.2 : ℕ) : ℚ) ≤
        ((rhs.num.toNat * acc.2 + acc.1.2 * rhs.den : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast hq

private theorem isPolyTime_checkRow : IsPolyTime checkRow := by
  have hstep : IsPolyTime dotStep := by
    have hid : IsPolyTime (id : List ℚ × (List ℚ × ((ℕ × ℕ) × ℕ)) → _) := isPolyTime_id
    have hua := isPolyTime_seq (pt_fst hid) (isPolyTime_listUncons (0 : ℚ))
    have hub := isPolyTime_seq (pt_fst (pt_snd hid)) (isPolyTime_listUncons (0 : ℚ))
    have hcond := pt_and (pt_fst hua) (pt_fst hub)
    have ha := isPolyTime_seq (pt_fst (pt_snd hua)) isPolyTime_ratToTriple
    have hb := isPolyTime_seq (pt_fst (pt_snd hub)) isPolyTime_ratToTriple
    have hacc' := isPolyTime_seq (isPolyTime_pair (pt_snd (pt_snd hid)) (isPolyTime_pair ha hb))
      isPolyTime_fracMulAdd
    exact isPolyTime_ite hcond
      (isPolyTime_pair (pt_snd (pt_snd hua)) (isPolyTime_pair (pt_snd (pt_snd hub)) hacc'))
      hid
  have hiter : IsPolyTime (fun q : List Bool × (List ℚ × (List ℚ × ((ℕ × ℕ) × ℕ))) =>
      dotStep^[q.1.length] q.2) := by
    refine isPolyTime_iter dotStep hstep (20 * Polynomial.X + 40)
      (fun u ⟨xs, ys, ((P, N), D)⟩ k _ => ?_)
    set st := dotStep^[k] (xs, (ys, ((P, N), D)))
    obtain ⟨h1, h2, h3, _⟩ := dotStep_spec k xs ys ((P, N), D)
    have h1' : (bitEncode st.1).length ≤ (bitEncode xs).length := h1
    have h2' : (bitEncode st.2.1).length ≤ (bitEncode ys).length := h2
    have hp1 : 1 ≤ prodWt st.1 * prodWt st.2.1 := Nat.mul_pos (prodWt_pos _) (prodWt_pos _)
    have hsum_le : st.2.2.1.1 + st.2.2.1.2 + st.2.2.2 ≤
        (P + N + D) * (prodWt xs * prodWt ys) := by
      calc st.2.2.1.1 + st.2.2.1.2 + st.2.2.2
          ≤ (st.2.2.1.1 + st.2.2.1.2 + st.2.2.2) * (prodWt st.1 * prodWt st.2.1) :=
            Nat.le_mul_of_pos_right _ hp1
        _ ≤ (P + N + D) * (prodWt xs * prodWt ys) := h3
    have hPND_lt : P + N + D < 2 ^ ((bitEncode P).length + (bitEncode N).length +
        (bitEncode D).length + 2) := by
      have hp := lt_two_pow_bitEncode_nat P
      have hn := lt_two_pow_bitEncode_nat N
      have hd := lt_two_pow_bitEncode_nat D
      set E := (bitEncode P).length + (bitEncode N).length + (bitEncode D).length
      have e1 : 2 ^ (bitEncode P).length ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      have e2 : 2 ^ (bitEncode N).length ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      have e3 : 2 ^ (bitEncode D).length ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      rw [pow_add]; omega
    have hxy_lt : prodWt xs * prodWt ys < 2 ^ ((bitEncode xs).length + (bitEncode ys).length + 2) := by
      have hmul := Nat.mul_lt_mul'' (prodWt_lt_pow xs) (prodWt_lt_pow ys)
      rw [← pow_add] at hmul
      exact lt_of_lt_of_eq hmul (by congr 1; omega)
    set K := (bitEncode P).length + (bitEncode N).length + (bitEncode D).length +
      (bitEncode xs).length + (bitEncode ys).length + 4
    have htot_lt : st.2.2.1.1 + st.2.2.1.2 + st.2.2.2 < 2 ^ K := by
      have hmul := Nat.mul_lt_mul'' hPND_lt hxy_lt
      rw [← pow_add] at hmul
      exact lt_of_le_of_lt hsum_le (lt_of_lt_of_eq hmul (by congr 1; omega))
    have hbP : (bitEncode st.2.2.1.1).length ≤ K := length_encodeNat_le (by omega)
    have hbN : (bitEncode st.2.2.1.2).length ≤ K := length_encodeNat_le (by omega)
    have hbD : (bitEncode st.2.2.2).length ≤ K := length_encodeNat_le (by omega)
    have hL : (bitEncode (u, (xs, (ys, ((P, N), D))))).length =
        2 * (3 * u.length) + 1 + (2 * (bitEncode xs).length + 1 +
          (2 * (bitEncode ys).length + 1 +
            (2 * (2 * (bitEncode P).length + 1 + (bitEncode N).length) + 1 + (bitEncode D).length))) := by
      rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len,
        bitEncode_pair_len, bitEncode_listBool_length]
    have hst_len : (bitEncode st).length =
        2 * (bitEncode st.1).length + 1 + (2 * (bitEncode st.2.1).length + 1 +
          (2 * (2 * (bitEncode st.2.2.1.1).length + 1 + (bitEncode st.2.2.1.2).length) + 1 + (bitEncode st.2.2.2).length)) := by
      rw [bitEncode_pair_len st.1 st.2, bitEncode_pair_len st.2.1 st.2.2,
        bitEncode_pair_len st.2.2.1 st.2.2.2, bitEncode_pair_len st.2.2.1.1 st.2.2.1.2]
    change (bitEncode st).length ≤ _
    rw [hst_len]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  have hid : IsPolyTime (id : (List ℚ × ℚ) × List ℚ → _) := isPolyTime_id
  have hprep : IsPolyTime (fun p : (List ℚ × ℚ) × List ℚ =>
      (List.replicate (bitEncode p.1.1).length false, (p.1.1, (p.2, (((0, 0), 1) : (ℕ × ℕ) × ℕ))))) :=
    isPolyTime_pair (isPolyTime_seq (pt_fst (pt_fst hid)) isPolyTime_unaryLen)
      (isPolyTime_pair (pt_fst (pt_fst hid))
        (isPolyTime_pair (pt_snd hid) (isPolyTime_const ((0, 0), 1))))
  have hacc := pt_snd (pt_snd (isPolyTime_seq hprep hiter))
  have hr := isPolyTime_seq (pt_snd (pt_fst hid)) isPolyTime_ratToTriple
  have hlhs := pt_add (pt_mul (pt_fst (pt_fst hacc)) (pt_snd hr))
    (pt_mul (pt_snd (pt_fst hr)) (pt_snd hacc))
  have hrhs := pt_add (pt_mul (pt_fst (pt_fst hr)) (pt_snd hacc))
    (pt_mul (pt_snd (pt_fst hacc)) (pt_snd hr))
  exact pt_le hlhs hrhs

private def checkConsStep (st : (ℕ × List ℚ) × (List (List ℚ × ℚ) × Bool)) :
    (ℕ × List ℚ) × (List (List ℚ × ℚ) × Bool) :=
  let u := listUncons (([], (0 : ℚ))) st.2.1
  if u.1 then
    let ok := decide (u.2.1.1.length = st.1.1) && checkRow (u.2.1, st.1.2)
    (st.1, (u.2.2, st.2.2 && ok))
  else st

private theorem checkConsStep_spec :
    ∀ (k : ℕ) (n : ℕ) (y : List ℚ) (cons : List (List ℚ × ℚ)) (acc : Bool),
      let st := checkConsStep^[k] ((n, y), (cons, acc))
      st.1 = (n, y) ∧
      (bitEncode st.2.1).length ≤ (bitEncode cons).length ∧
      (cons.length ≤ k →
        (st.2.2 = true ↔ acc = true ∧ ∀ r ∈ cons, r.1.length = n ∧ zipDot r.1 y ≤ r.2))
  | 0, n, y, cons, acc => by
    dsimp only
    refine ⟨rfl, le_rfl, fun h => ?_⟩
    cases cons with
    | nil => simp
    | cons _ _ => simp at h
  | k + 1, n, y, cons, acc => by
    dsimp only
    rw [Function.iterate_succ_apply]
    cases cons with
    | nil =>
      have hst : checkConsStep ((n, y), ([], acc)) = ((n, y), ([], acc)) := rfl
      rw [hst]
      have h := checkConsStep_spec k n y [] acc
      exact ⟨h.1, h.2.1, fun _ => h.2.2 (Nat.zero_le _)⟩
    | cons r rs =>
      have hst : checkConsStep ((n, y), (r :: rs, acc)) =
          ((n, y), (rs, acc && (decide (r.1.length = n) && checkRow (r, y)))) := rfl
      rw [hst]
      have h := checkConsStep_spec k n y rs (acc && (decide (r.1.length = n) && checkRow (r, y)))
      refine ⟨h.1, le_trans h.2.1 (by rw [bitEncode_list_cons_len]; omega), fun hk => ?_⟩
      rw [h.2.2 (by simp at hk; omega)]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      have hcr : checkRow (r, y) = true ↔ zipDot r.1 y ≤ r.2 := checkRow_iff r.1 r.2 y
      constructor
      · rintro ⟨⟨ha, hrlen, hdot⟩, hall⟩
        refine ⟨ha, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hxs
        · exact ⟨hrlen, hcr.mp hdot⟩
        · exact hall x hxs
      · rintro ⟨ha, hall⟩
        have hr0 := hall r (List.mem_cons_self ..)
        exact ⟨⟨ha, hr0.1, hcr.mpr hr0.2⟩, fun x hx => hall x (List.mem_cons_of_mem r hx)⟩

private def checkLP (p : (ℕ × List (List ℚ × ℚ)) × List ℚ) : Bool :=
  decide (p.2.length = p.1.1) &&
    (checkConsStep^[(List.replicate (bitEncode p.1.2).length false).length]
      ((p.1.1, p.2), (p.1.2, true))).2.2

private theorem checkLP_iff (n : ℕ) (cons : List (List ℚ × ℚ)) (y : List ℚ)
    (hrows : ∀ r ∈ cons, r.1.length = n) :
    checkLP ((n, cons), y) = true ↔
      y.length = n ∧
      ∀ r ∈ cons, (∑ j : Fin n, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2 := by
  dsimp only [checkLP]
  rw [List.length_replicate, Bool.and_eq_true, decide_eq_true_eq,
    (checkConsStep_spec (bitEncode cons).length n y cons true).2.2 (list_len_le_bitEncode cons)]
  simp only [true_and]
  constructor
  · rintro ⟨hy, hall⟩
    refine ⟨hy, fun r hr => ?_⟩
    obtain ⟨hrlen, hdot⟩ := hall r hr
    rwa [← zipDot_eq_fin_sum n r.1 y hrlen hy]
  · rintro ⟨hy, hall⟩
    refine ⟨hy, fun r hr => ⟨hrows r hr, ?_⟩⟩
    rw [zipDot_eq_fin_sum n r.1 y (hrows r hr) hy]
    exact hall r hr

private theorem isPolyTime_checkLP : IsPolyTime checkLP := by
  have hstep : IsPolyTime checkConsStep := by
    have hid : IsPolyTime (id : (ℕ × List ℚ) × (List (List ℚ × ℚ) × Bool) → _) := isPolyTime_id
    have hu := isPolyTime_seq (pt_fst (pt_snd hid)) (isPolyTime_listUncons (([], (0 : ℚ))))
    have hr := pt_fst (pt_snd hu)
    have hlen_eq := pt_eq (isPolyTime_seq (pt_fst hr) (isPolyTime_listLen (0 : ℚ)))
      (pt_fst (pt_fst hid))
    have hrow_ok := isPolyTime_seq (isPolyTime_pair hr (pt_snd (pt_fst hid))) isPolyTime_checkRow
    have hacc' := pt_and (pt_snd (pt_snd hid)) (pt_and hlen_eq hrow_ok)
    exact isPolyTime_ite (pt_fst hu)
      (isPolyTime_pair (pt_fst hid) (isPolyTime_pair (pt_snd (pt_snd hu)) hacc'))
      hid
  have hiter : IsPolyTime (fun q : List Bool × ((ℕ × List ℚ) × (List (List ℚ × ℚ) × Bool)) =>
      checkConsStep^[q.1.length] q.2) := by
    refine isPolyTime_iter checkConsStep hstep (4 * Polynomial.X + 8)
      (fun u ⟨⟨n, y⟩, ⟨cons, acc⟩⟩ k _ => ?_)
    set st := checkConsStep^[k] ((n, y), (cons, acc))
    obtain ⟨h1, h2, _⟩ := checkConsStep_spec k n y cons acc
    have h1' : st.1 = (n, y) := h1
    have h2' : (bitEncode st.2.1).length ≤ (bitEncode cons).length := h2
    have hL : (bitEncode (u, ((n, y), (cons, acc)))).length =
        2 * (3 * u.length) + 1 + (2 * (bitEncode (n, y)).length + 1 +
          (2 * (bitEncode cons).length + 1 + 1)) := by
      rw [bitEncode_pair_len u ((n, y), (cons, acc)), bitEncode_pair_len (n, y) (cons, acc),
        bitEncode_pair_len cons acc, bitEncode_listBool_length, bitEncode_bool_len]
    have hst_len : (bitEncode st).length =
        2 * (bitEncode st.1).length + 1 + (2 * (bitEncode st.2.1).length + 1 + 1) := by
      rw [bitEncode_pair_len st.1 st.2, bitEncode_pair_len st.2.1 st.2.2, bitEncode_bool_len]
    change (bitEncode st).length ≤ _
    rw [hst_len, h1']
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  have hid : IsPolyTime (id : (ℕ × List (List ℚ × ℚ)) × List ℚ → _) := isPolyTime_id
  have hylen := pt_eq (isPolyTime_seq (pt_snd hid) (isPolyTime_listLen (0 : ℚ)))
    (pt_fst (pt_fst hid))
  have hprep : IsPolyTime (fun p : (ℕ × List (List ℚ × ℚ)) × List ℚ =>
      (List.replicate (bitEncode p.1.2).length false, ((p.1.1, p.2), (p.1.2, true)))) :=
    isPolyTime_pair (isPolyTime_seq (pt_snd (pt_fst hid)) isPolyTime_unaryLen)
      (isPolyTime_pair (isPolyTime_pair (pt_fst (pt_fst hid)) (pt_snd hid))
        (isPolyTime_pair (pt_snd (pt_fst hid)) (isPolyTime_const true)))
  exact pt_and hylen (pt_snd (pt_snd (isPolyTime_seq hprep hiter)))


/- ## Section 5: Run-Length Weight Table, Quantiles, and Interval Doubling -/

private def totalLen : List (ℕ × ℕ) → ℕ
  | [] => 0
  | r :: rs => r.1 + totalLen rs

private def totalWt : List (ℕ × ℕ) → ℕ
  | [] => 0
  | r :: rs => r.1 * r.2 + totalWt rs

private def maxWt : List (ℕ × ℕ) → ℕ
  | [] => 0
  | r :: rs => max r.2 (maxWt rs)

private def wtAt : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | r :: rs, z => if z < r.1 then r.2 else wtAt rs (z - r.1)

private def cumWt (runs : List (ℕ × ℕ)) (z : ℕ) : ℕ :=
  ∑ u ∈ Finset.range z, wtAt runs u

private def wtInterval (runs : List (ℕ × ℕ)) (lo hi : ℕ) : ℕ :=
  ∑ u ∈ Finset.Ico lo hi, wtAt runs u

private theorem cumWt_zero (runs : List (ℕ × ℕ)) : cumWt runs 0 = 0 := by
  simp [cumWt]

private theorem cumWt_succ (runs : List (ℕ × ℕ)) (z : ℕ) :
    cumWt runs (z + 1) = cumWt runs z + wtAt runs z := by
  simp [cumWt, Finset.sum_range_succ]

private theorem cumWt_mono (runs : List (ℕ × ℕ)) {a b : ℕ} (h : a ≤ b) :
    cumWt runs a ≤ cumWt runs b :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

private theorem cumWt_add_wtInterval (runs : List (ℕ × ℕ)) {lo hi : ℕ} (h : lo ≤ hi) :
    cumWt runs hi = cumWt runs lo + wtInterval runs lo hi := by
  unfold cumWt wtInterval
  rw [← Finset.sum_union]
  · congr 1; ext u
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  · rw [Finset.disjoint_left]
    intro u hu1 hu2
    simp only [Finset.mem_range] at hu1
    simp only [Finset.mem_Ico] at hu2; omega

private theorem cumWt_cons_le (r : ℕ × ℕ) (rs : List (ℕ × ℕ)) :
    ∀ z ≤ r.1, cumWt (r :: rs) z = z * r.2
  | 0, _ => by simp [cumWt]
  | z + 1, hz => by
    rw [cumWt_succ, cumWt_cons_le r rs z (by omega), wtAt, if_pos (by omega)]
    ring

private theorem cumWt_cons_ge (r : ℕ × ℕ) (rs : List (ℕ × ℕ)) (z : ℕ) (hz : r.1 ≤ z) :
    cumWt (r :: rs) z = r.1 * r.2 + cumWt rs (z - r.1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hz
  clear hz
  rw [Nat.add_sub_cancel_left]
  induction d with
  | zero => simp [cumWt_cons_le r rs r.1 le_rfl, cumWt_zero]
  | succ d ih =>
    rw [show r.1 + (d + 1) = (r.1 + d) + 1 by omega, cumWt_succ, ih, cumWt_succ, wtAt,
      if_neg (by omega), Nat.add_sub_cancel_left, Nat.add_assoc]

private theorem cumWt_totalLen : ∀ runs : List (ℕ × ℕ), cumWt runs (totalLen runs) = totalWt runs
  | [] => by simp [totalLen, totalWt, cumWt]
  | r :: rs => by
    rw [totalLen, totalWt, cumWt_cons_ge r rs (r.1 + totalLen rs) (by omega),
      Nat.add_sub_cancel_left, cumWt_totalLen rs]

private theorem wtAt_le_totalWt (runs : List (ℕ × ℕ)) (z : ℕ) :
    wtAt runs z ≤ totalWt runs := by
  induction runs generalizing z with
  | nil => simp [wtAt, totalWt]
  | cons r rs ih =>
    simp only [wtAt, totalWt]
    split_ifs with h
    · have h1 : 1 * r.2 ≤ r.1 * r.2 := Nat.mul_le_mul_right r.2 (by omega)
      omega
    · have := ih (z - r.1); omega

private theorem totalLen_le_totalWt : ∀ runs : List (ℕ × ℕ),
    (∀ r ∈ runs, 1 ≤ r.2) → totalLen runs ≤ totalWt runs
  | [], _ => le_rfl
  | r :: rs, h => by
    simp only [totalLen, totalWt]
    have hr : 1 ≤ r.2 := h r (List.mem_cons_self ..)
    have hrs := totalLen_le_totalWt rs (fun x hx => h x (List.mem_cons_of_mem r hx))
    have hmul : r.1 ≤ r.1 * r.2 := Nat.le_mul_of_pos_right r.1 hr
    omega

private theorem totalLen_lt_pow : ∀ runs : List (ℕ × ℕ),
    totalLen runs < 2 ^ ((bitEncode runs).length + 1)
  | [] => by simp [totalLen, bitEncode_list_nil]
  | (len, wt) :: rs => by
    rw [totalLen, bitEncode_list_cons_len, bitEncode_pair_len]
    have h1 := lt_two_pow_bitEncode_nat len
    have h2 := totalLen_lt_pow rs
    set E := 2 * (2 * (bitEncode len).length + 1 + (bitEncode wt).length) + (bitEncode rs).length + 1
    have hp1 : 2 ^ (bitEncode len).length ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
    have hp2 : 2 ^ ((bitEncode rs).length + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
    have hE : 2 * (2 * (bitEncode len).length + 1 + (bitEncode wt).length) + 1 +
        (bitEncode rs).length + 1 = E + 1 := by omega
    rw [hE, pow_succ]; omega

private theorem totalWt_lt_pow : ∀ runs : List (ℕ × ℕ),
    totalWt runs < 2 ^ ((bitEncode runs).length + 1)
  | [] => by simp [totalWt, bitEncode_list_nil]
  | (len, wt) :: rs => by
    rw [totalWt, bitEncode_list_cons_len, bitEncode_pair_len]
    have h1 : len * wt < 2 ^ ((bitEncode len).length + (bitEncode wt).length) := by
      rw [pow_add]; exact Nat.mul_lt_mul'' (lt_two_pow_bitEncode_nat len) (lt_two_pow_bitEncode_nat wt)
    have h2 := totalWt_lt_pow rs
    set E := 2 * (2 * (bitEncode len).length + 1 + (bitEncode wt).length) + (bitEncode rs).length + 1
    have hp1 : 2 ^ ((bitEncode len).length + (bitEncode wt).length) ≤ 2 ^ E :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hp2 : 2 ^ ((bitEncode rs).length + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
    have hE : 2 * (2 * (bitEncode len).length + 1 + (bitEncode wt).length) + 1 +
        (bitEncode rs).length + 1 = E + 1 := by omega
    rw [hE, pow_succ]; dsimp only; omega

private theorem maxWt_lt_pow : ∀ runs : List (ℕ × ℕ),
    maxWt runs < 2 ^ ((bitEncode runs).length + 1)
  | [] => by simp [maxWt, bitEncode_list_nil]
  | (len, wt) :: rs => by
    rw [maxWt, bitEncode_list_cons_len, bitEncode_pair_len]
    have h1 := lt_two_pow_bitEncode_nat wt
    have h2 := maxWt_lt_pow rs
    set E := 2 * (2 * (bitEncode len).length + 1 + (bitEncode wt).length) + 1 +
      (bitEncode rs).length + 1
    have hp1 : 2 ^ (bitEncode wt).length ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
    have hp2 : 2 ^ ((bitEncode rs).length + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
    exact max_lt (lt_of_lt_of_le h1 hp1) (lt_of_lt_of_le h2 hp2)

private theorem run_le_totalLen : ∀ {r : ℕ × ℕ} {runs : List (ℕ × ℕ)},
    r ∈ runs → r.1 ≤ totalLen runs
  | _, [], h => by cases h
  | r, x :: rs, h => by
    simp only [totalLen]
    rcases List.mem_cons.mp h with rfl | h'
    · omega
    · have := run_le_totalLen h'; omega

private theorem run_le_maxWt : ∀ {r : ℕ × ℕ} {runs : List (ℕ × ℕ)},
    r ∈ runs → r.2 ≤ maxWt runs
  | _, [], h => by cases h
  | r, x :: rs, h => by
    simp only [maxWt]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (run_le_maxWt h') (le_max_right _ _)

/- ### `IsPolyTime` Total Weight (`totalWt`) -/

private def totalWtStep (p : List (ℕ × ℕ) × ℕ) : List (ℕ × ℕ) × ℕ :=
  let u := listUncons (0, 0) p.1
  if u.1 then (u.2.2, p.2 + u.2.1.1 * u.2.1.2) else p

private theorem totalWtStep_spec : ∀ (k : ℕ) (runs : List (ℕ × ℕ)) (acc : ℕ),
    let st := totalWtStep^[k] (runs, acc)
    (bitEncode st.1).length ≤ (bitEncode runs).length ∧
    st.2 + totalWt st.1 = acc + totalWt runs ∧
    (runs.length ≤ k → st.2 = acc + totalWt runs)
  | 0, runs, acc => by
    dsimp only
    refine ⟨le_rfl, rfl, fun h => ?_⟩
    cases runs with
    | nil => simp [totalWt]
    | cons _ _ => simp at h
  | k + 1, runs, acc => by
    dsimp only
    rw [Function.iterate_succ_apply]
    cases runs with
    | nil =>
      have hst : totalWtStep ([], acc) = ([], acc) := rfl
      rw [hst]
      have h := totalWtStep_spec k [] acc
      exact ⟨h.1, h.2.1, fun _ => h.2.2 (Nat.zero_le _)⟩
    | cons r rs =>
      have hst : totalWtStep (r :: rs, acc) = (rs, acc + r.1 * r.2) := rfl
      rw [hst]
      have h := totalWtStep_spec k rs (acc + r.1 * r.2)
      refine ⟨le_trans h.1 (by rw [bitEncode_list_cons_len]; omega),
        by simp only [totalWt]; omega, fun hk => ?_⟩
      rw [h.2.2 (by simp at hk; omega), totalWt]; omega

private theorem isPolyTime_totalWt : IsPolyTime totalWt := by
  have hstep : IsPolyTime totalWtStep := by
    have hid : IsPolyTime (id : List (ℕ × ℕ) × ℕ → _) := isPolyTime_id
    have hu := isPolyTime_seq (pt_fst hid) (isPolyTime_listUncons (0, 0))
    have hr := pt_fst (pt_snd hu)
    have hadd := pt_add (pt_snd hid) (pt_mul (pt_fst hr) (pt_snd hr))
    exact isPolyTime_ite (pt_fst hu) (isPolyTime_pair (pt_snd (pt_snd hu)) hadd) hid
  have hiter : IsPolyTime (fun q : List Bool × (List (ℕ × ℕ) × ℕ) => totalWtStep^[q.1.length] q.2) := by
    refine isPolyTime_iter totalWtStep hstep (6 * Polynomial.X + 10) (fun u ⟨runs, acc⟩ k _ => ?_)
    set st := totalWtStep^[k] (runs, acc)
    obtain ⟨h1, h2, _⟩ := totalWtStep_spec k runs acc
    have h1' : (bitEncode st.1).length ≤ (bitEncode runs).length := h1
    have h2' : st.2 + totalWt st.1 = acc + totalWt runs := h2
    have hacc_lt : st.2 < 2 ^ ((bitEncode acc).length + (bitEncode runs).length + 2) := by
      have ha := lt_two_pow_bitEncode_nat acc
      have hr := totalWt_lt_pow runs
      set E := (bitEncode acc).length + (bitEncode runs).length + 1
      have hp1 : 2 ^ (bitEncode acc).length ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      have hp2 : 2 ^ ((bitEncode runs).length + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      rw [show (bitEncode acc).length + (bitEncode runs).length + 2 = E + 1 by omega, pow_succ]
      omega
    have hacc_len : (bitEncode st.2).length ≤ (bitEncode acc).length + (bitEncode runs).length + 2 :=
      length_encodeNat_le hacc_lt
    have hL : (bitEncode (u, (runs, acc))).length =
        2 * (3 * u.length) + 1 + (2 * (bitEncode runs).length + 1 + (bitEncode acc).length) := by
      rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_listBool_length]
    have hst_len : (bitEncode st).length = 2 * (bitEncode st.1).length + 1 + (bitEncode st.2).length :=
      bitEncode_pair_len st.1 st.2
    change (bitEncode st).length ≤ _
    rw [hst_len]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  have hfn : totalWt =
      fun runs => (totalWtStep^[(List.replicate (bitEncode runs).length false).length] (runs, 0)).2 := by
    funext runs
    rw [List.length_replicate,
      (totalWtStep_spec (bitEncode runs).length runs 0).2.2 (list_len_le_bitEncode runs), zero_add]
  rw [hfn]
  have hprep : IsPolyTime (fun runs : List (ℕ × ℕ) =>
      (List.replicate (bitEncode runs).length false, (runs, (0 : ℕ)))) :=
    isPolyTime_pair isPolyTime_unaryLen (isPolyTime_pair isPolyTime_id (isPolyTime_const 0))
  exact pt_snd (isPolyTime_seq hprep hiter)

/- ### Quantile Selection (`findQuantile`, `cellQuantiles`, `tableQuantiles`) -/

private abbrev FQState : Type := (ℕ × ℕ) × (List (ℕ × ℕ) × ((ℕ × ℕ) × (Bool × ℕ)))

private def fqStep (st : FQState) : FQState :=
  let u := listUncons (0, 0) st.2.1
  if (!st.2.2.2.1) && u.1 then
    let nextCum := st.2.2.1.2 + u.2.1.1 * u.2.1.2
    if decide (st.1.1 * nextCum < st.1.2) then
      (st.1, (u.2.2, ((st.2.2.1.1 + u.2.1.1, nextCum), (false, st.2.2.2.2))))
    else
      let d := ((st.1.2 - st.1.1 * st.2.2.1.2) - 1) / (st.1.1 * u.2.1.2)
      (st.1, (u.2.2, (st.2.2.1, (true, st.2.2.1.1 + d))))
  else st

private theorem fqStep_bound : ∀ (k : ℕ) (J T : ℕ) (runs : List (ℕ × ℕ)) (pos prevCum : ℕ)
    (found : Bool) (res : ℕ),
    let st := fqStep^[k] ((J, T), (runs, ((pos, prevCum), (found, res))))
    st.1 = (J, T) ∧
    (bitEncode st.2.1).length ≤ (bitEncode runs).length ∧
    st.2.2.1.1 ≤ pos + totalLen runs ∧
    st.2.2.1.2 ≤ prevCum + totalWt runs ∧
    st.2.2.2.2 ≤ max res (pos + totalLen runs + T)
  | 0, J, T, runs, pos, prevCum, found, res => by
    simp only [Function.iterate_zero_apply]
    exact ⟨trivial, le_rfl, by omega, by omega, le_max_left _ _⟩
  | k + 1, J, T, runs, pos, prevCum, found, res => by
    dsimp only
    rw [Function.iterate_succ_apply]
    cases found with
    | true =>
      have hst : fqStep ((J, T), (runs, ((pos, prevCum), (true, res)))) =
          ((J, T), (runs, ((pos, prevCum), (true, res)))) := rfl
      rw [hst]
      exact fqStep_bound k J T runs pos prevCum true res
    | false =>
      cases runs with
      | nil =>
        have hst : fqStep ((J, T), ([], ((pos, prevCum), (false, res)))) =
            ((J, T), ([], ((pos, prevCum), (false, res)))) := rfl
        rw [hst]
        exact fqStep_bound k J T [] pos prevCum false res
      | cons r rs =>
        have hst : fqStep ((J, T), (r :: rs, ((pos, prevCum), (false, res)))) =
            if decide (J * (prevCum + r.1 * r.2) < T) then
              ((J, T), (rs, ((pos + r.1, prevCum + r.1 * r.2), (false, res))))
            else
              ((J, T), (rs, ((pos, prevCum), (true, pos + ((T - J * prevCum) - 1) / (J * r.2))))) := rfl
        rw [hst]
        by_cases hlt : J * (prevCum + r.1 * r.2) < T
        · rw [if_pos (decide_eq_true hlt)]
          have h := fqStep_bound k J T rs (pos + r.1) (prevCum + r.1 * r.2) false res
          refine ⟨h.1, le_trans h.2.1 (by rw [bitEncode_list_cons_len]; omega),
            by simp only [totalLen]; omega, by simp only [totalWt]; omega, ?_⟩
          simp only [totalLen] at h ⊢
          have hmax : max res (pos + r.1 + totalLen rs + T) = max res (pos + (r.1 + totalLen rs) + T) := by
            congr 1; omega
          rw [← hmax]; exact h.2.2.2.2
        · rw [if_neg (by rw [decide_eq_false hlt]; exact Bool.false_ne_true)]
          set d := (T - J * prevCum - 1) / (J * r.2)
          have hd_le : d ≤ T := le_trans (Nat.div_le_self _ _) (by omega)
          have h := fqStep_bound k J T rs pos prevCum true (pos + d)
          refine ⟨h.1, le_trans h.2.1 (by rw [bitEncode_list_cons_len]; omega),
            by simp only [totalLen]; omega, by simp only [totalWt]; omega, ?_⟩
          have h1 : pos + d ≤ pos + (r.1 + totalLen rs) + T := by omega
          have h2 : pos + totalLen rs + T ≤ pos + (r.1 + totalLen rs) + T := by omega
          have h3 : max (pos + d) (pos + totalLen rs + T) ≤ max res (pos + (r.1 + totalLen rs) + T) :=
            max_le (le_trans h1 (le_max_right _ _)) (le_trans h2 (le_max_right _ _))
          exact le_trans h.2.2.2.2 (by simpa [totalLen] using h3)

private theorem fqStep_true_noop : ∀ (k : ℕ) (J T : ℕ) (runs : List (ℕ × ℕ)) (pos prevCum res : ℕ),
    fqStep^[k] ((J, T), (runs, ((pos, prevCum), (true, res)))) =
      ((J, T), (runs, ((pos, prevCum), (true, res))))
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, J, T, runs, pos, prevCum, res => by
    rw [Function.iterate_succ_apply]
    have hst : fqStep ((J, T), (runs, ((pos, prevCum), (true, res)))) =
        ((J, T), (runs, ((pos, prevCum), (true, res)))) := rfl
    rw [hst]
    exact fqStep_true_noop k J T runs pos prevCum res

private theorem fqStep_correct : ∀ (k : ℕ) (J T : ℕ) (runs : List (ℕ × ℕ)) (pos prevCum : ℕ),
    runs.length ≤ k →
    1 ≤ J →
    (∀ r ∈ runs, 1 ≤ r.2) →
    J * prevCum < T →
    T ≤ J * (prevCum + totalWt runs) →
    ∃ z < totalLen runs,
      (fqStep^[k] ((J, T), (runs, ((pos, prevCum), (false, 0))))).2.2.2 = (true, pos + z) ∧
      J * (prevCum + cumWt runs z) < T ∧
      T ≤ J * (prevCum + cumWt runs (z + 1))
  | 0, _, _, runs, _, _, hlen, _, _, hlo, hhi => by
    cases runs with
    | nil => simp [totalWt] at hhi; omega
    | cons _ _ => simp at hlen
  | k + 1, J, T, runs, pos, prevCum, hlen, hJ, hwt, hlo, hhi => by
    cases runs with
    | nil => simp [totalWt] at hhi; omega
    | cons r rs =>
      rw [Function.iterate_succ_apply]
      have hst : fqStep ((J, T), (r :: rs, ((pos, prevCum), (false, 0)))) =
          if decide (J * (prevCum + r.1 * r.2) < T) then
            ((J, T), (rs, ((pos + r.1, prevCum + r.1 * r.2), (false, 0))))
          else
            ((J, T), (rs, ((pos, prevCum), (true, pos + ((T - J * prevCum) - 1) / (J * r.2))))) := rfl
      rw [hst]
      by_cases hlt : J * (prevCum + r.1 * r.2) < T
      · rw [if_pos (decide_eq_true hlt)]
        have hhi' : T ≤ J * (prevCum + r.1 * r.2 + totalWt rs) := by
          simp only [totalWt] at hhi; ring_nf at hhi ⊢; exact hhi
        obtain ⟨z', hz', heq, hlo', hhi''⟩ := fqStep_correct k J T rs (pos + r.1)
          (prevCum + r.1 * r.2) (by simp at hlen; omega) hJ
          (fun x hx => hwt x (List.mem_cons_of_mem r hx)) hlt hhi'
        refine ⟨r.1 + z', by simp only [totalLen]; omega, ?_, ?_, ?_⟩
        · rw [heq]; congr 1; omega
        · rw [cumWt_cons_ge r rs (r.1 + z') (by omega), Nat.add_sub_cancel_left]
          simpa [Nat.add_assoc] using hlo'
        · rw [cumWt_cons_ge r rs (r.1 + z' + 1) (by omega),
            show r.1 + z' + 1 - r.1 = z' + 1 by omega]
          simpa [Nat.add_assoc] using hhi''
      · rw [if_neg (by rw [decide_eq_false hlt]; exact Bool.false_ne_true)]
        rw [fqStep_true_noop]
        have hr2 : 1 ≤ r.2 := hwt r (List.mem_cons_self ..)
        have hstep_pos : 0 < J * r.2 := Nat.mul_pos hJ hr2
        have hrem_pos : 1 ≤ T - J * prevCum := by omega
        have hrem_le : T - J * prevCum ≤ r.1 * (J * r.2) := by
          have h1 : T ≤ J * (prevCum + r.1 * r.2) := by omega
          have h2 : J * (prevCum + r.1 * r.2) = J * prevCum + r.1 * (J * r.2) := by ring
          omega
        set d := (T - J * prevCum - 1) / (J * r.2)
        have hd_lt : d < r.1 := by
          apply Nat.div_lt_of_lt_mul
          have hcomm : r.1 * (J * r.2) = (J * r.2) * r.1 := mul_comm _ _
          omega
        have hd_lo : d * (J * r.2) ≤ T - J * prevCum - 1 := Nat.div_mul_le_self _ _
        have hd_hi : T - J * prevCum - 1 < (d + 1) * (J * r.2) := by
          rw [mul_comm (d + 1) (J * r.2)]
          exact Nat.lt_mul_div_succ (T - J * prevCum - 1) hstep_pos
        refine ⟨d, by simp only [totalLen]; omega, rfl, ?_, ?_⟩
        · rw [cumWt_cons_le r rs d (by omega)]
          have : J * (prevCum + d * r.2) = J * prevCum + d * (J * r.2) := by ring
          omega
        · rw [cumWt_cons_le r rs (d + 1) (by omega)]
          have : J * (prevCum + (d + 1) * r.2) = J * prevCum + (d + 1) * (J * r.2) := by ring
          omega

private def findQuantile (p : (ℕ × ℕ) × List (ℕ × ℕ)) : ℕ :=
  (fqStep^[(List.replicate (bitEncode p.2).length false).length]
    (p.1, (p.2, ((0, 0), (false, 0))))).2.2.2.2

private theorem findQuantile_le (J T : ℕ) (runs : List (ℕ × ℕ)) :
    findQuantile ((J, T), runs) ≤ totalLen runs + T := by
  dsimp only [findQuantile]
  have h := (fqStep_bound (List.replicate (bitEncode runs).length false).length J T runs 0 0 false 0).2.2.2.2
  simpa using h

private theorem findQuantile_spec (J r : ℕ) (runs : List (ℕ × ℕ))
    (hJ : 1 ≤ J) (hr1 : 1 ≤ r) (hr2 : r < J)
    (hwt : ∀ x ∈ runs, 1 ≤ x.2) (hlen : 1 ≤ totalLen runs) :
    let M := totalWt runs
    let z := findQuantile ((J, r * M), runs)
    z < totalLen runs ∧ J * cumWt runs z < r * M ∧ r * M ≤ J * cumWt runs (z + 1) := by
  dsimp only [findQuantile]
  rw [List.length_replicate]
  have hM : 1 ≤ totalWt runs := le_trans hlen (totalLen_le_totalWt runs hwt)
  have hlo : J * 0 < r * totalWt runs := by
    simp only [mul_zero]; exact Nat.mul_pos hr1 hM
  have hhi : r * totalWt runs ≤ J * (0 + totalWt runs) := by
    rw [zero_add]; exact Nat.mul_le_mul_right _ (by omega)
  obtain ⟨z, hz, heq, h1, h2⟩ := fqStep_correct (bitEncode runs).length J (r * totalWt runs)
    runs 0 0 (list_len_le_bitEncode runs) hJ hwt hlo hhi
  have hz_eq : (fqStep^[(bitEncode runs).length] ((J, r * totalWt runs), (runs, ((0, 0), (false, 0))))).2.2.2.2 = z := by
    rw [heq]; simp
  rw [hz_eq]
  exact ⟨hz, by simpa using h1, by simpa using h2⟩

private theorem isPolyTime_findQuantile : IsPolyTime findQuantile := by
  have hstep : IsPolyTime fqStep := by
    have hid : IsPolyTime (id : FQState → FQState) := isPolyTime_id
    have hJ := pt_fst (pt_fst hid)
    have hT := pt_snd (pt_fst hid)
    have hu := isPolyTime_seq (pt_fst (pt_snd hid)) (isPolyTime_listUncons (0, 0))
    have hrem' := pt_snd (pt_snd hu)
    have hr := pt_fst (pt_snd hu)
    have hr1 := pt_fst hr
    have hr2 := pt_snd hr
    have hpos := pt_fst (pt_fst (pt_snd (pt_snd hid)))
    have hcum := pt_snd (pt_fst (pt_snd (pt_snd hid)))
    have hfound := pt_fst (pt_snd (pt_snd (pt_snd hid)))
    have hres := pt_snd (pt_snd (pt_snd (pt_snd hid)))
    have hcond1 := pt_and (pt_not hfound) (pt_fst hu)
    have hnextCum := pt_add hcum (pt_mul hr1 hr2)
    have hcond2 := pt_lt (pt_mul hJ hnextCum) hT
    have hbrT := isPolyTime_pair (pt_fst hid)
      (isPolyTime_pair hrem' (isPolyTime_pair (isPolyTime_pair (pt_add hpos hr1) hnextCum)
        (isPolyTime_pair (isPolyTime_const false) hres)))
    have hnum := pt_sub (pt_sub hT (pt_mul hJ hcum)) (isPolyTime_const 1)
    have hd := pt_div hnum (pt_mul hJ hr2)
    have hbrF := isPolyTime_pair (pt_fst hid)
      (isPolyTime_pair hrem' (isPolyTime_pair (pt_fst (pt_snd (pt_snd hid)))
        (isPolyTime_pair (isPolyTime_const true) (pt_add hpos hd))))
    exact isPolyTime_ite hcond1 (isPolyTime_ite hcond2 hbrT hbrF) hid
  have hiter : IsPolyTime (fun q : List Bool × FQState => fqStep^[q.1.length] q.2) := by
    refine isPolyTime_iter fqStep hstep (40 * Polynomial.X + 80)
      (fun u ⟨⟨J, T⟩, ⟨runs, ⟨⟨pos, prevCum⟩, ⟨found, res⟩⟩⟩⟩ k _ => ?_)
    set st := fqStep^[k] ((J, T), (runs, ((pos, prevCum), (found, res))))
    obtain ⟨h1, h2, h3, h4, h5⟩ := fqStep_bound k J T runs pos prevCum found res
    have h1' : st.1 = (J, T) := h1
    have h2' : (bitEncode st.2.1).length ≤ (bitEncode runs).length := h2
    have h3' : st.2.2.1.1 ≤ pos + totalLen runs := h3
    have h4' : st.2.2.1.2 ≤ prevCum + totalWt runs := h4
    have h5' : st.2.2.2.2 ≤ max res (pos + totalLen runs + T) := h5
    have hpos_len : (bitEncode st.2.2.1.1).length ≤ (bitEncode pos).length + (bitEncode runs).length + 2 := by
      have hp := lt_two_pow_bitEncode_nat pos
      have hr := totalLen_lt_pow runs
      set E := (bitEncode pos).length + (bitEncode runs).length + 1
      have e1 : 2 ^ (bitEncode pos).length ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      have e2 : 2 ^ ((bitEncode runs).length + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      exact length_encodeNat_le (by rw [show (bitEncode pos).length + (bitEncode runs).length + 2 = E + 1 by omega, pow_succ]; omega)
    have hcum_len : (bitEncode st.2.2.1.2).length ≤ (bitEncode prevCum).length + (bitEncode runs).length + 2 := by
      have hc := lt_two_pow_bitEncode_nat prevCum
      have hr := totalWt_lt_pow runs
      set E := (bitEncode prevCum).length + (bitEncode runs).length + 1
      have e1 : 2 ^ (bitEncode prevCum).length ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      have e2 : 2 ^ ((bitEncode runs).length + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      exact length_encodeNat_le (by rw [show (bitEncode prevCum).length + (bitEncode runs).length + 2 = E + 1 by omega, pow_succ]; omega)
    have hres_len : (bitEncode st.2.2.2.2).length ≤
        (bitEncode res).length + (bitEncode pos).length + (bitEncode runs).length + (bitEncode T).length + 3 := by
      have hres_lt := lt_two_pow_bitEncode_nat res
      have hpos_lt := lt_two_pow_bitEncode_nat pos
      have hrun_lt := totalLen_lt_pow runs
      have hT_lt := lt_two_pow_bitEncode_nat T
      set E := (bitEncode res).length + (bitEncode pos).length + (bitEncode runs).length + (bitEncode T).length + 1
      have e1 : 2 ^ (bitEncode res).length ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      have e2 : 2 ^ (bitEncode pos).length ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      have e3 : 2 ^ ((bitEncode runs).length + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      have e4 : 2 ^ (bitEncode T).length ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      have hlt : st.2.2.2.2 < 2 ^ (E + 2) := by
        rw [pow_add]
        have : max res (pos + totalLen runs + T) < 4 * 2 ^ E := max_lt (by omega) (by omega)
        omega
      exact length_encodeNat_le (by simpa [E, Nat.add_assoc] using hlt)
    have hL : (bitEncode (u, ((J, T), (runs, ((pos, prevCum), (found, res)))))).length =
        2 * (3 * u.length) + 1 +
          (2 * (2 * (bitEncode J).length + 1 + (bitEncode T).length) + 1 +
            (2 * (bitEncode runs).length + 1 +
              (2 * (2 * (bitEncode pos).length + 1 + (bitEncode prevCum).length) + 1 +
                (2 * 1 + 1 + (bitEncode res).length)))) := by
      rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len,
        bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len, bitEncode_listBool_length,
        bitEncode_bool_len]
    have hst_len : (bitEncode st).length =
        2 * (bitEncode st.1).length + 1 +
          (2 * (bitEncode st.2.1).length + 1 +
            (2 * (2 * (bitEncode st.2.2.1.1).length + 1 + (bitEncode st.2.2.1.2).length) + 1 +
              (2 * 1 + 1 + (bitEncode st.2.2.2.2).length))) := by
      rw [bitEncode_pair_len st.1 st.2, bitEncode_pair_len st.2.1 st.2.2,
        bitEncode_pair_len st.2.2.1 st.2.2.2, bitEncode_pair_len st.2.2.1.1 st.2.2.1.2,
        bitEncode_pair_len st.2.2.2.1 st.2.2.2.2, bitEncode_bool_len]
    change (bitEncode st).length ≤ _
    rw [hst_len, h1', bitEncode_pair_len J T]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  have hprep : IsPolyTime (fun p : (ℕ × ℕ) × List (ℕ × ℕ) =>
      (List.replicate (bitEncode p.2).length false, (p.1, (p.2, (((0, 0), (false, 0))))))) :=
    isPolyTime_pair (isPolyTime_seq isPolyTime_snd isPolyTime_unaryLen)
      (isPolyTime_pair isPolyTime_fst
        (isPolyTime_pair isPolyTime_snd (isPolyTime_const ((0, 0), (false, 0)))))
  exact pt_snd (pt_snd (pt_snd (pt_snd (isPolyTime_seq hprep hiter))))

private abbrev CQState : Type := ((ℕ × ℕ) × List (ℕ × ℕ)) × (ℕ × List ℕ)

private def cqStep (st : CQState) : CQState :=
  (st.1, (st.2.1 + 1, findQuantile ((st.1.1.1, st.2.1 * st.1.1.2), st.1.2) :: st.2.2))

private theorem cqStep_spec : ∀ (k : ℕ) (J M : ℕ) (runs : List (ℕ × ℕ)) (r : ℕ) (acc : List ℕ),
    let st := cqStep^[k] (((J, M), runs), (r, acc))
    st.1 = ((J, M), runs) ∧
    st.2.1 = r + k ∧
    (∀ t < k, findQuantile ((J, (r + t) * M), runs) ∈ st.2.2) ∧
    (bitEncode st.2.2).length ≤ (bitEncode acc).length +
      k * (2 * ((bitEncode runs).length + (bitEncode r).length + k + (bitEncode M).length + 4) + 1)
  | 0, J, M, runs, r, acc => by
    dsimp only
    exact ⟨rfl, by simp, fun _ ht => by omega, by simp⟩
  | k + 1, J, M, runs, r, acc => by
    dsimp only
    rw [Function.iterate_succ_apply]
    set z0 := findQuantile ((J, r * M), runs)
    have hst : cqStep (((J, M), runs), (r, acc)) = (((J, M), runs), (r + 1, z0 :: acc)) := rfl
    rw [hst]
    have h := cqStep_spec k J M runs (r + 1) (z0 :: acc)
    have h1 := h.1; have h2 := h.2.1; have h3 := h.2.2.1; have hstep_len := h.2.2.2
    refine ⟨h1, by omega, ?_, ?_⟩
    · intro t ht
      cases t with
      | zero =>
        have hpres : ∀ (m : ℕ) (r' : ℕ) (a : List ℕ), z0 ∈ a →
            z0 ∈ (cqStep^[m] (((J, M), runs), (r', a))).2.2 := by
          intro m; induction m with
          | zero => intro _ _ ha; exact ha
          | succ m ihm =>
            intro r' a ha
            rw [Function.iterate_succ_apply]
            exact ihm (r' + 1) _ (List.mem_cons_of_mem _ ha)
        have hp := hpres k (r + 1) (z0 :: acc) (List.mem_cons_self ..)
        simpa only [add_zero] using hp
      | succ t' =>
        have ht' := h3 t' (by omega)
        rwa [show r + 1 + t' = r + (t' + 1) by omega] at ht'
    · have hz0_le : z0 ≤ totalLen runs + r * M := findQuantile_le J (r * M) runs
      have hz0_len : (bitEncode z0).length ≤
          (bitEncode runs).length + (bitEncode r).length + (bitEncode M).length + 2 := by
        have htl := totalLen_lt_pow runs
        have hrm : r * M < 2 ^ ((bitEncode r).length + (bitEncode M).length) := by
          rw [pow_add]; exact Nat.mul_lt_mul'' (lt_two_pow_bitEncode_nat r) (lt_two_pow_bitEncode_nat M)
        set E := (bitEncode runs).length + (bitEncode r).length + (bitEncode M).length + 1
        have e1 : 2 ^ ((bitEncode runs).length + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
        have e2 : 2 ^ ((bitEncode r).length + (bitEncode M).length) ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
        exact length_encodeNat_le (by rw [show (bitEncode runs).length + (bitEncode r).length + (bitEncode M).length + 2 = E + 1 by omega, pow_succ]; omega)
      have hr1_len : (bitEncode (r + 1)).length ≤ (bitEncode r).length + 1 := by
        have hr_lt := lt_two_pow_bitEncode_nat r
        exact length_encodeNat_le (by rw [pow_succ]; omega)
      rw [bitEncode_list_cons_len] at hstep_len
      have hmono : k * (2 * ((bitEncode runs).length + (bitEncode (r + 1)).length + k + (bitEncode M).length + 4) + 1) ≤
          k * (2 * ((bitEncode runs).length + (bitEncode r).length + (k + 1) + (bitEncode M).length + 4) + 1) := by
        apply Nat.mul_le_mul_left; omega
      have hone : 2 * (bitEncode z0).length + 1 ≤
          2 * ((bitEncode runs).length + (bitEncode r).length + (k + 1) + (bitEncode M).length + 4) + 1 := by
        omega
      rw [Nat.add_mul, one_mul]
      omega

private def cellQuantiles (p : (List Bool × ℕ) × List (ℕ × ℕ)) : List ℕ :=
  (cqStep^[p.1.1.length] (((p.1.2, totalWt p.2), p.2), (1, []))).2.2

private theorem cellQuantiles_mem (uJm1 : List Bool) (J : ℕ) (runs : List (ℕ × ℕ))
    (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ uJm1.length) :
    findQuantile ((J, r * totalWt runs), runs) ∈ cellQuantiles ((uJm1, J), runs) := by
  dsimp only [cellQuantiles]
  have h := (cqStep_spec uJm1.length J (totalWt runs) runs 1 []).2.2.1 (r - 1) (by omega)
  rwa [show 1 + (r - 1) = r by omega] at h

private theorem isPolyTime_cellQuantiles : IsPolyTime cellQuantiles := by
  have hstep : IsPolyTime cqStep := by
    have hid : IsPolyTime (id : CQState → CQState) := isPolyTime_id
    have hJ := pt_fst (pt_fst (pt_fst hid))
    have hM := pt_snd (pt_fst (pt_fst hid))
    have hruns := pt_snd (pt_fst hid)
    have hr := pt_fst (pt_snd hid)
    have hacc := pt_snd (pt_snd hid)
    have hz := isPolyTime_seq (isPolyTime_pair (isPolyTime_pair hJ (pt_mul hr hM)) hruns)
      isPolyTime_findQuantile
    exact isPolyTime_pair (pt_fst hid)
      (isPolyTime_pair (pt_add hr (isPolyTime_const 1)) (pt_cons hz hacc))
  have hiter : IsPolyTime (fun q : List Bool × CQState => cqStep^[q.1.length] q.2) := by
    refine isPolyTime_iter cqStep hstep (4 * Polynomial.X * Polynomial.X + 20 * Polynomial.X + 40)
      (fun u ⟨⟨⟨J, M⟩, runs⟩, ⟨r, acc⟩⟩ k hk => ?_)
    set st := cqStep^[k] (((J, M), runs), (r, acc))
    obtain ⟨h1, h2, _, h5⟩ := cqStep_spec k J M runs r acc
    have h1' : st.1 = ((J, M), runs) := h1
    have h2' : st.2.1 = r + k := h2
    have h5' : (bitEncode st.2.2).length ≤ (bitEncode acc).length +
        k * (2 * ((bitEncode runs).length + (bitEncode r).length + k + (bitEncode M).length + 4) + 1) := h5
    have hr_len : (bitEncode st.2.1).length ≤ (bitEncode r).length + k + 1 := by
      rw [h2']
      have h1r := lt_two_pow_bitEncode_nat r
      have h2k : k < 2 ^ k := Nat.lt_two_pow_self
      set E := (bitEncode r).length + k
      have e1 : 2 ^ (bitEncode r).length ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      have e2 : 2 ^ k ≤ 2 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      exact length_encodeNat_le (by rw [show (bitEncode r).length + k + 1 = E + 1 by omega, pow_succ]; omega)
    set L := (bitEncode (u, (((J, M), runs), (r, acc)))).length
    have hL : L = 2 * (3 * u.length) + 1 +
        (2 * (2 * (2 * (bitEncode J).length + 1 + (bitEncode M).length) + 1 + (bitEncode runs).length) + 1 +
          (2 * (bitEncode r).length + 1 + (bitEncode acc).length)) := by
      dsimp only [L]
      rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len,
        bitEncode_pair_len, bitEncode_listBool_length]
    have hmul : k * (2 * ((bitEncode runs).length + (bitEncode r).length + k + (bitEncode M).length + 4) + 1) ≤
        L * (2 * L + 9) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hst_len : (bitEncode st).length =
        2 * (bitEncode st.1).length + 1 + (2 * (bitEncode st.2.1).length + 1 + (bitEncode st.2.2).length) := by
      rw [bitEncode_pair_len st.1 st.2, bitEncode_pair_len st.2.1 st.2.2]
    change (bitEncode st).length ≤ _
    rw [hst_len, h1', bitEncode_pair_len (J, M) runs, bitEncode_pair_len J M]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    have h4L : 4 * L * L = 4 * (L * L) := by ring
    have hL2 : L * (2 * L + 9) = 2 * (L * L) + 9 * L := by ring
    omega
  have hid : IsPolyTime (id : (List Bool × ℕ) × List (ℕ × ℕ) → _) := isPolyTime_id
  have hprep : IsPolyTime (fun p : (List Bool × ℕ) × List (ℕ × ℕ) =>
      (p.1.1, (((p.1.2, totalWt p.2), p.2), ((1 : ℕ), ([] : List ℕ))))) :=
    isPolyTime_pair (pt_fst (pt_fst hid))
      (isPolyTime_pair
        (isPolyTime_pair (isPolyTime_pair (pt_snd (pt_fst hid))
          (isPolyTime_seq (pt_snd hid) isPolyTime_totalWt)) (pt_snd hid))
        (isPolyTime_const (1, [])))
  exact pt_snd (pt_snd (isPolyTime_seq hprep hiter))

private def rowQuantiles (p : (List Bool × ℕ) × List (List (ℕ × ℕ))) : List (List ℕ) :=
  p.2.map (fun runs => cellQuantiles (p.1, runs))

private theorem isPolyTime_rowQuantiles : IsPolyTime rowQuantiles :=
  isPolyTime_listMap ([] : List (ℕ × ℕ)) ([] : List ℕ) cellQuantiles isPolyTime_cellQuantiles

private def tableQuantiles (p : (List Bool × ℕ) × List (List (List (ℕ × ℕ)))) :
    List (List (List ℕ)) :=
  p.2.map (fun row => rowQuantiles (p.1, row))

private theorem isPolyTime_tableQuantiles : IsPolyTime tableQuantiles :=
  isPolyTime_listMap ([] : List (List (ℕ × ℕ))) ([] : List (List ℕ)) rowQuantiles isPolyTime_rowQuantiles

/- ### Interval Doubling (`doubleRuns`, `updateTable`) -/

private def doubleRunsAux : List (ℕ × ℕ) → ℕ → ℕ → List (ℕ × ℕ)
  | [], _, _ => []
  | (len, wt) :: rs, lo, hi =>
    if hi ≤ lo then (len, wt) :: doubleRunsAux rs 0 0
    else if len ≤ lo then (len, wt) :: doubleRunsAux rs (lo - len) (hi - len)
    else
      let endIn := min len hi
      let p1 := if 0 < lo then [(lo, wt)] else []
      let p2 := [(endIn - lo, 2 * wt)]
      let p3 := if endIn < len then [(len - endIn, wt)] else []
      p1 ++ p2 ++ p3 ++ doubleRunsAux rs 0 (hi - endIn)

private theorem doubleRunsAux_noop : ∀ (runs : List (ℕ × ℕ)) (lo hi : ℕ),
    hi ≤ lo → doubleRunsAux runs lo hi = runs
  | [], _, _, _ => rfl
  | (len, wt) :: rs, lo, hi, h => by
    simp only [doubleRunsAux, h, ↓reduceIte]
    rw [doubleRunsAux_noop rs 0 0 le_rfl]

private theorem doubleRunsAux_len_zero : ∀ (runs : List (ℕ × ℕ)) (hi : ℕ),
    (doubleRunsAux runs 0 hi).length ≤ runs.length + 1
  | [], _ => by simp [doubleRunsAux]
  | (len, wt) :: rs, hi => by
    by_cases h1 : hi ≤ 0
    · simp only [doubleRunsAux, h1, ↓reduceIte, List.length_cons]
      rw [doubleRunsAux_noop rs 0 0 le_rfl]; omega
    · by_cases h2 : len ≤ 0
      · have hlen0 : len = 0 := by omega
        subst hlen0
        simp only [doubleRunsAux, h1, Nat.le_refl, ↓reduceIte, List.length_cons, Nat.sub_zero]
        have := doubleRunsAux_len_zero rs hi; omega
      · simp only [doubleRunsAux, h1, h2, ↓reduceIte, lt_self_iff_false, Nat.sub_zero]
        by_cases h3 : min len hi < len
        · have hhi : hi - min len hi = 0 := by omega
          simp only [h3, ↓reduceIte, hhi, doubleRunsAux_noop rs 0 0 le_rfl]
          simp
        · simp only [h3, ↓reduceIte, List.nil_append, List.singleton_append, List.length_cons]
          have := doubleRunsAux_len_zero rs (hi - min len hi); omega

private theorem doubleRunsAux_len : ∀ (runs : List (ℕ × ℕ)) (lo hi : ℕ),
    (doubleRunsAux runs lo hi).length ≤ runs.length + 2
  | [], _, _ => by simp [doubleRunsAux]
  | (len, wt) :: rs, lo, hi => by
    by_cases h1 : hi ≤ lo
    · simp only [doubleRunsAux, h1, ↓reduceIte, List.length_cons]
      rw [doubleRunsAux_noop rs 0 0 le_rfl]; omega
    · by_cases h2 : len ≤ lo
      · simp only [doubleRunsAux, h1, h2, ↓reduceIte, List.length_cons]
        have := doubleRunsAux_len rs (lo - len) (hi - len); omega
      · simp only [doubleRunsAux, h1, h2, ↓reduceIte]
        by_cases h3 : min len hi < len
        · have hhi : hi - min len hi = 0 := by omega
          rw [hhi, doubleRunsAux_noop rs 0 0 le_rfl]
          split_ifs <;> simp
        · simp only [h3, ↓reduceIte]
          have h0 := doubleRunsAux_len_zero rs (hi - min len hi)
          split_ifs <;> simp <;> omega

private theorem totalLen_append (a b : List (ℕ × ℕ)) :
    totalLen (a ++ b) = totalLen a + totalLen b := by
  induction a with
  | nil => simp [totalLen]
  | cons x xs ih => simp [totalLen, ih]; omega

private theorem doubleRunsAux_totalLen : ∀ (runs : List (ℕ × ℕ)) (lo hi : ℕ),
    totalLen (doubleRunsAux runs lo hi) = totalLen runs
  | [], _, _ => rfl
  | (len, wt) :: rs, lo, hi => by
    by_cases h1 : hi ≤ lo
    · simp only [doubleRunsAux, h1, ↓reduceIte, totalLen]
      rw [doubleRunsAux_noop rs 0 0 le_rfl]
    · by_cases h2 : len ≤ lo
      · simp only [doubleRunsAux, h1, h2, ↓reduceIte, totalLen]
        rw [doubleRunsAux_totalLen rs (lo - len) (hi - len)]
      · simp only [doubleRunsAux, h1, h2, ↓reduceIte]
        rw [totalLen_append, totalLen_append, totalLen_append, doubleRunsAux_totalLen]
        split_ifs <;> simp [totalLen] <;> omega

private theorem doubleRunsAux_pos_wt : ∀ (runs : List (ℕ × ℕ)) (lo hi : ℕ),
    (∀ r ∈ runs, 1 ≤ r.2) → ∀ r ∈ doubleRunsAux runs lo hi, 1 ≤ r.2
  | [], _, _, _, _, hr => by cases hr
  | (len, wt) :: rs, lo, hi, hwt, r, hr => by
    have h1 : 1 ≤ wt := hwt (len, wt) (List.mem_cons_self ..)
    have hrs : ∀ x ∈ rs, 1 ≤ x.2 := fun x hx => hwt x (List.mem_cons_of_mem _ hx)
    by_cases hc1 : hi ≤ lo
    · simp only [doubleRunsAux, hc1, ↓reduceIte, doubleRunsAux_noop rs 0 0 le_rfl] at hr
      exact hwt r hr
    · by_cases hc2 : len ≤ lo
      · simp only [doubleRunsAux, hc1, hc2, ↓reduceIte, List.mem_cons] at hr
        rcases hr with rfl | hr'
        · exact h1
        · exact doubleRunsAux_pos_wt rs (lo - len) (hi - len) hrs r hr'
      · simp only [doubleRunsAux, hc1, hc2, ↓reduceIte, List.mem_append] at hr
        rcases hr with ((hr1 | hr2) | hr3) | hr4
        · split_ifs at hr1
          · simp at hr1; subst hr1; exact h1
          · simp at hr1
        · simp at hr2; subst hr2; omega
        · split_ifs at hr3
          · simp at hr3; subst hr3; exact h1
          · simp at hr3
        · exact doubleRunsAux_pos_wt rs 0 (hi - min len hi) hrs r hr4

private theorem maxWt_append (a b : List (ℕ × ℕ)) :
    maxWt (a ++ b) = max (maxWt a) (maxWt b) := by
  induction a with
  | nil => simp [maxWt]
  | cons x xs ih => simp [maxWt, ih, max_assoc]

private theorem doubleRunsAux_maxWt : ∀ (runs : List (ℕ × ℕ)) (lo hi : ℕ),
    maxWt (doubleRunsAux runs lo hi) ≤ 2 * maxWt runs
  | [], _, _ => by simp [doubleRunsAux, maxWt]
  | (len, wt) :: rs, lo, hi => by
    by_cases hc1 : hi ≤ lo
    · simp only [doubleRunsAux, hc1, ↓reduceIte, doubleRunsAux_noop rs 0 0 le_rfl]; omega
    · by_cases hc2 : len ≤ lo
      · simp only [doubleRunsAux, hc1, hc2, ↓reduceIte, maxWt]
        have := doubleRunsAux_maxWt rs (lo - len) (hi - len); omega
      · simp only [doubleRunsAux, hc1, hc2, ↓reduceIte, maxWt_append]
        have hrec := doubleRunsAux_maxWt rs 0 (hi - min len hi)
        simp only [maxWt]
        split_ifs <;> simp [maxWt] <;> omega

private theorem wtAt_append (a b : List (ℕ × ℕ)) (z : ℕ) :
    wtAt (a ++ b) z = if z < totalLen a then wtAt a z else wtAt b (z - totalLen a) := by
  induction a generalizing z with
  | nil => simp [totalLen]
  | cons r rs ih =>
    simp only [List.cons_append, wtAt, totalLen]
    by_cases h1 : z < r.1
    · simp [h1, show z < r.1 + totalLen rs by omega]
    · simp only [h1, ↓reduceIte, ih (z - r.1)]
      by_cases h2 : z < r.1 + totalLen rs
      · simp [h2, show z - r.1 < totalLen rs by omega]
      · simp [h2, show ¬(z - r.1 < totalLen rs) by omega, Nat.sub_sub]

private theorem doubleRunsAux_wtAt : ∀ (runs : List (ℕ × ℕ)) (lo hi z : ℕ),
    wtAt (doubleRunsAux runs lo hi) z =
      if lo ≤ z ∧ z < hi then 2 * wtAt runs z else wtAt runs z
  | [], _, _, _ => by simp [doubleRunsAux, wtAt]
  | (len, wt) :: rs, lo, hi, z => by
    by_cases hc1 : hi ≤ lo
    · simp only [doubleRunsAux, hc1, ↓reduceIte, doubleRunsAux_noop rs 0 0 le_rfl]
      rw [if_neg (by omega)]
    · by_cases hc2 : len ≤ lo
      · simp only [doubleRunsAux, hc1, hc2, ↓reduceIte, wtAt]
        by_cases hz : z < len
        · simp [hz, show ¬(lo ≤ z ∧ z < hi) by omega]
        · simp only [hz, ↓reduceIte, doubleRunsAux_wtAt rs (lo - len) (hi - len) (z - len)]
          by_cases hmem : lo ≤ z ∧ z < hi
          · rw [if_pos (show lo - len ≤ z - len ∧ z - len < hi - len by omega), if_pos hmem]
          · rw [if_neg (show ¬(lo - len ≤ z - len ∧ z - len < hi - len) by omega), if_neg hmem]
      · simp only [doubleRunsAux, hc1, hc2, ↓reduceIte]
        set endIn := min len hi
        set p1 := if 0 < lo then [(lo, wt)] else []
        set p2 := [(endIn - lo, 2 * wt)]
        set p3 := if endIn < len then [(len - endIn, wt)] else []
        have htl1 : totalLen p1 = lo := by
          dsimp only [p1]; split_ifs
          · simp [totalLen]
          · simp [totalLen]; omega
        have htl2 : totalLen p2 = endIn - lo := by simp [p2, totalLen]
        have htl3 : totalLen p3 = len - endIn := by
          dsimp only [p3]; split_ifs
          · simp [totalLen]
          · simp [totalLen]; omega
        have htl123 : totalLen (p1 ++ p2 ++ p3) = len := by
          rw [totalLen_append, totalLen_append, htl1, htl2, htl3]; omega
        rw [wtAt_append, htl123]
        by_cases hz : z < len
        · rw [if_pos hz, wtAt, if_pos hz]
          rw [wtAt_append, wtAt_append, htl1, totalLen_append, htl1, htl2]
          by_cases hz1 : z < lo
          · rw [if_pos (by omega), if_pos hz1, if_neg (by omega)]
            dsimp only [p1]; rw [if_pos (by omega)]; simp [wtAt, hz1]
          · by_cases hz2 : z < endIn
            · rw [if_pos (by omega), if_neg hz1, if_pos (by omega)]
              simp [p2, wtAt, show z - lo < endIn - lo by omega]
            · rw [if_neg (by omega), if_neg (by omega)]
              dsimp only [p3]; rw [if_pos (by omega)]
              simp [wtAt, show z - (lo + (endIn - lo)) < len - endIn by omega]
        · rw [if_neg hz, wtAt, if_neg hz, doubleRunsAux_wtAt rs 0 (hi - endIn) (z - len)]
          by_cases hmem : lo ≤ z ∧ z < hi
          · rw [if_pos hmem, if_pos (by omega)]
          · rw [if_neg hmem, if_neg (by omega)]

private theorem doubleRunsAux_totalWt (runs : List (ℕ × ℕ)) (lo hi : ℕ)
    (_hlo : lo ≤ hi) (hhi : hi ≤ totalLen runs) :
    totalWt (doubleRunsAux runs lo hi) = totalWt runs + wtInterval runs lo hi := by
  rw [← cumWt_totalLen, doubleRunsAux_totalLen, ← cumWt_totalLen runs]
  unfold cumWt wtInterval
  have hfn : ∀ u ∈ Finset.range (totalLen runs),
      wtAt (doubleRunsAux runs lo hi) u =
        wtAt runs u + if lo ≤ u ∧ u < hi then wtAt runs u else 0 := by
    intro u _
    rw [doubleRunsAux_wtAt]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl hfn, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

private abbrev DRState : Type := List (ℕ × ℕ) × ((ℕ × ℕ) × List (ℕ × ℕ))

private def drStep (st : DRState) : DRState :=
  let u := listUncons (0, 0) st.1
  if u.1 then
    let len := u.2.1.1
    let wt := u.2.1.2
    let lo := st.2.1.1
    let hi := st.2.1.2
    let out := st.2.2
    if decide (hi ≤ lo) then
      (u.2.2, ((0, 0), (len, wt) :: out))
    else if decide (len ≤ lo) then
      (u.2.2, ((lo - len, hi - len), (len, wt) :: out))
    else
      let endIn := min len hi
      let out1 := if decide (0 < lo) then (lo, wt) :: out else out
      let out2 := (endIn - lo, 2 * wt) :: out1
      let out3 := if decide (endIn < len) then (len - endIn, wt) :: out2 else out2
      (u.2.2, ((0, hi - endIn), out3))
  else st

private theorem drStep_spec : ∀ (k : ℕ) (rem : List (ℕ × ℕ)) (lo hi : ℕ) (out : List (ℕ × ℕ)),
    let st := drStep^[k] (rem, ((lo, hi), out))
    st.2.1.1 ≤ lo ∧
    st.2.1.2 ≤ hi ∧
    (bitEncode st.2.2).length + 10 * (bitEncode st.1).length ≤
      (bitEncode out).length + 10 * (bitEncode rem).length ∧
    (rem.length ≤ k → st.2.2 = (doubleRunsAux rem lo hi).reverse ++ out)
  | 0, rem, lo, hi, out => by
    dsimp only
    refine ⟨le_rfl, le_rfl, le_rfl, fun h => ?_⟩
    cases rem with
    | nil => simp [doubleRunsAux]
    | cons _ _ => simp at h
  | k + 1, rem, lo, hi, out => by
    dsimp only
    rw [Function.iterate_succ_apply]
    cases rem with
    | nil =>
      have hst : drStep ([], ((lo, hi), out)) = ([], ((lo, hi), out)) := rfl
      rw [hst]
      have h := drStep_spec k [] lo hi out
      exact ⟨h.1, h.2.1, h.2.2.1, fun _ => h.2.2.2 (Nat.zero_le _)⟩
    | cons r rs =>
      rcases r with ⟨len, wt⟩
      have hst : drStep ((len, wt) :: rs, ((lo, hi), out)) =
          if decide (hi ≤ lo) then (rs, ((0, 0), (len, wt) :: out))
          else if decide (len ≤ lo) then (rs, ((lo - len, hi - len), (len, wt) :: out))
          else
            let endIn := min len hi
            let out1 := if decide (0 < lo) then (lo, wt) :: out else out
            let out2 := (endIn - lo, 2 * wt) :: out1
            let out3 := if decide (endIn < len) then (len - endIn, wt) :: out2 else out2
            (rs, ((0, hi - endIn), out3)) := rfl
      rw [hst]
      by_cases hc1 : hi ≤ lo
      · rw [if_pos (decide_eq_true hc1)]
        have h := drStep_spec k rs 0 0 ((len, wt) :: out)
        refine ⟨by omega, by omega, ?_, fun hk => ?_⟩
        · have h1 := h.2.2.1
          rw [bitEncode_list_cons_len] at h1; rw [bitEncode_list_cons_len]; omega
        · rw [h.2.2.2 (by simp at hk; omega), doubleRunsAux, if_pos hc1,
            List.reverse_cons, List.append_assoc]; rfl
      · rw [if_neg (by rw [decide_eq_false hc1]; exact Bool.false_ne_true)]
        by_cases hc2 : len ≤ lo
        · rw [if_pos (decide_eq_true hc2)]
          have h := drStep_spec k rs (lo - len) (hi - len) ((len, wt) :: out)
          refine ⟨by omega, by omega, ?_, fun hk => ?_⟩
          · have h1 := h.2.2.1
            rw [bitEncode_list_cons_len] at h1; rw [bitEncode_list_cons_len]; omega
          · rw [h.2.2.2 (by simp at hk; omega), doubleRunsAux, if_neg hc1, if_pos hc2,
              List.reverse_cons, List.append_assoc]; rfl
        · rw [if_neg (by rw [decide_eq_false hc2]; exact Bool.false_ne_true)]
          set endIn := min len hi
          set out1 := if decide (0 < lo) then (lo, wt) :: out else out
          set out2 := (endIn - lo, 2 * wt) :: out1
          set out3 := if decide (endIn < len) then (len - endIn, wt) :: out2 else out2
          have h := drStep_spec k rs 0 (hi - endIn) out3
          have hle_enc : ∀ a b : ℕ, a ≤ b → (bitEncode a).length ≤ (bitEncode b).length := by
            intro a b hab
            exact length_encodeNat_le (lt_of_le_of_lt hab (lt_two_pow_bitEncode_nat b))
          have hwt2 : (bitEncode (2 * wt)).length ≤ (bitEncode wt).length + 1 := by
            have hlt := lt_two_pow_bitEncode_nat wt
            exact length_encodeNat_le (by rw [pow_succ]; omega)
          have hl1 : (bitEncode out1).length ≤ (bitEncode out).length +
              (2 * (2 * (bitEncode len).length + 1 + (bitEncode wt).length) + 1) := by
            dsimp only [out1]; split_ifs
            · rw [bitEncode_list_cons_len, bitEncode_pair_len]
              have := hle_enc lo len (by omega); omega
            · omega
          have hl2 : (bitEncode out2).length ≤ (bitEncode out1).length +
              (2 * (2 * (bitEncode len).length + 1 + ((bitEncode wt).length + 1)) + 1) := by
            dsimp only [out2]; rw [bitEncode_list_cons_len, bitEncode_pair_len]
            have := hle_enc (endIn - lo) len (by omega); omega
          have hl3 : (bitEncode out3).length ≤ (bitEncode out2).length +
              (2 * (2 * (bitEncode len).length + 1 + (bitEncode wt).length) + 1) := by
            dsimp only [out3]; split_ifs
            · rw [bitEncode_list_cons_len, bitEncode_pair_len]
              have := hle_enc (len - endIn) len (by omega); omega
            · omega
          change (drStep^[k] (rs, ((0, hi - endIn), out3))).2.1.1 ≤ lo ∧
            (drStep^[k] (rs, ((0, hi - endIn), out3))).2.1.2 ≤ hi ∧
            (bitEncode (drStep^[k] (rs, ((0, hi - endIn), out3))).2.2).length +
              10 * (bitEncode (drStep^[k] (rs, ((0, hi - endIn), out3))).1).length ≤
              (bitEncode out).length + 10 * (bitEncode ((len, wt) :: rs)).length ∧
            (((len, wt) :: rs).length ≤ k + 1 →
              (drStep^[k] (rs, ((0, hi - endIn), out3))).2.2 =
                (doubleRunsAux ((len, wt) :: rs) lo hi).reverse ++ out)
          have h_lo := h.1; have h_hi := h.2.1; have h_len := h.2.2.1; have h_rev := h.2.2.2
          refine ⟨by omega, by omega, ?_, fun hk => ?_⟩
          · have hcons : (bitEncode ((len, wt) :: rs)).length =
                2 * (2 * (bitEncode len).length + 1 + (bitEncode wt).length) + 1 + (bitEncode rs).length := by
              rw [bitEncode_list_cons_len, bitEncode_pair_len]
            omega
          · rw [h_rev (by simp at hk; omega), doubleRunsAux, if_neg hc1, if_neg hc2]
            dsimp only [out3, out2, out1, endIn]
            by_cases hlo0 : 0 < lo <;> by_cases hend : min len hi < len <;>
              simp [hlo0, hend, List.append_assoc]

private def doubleRuns (p : List (ℕ × ℕ) × (ℕ × ℕ)) : List (ℕ × ℕ) :=
  ((drStep^[(List.replicate (bitEncode p.1).length false).length] (p.1, (p.2, []))).2.2).reverse

private theorem doubleRuns_eq (runs : List (ℕ × ℕ)) (b : ℕ × ℕ) :
    doubleRuns (runs, b) = doubleRunsAux runs b.1 b.2 := by
  dsimp only [doubleRuns]
  rw [List.length_replicate,
    (drStep_spec (bitEncode runs).length runs b.1 b.2 []).2.2.2 (list_len_le_bitEncode runs),
    List.append_nil, List.reverse_reverse]

private theorem isPolyTime_doubleRuns : IsPolyTime doubleRuns := by
  have hstep : IsPolyTime drStep := by
    have hid : IsPolyTime (id : DRState → DRState) := isPolyTime_id
    have hu := isPolyTime_seq (pt_fst hid) (isPolyTime_listUncons (0, 0))
    have hrem' := pt_snd (pt_snd hu)
    have hr := pt_fst (pt_snd hu)
    have hlen := pt_fst hr
    have hwt := pt_snd hr
    have hlo := pt_fst (pt_fst (pt_snd hid))
    have hhi := pt_snd (pt_fst (pt_snd hid))
    have hout := pt_snd (pt_snd hid)
    have hbr1 := isPolyTime_pair hrem' (isPolyTime_pair (isPolyTime_const (0, 0)) (pt_cons hr hout))
    have hbr2 := isPolyTime_pair hrem'
      (isPolyTime_pair (isPolyTime_pair (pt_sub hlo hlen) (pt_sub hhi hlen)) (pt_cons hr hout))
    have hend := pt_min hlen hhi
    have hout1 := isPolyTime_ite (pt_lt (isPolyTime_const 0) hlo)
      (pt_cons (isPolyTime_pair hlo hwt) hout) hout
    have hout2 := pt_cons (isPolyTime_pair (pt_sub hend hlo) (isPolyTime_seq hwt isPolyTime_natDouble)) hout1
    have hout3 := isPolyTime_ite (pt_lt hend hlen)
      (pt_cons (isPolyTime_pair (pt_sub hlen hend) hwt) hout2) hout2
    have hbr3 := isPolyTime_pair hrem'
      (isPolyTime_pair (isPolyTime_pair (isPolyTime_const 0) (pt_sub hhi hend)) hout3)
    exact isPolyTime_ite (pt_fst hu)
      (isPolyTime_ite (pt_le hhi hlo) hbr1 (isPolyTime_ite (pt_le hlen hlo) hbr2 hbr3))
      hid
  have hiter : IsPolyTime (fun q : List Bool × DRState => drStep^[q.1.length] q.2) := by
    refine isPolyTime_iter drStep hstep (20 * Polynomial.X + 20)
      (fun u ⟨rem, ⟨⟨lo, hi⟩, out⟩⟩ k _ => ?_)
    set st := drStep^[k] (rem, ((lo, hi), out))
    obtain ⟨h1, h2, h3, _⟩ := drStep_spec k rem lo hi out
    have h1' : st.2.1.1 ≤ lo := h1
    have h2' : st.2.1.2 ≤ hi := h2
    have h3' : (bitEncode st.2.2).length + 10 * (bitEncode st.1).length ≤
        (bitEncode out).length + 10 * (bitEncode rem).length := h3
    have hlo_len : (bitEncode st.2.1.1).length ≤ (bitEncode lo).length :=
      length_encodeNat_le (lt_of_le_of_lt h1' (lt_two_pow_bitEncode_nat lo))
    have hhi_len : (bitEncode st.2.1.2).length ≤ (bitEncode hi).length :=
      length_encodeNat_le (lt_of_le_of_lt h2' (lt_two_pow_bitEncode_nat hi))
    have hL : (bitEncode (u, (rem, ((lo, hi), out)))).length =
        2 * (3 * u.length) + 1 + (2 * (bitEncode rem).length + 1 +
          (2 * (2 * (bitEncode lo).length + 1 + (bitEncode hi).length) + 1 + (bitEncode out).length)) := by
      rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len,
        bitEncode_listBool_length]
    have hst_len : (bitEncode st).length =
        2 * (bitEncode st.1).length + 1 +
          (2 * (2 * (bitEncode st.2.1.1).length + 1 + (bitEncode st.2.1.2).length) + 1 + (bitEncode st.2.2).length) := by
      rw [bitEncode_pair_len st.1 st.2, bitEncode_pair_len st.2.1 st.2.2,
        bitEncode_pair_len st.2.1.1 st.2.1.2]
    change (bitEncode st).length ≤ _
    rw [hst_len]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  have hid : IsPolyTime (id : List (ℕ × ℕ) × (ℕ × ℕ) → _) := isPolyTime_id
  have hprep : IsPolyTime (fun p : List (ℕ × ℕ) × (ℕ × ℕ) =>
      (List.replicate (bitEncode p.1).length false, (p.1, (p.2, ([] : List (ℕ × ℕ)))))) :=
    isPolyTime_pair (isPolyTime_seq (pt_fst hid) isPolyTime_unaryLen)
      (isPolyTime_pair (pt_fst hid) (isPolyTime_pair (pt_snd hid) (isPolyTime_const [])))
  have hres : IsPolyTime (fun p : List (ℕ × ℕ) × (ℕ × ℕ) =>
      ((drStep^[(List.replicate (bitEncode p.1).length false).length] (p.1, (p.2, []))).2.2).reverse) :=
    isPolyTime_seq (pt_snd (pt_snd (isPolyTime_seq hprep hiter))) (isPolyTime_listRev (0, 0))
  exact hres

private def updateRow (p : List (List (ℕ × ℕ)) × List (ℕ × ℕ)) : List (List (ℕ × ℕ)) :=
  zipMapD (0, 0) doubleRuns p.1 p.2

private theorem isPolyTime_updateRow : IsPolyTime updateRow :=
  isPolyTime_zipMapD ([] : List (ℕ × ℕ)) (0, 0) ([] : List (ℕ × ℕ)) doubleRuns isPolyTime_doubleRuns

private def updateTable (p : List (List (List (ℕ × ℕ))) × List (List (ℕ × ℕ))) :
    List (List (List (ℕ × ℕ))) :=
  zipMapD [] updateRow p.1 p.2

private theorem isPolyTime_updateTable : IsPolyTime updateTable :=
  isPolyTime_zipMapD ([] : List (List (ℕ × ℕ))) ([] : List (ℕ × ℕ)) ([] : List (List (ℕ × ℕ)))
    updateRow isPolyTime_updateRow


/- ## Section 6: MWU Search Engine, Polynomial-Time Proof, and Elementary Termination -/

section MWUEngine

variable
  (lp : ℕ × List (List ℚ × ℚ) → List ℚ)
  (eta : GameInput → ℚ)
  (patLP : GameInput × List ℚ → ℕ × List (List ℚ × ℚ))
  (decode : GameInput × List ℚ → EquilibriumOutput)
  (grid : GameInput × ℚ → ℕ)
  (sweep : (GameInput × ℚ) × List (List (List ℕ)) → List ℚ × List (List (ℕ × ℕ)))

private abbrev MWUCtx : Type := (GameInput × ℚ) × (List Bool × ℕ)
private abbrev MWUTable : Type := List (List (List (ℕ × ℕ)))
private abbrev MWUState : Type := MWUCtx × (Bool × (EquilibriumOutput × MWUTable))

private def tryDecode
    (p : MWUCtx × MWUTable) : EquilibriumOutput :=
  let Q := tableQuantiles (p.1.2, p.2)
  let xB := sweep (p.1.1, Q)
  let L := patLP (p.1.1.1, xB.1)
  let y := lp L
  decode (p.1.1.1, y)

private theorem isPolyTime_tryDecode
    (hlp : IsPolyTime lp) (hpat : IsPolyTime patLP)
    (hdec : IsPolyTime decode) (hsweep : IsPolyTime sweep) :
    IsPolyTime (tryDecode lp patLP decode sweep) := by
  have hid : IsPolyTime (id : MWUCtx × MWUTable → _) := isPolyTime_id
  have hQ := isPolyTime_seq (isPolyTime_pair (pt_snd (pt_fst hid)) (pt_snd hid))
    isPolyTime_tableQuantiles
  have hxB := isPolyTime_seq (isPolyTime_pair (pt_fst (pt_fst hid)) hQ) hsweep
  have hL := isPolyTime_seq (isPolyTime_pair (pt_fst (pt_fst (pt_fst hid))) (pt_fst hxB)) hpat
  have hy := isPolyTime_seq hL hlp
  have hres : IsPolyTime (fun p : MWUCtx × MWUTable =>
      decode (p.1.1.1, lp (patLP (p.1.1.1, (sweep (p.1.1, tableQuantiles (p.1.2, p.2))).1)))) :=
    isPolyTime_seq (isPolyTime_pair (pt_fst (pt_fst (pt_fst hid))) hy) hdec
  exact hres

private def mwuStep (st : MWUState) : MWUState :=
  if st.2.1 then st
  else
    let Q := tableQuantiles (st.1.2, st.2.2.2)
    let xB := sweep (st.1.1, Q)
    let L := patLP (st.1.1.1, xB.1)
    let y := lp L
    if checkLP (L, y) then
      (st.1, (true, (decode (st.1.1.1, y), st.2.2.2)))
    else
      (st.1, (false, (st.2.2.1, updateTable (st.2.2.2, xB.2))))

private theorem isPolyTime_mwuStep
    (hlp : IsPolyTime lp) (hpat : IsPolyTime patLP)
    (hdec : IsPolyTime decode) (hsweep : IsPolyTime sweep) :
    IsPolyTime (mwuStep lp patLP decode sweep) := by
  have hid : IsPolyTime (id : MWUState → MWUState) := isPolyTime_id
  have hctx := pt_fst hid
  have hfound := pt_fst (pt_snd hid)
  have hans := pt_fst (pt_snd (pt_snd hid))
  have htab := pt_snd (pt_snd (pt_snd hid))
  have hQ := isPolyTime_seq (isPolyTime_pair (pt_snd hctx) htab) isPolyTime_tableQuantiles
  have hxB := isPolyTime_seq (isPolyTime_pair (pt_fst hctx) hQ) hsweep
  have hL := isPolyTime_seq (isPolyTime_pair (pt_fst (pt_fst hctx)) (pt_fst hxB)) hpat
  have hy := isPolyTime_seq hL hlp
  have hchk := isPolyTime_seq (isPolyTime_pair hL hy) isPolyTime_checkLP
  have hsol := isPolyTime_seq (isPolyTime_pair (pt_fst (pt_fst hctx)) hy) hdec
  have htab' := isPolyTime_seq (isPolyTime_pair htab (pt_snd hxB)) isPolyTime_updateTable
  have hbrT := isPolyTime_pair hctx (isPolyTime_pair (isPolyTime_const true) (isPolyTime_pair hsol htab))
  have hbrF := isPolyTime_pair hctx (isPolyTime_pair (isPolyTime_const false) (isPolyTime_pair hans htab'))
  exact isPolyTime_ite hfound hid (isPolyTime_ite hchk hbrT hbrF)

/- ### Table Evolution & Space Bounds for `isPolyTime_iter (mwuStep ...)` -/

private def CellEvolves (t : ℕ) (c0 c : List (ℕ × ℕ)) : Prop :=
  c.length ≤ c0.length + 2 * t ∧ totalLen c = totalLen c0 ∧ maxWt c ≤ 2 ^ t * maxWt c0

private def RowEvolves (t : ℕ) (r0 r : List (List (ℕ × ℕ))) : Prop :=
  r.length = r0.length ∧ ∀ j < r0.length, CellEvolves t (r0[j]?.getD []) (r[j]?.getD [])

private def TableEvolves (t : ℕ) (t0 tab : MWUTable) : Prop :=
  tab.length = t0.length ∧ ∀ i < t0.length, RowEvolves t (t0[i]?.getD []) (tab[i]?.getD [])

private theorem cellEvolves_refl (c0 : List (ℕ × ℕ)) : CellEvolves 0 c0 c0 := by
  exact ⟨by simp, rfl, by simp⟩

private theorem cellEvolves_mono {t1 t2 : ℕ} {c0 c : List (ℕ × ℕ)} (h : t1 ≤ t2)
    (hc : CellEvolves t1 c0 c) : CellEvolves t2 c0 c := by
  have hc1 := hc.1
  refine ⟨by omega, hc.2.1, le_trans hc.2.2 ?_⟩
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) h)

private theorem cellEvolves_step {t : ℕ} {c0 c : List (ℕ × ℕ)} (hc : CellEvolves t c0 c)
    (b : ℕ × ℕ) : CellEvolves (t + 1) c0 (doubleRuns (c, b)) := by
  have hc1 := hc.1
  rw [doubleRuns_eq]
  refine ⟨le_trans (doubleRunsAux_len c b.1 b.2) (by omega),
    by rw [doubleRunsAux_totalLen, hc.2.1], ?_⟩
  calc maxWt (doubleRunsAux c b.1 b.2)
      ≤ 2 * maxWt c := doubleRunsAux_maxWt c b.1 b.2
    _ ≤ 2 * (2 ^ t * maxWt c0) := Nat.mul_le_mul_left 2 hc.2.2
    _ = 2 ^ (t + 1) * maxWt c0 := by rw [pow_succ]; ring

private theorem rowEvolves_refl (r0 : List (List (ℕ × ℕ))) : RowEvolves 0 r0 r0 :=
  ⟨rfl, fun _ _ => cellEvolves_refl _⟩

private theorem rowEvolves_mono {t1 t2 : ℕ} {r0 r : List (List (ℕ × ℕ))} (h : t1 ≤ t2)
    (hr : RowEvolves t1 r0 r) : RowEvolves t2 r0 r :=
  ⟨hr.1, fun j hj => cellEvolves_mono h (hr.2 j hj)⟩

private theorem rowEvolves_step {t : ℕ} {r0 r : List (List (ℕ × ℕ))} (hr : RowEvolves t r0 r)
    (brow : List (ℕ × ℕ)) : RowEvolves (t + 1) r0 (updateRow (r, brow)) := by
  dsimp only [updateRow]
  refine ⟨by rw [zipMapD_length, hr.1], fun j hj => ?_⟩
  rw [zipMapD_getElem?]
  have hr1 := hr.1
  have hjr : j < r.length := by omega
  have hsome : r[j]? = some r[j] := List.getElem?_eq_getElem hjr
  rw [hsome, Option.map_some, Option.getD_some]
  have hcj := hr.2 j hj
  rw [hsome, Option.getD_some] at hcj
  exact cellEvolves_step hcj (brow[j]?.getD (0, 0))

private theorem tableEvolves_refl (t0 : MWUTable) : TableEvolves 0 t0 t0 :=
  ⟨rfl, fun _ _ => rowEvolves_refl _⟩

private theorem tableEvolves_mono {t1 t2 : ℕ} {t0 tab : MWUTable} (h : t1 ≤ t2)
    (ht : TableEvolves t1 t0 tab) : TableEvolves t2 t0 tab :=
  ⟨ht.1, fun i hi => rowEvolves_mono h (ht.2 i hi)⟩

private theorem tableEvolves_step {t : ℕ} {t0 tab : MWUTable} (ht : TableEvolves t t0 tab)
    (B : List (List (ℕ × ℕ))) : TableEvolves (t + 1) t0 (updateTable (tab, B)) := by
  dsimp only [updateTable]
  refine ⟨by rw [zipMapD_length, ht.1], fun i hi => ?_⟩
  rw [zipMapD_getElem?]
  have ht1 := ht.1
  have hit : i < tab.length := by omega
  have hsome : tab[i]? = some tab[i] := List.getElem?_eq_getElem hit
  rw [hsome, Option.map_some, Option.getD_some]
  have hri := ht.2 i hi
  rw [hsome, Option.getD_some] at hri
  exact rowEvolves_step hri (B[i]?.getD [])

private theorem bitEncode_list_bound {α : Type} [BitstringEncoding α] (l : List α) (M : ℕ)
    (h : ∀ x ∈ l, (bitEncode x).length ≤ M) :
    (bitEncode l).length ≤ l.length * (2 * M + 1) := by
  induction l with
  | nil => simp [bitEncode_list_nil]
  | cons a t ih =>
    rw [bitEncode_list_cons_len, List.length_cons, Nat.add_mul, one_mul]
    have ha := h a (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    omega

private theorem bitEncode_tableEvolves_bound {t : ℕ} {t0 tab : MWUTable}
    (ht : TableEvolves t t0 tab) :
    let L0 := (bitEncode t0).length
    let Mcell := (L0 + 2 * t) * (6 * L0 + 2 * t + 9)
    let Mrow := L0 * (2 * Mcell + 1)
    (bitEncode tab).length ≤ L0 * (2 * Mrow + 1) := by
  dsimp only
  set L0 := (bitEncode t0).length
  set Mcell := (L0 + 2 * t) * (6 * L0 + 2 * t + 9)
  set Mrow := L0 * (2 * Mcell + 1)
  have htab_len : tab.length ≤ L0 := by rw [ht.1]; exact list_len_le_bitEncode t0
  have hrows : ∀ row ∈ tab, (bitEncode row).length ≤ Mrow := by
    intro row hrow
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hrow
    have ht1 := ht.1
    have hi0 : i < t0.length := by omega
    have hri := ht.2 i hi0
    have hsome_tab : tab[i]? = some tab[i] := List.getElem?_eq_getElem hi
    have hsome_t0 : t0[i]? = some t0[i] := List.getElem?_eq_getElem hi0
    rw [hsome_tab, hsome_t0, Option.getD_some, Option.getD_some] at hri
    have hrow0_le : (bitEncode t0[i]).length ≤ L0 := bitEncode_mem_le (List.getElem_mem hi0)
    have hrow_len : tab[i].length ≤ L0 := by
      rw [hri.1]; exact le_trans (list_len_le_bitEncode _) hrow0_le
    have hcells : ∀ cell ∈ tab[i], (bitEncode cell).length ≤ Mcell := by
      intro cell hcell
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hcell
      have hr1 := hri.1
      have hj0 : j < t0[i].length := by omega
      have hcj := hri.2 j hj0
      have hs1 : tab[i][j]? = some tab[i][j] := List.getElem?_eq_getElem hj
      have hs0 : t0[i][j]? = some t0[i][j] := List.getElem?_eq_getElem hj0
      rw [hs1, hs0, Option.getD_some, Option.getD_some] at hcj
      have hc0_le : (bitEncode t0[i][j]).length ≤ L0 :=
        le_trans (bitEncode_mem_le (List.getElem_mem hj0)) hrow0_le
      have hclen : tab[i][j].length ≤ L0 + 2 * t :=
        le_trans hcj.1 (Nat.add_le_add_right (le_trans (list_len_le_bitEncode _) hc0_le) _)
      have hruns : ∀ r ∈ tab[i][j], (bitEncode r).length ≤ 3 * L0 + t + 4 := by
        intro r hr
        have hr1 : r.1 < 2 ^ (L0 + 1) := by
          have h1 : r.1 ≤ totalLen tab[i][j] := run_le_totalLen hr
          rw [hcj.2.1] at h1
          have h2 := totalLen_lt_pow t0[i][j]
          exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by omega) (by omega)))
        have hr2 : r.2 < 2 ^ (t + L0 + 1) := by
          have h1 : r.2 ≤ maxWt tab[i][j] := run_le_maxWt hr
          have h2 := maxWt_lt_pow t0[i][j]
          have h3 : 2 ^ t * maxWt t0[i][j] < 2 ^ t * 2 ^ (L0 + 1) :=
            Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by omega) (by omega)))
              (by positivity)
          rw [← pow_add] at h3
          exact lt_of_le_of_lt (le_trans h1 hcj.2.2) (by simpa [Nat.add_assoc] using h3)
        have hb1 : (bitEncode r.1).length ≤ L0 + 1 := length_encodeNat_le hr1
        have hb2 : (bitEncode r.2).length ≤ t + L0 + 1 := length_encodeNat_le hr2
        rw [bitEncode_pair_len]; omega
      have hcb := bitEncode_list_bound tab[i][j] (3 * L0 + t + 4) hruns
      calc (bitEncode tab[i][j]).length
          ≤ tab[i][j].length * (2 * (3 * L0 + t + 4) + 1) := hcb
        _ ≤ (L0 + 2 * t) * (6 * L0 + 2 * t + 9) := Nat.mul_le_mul hclen (by omega)
    exact le_trans (bitEncode_list_bound tab[i] Mcell hcells) (Nat.mul_le_mul_right _ hrow_len)
  exact le_trans (bitEncode_list_bound tab Mrow hrows) (Nat.mul_le_mul_right _ htab_len)

private theorem mwuStep_of_true {st : MWUState} (h : st.2.1 = true) :
    mwuStep lp patLP decode sweep st = st := by
  simp [mwuStep, h]

private theorem mwuStep_of_false {st : MWUState} (h : st.2.1 = false) :
    mwuStep lp patLP decode sweep st =
      let Q := tableQuantiles (st.1.2, st.2.2.2)
      let xB := sweep (st.1.1, Q)
      let L := patLP (st.1.1.1, xB.1)
      let y := lp L
      if checkLP (L, y) then (st.1, (true, (decode (st.1.1.1, y), st.2.2.2)))
      else (st.1, (false, (st.2.2.1, updateTable (st.2.2.2, xB.2)))) := by
  simp [mwuStep, h]

private theorem mwuStep_inv : ∀ (k : ℕ) (ctx : MWUCtx) (found : Bool) (ans : EquilibriumOutput)
    (tab0 : MWUTable),
    let st := (mwuStep lp patLP decode sweep)^[k] (ctx, (found, (ans, tab0)))
    st.1 = ctx ∧
    TableEvolves k tab0 st.2.2.2 ∧
    (st.2.2.1 = ans ∨ ∃ tab', TableEvolves k tab0 tab' ∧
      st.2.2.1 = tryDecode lp patLP decode sweep (ctx, tab'))
  | 0, ctx, found, ans, tab0 => by
    dsimp only
    exact ⟨rfl, tableEvolves_refl tab0, Or.inl rfl⟩
  | k + 1, ctx, found, ans, tab0 => by
    dsimp only
    rw [Function.iterate_succ_apply']
    set st := (mwuStep lp patLP decode sweep)^[k] (ctx, (found, (ans, tab0)))
    obtain ⟨hctx, htab, hans⟩ := mwuStep_inv k ctx found ans tab0
    change let st' := mwuStep lp patLP decode sweep st; _
    dsimp only
    by_cases hf : st.2.1 = true
    · have hst' : mwuStep lp patLP decode sweep st = st := by
        simp only [mwuStep, hf, ↓reduceIte]
      rw [hst']
      refine ⟨hctx, tableEvolves_mono (by omega) htab, ?_⟩
      rcases hans with h1 | ⟨tab', hte, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨tab', tableEvolves_mono (by omega) hte, h2⟩
    · have hf' : st.2.1 = false := Bool.eq_false_iff.mpr hf
      set Q := tableQuantiles (st.1.2, st.2.2.2)
      set xB := sweep (st.1.1, Q)
      set L := patLP (st.1.1.1, xB.1)
      set y := lp L
      by_cases hchk : checkLP (L, y) = true
      · have hst' : mwuStep lp patLP decode sweep st =
            (st.1, (true, (decode (st.1.1.1, y), st.2.2.2))) := by
          rw [mwuStep_of_false lp patLP decode sweep hf']
          exact if_pos hchk
        rw [hst']
        refine ⟨hctx, tableEvolves_mono (by omega) htab, Or.inr ⟨st.2.2.2, tableEvolves_mono (by omega) htab, ?_⟩⟩
        dsimp only [tryDecode, y, L, xB, Q]
        rw [hctx]
      · have hchk' : checkLP (L, y) = false := Bool.eq_false_iff.mpr hchk
        have hst' : mwuStep lp patLP decode sweep st =
            (st.1, (false, (st.2.2.1, updateTable (st.2.2.2, xB.2)))) := by
          rw [mwuStep_of_false lp patLP decode sweep hf']
          exact if_neg (by rw [hchk']; exact Bool.false_ne_true)
        rw [hst']
        refine ⟨hctx, tableEvolves_step htab xB.2, ?_⟩
        rcases hans with h1 | ⟨tab', hte, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨tab', tableEvolves_mono (by omega) hte, h2⟩

private theorem isPolyTime_mwuIter
    (hlp : IsPolyTime lp) (hpat : IsPolyTime patLP)
    (hdec : IsPolyTime decode) (hsweep : IsPolyTime sweep) :
    IsPolyTime (fun p : List Bool × MWUState => (mwuStep lp patLP decode sweep)^[p.1.length] p.2) := by
  have hstep := isPolyTime_mwuStep lp patLP decode sweep hlp hpat hdec hsweep
  obtain ⟨Pdec, hPdec⟩ := isPolyTime_output_bound (isPolyTime_tryDecode lp patLP decode sweep hlp hpat hdec hsweep)
  let Ptab : Polynomial ℕ := 96 * Polynomial.X ^ 4 + 108 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 2 + Polynomial.X
  let S : Polynomial ℕ := 10 * Polynomial.X + 20 + 2 * Pdec.comp (2 * Polynomial.X + 1 + Ptab) + Ptab
  refine isPolyTime_iter (mwuStep lp patLP decode sweep) hstep S
    (fun u ⟨ctx, ⟨found, ⟨ans, tab0⟩⟩⟩ k hk => ?_)
  set L := (bitEncode (u, (ctx, (found, (ans, tab0))))).length
  have hL : L = 2 * (3 * u.length) + 1 + (2 * (bitEncode ctx).length + 1 +
      (2 * 1 + 1 + (2 * (bitEncode ans).length + 1 + (bitEncode tab0).length))) := by
    dsimp only [L]
    rw [bitEncode_pair_len u (ctx, (found, (ans, tab0))),
      bitEncode_pair_len ctx (found, (ans, tab0)),
      bitEncode_pair_len found (ans, tab0),
      bitEncode_pair_len ans tab0,
      bitEncode_listBool_length, bitEncode_bool_len]
  have htab_eval : ∀ tab', TableEvolves k tab0 tab' → (bitEncode tab').length ≤ Ptab.eval L := by
    intro tab' hte
    have hb := bitEncode_tableEvolves_bound hte
    dsimp only at hb
    set L0 := (bitEncode tab0).length
    have hL0 : L0 ≤ L := by omega
    have hkL : k ≤ L := by omega
    have hMc : (L0 + 2 * k) * (6 * L0 + 2 * k + 9) ≤ (3 * L) * (8 * L + 9) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hMr : L0 * (2 * ((L0 + 2 * k) * (6 * L0 + 2 * k + 9)) + 1) ≤
        L * (2 * ((3 * L) * (8 * L + 9)) + 1) :=
      Nat.mul_le_mul hL0 (by omega)
    have hMt : L0 * (2 * (L0 * (2 * ((L0 + 2 * k) * (6 * L0 + 2 * k + 9)) + 1)) + 1) ≤
        L * (2 * (L * (2 * ((3 * L) * (8 * L + 9)) + 1)) + 1) :=
      Nat.mul_le_mul hL0 (by omega)
    have hPtab_eq : Ptab.eval L = 96 * L ^ 4 + 108 * L ^ 3 + 2 * L ^ 2 + L := by
      simp [Ptab]
    have hMt_eq : L * (2 * (L * (2 * ((3 * L) * (8 * L + 9)) + 1)) + 1) =
        96 * L ^ 4 + 108 * L ^ 3 + 2 * L ^ 2 + L := by ring
    omega
  set st := (mwuStep lp patLP decode sweep)^[k] (ctx, (found, (ans, tab0)))
  obtain ⟨hctx, htab, hans⟩ := mwuStep_inv lp patLP decode sweep k ctx found ans tab0
  have htab_len : (bitEncode st.2.2.2).length ≤ Ptab.eval L := htab_eval st.2.2.2 htab
  have hans_len : (bitEncode st.2.2.1).length ≤ (bitEncode ans).length +
      Pdec.eval (2 * L + 1 + Ptab.eval L) := by
    rcases hans with h1 | ⟨tab', hte, h2⟩
    · rw [h1]; omega
    · rw [h2]
      have ht' := htab_eval tab' hte
      have harg : (bitEncode (ctx, tab')).length ≤ 2 * L + 1 + Ptab.eval L := by
        rw [bitEncode_pair_len]; omega
      exact le_trans (le_trans (hPdec (ctx, tab')) (poly_mono Pdec harg)) (by omega)
  have hst_len : (bitEncode st).length =
      2 * (bitEncode st.1).length + 1 +
        (2 * 1 + 1 + (2 * (bitEncode st.2.2.1).length + 1 + (bitEncode st.2.2.2).length)) := by
    rw [bitEncode_pair_len st.1 st.2, bitEncode_pair_len st.2.1 st.2.2,
      bitEncode_pair_len st.2.2.1 st.2.2.2, bitEncode_bool_len]
  change (bitEncode st).length ≤ S.eval L
  rw [hst_len, hctx]
  have hS_eq : S.eval L = 10 * L + 20 + 2 * Pdec.eval (2 * L + 1 + Ptab.eval L) + Ptab.eval L := by
    simp [S]
  rw [hS_eq]
  omega

/- ### Full Solver Construction (`mwuSolve`) and `IsPolyTime` Proof -/

def mwuSolve (g : GameInput) : EquilibriumOutput :=
  let eta_g := eta g
  let G_raw := grid (g, eta_g)
  let G := if decide (G_raw = 0) then 1 else G_raw
  let u_k := List.replicate g.2.2.length false
  let u_m := List.replicate g.2.1.length false
  let u_km1 := false :: (u_k ++ u_m)
  let u_J := (u_km1 ++ u_km1) ++ (u_km1 ++ u_km1)
  let u_Jm1 := u_J.tail
  let J := u_J.length
  let u_L := List.replicate (bitEncode G).length false
  let u_R := (unaryMulStep^[u_J.length] (u_L, [])).2
  let initRow := List.replicate u_m.length [(G, 1)]
  let initTable := List.replicate u_k.length initRow
  let initState : MWUState := (((g, eta_g), (u_Jm1, J)), (false, (([], []), initTable)))
  ((mwuStep lp patLP decode sweep)^[u_R.length] initState).2.2.1

theorem isPolyTime_mwuSolve
    (hlp : IsPolyTime lp) (heta : IsPolyTime eta) (hpat : IsPolyTime patLP)
    (hdec : IsPolyTime decode) (hgrid : IsPolyTime grid) (hsweep : IsPolyTime sweep) :
    IsPolyTime (mwuSolve lp eta patLP decode grid sweep) := by
  have hid : IsPolyTime (id : GameInput → GameInput) := isPolyTime_id
  have heta_g : IsPolyTime (fun g : GameInput => eta g) := heta
  have hG_raw : IsPolyTime (fun g : GameInput => grid (g, eta g)) :=
    isPolyTime_seq (isPolyTime_pair hid heta_g) hgrid
  have hG : IsPolyTime (fun g : GameInput => if decide (grid (g, eta g) = 0) then 1 else grid (g, eta g)) :=
    isPolyTime_ite (isPolyTime_seq hG_raw isPolyTime_natIsZero) (isPolyTime_const 1) hG_raw
  have hu_k : IsPolyTime (fun g : GameInput => List.replicate g.2.2.length false) :=
    isPolyTime_seq (pt_snd (pt_snd hid)) (isPolyTime_listToUnary ((0 : ℚ), []))
  have hu_m : IsPolyTime (fun g : GameInput => List.replicate g.2.1.length false) :=
    isPolyTime_seq (pt_fst (pt_snd hid)) (isPolyTime_listToUnary ((0 : ℚ), (0 : ℚ)))
  have hu_km1 : IsPolyTime (fun g : GameInput =>
      false :: (List.replicate g.2.2.length false ++ List.replicate g.2.1.length false)) :=
    isPolyTime_seq (pt_append hu_k hu_m) isPolyTime_unarySucc
  have hu_2 := pt_append hu_km1 hu_km1
  have hu_J := pt_append hu_2 hu_2
  have hu_Jm1 := isPolyTime_seq hu_J (isPolyTime_listTail false)
  have hJ := isPolyTime_seq hu_J (isPolyTime_listLen false)
  have hu_L := isPolyTime_seq hG isPolyTime_unaryLen
  have hu_R := isPolyTime_seq (isPolyTime_pair hu_J hu_L) isPolyTime_uRepeat
  have hcell0 := pt_cons (isPolyTime_pair hG (isPolyTime_const 1)) (isPolyTime_const ([] : List (ℕ × ℕ)))
  have hrow0 := isPolyTime_seq (isPolyTime_pair hu_m hcell0) isPolyTime_listReplicate
  have htab0 := isPolyTime_seq (isPolyTime_pair hu_k hrow0) isPolyTime_listReplicate
  have hinit : IsPolyTime (fun g : GameInput =>
      let eta_g := eta g
      let G := if decide (grid (g, eta_g) = 0) then 1 else grid (g, eta_g)
      let u_k := List.replicate g.2.2.length false
      let u_m := List.replicate g.2.1.length false
      let u_km1 := false :: (u_k ++ u_m)
      let u_J := (u_km1 ++ u_km1) ++ (u_km1 ++ u_km1)
      let u_L := List.replicate (bitEncode G).length false
      let u_R := (unaryMulStep^[u_J.length] (u_L, [])).2
      (u_R, ((((g, eta_g), (u_J.tail, u_J.length)),
        (false, (([], []), List.replicate u_k.length (List.replicate u_m.length [(G, 1)])))) : MWUState))) :=
    isPolyTime_pair hu_R
      (isPolyTime_pair (isPolyTime_pair (isPolyTime_pair hid heta_g) (isPolyTime_pair hu_Jm1 hJ))
        (isPolyTime_pair (isPolyTime_const false)
          (isPolyTime_pair (isPolyTime_const (([] : List ℚ), ([] : List (List ℚ)))) htab0)))
  have hiter := isPolyTime_mwuIter lp patLP decode sweep hlp hpat hdec hsweep
  exact pt_fst (pt_snd (pt_snd (isPolyTime_seq hinit hiter)))

/- ### Elementary Integer Termination Lemmas -/

private theorem quantile_avoidance_bound (uJm1 : List Bool) (J : ℕ) (runs : List (ℕ × ℕ))
    (lo hi : ℕ) (hJ : 1 ≤ J) (hu : uJm1.length = J - 1)
    (hwt : ∀ r ∈ runs, 1 ≤ r.2) (hlen : 1 ≤ totalLen runs)
    (hlo : lo ≤ hi) (hhi : hi ≤ totalLen runs)
    (havoid : ∀ z ∈ cellQuantiles ((uJm1, J), runs), ¬(lo ≤ z ∧ z < hi)) :
    J * wtInterval runs lo hi ≤ totalWt runs := by
  set M := totalWt runs
  have hM : 1 ≤ M := le_trans hlen (totalLen_le_totalWt runs hwt)
  set q := (J * cumWt runs lo) / M
  have hq_lo : q * M ≤ J * cumWt runs lo := Nat.div_mul_le_self _ _
  have hq_hi : J * cumWt runs lo < (q + 1) * M := by
    rw [mul_comm (q + 1) M]
    exact Nat.lt_mul_div_succ (J * cumWt runs lo) hM
  have hcum_add := cumWt_add_wtInterval runs hlo
  by_cases hqJ : q + 1 < J
  · set r := q + 1
    have hr1 : 1 ≤ r := Nat.succ_pos q
    have hr2 : r < J := hqJ
    have hr_le : r ≤ uJm1.length := by rw [hu]; omega
    have hrmem : findQuantile ((J, r * M), runs) ∈ cellQuantiles ((uJm1, J), runs) :=
      cellQuantiles_mem uJm1 J runs r hr1 hr_le
    obtain ⟨_, hz_lo, hz_hi⟩ := findQuantile_spec J r runs hJ hr1 hr2 hwt hlen
    set z := findQuantile ((J, r * M), runs)
    have hz_lo' : J * cumWt runs z < r * M := hz_lo
    have hz_hi' : r * M ≤ J * cumWt runs (z + 1) := hz_hi
    have hnot := havoid z hrmem
    have hlo_le_z : lo ≤ z := by
      by_contra hlt
      have h1 : z + 1 ≤ lo := by omega
      have h2 := cumWt_mono runs h1
      have h3 : J * cumWt runs (z + 1) ≤ J * cumWt runs lo := Nat.mul_le_mul_left J h2
      omega
    have hhi_le_z : hi ≤ z := by omega
    have hchi : J * cumWt runs hi ≤ J * cumWt runs z :=
      Nat.mul_le_mul_left J (cumWt_mono runs hhi_le_z)
    have hmul_add : J * cumWt runs hi = J * cumWt runs lo + J * wtInterval runs lo hi := by
      rw [hcum_add]; ring
    have hrM : r * M = q * M + M := by dsimp only [r]; ring
    omega
  · have hJm1 : J - 1 ≤ q := by omega
    have hqM : (J - 1) * M ≤ q * M := Nat.mul_le_mul_right M hJm1
    have hchi_M : cumWt runs hi ≤ M := by
      dsimp only [M]; rw [← cumWt_totalLen runs]; exact cumWt_mono runs hhi
    have hJchi : J * cumWt runs hi ≤ J * M := Nat.mul_le_mul_left J hchi_M
    have hmul_add : J * cumWt runs hi = J * cumWt runs lo + J * wtInterval runs lo hi := by
      rw [hcum_add]; ring
    have hJM : J * M = (J - 1) * M + M := by
      conv_lhs => rw [show J = (J - 1) + 1 by omega, Nat.add_mul, one_mul]
    omega

private theorem two_pow_le_factorial : ∀ k : ℕ, 1 ≤ k → 2 ^ (k - 1) ≤ k.factorial
  | 0, h => by omega
  | 1, _ => by simp
  | k + 2, _ => by
    have ih := two_pow_le_factorial (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at ih
    rw [show k + 2 - 1 = k + 1 by omega, pow_succ', Nat.factorial_succ]
    exact Nat.mul_le_mul (by omega) ih

private theorem geom_half_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 / 2 : ℚ) ^ k) + (1 / 2 : ℚ) ^ n * 2 = 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hpow : (1 / 2 : ℚ) ^ (n + 1) * 2 = (1 / 2 : ℚ) ^ n := by rw [pow_succ]; ring
    linarith

private theorem binom_bound (J : ℕ) (hJ : 1 ≤ J) : (J + 1) ^ J ≤ 3 * J ^ J := by
  have hJq : (0 : ℚ) < (J : ℚ) := Nat.cast_pos.mpr hJ
  have hJpow : (0 : ℚ) < (J : ℚ) ^ J := pow_pos hJq J
  suffices hq : (((J + 1) ^ J : ℕ) : ℚ) / (J : ℚ) ^ J ≤ 3 by
    have hq' : (((J + 1) ^ J : ℕ) : ℚ) ≤ 3 * (J : ℚ) ^ J := (div_le_iff₀ hJpow).mp hq
    exact_mod_cast hq'
  have h1 : (((J + 1) ^ J : ℕ) : ℚ) / (J : ℚ) ^ J = (1 + (1 / (J : ℚ))) ^ J := by
    rw [show (1 : ℚ) + 1 / (J : ℚ) = ((J : ℚ) + 1) / (J : ℚ) by field_simp [ne_of_gt hJq],
      div_pow]
    push_cast; rfl
  rw [h1, add_pow]
  have hterm : ∀ k ∈ Finset.range (J + 1),
      (1 : ℚ) ^ k * (1 / (J : ℚ)) ^ (J - k) * (J.choose k : ℚ) =
        (J.choose (J - k) : ℚ) / (J : ℚ) ^ (J - k) := by
    intro k hk
    have hkJ : k ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [one_pow, one_mul, one_div, inv_pow, ← div_eq_inv_mul, Nat.choose_symm hkJ]
  rw [Finset.sum_congr rfl hterm]
  -- Reindex `k ↦ J - k` via `Finset.sum_range_reflect`
  have href : (∑ k ∈ Finset.range (J + 1), (J.choose (J - k) : ℚ) / (J : ℚ) ^ (J - k)) =
      ∑ k ∈ Finset.range (J + 1), (J.choose k : ℚ) / (J : ℚ) ^ k := by
    simpa [Nat.add_sub_cancel] using
      Finset.sum_range_reflect (fun k => (J.choose k : ℚ) / (J : ℚ) ^ k) (J + 1)
  rw [href, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, div_one]
  have hle_half : ∀ k ∈ Finset.range J,
      (J.choose (k + 1) : ℚ) / (J : ℚ) ^ (k + 1) ≤ (1 / 2 : ℚ) ^ k := by
    intro k _
    have hdesc : (k + 1).factorial * J.choose (k + 1) ≤ J ^ (k + 1) := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow J (k + 1)
    have hpow2 : 2 ^ k ≤ (k + 1).factorial := by
      simpa using two_pow_le_factorial (k + 1) (by omega)
    have hmul : 2 ^ k * J.choose (k + 1) ≤ J ^ (k + 1) :=
      le_trans (Nat.mul_le_mul_right _ hpow2) hdesc
    have hmulq : (2 : ℚ) ^ k * (J.choose (k + 1) : ℚ) ≤ (J : ℚ) ^ (k + 1) := by exact_mod_cast hmul
    have h2pos : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
    have hJkpos : (0 : ℚ) < (J : ℚ) ^ (k + 1) := pow_pos hJq _
    rw [one_div, inv_pow, div_le_iff₀ hJkpos, inv_mul_eq_div, le_div_iff₀ h2pos]
    linarith
  have hsum_le : (∑ k ∈ Finset.range J, (J.choose (k + 1) : ℚ) / (J : ℚ) ^ (k + 1)) ≤
      ∑ k ∈ Finset.range J, (1 / 2 : ℚ) ^ k :=
    Finset.sum_le_sum hle_half
  have hgeom := geom_half_sum J
  have hnonneg : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ J * 2 := by positivity
  linarith

/- ### Main Correctness & Termination Proof for `mwuSolve` -/

theorem mwuSolve_correct
    (Good : GameInput → EquilibriumOutput → Prop)
    (hlp_spec : ∀ n cons, (∀ r ∈ cons, r.1.length = n) → (n = 0 ∨ cons ≠ []) →
      (∃ y : List ℚ, y.length = n ∧
        ∀ r ∈ cons, (∑ j : Fin n, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) →
      (lp (n, cons)).length = n ∧
      ∀ r ∈ cons, (∑ j : Fin n, r.1[j.val]?.getD 0 * (lp (n, cons))[j.val]?.getD 0) ≤ r.2)
    (g : GameInput)
    (hG_pos : 1 ≤ grid (g, eta g))
    (hpat_spec : ∀ x, let L := patLP (g, x)
      (∀ r ∈ L.2, r.1.length = L.1) ∧ (L.1 = 0 ∨ L.2 ≠ []) ∧
      ∀ y : List ℚ, y.length = L.1 →
        (∀ r ∈ L.2, (∑ j : Fin L.1, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) →
        Good g (decode (g, y)))
    (W : List (ℕ × ℕ × ℕ))
    (hW_len : W.length ≤ g.numTypes + g.numTargets)
    (hW_bnd : ∀ w ∈ W, w.1 < g.numTypes ∧ w.2.1 < g.numTargets ∧ w.2.2 < grid (g, eta g))
    (hW_spec : ∀ Q, let (x, B) := sweep ((g, eta g), Q); let L := patLP (g, x)
      (∃ y : List ℚ, y.length = L.1 ∧
        ∀ r ∈ L.2, (∑ j : Fin L.1, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) ∨
      ((∀ i < g.numTypes, ∀ j < g.numTargets, let b := (B[i]?.getD [])[j]?.getD (0, 0)
          b.1 ≤ b.2 ∧ b.2 ≤ grid (g, eta g) ∧ ∀ z ∈ (Q[i]?.getD [])[j]?.getD [], ¬(b.1 ≤ z ∧ z < b.2)) ∧
        ∃ w ∈ W, let b := (B[w.1]?.getD [])[w.2.1]?.getD (0, 0); b.1 ≤ w.2.2 ∧ w.2.2 < b.2)) :
    Good g (mwuSolve lp eta patLP decode grid sweep g) := by
  dsimp only [mwuSolve]
  set G := grid (g, eta g)
  have hG_if : (if decide (G = 0) then 1 else G) = G := by
    rw [decide_eq_false (by omega)]; rfl
  simp only [hG_if]
  set k := g.numTypes
  set m := g.numTargets
  have hk_def : g.2.2.length = k := rfl
  have hm_def : g.2.1.length = m := rfl
  set u_k := List.replicate g.2.2.length false
  set u_m := List.replicate g.2.1.length false
  set u_km1 := false :: (u_k ++ u_m)
  set u_J := (u_km1 ++ u_km1) ++ (u_km1 ++ u_km1)
  set u_Jm1 := u_J.tail
  set J := u_J.length
  set u_L := List.replicate (bitEncode G).length false
  set u_R := (unaryMulStep^[u_J.length] (u_L, [])).2
  have hJ_val : J = 4 * (k + m + 1) := by
    dsimp only [J, u_J, u_km1, u_k, u_m]
    simp [hk_def, hm_def]; omega
  have hJ_pos : 1 ≤ J := by omega
  have huJm1_len : u_Jm1.length = J - 1 := by
    dsimp only [u_Jm1, J]; simp
  set L := (bitEncode G).length
  have hL_pos : 1 ≤ L := by
    have hne : bitEncode G ≠ [] := by
      intro h; have := (encodeNat_eq_nil_iff G).mp h; omega
    cases h : bitEncode G with
    | nil => exact absurd h hne
    | cons _ _ => simp [L, h]
  have hG_lt_pow : G < 2 ^ L := lt_two_pow_bitEncode_nat G
  have hR_val : u_R.length = J * L := by
    dsimp only [u_R, u_L]
    have := (unaryMulStep_iter u_J.length (List.replicate L false) []).2
    simp only [List.length_replicate, List.length_nil, add_zero] at this
    exact this
  set R := u_R.length
  set initRow := List.replicate u_m.length [(G, 1)]
  set initTable : MWUTable := List.replicate u_k.length initRow
  set ctx : MWUCtx := ((g, eta g), (u_Jm1, J))
  set initState : MWUState := (ctx, (false, (([], []), initTable)))
  set step := mwuStep lp patLP decode sweep
  -- 1. Soundness invariant: whenever found = true, Good g ans holds
  have hsound : ∀ t, (step^[t] initState).1 = ctx ∧
      ((step^[t] initState).2.1 = true → Good g (step^[t] initState).2.2.1) := by
    intro t
    induction t with
    | zero => exact ⟨rfl, fun h => by cases h⟩
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      set st := step^[t] initState
      obtain ⟨hctx_t, hgood_t⟩ := ih
      by_cases hf : st.2.1 = true
      · have hst' : step st = st := mwuStep_of_true lp patLP decode sweep hf
        rw [hst']; exact ⟨hctx_t, hgood_t⟩
      · have hf' : st.2.1 = false := Bool.eq_false_iff.mpr hf
        set Q := tableQuantiles (st.1.2, st.2.2.2)
        set xB := sweep (st.1.1, Q)
        set LP := patLP (st.1.1.1, xB.1)
        set y := lp LP
        by_cases hchk : checkLP (LP, y) = true
        · have hst' : step st = (st.1, (true, (decode (st.1.1.1, y), st.2.2.2))) := by
            dsimp only [step]; rw [mwuStep_of_false lp patLP decode sweep hf']
            exact if_pos hchk
          rw [hst']
          refine ⟨hctx_t, fun _ => ?_⟩
          have hg1 : st.1.1.1 = g := by rw [hctx_t]
          rw [hg1]
          have hLP_eq : LP = patLP (g, xB.1) := by dsimp only [LP]; rw [hg1]
          obtain ⟨hrows, _, hdec_good⟩ := hpat_spec xB.1
          rw [hLP_eq] at hchk
          have hy_eq : y = lp (patLP (g, xB.1)) := by dsimp only [y]; rw [hLP_eq]
          rw [hy_eq] at hchk ⊢
          obtain ⟨hy_len, hy_feas⟩ := (checkLP_iff _ _ _ hrows).mp hchk
          exact hdec_good (lp (patLP (g, xB.1))) hy_len hy_feas
        · have hchk' : checkLP (LP, y) = false := Bool.eq_false_iff.mpr hchk
          have hst' : step st = (st.1, (false, (st.2.2.1, updateTable (st.2.2.2, xB.2)))) := by
            dsimp only [step]; rw [mwuStep_of_false lp patLP decode sweep hf']
            exact if_neg (by rw [hchk']; exact Bool.false_ne_true)
          rw [hst']
          exact ⟨hctx_t, fun h => by cases h⟩
  -- It suffices to show `(step^[R] initState).2.1 = true`
  suffices hterm : (step^[R] initState).2.1 = true by
    exact (hsound R).2 hterm
  -- 2. Prove termination by contradiction
  by_contra hnot_found
  have hfound_all : ∀ t ≤ R, (step^[t] initState).2.1 = false := by
    intro t ht
    by_contra ht_true
    have ht_eq : (step^[t] initState).2.1 = true := Bool.eq_true_of_not_eq_false ht_true
    have hsticky : ∀ d, (step^[t + d] initState).2.1 = true := by
      intro d; induction d with
      | zero => simpa using ht_eq
      | succ d ihd =>
        rw [← Nat.add_assoc, Function.iterate_succ_apply']
        have hnoop : step (step^[t + d] initState) = step^[t + d] initState :=
          mwuStep_of_true lp patLP decode sweep ihd
        rw [hnoop]; exact ihd
    have := hsticky (R - t)
    rw [Nat.add_sub_cancel' ht] at this
    exact hnot_found this
  -- Track table shape & cell invariants for all t ≤ R
  have htab_inv : ∀ t ≤ R,
      let tab := (step^[t] initState).2.2.2
      tab.length = k ∧
      ∀ i < k, (tab[i]?.getD []).length = m ∧
        ∀ j < m,
          let c := (tab[i]?.getD [])[j]?.getD []
          totalLen c = G ∧ (∀ r ∈ c, 1 ≤ r.2) := by
    intro t ht
    induction t with
    | zero =>
      simp only [Function.iterate_zero_apply]
      dsimp only [initState, initTable, initRow, u_k, u_m]
      refine ⟨by simp [hk_def], fun i hi => ?_⟩
      have hi' : i < g.2.2.length := hi
      simp only [List.length_replicate, List.getElem?_replicate, if_pos hi', Option.getD_some, hm_def]
      refine ⟨trivial, fun j hj => ?_⟩
      simp only [if_pos hj, Option.getD_some]
      refine ⟨by simp [totalLen], fun r hr => ?_⟩
      simp at hr; subst hr; omega
    | succ t ih =>
      obtain ⟨hlen_t, hrows_t⟩ := ih (by omega)
      have hf_t := hfound_all t (by omega)
      have hf_t1 := hfound_all (t + 1) ht
      rw [Function.iterate_succ_apply'] at hf_t1 ⊢
      set st := step^[t] initState
      set Q := tableQuantiles (st.1.2, st.2.2.2)
      set xB := sweep (st.1.1, Q)
      set LP := patLP (st.1.1.1, xB.1)
      set y := lp LP
      have hchk_f : checkLP (LP, y) = false := by
        by_contra hchk_t
        have hct : checkLP (LP, y) = true := Bool.eq_true_of_not_eq_false hchk_t
        have hst' : step st = (st.1, (true, (decode (st.1.1.1, y), st.2.2.2))) := by
          dsimp only [step]; rw [mwuStep_of_false lp patLP decode sweep hf_t]
          exact if_pos hct
        rw [hst'] at hf_t1; cases hf_t1
      have hst' : step st = (st.1, (false, (st.2.2.1, updateTable (st.2.2.2, xB.2)))) := by
        dsimp only [step]; rw [mwuStep_of_false lp patLP decode sweep hf_t]
        exact if_neg (by rw [hchk_f]; exact Bool.false_ne_true)
      rw [hst']
      dsimp only [updateTable]
      refine ⟨by rw [zipMapD_length, hlen_t], fun i hi => ?_⟩
      rw [zipMapD_getElem?]
      have hi_tab : i < st.2.2.2.length := by omega
      have hsi : st.2.2.2[i]? = some st.2.2.2[i] := List.getElem?_eq_getElem hi_tab
      rw [hsi, Option.map_some, Option.getD_some]
      obtain ⟨hrow_len, hcells⟩ := hrows_t i hi
      rw [hsi, Option.getD_some] at hrow_len hcells
      dsimp only [updateRow]
      refine ⟨by rw [zipMapD_length, hrow_len], fun j hj => ?_⟩
      rw [zipMapD_getElem?]
      have hj_row : j < st.2.2.2[i].length := by omega
      have hsj : st.2.2.2[i][j]? = some st.2.2.2[i][j] := List.getElem?_eq_getElem hj_row
      rw [hsj, Option.map_some, Option.getD_some]
      obtain ⟨hclen, hcwt⟩ := hcells j hj
      rw [hsj, Option.getD_some] at hclen hcwt
      rw [doubleRuns_eq]
      exact ⟨by rw [doubleRunsAux_totalLen, hclen], doubleRunsAux_pos_wt _ _ _ hcwt⟩
  -- For every round t < R, extract the blocker intervals & captured witness
  have hround_blk : ∀ t < R,
      let tab := (step^[t] initState).2.2.2
      let Q := tableQuantiles ((u_Jm1, J), tab)
      let xB := sweep ((g, eta g), Q)
      (step^[t + 1] initState).2.2.2 = updateTable (tab, xB.2) ∧
      (∀ i < k, ∀ j < m,
        let b := (xB.2[i]?.getD [])[j]?.getD (0, 0)
        b.1 ≤ b.2 ∧ b.2 ≤ G ∧
        ∀ z ∈ cellQuantiles ((u_Jm1, J), (tab[i]?.getD [])[j]?.getD []), ¬(b.1 ≤ z ∧ z < b.2)) ∧
      ∃ idx : Fin W.length,
        let w := W[idx]
        let b := (xB.2[w.1]?.getD [])[w.2.1]?.getD (0, 0)
        b.1 ≤ w.2.2 ∧ w.2.2 < b.2 := by
    intro t ht
    have hctx_t := (hsound t).1
    have hf_t := hfound_all t (by omega)
    have hf_t1 := hfound_all (t + 1) (by omega)
    rw [Function.iterate_succ_apply'] at hf_t1 ⊢
    set st := step^[t] initState
    have hQ_eq : tableQuantiles (st.1.2, st.2.2.2) = tableQuantiles ((u_Jm1, J), st.2.2.2) := by
      rw [hctx_t]
    have hxB_eq : sweep (st.1.1, tableQuantiles (st.1.2, st.2.2.2)) =
        sweep ((g, eta g), tableQuantiles ((u_Jm1, J), st.2.2.2)) := by
      rw [hQ_eq, hctx_t]
    set Q := tableQuantiles ((u_Jm1, J), st.2.2.2)
    set xB := sweep ((g, eta g), Q)
    have hLP_eq : patLP (st.1.1.1, (sweep (st.1.1, tableQuantiles (st.1.2, st.2.2.2))).1) =
        patLP (g, xB.1) := by rw [hxB_eq, hctx_t]
    have hchk_f : checkLP (patLP (g, xB.1), lp (patLP (g, xB.1))) = false := by
      by_contra hchk_t
      have hct : checkLP (patLP (g, xB.1), lp (patLP (g, xB.1))) = true := Bool.eq_true_of_not_eq_false hchk_t
      have hst' : step st = (st.1, (true, (decode (st.1.1.1, lp (patLP (g, xB.1))), st.2.2.2))) := by
        dsimp only [step]; rw [mwuStep_of_false lp patLP decode sweep hf_t]
        dsimp only; rw [hLP_eq, if_pos hct]
      rw [hst'] at hf_t1; cases hf_t1
    have hupd : (step st).2.2.2 = updateTable (st.2.2.2, xB.2) := by
      dsimp only [step]; rw [mwuStep_of_false lp patLP decode sweep hf_t]
      dsimp only; rw [hLP_eq, if_neg (by rw [hchk_f]; exact Bool.false_ne_true), hxB_eq]
    -- LP is infeasible
    have hinfeas : ¬ ∃ y : List ℚ, y.length = (patLP (g, xB.1)).1 ∧
        ∀ r ∈ (patLP (g, xB.1)).2,
          (∑ j : Fin (patLP (g, xB.1)).1, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2 := by
      intro hfeas
      obtain ⟨hrows, hne, _⟩ := hpat_spec xB.1
      have hlp_ok := hlp_spec (patLP (g, xB.1)).1 (patLP (g, xB.1)).2 hrows hne hfeas
      have hct := (checkLP_iff _ _ _ hrows).mpr hlp_ok
      rw [hct] at hchk_f; cases hchk_f
    -- Extract blocker property from hW_spec Q
    have hspec := hW_spec Q
    rcases hspec with hfeas | ⟨havoid, w, hw_mem, hw_hit⟩
    · exact absurd hfeas hinfeas
    · refine ⟨hupd, ?_, ?_⟩
      · intro i hi j hj
        obtain ⟨hb1, hb2, hbav⟩ := havoid i hi j hj
        refine ⟨hb1, hb2, fun z hz => hbav z ?_⟩
        obtain ⟨htab_len, hrows_t⟩ := htab_inv t (by omega)
        have hi_t : i < st.2.2.2.length := by change i < (step^[t] initState).2.2.2.length; omega
        have hj_t : j < (st.2.2.2[i]?.getD []).length := (hrows_t i hi).1 ▸ hj
        have hsi : st.2.2.2[i]? = some st.2.2.2[i] := List.getElem?_eq_getElem hi_t
        rw [hsi, Option.getD_some] at hj_t hz
        have hsj : st.2.2.2[i][j]? = some st.2.2.2[i][j] := List.getElem?_eq_getElem hj_t
        rw [hsj, Option.getD_some] at hz
        have hQi : Q[i]? = some (rowQuantiles ((u_Jm1, J), st.2.2.2[i])) := by
          dsimp only [Q, tableQuantiles]
          rw [List.getElem?_map, hsi, Option.map_some]
        have hQij : (Q[i]?.getD [])[j]? = some (cellQuantiles ((u_Jm1, J), st.2.2.2[i][j])) := by
          rw [hQi, Option.getD_some]
          dsimp only [rowQuantiles]
          rw [List.getElem?_map, hsj, Option.map_some]
        rw [hQij, Option.getD_some]
        exact hz
      · obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hw_mem
        exact ⟨⟨idx, hidx⟩, hw_hit⟩
  -- 3. Pigeonhole over W: pick a witness index hit at least 4 * L times
  have hR_pos : 0 < R := by rw [hR_val]; exact Nat.mul_pos hJ_pos hL_pos
  -- Choose hit witness index for each round t : Fin R
  let hitIdx (t : Fin R) : Fin W.length := Classical.choose (hround_blk t.val t.isLt).2.2
  have hhit_spec (t : Fin R) :
      let tab := (step^[t.val] initState).2.2.2
      let xB := sweep ((g, eta g), tableQuantiles ((u_Jm1, J), tab))
      let w := W[hitIdx t]
      let b := (xB.2[w.1]?.getD [])[w.2.1]?.getD (0, 0)
      b.1 ≤ w.2.2 ∧ w.2.2 < b.2 :=
    Classical.choose_spec (hround_blk t.val t.isLt).2.2
  have hex_heavy : ∃ idx : Fin W.length,
      4 * L ≤ (Finset.univ.filter (fun t : Fin R => hitIdx t = idx)).card := by
    by_contra hall
    push Not at hall
    have hsum_eq : ∑ idx : Fin W.length,
        (Finset.univ.filter (fun t : Fin R => hitIdx t = idx)).card = R := by
      have h := Finset.card_eq_sum_card_fiberwise (f := hitIdx) (s := Finset.univ)
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
      simpa using h.symm
    have hsum_le : ∑ idx : Fin W.length,
        (Finset.univ.filter (fun t : Fin R => hitIdx t = idx)).card ≤ W.length * (4 * L) := by
      calc ∑ idx : Fin W.length, (Finset.univ.filter (fun t : Fin R => hitIdx t = idx)).card
          ≤ ∑ _idx : Fin W.length, 4 * L := Finset.sum_le_sum (fun idx _ => Nat.le_of_lt (hall idx))
        _ = W.length * (4 * L) := by simp
    have hW_lt : W.length * (4 * L) < R := by
      rw [hR_val, hJ_val]
      have : W.length * (4 * L) ≤ (k + m) * (4 * L) := Nat.mul_le_mul_right _ hW_len
      have hstep_pos : 0 < 4 * L := by omega
      nlinarith
    omega
  obtain ⟨idx, hheavy⟩ := hex_heavy
  set w := W[idx]
  obtain ⟨hwi, hwj, hwz⟩ := hW_bnd w (List.getElem_mem idx.isLt)
  -- Track cell c(t) := ((step^[t] initState).2.2.2[w.1]?.getD [])[w.2.1]?.getD []
  let cell (t : ℕ) : List (ℕ × ℕ) := ((step^[t] initState).2.2.2[w.1]?.getD [])[w.2.1]?.getD []
  have hcell_0 : cell 0 = [(G, 1)] := by
    dsimp only [cell, initState, initTable, initRow, u_k, u_m]
    have hi' : w.1 < g.2.2.length := hwi
    have hj' : w.2.1 < g.2.1.length := hwj
    simp [hi', hj']
  have hcell_step : ∀ t < R,
      let xB := sweep ((g, eta g), tableQuantiles ((u_Jm1, J), (step^[t] initState).2.2.2))
      let b := (xB.2[w.1]?.getD [])[w.2.1]?.getD (0, 0)
      cell (t + 1) = doubleRunsAux (cell t) b.1 b.2 := by
    intro t ht
    obtain ⟨hupd, _, _⟩ := hround_blk t ht
    obtain ⟨htab_len, hrows_t⟩ := htab_inv t (by omega)
    dsimp only [cell]
    rw [hupd]
    dsimp only [updateTable]
    rw [zipMapD_getElem?]
    have hi_t : w.1 < (step^[t] initState).2.2.2.length := by omega
    have hsi : (step^[t] initState).2.2.2[w.1]? = some (step^[t] initState).2.2.2[w.1] :=
      List.getElem?_eq_getElem hi_t
    rw [hsi, Option.map_some, Option.getD_some]
    dsimp only [updateRow]
    rw [zipMapD_getElem?]
    have hrow_len := (hrows_t w.1 hwi).1
    rw [hsi, Option.getD_some] at hrow_len
    have hj_t : w.2.1 < (step^[t] initState).2.2.2[w.1].length := by omega
    have hsj : (step^[t] initState).2.2.2[w.1][w.2.1]? =
        some (step^[t] initState).2.2.2[w.1][w.2.1] := List.getElem?_eq_getElem hj_t
    rw [hsj, Option.map_some, Option.getD_some, doubleRuns_eq, Option.getD_some, hsj, Option.getD_some]
  -- 4. Lower bound on wtAt (cell R) w.2.2 via doubling count
  have hwt_lower : ∀ t ≤ R,
      2 ^ ((Finset.univ.filter (fun s : Fin R => s.val < t ∧ hitIdx s = idx)).card) ≤
        wtAt (cell t) w.2.2 := by
    intro t ht
    induction t with
    | zero =>
      have hemp : Finset.univ.filter (fun s : Fin R => s.val < 0 ∧ hitIdx s = idx) = ∅ := by
        ext s; simp
      rw [hemp, Finset.card_empty, pow_zero, hcell_0]
      simp [wtAt, hwz]
    | succ t ih =>
      have iht := ih (by omega)
      have hcs := hcell_step t (by omega)
      set xB := sweep ((g, eta g), tableQuantiles ((u_Jm1, J), (step^[t] initState).2.2.2))
      set b := (xB.2[w.1]?.getD [])[w.2.1]?.getD (0, 0)
      have hwa : wtAt (cell (t + 1)) w.2.2 =
          if b.1 ≤ w.2.2 ∧ w.2.2 < b.2 then 2 * wtAt (cell t) w.2.2 else wtAt (cell t) w.2.2 := by
        rw [hcs, doubleRunsAux_wtAt]
      let tFin : Fin R := ⟨t, by omega⟩
      by_cases hhit : hitIdx tFin = idx
      · have hcard : (Finset.univ.filter (fun s : Fin R => s.val < t + 1 ∧ hitIdx s = idx)).card =
            (Finset.univ.filter (fun s : Fin R => s.val < t ∧ hitIdx s = idx)).card + 1 := by
          have hset : Finset.univ.filter (fun s : Fin R => s.val < t + 1 ∧ hitIdx s = idx) =
              insert tFin (Finset.univ.filter (fun s : Fin R => s.val < t ∧ hitIdx s = idx)) := by
            ext s
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Fin.ext_iff, tFin]
            constructor
            · rintro ⟨hs1, hs2⟩
              by_cases heq : s.val = t
              · exact Or.inl heq
              · exact Or.inr ⟨by omega, hs2⟩
            · rintro (heq | ⟨hs1, hs2⟩)
              · refine ⟨by omega, ?_⟩
                have hs_eq : s = tFin := Fin.ext heq
                rw [hs_eq]; exact congrArg Fin.val hhit
              · exact ⟨by omega, hs2⟩
          rw [hset, Finset.card_insert_of_notMem]
          simp [tFin]
        have hhit_b : b.1 ≤ w.2.2 ∧ w.2.2 < b.2 := by
          have h := hhit_spec tFin
          have hhit_val : (hitIdx tFin).val = idx.val := congrArg Fin.val hhit
          simpa [w, hhit_val, tFin, xB, b] using h
        rw [hcard, pow_succ', hwa, if_pos hhit_b]
        exact Nat.mul_le_mul_left 2 iht
      · have hset : Finset.univ.filter (fun s : Fin R => s.val < t + 1 ∧ hitIdx s = idx) =
            Finset.univ.filter (fun s : Fin R => s.val < t ∧ hitIdx s = idx) := by
          ext s
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hs1, hs2⟩
            refine ⟨?_, hs2⟩
            by_contra hge
            have hs_eq : s = tFin := Fin.ext (show s.val = t by omega)
            rw [hs_eq] at hs2
            exact hhit hs2
          · rintro ⟨hs1, hs2⟩; exact ⟨by omega, hs2⟩
        rw [hset, hwa]
        split_ifs <;> omega
  have hwt_R : 16 ^ L ≤ wtAt (cell R) w.2.2 := by
    have h1 := hwt_lower R le_rfl
    have hset : Finset.univ.filter (fun s : Fin R => s.val < R ∧ hitIdx s = idx) =
        Finset.univ.filter (fun s : Fin R => hitIdx s = idx) := by
      ext s; simp
    rw [hset] at h1
    have h16 : 16 ^ L = 2 ^ (4 * L) := by rw [pow_mul]; norm_num
    rw [h16]
    exact le_trans (Nat.pow_le_pow_right (by omega) hheavy) h1
  -- 5. Upper bound on totalWt (cell R) via quantile avoidance + binomial bound
  have hM_upper : ∀ t ≤ R, J ^ t * totalWt (cell t) ≤ (J + 1) ^ t * G := by
    intro t ht
    induction t with
    | zero =>
      simp [hcell_0, totalWt]
    | succ t ih =>
      have iht := ih (by omega)
      have hcs := hcell_step t (by omega)
      obtain ⟨_, havoid, _⟩ := hround_blk t (by omega)
      obtain ⟨hb1, hb2, hbav⟩ := havoid w.1 hwi w.2.1 hwj
      obtain ⟨_, hrows_t⟩ := htab_inv t (by omega)
      obtain ⟨hclen, hcwt⟩ := (hrows_t w.1 hwi).2 w.2.1 hwj
      set xB := sweep ((g, eta g), tableQuantiles ((u_Jm1, J), (step^[t] initState).2.2.2))
      set b := (xB.2[w.1]?.getD [])[w.2.1]?.getD (0, 0)
      have hqa : J * wtInterval (cell t) b.1 b.2 ≤ totalWt (cell t) :=
        quantile_avoidance_bound u_Jm1 J (cell t) b.1 b.2 hJ_pos huJm1_len hcwt
          (by rw [hclen]; exact hG_pos) hb1 (by rw [hclen]; exact hb2) hbav
      have htot_step : totalWt (cell (t + 1)) = totalWt (cell t) + wtInterval (cell t) b.1 b.2 := by
        rw [hcs]; exact doubleRunsAux_totalWt (cell t) b.1 b.2 hb1 (by rw [hclen]; exact hb2)
      have hJ_step : J * totalWt (cell (t + 1)) ≤ (J + 1) * totalWt (cell t) := by
        rw [htot_step, Nat.mul_add, Nat.add_mul, one_mul]; omega
      calc J ^ (t + 1) * totalWt (cell (t + 1))
          = J ^ t * (J * totalWt (cell (t + 1))) := by rw [pow_succ]; ring
        _ ≤ J ^ t * ((J + 1) * totalWt (cell t)) := Nat.mul_le_mul_left _ hJ_step
        _ = (J + 1) * (J ^ t * totalWt (cell t)) := by ring
        _ ≤ (J + 1) * ((J + 1) ^ t * G) := Nat.mul_le_mul_left _ iht
        _ = (J + 1) ^ (t + 1) * G := by rw [pow_succ']; ring
  have hMR_le : totalWt (cell R) ≤ 3 ^ L * G := by
    have h1 := hM_upper R le_rfl
    have hbin := binom_bound J hJ_pos
    have hpow_bin : (J + 1) ^ R ≤ 3 ^ L * J ^ R := by
      rw [hR_val, pow_mul, pow_mul, ← mul_pow]
      exact Nat.pow_le_pow_left hbin L
    have h2 : J ^ R * totalWt (cell R) ≤ J ^ R * (3 ^ L * G) := by
      calc J ^ R * totalWt (cell R)
          ≤ (J + 1) ^ R * G := h1
        _ ≤ (3 ^ L * J ^ R) * G := Nat.mul_le_mul_right G hpow_bin
        _ = J ^ R * (3 ^ L * G) := by ring
    exact Nat.le_of_mul_le_mul_left h2 (pow_pos hJ_pos R)
  -- 6. Final contradiction: 16^L ≤ wtAt (cell R) w.2.2 ≤ totalWt (cell R) ≤ 3^L * G < 6^L < 16^L
  have hlt1 : 3 ^ L * G < 6 ^ L := by
    have hmul : 3 ^ L * G < 3 ^ L * 2 ^ L := Nat.mul_lt_mul_of_pos_left hG_lt_pow (by positivity)
    rwa [← mul_pow] at hmul
  have hlt2 : 6 ^ L < 16 ^ L := Nat.pow_lt_pow_left (by omega) (by omega)
  have hle_tot : wtAt (cell R) w.2.2 ≤ totalWt (cell R) := wtAt_le_totalWt (cell R) w.2.2
  omega

end MWUEngine

end OMA.Helpers

theorem OMA.solution : OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R3.H4 := by
  intro Good lp eta patLP decode grid sweep hlp heta hpat hdec hgrid hsweep hlp_spec hgame_spec
  refine ⟨OMA.Helpers.mwuSolve lp eta patLP decode grid sweep,
    OMA.Helpers.isPolyTime_mwuSolve lp eta patLP decode grid sweep hlp heta hpat hdec hgrid hsweep,
    fun g hg => ?_⟩
  obtain ⟨hG_pos, hpat_spec, W, hW_len, hW_bnd, hW_spec⟩ := hgame_spec g hg
  exact OMA.Helpers.mwuSolve_correct lp eta patLP decode grid sweep Good hlp_spec g
    hG_pos hpat_spec W hW_len hW_bnd hW_spec
