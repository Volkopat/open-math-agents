import OMAReductions.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H3_R1

-- Step H3 of reduction R2.H3.R1: generic polynomial-time binary search with exact
-- continued-fraction rational recovery.

/-!
# Generic Polynomial-Time Binary Search and Rational Recovery (`R2.H3.R1.H3`)

Given any `[BitstringEncoding α]`, a polynomial-time threshold oracle `dec : α × ℚ → Bool`,
and a polynomial `p : Polynomial ℕ`, we construct an `IsPolyTime` function `search : α → ℚ`
that recovers any exact rational cutoff `q ∈ [0, M]` with `q.den ≤ M` (`M = 2 ^ p.eval |x|`)
characterized on `[0, M]` by `dec (x, lam) = true ↔ lam ≤ q`.

## Architecture
1. **Core `FinTM2` combinators**: sequential composition (`isPolyTime_seq`), pairing
   (`isPolyTime_pair`), and polynomial-space-bounded unary iteration (`isPolyTime_iter`),
   plus subtype transport (`isPolyTime_ofSubtype_out`).
2. **4-stack Boolean `FinTM2` primitives**: projections, constants, `select`/`ite`,
   unary length & addition, binary `ℕ` primitives (`isZero`, `lsb`, `div2`, `mul2Add`,
   `add`, `subCmp`), and coprime-pair-to-`ℚ` encoding.
3. **Derived `IsPolyTime` arithmetic**: polynomial unary evaluation `p.eval |x|`,
   `2 ^ u.length`, schoolbook `natMul`, and restoring shift-subtract `natDivMod`.
4. **Oracle binary search + Euclidean rational recovery**:
   - Check `dec (x, M)`; if true, return `M`.
   - Binary search `B` integer bits and `3 * B + 1` fractional bits to obtain `a ∈ [0, M * D)`
     with `a / D ≤ q < (a + 1) / D` where `D = 2 ^ (3 * B + 1) = 2 * M ^ 3`.
   - Run `2 * B + 3` steps of the Euclidean convergent recurrence on `(a, D)` stopping when
     `r₁ = 0` or `q_next > M`. An elementary triangle inequality with `D = 2 * M ^ 3` shows
     `|p_curr * q.den - q_curr * q.num| < 1`, hence `p_curr / q_curr = q`.
-/

open Turing Computability ComplexityTheory StateTransition BitstringEncoding

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

/-- Lift an `IsPolyTime` function into a `BitstringEncoding.ofSubtype` codomain (zero overhead). -/
private theorem isPolyTime_ofSubtype_out {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {P : β → Prop} [DecidablePred P] (f : α → β) (hf : IsPolyTime f) (hP : ∀ x, P (f x)) :
    @IsPolyTime α (Subtype P) _ (BitstringEncoding.ofSubtype (p := P))
      (fun x => ⟨f x, hP x⟩) := by
  let _ : BitstringEncoding (Subtype P) := BitstringEncoding.ofSubtype (p := P)
  obtain ⟨Tf⟩ := hf
  exact ⟨{ tm := Tf.tm, inputAlphabet := Tf.inputAlphabet, outputAlphabet := Tf.outputAlphabet,
           time := Tf.time, outputsFun := Tf.outputsFun }⟩

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

private theorem isPolyTime_unaryAdd :
    IsPolyTime (fun p : List Bool × List Bool => p.1 ++ p.2) := by
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
  refine mkBoolPolyTime (fun p : List Bool × List Bool => p.1 ++ p.2)
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

/- ### Coprime Natural Pair to Rational (`coprimeToRat`) -/

private abbrev CoprimePair : Type := { p : ℕ × ℕ // p.2 ≠ 0 ∧ Nat.Coprime p.1 p.2 }

private instance instBitstringCoprimePair : BitstringEncoding CoprimePair :=
  BitstringEncoding.ofSubtype (p := fun p : ℕ × ℕ => p.2 ≠ 0 ∧ Nat.Coprime p.1 p.2)

private theorem bitEncode_rat_of_coprime (u v : ℕ) (hv : v ≠ 0) (hcop : Nat.Coprime u v) :
    bitEncode ((u : ℚ) / (v : ℚ)) = delimit (delimit (encodeNat u)) ++ encodeNat v := by
  have hq : ((u : ℚ) / (v : ℚ)) = Rat.mk' (u : ℤ) v hv (by simpa using hcop) := by
    rw [← Rat.num_div_den (Rat.mk' (u : ℤ) v hv (by simpa using hcop))]; rfl
  have hnum : ((u : ℚ) / (v : ℚ)).num = (u : ℤ) := by rw [hq]
  have hden : ((u : ℚ) / (v : ℚ)).den = v := by rw [hq]
  change delimit (delimit (encodeNat ((u : ℚ) / (v : ℚ)).num.toNat) ++
    encodeNat (-((u : ℚ) / (v : ℚ)).num).toNat) ++ encodeNat ((u : ℚ) / (v : ℚ)).den = _
  rw [hnum, hden]
  have hneg : (-(u : ℤ)).toNat = 0 := by omega
  simp [hneg, encodeNat_zero]

private theorem isPolyTime_coprimeToRat :
    IsPolyTime (fun p : CoprimePair => (p.val.1 : ℚ) / (p.val.2 : ℚ)) := by
  let prog : Fin 5 → TM2.Stmt (fun _ : Stk4 => Bool) (Fin 5) (Option Bool)
    | ⟨0, _⟩ => .pop Stk4.s0 (fun _ o => o) <|
        .branch (fun v => v == some true)
          (.pop Stk4.s0 (fun _ o => o) <|
            .push Stk4.s1 (fun v => v.getD false) (.goto fun _ => 0))
          (.push Stk4.s2 (fun _ => false) (.load (fun _ => none) (.goto fun _ => 1)))
    | ⟨1, _⟩ => .pop Stk4.s1 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push Stk4.s2 (fun v => v.getD false) <|
            .push Stk4.s2 (fun _ => true) (.goto fun _ => 1))
          (.goto fun _ => 2)
    | ⟨2, _⟩ => .pop Stk4.s2 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push Stk4.s1 (fun v => v.getD false) (.goto fun _ => 2))
          (.push Stk4.s0 (fun _ => false) (.goto fun _ => 3))
    | ⟨3, _⟩ => .pop Stk4.s1 (fun _ o => o) <|
        .branch (fun v => v.isSome)
          (.push Stk4.s0 (fun v => v.getD false) <|
            .push Stk4.s0 (fun _ => true) (.goto fun _ => 3))
          .halt
    | ⟨4, _⟩ => .halt
  refine mkBoolPolyTime (fun p : CoprimePair => (p.val.1 : ℚ) / (p.val.2 : ℚ))
    0 none prog (6 * Polynomial.X + 8) (fun ⟨⟨u, v⟩, hv, hcop⟩ => ?_)
  have h1 : ∀ (l rest s1 : List Bool) (o : Option Bool),
      (flip bind (TM2.step prog))^[l.length + 1]
        (some ⟨some 0, o, mk4 (delimit l ++ rest) s1 [] []⟩) =
      some ⟨some 1, none, mk4 rest (l.reverse ++ s1) [false] []⟩ := by
    intro l; induction l with
    | nil =>
      intro rest s1 o
      rw [List.length_nil, iter_step]; simp [delimit, prog]
    | cons x l ih =>
      intro rest s1 o
      rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [delimit, prog]); rw [ih rest (x :: s1) (some x)]
      simp
  have h2 : ∀ (s1 s0 s2 : List Bool) (o : Option Bool),
      (flip bind (TM2.step prog))^[s1.length + 1]
        (some ⟨some 1, o, mk4 s0 s1 s2 []⟩) =
      some ⟨some 2, none,
        mk4 s0 [] (s1.reverse.flatMap (fun b => [true, b]) ++ s2) []⟩ := by
    intro s1; induction s1 with
    | nil =>
      intro s0 s2 o
      rw [List.length_nil, iter_step]; simp [prog]; try rfl
    | cons x s1 ih =>
      intro s0 s2 o
      rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog]); rw [ih s0 (true :: x :: s2) (some x)]
      simp
  have h3 : ∀ (s2 s0 s1 : List Bool) (o : Option Bool),
      (flip bind (TM2.step prog))^[s2.length + 1]
        (some ⟨some 2, o, mk4 s0 s1 s2 []⟩) =
      some ⟨some 3, none, mk4 (false :: s0) (s2.reverse ++ s1) [] []⟩ := by
    intro s2; induction s2 with
    | nil =>
      intro s0 s1 o
      rw [List.length_nil, iter_step]; simp [prog]; try rfl
    | cons x s2 ih =>
      intro s0 s1 o
      rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog]); rw [ih s0 (x :: s1) (some x)]
      simp
  have h4 : ∀ (s1 s0 : List Bool) (o : Option Bool),
      (flip bind (TM2.step prog))^[s1.length + 1]
        (some ⟨some 3, o, mk4 s0 s1 [] []⟩) =
      some ⟨none, none, mk4 (s1.reverse.flatMap (fun b => [true, b]) ++ s0) [] [] []⟩ := by
    intro s1; induction s1 with
    | nil =>
      intro s0 o
      rw [List.length_nil, iter_step]; simp [prog]; try rfl
    | cons x s1 ih =>
      intro s0 o
      rw [List.length_cons, iter_step]; (conv_lhs => arg 3; simp [prog]); rw [ih (true :: x :: s0) (some x)]
      simp
  have hflat : ∀ (l rest : List Bool),
      l.flatMap (fun b => [true, b]) ++ false :: rest = delimit l ++ rest := by
    intro l rest; simpa [List.map_id] using delim_map id rest l
  have hp1 := h1 (encodeNat u) (encodeNat v) [] none
  simp only [List.append_nil] at hp1
  have hp2 := h2 (encodeNat u).reverse (encodeNat v) [false] none
  simp only [List.length_reverse, List.reverse_reverse] at hp2
  rw [hflat (encodeNat u) [], List.append_nil] at hp2
  have hp3 := h3 (delimit (encodeNat u)) (encodeNat v) [] none
  simp only [List.append_nil] at hp3
  have hp4 := h4 (delimit (encodeNat u)).reverse (false :: encodeNat v) none
  simp only [List.length_reverse, List.reverse_reverse] at hp4
  rw [hflat (delimit (encodeNat u)) (encodeNat v)] at hp4
  rw [bitEncode_rat_of_coprime u v hv hcop]
  refine ⟨_, ?_, iter_trans (iter_trans (iter_trans hp1 hp2) hp3) hp4⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]; change _ ≤ 6 * (delimit (encodeNat u) ++ encodeNat v).length + 8
  rw [List.length_append, length_delimit]; omega

/- ## Section 3: Derived `IsPolyTime` Arithmetic (`polyUnary`, `shiftLeft`, `natMul`, `natDivMod`) -/

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

private theorem isPolyTime_polyUnary {α : Type} [BitstringEncoding α] (p : Polynomial ℕ) :
    IsPolyTime (fun x : α => List.replicate (p.eval (bitEncode x).length) false) := by
  have hpow : ∀ n : ℕ, IsPolyTime (fun x : α => List.replicate ((bitEncode x).length ^ n) false) := by
    intro n; induction n with
    | zero => simpa using (isPolyTime_const (α := α) [false])
    | succ n ih =>
      have hfn : (fun x : α => List.replicate ((bitEncode x).length ^ (n + 1)) false) =
          fun x => (unaryMulStep^[(List.replicate ((bitEncode x).length ^ n) false).length]
            (List.replicate (bitEncode x).length false, [])).2 := by
        funext x
        rw [List.length_replicate, unaryMulStep_replicate, pow_succ]
      rw [hfn]
      simpa using isPolyTime_seq (isPolyTime_pair ih isPolyTime_unaryLen) isPolyTime_uRepeat
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hfn : (fun x : α => List.replicate ((p + q).eval (bitEncode x).length) false) =
        fun x => List.replicate (p.eval (bitEncode x).length) false ++
          List.replicate (q.eval (bitEncode x).length) false := by
      funext x; rw [Polynomial.eval_add, List.replicate_add]
    rw [hfn]
    exact isPolyTime_seq (isPolyTime_pair hp hq) isPolyTime_unaryAdd
  | monomial n c =>
    have hfn : (fun x : α => List.replicate ((Polynomial.monomial n c).eval (bitEncode x).length) false) =
        fun x => (unaryMulStep^[(List.replicate c false).length]
          (List.replicate ((bitEncode x).length ^ n) false, [])).2 := by
      funext x
      rw [Polynomial.eval_monomial, List.length_replicate, unaryMulStep_replicate]
    rw [hfn]
    simpa using isPolyTime_seq (isPolyTime_pair (isPolyTime_const (List.replicate c false)) (hpow n))
      isPolyTime_uRepeat

/- ### Shift Left (`n * 2 ^ u.length`) and `pow2` -/

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

/- ## Section 4: Oracle Binary Search and Euclidean Continued-Fraction Recovery -/

section SearchAndCF

variable {α : Type} [BitstringEncoding α]

private theorem coprime_odd_pow2 (a k : ℕ) : Nat.Coprime (2 * a + 1) (2 ^ k) :=
  Nat.Coprime.pow_right k (by
    rw [Nat.coprime_comm]
    exact Nat.coprime_two_left.mpr ⟨a, rfl⟩)

/- ### Integer Binary Search (`binSearchInt`) -/

private def bsIntStep (dec : α × ℚ → Bool) (s : α × (ℕ × ℕ)) : α × (ℕ × ℕ) :=
  let cand := s.2.1 + s.2.2
  if dec (s.1, (cand : ℚ)) then (s.1, (cand, s.2.2 / 2)) else (s.1, (s.2.1, s.2.2 / 2))

omit [BitstringEncoding α] in
private theorem bsIntStep_bound (dec : α × ℚ → Bool) (k : ℕ) (x : α) (a step : ℕ) :
    ((bsIntStep dec)^[k] (x, (a, step))).1 = x ∧
    ((bsIntStep dec)^[k] (x, (a, step))).2.2 ≤ step ∧
    ((bsIntStep dec)^[k] (x, (a, step))).2.1 + 2 * ((bsIntStep dec)^[k] (x, (a, step))).2.2 ≤
      a + 2 * step := by
  induction k generalizing a step with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    by_cases h : dec (x, ((a + step : ℕ) : ℚ)) = true
    · have hs : bsIntStep dec (x, (a, step)) = (x, (a + step, step / 2)) := by
        simp only [bsIntStep, h, ↓reduceIte]
      rw [hs]
      obtain ⟨h1, h2, h3⟩ := ih (a + step) (step / 2)
      refine ⟨h1, le_trans h2 (Nat.div_le_self step 2), by omega⟩
    · have hf : dec (x, ((a + step : ℕ) : ℚ)) = false := by cases h' : dec (x, ((a + step : ℕ) : ℚ)) <;> simp_all
      have hs : bsIntStep dec (x, (a, step)) = (x, (a, step / 2)) := by
        simp only [bsIntStep, hf, Bool.false_eq_true, ↓reduceIte]
      rw [hs]
      obtain ⟨h1, h2, h3⟩ := ih a (step / 2)
      refine ⟨h1, le_trans h2 (Nat.div_le_self step 2), by omega⟩

private theorem isPolyTime_bsIntIter (dec : α × ℚ → Bool) (hdec : IsPolyTime dec) :
    IsPolyTime (fun p : List Bool × (α × (ℕ × ℕ)) => (bsIntStep dec)^[p.1.length] p.2) := by
  have hstep : IsPolyTime (bsIntStep dec) := by
    have hcand : IsPolyTime (fun s : α × (ℕ × ℕ) => s.2.1 + s.2.2) :=
      isPolyTime_seq isPolyTime_snd isPolyTime_natAdd
    have hcop : IsPolyTime (fun s : α × (ℕ × ℕ) =>
        (⟨(s.2.1 + s.2.2, 1), one_ne_zero, Nat.coprime_one_right _⟩ : CoprimePair)) :=
      isPolyTime_ofSubtype_out (fun s : α × (ℕ × ℕ) => (s.2.1 + s.2.2, 1))
        (isPolyTime_pair hcand (isPolyTime_const 1))
        (fun s => ⟨one_ne_zero, Nat.coprime_one_right _⟩)
    have hrat : IsPolyTime (fun s : α × (ℕ × ℕ) => ((s.2.1 + s.2.2 : ℕ) : ℚ)) := by
      have hfn : (fun s : α × (ℕ × ℕ) => ((s.2.1 + s.2.2 : ℕ) : ℚ)) =
          fun s => ((⟨(s.2.1 + s.2.2, 1), one_ne_zero, Nat.coprime_one_right _⟩ : CoprimePair).val.1 : ℚ) /
            ((⟨(s.2.1 + s.2.2, 1), one_ne_zero, Nat.coprime_one_right _⟩ : CoprimePair).val.2 : ℚ) := by
        funext s; simp
      rw [hfn]
      exact isPolyTime_seq hcop isPolyTime_coprimeToRat
    have hcond : IsPolyTime (fun s : α × (ℕ × ℕ) => dec (s.1, ((s.2.1 + s.2.2 : ℕ) : ℚ))) :=
      isPolyTime_seq (isPolyTime_pair isPolyTime_fst hrat) hdec
    have hdiv : IsPolyTime (fun s : α × (ℕ × ℕ) => s.2.2 / 2) :=
      isPolyTime_seq (isPolyTime_seq isPolyTime_snd isPolyTime_snd) isPolyTime_natDiv2
    exact isPolyTime_ite hcond
      (isPolyTime_pair isPolyTime_fst (isPolyTime_pair hcand hdiv))
      (isPolyTime_pair isPolyTime_fst (isPolyTime_pair (isPolyTime_seq isPolyTime_snd isPolyTime_fst) hdiv))
  refine isPolyTime_iter (bsIntStep dec) hstep (4 * Polynomial.X + 8) (fun u ⟨x, a, step⟩ k _ => ?_)
  obtain ⟨h1, h2, h3⟩ := bsIntStep_bound dec k x a step
  set st := (bsIntStep dec)^[k] (x, (a, step))
  have hstep_len : (bitEncode st.2.2).length ≤ (bitEncode step).length :=
    length_encodeNat_le (lt_of_le_of_lt h2 (lt_two_pow_length_encodeNat step))
  have ha_len : (bitEncode st.2.1).length ≤ max (bitEncode a).length ((bitEncode step).length + 1) + 1 := by
    have hlt_a : a < 2 ^ (bitEncode a).length := lt_two_pow_bitEncode_nat a
    have hlt_s : 2 * step < 2 ^ ((bitEncode step).length + 1) := by
      rw [pow_succ]; have := lt_two_pow_bitEncode_nat step; omega
    have hm1 : 2 ^ (bitEncode a).length ≤ 2 ^ max (bitEncode a).length ((bitEncode step).length + 1) :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have hm2 : 2 ^ ((bitEncode step).length + 1) ≤
        2 ^ max (bitEncode a).length ((bitEncode step).length + 1) :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have h3' : st.2.1 + 2 * st.2.2 ≤ a + 2 * step := h3
    have hlt : st.2.1 < 2 ^ (max (bitEncode a).length ((bitEncode step).length + 1) + 1) := by
      rw [pow_succ]; omega
    exact length_encodeNat_le hlt
  have hL : (bitEncode (u, (x, (a, step)))).length =
      2 * (3 * u.length) + 1 + (2 * (bitEncode x).length + 1 +
        (2 * (bitEncode a).length + 1 + (bitEncode step).length)) := by
    rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len, bitEncode_listBool_length]
  have hst_len : (bitEncode st).length =
      2 * (bitEncode st.1).length + 1 + (2 * (bitEncode st.2.1).length + 1 + (bitEncode st.2.2).length) := by
    rw [bitEncode_pair_len, bitEncode_pair_len]
  have h1' : st.1 = x := h1
  change (bitEncode st).length ≤ _
  rw [hst_len, h1']
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

omit [BitstringEncoding α] in
private theorem bsIntStep_spec (dec : α × ℚ → Bool) (x : α) (q : ℚ) (B : ℕ)
    (hq0 : 0 ≤ q) (hqM : q < ((2 ^ B : ℕ) : ℚ))
    (hor : ∀ lam : ℚ, 0 ≤ lam → lam ≤ ((2 ^ B : ℕ) : ℚ) → (dec (x, lam) = true ↔ lam ≤ q)) :
    ∀ k ≤ B,
      let st := (bsIntStep dec)^[k] (x, (0, 2 ^ B / 2))
      st.1 = x ∧
      st.2.1 + 2 ^ (B - k) ≤ 2 ^ B ∧
      (st.2.1 : ℚ) ≤ q ∧
      q < ((st.2.1 + 2 ^ (B - k) : ℕ) : ℚ) ∧
      (k < B → st.2.2 = 2 ^ (B - 1 - k)) := by
  intro k
  induction k with
  | zero =>
    intro _
    dsimp only
    simp only [Function.iterate_zero, id_eq, Nat.sub_zero, zero_add, Nat.cast_zero]
    refine ⟨trivial, le_rfl, hq0, hqM, fun hB => ?_⟩
    have hpow : 2 ^ B = 2 ^ (B - 1) * 2 := by
      conv_lhs => rw [show B = (B - 1) + 1 by omega, pow_succ]
    rw [hpow, Nat.mul_div_cancel _ (by omega)]
  | succ k ih =>
    intro hk
    obtain ⟨hx, hle, hlo, hhi, hstep_eq⟩ := ih (by omega)
    have hltB : k < B := by omega
    have hs_eq : ((bsIntStep dec)^[k] (x, (0, 2 ^ B / 2))).2.2 = 2 ^ (B - 1 - k) := hstep_eq hltB
    set st := (bsIntStep dec)^[k] (x, (0, 2 ^ B / 2))
    have hpow2 : 2 ^ (B - k) = 2 ^ (B - 1 - k) + 2 ^ (B - 1 - k) := by
      have hexp : B - k = (B - 1 - k) + 1 := by omega
      rw [hexp, pow_succ]; ring
    have hnext_exp : B - (k + 1) = B - 1 - k := by omega
    have hcand_le : st.2.1 + 2 ^ (B - 1 - k) ≤ 2 ^ B := by omega
    have hcand_le_q : ((st.2.1 + 2 ^ (B - 1 - k) : ℕ) : ℚ) ≤ ((2 ^ B : ℕ) : ℚ) := by
      exact_mod_cast hcand_le
    have hdiv_step : (2 ^ (B - 1 - k)) / 2 = if k + 1 < B then 2 ^ (B - 1 - (k + 1)) else 0 := by
      split_ifs with hlt
      · have hexp : B - 1 - k = (B - 1 - (k + 1)) + 1 := by omega
        rw [hexp, pow_succ, Nat.mul_div_cancel _ (by omega)]
      · have heq0 : B - 1 - k = 0 := by omega
        rw [heq0]; rfl
    rw [Function.iterate_succ_apply']
    change let st' := bsIntStep dec st; _
    by_cases hdec_t : dec (x, ((st.2.1 + 2 ^ (B - 1 - k) : ℕ) : ℚ)) = true
    · have hst' : bsIntStep dec st = (x, (st.2.1 + 2 ^ (B - 1 - k), 2 ^ (B - 1 - k) / 2)) := by
        simp only [bsIntStep, hx, hs_eq, hdec_t, ↓reduceIte]
      have hq_ge : ((st.2.1 + 2 ^ (B - 1 - k) : ℕ) : ℚ) ≤ q :=
        (hor _ (Nat.cast_nonneg _) hcand_le_q).mp hdec_t
      dsimp only
      rw [hst', hnext_exp]
      refine ⟨rfl, by dsimp only; omega, hq_ge, ?_, fun hlt => by rw [hdiv_step, if_pos hlt]⟩
      dsimp only
      rw [show st.2.1 + 2 ^ (B - 1 - k) + 2 ^ (B - 1 - k) = st.2.1 + 2 ^ (B - k) by rw [hpow2]; ring]
      exact hhi
    · have hdec_f : dec (x, ((st.2.1 + 2 ^ (B - 1 - k) : ℕ) : ℚ)) = false := by
        cases h' : dec (x, ((st.2.1 + 2 ^ (B - 1 - k) : ℕ) : ℚ)) <;> simp_all
      have hst' : bsIntStep dec st = (x, (st.2.1, 2 ^ (B - 1 - k) / 2)) := by
        simp only [bsIntStep, hx, hs_eq, hdec_f, Bool.false_eq_true, ↓reduceIte]
      have hq_lt : q < ((st.2.1 + 2 ^ (B - 1 - k) : ℕ) : ℚ) := by
        by_contra hnot
        push Not at hnot
        exact hdec_t ((hor _ (Nat.cast_nonneg _) hcand_le_q).mpr hnot)
      dsimp only
      rw [hst', hnext_exp]
      exact ⟨rfl, by omega, hlo, hq_lt, fun hlt => by rw [hdiv_step, if_pos hlt]⟩

/- ### Fractional Binary Search (`binSearchFrac`) -/

private def bsFracStep (dec : α × ℚ → Bool) (s : α × (ℕ × List Bool)) : α × (ℕ × List Bool) :=
  let lam : ℚ := ((2 * s.2.1 + 1 : ℕ) : ℚ) / ((2 ^ s.2.2.length : ℕ) : ℚ)
  (s.1, (2 * s.2.1 + if dec (s.1, lam) then 1 else 0, false :: s.2.2))

omit [BitstringEncoding α] in
private theorem bsFracStep_bound (dec : α × ℚ → Bool) (k : ℕ) (x : α) (a : ℕ) (ud : List Bool) :
    ((bsFracStep dec)^[k] (x, (a, ud))).1 = x ∧
    ((bsFracStep dec)^[k] (x, (a, ud))).2.2.length = ud.length + k ∧
    (bitEncode ((bsFracStep dec)^[k] (x, (a, ud))).2.1).length ≤ (bitEncode a).length + k := by
  induction k generalizing a ud with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    set b := dec (x, ((2 * a + 1 : ℕ) : ℚ) / ((2 ^ ud.length : ℕ) : ℚ))
    have hs : bsFracStep dec (x, (a, ud)) = (x, (2 * a + if b then 1 else 0, false :: ud)) := rfl
    rw [hs]
    obtain ⟨h1, h2, h3⟩ := ih (2 * a + if b then 1 else 0) (false :: ud)
    have halen : (bitEncode (2 * a + if b then 1 else 0)).length ≤ (bitEncode a).length + 1 := by
      cases b with
      | true =>
        change (encodeNat (2 * a + 1)).length ≤ (encodeNat a).length + 1
        rw [encodeNat_bit1, List.length_cons]
      | false =>
        by_cases ha : a = 0
        · subst ha; simp [bitEncode_nat_eq, encodeNat_zero]
        · change (encodeNat (2 * a)).length ≤ (encodeNat a).length + 1
          rw [encodeNat_bit0 ha, List.length_cons]
    refine ⟨h1, by rw [h2, List.length_cons]; omega, by omega⟩

private theorem isPolyTime_bsFracIter (dec : α × ℚ → Bool) (hdec : IsPolyTime dec) :
    IsPolyTime (fun p : List Bool × (α × (ℕ × List Bool)) => (bsFracStep dec)^[p.1.length] p.2) := by
  have hstep : IsPolyTime (bsFracStep dec) := by
    have hnum : IsPolyTime (fun s : α × (ℕ × List Bool) => 2 * s.2.1 + 1) := by
      have h : (fun s : α × (ℕ × List Bool) => 2 * s.2.1 + 1) =
          fun s => 2 * s.2.1 + if true then 1 else 0 := rfl
      rw [h]
      simpa using isPolyTime_seq
        (isPolyTime_pair (isPolyTime_seq isPolyTime_snd isPolyTime_fst) (isPolyTime_const true))
        isPolyTime_natMul2Add
    have hden : IsPolyTime (fun s : α × (ℕ × List Bool) => 2 ^ s.2.2.length) :=
      isPolyTime_seq (f := fun s : α × (ℕ × List Bool) => s.2.2) (g := fun u : List Bool => 2 ^ u.length)
        (isPolyTime_seq isPolyTime_snd isPolyTime_snd) isPolyTime_pow2
    have hcop : IsPolyTime (fun s : α × (ℕ × List Bool) =>
        (⟨(2 * s.2.1 + 1, 2 ^ s.2.2.length), by positivity,
          coprime_odd_pow2 s.2.1 s.2.2.length⟩ : CoprimePair)) :=
      isPolyTime_ofSubtype_out (fun s : α × (ℕ × List Bool) => (2 * s.2.1 + 1, 2 ^ s.2.2.length))
        (isPolyTime_pair hnum hden)
        (fun s => ⟨by positivity, coprime_odd_pow2 s.2.1 s.2.2.length⟩)
    have hlam : IsPolyTime (fun s : α × (ℕ × List Bool) =>
        ((2 * s.2.1 + 1 : ℕ) : ℚ) / ((2 ^ s.2.2.length : ℕ) : ℚ)) :=
      isPolyTime_seq hcop isPolyTime_coprimeToRat
    have hans : IsPolyTime (fun s : α × (ℕ × List Bool) =>
        dec (s.1, ((2 * s.2.1 + 1 : ℕ) : ℚ) / ((2 ^ s.2.2.length : ℕ) : ℚ))) :=
      isPolyTime_seq (isPolyTime_pair isPolyTime_fst hlam) hdec
    have hna : IsPolyTime (fun s : α × (ℕ × List Bool) =>
        2 * s.2.1 + if dec (s.1, ((2 * s.2.1 + 1 : ℕ) : ℚ) / ((2 ^ s.2.2.length : ℕ) : ℚ))
          then 1 else 0) :=
      isPolyTime_seq (isPolyTime_pair (isPolyTime_seq isPolyTime_snd isPolyTime_fst) hans)
        isPolyTime_natMul2Add
    have hnu : IsPolyTime (fun s : α × (ℕ × List Bool) => false :: s.2.2) :=
      isPolyTime_seq (isPolyTime_seq isPolyTime_snd isPolyTime_snd) isPolyTime_unarySucc
    exact isPolyTime_pair isPolyTime_fst (isPolyTime_pair hna hnu)
  refine isPolyTime_iter (bsFracStep dec) hstep (6 * Polynomial.X + 8) (fun u ⟨x, a, ud⟩ k hk => ?_)
  obtain ⟨h1, h2, h3⟩ := bsFracStep_bound dec k x a ud
  set st := (bsFracStep dec)^[k] (x, (a, ud))
  have hL : (bitEncode (u, (x, (a, ud)))).length =
      2 * (3 * u.length) + 1 + (2 * (bitEncode x).length + 1 +
        (2 * (bitEncode a).length + 1 + 3 * ud.length)) := by
    rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_pair_len,
      bitEncode_listBool_length, bitEncode_listBool_length]
  have hst_len : (bitEncode st).length =
      2 * (bitEncode st.1).length + 1 + (2 * (bitEncode st.2.1).length + 1 + 3 * st.2.2.length) := by
    rw [bitEncode_pair_len, bitEncode_pair_len, bitEncode_listBool_length]
  have h1' : st.1 = x := h1
  have h2' : st.2.2.length = ud.length + k := h2
  have h3' : (bitEncode st.2.1).length ≤ (bitEncode a).length + k := h3
  change (bitEncode st).length ≤ _
  rw [hst_len, h1', h2']
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

omit [BitstringEncoding α] in
private theorem bsFracStep_spec (dec : α × ℚ → Bool) (x : α) (q : ℚ) (B a0 : ℕ)
    (ha0_lt : a0 < 2 ^ B) (hlo0 : (a0 : ℚ) ≤ q) (hhi0 : q < ((a0 + 1 : ℕ) : ℚ))
    (hor : ∀ lam : ℚ, 0 ≤ lam → lam ≤ ((2 ^ B : ℕ) : ℚ) → (dec (x, lam) = true ↔ lam ≤ q)) :
    ∀ k : ℕ,
      let st := (bsFracStep dec)^[k] (x, (a0, [false]))
      st.1 = x ∧
      st.2.2.length = k + 1 ∧
      st.2.1 < 2 ^ (B + k) ∧
      (st.2.1 : ℚ) / ((2 ^ k : ℕ) : ℚ) ≤ q ∧
      q < ((st.2.1 + 1 : ℕ) : ℚ) / ((2 ^ k : ℕ) : ℚ) := by
  intro k
  induction k with
  | zero =>
    dsimp only
    simp only [Function.iterate_zero, id_eq, List.length_singleton, pow_zero, Nat.cast_one, div_one,
      Nat.add_zero]
    exact ⟨trivial, trivial, ha0_lt, hlo0, hhi0⟩
  | succ k ih =>
    obtain ⟨hx, hud, hlt, hlo, hhi⟩ := ih
    set st := (bsFracStep dec)^[k] (x, (a0, [false]))
    set lam : ℚ := ((2 * st.2.1 + 1 : ℕ) : ℚ) / ((2 ^ (k + 1) : ℕ) : ℚ)
    have hlam0 : 0 ≤ lam := by positivity
    have hlamM : lam ≤ ((2 ^ B : ℕ) : ℚ) := by
      have hnum_le : 2 * st.2.1 + 1 ≤ 2 ^ B * 2 ^ (k + 1) := by
        rw [← pow_add, show B + (k + 1) = (B + k) + 1 by omega, pow_succ]; omega
      have hpos : (0 : ℚ) < ((2 ^ (k + 1) : ℕ) : ℚ) := by positivity
      rw [div_le_iff₀ hpos]
      exact_mod_cast hnum_le
    rw [Function.iterate_succ_apply']
    change let st' := bsFracStep dec st; _
    have hstep_lam : ((2 * st.2.1 + 1 : ℕ) : ℚ) / ((2 ^ st.2.2.length : ℕ) : ℚ) = lam := by
      rw [hud]
    have hpow_q : ((2 ^ (k + 1) : ℕ) : ℚ) = 2 * ((2 ^ k : ℕ) : ℚ) := by
      push_cast; rw [pow_succ]; ring
    by_cases hdec_t : dec (x, lam) = true
    · have hst' : bsFracStep dec st = (x, (2 * st.2.1 + 1, false :: st.2.2)) := by
        simp only [bsFracStep, hx, hstep_lam, hdec_t, ↓reduceIte]
      have hq_ge : lam ≤ q := (hor lam hlam0 hlamM).mp hdec_t
      dsimp only
      rw [hst']
      refine ⟨rfl, by rw [List.length_cons, hud], ?_, hq_ge, ?_⟩
      · dsimp only
        have hlt' : st.2.1 < 2 ^ (B + k) := hlt
        rw [show B + (k + 1) = (B + k) + 1 by omega, pow_succ]; omega
      · have heq_hi : (((2 * st.2.1 + 1 + 1 : ℕ) : ℚ)) / ((2 ^ (k + 1) : ℕ) : ℚ) =
            ((st.2.1 + 1 : ℕ) : ℚ) / ((2 ^ k : ℕ) : ℚ) := by
          rw [hpow_q]; push_cast; ring
        rw [heq_hi]; exact hhi
    · have hdec_f : dec (x, lam) = false := by cases h' : dec (x, lam) <;> simp_all
      have hst' : bsFracStep dec st = (x, (2 * st.2.1, false :: st.2.2)) := by
        simp only [bsFracStep, hx, hstep_lam, hdec_f, Bool.false_eq_true, ↓reduceIte, add_zero]
      have hq_lt : q < lam := by
        by_contra hnot; push Not at hnot
        exact hdec_t ((hor lam hlam0 hlamM).mpr hnot)
      dsimp only
      rw [hst']
      refine ⟨rfl, by rw [List.length_cons, hud], ?_, ?_, hq_lt⟩
      · dsimp only
        have hlt' : st.2.1 < 2 ^ (B + k) := hlt
        rw [show B + (k + 1) = (B + k) + 1 by omega, pow_succ]; omega
      · have heq_lo : ((2 * st.2.1 : ℕ) : ℚ) / ((2 ^ (k + 1) : ℕ) : ℚ) =
            (st.2.1 : ℚ) / ((2 ^ k : ℕ) : ℚ) := by
          rw [hpow_q]; push_cast; ring
        rw [heq_lo]; exact hlo

/- ### Euclidean Continued-Fraction Recovery (`cfRecover`) -/

private abbrev CFState : Type := Bool × (ℕ × (ℕ × (ℕ × (ℕ × (ℕ × (ℕ × ℕ))))))

private abbrev cfDone (s : CFState) : Bool := s.1
private abbrev cfR0 (s : CFState) : ℕ := s.2.1
private abbrev cfR1 (s : CFState) : ℕ := s.2.2.1
private abbrev cfPp (s : CFState) : ℕ := s.2.2.2.1
private abbrev cfPc (s : CFState) : ℕ := s.2.2.2.2.1
private abbrev cfQp (s : CFState) : ℕ := s.2.2.2.2.2.1
private abbrev cfQc (s : CFState) : ℕ := s.2.2.2.2.2.2.1
private abbrev cfM (s : CFState) : ℕ := s.2.2.2.2.2.2.2

private def cfStep (s : CFState) : CFState :=
  if (cfDone s || decide (cfR1 s = 0)) then
    (true, (cfR0 s, (cfR1 s, (cfPp s, (cfPc s, (cfQp s, (cfQc s, cfM s)))))))
  else
    let dm := natDivMod (cfR0 s, cfR1 s)
    let t := dm.1
    let rn := dm.2
    let pn := t * cfPc s + cfPp s
    let qn := t * cfQc s + cfQp s
    if decide (qn ≤ cfM s) then
      (false, (cfR1 s, (rn, (cfPc s, (pn, (cfQc s, (qn, cfM s)))))))
    else
      (true, (cfR0 s, (cfR1 s, (cfPp s, (cfPc s, (cfQp s, (cfQc s, cfM s)))))))

private theorem cfStep_universal_bound (k : ℕ) (s : CFState) :
    let sk := cfStep^[k] s
    cfM sk = cfM s ∧
    max (cfR0 sk) (cfR1 sk) ≤ max (cfR0 s) (cfR1 s) ∧
    cfQc sk ≤ max (cfQc s) (cfM s) ∧
    cfQp sk ≤ max (cfQp s) (max (cfQc s) (cfM s)) ∧
    cfPc sk * cfR0 sk + cfPp sk * cfR1 sk = cfPc s * cfR0 s + cfPp s * cfR1 s ∧
    cfPc sk ≤ max (cfPc s) (cfPp s) + (cfPc s * cfR0 s + cfPp s * cfR1 s) ∧
    cfPp sk ≤ max (cfPc s) (cfPp s) + (cfPc s * cfR0 s + cfPp s * cfR1 s) := by
  induction k with
  | zero =>
    dsimp only
    simp only [Function.iterate_zero, id_eq]
    exact ⟨trivial, le_rfl, le_max_left _ _, le_max_left _ _, trivial, by omega, by omega⟩
  | succ k ih =>
    obtain ⟨hM, hR, hQc, hQp, hE, hPc, hPp⟩ := ih
    set sk := cfStep^[k] s
    rw [Function.iterate_succ_apply']
    change let sk' := cfStep sk; _
    by_cases hstop : cfDone sk || decide (cfR1 sk = 0)
    · have hsk' : cfStep sk =
          (true, (cfR0 sk, (cfR1 sk, (cfPp sk, (cfPc sk, (cfQp sk, (cfQc sk, cfM sk))))))) := by
        simp [cfStep, hstop]
      dsimp only
      rw [hsk']
      exact ⟨hM, hR, hQc, hQp, hE, hPc, hPp⟩
    · have hr1_ne : cfR1 sk ≠ 0 := by
        intro hz
        have : (cfDone sk || decide (cfR1 sk = 0)) = true := by simp [hz]
        exact hstop this
      have hdm : natDivMod (cfR0 sk, cfR1 sk) = (cfR0 sk / cfR1 sk, cfR0 sk % cfR1 sk) := by
        simp [natDivMod, hr1_ne]
      set t := cfR0 sk / cfR1 sk
      set rn := cfR0 sk % cfR1 sk
      set pn := t * cfPc sk + cfPp sk
      set qn := t * cfQc sk + cfQp sk
      by_cases hqle : qn ≤ cfM sk
      · have hsk' : cfStep sk = (false, (cfR1 sk, (rn, (cfPc sk, (pn, (cfQc sk, (qn, cfM sk))))))) := by
          simp only [cfStep, hstop, Bool.false_eq_true, ↓reduceIte, hdm, decide_eq_true hqle, t, rn, pn, qn]
        dsimp only
        rw [hsk']
        have hrn_lt : rn < cfR1 sk := Nat.mod_lt _ (Nat.pos_of_ne_zero hr1_ne)
        have hE' : pn * cfR1 sk + cfPc sk * rn = cfPc sk * cfR0 sk + cfPp sk * cfR1 sk := by
          have hdiv : cfR1 sk * t + rn = cfR0 sk := Nat.div_add_mod (cfR0 sk) (cfR1 sk)
          calc pn * cfR1 sk + cfPc sk * rn
              = (t * cfPc sk + cfPp sk) * cfR1 sk + cfPc sk * rn := rfl
            _ = cfPc sk * (cfR1 sk * t + rn) + cfPp sk * cfR1 sk := by ring
            _ = cfPc sk * cfR0 sk + cfPp sk * cfR1 sk := by rw [hdiv]
        have hpn_le : pn ≤ pn * cfR1 sk := Nat.le_mul_of_pos_right pn (Nat.pos_of_ne_zero hr1_ne)
        refine ⟨hM, ?_, ?_, ?_, hE'.trans hE, ?_, hPc⟩
        · simp only [cfR0, cfR1]
          have h1 : cfR1 sk ≤ max (cfR0 s) (cfR1 s) := le_trans (le_max_right _ _) hR
          exact max_le h1 (le_trans (le_of_lt hrn_lt) h1)
        · simp only [cfQc]; exact le_trans hqle (by rw [hM]; exact le_max_right _ _)
        · simp only [cfQp]; exact le_trans hQc (le_max_right _ _)
        · change pn ≤ max (cfPc s) (cfPp s) + (cfPc s * cfR0 s + cfPp s * cfR1 s)
          have hE_tot : pn * cfR1 sk + cfPc sk * rn = cfPc s * cfR0 s + cfPp s * cfR1 s := hE'.trans hE
          omega
      · have hsk' : cfStep sk =
            (true, (cfR0 sk, (cfR1 sk, (cfPp sk, (cfPc sk, (cfQp sk, (cfQc sk, cfM sk))))))) := by
          simp [cfStep, hstop, hdm, hqle, t, rn, qn]
        dsimp only
        rw [hsk']
        exact ⟨hM, hR, hQc, hQp, hE, hPc, hPp⟩

private theorem isPolyTime_cfDone : IsPolyTime cfDone :=
  isPolyTime_fst (α := Bool) (β := ℕ × (ℕ × (ℕ × (ℕ × (ℕ × (ℕ × ℕ))))))
private theorem isPolyTime_cfT1 : IsPolyTime (fun s : CFState => s.2) := isPolyTime_snd
private theorem isPolyTime_cfR0 : IsPolyTime cfR0 :=
  isPolyTime_seq (f := fun s : CFState => s.2) (g := Prod.fst) isPolyTime_cfT1 isPolyTime_fst
private theorem isPolyTime_cfT2 : IsPolyTime (fun s : CFState => s.2.2) :=
  isPolyTime_seq (f := fun s : CFState => s.2) (g := Prod.snd) isPolyTime_cfT1 isPolyTime_snd
private theorem isPolyTime_cfR1 : IsPolyTime cfR1 :=
  isPolyTime_seq (f := fun s : CFState => s.2.2) (g := Prod.fst) isPolyTime_cfT2 isPolyTime_fst
private theorem isPolyTime_cfT3 : IsPolyTime (fun s : CFState => s.2.2.2) :=
  isPolyTime_seq (f := fun s : CFState => s.2.2) (g := Prod.snd) isPolyTime_cfT2 isPolyTime_snd
private theorem isPolyTime_cfPp : IsPolyTime cfPp :=
  isPolyTime_seq (f := fun s : CFState => s.2.2.2) (g := Prod.fst) isPolyTime_cfT3 isPolyTime_fst
private theorem isPolyTime_cfT4 : IsPolyTime (fun s : CFState => s.2.2.2.2) :=
  isPolyTime_seq (f := fun s : CFState => s.2.2.2) (g := Prod.snd) isPolyTime_cfT3 isPolyTime_snd
private theorem isPolyTime_cfPc : IsPolyTime cfPc :=
  isPolyTime_seq (f := fun s : CFState => s.2.2.2.2) (g := Prod.fst) isPolyTime_cfT4 isPolyTime_fst
private theorem isPolyTime_cfT5 : IsPolyTime (fun s : CFState => s.2.2.2.2.2) :=
  isPolyTime_seq (f := fun s : CFState => s.2.2.2.2) (g := Prod.snd) isPolyTime_cfT4 isPolyTime_snd
private theorem isPolyTime_cfQp : IsPolyTime cfQp :=
  isPolyTime_seq (f := fun s : CFState => s.2.2.2.2.2) (g := Prod.fst) isPolyTime_cfT5 isPolyTime_fst
private theorem isPolyTime_cfT6 : IsPolyTime (fun s : CFState => s.2.2.2.2.2.2) :=
  isPolyTime_seq (f := fun s : CFState => s.2.2.2.2.2) (g := Prod.snd) isPolyTime_cfT5 isPolyTime_snd
private theorem isPolyTime_cfQc : IsPolyTime cfQc :=
  isPolyTime_seq (f := fun s : CFState => s.2.2.2.2.2.2) (g := Prod.fst) isPolyTime_cfT6 isPolyTime_fst
private theorem isPolyTime_cfM : IsPolyTime cfM :=
  isPolyTime_seq (f := fun s : CFState => s.2.2.2.2.2.2) (g := Prod.snd) isPolyTime_cfT6 isPolyTime_snd

private theorem isPolyTime_cfStep : IsPolyTime cfStep := by
  have hDone := isPolyTime_cfDone
  have hR0 := isPolyTime_cfR0
  have hR1 := isPolyTime_cfR1
  have hPp := isPolyTime_cfPp
  have hPc := isPolyTime_cfPc
  have hQp := isPolyTime_cfQp
  have hQc := isPolyTime_cfQc
  have hM := isPolyTime_cfM
  have hStop : IsPolyTime (fun s : CFState => cfDone s || decide (cfR1 s = 0)) :=
    isPolyTime_seq (isPolyTime_pair hDone (isPolyTime_seq hR1 isPolyTime_natIsZero)) isPolyTime_boolOr
  have hFreeze : IsPolyTime (fun s : CFState =>
      (true, (cfR0 s, (cfR1 s, (cfPp s, (cfPc s, (cfQp s, (cfQc s, cfM s)))))))) :=
    isPolyTime_pair (isPolyTime_const true) isPolyTime_snd
  have hDM : IsPolyTime (fun s : CFState => natDivMod (cfR0 s, cfR1 s)) :=
    isPolyTime_seq (isPolyTime_pair hR0 hR1) isPolyTime_natDivMod
  have hT : IsPolyTime (fun s : CFState => (natDivMod (cfR0 s, cfR1 s)).1) :=
    isPolyTime_seq hDM isPolyTime_fst
  have hRn : IsPolyTime (fun s : CFState => (natDivMod (cfR0 s, cfR1 s)).2) :=
    isPolyTime_seq hDM isPolyTime_snd
  have hPn : IsPolyTime (fun s : CFState => (natDivMod (cfR0 s, cfR1 s)).1 * cfPc s + cfPp s) :=
    isPolyTime_seq (isPolyTime_pair (isPolyTime_seq (isPolyTime_pair hT hPc) isPolyTime_natMul) hPp)
      isPolyTime_natAdd
  have hQn : IsPolyTime (fun s : CFState => (natDivMod (cfR0 s, cfR1 s)).1 * cfQc s + cfQp s) :=
    isPolyTime_seq (isPolyTime_pair (isPolyTime_seq (isPolyTime_pair hT hQc) isPolyTime_natMul) hQp)
      isPolyTime_natAdd
  have hQle : IsPolyTime (fun s : CFState =>
      decide ((natDivMod (cfR0 s, cfR1 s)).1 * cfQc s + cfQp s ≤ cfM s)) :=
    isPolyTime_seq (isPolyTime_pair hQn hM) isPolyTime_natLe
  have hAdv : IsPolyTime (fun s : CFState =>
      (false, (cfR1 s, ((natDivMod (cfR0 s, cfR1 s)).2, (cfPc s,
        ((natDivMod (cfR0 s, cfR1 s)).1 * cfPc s + cfPp s, (cfQc s,
          ((natDivMod (cfR0 s, cfR1 s)).1 * cfQc s + cfQp s, cfM s)))))))) :=
    isPolyTime_pair (isPolyTime_const false)
      (isPolyTime_pair hR1 (isPolyTime_pair hRn (isPolyTime_pair hPc
        (isPolyTime_pair hPn (isPolyTime_pair hQc (isPolyTime_pair hQn hM))))))
  exact isPolyTime_ite hStop hFreeze (isPolyTime_ite hQle hAdv hFreeze)

private theorem isPolyTime_cfIter :
    IsPolyTime (fun p : List Bool × CFState => cfStep^[p.1.length] p.2) := by
  refine isPolyTime_iter cfStep isPolyTime_cfStep (32 * Polynomial.X + 40) (fun u s k _ => ?_)
  obtain ⟨hM, hR, hQc, hQp, _, hPc, hPp⟩ := cfStep_universal_bound k s
  set sk := cfStep^[k] s
  have hLs : (bitEncode s).length =
      2 * 1 + 1 + (2 * (bitEncode (cfR0 s)).length + 1 +
        (2 * (bitEncode (cfR1 s)).length + 1 +
          (2 * (bitEncode (cfPp s)).length + 1 +
            (2 * (bitEncode (cfPc s)).length + 1 +
              (2 * (bitEncode (cfQp s)).length + 1 +
                (2 * (bitEncode (cfQc s)).length + 1 + (bitEncode (cfM s)).length)))))) := by
    simp only [cfR0, cfR1, cfPp, cfPc, cfQp, cfQc, cfM]
    repeat rw [bitEncode_pair_len]
    rfl
  have hL : (bitEncode (u, s)).length = 2 * (3 * u.length) + 1 + (bitEncode s).length := by
    rw [bitEncode_pair_len, bitEncode_listBool_length]
  have hlen_le_of : ∀ {x y : ℕ}, x ≤ y → (bitEncode x).length ≤ (bitEncode y).length := by
    intro x y hxy
    exact length_encodeNat_le (lt_of_le_of_lt hxy (lt_two_pow_length_encodeNat y))
  have hlen_max : ∀ a b : ℕ, (bitEncode (max a b)).length ≤ max (bitEncode a).length (bitEncode b).length := by
    intro a b; rcases le_total a b with h | h
    · rw [max_eq_right h]; exact le_max_right _ _
    · rw [max_eq_left h]; exact le_max_left _ _
  have hL_r0 : (bitEncode (cfR0 sk)).length ≤ (bitEncode s).length := by
    have := le_trans (hlen_le_of (le_trans (le_max_left _ _) hR)) (hlen_max (cfR0 s) (cfR1 s))
    omega
  have hL_r1 : (bitEncode (cfR1 sk)).length ≤ (bitEncode s).length := by
    have := le_trans (hlen_le_of (le_trans (le_max_right _ _) hR)) (hlen_max (cfR0 s) (cfR1 s))
    omega
  have hL_qc : (bitEncode (cfQc sk)).length ≤ (bitEncode s).length := by
    have := le_trans (hlen_le_of hQc) (hlen_max (cfQc s) (cfM s))
    omega
  have hL_qp : (bitEncode (cfQp sk)).length ≤ (bitEncode s).length := by
    have h1 := le_trans (hlen_le_of hQp) (hlen_max (cfQp s) (max (cfQc s) (cfM s)))
    have h2 := hlen_max (cfQc s) (cfM s)
    omega
  have hL_m : (bitEncode (cfM sk)).length ≤ (bitEncode s).length := by
    rw [hM]; omega
  have hBnd_p : max (cfPc s) (cfPp s) + (cfPc s * cfR0 s + cfPp s * cfR1 s) <
      2 ^ (2 * (bitEncode s).length + 2) := by
    have h1 : max (cfPc s) (cfPp s) < 2 ^ (bitEncode s).length := by
      have ha := lt_two_pow_bitEncode_nat (cfPc s)
      have hb := lt_two_pow_bitEncode_nat (cfPp s)
      have hpa : 2 ^ (bitEncode (cfPc s)).length ≤ 2 ^ (bitEncode s).length :=
        Nat.pow_le_pow_right (by omega) (by rw [hLs]; omega)
      have hpb : 2 ^ (bitEncode (cfPp s)).length ≤ 2 ^ (bitEncode s).length :=
        Nat.pow_le_pow_right (by omega) (by rw [hLs]; omega)
      omega
    have h2 : cfPc s * cfR0 s < 2 ^ (2 * (bitEncode s).length) := by
      rw [two_mul, pow_add]
      have ha : cfPc s < 2 ^ (bitEncode s).length := lt_of_lt_of_le (lt_two_pow_bitEncode_nat _)
        (Nat.pow_le_pow_right (by omega) (by rw [hLs]; omega))
      have hb : cfR0 s < 2 ^ (bitEncode s).length := lt_of_lt_of_le (lt_two_pow_bitEncode_nat _)
        (Nat.pow_le_pow_right (by omega) (by rw [hLs]; omega))
      exact Nat.mul_lt_mul'' ha hb
    have h3 : cfPp s * cfR1 s < 2 ^ (2 * (bitEncode s).length) := by
      rw [two_mul, pow_add]
      have ha : cfPp s < 2 ^ (bitEncode s).length := lt_of_lt_of_le (lt_two_pow_bitEncode_nat _)
        (Nat.pow_le_pow_right (by omega) (by rw [hLs]; omega))
      have hb : cfR1 s < 2 ^ (bitEncode s).length := lt_of_lt_of_le (lt_two_pow_bitEncode_nat _)
        (Nat.pow_le_pow_right (by omega) (by rw [hLs]; omega))
      exact Nat.mul_lt_mul'' ha hb
    have hp : 2 ^ (bitEncode s).length ≤ 2 ^ (2 * (bitEncode s).length) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_succ, pow_succ]; omega
  have hL_pc : (bitEncode (cfPc sk)).length ≤ 2 * (bitEncode s).length + 2 :=
    length_encodeNat_le (lt_of_le_of_lt hPc hBnd_p)
  have hL_pp : (bitEncode (cfPp sk)).length ≤ 2 * (bitEncode s).length + 2 :=
    length_encodeNat_le (lt_of_le_of_lt hPp hBnd_p)
  have hLsk : (bitEncode sk).length =
      2 * 1 + 1 + (2 * (bitEncode (cfR0 sk)).length + 1 +
        (2 * (bitEncode (cfR1 sk)).length + 1 +
          (2 * (bitEncode (cfPp sk)).length + 1 +
            (2 * (bitEncode (cfPc sk)).length + 1 +
              (2 * (bitEncode (cfQp sk)).length + 1 +
                (2 * (bitEncode (cfQc sk)).length + 1 + (bitEncode (cfM sk)).length)))))) := by
    simp only [cfR0, cfR1, cfPp, cfPc, cfQp, cfQc, cfM]
    repeat rw [bitEncode_pair_len]
    rfl
  change (bitEncode sk).length ≤ _
  rw [hLsk]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

/- ### Exact Mathematical Correctness of Euclidean Continued-Fraction Recovery -/

private def cfInit (a B : ℕ) : CFState :=
  (false, (a, (2 ^ (3 * B + 1), (0, (1, (1, (0, 2 ^ B)))))))

/-- Core loop invariants of `cfStep^[k] (cfInit a B)`:
Bézout determinant `±1`, exact linear combinations for `(a, D)`, denominator bounds,
and exponential growth `q_curr ≥ 2 ^ ((k - 1) / 2)` while active. -/
private theorem cfStep_inv (a B : ℕ) :
    ∀ k : ℕ,
      let st := cfStep^[k] (cfInit a B)
      cfM st = 2 ^ B ∧
      ((cfPc st : ℤ) * (cfQp st : ℤ) - (cfQc st : ℤ) * (cfPp st : ℤ) = 1 ∨
       (cfPc st : ℤ) * (cfQp st : ℤ) - (cfQc st : ℤ) * (cfPp st : ℤ) = -1) ∧
      cfPc st * cfR0 st + cfPp st * cfR1 st = a ∧
      cfQc st * cfR0 st + cfQp st * cfR1 st = 2 ^ (3 * B + 1) ∧
      cfQc st ≤ 2 ^ B ∧
      (1 ≤ k → 1 ≤ cfQc st) ∧
      (1 ≤ k → cfDone st = false → cfR1 st < cfR0 st) ∧
      (1 ≤ k → cfDone st = false → cfQp st ≤ cfQc st) ∧
      (2 ≤ k → cfDone st = false → 2 ^ ((k - 1) / 2) ≤ cfQc st ∧ 2 ^ ((k - 2) / 2) ≤ cfQp st) ∧
      (cfDone st = true →
        cfR1 st = 0 ∨
        (0 < cfR1 st ∧ 2 ^ B < (cfR0 st / cfR1 st) * cfQc st + cfQp st)) := by
  intro k
  induction k with
  | zero =>
    dsimp only
    simp only [Function.iterate_zero, id_eq, cfInit, cfM, cfPc, cfQp, cfQc, cfPp, cfR0, cfR1, cfDone]
    exact ⟨trivial, Or.inl (by norm_num), by ring, by ring, Nat.zero_le _,
      fun h => by omega, fun h => by omega, fun h => by omega, fun h => by omega,
      fun h => Bool.noConfusion h⟩
  | succ k ih =>
    obtain ⟨hM, hdet, ha_eq, hD_eq, hQc_le, hQc_pos, hr_lt, hqp_le, hgrow, hdone⟩ := ih
    set st := cfStep^[k] (cfInit a B)
    rw [Function.iterate_succ_apply']
    change let st' := cfStep st; _
    by_cases hstop : cfDone st || decide (cfR1 st = 0)
    · have hst' : cfStep st =
          (true, (cfR0 st, (cfR1 st, (cfPp st, (cfPc st, (cfQp st, (cfQc st, cfM st))))))) := by
        simp [cfStep, hstop]
      have hk1 : 1 ≤ k := by
        by_contra h0
        have hk0 : k = 0 := by omega
        subst hk0
        simp [st, cfInit, cfDone, cfR1] at hstop
      dsimp only
      rw [hst']
      refine ⟨hM, hdet, ha_eq, hD_eq, hQc_le, fun _ => hQc_pos hk1,
        fun _ hd => Bool.noConfusion hd, fun _ hd => Bool.noConfusion hd, fun _ hd => Bool.noConfusion hd, fun _ => ?_⟩
      cases hst_d : cfDone st with
      | true => exact hdone hst_d
      | false =>
        simp [hst_d] at hstop
        exact Or.inl hstop
    · have hd_false : cfDone st = false := by
        cases h : cfDone st <;> simp_all
      have hr1_ne : cfR1 st ≠ 0 := by
        intro hz; simp [hz] at hstop
      have hdm : natDivMod (cfR0 st, cfR1 st) = (cfR0 st / cfR1 st, cfR0 st % cfR1 st) := by
        simp [natDivMod, hr1_ne]
      set t := cfR0 st / cfR1 st
      set rn := cfR0 st % cfR1 st
      set pn := t * cfPc st + cfPp st
      set qn := t * cfQc st + cfQp st
      by_cases hqle : qn ≤ cfM st
      · have hst' : cfStep st = (false, (cfR1 st, (rn, (cfPc st, (pn, (cfQc st, (qn, cfM st))))))) := by
          simp only [cfStep, hstop, Bool.false_eq_true, ↓reduceIte, hdm, decide_eq_true hqle, t, rn, pn, qn]
        dsimp only
        rw [hst']
        have hdiv : cfR1 st * t + rn = cfR0 st := Nat.div_add_mod (cfR0 st) (cfR1 st)
        have hdet' : (pn : ℤ) * (cfQc st : ℤ) - (qn : ℤ) * (cfPc st : ℤ) = 1 ∨
            (pn : ℤ) * (cfQc st : ℤ) - (qn : ℤ) * (cfPc st : ℤ) = -1 := by
          have hid : (pn : ℤ) * (cfQc st : ℤ) - (qn : ℤ) * (cfPc st : ℤ) =
              -((cfPc st : ℤ) * (cfQp st : ℤ) - (cfQc st : ℤ) * (cfPp st : ℤ)) := by
            simp only [pn, qn]; push_cast; ring
          rcases hdet with hd1 | hd2
          · right; linarith
          · left; linarith
        have ha' : pn * cfR1 st + cfPc st * rn = a := by
          calc pn * cfR1 st + cfPc st * rn
              = cfPc st * (cfR1 st * t + rn) + cfPp st * cfR1 st := by simp only [pn]; ring
            _ = cfPc st * cfR0 st + cfPp st * cfR1 st := by rw [hdiv]
            _ = a := ha_eq
        have hD' : qn * cfR1 st + cfQc st * rn = 2 ^ (3 * B + 1) := by
          calc qn * cfR1 st + cfQc st * rn
              = cfQc st * (cfR1 st * t + rn) + cfQp st * cfR1 st := by simp only [qn]; ring
            _ = cfQc st * cfR0 st + cfQp st * cfR1 st := by rw [hdiv]
            _ = 2 ^ (3 * B + 1) := hD_eq
        have hqn_pos : 1 ≤ qn := by
          cases k with
          | zero =>
            simp only [st, Function.iterate_zero, id_eq, cfInit, cfQc, cfQp, qn]; omega
          | succ k' =>
            have ht1 : 1 ≤ t := Nat.div_pos (le_of_lt (hr_lt (by omega) hd_false))
              (Nat.pos_of_ne_zero hr1_ne)
            have hqc1 : 1 ≤ cfQc st := hQc_pos (by omega)
            have : 1 ≤ t * cfQc st := Nat.mul_pos ht1 hqc1
            omega
        have hqc_le_qn : cfQc st ≤ qn := by
          cases k with
          | zero =>
            simp only [st, Function.iterate_zero, id_eq, cfInit, cfQc, cfQp, qn]; omega
          | succ k' =>
            have ht1 : 1 ≤ t := Nat.div_pos (le_of_lt (hr_lt (by omega) hd_false))
              (Nat.pos_of_ne_zero hr1_ne)
            have : cfQc st ≤ t * cfQc st := Nat.le_mul_of_pos_left _ ht1
            omega
        refine ⟨hM, hdet', ha', hD', by dsimp only [cfQc]; omega, fun _ => hqn_pos,
          fun _ _ => Nat.mod_lt _ (Nat.pos_of_ne_zero hr1_ne),
          fun _ _ => hqc_le_qn, fun hk2 _ => ?_, fun hd => Bool.noConfusion hd⟩
        cases k with
        | zero => omega
        | succ k' =>
          cases k' with
          | zero =>
            simp only [Nat.add_sub_cancel]
            exact ⟨hqn_pos, hQc_pos (by omega)⟩
          | succ k'' =>
            obtain ⟨hg1, hg2⟩ := hgrow (by omega) hd_false
            have ht1 : 1 ≤ t := Nat.div_pos (le_of_lt (hr_lt (by omega) hd_false))
              (Nat.pos_of_ne_zero hr1_ne)
            have hqn_ge : cfQc st + cfQp st ≤ qn := by
              have : cfQc st ≤ t * cfQc st := Nat.le_mul_of_pos_left _ ht1
              show cfQc st + cfQp st ≤ t * cfQc st + cfQp st; omega
            refine ⟨?_, hg1⟩
            have hq2 : 2 * cfQp st ≤ qn := by
              have := hqp_le (by omega) hd_false; omega
            have hexp : (k'' + 1 + 1 + 1 - 1) / 2 = (k'' + 1 + 1 - 2) / 2 + 1 := by omega
            dsimp only [cfQc]
            rw [hexp, pow_succ]
            omega
      · have hst' : cfStep st =
            (true, (cfR0 st, (cfR1 st, (cfPp st, (cfPc st, (cfQp st, (cfQc st, cfM st))))))) := by
          simp [cfStep, hstop, hdm, hqle, t, rn, qn]
        have hk1 : 1 ≤ k := by
          by_contra h0
          have hk0 : k = 0 := by omega
          subst hk0
          have hqn1 : qn = 1 := by
            simp [qn, st, cfInit, cfQc, cfQp]
          have hM1 : 1 ≤ cfM st := by rw [hM]; exact Nat.one_le_two_pow
          exact hqle (by rw [hqn1]; exact hM1)
        dsimp only
        rw [hst']
        exact ⟨hM, hdet, ha_eq, hD_eq, hQc_le, fun _ => hQc_pos hk1,
          fun _ hd => Bool.noConfusion hd, fun _ hd => Bool.noConfusion hd, fun _ hd => Bool.noConfusion hd,
          fun _ => Or.inr ⟨Nat.pos_of_ne_zero hr1_ne, by dsimp only [cfR0, cfR1, cfQc, cfQp, qn, t] at hqle ⊢; omega⟩⟩

/-- After `2 * B + 3` steps, `cfStep` has unconditionally halted (`cfDone = true`) with
coprime denominator `≥ 1`. -/
private theorem cfStep_halts (a B : ℕ) :
    let st := cfStep^[2 * B + 3] (cfInit a B)
    cfDone st = true ∧ cfQc st ≠ 0 ∧ Nat.Coprime (cfPc st) (cfQc st) := by
  obtain ⟨_, hdet, _, _, hQc_le, hQc_pos, _, _, hgrow, _⟩ := cfStep_inv a B (2 * B + 3)
  set st := cfStep^[2 * B + 3] (cfInit a B)
  have hdone : cfDone st = true := by
    by_contra hnot
    have hdf : cfDone st = false := by cases h : cfDone st <;> simp_all
    obtain ⟨hg, _⟩ := hgrow (by omega) hdf
    have hexp : (2 * B + 3 - 1) / 2 = B + 1 := by omega
    rw [hexp, pow_succ] at hg
    have hQc_le' : cfQc st ≤ 2 ^ B := hQc_le
    have : 0 < 2 ^ B := by positivity
    omega
  have hqnz : cfQc st ≠ 0 := by have := hQc_pos (by omega); omega
  have hcop : Nat.Coprime (cfPc st) (cfQc st) := by
    rw [← Int.natAbs_natCast (cfPc st), ← Int.natAbs_natCast (cfQc st), ← Int.isCoprime_iff_nat_coprime]
    rcases hdet with hd | hd
    · exact ⟨(cfQp st : ℤ), -(cfPp st : ℤ), by linarith⟩
    · exact ⟨-(cfQp st : ℤ), (cfPp st : ℤ), by linarith⟩
  exact ⟨hdone, hqnz, hcop⟩

/-- Exact rational recovery from a `1 / (2 * M^3)` bracket via the 5-line integer triangle
inequality (no ContinuedFraction library needed). -/
private theorem cfStep_recovers (a B : ℕ) (q : ℚ)
    (hq0 : 0 ≤ q) (hqden : q.den ≤ 2 ^ B)
    (hlo : (a : ℚ) / ((2 ^ (3 * B + 1) : ℕ) : ℚ) ≤ q)
    (hhi : q < ((a + 1 : ℕ) : ℚ) / ((2 ^ (3 * B + 1) : ℕ) : ℚ)) :
    let st := cfStep^[2 * B + 3] (cfInit a B)
    ((cfPc st : ℚ) / (cfQc st : ℚ)) = q := by
  obtain ⟨_, hdet, ha_eq, hD_eq, hQc_le, _, _, _, _, hdone_spec⟩ := cfStep_inv a B (2 * B + 3)
  obtain ⟨hdone, hqnz, _⟩ := cfStep_halts a B
  set st := cfStep^[2 * B + 3] (cfInit a B)
  set M : ℕ := 2 ^ B
  set D : ℕ := 2 ^ (3 * B + 1)
  have hM_pos : 1 ≤ M := Nat.one_le_two_pow
  have hD_eq_M : D = 2 * M ^ 3 := by
    simp only [D, M]; rw [pow_succ, ← pow_mul, mul_comm B 3]; ring
  set u : ℕ := q.num.toNat
  set v : ℕ := q.den
  have hv_pos : 1 ≤ v := q.pos
  have hq_eq : q = (u : ℚ) / (v : ℚ) := by
    have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
    have hu_int : (u : ℤ) = q.num := Int.toNat_of_nonneg hnum_nn
    rw [← Rat.num_div_den q, ← hu_int]; push_cast; rfl
  -- Bracket in integer form: |a * v - D * u| < v
  have hbr_lo : (a : ℤ) * (v : ℤ) ≤ (D : ℤ) * (u : ℤ) := by
    have hpos : (0 : ℚ) < (D : ℚ) * (v : ℚ) := by positivity
    have h1 : (a : ℚ) / (D : ℚ) ≤ (u : ℚ) / (v : ℚ) := by rw [← hq_eq]; exact hlo
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h1
    have h2 : (a : ℚ) * (v : ℚ) ≤ (D : ℚ) * (u : ℚ) := by linarith
    exact_mod_cast h2
  have hbr_hi : (D : ℤ) * (u : ℤ) < ((a : ℤ) + 1) * (v : ℤ) := by
    have h1 : (u : ℚ) / (v : ℚ) < ((a + 1 : ℕ) : ℚ) / (D : ℚ) := by rw [← hq_eq]; exact hhi
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h1
    have h2 : (u : ℚ) * (D : ℚ) < ((a : ℚ) + 1) * (v : ℚ) := by push_cast at h1; exact h1
    have h3 : (D : ℚ) * (u : ℚ) < ((a : ℚ) + 1) * (v : ℚ) := by linarith
    exact_mod_cast h3
  have habs_br : |(a : ℤ) * (v : ℤ) - (D : ℤ) * (u : ℤ)| < (v : ℤ) := by
    rw [abs_lt]; constructor <;> linarith
  -- Key identity: |a * q_curr - D * p_curr| = r_1
  have hdiff_r1 : |(a : ℤ) * (cfQc st : ℤ) - (D : ℤ) * (cfPc st : ℤ)| = (cfR1 st : ℤ) := by
    have hid : (a : ℤ) * (cfQc st : ℤ) - (D : ℤ) * (cfPc st : ℤ) =
        -((cfPc st : ℤ) * (cfQp st : ℤ) - (cfQc st : ℤ) * (cfPp st : ℤ)) * (cfR1 st : ℤ) := by
      have ha_z : (a : ℤ) = (cfPc st : ℤ) * (cfR0 st : ℤ) + (cfPp st : ℤ) * (cfR1 st : ℤ) := by
        exact_mod_cast ha_eq.symm
      have hD_z : (D : ℤ) = (cfQc st : ℤ) * (cfR0 st : ℤ) + (cfQp st : ℤ) * (cfR1 st : ℤ) := by
        exact_mod_cast hD_eq.symm
      rw [ha_z, hD_z]; ring
    rw [hid]
    rcases hdet with hd | hd
    · rw [hd]; simp
    · rw [hd]; simp
  -- Cross-multiplication identity
  have hcross : (D : ℤ) * ((cfPc st : ℤ) * (v : ℤ) - (cfQc st : ℤ) * (u : ℤ)) =
      (cfQc st : ℤ) * ((a : ℤ) * (v : ℤ) - (D : ℤ) * (u : ℤ)) -
      (v : ℤ) * ((a : ℤ) * (cfQc st : ℤ) - (D : ℤ) * (cfPc st : ℤ)) := by ring
  have htri : (D : ℤ) * |(cfPc st : ℤ) * (v : ℤ) - (cfQc st : ℤ) * (u : ℤ)| ≤
      (cfQc st : ℤ) * |(a : ℤ) * (v : ℤ) - (D : ℤ) * (u : ℤ)| + (v : ℤ) * (cfR1 st : ℤ) := by
    have hD_nn : (0 : ℤ) ≤ (D : ℤ) := by positivity
    calc (D : ℤ) * |(cfPc st : ℤ) * (v : ℤ) - (cfQc st : ℤ) * (u : ℤ)|
        = |(D : ℤ) * ((cfPc st : ℤ) * (v : ℤ) - (cfQc st : ℤ) * (u : ℤ))| := by
            rw [abs_mul, abs_of_nonneg hD_nn]
      _ = |(cfQc st : ℤ) * ((a : ℤ) * (v : ℤ) - (D : ℤ) * (u : ℤ)) -
            (v : ℤ) * ((a : ℤ) * (cfQc st : ℤ) - (D : ℤ) * (cfPc st : ℤ))| := by rw [hcross]
      _ ≤ |(cfQc st : ℤ) * ((a : ℤ) * (v : ℤ) - (D : ℤ) * (u : ℤ))| +
            |(v : ℤ) * ((a : ℤ) * (cfQc st : ℤ) - (D : ℤ) * (cfPc st : ℤ))| := abs_sub _ _
      _ = (cfQc st : ℤ) * |(a : ℤ) * (v : ℤ) - (D : ℤ) * (u : ℤ)| + (v : ℤ) * (cfR1 st : ℤ) := by
            rw [abs_mul, abs_mul,
              show |(cfQc st : ℤ)| = (cfQc st : ℤ) from abs_of_nonneg (Nat.cast_nonneg _),
              show |(v : ℤ)| = (v : ℤ) from abs_of_nonneg (Nat.cast_nonneg _), hdiff_r1]
  have hpcv_eq : (cfPc st : ℤ) * (v : ℤ) = (cfQc st : ℤ) * (u : ℤ) := by
    suffices hlt1 : |(cfPc st : ℤ) * (v : ℤ) - (cfQc st : ℤ) * (u : ℤ)| < 1 by
      have hz : |(cfPc st : ℤ) * (v : ℤ) - (cfQc st : ℤ) * (u : ℤ)| = 0 := by
        have := abs_nonneg ((cfPc st : ℤ) * (v : ℤ) - (cfQc st : ℤ) * (u : ℤ)); omega
      have := abs_eq_zero.mp hz; omega
    have hM_z : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM_pos
    have hD_z : (D : ℤ) = 2 * (M : ℤ) ^ 3 := by exact_mod_cast hD_eq_M
    have hqc_z : (cfQc st : ℤ) ≤ (M : ℤ) := by exact_mod_cast hQc_le
    have hqc_pos_z : (1 : ℤ) ≤ (cfQc st : ℤ) := by exact_mod_cast (Nat.pos_of_ne_zero hqnz)
    have hv_z : (v : ℤ) ≤ (M : ℤ) := by exact_mod_cast hqden
    have hv_pos_z : (1 : ℤ) ≤ (v : ℤ) := by exact_mod_cast hv_pos
    have hterm1 : (cfQc st : ℤ) * |(a : ℤ) * (v : ℤ) - (D : ℤ) * (u : ℤ)| < (M : ℤ) ^ 2 := by
      have h1 : (cfQc st : ℤ) * |(a : ℤ) * (v : ℤ) - (D : ℤ) * (u : ℤ)| < (cfQc st : ℤ) * (v : ℤ) :=
        mul_lt_mul_of_pos_left habs_br (by linarith)
      have h2 : (cfQc st : ℤ) * (v : ℤ) ≤ (M : ℤ) ^ 2 := by
        rw [sq]; exact mul_le_mul hqc_z hv_z (by linarith) (by linarith)
      linarith
    rcases hdone_spec hdone with hr1_zero | ⟨_, hqn_gt⟩
    · have hD_pos_z : (0 : ℤ) < (D : ℤ) := by positivity
      have hM2_le_D : (M : ℤ) ^ 2 ≤ (D : ℤ) := by
        rw [hD_z]
        have h1 : (M : ℤ) ^ 2 * 1 ≤ (M : ℤ) ^ 2 * (2 * (M : ℤ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
        linarith [show (M : ℤ) ^ 2 * (2 * (M : ℤ)) = 2 * (M : ℤ) ^ 3 by ring]
      have hbound : (D : ℤ) * |(cfPc st : ℤ) * (v : ℤ) - (cfQc st : ℤ) * (u : ℤ)| < (D : ℤ) * 1 := by
        rw [hr1_zero] at htri; simp only [Nat.cast_zero, mul_zero, add_zero] at htri
        linarith
      exact lt_of_mul_lt_mul_left hbound (le_of_lt hD_pos_z)
    · set qn : ℕ := (cfR0 st / cfR1 st) * cfQc st + cfQp st
      have hqn_r1 : qn * cfR1 st ≤ D := by
        have hdiv : cfR1 st * (cfR0 st / cfR1 st) + cfR0 st % cfR1 st = cfR0 st :=
          Nat.div_add_mod (cfR0 st) (cfR1 st)
        have h1 : D = qn * cfR1 st + cfQc st * (cfR0 st % cfR1 st) := by
          calc D = cfQc st * cfR0 st + cfQp st * cfR1 st := hD_eq.symm
            _ = cfQc st * (cfR1 st * (cfR0 st / cfR1 st) + cfR0 st % cfR1 st) +
                  cfQp st * cfR1 st := by rw [hdiv]
            _ = qn * cfR1 st + cfQc st * (cfR0 st % cfR1 st) := by simp only [qn]; ring
        omega
      have hqn_z : (M : ℤ) + 1 ≤ (qn : ℤ) := by exact_mod_cast hqn_gt
      have hqn_r1_z : (qn : ℤ) * (cfR1 st : ℤ) ≤ (D : ℤ) := by exact_mod_cast hqn_r1
      have hvr1 : ((M : ℤ) + 1) * ((v : ℤ) * (cfR1 st : ℤ)) ≤ (M : ℤ) * (D : ℤ) := by
        have hr1_nn : (0 : ℤ) ≤ (cfR1 st : ℤ) := Nat.cast_nonneg _
        have h1 : ((M : ℤ) + 1) * (cfR1 st : ℤ) ≤ (D : ℤ) :=
          le_trans (mul_le_mul_of_nonneg_right hqn_z hr1_nn) hqn_r1_z
        have h2 : (v : ℤ) * (((M : ℤ) + 1) * (cfR1 st : ℤ)) ≤ (M : ℤ) * (D : ℤ) :=
          mul_le_mul hv_z h1 (mul_nonneg (by linarith) hr1_nn) (by linarith)
        linarith
      have hpos_f : (0 : ℤ) < 2 * (M : ℤ) * ((M : ℤ) + 1) :=
        mul_pos (by linarith) (by linarith)
      have hD_pos : (0 : ℤ) < (D : ℤ) := by positivity
      have hbig : (2 * (M : ℤ) * ((M : ℤ) + 1) * (D : ℤ)) *
          |(cfPc st : ℤ) * (v : ℤ) - (cfQc st : ℤ) * (u : ℤ)| <
          (2 * (M : ℤ) * ((M : ℤ) + 1) * (D : ℤ)) * 1 := by
        have hmul_tri := mul_le_mul_of_nonneg_left htri (le_of_lt hpos_f)
        have h1 : 2 * (M : ℤ) * ((M : ℤ) + 1) *
            ((cfQc st : ℤ) * |(a : ℤ) * (v : ℤ) - (D : ℤ) * (u : ℤ)|) <
            ((M : ℤ) + 1) * (D : ℤ) := by
          have := mul_lt_mul_of_pos_left hterm1 hpos_f
          have heq : 2 * (M : ℤ) * ((M : ℤ) + 1) * (M : ℤ) ^ 2 = ((M : ℤ) + 1) * (D : ℤ) := by
            rw [hD_z]; ring
          linarith
        have h2 : 2 * (M : ℤ) * ((M : ℤ) + 1) * ((v : ℤ) * (cfR1 st : ℤ)) ≤
            2 * (M : ℤ) ^ 2 * (D : ℤ) := by
          have := mul_le_mul_of_nonneg_left hvr1 (show (0 : ℤ) ≤ 2 * (M : ℤ) by linarith)
          linarith [show 2 * (M : ℤ) * ((M : ℤ) + 1) * ((v : ℤ) * (cfR1 st : ℤ)) =
              2 * (M : ℤ) * (((M : ℤ) + 1) * ((v : ℤ) * (cfR1 st : ℤ))) by ring,
            show 2 * (M : ℤ) * ((M : ℤ) * (D : ℤ)) = 2 * (M : ℤ) ^ 2 * (D : ℤ) by ring]
        have h3 : ((M : ℤ) + 1) * (D : ℤ) + 2 * (M : ℤ) ^ 2 * (D : ℤ) ≤
            2 * (M : ℤ) * ((M : ℤ) + 1) * (D : ℤ) := by
          have hcoef : ((M : ℤ) + 1 + 2 * (M : ℤ) ^ 2) * (D : ℤ) ≤
              (2 * (M : ℤ) * ((M : ℤ) + 1)) * (D : ℤ) :=
            mul_le_mul_of_nonneg_right (by linarith [show 2 * (M : ℤ) * ((M : ℤ) + 1) =
              2 * (M : ℤ) ^ 2 + 2 * (M : ℤ) by ring]) (le_of_lt hD_pos)
          linarith
        linarith [show (2 * (M : ℤ) * ((M : ℤ) + 1) * (D : ℤ)) *
            |(cfPc st : ℤ) * (v : ℤ) - (cfQc st : ℤ) * (u : ℤ)| =
            2 * (M : ℤ) * ((M : ℤ) + 1) *
              ((D : ℤ) * |(cfPc st : ℤ) * (v : ℤ) - (cfQc st : ℤ) * (u : ℤ)|) by ring]
      exact lt_of_mul_lt_mul_left hbig (le_of_lt (mul_pos hpos_f hD_pos))
  rw [hq_eq, div_eq_div_iff (by positivity) (by positivity)]
  have hpcv_eq' : (cfPc st : ℤ) * (v : ℤ) = (u : ℤ) * (cfQc st : ℤ) := by linarith
  exact_mod_cast hpcv_eq'

end SearchAndCF

end OMA.Helpers

open BitstringEncoding ComplexityTheory OMA.Helpers

theorem OMA.solution : OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H3_R1.H3 := by
  intro α _ dec p hdec
  let uB : α → List Bool := fun x => List.replicate (p.eval (bitEncode x).length) false
  let Mfn : α → ℕ := fun x => 2 ^ (uB x).length
  let Dfn : α → ℕ := fun x => 2 ^ (3 * (uB x).length + 1)
  let aInt : α → ℕ := fun x => ((bsIntStep dec)^[(uB x).length] (x, (0, Mfn x / 2))).2.1
  let uFrac : α → List Bool := fun x => uB x ++ uB x ++ uB x ++ [false]
  let aFrac : α → ℕ := fun x => ((bsFracStep dec)^[(uFrac x).length] (x, (aInt x, [false]))).2.1
  let uCF : α → List Bool := fun x => uB x ++ uB x ++ [false, false, false]
  let cfRes : α → CFState := fun x =>
    cfStep^[(uCF x).length] (false, (aFrac x, (Dfn x, (0, (1, (1, (0, Mfn x)))))))
  let search : α → ℚ := fun x =>
    if dec (x, (Mfn x : ℚ)) then (Mfn x : ℚ)
    else ((cfPc (cfRes x) : ℚ) / (cfQc (cfRes x) : ℚ))
  -- 1. Prove `IsPolyTime search` by composing our polytime building blocks.
  have huB : IsPolyTime uB := isPolyTime_polyUnary p
  have hMfn : IsPolyTime Mfn := isPolyTime_seq (f := uB) (g := fun u : List Bool => 2 ^ u.length) huB isPolyTime_pow2
  have huFrac : IsPolyTime uFrac :=
    isPolyTime_seq (isPolyTime_pair
      (isPolyTime_seq (isPolyTime_pair
        (isPolyTime_seq (isPolyTime_pair huB huB) isPolyTime_unaryAdd) huB) isPolyTime_unaryAdd)
      (isPolyTime_const [false])) isPolyTime_unaryAdd
  have hDfn : IsPolyTime Dfn := by
    have hEq : Dfn = fun x => 2 ^ (uFrac x).length := by
      funext x; simp only [Dfn, uFrac, List.length_append, List.length_singleton]; congr 1; omega
    rw [hEq]
    exact isPolyTime_seq (f := uFrac) (g := fun u : List Bool => 2 ^ u.length) huFrac isPolyTime_pow2
  have huCF : IsPolyTime uCF :=
    isPolyTime_seq (isPolyTime_pair
      (isPolyTime_seq (isPolyTime_pair huB huB) isPolyTime_unaryAdd)
      (isPolyTime_const [false, false, false])) isPolyTime_unaryAdd
  have hMrat : IsPolyTime (fun x => (Mfn x : ℚ)) := by
    have hcop : IsPolyTime (fun x =>
        (⟨(Mfn x, 1), one_ne_zero, Nat.coprime_one_right _⟩ : CoprimePair)) :=
      isPolyTime_ofSubtype_out (fun x => (Mfn x, 1)) (isPolyTime_pair hMfn (isPolyTime_const 1))
        (fun x => ⟨one_ne_zero, Nat.coprime_one_right _⟩)
    have hEq : (fun x => (Mfn x : ℚ)) = fun x =>
        ((⟨(Mfn x, 1), one_ne_zero, Nat.coprime_one_right _⟩ : CoprimePair).val.1 : ℚ) /
        ((⟨(Mfn x, 1), one_ne_zero, Nat.coprime_one_right _⟩ : CoprimePair).val.2 : ℚ) := by
      funext x; simp
    rw [hEq]
    exact isPolyTime_seq hcop isPolyTime_coprimeToRat
  have hCheckM : IsPolyTime (fun x => dec (x, (Mfn x : ℚ))) :=
    isPolyTime_seq (isPolyTime_pair isPolyTime_id hMrat) hdec
  have haInt : IsPolyTime aInt := by
    have hprep : IsPolyTime (fun x => (uB x, (x, (0, Mfn x / 2)))) :=
      isPolyTime_pair huB (isPolyTime_pair isPolyTime_id
        (isPolyTime_pair (isPolyTime_const 0) (isPolyTime_seq hMfn isPolyTime_natDiv2)))
    exact isPolyTime_seq
      (f := fun x => (bsIntStep dec)^[(uB x).length] (x, (0, Mfn x / 2)))
      (g := fun s : α × (ℕ × ℕ) => s.2.1)
      (isPolyTime_seq (f := fun x => (uB x, (x, (0, Mfn x / 2))))
        (g := fun p : List Bool × (α × (ℕ × ℕ)) => (bsIntStep dec)^[p.1.length] p.2)
        hprep (isPolyTime_bsIntIter dec hdec))
      (isPolyTime_seq isPolyTime_snd isPolyTime_fst)
  have haFrac : IsPolyTime aFrac := by
    have hprep : IsPolyTime (fun x => (uFrac x, (x, (aInt x, [false])))) :=
      isPolyTime_pair huFrac (isPolyTime_pair isPolyTime_id
        (isPolyTime_pair haInt (isPolyTime_const [false])))
    exact isPolyTime_seq
      (f := fun x => (bsFracStep dec)^[(uFrac x).length] (x, (aInt x, [false])))
      (g := fun s : α × (ℕ × List Bool) => s.2.1)
      (isPolyTime_seq (f := fun x => (uFrac x, (x, (aInt x, [false]))))
        (g := fun p : List Bool × (α × (ℕ × List Bool)) => (bsFracStep dec)^[p.1.length] p.2)
        hprep (isPolyTime_bsFracIter dec hdec))
      (isPolyTime_seq isPolyTime_snd isPolyTime_fst)
  have hcfRes : IsPolyTime cfRes := by
    have hinit : IsPolyTime (fun x =>
        (false, (aFrac x, (Dfn x, (0, (1, (1, (0, Mfn x)))))))) :=
      isPolyTime_pair (isPolyTime_const false)
        (isPolyTime_pair haFrac (isPolyTime_pair hDfn (isPolyTime_pair (isPolyTime_const 0)
          (isPolyTime_pair (isPolyTime_const 1) (isPolyTime_pair (isPolyTime_const 1)
            (isPolyTime_pair (isPolyTime_const 0) hMfn))))))
    exact isPolyTime_seq (isPolyTime_pair huCF hinit) isPolyTime_cfIter
  have hcfRat : IsPolyTime (fun x => ((cfPc (cfRes x) : ℚ) / (cfQc (cfRes x) : ℚ))) := by
    have hPc : IsPolyTime (fun x => cfPc (cfRes x)) := isPolyTime_seq (f := cfRes) (g := cfPc) hcfRes isPolyTime_cfPc
    have hQc : IsPolyTime (fun x => cfQc (cfRes x)) := isPolyTime_seq (f := cfRes) (g := cfQc) hcfRes isPolyTime_cfQc
    have hcop_all : ∀ x, cfQc (cfRes x) ≠ 0 ∧ Nat.Coprime (cfPc (cfRes x)) (cfQc (cfRes x)) := by
      intro x
      have hlen : (uCF x).length = 2 * (uB x).length + 3 := by
        simp only [uCF, List.length_append, List.length_cons, List.length_nil]; omega
      have hst_eq : cfRes x = cfStep^[2 * (uB x).length + 3] (cfInit (aFrac x) (uB x).length) := by
        dsimp only [cfRes, cfInit, Dfn, Mfn]; rw [hlen]
      rw [hst_eq]
      obtain ⟨_, hqnz, hcop⟩ := cfStep_halts (aFrac x) (uB x).length
      exact ⟨hqnz, hcop⟩
    have hsub : IsPolyTime (fun x =>
        (⟨(cfPc (cfRes x), cfQc (cfRes x)), hcop_all x⟩ : CoprimePair)) :=
      isPolyTime_ofSubtype_out (fun x => (cfPc (cfRes x), cfQc (cfRes x)))
        (isPolyTime_pair hPc hQc) hcop_all
    exact isPolyTime_seq hsub isPolyTime_coprimeToRat
  have hsearch_pt : IsPolyTime search := isPolyTime_ite hCheckM hMrat hcfRat
  -- 2. Prove correctness on every valid `(x, q)`.
  refine ⟨search, hsearch_pt, fun x q hq0 hqM hqden hor => ?_⟩
  set B : ℕ := p.eval (bitEncode x).length
  have huB_len : (uB x).length = B := List.length_replicate
  have hM_eq : Mfn x = 2 ^ B := by simp only [Mfn, huB_len]
  dsimp only [search]
  by_cases htop : dec (x, (Mfn x : ℚ)) = true
  · rw [if_pos htop, hM_eq]
    have hge : ((2 ^ B : ℕ) : ℚ) ≤ q := by
      rw [hM_eq] at htop
      exact (hor ((2 ^ B : ℕ) : ℚ) (Nat.cast_nonneg _) le_rfl).mp htop
    exact le_antisymm hge hqM
  · rw [if_neg htop]
    have hq_ltM : q < ((2 ^ B : ℕ) : ℚ) := by
      by_contra hnot; push Not at hnot
      have hle_t : dec (x, ((2 ^ B : ℕ) : ℚ)) = true :=
        (hor ((2 ^ B : ℕ) : ℚ) (Nat.cast_nonneg _) le_rfl).mpr hnot
      rw [hM_eq] at htop; exact htop hle_t
    obtain ⟨_, haInt_le, haInt_lo, haInt_hi, _⟩ :=
      bsIntStep_spec dec x q B hq0 hq_ltM hor B le_rfl
    simp only [Nat.sub_self, pow_zero] at haInt_le haInt_lo haInt_hi
    have haInt_eq : aInt x = ((bsIntStep dec)^[B] (x, (0, 2 ^ B / 2))).2.1 := by
      simp only [aInt, huB_len, hM_eq]
    have haInt_lt : aInt x < 2 ^ B := by rw [haInt_eq]; omega
    have huFrac_len : (uFrac x).length = 3 * B + 1 := by
      simp only [uFrac, List.length_append, List.length_singleton, huB_len]; omega
    obtain ⟨_, _, _, hFrac_lo, hFrac_hi⟩ :=
      bsFracStep_spec dec x q B (aInt x) haInt_lt (by rw [haInt_eq]; exact haInt_lo)
        (by rw [haInt_eq]; exact haInt_hi) hor (3 * B + 1)
    have haFrac_eq : aFrac x = ((bsFracStep dec)^[3 * B + 1] (x, (aInt x, [false]))).2.1 := by
      simp only [aFrac, huFrac_len]
    rw [← haFrac_eq] at hFrac_lo hFrac_hi
    have huCF_len : (uCF x).length = 2 * B + 3 := by
      simp only [uCF, List.length_append, List.length_cons, List.length_nil, huB_len]; omega
    have hcf_eq : cfRes x = cfStep^[2 * B + 3] (cfInit (aFrac x) B) := by
      dsimp only [cfRes, cfInit, Dfn, Mfn]; rw [huCF_len, huB_len]
    rw [hcf_eq]
    exact cfStep_recovers (aFrac x) B q hq0 hqden hFrac_lo hFrac_hi

