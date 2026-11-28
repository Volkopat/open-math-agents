import FormalConjectures.Millennium.PvsNP

open Turing Computability ComplexityTheory

namespace OMA.PBPP

def RIn {σ : Type} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Prop :=
  ∃ n ≤ m, (flip bind f)^[n] (some a) = b

lemma RIn.single {σ : Type} {f : σ → Option σ} {a b : σ} (h : f a = some b) : RIn f a (some b) 1 :=
  ⟨1, le_rfl, h⟩

lemma RIn.trans {σ : Type} {f : σ → Option σ} {a b : σ} {c : Option σ} {m₁ m₂ : ℕ}
    (h₁ : RIn f a (some b) m₁) (h₂ : RIn f b c m₂) : RIn f a c (m₁ + m₂) := by
  obtain ⟨n₁, hn₁, e₁⟩ := h₁; obtain ⟨n₂, hn₂, e₂⟩ := h₂
  exact ⟨n₂ + n₁, by omega, by rw [Function.iterate_add_apply, e₁, e₂]⟩

lemma RIn.mono {σ : Type} {f : σ → Option σ} {a : σ} {b : Option σ} {m m' : ℕ}
    (h : RIn f a b m) (hm : m ≤ m') : RIn f a b m' :=
  let ⟨n, hn, e⟩ := h; ⟨n, hn.trans hm, e⟩

lemma eval_mono (q : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : q.eval a ≤ q.eval b := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; exact Nat.add_le_add hp hq
  | monomial n c => simp only [Polynomial.eval_monomial]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

inductive Ph | parse | erase | move deriving DecidableEq

instance : Fintype Ph := ⟨{.parse, .erase, .move}, by rintro (_ | _ | _) <;> simp⟩

variable (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool)

abbrev G : Bool ⊕ M.K → Type := fun k => Sum.casesOn (motive := fun _ => Type) k (fun _ => Bool) M.Γ

def liftStmt : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool)
  | .push k f q => .push (.inr k) (fun v => f v.1) (liftStmt q)
  | .peek k f q => .peek (.inr k) (fun v o => (f v.1 o, v.2)) (liftStmt q)
  | .pop k f q => .pop (.inr k) (fun v o => (f v.1 o, v.2)) (liftStmt q)
  | .load a q => .load (fun v => (a v.1, v.2)) (liftStmt q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (liftStmt q₁) (liftStmt q₂)
  | .goto f => .goto (fun v => .inl (f v.1))
  | .halt => .halt

def prog : M.Λ ⊕ Ph → TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool)
  | .inl l => liftStmt M (M.m l)
  | .inr .parse =>
    .pop (.inl false) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2 == some true)
        (.pop (.inl false) (fun v o => (v.1, o)) <|
          .push (.inl true) (fun v => v.2.getD false) <| .goto fun _ => .inr .parse)
        (.goto fun _ => .inr .erase)
  | .inr .erase =>
    .pop (.inl false) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome) (.goto fun _ => .inr .erase) (.goto fun _ => .inr .move)
  | .inr .move =>
    .pop (.inl true) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.push (.inr M.k₀) (fun v => e.symm (v.2.getD false)) <| .goto fun _ => .inr .move)
        (.goto fun _ => .inl M.main)

def N : FinTM2 :=
  letI := M.kFin; letI := M.ΛFin; letI := M.σFin
  { K := Bool ⊕ M.K, k₀ := .inl false, k₁ := .inr M.k₁, Γ := G M, Λ := M.Λ ⊕ Ph,
    main := .inr .parse, σ := M.σ × Option Bool, initialState := (M.initialState, none),
    Γk₀Fin := inferInstanceAs (Fintype Bool), m := prog M e }

def mk (i a : List Bool) (S : ∀ k, List (M.Γ k)) : ∀ k : Bool ⊕ M.K, List (G M k)
  | .inl false => i | .inl true => a | .inr k => S k

variable {M} {e}

@[simp] lemma upd_inp (i a : List Bool) (i' : List (G M (.inl false))) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk M i a S) (.inl false) i' = mk M i' a S := by
  funext k; rcases k with (_ | _) | k <;> simp [Function.update, mk]

@[simp] lemma upd_aux (i a : List Bool) (a' : List (G M (.inl true))) (S : ∀ k, List (M.Γ k)) :
    Function.update (mk M i a S) (.inl true) a' = mk M i a' S := by
  funext k; rcases k with (_ | _) | k <;> simp [Function.update, mk]

@[simp] lemma upd_inr (i a : List Bool) (S : ∀ k, List (M.Γ k)) (k : M.K) (v : List (G M (.inr k))) :
    Function.update (mk M i a S) (.inr k) v = mk M i a (Function.update S k v) := by
  funext k'
  rcases k' with (_ | _) | k'
  · simp [Function.update, mk]
  · simp [Function.update, mk]
  · by_cases h : k' = k
    · subst h; simp [Function.update, mk]
    · simp [Function.update, mk, h]

def liftCfg (c : TM2.Cfg M.Γ M.Λ M.σ) : (N M e).Cfg :=
  ⟨c.l.map .inl, (c.var, none), mk M [] [] c.stk⟩

def cfg (l : Ph) (o : Option Bool) (i a : List Bool) (S : ∀ k, List (M.Γ k)) : (N M e).Cfg :=
  ⟨some (.inr l), (M.initialState, o), mk M i a S⟩

lemma stepAux_lift (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (liftStmt M q) (v, none) (mk M [] [] S) = liftCfg (e := e) (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push _ _ _ ih | pop _ _ _ ih => simp only [liftStmt, TM2.stepAux, upd_inr]; exact ih _ _
  | peek _ _ _ ih | load _ _ ih => simp only [liftStmt, TM2.stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ => simp only [liftStmt, TM2.stepAux, ih₁, ih₂]; cases f v <;> rfl
  | goto | halt => rfl

lemma step_lift (c : TM2.Cfg M.Γ M.Λ M.σ) :
    (N M e).step (liftCfg c) = (M.step c).map liftCfg := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · show some (TM2.stepAux (liftStmt M (M.m l)) (v, none) (mk M [] [] S)) = _
    rw [stepAux_lift]; rfl

lemma iterate_lift (n : ℕ) (o : Option (TM2.Cfg M.Γ M.Λ M.σ)) :
    (flip bind (N M e).step)^[n] (o.map liftCfg) = ((flip bind M.step)^[n] o).map liftCfg := by
  refine ((Function.Semiconj.iterate_right ?_ n) o).symm
  rintro (_ | c)
  · rfl
  · show (M.step c).map liftCfg = (N M e).step (liftCfg c)
    rw [step_lift]

lemma parse_run (s rest a : List Bool) (o : Option Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e).step (cfg .parse o (BitstringEncoding.delimit s ++ rest) a S)
      (some (cfg .erase (some false) rest (s.reverse ++ a) S)) (s.length + 1) := by
  induction s generalizing a o with
  | nil =>
    refine RIn.single ?_
    show some (TM2.stepAux (prog M e (.inr .parse)) (M.initialState, o) (mk M (false :: rest) a S)) = _
    simp [prog, TM2.stepAux, mk, cfg]; rfl
  | cons c s ih =>
    have h1 : RIn (N M e).step (cfg .parse o (true :: c :: (BitstringEncoding.delimit s ++ rest)) a S)
        (some (cfg .parse (some c) (BitstringEncoding.delimit s ++ rest) (c :: a) S)) 1 := by
      refine RIn.single ?_
      show some (TM2.stepAux (prog M e (.inr .parse)) (M.initialState, o) (mk M _ a S)) = _
      simp [prog, TM2.stepAux, mk, cfg]; rfl
    simpa [BitstringEncoding.delimit, List.reverse_cons, List.append_assoc, Nat.add_comm] using
      h1.trans (ih (c :: a) (some c))

lemma erase_run (t a : List Bool) (o : Option Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e).step (cfg .erase o t a S) (some (cfg .move none [] a S)) (t.length + 1) := by
  induction t generalizing o with
  | nil =>
    refine RIn.single ?_
    show some (TM2.stepAux (prog M e (.inr .erase)) (M.initialState, o) (mk M [] a S)) = _
    simp [prog, TM2.stepAux, mk, cfg]; rfl
  | cons b t ih =>
    have h1 : RIn (N M e).step (cfg .erase o (b :: t) a S) (some (cfg .erase (some b) t a S)) 1 := by
      refine RIn.single ?_
      show some (TM2.stepAux (prog M e (.inr .erase)) (M.initialState, o) (mk M (b :: t) a S)) = _
      simp [prog, TM2.stepAux, mk, cfg]; rfl
    simpa [Nat.add_comm] using h1.trans (ih (some b))

lemma move_run (a : List Bool) (o : Option Bool) (S : ∀ k, List (M.Γ k)) :
    RIn (N M e).step (cfg .move o [] a S)
      (some (liftCfg ⟨some M.main, M.initialState,
        Function.update S M.k₀ ((a.map e.symm).reverse ++ S M.k₀)⟩))
      (a.length + 1) := by
  induction a generalizing o S with
  | nil =>
    simp only [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
    refine RIn.single ?_
    show some (TM2.stepAux (prog M e (.inr .move)) (M.initialState, o) (mk M [] [] S)) = _
    simp [prog, TM2.stepAux, mk, cfg, liftCfg]; rfl
  | cons c a ih =>
    have h1 : RIn (N M e).step (cfg .move o [] (c :: a) S)
        (some (cfg .move (some c) [] a (Function.update S M.k₀ (e.symm c :: S M.k₀)))) 1 := by
      refine RIn.single ?_
      show some (TM2.stepAux (prog M e (.inr .move)) (M.initialState, o) (mk M [] (c :: a) S)) = _
      simp [prog, TM2.stepAux, mk, cfg]; rfl
    have := h1.trans (ih (some c) _)
    simp only [Function.update_self, Function.update_idem] at this
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using this

lemma haltList_lift (s : List (M.Γ M.k₁)) : liftCfg (e := e) (haltList M s) = haltList (N M e) s := by
  simp only [liftCfg, haltList]; congr 1; funext k
  rcases k with (_ | _) | k
  · rfl
  · rfl
  · by_cases h : k = M.k₁
    · subst h; simp only [mk]; split
      · split
        · rfl
        · rename_i hne; exact absurd rfl hne
      · rename_i hne; exact absurd trivial hne
    · simp only [mk, dif_neg h]; split
      · rename_i heq; exact absurd (Sum.inr_injective (heq : (Sum.inr k : Bool ⊕ M.K) = .inr M.k₁)) h
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

end OMA.PBPP

open OMA.PBPP in
theorem OMA.solution : type_of% @ComplexityTheory.P_subset_BPP := by
  intro L ⟨M⟩
  refine ⟨0, fun q => L q.1, ⟨{
    tm := N M.tm M.inputAlphabet
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := M.outputAlphabet
    time := Polynomial.X + 2 + M.time
    outputsFun := fun p => ?_ }⟩, by simp; norm_num⟩
  set s := BitstringEncoding.bitEncode p.1
  set t := BitstringEncoding.bitEncode p.2
  have henc : (BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode p =
      BitstringEncoding.delimit s ++ t := rfl
  have hin : List.map ((Equiv.refl Bool : (N M.tm M.inputAlphabet).Γ (N M.tm M.inputAlphabet).k₀ ≃
      Bool).invFun) ((BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode p) =
      BitstringEncoding.delimit s ++ t := by rw [henc]; exact List.map_id _
  have hinit : initList (N M.tm M.inputAlphabet) (BitstringEncoding.delimit s ++ t) =
      cfg .parse none (BitstringEncoding.delimit s ++ t) [] (fun _ => []) := by
    simp only [initList, cfg]; congr 1; funext k; rcases k with (_ | _) | k <;> rfl
  have hM : liftCfg (e := M.inputAlphabet) ⟨some M.tm.main, M.tm.initialState,
      Function.update (fun _ => []) M.tm.k₀ (List.map M.inputAlphabet.symm s)⟩ =
      liftCfg (e := M.inputAlphabet) (initList M.tm (List.map M.inputAlphabet.invFun s)) := by
    simp only [initList]; congr 3; funext k
    by_cases h : k = M.tm.k₀
    · subst h; simp
    · rw [Function.update_of_ne h, dif_neg h]
  have h1 := parse_run (M := M.tm) (e := M.inputAlphabet) s t [] none (fun _ => [])
  have h2 := erase_run (M := M.tm) (e := M.inputAlphabet) t (s.reverse ++ []) (some false) (fun _ => [])
  have h3 := move_run (M := M.tm) (e := M.inputAlphabet) (s.reverse ++ []) none (fun _ => [])
  have h4 := run_M M.tm M.inputAlphabet (M.outputsFun p.1)
  simp only [List.append_nil, List.map_reverse, List.reverse_reverse, List.length_reverse] at h1 h2 h3
  rw [hM] at h3
  have hrun := hinit ▸ ((h1.trans h2).trans h3).trans h4
  have hn : ((BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode p).length =
      2 * s.length + 1 + t.length := by rw [henc]; simp [BitstringEncoding.length_delimit]
  have hb : (s.length + 1) + (t.length + 1) + (s.length + 1) + M.time.eval s.length ≤
      (Polynomial.X + 2 + M.time).eval
        ((BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode p).length := by
    rw [hn]; simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    have := eval_mono M.time (show s.length ≤ 2 * s.length + 1 + t.length by omega)
    omega
  have key : ∀ l : List Bool, l = BitstringEncoding.delimit s ++ t →
      TM2OutputsInTime (N M.tm M.inputAlphabet) l
        (some (List.map M.outputAlphabet.invFun
          ((BitstringEncoding.toEncoding (α := Bool)).encode (L p.1))))
        ((Polynomial.X + 2 + M.time).eval
          ((BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode p).length) := by
    rintro l rfl
    exact Classical.choice (let ⟨n, hle, he⟩ := hrun.mono hb; ⟨⟨⟨n, he⟩, hle⟩⟩)
  exact key _ hin
