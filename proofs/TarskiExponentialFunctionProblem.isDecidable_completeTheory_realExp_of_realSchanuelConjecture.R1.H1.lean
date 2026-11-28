import OMAReductions.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_realExp_of_realSchanuelConjecture_R1
import Mathlib.Data.Fin.Tuple.Take


/-! Exact computable recognition of the pinned sentence codes for Macintyre–Wilkie. -/


/- The raw numeric tokens of the pinned ordered exponential field encoding. -/

namespace TarskiMWSentenceCodes

open FirstOrder FirstOrder.Language

abbrev L := Language.orderedExpField
abbrev FuncSymbol := Σ n, L.Functions n
abbrev RelSymbol := Σ n, L.Relations n
abbrev Term (k : ℕ) := L.Term (Empty ⊕ Fin k)
abbrev TermSymbol (k : ℕ) := (Empty ⊕ Fin k) ⊕ FuncSymbol
abbrev FormulaSymbol := (Σ k, Term k) ⊕ (RelSymbol ⊕ ℕ)

def termTokens {k : ℕ} (t : Term k) : List ℕ :=
  t.listEncode.map Encodable.encode

def formulaTokens {k : ℕ} (φ : L.BoundedFormula Empty k) : List ℕ :=
  φ.listEncode.map Encodable.encode

theorem encode_list_map_encode {α : Type*} [Encodable α] (l : List α) :
    Encodable.encode (l.map Encodable.encode) = Encodable.encode l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, Encodable.encode_list_cons, Encodable.encode_nat, ih]

theorem term_encode_eq_tokens {k : ℕ} (t : Term k) :
    Encodable.encode t = Encodable.encode (termTokens t) := by
  change Encodable.encode t.listEncode = Encodable.encode (termTokens t)
  exact (encode_list_map_encode _).symm

theorem formula_encode_eq_tokens {k : ℕ} (φ : L.BoundedFormula Empty k) :
    Encodable.encode φ = Encodable.encode (formulaTokens φ) := by
  change Encodable.encode φ.listEncode = Encodable.encode (formulaTokens φ)
  exact (encode_list_map_encode _).symm

theorem sentence_code_iff_tokens (n : ℕ) :
    (∃ φ : L.Sentence, Encodable.encode φ = n) ↔
      ∃ φ : L.Sentence, formulaTokens φ = Denumerable.ofNat (List ℕ) n := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, ?_⟩
    rw [formula_encode_eq_tokens] at hφ
    rw [← hφ, Denumerable.ofNat_encode]
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, by rw [formula_encode_eq_tokens, hφ, Denumerable.encode_ofNat]⟩

/-- A computable recognizer on raw token lists gives exactly the desired recognizable range. -/
theorem computable_sentence_range_of_checker {check : List ℕ → Bool} (hcheck : Computable check)
    (hexact : ∀ l : List ℕ, check l = true ↔ ∃ φ : L.Sentence, formulaTokens φ = l) :
    ComputablePred (fun n : ℕ => ∃ φ : L.Sentence, Encodable.encode φ = n) := by
  apply ComputablePred.computable_iff.mpr
  refine ⟨check ∘ Denumerable.ofNat (List ℕ), hcheck.comp (Computable.ofNat _), ?_⟩
  funext n
  exact propext ((sentence_code_iff_tokens n).trans (hexact _).symm)

theorem encode_term_variable {k : ℕ} (i : Fin k) :
    Encodable.encode (Sum.inl (Sum.inr i) : TermSymbol k) = 4 * (i : ℕ) + 2 := by
  change 2 * (2 * (i : ℕ) + 1) = _
  omega

theorem encode_formula_term (k : ℕ) (t : Term k) :
    Encodable.encode (Sum.inl ⟨k, t⟩ : FormulaSymbol) =
      2 * Nat.pair k (Encodable.encode (termTokens t)) := by
  change 2 * Nat.pair k (Encodable.encode t) = _
  rw [term_encode_eq_tokens]

theorem encode_formula_marker (n : ℕ) :
    Encodable.encode (Sum.inr (Sum.inr n) : FormulaSymbol) = 4 * n + 3 := by
  change 2 * (2 * n + 1) + 1 = _
  omega

theorem relation_token_info (r : RelSymbol) :
    r.1 = 2 ∧ Encodable.encode (Sum.inr (Sum.inl r) : FormulaSymbol) = 13 := by
  obtain ⟨n, r⟩ := r
  rcases r with r | (r | r)
  · exact isEmptyElim r
  · exact isEmptyElim r
  · cases r
    exact ⟨rfl, rfl⟩

def symbolArity {k : ℕ} : TermSymbol k → ℕ
  | Sum.inl _ => 0
  | Sum.inr a => a.1

/-- The arithmetic classifier for the pinned term symbols at binder depth k. -/
def termArity (k c : ℕ) : Option ℕ :=
  if c = 1 ∨ c = 5 then some 2
  else if c = 3 ∨ c = 9 then some 1
  else if c = 13 ∨ c = 17 then some 0
  else if c % 4 = 2 ∧ c / 4 < k then some 0
  else none

theorem termArity_encode {k : ℕ} (s : TermSymbol k) :
    termArity k (Encodable.encode s) = some (symbolArity s) := by
  rcases s with (v | i) | ⟨n, f⟩
  · exact isEmptyElim v
  · rw [encode_term_variable]
    have h₁ : ¬ (4 * (i : ℕ) + 2 = 1 ∨ 4 * (i : ℕ) + 2 = 5) := by omega
    have h₂ : ¬ (4 * (i : ℕ) + 2 = 3 ∨ 4 * (i : ℕ) + 2 = 9) := by omega
    have h₃ : ¬ (4 * (i : ℕ) + 2 = 13 ∨ 4 * (i : ℕ) + 2 = 17) := by omega
    have h₄ : (4 * (i : ℕ) + 2) % 4 = 2 ∧ (4 * (i : ℕ) + 2) / 4 < k := by
      have hi := i.isLt
      omega
    simp only [termArity, if_neg h₁, if_neg h₂, if_neg h₃, if_pos h₄, symbolArity]
  · rcases f with f | (f | f)
    · cases f <;> rfl
    · cases f
      rfl
    · exact isEmptyElim f

theorem termArity_eq_some {k c a : ℕ} :
    termArity k c = some a ↔
      ∃ s : TermSymbol k, Encodable.encode s = c ∧ symbolArity s = a := by
  constructor
  · intro h
    unfold termArity at h
    split at h
    · rename_i hc
      have ha : a = 2 := (Option.some.inj h).symm
      rcases hc with rfl | rfl
      · exact ⟨Sum.inr ⟨2, Sum.inl Ring.addFunc⟩, rfl, ha.symm⟩
      · exact ⟨Sum.inr ⟨2, Sum.inl Ring.mulFunc⟩, rfl, ha.symm⟩
    · split at h
      · rename_i hc
        have ha : a = 1 := (Option.some.inj h).symm
        rcases hc with rfl | rfl
        · exact ⟨Sum.inr ⟨1, Sum.inr (Sum.inl FirstOrder.expFunc.exp)⟩, rfl, ha.symm⟩
        · exact ⟨Sum.inr ⟨1, Sum.inl Ring.negFunc⟩, rfl, ha.symm⟩
      · split at h
        · rename_i hc
          have ha : a = 0 := (Option.some.inj h).symm
          rcases hc with rfl | rfl
          · exact ⟨Sum.inr ⟨0, Sum.inl Ring.zeroFunc⟩, rfl, ha.symm⟩
          · exact ⟨Sum.inr ⟨0, Sum.inl Ring.oneFunc⟩, rfl, ha.symm⟩
        · split at h
          · rename_i hc
            have ha : a = 0 := (Option.some.inj h).symm
            let i : Fin k := ⟨c / 4, hc.2⟩
            refine ⟨Sum.inl (Sum.inr i), ?_, ha.symm⟩
            rw [encode_term_variable]
            change 4 * (c / 4) + 2 = c
            omega
          · contradiction
  · rintro ⟨s, rfl, rfl⟩
    exact termArity_encode s

theorem termArity_primrec : Primrec₂ termArity := by
  let c : ℕ × ℕ → ℕ := Prod.snd
  have hc : Primrec c := Primrec.snd
  have hEq (n : ℕ) : PrimrecPred (fun p => c p = n) :=
    Primrec.eq.comp hc (Primrec.const n)
  have hRem : PrimrecPred (fun p => c p % 4 = 2) :=
    Primrec.eq.comp (Primrec.nat_mod.comp hc (Primrec.const 4)) (Primrec.const 2)
  have hDiv : PrimrecPred (fun p : ℕ × ℕ => c p / 4 < p.1) :=
    Primrec.nat_lt.comp (Primrec.nat_div.comp hc (Primrec.const 4)) Primrec.fst
  exact Primrec.to₂ (Primrec.ite ((hEq 1).or (hEq 5)) (Primrec.const (some 2))
    (Primrec.ite ((hEq 3).or (hEq 9)) (Primrec.const (some 1))
      (Primrec.ite ((hEq 13).or (hEq 17)) (Primrec.const (some 0))
        (Primrec.ite (hRem.and hDiv) (Primrec.const (some 0)) (Primrec.const none)))))

end TarskiMWSentenceCodes


/- A primitive-recursive recognizer for exactly the pinned term codes. -/

namespace TarskiMWTermParser

open FirstOrder FirstOrder.Language TarskiMWSentenceCodes

/-- A symbol of arity a replaces a terms on the forest stack by one. -/
def advance (k c : ℕ) (r : Option ℕ) : Option ℕ :=
  (termArity k c).bind fun a =>
    r.bind fun size => if a ≤ size then some (size - a + 1) else none

def termCount (k : ℕ) (l : List ℕ) : Option ℕ :=
  l.foldr (advance k) (some 0)

theorem advance_primrec : Primrec (fun p : ℕ × (ℕ × Option ℕ) => advance p.1 p.2.1 p.2.2) := by
  let a : (ℕ × (ℕ × Option ℕ)) × ℕ → ℕ := Prod.snd
  let size : ((ℕ × (ℕ × Option ℕ)) × ℕ) × ℕ → ℕ := Prod.snd
  have ha : Primrec a := Primrec.snd
  have hsize : Primrec size := Primrec.snd
  have hle : PrimrecPred (fun p => a p.1 ≤ size p) :=
    Primrec.nat_le.comp (ha.comp Primrec.fst) hsize
  have hC : Primrec (fun p => if a p.1 ≤ size p then some (size p - a p.1 + 1) else none) :=
    Primrec.ite hle
      (Primrec.option_some.comp (Primrec.succ.comp (Primrec.nat_sub.comp hsize (ha.comp Primrec.fst))))
      (Primrec.const none)
  exact Primrec.option_bind (termArity_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.to₂ (Primrec.option_bind (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.to₂ hC)))

theorem termCount_primrec : Primrec₂ termCount := by
  change Primrec₂ (fun k (l : List ℕ) => l.foldr (advance k) (some 0))
  exact Primrec.to₂ (Primrec.list_foldr Primrec.snd (Primrec.const (some 0))
    (Primrec.to₂ (advance_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))))

theorem termTokens_var {k : ℕ} (x : Empty ⊕ Fin k) :
    termTokens (Language.Term.var x : TarskiMWSentenceCodes.Term k) =
      [Encodable.encode (Sum.inl x : TermSymbol k)] := rfl

theorem termTokens_func {k a : ℕ} (f : L.Functions a) (ts : Fin a → TarskiMWSentenceCodes.Term k) :
    termTokens (Language.Term.func f ts) =
      Encodable.encode (Sum.inr ⟨a, f⟩ : TermSymbol k) ::
        (List.finRange a).flatMap (fun i => termTokens (ts i)) := by
  simp [termTokens, Language.Term.listEncode, List.map_flatMap]

theorem count_append_term {k : ℕ} (t : TarskiMWSentenceCodes.Term k) (l : List ℕ) {n : ℕ}
    (hl : termCount k l = some n) : termCount k (termTokens t ++ l) = some (n + 1) := by
  induction t generalizing l n with
  | var x =>
    rw [termTokens_var]
    change advance k (Encodable.encode (Sum.inl x : TermSymbol k)) (termCount k l) = some (n + 1)
    simp only [advance, termArity_encode, symbolArity, hl, Option.bind_some, Nat.zero_le,
      if_pos, Nat.sub_zero]
  | @func a f ts ih =>
    have hArgs (xs : List (Fin a)) :
        termCount k (xs.flatMap (fun i => termTokens (ts i)) ++ l) = some (n + xs.length) := by
      induction xs with
      | nil => simpa using hl
      | cons x xs hx =>
        rw [List.flatMap_cons, List.append_assoc]
        simpa only [List.length_cons, Nat.add_assoc] using ih x _ hx
    rw [termTokens_func, List.cons_append]
    change advance k (Encodable.encode (Sum.inr ⟨a, f⟩ : TermSymbol k))
      (termCount k ((List.finRange a).flatMap (fun i => termTokens (ts i)) ++ l)) = some (n + 1)
    rw [hArgs, List.length_finRange]
    simp only [advance, termArity_encode, symbolArity, Option.bind_some]
    have hle : a ≤ n + a := by omega
    simp only [if_pos hle, Option.some.injEq]
    omega

theorem count_forest_tokens {k : ℕ} (ts : List (TarskiMWSentenceCodes.Term k)) :
    termCount k (ts.flatMap termTokens) = some ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.flatMap_cons, List.length_cons]
    exact count_append_term t _ ih

theorem forest_of_count {k n : ℕ} {l : List ℕ} (hl : termCount k l = some n) :
    ∃ ts : List (TarskiMWSentenceCodes.Term k), ts.length = n ∧ ts.flatMap termTokens = l := by
  induction l generalizing n with
  | nil =>
    change some 0 = some n at hl
    exact ⟨[], Option.some.inj hl, rfl⟩
  | cons c l ih =>
    change advance k c (termCount k l) = some n at hl
    cases ha : termArity k c with
    | none => simp [advance, ha] at hl
    | some a =>
      cases hcount : termCount k l with
      | none => simp [advance, ha, hcount] at hl
      | some m =>
        have hValid : a ≤ m := by
          by_contra h
          simp [advance, ha, hcount, h] at hl
        have hn : m - a + 1 = n := by simpa [advance, ha, hcount, hValid] using hl
        obtain ⟨ts, hts, rfl⟩ := ih hcount
        obtain ⟨s, hc, hs⟩ := termArity_eq_some.mp ha
        rcases s with x | ⟨i, f⟩
        · change 0 = a at hs
          subst a
          refine ⟨Language.Term.var x :: ts, by simp [hts, ← hn], ?_⟩
          simp [termTokens_var, hc]
        · change i = a at hs
          subst a
          have hI : i ≤ ts.length := hts.symm ▸ hValid
          let args := Fin.take i hI ts.get
          have hArgList : (List.finRange i).map args = ts.take i := by
            rw [← List.ofFn_eq_map]
            exact Fin.ofFn_take_get ts hI
          refine ⟨Language.Term.func f args :: ts.drop i, ?_, ?_⟩
          · simp only [List.length_cons, List.length_drop, hts, hn]
          · simp only [List.flatMap_cons, termTokens_func, List.cons_append, hc]
            rw [← List.flatMap_map, hArgList, ← List.flatMap_append, List.take_append_drop]

/-- A single complete term, recognized without consulting the permissive decoder. -/
def checkTermCode (k n : ℕ) : Bool :=
  decide (termCount k (Denumerable.ofNat (List ℕ) n) = some 1)

theorem checkTermCode_primrec : Primrec₂ checkTermCode := by
  change Primrec₂ (fun k n => decide (termCount k (Denumerable.ofNat (List ℕ) n) = some 1))
  exact Primrec.to₂ ((Primrec.eq.comp
    (termCount_primrec.comp Primrec.fst ((Primrec.ofNat _).comp Primrec.snd))
    (Primrec.const (some 1))).decide)

theorem checkTermCode_iff (k n : ℕ) :
    checkTermCode k n = true ↔
      ∃ t : TarskiMWSentenceCodes.Term k, Encodable.encode t = n := by
  simp only [checkTermCode, decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨l, hl, hcode⟩ := forest_of_count h
    obtain ⟨t, rfl⟩ := List.length_eq_one_iff.mp hl
    refine ⟨t, ?_⟩
    rw [term_encode_eq_tokens]
    simp only [List.flatMap_singleton] at hcode
    rw [hcode, Denumerable.encode_ofNat]
  · rintro ⟨t, ht⟩
    rw [term_encode_eq_tokens] at ht
    rw [← ht, Denumerable.ofNat_encode]
    simpa only [List.append_nil] using count_append_term t [] rfl

end TarskiMWTermParser


/- A primitive-recursive list scan that retains the results of four suffixes. -/

namespace TarskiMWFormulaLookback

abbrev Roll (σ : Type*) := σ × σ × σ × σ

def scan {σ : Type*} (base : σ) (step : ℕ × (List ℕ × Roll σ) → σ) :
    List ℕ → Roll σ
  | [] => (base, base, base, base)
  | c :: l =>
      let r := scan base step l
      (step (c, l, r), r.1, r.2.1, r.2.2.1)

def parse {σ : Type*} (base : σ) (step : ℕ × (List ℕ × Roll σ) → σ)
    (l : List ℕ) : σ :=
  (scan base step l).1

@[simp] theorem parse_nil {σ : Type*} (base : σ) (step : ℕ × (List ℕ × Roll σ) → σ) :
    parse base step [] = base := rfl

theorem scan_eq_lookbacks {σ : Type*} (base : σ) (step : ℕ × (List ℕ × Roll σ) → σ)
    (l : List ℕ) :
    scan base step l =
      (parse base step l, parse base step (l.drop 1),
        parse base step (l.drop 2), parse base step (l.drop 3)) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
      change (step (c, l, scan base step l), parse base step l,
          (scan base step l).2.1, (scan base step l).2.2.1) =
        (step (c, l, scan base step l), parse base step l,
          parse base step (l.drop 1), parse base step (l.drop 2))
      rw [congrArg (fun r : Roll σ => r.2.1) ih, congrArg (fun r : Roll σ => r.2.2.1) ih]

@[simp] theorem parse_cons {σ : Type*} (base : σ) (step : ℕ × (List ℕ × Roll σ) → σ)
    (c : ℕ) (l : List ℕ) :
    parse base step (c :: l) =
      step (c, l, (parse base step l, parse base step (l.drop 1),
        parse base step (l.drop 2), parse base step (l.drop 3))) := by
  change step (c, l, scan base step l) = _
  rw [scan_eq_lookbacks]

theorem scan_primrec {σ : Type*} [Primcodable σ] (base : σ)
    {step : ℕ × (List ℕ × Roll σ) → σ} (hStep : Primrec step) :
    Primrec (scan base step) := by
  let advance (p : ℕ × (List ℕ × Roll σ)) : Roll σ :=
    (step p, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1)
  have hRoll : Primrec (fun p : ℕ × (List ℕ × Roll σ) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hAdvance : Primrec advance :=
    Primrec.pair hStep (Primrec.pair (Primrec.fst.comp hRoll)
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp hRoll))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hRoll)))))
  refine (Primrec.list_rec Primrec.id (Primrec.const (base, base, base, base))
    (Primrec.to₂ (hAdvance.comp Primrec.snd))).of_eq ?_
  intro l
  change List.rec (base, base, base, base) (fun c l r => advance (c, l, r)) l =
    scan base step l
  induction l with
  | nil => rfl
  | cons c l ih =>
      change advance (c, l, List.rec (base, base, base, base)
        (fun c l r => advance (c, l, r)) l) = advance (c, l, scan base step l)
      rw [ih]

theorem parse_primrec {σ : Type*} [Primcodable σ] (base : σ)
    {step : ℕ × (List ℕ × Roll σ) → σ} (hStep : Primrec step) :
    Primrec (parse base step) :=
  Primrec.fst.comp (scan_primrec base hStep)

end TarskiMWFormulaLookback



/- The constructor equations for the pinned raw formula tokens. -/

namespace TarskiMWFormulaSyntax

open FirstOrder FirstOrder.Language TarskiMWSentenceCodes

def rawTerm (k : ℕ) (t : Term k) : ℕ :=
  2 * Nat.pair k (Encodable.encode t)

def rawMark (k : ℕ) : ℕ :=
  4 * k + 3

private theorem encode_term_symbol (k : ℕ) (t : Term k) :
    Encodable.encode (Sum.inl ⟨k, t⟩ : FormulaSymbol) = rawTerm k t :=
  rfl

private theorem encode_marker_symbol (k : ℕ) :
    Encodable.encode (Sum.inr (Sum.inr k) : FormulaSymbol) = rawMark k :=
  encode_formula_marker k

theorem tokens_falsum (k : ℕ) :
    formulaTokens (BoundedFormula.falsum : L.BoundedFormula Empty k) = [rawMark (k + 2)] := by
  simp only [formulaTokens, BoundedFormula.listEncode, List.map_cons, List.map_nil,
    encode_marker_symbol]

theorem tokens_equal {k : ℕ} (t u : Term k) :
    formulaTokens (BoundedFormula.equal t u) = [rawTerm k t, rawTerm k u] := by
  simp only [formulaTokens, BoundedFormula.listEncode, List.map_cons, List.map_nil,
    encode_term_symbol]

theorem tokens_rel {k : ℕ} (R : L.Relations 2) (ts : Fin 2 → Term k) :
    formulaTokens (BoundedFormula.rel R ts) =
      [13, rawMark k, rawTerm k (ts 0), rawTerm k (ts 1)] := by
  have hRel := (relation_token_info (⟨2, R⟩ : RelSymbol)).2
  change [Encodable.encode (Sum.inr (Sum.inl ⟨2, R⟩) : FormulaSymbol),
    Encodable.encode (Sum.inr (Sum.inr k) : FormulaSymbol),
    rawTerm k (ts 0), rawTerm k (ts 1)] = _
  rw [hRel, encode_marker_symbol]

theorem tokens_imp {k : ℕ} (φ ψ : L.BoundedFormula Empty k) :
    formulaTokens (.imp φ ψ) = rawMark 0 :: (formulaTokens φ ++ formulaTokens ψ) := by
  simp only [formulaTokens, BoundedFormula.listEncode, List.cons_append, List.map_cons,
    List.map_append, encode_marker_symbol]

theorem tokens_all {k : ℕ} (φ : L.BoundedFormula Empty (k + 1)) :
    formulaTokens (.all φ) = rawMark 1 :: formulaTokens φ := by
  simp only [formulaTokens, BoundedFormula.listEncode, List.map_cons, encode_marker_symbol]

end TarskiMWFormulaSyntax



/- A strict primitive-recursive parser for the pinned numeric formula syntax. -/

namespace TarskiMWFormulaParser

open FirstOrder FirstOrder.Language TarskiMWSentenceCodes TarskiMWTermParser
open TarskiMWFormulaLookback

abbrev CtxStack := Option (List ℕ)
abbrev ParseInput := ℕ × (List ℕ × Roll CtxStack)
abbrev Formula := Σ k, L.BoundedFormula Empty k

def termDepth (c : ℕ) : Option ℕ :=
  if c % 2 = 0 then
    let p := (c / 2).unpair
    bif checkTermCode p.1 p.2 then some p.1 else none
  else none

def markerDepth (c : ℕ) : Option ℕ :=
  if c % 4 = 3 then some (c / 4) else none

def commonDepth (a b : Option ℕ) : Option ℕ :=
  a.bind fun n => if b = some n then some n else none

def pushDepth (a : Option ℕ) (r : CtxStack) : CtxStack :=
  a.bind fun n => r.map (List.cons n)

def impStack (l : List ℕ) : CtxStack :=
  l.head?.bind fun a => l.tail.head?.bind fun b =>
    if a = b then some (a :: l.tail.tail) else none

def allStack (l : List ℕ) : CtxStack :=
  l.head?.bind fun n => if 0 < n then some ((n - 1) :: l.tail) else none

def markerStep (n : ℕ) (r : CtxStack) : CtxStack :=
  if n = 0 then r.bind impStack
  else if n = 1 then r.bind allStack
  else pushDepth (some (n - 2)) r

def markAt (l : List ℕ) : Option ℕ :=
  l.head?.bind markerDepth

def termAt (i : ℕ) (l : List ℕ) : Option ℕ :=
  l[i]?.bind termDepth

/-- The upstream grammar uses two raw term tokens for equality and an order
tag, context tag and two raw term tokens for the order relation. -/
def formulaStep (p : ParseInput) : CtxStack :=
  let c := p.1
  let l := p.2.1
  let r := p.2.2
  if c % 2 = 0 then
    pushDepth (commonDepth (termDepth c) (termAt 0 l)) r.2.1
  else if c = 13 then
    pushDepth (commonDepth (commonDepth (markAt l) (termAt 1 l)) (termAt 2 l)) r.2.2.2
  else (markerDepth c).bind fun m => markerStep m r.1

def parseCtx (l : List ℕ) : CtxStack :=
  parse (some []) formulaStep l

theorem termDepth_primrec : Primrec termDepth := by
  have hEven : PrimrecPred (fun c : ℕ => c % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)
  let p (c : ℕ) := (c / 2).unpair
  have hp : Primrec p := Primrec.unpair.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
  exact Primrec.ite hEven
    (Primrec.cond (checkTermCode_primrec.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp))
      (Primrec.option_some.comp (Primrec.fst.comp hp)) (Primrec.const none)) (Primrec.const none)

theorem markerDepth_primrec : Primrec markerDepth := by
  have hMark : PrimrecPred (fun c : ℕ => c % 4 = 3) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 4)) (Primrec.const 3)
  exact Primrec.ite hMark
    (Primrec.option_some.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 4)))
    (Primrec.const none)

theorem commonDepth_primrec : Primrec₂ commonDepth := by
  change Primrec₂ (fun a b : Option ℕ => a.bind fun n => if b = some n then some n else none)
  exact Primrec.to₂ (Primrec.option_bind Primrec.fst (Primrec.to₂
    (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.option_some.comp Primrec.snd)) (Primrec.option_some.comp Primrec.snd) (Primrec.const none))))

theorem pushDepth_primrec : Primrec₂ pushDepth := by
  change Primrec₂ (fun a : Option ℕ => fun r : CtxStack => a.bind fun n => r.map (List.cons n))
  exact Primrec.to₂ (Primrec.option_bind Primrec.fst (Primrec.to₂
    (Primrec.option_map (Primrec.snd.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂)))

theorem impStack_primrec : Primrec impStack := by
  change Primrec (fun l : List ℕ => l.head?.bind fun a => l.tail.head?.bind fun b =>
    if a = b then some (a :: l.tail.tail) else none)
  have hTail : Primrec (fun p : (List ℕ × ℕ) × ℕ => p.1.1.tail.tail) :=
    Primrec.list_tail.comp (Primrec.list_tail.comp (Primrec.fst.comp Primrec.fst))
  have hBody : Primrec (fun p : (List ℕ × ℕ) × ℕ =>
      if p.1.2 = p.2 then some (p.1.2 :: p.1.1.tail.tail) else none) :=
    Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.option_some.comp (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) hTail))
      (Primrec.const none)
  exact Primrec.option_bind Primrec.list_head? (Primrec.to₂
    (Primrec.option_bind (Primrec.list_head?.comp (Primrec.list_tail.comp Primrec.fst)) (Primrec.to₂ hBody)))

theorem allStack_primrec : Primrec allStack := by
  change Primrec (fun l : List ℕ => l.head?.bind fun n => if 0 < n then some ((n - 1) :: l.tail) else none)
  have hsub : Primrec (fun p : List ℕ × ℕ => p.2 - 1) :=
    Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)
  exact Primrec.option_bind Primrec.list_head? (Primrec.to₂
    (Primrec.ite (Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd)
      (Primrec.option_some.comp (Primrec.list_cons.comp hsub (Primrec.list_tail.comp Primrec.fst)))
      (Primrec.const none)))

theorem markerStep_primrec : Primrec₂ markerStep := by
  change Primrec₂ (fun n : ℕ => fun r : CtxStack =>
    if n = 0 then r.bind impStack
    else if n = 1 then r.bind allStack else pushDepth (some (n - 2)) r)
  exact Primrec.to₂
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
      ((Primrec.option_bind₁ impStack_primrec).comp Primrec.snd)
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
        ((Primrec.option_bind₁ allStack_primrec).comp Primrec.snd)
        (pushDepth_primrec.comp
          (Primrec.option_some.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.const 2))) Primrec.snd)))

theorem markAt_primrec : Primrec markAt :=
  (Primrec.option_bind₁ markerDepth_primrec).comp Primrec.list_head?

theorem termAt_primrec (i : ℕ) : Primrec (termAt i) :=
  (Primrec.option_bind₁ termDepth_primrec).comp (Primrec.list_getElem?.comp Primrec.id (Primrec.const i))

theorem formulaStep_primrec : Primrec formulaStep := by
  let c (p : ParseInput) := p.1
  let l (p : ParseInput) := p.2.1
  let r (p : ParseInput) := p.2.2
  have hc : Primrec c := Primrec.fst
  have hl : Primrec l := Primrec.fst.comp Primrec.snd
  have hr : Primrec r := Primrec.snd.comp Primrec.snd
  have r1 : Primrec (fun p => (r p).1) := Primrec.fst.comp hr
  have r2 : Primrec (fun p => (r p).2.1) := Primrec.fst.comp (Primrec.snd.comp hr)
  have r4 : Primrec (fun p => (r p).2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hr))
  have hTerm (i : ℕ) : Primrec (fun p => termAt i (l p)) := (termAt_primrec i).comp hl
  have hRel : Primrec (fun p => commonDepth (commonDepth (markAt (l p)) (termAt 1 (l p))) (termAt 2 (l p))) :=
    commonDepth_primrec.comp
      (commonDepth_primrec.comp (markAt_primrec.comp hl) (hTerm 1)) (hTerm 2)
  have hEven : PrimrecPred (fun p => c p % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp hc (Primrec.const 2)) (Primrec.const 0)
  exact Primrec.ite hEven
    (pushDepth_primrec.comp (commonDepth_primrec.comp (termDepth_primrec.comp hc) (hTerm 0)) r2)
    (Primrec.ite (Primrec.eq.comp hc (Primrec.const 13))
      (pushDepth_primrec.comp hRel r4)
      (Primrec.option_bind (markerDepth_primrec.comp hc)
        (markerStep_primrec.comp Primrec.snd (r1.comp Primrec.fst)).to₂))

theorem parseCtx_primrec : Primrec parseCtx :=
  parse_primrec (some []) formulaStep_primrec

theorem parseCtx_nil : parseCtx [] = some [] := rfl

theorem parseCtx_cons (c : ℕ) (l : List ℕ) :
    parseCtx (c :: l) =
      formulaStep (c, l, (parseCtx l, parseCtx (l.drop 1), parseCtx (l.drop 2), parseCtx (l.drop 3))) :=
  parse_cons (some []) formulaStep c l

theorem termDepth_encode {k : ℕ} (t : TarskiMWSentenceCodes.Term k) :
    termDepth (2 * Nat.pair k (Encodable.encode t)) = some k := by
  have hmod : (2 * Nat.pair k (Encodable.encode t)) % 2 = 0 := by omega
  have hdiv : (2 * Nat.pair k (Encodable.encode t)) / 2 = Nat.pair k (Encodable.encode t) := by omega
  have hcheck := (checkTermCode_iff k (Encodable.encode t)).mpr ⟨t, rfl⟩
  simp only [termDepth, hmod, if_pos, hdiv, Nat.unpair_pair, hcheck, Bool.cond_true]

theorem termDepth_eq_some {c k : ℕ} :
    termDepth c = some k ↔
      ∃ t : TarskiMWSentenceCodes.Term k, c = 2 * Nat.pair k (Encodable.encode t) := by
  constructor
  · intro h
    unfold termDepth at h
    split at h
    · rename_i he
      let p := (c / 2).unpair
      have hp : Nat.pair p.1 p.2 = c / 2 := Nat.pair_unpair _
      change (bif checkTermCode p.1 p.2 then some p.1 else none) = some k at h
      cases hcheck : checkTermCode p.1 p.2 with
      | false => simp [hcheck] at h
      | true =>
        have h1 : p.1 = k := by simpa [hcheck] using h
        have hValid : checkTermCode k p.2 = true := h1 ▸ hcheck
        obtain ⟨t, ht⟩ := (checkTermCode_iff k p.2).mp hValid
        refine ⟨t, ?_⟩
        rw [ht, ← h1]
        omega
    · contradiction
  · rintro ⟨t, rfl⟩
    exact termDepth_encode t

theorem markerDepth_eq_some {c k : ℕ} :
    markerDepth c = some k ↔ c = 4 * k + 3 := by
  unfold markerDepth
  split
  · rename_i hc
    simp only [Option.some.injEq]
    omega
  · rename_i hc
    constructor
    · intro h
      contradiction
    · intro h
      exfalso
      apply hc
      omega

@[simp] theorem commonDepth_some (k : ℕ) : commonDepth (some k) (some k) = some k := by
  simp [commonDepth]

theorem commonDepth_eq_some {a b : Option ℕ} {k : ℕ} :
    commonDepth a b = some k ↔ a = some k ∧ b = some k := by
  cases a with
  | none => simp [commonDepth]
  | some d =>
    by_cases hb : b = some d
    · subst b
      simp [commonDepth]
    · simp only [commonDepth, Option.bind_some, if_neg hb, reduceCtorEq, false_iff, not_and,
        Option.some.injEq]
      intro h
      exact fun e => hb (e.trans (congrArg some h.symm))

theorem pushDepth_eq_some {a : Option ℕ} {r : CtxStack} {out : List ℕ} :
    pushDepth a r = some out ↔ ∃ k rest, a = some k ∧ r = some rest ∧ out = k :: rest := by
  cases a <;> cases r <;> simp [pushDepth, eq_comm]

theorem parseCtx_equal {k : ℕ} (t u : TarskiMWSentenceCodes.Term k) (l : List ℕ) :
    parseCtx ((2 * Nat.pair k (Encodable.encode t)) :: (2 * Nat.pair k (Encodable.encode u)) :: l) =
      (parseCtx l).map (List.cons k) := by
  rw [parseCtx_cons]
  have he : (2 * Nat.pair k (Encodable.encode t)) % 2 = 0 := by omega
  simp [formulaStep, he, termDepth_encode, termAt, pushDepth]

theorem parseCtx_relation {k : ℕ} (t u : TarskiMWSentenceCodes.Term k) (l : List ℕ) :
    parseCtx (13 :: (4 * k + 3) :: (2 * Nat.pair k (Encodable.encode t)) ::
      (2 * Nat.pair k (Encodable.encode u)) :: l) = (parseCtx l).map (List.cons k) := by
  rw [parseCtx_cons]
  have hm : markerDepth (4 * k + 3) = some k := markerDepth_eq_some.mpr rfl
  simp [formulaStep, termAt, markAt, hm, termDepth_encode, pushDepth]

theorem parseCtx_marker (k : ℕ) (l : List ℕ) :
    parseCtx ((4 * k + 3) :: l) = markerStep k (parseCtx l) := by
  rw [parseCtx_cons]
  have hEven : ¬ (4 * k + 3) % 2 = 0 := by omega
  have hRel : 4 * k + 3 ≠ 13 := by omega
  have hMark : markerDepth (4 * k + 3) = some k := markerDepth_eq_some.mpr rfl
  simp [formulaStep, hEven, hRel, hMark]

end TarskiMWFormulaParser


/- Each valid formula pushes its binder depth onto the parsed suffix stack. -/

namespace TarskiMWFormulaCompleteness

open FirstOrder FirstOrder.Language TarskiMWSentenceCodes
open TarskiMWFormulaParser TarskiMWFormulaSyntax

theorem count_append_formula {k : ℕ} (f : L.BoundedFormula Empty k) (l : List ℕ)
    {rest : List ℕ} (hr : parseCtx l = some rest) :
    parseCtx (formulaTokens f ++ l) = some (k :: rest) := by
  induction f generalizing l rest with
  | @falsum n =>
    rw [tokens_falsum]
    change parseCtx ((4 * (n + 2) + 3) :: l) = _
    rw [parseCtx_marker, hr]
    have hone : n + 2 ≠ 1 := by omega
    simp [markerStep, pushDepth, hone]
  | @equal n t u =>
    rw [tokens_equal]
    change parseCtx (rawTerm n t :: rawTerm n u :: l) = _
    simpa only [rawTerm, hr, Option.map_some] using parseCtx_equal t u l
  | @rel n a R ts =>
    have ha := (relation_token_info (⟨a, R⟩ : RelSymbol)).1
    change a = 2 at ha
    subst a
    rw [tokens_rel]
    change parseCtx (13 :: rawMark n :: rawTerm n (ts 0) :: rawTerm n (ts 1) :: l) = _
    simpa only [rawMark, rawTerm, hr, Option.map_some] using parseCtx_relation (ts 0) (ts 1) l
  | @imp n f g ihf ihg =>
    rw [tokens_imp, List.cons_append, List.append_assoc]
    change parseCtx ((4 * 0 + 3) :: (formulaTokens f ++ (formulaTokens g ++ l))) = _
    rw [parseCtx_marker, ihf _ (ihg l hr)]
    simp [markerStep, impStack]
  | @all n f ih =>
    rw [tokens_all, List.cons_append]
    change parseCtx ((4 * 1 + 3) :: (formulaTokens f ++ l)) = _
    rw [parseCtx_marker, ih l hr]
    simp [markerStep, allStack]

theorem count_formula {k : ℕ} (f : L.BoundedFormula Empty k) :
    parseCtx (formulaTokens f) = some [k] := by
  simpa only [List.append_nil] using count_append_formula f [] parseCtx_nil

end TarskiMWFormulaCompleteness



/- Soundness of the arithmetic parser with respect to the pinned typed syntax. -/

namespace TarskiMWFormulaSoundness

open FirstOrder FirstOrder.Language TarskiMWSentenceCodes TarskiMWFormulaParser
open TarskiMWFormulaSyntax

abbrev PackedFormula := Σ k, L.BoundedFormula Empty k

def depths (fs : List PackedFormula) : List ℕ :=
  fs.map Sigma.fst

def forestTokens (fs : List PackedFormula) : List ℕ :=
  fs.flatMap fun f => formulaTokens f.2

private theorem impStack_forest {fs : List PackedFormula} {ctx : List ℕ}
    (h : impStack (depths fs) = some ctx) :
    ∃ gs : List PackedFormula, depths gs = ctx ∧ forestTokens gs = rawMark 0 :: forestTokens fs := by
  rcases fs with _ | ⟨⟨i, f⟩, fs⟩
  · simp [depths, impStack] at h
  rcases fs with _ | ⟨⟨j, g⟩, fs⟩
  · simp [depths, impStack] at h
  by_cases hij : i = j
  · subst j
    have hctx : i :: depths fs = ctx := by simpa [depths, impStack] using h
    refine ⟨⟨i, f.imp g⟩ :: fs, hctx, ?_⟩
    simp [forestTokens, tokens_imp, List.append_assoc]
  · simp [depths, impStack, hij] at h

private theorem allStack_forest {fs : List PackedFormula} {ctx : List ℕ}
    (h : allStack (depths fs) = some ctx) :
    ∃ gs : List PackedFormula, depths gs = ctx ∧ forestTokens gs = rawMark 1 :: forestTokens fs := by
  rcases fs with _ | ⟨⟨i, f⟩, fs⟩
  · simp [depths, allStack] at h
  cases i with
  | zero => simp [depths, allStack] at h
  | succ i =>
    have hctx : i :: depths fs = ctx := by simpa [depths, allStack] using h
    refine ⟨⟨i, f.all⟩ :: fs, hctx, ?_⟩
    simp [forestTokens, tokens_all]

private theorem markerStep_forest (m : ℕ) (fs : List PackedFormula) {ctx : List ℕ}
    (h : markerStep m (some (depths fs)) = some ctx) :
    ∃ gs : List PackedFormula, depths gs = ctx ∧ forestTokens gs = rawMark m :: forestTokens fs := by
  cases m with
  | zero => exact impStack_forest (by simpa [markerStep] using h)
  | succ m =>
    cases m with
    | zero => exact allStack_forest (by simpa [markerStep] using h)
    | succ m =>
      have hctx : m :: depths fs = ctx := by simp [markerStep, pushDepth] at h; exact h
      exact ⟨⟨m, .falsum⟩ :: fs, hctx, by simp [forestTokens, tokens_falsum]⟩

private theorem parseCtx_empty_on_marker_failure (m : ℕ) :
    markerStep m none = none := by unfold markerStep; split_ifs <;> rfl

/-- A successful arithmetic parse witnesses exactly a forest of bounded formulas
with the returned depths. Every input token is accounted for. -/
theorem parseCtx_sound {l : List ℕ} {ctx : List ℕ} (h : parseCtx l = some ctx) :
    ∃ fs : List PackedFormula, depths fs = ctx ∧ forestTokens fs = l := by
  induction hlen : l.length using Nat.strong_induction_on generalizing l ctx with
  | _ n ih =>
    cases l with
    | nil =>
      have hz : [] = ctx := by simpa only [parseCtx_nil, Option.some.injEq] using h
      exact ⟨[], hz, rfl⟩
    | cons c l =>
      have hsmall (r : List ℕ) (hr : r.length < (c :: l).length) {ds : List ℕ}
          (hp : parseCtx r = some ds) :
          ∃ fs : List PackedFormula, depths fs = ds ∧ forestTokens fs = r :=
        ih r.length (hlen ▸ hr) hp rfl
      rw [parseCtx_cons] at h
      by_cases hEven : c % 2 = 0
      · have hp : pushDepth (commonDepth (termDepth c) (termAt 0 l))
            (parseCtx (l.drop 1)) = some ctx := by simpa only [formulaStep, if_pos hEven] using h
        obtain ⟨k, ds, hh, hParse, rfl⟩ := pushDepth_eq_some.mp hp
        obtain ⟨hc, hd⟩ := commonDepth_eq_some.mp hh
        cases l with
        | nil => simp [termAt] at hd
        | cons d r =>
          change parseCtx r = some ds at hParse
          have hd' : termDepth d = some k := by simpa [termAt] using hd
          obtain ⟨t, ht⟩ := termDepth_eq_some.mp hc
          obtain ⟨u, hu⟩ := termDepth_eq_some.mp hd'
          obtain ⟨fs, hds, hfs⟩ := hsmall r (by simp only [List.length_cons]; omega) hParse
          refine ⟨⟨k, .equal t u⟩ :: fs, ?_, ?_⟩
          · simp [depths, ← hds]
          · change fs.flatMap (fun f => formulaTokens f.2) = r at hfs
            simp [forestTokens, tokens_equal, hfs, rawTerm, ht, hu]
      · by_cases hRel : c = 13
        · have hp : pushDepth (commonDepth (commonDepth (markAt l) (termAt 1 l)) (termAt 2 l))
                (parseCtx (l.drop 3)) = some ctx := by
              simpa only [formulaStep, if_neg hEven, if_pos hRel] using h
          obtain ⟨k, ds, hh, hParse, rfl⟩ := pushDepth_eq_some.mp hp
          obtain ⟨hh', hu⟩ := commonDepth_eq_some.mp hh
          obtain ⟨hm, ht⟩ := commonDepth_eq_some.mp hh'
          cases l with
          | nil => simp [termAt] at hu
          | cons d l =>
            cases l with
            | nil => simp [termAt] at hu
            | cons e l =>
              cases l with
              | nil => simp [termAt] at hu
              | cons f r =>
                change parseCtx r = some ds at hParse
                have hm' : markerDepth d = some k := by simpa [markAt] using hm
                have ht' : termDepth e = some k := by simpa [termAt] using ht
                have hu' : termDepth f = some k := by simpa [termAt] using hu
                obtain ⟨t, ht⟩ := termDepth_eq_some.mp ht'
                obtain ⟨u, hu⟩ := termDepth_eq_some.mp hu'
                have hMark := markerDepth_eq_some.mp hm'
                obtain ⟨fs, hds, hfs⟩ := hsmall r (by simp only [List.length_cons]; omega) hParse
                let ts : Fin 2 → TarskiMWSentenceCodes.Term k := Fin.cases t (fun _ => u)
                let rel : L.Relations 2 := leSymb
                refine ⟨⟨k, .rel rel ts⟩ :: fs, ?_, ?_⟩
                · simp [depths, ← hds]
                · have h0 : ts 0 = t := rfl
                  have h1 : ts 1 = u := rfl
                  change fs.flatMap (fun f => formulaTokens f.2) = r at hfs
                  simp [forestTokens, tokens_rel, h0, h1, hRel, hMark, ht, hu, hfs, rawTerm, rawMark]
        · have hp : (markerDepth c).bind (fun m => markerStep m (parseCtx l)) = some ctx := by
            simpa only [formulaStep, if_neg hEven, if_neg hRel] using h
          cases hMark : markerDepth c with
          | none => simp [hMark] at hp
          | some m =>
            have hc := markerDepth_eq_some.mp hMark
            cases hSub : parseCtx l with
            | none => simp [hMark, hSub, parseCtx_empty_on_marker_failure] at hp
            | some ds =>
              have hs : markerStep m (some ds) = some ctx := by simpa [hMark, hSub] using hp
              obtain ⟨fs, hd, hf⟩ := hsmall l (by simp) hSub
              rw [← hd] at hs
              obtain ⟨gs, hg, hCode⟩ := markerStep_forest m fs hs
              exact ⟨gs, hg, by simpa only [hf, rawMark, ← hc] using hCode⟩

theorem sentence_of_parseCtx {l : List ℕ} (h : parseCtx l = some [0]) :
    ∃ φ : L.Sentence, formulaTokens φ = l := by
  obtain ⟨fs, hd, hf⟩ := parseCtx_sound h
  have hl : fs.length = 1 := by
    have hlen := congrArg List.length hd
    simpa only [depths, List.length_map, List.length_cons, List.length_nil] using hlen
  obtain ⟨⟨k, φ⟩, rfl⟩ := List.length_eq_one_iff.mp hl
  have hk : k = 0 := by simpa [depths] using hd
  subst k
  exact ⟨φ, by simpa [forestTokens] using hf⟩

end TarskiMWFormulaSoundness


/- Computable recognition of exactly the pinned ordered-exponential-field sentence codes. -/

namespace TarskiMWSentenceCodes

open TarskiMWFormulaParser TarskiMWFormulaSoundness TarskiMWFormulaCompleteness

theorem computable_sentence_range :
    ComputablePred (fun n : ℕ => ∃ φ : L.Sentence, Encodable.encode φ = n) := by
  let check (l : List ℕ) := decide (parseCtx l = some [0])
  have hcheck : Primrec check := (Primrec.eq.comp parseCtx_primrec (Primrec.const (some [0]))).decide
  apply computable_sentence_range_of_checker hcheck.to_comp
  intro l
  simp only [check, decide_eq_true_eq]
  constructor
  · exact sentence_of_parseCtx
  · rintro ⟨φ, rfl⟩
    exact count_formula φ

end TarskiMWSentenceCodes


theorem OMA.solution : OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_realExp_of_realSchanuelConjecture_R1.H1 :=
  TarskiMWSentenceCodes.computable_sentence_range
