import OMAReductions.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_real_orderedField_R1
import Mathlib

-- Step H3 of TarskiExponentialFunctionProblem.isDecidable_completeTheory_real_orderedField.R1.
-- Credit: @LordMike

open FirstOrder FirstOrder.Language Encodable

/-- Glue: a theory that is a finite set of sentences together with the range of a family whose
Goedel codes are primitive recursive and dominate the index is recursive. -/
lemma oma_isRecursive_of_finite_union_range {L : Language} [Encodable (Σ n, L.Functions n)]
    [Encodable (Σ n, L.Relations n)] (F : Set L.Sentence) (hF : F.Finite)
    (ax : ℕ → L.Sentence) (hax : Primrec fun k => Encodable.encode (ax k))
    (hb : ∀ k, k ≤ Encodable.encode (ax k)) :
    (F ∪ Set.range ax : L.Theory).IsRecursive := by
  obtain ⟨cl, hcl⟩ : ∃ l : List ℕ, ∀ m, (∃ a ∈ l, a = m) ↔ ∃ φ ∈ F, Encodable.encode φ = m :=
    ⟨(hF.toFinset.toList).map Encodable.encode, fun m => by simp⟩
  have hmem : PrimrecPred fun m : ℕ => ∃ a ∈ cl, a = m :=
    PrimrecRel.comp (PrimrecRel.exists_mem_list (R := fun a b : ℕ => a = b) Primrec.eq)
      (Primrec.const cl) Primrec.id
  have hE : PrimrecPred fun m : ℕ => ∃ k < m + 1, Encodable.encode (ax k) = m := by
    have h1 : PrimrecRel fun k m : ℕ => Encodable.encode (ax k) = m :=
      Primrec.eq.comp (hax.comp Primrec.fst) Primrec.snd
    exact PrimrecRel.comp (PrimrecRel.exists_lt h1) Primrec.succ Primrec.id
  obtain ⟨_, hP⟩ := hmem.or hE
  refine ⟨_, hP.to_comp, ?_⟩
  intro φ
  simp only [decide_eq_true_iff, hcl, Set.mem_union, Set.mem_range]
  constructor
  · rintro (⟨ψ, hψ, hψφ⟩ | ⟨k, hk, hkφ⟩)
    · have : ψ = φ := Encodable.encode_injective hψφ
      exact Or.inl (this ▸ hψ)
    · have : ax k = φ := Encodable.encode_injective hkφ
      exact Or.inr ⟨k, this⟩
  · rintro (hφ | ⟨k, rfl⟩)
    · exact Or.inl ⟨φ, hφ, rfl⟩
    · exact Or.inr ⟨k, Nat.lt_succ_of_le (hb k), rfl⟩

lemma oma_encode_list_nat {β : Type*} [Encodable β] (l : List β) :
    encode l = encode (l.map encode) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [Encodable.encode_list_cons, ih]

lemma oma_term_codes (m : ℕ) (l : List (Fin m)) :
    (Term.listEncode ((LHom.sumInl : Language.ring →ᴸ Language.ring.sum Language.order).onTerm
      (l.foldr (fun i t => Term.var (Sum.inr i.castSucc) +
        Term.var (Sum.inr (Fin.last m)) * t) 1) :
        (Language.ring.sum Language.order).Term (Empty ⊕ Fin (m + 1)))).map encode =
      l.flatMap (fun i => [1, 2 * (2 * i.val + 1), 5, 2 * (2 * m + 1)]) ++ [17] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons, List.flatMap_cons, List.cons_append, List.nil_append]
    rw [← ih]
    simp [Term.listEncode, FirstOrder.Ring.add_def, FirstOrder.Ring.mul_def, Functions.apply₂, List.finRange_succ]
    exact ⟨rfl, rfl, rfl, rfl⟩

lemma oma_term_encode {L : Language} {α : Type*} [Encodable α] [Encodable (Σ n, L.Functions n)]
    (t : L.Term α) : encode t = encode (t.listEncode.map encode) := by
  rw [← oma_encode_list_nat]
  rfl

lemma oma_alls_listEncode {L : Language} {α : Type*} :
    ∀ (n : ℕ) (ψ : L.BoundedFormula α n),
      (BoundedFormula.alls ψ).listEncode =
        List.replicate n (Sum.inr (Sum.inr 1)) ++ ψ.listEncode
  | 0, ψ => rfl
  | n + 1, ψ => by
    rw [BoundedFormula.alls, oma_alls_listEncode n ψ.all, List.replicate_succ']
    simp [BoundedFormula.listEncode]

lemma oma_sentence_encode {L : Language} [Encodable (Σ n, L.Functions n)]
    [Encodable (Σ n, L.Relations n)] (φ : L.Sentence) :
    encode φ = encode (φ.listEncode.map encode) := by
  rw [← oma_encode_list_nat]
  rfl

lemma oma_rcf_code (k : ℕ) : let r := fun (n : ℕ) (t : Language.ring.Term (Empty ⊕ Fin n)) =>
    (LHom.sumInl : Language.ring →ᴸ Language.ring.sum Language.order).onTerm t
  encode (BoundedFormula.alls (∃' ((r (2 * k + 1 + 1)
      ((List.finRange (2 * k + 1)).foldr (fun i t => Term.var (Sum.inr i.castSucc) +
        Term.var (Sum.inr (Fin.last (2 * k + 1))) * t) 1)) =' (r (2 * k + 1 + 1) 0))) :
      (Language.ring.sum Language.order).Sentence) =
    encode (List.replicate (2 * k + 1) 7 ++ [3, 7, 3,
      2 * Nat.pair (2 * k + 2) (encode ((List.range (2 * k + 1)).flatMap
        (fun i => [1, 2 * (2 * i + 1), 5, 2 * (2 * (2 * k + 1) + 1)]) ++ [17])),
      2 * Nat.pair (2 * k + 2) (encode [13]),
      2 * (2 * (2 * k + 4) + 1) + 1, 2 * (2 * (2 * k + 3) + 1) + 1]) := by
  dsimp only
  rw [oma_sentence_encode, oma_alls_listEncode]
  simp only [Term.bdEqual, BoundedFormula.listEncode]
  congr 1
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, encode_inl, encode_inr, encode_sigma_val, encode_nat, oma_term_encode,
    oma_term_codes, ← List.map_coe_finRange_eq_range, List.flatMap_map]
  rfl

lemma oma_lin (a b : ℕ) : Primrec fun k : ℕ => a * k + b :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const a) Primrec.id) (Primrec.const b)

lemma oma_codes_primrec : Primrec fun k : ℕ =>
    encode (List.replicate (2 * k + 1) 7 ++ [3, 7, 3,
      2 * Nat.pair (2 * k + 2) (encode ((List.range (2 * k + 1)).flatMap
        (fun i => [1, 2 * (2 * i + 1), 5, 2 * (2 * (2 * k + 1) + 1)]) ++ [17])),
      2 * Nat.pair (2 * k + 2) (encode [13]),
      2 * (2 * (2 * k + 4) + 1) + 1, 2 * (2 * (2 * k + 3) + 1) + 1]) := by
  have hrep : Primrec fun k : ℕ => List.replicate (2 * k + 1) 7 :=
    (Primrec.list_map (Primrec.list_range.comp (oma_lin 2 1))
      ((Primrec.const 7).comp Primrec.fst).to₂).of_eq fun k => by simp
  have hg : Primrec₂ fun (k i : ℕ) => [1, 2 * (2 * i + 1), 5, 2 * (2 * (2 * k + 1) + 1)] :=
    (Primrec.list_cons.comp (Primrec.const 1) (Primrec.list_cons.comp
      ((oma_lin 2 0).comp ((oma_lin 2 1).comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.const 5) (Primrec.list_cons.comp
        ((oma_lin 2 0).comp ((oma_lin 2 1).comp ((oma_lin 2 1).comp Primrec.fst)))
        (Primrec.const []))))).of_eq fun p => by simp
  have hT : Primrec fun k : ℕ => 2 * Nat.pair (2 * k + 2) (encode ((List.range (2 * k + 1)).flatMap
        (fun i => [1, 2 * (2 * i + 1), 5, 2 * (2 * (2 * k + 1) + 1)]) ++ [17])) :=
    Primrec.nat_double.comp (Primrec₂.natPair.comp (oma_lin 2 2) (Primrec.encode.comp
      (Primrec.list_append.comp (Primrec.list_flatMap (Primrec.list_range.comp (oma_lin 2 1)) hg)
        (Primrec.const _))))
  have hZ : Primrec fun k : ℕ => 2 * Nat.pair (2 * k + 2) (encode [13]) :=
    Primrec.nat_double.comp (Primrec₂.natPair.comp (oma_lin 2 2) (Primrec.const _))
  have hF : ∀ c, Primrec fun k : ℕ => 2 * (2 * (2 * k + c) + 1) + 1 := fun c =>
    (oma_lin 2 1).comp ((oma_lin 2 1).comp (oma_lin 2 c))
  refine Primrec.encode.comp (Primrec.list_append.comp hrep ?_)
  refine Primrec.list_cons.comp (Primrec.const 3) ?_
  refine Primrec.list_cons.comp (Primrec.const 7) ?_
  refine Primrec.list_cons.comp (Primrec.const 3) ?_
  refine Primrec.list_cons.comp hT ?_
  refine Primrec.list_cons.comp hZ ?_
  refine Primrec.list_cons.comp (hF 4) ?_
  exact Primrec.list_cons.comp (hF 3) (Primrec.const [])

lemma oma_length_le_encode (l : List ℕ) : l.length ≤ encode l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [encode_list_cons, List.length_cons]
    exact Nat.succ_le_succ (ih.trans (Nat.right_le_pair _ _))

/-- The Goedel codes of the odd-degree root axioms are primitive recursive in the index. -/
lemma oma_rcf_family_primrec : let r := fun (n : ℕ) (t : Language.ring.Term (Empty ⊕ Fin n)) =>
    (LHom.sumInl : Language.ring →ᴸ Language.ring.sum Language.order).onTerm t
  Primrec fun k : ℕ => Encodable.encode (BoundedFormula.alls (∃' ((r (2 * k + 1 + 1)
      ((List.finRange (2 * k + 1)).foldr (fun i t => Term.var (Sum.inr i.castSucc) +
        Term.var (Sum.inr (Fin.last (2 * k + 1))) * t) 1)) =' (r (2 * k + 1 + 1) 0))) :
      (Language.ring.sum Language.order).Sentence) := by
  exact oma_codes_primrec.of_eq fun k => (oma_rcf_code k).symm

/-- The Goedel code of the odd-degree root axiom of index `k` is at least `k`. -/
lemma oma_rcf_family_ge : let r := fun (n : ℕ) (t : Language.ring.Term (Empty ⊕ Fin n)) =>
    (LHom.sumInl : Language.ring →ᴸ Language.ring.sum Language.order).onTerm t
  ∀ k : ℕ, k ≤ Encodable.encode (BoundedFormula.alls (∃' ((r (2 * k + 1 + 1)
      ((List.finRange (2 * k + 1)).foldr (fun i t => Term.var (Sum.inr i.castSucc) +
        Term.var (Sum.inr (Fin.last (2 * k + 1))) * t) 1)) =' (r (2 * k + 1 + 1) 0))) :
      (Language.ring.sum Language.order).Sentence) := by
  intro r k
  rw [oma_rcf_code]
  refine le_trans ?_ (oma_length_le_encode _)
  simp
  omega

theorem OMA.solution : OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_real_orderedField_R1.H3 := by
  unfold OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_real_orderedField_R1.H3
  dsimp only
  refine oma_isRecursive_of_finite_union_range _ ?_ _ oma_rcf_family_primrec oma_rcf_family_ge
  have : Finite Field.FieldAxiom :=
    Finite.of_injective (β := Fin 9) (fun a : Field.FieldAxiom =>
      match a with
      | .addAssoc => 0 | .zeroAdd => 1 | .negAddCancel => 2 | .mulAssoc => 3 | .mulComm => 4
      | .oneMul => 5 | .existsInv => 6 | .leftDistrib => 7 | .existsPairNE => 8)
      (by intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide))
  refine ((Set.Finite.image _ (Set.finite_range _)).union ?_).union (Set.toFinite _)
  unfold FirstOrder.Language.linearOrderTheory FirstOrder.Language.partialOrderTheory
    FirstOrder.Language.preorderTheory
  exact Set.toFinite _
