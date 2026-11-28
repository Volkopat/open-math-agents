import OMAReductions.R_Erdos118_erdos_118_R1

/-!
# Larson's partition relation at ω^(ω²)

The negative relation is witnessed by an alternating pattern on marked finite words.
The positive results include all smaller red targets and a reduction of the full red
target to graphs with edges between different outer lengths.

## Model and change of carrier
-/

namespace OMA.E118

open Ordinal
open scoped Ordinal

/-- An ordered tuple has a most significant coordinate, followed by a shorter tuple. -/
def Tuple (A : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => A ×ₗ Tuple A n

instance tupleOrder (A : Type) [LinearOrder A] (n : ℕ) : LinearOrder (Tuple A n) := by
  induction n with
  | zero => exact inferInstanceAs (LinearOrder Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (LinearOrder (A ×ₗ Tuple A n))

instance tupleWF (A : Type) [LinearOrder A] [WellFoundedLT A] (n : ℕ) :
    WellFoundedLT (Tuple A n) := by
  induction n with
  | zero => exact inferInstanceAs (WellFoundedLT Unit)
  | succ n ih =>
    let := ih
    exact inferInstanceAs (WellFoundedLT (A ×ₗ Tuple A n))

theorem type_tuple (A : Type) [LinearOrder A] [WellFoundedLT A] (n : ℕ) :
    typeLT (Tuple A n) = (typeLT A) ^ n := by
  induction n with
  | zero => exact (type_eq_one_of_unique (α := Unit) (· < ·)).trans (pow_zero _).symm
  | succ n ih =>
    change type (Prod.Lex (· < · : A → A → Prop)
      (· < · : Tuple A n → Tuple A n → Prop)) = _
    rw [type_prod_lex, pow_succ]
    exact congrArg (· * (typeLT A)) ih

/-- Finite words, ordered by length and lexicographically within a length. -/
abbrev Words (A : Type) := Σₗ n, Tuple A n

/-- Embed the block of length n above the cut a^n, where a is the alphabet's order type. -/
private noncomputable def wordCode {A : Type} [LinearOrder A] [WellFoundedLT A]
    (w : Words A) : Ordinal.{0} :=
  (typeLT A) ^ w.1 + typein (α := Tuple A w.1) (· < ·) w.2

private theorem wordCode_lt {A : Type} [LinearOrder A] [WellFoundedLT A]
    (h : 1 < typeLT A) (w : Words A) {m : ℕ} (hm : w.1 < m) :
    wordCode w < (typeLT A) ^ m := by
  have ht := (typein_lt_type (α := Tuple A w.1) (· < ·) w.2).trans_eq (type_tuple A w.1)
  simpa only [wordCode, opow_natCast, mul_one] using
    (opow_mul_add_lt_opow (u := (w.1 : Ordinal)) (x := (m : Ordinal)) h
      (by simpa only [opow_natCast] using ht) (by exact_mod_cast hm))

private theorem wordCode_strictMono {A : Type} [LinearOrder A] [WellFoundedLT A]
    (h : 1 < typeLT A) : StrictMono (wordCode (A := A)) := by
  intro x y hxy
  rcases Sigma.Lex.lt_def.mp hxy with hlen | ⟨heq, htail⟩
  · exact (wordCode_lt h x hlen).trans_le le_self_add
  · obtain ⟨n, v⟩ := x
    obtain ⟨m, w⟩ := y
    change n = m at heq
    subst m
    exact add_lt_add_right ((typein_lt_typein _).2 htail) _

instance wordsWF (A : Type) [LinearOrder A] [WellFoundedLT A] : WellFoundedLT (Words A) :=
  ⟨⟨by
    rintro ⟨n, w⟩
    induction n using Nat.strong_induction_on with
    | h n ih =>
      induction w using (wellFounded_lt (α := Tuple A n)).induction with
      | h w iw =>
        constructor
        rintro ⟨m, v⟩ h
        rcases h with ⟨_, _, hlen⟩ | ⟨_, _, ht⟩
        · exact ih _ hlen _
        · exact iw _ ht⟩⟩

/-- Each fixed length has type a^n, and all lengths together have type a^ω. -/
theorem type_words (A : Type) [LinearOrder A] [WellFoundedLT A] (h : 1 < typeLT A) :
    typeLT (Words A) = (typeLT A) ^ ω := by
  apply le_antisymm
  · let f (w : Words A) : ((typeLT A) ^ ω).ToType :=
      ToType.mk ⟨wordCode w, (wordCode_lt h w (Nat.lt_succ_self _)).trans_le
        (by rw [← iSup_pow_natCast h.pos]; exact Ordinal.le_iSup _ (w.1 + 1))⟩
    have hmono : StrictMono f := fun x y hxy =>
      ToType.mk.strictMono (show wordCode x < wordCode y from wordCode_strictMono h hxy)
    simpa only [type_toType] using (RelEmbedding.ofMonotone f hmono).ordinal_type_le
  · rw [← iSup_pow_natCast h.pos]
    apply Ordinal.iSup_le
    intro n
    let f (w : Tuple A n) : Words A := ⟨n, w⟩
    have hf : StrictMono f := fun _ _ hlt => Sigma.Lex.right _ _ hlt
    simpa only [type_tuple] using (RelEmbedding.ofMonotone f hf).ordinal_type_le

/-- Read a tuple from its most significant coordinate to its least significant coordinate. -/
def tupleList {A : Type} : {n : ℕ} → Tuple A n → List A
  | 0, _ => []
  | _ + 1, t => (ofLex t).1 :: tupleList (ofLex t).2

/-- A word of words of natural numbers. Both levels use the length-first order. -/
abbrev Model := Words (Words ℕ)

noncomputable abbrev target : Ordinal.{0} := ω ^ ω ^ (2 : Ordinal.{0})

theorem type_model : typeLT Model = target := by
  have inner : typeLT (Words ℕ) = ω ^ (ω : Ordinal.{0}) := by
    rw [type_words, type_nat_lt]
    simpa only [type_nat_lt] using (one_lt_omega0 : (1 : Ordinal.{0}) < ω)
  have h : 1 < typeLT (Words ℕ) := by
    rw [inner]
    exact one_lt_opow.mpr ⟨one_lt_omega0, omega0_ne_zero⟩
  rw [type_words _ h, inner, ← opow_mul]
  change ω ^ (ω * ω) = ω ^ ω ^ (2 : Ordinal.{0})
  congr 1
  exact (pow_two _).symm.trans (opow_natCast ω 2).symm

/-- A word is sent to its rank in the length-first order, viewed as a point of the target. -/
noncomputable def modelIso : Model ≃o target.ToType :=
  (OrderIso.ofRelIsoLT (enum (α := Model) (· < ·))).symm |>.trans
    ((OrderIso.setCongr _ _ (by rw [show type (α := Model) (· < ·) = target from type_model])).trans
      ToType.mk)


universe u

/-- A self-embedding selects a copy of the whole order on which the graph has no edges. -/
def IndependentCopy {A : Type*} [LinearOrder A] (G : SimpleGraph A) : Prop :=
  ∃ f : A ↪o A, ∀ x y, ¬ G.Adj (f x) (f y)

/-- The one-graph formulation of the partition relation with a finite blue target. -/
def PartitionProperty (A : Type*) [LinearOrder A] (n : ℕ) : Prop :=
  ∀ G : SimpleGraph A, G.CliqueFree n → IndependentCopy G

theorem exists_clique_type_nat_iff {A : Type*} [LinearOrder A] [WellFoundedLT A]
    (G : SimpleGraph A) (n : ℕ) :
    (∃ s, G.IsClique s ∧ typeLT s = n) ↔ ¬ G.CliqueFree n := by
  classical
  constructor
  · rintro ⟨s, hs, ht⟩
    have hc : Cardinal.mk s = n := by rw [← card_type (· < · : s → s → Prop), ht]; simp
    obtain ⟨inst, hn⟩ := Cardinal.mk_eq_nat_iff_fintype.mp hc
    let := inst
    exact fun hf => hf s.toFinset ⟨by simpa using hs, s.toFinset_card.trans hn⟩
  · intro hf
    obtain ⟨t, h⟩ := Classical.not_forall.mp hf
    have ht := Classical.not_not.mp h
    exact ⟨(t : Set A), ht.1, by simp [type_fintype, ht.2]⟩

theorem independentCopy_iff {A : Type*} [LinearOrder A] [WellFoundedLT A] (G : SimpleGraph A) :
    IndependentCopy G ↔ ∃ s, G.IsIndepSet s ∧ typeLT s = typeLT A := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨Set.range f, ?_, f.orderIso.symm.toRelIsoLT.ordinalType_congr⟩
    apply G.isIndepSet_iff.mpr
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
    exact hf x y
  · rintro ⟨s, hs, ht⟩
    obtain ⟨iso⟩ := type_eq.mp ht
    let e : A ≃o s := OrderIso.ofRelIsoLT iso.symm
    refine ⟨e.toOrderEmbedding.trans (OrderEmbedding.subtype _), ?_⟩
    intro x y
    by_cases h : (e x).val = (e y).val
    · change ¬ G.Adj (e x).val (e y).val
      rw [h]
      exact G.loopless.irrefl _
    · exact (G.isIndepSet_iff.mp hs) (e x).2 (e y).2 h

theorem ramsey_iff_partitionProperty (a : Ordinal) (n : ℕ) :
    Erdos118.OrdinalRamsey a a n ↔ PartitionProperty a.ToType n := by
  constructor
  · intro h G hf
    obtain hr | hb := h Gᶜ G isCompl_compl.symm
    · apply (independentCopy_iff G).mpr
      simpa only [type_toType, SimpleGraph.isClique_compl] using hr
    · exact False.elim ((exists_clique_type_nat_iff G n).mp hb hf)
  · intro h red blue hc
    by_cases hf : blue.CliqueFree n
    · left
      rw [hc.eq_compl]
      simpa only [type_toType, SimpleGraph.isClique_compl] using
        (independentCopy_iff blue).mp (h blue hf)
    · exact Or.inr ((exists_clique_type_nat_iff blue n).mpr hf)

private theorem partitionProperty_map {A B : Type*} [LinearOrder A] [LinearOrder B]
    (e : A ≃o B) {n : ℕ} (h : PartitionProperty A n) : PartitionProperty B n := by
  intro G hG
  let H := G.comap e
  have hH : H.CliqueFree n := hG.comap (SimpleGraph.Iso.comap e.toEquiv G).isContained
  obtain ⟨f, hf⟩ := h H hH
  exact ⟨(e.symm.toOrderEmbedding.trans f).trans e.toOrderEmbedding,
    fun x y => hf (e.symm x) (e.symm y)⟩

theorem partitionProperty_congr {A B : Type*} [LinearOrder A] [LinearOrder B]
    (e : A ≃o B) (n : ℕ) : PartitionProperty A n ↔ PartitionProperty B n :=
  ⟨partitionProperty_map e, partitionProperty_map e.symm⟩


/-- Lifting a countable sequence of ordinals commutes with taking its supremum. -/
private theorem lift_nat_iSup (f : ℕ → Ordinal.{0}) :
    lift.{u} (⨆ n, f n) = ⨆ n, lift.{u} (f n) := by
  apply le_antisymm
  · by_contra! h
    obtain ⟨b, hb, he⟩ := lt_lift_iff.mp h
    apply hb.not_ge
    apply Ordinal.iSup_le
    intro n
    exact lift_le.mp (he ▸ Ordinal.le_iSup (fun n => lift.{u} (f n)) n)
  · exact Ordinal.iSup_le fun n => lift_le.mpr (Ordinal.le_iSup f n)

private theorem lift_pow_omega (a : Ordinal.{0}) (ha : 0 < a) :
    lift.{u} (a ^ ω) = lift.{u} a ^ ω := by
  have h : 0 < lift.{u} a := by simpa using (lift_lt.mpr ha : lift.{u} 0 < lift.{u} a)
  rw [← iSup_pow_natCast ha, ← iSup_pow_natCast h, lift_nat_iSup]
  congr 1
  funext n
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ, lift_mul, ih]

private theorem opow_ordinal_two (a : Ordinal.{u}) : a ^ (2 : Ordinal.{u}) = a * a :=
  (opow_natCast a 2).trans (pow_two a)

private theorem lift_target :
    lift.{u} target = (ω ^ ω ^ (2 : Ordinal.{u})) := by
  simp only [target, opow_ordinal_two, opow_mul, lift_pow_omega _ (opow_pos _ omega0_pos),
    lift_pow_omega _ omega0_pos, lift_omega0]

/-- The concrete model also represents the target at any universe level. -/
noncomputable def modelIsoAt :
    Model ≃o (ω ^ ω ^ (2 : Ordinal.{u})).ToType :=
  OrderIso.ofRelIsoLT (Ordinal.lift_type_eq.{0,u,0}.mp (by
    rw [show type (α := Model) (· < ·) = target from type_model, type_toType,
      lift_uzero, lift_target])).some

theorem target_ramsey_iff (n : ℕ) :
    Erdos118.OrdinalRamsey (ω ^ ω ^ (2 : Ordinal.{u})) (ω ^ ω ^ (2 : Ordinal.{u})) n ↔
      PartitionProperty Model n :=
  (ramsey_iff_partitionProperty _ n).trans (partitionProperty_congr modelIsoAt n).symm

/- ## Finite colorings of the model -/

/-- Every finite coloring of the vertices contains a monochromatic copy of the whole order. -/
def VertexIndivisible (A : Type) [LinearOrder A] : Prop :=
  ∀ {C : Type} [Finite C] (color : A → C), ∃ e : A ↪o A, ∃ c : C, ∀ a, color (e a) = c

theorem vertexIndivisible_nat : VertexIndivisible ℕ := by
  intro C _ color
  obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber color
  let e := Nat.Subtype.orderIsoOfNat (color ⁻¹' {c})
  exact ⟨e.toOrderEmbedding.trans (OrderEmbedding.subtype _), c, fun n => (e n).2⟩

theorem vertexIndivisible_unit : VertexIndivisible Unit := by
  intro C _ color
  exact ⟨(OrderIso.refl _).toOrderEmbedding, color (), fun _ => rfl⟩

theorem VertexIndivisible.prod {A B : Type} [LinearOrder A] [LinearOrder B]
    (hA : VertexIndivisible A) (hB : VertexIndivisible B) :
    VertexIndivisible (A ×ₗ B) := by
  classical
  intro C _ color
  choose f c hf using fun a : A => hB (fun b : B => color (toLex (a, b)))
  obtain ⟨e, k, he⟩ := hA c
  let g (p : A ×ₗ B) : A ×ₗ B := toLex (e (ofLex p).1, f (e (ofLex p).1) (ofLex p).2)
  have hg : StrictMono g := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    rcases Prod.Lex.lt_iff.mp h with h | ⟨h, hb⟩
    · exact Prod.Lex.left _ _ (e.strictMono h)
    · change a = a' at h
      subst a'
      exact Prod.Lex.right _ ((f (e a)).strictMono hb)
  exact ⟨OrderEmbedding.ofStrictMono g hg, k, fun ⟨a, b⟩ => (hf (e a) b).trans (he a)⟩

theorem VertexIndivisible.tuple {A : Type} [LinearOrder A] (hA : VertexIndivisible A)
    (n : ℕ) : VertexIndivisible (Tuple A n) := by
  induction n with
  | zero => exact vertexIndivisible_unit
  | succ n ih => exact hA.prod ih

/-- Embed every length in a later length using an embedding of the corresponding tuples. -/
private def liftWordBlocks {A : Type} [LinearOrder A] (k : ℕ → ℕ) (hk : StrictMono k)
    (f : ∀ n, Tuple A n ↪o Tuple A (k n)) : Words A ↪o Words A :=
  OrderEmbedding.ofStrictMono (fun w => ⟨k w.1, f w.1 w.2⟩) (by
    intro x y h
    obtain ⟨n, x⟩ := x
    obtain ⟨m, y⟩ := y
    rcases Sigma.Lex.lt_def.mp h with hnm | ⟨hnm, hxy⟩
    · exact Sigma.Lex.left _ _ (hk hnm)
    · change n = m at hnm
      subst m
      exact Sigma.Lex.right _ _ ((f n).strictMono hxy))

private noncomputable def embedOfTypeLE {A B : Type} [LinearOrder A] [LinearOrder B]
    [WellFoundedLT A] [WellFoundedLT B] (h : typeLT A ≤ typeLT B) : A ↪o B :=
  (Ordinal.type_le_iff'.mp h).some.orderEmbeddingOfLTEmbedding

/-- Finite-color vertex indivisibility persists under length-first finite words. The infinite
pigeonhole principle selects one color on unboundedly many lengths. -/
theorem VertexIndivisible.words {A : Type} [LinearOrder A] [WellFoundedLT A]
    (hA : VertexIndivisible A) (ha : 1 ≤ typeLT A) : VertexIndivisible (Words A) := by
  classical
  intro C _ color
  choose f c hf using fun n : ℕ => hA.tuple n (fun x => color ⟨n, x⟩)
  obtain ⟨k, d, hk⟩ := vertexIndivisible_nat c
  have hle (n : ℕ) : typeLT (Tuple A n) ≤ typeLT (Tuple A (k n)) := by
    simpa only [type_tuple, id_eq] using pow_le_pow_right' ha (k.strictMono.id_le n)
  let g (n : ℕ) := (embedOfTypeLE (hle n)).trans (f (k n))
  exact ⟨liftWordBlocks k k.strictMono g, d,
    fun ⟨n, x⟩ => (hf (k n) (embedOfTypeLE (hle n) x)).trans (hk n)⟩

instance tupleCountable (A : Type) [Countable A] (n : ℕ) : Countable (Tuple A n) := by
  induction n with
  | zero => exact inferInstanceAs (Countable Unit)
  | succ n ih => exact inferInstanceAs (Countable (A × Tuple A n))

instance tupleNonempty (A : Type) [Nonempty A] (n : ℕ) : Nonempty (Tuple A n) := by
  induction n with
  | zero => exact ⟨()⟩
  | succ n ih => exact ⟨toLex (Classical.arbitrary A, ih.some)⟩

private theorem innerWordsIndivisible : VertexIndivisible (Words ℕ) :=
  vertexIndivisible_nat.words (by rw [type_nat_lt]; exact one_lt_omega0.le)

private theorem innerWordsType_gt_one : 1 < typeLT (Words ℕ) := by
  rw [type_words, type_nat_lt]
  · exact one_lt_opow.mpr ⟨one_lt_omega0, omega0_ne_zero⟩
  · simpa only [type_nat_lt] using (one_lt_omega0 : (1 : Ordinal.{0}) < ω)

/-- Every finite vertex coloring of the target model contains a full monochromatic copy. -/
theorem model_vertexIndivisible : VertexIndivisible Model :=
  innerWordsIndivisible.words innerWordsType_gt_one.le

/- ## The negative relation -/

/-- Marked runs of the pattern, indexed starting at zero. -/
def markedRun (i : Fin 11) : Bool := [0, 1, 4, 6, 9, 10].contains i.val

/-- A cut is the last allowed coordinate of the interval on its left. -/
def inRun (cut : Fin 10 → ℕ) (i : Fin 11) (z : ℕ) : Prop :=
  (∀ j : Fin 10, j.val + 1 = i.val → cut j < z) ∧
  (∀ j : Fin 10, j.val = i.val → z ≤ cut j)

/-- The two vertices occupy alternate runs, and precisely the specified runs contain a mark. -/
def MarkedPattern (X A Y B : Set ℕ) : Prop :=
  ∃ cut : Fin 10 → ℕ,
    (∀ i : Fin 11, ∃ z, inRun cut i z ∧
      (if i.val % 2 = 0 then z ∈ X else z ∈ Y) ∧
      (markedRun i = true → if i.val % 2 = 0 then z ∈ A else z ∈ B)) ∧
    (∀ z ∈ X, ∃ i : Fin 11, i.val % 2 = 0 ∧ inRun cut i z ∧ (z ∈ A → markedRun i = true)) ∧
    (∀ z ∈ Y, ∃ i : Fin 11, i.val % 2 = 1 ∧ inRun cut i z ∧ (z ∈ B → markedRun i = true))

/-- The graph of ordered occurrences of the pattern and their reversals. -/
def markedPatternGraph {V : Type*} (first : V → ℕ) (coord box : V → Set ℕ) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y =>
    first x < first y ∧ MarkedPattern (coord x) (box x) (coord y) (box y)

/-- A digit in the serialization. The Boolean records a block boundary. -/
abbrev Digit := ℕ × Bool
abbrev Digits := List Digit

def plain (xs : List ℕ) : Digits := xs.map fun a => (a, false)

def wordRaw (w : Words ℕ) : Digits := (w.1, true) :: plain (tupleList w.2)

def tupleRaw {n : ℕ} (t : Tuple (Words ℕ) n) : Digits := (tupleList t).flatMap wordRaw

def modelRaw (w : Model) : Digits :=
  (w.1, true) :: tupleRaw w.2 ++ [(0, true)]

/-- Interpret the digits as positive gaps between successive coordinates. -/
def positions (start : ℕ) : Digits → Digits
  | [] => []
  | (a, b) :: xs =>
    let j := start + a + 1
    (j, b) :: positions j xs

def modelCoords (w : Model) : Set ℕ :=
  {i | ∃ b, (i,b) ∈ positions 0 (modelRaw w)}

def modelBoxes (w : Model) : Set ℕ :=
  {i | (i,true) ∈ positions 0 (modelRaw w)}

def hasBox (xs : Digits) := xs.any Prod.snd

/-- The explicit graph on the ordinal model. -/
def patternGraph : SimpleGraph Model := markedPatternGraph (fun w => w.1) modelCoords modelBoxes

/- ## Extracting alternating segments from a set of full order type -/

/-- The fiber at the first coordinate of a set in a lexicographic product. -/
def firstFiber {A B : Type} (S : Set (A ×ₗ B)) (a : A) : Set B :=
  {b | toLex (a, b) ∈ S}

/-- Bounding the order types of individual fibers and of their index set bounds the sum. -/
theorem type_le_of_firstFiber {A B : Type} [LinearOrder A] [LinearOrder B]
    [WellFoundedLT A] [WellFoundedLT B] (S : Set (A ×ₗ B)) (T : Set A)
    (β : Ordinal.{0}) (hT : ∀ p ∈ S, (ofLex p).1 ∈ T)
    (hβ : ∀ a ∈ T, typeLT (firstFiber S a) ≤ β) : typeLT S ≤ β * typeLT T := by
  let val (p : S) : firstFiber S (ofLex p.val).1 := ⟨(ofLex p.val).2, p.property⟩
  let f (p : S) : T ×ₗ β.ToType := toLex (⟨(ofLex p.val).1, hT _ p.property⟩,
    ToType.mk ⟨typein (α := firstFiber S (ofLex p.val).1) (· < ·) (val p), (typein_lt_type (α := firstFiber S (ofLex p.val).1) (· < ·) (val p)).trans_le (hβ _ (hT _ p.property))⟩)
  have hf : StrictMono f := by
    rintro ⟨⟨a,b⟩,hx⟩ ⟨⟨c,d⟩,hy⟩ h
    rcases Prod.Lex.lt_iff.mp h with h | ⟨e,h⟩
    · exact Prod.Lex.left _ _ h
    · change a = c at e
      subst c
      apply Prod.Lex.right
      apply ToType.mk.strictMono
      apply (typein_lt_typein _).mpr
      exact h
  have bound := (RelEmbedding.ofMonotone f hf).ordinal_type_le
  change typeLT S ≤ type (Prod.Lex (· < · : T → T → Prop) (· < · : β.ToType → β.ToType → Prop)) at bound
  simpa only [type_prod_lex, type_toType] using bound

private theorem typeSubsetLE {A : Type} [LinearOrder A] [WellFoundedLT A]
    {S T : Set A} (h : S ⊆ T) : typeLT S ≤ typeLT T := by
  have hm : StrictMono (Set.inclusion h) := fun _ _ hxy => hxy
  exact (RelEmbedding.ofMonotone _ hm).ordinal_type_le

/-- Some prefix has many next symbols, each supporting a large set of suffixes. -/
def HasWideLevel {A : Type} [LinearOrder A] [WellFoundedLT A] (κ θ : Ordinal.{0}) :
    (m : ℕ) → Set (Tuple A m) → Prop
  | 0, _ => False
  | m + 1, S => κ ≤ typeLT {a : A | θ ≤ typeLT (firstFiber S a)} ∨
      ∃ a : A, HasWideLevel κ θ m (firstFiber S a)

/-- Color a leaf by the first depth at which its suffix fiber has type below θ. -/
noncomputable def fiberDepth {A : Type} [LinearOrder A] [WellFoundedLT A] (θ : Ordinal.{0}) :
    (m : ℕ) → Set (Tuple A m) → Tuple A m → ℕ
  | 0, _, _ => 0
  | m + 1, S, p => if θ ≤ typeLT (firstFiber S (ofLex p).1) then
        fiberDepth θ m (firstFiber S (ofLex p).1) (ofLex p).2 + 1 else 0

private theorem fiberDepth_le {A : Type} [LinearOrder A] [WellFoundedLT A] (θ : Ordinal.{0})
    (m : ℕ) (S : Set (Tuple A m)) (p : Tuple A m) : fiberDepth θ m S p ≤ m := by
  induction m with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    simp only [fiberDepth]
    split
    · exact Nat.succ_le_succ (ih _ _)
    · exact Nat.zero_le _

/-- All leaves of a fixed fiber depth, with their inherited tuple order. -/
def depthSlice {A : Type} [LinearOrder A] [WellFoundedLT A] (θ : Ordinal.{0}) (m : ℕ)
    (S : Set (Tuple A m)) (k : ℕ) : Set (Tuple A m) := S ∩ {p | fiberDepth θ m S p = k}

/-- A thin tree's leaves of each fixed depth fit in a product of bounded type. -/
theorem type_depthSlice_le {A : Type} [LinearOrder A] [WellFoundedLT A]
    {κ θ : Ordinal.{0}} (hκ : 1 ≤ κ) (hθ : 1 ≤ θ * typeLT A)
    (m : ℕ) (S : Set (Tuple A m)) (hs : ¬ HasWideLevel κ θ m S) (k : ℕ) :
    typeLT (depthSlice θ m S k) ≤ (θ * typeLT A) * κ ^ m := by
  induction m generalizing k with
  | zero =>
    have hle : typeLT (depthSlice θ 0 S k) ≤ typeLT (Tuple A 0) :=
      (RelEmbedding.ofMonotone _ (Subtype.strictMono_coe _ : StrictMono
        (Subtype.val : depthSlice θ 0 S k → Tuple A 0))).ordinal_type_le
    simpa only [type_tuple, pow_zero, mul_one] using hle.trans (by simpa only [type_tuple, pow_zero] using hθ)
  | succ n ih =>
    let T : Set A := {a | θ ≤ typeLT (firstFiber S a)}
    have hT : typeLT T ≤ κ := (lt_of_not_ge (fun h => hs (Or.inl h))).le
    have hn (a : A) : ¬HasWideLevel κ θ n (firstFiber S a) := fun h => hs (Or.inr ⟨a, h⟩)
    cases k with
    | zero =>
      let R := depthSlice θ (n+1) S 0
      have hα : typeLT (Set.univ : Set A) ≤ typeLT A :=
        OrderIso.Set.univ.toRelIsoLT.toRelEmbedding.ordinal_type_le
      have hb : ∀ a : A, typeLT (firstFiber R a) ≤ θ := by
        intro a
        by_cases ha : a ∈ T
        · have hemp : firstFiber R a = ∅ := by
            ext b
            apply iff_false_intro
            intro hb
            have hz := hb.2
            change fiberDepth θ (n+1) S (toLex (a,b)) = 0 at hz
            simp only [fiberDepth] at hz
            split at hz
            · omega
            · contradiction
          have : IsEmpty (firstFiber R a) := ⟨fun x => by simpa only [hemp, Set.mem_empty_iff_false] using x.property⟩
          exact (type_eq_zero_of_empty _).le.trans zero_le
        · exact (typeSubsetLE (show firstFiber R a ⊆ firstFiber S a from fun _ hx => hx.1)).trans
            (lt_of_not_ge ha).le
      have h1 := type_le_of_firstFiber R Set.univ θ (fun _ _ => Set.mem_univ _) (fun a _ => hb a)
      calc
        _ ≤ θ * typeLT (Set.univ : Set A) := h1
        _ ≤ θ * typeLT A := by gcongr
        _ ≤ _ := le_mul_of_one_le_right' (one_le_pow_of_one_le' hκ _)
    | succ k =>
      let R := depthSlice θ (n+1) S (k+1)
      have hfirst : ∀ p ∈ R, (ofLex p).1 ∈ T := by
        rintro ⟨a,b⟩ hp
        by_contra h
        have hk := hp.2
        change fiberDepth θ (n+1) S (toLex (a,b)) = _ at hk
        simp only [fiberDepth] at hk
        split at hk
        · contradiction
        · omega
      have hb (a : A) (ha : a ∈ T) : typeLT (firstFiber R a) ≤ (θ * typeLT A) * κ ^ n := by
        apply le_trans (typeSubsetLE (T := depthSlice θ n (firstFiber S a) k) ?_) (ih _ (hn a) _)
        intro b hb
        refine ⟨hb.1, ?_⟩
        have hk := hb.2
        change fiberDepth θ (n+1) S (toLex (a,b)) = k+1 at hk
        simp only [fiberDepth] at hk
        split at hk
        · exact Nat.succ.inj hk
        · contradiction
      calc
        _ ≤ ((θ * typeLT A) * κ ^ n) * typeLT T := type_le_of_firstFiber R T _ hfirst hb
        _ ≤ ((θ * typeLT A) * κ ^ n) * κ := by gcongr
        _ = _ := by rw [pow_succ, mul_assoc]
/-- Indivisibility turns the finite depth partition into an extraction lemma. -/
theorem wideLevel_of_type {A U : Type} [LinearOrder A] [WellFoundedLT A] [LinearOrder U]
    [WellFoundedLT U] (hU : VertexIndivisible U) {κ θ : Ordinal.{0}} (hκ : 1 ≤ κ)
    (hθ : 1 ≤ θ * typeLT A) (m : ℕ) (S : Set (Tuple A m)) (hemb : typeLT U ≤ typeLT S)
    (hlarge : (θ * typeLT A) * κ ^ m < typeLT U) : HasWideLevel κ θ m S := by
  by_contra hs
  let e := (type_le_iff'.mp hemb).some.orderEmbeddingOfLTEmbedding
  let color (u : U) : Fin (m+1) :=
    ⟨fiberDepth θ m S (e u).val, Nat.lt_succ_of_le (fiberDepth_le θ m S _)⟩
  obtain ⟨f, k, hf⟩ := hU color
  let g (u : U) : depthSlice θ m S k.val :=
    ⟨(e (f u)).val, (e (f u)).property, congrArg Fin.val (hf u)⟩
  have hg : StrictMono g := fun _ _ hab => e.strictMono (f.strictMono hab)
  have ht := (RelEmbedding.ofMonotone g hg).ordinal_type_le
  exact hlarge.not_ge (ht.trans (type_depthSlice_le hκ hθ m S hs k))

/-- Within a large outer block, extract a level with ω^k many choices of the next word,
all of whose suffix fibers still have type at least (ω^ω)^t. -/
theorem wideLevel_words (m k t : ℕ) (S : Set (Tuple (Words ℕ) m))
    (h : ((ω ^ (ω : Ordinal.{0})) ^ (t + 2)) ≤ typeLT S) :
    HasWideLevel (ω ^ k) ((ω ^ (ω : Ordinal.{0})) ^ t) m S := by
  let a : Ordinal.{0} := ω ^ (ω : Ordinal.{0})
  have hw : typeLT (Words ℕ) = a := by
    rw [type_words, type_nat_lt]
    simpa only [type_nat_lt] using (one_lt_omega0 : (1 : Ordinal.{0}) < ω)
  have ha : 1 ≤ a := (one_lt_opow.mpr ⟨one_lt_omega0, omega0_ne_zero⟩).le
  let U := Tuple (Words ℕ) (t+2)
  have wU : typeLT U = a^(t+2) := (type_tuple _ _).trans (congrArg (· ^ (t+2)) hw)
  have hI : VertexIndivisible (Words ℕ) := vertexIndivisible_nat.words
    (by rw [type_nat_lt]; exact one_lt_omega0.le)
  apply wideLevel_of_type (hI.tuple (t+2)) (one_le_pow_of_one_le' one_lt_omega0.le k)
      (by rw [hw]; exact one_le_mul (one_le_pow_of_one_le' ha t) ha) m S (wU.trans_le h)
  rw [wU, hw, ← pow_mul]
  have he : ω ^ (k * m) < a := by
    simpa only [opow_natCast] using (opow_lt_opow_iff_right one_lt_omega0).mpr (natCast_lt_omega0 (k*m))
  exact (mul_lt_mul_of_pos_left he (mul_pos (pow_pos (zero_lt_one.trans_le ha) _) (zero_lt_one.trans_le ha))).trans_eq
    (by rw [show t+2 = (t+1)+1 from rfl, pow_succ, pow_succ])


/-- Restriction of a set of words to the block of words of one length. -/
def lengthFiber {A : Type} (S : Set (Words A)) (n : ℕ) : Set (Tuple A n) :=
  {t | (⟨n,t⟩ : Words A) ∈ S}

/-- A countable sequence of blocks of uniformly bounded type has type at most β · ω. -/
theorem type_le_of_lengthFiber {A : Type} [LinearOrder A] [WellFoundedLT A]
    (S : Set (Words A)) (β : Ordinal.{0}) (h : ∀ n, typeLT (lengthFiber S n) ≤ β) :
    typeLT S ≤ β * ω := by
  let rank (n : ℕ) (t : lengthFiber S n) : β.ToType :=
    ToType.mk ⟨typein (α := lengthFiber S n) (· < ·) t,
      (typein_lt_type (α := lengthFiber S n) (· < ·) t).trans_le (h n)⟩
  let f (x : S) : ℕ ×ₗ β.ToType := toLex (x.val.1, rank x.val.1 ⟨x.val.2, x.property⟩)
  have hf : StrictMono f := by
    rintro ⟨⟨n,v⟩, hv⟩ ⟨⟨m,w⟩, hw⟩ hlt
    rcases Sigma.Lex.lt_def.mp hlt with nm | ⟨nm, vw⟩
    · exact Prod.Lex.left _ _ nm
    · change n = m at nm
      subst m
      apply Prod.Lex.right
      apply ToType.mk.strictMono
      apply (typein_lt_typein _).mpr
      exact vw
  have bound := (RelEmbedding.ofMonotone f hf).ordinal_type_le
  change typeLT S ≤ type (Prod.Lex (· < · : ℕ → ℕ → Prop) (· < · : β.ToType → β.ToType → Prop)) at bound
  simpa only [type_prod_lex, type_nat_lt, type_toType] using bound

/-- A full copy has arbitrarily late outer lengths with fibers of any specified finite
power of ω^ω. Both the length cutoff and the desired fiber rank can be chosen in advance. -/
theorem exists_large_outer_length (S : Set Model) (hS : typeLT S = target) (e b : ℕ) :
    ∃ n > b, (ω ^ (ω : Ordinal.{0})) ^ e ≤ typeLT (lengthFiber S n) := by
  let a : Ordinal.{0} := ω ^ (ω : Ordinal.{0})
  have hw : typeLT (Words ℕ) = a := by
    rw [type_words, type_nat_lt]
    simpa only [type_nat_lt] using (one_lt_omega0 : (1 : Ordinal.{0}) < ω)
  have ha : 1 < a := one_lt_opow.mpr ⟨one_lt_omega0, omega0_ne_zero⟩
  let nmax := max b e
  by_contra! h
  have hlen (n : ℕ) : typeLT (lengthFiber S n) ≤ a^nmax := by
    by_cases hb : n ≤ b
    · have hle : typeLT (lengthFiber S n) ≤ typeLT (Tuple (Words ℕ) n) :=
        (RelEmbedding.ofMonotone _ (Subtype.strictMono_coe _ : StrictMono
          (Subtype.val : lengthFiber S n → Tuple (Words ℕ) n))).ordinal_type_le
      rw [type_tuple, hw] at hle
      exact hle.trans (pow_le_pow_right' ha.le (hb.trans (le_max_left _ _)))
    · exact (h n (lt_of_not_ge hb)).le.trans (pow_le_pow_right' ha.le (le_max_right _ _))
  have htop : a ^ (ω : Ordinal.{0}) = target := by
    rw [← type_model]
    change a ^ (ω : Ordinal.{0}) = typeLT (Words (Words ℕ))
    rw [type_words _ (hw.trans_gt ha), hw]
  have homega : ω ≤ a := by
    exact (opow_one (ω : Ordinal.{0})).ge.trans ((opow_le_opow_iff_right one_lt_omega0).mpr one_lt_omega0.le)
  have hsmall : a^nmax * ω < target := calc
    a^nmax * ω ≤ a^nmax * a := by gcongr
    _ = a^(nmax+1) := (pow_succ _ _).symm
    _ < a^(ω : Ordinal.{0}) := by
      simpa only [opow_natCast] using (opow_lt_opow_iff_right ha).mpr (natCast_lt_omega0 (nmax+1))
    _ = target := htop
  exact hsmall.not_ge (hS ▸ type_le_of_lengthFiber S (a^nmax) hlen)


/-- A finite game in which every next segment must begin above a freshly supplied cutoff. -/
def PlayDigits (L : Set (List ℕ)) : ℕ → Prop
  | 0 => [] ∈ L
  | d + 1 => ∀ B : ℕ, ∃ (q : ℕ) (more : List ℕ), B < q ∧
      PlayDigits {s | (q :: more) ++ s ∈ L} d

private def tupleLanguage {m : ℕ} (S : Set (Tuple ℕ m)) (p : List ℕ) : Set (List ℕ) :=
  {t | ∃ w ∈ S, tupleList w = p ++ t}

private theorem tupleLanguage_cons {m : ℕ} (S : Set (Tuple ℕ (m+1))) (a : ℕ) (p : List ℕ) :
    tupleLanguage S (a :: p) = tupleLanguage (firstFiber S a) p := by
  ext t
  constructor
  · rintro ⟨⟨b,w⟩, hw, he⟩
    change b :: tupleList w = a :: (p ++ t) at he
    obtain ⟨rfl, hlist⟩ := List.cons.inj he
    exact ⟨w, hw, hlist⟩
  · rintro ⟨w, hw, he⟩
    exact ⟨toLex (a,w), hw, congrArg (a :: ·) he⟩

private theorem natOmegaPow_strict {a b : ℕ} (h : a < b) :
    (ω : Ordinal.{0}) ^ a < ω ^ b := by
  simpa only [opow_natCast] using
    (opow_lt_opow_iff_right (a := (ω : Ordinal.{0})) one_lt_omega0).mpr
      (show (a : Ordinal.{0}) < (b : Ordinal.{0}) by exact_mod_cast h)

private theorem split_digit_fibers (r m : ℕ) (S : Set (Tuple ℕ (m+1)))
    (hS : ω^(r+2) ≤ typeLT S) :
    (∃ a : ℕ, ω^(r+2) ≤ typeLT (firstFiber S a)) ∨
      ∀ b : ℕ, ∃ a > b, ω^r ≤ typeLT (firstFiber S a) := by
  classical
  by_contra! hn
  obtain ⟨hchild, B, htail⟩ := hn
  let U := Tuple ℕ (r+2)
  have hu : typeLT U = ω^(r+2) := by rw [type_tuple, type_nat_lt]
  let e := (type_le_iff'.mp (hu.trans_le hS)).some.orderEmbeddingOfLTEmbedding
  let label (u : U) : Fin (B+2) := ⟨min (ofLex (e u).val).1 (B+1), by omega⟩
  obtain ⟨f, k, hf⟩ := vertexIndivisible_nat.tuple (r+2) label
  let R : Set (ℕ ×ₗ Tuple ℕ m) := {p | p ∈ S ∧ min (ofLex p).1 (B+1) = k.val}
  let g (u : U) : R := ⟨(e (f u)).val, (e (f u)).property, congrArg Fin.val (hf u)⟩
  have hg : StrictMono g := fun _ _ hab => e.strictMono (f.strictMono hab)
  have hr : ω^(r+2) ≤ typeLT R := hu ▸ (RelEmbedding.ofMonotone g hg).ordinal_type_le
  have hsub (a : ℕ) : typeLT (firstFiber R a) ≤ typeLT (firstFiber S a) := by
    apply typeSubsetLE
    exact fun _ h => h.1
  by_cases hlow : k.val < B+1
  · have ha : ∀ p ∈ R, (ofLex p).1 ∈ ({k.val} : Set ℕ) := by
      intro p hp
      have h := hp.2
      change (ofLex p).1 = k.val
      omega
    have hbound := type_le_of_firstFiber R {k.val} (typeLT (firstFiber S k.val)) ha (by
      rintro a rfl
      exact hsub _)
    have htype : typeLT ({k.val} : Set ℕ) = 1 := type_eq_one_of_unique _
    rw [htype, mul_one] at hbound
    exact (hchild _).not_ge (hr.trans hbound)
  · have hb (a : ℕ) : typeLT (firstFiber R a) ≤ ω^r := by
      by_cases ha : B < a
      · exact (hsub a).trans (htail a ha).le
      · have hemp : IsEmpty (firstFiber R a) := ⟨by
          rintro ⟨w, hw⟩
          have h := hw.2
          change min a (B+1) = k.val at h
          omega⟩
        exact (type_eq_zero_of_empty _).le.trans zero_le
    have hbound := type_le_of_firstFiber R Set.univ (ω^r) (fun _ _ => Set.mem_univ _) (fun a _ => hb a)
    have ht : typeLT (Set.univ : Set ℕ) = ω :=
      OrderIso.Set.univ.toRelIsoLT.ordinalType_congr.trans type_nat_lt
    rw [ht, ← pow_succ] at hbound
    exact (natOmegaPow_strict (show r+1 < r+2 by omega)).not_ge (hr.trans hbound)

private theorem tuple_digit_play (d m : ℕ) (S : Set (Tuple ℕ m)) (hS : ω^(2*d) ≤ typeLT S) :
    ∃ p : List ℕ, PlayDigits (tupleLanguage S p) d := by
  induction d generalizing m with
  | zero =>
    have hpos : 0 < typeLT S := zero_lt_one.trans_le (by simpa using hS)
    have hne : Nonempty S := by
      by_contra! hn
      exact hpos.ne' (type_eq_zero_iff_isEmpty.mpr hn)
    obtain ⟨w⟩ := hne
    exact ⟨tupleList w.val, w.val, w.property, (List.append_nil _).symm⟩
  | succ d ih =>
    induction m with
    | zero =>
      have hb : typeLT S ≤ (1 : Ordinal.{0}) := by
        rcases isEmpty_or_nonempty S with hem | hne
        · exact (type_eq_zero_of_empty _).le.trans zero_le
        · let _ : Subsingleton S := ⟨fun x y => Subtype.ext (Subsingleton.elim (α := Unit) x.val y.val)⟩
          exact (type_eq_one_of_unique _).le
      have hle := hS.trans hb
      have hlt := natOmegaPow_strict
        (show 0 < 2*(d+1) by omega)
      simp only [pow_zero] at hlt
      exact (hlt.not_ge hle).elim
    | succ m shrink =>
      rw [show 2*(d+1) = 2*d+2 by omega] at hS
      rcases split_digit_fibers (2*d) m S hS with ⟨a, ha⟩ | hmany
      · obtain ⟨p, hp⟩ := shrink (firstFiber S a) (by simpa only [Nat.mul_add, Nat.mul_one] using ha)
        exact ⟨a :: p, (tupleLanguage_cons S a p).symm ▸ hp⟩
      · refine ⟨[], fun B => ?_⟩
        obtain ⟨a, haB, ha⟩ := hmany B
        obtain ⟨p, hp⟩ := ih m (firstFiber S a) ha
        refine ⟨a, p, haB, ?_⟩
        have heq : {s | (a :: p) ++ s ∈ tupleLanguage S []} = tupleLanguage S (a :: p) := rfl
        rwa [heq, tupleLanguage_cons]

/-- A large subset of inner words permits a fixed initial prefix, followed by any prescribed
number of increasingly constrained digit segments from one word of the chosen length. -/
theorem inner_word_play (S : Set (Words ℕ)) (d : ℕ) (hS : ω^(2*d+2) ≤ typeLT S) :
    ∃ (n : ℕ) (p : List ℕ), PlayDigits
      {t | ∃ w : Tuple ℕ n, (⟨n,w⟩ : Words ℕ) ∈ S ∧ tupleList w = p ++ t} d := by
  have hex : ∃ n, ω^(2*d) ≤ typeLT (lengthFiber S n) := by
    by_contra! hn
    have hb := type_le_of_lengthFiber S (ω^(2*d)) (fun n => (hn n).le)
    rw [← pow_succ] at hb
    exact (natOmegaPow_strict (show 2*d+1 < 2*d+2 by omega)).not_ge (hS.trans hb)
  obtain ⟨n, hn⟩ := hex
  obtain ⟨p, hp⟩ := tuple_digit_play d n (lengthFiber S n) hn
  exact ⟨n, p, hp⟩

/-- Starting from a fixed prefix, the player chooses one segment for each Boolean. The
opponent sets an arbitrary lower bound for its first digit before each choice. -/
def Play : List Bool → (Digits → Prop) → Prop
  | [], K => K []
  | b :: bs, K => ∀ B : ℕ, ∃ q : Digit, ∃ more : Digits, B < q.1 ∧
      hasBox (q :: more) = b ∧ Play bs (fun tail => K ((q :: more) ++ tail))

private theorem play_mono {bs : List Bool} {K L : Digits → Prop}
    (h : Play bs K) (f : ∀ w, K w → L w) : Play bs L := by
  induction bs generalizing K L with
  | nil => exact f [] h
  | cons b bs ih =>
    intro B
    obtain ⟨q, more, hB, hcol, hr⟩ := h B
    exact ⟨q, more, hB, hcol, ih hr (fun t => f ((q :: more) ++ t))⟩

/-- First play a marked segment with a fixed prefix, then respond to all future cutoffs. -/
private def Prepared (bs : List Bool) (K : Digits → Prop) : Prop :=
  ∃ p : Digits, hasBox p = true ∧ Play bs (fun tail => K (p ++ tail))

private theorem prepared_prefix {bs : List Bool} {K : Digits → Prop} (z : Digits)
    (h : Prepared bs (fun t => K (z ++ t))) : Prepared bs K := by
  obtain ⟨p, hp, hg⟩ := h
  exact ⟨z ++ p, by simp [hasBox, List.any_append, show p.any Prod.snd = true from hp],
    play_mono hg (fun w hw => by simpa only [List.append_assoc] using hw)⟩

private theorem prepared_mono {bs : List Bool} {K L : Digits → Prop}
    (h : Prepared bs K) (f : ∀ w, K w → L w) : Prepared bs L := by
  obtain ⟨p, hp, hg⟩ := h
  exact ⟨p, hp, play_mono hg (fun t => f (p ++ t))⟩

/-- The last flexible digit of a level lets the next marked segment start beyond a new
cutoff, even when the following block headers have already been fixed. -/
private theorem play_plain_then_box (r : ℕ) {bs : List Bool} {L : Set (List ℕ)}
    {K : Digits → Prop} (h : PlayDigits L (r + 1))
    (next : ∀ z ∈ L, Prepared bs (fun tail => K (plain z ++ tail))) :
    Play (List.replicate r false ++ true :: bs) K := by
  induction r generalizing L K with
  | zero =>
    intro B
    obtain ⟨q, v, hB, hv⟩ := h B
    have hm : q :: v ∈ L := by simpa [PlayDigits] using hv
    obtain ⟨p, hp, hl⟩ := next _ hm
    refine ⟨(q, false), plain v ++ p, hB, ?_, ?_⟩
    · simp [hasBox, List.any_append, show p.any Prod.snd = true from hp]
    · exact play_mono hl (by simp [plain, List.append_assoc])
  | succ r ih =>
    intro B
    obtain ⟨q, v, hB, hv⟩ := h B
    refine ⟨(q, false), plain v, hB, ?_, ih hv ?_⟩
    · simp [hasBox, plain]
    · intro z hz
      have := next ((q :: v) ++ z) hz
      simpa [plain, List.append_assoc] using this

/-- Each level supplies ordinary segments followed by a segment crossing a marked boundary. -/
def runPlan : List ℕ → List Bool
  | [] => []
  | d :: ds => List.replicate d false ++ true :: runPlan ds

/-- Extract one inner level while preserving a rich suffix for every completed word. -/
private theorem prepare_wide (r : ℕ) (bs : List Bool)
    (θ : Ordinal.{0}) (m : ℕ) (S : Set (Tuple (Words ℕ) m))
    (hw : HasWideLevel (ω ^ (2*(r+1)+2 : ℕ)) θ m S)
    (follow : ∀ {l : ℕ} (T : Set (Tuple (Words ℕ) l)), θ ≤ typeLT T →
      Prepared bs (fun z => ∃ t ∈ T, z = tupleRaw t ++ [(0,true)])) :
    Prepared (List.replicate r false ++ true :: bs)
      (fun z => ∃ t ∈ S, z = tupleRaw t ++ [(0,true)]) := by
  induction m with
  | zero => exact hw.elim
  | succ m ih =>
    rcases hw with h | ⟨a, h⟩
    · let T := {a : Words ℕ | θ ≤ typeLT (firstFiber S a)}
      obtain ⟨n, p, hp⟩ := inner_word_play T (r+1) h
      refine ⟨(n,true) :: plain p, by simp [hasBox], play_plain_then_box r hp ?_⟩
      intro z hz
      obtain ⟨w, hw, he⟩ := hz
      let a : Words ℕ := ⟨n,w⟩
      apply prepared_mono (follow (firstFiber S a) hw)
      intro u hu
      obtain ⟨t, ht, rfl⟩ := hu
      refine ⟨toLex (a,t), ht, ?_⟩
      change (n,true) :: (plain p ++ (plain z ++ (tupleRaw t ++ [(0,true)]))) =
        (wordRaw a ++ tupleRaw t) ++ [(0,true)]
      simp [wordRaw, a, plain, he, List.append_assoc]
    · apply prepared_prefix (wordRaw a)
      apply prepared_mono (ih (firstFiber S a) h)
      intro z hz
      obtain ⟨t, ht, rfl⟩ := hz
      exact ⟨toLex (a,t), ht, by simp [tupleRaw, tupleList, List.append_assoc]⟩

/-- A large fiber supports any prescribed finite sequence of within-level runs. -/
private theorem prepare_runs (ds : List ℕ)
    {m : ℕ} (S : Set (Tuple (Words ℕ) m))
    (h : (ω ^ (ω : Ordinal.{0})) ^ (2 * ds.length) ≤ typeLT S) :
    Prepared (runPlan ds) (fun z => ∃ t ∈ S, z = tupleRaw t ++ [(0,true)]) := by
  induction ds generalizing m with
  | nil =>
    have hn : 0 < typeLT S := lt_of_lt_of_le zero_lt_one (by simpa using h)
    obtain ⟨t⟩ := (type_ne_zero_iff_nonempty.mp hn.ne')
    exact ⟨tupleRaw t.val ++ [(0,true)], by simp [hasBox], ⟨t.val, t.property, by simp⟩⟩
  | cons r rs ih =>
    apply prepare_wide r _ ((ω ^ (ω : Ordinal.{0})) ^ (2 * rs.length)) m S
    · apply wideLevel_words
      simpa [Nat.mul_succ] using h
    · exact fun _ ht => ih _ ht

private theorem play_model
    (S : Set Model) (h : typeLT S = target) (ds : List ℕ) :
    Play (true :: runPlan ds) (fun z => ∃ w ∈ S, modelRaw w = z) := by
  intro B
  obtain ⟨n, hn, ht⟩ := exists_large_outer_length S h (2*ds.length) B
  obtain ⟨p, _, hp⟩ := prepare_runs ds _ ht
  refine ⟨(n,true), p, hn, by simp [hasBox], play_mono hp ?_⟩
  rintro s ⟨t, ht, he⟩
  exact ⟨⟨n,t⟩, ht, by simp [modelRaw, ← he]⟩


private def finish (n : ℕ) : Digits → ℕ
  | [] => n
  | q :: t => finish (n + q.1 + 1) t

private theorem start_le_finish (n : ℕ) (s : Digits) : n ≤ finish n s := by
  induction s generalizing n with
  | nil => exact le_rfl
  | cons q t ih => exact (Nat.le_add_right n (q.1+1)).trans (ih _)

private theorem bounds_positions {a : Digit} {n : ℕ} {xs : Digits} (h : a ∈ positions n xs) :
    n < a.1 ∧ a.1 ≤ finish n xs := by
  induction xs generalizing n with
  | nil => contradiction
  | cons q t ih =>
    obtain ⟨q,b⟩ := q
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨by dsimp; omega, start_le_finish _ _⟩
    · obtain ⟨hl, hr⟩ := ih h
      exact ⟨by omega, hr⟩

private theorem positions_append (n : ℕ) (s t : Digits) :
    positions n (s ++ t) = positions n s ++ positions (finish n s) t := by
  induction s generalizing n with
  | nil => rfl
  | cons q s ih => cases q; simp only [List.cons_append, positions, finish, ih]

private theorem hasBox_positions (n : ℕ) (s : Digits) :
    hasBox (positions n s) = hasBox s := by
  induction s generalizing n with
  | nil => rfl
  | cons q s ih =>
    cases q
    simpa only [positions, hasBox, List.any_cons] using congrArg (_ || ·) (ih _)

/-- Split a sequence of turns between the player going first and the player going second. -/
private def turns : List Bool → List Bool × List Bool
  | [] => ([], [])
  | b :: bs => (b :: (turns bs).2, (turns bs).1)

private def AtParity {n : ℕ} (cs : Fin n → Digits) (p : ℕ) (a : Digit) : Prop :=
  ∃ i : Fin n, i.val % 2 = p ∧ a ∈ cs i

private theorem even_cons {n : ℕ} (c : Digits) (cs : Fin n → Digits) (a : Digit) :
    AtParity (Fin.cases c cs) 0 a ↔ a ∈ c ∨ AtParity cs 1 a := by
  constructor
  · rintro ⟨i,hi,ha⟩
    refine Fin.cases (fun hi ha => Or.inl ha) (fun j hj h => Or.inr ⟨j, ?_, h⟩) i hi ha
    change (j.val+1)%2 = 0 at hj
    omega
  · rintro (h | ⟨i, hi, ha⟩)
    · exact ⟨0,rfl,h⟩
    · exact ⟨i.succ, show (i.val+1)%2 = 0 by omega, ha⟩

private theorem odd_cons {n : ℕ} (c : Digits) (cs : Fin n → Digits) (a : Digit) :
    AtParity (Fin.cases c cs) 1 a ↔ AtParity cs 0 a := by
  constructor
  · rintro ⟨i,hi,ha⟩
    refine Fin.cases (fun hi _ => False.elim (by contradiction)) (fun j hj h => ⟨j, ?_, h⟩) i hi ha
    change (j.val+1)%2 = 1 at hj
    omega
  · rintro ⟨i, hi, ha⟩
    exact ⟨i.succ, show (i.val+1)%2 = 1 by omega, ha⟩

/-- The actual coordinate segments produced by two alternating strategies. -/
private structure Segments (bs : List Bool) (X Y : Digits) (floor : ℕ) where
  chunks : Fin bs.length → Digits
  inhabited : ∀ i, chunks i ≠ []
  marks : ∀ i, hasBox (chunks i) = bs.get i
  separated : ∀ i j, i < j → ∀ a ∈ chunks i, ∀ b ∈ chunks j, a.1 < b.1
  above : ∀ i, ∀ a ∈ chunks i, floor < a.1
  left_mem : ∀ a, a ∈ X ↔ AtParity chunks 0 a
  right_mem : ∀ a, a ∈ Y ↔ AtParity chunks 1 a

private theorem interleave (bs : List Bool) {K L : Digits → Prop}
    (x y floor : ℕ) (hx : Play (turns bs).1 K) (hy : Play (turns bs).2 L) :
    ∃ s t, K s ∧ L t ∧ Nonempty (Segments bs (positions x s) (positions y t) floor) := by
  induction bs generalizing K L x y floor with
  | nil =>
    exact ⟨[],[],hx,hy,⟨⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0,fun i => i.elim0,fun i => i.elim0,
      fun _ => ⟨by simp [positions], fun ⟨i,_⟩ => i.elim0⟩,
      fun _ => ⟨by simp [positions], fun ⟨i,_⟩ => i.elim0⟩⟩⟩⟩
  | cons b bs ih =>
    obtain ⟨q,v,hq,hb,hx'⟩ := hx floor
    let u := q :: v
    let c := positions x u
    let last := finish x u
    have above (a : Digit) (ha : a ∈ c) : floor < a.1 := by
      rcases List.mem_cons.mp ha with rfl | h
      · dsimp; omega
      · have hh := (bounds_positions h).1
        omega
    have hlast : floor < last := by
      have := start_le_finish (x+q.1+1) v
      change floor < finish (x+q.1+1) v
      omega
    obtain ⟨t,s,ht,hs,⟨C⟩⟩ := ih y last last hy hx'
    refine ⟨u ++ s,t,hs,ht,⟨{
      chunks := Fin.cases c C.chunks
      inhabited := Fin.cases (by cases q; simp [c,u,positions]) C.inhabited
      marks := Fin.cases ((hasBox_positions x u).trans hb) C.marks
      separated := ?_
      above := Fin.cases above (fun i a ha => hlast.trans (C.above i a ha))
      left_mem := ?_
      right_mem := ?_ }⟩⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro h; exact (lt_irrefl _ h).elim
      · intro _ a ha b hb
        exact (bounds_positions ha).2.trans_lt (C.above j b hb)
      · intro h; exact (Fin.not_lt_zero _ h).elim
      · exact fun h => C.separated _ _ (Fin.succ_lt_succ_iff.mp h)
    · intro a
      rw [positions_append, List.mem_append, even_cons]
      exact or_congr_right (C.right_mem a)
    · intro a
      exact (C.left_mem a).trans (odd_cons _ _ _).symm

/-- Coordinates supplied by the chunks of the indicated parity. -/
def runCoords (chunks : Fin 11 → List (ℕ × Bool)) (p : ℕ) : Set ℕ :=
  {z | ∃ i, i.val % 2 = p ∧ ∃ a ∈ chunks i, a.1 = z}

/-- Box coordinates supplied by the chunks of the indicated parity. -/
def runBoxes (chunks : Fin 11 → List (ℕ × Bool)) (p : ℕ) : Set ℕ :=
  {z | ∃ i, i.val % 2 = p ∧ ∃ a ∈ chunks i, a.1 = z ∧ a.2 = true}

/-- Eleven separated nonempty chunks with the prescribed marks realize the graph pattern. -/
theorem markedPattern_of_chunks (chunks : Fin 11 → List (ℕ × Bool))
    (hne : ∀ i, chunks i ≠ []) (hmarks : ∀ i, (chunks i).any Prod.snd = markedRun i)
    (hsep : ∀ i j, i < j → ∀ a ∈ chunks i, ∀ b ∈ chunks j, a.1 < b.1) :
    MarkedPattern (runCoords chunks 0) (runBoxes chunks 0)
      (runCoords chunks 1) (runBoxes chunks 1) := by
  let xs (i : Fin 11) := ((chunks i).map Prod.fst).toFinset
  have hx (i : Fin 11) : (xs i).Nonempty := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (hne i)
    exact ⟨a.1, List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, rfl⟩)⟩
  let cut (j : Fin 10) := (xs j.castSucc).max' (hx j.castSucc)
  have hi {a i} (ha : a ∈ chunks i) : inRun cut i a.1 := by
    constructor
    · intro j hj
      obtain ⟨t, ht, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp
        (Finset.max'_mem (xs j.castSucc) (hx j.castSucc)))
      change (xs j.castSucc).max' _ < _
      rw [← heq]
      apply hsep j.castSucc i _ t ht a ha
      change j.val < i.val
      omega
    · intro j hj
      have eq : j.castSucc = i := Fin.ext hj
      subst i
      exact Finset.le_max' _ _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, rfl⟩))
  have same {i j : Fin 11} {a b : ℕ × Bool} (ha : a ∈ chunks i) (hb : b ∈ chunks j)
      (h : a.1 = b.1) : i = j := by
    rcases lt_trichotomy i j with hij | hij | hji
    · exact (ne_of_lt (hsep _ _ hij a ha b hb) h).elim
    · exact hij
    · exact (ne_of_lt (hsep _ _ hji b hb a ha) h.symm).elim
  have getMark {i : Fin 11} {a : ℕ × Bool} (ha : a ∈ chunks i) {p : ℕ}
      (hz : a.1 ∈ runBoxes chunks p) : markedRun i = true := by
    obtain ⟨j, _, b, hb, eq, hbox⟩ := hz
    have hji := same ha hb eq.symm
    subst j
    rw [← hmarks]
    exact List.any_eq_true.mpr ⟨b, hb, hbox⟩
  have both (i : Fin 11) : ∃ a ∈ chunks i, markedRun i = true → a.2 = true := by
    by_cases hm : markedRun i = true
    · have hx : (chunks i).any Prod.snd = true := (hmarks i).trans hm
      obtain ⟨a, ha, hb⟩ := List.any_eq_true.mp hx
      exact ⟨a, ha, fun _ => hb⟩
    · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (hne i)
      exact ⟨a, ha, fun h => (hm h).elim⟩
  refine ⟨cut, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨a,ha,h⟩ := both i
    refine ⟨a.1, hi ha, ?_, ?_⟩
    · split <;> rename_i hp
      · exact ⟨i, hp, a, ha, rfl⟩
      · exact ⟨i, by omega, a, ha, rfl⟩
    · intro hm
      split <;> rename_i hp
      · exact ⟨i, hp, a, ha, rfl, h hm⟩
      · exact ⟨i, by omega, a, ha, rfl, h hm⟩
  · rintro _ ⟨i, hp, a, ha, rfl⟩
    exact ⟨i, hp, hi ha, getMark ha⟩
  · rintro _ ⟨i, hp, a, ha, rfl⟩
    exact ⟨i, hp, hi ha, getMark ha⟩


private def flags : List Bool :=
  [true,true,false,false,true,false,true,false,false,true,true]

private theorem coords_of_segments {w : Model} {C : Fin 11 → Digits} {p : ℕ}
    (h : ∀ a, a ∈ positions 0 (modelRaw w) ↔ AtParity C p a) :
    modelCoords w = runCoords C p ∧ modelBoxes w = runBoxes C p := by
  constructor <;> ext z <;> constructor
  · rintro ⟨b,hb⟩
    obtain ⟨i,hi,hm⟩ := (h (z,b)).1 hb
    exact ⟨i,hi,(z,b),hm,rfl⟩
  · rintro ⟨i,hi,⟨z,b⟩,hm,rfl⟩
    exact ⟨b,(h _).2 ⟨i,hi,hm⟩⟩
  · intro hz
    obtain ⟨i,hi,hm⟩ := (h (z,true)).1 hz
    exact ⟨i,hi,(z,true),hm,rfl,rfl⟩
  · rintro ⟨i,hi,⟨z,b⟩,hm,rfl,rfl⟩
    exact (h _).2 ⟨i,hi,hm⟩

/-- Every subset having the order type of the whole model contains an edge of the pattern. -/
theorem pattern_edge_of_full_type (S : Set Model) (hS : typeLT S = target) :
    ∃ x ∈ S, ∃ y ∈ S, patternGraph.Adj x y := by
  let K z := ∃ w ∈ S, modelRaw w = z
  have hx : Play (turns flags).1 K := play_model S hS [1,0,1]
  have hy : Play (turns flags).2 K := play_model S hS [3]
  obtain ⟨s,t,⟨x,hx,rfl⟩,⟨y,hy,rfl⟩,⟨C⟩⟩ := interleave flags 0 0 0 hx hy
  have hpat := markedPattern_of_chunks C.chunks C.inhabited (fun i => ?_) C.separated
  case refine_1 =>
    exact (C.marks i).trans (by fin_cases i <;> rfl)
  obtain ⟨ex,bx⟩ := coords_of_segments C.left_mem
  obtain ⟨ey,by'⟩ := coords_of_segments C.right_mem
  rw [← ex, ← bx, ← ey, ← by'] at hpat
  have hy0 : (y.1+1,true) ∈ positions 0 (modelRaw y) := by
    simp [modelRaw, positions]
  obtain ⟨i, hi, hiy⟩ := (C.right_mem _).1 hy0
  obtain ⟨a,ha⟩ := List.exists_mem_of_ne_nil _ (C.inhabited (0 : Fin 11))
  have hlt : (0 : Fin 11) < i := by change 0 < i.val; omega
  have hxy := C.separated _ _ hlt a ha (y.1+1,true) hiy
  have ha' := (C.left_mem a).2 ⟨(0 : Fin 11),rfl,ha⟩
  have hm : x.1+1 ≤ a.1 := by
    change a ∈ (0 + x.1 + 1,true) :: _ at ha'
    rcases List.mem_cons.mp ha' with rfl | h
    · simp
    · exact le_of_lt (by simpa only [Nat.zero_add] using (bounds_positions h).1)
  have hfirst : x.1 < y.1 := by change a.1 < y.1+1 at hxy; omega
  exact ⟨x,hx,y,hy,fun he => hfirst.ne (congrArg Sigma.fst he), Or.inl ⟨hfirst,hpat⟩⟩

theorem patternGraph_no_independentCopy : ¬ IndependentCopy patternGraph := by
  intro h
  obtain ⟨s, hs, ht⟩ := (independentCopy_iff patternGraph).mp h
  obtain ⟨x,hx,y,hy,hxy⟩ := pattern_edge_of_full_type s (ht.trans type_model)
  exact (patternGraph.isIndepSet_iff.mp hs) hx hy hxy.ne hxy

/- ## Exclusion of a blue five-clique -/

private structure RunData where
  cut : Fin 10 → ℕ
  point : Fin 11 → ℕ
deriving Inhabited

private def RunData.Valid (d : RunData) (X A Y B : Set ℕ) : Prop :=
  (∀ i : Fin 11, inRun d.cut i (d.point i) ∧
    (if i.val % 2 = 0 then d.point i ∈ X else d.point i ∈ Y) ∧
    (markedRun i = true → if i.val % 2 = 0 then d.point i ∈ A else d.point i ∈ B)) ∧
  (∀ z ∈ X, ∃ i : Fin 11, i.val % 2 = 0 ∧ inRun d.cut i z ∧ (z ∈ A → markedRun i = true)) ∧
  (∀ z ∈ Y, ∃ i : Fin 11, i.val % 2 = 1 ∧ inRun d.cut i z ∧ (z ∈ B → markedRun i = true))

private theorem MarkedPattern.data {X A Y B : Set ℕ} (h : MarkedPattern X A Y B) :
    ∃ d : RunData, d.Valid X A Y B := by
  obtain ⟨cut, hs, hx, hy⟩ := h
  choose point hp using hs
  exact ⟨⟨cut, point⟩, hp, hx, hy⟩

private def evenSlots (marked : Bool) (c : Fin 10 → ℕ) (z : ℕ) : Prop :=
  if marked then
    z < c 0 ∨ (c 3 < z ∧ z < c 4) ∨ (c 5 < z ∧ z < c 6) ∨ c 9 < z
  else
    z < c 0 ∨ (c 1 < z ∧ z < c 2) ∨ (c 3 < z ∧ z < c 4) ∨
      (c 5 < z ∧ z < c 6) ∨ (c 7 < z ∧ z < c 8) ∨ c 9 < z

private def oddSlots (marked : Bool) (c : Fin 10 → ℕ) (z : ℕ) : Prop :=
  if marked then
    (c 0 < z ∧ z < c 1) ∨ (c 8 < z ∧ z < c 9)
  else
    (c 0 < z ∧ z < c 1) ∨ (c 2 < z ∧ z < c 3) ∨ (c 4 < z ∧ z < c 5) ∨
      (c 6 < z ∧ z < c 7) ∨ (c 8 < z ∧ z < c 9)

private theorem evenSlots_of_run (m : Bool) (c : Fin 10 → ℕ) (z : ℕ)
    (h : ∃ i : Fin 11, i.val % 2 = 0 ∧ inRun c i z ∧ (m = true → markedRun i = true)) :
    evenSlots m (fun k => 2 * c k + 1) (2 * z) := by
  obtain ⟨i, hi, hr, hm⟩ := h
  cases m <;> fin_cases i <;>
    simp_all [evenSlots, inRun, markedRun, Fin.forall_fin_succ] <;> omega

private theorem oddSlots_of_run (m : Bool) (c : Fin 10 → ℕ) (z : ℕ)
    (h : ∃ i : Fin 11, i.val % 2 = 1 ∧ inRun c i z ∧ (m = true → markedRun i = true)) :
    oddSlots m (fun k => 2 * c k + 1) (2 * z) := by
  obtain ⟨i, hi, hr, hm⟩ := h
  cases m <;> fin_cases i <;>
    simp_all [oddSlots, inRun, markedRun, Fin.forall_fin_succ] <;> omega

/-- Cuts are doubled and shifted by one, and sample coordinates are doubled, so
every interval boundary becomes a strict inequality. -/
private structure FiveRuns where
  c : Fin 5 → Fin 5 → Fin 10 → ℕ
  p : Fin 5 → Fin 5 → Fin 11 → ℕ
  before (i j : Fin 5) (k : Fin 10) (h : i < j) : p i j k.castSucc < c i j k
  after (i j : Fin 5) (k : Fin 10) (h : i < j) : c i j k < p i j k.succ
  left (i j a b : Fin 5) (r : Fin 11) (hij : i < j) (hab : a < b)
    (howner : (if r.val % 2 = 0 then i else j) = a) :
    evenSlots (markedRun r) (c a b) (p i j r)
  right (i j a b : Fin 5) (r : Fin 11) (hij : i < j) (hab : a < b)
    (howner : (if r.val % 2 = 0 then i else j) = b) :
    oddSlots (markedRun r) (c a b) (p i j r)

private theorem runsOfFive {V : Type*} (coord box : V → Set ℕ) (v : Fin 5 → V)
    (h : ∀ i j, i < j → MarkedPattern (coord (v i)) (box (v i)) (coord (v j)) (box (v j))) :
    Nonempty FiveRuns := by
  classical
  have H (i j : Fin 5) : ∃ d : RunData, i < j →
      d.Valid (coord (v i)) (box (v i)) (coord (v j)) (box (v j)) := by
    by_cases hij : i < j
    · obtain ⟨d, hd⟩ := (h i j hij).data
      exact ⟨d, fun _ => hd⟩
    · exact ⟨default, fun h' => (hij h').elim⟩
  choose d hd using H
  refine ⟨⟨fun i j k => 2 * (d i j).cut k + 1, fun i j k => 2 * (d i j).point k, ?_, ?_, ?_, ?_⟩⟩
  · intro i j k hij
    have := ((hd i j hij).1 k.castSucc).1.2 k rfl
    omega
  · intro i j k hij
    have := ((hd i j hij).1 k.succ).1.1 k rfl
    omega
  · intro i j a b r hij hab ho
    apply evenSlots_of_run
    obtain ⟨_, hmem, hmark⟩ := (hd i j hij).1 r
    let z := (d i j).point r
    have hx : z ∈ coord (v a) := by
      split at ho <;> rename_i he <;> subst a <;> simpa [z, he] using hmem
    obtain ⟨s, hs, hr, hb⟩ := (hd a b hab).2.1 z hx
    refine ⟨s, hs, hr, fun hm => hb ?_⟩
    split at ho <;> rename_i he <;> subst a <;> simpa [z, he] using hmark hm
  · intro i j a b r hij hab ho
    apply oddSlots_of_run
    obtain ⟨_, hmem, hmark⟩ := (hd i j hij).1 r
    let z := (d i j).point r
    have hy : z ∈ coord (v b) := by
      split at ho <;> rename_i he <;> subst b <;> simpa [z, he] using hmem
    obtain ⟨s, hs, hr, hb⟩ := (hd a b hab).2.2 z hy
    refine ⟨s, hs, hr, fun hm => hb ?_⟩
    split at ho <;> rename_i he <;> subst b <;> simpa [z, he] using hmark hm

/- Straight-line arithmetic certificate for the empty intersection of the ten pair constraints.
The indices name sample coordinates and cuts in the five diagrams. -/
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 32000 in
private theorem incompatibleSamples (p : Nat → Nat)
 (ℎ0 : p 0 < p 94)
 (ℎ1 : p 94 < p 1)
 (ℎ2 : p 1 < p 95)
 (ℎ3 : p 95 < p 2)
 (ℎ4 : p 2 < p 96)
 (ℎ5 : p 96 < p 3)
 (ℎ6 : p 3 < p 97)
 (ℎ7 : p 97 < p 4)
 (ℎ8 : p 4 < p 98)
 (ℎ9 : p 98 < p 5)
 (ℎ10 : p 5 < p 99)
 (ℎ11 : p 99 < p 6)
 (ℎ12 : p 6 < p 100)
 (ℎ13 : p 100 < p 7)
 (ℎ14 : p 7 < p 101)
 (ℎ15 : p 101 < p 8)
 (ℎ16 : p 8 < p 102)
 (ℎ17 : p 102 < p 9)
 (ℎ18 : p 10 < p 103)
 (ℎ19 : p 103 < p 11)
 (ℎ20 : p 11 < p 104)
 (ℎ21 : p 104 < p 12)
 (ℎ22 : p 12 < p 105)
 (ℎ23 : p 105 < p 13)
 (ℎ24 : p 13 < p 106)
 (ℎ25 : p 106 < p 14)
 (ℎ26 : p 14 < p 107)
 (ℎ27 : p 107 < p 15)
 (ℎ28 : p 15 < p 108)
 (ℎ29 : p 108 < p 16)
 (ℎ30 : p 16 < p 109)
 (ℎ31 : p 109 < p 17)
 (ℎ32 : p 17 < p 110)
 (ℎ33 : p 110 < p 18)
 (ℎ34 : p 18 < p 111)
 (ℎ35 : p 111 < p 19)
 (ℎ36 : p 20 < p 112)
 (ℎ37 : p 112 < p 21)
 (ℎ38 : p 21 < p 113)
 (ℎ39 : p 113 < p 22)
 (ℎ40 : p 22 < p 114)
 (ℎ41 : p 114 < p 23)
 (ℎ42 : p 23 < p 115)
 (ℎ43 : p 115 < p 24)
 (ℎ44 : p 24 < p 116)
 (ℎ45 : p 116 < p 25)
 (ℎ46 : p 25 < p 117)
 (ℎ47 : p 117 < p 26)
 (ℎ48 : p 26 < p 118)
 (ℎ49 : p 118 < p 27)
 (ℎ50 : p 27 < p 119)
 (ℎ51 : p 119 < p 28)
 (ℎ52 : p 28 < p 120)
 (ℎ53 : p 120 < p 29)
 (ℎ54 : p 121 < p 30)
 (ℎ55 : p 30 < p 122)
 (ℎ56 : p 122 < p 31)
 (ℎ57 : p 31 < p 123)
 (ℎ58 : p 123 < p 32)
 (ℎ59 : p 32 < p 124)
 (ℎ60 : p 124 < p 33)
 (ℎ61 : p 33 < p 125)
 (ℎ62 : p 125 < p 34)
 (ℎ63 : p 34 < p 126)
 (ℎ64 : p 126 < p 35)
 (ℎ65 : p 35 < p 127)
 (ℎ66 : p 127 < p 36)
 (ℎ67 : p 36 < p 128)
 (ℎ68 : p 128 < p 37)
 (ℎ69 : p 37 < p 129)
 (ℎ70 : p 130 < p 38)
 (ℎ71 : p 38 < p 131)
 (ℎ72 : p 131 < p 39)
 (ℎ73 : p 39 < p 133)
 (ℎ74 : p 133 < p 40)
 (ℎ75 : p 40 < p 134)
 (ℎ76 : p 134 < p 41)
 (ℎ77 : p 41 < p 135)
 (ℎ78 : p 135 < p 42)
 (ℎ79 : p 42 < p 136)
 (ℎ80 : p 136 < p 43)
 (ℎ81 : p 43 < p 137)
 (ℎ82 : p 137 < p 44)
 (ℎ83 : p 44 < p 138)
 (ℎ84 : p 138 < p 45)
 (ℎ85 : p 45 < p 139)
 (ℎ86 : p 139 < p 46)
 (ℎ87 : p 46 < p 140)
 (ℎ88 : p 140 < p 47)
 (ℎ89 : p 47 < p 132)
 (ℎ90 : p 48 < p 141)
 (ℎ91 : p 141 < p 49)
 (ℎ92 : p 49 < p 142)
 (ℎ93 : p 142 < p 50)
 (ℎ94 : p 50 < p 143)
 (ℎ95 : p 143 < p 51)
 (ℎ96 : p 51 < p 144)
 (ℎ97 : p 144 < p 52)
 (ℎ98 : p 52 < p 145)
 (ℎ99 : p 145 < p 53)
 (ℎ100 : p 53 < p 146)
 (ℎ101 : p 146 < p 54)
 (ℎ102 : p 54 < p 147)
 (ℎ103 : p 147 < p 55)
 (ℎ104 : p 55 < p 148)
 (ℎ105 : p 148 < p 56)
 (ℎ106 : p 56 < p 149)
 (ℎ107 : p 149 < p 57)
 (ℎ108 : p 150 < p 58)
 (ℎ109 : p 58 < p 151)
 (ℎ110 : p 151 < p 59)
 (ℎ111 : p 59 < p 152)
 (ℎ112 : p 152 < p 60)
 (ℎ113 : p 60 < p 153)
 (ℎ114 : p 153 < p 61)
 (ℎ115 : p 61 < p 154)
 (ℎ116 : p 154 < p 62)
 (ℎ117 : p 62 < p 155)
 (ℎ118 : p 155 < p 63)
 (ℎ119 : p 63 < p 156)
 (ℎ120 : p 156 < p 64)
 (ℎ121 : p 64 < p 157)
 (ℎ122 : p 157 < p 65)
 (ℎ123 : p 65 < p 158)
 (ℎ124 : p 159 < p 66)
 (ℎ125 : p 66 < p 160)
 (ℎ126 : p 160 < p 67)
 (ℎ127 : p 67 < p 162)
 (ℎ128 : p 162 < p 68)
 (ℎ129 : p 68 < p 163)
 (ℎ130 : p 163 < p 69)
 (ℎ131 : p 69 < p 164)
 (ℎ132 : p 164 < p 70)
 (ℎ133 : p 70 < p 165)
 (ℎ134 : p 165 < p 71)
 (ℎ135 : p 71 < p 166)
 (ℎ136 : p 166 < p 72)
 (ℎ137 : p 72 < p 167)
 (ℎ138 : p 167 < p 73)
 (ℎ139 : p 73 < p 168)
 (ℎ140 : p 168 < p 74)
 (ℎ141 : p 74 < p 169)
 (ℎ142 : p 169 < p 75)
 (ℎ143 : p 75 < p 161)
 (ℎ144 : p 170 < p 76)
 (ℎ145 : p 76 < p 171)
 (ℎ146 : p 171 < p 77)
 (ℎ147 : p 77 < p 172)
 (ℎ148 : p 172 < p 78)
 (ℎ149 : p 78 < p 173)
 (ℎ150 : p 173 < p 79)
 (ℎ151 : p 79 < p 174)
 (ℎ152 : p 174 < p 80)
 (ℎ153 : p 80 < p 175)
 (ℎ154 : p 175 < p 81)
 (ℎ155 : p 81 < p 176)
 (ℎ156 : p 176 < p 82)
 (ℎ157 : p 82 < p 177)
 (ℎ158 : p 177 < p 83)
 (ℎ159 : p 83 < p 178)
 (ℎ160 : p 179 < p 84)
 (ℎ161 : p 84 < p 180)
 (ℎ162 : p 180 < p 85)
 (ℎ163 : p 85 < p 182)
 (ℎ164 : p 182 < p 86)
 (ℎ165 : p 86 < p 183)
 (ℎ166 : p 183 < p 87)
 (ℎ167 : p 87 < p 184)
 (ℎ168 : p 184 < p 88)
 (ℎ169 : p 88 < p 185)
 (ℎ170 : p 185 < p 89)
 (ℎ171 : p 89 < p 186)
 (ℎ172 : p 186 < p 90)
 (ℎ173 : p 90 < p 187)
 (ℎ174 : p 187 < p 91)
 (ℎ175 : p 91 < p 188)
 (ℎ176 : p 188 < p 92)
 (ℎ177 : p 92 < p 189)
 (ℎ178 : p 189 < p 93)
 (ℎ179 : p 93 < p 181)
 (ℎ180 : (p 104 < p 0 ∨ (p 1 < p 104 ∧ p 104 < p 2) ∨ (p 3 < p 104 ∧ p 104 < p 4) ∨ (p 5 < p 104 ∧ p 104 < p 6) ∨ (p 7 < p 104 ∧ p 104 < p 8) ∨ p 9 < p 104))
 (ℎ181 : (p 110 < p 0 ∨ (p 1 < p 110 ∧ p 110 < p 2) ∨ (p 3 < p 110 ∧ p 110 < p 4) ∨ (p 5 < p 110 ∧ p 110 < p 6) ∨ (p 7 < p 110 ∧ p 110 < p 8) ∨ p 9 < p 110))
 (ℎ182 : (p 113 < p 0 ∨ (p 1 < p 113 ∧ p 113 < p 2) ∨ (p 3 < p 113 ∧ p 113 < p 4) ∨ (p 5 < p 113 ∧ p 113 < p 6) ∨ (p 7 < p 113 ∧ p 113 < p 8) ∨ p 9 < p 113))
 (ℎ183 : (p 119 < p 0 ∨ (p 1 < p 119 ∧ p 119 < p 2) ∨ (p 3 < p 119 ∧ p 119 < p 4) ∨ (p 5 < p 119 ∧ p 119 < p 6) ∨ (p 7 < p 119 ∧ p 119 < p 8) ∨ p 9 < p 119))
 (ℎ184 : (p 124 < p 0 ∨ (p 3 < p 124 ∧ p 124 < p 4) ∨ (p 5 < p 124 ∧ p 124 < p 6) ∨ p 9 < p 124))
 (ℎ185 : ((p 0 < p 130 ∧ p 130 < p 1) ∨ (p 8 < p 130 ∧ p 130 < p 9)))
 (ℎ186 : ((p 0 < p 132 ∧ p 132 < p 1) ∨ (p 8 < p 132 ∧ p 132 < p 9)))
 (ℎ187 : ((p 0 < p 153 ∧ p 153 < p 1) ∨ (p 8 < p 153 ∧ p 153 < p 9)))
 (ℎ188 : ((p 0 < p 155 ∧ p 155 < p 1) ∨ (p 8 < p 155 ∧ p 155 < p 9)))
 (ℎ189 : (p 95 < p 10 ∨ (p 11 < p 95 ∧ p 95 < p 12) ∨ (p 13 < p 95 ∧ p 95 < p 14) ∨ (p 15 < p 95 ∧ p 95 < p 16) ∨ (p 17 < p 95 ∧ p 95 < p 18) ∨ p 19 < p 95))
 (ℎ190 : (p 101 < p 10 ∨ (p 11 < p 101 ∧ p 101 < p 12) ∨ (p 13 < p 101 ∧ p 101 < p 14) ∨ (p 15 < p 101 ∧ p 101 < p 16) ∨ (p 17 < p 101 ∧ p 101 < p 18) ∨ p 19 < p 101))
 (ℎ191 : (p 113 < p 10 ∨ (p 11 < p 113 ∧ p 113 < p 12) ∨ (p 13 < p 113 ∧ p 113 < p 14) ∨ (p 15 < p 113 ∧ p 113 < p 16) ∨ (p 17 < p 113 ∧ p 113 < p 18) ∨ p 19 < p 113))
 (ℎ192 : (p 115 < p 10 ∨ (p 13 < p 115 ∧ p 115 < p 14) ∨ (p 15 < p 115 ∧ p 115 < p 16) ∨ p 19 < p 115))
 (ℎ193 : (p 117 < p 10 ∨ (p 13 < p 117 ∧ p 117 < p 14) ∨ (p 15 < p 117 ∧ p 117 < p 16) ∨ p 19 < p 117))
 (ℎ194 : (p 119 < p 10 ∨ (p 11 < p 119 ∧ p 119 < p 12) ∨ (p 13 < p 119 ∧ p 119 < p 14) ∨ (p 15 < p 119 ∧ p 119 < p 16) ∨ (p 17 < p 119 ∧ p 119 < p 18) ∨ p 19 < p 119))
 (ℎ195 : ((p 10 < p 159 ∧ p 159 < p 11) ∨ (p 18 < p 159 ∧ p 159 < p 19)))
 (ℎ196 : ((p 10 < p 161 ∧ p 161 < p 11) ∨ (p 18 < p 161 ∧ p 161 < p 19)))
 (ℎ197 : ((p 10 < p 173 ∧ p 173 < p 11) ∨ (p 18 < p 173 ∧ p 173 < p 19)))
 (ℎ198 : ((p 10 < p 175 ∧ p 175 < p 11) ∨ (p 18 < p 175 ∧ p 175 < p 19)))
 (ℎ199 : (p 95 < p 20 ∨ (p 21 < p 95 ∧ p 95 < p 22) ∨ (p 23 < p 95 ∧ p 95 < p 24) ∨ (p 25 < p 95 ∧ p 95 < p 26) ∨ (p 27 < p 95 ∧ p 95 < p 28) ∨ p 29 < p 95))
 (ℎ200 : (p 101 < p 20 ∨ (p 21 < p 101 ∧ p 101 < p 22) ∨ (p 23 < p 101 ∧ p 101 < p 24) ∨ (p 25 < p 101 ∧ p 101 < p 26) ∨ (p 27 < p 101 ∧ p 101 < p 28) ∨ p 29 < p 101))
 (ℎ201 : (p 124 < p 20 ∨ (p 23 < p 124 ∧ p 124 < p 24) ∨ (p 25 < p 124 ∧ p 124 < p 26) ∨ p 29 < p 124))
 (ℎ202 : (p 126 < p 20 ∨ (p 23 < p 126 ∧ p 126 < p 24) ∨ (p 25 < p 126 ∧ p 126 < p 26) ∨ p 29 < p 126))
 (ℎ203 : ((p 20 < p 179 ∧ p 179 < p 21) ∨ (p 28 < p 179 ∧ p 179 < p 29)))
 (ℎ204 : ((p 20 < p 184 ∧ p 184 < p 21) ∨ (p 28 < p 184 ∧ p 184 < p 29)))
 (ℎ205 : ((p 20 < p 186 ∧ p 186 < p 21) ∨ (p 28 < p 186 ∧ p 186 < p 29)))
 (ℎ206 : ((p 20 < p 181 ∧ p 181 < p 21) ∨ (p 28 < p 181 ∧ p 181 < p 29)))
 (ℎ207 : (p 96 < p 38 ∨ (p 39 < p 96 ∧ p 96 < p 40) ∨ (p 41 < p 96 ∧ p 96 < p 42) ∨ (p 43 < p 96 ∧ p 96 < p 44) ∨ (p 45 < p 96 ∧ p 96 < p 46) ∨ p 47 < p 96))
 (ℎ208 : (p 100 < p 38 ∨ (p 39 < p 100 ∧ p 100 < p 40) ∨ (p 41 < p 100 ∧ p 100 < p 42) ∨ (p 43 < p 100 ∧ p 100 < p 44) ∨ (p 45 < p 100 ∧ p 100 < p 46) ∨ p 47 < p 100))
 (ℎ209 : (p 142 < p 38 ∨ (p 39 < p 142 ∧ p 142 < p 40) ∨ (p 41 < p 142 ∧ p 142 < p 42) ∨ (p 43 < p 142 ∧ p 142 < p 44) ∨ (p 45 < p 142 ∧ p 142 < p 46) ∨ p 47 < p 142))
 (ℎ210 : (p 148 < p 38 ∨ (p 39 < p 148 ∧ p 148 < p 40) ∨ (p 41 < p 148 ∧ p 148 < p 42) ∨ (p 43 < p 148 ∧ p 148 < p 44) ∨ (p 45 < p 148 ∧ p 148 < p 46) ∨ p 47 < p 148))
 (ℎ211 : ((p 38 < p 159 ∧ p 159 < p 39) ∨ (p 46 < p 159 ∧ p 159 < p 47)))
 (ℎ212 : ((p 38 < p 164 ∧ p 164 < p 39) ∨ (p 46 < p 164 ∧ p 164 < p 47)))
 (ℎ213 : ((p 38 < p 166 ∧ p 166 < p 39) ∨ (p 46 < p 166 ∧ p 166 < p 47)))
 (ℎ214 : ((p 38 < p 161 ∧ p 161 < p 39) ∨ (p 46 < p 161 ∧ p 161 < p 47)))
 (ℎ215 : ((p 38 < p 173 ∧ p 173 < p 39) ∨ (p 46 < p 173 ∧ p 173 < p 47)))
 (ℎ216 : ((p 38 < p 175 ∧ p 175 < p 39) ∨ (p 46 < p 175 ∧ p 175 < p 47)))
 (ℎ217 : (p 96 < p 48 ∨ (p 49 < p 96 ∧ p 96 < p 50) ∨ (p 51 < p 96 ∧ p 96 < p 52) ∨ (p 53 < p 96 ∧ p 96 < p 54) ∨ (p 55 < p 96 ∧ p 96 < p 56) ∨ p 57 < p 96))
 (ℎ218 : (p 100 < p 48 ∨ (p 49 < p 100 ∧ p 100 < p 50) ∨ (p 51 < p 100 ∧ p 100 < p 52) ∨ (p 53 < p 100 ∧ p 100 < p 54) ∨ (p 55 < p 100 ∧ p 100 < p 56) ∨ p 57 < p 100))
 (ℎ219 : (p 153 < p 48 ∨ (p 51 < p 153 ∧ p 153 < p 52) ∨ (p 53 < p 153 ∧ p 153 < p 54) ∨ p 57 < p 153))
 (ℎ220 : (p 155 < p 48 ∨ (p 51 < p 155 ∧ p 155 < p 52) ∨ (p 53 < p 155 ∧ p 155 < p 54) ∨ p 57 < p 155))
 (ℎ221 : ((p 48 < p 179 ∧ p 179 < p 49) ∨ (p 56 < p 179 ∧ p 179 < p 57)))
 (ℎ222 : ((p 48 < p 184 ∧ p 184 < p 49) ∨ (p 56 < p 184 ∧ p 184 < p 57)))
 (ℎ223 : ((p 48 < p 186 ∧ p 186 < p 49) ∨ (p 56 < p 186 ∧ p 186 < p 57)))
 (ℎ224 : ((p 48 < p 181 ∧ p 181 < p 49) ∨ (p 56 < p 181 ∧ p 181 < p 57)))
 (ℎ225 : (p 105 < p 66 ∨ (p 67 < p 105 ∧ p 105 < p 68) ∨ (p 69 < p 105 ∧ p 105 < p 70) ∨ (p 71 < p 105 ∧ p 105 < p 72) ∨ (p 73 < p 105 ∧ p 105 < p 74) ∨ p 75 < p 105))
 (ℎ226 : (p 109 < p 66 ∨ (p 67 < p 109 ∧ p 109 < p 68) ∨ (p 69 < p 109 ∧ p 109 < p 70) ∨ (p 71 < p 109 ∧ p 109 < p 72) ∨ (p 73 < p 109 ∧ p 109 < p 74) ∨ p 75 < p 109))
 (ℎ227 : (p 173 < p 66 ∨ (p 69 < p 173 ∧ p 173 < p 70) ∨ (p 71 < p 173 ∧ p 173 < p 72) ∨ p 75 < p 173))
 (ℎ228 : (p 175 < p 66 ∨ (p 69 < p 175 ∧ p 175 < p 70) ∨ (p 71 < p 175 ∧ p 175 < p 72) ∨ p 75 < p 175))
 (ℎ229 : ((p 66 < p 116 ∧ p 116 < p 67) ∨ (p 68 < p 116 ∧ p 116 < p 69) ∨ (p 70 < p 116 ∧ p 116 < p 71) ∨ (p 72 < p 116 ∧ p 116 < p 73) ∨ (p 74 < p 116 ∧ p 116 < p 75)))
 (ℎ230 : ((p 66 < p 143 ∧ p 143 < p 67) ∨ (p 68 < p 143 ∧ p 143 < p 69) ∨ (p 70 < p 143 ∧ p 143 < p 71) ∨ (p 72 < p 143 ∧ p 143 < p 73) ∨ (p 74 < p 143 ∧ p 143 < p 75)))
 (ℎ231 : ((p 66 < p 147 ∧ p 147 < p 67) ∨ (p 68 < p 147 ∧ p 147 < p 69) ∨ (p 70 < p 147 ∧ p 147 < p 71) ∨ (p 72 < p 147 ∧ p 147 < p 73) ∨ (p 74 < p 147 ∧ p 147 < p 75)))
 (ℎ232 : ((p 66 < p 179 ∧ p 179 < p 67) ∨ (p 74 < p 179 ∧ p 179 < p 75)))
 (ℎ233 : ((p 66 < p 184 ∧ p 184 < p 67) ∨ (p 74 < p 184 ∧ p 184 < p 75)))
 (ℎ234 : ((p 66 < p 186 ∧ p 186 < p 67) ∨ (p 74 < p 186 ∧ p 186 < p 75)))
 (ℎ235 : ((p 66 < p 181 ∧ p 181 < p 67) ∨ (p 74 < p 181 ∧ p 181 < p 75)))
 (ℎ236 : (p 114 < p 84 ∨ (p 85 < p 114 ∧ p 114 < p 86) ∨ (p 87 < p 114 ∧ p 114 < p 88) ∨ (p 89 < p 114 ∧ p 114 < p 90) ∨ (p 91 < p 114 ∧ p 114 < p 92) ∨ p 93 < p 114))
 (ℎ237 : (p 118 < p 84 ∨ (p 85 < p 118 ∧ p 118 < p 86) ∨ (p 87 < p 118 ∧ p 118 < p 88) ∨ (p 89 < p 118 ∧ p 118 < p 90) ∨ (p 91 < p 118 ∧ p 118 < p 92) ∨ p 93 < p 118))
 (ℎ238 : (p 143 < p 84 ∨ (p 85 < p 143 ∧ p 143 < p 86) ∨ (p 87 < p 143 ∧ p 143 < p 88) ∨ (p 89 < p 143 ∧ p 143 < p 90) ∨ (p 91 < p 143 ∧ p 143 < p 92) ∨ p 93 < p 143))
 (ℎ239 : (p 147 < p 84 ∨ (p 85 < p 147 ∧ p 147 < p 86) ∨ (p 87 < p 147 ∧ p 147 < p 88) ∨ (p 89 < p 147 ∧ p 147 < p 90) ∨ (p 91 < p 147 ∧ p 147 < p 92) ∨ p 93 < p 147))
 (ℎ240 : ((p 84 < p 121 ∧ p 121 < p 85) ∨ (p 92 < p 121 ∧ p 121 < p 93)))
 (ℎ241 : ((p 84 < p 125 ∧ p 125 < p 85) ∨ (p 86 < p 125 ∧ p 125 < p 87) ∨ (p 88 < p 125 ∧ p 125 < p 89) ∨ (p 90 < p 125 ∧ p 125 < p 91) ∨ (p 92 < p 125 ∧ p 125 < p 93)))
 (ℎ242 : ((p 84 < p 129 ∧ p 129 < p 85) ∨ (p 92 < p 129 ∧ p 129 < p 93)))
 (ℎ243 : ((p 84 < p 150 ∧ p 150 < p 85) ∨ (p 92 < p 150 ∧ p 150 < p 93)))
 (ℎ244 : ((p 84 < p 154 ∧ p 154 < p 85) ∨ (p 86 < p 154 ∧ p 154 < p 87) ∨ (p 88 < p 154 ∧ p 154 < p 89) ∨ (p 90 < p 154 ∧ p 154 < p 91) ∨ (p 92 < p 154 ∧ p 154 < p 93)))
 (ℎ245 : ((p 84 < p 158 ∧ p 158 < p 85) ∨ (p 92 < p 158 ∧ p 158 < p 93)))
 (ℎ246 : ((p 84 < p 170 ∧ p 170 < p 85) ∨ (p 92 < p 170 ∧ p 170 < p 93)))
 (ℎ247 : ((p 84 < p 174 ∧ p 174 < p 85) ∨ (p 86 < p 174 ∧ p 174 < p 87) ∨ (p 88 < p 174 ∧ p 174 < p 89) ∨ (p 90 < p 174 ∧ p 174 < p 91) ∨ (p 92 < p 174 ∧ p 174 < p 93)))
 (ℎ248 : ((p 84 < p 178 ∧ p 178 < p 85) ∨ (p 92 < p 178 ∧ p 178 < p 93)))
: False := by
  have ℎ249 : (p 174 < p 89 ∨ ¬((p 174 ≤ p 90 ∨ p 91 ≤ p 174)) ∨ ¬((p 174 ≤ p 92 ∨ p 93 ≤ p 174)) ∨ ¬((p 174 ≤ p 84 ∨ p 85 ≤ p 174))) := by
    clear * - ℎ167 ℎ168 ℎ169 ℎ170 ℎ247
    grind (splits := 10000) (ematch := 0) only
  have ℎ250 : (p 148 < p 44 ∨ p 47 < p 148 ∨ p 148 < p 38 ∨ ¬((p 148 ≤ p 45 ∨ p 46 ≤ p 148))) := by
    clear * - ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ210
    grind (splits := 10000) (ematch := 0) only
  have ℎ251 : (p 148 < p 46 ∨ p 148 < p 38 ∨ p 47 < p 148) := by
    clear * - ℎ83 ℎ84 ℎ85 ℎ86 ℎ250
    grind (splits := 10000) (ematch := 0) only
  have ℎ252 : (p 148 < p 46 ∨ p 47 < p 148) := by
    clear * - ℎ71 ℎ72 ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ251
    grind (splits := 10000) (ematch := 0) only
  have ℎ253 : (p 47 ≤ p 161 ∨ p 75 ≤ p 181 ∨ p 181 ≤ p 56 ∨ p 148 ≤ p 47) := by
    clear * - ℎ105 ℎ143
    grind (splits := 10000) (ematch := 0) only
  have ℎ254 : (p 148 ≤ p 47 ∨ p 75 ≤ p 181 ∨ p 181 ≤ p 56) := by
    clear * - ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ87 ℎ88 ℎ105 ℎ143 ℎ214 ℎ253
    grind (splits := 10000) (ematch := 0) only
  have ℎ255 : p 181 < p 75 := by
    clear * - ℎ127 ℎ128 ℎ129 ℎ130 ℎ131 ℎ132 ℎ133 ℎ134 ℎ135 ℎ136 ℎ137 ℎ138 ℎ139 ℎ140 ℎ141 ℎ142 ℎ235
    grind (splits := 10000) (ematch := 0) only
  have ℎ256 : p 158 < p 93 := by
    clear * - ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176 ℎ177 ℎ178 ℎ245
    grind (splits := 10000) (ematch := 0) only
  have ℎ257 : (p 85 ≤ p 150 ∨ p 150 ≤ p 92) := by
    clear * - ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176
    grind (splits := 10000) (ematch := 0) only
  have ℎ258 : p 84 < p 150 := by
    clear * - ℎ161 ℎ162 ℎ243 ℎ257
    grind (splits := 10000) (ematch := 0) only
  have ℎ259 : (p 150 ≤ p 84 ∨ p 179 ≤ p 48 ∨ p 48 ≤ p 155) := by
    clear * - ℎ108 ℎ109 ℎ110 ℎ111 ℎ112 ℎ113 ℎ114 ℎ115 ℎ116 ℎ117 ℎ160
    grind (splits := 10000) (ematch := 0) only
  have ℎ260 : p 48 ≤ p 155 := by
    clear * - ℎ90 ℎ91 ℎ92 ℎ93 ℎ94 ℎ95 ℎ96 ℎ97 ℎ98 ℎ99 ℎ100 ℎ101 ℎ102 ℎ103 ℎ104 ℎ105 ℎ108 ℎ109 ℎ110 ℎ111 ℎ112 ℎ113 ℎ114 ℎ115 ℎ116 ℎ117 ℎ160 ℎ221 ℎ258 ℎ259
    grind (splits := 10000) (ematch := 0) only
  have ℎ261 : (p 51 < p 155 ∨ p 57 < p 155) := by
    clear * - ℎ96 ℎ97 ℎ98 ℎ99 ℎ220 ℎ260
    grind (splits := 10000) (ematch := 0) only
  have ℎ262 : (p 155 ≤ p 57 ∨ p 57 ≤ p 181) := by
    clear * - ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ179 ℎ256
    grind (splits := 10000) (ematch := 0) only
  have ℎ263 : p 181 < p 57 := by
    clear * - ℎ92 ℎ93 ℎ94 ℎ95 ℎ96 ℎ97 ℎ98 ℎ99 ℎ100 ℎ101 ℎ102 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ224
    grind (splits := 10000) (ematch := 0) only
  have ℎ264 : p 66 < p 179 := by
    clear * - ℎ125 ℎ126 ℎ127 ℎ128 ℎ129 ℎ130 ℎ131 ℎ132 ℎ133 ℎ134 ℎ135 ℎ136 ℎ137 ℎ138 ℎ139 ℎ140 ℎ232
    grind (splits := 10000) (ematch := 0) only
  have ℎ265 : (p 143 ≤ p 91 ∨ p 91 ≤ p 154 ∨ p 153 ≤ p 51) := by
    clear * - ℎ95 ℎ114 ℎ115
    grind (splits := 10000) (ematch := 0) only
  have ℎ266 : (p 45 < p 142 ∨ p 47 < p 142 ∨ p 142 < p 38 ∨ p 90 ≤ p 143 ∨ p 39 ≤ p 175 ∨ p 174 ≤ p 90) := by
    clear * - ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ93 ℎ94 ℎ152 ℎ153 ℎ209
    grind (splits := 10000) (ematch := 0) only
  have ℎ267 : (p 90 ≤ p 143 ∨ p 142 < p 38 ∨ p 47 < p 142 ∨ p 39 ≤ p 175 ∨ p 174 ≤ p 90) := by
    clear * - ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ93 ℎ94 ℎ152 ℎ153 ℎ266
    grind (splits := 10000) (ematch := 0) only
  have ℎ268 : (p 174 ≤ p 90 ∨ p 1 ≤ p 155 ∨ p 113 ≤ p 1 ∨ p 153 ≤ p 51 ∨ p 93 < p 143 ∨ p 143 < p 84 ∨ ¬((p 143 ≤ p 85 ∨ p 86 ≤ p 143)) ∨ ¬((p 143 ≤ p 87 ∨ p 88 ≤ p 143)) ∨ p 47 < p 142 ∨ p 39 ≤ p 175 ∨ p 142 < p 38 ∨ p 114 < p 84 ∨ ¬((p 114 ≤ p 85 ∨ p 86 ≤ p 114)) ∨ ¬((p 114 ≤ p 87 ∨ p 88 ≤ p 114)) ∨ p 93 < p 114 ∨ p 11 ≤ p 175 ∨ p 113 ≤ p 11) := by
    clear * - ℎ39 ℎ40 ℎ116 ℎ117 ℎ152 ℎ153 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ236 ℎ238 ℎ244 ℎ265 ℎ267
    grind (splits := 10000) (ematch := 0) only
  have ℎ269 : (p 89 ≤ p 174 ∨ p 173 ≤ p 69 ∨ p 67 ≤ p 186) := by
    clear * - ℎ127 ℎ128 ℎ129 ℎ130 ℎ150 ℎ151 ℎ171
    grind (splits := 10000) (ematch := 0) only
  have ℎ270 : (p 85 ≤ p 174 ∨ p 67 ≤ p 184 ∨ p 173 ≤ p 69) := by
    clear * - ℎ127 ℎ128 ℎ129 ℎ130 ℎ150 ℎ151 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167
    grind (splits := 10000) (ematch := 0) only
  have ℎ271 : (p 67 ≤ p 186 ∨ p 173 ≤ p 69 ∨ ¬((p 174 ≤ p 90 ∨ p 91 ≤ p 174)) ∨ ¬((p 174 ≤ p 92 ∨ p 93 ≤ p 174))) := by
    clear * - ℎ127 ℎ128 ℎ129 ℎ130 ℎ150 ℎ151 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ247 ℎ269 ℎ270
    grind (splits := 10000) (ematch := 0) only
  have ℎ272 : (p 90 < p 174 ∨ p 173 ≤ p 69 ∨ p 67 ≤ p 186) := by
    clear * - ℎ173 ℎ174 ℎ175 ℎ176 ℎ271
    grind (splits := 10000) (ematch := 0) only
  have ℎ273 : (p 186 ≤ p 74 ∨ p 105 < p 66 ∨ p 75 < p 105 ∨ ¬((p 105 ≤ p 67 ∨ p 68 ≤ p 105)) ∨ p 104 ≤ p 1 ∨ p 1 ≤ p 155 ∨ p 153 ≤ p 51 ∨ p 49 ≤ p 186) := by
    clear * - ℎ21 ℎ22 ℎ92 ℎ93 ℎ94 ℎ95 ℎ114 ℎ115 ℎ116 ℎ117 ℎ133 ℎ134 ℎ135 ℎ136 ℎ137 ℎ138 ℎ139 ℎ140 ℎ225
    grind (splits := 10000) (ematch := 0) only
  have ℎ274 : (p 113 ≤ p 9 ∨ p 4 ≤ p 124 ∨ p 124 ≤ p 23) := by
    clear * - ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ16 ℎ17 ℎ39 ℎ40 ℎ41
    grind (splits := 10000) (ematch := 0) only
  have ℎ275 : (p 10 ≤ p 113 ∨ p 21 ≤ p 179 ∨ p 159 ≤ p 10 ∨ p 179 ≤ p 66) := by
    clear * - ℎ38 ℎ124
    grind (splits := 10000) (ematch := 0) only
  have ℎ276 : (p 179 ≤ p 20 ∨ p 121 ≤ p 92 ∨ p 20 ≤ p 124) := by
    clear * - ℎ54 ℎ55 ℎ56 ℎ57 ℎ58 ℎ59 ℎ160 ℎ161 ℎ162 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176
    grind (splits := 10000) (ematch := 0) only
  have ℎ277 : (p 20 ≤ p 124 ∨ p 179 ≤ p 20) := by
    clear * - ℎ54 ℎ55 ℎ56 ℎ57 ℎ58 ℎ59 ℎ160 ℎ240 ℎ276
    grind (splits := 10000) (ematch := 0) only
  have ℎ278 : p 129 < p 93 := by
    clear * - ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176 ℎ177 ℎ178 ℎ242
    grind (splits := 10000) (ematch := 0) only
  have ℎ279 : (p 124 ≤ p 23 ∨ p 21 ≤ p 181) := by
    clear * - ℎ38 ℎ39 ℎ40 ℎ41 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ179 ℎ278
    grind (splits := 10000) (ematch := 0) only
  have ℎ280 : (p 124 ≤ p 25 ∨ p 21 ≤ p 181) := by
    clear * - ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ179 ℎ278
    grind (splits := 10000) (ematch := 0) only
  have ℎ281 : p 21 ≤ p 181 := by
    clear * - ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ52 ℎ53 ℎ160 ℎ161 ℎ162 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176 ℎ177 ℎ178 ℎ179 ℎ201 ℎ203 ℎ277 ℎ279 ℎ280
    grind (splits := 10000) (ematch := 0) only
  have ℎ282 : (p 115 ≤ p 13 ∨ p 105 ≤ p 75) := by
    clear * - ℎ23 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ206 ℎ255 ℎ281
    grind (splits := 10000) (ematch := 0) only
  have ℎ283 : p 20 < p 179 := by
    clear * - ℎ36 ℎ37 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ203
    grind (splits := 10000) (ematch := 0) only
  have ℎ284 : (p 179 ≤ p 28 ∨ p 29 < p 124 ∨ p 121 ≤ p 84) := by
    clear * - ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ54 ℎ55 ℎ56 ℎ57 ℎ58 ℎ59 ℎ160 ℎ201 ℎ277 ℎ283
    grind (splits := 10000) (ematch := 0) only
  have ℎ285 : (p 85 ≤ p 121 ∨ p 121 ≤ p 92) := by
    clear * - ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176
    grind (splits := 10000) (ematch := 0) only
  have ℎ286 : p 84 < p 121 := by
    clear * - ℎ161 ℎ162 ℎ240 ℎ285
    grind (splits := 10000) (ematch := 0) only
  have ℎ287 : (p 29 ≤ p 181 ∨ p 93 ≤ p 129 ∨ p 181 ≤ p 56 ∨ p 147 ≤ p 93 ∨ p 124 ≤ p 29) := by
    clear * - ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ103 ℎ104 ℎ105
    grind (splits := 10000) (ematch := 0) only
  have ℎ288 : (p 124 ≤ p 29 ∨ p 93 ≤ p 129 ∨ p 181 ≤ p 56 ∨ p 147 ≤ p 93) := by
    clear * - ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ52 ℎ53 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ103 ℎ104 ℎ105 ℎ206 ℎ287
    grind (splits := 10000) (ematch := 0) only
  have ℎ289 : (p 11 ≤ p 173 ∨ p 173 ≤ p 18) := by
    clear * - ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33
    grind (splits := 10000) (ematch := 0) only
  have ℎ290 : (p 14 ≤ p 119 ∨ p 119 < p 16) := by
    clear * - ℎ26 ℎ27 ℎ28 ℎ29
    grind (splits := 10000) (ematch := 0) only
  have ℎ291 : (p 16 ≤ p 119 ∨ p 119 < p 18) := by
    clear * - ℎ30 ℎ31 ℎ32 ℎ33
    grind (splits := 10000) (ematch := 0) only
  have ℎ292 : (p 119 ≤ p 19 ∨ p 19 ≤ p 161) := by
    clear * - ℎ51 ℎ143 ℎ206 ℎ255 ℎ281
    grind (splits := 10000) (ematch := 0) only
  have ℎ293 : (p 113 < p 14 ∨ ¬((p 113 ≤ p 17 ∨ p 18 ≤ p 113)) ∨ ¬((p 113 ≤ p 15 ∨ p 16 ≤ p 113)) ∨ p 19 < p 113) := by
    clear * - ℎ18 ℎ19 ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ191
    grind (splits := 10000) (ematch := 0) only
  have ℎ294 : (p 10 ≤ p 119 ∨ p 21 ≤ p 184) := by
    clear * - ℎ18 ℎ19 ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ34 ℎ35 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ124 ℎ160 ℎ161 ℎ162 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ195 ℎ264 ℎ293
    grind (splits := 10000) (ematch := 0) only
  have ℎ295 : (p 159 ≤ p 38 ∨ p 0 ≤ p 113 ∨ p 179 ≤ p 66 ∨ p 21 ≤ p 179 ∨ p 130 ≤ p 0) := by
    clear * - ℎ38 ℎ70 ℎ124
    grind (splits := 10000) (ematch := 0) only
  have ℎ296 : (p 179 ≤ p 66 ∨ p 21 ≤ p 179 ∨ p 130 ≤ p 0 ∨ p 0 ≤ p 113) := by
    clear * - ℎ38 ℎ70 ℎ71 ℎ72 ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ124 ℎ211 ℎ295
    grind (splits := 10000) (ematch := 0) only
  have ℎ297 : p 0 < p 130 := by
    clear * - ℎ0 ℎ1 ℎ2 ℎ3 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ185
    grind (splits := 10000) (ematch := 0) only
  have ℎ298 : p 181 < p 29 := by
    clear * - ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ52 ℎ53 ℎ206
    grind (splits := 10000) (ematch := 0) only
  have ℎ299 : (p 124 ≤ p 23 ∨ p 9 < p 124 ∨ p 20 ≤ p 101) := by
    clear * - ℎ0 ℎ1 ℎ2 ℎ3 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ36 ℎ37 ℎ38 ℎ39 ℎ40 ℎ41 ℎ184
    grind (splits := 10000) (ematch := 0) only
  have ℎ300 : p 161 < p 47 := by
    clear * - ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ87 ℎ88 ℎ214
    grind (splits := 10000) (ematch := 0) only
  have ℎ301 : (p 124 ≤ p 9 ∨ p 9 ≤ p 132 ∨ p 147 ≤ p 93 ∨ p 75 ≤ p 181 ∨ p 181 ≤ p 56) := by
    clear * - ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ89 ℎ103 ℎ104 ℎ105 ℎ143 ℎ278 ℎ300
    grind (splits := 10000) (ematch := 0) only
  have ℎ302 : p 132 < p 9 := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ16 ℎ17 ℎ186
    grind (splits := 10000) (ematch := 0) only
  have ℎ303 : (p 23 < p 124 ∨ p 29 < p 124) := by
    clear * - ℎ42 ℎ43 ℎ44 ℎ45 ℎ201 ℎ277 ℎ283
    grind (splits := 10000) (ematch := 0) only
  have ℎ304 : (p 186 ≤ p 56 ∨ p 147 ≤ p 93) := by
    clear * - ℎ103 ℎ104 ℎ105 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176 ℎ177 ℎ178
    grind (splits := 10000) (ematch := 0) only
  have ℎ305 : (p 119 < p 18 ∨ p 181 ≤ p 56 ∨ p 147 ≤ p 93 ∨ ¬((p 113 ≤ p 3 ∨ p 4 ≤ p 113)) ∨ ¬((p 113 ≤ p 7 ∨ p 8 ≤ p 113)) ∨ ¬((p 113 ≤ p 5 ∨ p 6 ≤ p 113)) ∨ p 101 ≤ p 19) := by
    clear * - ℎ15 ℎ16 ℎ17 ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ92 ℎ93 ℎ94 ℎ95 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ143 ℎ168 ℎ169 ℎ170 ℎ171 ℎ182 ℎ188 ℎ194 ℎ196 ℎ200 ℎ203 ℎ204 ℎ206 ℎ223 ℎ255 ℎ256 ℎ261 ℎ264 ℎ278 ℎ281 ℎ284 ℎ286 ℎ288 ℎ290 ℎ291 ℎ292 ℎ294 ℎ296 ℎ297 ℎ298 ℎ299 ℎ301 ℎ302 ℎ303 ℎ304
    grind (splits := 10000) (ematch := 0) only
  have ℎ306 : (p 113 ≤ p 17 ∨ p 19 < p 115 ∨ p 115 < p 10) := by
    clear * - ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ39 ℎ40 ℎ41 ℎ42 ℎ192
    grind (splits := 10000) (ematch := 0) only
  have ℎ307 : (p 96 ≤ p 39 ∨ p 19 < p 115 ∨ p 113 ≤ p 3 ∨ p 175 ≤ p 18 ∨ p 39 ≤ p 175) := by
    clear * - ℎ5 ℎ18 ℎ19 ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ39 ℎ40 ℎ41 ℎ42 ℎ306
    grind (splits := 10000) (ematch := 0) only
  have ℎ308 : (p 39 < p 96 ∨ p 96 < p 38) := by
    clear * - ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ87 ℎ88 ℎ207
    grind (splits := 10000) (ematch := 0) only
  have ℎ309 : (p 96 ≤ p 41 ∨ p 113 ≤ p 3 ∨ p 39 ≤ p 175 ∨ p 175 ≤ p 18 ∨ p 18 ≤ p 119) := by
    clear * - ℎ5 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ73 ℎ74 ℎ75 ℎ76
    grind (splits := 10000) (ematch := 0) only
  have ℎ310 : (p 18 ≤ p 119 ∨ p 113 ≤ p 3 ∨ p 39 ≤ p 175 ∨ p 175 ≤ p 18 ∨ p 96 < p 38) := by
    clear * - ℎ5 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ87 ℎ88 ℎ207 ℎ309
    grind (splits := 10000) (ematch := 0) only
  have ℎ311 : (p 113 ≤ p 3 ∨ p 175 ≤ p 18 ∨ p 39 ≤ p 175 ∨ p 96 < p 38) := by
    clear * - ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ143 ℎ196 ℎ206 ℎ255 ℎ281 ℎ307 ℎ308 ℎ310
    grind (splits := 10000) (ematch := 0) only
  have ℎ312 : (p 178 < p 93 ∨ p 155 ≤ p 51 ∨ p 49 ≤ p 186) := by
    clear * - ℎ92 ℎ93 ℎ94 ℎ95 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ248 ℎ256
    grind (splits := 10000) (ematch := 0) only
  have ℎ313 : (p 175 ≤ p 46 ∨ p 47 < p 148 ∨ p 147 ≤ p 93) := by
    clear * - ℎ71 ℎ72 ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ154 ℎ155 ℎ156 ℎ157 ℎ158 ℎ159 ℎ223 ℎ250 ℎ256 ℎ261 ℎ304 ℎ312
    grind (splits := 10000) (ematch := 0) only
  have ℎ314 : (p 100 ≤ p 43 ∨ p 39 < p 100) := by
    clear * - ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80
    grind (splits := 10000) (ematch := 0) only
  have ℎ315 : (p 100 ≤ p 41 ∨ p 39 < p 100) := by
    clear * - ℎ73 ℎ74 ℎ75 ℎ76
    grind (splits := 10000) (ematch := 0) only
  have ℎ316 : (p 39 < p 100 ∨ p 100 < p 38) := by
    clear * - ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ87 ℎ88 ℎ208 ℎ314 ℎ315
    grind (splits := 10000) (ematch := 0) only
  have ℎ317 : (p 38 ≤ p 100 ∨ p 159 ≤ p 38 ∨ p 9 < p 124) := by
    clear * - ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ54 ℎ55 ℎ56 ℎ57 ℎ58 ℎ59 ℎ70 ℎ124 ℎ160 ℎ184 ℎ264 ℎ286 ℎ297
    grind (splits := 10000) (ematch := 0) only
  have ℎ318 : p 84 < p 170 := by
    clear * - ℎ161 ℎ162 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176 ℎ246
    grind (splits := 10000) (ematch := 0) only
  have ℎ319 : (p 101 ≤ p 19 ∨ p 147 ≤ p 93 ∨ p 153 ≤ p 8 ∨ p 19 ≤ p 161 ∨ p 181 ≤ p 56) := by
    clear * - ℎ15 ℎ103 ℎ104 ℎ105 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ143 ℎ255 ℎ256
    grind (splits := 10000) (ematch := 0) only
  have ℎ320 : (p 10 ≤ p 101 ∨ p 101 ≤ p 11) := by
    clear * - ℎ18 ℎ19
    grind (splits := 10000) (ematch := 0) only
  have ℎ321 : (p 100 ≤ p 39 ∨ p 19 < p 101 ∨ p 175 ≤ p 18 ∨ p 39 ≤ p 175) := by
    clear * - ℎ13 ℎ14 ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ190 ℎ320
    grind (splits := 10000) (ematch := 0) only
  have ℎ322 : (p 153 ≤ p 8 ∨ p 147 ≤ p 93 ∨ p 181 ≤ p 56 ∨ p 175 ≤ p 18) := by
    clear * - ℎ13 ℎ14 ℎ15 ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ103 ℎ104 ℎ105 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ143 ℎ144 ℎ145 ℎ146 ℎ147 ℎ148 ℎ149 ℎ150 ℎ151 ℎ152 ℎ153 ℎ160 ℎ196 ℎ211 ℎ216 ℎ254 ℎ255 ℎ256 ℎ264 ℎ301 ℎ302 ℎ313 ℎ316 ℎ317 ℎ318 ℎ319 ℎ321
    grind (splits := 10000) (ematch := 0) only
  have ℎ323 : (p 126 < p 26 ∨ p 29 < p 126) := by
    clear * - ℎ44 ℎ45 ℎ46 ℎ47 ℎ60 ℎ61 ℎ62 ℎ63 ℎ202 ℎ277 ℎ283
    grind (splits := 10000) (ematch := 0) only
  have ℎ324 : (p 126 ≤ p 29 ∨ p 181 ≤ p 56 ∨ p 147 ≤ p 93) := by
    clear * - ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ103 ℎ104 ℎ105 ℎ278 ℎ298
    grind (splits := 10000) (ematch := 0) only
  have ℎ325 : (p 175 ≤ p 18 ∨ p 147 ≤ p 93 ∨ p 181 ≤ p 56) := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ48 ℎ49 ℎ50 ℎ54 ℎ55 ℎ56 ℎ57 ℎ58 ℎ59 ℎ60 ℎ61 ℎ62 ℎ63 ℎ70 ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ108 ℎ109 ℎ110 ℎ111 ℎ112 ℎ113 ℎ124 ℎ144 ℎ145 ℎ146 ℎ147 ℎ148 ℎ149 ℎ150 ℎ151 ℎ152 ℎ153 ℎ160 ℎ184 ℎ187 ℎ211 ℎ216 ℎ254 ℎ255 ℎ258 ℎ264 ℎ286 ℎ297 ℎ301 ℎ302 ℎ305 ℎ308 ℎ311 ℎ313 ℎ316 ℎ317 ℎ318 ℎ321 ℎ322 ℎ323 ℎ324
    grind (splits := 10000) (ematch := 0) only
  have ℎ326 : (p 105 ≤ p 75 ∨ p 1 ≤ p 155 ∨ p 181 ≤ p 56 ∨ p 147 ≤ p 93) := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ34 ℎ35 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ92 ℎ93 ℎ94 ℎ95 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ150 ℎ151 ℎ152 ℎ153 ℎ154 ℎ155 ℎ156 ℎ157 ℎ158 ℎ159 ℎ160 ℎ161 ℎ162 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ182 ℎ192 ℎ195 ℎ197 ℎ198 ℎ203 ℎ204 ℎ206 ℎ223 ℎ255 ℎ256 ℎ261 ℎ264 ℎ274 ℎ275 ℎ278 ℎ281 ℎ282 ℎ284 ℎ286 ℎ288 ℎ289 ℎ296 ℎ297 ℎ303 ℎ304 ℎ312 ℎ323 ℎ324 ℎ325
    grind (splits := 10000) (ematch := 0) only
  have ℎ327 : (p 170 ≤ p 84 ∨ p 66 ≤ p 105 ∨ p 11 ≤ p 173) := by
    clear * - ℎ20 ℎ21 ℎ22 ℎ144 ℎ145 ℎ146 ℎ147 ℎ148 ℎ149 ℎ160 ℎ264
    grind (splits := 10000) (ematch := 0) only
  have ℎ328 : (p 69 < p 173 ∨ p 75 < p 173) := by
    clear * - ℎ131 ℎ132 ℎ133 ℎ134 ℎ144 ℎ145 ℎ146 ℎ147 ℎ148 ℎ149 ℎ160 ℎ227 ℎ264 ℎ318
    grind (splits := 10000) (ematch := 0) only
  have ℎ329 : (p 1 < p 104 ∨ p 104 < p 0) := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ16 ℎ17 ℎ180
    grind (splits := 10000) (ematch := 0) only
  have ℎ330 : (p 51 < p 153 ∨ p 153 < p 48 ∨ p 57 < p 153) := by
    clear * - ℎ96 ℎ97 ℎ98 ℎ99 ℎ219
    grind (splits := 10000) (ematch := 0) only
  have ℎ331 : (p 48 ≤ p 153 ∨ p 179 ≤ p 48) := by
    clear * - ℎ108 ℎ109 ℎ110 ℎ111 ℎ112 ℎ113 ℎ160 ℎ258
    grind (splits := 10000) (ematch := 0) only
  have ℎ332 : (p 90 ≤ p 147 ∨ p 147 ≤ p 93) := by
    clear * - ℎ173 ℎ174 ℎ175 ℎ176 ℎ177 ℎ178
    grind (splits := 10000) (ematch := 0) only
  have ℎ333 : (p 1 < p 113 ∨ p 113 < p 0) := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ16 ℎ17 ℎ182
    grind (splits := 10000) (ematch := 0) only
  have ℎ334 : (p 1 ≤ p 155 ∨ p 181 ≤ p 56 ∨ p 147 ≤ p 93) := by
    clear * - ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ34 ℎ35 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ70 ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ92 ℎ93 ℎ94 ℎ95 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ129 ℎ130 ℎ143 ℎ144 ℎ145 ℎ146 ℎ147 ℎ148 ℎ149 ℎ150 ℎ151 ℎ152 ℎ153 ℎ154 ℎ155 ℎ156 ℎ157 ℎ158 ℎ159 ℎ160 ℎ161 ℎ162 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ179 ℎ191 ℎ195 ℎ198 ℎ203 ℎ204 ℎ211 ℎ216 ℎ221 ℎ223 ℎ234 ℎ254 ℎ255 ℎ256 ℎ261 ℎ264 ℎ268 ℎ272 ℎ273 ℎ275 ℎ278 ℎ284 ℎ286 ℎ288 ℎ296 ℎ297 ℎ300 ℎ303 ℎ304 ℎ312 ℎ313 ℎ318 ℎ325 ℎ326 ℎ327 ℎ328 ℎ329 ℎ330 ℎ331 ℎ332 ℎ333
    grind (splits := 10000) (ematch := 0) only
  have ℎ335 : p 124 ≤ p 29 := by
    clear * - ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ179 ℎ278 ℎ298
    grind (splits := 10000) (ematch := 0) only
  have ℎ336 : (p 113 ≤ p 17 ∨ p 19 < p 115) := by
    clear * - ℎ18 ℎ19 ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ39 ℎ40 ℎ41 ℎ42 ℎ306
    grind (splits := 10000) (ematch := 0) only
  have ℎ337 : p 161 < p 19 := by
    clear * - ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ34 ℎ35 ℎ196
    grind (splits := 10000) (ematch := 0) only
  have ℎ338 : (p 110 < p 4 ∨ p 9 < p 110 ∨ p 110 < p 8) := by
    clear * - ℎ0 ℎ1 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ32 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ143 ℎ181 ℎ203 ℎ206 ℎ255 ℎ264 ℎ281 ℎ284 ℎ286 ℎ296 ℎ297 ℎ333 ℎ335 ℎ336 ℎ337
    grind (splits := 10000) (ematch := 0) only
  have ℎ339 : (p 110 < p 8 ∨ p 9 < p 110) := by
    clear * - ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ338
    grind (splits := 10000) (ematch := 0) only
  have ℎ340 : (p 11 ≤ p 161 ∨ p 75 < p 105) := by
    clear * - ℎ20 ℎ21 ℎ22 ℎ143
    grind (splits := 10000) (ematch := 0) only
  have ℎ341 : (p 13 < p 115 ∨ p 115 < p 10 ∨ p 19 < p 115) := by
    clear * - ℎ24 ℎ25 ℎ26 ℎ27 ℎ192
    grind (splits := 10000) (ematch := 0) only
  have ℎ342 : (p 66 ≤ p 109 ∨ p 16 ≤ p 117) := by
    clear * - ℎ30 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ203 ℎ264 ℎ284 ℎ286 ℎ335
    grind (splits := 10000) (ematch := 0) only
  have ℎ343 : (p 109 ≤ p 75 ∨ p 119 ≤ p 17) := by
    clear * - ℎ31 ℎ51 ℎ206 ℎ255 ℎ281
    grind (splits := 10000) (ematch := 0) only
  have ℎ344 : (p 11 ≤ p 161 ∨ p 75 < p 109) := by
    clear * - ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ143
    grind (splits := 10000) (ematch := 0) only
  have ℎ345 : p 117 ≤ p 19 := by
    clear * - ℎ32 ℎ33 ℎ34 ℎ35 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ143 ℎ196 ℎ206 ℎ255 ℎ281 ℎ343 ℎ344
    grind (splits := 10000) (ematch := 0) only
  have ℎ346 : (p 117 < p 16 ∨ p 117 < p 10) := by
    clear * - ℎ26 ℎ27 ℎ28 ℎ29 ℎ193 ℎ345
    grind (splits := 10000) (ematch := 0) only
  have ℎ347 : p 117 < p 16 := by
    clear * - ℎ18 ℎ19 ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ346
    grind (splits := 10000) (ematch := 0) only
  have ℎ348 : (p 72 < p 143 ∨ ¬((p 143 ≤ p 66 ∨ p 67 ≤ p 143)) ∨ ¬((p 143 ≤ p 70 ∨ p 71 ≤ p 143)) ∨ ¬((p 143 ≤ p 68 ∨ p 69 ≤ p 143))) := by
    clear * - ℎ137 ℎ138 ℎ139 ℎ140 ℎ230
    grind (splits := 10000) (ematch := 0) only
  have ℎ349 : p 178 < p 93 := by
    clear * - ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176 ℎ177 ℎ178 ℎ248
    grind (splits := 10000) (ematch := 0) only
  have ℎ350 : (p 142 < p 40 ∨ p 39 < p 142) := by
    clear * - ℎ73 ℎ74
    grind (splits := 10000) (ematch := 0) only
  have ℎ351 : (p 39 < p 142 ∨ p 142 < p 38) := by
    clear * - ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ87 ℎ88 ℎ92 ℎ93 ℎ94 ℎ95 ℎ96 ℎ97 ℎ98 ℎ99 ℎ100 ℎ101 ℎ102 ℎ103 ℎ104 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ179 ℎ209 ℎ224 ℎ252 ℎ254 ℎ255 ℎ256 ℎ261 ℎ262 ℎ263 ℎ350
    grind (splits := 10000) (ematch := 0) only
  have ℎ352 : (p 124 < p 6 ∨ p 9 < p 124) := by
    clear * - ℎ0 ℎ1 ℎ2 ℎ3 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ184
    grind (splits := 10000) (ematch := 0) only
  have ℎ353 : p 126 ≤ p 29 := by
    clear * - ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ179 ℎ278 ℎ298
    grind (splits := 10000) (ematch := 0) only
  have ℎ354 : (p 11 < p 113 ∨ p 113 < p 10 ∨ ¬((p 113 ≤ p 17 ∨ p 18 ≤ p 113)) ∨ ¬((p 113 ≤ p 15 ∨ p 16 ≤ p 113))) := by
    clear * - ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ34 ℎ35 ℎ191
    grind (splits := 10000) (ematch := 0) only
  have ℎ355 : (p 11 < p 113 ∨ p 113 < p 10) := by
    clear * - ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ143 ℎ206 ℎ255 ℎ281 ℎ336 ℎ337 ℎ354
    grind (splits := 10000) (ematch := 0) only
  have ℎ356 : (p 11 ≤ p 175 ∨ p 46 ≤ p 100 ∨ p 175 ≤ p 46) := by
    clear * - ℎ12 ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ39 ℎ40 ℎ41 ℎ48 ℎ49 ℎ50 ℎ51 ℎ60 ℎ61 ℎ62 ℎ63 ℎ89 ℎ124 ℎ143 ℎ144 ℎ145 ℎ146 ℎ147 ℎ148 ℎ149 ℎ150 ℎ151 ℎ152 ℎ153 ℎ160 ℎ195 ℎ203 ℎ206 ℎ255 ℎ264 ℎ275 ℎ281 ℎ284 ℎ286 ℎ300 ℎ302 ℎ303 ℎ318 ℎ323 ℎ335 ℎ352 ℎ353 ℎ355
    grind (splits := 10000) (ematch := 0) only
  have ℎ357 : (p 38 ≤ p 100 ∨ p 100 ≤ p 43) := by
    clear * - ℎ71 ℎ72 ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80
    grind (splits := 10000) (ematch := 0) only
  have ℎ358 : (p 100 < p 46 ∨ p 47 < p 100) := by
    clear * - ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ208 ℎ357
    grind (splits := 10000) (ematch := 0) only
  have ℎ359 : p 119 ≤ p 9 := by
    clear * - ℎ51 ℎ89 ℎ143 ℎ206 ℎ255 ℎ281 ℎ300 ℎ302
    grind (splits := 10000) (ematch := 0) only
  have ℎ360 : p 119 < p 8 := by
    clear * - ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ183 ℎ203 ℎ264 ℎ284 ℎ286 ℎ296 ℎ297 ℎ335 ℎ359
    grind (splits := 10000) (ematch := 0) only
  have ℎ361 : p 155 < p 54 := by
    clear * - ℎ98 ℎ99 ℎ100 ℎ101 ℎ220 ℎ260 ℎ262 ℎ263
    grind (splits := 10000) (ematch := 0) only
  have ℎ362 : (p 1 ≤ p 153 ∨ p 143 ≤ p 72 ∨ p 104 ≤ p 1 ∨ p 153 ≤ p 51 ∨ p 72 ≤ p 105) := by
    clear * - ℎ21 ℎ22 ℎ95
    grind (splits := 10000) (ematch := 0) only
  have ℎ363 : (p 26 ≤ p 126 ∨ ¬((p 125 ≤ p 86 ∨ p 87 ≤ p 125)) ∨ ¬((p 125 ≤ p 84 ∨ p 85 ≤ p 125)) ∨ ¬((p 125 ≤ p 88 ∨ p 89 ≤ p 125)) ∨ p 90 ≤ p 118) := by
    clear * - ℎ48 ℎ62 ℎ63 ℎ173 ℎ174 ℎ175 ℎ176 ℎ241
    grind (splits := 10000) (ematch := 0) only
  have ℎ364 : (p 87 < p 118 ∨ p 93 < p 118 ∨ p 114 < p 84) := by
    clear * - ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ54 ℎ55 ℎ56 ℎ57 ℎ58 ℎ59 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ204 ℎ236 ℎ237 ℎ278 ℎ286 ℎ303 ℎ323 ℎ335 ℎ353 ℎ363
    grind (splits := 10000) (ematch := 0) only
  have ℎ365 : (p 11 ≤ p 173 ∨ p 113 ≤ p 11 ∨ p 84 ≤ p 114) := by
    clear * - ℎ39 ℎ40 ℎ144 ℎ145 ℎ146 ℎ147 ℎ148 ℎ149 ℎ318
    grind (splits := 10000) (ematch := 0) only
  have ℎ366 : p 175 < p 72 := by
    clear * - ℎ133 ℎ134 ℎ135 ℎ136 ℎ144 ℎ145 ℎ146 ℎ147 ℎ148 ℎ149 ℎ150 ℎ151 ℎ152 ℎ153 ℎ154 ℎ155 ℎ156 ℎ157 ℎ158 ℎ159 ℎ160 ℎ179 ℎ228 ℎ255 ℎ264 ℎ318 ℎ349
    grind (splits := 10000) (ematch := 0) only
  have ℎ367 : (p 109 ≤ p 67 ∨ p 184 ≤ p 56 ∨ p 54 ≤ p 155 ∨ p 153 ≤ p 8 ∨ p 8 ≤ p 110 ∨ ¬((p 174 ≤ p 84 ∨ p 85 ≤ p 174)) ∨ ¬((p 174 ≤ p 86 ∨ p 87 ≤ p 174))) := by
    clear * - ℎ31 ℎ32 ℎ102 ℎ103 ℎ104 ℎ105 ℎ114 ℎ115 ℎ116 ℎ117 ℎ137 ℎ138 ℎ139 ℎ140 ℎ152 ℎ153 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176 ℎ233 ℎ234 ℎ247 ℎ366
    grind (splits := 10000) (ematch := 0) only
  have ℎ368 : (p 85 < p 118 ∨ p 93 < p 118 ∨ ¬((p 118 ≤ p 89 ∨ p 90 ≤ p 118)) ∨ p 118 < p 84 ∨ ¬((p 118 ≤ p 91 ∨ p 92 ≤ p 118))) := by
    clear * - ℎ163 ℎ164 ℎ165 ℎ166 ℎ237
    grind (splits := 10000) (ematch := 0) only
  have ℎ369 : (p 101 ≤ p 17 ∨ p 153 ≤ p 8 ∨ p 147 ≤ p 93 ∨ p 109 ≤ p 75) := by
    clear * - ℎ15 ℎ31 ℎ92 ℎ93 ℎ94 ℎ95 ℎ103 ℎ104 ℎ105 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ179 ℎ224 ℎ255 ℎ256 ℎ261 ℎ262 ℎ263
    grind (splits := 10000) (ematch := 0) only
  have ℎ370 : (p 90 ≤ p 147 ∨ p 154 ≤ p 90 ∨ p 54 ≤ p 155) := by
    clear * - ℎ102 ℎ116 ℎ117
    grind (splits := 10000) (ematch := 0) only
  have ℎ371 : (p 91 ≤ p 154 ∨ p 154 ≤ p 92) := by
    clear * - ℎ175 ℎ176
    grind (splits := 10000) (ematch := 0) only
  have ℎ372 : (p 154 ≤ p 92 ∨ p 54 ≤ p 155 ∨ p 93 < p 147 ∨ p 147 < p 84 ∨ ¬((p 147 ≤ p 85 ∨ p 86 ≤ p 147)) ∨ ¬((p 147 ≤ p 87 ∨ p 88 ≤ p 147))) := by
    clear * - ℎ102 ℎ116 ℎ117 ℎ173 ℎ174 ℎ239 ℎ370 ℎ371
    grind (splits := 10000) (ematch := 0) only
  have ℎ373 : (p 118 ≤ p 91 ∨ p 153 ≤ p 8 ∨ p 91 ≤ p 154 ∨ p 8 ≤ p 119) := by
    clear * - ℎ49 ℎ50 ℎ114 ℎ115
    grind (splits := 10000) (ematch := 0) only
  have ℎ374 : (p 186 ≤ p 28 ∨ p 29 < p 101 ∨ ¬((p 101 ≤ p 23 ∨ p 24 ≤ p 101)) ∨ p 100 ≤ p 49 ∨ p 49 ≤ p 186) := by
    clear * - ℎ12 ℎ13 ℎ14 ℎ40 ℎ41 ℎ48 ℎ49 ℎ50 ℎ51 ℎ60 ℎ61 ℎ62 ℎ63 ℎ89 ℎ143 ℎ200 ℎ206 ℎ255 ℎ281 ℎ299 ℎ300 ℎ302 ℎ303 ℎ323 ℎ335 ℎ352 ℎ353
    grind (splits := 10000) (ematch := 0) only
  have ℎ375 : (p 186 ≤ p 56 ∨ ¬((p 154 ≤ p 86 ∨ p 87 ≤ p 154)) ∨ ¬((p 154 ≤ p 88 ∨ p 89 ≤ p 154)) ∨ ¬((p 154 ≤ p 84 ∨ p 85 ≤ p 154)) ∨ p 54 ≤ p 155) := by
    clear * - ℎ102 ℎ103 ℎ104 ℎ105 ℎ116 ℎ117 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176 ℎ244
    grind (splits := 10000) (ematch := 0) only
  have ℎ376 : (p 8 ≤ p 119 ∨ p 118 ≤ p 93 ∨ p 153 ≤ p 8) := by
    clear * - ℎ49 ℎ50 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ256
    grind (splits := 10000) (ematch := 0) only
  have ℎ377 : (p 153 ≤ p 8 ∨ p 118 ≤ p 93) := by
    clear * - ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ160 ℎ161 ℎ162 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176 ℎ177 ℎ178 ℎ183 ℎ203 ℎ256 ℎ264 ℎ296 ℎ297 ℎ359 ℎ376
    grind (splits := 10000) (ematch := 0) only
  have ℎ378 : (p 89 ≤ p 154 ∨ p 153 ≤ p 8 ∨ p 8 ≤ p 119 ∨ ¬((p 118 ≤ p 85 ∨ p 86 ≤ p 118)) ∨ ¬((p 118 ≤ p 87 ∨ p 88 ≤ p 118))) := by
    clear * - ℎ48 ℎ49 ℎ50 ℎ54 ℎ55 ℎ56 ℎ57 ℎ58 ℎ59 ℎ60 ℎ61 ℎ62 ℎ63 ℎ114 ℎ115 ℎ171 ℎ172 ℎ173 ℎ174 ℎ237 ℎ286 ℎ323 ℎ353 ℎ373 ℎ377
    grind (splits := 10000) (ematch := 0) only
  have ℎ379 : (p 88 ≤ p 118 ∨ ¬((p 125 ≤ p 86 ∨ p 87 ≤ p 125)) ∨ ¬((p 125 ≤ p 84 ∨ p 85 ≤ p 125))) := by
    clear * - ℎ48 ℎ62 ℎ63 ℎ169 ℎ170 ℎ171 ℎ172 ℎ323 ℎ353 ℎ363
    grind (splits := 10000) (ematch := 0) only
  have ℎ380 : (p 101 < p 16 ∨ p 24 ≤ p 101 ∨ p 19 < p 101) := by
    clear * - ℎ18 ℎ19 ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ44 ℎ45 ℎ46 ℎ190 ℎ320 ℎ346
    grind (splits := 10000) (ematch := 0) only
  have ℎ381 : (p 109 < p 74 ∨ p 75 < p 109 ∨ p 109 < p 66 ∨ ¬((p 109 ≤ p 67 ∨ p 68 ≤ p 109))) := by
    clear * - ℎ133 ℎ134 ℎ135 ℎ136 ℎ137 ℎ138 ℎ139 ℎ140 ℎ226
    grind (splits := 10000) (ematch := 0) only
  have ℎ382 : (p 109 < p 74 ∨ p 109 < p 66 ∨ p 75 < p 109) := by
    clear * - ℎ129 ℎ130 ℎ131 ℎ132 ℎ133 ℎ134 ℎ135 ℎ136 ℎ137 ℎ138 ℎ139 ℎ140 ℎ381
    grind (splits := 10000) (ematch := 0) only
  have ℎ383 : (p 101 ≤ p 17 ∨ p 16 ≤ p 119 ∨ p 24 ≤ p 101) := by
    clear * - ℎ30 ℎ31 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50
    grind (splits := 10000) (ematch := 0) only
  have ℎ384 : (p 12 ≤ p 119 ∨ p 119 < p 14) := by
    clear * - ℎ22 ℎ23 ℎ24 ℎ25
    grind (splits := 10000) (ematch := 0) only
  have ℎ385 : (p 119 < p 16 ∨ ¬((p 119 ≤ p 17 ∨ p 18 ≤ p 119)) ∨ p 119 < p 10) := by
    clear * - ℎ194 ℎ290 ℎ292 ℎ337 ℎ384
    grind (splits := 10000) (ematch := 0) only
  have ℎ386 : (p 109 ≤ p 75 ∨ p 155 ≤ p 8 ∨ p 110 < p 0 ∨ p 9 < p 110 ∨ p 24 ≤ p 101 ∨ p 119 < p 10) := by
    clear * - ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ31 ℎ32 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ179 ℎ181 ℎ255 ℎ256 ℎ343 ℎ383 ℎ385
    grind (splits := 10000) (ematch := 0) only
  have ℎ387 : (p 66 ≤ p 109 ∨ p 16 ≤ p 101) := by
    clear * - ℎ12 ℎ13 ℎ14 ℎ30 ℎ38 ℎ39 ℎ40 ℎ41 ℎ48 ℎ49 ℎ50 ℎ51 ℎ60 ℎ61 ℎ62 ℎ63 ℎ89 ℎ143 ℎ203 ℎ206 ℎ255 ℎ264 ℎ281 ℎ284 ℎ286 ℎ300 ℎ302 ℎ303 ℎ323 ℎ335 ℎ352 ℎ353
    grind (splits := 10000) (ematch := 0) only
  have ℎ388 : (p 100 ≤ p 53 ∨ p 49 < p 100) := by
    clear * - ℎ92 ℎ93 ℎ94 ℎ95 ℎ96 ℎ97 ℎ98 ℎ99
    grind (splits := 10000) (ematch := 0) only
  have ℎ389 : (p 49 < p 100 ∨ p 100 < p 48 ∨ p 57 < p 100 ∨ ¬((p 100 ≤ p 55 ∨ p 56 ≤ p 100))) := by
    clear * - ℎ92 ℎ93 ℎ94 ℎ95 ℎ218 ℎ388
    grind (splits := 10000) (ematch := 0) only
  have ℎ390 : (p 48 ≤ p 100 ∨ p 179 ≤ p 48) := by
    clear * - ℎ12 ℎ38 ℎ39 ℎ40 ℎ41 ℎ48 ℎ49 ℎ50 ℎ51 ℎ60 ℎ61 ℎ62 ℎ63 ℎ89 ℎ143 ℎ203 ℎ206 ℎ255 ℎ281 ℎ284 ℎ286 ℎ300 ℎ302 ℎ303 ℎ323 ℎ335 ℎ352 ℎ353
    grind (splits := 10000) (ematch := 0) only
  have ℎ391 : (p 147 < p 90 ∨ p 90 ≤ p 118 ∨ p 24 ≤ p 101 ∨ p 100 ≤ p 49) := by
    clear * - ℎ13 ℎ14 ℎ38 ℎ39 ℎ40 ℎ41 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ60 ℎ61 ℎ103 ℎ104 ℎ105 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ204 ℎ205 ℎ222 ℎ223 ℎ303 ℎ323 ℎ335 ℎ353 ℎ363
    grind (splits := 10000) (ematch := 0) only
  have ℎ392 : (p 184 ≤ p 28 ∨ p 24 ≤ p 101 ∨ p 49 ≤ p 186 ∨ p 100 < p 48 ∨ ¬((p 100 ≤ p 55 ∨ p 56 ≤ p 100))) := by
    clear * - ℎ13 ℎ14 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ92 ℎ93 ℎ94 ℎ95 ℎ96 ℎ97 ℎ98 ℎ99 ℎ100 ℎ101 ℎ102 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ168 ℎ169 ℎ170 ℎ171 ℎ218
    grind (splits := 10000) (ematch := 0) only
  have ℎ393 : (p 119 < p 18 ∨ p 119 < p 10) := by
    clear * - ℎ291 ℎ385
    grind (splits := 10000) (ematch := 0) only
  have ℎ394 : (p 109 ≤ p 73 ∨ p 67 < p 109) := by
    clear * - ℎ127 ℎ128 ℎ129 ℎ130 ℎ131 ℎ132 ℎ133 ℎ134 ℎ135 ℎ136 ℎ137 ℎ138
    grind (splits := 10000) (ematch := 0) only
  have ℎ395 : (p 67 < p 109 ∨ p 109 < p 66) := by
    clear * - ℎ127 ℎ128 ℎ129 ℎ130 ℎ131 ℎ132 ℎ133 ℎ134 ℎ135 ℎ136 ℎ137 ℎ138 ℎ139 ℎ140 ℎ141 ℎ142 ℎ226 ℎ394
    grind (splits := 10000) (ematch := 0) only
  have ℎ396 : (p 39 ≤ p 173 ∨ p 16 ≤ p 117 ∨ p 173 ≤ p 18 ∨ p 24 ≤ p 101) := by
    clear * - ℎ13 ℎ14 ℎ30 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ48 ℎ49 ℎ50 ℎ51 ℎ60 ℎ61 ℎ62 ℎ63 ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ89 ℎ124 ℎ143 ℎ203 ℎ206 ℎ211 ℎ255 ℎ264 ℎ281 ℎ284 ℎ286 ℎ300 ℎ302 ℎ316 ℎ317 ℎ323 ℎ335 ℎ353
    grind (splits := 10000) (ematch := 0) only
  have ℎ397 : (p 184 ≤ p 56 ∨ p 54 ≤ p 155 ∨ ¬((p 154 ≤ p 92 ∨ p 93 ≤ p 154)) ∨ ¬((p 154 ≤ p 90 ∨ p 91 ≤ p 154)) ∨ ¬((p 154 ≤ p 84 ∨ p 85 ≤ p 154)) ∨ p 93 < p 147 ∨ p 147 < p 84 ∨ ¬((p 147 ≤ p 91 ∨ p 92 ≤ p 147)) ∨ ¬((p 147 ≤ p 87 ∨ p 88 ≤ p 147))) := by
    clear * - ℎ102 ℎ103 ℎ104 ℎ105 ℎ116 ℎ117 ℎ168 ℎ169 ℎ170 ℎ239 ℎ244
    grind (splits := 10000) (ematch := 0) only
  have ℎ398 : (p 90 ≤ p 147 ∨ p 147 ≤ p 91) := by
    clear * - ℎ173 ℎ174
    grind (splits := 10000) (ematch := 0) only
  have ℎ399 : (p 184 ≤ p 28 ∨ p 54 ≤ p 155 ∨ p 153 ≤ p 8 ∨ p 24 ≤ p 101 ∨ p 8 ≤ p 119) := by
    clear * - ℎ0 ℎ1 ℎ2 ℎ3 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ18 ℎ19 ℎ20 ℎ21 ℎ22 ℎ23 ℎ30 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ54 ℎ55 ℎ56 ℎ57 ℎ58 ℎ59 ℎ60 ℎ61 ℎ62 ℎ63 ℎ89 ℎ92 ℎ93 ℎ94 ℎ95 ℎ102 ℎ103 ℎ104 ℎ105 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ143 ℎ150 ℎ151 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176 ℎ179 ℎ181 ℎ188 ℎ195 ℎ196 ℎ197 ℎ203 ℎ206 ℎ215 ℎ221 ℎ222 ℎ223 ℎ224 ℎ244 ℎ252 ℎ254 ℎ255 ℎ256 ℎ261 ℎ262 ℎ263 ℎ264 ℎ275 ℎ281 ℎ282 ℎ284 ℎ286 ℎ296 ℎ297 ℎ300 ℎ302 ℎ323 ℎ332 ℎ333 ℎ335 ℎ336 ℎ337 ℎ340 ℎ341 ℎ346 ℎ353 ℎ355 ℎ364 ℎ365 ℎ367 ℎ368 ℎ370 ℎ377 ℎ380 ℎ387 ℎ389 ℎ390 ℎ391 ℎ392 ℎ393 ℎ395 ℎ396 ℎ397 ℎ398
    grind (splits := 10000) (ematch := 0) only
  have ℎ400 : (p 91 ≤ p 125 ∨ p 114 ≤ p 91 ∨ p 124 ≤ p 23) := by
    clear * - ℎ41 ℎ60 ℎ61
    grind (splits := 10000) (ematch := 0) only
  have ℎ401 : (p 92 ≤ p 118 ∨ p 125 ≤ p 92 ∨ p 26 ≤ p 126) := by
    clear * - ℎ48 ℎ62 ℎ63
    grind (splits := 10000) (ematch := 0) only
  have ℎ402 : (p 24 ≤ p 101 ∨ p 54 ≤ p 155 ∨ p 153 ≤ p 8 ∨ p 8 ≤ p 119) := by
    clear * - ℎ0 ℎ1 ℎ2 ℎ3 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ30 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ54 ℎ55 ℎ56 ℎ57 ℎ58 ℎ59 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ89 ℎ92 ℎ93 ℎ94 ℎ95 ℎ96 ℎ97 ℎ98 ℎ99 ℎ100 ℎ101 ℎ102 ℎ103 ℎ104 ℎ105 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ143 ℎ150 ℎ151 ℎ152 ℎ153 ℎ154 ℎ155 ℎ156 ℎ157 ℎ158 ℎ159 ℎ161 ℎ162 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ169 ℎ170 ℎ171 ℎ179 ℎ188 ℎ195 ℎ196 ℎ198 ℎ203 ℎ204 ℎ205 ℎ206 ℎ221 ℎ223 ℎ224 ℎ234 ℎ236 ℎ237 ℎ241 ℎ244 ℎ255 ℎ256 ℎ261 ℎ262 ℎ263 ℎ264 ℎ272 ℎ275 ℎ278 ℎ281 ℎ282 ℎ284 ℎ286 ℎ296 ℎ297 ℎ300 ℎ302 ℎ303 ℎ323 ℎ325 ℎ328 ℎ333 ℎ335 ℎ336 ℎ337 ℎ340 ℎ341 ℎ349 ℎ352 ℎ353 ℎ355 ℎ363 ℎ372 ℎ373 ℎ375 ℎ377 ℎ378 ℎ379 ℎ380 ℎ382 ℎ386 ℎ387 ℎ389 ℎ390 ℎ399 ℎ400 ℎ401
    grind (splits := 10000) (ematch := 0) only
  have ℎ403 : (p 186 ≤ p 74 ∨ p 16 ≤ p 117 ∨ p 74 ≤ p 109 ∨ p 118 ≤ p 91) := by
    clear * - ℎ30 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ49 ℎ50 ℎ51 ℎ172 ℎ173 ℎ174 ℎ205
    grind (splits := 10000) (ematch := 0) only
  have ℎ404 : ((p 118 ≤ p 91 ∨ p 92 ≤ p 118) ∨ p 114 < p 84 ∨ ¬((p 114 ≤ p 85 ∨ p 86 ≤ p 114)) ∨ ¬((p 125 ≤ p 86 ∨ p 87 ≤ p 125)) ∨ ¬((p 125 ≤ p 84 ∨ p 85 ≤ p 125)) ∨ p 11 ≤ p 175 ∨ p 74 ≤ p 109 ∨ p 16 ≤ p 117) := by
    clear * - ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ49 ℎ50 ℎ51 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ124 ℎ144 ℎ145 ℎ146 ℎ147 ℎ148 ℎ149 ℎ150 ℎ151 ℎ152 ℎ153 ℎ154 ℎ155 ℎ156 ℎ157 ℎ158 ℎ159 ℎ160 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ179 ℎ195 ℎ203 ℎ205 ℎ234 ℎ236 ℎ241 ℎ255 ℎ264 ℎ272 ℎ275 ℎ278 ℎ284 ℎ286 ℎ303 ℎ318 ℎ323 ℎ328 ℎ335 ℎ349 ℎ353 ℎ355 ℎ400 ℎ401 ℎ403
    grind (splits := 10000) (ematch := 0) only
  have ℎ405 : (p 67 ≤ p 184 ∨ p 87 ≤ p 174 ∨ p 173 ≤ p 69) := by
    clear * - ℎ127 ℎ128 ℎ129 ℎ130 ℎ150 ℎ151 ℎ167
    grind (splits := 10000) (ematch := 0) only
  have ℎ406 : (p 11 ≤ p 175 ∨ p 93 < p 118 ∨ p 21 ≤ p 184 ∨ p 75 < p 109) := by
    clear * - ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ54 ℎ55 ℎ56 ℎ57 ℎ58 ℎ59 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ124 ℎ144 ℎ145 ℎ146 ℎ147 ℎ148 ℎ149 ℎ150 ℎ151 ℎ152 ℎ153 ℎ154 ℎ155 ℎ156 ℎ157 ℎ158 ℎ159 ℎ160 ℎ161 ℎ162 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ173 ℎ174 ℎ175 ℎ176 ℎ179 ℎ195 ℎ203 ℎ233 ℎ236 ℎ237 ℎ247 ℎ255 ℎ264 ℎ270 ℎ275 ℎ278 ℎ284 ℎ286 ℎ303 ℎ318 ℎ323 ℎ328 ℎ335 ℎ346 ℎ349 ℎ353 ℎ355 ℎ363 ℎ379 ℎ382 ℎ404 ℎ405
    grind (splits := 10000) (ematch := 0) only
  have ℎ407 : (p 109 ≤ p 75 ∨ p 153 ≤ p 8 ∨ p 8 ≤ p 110) := by
    clear * - ℎ31 ℎ32 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ179 ℎ255 ℎ256
    grind (splits := 10000) (ematch := 0) only
  have ℎ408 : (p 21 ≤ p 184 ∨ p 153 ≤ p 8 ∨ p 54 ≤ p 155 ∨ p 8 ≤ p 119 ∨ p 100 ≤ p 49) := by
    clear * - ℎ0 ℎ1 ℎ2 ℎ3 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ54 ℎ55 ℎ56 ℎ57 ℎ58 ℎ59 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ89 ℎ92 ℎ93 ℎ94 ℎ95 ℎ96 ℎ97 ℎ98 ℎ99 ℎ100 ℎ101 ℎ102 ℎ103 ℎ104 ℎ105 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ143 ℎ144 ℎ145 ℎ146 ℎ147 ℎ148 ℎ149 ℎ150 ℎ151 ℎ152 ℎ153 ℎ160 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ169 ℎ170 ℎ171 ℎ179 ℎ181 ℎ188 ℎ195 ℎ196 ℎ198 ℎ203 ℎ205 ℎ206 ℎ223 ℎ224 ℎ237 ℎ244 ℎ255 ℎ256 ℎ261 ℎ262 ℎ263 ℎ264 ℎ275 ℎ278 ℎ281 ℎ284 ℎ286 ℎ296 ℎ297 ℎ298 ℎ300 ℎ302 ℎ303 ℎ318 ℎ323 ℎ325 ℎ333 ℎ335 ℎ336 ℎ337 ℎ353 ℎ355 ℎ363 ℎ369 ℎ372 ℎ373 ℎ374 ℎ375 ℎ377 ℎ378 ℎ379 ℎ402 ℎ406 ℎ407
    grind (splits := 10000) (ematch := 0) only
  have ℎ409 : (p 101 < p 26 ∨ p 29 < p 101 ∨ ¬((p 101 ≤ p 23 ∨ p 24 ≤ p 101)) ∨ p 49 ≤ p 184 ∨ p 184 ≤ p 28 ∨ p 100 ≤ p 49) := by
    clear * - ℎ12 ℎ13 ℎ14 ℎ40 ℎ41 ℎ48 ℎ49 ℎ50 ℎ51 ℎ60 ℎ61 ℎ62 ℎ63 ℎ89 ℎ143 ℎ200 ℎ206 ℎ255 ℎ281 ℎ299 ℎ300 ℎ302 ℎ303 ℎ323 ℎ335 ℎ352 ℎ353
    grind (splits := 10000) (ematch := 0) only
  have ℎ410 : (p 49 ≤ p 184 ∨ ¬((p 101 ≤ p 23 ∨ p 24 ≤ p 101)) ∨ p 29 < p 101 ∨ p 184 ≤ p 28 ∨ p 100 ≤ p 49) := by
    clear * - ℎ13 ℎ14 ℎ48 ℎ49 ℎ50 ℎ51 ℎ409
    grind (splits := 10000) (ematch := 0) only
  have ℎ411 : (p 101 < p 16 ∨ ¬((p 101 ≤ p 17 ∨ p 18 ≤ p 101)) ∨ p 19 < p 101 ∨ p 101 < p 10 ∨ ¬((p 101 ≤ p 11 ∨ p 12 ≤ p 101))) := by
    clear * - ℎ26 ℎ27 ℎ28 ℎ29 ℎ190
    grind (splits := 10000) (ematch := 0) only
  have ℎ412 : (p 159 ≤ p 46 ∨ p 39 ≤ p 173) := by
    clear * - ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ124 ℎ125 ℎ126 ℎ127 ℎ128 ℎ129 ℎ130 ℎ150 ℎ151 ℎ152 ℎ153 ℎ154 ℎ155 ℎ156 ℎ157 ℎ158 ℎ159 ℎ179 ℎ255 ℎ328 ℎ349
    grind (splits := 10000) (ematch := 0) only
  have ℎ413 : (p 39 ≤ p 173 ∨ p 19 < p 101 ∨ p 173 ≤ p 18 ∨ p 117 < p 10 ∨ p 16 ≤ p 117) := by
    clear * - ℎ13 ℎ14 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ48 ℎ49 ℎ50 ℎ51 ℎ60 ℎ61 ℎ62 ℎ63 ℎ89 ℎ143 ℎ206 ℎ211 ℎ255 ℎ281 ℎ300 ℎ302 ℎ316 ℎ317 ℎ323 ℎ353 ℎ411 ℎ412
    grind (splits := 10000) (ematch := 0) only
  have ℎ414 : (p 8 ≤ p 119 ∨ p 54 ≤ p 155 ∨ p 153 ≤ p 8 ∨ p 173 ≤ p 18 ∨ ¬((p 118 ≤ p 91 ∨ p 92 ≤ p 118)) ∨ p 100 ≤ p 49) := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ18 ℎ19 ℎ20 ℎ21 ℎ22 ℎ23 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ54 ℎ55 ℎ56 ℎ57 ℎ58 ℎ59 ℎ60 ℎ61 ℎ62 ℎ63 ℎ89 ℎ92 ℎ93 ℎ94 ℎ95 ℎ102 ℎ103 ℎ104 ℎ105 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ143 ℎ150 ℎ151 ℎ152 ℎ153 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176 ℎ179 ℎ188 ℎ195 ℎ196 ℎ198 ℎ203 ℎ204 ℎ206 ℎ215 ℎ222 ℎ223 ℎ224 ℎ252 ℎ254 ℎ255 ℎ256 ℎ261 ℎ262 ℎ263 ℎ264 ℎ275 ℎ281 ℎ282 ℎ284 ℎ286 ℎ289 ℎ298 ℎ300 ℎ302 ℎ323 ℎ325 ℎ335 ℎ337 ℎ339 ℎ340 ℎ341 ℎ342 ℎ347 ℎ353 ℎ367 ℎ368 ℎ370 ℎ377 ℎ393 ℎ395 ℎ397 ℎ398 ℎ402 ℎ408 ℎ410 ℎ413
    grind (splits := 10000) (ematch := 0) only
  have ℎ415 : (p 54 ≤ p 155 ∨ p 153 ≤ p 8) := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ54 ℎ55 ℎ56 ℎ57 ℎ58 ℎ59 ℎ60 ℎ61 ℎ62 ℎ63 ℎ102 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ179 ℎ188 ℎ195 ℎ197 ℎ203 ℎ204 ℎ221 ℎ222 ℎ223 ℎ256 ℎ264 ℎ275 ℎ284 ℎ286 ℎ298 ℎ323 ℎ335 ℎ342 ℎ347 ℎ353 ℎ355 ℎ360 ℎ364 ℎ365 ℎ368 ℎ375 ℎ377 ℎ389 ℎ390 ℎ402 ℎ408 ℎ410 ℎ414
    grind (splits := 10000) (ematch := 0) only
  have ℎ416 : (p 105 < p 72 ∨ ¬((p 105 ≤ p 73 ∨ p 74 ≤ p 105)) ∨ p 75 < p 105 ∨ p 105 < p 66 ∨ ¬((p 105 ≤ p 67 ∨ p 68 ≤ p 105))) := by
    clear * - ℎ133 ℎ134 ℎ135 ℎ136 ℎ225
    grind (splits := 10000) (ematch := 0) only
  have ℎ417 : (p 73 ≤ p 116 ∨ p 105 ≤ p 73 ∨ p 115 ≤ p 13) := by
    clear * - ℎ23 ℎ43 ℎ44
    grind (splits := 10000) (ematch := 0) only
  have ℎ418 : (p 71 ≤ p 116 ∨ p 116 < p 73) := by
    clear * - ℎ135 ℎ136 ℎ137 ℎ138
    grind (splits := 10000) (ematch := 0) only
  have ℎ419 : (p 116 < p 73 ∨ ¬((p 116 ≤ p 74 ∨ p 75 ≤ p 116))) := by
    clear * - ℎ127 ℎ128 ℎ129 ℎ130 ℎ131 ℎ132 ℎ133 ℎ134 ℎ229 ℎ418
    grind (splits := 10000) (ematch := 0) only
  have ℎ420 : (p 109 ≤ p 75 ∨ p 155 ≤ p 8) := by
    clear * - ℎ31 ℎ32 ℎ33 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ89 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ143 ℎ179 ℎ195 ℎ196 ℎ203 ℎ206 ℎ255 ℎ256 ℎ264 ℎ275 ℎ281 ℎ282 ℎ284 ℎ286 ℎ300 ℎ302 ℎ335 ℎ337 ℎ339 ℎ340 ℎ341 ℎ342 ℎ347
    grind (splits := 10000) (ematch := 0) only
  have ℎ421 : (p 147 < p 69 ∨ ¬((p 147 ≤ p 74 ∨ p 75 ≤ p 147)) ∨ ¬((p 147 ≤ p 70 ∨ p 71 ≤ p 147)) ∨ ¬((p 147 ≤ p 72 ∨ p 73 ≤ p 147))) := by
    clear * - ℎ127 ℎ128 ℎ129 ℎ130 ℎ231
    grind (splits := 10000) (ematch := 0) only
  have ℎ422 : (p 166 ≤ p 46 ∨ p 46 ≤ p 148 ∨ p 147 ≤ p 74) := by
    clear * - ℎ103 ℎ104 ℎ136 ℎ137 ℎ138 ℎ139 ℎ140
    grind (splits := 10000) (ematch := 0) only
  have ℎ423 : (p 70 ≤ p 109 ∨ p 16 ≤ p 117 ∨ p 116 ≤ p 70) := by
    clear * - ℎ30 ℎ45 ℎ46
    grind (splits := 10000) (ematch := 0) only
  have ℎ424 : (p 166 ≤ p 46 ∨ ¬((p 109 ≤ p 67 ∨ p 68 ≤ p 109)) ∨ ¬((p 109 ≤ p 71 ∨ p 72 ≤ p 109)) ∨ p 75 < p 109 ∨ p 155 ≤ p 8 ∨ ¬((p 116 ≤ p 68 ∨ p 69 ≤ p 116)) ∨ ¬((p 116 ≤ p 66 ∨ p 67 ≤ p 116)) ∨ p 147 < p 69) := by
    clear * - ℎ30 ℎ31 ℎ32 ℎ33 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ89 ℎ92 ℎ93 ℎ94 ℎ95 ℎ102 ℎ103 ℎ104 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ135 ℎ136 ℎ137 ℎ138 ℎ143 ℎ179 ℎ195 ℎ196 ℎ203 ℎ206 ℎ224 ℎ226 ℎ229 ℎ252 ℎ254 ℎ255 ℎ256 ℎ261 ℎ262 ℎ263 ℎ264 ℎ275 ℎ281 ℎ282 ℎ284 ℎ286 ℎ300 ℎ302 ℎ335 ℎ337 ℎ339 ℎ340 ℎ341 ℎ342 ℎ347 ℎ360 ℎ361 ℎ382 ℎ421 ℎ422 ℎ423
    grind (splits := 10000) (ematch := 0) only
  have ℎ425 : (p 179 ≤ p 56 ∨ p 11 ≤ p 175 ∨ p 155 ≤ p 8 ∨ p 71 ≤ p 116 ∨ p 39 ≤ p 166 ∨ p 96 ≤ p 39) := by
    clear * - ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ31 ℎ32 ℎ33 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ102 ℎ103 ℎ104 ℎ105 ℎ124 ℎ135 ℎ144 ℎ145 ℎ146 ℎ147 ℎ148 ℎ149 ℎ150 ℎ151 ℎ152 ℎ153 ℎ160 ℎ195 ℎ203 ℎ264 ℎ275 ℎ284 ℎ286 ℎ318 ℎ335 ℎ342 ℎ347 ℎ355 ℎ361
    grind (splits := 10000) (ematch := 0) only
  have ℎ426 : (p 39 ≤ p 166 ∨ p 71 ≤ p 116 ∨ p 159 ≤ p 38 ∨ p 155 ≤ p 8 ∨ p 11 ≤ p 175) := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ87 ℎ88 ℎ92 ℎ93 ℎ94 ℎ95 ℎ96 ℎ97 ℎ98 ℎ99 ℎ100 ℎ101 ℎ102 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ108 ℎ109 ℎ110 ℎ111 ℎ112 ℎ113 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ135 ℎ160 ℎ179 ℎ187 ℎ203 ℎ209 ℎ221 ℎ224 ℎ252 ℎ254 ℎ255 ℎ256 ℎ258 ℎ261 ℎ262 ℎ263 ℎ264 ℎ284 ℎ286 ℎ296 ℎ297 ℎ308 ℎ330 ℎ331 ℎ333 ℎ335 ℎ361 ℎ415 ℎ425
    grind (splits := 10000) (ematch := 0) only
  have ℎ427 : (p 116 < p 71 ∨ ¬((p 116 ≤ p 72 ∨ p 73 ≤ p 116)) ∨ ¬((p 116 ≤ p 74 ∨ p 75 ≤ p 116))) := by
    clear * - ℎ127 ℎ128 ℎ129 ℎ130 ℎ131 ℎ132 ℎ133 ℎ134 ℎ229
    grind (splits := 10000) (ematch := 0) only
  have ℎ428 : ((p 109 ≤ p 71 ∨ p 72 ≤ p 109) ∨ p 147 < p 69 ∨ p 159 ≤ p 38 ∨ p 155 ≤ p 8 ∨ p 11 ≤ p 175 ∨ ¬((p 116 ≤ p 74 ∨ p 75 ≤ p 116))) := by
    clear * - ℎ30 ℎ31 ℎ32 ℎ33 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ89 ℎ92 ℎ93 ℎ94 ℎ95 ℎ102 ℎ103 ℎ104 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ136 ℎ143 ℎ179 ℎ195 ℎ196 ℎ203 ℎ206 ℎ213 ℎ224 ℎ252 ℎ254 ℎ255 ℎ256 ℎ261 ℎ262 ℎ263 ℎ264 ℎ275 ℎ281 ℎ282 ℎ284 ℎ286 ℎ300 ℎ302 ℎ335 ℎ337 ℎ339 ℎ340 ℎ341 ℎ342 ℎ347 ℎ361 ℎ421 ℎ422 ℎ426 ℎ427
    grind (splits := 10000) (ematch := 0) only
  have ℎ429 : (p 11 ≤ p 175 ∨ ¬((p 109 ≤ p 67 ∨ p 68 ≤ p 109)) ∨ p 155 ≤ p 8 ∨ p 147 < p 69) := by
    clear * - ℎ13 ℎ14 ℎ15 ℎ20 ℎ21 ℎ22 ℎ30 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ70 ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ92 ℎ93 ℎ94 ℎ102 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ127 ℎ128 ℎ129 ℎ130 ℎ135 ℎ143 ℎ144 ℎ145 ℎ146 ℎ147 ℎ148 ℎ149 ℎ150 ℎ151 ℎ152 ℎ153 ℎ154 ℎ155 ℎ156 ℎ157 ℎ158 ℎ159 ℎ160 ℎ179 ℎ187 ℎ195 ℎ203 ℎ206 ℎ211 ℎ213 ℎ216 ℎ221 ℎ255 ℎ256 ℎ264 ℎ275 ℎ281 ℎ282 ℎ284 ℎ286 ℎ297 ℎ300 ℎ318 ℎ327 ℎ328 ℎ329 ℎ330 ℎ331 ℎ335 ℎ337 ℎ341 ℎ342 ℎ347 ℎ348 ℎ349 ℎ351 ℎ355 ℎ356 ℎ358 ℎ360 ℎ361 ℎ362 ℎ382 ℎ415 ℎ416 ℎ417 ℎ419 ℎ420 ℎ424 ℎ428
    grind (splits := 10000) (ematch := 0) only
  have ℎ430 : (p 18 ≤ p 119 ∨ p 116 ≤ p 72 ∨ p 175 ≤ p 18) := by
    clear * - ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ366
    grind (splits := 10000) (ematch := 0) only
  have ℎ431 : (p 175 ≤ p 18 ∨ p 155 ≤ p 8 ∨ p 147 < p 69 ∨ ¬((p 109 ≤ p 67 ∨ p 68 ≤ p 109)) ∨ ¬((p 116 ≤ p 68 ∨ p 69 ≤ p 116)) ∨ ¬((p 116 ≤ p 66 ∨ p 67 ≤ p 116)) ∨ p 100 ≤ p 39) := by
    clear * - ℎ15 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ89 ℎ92 ℎ93 ℎ94 ℎ95 ℎ102 ℎ103 ℎ104 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ137 ℎ138 ℎ139 ℎ140 ℎ141 ℎ142 ℎ143 ℎ179 ℎ195 ℎ196 ℎ203 ℎ206 ℎ216 ℎ224 ℎ226 ℎ229 ℎ252 ℎ254 ℎ255 ℎ256 ℎ261 ℎ262 ℎ263 ℎ264 ℎ275 ℎ281 ℎ282 ℎ284 ℎ286 ℎ300 ℎ302 ℎ321 ℎ335 ℎ337 ℎ339 ℎ340 ℎ341 ℎ342 ℎ347 ℎ361 ℎ366 ℎ393 ℎ421 ℎ423 ℎ430
    grind (splits := 10000) (ematch := 0) only
  have ℎ432 : (p 38 ≤ p 142 ∨ p 49 ≤ p 179) := by
    clear * - ℎ71 ℎ72 ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ92 ℎ124 ℎ211 ℎ264
    grind (splits := 10000) (ematch := 0) only
  have ℎ433 : (p 175 ≤ p 18 ∨ p 155 ≤ p 8 ∨ p 147 < p 69) := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ70 ℎ92 ℎ93 ℎ94 ℎ95 ℎ102 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ127 ℎ128 ℎ129 ℎ130 ℎ131 ℎ132 ℎ137 ℎ138 ℎ139 ℎ140 ℎ143 ℎ179 ℎ187 ℎ195 ℎ203 ℎ206 ℎ211 ℎ212 ℎ216 ℎ221 ℎ224 ℎ252 ℎ254 ℎ255 ℎ256 ℎ261 ℎ262 ℎ263 ℎ264 ℎ275 ℎ281 ℎ284 ℎ286 ℎ297 ℎ321 ℎ329 ℎ330 ℎ331 ℎ335 ℎ337 ℎ341 ℎ342 ℎ347 ℎ351 ℎ360 ℎ361 ℎ366 ℎ415 ℎ421 ℎ431 ℎ432
    grind (splits := 10000) (ematch := 0) only
  have ℎ434 : (p 147 < p 69 ∨ p 155 ≤ p 8) := by
    clear * - ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ129 ℎ130 ℎ150 ℎ151 ℎ152 ℎ153 ℎ154 ℎ155 ℎ156 ℎ157 ℎ158 ℎ159 ℎ179 ℎ198 ℎ255 ℎ328 ℎ349 ℎ429 ℎ433
    grind (splits := 10000) (ematch := 0) only
  have ℎ435 : (p 105 ≤ p 67 ∨ p 67 ≤ p 116) := by
    clear * - ℎ23 ℎ31 ℎ32 ℎ33 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ124 ℎ143 ℎ195 ℎ203 ℎ206 ℎ255 ℎ264 ℎ275 ℎ281 ℎ284 ℎ286 ℎ335 ℎ337 ℎ341 ℎ342 ℎ347
    grind (splits := 10000) (ematch := 0) only
  have ℎ436 : (p 68 ≤ p 109 ∨ ¬((p 116 ≤ p 74 ∨ p 75 ≤ p 116)) ∨ ¬((p 116 ≤ p 72 ∨ p 73 ≤ p 116)) ∨ ¬((p 116 ≤ p 70 ∨ p 71 ≤ p 116)) ∨ p 105 < p 66) := by
    clear * - ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ124 ℎ129 ℎ130 ℎ143 ℎ195 ℎ203 ℎ206 ℎ225 ℎ229 ℎ255 ℎ264 ℎ275 ℎ281 ℎ282 ℎ284 ℎ286 ℎ335 ℎ337 ℎ341 ℎ342 ℎ347 ℎ417 ℎ419 ℎ427 ℎ435
    grind (splits := 10000) (ematch := 0) only
  have ℎ437 : (p 66 ≤ p 105 ∨ p 153 ≤ p 51 ∨ p 49 ≤ p 186 ∨ p 104 ≤ p 1) := by
    clear * - ℎ21 ℎ22 ℎ92 ℎ93 ℎ94 ℎ95 ℎ160 ℎ161 ℎ162 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ187 ℎ264 ℎ361 ℎ415
    grind (splits := 10000) (ematch := 0) only
  have ℎ438 : (p 90 < p 174 ∨ ¬((p 154 ≤ p 86 ∨ p 87 ≤ p 154)) ∨ ¬((p 154 ≤ p 84 ∨ p 85 ≤ p 154)) ∨ ¬((p 147 ≤ p 85 ∨ p 86 ≤ p 147)) ∨ p 173 ≤ p 46 ∨ ¬((p 174 ≤ p 84 ∨ p 85 ≤ p 174)) ∨ p 69 ≤ p 147) := by
    clear * - ℎ92 ℎ93 ℎ94 ℎ95 ℎ96 ℎ97 ℎ98 ℎ99 ℎ100 ℎ101 ℎ102 ℎ103 ℎ104 ℎ108 ℎ109 ℎ110 ℎ111 ℎ112 ℎ113 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ150 ℎ151 ℎ152 ℎ153 ℎ154 ℎ155 ℎ156 ℎ157 ℎ158 ℎ159 ℎ171 ℎ173 ℎ174 ℎ175 ℎ176 ℎ179 ℎ223 ℎ224 ℎ239 ℎ249 ℎ252 ℎ254 ℎ255 ℎ256 ℎ258 ℎ261 ℎ262 ℎ263 ℎ328 ℎ349 ℎ361 ℎ375
    grind (splits := 10000) (ematch := 0) only
  have ℎ439 : (p 88 < p 174 ∨ ¬((p 174 ≤ p 86 ∨ p 87 ≤ p 174)) ∨ ¬((p 174 ≤ p 84 ∨ p 85 ≤ p 174))) := by
    clear * - ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176 ℎ247
    grind (splits := 10000) (ematch := 0) only
  have ℎ440 : (p 6 ≤ p 119 ∨ p 155 ≤ p 8 ∨ p 118 ≤ p 93) := by
    clear * - ℎ12 ℎ13 ℎ14 ℎ15 ℎ49 ℎ50 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ256
    grind (splits := 10000) (ematch := 0) only
  have ℎ441 : (p 118 ≤ p 93 ∨ p 155 ≤ p 8) := by
    clear * - ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ160 ℎ161 ℎ162 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176 ℎ177 ℎ178 ℎ183 ℎ203 ℎ256 ℎ264 ℎ296 ℎ297 ℎ359 ℎ440
    grind (splits := 10000) (ematch := 0) only
  have ℎ442 : (p 1 ≤ p 153 ∨ p 84 ≤ p 114) := by
    clear * - ℎ39 ℎ40 ℎ108 ℎ109 ℎ110 ℎ111 ℎ112 ℎ113 ℎ203 ℎ258 ℎ264 ℎ284 ℎ286 ℎ296 ℎ297 ℎ333 ℎ335
    grind (splits := 10000) (ematch := 0) only
  have ℎ443 : (p 166 ≤ p 46 ∨ p 147 < p 69 ∨ ¬((p 147 ≤ p 70 ∨ p 71 ≤ p 147))) := by
    clear * - ℎ92 ℎ93 ℎ94 ℎ95 ℎ103 ℎ104 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ136 ℎ179 ℎ224 ℎ252 ℎ254 ℎ255 ℎ256 ℎ261 ℎ262 ℎ263 ℎ421 ℎ422
    grind (splits := 10000) (ematch := 0) only
  have ℎ444 : (p 109 ≤ p 71 ∨ p 155 ≤ p 8) := by
    clear * - ℎ30 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ89 ℎ92 ℎ93 ℎ94 ℎ95 ℎ102 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ129 ℎ130 ℎ131 ℎ132 ℎ133 ℎ134 ℎ135 ℎ137 ℎ138 ℎ139 ℎ140 ℎ143 ℎ144 ℎ145 ℎ146 ℎ147 ℎ148 ℎ149 ℎ150 ℎ151 ℎ152 ℎ153 ℎ160 ℎ179 ℎ187 ℎ195 ℎ196 ℎ198 ℎ203 ℎ206 ℎ211 ℎ213 ℎ216 ℎ221 ℎ224 ℎ252 ℎ254 ℎ255 ℎ256 ℎ261 ℎ262 ℎ263 ℎ264 ℎ275 ℎ281 ℎ282 ℎ284 ℎ286 ℎ296 ℎ297 ℎ300 ℎ302 ℎ318 ℎ330 ℎ331 ℎ333 ℎ335 ℎ337 ℎ339 ℎ340 ℎ341 ℎ342 ℎ347 ℎ351 ℎ360 ℎ361 ℎ366 ℎ382 ℎ393 ℎ415 ℎ420 ℎ421 ℎ427 ℎ429 ℎ430 ℎ443
    grind (splits := 10000) (ematch := 0) only
  have ℎ445 : (p 71 < p 109 ∨ p 109 ≤ p 73) := by
    clear * - ℎ135 ℎ136 ℎ137 ℎ138
    grind (splits := 10000) (ematch := 0) only
  have ℎ446 : p 155 ≤ p 8 := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ5 ℎ6 ℎ7 ℎ8 ℎ9 ℎ10 ℎ11 ℎ12 ℎ13 ℎ14 ℎ15 ℎ18 ℎ19 ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ70 ℎ89 ℎ92 ℎ93 ℎ94 ℎ95 ℎ96 ℎ97 ℎ98 ℎ99 ℎ100 ℎ101 ℎ102 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ131 ℎ132 ℎ133 ℎ134 ℎ135 ℎ136 ℎ137 ℎ138 ℎ139 ℎ140 ℎ143 ℎ150 ℎ151 ℎ152 ℎ153 ℎ154 ℎ155 ℎ156 ℎ157 ℎ158 ℎ159 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ172 ℎ179 ℎ187 ℎ195 ℎ196 ℎ197 ℎ203 ℎ206 ℎ211 ℎ212 ℎ215 ℎ221 ℎ222 ℎ223 ℎ224 ℎ226 ℎ233 ℎ234 ℎ252 ℎ254 ℎ255 ℎ256 ℎ261 ℎ262 ℎ263 ℎ264 ℎ275 ℎ281 ℎ282 ℎ284 ℎ286 ℎ297 ℎ300 ℎ302 ℎ328 ℎ329 ℎ330 ℎ331 ℎ335 ℎ337 ℎ339 ℎ340 ℎ341 ℎ342 ℎ347 ℎ349 ℎ351 ℎ360 ℎ361 ℎ364 ℎ366 ℎ382 ℎ393 ℎ395 ℎ413 ℎ415 ℎ420 ℎ423 ℎ432 ℎ434 ℎ436 ℎ437 ℎ438 ℎ439 ℎ441 ℎ442 ℎ444 ℎ445
    grind (splits := 10000) (ematch := 0) only
  have ℎ447 : (p 96 ≤ p 57 ∨ p 124 ≤ p 3) := by
    clear * - ℎ5 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ179 ℎ263 ℎ278
    grind (splits := 10000) (ematch := 0) only
  have ℎ448 : p 0 ≤ p 124 := by
    clear * - ℎ0 ℎ1 ℎ39 ℎ40 ℎ41 ℎ203 ℎ264 ℎ284 ℎ286 ℎ296 ℎ297 ℎ303 ℎ333 ℎ335
    grind (splits := 10000) (ematch := 0) only
  have ℎ449 : p 3 < p 124 := by
    clear * - ℎ6 ℎ7 ℎ8 ℎ9 ℎ48 ℎ49 ℎ50 ℎ51 ℎ60 ℎ61 ℎ62 ℎ63 ℎ89 ℎ143 ℎ184 ℎ206 ℎ255 ℎ281 ℎ300 ℎ302 ℎ323 ℎ353 ℎ448
    grind (splits := 10000) (ematch := 0) only
  have ℎ450 : p 48 ≤ p 96 := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ90 ℎ91 ℎ92 ℎ93 ℎ94 ℎ95 ℎ188 ℎ261 ℎ262 ℎ263 ℎ446
    grind (splits := 10000) (ematch := 0) only
  have ℎ451 : p 96 < p 56 := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ94 ℎ95 ℎ98 ℎ99 ℎ100 ℎ101 ℎ102 ℎ103 ℎ104 ℎ105 ℎ188 ℎ217 ℎ261 ℎ262 ℎ263 ℎ446 ℎ447 ℎ449 ℎ450
    grind (splits := 10000) (ematch := 0) only
  have ℎ452 : (p 21 ≤ p 184 ∨ p 184 ≤ p 56 ∨ p 95 ≤ p 21) := by
    clear * - ℎ3 ℎ4 ℎ451
    grind (splits := 10000) (ematch := 0) only
  have ℎ453 : p 0 ≤ p 104 := by
    clear * - ℎ20 ℎ31 ℎ32 ℎ33 ℎ70 ℎ71 ℎ72 ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ124 ℎ195 ℎ211 ℎ297 ℎ342 ℎ347
    grind (splits := 10000) (ematch := 0) only
  have ℎ454 : (p 67 ≤ p 184 ∨ ¬((p 105 ≤ p 73 ∨ p 74 ≤ p 105)) ∨ ¬((p 105 ≤ p 71 ∨ p 72 ≤ p 105)) ∨ p 184 ≤ p 28) := by
    clear * - ℎ21 ℎ22 ℎ23 ℎ31 ℎ32 ℎ33 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ108 ℎ109 ℎ110 ℎ111 ℎ112 ℎ113 ℎ114 ℎ115 ℎ116 ℎ117 ℎ124 ℎ127 ℎ128 ℎ129 ℎ130 ℎ143 ℎ160 ℎ188 ℎ195 ℎ203 ℎ206 ℎ225 ℎ255 ℎ258 ℎ264 ℎ275 ℎ281 ℎ282 ℎ284 ℎ286 ℎ329 ℎ335 ℎ337 ℎ341 ℎ342 ℎ347 ℎ446 ℎ453
    grind (splits := 10000) (ematch := 0) only
  have ℎ455 : (p 173 ≤ p 18 ∨ p 118 ≤ p 87 ∨ p 88 < p 174) := by
    clear * - ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ124 ℎ150 ℎ151 ℎ163 ℎ164 ℎ165 ℎ166 ℎ195 ℎ203 ℎ264 ℎ284 ℎ286 ℎ335 ℎ342 ℎ347 ℎ393 ℎ439
    grind (splits := 10000) (ematch := 0) only
  have ℎ456 : (p 173 < p 11 ∨ p 184 ≤ p 28 ∨ p 118 ≤ p 87) := by
    clear * - ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ124 ℎ137 ℎ138 ℎ139 ℎ140 ℎ143 ℎ150 ℎ151 ℎ152 ℎ153 ℎ168 ℎ195 ℎ197 ℎ198 ℎ203 ℎ206 ℎ233 ℎ255 ℎ264 ℎ275 ℎ281 ℎ284 ℎ286 ℎ335 ℎ337 ℎ341 ℎ342 ℎ347 ℎ366 ℎ393 ℎ427 ℎ430 ℎ454 ℎ455
    grind (splits := 10000) (ematch := 0) only
  have ℎ457 : (p 96 ≤ p 39 ∨ p 38 ≤ p 96) := by
    clear * - ℎ71 ℎ72
    grind (splits := 10000) (ematch := 0) only
  have ℎ458 : (p 96 < p 42 ∨ p 96 < p 38 ∨ p 95 ≤ p 11 ∨ p 11 ≤ p 173 ∨ p 173 ≤ p 46) := by
    clear * - ℎ3 ℎ4 ℎ5 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ143 ℎ179 ℎ207 ℎ255 ℎ278 ℎ300 ℎ449
    grind (splits := 10000) (ematch := 0) only
  have ℎ459 : (p 95 ≤ p 11 ∨ p 96 < p 38 ∨ p 11 ≤ p 173 ∨ p 173 ≤ p 46) := by
    clear * - ℎ3 ℎ4 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ458
    grind (splits := 10000) (ematch := 0) only
  have ℎ460 : (p 11 ≤ p 173 ∨ p 95 ≤ p 11 ∨ p 173 ≤ p 46) := by
    clear * - ℎ3 ℎ4 ℎ73 ℎ74 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ457 ℎ459
    grind (splits := 10000) (ematch := 0) only
  have ℎ461 : (p 52 ≤ p 96 ∨ p 21 ≤ p 186 ∨ p 186 ≤ p 56 ∨ p 2 ≤ p 113) := by
    clear * - ℎ4 ℎ38 ℎ98 ℎ99 ℎ100 ℎ101 ℎ102 ℎ103 ℎ104 ℎ105
    grind (splits := 10000) (ematch := 0) only
  have ℎ462 : (p 56 ≤ p 96 ∨ p 21 ≤ p 186 ∨ p 186 ≤ p 56 ∨ p 2 ≤ p 113) := by
    clear * - ℎ4 ℎ38
    grind (splits := 10000) (ematch := 0) only
  have ℎ463 : (p 2 ≤ p 113 ∨ p 57 < p 96 ∨ p 96 < p 48 ∨ p 186 ≤ p 56 ∨ p 21 ≤ p 186) := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ94 ℎ95 ℎ102 ℎ103 ℎ104 ℎ105 ℎ188 ℎ217 ℎ261 ℎ262 ℎ263 ℎ446 ℎ461 ℎ462
    grind (splits := 10000) (ematch := 0) only
  have ℎ464 : (p 95 ≤ p 29 ∨ p 124 ≤ p 3) := by
    clear * - ℎ3 ℎ4 ℎ5 ℎ48 ℎ49 ℎ50 ℎ51 ℎ52 ℎ53 ℎ60 ℎ61 ℎ62 ℎ63 ℎ323 ℎ353
    grind (splits := 10000) (ematch := 0) only
  have ℎ465 : (p 124 ≤ p 3 ∨ p 96 < p 48 ∨ p 21 ≤ p 186 ∨ p 186 ≤ p 56) := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ5 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ48 ℎ49 ℎ60 ℎ61 ℎ62 ℎ63 ℎ94 ℎ95 ℎ98 ℎ99 ℎ100 ℎ101 ℎ102 ℎ103 ℎ104 ℎ105 ℎ108 ℎ109 ℎ110 ℎ111 ℎ112 ℎ113 ℎ160 ℎ187 ℎ188 ℎ199 ℎ217 ℎ258 ℎ261 ℎ262 ℎ263 ℎ283 ℎ323 ℎ353 ℎ361 ℎ415 ℎ446 ℎ447 ℎ463 ℎ464
    grind (splits := 10000) (ematch := 0) only
  have ℎ466 : p 48 ≤ p 153 := by
    clear * - ℎ90 ℎ91 ℎ92 ℎ93 ℎ94 ℎ95 ℎ96 ℎ97 ℎ98 ℎ99 ℎ100 ℎ101 ℎ102 ℎ103 ℎ104 ℎ105 ℎ108 ℎ109 ℎ110 ℎ111 ℎ112 ℎ113 ℎ160 ℎ221 ℎ258 ℎ331
    grind (splits := 10000) (ematch := 0) only
  have ℎ467 : (p 67 < p 105 ∨ ¬((p 105 ≤ p 73 ∨ p 74 ≤ p 105)) ∨ ¬((p 105 ≤ p 71 ∨ p 72 ≤ p 105))) := by
    clear * - ℎ21 ℎ22 ℎ31 ℎ32 ℎ33 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ108 ℎ109 ℎ110 ℎ111 ℎ112 ℎ113 ℎ114 ℎ115 ℎ116 ℎ117 ℎ124 ℎ127 ℎ128 ℎ129 ℎ130 ℎ143 ℎ160 ℎ188 ℎ195 ℎ203 ℎ206 ℎ225 ℎ255 ℎ258 ℎ264 ℎ275 ℎ281 ℎ282 ℎ284 ℎ286 ℎ329 ℎ335 ℎ337 ℎ341 ℎ342 ℎ347 ℎ446 ℎ453
    grind (splits := 10000) (ematch := 0) only
  have ℎ468 : (p 173 ≤ p 46 ∨ p 186 ≤ p 56 ∨ p 95 ≤ p 21 ∨ p 95 ≤ p 11) := by
    clear * - ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ92 ℎ93 ℎ94 ℎ95 ℎ102 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ108 ℎ109 ℎ110 ℎ111 ℎ112 ℎ113 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ137 ℎ138 ℎ139 ℎ140 ℎ143 ℎ150 ℎ151 ℎ152 ℎ153 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176 ℎ177 ℎ178 ℎ179 ℎ187 ℎ188 ℎ195 ℎ197 ℎ198 ℎ203 ℎ204 ℎ205 ℎ206 ℎ222 ℎ224 ℎ234 ℎ239 ℎ249 ℎ252 ℎ254 ℎ255 ℎ256 ℎ258 ℎ261 ℎ262 ℎ263 ℎ264 ℎ275 ℎ281 ℎ284 ℎ286 ℎ330 ℎ334 ℎ335 ℎ337 ℎ341 ℎ342 ℎ347 ℎ361 ℎ364 ℎ366 ℎ375 ℎ393 ℎ398 ℎ415 ℎ427 ℎ430 ℎ435 ℎ442 ℎ446 ℎ449 ℎ450 ℎ452 ℎ456 ℎ460 ℎ465 ℎ466 ℎ467
    grind (splits := 10000) (ematch := 0) only
  have ℎ469 : p 21 < p 95 := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ5 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ48 ℎ49 ℎ60 ℎ61 ℎ62 ℎ63 ℎ108 ℎ109 ℎ110 ℎ111 ℎ112 ℎ113 ℎ160 ℎ187 ℎ199 ℎ258 ℎ283 ℎ323 ℎ353 ℎ361 ℎ415 ℎ449 ℎ464
    grind (splits := 10000) (ematch := 0) only
  have ℎ470 : (p 95 ≤ p 11 ∨ p 11 ≤ p 175 ∨ p 175 ≤ p 46) := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ5 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ75 ℎ76 ℎ77 ℎ78 ℎ79 ℎ80 ℎ81 ℎ82 ℎ83 ℎ84 ℎ85 ℎ86 ℎ93 ℎ94 ℎ95 ℎ102 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ114 ℎ115 ℎ116 ℎ117 ℎ143 ℎ179 ℎ187 ℎ203 ℎ207 ℎ221 ℎ255 ℎ278 ℎ284 ℎ286 ℎ300 ℎ330 ℎ335 ℎ361 ℎ415 ℎ432 ℎ449 ℎ451 ℎ466 ℎ469
    grind (splits := 10000) (ematch := 0) only
  have ℎ471 : (p 95 ≤ p 17 ∨ p 13 < p 95) := by
    clear * - ℎ24 ℎ25 ℎ26 ℎ27 ℎ28 ℎ29 ℎ30 ℎ31
    grind (splits := 10000) (ematch := 0) only
  have ℎ472 : p 10 ≤ p 95 := by
    clear * - ℎ2 ℎ31 ℎ32 ℎ33 ℎ108 ℎ109 ℎ110 ℎ111 ℎ112 ℎ113 ℎ114 ℎ115 ℎ116 ℎ117 ℎ124 ℎ160 ℎ188 ℎ195 ℎ258 ℎ264 ℎ342 ℎ347 ℎ446
    grind (splits := 10000) (ematch := 0) only
  have ℎ473 : (p 11 < p 95 ∨ ¬((p 95 ≤ p 17 ∨ p 18 ≤ p 95))) := by
    clear * - ℎ3 ℎ4 ℎ5 ℎ20 ℎ21 ℎ22 ℎ23 ℎ24 ℎ25 ℎ26 ℎ27 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ143 ℎ179 ℎ189 ℎ255 ℎ278 ℎ337 ℎ449 ℎ472
    grind (splits := 10000) (ematch := 0) only
  have ℎ474 : p 11 < p 95 := by
    clear * - ℎ20 ℎ21 ℎ22 ℎ23 ℎ471 ℎ473
    grind (splits := 10000) (ematch := 0) only
  have ℎ475 : p 49 ≤ p 186 := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ5 ℎ20 ℎ21 ℎ22 ℎ31 ℎ32 ℎ33 ℎ38 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ54 ℎ55 ℎ56 ℎ57 ℎ58 ℎ59 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ87 ℎ88 ℎ92 ℎ93 ℎ94 ℎ95 ℎ96 ℎ97 ℎ98 ℎ99 ℎ100 ℎ101 ℎ102 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ108 ℎ109 ℎ110 ℎ111 ℎ112 ℎ113 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ124 ℎ129 ℎ130 ℎ143 ℎ150 ℎ151 ℎ152 ℎ153 ℎ154 ℎ155 ℎ156 ℎ157 ℎ158 ℎ159 ℎ160 ℎ161 ℎ162 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ168 ℎ169 ℎ170 ℎ171 ℎ179 ℎ187 ℎ188 ℎ195 ℎ198 ℎ203 ℎ206 ℎ216 ℎ221 ℎ224 ℎ234 ℎ236 ℎ237 ℎ238 ℎ241 ℎ244 ℎ252 ℎ254 ℎ255 ℎ256 ℎ258 ℎ261 ℎ262 ℎ263 ℎ264 ℎ265 ℎ267 ℎ272 ℎ273 ℎ275 ℎ278 ℎ281 ℎ282 ℎ284 ℎ286 ℎ296 ℎ297 ℎ303 ℎ323 ℎ328 ℎ329 ℎ330 ℎ333 ℎ334 ℎ335 ℎ337 ℎ341 ℎ342 ℎ347 ℎ349 ℎ353 ℎ361 ℎ363 ℎ372 ℎ393 ℎ400 ℎ401 ℎ415 ℎ432 ℎ442 ℎ446 ℎ449 ℎ451 ℎ453 ℎ466 ℎ469 ℎ470 ℎ474
    grind (splits := 10000) (ematch := 0) only
  have ℎ476 : (p 39 ≤ p 173 ∨ p 142 ≤ p 39 ∨ p 84 ≤ p 143) := by
    clear * - ℎ93 ℎ94 ℎ144 ℎ145 ℎ146 ℎ147 ℎ148 ℎ149 ℎ318
    grind (splits := 10000) (ematch := 0) only
  have ℎ477 : (p 143 ≤ p 87 ∨ p 86 ≤ p 114) := by
    clear * - ℎ39 ℎ40 ℎ95 ℎ102 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ114 ℎ115 ℎ116 ℎ117 ℎ165 ℎ166 ℎ188 ℎ203 ℎ264 ℎ284 ℎ286 ℎ296 ℎ297 ℎ330 ℎ333 ℎ335 ℎ361 ℎ446 ℎ466
    grind (splits := 10000) (ematch := 0) only
  have ℎ478 : (p 85 ≤ p 125 ∨ ¬((p 114 ≤ p 89 ∨ p 90 ≤ p 114)) ∨ ¬((p 114 ≤ p 91 ∨ p 92 ≤ p 114))) := by
    clear * - ℎ41 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ163 ℎ164 ℎ165 ℎ166 ℎ187 ℎ236 ℎ278 ℎ303 ℎ335 ℎ361 ℎ415 ℎ442
    grind (splits := 10000) (ematch := 0) only
  have ℎ479 : (p 184 ≤ p 56 ∨ p 143 < p 84 ∨ p 186 ≤ p 56) := by
    clear * - ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ95 ℎ96 ℎ97 ℎ98 ℎ99 ℎ100 ℎ101 ℎ102 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ114 ℎ115 ℎ116 ℎ117 ℎ118 ℎ119 ℎ120 ℎ121 ℎ122 ℎ123 ℎ168 ℎ169 ℎ170 ℎ172 ℎ173 ℎ174 ℎ187 ℎ188 ℎ203 ℎ204 ℎ205 ℎ236 ℎ238 ℎ256 ℎ261 ℎ262 ℎ263 ℎ264 ℎ278 ℎ284 ℎ286 ℎ296 ℎ297 ℎ303 ℎ330 ℎ333 ℎ335 ℎ361 ℎ375 ℎ379 ℎ415 ℎ442 ℎ446 ℎ449 ℎ450 ℎ452 ℎ465 ℎ466 ℎ469 ℎ477 ℎ478
    grind (splits := 10000) (ematch := 0) only
  have ℎ480 : (p 186 ≤ p 56 ∨ p 143 < p 84) := by
    clear * - ℎ2 ℎ3 ℎ4 ℎ5 ℎ39 ℎ40 ℎ41 ℎ42 ℎ43 ℎ44 ℎ45 ℎ46 ℎ47 ℎ48 ℎ49 ℎ50 ℎ51 ℎ60 ℎ61 ℎ62 ℎ63 ℎ64 ℎ65 ℎ66 ℎ67 ℎ68 ℎ69 ℎ92 ℎ93 ℎ94 ℎ95 ℎ102 ℎ103 ℎ104 ℎ105 ℎ106 ℎ107 ℎ114 ℎ115 ℎ116 ℎ117 ℎ163 ℎ164 ℎ165 ℎ166 ℎ167 ℎ172 ℎ173 ℎ174 ℎ175 ℎ176 ℎ187 ℎ188 ℎ203 ℎ205 ℎ222 ℎ236 ℎ241 ℎ264 ℎ278 ℎ284 ℎ286 ℎ296 ℎ297 ℎ303 ℎ323 ℎ330 ℎ333 ℎ335 ℎ353 ℎ361 ℎ375 ℎ415 ℎ442 ℎ446 ℎ449 ℎ450 ℎ465 ℎ466 ℎ477 ℎ479
    grind (splits := 10000) (ematch := 0) only
  have ℎ481 : False := by
    clear * - ℎ3 ℎ4 ℎ203 ℎ215 ℎ221 ℎ223 ℎ284 ℎ286 ℎ335 ℎ351 ℎ432 ℎ451 ℎ468 ℎ469 ℎ474 ℎ475 ℎ476 ℎ480
    grind (splits := 10000) (ematch := 0) only
  exact ℎ481

private def FiveRuns.value (d : FiveRuns) : ℕ → ℕ
  | 0 => d.c 0 1 0
  | 1 => d.c 0 1 1
  | 2 => d.c 0 1 2
  | 3 => d.c 0 1 3
  | 4 => d.c 0 1 4
  | 5 => d.c 0 1 5
  | 6 => d.c 0 1 6
  | 7 => d.c 0 1 7
  | 8 => d.c 0 1 8
  | 9 => d.c 0 1 9
  | 10 => d.c 0 2 0
  | 11 => d.c 0 2 1
  | 12 => d.c 0 2 2
  | 13 => d.c 0 2 3
  | 14 => d.c 0 2 4
  | 15 => d.c 0 2 5
  | 16 => d.c 0 2 6
  | 17 => d.c 0 2 7
  | 18 => d.c 0 2 8
  | 19 => d.c 0 2 9
  | 20 => d.c 0 3 0
  | 21 => d.c 0 3 1
  | 22 => d.c 0 3 2
  | 23 => d.c 0 3 3
  | 24 => d.c 0 3 4
  | 25 => d.c 0 3 5
  | 26 => d.c 0 3 6
  | 27 => d.c 0 3 7
  | 28 => d.c 0 3 8
  | 29 => d.c 0 3 9
  | 30 => d.c 0 4 1
  | 31 => d.c 0 4 2
  | 32 => d.c 0 4 3
  | 33 => d.c 0 4 4
  | 34 => d.c 0 4 5
  | 35 => d.c 0 4 6
  | 36 => d.c 0 4 7
  | 37 => d.c 0 4 8
  | 38 => d.c 1 2 0
  | 39 => d.c 1 2 1
  | 40 => d.c 1 2 2
  | 41 => d.c 1 2 3
  | 42 => d.c 1 2 4
  | 43 => d.c 1 2 5
  | 44 => d.c 1 2 6
  | 45 => d.c 1 2 7
  | 46 => d.c 1 2 8
  | 47 => d.c 1 2 9
  | 48 => d.c 1 3 0
  | 49 => d.c 1 3 1
  | 50 => d.c 1 3 2
  | 51 => d.c 1 3 3
  | 52 => d.c 1 3 4
  | 53 => d.c 1 3 5
  | 54 => d.c 1 3 6
  | 55 => d.c 1 3 7
  | 56 => d.c 1 3 8
  | 57 => d.c 1 3 9
  | 58 => d.c 1 4 1
  | 59 => d.c 1 4 2
  | 60 => d.c 1 4 3
  | 61 => d.c 1 4 4
  | 62 => d.c 1 4 5
  | 63 => d.c 1 4 6
  | 64 => d.c 1 4 7
  | 65 => d.c 1 4 8
  | 66 => d.c 2 3 0
  | 67 => d.c 2 3 1
  | 68 => d.c 2 3 2
  | 69 => d.c 2 3 3
  | 70 => d.c 2 3 4
  | 71 => d.c 2 3 5
  | 72 => d.c 2 3 6
  | 73 => d.c 2 3 7
  | 74 => d.c 2 3 8
  | 75 => d.c 2 3 9
  | 76 => d.c 2 4 1
  | 77 => d.c 2 4 2
  | 78 => d.c 2 4 3
  | 79 => d.c 2 4 4
  | 80 => d.c 2 4 5
  | 81 => d.c 2 4 6
  | 82 => d.c 2 4 7
  | 83 => d.c 2 4 8
  | 84 => d.c 3 4 0
  | 85 => d.c 3 4 1
  | 86 => d.c 3 4 2
  | 87 => d.c 3 4 3
  | 88 => d.c 3 4 4
  | 89 => d.c 3 4 5
  | 90 => d.c 3 4 6
  | 91 => d.c 3 4 7
  | 92 => d.c 3 4 8
  | 93 => d.c 3 4 9
  | 94 => d.p 0 1 1
  | 95 => d.p 0 1 2
  | 96 => d.p 0 1 3
  | 97 => d.p 0 1 4
  | 98 => d.p 0 1 5
  | 99 => d.p 0 1 6
  | 100 => d.p 0 1 7
  | 101 => d.p 0 1 8
  | 102 => d.p 0 1 9
  | 103 => d.p 0 2 1
  | 104 => d.p 0 2 2
  | 105 => d.p 0 2 3
  | 106 => d.p 0 2 4
  | 107 => d.p 0 2 5
  | 108 => d.p 0 2 6
  | 109 => d.p 0 2 7
  | 110 => d.p 0 2 8
  | 111 => d.p 0 2 9
  | 112 => d.p 0 3 1
  | 113 => d.p 0 3 2
  | 114 => d.p 0 3 3
  | 115 => d.p 0 3 4
  | 116 => d.p 0 3 5
  | 117 => d.p 0 3 6
  | 118 => d.p 0 3 7
  | 119 => d.p 0 3 8
  | 120 => d.p 0 3 9
  | 121 => d.p 0 4 1
  | 122 => d.p 0 4 2
  | 123 => d.p 0 4 3
  | 124 => d.p 0 4 4
  | 125 => d.p 0 4 5
  | 126 => d.p 0 4 6
  | 127 => d.p 0 4 7
  | 128 => d.p 0 4 8
  | 129 => d.p 0 4 9
  | 130 => d.p 1 2 0
  | 131 => d.p 1 2 1
  | 132 => d.p 1 2 10
  | 133 => d.p 1 2 2
  | 134 => d.p 1 2 3
  | 135 => d.p 1 2 4
  | 136 => d.p 1 2 5
  | 137 => d.p 1 2 6
  | 138 => d.p 1 2 7
  | 139 => d.p 1 2 8
  | 140 => d.p 1 2 9
  | 141 => d.p 1 3 1
  | 142 => d.p 1 3 2
  | 143 => d.p 1 3 3
  | 144 => d.p 1 3 4
  | 145 => d.p 1 3 5
  | 146 => d.p 1 3 6
  | 147 => d.p 1 3 7
  | 148 => d.p 1 3 8
  | 149 => d.p 1 3 9
  | 150 => d.p 1 4 1
  | 151 => d.p 1 4 2
  | 152 => d.p 1 4 3
  | 153 => d.p 1 4 4
  | 154 => d.p 1 4 5
  | 155 => d.p 1 4 6
  | 156 => d.p 1 4 7
  | 157 => d.p 1 4 8
  | 158 => d.p 1 4 9
  | 159 => d.p 2 3 0
  | 160 => d.p 2 3 1
  | 161 => d.p 2 3 10
  | 162 => d.p 2 3 2
  | 163 => d.p 2 3 3
  | 164 => d.p 2 3 4
  | 165 => d.p 2 3 5
  | 166 => d.p 2 3 6
  | 167 => d.p 2 3 7
  | 168 => d.p 2 3 8
  | 169 => d.p 2 3 9
  | 170 => d.p 2 4 1
  | 171 => d.p 2 4 2
  | 172 => d.p 2 4 3
  | 173 => d.p 2 4 4
  | 174 => d.p 2 4 5
  | 175 => d.p 2 4 6
  | 176 => d.p 2 4 7
  | 177 => d.p 2 4 8
  | 178 => d.p 2 4 9
  | 179 => d.p 3 4 0
  | 180 => d.p 3 4 1
  | 181 => d.p 3 4 10
  | 182 => d.p 3 4 2
  | 183 => d.p 3 4 3
  | 184 => d.p 3 4 4
  | 185 => d.p 3 4 5
  | 186 => d.p 3 4 6
  | 187 => d.p 3 4 7
  | 188 => d.p 3 4 8
  | 189 => d.p 3 4 9
  | _ => 0

set_option maxRecDepth 32000 in
private theorem fiveRunsImpossible (d : FiveRuns) : False := by
  apply incompatibleSamples d.value
  · exact d.after 0 1 0 (by decide)
  · exact d.before 0 1 1 (by decide)
  · exact d.after 0 1 1 (by decide)
  · exact d.before 0 1 2 (by decide)
  · exact d.after 0 1 2 (by decide)
  · exact d.before 0 1 3 (by decide)
  · exact d.after 0 1 3 (by decide)
  · exact d.before 0 1 4 (by decide)
  · exact d.after 0 1 4 (by decide)
  · exact d.before 0 1 5 (by decide)
  · exact d.after 0 1 5 (by decide)
  · exact d.before 0 1 6 (by decide)
  · exact d.after 0 1 6 (by decide)
  · exact d.before 0 1 7 (by decide)
  · exact d.after 0 1 7 (by decide)
  · exact d.before 0 1 8 (by decide)
  · exact d.after 0 1 8 (by decide)
  · exact d.before 0 1 9 (by decide)
  · exact d.after 0 2 0 (by decide)
  · exact d.before 0 2 1 (by decide)
  · exact d.after 0 2 1 (by decide)
  · exact d.before 0 2 2 (by decide)
  · exact d.after 0 2 2 (by decide)
  · exact d.before 0 2 3 (by decide)
  · exact d.after 0 2 3 (by decide)
  · exact d.before 0 2 4 (by decide)
  · exact d.after 0 2 4 (by decide)
  · exact d.before 0 2 5 (by decide)
  · exact d.after 0 2 5 (by decide)
  · exact d.before 0 2 6 (by decide)
  · exact d.after 0 2 6 (by decide)
  · exact d.before 0 2 7 (by decide)
  · exact d.after 0 2 7 (by decide)
  · exact d.before 0 2 8 (by decide)
  · exact d.after 0 2 8 (by decide)
  · exact d.before 0 2 9 (by decide)
  · exact d.after 0 3 0 (by decide)
  · exact d.before 0 3 1 (by decide)
  · exact d.after 0 3 1 (by decide)
  · exact d.before 0 3 2 (by decide)
  · exact d.after 0 3 2 (by decide)
  · exact d.before 0 3 3 (by decide)
  · exact d.after 0 3 3 (by decide)
  · exact d.before 0 3 4 (by decide)
  · exact d.after 0 3 4 (by decide)
  · exact d.before 0 3 5 (by decide)
  · exact d.after 0 3 5 (by decide)
  · exact d.before 0 3 6 (by decide)
  · exact d.after 0 3 6 (by decide)
  · exact d.before 0 3 7 (by decide)
  · exact d.after 0 3 7 (by decide)
  · exact d.before 0 3 8 (by decide)
  · exact d.after 0 3 8 (by decide)
  · exact d.before 0 3 9 (by decide)
  · exact d.before 0 4 1 (by decide)
  · exact d.after 0 4 1 (by decide)
  · exact d.before 0 4 2 (by decide)
  · exact d.after 0 4 2 (by decide)
  · exact d.before 0 4 3 (by decide)
  · exact d.after 0 4 3 (by decide)
  · exact d.before 0 4 4 (by decide)
  · exact d.after 0 4 4 (by decide)
  · exact d.before 0 4 5 (by decide)
  · exact d.after 0 4 5 (by decide)
  · exact d.before 0 4 6 (by decide)
  · exact d.after 0 4 6 (by decide)
  · exact d.before 0 4 7 (by decide)
  · exact d.after 0 4 7 (by decide)
  · exact d.before 0 4 8 (by decide)
  · exact d.after 0 4 8 (by decide)
  · exact d.before 1 2 0 (by decide)
  · exact d.after 1 2 0 (by decide)
  · exact d.before 1 2 1 (by decide)
  · exact d.after 1 2 1 (by decide)
  · exact d.before 1 2 2 (by decide)
  · exact d.after 1 2 2 (by decide)
  · exact d.before 1 2 3 (by decide)
  · exact d.after 1 2 3 (by decide)
  · exact d.before 1 2 4 (by decide)
  · exact d.after 1 2 4 (by decide)
  · exact d.before 1 2 5 (by decide)
  · exact d.after 1 2 5 (by decide)
  · exact d.before 1 2 6 (by decide)
  · exact d.after 1 2 6 (by decide)
  · exact d.before 1 2 7 (by decide)
  · exact d.after 1 2 7 (by decide)
  · exact d.before 1 2 8 (by decide)
  · exact d.after 1 2 8 (by decide)
  · exact d.before 1 2 9 (by decide)
  · exact d.after 1 2 9 (by decide)
  · exact d.after 1 3 0 (by decide)
  · exact d.before 1 3 1 (by decide)
  · exact d.after 1 3 1 (by decide)
  · exact d.before 1 3 2 (by decide)
  · exact d.after 1 3 2 (by decide)
  · exact d.before 1 3 3 (by decide)
  · exact d.after 1 3 3 (by decide)
  · exact d.before 1 3 4 (by decide)
  · exact d.after 1 3 4 (by decide)
  · exact d.before 1 3 5 (by decide)
  · exact d.after 1 3 5 (by decide)
  · exact d.before 1 3 6 (by decide)
  · exact d.after 1 3 6 (by decide)
  · exact d.before 1 3 7 (by decide)
  · exact d.after 1 3 7 (by decide)
  · exact d.before 1 3 8 (by decide)
  · exact d.after 1 3 8 (by decide)
  · exact d.before 1 3 9 (by decide)
  · exact d.before 1 4 1 (by decide)
  · exact d.after 1 4 1 (by decide)
  · exact d.before 1 4 2 (by decide)
  · exact d.after 1 4 2 (by decide)
  · exact d.before 1 4 3 (by decide)
  · exact d.after 1 4 3 (by decide)
  · exact d.before 1 4 4 (by decide)
  · exact d.after 1 4 4 (by decide)
  · exact d.before 1 4 5 (by decide)
  · exact d.after 1 4 5 (by decide)
  · exact d.before 1 4 6 (by decide)
  · exact d.after 1 4 6 (by decide)
  · exact d.before 1 4 7 (by decide)
  · exact d.after 1 4 7 (by decide)
  · exact d.before 1 4 8 (by decide)
  · exact d.after 1 4 8 (by decide)
  · exact d.before 2 3 0 (by decide)
  · exact d.after 2 3 0 (by decide)
  · exact d.before 2 3 1 (by decide)
  · exact d.after 2 3 1 (by decide)
  · exact d.before 2 3 2 (by decide)
  · exact d.after 2 3 2 (by decide)
  · exact d.before 2 3 3 (by decide)
  · exact d.after 2 3 3 (by decide)
  · exact d.before 2 3 4 (by decide)
  · exact d.after 2 3 4 (by decide)
  · exact d.before 2 3 5 (by decide)
  · exact d.after 2 3 5 (by decide)
  · exact d.before 2 3 6 (by decide)
  · exact d.after 2 3 6 (by decide)
  · exact d.before 2 3 7 (by decide)
  · exact d.after 2 3 7 (by decide)
  · exact d.before 2 3 8 (by decide)
  · exact d.after 2 3 8 (by decide)
  · exact d.before 2 3 9 (by decide)
  · exact d.after 2 3 9 (by decide)
  · exact d.before 2 4 1 (by decide)
  · exact d.after 2 4 1 (by decide)
  · exact d.before 2 4 2 (by decide)
  · exact d.after 2 4 2 (by decide)
  · exact d.before 2 4 3 (by decide)
  · exact d.after 2 4 3 (by decide)
  · exact d.before 2 4 4 (by decide)
  · exact d.after 2 4 4 (by decide)
  · exact d.before 2 4 5 (by decide)
  · exact d.after 2 4 5 (by decide)
  · exact d.before 2 4 6 (by decide)
  · exact d.after 2 4 6 (by decide)
  · exact d.before 2 4 7 (by decide)
  · exact d.after 2 4 7 (by decide)
  · exact d.before 2 4 8 (by decide)
  · exact d.after 2 4 8 (by decide)
  · exact d.before 3 4 0 (by decide)
  · exact d.after 3 4 0 (by decide)
  · exact d.before 3 4 1 (by decide)
  · exact d.after 3 4 1 (by decide)
  · exact d.before 3 4 2 (by decide)
  · exact d.after 3 4 2 (by decide)
  · exact d.before 3 4 3 (by decide)
  · exact d.after 3 4 3 (by decide)
  · exact d.before 3 4 4 (by decide)
  · exact d.after 3 4 4 (by decide)
  · exact d.before 3 4 5 (by decide)
  · exact d.after 3 4 5 (by decide)
  · exact d.before 3 4 6 (by decide)
  · exact d.after 3 4 6 (by decide)
  · exact d.before 3 4 7 (by decide)
  · exact d.after 3 4 7 (by decide)
  · exact d.before 3 4 8 (by decide)
  · exact d.after 3 4 8 (by decide)
  · exact d.before 3 4 9 (by decide)
  · exact d.after 3 4 9 (by decide)
  · exact d.left 0 2 0 1 2 (by decide) (by decide) (by decide)
  · exact d.left 0 2 0 1 8 (by decide) (by decide) (by decide)
  · exact d.left 0 3 0 1 2 (by decide) (by decide) (by decide)
  · exact d.left 0 3 0 1 8 (by decide) (by decide) (by decide)
  · exact d.left 0 4 0 1 4 (by decide) (by decide) (by decide)
  · exact d.right 1 2 0 1 0 (by decide) (by decide) (by decide)
  · exact d.right 1 2 0 1 10 (by decide) (by decide) (by decide)
  · exact d.right 1 4 0 1 4 (by decide) (by decide) (by decide)
  · exact d.right 1 4 0 1 6 (by decide) (by decide) (by decide)
  · exact d.left 0 1 0 2 2 (by decide) (by decide) (by decide)
  · exact d.left 0 1 0 2 8 (by decide) (by decide) (by decide)
  · exact d.left 0 3 0 2 2 (by decide) (by decide) (by decide)
  · exact d.left 0 3 0 2 4 (by decide) (by decide) (by decide)
  · exact d.left 0 3 0 2 6 (by decide) (by decide) (by decide)
  · exact d.left 0 3 0 2 8 (by decide) (by decide) (by decide)
  · exact d.right 2 3 0 2 0 (by decide) (by decide) (by decide)
  · exact d.right 2 3 0 2 10 (by decide) (by decide) (by decide)
  · exact d.right 2 4 0 2 4 (by decide) (by decide) (by decide)
  · exact d.right 2 4 0 2 6 (by decide) (by decide) (by decide)
  · exact d.left 0 1 0 3 2 (by decide) (by decide) (by decide)
  · exact d.left 0 1 0 3 8 (by decide) (by decide) (by decide)
  · exact d.left 0 4 0 3 4 (by decide) (by decide) (by decide)
  · exact d.left 0 4 0 3 6 (by decide) (by decide) (by decide)
  · exact d.right 3 4 0 3 0 (by decide) (by decide) (by decide)
  · exact d.right 3 4 0 3 4 (by decide) (by decide) (by decide)
  · exact d.right 3 4 0 3 6 (by decide) (by decide) (by decide)
  · exact d.right 3 4 0 3 10 (by decide) (by decide) (by decide)
  · exact d.left 0 1 1 2 3 (by decide) (by decide) (by decide)
  · exact d.left 0 1 1 2 7 (by decide) (by decide) (by decide)
  · exact d.left 1 3 1 2 2 (by decide) (by decide) (by decide)
  · exact d.left 1 3 1 2 8 (by decide) (by decide) (by decide)
  · exact d.right 2 3 1 2 0 (by decide) (by decide) (by decide)
  · exact d.right 2 3 1 2 4 (by decide) (by decide) (by decide)
  · exact d.right 2 3 1 2 6 (by decide) (by decide) (by decide)
  · exact d.right 2 3 1 2 10 (by decide) (by decide) (by decide)
  · exact d.right 2 4 1 2 4 (by decide) (by decide) (by decide)
  · exact d.right 2 4 1 2 6 (by decide) (by decide) (by decide)
  · exact d.left 0 1 1 3 3 (by decide) (by decide) (by decide)
  · exact d.left 0 1 1 3 7 (by decide) (by decide) (by decide)
  · exact d.left 1 4 1 3 4 (by decide) (by decide) (by decide)
  · exact d.left 1 4 1 3 6 (by decide) (by decide) (by decide)
  · exact d.right 3 4 1 3 0 (by decide) (by decide) (by decide)
  · exact d.right 3 4 1 3 4 (by decide) (by decide) (by decide)
  · exact d.right 3 4 1 3 6 (by decide) (by decide) (by decide)
  · exact d.right 3 4 1 3 10 (by decide) (by decide) (by decide)
  · exact d.left 0 2 2 3 3 (by decide) (by decide) (by decide)
  · exact d.left 0 2 2 3 7 (by decide) (by decide) (by decide)
  · exact d.left 2 4 2 3 4 (by decide) (by decide) (by decide)
  · exact d.left 2 4 2 3 6 (by decide) (by decide) (by decide)
  · exact d.right 0 3 2 3 5 (by decide) (by decide) (by decide)
  · exact d.right 1 3 2 3 3 (by decide) (by decide) (by decide)
  · exact d.right 1 3 2 3 7 (by decide) (by decide) (by decide)
  · exact d.right 3 4 2 3 0 (by decide) (by decide) (by decide)
  · exact d.right 3 4 2 3 4 (by decide) (by decide) (by decide)
  · exact d.right 3 4 2 3 6 (by decide) (by decide) (by decide)
  · exact d.right 3 4 2 3 10 (by decide) (by decide) (by decide)
  · exact d.left 0 3 3 4 3 (by decide) (by decide) (by decide)
  · exact d.left 0 3 3 4 7 (by decide) (by decide) (by decide)
  · exact d.left 1 3 3 4 3 (by decide) (by decide) (by decide)
  · exact d.left 1 3 3 4 7 (by decide) (by decide) (by decide)
  · exact d.right 0 4 3 4 1 (by decide) (by decide) (by decide)
  · exact d.right 0 4 3 4 5 (by decide) (by decide) (by decide)
  · exact d.right 0 4 3 4 9 (by decide) (by decide) (by decide)
  · exact d.right 1 4 3 4 1 (by decide) (by decide) (by decide)
  · exact d.right 1 4 3 4 5 (by decide) (by decide) (by decide)
  · exact d.right 1 4 3 4 9 (by decide) (by decide) (by decide)
  · exact d.right 2 4 3 4 1 (by decide) (by decide) (by decide)
  · exact d.right 2 4 3 4 5 (by decide) (by decide) (by decide)
  · exact d.right 2 4 3 4 9 (by decide) (by decide) (by decide)
/-- No five vertices can realize the marked interaction pattern in every pair. -/
theorem markedPatternGraph_cliqueFree {V : Type*} (first : V → ℕ) (coord box : V → Set ℕ) :
    (markedPatternGraph first coord box).CliqueFree 5 := by
  classical
  intro s hs
  have hinj : Set.InjOn first (s : Set V) := by
    intro x hx y hy he
    by_contra hxy
    have ha := hs.isClique hx hy hxy
    rcases ha.2 with h | h
    · exact h.1.ne he
    · exact h.1.ne he.symm
  let t := s.image first
  have hcard : t.card = 5 := (Finset.card_image_of_injOn hinj).trans hs.card_eq
  let ord := t.orderEmbOfFin hcard
  have hm (i : Fin 5) : ∃ x ∈ s, first x = ord i :=
    Finset.mem_image.mp (t.orderEmbOfFin_mem hcard i)
  choose v hv ho using hm
  apply fiveRunsImpossible
  apply (runsOfFive coord box v ?_).some
  intro i j hij
  have hlt : first (v i) < first (v j) := by simpa only [ho] using ord.strictMono hij
  have hne : v i ≠ v j := fun eq => hlt.ne (congrArg first eq)
  rcases (hs.isClique (hv i) (hv j) hne).2 with h | h
  · exact h.2
  · exact (hlt.asymm h.1).elim

/-- The blue pattern graph has no five-clique and its complement has no full-order clique. -/
theorem neg_part : ¬ Erdos118.OrdinalRamsey target target 5 := by
  intro h
  exact patternGraph_no_independentCopy ((target_ramsey_iff.{0} 5).mp h patternGraph
    (markedPatternGraph_cliqueFree _ _ _))


end OMA.E118

theorem OMA.solution : OMA.R_Erdos118_erdos_118_R1.H2 :=
  OMA.E118.neg_part
