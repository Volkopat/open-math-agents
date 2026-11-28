import FormalConjectures.Wikipedia.TarskiExponentialFunctionProblem
import Mathlib.Computability.Primrec.List
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Polynomial.Roots

/-!
# Tarski's Theorem (Decidability of the Real Ordered Field)

Proof of `TarskiExponentialFunctionProblem.isDecidable_completeTheory_real_orderedField`
via Cohen-Hormander quantifier elimination directly over `ℝ`, proved `Primrec` (hence
`Computable`) over Mathlib's Godel encoding of first-order sentences.
-/

-- Problem: Tarski's theorem.
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/TarskiExponentialFunctionProblem.lean:66 (declaration TarskiExponentialFunctionProblem.isDecidable_completeTheory_real_orderedField)
-- Credit: @Andyi955

namespace TarskiProof

open FirstOrder

/- Section 0: Generic Primrec helpers -/

lemma primrec_ite_bool {α β : Type*} [Primcodable α] [Primcodable β]
    {c : α → Bool} {f g : α → β} (hc : Primrec c) (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => if c a = true then f a else g a :=
  (Primrec.cond hc hf hg).of_eq fun a => by cases h : c a <;> simp [h]

lemma primrec_list_filter {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).filter (p a) := by
  have hcond : Primrec₂ fun a b => if p a b = true then some b else none :=
    (primrec_ite_bool hp (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂
  have h1 : Primrec fun a => (f a).filterMap (fun b => if p a b = true then some b else none) :=
    Primrec.listFilterMap hf hcond
  refine h1.of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons b l ih =>
    simp only [List.filterMap_cons, List.filter_cons]
    cases p a b <;> simp [ih]

lemma primrec_list_any {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).any (p a) := by
  have hstep : Primrec₂ fun a (x : Bool × β) => x.1 || p a x.2 := by
    refine (Primrec.cond (Primrec.fst.comp Primrec.snd) (Primrec.const true)
      (hp.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).of_eq ?_
    rintro ⟨a, ⟨b1, b2⟩⟩
    cases b1 <;> rfl
  have h1 : Primrec fun a => (f a).foldl (fun acc b => acc || p a b) false :=
    Primrec.list_foldl hf (Primrec.const false) hstep
  refine h1.of_eq fun a => ?_
  have key : ∀ (l : List β) (init : Bool),
      l.foldl (fun acc b => acc || p a b) init = (init || l.any (p a)) := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons b t ih =>
      intro init
      simp only [List.foldl_cons, List.any_cons, ih, Bool.or_assoc]
  simpa using key (f a) false

lemma primrec_list_all {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).all (p a) := by
  have hstep : Primrec₂ fun a (x : Bool × β) => x.1 && p a x.2 := by
    refine (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (hp.comp Primrec.fst (Primrec.snd.comp Primrec.snd)) (Primrec.const false)).of_eq ?_
    rintro ⟨a, ⟨b1, b2⟩⟩
    cases b1 <;> rfl
  have h1 : Primrec fun a => (f a).foldl (fun acc b => acc && p a b) true :=
    Primrec.list_foldl hf (Primrec.const true) hstep
  refine h1.of_eq fun a => ?_
  have key : ∀ (l : List β) (init : Bool),
      l.foldl (fun acc b => acc && p a b) init = (init && l.all (p a)) := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons b t ih =>
      intro init
      simp only [List.foldl_cons, List.all_cons, ih, Bool.and_assoc]
  simpa using key (f a) true

lemma primrec_iterate {α β : Type*} [Primcodable α] [Primcodable β]
    {n : α → ℕ} {x : α → β} {f : α → β → β}
    (hn : Primrec n) (hx : Primrec x) (hf : Primrec₂ f) :
    Primrec fun a => (f a)^[n a] (x a) := by
  have h1 : Primrec fun a => (n a).rec (motive := fun _ => β) (x a) (fun _ ih => f a ih) :=
    Primrec.nat_rec' hn hx (hf.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to₂
  refine h1.of_eq fun a => ?_
  generalize n a = k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', ← ih]

lemma primrec_bool_not : Primrec Bool.not := Primrec.dom_bool Bool.not
lemma primrec_bool_and : Primrec₂ Bool.and := Primrec.dom_bool₂ Bool.and
lemma primrec_bool_or : Primrec₂ Bool.or := Primrec.dom_bool₂ Bool.or

lemma primrec_list_headD {α : Type*} [Primcodable α] (d : α) :
    Primrec fun l : List α => l.headD d := by
  have h1 : Primrec fun l : List α => l.getD 0 d :=
    (Primrec.list_getD d).comp Primrec.id (Primrec.const 0)
  refine h1.of_eq fun l => ?_
  cases l <;> rfl

lemma primrec_bne {α : Type*} [Primcodable α] [DecidableEq α] :
    Primrec₂ (fun a b : α => a != b) :=
  (primrec_bool_not.comp Primrec.beq).to₂

/- Section 1: Signs, IntPair, MPoly, UPoly -/

noncomputable def realSign (x : ℝ) : ℕ :=
  if x = 0 then 0 else if 0 < x then 1 else 2

def negSign (s : ℕ) : ℕ :=
  if s = 1 then 2 else if s = 2 then 1 else 0

lemma primrec_negSign : Primrec negSign :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const 2)
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 2)) (Primrec.const 1) (Primrec.const 0))

lemma realSign_eq_zero_iff (x : ℝ) : realSign x = 0 ↔ x = 0 := by
  unfold realSign
  split_ifs <;> simp_all

lemma realSign_eq_one_iff (x : ℝ) : realSign x = 1 ↔ 0 < x := by
  unfold realSign
  split_ifs with h1 h2
  · simp [h1]
  · simp [h2]
  · simp [h2]

lemma realSign_eq_two_iff (x : ℝ) : realSign x = 2 ↔ x < 0 := by
  unfold realSign
  split_ifs with h1 h2
  · simp [h1]
  · exact ⟨fun h => (by cases h), fun h => absurd (lt_trans h h2) (lt_irrefl _)⟩
  · constructor
    · intro _; exact lt_of_le_of_ne (not_lt.mp h2) h1
    · intro _; rfl

lemma realSign_lt_three (x : ℝ) : realSign x < 3 := by
  unfold realSign; split_ifs <;> omega

lemma realSign_neg (x : ℝ) : realSign (-x) = negSign (realSign x) := by
  unfold realSign negSign
  rcases lt_trichotomy x 0 with h | rfl | h
  · have h1 : -x ≠ 0 := by linarith
    have h2 : 0 < -x := by linarith
    have h3 : x ≠ 0 := ne_of_lt h
    have h4 : ¬ (0 < x) := not_lt.mpr (le_of_lt h)
    simp [h1, h2, h3, h4]
  · simp
  · have h1 : -x ≠ 0 := by linarith
    have h2 : ¬ (0 < -x) := by linarith
    have h3 : x ≠ 0 := ne_of_gt h
    simp [h1, h2, h3, h]

lemma realSign_mul_pos {a x : ℝ} (ha : 0 < a) : realSign (a * x) = realSign x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [(realSign_eq_two_iff _).2 (mul_neg_of_pos_of_neg ha hx), (realSign_eq_two_iff _).2 hx]
  · simp [realSign]
  · rw [(realSign_eq_one_iff _).2 (mul_pos ha hx), (realSign_eq_one_iff _).2 hx]

lemma realSign_mul_neg {a x : ℝ} (ha : a < 0) : realSign (a * x) = negSign (realSign x) := by
  have : a * x = (-a) * (-x) := by ring
  rw [this, realSign_mul_pos (by linarith), realSign_neg]

lemma realSign_eq_of_eq_sign {x y : ℝ} (h : realSign x = realSign y) :
    (x = 0 ↔ y = 0) ∧ (0 < x ↔ 0 < y) ∧ (x < 0 ↔ y < 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← realSign_eq_zero_iff, ← realSign_eq_zero_iff, h]
  · rw [← realSign_eq_one_iff, ← realSign_eq_one_iff, h]
  · rw [← realSign_eq_two_iff, ← realSign_eq_two_iff, h]

abbrev IntPair := ℕ × ℕ

def addZ (z₁ z₂ : IntPair) : IntPair := (z₁.1 + z₂.1, z₁.2 + z₂.2)
def negZ (z : IntPair) : IntPair := (z.2, z.1)
def mulZ (z₁ z₂ : IntPair) : IntPair :=
  (z₁.1 * z₂.1 + z₁.2 * z₂.2, z₁.1 * z₂.2 + z₁.2 * z₂.1)
def scaleNatZ (k : ℕ) (z : IntPair) : IntPair := (k * z.1, k * z.2)
def signZ (z : IntPair) : ℕ :=
  if z.1 = z.2 then 0 else if z.2 < z.1 then 1 else 2

noncomputable def evalZ (z : IntPair) : ℝ := (z.1 : ℝ) - (z.2 : ℝ)

lemma primrec_addZ : Primrec₂ addZ :=
  (Primrec.pair
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂

lemma primrec_negZ : Primrec negZ := Primrec.pair Primrec.snd Primrec.fst

lemma primrec_mulZ : Primrec₂ mulZ :=
  (Primrec.pair
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))).to₂

lemma primrec_scaleNatZ : Primrec₂ scaleNatZ :=
  (Primrec.pair
    (Primrec.nat_mul.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.nat_mul.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).to₂

lemma primrec_signZ : Primrec signZ :=
  Primrec.ite (Primrec.eq.comp Primrec.fst Primrec.snd) (Primrec.const 0)
    (Primrec.ite (Primrec.nat_lt.comp Primrec.snd Primrec.fst) (Primrec.const 1) (Primrec.const 2))

@[simp] lemma evalZ_add (z₁ z₂ : IntPair) : evalZ (addZ z₁ z₂) = evalZ z₁ + evalZ z₂ := by
  simp [evalZ, addZ]; ring

@[simp] lemma evalZ_neg (z : IntPair) : evalZ (negZ z) = -evalZ z := by
  simp [evalZ, negZ]

@[simp] lemma evalZ_mul (z₁ z₂ : IntPair) : evalZ (mulZ z₁ z₂) = evalZ z₁ * evalZ z₂ := by
  simp [evalZ, mulZ]; ring

@[simp] lemma evalZ_scaleNat (k : ℕ) (z : IntPair) :
    evalZ (scaleNatZ k z) = (k : ℝ) * evalZ z := by
  simp [evalZ, scaleNatZ]; ring

lemma signZ_eq_realSign (z : IntPair) : signZ z = realSign (evalZ z) := by
  unfold signZ realSign evalZ
  by_cases h1 : z.1 = z.2
  · simp [h1]
  · have h1r : (z.1 : ℝ) - (z.2 : ℝ) ≠ 0 := by
      intro h; apply h1; exact Nat.cast_injective (sub_eq_zero.mp h)
    by_cases h2 : z.2 < z.1
    · have h2r : (0 : ℝ) < (z.1 : ℝ) - (z.2 : ℝ) := by
        have : (z.2 : ℝ) < (z.1 : ℝ) := Nat.cast_lt.mpr h2
        linarith
      simp [h1, h2, h1r, h2r]
    · have h2r : ¬ ((0 : ℝ) < (z.1 : ℝ) - (z.2 : ℝ)) := by
        have : (z.1 : ℝ) ≤ (z.2 : ℝ) := Nat.cast_le.mpr (not_lt.mp h2)
        linarith
      simp [h1, h2, h1r, h2r]

/- Multivariate Polynomials `MPoly` -/

abbrev MPoly := List (List ℕ × IntPair)

def addExps (e₁ e₂ : List ℕ) : List ℕ :=
  (List.range (max e₁.length e₂.length)).map fun i => e₁.getD i 0 + e₂.getD i 0

def zeroM : MPoly := []
def oneM : MPoly := [([], (1, 0))]
def varM (v : ℕ) : MPoly := [((List.range (v + 1)).map fun i => if i = v then 1 else 0, (1, 0))]
def addM (p q : MPoly) : MPoly := p ++ q
def negM (p : MPoly) : MPoly := p.map fun t => (t.1, negZ t.2)
def subM (p q : MPoly) : MPoly := addM p (negM q)
def mulM (p q : MPoly) : MPoly :=
  p.flatMap fun t₁ => q.map fun t₂ => (addExps t₁.1 t₂.1, mulZ t₁.2 t₂.2)
def scaleNatM (k : ℕ) (p : MPoly) : MPoly :=
  p.map fun t => (t.1, scaleNatZ k t.2)

def evalZeroZ (p : MPoly) : IntPair :=
  p.foldl (fun acc t => if t.1.all (fun e => e == 0) then addZ acc t.2 else acc) (0, 0)

def evalZeroSign (p : MPoly) : ℕ := signZ (evalZeroZ p)

lemma primrec_addExps : Primrec₂ addExps := by
  unfold addExps
  refine (Primrec.list_map
    (Primrec.list_range.comp
      (Primrec.nat_max.comp (Primrec.list_length.comp Primrec.fst)
        (Primrec.list_length.comp Primrec.snd)))
    (Primrec.nat_add.comp
      ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂).to₂

lemma primrec_varM : Primrec varM := by
  unfold varM
  have h1 : Primrec fun v : ℕ => (List.range (v + 1)).map (fun i => if i = v then 1 else 0) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 1)))
      (Primrec.ite (Primrec.eq.comp Primrec.snd Primrec.fst) (Primrec.const 1)
        (Primrec.const 0)).to₂
  exact Primrec.list_cons.comp (Primrec.pair h1 (Primrec.const (1, 0))) (Primrec.const [])

lemma primrec_addM : Primrec₂ addM := Primrec.list_append

lemma primrec_negM : Primrec negM :=
  Primrec.list_map Primrec.id
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (primrec_negZ.comp (Primrec.snd.comp Primrec.snd))).to₂

lemma primrec_subM : Primrec₂ subM :=
  (primrec_addM.comp Primrec.fst (primrec_negM.comp Primrec.snd)).to₂

lemma primrec_mulM : Primrec₂ mulM := by
  unfold mulM
  have hinner : Primrec₂ (fun (x : (MPoly × MPoly) × (List ℕ × IntPair)) (t₂ : List ℕ × IntPair) =>
      (addExps x.2.1 t₂.1, mulZ x.2.2 t₂.2)) :=
    (Primrec.pair
      (primrec_addExps.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd))
      (primrec_mulZ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))).to₂
  have hmid : Primrec₂ (fun (pq : MPoly × MPoly) (t₁ : List ℕ × IntPair) =>
      pq.2.map fun t₂ => (addExps t₁.1 t₂.1, mulZ t₁.2 t₂.2)) :=
    (Primrec.list_map (Primrec.snd.comp Primrec.fst) hinner).to₂
  exact (Primrec.list_flatMap Primrec.fst hmid).to₂

lemma primrec_scaleNatM : Primrec₂ scaleNatM :=
  (Primrec.list_map Primrec.snd
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (primrec_scaleNatZ.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))).to₂).to₂

lemma primrec_evalZeroZ : Primrec evalZeroZ := by
  unfold evalZeroZ
  have hall : Primrec fun e : List ℕ => e.all (fun x => x == 0) :=
    primrec_list_all Primrec.id (Primrec.beq.comp Primrec.snd (Primrec.const 0)).to₂
  have hstep : Primrec₂ fun (_ : MPoly) (x : IntPair × (List ℕ × IntPair)) =>
      if x.2.1.all (fun e => e == 0) = true then addZ x.1 x.2.2 else x.1 :=
    (primrec_ite_bool (hall.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (primrec_addZ.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.fst.comp Primrec.snd)).to₂
  exact Primrec.list_foldl Primrec.id (Primrec.const (0, 0)) hstep

lemma primrec_evalZeroSign : Primrec evalZeroSign :=
  primrec_signZ.comp primrec_evalZeroZ

noncomputable def evalMon (e : List ℕ) (ρ : ℕ → ℝ) : ℝ :=
  ∏ i ∈ Finset.range e.length, (ρ i) ^ (e.getD i 0)

noncomputable def evalM (p : MPoly) (ρ : ℕ → ℝ) : ℝ :=
  (p.map fun t => evalZ t.2 * evalMon t.1 ρ).sum

@[simp] lemma evalM_nil (ρ : ℕ → ℝ) : evalM [] ρ = 0 := by simp [evalM]
@[simp] lemma evalM_zero (ρ : ℕ → ℝ) : evalM zeroM ρ = 0 := by simp [evalM, zeroM]

@[simp] lemma evalM_one (ρ : ℕ → ℝ) : evalM oneM ρ = 1 := by
  simp [evalM, oneM, evalZ, evalMon]

lemma evalMon_eq_range (e : List ℕ) (ρ : ℕ → ℝ) {M : ℕ} (hM : e.length ≤ M) :
    evalMon e ρ = ∏ i ∈ Finset.range M, (ρ i) ^ (e.getD i 0) := by
  unfold evalMon
  apply Finset.prod_subset (Finset.range_mono hM)
  intro i _ hi
  simp only [Finset.mem_range, not_lt] at hi
  have hget : e.getD i 0 = 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rw [hget, pow_zero]

lemma evalMon_addExps (e₁ e₂ : List ℕ) (ρ : ℕ → ℝ) :
    evalMon (addExps e₁ e₂) ρ = evalMon e₁ ρ * evalMon e₂ ρ := by
  set M := max e₁.length e₂.length
  have hlen : (addExps e₁ e₂).length = M := by simp [addExps, M]
  rw [evalMon_eq_range e₁ ρ (le_max_left _ _), evalMon_eq_range e₂ ρ (le_max_right _ _),
    ← Finset.prod_mul_distrib]
  unfold evalMon
  rw [hlen]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hget : (addExps e₁ e₂).getD i 0 = e₁.getD i 0 + e₂.getD i 0 := by
    simp [addExps, List.getD_eq_getElem?_getD, hi, M]
  rw [hget, pow_add]

@[simp] lemma evalM_var (v : ℕ) (ρ : ℕ → ℝ) : evalM (varM v) ρ = ρ v := by
  simp only [evalM, varM, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    evalZ, Nat.cast_one, Nat.cast_zero, sub_zero, one_mul]
  unfold evalMon
  have hlen : ((List.range (v + 1)).map fun i => if i = v then 1 else 0).length = v + 1 := by simp
  rw [hlen, Finset.prod_eq_single v]
  · have hget : ((List.range (v + 1)).map fun i => if i = v then 1 else 0).getD v 0 = 1 := by
      simp [List.getD_eq_getElem?_getD]
    rw [hget, pow_one]
  · intro i hi hiv
    rw [Finset.mem_range] at hi
    have hget : ((List.range (v + 1)).map fun i => if i = v then 1 else 0).getD i 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, hi, hiv]
    rw [hget, pow_zero]
  · intro hv; simp at hv

@[simp] lemma evalM_add (p q : MPoly) (ρ : ℕ → ℝ) :
    evalM (addM p q) ρ = evalM p ρ + evalM q ρ := by
  simp [evalM, addM, List.map_append, List.sum_append]

@[simp] lemma evalM_neg (p : MPoly) (ρ : ℕ → ℝ) :
    evalM (negM p) ρ = -evalM p ρ := by
  induction p with
  | nil => simp [evalM, negM]
  | cons t ts ih =>
    simp only [evalM, negM, List.map_cons, List.sum_cons, evalZ_neg, neg_mul] at ih ⊢
    linarith

@[simp] lemma evalM_sub (p q : MPoly) (ρ : ℕ → ℝ) :
    evalM (subM p q) ρ = evalM p ρ - evalM q ρ := by
  simp [subM, sub_eq_add_neg]

@[simp] lemma evalM_scaleNat (k : ℕ) (p : MPoly) (ρ : ℕ → ℝ) :
    evalM (scaleNatM k p) ρ = (k : ℝ) * evalM p ρ := by
  induction p with
  | nil => simp [evalM, scaleNatM]
  | cons t ts ih =>
    simp only [evalM, scaleNatM, List.map_cons, List.sum_cons, evalZ_scaleNat] at ih ⊢
    linarith

@[simp] lemma evalM_mul (p q : MPoly) (ρ : ℕ → ℝ) :
    evalM (mulM p q) ρ = evalM p ρ * evalM q ρ := by
  have hsingle : ∀ (t₁ : List ℕ × IntPair) (l : MPoly),
      (List.map (fun t => evalZ t.2 * evalMon t.1 ρ)
        (l.map fun t₂ => (addExps t₁.1 t₂.1, mulZ t₁.2 t₂.2))).sum =
      (evalZ t₁.2 * evalMon t₁.1 ρ) * (l.map fun t => evalZ t.2 * evalMon t.1 ρ).sum := by
    intro t₁ l
    induction l with
    | nil => simp
    | cons t₂ ls ihl =>
      simp only [List.map_cons, List.sum_cons, evalZ_mul, evalMon_addExps] at ihl ⊢
      rw [ihl]; ring
  induction p with
  | nil => simp [evalM, mulM]
  | cons t₁ ts ih =>
    simp only [evalM, mulM, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, hsingle t₁ q]; ring

lemma evalMon_zero (e : List ℕ) :
    evalMon e (fun _ => (0 : ℝ)) = if e.all (fun x => x == 0) then 1 else 0 := by
  unfold evalMon
  by_cases hall : e.all (fun x => x == 0) = true
  · rw [if_pos hall]
    apply Finset.prod_eq_one
    intro i hi
    rw [Finset.mem_range] at hi
    rw [List.all_eq_true] at hall
    have h0 : e[i] = 0 := beq_iff_eq.mp (hall e[i] (List.getElem_mem hi))
    have hget : e.getD i 0 = 0 := by simp [List.getD_eq_getElem?_getD, hi, h0]
    rw [hget, pow_zero]
  · rw [if_neg hall]
    have hall' : ¬ ∀ x ∈ e, x = 0 := by
      intro h; apply hall; rw [List.all_eq_true]; intro x hx; exact beq_iff_eq.mpr (h x hx)
    push Not at hall'
    obtain ⟨x, hx, hne⟩ := hall'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
    have hget : e.getD i 0 = e[i] := by simp [List.getD_eq_getElem?_getD, hi]
    rw [hget, zero_pow hne]

lemma evalZ_evalZeroZ (p : MPoly) : evalZ (evalZeroZ p) = evalM p (fun _ => 0) := by
  unfold evalZeroZ
  have key : ∀ (l : MPoly) (init : IntPair),
      evalZ (l.foldl (fun acc t => if t.1.all (fun e => e == 0) then addZ acc t.2 else acc) init) =
        evalZ init + evalM l (fun _ => 0) := by
    intro l
    induction l with
    | nil => intro init; simp [evalM]
    | cons t ts ih =>
      intro init
      simp only [List.foldl_cons, ih, evalM, List.map_cons, List.sum_cons, evalMon_zero]
      split_ifs
      · simp; ring
      · simp
  simpa [evalZ] using key p (0, 0)

lemma evalZeroSign_eq (p : MPoly) : evalZeroSign p = realSign (evalM p (fun _ => 0)) := by
  rw [evalZeroSign, signZ_eq_realSign, evalZ_evalZeroZ]

/- Variable independence and Univariate Polynomials `UPoly` -/

def IndepOf (v : ℕ) (p : MPoly) : Prop := ∀ t ∈ p, t.1.getD v 0 = 0

lemma evalMon_update_of_getD_zero {v : ℕ} {e : List ℕ} (he : e.getD v 0 = 0)
    (ρ : ℕ → ℝ) (x : ℝ) :
    evalMon e (Function.update ρ v x) = evalMon e ρ := by
  unfold evalMon
  apply Finset.prod_congr rfl
  intro i _
  by_cases hiv : i = v
  · subst hiv; rw [he, pow_zero, pow_zero]
  · rw [Function.update_of_ne hiv]

lemma evalM_update_of_indepOf {v : ℕ} {p : MPoly} (hp : IndepOf v p) (ρ : ℕ → ℝ) (x : ℝ) :
    evalM p (Function.update ρ v x) = evalM p ρ := by
  induction p with
  | nil => simp [evalM]
  | cons t ts ih =>
    simp only [evalM, List.map_cons, List.sum_cons] at ih ⊢
    rw [evalMon_update_of_getD_zero (hp t (List.mem_cons_self ..)),
      ih (fun s hs => hp s (List.mem_cons_of_mem _ hs))]

lemma indepOf_zero (v : ℕ) : IndepOf v zeroM := by intro t ht; cases ht

lemma indepOf_add {v : ℕ} {p q : MPoly} (hp : IndepOf v p) (hq : IndepOf v q) :
    IndepOf v (addM p q) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact hp t h
  · exact hq t h

lemma indepOf_neg {v : ℕ} {p : MPoly} (hp : IndepOf v p) : IndepOf v (negM p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

lemma indepOf_scaleNat {v k : ℕ} {p : MPoly} (hp : IndepOf v p) : IndepOf v (scaleNatM k p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

lemma indepOf_mul {v : ℕ} {p q : MPoly} (hp : IndepOf v p) (hq : IndepOf v q) :
    IndepOf v (mulM p q) := by
  intro t ht
  obtain ⟨t₁, ht₁, ht'⟩ := List.mem_flatMap.mp ht
  obtain ⟨t₂, ht₂, rfl⟩ := List.mem_map.mp ht'
  dsimp only
  have h1 : t₁.1.getD v 0 = 0 := hp t₁ ht₁
  have h2 : t₂.1.getD v 0 = 0 := hq t₂ ht₂
  unfold addExps
  by_cases hv : v < max t₁.1.length t₂.1.length
  · rw [List.getD_eq_getElem _ _ (by simp [hv])]
    simp only [List.getElem_map, List.getElem_range]
    rw [h1, h2]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

abbrev UPoly := List MPoly

def IndepOfU (v : ℕ) (u : UPoly) : Prop := ∀ c ∈ u, IndepOf v c

def degAt (v : ℕ) (p : MPoly) : ℕ :=
  p.foldl (fun acc t => max acc (t.1.getD v 0)) 0

def zeroAt (v : ℕ) (e : List ℕ) : List ℕ :=
  (List.range e.length).map fun i => if i = v then 0 else e.getD i 0

def toUPoly (v : ℕ) (p : MPoly) : UPoly :=
  (List.range (degAt v p + 1)).map fun d =>
    (p.filter fun t => t.1.getD v 0 == d).map fun t => (zeroAt v t.1, t.2)

def lcU (u : UPoly) : MPoly := u.getD (u.length - 1) []
def redU (u : UPoly) : UPoly := (List.range (u.length - 1)).map fun i => u.getD i []
def derivU (u : UPoly) : UPoly :=
  (List.range (u.length - 1)).map fun i => scaleNatM (i + 1) (u.getD (i + 1) [])

def premStep (p q : UPoly) : UPoly :=
  let a := lcU p
  let b := lcU q
  let b2 := mulM b b
  let ba := mulM b a
  let sh := p.length - q.length
  (List.range (p.length - 1)).map fun i =>
    addM (mulM b2 (p.getD i []))
      (negM (if i < sh then [] else mulM ba (q.getD (i - sh) [])))

def prem2 (p q : UPoly) : UPoly :=
  (fun r => premStep r q)^[p.length - q.length + 1] p

lemma primrec_degAt : Primrec₂ degAt := by
  unfold degAt
  have hstep : Primrec₂ (fun (vp : ℕ × MPoly) (x : ℕ × (List ℕ × IntPair)) =>
      max x.1 (x.2.1.getD vp.1 0)) :=
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.fst))).to₂
  exact (Primrec.list_foldl Primrec.snd (Primrec.const 0) hstep).to₂

lemma primrec_zeroAt : Primrec₂ zeroAt := by
  unfold zeroAt
  have hfn : Primrec₂ (fun (ve : ℕ × List ℕ) (i : ℕ) => if i = ve.1 then 0 else ve.2.getD i 0) :=
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.fst.comp Primrec.fst)) (Primrec.const 0)
      ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
  exact (Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)) hfn).to₂

lemma primrec_toUPoly : Primrec₂ toUPoly := by
  unfold toUPoly
  have hfilt : Primrec fun x : (ℕ × MPoly) × ℕ =>
      x.1.2.filter (fun t => t.1.getD x.1.1 0 == x.2) :=
    primrec_list_filter (Primrec.snd.comp Primrec.fst)
      (Primrec.beq.comp
        ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.fst)).to₂
  have hinner : Primrec₂ (fun (x : (ℕ × MPoly) × ℕ) (t : List ℕ × IntPair) =>
      (zeroAt x.1.1 t.1, t.2)) :=
    (Primrec.pair
      (primrec_zeroAt.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_add.comp (primrec_degAt.comp Primrec.fst Primrec.snd)
      (Primrec.const 1)))
    (Primrec.list_map hfilt hinner).to₂).to₂

lemma primrec_lcU : Primrec lcU :=
  (Primrec.list_getD []).comp Primrec.id
    (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1))

lemma primrec_redU : Primrec redU :=
  Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)))
    ((Primrec.list_getD ([] : MPoly)).comp Primrec.fst Primrec.snd).to₂

lemma primrec_derivU : Primrec derivU :=
  Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)))
    (primrec_scaleNatM.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))
      ((Primrec.list_getD ([] : MPoly)).comp Primrec.fst
        (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)))).to₂

lemma primrec_premStep : Primrec₂ premStep := by
  unfold premStep
  have ha : Primrec fun x : (UPoly × UPoly) × ℕ => lcU x.1.1 :=
    primrec_lcU.comp (Primrec.fst.comp Primrec.fst)
  have hb : Primrec fun x : (UPoly × UPoly) × ℕ => lcU x.1.2 :=
    primrec_lcU.comp (Primrec.snd.comp Primrec.fst)
  have hb2 : Primrec fun x : (UPoly × UPoly) × ℕ => mulM (lcU x.1.2) (lcU x.1.2) :=
    primrec_mulM.comp hb hb
  have hba : Primrec fun x : (UPoly × UPoly) × ℕ => mulM (lcU x.1.2) (lcU x.1.1) :=
    primrec_mulM.comp hb ha
  have hsh : Primrec fun x : (UPoly × UPoly) × ℕ => x.1.1.length - x.1.2.length :=
    Primrec.nat_sub.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
  have hterm1 : Primrec fun x : (UPoly × UPoly) × ℕ =>
      mulM (mulM (lcU x.1.2) (lcU x.1.2)) (x.1.1.getD x.2 []) :=
    primrec_mulM.comp hb2 ((Primrec.list_getD ([] : MPoly)).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hterm2 : Primrec fun x : (UPoly × UPoly) × ℕ =>
      if x.2 < x.1.1.length - x.1.2.length then ([] : MPoly)
      else mulM (mulM (lcU x.1.2) (lcU x.1.1))
        (x.1.2.getD (x.2 - (x.1.1.length - x.1.2.length)) []) :=
    Primrec.ite (Primrec.nat_lt.comp Primrec.snd hsh) (Primrec.const ([] : MPoly))
      (primrec_mulM.comp hba
        ((Primrec.list_getD ([] : MPoly)).comp (Primrec.snd.comp Primrec.fst)
          (Primrec.nat_sub.comp Primrec.snd hsh)))
  have hbody : Primrec₂ fun (pq : UPoly × UPoly) (i : ℕ) =>
      addM (mulM (mulM (lcU pq.2) (lcU pq.2)) (pq.1.getD i []))
        (negM (if i < pq.1.length - pq.2.length then ([] : MPoly)
          else mulM (mulM (lcU pq.2) (lcU pq.1)) (pq.2.getD (i - (pq.1.length - pq.2.length)) []))) :=
    (primrec_addM.comp hterm1 (primrec_negM.comp hterm2)).to₂
  exact (Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.fst)
      (Primrec.const 1)))
    hbody).to₂

lemma primrec_prem2 : Primrec₂ prem2 := by
  unfold prem2
  exact (primrec_iterate
    (Primrec.nat_add.comp
      (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.fst)
        (Primrec.list_length.comp Primrec.snd))
      (Primrec.const 1))
    Primrec.fst
    (primrec_premStep.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).to₂

noncomputable def evalU (u : UPoly) (ρ : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range u.length, evalM (u.getD i []) ρ * x ^ i

lemma degAt_ge {v : ℕ} {p : MPoly} {t : List ℕ × IntPair} (ht : t ∈ p) :
    t.1.getD v 0 ≤ degAt v p := by
  unfold degAt
  have key : ∀ (l : MPoly) (init : ℕ),
      init ≤ l.foldl (fun acc s => max acc (s.1.getD v 0)) init ∧
      ∀ s ∈ l, s.1.getD v 0 ≤ l.foldl (fun acc s => max acc (s.1.getD v 0)) init := by
    intro l
    induction l with
    | nil => intro init; exact ⟨le_rfl, fun _ h => by cases h⟩
    | cons a ls ih =>
      intro init
      obtain ⟨h1, h2⟩ := ih (max init (a.1.getD v 0))
      refine ⟨le_trans (le_max_left _ _) h1, ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact le_trans (le_max_right _ _) h1
      · exact h2 s hs'
  exact (key p 0).2 t ht

lemma getD_zeroAt (v : ℕ) (e : List ℕ) (i : ℕ) :
    (zeroAt v e).getD i 0 = if i = v then 0 else e.getD i 0 := by
  unfold zeroAt
  by_cases hi : i < e.length
  · rw [List.getD_eq_getElem _ _ (by simp [hi])]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    rw [List.getD_eq_default e 0 (by omega)]
    split_ifs <;> rfl

lemma evalMon_update_eq_zeroAt (v : ℕ) (e : List ℕ) (ρ : ℕ → ℝ) (x : ℝ) :
    evalMon e (Function.update ρ v x) = evalMon (zeroAt v e) ρ * x ^ (e.getD v 0) := by
  set M := max e.length (v + 1)
  have hze_len : (zeroAt v e).length = e.length := by simp [zeroAt]
  have hle1 : e.length ≤ M := le_max_left _ _
  have hle2 : (zeroAt v e).length ≤ M := by rw [hze_len]; exact hle1
  rw [evalMon_eq_range e _ hle1, evalMon_eq_range (zeroAt v e) ρ hle2]
  have hvM : v ∈ Finset.range M :=
    Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self v) (le_max_right _ _))
  rw [← Finset.mul_prod_erase _ _ hvM, ← Finset.mul_prod_erase _ _ hvM]
  rw [Function.update_self, getD_zeroAt, if_pos rfl, pow_zero, one_mul, mul_comm (x ^ _)]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hiv : i ≠ v := (Finset.mem_erase.mp hi).1
  rw [Function.update_of_ne hiv, getD_zeroAt, if_neg hiv]

lemma indepOfU_toUPoly (v : ℕ) (p : MPoly) : IndepOfU v (toUPoly v p) := by
  intro c hc
  unfold toUPoly at hc
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc
  intro t ht
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
  rw [getD_zeroAt, if_pos rfl]

lemma evalU_toUPoly (v : ℕ) (p : MPoly) (ρ : ℕ → ℝ) (x : ℝ) :
    evalU (toUPoly v p) ρ x = evalM p (Function.update ρ v x) := by
  unfold evalU toUPoly
  have hlen : ((List.range (degAt v p + 1)).map fun d =>
      (p.filter fun t => t.1.getD v 0 == d).map fun t => (zeroAt v t.1, t.2)).length =
      degAt v p + 1 := by simp
  rw [hlen]
  have hterm : ∀ d ∈ Finset.range (degAt v p + 1),
      evalM (((List.range (degAt v p + 1)).map fun d =>
        (p.filter fun t => t.1.getD v 0 == d).map fun t => (zeroAt v t.1, t.2)).getD d []) ρ * x ^ d =
      ((p.filter fun t => t.1.getD v 0 == d).map
        fun t => evalZ t.2 * evalMon t.1 (Function.update ρ v x)).sum := by
    intro d hd
    rw [Finset.mem_range] at hd
    have hget : ((List.range (degAt v p + 1)).map fun d =>
        (p.filter fun t => t.1.getD v 0 == d).map fun t => (zeroAt v t.1, t.2)).getD d [] =
        (p.filter fun t => t.1.getD v 0 == d).map fun t => (zeroAt v t.1, t.2) := by
      rw [List.getD_eq_getElem _ _ (by simp [hd])]; simp [hd]
    rw [hget]
    unfold evalM
    have hfilt : ∀ l : MPoly, (∀ t ∈ l, t.1.getD v 0 = d) →
        (List.map (fun t => evalZ t.2 * evalMon t.1 ρ)
          (l.map fun t => (zeroAt v t.1, t.2))).sum * x ^ d =
        (l.map fun t => evalZ t.2 * evalMon t.1 (Function.update ρ v x)).sum := by
      intro l hl
      induction l with
      | nil => simp
      | cons t ts ih =>
        simp only [List.map_cons, List.sum_cons, add_mul]
        rw [ih (fun s hs => hl s (List.mem_cons_of_mem _ hs))]
        have htd := hl t (List.mem_cons_self ..)
        rw [evalMon_update_eq_zeroAt v t.1 ρ x, htd]; ring
    exact hfilt _ (fun t ht => beq_iff_eq.mp (List.mem_filter.mp ht).2)
  rw [Finset.sum_congr rfl hterm]
  have hsum_all : ∀ (l : MPoly), (∀ t ∈ l, t.1.getD v 0 ≤ degAt v p) →
      ∑ d ∈ Finset.range (degAt v p + 1),
        ((l.filter fun t => t.1.getD v 0 == d).map
          fun t => evalZ t.2 * evalMon t.1 (Function.update ρ v x)).sum =
      evalM l (Function.update ρ v x) := by
    intro l hl
    induction l with
    | nil => simp [evalM]
    | cons t ts ih =>
      simp only [List.filter_cons, evalM, List.map_cons, List.sum_cons] at ih ⊢
      have hsplit : ∀ d,
          ((if (t.1.getD v 0 == d) = true then t :: ts.filter (fun s => s.1.getD v 0 == d)
            else ts.filter (fun s => s.1.getD v 0 == d)).map
              fun s => evalZ s.2 * evalMon s.1 (Function.update ρ v x)).sum =
          (if t.1.getD v 0 = d then evalZ t.2 * evalMon t.1 (Function.update ρ v x) else 0) +
          ((ts.filter fun s => s.1.getD v 0 == d).map
            fun s => evalZ s.2 * evalMon s.1 (Function.update ρ v x)).sum := by
        intro d
        by_cases hd : t.1.getD v 0 = d
        · rw [if_pos (beq_iff_eq.mpr hd), if_pos hd, List.map_cons, List.sum_cons]
        · rw [if_neg (by intro h; exact hd (beq_iff_eq.mp h)), if_neg hd, zero_add]
      simp_rw [hsplit, Finset.sum_add_distrib]
      rw [ih (fun s hs => hl s (List.mem_cons_of_mem _ hs))]
      congr 1
      rw [Finset.sum_ite_eq]
      rw [if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le (hl t (List.mem_cons_self ..))))]
  exact hsum_all p (fun t ht => degAt_ge ht)

lemma indepOfU_lcU {v : ℕ} {u : UPoly} (hu : IndepOfU v u) : IndepOf v (lcU u) := by
  unfold lcU
  by_cases h : u.length - 1 < u.length
  · rw [List.getD_eq_getElem _ _ h]; exact hu _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (not_lt.mp h)]; exact indepOf_zero v

lemma indepOfU_redU {v : ℕ} {u : UPoly} (hu : IndepOfU v u) : IndepOfU v (redU u) := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  rw [List.mem_range] at hi
  have hil : i < u.length := by omega
  rw [List.getD_eq_getElem _ _ hil]
  exact hu _ (List.getElem_mem hil)

lemma indepOfU_derivU {v : ℕ} {u : UPoly} (hu : IndepOfU v u) : IndepOfU v (derivU u) := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  rw [List.mem_range] at hi
  have hil : i + 1 < u.length := by omega
  rw [List.getD_eq_getElem _ _ hil]
  exact indepOf_scaleNat (hu _ (List.getElem_mem hil))

lemma indepOfU_premStep {v : ℕ} {p q : UPoly} (hp : IndepOfU v p) (hq : IndepOfU v q) :
    IndepOfU v (premStep p q) := by
  intro c hc
  unfold premStep at hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
  have hlp := indepOfU_lcU hp
  have hlq := indepOfU_lcU hq
  have get_ind : ∀ (w : UPoly), IndepOfU v w → ∀ j, IndepOf v (w.getD j []) := by
    intro w hw j
    by_cases hj : j < w.length
    · rw [List.getD_eq_getElem _ _ hj]; exact hw _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (not_lt.mp hj)]; exact indepOf_zero v
  refine indepOf_add (indepOf_mul (indepOf_mul hlq hlq) (get_ind p hp i)) (indepOf_neg ?_)
  split_ifs
  · exact indepOf_zero v
  · exact indepOf_mul (indepOf_mul hlq hlp) (get_ind q hq _)

lemma indepOfU_prem2 {v : ℕ} {p q : UPoly} (hp : IndepOfU v p) (hq : IndepOfU v q) :
    IndepOfU v (prem2 p q) := by
  unfold prem2
  generalize p.length - q.length + 1 = k
  induction k generalizing p with
  | zero => exact hp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact indepOfU_premStep (ih hp) hq

lemma length_redU (u : UPoly) : (redU u).length = u.length - 1 := by simp [redU]
lemma length_derivU (u : UPoly) : (derivU u).length = u.length - 1 := by simp [derivU]
lemma length_premStep (p q : UPoly) : (premStep p q).length = p.length - 1 := by simp [premStep]

lemma length_prem2 {p q : UPoly} (hq : 2 ≤ q.length) (hpq : q.length ≤ p.length) :
    (prem2 p q).length = q.length - 1 := by
  unfold prem2
  have key : ∀ (k : ℕ) (r : UPoly), k ≤ r.length →
      ((fun w => premStep w q)^[k] r).length = r.length - k := by
    intro k
    induction k with
    | zero => intro r _; simp
    | succ k ih =>
      intro r hr
      rw [Function.iterate_succ_apply', length_premStep, ih r (by omega)]
      omega
  rw [key (p.length - q.length + 1) p (by omega)]
  omega

lemma evalU_eq_const {u : UPoly} (hu : u.length ≤ 1) (ρ : ℕ → ℝ) (x : ℝ) :
    evalU u ρ x = evalM (u.getD 0 []) ρ := by
  unfold evalU
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hu with h0 | h1
  · rw [h0, List.length_eq_zero_iff.mp h0]; simp
  · rw [h1]; simp

lemma evalU_redU_of_lc_zero {u : UPoly} (hu : 1 ≤ u.length) {ρ : ℕ → ℝ}
    (hlc : evalM (lcU u) ρ = 0) (x : ℝ) :
    evalU (redU u) ρ x = evalU u ρ x := by
  unfold evalU
  rw [length_redU]
  have hsplit : u.length = (u.length - 1) + 1 := by omega
  conv_rhs => rw [hsplit, Finset.sum_range_succ]
  have hlast : evalM (u.getD (u.length - 1) []) ρ = 0 := hlc
  rw [hlast, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hget : (redU u).getD i [] = u.getD i [] := by
    rw [redU, List.getD_eq_getElem _ _ (by simp [hi])]; simp [hi]
  rw [hget]

lemma hasDerivAt_evalU (u : UPoly) (ρ : ℕ → ℝ) (x : ℝ) :
    HasDerivAt (fun t => evalU u ρ t) (evalU (derivU u) ρ x) x := by
  unfold evalU
  have h1 : HasDerivAt (fun t => ∑ i ∈ Finset.range u.length, evalM (u.getD i []) ρ * t ^ i)
      (∑ i ∈ Finset.range u.length, evalM (u.getD i []) ρ * (i * x ^ (i - 1))) x := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (hasDerivAt_pow i x).const_mul (evalM (u.getD i []) ρ)
  convert h1 using 1
  rw [length_derivU]
  cases hlen : u.length with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel, Finset.sum_range_succ', Nat.cast_zero, zero_mul, mul_zero,
      add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hget : (derivU u).getD i [] = scaleNatM (i + 1) (u.getD (i + 1) []) := by
      rw [derivU, List.getD_eq_getElem _ _ (by simp [hlen, hi])]; simp [hlen, hi]
    rw [hget, evalM_scaleNat]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

lemma continuous_evalU (u : UPoly) (ρ : ℕ → ℝ) : Continuous (fun t => evalU u ρ t) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_evalU u ρ x).continuousAt

lemma evalU_premStep {p q : UPoly} (hq : 1 ≤ q.length) (hpq : q.length ≤ p.length)
    (ρ : ℕ → ℝ) (x : ℝ) :
    evalU (premStep p q) ρ x =
      (evalM (lcU q) ρ) ^ 2 * evalU p ρ x -
      evalM (lcU q) ρ * evalM (lcU p) ρ * x ^ (p.length - q.length) * evalU q ρ x := by
  set a := evalM (lcU p) ρ
  set b := evalM (lcU q) ρ
  set sh := p.length - q.length
  set np := p.length - 1
  set nq := q.length - 1
  have hp_eq : p.length = np + 1 := by omega
  have hq_eq : q.length = nq + 1 := by omega
  have hlen : (premStep p q).length = np := length_premStep p q
  unfold evalU
  rw [hlen]
  have hstep_sum :
      ∑ i ∈ Finset.range np, evalM ((premStep p q).getD i []) ρ * x ^ i =
      ∑ i ∈ Finset.range np,
        (b ^ 2 * evalM (p.getD i []) ρ * x ^ i -
         (if i < sh then 0 else b * a * evalM (q.getD (i - sh) []) ρ * x ^ i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hget : (premStep p q).getD i [] =
        addM (mulM (mulM (lcU q) (lcU q)) (p.getD i []))
          (negM (if i < sh then [] else mulM (mulM (lcU q) (lcU p)) (q.getD (i - sh) []))) := by
      rw [premStep, List.getD_eq_getElem _ _ (by simp [hi, np])]
      simp [hi, np, sh]
    rw [hget, evalM_add, evalM_mul, evalM_mul, evalM_neg]
    split_ifs
    · simp only [evalM_nil]; dsimp only [b]; ring
    · rw [evalM_mul, evalM_mul]; dsimp only [a, b]; ring
  rw [hstep_sum, Finset.sum_sub_distrib]
  have hsum_p :
      ∑ i ∈ Finset.range np, b ^ 2 * evalM (p.getD i []) ρ * x ^ i =
      b ^ 2 * (∑ i ∈ Finset.range p.length, evalM (p.getD i []) ρ * x ^ i) -
        b ^ 2 * a * x ^ np := by
    have hsp : ∑ i ∈ Finset.range p.length, evalM (p.getD i []) ρ * x ^ i =
        (∑ i ∈ Finset.range np, evalM (p.getD i []) ρ * x ^ i) + a * x ^ np := by
      rw [hp_eq, Finset.sum_range_succ]; rfl
    rw [hsp]
    have h1 : ∑ i ∈ Finset.range np, b ^ 2 * evalM (p.getD i []) ρ * x ^ i =
        b ^ 2 * ∑ i ∈ Finset.range np, evalM (p.getD i []) ρ * x ^ i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h1]; ring
  have hsum_q :
      ∑ i ∈ Finset.range np,
        (if i < sh then (0 : ℝ) else b * a * evalM (q.getD (i - sh) []) ρ * x ^ i) =
      b * a * x ^ sh * (∑ j ∈ Finset.range q.length, evalM (q.getD j []) ρ * x ^ j) -
        b ^ 2 * a * x ^ np := by
    have hshift : np = sh + nq := by omega
    rw [hshift, Finset.sum_range_add]
    have hleft : ∑ i ∈ Finset.range sh,
        (if i < sh then (0 : ℝ) else b * a * evalM (q.getD (i - sh) []) ρ * x ^ i) = 0 := by
      apply Finset.sum_eq_zero; intro i hi; rw [if_pos (Finset.mem_range.mp hi)]
    rw [hleft, zero_add]
    have hright : ∑ j ∈ Finset.range nq,
        (if sh + j < sh then (0 : ℝ)
         else b * a * evalM (q.getD (sh + j - sh) []) ρ * x ^ (sh + j)) =
        b * a * x ^ sh * ∑ j ∈ Finset.range nq, evalM (q.getD j []) ρ * x ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [if_neg (by omega), Nat.add_sub_cancel_left, pow_add]; ring
    rw [hright]
    have hsq : ∑ j ∈ Finset.range q.length, evalM (q.getD j []) ρ * x ^ j =
        (∑ j ∈ Finset.range nq, evalM (q.getD j []) ρ * x ^ j) + b * x ^ nq := by
      rw [hq_eq, Finset.sum_range_succ]; rfl
    rw [hsq]
    calc b * a * x ^ sh * ∑ j ∈ Finset.range nq, evalM (q.getD j []) ρ * x ^ j
        = b * a * x ^ sh * ((∑ j ∈ Finset.range nq, evalM (q.getD j []) ρ * x ^ j) + b * x ^ nq) -
          b ^ 2 * a * (x ^ sh * x ^ nq) := by ring
      _ = b * a * x ^ sh * ((∑ j ∈ Finset.range nq, evalM (q.getD j []) ρ * x ^ j) + b * x ^ nq) -
          b ^ 2 * a * x ^ (sh + nq) := by rw [← pow_add]
  rw [hsum_p, hsum_q]; ring

lemma evalU_prem2_root {p q : UPoly} (hq : 2 ≤ q.length) (hpq : q.length ≤ p.length)
    {ρ : ℕ → ℝ} (hlq : evalM (lcU q) ρ ≠ 0) {r : ℝ} (hr : evalU q ρ r = 0) :
    realSign (evalU (prem2 p q) ρ r) = realSign (evalU p ρ r) := by
  unfold prem2
  have key : ∀ (k : ℕ) (u : UPoly), q.length ≤ u.length - k + 1 →
      realSign (evalU ((fun w => premStep w q)^[k] u) ρ r) = realSign (evalU u ρ r) := by
    intro k
    induction k with
    | zero => intro u _; rfl
    | succ k ih =>
      intro u hu
      have hlen_k : ((fun w => premStep w q)^[k] u).length = u.length - k := by
        have hlen : ∀ (m : ℕ) (w : UPoly), m ≤ w.length →
            ((fun z => premStep z q)^[m] w).length = w.length - m := by
          intro m; induction m with
          | zero => intro w _; simp
          | succ m ihm =>
            intro w hw; rw [Function.iterate_succ_apply', length_premStep, ihm w (by omega)]; omega
        exact hlen k u (by omega)
      rw [Function.iterate_succ_apply',
        evalU_premStep (by omega) (by rw [hlen_k]; omega) ρ r, hr, mul_zero, sub_zero,
        realSign_mul_pos (sq_pos_of_ne_zero hlq)]
      exact ih u (by omega)
  exact key (p.length - q.length + 1) p (by omega)

lemma evalU_sign_atTop {u : UPoly} (hu : 2 ≤ u.length) {ρ : ℕ → ℝ}
    (hlc : evalM (lcU u) ρ ≠ 0) :
    ∃ M : ℝ, ∀ x : ℝ, M < x → realSign (evalU u ρ x) = realSign (evalM (lcU u) ρ) := by
  set d := u.length - 1
  have hd : 1 ≤ d := by omega
  set c := evalM (lcU u) ρ
  set B := ∑ i ∈ Finset.range d, |evalM (u.getD i []) ρ|
  refine ⟨max 1 (B / |c| + 1), fun x hx => ?_⟩
  have hx1 : 1 < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hxB : B / |c| + 1 < x := lt_of_le_of_lt (le_max_right _ _) hx
  have hc_pos : 0 < |c| := abs_pos.mpr hlc
  have hdom : |∑ i ∈ Finset.range d, evalM (u.getD i []) ρ * x ^ i| < |c * x ^ d| := by
    calc |∑ i ∈ Finset.range d, evalM (u.getD i []) ρ * x ^ i|
        ≤ ∑ i ∈ Finset.range d, |evalM (u.getD i []) ρ * x ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range d, |evalM (u.getD i []) ρ| * x ^ (d - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul, abs_pow, abs_of_pos hx0]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (le_of_lt hx1) (by rw [Finset.mem_range] at hi; omega))
            (abs_nonneg _)
      _ = B * x ^ (d - 1) := by rw [← Finset.sum_mul]
      _ < |c| * x * x ^ (d - 1) := by
          have hBx : B < |c| * x := by
            have : B / |c| < x := by linarith
            exact (div_lt_iff₀ hc_pos).mp this |> fun h => by linarith
          exact mul_lt_mul_of_pos_right hBx (pow_pos hx0 _)
      _ = |c * x ^ d| := by
          rw [abs_mul, abs_pow, abs_of_pos hx0, mul_assoc, ← pow_succ']
          congr 2; omega
  have hsplit : evalU u ρ x =
      (∑ i ∈ Finset.range d, evalM (u.getD i []) ρ * x ^ i) + c * x ^ d := by
    unfold evalU
    have hlen : u.length = d + 1 := by omega
    rw [hlen, Finset.sum_range_succ]; rfl
  rw [hsplit]
  set rest := ∑ i ∈ Finset.range d, evalM (u.getD i []) ρ * x ^ i
  rcases lt_or_gt_of_ne hlc with hcn | hcp
  · have hlead : c * x ^ d < 0 := mul_neg_of_neg_of_pos hcn (pow_pos hx0 _)
    rw [abs_of_neg hlead] at hdom
    have htot : rest + c * x ^ d < 0 := by linarith [le_abs_self rest]
    rw [(realSign_eq_two_iff _).2 htot, (realSign_eq_two_iff _).2 hcn]
  · have hlead : 0 < c * x ^ d := mul_pos hcp (pow_pos hx0 _)
    rw [abs_of_pos hlead] at hdom
    have htot : 0 < rest + c * x ^ d := by linarith [neg_abs_le rest]
    rw [(realSign_eq_one_iff _).2 htot, (realSign_eq_one_iff _).2 hcp]

def negInfSign (len s : ℕ) : ℕ :=
  if (len - 1) % 2 = 0 then s else negSign s

lemma primrec_negInfSign : Primrec₂ negInfSign :=
  (Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))
      (Primrec.const 2)) (Primrec.const 0))
    Primrec.snd (primrec_negSign.comp Primrec.snd)).to₂

lemma evalU_sign_atBot {u : UPoly} (hu : 2 ≤ u.length) {ρ : ℕ → ℝ}
    (hlc : evalM (lcU u) ρ ≠ 0) :
    ∃ M : ℝ, ∀ x : ℝ, x < -M →
      realSign (evalU u ρ x) = negInfSign u.length (realSign (evalM (lcU u) ρ)) := by
  set d := u.length - 1
  have hd : 1 ≤ d := by omega
  set c := evalM (lcU u) ρ
  set B := ∑ i ∈ Finset.range d, |evalM (u.getD i []) ρ|
  refine ⟨max 1 (B / |c| + 1), fun x hx => ?_⟩
  set y := -x
  have hy : max 1 (B / |c| + 1) < y := by linarith
  have hy1 : 1 < y := lt_of_le_of_lt (le_max_left _ _) hy
  have hy0 : 0 < y := by linarith
  have hc_pos : 0 < |c| := abs_pos.mpr hlc
  have hdom : |∑ i ∈ Finset.range d, evalM (u.getD i []) ρ * x ^ i| < |c * x ^ d| := by
    calc |∑ i ∈ Finset.range d, evalM (u.getD i []) ρ * x ^ i|
        ≤ ∑ i ∈ Finset.range d, |evalM (u.getD i []) ρ * x ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range d, |evalM (u.getD i []) ρ| * y ^ (d - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul, abs_pow, show |x| = y from abs_of_neg (by linarith)]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (le_of_lt hy1) (by rw [Finset.mem_range] at hi; omega))
            (abs_nonneg _)
      _ = B * y ^ (d - 1) := by rw [← Finset.sum_mul]
      _ < |c| * y * y ^ (d - 1) := by
          have hBy : B < |c| * y := by
            have : B / |c| < y := by linarith [le_max_right (1 : ℝ) (B / |c| + 1)]
            exact (div_lt_iff₀ hc_pos).mp this |> fun h => by linarith
          exact mul_lt_mul_of_pos_right hBy (pow_pos hy0 _)
      _ = |c * x ^ d| := by
          rw [abs_mul, abs_pow, show |x| = y from abs_of_neg (by linarith), mul_assoc, ← pow_succ']
          congr 2; omega
  have hsplit : evalU u ρ x =
      (∑ i ∈ Finset.range d, evalM (u.getD i []) ρ * x ^ i) + c * x ^ d := by
    unfold evalU
    have hlen : u.length = d + 1 := by omega
    rw [hlen, Finset.sum_range_succ]; rfl
  rw [hsplit]
  set rest := ∑ i ∈ Finset.range d, evalM (u.getD i []) ρ * x ^ i
  have hx_pow : x ^ d = (-1 : ℝ) ^ d * y ^ d := by
    rw [← mul_pow]; congr 1; simp [y]
  unfold negInfSign
  by_cases hev : d % 2 = 0
  · rw [if_pos hev]
    have hneg1 : (-1 : ℝ) ^ d = 1 := Even.neg_one_pow (Nat.even_iff.mpr hev)
    have hxd_pos : 0 < x ^ d := by rw [hx_pow, hneg1, one_mul]; exact pow_pos hy0 _
    rcases lt_or_gt_of_ne hlc with hcn | hcp
    · have hlead : c * x ^ d < 0 := mul_neg_of_neg_of_pos hcn hxd_pos
      rw [abs_of_neg hlead] at hdom
      rw [(realSign_eq_two_iff _).2 (by linarith [le_abs_self rest]), (realSign_eq_two_iff _).2 hcn]
    · have hlead : 0 < c * x ^ d := mul_pos hcp hxd_pos
      rw [abs_of_pos hlead] at hdom
      rw [(realSign_eq_one_iff _).2 (by linarith [neg_abs_le rest]), (realSign_eq_one_iff _).2 hcp]
  · rw [if_neg hev]
    have hodd : Odd d := Nat.odd_iff.mpr (by omega)
    have hneg1 : (-1 : ℝ) ^ d = -1 := Odd.neg_one_pow hodd
    have hxd_neg : x ^ d < 0 := by rw [hx_pow, hneg1, neg_one_mul]; linarith [pow_pos hy0 d]
    rcases lt_or_gt_of_ne hlc with hcn | hcp
    · have hlead : 0 < c * x ^ d := mul_pos_of_neg_of_neg hcn hxd_neg
      rw [abs_of_pos hlead] at hdom
      rw [(realSign_eq_one_iff _).2 (by linarith [neg_abs_le rest]), (realSign_eq_two_iff _).2 hcn]
      rfl
    · have hlead : c * x ^ d < 0 := mul_neg_of_pos_of_neg hcp hxd_neg
      rw [abs_of_neg hlead] at hdom
      rw [(realSign_eq_two_iff _).2 (by linarith [le_abs_self rest]), (realSign_eq_one_iff _).2 hcp]
      rfl

/- Monotonicity and Root Uniqueness on Open Intervals -/

lemma evalU_strictMono_or_strictAnti {u : UPoly} {ρ : ℕ → ℝ} {I : Set ℝ}
    (hconv : Convex ℝ I) (hnd : ∀ x ∈ I, evalU (derivU u) ρ x ≠ 0) :
    StrictMonoOn (fun x => evalU u ρ x) I ∨ StrictAntiOn (fun x => evalU u ρ x) I := by
  have hcont : ContinuousOn (fun x => evalU (derivU u) ρ x) I :=
    (continuous_evalU (derivU u) ρ).continuousOn
  by_cases hpos : ∃ x₀ ∈ I, 0 < evalU (derivU u) ρ x₀
  · left
    obtain ⟨x₀, hx₀, hpx₀⟩ := hpos
    have hall : ∀ x ∈ I, 0 < evalU (derivU u) ρ x := by
      intro x hx
      by_contra hle
      push Not at hle
      have hlt : evalU (derivU u) ρ x < 0 := lt_of_le_of_ne hle (hnd x hx)
      have h0 : (0 : ℝ) ∈ (fun t => evalU (derivU u) ρ t) '' I :=
        hconv.isPreconnected.image _ hcont |>.Icc_subset
          ⟨x, hx, rfl⟩ ⟨x₀, hx₀, rfl⟩ ⟨le_of_lt hlt, le_of_lt hpx₀⟩
      obtain ⟨c, hcI, hc0⟩ := h0
      exact hnd c hcI hc0
    exact strictMonoOn_of_deriv_pos hconv (continuous_evalU u ρ).continuousOn
      (fun x hx => by
        rw [(hasDerivAt_evalU u ρ x).deriv]
        exact hall x (interior_subset hx))
  · right
    push Not at hpos
    have hall : ∀ x ∈ I, evalU (derivU u) ρ x < 0 := fun x hx =>
      lt_of_le_of_ne (hpos x hx) (hnd x hx)
    exact strictAntiOn_of_deriv_neg hconv (continuous_evalU u ρ).continuousOn
      (fun x hx => by
        rw [(hasDerivAt_evalU u ρ x).deriv]
        exact hall x (interior_subset hx))

lemma evalU_deriv_ne_zero_of_lc_ne_zero {u : UPoly} (hu : 2 ≤ u.length)
    {ρ : ℕ → ℝ} (hlc : evalM (lcU u) ρ ≠ 0) :
    ∃ x : ℝ, evalU (derivU u) ρ x ≠ 0 := by
  by_contra hall
  push Not at hall
  set P : Polynomial ℝ := ∑ i ∈ Finset.range (u.length - 1),
      Polynomial.C (evalM ((derivU u).getD i []) ρ) * Polynomial.X ^ i
  have hpoly : ∀ x : ℝ, P.eval x = 0 := by
    intro x
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    simpa [evalU, length_derivU] using hall x
  have hP0 : P = 0 := Polynomial.funext fun x => by rw [hpoly x, Polynomial.eval_zero]
  have hcoeff := congrArg (fun Q : Polynomial ℝ => Q.coeff (u.length - 2)) hP0
  simp only [Polynomial.coeff_zero, P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow] at hcoeff
  rw [Finset.sum_eq_single (u.length - 2)] at hcoeff
  · simp only [↓reduceIte, mul_one] at hcoeff
    have hidx : u.length - 2 < u.length - 1 := by omega
    have hget : (derivU u).getD (u.length - 2) [] =
        scaleNatM (u.length - 1) (u.getD (u.length - 1) []) := by
      rw [derivU, List.getD_eq_getElem _ _ (by simp [hidx])]
      simp [hidx, show u.length - 2 + 1 = u.length - 1 by omega]
    rw [hget, evalM_scaleNat] at hcoeff
    have hne : ((u.length - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact (mul_ne_zero hne hlc) hcoeff
  · intro i _ hi; simp [hi.symm]
  · intro h; simp at h; omega

/- Section 2: Cohen-Hormander Closure and Sign Table Lifting -/

def maxLen (L : List UPoly) : ℕ :=
  L.foldl (fun acc u => max acc u.length) 0

lemma primrec_maxLen : Primrec maxLen :=
  Primrec.list_foldl Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))).to₂

def closeStep (k : ℕ) (CL : List UPoly) : List UPoly :=
  let Ck := CL.filter (fun u => u.length == k)
  let Cgt := CL.filter (fun u => decide (k < u.length))
  let added1 := Ck.flatMap (fun p => [ [lcU p], redU p, derivU p ])
  let added2 := Ck.flatMap (fun p => Ck.map (fun q => prem2 p q))
  let added3 := Cgt.flatMap (fun p => Ck.map (fun q => prem2 p q))
  CL ++ added1 ++ added2 ++ added3

lemma primrec_closeStep : Primrec₂ closeStep := by
  unfold closeStep
  have hCk : Primrec fun x : ℕ × List UPoly => x.2.filter (fun u => u.length == x.1) :=
    primrec_list_filter Primrec.snd
      (Primrec.beq.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst)).to₂
  have hCgt : Primrec fun x : ℕ × List UPoly => x.2.filter (fun u => decide (x.1 < u.length)) :=
    primrec_list_filter Primrec.snd
      ((Primrec.nat_lt.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_length.comp Primrec.snd)).decide).to₂
  have h1fn : Primrec₂ fun (_ : ℕ × List UPoly) (p : UPoly) => [ [lcU p], redU p, derivU p ] :=
    (Primrec.list_cons.comp
      (Primrec.list_cons.comp (primrec_lcU.comp Primrec.snd) (Primrec.const ([] : UPoly)))
      (Primrec.list_cons.comp (primrec_redU.comp Primrec.snd)
        (Primrec.list_cons.comp (primrec_derivU.comp Primrec.snd) (Primrec.const [])))).to₂
  have hadded1 : Primrec fun x : ℕ × List UPoly =>
      (x.2.filter (fun u => u.length == x.1)).flatMap (fun p => [ [lcU p], redU p, derivU p ]) :=
    Primrec.list_flatMap hCk h1fn
  have hpremMap : Primrec₂ (fun (a : (ℕ × List UPoly) × UPoly) (q : UPoly) => prem2 a.2 q) :=
    (primrec_prem2.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hadded2 : Primrec fun x : ℕ × List UPoly =>
      (x.2.filter (fun u => u.length == x.1)).flatMap
        (fun p => (x.2.filter (fun u => u.length == x.1)).map (fun q => prem2 p q)) :=
    Primrec.list_flatMap hCk (Primrec.list_map (hCk.comp Primrec.fst) hpremMap).to₂
  have hadded3 : Primrec fun x : ℕ × List UPoly =>
      (x.2.filter (fun u => decide (x.1 < u.length))).flatMap
        (fun p => (x.2.filter (fun u => u.length == x.1)).map (fun q => prem2 p q)) :=
    Primrec.list_flatMap hCgt (Primrec.list_map (hCk.comp Primrec.fst) hpremMap).to₂
  exact (Primrec.list_append.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp Primrec.snd hadded1) hadded2) hadded3).to₂

def closeUPolys (L : List UPoly) : List UPoly :=
  let D := maxLen L
  D.rec (motive := fun _ => List UPoly) L (fun m acc =>
    if 2 ≤ D - m then closeStep (D - m) acc else acc)

lemma primrec_closeUPolys : Primrec closeUPolys := by
  unfold closeUPolys
  have hstep : Primrec₂ fun (L : List UPoly) (ma : ℕ × List UPoly) =>
      if 2 ≤ maxLen L - ma.1 then closeStep (maxLen L - ma.1) ma.2 else ma.2 :=
    (Primrec.ite
      (Primrec.nat_le.comp (Primrec.const 2)
        (Primrec.nat_sub.comp (primrec_maxLen.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
      (primrec_closeStep.comp
        (Primrec.nat_sub.comp (primrec_maxLen.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.nat_rec' primrec_maxLen Primrec.id hstep

def oppSign (a b : ℕ) : Bool :=
  (a == 1 && b == 2) || (a == 2 && b == 1)

lemma primrec_oppSign : Primrec₂ oppSign := by
  unfold oppSign
  exact (primrec_bool_or.comp
    (primrec_bool_and.comp (Primrec.beq.comp Primrec.fst (Primrec.const 1))
      (Primrec.beq.comp Primrec.snd (Primrec.const 2)))
    (primrec_bool_and.comp (Primrec.beq.comp Primrec.fst (Primrec.const 2))
      (Primrec.beq.comp Primrec.snd (Primrec.const 1)))).to₂

/- Lifting helpers packed cleanly over `Ctx := (List UPoly × ℕ) × List (List ℕ)` -/

abbrev LiftCtx := (List UPoly × ℕ) × List (List ℕ)

def ctxLprev (c : LiftCtx) : List UPoly := c.1.1.filter (fun u => decide (u.length < c.1.2))
def ctxLcurr (c : LiftCtx) : List UPoly := c.1.1.filter (fun u => decide (u.length ≤ c.1.2))
def ctxRow0 (c : LiftCtx) : List ℕ := c.2.getD 0 []
def ctxNumRoots (c : LiftCtx) : ℕ := c.2.length / 2

def lookupPrev (c : LiftCtx) (row : List ℕ) (u : UPoly) : ℕ :=
  row.getD ((ctxLprev c).findIdx (fun w => decide (w = u))) 0

def witnessRoot (c : LiftCtx) (j : ℕ) : UPoly :=
  let rRow := c.2.getD (2 * j + 1) []
  let row0 := ctxRow0 c
  ((ctxLprev c).filter (fun q =>
    decide (2 ≤ q.length) && (lookupPrev c row0 [lcU q] != 0) &&
      (lookupPrev c rRow q == 0))).headD []

def signAtRoot (c : LiftCtx) (j : ℕ) (p : UPoly) : ℕ :=
  let rRow := c.2.getD (2 * j + 1) []
  if p.length < c.1.2 then lookupPrev c rRow p
  else if lookupPrev c (ctxRow0 c) [lcU p] = 0 then lookupPrev c rRow (redU p)
  else lookupPrev c rRow (prem2 p (witnessRoot c j))

def rootRowNew (c : LiftCtx) (j : ℕ) : List ℕ :=
  (ctxLcurr c).map (signAtRoot c j)

def sL (c : LiftCtx) (j : ℕ) (p : UPoly) : ℕ :=
  if j = 0 then negInfSign c.1.2 (lookupPrev c (ctxRow0 c) [lcU p])
  else signAtRoot c (j - 1) p

def sR (c : LiftCtx) (j : ℕ) (p : UPoly) : ℕ :=
  if j = ctxNumRoots c then lookupPrev c (ctxRow0 c) [lcU p]
  else signAtRoot c j p

def isActive (c : LiftCtx) (j : ℕ) (p : UPoly) : Bool :=
  (p.length == c.1.2) && (lookupPrev c (ctxRow0 c) [lcU p] != 0) &&
    oppSign (sL c j p) (sR c j p)

def activeList (c : LiftCtx) (j : ℕ) : List UPoly :=
  (ctxLcurr c).filter (isActive c j)

def ltRoot (c : LiftCtx) (j : ℕ) (p₁ p₂ : UPoly) : Bool :=
  lookupPrev c (c.2.getD (2 * j) []) (prem2 p₁ p₂) == sR c j p₁

def rootRank (c : LiftCtx) (j : ℕ) (p : UPoly) : ℕ :=
  ((activeList c j).filter (fun q => ltRoot c j q p)).length

def activeRanks (c : LiftCtx) (j : ℕ) : List ℕ :=
  let act := activeList c j
  (List.range act.length).filter (fun r => act.any (fun p => rootRank c j p == r))

def signOnSubInt (c : LiftCtx) (j u : ℕ) (p : UPoly) : ℕ :=
  let iRow := c.2.getD (2 * j) []
  if p.length < c.1.2 then lookupPrev c iRow p
  else if lookupPrev c (ctxRow0 c) [lcU p] = 0 then lookupPrev c iRow (redU p)
  else if !(oppSign (sL c j p) (sR c j p)) then
    if sL c j p != 0 then sL c j p else sR c j p
  else if u = 0 then sL c j p
  else if rootRank c j p ≤ (activeRanks c j).getD (u - 1) 0 then sR c j p
  else sL c j p

def signAtNewRoot (c : LiftCtx) (j u : ℕ) (p : UPoly) : ℕ :=
  let iRow := c.2.getD (2 * j) []
  if p.length < c.1.2 then lookupPrev c iRow p
  else if lookupPrev c (ctxRow0 c) [lcU p] = 0 then lookupPrev c iRow (redU p)
  else if !(oppSign (sL c j p) (sR c j p)) then
    if sL c j p != 0 then sL c j p else sR c j p
  else
    let rk := rootRank c j p
    let target := (activeRanks c j).getD u 0
    if rk < target then sR c j p else if rk = target then 0 else sL c j p

def expandInterval (c : LiftCtx) (j : ℕ) : List (List ℕ) :=
  let ranks := activeRanks c j
  (List.range ranks.length).flatMap (fun u =>
    [(ctxLcurr c).map (signOnSubInt c j u), (ctxLcurr c).map (signAtNewRoot c j u)]) ++
    [(ctxLcurr c).map (signOnSubInt c j ranks.length)]

def liftTable (CL : List UPoly) (k : ℕ) (M : List (List ℕ)) : List (List ℕ) :=
  let c : LiftCtx := ((CL, k), M)
  (List.range (ctxNumRoots c)).flatMap (fun j => expandInterval c j ++ [rootRowNew c j]) ++
    expandInterval c (ctxNumRoots c)

def buildSignTable (CL : List UPoly) (σ : List ℕ) : List (List ℕ) :=
  let D := maxLen CL
  (D - 1).rec (motive := fun _ => List (List ℕ)) [σ] (fun m acc => liftTable CL (m + 2) acc)

/- Primrec proofs for liftTable and buildSignTable -/

lemma primrec_ctxLprev : Primrec ctxLprev :=
  primrec_list_filter (Primrec.fst.comp Primrec.fst)
    ((Primrec.nat_lt.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).decide).to₂

lemma primrec_ctxLcurr : Primrec ctxLcurr :=
  primrec_list_filter (Primrec.fst.comp Primrec.fst)
    ((Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).decide).to₂

lemma primrec_ctxRow0 : Primrec ctxRow0 :=
  (Primrec.list_getD ([] : List ℕ)).comp Primrec.snd (Primrec.const 0)

lemma primrec_ctxNumRoots : Primrec ctxNumRoots :=
  Primrec.nat_div.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 2)

lemma primrec_lookupPrev_gen {α : Type*} [Primcodable α]
    {fc : α → LiftCtx} {frow : α → List ℕ} {fu : α → UPoly}
    (hfc : Primrec fc) (hfrow : Primrec frow) (hfu : Primrec fu) :
    Primrec fun a => lookupPrev (fc a) (frow a) (fu a) := by
  unfold lookupPrev
  have hidx : Primrec fun a => (ctxLprev (fc a)).findIdx (fun w => decide (w = fu a)) :=
    Primrec.list_findIdx (primrec_ctxLprev.comp hfc)
      ((Primrec.eq.comp Primrec.snd (hfu.comp Primrec.fst)).decide).to₂
  exact (Primrec.list_getD 0).comp hfrow hidx

lemma primrec_witnessRoot_gen {α : Type*} [Primcodable α]
    {fc : α → LiftCtx} {fj : α → ℕ}
    (hfc : Primrec fc) (hfj : Primrec fj) :
    Primrec fun a => witnessRoot (fc a) (fj a) := by
  unfold witnessRoot
  have hrRow : Primrec fun a => (fc a).2.getD (2 * fj a + 1) [] :=
    (Primrec.list_getD ([] : List ℕ)).comp (Primrec.snd.comp hfc)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hfj) (Primrec.const 1))
  have hlcSing : Primrec fun q : UPoly => [lcU q] :=
    Primrec.list_cons.comp primrec_lcU (Primrec.const ([] : UPoly))
  have hp : Primrec₂ fun a (q : UPoly) =>
      decide (2 ≤ q.length) && (lookupPrev (fc a) (ctxRow0 (fc a)) [lcU q] != 0) &&
        (lookupPrev (fc a) ((fc a).2.getD (2 * fj a + 1) []) q == 0) :=
    (primrec_bool_and.comp
      (primrec_bool_and.comp
        ((Primrec.nat_le.comp (Primrec.const 2) (Primrec.list_length.comp Primrec.snd)).decide)
        (primrec_bne.comp
          (primrec_lookupPrev_gen (hfc.comp Primrec.fst)
            (primrec_ctxRow0.comp (hfc.comp Primrec.fst)) (hlcSing.comp Primrec.snd))
          (Primrec.const 0)))
      (Primrec.beq.comp
        (primrec_lookupPrev_gen (hfc.comp Primrec.fst) (hrRow.comp Primrec.fst) Primrec.snd)
        (Primrec.const 0))).to₂
  exact (primrec_list_headD ([] : UPoly)).comp
    (primrec_list_filter (primrec_ctxLprev.comp hfc) hp)

lemma primrec_signAtRoot_gen {α : Type*} [Primcodable α]
    {fc : α → LiftCtx} {fj : α → ℕ} {fp : α → UPoly}
    (hfc : Primrec fc) (hfj : Primrec fj) (hfp : Primrec fp) :
    Primrec fun a => signAtRoot (fc a) (fj a) (fp a) := by
  unfold signAtRoot
  have hrRow : Primrec fun a => (fc a).2.getD (2 * fj a + 1) [] :=
    (Primrec.list_getD ([] : List ℕ)).comp (Primrec.snd.comp hfc)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hfj) (Primrec.const 1))
  have hlcSing : Primrec fun a => [lcU (fp a)] :=
    Primrec.list_cons.comp (primrec_lcU.comp hfp) (Primrec.const ([] : UPoly))
  exact Primrec.ite
    (Primrec.nat_lt.comp (Primrec.list_length.comp hfp)
      (Primrec.snd.comp (Primrec.fst.comp hfc)))
    (primrec_lookupPrev_gen hfc hrRow hfp)
    (Primrec.ite
      (Primrec.eq.comp (primrec_lookupPrev_gen hfc (primrec_ctxRow0.comp hfc) hlcSing)
        (Primrec.const 0))
      (primrec_lookupPrev_gen hfc hrRow (primrec_redU.comp hfp))
      (primrec_lookupPrev_gen hfc hrRow (primrec_prem2.comp hfp (primrec_witnessRoot_gen hfc hfj))))

lemma primrec_rootRowNew_gen {α : Type*} [Primcodable α]
    {fc : α → LiftCtx} {fj : α → ℕ}
    (hfc : Primrec fc) (hfj : Primrec fj) :
    Primrec fun a => rootRowNew (fc a) (fj a) :=
  Primrec.list_map (primrec_ctxLcurr.comp hfc)
    (primrec_signAtRoot_gen (hfc.comp Primrec.fst) (hfj.comp Primrec.fst) Primrec.snd).to₂

lemma primrec_sL_gen {α : Type*} [Primcodable α]
    {fc : α → LiftCtx} {fj : α → ℕ} {fp : α → UPoly}
    (hfc : Primrec fc) (hfj : Primrec fj) (hfp : Primrec fp) :
    Primrec fun a => sL (fc a) (fj a) (fp a) := by
  unfold sL
  have hlcSing : Primrec fun a => [lcU (fp a)] :=
    Primrec.list_cons.comp (primrec_lcU.comp hfp) (Primrec.const ([] : UPoly))
  exact Primrec.ite
    (Primrec.eq.comp hfj (Primrec.const 0))
    (primrec_negInfSign.comp
      (Primrec.snd.comp (Primrec.fst.comp hfc))
      (primrec_lookupPrev_gen hfc (primrec_ctxRow0.comp hfc) hlcSing))
    (primrec_signAtRoot_gen hfc (Primrec.nat_sub.comp hfj (Primrec.const 1)) hfp)

lemma primrec_sR_gen {α : Type*} [Primcodable α]
    {fc : α → LiftCtx} {fj : α → ℕ} {fp : α → UPoly}
    (hfc : Primrec fc) (hfj : Primrec fj) (hfp : Primrec fp) :
    Primrec fun a => sR (fc a) (fj a) (fp a) := by
  unfold sR
  have hlcSing : Primrec fun a => [lcU (fp a)] :=
    Primrec.list_cons.comp (primrec_lcU.comp hfp) (Primrec.const ([] : UPoly))
  exact Primrec.ite
    (Primrec.eq.comp hfj (primrec_ctxNumRoots.comp hfc))
    (primrec_lookupPrev_gen hfc (primrec_ctxRow0.comp hfc) hlcSing)
    (primrec_signAtRoot_gen hfc hfj hfp)

lemma primrec_isActive_gen {α : Type*} [Primcodable α]
    {fc : α → LiftCtx} {fj : α → ℕ} {fp : α → UPoly}
    (hfc : Primrec fc) (hfj : Primrec fj) (hfp : Primrec fp) :
    Primrec fun a => isActive (fc a) (fj a) (fp a) := by
  unfold isActive
  have hlcSing : Primrec fun a => [lcU (fp a)] :=
    Primrec.list_cons.comp (primrec_lcU.comp hfp) (Primrec.const ([] : UPoly))
  exact primrec_bool_and.comp
    (primrec_bool_and.comp
      (Primrec.beq.comp (Primrec.list_length.comp hfp)
        (Primrec.snd.comp (Primrec.fst.comp hfc)))
      (primrec_bne.comp (primrec_lookupPrev_gen hfc (primrec_ctxRow0.comp hfc) hlcSing)
        (Primrec.const 0)))
    (primrec_oppSign.comp (primrec_sL_gen hfc hfj hfp) (primrec_sR_gen hfc hfj hfp))

lemma primrec_activeList_gen {α : Type*} [Primcodable α]
    {fc : α → LiftCtx} {fj : α → ℕ}
    (hfc : Primrec fc) (hfj : Primrec fj) :
    Primrec fun a => activeList (fc a) (fj a) :=
  primrec_list_filter (primrec_ctxLcurr.comp hfc)
    (primrec_isActive_gen (hfc.comp Primrec.fst) (hfj.comp Primrec.fst) Primrec.snd).to₂

lemma primrec_ltRoot_gen {α : Type*} [Primcodable α]
    {fc : α → LiftCtx} {fj : α → ℕ} {fp₁ fp₂ : α → UPoly}
    (hfc : Primrec fc) (hfj : Primrec fj) (hfp₁ : Primrec fp₁) (hfp₂ : Primrec fp₂) :
    Primrec fun a => ltRoot (fc a) (fj a) (fp₁ a) (fp₂ a) := by
  unfold ltRoot
  have hiRow : Primrec fun a => (fc a).2.getD (2 * fj a) [] :=
    (Primrec.list_getD ([] : List ℕ)).comp (Primrec.snd.comp hfc)
      (Primrec.nat_mul.comp (Primrec.const 2) hfj)
  exact Primrec.beq.comp
    (primrec_lookupPrev_gen hfc hiRow (primrec_prem2.comp hfp₁ hfp₂))
    (primrec_sR_gen hfc hfj hfp₁)

lemma primrec_rootRank_gen {α : Type*} [Primcodable α]
    {fc : α → LiftCtx} {fj : α → ℕ} {fp : α → UPoly}
    (hfc : Primrec fc) (hfj : Primrec fj) (hfp : Primrec fp) :
    Primrec fun a => rootRank (fc a) (fj a) (fp a) := by
  unfold rootRank
  exact Primrec.list_length.comp
    (primrec_list_filter (primrec_activeList_gen hfc hfj)
      (primrec_ltRoot_gen (hfc.comp Primrec.fst) (hfj.comp Primrec.fst)
        Primrec.snd (hfp.comp Primrec.fst)).to₂)

lemma primrec_activeRanks_gen {α : Type*} [Primcodable α]
    {fc : α → LiftCtx} {fj : α → ℕ}
    (hfc : Primrec fc) (hfj : Primrec fj) :
    Primrec fun a => activeRanks (fc a) (fj a) := by
  unfold activeRanks
  have hact := primrec_activeList_gen hfc hfj
  have hany : Primrec₂ fun a (r : ℕ) =>
      (activeList (fc a) (fj a)).any (fun p => rootRank (fc a) (fj a) p == r) :=
    (primrec_list_any (hact.comp Primrec.fst)
      (Primrec.beq.comp
        (primrec_rootRank_gen (hfc.comp (Primrec.fst.comp Primrec.fst))
          (hfj.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
        (Primrec.snd.comp Primrec.fst)).to₂).to₂
  exact primrec_list_filter (Primrec.list_range.comp (Primrec.list_length.comp hact)) hany

lemma primrec_signOnSubInt_gen {α : Type*} [Primcodable α]
    {fc : α → LiftCtx} {fj fu : α → ℕ} {fp : α → UPoly}
    (hfc : Primrec fc) (hfj : Primrec fj) (hfu : Primrec fu) (hfp : Primrec fp) :
    Primrec fun a => signOnSubInt (fc a) (fj a) (fu a) (fp a) := by
  unfold signOnSubInt
  have hiRow : Primrec fun a => (fc a).2.getD (2 * fj a) [] :=
    (Primrec.list_getD ([] : List ℕ)).comp (Primrec.snd.comp hfc)
      (Primrec.nat_mul.comp (Primrec.const 2) hfj)
  have hlcSing : Primrec fun a => [lcU (fp a)] :=
    Primrec.list_cons.comp (primrec_lcU.comp hfp) (Primrec.const ([] : UPoly))
  have hsL := primrec_sL_gen hfc hfj hfp
  have hsR := primrec_sR_gen hfc hfj hfp
  have hopp := primrec_oppSign.comp hsL hsR
  have hbranch_nonopp := primrec_ite_bool (primrec_bne.comp hsL (Primrec.const 0)) hsL hsR
  have hbranch_act := Primrec.ite (Primrec.eq.comp hfu (Primrec.const 0)) hsL
    (Primrec.ite
      (Primrec.nat_le.comp (primrec_rootRank_gen hfc hfj hfp)
        ((Primrec.list_getD 0).comp (primrec_activeRanks_gen hfc hfj)
          (Primrec.nat_sub.comp hfu (Primrec.const 1))))
      hsR hsL)
  have hbranch_lc := primrec_ite_bool (primrec_bool_not.comp hopp) hbranch_nonopp hbranch_act
  exact Primrec.ite
    (Primrec.nat_lt.comp (Primrec.list_length.comp hfp) (Primrec.snd.comp (Primrec.fst.comp hfc)))
    (primrec_lookupPrev_gen hfc hiRow hfp)
    (Primrec.ite
      (Primrec.eq.comp (primrec_lookupPrev_gen hfc (primrec_ctxRow0.comp hfc) hlcSing)
        (Primrec.const 0))
      (primrec_lookupPrev_gen hfc hiRow (primrec_redU.comp hfp))
      hbranch_lc)

lemma primrec_signAtNewRoot_gen {α : Type*} [Primcodable α]
    {fc : α → LiftCtx} {fj fu : α → ℕ} {fp : α → UPoly}
    (hfc : Primrec fc) (hfj : Primrec fj) (hfu : Primrec fu) (hfp : Primrec fp) :
    Primrec fun a => signAtNewRoot (fc a) (fj a) (fu a) (fp a) := by
  unfold signAtNewRoot
  have hiRow : Primrec fun a => (fc a).2.getD (2 * fj a) [] :=
    (Primrec.list_getD ([] : List ℕ)).comp (Primrec.snd.comp hfc)
      (Primrec.nat_mul.comp (Primrec.const 2) hfj)
  have hlcSing : Primrec fun a => [lcU (fp a)] :=
    Primrec.list_cons.comp (primrec_lcU.comp hfp) (Primrec.const ([] : UPoly))
  have hsL := primrec_sL_gen hfc hfj hfp
  have hsR := primrec_sR_gen hfc hfj hfp
  have hopp := primrec_oppSign.comp hsL hsR
  have hbranch_nonopp := primrec_ite_bool (primrec_bne.comp hsL (Primrec.const 0)) hsL hsR
  have hrk := primrec_rootRank_gen hfc hfj hfp
  have htgt := (Primrec.list_getD 0).comp (primrec_activeRanks_gen hfc hfj) hfu
  have hbranch_act := Primrec.ite (Primrec.nat_lt.comp hrk htgt) hsR
    (Primrec.ite (Primrec.eq.comp hrk htgt) (Primrec.const 0) hsL)
  have hbranch_lc := primrec_ite_bool (primrec_bool_not.comp hopp) hbranch_nonopp hbranch_act
  exact Primrec.ite
    (Primrec.nat_lt.comp (Primrec.list_length.comp hfp) (Primrec.snd.comp (Primrec.fst.comp hfc)))
    (primrec_lookupPrev_gen hfc hiRow hfp)
    (Primrec.ite
      (Primrec.eq.comp (primrec_lookupPrev_gen hfc (primrec_ctxRow0.comp hfc) hlcSing)
        (Primrec.const 0))
      (primrec_lookupPrev_gen hfc hiRow (primrec_redU.comp hfp))
      hbranch_lc)

lemma primrec_expandInterval_gen {α : Type*} [Primcodable α]
    {fc : α → LiftCtx} {fj : α → ℕ}
    (hfc : Primrec fc) (hfj : Primrec fj) :
    Primrec fun a => expandInterval (fc a) (fj a) := by
  unfold expandInterval
  have hrlen : Primrec fun a => (activeRanks (fc a) (fj a)).length :=
    Primrec.list_length.comp (primrec_activeRanks_gen hfc hfj)
  have hsub : Primrec fun x : α × ℕ =>
      (ctxLcurr (fc x.1)).map (signOnSubInt (fc x.1) (fj x.1) x.2) :=
    Primrec.list_map (primrec_ctxLcurr.comp (hfc.comp Primrec.fst))
      (primrec_signOnSubInt_gen (hfc.comp (Primrec.fst.comp Primrec.fst))
        (hfj.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hnr : Primrec fun x : α × ℕ =>
      (ctxLcurr (fc x.1)).map (signAtNewRoot (fc x.1) (fj x.1) x.2) :=
    Primrec.list_map (primrec_ctxLcurr.comp (hfc.comp Primrec.fst))
      (primrec_signAtNewRoot_gen (hfc.comp (Primrec.fst.comp Primrec.fst))
        (hfj.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hpair : Primrec₂ fun a (u : ℕ) =>
      [(ctxLcurr (fc a)).map (signOnSubInt (fc a) (fj a) u),
       (ctxLcurr (fc a)).map (signAtNewRoot (fc a) (fj a) u)] :=
    (Primrec.list_cons.comp hsub (Primrec.list_cons.comp hnr (Primrec.const []))).to₂
  exact Primrec.list_append.comp
    (Primrec.list_flatMap (Primrec.list_range.comp hrlen) hpair)
    (Primrec.list_cons.comp (hsub.comp (Primrec.pair Primrec.id hrlen))
      (Primrec.const []))

lemma primrec_liftTable_gen {α : Type*} [Primcodable α]
    {fCL : α → List UPoly} {fk : α → ℕ} {fM : α → List (List ℕ)}
    (hfCL : Primrec fCL) (hfk : Primrec fk) (hfM : Primrec fM) :
    Primrec fun a => liftTable (fCL a) (fk a) (fM a) := by
  unfold liftTable
  have hfc : Primrec fun a => ((fCL a, fk a), fM a) :=
    Primrec.pair (Primrec.pair hfCL hfk) hfM
  have hmid : Primrec₂ fun a (j : ℕ) =>
      expandInterval ((fCL a, fk a), fM a) j ++ [rootRowNew ((fCL a, fk a), fM a) j] :=
    (Primrec.list_append.comp
      (primrec_expandInterval_gen (hfc.comp Primrec.fst) Primrec.snd)
      (Primrec.list_cons.comp (primrec_rootRowNew_gen (hfc.comp Primrec.fst) Primrec.snd)
        (Primrec.const []))).to₂
  exact Primrec.list_append.comp
    (Primrec.list_flatMap (Primrec.list_range.comp (primrec_ctxNumRoots.comp hfc)) hmid)
    (primrec_expandInterval_gen hfc (primrec_ctxNumRoots.comp hfc))

lemma primrec_buildSignTable : Primrec₂ buildSignTable := by
  unfold buildSignTable
  have hstep : Primrec₂ fun (x : List UPoly × List ℕ) (ma : ℕ × List (List ℕ)) =>
      liftTable x.1 (ma.1 + 2) ma.2 :=
    (primrec_liftTable_gen (Primrec.fst.comp Primrec.fst)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.nat_rec'
    (Primrec.nat_sub.comp (primrec_maxLen.comp Primrec.fst) (Primrec.const 1))
    (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
    hstep).to₂

/- Section 2B: Correctness of closeUPolys, liftTable, and buildSignTable -/

lemma le_maxLen {u : UPoly} {L : List UPoly} (hu : u ∈ L) : u.length ≤ maxLen L := by
  unfold maxLen
  have key : ∀ (l : List UPoly) (init : ℕ),
      init ≤ l.foldl (fun acc w => max acc w.length) init ∧
      ∀ w ∈ l, w.length ≤ l.foldl (fun acc w => max acc w.length) init := by
    intro l
    induction l with
    | nil => intro init; exact ⟨le_rfl, fun _ h => by cases h⟩
    | cons a ls ih =>
      intro init
      obtain ⟨h1, h2⟩ := ih (max init a.length)
      refine ⟨le_trans (le_max_left _ _) h1, fun w hw => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact le_trans (le_max_right _ _) h1
      · exact h2 w hw'
  exact (key L 0).2 u hu

structure IsClosed (CL : List UPoly) : Prop where
  mem_lc : ∀ p ∈ CL, 2 ≤ p.length → [lcU p] ∈ CL
  mem_red : ∀ p ∈ CL, 2 ≤ p.length → redU p ∈ CL
  mem_deriv : ∀ p ∈ CL, 2 ≤ p.length → derivU p ∈ CL
  mem_prem2 : ∀ p ∈ CL, ∀ q ∈ CL, 2 ≤ q.length → q.length ≤ p.length → prem2 p q ∈ CL

lemma mem_closeStep_of_mem {k : ℕ} {CL : List UPoly} {u : UPoly} (hu : u ∈ CL) :
    u ∈ closeStep k CL := by
  unfold closeStep
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hu))

lemma closeStep_new_lt {k : ℕ} (hk : 2 ≤ k) {CL : List UPoly} {u : UPoly}
    (hu : u ∈ closeStep k CL) (hnot : u ∉ CL) : u.length < k := by
  unfold closeStep at hu
  rcases List.mem_append.mp hu with h12 | h3
  · rcases List.mem_append.mp h12 with h01 | h2
    · rcases List.mem_append.mp h01 with h0 | h1
      · exact absurd h0 hnot
      · obtain ⟨p, hp, hu'⟩ := List.mem_flatMap.mp h1
        have hplen : p.length = k := beq_iff_eq.mp (List.mem_filter.mp hp).2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu'
        rcases hu' with rfl | rfl | rfl
        · simp; omega
        · rw [length_redU, hplen]; omega
        · rw [length_derivU, hplen]; omega
    · obtain ⟨p, hp, hu'⟩ := List.mem_flatMap.mp h2
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu'
      have hplen : p.length = k := beq_iff_eq.mp (List.mem_filter.mp hp).2
      have hqlen : q.length = k := beq_iff_eq.mp (List.mem_filter.mp hq).2
      rw [length_prem2 (by omega) (by omega)]; omega
  · obtain ⟨p, hp, hu'⟩ := List.mem_flatMap.mp h3
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu'
    have hplen : k < p.length := of_decide_eq_true (List.mem_filter.mp hp).2
    have hqlen : q.length = k := beq_iff_eq.mp (List.mem_filter.mp hq).2
    rw [length_prem2 (by omega) (by omega)]; omega

lemma indepOfU_closeStep {v k : ℕ} {CL : List UPoly} (h : ∀ u ∈ CL, IndepOfU v u) :
    ∀ u ∈ closeStep k CL, IndepOfU v u := by
  intro u hu
  unfold closeStep at hu
  rcases List.mem_append.mp hu with h12 | h3
  · rcases List.mem_append.mp h12 with h01 | h2
    · rcases List.mem_append.mp h01 with h0 | h1
      · exact h u h0
      · obtain ⟨p, hp, hu'⟩ := List.mem_flatMap.mp h1
        have hpCL : p ∈ CL := (List.mem_filter.mp hp).1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu'
        rcases hu' with rfl | rfl | rfl
        · intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact indepOfU_lcU (h p hpCL)
        · exact indepOfU_redU (h p hpCL)
        · exact indepOfU_derivU (h p hpCL)
    · obtain ⟨p, hp, hu'⟩ := List.mem_flatMap.mp h2
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu'
      exact indepOfU_prem2 (h p (List.mem_filter.mp hp).1) (h q (List.mem_filter.mp hq).1)
  · obtain ⟨p, hp, hu'⟩ := List.mem_flatMap.mp h3
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu'
    exact indepOfU_prem2 (h p (List.mem_filter.mp hp).1) (h q (List.mem_filter.mp hq).1)

lemma closeUPolys_spec (v : ℕ) (L : List UPoly) :
    (∀ u ∈ L, u ∈ closeUPolys L) ∧
    (∀ u ∈ closeUPolys L, u.length ≤ maxLen L) ∧
    IsClosed (closeUPolys L) ∧
    ((∀ u ∈ L, IndepOfU v u) → ∀ u ∈ closeUPolys L, IndepOfU v u) := by
  set D := maxLen L
  let F : ℕ → List UPoly := fun n =>
    n.rec (motive := fun _ => List UPoly) L (fun m acc =>
      if 2 ≤ D - m then closeStep (D - m) acc else acc)
  have hF : ∀ n, n ≤ D →
      (∀ u ∈ L, u ∈ F n) ∧
      (∀ u ∈ F n, u.length ≤ D) ∧
      (∀ p ∈ F n, max 2 (D - n + 1) ≤ p.length →
        [lcU p] ∈ F n ∧ redU p ∈ F n ∧ derivU p ∈ F n) ∧
      (∀ p ∈ F n, ∀ q ∈ F n, max 2 (D - n + 1) ≤ q.length → q.length ≤ p.length →
        prem2 p q ∈ F n) ∧
      ((∀ u ∈ L, IndepOfU v u) → ∀ u ∈ F n, IndepOfU v u) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨fun _ h => h, fun u hu => le_maxLen hu, ?_, ?_, fun h => h⟩
      · intro p hp hge
        have hle : p.length ≤ D := le_maxLen hp
        omega
      · intro p _ q hq hge _
        have hle : q.length ≤ D := le_maxLen hq
        omega
    | succ n ih =>
      intro hn
      obtain ⟨hsub, hlen, h1, h2, hind⟩ := ih (by omega)
      have hFn : F (n + 1) = if 2 ≤ D - n then closeStep (D - n) (F n) else F n := rfl
      by_cases hk : 2 ≤ D - n
      · rw [hFn, if_pos hk]
        set k := D - n
        have hsub' : ∀ u ∈ F n, u ∈ closeStep k (F n) := fun u hu => mem_closeStep_of_mem hu
        have hlen' : ∀ u ∈ closeStep k (F n), u.length ≤ D := by
          intro u hu
          by_cases hu' : u ∈ F n
          · exact hlen u hu'
          · have hlt := closeStep_new_lt hk hu hu'
            omega
        have hge_old : ∀ u ∈ closeStep k (F n), k ≤ u.length → u ∈ F n := by
          intro u hu hge
          by_contra hnot
          have hlt := closeStep_new_lt hk hu hnot
          omega
        refine ⟨fun u hu => hsub' u (hsub u hu), hlen', ?_, ?_,
          fun hL => indepOfU_closeStep (hind hL)⟩
        · intro p hp hge
          have hp_old : p ∈ F n := hge_old p hp (by omega)
          by_cases hpk : p.length = k
          · have hpCk : p ∈ (F n).filter (fun u => u.length == k) :=
              List.mem_filter.mpr ⟨hp_old, beq_iff_eq.mpr hpk⟩
            unfold closeStep
            have hin1 : ∀ w ∈ [ [lcU p], redU p, derivU p ],
                w ∈ ((F n).filter (fun u => u.length == k)).flatMap
                  (fun p => [ [lcU p], redU p, derivU p ]) := fun w hw =>
              List.mem_flatMap.mpr ⟨p, hpCk, hw⟩
            refine ⟨?_, ?_, ?_⟩
            · exact List.mem_append_left _ (List.mem_append_left _
                (List.mem_append_right _ (hin1 _ (by simp))))
            · exact List.mem_append_left _ (List.mem_append_left _
                (List.mem_append_right _ (hin1 _ (by simp))))
            · exact List.mem_append_left _ (List.mem_append_left _
                (List.mem_append_right _ (hin1 _ (by simp))))
          · have hge' : max 2 (D - n + 1) ≤ p.length := by omega
            obtain ⟨ha, hb, hc⟩ := h1 p hp_old hge'
            exact ⟨hsub' _ ha, hsub' _ hb, hsub' _ hc⟩
        · intro p hp q hq hge hpq
          have hp_old : p ∈ F n := hge_old p hp (by omega)
          have hq_old : q ∈ F n := hge_old q hq (by omega)
          by_cases hqk : q.length = k
          · have hqCk : q ∈ (F n).filter (fun u => u.length == k) :=
              List.mem_filter.mpr ⟨hq_old, beq_iff_eq.mpr hqk⟩
            unfold closeStep
            by_cases hpk : p.length = k
            · have hpCk : p ∈ (F n).filter (fun u => u.length == k) :=
                List.mem_filter.mpr ⟨hp_old, beq_iff_eq.mpr hpk⟩
              exact List.mem_append_left _ (List.mem_append_right _
                (List.mem_flatMap.mpr ⟨p, hpCk, List.mem_map.mpr ⟨q, hqCk, rfl⟩⟩))
            · have hpCgt : p ∈ (F n).filter (fun u => decide (k < u.length)) :=
                List.mem_filter.mpr ⟨hp_old, decide_eq_true (by omega)⟩
              exact List.mem_append_right _
                (List.mem_flatMap.mpr ⟨p, hpCgt, List.mem_map.mpr ⟨q, hqCk, rfl⟩⟩)
          · exact hsub' _ (h2 p hp_old q hq_old (by omega) hpq)
      · rw [hFn, if_neg hk]
        refine ⟨hsub, hlen, ?_, ?_, hind⟩
        · intro p hp hge
          exact h1 p hp (by omega)
        · intro p hp q hq hge hpq
          exact h2 p hp q hq (by omega) hpq
  obtain ⟨hsub, hlen, h1, h2, hind⟩ := hF D le_rfl
  refine ⟨hsub, hlen, ⟨?_, ?_, ?_, ?_⟩, hind⟩
  · intro p hp hge; exact (h1 p hp (by omega)).1
  · intro p hp hge; exact (h1 p hp (by omega)).2.1
  · intro p hp hge; exact (h1 p hp (by omega)).2.2
  · intro p hp q hq hge hpq; exact h2 p hp q hq (by omega) hpq

/- Sign Table Invariant -/

structure IsSignTable (L : List UPoly) (ρ : ℕ → ℝ) (roots : List ℝ) (M : List (List ℕ)) : Prop where
  roots_sorted : roots.Pairwise (· < ·)
  roots_complete : ∀ p ∈ L, (∃ x, evalU p ρ x ≠ 0) → ∀ x, evalU p ρ x = 0 → x ∈ roots
  roots_sound : ∀ r ∈ roots, ∃ p ∈ L, (∃ x, evalU p ρ x ≠ 0) ∧ evalU p ρ r = 0
  rows_len : M.length = 2 * roots.length + 1
  row_width : ∀ row ∈ M, row.length = L.length
  at_root : ∀ (j : ℕ) (hj : j < roots.length) (i : ℕ) (hi : i < L.length),
    (M.getD (2 * j + 1) []).getD i 0 = realSign (evalU (L[i]'hi) ρ (roots[j]'hj))
  on_interval : ∀ (j : ℕ) (hj : j ≤ roots.length) (x : ℝ),
    (∀ (h : 0 < j), roots[j - 1]'(by omega) < x) →
    (∀ (h : j < roots.length), x < roots[j]'h) →
    ∀ (i : ℕ) (hi : i < L.length),
      (M.getD (2 * j) []).getD i 0 = realSign (evalU (L[i]'hi) ρ x)

lemma pairwise_lt_getElem {rs : List ℝ} (hs : rs.Pairwise (· < ·))
    {i j : ℕ} (hi : i < rs.length) (hj : j < rs.length) (hij : i < j) :
    rs[i]'hi < rs[j]'hj :=
  (List.pairwise_iff_getElem.mp hs) i j hi hj hij

lemma pairwise_lt_iff {rs : List ℝ} (hs : rs.Pairwise (· < ·))
    {i j : ℕ} (hi : i < rs.length) (hj : j < rs.length) :
    rs[i]'hi < rs[j]'hj ↔ i < j := by
  constructor
  · intro hlt
    by_contra hge
    push Not at hge
    rcases eq_or_lt_of_le hge with rfl | hji
    · exact lt_irrefl _ hlt
    · exact lt_asymm hlt (pairwise_lt_getElem hs hj hi hji)
  · exact pairwise_lt_getElem hs hi hj

lemma exists_in_interval (rs : List ℝ) (hs : rs.Pairwise (· < ·)) (j : ℕ) (hj : j ≤ rs.length) :
    ∃ x : ℝ, (∀ (h : 0 < j), rs[j - 1]'(by omega) < x) ∧
      (∀ (h : j < rs.length), x < rs[j]'h) := by
  by_cases h0 : j = 0
  · subst h0
    by_cases he : rs.length = 0
    · exact ⟨0, fun h => by omega, fun h => by omega⟩
    · refine ⟨rs[0]'(by omega) - 1, fun h => by omega, fun h => ?_⟩
      linarith
  · by_cases hend : j = rs.length
    · subst hend
      refine ⟨rs[rs.length - 1]'(by omega) + 1, fun h => ?_, fun h => by omega⟩
      linarith
    · have hlt : rs[j - 1]'(by omega) < rs[j]'(by omega) :=
        pairwise_lt_getElem hs (by omega) (by omega) (by omega)
      refine ⟨(rs[j - 1]'(by omega) + rs[j]'(by omega)) / 2, fun _ => ?_, fun _ => ?_⟩
      · linarith
      · linarith

lemma findIdx_eq_spec {α : Type*} [DecidableEq α] {L : List α} {a : α} (ha : a ∈ L) :
    L.findIdx (fun w => decide (w = a)) < L.length ∧
    L[L.findIdx (fun w => decide (w = a))]'(List.findIdx_lt_length.mpr ⟨a, ha, decide_eq_true rfl⟩) = a := by
  have hlt : L.findIdx (fun w => decide (w = a)) < L.length :=
    List.findIdx_lt_length.mpr ⟨a, ha, decide_eq_true rfl⟩
  have hsat := List.findIdx_getElem (w := hlt)
  exact ⟨hlt, of_decide_eq_true hsat⟩

lemma lookupPrev_at_root {c : LiftCtx} {ρ : ℕ → ℝ} {roots : List ℝ}
    (hM : IsSignTable (ctxLprev c) ρ roots c.2)
    {j : ℕ} (hj : j < roots.length) {u : UPoly} (hu : u ∈ ctxLprev c) :
    lookupPrev c (c.2.getD (2 * j + 1) []) u = realSign (evalU u ρ (roots[j]'hj)) := by
  unfold lookupPrev
  obtain ⟨hlt, heq⟩ := findIdx_eq_spec hu
  rw [hM.at_root j hj _ hlt, heq]

lemma lookupPrev_on_interval {c : LiftCtx} {ρ : ℕ → ℝ} {roots : List ℝ}
    (hM : IsSignTable (ctxLprev c) ρ roots c.2)
    {j : ℕ} (hj : j ≤ roots.length) {x : ℝ}
    (hxL : ∀ (h : 0 < j), roots[j - 1]'(by omega) < x)
    (hxR : ∀ (h : j < roots.length), x < roots[j]'h)
    {u : UPoly} (hu : u ∈ ctxLprev c) :
    lookupPrev c (c.2.getD (2 * j) []) u = realSign (evalU u ρ x) := by
  unfold lookupPrev
  obtain ⟨hlt, heq⟩ := findIdx_eq_spec hu
  rw [hM.on_interval j hj x hxL hxR _ hlt, heq]

lemma lookupPrev_row0_const {c : LiftCtx} {ρ : ℕ → ℝ} {roots : List ℝ}
    (hM : IsSignTable (ctxLprev c) ρ roots c.2)
    {mp : MPoly} (hmp : [mp] ∈ ctxLprev c) :
    lookupPrev c (ctxRow0 c) [mp] = realSign (evalM mp ρ) := by
  obtain ⟨x, hxL, hxR⟩ := exists_in_interval roots hM.roots_sorted 0 (Nat.zero_le _)
  have h := lookupPrev_on_interval hM (Nat.zero_le _) hxL hxR hmp
  simpa [ctxRow0, evalU] using h

lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (d : α) {i : ℕ} (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
    List.getElem_append_left hi, ← List.getD_eq_getElem _ _ hi]

lemma getD_append_right {α : Type*} (l₁ l₂ : List α) (d : α) {i : ℕ} (hi : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  by_cases h : i < (l₁ ++ l₂).length
  · rw [List.getD_eq_getElem _ _ h, List.getElem_append_right hi,
      ← List.getD_eq_getElem _ _ (by rw [List.length_append] at h; omega)]
  · rw [List.getD_eq_default _ _ (not_lt.mp h),
      List.getD_eq_default _ _ (by rw [List.length_append] at h; omega)]

lemma witnessRoot_spec {CL : List UPoly} {k : ℕ} {M : List (List ℕ)} {ρ : ℕ → ℝ} {roots : List ℝ}
    (hCL : IsClosed CL) (hk : 2 ≤ k)
    (hM : IsSignTable (ctxLprev ((CL, k), M)) ρ roots M)
    {j : ℕ} (hj : j < roots.length) :
    witnessRoot ((CL, k), M) j ∈ ctxLprev ((CL, k), M) ∧
    2 ≤ (witnessRoot ((CL, k), M) j).length ∧
    evalM (lcU (witnessRoot ((CL, k), M) j)) ρ ≠ 0 ∧
    evalU (witnessRoot ((CL, k), M) j) ρ (roots[j]'hj) = 0 := by
  set c : LiftCtx := ((CL, k), M)
  have hck : c.1.2 = k := rfl
  have hfilt_ne : ((ctxLprev c).filter (fun q =>
      decide (2 ≤ q.length) && (lookupPrev c (ctxRow0 c) [lcU q] != 0) &&
        (lookupPrev c (c.2.getD (2 * j + 1) []) q == 0))) ≠ [] := by
    have hex : ∃ n, ∃ q ∈ ctxLprev c, q.length = n ∧ (∃ x, evalU q ρ x ≠ 0) ∧
        evalU q ρ (roots[j]'hj) = 0 := by
      obtain ⟨q, hq, hnz, hroot⟩ := hM.roots_sound (roots[j]'hj) (List.getElem_mem hj)
      exact ⟨q.length, q, hq, rfl, hnz, hroot⟩
    classical
    let n₀ := Nat.find hex
    obtain ⟨q, hq, hqlen, hnz, hroot⟩ := Nat.find_spec hex
    have hq2 : 2 ≤ q.length := by
      by_contra hlt
      push Not at hlt
      obtain ⟨x, hx⟩ := hnz
      have h1 : evalU q ρ x = evalM (q.getD 0 []) ρ := evalU_eq_const (by omega) ρ x
      have h2 : evalU q ρ (roots[j]'hj) = evalM (q.getD 0 []) ρ :=
        evalU_eq_const (by omega) ρ (roots[j]'hj)
      rw [h1, ← h2, hroot] at hx
      exact hx rfl
    have hqCL : q ∈ CL := (List.mem_filter.mp hq).1
    have hqlt : q.length < k := of_decide_eq_true (List.mem_filter.mp hq).2
    have hlc_ne : evalM (lcU q) ρ ≠ 0 := by
      intro hlc0
      have hredCL : redU q ∈ CL := hCL.mem_red q hqCL hq2
      have hred_prev : redU q ∈ ctxLprev c :=
        List.mem_filter.mpr ⟨hredCL, decide_eq_true (by rw [length_redU, hck]; omega)⟩
      have hred_eq : ∀ x, evalU (redU q) ρ x = evalU q ρ x :=
        evalU_redU_of_lc_zero (by omega) hlc0
      have hless : (redU q).length < n₀ := by rw [length_redU]; omega
      exact Nat.find_min hex hless ⟨redU q, hred_prev, rfl,
        by obtain ⟨x, hx⟩ := hnz; exact ⟨x, by rw [hred_eq]; exact hx⟩,
        by rw [hred_eq]; exact hroot⟩
    have hlc_prev : [lcU q] ∈ ctxLprev c :=
      List.mem_filter.mpr ⟨hCL.mem_lc q hqCL hq2, decide_eq_true (by simp [hck]; omega)⟩
    have hq_in : q ∈ (ctxLprev c).filter (fun q =>
        decide (2 ≤ q.length) && (lookupPrev c (ctxRow0 c) [lcU q] != 0) &&
          (lookupPrev c (c.2.getD (2 * j + 1) []) q == 0)) := by
      rw [List.mem_filter]
      refine ⟨hq, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, beq_iff_eq]
      refine ⟨⟨hq2, ?_⟩, ?_⟩
      · rw [lookupPrev_row0_const hM hlc_prev]
        intro h0; exact hlc_ne ((realSign_eq_zero_iff _).mp h0)
      · rw [lookupPrev_at_root hM hj hq, hroot, realSign_eq_zero_iff]
    exact List.ne_nil_of_mem hq_in
  unfold witnessRoot
  dsimp only
  set flist := (ctxLprev c).filter (fun q =>
      decide (2 ≤ q.length) && (lookupPrev c (ctxRow0 c) [lcU q] != 0) &&
        (lookupPrev c (c.2.getD (2 * j + 1) []) q == 0))
  have hmem : flist.headD [] ∈ flist := by
    cases hf : flist with
    | nil => exact absurd hf hfilt_ne
    | cons q rest => exact List.mem_cons_self ..
  obtain ⟨hqprev, hqpred⟩ := List.mem_filter.mp hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, beq_iff_eq] at hqpred
  obtain ⟨⟨hq2, hlc_s⟩, hroot_s⟩ := hqpred
  have hqCL : flist.headD [] ∈ CL := (List.mem_filter.mp hqprev).1
  have hlc_prev : [lcU (flist.headD [])] ∈ ctxLprev c :=
    List.mem_filter.mpr ⟨hCL.mem_lc _ hqCL hq2, decide_eq_true (by simp [hck]; omega)⟩
  rw [lookupPrev_row0_const hM hlc_prev] at hlc_s
  rw [lookupPrev_at_root hM hj hqprev] at hroot_s
  exact ⟨hqprev, hq2, fun h => hlc_s ((realSign_eq_zero_iff _).mpr h),
    (realSign_eq_zero_iff _).mp hroot_s⟩

lemma signAtRoot_spec {CL : List UPoly} {k : ℕ} {M : List (List ℕ)} {ρ : ℕ → ℝ} {roots : List ℝ}
    (hCL : IsClosed CL) (hk : 2 ≤ k)
    (hM : IsSignTable (ctxLprev ((CL, k), M)) ρ roots M)
    {j : ℕ} (hj : j < roots.length) {p : UPoly} (hp : p ∈ ctxLcurr ((CL, k), M)) :
    signAtRoot ((CL, k), M) j p = realSign (evalU p ρ (roots[j]'hj)) := by
  set c : LiftCtx := ((CL, k), M)
  have hck : c.1.2 = k := rfl
  have hpCL : p ∈ CL := (List.mem_filter.mp hp).1
  have hple : p.length ≤ k := of_decide_eq_true (List.mem_filter.mp hp).2
  unfold signAtRoot
  by_cases hlt : p.length < k
  · rw [if_pos hlt]
    have hp_prev : p ∈ ctxLprev c := List.mem_filter.mpr ⟨hpCL, decide_eq_true (by rw [hck]; exact hlt)⟩
    exact lookupPrev_at_root hM hj hp_prev
  · rw [if_neg hlt]
    have hpeq : p.length = k := by omega
    have hlc_prev : [lcU p] ∈ ctxLprev c :=
      List.mem_filter.mpr ⟨hCL.mem_lc p hpCL (by omega), decide_eq_true (by simp [hck]; omega)⟩
    rw [lookupPrev_row0_const hM hlc_prev]
    by_cases hlc0 : realSign (evalM (lcU p) ρ) = 0
    · rw [if_pos hlc0]
      have hred_prev : redU p ∈ ctxLprev c :=
        List.mem_filter.mpr ⟨hCL.mem_red p hpCL (by omega),
          decide_eq_true (by rw [length_redU, hck]; omega)⟩
      rw [lookupPrev_at_root hM hj hred_prev,
        evalU_redU_of_lc_zero (by omega) ((realSign_eq_zero_iff _).mp hlc0)]
    · rw [if_neg hlc0]
      obtain ⟨hq_prev, hq2, hqlc, hqroot⟩ := witnessRoot_spec hCL hk hM hj
      have hqw : witnessRoot ((CL, k), M) j = witnessRoot c j := rfl
      rw [hqw] at hq_prev hq2 hqlc hqroot
      have hqCL : witnessRoot c j ∈ CL := (List.mem_filter.mp hq_prev).1
      have hqlt : (witnessRoot c j).length < k := of_decide_eq_true (List.mem_filter.mp hq_prev).2
      have hprem_prev : prem2 p (witnessRoot c j) ∈ ctxLprev c :=
        List.mem_filter.mpr ⟨hCL.mem_prem2 p hpCL _ hqCL hq2 (by omega),
          decide_eq_true (by rw [length_prem2 hq2 (by omega), hck]; omega)⟩
      rw [lookupPrev_at_root hM hj hprem_prev, evalU_prem2_root hq2 (by omega) hqlc hqroot]

lemma oppSign_iff (a b : ℕ) : oppSign a b = true ↔ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
  unfold oppSign
  simp [Bool.or_eq_true, Bool.and_eq_true]

def OpenInt (roots : List ℝ) (j : ℕ) : Set ℝ :=
  {x : ℝ | (∀ (h : 0 < j), roots.getD (j - 1) 0 < x) ∧
           (∀ (h : j < roots.length), x < roots[j]'h)}

def ClosedInt (roots : List ℝ) (j : ℕ) : Set ℝ :=
  {x : ℝ | (∀ (h : 0 < j), roots.getD (j - 1) 0 ≤ x) ∧
           (∀ (h : j < roots.length), x ≤ roots[j]'h)}

lemma openInt_left {roots : List ℝ} {j : ℕ} (hj : j ≤ roots.length) {x : ℝ}
    (hx : x ∈ OpenInt roots j) (h : 0 < j) : roots[j - 1]'(by omega) < x := by
  have := hx.1 h
  rwa [List.getD_eq_getElem _ _ (by omega)] at this

lemma openInt_mk {roots : List ℝ} {j : ℕ} (hj : j ≤ roots.length) {x : ℝ}
    (hL : ∀ (h : 0 < j), roots[j - 1]'(by omega) < x)
    (hR : ∀ (h : j < roots.length), x < roots[j]'h) : x ∈ OpenInt roots j :=
  ⟨fun h => by rw [List.getD_eq_getElem _ _ (by omega)]; exact hL h, hR⟩

lemma openInt_convex (roots : List ℝ) (j : ℕ) : Convex ℝ (OpenInt roots j) := by
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := hx.1 h; have h2 := hy.1 h
    have hlt : a * roots.getD (j - 1) 0 + b * roots.getD (j - 1) 0 < a * x + b * y := by
      rcases eq_or_lt_of_le ha with rfl | hap
      · have hb1 : b = 1 := by linarith
        subst hb1; linarith
      · nlinarith
    have heq : a * roots.getD (j - 1) 0 + b * roots.getD (j - 1) 0 = roots.getD (j - 1) 0 := by
      rw [← add_mul, hab, one_mul]
    linarith
  · have h1 := hx.2 h; have h2 := hy.2 h
    have hlt : a * x + b * y < a * roots[j]'h + b * roots[j]'h := by
      rcases eq_or_lt_of_le ha with rfl | hap
      · have hb1 : b = 1 := by linarith
        subst hb1; linarith
      · nlinarith
    have heq : a * roots[j]'h + b * roots[j]'h = roots[j]'h := by
      rw [← add_mul, hab, one_mul]
    linarith

lemma closedInt_convex (roots : List ℝ) (j : ℕ) : Convex ℝ (ClosedInt roots j) := by
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := hx.1 h; have h2 := hy.1 h
    have heq : a * roots.getD (j - 1) 0 + b * roots.getD (j - 1) 0 = roots.getD (j - 1) 0 := by
      rw [← add_mul, hab, one_mul]
    nlinarith
  · have h1 := hx.2 h; have h2 := hy.2 h
    have heq : a * roots[j]'h + b * roots[j]'h = roots[j]'h := by
      rw [← add_mul, hab, one_mul]
    nlinarith

lemma interior_closedInt_subset_openInt (roots : List ℝ) (j : ℕ) :
    interior (ClosedInt roots j) ⊆ OpenInt roots j := by
  intro x hx
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
  obtain ⟨ε, hε, hball⟩ := hx
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hmem : x - ε / 2 ∈ ClosedInt roots j :=
      hball (by rw [Metric.mem_ball, Real.dist_eq]; rw [show x - ε / 2 - x = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]; linarith)
    linarith [hmem.1 h]
  · have hmem : x + ε / 2 ∈ ClosedInt roots j :=
      hball (by rw [Metric.mem_ball, Real.dist_eq]; rw [show x + ε / 2 - x = ε / 2 by ring, abs_of_pos (by linarith)]; linarith)
    linarith [hmem.2 h]

lemma evalU_strictMono_or_strictAnti_closedInt {CL : List UPoly} {k : ℕ} {M : List (List ℕ)}
    {ρ : ℕ → ℝ} {roots : List ℝ}
    (hCL : IsClosed CL) (hk : 2 ≤ k)
    (hM : IsSignTable (ctxLprev ((CL, k), M)) ρ roots M)
    {j : ℕ} (hj : j ≤ roots.length) {p : UPoly} (hp : p ∈ ctxLcurr ((CL, k), M))
    (hpeq : p.length = k) (hlc : evalM (lcU p) ρ ≠ 0) :
    StrictMonoOn (fun x => evalU p ρ x) (ClosedInt roots j) ∨
    StrictAntiOn (fun x => evalU p ρ x) (ClosedInt roots j) := by
  have hpCL : p ∈ CL := (List.mem_filter.mp hp).1
  have hdp_prev : derivU p ∈ ctxLprev ((CL, k), M) :=
    List.mem_filter.mpr ⟨hCL.mem_deriv p hpCL (by omega),
      decide_eq_true (by rw [length_derivU]; dsimp only; omega)⟩
  have hdp_nz : ∃ x, evalU (derivU p) ρ x ≠ 0 :=
    evalU_deriv_ne_zero_of_lc_ne_zero (by omega) hlc
  have hnd : ∀ x ∈ OpenInt roots j, evalU (derivU p) ρ x ≠ 0 := by
    intro x hx h0
    have hmem := hM.roots_complete (derivU p) hdp_prev hdp_nz x h0
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    by_cases hmj : m < j
    · have h1 := openInt_left hj hx (by omega)
      have h2 : roots[m]'hm ≤ roots[j - 1]'(by omega) := by
        rcases eq_or_lt_of_le (show m ≤ j - 1 by omega) with rfl | hlt
        · exact le_rfl
        · exact le_of_lt (pairwise_lt_getElem hM.roots_sorted hm (by omega) hlt)
      linarith
    · have h1 := hx.2 (by omega)
      have h2 : roots[j]'(by omega) ≤ roots[m]'hm := by
        rcases eq_or_lt_of_le (show j ≤ m by omega) with rfl | hlt
        · exact le_rfl
        · exact le_of_lt (pairwise_lt_getElem hM.roots_sorted (by omega) hm hlt)
      linarith
  have hcont_d : ContinuousOn (fun x => evalU (derivU p) ρ x) (OpenInt roots j) :=
    (continuous_evalU (derivU p) ρ).continuousOn
  have hconv_o := openInt_convex roots j
  have hconv_c := closedInt_convex roots j
  have hinter := interior_closedInt_subset_openInt roots j
  by_cases hpos : ∃ x₀ ∈ OpenInt roots j, 0 < evalU (derivU p) ρ x₀
  · left
    obtain ⟨x₀, hx₀, hpx₀⟩ := hpos
    have hall : ∀ x ∈ OpenInt roots j, 0 < evalU (derivU p) ρ x := by
      intro x hx
      by_contra hle
      push Not at hle
      have hlt : evalU (derivU p) ρ x < 0 := lt_of_le_of_ne hle (hnd x hx)
      have h0 : (0 : ℝ) ∈ (fun t => evalU (derivU p) ρ t) '' OpenInt roots j :=
        hconv_o.isPreconnected.image _ hcont_d |>.Icc_subset
          ⟨x, hx, rfl⟩ ⟨x₀, hx₀, rfl⟩ ⟨le_of_lt hlt, le_of_lt hpx₀⟩
      obtain ⟨c, hcI, hc0⟩ := h0
      exact hnd c hcI hc0
    exact strictMonoOn_of_deriv_pos hconv_c (continuous_evalU p ρ).continuousOn
      (fun x hx => by rw [(hasDerivAt_evalU p ρ x).deriv]; exact hall x (hinter hx))
  · right
    push Not at hpos
    have hall : ∀ x ∈ OpenInt roots j, evalU (derivU p) ρ x < 0 := fun x hx =>
      lt_of_le_of_ne (hpos x hx) (hnd x hx)
    exact strictAntiOn_of_deriv_neg hconv_c (continuous_evalU p ρ).continuousOn
      (fun x hx => by rw [(hasDerivAt_evalU p ρ x).deriv]; exact hall x (hinter hx))

lemma exists_near_left_endpoint {CL : List UPoly} {k : ℕ} {M : List (List ℕ)}
    {ρ : ℕ → ℝ} {roots : List ℝ}
    (hCL : IsClosed CL) (hk : 2 ≤ k)
    (hM : IsSignTable (ctxLprev ((CL, k), M)) ρ roots M)
    {j : ℕ} (hj : j ≤ roots.length) {p : UPoly} (hp : p ∈ ctxLcurr ((CL, k), M))
    (hpeq : p.length = k) (hlc : evalM (lcU p) ρ ≠ 0)
    (hsL_ne : sL ((CL, k), M) j p ≠ 0) :
    ∀ y ∈ OpenInt roots j, ∃ x ∈ OpenInt roots j, x < y ∧
      realSign (evalU p ρ x) = sL ((CL, k), M) j p := by
  set c : LiftCtx := ((CL, k), M)
  have hck : c.1.2 = k := rfl
  have hpCL : p ∈ CL := (List.mem_filter.mp hp).1
  have hlc_prev : [lcU p] ∈ ctxLprev c :=
    List.mem_filter.mpr ⟨hCL.mem_lc p hpCL (by omega), decide_eq_true (by simp [hck]; omega)⟩
  intro y hy
  by_cases hj0 : j = 0
  · subst hj0
    obtain ⟨B, hB⟩ := evalU_sign_atBot (u := p) (by omega) hlc
    refine ⟨min (y - 1) (-B - 1), ?_, lt_of_le_of_lt (min_le_left _ _) (by linarith), ?_⟩
    · exact openInt_mk hj (fun h => by omega)
        (fun h => lt_trans (lt_of_le_of_lt (min_le_left _ _) (by linarith)) (hy.2 h))
    · rw [hB _ (lt_of_le_of_lt (min_le_right _ _) (by linarith))]
      simp only [sL, ↓reduceIte, lookupPrev_row0_const hM hlc_prev, hck, hpeq]
  · have hpos_j : 0 < j := by omega
    set a := roots[j - 1]'(by omega)
    have hay : a < y := openInt_left hj hy hpos_j
    have hsa : realSign (evalU p ρ a) = sL c j p := by
      simp only [sL, if_neg hj0]
      exact (signAtRoot_spec hCL hk hM (j := j - 1) (by omega) hp).symm
    have hfa_ne : evalU p ρ a ≠ 0 := by
      intro h0; apply hsL_ne; rw [← hsa, h0, realSign_eq_zero_iff]
    have hcont : ContinuousAt (fun t => evalU p ρ t) a := (continuous_evalU p ρ).continuousAt
    have hnhds : {t : ℝ | realSign (evalU p ρ t) = realSign (evalU p ρ a)} ∈ nhds a := by
      rcases lt_or_gt_of_ne hfa_ne with hneg | hpos
      · have h1 : {t : ℝ | evalU p ρ t < 0} ∈ nhds a := hcont.preimage_mem_nhds (Iio_mem_nhds hneg)
        filter_upwards [h1] with t ht
        rw [(realSign_eq_two_iff _).2 ht, (realSign_eq_two_iff _).2 hneg]
      · have h1 : {t : ℝ | 0 < evalU p ρ t} ∈ nhds a := hcont.preimage_mem_nhds (Ioi_mem_nhds hpos)
        filter_upwards [h1] with t ht
        rw [(realSign_eq_one_iff _).2 ht, (realSign_eq_one_iff _).2 hpos]
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    set x := a + min (δ / 2) ((y - a) / 2)
    have hx_gt : a < x := by
      have : 0 < min (δ / 2) ((y - a) / 2) := lt_min (by linarith) (by linarith)
      linarith
    have hx_lt : x < y := by
      have : min (δ / 2) ((y - a) / 2) ≤ (y - a) / 2 := min_le_right _ _
      linarith
    have hx_ball : x ∈ Metric.ball a δ := by
      rw [Metric.mem_ball, Real.dist_eq, show x - a = min (δ / 2) ((y - a) / 2) by ring,
        abs_of_pos (lt_min (by linarith) (by linarith))]
      linarith [min_le_left (δ / 2) ((y - a) / 2)]
    refine ⟨x, openInt_mk hj (fun _ => hx_gt) (fun h => lt_trans hx_lt (hy.2 h)), hx_lt, ?_⟩
    rw [← hsa]
    exact hball hx_ball

lemma exists_near_right_endpoint {CL : List UPoly} {k : ℕ} {M : List (List ℕ)}
    {ρ : ℕ → ℝ} {roots : List ℝ}
    (hCL : IsClosed CL) (hk : 2 ≤ k)
    (hM : IsSignTable (ctxLprev ((CL, k), M)) ρ roots M)
    {j : ℕ} (hj : j ≤ roots.length) {p : UPoly} (hp : p ∈ ctxLcurr ((CL, k), M))
    (hpeq : p.length = k) (hlc : evalM (lcU p) ρ ≠ 0)
    (hsR_ne : sR ((CL, k), M) j p ≠ 0) :
    ∀ y ∈ OpenInt roots j, ∃ x ∈ OpenInt roots j, y < x ∧
      realSign (evalU p ρ x) = sR ((CL, k), M) j p := by
  set c : LiftCtx := ((CL, k), M)
  have hck : c.1.2 = k := rfl
  have hpCL : p ∈ CL := (List.mem_filter.mp hp).1
  have hlc_prev : [lcU p] ∈ ctxLprev c :=
    List.mem_filter.mpr ⟨hCL.mem_lc p hpCL (by omega), decide_eq_true (by simp [hck]; omega)⟩
  have hnr : ctxNumRoots c = roots.length := by
    unfold ctxNumRoots; rw [hM.rows_len]; omega
  intro y hy
  by_cases hjend : j = roots.length
  · subst hjend
    obtain ⟨B, hB⟩ := evalU_sign_atTop (u := p) (by omega) hlc
    refine ⟨max (y + 1) (B + 1), ?_, lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
    · exact openInt_mk hj
        (fun h => lt_trans (openInt_left hj hy h) (lt_of_lt_of_le (by linarith) (le_max_left _ _)))
        (fun h => by omega)
    · rw [hB _ (lt_of_lt_of_le (by linarith) (le_max_right _ _))]
      simp only [sR, hnr, ↓reduceIte, lookupPrev_row0_const hM hlc_prev]
  · have hlt_j : j < roots.length := by omega
    set b := roots[j]'hlt_j
    have hyb : y < b := hy.2 hlt_j
    have hsb : realSign (evalU p ρ b) = sR c j p := by
      simp only [sR, hnr, if_neg hjend]
      exact (signAtRoot_spec hCL hk hM hlt_j hp).symm
    have hfb_ne : evalU p ρ b ≠ 0 := by
      intro h0; apply hsR_ne; rw [← hsb, h0, realSign_eq_zero_iff]
    have hcont : ContinuousAt (fun t => evalU p ρ t) b := (continuous_evalU p ρ).continuousAt
    have hnhds : {t : ℝ | realSign (evalU p ρ t) = realSign (evalU p ρ b)} ∈ nhds b := by
      rcases lt_or_gt_of_ne hfb_ne with hneg | hpos
      · have h1 : {t : ℝ | evalU p ρ t < 0} ∈ nhds b := hcont.preimage_mem_nhds (Iio_mem_nhds hneg)
        filter_upwards [h1] with t ht
        rw [(realSign_eq_two_iff _).2 ht, (realSign_eq_two_iff _).2 hneg]
      · have h1 : {t : ℝ | 0 < evalU p ρ t} ∈ nhds b := hcont.preimage_mem_nhds (Ioi_mem_nhds hpos)
        filter_upwards [h1] with t ht
        rw [(realSign_eq_one_iff _).2 ht, (realSign_eq_one_iff _).2 hpos]
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    set x := b - min (δ / 2) ((b - y) / 2)
    have hx_lt : x < b := by
      have : 0 < min (δ / 2) ((b - y) / 2) := lt_min (by linarith) (by linarith)
      linarith
    have hx_gt : y < x := by
      have : min (δ / 2) ((b - y) / 2) ≤ (b - y) / 2 := min_le_right _ _
      linarith
    have hx_ball : x ∈ Metric.ball b δ := by
      rw [Metric.mem_ball, Real.dist_eq, show x - b = -(min (δ / 2) ((b - y) / 2)) by ring,
        abs_neg, abs_of_pos (lt_min (by linarith) (by linarith))]
      linarith [min_le_left (δ / 2) ((b - y) / 2)]
    refine ⟨x, openInt_mk hj (fun h => lt_trans (openInt_left hj hy h) hx_gt) (fun _ => hx_lt), hx_gt, ?_⟩
    rw [← hsb]
    exact hball hx_ball

lemma active_unique_root {CL : List UPoly} {k : ℕ} {M : List (List ℕ)}
    {ρ : ℕ → ℝ} {roots : List ℝ}
    (hCL : IsClosed CL) (hk : 2 ≤ k)
    (hM : IsSignTable (ctxLprev ((CL, k), M)) ρ roots M)
    {j : ℕ} (hj : j ≤ roots.length) {p : UPoly} (hp : p ∈ ctxLcurr ((CL, k), M))
    (hpeq : p.length = k) (hlc : evalM (lcU p) ρ ≠ 0)
    (hopp : oppSign (sL ((CL, k), M) j p) (sR ((CL, k), M) j p) = true) :
    ∃ α ∈ OpenInt roots j, evalU p ρ α = 0 ∧
      (∀ x ∈ OpenInt roots j, x < α → realSign (evalU p ρ x) = sL ((CL, k), M) j p) ∧
      (∀ x ∈ OpenInt roots j, α < x → realSign (evalU p ρ x) = sR ((CL, k), M) j p) := by
  set c : LiftCtx := ((CL, k), M)
  have hopp' := (oppSign_iff _ _).mp hopp
  have hsL_ne : sL c j p ≠ 0 := by rcases hopp' with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have hsR_ne : sR c j p ≠ 0 := by rcases hopp' with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
  obtain ⟨y₀, hy₀L, hy₀R⟩ := exists_in_interval roots hM.roots_sorted j hj
  have hy₀ : y₀ ∈ OpenInt roots j := openInt_mk hj hy₀L hy₀R
  obtain ⟨xL, hxL, hxLy, hsignL⟩ := exists_near_left_endpoint hCL hk hM hj hp hpeq hlc hsL_ne y₀ hy₀
  obtain ⟨xR, hxR, hyxR, hsignR⟩ := exists_near_right_endpoint hCL hk hM hj hp hpeq hlc hsR_ne y₀ hy₀
  have hxLR : xL < xR := lt_trans hxLy hyxR
  have hmono_or_anti := evalU_strictMono_or_strictAnti_closedInt hCL hk hM hj hp hpeq hlc
  have hopen_sub : OpenInt roots j ⊆ ClosedInt roots j :=
    fun z hz => ⟨fun h => le_of_lt (hz.1 h), fun h => le_of_lt (hz.2 h)⟩
  rcases hopp' with ⟨hL1, hR2⟩ | ⟨hL2, hR1⟩
  · have hfL : 0 < evalU p ρ xL := (realSign_eq_one_iff _).mp (hsignL.trans hL1)
    have hfR : evalU p ρ xR < 0 := (realSign_eq_two_iff _).mp (hsignR.trans hR2)
    have hanti : StrictAntiOn (fun x => evalU p ρ x) (ClosedInt roots j) := by
      rcases hmono_or_anti with hmono | hanti
      · have := hmono (hopen_sub hxL) (hopen_sub hxR) hxLR; linarith
      · exact hanti
    have h0mem : (0 : ℝ) ∈ (fun t => evalU p ρ t) '' Set.Icc xL xR :=
      intermediate_value_Icc' (le_of_lt hxLR) (continuous_evalU p ρ).continuousOn ⟨le_of_lt hfR, le_of_lt hfL⟩
    obtain ⟨α, ⟨hLα, hαR⟩, hα0⟩ := h0mem
    have hαI : α ∈ OpenInt roots j :=
      ⟨fun h => lt_of_lt_of_le (hxL.1 h) hLα, fun h => lt_of_le_of_lt hαR (hxR.2 h)⟩
    refine ⟨α, hαI, hα0, fun x hx hxα => ?_, fun x hx hαx => ?_⟩
    · have hgt : 0 < evalU p ρ x := by
        rw [← hα0]; exact hanti (hopen_sub hx) (hopen_sub hαI) hxα
      rw [(realSign_eq_one_iff _).2 hgt, hL1]
    · have hlt : evalU p ρ x < 0 := by
        rw [← hα0]; exact hanti (hopen_sub hαI) (hopen_sub hx) hαx
      rw [(realSign_eq_two_iff _).2 hlt, hR2]
  · have hfL : evalU p ρ xL < 0 := (realSign_eq_two_iff _).mp (hsignL.trans hL2)
    have hfR : 0 < evalU p ρ xR := (realSign_eq_one_iff _).mp (hsignR.trans hR1)
    have hmono : StrictMonoOn (fun x => evalU p ρ x) (ClosedInt roots j) := by
      rcases hmono_or_anti with hmono | hanti
      · exact hmono
      · have := hanti (hopen_sub hxL) (hopen_sub hxR) hxLR; linarith
    have h0mem : (0 : ℝ) ∈ (fun t => evalU p ρ t) '' Set.Icc xL xR :=
      intermediate_value_Icc (le_of_lt hxLR) (continuous_evalU p ρ).continuousOn ⟨le_of_lt hfL, le_of_lt hfR⟩
    obtain ⟨α, ⟨hLα, hαR⟩, hα0⟩ := h0mem
    have hαI : α ∈ OpenInt roots j :=
      ⟨fun h => lt_of_lt_of_le (hxL.1 h) hLα, fun h => lt_of_le_of_lt hαR (hxR.2 h)⟩
    refine ⟨α, hαI, hα0, fun x hx hxα => ?_, fun x hx hαx => ?_⟩
    · have hlt : evalU p ρ x < 0 := by
        rw [← hα0]; exact hmono (hopen_sub hx) (hopen_sub hαI) hxα
      rw [(realSign_eq_two_iff _).2 hlt, hL2]
    · have hgt : 0 < evalU p ρ x := by
        rw [← hα0]; exact hmono (hopen_sub hαI) (hopen_sub hx) hαx
      rw [(realSign_eq_one_iff _).2 hgt, hR1]

lemma nonactive_constant_sign {CL : List UPoly} {k : ℕ} {M : List (List ℕ)}
    {ρ : ℕ → ℝ} {roots : List ℝ}
    (hCL : IsClosed CL) (hk : 2 ≤ k)
    (hM : IsSignTable (ctxLprev ((CL, k), M)) ρ roots M)
    {j : ℕ} (hj : j ≤ roots.length) {p : UPoly} (hp : p ∈ ctxLcurr ((CL, k), M))
    (hpeq : p.length = k) (hlc : evalM (lcU p) ρ ≠ 0)
    (hnopp : oppSign (sL ((CL, k), M) j p) (sR ((CL, k), M) j p) = false) :
    ∀ x ∈ OpenInt roots j,
      realSign (evalU p ρ x) =
        (if (sL ((CL, k), M) j p != 0) = true then sL ((CL, k), M) j p else sR ((CL, k), M) j p) ∧
      evalU p ρ x ≠ 0 := by
  set c : LiftCtx := ((CL, k), M)
  have hck : c.1.2 = k := rfl
  have hpCL : p ∈ CL := (List.mem_filter.mp hp).1
  have hlc_prev : [lcU p] ∈ ctxLprev c :=
    List.mem_filter.mpr ⟨hCL.mem_lc p hpCL (by omega), decide_eq_true (by simp [hck]; omega)⟩
  have hnr : ctxNumRoots c = roots.length := by
    unfold ctxNumRoots; rw [hM.rows_len]; omega
  have hmono_or_anti := evalU_strictMono_or_strictAnti_closedInt hCL hk hM hj hp hpeq hlc
  have hopen_sub : OpenInt roots j ⊆ ClosedInt roots j :=
    fun z hz => ⟨fun h => le_of_lt (hz.1 h), fun h => le_of_lt (hz.2 h)⟩
  have hno_root : ∀ α ∈ OpenInt roots j, evalU p ρ α ≠ 0 := by
    intro α hα hα0
    have hsL_eq : ∀ s : ℕ, (∀ x ∈ OpenInt roots j, x < α → realSign (evalU p ρ x) = s) →
        s = 1 ∨ s = 2 → sL c j p = s := by
      intro s hs _
      by_cases hj0 : j = 0
      · subst hj0
        obtain ⟨B, hB⟩ := evalU_sign_atBot (u := p) (by omega) hlc
        set x := min (α - 1) (-B - 1)
        have hxI : x ∈ OpenInt roots 0 :=
          openInt_mk hj (fun h => by omega)
            (fun h => lt_trans (lt_of_le_of_lt (min_le_left _ _) (by linarith)) (hα.2 h))
        have hxα : x < α := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have h1 := hs x hxI hxα
        have h2 := hB x (lt_of_le_of_lt (min_le_right _ _) (by linarith))
        simp only [sL, ↓reduceIte, lookupPrev_row0_const hM hlc_prev, hck, ← hpeq]
        rw [← h2, h1]
      · have hpos_j : 0 < j := by omega
        set a := roots[j - 1]'(by omega)
        have haC : a ∈ ClosedInt roots j :=
          ⟨fun _ => by rw [List.getD_eq_getElem _ _ (by omega)],
           fun h => le_of_lt (pairwise_lt_getElem hM.roots_sorted (by omega) h (by omega))⟩
        have haα : a < α := openInt_left hj hα hpos_j
        have hsa : sL c j p = realSign (evalU p ρ a) := by
          simp only [sL, if_neg hj0]
          exact signAtRoot_spec hCL hk hM (j := j - 1) (by omega) hp
        rw [hsa]
        set x := (a + α) / 2
        have hax : a < x := by dsimp only [x]; linarith
        have hxα : x < α := by dsimp only [x]; linarith
        have hxI : x ∈ OpenInt roots j :=
          openInt_mk hj (fun _ => hax) (fun h => lt_trans hxα (hα.2 h))
        have hxs := hs x hxI hxα
        rcases hmono_or_anti with hmono | hanti
        · have hfx : evalU p ρ x < 0 := by rw [← hα0]; exact hmono (hopen_sub hxI) (hopen_sub hα) hxα
          have hfa : evalU p ρ a < 0 := lt_trans (hmono haC (hopen_sub hxI) hax) hfx
          rw [(realSign_eq_two_iff _).2 hfa, ← hxs, (realSign_eq_two_iff _).2 hfx]
        · have hfx : 0 < evalU p ρ x := by rw [← hα0]; exact hanti (hopen_sub hxI) (hopen_sub hα) hxα
          have hfa : 0 < evalU p ρ a := lt_trans hfx (hanti haC (hopen_sub hxI) hax)
          rw [(realSign_eq_one_iff _).2 hfa, ← hxs, (realSign_eq_one_iff _).2 hfx]
    have hsR_eq : ∀ s : ℕ, (∀ x ∈ OpenInt roots j, α < x → realSign (evalU p ρ x) = s) →
        s = 1 ∨ s = 2 → sR c j p = s := by
      intro s hs _
      by_cases hjend : j = roots.length
      · subst hjend
        obtain ⟨B, hB⟩ := evalU_sign_atTop (u := p) (by omega) hlc
        set x := max (α + 1) (B + 1)
        have hxI : x ∈ OpenInt roots roots.length :=
          openInt_mk hj
            (fun h => lt_trans (openInt_left hj hα h) (lt_of_lt_of_le (by linarith) (le_max_left _ _)))
            (fun h => by omega)
        have hαx : α < x := lt_of_lt_of_le (by linarith) (le_max_left _ _)
        have h1 := hs x hxI hαx
        have h2 := hB x (lt_of_lt_of_le (by linarith) (le_max_right _ _))
        simp only [sR, hnr, ↓reduceIte, lookupPrev_row0_const hM hlc_prev]
        rw [← h2, h1]
      · have hlt_j : j < roots.length := by omega
        set b := roots[j]'hlt_j
        have hbC : b ∈ ClosedInt roots j :=
          ⟨fun h => by rw [List.getD_eq_getElem _ _ (by omega)]; exact le_of_lt (pairwise_lt_getElem hM.roots_sorted (by omega) hlt_j (by omega)),
           fun _ => le_rfl⟩
        have hαb : α < b := hα.2 hlt_j
        have hsb : sR c j p = realSign (evalU p ρ b) := by
          simp only [sR, hnr, if_neg hjend]
          exact signAtRoot_spec hCL hk hM hlt_j hp
        rw [hsb]
        set x := (α + b) / 2
        have hαx : α < x := by dsimp only [x]; linarith
        have hxb : x < b := by dsimp only [x]; linarith
        have hxI : x ∈ OpenInt roots j :=
          openInt_mk hj (fun h => lt_trans (openInt_left hj hα h) hαx) (fun _ => hxb)
        have hxs := hs x hxI hαx
        rcases hmono_or_anti with hmono | hanti
        · have hfx : 0 < evalU p ρ x := by rw [← hα0]; exact hmono (hopen_sub hα) (hopen_sub hxI) hαx
          have hfb : 0 < evalU p ρ b := lt_trans hfx (hmono (hopen_sub hxI) hbC hxb)
          rw [(realSign_eq_one_iff _).2 hfb, ← hxs, (realSign_eq_one_iff _).2 hfx]
        · have hfx : evalU p ρ x < 0 := by rw [← hα0]; exact hanti (hopen_sub hα) (hopen_sub hxI) hαx
          have hfb : evalU p ρ b < 0 := lt_trans (hanti (hopen_sub hxI) hbC hxb) hfx
          rw [(realSign_eq_two_iff _).2 hfb, ← hxs, (realSign_eq_two_iff _).2 hfx]
    rcases hmono_or_anti with hmono | hanti
    · have hL2 : sL c j p = 2 := hsL_eq 2 (fun x hx hxα =>
        (realSign_eq_two_iff _).2 (by rw [← hα0]; exact hmono (hopen_sub hx) (hopen_sub hα) hxα)) (Or.inr rfl)
      have hR1 : sR c j p = 1 := hsR_eq 1 (fun x hx hαx =>
        (realSign_eq_one_iff _).2 (by rw [← hα0]; exact hmono (hopen_sub hα) (hopen_sub hx) hαx)) (Or.inl rfl)
      have : oppSign (sL c j p) (sR c j p) = true := (oppSign_iff _ _).2 (Or.inr ⟨hL2, hR1⟩)
      rw [hnopp] at this; cases this
    · have hL1 : sL c j p = 1 := hsL_eq 1 (fun x hx hxα =>
        (realSign_eq_one_iff _).2 (by rw [← hα0]; exact hanti (hopen_sub hx) (hopen_sub hα) hxα)) (Or.inl rfl)
      have hR2 : sR c j p = 2 := hsR_eq 2 (fun x hx hαx =>
        (realSign_eq_two_iff _).2 (by rw [← hα0]; exact hanti (hopen_sub hα) (hopen_sub hx) hαx)) (Or.inr rfl)
      have : oppSign (sL c j p) (sR c j p) = true := (oppSign_iff _ _).2 (Or.inl ⟨hL1, hR2⟩)
      rw [hnopp] at this; cases this
  have hconst_sign : ∀ x y : ℝ, x ∈ OpenInt roots j → y ∈ OpenInt roots j →
      realSign (evalU p ρ x) = realSign (evalU p ρ y) := by
    intro x y hx hy
    have hfx := hno_root x hx
    have hfy := hno_root y hy
    rcases lt_or_gt_of_ne hfx with hxn | hxp
    · rcases lt_or_gt_of_ne hfy with hyn | hyp
      · rw [(realSign_eq_two_iff _).2 hxn, (realSign_eq_two_iff _).2 hyn]
      · exfalso
        have h0 : (0 : ℝ) ∈ (fun t => evalU p ρ t) '' OpenInt roots j :=
          (openInt_convex roots j).isPreconnected.image _ (continuous_evalU p ρ).continuousOn
            |>.Icc_subset ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨le_of_lt hxn, le_of_lt hyp⟩
        obtain ⟨z, hz, hz0⟩ := h0
        exact hno_root z hz hz0
    · rcases lt_or_gt_of_ne hfy with hyn | hyp
      · exfalso
        have h0 : (0 : ℝ) ∈ (fun t => evalU p ρ t) '' OpenInt roots j :=
          (openInt_convex roots j).isPreconnected.image _ (continuous_evalU p ρ).continuousOn
            |>.Icc_subset ⟨y, hy, rfl⟩ ⟨x, hx, rfl⟩ ⟨le_of_lt hyn, le_of_lt hxp⟩
        obtain ⟨z, hz, hz0⟩ := h0
        exact hno_root z hz hz0
      · rw [(realSign_eq_one_iff _).2 hxp, (realSign_eq_one_iff _).2 hyp]
  intro x hx
  refine ⟨?_, hno_root x hx⟩
  by_cases hsL : sL c j p = 0
  · have hcond : (sL c j p != 0) = false := by simp [hsL]
    rw [if_neg (by simp [hcond])]
    have hsR_ne : sR c j p ≠ 0 := by
      intro hsR
      have hj0 : j ≠ 0 := by
        intro h0; subst h0
        simp only [sL, ↓reduceIte, lookupPrev_row0_const hM hlc_prev] at hsL
        unfold negInfSign at hsL
        split_ifs at hsL
        · exact hlc ((realSign_eq_zero_iff _).mp hsL)
        · unfold negSign at hsL
          rcases lt_or_gt_of_ne hlc with hcn | hcp
          · rw [(realSign_eq_two_iff _).2 hcn] at hsL; simp at hsL
          · rw [(realSign_eq_one_iff _).2 hcp] at hsL; simp at hsL
      have hjend : j ≠ roots.length := by
        intro hend; subst hend
        simp only [sR, hnr, ↓reduceIte, lookupPrev_row0_const hM hlc_prev] at hsR
        exact hlc ((realSign_eq_zero_iff _).mp hsR)
      have ha0 : evalU p ρ (roots[j - 1]'(by omega)) = 0 := by
        simp only [sL, if_neg hj0] at hsL
        rw [signAtRoot_spec hCL hk hM (j := j - 1) (by omega) hp] at hsL
        exact (realSign_eq_zero_iff _).mp hsL
      have hb0 : evalU p ρ (roots[j]'(by omega)) = 0 := by
        simp only [sR, hnr, if_neg hjend] at hsR
        rw [signAtRoot_spec hCL hk hM (by omega) hp] at hsR
        exact (realSign_eq_zero_iff _).mp hsR
      have hab : roots[j - 1]'(by omega) < roots[j]'(by omega) :=
        pairwise_lt_getElem hM.roots_sorted (by omega) (by omega) (by omega)
      have haC : roots[j - 1]'(by omega) ∈ ClosedInt roots j :=
        ⟨fun _ => by rw [List.getD_eq_getElem _ _ (by omega)],
         fun h => le_of_lt (pairwise_lt_getElem hM.roots_sorted (by omega) h (by omega))⟩
      have hbC : roots[j]'(by omega) ∈ ClosedInt roots j :=
        ⟨fun h => by rw [List.getD_eq_getElem _ _ (by omega)]; exact le_of_lt (pairwise_lt_getElem hM.roots_sorted (by omega) (by omega) (by omega)),
         fun _ => le_rfl⟩
      rcases hmono_or_anti with hmono | hanti
      · have := hmono haC hbC hab; linarith
      · have := hanti haC hbC hab; linarith
    obtain ⟨y, hy, _, hyR⟩ := exists_near_right_endpoint hCL hk hM hj hp hpeq hlc hsR_ne x hx
    rw [hconst_sign x y hx hy, hyR]
  · have hcond : (sL c j p != 0) = true := bne_iff_ne.mpr hsL
    rw [if_pos hcond]
    obtain ⟨y, hy, _, hyL⟩ := exists_near_left_endpoint hCL hk hM hj hp hpeq hlc hsL x hx
    rw [hconst_sign x y hx hy, hyL]

/- Extracting the unique root of an active polynomial and proving expandInterval & liftTable -/

noncomputable def activeRoot (c : LiftCtx) (ρ : ℕ → ℝ) (roots : List ℝ) (j : ℕ) (p : UPoly) : ℝ :=
  Classical.epsilon (fun α : ℝ => α ∈ OpenInt roots j ∧ evalU p ρ α = 0)

lemma activeRoot_spec {CL : List UPoly} {k : ℕ} {M : List (List ℕ)}
    {ρ : ℕ → ℝ} {roots : List ℝ}
    (hCL : IsClosed CL) (hk : 2 ≤ k)
    (hM : IsSignTable (ctxLprev ((CL, k), M)) ρ roots M)
    {j : ℕ} (hj : j ≤ roots.length) {p : UPoly} (hp : p ∈ activeList ((CL, k), M) j) :
    activeRoot ((CL, k), M) ρ roots j p ∈ OpenInt roots j ∧
    evalU p ρ (activeRoot ((CL, k), M) ρ roots j p) = 0 ∧
      (∀ x ∈ OpenInt roots j, x < activeRoot ((CL, k), M) ρ roots j p →
        realSign (evalU p ρ x) = sL ((CL, k), M) j p) ∧
      (∀ x ∈ OpenInt roots j, activeRoot ((CL, k), M) ρ roots j p < x →
        realSign (evalU p ρ x) = sR ((CL, k), M) j p) := by
  set c : LiftCtx := ((CL, k), M)
  have hck : c.1.2 = k := rfl
  set α := activeRoot c ρ roots j p
  have hp_mem : p ∈ ctxLcurr c := (List.mem_filter.mp hp).1
  have hp_act : isActive c j p = true := (List.mem_filter.mp hp).2
  unfold isActive at hp_act
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, hck] at hp_act
  obtain ⟨⟨hpeq, hlc_s⟩, hopp⟩ := hp_act
  have hpCL : p ∈ CL := (List.mem_filter.mp hp_mem).1
  have hlc_prev : [lcU p] ∈ ctxLprev c :=
    List.mem_filter.mpr ⟨hCL.mem_lc p hpCL (by omega), decide_eq_true (by simp [hck]; omega)⟩
  rw [lookupPrev_row0_const hM hlc_prev] at hlc_s
  have hlc : evalM (lcU p) ρ ≠ 0 := fun h => hlc_s ((realSign_eq_zero_iff _).mpr h)
  obtain ⟨α₀, hα₀I, hα₀0, hL, hR⟩ := active_unique_root hCL hk hM hj hp_mem hpeq hlc hopp
  have hex : ∃ β : ℝ, β ∈ OpenInt roots j ∧ evalU p ρ β = 0 := ⟨α₀, hα₀I, hα₀0⟩
  have hspec : α ∈ OpenInt roots j ∧ evalU p ρ α = 0 := Classical.epsilon_spec hex
  have heq : α = α₀ := by
    have hopp' := (oppSign_iff _ _).mp hopp
    have hsL_c : sL ((CL, k), M) j p = sL c j p := rfl
    have hsR_c : sR ((CL, k), M) j p = sR c j p := rfl
    rcases lt_trichotomy α α₀ with hlt | heq | hgt
    · have hs := hL α hspec.1 hlt
      rw [hspec.2, (realSign_eq_zero_iff _).2 rfl, hsL_c] at hs
      rcases hopp' with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    · exact heq
    · have hs := hR α hspec.1 hgt
      rw [hspec.2, (realSign_eq_zero_iff _).2 rfl, hsR_c] at hs
      rcases hopp' with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
  change α ∈ OpenInt roots j ∧ evalU p ρ α = 0 ∧
    (∀ x ∈ OpenInt roots j, x < α → realSign (evalU p ρ x) = sL c j p) ∧
    (∀ x ∈ OpenInt roots j, α < x → realSign (evalU p ρ x) = sR c j p)
  rw [heq]
  exact ⟨hα₀I, hα₀0, hL, hR⟩

lemma ltRoot_iff {CL : List UPoly} {k : ℕ} {M : List (List ℕ)}
    {ρ : ℕ → ℝ} {roots : List ℝ}
    (hCL : IsClosed CL) (hk : 2 ≤ k)
    (hM : IsSignTable (ctxLprev ((CL, k), M)) ρ roots M)
    {j : ℕ} (hj : j ≤ roots.length)
    {p₁ p₂ : UPoly} (hp₁ : p₁ ∈ activeList ((CL, k), M) j) (hp₂ : p₂ ∈ activeList ((CL, k), M) j) :
    ltRoot ((CL, k), M) j p₁ p₂ = true ↔
      activeRoot ((CL, k), M) ρ roots j p₁ < activeRoot ((CL, k), M) ρ roots j p₂ := by
  set c : LiftCtx := ((CL, k), M)
  have hck : c.1.2 = k := rfl
  obtain ⟨hα₁I, hα₁0, hL₁, hR₁⟩ := activeRoot_spec hCL hk hM hj hp₁
  obtain ⟨hα₂I, hα₂0, _, _⟩ := activeRoot_spec hCL hk hM hj hp₂
  have hact₁ := (List.mem_filter.mp hp₁).2
  have hact₂ := (List.mem_filter.mp hp₂).2
  unfold isActive at hact₁ hact₂
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, hck] at hact₁ hact₂
  have hp₁CL : p₁ ∈ CL := (List.mem_filter.mp (List.mem_filter.mp hp₁).1).1
  have hp₂CL : p₂ ∈ CL := (List.mem_filter.mp (List.mem_filter.mp hp₂).1).1
  have hlc₂_prev : [lcU p₂] ∈ ctxLprev c :=
    List.mem_filter.mpr ⟨hCL.mem_lc p₂ hp₂CL (by omega), decide_eq_true (by simp [hck]; omega)⟩
  have hlc₂ : evalM (lcU p₂) ρ ≠ 0 := by
    intro h0; exact hact₂.1.2 (by rw [lookupPrev_row0_const hM hlc₂_prev, h0, realSign_eq_zero_iff])
  have hprem_prev : prem2 p₁ p₂ ∈ ctxLprev c :=
    List.mem_filter.mpr ⟨hCL.mem_prem2 p₁ hp₁CL p₂ hp₂CL (by omega) (by omega),
      decide_eq_true (by rw [length_prem2 (by omega) (by omega), hck]; omega)⟩
  unfold ltRoot
  rw [beq_iff_eq, lookupPrev_on_interval hM hj (openInt_left hj hα₂I) hα₂I.2 hprem_prev,
    evalU_prem2_root (by omega) (by omega) hlc₂ hα₂0]
  have hopp₁ := (oppSign_iff _ _).mp hact₁.2
  have hsL_c : sL ((CL, k), M) j p₁ = sL c j p₁ := rfl
  have hsR_c : sR ((CL, k), M) j p₁ = sR c j p₁ := rfl
  constructor
  · intro hsign
    rcases lt_trichotomy (activeRoot c ρ roots j p₁) (activeRoot c ρ roots j p₂) with hlt | heq | hgt
    · exact hlt
    · rw [← heq, hα₁0, (realSign_eq_zero_iff _).2 rfl, hsR_c] at hsign
      rcases hopp₁ with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
    · rw [hL₁ _ hα₂I hgt, hsL_c, hsR_c] at hsign
      rcases hopp₁ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · intro hlt
    exact hR₁ _ hα₂I hlt

lemma rootRank_lt_iff {CL : List UPoly} {k : ℕ} {M : List (List ℕ)}
    {ρ : ℕ → ℝ} {roots : List ℝ}
    (hCL : IsClosed CL) (hk : 2 ≤ k)
    (hM : IsSignTable (ctxLprev ((CL, k), M)) ρ roots M)
    {j : ℕ} (hj : j ≤ roots.length)
    {p₁ p₂ : UPoly} (hp₁ : p₁ ∈ activeList ((CL, k), M) j) (hp₂ : p₂ ∈ activeList ((CL, k), M) j) :
    (rootRank ((CL, k), M) j p₁ < rootRank ((CL, k), M) j p₂ ↔
      activeRoot ((CL, k), M) ρ roots j p₁ < activeRoot ((CL, k), M) ρ roots j p₂) ∧
    (rootRank ((CL, k), M) j p₁ = rootRank ((CL, k), M) j p₂ ↔
      activeRoot ((CL, k), M) ρ roots j p₁ = activeRoot ((CL, k), M) ρ roots j p₂) := by
  set c : LiftCtx := ((CL, k), M)
  set act := activeList c j
  have hlt_imp : ∀ a b, a ∈ act → b ∈ act →
      activeRoot c ρ roots j a < activeRoot c ρ roots j b →
      rootRank c j a < rootRank c j b := by
    intro a b ha hb hab
    unfold rootRank
    have hsub : ∀ l : List UPoly, (∀ q ∈ l, q ∈ act) →
        (l.filter (fun q => ltRoot c j q a)).length ≤ (l.filter (fun q => ltRoot c j q b)).length ∧
        (a ∈ l → (l.filter (fun q => ltRoot c j q a)).length < (l.filter (fun q => ltRoot c j q b)).length) := by
      intro l
      induction l with
      | nil => intro _; exact ⟨le_rfl, fun h => (by cases h)⟩
      | cons q ls ih =>
        intro hl
        obtain ⟨hle, hlt⟩ := ih (fun w hw => hl w (List.mem_cons_of_mem _ hw))
        have hq : q ∈ act := hl q (List.mem_cons_self ..)
        simp only [List.filter_cons]
        by_cases hqa : ltRoot c j q a = true
        · have hqab : activeRoot c ρ roots j q < activeRoot c ρ roots j b :=
            lt_trans ((ltRoot_iff hCL hk hM hj hq ha).mp hqa) hab
          have hqb : ltRoot c j q b = true := (ltRoot_iff hCL hk hM hj hq hb).mpr hqab
          rw [if_pos hqa, if_pos hqb, List.length_cons, List.length_cons]
          refine ⟨Nat.add_le_add_right hle 1, fun ha' => ?_⟩
          rcases List.mem_cons.mp ha' with rfl | hmem
          · exact absurd ((ltRoot_iff hCL hk hM hj ha ha).mp hqa) (lt_irrefl _)
          · exact Nat.add_lt_add_right (hlt hmem) 1
        · rw [if_neg hqa]
          by_cases hqb : ltRoot c j q b = true
          · rw [if_pos hqb, List.length_cons]
            exact ⟨Nat.le_succ_of_le hle, fun _ => Nat.lt_succ_of_le hle⟩
          · rw [if_neg hqb]
            refine ⟨hle, fun ha' => ?_⟩
            rcases List.mem_cons.mp ha' with rfl | hmem
            · exact absurd ((ltRoot_iff hCL hk hM hj ha hb).mpr hab) hqb
            · exact hlt hmem
    exact (hsub act (fun _ h => h)).2 ha
  have heq_imp : activeRoot c ρ roots j p₁ = activeRoot c ρ roots j p₂ →
      rootRank c j p₁ = rootRank c j p₂ := by
    intro heq
    unfold rootRank
    congr 1
    apply List.filter_congr
    intro q hq
    rw [Bool.eq_iff_iff, ltRoot_iff hCL hk hM hj hq hp₁, ltRoot_iff hCL hk hM hj hq hp₂, heq]
  constructor
  · constructor
    · intro hlt
      rcases lt_trichotomy (activeRoot c ρ roots j p₁) (activeRoot c ρ roots j p₂) with h | h | h
      · exact h
      · rw [heq_imp h] at hlt; omega
      · have := hlt_imp p₂ p₁ hp₂ hp₁ h; omega
    · exact hlt_imp p₁ p₂ hp₁ hp₂
  · constructor
    · intro heq
      rcases lt_trichotomy (activeRoot c ρ roots j p₁) (activeRoot c ρ roots j p₂) with h | h | h
      · have := hlt_imp p₁ p₂ hp₁ hp₂ h; omega
      · exact h
      · have := hlt_imp p₂ p₁ hp₂ hp₁ h; omega
    · exact heq_imp

lemma rootRank_lt_length {CL : List UPoly} {k : ℕ} {M : List (List ℕ)}
    {ρ : ℕ → ℝ} {roots : List ℝ}
    (hCL : IsClosed CL) (hk : 2 ≤ k)
    (hM : IsSignTable (ctxLprev ((CL, k), M)) ρ roots M)
    {j : ℕ} (hj : j ≤ roots.length)
    {p : UPoly} (hp : p ∈ activeList ((CL, k), M) j) :
    rootRank ((CL, k), M) j p < (activeList ((CL, k), M) j).length := by
  set c : LiftCtx := ((CL, k), M)
  unfold rootRank
  have hnot : ltRoot c j p p = false := by
    by_contra h
    have h' : ltRoot c j p p = true := by cases hlt : ltRoot c j p p <;> simp_all
    exact lt_irrefl _ ((ltRoot_iff hCL hk hM hj hp hp).mp h')
  have key : ∀ l : List UPoly, p ∈ l → (l.filter (fun q => ltRoot c j q p)).length < l.length := by
    intro l
    induction l with
    | nil => intro h; cases h
    | cons q ls ih =>
      intro hmem
      simp only [List.filter_cons, List.length_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · rw [hnot]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact Nat.lt_succ_of_le (List.length_filter_le _ _)
      · split_ifs
        · rw [List.length_cons]; exact Nat.add_lt_add_right (ih hmem') 1
        · exact Nat.lt_succ_of_le (le_of_lt (ih hmem'))
  exact key (activeList c j) hp

noncomputable def newRootsInterval (c : LiftCtx) (ρ : ℕ → ℝ) (roots : List ℝ) (j : ℕ) : List ℝ :=
  (activeRanks c j).map fun r =>
    activeRoot c ρ roots j (((activeList c j).filter (fun p => rootRank c j p == r)).headD [])

lemma activeRanks_pairwise_lt (c : LiftCtx) (j : ℕ) : (activeRanks c j).Pairwise (· < ·) := by
  unfold activeRanks
  exact List.Pairwise.filter _ List.pairwise_lt_range

lemma newRootsInterval_length (c : LiftCtx) (ρ : ℕ → ℝ) (roots : List ℝ) (j : ℕ) :
    (newRootsInterval c ρ roots j).length = (activeRanks c j).length := by
  simp [newRootsInterval]

lemma newRootsInterval_spec {CL : List UPoly} {k : ℕ} {M : List (List ℕ)}
    {ρ : ℕ → ℝ} {roots : List ℝ}
    (hCL : IsClosed CL) (hk : 2 ≤ k)
    (hM : IsSignTable (ctxLprev ((CL, k), M)) ρ roots M)
    {j : ℕ} (hj : j ≤ roots.length) :
    (newRootsInterval ((CL, k), M) ρ roots j).length = (activeRanks ((CL, k), M) j).length ∧
    (newRootsInterval ((CL, k), M) ρ roots j).Pairwise (· < ·) ∧
    (∀ x ∈ newRootsInterval ((CL, k), M) ρ roots j, x ∈ OpenInt roots j) ∧
    (∀ u (hu : u < (newRootsInterval ((CL, k), M) ρ roots j).length),
      ∃ p ∈ activeList ((CL, k), M) j,
        rootRank ((CL, k), M) j p = (activeRanks ((CL, k), M) j)[u]'(by rwa [← newRootsInterval_length]) ∧
        activeRoot ((CL, k), M) ρ roots j p = (newRootsInterval ((CL, k), M) ρ roots j)[u]'hu) ∧
    (∀ p ∈ activeList ((CL, k), M) j,
      ∃ u, ∃ hu : u < (newRootsInterval ((CL, k), M) ρ roots j).length,
        (activeRanks ((CL, k), M) j)[u]'(by rwa [← newRootsInterval_length]) = rootRank ((CL, k), M) j p ∧
        (newRootsInterval ((CL, k), M) ρ roots j)[u]'hu = activeRoot ((CL, k), M) ρ roots j p) := by
  set c : LiftCtx := ((CL, k), M)
  set nr := newRootsInterval c ρ roots j
  set rks := activeRanks c j
  have hlen : nr.length = rks.length := newRootsInterval_length c ρ roots j
  have hrep : ∀ r ∈ rks,
      let p := ((activeList c j).filter (fun p => rootRank c j p == r)).headD []
      p ∈ activeList c j ∧ rootRank c j p = r := by
    intro r hr
    have hany := (List.mem_filter.mp hr).2
    rw [List.any_eq_true] at hany
    obtain ⟨p₀, hp₀, hr₀⟩ := hany
    have hne : ((activeList c j).filter (fun p => rootRank c j p == r)) ≠ [] :=
      List.ne_nil_of_mem (List.mem_filter.mpr ⟨hp₀, hr₀⟩)
    cases hf : ((activeList c j).filter (fun p => rootRank c j p == r)) with
    | nil => exact absurd hf hne
    | cons p rest =>
      simp only [List.headD_cons]
      have hpmem : p ∈ (activeList c j).filter (fun p => rootRank c j p == r) := by
        rw [hf]; exact List.mem_cons_self ..
      exact ⟨(List.mem_filter.mp hpmem).1, beq_iff_eq.mp (List.mem_filter.mp hpmem).2⟩
  have hsorted : nr.Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro u₁ u₂ hu₁ hu₂ hlt
    have hu₁' : u₁ < rks.length := by omega
    have hu₂' : u₂ < rks.length := by omega
    simp only [nr, newRootsInterval, List.getElem_map]
    obtain ⟨hp₁, hrk₁⟩ := hrep rks[u₁] (List.getElem_mem hu₁')
    obtain ⟨hp₂, hrk₂⟩ := hrep rks[u₂] (List.getElem_mem hu₂')
    rw [← (rootRank_lt_iff hCL hk hM hj hp₁ hp₂).1, hrk₁, hrk₂]
    exact (List.pairwise_iff_getElem.mp (activeRanks_pairwise_lt c j)) u₁ u₂ hu₁' hu₂' hlt
  have hinI : ∀ x ∈ nr, x ∈ OpenInt roots j := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hp, _⟩ := hrep r hr
    exact (activeRoot_spec hCL hk hM hj hp).1
  have hforU : ∀ u (hu : u < nr.length), ∃ p ∈ activeList c j,
      rootRank c j p = rks[u]'(by omega) ∧ activeRoot c ρ roots j p = nr[u]'hu := by
    intro u hu
    have hu' : u < rks.length := by omega
    obtain ⟨hp, hrk⟩ := hrep rks[u] (List.getElem_mem hu')
    refine ⟨_, hp, hrk, ?_⟩
    simp [nr, newRootsInterval, rks]
  have hforP : ∀ p ∈ activeList c j, ∃ u, ∃ hu : u < nr.length,
      rks[u]'(by omega) = rootRank c j p ∧ nr[u]'hu = activeRoot c ρ roots j p := by
    intro p hp
    have hrk_mem : rootRank c j p ∈ rks := by
      unfold rks activeRanks
      rw [List.mem_filter, List.mem_range, List.any_eq_true]
      exact ⟨rootRank_lt_length hCL hk hM hj hp, ⟨p, hp, beq_iff_eq.mpr rfl⟩⟩
    obtain ⟨u, hu', hrku⟩ := List.getElem_of_mem hrk_mem
    have hu : u < nr.length := by omega
    obtain ⟨q, hq, hrkq, hαq⟩ := hforU u hu
    refine ⟨u, hu, hrku, ?_⟩
    rw [← hαq]
    exact (rootRank_lt_iff hCL hk hM hj hq hp).2.mp (hrkq.trans hrku)
  exact ⟨hlen, hsorted, hinI, hforU, hforP⟩

lemma expandInterval_spec {CL : List UPoly} {k : ℕ} {M : List (List ℕ)}
    {ρ : ℕ → ℝ} {roots : List ℝ}
    (hCL : IsClosed CL) (hk : 2 ≤ k)
    (hM : IsSignTable (ctxLprev ((CL, k), M)) ρ roots M)
    {j : ℕ} (hj : j ≤ roots.length) :
    (expandInterval ((CL, k), M) j).length = 2 * (newRootsInterval ((CL, k), M) ρ roots j).length + 1 ∧
    (∀ row ∈ expandInterval ((CL, k), M) j, row.length = (ctxLcurr ((CL, k), M)).length) ∧
    (∀ u (hu : u < (newRootsInterval ((CL, k), M) ρ roots j).length) (i : ℕ)
      (hi : i < (ctxLcurr ((CL, k), M)).length),
      ((expandInterval ((CL, k), M) j).getD (2 * u + 1) []).getD i 0 =
        realSign (evalU ((ctxLcurr ((CL, k), M))[i]'hi) ρ ((newRootsInterval ((CL, k), M) ρ roots j)[u]'hu))) ∧
    (∀ u (hu : u ≤ (newRootsInterval ((CL, k), M) ρ roots j).length) (x : ℝ), x ∈ OpenInt roots j →
      (∀ (h : 0 < u), (newRootsInterval ((CL, k), M) ρ roots j)[u - 1]'(by omega) < x) →
      (∀ (h : u < (newRootsInterval ((CL, k), M) ρ roots j).length),
        x < (newRootsInterval ((CL, k), M) ρ roots j)[u]'h) →
      ∀ (i : ℕ) (hi : i < (ctxLcurr ((CL, k), M)).length),
        ((expandInterval ((CL, k), M) j).getD (2 * u) []).getD i 0 =
          realSign (evalU ((ctxLcurr ((CL, k), M))[i]'hi) ρ x)) := by
  set c : LiftCtx := ((CL, k), M)
  have hck : c.1.2 = k := rfl
  set nr := newRootsInterval c ρ roots j
  set rows := expandInterval c j
  obtain ⟨hnr_len', hnr_sorted', hnr_inI', hforU', hforP'⟩ := newRootsInterval_spec hCL hk hM hj
  set rks := activeRanks c j
  have hnr_len : nr.length = rks.length := hnr_len'
  have hnr_sorted : nr.Pairwise (· < ·) := hnr_sorted'
  have hnr_inI : ∀ x ∈ nr, x ∈ OpenInt roots j := hnr_inI'
  have hforU : ∀ u (hu : u < nr.length), ∃ p ∈ activeList c j,
      rootRank c j p = rks[u]'(by omega) ∧ activeRoot c ρ roots j p = nr[u]'hu := hforU'
  have hforP : ∀ p ∈ activeList c j, ∃ u, ∃ hu : u < nr.length,
      rks[u]'(by omega) = rootRank c j p ∧ nr[u]'hu = activeRoot c ρ roots j p := hforP'
  have hflat_len : ∀ n (f : ℕ → List (List ℕ)), (∀ u < n, (f u).length = 2) →
      ((List.range n).flatMap f).length = 2 * n := by
    intro n f hf
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append, List.flatMap_singleton,
        ih (fun u hu => hf u (by omega)), hf n (Nat.lt_succ_self n)]
      omega
  have hflat_get : ∀ n (f : ℕ → List (List ℕ)), (∀ u < n, (f u).length = 2) →
      ∀ u (hu : u < n),
        (((List.range n).flatMap f).getD (2 * u) [] = (f u).getD 0 []) ∧
        (((List.range n).flatMap f).getD (2 * u + 1) [] = (f u).getD 1 []) := by
    intro n f hf
    induction n with
    | zero => intro u hu; omega
    | succ n ih =>
      intro u hu
      have hlen_pre : ((List.range n).flatMap f).length = 2 * n :=
        hflat_len n f (fun m hm => hf m (by omega))
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      by_cases hun : u < n
      · obtain ⟨h0, h1⟩ := ih (fun m hm => hf m (by omega)) u hun
        exact ⟨by rw [getD_append_left _ _ _ (by omega), h0],
               by rw [getD_append_left _ _ _ (by omega), h1]⟩
      · have h_eq : u = n := by omega
        subst h_eq
        exact ⟨by rw [getD_append_right _ _ _ (by omega), hlen_pre, Nat.sub_self],
               by rw [getD_append_right _ _ _ (by omega), hlen_pre, show 2 * u + 1 - 2 * u = 1 by omega]⟩
  set f : ℕ → List (List ℕ) := fun u =>
    [(ctxLcurr c).map (signOnSubInt c j u), (ctxLcurr c).map (signAtNewRoot c j u)]
  have hf2 : ∀ u < rks.length, (f u).length = 2 := fun _ _ => rfl
  have hrows_len : rows.length = 2 * nr.length + 1 := by
    unfold rows expandInterval
    rw [List.length_append, hflat_len rks.length f hf2, List.length_singleton, hnr_len]
  have hrows_width : ∀ row ∈ rows, row.length = (ctxLcurr c).length := by
    intro row hrow
    unfold rows expandInterval at hrow
    rcases List.mem_append.mp hrow with h1 | h2
    · obtain ⟨u, _, hrow'⟩ := List.mem_flatMap.mp h1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow'
      rcases hrow' with rfl | rfl <;> simp
    · simp only [List.mem_singleton] at h2; subst h2; simp
  have hget_odd : ∀ u (hu : u < nr.length),
      rows.getD (2 * u + 1) [] = (ctxLcurr c).map (signAtNewRoot c j u) := by
    intro u hu
    have hu' : u < rks.length := by omega
    have hfl : ((List.range rks.length).flatMap f).length = 2 * rks.length := hflat_len _ f hf2
    change ((List.range rks.length).flatMap f ++ [(ctxLcurr c).map (signOnSubInt c j rks.length)]).getD (2 * u + 1) [] = _
    rw [getD_append_left _ _ _ (by omega), (hflat_get rks.length f hf2 u hu').2]
    rfl
  have hget_even : ∀ u (hu : u ≤ nr.length),
      rows.getD (2 * u) [] = (ctxLcurr c).map (signOnSubInt c j u) := by
    intro u hu
    have hfl : ((List.range rks.length).flatMap f).length = 2 * rks.length := hflat_len _ f hf2
    change ((List.range rks.length).flatMap f ++ [(ctxLcurr c).map (signOnSubInt c j rks.length)]).getD (2 * u) [] = _
    by_cases hlt : u < rks.length
    · rw [getD_append_left _ _ _ (by omega), (hflat_get rks.length f hf2 u hlt).1]
      rfl
    · have hueq : u = rks.length := by omega
      subst hueq
      rw [getD_append_right _ _ _ (by omega), hfl, Nat.sub_self]
      rfl
  have hcommon : ∀ (x : ℝ) (hx : x ∈ OpenInt roots j) (p : UPoly) (hp : p ∈ ctxLcurr c),
      (p.length < k → lookupPrev c (c.2.getD (2 * j) []) p = realSign (evalU p ρ x)) ∧
      (¬ p.length < k → lookupPrev c (ctxRow0 c) [lcU p] = 0 →
        lookupPrev c (c.2.getD (2 * j) []) (redU p) = realSign (evalU p ρ x)) ∧
      (¬ p.length < k → lookupPrev c (ctxRow0 c) [lcU p] ≠ 0 →
        oppSign (sL c j p) (sR c j p) = false →
        (if (sL c j p != 0) = true then sL c j p else sR c j p) = realSign (evalU p ρ x)) := by
    intro x hx p hp
    have hpCL : p ∈ CL := (List.mem_filter.mp hp).1
    have hple : p.length ≤ k := of_decide_eq_true (List.mem_filter.mp hp).2
    refine ⟨?_, ?_, ?_⟩
    · intro hlt
      exact lookupPrev_on_interval hM hj (openInt_left hj hx) hx.2
        (List.mem_filter.mpr ⟨hpCL, decide_eq_true (by rw [hck]; exact hlt)⟩)
    · intro hge hlc0
      have hpeq : p.length = k := by omega
      have hlc_prev : [lcU p] ∈ ctxLprev c :=
        List.mem_filter.mpr ⟨hCL.mem_lc p hpCL (by omega), decide_eq_true (by simp [hck]; omega)⟩
      rw [lookupPrev_row0_const hM hlc_prev] at hlc0
      have hred_prev : redU p ∈ ctxLprev c :=
        List.mem_filter.mpr ⟨hCL.mem_red p hpCL (by omega),
          decide_eq_true (by rw [length_redU, hck]; omega)⟩
      rw [lookupPrev_on_interval hM hj (openInt_left hj hx) hx.2 hred_prev,
        evalU_redU_of_lc_zero (by omega) ((realSign_eq_zero_iff _).mp hlc0)]
    · intro hge hlc_ne hnopp
      have hpeq : p.length = k := by omega
      have hlc_prev : [lcU p] ∈ ctxLprev c :=
        List.mem_filter.mpr ⟨hCL.mem_lc p hpCL (by omega), decide_eq_true (by simp [hck]; omega)⟩
      rw [lookupPrev_row0_const hM hlc_prev] at hlc_ne
      have hlc : evalM (lcU p) ρ ≠ 0 := fun h => hlc_ne ((realSign_eq_zero_iff _).mpr h)
      exact (nonactive_constant_sign hCL hk hM hj hp hpeq hlc hnopp x hx).1.symm
  refine ⟨hrows_len, hrows_width, ?_, ?_⟩
  · intro u hu i hi
    change (rows.getD (2 * u + 1) []).getD i 0 = realSign (evalU ((ctxLcurr c)[i]'hi) ρ (nr[u]'hu))
    rw [hget_odd u hu, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map]
    set p := (ctxLcurr c)[i]'hi
    have hp : p ∈ ctxLcurr c := List.getElem_mem hi
    have hnrI : nr[u]'hu ∈ OpenInt roots j := hnr_inI _ (List.getElem_mem hu)
    obtain ⟨hc1, hc2, hc3⟩ := hcommon (nr[u]'hu) hnrI p hp
    unfold signAtNewRoot
    by_cases hlt : p.length < k
    · rw [if_pos (by rw [hck]; exact hlt)]; exact hc1 hlt
    · rw [if_neg (by rw [hck]; exact hlt)]
      by_cases hlc0 : lookupPrev c (ctxRow0 c) [lcU p] = 0
      · rw [if_pos hlc0]; exact hc2 hlt hlc0
      · rw [if_neg hlc0]
        by_cases hopp : oppSign (sL c j p) (sR c j p) = true
        · rw [if_neg (by simp [hopp])]
          have hp_act : p ∈ activeList c j := by
            rw [activeList, List.mem_filter]
            have hple : p.length ≤ k := of_decide_eq_true (List.mem_filter.mp hp).2
            refine ⟨hp, ?_⟩
            unfold isActive
            simp [hck, show p.length = k by omega, hlc0, hopp]
          obtain ⟨q, hq_act, hqrk, hqα⟩ := hforU u hu
          have htarget : rks.getD u 0 = rks[u]'(by omega) :=
            List.getD_eq_getElem _ _ (by omega)
          dsimp only
          change (if rootRank c j p < rks.getD u 0 then sR c j p
            else if rootRank c j p = rks.getD u 0 then 0 else sL c j p) =
            realSign (evalU p ρ (nr[u]'hu))
          rw [htarget, ← hqrk, ← hqα]
          obtain ⟨_, hαp0, hLp, hRp⟩ := activeRoot_spec hCL hk hM hj hp_act
          obtain ⟨hαqI, _, _, _⟩ := activeRoot_spec hCL hk hM hj hq_act
          obtain ⟨hrk_lt, hrk_eq⟩ := rootRank_lt_iff hCL hk hM hj hp_act hq_act
          by_cases h1 : rootRank c j p < rootRank c j q
          · rw [if_pos h1]
            exact (hRp _ hαqI (hrk_lt.mp h1)).symm
          · rw [if_neg h1]
            by_cases h2 : rootRank c j p = rootRank c j q
            · rw [if_pos h2, ← hrk_eq.mp h2, hαp0, (realSign_eq_zero_iff _).2 rfl]
            · rw [if_neg h2]
              have h3 : activeRoot c ρ roots j q < activeRoot c ρ roots j p :=
                (rootRank_lt_iff hCL hk hM hj hq_act hp_act).1.mp (by change rootRank c j q < rootRank c j p; omega)
              exact (hLp _ hαqI h3).symm
        · have hnopp : oppSign (sL c j p) (sR c j p) = false := by
            cases h : oppSign (sL c j p) (sR c j p) <;> simp_all
          rw [if_pos (by simp [hnopp])]
          exact hc3 hlt hlc0 hnopp
  · intro u hu x hx hxL hxR i hi
    change (rows.getD (2 * u) []).getD i 0 = realSign (evalU ((ctxLcurr c)[i]'hi) ρ x)
    rw [hget_even u hu, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map]
    set p := (ctxLcurr c)[i]'hi
    have hp : p ∈ ctxLcurr c := List.getElem_mem hi
    obtain ⟨hc1, hc2, hc3⟩ := hcommon x hx p hp
    unfold signOnSubInt
    by_cases hlt : p.length < k
    · rw [if_pos (by rw [hck]; exact hlt)]; exact hc1 hlt
    · rw [if_neg (by rw [hck]; exact hlt)]
      by_cases hlc0 : lookupPrev c (ctxRow0 c) [lcU p] = 0
      · rw [if_pos hlc0]; exact hc2 hlt hlc0
      · rw [if_neg hlc0]
        by_cases hopp : oppSign (sL c j p) (sR c j p) = true
        · rw [if_neg (by simp [hopp])]
          have hp_act : p ∈ activeList c j := by
            rw [activeList, List.mem_filter]
            have hple : p.length ≤ k := of_decide_eq_true (List.mem_filter.mp hp).2
            refine ⟨hp, ?_⟩
            unfold isActive
            simp [hck, show p.length = k by omega, hlc0, hopp]
          obtain ⟨_, _, hLp, hRp⟩ := activeRoot_spec hCL hk hM hj hp_act
          obtain ⟨up, hup, hrkup, hαup⟩ := hforP p hp_act
          by_cases hu0 : u = 0
          · subst hu0
            rw [if_pos rfl]
            have hx_lt_nr0 : x < nr[0]'(by omega) := hxR (by omega)
            have hnr0_le : nr[0]'(by omega) ≤ nr[up]'hup := by
              rcases Nat.eq_zero_or_pos up with rfl | hpos
              · exact le_rfl
              · exact le_of_lt (pairwise_lt_getElem hnr_sorted (by omega) hup hpos)
            rw [hαup] at hnr0_le
            exact (hLp x hx (lt_of_lt_of_le hx_lt_nr0 hnr0_le)).symm
          · rw [if_neg hu0]
            have htarget : rks.getD (u - 1) 0 = rks[u - 1]'(by omega) :=
              List.getD_eq_getElem _ _ (by omega)
            have hrks_pw : rks.Pairwise (· < ·) := activeRanks_pairwise_lt c j
            change (if rootRank c j p ≤ rks.getD (u - 1) 0 then sR c j p else sL c j p) =
              realSign (evalU p ρ x)
            rw [htarget, ← hrkup]
            by_cases hle : rks[up]'(by omega) ≤ rks[u - 1]'(by omega)
            · rw [if_pos hle]
              have hup_le : up ≤ u - 1 := by
                by_contra hgt; push Not at hgt
                have := (List.pairwise_iff_getElem.mp hrks_pw)
                  (u - 1) up (by omega) (by omega) hgt
                omega
              have hα_le : nr[up]'hup ≤ nr[u - 1]'(by omega) := by
                rcases eq_or_lt_of_le hup_le with rfl | hlt'
                · exact le_rfl
                · exact le_of_lt (pairwise_lt_getElem hnr_sorted hup (by omega) hlt')
              have hx_gt : nr[u - 1]'(by omega) < x := hxL (by omega)
              rw [hαup] at hα_le
              exact (hRp x hx (lt_of_le_of_lt hα_le hx_gt)).symm
            · rw [if_neg hle]
              have hu_le_up : u ≤ up := by
                by_contra hlt'; push Not at hlt'
                have hup_le : up ≤ u - 1 := by omega
                rcases eq_or_lt_of_le hup_le with rfl | hlt''
                · exact hle le_rfl
                · exact hle (le_of_lt ((List.pairwise_iff_getElem.mp hrks_pw)
                    up (u - 1) (by omega) (by omega) hlt''))
              have hx_lt : x < nr[u]'(by omega) := hxR (by omega)
              have hnr_le : nr[u]'(by omega) ≤ nr[up]'hup := by
                rcases eq_or_lt_of_le hu_le_up with rfl | hlt'
                · exact le_rfl
                · exact le_of_lt (pairwise_lt_getElem hnr_sorted (by omega) hup hlt')
              rw [hαup] at hnr_le
              exact (hLp x hx (lt_of_lt_of_le hx_lt hnr_le)).symm
        · have hnopp : oppSign (sL c j p) (sR c j p) = false := by
            cases h : oppSign (sL c j p) (sR c j p) <;> simp_all
          rw [if_pos (by simp [hnopp])]
          exact hc3 hlt hlc0 hnopp

/- Stitch all expanded intervals and old roots together into liftTable_spec -/

lemma stitch_sign_table {L : List UPoly} {ρ : ℕ → ℝ}
    {oldRoots : List ℝ} (hold_sorted : oldRoots.Pairwise (· < ·))
    {newR : ℕ → List ℝ} {expM : ℕ → List (List ℕ)} {oldRow : ℕ → List ℕ}
    (hnew_sorted : ∀ j ≤ oldRoots.length, (newR j).Pairwise (· < ·))
    (hnew_inI : ∀ j ≤ oldRoots.length, ∀ x ∈ newR j, x ∈ OpenInt oldRoots j)
    (hexp_len : ∀ j ≤ oldRoots.length, (expM j).length = 2 * (newR j).length + 1)
    (hexp_w : ∀ j ≤ oldRoots.length, ∀ row ∈ expM j, row.length = L.length)
    (hold_w : ∀ j < oldRoots.length, (oldRow j).length = L.length)
    (hexp_root : ∀ j ≤ oldRoots.length, ∀ u (hu : u < (newR j).length) i (hi : i < L.length),
      ((expM j).getD (2 * u + 1) []).getD i 0 = realSign (evalU (L[i]'hi) ρ ((newR j)[u]'hu)))
    (hexp_int : ∀ j ≤ oldRoots.length, ∀ u (hu : u ≤ (newR j).length) (x : ℝ),
      x ∈ OpenInt oldRoots j →
      (∀ (h : 0 < u), (newR j)[u - 1]'(by omega) < x) →
      (∀ (h : u < (newR j).length), x < (newR j)[u]'h) →
      ∀ i (hi : i < L.length), ((expM j).getD (2 * u) []).getD i 0 = realSign (evalU (L[i]'hi) ρ x))
    (hold_root : ∀ j (hj : j < oldRoots.length) i (hi : i < L.length),
      (oldRow j).getD i 0 = realSign (evalU (L[i]'hi) ρ (oldRoots[j]'hj)))
    (hcomp : ∀ p ∈ L, (∃ x, evalU p ρ x ≠ 0) → ∀ x, evalU p ρ x = 0 →
      x ∈ oldRoots ∨ ∃ j ≤ oldRoots.length, x ∈ newR j)
    (hsound_old : ∀ r ∈ oldRoots, ∃ p ∈ L, (∃ x, evalU p ρ x ≠ 0) ∧ evalU p ρ r = 0)
    (hsound_new : ∀ j ≤ oldRoots.length, ∀ r ∈ newR j,
      ∃ p ∈ L, (∃ x, evalU p ρ x ≠ 0) ∧ evalU p ρ r = 0) :
    let allR := (List.range oldRoots.length).flatMap
      (fun j => newR j ++ [oldRoots.getD j 0]) ++ newR oldRoots.length
    let allM := (List.range oldRoots.length).flatMap
      (fun j => expM j ++ [oldRow j]) ++ expM oldRoots.length
    IsSignTable L ρ allR allM := by
  intro allR allM
  -- Helper: prefix up to k ≤ oldRoots.length
  let prefR : ℕ → List ℝ := fun m =>
    (List.range m).flatMap (fun j => newR j ++ [oldRoots.getD j 0])
  let prefM : ℕ → List (List ℕ) := fun m =>
    (List.range m).flatMap (fun j => expM j ++ [oldRow j])
  have hpref : ∀ m, (hm : m ≤ oldRoots.length) →
      (prefR m).Pairwise (· < ·) ∧
      (∀ x ∈ prefR m, ∀ (hm : m < oldRoots.length), x < oldRoots[m]'hm) ∧
      (∀ x ∈ prefR m, ∀ y ∈ newR m, x < y) ∧
      (prefM m).length = 2 * (prefR m).length ∧
      (∀ row ∈ prefM m, row.length = L.length) ∧
      (∀ r ∈ prefR m, ∃ p ∈ L, (∃ x, evalU p ρ x ≠ 0) ∧ evalU p ρ r = 0) ∧
      (∀ (j : ℕ) (hj : j < (prefR m).length) (i : ℕ) (hi : i < L.length),
        ((prefM m).getD (2 * j + 1) []).getD i 0 =
          realSign (evalU (L[i]'hi) ρ ((prefR m)[j]'hj))) ∧
      (∀ (j : ℕ) (hj : j < (prefR m).length) (x : ℝ),
        (∀ (h : 0 < j), (prefR m)[j - 1]'(by omega) < x) →
        x < (prefR m)[j]'hj →
        ∀ (i : ℕ) (hi : i < L.length),
          ((prefM m).getD (2 * j) []).getD i 0 = realSign (evalU (L[i]'hi) ρ x)) ∧
      (∀ (x : ℝ), x ∈ prefR m ↔
        (∃ j, ∃ (_ : j < m), x = oldRoots[j]'(by omega) ∨ x ∈ newR j)) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨List.Pairwise.nil, fun _ h => (by cases h), fun _ h => (by cases h),
        rfl, fun _ h => (by cases h), fun _ h => (by cases h),
        fun _ h => by simp [prefR] at h, fun _ h => by simp [prefR] at h,
        fun _ => by simp [prefR]⟩
    | succ m ih =>
      intro hm
      obtain ⟨hsort, hlt_old, hlt_new, hlenM, hwM, hsound, hat_r, hon_i, hmem⟩ := ih (by omega)
      have hR_eq : prefR (m + 1) = prefR m ++ (newR m ++ [oldRoots[m]'(by omega)]) := by
        simp only [prefR, List.range_succ, List.flatMap_append, List.flatMap_singleton]
        rw [List.getD_eq_getElem _ _ (by omega)]
      have hM_eq : prefM (m + 1) = prefM m ++ (expM m ++ [oldRow m]) := by
        simp only [prefM, List.range_succ, List.flatMap_append, List.flatMap_singleton]
      have hnr_lt_old : ∀ y ∈ newR m, y < oldRoots[m]'(by omega) :=
        fun y hy => (hnew_inI m (by omega) y hy).2 (by omega)
      have hsort_tail : (newR m ++ [oldRoots[m]'(by omega)]).Pairwise (· < ·) := by
        rw [List.pairwise_append]
        exact ⟨hnew_sorted m (by omega), List.pairwise_singleton _ _,
          fun y hy z hz => by simp only [List.mem_singleton] at hz; subst hz; exact hnr_lt_old y hy⟩
      have hsort' : (prefR (m + 1)).Pairwise (· < ·) := by
        rw [hR_eq, List.pairwise_append]
        refine ⟨hsort, hsort_tail, fun x hx y hy => ?_⟩
        rcases List.mem_append.mp hy with hy1 | hy2
        · exact hlt_new x hx y hy1
        · simp only [List.mem_singleton] at hy2; subst hy2; exact hlt_old x hx (by omega)
      have hlt_old' : ∀ x ∈ prefR (m + 1), ∀ (hm' : m + 1 < oldRoots.length),
          x < oldRoots[m + 1]'hm' := by
        intro x hx hm'
        have hstep : oldRoots[m]'(by omega) < oldRoots[m + 1]'hm' :=
          pairwise_lt_getElem hold_sorted (by omega) hm' (by omega)
        rw [hR_eq] at hx
        rcases List.mem_append.mp hx with h1 | h2
        · exact lt_trans (hlt_old x h1 (by omega)) hstep
        · rcases List.mem_append.mp h2 with h2a | h2b
          · exact lt_trans (hnr_lt_old x h2a) hstep
          · simp only [List.mem_singleton] at h2b; subst h2b; exact hstep
      have hlt_new' : ∀ x ∈ prefR (m + 1), ∀ y ∈ newR (m + 1), x < y := by
        intro x hx y hy
        have hy_gt : oldRoots[m]'(by omega) < y := openInt_left hm (hnew_inI (m + 1) hm y hy) (by omega)
        rw [hR_eq] at hx
        rcases List.mem_append.mp hx with h1 | h2
        · exact lt_trans (hlt_old x h1 (by omega)) hy_gt
        · rcases List.mem_append.mp h2 with h2a | h2b
          · exact lt_trans (hnr_lt_old x h2a) hy_gt
          · simp only [List.mem_singleton] at h2b; subst h2b; exact hy_gt
      have hlenM' : (prefM (m + 1)).length = 2 * (prefR (m + 1)).length := by
        rw [hM_eq, hR_eq, List.length_append, List.length_append, List.length_append,
          List.length_append, List.length_singleton, List.length_singleton,
          hlenM, hexp_len m (by omega)]
        omega
      have hwM' : ∀ row ∈ prefM (m + 1), row.length = L.length := by
        intro row hrow
        rw [hM_eq] at hrow
        rcases List.mem_append.mp hrow with h1 | h2
        · exact hwM row h1
        · rcases List.mem_append.mp h2 with h2a | h2b
          · exact hexp_w m (by omega) row h2a
          · simp only [List.mem_singleton] at h2b; subst h2b; exact hold_w m (by omega)
      have hsound' : ∀ r ∈ prefR (m + 1), ∃ p ∈ L, (∃ x, evalU p ρ x ≠ 0) ∧ evalU p ρ r = 0 := by
        intro r hr
        rw [hR_eq] at hr
        rcases List.mem_append.mp hr with h1 | h2
        · exact hsound r h1
        · rcases List.mem_append.mp h2 with h2a | h2b
          · exact hsound_new m (by omega) r h2a
          · simp only [List.mem_singleton] at h2b; subst h2b
            exact hsound_old _ (List.getElem_mem (by omega))
      have hmem' : ∀ x, x ∈ prefR (m + 1) ↔
          ∃ j, ∃ (_ : j < m + 1), x = oldRoots[j]'(by omega) ∨ x ∈ newR j := by
        intro x
        rw [hR_eq, List.mem_append, List.mem_append, List.mem_singleton, hmem]
        constructor
        · rintro (⟨j, hj, h⟩ | (h | rfl))
          · exact ⟨j, by omega, h⟩
          · exact ⟨m, Nat.lt_succ_self m, Or.inr h⟩
          · exact ⟨m, Nat.lt_succ_self m, Or.inl rfl⟩
        · rintro ⟨j, hj, h⟩
          by_cases hjm : j < m
          · exact Or.inl ⟨j, hjm, h⟩
          · have : j = m := by omega
            subst this
            rcases h with rfl | h
            · exact Or.inr (Or.inr rfl)
            · exact Or.inr (Or.inl h)
      -- Helper for last element of prefR m when m > 0:
      have hlast_pref : ∀ (hpos : 0 < m), ∃ hne : 0 < (prefR m).length,
          (prefR m)[(prefR m).length - 1]'(by omega) = oldRoots[m - 1]'(by omega) := by
        intro hpos
        have hm' : m = (m - 1) + 1 := by omega
        have hEq : prefR m = prefR (m - 1) ++ (newR (m - 1) ++ [oldRoots[m - 1]'(by omega)]) := by
          conv_lhs => rw [hm']
          simp only [prefR, List.range_succ, List.flatMap_append, List.flatMap_singleton]
          rw [List.getD_eq_getElem _ _ (by omega)]
        have hlen_pos : 0 < (prefR m).length := by rw [hEq]; simp
        refine ⟨hlen_pos, ?_⟩
        have hidx : (prefR m).length - 1 = (prefR (m - 1)).length + (newR (m - 1)).length := by
          rw [hEq]; simp
        have hge1 : (prefR (m - 1)).length ≤ (prefR m).length - 1 := by omega
        have hge1 : (prefR (m - 1)).length ≤ (prefR m).length - 1 := by omega
        have hcast : (prefR m)[(prefR m).length - 1]'(by omega) =
            (prefR (m - 1) ++ (newR (m - 1) ++ [oldRoots[m - 1]'(by omega)]))[(prefR m).length - 1]'(by rw [← hEq]; omega) := by
          congr 1
        rw [hcast, List.getElem_append_right hge1]
        have hsub : (prefR m).length - 1 - (prefR (m - 1)).length = (newR (m - 1)).length := by omega
        simp [hsub]
      -- Now verify hat_r' and hon_i':
      set P := (prefR m).length
      set N := (newR m).length
      have hlenR' : (prefR (m + 1)).length = P + N + 1 := by
        rw [hR_eq]; simp [P, N]; omega
      have hgetR_lt : ∀ j (hj : j < P), (prefR (m + 1))[j]'(by omega) = (prefR m)[j]'hj := by
        intro j hj
        have h1 : (prefR (m + 1)).getD j 0 = (prefR m).getD j 0 := by
          rw [hR_eq, getD_append_left _ _ _ hj]
        rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj] at h1
      have hgetR_mid : ∀ u (hu : u < N),
          (prefR (m + 1))[P + u]'(by omega) = (newR m)[u]'hu := by
        intro u hu
        have h1 : (prefR (m + 1)).getD (P + u) 0 = (newR m).getD u 0 := by
          rw [hR_eq, getD_append_right _ _ _ (by omega), show P + u - P = u by omega,
            getD_append_left _ _ _ hu]
        rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hu] at h1
      have hgetR_end : (prefR (m + 1))[P + N]'(by omega) = oldRoots[m]'(by omega) := by
        have h1 : (prefR (m + 1)).getD (P + N) 0 = oldRoots[m]'(by omega) := by
          rw [hR_eq, getD_append_right _ _ _ (by omega), show P + N - P = N by omega,
            getD_append_right _ _ _ (le_refl N), Nat.sub_self]; rfl
        rwa [List.getD_eq_getElem _ _ (by omega)] at h1
      have hgetM_lt : ∀ t (ht : t < 2 * P), (prefM (m + 1)).getD t [] = (prefM m).getD t [] := by
        intro t ht
        rw [hM_eq, getD_append_left _ _ _ (by omega)]
      have hgetM_mid : ∀ t (ht : t < 2 * N + 1),
          (prefM (m + 1)).getD (2 * P + t) [] = (expM m).getD t [] := by
        intro t ht
        have hexp_l := hexp_len m (by omega)
        rw [hM_eq, getD_append_right _ _ _ (by omega), hlenM,
          show 2 * P + t - 2 * P = t by omega, getD_append_left _ _ _ (by omega)]
      have hgetM_end : (prefM (m + 1)).getD (2 * (P + N) + 1) [] = oldRow m := by
        have hexp_l := hexp_len m (by omega)
        rw [hM_eq, getD_append_right _ _ _ (by omega), hlenM,
          show 2 * (P + N) + 1 - 2 * P = 2 * N + 1 by omega,
          getD_append_right _ _ _ (by omega), hexp_l, Nat.sub_self]; rfl
      refine ⟨hsort', hlt_old', hlt_new', hlenM', hwM', hsound', ?_, ?_, hmem'⟩
      · intro j hj i hi
        by_cases hjP : j < P
        · rw [hgetM_lt (2 * j + 1) (by omega), hgetR_lt j hjP]
          exact hat_r j hjP i hi
        · by_cases hjPN : j < P + N
          · set u := j - P
            have hj_eq : j = P + u := by omega
            have hu : u < N := by omega
            have h2j : 2 * j + 1 = 2 * P + (2 * u + 1) := by omega
            rw [h2j, hgetM_mid (2 * u + 1) (by omega)]
            have hr_eq : (prefR (m + 1))[j]'hj = (newR m)[u]'hu := by
              have h1 : (prefR (m + 1))[j]'hj = (prefR (m + 1))[P + u]'(by omega) := by congr 1
              rw [h1]; exact hgetR_mid u hu
            rw [hr_eq]
            exact hexp_root m (by omega) u hu i hi
          · have hjeq : j = P + N := by omega
            have h2j : 2 * j + 1 = 2 * (P + N) + 1 := by omega
            rw [h2j, hgetM_end]
            have hr_eq : (prefR (m + 1))[j]'hj = oldRoots[m]'(by omega) := by
              have h1 : (prefR (m + 1))[j]'hj = (prefR (m + 1))[P + N]'(by omega) := by congr 1
              rw [h1]; exact hgetR_end
            rw [hr_eq]
            exact hold_root m (by omega) i hi
      · intro j hj x hxL hxR i hi
        by_cases hjP : j < P
        · rw [hgetM_lt (2 * j) (by omega)]
          apply hon_i j hjP x
          · intro hpos
            have := hxL hpos
            rwa [hgetR_lt (j - 1) (by omega)] at this
          · rwa [hgetR_lt j hjP] at hxR
        · set u := j - P
          have hj_eq : j = P + u := by omega
          have hu : u ≤ N := by omega
          have hx_inI : x ∈ OpenInt oldRoots m := by
            apply openInt_mk (by omega)
            · intro hm_pos
              obtain ⟨hPpos, hlast⟩ := hlast_pref hm_pos
              have hlt1 : (prefR (m + 1))[P - 1]'(by omega) ≤ (prefR (m + 1))[j - 1]'(by omega) := by
                rcases eq_or_lt_of_le (show P - 1 ≤ j - 1 by omega) with heq | hlt
                · simp [heq]
                · exact le_of_lt (pairwise_lt_getElem hsort' (by omega) (by omega) hlt)
              have hlt2 : (prefR (m + 1))[j - 1]'(by omega) < x := hxL (by omega)
              rw [hgetR_lt (P - 1) (by omega), hlast] at hlt1
              linarith
            · intro _
              have hle1 : (prefR (m + 1))[j]'hj ≤ (prefR (m + 1))[P + N]'(by omega) := by
                rcases eq_or_lt_of_le (show j ≤ P + N by omega) with heq | hlt
                · simp [heq]
                · exact le_of_lt (pairwise_lt_getElem hsort' hj (by omega) hlt)
              rw [hgetR_end] at hle1
              linarith
          have h2j : 2 * j = 2 * P + 2 * u := by omega
          rw [h2j, hgetM_mid (2 * u) (by omega)]
          apply hexp_int m (by omega) u hu x hx_inI
          · intro hu_pos
            have := hxL (by omega)
            have hidx : j - 1 = P + (u - 1) := by omega
            have hr_eq : (prefR (m + 1))[j - 1]'(by omega) = (newR m)[u - 1]'(by omega) := by
              have h1 : (prefR (m + 1))[j - 1]'(by omega) = (prefR (m + 1))[P + (u - 1)]'(by omega) := by
                congr 1
              rw [h1]; exact hgetR_mid (u - 1) (by omega)
            rwa [hr_eq] at this
          · intro hu_lt
            have hr_eq : (prefR (m + 1))[j]'hj = (newR m)[u]'hu_lt := by
              have h1 : (prefR (m + 1))[j]'hj = (prefR (m + 1))[P + u]'(by omega) := by congr 1
              rw [h1]; exact hgetR_mid u hu_lt
            rwa [hr_eq] at hxR
  -- Now append the final interval m = oldRoots.length!
  set M₀ := oldRoots.length
  obtain ⟨hsort, _, hlt_new, hlenM, hwM, hsound, hat_r, hon_i, hmem⟩ := hpref M₀ le_rfl
  set P := (prefR M₀).length
  set N := (newR M₀).length
  have hallR_eq : allR = prefR M₀ ++ newR M₀ := rfl
  have hallM_eq : allM = prefM M₀ ++ expM M₀ := rfl
  have hsort_all : allR.Pairwise (· < ·) := by
    rw [hallR_eq, List.pairwise_append]
    exact ⟨hsort, hnew_sorted M₀ le_rfl, hlt_new⟩
  have hrows_len : allM.length = 2 * allR.length + 1 := by
    rw [hallM_eq, hallR_eq, List.length_append, List.length_append, hlenM, hexp_len M₀ le_rfl]
    omega
  have hrow_w : ∀ row ∈ allM, row.length = L.length := by
    intro row hrow
    rw [hallM_eq] at hrow
    rcases List.mem_append.mp hrow with h1 | h2
    · exact hwM row h1
    · exact hexp_w M₀ le_rfl row h2
  have hcomp_all : ∀ p ∈ L, (∃ x, evalU p ρ x ≠ 0) → ∀ x, evalU p ρ x = 0 → x ∈ allR := by
    intro p hp hnz x hx
    rw [hallR_eq, List.mem_append, hmem]
    rcases hcomp p hp hnz x hx with hold | ⟨j, hj, hnew⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hold
      exact Or.inl ⟨j, hj, Or.inl rfl⟩
    · by_cases hjm : j < M₀
      · exact Or.inl ⟨j, hjm, Or.inr hnew⟩
      · have : j = M₀ := by omega
        subst this; exact Or.inr hnew
  have hsound_all : ∀ r ∈ allR, ∃ p ∈ L, (∃ x, evalU p ρ x ≠ 0) ∧ evalU p ρ r = 0 := by
    intro r hr
    rw [hallR_eq] at hr
    rcases List.mem_append.mp hr with h1 | h2
    · exact hsound r h1
    · exact hsound_new M₀ le_rfl r h2
  have hlast_M0 : ∀ (hpos : 0 < M₀), ∃ hne : 0 < P,
      (prefR M₀)[P - 1]'(by omega) = oldRoots[M₀ - 1]'(by omega) := by
    intro hpos
    have hm' : M₀ = (M₀ - 1) + 1 := by omega
    have hEq : prefR M₀ = prefR (M₀ - 1) ++ (newR (M₀ - 1) ++ [oldRoots[M₀ - 1]'(by omega)]) := by
      conv_lhs => rw [hm']
      simp only [prefR, List.range_succ, List.flatMap_append, List.flatMap_singleton]
      rw [List.getD_eq_getElem _ _ (by omega)]
    have hlen_pos : 0 < P := by dsimp only [P]; rw [hEq]; simp
    refine ⟨hlen_pos, ?_⟩
    have hidx : P - 1 = (prefR (M₀ - 1)).length + (newR (M₀ - 1)).length := by
      dsimp only [P]; rw [hEq]; simp
    have hge1 : (prefR (M₀ - 1)).length ≤ P - 1 := by omega
    have hcast : (prefR M₀)[P - 1]'(by omega) =
        (prefR (M₀ - 1) ++ (newR (M₀ - 1) ++ [oldRoots[M₀ - 1]'(by omega)]))[P - 1]'(by rw [← hEq]; omega) := by
      congr 1
    rw [hcast, List.getElem_append_right hge1]
    have hsub : P - 1 - (prefR (M₀ - 1)).length = (newR (M₀ - 1)).length := by omega
    simp [hsub]
  have hallR_get_lt : ∀ j (hj : j < P), allR[j]'(by rw [hallR_eq, List.length_append]; omega) = (prefR M₀)[j]'hj := by
    intro j hj
    have h1 : allR.getD j 0 = (prefR M₀).getD j 0 := by rw [hallR_eq, getD_append_left _ _ _ hj]
    rwa [List.getD_eq_getElem _ _ (by rw [hallR_eq, List.length_append]; omega),
      List.getD_eq_getElem _ _ hj] at h1
  have hallR_get_ge : ∀ j (hj : P ≤ j) (hj' : j < P + N),
      allR[j]'(by rw [hallR_eq, List.length_append]; omega) = (newR M₀)[j - P]'(by omega) := by
    intro j hj hj'
    have h1 : allR.getD j 0 = (newR M₀).getD (j - P) 0 := by
      rw [hallR_eq, getD_append_right _ _ _ hj]
    rwa [List.getD_eq_getElem _ _ (by rw [hallR_eq, List.length_append]; omega),
      List.getD_eq_getElem _ _ (by omega)] at h1
  refine ⟨hsort_all, hcomp_all, hsound_all, hrows_len, hrow_w, ?_, ?_⟩
  · intro j hj i hi
    have hj_len : allR.length = P + N := by rw [hallR_eq, List.length_append]
    by_cases hjP : j < P
    · have hgetM : allM.getD (2 * j + 1) [] = (prefM M₀).getD (2 * j + 1) [] := by
        rw [hallM_eq, getD_append_left _ _ _ (by omega)]
      rw [hgetM, hallR_get_lt j hjP]
      exact hat_r j hjP i hi
    · set u := j - P
      have hu : u < N := by omega
      have hgetM : allM.getD (2 * j + 1) [] = (expM M₀).getD (2 * u + 1) [] := by
        rw [hallM_eq, getD_append_right _ _ _ (by omega), hlenM,
          show 2 * j + 1 - 2 * P = 2 * u + 1 by omega]
      rw [hgetM, hallR_get_ge j (by omega) (by omega)]
      exact hexp_root M₀ le_rfl u hu i hi
  · intro j hj x hxL hxR i hi
    have hj_len : allR.length = P + N := by rw [hallR_eq, List.length_append]
    by_cases hjP : j < P
    · have hgetM : allM.getD (2 * j) [] = (prefM M₀).getD (2 * j) [] := by
        rw [hallM_eq, getD_append_left _ _ _ (by omega)]
      rw [hgetM]
      apply hon_i j hjP x
      · intro hpos
        have := hxL hpos
        rwa [hallR_get_lt (j - 1) (by omega)] at this
      · have := hxR (by omega)
        rwa [hallR_get_lt j hjP] at this
    · set u := j - P
      have hu : u ≤ N := by omega
      have hgetM : allM.getD (2 * j) [] = (expM M₀).getD (2 * u) [] := by
        rw [hallM_eq, getD_append_right _ _ _ (by omega), hlenM,
          show 2 * j - 2 * P = 2 * u by omega]
      rw [hgetM]
      have hx_inI : x ∈ OpenInt oldRoots M₀ := by
        apply openInt_mk le_rfl
        · intro hpos
          obtain ⟨hPpos, hlast⟩ := hlast_M0 hpos
          have hle1 : allR[P - 1]'(by omega) ≤ allR[j - 1]'(by omega) := by
            rcases eq_or_lt_of_le (show P - 1 ≤ j - 1 by omega) with heq | hlt
            · simp [heq]
            · exact le_of_lt (pairwise_lt_getElem hsort_all (by omega) (by omega) hlt)
          have hlt2 : allR[j - 1]'(by omega) < x := hxL (by omega)
          rw [hallR_get_lt (P - 1) (by omega), hlast] at hle1
          linarith
        · intro h; omega
      apply hexp_int M₀ le_rfl u hu x hx_inI
      · intro hpos
        have := hxL (by omega)
        rw [hallR_get_ge (j - 1) (by omega) (by omega)] at this
        have hsub : j - 1 - P = u - 1 := by omega
        have heq : (newR M₀)[j - 1 - P]'(by omega) = (newR M₀)[u - 1]'(by omega) := by congr 1
        rwa [heq] at this
      · intro hlt
        have := hxR (by omega)
        rwa [hallR_get_ge j (by omega) (by omega)] at this

lemma liftTable_spec {CL : List UPoly} {k : ℕ} {M : List (List ℕ)}
    {ρ : ℕ → ℝ} {roots : List ℝ}
    (hCL : IsClosed CL) (hk : 2 ≤ k)
    (hM : IsSignTable (ctxLprev ((CL, k), M)) ρ roots M) :
    ∃ roots' : List ℝ, IsSignTable (ctxLcurr ((CL, k), M)) ρ roots' (liftTable CL k M) := by
  set c : LiftCtx := ((CL, k), M)
  have hck : c.1.2 = k := rfl
  have hnr : ctxNumRoots c = roots.length := by
    unfold ctxNumRoots; rw [hM.rows_len]; omega
  refine ⟨(List.range roots.length).flatMap
      (fun j => newRootsInterval c ρ roots j ++ [roots.getD j 0]) ++
      newRootsInterval c ρ roots roots.length, ?_⟩
  unfold liftTable
  change IsSignTable (ctxLcurr c) ρ _
    ((List.range (ctxNumRoots c)).flatMap (fun j => expandInterval c j ++ [rootRowNew c j]) ++
      expandInterval c (ctxNumRoots c))
  rw [hnr]
  apply stitch_sign_table hM.roots_sorted
    (newR := newRootsInterval c ρ roots)
    (expM := expandInterval c)
    (oldRow := rootRowNew c)
  · intro j hj; exact (newRootsInterval_spec hCL hk hM hj).2.1
  · intro j hj; exact (newRootsInterval_spec hCL hk hM hj).2.2.1
  · intro j hj; exact (expandInterval_spec hCL hk hM hj).1
  · intro j hj; exact (expandInterval_spec hCL hk hM hj).2.1
  · intro j _; simp [rootRowNew]
  · intro j hj; exact (expandInterval_spec hCL hk hM hj).2.2.1
  · intro j hj; exact (expandInterval_spec hCL hk hM hj).2.2.2
  · intro j hj i hi
    simp only [rootRowNew]
    rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_map]
    exact signAtRoot_spec hCL hk hM hj (List.getElem_mem hi)
  · intro p hp hnz x hx
    by_cases hmem : x ∈ roots
    · exact Or.inl hmem
    · right
      set j := (roots.filter (fun r => decide (r < x))).length
      have hj : j ≤ roots.length := List.length_filter_le _ _
      have hfilt_prefix : ∀ (rs : List ℝ), rs.Pairwise (· < ·) → x ∉ rs →
          let m := (rs.filter (fun r => decide (r < x))).length
          (∀ i (hi : i < rs.length), i < m → rs[i]'hi < x) ∧
          (∀ i (hi : i < rs.length), m ≤ i → x < rs[i]'hi) := by
        intro rs hrs hxnot
        induction rs with
        | nil => exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
        | cons r ts ih =>
          have hts := (List.pairwise_cons.mp hrs).2
          have hrall := (List.pairwise_cons.mp hrs).1
          have hxts : x ∉ ts := fun h => hxnot (List.mem_cons_of_mem _ h)
          have hxr : r ≠ x := fun h => hxnot (h ▸ List.mem_cons_self ..)
          obtain ⟨ihL, ihR⟩ := ih hts hxts
          rcases lt_or_gt_of_ne hxr with hlt | hgt
          · have hm_eq : ((r :: ts).filter (fun w => decide (w < x))).length =
                (ts.filter (fun w => decide (w < x))).length + 1 := by
              simp [List.filter_cons, hlt]
            constructor
            · intro i hi him
              rw [hm_eq] at him
              cases i with
              | zero => exact hlt
              | succ i' => exact ihL i' (by simpa using hi) (by omega)
            · intro i hi him
              rw [hm_eq] at him
              cases i with
              | zero => omega
              | succ i' => exact ihR i' (by simpa using hi) (by omega)
          · have hm_eq : ((r :: ts).filter (fun w => decide (w < x))).length = 0 := by
              have hnone : ts.filter (fun w => decide (w < x)) = [] := by
                rw [List.filter_eq_nil_iff]
                intro w hw
                simp [not_lt.mpr (le_of_lt (lt_trans hgt (hrall w hw)))]
              simp [List.filter_cons, not_lt.mpr (le_of_lt hgt), hnone]
            constructor
            · intro i _ him; rw [hm_eq] at him; omega
            · intro i hi _
              cases i with
              | zero => exact hgt
              | succ i' => exact lt_trans hgt (hrall _ (List.getElem_mem (by simpa using hi)))
      obtain ⟨hL, hR⟩ := hfilt_prefix roots hM.roots_sorted hmem
      have hxI : x ∈ OpenInt roots j :=
        openInt_mk hj (fun h => hL (j - 1) (by omega) (by omega)) (fun h => hR j h le_rfl)
      refine ⟨j, hj, ?_⟩
      have hpCL : p ∈ CL := (List.mem_filter.mp hp).1
      have hple : p.length ≤ k := of_decide_eq_true (List.mem_filter.mp hp).2
      by_cases hplt : p.length < k
      · exfalso
        exact hmem (hM.roots_complete p
          (List.mem_filter.mpr ⟨hpCL, decide_eq_true (by rw [hck]; exact hplt)⟩) hnz x hx)
      · have hpeq : p.length = k := by omega
        by_cases hlc0 : evalM (lcU p) ρ = 0
        · exfalso
          have hred_prev : redU p ∈ ctxLprev c :=
            List.mem_filter.mpr ⟨hCL.mem_red p hpCL (by omega),
              decide_eq_true (by rw [length_redU, hck]; omega)⟩
          have heq := evalU_redU_of_lc_zero (u := p) (by omega) hlc0
          exact hmem (hM.roots_complete (redU p) hred_prev
            (by obtain ⟨y, hy⟩ := hnz; exact ⟨y, by rw [heq]; exact hy⟩)
            x (by rw [heq]; exact hx))
        · by_cases hopp : oppSign (sL c j p) (sR c j p) = true
          · have hp_act : p ∈ activeList c j := by
              rw [activeList, List.mem_filter]
              have hlc_prev : [lcU p] ∈ ctxLprev c :=
                List.mem_filter.mpr ⟨hCL.mem_lc p hpCL (by omega),
                  decide_eq_true (by simp [hck]; omega)⟩
              refine ⟨hp, ?_⟩
              unfold isActive
              simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, hck]
              refine ⟨⟨hpeq, ?_⟩, hopp⟩
              rw [lookupPrev_row0_const hM hlc_prev]
              intro h0; exact hlc0 ((realSign_eq_zero_iff _).mp h0)
            obtain ⟨u, hu, _, hαu⟩ := (newRootsInterval_spec hCL hk hM hj).2.2.2.2 p hp_act
            obtain ⟨_, _, hLp, hRp⟩ := activeRoot_spec hCL hk hM hj hp_act
            have hx_eq : x = activeRoot c ρ roots j p := by
              have hsL_c : sL ((CL, k), M) j p = sL c j p := rfl
              have hsR_c : sR ((CL, k), M) j p = sR c j p := rfl
              rcases lt_trichotomy x (activeRoot c ρ roots j p) with hlt | heq | hgt
              · have hs := hLp x hxI hlt
                rw [hx, (realSign_eq_zero_iff _).2 rfl, hsL_c] at hs
                rcases (oppSign_iff _ _).mp hopp with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
              · exact heq
              · have hs := hRp x hxI hgt
                rw [hx, (realSign_eq_zero_iff _).2 rfl, hsR_c] at hs
                rcases (oppSign_iff _ _).mp hopp with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
            rw [hx_eq, ← hαu]
            exact List.getElem_mem hu
          · exfalso
            have hnopp : oppSign (sL c j p) (sR c j p) = false := by
              cases h : oppSign (sL c j p) (sR c j p) <;> simp_all
            exact (nonactive_constant_sign hCL hk hM hj hp hpeq hlc0 hnopp x hxI).2 hx
  · intro r hr
    obtain ⟨p, hp_prev, hnz, hroot⟩ := hM.roots_sound r hr
    have hpCL : p ∈ CL := (List.mem_filter.mp hp_prev).1
    have hplt : p.length < k := of_decide_eq_true (List.mem_filter.mp hp_prev).2
    exact ⟨p, List.mem_filter.mpr ⟨hpCL, decide_eq_true (by rw [hck]; omega)⟩, hnz, hroot⟩
  · intro j hj r hr
    obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem hr
    obtain ⟨p, hp_act, _, hαp⟩ := (newRootsInterval_spec hCL hk hM hj).2.2.2.1 u hu
    obtain ⟨_, hroot, _, _⟩ := activeRoot_spec hCL hk hM hj hp_act
    have hp_curr : p ∈ ctxLcurr c := (List.mem_filter.mp hp_act).1
    have hact := (List.mem_filter.mp hp_act).2
    unfold isActive at hact
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, hck] at hact
    have hpCL : p ∈ CL := (List.mem_filter.mp hp_curr).1
    have hlc_prev : [lcU p] ∈ ctxLprev c :=
      List.mem_filter.mpr ⟨hCL.mem_lc p hpCL (by omega), decide_eq_true (by simp [hck]; omega)⟩
    have hlc : evalM (lcU p) ρ ≠ 0 := by
      intro h0; exact hact.1.2 (by rw [lookupPrev_row0_const hM hlc_prev, h0, realSign_eq_zero_iff])
    obtain ⟨B, hB⟩ := evalU_sign_atTop (u := p) (by omega) hlc
    refine ⟨p, hp_curr, ⟨B + 1, ?_⟩, hαp ▸ hroot⟩
    intro h0
    have hs := hB (B + 1) (by linarith)
    rw [h0, (realSign_eq_zero_iff _).2 rfl] at hs
    exact hlc ((realSign_eq_zero_iff _).mp hs.symm)

lemma buildSignTable_spec {CL : List UPoly} (hCL : IsClosed CL) (ρ : ℕ → ℝ) :
    let consts := CL.filter (fun u => decide (u.length ≤ 1))
    let σ := consts.map (fun u => realSign (evalM (u.getD 0 []) ρ))
    ∃ roots : List ℝ, IsSignTable CL ρ roots (buildSignTable CL σ) := by
  intro consts σ
  have hstep : ∀ n : ℕ,
      ∃ roots : List ℝ,
        IsSignTable (CL.filter (fun u => decide (u.length ≤ n + 1))) ρ roots
          (n.rec (motive := fun _ => List (List ℕ)) [σ] (fun m acc => liftTable CL (m + 2) acc)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨[], ⟨List.Pairwise.nil, ?_, fun _ h => (by cases h), rfl, ?_, fun _ h => (by cases h), ?_⟩⟩
      · intro p hp hnz x hx
        have hle : p.length ≤ 1 := of_decide_eq_true (List.mem_filter.mp hp).2
        obtain ⟨y, hy⟩ := hnz
        rw [evalU_eq_const hle ρ y, ← evalU_eq_const hle ρ x, hx] at hy
        exact absurd rfl hy
      · intro row hrow
        change row ∈ [σ] at hrow
        simp only [List.mem_singleton] at hrow
        subst hrow
        simp only [σ, consts, List.length_map]
      · intro j hj x _ _ i hi
        have hj0 : j = 0 := by simp at hj; omega
        subst hj0
        change ([σ].getD (2 * 0) []).getD i 0 = _
        simp only [Nat.mul_zero, List.getD_cons_zero]
        have hi' : i < consts.length := hi
        rw [List.getD_eq_getElem _ _ (by simp [σ, hi'])]
        simp only [σ, List.getElem_map]
        have hle : consts[i].length ≤ 1 :=
          of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hi')).2
        rw [evalU_eq_const hle ρ x]
    | succ n ih =>
      obtain ⟨roots, hM⟩ := ih
      have hprev_eq : ctxLprev ((CL, n + 2),
          n.rec (motive := fun _ => List (List ℕ)) [σ] (fun m acc => liftTable CL (m + 2) acc)) =
          CL.filter (fun u => decide (u.length ≤ n + 1)) := by
        unfold ctxLprev
        apply List.filter_congr
        intro u _
        simp only [decide_eq_decide]
        omega
      rw [← hprev_eq] at hM
      obtain ⟨roots', hM'⟩ := liftTable_spec hCL (by omega) hM
      exact ⟨roots', hM'⟩
  obtain ⟨roots, hM⟩ := hstep (maxLen CL - 1)
  have hfilt_all : CL.filter (fun u => decide (u.length ≤ (maxLen CL - 1) + 1)) = CL := by
    rw [List.filter_eq_self]
    intro u hu
    have hle := le_maxLen hu
    exact decide_eq_true (by omega)
  rw [hfilt_all] at hM
  exact ⟨roots, hM⟩

/- Section 3: DNF Operations, Quantifier Elimination, and Correctness -/

abbrev Lit := MPoly × ℕ
abbrev Clause := List Lit
abbrev DNF := List Clause

def evalLit (l : Lit) (ρ : ℕ → ℝ) : Prop := realSign (evalM l.1 ρ) = l.2
def evalClause (c : Clause) (ρ : ℕ → ℝ) : Prop := ∀ l ∈ c, evalLit l ρ
def evalDNF (d : DNF) (ρ : ℕ → ℝ) : Prop := ∃ c ∈ d, evalClause c ρ

def botDNF : DNF := []
def topDNF : DNF := [ [] ]
def eq0DNF (p : MPoly) : DNF := [ [(p, 0)] ]
def le0DNF (p : MPoly) : DNF := [ [(p, 0)], [(p, 2)] ]
def orDNF (d₁ d₂ : DNF) : DNF := d₁ ++ d₂
def andDNF (d₁ d₂ : DNF) : DNF := d₁.flatMap fun c₁ => d₂.map fun c₂ => c₁ ++ c₂

def notLit (l : Lit) : DNF :=
  if l.2 = 0 then [ [(l.1, 1)], [(l.1, 2)] ]
  else if l.2 = 1 then [ [(l.1, 0)], [(l.1, 2)] ]
  else if l.2 = 2 then [ [(l.1, 0)], [(l.1, 1)] ]
  else [ [] ]

def notClause (c : Clause) : DNF :=
  c.foldl (fun acc l => orDNF acc (notLit l)) []

def notDNF (d : DNF) : DNF :=
  d.foldl (fun acc c => andDNF acc (notClause c)) [ [] ]

def impDNF (d₁ d₂ : DNF) : DNF := orDNF (notDNF d₁) d₂

def allSigns (n : ℕ) : List (List ℕ) :=
  n.rec (motive := fun _ => List (List ℕ)) [ [] ]
    (fun _ acc => acc.flatMap fun s => [0 :: s, 1 :: s, 2 :: s])

def evalDNFRow (v : ℕ) (CL : List UPoly) (row : List ℕ) (d : DNF) : Bool :=
  d.any fun c => c.all fun l =>
    row.getD (CL.findIdx (fun w => decide (w = toUPoly v l.1))) 0 == l.2

def elimExists (v : ℕ) (d : DNF) : DNF :=
  let polys := d.flatten.map (fun l => toUPoly v l.1)
  let CL := closeUPolys polys
  let consts := (CL.filter (fun u => decide (u.length ≤ 1))).map (fun u => u.getD 0 [])
  let good := (allSigns consts.length).filter (fun σ =>
    (buildSignTable CL σ).any (fun row => evalDNFRow v CL row d))
  good.map (fun σ => (List.range consts.length).map (fun i => (consts.getD i [], σ.getD i 0)))

def elimForall (v : ℕ) (d : DNF) : DNF := notDNF (elimExists v (notDNF d))

def evalClosedDNF (d : DNF) : Bool :=
  d.any fun c => c.all fun l => evalZeroSign l.1 == l.2

/- Primrec proofs for DNF and QE (using opaque-domain style) -/

lemma primrec_eq0DNF : Primrec eq0DNF :=
  Primrec.list_cons.comp
    (Primrec.list_cons.comp (Primrec.pair Primrec.id (Primrec.const 0)) (Primrec.const []))
    (Primrec.const [])

lemma primrec_le0DNF : Primrec le0DNF :=
  Primrec.list_cons.comp
    (Primrec.list_cons.comp (Primrec.pair Primrec.id (Primrec.const 0)) (Primrec.const []))
    (Primrec.list_cons.comp
      (Primrec.list_cons.comp (Primrec.pair Primrec.id (Primrec.const 2)) (Primrec.const []))
      (Primrec.const []))

lemma primrec_orDNF : Primrec₂ orDNF := Primrec.list_append

lemma primrec_andDNF : Primrec₂ andDNF := by
  unfold andDNF
  have hinner : Primrec₂ fun (x : (DNF × DNF) × Clause) (c₂ : Clause) => x.2 ++ c₂ :=
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hmid : Primrec₂ fun (dd : DNF × DNF) (c₁ : Clause) => dd.2.map (fun c₂ => c₁ ++ c₂) :=
    (Primrec.list_map (Primrec.snd.comp Primrec.fst) hinner).to₂
  exact (Primrec.list_flatMap Primrec.fst hmid).to₂

lemma primrec_notLit : Primrec notLit := by
  unfold notLit
  have mkPair : ∀ s₁ s₂ : ℕ, Primrec fun l : Lit => [ [(l.1, s₁)], [(l.1, s₂)] ] := fun s₁ s₂ =>
    Primrec.list_cons.comp
      (Primrec.list_cons.comp (Primrec.pair Primrec.fst (Primrec.const s₁)) (Primrec.const []))
      (Primrec.list_cons.comp
        (Primrec.list_cons.comp (Primrec.pair Primrec.fst (Primrec.const s₂)) (Primrec.const []))
        (Primrec.const []))
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (mkPair 1 2)
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1)) (mkPair 0 2)
      (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 2)) (mkPair 0 1)
        (Primrec.const ([ [] ] : DNF))))

lemma primrec_notClause : Primrec notClause := by
  unfold notClause
  exact Primrec.list_foldl Primrec.id (Primrec.const [])
    (primrec_orDNF.comp (Primrec.fst.comp Primrec.snd)
      (primrec_notLit.comp (Primrec.snd.comp Primrec.snd))).to₂

lemma primrec_notDNF : Primrec notDNF := by
  unfold notDNF
  exact Primrec.list_foldl Primrec.id (Primrec.const ([ [] ] : DNF))
    (primrec_andDNF.comp (Primrec.fst.comp Primrec.snd)
      (primrec_notClause.comp (Primrec.snd.comp Primrec.snd))).to₂

lemma primrec_impDNF : Primrec₂ impDNF :=
  (primrec_orDNF.comp (primrec_notDNF.comp Primrec.fst) Primrec.snd).to₂

lemma primrec_allSigns : Primrec allSigns := by
  unfold allSigns
  have hcons : ∀ k : ℕ, Primrec fun s : List ℕ => k :: s := fun k =>
    Primrec.list_cons.comp (Primrec.const k) Primrec.id
  have h3 : Primrec₂ fun (_ : ℕ × (ℕ × List (List ℕ))) (s : List ℕ) => [0 :: s, 1 :: s, 2 :: s] :=
    (Primrec.list_cons.comp ((hcons 0).comp Primrec.snd)
      (Primrec.list_cons.comp ((hcons 1).comp Primrec.snd)
        (Primrec.list_cons.comp ((hcons 2).comp Primrec.snd) (Primrec.const [])))).to₂
  exact Primrec.nat_rec' Primrec.id (Primrec.const ([ [] ] : List (List ℕ)))
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) h3).to₂

lemma primrec_evalDNFRow_gen {α : Type*} [Primcodable α]
    {fv : α → ℕ} {fCL : α → List UPoly} {frow : α → List ℕ} {fd : α → DNF}
    (hfv : Primrec fv) (hfCL : Primrec fCL) (hfrow : Primrec frow) (hfd : Primrec fd) :
    Primrec fun a => evalDNFRow (fv a) (fCL a) (frow a) (fd a) := by
  unfold evalDNFRow
  have hlit : Primrec₂ fun (ac : α × Clause) (l : Lit) =>
      (frow ac.1).getD ((fCL ac.1).findIdx (fun w => decide (w = toUPoly (fv ac.1) l.1))) 0 == l.2 :=
    (Primrec.beq.comp
      ((Primrec.list_getD 0).comp (hfrow.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.list_findIdx (hfCL.comp (Primrec.fst.comp Primrec.fst))
          ((Primrec.eq.comp Primrec.snd
            (primrec_toUPoly.comp (hfv.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
              (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))).decide).to₂))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact primrec_list_any hfd (primrec_list_all Primrec.snd hlit).to₂

lemma primrec_elimExists_gen {α : Type*} [Primcodable α]
    {fv : α → ℕ} {fd : α → DNF} (hfv : Primrec fv) (hfd : Primrec fd) :
    Primrec fun a => elimExists (fv a) (fd a) := by
  unfold elimExists
  have hpolys : Primrec fun a => (fd a).flatten.map (fun l => toUPoly (fv a) l.1) :=
    Primrec.list_map (Primrec.list_flatten.comp hfd)
      (primrec_toUPoly.comp (hfv.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).to₂
  have hCL : Primrec fun a => closeUPolys ((fd a).flatten.map (fun l => toUPoly (fv a) l.1)) :=
    primrec_closeUPolys.comp hpolys
  have hconstsU : Primrec fun a =>
      (closeUPolys ((fd a).flatten.map (fun l => toUPoly (fv a) l.1))).filter
        (fun u => decide (u.length ≤ 1)) :=
    primrec_list_filter hCL
      ((Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 1)).decide).to₂
  have hconsts : Primrec fun a =>
      ((closeUPolys ((fd a).flatten.map (fun l => toUPoly (fv a) l.1))).filter
        (fun u => decide (u.length ≤ 1))).map (fun u => u.getD 0 []) :=
    Primrec.list_map hconstsU
      ((Primrec.list_getD ([] : MPoly)).comp Primrec.snd (Primrec.const 0)).to₂
  have htest : Primrec₂ fun a (σ : List ℕ) =>
      (buildSignTable (closeUPolys ((fd a).flatten.map (fun l => toUPoly (fv a) l.1))) σ).any
        (fun row => evalDNFRow (fv a)
          (closeUPolys ((fd a).flatten.map (fun l => toUPoly (fv a) l.1))) row (fd a)) :=
    (primrec_list_any (primrec_buildSignTable.comp (hCL.comp Primrec.fst) Primrec.snd)
      (primrec_evalDNFRow_gen (hfv.comp (Primrec.fst.comp Primrec.fst))
        (hCL.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
        (hfd.comp (Primrec.fst.comp Primrec.fst))).to₂).to₂
  have hgood : Primrec fun a =>
      (allSigns ((closeUPolys ((fd a).flatten.map (fun l => toUPoly (fv a) l.1))).filter
          (fun u => decide (u.length ≤ 1)) |>.map (fun u => u.getD 0 [])).length).filter
        (fun σ => (buildSignTable (closeUPolys ((fd a).flatten.map (fun l => toUPoly (fv a) l.1))) σ).any
          (fun row => evalDNFRow (fv a)
            (closeUPolys ((fd a).flatten.map (fun l => toUPoly (fv a) l.1))) row (fd a))) :=
    primrec_list_filter (primrec_allSigns.comp (Primrec.list_length.comp hconsts)) htest
  have hclause : Primrec₂ fun a (σ : List ℕ) =>
      (List.range ((closeUPolys ((fd a).flatten.map (fun l => toUPoly (fv a) l.1))).filter
          (fun u => decide (u.length ≤ 1)) |>.map (fun u => u.getD 0 [])).length).map
        (fun i => (((closeUPolys ((fd a).flatten.map (fun l => toUPoly (fv a) l.1))).filter
          (fun u => decide (u.length ≤ 1)) |>.map (fun u => u.getD 0 [])).getD i [], σ.getD i 0)) :=
    (Primrec.list_map
      (Primrec.list_range.comp (Primrec.list_length.comp (hconsts.comp Primrec.fst)))
      (Primrec.pair
        ((Primrec.list_getD ([] : MPoly)).comp (hconsts.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
        ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂).to₂
  exact Primrec.list_map hgood hclause

lemma primrec_elimForall_gen {α : Type*} [Primcodable α]
    {fv : α → ℕ} {fd : α → DNF} (hfv : Primrec fv) (hfd : Primrec fd) :
    Primrec fun a => elimForall (fv a) (fd a) :=
  primrec_notDNF.comp (primrec_elimExists_gen hfv (primrec_notDNF.comp hfd))

lemma primrec_evalClosedDNF : Primrec evalClosedDNF := by
  unfold evalClosedDNF
  exact primrec_list_any Primrec.id
    (primrec_list_all Primrec.snd
      (Primrec.beq.comp (primrec_evalZeroSign.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂).to₂

/- Semantics of DNF connectives and Quantifier Elimination -/

lemma evalDNF_bot (ρ : ℕ → ℝ) : evalDNF botDNF ρ ↔ False := by simp [evalDNF, botDNF]

lemma evalDNF_top (ρ : ℕ → ℝ) : evalDNF topDNF ρ ↔ True := by
  simp [evalDNF, topDNF, evalClause]

lemma evalDNF_eq0 (p : MPoly) (ρ : ℕ → ℝ) : evalDNF (eq0DNF p) ρ ↔ evalM p ρ = 0 := by
  simp [evalDNF, eq0DNF, evalClause, evalLit, realSign_eq_zero_iff]

lemma evalDNF_le0 (p : MPoly) (ρ : ℕ → ℝ) : evalDNF (le0DNF p) ρ ↔ evalM p ρ ≤ 0 := by
  simp only [evalDNF, le0DNF, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, evalClause, List.mem_singleton, forall_eq, evalLit, realSign_eq_zero_iff,
    realSign_eq_two_iff]
  constructor
  · rintro (h | h) <;> linarith
  · intro h; rcases eq_or_lt_of_le h with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr hlt

lemma evalDNF_or (d₁ d₂ : DNF) (ρ : ℕ → ℝ) :
    evalDNF (orDNF d₁ d₂) ρ ↔ evalDNF d₁ ρ ∨ evalDNF d₂ ρ := by
  simp only [evalDNF, orDNF, List.mem_append]
  constructor
  · rintro ⟨c, hc | hc, h⟩
    · exact Or.inl ⟨c, hc, h⟩
    · exact Or.inr ⟨c, hc, h⟩
  · rintro (⟨c, hc, h⟩ | ⟨c, hc, h⟩)
    · exact ⟨c, Or.inl hc, h⟩
    · exact ⟨c, Or.inr hc, h⟩

lemma evalDNF_and (d₁ d₂ : DNF) (ρ : ℕ → ℝ) :
    evalDNF (andDNF d₁ d₂) ρ ↔ evalDNF d₁ ρ ∧ evalDNF d₂ ρ := by
  simp only [evalDNF, andDNF, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨c, ⟨c₁, hc₁, c₂, hc₂, rfl⟩, hc⟩
    exact ⟨⟨c₁, hc₁, fun l hl => hc l (List.mem_append_left _ hl)⟩,
           ⟨c₂, hc₂, fun l hl => hc l (List.mem_append_right _ hl)⟩⟩
  · rintro ⟨⟨c₁, hc₁, h₁⟩, ⟨c₂, hc₂, h₂⟩⟩
    refine ⟨c₁ ++ c₂, ⟨c₁, hc₁, c₂, hc₂, rfl⟩, fun l hl => ?_⟩
    rcases List.mem_append.mp hl with h | h
    · exact h₁ l h
    · exact h₂ l h

lemma evalDNF_notLit (l : Lit) (ρ : ℕ → ℝ) : evalDNF (notLit l) ρ ↔ ¬ evalLit l ρ := by
  unfold notLit evalLit
  have hlt := realSign_lt_three (evalM l.1 ρ)
  by_cases h0 : l.2 = 0
  · rw [if_pos h0, h0]
    simp only [evalDNF, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, evalClause, List.mem_singleton, forall_eq, evalLit]
    omega
  · rw [if_neg h0]
    by_cases h1 : l.2 = 1
    · rw [if_pos h1, h1]
      simp only [evalDNF, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
        exists_eq_left, evalClause, List.mem_singleton, forall_eq, evalLit]
      omega
    · rw [if_neg h1]
      by_cases h2 : l.2 = 2
      · rw [if_pos h2, h2]
        simp only [evalDNF, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
          exists_eq_left, evalClause, List.mem_singleton, forall_eq, evalLit]
        omega
      · rw [if_neg h2]
        simp only [evalDNF, List.mem_singleton, exists_eq_left, evalClause, List.not_mem_nil,
          IsEmpty.forall_iff, implies_true, true_iff]
        omega

lemma evalDNF_notClause (c : Clause) (ρ : ℕ → ℝ) : evalDNF (notClause c) ρ ↔ ¬ evalClause c ρ := by
  unfold notClause
  have key : ∀ (l : Clause) (init : DNF),
      evalDNF (l.foldl (fun acc x => orDNF acc (notLit x)) init) ρ ↔
        evalDNF init ρ ∨ ¬ evalClause l ρ := by
    intro l
    induction l with
    | nil => intro init; simp [evalClause]
    | cons x xs ih =>
      intro init
      rw [List.foldl_cons, ih, evalDNF_or, evalDNF_notLit]
      simp only [evalClause, List.mem_cons, forall_eq_or_imp, not_and_or, or_assoc]
  simpa [evalDNF] using key c []

lemma evalDNF_not (d : DNF) (ρ : ℕ → ℝ) : evalDNF (notDNF d) ρ ↔ ¬ evalDNF d ρ := by
  unfold notDNF
  have key : ∀ (l : DNF) (init : DNF),
      evalDNF (l.foldl (fun acc c => andDNF acc (notClause c)) init) ρ ↔
        evalDNF init ρ ∧ ¬ evalDNF l ρ := by
    intro l
    induction l with
    | nil => intro init; simp [evalDNF]
    | cons c cs ih =>
      intro init
      rw [List.foldl_cons, ih, evalDNF_and, evalDNF_notClause]
      simp only [evalDNF, List.mem_cons, exists_eq_or_imp, not_or, and_assoc]
  simpa [evalDNF, evalClause] using key d [ [] ]

lemma evalDNF_imp (d₁ d₂ : DNF) (ρ : ℕ → ℝ) :
    evalDNF (impDNF d₁ d₂) ρ ↔ (evalDNF d₁ ρ → evalDNF d₂ ρ) := by
  rw [impDNF, evalDNF_or, evalDNF_not, imp_iff_not_or]

lemma mem_allSigns_iff (n : ℕ) (σ : List ℕ) :
    σ ∈ allSigns n ↔ σ.length = n ∧ ∀ s ∈ σ, s < 3 := by
  induction n generalizing σ with
  | zero =>
    change σ ∈ [ [] ] ↔ _
    simp only [List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨rfl, fun _ h => (by cases h)⟩
    · rintro ⟨h0, _⟩; exact List.length_eq_zero_iff.mp h0
  | succ n ih =>
    change σ ∈ (allSigns n).flatMap (fun s => [0 :: s, 1 :: s, 2 :: s]) ↔ _
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨s, hs, hσ⟩
      obtain ⟨hslen, hsbnd⟩ := (ih s).mp hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
      rcases hσ with rfl | rfl | rfl <;>
        refine ⟨by simp [hslen], fun a ha => ?_⟩ <;>
        rcases List.mem_cons.mp ha with rfl | ha' <;> first | omega | exact hsbnd a ha'
    · rintro ⟨hσlen, hσbnd⟩
      cases σ with
      | nil => simp at hσlen
      | cons a s =>
        have ha3 : a < 3 := hσbnd a (List.mem_cons_self ..)
        have hs : s ∈ allSigns n := (ih s).mpr ⟨by simpa using hσlen,
          fun b hb => hσbnd b (List.mem_cons_of_mem _ hb)⟩
        refine ⟨s, hs, ?_⟩
        have : a = 0 ∨ a = 1 ∨ a = 2 := by omega
        rcases this with rfl | rfl | rfl <;> simp

lemma evalDNF_elimExists (v : ℕ) (d : DNF) (ρ : ℕ → ℝ) :
    evalDNF (elimExists v d) ρ ↔ ∃ x : ℝ, evalDNF d (Function.update ρ v x) := by
  set polys := d.flatten.map (fun l => toUPoly v l.1)
  set CL := closeUPolys polys
  set constsU := CL.filter (fun u => decide (u.length ≤ 1))
  set consts := constsU.map (fun u => u.getD 0 [])
  set σ_ρ := constsU.map (fun u => realSign (evalM (u.getD 0 []) ρ))
  obtain ⟨hsubCL, _, hCL_closed, _⟩ := closeUPolys_spec v polys
  have hσ_len : σ_ρ.length = consts.length := by simp [σ_ρ, consts]
  have hσ_mem : σ_ρ ∈ allSigns consts.length := by
    rw [mem_allSigns_iff]
    refine ⟨hσ_len, fun s hs => ?_⟩
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hs
    exact realSign_lt_three _
  -- Step 1: A clause built from σ holds at ρ iff σ = σ_ρ
  have hclause_iff : ∀ σ ∈ allSigns consts.length,
      evalClause ((List.range consts.length).map (fun i => (consts.getD i [], σ.getD i 0))) ρ ↔
      σ = σ_ρ := by
    intro σ hσ
    obtain ⟨hσl, _⟩ := (mem_allSigns_iff _ _).mp hσ
    constructor
    · intro hcl
      apply List.ext_getElem (by omega)
      intro i hi1 hi2
      have hi : i < consts.length := by omega
      have hlit := hcl (consts.getD i [], σ.getD i 0)
        (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
      unfold evalLit at hlit
      have h1 : σ.getD i 0 = σ[i]'hi1 := List.getD_eq_getElem _ _ hi1
      have h2 : consts.getD i [] = (constsU[i]'(by simpa [consts] using hi)).getD 0 [] := by
        rw [List.getD_eq_getElem _ _ hi]; simp [consts]
      rw [h1, h2] at hlit
      simp only [σ_ρ, List.getElem_map]
      exact hlit.symm
    · rintro rfl l hl
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
      rw [List.mem_range] at hi
      unfold evalLit
      have h1 : σ_ρ.getD i 0 = realSign (evalM ((constsU[i]'(by simpa [consts] using hi)).getD 0 []) ρ) := by
        rw [List.getD_eq_getElem _ _ (by omega)]; simp [σ_ρ]
      have h2 : consts.getD i [] = (constsU[i]'(by simpa [consts] using hi)).getD 0 [] := by
        rw [List.getD_eq_getElem _ _ hi]; simp [consts]
      rw [h1, h2]
  -- Step 2: Simplify LHS to existence of a row in buildSignTable CL σ_ρ satisfying evalDNFRow
  have hlhs : evalDNF (elimExists v d) ρ ↔
      (buildSignTable CL σ_ρ).any (fun row => evalDNFRow v CL row d) = true := by
    unfold elimExists evalDNF
    change (∃ cl ∈ ((allSigns consts.length).filter (fun σ =>
        (buildSignTable CL σ).any (fun row => evalDNFRow v CL row d))).map
        (fun σ => (List.range consts.length).map (fun i => (consts.getD i [], σ.getD i 0))),
      evalClause cl ρ) ↔ _
    constructor
    · rintro ⟨cl, hcl_mem, hcl⟩
      obtain ⟨σ, hσ_filt, rfl⟩ := List.mem_map.mp hcl_mem
      obtain ⟨hσ_all, hσ_ok⟩ := List.mem_filter.mp hσ_filt
      have heq := (hclause_iff σ hσ_all).mp hcl
      rwa [heq] at hσ_ok
    · intro hok
      refine ⟨(List.range consts.length).map (fun i => (consts.getD i [], σ_ρ.getD i 0)),
        List.mem_map.mpr ⟨σ_ρ, List.mem_filter.mpr ⟨hσ_mem, hok⟩, rfl⟩,
        (hclause_iff σ_ρ hσ_mem).mpr rfl⟩
  rw [hlhs]
  -- Step 3: Use buildSignTable_spec to match rows with real points x : ℝ!
  obtain ⟨roots, hM⟩ := buildSignTable_spec hCL_closed ρ
  set M := buildSignTable CL σ_ρ
  have hrow_match : ∀ (row : List ℕ) (x : ℝ),
      (∀ (i : ℕ) (hi : i < CL.length), row.getD i 0 = realSign (evalU (CL[i]'hi) ρ x)) →
      (evalDNFRow v CL row d = true ↔ evalDNF d (Function.update ρ v x)) := by
    intro row x hrow
    unfold evalDNFRow evalDNF
    rw [List.any_eq_true]
    constructor
    · rintro ⟨c, hc, hall⟩
      rw [List.all_eq_true] at hall
      refine ⟨c, hc, fun l hl => ?_⟩
      have hu_in : toUPoly v l.1 ∈ CL :=
        hsubCL _ (List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨c, hc, hl⟩, rfl⟩)
      obtain ⟨hlt, heq⟩ := findIdx_eq_spec hu_in
      have hsat := beq_iff_eq.mp (hall l hl)
      rw [hrow _ hlt, heq, evalU_toUPoly] at hsat
      exact hsat
    · rintro ⟨c, hc, hcl⟩
      refine ⟨c, hc, ?_⟩
      rw [List.all_eq_true]
      intro l hl
      have hu_in : toUPoly v l.1 ∈ CL :=
        hsubCL _ (List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨c, hc, hl⟩, rfl⟩)
      obtain ⟨hlt, heq⟩ := findIdx_eq_spec hu_in
      rw [beq_iff_eq, hrow _ hlt, heq, evalU_toUPoly]
      exact hcl l hl
  rw [List.any_eq_true]
  constructor
  · rintro ⟨row, hrow_mem, hok⟩
    obtain ⟨rIdx, hrIdx, rfl⟩ := List.getElem_of_mem hrow_mem
    have hget : M[rIdx]'hrIdx = M.getD rIdx [] := (List.getD_eq_getElem _ _ hrIdx).symm
    rw [hget] at hok
    by_cases hev : rIdx % 2 = 0
    · set j := rIdx / 2
      have hrIdx_eq : rIdx = 2 * j := by omega
      have hj : j ≤ roots.length := by have := hM.rows_len; omega
      obtain ⟨x, hxL, hxR⟩ := exists_in_interval roots hM.roots_sorted j hj
      refine ⟨x, (hrow_match (M.getD rIdx []) x ?_).mp hok⟩
      rw [hrIdx_eq]
      exact hM.on_interval j hj x hxL hxR
    · set j := rIdx / 2
      have hrIdx_eq : rIdx = 2 * j + 1 := by omega
      have hj : j < roots.length := by have := hM.rows_len; omega
      refine ⟨roots[j]'hj, (hrow_match (M.getD rIdx []) (roots[j]'hj) ?_).mp hok⟩
      rw [hrIdx_eq]
      exact hM.at_root j hj
  · rintro ⟨x, hx⟩
    by_cases hmem : x ∈ roots
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
      have hrIdx : 2 * j + 1 < M.length := by rw [hM.rows_len]; omega
      refine ⟨M[2 * j + 1]'hrIdx, List.getElem_mem hrIdx, ?_⟩
      rw [← List.getD_eq_getElem _ [] hrIdx]
      exact (hrow_match _ _ (hM.at_root j hj)).mpr hx
    · set j := (roots.filter (fun r => decide (r < x))).length
      have hj : j ≤ roots.length := List.length_filter_le _ _
      have hfilt_prefix : ∀ (rs : List ℝ), rs.Pairwise (· < ·) → x ∉ rs →
          let m := (rs.filter (fun r => decide (r < x))).length
          (∀ i (hi : i < rs.length), i < m → rs[i]'hi < x) ∧
          (∀ i (hi : i < rs.length), m ≤ i → x < rs[i]'hi) := by
        intro rs hrs hxnot
        induction rs with
        | nil => exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
        | cons r ts ih =>
          have hts := (List.pairwise_cons.mp hrs).2
          have hrall := (List.pairwise_cons.mp hrs).1
          have hxts : x ∉ ts := fun h => hxnot (List.mem_cons_of_mem _ h)
          have hxr : r ≠ x := fun h => hxnot (h ▸ List.mem_cons_self ..)
          obtain ⟨ihL, ihR⟩ := ih hts hxts
          rcases lt_or_gt_of_ne hxr with hlt | hgt
          · have hm_eq : ((r :: ts).filter (fun w => decide (w < x))).length =
                (ts.filter (fun w => decide (w < x))).length + 1 := by simp [hlt]
            constructor
            · intro i hi him; rw [hm_eq] at him
              cases i with
              | zero => exact hlt
              | succ i' => exact ihL i' (by simpa using hi) (by omega)
            · intro i hi him; rw [hm_eq] at him
              cases i with
              | zero => omega
              | succ i' => exact ihR i' (by simpa using hi) (by omega)
          · have hm_eq : ((r :: ts).filter (fun w => decide (w < x))).length = 0 := by
              have hnone : ts.filter (fun w => decide (w < x)) = [] := by
                rw [List.filter_eq_nil_iff]
                intro w hw; simp [not_lt.mpr (le_of_lt (lt_trans hgt (hrall w hw)))]
              simp [not_lt.mpr (le_of_lt hgt), hnone]
            constructor
            · intro i _ him; rw [hm_eq] at him; omega
            · intro i hi _
              cases i with
              | zero => exact hgt
              | succ i' => exact lt_trans hgt (hrall _ (List.getElem_mem (by simpa using hi)))
      obtain ⟨hL, hR⟩ := hfilt_prefix roots hM.roots_sorted hmem
      have hrIdx : 2 * j < M.length := by rw [hM.rows_len]; omega
      refine ⟨M[2 * j]'hrIdx, List.getElem_mem hrIdx, ?_⟩
      rw [← List.getD_eq_getElem _ [] hrIdx]
      exact (hrow_match _ _ (hM.on_interval j hj x
        (fun h => hL (j - 1) (by omega) (by omega)) (fun h => hR j h le_rfl))).mpr hx

lemma evalDNF_elimForall (v : ℕ) (d : DNF) (ρ : ℕ → ℝ) :
    evalDNF (elimForall v d) ρ ↔ ∀ x : ℝ, evalDNF d (Function.update ρ v x) := by
  unfold elimForall
  rw [evalDNF_not, evalDNF_elimExists]
  simp only [evalDNF_not, not_exists, not_not]

lemma evalClosedDNF_iff (d : DNF) :
    evalClosedDNF d = true ↔ evalDNF d (fun _ => 0) := by
  unfold evalClosedDNF evalDNF
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, hc, hall⟩
    rw [List.all_eq_true] at hall
    refine ⟨c, hc, fun l hl => ?_⟩
    have h := beq_iff_eq.mp (hall l hl)
    rwa [evalZeroSign_eq] at h
  · rintro ⟨c, hc, hcl⟩
    refine ⟨c, hc, List.all_eq_true.mpr fun l hl => ?_⟩
    rw [beq_iff_eq, evalZeroSign_eq]
    exact hcl l hl

/- Section 4: Godel Decoder for `(Language.ring.sum Language.order).Sentence` -/

abbrev LRO : Language := Language.ring.sum Language.order

lemma encode_list_eq_map_encode {α : Type*} [Encodable α] (l : List α) :
    Encodable.encode l = Encodable.encode (l.map Encodable.encode) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    change Nat.pair (Encodable.encode a) (Encodable.encode t) + 1 =
      Nat.pair (Encodable.encode a) (Encodable.encode (t.map Encodable.encode)) + 1
    rw [ih]

def termStep (tok : ℕ) (stk : List MPoly) : List MPoly :=
  if tok % 2 = 0 then
    varM (tok / 4) :: stk
  else if tok = 1 then
    addM (stk.getD 0 []) (stk.getD 1 []) :: stk.tail.tail
  else if tok = 5 then
    mulM (stk.getD 0 []) (stk.getD 1 []) :: stk.tail.tail
  else if tok = 9 then
    negM (stk.getD 0 []) :: stk.tail
  else if tok = 13 then
    zeroM :: stk
  else if tok = 17 then
    oneM :: stk
  else []

def decodeTermToks (toks : List ℕ) : List MPoly :=
  toks.foldr termStep []

def decodeTermNat (n : ℕ) : MPoly :=
  (decodeTermToks ((Encodable.decode (α := List ℕ) n).getD [])).headD []

lemma primrec_termStep : Primrec₂ termStep := by
  unfold termStep
  have hs0 : Primrec fun x : ℕ × List MPoly => x.2.getD 0 [] :=
    (Primrec.list_getD ([] : MPoly)).comp Primrec.snd (Primrec.const 0)
  have hs1 : Primrec fun x : ℕ × List MPoly => x.2.getD 1 [] :=
    (Primrec.list_getD ([] : MPoly)).comp Primrec.snd (Primrec.const 1)
  have htl : Primrec fun x : ℕ × List MPoly => x.2.tail :=
    Primrec.list_tail.comp Primrec.snd
  have htl2 : Primrec fun x : ℕ × List MPoly => x.2.tail.tail :=
    Primrec.list_tail.comp htl
  exact (Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) (Primrec.const 0))
    (Primrec.list_cons.comp
      (primrec_varM.comp (Primrec.nat_div.comp Primrec.fst (Primrec.const 4))) Primrec.snd)
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
      (Primrec.list_cons.comp (primrec_addM.comp hs0 hs1) htl2)
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 5))
        (Primrec.list_cons.comp (primrec_mulM.comp hs0 hs1) htl2)
        (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 9))
          (Primrec.list_cons.comp (primrec_negM.comp hs0) htl)
          (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 13))
            (Primrec.list_cons.comp (Primrec.const zeroM) Primrec.snd)
            (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 17))
              (Primrec.list_cons.comp (Primrec.const oneM) Primrec.snd)
              (Primrec.const []))))))).to₂

lemma primrec_decodeTermToks : Primrec decodeTermToks :=
  Primrec.list_foldr Primrec.id (Primrec.const [])
    (primrec_termStep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

lemma primrec_decodeTermNat : Primrec decodeTermNat :=
  (primrec_list_headD ([] : MPoly)).comp
    (primrec_decodeTermToks.comp
      (Primrec.option_getD.comp (Primrec.decode (α := List ℕ)) (Primrec.const [])))

/- Formula suffix evaluator via Primrec.nat_strong_rec -/

def formulaStep (toks : List ℕ) (hist : List (List (ℕ × DNF))) : List (ℕ × DNF) :=
  let m := hist.length
  if m = 0 then []
  else
    let pos := toks.length - m
    let t0 := toks.getD pos 0
    let t1 := toks.getD (pos + 1) 0
    let t2 := toks.getD (pos + 2) 0
    let t3 := toks.getD (pos + 3) 0
    if t0 = 3 then
      let st := hist.getD (m - 1) []
      ((st.getD 0 (0, [])).1, impDNF (st.getD 0 (0, [])).2 (st.getD 1 (0, [])).2) :: st.tail.tail
    else if t0 = 7 then
      let st := hist.getD (m - 1) []
      let top := st.getD 0 (0, [])
      (top.1 - 1, elimForall (top.1 - 1) top.2) :: st.tail
    else if t0 = 5 then
      let st := hist.getD (m - 4) []
      let k := (t1 - 3) / 4
      let p0 := decodeTermNat (t2 / 2).unpair.2
      let p1 := decodeTermNat (t3 / 2).unpair.2
      (k, le0DNF (subM p0 p1)) :: st
    else if t0 % 2 = 0 then
      let st := hist.getD (m - 2) []
      let k := (t0 / 2).unpair.1
      let p0 := decodeTermNat (t0 / 2).unpair.2
      let p1 := decodeTermNat (t1 / 2).unpair.2
      (k, eq0DNF (subM p0 p1)) :: st
    else if t0 % 4 = 3 ∧ 11 ≤ t0 then
      let st := hist.getD (m - 1) []
      ((t0 - 11) / 4, botDNF) :: st
    else []

def evalFormulaSuffix (toks : List ℕ) (m : ℕ) : List (ℕ × DNF) :=
  let hist := m.rec (motive := fun _ => List (List (ℕ × DNF))) []
    (fun _ acc => acc ++ [formulaStep toks acc])
  formulaStep toks hist

def decideTarski (n : ℕ) : Bool :=
  let toks := (Encodable.decode (α := List ℕ) n).getD []
  let st := evalFormulaSuffix toks toks.length
  evalClosedDNF (st.getD 0 (0, [])).2

lemma primrec_formulaStep_gen {α : Type*} [Primcodable α]
    {ftoks : α → List ℕ} {fhist : α → List (List (ℕ × DNF))}
    (hftoks : Primrec ftoks) (hfhist : Primrec fhist) :
    Primrec fun a => formulaStep (ftoks a) (fhist a) := by
  unfold formulaStep
  have hm : Primrec fun a => (fhist a).length := Primrec.list_length.comp hfhist
  have hpos : Primrec fun a => (ftoks a).length - (fhist a).length :=
    Primrec.nat_sub.comp (Primrec.list_length.comp hftoks) hm
  have ht0 : Primrec fun a => (ftoks a).getD ((ftoks a).length - (fhist a).length) 0 :=
    (Primrec.list_getD 0).comp hftoks hpos
  have ht1 : Primrec fun a => (ftoks a).getD ((ftoks a).length - (fhist a).length + 1) 0 :=
    (Primrec.list_getD 0).comp hftoks (Primrec.nat_add.comp hpos (Primrec.const 1))
  have ht2 : Primrec fun a => (ftoks a).getD ((ftoks a).length - (fhist a).length + 2) 0 :=
    (Primrec.list_getD 0).comp hftoks (Primrec.nat_add.comp hpos (Primrec.const 2))
  have ht3 : Primrec fun a => (ftoks a).getD ((ftoks a).length - (fhist a).length + 3) 0 :=
    (Primrec.list_getD 0).comp hftoks (Primrec.nat_add.comp hpos (Primrec.const 3))
  have hst : ∀ d : ℕ, Primrec fun a => (fhist a).getD ((fhist a).length - d) [] := fun d =>
    (Primrec.list_getD ([] : List (ℕ × DNF))).comp hfhist (Primrec.nat_sub.comp hm (Primrec.const d))
  have hst1 := hst 1
  have hst2 := hst 2
  have hst4 := hst 4
  have htop0 : Primrec fun a => ((fhist a).getD ((fhist a).length - 1) []).getD 0 (0, []) :=
    (Primrec.list_getD (0, ([] : DNF))).comp hst1 (Primrec.const 0)
  have htop1 : Primrec fun a => ((fhist a).getD ((fhist a).length - 1) []).getD 1 (0, []) :=
    (Primrec.list_getD (0, ([] : DNF))).comp hst1 (Primrec.const 1)
  have hb_imp : Primrec fun a =>
      (((((fhist a).getD ((fhist a).length - 1) []).getD 0 (0, [])).1,
        impDNF (((fhist a).getD ((fhist a).length - 1) []).getD 0 (0, [])).2
          (((fhist a).getD ((fhist a).length - 1) []).getD 1 (0, [])).2) ::
        ((fhist a).getD ((fhist a).length - 1) []).tail.tail) :=
    Primrec.list_cons.comp
      (Primrec.pair (Primrec.fst.comp htop0)
        (primrec_impDNF.comp (Primrec.snd.comp htop0) (Primrec.snd.comp htop1)))
      (Primrec.list_tail.comp (Primrec.list_tail.comp hst1))
  have hb_all : Primrec fun a =>
      (((((fhist a).getD ((fhist a).length - 1) []).getD 0 (0, [])).1 - 1,
        elimForall ((((fhist a).getD ((fhist a).length - 1) []).getD 0 (0, [])).1 - 1)
          (((fhist a).getD ((fhist a).length - 1) []).getD 0 (0, [])).2) ::
        ((fhist a).getD ((fhist a).length - 1) []).tail) :=
    Primrec.list_cons.comp
      (Primrec.pair (Primrec.nat_sub.comp (Primrec.fst.comp htop0) (Primrec.const 1))
        (primrec_elimForall_gen
          (Primrec.nat_sub.comp (Primrec.fst.comp htop0) (Primrec.const 1))
          (Primrec.snd.comp htop0)))
      (Primrec.list_tail.comp hst1)
  have hdecTerm : ∀ (ft : α → ℕ), Primrec ft →
      Primrec fun a => decodeTermNat (ft a / 2).unpair.2 := fun ft hft =>
    primrec_decodeTermNat.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.nat_div.comp hft (Primrec.const 2))))
  have hb_rel : Primrec fun a =>
      ((((ftoks a).getD ((ftoks a).length - (fhist a).length + 1) 0 - 3) / 4,
        le0DNF (subM (decodeTermNat ((ftoks a).getD ((ftoks a).length - (fhist a).length + 2) 0 / 2).unpair.2)
          (decodeTermNat ((ftoks a).getD ((ftoks a).length - (fhist a).length + 3) 0 / 2).unpair.2))) ::
        (fhist a).getD ((fhist a).length - 4) []) :=
    Primrec.list_cons.comp
      (Primrec.pair
        (Primrec.nat_div.comp (Primrec.nat_sub.comp ht1 (Primrec.const 3)) (Primrec.const 4))
        (primrec_le0DNF.comp (primrec_subM.comp (hdecTerm _ ht2) (hdecTerm _ ht3))))
      hst4
  have hb_eq : Primrec fun a =>
      (((((ftoks a).getD ((ftoks a).length - (fhist a).length) 0 / 2).unpair.1,
        eq0DNF (subM (decodeTermNat ((ftoks a).getD ((ftoks a).length - (fhist a).length) 0 / 2).unpair.2)
          (decodeTermNat ((ftoks a).getD ((ftoks a).length - (fhist a).length + 1) 0 / 2).unpair.2)))) ::
        (fhist a).getD ((fhist a).length - 2) []) :=
    Primrec.list_cons.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.nat_div.comp ht0 (Primrec.const 2))))
        (primrec_eq0DNF.comp (primrec_subM.comp (hdecTerm _ ht0) (hdecTerm _ ht1))))
      hst2
  have hb_bot : Primrec fun a =>
      ((((ftoks a).getD ((ftoks a).length - (fhist a).length) 0 - 11) / 4, botDNF) ::
        (fhist a).getD ((fhist a).length - 1) []) :=
    Primrec.list_cons.comp
      (Primrec.pair
        (Primrec.nat_div.comp (Primrec.nat_sub.comp ht0 (Primrec.const 11)) (Primrec.const 4))
        (Primrec.const botDNF))
      hst1
  exact Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) (Primrec.const [])
    (Primrec.ite (Primrec.eq.comp ht0 (Primrec.const 3)) hb_imp
      (Primrec.ite (Primrec.eq.comp ht0 (Primrec.const 7)) hb_all
        (Primrec.ite (Primrec.eq.comp ht0 (Primrec.const 5)) hb_rel
          (Primrec.ite
            (Primrec.eq.comp (Primrec.nat_mod.comp ht0 (Primrec.const 2)) (Primrec.const 0)) hb_eq
            (Primrec.ite
              (PrimrecPred.and
                (Primrec.eq.comp (Primrec.nat_mod.comp ht0 (Primrec.const 4)) (Primrec.const 3))
                (Primrec.nat_le.comp (Primrec.const 11) ht0))
              hb_bot (Primrec.const []))))))

lemma primrec_evalFormulaSuffix : Primrec₂ evalFormulaSuffix := by
  unfold evalFormulaSuffix
  have hhist : Primrec fun x : List ℕ × ℕ =>
      x.2.rec (motive := fun _ => List (List (ℕ × DNF))) []
        (fun _ acc => acc ++ [formulaStep x.1 acc]) :=
    Primrec.nat_rec' Primrec.snd (Primrec.const [])
      (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp
          (primrec_formulaStep_gen (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
          (Primrec.const []))).to₂
  exact (primrec_formulaStep_gen Primrec.fst hhist).to₂

lemma primrec_decideTarski : Primrec decideTarski := by
  unfold decideTarski
  have htoks : Primrec fun n : ℕ => (Encodable.decode (α := List ℕ) n).getD [] :=
    Primrec.option_getD.comp (Primrec.decode (α := List ℕ)) (Primrec.const [])
  have hst : Primrec fun n : ℕ =>
      evalFormulaSuffix ((Encodable.decode (α := List ℕ) n).getD [])
        ((Encodable.decode (α := List ℕ) n).getD []).length :=
    primrec_evalFormulaSuffix.comp htoks (Primrec.list_length.comp htoks)
  exact primrec_evalClosedDNF.comp
    (Primrec.snd.comp ((Primrec.list_getD (0, ([] : DNF))).comp hst (Primrec.const 0)))

/- Semantics agreement of `decodeTermNat` and `evalFormulaSuffix` with Mathlib `Realize` -/

def extendFin {k : ℕ} (xs : Fin k → ℝ) (i : ℕ) : ℝ :=
  if h : i < k then xs ⟨i, h⟩ else 0

lemma extendFin_snoc {k : ℕ} (xs : Fin k → ℝ) (a : ℝ) :
    extendFin (Fin.snoc xs a) = Function.update (extendFin xs) k a := by
  funext i
  unfold extendFin
  by_cases hik : i = k
  · subst hik
    simp [Fin.snoc]
  · rw [Function.update_of_ne hik]
    by_cases hlt : i < k
    · have hlt1 : i < k + 1 := by omega
      rw [dif_pos hlt1, dif_pos hlt]
      simp [Fin.snoc, hlt]
    · have hlt1 : ¬ (i < k + 1) := by omega
      rw [dif_neg hlt1, dif_neg hlt]

lemma encode_ring_func_sum (n : ℕ) (f : LRO.Functions n) :
    (match n, f with
      | _, Sum.inl ringFunc.add => Encodable.encode (⟨2, Sum.inl ringFunc.add⟩ : Σ m, LRO.Functions m) = 0
      | _, Sum.inl ringFunc.mul => Encodable.encode (⟨2, Sum.inl ringFunc.mul⟩ : Σ m, LRO.Functions m) = 2
      | _, Sum.inl ringFunc.neg => Encodable.encode (⟨1, Sum.inl ringFunc.neg⟩ : Σ m, LRO.Functions m) = 4
      | _, Sum.inl ringFunc.zero => Encodable.encode (⟨0, Sum.inl ringFunc.zero⟩ : Σ m, LRO.Functions m) = 6
      | _, Sum.inl ringFunc.one => Encodable.encode (⟨0, Sum.inl ringFunc.one⟩ : Σ m, LRO.Functions m) = 8
      | _, Sum.inr e => Empty.elim e) := by
  rcases f with f | e
  · cases f <;> rfl
  · exact Empty.elim e

lemma decodeTermToks_append {k : ℕ} (t : LRO.Term (Empty ⊕ Fin k)) (rest : List ℕ) :
    ∃ p : MPoly,
      decodeTermToks (t.listEncode.map Encodable.encode ++ rest) = p :: decodeTermToks rest ∧
      ∀ (xs : Fin k → ℝ), evalM p (extendFin xs) = t.realize (Sum.elim Empty.elim xs) := by
  induction t generalizing rest with
  | var a =>
    rcases a with e | i
    · exact Empty.elim e
    · refine ⟨varM i.val, ?_, ?_⟩
      · have henc : Encodable.encode (Sum.inl (Sum.inr i) : (Empty ⊕ Fin k) ⊕ (Σ m, LRO.Functions m)) =
            4 * i.val + 2 := by
          rw [Encodable.encode_inl, Encodable.encode_inr]
          have hfin : Encodable.encode i = i.val := rfl
          rw [hfin]; omega
        simp only [Language.Term.listEncode, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, decodeTermToks, List.foldr_cons, henc, termStep]
        have hmod : (4 * i.val + 2) % 2 = 0 := by omega
        have hdiv : (4 * i.val + 2) / 4 = i.val := by omega
        rw [if_pos hmod, hdiv]
      · intro xs
        simp [extendFin, i.isLt, Language.Term.realize]
  | @func n f ts ih =>
    have hfr2 : List.finRange 2 = [0, 1] := rfl
    have hfr1 : List.finRange 1 = [0] := rfl
    have hfr0 : List.finRange 0 = [] := rfl
    rcases f with f | e
    · cases f with
      | add =>
        have htok : Encodable.encode (Sum.inr ⟨2, Sum.inl ringFunc.add⟩ :
            (Empty ⊕ Fin k) ⊕ (Σ m, LRO.Functions m)) = 1 := rfl
        have hlist : (Language.Term.func (Sum.inl ringFunc.add : LRO.Functions 2) ts).listEncode.map
              Encodable.encode ++ rest =
            1 :: ((ts 0).listEncode.map Encodable.encode ++
              ((ts 1).listEncode.map Encodable.encode ++ rest)) := by
          simp only [Language.Term.listEncode, hfr2, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.map_cons, List.map_append, List.cons_append, List.append_assoc, htok]
        obtain ⟨p₁, hp₁, hev₁⟩ := ih 1 rest
        obtain ⟨p₀, hp₀, hev₀⟩ := ih 0 ((ts 1).listEncode.map Encodable.encode ++ rest)
        refine ⟨addM p₀ p₁, ?_, ?_⟩
        · change decodeTermToks ((Language.Term.func (Sum.inl ringFunc.add : LRO.Functions 2) ts).listEncode.map
            Encodable.encode ++ rest) = _
          rw [hlist, decodeTermToks, List.foldr_cons]
          change termStep 1 (decodeTermToks _) = _
          rw [hp₀, hp₁]
          simp [termStep]
        · intro xs
          rw [evalM_add, hev₀, hev₁]
          rfl
      | mul =>
        have htok : Encodable.encode (Sum.inr ⟨2, Sum.inl ringFunc.mul⟩ :
            (Empty ⊕ Fin k) ⊕ (Σ m, LRO.Functions m)) = 5 := rfl
        have hlist : (Language.Term.func (Sum.inl ringFunc.mul : LRO.Functions 2) ts).listEncode.map
              Encodable.encode ++ rest =
            5 :: ((ts 0).listEncode.map Encodable.encode ++
              ((ts 1).listEncode.map Encodable.encode ++ rest)) := by
          simp only [Language.Term.listEncode, hfr2, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.map_cons, List.map_append, List.cons_append, List.append_assoc, htok]
        obtain ⟨p₁, hp₁, hev₁⟩ := ih 1 rest
        obtain ⟨p₀, hp₀, hev₀⟩ := ih 0 ((ts 1).listEncode.map Encodable.encode ++ rest)
        refine ⟨mulM p₀ p₁, ?_, ?_⟩
        · change decodeTermToks ((Language.Term.func (Sum.inl ringFunc.mul : LRO.Functions 2) ts).listEncode.map
            Encodable.encode ++ rest) = _
          rw [hlist, decodeTermToks, List.foldr_cons]
          change termStep 5 (decodeTermToks _) = _
          rw [hp₀, hp₁]
          simp [termStep]
        · intro xs
          rw [evalM_mul, hev₀, hev₁]
          rfl
      | neg =>
        have htok : Encodable.encode (Sum.inr ⟨1, Sum.inl ringFunc.neg⟩ :
            (Empty ⊕ Fin k) ⊕ (Σ m, LRO.Functions m)) = 9 := rfl
        have hlist : (Language.Term.func (Sum.inl ringFunc.neg : LRO.Functions 1) ts).listEncode.map
              Encodable.encode ++ rest =
            9 :: ((ts 0).listEncode.map Encodable.encode ++ rest) := by
          simp only [Language.Term.listEncode, hfr1, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.map_cons, List.cons_append, htok]
        obtain ⟨p₀, hp₀, hev₀⟩ := ih 0 rest
        refine ⟨negM p₀, ?_, ?_⟩
        · change decodeTermToks ((Language.Term.func (Sum.inl ringFunc.neg : LRO.Functions 1) ts).listEncode.map
            Encodable.encode ++ rest) = _
          rw [hlist, decodeTermToks, List.foldr_cons]
          change termStep 9 (decodeTermToks _) = _
          rw [hp₀]
          simp [termStep]
        · intro xs
          rw [evalM_neg, hev₀]
          rfl
      | zero =>
        have htok : Encodable.encode (Sum.inr ⟨0, Sum.inl ringFunc.zero⟩ :
            (Empty ⊕ Fin k) ⊕ (Σ m, LRO.Functions m)) = 13 := rfl
        have hlist : (Language.Term.func (Sum.inl ringFunc.zero : LRO.Functions 0) ts).listEncode.map
              Encodable.encode ++ rest =
            13 :: rest := by
          simp only [Language.Term.listEncode, hfr0, List.flatMap_nil, List.map_cons, List.map_nil,
            List.cons_append, List.nil_append, htok]
        refine ⟨zeroM, ?_, ?_⟩
        · change decodeTermToks ((Language.Term.func (Sum.inl ringFunc.zero : LRO.Functions 0) ts).listEncode.map
            Encodable.encode ++ rest) = _
          rw [hlist, decodeTermToks, List.foldr_cons]
          simp [termStep, decodeTermToks]
        · intro xs
          rw [evalM_zero]
          rfl
      | one =>
        have htok : Encodable.encode (Sum.inr ⟨0, Sum.inl ringFunc.one⟩ :
            (Empty ⊕ Fin k) ⊕ (Σ m, LRO.Functions m)) = 17 := rfl
        have hlist : (Language.Term.func (Sum.inl ringFunc.one : LRO.Functions 0) ts).listEncode.map
              Encodable.encode ++ rest =
            17 :: rest := by
          simp only [Language.Term.listEncode, hfr0, List.flatMap_nil, List.map_cons, List.map_nil,
            List.cons_append, List.nil_append, htok]
        refine ⟨oneM, ?_, ?_⟩
        · change decodeTermToks ((Language.Term.func (Sum.inl ringFunc.one : LRO.Functions 0) ts).listEncode.map
            Encodable.encode ++ rest) = _
          rw [hlist, decodeTermToks, List.foldr_cons]
          simp [termStep, decodeTermToks]
        · intro xs
          rw [evalM_one]
          rfl
    · exact Empty.elim e

lemma decodeTermNat_spec {k : ℕ} (t : LRO.Term (Empty ⊕ Fin k)) (xs : Fin k → ℝ) :
    evalM (decodeTermNat (Encodable.encode t)) (extendFin xs) =
      t.realize (Sum.elim Empty.elim xs) := by
  unfold decodeTermNat
  have henc : Encodable.encode t = Encodable.encode (t.listEncode.map Encodable.encode) :=
    encode_list_eq_map_encode t.listEncode
  rw [henc, Encodable.encodek]
  simp only [Option.getD_some]
  obtain ⟨p, hp, hev⟩ := decodeTermToks_append t []
  rw [List.append_nil] at hp
  rw [hp, List.headD_cons]
  exact hev xs

lemma evalFormulaSuffix_hist (toks : List ℕ) (m : ℕ) :
    m.rec (motive := fun _ => List (List (ℕ × DNF))) []
      (fun _ acc => acc ++ [formulaStep toks acc]) =
    (List.range m).map (evalFormulaSuffix toks) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_singleton]
    change (m.rec (motive := fun _ => List (List (ℕ × DNF))) []
      (fun _ acc => acc ++ [formulaStep toks acc])) ++
      [formulaStep toks (m.rec (motive := fun _ => List (List (ℕ × DNF))) []
        (fun _ acc => acc ++ [formulaStep toks acc]))] = _
    rw [← ih]; rfl

lemma evalFormulaSuffix_unfold (toks : List ℕ) (m : ℕ) :
    evalFormulaSuffix toks m = formulaStep toks ((List.range m).map (evalFormulaSuffix toks)) := by
  conv_lhs => unfold evalFormulaSuffix
  rw [evalFormulaSuffix_hist]

lemma evalFormulaSuffix_eq_of_suffix (toks₁ toks₂ : List ℕ) (m : ℕ)
    (hm₁ : m ≤ toks₁.length) (hm₂ : m ≤ toks₂.length)
    (hsuf : toks₁.drop (toks₁.length - m) = toks₂.drop (toks₂.length - m)) :
    evalFormulaSuffix toks₁ m = evalFormulaSuffix toks₂ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [evalFormulaSuffix_unfold toks₁ m, evalFormulaSuffix_unfold toks₂ m]
    unfold formulaStep
    simp only [List.length_map, List.length_range]
    by_cases hm0 : m = 0
    · simp [hm0]
    · rw [if_neg hm0, if_neg hm0]
      have hget : ∀ off : ℕ, toks₁.getD (toks₁.length - m + off) 0 = toks₂.getD (toks₂.length - m + off) 0 := by
        intro off
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          ← List.getElem?_drop, ← List.getElem?_drop, hsuf]
      have ht0 : toks₁.getD (toks₁.length - m) 0 = toks₂.getD (toks₂.length - m) 0 := by
        simpa using hget 0
      have ht1 := hget 1
      have ht2 := hget 2
      have ht3 := hget 3
      have hrec : ∀ d : ℕ, 1 ≤ d →
          ((List.range m).map (evalFormulaSuffix toks₁)).getD (m - d) [] =
          ((List.range m).map (evalFormulaSuffix toks₂)).getD (m - d) [] := by
        intro d hd
        have hlt : m - d < m := by omega
        rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt])]
        simp only [List.getElem_map, List.getElem_range]
        apply ih (m - d) hlt (by omega) (by omega)
        have h1 : toks₁.drop (toks₁.length - (m - d)) = (toks₁.drop (toks₁.length - m)).drop (m - (m - d)) := by
          rw [List.drop_drop]; congr 1; omega
        have h2 : toks₂.drop (toks₂.length - (m - d)) = (toks₂.drop (toks₂.length - m)).drop (m - (m - d)) := by
          rw [List.drop_drop]; congr 1; omega
        rw [h1, h2, hsuf]
      have hr1 := hrec 1 le_rfl
      have hr2 := hrec 2 (by omega)
      have hr4 := hrec 4 (by omega)
      simp only [ht0, ht1, ht2, ht3, hr1, hr2, hr4]

lemma evalFormulaSuffix_full_cons (a : ℕ) (l : List ℕ) :
    evalFormulaSuffix (a :: l) (a :: l).length =
      formulaStep (a :: l) ((List.range (l.length + 1)).map (evalFormulaSuffix (a :: l))) :=
  evalFormulaSuffix_unfold (a :: l) (l.length + 1)

lemma evalFormulaSuffix_tail_eq (pre l : List ℕ) :
    evalFormulaSuffix (pre ++ l) l.length = evalFormulaSuffix l l.length := by
  apply evalFormulaSuffix_eq_of_suffix (pre ++ l) l l.length (by simp) le_rfl
  rw [List.length_append, Nat.add_sub_cancel, Nat.sub_self, List.drop_zero, List.drop_left]

lemma evalFormulaSuffix_spec {k : ℕ} (φ : LRO.BoundedFormula Empty k) (rest : List ℕ) :
    ∃ d : DNF,
      evalFormulaSuffix (φ.listEncode.map Encodable.encode ++ rest)
        (φ.listEncode.map Encodable.encode ++ rest).length =
      (k, d) :: evalFormulaSuffix rest rest.length ∧
      ∀ (xs : Fin k → ℝ), evalDNF d (extendFin xs) ↔ φ.Realize Empty.elim xs := by
  induction φ generalizing rest with
  | @falsum k =>
    set tok := Encodable.encode (Sum.inr (Sum.inr (k + 2)) :
      (Σ m, LRO.Term (Empty ⊕ Fin m)) ⊕ ((Σ m, LRO.Relations m) ⊕ ℕ))
    have htok : tok = 4 * k + 11 := by
      unfold tok
      rw [Encodable.encode_inr, Encodable.encode_inr]
      change 2 * (2 * (k + 2) + 1) + 1 = 4 * k + 11
      omega
    refine ⟨botDNF, ?_, ?_⟩
    · have hlist : (Language.BoundedFormula.falsum (L := LRO) (n := k) (α := Empty)).listEncode.map
            Encodable.encode ++ rest =
          (4 * k + 11) :: rest := by
        simp only [Language.BoundedFormula.listEncode, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, ← htok, tok]
      rw [hlist, evalFormulaSuffix_unfold]
      unfold formulaStep
      simp only [List.length_map, List.length_range, List.length_cons, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, ↓reduceIte, Nat.sub_self, List.getD_cons_zero]
      have hne3 : 4 * k + 11 ≠ 3 := by omega
      have hne7 : 4 * k + 11 ≠ 7 := by omega
      have hne5 : 4 * k + 11 ≠ 5 := by omega
      have hmod2 : (4 * k + 11) % 2 ≠ 0 := by omega
      have hmod4 : (4 * k + 11) % 4 = 3 ∧ 11 ≤ 4 * k + 11 := by omega
      rw [if_neg hne3, if_neg hne7, if_neg hne5, if_neg hmod2, if_pos hmod4]
      have hget : ((List.range (rest.length + 1)).map (evalFormulaSuffix ((4 * k + 11) :: rest))).getD
          (rest.length + 1 - 1) [] = evalFormulaSuffix rest rest.length := by
        rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
        simpa using evalFormulaSuffix_tail_eq [4 * k + 11] rest
      rw [hget]
      have hdiv : (4 * k + 11 - 11) / 4 = k := by omega
      rw [hdiv]
    · intro xs
      rw [evalDNF_bot]
      simp [Language.BoundedFormula.Realize]
  | @equal k t₁ t₂ =>
    set tok₁ := Encodable.encode (Sum.inl ⟨k, t₁⟩ :
      (Σ m, LRO.Term (Empty ⊕ Fin m)) ⊕ ((Σ m, LRO.Relations m) ⊕ ℕ))
    set tok₂ := Encodable.encode (Sum.inl ⟨k, t₂⟩ :
      (Σ m, LRO.Term (Empty ⊕ Fin m)) ⊕ ((Σ m, LRO.Relations m) ⊕ ℕ))
    have htok₁ : tok₁ = 2 * Nat.pair k (Encodable.encode t₁) := by
      unfold tok₁; rw [Encodable.encode_inl, Encodable.encode_sigma_val]; rfl
    have htok₂ : tok₂ = 2 * Nat.pair k (Encodable.encode t₂) := by
      unfold tok₂; rw [Encodable.encode_inl, Encodable.encode_sigma_val]; rfl
    refine ⟨eq0DNF (subM (decodeTermNat (Encodable.encode t₁)) (decodeTermNat (Encodable.encode t₂))), ?_, ?_⟩
    · have hlist : (Language.BoundedFormula.equal t₁ t₂).listEncode.map Encodable.encode ++ rest =
          tok₁ :: tok₂ :: rest := by
        simp [Language.BoundedFormula.listEncode, tok₁, tok₂]
      rw [hlist, evalFormulaSuffix_unfold]
      unfold formulaStep
      simp only [List.length_map, List.length_range, List.length_cons, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, ↓reduceIte, Nat.sub_self, List.getD_cons_zero, zero_add,
        List.getD_cons_succ]
      have hne3 : tok₁ ≠ 3 := by rw [htok₁]; omega
      have hne7 : tok₁ ≠ 7 := by rw [htok₁]; omega
      have hne5 : tok₁ ≠ 5 := by rw [htok₁]; omega
      have hmod2 : tok₁ % 2 = 0 := by rw [htok₁]; omega
      rw [if_neg hne3, if_neg hne7, if_neg hne5, if_pos hmod2]
      have hu1 : (tok₁ / 2).unpair = (k, Encodable.encode t₁) := by
        rw [htok₁, Nat.mul_div_cancel_left _ (by omega), Nat.unpair_pair]
      have hu2 : (tok₂ / 2).unpair = (k, Encodable.encode t₂) := by
        rw [htok₂, Nat.mul_div_cancel_left _ (by omega), Nat.unpair_pair]
      have hget : ((List.range (rest.length + 1 + 1)).map (evalFormulaSuffix (tok₁ :: tok₂ :: rest))).getD
          (rest.length + 1 + 1 - 2) [] = evalFormulaSuffix rest rest.length := by
        have hsub : rest.length + 1 + 1 - 2 = rest.length := by omega
        rw [hsub, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
        simpa using evalFormulaSuffix_tail_eq [tok₁, tok₂] rest
      rw [hu1, hu2, hget]
    · intro xs
      rw [evalDNF_eq0, evalM_sub, decodeTermNat_spec, decodeTermNat_spec, sub_eq_zero]
      simp [Language.BoundedFormula.Realize]
  | @rel k l R ts =>
    rcases R with e | R'
    · exact Empty.elim e
    · cases R' with
      | le =>
        set tokR := Encodable.encode (Sum.inr (Sum.inl ⟨2, Sum.inr Language.orderRel.le⟩) :
          (Σ m, LRO.Term (Empty ⊕ Fin m)) ⊕ ((Σ m, LRO.Relations m) ⊕ ℕ))
        set tokK := Encodable.encode (Sum.inr (Sum.inr k) :
          (Σ m, LRO.Term (Empty ⊕ Fin m)) ⊕ ((Σ m, LRO.Relations m) ⊕ ℕ))
        set tok0 := Encodable.encode (Sum.inl ⟨k, ts 0⟩ :
          (Σ m, LRO.Term (Empty ⊕ Fin m)) ⊕ ((Σ m, LRO.Relations m) ⊕ ℕ))
        set tok1 := Encodable.encode (Sum.inl ⟨k, ts 1⟩ :
          (Σ m, LRO.Term (Empty ⊕ Fin m)) ⊕ ((Σ m, LRO.Relations m) ⊕ ℕ))
        have htokR : tokR = 5 := rfl
        have htokK : tokK = 4 * k + 3 := by
          unfold tokK; rw [Encodable.encode_inr, Encodable.encode_inr]
          change 2 * (2 * k + 1) + 1 = 4 * k + 3; omega
        have htok0 : tok0 = 2 * Nat.pair k (Encodable.encode (ts 0)) := by
          unfold tok0; rw [Encodable.encode_inl, Encodable.encode_sigma_val]; rfl
        have htok1 : tok1 = 2 * Nat.pair k (Encodable.encode (ts 1)) := by
          unfold tok1; rw [Encodable.encode_inl, Encodable.encode_sigma_val]; rfl
        refine ⟨le0DNF (subM (decodeTermNat (Encodable.encode (ts 0)))
          (decodeTermNat (Encodable.encode (ts 1)))), ?_, ?_⟩
        · have hfr2 : List.finRange 2 = [0, 1] := rfl
          have hlist : (Language.BoundedFormula.rel (Sum.inr Language.orderRel.le : LRO.Relations 2) ts).listEncode.map
              Encodable.encode ++ rest = 5 :: tokK :: tok0 :: tok1 :: rest := by
            simp only [Language.BoundedFormula.listEncode, hfr2, List.map_cons, List.map_nil,
              List.cons_append, List.nil_append, List.map_append, ← htokR, tokR, tokK, tok0, tok1]
          change evalFormulaSuffix
              ((Language.BoundedFormula.rel (Sum.inr Language.orderRel.le : LRO.Relations 2) ts).listEncode.map
                Encodable.encode ++ rest)
              ((Language.BoundedFormula.rel (Sum.inr Language.orderRel.le : LRO.Relations 2) ts).listEncode.map
                Encodable.encode ++ rest).length = _
          rw [hlist, evalFormulaSuffix_unfold]
          unfold formulaStep
          simp only [List.length_map, List.length_range, List.length_cons, Nat.add_eq_zero_iff,
            one_ne_zero, and_false, ↓reduceIte, Nat.sub_self, List.getD_cons_zero, zero_add,
            List.getD_cons_succ]
          have hu0 : (tok0 / 2).unpair = (k, Encodable.encode (ts 0)) := by
            rw [htok0, Nat.mul_div_cancel_left _ (by omega), Nat.unpair_pair]
          have hu1 : (tok1 / 2).unpair = (k, Encodable.encode (ts 1)) := by
            rw [htok1, Nat.mul_div_cancel_left _ (by omega), Nat.unpair_pair]
          have hkdiv : (tokK - 3) / 4 = k := by rw [htokK]; omega
          have hget : ((List.range (rest.length + 1 + 1 + 1 + 1)).map
              (evalFormulaSuffix (5 :: tokK :: tok0 :: tok1 :: rest))).getD
              (rest.length + 1 + 1 + 1 + 1 - 4) [] = evalFormulaSuffix rest rest.length := by
            have hsub : rest.length + 1 + 1 + 1 + 1 - 4 = rest.length := by omega
            rw [hsub, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
            simpa using evalFormulaSuffix_tail_eq [5, tokK, tok0, tok1] rest
          simp only [show (5 : ℕ) ≠ 3 by decide, show (5 : ℕ) ≠ 7 by decide, ↓reduceIte]
          rw [hkdiv, hu0, hu1, hget]
        · intro xs
          rw [evalDNF_le0, evalM_sub, decodeTermNat_spec, decodeTermNat_spec, sub_nonpos]
          rfl
  | @imp k φ₁ φ₂ ih₁ ih₂ =>
    obtain ⟨d₂, hd₂, hev₂⟩ := ih₂ rest
    obtain ⟨d₁, hd₁, hev₁⟩ := ih₁ (φ₂.listEncode.map Encodable.encode ++ rest)
    refine ⟨impDNF d₁ d₂, ?_, ?_⟩
    · have htok : Encodable.encode (Sum.inr (Sum.inr 0) :
          (Σ m, LRO.Term (Empty ⊕ Fin m)) ⊕ ((Σ m, LRO.Relations m) ⊕ ℕ)) = 3 := rfl
      have hlist : (φ₁.imp φ₂).listEncode.map Encodable.encode ++ rest =
          3 :: (φ₁.listEncode.map Encodable.encode ++ (φ₂.listEncode.map Encodable.encode ++ rest)) := by
        simp [Language.BoundedFormula.listEncode, List.append_assoc, htok]
      rw [hlist, evalFormulaSuffix_unfold]
      unfold formulaStep
      set tail := φ₁.listEncode.map Encodable.encode ++ (φ₂.listEncode.map Encodable.encode ++ rest)
      simp only [List.length_map, List.length_range, List.length_cons, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, ↓reduceIte, Nat.sub_self, List.getD_cons_zero]
      have hget : ((List.range (tail.length + 1)).map (evalFormulaSuffix (3 :: tail))).getD
          (tail.length + 1 - 1) [] = evalFormulaSuffix tail tail.length := by
        rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
        simpa using evalFormulaSuffix_tail_eq [3] tail
      rw [hget]
      dsimp only [tail]
      rw [hd₁, hd₂]
      simp
    · intro xs
      rw [evalDNF_imp, hev₁, hev₂, Language.BoundedFormula.realize_imp]
  | @all k φ ih =>
    obtain ⟨d, hd, hev⟩ := ih rest
    refine ⟨elimForall k d, ?_, ?_⟩
    · have htok : Encodable.encode (Sum.inr (Sum.inr 1) :
          (Σ m, LRO.Term (Empty ⊕ Fin m)) ⊕ ((Σ m, LRO.Relations m) ⊕ ℕ)) = 7 := rfl
      have hlist : φ.all.listEncode.map Encodable.encode ++ rest =
          7 :: (φ.listEncode.map Encodable.encode ++ rest) := by
        simp [Language.BoundedFormula.listEncode, htok]
      rw [hlist, evalFormulaSuffix_unfold]
      unfold formulaStep
      set tail := φ.listEncode.map Encodable.encode ++ rest
      simp only [List.length_map, List.length_range, List.length_cons, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, ↓reduceIte, Nat.sub_self, List.getD_cons_zero,
        show (7 : ℕ) ≠ 3 by decide]
      have hget : ((List.range (tail.length + 1)).map (evalFormulaSuffix (7 :: tail))).getD
          (tail.length + 1 - 1) [] = evalFormulaSuffix tail tail.length := by
        rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
        simpa using evalFormulaSuffix_tail_eq [7] tail
      rw [hget]
      dsimp only [tail]
      rw [hd]
      simp
    · intro xs
      rw [evalDNF_elimForall, Language.BoundedFormula.realize_all]
      constructor
      · intro h a
        have ha := h a
        rw [← extendFin_snoc] at ha
        exact (hev (Fin.snoc xs a)).mp ha
      · intro h a
        rw [← extendFin_snoc]
        exact (hev (Fin.snoc xs a)).mpr (h a)

lemma decideTarski_spec (φ : LRO.Sentence) :
    decideTarski (Encodable.encode φ) = true ↔ φ ∈ LRO.completeTheory ℝ := by
  unfold decideTarski
  have henc : Encodable.encode φ = Encodable.encode (φ.listEncode.map Encodable.encode) :=
    encode_list_eq_map_encode φ.listEncode
  rw [henc, Encodable.encodek]
  simp only [Option.getD_some]
  obtain ⟨d, hd, hev⟩ := evalFormulaSuffix_spec φ []
  rw [List.append_nil] at hd
  rw [hd, List.getD_cons_zero, evalClosedDNF_iff]
  have hext : extendFin (k := 0) default = fun _ => (0 : ℝ) := by
    funext i; unfold extendFin; simp
  rw [← hext, hev default]
  rw [Language.mem_completeTheory, Language.Sentence.Realize, Language.Formula.Realize]
  exact iff_of_eq (congr (congrArg (Language.BoundedFormula.Realize φ) (Subsingleton.elim _ _))
    (Subsingleton.elim _ _))

end TarskiProof

/- Section 5: Final Target Theorem -/

theorem OMA.solution :
    type_of% @TarskiExponentialFunctionProblem.isDecidable_completeTheory_real_orderedField := by
  rw [FirstOrder.Language.Theory.isDecidable_completeTheory_iff]
  exact ⟨TarskiProof.decideTarski, TarskiProof.primrec_decideTarski.to_comp,
    TarskiProof.decideTarski_spec⟩
