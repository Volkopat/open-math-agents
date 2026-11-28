import OMAStatements.S_oeis_a263660

/-!
# Alternating permutations with displacement at most two

An independent proof of Colin Barker's conjectures for OEIS A263660.
The registered statement and its conventions are imported unchanged.

Each permutation is encoded by the digits p(i)+2-i in {0,1,2,3,4}.
The proof establishes an exact bijection with bounded, injective shifted words.
Two sentinel digits at either end enforce the boundary bounds, and the last four
letters suffice to detect repeated values. An 80-state finite transition system
counts precisely these words. Its transition table and the identity T^7 v=2 T^5 v
are checked by the Lean kernel. Induction gives a(n+2)=2a(n) for n>=5;
the six initial values give both parity formulas and the generating function.

Source: https://oeis.org/A263660
Statement credit: @VashaTS. Proof: @CubeJerry with Codex (gpt-6.2-astra).
-/


section

-- Automaton

namespace A263660Proof

abbrev Digit := Fin 5

structure State where
  history : List Digit
  phase : ℕ
  deriving DecidableEq

def initial : State := ⟨[2, 2], 0⟩

/-- The new value differs from each of the four most recent values. -/
def separate (h : List Digit) (d : Digit) : Bool :=
  (h.zipIdx).all fun x => decide (x.1.val ≠ d.val + x.2 + 1)

def turnOK (h : List Digit) (d : Digit) : Bool :=
  match h with
  | b :: a :: _ =>
      !(decide (a.val < b.val + 1) && decide (b.val < d.val + 1)) &&
      !(decide (d.val + 1 < b.val) && decide (b.val + 1 < a.val))
  | _ => true

def push (h : List Digit) (d : Digit) : List Digit := d :: h.take 3

def step (s : State) (d : Digit) : Option State :=
  if separate s.history d && (s.phase < 2 || turnOK s.history d) then
    some ⟨push s.history d, min 2 (s.phase + 1)⟩
  else none

def accept (s : State) : Bool :=
  separate s.history 2 && separate (push s.history 2) 2

def runFrom : State → List Digit → Option State
  | s, [] => some s
  | s, d :: ds => (step s d).bind fun t => runFrom t ds

def run (w : List Digit) : Option State := runFrom initial w

def GoodWord (w : List Digit) : Prop :=
  ∃ s, run w = some s ∧ accept s = true

noncomputable def wordCount (n : ℕ) : ℕ :=
  Nat.card {w : List Digit // w.length = n ∧ GoodWord w}

end A263660Proof

end

section

-- Spec

namespace A263660Proof

def value (w : List Digit) (i : Fin w.length) : ℕ :=
  i.val + (w.get i).val

def LegalWord (w : List Digit) : Prop :=
  (∀ i : Fin w.length, 2 ≤ value w i ∧ value w i < w.length + 2) ∧
  Function.Injective (value w) ∧
  ∀ i j k : Fin w.length, j.val = i.val + 1 → k.val = j.val + 1 →
    ¬ (value w i < value w j ∧ value w j < value w k) ∧
    ¬ (value w k < value w j ∧ value w j < value w i)

noncomputable def legalCount (n : ℕ) : ℕ :=
  Nat.card {w : List Digit // w.length = n ∧ LegalWord w}

end A263660Proof

end

section

-- Local

namespace A263660Proof

def Separated (w : List Digit) : Prop :=
  ∀ (i j : ℕ) (hi : i < w.length) (hj : j < w.length), i < j →
    i + (w[i]).val ≠ j + (w[j]).val

def Triple (a b c : Digit) : Prop :=
  ¬ (a.val < b.val + 1 ∧ b.val < c.val + 1) ∧
  ¬ (c.val + 1 < b.val ∧ b.val + 1 < a.val)

def Zigzag (w : List Digit) : Prop :=
  ∀ (i : ℕ) (hi : i + 2 < w.length),
    Triple (w[i]) (w[i + 1]) (w[i + 2])

def preword (w : List Digit) : List Digit := [2, 2] ++ w

def padded (w : List Digit) : List Digit := preword w ++ [2, 2]

def history (w : List Digit) : List Digit := w.reverse.take 4

def stateOf (w : List Digit) : State :=
  ⟨history (preword w), min 2 w.length⟩

theorem separated_iff_injective (w : List Digit) :
    Separated w ↔ Function.Injective (value w) := by
  constructor
  · intro h i j he
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · exact False.elim (h i.val j.val i.isLt j.isLt hij he)
    · exact hij
    · exact False.elim (h j.val i.val j.isLt i.isLt hij he.symm)
  · intro h i j hi hj hij he
    have := h (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) he
    have heq : i = j := congrArg Fin.val this
    omega

end A263660Proof

end

section

-- Run

namespace A263660Proof

theorem separate_iff (h : List Digit) (d : Digit) :
    separate h d = true ↔
      ∀ (i : ℕ) (hi : i < h.length), (h[i]).val ≠ d.val + i + 1 := by
  simp only [separate, List.all_eq_true, decide_eq_true_eq]
  exact List.forall_mem_zipIdx'

theorem separate_take_four (h : List Digit) (d : Digit) :
    separate (h.take 4) d = true ↔ separate h d = true := by
  rw [separate_iff, separate_iff]
  constructor
  · intro H i hi
    by_cases h4 : i < 4
    · have hh : i < (h.take 4).length := by simp; omega
      simpa using H i hh
    · have hv := (h[i]).isLt
      omega
  · intro H i hi
    have hil : i < h.length := by
      have ht : i < min 4 h.length := by simpa using hi
      exact (lt_min_iff.mp ht).2
    simpa using H i hil

theorem separate_history_iff (w : List Digit) (d : Digit) :
    separate (history w) d = true ↔
      ∀ (i : ℕ) (hi : i < w.length), i + (w[i]).val ≠ w.length + d.val := by
  rw [history, separate_take_four, separate_iff]
  constructor
  · intro H i hi he
    have hj : w.length - 1 - i < w.reverse.length := by simp; omega
    have hh := H (w.length - 1 - i) hj
    rw [List.getElem_reverse] at hh
    have heq : w.length - 1 - (w.length - 1 - i) = i := by omega
    simp only [heq] at hh
    apply hh
    omega
  · intro H j hj he
    have hji : j < w.length := by simpa using hj
    rw [List.getElem_reverse] at he
    have hi : w.length - 1 - j < w.length := by omega
    apply H (w.length - 1 - j) hi
    omega

theorem separated_snoc_iff (w : List Digit) (d : Digit) :
    Separated (w ++ [d]) ↔
      Separated w ∧ separate (history w) d = true := by
  rw [separate_history_iff]
  constructor
  · intro H
    constructor
    · intro i j hi hj hij
      have he := H i j (by simp; omega) (by simp; omega) hij
      simpa only [List.getElem_append_left hi, List.getElem_append_left hj] using he
    · intro i hi
      have he := H i w.length (by simp; omega) (by simp) hi
      simpa only [List.getElem_append_left hi, List.getElem_concat_length rfl] using he
  · rintro ⟨H, Hd⟩ i j hi hj hij
    have hil : i < w.length := by simp at hi hj; omega
    by_cases hjl : j < w.length
    · simpa only [List.getElem_append_left hil, List.getElem_append_left hjl] using
        H i j hil hjl hij
    · have hje : j = w.length := by simp at hj; omega
      subst j
      simpa only [List.getElem_append_left hil, List.getElem_concat_length rfl] using Hd i hil

@[simp] theorem history_snoc (w : List Digit) (d : Digit) :
    history (w ++ [d]) = push (history w) d := by
  simp [history, push, List.take_take]

@[simp] theorem preword_snoc (w : List Digit) (d : Digit) :
    preword (w ++ [d]) = preword w ++ [d] := by
  simp [preword, List.append_assoc]

@[simp] theorem stateOf_nil : stateOf [] = initial := by rfl

def TailTriple (w : List Digit) (d : Digit) : Prop :=
  ∀ h : 2 ≤ w.length, Triple (w[w.length - 2]) (w[w.length - 1]) d

theorem zigzag_snoc_iff (w : List Digit) (d : Digit) :
    Zigzag (w ++ [d]) ↔ Zigzag w ∧ TailTriple w d := by
  constructor
  · intro H
    constructor
    · intro i hi
      have hh := H i (by simp; omega)
      simpa only [List.getElem_append_left (by omega : i < w.length),
        List.getElem_append_left (by omega : i + 1 < w.length),
        List.getElem_append_left hi] using hh
    · intro hw
      have hh := H (w.length - 2) (by simp; omega)
      have he : w.length - 2 + 2 = w.length := by omega
      have he1 : w.length - 2 + 1 = w.length - 1 := by omega
      simpa only [he, he1,
        List.getElem_append_left (by omega : w.length - 2 < w.length),
        List.getElem_append_left (by omega : w.length - 1 < w.length),
        List.getElem_concat_length rfl] using hh
  · rintro ⟨H, Hd⟩ i hi
    by_cases hil : i + 2 < w.length
    · simpa only [List.getElem_append_left (by omega : i < w.length),
        List.getElem_append_left (by omega : i + 1 < w.length),
        List.getElem_append_left hil] using H i hil
    · have he : i + 2 = w.length := by simp at hi; omega
      have h2 : 2 ≤ w.length := by omega
      have he0 : i = w.length - 2 := by omega
      have he1 : w.length - 2 + 1 = w.length - 1 := by omega
      have he2 : w.length - 2 + 2 = w.length := by omega
      simpa only [he0, he1, he2,
        List.getElem_append_left (by omega : w.length - 2 < w.length),
        List.getElem_append_left (by omega : w.length - 1 < w.length),
        List.getElem_concat_length rfl] using Hd h2

theorem turnOK_iff (h : List Digit) (d : Digit) (hh : 2 ≤ h.length) :
    turnOK h d = true ↔ Triple (h[1]) (h[0]) d := by
  cases h with
  | nil => simp at hh
  | cons b h =>
    cases h with
    | nil => simp at hh
    | cons a h => simp [turnOK, Triple] <;> omega

theorem turn_history_iff (w : List Digit) (d : Digit) (hw : 2 ≤ w.length) :
    turnOK (history (preword w)) d = true ↔
      Triple (w[w.length - 2]) (w[w.length - 1]) d := by
  have hlen : 2 ≤ (history (preword w)).length := by simp [history, preword]
  rw [turnOK_iff _ _ hlen]
  have h0 : (history (preword w))[0] = w[w.length - 1] := by
    simp only [history, List.getElem_take, List.getElem_reverse, preword,
      List.length_append, List.length_cons, List.length_nil]
    rw [List.getElem_append_right (by simp; omega)]
    congr 1
    simp only [List.length_cons, List.length_nil]
    omega
  have h1 : (history (preword w))[1] = w[w.length - 2] := by
    simp only [history, List.getElem_take, List.getElem_reverse, preword,
      List.length_append, List.length_cons, List.length_nil]
    rw [List.getElem_append_right (by simp; omega)]
    congr 1
    simp only [List.length_cons, List.length_nil]
    omega
  rw [h0, h1]

theorem turn_phase_iff (w : List Digit) (d : Digit) :
    ((min 2 w.length < 2) || turnOK (history (preword w)) d) = true ↔
      TailTriple w d := by
  by_cases hw : 2 ≤ w.length
  · have he : min 2 w.length = 2 := min_eq_left hw
    have hdec : decide (min 2 w.length < 2) = false := by simp [he]
    simp only [hdec, Bool.false_or]
    rw [turn_history_iff w d hw]
    simp [TailTriple, hw]
  · have he : min 2 w.length < 2 := by omega
    simp [he, TailTriple, hw]

@[simp] theorem stateOf_snoc (w : List Digit) (d : Digit) :
    stateOf (w ++ [d]) =
      ⟨push (stateOf w).history d, min 2 ((stateOf w).phase + 1)⟩ := by
  simp only [stateOf, preword_snoc, history_snoc, List.length_append, List.length_singleton]
  congr 1
  omega

theorem runFrom_snoc (s : State) (w : List Digit) (d : Digit) :
    runFrom s (w ++ [d]) = (runFrom s w).bind (fun t => step t d) := by
  induction w generalizing s with
  | nil => simp [runFrom]
  | cons a w ih => simp [runFrom, ih, Option.bind_assoc]

theorem run_snoc (w : List Digit) (d : Digit) :
    run (w ++ [d]) = (run w).bind (fun t => step t d) :=
  runFrom_snoc initial w d

open scoped Classical in
theorem step_stateOf (w : List Digit) (d : Digit) :
    step (stateOf w) d =
      if separate (history (preword w)) d = true ∧ TailTriple w d then
        some (stateOf (w ++ [d])) else none := by
  classical
  have hc :
      (separate (history (preword w)) d &&
        ((min 2 w.length < 2) || turnOK (history (preword w)) d)) = true ↔
        separate (history (preword w)) d = true ∧ TailTriple w d := by
    rw [Bool.and_eq_true, turn_phase_iff]
  rw [step]
  change (if (separate (history (preword w)) d &&
      ((min 2 w.length < 2) || turnOK (history (preword w)) d)) = true then
      some (⟨push (stateOf w).history d, min 2 ((stateOf w).phase + 1)⟩ : State) else none) = _
  simp only [hc, ← stateOf_snoc]

open scoped Classical in
theorem run_formula (w : List Digit) :
    run w = if Separated (preword w) ∧ Zigzag w then some (stateOf w) else none := by
  classical
  induction w using List.reverseRecOn with
  | nil =>
    have hs : Separated (preword []) := by
      intro i j hi hj hij
      simp [preword] at hi hj
      have hi0 : i = 0 := by omega
      have hj1 : j = 1 := by omega
      subst i; subst j
      simp [preword]
    have hz : Zigzag [] := by intro i hi; simp at hi
    simp [run, runFrom, hs, hz]
  | append_singleton w d ih =>
    have hsep : Separated (preword (w ++ [d])) ↔
        Separated (preword w) ∧ separate (history (preword w)) d = true := by
      rw [preword_snoc, separated_snoc_iff]
    rw [run_snoc, ih]
    by_cases hs : Separated (preword w) <;>
      by_cases hz : Zigzag w <;>
      by_cases hd : separate (history (preword w)) d = true <;>
      by_cases ht : TailTriple w d <;>
      simp [hs, hz, hd, ht, separated_snoc_iff, zigzag_snoc_iff, step_stateOf]

theorem separated_padded_iff (w : List Digit) :
    Separated (padded w) ↔ Separated (preword w) ∧ accept (stateOf w) = true := by
  have he : padded w = (preword w ++ [2]) ++ [2] := by
    simp [padded, List.append_assoc]
  rw [he, separated_snoc_iff, separated_snoc_iff]
  simp [accept, stateOf, and_assoc]

theorem goodWord_iff_padded (w : List Digit) :
    GoodWord w ↔ Separated (padded w) ∧ Zigzag w := by
  classical
  by_cases hs : Separated (preword w) <;> by_cases hz : Zigzag w <;>
    simp [GoodWord, run_formula, separated_padded_iff, hs, hz]

end A263660Proof

end

section

-- Bijection

namespace A263660Proof

open OMA.S_oeis_a263660

def digit {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : Good p) (i : Fin n) : Digit :=
  ⟨(p i).val + 2 - i.val, by
    have h := abs_le.mp (hp.1 i)
    omega⟩

theorem digit_value {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : Good p) (i : Fin n) :
    i.val + (digit p hp i).val = (p i).val + 2 := by
  have h := abs_le.mp (hp.1 i)
  simp only [digit]
  omega

def encode {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : Good p) : List Digit :=
  List.ofFn (digit p hp)

@[simp] theorem encode_length {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : Good p) :
    (encode p hp).length = n := by simp [encode]

theorem encode_value {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : Good p)
    (i : Fin (encode p hp).length) :
    value (encode p hp) i = (p (Fin.cast (encode_length p hp) i)).val + 2 := by
  have hg : (encode p hp).get i = digit p hp (Fin.cast (encode_length p hp) i) :=
    List.get_ofFn (digit p hp) i
  change i.val + ((encode p hp).get i).val = _
  rw [hg]
  exact digit_value p hp (Fin.cast (encode_length p hp) i)

theorem legal_encode {n : ℕ} (p : Equiv.Perm (Fin n)) (hp : Good p) :
    LegalWord (encode p hp) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [encode_value]
    have hl := encode_length p hp
    have hb := (p (Fin.cast (encode_length p hp) i)).isLt
    omega
  · intro i j hij
    rw [encode_value, encode_value] at hij
    have h : p (Fin.cast (encode_length p hp) i) =
        p (Fin.cast (encode_length p hp) j) := Fin.ext (by omega)
    have h' := p.injective h
    exact Fin.ext (congrArg (fun x : Fin n => x.val) h')
  · intro i j k hj hk
    simp only [encode_value]
    have h := hp.2 (Fin.cast (encode_length p hp) i)
      (Fin.cast (encode_length p hp) j) (Fin.cast (encode_length p hp) k) hj hk
    simpa only [Fin.lt_def, Nat.add_lt_add_iff_right] using h

theorem encode_injective {n : ℕ} {p q : Equiv.Perm (Fin n)} {hp : Good p} {hq : Good q}
    (h : encode p hp = encode q hq) : p = q := by
  have hfun := List.ofFn_injective h
  apply Equiv.ext
  intro i
  have hi := congrArg (fun f => (f i).val) hfun
  have hp' := digit_value p hp i
  have hq' := digit_value q hq i
  apply Fin.ext
  omega

def wordMap {n : ℕ} (w : List Digit) (hn : w.length = n) (hw : LegalWord w)
    (i : Fin n) : Fin n :=
  ⟨value w (Fin.cast hn.symm i) - 2, by
    have h := hw.1 (Fin.cast hn.symm i)
    omega⟩

theorem wordMap_value {n : ℕ} (w : List Digit) (hn : w.length = n) (hw : LegalWord w)
    (i : Fin n) : (wordMap w hn hw i).val + 2 = value w (Fin.cast hn.symm i) := by
  have h := hw.1 (Fin.cast hn.symm i)
  simp only [wordMap]
  omega

theorem wordMap_injective {n : ℕ} (w : List Digit) (hn : w.length = n)
    (hw : LegalWord w) : Function.Injective (wordMap w hn hw) := by
  intro i j hij
  have hi := wordMap_value w hn hw i
  have hj := wordMap_value w hn hw j
  have hv := congrArg Fin.val hij
  have h := hw.2.1 (a₁ := Fin.cast hn.symm i) (a₂ := Fin.cast hn.symm j) (by omega)
  exact Fin.ext (congrArg (fun x : Fin w.length => x.val) h)

noncomputable def decode {n : ℕ} (w : List Digit) (hn : w.length = n) (hw : LegalWord w) :
    Equiv.Perm (Fin n) :=
  Equiv.ofBijective (wordMap w hn hw)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨wordMap_injective w hn hw, rfl⟩)

theorem decode_value {n : ℕ} (w : List Digit) (hn : w.length = n) (hw : LegalWord w)
    (i : Fin n) : (decode w hn hw i).val + 2 = value w (Fin.cast hn.symm i) :=
  wordMap_value w hn hw i

theorem good_decode {n : ℕ} (w : List Digit) (hn : w.length = n) (hw : LegalWord w) :
    Good (decode w hn hw) := by
  refine ⟨?_, ?_⟩
  · intro i
    have hv := decode_value w hn hw i
    have hd := (w.get (Fin.cast hn.symm i)).isLt
    simp only [value, Fin.val_cast] at hv
    rw [abs_le]
    omega
  · intro i j k hj hk
    have h := hw.2.2 (Fin.cast hn.symm i) (Fin.cast hn.symm j)
      (Fin.cast hn.symm k) hj hk
    have hi := decode_value w hn hw i
    have hj' := decode_value w hn hw j
    have hk' := decode_value w hn hw k
    simp only [Fin.lt_def]
    omega

theorem encode_decode {n : ℕ} (w : List Digit) (hn : w.length = n) (hw : LegalWord w) :
    encode (decode w hn hw) (good_decode w hn hw) = w := by
  apply List.ext_getElem
  · simpa using hn.symm
  · intro i hi hj
    simp only [encode, List.getElem_ofFn]
    apply Fin.ext
    have hv := decode_value w hn hw ⟨i, by simpa using hi⟩
    simp only [value, Fin.val_cast, List.get_eq_getElem] at hv
    simp only [digit]
    omega

def encodeGood (n : ℕ) : {p : Equiv.Perm (Fin n) // Good p} →
    {w : List Digit // w.length = n ∧ LegalWord w} :=
  fun p => ⟨encode p.val p.property, encode_length _ _, legal_encode _ _⟩

theorem encodeGood_bijective (n : ℕ) : Function.Bijective (encodeGood n) := by
  constructor
  · intro p q h
    apply Subtype.ext
    exact encode_injective (congrArg Subtype.val h)
  · intro w
    refine ⟨⟨decode w.val w.property.1 w.property.2,
      good_decode w.val w.property.1 w.property.2⟩, ?_⟩
    apply Subtype.ext
    exact encode_decode w.val w.property.1 w.property.2

theorem a_eq_legalCount (n : ℕ) : OMA.S_oeis_a263660.a n = legalCount n := by
  classical
  rw [legalCount, ← Nat.card_congr (Equiv.ofBijective (encodeGood n) (encodeGood_bijective n))]
  simp [a, Nat.card_eq_fintype_card, Fintype.card_subtype]

end A263660Proof

end

section

-- Padded

namespace A263660Proof

@[simp] theorem padded_length (w : List Digit) : (padded w).length = w.length + 4 := by
  simp [padded, preword]

def padLeft (w : List Digit) (j : Fin 2) : Fin (padded w).length :=
  ⟨j.val, by rw [padded_length]; omega⟩

def padMiddle (w : List Digit) (j : Fin w.length) : Fin (padded w).length :=
  ⟨j.val + 2, by rw [padded_length]; omega⟩

def padRight (w : List Digit) (j : Fin 2) : Fin (padded w).length :=
  ⟨w.length + 2 + j.val, by rw [padded_length]; omega⟩

@[simp] theorem padLeft_value (w : List Digit) (j : Fin 2) :
    value (padded w) (padLeft w j) = j.val + 2 := by
  fin_cases j <;> simp [value, padded, preword, padLeft, List.get_eq_getElem]

@[simp] theorem padMiddle_value (w : List Digit) (j : Fin w.length) :
    value (padded w) (padMiddle w j) = value w j + 2 := by
  have hj := j.isLt
  simp [value, padded, preword, padMiddle, List.get_eq_getElem,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem padRight_value (w : List Digit) (j : Fin 2) :
    value (padded w) (padRight w j) = w.length + 4 + j.val := by
  have hg : (padded w).get (padRight w j) = (2 : Digit) := by
    simp only [List.get_eq_getElem, padRight]
    unfold padded
    rw [List.getElem_append_right (by simp [preword])]
    have he : w.length + 2 + j.val - (preword w).length = j.val := by
      simp [preword]
    simp only [he]
    fin_cases j <;> rfl
  change w.length + 2 + j.val + ((padded w).get (padRight w j)).val = _
  rw [hg]
  change w.length + 2 + j.val + 2 = w.length + 4 + j.val
  omega

theorem pad_cases (w : List Digit) (i : Fin (padded w).length) :
    (∃ j : Fin 2, i = padLeft w j) ∨
    (∃ j : Fin w.length, i = padMiddle w j) ∨
    (∃ j : Fin 2, i = padRight w j) := by
  have hi := i.isLt
  have hl := padded_length w
  by_cases h1 : i.val < 2
  · exact Or.inl ⟨⟨i.val, h1⟩, Fin.ext rfl⟩
  by_cases h2 : i.val < w.length + 2
  · exact Or.inr (Or.inl ⟨⟨i.val - 2, by omega⟩, Fin.ext (by simp [padMiddle]; omega)⟩)
  · exact Or.inr (Or.inr ⟨⟨i.val - (w.length + 2), by omega⟩,
      Fin.ext (by simp [padRight]; omega)⟩)

theorem separated_padded_iff_legal (w : List Digit) :
    Separated (padded w) ↔
      (∀ i : Fin w.length, 2 ≤ value w i ∧ value w i < w.length + 2) ∧
      Function.Injective (value w) := by
  rw [separated_iff_injective]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      have h0 : value w i ≠ 0 := by
        intro hv
        have he := h (a₁ := padMiddle w i) (a₂ := padLeft w 0) (by simp [hv])
        have := congrArg (fun x : Fin (padded w).length => x.val) he
        simp only [padMiddle, padLeft, Fin.val_mk, Fin.val_zero] at this
        omega
      have h1 : value w i ≠ 1 := by
        intro hv
        have he := h (a₁ := padMiddle w i) (a₂ := padLeft w 1) (by simp [hv])
        have := congrArg (fun x : Fin (padded w).length => x.val) he
        simp only [padMiddle, padLeft, Fin.val_mk, Fin.val_one] at this
        omega
      have h2 : value w i ≠ w.length + 2 := by
        intro hv
        have he := h (a₁ := padMiddle w i) (a₂ := padRight w 0) (by simp [hv])
        have := congrArg (fun x : Fin (padded w).length => x.val) he
        simp only [padMiddle, padRight, Fin.val_mk, Fin.val_zero] at this
        omega
      have h3 : value w i ≠ w.length + 3 := by
        intro hv
        have he := h (a₁ := padMiddle w i) (a₂ := padRight w 1) (by simp [hv])
        have := congrArg (fun x : Fin (padded w).length => x.val) he
        simp only [padMiddle, padRight, Fin.val_mk, Fin.val_one] at this
        omega
      have hd := (w.get i).isLt
      have hi := i.isLt
      unfold value at *
      omega
    · intro i j hij
      have he := h (a₁ := padMiddle w i) (a₂ := padMiddle w j) (by simpa using hij)
      have := congrArg (fun x : Fin (padded w).length => x.val) he
      apply Fin.ext
      simp only [padMiddle, Fin.val_mk] at this
      omega
  · rintro ⟨hr, hinj⟩ i j hij
    rcases pad_cases w i with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
      rcases pad_cases w j with ⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩ <;>
      simp only [padLeft_value, padMiddle_value, padRight_value] at hij
    · congr 1
      apply Fin.ext
      omega
    · have := hr y
      have := x.isLt
      omega
    · have := x.isLt
      omega
    · have := hr x
      have := y.isLt
      omega
    · have he : value w x = value w y := by omega
      exact congrArg (padMiddle w) (hinj he)
    · have := hr x
      omega
    · have := y.isLt
      omega
    · have := hr y
      omega
    · congr 1
      apply Fin.ext
      omega

theorem zigzag_iff (w : List Digit) : Zigzag w ↔
    ∀ i j k : Fin w.length, j.val = i.val + 1 → k.val = j.val + 1 →
      ¬ (value w i < value w j ∧ value w j < value w k) ∧
      ¬ (value w k < value w j ∧ value w j < value w i) := by
  constructor
  · intro h i j k hj hk
    have hb : i.val + 2 < w.length := by omega
    have hh := h i.val hb
    have hgetj : w[i.val + 1] = w.get j := by
      simp only [List.get_eq_getElem]
      congr 1
      omega
    have hgetk : w[i.val + 2] = w.get k := by
      simp only [List.get_eq_getElem]
      congr 1
      omega
    simp only [Triple, hgetj, hgetk, ← List.get_eq_getElem] at hh
    unfold value
    omega
  · intro h i hi
    have hh := h ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, hi⟩ rfl (by rfl)
    simp only [value, List.get_eq_getElem] at hh
    unfold Triple
    omega

theorem legal_iff_padded (w : List Digit) :
    LegalWord w ↔ Separated (padded w) ∧ Zigzag w := by
  rw [separated_padded_iff_legal, zigzag_iff]
  simp only [LegalWord, and_assoc]

end A263660Proof

end

section

-- Bridge

namespace A263660Proof

theorem goodWord_iff_legal (w : List Digit) : GoodWord w ↔ LegalWord w :=
  (goodWord_iff_padded w).trans (legal_iff_padded w).symm

theorem legalCount_eq_wordCount (n : ℕ) : legalCount n = wordCount n := by
  unfold legalCount wordCount
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun w => and_congr Iff.rfl (goodWord_iff_legal w).symm

theorem a_eq_wordCount (n : ℕ) : OMA.S_oeis_a263660.a n = wordCount n :=
  (a_eq_legalCount n).trans (legalCount_eq_wordCount n)

end A263660Proof

end

section

-- Count

namespace A263660Count

variable {S : Type*}

def paths (succ : S → List S) (accept : S → ℕ) : ℕ → S → ℕ
  | 0, s => accept s
  | n + 1, s => ((succ s).map (paths succ accept n)).sum

lemma sum_double (L : List S) (f : S → ℕ) :
    (L.map (fun s => 2 * f s)).sum = 2 * (L.map f).sum := by
  induction L with
  | nil => rfl
  | cons s L ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem paths_eq_values (succ : S → List S) (accept : S → ℕ) (v : ℕ → S → ℕ)
    (hzero : ∀ s, accept s = v 0 s)
    (hstep : ∀ n, n < 7 → ∀ s, ((succ s).map (v n)).sum = v (n + 1) s) :
    ∀ n, n ≤ 7 → ∀ s, paths succ accept n s = v n s := by
  intro n
  induction n with
  | zero => intro _ s; exact hzero s
  | succ n ih =>
    intro hn s
    change ((succ s).map (paths succ accept n)).sum = v (n + 1) s
    rw [show paths succ accept n = v n from funext (ih (by omega))]
    exact hstep n (by omega) s

theorem recurrence_from_base (succ : S → List S) (accept : S → ℕ)
    (hbase : ∀ s, paths succ accept 7 s = 2 * paths succ accept 5 s) :
    ∀ k s, paths succ accept (k + 7) s = 2 * paths succ accept (k + 5) s := by
  intro k
  induction k with
  | zero => intro s; exact hbase s
  | succ k ih =>
    intro s
    change ((succ s).map (paths succ accept (k + 7))).sum =
      2 * ((succ s).map (paths succ accept (k + 5))).sum
    rw [show paths succ accept (k + 7) =
      (fun t => 2 * paths succ accept (k + 5) t) from funext ih]
    exact sum_double _ _

theorem recurrence (succ : S → List S) (accept : S → ℕ)
    (hbase : ∀ s, paths succ accept 7 s = 2 * paths succ accept 5 s)
    (n : ℕ) (hn : 5 ≤ n) (s : S) :
    paths succ accept (n + 2) s = 2 * paths succ accept n s := by
  have he5 : n - 5 + 5 = n := by omega
  have he7 : n - 5 + 7 = n + 2 := by omega
  simpa only [he5, he7] using recurrence_from_base succ accept hbase (n - 5) s

end A263660Count

end

section

-- Words

namespace A263660Proof

open scoped BigOperators

theorem card_lists {A : Type*} (n : ℕ) (P : List A → Prop) :
    Nat.card {w : List A // w.length = n ∧ P w} =
      Nat.card {w : Fin n → A // P (List.ofFn w)} := by
  let e : {w : List A // w.length = n ∧ P w} ≃
      {v : List.Vector A n // P v.val} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun w : List A => w.length = n) P).symm
  apply Nat.card_congr
  refine e.trans ((Equiv.vectorEquivFin A n).subtypeEquiv ?_)
  intro v
  change P v.val ↔ P (List.ofFn v.get)
  have hv : List.ofFn v.get = v.val := by
    calc
      List.ofFn v.get = v.toList := by
        simpa only [List.Vector.toList_ofFn] using
          congrArg List.Vector.toList (List.Vector.ofFn_get v)
      _ = v.val := by cases v; rfl
  rw [hv]

theorem card_words_succ {A : Type*} [Fintype A] (n : ℕ)
    (P : (Fin (n + 1) → A) → Prop) :
    Nat.card {w : Fin (n + 1) → A // P w} =
      ∑ a : A, Nat.card {v : Fin n → A // P (Fin.cons a v)} := by
  classical
  calc
    _ = Nat.card {p : A × (Fin n → A) // P (Fin.cons p.1 p.2)} :=
      Nat.card_congr ((Fin.consEquiv (fun _ : Fin (n + 1) => A)).symm.subtypeEquiv
        (by intro w; simp [Fin.consEquiv]))
    _ = Nat.card (Σ a : A, {v : Fin n → A // P (Fin.cons a v)}) :=
      Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun a v => P (Fin.cons a v)))
    _ = _ := Nat.card_sigma

noncomputable def suffixCount (s : State) (n : ℕ) : ℕ :=
  Nat.card {w : Fin n → Digit //
    ∃ t, runFrom s (List.ofFn w) = some t ∧ accept t = true}

theorem wordCount_eq_suffix (n : ℕ) : wordCount n = suffixCount initial n := by
  unfold wordCount
  rw [card_lists]
  rfl

lemma suffixCount_zero (s : State) :
    suffixCount s 0 = if accept s then 1 else 0 := by
  cases h : accept s <;> simp [suffixCount, runFrom, h, Nat.card_eq_fintype_card]

lemma suffixCount_succ (s : State) (n : ℕ) :
    suffixCount s (n + 1) =
      ∑ d : Digit, (step s d).elim 0 (fun t => suffixCount t n) := by
  classical
  unfold suffixCount
  rw [card_words_succ]
  apply Finset.sum_congr rfl
  intro d _
  cases h : step s d with
  | none => simp [runFrom, h, Nat.card_eq_fintype_card]
  | some t => simp [runFrom, h]

lemma sum_digits (f : Digit → ℕ) :
    ((List.finRange 5).map f).sum = ∑ d : Digit, f d := by
  rw [← List.ofFn_eq_map, List.sum_ofFn]

lemma sum_filterMap {A B : Type*} (L : List A) (f : A → Option B) (g : B → ℕ) :
    ((L.filterMap f).map g).sum = (L.map (fun a => (f a).elim 0 g)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => cases h : f a <;> simp [h, ih]

variable {I : Type*}

theorem suffixCount_eq_paths
    (state : I → State) (succ : I → List I) (accepted : I → ℕ)
    (hstep : ∀ i, (List.finRange 5).filterMap (step (state i)) = (succ i).map state)
    (haccept : ∀ i, (if accept (state i) then 1 else 0) = accepted i) :
    ∀ n i, suffixCount (state i) n = A263660Count.paths succ accepted n i := by
  intro n
  induction n with
  | zero => intro i; exact (suffixCount_zero _).trans (haccept i)
  | succ n ih =>
    intro i
    rw [suffixCount_succ, ← sum_digits, ← sum_filterMap, hstep, List.map_map]
    change ((succ i).map (fun j => suffixCount (state j) n)).sum = _
    rw [show (fun j => suffixCount (state j) n) =
      A263660Count.paths succ accepted n from funext ih]
    rfl

theorem wordCount_eq_paths
    (state : I → State) (succ : I → List I) (accepted : I → ℕ) (start : I)
    (hstep : ∀ i, (List.finRange 5).filterMap (step (state i)) = (succ i).map state)
    (haccept : ∀ i, (if accept (state i) then 1 else 0) = accepted i)
    (hstart : state start = initial) (n : ℕ) :
    wordCount n = A263660Count.paths succ accepted n start := by
  rw [wordCount_eq_suffix, ← hstart]
  exact suffixCount_eq_paths state succ accepted hstep haccept n start

end A263660Proof

end

section

-- Certificate

namespace A263660Table

def stateData (i : ℕ) : List (Fin 5) × ℕ := (if i < 40 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then ([2, 2], 0) else ([2, 2, 2], 1)) else (if i < 3 then ([3, 2, 2], 1) else (if i < 4 then ([4, 2, 2], 1) else ([2, 2, 2, 2], 2)))) else (if i < 7 then (if i < 6 then ([3, 2, 2, 2], 2) else ([4, 2, 2, 2], 2)) else (if i < 8 then ([1, 3, 2, 2], 2) else (if i < 9 then ([3, 3, 2, 2], 2) else ([4, 3, 2, 2], 2))))) else (if i < 15 then (if i < 12 then (if i < 11 then ([1, 4, 2, 2], 2) else ([2, 4, 2, 2], 2)) else (if i < 13 then ([4, 4, 2, 2], 2) else (if i < 14 then ([2, 1, 3, 2], 2) else ([3, 1, 3, 2], 2)))) else (if i < 17 then (if i < 16 then ([4, 1, 3, 2], 2) else ([0, 3, 3, 2], 2)) else (if i < 18 then ([0, 4, 3, 2], 2) else (if i < 19 then ([2, 4, 3, 2], 2) else ([1, 1, 4, 2], 2)))))) else (if i < 30 then (if i < 25 then (if i < 22 then (if i < 21 then ([3, 1, 4, 2], 2) else ([4, 1, 4, 2], 2)) else (if i < 23 then ([3, 2, 4, 2], 2) else (if i < 24 then ([4, 2, 4, 2], 2) else ([0, 4, 4, 2], 2)))) else (if i < 27 then (if i < 26 then ([1, 4, 4, 2], 2) else ([1, 3, 1, 3], 2)) else (if i < 28 then ([1, 4, 1, 3], 2) else (if i < 29 then ([2, 4, 1, 3], 2) else ([2, 0, 3, 3], 2))))) else (if i < 35 then (if i < 32 then (if i < 31 then ([3, 0, 3, 3], 2) else ([4, 0, 3, 3], 2)) else (if i < 33 then ([1, 0, 4, 3], 2) else (if i < 34 then ([3, 0, 4, 3], 2) else ([4, 0, 4, 3], 2)))) else (if i < 37 then (if i < 36 then ([3, 2, 4, 3], 2) else ([4, 2, 4, 3], 2)) else (if i < 38 then ([0, 3, 1, 4], 2) else (if i < 39 then ([0, 4, 1, 4], 2) else ([2, 4, 1, 4], 2))))))) else (if i < 60 then (if i < 50 then (if i < 45 then (if i < 42 then (if i < 41 then ([2, 4, 2, 4], 2) else ([0, 0, 4, 4], 2)) else (if i < 43 then ([3, 0, 4, 4], 2) else (if i < 44 then ([4, 0, 4, 4], 2) else ([3, 1, 4, 4], 2)))) else (if i < 47 then (if i < 46 then ([4, 1, 4, 4], 2) else ([2, 1, 3, 1], 2)) else (if i < 48 then ([3, 1, 3, 1], 2) else (if i < 49 then ([4, 1, 3, 1], 2) else ([1, 1, 4, 1], 2))))) else (if i < 55 then (if i < 52 then (if i < 51 then ([3, 1, 4, 1], 2) else ([4, 1, 4, 1], 2)) else (if i < 53 then ([3, 2, 4, 1], 2) else (if i < 54 then ([4, 2, 4, 1], 2) else ([1, 3, 0, 3], 2)))) else (if i < 57 then (if i < 56 then ([1, 4, 0, 3], 2) else ([2, 4, 0, 3], 2)) else (if i < 58 then ([0, 3, 0, 4], 2) else (if i < 59 then ([0, 4, 0, 4], 2) else ([2, 4, 0, 4], 2)))))) else (if i < 70 then (if i < 65 then (if i < 62 then (if i < 61 then ([2, 0, 3, 1], 2) else ([3, 0, 3, 1], 2)) else (if i < 63 then ([4, 0, 3, 1], 2) else (if i < 64 then ([1, 0, 4, 1], 2) else ([3, 0, 4, 1], 2)))) else (if i < 67 then (if i < 66 then ([4, 0, 4, 1], 2) else ([2, 1, 3, 0], 2)) else (if i < 68 then ([3, 1, 3, 0], 2) else (if i < 69 then ([4, 1, 3, 0], 2) else ([1, 1, 4, 0], 2))))) else (if i < 75 then (if i < 72 then (if i < 71 then ([3, 1, 4, 0], 2) else ([4, 1, 4, 0], 2)) else (if i < 73 then ([3, 2, 4, 0], 2) else (if i < 74 then ([4, 2, 4, 0], 2) else ([2, 0, 3, 0], 2)))) else (if i < 77 then (if i < 76 then ([3, 0, 3, 0], 2) else ([4, 0, 3, 0], 2)) else (if i < 78 then ([1, 0, 4, 0], 2) else (if i < 79 then ([3, 0, 4, 0], 2) else ([4, 0, 4, 0], 2))))))))

def state (i : Fin 80) : A263660Proof.State :=
  ⟨(stateData i.val).1, (stateData i.val).2⟩

def successorData (i : ℕ) : List (Fin 80) := (if i < 40 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then [1, 2, 3] else [4, 5, 6]) else (if i < 3 then [7, 8, 9] else (if i < 4 then [10, 11, 12] else []))) else (if i < 7 then (if i < 6 then [7] else [10, 11]) else (if i < 8 then [13, 14, 15] else (if i < 9 then [16] else [17, 18])))) else (if i < 15 then (if i < 12 then (if i < 11 then [19, 20, 21] else [22, 23]) else (if i < 13 then [24, 25] else (if i < 14 then [] else [26]))) else (if i < 17 then (if i < 16 then [27, 28] else [29, 30, 31]) else (if i < 18 then [32, 33, 34] else (if i < 19 then [35, 36] else []))))) else (if i < 30 then (if i < 25 then (if i < 22 then (if i < 21 then [37] else [38, 39]) else (if i < 23 then [] else (if i < 24 then [40] else [41, 42, 43]))) else (if i < 27 then (if i < 26 then [44, 45] else [46, 47, 48]) else (if i < 28 then [49, 50, 51] else (if i < 29 then [52, 53] else [])))) else (if i < 35 then (if i < 32 then (if i < 31 then [54] else [55, 56]) else (if i < 33 then [] else (if i < 34 then [57] else [58, 59]))) else (if i < 37 then (if i < 36 then [] else [40]) else (if i < 38 then [60, 61, 62] else (if i < 39 then [63, 64, 65] else [52, 53])))))) else (if i < 60 then (if i < 50 then (if i < 45 then (if i < 42 then (if i < 41 then [22, 23] else []) else (if i < 43 then [] else (if i < 44 then [59] else []))) else (if i < 47 then (if i < 46 then [39] else []) else (if i < 48 then [26] else (if i < 49 then [27, 28] else [])))) else (if i < 55 then (if i < 52 then (if i < 51 then [37] else [38, 39]) else (if i < 53 then [] else (if i < 54 then [40] else [66, 67, 68]))) else (if i < 57 then (if i < 56 then [69, 70, 71] else [72, 73]) else (if i < 58 then [74, 75, 76] else (if i < 59 then [77, 78, 79] else [72, 73]))))) else (if i < 70 then (if i < 65 then (if i < 62 then (if i < 61 then [] else [54]) else (if i < 63 then [55, 56] else (if i < 64 then [] else [57]))) else (if i < 67 then (if i < 66 then [58, 59] else []) else (if i < 68 then [26] else (if i < 69 then [27, 28] else [])))) else (if i < 75 then (if i < 72 then (if i < 71 then [37] else [38, 39]) else (if i < 73 then [] else (if i < 74 then [40] else []))) else (if i < 77 then (if i < 76 then [54] else [55, 56]) else (if i < 78 then [] else (if i < 79 then [57] else [58, 59])))))))

def succ (i : Fin 80) : List (Fin 80) := successorData i.val

def v0Data (i : ℕ) : ℕ := (if i < 40 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then 1 else (if i < 3 then 0 else (if i < 4 then 0 else 1))) else (if i < 7 then 0 else (if i < 8 then 1 else 0))) else (if i < 15 then (if i < 12 then 0 else (if i < 13 then 0 else (if i < 14 then 1 else 0))) else (if i < 17 then (if i < 16 then 0 else 1) else (if i < 18 then 0 else (if i < 19 then 0 else 1))))) else (if i < 30 then (if i < 25 then 0 else (if i < 27 then (if i < 26 then 0 else 1) else (if i < 28 then 0 else (if i < 29 then 0 else 1)))) else (if i < 35 then (if i < 32 then 0 else (if i < 33 then 1 else 0)) else (if i < 37 then 0 else (if i < 38 then 1 else 0))))) else (if i < 60 then (if i < 50 then (if i < 45 then (if i < 42 then (if i < 41 then 0 else 1) else 0) else (if i < 47 then (if i < 46 then 0 else 1) else (if i < 48 then 0 else (if i < 49 then 0 else 1)))) else (if i < 55 then (if i < 52 then 0 else (if i < 53 then 0 else (if i < 54 then 0 else 1))) else (if i < 57 then 0 else (if i < 58 then 1 else 0)))) else (if i < 70 then (if i < 65 then (if i < 62 then (if i < 61 then 1 else 0) else (if i < 63 then 0 else (if i < 64 then 1 else 0))) else (if i < 67 then (if i < 66 then 0 else 1) else (if i < 68 then 0 else (if i < 69 then 0 else 1)))) else (if i < 75 then (if i < 72 then 0 else (if i < 73 then 0 else (if i < 74 then 0 else 1))) else (if i < 77 then 0 else (if i < 78 then 1 else 0))))))

def v1Data (i : ℕ) : ℕ := (if i < 40 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then 1 else (if i < 3 then 1 else 0)) else (if i < 7 then (if i < 6 then 1 else 0) else (if i < 8 then 1 else (if i < 9 then 1 else 0)))) else (if i < 15 then (if i < 12 then (if i < 11 then 1 else 0) else (if i < 13 then 0 else (if i < 14 then 0 else 1))) else (if i < 17 then (if i < 16 then 0 else 1) else (if i < 18 then 1 else 0)))) else (if i < 30 then (if i < 25 then (if i < 22 then (if i < 21 then 1 else 0) else (if i < 23 then 0 else (if i < 24 then 0 else 1))) else (if i < 27 then (if i < 26 then 0 else 1) else (if i < 28 then 1 else 0))) else (if i < 35 then (if i < 32 then (if i < 31 then 1 else 0) else (if i < 33 then 0 else (if i < 34 then 1 else 0))) else (if i < 37 then 0 else (if i < 38 then 1 else (if i < 39 then 1 else 0)))))) else (if i < 60 then (if i < 50 then (if i < 45 then 0 else (if i < 47 then 0 else (if i < 48 then 1 else 0))) else (if i < 55 then (if i < 52 then (if i < 51 then 1 else 0) else (if i < 53 then 0 else (if i < 54 then 0 else 1))) else (if i < 57 then (if i < 56 then 1 else 0) else (if i < 58 then 1 else (if i < 59 then 1 else 0))))) else (if i < 70 then (if i < 65 then (if i < 62 then (if i < 61 then 0 else 1) else (if i < 63 then 0 else (if i < 64 then 0 else 1))) else (if i < 67 then 0 else (if i < 68 then 1 else 0))) else (if i < 75 then (if i < 72 then (if i < 71 then 1 else 0) else 0) else (if i < 77 then (if i < 76 then 1 else 0) else (if i < 78 then 0 else (if i < 79 then 1 else 0)))))))

def v2Data (i : ℕ) : ℕ := (if i < 40 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 2 else 1) else (if i < 3 then 2 else (if i < 4 then 1 else 0))) else 1) else (if i < 15 then (if i < 12 then (if i < 11 then 1 else 0) else (if i < 13 then 1 else (if i < 14 then 0 else 1))) else (if i < 17 then 1 else (if i < 18 then 1 else 0)))) else (if i < 30 then (if i < 25 then (if i < 22 then 1 else 0) else (if i < 27 then (if i < 26 then 0 else 1) else (if i < 28 then 1 else 0))) else (if i < 35 then (if i < 32 then 1 else (if i < 33 then 0 else 1)) else (if i < 37 then 0 else (if i < 38 then 1 else (if i < 39 then 1 else 0)))))) else (if i < 60 then (if i < 50 then (if i < 45 then 0 else (if i < 47 then 0 else (if i < 48 then 1 else (if i < 49 then 1 else 0)))) else (if i < 55 then (if i < 52 then 1 else (if i < 53 then 0 else (if i < 54 then 0 else 1))) else (if i < 57 then (if i < 56 then 1 else 0) else (if i < 58 then 1 else (if i < 59 then 1 else 0))))) else (if i < 70 then (if i < 65 then (if i < 62 then (if i < 61 then 0 else 1) else (if i < 63 then 1 else (if i < 64 then 0 else 1))) else (if i < 67 then (if i < 66 then 1 else 0) else (if i < 68 then 1 else (if i < 69 then 1 else 0)))) else (if i < 75 then (if i < 72 then 1 else 0) else (if i < 77 then 1 else (if i < 78 then 0 else 1))))))

def v3Data (i : ℕ) : ℕ := (if i < 40 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 4 else 2) else (if i < 3 then 3 else (if i < 4 then 2 else 0))) else (if i < 7 then 1 else (if i < 8 then 2 else 1))) else (if i < 15 then (if i < 12 then (if i < 11 then 2 else 0) else (if i < 13 then 0 else (if i < 14 then 0 else 1))) else (if i < 17 then (if i < 16 then 1 else 2) else (if i < 18 then 2 else 0)))) else (if i < 30 then (if i < 25 then (if i < 22 then 1 else 0) else (if i < 27 then (if i < 26 then 0 else 2) else (if i < 28 then 2 else 0))) else (if i < 35 then (if i < 32 then 1 else (if i < 33 then 0 else 1)) else (if i < 37 then 0 else (if i < 38 then 2 else (if i < 39 then 2 else 0)))))) else (if i < 60 then (if i < 50 then (if i < 45 then 0 else (if i < 47 then 0 else (if i < 48 then 1 else (if i < 49 then 1 else 0)))) else (if i < 55 then (if i < 52 then 1 else (if i < 53 then 0 else (if i < 54 then 0 else 2))) else (if i < 57 then (if i < 56 then 2 else 0) else (if i < 58 then 2 else (if i < 59 then 2 else 0))))) else (if i < 70 then (if i < 65 then (if i < 62 then (if i < 61 then 0 else 1) else (if i < 63 then 1 else (if i < 64 then 0 else 1))) else (if i < 67 then (if i < 66 then 1 else 0) else (if i < 68 then 1 else (if i < 69 then 1 else 0)))) else (if i < 75 then (if i < 72 then 1 else 0) else (if i < 77 then 1 else (if i < 78 then 0 else 1))))))

def v4Data (i : ℕ) : ℕ := (if i < 40 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 7 else 2) else (if i < 3 then 4 else (if i < 4 then 2 else 0))) else 2) else (if i < 15 then (if i < 12 then (if i < 11 then 2 else 0) else (if i < 13 then 0 else (if i < 14 then 0 else 2))) else (if i < 17 then 2 else (if i < 18 then 2 else 0)))) else (if i < 30 then (if i < 25 then (if i < 22 then 2 else 0) else (if i < 27 then (if i < 26 then 0 else 2) else (if i < 28 then 2 else 0))) else (if i < 35 then (if i < 32 then 2 else (if i < 33 then 0 else 2)) else (if i < 37 then 0 else (if i < 38 then 2 else (if i < 39 then 2 else 0)))))) else (if i < 60 then (if i < 50 then (if i < 45 then 0 else (if i < 47 then 0 else (if i < 48 then 2 else (if i < 49 then 2 else 0)))) else (if i < 55 then (if i < 52 then 2 else (if i < 53 then 0 else (if i < 54 then 0 else 2))) else (if i < 57 then (if i < 56 then 2 else 0) else (if i < 58 then 2 else (if i < 59 then 2 else 0))))) else (if i < 70 then (if i < 65 then (if i < 62 then (if i < 61 then 0 else 2) else (if i < 63 then 2 else (if i < 64 then 0 else 2))) else (if i < 67 then (if i < 66 then 2 else 0) else (if i < 68 then 2 else (if i < 69 then 2 else 0)))) else (if i < 75 then (if i < 72 then 2 else 0) else (if i < 77 then 2 else (if i < 78 then 0 else 2))))))

def v5Data (i : ℕ) : ℕ := (if i < 40 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 8 else 4) else (if i < 3 then 6 else (if i < 4 then 2 else 0))) else (if i < 7 then 2 else (if i < 8 then 4 else 2))) else (if i < 15 then (if i < 12 then (if i < 11 then 4 else 0) else (if i < 13 then 0 else (if i < 14 then 0 else 2))) else (if i < 17 then (if i < 16 then 2 else 4) else (if i < 18 then 4 else 0)))) else (if i < 30 then (if i < 25 then (if i < 22 then 2 else 0) else (if i < 27 then (if i < 26 then 0 else 4) else (if i < 28 then 4 else 0))) else (if i < 35 then (if i < 32 then 2 else (if i < 33 then 0 else 2)) else (if i < 37 then 0 else (if i < 38 then 4 else (if i < 39 then 4 else 0)))))) else (if i < 60 then (if i < 50 then (if i < 45 then 0 else (if i < 47 then 0 else (if i < 48 then 2 else (if i < 49 then 2 else 0)))) else (if i < 55 then (if i < 52 then 2 else (if i < 53 then 0 else (if i < 54 then 0 else 4))) else (if i < 57 then (if i < 56 then 4 else 0) else (if i < 58 then 4 else (if i < 59 then 4 else 0))))) else (if i < 70 then (if i < 65 then (if i < 62 then (if i < 61 then 0 else 2) else (if i < 63 then 2 else (if i < 64 then 0 else 2))) else (if i < 67 then (if i < 66 then 2 else 0) else (if i < 68 then 2 else (if i < 69 then 2 else 0)))) else (if i < 75 then (if i < 72 then 2 else 0) else (if i < 77 then 2 else (if i < 78 then 0 else 2))))))

def v6Data (i : ℕ) : ℕ := (if i < 40 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 12 else 4) else (if i < 3 then 8 else (if i < 4 then 4 else 0))) else 4) else (if i < 15 then (if i < 12 then (if i < 11 then 4 else 0) else (if i < 13 then 0 else (if i < 14 then 0 else 4))) else (if i < 17 then 4 else (if i < 18 then 4 else 0)))) else (if i < 30 then (if i < 25 then (if i < 22 then 4 else 0) else (if i < 27 then (if i < 26 then 0 else 4) else (if i < 28 then 4 else 0))) else (if i < 35 then (if i < 32 then 4 else (if i < 33 then 0 else 4)) else (if i < 37 then 0 else (if i < 38 then 4 else (if i < 39 then 4 else 0)))))) else (if i < 60 then (if i < 50 then (if i < 45 then 0 else (if i < 47 then 0 else (if i < 48 then 4 else (if i < 49 then 4 else 0)))) else (if i < 55 then (if i < 52 then 4 else (if i < 53 then 0 else (if i < 54 then 0 else 4))) else (if i < 57 then (if i < 56 then 4 else 0) else (if i < 58 then 4 else (if i < 59 then 4 else 0))))) else (if i < 70 then (if i < 65 then (if i < 62 then (if i < 61 then 0 else 4) else (if i < 63 then 4 else (if i < 64 then 0 else 4))) else (if i < 67 then (if i < 66 then 4 else 0) else (if i < 68 then 4 else (if i < 69 then 4 else 0)))) else (if i < 75 then (if i < 72 then 4 else 0) else (if i < 77 then 4 else (if i < 78 then 0 else 4))))))

def v7Data (i : ℕ) : ℕ := (if i < 40 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 16 else 8) else (if i < 3 then 12 else (if i < 4 then 4 else 0))) else (if i < 7 then 4 else (if i < 8 then 8 else 4))) else (if i < 15 then (if i < 12 then (if i < 11 then 8 else 0) else (if i < 13 then 0 else (if i < 14 then 0 else 4))) else (if i < 17 then (if i < 16 then 4 else 8) else (if i < 18 then 8 else 0)))) else (if i < 30 then (if i < 25 then (if i < 22 then 4 else 0) else (if i < 27 then (if i < 26 then 0 else 8) else (if i < 28 then 8 else 0))) else (if i < 35 then (if i < 32 then 4 else (if i < 33 then 0 else 4)) else (if i < 37 then 0 else (if i < 38 then 8 else (if i < 39 then 8 else 0)))))) else (if i < 60 then (if i < 50 then (if i < 45 then 0 else (if i < 47 then 0 else (if i < 48 then 4 else (if i < 49 then 4 else 0)))) else (if i < 55 then (if i < 52 then 4 else (if i < 53 then 0 else (if i < 54 then 0 else 8))) else (if i < 57 then (if i < 56 then 8 else 0) else (if i < 58 then 8 else (if i < 59 then 8 else 0))))) else (if i < 70 then (if i < 65 then (if i < 62 then (if i < 61 then 0 else 4) else (if i < 63 then 4 else (if i < 64 then 0 else 4))) else (if i < 67 then (if i < 66 then 4 else 0) else (if i < 68 then 4 else (if i < 69 then 4 else 0)))) else (if i < 75 then (if i < 72 then 4 else 0) else (if i < 77 then 4 else (if i < 78 then 0 else 4))))))

def valueData (n i : ℕ) : ℕ := (if n < 4 then (if n < 2 then (if n < 1 then v0Data i else v1Data i) else (if n < 3 then v2Data i else v3Data i)) else (if n < 6 then (if n < 5 then v4Data i else v5Data i) else (if n < 7 then v6Data i else v7Data i)))

def values (n : ℕ) (i : Fin 80) : ℕ := valueData n i.val

def accepted (i : Fin 80) : ℕ := v0Data i.val

def index (n : ℕ) : Fin 80 := ⟨n % 80, Nat.mod_lt _ (by decide)⟩

abbrev LocalAt (i : Fin 80) : Prop :=
  (List.finRange 5).filterMap (A263660Proof.step (state i)) = (succ i).map state ∧
  (if A263660Proof.accept (state i) then 1 else 0) = accepted i ∧
  accepted i = values 0 i ∧
  (∀ n : Fin 7, ((succ i).map (values n.val)).sum = values (n.val + 1) i) ∧
  values 7 i = 2 * values 5 i

def Block (k : ℕ) : Prop := ∀ j : Fin 8, LocalAt (index (8 * k + j.val))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
lemma blocks (k : Fin 10) : Block k.val := by
  have h0 : Block 0 := by
    unfold Block
    decide +kernel
  have h1 : Block 1 := by
    unfold Block
    decide +kernel
  have h2 : Block 2 := by
    unfold Block
    decide +kernel
  have h3 : Block 3 := by
    unfold Block
    decide +kernel
  have h4 : Block 4 := by
    unfold Block
    decide +kernel
  have h5 : Block 5 := by
    unfold Block
    decide +kernel
  have h6 : Block 6 := by
    unfold Block
    decide +kernel
  have h7 : Block 7 := by
    unfold Block
    decide +kernel
  have h8 : Block 8 := by
    unfold Block
    decide +kernel
  have h9 : Block 9 := by
    unfold Block
    decide +kernel
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9

lemma local_certificate (i : Fin 80) : LocalAt i := by
  have h := blocks ⟨i.val / 8, by omega⟩ ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
  have he : index (8 * (i.val / 8) + i.val % 8) = i := by
    apply Fin.ext
    have hi := i.isLt
    dsimp [index]
    omega
  simpa only [he] using h

lemma initial_ok : state 0 = A263660Proof.initial := by decide +kernel

lemma initial_values : values 1 0 = 1 ∧ values 2 0 = 2 ∧ values 3 0 = 4 ∧
    values 4 0 = 7 ∧ values 5 0 = 8 ∧ values 6 0 = 12 := by decide +kernel

lemma paths_values (n : ℕ) (hn : n ≤ 7) (i : Fin 80) :
    A263660Count.paths succ accepted n i = values n i :=
  A263660Count.paths_eq_values succ accepted values
    (fun i => (local_certificate i).2.2.1)
    (fun n hn i => (local_certificate i).2.2.2.1 ⟨n, hn⟩) n hn i

lemma paths_base (i : Fin 80) :
    A263660Count.paths succ accepted 7 i = 2 * A263660Count.paths succ accepted 5 i := by
  rw [paths_values 7 (by decide), paths_values 5 (by decide)]
  exact (local_certificate i).2.2.2.2

def count (n : ℕ) : ℕ := A263660Count.paths succ accepted n 0

lemma count_small : count 1 = 1 ∧ count 2 = 2 ∧ count 3 = 4 ∧
    count 4 = 7 ∧ count 5 = 8 ∧ count 6 = 12 := by
  simpa only [count, paths_values 1 (by decide), paths_values 2 (by decide),
    paths_values 3 (by decide), paths_values 4 (by decide), paths_values 5 (by decide),
    paths_values 6 (by decide)] using initial_values

lemma count_rec (n : ℕ) (hn : 5 ≤ n) : count (n + 2) = 2 * count n :=
  A263660Count.recurrence succ accepted paths_base n hn 0

end A263660Table

end

section

-- Enumerate

namespace A263660Proof

theorem wordCount_eq_count (n : ℕ) : wordCount n = A263660Table.count n :=
  wordCount_eq_paths A263660Table.state A263660Table.succ A263660Table.accepted 0
    (fun i => (A263660Table.local_certificate i).1)
    (fun i => (A263660Table.local_certificate i).2.1)
    A263660Table.initial_ok n

theorem wordCount_small : wordCount 1 = 1 ∧ wordCount 2 = 2 ∧ wordCount 3 = 4 ∧
    wordCount 4 = 7 ∧ wordCount 5 = 8 ∧ wordCount 6 = 12 := by
  simpa only [wordCount_eq_count] using A263660Table.count_small

theorem wordCount_rec (n : ℕ) (hn : 5 ≤ n) : wordCount (n + 2) = 2 * wordCount n := by
  simpa only [wordCount_eq_count] using A263660Table.count_rec n hn

end A263660Proof

end

section

-- Formula

namespace A263660Formula

open PowerSeries

variable (a : ℕ → ℕ)
variable (h1 : a 1 = 1) (h2 : a 2 = 2) (h3 : a 3 = 4)
variable (h4 : a 4 = 7) (h5 : a 5 = 8) (h6 : a 6 = 12)
variable (hs : ∀ n : ℕ, 5 ≤ n → a (n + 2) = 2 * a n)

include h5 hs in
theorem odd_tail (k : ℕ) : a (2 * k + 5) = 2 ^ (k + 3) := by
  induction k with
  | zero => simpa using h5
  | succ k ih =>
    rw [show 2 * (k + 1) + 5 = (2 * k + 5) + 2 by omega, hs _ (by omega), ih]
    rw [show k + 1 + 3 = (k + 3) + 1 by omega]
    exact (Nat.mul_comm _ _).trans (pow_succ 2 (k + 3)).symm

include h6 hs in
theorem even_tail (k : ℕ) : a (2 * k + 6) = 3 * 2 ^ (k + 2) := by
  induction k with
  | zero => simpa using h6
  | succ k ih =>
    rw [show 2 * (k + 1) + 6 = (2 * k + 6) + 2 by omega, hs _ (by omega), ih]
    have hp : 2 ^ (k + 1 + 2) = 2 ^ (k + 2) * 2 := by
      rw [show k + 1 + 2 = (k + 2) + 1 by omega]
      exact pow_succ 2 (k + 2)
    rw [hp]
    ring

include h6 hs in
theorem even_formula (n : ℕ) (hn : 4 < n) (he : Even n) :
    a n = 3 * 2 ^ (n / 2 - 1) := by
  obtain ⟨m, rfl⟩ := he
  have hm : 3 ≤ m := by omega
  have h := even_tail a h6 hs (m - 3)
  have hi : 2 * (m - 3) + 6 = m + m := by omega
  have he : m - 3 + 2 = (m + m) / 2 - 1 := by omega
  simpa only [hi, he] using h

include h5 hs in
theorem odd_formula (n : ℕ) (hn : 4 < n) (ho : Odd n) :
    a n = 2 ^ ((n - 5) / 2 + 3) := by
  obtain ⟨m, rfl⟩ := ho
  have hm : 2 ≤ m := by omega
  have h := odd_tail a h5 hs (m - 2)
  have hi : 2 * (m - 2) + 5 = 2 * m + 1 := by omega
  have he : m - 2 + 3 = (2 * m + 1 - 5) / 2 + 3 := by omega
  simpa only [hi, he] using h

include h1 h2 h3 h4 h5 h6 hs in
theorem generating_function :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 2 * X ^ 2) =
      X * (1 + X) * (1 + X - X ^ 2) * (1 + 2 * X ^ 2) := by
  let g : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℚ))
  change g * (1 - 2 * X ^ 2) = _
  have hl : g * (1 - 2 * X ^ 2) = g - (g * X ^ 2 + g * X ^ 2) := by ring
  have hr : (X : PowerSeries ℚ) * (1 + X) * (1 + X - X ^ 2) * (1 + 2 * X ^ 2) =
      X + X ^ 2 + X ^ 2 + X ^ 3 + X ^ 3 + X ^ 4 + X ^ 4 + X ^ 4 - X ^ 6 - X ^ 6 := by
    ring
  rw [hl, hr]
  ext n
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_X_pow, coeff_X, g, coeff_mk]
  by_cases hn : n ≤ 6
  · interval_cases n <;> norm_num [h1, h2, h3, h4, h5, h6]
  · have hrec := hs (n - 2) (by omega)
    have hp : n - 2 + 2 = n := by omega
    rw [hp] at hrec
    have hzero : n ≠ 0 := by omega
    have hpred : n - 2 ≠ 0 := by omega
    have hge : 2 ≤ n := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn4 : n ≠ 4 := by omega
    have hn6 : n ≠ 6 := by omega
    simp only [if_neg hzero, if_pos hge, if_neg hpred, if_neg hn1,
      if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn6, add_zero, sub_zero]
    rw [hrec]
    push_cast
    ring

include h1 h2 h3 h4 h5 h6 hs in
theorem of_recurrence :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 2 * X ^ 2) =
      X * (1 + X) * (1 + X - X ^ 2) * (1 + 2 * X ^ 2) ∧
    (∀ n : ℕ, 4 < n → Even n → a n = 3 * 2 ^ (n / 2 - 1)) ∧
    ∀ n : ℕ, 4 < n → Odd n → a n = 2 ^ ((n - 5) / 2 + 3) := by
  exact ⟨generating_function a h1 h2 h3 h4 h5 h6 hs,
    even_formula a h6 hs, odd_formula a h5 hs⟩

end A263660Formula

end


theorem OMA.solution : type_of% @OMA.S_oeis_a263660.main := by
  have hsmall : OMA.S_oeis_a263660.a 1 = 1 ∧ OMA.S_oeis_a263660.a 2 = 2 ∧
      OMA.S_oeis_a263660.a 3 = 4 ∧ OMA.S_oeis_a263660.a 4 = 7 ∧
      OMA.S_oeis_a263660.a 5 = 8 ∧ OMA.S_oeis_a263660.a 6 = 12 := by
    simpa only [A263660Proof.a_eq_wordCount] using A263660Proof.wordCount_small
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hsmall
  apply A263660Formula.of_recurrence OMA.S_oeis_a263660.a h1 h2 h3 h4 h5 h6
  intro n hn
  simpa only [A263660Proof.a_eq_wordCount] using A263660Proof.wordCount_rec n hn
