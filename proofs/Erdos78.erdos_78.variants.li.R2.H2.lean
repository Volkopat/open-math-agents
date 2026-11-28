import OMAReductions.R_Erdos78_erdos_78_variants_li_R2

-- Step Erdos78.erdos_78.variants.li.R2.H2: hypothesis H2 of reduction Erdos78.erdos_78.variants.li.R2
-- Credit: @nisbenz
-- Proves poly-time preprocessing (s, u, v) ↦ (List.replicate (Nat.log 2 s.length + 1) true, u ^^^ v)
-- via a 4-stack FinTM2, then composes with any poly-time FinTM2 for f.

open ComplexityTheory Turing Computability

namespace OMA.Erdos78LiH2

/-! ## Bounded reachability -/

def RIn {σ : Type} (step : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Prop :=
  ∃ n ≤ m, (flip bind step)^[n] (some a) = b

lemma RIn.refl {σ : Type} {step : σ → Option σ} (a : σ) : RIn step a (some a) 0 :=
  ⟨0, le_rfl, rfl⟩

lemma RIn.single {σ : Type} {step : σ → Option σ} {a b : σ} (h : step a = some b) :
    RIn step a (some b) 1 :=
  ⟨1, le_rfl, h⟩

lemma RIn.trans {σ : Type} {step : σ → Option σ} {a b : σ} {c : Option σ} {m₁ m₂ : ℕ}
    (h₁ : RIn step a (some b) m₁) (h₂ : RIn step b c m₂) : RIn step a c (m₁ + m₂) := by
  obtain ⟨n₁, hn₁, e₁⟩ := h₁
  obtain ⟨n₂, hn₂, e₂⟩ := h₂
  refine ⟨n₂ + n₁, by omega, ?_⟩
  rw [Function.iterate_add_apply, e₁, e₂]

lemma RIn.mono {σ : Type} {step : σ → Option σ} {a : σ} {b : Option σ} {m m' : ℕ}
    (h : RIn step a b m) (hm : m ≤ m') : RIn step a b m' := by
  obtain ⟨n, hn, e⟩ := h
  exact ⟨n, hn.trans hm, e⟩

lemma RIn.step_trans {σ : Type} {step : σ → Option σ} {a b : σ} {c : Option σ} {m : ℕ}
    (h₁ : step a = some b) (h₂ : RIn step b c m) : RIn step a c (m + 1) := by
  have := (RIn.single h₁).trans h₂
  rwa [Nat.add_comm] at this

lemma eval_mono (q : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : q.eval a ≤ q.eval b := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; exact Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

lemma iterate_none {σ : Type} (step : σ → Option σ) (n : ℕ) :
    (flip bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/- ## Binary encoding and bitwise XOR lemmas -/

lemma encodePosNum_eq_bits (p : PosNum) : encodePosNum p = Nat.bits (p : ℕ) := by
  induction p with
  | one => simp [encodePosNum]
  | bit1 p ih =>
    rw [encodePosNum, ih, PosNum.cast_bit1, ← two_mul, Nat.bit1_bits]
  | bit0 p ih =>
    rw [encodePosNum, ih, PosNum.cast_bit0, ← two_mul,
      Nat.bit0_bits _ (PosNum.to_nat_pos p).ne']

lemma encodeNum_eq_bits (q : Num) : encodeNum q = Nat.bits (q : ℕ) := by
  cases q with
  | zero => simp [encodeNum]
  | pos p => simpa [encodeNum] using encodePosNum_eq_bits p

lemma encodeNat_eq_bits (n : ℕ) : encodeNat n = Nat.bits n := by
  rw [encodeNat, encodeNum_eq_bits, Num.to_of_nat]

lemma max_one_encodeNat_length (n : ℕ) : max 1 (encodeNat n).length = Nat.log 2 n + 1 := by
  rw [encodeNat_eq_bits, Nat.size_eq_bits_len]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : Nat.size n ≤ Nat.log 2 n + 1 :=
      Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide) n)
    have h2 : Nat.log 2 n < Nat.size n :=
      Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn.ne')
    omega

def bump : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: bump bs

lemma bump_pos (p : PosNum) : bump (encodePosNum p) = encodePosNum p.succ := by
  induction p with
  | one => rfl
  | bit1 p ih => exact congrArg (List.cons false) ih
  | bit0 p _ => rfl

lemma bump_num (q : Num) : bump (encodeNum q) = encodeNum q.succ := by
  cases q with
  | zero => rfl
  | pos p => exact bump_pos p

lemma bump_nat (n : ℕ) : bump (encodeNat n) = encodeNat (n + 1) := by
  unfold encodeNat
  rw [Nat.cast_succ, Num.add_one]
  exact bump_num _

lemma bump_len (bs : List Bool) : (bump bs).length ≤ bs.length + 1 := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    cases b with
    | false => simp [bump]
    | true => simp [bump]; omega

lemma encodeNat_len_le (n : ℕ) : (encodeNat n).length ≤ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [← bump_nat]; exact (bump_len _).trans (by omega)

def listBits : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: false :: listBits bs

def inputList : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: true :: true :: b :: true :: false :: inputList bs

lemma bitEncode_listBool (s : List Bool) : BitstringEncoding.bitEncode s = listBits s := by
  induction s with
  | nil => rfl
  | cons b bs ih =>
    change true :: b :: false :: BitstringEncoding.bitEncode bs = true :: b :: false :: listBits bs
    rw [ih]

lemma delimit_listBits (s : List Bool) : BitstringEncoding.delimit (listBits s) = inputList s := by
  induction s with
  | nil => rfl
  | cons b bs ih => simp [listBits, inputList, BitstringEncoding.delimit, ih]

lemma inputList_len (s : List Bool) : (inputList s).length = 6 * s.length + 1 := by
  induction s with
  | nil => rfl
  | cons _ bs ih => simp [inputList, ih]; omega

def xorBits : List Bool → List Bool → List Bool
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => xor a b :: xorBits as bs

lemma xorBits_nil_left (bs : List Bool) : xorBits [] bs = bs := rfl

lemma xorBits_nil_right (as : List Bool) : xorBits as [] = as := by
  cases as <;> rfl

lemma xorBits_len (as bs : List Bool) : (xorBits as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [xorBits_nil_left]
  | cons a as ih =>
    cases bs with
    | nil => simp [xorBits_nil_right]
    | cons b bs => simp [xorBits, ih]

def stripLead : List Bool → List Bool
  | [] => []
  | false :: rest => stripLead rest
  | true :: rest => true :: rest

def trim : List Bool → List Bool
  | [] => []
  | b :: bs =>
    match trim bs with
    | [] => if b then [true] else []
    | ts => b :: ts

lemma stripLead_append_singleton (xs : List Bool) (b : Bool) :
    stripLead (xs ++ [b]) =
      match stripLead xs with
      | [] => if b then [true] else []
      | ts => ts ++ [b] := by
  induction xs with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases x with
    | false => simpa [stripLead] using ih
    | true => simp [stripLead]

lemma stripLead_reverse_eq_trim (l : List Bool) : (stripLead l.reverse).reverse = trim l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    rw [List.reverse_cons, stripLead_append_singleton]
    cases h : stripLead bs.reverse with
    | nil =>
      have ht : trim bs = [] := by rw [← ih, h]; rfl
      cases b <;> simp [trim, ht]
    | cons t ts =>
      have ht : trim bs = (t :: ts).reverse := by rw [← ih, h]
      simp [trim, ht]

lemma trim_cons_trim (b : Bool) (bs : List Bool) : trim (b :: trim bs) = trim (b :: bs) := by
  have h1 : ∀ l : List Bool, trim (trim l) = trim l := by
    intro l
    induction l with
    | nil => rfl
    | cons c cs ih =>
      simp only [trim]
      cases h : trim cs with
      | nil => cases c <;> rfl
      | cons t ts =>
        rw [h] at ih
        show trim (c :: t :: ts) = c :: t :: ts
        unfold trim
        rw [ih]
  simp only [trim, h1]

lemma trim_bits (n : ℕ) : trim (Nat.bits n) = Nat.bits n := by
  induction n using Nat.binaryRec with
  | zero => rfl
  | bit b m ih =>
    by_cases h : b = false ∧ m = 0
    · rcases h with ⟨rfl, rfl⟩
      simp [trim]
    · have hbits : Nat.bits (Nat.bit b m) = b :: Nat.bits m := by
        cases b with
        | false =>
          have hm : m ≠ 0 := fun hm => h ⟨rfl, hm⟩
          rw [Nat.bit_false, Nat.bit0_bits _ hm]
        | true =>
          rw [Nat.bit_true, Nat.bit1_bits]
      rw [hbits]
      simp only [trim, ih]
      cases hm : Nat.bits m with
      | nil =>
        cases b with
        | false =>
          have hm0 : m = 0 := by
            have := Nat.size_eq_bits_len m
            rw [hm] at this
            exact Nat.size_eq_zero.mp this.symm
          exact absurd ⟨rfl, hm0⟩ h
        | true => rfl
      | cons t ts => rfl

lemma trim_cons_bits (b : Bool) (m : ℕ) : trim (b :: Nat.bits m) = Nat.bits (Nat.bit b m) := by
  by_cases h : b = false ∧ m = 0
  · rcases h with ⟨rfl, rfl⟩
    rfl
  · have hbits : Nat.bits (Nat.bit b m) = b :: Nat.bits m := by
      cases b with
      | false =>
        have hm : m ≠ 0 := fun hm => h ⟨rfl, hm⟩
        rw [Nat.bit_false, Nat.bit0_bits _ hm]
      | true =>
        rw [Nat.bit_true, Nat.bit1_bits]
    rw [← hbits, trim_bits]

lemma bit_xor_eq (b₁ b₂ : Bool) (m₁ m₂ : ℕ) :
    Nat.bit b₁ m₁ ^^^ Nat.bit b₂ m₂ = Nat.bit (xor b₁ b₂) (m₁ ^^^ m₂) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp
  | succ i => simp [Nat.testBit_bit_succ]

lemma trim_xorBits_bits (u v : ℕ) :
    trim (xorBits (Nat.bits u) (Nat.bits v)) = Nat.bits (u ^^^ v) := by
  induction u using Nat.binaryRec generalizing v with
  | zero =>
    simp [xorBits_nil_left, trim_bits]
  | bit b₁ m₁ ih =>
    by_cases hu : b₁ = false ∧ m₁ = 0
    · rcases hu with ⟨rfl, rfl⟩
      simp [xorBits_nil_left, trim_bits]
    · have hbu : Nat.bits (Nat.bit b₁ m₁) = b₁ :: Nat.bits m₁ := by
        cases b₁ with
        | false =>
          have hm : m₁ ≠ 0 := fun hm => hu ⟨rfl, hm⟩
          rw [Nat.bit_false, Nat.bit0_bits _ hm]
        | true => rw [Nat.bit_true, Nat.bit1_bits]
      induction v using Nat.binaryRec with
      | zero =>
        simp [xorBits_nil_right, trim_bits]
      | bit b₂ m₂ _ =>
        by_cases hv : b₂ = false ∧ m₂ = 0
        · rcases hv with ⟨rfl, rfl⟩
          simp [xorBits_nil_right, trim_bits]
        · have hbv : Nat.bits (Nat.bit b₂ m₂) = b₂ :: Nat.bits m₂ := by
            cases b₂ with
            | false =>
              have hm : m₂ ≠ 0 := fun hm => hv ⟨rfl, hm⟩
              rw [Nat.bit_false, Nat.bit0_bits _ hm]
            | true => rw [Nat.bit_true, Nat.bit1_bits]
          rw [hbu, hbv, xorBits, ← trim_cons_trim, ih m₂, trim_cons_bits, bit_xor_eq]

lemma stripLead_reverse_xorBits (u v : ℕ) :
    (stripLead (xorBits (encodeNat u) (encodeNat v)).reverse).reverse = encodeNat (u ^^^ v) := by
  rw [encodeNat_eq_bits, encodeNat_eq_bits, encodeNat_eq_bits,
    stripLead_reverse_eq_trim, trim_xorBits_bits]

/- ## Preprocessor FinTM2 -/

inductive Tape | input | cnt | aux | uStk deriving DecidableEq

instance : Fintype Tape :=
  ⟨{.input, .cnt, .aux, .uStk}, fun t => by cases t <;> simp⟩

inductive Label
  | read | carry | restore | readU | revU | xorStep | strip | pourOut | emitFirst | emitRest
  deriving DecidableEq

instance : Fintype Label :=
  ⟨{.read, .carry, .restore, .readU, .revU, .xorStep, .strip, .pourOut, .emitFirst, .emitRest},
    fun l => by cases l <;> simp⟩

abbrev Reg := Option Bool

def tapes (i c a u : List Bool) : Tape → List Bool
  | .input => i
  | .cnt => c
  | .aux => a
  | .uStk => u

@[simp] lemma getI (i c a u : List Bool) : tapes i c a u .input = i := rfl
@[simp] lemma getC (i c a u : List Bool) : tapes i c a u .cnt = c := rfl
@[simp] lemma getA (i c a u : List Bool) : tapes i c a u .aux = a := rfl
@[simp] lemma getU (i c a u : List Bool) : tapes i c a u .uStk = u := rfl

@[simp] lemma updI (i c a u v : List Bool) :
    Function.update (tapes i c a u) .input v = tapes v c a u := by
  funext k; cases k <;> rfl

@[simp] lemma updC (i c a u v : List Bool) :
    Function.update (tapes i c a u) .cnt v = tapes i v a u := by
  funext k; cases k <;> rfl

@[simp] lemma updA (i c a u v : List Bool) :
    Function.update (tapes i c a u) .aux v = tapes i c v u := by
  funext k; cases k <;> rfl

@[simp] lemma updU (i c a u v : List Bool) :
    Function.update (tapes i c a u) .uStk v = tapes i c a v := by
  funext k; cases k <;> rfl

abbrev PStmt := TM2.Stmt (fun _ : Tape => Bool) Label Reg

def jump (l : Label) : PStmt := .load (fun _ => none) (.goto fun _ => l)
def skipIn (q : PStmt) : PStmt := .pop .input (fun v _ => v) q
def takeB (k : Tape) (q : PStmt) : PStmt := .pop k (fun _ x => x) q
def pushB (k : Tape) (b : Bool) (q : PStmt) : PStmt := .push k (fun _ => b) q

def pushSix (q : PStmt) : PStmt :=
  pushB .input false <|
  pushB .input true <|
  pushB .input true <|
  pushB .input true <|
  pushB .input true <|
  pushB .input true q

def prepProg : Label → PStmt
  | .read =>
    takeB .input <| .branch (fun r => r.getD false)
      (skipIn (skipIn (skipIn (skipIn (skipIn (jump .carry))))))
      (jump .readU)
  | .carry =>
    takeB .cnt <| .branch (fun r => r.getD false)
      (pushB .aux false (jump .carry))
      (pushB .cnt true (jump .restore))
  | .restore =>
    takeB .aux <| .branch Option.isSome
      (pushB .cnt false (jump .restore))
      (jump .read)
  | .readU =>
    takeB .input <| .branch (fun r => r.getD false)
      (takeB .input <| .push .aux (fun r => r.getD false) (jump .readU))
      (jump .revU)
  | .revU =>
    takeB .aux <| .branch Option.isSome
      (.push .uStk (fun r => r.getD false) (jump .revU))
      (jump .xorStep)
  | .xorStep =>
    takeB .uStk <| .branch Option.isSome
      (.branch (fun r => r.getD false)
        (takeB .input <| .push .aux (fun r => !(r.getD false)) (jump .xorStep))
        (takeB .input <| .push .aux (fun r => r.getD false) (jump .xorStep)))
      (takeB .input <| .branch Option.isSome
        (.push .aux (fun r => r.getD false) (jump .xorStep))
        (jump .strip))
  | .strip =>
    takeB .aux <| .branch Option.isSome
      (.branch (fun r => r.getD false)
        (pushB .input true (jump .pourOut))
        (jump .strip))
      (pushB .input false (jump .emitFirst))
  | .pourOut =>
    takeB .aux <| .branch Option.isSome
      (.push .input (fun r => r.getD false) (jump .pourOut))
      (pushB .input false (jump .emitFirst))
  | .emitFirst =>
    takeB .cnt <| .branch Option.isSome
      (pushSix (jump .emitRest))
      (pushSix (.load (fun _ => none) .halt))
  | .emitRest =>
    takeB .cnt <| .branch Option.isSome
      (pushSix (jump .emitRest))
      (.load (fun _ => none) .halt)

def prepTM : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .input
  Γ _ := Bool
  Λ := Label
  main := .read
  σ := Reg
  initialState := none
  m := prepProg

def pcfg (l : Option Label) (i c a u : List Bool) : prepTM.Cfg :=
  ⟨l, none, tapes i c a u⟩

lemma restore_run (i acc : List Bool) (m : ℕ) :
    RIn prepTM.step (pcfg (some .restore) i acc (List.replicate m false) [])
      (some (pcfg (some .read) i (List.replicate m false ++ acc) [] [])) (m + 1) := by
  induction m generalizing acc with
  | zero =>
    apply RIn.single
    show some (TM2.stepAux (prepProg .restore) none (tapes i acc [] [])) = _
    simp [prepProg, takeB, jump, pcfg]; rfl
  | succ m ih =>
    have heq : List.replicate m false ++ false :: acc = List.replicate (m + 1) false ++ acc := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    rw [← heq]
    refine RIn.step_trans ?_ (ih (false :: acc))
    show some (TM2.stepAux (prepProg .restore) none
      (tapes i acc (List.replicate (m + 1) false) [])) = _
    simp [prepProg, takeB, pushB, jump, pcfg, List.replicate_succ]; rfl

lemma carry_run (i bs : List Bool) (m : ℕ) :
    RIn prepTM.step (pcfg (some .carry) i bs (List.replicate m false) [])
      (some (pcfg (some .read) i (List.replicate m false ++ bump bs) [] []))
      (2 * bs.length + m + 2) := by
  induction bs generalizing m with
  | nil =>
    have hstep : prepTM.step (pcfg (some .carry) i [] (List.replicate m false) []) =
        some (pcfg (some .restore) i [true] (List.replicate m false) []) := by
      show some (TM2.stepAux (prepProg .carry) none (tapes i [] (List.replicate m false) [])) = _
      simp [prepProg, takeB, pushB, jump, pcfg]; rfl
    exact (RIn.step_trans hstep (restore_run i [true] m)).mono (by omega)
  | cons b bs ih =>
    cases b with
    | false =>
      have hstep : prepTM.step (pcfg (some .carry) i (false :: bs) (List.replicate m false) []) =
          some (pcfg (some .restore) i (true :: bs) (List.replicate m false) []) := by
        show some (TM2.stepAux (prepProg .carry) none
          (tapes i (false :: bs) (List.replicate m false) [])) = _
        simp [prepProg, takeB, pushB, jump, pcfg]; rfl
      exact (RIn.step_trans hstep (restore_run i (true :: bs) m)).mono (by simp)
    | true =>
      have hstep : prepTM.step (pcfg (some .carry) i (true :: bs) (List.replicate m false) []) =
          some (pcfg (some .carry) i bs (List.replicate (m + 1) false) []) := by
        show some (TM2.stepAux (prepProg .carry) none
          (tapes i (true :: bs) (List.replicate m false) [])) = _
        simp [prepProg, takeB, pushB, jump, pcfg, List.replicate_succ]; rfl
      have h := RIn.step_trans hstep (ih (m + 1))
      rw [List.replicate_succ', List.append_assoc, List.singleton_append] at h
      exact h.mono (by simp; omega)

lemma read_run (s rest : List Bool) (n : ℕ) :
    RIn prepTM.step (pcfg (some .read) (inputList s ++ rest) (encodeNat n) [] [])
      (some (pcfg (some .readU) rest (encodeNat (n + s.length)) [] []))
      (s.length * (2 * (n + s.length) + 4) + 1) := by
  induction s generalizing n with
  | nil =>
    simp only [List.length_nil, Nat.add_zero, Nat.zero_mul, Nat.zero_add]
    apply RIn.single
    show some (TM2.stepAux (prepProg .read) none (tapes (inputList [] ++ rest) (encodeNat n) [] [])) = _
    simp [prepProg, inputList, takeB, jump, pcfg]; rfl
  | cons b bs ih =>
    have hstep : prepTM.step (pcfg (some .read) (inputList (b :: bs) ++ rest) (encodeNat n) [] []) =
        some (pcfg (some .carry) (inputList bs ++ rest) (encodeNat n) [] []) := by
      show some (TM2.stepAux (prepProg .read) none
        (tapes (inputList (b :: bs) ++ rest) (encodeNat n) [] [])) = _
      simp [prepProg, inputList, takeB, skipIn, jump, pcfg]; rfl
    have hc := carry_run (inputList bs ++ rest) (encodeNat n) 0
    simp only [List.replicate_zero, List.nil_append, Nat.add_zero, bump_nat] at hc
    have h := (RIn.step_trans hstep hc).trans (ih (n + 1))
    rw [show n + 1 + bs.length = n + (b :: bs).length by simp; omega] at h
    refine h.mono ?_
    simp only [List.length_cons]
    nlinarith [encodeNat_len_le n]

lemma readU_run (us rest c acc : List Bool) :
    RIn prepTM.step (pcfg (some .readU) (BitstringEncoding.delimit us ++ rest) c acc [])
      (some (pcfg (some .revU) rest c (us.reverse ++ acc) []))
      (us.length + 1) := by
  induction us generalizing acc with
  | nil =>
    apply RIn.single
    show some (TM2.stepAux (prepProg .readU) none
      (tapes (BitstringEncoding.delimit [] ++ rest) c acc [])) = _
    simp [prepProg, BitstringEncoding.delimit, takeB, jump, pcfg]; rfl
  | cons b bs ih =>
    have hstep : prepTM.step
        (pcfg (some .readU) (BitstringEncoding.delimit (b :: bs) ++ rest) c acc []) =
        some (pcfg (some .readU) (BitstringEncoding.delimit bs ++ rest) c (b :: acc) []) := by
      show some (TM2.stepAux (prepProg .readU) none
        (tapes (BitstringEncoding.delimit (b :: bs) ++ rest) c acc [])) = _
      simp [prepProg, BitstringEncoding.delimit, takeB, jump, pcfg]; rfl
    have h := RIn.step_trans hstep (ih (b :: acc))
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h

lemma revU_run (vs c a acc : List Bool) :
    RIn prepTM.step (pcfg (some .revU) vs c a acc)
      (some (pcfg (some .xorStep) vs c [] (a.reverse ++ acc)))
      (a.length + 1) := by
  induction a generalizing acc with
  | nil =>
    apply RIn.single
    show some (TM2.stepAux (prepProg .revU) none (tapes vs c [] acc)) = _
    simp [prepProg, takeB, jump, pcfg]; rfl
  | cons b bs ih =>
    have hstep : prepTM.step (pcfg (some .revU) vs c (b :: bs) acc) =
        some (pcfg (some .revU) vs c bs (b :: acc)) := by
      show some (TM2.stepAux (prepProg .revU) none (tapes vs c (b :: bs) acc)) = _
      simp [prepProg, takeB, jump, pcfg]; rfl
    have h := RIn.step_trans hstep (ih (b :: acc))
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h

lemma xorStep_run (us vs c acc : List Bool) :
    RIn prepTM.step (pcfg (some .xorStep) vs c acc us)
      (some (pcfg (some .strip) [] c ((xorBits us vs).reverse ++ acc) []))
      ((xorBits us vs).length + 1) := by
  induction us generalizing vs acc with
  | nil =>
    induction vs generalizing acc with
    | nil =>
      apply RIn.single
      show some (TM2.stepAux (prepProg .xorStep) none (tapes [] c acc [])) = _
      simp [prepProg, takeB, jump, pcfg]; rfl
    | cons v vs ihv =>
      have hstep : prepTM.step (pcfg (some .xorStep) (v :: vs) c acc []) =
          some (pcfg (some .xorStep) vs c (v :: acc) []) := by
        show some (TM2.stepAux (prepProg .xorStep) none (tapes (v :: vs) c acc [])) = _
        simp [prepProg, takeB, jump, pcfg]; rfl
      have h := RIn.step_trans hstep (ihv (v :: acc))
      simpa [xorBits, List.reverse_cons, List.append_assoc, Nat.add_comm] using h
  | cons u us ihu =>
    cases vs with
    | nil =>
      have hstep : prepTM.step (pcfg (some .xorStep) [] c acc (u :: us)) =
          some (pcfg (some .xorStep) [] c (u :: acc) us) := by
        show some (TM2.stepAux (prepProg .xorStep) none (tapes [] c acc (u :: us))) = _
        cases u <;> (simp [prepProg, takeB, jump, pcfg]; rfl)
      have h := RIn.step_trans hstep (ihu [] (u :: acc))
      simpa [xorBits, xorBits_nil_right, List.reverse_cons, List.append_assoc, Nat.add_comm] using h
    | cons v vs =>
      have hstep : prepTM.step (pcfg (some .xorStep) (v :: vs) c acc (u :: us)) =
          some (pcfg (some .xorStep) vs c (xor u v :: acc) us) := by
        show some (TM2.stepAux (prepProg .xorStep) none (tapes (v :: vs) c acc (u :: us))) = _
        cases u <;> cases v <;> (simp [prepProg, takeB, jump, pcfg]; rfl)
      have h := RIn.step_trans hstep (ihu vs (xor u v :: acc))
      simpa [xorBits, List.reverse_cons, List.append_assoc, Nat.add_comm] using h

lemma pourOut_run (acc c a : List Bool) :
    RIn prepTM.step (pcfg (some .pourOut) acc c a [])
      (some (pcfg (some .emitFirst) (false :: (a.reverse ++ acc)) c [] []))
      (a.length + 1) := by
  induction a generalizing acc with
  | nil =>
    apply RIn.single
    show some (TM2.stepAux (prepProg .pourOut) none (tapes acc c [] [])) = _
    simp [prepProg, takeB, pushB, jump, pcfg]; rfl
  | cons b bs ih =>
    have hstep : prepTM.step (pcfg (some .pourOut) acc c (b :: bs) []) =
        some (pcfg (some .pourOut) (b :: acc) c bs []) := by
      show some (TM2.stepAux (prepProg .pourOut) none (tapes acc c (b :: bs) [])) = _
      simp [prepProg, takeB, jump, pcfg]; rfl
    have h := RIn.step_trans hstep (ih (b :: acc))
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using h

lemma strip_run (c a : List Bool) :
    RIn prepTM.step (pcfg (some .strip) [] c a [])
      (some (pcfg (some .emitFirst) (false :: (stripLead a).reverse) c [] []))
      (a.length + 1) := by
  induction a with
  | nil =>
    apply RIn.single
    show some (TM2.stepAux (prepProg .strip) none (tapes [] c [] [])) = _
    simp [prepProg, takeB, pushB, jump, pcfg, stripLead]; rfl
  | cons b bs ih =>
    cases b with
    | false =>
      have hstep : prepTM.step (pcfg (some .strip) [] c (false :: bs) []) =
          some (pcfg (some .strip) [] c bs []) := by
        show some (TM2.stepAux (prepProg .strip) none (tapes [] c (false :: bs) [])) = _
        simp [prepProg, takeB, jump, pcfg]; rfl
      simpa [stripLead] using RIn.step_trans hstep ih
    | true =>
      have hstep : prepTM.step (pcfg (some .strip) [] c (true :: bs) []) =
          some (pcfg (some .pourOut) [true] c bs []) := by
        show some (TM2.stepAux (prepProg .strip) none (tapes [] c (true :: bs) [])) = _
        simp [prepProg, takeB, pushB, jump, pcfg]; rfl
      have h := RIn.step_trans hstep (pourOut_run [true] c bs)
      simpa [stripLead, List.reverse_cons] using h

lemma emitRest_run (k : ℕ) (c rest : List Bool) :
    RIn prepTM.step (pcfg (some .emitRest) (inputList (List.replicate k true) ++ rest) c [] [])
      (some (pcfg none (inputList (List.replicate (k + c.length) true) ++ rest) [] [] []))
      (c.length + 1) := by
  induction c generalizing k with
  | nil =>
    apply RIn.single
    show some (TM2.stepAux (prepProg .emitRest) none
      (tapes (inputList (List.replicate k true) ++ rest) [] [] [])) = _
    simp [prepProg, takeB, pcfg]; rfl
  | cons b cs ih =>
    have hstep : prepTM.step
        (pcfg (some .emitRest) (inputList (List.replicate k true) ++ rest) (b :: cs) [] []) =
        some (pcfg (some .emitRest) (inputList (List.replicate (k + 1) true) ++ rest) cs [] []) := by
      show some (TM2.stepAux (prepProg .emitRest) none
        (tapes (inputList (List.replicate k true) ++ rest) (b :: cs) [] [])) = _
      simp [prepProg, takeB, pushSix, pushB, jump, pcfg, List.replicate_succ, inputList]; rfl
    have h := RIn.step_trans hstep (ih (k + 1))
    rw [show k + 1 + cs.length = k + (b :: cs).length by simp; omega] at h
    exact h

lemma emitFirst_run (c rest : List Bool) :
    RIn prepTM.step (pcfg (some .emitFirst) (false :: rest) c [] [])
      (some (pcfg none (inputList (List.replicate (max 1 c.length) true) ++ rest) [] [] []))
      (c.length + 1) := by
  cases c with
  | nil =>
    apply RIn.single
    show some (TM2.stepAux (prepProg .emitFirst) none (tapes (false :: rest) [] [] [])) = _
    simp [prepProg, takeB, pushSix, pushB, pcfg, inputList]; rfl
  | cons b cs =>
    have hstep : prepTM.step (pcfg (some .emitFirst) (false :: rest) (b :: cs) [] []) =
        some (pcfg (some .emitRest) (inputList (List.replicate 1 true) ++ rest) cs [] []) := by
      show some (TM2.stepAux (prepProg .emitFirst) none (tapes (false :: rest) (b :: cs) [] [])) = _
      simp [prepProg, takeB, pushSix, pushB, jump, pcfg, inputList]; rfl
    have h := RIn.step_trans hstep (emitRest_run 1 cs rest)
    have hmax : max 1 (b :: cs).length = 1 + cs.length := by simp; omega
    rw [hmax]
    exact h

lemma initList_prepTM (l : List Bool) : initList prepTM l = pcfg (some .read) l [] [] [] := by
  simp only [initList, pcfg]
  congr 1
  funext k
  cases k <;> rfl

lemma haltList_prepTM (l : List Bool) : haltList prepTM l = pcfg none l [] [] [] := by
  simp only [haltList, pcfg]
  congr 1
  funext k
  cases k <;> rfl

def prepFun (x : List Bool × ℕ × ℕ) : List Bool × ℕ :=
  (List.replicate (Nat.log 2 x.1.length + 1) true, x.2.1 ^^^ x.2.2)

theorem isPolyTime_prepFun : IsPolyTime prepFun := by
  refine ⟨{
    tm := prepTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := (Polynomial.X + Polynomial.C 10) ^ 2
    outputsFun := ?_ }⟩
  rintro ⟨s, u, v⟩
  let us := encodeNat u
  let vs := encodeNat v
  let inp := inputList s ++ (BitstringEncoding.delimit us ++ vs)
  let out := inputList (List.replicate (Nat.log 2 s.length + 1) true) ++ encodeNat (u ^^^ v)
  have henc : BitstringEncoding.bitEncode (s, u, v) = inp := by
    change BitstringEncoding.delimit (BitstringEncoding.bitEncode s) ++
      (BitstringEncoding.delimit (encodeNat u) ++ encodeNat v) = inp
    rw [bitEncode_listBool, delimit_listBits]
  have hout : BitstringEncoding.bitEncode (prepFun (s, u, v)) = out := by
    change BitstringEncoding.delimit
      (BitstringEncoding.bitEncode (List.replicate (Nat.log 2 s.length + 1) true)) ++
      encodeNat (u ^^^ v) = out
    rw [bitEncode_listBool, delimit_listBits]
  have h1 := read_run s (BitstringEncoding.delimit us ++ vs) 0
  simp only [Nat.zero_add] at h1
  have h2 := readU_run us vs (encodeNat s.length) []
  simp only [List.append_nil] at h2
  have h3 := revU_run vs (encodeNat s.length) us.reverse []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h3
  have h4 := xorStep_run us vs (encodeNat s.length) []
  simp only [List.append_nil] at h4
  have h5 := strip_run (encodeNat s.length) (xorBits us vs).reverse
  simp only [List.length_reverse] at h5
  rw [show (stripLead (xorBits us vs).reverse).reverse = encodeNat (u ^^^ v) from
    stripLead_reverse_xorBits u v] at h5
  have h6 := emitFirst_run (encodeNat s.length) (encodeNat (u ^^^ v))
  rw [max_one_encodeNat_length] at h6
  have hall := ((((h1.trans h2).trans h3).trans h4).trans h5).trans h6
  have hlen : inp.length = 6 * s.length + 1 + (2 * us.length + 1 + vs.length) := by
    simp [inp, inputList_len, BitstringEncoding.length_delimit]
  have hbound :
      s.length * (2 * s.length + 4) + 1 + (us.length + 1) + (us.length + 1) +
        ((xorBits us vs).length + 1) + ((xorBits us vs).length + 1) +
        ((encodeNat s.length).length + 1) ≤
      ((Polynomial.X + Polynomial.C 10) ^ 2).eval (BitstringEncoding.bitEncode (s, u, v)).length := by
    rw [henc, hlen, xorBits_len]
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    have hcl := encodeNat_len_le s.length
    have hmax : max us.length vs.length ≤ us.length + vs.length := by omega
    nlinarith
  have hall' : RIn prepTM.step (initList prepTM inp) (some (haltList prepTM out))
      (((Polynomial.X + Polynomial.C 10) ^ 2).eval
        ((BitstringEncoding.toEncoding (α := List Bool × ℕ × ℕ)).encode (s, u, v)).length) := by
    rw [initList_prepTM, haltList_prepTM]
    exact hall.mono hbound
  have hinMap : List.map ((Equiv.refl Bool : prepTM.Γ prepTM.k₀ ≃ Bool).invFun)
      ((BitstringEncoding.toEncoding (α := List Bool × ℕ × ℕ)).encode (s, u, v)) = inp := by
    change List.map id (BitstringEncoding.bitEncode (s, u, v)) = inp
    rw [List.map_id, henc]
  have houtMap : List.map ((Equiv.refl Bool : prepTM.Γ prepTM.k₁ ≃ Bool).invFun)
      ((BitstringEncoding.toEncoding (α := List Bool × ℕ)).encode (prepFun (s, u, v))) = out := by
    change List.map id (BitstringEncoding.bitEncode (prepFun (s, u, v))) = out
    rw [List.map_id, hout]
  have key : ∀ l l' : List Bool, l = inp → l' = out →
      TM2OutputsInTime prepTM l (some l')
        (((Polynomial.X + Polynomial.C 10) ^ 2).eval
          ((BitstringEncoding.toEncoding (α := List Bool × ℕ × ℕ)).encode (s, u, v)).length) := by
    rintro l l' rfl rfl
    exact Classical.choice (by
      obtain ⟨n, hle, he⟩ := hall'
      exact ⟨⟨⟨n, he⟩, hle⟩⟩)
  exact key _ _ hinMap houtMap

/- ## General FinTM2 composition in polynomial time -/

def pushCount {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushCount q + 1
  | .peek _ _ q => pushCount q
  | .pop _ _ q => pushCount q
  | .load _ q => pushCount q
  | .branch _ q₁ q₂ => pushCount q₁ + pushCount q₂
  | .goto _ => 0
  | .halt => 0

lemma stepAux_len {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushCount q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux, pushCount]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h; simp only [Function.update_self, List.length_cons]; omega
    · rw [Function.update_of_ne h]; omega
  | peek _ _ _ ih => exact ih _ _
  | pop k' _ _ ih =>
    simp only [TM2.stepAux, pushCount]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h; simp only [Function.update_self, List.length_tail]; omega
    · rw [Function.update_of_ne h]
  | load _ _ ih => exact ih _ _
  | branch f _ _ ih₁ ih₂ =>
    simp only [TM2.stepAux, pushCount]
    cases f v
    · exact (ih₂ v S).trans (by omega)
    · exact (ih₁ v S).trans (by omega)
  | goto _ => simp [TM2.stepAux, pushCount]
  | halt => simp [TM2.stepAux, pushCount]

lemma exists_pushBound (M : FinTM2) : ∃ B : ℕ, ∀ l, pushCount (M.m l) ≤ B := by
  let _ : Fintype M.Λ := M.ΛFin
  exact ⟨Finset.univ.sup (fun l => pushCount (M.m l)),
    fun l => Finset.le_sup (f := fun l => pushCount (M.m l)) (Finset.mem_univ l)⟩

lemma step_len (M : FinTM2) {B : ℕ} (hB : ∀ l, pushCount (M.m l) ≤ B)
    {c c' : TM2.Cfg M.Γ M.Λ M.σ} (h : M.step c = some c') (k : M.K) :
    (c'.stk k).length ≤ (c.stk k).length + B := by
  rcases c with ⟨_ | l, v, S⟩
  · exact absurd h (by simp [FinTM2.step, TM2.step])
  · have h' : some (TM2.stepAux (M.m l) v S) = some c' := h
    injection h' with h'
    subst h'
    exact (stepAux_len (M.m l) v S k).trans (Nat.add_le_add_left (hB l) _)

lemma iterate_len (M : FinTM2) {B : ℕ} (hB : ∀ l, pushCount (M.m l) ≤ B) (n : ℕ)
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : (flip bind M.step)^[n] (some c) = some c') (k : M.K) :
    (c'.stk k).length ≤ (c.stk k).length + n * B := by
  induction n generalizing c with
  | zero =>
    have h' : some c = some c' := h
    injection h' with h'
    subst h'
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    change (flip bind M.step)^[n] (M.step c) = some c' at h
    cases hs : M.step c with
    | none =>
      rw [hs, iterate_none] at h
      exact absurd h (by simp)
    | some c₁ =>
      rw [hs] at h
      have h1 := ih c₁ h
      have h2 := step_len M hB hs k
      rw [Nat.succ_mul]
      omega

lemma initList_stk_len (M : FinTM2) (s : List (M.Γ M.k₀)) (k : M.K) :
    ((initList M s).stk k).length ≤ s.length := by
  by_cases h : k = M.k₀
  · subst h; simp [initList]
  · simp [initList, h]

lemma out_len (M : FinTM2) {B : ℕ} (hB : ∀ l, pushCount (M.m l) ≤ B)
    {s : List (M.Γ M.k₀)} {out : List (M.Γ M.k₁)} {T : ℕ}
    (h : TM2OutputsInTime M s (some out) T) : out.length ≤ s.length + T * B := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  have h1 := iterate_len M hB n (initList M s) (haltList M out) hn M.k₁
  have hhalt : (haltList M out).stk M.k₁ = out := by simp [haltList]
  have hinit := initList_stk_len M s M.k₁
  have h3 : n * B ≤ T * B := Nat.mul_le_mul_right B hle
  rw [hhalt] at h1
  omega

section Comp
variable (M N : FinTM2) (eo : M.Γ M.k₁ ≃ Bool) (ei : N.Γ N.k₀ ≃ Bool)

abbrev CK : Type := M.K ⊕ (N.K ⊕ Unit)
abbrev CL : Type := M.Λ ⊕ (N.Λ ⊕ Bool)
abbrev CV : Type := M.σ × N.σ × Option Bool

abbrev CG : CK M N → Type := fun k =>
  Sum.casesOn (motive := fun _ => Type) k M.Γ
    (fun k' => Sum.casesOn (motive := fun _ => Type) k' N.Γ (fun _ => Bool))

def liftM : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (CG M N) (CL M N) (CV M N)
  | .push k f q => .push (Sum.inl k) (fun v => f v.1) (liftM q)
  | .peek k f q => .peek (Sum.inl k) (fun v o => (f v.1 o, v.2)) (liftM q)
  | .pop k f q => .pop (Sum.inl k) (fun v o => (f v.1 o, v.2)) (liftM q)
  | .load a q => .load (fun v => (a v.1, v.2)) (liftM q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (liftM q₁) (liftM q₂)
  | .goto f => .goto (fun v => Sum.inl (f v.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr false))

def liftN : TM2.Stmt N.Γ N.Λ N.σ → TM2.Stmt (CG M N) (CL M N) (CV M N)
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun v => f v.2.1) (liftN q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftN q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftN q)
  | .load a q => .load (fun v => (v.1, a v.2.1, v.2.2)) (liftN q)
  | .branch f q₁ q₂ => .branch (fun v => f v.2.1) (liftN q₁) (liftN q₂)
  | .goto f => .goto (fun v => Sum.inr (Sum.inl (f v.2.1)))
  | .halt => .halt

def cprog : CL M N → TM2.Stmt (CG M N) (CL M N) (CV M N)
  | Sum.inl l => liftM M N (M.m l)
  | Sum.inr (Sum.inl l) => liftN M N (N.m l)
  | Sum.inr (Sum.inr false) =>
    .pop (Sum.inl M.k₁) (fun v (o : Option (M.Γ M.k₁)) => (v.1, v.2.1, o.map eo)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inr (Sum.inr ())) (fun v => v.2.2.getD false) <|
          .goto fun _ => Sum.inr (Sum.inr false))
        (.goto fun _ => Sum.inr (Sum.inr true))
  | Sum.inr (Sum.inr true) =>
    .pop (Sum.inr (Sum.inr ())) (fun v (o : Option Bool) => (v.1, v.2.1, o)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inr (Sum.inl N.k₀)) (fun v => ei.symm (v.2.2.getD false)) <|
          .goto fun _ => Sum.inr (Sum.inr true))
        (.goto fun _ => Sum.inr (Sum.inl N.main))

def Cmp : FinTM2 :=
  letI := M.kFin
  letI := N.kFin
  letI := M.ΛFin
  letI := N.ΛFin
  letI := M.σFin
  letI := N.σFin
  { K := CK M N
    k₀ := Sum.inl M.k₀
    k₁ := Sum.inr (Sum.inl N.k₁)
    Γ := CG M N
    Λ := CL M N
    main := Sum.inl M.main
    σ := CV M N
    initialState := (M.initialState, N.initialState, none)
    Γk₀Fin := M.Γk₀Fin
    m := cprog M N eo ei }

def mkStk (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool) :
    ∀ k : CK M N, List (CG M N k)
  | Sum.inl k => SM k
  | Sum.inr (Sum.inl k) => SN k
  | Sum.inr (Sum.inr _) => a

variable {M N eo ei}

lemma upd_M (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool) (k : M.K)
    (v : List (CG M N (Sum.inl k))) :
    Function.update (mkStk M N SM SN a) (Sum.inl k) v =
      mkStk M N (Function.update SM k v) SN a := by
  funext k'
  rcases k' with k' | k' | k'
  · by_cases h : k' = k
    · subst h; simp [Function.update, mkStk]
    · simp [Function.update, mkStk, h]
  · simp [Function.update, mkStk]
  · simp [Function.update, mkStk]

lemma upd_N (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool) (k : N.K)
    (v : List (CG M N (Sum.inr (Sum.inl k)))) :
    Function.update (mkStk M N SM SN a) (Sum.inr (Sum.inl k)) v =
      mkStk M N SM (Function.update SN k v) a := by
  funext k'
  rcases k' with k' | k' | k'
  · simp [Function.update, mkStk]
  · by_cases h : k' = k
    · subst h; simp [Function.update, mkStk]
    · simp [Function.update, mkStk, h]
  · simp [Function.update, mkStk]

lemma upd_A (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool)
    (v : List (CG M N (Sum.inr (Sum.inr ())))) :
    Function.update (mkStk M N SM SN a) (Sum.inr (Sum.inr ())) v = mkStk M N SM SN v := by
  funext k'
  rcases k' with k' | k' | k' <;> simp [Function.update, mkStk]

def liftCfgM (c : TM2.Cfg M.Γ M.Λ M.σ) : (Cmp M N eo ei).Cfg :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr false)) Sum.inl), (c.var, N.initialState, none),
    mkStk M N c.stk (fun _ => []) []⟩

def liftCfgN (c : TM2.Cfg N.Γ N.Λ N.σ) : (Cmp M N eo ei).Cfg :=
  ⟨c.l.map (fun l => Sum.inr (Sum.inl l)), (M.initialState, c.var, none),
    mkStk M N (fun _ => []) c.stk []⟩

def tcfg (b : Bool) (o : Option Bool) (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k))
    (a : List Bool) : (Cmp M N eo ei).Cfg :=
  ⟨some (Sum.inr (Sum.inr b)), (M.initialState, N.initialState, o), mkStk M N SM SN a⟩

lemma stepAux_liftM (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (liftM M N q) (v, N.initialState, none) (mkStk M N S (fun _ => []) []) =
      liftCfgM (eo := eo) (ei := ei) (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push _ _ _ ih => simp only [liftM, TM2.stepAux]; rw [upd_M]; exact ih _ _
  | peek _ _ _ ih => exact ih _ _
  | pop _ _ _ ih => simp only [liftM, TM2.stepAux]; rw [upd_M]; exact ih _ _
  | load _ _ ih => exact ih _ _
  | branch f _ _ ih₁ ih₂ => simp only [liftM, TM2.stepAux, ih₁, ih₂]; cases f v <;> rfl
  | goto _ => rfl
  | halt => rfl

lemma step_liftM {c c' : TM2.Cfg M.Γ M.Λ M.σ} (h : M.step c = some c') :
    (Cmp M N eo ei).step (liftCfgM c) = some (liftCfgM c') := by
  rcases c with ⟨_ | l, v, S⟩
  · exact absurd h (by simp [FinTM2.step, TM2.step])
  · have h' : some (TM2.stepAux (M.m l) v S) = some c' := h
    injection h' with h'
    subst h'
    show some (TM2.stepAux (liftM M N (M.m l)) (v, N.initialState, none)
      (mkStk M N S (fun _ => []) [])) = _
    exact congrArg some (stepAux_liftM (eo := eo) (ei := ei) (M.m l) v S)

lemma iterate_liftM (n : ℕ) (c c' : TM2.Cfg M.Γ M.Λ M.σ)
    (h : (flip bind M.step)^[n] (some c) = some c') :
    (flip bind (Cmp M N eo ei).step)^[n] (some (liftCfgM c)) = some (liftCfgM c') := by
  induction n generalizing c with
  | zero =>
    have h' : some c = some c' := h
    injection h' with h'
    subst h'
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    change (flip bind M.step)^[n] (M.step c) = some c' at h
    change (flip bind (Cmp M N eo ei).step)^[n] ((Cmp M N eo ei).step (liftCfgM c)) = _
    cases hs : M.step c with
    | none => rw [hs, iterate_none] at h; exact absurd h (by simp)
    | some c₁ => rw [hs] at h; rw [step_liftM hs]; exact ih c₁ h

lemma stepAux_liftN (q : TM2.Stmt N.Γ N.Λ N.σ) (v : N.σ) (S : ∀ k, List (N.Γ k)) :
    TM2.stepAux (liftN M N q) (M.initialState, v, none) (mkStk M N (fun _ => []) S []) =
      liftCfgN (eo := eo) (ei := ei) (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push _ _ _ ih => simp only [liftN, TM2.stepAux]; rw [upd_N]; exact ih _ _
  | peek _ _ _ ih => exact ih _ _
  | pop _ _ _ ih => simp only [liftN, TM2.stepAux]; rw [upd_N]; exact ih _ _
  | load _ _ ih => exact ih _ _
  | branch f _ _ ih₁ ih₂ => simp only [liftN, TM2.stepAux, ih₁, ih₂]; cases f v <;> rfl
  | goto _ => rfl
  | halt => rfl

lemma step_liftN (c : TM2.Cfg N.Γ N.Λ N.σ) :
    (Cmp M N eo ei).step (liftCfgN c) = (N.step c).map liftCfgN := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · show some (TM2.stepAux (liftN M N (N.m l)) (M.initialState, v, none)
      (mkStk M N (fun _ => []) S [])) = _
    rw [stepAux_liftN]
    rfl

lemma iterate_liftN (n : ℕ) (o : Option (TM2.Cfg N.Γ N.Λ N.σ)) :
    (flip bind (Cmp M N eo ei).step)^[n] (o.map liftCfgN) =
      ((flip bind N.step)^[n] o).map liftCfgN := by
  have hs : Function.Semiconj (Option.map (liftCfgN (M := M) (N := N) (eo := eo) (ei := ei)))
      (flip bind N.step) (flip bind (Cmp M N eo ei).step) := by
    intro o
    rcases o with _ | c
    · rfl
    · show (N.step c).map liftCfgN = (Cmp M N eo ei).step (liftCfgN c)
      rw [step_liftN]
  exact ((hs.iterate_right n) o).symm

lemma mv1_run (s : List (M.Γ M.k₁)) (o : Option Bool)
    (SM : ∀ k, List (M.Γ k)) (SN : ∀ k, List (N.Γ k)) (a : List Bool) (h : SM M.k₁ = s) :
    RIn (Cmp M N eo ei).step (tcfg false o SM SN a)
      (some (tcfg true none (Function.update SM M.k₁ []) SN ((s.map eo).reverse ++ a)))
      (s.length + 1) := by
  induction s generalizing o SM a with
  | nil =>
    apply RIn.single
    show some (TM2.stepAux (cprog M N eo ei (Sum.inr (Sum.inr false)))
      (M.initialState, N.initialState, o) (mkStk M N SM SN a)) = _
    simp [cprog, TM2.stepAux, mkStk, upd_M, upd_A, tcfg, h]
    rfl
  | cons c s ih =>
    have hstep : (Cmp M N eo ei).step (tcfg false o SM SN a) =
        some (tcfg false (some (eo c)) (Function.update SM M.k₁ s) SN (eo c :: a)) := by
      show some (TM2.stepAux (cprog M N eo ei (Sum.inr (Sum.inr false)))
        (M.initialState, N.initialState, o) (mkStk M N SM SN a)) = _
      simp [cprog, TM2.stepAux, mkStk, upd_M, upd_A, tcfg, h]
      rfl
    have h2 := ih (some (eo c)) (Function.update SM M.k₁ s) (eo c :: a) (Function.update_self _ _ _)
    have ht := RIn.step_trans hstep h2
    simp only [Function.update_idem] at ht
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using ht

lemma mv2_run (a : List Bool) (o : Option Bool) (SN : ∀ k, List (N.Γ k)) :
    RIn (Cmp M N eo ei).step (tcfg true o (fun _ => []) SN a)
      (some (liftCfgN ⟨some N.main, N.initialState,
        Function.update SN N.k₀ ((a.map ei.symm).reverse ++ SN N.k₀)⟩))
      (a.length + 1) := by
  induction a generalizing o SN with
  | nil =>
    simp only [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
    apply RIn.single
    show some (TM2.stepAux (cprog M N eo ei (Sum.inr (Sum.inr true)))
      (M.initialState, N.initialState, o) (mkStk M N (fun _ => []) SN [])) = _
    simp [cprog, TM2.stepAux, mkStk, upd_N, upd_A, liftCfgN]
    rfl
  | cons c a ih =>
    have hstep : (Cmp M N eo ei).step (tcfg true o (fun _ => []) SN (c :: a)) =
        some (tcfg true (some c) (fun _ => [])
          (Function.update SN N.k₀ (ei.symm c :: SN N.k₀)) a) := by
      show some (TM2.stepAux (cprog M N eo ei (Sum.inr (Sum.inr true)))
        (M.initialState, N.initialState, o) (mkStk M N (fun _ => []) SN (c :: a))) = _
      simp [cprog, TM2.stepAux, mkStk, upd_N, upd_A, tcfg]
      rfl
    have ht := RIn.step_trans hstep (ih (some c) _)
    simp only [Function.update_self, Function.update_idem] at ht
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using ht

lemma initList_Cmp (s : List (M.Γ M.k₀)) :
    initList (Cmp M N eo ei) s = liftCfgM (initList M s) := by
  simp only [initList, liftCfgM]
  congr 1
  funext k
  rcases k with k | k | k
  · by_cases h : k = M.k₀
    · subst h
      simp [mkStk]
      split
      · rfl
      · rename_i hne; exact absurd rfl hne
    · simp [mkStk, h]
      split
      · rename_i heq
        exact absurd (Sum.inl_injective (heq : (Sum.inl k : CK M N) = Sum.inl M.k₀)) h
      · rfl
  · rfl
  · rfl

lemma haltList_Cmp (s : List (N.Γ N.k₁)) :
    liftCfgN (eo := eo) (ei := ei) (haltList N s) = haltList (Cmp M N eo ei) s := by
  simp only [liftCfgN, haltList]
  congr 1
  funext k
  rcases k with k | k | k
  · rfl
  · by_cases h : k = N.k₁
    · subst h
      simp [mkStk]
      split
      · rfl
      · rename_i hne; exact absurd rfl hne
    · simp [mkStk, h]
      split
      · rename_i heq
        exact absurd (Sum.inl_injective (Sum.inr_injective
          (heq : (Sum.inr (Sum.inl k) : CK M N) = Sum.inr (Sum.inl N.k₁)))) h
      · rfl
  · rfl

lemma comp_run {s : List (M.Γ M.k₀)} {mid : List Bool} {out : List (N.Γ N.k₁)} {T₁ T₂ : ℕ}
    (h₁ : TM2OutputsInTime M s (some (List.map eo.symm mid)) T₁)
    (h₂ : TM2OutputsInTime N (List.map ei.symm mid) (some out) T₂) :
    RIn (Cmp M N eo ei).step (initList (Cmp M N eo ei) s)
      (some (haltList (Cmp M N eo ei) out))
      (T₁ + ((mid.length + 1) + (mid.length + 1)) + T₂) := by
  have r1 : RIn (Cmp M N eo ei).step (initList (Cmp M N eo ei) s)
      (some (tcfg false none (haltList M (List.map eo.symm mid)).stk (fun _ => []) [])) T₁ := by
    obtain ⟨⟨n, hn⟩, hle⟩ := h₁
    refine ⟨n, hle, ?_⟩
    rw [initList_Cmp]
    exact iterate_liftM n (initList M s) (haltList M (List.map eo.symm mid)) hn
  have hstk : (haltList M (List.map eo.symm mid)).stk M.k₁ = List.map eo.symm mid := by
    simp [haltList]
  have hupd : Function.update (haltList M (List.map eo.symm mid)).stk M.k₁ [] = fun _ => [] := by
    funext k
    by_cases hk : k = M.k₁
    · subst hk; simp
    · simp [haltList, hk]
  have r2a := mv1_run (eo := eo) (ei := ei) (List.map eo.symm mid) none
    (haltList M (List.map eo.symm mid)).stk (fun _ => []) [] hstk
  rw [hupd] at r2a
  have hmid : (List.map eo.symm mid).map eo = mid := by simp
  rw [hmid, List.length_map] at r2a
  have r2b := mv2_run (M := M) (eo := eo) (ei := ei) (mid.reverse ++ []) none (fun _ => [])
  have hcfg : (List.map ei.symm (mid.reverse ++ [])).reverse ++ [] = List.map ei.symm mid := by
    simp [List.map_reverse]
  have hinitN : (⟨some N.main, N.initialState,
      Function.update (fun _ => []) N.k₀ (List.map ei.symm mid)⟩ : TM2.Cfg N.Γ N.Λ N.σ) =
      initList N (List.map ei.symm mid) := by
    simp only [initList]
    congr 1
    funext k
    by_cases hk : k = N.k₀
    · subst hk; simp
    · simp [hk]
  rw [hcfg, hinitN] at r2b
  have hlen : (mid.reverse ++ []).length = mid.length := by simp
  rw [hlen] at r2b
  have r3 : RIn (Cmp M N eo ei).step (liftCfgN (initList N (List.map ei.symm mid)))
      (some (haltList (Cmp M N eo ei) out)) T₂ := by
    obtain ⟨⟨n, hn⟩, hle⟩ := h₂
    refine ⟨n, hle, ?_⟩
    have hi := iterate_liftN (M := M) (N := N) (eo := eo) (ei := ei) n
      (some (initList N (List.map ei.symm mid)))
    change (flip bind (Cmp M N eo ei).step)^[n]
      (Option.map liftCfgN (some (initList N (List.map ei.symm mid)))) = _
    rw [hi]
    refine (congrArg (Option.map liftCfgN) hn).trans ?_
    show some (liftCfgN (haltList N out)) = _
    rw [haltList_Cmp]
  exact (r1.trans (r2a.trans r2b)).trans r3

end Comp

theorem comp_polyTime {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] (f : α → β) (g : β → γ) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (g ∘ f) := by
  obtain ⟨M⟩ := hf
  obtain ⟨N⟩ := hg
  obtain ⟨B, hB⟩ := exists_pushBound M.tm
  refine ⟨{
    tm := Cmp M.tm N.tm M.outputAlphabet N.inputAlphabet
    inputAlphabet := M.inputAlphabet
    outputAlphabet := N.outputAlphabet
    time := M.time + Polynomial.C 2 * (Polynomial.X + M.time * Polynomial.C B + 1) +
      N.time.comp (Polynomial.X + M.time * Polynomial.C B)
    outputsFun := fun a => ?_ }⟩
  have hM := M.outputsFun a
  have hN := N.outputsFun (f a)
  set x := (BitstringEncoding.toEncoding (α := α)).encode a
  set y := (BitstringEncoding.toEncoding (α := β)).encode (f a)
  have hlen : y.length ≤ x.length + M.time.eval x.length * B := by
    have := out_len M.tm hB hM
    simpa using this
  have hrun := comp_run (M := M.tm) (N := N.tm) (eo := M.outputAlphabet)
    (ei := N.inputAlphabet) (mid := y) hM hN
  have hb : M.time.eval x.length + ((y.length + 1) + (y.length + 1)) + N.time.eval y.length ≤
      (M.time + Polynomial.C 2 * (Polynomial.X + M.time * Polynomial.C B + 1) +
        N.time.comp (Polynomial.X + M.time * Polynomial.C B)).eval x.length := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_comp]
    have := eval_mono N.time hlen
    generalize M.time.eval x.length * B = W at *
    omega
  exact Classical.choice (by
    obtain ⟨n, hle, he⟩ := hrun.mono hb
    exact ⟨⟨⟨n, he⟩, hle⟩⟩)

end OMA.Erdos78LiH2

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_li_R2.H2 := fun f hf =>
  ⟨f ∘ OMA.Erdos78LiH2.prepFun,
    OMA.Erdos78LiH2.comp_polyTime OMA.Erdos78LiH2.prepFun f OMA.Erdos78LiH2.isPolyTime_prepFun hf,
    fun _ _ _ => rfl⟩
